//! This is an aggressively simple Tcl-like language optimized for binary size,
//! code complexity, and performance, in that order. That is, it's mostly
//! intended to be small, but with readable code and ok performance.
//!
//! # Implementation design and theory of operation
//!
//! The Tcl language is one example the principle "everything is a string." All
//! of Tcl's data types are --- notionally, at least --- represented as strings,
//! and they can be converted from one to the other by parsing. Modern Tcl
//! implementations provide this illusion while using more efficient
//! representations under the hood.
//!
//! `wartcl` takes it literally. Everything is a string, a heap-allocated
//! sequence of human-readable bytes, encoded in either ASCII (if you leave the
//! top bit of each byte clear) or UTF-8 (if you don't). `wartcl` doesn't
//! actually care about character encoding.
//!
//! This keeps the implementation _very simple_ but has significant performance
//! costs. Want to add two numbers? Well, you'll have to parse two numeric
//! strings, add the result, and then re-format the result into another
//! (heap-allocated) numeric string. (This is not the fastest way to use a
//! computer, but `wartcl` is not really designed for arithmetic-heavy
//! applications.)
//!
//! Basically every value, from the program's source code on up, is represented
//! as a `Box<[u8]>`. This is an owned pointer to a slice of bytes. Cloning it
//! implies a full copy of its contents; dropping it deallocates the contents.
//!
//! The advantages of `Box<[u8]>` over `Vec<u8>` are:
//!
//! 1. `Vec` may retain extra memory for expansion, which we don't generally
//!    need because values are immutable once constructed.
//! 2. `Vec` is one word larger, making it correspondingly more expensive to
//!    store and pass around.
//!
//! To clarify intent, in the implementation, `[u8]` is given the type alias
//! `Value`.
//!
//! # About the name
//!
//! `wartcl` stands for "`wartcl` Ain't Really Tcl" because the language differs
//! from standard Tcl in a whole bunch of ways.
//!
//! It's also a pun on the C `partcl` library's name, after the "warticle" term
//! humorously used to describe phenomena exhibiting wave/partical duality in
//! quantum physics.

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![forbid(unsafe_code)]

extern crate alloc;
use core::mem;
use alloc::rc::Rc;
use alloc::boxed::Box;
use alloc::vec::Vec;

/// Internal macro to make it easier to comment/uncomment a bunch of printlns
/// all in one place.
macro_rules! debug {
    ($($x:tt)*) => { /* println!($($x)*) */ };
}

/// Interpreter state.
///
/// To run a program, you need one of these. You can create one using
/// `init()`, and then call `eval` as many times as required.
///
/// Dropping it will deallocate all associated state.
#[derive(Default)]
pub struct Tcl {
    env: Box<Env>,
    cmds: Option<Box<Cmd>>,
    pub result: Box<Value>,
}

impl Tcl {
    /// Creates a new `Tcl` environment and initializes it with the standard
    /// bundled command set before returning it.
    pub fn init() -> Self {
        let env = Env::alloc(None);

        let mut tcl = Self {
            env,
            ..Self::default()
        };

        for &(name, arity, function) in STANDARD_COMMANDS {
            tcl.register(name, arity, function);
        }

        tcl
    }

    /// Adds a command to `tcl`, under the name `name`, expecting `arity`
    /// arguments (including its own name!), and implemented by the Rust
    /// function `function`.
    ///
    /// If a command can handle various numbers of arguments, the `arity` here
    /// should be 0, and the command is responsible for checking argument count
    /// itself.
    pub fn register(&mut self, name: &Value, arity: usize, function: impl Fn(&mut Tcl, Vec<Box<Value>>) -> Result<(), FlowChange> + 'static) {
        let next = self.cmds.take();
        self.cmds = Some(Box::new(Cmd {
            name: name.into(),
            arity,
            function: Rc::new(function),
            next,
        }));
    }

    /// Evaluates the source code `s` in terms of the interpreter `tcl`.
    ///
    /// The result will be deposited in `tcl.result`, and the final control flow
    /// decision returned.
    pub fn eval(&mut self, s: &Value) -> Result<(), FlowChange> {
        debug!("eval({:?})", String::from_utf8_lossy(s));
        let mut p = Tokenizer::new(s);

        let mut cur = Vec::new();
        let mut list = Vec::new();

        while let Some((tok, from)) = p.next(true) {
            match tok {
                Token::Error => {
                    return self.set_result_err(FlowChange::Error, empty());
                }

                Token::Word => {
                    // N.B. result ignored in original
                    self.subst(from)?;
                    cur.push(mem::take(&mut self.result));
                    list.push(flatten_string(&cur));
                    cur.clear();
                }

                Token::Part => {
                    self.subst(from)?;
                    cur.push(mem::take(&mut self.result));
                }
                Token::Cmd => {
                    let n = list.len();
                    if n == 0 {
                        debug!("Cmd with zero length list");
                        self.result = empty();
                    } else {
                        debug!("Cmd with proper list");
                        let cmdname = &*list[0];
                        debug!("finding: {}/{}", String::from_utf8_lossy(&cmdname), n);
                        let mut cmd = self.cmds.as_deref();
                        let mut found = false;

                        while let Some(c) = cmd.take() {
                            if &*c.name == cmdname && (c.arity == 0 || c.arity == n) {
                                found = true;
                                debug!("calling: {}/{}", String::from_utf8_lossy(&c.name), c.arity);
                                let f = Rc::clone(&c.function);
                                f(self, mem::take(&mut list))?;
                                break;
                            }

                            cmd = c.next.as_deref();
                        }

                        if !found {
                            return Err(FlowChange::Error);
                        }

                        debug!("normal");
                        debug_assert!(list.is_empty());
                    }
                }
            }
        }

        debug!("end eval");
        Ok(())
    }

    pub fn clear_result(&mut self) {
        if !self.result.is_empty() {
            self.result = empty();
        }
    }

    /// Shorthand for storing `value` in `tcl.result` and then returning `flow`.
    pub fn set_result_ok(&mut self, value: Box<Value>) -> Result<(), FlowChange> {
        self.result = value;
        Ok(())
    }

    /// Shorthand for storing `value` in `tcl.result` and then returning `Err(flow)`.
    pub fn set_result_err<T>(&mut self, flow: FlowChange, value: Box<Value>) -> Result<T, FlowChange> {
        self.result = value;
        Err(flow)
    }

    /// Looks up a variable named `name` in the current innermost scope,
    /// creating it if it doesn't exist.
    ///
    /// If `value` is `Some(v)`, the variable's contents will be set to `v`. If
    /// a variable is newly created but `value` is `None`, the variable will
    /// default to the empty string.
    ///
    /// Returns a copy of the variable's contents. (TODO: ideally this would not
    /// imply an automatic copy.)
    fn var(&mut self, name: Box<Value>, value: Option<Box<Value>>) -> Box<Value> {
        let mut var = self.env.vars.as_mut();
        while let Some(v) = var.take() {
            if v.name == name {
                var = Some(v);
                break;
            }
            var = v.next.as_mut();
        }
        let var = match var {
            Some(v) => v,
            None => self.env.add_var(name),
        };

        if let Some(value) = value {
            var.value = value;
        }

        var.value.clone()
    }

    /// Performs a single substitution step on `s`, leaving the result in
    /// `tcl.result`.
    ///
    /// Substitution steps include peeling the outer curly braces off a braced
    /// string, evaluating a square-bracketed subcommand, or processing a
    /// dollar-sign variable splice.
    fn subst(&mut self, s: &Value) -> Result<(), FlowChange> {
        match s.split_first() {
            None => self.set_result_ok(empty()),
            Some((b'{', b"")) => self.set_result_err(FlowChange::Error, empty()),
            Some((b'{', rest)) => {
                self.set_result_ok(rest[..rest.len() - 1].into())
            }
            Some((b'$', name)) => {
                let mut subcmd = b"set ".to_vec();
                subcmd.extend_from_slice(name);
                subcmd.push(b'\n');
                self.eval(&subcmd)
            }
            Some((b'[', rest)) => {
                // ugh TODO
                let rest = add_newline(&rest[..rest.len() - 1]);
                self.eval(&rest)
            }
            _ => self.set_result_ok(s.into()),
        }
    }
}

fn add_newline(v: impl Into<Vec<u8>>) -> Box<Value> {
    let mut v: Vec<u8> = v.into();
    v.push(b'\n');
    v.into()
}

/// Parses `v` as a signed integer. This always succeeds; if `v` is not a valid
/// signed integer, this returns 0.
pub fn int(v: &Value) -> i32 {
    core::str::from_utf8(v)
        .ok()
        .and_then(|s| s.parse::<i32>().ok())
        .unwrap_or(0)
}

pub fn int_value(x: i32) -> Box<Value> {
    let mut text = Vec::new();
    let negative = x < 0;
    let mut c = x.abs();
    loop {
        text.push((c % 10) as u8 + b'0');
        c /= 10;
        if c == 0 { break; }
    }
    if negative {
        text.push(b'-');
    }
    text.reverse();
    text.into()
}

/// Types of tokens that may be produced by the tokenizer.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Token {
    /// A command has been completed (though it might be empty).
    Cmd,
    /// A word has been completed syntactically. Note that a "word" in this case
    /// may be an arbitrarily complex braced structure, or a subcommand, or a
    /// quoted string, in addition to the obvious "string of characters without
    /// whitespace" definition.
    Word,
    /// Part of a word has been completed. Multiple parts found next to each
    /// other should be pasted together.
    Part,
    /// Input was invalid.
    Error,
}

/// Source code tokenizer state.
pub struct Tokenizer<'a> {
    text: &'a Value,
    quote_mode: bool,
}

impl<'a> Tokenizer<'a> {
    /// Creates a new tokenizer to process the input `text`.
    pub fn new(text: &'a Value) -> Self {
        Self {
            text,
            quote_mode: false,
        }
    }

    /// Checks if the tokenizer has no further input. (Note that even if this
    /// returns `false`, there may not be any _useful_ remaining input, because
    /// it might be e.g. whitespace.)
    pub fn at_end(&self) -> bool {
        self.text.is_empty()
    }

    /// Advances the tokenizer and returns the next thing found, or `None` if
    /// we've exhausted the input.
    ///
    /// `skiperr` is normally `false`, which causes tokenization to treat an
    /// error as the end of input. If `skiperr` is true, any error found will be
    /// returned, and the tokenizer will be ready to continue past the error to
    /// the best of its ability.
    ///
    /// When input is successfully tokenized, this returns `Some((token,
    /// text))`, where `token` describes what was found, and `text` contains its
    /// actual bytes.
    pub fn next(&mut self, skiperr: bool) -> Option<(Token, &'a Value)> {
        if self.text.is_empty() {
            return None;
        }
        let (tok, from, to) = next(self.text, &mut self.quote_mode);
        if !skiperr && tok == Token::Error {
            return None;
        }
        self.text = to;
        Some((tok, from))
    }
}

/// Processes a value as a list, breaking it at (top-level) whitespace into a
/// vector of element values.
///
/// This follows normal Tcl-style list parsing rules, so "a" is a list of one
/// element, "a b c" is a list of three, and "a {b c}" is a list of two.
pub fn parse_list(v: &Value) -> Vec<Box<Value>> {
    let mut words = Vec::new();

    let mut p = Tokenizer::new(v);
    let mut rest = v;
    while let Some((tok, from)) = p.next(false) {
        rest = p.text;
        if tok == Token::Word {
            words.push(if from[0] == b'{' {
                from[1..from.len() - 1].into()
            } else {
                from.into()
            });
        }
    }
    skip_leading_whitespace(&mut rest);

    if !rest.is_empty() {
        words.push(if rest[0] == b'{' {
            rest[1..rest.len() - 1].into()
        } else {
            rest.into()
        });
    }

    words
}

/// Flow control instructions that can be returned by commands, in place of
/// normal completion.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum FlowChange {
    /// Something has gone wrong, the program is failing.
    Error = 1,
    /// The command is asking to return from the current scope/procedure.
    Return,
    /// The command is asking to terminate the current innermost loop.
    Break,
    /// The command is asking to repeat the current innermost loop.
    Again,
}

/// Checks if `c` is a "special" character with syntactic significance. This has
/// two different modes, controlled by `q`: when `q` is `true`, this checks for
/// characters that are significant inside a quoted string; when `q` is `false`,
/// this does the same check for _outside_ a quoted string.
fn is_special(c: u8, q: bool) -> bool {
    (!q && b"{};\r\n".contains(&c)) || b"$[]\"".contains(&c)
}

/// Checks if `c` is token-separating whitespace that can appear within a
/// command, which in practice means space or tab.
fn is_space(c: u8) -> bool { b" \t".contains(&c) }

/// Checks if `c` is a command-terminating character, such as an end-of-line or
/// a semicolon.
fn is_end(c: u8) -> bool { b"\n\r;".contains(&c) }

/// This is a little weird, but it's convenient below to indicate where we're
/// treating a slice of bytes as a value vs just any old bytes.
type Value = [u8];

/// Produces a newly allocated string value that contains all the elements of
/// `v` concatenated together, with no intervening bytes. This operation is
/// useful for pasting strings together during substitution handling.
fn flatten_string(v: &[Box<Value>]) -> Box<Value> {
    let len = v.iter().map(|component| component.len()).sum::<usize>();
    let mut out = Vec::with_capacity(len);
    for component in v {
        out.extend_from_slice(component);
    }
    out.into()
}

/// Convenience function for getting an empty value.
fn empty() -> Box<Value> {
    Box::new([])
}

/// Updates `s` by stripping off leading (horizontal) whitespace characters.
fn skip_leading_whitespace(s: &mut &Value) {
    while let Some((&first, next)) = s.split_first() {
        if is_space(first) {
            *s = next;
        } else {
            break;
        }
    }
}

/// Basic step function for the tokenizer. Generally you won't need to call this
/// directly.
///
/// `s` is the currently available input.
///
/// `quote_mode` indicates if we're starting within a quoted string. On return,
/// it will be updated to indicate if the _next_ parse will start within a
/// quoted string.
///
/// Returns a triple of `(token, text, rest)`, where `token` indicates the type
/// of thing that was found, `text` is its contents, and `rest` is the remaining
/// input to parse next.
fn next<'data>(
    mut s: &'data Value,
    quote_mode: &mut bool,
) -> (Token, &'data Value, &'data Value) {
    if !*quote_mode {
        skip_leading_whitespace(&mut s);
    }

    if !*quote_mode && s.first().map(|&c| is_end(c)).unwrap_or(false) {
        let (before, after) = s.split_at(1);
        return (Token::Cmd, before, after);
    }

    if s.first().map(|&c| c == b'$').unwrap_or(false) {
        // variable token, must not start with a space or quote
        if s.get(1).map(|&c| is_space(c) || c == b'"').unwrap_or(false) {
            return (Token::Error, s, &[]);
        }
        let (subtoken, subused, subrest) = next(&s[1..], &mut false);
        return (
            if subtoken == Token::Word && *quote_mode { Token::Part } else { subtoken },
            &s[..subused.len() + 1],
            subrest,
        );
    }

    let i = if let Some((&open, after)) = s.split_first() {
        if open == b'[' || (!*quote_mode && open == b'{') {
            // interleaving pairs are not welcome, but it simplifies the code
            let close = if open == b'[' { b']' } else { b'}' };
            let mut depth = 1;
            s.iter().enumerate().position(|(i, &c)| {
                if depth == 0 {
                    return true;
                }

                if i > 0 && c == open {
                    depth += 1;
                } else if c == close {
                    depth -= 1;
                }
                false
            }).unwrap_or(s.len())
        } else if open == b'"' {
            *quote_mode = !*quote_mode;

            // *from = *to = s + 1;
            let from = &[];
            let to = after;

            if *quote_mode {
                // We have just _entered_ a quoted string.
                return (Token::Part, from, to);
            }
            // Otherwise, we are exiting a quoted string.

            // Character immediately after the quote must be space or
            // terminator.
            let token = if to.is_empty() || (!is_space(to[0]) && !is_end(to[0])) {
                Token::Error
            } else {
                Token::Word
            };
            return (token, from, to);
        } else if open == b']' || open == b'}' {
            // unbalanced bracket or brace
            return (Token::Error, s, &[]);
        } else {
            s.iter().position(|&c| (!*quote_mode && is_space(c))
                              || is_special(c, *quote_mode))
                .unwrap_or(s.len())
        }
    } else {
        0
    };
    let (from, to) = s.split_at(i);
    let Some(&first) = to.first() else {
        return (Token::Error, from, to);
    };
    let token = if *quote_mode {
        Token::Part
    } else if is_space(first) || is_end(first) {
        Token::Word
    } else {
        Token::Part
    };
    (token, from, to)
}

/// A variable in a scope.
struct Var {
    /// Name of the variable, used to find it during search.
    name: Box<Value>,
    /// Contents of the variable.
    value: Box<Value>,
    /// Link to next variable in this scope, or `None` if this is the end of the
    /// chain.
    next: Option<Box<Var>>,
}

/// A scope, either global or procedural.
#[derive(Default)]
struct Env {
    /// Chain of variables defined in this scope, or `None` if there aren't any.
    vars: Option<Box<Var>>,
    /// Next outer scope. Note that this is _not_ a lexical parent --- variable
    /// lookup never uses this. This is a pointer to the scope that will become
    /// current if this scope returns.
    ///
    /// In the outermost global scope, this is `None`.
    parent: Option<Box<Env>>,
}

impl Env {
    /// Creates a new empty scope, with the given parent.
    fn alloc(parent: Option<Box<Env>>) -> Box<Env> {
        Box::new(Env {
            vars: None,
            parent,
        })
    }

    /// Creates a new `Var` with the given `name` and attaches it at the front
    /// of `env`'s var chain.
    ///
    /// This operation is unconditional. If there's already a `Var` named `name`
    /// in `env`, the new one will shadow it. (You almost never want that.)
    ///
    /// Returns a reference to the newly created `Var` so it can be filled in.
    fn add_var(&mut self, name: Box<Value>) -> &mut Var {
        let var = Box::new(Var {
            name,
            value: Box::new([]),
            next: self.vars.take(),
        });
        self.vars.insert(var)
    }
}

/// Shorthand for the type of our boxed command closures.
type FnDyn = dyn Fn(&mut Tcl, Vec<Box<Value>>) -> Result<(), FlowChange>;

/// A command record. Each command that is registered gets one of these,
/// assembled into a chain.
struct Cmd {
    /// Name of the command, used for lookup.
    name: Box<Value>,
    /// Number of arguments the command requires, or `0` if the command can take
    /// varying numbers of arguments. This affects lookup: `x y z` will only
    /// find a command named `"x"` if its `arity` is either 3 or 0.
    arity: usize,
    /// Implementation of the command, as a boxed (reference-counted) closure.
    ///
    /// This is an `Rc` instead of `Box` because we need to be able to separate
    /// its lifetime from the lifetime of the overall `Tcl` struct during
    /// evaluation, lest we wind up with aliasing. (This also ensures a command
    /// keeps working even if it's deleted or replaced during execution.)
    function: Rc<FnDyn>,
    /// Next command in the chain, or `None` if this is the last one.
    next: Option<Box<Cmd>>,
}

/// Implementation of the `set` standard command.
fn cmd_set(tcl: &mut Tcl, mut args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let name = mem::take(&mut args[1]);
    let val = args.get_mut(2).map(mem::take);

    let v = tcl.var(name, val);
    tcl.set_result_ok(v)
}

/// Implementation of the `subst` standard command.
fn cmd_subst(tcl: &mut Tcl, args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let s = &args[1];
    tcl.subst(s)
}

fn cmd_incr(tcl: &mut Tcl, mut args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let name = mem::take(&mut args[1]);
    let v = tcl.var(name.clone(), None);
    let r = tcl.var(name, Some(int_value(int(&v) + 1)));
    tcl.set_result_ok(r)
}

/// Implementation of the `puts` standard command.
#[cfg(any(test, feature = "std"))]
fn cmd_puts(tcl: &mut Tcl, mut args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let str = mem::take(&mut args[1]);
    println!("{}", String::from_utf8_lossy(&str));
    tcl.set_result_ok(str)
}

/// Implementation of the `proc` standard command.
fn cmd_proc(tcl: &mut Tcl, mut args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let body = mem::take(&mut args[3]);
    let params = mem::take(&mut args[2]);
    let name = &args[1];
    let body = add_newline(body);

    let parsed_params = parse_list(&params);

    tcl.register(name, 0, move |tcl, mut act_args| {
        tcl.env = Env::alloc(Some(mem::take(&mut tcl.env)));

        for (i, param) in parsed_params.iter().enumerate() {
            let v = act_args.get_mut(i + 1).map(mem::take);
            tcl.var(param.clone(), v);
        }
        let r = tcl.eval(&body);

        let parent_env = tcl.env.parent.take().unwrap();
        tcl.env = parent_env;

        match r {
            Err(FlowChange::Return) | Ok(()) => Ok(()),
            // Coerce break/continue at top level of proc into error.
            Err(_) => Err(FlowChange::Error),
        }
    });
    tcl.set_result_ok(empty())
}

/// Implementation of the `if` standard command.
///
/// `if {condition} {body}`
/// `if {condition} {body} else {body2}`
/// `if {condition} {body} elseif {condition2} {body2} ...`
/// `if {condition} {body} elseif {condition2} {body2} ... else {body3}`
fn cmd_if(tcl: &mut Tcl, mut args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    // Skip the first argument.
    let mut i = 1;

    // We always arrive at the top of this loop while expecting a condition,
    // either just after the initial "if", or after an "elseif".
    while i < args.len() {
        let cond = add_newline(mem::take(&mut args[i]));
        tcl.eval(&cond)?;

        let cond = int(&tcl.result) != 0;

        if cond {
            let branch = mem::take(&mut args[i + 1]);
            let branch = add_newline(branch);
            tcl.eval(&branch)?;
            break;
        }

        i += 2;

        if let Some(next) = args.get(i) {
            match &**next {
                b"else" => {
                    let branch = add_newline(mem::take(&mut args[i + 1]));
                    return tcl.eval(&branch);
                }
                b"elseif" => {
                    // Prime the result to return error if elseif is the last
                    // token.
                    if i + 1 == args.len() {
                        return Err(FlowChange::Error);
                    }
                    i += 1;
                }
                _ => return Err(FlowChange::Error),
            }
        }
    }
    Ok(())
}

/// Implementation of the `while` standard command.
fn cmd_while(tcl: &mut Tcl, mut args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let body = add_newline(mem::take(&mut args[2]));

    let cond = add_newline(mem::take(&mut args[1]));

    debug!("while body = {:?}", String::from_utf8_lossy(&body));
    loop {
        tcl.eval(&cond)?;
        if int(&tcl.result) == 0 {
            return Ok(());
        }
        let r = tcl.eval(&body);
        match r {
            Err(FlowChange::Again) | Ok(_) => (),

            Err(FlowChange::Break) => return Ok(()),
            Err(e) => return Err(e),
        }
    }
}

/// Implementation of the standard math commands; parses its first argument to
/// choose the operation.
fn cmd_math(tcl: &mut Tcl, args: Vec<Box<Value>>) -> Result<(), FlowChange> {
    let bval = &args[2];
    let aval = &args[1];
    let opval = &args[0];

    let a = int(aval);
    let b = int(bval);

    let c = match &**opval {
        b"+" => a + b,
        b"-" => a - b,
        b"*" => a * b,
        b"/" => a / b,
        b">" => (a > b) as i32,
        b">=" => (a >= b) as i32,
        b"<" => (a < b) as i32,
        b"<=" => (a <= b) as i32,
        b"==" => (a == b) as i32,
        b"!=" => (a != b) as i32,
        _ => panic!(),
    };

    tcl.set_result_ok(int_value(c))
}

/// Type of a command implemented with a stateless function pointer, as opposed
/// to a general closure.
type StaticCmd = fn(&mut Tcl, Vec<Box<Value>>) -> Result<(), FlowChange>;

static STANDARD_COMMANDS: &[(&Value, usize, StaticCmd)] = &[
    (b"set", 0, cmd_set),
    #[cfg(any(test, feature = "std"))]
    (b"puts", 2, cmd_puts),
    (b"subst", 2, cmd_subst),
    (b"proc", 4, cmd_proc),
    (b"if", 0, cmd_if),
    (b"while", 3, cmd_while),
    (b"break", 1, |_, _| Err(FlowChange::Break)),
    (b"continue", 1, |_, _| Err(FlowChange::Again)),
    (b"return", 0, |tcl, mut args| {
        tcl.set_result_err(
            FlowChange::Return,
            args.get_mut(1).map(mem::take).unwrap_or_default(),
        )
    }),
    //(b"incr", 2, cmd_incr),
    (b"+", 3, cmd_math),
    (b"-", 3, cmd_math),
    (b"*", 3, cmd_math),
    (b"/", 3, cmd_math),
    (b">", 3, cmd_math),
    (b">=", 3, cmd_math),
    (b"<", 3, cmd_math),
    (b"<=", 3, cmd_math),
    (b"==", 3, cmd_math),
    (b"!=", 3, cmd_math),
];

#[cfg(test)]
mod test;
