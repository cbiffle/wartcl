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

mod cmd;

/// Interpreter state.
///
/// To run a program, you need one of these. You can create one using
/// `init()`, and then call `eval` as many times as required.
///
/// Dropping it will deallocate all associated state.
#[derive(Default)]
pub struct Env {
    env: Scope,
    cmds: Option<Box<Cmd>>,
}

impl Env {
    /// Creates a new `Env` environment and initializes it with the standard
    /// bundled command set before returning it.
    pub fn init() -> Self {
        let mut env = Self::default();

        cmd::register_all(&mut env);

        env
    }

    /// Adds a command to `self`, under the name `name`, expecting `arity`
    /// arguments (including its own name!), and implemented by the Rust
    /// function `function`.
    ///
    /// If a command can handle various numbers of arguments, the `arity` here
    /// should be 0, and the command is responsible for checking argument count
    /// itself.
    pub fn register(&mut self, name: &Value, arity: usize, function: impl Fn(&mut Env, &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> + 'static) {
        let next = self.cmds.take();
        self.cmds = Some(Box::new(Cmd {
            name: name.into(),
            arity,
            function: Rc::new(function),
            next,
        }));
    }

    /// Evaluates the source code `s` in terms of this interpreter.
    ///
    /// On normal completion, returns the result. Otherwise, returns the change
    /// in flow control.
    pub fn eval(&mut self, s: &Value) -> Result<OwnedValue, FlowChange> {
        debug!("eval({:?})", String::from_utf8_lossy(s));
        let mut p = Tokenizer::new(s);

        let mut cur = Vec::new();
        let mut list = Vec::new();

        let mut last_result = None;

        loop {
            let tok = p.next();
            match tok {
                Some(Token::Error) => {
                    return Err(FlowChange::Error);
                }

                Some(Token::Word(w) | Token::Part(w)) => {
                    cur.push(self.subst(w)?);
                    if matches!(tok, Some(Token::Word(_))) {
                        list.push(flatten_string(&cur));
                        cur.clear();
                    }
                }

                Some(Token::CmdSep) | None => {
                    if !cur.is_empty() {
                        return Err(FlowChange::Error);
                    }

                    if let Some(cmdname) = list.first() {
                        debug!("Cmd with proper list");
                        debug!("finding: {}/{}", String::from_utf8_lossy(&cmdname), n);
                        let mut cmd = self.cmds.as_deref();
                        let mut found = false;

                        while let Some(c) = cmd.take() {
                            if &c.name == cmdname && (c.arity == 0 || c.arity == list.len()) {
                                found = true;
                                debug!("calling: {}/{}", String::from_utf8_lossy(&c.name), c.arity);
                                let f = Rc::clone(&c.function);
                                last_result = Some(f(self, &mut list)?);
                                list.clear();
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

                    if tok.is_none() {
                        break;
                    }
                }
            }
        }

        debug!("end eval");
        Ok(last_result.unwrap_or_default())
    }

    fn find_var(&mut self, name: &Value) -> Option<&mut Var> {
        let mut var = self.env.vars.as_mut();
        while let Some(v) = var.take() {
            if &*v.name == name {
                return Some(v);
            }
            var = v.next.as_mut();
        }
        None
    }

    /// Sets a variable named `name` to `value` in the current innermost scope,
    /// creating it if it doesn't exist.
    pub fn set_or_create_var(&mut self, name: OwnedValue, value: OwnedValue) {
        let var = match self.find_var(&name) {
            Some(v) => v,
            None => self.env.add_var(name),
        };

        var.value = value;
    }

    /// Gets a copy of the contents of an existing variable, or returns
    /// `Err(Error)` if it doesn't exist.
    pub fn get_existing_var(&mut self, name: &Value) -> Option<OwnedValue> {
        let var = self.find_var(name)?;

        Some(var.value.clone())
    }

    /// Performs a single substitution step on `s`, returning the result on
    /// success.
    ///
    /// Substitution steps include peeling the outer curly braces off a braced
    /// string, evaluating a square-bracketed subcommand, or processing a
    /// dollar-sign variable splice.
    fn subst(&mut self, s: &Value) -> Result<OwnedValue, FlowChange> {
        match s.split_first() {
            None => Ok(empty()),
            Some((b'{', b"")) => Err(FlowChange::Error),
            Some((b'{', rest)) => {
                Ok(rest[..rest.len() - 1].into())
            }
            Some((b'$', name)) => {
                let mut subcmd = b"set ".to_vec();
                subcmd.extend_from_slice(name);
                self.eval(&subcmd)
            }
            Some((b'[', rest)) => {
                self.eval(&rest[..rest.len() - 1])
            }
            _ => Ok(s.into()),
        }
    }
}

/// Parses `v` as a signed integer. This always succeeds; if `v` is not a valid
/// signed integer, this returns 0.
///
/// This handles hex numbers prefixed with a leading `0x`.
///
/// Quirks of this implementation:
/// - Skips leading whitespace
/// - Allows a + sign on positive numbers in addition to a - for negative.
/// - Parses a number from 0 or more valid ASCII digits.
/// - Ignores any trailing non-digit characters (whitespace or otherwise).
pub fn int(mut v: &Value) -> i32 {
    // In partcl, this was just a call to atoi. Rust's standard library
    // integer-string conversions are all _nice_ and have _error checking_ and
    // _Unicode handling_ and stuff like that. It adds about a kiB.
    //
    // So instead, here's an atoi-equivalent handrolled function.

    skip_leading_whitespace(&mut v);

    let mut negative = false;
    let Some((&first, rest)) = v.split_first() else {
        return 0;
    };
    if first == b'+' || first == b'-' {
        v = rest;
        negative = first == b'-';
    }

    let mut value = 0;
    if let Some(hexits) = v.strip_prefix(b"0x") {
        for &c in hexits {
            if !c.is_ascii_hexdigit() { break; }

            let c = c.to_ascii_lowercase();
            value = (value * 16) + if c >= b'a' {
                (c - b'a') as i32 + 10
            } else {
                (c - b'0') as i32
            };
        }
    } else {
        for &c in v {
            if !c.is_ascii_digit() { break; }

            value = (value * 10) + (c - b'0') as i32;
        }
    }
    if negative { -value } else { value }
}

pub fn int_value(x: i32) -> OwnedValue {
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

/// Processes a value as a list, breaking it at (top-level) whitespace into a
/// vector of element values.
///
/// This follows normal Tcl-style list parsing rules, so "a" is a list of one
/// element, "a b c" is a list of three, and "a {b c}" is a list of two.
pub fn parse_list(v: &Value) -> Vec<OwnedValue> {
    let mut words = Vec::new();

    for tok in Tokenizer::new(v) {
        if let Token::Word(text) = tok {
            words.push(if text[0] == b'{' {
                text[1..text.len() - 1].into()
            } else {
                text.into()
            });
        }
    }

    words
}

/// Flow control instructions that can be returned by commands, in place of
/// normal completion.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FlowChange {
    /// Something has gone wrong, the program is failing.
    Error,
    /// The command is asking to return from the current scope/procedure, with
    /// the given value.
    Return(OwnedValue),
    /// The command is asking to terminate the current innermost loop.
    Break,
    /// The command is asking to repeat the current innermost loop.
    Again,
}

static C_END: [u8; 3] = *b"\n\r;";
static C_SPECIAL: [u8; 4] = *b"$[]\"";

#[inline(never)]
fn is_splice_end(c: u8) -> bool { b"\t\n\r ;".contains(&c) }

/// Checks if `c` is token-separating whitespace that can appear within a
/// command, which in practice means space or tab.
fn is_space(c: u8) -> bool { b" \t".contains(&c) }

/// This is a little weird, but it's convenient below to indicate where we're
/// treating a slice of bytes as a value vs just any old bytes.
pub type Value = [u8];

pub type OwnedValue = Box<Value>;

/// Produces a newly allocated string value that contains all the elements of
/// `v` concatenated together, with no intervening bytes. This operation is
/// useful for pasting strings together during substitution handling.
fn flatten_string(v: &[OwnedValue]) -> OwnedValue {
    let len = v.iter().map(|component| component.len()).sum::<usize>();
    let mut out = Vec::with_capacity(len);
    for component in v {
        out.extend_from_slice(component);
    }
    out.into()
}

/// Convenience function for getting an empty value.
pub fn empty() -> OwnedValue {
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

pub struct Tokenizer<'a> {
    input: &'a [u8],
    quote: bool,
}

impl<'a> Tokenizer<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        Self { input, quote: false }
    }

    pub fn at_end(&self) -> bool {
        self.input.is_empty()
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Token<'a>> {
        // We are whitespace insensitive ... except inside a quoted string.
        if !self.quote {
            skip_leading_whitespace(&mut self.input);
        }

        // Separate first character and handle end-of-input.
        let Some((&first, rest)) = self.input.split_first() else {
            return if self.quote {
                Some(Token::Error)
            }  else {
                None
            };
        };

        // Detect, and skip, command separators.
        if C_END.contains(&first) {
            self.input = rest;
            return Some(Token::CmdSep);
        }

        let taken = match (first, rest.first(), self.quote) {
            // Characters that cannot legally appear at the end of input.
            (b'$' | b'[' | b'{', None, _) => {
                self.input = rest;
                return Some(Token::Error);
            }
            // Characters that cannot appear at the start of a word, outside of
            // quote mode.
            (b']', _, _) | (b'}', _, false) => {
                self.input = rest;
                return Some(Token::Error);
            }
            // Characters that cannot follow a dollar sign
            (b'$', Some(b' ' | b'"'), _) => {
                self.input = rest;
                return Some(Token::Error);
            }
            // Variable name.
            (b'$', Some(_), _) => {
                let mut subtok = Tokenizer::new(rest);
                match subtok.next() {
                    Some(Token::Word(name)) => {
                        let (name, rest) = self.input.split_at(name.len() + 1);
                        self.input = rest;
                        return Some(if self.quote {
                            Token::Part(name)
                        } else {
                            Token::Word(name)
                        });
                    }
                    Some(Token::Part(name)) => {
                        let (name, rest) = self.input.split_at(name.len() + 1);
                        self.input = rest;
                        return Some(Token::Part(name));
                    }
                    _ => {
                        self.input = rest;
                        return Some(Token::Error);
                    }
                }
            }
            (b'[', _, _) | (b'{', _, false) => {
                let last = if first == b'[' { b']' } else { b'}' };
                let mut depth = 0;
                let p = self.input.iter().position(|&c| {
                    if c == first {
                        depth += 1;
                    } else if c == last {
                        depth -= 1;
                    }
                    depth == 0
                });
                match p {
                    Some(p) => p + 1,
                    None => {
                        self.input = &[];
                        return Some(Token::Error);
                    }
                }
            }
            (b'"', nxt, _) => {
                self.quote = !self.quote;
                self.input = rest;

                if self.quote {
                    // New quoted string. Return an empty part as a hack to
                    // restart tokenization with the quote flag on.
                    return Some(Token::Part(b""));
                } else {
                    // Leaving a quoted string.
                    return Some(match nxt {
                        None => Token::Word(b""),
                        Some(c) if is_splice_end(*c) => Token::Word(b""),
                        _ => Token::Error,
                    });
                }
            }
            _ => {
                // Gonna try and lex a normal everyday word. We will include
                // characters as long as they are not significant in our mode,
                // which means stopping at whitespace outside of quotes, and
                // _not_ stopping at whitespace inside.
                //
                // Note that we are splitting the input, _not_ rest, because we
                // want to include the leading character.
                self.input.iter().position(|c| {
                    C_SPECIAL.contains(c)
                        || (!self.quote && (b"{}".contains(c) || is_splice_end(*c)))
                }).unwrap_or(self.input.len())
            }
        };
        let (word, rest) = self.input.split_at(taken);
        self.input = rest;
        if self.quote || !self.input.first().map(|&c| is_splice_end(c)).unwrap_or(true) {
            Some(Token::Part(word))
        } else {
            Some(Token::Word(word))
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Token<'a> {
    CmdSep,
    Word(&'a [u8]),
    Part(&'a [u8]),
    Error,
}


/// A variable in a scope.
struct Var {
    /// Name of the variable, used to find it during search.
    name: OwnedValue,
    /// Contents of the variable.
    value: OwnedValue,
    /// Link to next variable in this scope, or `None` if this is the end of the
    /// chain.
    next: Option<Box<Var>>,
}

/// A scope, either global or procedural.
#[derive(Default)]
struct Scope {
    /// Chain of variables defined in this scope, or `None` if there aren't any.
    vars: Option<Box<Var>>,
    /// Next outer scope. Note that this is _not_ a lexical parent --- variable
    /// lookup never uses this. This is a pointer to the scope that will become
    /// current if this scope returns.
    ///
    /// In the outermost global scope, this is `None`.
    ///
    /// If `proc` support is disabled, this is implicitly always `None`.
    #[cfg(feature = "proc")]
    parent: Option<Box<Scope>>,
}

impl Scope {
    /// Creates a new `Var` with the given `name` and attaches it at the front
    /// of `env`'s var chain.
    ///
    /// This operation is unconditional. If there's already a `Var` named `name`
    /// in `env`, the new one will shadow it. (You almost never want that.)
    ///
    /// Returns a reference to the newly created `Var` so it can be filled in.
    fn add_var(&mut self, name: OwnedValue) -> &mut Var {
        let var = Box::new(Var {
            name,
            value: Box::new([]),
            next: self.vars.take(),
        });
        self.vars.insert(var)
    }
}

/// Shorthand for the type of our boxed command closures.
type FnDyn = dyn Fn(&mut Env, &mut [OwnedValue]) -> Result<OwnedValue, FlowChange>;

/// A command record. Each command that is registered gets one of these,
/// assembled into a chain.
struct Cmd {
    /// Name of the command, used for lookup.
    name: OwnedValue,
    /// Number of arguments the command requires, or `0` if the command can take
    /// varying numbers of arguments. This affects lookup: `x y z` will only
    /// find a command named `"x"` if its `arity` is either 3 or 0.
    arity: usize,
    /// Implementation of the command, as a boxed (reference-counted) closure.
    ///
    /// This is an `Rc` instead of `Box` because we need to be able to separate
    /// its lifetime from the lifetime of the overall `Env` struct during
    /// evaluation, lest we wind up with aliasing. (This also ensures a command
    /// keeps working even if it's deleted or replaced during execution.)
    function: Rc<FnDyn>,
    /// Next command in the chain, or `None` if this is the last one.
    next: Option<Box<Cmd>>,
}

#[cfg(test)]
mod test;
