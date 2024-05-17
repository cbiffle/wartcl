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

/// Integer type used internally for arithmetic.
#[cfg(feature = "i64")]
pub type Int = i64;

/// Integer type used internally for arithmetic.
#[cfg(not(feature = "i64"))]
pub type Int = i32;

/// Interpreter state.
///
/// To run a program, you need one of these. You can create one containing the
/// standard set of commands using `Env::default()`, and then call `eval` as
/// many times as required.
///
/// Dropping it will deallocate all associated state.
pub struct Env {
    scope: Scope,
    cmds: Option<Box<Cmd>>,
}

impl Default for Env {
    /// Creates a new `Env` environment and initializes it with the standard
    /// bundled command set before returning it.
    fn default() -> Self {
        let mut env = Env { scope: Scope::default(), cmds: None };
        cmd::register_all(&mut env);
        env
    }
}

impl Env {
    /// Adds a command to `self`, under the name `name`, expecting `arity`
    /// arguments (including its own name!), and implemented by the Rust
    /// function `function`.
    ///
    /// If a command can handle various numbers of arguments, the `arity` here
    /// should be 0, and the command is responsible for checking argument count
    /// itself.
    pub fn register(
        &mut self,
        name: &Value,
        arity: usize,
        function: impl Fn(&mut Env, &mut [OwnedValue])
            -> Result<OwnedValue, FlowChange> + 'static,
    ) {
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
        // Current string being accumulated out of pieces. We retain this vector
        // across pieces, clear()ing it each time, to reuse its allocation.
        let mut strpieces = Vec::new();
        // Current command being accumulated out of strings. We retain this
        // vector across commands, clear()ing it each time, to reuse its
        // allocation.
        let mut command = Vec::new();

        // Each command we evaluate stores its result here, so that we can
        // return the final one.
        let mut last_result = None;

        let mut p = Tokenizer::new(s);

        loop {
            let tok = p.next();
            match tok {
                // Bounce on any parse failure, aborting execution.
                Some(Token::Error) => return Err(FlowChange::Error),

                // Accumulate string pieces.
                Some(Token::Word(w) | Token::Part(w)) => {
                    strpieces.push(self.subst(w)?);
                    // Word(_) marks the _end_ of a piece, so transfer it to the
                    // command.
                    if matches!(tok, Some(Token::Word(_))) {
                        command.push(flatten_string(&strpieces));
                        strpieces.clear();
                    }
                }

                // Process commands either at a command separator, or the end of
                // the input string.
                Some(Token::CmdSep(_)) | None => {
                    // If we've gotten Parts but not a Word to terminate the
                    // final string, this indicates a bug in this function.
                    debug_assert!(strpieces.is_empty());

                    // Run non-empty command, treating an empty command as a
                    // no-op.
                    if let Some(cmdname) = command.first() {
                        let mut cmd = self.cmds.as_deref();
                        let mut found = false;

                        while let Some(c) = cmd.take() {
                            if &c.name == cmdname
                                && (c.arity == 0 || c.arity == command.len())
                            {
                                found = true;
                                // Command implementations are in Rcs, so that
                                // we can retain an executing command even if it
                                // changes the interpreter's internal state.
                                // Clone this Rc to un-borrow the interpreter.
                                let f = Rc::clone(&c.function);
                                last_result = Some(f(self, &mut command)?);
                                command.clear();
                                break;
                            }

                            cmd = c.next.as_deref();
                        }

                        if !found {
                            return Err(FlowChange::Error);
                        }

                        debug_assert!(command.is_empty());
                    }

                    // Distinguish end-of-input from command separator:
                    if tok.is_none() {
                        break;
                    }
                }
            }
        }

        // If we haven't run any commands, we'll produce the empty string.
        Ok(last_result.unwrap_or_default())
    }

    fn find_var_mut(&mut self, name: &Value) -> Option<&mut Var> {
        let mut var = self.scope.vars.as_mut();
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
        let var = match self.find_var_mut(&name) {
            Some(v) => v,
            None => self.scope.add_var(name),
        };

        var.value = value;
    }

    /// Gets a copy of the contents of an existing variable, or returns
    /// `None` if it doesn't exist.
    pub fn get_existing_var(&mut self, name: &Value) -> Option<OwnedValue> {
        let var = self.find_var_mut(name)?;

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
                // TODO: picked up this shortcut behavior from partcl... this
                // assumes that last char is `}` because the tokenizer will have
                // run before we got here, and the tokenizer validates that.
                // Should this function also validate that? I'm not sure.
                Ok(rest[..rest.len() - 1].into())
            }
            Some((b'$', name)) => {
                // TODO: this behavior is from partcl, and doesn't match real
                // Tcl for code like:
                //
                //      set a b; set b 3; puts $[set a]
                //
                // Which in real Tcl prints "$b" and in partcl prints "3"
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
pub fn int(mut v: &Value) -> Int {
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
                (c - b'a') as Int + 10
            } else {
                (c - b'0') as Int
            };
        }
    } else {
        for &c in v {
            if !c.is_ascii_digit() { break; }

            value = (value * 10) + (c - b'0') as Int;
        }
    }
    if negative { -value } else { value }
}

pub fn int_value(x: Int) -> OwnedValue {
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
    while let Some((first, next)) = s.split_first() {
        if b" \t".contains(first) {
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
            return Some(Token::CmdSep(first));
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
    CmdSep(u8),
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
