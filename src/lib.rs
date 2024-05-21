//! This is an aggressively simple Tcl-like language optimized for binary size,
//! code complexity, and performance, in that order. That is, it's mostly
//! intended to be small, but with readable code and ok performance.
//!
//! `wartcl` has been used on a Cortex-M0 for basic boundary scan and
//! manufacturing test scripting. In that application it required 10 kiB of
//! flash and 8 kiB of RAM.
//!
//! # Putting this in your application
//!
//! `wartcl` is designed to be very easy to embed in a larger application,
//! including exposing custom commands. Here's a toy example:
//!
//! ```rust
//! use wartcl::Val;
//!
//! let mut tcl = wartcl::Env::default();
//!
//! tcl.register(Val::from_static(b"my-custom-command"), 1, |_, _| {
//!     println!("hi!");
//!     Ok(wartcl::empty())
//! });
//!
//! match tcl.eval(Val::from_static(b"my-custom-command\n")) {
//!     Ok(_) => {
//!         // the script worked!
//!     }
//!     Err(e) => panic!("script failed: {e:?}"),
//! }
//! ```
//!
//! # The `wartcl` language
//!
//! The language implemented by `wartcl` is intended to be very close to Tcl,
//! but smaller. Most (all?) `wartcl` programs should be valid Tcl programs, but
//! not vice versa.
//!
//! `wartcl` supports the following Tcl-like commands by default. Some are
//! controlled by a Cargo feature in case you want to disable them.
//!
//! - `break`
//! - `continue`
//! - `+`, `-`, `*`, `/` (feature `arithmetic`)
//! - `>`, `>=`, `<`, `<=`, `==`, `!=` (feature `comparison`)
//! - `if`
//! - `incr` (feature `incr`)
//! - `proc` (feature `proc`)
//! - `puts` (feature `std`)
//! - `return`
//! - `set`
//! - `subst`
//! - `while`
//!
//! Probably the biggest difference is that the `expr` command, which does
//! math-style expression parsing, is not included. You can still do math, but
//! in prefix notation; instead of `expr 2*(3+4)`, you must write `* 2 [+ 3 4]`.
//! This isn't ideal, but expression parsing is _big_ and `wartcl` is small.
//!
//! # Implementation design and theory of operation
//!
//! The Tcl language is an extended meditation on the idea "everything is a
//! string." All of Tcl's data types are --- notionally, at least ---
//! represented as strings, and they can be converted from one to the other by
//! parsing. Modern Tcl implementations provide this illusion while using more
//! efficient representations under the hood.
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

extern crate alloc;
use core::mem;
use alloc::rc::Rc;
use alloc::boxed::Box;
use alloc::{vec, vec::Vec};
pub use heap::Val;

/// Internal macro to make it easier to comment/uncomment a bunch of printlns
/// all in one place.
macro_rules! debug {
    ($($x:tt)*) => { /* println!($($x)*) */ };
}

mod heap;
mod cmd;

/// Integer type used internally for arithmetic.
#[cfg(feature = "i64")]
pub type Int = i64;

/// Integer type used internally for arithmetic.
#[cfg(not(feature = "i64"))]
pub type Int = i32;

/// An instance of the interpreter, the "Tcl machine."
///
/// To run a program, you need one of these. You can create one containing the
/// standard set of commands using `Env::default()`, and then call `eval` as
/// many times as required.
///
/// Dropping it will deallocate all associated state.
pub struct Env {
    cmds: Option<Box<Cmd>>,
    commandstack: Vec<Val>,
    strpiecestack: Vec<Val>,
    varstack: Vec<Var>,
    varframe: usize,
}

impl Default for Env {
    /// Creates a new `Env` environment and initializes it with the standard
    /// bundled command set before returning it.
    fn default() -> Self {
        let mut env = Env {
            cmds: None,
            commandstack: vec![],
            strpiecestack: vec![],
            varstack: vec![],
            varframe: 0,
        };
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
        name: Val,
        arity: usize,
        function: impl Fn(&mut Env, usize)
            -> Result<Val, FlowChange> + 'static,
    ) {
        let next = self.cmds.take();
        self.cmds = Some(Box::new(Cmd {
            name,
            arity,
            function: Rc::new(function),
            next,
        }));
    }

    pub fn stack_mut(&mut self, frame: usize) -> &mut [Val] {
        &mut self.commandstack[frame..]
    }

    /// Evaluates the source code `s` in terms of this interpreter.
    ///
    /// On normal completion, returns the result. Otherwise, returns the change
    /// in flow control.
    pub fn eval(&mut self, s: Val) -> Result<Val, FlowChange> {
        let cmdframe = self.commandstack.len();
        let strframe = self.strpiecestack.len();
        let r = self.eval_(s);
        self.commandstack.truncate(cmdframe);
        self.strpiecestack.truncate(strframe);
        r
    }

    fn eval_(&mut self, s: Val) -> Result<Val, FlowChange> {
        let cmdframe = self.commandstack.len();
        let strframe = self.strpiecestack.len();
        // Each command we evaluate stores its result here, so that we can
        // return the final one.
        let mut last_result = None;

        let mut p = Tokenizer::new(&s);

        loop {
            let tok = p.next();
            match tok {
                // Bounce on any parse failure, aborting execution.
                Some(Token::Error) => return Err(FlowChange::Error),

                // Accumulate string pieces.
                Some(Token::Word(w) | Token::Part(w)) => {
                    let subst_result = match self.subst(Val::slice_ref(&s, w))? {
                        DelayedEval::Ready(v) => v,
                        DelayedEval::EvalThis(v) => self.eval(v)?,
                    };
                    self.strpiecestack.push(subst_result);
                    // Word(_) marks the _end_ of a piece, so transfer it to the
                    // command.
                    if matches!(tok, Some(Token::Word(_))) {
                        self.commandstack.push(flatten_string(&self.strpiecestack[strframe..]));
                        self.strpiecestack.truncate(strframe);
                    }
                }

                // Process commands either at a command separator, or the end of
                // the input string.
                Some(Token::CmdSep(_)) | None => {
                    // If we've gotten Parts but not a Word to terminate the
                    // final string, this indicates a bug in this function.
                    debug_assert!(self.strpiecestack.len() == strframe);

                    // Run non-empty command, treating an empty command as a
                    // no-op.
                    if let Some(cmdname) = self.commandstack.get(cmdframe) {
                        let mut cmd = self.cmds.as_deref();
                        let mut found = false;

                        while let Some(c) = cmd.take() {
                            if &c.name == cmdname
                                && (c.arity == 0 || c.arity == self.commandstack.len() - cmdframe)
                            {
                                found = true;
                                // Command implementations are in Rcs, so that
                                // we can retain an executing command even if it
                                // changes the interpreter's internal state.
                                // Clone this Rc to un-borrow the interpreter.
                                let f = Rc::clone(&c.function);
                                last_result = Some(f(self, cmdframe)?);
                                self.commandstack.truncate(cmdframe);
                                break;
                            }

                            cmd = c.next.as_deref();
                        }

                        if !found {
                            return Err(FlowChange::Error);
                        }

                        debug_assert!(self.commandstack.len() == cmdframe);
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

    fn find_var_mut(&mut self, name: &Val) -> Option<&mut Var> {
        self.varstack[self.varframe..].iter_mut().rev()
            .find(|v| &v.name == name)
    }

    /// Sets a variable named `name` to `value` in the current innermost scope,
    /// creating it if it doesn't exist.
    pub fn set_or_create_var(&mut self, name: &Val, value: Val) {
        match self.find_var_mut(&name) {
            Some(v) => v.value = value,
            None => {
                self.varstack.push(Var {
                    name: name.clone(),
                    value,
                });
            }
        }
    }

    /// Gets a copy of the contents of an existing variable, or returns
    /// `None` if it doesn't exist.
    pub fn get_existing_var(&mut self, name: &Val) -> Option<Val> {
        let var = self.find_var_mut(name)?;

        Some(var.value.clone())
    }

    /// Performs a single substitution step on `s`, returning the result on
    /// success.
    ///
    /// Substitution steps include peeling the outer curly braces off a braced
    /// string, evaluating a square-bracketed subcommand, or processing a
    /// dollar-sign variable splice.
    fn subst(&mut self, s: Val) -> Result<DelayedEval, FlowChange> {
        match s.split_first() {
            None => Ok(DelayedEval::Ready(empty())),
            Some((b'{', b"")) => Err(FlowChange::Error),
            Some((b'{', rest)) => {
                // TODO: picked up this shortcut behavior from partcl... this
                // assumes that last char is `}` because the tokenizer will have
                // run before we got here, and the tokenizer validates that.
                // Should this function also validate that? I'm not sure.
                Ok(DelayedEval::Ready(Val::slice_ref(&s, &rest[..rest.len() - 1])))
            }
            Some((b'$', name)) => {
                // TODO: this behavior is from partcl, and doesn't match real
                // Tcl for code like:
                //
                //      set a b; set b 3; puts $[set a]
                //
                // Which in real Tcl prints "$b" and in partcl prints "3"
                let mut subcmd = Vec::with_capacity(name.len() + b"set ".len());
                subcmd.extend_from_slice(b"set ");
                subcmd.extend_from_slice(name);
                Ok(DelayedEval::EvalThis(subcmd.into()))
            }
            Some((b'[', rest)) => {
                Ok(DelayedEval::EvalThis(Val::slice_ref(&s, &rest[..rest.len() - 1])))
            }
            _ => Ok(DelayedEval::Ready(s)),
        }
    }
}

enum DelayedEval {
    Ready(Val),
    EvalThis(Val),
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
pub fn int(mut v: &[u8]) -> Int {
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

/// Formats an integer as a decimal string.
///
/// There is decimal formatting code in `core`, of course, but it just keeps
/// getting bigger with every toolchain revision. So, we provide our own,
/// optimized for size.
pub fn int_value(x: Int) -> Val {
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
pub fn parse_list(v: Val) -> Vec<Val> {
    let mut words = Vec::new();

    for tok in Tokenizer::new(&v) {
        if let Token::Word(text) = tok {
            words.push(Val::slice_ref(&v, if text[0] == b'{' {
                &text[1..text.len() - 1]
            } else {
                text
            }));
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
    Return(Val),
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

/// Shorthand type for a `Value` that you own.
pub type OwnedValue = Box<Value>;

/// Produces a newly allocated string value that contains all the elements of
/// `v` concatenated together, with no intervening bytes. This operation is
/// useful for pasting strings together during substitution handling.
fn flatten_string(v: &[Val]) -> Val {
    if v.len() == 1 {
        return v[0].clone();
    }
    let len = v.iter().map(|component| component.len()).sum::<usize>();
    let mut out = Vec::with_capacity(len);
    for component in v {
        out.extend_from_slice(component);
    }
    out.into()
}

/// Convenience function for getting an empty value.
pub fn empty() -> Val {
    Val::new()
}

/// Updates `s` by stripping off leading (horizontal) whitespace characters.
fn skip_leading_whitespace(s: &mut &[u8]) {
    while let Some((first, next)) = s.split_first() {
        if b" \t".contains(first) {
            *s = next;
        } else {
            break;
        }
    }
}

/// The input tokenizer, exposed mostly because it can be useful for building a
/// REPL.
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

/// A token, produced by the `Tokenizer`.
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
    name: Val,
    /// Contents of the variable.
    value: Val,
}

/// Shorthand for the type of our boxed command closures.
type FnDyn = dyn Fn(&mut Env, usize) -> Result<Val, FlowChange>;

/// A command record. Each command that is registered gets one of these,
/// assembled into a chain.
struct Cmd {
    /// Name of the command, used for lookup.
    name: Val,
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
