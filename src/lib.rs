use std::{mem, rc::Rc};

macro_rules! debug {
    ($($x:tt)*) => {
        //println!($($x)*)
    };
}

fn is_special(c: u8, q: bool) -> bool {
    (!q && b"{};\r\n".contains(&c)) || b"$[]\"".contains(&c)
}

fn is_space(c: u8) -> bool { b" \t".contains(&c) }

fn is_end(c: u8) -> bool { b"\n\r;".contains(&c) }

type Value = [u8];

fn int(v: &[u8]) -> i32 {
    std::str::from_utf8(v)
        .ok()
        .and_then(|s| s.parse::<i32>().ok())
        .unwrap_or(0)
}

fn append_string(v: Option<Box<Value>>, s: &Value) -> Box<Value> {
    let mut v = v.map(Vec::from).unwrap_or_default();
    v.extend_from_slice(s); 
    v.into()
}

fn list_alloc() -> Box<Value> {
    Box::new([])
}

fn empty() -> Box<Value> {
    Box::new([])
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Token {
    Cmd,
    Word,
    Part,
    Error,
}

fn next<'data>(mut s: &'data [u8], q: &mut bool) -> (Token, &'data [u8], &'data [u8]) {
    //debug!("tcl_next({}, {})", String::from_utf8_lossy(s), *q);
    if !*q {
        // skip leading spaces
        while !s.is_empty() && is_space(s[0]) {
            s = &s[1..];
        }
    }

    /*
    if s.is_empty() {
        return (Token::Cmd, &[], &[]);
    }
    */

    if !*q && s.first().map(|&c| is_end(c)).unwrap_or(false) {
        let (before, after) = s.split_at(1);
        return (Token::Cmd, before, after);
    }

    if s.first().map(|&c| c == b'$').unwrap_or(false) {
        // variable token, must not start with a space or quote
        if s.get(1).map(|&c| is_space(c) || c == b'"').unwrap_or(false) {
            return (Token::Error, s, &[]);
        }
        let mode = *q;
        *q = false;
        let (subtoken, subused, subrest) = next(&s[1..], q);
        *q = mode;
        return (
            if subtoken == Token::Word && *q { Token::Part } else { subtoken },
            &s[..subused.len() + 1],
            subrest,
        );
    }

    let i = if let Some(open) = s.first().copied() {
        //debug!("{open:?}");
        if open == b'[' || (!*q && open == b'{') {
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
            *q = !*q;

            // *from = *to = s + 1;
            let from = &[];
            let to = &s[1..];

            if *q {
                return (Token::Part, from, to);
            }
            // Character immediately after the quote must be space or
            // terminator.
            if to.len() < 1 || (!is_space(to[0]) && !is_end(to[0])) {
                return (Token::Error, from, to);
            }
            return (Token::Word, from, to);
        } else if open == b']' || open == b'}' {
            // unbalanced bracket or brace
            return (Token::Error, s, &[]);
        } else {
            s.iter().position(|&c| !((*q || !is_space(c)) && !is_special(c, *q))).unwrap_or(s.len())
        }
    } else {
        0
    };
    let (from, to) = s.split_at(i);
    let token = if let Some(&first) = to.first() {
        if *q {
            Token::Part
        } else if is_space(first) || is_end(first) {
            Token::Word
        } else {
            Token::Part
        }
    } else {
        Token::Error
    };
    (token, from, to)
}

pub struct Parser<'a> {
    text: &'a [u8],
    q: bool,
}

impl<'a> Parser<'a> {
    pub fn new(text: &'a [u8]) -> Self {
        Self {
            text,
            q: false,
        }
    }

    pub fn at_end(&self) -> bool {
        self.text.is_empty()
    }

    pub fn next(&mut self, skiperr: bool) -> Option<(Token, &'a [u8])> {
        if self.text.is_empty() {
            return None;
        }
        let (tok, from, to) = next(self.text, &mut self.q);
        //debug!("({tok:?}, {}, {})", String::from_utf8_lossy(from), String::from_utf8_lossy(to));
        if !skiperr && tok == Token::Error {
            return None;
        }
        self.text = to;
        Some((tok, from))
    }
}

fn list_length(v: &[u8]) -> usize {
    debug!("list length...");
    let mut count = 0;
    let mut p = Parser::new(v);
    while let Some((tok, _)) = p.next(false) {
        if tok == Token::Word {
            count += 1;
        }
    }
    if !v.is_empty() {
        count += 1;
    }
    debug!("list length is {count}");
    count
}

fn list_at(v: &[u8], index: usize) -> Option<Box<Value>> {
    let mut i = 0;
    let mut p = Parser::new(v);
    let mut rest = v;
    while let Some((tok, from)) = p.next(false) {
        rest = p.text;
        if tok == Token::Word {
            if i == index {
                if from[0] == b'{' {
                    return Some(from[1..from.len() - 1].into());
                } else {
                    return Some(from.into());
                }
            }
            i += 1;
        }
    }
    if i == index {
        while !rest.is_empty() {
            if is_space(rest[0]) {
                rest = &rest[1..];
            } else {
                break;
            }
        }

        if !rest.is_empty() {
            if rest[0] == b'{' {
                return Some(rest[1..rest.len() - 1].into());
            } else {
                return Some(rest.into());
            }
        }
    }
    None
}

fn list_append(v: Box<Value>, tail: &[u8]) -> Box<Value> {
    let mut v = if !v.is_empty() {
        append_string(Some(v), b" ")
    } else {
        v
    };

    if !tail.is_empty() {
        let q = tail.iter().any(|&p| is_space(p) || is_special(p, false));
        if q {
            v = append_string(Some(v), b"{");
        }
        v = append_string(Some(v), tail);
        if q {
            v = append_string(Some(v), b"}");
        }
    } else {
        v = append_string(Some(v), b"{}");
    }

    v
}

struct Var {
    name: Box<Value>,
    value: Box<Value>,
    next: Option<Box<Var>>,
}

#[derive(Default)]
struct Env {
    vars: Option<Box<Var>>,
    parent: Option<Box<Env>>,
}

struct Cmd {
    name: Box<Value>,
    arity: usize,
    function: Rc<dyn Fn(&mut Tcl, &[u8]) -> Flow>,
    next: Option<Box<Cmd>>,
}

fn env_alloc(parent: Option<Box<Env>>) -> Box<Env> {
    Box::new(Env {
        vars: None,
        parent,
    })
}

fn env_var(env: &mut Env, name: Box<Value>) -> &mut Var {
    let next = env.vars.take();
    let var = Box::new(Var {
        name,
        value: Box::new([]),
        next,
    });
    env.vars.insert(var)
}

fn env_free(mut env: Box<Env>) -> Option<Box<Env>> {
    env.parent.take()
}

pub struct Tcl {
    env: Box<Env>,
    cmds: Option<Box<Cmd>>,
    pub result: Box<Value>,
}

// N.B. The mandatory allocation here (for the result) is weird.
fn var(tcl: &mut Tcl, name: Box<Value>, value: Option<Box<Value>>) -> Box<Value> {
    let mut var = tcl.env.vars.as_mut();
    while let Some(v) = var.take() {
        if v.name == name {
            var = Some(v);
            break;
        }
        var = v.next.as_mut();
    }
    let var = match var {
        Some(v) => v,
        None => env_var(&mut tcl.env, name),
    };

    if let Some(value) = value {
        var.value = value;
    }

    var.value.clone()
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Flow {
    Error,
    Normal,
    Return,
    Break,
    Again,
}

fn result(tcl: &mut Tcl, flow: Flow, value: Box<Value>) -> Flow {
    tcl.result = value;
    flow
}

fn subst(tcl: &mut Tcl, s: &[u8]) -> Flow {
    match s.split_first() {
        None => result(tcl, Flow::Normal, Box::new([])),
        Some((b'{', b"")) => result(tcl, Flow::Error, Box::new([])),
        Some((b'{', rest)) => {
            result(tcl, Flow::Normal, rest[..rest.len() - 1].into())
        }
        Some((b'$', name)) => {
            let mut subcmd = b"set ".to_vec();
            subcmd.extend_from_slice(name);
            subcmd.push(b'\n');
            eval(tcl, &subcmd)
        }
        Some((b'[', rest)) => {
            // ugh TODO
            let mut rest = rest[..rest.len() - 1].to_vec();
            rest.push(b'\n');
            eval(tcl, &rest)
        }
        _ => result(tcl, Flow::Normal, s.into()),
    }
}

pub fn eval(tcl: &mut Tcl, s: &[u8]) -> Flow {
    debug!("eval({:?})", String::from_utf8_lossy(s));
    let mut p = Parser::new(s);

    let mut cur = None;
    let mut list = list_alloc();

    while let Some((tok, from)) = p.next(true) {
        match tok {
            Token::Error => return result(tcl, Flow::Error, Box::new([])),

            Token::Word => {
                // N.B. result ignored in original
                subst(tcl, from);
                cur = Some(append_string(cur.take(), &tcl.result));
                list = list_append(list, cur.as_ref().unwrap());
                cur = None;
            }

            Token::Part => {
                subst(tcl, from);
                cur = Some(append_string(cur.take(), &tcl.result));
            }
            Token::Cmd => {
                let n = list_length(&list);
                debug!("list = {:?} ({n})", String::from_utf8_lossy(&list));
                if n == 0 {
                    debug!("Cmd with zero length list");
                    result(tcl, Flow::Normal, empty());
                } else {
                    debug!("Cmd with proper list");
                    let cmdname = list_at(&list, 0).unwrap(); // N.B. lolwut
                    debug!("finding: {}/{}", String::from_utf8_lossy(&cmdname), n);
                    let mut cmd = tcl.cmds.as_deref();
                    let mut r = Flow::Error;
                    while let Some(c) = cmd.take() {
                        if c.name == cmdname && (c.arity == 0 || c.arity == n) {
                            debug!("calling: {}/{}", String::from_utf8_lossy(&c.name), c.arity);
                            let f = Rc::clone(&c.function);
                            r = f(tcl, &list);
                            break;
                        }

                        cmd = c.next.as_deref();
                    }
                    if r != Flow::Normal {
                        debug!("---- oh noes: {r:?}");
                        return r;
                    }
                    debug!("normal");
                    // Reset command list
                    list = list_alloc();
                }
            }
        }
    }

    debug!("end eval");
    Flow::Normal
}





fn register(tcl: &mut Tcl, name: &[u8], arity: usize, function: impl Fn(&mut Tcl, &[u8]) -> Flow + 'static) {
    let next = tcl.cmds.take();
    tcl.cmds = Some(Box::new(Cmd {
        name: name.into(),
        arity,
        function: Rc::new(function),
        next,
    }));
}


fn cmd_set(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let name = list_at(args, 1).unwrap();
    let val = list_at(args, 2);

    let v = var(tcl, name, val);
    result(tcl, Flow::Normal, v)
}

fn cmd_subst(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let s = list_at(args, 1).unwrap();
    subst(tcl, &s)
}

fn cmd_puts(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let str = list_at(args, 1).unwrap();
    println!("{}", String::from_utf8_lossy(&str));
    result(tcl, Flow::Normal, str)
}

fn cmd_proc(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let name = list_at(args, 1).unwrap();
    let args: Box<Value> = args.into();
    register(tcl, &name, 0, move |tcl, act_args| {
        let params = list_at(&args, 2).unwrap();
        let body = list_at(&args, 3).unwrap();

        tcl.env = env_alloc(Some(mem::take(&mut tcl.env)));

        for i in 0..list_length(&params) {
            let param = list_at(&params, i).unwrap();
            let v = list_at(act_args, i + 1).unwrap();
            var(tcl, param, v.into());
        }
        let mut body = Vec::from(body);
        body.push(b'\n');
        eval(tcl, &body);

        let parent_env = tcl.env.parent.take().unwrap();
        tcl.env = parent_env;

        Flow::Normal
    });
    result(tcl, Flow::Normal, empty())
}

fn cmd_if(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let n = list_length(args);
    let mut r = Flow::Normal;
    let mut i = 1;
    while i < n {
        let cond = list_at(args, i).unwrap();
        let branch = if i + 1 < n {
            list_at(args, i + 1)
        } else {
            None
        };
        let mut cond = Vec::from(cond);
        cond.push(b'\n');
        r = eval(tcl, &cond);
        if r != Flow::Normal {
            break;
        }
        if int(&tcl.result) != 0 {
            let mut branch = Vec::from(branch.unwrap());
            branch.push(b'\n');
            r = eval(tcl, &branch);
            break;
        }

        i += 2;
    }
    r
}

fn cmd_while(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let cond = list_at(args, 1).unwrap();
    let mut cond = Vec::from(cond);
    cond.push(b'\n');
    let body = list_at(args, 2).unwrap();
    let mut body = Vec::from(body);
    body.push(b'\n');
    debug!("while body = {:?}", String::from_utf8_lossy(&body));
    loop {
        let r = eval(tcl, &cond);
        if r != Flow::Normal {
            return r;
        }
        if int(&tcl.result) == 0 {
            return Flow::Normal;
        }
        let r = eval(tcl, &body);
        match r {
            Flow::Again | Flow::Normal => (),

            Flow::Break => return Flow::Normal,
            Flow::Return => return Flow::Return,
            Flow::Error => return Flow::Error,
        }
    }
}

fn cmd_math(tcl: &mut Tcl, args: &[u8]) -> Flow {
    let opval = list_at(args, 0).unwrap();
    let aval = list_at(args, 1).unwrap();
    let bval = list_at(args, 2).unwrap();

    let a = int(&aval);
    let b = int(&bval);

    let c = match &*opval {
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
        _ => panic!("unknown math operator: {:?}", String::from_utf8_lossy(&opval)),
    };

    let p = c.to_string().into_boxed_str().into_boxed_bytes();
    result(tcl, Flow::Normal, p)
}

pub fn init() -> Tcl {
    let env = env_alloc(None);

    let mut tcl = Tcl {
        env,
        cmds: None,
        result: empty(),
    };

    register(&mut tcl, b"set", 0, cmd_set);
    register(&mut tcl, b"puts", 2, cmd_puts);
    register(&mut tcl, b"subst", 2, cmd_subst);
    register(&mut tcl, b"proc", 4, cmd_proc);
    register(&mut tcl, b"if", 0, cmd_if);
    register(&mut tcl, b"while", 3, cmd_while);

    register(&mut tcl, b"break", 1, |_, _| Flow::Break);
    register(&mut tcl, b"continue", 1, |_, _| Flow::Again);
    register(&mut tcl, b"return", 0, |tcl, args| result(tcl, Flow::Return, list_at(args, 1).unwrap_or_default()));

    let ops: [&[u8]; 10] = [b"+", b"-", b"*", b"/", b">", b">=", b"<", b"<=", b"==", b"!="];
    for op in ops {
        register(&mut tcl, op, 3, cmd_math);
    }
    tcl
}


#[cfg(test)]
mod test {
    use super::*;

    #[track_caller]
    fn check_tokens(input: &[u8], expect: &[(Token, &[u8])]) {
        let mut p = Parser::new(input);
        let expect_count = expect.len();
        let mut expect = expect.iter().enumerate();
        let mut found = 0;
        while let Some((tok, text)) = p.next(true) {
            found += 1;
            let (ex_i, &(ex_tok, ex_text)) = expect.next()
                .expect("more tokens in input than expected");
            assert_eq!(tok, ex_tok,
                       "wrong token for expected text at {ex_i}: {:?} (got: {:?})",
                       String::from_utf8_lossy(ex_text),
                       String::from_utf8_lossy(text));
            match tok {
                Token::Error => {
                    break; // ???
                }
                Token::Part | Token::Word => {
                    assert_eq!(text, ex_text,
                            "got {:?}, expected {:?}",
                            String::from_utf8_lossy(text),
                            String::from_utf8_lossy(ex_text),
                            );
                }
                Token::Cmd => (), // ???
            }
        }
        let input = String::from_utf8_lossy(input);
        if found != expect_count {
            panic!("Expected {expect_count} tokens, found {found}: {input:?}");
        } else {
            println!("OK: {input:?}");
        }

    }

    #[test]
    fn lexer_tests() {
        // So, the original lexer inherently relies on the ability to read past
        // the end of the strings it's passed. It will find a 0 there if the
        // string is separately allocated, or a different "end" character if
        // not. (Close bracket is not treated as an end character, and so the
        // system also relies on allocating copies of substituted commands.)
        //
        // I'm not willing to recreate this behavior, so I've changed these test
        // cases. To preserve the incremental parse behavior of the original,
        // I'm using other command-terminating bytes to indicate a complete
        // command. Generally a \n replaces the original \0.
        //
        // Note that no tests in the original use a zero-byte string. This is
        // probably good because I'm pretty sure the lexer can't handle them.

        check_tokens(b"\n", &[(Token::Cmd, b"")]);
        check_tokens(b";\n", &[
            (Token::Cmd, b";"),
            (Token::Cmd, b""),
        ]);
        check_tokens(b";;;  ;\n", &[
            (Token::Cmd, b";"),
            (Token::Cmd, b";"),
            (Token::Cmd, b";"),
            (Token::Cmd, b";"),
            (Token::Cmd, b""),
        ]);

        // Regular words
        check_tokens(b"foo\n", &[(Token::Word, b"foo"), (Token::Cmd, b"")]);
        check_tokens(b"foo bar\n", &[(Token::Word, b"foo"), (Token::Word, b"bar"), (Token::Cmd, b"")]);
        check_tokens(b"foo bar baz\n", &[(Token::Word, b"foo"), (Token::Word, b"bar"), (Token::Word, b"baz"), (Token::Cmd,
                                                                                                               b"")]);
        /* Imbalanced braces/brackets */
        check_tokens(b"foo ]\n", &[(Token::Word, b"foo"), (Token::Error, b"")]);
        check_tokens(b"foo }\n", &[(Token::Word, b"foo"), (Token::Error, b"")]);

        /* Grouping */
        check_tokens(b"foo {bar baz}\n", &[(Token::Word, b"foo"), (Token::Word, b"{bar baz}"), (Token::Cmd, b"")]);
        check_tokens(b"foo {bar {baz} {q u x}}\n", &[(Token::Word, b"foo"), (Token::Word,
                                                                             b"{bar {baz} {q u x}}"), (Token::Cmd, b"")]);
        check_tokens(b"foo {bar {baz} [q u x]}\n", &[(Token::Word, b"foo"), (Token::Word,
                                                                             b"{bar {baz} [q u x]}"), (Token::Cmd, b"")]);
        check_tokens(b"foo {bar $baz [q u x]}\n", &[(Token::Word, b"foo"), (Token::Word,
                                                                            b"{bar $baz [q u x]}"), (Token::Cmd, b"")]);
        check_tokens(b"foo {bar \" baz}\n", &[(Token::Word, b"foo"), (Token::Word, b"{bar \" baz}"), (Token::Cmd,
                                                                                                      b"")]);
        check_tokens(b"foo {\n\tbar\n}\n", &[(Token::Word, b"foo"), (Token::Word, b"{\n\tbar\n}"), (Token::Cmd,
                                                                                                    b"")]);
        /* Substitution */
        check_tokens(b"foo [bar baz]\n", &[(Token::Word, b"foo"), (Token::Word, b"[bar baz]"), (Token::Cmd, b"")]);
        check_tokens(b"foo [bar {baz}]\n", &[(Token::Word, b"foo"), (Token::Word, b"[bar {baz}]"), (Token::Cmd,
                                                                                                    b"")]);
        check_tokens(b"foo $bar $baz\n", &[
                (Token::Word, b"foo"),
                (Token::Word, b"$bar"),
                (Token::Word, b"$baz"),
                (Token::Cmd, b""),
        ]);
        check_tokens(b"foo $bar$baz\n", &[(Token::Word, b"foo"), (Token::Part, b"$bar"), (Token::Word, b"$baz"),
        (Token::Cmd, b"")]);
        check_tokens(b"foo ${bar baz}\n", &[(Token::Word, b"foo"), (Token::Word, b"${bar baz}"), (Token::Cmd,
                                                                                                  b"")]);
        check_tokens(b"puts hello[\n]world\n", &[(Token::Word, b"puts"), (Token::Part, b"hello"), (Token::Part,
                                                                                                   b"[\n]"), (Token::Word, b"world"), (Token::Cmd, b"")]);
        /* Quotes */
        check_tokens(b"\"\"\n", &[
            (Token::Part, b""),
            (Token::Word, b""),
            (Token::Cmd, b""),
        ]);
        check_tokens(b"\"\"\"\"\n", &[(Token::Part, b""), (Token::Error, b"")]);
        check_tokens(b"foo \"bar baz\"\n", &[(Token::Word, b"foo"), (Token::Part, b""), (Token::Part, b"bar baz"),
        (Token::Word, b""), (Token::Cmd, b"")]);
        check_tokens(b"foo \"bar $b[a z]\" qux\n", &[(Token::Word, b"foo"), (Token::Part, b""), (Token::Part, b"bar "), (Token::Part, b"$b"), (Token::Part, b"[a z]"), (Token::Word, b""), (Token::Word, b"qux"),
        (Token::Cmd, b"")]);
        check_tokens(b"foo \"bar baz\" \"qux quz\"\n", &[(Token::Word, b"foo"), (Token::Part, b""), (Token::Part,
                                                                                                     b"bar baz"), (Token::Word, b""), (Token::Part, b""), (Token::Part, b"qux quz"), (Token::Word, b""),
                                                                                                     (Token::Cmd, b"")]);
        check_tokens(b"\"{\" \"$a$b\"\n", &[(Token::Part, b""), (Token::Part, b"{"), (Token::Word, b""), (Token::Part, b""),
        (Token::Part, b"$a"), (Token::Part, b"$b"), (Token::Word, b""), (Token::Cmd, b"")]);

        check_tokens(b"\"{\" \"$a\"$b\n", &[
            (Token::Part, b""),
            (Token::Part, b"{"),
            (Token::Word, b""),
            (Token::Part, b""),
            (Token::Part, b"$a"),
            (Token::Error, b""),
        ]);
        check_tokens(b"\"$a + $a = ?\"\n", &[
            (Token::Part, b""),
            (Token::Part, b"$a"),
            (Token::Part, b" + "),
            (Token::Part, b"$a"),
            (Token::Part, b" = ?"),
            (Token::Word, b""),
            (Token::Cmd, b""),
        ]);

        /* Variables */
        check_tokens(b"puts $ a\n", &[(Token::Word, b"puts"), (Token::Error, b"")]);
        check_tokens(b"puts $\"a b\"\n", &[(Token::Word, b"puts"), (Token::Error, b"")]);
        check_tokens(b"puts $$foo\n", &[(Token::Word, b"puts"), (Token::Word, b"$$foo"), (Token::Cmd, b"")]);
        check_tokens(b"puts ${a b}\n", &[(Token::Word, b"puts"), (Token::Word, b"${a b}"), (Token::Cmd, b"")]);
        check_tokens(b"puts $[a b]\n", &[(Token::Word, b"puts"), (Token::Word, b"$[a b]"), (Token::Cmd, b"")]);
        check_tokens(b"puts { \n", &[(Token::Word, b"puts"), (Token::Error, b"")]);
        check_tokens(b"set a {\n\n", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
        check_tokens(b"puts {[}\n", &[(Token::Word, b"puts"), (Token::Word, b"{[}"), (Token::Cmd, b"")]);
        check_tokens(b"puts [{]\n", &[(Token::Word, b"puts"), (Token::Word, b"[{]"), (Token::Cmd, b"")]);
        check_tokens(b"puts {[}{]} \n", &[(Token::Word, b"puts"), (Token::Part, b"{[}"), (Token::Word, b"{]}"),
        (Token::Cmd, b"")]);

      /* Strings without trailing ~zero~newline */
      check_tokens(b"a", &[(Token::Error, b"a")]);
      check_tokens(b"ab", &[(Token::Error, b"a")]);
      check_tokens(b"abc", &[(Token::Error, b"a")]);
      check_tokens(b"abc ", &[(Token::Word, b"abc"), (Token::Error, b"")]);
      check_tokens(b"abc foo", &[(Token::Word, b"abc"), (Token::Error, b"")]);
      check_tokens(b"abc foo\n", &[(Token::Word, b"abc"), (Token::Word, b"foo"), (Token::Cmd, b"")]);

      check_tokens(b"s", &[(Token::Error, b"s")]);
      check_tokens(b"se", &[(Token::Error, b"s")]);
      check_tokens(b"set", &[(Token::Error, b"s")]);
      check_tokens(b"set ", &[(Token::Word, b"set"), (Token::Error, b"")]);
      check_tokens(b"set a", &[(Token::Word, b"set"), (Token::Error, b"")]);
      check_tokens(b"set a ", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\n", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nh", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhe", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhel", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhell", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhello", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhello\n", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhello\n}", &[(Token::Word, b"set"), (Token::Word, b"a"), (Token::Error, b"")]);
      check_tokens(b"set a {\nhello\n}\n", &[
            (Token::Word, b"set"),
            (Token::Word, b"a"),
            (Token::Word, b"{\nhello\n}"),
            (Token::Cmd, b""),
        ]);
    }

    #[track_caller]
    fn check_eval(tcl: Option<&mut Tcl>, s: &[u8], expected: &[u8]) {
        // Ensure termination
        let mut s = s.to_vec();
        s.push(b'\n');
        let s = &s[..];

        let mut local = None;
        let tcl = if let Some(outer) = tcl {
            outer
        } else {
            local.insert(init())
        };

        if eval(tcl, s) == Flow::Error {
            panic!("eval returned error: {:?}, ({:?})",
                String::from_utf8_lossy(&tcl.result),
                String::from_utf8_lossy(s));
        }
        assert_eq!(&*tcl.result, expected,
            "expected result {:?} but got {:?}",
            String::from_utf8_lossy(expected),
            String::from_utf8_lossy(&tcl.result));
        
        println!("OK: {:?} -> {:?}",
                 String::from_utf8_lossy(s),
                 String::from_utf8_lossy(expected));
    }

    #[test]
    fn test_subst() {
        // N.B. for these commands, the test framework will append the
        // terminating character to make the damn lexer happy.

        check_eval(None, b"subst hello", b"hello");
        check_eval(None, b"subst {hello}", b"hello");
        check_eval(None, b"subst {hello world}", b"hello world");
        check_eval(None, b"subst {hello {world}}", b"hello {world}");

        check_eval(None, b"subst $foo", b"");

        if false { // TODO
            let mut tcl = init();
            var(&mut tcl, (*b"foo").into(), Some((*b"bar").into()));
            var(&mut tcl, (*b"bar").into(), Some((*b"baz").into()));
            var(&mut tcl, (*b"baz").into(), Some((*b"Hello").into()));
            check_eval(Some(&mut tcl), b"subst $foo", b"bar");
            check_eval(Some(&mut tcl), b"subst $foo[]$foo", b"barbar");
            check_eval(Some(&mut tcl), b"subst $$foo", b"baz");
            check_eval(Some(&mut tcl), b"subst [set $foo]", b"baz");
            check_eval(Some(&mut tcl), b"subst $[set $foo]", b"Hello");
            check_eval(Some(&mut tcl), b"subst $$$foo", b"Hello");
        }

        check_eval(None, b"subst {hello}{world}", b"helloworld");
        check_eval(None, b"subst hello[subst world]", b"helloworld");
        check_eval(None, b"subst hello[\n]world", b"helloworld");

        
        /* Example from Picol */
        check_eval(None, b"set a su; set b bst; $a$b Hello", b"Hello");
        /* This is an error in TCL, but works in Picol */
        check_eval(None, b"set foo {hello world}", b"hello world");
        check_eval(None,
                   b"set foo {hello world}; set bar \"qux $foo\"; subst $foo$bar",
                   b"hello worldqux hello world");
        check_eval(None, b"set a f; set b {o}; set $a$b$b [subst \"hello\"]; set foo",
                   b"hello");
        check_eval(None, b"set {a \"b\"} hello; subst ${a \"b\"}", b"hello");
        check_eval(None, b"set \"a b\" hello; subst ${a b}", b"hello");

        check_eval(None, b"set q {\"}; set msg hello; subst $q$msg$q", b"\"hello\"");
        check_eval(None, b"set q {\"}; subst $q[]hello[]$q", b"\"hello\"");
        check_eval(None, b"set x {\n\thello\n}", b"\n\thello\n");

        /* Some puts commands */
        check_eval(None, b"puts {[}[]hello[]{]}", b"[hello]");
        check_eval(None, b"puts {{hello}}", b"{hello}");
    }

    #[test]
    fn test_flow() {
        check_eval(None, b"if {< 1 2} {puts A} {puts B}", b"A");
        check_eval(None, b"if {> 1 2} {puts A} {puts B}", b"B");
        check_eval(None, b"if {> 1 2} {puts A}", b"0");

        check_eval(None,
                   b"set x 0; if {== $x 0} {subst A} {== $x 1} {subst B} {subst C}",
                   b"A");
        check_eval(None,
                   b"set x 1; if {== $x 0} {subst A} {== $x 1} {subst B} {subst C}",
                   b"B");
        check_eval(None,
                   b"set x 2; if {== $x 0} {subst A} {== $x 1} {subst B} {subst C}",
                   b"C");

        check_eval(None, b"while {< $x 5} {set x [+ $x 1]}", b"0");
        check_eval(None, b"while {== 1 1} {set x [+ $x 1]; if {== $x 5} {break}}",
                   b"break");
        check_eval(
            None,
            b"while {== 1 1} {set x [+ $x 1]; if {!= $x 5} {continue} ; return foo}",
            b"foo");
        check_eval(None, b"proc foo {} { subst hello }; foo", b"hello");
        check_eval(None, b"proc five {} { + 2 3}; five", b"5");
        check_eval(None, b"proc foo {a} { subst $a }; foo hello", b"hello");
        check_eval(None, b"proc foo {} { subst hello; return A; return B;}; foo", b"A");
        check_eval(None, b"set x 1; proc two {} { set x 2;}; two; subst $x", b"1");
        /* Example from Picol */
        check_eval(None, b"proc fib {x} { if {<= $x 1} {return 1} \
                   { return [+ [fib [- $x 1]] [fib [- $x 2]]]}}; fib 20",
                   b"10946");

        let mut tcl = init();
        check_eval(Some(&mut tcl), b"proc square {x} { * $x $x }; square 7", b"49");
        check_eval(Some(&mut tcl), b"set a 4", b"4");
        check_eval(Some(&mut tcl), b"square $a", b"16");
        check_eval(Some(&mut tcl), b"subst \"$a[]*$a ?\"", b"4*4 ?");
        check_eval(Some(&mut tcl), b"subst \"I can compute that $a[]x$a = [square $a]\"",
                   b"I can compute that 4x4 = 16");
        check_eval(Some(&mut tcl), b"set a 1", b"1");
        check_eval(Some(&mut tcl), b"while {<= $a 10} { puts \"$a [== $a 5]\";\
                   if {== $a 5} { puts {Missing five!}; set a [+ $a 1]; \
                   continue;}; puts \"I can compute that $a[]x$a = [square \
                   $a]\" ; set a [+ $a 1]}",
                   b"0");
        drop(tcl);
    }
    
    #[test]
    fn test_math() {
        check_eval(None, b"< 1 2", b"1");
        check_eval(None, b"< 1 1", b"0");
        check_eval(None, b"<= 1 1", b"1");
        check_eval(None, b"> 1 2", b"0");
        check_eval(None, b"> 1 1", b"0");
        check_eval(None, b">= 1 1", b"1");
        check_eval(None, b"== 1 1", b"1");
        check_eval(None, b"!= 1 1", b"0");

        check_eval(None, b"+ 1 2", b"3");
        check_eval(None, b"* 4 2", b"8");
        check_eval(None, b"- 7 2", b"5");
        check_eval(None, b"/ 7 2", b"3");

        check_eval(None, b"set a 5;set b 7; subst [- [* 4 [+ $a $b]] 6]", b"42");
    }
}
