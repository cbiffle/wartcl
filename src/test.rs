// Changes made to the test cases here are as follows.
//
// # Trailing newlines
//
// The original lexer inherently relies on the ability to read past the end of
// the strings it's passed. It will find a 0 there if the string is separately
// allocated, or a different "end" character if not. (Close bracket is not
// treated as an end character, and so the system also relies on allocating
// copies of substituted commands.)
//
// I'm not willing to recreate this behavior, so I've changed these test cases.
// To preserve the incremental parse behavior of the original, I'm using other
// command-terminating bytes to indicate a complete command. Generally a \n
// replaces the original \0.
//
// Note that no tests in the original use a zero-byte string. This is probably
// good because I'm pretty sure the original lexer can't handle them.
//
//
// # if/else syntax
//
// The original system doesn't support the 'else' and 'elseif' tokens in the if
// command. I've fixed this, which has required patching the test cases to use
// them.
//
//
// # Checking error cases
//
// The original tests has basically no validation of error behavior, which let
// several subtle bugs sneak through (either in their implementation, or in my
// reimplementation). The check_eval_err tests fix this.

use core::cell::RefCell;

use super::*;

#[track_caller]
fn check_tokens(input: &[u8], expect: &[Token]) {
    let p = Tokenizer::new(input);
    let expect_count = expect.len();
    let mut expect = expect.iter().enumerate();
    let mut found = 0;
    for tok in p {
        found += 1;
        let Some((ex_i, &ex_tok)) = expect.next() else {
            panic!("found more tokens in input than expected, starting with: {tok:?}");
        };
        assert_eq!(
            tok,
            ex_tok,
            "at token {ex_i}: expected {ex_tok:?}, got: {tok:?}",
        );
        if tok == Token::Error {
            // Don't test behavior after an error token
            break;
        }
    }
    let input = String::from_utf8_lossy(input);
    if found != expect_count {
        panic!("Expected {expect_count} tokens, found {found}: {input:?}");
    } else {
        println!("OK: {input:?}");
    }
}

fn sep<'a>(c: u8) -> Token<'a> { Token::CmdSep(c) }
fn text_incomplete(t: &[u8]) -> Token<'_> { Token::WordPart(t, PartRole::Text, false) }
fn text(t: &[u8]) -> Token<'_> { Token::WordPart(t, PartRole::Text, true) }
fn script_incomplete(t: &[u8]) -> Token<'_> { Token::WordPart(t, PartRole::Script, false) }
fn script(t: &[u8]) -> Token<'_> { Token::WordPart(t, PartRole::Script, true) }
fn var_incomplete(t: &[u8]) -> Token<'_> { Token::WordPart(t, PartRole::VarName, false) }
fn var(t: &[u8]) -> Token<'_> { Token::WordPart(t, PartRole::VarName, true) }

#[test]
fn test_0_lexer2() {
    check_tokens(b"", &[]);
    check_tokens(b"\n", &[sep(b'\n')]);
    check_tokens(b";\n", &[sep(b';'), Token::CmdSep(b'\n')]);
    check_tokens(
        b";;;  ;\n",
        &[
            sep(b';'),
            sep(b';'),
            sep(b';'),
            sep(b';'),
            sep(b'\n'),
        ],
    );

    // Regular words
    check_tokens(b"foo", &[text(b"foo")]);
    check_tokens(
        b"foo bar",
        &[
            text(b"foo"),
            text(b"bar"),
        ],
    );
    check_tokens(
        b"foo bar\n",
        &[
            text(b"foo"),
            text(b"bar"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo bar baz\n",
        &[
            text(b"foo"),
            text(b"bar"),
            text(b"baz"),
            sep(b'\n'),
        ],
    );
    // Variable substitution: easy case, whitespace separated, basically just
    // words.
    check_tokens(
        b"foo $bar $baz",
        &[
            text(b"foo"),
            var(b"bar"),
            var(b"baz"),
        ],
    );
    check_tokens(
        b"foo $bar$baz\n",
        &[
            text(b"foo"),
            var_incomplete(b"bar"),
            var(b"baz"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo ${bar baz}\n",
        &[
            text(b"foo"),
            var(b"bar baz"),
            sep(b'\n'),
        ],
    );

    // Imbalanced braces/brackets
    check_tokens(b"foo ]\n", &[text(b"foo"), Token::Error]);
    check_tokens(b"foo }\n", &[text(b"foo"), Token::Error]);
    check_tokens(b"foo ]", &[text(b"foo"), Token::Error]);
    check_tokens(b"foo }", &[text(b"foo"), Token::Error]);

    // Grouping
    check_tokens(
        b"foo {bar baz}\n",
        &[
            text(b"foo"),
            text(b"bar baz"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo {bar {baz} {q u x}}\n",
        &[
            text(b"foo"),
            text(b"bar {baz} {q u x}"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo {bar {baz} [q u x]}\n",
        &[
            text(b"foo"),
            text(b"bar {baz} [q u x]"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo {bar $baz [q u x]}\n",
        &[
            text(b"foo"),
            text(b"bar $baz [q u x]"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo {bar \" baz}\n",
        &[
            text(b"foo"),
            Token::WordPart(b"bar \" baz", PartRole::Text, true),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo {\n\tbar\n}\n",
        &[
            text(b"foo"),
            text(b"\n\tbar\n"),
            sep(b'\n'),
        ],
    );
    // Substitution
    check_tokens(
        b"foo [bar baz]\n",
        &[
            text(b"foo"),
            script(b"bar baz"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo [bar {baz}]\n",
        &[
            text(b"foo"),
            script(b"bar {baz}"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo $bar $baz\n",
        &[
            text(b"foo"),
            var(b"bar"),
            var(b"baz"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo $bar$baz\n",
        &[
            text(b"foo"),
            var_incomplete(b"bar"),
            var(b"baz"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo ${bar baz}\n",
        &[
            text(b"foo"),
            var(b"bar baz"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts hello[\n]world\n",
        &[
            text(b"puts"),
            text_incomplete(b"hello"),
            script_incomplete(b"\n"),
            text(b"world"),
            sep(b'\n'),
        ],
    );
    /* Quotes */
    check_tokens(
        b"\"\"",
        &[text_incomplete(b""), text(b"")],
    );
    check_tokens(
        b"\"\"\n",
        &[text_incomplete(b""), text(b""), sep(b'\n')],
    );
    check_tokens(
        b"\"",
        &[text_incomplete(b""), Token::Error],
    );
    check_tokens(
        b"\"\"b",
        &[text_incomplete(b""), Token::Error],
    );
    check_tokens(
        b"foo \"bar baz\"\n",
        &[
            text(b"foo"),
            text_incomplete(b""),
            text_incomplete(b"bar baz"),
            text(b""),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo \"bar $b[a z]\" qux\n",
        &[
            text(b"foo"),
            text_incomplete(b""),
            text_incomplete(b"bar "),
            var_incomplete(b"b"),
            script_incomplete(b"a z"),
            text(b""),
            text(b"qux"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"foo \"bar baz\" \"qux quz\"\n",
        &[
            text(b"foo"),
            text_incomplete(b""),
            text_incomplete(b"bar baz"),
            text(b""),
            text_incomplete(b""),
            text_incomplete(b"qux quz"),
            text(b""),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"\"{\" \"$a$b\"\n",
        &[
            text_incomplete(b""),
            text_incomplete(b"{"),
            text(b""),
            text_incomplete(b""),
            var_incomplete(b"a"),
            var_incomplete(b"b"),
            text(b""),
            sep(b'\n'),
        ],
    );

    check_tokens(
        b"\"{\" \"$a\"$b\n",
        &[
            text_incomplete(b""),
            text_incomplete(b"{"),
            text(b""),
            text_incomplete(b""),
            var_incomplete(b"a"),
            Token::Error,
        ],
    );
    check_tokens(
        b"\"$a + $a = ?\"\n",
        &[
            text_incomplete(b""),
            var_incomplete(b"a"),
            text_incomplete(b" + "),
            var_incomplete(b"a"),
            text_incomplete(b" = ?"),
            text(b""),
            sep(b'\n'),
        ],
    );

    /* Variables */
    check_tokens(
        b"puts $ a\n",
        &[
            text(b"puts"),
            text(b"$"),
            text(b"a"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts $\"a b\"\n",
        &[
            text(b"puts"),
            text_incomplete(b"$"),
            text_incomplete(b""),
            text_incomplete(b"a b"),
            text(b""),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts $$foo\n",
        &[
            text(b"puts"),
            text_incomplete(b"$"),
            var(b"foo"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts ${a b}\n",
        &[
            text(b"puts"),
            var(b"a b"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts $[a b]\n",
        &[
            text(b"puts"),
            text_incomplete(b"$"),
            script(b"a b"),
            sep(b'\n'),
        ],
    );
    check_tokens(b"puts { \n", &[text(b"puts"), Token::Error]);
    check_tokens(
        b"set a {\n\n",
        &[
            text(b"set"),
            text(b"a"),
            Token::Error,
        ],
    );
    check_tokens(
        b"puts {[}\n",
        &[
            text(b"puts"),
            text(b"["),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts [{]\n",
        &[
            text(b"puts"),
            script(b"{"),
            sep(b'\n'),
        ],
    );
    check_tokens(
        b"puts {[}{]} \n",
        &[
            text(b"puts"),
            text_incomplete(b"["),
            text(b"]"),
            sep(b'\n'),
        ],
    );
}

#[track_caller]
fn check_eval(tcl: Option<&mut Env>, s: &[u8], expected: &[u8]) {
    // Ensure termination
    let mut s = s.to_vec();
    s.push(b'\n');
    let s = &s[..];

    let mut local = None;
    let tcl = if let Some(outer) = tcl {
        outer
    } else {
        local.insert(Env::default())
    };

    match tcl.eval(s) {
        Err(FlowChange::Error) => {
            panic!("{:?}: got error, expected: {}",
                String::from_utf8_lossy(s),
                String::from_utf8_lossy(expected));
        }
        Ok(value) => {
            assert_eq!(
                &*value,
                expected,
                "expected result {:?} but got {:?}",
                String::from_utf8_lossy(expected),
                String::from_utf8_lossy(&value)
            );
        }
        Err(other) => {
            panic!("eval returned unexpected result: {other:?}");
        }
    }

    println!(
        "OK: {:?} -> {:?}",
        String::from_utf8_lossy(s),
        String::from_utf8_lossy(expected)
    );
}

#[track_caller]
fn check_eval_new(s: &[u8], expected: &[u8]) {
    check_eval(None, s, expected)
}

#[track_caller]
fn check_eval_err(tcl: Option<&mut Env>, s: &[u8], expected: FlowChange) {
    // Ensure termination
    let mut s = s.to_vec();
    s.push(b'\n');
    let s = &s[..];

    let mut local = None;
    let tcl = if let Some(outer) = tcl {
        outer
    } else {
        local.insert(Env::default())
    };

    assert_eq!(tcl.eval(s), Err(expected.clone()));

    println!("OK: {:?} -> !{expected:?}", String::from_utf8_lossy(s));
}

#[test]
#[should_panic]
fn test_1_subst() {
    // N.B. for these commands, the test framework will append the
    // terminating character to make the damn lexer happy.

    // subst typo:
    check_eval_err(None, b"sust hello", FlowChange::Error);

    check_eval(None, b"subst hello", b"hello");
    check_eval(None, b"subst {hello}", b"hello");
    check_eval(None, b"subst {hello world}", b"hello world");
    check_eval(None, b"subst {hello {world}}", b"hello {world}");

    // DEVIATION: partcl creates undefined variables on references and stores
    // the empty string in them. This is bad and I'm not replicating it.
    check_eval_err(None, b"subst $foo", FlowChange::Error);
    check_eval(None, b"set foo {}; subst $foo", b"");

    {
        let mut tcl = Env::default();
        tcl.set_or_create_var((*b"foo").into(), (*b"bar").into());
        tcl.set_or_create_var((*b"bar").into(), (*b"baz").into());
        tcl.set_or_create_var((*b"baz").into(), (*b"Hello").into());
        check_eval(Some(&mut tcl), b"set foo", b"bar");
        check_eval(Some(&mut tcl), b"set $foo", b"baz");
        check_eval(Some(&mut tcl), b"subst $foo", b"bar");
        check_eval(Some(&mut tcl), b"subst $foo[]$foo", b"barbar");
        check_eval(Some(&mut tcl), b"subst $$foo", b"baz");
        check_eval(Some(&mut tcl), b"subst [set $foo]", b"baz");
        check_eval(Some(&mut tcl), b"subst $[set $foo]", b"Hello");
        check_eval(Some(&mut tcl), b"subst $$$foo", b"$baz");
    }

    check_eval(None, b"subst {hello}{world}", b"helloworld");
    check_eval(None, b"subst hello[subst world]", b"helloworld");
    check_eval(None, b"subst hello[\n]world", b"helloworld");

    /* Example from Picol */
    check_eval(None, b"set a su; set b bst; $a$b Hello", b"Hello");
    /* This is an error in TCL, but works in Picol */
    check_eval(None, b"set foo {hello world}", b"hello world");
    check_eval(
        None,
        b"set foo {hello world}; set bar \"qux $foo\"; subst $foo$bar",
        b"hello worldqux hello world",
    );
    check_eval(
        None,
        b"set a f; set b {o}; set $a$b$b [subst \"hello\"]; set foo",
        b"hello",
    );
    check_eval(None, b"set {a \"b\"} hello; subst ${a \"b\"}", b"hello");
    check_eval(None, b"set \"a b\" hello; subst ${a b}", b"hello");

    check_eval(
        None,
        b"set q {\"}; set msg hello; subst $q$msg$q",
        b"\"hello\"",
    );
    check_eval(None, b"set q {\"}; subst $q[]hello[]$q", b"\"hello\"");
    check_eval(None, b"set x {\n\thello\n}", b"\n\thello\n");

    // The puts command normally write to stdout directly. Test it by overriding
    // that.
    {
        let (mut e, output) = make_env_with_output_collector();
        check_eval(Some(&mut e), b"puts {[}[]hello[]{]}", b"");
        check_eval(Some(&mut e), b"puts {{hello}}", b"");
        assert_eq!(output.borrow().as_slice(), b"[hello]\n{hello}\n");
    }
}

#[test]
fn test_2_flow() {
    {
        let (mut e, output) = make_env_with_output_collector();
        check_eval(Some(&mut e), b"if {< 1 2} {puts A} else {puts B}", b"");
        assert_eq!(output.borrow().as_slice(), b"A\n");
    }
    {
        let (mut e, output) = make_env_with_output_collector();
        check_eval(Some(&mut e), b"if {> 1 2} {puts A} else {puts B}", b"");
        assert_eq!(output.borrow().as_slice(), b"B\n");
    }
    // DEVIATION: partcl returns 0 if no branch passes, standard says empty
    // string -- I choose empty string.
    check_eval(None, b"if {> 1 2} {puts A}", b"");

    check_eval(
        None,
        b"set x 0; \
            if {== $x 0} {set _ A} elseif {== $x 1} {set _ B} else {set _ C}",
        b"A",
    );
    check_eval(
        None,
        b"set x 1; \
            if {== $x 0} {set _ A} elseif {== $x 1} {set _ B} else {set _ C}",
        b"B",
    );
    check_eval(
        None,
        b"set x 2; \
            if {== $x 0} {set _ A} elseif {== $x 1} {set _ B} else {set _ C}",
        b"C",
    );

    // DEVIATION: partcl returns 0 from while loops, standard says empty string;
    // I choose empty string.
    // DEVIATION: partcl creates unknown variables when they are first used, and
    // initializes them to empty string, which it treats as zero; this hides
    // errors and I choose to treat it as an error like standard Tcl. So, we
    // must set x first here.
    check_eval(None, b"set x 0; while {< $x 5} {set x [+ $x 1]}", b"");
    // DEVIATION: partcl break returns the string "break". It does this due
    // to an almost accidental leaving-around of state. I have fixed this; a
    // loop exited with "break" now returns the empty string like in normal
    // Tcl.
    // DEVIATION: again with the undefined variables
    check_eval(
        None,
        b"set x 0; while {== 1 1} {set x [+ $x 1]; if {== $x 5} {break}}",
        b"",
    );
    // DEVIATION: partcl is able to ignore the fact that this ends in RETURN
    // because of the lack of type safety on return values; I need to handle it
    // explicitly here, which I think is a better test anyway.
    // DEVIATION: again with the undefined variables
    check_eval_err(
        None,
        b"set x 0; \
            while {== 1 1} {set x [+ $x 1]; \
            if {!= $x 5} {continue} ; \
            return foo}",
        FlowChange::Return((*b"foo").into()),
    );
    check_eval(None, b"proc foo {} { return hello }; foo", b"hello");
    check_eval(None, b"proc five {} { + 2 3}; five", b"5");
    check_eval(None, b"proc foo {a} { return $a }; foo hello", b"hello");
    check_eval(
        None,
        b"proc foo {} { return A; return B;}; foo",
        b"A",
    );
    check_eval(
        None,
        b"set x 1; proc two {} { set x 2;}; two; set x",
        b"1",
    );
    /* Example from Picol */
    check_eval(
        None,
        b"proc fib {x} { if {<= $x 1} {return 1} \
               else { return [+ [fib [- $x 1]] [fib [- $x 2]]]}}; fib 20",
        b"10946",
    );

    let mut tcl = Env::default();
    check_eval(
        Some(&mut tcl),
        b"proc square {x} { * $x $x }; square 7",
        b"49",
    );
    check_eval(Some(&mut tcl), b"set a 4", b"4");
    check_eval(Some(&mut tcl), b"square $a", b"16");
    check_eval(Some(&mut tcl), b"set _ \"$a[]*$a ?\"", b"4*4 ?");
    check_eval(
        Some(&mut tcl),
        b"set _ \"I can compute that $a[]x$a = [square $a]\"",
        b"I can compute that 4x4 = 16",
    );
    check_eval(Some(&mut tcl), b"set a 1", b"1");
    // DEVIATION: partcl's version of this test relied on either while or if's
    // tendency to return "0" (not clear which tbh).
    check_eval(
        Some(&mut tcl),
        b"while {<= $a 10} { puts \"$a [== $a 5]\";\
               if {== $a 5} { puts {Missing five!}; set a [+ $a 1]; \
               continue;}; puts \"I can compute that $a[]x$a = [square \
               $a]\" ; set a [+ $a 1]}",
        b"",
    );
    drop(tcl);

    // Weirdly, the partcl tests don't have any tests for procs with >2
    // arguments. Let's fix that.
    check_eval(
        None,
        b"proc sum_of_squares {x y} { + [* $x $x] [* $y $y] }; \
            sum_of_squares 9 10",
        b"181",
    );
}

#[test]
fn test_3_math() {
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

    check_eval(None, b"set a 5;set b 7; - [* 4 [+ $a $b]] 6", b"42");

    // New operations not available in partcl:
    check_eval_new(b"incr x", b"1");

    check_eval_new(
        b"incr x
          incr x",
        b"2",
    );
}

fn make_env_with_output_collector() -> (Env, Rc<RefCell<Vec<u8>>>) {
    let mut e = Env::default();
    let output = Rc::new(RefCell::new(vec![]));
    let o = output.clone();
    e.register(b"puts", 2, move |_, args| {
        let mut v = o.borrow_mut();
        v.extend_from_slice(&args[1]);
        v.push(b'\n');
        // Like standard puts, we return empty.
        Ok(empty())
    });
    (e, output)
}
