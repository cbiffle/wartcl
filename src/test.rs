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

use super::*;

#[track_caller]
fn check_tokens(input: &[u8], expect: &[(Token, &[u8])]) {
    let mut p = Tokenizer::new(input);
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
fn test_0_lexer() {
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
        local.insert(Tcl::init())
    };

    match tcl.eval(s) {
        Err(FlowChange::Error) => {
            panic!("eval returned error: {:?}",
                   String::from_utf8_lossy(s));
        }
        Ok(value) => {
            assert_eq!(&*value, expected,
                       "expected result {:?} but got {:?}",
                       String::from_utf8_lossy(expected),
                       String::from_utf8_lossy(&value));
        }
        Err(other) => {
            panic!("eval returned unexpected result: {other:?}");
        }
    }

    println!("OK: {:?} -> {:?}",
             String::from_utf8_lossy(s),
             String::from_utf8_lossy(expected));
}

#[track_caller]
fn check_eval_err(tcl: Option<&mut Tcl>, s: &[u8], expected: FlowChange) {
    // Ensure termination
    let mut s = s.to_vec();
    s.push(b'\n');
    let s = &s[..];

    let mut local = None;
    let tcl = if let Some(outer) = tcl {
        outer
    } else {
        local.insert(Tcl::init())
    };

    assert_eq!(tcl.eval(s), Err(expected.clone()));

    println!("OK: {:?} -> !{expected:?}",
             String::from_utf8_lossy(s));
}

#[test]
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

    if false { // TODO
        let mut tcl = Tcl::init();
        tcl.set_or_create_var((*b"foo").into(), (*b"bar").into());
        tcl.set_or_create_var((*b"bar").into(), (*b"baz").into());
        tcl.set_or_create_var((*b"baz").into(), (*b"Hello").into());
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
fn test_2_flow() {
    check_eval(None, b"if {< 1 2} {puts A} else {puts B}", b"A");
    check_eval(None, b"if {> 1 2} {puts A} else {puts B}", b"B");
    // DEVIATION: partcl returns 0 if no branch passes, standard says empty
    // string -- I choose empty string.
    check_eval(None, b"if {> 1 2} {puts A}", b"");

    check_eval(None,
               b"set x 0; if {== $x 0} {subst A} elseif {== $x 1} {subst B} else {subst C}",
               b"A");
    check_eval(None,
               b"set x 1; if {== $x 0} {subst A} elseif {== $x 1} {subst B} else {subst C}",
               b"B");
    check_eval(None,
               b"set x 2; if {== $x 0} {subst A} elseif {== $x 1} {subst B} else {subst C}",
               b"C");

    // DEVIATION: partcl returns 0 from while loops, standard says empty string;
    // I choose empty string.
    // DEVIATION: partcl creates variables on reference to contain empty string,
    // which it treats as zero; this hides errors and I choose to treat it as an
    // error like standard Tcl. So, we must set x first here.
    check_eval(None, b"set x 0; while {< $x 5} {set x [+ $x 1]}", b"");
    // DEVIATION: partcl break returns the string "break". It does this due
    // to an almost accidental leaving-around of state. I have fixed this; a
    // loop exited with "break" now returns the empty string like in normal
    // Tcl.
    // DEVIATION: again with the undefined variables
    check_eval(None, b"set x 0; while {== 1 1} {set x [+ $x 1]; if {== $x 5} {break}}",
               b"");
    // DEVIATION: partcl is able to ignore the fact that this ends in RETURN
    // because of the lack of type safety on return values; I need to handle it
    // explicitly here, which I think is a better test anyway.
    // DEVIATION: again with the undefined variables
    check_eval_err(
        None,
        b"set x 0; while {== 1 1} {set x [+ $x 1]; if {!= $x 5} {continue} ; return foo}",
        FlowChange::Return((*b"foo").into()));
    check_eval(None, b"proc foo {} { subst hello }; foo", b"hello");
    check_eval(None, b"proc five {} { + 2 3}; five", b"5");
    check_eval(None, b"proc foo {a} { subst $a }; foo hello", b"hello");
    check_eval(None, b"proc foo {} { subst hello; return A; return B;}; foo", b"A");
    check_eval(None, b"set x 1; proc two {} { set x 2;}; two; subst $x", b"1");
    /* Example from Picol */
    check_eval(None, b"proc fib {x} { if {<= $x 1} {return 1} \
               else { return [+ [fib [- $x 1]] [fib [- $x 2]]]}}; fib 20",
               b"10946");

    let mut tcl = Tcl::init();
    check_eval(Some(&mut tcl), b"proc square {x} { * $x $x }; square 7", b"49");
    check_eval(Some(&mut tcl), b"set a 4", b"4");
    check_eval(Some(&mut tcl), b"square $a", b"16");
    check_eval(Some(&mut tcl), b"subst \"$a[]*$a ?\"", b"4*4 ?");
    check_eval(Some(&mut tcl), b"subst \"I can compute that $a[]x$a = [square $a]\"",
               b"I can compute that 4x4 = 16");
    check_eval(Some(&mut tcl), b"set a 1", b"1");
    // DEVIATION: partcl's version of this test relied on either while or if's
    // tendency to return "0" (not clear which tbh).
    check_eval(Some(&mut tcl), b"while {<= $a 10} { puts \"$a [== $a 5]\";\
               if {== $a 5} { puts {Missing five!}; set a [+ $a 1]; \
               continue;}; puts \"I can compute that $a[]x$a = [square \
               $a]\" ; set a [+ $a 1]}",
               b"");
    drop(tcl);

    // Weirdly, the partcl tests don't have any tests for procs with >2
    // arguments. Let's fix that.
    check_eval(None, b"proc sum_of_squares {x y} { + [* $x $x] [* $y $y] }; sum_of_squares 9 10",
               b"181");
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

    check_eval(None, b"set a 5;set b 7; subst [- [* 4 [+ $a $b]] 6]", b"42");
}
