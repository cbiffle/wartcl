//! A very basic REPL (read/eval/print loop) for wartcl.
//!
//! wartcl isn't necessarily designed to be an amazing interactive development
//! environment -- in particular, it reports errors in less detail than real
//! Tcl. However, it can work.

use std::error::Error;

use rustyline::DefaultEditor;
use wartcl::{empty, Env, FlowChange, Token, Tokenizer, Val};

fn main() -> Result<(), Box<dyn Error>> {
    // Create a halfway-decent command line editor experience using rustyline.
    let mut editor = DefaultEditor::new()?;

    // Create our wartcl system state.
    let mut tcl = Env::default();

    // This is where you would register custom commands or set variables before
    // starting the REPL. Here is an example: this command prints a short
    // message and then asks the REPL to exit.
    tcl.register(Val::from_static(b"exit"), 0, |_, _| {
        println!("so long!");
        Err(FlowChange::Return(empty()))
    });

    'outerloop:
    loop {
        // Prompt displayed to the user -- we'll change this if we detect that
        // an expression is being continued across lines.
        let mut prompt = "> ";
        // String containing the code we're reading.
        let mut read = String::new();

        // Read lines until we get a full thought.
        'readloop:
        loop {
            let line = editor.readline(prompt)?;

            read.push_str(&line);
            // rustyline removes the trailing newline; add it back.
            read.push('\n');

            editor.add_history_entry(line)?;

            // Each time we get a line of input, we attempt to tokenize the
            // entire `read` buffer, to see if there's a full command yet.
            let mut t = Tokenizer::new(read.as_bytes());
            while let Some(tok) = t.next() {
                if tok == Token::Error && !t.at_end() {
                    // We've found something that makes no sense, like a closing
                    // curly brace without a corresponding opening brace.
                    println!("ERROR");
                    continue 'outerloop;
                }
                if matches!(tok, Token::CmdSep(b'\r' | b'\n')) {
                    // The tokenizer only emits CmdSep when it hits a newline at
                    // top level, which means we've just collected a full
                    // command!
                    break 'readloop;
                }
            }
            // If we get here, tokenization did not find a CmdSep. This means
            // the expression is continuing across lines. Update the prompt to
            // indicate that:
            prompt = "… ";
        }

        // We have collected an entire statement. Run it!
        match tcl.eval(Val::from(read.clone().into_bytes())) {
            Err(FlowChange::Error) => println!("ERROR"),
            Err(FlowChange::Return(_)) => {
                // We'll let the user exit the REPL by typing return, sure, why
                // not.
                break;
            }
            Err(fc) => {
                // This handles cases where the user typed something like
                // `break` at the top level.
                println!("Unexpected flow change outside loop: {fc:?}");
            }
            Ok(result) => {
                if !result.is_empty() {
                    println!("{}", String::from_utf8_lossy(&result));
                }
            }
        }
    }

    Ok(())
}
