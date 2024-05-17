use std::{error::Error, io::{ErrorKind, Read}};

use wartcl::*;

fn main() -> Result<(), Box<dyn Error>> {
    let mut tcl = Env::init();

    let mut stdin = std::io::stdin();
    let mut buf = vec![];

    loop {
        let mut inp = 0u8;
        match stdin.read_exact(std::slice::from_mut(&mut inp)) {
            Ok(()) => (),
            Err(e) if e.kind() == ErrorKind::UnexpectedEof => {
                println!("eof");
                break;
            }
            Err(e) => return Err(e.into()),
        }

        buf.push(inp);

        if inp != b'\r' && inp != b'\n' {
            continue;
        }

        let mut p = Tokenizer::new(&buf);

        while let Some(tok) = p.next() {
            if tok == Token::Error && !p.at_end() {
                buf.clear();
                break;
            }

            if matches!(tok, Token::CmdSep(b'\r' | b'\n')) {
                let r = tcl.eval(&buf);
                match r {
                    Err(e) => {
                        println!("{e:?}");
                    }
                    Ok(result) => {
                        println!("{}", String::from_utf8_lossy(&result));
                    }
                }
                buf.clear();
                break;
            }
        }
    }

    Ok(())
}
