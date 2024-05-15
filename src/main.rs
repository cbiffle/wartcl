use std::{error::Error, io::{ErrorKind, Read}};

use wartcl::*;

fn main() -> Result<(), Box<dyn Error>> {
    let mut tcl = init();

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

        let mut p = Tokenizer::new(&buf);

        while let Some((tok, from)) = p.next(true) {
            if tok == Token::Error && !p.at_end() {
                buf.clear();
                break;
            }

            if tok == Token::Cmd && !from.is_empty() {
                let r = eval(&mut tcl, &buf);
                if r != Flow::Error {
                    println!("{r:?}> {}", String::from_utf8_lossy(&tcl.result));
                } else {
                    println!("?!");
                }
                buf.clear();
                break;
            }
        }
    }

    Ok(())
}
