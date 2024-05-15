use std::{error::Error, io::{ErrorKind, Read}};

use wartcl::*;

fn main() -> Result<(), Box<dyn Error>> {
    let mut tcl = Tcl::init();

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
                let r = tcl.eval(&buf);
                if let Err(e) = r {
                    print!("{e:?}");
                }
                println!("> {}", String::from_utf8_lossy(&tcl.result));
                buf.clear();
                break;
            }
        }
    }

    Ok(())
}
