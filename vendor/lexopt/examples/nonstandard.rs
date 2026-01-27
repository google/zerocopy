//! Some programs accept options with an unusual syntax. For example, tail
//! accepts `-13` as an alias for `-n 13`.
//!
//! This program shows how to use `Parser::try_raw_args()` to handle them
//! manually.
//!
//! (Note: actual tail implementations handle it slightly differently! This
//! is just an example.)

use std::path::PathBuf;

fn parse_dashnum(parser: &mut lexopt::Parser) -> Option<u64> {
    let mut raw = parser.try_raw_args()?;
    let arg = raw.peek()?.to_str()?;
    let num = arg.strip_prefix('-')?.parse::<u64>().ok()?;
    raw.next(); // Consume the argument we just parsed
    Some(num)
}

fn main() -> Result<(), lexopt::Error> {
    use lexopt::prelude::*;

    let mut parser = lexopt::Parser::from_env();
    loop {
        if let Some(num) = parse_dashnum(&mut parser) {
            println!("Got number {}", num);
        } else if let Some(arg) = parser.next()? {
            match arg {
                Short('f') | Long("follow") => {
                    println!("Got --follow");
                }
                Short('n') | Long("number") => {
                    let num: u64 = parser.value()?.parse()?;
                    println!("Got number {}", num);
                }
                Value(path) => {
                    let path = PathBuf::from(path);
                    println!("Got file {}", path.display());
                }
                _ => return Err(arg.unexpected()),
            }
        } else {
            break;
        }
    }

    Ok(())
}
