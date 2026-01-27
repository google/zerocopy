//! POSIX [recommends](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap12.html#tag_12_02)
//! that no more options are parsed after the first positional argument.
//! The other arguments are then all treated as positional arguments.
//!
//! lexopt can be used like this. After seeing the first positional argument
//! (`Arg::Value`), call `Parser::raw_args`.
//!
//! The most logical thing to then do is often to collect the values
//! into a `Vec`. This is shown below.
//!
//! Note that most modern software doesn't follow POSIX's rule and allows
//! options anywhere (as long as they come before "--").

fn main() -> Result<(), lexopt::Error> {
    use lexopt::prelude::*;

    let mut parser = lexopt::Parser::from_env();
    let mut free = Vec::new();
    while let Some(arg) = parser.next()? {
        match arg {
            Short('n') | Long("number") => {
                let num: u16 = parser.value()?.parse()?;
                println!("Got number {}", num);
            }
            Long("shout") => {
                println!("Got --shout");
            }
            Value(val) => {
                free.push(val);
                free.extend(parser.raw_args()?);
            }
            _ => return Err(arg.unexpected()),
        }
    }
    println!("Got free args {:?}", free);
    Ok(())
}
