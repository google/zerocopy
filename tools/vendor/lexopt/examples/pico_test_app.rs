#![allow(dead_code)]
//! pico-args implements this program for a number of argument parsers:
//! https://github.com/RazrFalcon/pico-args/tree/master/test-apps
//!
//! It's a nice reference point.
//!
//! I release this implementation into the public domain. Feel free to copy.

const HELP: &str = "\
USAGE: app [OPTIONS] --number NUMBER INPUT

OPTIONS:
  --number NUMBER       Set a number (required)
  --opt-number NUMBER   Set an optional number
  --width WIDTH         Set a width (non-zero, default 10)

ARGS:
  <INPUT>               Input file
";

#[derive(Debug)]
struct AppArgs {
    number: u32,
    opt_number: Option<u32>,
    width: u32,
    input: std::path::PathBuf,
}

fn parse_width(s: &str) -> Result<u32, String> {
    let w = s.parse().map_err(|_| "not a number")?;
    if w != 0 {
        Ok(w)
    } else {
        Err("width must be positive".to_string())
    }
}

fn main() {
    let args = match parse_args() {
        Ok(args) => args,
        Err(err) => {
            eprintln!("Error: {}.", err);
            std::process::exit(1);
        }
    };
    println!("{:#?}", args);
}

fn parse_args() -> Result<AppArgs, lexopt::Error> {
    use lexopt::prelude::*;

    let mut number = None;
    let mut opt_number = None;
    let mut width = 10;
    let mut input = None;

    let mut parser = lexopt::Parser::from_env();
    while let Some(arg) = parser.next()? {
        match arg {
            Short('h') | Long("help") => {
                print!("{}", HELP);
                std::process::exit(0);
            }
            Long("number") => number = Some(parser.value()?.parse()?),
            Long("opt-number") => opt_number = Some(parser.value()?.parse()?),
            Long("width") => width = parser.value()?.parse_with(parse_width)?,
            Value(path) if input.is_none() => input = Some(path.into()),
            _ => return Err(arg.unexpected()),
        }
    }
    Ok(AppArgs {
        number: number.ok_or("missing required option --number")?,
        opt_number,
        width,
        input: input.ok_or("missing required argument INPUT")?,
    })
}
