extern crate colored;

use colored::Colorize;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    Err("ERROR".red())?
}
