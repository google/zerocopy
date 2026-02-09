extern crate strip_ansi_escapes;

use std::io;
use strip_ansi_escapes::Writer;

pub fn work() -> io::Result<()> {
    let stdin = io::stdin();
    let mut in_lock = stdin.lock();
    let stdout = io::stdout();
    let out_lock = stdout.lock();
    let mut writer = Writer::new(out_lock);
    io::copy(&mut in_lock, &mut writer)?;
    Ok(())
}

pub fn main() {
    work().unwrap();
}
