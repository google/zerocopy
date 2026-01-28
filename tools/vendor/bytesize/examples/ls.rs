//! Emulates running `ls -la` in the terminal, showing human-readable file sizes and file names.

use std::{fs, io};

fn main() -> io::Result<()> {
    let dir = fs::read_dir(".")?;

    for entry in dir {
        let entry = entry?;

        let md = entry.metadata()?;

        let file_name = entry.file_name();
        let file_name = file_name.to_string_lossy();

        if md.is_file() {
            let file_size = md.len();
            let file_size = bytesize::ByteSize::b(file_size).display().iec_short();

            println!("{file_size}\t{file_name}");
        } else {
            println!("-\t{file_name}");
        }
    }

    Ok(())
}
