#![deny(warnings)]

extern crate duct;

use std::env::{args, current_dir, set_current_dir};
use std::io;
use std::path::Path;
use std::process::exit;

#[cfg(unix)]
fn check_executable(path: &Path) {
    use std::os::unix::fs::MetadataExt;
    const EXECUTABLE_BIT: u32 = 0o100;
    let metadata = path.metadata().unwrap();
    let mode = metadata.mode();
    if mode & EXECUTABLE_BIT == 0 {
        println!(
            "Expected {:?} to be publicly executable, but found mode {:o}.",
            path, mode
        );
        exit(1);
    }
}

#[cfg(windows)]
fn check_executable(_: &Path) {
    // no-op
}

fn main() {
    // The first command line arg is a path to an executable, and the rest are
    // its arguments. Chdir to the parent dir, and then try to execute the
    // program as a single-component Path (*not* a string). Duct should
    // automatically add the leading ./ for us so that it works on Unix. (And if
    // the executable doesn't actually exist, duct should prevent it from
    // matching some other command in the PATH, on either Unix or Windows.)

    let args_vec: Vec<_> = args().collect();
    if args_vec.len() < 2 {
        println!("must have at least 1 exe arg");
        exit(1);
    }

    // Parse out the exe name and the dir it's in.
    let exe_full_path = Path::new(&args_vec[1]);
    let exe_parent = exe_full_path.parent().unwrap();
    let exe_name: &Path = exe_full_path.file_name().unwrap().as_ref();

    // Sanity check that exe actually exists.
    if !exe_full_path.is_file() {
        println!(r#""{}" is not a file."#, exe_full_path.display());
        exit(1);
    }

    // If we try to execute a non-executable file on Unix, we'll end up with a
    // "file not found" error. We really don't want to confuse those with the
    // errors we get from bad Path handling. Explicitly check for that here.
    check_executable(exe_full_path);

    // Chdir to that dir.
    set_current_dir(exe_parent).unwrap();

    // Run the child!
    let res = duct::cmd(exe_name, &args_vec[2..]).run();

    // Check what the child did, and exit appropriately.
    if let Err(err) = res {
        println!(
            "error executing command {:?} in dir {:?}",
            exe_name,
            current_dir().unwrap()
        );
        if err.kind() == io::ErrorKind::NotFound {
            println!("File not found during execution! Path sanitization is TOTALLY BROKEN!");
            exit(1);
        } else {
            println!("Unexpected IO error: {:?}", err);
            exit(1);
        }
    }

    // Success!
}
