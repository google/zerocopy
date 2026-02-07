extern crate libtest_mimic;

use libtest_mimic::{Arguments, Trial, Failed};

use std::{
    env,
    error::Error,
    ffi::OsStr,
    fs,
    path::Path, process::ExitCode,
};


fn main() -> Result<ExitCode, Box<dyn Error>> {
    let args = Arguments::from_args();
    let tests = collect_tests()?;
    Ok(libtest_mimic::run(&args, tests).exit_code())
}

/// Creates one test for each `.rs` file in the current directory or
/// sub-directories of the current directory.
fn collect_tests() -> Result<Vec<Trial>, Box<dyn Error>> {
    fn visit_dir(path: &Path, tests: &mut Vec<Trial>) -> Result<(), Box<dyn Error>> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let file_type = entry.file_type()?;

            // Handle files
            let path = entry.path();
            if file_type.is_file() {
                if path.extension() == Some(OsStr::new("rs")) {
                    let name = path
                        .strip_prefix(env::current_dir()?)?
                        .display()
                        .to_string();

                    let test = Trial::test(name, move || check_file(&path))
                        .with_kind("tidy");
                    tests.push(test);
                }
            } else if file_type.is_dir() {
                // Handle directories
                visit_dir(&path, tests)?;
            }
        }

        Ok(())
    }

    // We recursively look for `.rs` files, starting from the current
    // directory.
    let mut tests = Vec::new();
    let current_dir = env::current_dir()?;
    visit_dir(&current_dir, &mut tests)?;

    Ok(tests)
}

/// Performs a couple of tidy tests.
fn check_file(path: &Path) -> Result<(), Failed> {
    let content = fs::read(path).map_err(|e| format!("Cannot read file: {e}"))?;

    // Check that the file is valid UTF-8
    let content = String::from_utf8(content)
        .map_err(|_| "The file's contents are not a valid UTF-8 string!")?;

    // Check for `\r`: we only want `\n` line breaks!
    if content.contains('\r') {
        return Err("Contains '\\r' chars. Please use ' \\n' line breaks only!".into());
    }

    // Check for tab characters `\t`
    if content.contains('\t') {
        return Err("Contains tab characters ('\\t'). Indent with four spaces!".into());
    }

    // Check for too long lines
    if content.lines().any(|line| line.chars().count() > 100) {
        return Err("Contains lines longer than 100 codepoints!".into());
    }

    Ok(())
}
