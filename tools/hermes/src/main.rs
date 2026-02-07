mod errors;
mod parse;
mod ui_test_shim;

use std::{env, fs, path::PathBuf, process::exit};

fn main() {
    if env::var("HERMES_UI_TEST_MODE").is_ok() {
        ui_test_shim::run();
        return;
    }

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: hermes <file.rs>");
        exit(1);
    }

    let file_path = PathBuf::from(&args[1]);
    let source = match fs::read_to_string(&file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            exit(1);
        }
    };

    let mut has_errors = false;
    parse::visit_hermes_items_in_file(&file_path, &source, |res| {
        if let Err(e) = res {
            has_errors = true;
            eprint!("{:?}", miette::Report::new(e));
        }
    });

    if has_errors {
        exit(1);
    }
}
