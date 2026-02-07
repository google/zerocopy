mod errors;
mod parse;
mod transform;
mod ui_test_shim;

use std::{env, path::PathBuf, process::exit};

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

    let mut has_errors = false;
    let mut edits = Vec::new();
    let res = parse::read_file_and_visit_hermes_items(&file_path, |_src, res| {
        if let Err(e) = res {
            has_errors = true;
            eprint!("{:?}", miette::Report::new(e));
        } else if let Ok(item) = res {
            transform::append_edits(&item, &mut edits);
        }
    });

    let source = res.unwrap_or_else(|e| {
        eprintln!("Error parsing file: {}", e);
        exit(1);
    });

    if has_errors {
        exit(1);
    }

    let mut source = source.into_bytes();
    transform::apply_edits(&mut source, &edits);
}
