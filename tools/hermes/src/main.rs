mod errors;
mod parse;
mod resolve;
mod transform;
mod ui_test_shim;

use std::{env, process::exit};

use clap::Parser;

/// Hermes: A Literate Verification Toolchain
#[derive(Parser, Debug)]
#[command(name = "hermes", version, about, long_about = None)]
struct Cli {
    #[command(flatten)]
    resolve: resolve::Args,
}

fn main() {
    if env::var("HERMES_UI_TEST_MODE").is_ok() {
        ui_test_shim::run();
        return;
    }

    let args = Cli::parse();

    // TODO: Better error handling than `.unwrap()`.
    let roots = resolve::resolve_roots(&args.resolve).unwrap();

    // TODO: From each root, parse and walk referenced modules.
    let mut has_errors = false;
    for (package, kind, path) in roots {
        let mut edits = Vec::new();
        let res = parse::read_file_and_visit_hermes_items(path.as_std_path(), |_src, res| {
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
}
