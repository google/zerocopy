use std::fs::File;
use std::io::{ErrorKind, Write};
use std::path::{Path, PathBuf};

use cargo_readme::get_manifest;
use cargo_readme::project;

const DEFAULT_TEMPLATE: &'static str = "README.tpl";

/// Get the project root from given path or defaults to current directory
///
/// The given path is appended to the current directory if is a relative path, otherwise it is used
/// as is. If no path is given, the current directory is used.
/// A `Cargo.toml` file must be present is the root directory.
pub fn get_project_root(given_root: Option<&str>) -> Result<PathBuf, String> {
    project::get_root(given_root)
}

/// Get the source file from which the doc comments will be extracted
pub fn get_source(project_root: &Path, input: Option<&str>) -> Result<File, String> {
    match input {
        Some(input) => {
            let input = project_root.join(input);
            File::open(&input)
                .map_err(|e| format!("Could not open file '{}': {}", input.to_string_lossy(), e))
        }
        None => find_entrypoint(&project_root),
    }
}

/// Get the destination file where the result will be output to
pub fn get_dest(project_root: &Path, output: Option<&str>) -> Result<Option<File>, String> {
    match output {
        Some(filename) => {
            let output = project_root.join(filename);
            File::create(&output).map(|f| Some(f)).map_err(|e| {
                format!(
                    "Could not create output file '{}': {}",
                    output.to_string_lossy(),
                    e
                )
            })
        }
        None => Ok(None),
    }
}

/// Get the template file that will be used to render the output
pub fn get_template_file(
    project_root: &Path,
    template: Option<&str>,
) -> Result<Option<File>, String> {
    match template {
        // template path was given, try to read it
        Some(template) => {
            let template = project_root.join(template);
            File::open(&template).map(|f| Some(f)).map_err(|e| {
                format!(
                    "Could not open template file '{}': {}",
                    template.to_string_lossy(),
                    e
                )
            })
        }
        // try to read the defautl template file
        None => {
            let template = project_root.join(DEFAULT_TEMPLATE);
            match File::open(&template) {
                Ok(file) => Ok(Some(file)),
                // do not generate an error on file not found
                Err(ref e) if e.kind() != ErrorKind::NotFound => {
                    return Err(format!(
                        "Could not open template file '{}': {}",
                        DEFAULT_TEMPLATE, e
                    ))
                }
                // default template not found, return `None`
                _ => Ok(None),
            }
        }
    }
}

/// Write result to output, either stdout or destination file
pub fn write_output(dest: &mut Option<File>, readme: String) -> Result<(), String> {
    match dest.as_mut() {
        Some(dest) => {
            let mut bytes = readme.into_bytes();
            // Append new line at end of file to match behavior of `cargo readme > README.md`
            bytes.push(b'\n');

            dest.write_all(&mut bytes)
                .map(|_| ())
                .map_err(|e| format!("Could not write to output file: {}", e))?;
        }
        None => println!("{}", readme),
    }

    Ok(())
}

/// Find the default entrypoiny to read the doc comments from
///
/// Try to read entrypoint in the following order:
/// - src/lib.rs
/// - src/main.rs
/// - file defined in the `[lib]` section of Cargo.toml
/// - file defined in the `[[bin]]` section of Cargo.toml, if there is only one
///   - if there is more than one `[[bin]]`, an error is returned
pub fn find_entrypoint(current_dir: &Path) -> Result<File, String> {
    let manifest = get_manifest(current_dir)?;
    let entrypoint = project::find_entrypoint(current_dir, &manifest)?;

    File::open(current_dir.join(entrypoint)).map_err(|e| format!("{}", e))
}
