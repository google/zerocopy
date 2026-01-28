use std::io::Read;
use std::path::Path;

mod extract;
mod process;
mod template;

use crate::config;

/// Generates readme data from `source` file
///
/// Optionally, a template can be used to render the output
pub fn generate_readme<T: Read>(
    project_root: &Path,
    source: &mut T,
    template: Option<&mut T>,
    add_title: bool,
    add_badges: bool,
    add_license: bool,
    indent_headings: bool,
) -> Result<String, String> {
    let lines = extract::extract_docs(source).map_err(|e| format!("{}", e))?;

    let readme = process::process_docs(lines, indent_headings).join("\n");

    // get template from file
    let template = if let Some(template) = template {
        Some(get_template_string(template)?)
    } else {
        None
    };

    // get manifest from Cargo.toml
    let cargo = config::get_manifest(project_root)?;

    template::render(template, readme, &cargo, add_title, add_badges, add_license)
}

/// Load a template String from a file
fn get_template_string<T: Read>(template: &mut T) -> Result<String, String> {
    let mut template_string = String::new();
    match template.read_to_string(&mut template_string) {
        Err(e) => return Err(format!("Error: {}", e)),
        _ => {}
    }

    Ok(template_string)
}
