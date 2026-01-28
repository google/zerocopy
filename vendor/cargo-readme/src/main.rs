//! Generate README.md from doc comments.

use clap::Parser;
use std::io;
use std::io::Write;

mod helper;

fn main() {
    let args = Args::parse();
    let result = match &args.command {
        Command::Readme(readme_args) => execute(readme_args),
    };
    match result {
        Err(e) => {
            io::stderr()
                .write_fmt(format_args!("Error: {}\n", e))
                .expect("An error occurred while trying to show an error message");
            std::process::exit(1);
        }
        _ => {}
    }
}
/// The command line interface for setting up a Bottlerocket TestSys cluster and running tests.
#[derive(Debug, Parser)]
#[clap(author, version, about)]
struct Args {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Debug, Parser)]
enum Command {
    /// Generate README.md from doc comments
    Readme(ReadmeArgs),
}

/// Generate README.md from doc comments
#[derive(Debug, Parser)]
#[clap(author, version, about)]
struct ReadmeArgs {
    /// Do not prepend badges line.
    /// By default, badges defined in Cargo.toml are prepended to the output.
    /// Ignored when using a template.
    #[clap(long)]
    no_badges: bool,

    /// Do not add an extra level to headings.
    /// By default, '#' headings become '##', so the first '#' can be the crate name. Use this
    /// option to prevent this behavior.
    #[clap(long)]
    no_indent_headings: bool,

    /// Do not append license line.
    /// By default, the license defined in `Cargo.toml` will be prepended to the output.
    /// Ignored when using a template.
    #[clap(long)]
    no_license: bool,

    /// Ignore template file when generating README.
    /// Only useful to ignore default template `README.tpl`.
    #[clap(long)]
    no_template: bool,

    /// Do not prepend title line.
    /// By default, the title ('# crate-name') is prepended to the output.
    #[clap(long)]
    no_title: bool,

    /// File to read from.
    /// If not provided, will try to use `src/lib.rs`, then `src/main.rs`. If neither file
    /// could be found, will look into `Cargo.toml` for a `[lib]`, then for a single `[[bin]]`.
    /// If multiple binaries are found, an error will be returned.
    #[clap(long, short = 'i')]
    input: Option<String>,

    /// File to write to. If not provided, will output to stdout.
    #[clap(long, short = 'o')]
    output: Option<String>,

    /// Directory to be set as project root (where `Cargo.toml` is)
    /// Defaults to the current directory.
    #[clap(long = "project-root", short = 'r')]
    root: Option<String>,

    /// Template used to render the output.
    /// Default behavior is to use `README.tpl` if it exists.
    #[clap(long, short = 't')]
    template: Option<String>,
}

// Takes the arguments matches from clap and outputs the result, either to stdout of a file
fn execute(args: &ReadmeArgs) -> Result<(), String> {
    // get project root
    let project_root = helper::get_project_root(args.root.as_deref())?;

    // get source file
    let mut source = helper::get_source(&project_root, args.input.as_deref())?;

    // get destination file
    let mut dest = helper::get_dest(&project_root, args.output.as_deref())?;

    // get template file
    let mut template_file = if args.no_template {
        None
    } else {
        helper::get_template_file(&project_root, args.template.as_deref())?
    };

    let add_title = !args.no_title;
    let add_badges = !args.no_badges;
    let add_license = !args.no_license;
    let indent_headings = !args.no_indent_headings;

    // generate output
    let readme = cargo_readme::generate_readme(
        &project_root,
        &mut source,
        template_file.as_mut(),
        add_title,
        add_badges,
        add_license,
        indent_headings,
    )?;

    helper::write_output(&mut dest, readme)
}
