use clap::{Command, Arg, ArgAction};
use deltae::DEMethod;
use std::str::FromStr;

pub fn command() -> Command {
    Command::new("deltae")
        .version(env!("CARGO_PKG_VERSION"))
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .arg(Arg::new("METHOD")
            .help("Set DeltaE method")
            .long("method")
            .short('m')
            .value_parser(DEMethod::from_str)
            .ignore_case(true)
            .default_value("2000")
            .action(ArgAction::Set))
        .arg(Arg::new("REFERENCE")
            .help("Reference color values")
            .required(true))
        .arg(Arg::new("SAMPLE")
            .help("Sample color values")
            .required(true))
        .arg(Arg::new("COLORTYPE")
            .help("Set color type")
            .short('c')
            .long("color-type")
            .aliases(["color", "type"])
            .default_value("lab")
            .value_names(["lab", "lch", "xyz"])
            .ignore_case(true)
            .action(ArgAction::Set))
}
