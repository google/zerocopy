use deltae::*;
use std::error::Error;

mod cli;

fn main() -> Result<(), Box<dyn Error>> {
    //Parse command line arguments with clap
    let matches = cli::command().get_matches();

    let method = matches.get_one::<DEMethod>("METHOD").unwrap().to_owned();
    let color_type = matches.get_one::<String>("COLORTYPE").unwrap();
    let color0 = matches.get_one::<String>("REFERENCE").unwrap();
    let color1 = matches.get_one::<String>("SAMPLE").unwrap();

    let delta = match color_type.as_str() {
        "lab" => color0.parse::<LabValue>()?.delta(color1.parse::<LabValue>()?, method),
        "lch" => color0.parse::<LchValue>()?.delta(color1.parse::<LchValue>()?, method),
        "xyz" => color0.parse::<XyzValue>()?.delta(color1.parse::<XyzValue>()?, method),
        _ => unreachable!("COLORTYPE"),
    };

    println!("{}: {}", delta.method(), delta.value());

    Ok(())
}
