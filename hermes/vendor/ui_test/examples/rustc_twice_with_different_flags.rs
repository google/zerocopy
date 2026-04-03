#[cfg(feature = "rustc")]
use ui_test::{
    default_file_filter, default_per_file_config, run_tests_generic, status_emitter, Config,
};

#[cfg(feature = "rustc")]
#[cfg_attr(test, test)]
fn main() -> ui_test::color_eyre::Result<()> {
    let config = Config::rustc("examples_tests/rustc_basic");
    let abort_check = config.abort_check.clone();
    ctrlc::set_handler(move || abort_check.abort())?;

    // Compile all `.rs` files in the given directory (relative to your
    // Cargo.toml) and compare their output against the corresponding
    // `.stderr` files.
    run_tests_generic(
        vec![config.clone(), config],
        default_file_filter,
        default_per_file_config,
        status_emitter::Text::verbose(),
    )
}

#[cfg(not(feature = "rustc"))]
fn main() -> ui_test::color_eyre::Result<()> {
    Ok(())
}
