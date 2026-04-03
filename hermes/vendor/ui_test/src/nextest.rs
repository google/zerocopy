//! Helper functions for nextest emulation.

use crate::Config;

/// Nexttest emulation: we act as if we are one single test.
/// Returns `true` if we should not run any tests.
/// Patches up the `Config`s to have appropriate filters.
pub fn emulate(configs: &mut Vec<Config>) -> bool {
    if configs.iter().any(|c| c.list) {
        if configs.iter().any(|c| !c.run_only_ignored) {
            println!("ui_test: test");
        }
        return true;
    }
    for config in configs {
        if config.filter_exact
            && config.filter_files.len() == 1
            && config.filter_files[0] == "ui_test"
        {
            config.filter_exact = false;
            config.filter_files.clear();
        }
    }
    false
}
