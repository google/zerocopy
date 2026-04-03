//! Custom flag for setting rustc revision-specific args.

use super::Flag;
use crate::{build_manager::BuildManager, per_test_config::TestConfig, Errored};

/// Set rustc revision-specific args.
#[derive(Clone, Debug)]
pub struct RustcRevisionArgs;

impl Flag for RustcRevisionArgs {
    fn clone_inner(&self) -> Box<dyn Flag> {
        Box::new(self.clone())
    }

    fn must_be_unique(&self) -> bool {
        true
    }

    fn apply(
        &self,
        cmd: &mut std::process::Command,
        config: &TestConfig,
        _build_manager: &BuildManager,
    ) -> Result<(), Errored> {
        let revision = config.status.revision();
        if !revision.is_empty() {
            cmd.arg(format!("--cfg={revision}"));
            cmd.arg(format!("-Cextra-filename={revision}"));
        }
        Ok(())
    }
}
