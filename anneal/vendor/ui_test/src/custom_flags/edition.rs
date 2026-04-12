//! Custom flag for setting the edition for all tests

use super::Flag;
use crate::{build_manager::BuildManager, per_test_config::TestConfig, Errored};

#[derive(Debug)]
/// Set the edition of the tests
pub struct Edition(pub String);

impl Flag for Edition {
    fn must_be_unique(&self) -> bool {
        true
    }
    fn clone_inner(&self) -> Box<dyn Flag> {
        Box::new(Edition(self.0.clone()))
    }

    fn apply(
        &self,
        cmd: &mut std::process::Command,
        _config: &TestConfig,
        _build_manager: &BuildManager,
    ) -> Result<(), Errored> {
        cmd.arg("--edition").arg(&self.0);
        Ok(())
    }
}
