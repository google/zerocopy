//! Define custom test flags not natively supported by ui_test

use crate::{
    build_manager::BuildManager, parser::Comments, per_test_config::TestConfig, Config, Errored,
};
use std::{
    panic::{RefUnwindSafe, UnwindSafe},
    process::{Command, Output},
};

#[cfg(feature = "rustc")]
pub mod edition;
#[cfg(feature = "rustc")]
pub mod revision_args;
#[cfg(feature = "rustc")]
pub mod run;
pub mod rustfix;

/// Tester-specific flag that gets parsed from `//@` comments.
pub trait Flag: Send + Sync + UnwindSafe + RefUnwindSafe + std::fmt::Debug {
    /// Clone the boxed value and create a new box.
    fn clone_inner(&self) -> Box<dyn Flag>;

    /// Modify a command to what the flag specifies
    fn apply(
        &self,
        _cmd: &mut Command,
        _config: &TestConfig,
        _build_manager: &BuildManager,
    ) -> Result<(), Errored> {
        Ok(())
    }

    /// Whether this flag causes a test to be filtered out
    fn test_condition(&self, _config: &Config, _comments: &Comments, _revision: &str) -> bool {
        false
    }

    /// Run an action after a test is finished.
    /// Returns an empty [`Vec`] if no action was taken.
    fn post_test_action(
        &self,
        _config: &TestConfig,
        _output: &Output,
        _build_manager: &BuildManager,
    ) -> Result<(), Errored> {
        Ok(())
    }

    /// Whether the flag gets overridden by the same flag in revisions.
    fn must_be_unique(&self) -> bool;
}

/// Use the unit type for when you don't need any behaviour and just need to know if the flag was set or not.
impl Flag for () {
    fn clone_inner(&self) -> Box<dyn Flag> {
        Box::new(())
    }
    fn must_be_unique(&self) -> bool {
        true
    }
}

impl Clone for Box<dyn Flag> {
    fn clone(&self) -> Self {
        self.clone_inner()
    }
}
