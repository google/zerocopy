use super::Error;
use crate::{per_test_config::TestConfig, Errored};
use spanned::Spanned;
use std::process::ExitStatus;

impl TestConfig {
    #[allow(clippy::result_large_err)]
    pub(crate) fn ok(&self, status: ExitStatus) -> Result<Option<Error>, Errored> {
        let Some(expected) = self.exit_status()? else {
            return Ok(None);
        };
        if status.code() == Some(*expected) {
            Ok(None)
        } else {
            let span = expected.span.clone();
            let expected = expected.content;
            Ok(Some(Error::ExitStatus {
                status,
                expected,
                reason: Spanned::new(
                    match (expected, status.code()) {
                        (_, Some(101)) => "the compiler panicked",
                        (0, Some(1)) => "compilation failed, but was expected to succeed",
                        (1, Some(0)) => "compilation succeeded, but was expected to fail",
                        _ => "",
                    }
                    .into(),
                    span,
                ),
            }))
        }
    }
}
