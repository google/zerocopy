use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
#[non_exhaustive]
pub enum JobError {
    #[error("Failed to create job")]
    CreateFailed(io::Error),
    #[error("Failed to assign job")]
    AssignFailed(io::Error),
    #[error("Failed to set info for job")]
    SetInfoFailed(io::Error),
    #[error("Failed to get info for job")]
    GetInfoFailed(io::Error),
}

impl From<JobError> for io::Error {
    fn from(value: JobError) -> Self {
        match value {
            JobError::CreateFailed(error)
            | JobError::AssignFailed(error)
            | JobError::SetInfoFailed(error)
            | JobError::GetInfoFailed(error) => error,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn job_error_into_io_error() {
        fn example() -> Result<(), JobError> {
            Err(JobError::AssignFailed(io::Error::from_raw_os_error(1)))
        }

        fn test_example() -> Result<(), io::Error> {
            let _ = example()?;

            Ok(())
        }

        let e = test_example().unwrap_err();

        assert_eq!(e.raw_os_error(), Some(1));
    }
}
