//! # wun32job-rs
//!
//! A safe API for Windows' job objects, which can be used to set various limits to
//! processes associated with them.
//! See also [Microsoft Docs](https://docs.microsoft.com/en-us/windows/win32/api/jobapi2/nf-jobapi2-createjobobjectw).
//!
//! # Using the higher level API
//!
//! After getting an `ExtendedLimitInfo` object, either by querying the info of a job
//! or by creating an empty one using `new()`, use helper methods to configure
//! the required limits, and finally set the info to the job.
//!
//! ```edition2021
//! use win32job::*;
//! # fn main() -> Result<(), JobError> {
//!
//! let mut info = ExtendedLimitInfo::new();
//!
//! info.limit_working_memory(1 * 1024 * 1024,  4 * 1024 * 1024)
//!     .limit_priority_class(PriorityClass::BelowNormal);
//!
//! let job = Job::create_with_limit_info(&mut info)?;
//! job.assign_current_process()?;
//! #   info.clear_limits();
//! #   job.set_extended_limit_info(&mut info)?;
//! #   Ok(())
//! # }
//! ```
//!
//! Which is equivalnent to:
//! ```edition2021
//! use win32job::*;
//! # fn main() -> Result<(), JobError> {
//!
//! let job = Job::create()?;
//! let mut info = job.query_extended_limit_info()?;
//!
//! info.limit_working_memory(1 * 1024 * 1024,  4 * 1024 * 1024)
//!     .limit_priority_class(PriorityClass::BelowNormal);
//!
//! job.set_extended_limit_info(&mut info)?;
//! job.assign_current_process()?;
//! #   info.clear_limits();
//! #   job.set_extended_limit_info(&mut info)?;
//! #   Ok(())
//! # }
//! ```
mod error;
mod job;
mod limits;
mod query;
pub mod utils;

pub use crate::error::JobError;
pub use crate::job::Job;
pub use crate::limits::{ExtendedLimitInfo, PriorityClass};

// Cannot use `cfg(test)` here since `rustdoc` won't look at it.
#[cfg(debug_assertions)]
mod test_readme {
    #[doc = include_str!("../README.md")]
    enum _DoctestReadme {}
}
