use windows::{
    core::PCWSTR,
    Win32::{
        Foundation::{CloseHandle, HANDLE},
        System::JobObjects::{
            AssignProcessToJobObject, CreateJobObjectW, JobObjectExtendedLimitInformation,
            QueryInformationJobObject, SetInformationJobObject,
        },
    },
};

use crate::error::JobError;
use crate::limits::ExtendedLimitInfo;
use std::{ffi::c_void, mem};

pub use crate::utils::get_current_process;

#[derive(Debug)]
pub struct Job {
    pub(crate) handle: HANDLE,
}

unsafe impl Send for Job {}
unsafe impl Sync for Job {}

impl Job {
    /// Create an anonymous job object.
    pub fn create() -> Result<Self, JobError> {
        unsafe { CreateJobObjectW(None, PCWSTR::null()) }
            .map_err(|e| JobError::CreateFailed(e.into()))
            .map(|handle| Self { handle })
    }

    /// Create an anonymous job object and sets it's limit according to `info`.
    pub fn create_with_limit_info(info: &ExtendedLimitInfo) -> Result<Self, JobError> {
        let job = Self::create()?;
        job.set_extended_limit_info(info)?;

        Ok(job)
    }

    /// Return the underlying handle to the job.
    /// Note that this handle will be closed once the `Job` object is dropped.
    pub fn handle(&self) -> isize {
        self.handle.0 as _
    }

    /// Return the underlying handle to the job, consuming the job.
    /// Note that the handle will NOT be closed, so it is the caller's responsibly to close it.
    pub fn into_handle(self) -> isize {
        let job = mem::ManuallyDrop::new(self);

        job.handle.0 as _
    }

    /// Return basic and extended limit information for a job object.
    /// See also [Microsoft Docs](https://docs.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_extended_limit_information).
    pub fn query_extended_limit_info(&self) -> Result<ExtendedLimitInfo, JobError> {
        let mut info = ExtendedLimitInfo::default();

        unsafe {
            QueryInformationJobObject(
                Some(self.handle),
                JobObjectExtendedLimitInformation,
                &mut info.0 as *mut _ as *mut c_void,
                mem::size_of_val(&info.0) as u32,
                None,
            )
        }
        .map_err(|e| JobError::GetInfoFailed(e.into()))?;
        Ok(info)
    }

    /// Set the basic and extended limit information for a job object.
    pub fn set_extended_limit_info(&self, info: &ExtendedLimitInfo) -> Result<(), JobError> {
        unsafe {
            SetInformationJobObject(
                self.handle,
                JobObjectExtendedLimitInformation,
                &info.0 as *const _ as *const c_void,
                mem::size_of_val(&info.0) as u32,
            )
            .map_err(|e| JobError::SetInfoFailed(e.into()))
        }
    }

    /// Assigns a process to the job object.
    /// See also [Microsoft Docs](https://docs.microsoft.com/en-us/windows/win32/api/jobapi2/nf-jobapi2-assignprocesstojobobject).
    pub fn assign_process(&self, proc_handle: isize) -> Result<(), JobError> {
        unsafe { AssignProcessToJobObject(self.handle, HANDLE(proc_handle as _)) }
            .map_err(|e| JobError::AssignFailed(e.into()))
    }

    /// Assigns the current process to the job object.
    pub fn assign_current_process(&self) -> Result<(), JobError> {
        let current_proc_handle = get_current_process();

        self.assign_process(current_proc_handle)
    }
}

impl Drop for Job {
    fn drop(&mut self) {
        unsafe {
            let _ = CloseHandle(self.handle);
        }
    }
}

#[cfg(test)]
mod tests {
    use windows::Win32::System::JobObjects::JOB_OBJECT_LIMIT_WORKINGSET;

    use crate::Job;

    #[test]
    fn it_works() {
        let job = Job::create().unwrap();

        let mut info = job.query_extended_limit_info().unwrap();

        assert_eq!(info.0.BasicLimitInformation.LimitFlags.0, 0);

        // This is the default.
        assert_eq!(info.0.BasicLimitInformation.SchedulingClass, 5);

        info.0.BasicLimitInformation.MinimumWorkingSetSize = 1 * 1024 * 1024;
        info.0.BasicLimitInformation.MaximumWorkingSetSize = 4 * 1024 * 1024;

        info.0.BasicLimitInformation.LimitFlags |= JOB_OBJECT_LIMIT_WORKINGSET;

        job.set_extended_limit_info(&mut info).unwrap();

        // Clear limits.
        info.0.BasicLimitInformation.LimitFlags.0 = 0;
        job.set_extended_limit_info(&mut info).unwrap();
    }
}
