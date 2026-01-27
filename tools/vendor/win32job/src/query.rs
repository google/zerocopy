use std::{ffi::c_void, mem};
use windows::Win32::System::JobObjects::{
    JobObjectBasicProcessIdList, QueryInformationJobObject, JOBOBJECT_BASIC_PROCESS_ID_LIST,
};

use crate::{Job, JobError};

#[repr(C)]
#[derive(Debug)]
struct ProcessIdList {
    header: JOBOBJECT_BASIC_PROCESS_ID_LIST,
    list: [usize; 1024],
}

impl Job {
    /// Return all the process identifiers for a job object.
    /// If the job is nested, the process identifier list consists of all processes
    /// associated with the job and its child jobs.
    pub fn query_process_id_list(&self) -> Result<Vec<usize>, JobError> {
        // TODO: We will get an error if there are more than 1024 processes in the job.
        // This can be fixed by calling `QueryInformationJobObject` a second time,
        // with a bigger list with the correct size (as returned from the first call).
        let mut proc_id_list = ProcessIdList {
            header: Default::default(),
            list: [0usize; 1024],
        };

        unsafe {
            QueryInformationJobObject(
                Some(self.handle),
                JobObjectBasicProcessIdList,
                &mut proc_id_list as *mut _ as *mut c_void,
                mem::size_of_val(&proc_id_list) as u32,
                None,
            )
        }
        .map_err(|e| JobError::GetInfoFailed(e.into()))?;

        let list = proc_id_list
            .header
            .ProcessIdList
            .into_iter()
            .chain(proc_id_list.list)
            .take(proc_id_list.header.NumberOfProcessIdsInList as usize)
            .collect();

        Ok(list)
    }
}

#[cfg(test)]
mod tests {
    use crate::Job;

    #[test]
    fn query_proc_id() {
        let job = Job::create().unwrap();

        let pids = job.query_process_id_list().unwrap();
        assert_eq!(pids, []);

        job.assign_current_process().unwrap();

        let pids = job.query_process_id_list().unwrap();

        let current_process_id = std::process::id() as usize;

        // It's not equal to 1 because sometime we "catch" `rusty_fork_test` sub procs.
        assert!(pids.len() >= 1);

        assert!(pids.contains(&current_process_id));
    }
}
