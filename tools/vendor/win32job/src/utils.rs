use std::{io, mem};

use windows::Win32::{
    Foundation::HANDLE,
    System::{
        ProcessStatus::{GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS_EX},
        Threading::{GetCurrentProcess, GetProcessAffinityMask},
    },
};

/// Return a pseudo handle to the current process.
/// See also [Microsoft Docs](https://docs.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-getcurrentprocess) for this function.
pub fn get_current_process() -> isize {
    unsafe { GetCurrentProcess() }.0 as _
}

#[derive(Debug, Clone)]
pub struct ProcessMemoryCounters {
    pub page_fault_count: u32,
    pub peak_working_set_size: usize,
    pub working_set_size: usize,
    pub quota_peak_paged_pool_usage: usize,
    pub quota_paged_pool_usage: usize,
    pub quota_peak_non_paged_pool_usage: usize,
    pub quota_non_paged_pool_usage: usize,
    pub pagefile_usage: usize,
    pub peak_pagefile_usage: usize,
    pub private_usage: usize,
}

/// Retrieves information about the memory usage of the specified process.
/// See also [Microsoft Docs](https://docs.microsoft.com/en-us/windows/win32/api/psapi/nf-psapi-getprocessmemoryinfo) for this function.
pub fn get_process_memory_info(process_handle: isize) -> Result<ProcessMemoryCounters, io::Error> {
    let mut counters = PROCESS_MEMORY_COUNTERS_EX::default();
    unsafe {
        GetProcessMemoryInfo(
            HANDLE(process_handle as _),
            &mut counters as *mut _ as *mut _,
            mem::size_of_val(&counters) as u32,
        )
    }?;

    Ok(ProcessMemoryCounters {
        page_fault_count: counters.PageFaultCount,
        peak_working_set_size: counters.PeakWorkingSetSize,
        working_set_size: counters.WorkingSetSize,
        quota_peak_paged_pool_usage: counters.QuotaPeakPagedPoolUsage,
        quota_paged_pool_usage: counters.QuotaPagedPoolUsage,
        quota_peak_non_paged_pool_usage: counters.QuotaPeakNonPagedPoolUsage,
        quota_non_paged_pool_usage: counters.QuotaNonPagedPoolUsage,
        pagefile_usage: counters.PagefileUsage,
        peak_pagefile_usage: counters.PeakPagefileUsage,
        private_usage: counters.PrivateUsage,
    })
}

/// Retrieves the process affinity mask for the specified process and the system affinity mask for the system.
/// See also [Microsoft Docs](https://docs.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-getprocessaffinitymask) for this function.
pub fn get_process_affinity_mask(process_handle: isize) -> Result<(usize, usize), io::Error> {
    let mut process_affinity_mask = 0usize;
    let mut system_affinity_mask = 0usize;

    unsafe {
        GetProcessAffinityMask(
            HANDLE(process_handle as _),
            &mut process_affinity_mask as *mut _,
            &mut system_affinity_mask as *mut _,
        )
    }
    .map_err(|e| e.into())
    .map(|_| (process_affinity_mask, system_affinity_mask))
}
