# win32job

[![docs.rs](https://docs.rs/win32job/badge.svg)](https://docs.rs/crate/win32job)
[![crates.io](https://img.shields.io/crates/v/win32job.svg)](https://crates.io/crates/win32job)

[Documentation](https://docs.rs/crate/win32job)

A safe API for Windows' [job objects](https://docs.microsoft.com/en-us/windows/win32/api/jobapi2/nf-jobapi2-createjobobjectw), 
which can be used to set various limits to processes associated with them. 

```toml
[dependencies]
win32job = "2"
```


## Examples

Limit the amount of memory that will be available for this process (allocating more memory is still possible, but it will be paged):

```rust
use win32job::{Job, ExtendedLimitInfo};

fn main() -> Result<(), Box<dyn std::error::Error>>  {
    let mut info = ExtendedLimitInfo::new();

    info.limit_working_memory(1 * 1024 * 1024, 4 * 1024 * 1024);

    let job = Job::create_with_limit_info(&mut info)?;

    job.assign_current_process()?;
    
    Ok(())
}
```

Force any created sub processes to exit when the main process exits: 

```rust
use win32job::Job;
use std::process::Command;

fn main() -> Result<(), Box<dyn std::error::Error>>  {
    let job = Job::create()?;
    
    let mut info = job.query_extended_limit_info()?;

    info.limit_kill_on_job_close();

    job.set_extended_limit_info(&mut info)?;
    
    job.assign_current_process()?;

    Command::new("cmd.exe")
            .arg("/C")
            .arg("ping -n 9999 127.0.0.1")
            .spawn()?;

    // The cmd will be killed once we exit, or `job` is dropped.
    
    Ok(())
}
```

## License
 
The `win32job` crate is licensed under either of

```text
Apache License, Version 2.0, (LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0)
MIT license (LICENSE-MIT or http://opensource.org/licenses/MIT)
```

at your option.
