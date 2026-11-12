// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Fine-grained wall-clock, rusage (`wait4`/`getrusage`), file I/O, and SHA-256
//! profiler for Track 1 reference research.

use serde::Serialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::io::{self, Read};
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug, Serialize)]
pub struct Timeval {
    pub tv_sec: i64,
    pub tv_usec: i64,
}

impl Timeval {
    pub fn as_ms(self) -> f64 {
        (self.tv_sec as f64) * 1000.0 + (self.tv_usec as f64) / 1000.0
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug, Serialize)]
pub struct RUsage {
    pub ru_utime: Timeval,
    pub ru_stime: Timeval,
    pub ru_maxrss: i64,
    pub ru_ixrss: i64,
    pub ru_idrss: i64,
    pub ru_isrss: i64,
    pub ru_minflt: i64,
    pub ru_majflt: i64,
    pub ru_nswap: i64,
    pub ru_inblock: i64,
    pub ru_oublock: i64,
    pub ru_msgsnd: i64,
    pub ru_msgrcv: i64,
    pub ru_nsignals: i64,
    pub ru_nvcsw: i64,
    pub ru_nivcsw: i64,
}

const RUSAGE_SELF: i32 = 0;
const RUSAGE_CHILDREN: i32 = -1;

unsafe extern "C" {
    fn wait4(pid: i32, status: *mut i32, options: i32, rusage: *mut RUsage) -> i32;
    fn getrusage(who: i32, usage: *mut RUsage) -> i32;
}

pub fn get_rusage_self() -> RUsage {
    let mut usage = RUsage::default();
    unsafe {
        getrusage(RUSAGE_SELF, &mut usage);
    }
    usage
}

pub fn get_rusage_children() -> RUsage {
    let mut usage = RUsage::default();
    unsafe {
        getrusage(RUSAGE_CHILDREN, &mut usage);
    }
    usage
}

#[derive(Clone, Default, Debug, Serialize)]
pub struct PhaseIoStats {
    pub files_read: usize,
    pub bytes_read: u64,
    pub read_wall_ms: f64,
    pub files_written: usize,
    pub bytes_written: u64,
    pub write_wall_ms: f64,
    pub sha256_calls: usize,
    pub bytes_hashed: u64,
    pub sha256_wall_ms: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SubprocessRecord {
    pub index: usize,
    pub stage: String,
    pub label: String,
    pub program: String,
    pub args: Vec<String>,
    pub wall_ms: f64,
    pub utime_ms: f64,
    pub stime_ms: f64,
    pub cpu_total_ms: f64,
    pub maxrss_kib: i64,
    pub minflt: i64,
    pub majflt: i64,
    pub inblock: i64,
    pub oublock: i64,
    pub nvcsw: i64,
    pub nivcsw: i64,
    pub extra: Value,
}

#[derive(Clone, Debug, Serialize)]
pub struct SubstageRecord {
    pub stage: String,
    pub substage: String,
    pub wall_ms: f64,
    pub self_utime_ms: f64,
    pub self_stime_ms: f64,
    pub self_minflt: i64,
    pub self_majflt: i64,
    pub children_utime_ms: f64,
    pub children_stime_ms: f64,
    pub children_minflt: i64,
    pub children_majflt: i64,
    pub extra: Value,
}

#[derive(Default, Debug, Serialize)]
pub struct ProfileData {
    pub io_by_phase: BTreeMap<String, PhaseIoStats>,
    pub subprocesses: Vec<SubprocessRecord>,
    pub substages: Vec<SubstageRecord>,
}

static PROFILER: OnceLock<Mutex<ProfileData>> = OnceLock::new();

fn lock_prof() -> std::sync::MutexGuard<'static, ProfileData> {
    PROFILER
        .get_or_init(|| Mutex::new(ProfileData::default()))
        .lock()
        .unwrap()
}

pub fn reset() {
    let mut g = lock_prof();
    *g = ProfileData::default();
}

pub fn snapshot_json(total_wall_ms: f64) -> Value {
    let g = lock_prof();
    let self_ru = get_rusage_self();
    let child_ru = get_rusage_children();

    let mut total_io = PhaseIoStats::default();
    for stats in g.io_by_phase.values() {
        total_io.files_read += stats.files_read;
        total_io.bytes_read += stats.bytes_read;
        total_io.read_wall_ms += stats.read_wall_ms;
        total_io.files_written += stats.files_written;
        total_io.bytes_written += stats.bytes_written;
        total_io.write_wall_ms += stats.write_wall_ms;
        total_io.sha256_calls += stats.sha256_calls;
        total_io.bytes_hashed += stats.bytes_hashed;
        total_io.sha256_wall_ms += stats.sha256_wall_ms;
    }

    json!({
        "total_wall_ms": total_wall_ms,
        "parent_rusage": {
            "utime_ms": self_ru.ru_utime.as_ms(),
            "stime_ms": self_ru.ru_stime.as_ms(),
            "maxrss_kib": self_ru.ru_maxrss,
            "minflt": self_ru.ru_minflt,
            "majflt": self_ru.ru_majflt,
            "inblock": self_ru.ru_inblock,
            "oublock": self_ru.ru_oublock,
            "nvcsw": self_ru.ru_nvcsw,
            "nivcsw": self_ru.ru_nivcsw,
        },
        "children_cumulative_rusage": {
            "utime_ms": child_ru.ru_utime.as_ms(),
            "stime_ms": child_ru.ru_stime.as_ms(),
            "maxrss_kib": child_ru.ru_maxrss,
            "minflt": child_ru.ru_minflt,
            "majflt": child_ru.ru_majflt,
            "inblock": child_ru.ru_inblock,
            "oublock": child_ru.ru_oublock,
            "nvcsw": child_ru.ru_nvcsw,
            "nivcsw": child_ru.ru_nivcsw,
        },
        "io_totals": total_io,
        "io_by_phase": g.io_by_phase,
        "substages": g.substages,
        "subprocesses": g.subprocesses,
    })
}

pub struct SubstageSpan {
    stage: String,
    substage: String,
    start: Instant,
    self_before: RUsage,
    child_before: RUsage,
}

impl SubstageSpan {
    pub fn enter(stage: &str, substage: &str) -> Self {
        Self {
            stage: stage.to_owned(),
            substage: substage.to_owned(),
            start: Instant::now(),
            self_before: get_rusage_self(),
            child_before: get_rusage_children(),
        }
    }

    pub fn finish(self) -> f64 {
        self.finish_with_extra(Value::Null)
    }

    pub fn finish_with_extra(self, extra: Value) -> f64 {
        let wall_ms = self.start.elapsed().as_secs_f64() * 1000.0;
        let self_after = get_rusage_self();
        let child_after = get_rusage_children();
        let mut g = lock_prof();
        g.substages.push(SubstageRecord {
            stage: self.stage,
            substage: self.substage,
            wall_ms,
            self_utime_ms: self_after.ru_utime.as_ms() - self.self_before.ru_utime.as_ms(),
            self_stime_ms: self_after.ru_stime.as_ms() - self.self_before.ru_stime.as_ms(),
            self_minflt: self_after.ru_minflt - self.self_before.ru_minflt,
            self_majflt: self_after.ru_majflt - self.self_before.ru_majflt,
            children_utime_ms: child_after.ru_utime.as_ms() - self.child_before.ru_utime.as_ms(),
            children_stime_ms: child_after.ru_stime.as_ms() - self.child_before.ru_stime.as_ms(),
            children_minflt: child_after.ru_minflt - self.child_before.ru_minflt,
            children_majflt: child_after.ru_majflt - self.child_before.ru_majflt,
            extra,
        });
        wall_ms
    }
}

pub fn record_read(phase: &str, bytes: u64, wall_ms: f64) {
    let mut g = lock_prof();
    let entry = g.io_by_phase.entry(phase.to_owned()).or_default();
    entry.files_read += 1;
    entry.bytes_read += bytes;
    entry.read_wall_ms += wall_ms;
}

pub fn record_write(phase: &str, bytes: u64, wall_ms: f64) {
    let mut g = lock_prof();
    let entry = g.io_by_phase.entry(phase.to_owned()).or_default();
    entry.files_written += 1;
    entry.bytes_written += bytes;
    entry.write_wall_ms += wall_ms;
}

pub fn record_sha256(phase: &str, bytes: u64, wall_ms: f64) {
    let mut g = lock_prof();
    let entry = g.io_by_phase.entry(phase.to_owned()).or_default();
    entry.sha256_calls += 1;
    entry.bytes_hashed += bytes;
    entry.sha256_wall_ms += wall_ms;
}

pub fn read_file(phase: &str, path: &Path) -> io::Result<Vec<u8>> {
    let t0 = Instant::now();
    let res = fs::read(path);
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    if let Ok(ref bytes) = res {
        record_read(phase, bytes.len() as u64, ms);
    }
    res
}

pub fn read_to_string(phase: &str, path: &Path) -> io::Result<String> {
    let t0 = Instant::now();
    let res = fs::read_to_string(path);
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    if let Ok(ref s) = res {
        record_read(phase, s.len() as u64, ms);
    }
    res
}

pub fn write_file(phase: &str, path: &Path, bytes: &[u8]) -> io::Result<()> {
    let t0 = Instant::now();
    let res = fs::write(path, bytes);
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    if res.is_ok() {
        record_write(phase, bytes.len() as u64, ms);
    }
    res
}

pub fn sha256_bytes_tagged(phase: &str, data: &[u8]) -> String {
    let t0 = Instant::now();
    let hex = format!("{:x}", Sha256::digest(data));
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    record_sha256(phase, data.len() as u64, ms);
    hex
}

pub fn spawn_and_wait4(
    cmd: &mut Command,
    stage: &str,
    label: &str,
    program: &str,
    args: &[String],
    extra: Value,
) -> io::Result<(Output, SubprocessRecord)> {
    let start = Instant::now();
    let mut child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let pid = child.id() as i32;
    let mut stdout_pipe = child.stdout.take().unwrap();
    let mut stderr_pipe = child.stderr.take().unwrap();

    let out_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout_pipe.read_to_end(&mut buf);
        buf
    });
    let err_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr_pipe.read_to_end(&mut buf);
        buf
    });

    let mut status: i32 = 0;
    let mut usage = RUsage::default();
    loop {
        let ret = unsafe { wait4(pid, &mut status, 0, &mut usage) };
        if ret < 0 {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(err);
        }
        break;
    }
    let wall_ms = start.elapsed().as_secs_f64() * 1000.0;
    let stdout = out_thread.join().unwrap_or_default();
    let stderr = err_thread.join().unwrap_or_default();
    let exit_status = ExitStatus::from_raw(status);

    let utime_ms = usage.ru_utime.as_ms();
    let stime_ms = usage.ru_stime.as_ms();
    let mut g = lock_prof();
    let index = g.subprocesses.len();
    let rec = SubprocessRecord {
        index,
        stage: stage.to_owned(),
        label: label.to_owned(),
        program: program.to_owned(),
        args: args.to_vec(),
        wall_ms,
        utime_ms,
        stime_ms,
        cpu_total_ms: utime_ms + stime_ms,
        maxrss_kib: usage.ru_maxrss,
        minflt: usage.ru_minflt,
        majflt: usage.ru_majflt,
        inblock: usage.ru_inblock,
        oublock: usage.ru_oublock,
        nvcsw: usage.ru_nvcsw,
        nivcsw: usage.ru_nivcsw,
        extra,
    };
    g.subprocesses.push(rec.clone());

    Ok((
        Output {
            status: exit_status,
            stdout,
            stderr,
        },
        rec,
    ))
}

pub fn update_last_subprocess_extra(label: &str, extra: Value) {
    let mut g = lock_prof();
    if let Some(last) = g.subprocesses.iter_mut().rev().find(|r| r.label == label) {
        last.extra = extra;
    }
}
