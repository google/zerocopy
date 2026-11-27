// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI driver for the multi-leg MIR differential oracle (`run` and `fuzz`).

use std::{
    env, fs,
    io::{ErrorKind, Write as _},
    path::{Component, Path, PathBuf},
    process::ExitCode,
};

use anneal_differential_tests::{
    RunOptions, default_manifest_path,
    fuzz::{FuzzOptions, is_shrinkable_case, run_fuzz_campaign, validate_fuzz_options},
    run_differential_suite,
};

fn usage() -> &'static str {
    "Usage:
  anneal-diff run [--manifest <path>] [--capture-bin <path>]
                  [--mir-eval-bin <path>] [--cache-root <path>]
                  [--json] [--self-check-oracle]

  anneal-diff fuzz [--seed <u64>] [--cases <usize>] [--max-stmts <1..=20>]
                   [--ub-ratio <0.0..=0.85>] [--shrink | --no-shrink]
                   [--rustc | --no-rustc] [--capture-bin <path>]
                   [--mir-eval-bin <path>] [--mir-eval-manifest <path>]
                   [--cache-root <path>] [--min-admission-rate <f64>]
                   [--fuel <usize>] [--json] [--out <path>]"
}

fn next_arg(args: &[String], idx: &mut usize, flag: &str) -> Result<String, String> {
    *idx += 1;
    args.get(*idx).cloned().ok_or_else(|| format!("missing argument after {flag}"))
}

fn run_corpus_subcommand(args: &[String]) -> Result<ExitCode, String> {
    let mut manifest_path: Option<PathBuf> = None;
    let mut capture_bin: Option<PathBuf> = None;
    let mut mir_eval_bin: Option<PathBuf> = None;
    let mut cache_root: Option<PathBuf> = None;
    let mut json_out = false;
    let mut self_check_oracle = false;

    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "--manifest" => {
                manifest_path = Some(PathBuf::from(next_arg(args, &mut i, "--manifest")?));
            }
            "--capture-bin" => {
                capture_bin = Some(PathBuf::from(next_arg(args, &mut i, "--capture-bin")?));
            }
            "--mir-eval-bin" => {
                mir_eval_bin = Some(PathBuf::from(next_arg(args, &mut i, "--mir-eval-bin")?));
            }
            "--cache-root" => {
                cache_root = Some(PathBuf::from(next_arg(args, &mut i, "--cache-root")?));
            }
            "--json" => json_out = true,
            "--self-check-oracle" => self_check_oracle = true,
            "--help" | "-h" => {
                println!("{}", usage());
                return Ok(ExitCode::SUCCESS);
            }
            other => return Err(format!("unknown flag {other:?}\n\n{}", usage())),
        }
        i += 1;
    }

    let resolved_manifest = match manifest_path {
        Some(p) => p,
        None => default_manifest_path()?,
    };
    let opts = RunOptions {
        manifest_path: resolved_manifest,
        capture_bin,
        mir_eval_bin,
        self_check_oracle,
        cache_root,
    };

    let report = run_differential_suite(&opts)?;
    let passed = report.is_passing();

    if json_out {
        let serialized = serde_json::to_string_pretty(&report)
            .map_err(|e| format!("serialize differential report: {e}"))?;
        println!("{serialized}");
    } else {
        println!(
            "{} | dialect={} | legs={}",
            report.alpha_notice,
            report.mir_dialect,
            report.legs.join(",")
        );
        for case in &report.cases {
            println!(
                "  [{:>4}] {:<36} -> {} (kernel={})",
                if case.verdict.is_ok() { "PASS" } else { "FAIL" },
                case.id,
                case.verdict.label(),
                case.kernel_checked
            );
            if !case.verdict.is_ok() {
                println!("         detail: {:?}", case.verdict);
            }
        }
        println!(
            "Summary: compared={} pass={} ub={} conservative={} kernel_pass={} kernel_ub={} red_flags_passed={}",
            report.metrics.compared_count,
            report.metrics.pass_agreed_count,
            report.metrics.ub_agreed_count,
            report.metrics.conservative_unsupported_count,
            report.metrics.kernel_checked_pass_count,
            report.metrics.kernel_checked_ub_count,
            report.red_flags_passed
        );
        if let Some(err) = &report.red_flag_error {
            println!("RED FLAG ERROR: {err}");
        }
        if let Some(m) = &report.mutant_check {
            println!(
                "Mutant self-check: killed={}/{} ({:.1}%)",
                m.killed_mutants, m.total_mutants, m.killed_pct
            );
            for r in &m.results {
                println!(
                    "  [{:>4}] {} -> {} (expected {})",
                    if r.killed { "KILL" } else { "MISS" },
                    r.mutant_id,
                    r.actual_verdict,
                    r.expected_kill_verdict
                );
            }
            for p in &m.synthetic_lean_probes {
                println!(
                    "  [{:>4}] synthetic:{} -> {} (expected {})",
                    if p.passed { "PASS" } else { "FAIL" },
                    p.probe_id,
                    p.actual_verdict,
                    p.expected_kill_verdict
                );
            }
        }
    }

    Ok(if passed { ExitCode::SUCCESS } else { ExitCode::FAILURE })
}

fn run_fuzz_subcommand(args: &[String]) -> Result<ExitCode, String> {
    let mut opts = FuzzOptions::default();
    let mut json_out = false;
    let mut out_path: Option<PathBuf> = None;

    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "--seed" => {
                let raw = next_arg(args, &mut i, "--seed")?;
                opts.seed = raw.parse().map_err(|e| format!("invalid --seed {raw:?}: {e}"))?;
            }
            "--cases" => {
                let raw = next_arg(args, &mut i, "--cases")?;
                opts.cases = raw.parse().map_err(|e| format!("invalid --cases {raw:?}: {e}"))?;
            }
            "--max-stmts" => {
                let raw = next_arg(args, &mut i, "--max-stmts")?;
                let val: usize =
                    raw.parse().map_err(|e| format!("invalid --max-stmts {raw:?}: {e}"))?;
                if !(1..=20).contains(&val) {
                    return Err(format!("--max-stmts must be in 1..=20, got {val}"));
                }
                opts.max_stmts = val;
            }
            "--ub-ratio" => {
                let raw = next_arg(args, &mut i, "--ub-ratio")?;
                let val: f64 =
                    raw.parse().map_err(|e| format!("invalid --ub-ratio {raw:?}: {e}"))?;
                if !val.is_finite() || !(0.0..=0.85).contains(&val) {
                    return Err(format!("--ub-ratio must be in 0.0..=0.85, got {val}"));
                }
                opts.ub_ratio = val;
            }
            "--shrink" => opts.shrink = true,
            "--no-shrink" => opts.shrink = false,
            "--rustc" => opts.run_rustc = true,
            "--no-rustc" => opts.run_rustc = false,
            "--capture-bin" => {
                opts.capture_bin = Some(PathBuf::from(next_arg(args, &mut i, "--capture-bin")?));
            }
            "--mir-eval-bin" => {
                opts.mir_eval_bin = Some(PathBuf::from(next_arg(args, &mut i, "--mir-eval-bin")?));
            }
            "--mir-eval-manifest" => {
                opts.mir_eval_manifest =
                    Some(PathBuf::from(next_arg(args, &mut i, "--mir-eval-manifest")?));
            }
            "--cache-root" => {
                opts.cache_root = Some(PathBuf::from(next_arg(args, &mut i, "--cache-root")?));
            }
            "--min-admission-rate" => {
                let raw = next_arg(args, &mut i, "--min-admission-rate")?;
                opts.min_admission_rate = raw
                    .parse()
                    .map_err(|e| format!("invalid --min-admission-rate {raw:?}: {e}"))?;
            }
            "--fuel" => {
                let raw = next_arg(args, &mut i, "--fuel")?;
                opts.fuel = raw.parse().map_err(|e| format!("invalid --fuel {raw:?}: {e}"))?;
            }
            "--json" => json_out = true,
            "--out" => {
                out_path = Some(PathBuf::from(next_arg(args, &mut i, "--out")?));
            }
            "--help" | "-h" => {
                println!("{}", usage());
                return Ok(ExitCode::SUCCESS);
            }
            other => return Err(format!("unknown flag {other:?}\n\n{}", usage())),
        }
        i += 1;
    }

    let _ = validate_fuzz_options(&opts)?;

    let validated_out = out_path.as_deref().map(resolve_and_validate_out_path).transpose()?;

    let report = run_fuzz_campaign(&opts)?;
    let passed = report.is_passing();
    let serialized =
        serde_json::to_string_pretty(&report).map_err(|e| format!("serialize fuzz report: {e}"))?;

    if let Some(p) = &validated_out {
        write_out_report_no_symlinks(p, format!("{serialized}\n").as_bytes())?;
    }

    if json_out {
        println!("{serialized}");
    } else {
        let m = &report.metrics;
        println!(
            "{} | fuzz seed={} | dialect={} | legs={}",
            report.alpha_notice,
            report.seed,
            report.mir_dialect,
            report.legs.join(",")
        );
        println!(
            "Summary: total={} bi_fault_equiv={} (ub_agreed={}) conservative={} spurious_ub={} admitted_ub={} unsound={} authority_disagree={} admission={}/{} ({:.1}%) move_reinit={} rustc_ok={} rustc_ignored_ub={} elapsed={:.2}s",
            m.total_cases,
            m.bi_fault_equiv_count,
            m.ub_probes_agreed_count,
            m.conservative_over_approx_count,
            m.spurious_lean_ub_count,
            m.admitted_authority_ub_count,
            m.unsound_accept_count,
            m.authority_disagreement_count,
            m.admitted_cases,
            m.admission_eligible_cases,
            m.admission_rate * 100.0,
            m.move_reinit_exercised_count,
            m.rustc_agreed_count,
            m.rustc_ignored_ub_count,
            m.wall_clock_sec
        );
        if !m.disclosed_gaps.is_empty() {
            println!("Disclosed gaps: {:?}", m.disclosed_gaps);
        }
        for case in
            report.cases.iter().filter(|c| is_shrinkable_case(c.category, &c.miri, &c.evaluation))
        {
            println!(
                "  [FAIL] {} ({:?}) -> {}: {}",
                case.case_id,
                case.category,
                case.evaluation.agreement.as_str(),
                case.evaluation.detail
            );
            if let Some(st) = &case.shrink_trace {
                println!(
                    "         shrunk: {} -> {} nodes (1-minimal={}, evals={})",
                    st.original_nodes, st.shrunk_nodes, st.converged_1_minimal, st.steps_evaluated
                );
                println!("         minimized_args: {:?}", st.minimized_args);
            }
        }
        if let Some(err) = &report.gate_error {
            println!("GATE ERROR: {err}");
        }
    }

    Ok(if passed { ExitCode::SUCCESS } else { ExitCode::FAILURE })
}

fn resolve_and_validate_out_path(raw: &Path) -> Result<PathBuf, String> {
    resolve_and_validate_out_path_from(
        raw,
        &env::current_dir().map_err(|e| format!("resolve current directory for --out: {e}"))?,
    )
}

fn resolve_and_validate_out_path_from(raw: &Path, base_dir: &Path) -> Result<PathBuf, String> {
    if raw.as_os_str().is_empty() {
        return Err("--out path must not be empty".to_owned());
    }
    let raw_lossy = raw.to_string_lossy();
    if raw_lossy.ends_with('/') || raw_lossy.ends_with(std::path::MAIN_SEPARATOR) {
        return Err(format!("--out must name a regular file, not a directory: {}", raw.display()));
    }

    let mut clean = if raw.is_absolute() { PathBuf::new() } else { base_dir.to_path_buf() };
    let mut last_was_normal = false;
    for comp in raw.components() {
        match comp {
            Component::Prefix(p) => {
                clean.push(p.as_os_str());
                last_was_normal = false;
            }
            Component::RootDir => {
                clean.push(comp.as_os_str());
                last_was_normal = false;
            }
            Component::CurDir => {
                last_was_normal = false;
            }
            Component::Normal(part) => {
                clean.push(part);
                last_was_normal = true;
            }
            Component::ParentDir => {
                return Err(format!(
                    "--out must not contain parent-directory traversal ('..'): {}",
                    raw.display()
                ));
            }
        }
    }
    if !last_was_normal {
        return Err(format!("--out must name a regular file path: {}", raw.display()));
    }

    validate_out_ancestors_no_symlinks(&clean)?;
    Ok(clean)
}

fn validate_out_ancestors_no_symlinks(abs_out: &Path) -> Result<(), String> {
    let ancestors: Vec<&Path> = abs_out.ancestors().collect();
    for &anc in ancestors.iter().rev() {
        if anc == abs_out {
            match fs::symlink_metadata(anc) {
                Ok(meta) if meta.file_type().is_symlink() => {
                    return Err(format!("--out must not be a symlink: {}", anc.display()));
                }
                Ok(meta) if !meta.is_file() => {
                    return Err(format!(
                        "--out destination exists and is not a regular file: {}",
                        anc.display()
                    ));
                }
                Ok(meta) => {
                    #[cfg(unix)]
                    {
                        use std::os::unix::fs::MetadataExt as _;

                        if meta.nlink() > 1 {
                            return Err(format!(
                                "--out destination must not be a hardlink (nlink={}): {}",
                                meta.nlink(),
                                anc.display()
                            ));
                        }
                    }
                    #[cfg(not(unix))]
                    let _ = meta;
                }
                Err(e) if e.kind() == ErrorKind::NotFound => {}
                Err(e) => return Err(format!("stat --out {}: {e}", anc.display())),
            }
        } else {
            match fs::symlink_metadata(anc) {
                Ok(meta) if meta.file_type().is_symlink() => {
                    return Err(format!("--out ancestor must not be a symlink: {}", anc.display()));
                }
                Ok(meta) if !meta.is_dir() => {
                    return Err(format!("--out ancestor is not a directory: {}", anc.display()));
                }
                Ok(_) => {}
                Err(e) if e.kind() == ErrorKind::NotFound => {}
                Err(e) => return Err(format!("stat --out ancestor {}: {e}", anc.display())),
            }
        }
    }
    Ok(())
}

#[cfg(unix)]
fn os_str_to_single_component_cstring(
    part: &std::ffi::OsStr,
    label: &str,
) -> Result<std::ffi::CString, String> {
    use std::os::unix::ffi::OsStrExt as _;

    let bytes = part.as_bytes();
    if bytes.is_empty() || bytes == b"." || bytes == b".." || bytes.contains(&b'/') {
        return Err(format!("invalid {label}: {}", Path::new(part).display()));
    }
    std::ffi::CString::new(bytes)
        .map_err(|_| format!("{label} contains interior NUL byte: {}", Path::new(part).display()))
}

#[cfg(unix)]
fn write_out_report_dirfd_unix(abs_out: &Path, contents: &[u8]) -> Result<(), String> {
    use std::{
        collections::hash_map::RandomState,
        ffi::CString,
        hash::BuildHasher as _,
        os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd},
    };

    struct TempEntryGuard<'a> {
        parent_fd: &'a OwnedFd,
        name: CString,
        armed: bool,
    }

    impl Drop for TempEntryGuard<'_> {
        fn drop(&mut self) {
            if self.armed {
                // SAFETY: `parent_fd` is a valid open directory fd and `name`
                // is a NUL-terminated single-component filename created by us.
                let _ =
                    unsafe { libc::unlinkat(self.parent_fd.as_raw_fd(), self.name.as_ptr(), 0) };
            }
        }
    }

    if !abs_out.is_absolute() {
        return Err(format!("--out must resolve to an absolute path: {}", abs_out.display()));
    }
    let parent = abs_out
        .parent()
        .ok_or_else(|| format!("--out path has no parent directory: {}", abs_out.display()))?;
    let leaf_os = abs_out
        .file_name()
        .ok_or_else(|| format!("--out must name a regular file path: {}", abs_out.display()))?;
    let leaf_cstr = os_str_to_single_component_cstring(leaf_os, "--out file name")?;

    let root_cstr = CString::new("/").expect("static root CString");
    let raw_root = loop {
        // SAFETY: `root_cstr` is a valid NUL-terminated string (`"/"`).
        let fd = unsafe {
            libc::open(root_cstr.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC)
        };
        if fd >= 0 {
            break fd;
        }
        let err = std::io::Error::last_os_error();
        if err.kind() != ErrorKind::Interrupted {
            return Err(format!("open root directory `/`: {err}"));
        }
    };
    // SAFETY: `raw_root >= 0` is a freshly opened descriptor owned solely here.
    let mut cur_fd = unsafe { OwnedFd::from_raw_fd(raw_root) };

    for comp in parent.components() {
        match comp {
            Component::RootDir | Component::CurDir => {}
            Component::ParentDir | Component::Prefix(_) => {
                return Err(format!(
                    "--out must not contain parent-directory traversal ('..'): {}",
                    abs_out.display()
                ));
            }
            Component::Normal(seg) => {
                let seg_cstr = os_str_to_single_component_cstring(seg, "--out ancestor")?;
                let open_step = |dir_fd: &OwnedFd| -> Result<OwnedFd, std::io::Error> {
                    loop {
                        // SAFETY: `dir_fd` is a valid open directory fd and
                        // `seg_cstr` is a single-component NUL-terminated name.
                        let fd = unsafe {
                            libc::openat(
                                dir_fd.as_raw_fd(),
                                seg_cstr.as_ptr(),
                                libc::O_RDONLY
                                    | libc::O_DIRECTORY
                                    | libc::O_NOFOLLOW
                                    | libc::O_CLOEXEC,
                            )
                        };
                        if fd >= 0 {
                            // SAFETY: `fd >= 0` is newly opened and owned here.
                            return Ok(unsafe { OwnedFd::from_raw_fd(fd) });
                        }
                        let err = std::io::Error::last_os_error();
                        if err.kind() != ErrorKind::Interrupted {
                            return Err(err);
                        }
                    }
                };

                let next_fd = match open_step(&cur_fd) {
                    Ok(fd) => fd,
                    Err(e) if e.raw_os_error() == Some(libc::ELOOP) => {
                        return Err(format!(
                            "--out ancestor must not be a symlink: {}",
                            abs_out.display()
                        ));
                    }
                    Err(e) if e.raw_os_error() == Some(libc::ENOTDIR) => {
                        return Err(format!(
                            "--out ancestor is not a directory: {}",
                            abs_out.display()
                        ));
                    }
                    Err(e) if e.kind() == ErrorKind::NotFound => {
                        // SAFETY: `cur_fd` is a valid open directory fd and
                        // `seg_cstr` is a single-component NUL-terminated name.
                        let mk_rc =
                            unsafe { libc::mkdirat(cur_fd.as_raw_fd(), seg_cstr.as_ptr(), 0o777) };
                        if mk_rc < 0 {
                            let mk_err = std::io::Error::last_os_error();
                            if mk_err.kind() != ErrorKind::AlreadyExists {
                                return Err(format!(
                                    "create parent directory for {}: {mk_err}",
                                    abs_out.display()
                                ));
                            }
                        }
                        open_step(&cur_fd).map_err(|re| match re.raw_os_error() {
                            Some(libc::ELOOP) => {
                                format!(
                                    "--out ancestor must not be a symlink: {}",
                                    abs_out.display()
                                )
                            }
                            Some(libc::ENOTDIR) => {
                                format!("--out ancestor is not a directory: {}", abs_out.display())
                            }
                            _ => format!("open parent directory for {}: {re}", abs_out.display()),
                        })?
                    }
                    Err(e) => {
                        return Err(format!("open --out ancestor for {}: {e}", abs_out.display()));
                    }
                };
                cur_fd = next_fd;
            }
        }
    }

    let parent_fd = cur_fd;
    let check_leaf = || -> Result<(), String> {
        // SAFETY: `libc::stat` is a plain C struct for which all-zero is valid.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        // SAFETY: `parent_fd` is a valid open directory fd, `leaf_cstr` is a
        // valid NUL-terminated name, and `st` is writable `libc::stat` storage.
        let rc = unsafe {
            libc::fstatat(
                parent_fd.as_raw_fd(),
                leaf_cstr.as_ptr(),
                &mut st,
                libc::AT_SYMLINK_NOFOLLOW,
            )
        };
        if rc == 0 {
            let fmt = st.st_mode & libc::S_IFMT;
            if fmt == libc::S_IFLNK {
                return Err(format!("--out must not be a symlink: {}", abs_out.display()));
            }
            if fmt != libc::S_IFREG {
                return Err(format!(
                    "--out destination exists and is not a regular file: {}",
                    abs_out.display()
                ));
            }
            if st.st_nlink > 1 {
                return Err(format!(
                    "--out destination must not be a hardlink (nlink={}): {}",
                    st.st_nlink,
                    abs_out.display()
                ));
            }
            Ok(())
        } else {
            let err = std::io::Error::last_os_error();
            if err.kind() == ErrorKind::NotFound {
                Ok(())
            } else {
                Err(format!("stat --out {}: {err}", abs_out.display()))
            }
        }
    };

    check_leaf()?;

    let pid = std::process::id();
    let hasher_state = RandomState::new();
    let mut staged: Option<(fs::File, TempEntryGuard<'_>)> = None;
    for attempt in 0u64..64 {
        let nonce = hasher_state.hash_one((pid, attempt));
        let tmp_name = CString::new(format!(".anneal-diff-tmp-{pid}-{nonce:016x}"))
            .expect("hex temp filename has no NUL");
        // SAFETY: `parent_fd` is a valid open directory fd and `tmp_name` is a
        // NUL-terminated single-component filename.
        let fd = unsafe {
            libc::openat(
                parent_fd.as_raw_fd(),
                tmp_name.as_ptr(),
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0o666,
            )
        };
        if fd >= 0 {
            // SAFETY: `fd >= 0` is newly created and owned solely here.
            let file = fs::File::from(unsafe { OwnedFd::from_raw_fd(fd) });
            let guard = TempEntryGuard { parent_fd: &parent_fd, name: tmp_name, armed: true };
            staged = Some((file, guard));
            break;
        }
        let err = std::io::Error::last_os_error();
        if err.kind() == ErrorKind::AlreadyExists || err.kind() == ErrorKind::Interrupted {
            continue;
        }
        return Err(format!("stage fuzz report in {}: {err}", parent.display()));
    }

    let (mut tmp_file, mut tmp_guard) = staged
        .ok_or_else(|| format!("exhausted temporary filename attempts in {}", parent.display()))?;

    tmp_file
        .write_all(contents)
        .and_then(|()| tmp_file.flush())
        .map_err(|e| format!("write staged fuzz report {}: {e}", abs_out.display()))?;
    drop(tmp_file);

    check_leaf()?;

    // Perform a single-component `renameat` strictly inside `parent_fd` so
    // neither source nor destination re-resolves ancestor pathnames.
    // SAFETY: `parent_fd` is a valid open directory fd, and both
    // `tmp_guard.name` and `leaf_cstr` are NUL-terminated leaf names.
    let ren_rc = unsafe {
        libc::renameat(
            parent_fd.as_raw_fd(),
            tmp_guard.name.as_ptr(),
            parent_fd.as_raw_fd(),
            leaf_cstr.as_ptr(),
        )
    };
    if ren_rc != 0 {
        let err = std::io::Error::last_os_error();
        return Err(format!("persist fuzz report {}: {err}", abs_out.display()));
    }
    tmp_guard.armed = false;
    Ok(())
}

#[cfg(not(unix))]
fn ensure_dir_chain_no_symlinks(dir: &Path) -> Result<(), String> {
    let mut cur = PathBuf::new();
    for comp in dir.components() {
        cur.push(comp.as_os_str());
        match fs::symlink_metadata(&cur) {
            Ok(meta) => {
                if meta.file_type().is_symlink() {
                    return Err(format!("--out ancestor must not be a symlink: {}", cur.display()));
                }
                if !meta.is_dir() {
                    return Err(format!("--out ancestor is not a directory: {}", cur.display()));
                }
            }
            Err(e) if e.kind() == ErrorKind::NotFound => {
                match fs::create_dir(&cur) {
                    Ok(()) => {}
                    Err(ce) if ce.kind() == ErrorKind::AlreadyExists => {}
                    Err(ce) => {
                        return Err(format!("create parent directory {}: {ce}", cur.display()));
                    }
                }
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|me| format!("verify parent directory {}: {me}", cur.display()))?;
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(format!(
                        "--out ancestor is not a real directory: {}",
                        cur.display()
                    ));
                }
            }
            Err(e) => return Err(format!("stat --out ancestor {}: {e}", cur.display())),
        }
    }
    Ok(())
}

fn write_out_report_no_symlinks(abs_out: &Path, contents: &[u8]) -> Result<(), String> {
    #[cfg(unix)]
    {
        write_out_report_dirfd_unix(abs_out, contents)
    }

    #[cfg(not(unix))]
    {
        validate_out_ancestors_no_symlinks(abs_out)?;
        let parent = abs_out
            .parent()
            .ok_or_else(|| format!("--out path has no parent directory: {}", abs_out.display()))?;
        ensure_dir_chain_no_symlinks(parent)?;
        let mut temp = tempfile::NamedTempFile::new_in(parent)
            .map_err(|e| format!("stage fuzz report in {}: {e}", parent.display()))?;
        validate_out_ancestors_no_symlinks(abs_out)?;
        temp.write_all(contents)
            .and_then(|()| temp.flush())
            .map_err(|e| format!("write staged fuzz report {}: {e}", abs_out.display()))?;
        temp.persist(abs_out)
            .map_err(|e| format!("persist fuzz report {}: {e}", abs_out.display()))?;
        Ok(())
    }
}

fn run_cli(args: &[String]) -> Result<ExitCode, String> {
    if args.is_empty() || matches!(args[0].as_str(), "-h" | "--help" | "help") {
        println!("{}", usage());
        return Ok(ExitCode::SUCCESS);
    }
    match args[0].as_str() {
        "run" => run_corpus_subcommand(args),
        "fuzz" => run_fuzz_subcommand(args),
        other => Err(format!("unknown subcommand {other:?}\n\n{}", usage())),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    match run_cli(&args) {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn out_path_creates_real_nested_dirs_and_writes_report() {
        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let rel = Path::new("nested/sub/report.json");
        let resolved = resolve_and_validate_out_path_from(rel, &base).unwrap();
        write_out_report_no_symlinks(&resolved, b"{\"ok\":true}\n").unwrap();
        assert_eq!(fs::read_to_string(&resolved).unwrap(), "{\"ok\":true}\n");

        // Overwriting an existing regular file also succeeds cleanly.
        write_out_report_no_symlinks(&resolved, b"{\"ok\":false}\n").unwrap();
        assert_eq!(fs::read_to_string(&resolved).unwrap(), "{\"ok\":false}\n");
    }

    #[cfg(unix)]
    #[test]
    fn out_path_rejects_leaf_symlink_and_symlinked_ancestors_and_traversal() {
        use std::os::unix::fs::symlink;

        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let outside = tempfile::tempdir().unwrap();
        let outside_canon = fs::canonicalize(outside.path()).unwrap();

        // 1. Direct leaf symlink.
        let target_file = outside_canon.join("outside.json");
        fs::write(&target_file, "untouched").unwrap();
        let leaf_link = base.join("leaf_link.json");
        symlink(&target_file, &leaf_link).unwrap();
        let err_leaf = resolve_and_validate_out_path_from(&leaf_link, &base).unwrap_err();
        assert!(err_leaf.contains("symlink"), "unexpected error: {err_leaf}");

        // 2. Existing symlinked parent directory (`<sym_dir>/report.json`).
        let sym_dir = base.join("sym_dir");
        symlink(&outside_canon, &sym_dir).unwrap();
        let direct_under_sym = sym_dir.join("report.json");
        let err_anc = resolve_and_validate_out_path_from(&direct_under_sym, &base).unwrap_err();
        assert!(err_anc.contains("ancestor must not be a symlink"), "unexpected: {err_anc}");
        assert!(write_out_report_no_symlinks(&direct_under_sym, b"{}").is_err());
        assert!(!outside_canon.join("report.json").exists());

        // 3. Non-existent nested subdirectories beneath a symlinked ancestor.
        let deep_under_sym = sym_dir.join("new_a/new_b/report.json");
        let err_deep = resolve_and_validate_out_path_from(&deep_under_sym, &base).unwrap_err();
        assert!(err_deep.contains("ancestor must not be a symlink"), "unexpected: {err_deep}");
        assert!(write_out_report_no_symlinks(&deep_under_sym, b"{}").is_err());
        assert!(!outside_canon.join("new_a").exists());

        // 4. Relative path under a symlinked directory and `..` traversal.
        assert!(resolve_and_validate_out_path_from(Path::new("sym_dir/out.json"), &base).is_err());
        assert!(resolve_and_validate_out_path_from(Path::new("real/../out.json"), &base).is_err());
        assert!(resolve_and_validate_out_path_from(Path::new("dir_only/"), &base).is_err());
        assert_eq!(fs::read_to_string(&target_file).unwrap(), "untouched");
    }

    #[cfg(unix)]
    #[test]
    fn write_out_report_dirfd_rejects_leaf_symlink_fifo_and_cleans_up_temp() {
        use std::{
            ffi::CString,
            os::unix::{ffi::OsStrExt as _, fs::symlink},
        };

        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let outside = tempfile::tempdir().unwrap();
        let outside_file = fs::canonicalize(outside.path()).unwrap().join("victim.json");
        fs::write(&outside_file, "keep").unwrap();

        let raced_leaf = base.join("raced_leaf.json");
        symlink(&outside_file, &raced_leaf).unwrap();
        let sym_err = write_out_report_no_symlinks(&raced_leaf, b"{\"bad\":1}").unwrap_err();
        assert!(sym_err.contains("symlink"), "{sym_err}");
        assert_eq!(fs::read_to_string(&outside_file).unwrap(), "keep");

        let hard_target = base.join("hard_target.json");
        fs::write(&hard_target, "keep-hard").unwrap();
        let hard_leaf = base.join("hard_leaf.json");
        fs::hard_link(&hard_target, &hard_leaf).unwrap();
        let hard_pre_err = resolve_and_validate_out_path_from(&hard_leaf, &base).unwrap_err();
        assert!(hard_pre_err.contains("hardlink"), "{hard_pre_err}");
        let hard_err = write_out_report_no_symlinks(&hard_leaf, b"{\"bad\":3}").unwrap_err();
        assert!(hard_err.contains("hardlink"), "{hard_err}");
        assert_eq!(fs::read_to_string(&hard_target).unwrap(), "keep-hard");

        let fifo_path = base.join("fifo_out.json");
        let fifo_c = CString::new(fifo_path.as_os_str().as_bytes()).unwrap();
        // SAFETY: `fifo_c` is a valid NUL-terminated path inside `base`.
        assert_eq!(unsafe { libc::mkfifo(fifo_c.as_ptr(), 0o600) }, 0);
        let fifo_err = write_out_report_no_symlinks(&fifo_path, b"{\"bad\":2}").unwrap_err();
        assert!(fifo_err.contains("not a regular file"), "{fifo_err}");

        for entry in fs::read_dir(&base).unwrap() {
            let name = entry.unwrap().file_name().to_string_lossy().into_owned();
            assert!(!name.starts_with(".anneal-diff-tmp-"), "leaked temp file: {name}");
        }
    }

    #[test]
    fn fuzz_subcommand_rejects_simultaneous_mir_eval_bin_and_manifest() {
        let args = vec![
            "fuzz".to_owned(),
            "--mir-eval-bin".to_owned(),
            "/tmp/fake-bin".to_owned(),
            "--mir-eval-manifest".to_owned(),
            "/tmp/Cargo.toml".to_owned(),
        ];
        let err = run_fuzz_subcommand(&args).unwrap_err();
        assert!(err.contains("mutually exclusive"), "{err}");

        let fuel_args = vec![
            "fuzz".to_owned(),
            "--fuel".to_owned(),
            "0".to_owned(),
            "--mir-eval-manifest".to_owned(),
            "/nonexistent/Cargo.toml".to_owned(),
            "--out".to_owned(),
            "/nonexistent/sub/report.json".to_owned(),
        ];
        let fuel_err = run_fuzz_subcommand(&fuel_args).unwrap_err();
        assert!(fuel_err.contains("--fuel"), "{fuel_err}");
    }
}
