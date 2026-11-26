// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI driver for the Stage-1 multi-leg MIR differential oracle.

use std::{env, path::PathBuf, process::ExitCode};

use anneal_differential_tests::{RunOptions, default_manifest_path, run_differential_suite};

fn usage() -> &'static str {
    "Usage:
  anneal-diff run [--manifest <path>] [--capture-bin <path>]
                  [--mir-eval-bin <path>] [--cache-root <path>]
                  [--json] [--self-check-oracle]"
}

fn next_arg(args: &[String], idx: &mut usize, flag: &str) -> Result<String, String> {
    *idx += 1;
    args.get(*idx).cloned().ok_or_else(|| format!("missing argument after {flag}"))
}

fn run_cli(args: &[String]) -> Result<ExitCode, String> {
    if args.is_empty() || matches!(args[0].as_str(), "-h" | "--help" | "help") {
        println!("{}", usage());
        return Ok(ExitCode::SUCCESS);
    }
    if args[0] != "run" {
        return Err(format!("unknown subcommand {:?}\n\n{}", args[0], usage()));
    }

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
