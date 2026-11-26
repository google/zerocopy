// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI driver (`itree-diff`) for multi-step & multi-call observable-trace
//! differential testing, deterministic fuzzing, and 1-minimal shrinking.

use std::{fs, path::PathBuf, process::ExitCode};

use anneal_itree_diff::{
    DifferentialConfig, DifferentialEngine, DifferentialReport, corpus::curated_corpus,
    filter_corpus_cases, lean_trace_runner::LeanTraceMode, validate_cli_run_plan,
    workspace_anneal_root,
};
use clap::{Parser, ValueEnum};

#[derive(Clone, Copy, Debug, ValueEnum)]
enum CliLeanMode {
    Strict,
    Compositional,
}

impl From<CliLeanMode> for LeanTraceMode {
    fn from(m: CliLeanMode) -> Self {
        match m {
            CliLeanMode::Strict => Self::StrictVerbatim,
            CliLeanMode::Compositional => Self::CompositionalITree,
        }
    }
}

#[derive(Debug, Parser)]
#[command(
    name = "itree-diff",
    about = "4-way observable-trace (ITree) differential tester, fuzzer, and 1-minimal shrinker"
)]
struct CliArgs {
    /// Run the curated 6-category differential corpus.
    #[arg(long)]
    corpus: bool,

    /// Generate and differentially test N deterministic multi-call programs.
    #[arg(long, value_name = "N")]
    fuzz: Option<usize>,

    /// Deterministic PRNG seed for `--fuzz`.
    #[arg(long, default_value_t = 0xA11E_A101)]
    seed: u64,

    /// Shrink any critical divergence to a verified 1-minimal witness artifact
    /// (suppresses witness emission and reports a secondary `shrink-witness`
    /// error if the shrink budget is exhausted before 1-minimality).
    #[arg(long)]
    shrink: bool,

    /// Directory to write verified 1-minimal witness artifacts when `--shrink`
    /// succeeds.
    #[arg(long)]
    witness_dir: Option<PathBuf>,

    /// Explicit directory for content-keyed capture, Miri, and Lean caches.
    #[arg(long)]
    cache_dir: Option<PathBuf>,

    /// Write structured JSON report to `<PATH>`.
    #[arg(long)]
    json_report: Option<PathBuf>,

    /// Lean trace driver mode (`strict` or `compositional`).
    #[arg(long, value_enum, default_value_t = CliLeanMode::Compositional)]
    mode: CliLeanMode,

    /// Optional substring filter over corpus case IDs.
    #[arg(long)]
    filter: Option<String>,

    /// Fail closed with exit code 2 if Miri is unavailable at startup (and
    /// exit code 1 if any case degrades without Miri).
    #[arg(long)]
    require_miri: bool,

    /// Disable Miri authority execution.
    #[arg(long)]
    no_miri: bool,

    /// Disable Lean authority execution.
    #[arg(long)]
    no_lean: bool,
}

fn main() -> ExitCode {
    let args = CliArgs::parse();
    let run_corpus = args.corpus || args.fuzz.is_none();

    if let Err(e) = validate_cli_run_plan(
        run_corpus,
        args.filter.as_deref(),
        args.fuzz,
        args.shrink,
        args.witness_dir.is_some(),
    ) {
        eprintln!("error: {e}");
        return ExitCode::from(2);
    }

    let selected_corpus = if run_corpus {
        match filter_corpus_cases(curated_corpus(), args.filter.as_deref()) {
            Ok(cases) => Some(cases),
            Err(e) => {
                eprintln!("error: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };

    let anneal_root = match workspace_anneal_root() {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: cannot locate anneal workspace root: {e}");
            return ExitCode::from(2);
        }
    };

    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, args.cache_dir.clone());
    cfg.enable_miri = !args.no_miri;
    if args.require_miri {
        cfg.require_miri = true;
    }
    cfg.enable_lean = !args.no_lean;
    cfg.lean_mode = args.mode.into();
    cfg.shrink_on_divergence = args.shrink;
    cfg.witness_dir = args.witness_dir.clone();

    let engine = match DifferentialEngine::prepare(cfg) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("error: failed to initialize differential engine: {e}");
            return ExitCode::from(2);
        }
    };

    let mut all_cases = Vec::new();
    let mut all_witnesses = Vec::new();

    if let Some(corpus) = selected_corpus {
        let rep = engine.run_cases(&corpus);
        all_cases.extend(rep.cases);
        all_witnesses.extend(rep.witnesses);
    }

    if let Some(fuzz_n) = args.fuzz {
        let rep = engine.run_fuzz_campaign(args.seed, fuzz_n);
        all_cases.extend(rep.cases);
        all_witnesses.extend(rep.witnesses);
    }

    let combined = DifferentialReport::from_cases(
        &engine.miri_status,
        engine.miri.is_some(),
        engine.config.require_miri,
        &engine.mir_eval_status,
        engine.config.lean_mode,
        all_cases,
        all_witnesses,
    );

    if combined.counts.total == 0 {
        eprintln!("error: differential run executed 0 test cases");
        return ExitCode::from(2);
    }

    println!(
        "itree-diff summary: total={} agree={} degraded_no_miri={} degraded_no_lean={} conservative={} undeclared_ub={} disclosed_gap={} unsound_p0={} tool_error={} expectation_mismatches={} metamorphic={}/{} metamorphic_skipped={} miri={} mir_eval={}",
        combined.counts.total,
        combined.counts.agree,
        combined.counts.degraded_no_miri,
        combined.counts.degraded_no_lean,
        combined.counts.conservative_over_approx,
        combined.counts.undeclared_ub_fault,
        combined.counts.disclosed_gap_artifact,
        combined.counts.unsound_accept,
        combined.counts.tool_error,
        combined.counts.expectation_mismatches,
        combined.counts.metamorphic_passed,
        combined.counts.metamorphic_checked,
        combined.counts.metamorphic_skipped,
        combined.miri_status,
        combined.mir_eval_status,
    );
    for c in &combined.cases {
        println!("  [{}] {} ({:?})", c.verdict.label(), c.case_id, c.category);
        if c.verdict.is_critical_failure() {
            eprintln!("    FAILURE: {}", c.verdict);
        }
        if let Some(violation) = &c.expectation_violation {
            eprintln!("    FAILURE (expectation mismatch): {violation}");
        }
    }

    if let Some(path) = &args.json_report {
        match serde_json::to_string_pretty(&combined) {
            Ok(json) => {
                if let Err(e) = fs::write(path, json) {
                    eprintln!("error: write JSON report {}: {e}", path.display());
                    return ExitCode::from(2);
                }
            }
            Err(e) => {
                eprintln!("error: serialize JSON report: {e}");
                return ExitCode::from(2);
            }
        }
    }

    if combined.has_critical_failures() { ExitCode::from(1) } else { ExitCode::SUCCESS }
}
