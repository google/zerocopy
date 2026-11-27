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
    DifferentialConfig, DifferentialEngine, DifferentialReport,
    corpus::curated_corpus,
    dedup::{BugRegistry, dialect_key_for_mode},
    filter_corpus_cases,
    lean_trace_runner::LeanTraceMode,
    load_fuzz_programs_from_dir, resolve_anneal_root,
    telemetry::{
        KnownBugsExport, SemanticDetailRecord, TelemetryContext, record_report_telemetry_witnesses,
        try_normalize_repo_slug,
    },
    validate_cli_run_plan_with_corpus_dir, validate_distinct_output_paths_with_dirs,
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

    /// Explicit `anneal/` (or repository) root directory (overrides
    /// `ANNEAL_ROOT` and compile-time `CARGO_MANIFEST_DIR` for relocated
    /// binaries).
    #[arg(long, value_name = "PATH")]
    anneal_root: Option<PathBuf>,

    /// Optional directory containing `.json`/`.jsonl` [`FuzzProgram`] seed
    /// artifacts (also read from `ANNEAL_CORPUS_DIR`).
    #[arg(long, value_name = "PATH")]
    corpus_dir: Option<PathBuf>,

    /// Write structured JSON report to `<PATH>`.
    #[arg(long)]
    json_report: Option<PathBuf>,

    /// Write `anneal-itree-semantic-detail/v1` JSONL telemetry to `<PATH>`.
    #[arg(long, value_name = "PATH")]
    semantics_detail_out: Option<PathBuf>,

    /// Write deduplicated `anneal-known-bug/v1` record(s) to `<PATH>`
    /// (`.jsonl`/`.ndjson` emits one row per canonical bug retaining export
    /// provenance, or a summary line when empty; `.json` emits a structured
    /// `anneal-known-bugs/v1` envelope).
    #[arg(long, value_name = "PATH")]
    known_bugs_out: Option<PathBuf>,

    /// Repository override for emitted telemetry (e.g. `google/zerocopy`).
    #[arg(long)]
    repo: Option<String>,

    /// Branch override for emitted telemetry (e.g. `main` or `unstable`).
    #[arg(long)]
    branch: Option<String>,

    /// Environment profile override for emitted telemetry.
    #[arg(long)]
    env_profile: Option<String>,

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

fn should_run_curated_corpus(args: &CliArgs) -> bool {
    // Only explicit CLI `--fuzz` or `--corpus-dir` skips the default curated
    // corpus when `--corpus` is omitted; an ambient `ANNEAL_CORPUS_DIR` adds
    // seeds without silently suppressing curated corpus checks.
    args.corpus || (args.fuzz.is_none() && args.corpus_dir.is_none())
}

fn main() -> ExitCode {
    run_with_discover_cfg(CliArgs::parse(), TelemetryContext::discover, true)
}

fn normalize_branch_override(raw: &str) -> Result<String, String> {
    let trimmed = raw.trim();
    if trimmed.is_empty() || trimmed.chars().any(char::is_whitespace) {
        return Err("branch must be non-empty without internal whitespace".to_string());
    }
    Ok(trimmed.to_string())
}

fn apply_branch_override(ctx: &mut TelemetryContext, branch: String) {
    let is_main = branch == "main";
    ctx.branch = branch;
    ctx.branch_scope = if is_main { "main".to_string() } else { "unstable_only".to_string() };
    ctx.exposed_on_main = is_main;
}

fn run_with_discover_cfg<F>(
    args: CliArgs,
    mut discover_ctx: F,
    honor_env_require_miri: bool,
) -> ExitCode
where
    F: FnMut(&std::path::Path) -> TelemetryContext,
{
    let corpus_dir = args.corpus_dir.clone().or_else(|| {
        std::env::var_os("ANNEAL_CORPUS_DIR").filter(|v| !v.is_empty()).map(PathBuf::from)
    });
    let run_corpus = should_run_curated_corpus(&args);

    if let Err(e) = validate_cli_run_plan_with_corpus_dir(
        run_corpus,
        corpus_dir.is_some(),
        args.filter.as_deref(),
        args.fuzz,
        args.shrink,
        args.witness_dir.is_some(),
    ) {
        eprintln!("error: {e}");
        return ExitCode::from(2);
    }

    let mut output_paths: Vec<(&str, &std::path::Path)> = Vec::new();
    if let Some(p) = args.json_report.as_deref() {
        output_paths.push(("--json-report", p));
    }
    if let Some(p) = args.semantics_detail_out.as_deref() {
        output_paths.push(("--semantics-detail-out", p));
    }
    if let Some(p) = args.known_bugs_out.as_deref() {
        output_paths.push(("--known-bugs-out", p));
    }
    let mut managed_dirs: Vec<(&str, &std::path::Path)> = Vec::new();
    if let Some(d) = corpus_dir.as_deref() {
        managed_dirs.push(("--corpus-dir", d));
    }
    if let Some(d) = args.witness_dir.as_deref() {
        managed_dirs.push(("--witness-dir", d));
    }
    if let Some(d) = args.cache_dir.as_deref() {
        managed_dirs.push(("--cache-dir", d));
    }
    if let Err(e) = validate_distinct_output_paths_with_dirs(&output_paths, &managed_dirs) {
        eprintln!("error: {e}");
        return ExitCode::from(2);
    }
    let validated_repo_override = match args.repo.as_deref() {
        Some(raw) => match try_normalize_repo_slug(raw) {
            Ok(slug) => Some(slug),
            Err(e) => {
                eprintln!("error: invalid --repo override {raw:?}: {e}");
                return ExitCode::from(2);
            }
        },
        None => None,
    };
    let validated_branch_override = match args.branch.as_deref() {
        Some(raw) => match normalize_branch_override(raw) {
            Ok(branch) => Some(branch),
            Err(e) => {
                eprintln!("error: invalid --branch override {raw:?}: {e}");
                return ExitCode::from(2);
            }
        },
        None => None,
    };

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

    let anneal_root = match resolve_anneal_root(args.anneal_root.as_deref()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: cannot locate anneal workspace root: {e}");
            return ExitCode::from(2);
        }
    };

    let seed_programs = match corpus_dir {
        Some(ref dir) => match load_fuzz_programs_from_dir(dir) {
            Ok(seeds) => {
                if seeds.is_empty() && selected_corpus.is_none() && args.fuzz.is_none() {
                    eprintln!(
                        "error: explicit --corpus-dir {} contained no supported seed programs and neither --corpus nor --fuzz was passed",
                        dir.display()
                    );
                    return ExitCode::from(2);
                }
                seeds
            }
            Err(e) => {
                eprintln!("error: {e}");
                return ExitCode::from(2);
            }
        },
        None => Vec::new(),
    };

    // Capture build provenance and checkout cleanliness before preparing caches
    // or writing `--shrink --witness-dir` / `--json-report` artifacts.
    let pre_run_telemetry_ctx = (args.semantics_detail_out.is_some()
        || args.known_bugs_out.is_some())
    .then(|| discover_ctx(&anneal_root));

    let mut cfg = DifferentialConfig::for_workspace_with_cache(anneal_root, args.cache_dir.clone());
    cfg.enable_miri = !args.no_miri;
    if honor_env_require_miri {
        if args.require_miri {
            cfg.require_miri = true;
        }
    } else {
        cfg.require_miri = args.require_miri;
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
    let mut seen_witness_stems = std::collections::BTreeSet::new();

    if let Some(corpus) = selected_corpus {
        let rep = engine.run_cases(&corpus);
        all_cases.extend(rep.cases);
        all_witnesses.extend(rep.witnesses);
    }

    if !seed_programs.is_empty() {
        let rep = engine.run_fuzz_programs_with_seen(&seed_programs, &mut seen_witness_stems);
        let base_idx = all_cases.len();
        all_cases.extend(rep.cases);
        all_witnesses.extend(rep.witnesses.into_iter().map(|mut w| {
            w.report_index = w.report_index.map(|idx| base_idx + idx);
            w
        }));
    }

    if let Some(fuzz_n) = args.fuzz {
        let generated = anneal_itree_diff::fuzzer::generate_fuzz_batch(args.seed, fuzz_n);
        let rep = engine.run_fuzz_programs_with_seen(&generated, &mut seen_witness_stems);
        let base_idx = all_cases.len();
        all_cases.extend(rep.cases);
        all_witnesses.extend(rep.witnesses.into_iter().map(|mut w| {
            w.report_index = w.report_index.map(|idx| base_idx + idx);
            w
        }));
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

    if let Some(mut ctx) = pre_run_telemetry_ctx {
        if let Some(repo) = validated_repo_override {
            ctx.repo = repo;
        }
        if let Some(branch) = validated_branch_override {
            apply_branch_override(&mut ctx, branch);
        }
        if let Some(profile) = &args.env_profile {
            ctx.environment_profile = profile.clone();
        }

        let dialect_key = dialect_key_for_mode(combined.lean_mode, ctx.profile_v2);
        let mut registry = BugRegistry::new(&ctx.repo);
        record_report_telemetry_witnesses(
            &mut registry,
            &combined.cases,
            &combined.witnesses,
            &ctx.branch_scope,
            ctx.exposed_on_main,
            dialect_key,
            &ctx.commit_sha,
        );

        if let Some(path) = &args.semantics_detail_out {
            let rec =
                match SemanticDetailRecord::from_report_and_registry(&combined, &registry, &ctx) {
                    Ok(r) => r,
                    Err(e) => {
                        eprintln!("error: build semantics-detail telemetry: {e}");
                        return ExitCode::from(2);
                    }
                };
            if let Err(e) = rec.write_jsonl(path) {
                eprintln!("error: write semantics-detail JSONL {}: {e}", path.display());
                return ExitCode::from(2);
            }
        }
        if let Some(path) = &args.known_bugs_out {
            let export = match KnownBugsExport::from_report_and_registry(&combined, &registry, &ctx)
            {
                Ok(ex) => ex,
                Err(e) => {
                    eprintln!("error: build known-bugs export: {e}");
                    return ExitCode::from(2);
                }
            };
            if let Err(e) = export.write_to_path(path) {
                eprintln!("error: write known-bugs export {}: {e}", path.display());
                return ExitCode::from(2);
            }
        }
    }

    if combined.has_critical_failures() { ExitCode::from(1) } else { ExitCode::SUCCESS }
}

#[cfg(test)]
mod tests {
    use anneal_itree_diff::fuzzer::generate_fuzz_batch;

    use super::*;

    #[test]
    fn cli_captures_telemetry_provenance_before_writing_reports_or_witnesses() {
        let tmp = tempfile::tempdir().unwrap();
        let anneal_root = resolve_anneal_root(None).expect("locate anneal root");
        let seed_dir = tmp.path().join("seeds");
        fs::create_dir_all(&seed_dir).unwrap();
        let prog = generate_fuzz_batch(0xFEED_1234, 1).pop().unwrap();
        fs::write(seed_dir.join("seed.json"), serde_json::to_string(&prog).unwrap()).unwrap();

        let witness_dir = tmp.path().join("witnesses");
        let json_report = tmp.path().join("report.json");
        let detail_out = tmp.path().join("detail.jsonl");
        let kb_out = tmp.path().join("known_bugs.json");
        let cache_dir = tmp.path().join("cache");

        let args = CliArgs::parse_from([
            "itree-diff",
            "--anneal-root",
            anneal_root.to_str().unwrap(),
            "--corpus-dir",
            seed_dir.to_str().unwrap(),
            "--shrink",
            "--witness-dir",
            witness_dir.to_str().unwrap(),
            "--cache-dir",
            cache_dir.to_str().unwrap(),
            "--json-report",
            json_report.to_str().unwrap(),
            "--semantics-detail-out",
            detail_out.to_str().unwrap(),
            "--known-bugs-out",
            kb_out.to_str().unwrap(),
            "--no-miri",
            "--no-lean",
        ]);

        let mut discover_called_before_writes = false;
        let rc = run_with_discover_cfg(
            args,
            |_root| {
                assert!(!json_report.exists(), "json-report must not exist before provenance");
                assert!(!witness_dir.exists(), "witness-dir must not exist before provenance");
                assert!(!cache_dir.exists(), "cache-dir must not exist before provenance");
                discover_called_before_writes = true;
                TelemetryContext {
                    repo: "google/zerocopy".to_string(),
                    branch: "main".to_string(),
                    branch_scope: "main".to_string(),
                    exposed_on_main: true,
                    commit_sha: "1111111111111111111111111111111111111111".to_string(),
                    commit_unix_ts: 1_700_000_000,
                    environment_profile: "test".to_string(),
                    source_url: String::new(),
                    profile_v2: false,
                    build_freshness_override: None,
                    build_exit_code_override: None,
                    head_provenance_verified: true,
                    discovered_head_sha: Some(
                        "1111111111111111111111111111111111111111".to_string(),
                    ),
                }
            },
            false,
        );
        assert_eq!(rc, ExitCode::SUCCESS);
        assert!(discover_called_before_writes);
        assert!(json_report.exists());
        let detail_json: serde_json::Value =
            serde_json::from_str(fs::read_to_string(&detail_out).unwrap().trim()).unwrap();
        assert_eq!(detail_json["build_freshness"], "verified_at_head");
        let kb_json: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(&kb_out).unwrap()).unwrap();
        assert_eq!(kb_json["build_freshness"], "verified_at_head");
    }

    #[test]
    fn curated_corpus_selection_ignores_ambient_corpus_dir_when_flags_omitted() {
        let default_args = CliArgs::parse_from(["itree-diff"]);
        assert!(should_run_curated_corpus(&default_args));

        let explicit_dir_args = CliArgs::parse_from(["itree-diff", "--corpus-dir", "/tmp/seeds"]);
        assert!(!should_run_curated_corpus(&explicit_dir_args));

        let explicit_both =
            CliArgs::parse_from(["itree-diff", "--corpus", "--corpus-dir", "/tmp/seeds"]);
        assert!(should_run_curated_corpus(&explicit_both));
    }

    #[test]
    fn cli_rejects_colliding_telemetry_output_paths_without_clobbering() {
        let tmp = tempfile::tempdir().unwrap();
        let anneal_root = resolve_anneal_root(None).expect("locate anneal root");
        let seed_dir = tmp.path().join("seeds");
        fs::create_dir_all(&seed_dir).unwrap();
        let prog = generate_fuzz_batch(0xFEED_4321, 1).pop().unwrap();
        fs::write(seed_dir.join("seed.json"), serde_json::to_string(&prog).unwrap()).unwrap();

        let shared_out = tmp.path().join("shared_out.json");
        let dot_alias = tmp.path().join("sub").join("..").join("shared_out.json");
        fs::write(&shared_out, "sentinel-keep-intact\n").unwrap();

        for (flag_a, path_a, flag_b, path_b) in [
            ("--semantics-detail-out", &shared_out, "--known-bugs-out", &shared_out),
            ("--json-report", &shared_out, "--semantics-detail-out", &dot_alias),
            ("--json-report", &dot_alias, "--known-bugs-out", &shared_out),
        ] {
            let args = CliArgs::parse_from([
                "itree-diff",
                "--anneal-root",
                anneal_root.to_str().unwrap(),
                "--corpus-dir",
                seed_dir.to_str().unwrap(),
                flag_a,
                path_a.to_str().unwrap(),
                flag_b,
                path_b.to_str().unwrap(),
                "--no-miri",
                "--no-lean",
            ]);
            let rc = run_with_discover_cfg(args, |_| unreachable!("must fail preflight"), false);
            assert_eq!(rc, ExitCode::from(2));
            assert_eq!(
                fs::read_to_string(&shared_out).unwrap(),
                "sentinel-keep-intact\n",
                "colliding flags must fail before writing any output"
            );
        }

        // Report paths inside `--corpus-dir` or `--witness-dir` (or
        // colliding managed dirs) must also be rejected without clobbering.
        let seed_file = seed_dir.join("seed.json");
        let seed_before = fs::read_to_string(&seed_file).unwrap();
        let witness_dir = tmp.path().join("witnesses");
        let witness_collide = witness_dir.join("case.witness.json");

        let corpus_collision = CliArgs::parse_from([
            "itree-diff",
            "--anneal-root",
            anneal_root.to_str().unwrap(),
            "--corpus-dir",
            seed_dir.to_str().unwrap(),
            "--json-report",
            seed_file.to_str().unwrap(),
            "--no-miri",
            "--no-lean",
        ]);
        assert_eq!(
            run_with_discover_cfg(corpus_collision, |_| unreachable!("must fail preflight"), false),
            ExitCode::from(2)
        );
        assert_eq!(fs::read_to_string(&seed_file).unwrap(), seed_before);

        let witness_collision = CliArgs::parse_from([
            "itree-diff",
            "--anneal-root",
            anneal_root.to_str().unwrap(),
            "--corpus-dir",
            seed_dir.to_str().unwrap(),
            "--shrink",
            "--witness-dir",
            witness_dir.to_str().unwrap(),
            "--semantics-detail-out",
            witness_collide.to_str().unwrap(),
            "--no-miri",
            "--no-lean",
        ]);
        assert_eq!(
            run_with_discover_cfg(
                witness_collision,
                |_| unreachable!("must fail preflight"),
                false
            ),
            ExitCode::from(2)
        );

        let managed_dir_collision = CliArgs::parse_from([
            "itree-diff",
            "--anneal-root",
            anneal_root.to_str().unwrap(),
            "--corpus-dir",
            seed_dir.to_str().unwrap(),
            "--shrink",
            "--witness-dir",
            seed_dir.to_str().unwrap(),
            "--no-miri",
            "--no-lean",
        ]);
        assert_eq!(
            run_with_discover_cfg(
                managed_dir_collision,
                |_| unreachable!("must fail preflight"),
                false,
            ),
            ExitCode::from(2)
        );
    }

    #[test]
    fn cli_rejects_invalid_explicit_repo_override_with_exit_2() {
        let tmp = tempfile::tempdir().unwrap();
        let anneal_root = resolve_anneal_root(None).expect("locate anneal root");
        let seed_dir = tmp.path().join("seeds");
        fs::create_dir_all(&seed_dir).unwrap();
        let prog = generate_fuzz_batch(0xFEED_9999, 1).pop().unwrap();
        fs::write(seed_dir.join("seed.json"), serde_json::to_string(&prog).unwrap()).unwrap();
        let kb_out = tmp.path().join("known_bugs.json");

        for bad_repo in ["work/customer/private.git", "file:///tmp/private.git", "", "zerocopy"] {
            let args = CliArgs::parse_from([
                "itree-diff",
                "--anneal-root",
                anneal_root.to_str().unwrap(),
                "--corpus-dir",
                seed_dir.to_str().unwrap(),
                "--known-bugs-out",
                kb_out.to_str().unwrap(),
                "--repo",
                bad_repo,
                "--no-miri",
                "--no-lean",
            ]);
            let rc = run_with_discover_cfg(args, |_| unreachable!("must fail preflight"), false);
            assert_eq!(rc, ExitCode::from(2), "bad_repo={bad_repo:?}");
            assert!(!kb_out.exists(), "invalid --repo must not write {kb_out:?}");
        }
    }

    #[test]
    fn cli_normalizes_and_validates_explicit_branch_override() {
        let tmp = tempfile::tempdir().unwrap();
        let anneal_root = resolve_anneal_root(None).expect("locate anneal root");
        let seed_dir = tmp.path().join("seeds");
        fs::create_dir_all(&seed_dir).unwrap();
        let prog = generate_fuzz_batch(0xFEED_8888, 1).pop().unwrap();
        fs::write(seed_dir.join("seed.json"), serde_json::to_string(&prog).unwrap()).unwrap();
        let kb_out = tmp.path().join("known_bugs.json");

        for bad_branch in ["", "   ", "\t\n", "main extra"] {
            let args = CliArgs::parse_from([
                "itree-diff",
                "--anneal-root",
                anneal_root.to_str().unwrap(),
                "--corpus-dir",
                seed_dir.to_str().unwrap(),
                "--known-bugs-out",
                kb_out.to_str().unwrap(),
                "--branch",
                bad_branch,
                "--no-miri",
                "--no-lean",
            ]);
            let rc = run_with_discover_cfg(args, |_| unreachable!("must fail preflight"), false);
            assert_eq!(rc, ExitCode::from(2), "bad_branch={bad_branch:?}");
            assert!(!kb_out.exists(), "invalid --branch must not write {kb_out:?}");
        }

        let norm_main = normalize_branch_override("  main \n").unwrap();
        let mut ctx = TelemetryContext::discover(&anneal_root);
        ctx.branch = "unstable".to_string();
        ctx.branch_scope = "unstable_only".to_string();
        ctx.exposed_on_main = false;
        apply_branch_override(&mut ctx, norm_main);
        assert_eq!(ctx.branch, "main");
        assert_eq!(ctx.branch_scope, "main");
        assert!(ctx.exposed_on_main);

        let args = CliArgs::parse_from([
            "itree-diff",
            "--anneal-root",
            anneal_root.to_str().unwrap(),
            "--corpus-dir",
            seed_dir.to_str().unwrap(),
            "--known-bugs-out",
            kb_out.to_str().unwrap(),
            "--branch",
            " main ",
            "--no-miri",
            "--no-lean",
        ]);
        let rc = run_with_discover_cfg(
            args,
            |root| {
                let mut d = TelemetryContext::discover(root);
                d.branch = "unstable".to_string();
                d.branch_scope = "unstable_only".to_string();
                d.exposed_on_main = false;
                d
            },
            false,
        );
        assert_eq!(rc, ExitCode::SUCCESS);
        let parsed: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(&kb_out).unwrap()).unwrap();
        assert_eq!(parsed["branch"].as_str(), Some("main"));
    }
}
