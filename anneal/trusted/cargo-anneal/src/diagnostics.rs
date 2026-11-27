// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Actionable diagnostic hints for `cargo anneal verify` failure receipts.
//!
//! Maps opaque compiler, capture, cargo-shortcut, syntactic-preflight, and
//! Lean JSON diagnostic payloads to concise developer guidance without mutating
//! the underlying [`FailureReceipt`](crate::verify) `detail` contract.

use std::path::Path;

use serde_json::Value;

/// Pattern rule mapping a substring in a failure detail to a developer hint.
struct DetailRule {
    needle: &'static str,
    hint: &'static str,
}

const CARGO_RULES: &[DetailRule] = &[
    DetailRule {
        needle: "cannot inspect Cargo manifest",
        hint: "Pass `--manifest-path path/to/Cargo.toml` pointing to an existing library crate \
               manifest, or run from the crate root.",
    },
    DetailRule {
        needle: "choose a package Cargo.toml, not a virtual workspace",
        hint: "Pass `--manifest-path path/to/crate/Cargo.toml` for a concrete workspace member \
               instead of the virtual workspace root.",
    },
    DetailRule {
        needle: "does not have feature",
        hint: "Check `[features]` in `Cargo.toml` and adjust `--features`.",
    },
    DetailRule {
        needle: "Cargo shortcut",
        hint: "The `--manifest-path` Cargo shortcut supports single library or binary crates \
               without active normal/build dependencies, build scripts, or proc-macros (use \
               `--features`, `--all-features`, or `--no-default-features` to configure package \
               features). For other crates, pass `--request <file>` (run `cargo anneal skill \
               --example` for a template) or `verify rustc`.",
    },
    DetailRule {
        needle: "cargo metadata probe directory",
        hint: "The `--manifest-path` Cargo shortcut executes `cargo metadata` from a temporary \
               directory under `$TMPDIR` and refuses `rust-toolchain` or `rust-toolchain.toml` \
               files along its resolved ancestry. Unset `TMPDIR` or point it at a clean \
               directory, or pass `--request <file>` / `verify rustc`.",
    },
    DetailRule {
        needle: "explicit configured compilation",
        hint: "The `--manifest-path` Cargo shortcut rejects build scripts, proc-macros, \
               and `.cargo/config` files that set anything beyond the \
               `[alias]`, `[term]`, `[doc]`, `[cargo-new]`, and `[future-incompat-report]` \
               tables (plus `[net]`, `[registries]`, `[registry]`, and `[source]` strictly above \
               the workspace root or in `$CARGO_HOME`). Use `cargo anneal verify --request <file>` \
               (see `cargo anneal skill --example`) or `verify rustc`.",
    },
];

const UNSUPPORTED_CAPTURE_RULES: &[DetailRule] = &[
    DetailRule {
        needle: "body mixes reference and raw-pointer locals",
        hint: "Profile v2 does not model Rust's pointer aliasing rules, so a function may use \
               references or raw pointers but not both, and cannot convert between them. Split \
               the reference-based and raw-pointer-based logic into separate functions or narrow \
               scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "outside the Profile v2 type fragment",
        hint: "Profile v2 admits single-level references and raw pointers to scalars and integer \
               slices (`&T`, `&mut T`, `&[T]`, `*const T`, `*mut T`); nested references, \
               pointers to references, and references to other types are not supported yet. \
               Refactor the selected function or narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported type: ",
        hint: "Capture refuses this Rust type. Profile v2 admits scalars, fieldless local enums, \
               tuples, `RangeTo<usize>`/`RangeFrom<usize>`, shared `&str`, and single-level \
               references and raw pointers to scalars and integer slices; references or pointers \
               to other types (such as `&mut str`, `*const str`, or structs) are not supported \
               yet. Refactor the selected function or narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "cleanup unwinds on",
        hint: "A panicking `Assert` or call has a cleanup (drop) path on unwind, which Profile v2 \
               does not support yet. Keep values with drop glue out of verified functions or \
               narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported core call",
        hint: "Profile v2 captures returning calls only to `<[T]>::len`, `<[T]>::get_unchecked` \
               with `..n` or `n..`, `<*const T>::add`, `<*mut T>::add`, and \
               `usize::unchecked_sub` from the sysroot `core`. Inline other helpers or verify a \
               leaf function via `--select <fn>`.",
    },
    DetailRule {
        needle: "CallSource::Use call terminators are unsupported",
        hint: "Capture rejects `CallSource::Use` clones under every MIR profile, because later \
               codegen may rewrite them to bitwise copies; avoid implicit use-clones or narrow \
               scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "external call to non-core def",
        hint: "Profile v2 does not yet capture calls to functions outside the sysroot `core` \
               call table (including other functions in this crate). Inline helper arithmetic or \
               verify a leaf function via `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported terminator: Drop",
        hint: "Neither MIR Profile v1 nor v2 supports `Drop` terminators yet. Keep values with \
               drop glue out of verified functions or narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "place projections are unsupported",
        hint: "A call's return value must be written to an unprojected local; storing it \
               directly into a field, through a dereference, or into a tuple element is not \
               supported yet. Bind the result to a temporary local before assigning it, or narrow \
               scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "enum payloads are unsupported",
        hint: "MIR Profiles v1 and v2 support only non-generic fieldless local enums; avoid \
               payloads or narrow scope with `--select <fn>`.",
    },
];

const AUDIT_POLICY_RULES: &[DetailRule] = &[
    DetailRule {
        needle: "cannot import ",
        hint: "Specification modules (`Spec`) must stay pure and may only import `Trusted.*` or \
               other specification/model modules; move proof automation imports such as \
               `Anneal.MirWp` into `Proof.lean`.",
    },
    DetailRule {
        needle: "Lean.Parser.Term.sorry",
        hint: "`sorry` is strictly forbidden in specification modules even when \
               `--allow-sorry-in-proof` is passed. Remove `sorry` from `Spec.lean`; place temporary \
               proof holes only in `Proof.lean`.",
    },
    DetailRule {
        needle: "Lean.Parser.Tactic.tacticSorry",
        hint: "`sorry` is strictly forbidden in specification modules even when \
               `--allow-sorry-in-proof` is passed. Remove `sorry` from `Spec.lean`; place temporary \
               proof holes only in `Proof.lean`.",
    },
    DetailRule {
        needle: "policy:unapproved axiom sorryAx",
        hint: "Your proof contains `sorry`. Complete the proof in `Proof.lean`, or pass \
               `--allow-sorry-in-proof` during local prototyping (taints the verification receipt).",
    },
    DetailRule {
        needle: "policy:target theorem type differs from Expected",
        hint: "Your proof theorem (`Proof.verify` by default) does not match `Expected.claim` (or \
               `--spec-decl`). Run `cargo anneal init` or `cargo anneal skill --example` to check \
               the required theorem signature.",
    },
];

fn match_rule(rules: &[DetailRule], text: &str) -> Option<&'static str> {
    rules.iter().find(|rule| text.contains(rule.needle)).map(|rule| rule.hint)
}

/// Produce a concise, human-actionable hint for a verification failure receipt,
/// returning `None` when the raw `detail` is already self-explanatory.
pub fn hint_for_failure(status: &str, phase: &str, detail: &str) -> Option<String> {
    match phase {
        "capture-tool" | "toolchain" => Some(hint_for_capture_tool(phase, detail)),
        "cargo" => match_rule(CARGO_RULES, detail).map(str::to_owned),
        "proof" => hint_for_proof_phase(detail),
        "capture" => hint_for_capture(status, detail),
        "audit" => hint_for_audit(detail),
        "retention" if detail.contains("already exists") || detail.contains("File exists") => Some(
            "Pass a new non-existent directory path to `--artifacts <dir>`, or add \
                 `--overwrite-artifacts` to replace an artifact directory that `verify` wrote \
                 earlier; other existing paths are never overwritten."
                .into(),
        ),
        _ => None,
    }
}

fn hint_for_capture_tool(phase: &str, detail: &str) -> String {
    let same_toolchain = same_toolchain_requirement();
    if detail.contains("explicit --capture, --sysroot, and --lean") {
        return format!(
            "Rebuild with the default `setup` feature for bundled discovery, or pass all three \
             tool paths: `--capture`, `--sysroot`, and `--lean`. {same_toolchain}"
        );
    }
    #[cfg(feature = "setup")]
    {
        if phase == "toolchain" {
            return format!(
                "Run `cargo anneal setup` to install the matching Anneal toolchain bundle, or \
                 pass explicit `--capture`, `--sysroot`, and `--lean` paths. {same_toolchain}"
            );
        }
        format!(
            "No usable `anneal-rustc-capture` binary or installed Anneal toolchain bundle was \
             found. Check `--capture` if passed explicitly, or run `cargo anneal setup \
             --local-archive <archive>` (or pass `--capture`, `--sysroot`, and `--lean`). \
             {same_toolchain}"
        )
    }
    #[cfg(not(feature = "setup"))]
    {
        let _ = phase;
        format!(
            "Pass matching explicit `--capture`, `--sysroot`, and `--lean` paths for the pinned \
             Anneal toolchain (or rebuild with the default `setup` feature). {same_toolchain}"
        )
    }
}

// Mirrors the private `verify.rs` pins that `parse_capture_receipt`
// enforces; `hint_pins_match_verify_pins` fails if they drift.
const EXPECTED_CAPTURE_SCHEMA_VERSION: u32 = 5;
const EXPECTED_RUSTC_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";

fn same_toolchain_requirement() -> String {
    format!(
        "An explicit `--capture` and `--sysroot` must come from the same Anneal toolchain: \
         capture schema {EXPECTED_CAPTURE_SCHEMA_VERSION} built from `rust-lang/rust` commit \
         `{EXPECTED_RUSTC_COMMIT}`."
    )
}

fn hint_for_proof_phase(detail: &str) -> Option<String> {
    if detail.contains("cannot inspect proof directory") {
        return Some(
            "Create starter Lean files with `cargo anneal init`, or pass `--proof-dir <DIR>` \
             pointing to an existing directory containing `Spec.lean` and `Proof.lean`."
                .into(),
        );
    }
    if detail.contains("specification and theorem must have their declared source roles") {
        return Some(
            "Expected both a specification module (`Spec.lean`) and a proof module \
             (`Proof.lean`). Run `cargo anneal init` to scaffold starter files or see `cargo \
             anneal skill --example`."
                .into(),
        );
    }
    None
}

fn hint_for_capture(status: &str, detail: &str) -> Option<String> {
    if detail == "unexpected capture schema or compiler" {
        return Some(format!(
            "The capture receipt's schema or compiler commit does not match this `cargo anneal`. \
             {} Reinstall a matching bundle with `cargo anneal setup`.",
            same_toolchain_requirement()
        ));
    }
    if status == "compiler_failed" {
        return Some(
            "`rustc` failed to compile the crate; fix the Rust compiler diagnostics printed on \
             stderr and re-run `cargo anneal verify`."
                .into(),
        );
    }
    let envelope: Value = serde_json::from_str(detail).ok()?;
    if let Some(items) = envelope["unsupported"].as_array()
        && !items.is_empty()
    {
        let mut summaries = Vec::new();
        let mut guidance: Option<&str> = None;
        for item in items {
            let path = item["path"].as_str().unwrap_or("<item>");
            let reason = item["reason"].as_str().unwrap_or("unsupported construct");
            if guidance.is_none() {
                guidance = match_rule(UNSUPPORTED_CAPTURE_RULES, reason);
            }
            if summaries.len() < 2 {
                summaries.push(format!("`{path}`: {reason}"));
            }
        }
        let extra =
            if items.len() > 2 { format!(" (+{} more)", items.len() - 2) } else { String::new() };
        let fallback = "Narrow verification scope to a supported function with `--select <fn>`, \
                        or see `cargo anneal skill` for the MIR Profile v1 (scalar) and Profile \
                        v2 (references, raw pointers, and integer slices) bounds.";
        let advice = guidance.unwrap_or(fallback);
        return Some(format!("Unsupported MIR in {}{extra}. {advice}", summaries.join("; ")));
    }
    if let Some(diags) = envelope["diagnostics"].as_array() {
        let msgs: Vec<&str> = diags.iter().filter_map(Value::as_str).collect();
        if !msgs.is_empty() {
            return Some(format!(
                "Capture rejected compilation: {}. See `cargo anneal skill` for the MIR Profile \
                 v1 (scalar) and Profile v2 (references, raw pointers, and integer slices) \
                 requirements.",
                msgs.join("; ")
            ));
        }
    }
    None
}

fn is_spec_module(target: &str) -> bool {
    target == "Spec" || target.starts_with("Spec.")
}

fn hint_for_audit(detail: &str) -> Option<String> {
    if let Some(hint) = match_rule(AUDIT_POLICY_RULES, detail) {
        return Some(hint.to_owned());
    }
    if let Some((module, target)) = parse_unsupported_import(detail) {
        if module == "Init" {
            if is_spec_module(target) {
                return Some(format!(
                    "Lean specification module `{target}` must begin with `prelude` as its \
                     first non-comment line (without `prelude`, Lean implicitly imports `Init`) \
                     and import only pinned `Trusted.*` or supported checked math modules (such \
                     as `Trusted.MirSemantics`). For local unpinned sysroot imports, pass \
                     `--allow-unpinned-lean --lean <path>`."
                ));
            }
            return Some(format!(
                "Lean module `{target}` must begin with `prelude` as its first non-comment line \
                 (without `prelude`, Lean implicitly imports `Init`) and import only pinned \
                 modules such as `Trusted.MirSemantics` or `Anneal.MirWp`. For local unpinned \
                 sysroot imports, pass `--allow-unpinned-lean --lean <path>`."
            ));
        }
        if is_spec_module(target) {
            return Some(format!(
                "`{module}` is not in the pinned import lock for specification module `{target}`. \
                 Specifications must begin with `prelude` and may only import pinned `Trusted.*` \
                 or supported checked math modules (never `Anneal.*`), or pass \
                 `--allow-unpinned-lean --lean <path>` for local sysroot imports."
            ));
        }
        return Some(format!(
            "`{module}` is not in the pinned import lock for `{target}`. Import only pinned \
             `Trusted.*` / `Anneal.*` / supported checked math modules (and begin the file with \
             `prelude`), or pass `--allow-unpinned-lean --lean <path>` for local experimentation."
        ));
    }
    if let Some(kind) = detail.strip_prefix("policy:unsupported declaration kind ") {
        let cmd = kind
            .strip_suffix(" in specification")
            .unwrap_or(kind)
            .rsplit('.')
            .next()
            .unwrap_or(kind);
        return Some(format!(
            "Specification modules permit pure definitions and theorems (`def`, `abbrev`, \
             `theorem`, `structure`, `inductive`, `class inductive`, `instance`); `{cmd}` is \
             disallowed in `Spec.lean`. Move examples or proof helpers into `Proof.lean`."
        ));
    }
    if detail.contains("in specification") && detail.starts_with("policy:") {
        return Some(
            "Specification modules are validated under a strict pure syntactic subset before \
             elaboration. Move tactical proofs and Lean commands out of `Spec.lean` into \
             `Proof.lean`."
                .into(),
        );
    }
    if detail.contains("Lean exited ") {
        return summarize_lean_errors(detail);
    }
    if (detail.contains("exceeds size cap")
        || detail.contains("grew past size cap")
        || detail.contains("regular file exceeds ")
        || detail.contains("regular file exceeded "))
        && detail.contains("result.json")
    {
        let max_cap = crate::sandbox::MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES;
        let at_ceiling = detail.contains(&format!(" {max_cap} bytes)"))
            || detail.contains(&format!("({max_cap} bytes)"))
            || detail.contains(&format!(" {max_cap}-byte limit"));
        if !at_ceiling {
            return Some(
                "Inspector output `result.json` exceeded the output size cap (default 64 MiB). \
                 Pass `--max-inspector-output-bytes <BYTES>` (up to 1 GiB) to raise the limit for \
                 large crate exports."
                    .into(),
            );
        }
    }
    None
}

fn parse_unsupported_import(detail: &str) -> Option<(&str, &str)> {
    let rest = detail.strip_prefix("unsupported import ")?;
    let (module, after) = rest.split_once(" in ")?;
    let target = after.split(';').next()?.trim();
    if module.is_empty() || target.is_empty() {
        return None;
    }
    Some((module, target))
}

fn display_lean_filename(raw: &str) -> &str {
    for prefix in ["/work/in/", "/work/ro/", "/work/generated/"] {
        if let Some(stripped) = raw.strip_prefix(prefix) {
            return stripped;
        }
    }
    Path::new(raw).file_name().and_then(|n| n.to_str()).unwrap_or(raw)
}

fn summarize_lean_errors(detail: &str) -> Option<String> {
    let mut errors = Vec::new();
    let mut full_data = String::new();
    for line in detail.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        let Ok(msg) = serde_json::from_str::<Value>(trimmed) else {
            continue;
        };
        if msg["severity"].as_str() != Some("error") {
            continue;
        }
        let file = msg["fileName"].as_str().map(display_lean_filename).unwrap_or("Proof.lean");
        let line_no = msg["pos"]["line"].as_u64();
        let col_no = msg["pos"]["column"].as_u64();
        let data = msg["data"].as_str().unwrap_or("Lean error");
        if full_data.is_empty() {
            full_data = data.to_owned();
        }
        let compact: String = data.split_whitespace().collect::<Vec<_>>().join(" ");
        let truncated: String = compact.chars().take(140).collect();
        let ellipsis = if compact.chars().count() > 140 { "..." } else { "" };
        let loc = match (line_no, col_no) {
            (Some(l), Some(c)) => format!("{file}:{l}:{c}"),
            _ => file.to_owned(),
        };
        errors.push(format!("{loc}: {truncated}{ellipsis}"));
    }
    let first = errors.first()?;
    let extra = if errors.len() > 1 {
        format!(" (+{} more Lean diagnostic(s))", errors.len() - 1)
    } else {
        String::new()
    };
    let tail = if full_data.contains("Not a definitional equality")
        || full_data.contains("Type mismatch")
    {
        " Check that the Rust body satisfies `Spec` and that indices/types in `Proof.lean` match \
         `Captured.program`."
    } else if full_data.contains("don't know how to synthesize placeholder")
        || full_data.contains("unsolved goals")
    {
        " Complete the remaining proof goal(s) in `Proof.lean` (or run `cargo anneal skill \
         --example` for a worked `Proof.lean` template)."
    } else {
        ""
    };
    Some(format!("{first}{extra}.{tail}"))
}

#[cfg(test)]
mod tests {
    use super::hint_for_failure;

    #[test]
    fn maps_capture_reference_call_and_cleanup_diagnostics() {
        let ref_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 3, "path": "take_ref", "reason": "local _1 of type Ref { mutability: Not, pointee: Ref { mutability: Not, pointee: Int(U64) } } is outside the Profile v2 type fragment"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &ref_detail).unwrap();
        assert!(hint.contains("`take_ref`"), "{hint}");
        assert!(hint.contains("nested references"), "{hint}");

        let mixed_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 5, "path": "mixed", "reason": "body mixes reference and raw-pointer locals, which Profile v2 refuses because it does not model Rust's pointer aliasing rules"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &mixed_detail).unwrap();
        assert!(hint.contains("`mixed`"), "{hint}");
        assert!(hint.contains("aliasing"), "{hint}");
        assert!(!hint.contains("from_raw_parts") && !hint.contains("as_ptr"), "{hint}");

        let pointee_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 6, "path": "take_str", "reason": "unsupported type: str"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &pointee_detail).unwrap();
        assert!(hint.contains("`take_str`"), "{hint}");
        assert!(hint.contains("references or pointers to other types"), "{hint}");

        let call_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 4, "path": "iter", "reason": "bb0: unsupported core call `core::slice::<impl [T]>::iter`"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &call_detail).unwrap();
        assert!(hint.contains("`<[T]>::len`"), "{hint}");
        assert!(hint.contains("`usize::unchecked_sub`"), "{hint}");

        let cleanup_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 7, "path": "drops", "reason": "bb1: cleanup unwinds on call are unsupported"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &cleanup_detail).unwrap();
        assert!(hint.contains("drop glue"), "{hint}");
    }

    #[test]
    fn maps_compiler_failure_and_cargo_shortcuts() {
        let hint = hint_for_failure("compiler_failed", "capture", "{}").unwrap();
        assert!(hint.contains("stderr"), "{hint}");

        let shortcut_hint = hint_for_failure(
            "unsupported",
            "cargo",
            "Cargo shortcut requires a dependency-free crate; pass `--request` for crates with dependencies",
        )
        .unwrap();
        assert!(shortcut_hint.contains("--features"), "{shortcut_hint}");
        assert!(shortcut_hint.contains("--request"), "{shortcut_hint}");

        let compiled_hint = hint_for_failure(
            "unsupported",
            "cargo",
            "build scripts and procedural macros need an explicit configured compilation",
        )
        .unwrap();
        assert!(compiled_hint.contains("build scripts"), "{compiled_hint}");
        assert!(compiled_hint.contains("--request"), "{compiled_hint}");
        assert!(compiled_hint.contains("`[alias]`"), "{compiled_hint}");

        let probe_cwd_hint = hint_for_failure(
            "unsupported",
            "cargo",
            "compiler overrides need an explicit configured compilation \
             (rust-toolchain.toml: present in cargo metadata probe directory ancestor /tmp)",
        )
        .unwrap();
        assert!(probe_cwd_hint.contains("$TMPDIR"), "{probe_cwd_hint}");
        assert!(probe_cwd_hint.contains("--request"), "{probe_cwd_hint}");
    }

    #[test]
    fn maps_unpinned_init_and_spec_preflight_errors() {
        let init_spec_hint = hint_for_failure(
            "proof_failed",
            "audit",
            "unsupported import Init in Spec; use explicit prelude and supported checked math imports",
        )
        .unwrap();
        assert!(init_spec_hint.contains("prelude"), "{init_spec_hint}");
        assert!(init_spec_hint.contains("Trusted.MirSemantics"), "{init_spec_hint}");
        assert!(!init_spec_hint.contains("Anneal.MirWp"), "{init_spec_hint}");
        assert!(init_spec_hint.contains("--allow-unpinned-lean"), "{init_spec_hint}");

        let init_proof_hint = hint_for_failure(
            "proof_failed",
            "audit",
            "unsupported import Init in Proof; use explicit prelude and supported checked math imports",
        )
        .unwrap();
        assert!(init_proof_hint.contains("Anneal.MirWp"), "{init_proof_hint}");

        let spec_sub_hint = hint_for_failure(
            "proof_failed",
            "audit",
            "unsupported import Custom.Mod in Spec.Sub; not in lock",
        )
        .unwrap();
        assert!(spec_sub_hint.contains("never `Anneal.*`"), "{spec_sub_hint}");

        let example_hint = hint_for_failure(
            "proof_failed",
            "audit",
            "policy:unsupported declaration kind Lean.Parser.Command.example in specification",
        )
        .unwrap();
        assert!(example_hint.contains("`example`"), "{example_hint}");
        assert!(example_hint.contains("`class inductive`"), "{example_hint}");
        assert!(example_hint.contains("Proof.lean"), "{example_hint}");

        let opaque_hint = hint_for_failure(
            "proof_failed",
            "audit",
            "policy:unsupported declaration kind Lean.Parser.Command.opaque in specification",
        )
        .unwrap();
        assert!(opaque_hint.contains("`opaque` is disallowed"), "{opaque_hint}");
        assert!(!opaque_hint.contains("`opaque`,"), "{opaque_hint}");

        let sorry_hint = hint_for_failure(
            "proof_failed",
            "audit",
            "policy:unsupported tactic Lean.Parser.Tactic.tacticSorry in specification",
        )
        .unwrap();
        assert!(sorry_hint.contains("`sorry`"), "{sorry_hint}");
    }

    #[test]
    fn summarizes_lean_json_errors() {
        let detail = "Lean exited Some(1): stdout:\n\
            {\"severity\":\"error\",\"fileName\":\"/work/in/Proof.lean\",\"pos\":{\"line\":9,\"column\":8},\
            \"data\":\"Not a definitional equality: LHS != RHS\"}\nstderr:\n";
        let hint = hint_for_failure("proof_failed", "audit", detail).unwrap();
        assert!(hint.contains("Proof.lean:9:8"), "{hint}");
        assert!(hint.contains("Not a definitional equality"), "{hint}");
        assert!(hint.contains("Captured.program"), "{hint}");
    }

    #[test]
    fn maps_capture_tool_setup_and_no_setup_hints() {
        let missing_setup = hint_for_failure(
            "tool_failed",
            "capture-tool",
            "missing capture; explicit --capture, --sysroot, and --lean tool paths are required \
             when built without the `setup` feature",
        )
        .unwrap();
        assert!(missing_setup.contains("default `setup` feature"), "{missing_setup}");
        assert!(missing_setup.contains("--capture"), "{missing_setup}");

        let missing_bundle = hint_for_failure(
            "tool_failed",
            "capture-tool",
            "cannot inspect /tmp/x/anneal-rustc-capture: No such file or directory (os error 2)",
        )
        .unwrap();
        #[cfg(feature = "setup")]
        assert!(missing_bundle.contains("cargo anneal setup --local-archive"), "{missing_bundle}");
        #[cfg(not(feature = "setup"))]
        assert!(
            missing_bundle.contains("default `setup` feature")
                && missing_bundle.contains("--capture"),
            "{missing_bundle}"
        );
        for hint in [&missing_setup, &missing_bundle] {
            assert!(hint.contains(super::EXPECTED_RUSTC_COMMIT), "{hint}");
            assert!(hint.contains("same Anneal toolchain"), "{hint}");
        }
    }

    #[test]
    fn maps_capture_schema_mismatch_to_pinned_toolchain() {
        let hint =
            hint_for_failure("tool_failed", "capture", "unexpected capture schema or compiler")
                .unwrap();
        assert!(hint.contains("`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`"), "{hint}");
        assert!(hint.contains("capture schema 5"), "{hint}");
        assert!(hint.contains("`--capture` and `--sysroot`"), "{hint}");
        assert!(hint.contains("cargo anneal setup"), "{hint}");
    }

    #[test]
    fn hint_pins_match_verify_pins() {
        let verify = include_str!("verify.rs");
        let commit =
            format!("const PINNED_RUSTC_COMMIT: &str = \"{}\";", super::EXPECTED_RUSTC_COMMIT);
        let schema = format!(
            "const PINNED_CAPTURE_SCHEMA_VERSION: u32 = {};",
            super::EXPECTED_CAPTURE_SCHEMA_VERSION
        );
        assert!(verify.contains(&commit), "verify.rs no longer pins {commit}");
        assert!(verify.contains(&schema), "verify.rs no longer pins {schema}");
    }

    #[test]
    fn capture_fallbacks_describe_both_mir_profiles() {
        let unknown = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 1, "path": "f", "reason": "something new"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &unknown).unwrap();
        assert!(hint.contains("Profile v1 (scalar)"), "{hint}");
        assert!(hint.contains("Profile v2 (references, raw pointers"), "{hint}");

        let rejected = serde_json::json!({"diagnostics": ["no crate root"]}).to_string();
        let hint = hint_for_failure("unsupported", "capture", &rejected).unwrap();
        assert!(hint.starts_with("Capture rejected compilation: no crate root."), "{hint}");
        assert!(hint.contains("Profile v1 (scalar)"), "{hint}");
        assert!(hint.contains("Profile v2 (references, raw pointers"), "{hint}");

        for (reason, needle) in [
            ("unsupported terminator: Drop { .. }", "Neither MIR Profile v1 nor v2"),
            ("place projections are unsupported: (*_1)", "temporary local"),
            ("enum payloads are unsupported: E", "Profiles v1 and v2"),
            ("CallSource::Use call terminators are unsupported: x", "every MIR profile"),
        ] {
            let detail = serde_json::json!({
                "unsupported": [{"def_id": 1, "path": "f", "reason": reason}],
            })
            .to_string();
            let hint = hint_for_failure("unsupported", "capture", &detail).unwrap();
            assert!(hint.contains(needle), "{reason}: {hint}");
        }
    }

    #[test]
    fn maps_inspector_output_size_cap_hints_from_real_errors() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        std::fs::create_dir_all(&out).unwrap();
        let result_path = out.join("result.json");
        std::fs::write(&result_path, b"0123456789abcdef").unwrap();

        let door1_err = crate::sandbox::validate_inspector_result_with_cap(&out, "result.json", 10)
            .unwrap_err()
            .to_string();
        let door1_hint = hint_for_failure("tool_failed", "audit", &door1_err).unwrap();
        assert!(door1_hint.contains("--max-inspector-output-bytes"), "{door1_hint}");

        let direct_err =
            crate::sys_util::SafeFs::read_regular_string_capped(&result_path, 10, "audit")
                .unwrap_err()
                .to_string();
        let direct_hint = hint_for_failure("tool_failed", "audit", &direct_err).unwrap();
        assert!(direct_hint.contains("--max-inspector-output-bytes"), "{direct_hint}");

        let grew_hint = hint_for_failure(
            "tool_failed",
            "audit",
            "regular file exceeded 10-byte limit: /work/out/result.json",
        )
        .unwrap();
        assert!(grew_hint.contains("--max-inspector-output-bytes"), "{grew_hint}");

        let door1_grew_hint = hint_for_failure(
            "tool_failed",
            "audit",
            "sandbox output /work/out/result.json grew past size cap (10 bytes)",
        )
        .unwrap();
        assert!(door1_grew_hint.contains("--max-inspector-output-bytes"), "{door1_grew_hint}");

        // When already at the 1 GiB ceiling, do not suggest raising the flag.
        let max_cap = crate::sandbox::MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES;
        for at_max in [
            format!(
                "sandbox output /work/out/result.json exceeds size cap ({} > {max_cap} bytes)",
                max_cap + 1
            ),
            format!("sandbox output /work/out/result.json grew past size cap ({max_cap} bytes)"),
            format!("regular file exceeds {max_cap}-byte limit: /work/out/result.json"),
            format!("regular file exceeded {max_cap}-byte limit: /work/out/result.json"),
        ] {
            assert_eq!(
                hint_for_failure("tool_failed", "audit", &at_max),
                None,
                "should suppress hint at ceiling: {at_max}"
            );
        }
    }
}
