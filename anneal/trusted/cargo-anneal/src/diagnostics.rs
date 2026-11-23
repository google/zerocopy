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
        needle: "Cargo shortcut",
        hint: "The `--manifest-path` Cargo shortcut supports dependency-free, feature-free library \
               crates without build scripts or proc-macros. For other crates, pass `--request \
               <file>` (run `cargo anneal skill --example` for a template) or `verify rustc`.",
    },
    DetailRule {
        needle: "explicit configured compilation",
        hint: "The `--manifest-path` Cargo shortcut rejects features, build scripts, proc-macros, \
               and `.cargo`/toolchain overrides. Use `cargo anneal verify --request <file>` (see \
               `cargo anneal skill --example`) or `verify rustc`.",
    },
];

const UNSUPPORTED_CAPTURE_RULES: &[DetailRule] = &[
    DetailRule {
        needle: "unsupported type: &",
        hint: "Profile v1 covers pointer-free scalar, bool, char, unit, `Ordering`, and fieldless \
               enum values; references are not supported yet. Refactor the selected function to \
               take scalar values by value or narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported type: *",
        hint: "Profile v1 covers pointer-free scalar values only; raw pointers are not supported \
               yet. Test a pointer-free helper or narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported terminator: Assert",
        hint: "`rustc` emitted a runtime panic/overflow assertion (`Assert` terminator), which \
               Profile v1 does not support yet. Prefer wrapping/checked/saturating operations or \
               explicit branching instead of panicking arithmetic or `/` overflow checks.",
    },
    DetailRule {
        needle: "CallSource::Use call terminators are unsupported",
        hint: "Profile v1 rejects `CallSource::Use` clones; avoid implicit use-clones or narrow \
               scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported terminator: Call",
        hint: "Profile v1 does not yet capture function call terminators inside a verified body. \
               Inline helper arithmetic or verify a leaf function via `--select <fn>`.",
    },
    DetailRule {
        needle: "unsupported terminator: Drop",
        hint: "Profile v1 does not support `Drop` terminators yet. Keep verified functions limited \
               to `Copy` scalar types or narrow scope with `--select <fn>`.",
    },
    DetailRule {
        needle: "place projections are unsupported",
        hint: "Profile v1 only admits unprojected scalar locals and `(T, bool)` overflow pairs. \
               Avoid struct/tuple field projections in selected items or narrow scope with \
               `--select <fn>`.",
    },
    DetailRule {
        needle: "enum payloads are unsupported",
        hint: "Profile v1 supports non-generic fieldless local enums only; avoid payloads or \
               narrow scope with `--select <fn>`.",
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
        "capture-tool" => Some(hint_for_capture_tool(detail)),
        "cargo" => match_rule(CARGO_RULES, detail).map(str::to_owned),
        "proof" => hint_for_proof_phase(detail),
        "capture" => hint_for_capture(status, detail),
        "audit" => hint_for_audit(detail),
        _ => None,
    }
}

fn hint_for_capture_tool(detail: &str) -> String {
    if detail.contains("explicit --capture, --sysroot, and --lean") {
        return "Rebuild with the default `setup` feature for bundled discovery, or pass all \
                three tool paths: `--capture`, `--sysroot`, and `--lean`."
            .into();
    }
    "No usable `anneal-rustc-capture` binary or installed Anneal toolchain bundle was found. \
     Check `--capture` if passed explicitly, or run `cargo anneal setup --local-archive <archive>` \
     (or pass `--capture`, `--sysroot`, and `--lean`)."
        .into()
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
        return Some(
            "Ensure `anneal-rustc-capture` and `--sysroot` belong to the same pinned Anneal \
             toolchain release (`cargo anneal setup`)."
                .into(),
        );
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
        let fallback = "Narrow verification scope to a supported scalar function with `--select \
                        <fn>`, or see `cargo anneal skill` for Profile v1 bounds.";
        let advice = guidance.unwrap_or(fallback);
        return Some(format!("Unsupported MIR in {}{extra}. {advice}", summaries.join("; ")));
    }
    if let Some(diags) = envelope["diagnostics"].as_array() {
        let msgs: Vec<&str> = diags.iter().filter_map(Value::as_str).collect();
        if !msgs.is_empty() {
            return Some(format!(
                "Capture rejected compilation: {}. See `cargo anneal skill --example` for \
                 Profile v1 requirements.",
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
    fn maps_capture_reference_and_assert_diagnostics() {
        let ref_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 3, "path": "take_ref", "reason": "unsupported type: &'{erased} u64"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &ref_detail).unwrap();
        assert!(hint.contains("`take_ref`"), "{hint}");
        assert!(hint.contains("references are not supported"), "{hint}");

        let assert_detail = serde_json::json!({
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [{"def_id": 4, "path": "div", "reason": "unsupported terminator: Assert { cond: true }"}],
        })
        .to_string();
        let hint = hint_for_failure("unsupported", "capture", &assert_detail).unwrap();
        assert!(hint.contains("Assert"), "{hint}");
        assert!(hint.contains("wrapping/checked/saturating"), "{hint}");
    }

    #[test]
    fn maps_compiler_failure_and_cargo_shortcuts() {
        let hint = hint_for_failure("compiler_failed", "capture", "{}").unwrap();
        assert!(hint.contains("stderr"), "{hint}");

        let cargo_hint = hint_for_failure(
            "unsupported",
            "cargo",
            "Cargo features require an explicit configured compilation request",
        )
        .unwrap();
        assert!(cargo_hint.contains("--request"), "{cargo_hint}");
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
        assert!(missing_bundle.contains("cargo anneal setup --local-archive"), "{missing_bundle}");
    }
}
