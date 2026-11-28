// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The synthetic `v4.35.0` sysroot harness: NDJSON fixture builders, the
//! stub installation, and the target request run through it.

use std::os::unix::fs::PermissionsExt;

use super::*;

#[derive(Clone, Debug)]
pub(super) struct SyntheticHarnessConfig {
    pub(super) omit_init_primitive: Option<&'static str>,
    pub(super) tamper_expected_claim_in_expected: bool,
    pub(super) tamper_expected_claim_in_proof: bool,
    pub(super) inject_custom_axiom_in_proof: Option<&'static str>,
    pub(super) nanoda_behavior: StubBehavior,
    pub(super) con_ron_behavior: StubBehavior,
}

impl Default for SyntheticHarnessConfig {
    fn default() -> Self {
        Self {
            omit_init_primitive: None,
            tamper_expected_claim_in_expected: false,
            tamper_expected_claim_in_proof: false,
            inject_custom_axiom_in_proof: None,
            nanoda_behavior: StubBehavior::Accept,
            con_ron_behavior: StubBehavior::Accept,
        }
    }
}

pub(super) struct SyntheticComparatorHarness {
    pub(super) tmp: TempDir,
    lean_bin: PathBuf,
    pub(super) nanoda_bin: PathBuf,
    pub(super) con_ron_bin: PathBuf,
    pub(super) fixtures_dir: PathBuf,
    invocation_log: PathBuf,
    pub(super) request: TargetAuditRequest,
}

fn build_init_ndjson(omit_primitive: Option<&str>) -> String {
    let mut init_lines = vec![
        SYNTHETIC_META.to_owned(),
        r#"{"ie":0,"sort":0}"#.to_owned(),
        r#"{"il":1,"succ":0}"#.to_owned(),
        r#"{"ie":1,"sort":1}"#.to_owned(),
    ];
    let mut next_in = 1u64;
    let mut name_ids = std::collections::HashMap::<String, u64>::new();
    let mut intern = |dotted: &str, lines: &mut Vec<String>| -> u64 {
        let mut cur = 0u64;
        let mut pref = String::new();
        for seg in dotted.split('.') {
            if !pref.is_empty() {
                pref.push('.');
            }
            pref.push_str(seg);
            if let Some(&id) = name_ids.get(&pref) {
                cur = id;
            } else {
                let id = next_in;
                next_in += 1;
                lines.push(format!(r#"{{"in":{id},"str":{{"pre":{cur},"str":"{seg}"}}}}"#));
                name_ids.insert(pref.clone(), id);
                cur = id;
            }
        }
        cur
    };
    for prim in PINNED_INIT_PRIMITIVES {
        if omit_primitive == Some(prim) {
            continue;
        }
        let nid = intern(prim, &mut init_lines);
        let line = match prim {
            "Quot" => {
                format!(r#"{{"quot":{{"kind":"type","levelParams":[],"name":{nid},"type":1}}}}"#)
            }
            "Quot.mk" => {
                format!(r#"{{"quot":{{"kind":"ctor","levelParams":[],"name":{nid},"type":1}}}}"#)
            }
            "Quot.lift" => {
                format!(r#"{{"quot":{{"kind":"lift","levelParams":[],"name":{nid},"type":1}}}}"#)
            }
            "Quot.ind" => {
                format!(r#"{{"quot":{{"kind":"ind","levelParams":[],"name":{nid},"type":1}}}}"#)
            }
            _ => format!(
                r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#
            ),
        };
        init_lines.push(line);
    }
    for ax in STANDARD_PERMITTED_AXIOMS {
        let nid = intern(ax, &mut init_lines);
        init_lines.push(format!(
            r#"{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{nid},"type":0}}}}"#
        ));
    }
    for decl in PINNED_SYSTEM_PLATFORM_DECLS {
        let nid = intern(decl, &mut init_lines);
        if decl == "System.Platform.getNumBits" {
            init_lines.push(format!(
                r#"{{"opaque":{{"all":[{nid}],"isUnsafe":false,"levelParams":[],"name":{nid},"type":1,"value":0}}}}"#
            ));
        } else {
            init_lines.push(format!(
                r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#
            ));
        }
    }
    init_lines.join("\n") + "\n"
}

fn build_expected_ndjson(tamper_claim: bool) -> String {
    let claim_value_expr = if tamper_claim { 10 } else { 17 };
    [
        SYNTHETIC_META.to_owned(),
        r#"{"in":10,"str":{"pre":0,"str":"Trusted"}}"#.to_owned(),
        r#"{"in":11,"str":{"pre":10,"str":"MirSemantics"}}"#.to_owned(),
        r#"{"in":12,"str":{"pre":11,"str":"UnitTheorem"}}"#.to_owned(),
        r#"{"in":13,"str":{"pre":11,"str":"Crate"}}"#.to_owned(),
        r#"{"in":14,"str":{"pre":13,"str":"mk"}}"#.to_owned(),
        r#"{"in":15,"str":{"pre":0,"str":"Captured"}}"#.to_owned(),
        r#"{"in":16,"str":{"pre":15,"str":"program"}}"#.to_owned(),
        r#"{"in":17,"str":{"pre":0,"str":"Spec"}}"#.to_owned(),
        r#"{"in":18,"str":{"pre":17,"str":"specs"}}"#.to_owned(),
        r#"{"in":19,"str":{"pre":0,"str":"Expected"}}"#.to_owned(),
        r#"{"in":20,"str":{"pre":19,"str":"claim"}}"#.to_owned(),
        r#"{"ie":10,"sort":0}"#.to_owned(),
        r#"{"ie":11,"const":{"name":12,"us":[]}}"#.to_owned(),
        r#"{"ie":12,"const":{"name":14,"us":[]}}"#.to_owned(),
        r#"{"ie":13,"const":{"name":16,"us":[]}}"#.to_owned(),
        r#"{"ie":14,"const":{"name":18,"us":[]}}"#.to_owned(),
        r#"{"ie":15,"app":{"arg":13,"fn":12}}"#.to_owned(),
        r#"{"ie":16,"app":{"arg":14,"fn":15}}"#.to_owned(),
        r#"{"ie":17,"app":{"arg":16,"fn":11}}"#.to_owned(),
        r#"{"def":{"all":[12],"hints":"abbrev","levelParams":[],"name":12,"safety":"safe","type":10,"value":10}}"#.to_owned(),
        r#"{"def":{"all":[14],"hints":"abbrev","levelParams":[],"name":14,"safety":"safe","type":10,"value":10}}"#.to_owned(),
        r#"{"def":{"all":[16],"hints":"abbrev","levelParams":[],"name":16,"safety":"safe","type":10,"value":10}}"#.to_owned(),
        r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#.to_owned(),
        format!(
            r#"{{"def":{{"all":[20],"hints":"abbrev","levelParams":[],"name":20,"safety":"safe","type":10,"value":{claim_value_expr}}}}}"#
        ),
    ]
    .join("\n")
        + "\n"
}

pub(super) fn build_proof_ndjson(tamper_claim: bool, custom_axiom: Option<&str>) -> String {
    let base_expected = build_expected_ndjson(tamper_claim);
    let mut lines = vec![
        base_expected.trim_end().to_owned(),
        r#"{"in":21,"str":{"pre":0,"str":"Proof"}}"#.to_owned(),
        r#"{"in":22,"str":{"pre":21,"str":"verify"}}"#.to_owned(),
        r#"{"ie":20,"const":{"name":20,"us":[]}}"#.to_owned(),
    ];
    if let Some(ax_leaf) = custom_axiom {
        lines.push(format!(r#"{{"in":23,"str":{{"pre":21,"str":"{ax_leaf}"}}}}"#));
        lines.push(r#"{"ie":21,"const":{"name":23,"us":[]}}"#.to_owned());
        lines.push(
            r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":23,"type":20}}"#.to_owned(),
        );
        lines.push(
            r#"{"thm":{"all":[22],"levelParams":[],"name":22,"type":20,"value":21}}"#.to_owned(),
        );
    } else {
        lines.push(
            r#"{"thm":{"all":[22],"levelParams":[],"name":22,"type":20,"value":10}}"#.to_owned(),
        );
    }
    lines.join("\n") + "\n"
}

impl SyntheticComparatorHarness {
    pub(super) fn new(cfg: SyntheticHarnessConfig) -> Self {
        let tmp = TempDir::new().unwrap();
        let sysroot = tmp.path().join("sysroot");
        let bin_dir = sysroot.join("bin");
        let init_lib = sysroot.join("lib/lean/Init");
        let init_src = sysroot.join("src/lean/Init");
        fs::create_dir_all(&bin_dir).unwrap();
        fs::create_dir_all(&init_lib).unwrap();
        fs::create_dir_all(&init_src).unwrap();
        for m in ["Coe", "Core", "Notation", "Prelude", "SizeOf", "Tactics"] {
            fs::write(init_lib.join(format!("{m}.olean")), b"olean\x02\x00\x00").unwrap();
            fs::write(init_src.join(format!("{m}.lean")), b"prelude\n").unwrap();
        }

        let fixtures_dir = tmp.path().join("ndjson_fixtures");
        fs::create_dir_all(&fixtures_dir).unwrap();
        fs::write(
            fixtures_dir.join("init.ndjson"),
            build_init_ndjson(cfg.omit_init_primitive),
        )
        .unwrap();
        fs::write(
            fixtures_dir.join("expected.ndjson"),
            build_expected_ndjson(cfg.tamper_expected_claim_in_expected),
        )
        .unwrap();
        fs::write(
            fixtures_dir.join("proof.ndjson"),
            build_proof_ndjson(
                cfg.tamper_expected_claim_in_proof,
                cfg.inject_custom_axiom_in_proof,
            ),
        )
        .unwrap();

        let lean_bin = bin_dir.join("lean");
        let lean_script = format!(
            r#"#!/usr/bin/env python3
import json, pathlib, sys
args = sys.argv[1:]
if args == ["--version"]:
    print("Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit 0000000000000000000000000000000000000000, Release)")
    sys.exit(0)
if args == ["--print-prefix"]:
    print({sysroot:?})
    sys.exit(0)
if "--run" in args:
    idx = args.index("--run")
    req = json.loads(pathlib.Path(args[idx + 2]).read_text())
    mode = req["mode"]
    out = pathlib.Path(args[idx + 3])
    if mode == "headers":
        res = {{"headers": [{{"module": m, "imports": [], "isModule": False}} for m, _ in req["sources"]]}}
    elif mode == "resolve-imports":
        edge = lambda m: {{"module": m, "isMeta": False, "importAll": False, "isExported": True}}
        res = {{"graph": {{
            "Init.Prelude": [],
            "Init.Core": [edge(m) for m in ("Init.Prelude", "Init.Coe", "Init.Notation", "Init.SizeOf", "Init.Tactics")],
            "Init.Coe": [edge("Init.Prelude")],
            "Init.Notation": [edge("Init.Prelude")],
            "Init.SizeOf": [edge("Init.Prelude")],
            "Init.Tactics": [edge("Init.Prelude")],
        }}}}
    elif mode == "spec-preflight":
        res = {{"checked": [m for m, _ in req["sources"]]}}
    elif mode == "sysroot-consts":
        res = {{"sysrootConsts": [["Init.Core", ["Classical.choice", "Quot.sound", "propext"]]]}}
    elif mode == "target-consts":
        listing = {{
            "Trusted.MirSemantics": ["Trusted.MirSemantics.Crate.mk", "Trusted.MirSemantics.UnitTheorem"],
            "Trusted.Unused": ["Trusted.Unused.helper"],
            "Captured": ["Captured.program"],
            "Spec": ["Spec.specs"],
            "Expected": ["Expected.claim"],
        }}
        res = {{"targetConsts": [[m, listing[m], [], []] for m, _ in req["targets"]]}}
    else:
        raise RuntimeError(f"unexpected mode {{mode}}")
    out.write_text(json.dumps({{"ok": True, "result": res}}))
    sys.exit(0)
if "-o" in args:
    pathlib.Path(args[args.index("-o") + 1]).write_bytes(b"olean\x02\x00\x00")
    sys.exit(0)
sys.exit(0)
"#,
            sysroot = sysroot.to_string_lossy()
        );
        fs::write(&lean_bin, lean_script).unwrap();
        fs::set_permissions(&lean_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let leanexport_bin = bin_dir.join("leanexport");
        let leanexport_script = format!(
            r#"#!/usr/bin/env python3
import pathlib, sys
args = sys.argv[1:]
fixtures = pathlib.Path({fixtures:?})
if "--ignore-missing" in args:
    sys.exit("unexpected --ignore-missing")
if "Proof.verify" in args:
    sys.stdout.write((fixtures / "proof.ndjson").read_text())
elif "Expected.claim" in args:
    sys.stdout.write((fixtures / "expected.ndjson").read_text())
elif args and args[0] == "Init":
    sys.stdout.write((fixtures / "init.ndjson").read_text())
else:
    sys.exit(f"unexpected leanexport arguments {{args}}")
"#,
            fixtures = fixtures_dir.to_string_lossy()
        );
        fs::write(&leanexport_bin, leanexport_script).unwrap();
        fs::set_permissions(&leanexport_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let invocation_log = tmp.path().join("stub_invocations.jsonl");
        let nanoda_bin = bin_dir.join("nanoda_bin");
        fs::write(
            &nanoda_bin,
            render_inspecting_stub(NANODA_STUB_BODY, &invocation_log, cfg.nanoda_behavior),
        )
        .unwrap();
        fs::set_permissions(&nanoda_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let con_ron_bin = bin_dir.join("con-ron");
        fs::write(
            &con_ron_bin,
            render_inspecting_stub(CON_RON_STUB_BODY, &invocation_log, cfg.con_ron_behavior),
        )
        .unwrap();
        fs::set_permissions(&con_ron_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let target_dir = tmp.path().join("target");
        fs::create_dir_all(&target_dir).unwrap();
        let files = [
            ("Trusted/MirSemantics.lean", "prelude\n", TargetRole::Model),
            ("Trusted/Unused.lean", "prelude\n", TargetRole::Model),
            ("Captured.lean", "prelude\n", TargetRole::Capture),
            ("Spec.lean", "prelude\n", TargetRole::Specification),
            ("Expected.lean", "prelude\n", TargetRole::Expected),
            ("Proof.lean", "prelude\n", TargetRole::Proof),
        ];
        let mut modules = Vec::new();
        for (rel, content, role) in files {
            let p = target_dir.join(rel);
            fs::create_dir_all(p.parent().unwrap()).unwrap();
            fs::write(&p, content).unwrap();
            modules.push(TargetModule {
                module: rel.trim_end_matches(".lean").replace('/', "."),
                source: p,
                expected_sha256: sha256_bytes(content.as_bytes()),
                role,
            });
        }
        let zero_hash = "0".repeat(64);
        let request = TargetAuditRequest {
            modules,
            theorem_module: "Proof".to_owned(),
            theorem_name: "Proof.verify".to_owned(),
            expected_module: "Expected".to_owned(),
            expected_declaration: "Expected.claim".to_owned(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
            subject_declaration: "Captured.program".to_owned(),
            specification_declaration: "Spec.specs".to_owned(),
            allow_sorry_in_proof: false,
            bindings: TargetBindings {
                request_sha256: zero_hash.clone(),
                capture_sha256: zero_hash.clone(),
                model_manifest_sha256: zero_hash.clone(),
                specification_manifest_sha256: zero_hash,
            },
        };

        Self {
            tmp,
            lean_bin,
            nanoda_bin,
            con_ron_bin,
            fixtures_dir,
            invocation_log,
            request,
        }
    }

    pub(super) fn checker(&self) -> Checker {
        let mut checker =
            Checker::new(&repo_root(), Some(&self.lean_bin)).expect("create checker");
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(SandboxMode::Unsandboxed);
        checker
    }

    pub(super) fn invocations(&self) -> Vec<Value> {
        if !self.invocation_log.is_file() {
            return Vec::new();
        }
        fs::read_to_string(&self.invocation_log)
            .unwrap()
            .lines()
            .filter(|line| !line.is_empty())
            .map(|line| serde_json::from_str::<Value>(line).expect("valid invocation log JSON"))
            .collect()
    }
}

/// Run `Checker::run_target` through the NDJSON comparator route against
/// a synthetic `v4.35.0` sysroot whose `nanoda_bin` and `con-ron` stubs
/// inspect CLI flags and NDJSON payloads before applying their configured
/// [`StubBehavior`].
pub(super) fn run_synthetic_ndjson_pipeline(
    nanoda_behavior: StubBehavior,
    con_ron_behavior: StubBehavior,
) -> (SyntheticComparatorHarness, Result<Value, cargo_anneal::Failure>) {
    let harness = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        nanoda_behavior,
        con_ron_behavior,
        ..Default::default()
    });
    let mut checker = harness.checker();
    let res = checker.run_target(&harness.request);
    (harness, res)
}
