// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Synthetic `nanoda_bin` and `con-ron` stubs that exercise the full NDJSON
//! comparator pipeline without a `v4.35.0` install (Unix only).

use super::*;
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const SYNTHETIC_META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.35.0"}}}"#;

/// Shared Python 3 NDJSON stream validator embedded in the inspecting
/// `nanoda_bin` and `con-ron` stubs. Rejects malformed JSON, duplicate
/// object keys, missing/wrong metadata, dangling table references,
/// forbidden markers, unsafe/partial declarations, unpermitted axioms,
/// missing required roots, and tampered `Expected.claim` bodies.
const PYTHON_NDJSON_VALIDATOR: &str = r#"
import json, os, pathlib, sys

STANDARD_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
REQUIRED_DECLS = {
    "Expected.claim",
    "Proof.verify",
    "Trusted.MirSemantics.UnitTheorem",
    "Trusted.MirSemantics.Crate.mk",
    "Captured.program",
    "Spec.specs",
}
REQUIRED_CLAIM_CONSTS = {
    "Trusted.MirSemantics.UnitTheorem",
    "Trusted.MirSemantics.Crate.mk",
    "Captured.program",
    "Spec.specs",
}
FORBIDDEN_MARKER = "ANNEAL_FORBIDDEN_MARKER"

def fail(msg):
    sys.stderr.write(f"stub-inspector-error: {msg}\n")
    sys.exit(2)

def parse_json_strict(text, ctx):
    def no_dups(pairs):
        out = {}
        for k, v in pairs:
            if k in out:
                raise ValueError(f"duplicate JSON key {k!r}")
            out[k] = v
        return out
    try:
        return json.loads(text, object_pairs_hook=no_dups)
    except Exception as exc:
        fail(f"{ctx}: invalid JSON: {exc}")

def collect_expr_consts(expr_id, exprs, names):
    seen = set()
    stack = [expr_id]
    consts = set()
    while stack:
        eid = stack.pop()
        if eid in seen:
            continue
        seen.add(eid)
        rec = exprs.get(eid)
        if rec is None:
            fail(f"dangling expr reference {eid}")
        if "const" in rec:
            nid = rec["const"]["name"]
            if nid not in names:
                fail(f"dangling const name reference {nid}")
            consts.add(names[nid])
        elif "app" in rec:
            stack.append(rec["app"]["fn"])
            stack.append(rec["app"]["arg"])
        elif "lam" in rec:
            stack.append(rec["lam"]["type"])
            stack.append(rec["lam"]["body"])
        elif "forallE" in rec:
            stack.append(rec["forallE"]["type"])
            stack.append(rec["forallE"]["body"])
        elif "letE" in rec:
            stack.append(rec["letE"]["type"])
            stack.append(rec["letE"]["value"])
            stack.append(rec["letE"]["body"])
        elif "proj" in rec:
            stack.append(rec["proj"]["struct"])
        elif "mdata" in rec:
            stack.append(rec["mdata"]["expr"])
    return consts

def validate_ndjson(ndjson_path, permitted_axioms):
    if not ndjson_path.is_file():
        fail(f"missing NDJSON file {ndjson_path}")
    raw_lines = [ln for ln in ndjson_path.read_text(encoding="utf-8").splitlines() if ln]
    if not raw_lines:
        fail(f"empty NDJSON stream at {ndjson_path}")

    meta_obj = parse_json_strict(raw_lines[0], f"{ndjson_path}:1")
    if not isinstance(meta_obj, dict) or list(meta_obj.keys()) != ["meta"]:
        fail("line 1 must contain only 'meta'")
    meta = meta_obj["meta"]
    if meta.get("format", {}).get("version") != "3.1.0":
        fail(f"unexpected NDJSON format version: {meta.get('format')}")
    if not meta.get("exporter", {}).get("name") or not meta.get("lean", {}).get("version"):
        fail(f"incomplete NDJSON metadata header: {meta}")

    names = {0: ""}
    levels = {0}
    exprs = {}
    decls = {}
    axioms = []

    for line_no, line in enumerate(raw_lines[1:], start=2):
        if FORBIDDEN_MARKER in line:
            fail(f"line {line_no}: forbidden marker {FORBIDDEN_MARKER} detected")
        obj = parse_json_strict(line, f"{ndjson_path}:{line_no}")
        if not isinstance(obj, dict):
            fail(f"line {line_no}: expected JSON object")
        if "in" in obj:
            if len(obj) != 2:
                fail(f"line {line_no}: name entry must have 2 keys")
            idx = obj["in"]
            if not isinstance(idx, int) or idx in names:
                fail(f"line {line_no}: invalid or duplicate name index {idx!r}")
            if "str" in obj:
                pre = obj["str"]["pre"]
                seg = obj["str"]["str"]
                if pre not in names or not isinstance(seg, str):
                    fail(f"line {line_no}: malformed Name.str")
                names[idx] = f"{names[pre]}.{seg}" if names[pre] else seg
            elif "num" in obj:
                pre = obj["num"]["pre"]
                num = obj["num"]["i"]
                if pre not in names or not isinstance(num, int):
                    fail(f"line {line_no}: malformed Name.num")
                names[idx] = f"{names[pre]}.{num}" if names[pre] else str(num)
            else:
                fail(f"line {line_no}: unknown name variant")
        elif "il" in obj:
            if len(obj) != 2:
                fail(f"line {line_no}: level entry must have 2 keys")
            idx = obj["il"]
            if not isinstance(idx, int) or idx in levels:
                fail(f"line {line_no}: invalid or duplicate level index {idx!r}")
            levels.add(idx)
        elif "ie" in obj:
            if len(obj) != 2:
                fail(f"line {line_no}: expr entry must have 2 keys")
            idx = obj["ie"]
            if not isinstance(idx, int) or idx in exprs:
                fail(f"line {line_no}: invalid or duplicate expr index {idx!r}")
            exprs[idx] = obj
        else:
            if len(obj) != 1:
                fail(f"line {line_no}: declaration record must have exactly 1 key")
            tag, rec = next(iter(obj.items()))
            if tag not in ("axiom", "def", "thm", "opaque", "quot", "inductive"):
                fail(f"line {line_no}: unknown record tag {tag!r}")
            if tag == "inductive":
                for sub_key in ("types", "ctors", "recs"):
                    for item in rec.get(sub_key, []):
                        if item.get("isUnsafe", False):
                            fail(f"line {line_no}: unsafe inductive item")
                        nid = item["name"]
                        if nid not in names:
                            fail(f"line {line_no}: dangling inductive name {nid}")
                        decls[names[nid]] = (sub_key, item)
                continue
            nid = rec["name"]
            if nid not in names:
                fail(f"line {line_no}: dangling decl name {nid}")
            dname = names[nid]
            if dname in decls:
                fail(f"line {line_no}: duplicate declaration {dname}")
            if tag == "axiom":
                if rec.get("isUnsafe", False):
                    fail(f"line {line_no}: unsafe axiom {dname}")
                if dname not in permitted_axioms:
                    fail(f"line {line_no}: unpermitted axiom {dname}")
                axioms.append(dname)
            elif tag == "def":
                if rec.get("safety") != "safe":
                    fail(f"line {line_no}: non-safe def {dname}: {rec.get('safety')}")
            elif tag == "opaque":
                if rec.get("isUnsafe", False):
                    fail(f"line {line_no}: unsafe opaque {dname}")
            decls[dname] = (tag, rec)

    missing = sorted(REQUIRED_DECLS - set(decls.keys()))
    if missing:
        fail(f"missing required declarations in NDJSON stream: {missing}")

    claim_tag, claim_rec = decls["Expected.claim"]
    if claim_tag != "def":
        fail(f"Expected.claim must be a def, found {claim_tag}")
    claim_ty_expr = exprs.get(claim_rec["type"])
    if not isinstance(claim_ty_expr, dict) or claim_ty_expr.get("sort") != 0:
        fail(f"tampered Expected.claim type expr: expected Prop (sort 0), got {claim_ty_expr}")
    claim_val_expr = exprs.get(claim_rec["value"])
    if not isinstance(claim_val_expr, dict) or "app" not in claim_val_expr:
        fail(f"tampered Expected.claim value expr: expected app, got {claim_val_expr}")
    claim_consts = collect_expr_consts(claim_rec["value"], exprs, names)
    missing_claim_consts = sorted(REQUIRED_CLAIM_CONSTS - claim_consts)
    if missing_claim_consts:
        fail(f"tampered Expected.claim body missing canonical roots: {missing_claim_consts}")

    verify_tag, _ = decls["Proof.verify"]
    if verify_tag != "thm":
        fail(f"Proof.verify must be a thm, found {verify_tag}")

    return {"decl_count": len(decls), "axioms": sorted(axioms), "line_count": len(raw_lines)}

def record_invocation(log_path, entry):
    if log_path:
        with open(log_path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry) + "\n")
"#;

const NANODA_STUB_BODY: &str = r#"
args = sys.argv[1:]
if len(args) != 1:
    fail(f"nanoda_bin expected exactly 1 config argument, got {args!r}")
cfg_path = pathlib.Path(args[0])
if cfg_path.name != "nanoda_config.json" or not cfg_path.is_file():
    fail(f"nanoda_bin expected nanoda_config.json file, got {cfg_path}")
cfg = parse_json_strict(cfg_path.read_text(encoding="utf-8"), str(cfg_path))
expected_keys = {
    "use_stdin",
    "export_file_path",
    "permitted_axioms",
    "unpermitted_axiom_hard_error",
    "num_threads",
    "nat_extension",
    "string_extension",
}
if set(cfg.keys()) != expected_keys:
    fail(f"nanoda_config.json keys mismatch: got {sorted(cfg.keys())}")
if cfg["use_stdin"] is not False:
    fail(f"nanoda_config.json use_stdin must be false, got {cfg['use_stdin']!r}")
if cfg["unpermitted_axiom_hard_error"] is not True:
    fail("nanoda_config.json unpermitted_axiom_hard_error must be true")
if cfg["nat_extension"] is not True or cfg["string_extension"] is not True:
    fail("nanoda_config.json nat_extension and string_extension must be true")
if type(cfg["num_threads"]) is not int or not (1 <= cfg["num_threads"] <= 4):
    fail(f"nanoda_config.json invalid num_threads: {cfg['num_threads']!r}")
permitted = cfg["permitted_axioms"]
if not isinstance(permitted, list) or not all(isinstance(x, str) for x in permitted):
    fail(f"nanoda_config.json invalid permitted_axioms: {permitted!r}")
if set(permitted) != STANDARD_AXIOMS:
    fail(f"nanoda_config.json unexpected permitted_axioms: {permitted!r}")
export_path = pathlib.Path(cfg["export_file_path"])
if export_path.name != "proof_full.ndjson":
    fail(f"nanoda_config.json unexpected export_file_path: {export_path}")

stats = validate_ndjson(export_path, set(permitted))
record_invocation(LOG_PATH, {
    "tool": "nanoda_bin",
    "argv": args,
    "config": cfg,
    "stats": stats,
})
forced_exit = FORCED_EXIT
env_exit = os.environ.get("ANNEAL_STUB_NANODA_EXIT")
if env_exit:
    forced_exit = int(env_exit)
if FORCED_DIAG:
    sys.stderr.write(f"{FORCED_DIAG}\n")
sys.exit(forced_exit)
"#;

const CON_RON_STUB_BODY: &str = r#"
args = sys.argv[1:]
if len(args) != 3:
    fail(f"con-ron expected 3 arguments (--verified --jobs=N <proof_full.ndjson>), got {args!r}")
if args[0] != "--verified":
    fail(f"con-ron arg[0] must be --verified, got {args[0]!r}")
if not args[1].startswith("--jobs="):
    fail(f"con-ron arg[1] must be --jobs=N, got {args[1]!r}")
jobs_str = args[1][len("--jobs="):]
if not jobs_str.isdigit() or not (1 <= int(jobs_str) <= 2):
    fail(f"con-ron invalid --jobs value: {args[1]!r}")
ndjson_path = pathlib.Path(args[2])
if ndjson_path.name != "proof_full.ndjson":
    fail(f"con-ron unexpected NDJSON path: {ndjson_path}")

stats = validate_ndjson(ndjson_path, STANDARD_AXIOMS)
record_invocation(LOG_PATH, {
    "tool": "con-ron",
    "argv": args,
    "jobs": int(jobs_str),
    "stats": stats,
})
forced_exit = FORCED_EXIT
env_exit = os.environ.get("ANNEAL_STUB_CON_RON_EXIT")
if env_exit:
    forced_exit = int(env_exit)
if FORCED_DIAG:
    sys.stderr.write(f"{FORCED_DIAG}\n")
sys.exit(forced_exit)
"#;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StubBehavior {
    Accept,
    Fail { exit_code: i32, diagnostic: &'static str },
    PanicAtExitZero { diagnostic: &'static str },
}

impl StubBehavior {
    fn exit_code(self) -> i32 {
        match self {
            Self::Accept | Self::PanicAtExitZero { .. } => 0,
            Self::Fail { exit_code, .. } => exit_code,
        }
    }

    fn diagnostic(self) -> &'static str {
        match self {
            Self::Accept => "",
            Self::Fail { diagnostic, .. } | Self::PanicAtExitZero { diagnostic } => diagnostic,
        }
    }
}

#[derive(Clone, Debug)]
struct SyntheticHarnessConfig {
    omit_init_primitive: Option<&'static str>,
    tamper_expected_claim_in_expected: bool,
    tamper_expected_claim_in_proof: bool,
    inject_custom_axiom_in_proof: Option<&'static str>,
    nanoda_behavior: StubBehavior,
    con_ron_behavior: StubBehavior,
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

struct SyntheticComparatorHarness {
    tmp: TempDir,
    lean_bin: PathBuf,
    nanoda_bin: PathBuf,
    con_ron_bin: PathBuf,
    fixtures_dir: PathBuf,
    invocation_log: PathBuf,
    request: TargetAuditRequest,
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

fn build_proof_ndjson(tamper_claim: bool, custom_axiom: Option<&str>) -> String {
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

fn render_inspecting_stub(body: &str, log_path: &Path, behavior: StubBehavior) -> String {
    let log_json = serde_json::to_string(&log_path.to_string_lossy()).unwrap();
    let diag_json = serde_json::to_string(behavior.diagnostic()).unwrap();
    format!(
        "#!/usr/bin/env python3\n{PYTHON_NDJSON_VALIDATOR}\nLOG_PATH = {log_json}\nFORCED_EXIT = {}\nFORCED_DIAG = {diag_json}\n{body}",
        behavior.exit_code()
    )
}

impl SyntheticComparatorHarness {
    fn new(cfg: SyntheticHarnessConfig) -> Self {
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

    fn checker(&self) -> Checker {
        let mut checker =
            Checker::new(&repo_root(), Some(&self.lean_bin)).expect("create checker");
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(SandboxMode::Unsandboxed);
        checker
    }

    fn invocations(&self) -> Vec<Value> {
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
fn run_synthetic_ndjson_pipeline(
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

#[test]
fn synthetic_ndjson_comparator_runs_full_target_audit_pipeline_without_v435_install() {
    let (harness, res) =
        run_synthetic_ndjson_pipeline(StubBehavior::Accept, StubBehavior::Accept);
    let report = res.expect("synthetic NDJSON comparator run_target must succeed");
    assert_eq!(report["auditMode"], json!("ndjson_comparator"));
    assert_eq!(report["replay"], json!(true));
    assert_eq!(report["kernelsPassed"], json!(["nanoda_bin", "con-ron"]));
    for key in ["leanexportSha256", "nanodaBinSha256", "conRonSha256"] {
        assert!(cargo_anneal::is_sha256_hex(report[key].as_str().unwrap()));
    }

    // The report carries the admitted import graph, and each closure lists
    // exactly the declarations it reaches, attributed to their modules, so
    // the unreached `Trusted.Unused` model module appears in no closure and
    // receives no `moduleIdentities` entry.
    let graph = report["graph"].as_object().expect("audit.graph must be an object");
    for module in [
        "Trusted.MirSemantics",
        "Trusted.Unused",
        "Captured",
        "Spec",
        "Expected",
        "Init.Prelude",
        "Init.Core",
    ] {
        assert!(graph.contains_key(module), "audit.graph lacks {module}: {graph:?}");
    }
    let closure = |key: &str| -> Vec<(String, String)> {
        report[key]
            .as_array()
            .unwrap_or_else(|| panic!("missing {key}"))
            .iter()
            .map(|e| {
                (
                    e["name"].as_str().unwrap().to_owned(),
                    e["module"].as_str().unwrap().to_owned(),
                )
            })
            .collect()
    };
    let model = closure("modelClosure");
    assert!(model.contains(&(
        "Trusted.MirSemantics.UnitTheorem".to_owned(),
        "Trusted.MirSemantics".to_owned()
    )));
    assert!(model.iter().all(|(_, m)| m == "Trusted.MirSemantics" || m.starts_with("Init.")));
    assert!(
        closure("subjectClosure")
            .contains(&("Captured.program".to_owned(), "Captured".to_owned()))
    );
    assert!(
        closure("specificationClosure")
            .contains(&("Spec.specs".to_owned(), "Spec".to_owned()))
    );
    for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
        assert!(
            closure(key)
                .iter()
                .all(|(n, m)| n != m && m != "Trusted.Unused" && graph.contains_key(m)),
            "{key}"
        );
    }
    let identities = report["moduleIdentities"].as_object().expect("moduleIdentities");
    assert!(identities.contains_key("Trusted.MirSemantics"), "{identities:?}");
    assert!(!identities.contains_key("Trusted.Unused"), "{identities:?}");

    // Confirm both inspecting kernel stubs actually ran in order and
    // validated exact CLI flags, config JSON, and NDJSON declarations.
    let calls = harness.invocations();
    let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
    assert_eq!(tools, vec!["nanoda_bin", "con-ron"]);
    assert_eq!(calls[0]["config"]["unpermitted_axiom_hard_error"], json!(true));
    assert_eq!(calls[0]["config"]["nat_extension"], json!(true));
    assert_eq!(calls[0]["config"]["string_extension"], json!(true));
    assert_eq!(calls[1]["argv"][0], json!("--verified"));
    assert!(calls[0]["stats"]["decl_count"].as_u64().is_some_and(|n| n >= 6));
    assert!(calls[1]["stats"]["decl_count"].as_u64().is_some_and(|n| n >= 6));
}

/// The comparator route fails closed whenever either required kernel
/// rejects the export, by a nonzero exit or by a Lean panic marker on
/// stderr despite exit code 0, without a `v4.35.0` install.
#[test]
fn synthetic_ndjson_comparator_fails_closed_when_a_stub_kernel_rejects() {
    let rejecting = StubBehavior::Fail { exit_code: 1, diagnostic: "type mismatch" };
    let panicking = StubBehavior::PanicAtExitZero { diagnostic: "PANIC at Lean.Kernel" };
    for (label, nanoda_bin, con_ron, code, needle) in [
        (
            "nanoda_bin exit 1",
            rejecting,
            StubBehavior::Accept,
            1,
            "nanoda_bin rejected proof export",
        ),
        (
            "con-ron exit 1",
            StubBehavior::Accept,
            rejecting,
            1,
            "con-ron rejected proof export",
        ),
        ("nanoda_bin panic", panicking, StubBehavior::Accept, 2, "Lean runtime panic marker"),
        ("con-ron panic", StubBehavior::Accept, panicking, 2, "Lean runtime panic marker"),
    ] {
        let (harness, res) = run_synthetic_ndjson_pipeline(nanoda_bin, con_ron);
        let err = res.expect_err(label);
        assert_eq!(err.code, code, "{label}: {err}");
        assert!(err.message.contains(needle), "{label}: {err}");
        let (phase, expected_tools): (&str, &[&str]) = if nanoda_bin == StubBehavior::Accept {
            ("con-ron", &["nanoda_bin", "con-ron"])
        } else {
            ("nanoda", &["nanoda_bin"])
        };
        assert!(err.phase.contains(phase), "{label}: {err}");
        let calls = harness.invocations();
        let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
        assert_eq!(tools, expected_tools, "{label}");
    }
}

#[test]
fn synthetic_ndjson_comparator_rejects_nanoda_nonzero_exit() {
    let (harness, res) = run_synthetic_ndjson_pipeline(
        StubBehavior::Fail {
            exit_code: 1,
            diagnostic: "injected nanoda_bin kernel rejection",
        },
        StubBehavior::Accept,
    );
    let err = res.unwrap_err();
    assert_eq!(err.code, 1, "nanoda_bin failure must fail with policy code 1: {err}");
    assert_eq!(err.phase, "ndjson-nanoda", "{err}");
    assert!(err.message.contains("injected nanoda_bin kernel rejection"), "{err}");

    // Must fail closed before invoking `con-ron`.
    let calls = harness.invocations();
    let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
    assert_eq!(tools, vec!["nanoda_bin"]);
}

#[test]
fn synthetic_ndjson_comparator_rejects_con_ron_nonzero_exit() {
    let (harness, res) = run_synthetic_ndjson_pipeline(
        StubBehavior::Accept,
        StubBehavior::Fail { exit_code: 1, diagnostic: "injected con-ron kernel rejection" },
    );
    let err = res.unwrap_err();
    assert_eq!(err.code, 1, "con-ron failure must fail with policy code 1: {err}");
    assert_eq!(err.phase, "ndjson-con-ron", "{err}");
    assert!(err.message.contains("injected con-ron kernel rejection"), "{err}");

    let calls = harness.invocations();
    let tools: Vec<&str> = calls.iter().map(|c| c["tool"].as_str().unwrap()).collect();
    assert_eq!(tools, vec!["nanoda_bin", "con-ron"]);
}

#[test]
fn synthetic_ndjson_comparator_rejects_tampered_expected_claim() {
    // 1. Tampering `Expected.claim` in the untrusted proof export diverges
    // from trusted `expected_cone.ndjson`.
    let proof_tamper = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        tamper_expected_claim_in_proof: true,
        ..Default::default()
    });
    let mut checker = proof_tamper.checker();
    let err = checker.run_target(&proof_tamper.request).unwrap_err();
    assert_eq!(err.code, 1, "proof-side Expected.claim tamper must fail with code 1: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(
        err.message.contains("Expected.claim")
            && err.message.contains("differs between trusted expected export and proof export"),
        "{err}"
    );
    assert!(proof_tamper.invocations().is_empty());

    // 2. Tampering `Expected.claim` identically in BOTH exports still fails
    // canonical claim-body verification.
    let both_tamper = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        tamper_expected_claim_in_expected: true,
        tamper_expected_claim_in_proof: true,
        ..Default::default()
    });
    let mut checker = both_tamper.checker();
    let err = checker.run_target(&both_tamper.request).unwrap_err();
    assert_eq!(err.code, 1, "canonical Expected.claim tamper must fail with code 1: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(
        err.message.contains("Expected.claim")
            && err.message.contains("differs from canonical root application"),
        "{err}"
    );
    assert!(both_tamper.invocations().is_empty());
}

#[test]
fn synthetic_ndjson_comparator_rejects_missing_init_primitive_and_custom_axiom() {
    // 1. Missing pinned `Init` primitive (`Nat.gcd`) fails closed.
    let missing_prim = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        omit_init_primitive: Some("Nat.gcd"),
        ..Default::default()
    });
    let mut checker = missing_prim.checker();
    let err = checker.run_target(&missing_prim.request).unwrap_err();
    assert_eq!(err.code, 2, "missing Init primitive must fail with operational code 2: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(err.message.contains("Nat.gcd"), "{err}");
    assert!(missing_prim.invocations().is_empty());

    // 2. Unexpected custom axiom (`Proof.cheat`) in exported NDJSON fails
    // closed with policy code 1.
    let custom_ax = SyntheticComparatorHarness::new(SyntheticHarnessConfig {
        inject_custom_axiom_in_proof: Some("cheat"),
        ..Default::default()
    });
    let mut checker = custom_ax.checker();
    let err = checker.run_target(&custom_ax.request).unwrap_err();
    assert_eq!(err.code, 1, "custom axiom must fail with policy code 1: {err}");
    assert_eq!(err.phase, "ndjson-comparator", "{err}");
    assert!(
        err.message.contains("unpermitted axiom `Proof.cheat` in proof export"),
        "{err}"
    );
    assert!(custom_ax.invocations().is_empty());
}

#[test]
fn synthetic_inspecting_stubs_reject_malformed_cli_and_ndjson_directly() {
    let harness = SyntheticComparatorHarness::new(SyntheticHarnessConfig::default());
    let scratch = harness.tmp.path().join("direct_stub_cases");
    fs::create_dir_all(&scratch).unwrap();
    let valid_proof = harness.fixtures_dir.join("proof.ndjson");
    let staged_valid = scratch.join("proof_full.ndjson");
    fs::copy(&valid_proof, &staged_valid).unwrap();

    let write_nanoda_cfg = |name: &str, ndjson: &Path, hard_err: bool| -> PathBuf {
        let dir = scratch.join(name);
        fs::create_dir_all(&dir).unwrap();
        let cfg_path = dir.join("nanoda_config.json");
        let cfg = json!({
            "use_stdin": false,
            "export_file_path": ndjson.to_string_lossy(),
            "permitted_axioms": STANDARD_PERMITTED_AXIOMS,
            "unpermitted_axiom_hard_error": hard_err,
            "num_threads": 2,
            "nat_extension": true,
            "string_extension": true,
        });
        fs::write(&cfg_path, serde_json::to_vec(&cfg).unwrap()).unwrap();
        cfg_path
    };

    // 1. `nanoda_bin` rejects weakened config
    // (`unpermitted_axiom_hard_error: false`).
    let weak_cfg = write_nanoda_cfg("weak_cfg", &staged_valid, false);
    let out = Command::new(&harness.nanoda_bin).arg(&weak_cfg).output().unwrap();
    assert!(!out.status.success(), "nanoda_bin stub must reject hard_error=false");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("unpermitted_axiom_hard_error"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );

    // 2. `con-ron` rejects wrong flag where `--verified` is required.
    let out = Command::new(&harness.con_ron_bin)
        .args(["--unverified", "--jobs=2", staged_valid.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!out.status.success(), "con-ron stub must reject --unverified");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("must be --verified"), "{stderr}");

    // 3. Both stubs reject tampered `Expected.claim`, custom axioms,
    // forbidden markers, and malformed JSON.
    let tampered_dir = scratch.join("tampered");
    fs::create_dir_all(&tampered_dir).unwrap();
    let tampered_ndjson = tampered_dir.join("proof_full.ndjson");
    fs::write(&tampered_ndjson, build_proof_ndjson(true, None)).unwrap();

    let axiom_dir = scratch.join("custom_axiom");
    fs::create_dir_all(&axiom_dir).unwrap();
    let axiom_ndjson = axiom_dir.join("proof_full.ndjson");
    fs::write(&axiom_ndjson, build_proof_ndjson(false, Some("cheat"))).unwrap();

    let marker_dir = scratch.join("forbidden_marker");
    fs::create_dir_all(&marker_dir).unwrap();
    let marker_ndjson = marker_dir.join("proof_full.ndjson");
    let mut with_marker = build_proof_ndjson(false, None);
    with_marker.push_str(r#"{"in":99,"str":{"pre":0,"str":"ANNEAL_FORBIDDEN_MARKER"}}"#);
    with_marker.push('\n');
    fs::write(&marker_ndjson, with_marker).unwrap();

    let malformed_dir = scratch.join("malformed");
    fs::create_dir_all(&malformed_dir).unwrap();
    let malformed_ndjson = malformed_dir.join("proof_full.ndjson");
    fs::write(&malformed_ndjson, format!("{SYNTHETIC_META}\n{{not-json\n")).unwrap();

    for (label, bad_ndjson, expected_substr) in [
        ("tampered-claim", &tampered_ndjson, "tampered Expected.claim"),
        ("custom-axiom", &axiom_ndjson, "unpermitted axiom Proof.cheat"),
        ("forbidden-marker", &marker_ndjson, "ANNEAL_FORBIDDEN_MARKER"),
        ("malformed-json", &malformed_ndjson, "invalid JSON"),
    ] {
        let cfg = write_nanoda_cfg(label, bad_ndjson, true);
        let nanoda_out = Command::new(&harness.nanoda_bin).arg(&cfg).output().unwrap();
        assert!(
            !nanoda_out.status.success(),
            "nanoda_bin stub must reject {label}"
        );
        let nanoda_err = String::from_utf8_lossy(&nanoda_out.stderr);
        assert!(
            nanoda_err.contains(expected_substr),
            "nanoda_bin {label}: expected `{expected_substr}` in `{nanoda_err}`"
        );

        let con_ron_out = Command::new(&harness.con_ron_bin)
            .args(["--verified", "--jobs=2", bad_ndjson.to_str().unwrap()])
            .output()
            .unwrap();
        assert!(
            !con_ron_out.status.success(),
            "con-ron stub must reject {label}"
        );
        let con_ron_err = String::from_utf8_lossy(&con_ron_out.stderr);
        assert!(
            con_ron_err.contains(expected_substr),
            "con-ron {label}: expected `{expected_substr}` in `{con_ron_err}`"
        );
    }

    // 4. Fault-injection env vars work on direct stub invocations.
    let valid_cfg = write_nanoda_cfg("valid_fault_inject", &staged_valid, true);
    let out = Command::new(&harness.nanoda_bin)
        .arg(&valid_cfg)
        .env("ANNEAL_STUB_NANODA_EXIT", "1")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));

    let out = Command::new(&harness.con_ron_bin)
        .args(["--verified", "--jobs=2", staged_valid.to_str().unwrap()])
        .env("ANNEAL_STUB_CON_RON_EXIT", "1")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
}
