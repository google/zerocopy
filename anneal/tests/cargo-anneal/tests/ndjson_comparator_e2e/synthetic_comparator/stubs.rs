// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The NDJSON validator and the `nanoda_bin` and `con-ron` stub scripts
//! that the synthetic comparator tests install, and how each stub exits.

use super::*;

pub(super) const SYNTHETIC_META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.35.0"}}}"#;

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

pub(super) const NANODA_STUB_BODY: &str = r#"
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

pub(super) const CON_RON_STUB_BODY: &str = r#"
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
pub(super) enum StubBehavior {
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

pub(super) fn render_inspecting_stub(
    body: &str,
    log_path: &Path,
    behavior: StubBehavior,
) -> String {
    let log_json = serde_json::to_string(&log_path.to_string_lossy()).unwrap();
    let diag_json = serde_json::to_string(behavior.diagnostic()).unwrap();
    format!(
        "#!/usr/bin/env python3\n{PYTHON_NDJSON_VALIDATOR}\nLOG_PATH = {log_json}\nFORCED_EXIT = {}\nFORCED_DIAG = {diag_json}\n{body}",
        behavior.exit_code()
    )
}
