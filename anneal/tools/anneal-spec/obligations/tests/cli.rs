// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end tests of `cargo-anneal-obligations`, including a ledger over the
//! real `zerocopy` proof units and inline specifications.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use serde_json::{json, Value};

/// A scratch directory removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let dir =
            std::env::temp_dir().join(format!("anneal-obligations-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        Scratch(dir)
    }

    fn write(&self, name: &str, value: &Value) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, serde_json::to_string_pretty(value).unwrap()).unwrap();
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run<I, S>(args: I) -> Output
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    Command::new(env!("CARGO_BIN_EXE_cargo-anneal-obligations")).args(args).output().unwrap()
}

fn stdout(out: &Output) -> String {
    String::from_utf8(out.stdout.clone()).unwrap()
}

fn stderr(out: &Output) -> String {
    String::from_utf8(out.stderr.clone()).unwrap()
}

/// A verified selected-unit receipt for crate `demo` that selects `a` out of
/// functions `a` and `b`.
fn receipt() -> Value {
    json!({
        "schema_version": 3,
        "status": "selected_unit_verified",
        "taint_reasons": [],
        "experimental": true,
        "spec_warnings": [],
        "scope": {"kind": "selected_unit", "roots": ["a"]},
        "configuration": {"crate_name": "demo"},
        "correspondence_provenance": {"schema_version": 1},
        "census": [
            {"def_id": 1, "path": "a", "kind": "Fn", "has_body": true,
             "selected": true, "required": true},
            {"def_id": 2, "path": "b", "kind": "Fn", "has_body": true,
             "selected": false, "required": true},
        ],
        "selected": [{"def_id": 1, "path": "a", "body_index": 0}],
        "audit": {
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "axioms": ["propext"],
            "sorryDeclarations": [],
            "replay": true,
            "exactType": true,
        },
    })
}

fn request(roots: &[&str]) -> Value {
    json!({
        "schema_version": 1,
        "compilation": {"crate_name": "demo"},
        "scope": {"kind": "selected_unit", "roots": roots},
    })
}

#[test]
fn help_and_usage_errors() {
    for args in [&["--help"][..], &["anneal-obligations", "-h"]] {
        let out = run(args);
        assert!(out.status.success(), "{}", stderr(&out));
        assert!(stdout(&out).contains("--audit-assumptions"));
    }
    for (args, needle) in [
        (&[][..], "at least one --receipt"),
        (&["--format", "yaml", "--spec", "x.rs"], "unknown format"),
        (&["--receipt"], "--receipt needs a value"),
        (&["--bogus"], "unknown argument"),
        (&["--spec-src-root", "src", "--receipt", "r.json"], "needs at least one --spec"),
        (&["--crate", "a", "--crate", "b", "--spec", "x.rs"], "--crate may be given once"),
    ] {
        let out = run(args);
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert!(stderr(&out).contains(needle), "{args:?}: {}", stderr(&out));
    }
}

#[test]
fn malformed_inputs_exit_2() {
    let dir = Scratch::new("malformed");
    let mut bad = receipt();
    bad["taint_reasons"] = json!(["unpinned_lean"]);
    let bad = dir.write("bad.json", &bad);
    let out = run([Path::new("--receipt"), &bad]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("disagrees with taint_reasons"), "{}", stderr(&out));

    let text = dir.0.join("text.json");
    fs::write(&text, "not json").unwrap();
    let out = run([Path::new("--request"), &text]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("is not valid JSON"), "{}", stderr(&out));

    let out = run(["--receipt", "/nonexistent/receipt.json"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("cannot read"), "{}", stderr(&out));

    // `--spec` diagnostics and CLI flag diagnostics escape control, bidi, and
    // Unicode line/paragraph-separator characters before printing to stderr.
    let bad_spec = dir.0.join("bad_spec.rs");
    fs::write(&bad_spec, "#[anneal::spec(bogus(\"\x1b[2J\u{202e}\u{2028}\r\"))]\npub fn f() {}\n")
        .unwrap();
    let out = run([Path::new("--spec"), &bad_spec]);
    assert_eq!(out.status.code(), Some(2));
    let err = stderr(&out);
    assert!(
        !err.contains('\x1b')
            && !err.contains('\r')
            && !err.contains('\u{202e}')
            && !err.contains('\u{2028}'),
        "{err:?}"
    );
    assert!(err.contains("\\u{1b}[2J"), "{err}");

    let out = run(["--unknown-\x1b[31m\u{202e}"]);
    assert_eq!(out.status.code(), Some(2));
    let err = stderr(&out);
    assert!(!err.contains('\x1b') && !err.contains('\u{202e}'), "{err:?}");
}

#[test]
fn json_ledger_is_independent_of_argument_order() {
    let dir = Scratch::new("order");
    let r = dir.write("r.json", &receipt());
    let q = dir.write("q.json", &request(&["b"]));
    // Repeating an input changes nothing.
    let repeated = run([
        Path::new("--format"),
        Path::new("json"),
        Path::new("--receipt"),
        &r,
        Path::new("--receipt"),
        &r,
        Path::new("--request"),
        &q,
    ]);
    let forward = run([
        Path::new("--format"),
        Path::new("json"),
        Path::new("--receipt"),
        &r,
        Path::new("--request"),
        &q,
    ]);
    let backward = run([
        Path::new("--request"),
        &q,
        Path::new("--receipt"),
        &r,
        Path::new("--format"),
        Path::new("json"),
    ]);
    assert!(forward.status.success(), "{}", stderr(&forward));
    assert_eq!(forward.stdout, backward.stdout);
    assert_eq!(forward.stdout, repeated.stdout);
    let ledger: Value = serde_json::from_slice(&forward.stdout).unwrap();
    assert_eq!(ledger["schema"], json!("anneal-obligations/1"));
    assert_eq!(ledger["crate"], json!("demo"));
    let items: Vec<(&str, &str)> = ledger["items"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| (i["id"].as_str().unwrap(), i["tier"].as_str().unwrap()))
        .collect();
    assert_eq!(items, [("rust-path-v1::a", "proven_conditional"), ("rust-path-v1::b", "deferred")]);
    assert_eq!(
        ledger["items"][0]["conditions"],
        json!(["candidate_tier_model", "selected_unit_scope"])
    );
}

#[test]
fn ratchet_exit_codes() {
    let dir = Scratch::new("ratchet");
    let r = dir.write("r.json", &receipt());
    let q = dir.write("q.json", &request(&["b"]));

    let base = run([
        Path::new("--format"),
        Path::new("json"),
        Path::new("--receipt"),
        &r,
        Path::new("--request"),
        &q,
    ]);
    assert!(base.status.success(), "{}", stderr(&base));
    let baseline = dir.0.join("baseline.json");
    fs::write(&baseline, &base.stdout).unwrap();

    // Same inputs: no regression.
    let same = run([
        Path::new("--receipt"),
        &r,
        Path::new("--request"),
        &q,
        Path::new("--ratchet"),
        &baseline,
    ]);
    assert_eq!(same.status.code(), Some(0), "{}", stderr(&same));

    // Dropping the receipt loses the proof of `a` and the census entry `b`
    // keeps only its request contract.
    let weaker = run([
        Path::new("--request"),
        &q,
        Path::new("--crate"),
        Path::new("demo"),
        Path::new("--ratchet"),
        &baseline,
    ]);
    assert_eq!(weaker.status.code(), Some(1));
    let err = stderr(&weaker);
    assert!(err.contains("ratchet: missing: rust-path-v1::a (was proven_conditional)"), "{err}");
    assert!(err.contains("ratchet failed with 1 finding(s)"), "{err}");

    // `--audit-assumptions` reports `a` as assumed, which is not comparable.
    let audit = run([
        Path::new("--receipt"),
        &r,
        Path::new("--request"),
        &q,
        Path::new("--audit-assumptions"),
        Path::new("--ratchet"),
        &baseline,
    ]);
    assert_eq!(audit.status.code(), Some(2));
    assert!(stderr(&audit).contains("without --audit-assumptions"), "{}", stderr(&audit));
}

/// The `zerocopy` crate root.
fn zerocopy() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../zerocopy")
}

/// The ledger over every `zerocopy/proofs` request and every inline
/// specification in `zerocopy/src`, without receipts: each stated
/// specification is `deferred`, and the IDs that inline specifications and
/// request roots give the same function must coincide, or the ledger would
/// list one function twice.
#[test]
fn zerocopy_requests_and_inline_specs_share_item_ids() {
    let root = zerocopy();
    let mut args = vec!["--format".to_owned(), "json".to_owned()];
    let mut roots_by_claim: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut source_files = BTreeSet::new();
    let mut all_roots = BTreeSet::new();
    let mut units: Vec<PathBuf> =
        fs::read_dir(root.join("proofs")).unwrap().map(|e| e.unwrap().path()).collect();
    units.sort();
    for unit in units.iter().filter(|u| u.join("request.json").is_file()) {
        let request = unit.join("request.json");
        let value: Value = serde_json::from_str(&fs::read_to_string(&request).unwrap()).unwrap();
        let roots: BTreeSet<String> = value["scope"]["roots"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| r.as_str().unwrap().to_owned())
            .collect();
        all_roots.extend(roots.iter().cloned());
        for file in value["compilation"]["source_files"].as_array().unwrap() {
            source_files.insert(file.as_str().unwrap().to_owned());
        }
        if let Ok(text) = fs::read_to_string(unit.join("spec_sources.json")) {
            let sources: Value = serde_json::from_str(&text).unwrap();
            let claim = sources["claim"].as_str().unwrap().to_owned();
            roots_by_claim.entry(claim).or_default().extend(roots);
        }
        args.extend(["--request".to_owned(), request.to_str().unwrap().to_owned()]);
    }
    assert!(!roots_by_claim.is_empty(), "no claim-bound units under {}", root.display());
    let src = root.join("src");
    args.extend(["--spec-src-root".to_owned(), src.to_str().unwrap().to_owned()]);
    // The files the units compile, which omit `doctests.rs`.
    for file in &source_files {
        args.extend(["--spec".to_owned(), file.clone()]);
    }

    let out = run(&args);
    assert!(out.status.success(), "{}", stderr(&out));
    let ledger: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(ledger["crate"], json!("zerocopy"));
    let items = ledger["items"].as_array().unwrap();
    let ids: BTreeSet<&str> = items.iter().map(|i| i["id"].as_str().unwrap()).collect();
    assert!(items.iter().all(|i| i["tier"] == json!("deferred")), "{ledger}");
    for path in &all_roots {
        assert!(ids.contains(format!("rust-path-v1::{path}").as_str()), "{path}");
    }

    // Each claim-bound unit's roots are exactly the inline targets of its
    // claim, and each such function is contracted by both its request and its
    // source file.
    let lower = anneal_spec_lower_targets(&src, &source_files);
    for (claim, roots) in &roots_by_claim {
        let targets: BTreeSet<String> =
            lower.iter().filter(|(c, _)| c == claim).map(|(_, t)| t.clone()).collect();
        assert_eq!(&targets, roots, "claim {claim}");
        for path in roots {
            let id = format!("rust-path-v1::{path}");
            let item = items.iter().find(|i| i["id"] == json!(id)).unwrap();
            let contracts: Vec<&str> =
                item["contracts"].as_array().unwrap().iter().map(|c| c.as_str().unwrap()).collect();
            assert!(contracts.iter().any(|c| c.starts_with("request:")), "{id}: {contracts:?}");
            assert!(contracts.iter().any(|c| c.starts_with("spec:")), "{id}: {contracts:?}");
        }
    }
}

/// `(claim, target)` for every inline specification in `files` under `src`.
fn anneal_spec_lower_targets(src: &Path, files: &BTreeSet<String>) -> Vec<(String, String)> {
    let sources: Vec<anneal_spec_lower::Source> = files
        .iter()
        .map(|file| anneal_spec_lower::Source {
            text: fs::read_to_string(src.join(file)).unwrap(),
            module: anneal_spec_lower::module_path(file),
            label: file.clone(),
        })
        .collect();
    let targets = match anneal_spec_lower::list_targets(&sources) {
        Ok(targets) => targets,
        Err(errors) => panic!("{}", errors.iter().map(|e| e.render(&sources)).collect::<String>()),
    };
    targets.into_iter().map(|t| (t.claim, t.target)).collect()
}

/// Real `zerocopy` overlap (`util::macros::__unsafe` shared between claim-bound
/// unit `03_macros_unsafe` and hand-written unit
/// `04_substantive_and_frombytes_markers`): losing unit `03`'s receipt cannot
/// be masked by unit `04`'s receipt.
#[test]
fn zerocopy_overlapping_units_bind_receipts_to_their_own_contracts() {
    let dir = Scratch::new("zc-overlap");
    let root = zerocopy();
    let req03_path = root.join("proofs/03_macros_unsafe/request.json");
    let req04_path = root.join("proofs/04_substantive_and_frombytes_markers/request.json");
    let req03_val: Value = serde_json::from_str(&fs::read_to_string(&req03_path).unwrap()).unwrap();
    let req04_val: Value = serde_json::from_str(&fs::read_to_string(&req04_path).unwrap()).unwrap();
    let parsed_req03 = anneal_obligations::Request::from_json(&req03_val).unwrap();
    let parsed_req04 = anneal_obligations::Request::from_json(&req04_val).unwrap();

    // Unit 03's checked-in generated Lean module must hash to the exact
    // `specification_manifest_sha256` that `--spec util/macros.rs` expects.
    let spec03_lean =
        fs::read(root.join("proofs/03_macros_unsafe/Specs/zerocopy/zc03_macros_unsafe.lean"))
            .unwrap();
    let sha256_cmd = |bytes: &[u8]| -> String {
        use std::io::Write as _;
        let mut child = std::process::Command::new("sha256sum")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.as_mut().unwrap().write_all(bytes).unwrap();
        let out = child.wait_with_output().unwrap();
        assert!(out.status.success());
        String::from_utf8(out.stdout).unwrap().split_whitespace().next().unwrap().to_owned()
    };
    let spec03_lean_sha = sha256_cmd(&spec03_lean);
    let spec03_manifest =
        serde_json::to_vec_pretty(&json!([["Specs.zerocopy.zc03_macros_unsafe", spec03_lean_sha]]))
            .unwrap();
    let spec03_manifest_sha = sha256_cmd(&spec03_manifest);
    let spec04_lean_sha = sha256_cmd(
        &fs::read(root.join("proofs/04_substantive_and_frombytes_markers/Spec.lean")).unwrap(),
    );
    let spec04_manifest_sha =
        sha256_cmd(&serde_json::to_vec_pretty(&json!([["Spec", spec04_lean_sha]])).unwrap());

    let make_unit_receipt = |roots: &[String], req_sha: &str, spec_sha: &str| -> Value {
        let mut census = Vec::new();
        let mut selected = Vec::new();
        for (i, p) in roots.iter().enumerate() {
            census.push(json!({
                "def_id": i + 1,
                "path": p,
                "kind": "Fn",
                "has_body": true,
                "selected": true,
                "required": true,
            }));
            selected.push(json!({"def_id": i + 1, "path": p, "body_index": i}));
        }
        json!({
            "schema_version": 3,
            "status": "selected_unit_verified",
            "taint_reasons": [],
            "experimental": false,
            "spec_warnings": [],
            "request_sha256": req_sha,
            "specification_manifest_sha256": spec_sha,
            "scope": {"kind": "selected_unit", "roots": roots},
            "configuration": {"crate_name": "zerocopy"},
            "correspondence_provenance": {"schema_version": 1},
            "census": census,
            "selected": selected,
            "audit": {
                "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
                "axioms": ["propext"],
                "sorryDeclarations": [],
                "replay": true,
                "exactType": true,
            },
        })
    };

    let r03 = dir.write(
        "r03.json",
        &make_unit_receipt(
            &parsed_req03.roots,
            parsed_req03.request_sha256.as_deref().unwrap(),
            &spec03_manifest_sha,
        ),
    );
    let r04 = dir.write(
        "r04.json",
        &make_unit_receipt(
            &parsed_req04.roots,
            parsed_req04.request_sha256.as_deref().unwrap(),
            &spec04_manifest_sha,
        ),
    );
    let src_root = root.join("src");

    let base_out = run([
        Path::new("--format"),
        Path::new("json"),
        Path::new("--receipt"),
        &r03,
        Path::new("--receipt"),
        &r04,
        Path::new("--request"),
        &req03_path,
        Path::new("--request"),
        &req04_path,
        Path::new("--spec-src-root"),
        &src_root,
        Path::new("--spec"),
        Path::new("util/macros.rs"),
    ]);
    assert!(base_out.status.success(), "{}", stderr(&base_out));
    let base_json: Value = serde_json::from_slice(&base_out.stdout).unwrap();
    let mac_item = base_json["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|i| i["id"] == json!("rust-path-v1::util::macros::__unsafe"))
        .unwrap();
    assert_eq!(mac_item["tier"], json!("proven_conditional"), "{mac_item}");
    let baseline = dir.0.join("baseline.json");
    fs::write(&baseline, &base_out.stdout).unwrap();

    // Omitting `r03` while `r04` still verifies must regress
    // `util::macros::__unsafe`.
    let dropped = run([
        Path::new("--receipt"),
        &r04,
        Path::new("--request"),
        &req03_path,
        Path::new("--request"),
        &req04_path,
        Path::new("--spec-src-root"),
        &src_root,
        Path::new("--spec"),
        Path::new("util/macros.rs"),
        Path::new("--ratchet"),
        &baseline,
    ]);
    assert_eq!(dropped.status.code(), Some(1), "{}", stderr(&dropped));
    assert!(
        stderr(&dropped).contains(
            "regressed: rust-path-v1::util::macros::__unsafe: proven_conditional -> deferred"
        ),
        "{}",
        stderr(&dropped)
    );
}

/// Real `zerocopy` unit `14_known_layout_and_dst_layout` verifies 40
/// non-generic `<impl KnownLayout for ...>` methods through zero-argument
/// `scope.instantiations` entries. Capture selects each under its census
/// path, which contains `<impl ...>`. A receipt shaped that way is accepted,
/// and its request's contract on each method is discharged only by a receipt
/// for that request.
#[test]
fn zerocopy_zero_argument_instantiations_are_proven_through_their_request() {
    let dir = Scratch::new("zc-zero-arg");
    let req_path = zerocopy().join("proofs/14_known_layout_and_dst_layout/request.json");
    let req: Value = serde_json::from_str(&fs::read_to_string(&req_path).unwrap()).unwrap();
    let parsed = anneal_obligations::Request::from_json(&req).unwrap();
    let roots: Vec<&str> =
        req["scope"]["roots"].as_array().unwrap().iter().map(|r| r.as_str().unwrap()).collect();
    let insts: Vec<&str> = req["scope"]["instantiations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| {
            assert_eq!(i["args"], json!([]), "{i}");
            i["path"].as_str().unwrap()
        })
        .collect();
    assert_eq!(insts.len(), 40);
    assert!(insts.iter().all(|p| p.contains("<impl KnownLayout for ")));
    assert!(parsed.instantiated.is_empty());
    assert_eq!(parsed.roots.len(), roots.len() + insts.len());

    let receipt = |req_sha: &str| -> Value {
        let mut census = Vec::new();
        let mut selected = Vec::new();
        for (i, p) in roots.iter().chain(&insts).enumerate() {
            let root = i < roots.len();
            census.push(json!({
                "def_id": i + 1, "path": p, "kind": "AssocFn", "has_body": true,
                "selected": root, "required": true,
            }));
            selected.push(json!({"def_id": i + 1, "path": p, "body_index": i}));
        }
        json!({
            "schema_version": 3,
            "status": "selected_unit_verified",
            "taint_reasons": [],
            "experimental": false,
            "spec_warnings": [],
            "request_sha256": req_sha,
            "scope": req["scope"],
            "configuration": {"crate_name": "zerocopy"},
            "correspondence_provenance": {"schema_version": 1},
            "census": census,
            "selected": selected,
            "audit": {
                "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
                "axioms": ["propext"],
                "sorryDeclarations": [],
                "replay": true,
                "exactType": true,
            },
        })
    };
    let ledger = |receipt: &Value| -> Value {
        let path = dir.write("r14.json", receipt);
        let out = run([
            Path::new("--format"),
            Path::new("json"),
            Path::new("--receipt"),
            &path,
            Path::new("--request"),
            &req_path,
        ]);
        assert!(out.status.success(), "{}", stderr(&out));
        serde_json::from_slice(&out.stdout).unwrap()
    };
    let tiers = |ledger: &Value| -> BTreeMap<String, String> {
        ledger["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|i| (i["id"].as_str().unwrap().to_owned(), i["tier"].as_str().unwrap().to_owned()))
            .collect()
    };

    let own = tiers(&ledger(&receipt(parsed.request_sha256.as_deref().unwrap())));
    for p in roots.iter().chain(&insts) {
        assert_eq!(own[&format!("rust-path-v1::{p}")], "proven_conditional", "{p}");
    }
    let other = tiers(&ledger(&receipt(&"0".repeat(64))));
    for p in roots.iter().chain(&insts) {
        assert_eq!(other[&format!("rust-path-v1::{p}")], "deferred", "{p}");
    }
}

/// Real `zerocopy` unit `15_generic_wrapper_and_array_markers` verifies 85
/// generic trait-impl methods across 7 traits, 14 wrapper/array types, and 4
/// modules that all share leaf `only_derive_is_allowed_to_implement_this_trait`
/// (plus 4 `util::macro_util::must_use` instances). Adding a second request
/// for another `impl` sharing that leaf must not attach its contract to unit
/// 15's unrelated `impl` instances.
#[test]
fn zerocopy_unit_15_impl_instantiations_isolate_contracts_per_impl() {
    let dir = Scratch::new("zc-unit-15");
    let req15_path = zerocopy().join("proofs/15_generic_wrapper_and_array_markers/request.json");
    let req15: Value = serde_json::from_str(&fs::read_to_string(&req15_path).unwrap()).unwrap();
    let parsed15 = anneal_obligations::Request::from_json(&req15).unwrap();
    assert_eq!(parsed15.roots, ["util::macros::__unsafe"]);
    assert_eq!(parsed15.instantiated.len(), 89);

    let instantiate_path = |path: &str, args: &[String]| -> String {
        if path == "util::macro_util::must_use" {
            return format!("{path}::<{}>", args[0]);
        }
        if args.len() == 2 {
            return path.replace("[T; N]", &format!("[{}; {}]", args[0], args[1]));
        }
        path.replace("<T>", &format!("<{}>", args[0]))
            .replace("*const T>", &format!("*const {}>", args[0]))
            .replace("*mut T>", &format!("*mut {}>", args[0]))
            .replace("<&T>", &format!("<&{}>", args[0]))
    };

    let mut census = vec![json!({
        "def_id": 1,
        "path": "util::macros::__unsafe",
        "kind": "Fn",
        "has_body": true,
        "selected": true,
        "required": true,
    })];
    let mut selected = vec![json!({
        "def_id": 1,
        "path": "util::macros::__unsafe",
        "body_index": 0,
    })];
    let mut def_ids: BTreeMap<String, u64> = BTreeMap::new();
    let mut expected_instances = Vec::new();
    for (idx, (ip, args)) in parsed15.instantiated.iter().enumerate() {
        let next_id = (def_ids.len() + 2) as u64;
        let def_id = *def_ids.entry(ip.clone()).or_insert_with(|| {
            census.push(json!({
                "def_id": next_id,
                "path": ip,
                "kind": if ip.contains("<impl ") { "AssocFn" } else { "Fn" },
                "has_body": true,
                "selected": false,
                "required": true,
            }));
            next_id
        });
        let inst_path = instantiate_path(ip, args);
        assert_ne!(&inst_path, ip, "uninstantiated path for {ip} {args:?}");
        selected.push(json!({
            "def_id": def_id,
            "path": inst_path,
            "body_index": idx + 1,
        }));
        expected_instances.push(inst_path);
    }
    let r15 = dir.write(
        "r15.json",
        &json!({
            "schema_version": 3,
            "status": "selected_unit_verified",
            "taint_reasons": [],
            "experimental": false,
            "spec_warnings": [],
            "request_sha256": parsed15.request_sha256.as_deref().unwrap(),
            "scope": req15["scope"],
            "configuration": {"crate_name": "zerocopy"},
            "correspondence_provenance": {"schema_version": 1},
            "census": census,
            "selected": selected,
            "audit": {
                "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
                "axioms": ["propext"],
                "sorryDeclarations": [],
                "replay": true,
                "exactType": true,
            },
        }),
    );

    // Real `zerocopy` unit `17_slice_array_ref_tuple_instantiations` lists 21
    // distinct `<impl ...>::only_derive_is_allowed_to_implement_this_trait`
    // entries with NO receipt passed here: unit 15's 85 impl instances must
    // still remain `proven_conditional` without acquiring unit 17's contract.
    let req17_path = zerocopy().join("proofs/17_slice_array_ref_tuple_instantiations/request.json");

    let out = run([
        Path::new("--format"),
        Path::new("json"),
        Path::new("--receipt"),
        &r15,
        Path::new("--request"),
        &req15_path,
        Path::new("--request"),
        &req17_path,
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let ledger: Value = serde_json::from_slice(&out.stdout).unwrap();
    let by_id: BTreeMap<&str, &Value> = ledger["items"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| (i["id"].as_str().unwrap(), i))
        .collect();
    let req17_contract = format!("request:{}", req17_path.display());
    for inst in &expected_instances {
        let item = by_id[format!("rust-path-v1::{inst}").as_str()];
        assert_eq!(item["tier"], json!("proven_conditional"), "{inst}: {item}");
        let contracts: Vec<&str> =
            item["contracts"].as_array().unwrap().iter().map(|c| c.as_str().unwrap()).collect();
        assert!(!contracts.contains(&req17_contract.as_str()), "{inst}: {contracts:?}");
    }
    let ref_impl = "_::<impl KnownLayout for &T>::only_derive_is_allowed_to_implement_this_trait";
    assert_eq!(by_id[format!("rust-path-v1::{ref_impl}").as_str()]["tier"], json!("deferred"));
}
