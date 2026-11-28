// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `v4.35.0` specification preflight bans, system-platform admission and
//! namespace escapes, and the strict skip gate.

use super::*;

#[test]
fn spec_preflight_enforces_4130_bans_and_module_reservation_on_v435() {
    let Some(lean) =
        require_or_skip_v435_lean("spec_preflight_enforces_4130_bans_and_module_reservation_on_v435")
    else {
        return;
    };
    let mut checker = new_v435_checker(&lean);

    // 1. Reserved toolchain/inspector roots must fail closed before preflight.
    for reserved in ["SpecPreflight", "SpecPreflight.Extra", "TrustedBoundary", "Init.System.IO"] {
        let tmp = TempDir::new().unwrap();
        let mut req = build_scalar_target_request(tmp.path(), SCALAR_SPEC, SCALAR_PROOF, false);
        let dummy_src = tmp.path().join("Reserved.lean");
        let bytes = b"prelude\n";
        fs::write(&dummy_src, bytes).unwrap();
        req.modules.push(TargetModule {
            module: reserved.to_owned(),
            source: dummy_src,
            expected_sha256: sha256_bytes(bytes),
            role: TargetRole::Proof,
        });
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "reserved module `{reserved}` must fail with policy code 1: {err}");
        assert_eq!(err.phase, "target-input", "{err}");
    }

    // 2. #4130 spec-preflight parser/identifier bans must hold in
    // `SpecPreflight.lean` on Lean v4.35.0 (not only `TrustedBoundary.lean`).
    let cases = [
        ("term-panic", "def p : Nat := panic! \"boom\"\n", "Lean.Parser.Term.panic"),
        ("direct-panic-core", "def pc : Nat := panicCore \"boom\"\n", "panicCore"),
        (
            "term-mod-cast",
            "theorem mc (n : Nat) : (n : Int) = (n : Int) := mod_cast (rfl : n = n)\n",
            "Lean.modCast",
        ),
        (
            "contract-decl-val",
            "def contracted (n : Nat) : Nat\nrequires True\nensures _ => True\n:= n\n",
            "Lean.Parser.Command.contractDeclVal",
        ),
        ("term-qed-try", "theorem t : True := ∎\n", "«term∎»"),
        ("ns-init", "end Spec\nnamespace Init\nend Init\nnamespace Spec\n", "reserved namespace Init"),
        ("ns-std", "end Spec\nnamespace Std\nend Std\nnamespace Spec\n", "reserved namespace Std"),
        ("ns-nat", "end Spec\nnamespace Nat\nend Nat\nnamespace Spec\n", "reserved namespace Nat"),
        (
            "ns-internal-uv",
            "end Spec\nnamespace Internal.UV\nend Internal.UV\nnamespace Spec\n",
            "Internal.UV",
        ),
        (
            "ns-root-trusted",
            "end Spec\nnamespace _root_.Trusted\nend _root_.Trusted\nnamespace Spec\n",
            "_root_.Trusted",
        ),
        ("decl-bare-nat", "end Spec\ndef Nat : Nat := 0\nnamespace Spec\n", "reserved namespace Nat"),
    ];
    for (label, snippet, expected_tok) in cases {
        let mut bad_spec = SCALAR_SPEC.replace("end Spec", &format!("{snippet}\nend Spec"));
        if label == "term-qed-try" {
            bad_spec = bad_spec.replace(
                "import Trusted.MirSemantics",
                "import Trusted.MirSemantics\npublic import Init",
            );
        }
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &bad_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "{label} must fail with policy code 1: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(
            err.message.contains(expected_tok),
            "{label}: expected `{expected_tok}` in `{}`",
            err.message
        );
    }
}

#[test]
fn ndjson_comparator_admits_system_platform_and_blocks_namespace_escapes_on_v435() {
    let Some(lean) = require_or_skip_v435_lean(
        "ndjson_comparator_admits_system_platform_and_blocks_namespace_escapes_on_v435",
    ) else {
        return;
    };
    let mut checker = new_v435_checker(&lean);

    // 1. Real `System.Platform.numBits` (referencing `Init.Prelude`
    // `opaque` `System.Platform.getNumBits`) in `Spec.lean` passes on v4.35.0
    // and records `"Init.Prelude"` provenance in `specificationClosure` and
    // `moduleIdentities`.
    let platform_spec = SCALAR_SPEC.replace(
        "⟨fun _ _ => True, returnsZero⟩",
        "⟨fun _ _ => System.Platform.numBits = 64 ∨ System.Platform.numBits = 32, returnsZero⟩",
    );
    assert!(platform_spec.contains("System.Platform.numBits"));
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &platform_spec, SCALAR_PROOF, false);
        let rep = checker
            .run_target(&req)
            .expect("System.Platform.numBits in Spec must pass on v4.35.0");
        assert_eq!(rep["auditMode"], json!("ndjson_comparator"));
        assert!(
            rep["moduleIdentities"].get("Init.Prelude").is_some(),
            "Init.Prelude provenance must appear in moduleIdentities: {}",
            rep["moduleIdentities"]
        );
        assert!(
            rep["specificationClosure"]
                .as_array()
                .expect("specificationClosure array")
                .iter()
                .any(|e| {
                    e["name"] == "System.Platform.getNumBits" && e["module"] == "Init.Prelude"
                }),
            "System.Platform.getNumBits must be attributed to Init.Prelude in specificationClosure: {}",
            rep["specificationClosure"]
        );
    }

    // 2. Unused `Spec` helper in a custom namespace referencing `runST`
    // (whose type transitively depends on `ST`) passes `SpecPreflight` and
    // fails closed in Action 5c via `spec_declared_consts` even though
    // `Spec.specs` does not use it; `System.FilePath` is blocked earlier in
    // `SpecPreflight`.
    let unused_sys_spec = SCALAR_SPEC.replace(
        "end Spec",
        "end Spec\nnamespace Contract\ndef unusedPath : System.FilePath := ⟨\"/etc/passwd\"⟩\nend Contract\nnamespace Spec\nend Spec",
    );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &unused_sys_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "unused Contract.unusedPath must fail with code 1: {err}");
        assert_eq!(err.phase, "spec-preflight", "{err}");
        assert!(err.message.contains("System.FilePath"), "{err}");
    }
    let unused_st_spec = SCALAR_SPEC
        .replace(
            "import Trusted.MirSemantics\n",
            "import Trusted.MirSemantics\npublic import Init.Control.StateRef\n",
        )
        .replace(
            "end Spec",
            "end Spec\nnamespace Contract\ndef unusedStHelper : Nat := runST (fun _ => pure 0)\nend Contract\nnamespace Spec\nend Spec",
        );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &unused_st_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "unused Contract.unusedStHelper must fail with code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(err.message.contains("ST"), "{err}");
    }

    // 2b. An unreferenced anonymous instance (whose name only elaboration
    // generates) calling `runST` is attributed to `Spec` by the
    // `"target-consts"` module index and fails closed in Action 5c.
    let anon_instance_spec = SCALAR_SPEC
        .replace(
            "import Trusted.MirSemantics\n",
            "import Trusted.MirSemantics\npublic import Init.Control.StateRef\n",
        )
        .replace(
            "end Spec",
            "end Spec\nnamespace Contract\nstructure Box where\n  n : Nat\ninstance : Inhabited Box := ⟨⟨runST (fun _ => pure 0)⟩⟩\nend Contract\nnamespace Spec\nend Spec",
        );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &anon_instance_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "anonymous runST instance must fail with code 1: {err}");
        assert_eq!(err.phase, "ndjson-comparator", "{err}");
        assert!(err.message.contains("ST"), "{err}");
    }

    // 2c. Compiler-generated specification constants (structure
    // constructors/projections, `deriving` instances, named and anonymous
    // instances, `where` and `let rec` auxiliaries) are exported and checked
    // without false rejections.
    let generated_spec = SCALAR_SPEC.replace(
        "end Spec",
        "structure Pair where\n  a : Nat\n  b : Nat\nderiving BEq, Repr, Inhabited\n\
         instance : Add Pair := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩\n\
         def sumTo (n : Nat) : Nat := go n 0\nwhere\n  go : Nat → Nat → Nat\n    | 0, acc => acc\n    | k + 1, acc => go k (acc + k + 1)\n\
         def twice (n : Nat) : Nat :=\n  let rec loop : Nat → Nat\n    | 0 => 0\n    | k + 1 => loop k + 2\n  loop n\n\
         end Spec",
    );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &generated_spec, SCALAR_PROOF, false);
        let rep = checker
            .run_target(&req)
            .expect("generated specification constants must pass on v4.35.0");
        assert_eq!(rep["auditMode"], json!("ndjson_comparator"));
    }

    // 3. `namespace Trusted` in `Spec.lean` fails closed in `SpecPreflight`.
    let trusted_ns_spec = SCALAR_SPEC.replace(
        "end Spec",
        "end Spec\nnamespace Trusted\ndef hijack : Nat := 0\nend Trusted\nnamespace Spec\nend Spec",
    );
    {
        let tmp = TempDir::new().unwrap();
        let req = build_scalar_target_request(tmp.path(), &trusted_ns_spec, SCALAR_PROOF, false);
        let err = checker.run_target(&req).unwrap_err();
        assert_eq!(err.code, 1, "namespace Trusted in Spec must fail with code 1: {err}");
        assert_eq!(err.phase, "spec-preflight", "{err}");
        assert!(err.message.contains("Trusted"), "{err}");
    }
}

#[test]
fn v435_strict_skip_gate_fails_closed_under_ci_strict_and_require_v435() {
    let tmp = TempDir::new().unwrap();
    let empty_home = tmp.path().join("empty_home");
    fs::create_dir_all(&empty_home).unwrap();

    // 1. Non-strict local dev: missing toolchain skips (`Ok(None)`).
    let local_env = |key: &str| match key {
        "HOME" => Some(empty_home.as_os_str().to_os_string()),
        _ => None,
    };
    assert_eq!(
        discover_v435_lean_with_env("sample_v435_test", local_env).unwrap(),
        None
    );

    // 2. `ANNEAL_CI_STRICT=1` fails closed when v4.35.0 comparator tools are
    // missing, even if `ANNEAL_REQUIRE_V435` is unset.
    let ci_strict_env = |key: &str| match key {
        "HOME" => Some(empty_home.as_os_str().to_os_string()),
        "ANNEAL_CI_STRICT" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", ci_strict_env).unwrap_err();
    assert!(err.contains("ANNEAL_CI_STRICT=1"), "{err}");
    assert!(err.contains("sample_v435_test"), "{err}");

    // 3. `ANNEAL_REQUIRE_V435=1` fails closed independently.
    let require_env = |key: &str| match key {
        "HOME" => Some(empty_home.as_os_str().to_os_string()),
        "ANNEAL_REQUIRE_V435" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", require_env).unwrap_err();
    assert!(err.contains("ANNEAL_REQUIRE_V435=1"), "{err}");

    // 4. Unset `HOME` under `ANNEAL_CI_STRICT=1` must still fail closed rather
    // than returning `None` early.
    let no_home_strict = |key: &str| match key {
        "ANNEAL_CI_STRICT" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", no_home_strict).unwrap_err();
    assert!(err.contains("ANNEAL_CI_STRICT=1"), "{err}");

    // 5. Explicit `ANNEAL_LEAN_V435` pointing to a `lean` binary that lacks
    // sibling `leanexport`/`nanoda_bin`/`con-ron` fails closed even in
    // non-strict mode (never silently skips).
    let partial_bin = tmp.path().join("partial/bin");
    fs::create_dir_all(&partial_bin).unwrap();
    let partial_lean = partial_bin.join("lean");
    fs::write(&partial_lean, b"stub").unwrap();
    let partial_non_strict_env = |key: &str| match key {
        "ANNEAL_LEAN_V435" => Some(partial_lean.as_os_str().to_os_string()),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", partial_non_strict_env).unwrap_err();
    assert!(err.contains("ANNEAL_LEAN_V435=") && err.contains("comparator tools"), "{err}");
    let partial_strict_env = |key: &str| match key {
        "ANNEAL_LEAN_V435" => Some(partial_lean.as_os_str().to_os_string()),
        "ANNEAL_CI_STRICT" => Some(OsString::from("1")),
        _ => None,
    };
    let err = discover_v435_lean_with_env("sample_v435_test", partial_strict_env).unwrap_err();
    assert!(err.contains("ANNEAL_LEAN_V435=") && err.contains("comparator tools"), "{err}");

    // 6. Complete `ANNEAL_LEAN_V435` with sibling `leanexport`, `nanoda_bin`,
    // and `con-ron` succeeds.
    for tool in ["leanexport", "nanoda_bin", "con-ron"] {
        fs::write(partial_bin.join(tool), b"stub").unwrap();
    }
    assert_eq!(
        discover_v435_lean_with_env("sample_v435_test", partial_non_strict_env).unwrap(),
        Some(partial_lean)
    );
}
