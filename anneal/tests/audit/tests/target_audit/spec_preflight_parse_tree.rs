// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specification preflight parse-tree round trips and negative guards.

use super::*;

#[path = "spec_preflight_parse_tree/command_vectors.rs"]
mod command_vectors;
#[path = "spec_preflight_parse_tree/term_vectors.rs"]
mod term_vectors;

/// Live parse-tree round-trip verification against the pinned Lean parser plus
/// comprehensive negative tests for `"spec-preflight"` covering commands,
/// modifiers, lexical scopes, attributes, deriving, `set_option`, tactics, and
/// term/quotation guards.
#[test]
fn spec_preflight_parse_tree_round_trip_and_negative_guards() {
    // 1. Live parse-tree round-trip probe + exhaustive negative-vector
    //    check against the real `TrustedBoundary.parseAndInspectSpecCommands`
    //    on one loaded `Init` + `Std` parser environment (fast in CI).
    let spec_base = "def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    let vectors: Vec<(&str, &str, &str)> =
        command_vectors::vectors().iter().chain(term_vectors::vectors()).copied().collect();

    // 1. Live parse-tree round-trip probe + exhaustive check of all negative
    //    vectors against `TrustedBoundary.parseAndInspectSpecCommands` in one
    //    loaded `Init` + `Std` parser environment (~3 s total).
    let fixture = Fixture::new(PROOF);
    let mut checker = fixture.checker();
    let adm = checker.tool_admission().unwrap().clone();
    let vectors_json_path = checker.stage().join("spec_preflight_vectors.json");
    let vectors_json: Vec<Json> = vectors
        .iter()
        .map(|(label, snippet, expected)| {
            serde_json::json!([label, format!("{snippet}{spec_base}"), expected])
        })
        .collect();
    fs::write(
        &vectors_json_path,
        serde_json::to_vec(&vectors_json).unwrap(),
    )
    .unwrap();
    let mut source = fs::read_to_string(&adm.inspector).unwrap();
    source.push_str(&format!(
        r#"

#eval do
  Lean.initSearchPath (System.FilePath.mk {:?})
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules #[{{ module := `Init }}, {{ module := `Std }}] {{}}
    (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
  let (cmdKinds, tacKinds) ← TrustedBoundary.collectSpecParserSets env
  unless cmdKinds.contains ``Lean.Parser.Command.eval &&
      cmdKinds.contains ``Lean.Parser.Command.initialize &&
      !cmdKinds.contains ``Lean.Parser.Command.declModifiers do
    throw <| IO.userError "unexpected commandLikeKinds partition"
  unless tacKinds.contains `Lean.Parser.Tactic.bvDecide &&
      tacKinds.contains `Lean.Parser.Tactic.nativeDecide &&
      tacKinds.contains `Lean.Parser.Tactic.grind &&
      tacKinds.contains `Lean.Parser.Tactic.runTac &&
      tacKinds.contains `Lean.Parser.Tactic.Conv.conv do
    throw <| IO.userError "unexpected tacticLikeKinds partition"
  let parseHasKind (src : String) (want : Lean.Name) : IO Unit := do
    let ctx := Lean.Parser.mkInputContext src "<rt>"
    let (stx, st, msgs) := Lean.Parser.parseCommand ctx {{ env := env, options := {{}} }} {{}} {{}}
    if msgs.hasErrors || st.recovering then
      throw <| IO.userError s!"parse failed for: {{src}}"
    let rec hasKind : Lean.Syntax → Bool
      | .node _ k args => k == want || args.any hasKind
      | _ => false
    unless hasKind stx do
      throw <| IO.userError s!"expected syntax kind {{want}} in: {{src}}"
  parseHasKind "def s := include_str \"foo\"" ``Lean.includeStr
  parseHasKind "def e : Nat := by_elab return 0" ``Lean.byElab
  parseHasKind "noncomputable section S" ``Lean.Parser.Command.sectionHeader
  parseHasKind "attribute [local simp] Nat.add_zero" ``Lean.Parser.Term.attrInstance
  parseHasKind "deriving instance BEq for Nat" ``Lean.Parser.Command.derivingClass
  parseHasKind "set_option maxHeartbeats 100 in def f := 1" ``Lean.Parser.Command.set_option
  parseHasKind "def f := set_option maxHeartbeats 100 in 1" ``Lean.Parser.Term.set_option
  parseHasKind "theorem t : 1 = 1 := by decide +native" `Lean.Parser.Tactic.decide
  parseHasKind "def q := `(1 + 2)" `Lean.Parser.Term.quot
  parseHasKind "def dq := `(term| 1 + 2)" `Lean.Parser.Term.dynamicQuot
  parseHasKind "def x := (#[] : Array Nat)[0]!" `«term__[_]_!»
  parseHasKind "def x : Nat := Id.run do\n  let mut i := 1\n  while i > 0 do i := i - 1\n  return i" `Lean.Parser.Term.doWhile
  parseHasKind "def x : Nat := Id.run do\n  repeat break\n  return 0" `Lean.Parser.Term.doRepeat
  parseHasKind "def x : Nat := Id.run do\n  let mut i := 0\n  repeat i := i + 1 until i > 0\n  return i" `Lean.Parser.Term.doRepeatUntil
  let raw ← IO.FS.readFile (System.FilePath.mk {:?})
  let j ← IO.ofExcept (Lean.Json.parse raw)
  let cases ← IO.ofExcept (Lean.fromJson? (α := Array (Array String)) j)
  let rootScope : TrustedBoundary.ParseScope :=
    {{ header := "", currNamespace := .anonymous, openDecls := [] }}
  for row in cases do
    let #[label, body, want] := row
      | throw <| IO.userError "malformed test vector row"
    let ctx := Lean.Parser.mkInputContext body label
    let ok ← try
      TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
        [rootScope] `Spec {{}} {{}}
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: expected {{want}} in {{msg}}"
      pure true
    unless ok do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
  -- Non-`module` specs reject `@[expose]` attributes and section modifiers.
  for (label, body, want) in #[
      ("nonmod-expose-def", "@[expose] def Spec.e : Nat := 0\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n", "unsupported attribute"),
      ("nonmod-expose-sec", "@[expose] section S\nend S\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n", "unsupported section/namespace modifier")
    ] do
    let ctx := Lean.Parser.mkInputContext body label
    let rejected ← try
      TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
        [rootScope] `Spec {{}} {{}} false
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: expected {{want}} in {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
  -- `module`-mode (`isModule := true`) admits `public`, `@[expose]`,
  -- `@[expose] public section`, and `public noncomputable section`, while
  -- rejecting `meta`, `@[local expose]`, and `attribute [-expose]`.
  let modOk := #[
    "@[expose] public section\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\nend\n",
    "public noncomputable section S\ndef Spec.ncHelper : Nat := 0\nend S\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    "@[expose] public def Spec.helper (n : Nat) : Nat := n\npublic theorem Spec.thm : True := trivial\nprivate theorem Spec.privThm : True := trivial\npublic section\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\nend\n"
  ]
  for body in modOk do
    let ctx := Lean.Parser.mkInputContext body "mod-ok"
    TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
      [rootScope] `Spec {{}} {{}} true
  for (label, body, want) in #[
      ("mod-meta-sec", "meta section S\nend S\n", "unsupported section/namespace modifier"),
      ("mod-public-meta-sec", "public meta section S\nend S\n", "unsupported section/namespace modifier"),
      ("mod-meta-def", "meta def Spec.m : Nat := 0\n", "unsupported declaration modifier"),
      ("mod-public-meta-def", "public meta def Spec.m : Nat := 0\n", "unsupported declaration modifier"),
      ("mod-local-expose", "@[local expose] public def f : Nat := 0\n", "unsupported attribute"),
      ("mod-erase-expose", "attribute [-expose] Nat.add\n", "unsupported attribute removal")
    ] do
    let ctx := Lean.Parser.mkInputContext body label
    let rejected ← try
      TrustedBoundary.parseAndInspectSpecCommands ctx cmdKinds tacKinds env
        [rootScope] `Spec {{}} {{}} true
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: expected {{want}} in {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
"#,
        adm.prefix.to_string_lossy(),
        vectors_json_path.to_string_lossy()
    ));
    let probe = checker.stage().join("SpecPreflightRoundTrip.lean");
    fs::write(&probe, source).unwrap();
    checker
        .process(
            "spec-preflight-roundtrip",
            &[probe.to_string_lossy().into_owned()],
        )
        .unwrap();

    // 2. End-to-end `run_target` and sandboxed wire-protocol
    //    `inspect_spec_preflight` checks proving `"spec-preflight"` halts with
    //    exit code 1 inside `ExecSeal` BEFORE any target compilation.
    for (label, snippet, expected) in [
        ("e2e-eval", "#eval 1\n", "unsupported command"),
        (
            "e2e-include-str",
            "def s := include_str \"foo\"\n",
            "disallowed syntax Lean.includeStr",
        ),
    ] {
        let mut e2e_f = Fixture::new(
            "import Expected\n\
             theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
        );
        e2e_f.set(
            "Spec",
            TargetRole::Specification,
            &format!("import Model\n{snippet}{spec_base}"),
        );
        let mut c = e2e_f.cargo_checker();
        c.set_allow_unpinned_lean(true);
        let err = c.run_target(&e2e_f.request).unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }

    let mut base_fixture = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    let mut unpinned = base_fixture.cargo_checker();
    unpinned.set_allow_unpinned_lean(true);
    base_fixture.set(
        "Spec",
        TargetRole::Specification,
        &format!("import Model\n{spec_base}"),
    );
    unpinned.run_target(&base_fixture.request).unwrap();

    let wire_samples = [
        "ns-init",
        "ns-internal-uv",
        "decl-bare-nat",
        "axiom-decl",
        "partial-def",
        "unsafe-rec-ident",
        "open-platform-target",
        "attr-impl-by",
        "deriving-unknown",
        "tactic-decide-native",
        "term-quot",
        "auto-param-exploit",
        "scoped-instance",
        "cmd-in-opt-auto-implicit-true",
        "term-get-elem-bang",
        "ident-list-head-bang",
        "ident-option-get-bang",
        "do-while",
    ];
    for (idx, (label, snippet, expected)) in vectors
        .iter()
        .filter(|(label, _, _)| wire_samples.contains(label))
        .enumerate()
    {
        let path = base_fixture.root.join(format!("neg_spec_{idx:03}.lean"));
        fs::write(&path, format!("import Model\n{snippet}{spec_base}")).unwrap();
        let err = unpinned
            .inspect_spec_preflight(&[("Spec".to_owned(), path)])
            .unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "{label}: {err}");
        assert!(
            err.message.contains(expected),
            "{label}: expected {expected:?} in {err}"
        );
    }

    // 3. `SpecPreflight.lean`'s `"spec-preflight"`, which serves the NDJSON
    //    comparator route, admits the base specification during `run_target`
    //    and rejects every wire sample with the same reason on the pinned
    //    toolchain.
    with_spec_preflight(&base_fixture);
    let mut via_sp = base_fixture.cargo_checker();
    via_sp.set_allow_unpinned_lean(true);
    via_sp.set_spec_preflight_mode_via_spec_preflight(true);
    via_sp.run_target(&base_fixture.request).unwrap();
    assert!(
        via_sp.stage().join("control/SpecPreflight.olean").is_file(),
        "`\"spec-preflight\"` did not run SpecPreflight.lean"
    );
    for (idx, (label, snippet, expected)) in
        vectors.iter().filter(|(label, _, _)| wire_samples.contains(label)).enumerate()
    {
        let path = base_fixture.root.join(format!("neg_spec_sp_{idx:03}.lean"));
        fs::write(&path, format!("import Model\n{snippet}{spec_base}")).unwrap();
        let err = via_sp.inspect_spec_preflight(&[("Spec".to_owned(), path)]).unwrap_err();
        assert_eq!(err.code, 1, "SpecPreflight {label}: {err}");
        assert_eq!(err.phase, "spec-preflight", "SpecPreflight {label}: {err}");
        assert!(
            err.message.contains(expected),
            "SpecPreflight {label}: expected {expected:?} in {err}"
        );
    }
}
