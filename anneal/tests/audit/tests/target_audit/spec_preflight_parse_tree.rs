// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specification preflight parse-tree round trips and negative guards.

use super::*;

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
    let vectors: &[(&str, &str, &str)] = &[
        ("eval-cmd", "#eval 1\n", "unsupported command"),
        (
            "axiom-decl",
            "axiom badAx : True\n",
            "unsupported declaration kind",
        ),
        (
            "opaque-decl",
            "opaque badOp : Nat := 0\n",
            "unsupported declaration kind",
        ),
        (
            "example-decl",
            "example : True := trivial\n",
            "unsupported declaration kind",
        ),
        (
            "macro-cmd",
            "macro \"m\" : term => `(0)\n",
            "unsupported command",
        ),
        (
            "syntax-cmd",
            "syntax \"mykw\" : term\n",
            "unsupported command",
        ),
        ("init-cmd", "initialize pure ()\n", "unsupported command"),
        (
            "notation-cmd",
            "notation \"x99\" => 1\n",
            "unsupported command",
        ),
        (
            "in-bad-lhs",
            "namespace N in def f : Nat := 0\n",
            "unsupported command on LHS of `in`",
        ),
        (
            "in-bad-rhs",
            "open Nat in namespace N\n",
            "unsupported command inside `in`",
        ),
        (
            "mutual-nested-sec",
            "mutual\nsection S\nend S\nend\n",
            "unsupported mutual-block shape",
        ),
        (
            "partial-def",
            "partial def p (n : Nat) : Nat := p n\n",
            "unsupported declaration modifier",
        ),
        (
            "unsafe-def",
            "unsafe def u : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "meta-def",
            "meta def m : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "public-def",
            "public def pub : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "term-unsafe",
            "def u2 : Nat := unsafe 0\n",
            "disallowed modifier",
        ),
        (
            "public-section",
            "public section S\nend S\n",
            "unsupported section/namespace modifier",
        ),
        (
            "meta-section",
            "meta section S\nend S\n",
            "unsupported section/namespace modifier",
        ),
        (
            "partial-fixpoint",
            "def pf (n : Nat) : Nat := pf n\npartial_fixpoint\n",
            "disallowed modifier",
        ),
        (
            "unsafe-rec-ident",
            "def foo._unsafe_rec : Nat := 0\n",
            "_unsafe_rec",
        ),
        ("open-io", "open IO\n", "forbidden namespace IO"),
        ("open-lean", "open Lean\n", "forbidden namespace Lean"),
        ("open-lake", "open Lake\n", "forbidden namespace Lake"),
        ("open-system", "open System\n", "forbidden namespace System"),
        (
            "open-platform-all",
            "open System.Platform\n",
            "forbidden namespace System.Platform",
        ),
        (
            "open-platform-target",
            "open System.Platform (target)\n",
            "disallowed open item System.Platform.target",
        ),
        (
            "open-platform-hiding",
            "open System.Platform hiding target\n",
            "forbidden namespace System.Platform",
        ),
        (
            "open-scoped-io",
            "open scoped IO\n",
            "forbidden namespace IO",
        ),
        ("ns-io", "namespace IO\nend IO\n", "disallowed reference IO"),
        (
            "term-open-io",
            "def x : Nat := open IO in 0\n",
            "forbidden namespace IO",
        ),
        (
            "export-platform-target",
            "export System.Platform (target)\n",
            "disallowed export item System.Platform.target",
        ),
        (
            "ref-io",
            "def x := IO.println\n",
            "disallowed reference IO.println",
        ),
        (
            "ref-platform-target",
            "def x := System.Platform.target\n",
            "disallowed reference System.Platform.target",
        ),
        (
            "attr-impl-by",
            "@[implemented_by Nat.add] def f := Nat.add\n",
            "unsupported attribute implemented_by",
        ),
        (
            "attr-extern",
            "@[extern \"c_fn\"] def f (x : Nat) : Nat := x\n",
            "unsupported attribute kind",
        ),
        (
            "attr-csimp",
            "@[csimp] theorem t : Nat.add = Nat.add := rfl\n",
            "unsupported attribute csimp",
        ),
        (
            "attr-scoped-simp",
            "@[scoped simp] theorem t : True := trivial\n",
            "only global or local attributes",
        ),
        (
            "attr-erase-extern",
            "attribute [-extern] Nat.add\n",
            "unsupported attribute removal extern",
        ),
        (
            "deriving-unknown",
            "structure S where\n  x : Nat\nderiving UnknownClass\n",
            "unsupported deriving class",
        ),
        (
            "opt-skip-kernel",
            "set_option debug.skipKernelTC true\n",
            "unsupported option debug.skipKernelTC",
        ),
        (
            "opt-non-num",
            "set_option maxHeartbeats true\n",
            "requires a numeric literal",
        ),
        (
            "opt-non-bool",
            "set_option linter.unusedVariables 1\n",
            "requires a boolean literal",
        ),
        (
            "term-opt-bad",
            "def x : Nat := set_option debug.skipKernelTC true in 0\n",
            "unsupported option debug.skipKernelTC",
        ),
        (
            "tactic-sorry",
            "theorem t : True := by sorry\n",
            "unsupported tactic",
        ),
        (
            "tactic-admit",
            "theorem t : True := by admit\n",
            "unsupported tactic",
        ),
        (
            "tactic-native-decide",
            "theorem t : 1 = 1 := by native_decide\n",
            "unsupported tactic",
        ),
        (
            "tactic-decide-native",
            "theorem t : 1 = 1 := by decide +native\n",
            "unsupported decide config option native",
        ),
        (
            "tactic-decide-valcfg",
            "theorem t : 1 = 1 := by decide (config := { native := true })\n",
            "unsupported decide config",
        ),
        (
            "tactic-bv-decide",
            "theorem t : true = true := by bv_decide\n",
            "unsupported tactic",
        ),
        (
            "tactic-grind",
            "theorem t : 1 = 1 := by grind\n",
            "unsupported tactic",
        ),
        (
            "tactic-rfl-prime",
            "theorem t : 1 = 1 := by rfl'\n",
            "unsupported tactic",
        ),
        (
            "tactic-run-tac",
            "theorem t : True := by run_tac pure ()\n",
            "unsupported tactic",
        ),
        (
            "tactic-open",
            "theorem t : True := by open Nat in trivial\n",
            "unsupported tactic",
        ),
        (
            "tactic-set-option",
            "theorem t : True := by set_option maxHeartbeats 1 in trivial\n",
            "unsupported tactic",
        ),
        (
            "tactic-conv",
            "theorem t : 1 = 1 := by conv => rfl\n",
            "unsupported tactic",
        ),
        (
            "term-include-str",
            "def s := include_str \"foo\"\n",
            "disallowed syntax Lean.includeStr",
        ),
        (
            "term-by-elab",
            "def e : Nat := by_elab return 0\n",
            "disallowed syntax Lean.byElab",
        ),
        (
            "term-sorry",
            "def s : Nat := sorry\n",
            "disallowed syntax Lean.Parser.Term.sorry",
        ),
        (
            "term-dbg-trace",
            "def d : Nat := dbg_trace \"hi\"; 0\n",
            "disallowed syntax Lean.Parser.Term.dbgTrace",
        ),
        (
            "term-decl-name",
            "def f := decl_name%\n",
            "disallowed syntax Lean.Parser.Term.declName",
        ),
        (
            "term-quot",
            "def q := `(1 + 2)\n",
            "disallowed syntax Lean.Parser.Term.quot",
        ),
        (
            "term-dyn-quot",
            "def dq := `(term| 1 + 2)\n",
            "disallowed syntax Lean.Parser.Term.dynamicQuot",
        ),
        (
            "auto-param-exploit",
            "universe u\n\
             def idAt {α : Sort u} (_f : α → Prop) (a : α) : α := a\n\
             def myTac := idAt (fun s => autoParam True s)\n\
               (.node .none `Lean.Parser.Tactic.tacticSeq #[\n\
                 .node .none `Lean.Parser.Tactic.tacticSeq1Indented #[\n\
                   .node .none `null #[\n\
                     .node .none `Lean.Parser.Tactic.tacticSorry #[.atom .none \"sorry\"]]]])\n\
             theorem evil (h : autoParam False myTac) : False := h\n",
            "disallowed identifier autoParam",
        ),
        (
            "quoted-name",
            "def qn := `foo\n",
            "disallowed syntax Lean.Parser.Term.quotedName",
        ),
        (
            "double-quoted-name",
            "def dqn := ``Nat.add\n",
            "disallowed syntax Lean.Parser.Term.doubleQuotedName",
        ),
        (
            "binder-tactic",
            "def half (n : Nat) (h : n > 0 := by omega) : Nat := n / 2\n",
            "disallowed syntax Lean.Parser.Term.binderTactic",
        ),
        (
            "scoped-instance",
            "namespace N\nscoped instance : Inhabited Unit := ⟨()⟩\nend N\n",
            "disallowed modifier Lean.Parser.Term.scoped",
        ),
        (
            "term-mod-cast",
            "theorem mc (n : Nat) : (n : Int) = (n : Int) := mod_cast (rfl : n = n)\n",
            "disallowed syntax Lean.modCast",
        ),
        (
            "term-panic",
            "def p : Nat := panic! \"boom\"\n",
            "disallowed syntax Lean.Parser.Term.panic",
        ),
        (
            "term-unreachable",
            "def u : Nat := unreachable!\n",
            "disallowed syntax Lean.Parser.Term.unreachable",
        ),
        (
            "term-assert",
            "def a : Nat := assert! true; 0\n",
            "disallowed syntax Lean.Parser.Term.assert",
        ),
        (
            "term-debug-assert",
            "def da : Nat := debug_assert! true; 0\n",
            "disallowed syntax Lean.Parser.Term.debugAssert",
        ),
        (
            "direct-panic-core",
            "def pc : Nat := panicCore \"boom\"\n",
            "disallowed identifier panicCore",
        ),
        (
            "contract-decl-val",
            "def contracted (n : Nat) : Nat\n\
             requires True\n\
             ensures _ => True\n\
             := n\n",
            "disallowed syntax Lean.Parser.Command.contractDeclVal",
        ),
        (
            "term-qed-try",
            "theorem t : True := ∎\n",
            "disallowed syntax «term∎»",
        ),
        (
            "opt-auto-implicit-true",
            "set_option autoImplicit true\n",
            "unsupported option autoImplicit",
        ),
        (
            "opt-auto-implicit-false",
            "set_option autoImplicit false\n",
            "unsupported option autoImplicit",
        ),
        (
            "opt-relaxed-auto-implicit-true",
            "set_option relaxedAutoImplicit true\n",
            "unsupported option relaxedAutoImplicit",
        ),
        (
            "term-opt-auto-implicit-true",
            "def x : Nat := set_option autoImplicit true in 0\n",
            "unsupported option autoImplicit",
        ),
        (
            "cmd-in-opt-auto-implicit-true",
            "set_option autoImplicit true in\ndef x (n : Nat) : pre_ok → True := fun _ => trivial\n",
            "unsupported option autoImplicit",
        ),
        (
            "term-get-elem-bang",
            "def x : Nat := (#[] : Array Nat)[0]!\n",
            "disallowed syntax «term__[_]_!»",
        ),
        (
            "ident-list-head-bang",
            "def x : Nat := ([] : List Nat).head!\n",
            "disallowed identifier head!",
        ),
        (
            "ident-option-get-bang",
            "def x : Nat := (none : Option Nat).get!\n",
            "disallowed identifier get!",
        ),
        (
            "ident-get-elem-bang-qual",
            "def x : Nat := GetElem?.getElem! (#[] : Array Nat) 0\n",
            "disallowed identifier GetElem?.getElem!",
        ),
        (
            "ident-out-of-bounds",
            "def x : Nat := outOfBounds\n",
            "disallowed identifier outOfBounds",
        ),
        (
            "ident-pos-slice-or-panic",
            "def x := @String.Pos.sliceOrPanic\n",
            "disallowed identifier String.Pos.sliceOrPanic",
        ),
        (
            "ident-slice-pos-slice-or-panic",
            "def x := @String.Slice.Pos.sliceOrPanic\n",
            "disallowed identifier String.Slice.Pos.sliceOrPanic",
        ),
        (
            "proj-slice-or-panic",
            "def x (s : String) (pos : s.Pos) (h : pos ≤ pos) := pos.sliceOrPanic pos pos (h := h)\n",
            "disallowed identifier pos.sliceOrPanic",
        ),
        (
            "open-only-head-bang",
            "open List (head!)\n",
            "invalid open item head!",
        ),
        (
            "export-head-bang",
            "export List (head!)\n",
            "invalid export item head!",
        ),
        (
            "open-renaming-head-bang",
            "open List renaming head! -> safeHead\n",
            "invalid open renaming item head! -> safeHead",
        ),
        (
            "open-renaming-slice-or-panic",
            "open String.Slice renaming Pos.sliceOrPanic -> safeSlice\n",
            "invalid open renaming item Pos.sliceOrPanic -> safeSlice",
        ),
        (
            "do-while",
            "def x : Nat := Id.run do\n  let mut i := 5\n  while i > 0 do\n    i := i - 1\n  return i\n",
            "disallowed syntax Lean.Parser.Term.doWhile",
        ),
        (
            "do-repeat",
            "def x : Nat := Id.run do\n  repeat\n    break\n  return 0\n",
            "disallowed syntax Lean.Parser.Term.doRepeat",
        ),
        (
            "do-repeat-until",
            "def x : Nat := Id.run do\n  let mut i := 0\n  repeat\n    i := i + 1\n  until i > 0\n  return i\n",
            "disallowed syntax Lean.Parser.Term.doRepeatUntil",
        ),
        (
            "ident-repeat-m",
            "def x := repeatM\n",
            "disallowed identifier repeatM",
        ),
        // Declaration-namespace guards: entering or declaring under the
        // `Trusted`/`Anneal`/`Proof` roots, every `reservedKernelRoots` root
        // (including `Init` and `Std`), and the `forbiddenSysUvPrefixes`
        // sub-scopes (which an earlier reference guard may reject first),
        // with `_root_` stripped.
        (
            "ns-trusted",
            "namespace Trusted\nend Trusted\n",
            "cannot enter reserved namespace Trusted",
        ),
        (
            "ns-anneal",
            "namespace Anneal\nend Anneal\n",
            "cannot enter reserved namespace Anneal",
        ),
        (
            "ns-proof",
            "namespace Proof\nend Proof\n",
            "cannot enter reserved namespace Proof",
        ),
        (
            "ns-nat",
            "namespace Nat\nend Nat\n",
            "cannot enter reserved namespace Nat",
        ),
        (
            "ns-init",
            "namespace Init\nend Init\n",
            "cannot enter reserved namespace Init",
        ),
        (
            "ns-std",
            "namespace Std\nend Std\n",
            "cannot enter reserved namespace Std",
        ),
        (
            "ns-internal-uv",
            "namespace Internal.UV\nend Internal.UV\n",
            "Internal.UV",
        ),
        (
            "ns-dynlib",
            "namespace Dynlib\nend Dynlib\n",
            "Dynlib",
        ),
        (
            "ns-root-trusted",
            "namespace _root_.Trusted\nend _root_.Trusted\n",
            "_root_.Trusted",
        ),
        (
            "decl-bare-nat",
            "def Nat : Nat := 0\n",
            "cannot declare reserved namespace Nat",
        ),
        (
            "decl-in-std",
            "def Std.evil : Nat := 0\n",
            "cannot declare in reserved namespace Std",
        ),
        (
            "decl-in-internal-uv",
            "def Internal.UV.evil : Nat := 0\n",
            "Internal.UV",
        ),
    ];

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
