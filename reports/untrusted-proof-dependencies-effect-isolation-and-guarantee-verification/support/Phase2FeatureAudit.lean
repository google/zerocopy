-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay

open Lean

namespace Phase2FeatureAudit

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "defn"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

def safetyStr : ConstantInfo → String
  | .defnInfo v => match v.safety with
    | .unsafe  => "unsafe"
    | .safe    => "safe"
    | .partial => "partial"
  | ci => if ci.isUnsafe then "unsafe" else if ci.isPartial then "partial" else "safe"

/-- Phase 2 `validateLocalConstant` from `TrustedBoundary.lean:644-664` for `.theory` role. -/
def checkStrictPhase2 (ci : ConstantInfo) : Option String :=
  if (privateToUserName ci.name).getRoot == `Trusted then
    some s!"Trusted namespace violation: {ci.name}"
  else if ci matches .opaqueInfo _ then
    some s!"opaqueInfo not allowed in theory: {ci.name}"
  else if ci.isUnsafe || ci.isPartial then
    some s!"isUnsafe={ci.isUnsafe} / isPartial={ci.isPartial}: {ci.name}"
  else if ci.isAxiom then
    some s!"axiomInfo: {ci.name}"
  else if ci matches .quotInfo _ then
    some s!"quotInfo: {ci.name}"
  else if ci.hasValue true && (ci.value? true).isNone then
    some s!"missing body: {ci.name}"
  else
    none

/-- Phase 2 `validateLocalConstant` with the `Compiler.isUnsafeRecName?` companion check
    allowing equation-compiler-generated `<base>._unsafe_rec` only when `<base>` is a
    local `.defnInfo` with `safety == .safe`. -/
def checkRelaxedPhase2 (stage2Map : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : Option String :=
  if (privateToUserName ci.name).getRoot == `Trusted then
    some s!"Trusted namespace violation: {ci.name}"
  else if ci matches .opaqueInfo _ then
    some s!"opaqueInfo not allowed in theory: {ci.name}"
  else if ci.isUnsafe then
    some s!"isUnsafe=true: {ci.name}"
  else if ci.isPartial then
    match Compiler.isUnsafeRecName? ci.name with
    | some baseName =>
      match stage2Map.get? baseName with
      | some (.defnInfo baseVal) =>
        if baseVal.safety == .safe then none
        else some s!"_unsafe_rec base {baseName} is not .safe"
      | _ => some s!"_unsafe_rec without safe local defnInfo base {baseName}: {ci.name}"
    | none => some s!"isPartial=true (non-_unsafe_rec): {ci.name}"
  else if ci.isAxiom then
    some s!"axiomInfo: {ci.name}"
  else if ci matches .quotInfo _ then
    some s!"quotInfo: {ci.name}"
  else if ci.hasValue true && (ci.value? true).isNone then
    some s!"missing body: {ci.name}"
  else
    none

structure FeatureSpecimen where
  name   : String
  source : String

def foundationHeader : String :=
  "prelude\nimport Init.Prelude\nimport Init.Core\nimport Init.Notation\nimport Init.NotationExtra\nimport Init.Tactics\nimport Init.Ext\nimport Init.ByCases\nimport Init.Classical\nimport Init.Conv\nimport Init.WF\nimport Init.WFTactics\nimport Init.Control.Do\nimport Init.Control.Id\nimport Init.Data.Repr\nimport Init.Data.ToString.Basic\nimport Init.Data.Nat.Basic\nimport Init.Data.List.Basic\nimport Init.Data.List.Notation\nimport Init.SimpLemmas\n"

def specimens : Array FeatureSpecimen := #[
  { name := "macro_and_syntax_foundation_only",
    source := foundationHeader ++ "syntax \"my_tac\" : tactic\nmacro_rules | `(tactic| my_tac) => `(tactic| rfl)\nmacro \"my_rfl\" : tactic => `(tactic| rfl)\ntheorem t_macro : 1 = 1 := by my_rfl\ntheorem t_syn : 2 = 2 := by my_tac\n" },
  { name := "elab_tactic_requires_lean",
    source := "import Lean\nelab \"my_elab\" : tactic => do\n  let stx ← `(tactic| rfl)\n  Lean.Elab.Tactic.evalTactic stx\ntheorem t_elab : 1 = 1 := by my_elab\n" },
  { name := "notation_infix_foundation_only",
    source := foundationHeader ++ "notation \"Nat0\" => Nat\ninfixl:65 \" +++ \" => Nat.add\ntheorem t_not (x : Nat0) : x +++ 0 = x := Nat.add_zero x\n" },
  { name := "set_option_example_open_section_foundation_only",
    source := foundationHeader ++ "open Nat (add)\nopen Nat renaming mul -> times\nnoncomputable section\nset_option maxHeartbeats 400000 in\nexample : add 1 0 = 1 := rfl\ntheorem t_opt : (set_option pp.all true in times 1 1) = 1 := rfl\nend\n" },
  { name := "deriving_nonrec_inductive_foundation_only",
    source := foundationHeader ++ "inductive Color where | r | g | b deriving DecidableEq, BEq, Repr\ntheorem t_color : (Color.r == Color.r) = true := rfl\n" },
  { name := "deriving_rec_inductive_foundation_only",
    source := foundationHeader ++ "inductive Tree where | leaf | node (l r : Tree) deriving DecidableEq, BEq, Repr\n" },
  { name := "termination_by_decreasing_by_foundation_only",
    source := foundationHeader ++ "def countDown (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | k + 1 => countDown k\ntermination_by n\ndecreasing_by simp_wf\n" },
  { name := "noncomputable_termination_by_foundation_only",
    source := foundationHeader ++ "noncomputable def countDownNC (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | k + 1 => countDownNC k\ntermination_by n\ndecreasing_by simp_wf\n" },
  { name := "partial_def_rejected_even_under_relaxed_phase2",
    source := foundationHeader ++ "partial def diverge (n : Nat) : Nat := diverge (n + 1)\n" },
  { name := "omega_and_grind_requires_init_omega_grind",
    source := "import Init.Omega\nimport Init.Grind\ntheorem t_omega (x : Nat) : x + 1 > x := by omega\ntheorem t_grind (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y := by grind\n" },
  { name := "tactics_suite_foundation_only",
    source := foundationHeader ++ "theorem t_tacs (f g : Nat → Nat) (hfg : ∀ x, f x = g x) (x y : Nat) (hxy : x = y) (p : Prop) (hp : p) (b : Bool) :\n    f x = f y ∧ (if b then 1 else 1) = 1 ∧ f = g ∧ (1 + 1 = 2) := by\n  have hex : ∃ z : Nat, z = 0 := ⟨0, rfl⟩\n  obtain ⟨z, hz⟩ := hex\n  refine ⟨?_, ?_, ?_, ?_⟩\n  · congr 1\n  · split <;> rfl\n  · ext w; rename_i _ _; by_cases h : p\n    · simp_all\n    · contradiction\n  · decide +kernel\n" },
  { name := "rcases_and_sinterp_requires_init_rcases_string",
    source := "import Init.RCases\nimport Init.Data.String.Basic\ntheorem t_rcases (p q : Prop) (h : p ∧ q) : q ∧ p := by\n  rcases h with ⟨hp, hq⟩\n  exact ⟨hq, hp⟩\ndef greet (n : Nat) : String := s!\"hello {n}\"\n" },
  { name := "calc_and_conv_foundation_only",
    source := foundationHeader ++ "theorem t_calc_conv (a b : Nat) (h : a = b) : a + 0 = b := by\n  conv => lhs; rw [Nat.add_zero]\n  calc a = b := h\n" },
  { name := "do_notation_if_let_where_foundation_only",
    source := foundationHeader ++ "def helper (o : Option Nat) : Nat := Id.run do\n  let mut acc := 0\n  if let some x := o then\n    acc := addOne x\n  return acc\nwhere\n  addOne (y : Nat) : Nat := y + 1\ntheorem t_helper : helper (some 4) = 5 := rfl\n" },
  { name := "local_scoped_attrs_and_root_foundation_only",
    source := foundationHeader ++ "@[inline] def myId (x : _root_.Nat) : _root_.Nat := x\nattribute [local simp] myId\n@[simp high] theorem myId_eq (x : Nat) : myId x = x := rfl\n" }
]

unsafe def runSpecimen (s : FeatureSpecimen) : IO Json := do
  let inputCtx := Parser.mkInputContext s.source s!"<{s.name}>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  enableInitializersExecution
  let (env, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 0)
  let cmdState := Elab.Command.mkState env messages {}
  let ioState ← Elab.IO.processCommands inputCtx parserState cmdState
  let finalEnv := ioState.commandState.env
  let finalMsgs := ioState.commandState.messages
  let hasErr := finalMsgs.hasErrors
  let errStrs := (← finalMsgs.toList.filter (·.severity == .error) |>.mapM (·.data.toString)).toArray

  -- Collect Stage-2 constants (newly added by this module)
  let stage2 : Array (Name × ConstantInfo) :=
    finalEnv.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) #[]
  let stage2Map : Std.HashMap Name ConstantInfo :=
    stage2.foldl (init := {}) fun acc (n, ci) => acc.insert n ci

  let mut strictViolations : Array String := #[]
  let mut relaxedViolations : Array String := #[]
  let mut unsafeConsts : Array String := #[]
  let mut partialConsts : Array String := #[]
  let mut safeConsts : Array String := #[]
  for (n, ci) in stage2 do
    if let some v := checkStrictPhase2 ci then
      strictViolations := strictViolations.push v
    if let some v := checkRelaxedPhase2 stage2Map ci then
      relaxedViolations := relaxedViolations.push v
    if ci.isUnsafe then
      unsafeConsts := unsafeConsts.push s!"{n} ({kindStr ci})"
    else if ci.isPartial then
      partialConsts := partialConsts.push s!"{n} ({kindStr ci})"
    else
      safeConsts := safeConsts.push s!"{n} ({kindStr ci})"

  -- Check if replay of all `isCEnv` (`!isUnsafe && !isPartial`) constants succeeds on `env.toKernelEnv`
  let replayMap : Std.HashMap Name ConstantInfo :=
    stage2.foldl (init := {}) fun acc (n, ci) =>
      if !ci.isUnsafe && !ci.isPartial then acc.insert n ci else acc
  let replayResult ← try
    discard <| env.toKernelEnv.replay replayMap
    pure "OK"
  catch e =>
    pure s!"FAIL: {e.toString}"

  return Json.mkObj [
    ("specimen", toJson s.name),
    ("elabErrors", toJson errStrs),
    ("hasElabError", toJson hasErr),
    ("totalStage2Consts", toJson stage2.size),
    ("safeConstsCount", toJson safeConsts.size),
    ("safeConsts", toJson safeConsts),
    ("partialConsts", toJson partialConsts),
    ("unsafeConsts", toJson unsafeConsts),
    ("strictPhase2Violations", toJson strictViolations),
    ("relaxedPhase2Violations", toJson relaxedViolations),
    ("kernelReplayOfSafeConsts", toJson replayResult)
  ]

end Phase2FeatureAudit

unsafe def main : IO UInt32 := do
  let sysroot := ((← IO.appPath).parent >>= System.FilePath.parent).getD
    ((← Lean.findSysroot))
  initSearchPath sysroot
  let mut results : Array Json := #[]
  for s in Phase2FeatureAudit.specimens do
    let r ← Phase2FeatureAudit.runSpecimen s
    results := results.push r
  IO.println (Json.arr results).pretty
  return 0
