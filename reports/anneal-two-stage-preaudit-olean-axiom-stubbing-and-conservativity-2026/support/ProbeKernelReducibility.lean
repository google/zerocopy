-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Empirical Probe of Lean 4.34.1 Elaborator vs. C++ Kernel Reducibility

This executable probe inspects how Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`)
represents and reduces declarations across the elaborator (`MetaM` /
`ReducibilityStatus`) and the C++ kernel (`Kernel.Environment`, `Kernel.whnf`,
`Kernel.isDefEq`):

1. `def` (`ReducibilityStatus.semireducible`, `ReducibilityHints.regular h`)
2. `@[irreducible] def` (`ReducibilityStatus.irreducible`,
   `ReducibilityHints.regular h` — proving `@[irreducible]` never alters kernel
   `DefinitionVal.hints`)
3. `@[reducible] def` vs. `abbrev` (`ReducibilityHints.regular h` vs.
   `ReducibilityHints.abbrev`)
4. Kernel `.defnInfo` with explicit `ReducibilityHints.opaque` (proving that
   even `ReducibilityHints.opaque` on a `.defnInfo` is STILL unfolded by C++
   `type_checker::whnf` and `type_checker::lazy_delta_reduction_step`)
5. `opaque` (`.opaqueInfo` — hard opacity wall in the C++ kernel)
6. `theorem` (`.thmInfo` — proof-irrelevance short-circuit at
   `type_checker.cpp:1202` before `lazy_delta_reduction` at line 1206, plus
   direct probe of `Kernel.whnf` exposing `constant_info::has_value(false)` in
   `src/kernel/declaration.h:467`).
-/

open Lean Meta

namespace Anneal.ProbeKernelReducibility

/-- 1. Standard semireducible definition. -/
def regularDef : Nat := 21 + 21

/-- 2. `@[irreducible]` definition: updates `reducibilityCoreExt` in the
    elaborator after `addDecl`, leaving kernel `DefinitionVal.hints` as
    `.regular`. -/
@[irreducible] def irredDef : Nat := 21 + 21

/-- 3. `@[reducible]` definition vs. `abbrev`. -/
@[reducible] def redAttrDef : Nat := 21 + 21
abbrev abbrevDef : Nat := 21 + 21

/-- 4. `opaque` declaration: produces `.opaqueInfo` in the kernel. -/
opaque opaqueDef : Nat := 21 + 21

/-- 5. `theorem` declaration: produces `.thmInfo` in the kernel. -/
theorem thmDef : 21 + 21 = 42 := Eq.refl 42

/-- Format `ReducibilityHints` for diagnostic output. -/
def formatHints : ReducibilityHints → String
  | .opaque => "ReducibilityHints.opaque"
  | .abbrev => "ReducibilityHints.abbrev"
  | .regular h => s!"ReducibilityHints.regular (height := {h})"

/-- Format `ReducibilityStatus` for diagnostic output. -/
def formatStatus : ReducibilityStatus → String
  | .reducible => "ReducibilityStatus.reducible"
  | .semireducible => "ReducibilityStatus.semireducible"
  | .irreducible => "ReducibilityStatus.irreducible"
  | .implicitReducible => "ReducibilityStatus.implicitReducible"
  | .instanceReducible => "ReducibilityStatus.instanceReducible"

/-- Format `ConstantInfo` variant and kernel hints. -/
def describeConstant (env : Environment) (n : Name) : MetaM String := do
  let some ci := env.find? n | return s!"{n}: not found"
  let status ← getReducibilityStatus n
  let kindStr := match ci with
    | .defnInfo v => s!".defnInfo (hints := {formatHints v.hints}, safety := {repr v.safety})"
    | .thmInfo _ => ".thmInfo"
    | .opaqueInfo _ => ".opaqueInfo"
    | .axiomInfo _ => ".axiomInfo"
    | _ => "other"
  return s!"{n}: kernel={kindStr}, elabAttr={formatStatus status}, Lean.ConstantInfo.hasValue(false)={ci.hasValue false}, hasValue(true)={ci.hasValue true}"

/-- Symbolic-evaluator-like recursion with distinct state arguments at each step
    so `m_whnf_core` / `m_success` in `type_checker::state` cannot collapse
    subtrees. -/
def symEval : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => symEval n (acc + 1)

/-- Second symbolic-evaluator definition with identical step behavior. -/
def symEvalMirror : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => symEvalMirror n (acc + 1)

/-- Characterization theorem proved once in Stage 1 (`theory/Anneal/`):
    seals `symEval n acc = symEvalMirror n acc` inside `.thmInfo`. -/
theorem symEval_eq_mirror : ∀ n acc, symEval n acc = symEvalMirror n acc
  | 0, _ => rfl
  | n + 1, acc => symEval_eq_mirror n (acc + 1)

-- Seal both definitions with `@[irreducible]` after proving their Stage-1
-- characterization theorem. Notice that in `MetaM` their status becomes
-- `.irreducible`, whereas in the C++ kernel their `DefinitionVal.hints`
-- remain `ReducibilityHints.regular`!
attribute [irreducible] symEval symEvalMirror

def runProbes : MetaM Unit := do
  IO.println "=== [Probe 1] Elaborator Status vs. Kernel ConstantInfo & ReducibilityHints ==="
  let env ← getEnv
  for n in [``regularDef, ``irredDef, ``redAttrDef, ``abbrevDef, ``opaqueDef, ``thmDef, ``symEval] do
    IO.println (← describeConstant env n)

  -- Add two raw kernel `.defnInfo` declarations with explicit `hints := .opaque`
  -- to test `type_checker.cpp` on `.defnInfo` with `ReducibilityHints.opaque`.
  let opaqueHintDef1 : Name := `Anneal.ProbeKernelReducibility.opaqueHintDef1
  let opaqueHintDef2 : Name := `Anneal.ProbeKernelReducibility.opaqueHintDef2
  let decl1 := Declaration.defnDecl {
    name := opaqueHintDef1
    levelParams := []
    type := mkConst ``Nat
    value := mkApp2 (mkConst ``Nat.add) (mkNatLit 21) (mkNatLit 21)
    hints := .opaque
    safety := .safe
  }
  let decl2 := Declaration.defnDecl {
    name := opaqueHintDef2
    levelParams := []
    type := mkConst ``Nat
    value := mkApp2 (mkConst ``Nat.add) (mkNatLit 20) (mkNatLit 22)
    hints := .opaque
    safety := .safe
  }
  let env1 ← ofExceptKernelException (env.addDeclCore 0 0 decl1 none)
  let env2 ← ofExceptKernelException (env1.addDeclCore 0 0 decl2 none)
  setEnv env2
  IO.println (← describeConstant env2 opaqueHintDef1)
  IO.println (← describeConstant env2 opaqueHintDef2)

  IO.println "\n=== [Probe 2] MetaM (Default Transparency) vs. C++ Kernel Unfolding ==="
  let lit42 := mkNatLit 42
  let metaIrredEq ← isDefEq (mkConst ``irredDef) lit42
  let metaIrredWhnf ← Meta.whnf (mkConst ``irredDef)
  let kernIrredWhnf :=
    match Kernel.whnf env2 {} (mkConst ``irredDef) with
    | .ok e => s!"{e}"
    | .error _ => "error"
  let kernIrredEq :=
    match Kernel.isDefEq env2 {} (mkConst ``irredDef) lit42 with
    | .ok b => s!"{b}"
    | .error _ => "error"
  IO.println s!"@[irreducible] irredDef == 42 in MetaM (default): {metaIrredEq} (Meta.whnf = {metaIrredWhnf})"
  IO.println s!"@[irreducible] irredDef == 42 in C++ Kernel:      {kernIrredEq} (Kernel.whnf = {kernIrredWhnf})"

  let kernOpaqueHintWhnf :=
    match Kernel.whnf env2 {} (mkConst opaqueHintDef1) with
    | .ok e => s!"{e}"
    | .error _ => "error"
  let kernOpaqueHintVsLit :=
    match Kernel.isDefEq env2 {} (mkConst opaqueHintDef1) lit42 with
    | .ok b => s!"{b}"
    | .error _ => "error"
  let kernOpaqueHintVsEachOther :=
    match Kernel.isDefEq env2 {} (mkConst opaqueHintDef1) (mkConst opaqueHintDef2) with
    | .ok b => s!"{b}"
    | .error _ => "error"
  IO.println s!".defnInfo (hints := .opaque) Kernel.whnf:                   {kernOpaqueHintWhnf}"
  IO.println s!".defnInfo (hints := .opaque) == 42 in C++ Kernel:           {kernOpaqueHintVsLit}"
  IO.println s!".defnInfo (hints := .opaque) #1 == #2 in C++ Kernel:        {kernOpaqueHintVsEachOther}"

  let kernOpaqueDeclWhnf :=
    match Kernel.whnf env2 {} (mkConst ``opaqueDef) with
    | .ok e => s!"{e}"
    | .error _ => "error"
  let kernOpaqueDeclEq :=
    match Kernel.isDefEq env2 {} (mkConst ``opaqueDef) lit42 with
    | .ok b => s!"{b}"
    | .error _ => "error"
  IO.println s!".opaqueInfo (opaque opaqueDef) Kernel.whnf:                 {kernOpaqueDeclWhnf}"
  IO.println s!".opaqueInfo (opaque opaqueDef) == 42 in C++ Kernel:         {kernOpaqueDeclEq}"

  -- Test `Kernel.whnf` on `.thmInfo` (`thmDef`), exposing C++
  -- `constant_info::has_value(false)` in `src/kernel/declaration.h:467`!
  let kernThmWhnf :=
    match Kernel.whnf env2 {} (mkConst ``thmDef) with
    | .ok e => s!"{e}"
    | .error _ => "error"
  IO.println s!".thmInfo (theorem thmDef) Kernel.whnf (C++ has_value=true): {kernThmWhnf}"

  -- Test `Kernel.isDefEq` between two distinct `.thmInfo` proofs of the same
  -- proposition: short-circuited in O(1) by `is_def_eq_proof_irrel`
  -- (`type_checker.cpp:1202`) BEFORE `lazy_delta_reduction` (line 1206).
  let kernThmProofIrrel :=
    match Kernel.isDefEq env2 {} (mkConst ``thmDef) (← mkEqRefl lit42) with
    | .ok b => s!"{b}"
    | .error _ => "error"
  IO.println s!".thmInfo proof-irrelevance short-circuit in Kernel.isDefEq: {kernThmProofIrrel}"

  IO.println "\n=== [Probe 3] Kernel Timing: Unfolding @[irreducible] def vs. .thmInfo Short-Circuit ==="
  for fuel in [200, 500, 1000, 2000] do
    let lhs := mkApp2 (mkConst ``symEval) (mkNatLit fuel) (mkNatLit 0)
    let rhs := mkApp2 (mkConst ``symEvalMirror) (mkNatLit fuel) (mkNatLit 0)
    let eqType ← mkEq lhs rhs

    let reflDecl := Declaration.thmDecl {
      name := Name.mkSimple s!"slowReflProof_{fuel}"
      levelParams := []
      type := eqType
      value := ← mkEqRefl lhs
    }
    let t0 ← IO.monoNanosNow
    let _ ← ofExceptKernelException (env2.addDeclCore 0 0 reflDecl none)
    let t1 ← IO.monoNanosNow
    let reflUs := (t1 - t0) / 1000

    let thmAppDecl := Declaration.thmDecl {
      name := Name.mkSimple s!"fastThmProof_{fuel}"
      levelParams := []
      type := eqType
      value := mkApp2 (mkConst ``symEval_eq_mirror) (mkNatLit fuel) (mkNatLit 0)
    }
    let t2 ← IO.monoNanosNow
    let _ ← ofExceptKernelException (env2.addDeclCore 0 0 thmAppDecl none)
    let t3 ← IO.monoNanosNow
    let thmAppUs := (t3 - t2) / 1000

    IO.println s!"fuel={fuel}: @[irreducible] Eq.refl={reflUs} us vs. .thmInfo app={thmAppUs} us (speedup={reflUs / (max 1 thmAppUs)}x)"

#eval runProbes

end Anneal.ProbeKernelReducibility
