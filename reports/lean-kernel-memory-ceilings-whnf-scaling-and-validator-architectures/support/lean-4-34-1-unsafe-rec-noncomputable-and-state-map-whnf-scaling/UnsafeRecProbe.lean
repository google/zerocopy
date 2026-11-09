-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

open Lean Elab Command

/-!
# Empirical Probe for Cluster A1 (`UnsafeRecProbe.lean`)

Inspects:
1. `PreludeRecProbe.olean` (`ModuleData.constants`, `ModuleData.extraConstNames`,
   `isUnsafe`, `isPartial`, `Compiler.isUnsafeRecName?`, and `toKernelEnv.replay`).
2. Elaborating declarations under:
   - non-recursive `def`
   - structural recursive `def`
   - well-founded recursive `def`
   - `partial_fixpoint` recursive `def`
   - mutual recursive `def`
   - `where` / `let rec` local recursive helpers
   - `deriving DecidableEq` on recursive vs non-recursive `inductive`
   - `partial def`
   - `unsafe def`
   - `unsafe t` inside a safe `def`
   - `noncomputable def`
   - `noncomputable section` without `noncomputable` on `def` (both computable body
     and body referencing a `noncomputable` constant!)
3. Recursor codegen error reproduction (`MirVal.rec` vs `Nat.rec` vs `Prop`-valued
   `MirVal.rec`).
4. Bit-for-bit `ConstantInfo` comparison (`<fn>`, `<fn>._f`, `<fn>._sunfold`) and
   microbenchmarks of compilation, `.olean` size, kernel `whnf`/`isDefEq` reduction,
   and `toKernelEnv.replay` time.
-/

def kindStr (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo v =>
    let s := match v.safety with
      | .safe => "safe"
      | .unsafe => "unsafe"
      | .partial => "partial"
    let h := match v.hints with
      | .opaque => "opaque"
      | .abbrev => "abbrev"
      | .regular n => s!"regular({n})"
    s!"defnInfo(safety={s}, hints={h})"
  | .thmInfo _ => "thmInfo"
  | .axiomInfo v => s!"axiomInfo(isUnsafe={v.isUnsafe})"
  | .opaqueInfo v => s!"opaqueInfo(isUnsafe={v.isUnsafe})"
  | .quotInfo _ => "quotInfo"
  | .inductInfo _ => "inductInfo"
  | .ctorInfo _ => "ctorInfo"
  | .recInfo _ => "recInfo"

def runSnippet (baseEnv : Environment) (code : String) : IO (Environment × List Message) := do
  let (env, msgs) ← Lean.Elab.process code baseEnv {} "<probe>"
  return (env, msgs.toList)

def inspectSnippet (baseEnv : Environment) (title : String) (code : String) : IO Unit := do
  IO.println s!"=== {title} ==="
  let (env, msgs) ← runSnippet baseEnv code
  for m in msgs do
    let sev := match m.severity with
      | .information => "info"
      | .warning => "warn"
      | .error => "error"
    let txt ← m.data.toString
    IO.println s!"  [msg:{sev}] {txt.trimAscii}"
  let kenv := env.toKernelEnv
  let mut decls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in kenv.constants.map₂.toList do
    if !(baseEnv.toKernelEnv.constants.map₂.contains n) then
      if !n.isInternalDetail || (Compiler.isUnsafeRecName? n).isSome || ci.isUnsafe || ci.isPartial ||
         n.toString.contains "_unsafe" || n.toString.contains "_f" || n.toString.contains "_sunfold" ||
         n.toString.contains "_unary" || n.toString.contains "_mutual" || n.toString.contains "mutual" then
        decls := decls.push (n, ci)
  let sorted := decls.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, ci) in sorted do
    let isNC := isNoncomputable env n
    let hasIR := (IR.findEnvDecl env n).isSome
    let implBy := Compiler.getImplementedBy? env n
    IO.println s!"  const {n} : {kindStr ci} | isUnsafe={ci.isUnsafe} isPartial={ci.isPartial} isUnsafeRec={Compiler.isUnsafeRecName? n} noncompExt={isNC} hasIR={hasIR} implBy={implBy}"
  let baseModData ← mkModuleData baseEnv
  let modData ← mkModuleData env
  let newExtra := modData.extraConstNames.filter (!baseModData.extraConstNames.contains ·)
  IO.println s!"  ModuleData.extraConstNames (new): {newExtra}"

unsafe def inspectPreludeRecProbeOlean : IO Unit := do
  IO.println "=== Inspecting PreludeRecProbe.olean ==="
  let (modData, _) ← readModuleData (System.FilePath.mk "PreludeRecProbe.olean")
  IO.println s!"  ModuleData.constants.size = {modData.constants.size}"
  IO.println s!"  ModuleData.extraConstNames.size = {modData.extraConstNames.size}"
  let mut unsafeOrPartial : Array (Name × ConstantInfo) := #[]
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  for ci in modData.constants do
    replayMap := replayMap.insert ci.name ci
    if ci.isUnsafe || ci.isPartial then
      unsafeOrPartial := unsafeOrPartial.push (ci.name, ci)
  IO.println s!"  unsafeOrPartial count in PreludeRecProbe.olean = {unsafeOrPartial.size}"
  for (n, ci) in unsafeOrPartial do
    IO.println s!"    ! {n} : {kindStr ci} (isUnsafe={ci.isUnsafe}, isPartial={ci.isPartial})"
  let base ← importModules modData.imports {} 0 (loadExts := false) (level := .private)
  let t0 ← IO.monoNanosNow
  let replayed ← base.toKernelEnv.replay replayMap
  let t1 ← IO.monoNanosNow
  let hasTheorem := (replayed.find? `ClusterA1Probe.test_compileStage0Repeat_rfl).isSome
  IO.println s!"  base.toKernelEnv.replay succeeded: {hasTheorem} in {(t1 - t0) / 1000000} ms"

unsafe def runBenchmarks (baseEnv : Environment) : IO Unit := do
  IO.println "=== 7. Performance & Size Benchmarks (Computable vs Noncomputable vs Nat.repeat) ==="
  let preamble := "
inductive Val where
  | num (n : Nat)
  | add1 (inner : Val)

def mkDeepVal : Nat → Val :=
  Nat.rec (.num 7) (fun _ ih => .add1 ih)
"
  -- Variant A: Structural `noncomputable def`
  let codeNC := preamble ++ "
noncomputable def evalVal : Val → Nat
  | .num n => n
  | .add1 inner => evalVal inner + 1

theorem test_eval : evalVal (mkDeepVal 50) = 57 := rfl
"
  -- Variant B: Structural computable `def` (emits `evalVal._unsafe_rec`)
  let codeComp := preamble ++ "
def evalVal : Val → Nat
  | .num n => n
  | .add1 inner => evalVal inner + 1

theorem test_eval : evalVal (mkDeepVal 50) = 57 := rfl
"
  -- Variant C: Computable `Nat.repeat` `def` (zero `._unsafe_rec`)
  let codeRepeat := preamble ++ "
def evalValStep (recStep : Val → Nat) (v : Val) : Nat :=
  match v with
  | .num n => n
  | .add1 inner => recStep inner + 1

def evalVal (fuel : Nat) (v : Val) : Nat :=
  Nat.repeat evalValStep fuel (fun _ => 0) v

theorem test_eval : evalVal 60 (mkDeepVal 50) = 57 := rfl
"
  let baseModData ← mkModuleData baseEnv
  for (label, code) in [("noncomputable def (structural)", codeNC),
                        ("computable def (structural, emits ._unsafe_rec)", codeComp),
                        ("computable def (Nat.repeat, zero ._unsafe_rec)", codeRepeat)] do
    let tStart ← IO.monoNanosNow
    let (env, msgs) ← runSnippet baseEnv code
    let tElab ← IO.monoNanosNow
    let errCount := msgs.filter (fun m => match m.severity with | .error => true | _ => false) |>.length
    let modData ← mkModuleData env
    let newConsts := modData.constants.filter (fun ci => !(baseEnv.toKernelEnv.constants.map₂.contains ci.name))
    let newExtra := modData.extraConstNames.filter (!baseModData.extraConstNames.contains ·)
    let kenv := env.toKernelEnv
    let mut replayMap : Std.HashMap Name ConstantInfo := {}
    let mut unsafeRecCount := 0
    for ci in newConsts do
      if ci.isUnsafe || ci.isPartial then
        unsafeRecCount := unsafeRecCount + 1
      else
        replayMap := replayMap.insert ci.name ci
    let tReplay0 ← IO.monoNanosNow
    let _ ← baseEnv.toKernelEnv.replay replayMap
    let tReplay1 ← IO.monoNanosNow
    -- Also time 50 direct Kernel.isDefEq calls on `test_eval`'s equation
    let some (.thmInfo thm) := kenv.find? `test_eval | unreachable!
    let eqArgs := thm.type.getAppArgs
    let lhs := eqArgs[1]!
    let rhs := eqArgs[2]!
    let tK0 ← IO.monoNanosNow
    for _ in [0:50] do
      let _ := Kernel.isDefEqGuarded env {} lhs rhs
    let tK1 ← IO.monoNanosNow
    IO.println s!"  [{label}]"
    IO.println s!"    errors={errCount} | new_constants={newConsts.size} | new_extraConstNames={newExtra.size} | unsafe/partial={unsafeRecCount}"
    IO.println s!"    elab_ms={(tElab - tStart) / 1000000} | replay_us={(tReplay1 - tReplay0) / 1000} | 50x_kernel_isDefEq_us={(tK1 - tK0) / 1000}"

unsafe def runAllProbes : CommandElabM Unit := do
  let baseEnv ← getEnv
  liftM (m := IO) do
    let sysroot := System.FilePath.mk "/home/user/.elan/toolchains/leanprover--lean4---v4.34.1"
    initSearchPath sysroot [System.FilePath.mk "."]
    inspectPreludeRecProbeOlean

    inspectSnippet baseEnv "1. Non-recursive vs Structural vs WF vs PartialFixpoint vs Partial vs Unsafe" "
def nonRecFn (n : Nat) : Nat := n + 1

def structRecFn : Nat → Nat
  | 0 => 0
  | n + 1 => structRecFn n + 1

def wfRecFn (n : Nat) : Nat :=
  if h : n == 0 then 0 else wfRecFn (n - 1) + 1
termination_by n
decreasing_by
  simp_wf
  exact Nat.sub_lt (Nat.pos_of_ne_zero (by intro h0; subst h0; revert h; decide)) (by decide)

def pfRecFn (n : Nat) : Option Nat :=
  if n == 0 then some 0 else pfRecFn (n - 1)
partial_fixpoint

partial def partialFn (n : Nat) : Nat :=
  if n == 0 then 0 else partialFn (n - 1)

unsafe def unsafeFn (n : Nat) : Nat :=
  if n == 0 then 0 else unsafeFn (n - 1)
"

    inspectSnippet baseEnv "2. Mutual Recursion, Where / Let Rec Closures, and Deriving DecidableEq" "
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def outerWithWhere (n : Nat) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | k + 1, acc => go k (acc + 1)

def outerWithLetRec (n : Nat) : Nat :=
  let rec loop : Nat → Nat
    | 0 => 0
    | k + 1 => loop k + 1
  loop n

inductive RecTree where
  | leaf (n : Nat)
  | branch (sub : RecTree)
  deriving DecidableEq
"

    inspectSnippet baseEnv "3. noncomputable section vs noncomputable def" "
noncomputable section

-- A: Recursive def in `noncomputable section` WITHOUT `noncomputable` keyword
def recInNoncompSection : Nat → Nat
  | 0 => 0
  | n + 1 => recInNoncompSection n + 1

-- B: Recursive def in `noncomputable section` WITHOUT `noncomputable` keyword
--    whose body actually uses a noncomputable axiom (`Classical.choice`)!
def recUsingChoiceInNoncompSection : Nat → Nat
  | 0 => Classical.choice ⟨0⟩
  | n + 1 => recUsingChoiceInNoncompSection n + 1

-- C: Recursive def WITH explicit `noncomputable def`
noncomputable def recWithExplicitNoncomp : Nat → Nat
  | 0 => 0
  | n + 1 => recWithExplicitNoncomp n + 1

end
"

    inspectSnippet baseEnv "4. `unsafe t` Expression Inside a Safe `def`" "
unsafe def fastImpl (n : Nat) : Nat := n + 1

def safeWrapperUsingUnsafeExpr (n : Nat) : Nat :=
  unsafe (fastImpl n)
"

    inspectSnippet baseEnv "5. Recursor Codegen: Custom `Val.rec` (Type) vs `Nat.rec` vs `Prop`-valued `Val.rec`" "
inductive CustomVal where
  | leaf (n : Nat)
  | node (inner : CustomVal)

-- 5a: Direct `Nat.rec` in computable `def` (SUCCEEDS via @[csimp] Nat.rec_eq_recCompiled)
def natRecComputable (n : Nat) : Nat :=
  Nat.rec 0 (fun _ ih => ih + 1) n

-- 5b: Direct `CustomVal.rec` in `Prop`-valued `def` (SUCCEEDS via LCNF.shouldGenerateCode isProp)
def customValRecProp (v : CustomVal) : Prop :=
  CustomVal.rec (motive := fun _ => Prop) (fun n => n == 0) (fun _ ih => ih) v

-- 5c: Direct `CustomVal.rec` in `Type`-valued `def` (FAILS in LCNF ToImpure.lean:184)
def customValRecType (v : CustomVal) : Nat :=
  CustomVal.rec (motive := fun _ => Nat) (fun n => n) (fun _ ih => ih + 1) v
"

    -- 6. Bit-for-bit ConstantInfo comparison between computable `def` and `noncomputable def`
    IO.println "=== 6. Bit-for-Bit ConstantInfo Comparison (Computable vs Noncomputable Structural Rec) ==="
    let (envComp, _) ← runSnippet baseEnv "
inductive Val where | base (n : Nat) | wrap (v : Val)
def evalVal : Val → Nat
  | .base n => n
  | .wrap v => evalVal v + 1
"
    let (envNC, _) ← runSnippet baseEnv "
inductive Val where | base (n : Nat) | wrap (v : Val)
noncomputable def evalVal : Val → Nat
  | .base n => n
  | .wrap v => evalVal v + 1
"
    for suffix in [`evalVal, `evalVal._f, `evalVal._sunfold] do
      let c1 := envComp.toKernelEnv.find? suffix
      let c2 := envNC.toKernelEnv.find? suffix
      match c1, c2 with
      | some (.defnInfo d1), some (.defnInfo d2) =>
        let sameType := d1.type == d2.type
        let sameVal := d1.value == d2.value
        let sameHints := d1.hints == d2.hints
        let sameSafety := d1.safety == d2.safety
        let sameAll := d1.all == d2.all
        IO.println s!"  {suffix}: sameType={sameType} sameVal={sameVal} sameHints={sameHints} sameSafety={sameSafety} sameAll={sameAll}"
      | _, _ =>
        IO.println s!"  {suffix}: missing in one environment!"
    IO.println s!"  evalVal._unsafe_rec in envComp: {(envComp.toKernelEnv.find? `evalVal._unsafe_rec).isSome}"
    IO.println s!"  evalVal._unsafe_rec in envNC:   {(envNC.toKernelEnv.find? `evalVal._unsafe_rec).isSome}"

    runBenchmarks baseEnv

#eval unsafe runAllProbes
