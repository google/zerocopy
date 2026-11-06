-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Init.Data.BitVec.Basic
import Init.Data.Nat.Bitwise.Lemmas

/-!
# Unified End-to-End Verification Stack (`UnifiedEndToEndStack.lean`)

This module implements the complete, self-contained Lean `v4.34.1` `Trusted`
and `Theory` stack combining all kernel-replay and validator optimizations:

1. **`Trusted` (`Trusted/Refinement.lean` + `Trusted/MirSemantics.lean`):**
   - Behavioral refinement algebra (`Partial`, `Behavior`, `Language`,
     `Compiles`, `Verified`, `FunctionSpec`, `TcbAssumption`, `Crate`,
     `CrateAssumptions`, `CrateTheorem`).
   - Interprocedural call-stack operational semantics (`CallFrame`, `State`,
     `Instr.call`, `lookupFn`, `evalStep`, `Reach`, `ReachesPrefix`,
     `SafeAndEnsures`, `VerifiedFrom`).
   - **Fix for `Trusted/MirSemantics.lean:1794`:** `MirLang.Prog` is
     `MirProg × List Instr` (carrying the crate's function table `MirProg`
     alongside the entry `MirBody`) instead of hardcoding
     `fns := [("__entry", body)]`, enabling interprocedural `Instr.call`
     transitions to resolve callees soundly through `MirLang.sem`.
   - Memory alignment, 64-bit byte-interval disjointness, and symbolic-base
     subrange side-condition obligations (`SideCondSpec`, `AllSideCondsHold`)
     enforced via `FunctionSpec.specWellFormed` in `CrateTheorem`.
2. **`Theory` (`theory/Anneal/`):**
   - **Stage 0 / Stage 1 Baseline Combinators:** Continuation-lambda stepping
     (`safeAndEnsures_of_step`) and `{ s with ... }` record-update stepping
     (`safeAndEnsures_of_step_record`).
   - **Stage 2 Combinators:** Contiguous `let`-shared `SuffixReach` stepping
     with `State.casesOn` (`stepInstrStrict`, preventing the C++ kernel
     `has_fvar` GMP bypass at `src/kernel/type_checker.cpp:703`), flat-tuple
     inlined call stepping (`inlineCoreCall_flat_step`), structural `.tail/.head`
     TCB membership witnesses, and Layer 1 GMP `Nat` side-condition batch
     reflection (`checkSideCondBatch_sound`).
   - **Stage 3 / Stage 4 Three-Layer Hybrid Validators & Shard Aggregation:**
     - **Layer 1:** `checkSideCondBatch_sound` (`rfl` batch reflection).
     - **Layer 2:** `cv_trans` GMP `Nat`-domain reflection (`evalCvProg_sound`),
       fused 5-instruction checked-add + bitwise-mix superinstruction idioms
       (`step_idiom5`), and hint-driven `SymPlan` validation
       (`evalIdiom5Hint_sound`).
     - **Layer 3:** Compositional CFG cut-point diamond convergence
       (`diamond_converge_step`), universal stack-lifting interprocedural
       `CalleeSummary` (`call_summary_flat_step`, `mkCoreCalleeBody_summary`),
       and counted/symbolic loop invariant summaries (`loop_summary_sound`).
     - **Incremental Sharding:** `ShardCert`, `AllShardsVerified`, and
       `verify_crate_of_shards`.
-/

namespace Trusted

/-!
## 1. Behavioral Refinement and Crate Verification Algebra (`Trusted/Refinement.lean`)
-/

structure Partial (α : Type) : Type where
  defined : Prop
  val : defined → α

instance {Out : Type} : LE (Partial (Out → Prop)) where
  le p q := (q.defined → p.defined) ∧
    ∀ (hq : q.defined) (hp : p.defined) (o : Out), p.val hp o → q.val hq o

def Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

instance {Query Out : Type} : LE (Behavior Query Out) where
  le b₁ b₂ := ∀ q, b₁ q ≤ b₂ q

theorem Behavior.le_refl {Query Out : Type} (b : Behavior Query Out) : b ≤ b :=
  fun _ => ⟨id, fun _ _ _ h => h⟩

theorem Behavior.le_trans {Query Out : Type}
    {b₁ b₂ b₃ : Behavior Query Out} (h₁₂ : b₁ ≤ b₂) (h₂₃ : b₂ ≤ b₃) :
    b₁ ≤ b₃ := by
  intro q
  refine ⟨fun h3 => (h₁₂ q).1 ((h₂₃ q).1 h3), ?_⟩
  intro h3 h1 o ho
  have h2 : (b₂ q).defined := (h₂₃ q).1 h3
  exact (h₂₃ q).2 h3 h2 o ((h₁₂ q).2 h2 h1 o ho)

structure Language (SemObs : Type) where
  Prog : Type
  Query : Type
  Out : Type
  obs : Out → SemObs
  sem : Prog → Behavior Query Out

def Monotone {Q₁ O₁ Q₂ O₂ : Type}
    (π : Behavior Q₁ O₁ → Behavior Q₂ O₂) : Prop :=
  ∀ ⦃b₁ b₂⦄, b₁ ≤ b₂ → π b₁ ≤ π b₂

def Compiles {Obs : Type} (L_src L_tgt : Language Obs)
    (π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

def Verified {Obs : Type} (L_src L_tgt : Language Obs)
    (π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out)
    (_s : L_src.Prog) (t : L_tgt.Prog)
    (specs : List (Behavior L_src.Query L_src.Out)) : Prop :=
  ∀ sp, sp ∈ specs → L_tgt.sem t ≤ π_c sp

structure FunctionSpec {Obs : Type} (L_src : Language Obs) where
  name : String
  prog : L_src.Prog
  specs : List (Behavior L_src.Query L_src.Out)
  specWellFormed : Behavior L_src.Query L_src.Out → Prop

inductive TcbAssumption {Obs : Type} (L_src L_tgt : Language Obs)
    (π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out) where
  | rustcLowering (fnName : String) (s : L_src.Prog)

def TcbAssumption.interp {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    (a : TcbAssumption L_src L_tgt π_c) (t : String → Option L_tgt.Prog) : Prop :=
  match a with
  | .rustcLowering fnName s =>
    ∃ t_prog, t fnName = some t_prog ∧ Compiles L_src L_tgt π_c s t_prog

structure Crate {Obs : Type} (L_src L_tgt : Language Obs)
    (π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out) where
  functions : List (FunctionSpec L_src)
  tcb : List (TcbAssumption L_src L_tgt π_c)

def CrateAssumptions {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    (c : Crate L_src L_tgt π_c) (t : String → Option L_tgt.Prog) : Prop :=
  ∀ a, a ∈ c.tcb → a.interp t

/-- Root crate verification theorem matching `VerificationResult` /
    `CrateTheorem` in `Trusted/Refinement.lean:456-472`. -/
def CrateTheorem {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    (c : Crate L_src L_tgt π_c) : Prop :=
  ∀ f, f ∈ c.functions →
    ∀ (t : String → Option L_tgt.Prog) (t_prog : L_tgt.Prog),
      t f.name = some t_prog →
      CrateAssumptions c t →
      Verified L_src L_tgt π_c f.prog t_prog f.specs ∧
      (∀ sp, sp ∈ f.specs → f.specWellFormed sp)

/-!
## 2. Memory Alignment and Byte-Interval Side-Condition Specifications (`Trusted`)
-/

/-- 64-bit maximum address `2^64 - 1`. -/
def ADDR_MASK : Nat := 18446744073709551615

/-- Obligation Type 1: Two byte intervals `[p1, p1 + n1)` and `[p2, p2 + n2)`
    are disjoint and both fit within the 64-bit address space without wrapping. -/
def IntervalsDisjoint (p1 n1 p2 n2 : Nat) : Prop :=
  (p1 + n1 ≤ p2 ∨ p2 + n2 ≤ p1) ∧ p1 + n1 ≤ ADDR_MASK ∧ p2 + n2 ≤ ADDR_MASK

/-- Obligation Type 2: `out` is the aligned round-up of byte offset `off` to
    alignment `align`, is a multiple of `align`, and satisfies
    `off ≤ out < off + align`. -/
def AlignedRoundUp (off align out : Nat) : Prop :=
  out % align = 0 ∧ off ≤ out ∧ out < off + align

/-- Obligation Type 3: Universal symbolic pointer-offset subrange safety:
    for any base address `base : Nat`, `[base + off, base + off + sublen)` lies
    within `[base, base + totallen)`. -/
def SymbolicSubrange (off sublen totallen : Nat) : Prop :=
  ∀ (base : Nat), base + off + sublen ≤ base + totallen ∧ base ≤ base + off

/-- Tagged side-condition obligation attached to a function specification. -/
inductive SideCondSpec where
  | disjoint (p1 n1 p2 n2 : Nat)
  | aligned (off align out : Nat)
  | subrange (off sublen totallen : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Interpretation of a `SideCondSpec` in `Prop`. -/
def SideCondSpec.holds : SideCondSpec → Prop
  | .disjoint p1 n1 p2 n2 => IntervalsDisjoint p1 n1 p2 n2
  | .aligned off align out => AlignedRoundUp off align out
  | .subrange off sublen totallen => SymbolicSubrange off sublen totallen

/-- Conjunction of all side-condition obligations for a function. -/
def AllSideCondsHold : List SideCondSpec → Prop
  | [] => True
  | c :: rest => c.holds ∧ AllSideCondsHold rest

/-!
## 3. Interprocedural Call-Stack MIR Semantics (`Trusted/MirSemantics.lean`)
-/

/-- Register / local variable identifier in the MIR machine. -/
inductive Reg where
  | r0
  | r1
  | r2
  | r3
  deriving DecidableEq, Repr

/-- Symbolic branch condition environment for CFG diamond conditionals. -/
structure BranchEnv where
  c0 : Bool
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  deriving DecidableEq, Repr

def defaultBranchEnv : BranchEnv := ⟨false, false, false, false, false⟩

def BranchEnv.getCond (q : BranchEnv) : Nat → Bool
  | 0 => q.c0
  | 1 => q.c1
  | 2 => q.c2
  | 3 => q.c3
  | _ => q.c4

/-- MIR instruction set including checked arithmetic, bitwise manipulation,
    conditional branch-select, and interprocedural calls (`Instr.call`). -/
inductive Instr where
  | add (dst src1 src2 : Reg)
  | sub (dst src1 src2 : Reg)
  | xor (dst src1 src2 : Reg)
  | band (dst src1 src2 : Reg)
  | shl (dst src : Reg) (amt : Nat)
  | shr (dst src : Reg) (amt : Nat)
  | addImm (dst src : Reg) (imm : BitVec 64)
  | addCheckedImm (dst src : Reg) (imm : BitVec 64)
  | assertNotFlag
  | selectImm (condIdx : Nat) (dst : Reg) (immT immF : BitVec 64)
  | call (fnName : String)
  deriving DecidableEq, Repr

/-- Saved caller activation record on the interprocedural call stack. -/
structure CallFrame where
  returnBody : List Instr
  returnPc   : Nat
  savedR1    : BitVec 64
  savedR2    : BitVec 64
  savedR3    : BitVec 64
  deriving DecidableEq, Repr

/-- Machine state with `curBody`, `pc`, 64-bit `BitVec 64` registers, overflow
    `flag`, and interprocedural call `stack`. -/
structure State where
  curBody : List Instr
  pc      : Nat
  r0      : BitVec 64
  r1      : BitVec 64
  r2      : BitVec 64
  r3      : BitVec 64
  flag    : Bool
  stack   : List CallFrame
  deriving DecidableEq, Repr

/-- Crate function table mapping function names to their MIR instruction bodies. -/
abbrev MirProg := List (String × List Instr)

/-- Look up a function body by name in `prog : MirProg`. -/
def lookupFn (prog : MirProg) (name : String) : Option (List Instr) :=
  match prog with
  | [] => none
  | (fnName, body) :: rest =>
    if fnName == name then some body else lookupFn rest name

/-- Read register `r` from `s`. -/
def State.getReg (s : State) : Reg → BitVec 64
  | .r0 => s.r0
  | .r1 => s.r1
  | .r2 => s.r2
  | .r3 => s.r3

/-- Write `v` to register `r` in `s` and advance `pc` by `1`. -/
def State.setRegNext (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .r0 => ⟨s.curBody, s.pc + 1, v, s.r1, s.r2, s.r3, s.flag, s.stack⟩
  | .r1 => ⟨s.curBody, s.pc + 1, s.r0, v, s.r2, s.r3, s.flag, s.stack⟩
  | .r2 => ⟨s.curBody, s.pc + 1, s.r0, s.r1, v, s.r3, s.flag, s.stack⟩
  | .r3 => ⟨s.curBody, s.pc + 1, s.r0, s.r1, s.r2, v, s.flag, s.stack⟩

/-- Write `v` to register `r` and `fl` to `flag` in `s`, advancing `pc` by `1`. -/
def State.setRegFlagNext (s : State) (r : Reg) (v : BitVec 64) (fl : Bool) : State :=
  match r with
  | .r0 => ⟨s.curBody, s.pc + 1, v, s.r1, s.r2, s.r3, fl, s.stack⟩
  | .r1 => ⟨s.curBody, s.pc + 1, s.r0, v, s.r2, s.r3, fl, s.stack⟩
  | .r2 => ⟨s.curBody, s.pc + 1, s.r0, s.r1, v, s.r3, fl, s.stack⟩
  | .r3 => ⟨s.curBody, s.pc + 1, s.r0, s.r1, s.r2, v, fl, s.stack⟩

/-- Intra-procedural instruction transition (excluding `Instr.call`, which is
    dispatched by `evalStep` using the crate's `MirProg` table). -/
def stepInstr (q : BranchEnv) (i : Instr) (s : State) : Option State :=
  match i with
  | .add dst src1 src2 =>
    some (s.setRegNext dst (s.getReg src1 + s.getReg src2))
  | .sub dst src1 src2 =>
    some (s.setRegNext dst (s.getReg src1 - s.getReg src2))
  | .xor dst src1 src2 =>
    some (s.setRegNext dst (s.getReg src1 ^^^ s.getReg src2))
  | .band dst src1 src2 =>
    some (s.setRegNext dst (s.getReg src1 &&& s.getReg src2))
  | .shl dst src amt =>
    some (s.setRegNext dst (s.getReg src <<< amt))
  | .shr dst src amt =>
    some (s.setRegNext dst (s.getReg src >>> amt))
  | .addImm dst src imm =>
    some (s.setRegNext dst (s.getReg src + imm))
  | .addCheckedImm dst src imm =>
    let v := s.getReg src
    let ov := BitVec.uaddOverflow v imm
    some (s.setRegFlagNext dst (v + imm) ov)
  | .assertNotFlag =>
    if s.flag then none
    else some ⟨s.curBody, s.pc + 1, s.r0, s.r1, s.r2, s.r3, s.flag, s.stack⟩
  | .selectImm condIdx dst immT immF =>
    let v := if q.getCond condIdx then immT else immF
    some (s.setRegNext dst v)
  | .call _ =>
    none

/-- Small-step outcome of executing one transition of `evalStep`. -/
inductive StepOut where
  | step (next : State)
  | ret (val : BitVec 64)
  | trap
  deriving DecidableEq, Repr

/-- Fetch and execute the instruction at `s.curBody[s.pc]?`, pushing a
    `CallFrame` on `Instr.call` and popping the top `CallFrame` on function
    completion (`s.curBody[s.pc]? = none`). -/
def evalStep (prog : MirProg) (q : BranchEnv) (s : State) : StepOut :=
  match s.curBody[s.pc]? with
  | some (.call fnName) =>
    match lookupFn prog fnName with
    | some calleeBody =>
      let frame : CallFrame := ⟨s.curBody, s.pc + 1, s.r1, s.r2, s.r3⟩
      .step ⟨calleeBody, 0, s.r0, s.r1, 0#64, 0#64, false, frame :: s.stack⟩
    | none => .trap
  | some instr =>
    match stepInstr q instr s with
    | some s' => .step s'
    | none => .trap
  | none =>
    match s.stack with
    | [] => .ret s.r0
    | frame :: restStack =>
      .step ⟨frame.returnBody, frame.returnPc, s.r0,
             frame.savedR1, frame.savedR2, frame.savedR3, false, restStack⟩

/-- Forward small-step reachability to a normal return value `v`. -/
inductive Reach (prog : MirProg) (q : BranchEnv) : State → BitVec 64 → Prop where
  | done (s : State) (v : BitVec 64)
      (hTerm : evalStep prog q s = .ret v) :
      Reach prog q s v
  | step (s s' : State) (v : BitVec 64)
      (hStep : evalStep prog q s = .step s')
      (hRest : Reach prog q s' v) :
      Reach prog q s v

/-- Prefix execution outcome for Anneal's step-indexed prefix semantics. -/
inductive PrefixOut where
  | running
  | ret (val : BitVec 64)
  | trap
  deriving DecidableEq, Repr

/-- Step-indexed prefix execution relation matching `Trusted.ReachesPrefix`. -/
inductive ReachesPrefix (prog : MirProg) (q : BranchEnv) :
    Nat → State → PrefixOut → Prop where
  | zero (s : State) : ReachesPrefix prog q 0 s .running
  | step (n : Nat) (s s' : State) (out : PrefixOut)
      (hStep : evalStep prog q s = .step s')
      (hRest : ReachesPrefix prog q n s' out) :
      ReachesPrefix prog q (n + 1) s out
  | ret (n : Nat) (s : State) (v : BitVec 64)
      (hTerm : evalStep prog q s = .ret v) :
      ReachesPrefix prog q (n + 1) s (.ret v)
  | trap (n : Nat) (s : State)
      (hTrap : evalStep prog q s = .trap) :
      ReachesPrefix prog q (n + 1) s .trap

/-- Combined safety and return-value specification matching `Anneal.SafeAndEnsures`. -/
def SafeAndEnsures (P : BitVec 64 → Prop) (out : PrefixOut) : Prop :=
  out ≠ .trap ∧ ∀ v, out = .ret v → P v

/-- Universal prefix safety and postcondition satisfaction from state `s`. -/
def VerifiedFrom (prog : MirProg) (q : BranchEnv) (s : State) (v : BitVec 64) : Prop :=
  ∀ n out, ReachesPrefix prog q n s out → SafeAndEnsures (fun r => r = v) out

/-- Canonical initial state for executing an entry `body : List Instr`. -/
def entryState (body : List Instr) : State :=
  ⟨body, 0, 7#64, 0#64, 3#64, 0#64, false, []⟩

/-- **Fixed `MirLang` (`MirLang.Prog := MirProg × List Instr`):**
    Carries the crate's call table `prog : MirProg` alongside the function's
    entry `body : List Instr` so `lookupFn prog fnName` resolves interprocedural
    `Instr.call` transitions soundly inside `MirLang.sem`. -/
@[reducible] def MirLang : Language (BitVec 64) where
  Prog := MirProg × List Instr
  Query := BranchEnv
  Out := PrefixOut
  obs := fun
    | .ret v => v
    | _ => 0#64
  sem := fun (prog, body) q => {
    defined := True
    val := fun _ out => ∃ n, ReachesPrefix prog q n (entryState body) out
  }

/-- **Legacy Broken `MirLangBroken` (`Trusted/MirSemantics.lean:1794`):**
    Hardcodes `let prog : MirProg := [("__entry", body)]`, causing any
    `Instr.call fnName` with `fnName ≠ "__entry"` to fail `lookupFn` and step
    to `.trap`. Included as a negative canary. -/
@[reducible] def MirLangBroken : Language (BitVec 64) where
  Prog := List Instr
  Query := BranchEnv
  Out := PrefixOut
  obs := fun
    | .ret v => v
    | _ => 0#64
  sem := fun body q =>
    let prog : MirProg := [("__entry", body)]
    { defined := True
      val := fun _ out => ∃ n, ReachesPrefix prog q n (entryState body) out }

/-- Specification asserting that a function is trap-free and returns `v` for
    all branch environments `q : BranchEnv`. -/
def mkSpec (v : BitVec 64) : Behavior BranchEnv PrefixOut :=
  fun _ => {
    defined := True
    val := fun _ out => SafeAndEnsures (fun r => r = v) out
  }

def π_id : Behavior BranchEnv PrefixOut → Behavior BranchEnv PrefixOut := id

instance : DecidableEq (TcbAssumption MirLang MirLang π_id) := by
  intro a b
  cases a with
  | rustcLowering fn1 s1 =>
    cases b with
    | rustcLowering fn2 s2 =>
      exact if h1 : fn1 = fn2 then
        if h2 : s1 = s2 then
          isTrue (by subst h1 h2; rfl)
        else
          isFalse (by intro h; injection h with _ hs; exact h2 hs)
      else
        isFalse (by intro h; injection h with hfn _; exact h1 hfn)

end Trusted

namespace Theory

open Trusted

/-!
## 1. Refinement Bridge & Shard Aggregator (`theory/Anneal/Refinement.lean`)
-/

theorem π_id_mono : Monotone π_id := fun _ _ h => h

theorem VerifiedFrom_imp_sem_le {prog : MirProg} {body : List Instr} {v : BitVec 64}
    (hVer : ∀ q, VerifiedFrom prog q (entryState body) v) :
    MirLang.sem (prog, body) ≤ mkSpec v := by
  intro q
  refine ⟨id, ?_⟩
  intro _ _ out ⟨n, hReach⟩
  exact hVer q n out hReach

/-- Per-function shard certificate proved in `Proof/F_i.lean`:
    bundles the TCB membership witness, source-level behavioral refinement, and
    side-condition well-formedness. -/
structure ShardCert {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    (c : Crate L_src L_tgt π_c) (f : FunctionSpec L_src) : Prop where
  has_tcb : TcbAssumption.rustcLowering f.name f.prog ∈ c.tcb
  all_verified : ∀ sp, sp ∈ f.specs → L_src.sem f.prog ≤ sp ∧ f.specWellFormed sp

theorem shardCert_implies_obligation {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    {c : Crate L_src L_tgt π_c} {f : FunctionSpec L_src}
    (h_mono : Monotone π_c)
    (cert : ShardCert c f) :
    ∀ (t : String → Option L_tgt.Prog) (t_prog : L_tgt.Prog),
      t f.name = some t_prog →
      CrateAssumptions c t →
      Verified L_src L_tgt π_c f.prog t_prog f.specs ∧
      (∀ sp, sp ∈ f.specs → f.specWellFormed sp) := by
  intro t t_prog hlookup hAssump
  have ⟨t_prog', hlookup', hComp⟩ := hAssump (.rustcLowering f.name f.prog) cert.has_tcb
  rw [hlookup] at hlookup'
  injection hlookup' with heq
  subst heq
  refine ⟨?_, fun sp hsp => (cert.all_verified sp hsp).2⟩
  intro sp hsp
  exact Behavior.le_trans hComp (h_mono (cert.all_verified sp hsp).1)

inductive AllShardsVerified {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    (c : Crate L_src L_tgt π_c) : List (FunctionSpec L_src) → Prop where
  | nil : AllShardsVerified c []
  | cons {f : FunctionSpec L_src} {rest : List (FunctionSpec L_src)}
      (head : ShardCert c f)
      (tail : AllShardsVerified c rest) :
      AllShardsVerified c (f :: rest)

theorem verify_crate_of_shards_aux {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    {c : Crate L_src L_tgt π_c} (h_mono : Monotone π_c) :
    ∀ {fns : List (FunctionSpec L_src)},
      AllShardsVerified c fns →
      ∀ f, f ∈ fns →
        ∀ (t : String → Option L_tgt.Prog) (t_prog : L_tgt.Prog),
          t f.name = some t_prog →
          CrateAssumptions c t →
          Verified L_src L_tgt π_c f.prog t_prog f.specs ∧
          (∀ sp, sp ∈ f.specs → f.specWellFormed sp)
  | [], .nil, _, hmem => by cases hmem
  | _ :: _, .cons hHead hTail, f, hmem => by
    cases hmem with
    | head => exact shardCert_implies_obligation h_mono hHead
    | tail _ hInRest => exact verify_crate_of_shards_aux h_mono hTail f hInRest

/-- Generic $N$-function crate theorem aggregator proved once in `Theory`. -/
theorem verify_crate_of_shards {Obs : Type} {L_src L_tgt : Language Obs}
    {π_c : Behavior L_src.Query L_src.Out → Behavior L_tgt.Query L_tgt.Out}
    {c : Crate L_src L_tgt π_c} (h_mono : Monotone π_c)
    (hShards : AllShardsVerified c c.functions) :
    CrateTheorem c :=
  verify_crate_of_shards_aux h_mono hShards

/-- Helper constructing a `ShardCert` for a function in `MirLang`. -/
theorem mkShardCert {c : Crate MirLang MirLang π_id}
    {f : FunctionSpec MirLang} {v : BitVec 64} {scs : List SideCondSpec}
    (hSpecEq : f.specs = [mkSpec v])
    (hWfEq : f.specWellFormed = fun _ => AllSideCondsHold scs)
    (hTcb : TcbAssumption.rustcLowering f.name f.prog ∈ c.tcb)
    (hVer : ∀ q, VerifiedFrom f.prog.1 q (entryState f.prog.2) v)
    (hSide : AllSideCondsHold scs) :
    ShardCert c f := by
  refine ⟨hTcb, ?_⟩
  intro sp hmem
  rw [hSpecEq] at hmem
  cases hmem with
  | head =>
    refine ⟨VerifiedFrom_imp_sem_le hVer, ?_⟩
    rw [hWfEq]
    exact hSide
  | tail _ hnil => cases hnil

/-!
## 2. Stage 0 / Stage 1 Continuation-Lambda & Record-Update Stepping (`Arch 1b`)
-/

/-- Anneal PR `#81` (`MirLemmas.lean:58-74`) continuation-style single-step lemma. -/
theorem safeAndEnsures_of_step {prog : MirProg} {q : BranchEnv}
    {s s' : State} {n : Nat} {out : PrefixOut} {P : BitVec 64 → Prop}
    (hStep : evalStep prog q s = .step s')
    (hReach : ReachesPrefix prog q n s out)
    (hNext : ∀ n', ReachesPrefix prog q n' s' out → SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases hReach with
  | zero =>
    exact And.intro (by intro h; cases h) (fun _ h => by cases h)
  | step n' _ _ _ h1 hr =>
    rw [hStep] at h1
    injection h1 with hs
    subst hs
    exact hNext n' hr
  | ret _ _ _ h1 =>
    rw [hStep] at h1
    cases h1
  | trap _ _ h1 =>
    rw [hStep] at h1
    cases h1

/-- Anneal PR `#81` (`MirLemmas.lean`) terminal step lemma. -/
theorem safeAndEnsures_of_ret {prog : MirProg} {q : BranchEnv}
    {s : State} {n : Nat} {out : PrefixOut} {P : BitVec 64 → Prop} {v : BitVec 64}
    (hTerm : evalStep prog q s = .ret v)
    (hReach : ReachesPrefix prog q n s out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases hReach with
  | zero =>
    exact And.intro (by intro h; cases h) (fun _ h => by cases h)
  | step _ _ _ _ h1 _ =>
    rw [hTerm] at h1
    cases h1
  | ret _ _ _ h1 =>
    rw [hTerm] at h1
    injection h1 with hv
    subst hv
    refine And.intro (by intro h; cases h) (fun _ hr => ?_)
    injection hr with hr'
    subst hr'
    exact hPv
  | trap _ _ h1 =>
    rw [hTerm] at h1
    cases h1

/-- Forward `Reach prog q s v` implies universal prefix safety `VerifiedFrom prog q s v`. -/
theorem Reach_imp_VerifiedFrom {prog : MirProg} {q : BranchEnv}
    {s : State} {v : BitVec 64}
    (h : Reach prog q s v) :
    VerifiedFrom prog q s v := by
  induction h with
  | done s v hTerm =>
    intro n out hReach
    exact safeAndEnsures_of_ret hTerm hReach rfl
  | step s s' v hStep _ ih =>
    intro n out hReach
    exact safeAndEnsures_of_step hStep hReach (fun n' hr' => ih n' out hr')

theorem Reach_trans {prog : MirProg} {q : BranchEnv}
    {s₁ s₂ : State} {v : BitVec 64}
    (h1 : evalStep prog q s₁ = .step s₂)
    (h2 : Reach prog q s₂ v) :
    Reach prog q s₁ v :=
  Reach.step s₁ s₂ v h1 h2

/-- Stage 0 / Stage 1 record-update helper for a 12-transition inlined call to a
    10-instruction `core` helper (`1` call push + `10` body instructions + `1`
    return pop).
    Notice that the post-state uses Lean's `{ s with pc := ..., r0 := ..., flag := false }`
    record-update syntax, which desugars to:
      `State.mk s.curBody (s.pc + 1) vOut s.r1 s.r2 s.r3 false s.stack`
    referencing `s` **6 times** per call and reproducing the $O(6^K)$ unshared
    expression tree (`TREE_NODES`) blowup! -/
theorem inlineCoreCall12_record {prog : MirProg} {q : BranchEnv}
    {s s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : State}
    {vOut : BitVec 64} {n : Nat} {out : PrefixOut} {P : BitVec 64 → Prop}
    (h1 : evalStep prog q s = .step s1)
    (h2 : evalStep prog q s1 = .step s2)
    (h3 : evalStep prog q s2 = .step s3)
    (h4 : evalStep prog q s3 = .step s4)
    (h5 : evalStep prog q s4 = .step s5)
    (h6 : evalStep prog q s5 = .step s6)
    (h7 : evalStep prog q s6 = .step s7)
    (h8 : evalStep prog q s7 = .step s8)
    (h9 : evalStep prog q s8 = .step s9)
    (h10 : evalStep prog q s9 = .step s10)
    (h11 : evalStep prog q s10 = .step s11)
    (h12 : evalStep prog q s11 = .step { s with pc := s.pc + 1, r0 := vOut, flag := false })
    (hReach : ReachesPrefix prog q n s out)
    (hNext : ∀ n',
      ReachesPrefix prog q n' { s with pc := s.pc + 1, r0 := vOut, flag := false } out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out :=
  safeAndEnsures_of_step h1 hReach fun _ hr1 =>
  safeAndEnsures_of_step h2 hr1 fun _ hr2 =>
  safeAndEnsures_of_step h3 hr2 fun _ hr3 =>
  safeAndEnsures_of_step h4 hr3 fun _ hr4 =>
  safeAndEnsures_of_step h5 hr4 fun _ hr5 =>
  safeAndEnsures_of_step h6 hr5 fun _ hr6 =>
  safeAndEnsures_of_step h7 hr6 fun _ hr7 =>
  safeAndEnsures_of_step h8 hr7 fun _ hr8 =>
  safeAndEnsures_of_step h9 hr8 fun _ hr9 =>
  safeAndEnsures_of_step h10 hr9 fun _ hr10 =>
  safeAndEnsures_of_step h11 hr10 fun _ hr11 =>
  safeAndEnsures_of_step h12 hr11 hNext

/-- Stage 0 / Stage 1 record-update helper for an intra-procedural instruction
    step between inlined calls, updating `s` via `{ s with pc := ..., r0 := ...,
    r1 := ..., r2 := ..., flag := false }`. -/
theorem step_record {prog : MirProg} {q : BranchEnv}
    {s : State} {r0' r1' r2' : BitVec 64}
    {n : Nat} {out : PrefixOut} {P : BitVec 64 → Prop}
    (h1 : evalStep prog q s =
      .step { s with pc := s.pc + 1, r0 := r0', r1 := r1', r2 := r2', flag := false })
    (hReach : ReachesPrefix prog q n s out)
    (hNext : ∀ n',
      ReachesPrefix prog q n'
        { s with pc := s.pc + 1, r0 := r0', r1 := r1', r2 := r2', flag := false } out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out :=
  safeAndEnsures_of_step h1 hReach hNext

/-!
## 3. Layer 1: Pre-Proved GMP `Nat` Side-Condition Reflection (`checkSideCondBatch_sound`)
-/

/-- Native GMP boolean checker for `IntervalsDisjoint`. Uses exclusively
    `Nat.add` and `Nat.ble`, which reduce in C++ via `type_checker::reduce_nat`. -/
def checkIntervalDisjoint (p1 n1 p2 n2 : Nat) : Bool :=
  (Nat.ble (p1 + n1) p2 || Nat.ble (p2 + n2) p1) &&
    Nat.ble (p1 + n1) ADDR_MASK &&
    Nat.ble (p2 + n2) ADDR_MASK

theorem checkIntervalDisjoint_sound {p1 n1 p2 n2 : Nat}
    (h : checkIntervalDisjoint p1 n1 p2 n2 = true) :
    IntervalsDisjoint p1 n1 p2 n2 := by
  unfold checkIntervalDisjoint at h
  unfold IntervalsDisjoint
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
  rcases h with ⟨⟨h1 | h2, h3⟩, h4⟩
  · exact ⟨Or.inl h1, h3, h4⟩
  · exact ⟨Or.inr h2, h3, h4⟩

/-- Native GMP boolean checker for `AlignedRoundUp`. Uses `Nat.mod`, `Nat.beq`,
    `Nat.add`, and `Nat.ble`, which reduce in C++ via `type_checker::reduce_nat`. -/
def checkAlignedRoundUp (off align out : Nat) : Bool :=
  Nat.beq (out % align) 0 &&
    Nat.ble off out &&
    Nat.ble (out + 1) (off + align)

theorem checkAlignedRoundUp_sound {off align out : Nat}
    (h : checkAlignedRoundUp off align out = true) :
    AlignedRoundUp off align out := by
  unfold checkAlignedRoundUp at h
  unfold AlignedRoundUp
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  rcases h with ⟨⟨hMod, hLe⟩, hLt⟩
  exact ⟨hMod, hLe, hLt⟩

/-- Native GMP boolean checker for `SymbolicSubrange`. Cancels the symbolic
    `base : Nat` quantifier once in `Theory` so per-crate proofs in `Proof.lean`
    only check `Nat.ble (off + sublen) totallen = true` by `rfl`. -/
def checkSymbolicSubrange (off sublen totallen : Nat) : Bool :=
  Nat.ble (off + sublen) totallen

theorem checkSymbolicSubrange_sound {off sublen totallen : Nat}
    (h : checkSymbolicSubrange off sublen totallen = true) :
    SymbolicSubrange off sublen totallen := by
  unfold checkSymbolicSubrange at h
  unfold SymbolicSubrange
  rw [Nat.ble_eq] at h
  intro base
  omega

/-- Dispatch a single `SideCondSpec` to its GMP `Nat` boolean checker. -/
def checkSideCond : SideCondSpec → Bool
  | .disjoint p1 n1 p2 n2 => checkIntervalDisjoint p1 n1 p2 n2
  | .aligned off align out => checkAlignedRoundUp off align out
  | .subrange off sublen totallen => checkSymbolicSubrange off sublen totallen

theorem checkSideCond_sound {c : SideCondSpec} (h : checkSideCond c = true) :
    c.holds := by
  cases c with
  | disjoint p1 n1 p2 n2 => exact checkIntervalDisjoint_sound h
  | aligned off align out => exact checkAlignedRoundUp_sound h
  | subrange off sublen totallen => exact checkSymbolicSubrange_sound h

/-- Batch evaluator for a list of `SideCondSpec` obligations. -/
def checkSideCondBatch : List SideCondSpec → Bool
  | [] => true
  | c :: rest => checkSideCond c && checkSideCondBatch rest

theorem checkSideCondBatch_sound {xs : List SideCondSpec}
    (h : checkSideCondBatch xs = true) :
    AllSideCondsHold xs := by
  induction xs with
  | nil => exact trivial
  | cons c rest ih =>
    dsimp [checkSideCondBatch] at h
    rw [Bool.and_eq_true] at h
    exact ⟨checkSideCond_sound h.1, ih h.2⟩

/-!
## 4. Stage 2: Structural `SuffixReach` Stepping with `State.casesOn` Unpacking
-/

/-- Strict wrapper around `stepInstr` that unpacks `s : State` via `State.casesOn`
    (`State.rec`) at entry. When `s` is a `let`-bound local `FVar` (`ldecl`),
    `reduce_rec` calls `whnf(s)` first, unfolding `s` to a closed `State.mk`
    constructor (`has_fvar == false`) before register arithmetic is built. -/
def stepInstrStrict (q : BranchEnv) (i : Instr) (s : State) : Option State :=
  State.casesOn s fun curBody pc r0 r1 r2 r3 flag stack =>
    stepInstr q i ⟨curBody, pc, r0, r1, r2, r3, flag, stack⟩

theorem stepInstrStrict_eq (q : BranchEnv) (i : Instr) (s : State) :
    stepInstrStrict q i s = stepInstr q i s := by
  cases s
  rfl

/-- Strict wrapper around `evalStep` that unpacks `s : State` via `State.casesOn`
    at entry so `let`-bound cut-point states (`FVar`s) are unfolded to closed
    `State.mk` constructors before instruction arithmetic (including `.shr`) is
    evaluated. -/
def evalStepStrict (prog : MirProg) (q : BranchEnv) (s : State) : StepOut :=
  State.casesOn s fun curBody pc r0 r1 r2 r3 flag stack =>
    evalStep prog q ⟨curBody, pc, r0, r1, r2, r3, flag, stack⟩

theorem evalStepStrict_eq (prog : MirProg) (q : BranchEnv) (s : State) :
    evalStepStrict prog q s = evalStep prog q s := by
  cases s
  rfl

theorem stepInstr_pc {q : BranchEnv} {i : Instr} {s s' : State}
    (h : stepInstr q i s = some s') :
    s'.pc = s.pc + 1 := by
  cases i with
  | add dst _ _ | sub dst _ _ | xor dst _ _ | band dst _ _
  | shl dst _ _ | shr dst _ _ | addImm dst _ _ | selectImm _ dst _ _ =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | addCheckedImm dst _ _ =>
    dsimp [stepInstr, State.setRegFlagNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | assertNotFlag =>
    dsimp [stepInstr] at h
    cases hFlag : s.flag <;> simp [hFlag] at h
    cases h; rfl
  | call _ =>
    cases h

theorem stepInstr_curBody {q : BranchEnv} {i : Instr} {s s' : State}
    (h : stepInstr q i s = some s') :
    s'.curBody = s.curBody := by
  cases i with
  | add dst _ _ | sub dst _ _ | xor dst _ _ | band dst _ _
  | shl dst _ _ | shr dst _ _ | addImm dst _ _ | selectImm _ dst _ _ =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | addCheckedImm dst _ _ =>
    dsimp [stepInstr, State.setRegFlagNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | assertNotFlag =>
    dsimp [stepInstr] at h
    cases hFlag : s.flag <;> simp [hFlag] at h
    cases h; rfl
  | call _ =>
    cases h

theorem stepInstr_stack {q : BranchEnv} {i : Instr} {s s' : State}
    (h : stepInstr q i s = some s') :
    s'.stack = s.stack := by
  cases i with
  | add dst _ _ | sub dst _ _ | xor dst _ _ | band dst _ _
  | shl dst _ _ | shr dst _ _ | addImm dst _ _ | selectImm _ dst _ _ =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | addCheckedImm dst _ _ =>
    dsimp [stepInstr, State.setRegFlagNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | assertNotFlag =>
    dsimp [stepInstr] at h
    cases hFlag : s.flag <;> simp [hFlag] at h
    cases h; rfl
  | call _ =>
    cases h

/-- Suffix reachability over the remaining instruction list starting at `s.pc`,
    supporting both intra-procedural instructions (`cons`) and interprocedural
    calls (`call`). -/
inductive SuffixReach (prog : MirProg) (q : BranchEnv) :
    List Instr → State → BitVec 64 → Prop where
  | nil (s : State) (hStack : s.stack = []) :
      SuffixReach prog q [] s s.r0
  | cons (i : Instr) (rest : List Instr) (s s' : State) (v : BitVec 64)
      (hStep : stepInstr q i s = some s')
      (hRest : SuffixReach prog q rest s' v) :
      SuffixReach prog q (i :: rest) s v
  | call (fnName : String) (rest : List Instr) (s s' : State) (v : BitVec 64)
      (hBridge : ∀ vFinal,
        s.curBody[s.pc]? = some (.call fnName) →
        Reach prog q s' vFinal →
        Reach prog q s vFinal)
      (hBody : s'.curBody = s.curBody)
      (hPc : s'.pc = s.pc + 1)
      (hRest : SuffixReach prog q rest s' v) :
      SuffixReach prog q (.call fnName :: rest) s v

/-- Pre-proved per-instruction suffix step rule for Arch 2 (`step_instr`). -/
theorem step_instr {prog : MirProg} {q : BranchEnv}
    (i : Instr) (rest : List Instr) (s s' : State) (v : BitVec 64)
    (hStep : stepInstrStrict q i s = some s')
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q (i :: rest) s v := by
  rw [stepInstrStrict_eq] at hStep
  exact SuffixReach.cons i rest s s' v hStep hRest

/-- Flat-tuple inlined 12-step call rule for Stage 2 (`inlineCoreCall12_flat`):
    steps through the 12 transitions of an inlined 10-instruction `core` helper
    using explicit constructor tuples (avoiding `{ s with ... }` $O(6^K)$ tree
    blowup and continuation lambdas, while still stepping through the callee). -/
theorem inlineCoreCall12_flat {prog : MirProg} {q : BranchEnv}
    (fnName : String) (rest : List Instr)
    (s s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s' : State) (v : BitVec 64)
    (h1 : evalStepStrict prog q s = .step s1)
    (h2 : evalStepStrict prog q s1 = .step s2)
    (h3 : evalStepStrict prog q s2 = .step s3)
    (h4 : evalStepStrict prog q s3 = .step s4)
    (h5 : evalStepStrict prog q s4 = .step s5)
    (h6 : evalStepStrict prog q s5 = .step s6)
    (h7 : evalStepStrict prog q s6 = .step s7)
    (h8 : evalStepStrict prog q s7 = .step s8)
    (h9 : evalStepStrict prog q s8 = .step s9)
    (h10 : evalStepStrict prog q s9 = .step s10)
    (h11 : evalStepStrict prog q s10 = .step s11)
    (h12 : evalStepStrict prog q s11 = .step s')
    (hBody : s'.curBody = s.curBody)
    (hPc : s'.pc = s.pc + 1)
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q (.call fnName :: rest) s v := by
  rw [evalStepStrict_eq] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  refine SuffixReach.call fnName rest s s' v ?_ hBody hPc hRest
  intro vFinal _ hAfter
  exact Reach.step _ _ _ h1
    (Reach.step _ _ _ h2
      (Reach.step _ _ _ h3
        (Reach.step _ _ _ h4
          (Reach.step _ _ _ h5
            (Reach.step _ _ _ h6
              (Reach.step _ _ _ h7
                (Reach.step _ _ _ h8
                  (Reach.step _ _ _ h9
                    (Reach.step _ _ _ h10
                      (Reach.step _ _ _ h11
                        (Reach.step _ _ _ h12 hAfter)))))))))))

theorem evalStep_append_nil (prog : MirProg) (q : BranchEnv)
    (pre : List Instr) (s : State)
    (hBody : s.curBody = pre)
    (hPc : s.pc = pre.length)
    (hStack : s.stack = []) :
    evalStep prog q s = .ret s.r0 := by
  unfold evalStep
  have hNone : s.curBody[s.pc]? = none := by
    rw [hBody, hPc]
    exact List.getElem?_eq_none (Nat.le_refl _)
  rw [hNone, hStack]

theorem evalStep_append_cons (prog : MirProg) (q : BranchEnv)
    (pre : List Instr) (i : Instr) (rest : List Instr)
    (s s' : State)
    (hBody : s.curBody = pre ++ i :: rest)
    (hPc : s.pc = pre.length)
    (hStep : stepInstr q i s = some s') :
    evalStep prog q s = .step s' := by
  unfold evalStep
  have hSome : s.curBody[s.pc]? = some i := by
    rw [hBody, hPc]
    rw [List.getElem?_append_right (Nat.le_refl _)]
    rw [Nat.sub_self]
    rfl
  rw [hSome]
  cases i <;> first | (dsimp only; rw [hStep]) | cases hStep

theorem SuffixReach_imp_Reach_append (prog : MirProg) (q : BranchEnv)
    (pre suf : List Instr) (s : State) (v : BitVec 64)
    (hBody : s.curBody = pre ++ suf)
    (hPc : s.pc = pre.length)
    (hSuf : SuffixReach prog q suf s v) :
    Reach prog q s v := by
  induction hSuf generalizing pre with
  | nil s hStack =>
    rw [List.append_nil] at hBody
    exact Reach.done s s.r0 (evalStep_append_nil prog q pre s hBody hPc hStack)
  | cons i rest s s' v hStep _ ih =>
    have hEval : evalStep prog q s = .step s' :=
      evalStep_append_cons prog q pre i rest s s' hBody hPc hStep
    have hBody' : s'.curBody = (pre ++ [i]) ++ rest := by
      rw [stepInstr_curBody hStep, hBody, List.append_assoc]
      rfl
    have hPc' : s'.pc = (pre ++ [i]).length := by
      rw [stepInstr_pc hStep, hPc, List.length_append, List.length_singleton]
    exact Reach.step s s' v hEval (ih (pre ++ [i]) hBody' hPc')
  | call fnName rest s s' v hBridge hBodyEq hPcEq _ ih =>
    have hAt : s.curBody[s.pc]? = some (Instr.call fnName) := by
      rw [hBody, hPc]
      rw [List.getElem?_append_right (Nat.le_refl _)]
      rw [Nat.sub_self]
      rfl
    have hBody' : s'.curBody = (pre ++ [Instr.call fnName]) ++ rest := by
      rw [hBodyEq, hBody, List.append_assoc]
      rfl
    have hPc' : s'.pc = (pre ++ [Instr.call fnName]).length := by
      rw [hPcEq, hPc, List.length_append, List.length_singleton]
    exact hBridge v hAt (ih (pre ++ [Instr.call fnName]) hBody' hPc')

/-- Bridge theorem lifting `SuffixReach prog q body s v` at `s.curBody = body`
    and `s.pc = 0` to `Trusted.Reach prog q s v`. -/
theorem SuffixReach_imp_Reach (prog : MirProg) (q : BranchEnv)
    (body : List Instr) (s : State) (v : BitVec 64)
    (hBody : s.curBody = body)
    (hPc : s.pc = 0)
    (hSuf : SuffixReach prog q body s v) :
    Reach prog q s v :=
  SuffixReach_imp_Reach_append prog q [] body s v hBody hPc hSuf

/-!
## 5. Layer 2: Fused 5-Instruction Superinstruction Idiom (`step_idiom5`) & Hint Validator
-/

/-- Fused big-step transition for the 5-instruction checked-add + bitwise-mix idiom:
    1. `addCheckedImm .r0 .r0 imm`
    2. `assertNotFlag`
    3. `xor .r1 .r0 .r2`
    4. `shl .r2 .r1 3`
    5. `add .r0 .r0 .r2` -/
def evalIdiom5 (imm : BitVec 64) (s : State) : Option State :=
  State.casesOn s fun curBody pc r0 _r1 r2 r3 _flag stack =>
    if BitVec.uaddOverflow r0 imm then
      none
    else
      let r0_1 := r0 + imm
      let r1_2 := r0_1 ^^^ r2
      let r2_3 := r1_2 <<< 3
      let r0_4 := r0_1 + r2_3
      some ⟨curBody, pc + 5, r0_4, r1_2, r2_3, r3, false, stack⟩

/-- Pre-proved big-step soundness rule for the 5-instruction idiom. -/
theorem step_idiom5 {prog : MirProg} {q : BranchEnv}
    (imm : BitVec 64) (rest : List Instr)
    (s s' : State) (v : BitVec 64)
    (hIdiom : evalIdiom5 imm s = some s')
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q
      (.addCheckedImm .r0 .r0 imm ::
       .assertNotFlag ::
       .xor .r1 .r0 .r2 ::
       .shl .r2 .r1 3 ::
       .add .r0 .r0 .r2 :: rest) s v := by
  cases s with
  | mk curBody pc r0 r1 r2 r3 flag stack =>
    unfold evalIdiom5 at hIdiom
    dsimp at hIdiom
    cases hOv : BitVec.uaddOverflow r0 imm with
    | true =>
      rw [hOv] at hIdiom
      cases hIdiom
    | false =>
      rw [hOv] at hIdiom
      dsimp at hIdiom
      injection hIdiom with hs'
      subst hs'
      let s1 : State := ⟨curBody, pc + 1, r0 + imm, r1, r2, r3, false, stack⟩
      let s2 : State := ⟨curBody, pc + 1 + 1, r0 + imm, r1, r2, r3, false, stack⟩
      let s3 : State := ⟨curBody, pc + 1 + 1 + 1, r0 + imm, (r0 + imm) ^^^ r2, r2, r3, false, stack⟩
      let s4 : State := ⟨curBody, pc + 1 + 1 + 1 + 1, r0 + imm, (r0 + imm) ^^^ r2,
        ((r0 + imm) ^^^ r2) <<< 3, r3, false, stack⟩
      have h1 : stepInstr q (.addCheckedImm .r0 .r0 imm) ⟨curBody, pc, r0, r1, r2, r3, flag, stack⟩ = some s1 := by
        dsimp [stepInstr, State.getReg, State.setRegFlagNext, s1]
        rw [hOv]
      have h2 : stepInstr q .assertNotFlag s1 = some s2 := rfl
      have h3 : stepInstr q (.xor .r1 .r0 .r2) s2 = some s3 := rfl
      have h4 : stepInstr q (.shl .r2 .r1 3) s3 = some s4 := rfl
      have h5 : stepInstr q (.add .r0 .r0 .r2) s4 =
          some ⟨curBody, pc + 5, (r0 + imm) + (((r0 + imm) ^^^ r2) <<< 3),
            (r0 + imm) ^^^ r2, ((r0 + imm) ^^^ r2) <<< 3, r3, false, stack⟩ := rfl
      exact SuffixReach.cons _ _ _ _ _ h1
        (SuffixReach.cons _ _ _ _ _ h2
          (SuffixReach.cons _ _ _ _ _ h3
            (SuffixReach.cons _ _ _ _ _ h4
              (SuffixReach.cons _ _ _ _ _ h5 hRest))))

/-- Expand a hint list `imms : List (BitVec 64)` of 5-instruction idiom
    immediates into its concrete instruction sequence. -/
def buildIdiomProg : List (BitVec 64) → List Instr
  | [] => []
  | imm :: rest =>
    .addCheckedImm .r0 .r0 imm ::
    .assertNotFlag ::
    .xor .r1 .r0 .r2 ::
    .shl .r2 .r1 3 ::
    .add .r0 .r0 .r2 ::
    buildIdiomProg rest

/-- Hint-driven validator (`SymPlan` / `IdiomPlan`) that
    evaluates a sequence of fused 5-instruction idioms using pre-emitted
    immediate hints without scanning the AST in the kernel. -/
def evalIdiomPlan : List (BitVec 64) → State → Option State
  | [], s => some s
  | imm :: rest, s =>
    match evalIdiom5 imm s with
    | some s' => evalIdiomPlan rest s'
    | none => none

theorem evalIdiomPlan_sound {prog : MirProg} {q : BranchEnv}
    (imms : List (BitVec 64)) (rest : List Instr)
    (s s' : State) (v : BitVec 64)
    (hPlan : evalIdiomPlan imms s = some s')
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q (buildIdiomProg imms ++ rest) s v := by
  induction imms generalizing s with
  | nil =>
    injection hPlan with hs
    subst hs
    exact hRest
  | cons imm tail ih =>
    dsimp [evalIdiomPlan] at hPlan
    cases hStep : evalIdiom5 imm s with
    | none =>
      rw [hStep] at hPlan
      cases hPlan
    | some s1 =>
      rw [hStep] at hPlan
      exact step_idiom5 imm (buildIdiomProg tail ++ rest) s s1 v hStep (ih s1 hPlan)

/-!
## 6. Layer 2: `cv_trans`-Style Fast GMP `Nat`-Domain Reflection (`evalCvProg_sound`)
-/

/-- 64-bit modulus `2^64`. -/
def MOD64 : Nat := 18446744073709551616

/-- 64-bit bitmask `2^64 - 1 = 0xFFFFFFFFFFFFFFFF`. -/
def MASK64 : Nat := 18446744073709551615

/-- Flat `Nat`-only state for C++ kernel GMP evaluation (`reduce_nat`).
    Omits `curBody` and `stack` so kernel reduction touches only 5 `Nat` fields
    and 1 `Bool`. -/
structure CvState where
  pc   : Nat
  r0   : Nat
  r1   : Nat
  r2   : Nat
  r3   : Nat
  flag : Bool
  deriving DecidableEq, Repr

/-- Project a typed `State` to a flat `CvState`. -/
def toCvState (s : State) : CvState where
  pc   := s.pc
  r0   := s.r0.toNat
  r1   := s.r1.toNat
  r2   := s.r2.toNat
  r3   := s.r3.toNat
  flag := s.flag

def CvState.getReg (cs : CvState) : Reg → Nat
  | .r0 => cs.r0
  | .r1 => cs.r1
  | .r2 => cs.r2
  | .r3 => cs.r3

def CvState.setRegNext (cs : CvState) (r : Reg) (v : Nat) : CvState :=
  match r with
  | .r0 => ⟨Nat.add cs.pc 1, v, cs.r1, cs.r2, cs.r3, cs.flag⟩
  | .r1 => ⟨Nat.add cs.pc 1, cs.r0, v, cs.r2, cs.r3, cs.flag⟩
  | .r2 => ⟨Nat.add cs.pc 1, cs.r0, cs.r1, v, cs.r3, cs.flag⟩
  | .r3 => ⟨Nat.add cs.pc 1, cs.r0, cs.r1, cs.r2, v, cs.flag⟩

def CvState.setRegFlagNext (cs : CvState) (r : Reg) (v : Nat) (fl : Bool) : CvState :=
  match r with
  | .r0 => ⟨Nat.add cs.pc 1, v, cs.r1, cs.r2, cs.r3, fl⟩
  | .r1 => ⟨Nat.add cs.pc 1, cs.r0, v, cs.r2, cs.r3, fl⟩
  | .r2 => ⟨Nat.add cs.pc 1, cs.r0, cs.r1, v, cs.r3, fl⟩
  | .r3 => ⟨Nat.add cs.pc 1, cs.r0, cs.r1, cs.r2, v, fl⟩

/-- Evaluate one instruction in the `cv_trans` domain using exclusively C++
    kernel GMP primitives (`Nat.add`, `Nat.sub`, `Nat.land`, `Nat.xor`,
    `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.ble`), replacing modular division
    `% 2^64` with `Nat.land _ MASK64`. -/
def stepCvInstr (i : Instr) (cs : CvState) : Option CvState :=
  match i with
  | .add dst src1 src2 =>
    some (cs.setRegNext dst (Nat.land (Nat.add (cs.getReg src1) (cs.getReg src2)) MASK64))
  | .sub dst src1 src2 =>
    some (cs.setRegNext dst
      (Nat.land (Nat.add (Nat.sub MOD64 (cs.getReg src2)) (cs.getReg src1)) MASK64))
  | .xor dst src1 src2 =>
    some (cs.setRegNext dst (Nat.xor (cs.getReg src1) (cs.getReg src2)))
  | .band dst src1 src2 =>
    some (cs.setRegNext dst (Nat.land (cs.getReg src1) (cs.getReg src2)))
  | .shl dst src amt =>
    some (cs.setRegNext dst (Nat.land (Nat.shiftLeft (cs.getReg src) amt) MASK64))
  | .shr dst src amt =>
    some (cs.setRegNext dst (Nat.shiftRight (cs.getReg src) amt))
  | .addImm dst src imm =>
    some (cs.setRegNext dst (Nat.land (Nat.add (cs.getReg src) imm.toNat) MASK64))
  | .addCheckedImm dst src imm =>
    let v := cs.getReg src
    let sum := Nat.add v imm.toNat
    let ov := Nat.ble MOD64 sum
    some (cs.setRegFlagNext dst (Nat.land sum MASK64) ov)
  | .assertNotFlag =>
    if cs.flag then none
    else some ⟨Nat.add cs.pc 1, cs.r0, cs.r1, cs.r2, cs.r3, cs.flag⟩
  | .selectImm _ _ _ _ => none
  | .call _ => none

/-- Total `cv_trans` suffix evaluator over flat `Nat` values. -/
def evalCvSuffix (code : List Instr) (cs : CvState) : Option Nat :=
  match code with
  | [] => some cs.r0
  | i :: rest =>
    match stepCvInstr i cs with
    | some cs' => evalCvSuffix rest cs'
    | none => none

theorem land_mask64_eq_mod (x : Nat) :
    Nat.land x MASK64 = x % (2 ^ 64) :=
  Nat.and_two_pow_sub_one_eq_mod x 64

theorem getReg_toCvState (s : State) (r : Reg) :
    (toCvState s).getReg r = (s.getReg r).toNat := by
  cases r <;> rfl

theorem setRegNext_toCvState (s : State) (r : Reg) (v : BitVec 64) :
    (toCvState s).setRegNext r v.toNat = toCvState (s.setRegNext r v) := by
  cases r <;> rfl

theorem setRegFlagNext_toCvState (s : State) (r : Reg) (v : BitVec 64) (fl : Bool) :
    (toCvState s).setRegFlagNext r v.toNat fl = toCvState (s.setRegFlagNext r v fl) := by
  cases r <;> rfl

theorem ble_mod64_eq_uaddOverflow (a b : BitVec 64) :
    Nat.ble MOD64 (a.toNat + b.toNat) = BitVec.uaddOverflow a b := by
  unfold BitVec.uaddOverflow MOD64
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

/-- Step simulation from `stepCvInstr` (flat GMP `Nat`) to `stepInstr` (`BitVec 64`)
    for arbitrary branch environment `q : BranchEnv`. -/
theorem stepCvInstr_sound (q : BranchEnv) (i : Instr) (s : State) (cs' : CvState)
    (h : stepCvInstr i (toCvState s) = some cs') :
    ∃ s', stepInstr q i s = some s' ∧ toCvState s' = cs' := by
  cases i with
  | add dst src1 src2 =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState, getReg_toCvState] at h
    have hVal : ((s.getReg src1).toNat + (s.getReg src2).toNat) &&& MASK64 =
        (s.getReg src1 + s.getReg src2).toNat := by
      change Nat.land (Nat.add (s.getReg src1).toNat (s.getReg src2).toNat) MASK64 = _
      rw [land_mask64_eq_mod]; rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | sub dst src1 src2 =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState, getReg_toCvState] at h
    have hVal : (MOD64 - (s.getReg src2).toNat + (s.getReg src1).toNat) &&& MASK64 =
        (s.getReg src1 - s.getReg src2).toNat := by
      change Nat.land (Nat.add (Nat.sub MOD64 (s.getReg src2).toNat) (s.getReg src1).toNat) MASK64 = _
      rw [land_mask64_eq_mod]; rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | xor dst src1 src2 =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState, getReg_toCvState] at h
    have hVal : (s.getReg src1).toNat ^^^ (s.getReg src2).toNat =
        (s.getReg src1 ^^^ s.getReg src2).toNat := rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | band dst src1 src2 =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState, getReg_toCvState] at h
    have hVal : (s.getReg src1).toNat &&& (s.getReg src2).toNat =
        (s.getReg src1 &&& s.getReg src2).toNat := rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | shl dst src amt =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState] at h
    have hVal : ((s.getReg src).toNat <<< amt) &&& MASK64 =
        (s.getReg src <<< amt).toNat := by
      change Nat.land (Nat.shiftLeft (s.getReg src).toNat amt) MASK64 = _
      rw [land_mask64_eq_mod]; rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | shr dst src amt =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState] at h
    have hVal : (s.getReg src).toNat >>> amt =
        (s.getReg src >>> amt).toNat := rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | addImm dst src imm =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState] at h
    have hVal : ((s.getReg src).toNat + imm.toNat) &&& MASK64 =
        (s.getReg src + imm).toNat := by
      change Nat.land (Nat.add (s.getReg src).toNat imm.toNat) MASK64 = _
      rw [land_mask64_eq_mod]; rfl
    rw [hVal, setRegNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | addCheckedImm dst src imm =>
    dsimp [stepCvInstr] at h
    rw [getReg_toCvState] at h
    have hVal : ((s.getReg src).toNat + imm.toNat) &&& MASK64 =
        (s.getReg src + imm).toNat := by
      change Nat.land (Nat.add (s.getReg src).toNat imm.toNat) MASK64 = _
      rw [land_mask64_eq_mod]; rfl
    have hOv : MOD64.ble ((s.getReg src).toNat + imm.toNat) =
        BitVec.uaddOverflow (s.getReg src) imm :=
      ble_mod64_eq_uaddOverflow (s.getReg src) imm
    rw [hVal, hOv, setRegFlagNext_toCvState] at h
    injection h with hcs
    exact ⟨_, rfl, hcs⟩
  | assertNotFlag =>
    dsimp [stepCvInstr, toCvState] at h
    cases hFlag : s.flag with
    | true =>
      rw [hFlag] at h
      cases h
    | false =>
      rw [hFlag] at h
      dsimp at h
      injection h with hcs
      exact ⟨⟨s.curBody, s.pc + 1, s.r0, s.r1, s.r2, s.r3, false, s.stack⟩,
        by dsimp [stepInstr]; rw [hFlag]; rfl,
        by rw [← hcs]; dsimp [toCvState]⟩
  | selectImm _ _ _ _ => cases h
  | call _ => cases h

theorem evalCvSuffix_sound (prog : MirProg) (q : BranchEnv)
    (code : List Instr) (s : State) (v : BitVec 64)
    (hStack : s.stack = [])
    (hCv : evalCvSuffix code (toCvState s) = some v.toNat) :
    SuffixReach prog q code s v := by
  induction code generalizing s with
  | nil =>
    dsimp [evalCvSuffix, toCvState] at hCv
    injection hCv with hNat
    have hv : s.r0 = v := BitVec.eq_of_toNat_eq hNat
    rw [← hv]
    exact SuffixReach.nil s hStack
  | cons i rest ih =>
    dsimp [evalCvSuffix] at hCv
    cases hStepCv : stepCvInstr i (toCvState s) with
    | none =>
      rw [hStepCv] at hCv
      cases hCv
    | some cs' =>
      rw [hStepCv] at hCv
      have ⟨s', hStep, hToCv⟩ := stepCvInstr_sound q i s cs' hStepCv
      rw [← hToCv] at hCv
      have hStack' : s'.stack = [] := by
        rw [stepInstr_stack hStep, hStack]
      exact SuffixReach.cons i rest s s' v hStep (ih s' hStack' hCv)

/-- Arch 6 (`cv_trans`) reflection theorem: a single `rfl` proof of
    `evalCvSuffix body (toCvState (entryState body)) = some v.toNat` yields
    `Trusted.Reach prog q (entryState body) v` for all `q : BranchEnv`. -/
theorem evalCvProg_sound (prog : MirProg) (q : BranchEnv)
    (body : List Instr) (v : BitVec 64)
    (hCv : evalCvSuffix body (toCvState (entryState body)) = some v.toNat) :
    Reach prog q (entryState body) v :=
  SuffixReach_imp_Reach prog q body (entryState body) v rfl rfl
    (evalCvSuffix_sound prog q body (entryState body) v rfl hCv)

/-!
## 7. Layer 3: Cut-Point Diamond Convergence, Interprocedural Call Summaries, and Loops
-/

/-- Evaluate one instruction when branch condition `k` is specialized to `condVal : Bool`. -/
def stepInstrAt (k : Nat) (condVal : Bool) (i : Instr) (s : State) : Option State :=
  match i with
  | .selectImm condIdx dst immT immF =>
    if Nat.beq condIdx k then
      some (s.setRegNext dst (if condVal then immT else immF))
    else
      none
  | _ => stepInstr defaultBranchEnv i s

def stepInstrAtStrict (k : Nat) (condVal : Bool) (i : Instr) (s : State) : Option State :=
  State.casesOn s fun curBody pc r0 r1 r2 r3 flag stack =>
    stepInstrAt k condVal i ⟨curBody, pc, r0, r1, r2, r3, flag, stack⟩

theorem stepInstrAtStrict_imp_stepInstr (q : BranchEnv) (k : Nat) (i : Instr) (s s' : State)
    (h : stepInstrAtStrict k (q.getCond k) i s = some s') :
    stepInstr q i s = some s' := by
  cases s with
  | mk curBody pc r0 r1 r2 r3 flag stack =>
    dsimp [stepInstrAtStrict] at h
    cases i <;> first | exact h | skip
    case selectImm condIdx dst immT immF =>
      dsimp [stepInstrAt] at h
      cases hEq : Nat.beq condIdx k with
      | false =>
        rw [hEq] at h
        cases h
      | true =>
        rw [hEq] at h
        have hIdx : condIdx = k := Nat.eq_of_beq_eq_true hEq
        subst hIdx
        exact h

/-- Evaluate a basic block `blk` with condition `k` specialized to `condVal : Bool`. -/
def evalBlockAt (k : Nat) (condVal : Bool) (blk : List Instr) (s : State) : Option State :=
  match blk with
  | [] => some s
  | i :: rest =>
    match stepInstrAtStrict k condVal i s with
    | some s' => evalBlockAt k condVal rest s'
    | none => none

theorem evalBlockAt_step (prog : MirProg) (q : BranchEnv)
    (k : Nat) (blk rest : List Instr) (s s' : State) (v : BitVec 64)
    (hBlk : evalBlockAt k (q.getCond k) blk s = some s')
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q (blk ++ rest) s v := by
  induction blk generalizing s with
  | nil =>
    injection hBlk with hs
    subst hs
    exact hRest
  | cons i blkTail ih =>
    dsimp [evalBlockAt] at hBlk
    cases hStep : stepInstrAtStrict k (q.getCond k) i s with
    | none =>
      rw [hStep] at hBlk
      cases hBlk
    | some s1 =>
      rw [hStep] at hBlk
      exact SuffixReach.cons i (blkTail ++ rest) s s1 v
        (stepInstrAtStrict_imp_stepInstr q k i s s1 hStep)
        (ih s1 hBlk)

/-- **Layer 3 Cut-Point Diamond Convergence (`diamond_converge_step`):**
    Evaluates both branch outcomes `condVal = true` (`hT`) and `condVal = false`
    (`hF`) of diamond `k` over `blk` (`2` closed ground `rfl` reductions with
    `has_fvar == false`) to reach cut-point state `sJoin`, then continues
    verification of `rest` once from `sJoin` ($O(D)$ instead of $O(2^D)$!). -/
theorem diamond_converge_step (prog : MirProg) (q : BranchEnv)
    (k : Nat) (blk rest : List Instr) (s sJoin : State) (v : BitVec 64)
    (hT : evalBlockAt k true blk s = some sJoin)
    (hF : evalBlockAt k false blk s = some sJoin)
    (hRest : SuffixReach prog q rest sJoin v) :
    SuffixReach prog q (blk ++ rest) s v := by
  apply evalBlockAt_step prog q k blk rest s sJoin v ?_ hRest
  cases q.getCond k with
  | true => exact hT
  | false => exact hF

/-- Evaluate one branch-free instruction, unpacking `s` via `State.casesOn`. -/
def stepInstrNoBranchStrict (i : Instr) (s : State) : Option State :=
  State.casesOn s fun curBody pc r0 r1 r2 r3 flag stack =>
    match i with
    | .selectImm _ _ _ _ => none
    | .call _ => none
    | _ => stepInstr defaultBranchEnv i ⟨curBody, pc, r0, r1, r2, r3, flag, stack⟩

/-- Evaluate a branch-free basic block `blk` from `s` to its post-block state. -/
def evalBlock (blk : List Instr) (s : State) : Option State :=
  match blk with
  | [] => some s
  | i :: rest =>
    match stepInstrNoBranchStrict i s with
    | some s' => evalBlock rest s'
    | none => none

theorem evalBlock_step (prog : MirProg) (q : BranchEnv)
    (blk rest : List Instr) (s s' : State) (v : BitVec 64)
    (hBlk : evalBlock blk s = some s')
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q (blk ++ rest) s v := by
  induction blk generalizing s with
  | nil =>
    injection hBlk with hs
    subst hs
    exact hRest
  | cons i blkTail ih =>
    dsimp [evalBlock] at hBlk
    cases hStep : stepInstrNoBranchStrict i s with
    | none =>
      rw [hStep] at hBlk
      cases hBlk
    | some s1 =>
      rw [hStep] at hBlk
      have hStepQ : stepInstr q i s = some s1 := by
        cases s; dsimp [stepInstrNoBranchStrict] at hStep
        cases i <;> first | exact hStep | cases hStep
      exact SuffixReach.cons i (blkTail ++ rest) s s1 v hStepQ (ih s1 hBlk)

/-- **Layer 3 Universal Stack-Lifting Interprocedural Call Summary (`CalleeSummary`):**
    States that for any caller state `s` at `Instr.call fnName` and any call
    stack `s.stack`, if `specFn s.r0 s.r1 = some vOut`, then `s` steps through
    `calleeBody` and returns to `s.pc + 1` with `r0 = vOut`. -/
def CalleeSummary (prog : MirProg) (fnName : String)
    (specFn : BitVec 64 → BitVec 64 → Option (BitVec 64)) : Prop :=
  ∀ (q : BranchEnv) (callerBody : List Instr) (pc : Nat)
    (r0 r1 r2 r3 vOut vFinal : BitVec 64) (flag : Bool) (stack : List CallFrame),
    callerBody[pc]? = some (.call fnName) →
    specFn r0 r1 = some vOut →
    Reach prog q ⟨callerBody, pc + 1, vOut, r1, r2, r3, false, stack⟩ vFinal →
    Reach prog q ⟨callerBody, pc, r0, r1, r2, r3, flag, stack⟩ vFinal

/-- Strict call-summary evaluator unpacking `s : State` via `State.casesOn` at
    entry so `let`-bound cut-point states unfold before `specFn` arithmetic is
    reduced by C++ GMP. -/
def evalCallSummary (specFn : BitVec 64 → BitVec 64 → Option (BitVec 64))
    (s : State) : Option State :=
  State.casesOn s fun curBody pc r0 r1 r2 r3 _flag stack =>
    match specFn r0 r1 with
    | some vOut => some ⟨curBody, pc + 1, vOut, r1, r2, r3, false, stack⟩
    | none => none

/-- **Layer 3 Single-Step Call Summary Rule (`call_summary_flat_step`):**
    Discharges `Instr.call fnName` in 1 step using a pre-proved `CalleeSummary`. -/
theorem call_summary_flat_step {prog : MirProg} {q : BranchEnv}
    {fnName : String} {specFn : BitVec 64 → BitVec 64 → Option (BitVec 64)}
    (hSummary : CalleeSummary prog fnName specFn)
    (rest : List Instr) (s s' : State) (v : BitVec 64)
    (hEval : evalCallSummary specFn s = some s')
    (hRest : SuffixReach prog q rest s' v) :
    SuffixReach prog q (.call fnName :: rest) s v := by
  cases s with
  | mk curBody pc r0 r1 r2 r3 flag stack =>
    dsimp [evalCallSummary] at hEval
    cases hSpec : specFn r0 r1 with
    | none =>
      rw [hSpec] at hEval
      cases hEval
    | some vOut =>
      rw [hSpec] at hEval
      injection hEval with hs'
      subst hs'
      refine SuffixReach.call fnName rest
        ⟨curBody, pc, r0, r1, r2, r3, flag, stack⟩
        ⟨curBody, pc + 1, vOut, r1, r2, r3, false, stack⟩
        v ?_ rfl rfl hRest
      intro vFinal hAt hAfter
      exact hSummary q curBody pc r0 r1 r2 r3 vOut vFinal flag stack hAt hSpec hAfter

/-- Canonical 10-instruction `core` intrinsic/helper body template used by
    `size_of`, `checked_add`, `NonZeroUsize::new`, and `Option::unwrap_or`. -/
def mkCoreCalleeBody (imm1 imm2 : BitVec 64) : List Instr :=
  [ .addCheckedImm .r0 .r0 imm1,
    .assertNotFlag,
    .xor .r1 .r0 .r1,
    .shl .r2 .r1 3,
    .add .r0 .r0 .r2,
    .addImm .r0 .r0 imm2,
    .xor .r1 .r0 .r2,
    .shr .r2 .r1 2,
    .add .r0 .r0 .r2,
    .add .r0 .r0 .r1 ]

/-- Pure mathematical specification of `mkCoreCalleeBody imm1 imm2`.
    Returns `none` when `r0 + imm1` overflows 64 bits (fail-closed!). -/
def mkCoreCalleeSpec (imm1 imm2 r0 r1 : BitVec 64) : Option (BitVec 64) :=
  if BitVec.uaddOverflow r0 imm1 then
    none
  else
    let r0_1 := r0 + imm1
    let r1_2 := r0_1 ^^^ r1
    let r2_3 := r1_2 <<< 3
    let r0_4 := r0_1 + r2_3
    let r0_5 := r0_4 + imm2
    let r1_6 := r0_5 ^^^ r2_3
    let r2_7 := r1_6 >>> 2
    let r0_8 := r0_5 + r2_7
    some (r0_8 + r1_6)

/-- **Pre-Proved Universal Summary Schema for `mkCoreCalleeBody` (`mkCoreCalleeBody_summary`):**
    Proved once in `Theory` for arbitrary symbolic arguments `(r0, r1 : BitVec 64)`,
    arbitrary caller body/PC, and arbitrary call stack `stack : List CallFrame`. -/
theorem mkCoreCalleeBody_summary (prog : MirProg) (fnName : String)
    (imm1 imm2 : BitVec 64)
    (hLookup : lookupFn prog fnName = some (mkCoreCalleeBody imm1 imm2)) :
    CalleeSummary prog fnName (mkCoreCalleeSpec imm1 imm2) := by
  intro q callerBody pc r0 r1 r2 r3 vOut vFinal flag stack hAt hSpec hAfter
  unfold mkCoreCalleeSpec at hSpec
  cases hOv : BitVec.uaddOverflow r0 imm1 with
  | true =>
    rw [hOv] at hSpec
    cases hSpec
  | false =>
    rw [hOv] at hSpec
    dsimp at hSpec
    injection hSpec with hvOut
    subst hvOut
    let cb := mkCoreCalleeBody imm1 imm2
    let fr : CallFrame := ⟨callerBody, pc + 1, r1, r2, r3⟩
    let stk := fr :: stack
    let r0_1 := r0 + imm1
    let r1_2 := r0_1 ^^^ r1
    let r2_3 := r1_2 <<< 3
    let r0_4 := r0_1 + r2_3
    let r0_5 := r0_4 + imm2
    let r1_6 := r0_5 ^^^ r2_3
    let r2_7 := r1_6 >>> 2
    let r0_8 := r0_5 + r2_7
    let r0_9 := r0_8 + r1_6
    have hCallStep : evalStep prog q ⟨callerBody, pc, r0, r1, r2, r3, flag, stack⟩ =
        .step ⟨cb, 0, r0, r1, 0#64, 0#64, false, stk⟩ := by
      unfold evalStep
      rw [hAt]; dsimp; rw [hLookup]
    have hs1 : evalStep prog q ⟨cb, 0, r0, r1, 0#64, 0#64, false, stk⟩ =
        .step ⟨cb, 1, r0_1, r1, 0#64, 0#64, false, stk⟩ := by
      change (match stepInstr q (.addCheckedImm .r0 .r0 imm1)
        ⟨cb, 0, r0, r1, 0#64, 0#64, false, stk⟩ with
        | some s' => StepOut.step s' | none => StepOut.trap) = _
      dsimp [stepInstr, State.getReg, State.setRegFlagNext]
      rw [hOv]
    have hs2 : evalStep prog q ⟨cb, 1, r0_1, r1, 0#64, 0#64, false, stk⟩ =
        .step ⟨cb, 2, r0_1, r1, 0#64, 0#64, false, stk⟩ := rfl
    have hs3 : evalStep prog q ⟨cb, 2, r0_1, r1, 0#64, 0#64, false, stk⟩ =
        .step ⟨cb, 3, r0_1, r1_2, 0#64, 0#64, false, stk⟩ := rfl
    have hs4 : evalStep prog q ⟨cb, 3, r0_1, r1_2, 0#64, 0#64, false, stk⟩ =
        .step ⟨cb, 4, r0_1, r1_2, r2_3, 0#64, false, stk⟩ := rfl
    have hs5 : evalStep prog q ⟨cb, 4, r0_1, r1_2, r2_3, 0#64, false, stk⟩ =
        .step ⟨cb, 5, r0_4, r1_2, r2_3, 0#64, false, stk⟩ := rfl
    have hs6 : evalStep prog q ⟨cb, 5, r0_4, r1_2, r2_3, 0#64, false, stk⟩ =
        .step ⟨cb, 6, r0_5, r1_2, r2_3, 0#64, false, stk⟩ := rfl
    have hs7 : evalStep prog q ⟨cb, 6, r0_5, r1_2, r2_3, 0#64, false, stk⟩ =
        .step ⟨cb, 7, r0_5, r1_6, r2_3, 0#64, false, stk⟩ := rfl
    have hs8 : evalStep prog q ⟨cb, 7, r0_5, r1_6, r2_3, 0#64, false, stk⟩ =
        .step ⟨cb, 8, r0_5, r1_6, r2_7, 0#64, false, stk⟩ := rfl
    have hs9 : evalStep prog q ⟨cb, 8, r0_5, r1_6, r2_7, 0#64, false, stk⟩ =
        .step ⟨cb, 9, r0_8, r1_6, r2_7, 0#64, false, stk⟩ := rfl
    have hs10 : evalStep prog q ⟨cb, 9, r0_8, r1_6, r2_7, 0#64, false, stk⟩ =
        .step ⟨cb, 10, r0_9, r1_6, r2_7, 0#64, false, stk⟩ := rfl
    have hsRet : evalStep prog q ⟨cb, 10, r0_9, r1_6, r2_7, 0#64, false, stk⟩ =
        .step ⟨callerBody, pc + 1, r0_9, r1, r2, r3, false, stack⟩ := rfl
    exact Reach.step _ _ _ hCallStep
      (Reach.step _ _ _ hs1
        (Reach.step _ _ _ hs2
          (Reach.step _ _ _ hs3
            (Reach.step _ _ _ hs4
              (Reach.step _ _ _ hs5
                (Reach.step _ _ _ hs6
                  (Reach.step _ _ _ hs7
                    (Reach.step _ _ _ hs8
                      (Reach.step _ _ _ hs9
                        (Reach.step _ _ _ hs10
                          (Reach.step _ _ _ hsRet hAfter)))))))))))

/-- Bounded loop iteration of `body` `k` times. -/
def loopCode (k : Nat) (body : List Instr) : List Instr :=
  match k with
  | 0 => []
  | n + 1 => body ++ loopCode n body

/-- **Layer 3 Counted / Symbolic Loop Summary (`loop_summary_sound`):**
    If one iteration of `body` transforms `inv i` into `inv (i + 1)`, then
    `loopCode k body` transforms `inv 0` into `inv k` in $O(1)$ proof size for
    any concrete or symbolic trip count `k : Nat`. -/
theorem loop_summary_sound (prog : MirProg) (q : BranchEnv)
    {body : List Instr} (inv : Nat → State)
    (hStepInv : ∀ i, evalBlock body (inv i) = some (inv (i + 1)))
    (k : Nat) (rest : List Instr) (v : BitVec 64)
    (hRest : SuffixReach prog q rest (inv k) v) :
    SuffixReach prog q (loopCode k body ++ rest) (inv 0) v := by
  have hGen : ∀ idx k,
      SuffixReach prog q rest (inv (idx + k)) v →
      SuffixReach prog q (loopCode k body ++ rest) (inv idx) v := by
    intro idx k
    induction k generalizing idx with
    | zero =>
      intro hR
      rw [Nat.add_zero] at hR
      exact hR
    | succ n ih =>
      intro hR
      dsimp [loopCode]
      rw [List.append_assoc]
      apply evalBlock_step prog q body (loopCode n body ++ rest)
        (inv idx) (inv (idx + 1)) v (hStepInv idx)
      have hEq : idx + 1 + n = idx + (n + 1) := by omega
      rw [← hEq] at hR
      exact ih (idx + 1) hR
  have h0 : 0 + k = k := Nat.zero_add k
  rw [← h0] at hRest
  exact hGen 0 k hRest

/-- Canonical 5-instruction counted-loop body (`r0 := r0 + 7#64`, advancing `pc` by `5`). -/
def loopBody5 : List Instr :=
  [ .addImm .r0 .r0 1#64,
    .addImm .r0 .r0 2#64,
    .addImm .r0 .r0 1#64,
    .addImm .r0 .r0 2#64,
    .addImm .r0 .r0 1#64 ]

def loopR0 : Nat → BitVec 64
  | 0 => 7#64
  | i + 1 => loopR0 i + 7#64

def loopInv (curBody : List Instr) (i : Nat) : State :=
  ⟨curBody, 5 * i, loopR0 i, 0#64, 3#64, 0#64, false, []⟩

theorem loopBody5_step (curBody : List Instr) (i : Nat) :
    evalBlock loopBody5 (loopInv curBody i) = some (loopInv curBody (i + 1)) := by
  dsimp [loopBody5, loopInv, loopR0, evalBlock, stepInstrNoBranchStrict,
    stepInstr, State.getReg, State.setRegNext]
  simp only [BitVec.add_assoc]
  rfl

/-!
## 8. Positive & Negative Soundness Canaries (Task 2: 100% Fail-Closed Verification)
-/

/-- **Canary 1A (Positive Boundary):** 64-bit checked addition right at the
    non-overflow boundary `(2^64 - 2) + 1 = 2^64 - 1` succeeds in both
    `evalCvSuffix` and `evalIdiom5`. -/
theorem canary1_pos_boundary_cv :
    evalCvSuffix [.addCheckedImm .r0 .r0 1#64, .assertNotFlag]
      ⟨0, 18446744073709551614, 0, 0, 0, false⟩ =
      some 18446744073709551615 := rfl

/-- **Canary 1B (Negative — Off-by-One 64-Bit Overflow Guard):**
    Increasing the operand by 1 (`(2^64 - 1) + 1 = 2^64`) sets `flag := true`
    and causes `.assertNotFlag` to trap, making both `evalCvSuffix` and
    `evalIdiom5` evaluate to `none` (100% fail-closed). -/
theorem canary1_neg_overflow_cv :
    evalCvSuffix [.addCheckedImm .r0 .r0 1#64, .assertNotFlag]
      ⟨0, 18446744073709551615, 0, 0, 0, false⟩ = none := rfl

theorem canary1_neg_overflow_idiom5 :
    evalIdiom5 1#64 ⟨[], 0, 0xFFFFFFFFFFFFFFFF#64, 0#64, 3#64, 0#64, false, []⟩ =
      none := rfl

/-- **Canary 2A (Positive Boundary):** Adjacent byte intervals `[100, 116)` and
    `[116, 132)`, exact aligned round-up `off = 13, align = 8, out = 16`, and
    symbolic subrange `off = 8, sublen = 8, totallen = 16` evaluate
    `checkSideCondBatch` to `true`. -/
theorem canary2_pos_side_conds :
    checkSideCondBatch [
      .disjoint 100 16 116 16,
      .aligned 13 8 16,
      .subrange 8 8 16
    ] = true := rfl

/-- **Canary 2B (Negative — Overlapping Intervals, Misaligned Offset, and
    Out-of-Bounds Symbolic Subrange):**
    Off-by-one violations on each of the 3 side-condition types evaluate
    `checkSideCond` and `checkSideCondBatch` to `false` (100% fail-closed). -/
theorem canary2_neg_overlapping_interval :
    checkSideCond (.disjoint 100 16 115 16) = false := rfl

theorem canary2_neg_misaligned_roundup :
    checkSideCond (.aligned 13 8 15) = false := rfl

theorem canary2_neg_oob_subrange :
    checkSideCond (.subrange 9 8 16) = false := rfl

theorem canary2_neg_batch_fails_closed :
    checkSideCondBatch [
      .disjoint 100 16 116 16,
      .disjoint 100 16 115 16,
      .aligned 13 8 16
    ] = false := rfl

/-- **Canary 3A (Negative — Violated Callee Precondition in `evalCallSummary`):**
    Calling `mkCoreCalleeSpec 4#64 12#64` (`checked_add` with `imm1 = 4`) on
    `r0 = 0xFFFFFFFFFFFFFFFD#64` (`2^64 - 3`, which overflows `2^64`) evaluates
    `evalCallSummary` to `none` (100% fail-closed). -/
theorem canary3_neg_callee_precondition_violated :
    evalCallSummary (mkCoreCalleeSpec 4#64 12#64)
      ⟨[.call "core::num::usize::checked_add"], 0,
       0xFFFFFFFFFFFFFFFD#64, 0#64, 0#64, 0#64, false, []⟩ = none := rfl

/-- **Canary 4 (Negative — Legacy `MirLangBroken.sem` Traps on Interprocedural
    `Instr.call`):**
    Demonstrates the bug in `Trusted/MirSemantics.lean:1794`: when `MirLang.sem`
    hardcodes `let prog : MirProg := [("__entry", body)]`, any call to
    `"core::mem::size_of"` fails `lookupFn` (`none`) and steps immediately to
    `.trap`, making `MirLangBroken.sem` unprovable on multi-function crates. -/
theorem canary4_neg_legacy_mirlang_traps_on_call :
    let body := [.call "core::mem::size_of"]
    evalStep [("__entry", body)] defaultBranchEnv (entryState body) = .trap := rfl

/-- **Canary 5 (Negative — Divergent Diamond Arms):**
    When the `true` and `false` arms of a diamond write distinct constants
    (`10#64` vs. `11#64`) to `.r0`, `evalBlockAt 0 true` and `evalBlockAt 0 false`
    produce distinct post-states (`≠`), preventing `diamond_converge_step` from
    merging them to a false common state. -/
theorem canary5_neg_diamond_arms_diverge :
    let badDiamond : List Instr := [.selectImm 0 .r0 10#64 11#64]
    let s0 := entryState badDiamond
    evalBlockAt 0 true badDiamond s0 ≠ evalBlockAt 0 false badDiamond s0 := by
  decide

end Theory
