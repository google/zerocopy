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
# Pre-Proved Theorem Architectures for `Proof.lean` (`BenchmarkProofStrategies.lean`)

This module defines:
1. `Trusted`: A minimal small-step operational semantics over a 64-bit word
   register/local state (`BitVec 64` locals, program counter `pc`, and overflow
   `flag`), providing both forward small-step reachability (`Trusted.Reach`)
   and Anneal's prefix-safety relation (`Trusted.ReachesPrefix`,
   `Trusted.SafeAndEnsures`).
2. `Theory`: Six verification architectures pre-verified at Anneal compile time
   (loaded into `base` before checking `Proof.lean`):
   - **Arch 1 (`Trusted.Reach.step` / `Theory.safeAndEnsures_of_step`):**
     Primitive small-step proof chains embedding intermediate states at every
     step (both flat `Reach.step` and Anneal PR `#81`'s nested-lambda
     continuation `safeAndEnsures_of_step`).
   - **Arch 2 (`Theory.SuffixReach` + `let`-shared functional step rules):**
     Structural instruction-list stepping with `let`-shared intermediate states
     that eliminate $O(N^2)$ program-list indexing and binder re-instantiation.
   - **Arch 3 (`Theory.step_idiom5`):**
     Pre-proved fused 5-instruction basic-block / idiom schemas (checked
     addition + overflow guard + bitwise mix), reducing $N$ primitive steps to
     $N / 5$ idiom steps.
   - **Arch 4 (`Theory.evalProg_sound`):**
     Monolithic full-function computational reflection over typed `BitVec 64`
     machine states discharged by kernel `rfl`.
   - **Arch 5 (`Theory.evalBlock_step`, `Theory.diamond_join_sound`,
     `Theory.call_summary_sound`, `Theory.loop_summary_sound`):**
     Compositional cut-point / block-modular reflection with pre-proved
     diamond-join merging, interprocedural call summaries, and loop summaries.
   - **Arch 6 (`Theory.evalCvProg_sound`):**
     `cv_trans`-style fast `Nat`-encoded kernel domain reflection that
     evaluates instructions using exclusively C++ kernel GMP primitives
     (`Nat.add`, `Nat.sub`, `Nat.land`, `Nat.xor`, `Nat.shiftLeft`,
     `Nat.shiftRight`, `Nat.ble`) before lifting back to `Trusted.Reach` via a
     pre-proved simulation bridge.
-/

namespace Trusted

/-- Register / local variable identifier in the benchmark machine. -/
inductive Reg where
  | r0
  | r1
  | r2
  | r3
  deriving DecidableEq, Repr

/-- Machine state with 64-bit `BitVec 64` local registers and an overflow flag. -/
structure State where
  pc   : Nat
  r0   : BitVec 64
  r1   : BitVec 64
  r2   : BitVec 64
  r3   : BitVec 64
  flag : Bool
  deriving DecidableEq, Repr

/-- Read register `r` from `s`. -/
def State.getReg (s : State) : Reg → BitVec 64
  | .r0 => s.r0
  | .r1 => s.r1
  | .r2 => s.r2
  | .r3 => s.r3

/-- Write `v` to register `r` in `s` and advance `pc` by `1`. -/
def State.setRegNext (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .r0 => { s with pc := s.pc + 1, r0 := v }
  | .r1 => { s with pc := s.pc + 1, r1 := v }
  | .r2 => { s with pc := s.pc + 1, r2 := v }
  | .r3 => { s with pc := s.pc + 1, r3 := v }

/-- Write `v` to register `r` and `fl` to `flag` in `s`, advancing `pc` by `1`. -/
def State.setRegFlagNext (s : State) (r : Reg) (v : BitVec 64) (fl : Bool) : State :=
  match r with
  | .r0 => { s with pc := s.pc + 1, r0 := v, flag := fl }
  | .r1 => { s with pc := s.pc + 1, r1 := v, flag := fl }
  | .r2 => { s with pc := s.pc + 1, r2 := v, flag := fl }
  | .r3 => { s with pc := s.pc + 1, r3 := v, flag := fl }

/-- MIR-like scalar and checked-arithmetic instruction set. -/
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
  deriving DecidableEq, Repr

/-- Single-instruction transition over typed `BitVec 64` registers. -/
def stepInstr (i : Instr) (s : State) : Option State :=
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
    if s.flag then none else some { s with pc := s.pc + 1 }

/-- Small-step outcome of executing one step of a ` List Instr` program. -/
inductive StepOut where
  | step (next : State)
  | ret (val : BitVec 64)
  | trap
  deriving DecidableEq, Repr

/-- Fetch and execute the instruction at `prog[s.pc]?`. -/
def evalStep (prog : List Instr) (s : State) : StepOut :=
  match prog[s.pc]? with
  | some instr =>
    match stepInstr instr s with
    | some s' => .step s'
    | none => .trap
  | none => .ret s.r0

/-- Forward small-step reachability to a normal return value `v`. -/
inductive Reach (prog : List Instr) : State → BitVec 64 → Prop where
  | done (s : State) (v : BitVec 64)
      (hTerm : evalStep prog s = .ret v) :
      Reach prog s v
  | step (s s' : State) (v : BitVec 64)
      (hStep : evalStep prog s = .step s')
      (hRest : Reach prog s' v) :
      Reach prog s v

/-- Prefix execution outcome for Anneal's step-indexed prefix semantics. -/
inductive PrefixOut where
  | running
  | ret (val : BitVec 64)
  | trap
  deriving DecidableEq, Repr

/-- Step-indexed prefix execution relation matching `Trusted.ReachesPrefix`. -/
inductive ReachesPrefix (prog : List Instr) : Nat → State → PrefixOut → Prop where
  | zero (s : State) : ReachesPrefix prog 0 s .running
  | step (n : Nat) (s s' : State) (out : PrefixOut)
      (hStep : evalStep prog s = .step s')
      (hRest : ReachesPrefix prog n s' out) :
      ReachesPrefix prog (n + 1) s out
  | ret (n : Nat) (s : State) (v : BitVec 64)
      (hTerm : evalStep prog s = .ret v) :
      ReachesPrefix prog (n + 1) s (.ret v)
  | trap (n : Nat) (s : State)
      (hTrap : evalStep prog s = .trap) :
      ReachesPrefix prog (n + 1) s .trap

/-- Combined safety and return-value specification matching `Anneal.SafeAndEnsures`. -/
def SafeAndEnsures (P : BitVec 64 → Prop) (out : PrefixOut) : Prop :=
  out ≠ .trap ∧ ∀ v, out = .ret v → P v

/-- Universal prefix safety and postcondition satisfaction from state `s`. -/
def VerifiedFrom (prog : List Instr) (s : State) (v : BitVec 64) : Prop :=
  ∀ n out, ReachesPrefix prog n s out → SafeAndEnsures (fun r => r = v) out

end Trusted

namespace Theory

open Trusted

/-!
## Bridge Between `Reach` and `VerifiedFrom` (`ReachesPrefix`)
-/

/-- Anneal PR `#81` (`MirLemmas.lean`) continuation-style single-step lemma. -/
theorem safeAndEnsures_of_step {prog : List Instr} {s s' : State} {n : Nat}
    {out : PrefixOut} {P : BitVec 64 → Prop}
    (hStep : evalStep prog s = .step s')
    (hReach : ReachesPrefix prog n s out)
    (hNext : ∀ n', ReachesPrefix prog n' s' out → SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases hReach with
  | zero =>
    exact And.intro (by intro h; cases h) (fun _ h => by cases h)
  | step n' _ s₂ _ h1 hr =>
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
theorem safeAndEnsures_of_ret {prog : List Instr} {s : State} {n : Nat}
    {out : PrefixOut} {P : BitVec 64 → Prop} {v : BitVec 64}
    (hTerm : evalStep prog s = .ret v)
    (hReach : ReachesPrefix prog n s out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases hReach with
  | zero =>
    exact And.intro (by intro h; cases h) (fun _ h => by cases h)
  | step _ _ _ _ h1 _ =>
    rw [hTerm] at h1
    cases h1
  | ret _ _ v' h1 =>
    rw [hTerm] at h1
    injection h1 with hv
    subst hv
    refine And.intro (by intro h; cases h) (fun r hr => ?_)
    injection hr with hr'
    subst hr'
    exact hPv
  | trap _ _ h1 =>
    rw [hTerm] at h1
    cases h1

/-- Forward `Reach prog s v` implies universal prefix safety `VerifiedFrom prog s v`. -/
theorem Reach_imp_VerifiedFrom {prog : List Instr} {s : State} {v : BitVec 64}
    (h : Reach prog s v) :
    VerifiedFrom prog s v := by
  induction h with
  | done s v hTerm =>
    intro n out hReach
    exact safeAndEnsures_of_ret hTerm hReach rfl
  | step s s' v hStep _ ih =>
    intro n out hReach
    exact safeAndEnsures_of_step hStep hReach (fun n' hr' => ih n' out hr')

/-!
## Arch 2: Structural Suffix Stepping (`SuffixReach`) and `let`-Shared Rules
-/

/-- Suffix reachability over the remaining instruction list starting at `s.pc`. -/
inductive SuffixReach : List Instr → State → BitVec 64 → Prop where
  | nil (s : State) : SuffixReach [] s s.r0
  | cons (i : Instr) (rest : List Instr) (s s' : State) (v : BitVec 64)
      (hStep : stepInstr i s = some s')
      (hRest : SuffixReach rest s' v) :
      SuffixReach (i :: rest) s v

/-- Strict wrapper around `stepInstr` that unpacks `s : State` via `State.casesOn`
    (`State.rec`) at entry. When `s` is a `let`-bound local `FVar` (`ldecl`),
    `reduce_rec` calls `whnf(s)` first, unfolding `s` to a closed `State.mk`
    constructor (`has_fvar == false`) before register operations are constructed.
    Without this, `s.getReg` projections retain the `FVar` inside `Nat.xor` /
    `Nat.add` arguments, causing both `type_checker::reduce_nat`
    (`type_checker.cpp:703`, `if (has_fvar(e)) return none_expr();`) and
    `Meta.withNatValue` (`WHNF.lean:994`) to abort native GMP reduction! -/
def stepInstrStrict (i : Instr) (s : State) : Option State :=
  State.casesOn s fun pc r0 r1 r2 r3 flag =>
    stepInstr i ⟨pc, r0, r1, r2, r3, flag⟩

theorem stepInstrStrict_eq (i : Instr) (s : State) :
    stepInstrStrict i s = stepInstr i s := by
  cases s
  rfl

/-- Pre-proved per-instruction suffix step rule for Arch 2 (`step_instr`). -/
theorem step_instr (i : Instr) (rest : List Instr) (s s' : State) (v : BitVec 64)
    (hStep : stepInstrStrict i s = some s')
    (hRest : SuffixReach rest s' v) :
    SuffixReach (i :: rest) s v := by
  rw [stepInstrStrict_eq] at hStep
  exact SuffixReach.cons i rest s s' v hStep hRest

theorem stepInstr_pc {i : Instr} {s s' : State}
    (h : stepInstr i s = some s') :
    s'.pc = s.pc + 1 := by
  cases i with
  | add dst s1 s2 =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | sub dst s1 s2 =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | xor dst s1 s2 =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | band dst s1 s2 =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | shl dst src amt =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | shr dst src amt =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | addImm dst src imm =>
    dsimp [stepInstr, State.setRegNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | addCheckedImm dst src imm =>
    dsimp [stepInstr, State.setRegFlagNext] at h
    cases dst <;> injection h with h' <;> subst h' <;> rfl
  | assertNotFlag =>
    dsimp [stepInstr] at h
    cases hFlag : s.flag <;> simp [hFlag] at h
    cases h; rfl

theorem evalStep_append_nil (pre : List Instr) (s : State)
    (hPc : s.pc = pre.length) :
    evalStep pre s = .ret s.r0 := by
  unfold evalStep
  have hNone : pre[s.pc]? = none := by
    rw [hPc]
    exact List.getElem?_eq_none (Nat.le_refl _)
  rw [hNone]

theorem evalStep_append_cons (pre : List Instr) (i : Instr) (rest : List Instr)
    (s s' : State) (hPc : s.pc = pre.length) (hStep : stepInstr i s = some s') :
    evalStep (pre ++ i :: rest) s = .step s' := by
  unfold evalStep
  have hSome : (pre ++ i :: rest)[s.pc]? = some i := by
    rw [hPc]
    rw [List.getElem?_append_right (Nat.le_refl _)]
    rw [Nat.sub_self]
    rfl
  rw [hSome]
  dsimp only
  rw [hStep]

theorem SuffixReach_imp_Reach_append (pre suf : List Instr) (s : State) (v : BitVec 64)
    (hPc : s.pc = pre.length)
    (hSuf : SuffixReach suf s v) :
    Reach (pre ++ suf) s v := by
  induction hSuf generalizing pre with
  | nil s =>
    rw [List.append_nil]
    exact Reach.done s s.r0 (evalStep_append_nil pre s hPc)
  | cons i rest s s' v hStep hRest ih =>
    have hEval : evalStep (pre ++ i :: rest) s = .step s' :=
      evalStep_append_cons pre i rest s s' hPc hStep
    have hAssoc : pre ++ i :: rest = (pre ++ [i]) ++ rest := by
      simp
    have hPc' : s'.pc = (pre ++ [i]).length := by
      rw [stepInstr_pc hStep, hPc, List.length_append, List.length_singleton]
    have hReach' : Reach ((pre ++ [i]) ++ rest) s' v :=
      ih (pre ++ [i]) hPc'
    rw [← hAssoc] at hReach'
    exact Reach.step s s' v hEval hReach'

/-- Bridge theorem lifting `SuffixReach prog s v` at `s.pc = 0` to `Trusted.Reach prog s v`. -/
theorem SuffixReach_imp_Reach (prog : List Instr) (s : State) (v : BitVec 64)
    (hPc : s.pc = 0)
    (hSuf : SuffixReach prog s v) :
    Reach prog s v :=
  SuffixReach_imp_Reach_append [] prog s v hPc hSuf

/-!
## Arch 3: Pre-Proved Fused 5-Instruction Idiom Schema (`step_idiom5`)
-/

/-- Fused big-step transition for the 5-instruction checked-add + bitwise-mix idiom:
    1. `addCheckedImm .r0 .r0 imm`
    2. `assertNotFlag`
    3. `xor .r1 .r0 .r2`
    4. `shl .r2 .r1 3`
    5. `add .r0 .r0 .r2` -/
def evalIdiom5 (imm : BitVec 64) (s : State) : Option State :=
  State.casesOn s fun pc r0 _r1 r2 r3 _flag =>
    if BitVec.uaddOverflow r0 imm then
      none
    else
      let r0_1 := r0 + imm
      let r1_2 := r0_1 ^^^ r2
      let r2_3 := r1_2 <<< 3
      let r0_4 := r0_1 + r2_3
      some ⟨pc + 5, r0_4, r1_2, r2_3, r3, false⟩

/-- Pre-proved big-step soundness rule for the 5-instruction idiom. -/
theorem step_idiom5 (imm : BitVec 64) (rest : List Instr)
    (s s' : State) (v : BitVec 64)
    (hIdiom : evalIdiom5 imm s = some s')
    (hRest : SuffixReach rest s' v) :
    SuffixReach
      (.addCheckedImm .r0 .r0 imm ::
       .assertNotFlag ::
       .xor .r1 .r0 .r2 ::
       .shl .r2 .r1 3 ::
       .add .r0 .r0 .r2 :: rest) s v := by
  cases s with
  | mk pc r0 r1 r2 r3 flag =>
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
      let s1 : State := ⟨pc + 1, r0 + imm, r1, r2, r3, false⟩
      let s2 : State := ⟨pc + 1 + 1, r0 + imm, r1, r2, r3, false⟩
      let s3 : State := ⟨pc + 1 + 1 + 1, r0 + imm, (r0 + imm) ^^^ r2, r2, r3, false⟩
      let s4 : State := ⟨pc + 1 + 1 + 1 + 1, r0 + imm, (r0 + imm) ^^^ r2,
        ((r0 + imm) ^^^ r2) <<< 3, r3, false⟩
      have h1 : stepInstr (.addCheckedImm .r0 .r0 imm) ⟨pc, r0, r1, r2, r3, flag⟩ = some s1 := by
        dsimp [stepInstr, State.getReg, State.setRegFlagNext, s1]
        rw [hOv]
      have h2 : stepInstr .assertNotFlag s1 = some s2 := rfl
      have h3 : stepInstr (.xor .r1 .r0 .r2) s2 = some s3 := rfl
      have h4 : stepInstr (.shl .r2 .r1 3) s3 = some s4 := rfl
      have h5 : stepInstr (.add .r0 .r0 .r2) s4 =
          some ⟨pc + 5, (r0 + imm) + (((r0 + imm) ^^^ r2) <<< 3),
            (r0 + imm) ^^^ r2, ((r0 + imm) ^^^ r2) <<< 3, r3, false⟩ := rfl
      exact SuffixReach.cons _ _ _ _ _ h1
        (SuffixReach.cons _ _ _ _ _ h2
          (SuffixReach.cons _ _ _ _ _ h3
            (SuffixReach.cons _ _ _ _ _ h4
              (SuffixReach.cons _ _ _ _ _ h5 hRest))))

/-!
## Arch 4: Monolithic Full-Function Computational Reflection (`evalProg_sound`)
-/

/-- Total structural evaluator over `code : List Instr` on typed `State`. -/
def evalSuffix (code : List Instr) (s : State) : Option (BitVec 64) :=
  match code with
  | [] => some s.r0
  | i :: rest =>
    match stepInstr i s with
    | some s' => evalSuffix rest s'
    | none => none

theorem evalSuffix_sound (code : List Instr) (s : State) (v : BitVec 64)
    (h : evalSuffix code s = some v) :
    SuffixReach code s v := by
  induction code generalizing s with
  | nil =>
    injection h with hv
    subst hv
    exact SuffixReach.nil s
  | cons i rest ih =>
    dsimp [evalSuffix] at h
    cases hStep : stepInstr i s with
    | none =>
      rw [hStep] at h
      cases h
    | some s' =>
      rw [hStep] at h
      exact SuffixReach.cons i rest s s' v hStep (ih s' h)

/-- Arch 4 reflection theorem: a single `rfl` proof of `evalSuffix prog s = some v`
    yields `Trusted.Reach prog s v`. -/
theorem evalProg_sound (prog : List Instr) (s : State) (v : BitVec 64)
    (hPc : s.pc = 0)
    (hEval : evalSuffix prog s = some v) :
    Reach prog s v :=
  SuffixReach_imp_Reach prog s v hPc (evalSuffix_sound prog s v hEval)

/-!
## Arch 5: Compositional Cut-Point / Block-Modular Reflection & Summaries
-/

/-- Evaluate a basic block `blk : List Instr` from state `s` to its post-block cut-point state. -/
def evalBlock (blk : List Instr) (s : State) : Option State :=
  match blk with
  | [] => some s
  | i :: rest =>
    match stepInstrStrict i s with
    | some s' => evalBlock rest s'
    | none => none

/-- Pre-proved cut-point composition lemma (`evalBlock_step`): verifies a block
    `blk` by `rfl` to reach cut-point state `s'`, then continues with `rest`. -/
theorem evalBlock_step (blk rest : List Instr) (s s' : State) (v : BitVec 64)
    (hBlk : evalBlock blk s = some s')
    (hRest : SuffixReach rest s' v) :
    SuffixReach (blk ++ rest) s v := by
  induction blk generalizing s with
  | nil =>
    injection hBlk with hs
    subst hs
    exact hRest
  | cons i blkTail ih =>
    dsimp [evalBlock] at hBlk
    cases hStep : stepInstrStrict i s with
    | none =>
      rw [hStep] at hBlk
      cases hBlk
    | some s1 =>
      rw [hStep] at hBlk
      exact step_instr i (blkTail ++ rest) s s1 v hStep (ih s1 hBlk)

/-- Spine-preserving conditional state merge at a CFG diamond join point:
    pushes `if cond then ... else ...` inside register fields so the outer
    `State.mk` constructor and `pc` remain exposed for subsequent `rfl` block
    evaluation on symbolic inputs! -/
def mergeState (cond : Bool) (sT sF : State) : State where
  pc   := if cond then sT.pc else sF.pc
  r0   := if cond then sT.r0 else sF.r0
  r1   := if cond then sT.r1 else sF.r1
  r2   := if cond then sT.r2 else sF.r2
  r3   := if cond then sT.r3 else sF.r3
  flag := if cond then sT.flag else sF.flag

theorem mergeState_eq_ite (cond : Bool) (sT sF : State) :
    mergeState cond sT sF = (if cond then sT else sF) := by
  cases cond <;> cases sT <;> cases sF <;> rfl

/-- Pre-proved diamond join theorem (`diamond_join_sound`): evaluates `blkT`
    and `blkF` independently from `s`, merges the resulting states into a
    single spine-preserving `sJoin` state when their `pc`s agree, and continues
    verification of `rest` once from `sJoin`. -/
theorem diamond_join_sound (cond : Bool) (blkT blkF rest : List Instr)
    (s sT sF sJoin : State) (v : BitVec 64)
    (hT : evalBlock blkT s = some sT)
    (hF : evalBlock blkF s = some sF)
    (hJoin : mergeState cond sT sF = sJoin)
    (hRest : SuffixReach rest sJoin v) :
    SuffixReach ((if cond then blkT else blkF) ++ rest) s v := by
  subst hJoin
  rw [mergeState_eq_ite] at hRest
  cases cond with
  | true => exact evalBlock_step blkT rest s sT v hT hRest
  | false => exact evalBlock_step blkF rest s sF v hF hRest

/-- Pre-proved cut-point diamond convergence rule (`diamond_converge_step`):
    evaluates both arms `blkT` and `blkF` independently at diamond $k$ (`2`
    arm evaluations of length $B$) and continues verification of `rest` once
    from the shared cut-point state `sJoin`, avoiding the $2^D$ path explosion
    of monolithic full-function reflection. -/
theorem diamond_converge_step (cond : Bool) (blkT blkF rest : List Instr)
    (s sJoin : State) (v : BitVec 64)
    (hT : evalBlock blkT s = some sJoin)
    (hF : evalBlock blkF s = some sJoin)
    (hRest : SuffixReach rest sJoin v) :
    SuffixReach ((if cond then blkT else blkF) ++ rest) s v := by
  cases cond with
  | true => exact evalBlock_step blkT rest s sJoin v hT hRest
  | false => exact evalBlock_step blkF rest s sJoin v hF hRest

/-- Pre-proved polymorphic call summary rule (`call_summary_sound`):
    Given a pre-proved algebraic specification ` ∀ s, evalBlock callee s = some (specFn s)`
    for a helper block `callee`, any call site in a caller transitions directly
    from `s` to `specFn s` in $O(1)$ without re-evaluating `callee`! -/
theorem call_summary_sound {callee : List Instr} {specFn : State → State}
    (hSummary : ∀ s, evalBlock callee s = some (specFn s))
    (rest : List Instr) (s : State) (v : BitVec 64)
    (hRest : SuffixReach rest (specFn s) v) :
    SuffixReach (callee ++ rest) s v :=
  evalBlock_step callee rest s (specFn s) v (hSummary s) hRest

/-- Bounded loop iteration of `body` `k` times (`List.replicate k body |>.flatten`). -/
def loopCode (k : Nat) (body : List Instr) : List Instr :=
  match k with
  | 0 => []
  | n + 1 => body ++ loopCode n body

/-- Pre-proved loop summary rule (`loop_summary_sound`):
    If one iteration of `body` transforms state `inv i` into `inv (i + 1)`, then
    `loopCode k body` transforms `inv 0` into `inv k` in $O(1)$ proof size for
    arbitrary symbolic trip count `k : Nat`! -/
theorem loop_summary_sound {body : List Instr} (inv : Nat → State)
    (hStepInv : ∀ i, evalBlock body (inv i) = some (inv (i + 1)))
    (k : Nat) (rest : List Instr) (v : BitVec 64)
    (hRest : SuffixReach rest (inv k) v) :
    SuffixReach (loopCode k body ++ rest) (inv 0) v := by
  have hGen : ∀ idx k,
      SuffixReach rest (inv (idx + k)) v →
      SuffixReach (loopCode k body ++ rest) (inv idx) v := by
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
      apply evalBlock_step body (loopCode n body ++ rest) (inv idx) (inv (idx + 1)) v (hStepInv idx)
      have hEq : idx + 1 + n = idx + (n + 1) := by omega
      rw [← hEq] at hR
      exact ih (idx + 1) hR
  have h0 : 0 + k = k := Nat.zero_add k
  rw [← h0] at hRest
  exact hGen 0 k hRest

/-!
## Arch 6: `cv_trans`-Style Fast `Nat`-Encoded Kernel Domain Reflection (`evalCvProg_sound`)
-/

/-- 64-bit modulus `2^64`. -/
def MOD64 : Nat := 18446744073709551616

/-- 64-bit bitmask `2^64 - 1 = 0xFFFFFFFFFFFFFFFF`. -/
def MASK64 : Nat := 18446744073709551615

/-- Flat `Nat`-only state for C++ kernel GMP evaluation (`reduce_nat`). -/
structure CvState where
  pc   : Nat
  r0   : Nat
  r1   : Nat
  r2   : Nat
  r3   : Nat
  flag : Bool
  deriving DecidableEq, Repr

/-- Project a typed `State` (`BitVec 64` registers) to a flat `CvState` (`Nat` registers). -/
def toCvState (s : State) : CvState where
  pc   := s.pc
  r0   := s.r0.toNat
  r1   := s.r1.toNat
  r2   := s.r2.toNat
  r3   := s.r3.toNat
  flag := s.flag

/-- Read register `r` from `CvState`. -/
def CvState.getReg (cs : CvState) : Reg → Nat
  | .r0 => cs.r0
  | .r1 => cs.r1
  | .r2 => cs.r2
  | .r3 => cs.r3

/-- Write `v` to register `r` in `CvState` and increment `pc`. -/
def CvState.setRegNext (cs : CvState) (r : Reg) (v : Nat) : CvState :=
  match r with
  | .r0 => { cs with pc := Nat.add cs.pc 1, r0 := v }
  | .r1 => { cs with pc := Nat.add cs.pc 1, r1 := v }
  | .r2 => { cs with pc := Nat.add cs.pc 1, r2 := v }
  | .r3 => { cs with pc := Nat.add cs.pc 1, r3 := v }

/-- Write `v` to register `r` and `fl` to `flag` in `CvState`, incrementing `pc`. -/
def CvState.setRegFlagNext (cs : CvState) (r : Reg) (v : Nat) (fl : Bool) : CvState :=
  match r with
  | .r0 => { cs with pc := Nat.add cs.pc 1, r0 := v, flag := fl }
  | .r1 => { cs with pc := Nat.add cs.pc 1, r1 := v, flag := fl }
  | .r2 => { cs with pc := Nat.add cs.pc 1, r2 := v, flag := fl }
  | .r3 => { cs with pc := Nat.add cs.pc 1, r3 := v, flag := fl }

/-- Evaluate one instruction in the `cv_trans` domain using exclusively C++
    kernel GMP primitives (`Nat.add`, `Nat.sub`, `Nat.land`, `Nat.xor`,
    `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.ble`), replacing modular division
    `% 2^64` with `Nat.land _ MASK64` and avoiding all `BitVec` / `Fin` /
    `isLt` proof terms. -/
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
    if cs.flag then none else some { cs with pc := Nat.add cs.pc 1 }

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

/-- Exact step simulation between `stepCvInstr` (flat GMP `Nat`) and `stepInstr` (`BitVec 64`). -/
theorem stepCvInstr_sim (i : Instr) (s : State) :
    stepCvInstr i (toCvState s) = (stepInstr i s).map toCvState := by
  cases i with
  | add dst src1 src2 =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState, getReg_toCvState]
    have hVal : ((s.getReg src1).toNat + (s.getReg src2).toNat) &&& MASK64 =
        (s.getReg src1 + s.getReg src2).toNat := by
      change Nat.land (Nat.add (s.getReg src1).toNat (s.getReg src2).toNat) MASK64 = _
      rw [land_mask64_eq_mod]
      rfl
    rw [hVal, setRegNext_toCvState]
  | sub dst src1 src2 =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState, getReg_toCvState]
    have hVal : (MOD64 - (s.getReg src2).toNat + (s.getReg src1).toNat) &&& MASK64 =
        (s.getReg src1 - s.getReg src2).toNat := by
      change Nat.land (Nat.add (Nat.sub MOD64 (s.getReg src2).toNat) (s.getReg src1).toNat) MASK64 = _
      rw [land_mask64_eq_mod]
      rfl
    rw [hVal, setRegNext_toCvState]
  | xor dst src1 src2 =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState, getReg_toCvState]
    have hVal : (s.getReg src1).toNat ^^^ (s.getReg src2).toNat =
        (s.getReg src1 ^^^ s.getReg src2).toNat := rfl
    rw [hVal, setRegNext_toCvState]
  | band dst src1 src2 =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState, getReg_toCvState]
    have hVal : (s.getReg src1).toNat &&& (s.getReg src2).toNat =
        (s.getReg src1 &&& s.getReg src2).toNat := rfl
    rw [hVal, setRegNext_toCvState]
  | shl dst src amt =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState]
    have hVal : ((s.getReg src).toNat <<< amt) &&& MASK64 =
        (s.getReg src <<< amt).toNat := by
      change Nat.land (Nat.shiftLeft (s.getReg src).toNat amt) MASK64 = _
      rw [land_mask64_eq_mod]
      rfl
    rw [hVal, setRegNext_toCvState]
  | shr dst src amt =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState]
    have hVal : (s.getReg src).toNat >>> amt =
        (s.getReg src >>> amt).toNat := rfl
    rw [hVal, setRegNext_toCvState]
  | addImm dst src imm =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState]
    have hVal : ((s.getReg src).toNat + imm.toNat) &&& MASK64 =
        (s.getReg src + imm).toNat := by
      change Nat.land (Nat.add (s.getReg src).toNat imm.toNat) MASK64 = _
      rw [land_mask64_eq_mod]
      rfl
    rw [hVal, setRegNext_toCvState]
  | addCheckedImm dst src imm =>
    dsimp [stepCvInstr, stepInstr]
    rw [getReg_toCvState]
    have hVal : ((s.getReg src).toNat + imm.toNat) &&& MASK64 =
        (s.getReg src + imm).toNat := by
      change Nat.land (Nat.add (s.getReg src).toNat imm.toNat) MASK64 = _
      rw [land_mask64_eq_mod]
      rfl
    have hOv : MOD64.ble ((s.getReg src).toNat + imm.toNat) =
        BitVec.uaddOverflow (s.getReg src) imm :=
      ble_mod64_eq_uaddOverflow (s.getReg src) imm
    rw [hVal, hOv, setRegFlagNext_toCvState]
  | assertNotFlag =>
    dsimp [stepCvInstr, stepInstr, toCvState]
    cases s.flag <;> rfl

/-- Multi-step simulation between `evalCvSuffix` and `evalSuffix`. -/
theorem evalCvSuffix_sim (code : List Instr) (s : State) :
    evalCvSuffix code (toCvState s) = (evalSuffix code s).map BitVec.toNat := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    dsimp [evalCvSuffix, evalSuffix]
    rw [stepCvInstr_sim]
    cases stepInstr i s with
    | none => rfl
    | some s' => exact ih s'

/-- Arch 6 (`cv_trans`) bridge theorem: a single `rfl` reduction of
    `evalCvSuffix prog (toCvState s) = some v.toNat` in the C++ kernel's native
    GMP arithmetic engine proves `Trusted.Reach prog s v`! -/
theorem evalCvProg_sound (prog : List Instr) (s : State) (v : BitVec 64)
    (hPc : s.pc = 0)
    (hCv : evalCvSuffix prog (toCvState s) = some v.toNat) :
    Reach prog s v := by
  rw [evalCvSuffix_sim] at hCv
  cases hEval : evalSuffix prog s with
  | none =>
    rw [hEval] at hCv
    cases hCv
  | some v' =>
    rw [hEval] at hCv
    dsimp at hCv
    injection hCv with hNat
    have hEq : v' = v := BitVec.eq_of_toNat_eq hNat
    subst hEq
    exact evalProg_sound prog s v' hPc hEval

end Theory
