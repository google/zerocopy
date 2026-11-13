-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Safe-Rust UB-Freedom Fundamental Theorem and Unsafe Standard-Library Boundary

Standalone Lean 4 (`v4.34.1`) mechanization covering:
1. **Operational Semantics with Undefined Behavior (`StepResult`)**:
   Models a MIR-level memory state (`MemState`) with capability-tagged slots
   (`Permission.unique`, `Permission.shared`, `Permission.disabled`), where
   dereferencing an unallocated or disabled capability triggers explicit
   Undefined Behavior (`StepResult.ub`).
2. **Syntactic Safe-Rust Well-Formedness (`SynSafeStmt`, `SynSafeBody`)**:
   Models `rustc_mir_build::check_unsafety::UnsafetyVisitor`: safe statements
   never perform unchecked raw-pointer dereferences and only invoke external
   (`unsafe`) standard-library primitives through their typed semantic interface.
3. **Semantic Type Interpretation & Fundamental Theorem of Logical Relations (FTLR)**:
   Defines the semantic type invariant `SemValidState` and the semantic library
   contract `SemLibContract`. Proves the **Fundamental Theorem of Logical
   Relations (`ftlr_safe_stmt`, `ftlr_safe_body_ub_free`)**: *every* syntactically
   well-typed safe MIR body is automatically free of UB (`≠ .ub`) whenever all
   invoked standard-library `unsafe` primitives satisfy `SemLibContract`.
4. **Refutation Canary (`canary_buggy_unsafe_lib_breaks_safe_caller`)**:
   Demonstrates that if an `unsafe` standard-library primitive (such as a buggy
   `Slice::get_unchecked` or `Vec::set_len` wrapper) violates `SemLibContract`
   by returning a dangling/disabled capability, a 100% syntactically safe caller
   triggers `StepResult.ub`.
-/

namespace SafeRustUbFreedomProbe

/-- Capability permission on a memory slot (analogous to Stacked/Tree Borrows
    and RustBelt `ty_own` / `ty_shr`). -/
inductive Permission where
  | unique
  | shared
  | disabled
  deriving DecidableEq, Repr

/-- A memory slot holds a value and an active capability permission. -/
structure Slot where
  val  : Nat
  perm : Permission
  deriving DecidableEq, Repr

abbrev Reg := Nat
abbrev Loc := Nat

/-- Abstract machine state mapping registers to locations and locations to slots. -/
structure MachineState where
  regLoc : Reg -> Loc
  heap   : Loc -> Slot

/-- Result of executing a statement or body: either a valid next state or UB. -/
inductive StepResult where
  | ok (st : MachineState)
  | ub

/-- A primitive statement in `Runtime(PostCleanup)` MIR. -/
inductive MirStmt where
  | readRef (dstValLoc : Loc) (srcRef : Reg)
  | writeUniqueRef (dstRef : Reg) (newVal : Nat)
  | reborrowShared (dstRef : Reg) (srcRef : Reg)
  | callStdPrimitive (primId : Nat) (argRef : Reg) (retRef : Reg)
  | rawPtrDerefWrite (rawLoc : Loc) (newVal : Nat)
  deriving DecidableEq, Repr

/-- Operational semantics of a single MIR statement. -/
def execStmt (stdEnv : Nat -> MachineState -> Reg -> Reg -> StepResult)
    (st : MachineState) : MirStmt -> StepResult
  | .readRef dstValLoc srcRef =>
    let l := st.regLoc srcRef
    match (st.heap l).perm with
    | .unique | .shared =>
      let v := (st.heap l).val
      .ok { st with heap := fun loc =>
        if loc = dstValLoc then { val := v, perm := (st.heap dstValLoc).perm }
        else st.heap loc }
    | .disabled => .ub
  | .writeUniqueRef dstRef newVal =>
    let l := st.regLoc dstRef
    match (st.heap l).perm with
    | .unique =>
      .ok { st with heap := fun loc =>
        if loc = l then { val := newVal, perm := .unique }
        else st.heap loc }
    | _ => .ub
  | .reborrowShared dstRef srcRef =>
    let l := st.regLoc srcRef
    match (st.heap l).perm with
    | .unique | .shared =>
      .ok { regLoc := fun r => if r = dstRef then l else st.regLoc r,
            heap := fun loc =>
              if loc = l then { val := (st.heap l).val, perm := .shared }
              else st.heap loc }
    | .disabled => .ub
  | .callStdPrimitive primId argRef retRef =>
    stdEnv primId st argRef retRef
  | .rawPtrDerefWrite rawLoc newVal =>
    match (st.heap rawLoc).perm with
    | .unique =>
      .ok { st with heap := fun loc =>
        if loc = rawLoc then { val := newVal, perm := .unique }
        else st.heap loc }
    | _ => .ub

/-- Multi-statement body execution. -/
def execBody (stdEnv : Nat -> MachineState -> Reg -> Reg -> StepResult)
    (st : MachineState) : List MirStmt -> StepResult
  | [] => .ok st
  | s :: rest =>
    match execStmt stdEnv st s with
    | .ub => .ub
    | .ok st' => execBody stdEnv st' rest

/-- Borrow-checker capability assignment at a program point: maps each register
    to the minimum required permission (`some .unique` or `some .shared`). -/
abbrev BorrowTyping := Reg -> Option Permission

/-- Semantic validity of `MachineState` under `BorrowTyping`:
    - If `Γ r = some .unique`, the target heap slot has `.unique` permission.
    - If `Γ r = some .shared`, the target heap slot has `.unique` or `.shared`
      permission (never `.disabled`). -/
def SemValidState (Γ : BorrowTyping) (st : MachineState) : Prop :=
  ∀ r,
    (Γ r = some .unique -> (st.heap (st.regLoc r)).perm = .unique) ∧
    (Γ r = some .shared ->
      (st.heap (st.regLoc r)).perm = .unique ∨ (st.heap (st.regLoc r)).perm = .shared)

/-- Semantic contract for an `unsafe` standard-library primitive `primId`:
    whenever `argRef` has at least `.shared` permission in a semantically valid
    state `st`, calling `primId` does not trigger UB and establishes `.shared`
    permission on `retRef` while preserving existing capabilities. -/
def SemLibContract (stdEnv : Nat -> MachineState -> Reg -> Reg -> StepResult) : Prop :=
  ∀ primId Γ st argRef retRef,
    SemValidState Γ st ->
    (Γ argRef = some .unique ∨ Γ argRef = some .shared) ->
    ∃ st',
      stdEnv primId st argRef retRef = .ok st' ∧
      SemValidState (fun r => if r = retRef then some .shared else Γ r) st'

/-- Syntactic typing and borrow-checking judgment (`SynSafeStmt Γ s Γ'`) for
    safe MIR statements (notice `.rawPtrDerefWrite` is rejected by
    `check_unsafety` in safe code!). -/
inductive SynSafeStmt : BorrowTyping -> MirStmt -> BorrowTyping -> Prop where
  | safeRead (Γ : BorrowTyping) (dstValLoc : Loc) (srcRef : Reg)
      (h_src : Γ srcRef = some .unique ∨ Γ srcRef = some .shared) :
      SynSafeStmt Γ (.readRef dstValLoc srcRef) Γ
  | safeWriteUnique (Γ : BorrowTyping) (dstRef : Reg) (newVal : Nat)
      (h_dst : Γ dstRef = some .unique) :
      SynSafeStmt Γ (.writeUniqueRef dstRef newVal) Γ
  | safeReborrowShared (Γ : BorrowTyping) (dstRef srcRef : Reg)
      (h_src : Γ srcRef = some .unique ∨ Γ srcRef = some .shared) :
      SynSafeStmt Γ (.reborrowShared dstRef srcRef)
        (fun r => if r = dstRef ∨ r = srcRef then some .shared else
          if Γ r = some .unique then none else Γ r)
  | safeCallStd (Γ : BorrowTyping) (primId : Nat) (argRef retRef : Reg)
      (h_arg : Γ argRef = some .unique ∨ Γ argRef = some .shared) :
      SynSafeStmt Γ (.callStdPrimitive primId argRef retRef)
        (fun r => if r = retRef then some .shared else Γ r)

/-- Sequence of syntactically safe statements. -/
inductive SynSafeBody : BorrowTyping -> List MirStmt -> BorrowTyping -> Prop where
  | nil (Γ : BorrowTyping) : SynSafeBody Γ [] Γ
  | cons {Γ₁ Γ₂ Γ₃ : BorrowTyping} {s : MirStmt} {rest : List MirStmt}
      (h_stmt : SynSafeStmt Γ₁ s Γ₂)
      (h_rest : SynSafeBody Γ₂ rest Γ₃) :
      SynSafeBody Γ₁ (s :: rest) Γ₃

/-- Fundamental Theorem of Logical Relations (FTLR) for a single safe MIR statement. -/
theorem ftlr_safe_stmt
    (stdEnv : Nat -> MachineState -> Reg -> Reg -> StepResult)
    (h_lib : SemLibContract stdEnv)
    {Γ Γ' : BorrowTyping} {s : MirStmt} {st : MachineState}
    (h_syn : SynSafeStmt Γ s Γ')
    (h_sem : SemValidState Γ st) :
    ∃ st', execStmt stdEnv st s = .ok st' ∧ SemValidState Γ' st' := by
  cases h_syn with
  | safeRead dstValLoc srcRef h_src =>
    have h_r := h_sem srcRef
    have h_perm : (st.heap (st.regLoc srcRef)).perm = .unique ∨
                  (st.heap (st.regLoc srcRef)).perm = .shared := by
      cases h_src with
      | inl hu => exact Or.inl (h_r.1 hu)
      | inr hs => exact h_r.2 hs
    cases h_p : (st.heap (st.regLoc srcRef)).perm with
    | disabled =>
      cases h_perm with
      | inl h1 => rw [h_p] at h1; cases h1
      | inr h2 => rw [h_p] at h2; cases h2
    | unique =>
      unfold execStmt
      dsimp only
      rw [h_p]
      refine ⟨_, rfl, ?_⟩
      intro r
      have hr := h_sem r
      have h_perm_eq :
        ((if st.regLoc r = dstValLoc then
            { val := (st.heap (st.regLoc srcRef)).val, perm := (st.heap dstValLoc).perm }
          else st.heap (st.regLoc r)) : Slot).perm = (st.heap (st.regLoc r)).perm := by
        by_cases h_eq : st.regLoc r = dstValLoc
        · simp [h_eq]
        · simp [h_eq]
      exact ⟨fun hu => h_perm_eq.trans (hr.1 hu), fun hs => h_perm_eq ▸ hr.2 hs⟩
    | shared =>
      unfold execStmt
      dsimp only
      rw [h_p]
      refine ⟨_, rfl, ?_⟩
      intro r
      have hr := h_sem r
      have h_perm_eq :
        ((if st.regLoc r = dstValLoc then
            { val := (st.heap (st.regLoc srcRef)).val, perm := (st.heap dstValLoc).perm }
          else st.heap (st.regLoc r)) : Slot).perm = (st.heap (st.regLoc r)).perm := by
        by_cases h_eq : st.regLoc r = dstValLoc
        · simp [h_eq]
        · simp [h_eq]
      exact ⟨fun hu => h_perm_eq.trans (hr.1 hu), fun hs => h_perm_eq ▸ hr.2 hs⟩
  | safeWriteUnique dstRef newVal h_dst =>
    have h_p := (h_sem dstRef).1 h_dst
    unfold execStmt
    dsimp only
    rw [h_p]
    refine ⟨_, rfl, ?_⟩
    intro r
    have hr := h_sem r
    constructor
    · intro hu
      by_cases h_eq : st.regLoc r = st.regLoc dstRef <;> simp [h_eq, hr.1 hu]
    · intro hs
      by_cases h_eq : st.regLoc r = st.regLoc dstRef <;> simp [h_eq, hr.2 hs]
  | safeReborrowShared dstRef srcRef h_src =>
    have h_r := h_sem srcRef
    have h_perm : (st.heap (st.regLoc srcRef)).perm = .unique ∨
                  (st.heap (st.regLoc srcRef)).perm = .shared := by
      cases h_src with
      | inl hu => exact Or.inl (h_r.1 hu)
      | inr hs => exact h_r.2 hs
    cases h_p : (st.heap (st.regLoc srcRef)).perm with
    | disabled =>
      cases h_perm with
      | inl h1 => rw [h_p] at h1; cases h1
      | inr h2 => rw [h_p] at h2; cases h2
    | unique =>
      unfold execStmt
      dsimp only
      rw [h_p]
      refine ⟨_, rfl, ?_⟩
      intro r
      constructor
      · intro hu
        by_cases h1 : r = dstRef ∨ r = srcRef
        · simp [h1] at hu
        · simp [h1] at hu
      · intro hs
        by_cases h_rd : r = dstRef
        · simp [h_rd]
        · by_cases h_rs : r = srcRef
          · simp [h_rs]
          · have h_not_or : ¬ (r = dstRef ∨ r = srcRef) := by
              intro h_or
              cases h_or with
              | inl h => exact h_rd h
              | inr h => exact h_rs h
            simp [h_not_or] at hs
            by_cases h_u : Γ r = some .unique
            · simp [h_u] at hs
            · simp [h_u] at hs
              have hr_shr := (h_sem r).2 hs
              by_cases h_loc : st.regLoc r = st.regLoc srcRef
              · simp [h_rd, h_loc]
              · simp [h_rd, h_loc, hr_shr]
    | shared =>
      unfold execStmt
      dsimp only
      rw [h_p]
      refine ⟨_, rfl, ?_⟩
      intro r
      constructor
      · intro hu
        by_cases h1 : r = dstRef ∨ r = srcRef
        · simp [h1] at hu
        · simp [h1] at hu
      · intro hs
        by_cases h_rd : r = dstRef
        · simp [h_rd]
        · by_cases h_rs : r = srcRef
          · simp [h_rs]
          · have h_not_or : ¬ (r = dstRef ∨ r = srcRef) := by
              intro h_or
              cases h_or with
              | inl h => exact h_rd h
              | inr h => exact h_rs h
            simp [h_not_or] at hs
            by_cases h_u : Γ r = some .unique
            · simp [h_u] at hs
            · simp [h_u] at hs
              have hr_shr := (h_sem r).2 hs
              by_cases h_loc : st.regLoc r = st.regLoc srcRef
              · simp [h_rd, h_loc]
              · simp [h_rd, h_loc, hr_shr]
  | safeCallStd primId argRef retRef h_arg =>
    exact h_lib primId Γ st argRef retRef h_sem h_arg

/-- Fundamental Theorem of Logical Relations (FTLR) for an arbitrary syntactically
    safe MIR body: safe code cannot cause Undefined Behavior if all called
    standard-library `unsafe` primitives uphold `SemLibContract`. -/
theorem ftlr_safe_body_ub_free
    (stdEnv : Nat -> MachineState -> Reg -> Reg -> StepResult)
    (h_lib : SemLibContract stdEnv)
    {Γ Γ' : BorrowTyping} {body : List MirStmt} {st : MachineState}
    (h_syn : SynSafeBody Γ body Γ')
    (h_sem : SemValidState Γ st) :
    ∃ st', execBody stdEnv st body = .ok st' ∧ SemValidState Γ' st' := by
  induction h_syn generalizing st with
  | nil Γ =>
    exact ⟨st, rfl, h_sem⟩
  | cons h_stmt h_rest ih =>
    rcases ftlr_safe_stmt stdEnv h_lib h_stmt h_sem with ⟨st_mid, h_exec_s, h_sem_mid⟩
    rcases ih h_sem_mid with ⟨st_fin, h_exec_rest, h_sem_fin⟩
    refine ⟨st_fin, ?_, h_sem_fin⟩
    simp [execBody, h_exec_s, h_exec_rest]

/-- Canary: If an `unsafe` standard-library primitive violates `SemLibContract`
    (for instance, returning a pointer to an out-of-bounds / `.disabled` slot `loc = 99`),
    then a 100% syntactically well-typed safe caller (`callStdPrimitive` followed by
    `readRef`) triggers `StepResult.ub`. -/
def buggyStdEnv : Nat -> MachineState -> Reg -> Reg -> StepResult :=
  fun _ st _ retRef =>
    .ok { st with regLoc := fun r => if r = retRef then 99 else st.regLoc r }

def canaryGamma0 : BorrowTyping := fun r => if r = 0 then some .unique else none
def canaryGamma1 : BorrowTyping := fun r => if r = 1 then some .shared else canaryGamma0 r

theorem canary_buggy_unsafe_lib_breaks_safe_caller :
    let st₀ : MachineState := {
      regLoc := fun _ => 0
      heap   := fun l => if l = 0 then { val := 42, perm := .unique }
                         else { val := 0, perm := .disabled }
    }
    let body : List MirStmt := [
      .callStdPrimitive 0 0 1,
      .readRef 0 1
    ]
    SemValidState canaryGamma0 st₀ ∧
    SynSafeBody canaryGamma0 body canaryGamma1 ∧
    execBody buggyStdEnv st₀ body = .ub := by
  refine ⟨?_, ?_, rfl⟩
  · intro r
    by_cases hr : r = 0 <;> simp [canaryGamma0, hr]
  · refine SynSafeBody.cons
      (SynSafeStmt.safeCallStd canaryGamma0 0 0 1 (Or.inl rfl))
      (SynSafeBody.cons
        (SynSafeStmt.safeRead canaryGamma1 0 1 (Or.inr rfl))
        (SynSafeBody.nil canaryGamma1))

#print axioms ftlr_safe_stmt
#print axioms ftlr_safe_body_ub_free
#print axioms canary_buggy_unsafe_lib_breaks_safe_caller

end SafeRustUbFreedomProbe
