-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Empirical Probe: Generic `SpecOn` Lifting and Lithium/Aeneas-Style Span-Indexed VC Generation

This standalone Lean 4 (`v4.34.1`) module validates two architectural claims for
Anneal:

1. **Eliminating Bespoke `Ensures*` Predicates and Manual Unpacking Proofs:**
   In Anneal's current `skeleton` branch (`e75556f5`), `Trusted/MirSemantics.lean`
   defines 15 per-function specification predicates (`EnsuresMaxAssign`,
   `EnsuresClampAssign`, etc.), and `theory/Anneal/FunctionalTranslation.lean`
   requires a 50-line bespoke proof per function (`translate_maxAssignBody_spec`,
   etc.) to unpack `extractSymArgsAux` against raw `MirState` hypotheses.
   Below, we show that `Language.SpecOn` (already in `Trusted/Refinement.lean`)
   combined with a declarative argument-binding telescope (`ArgSpec`) in
   `theory/` allows a **single generic lifting theorem** (`verify_func_spec`)
   to discharge arbitrary `&mut`, `&`, and scalar Rust specifications without
   adding any per-function definitions to `Trusted/`.

2. **Lithium/Aeneas-Style Goal-Directed VC Generation with Shelved Side
   Conditions and Span-Indexed Diagnostics (`R-UX-01`, `R-UX-02`):**
   Inspired by RefinedRust's Lithium engine (`SHELVED_SIDECOND`,
   `LAST_RUST_PROGRAM_POINT`, `CASE_DISTINCTION_INFO`) and Aeneas's `@[step]`
   weakest-precondition calculus (`Result.ok` / `Result.fail`), we implement a
   symbolic VC generator over span-annotated MIR that shelves pure side
   conditions during symbolic execution, proves its soundness theorem
   (`vcgen_sound`), discharges valid obligations via a unified tactic
   (`anneal_vcgen`), and preserves exact source spans, obligation kinds, and
   branch traces on any unprovable obligation.
-/

namespace Anneal.Probe

/-!
## Section 1: Minimal Trusted Foundation (`Trusted/Refinement.lean` & `Trusted/MirSemantics.lean`)

Everything in `Trusted` below mirrors Anneal's existing trusted kernel boundary:
`Behavior`, `ProgramSem`, `Language`, `Language.SpecOn`, and a minimal `MirLang`
operational model. Crucially, `Trusted` contains **zero** function-specific
`Ensures*` predicates.
-/

namespace Trusted

/-- Observable outcome of a single execution trace. -/
inductive Behavior (State : Type) where
  | terminates (s : State)
  | diverges
  | goesWrong

/-- Non-deterministic execution semantics as a predicate over behaviors. -/
structure ProgramSem (State : Type) where
  allows : State → Behavior State → Prop

/-- Behavioral refinement (`sub ≤ sup`): every behavior of `sub` is allowed by
`sup`. -/
def ProgramSem.Refines {State : Type} (sub sup : ProgramSem State) : Prop :=
  ∀ init b, sub.allows init b → sup.allows init b

infix:50 " ≤ " => ProgramSem.Refines

/-- A language bundles a syntax type, state type, and operational semantics. -/
structure Language where
  Syntax : Type
  State : Type
  sem : Syntax → ProgramSem State

/-- Generic Hoare-style partial/total specification on `L.State`, mirroring
`Language.SpecOn` in `trusted/lean/Trusted/Refinement.lean` (lines 379–386). -/
def Language.SpecOn (L : Language)
    (pre : L.State → Prop)
    (post : L.State → L.State → Prop) : ProgramSem L.State where
  allows init b :=
    pre init →
    match b with
    | .terminates term => post init term
    | .diverges => False
    | .goesWrong => False

/-- Heap address for flat non-atomic memory. -/
abbrev Addr := Nat

/-- Runtime values in the miniature MIR model. -/
inductive Val where
  | int (n : Nat)
  | ptr (a : Addr)
  | unit
  deriving DecidableEq, Repr

/-- MIR machine state: local register file and flat heap memory. -/
structure MirState where
  locals : Nat → Val
  heap : Addr → Val

/-- Source span identifier attached to MIR statements and terminators. -/
structure SourceSpan where
  file : String
  line : Nat
  col : Nat
  snippet : String
  deriving DecidableEq, Repr

/-- Categorization of verification obligations for diagnostics (`R-UX-01`). -/
inductive ObligationKind where
  | arithmeticOverflow
  | divisionByZero
  | assertionFailure
  | postconditionViolation
  deriving DecidableEq, Repr

/-- Pure expressions over MIR locals and dereferences. -/
inductive Rvalue where
  | copyLocal (idx : Nat)
  | derefLocal (idx : Nat)
  | constInt (n : Nat)
  | checkedAdd (lhs rhs : Rvalue)
  | checkedSub (lhs rhs : Rvalue)
  | lt (lhs rhs : Rvalue)
  | le (lhs rhs : Rvalue)
  deriving Repr

/-- Left-hand-side place for assignments. -/
inductive Place where
  | localVar (idx : Nat)
  | derefLocal (idx : Nat)
  deriving Repr

/-- Structured MIR body with source spans on every effectful operation. -/
inductive MirStmt where
  | assign (span : SourceSpan) (dst : Place) (rv : Rvalue)
  | seq (s1 s2 : MirStmt)
  | ite (span : SourceSpan) (condDesc : String) (cond : Rvalue)
      (thenBr elseBr : MirStmt)
  | ret (span : SourceSpan)
  deriving Repr

/-- Maximum 32-bit unsigned integer bound (`U32.max`). -/
def U32_MAX : Nat := 4294967295

/-- Evaluate an `Rvalue` in `s`, returning `none` on type mismatch or arithmetic
overflow (`U32_MAX`). -/
def evalRvalue (s : MirState) : Rvalue → Option Val
  | .copyLocal idx => some (s.locals idx)
  | .derefLocal idx =>
    match s.locals idx with
    | .ptr a => some (s.heap a)
    | _ => none
  | .constInt n =>
    if n ≤ U32_MAX then some (.int n) else none
  | .checkedAdd lhs rhs =>
    match evalRvalue s lhs, evalRvalue s rhs with
    | some (.int a), some (.int b) =>
      if a + b ≤ U32_MAX then some (.int (a + b)) else none
    | _, _ => none
  | .checkedSub lhs rhs =>
    match evalRvalue s lhs, evalRvalue s rhs with
    | some (.int a), some (.int b) =>
      if b ≤ a then some (.int (a - b)) else none
    | _, _ => none
  | .lt lhs rhs =>
    match evalRvalue s lhs, evalRvalue s rhs with
    | some (.int a), some (.int b) =>
      some (.int (if a < b then 1 else 0))
    | _, _ => none
  | .le lhs rhs =>
    match evalRvalue s lhs, evalRvalue s rhs with
    | some (.int a), some (.int b) =>
      some (.int (if a ≤ b then 1 else 0))
    | _, _ => none

/-- Write `v` to `Place` in `s`, returning `none` if dereferencing a non-pointer. -/
def writePlace (s : MirState) (p : Place) (v : Val) : Option MirState :=
  match p with
  | .localVar idx =>
    some { s with locals := fun i => if i = idx then v else s.locals i }
  | .derefLocal idx =>
    match s.locals idx with
    | .ptr a =>
      some { s with heap := fun addr => if addr = a then v else s.heap addr }
    | _ => none

/-- Big-step evaluation of `MirStmt`. -/
def evalStmt (s : MirState) : MirStmt → Option MirState
  | .assign _ dst rv =>
    match evalRvalue s rv with
    | some v => writePlace s dst v
    | none => none
  | .seq s1 s2 =>
    match evalStmt s s1 with
    | some s' => evalStmt s' s2
    | none => none
  | .ite _ _ cond thenBr elseBr =>
    match evalRvalue s cond with
    | some (.int c) =>
      if c ≠ 0 then evalStmt s thenBr else evalStmt s elseBr
    | _ => none
  | .ret _ => some s

/-- The trusted `MirLang` language definition. -/
def MirLang : Language where
  Syntax := MirStmt
  State := MirState
  sem body := {
    allows init b :=
      match evalStmt init body with
      | some term => b = .terminates term
      | none => b = .goesWrong
  }

end Trusted

/-!
## Section 2: Untrusted `theory/` Layer — Declarative Calling Conventions & Generic `SpecOn` Lifting

Instead of adding `EnsuresMaxAssign`, `EnsuresClampAssign`, etc. to `Trusted`,
we define a compositional calling-convention descriptor (`FnSig`) in `theory/`
that translates user-level logical preconditions and postconditions into
`Trusted.MirLang.SpecOn`.
-/

namespace Theory

open Trusted

/-- Declarative calling convention for a Rust function's ABI:
`LogicalIn` is the tuple of initial logical values (scalars and initial pointee
values of references); `LogicalOut` is the tuple of final logical values (return
value and final pointee values of `&mut` references). -/
structure FnSig (LogicalIn LogicalOut : Type) where
  /-- Extract initial logical values and separation/validity invariants from the
  initial `MirState`. -/
  bindIn : MirState → LogicalIn → Prop
  /-- Extract updated logical values from the initial and terminal `MirState`. -/
  bindOut : MirState → MirState → LogicalOut → Prop

/-- Generic specification builder in `theory/` parameterized by any `FnSig`.
Notice that this lowers directly to `Trusted.MirLang.SpecOn` without needing any
function-specific definitions in `Trusted`. -/
def FuncSpec {LogicalIn LogicalOut : Type}
    (sig : FnSig LogicalIn LogicalOut)
    (pre : LogicalIn → Prop)
    (post : LogicalIn → LogicalOut → Prop) : ProgramSem MirState :=
  MirLang.SpecOn
    (fun init => ∃ x, sig.bindIn init x ∧ pre x)
    (fun init term =>
      ∀ x, sig.bindIn init x → pre x →
        ∃ y, sig.bindOut init term y ∧ post x y)

/-- Standard calling convention for `fn(&mut u32, u32)`:
- Local 1 holds `&mut u32` pointing to address `a` with initial pointee `dest0`.
- Local 2 holds scalar `other : u32`.
- On return, local 0 holds `.unit` and heap address `a` holds `destFinal`. -/
def sigMutU32ValU32 : FnSig (Nat × Nat) Nat where
  bindIn init := fun (dest0, other) =>
    ∃ a, init.locals 1 = .ptr a ∧ init.heap a = .int dest0 ∧
      dest0 ≤ U32_MAX ∧ init.locals 2 = .int other ∧ other ≤ U32_MAX
  bindOut init term := fun destFinal =>
    ∃ a, init.locals 1 = .ptr a ∧ term.heap a = .int destFinal

/-- Standard calling convention for `fn(&mut u32, u32, u32)`:
- Local 1 holds `&mut u32` pointing to address `a` with initial pointee `x0`.
- Local 2 holds `lo : u32`, local 3 holds `hi : u32`.
- On return, heap address `a` holds `xFinal`. -/
def sigMutU32ValU32ValU32 : FnSig (Nat × Nat × Nat) Nat where
  bindIn init := fun (x0, lo, hi) =>
    ∃ a, init.locals 1 = .ptr a ∧ init.heap a = .int x0 ∧ x0 ≤ U32_MAX ∧
      init.locals 2 = .int lo ∧ lo ≤ U32_MAX ∧
      init.locals 3 = .int hi ∧ hi ≤ U32_MAX
  bindOut init term := fun xFinal =>
    ∃ a, init.locals 1 = .ptr a ∧ term.heap a = .int xFinal

/-- Standard calling convention for pure scalar `fn(u32, u32) -> u32`:
- Local 1 holds `a : u32`, local 2 holds `b : u32`.
- On return, local 0 holds `ret : u32`. -/
def sigValU32ValU32RetU32 : FnSig (Nat × Nat) Nat where
  bindIn init := fun (a, b) =>
    init.locals 1 = .int a ∧ a ≤ U32_MAX ∧
    init.locals 2 = .int b ∧ b ≤ U32_MAX
  bindOut _init term := fun ret =>
    term.locals 0 = .int ret

/-!
## Section 3: Lithium/Aeneas-Style Symbolic VC Generator with Shelved Side Conditions

We now combine two key ideas from the primary-source investigation:

1. **Aeneas's `Result` / WP decomposition (`Aeneas/Std/WP.lean`):**
   Every operation steps into either a pure value continuation or a guarded
   verification condition.
2. **RefinedRust Lithium's `SHELVED_SIDECOND` + `LAST_RUST_PROGRAM_POINT` +
   `CASE_DISTINCTION_INFO` (`lithium/proof_state.v`, `typing/automation.v`):**
   During symbolic execution of a MIR body, side conditions (such as checked
   arithmetic bounds or postconditions) are wrapped in `ShelvedVC` carrying:
   - `span : SourceSpan` (from `LAST_RUST_PROGRAM_POINT`),
   - `kind : ObligationKind` (overflow vs. postcondition),
   - `trace : List BranchTrace` (from `CASE_DISTINCTION_INFO` branch splits),
   - `goal : Prop` (the pure mathematical proposition to discharge).
-/

/-- A single branch decision recorded along a symbolic execution path,
mirroring RefinedRust's `CASE_DISTINCTION_INFO`. -/
structure BranchTrace where
  span : SourceSpan
  condition : String
  taken : Bool
  deriving DecidableEq, Repr

/-- A shelved verification condition produced during symbolic execution,
mirroring RefinedRust's `SHELVED_SIDECOND` combined with
`LAST_RUST_PROGRAM_POINT` and `CASE_DISTINCTION_INFO`.
Because `ShelvedVC` is a `Prop` structure wrapping `goal : Prop`, tactics like
`simp`, `intro`, and `And.intro` never pierce through it accidentally, and any
unproved obligation left in the Lean goal state after automation displays the
exact source span, obligation kind, and branch path (`R-UX-01`, `R-UX-02`). -/
structure ShelvedVC (span : SourceSpan) (kind : ObligationKind)
    (trace : List BranchTrace) (goal : Prop) : Prop where
  intro ::
  proof : goal

/-- Symbolic weakest-precondition transformer (`wpStmt`) over `MirStmt`.
Given an initial state `s`, current branch trace `trace`, statement `stmt`, and
postcondition `k : MirState → Prop`, `wpStmt` computes a pure proposition
consisting solely of conjunctions, implications (guarded by branch conditions),
and `ShelvedVC`-tagged leaf obligations. -/
def wpRvalue (span : SourceSpan) (trace : List BranchTrace) (s : MirState) :
    Rvalue → (Val → Prop) → Prop
  | .copyLocal idx, k => k (s.locals idx)
  | .derefLocal idx, k =>
    match s.locals idx with
    | .ptr a => k (s.heap a)
    | _ => False
  | .constInt n, k =>
    ShelvedVC span .arithmeticOverflow trace (n ≤ U32_MAX) ∧ k (.int n)
  | .checkedAdd lhs rhs, k =>
    wpRvalue span trace s lhs (fun v1 =>
      wpRvalue span trace s rhs (fun v2 =>
        match v1, v2 with
        | .int a, .int b =>
          ShelvedVC span .arithmeticOverflow trace (a + b ≤ U32_MAX) ∧
            k (.int (a + b))
        | _, _ => False))
  | .checkedSub lhs rhs, k =>
    wpRvalue span trace s lhs (fun v1 =>
      wpRvalue span trace s rhs (fun v2 =>
        match v1, v2 with
        | .int a, .int b =>
          ShelvedVC span .arithmeticOverflow trace (b ≤ a) ∧
            k (.int (a - b))
        | _, _ => False))
  | .lt lhs rhs, k =>
    wpRvalue span trace s lhs (fun v1 =>
      wpRvalue span trace s rhs (fun v2 =>
        match v1, v2 with
        | .int a, .int b => k (.int (if a < b then 1 else 0))
        | _, _ => False))
  | .le lhs rhs, k =>
    wpRvalue span trace s lhs (fun v1 =>
      wpRvalue span trace s rhs (fun v2 =>
        match v1, v2 with
        | .int a, .int b => k (.int (if a ≤ b then 1 else 0))
        | _, _ => False))

/-- Symbolic weakest precondition for a `MirStmt`. -/
def wpStmt (trace : List BranchTrace) (s : MirState) :
    MirStmt → (MirState → Prop) → Prop
  | .assign span dst rv, k =>
    wpRvalue span trace s rv (fun v =>
      match writePlace s dst v with
      | some s' => k s'
      | none => False)
  | .seq s1 s2, k =>
    wpStmt trace s s1 (fun s' => wpStmt trace s' s2 k)
  | .ite span condDesc cond thenBr elseBr, k =>
    wpRvalue span trace s cond (fun v =>
      match v with
      | .int c =>
        (c ≠ 0 →
          wpStmt (trace ++ [{ span, condition := condDesc, taken := true }])
            s thenBr k) ∧
        (c = 0 →
          wpStmt (trace ++ [{ span, condition := condDesc, taken := false }])
            s elseBr k)
      | _ => False)
  | .ret _span, k => k s

/-- Soundness of `wpRvalue`: if `wpRvalue span trace s rv k` holds, then
`evalRvalue s rv` succeeds with some value `v` satisfying `k v`. -/
theorem wpRvalue_sound (span : SourceSpan) (trace : List BranchTrace)
    (s : MirState) (rv : Rvalue) (k : Val → Prop)
    (hwp : wpRvalue span trace s rv k) :
    ∃ v, evalRvalue s rv = some v ∧ k v := by
  induction rv generalizing k with
  | copyLocal idx =>
    exact ⟨s.locals idx, rfl, hwp⟩
  | derefLocal idx =>
    simp only [wpRvalue, evalRvalue] at hwp ⊢
    cases hloc : s.locals idx <;> simp_all
  | constInt n =>
    simp only [wpRvalue, evalRvalue] at hwp ⊢
    rcases hwp with ⟨⟨hle⟩, hk⟩
    simp [hle, hk]
  | checkedAdd lhs rhs ihl ihr =>
    simp only [wpRvalue] at hwp
    rcases ihl _ hwp with ⟨v1, hev1, hwp1⟩
    rcases ihr _ hwp1 with ⟨v2, hev2, hwp2⟩
    cases v1 <;> cases v2 <;> try contradiction
    rename_i a b
    rcases hwp2 with ⟨⟨hle⟩, hk⟩
    simp only [evalRvalue, hev1, hev2, hle, ↓reduceIte]
    exact ⟨.int (a + b), rfl, hk⟩
  | checkedSub lhs rhs ihl ihr =>
    simp only [wpRvalue] at hwp
    rcases ihl _ hwp with ⟨v1, hev1, hwp1⟩
    rcases ihr _ hwp1 with ⟨v2, hev2, hwp2⟩
    cases v1 <;> cases v2 <;> try contradiction
    rename_i a b
    rcases hwp2 with ⟨⟨hle⟩, hk⟩
    simp only [evalRvalue, hev1, hev2, hle, ↓reduceIte]
    exact ⟨.int (a - b), rfl, hk⟩
  | lt lhs rhs ihl ihr =>
    simp only [wpRvalue] at hwp
    rcases ihl _ hwp with ⟨v1, hev1, hwp1⟩
    rcases ihr _ hwp1 with ⟨v2, hev2, hwp2⟩
    cases v1 <;> cases v2 <;> try contradiction
    rename_i a b
    simp only [evalRvalue, hev1, hev2]
    exact ⟨.int (if a < b then 1 else 0), rfl, hwp2⟩
  | le lhs rhs ihl ihr =>
    simp only [wpRvalue] at hwp
    rcases ihl _ hwp with ⟨v1, hev1, hwp1⟩
    rcases ihr _ hwp1 with ⟨v2, hev2, hwp2⟩
    cases v1 <;> cases v2 <;> try contradiction
    rename_i a b
    simp only [evalRvalue, hev1, hev2]
    exact ⟨.int (if a ≤ b then 1 else 0), rfl, hwp2⟩

/-- Soundness of `wpStmt`: if `wpStmt trace s stmt k` holds, then big-step MIR
evaluation `evalStmt s stmt` terminates normally (`some term`) and satisfies
`k term`. -/
theorem wpStmt_sound (trace : List BranchTrace) (s : MirState)
    (stmt : MirStmt) (k : MirState → Prop)
    (hwp : wpStmt trace s stmt k) :
    ∃ term, evalStmt s stmt = some term ∧ k term := by
  induction stmt generalizing trace s k with
  | assign span dst rv =>
    simp only [wpStmt] at hwp
    rcases wpRvalue_sound span trace s rv _ hwp with ⟨v, hev, hw⟩
    simp only [evalStmt, hev]
    cases hwp_place : writePlace s dst v <;> simp_all
  | seq s1 s2 ih1 ih2 =>
    simp only [wpStmt] at hwp
    rcases ih1 trace s _ hwp with ⟨mid, hev1, hwp2⟩
    rcases ih2 trace mid k hwp2 with ⟨term, hev2, hk⟩
    simp only [evalStmt, hev1, hev2]
    exact ⟨term, rfl, hk⟩
  | ite span condDesc cond thenBr elseBr ihThen ihElse =>
    simp only [wpStmt] at hwp
    rcases wpRvalue_sound span trace s cond _ hwp with ⟨v, hev, hbr⟩
    cases v <;> try contradiction
    rename_i c
    rcases hbr with ⟨hThen, hElse⟩
    simp only [evalStmt, hev]
    split
    · rename_i hc
      exact ihThen _ s k (hThen hc)
    · rename_i hc
      have hc0 : c = 0 := by omega
      exact ihElse _ s k (hElse hc0)
  | ret _span =>
    exact ⟨s, rfl, hwp⟩

/-- **Single Generic Specification Lifting Theorem (`verify_func_spec`):**
To prove that any `MirStmt` body refines `FuncSpec sig pre post` (which is
`MirLang.SpecOn`), it suffices to prove `wpStmt [] init body` ending in a
`ShelvedVC` postcondition obligation.
This single theorem replaces all 15 bespoke `translate_*_spec` unpacking proofs! -/
theorem verify_func_spec {LogicalIn LogicalOut : Type}
    (sig : FnSig LogicalIn LogicalOut)
    (pre : LogicalIn → Prop)
    (post : LogicalIn → LogicalOut → Prop)
    (retSpan : SourceSpan)
    (body : MirStmt)
    (hvc : ∀ init x, sig.bindIn init x → pre x →
      wpStmt [] init body (fun term =>
        ∃ y, sig.bindOut init term y ∧
          ShelvedVC retSpan .postconditionViolation [] (post x y))) :
    MirLang.sem body ≤ FuncSpec sig pre post := by
  intro init b hsem ⟨x, hbind, hpre⟩
  have hwp := hvc init x hbind hpre
  rcases wpStmt_sound [] init body _ hwp with ⟨term, heval, hpost⟩
  simp only [MirLang, heval] at hsem
  subst hsem
  intro x' hbind' hpre'
  have hwp' := hvc init x' hbind' hpre'
  rcases wpStmt_sound [] init body _ hwp' with ⟨term', heval', ⟨y, hout, ⟨hp⟩⟩⟩
  rw [heval] at heval'
  injection heval' with hterm
  subst hterm
  exact ⟨y, hout, hp⟩

/-!
## Section 4: Unified Automation Tactic (`anneal_vcgen`)

Mirroring RefinedRust's generated proof template (`rep <-! liRStep; ...
sidecond_solver`) and Aeneas's `step*` + `scalar_tac`, we define a single tactic
`anneal_vcgen` that:
1. Applies the generic `verify_func_spec` theorem.
2. Evaluates `wpStmt`, `wpRvalue`, `writePlace`, and calling-convention bindings
   symbolically using `dsimp`.
3. Splits branch conjunctions and introduces path hypotheses (`c ≠ 0` vs `c = 0`).
4. Attempts to discharge every `ShelvedVC span kind trace goal` via `omega`.
   Crucially, if a side condition is false, `try (apply ShelvedVC.intro; omega)`
   leaves the `ShelvedVC span kind trace goal` wrapper intact in the goal state!
-/

macro "anneal_vcgen" body:ident retSpan:term : tactic =>
  `(tactic| (
    refine verify_func_spec _ _ _ $retSpan _ ?_
    simp only [
      sigMutU32ValU32, sigMutU32ValU32ValU32, sigValU32ValU32RetU32,
      Prod.forall, forall_exists_index, and_imp
    ]
    intros
    simp_all only [
      $body:ident, U32_MAX,
      wpStmt, wpRvalue, writePlace,
      Val.ptr.injEq, Val.int.injEq, exists_eq_left, exists_eq_left', ↓reduceIte
    ]
    repeat' (first
      | (apply ShelvedVC.intro; solve | (try split) <;> (try simp_all) <;> (try omega))
      | refine And.intro ?_ ?_
      | (intro hbr; try (split at hbr <;> try contradiction)))
  ))

/-!
## Section 5: Empirical Validation — Three Distinct Specifications with Zero `Ensures*` Boilerplate

We now verify three distinct Rust functions against `FuncSpec` using the exact
same generic lifting theorem `verify_func_spec` and 1-line `by anneal_vcgen`
tactic:
1. `max_assign(dest: &mut u32, other: u32)`
2. `clamp_assign(x: &mut u32, lo: u32, hi: u32)` (with precondition `lo ≤ hi`)
3. `checked_add_bounded(a: u32, b: u32) -> u32` (with precondition `a + b ≤ U32_MAX`)
-/

def spanMaxIf : SourceSpan := ⟨"src/lib.rs", 10, 5, "if *dest < other"⟩
def spanMaxAssign : SourceSpan := ⟨"src/lib.rs", 11, 9, "*dest = other"⟩
def spanMaxRet : SourceSpan := ⟨"src/lib.rs", 13, 2, "}"⟩

/-- MIR for `pub fn max_assign(dest: &mut u32, other: u32)`:
`if *dest < other { *dest = other; }` -/
def maxAssignBody : MirStmt :=
  .seq
    (.ite spanMaxIf "*dest < other"
      (.lt (.derefLocal 1) (.copyLocal 2))
      (.assign spanMaxAssign (.derefLocal 1) (.copyLocal 2))
      (.ret spanMaxRet))
    (.ret spanMaxRet)

/-- Verification of `max_assign` using generic `FuncSpec` and the 1-line
`anneal_vcgen` tactic — no `EnsuresMaxAssign` in `Trusted`! -/
theorem maxAssign_verified :
    MirLang.sem maxAssignBody ≤
      FuncSpec sigMutU32ValU32
        (fun _ => True)
        (fun (dest0, other) destFinal =>
          destFinal = if dest0 < other then other else dest0) := by
  anneal_vcgen maxAssignBody spanMaxRet

def spanClampIf1 : SourceSpan := ⟨"src/lib.rs", 20, 5, "if *x < lo"⟩
def spanClampSetLo : SourceSpan := ⟨"src/lib.rs", 21, 9, "*x = lo"⟩
def spanClampIf2 : SourceSpan := ⟨"src/lib.rs", 22, 12, "else if hi < *x"⟩
def spanClampSetHi : SourceSpan := ⟨"src/lib.rs", 23, 9, "*x = hi"⟩
def spanClampRet : SourceSpan := ⟨"src/lib.rs", 25, 2, "}"⟩

/-- MIR for `pub fn clamp_assign(x: &mut u32, lo: u32, hi: u32)` with
precondition `lo ≤ hi`. -/
def clampAssignBody : MirStmt :=
  .ite spanClampIf1 "*x < lo"
    (.lt (.derefLocal 1) (.copyLocal 2))
    (.assign spanClampSetLo (.derefLocal 1) (.copyLocal 2))
    (.ite spanClampIf2 "hi < *x"
      (.lt (.copyLocal 3) (.derefLocal 1))
      (.assign spanClampSetHi (.derefLocal 1) (.copyLocal 3))
      (.ret spanClampRet))

/-- Verification of `clamp_assign` using generic `FuncSpec` and the 1-line
`anneal_vcgen` tactic — no `EnsuresClampAssign` in `Trusted`! -/
theorem clampAssign_verified :
    MirLang.sem clampAssignBody ≤
      FuncSpec sigMutU32ValU32ValU32
        (fun (_x0, lo, hi) => lo ≤ hi)
        (fun (x0, lo, hi) xFinal =>
          lo ≤ xFinal ∧ xFinal ≤ hi ∧
          (lo ≤ x0 ∧ x0 ≤ hi → xFinal = x0)) := by
  anneal_vcgen clampAssignBody spanClampRet

def spanAddStmt : SourceSpan := ⟨"src/lib.rs", 30, 5, "_0 = a + b"⟩
def spanAddRet : SourceSpan := ⟨"src/lib.rs", 31, 2, "return _0"⟩

/-- MIR for `pub fn checked_add_bounded(a: u32, b: u32) -> u32`. -/
def checkedAddBoundedBody : MirStmt :=
  .seq
    (.assign spanAddStmt (.localVar 0)
      (.checkedAdd (.copyLocal 1) (.copyLocal 2)))
    (.ret spanAddRet)

/-- Verification of `checked_add_bounded` using generic `FuncSpec` and the
1-line `anneal_vcgen` tactic — the arithmetic overflow `ShelvedVC` at
`spanAddStmt` is discharged from the user precondition `a + b ≤ U32_MAX`. -/
theorem checkedAddBounded_verified :
    MirLang.sem checkedAddBoundedBody ≤
      FuncSpec sigValU32ValU32RetU32
        (fun (a, b) => a + b ≤ U32_MAX)
        (fun (a, b) ret => ret = a + b) := by
  anneal_vcgen checkedAddBoundedBody spanAddRet

/-!
## Section 6: Span-Indexed Diagnostic Extraction (`R-UX-01`, `R-UX-02`)

When verification fails on a buggy Rust function, Anneal must report:
1. Which source span failed (`SourceSpan`: file, line, column, snippet).
2. What kind of obligation failed (`ObligationKind`: overflow vs. postcondition).
3. Which branch path (`List BranchTrace`, corresponding to RefinedRust's
   `CASE_DISTINCTION_INFO`) led to the failure.

Below we show a decidable symbolic VC collector (`collectDiagnostics`) over concrete
or bounded symbolic test cases that extracts structured `DiagnosticReport` records
from the exact same `MirStmt` AST, and we also show how an unprovable obligation
in interactive Lean proof mode stops at a readable `ShelvedVC span kind trace goal`
subgoal.
-/

/-- Structured diagnostic report emitted when a shelved obligation cannot be
discharged (`R-UX-01`, `R-UX-02`). -/
structure DiagnosticReport where
  span : SourceSpan
  kind : ObligationKind
  branchPath : List BranchTrace
  message : String
  deriving DecidableEq, Repr

/-- Collect all runtime/postcondition diagnostic failures along a concrete trace
of `MirStmt`, recording the exact `SourceSpan`, `ObligationKind`, and
`BranchTrace` stack (`CASE_DISTINCTION_INFO`). -/
def checkRvalueDiag (span : SourceSpan) (trace : List BranchTrace) (s : MirState) :
    Rvalue → Except DiagnosticReport Val
  | .copyLocal idx => .ok (s.locals idx)
  | .derefLocal idx =>
    match s.locals idx with
    | .ptr a => .ok (s.heap a)
    | _ => .error ⟨span, .assertionFailure, trace, "dereference of non-pointer"⟩
  | .constInt n =>
    if n ≤ U32_MAX then .ok (.int n)
    else .error ⟨span, .arithmeticOverflow, trace, s!"constant {n} exceeds U32_MAX"⟩
  | .checkedAdd lhs rhs => do
    let v1 ← checkRvalueDiag span trace s lhs
    let v2 ← checkRvalueDiag span trace s rhs
    match v1, v2 with
    | .int a, .int b =>
      if a + b ≤ U32_MAX then .ok (.int (a + b))
      else .error ⟨span, .arithmeticOverflow, trace,
        s!"addition overflow: {a} + {b} > U32_MAX ({U32_MAX})"⟩
    | _, _ => .error ⟨span, .assertionFailure, trace, "invalid operands to +"⟩
  | .checkedSub lhs rhs => do
    let v1 ← checkRvalueDiag span trace s lhs
    let v2 ← checkRvalueDiag span trace s rhs
    match v1, v2 with
    | .int a, .int b =>
      if b ≤ a then .ok (.int (a - b))
      else .error ⟨span, .arithmeticOverflow, trace,
        s!"subtraction underflow: {a} - {b} < 0"⟩
    | _, _ => .error ⟨span, .assertionFailure, trace, "invalid operands to -"⟩
  | .lt lhs rhs => do
    let v1 ← checkRvalueDiag span trace s lhs
    let v2 ← checkRvalueDiag span trace s rhs
    match v1, v2 with
    | .int a, .int b => .ok (.int (if a < b then 1 else 0))
    | _, _ => .error ⟨span, .assertionFailure, trace, "invalid operands to <"⟩
  | .le lhs rhs => do
    let v1 ← checkRvalueDiag span trace s lhs
    let v2 ← checkRvalueDiag span trace s rhs
    match v1, v2 with
    | .int a, .int b => .ok (.int (if a ≤ b then 1 else 0))
    | _, _ => .error ⟨span, .assertionFailure, trace, "invalid operands to <="⟩

/-- Execute a `MirStmt` while tracking `BranchTrace` (`CASE_DISTINCTION_INFO`)
and pinpointing the exact `SourceSpan` of any failure. -/
def checkStmtDiag (trace : List BranchTrace) (s : MirState) :
    MirStmt → Except DiagnosticReport MirState
  | .assign span dst rv => do
    let v ← checkRvalueDiag span trace s rv
    match writePlace s dst v with
    | some s' => .ok s'
    | none => .error ⟨span, .assertionFailure, trace, "invalid write place"⟩
  | .seq s1 s2 => do
    let s' ← checkStmtDiag trace s s1
    checkStmtDiag trace s' s2
  | .ite span condDesc cond thenBr elseBr => do
    let v ← checkRvalueDiag span trace s cond
    match v with
    | .int c =>
      if c ≠ 0 then
        checkStmtDiag (trace ++ [{ span, condition := condDesc, taken := true }]) s thenBr
      else
        checkStmtDiag (trace ++ [{ span, condition := condDesc, taken := false }]) s elseBr
    | _ => .error ⟨span, .assertionFailure, trace, "non-integer branch condition"⟩
  | .ret _span => .ok s

/-- Example buggy function:
```rust
pub fn buggy_threshold_add(x: u32, y: u32) -> u32 {
    if 100 < x {
        x + y // line 42: overflows when x + y > U32_MAX!
    } else {
        x
    }
}
```
-/
def spanBugIf : SourceSpan := ⟨"src/lib.rs", 41, 5, "if 100 < x"⟩
def spanBugAdd : SourceSpan := ⟨"src/lib.rs", 42, 9, "_0 = x + y"⟩
def spanBugElse : SourceSpan := ⟨"src/lib.rs", 44, 9, "_0 = x"⟩
def spanBugRet : SourceSpan := ⟨"src/lib.rs", 46, 2, "}"⟩

def buggyThresholdAddBody : MirStmt :=
  .seq
    (.ite spanBugIf "100 < x"
      (.lt (.constInt 100) (.copyLocal 1))
      (.assign spanBugAdd (.localVar 0) (.checkedAdd (.copyLocal 1) (.copyLocal 2)))
      (.assign spanBugElse (.localVar 0) (.copyLocal 1)))
    (.ret spanBugRet)

/-- Concrete counterexample state where `x = U32_MAX` and `y = 1`. -/
def counterexampleState : MirState where
  locals := fun
    | 1 => .int U32_MAX
    | 2 => .int 1
    | _ => .unit
  heap := fun _ => .unit

/-- Empirical test 1 (Concrete/Decidable Diagnostic Extractor):
Confirms that `checkStmtDiag` pinpoints:
- Exact file/line/col: `src/lib.rs:42:9` (`_0 = x + y`),
- Exact obligation kind: `.arithmeticOverflow`,
- Exact branch path (`CASE_DISTINCTION_INFO`): `100 < x` taken (`true`). -/
theorem buggyThresholdAdd_diagnostic_pinpoints_span_and_branch :
    checkStmtDiag [] counterexampleState buggyThresholdAddBody =
      .error {
        span := spanBugAdd
        kind := .arithmeticOverflow
        branchPath := [{ span := spanBugIf, condition := "100 < x", taken := true }]
        message := "addition overflow: 4294967295 + 1 > U32_MAX (4294967295)"
      } := rfl

/-- Empirical test 2 (Symbolic `anneal_vcgen` Residual Subgoal Isolation):
When `anneal_vcgen` runs on `buggyThresholdAddBody`, it automatically discharges:
1. The constant check `100 ≤ U32_MAX` at `spanBugIf`,
2. The `then`-branch postcondition at `spanBugRet`, and
3. The `else`-branch postcondition at `spanBugRet`,
and stops with **only** the single unprovable `ShelvedVC` at `spanBugAdd`
(`src/lib.rs:42:9`), carrying `.arithmeticOverflow` and the exact branch trace
`[{ span := spanBugIf, condition := "100 < x", taken := true }]`! -/
theorem buggyThresholdAdd_reduces_to_exact_shelved_vc
    (h_unprovable_vc : ∀ x y, x ≤ U32_MAX → y ≤ U32_MAX → 100 < x →
      ShelvedVC spanBugAdd .arithmeticOverflow
        [{ span := spanBugIf, condition := "100 < x", taken := true }]
        (x + y ≤ U32_MAX)) :
    MirLang.sem buggyThresholdAddBody ≤
      FuncSpec sigValU32ValU32RetU32
        (fun _ => True)
        (fun (x, _y) ret => 100 ≤ x ∨ ret = x) := by
  anneal_vcgen buggyThresholdAddBody spanBugRet
  apply h_unprovable_vc <;> assumption

end Theory
end Anneal.Probe
