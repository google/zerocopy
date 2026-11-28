-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Trusted.Framework
public import Trusted.Framework.Link
public import Trusted.CppAst
public import Trusted.CppSemantics

public section

namespace Anneal.CppEquiv

open Trusted.Framework Trusted.CppAst Trusted.CppSemantics

/-!
# Rung-0 C11 Proof Theory and Cross-Language Equivalence (`Anneal.CppEquiv`)

Untrusted (`0`-TCB) proof theory over `Trusted.CppSemantics` and
`Trusted.Framework.Link`:

1. **Deterministic step and reachability laws:**
   - `cppReaches_single`, `cppReaches_trans`, `cppReaches_head`, and the
     step-counted `cppReachesN_det` and `cppReachesN_terminal_unique`
   - `cppTerminates_of_trace`: a single finite terminating trace from `s0` to
     `evalStep prog sEnd = .done out` simultaneously proves `CppWellFormed`,
     `¬ CppDiverges`, `CppBehavior prog q out`, and outcome uniqueness (`0`
     axioms).
   - `cppReaches_loop_inv`: `Nat`-indexed loop-invariant induction lemma for
     arbitrary-length buffer loops.
2. **Bidirectional total functional equivalence (`BiTotalEquiv`):** Relates a
   Rung-0 C11 function execution to a pure/Rust reference specification over
   arbitrary inputs and memories.
3. **C-ABI `SimConv` constructor (`mkCAbiSimConv`):** Builds a
   `Trusted.Framework.SimConv` whose `abiCompat` rejects every callee
   signature not declared with `CppAbiKind.c`. It is a proof-side convenience
   only: it pins neither the value/memory relations nor the execution models,
   so any linking claim stated with it inherits `Trusted.Framework.Link`'s
   pinning requirement.
-/

/-- Single forward step into `CppReaches`. -/
theorem cppReaches_single (prog : CppProgram) {s1 s2 : CppState}
    (h : evalStep prog s1 = .step s2) :
    CppReaches prog s1 s2 :=
  CppReaches.tail (CppReaches.refl s1) h

/-- Transitivity of `CppReaches`. -/
theorem cppReaches_trans (prog : CppProgram) {s1 s2 s3 : CppState}
    (h1 : CppReaches prog s1 s2) (h2 : CppReaches prog s2 s3) :
    CppReaches prog s1 s3 := by
  induction h2 with
  | refl => exact h1
  | tail _ hStep ih => exact CppReaches.tail ih hStep

/-- Prepend a single step to a `CppReaches` derivation. -/
theorem cppReaches_head (prog : CppProgram) {s1 s2 s3 : CppState}
    (hStep : evalStep prog s1 = .step s2) (hRest : CppReaches prog s2 s3) :
    CppReaches prog s1 s3 :=
  cppReaches_trans prog (cppReaches_single prog hStep) hRest

/-- Step-counted deterministic execution relation. Kept `noncomputable`
because structural recursion would otherwise emit a `._unsafe_rec` helper. -/
noncomputable def CppReachesN (prog : CppProgram) :
    Nat → CppState → CppState → Prop
  | 0, s1, s2 => s1 = s2
  | n + 1, s1, s3 =>
    ∃ s2 : CppState, evalStep prog s1 = .step s2 ∧ CppReachesN prog n s2 s3

theorem cppReachesN_to_reaches (prog : CppProgram) :
    ∀ {n : Nat} {s1 s2 : CppState},
      CppReachesN prog n s1 s2 → CppReaches prog s1 s2
  | 0, _, _, hEq => by
    subst hEq
    exact CppReaches.refl _
  | n + 1, _, _, ⟨_, hStep, hRest⟩ =>
    cppReaches_head prog hStep (cppReachesN_to_reaches prog hRest)

theorem cppReachesN_tail (prog : CppProgram) :
    ∀ {n : Nat} {s1 s2 s3 : CppState},
      CppReachesN prog n s1 s2 →
      evalStep prog s2 = .step s3 →
      CppReachesN prog (n + 1) s1 s3
  | 0, _, _, _, hEq, hStep => by
    subst hEq
    exact ⟨_, hStep, rfl⟩
  | n + 1, _, _, _, ⟨sMid, hFirst, hRest⟩, hStep =>
    ⟨sMid, hFirst, cppReachesN_tail prog hRest hStep⟩

theorem cppReaches_to_reachesN (prog : CppProgram) {s1 s2 : CppState}
    (h : CppReaches prog s1 s2) :
    ∃ n : Nat, CppReachesN prog n s1 s2 := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hStep ih =>
    cases ih with
    | intro n hn => exact ⟨n + 1, cppReachesN_tail prog hn hStep⟩

/-- Determinism of `CppReachesN` for equal step counts. -/
theorem cppReachesN_det (prog : CppProgram) :
    ∀ {n : Nat} {s0 s1 s2 : CppState},
      CppReachesN prog n s0 s1 → CppReachesN prog n s0 s2 → s1 = s2
  | 0, _, _, _, h1, h2 => by
    subst h1
    exact h2
  | n + 1, _, _, _, ⟨m1, hs1, hr1⟩, ⟨m2, hs2, hr2⟩ => by
    rw [hs1] at hs2
    injection hs2 with hMid
    subst hMid
    exact cppReachesN_det prog hr1 hr2

/-- If `s0` reaches `sEnd` in `n` steps and `sEnd` does not `.step`, then any
other non-stepping terminal/faulting state reachable from `s0` in `m` steps
must equal `sEnd` (and `m = n`). -/
theorem cppReachesN_terminal_unique (prog : CppProgram) :
    ∀ {n m : Nat} {s0 s1 s2 : CppState},
      CppReachesN prog n s0 s1 →
      (∀ s', evalStep prog s1 ≠ .step s') →
      CppReachesN prog m s0 s2 →
      (∀ s', evalStep prog s2 ≠ .step s') →
      s1 = s2
  | 0, 0, _, _, _, h1, _, h2, _ => by
    subst h1
    exact h2
  | 0, _ + 1, _, _, _, h1, hStop1, ⟨sNext, hStep, _⟩, _ => by
    subst h1
    exact False.elim (hStop1 sNext hStep)
  | _ + 1, 0, _, _, _, ⟨sNext, hStep, _⟩, _, h2, hStop2 => by
    subst h2
    exact False.elim (hStop2 sNext hStep)
  | n + 1, m + 1, _, _, _, ⟨a, ha, hra⟩, hStop1, ⟨b, hb, hrb⟩, hStop2 => by
    rw [ha] at hb
    injection hb with hEq
    subst hEq
    exact cppReachesN_terminal_unique prog hra hStop1 hrb hStop2

/-- Every state in a divergent trace is `CppReachesN`-reachable in `n` steps. -/
theorem cppTrace_reachesN (prog : CppProgram) (trace : Nat → CppState)
    (hStep : ∀ k : Nat, evalStep prog (trace k) = .step (trace (k + 1))) :
    ∀ n : Nat, CppReachesN prog n (trace 0) (trace n)
  | 0 => rfl
  | n + 1 =>
    cppReachesN_tail prog (cppTrace_reachesN prog trace hStep n) (hStep n)

/-- Master constructive determinism theorem for Rung-0 C11: a single finite
terminating trace from `initCppState prog q = .ok s0` to
`evalStep prog sEnd = .done out` yields `CppWellFormed`, `¬ CppDiverges`,
`CppBehavior prog q out`, and uniqueness of `out` with zero axioms. -/
theorem cppTerminates_of_trace (prog : CppProgram) (q : CppQuery)
    (s0 sEnd : CppState) (out : CppTerminalOut)
    (hInit : initCppState prog q = .ok s0)
    (hReach : CppReaches prog s0 sEnd)
    (hDone : evalStep prog sEnd = .done out) :
    CppWellFormed prog q ∧
    ¬ CppDiverges prog q ∧
    CppBehavior prog q out ∧
    (∀ out', CppBehavior prog q out' → out' = out) := by
  have ⟨nEnd, hReachN⟩ := cppReaches_to_reachesN prog hReach
  have hStopEnd : ∀ s', evalStep prog sEnd ≠ .step s' := by
    intro s' hStep
    rw [hDone] at hStep
    cases hStep
  refine ⟨⟨⟨s0, hInit⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro k hFault
    unfold CppReachesResult at hFault
    rw [hInit] at hFault
    cases hFault with
    | intro sF hF =>
      have ⟨nF, hRF⟩ := cppReaches_to_reachesN prog hF.1
      have hStopF : ∀ s', evalStep prog sF ≠ .step s' := by
        intro s' hStep
        rw [hF.2] at hStep
        cases hStep
      have hEq := cppReachesN_terminal_unique prog hReachN hStopEnd hRF hStopF
      subst hEq
      have hContra := hF.2
      rw [hDone] at hContra
      cases hContra
  · intro hDiv
    cases hDiv with
    | intro s0' hDiv1 =>
      rw [hInit] at hDiv1
      injection hDiv1.1 with hS0Eq
      subst hS0Eq
      cases hDiv1.2 with
      | intro trace hTr =>
        have hTrN := cppTrace_reachesN prog trace hTr.2 nEnd
        rw [hTr.1] at hTrN
        have hEq := cppReachesN_det prog hReachN hTrN
        have hStep := hTr.2 nEnd
        rw [← hEq, hDone] at hStep
        cases hStep
  · unfold CppBehavior CppReachesResult
    rw [hInit]
    exact ⟨sEnd, hReach, hDone⟩
  · intro out' hBeh'
    unfold CppBehavior CppReachesResult at hBeh'
    rw [hInit] at hBeh'
    cases hBeh' with
    | intro sEnd' hE' =>
      have ⟨nEnd', hRN'⟩ := cppReaches_to_reachesN prog hE'.1
      have hStopEnd' : ∀ s', evalStep prog sEnd' ≠ .step s' := by
        intro s' hStep
        rw [hE'.2] at hStep
        cases hStep
      have hEq :=
        cppReachesN_terminal_unique prog hReachN hStopEnd hRN' hStopEnd'
      subst hEq
      have hD' := hE'.2
      rw [hDone] at hD'
      injection hD' with hOutEq
      exact hOutEq.symm

/-- `Nat`-indexed loop-invariant reachability lemma: if invariant `Inv k s`
steps from `Inv (k + 1) s` to `∃ s', CppReaches prog s s' ∧ Inv k s'`, then
`Inv n s0` reaches some `sFinal` satisfying `Inv 0 sFinal`. -/
theorem cppReaches_loop_inv (prog : CppProgram) (Inv : Nat → CppState → Prop)
    (hStep : ∀ (k : Nat) (s : CppState),
      Inv (k + 1) s → ∃ s' : CppState, CppReaches prog s s' ∧ Inv k s') :
    ∀ (n : Nat) (s0 : CppState),
      Inv n s0 → ∃ sFinal : CppState, CppReaches prog s0 sFinal ∧ Inv 0 sFinal
  | 0, s0, hInv => ⟨s0, CppReaches.refl s0, hInv⟩
  | k + 1, s0, hInv =>
    match hStep k s0 hInv with
    | ⟨s1, hR1, hInv1⟩ =>
      match cppReaches_loop_inv prog Inv hStep k s1 hInv1 with
      | ⟨sFinal, hR2, hInv0⟩ =>
        ⟨sFinal, cppReaches_trans prog hR1 hR2, hInv0⟩

/-- Existential UB fault witness helper: if `initCppState prog q = .ok s0`,
`CppReaches prog s0 sBad`, and `evalStep prog sBad = .fault .undefined`, then
`CppFaultsUB prog q`. -/
theorem cppFaultsUB_of_trace (prog : CppProgram) (q : CppQuery)
    (s0 sBad : CppState)
    (hInit : initCppState prog q = .ok s0)
    (hReach : CppReaches prog s0 sBad)
    (hFault : evalStep prog sBad = .fault .undefined) :
    CppFaultsUB prog q := by
  unfold CppFaultsUB CppReachesResult
  rw [hInit]
  exact ⟨sBad, hReach, hFault⟩

/-- Bidirectional total functional equivalence between the Rung-0 C11 function
body `body = prog.bodies[defId]` and a pure/Rust reference specification
`specFn : SpecIn → SpecOut`, with record layouts taken from `prog.records`:
1. **Forward refinement:** every valid C11 query `q` related to an input `x`
   lies in the body's entry domain, terminates UB-freely (`CppWellFormed`,
   `¬ CppDiverges`), and every terminal outcome is a normal return that
   satisfies `CppReturnValid` and matches `specFn x` via `relOut`.
2. **Backward completeness:** every pure specification input `x` has a related
   C11 query. -/
@[expose] def BiTotalEquiv {SpecIn SpecOut : Type}
    (policy : CppLangPolicy) (prog : CppProgram) (defId : Nat) (body : CppBody)
    (specFn : SpecIn → SpecOut)
    (relIn : SpecIn → CppQuery → Prop)
    (relOut : SpecIn → SpecOut → CppVal → CppMemory → Prop) : Prop :=
  let ep := cppExecForBody prog defId
  cppGetElem? prog.bodies defId = some body ∧
  (∀ (x : SpecIn) (q : CppQuery),
    relIn x q →
    CppEntryDom policy prog.records body q ∧
    CppWellFormed ep q ∧
    ¬ CppDiverges ep q ∧
    (∃ r m, CppBehavior ep q (.returned { ret := r, mem := m }) ∧
      CppReturnValid policy prog.records body r m ∧
      relOut x (specFn x) r m) ∧
    (∀ out, CppBehavior ep q out →
      ∃ r m, out = .returned { ret := r, mem := m } ∧
        CppReturnValid policy prog.records body r m ∧
        relOut x (specFn x) r m)) ∧
  (∀ x : SpecIn,
    ∃ q : CppQuery, relIn x q)

/-- Construct a `Trusted.Framework.SimConv` targeting a C-ABI
(`CppAbiKind.c`) Rung-0 C11 callee from an arbitrary caller profile
`(SigA, QA, RA, MA)`. `abiCompat` conjoins the caller-supplied `sigCompat` with
`sb.abi = .c`; the query, return, unwind, and abort relations are passed
through unchanged. Whether each side's `safetyPre` applies is chosen per body
by `CrossLangLinkedTheorem`, not here. -/
@[expose] noncomputable def mkCAbiSimConv
    {SigA QA RA MA Frame : Type}
    (sigCompat : SigA → CppSignature → Bool)
    (relQuery : Frame → QA → CppQuery → Prop)
    (relReturn : Frame → CppVal → CppMemory → RA → MA → Prop)
    (relUnwind : Frame → CppMemory → MA → Prop)
    (relAbort : Frame → CppMemory → MA → Prop) :
    SimConv SigA QA RA MA CppSignature CppQuery CppVal CppMemory Frame :=
  { abiCompat := fun sa sb => CppAbiKind.beq sb.abi .c && sigCompat sa sb
    relQuery := relQuery
    relReturn := relReturn
    relUnwind := relUnwind
    relAbort := relAbort }

/-- `mkCAbiSimConv` is ABI-compatible only with `CppAbiKind.c` callees whose
signatures also pass `sigCompat`. -/
theorem mkCAbiSimConv_abiCompat {SigA QA RA MA Frame : Type}
    {sigCompat : SigA → CppSignature → Bool}
    {relQuery : Frame → QA → CppQuery → Prop}
    {relReturn : Frame → CppVal → CppMemory → RA → MA → Prop}
    {relUnwind : Frame → CppMemory → MA → Prop}
    {relAbort : Frame → CppMemory → MA → Prop}
    {sa : SigA} {sb : CppSignature}
    (h : (mkCAbiSimConv sigCompat relQuery relReturn relUnwind
      relAbort).abiCompat sa sb = true) :
    CppAbiKind.beq sb.abi .c = true ∧ sigCompat sa sb = true := by
  have h' : (CppAbiKind.beq sb.abi .c && sigCompat sa sb) = true := h
  cases hAbi : CppAbiKind.beq sb.abi .c with
  | false =>
    rw [hAbi] at h'
    cases h'
  | true =>
    rw [hAbi] at h'
    exact ⟨rfl, h'⟩

/-- A C-ABI convention never discharges a stub with an Itanium C++ callee:
`StubDischargedByVerifiedCallee` fails whenever the callee entry's signature
uses `CppAbiKind.cxxItanium`. -/
theorem mkCAbiSimConv_rejects_cxxItanium {SigA QA RA MA Frame : Type}
    {sigCompat : SigA → CppSignature → Bool}
    {relQuery : Frame → QA → CppQuery → Prop}
    {relReturn : Frame → CppVal → CppMemory → RA → MA → Prop}
    {relUnwind : Frame → CppMemory → MA → Prop}
    {relAbort : Frame → CppMemory → MA → Prop}
    (callerStubIsUnsafe calleeIsUnsafe : Bool)
    (callerEntryDom : QA → Prop) (callerReturnValid : RA → MA → Prop)
    (callerMemValid : MA → Prop) (calleeEntryDom : CppQuery → Prop)
    (calleeReturnValid : CppVal → CppMemory → Prop)
    (calleeMemValid : CppMemory → Prop)
    (s : AssumedStub SigA QA RA MA) (e : CppVerifiedEntry)
    (hItanium : e.sig.abi = .cxxItanium) :
    ¬ StubDischargedByVerifiedCallee
        (mkCAbiSimConv (Frame := Frame) sigCompat relQuery relReturn
          relUnwind relAbort)
        callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDis
  have hAbi := (mkCAbiSimConv_abiCompat hDis.2.1).1
  rw [hItanium] at hAbi
  cases hAbi

/-! ## Execution canaries

Bounded runs of small programs through `initCppState` and `evalStep`, checked
by the kernel, pinning down behavior the fail-closed rules rely on. -/

/-- Run `prog` for at most `n` steps from `s`. -/
@[expose] noncomputable def cppRunFrom (prog : CppProgram) :
    Nat → CppState → CppStepResult CppState CppTerminalOut
  | 0, s => .step s
  | n + 1, s =>
    match evalStep prog s with
    | .step s' => cppRunFrom prog n s'
    | .done o  => .done o
    | .fault k => .fault k

/-- Run `prog` on query `q` for at most `n` steps. -/
@[expose] noncomputable def cppRun (prog : CppProgram) (q : CppQuery)
    (n : Nat) :
    CppStepResult CppState CppTerminalOut :=
  match initCppState prog q with
  | .ok s    => cppRunFrom prog n s
  | .error k => .fault k

/-- Canary policy: LP64, little-endian, no strict aliasing, ISO overflow. -/
@[expose] def cnPolicy : CppLangPolicy :=
  { pointerWidthBits := 64, charIsSigned := true, strictAliasing := false,
    signedOverflow := .isoUB, exceptionsOff := true }

/-- `int32_t`. -/
@[expose] def cnI32 : CppTy := .int .w32 .signed false

/-- `int32_t *`. -/
@[expose] def cnPI32 : CppTy := .ptr cnI32 false false false

/-- `uint64_t`, used for array indices. -/
@[expose] def cnU64 : CppTy := .int .w64 .unsigned false

/-- The whole-local place `_i`. -/
@[expose] def cnL (i : Nat) : CppPlace := { base := i, projs := [] }

/-- Read whole local `_i` at type `ty`. -/
@[expose] def cnR (i : Nat) (ty : CppTy) : CppExpr := .readPlace (cnL i) ty

/-- An `int32_t` constant. -/
@[expose] def cnC (v : Int) : CppExpr := .constInt .w32 .signed false v

/-- A one-block, zero-parameter-or-more C function returning `ret`. -/
@[expose] def cnBody (params : List CppTy) (ret : CppTy)
    (locals : List CppLocalDecl) (stmts : List CppStmt) : CppBody :=
  { identity := "f", isExternal := false,
    sig := { abi := .c, params := params, ret := ret },
    locals := locals, blocks := [{ stmts := stmts, term := .ret }],
    entryBlock := 0 }

/-- A single-function program. -/
@[expose] def cnProg (policy : CppLangPolicy) (records : List CppRecordDef)
    (b : CppBody) : CppProgram :=
  { policy := policy, isPartial := false, records := records, bodies := [b],
    entryDefId := 0 }

/-- `int32_t f(int32_t x) { return x + 1; }` -/
@[expose] def cnIncBody : CppBody :=
  cnBody [cnI32] cnI32 [{ ty := cnI32, isParam := false },
    { ty := cnI32, isParam := true }]
    [.assign (cnL 0) cnI32 (.binary .add cnI32 (cnR 1 cnI32) (cnC 1))]

/-- `INT32_MAX + 1` is undefined under ISO overflow rules. -/
theorem canary_isoUB_overflow :
    cppRun (cnProg cnPolicy [] cnIncBody)
      { args := [.int .w32 .signed 2147483647] } 4 = .fault .undefined := rfl

/-- `INT32_MAX + 1` wraps to `INT32_MIN` under `-fwrapv`. -/
theorem canary_wrapv_wraps :
    ∃ m, cppRun (cnProg { cnPolicy with signedOverflow := .wrapv } []
        cnIncBody)
      { args := [.int .w32 .signed 2147483647] } 4 =
      .done (.returned { ret := .int .w32 .signed 2147483648, mem := m }) :=
  ⟨_, rfl⟩

/-- `int32_t *p; { int32_t x = 1; p = &x; } return *p;` reads through a
dangling pointer. -/
theorem canary_dangling_read :
    cppRun (cnProg cnPolicy []
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false }, { ty := cnI32, isParam := false },
           { ty := cnPI32, isParam := false }]
          [.storageLive 1, .assign (cnL 1) cnI32 (cnC 1),
           .assign (cnL 2) cnPI32 (.addrOf (cnL 1) cnPI32), .storageDead 1,
           .assign (cnL 0) cnI32 (.readPlace { base := 2, projs := [.deref] }
             cnI32)]))
      { args := [] } 8 = .fault .undefined := rfl

/-- Control for `canary_dangling_read`: while `x` is live, `*p` reads it. -/
theorem canary_live_read :
    ∃ m, cppRun (cnProg cnPolicy []
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false }, { ty := cnI32, isParam := false },
           { ty := cnPI32, isParam := false }]
          [.storageLive 1, .assign (cnL 1) cnI32 (cnC 1),
           .assign (cnL 2) cnPI32 (.addrOf (cnL 1) cnPI32),
           .assign (cnL 0) cnI32 (.readPlace { base := 2, projs := [.deref] }
             cnI32)]))
      { args := [] } 8 =
      .done (.returned { ret := .int .w32 .signed 1, mem := m }) := ⟨_, rfl⟩

/-- `struct __attribute__((packed)) P { uint8_t a; int32_t b; }`. -/
@[expose] def cnPacked : CppRecordDef :=
  { recordId := "P", isUnion := false, sizeBytes := 5, alignBytes := 1,
    fields := [{ name := "a", offsetBits := 0, bitWidth := none,
                 ty := .int .w8 .unsigned false },
               { name := "b", offsetBits := 8, bitWidth := none,
                 ty := cnI32 }] }

/-- `struct P s; s.b = 7; return s.b;` reads a member of a packed record at
the record's alignment. -/
theorem canary_packed_member :
    ∃ m, cppRun (cnProg cnPolicy [cnPacked]
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false },
           { ty := .record "P", isParam := false }]
          [.assign { base := 1, projs := [.field "P" 1 cnI32] } cnI32 (cnC 7),
           .assign (cnL 0) cnI32
             (.readPlace { base := 1, projs := [.field "P" 1 cnI32] } cnI32)]))
      { args := [] } 4 =
      .done (.returned { ret := .int .w32 .signed 7, mem := m }) := ⟨_, rfl⟩

/-- Control for `canary_packed_member`: without packing, the member at byte
offset 1 is misaligned. -/
theorem canary_unpacked_misaligned :
    cppRun (cnProg cnPolicy [{ cnPacked with alignBytes := 4 }]
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false },
           { ty := .record "P", isParam := false }]
          [.assign { base := 1, projs := [.field "P" 1 cnI32] } cnI32 (cnC 7)]))
      { args := [] } 4 = .fault .undefined := rfl

/-- `struct Pd { uint8_t a; int32_t b; }`, with three padding bytes. -/
@[expose] def cnPadded : CppRecordDef :=
  { recordId := "Pd", isUnion := false, sizeBytes := 8, alignBytes := 4,
    fields := [{ name := "a", offsetBits := 0, bitWidth := none,
                 ty := .int .w8 .unsigned false },
               { name := "b", offsetBits := 32, bitWidth := none,
                 ty := cnI32 }] }

/-- `struct Pd s = {}; s.b = 42; return s.b;` zero-initializes a padded
record and accesses a member. -/
theorem canary_zeroInit_padded :
    ∃ m, cppRun (cnProg cnPolicy [cnPadded]
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false },
           { ty := .record "Pd", isParam := false }]
          [.zeroInit (cnL 1) (.record "Pd"),
           .assign { base := 1, projs := [.field "Pd" 1 cnI32] } cnI32 (cnC 42),
           .assign (cnL 0) cnI32
             (.readPlace { base := 1, projs := [.field "Pd" 1 cnI32] } cnI32)]))
      { args := [] } 6 =
      .done (.returned { ret := .int .w32 .signed 42, mem := m }) := ⟨_, rfl⟩

/-- `struct Pd s = {}, t; t = s;` copies a padded record by value. -/
theorem canary_padded_copy_unsupported :
    cppRun (cnProg cnPolicy [cnPadded]
        (cnBody [] .void
          [{ ty := .void, isParam := false },
           { ty := .record "Pd", isParam := false },
           { ty := .record "Pd", isParam := false }]
          [.zeroInit (cnL 1) (.record "Pd"),
           .assign (cnL 2) (.record "Pd") (cnR 1 (.record "Pd"))]))
      { args := [] } 6 = .fault .unsupported := rfl

/-- `std::bit_cast<uint8_t>(true)`: `bool` has padding bits. -/
theorem canary_bitCast_bool_unsupported :
    cppRun (cnProg cnPolicy []
        (cnBody [] (.int .w8 .unsigned false)
          [{ ty := .int .w8 .unsigned false, isParam := false }]
          [.assign (cnL 0) (.int .w8 .unsigned false)
            (.bitCast .bool (.int .w8 .unsigned false) (.constBool true))]))
      { args := [] } 4 = .fault .unsupported := rfl

/-- `struct BB { bool b : 8; }`: a `bool` bit-field has padding bits. -/
theorem canary_bool_bitfield_padded :
    tyHasNoPadding cnPolicy
      [{ recordId := "BB", isUnion := false, sizeBytes := 1, alignBytes := 1,
         fields := [{ name := "b", offsetBits := 0, bitWidth := some 8,
                      ty := .bool }] }]
      false 16 (.record "BB") = false := rfl

/-- `const int32_t x = 1; *(int32_t *)&x = 2;` modifies a `const` object. -/
theorem canary_const_write :
    cppRun (cnProg cnPolicy []
        (cnBody [] .void
          [{ ty := .void, isParam := false },
           { ty := cnI32, isParam := false, isConst := true },
           { ty := cnPI32, isParam := false }]
          [.assign (cnL 1) cnI32 (cnC 1),
           .assign (cnL 2) cnPI32 (.addrOf (cnL 1) cnPI32),
           .assign { base := 2, projs := [.deref] } cnI32 (cnC 2)]))
      { args := [] } 6 = .fault .undefined := rfl

/-- Control for `canary_const_write`: the same store to a non-`const` local
succeeds. -/
theorem canary_nonconst_write :
    ∃ m, cppRun (cnProg cnPolicy []
        (cnBody [] .void
          [{ ty := .void, isParam := false },
           { ty := cnI32, isParam := false },
           { ty := cnPI32, isParam := false }]
          [.assign (cnL 1) cnI32 (cnC 1),
           .assign (cnL 2) cnPI32 (.addrOf (cnL 1) cnPI32),
           .assign { base := 2, projs := [.deref] } cnI32 (cnC 2)]))
      { args := [] } 6 = .done (.returned { ret := .void, mem := m }) :=
  ⟨_, rfl⟩

/-- `struct W { int32_t a, b; }`, padding-free. -/
@[expose] def cnW : CppRecordDef :=
  { recordId := "W", isUnion := false, sizeBytes := 8, alignBytes := 4,
    fields := [{ name := "a", offsetBits := 0, bitWidth := none, ty := cnI32 },
               { name := "b", offsetBits := 32, bitWidth := none,
                 ty := cnI32 }] }

/-- `struct W *`. -/
@[expose] def cnPW : CppTy := .ptr (.record "W") false false false

/-- `int32_t buf[3] = {};`, then `struct W *p = (struct W *)&buf[0];`,
`struct W *q = (struct W *)&buf[1];`, and `*p = *q;` assigns between
partially overlapping objects. -/
theorem canary_overlap_copy :
    cppRun (cnProg cnPolicy [cnW]
        (cnBody [] .void
          [{ ty := .void, isParam := false },
           { ty := .array cnI32 3, isParam := false },
           { ty := cnPW, isParam := false }, { ty := cnPW, isParam := false },
           { ty := cnU64, isParam := false }, { ty := cnU64, isParam := false }]
          [.zeroInit (cnL 1) (.array cnI32 3),
           .assign (cnL 4) cnU64 (.constInt .w64 .unsigned false 0),
           .assign (cnL 5) cnU64 (.constInt .w64 .unsigned false 1),
           .assign (cnL 2) cnPW (.ptrCast cnPW
             (.addrOf { base := 1, projs := [.index cnI32 4] } cnPI32)),
           .assign (cnL 3) cnPW (.ptrCast cnPW
             (.addrOf { base := 1, projs := [.index cnI32 5] } cnPI32)),
           .assign { base := 2, projs := [.deref] } (.record "W")
             (.readPlace { base := 3, projs := [.deref] } (.record "W"))]))
      { args := [] } 10 = .fault .undefined := rfl

/-- Control for `canary_overlap_copy`: copying between disjoint halves of a
four-element buffer succeeds. -/
theorem canary_disjoint_copy :
    ∃ m, cppRun (cnProg cnPolicy [cnW]
        (cnBody [] .void
          [{ ty := .void, isParam := false },
           { ty := .array cnI32 4, isParam := false },
           { ty := cnPW, isParam := false }, { ty := cnPW, isParam := false },
           { ty := cnU64, isParam := false }, { ty := cnU64, isParam := false }]
          [.zeroInit (cnL 1) (.array cnI32 4),
           .assign (cnL 4) cnU64 (.constInt .w64 .unsigned false 0),
           .assign (cnL 5) cnU64 (.constInt .w64 .unsigned false 2),
           .assign (cnL 2) cnPW (.ptrCast cnPW
             (.addrOf { base := 1, projs := [.index cnI32 4] } cnPI32)),
           .assign (cnL 3) cnPW (.ptrCast cnPW
             (.addrOf { base := 1, projs := [.index cnI32 5] } cnPI32)),
           .assign { base := 2, projs := [.deref] } (.record "W")
             (.readPlace { base := 3, projs := [.deref] } (.record "W"))]))
      { args := [] } 10 = .done (.returned { ret := .void, mem := m }) :=
  ⟨_, rfl⟩

/-- `struct TA { int32_t a[2]; int32_t b[2]; }`. -/
@[expose] def cnTA : CppRecordDef :=
  { recordId := "TA", isUnion := false, sizeBytes := 16, alignBytes := 4,
    fields := [{ name := "a", offsetBits := 0, bitWidth := none,
                 ty := .array cnI32 2 },
               { name := "b", offsetBits := 64, bitWidth := none,
                 ty := .array cnI32 2 }] }

/-- `struct TA s = {}; int32_t *p = &s.a[0]; return p[3];` indexes past the
end of the member array `a`, though still inside `s`. -/
theorem canary_subobject_oob :
    cppRun (cnProg cnPolicy [cnTA]
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false },
           { ty := .record "TA", isParam := false },
           { ty := cnPI32, isParam := false },
           { ty := cnU64, isParam := false }, { ty := cnU64, isParam := false }]
          [.zeroInit (cnL 1) (.record "TA"),
           .assign (cnL 3) cnU64 (.constInt .w64 .unsigned false 0),
           .assign (cnL 4) cnU64 (.constInt .w64 .unsigned false 3),
           .assign (cnL 2) cnPI32
             (.addrOf { base := 1,
                        projs := [.field "TA" 0 (.array cnI32 2),
                                  .index cnI32 3] } cnPI32),
           .assign (cnL 0) cnI32
             (.readPlace { base := 2, projs := [.index cnI32 4] } cnI32)]))
      { args := [] } 10 = .fault .undefined := rfl

/-- Control for `canary_subobject_oob`: `p[1]` stays inside `s.a`. -/
theorem canary_subobject_inbounds :
    ∃ m, cppRun (cnProg cnPolicy [cnTA]
        (cnBody [] cnI32
          [{ ty := cnI32, isParam := false },
           { ty := .record "TA", isParam := false },
           { ty := cnPI32, isParam := false },
           { ty := cnU64, isParam := false }, { ty := cnU64, isParam := false }]
          [.zeroInit (cnL 1) (.record "TA"),
           .assign (cnL 3) cnU64 (.constInt .w64 .unsigned false 0),
           .assign (cnL 4) cnU64 (.constInt .w64 .unsigned false 1),
           .assign (cnL 2) cnPI32
             (.addrOf { base := 1,
                        projs := [.field "TA" 0 (.array cnI32 2),
                                  .index cnI32 3] } cnPI32),
           .assign (cnL 0) cnI32
             (.readPlace { base := 2, projs := [.index cnI32 4] } cnI32)]))
      { args := [] } 10 =
      .done (.returned { ret := .int .w32 .signed 0, mem := m }) := ⟨_, rfl⟩

/-- `const struct Pd s = {}; *(int32_t *)&s.b = 99;` zero-initializes a
`const` record, then modifies it. -/
theorem canary_const_zeroInit_write :
    cppRun (cnProg cnPolicy [cnPadded]
        (cnBody [] .void
          [{ ty := .void, isParam := false },
           { ty := .record "Pd", isParam := false, isConst := true },
           { ty := cnPI32, isParam := false }]
          [.zeroInit (cnL 1) (.record "Pd"),
           .assign (cnL 2) cnPI32
             (.addrOf { base := 1, projs := [.field "Pd" 1 cnI32] } cnPI32),
           .assign { base := 2, projs := [.deref] } cnI32 (cnC 99)]))
      { args := [] } 6 = .fault .undefined := rfl

/-- `struct TA s = {}; return &s.a[0] < &m[j];`, where `m` is member
`field2` of `s` (`a` or `b`). -/
@[expose] def cnRelBody (field2 : Nat) (j : Nat) : CppBody :=
  cnBody [] .bool
    [{ ty := .bool, isParam := false },
     { ty := .record "TA", isParam := false },
     { ty := cnPI32, isParam := false }, { ty := cnPI32, isParam := false },
     { ty := cnU64, isParam := false }, { ty := cnU64, isParam := false }]
    [.zeroInit (cnL 1) (.record "TA"),
     .assign (cnL 4) cnU64 (.constInt .w64 .unsigned false 0),
     .assign (cnL 5) cnU64 (.constInt .w64 .unsigned false j),
     .assign (cnL 2) cnPI32
       (.addrOf { base := 1,
                  projs := [.field "TA" 0 (.array cnI32 2), .index cnI32 4] }
         cnPI32),
     .assign (cnL 3) cnPI32
       (.addrOf { base := 1,
                  projs := [.field "TA" field2 (.array cnI32 2),
                            .index cnI32 5] } cnPI32),
     .assign (cnL 0) .bool (.binary .lt .bool (cnR 2 cnPI32) (cnR 3 cnPI32))]

/-- `&s.a[0] < &s.b[0]` compares pointers into distinct subobjects. -/
theorem canary_subobject_rel_unsupported :
    cppRun (cnProg cnPolicy [cnTA] (cnRelBody 1 0)) { args := [] } 10 =
      .fault .unsupported := rfl

/-- Control: `&s.a[0] < &s.a[1]` compares within one array. -/
theorem canary_subobject_rel_same_array :
    ∃ m, cppRun (cnProg cnPolicy [cnTA] (cnRelBody 0 1)) { args := [] } 10 =
      .done (.returned { ret := .bool true, mem := m }) := ⟨_, rfl⟩

/-- A pointer value at address `2^64` is not a valid LP64 pointer. -/
theorem canary_ptr_addr_bound :
    checkCppVal cnPolicy [] (.ptr none (Nat.pow 2 64) none) cnPI32 = false :=
  rfl

end Anneal.CppEquiv

end
