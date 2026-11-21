-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Probe: Reentrant Mixed MIR↔ISA Call Stacks, Tree Borrows Protectors,
Provenance Exposure, Cross-Allocator Disjointness, and Two-Oracle Pass-2 Correspondence

Self-contained Lean 4 (`v4.34.1`) formalization using strictly Lean's standard
`Init` library (zero external dependencies, zero `sorry`, zero `axiom`, zero
`partial`, zero `native_decide`, zero Iris COFEs or step-indexing).

This module establishes:
1. **Part A (Mixed MIR↔ISA Interleaved Call Stack & Big-Step Impossibility):**
   - Models Tree Borrows `FnEntry` protectors, explicit provenance exposure
     (`exposed : List AllocId`), allocator-domain tags
     (`AllocDomain := rustGlobal | foreignC | rustStack`), and `"C"` vs.
     `"C-unwind"` unwinding boundaries.
   - Proves `big_step_bridge_blind_to_callback_semantics`,
     `reentrant_stack_preserves_outer_protector`,
     `reentrant_callback_child_write_activates_outer`,
     `reentrant_callback_sibling_write_triggers_outer_protector_ub`,
     `reentrant_callback_foreign_read_then_outer_write_ub`,
     `unexposed_stack_local_guess_is_ub`,
     `cross_allocator_and_malloc_zero_laws`, and `ffi_unwind_abi_laws`.
2. **Part B (Parameterized Leaf External Oracle & Two-Oracle Pass-2 Composition):**
   - Proves `horizontal_two_oracle_composition` and
     `parametric_oracle_correspondence` preserving `BehaviorTrace`,
     `FaultTrace`, and `DivergesTrace`.
   - Proves `closed_terminal_out_insufficient_for_effectful_ffi` (negative
     canary proving trace-indexed behaviors are mandatory once external effects
     enter).
3. **Part C (Arbitrarily Reentrant Heterogeneous MIR↔ISA Stack Composition):**
   - Formalizes a CompCertO/CompCertM-style multi-step heterogeneous call stack
     (`LinkFrame SM SI`, `linkStep`) where MIR can call ISA, ISA can invoke
     reentrant MIR callbacks, MIR can call ISA again to arbitrary depth, and
     frames pop or fault.
   - Proves `reentrant_heterogeneous_stack_composition`: combining open MIR
     simulation (`M_anneal ~ M_ref`) and open ISA simulation (`I_anneal ~ I_ref`)
     across a shared call/return/memory interface yields exact `BehaviorTrace`,
     `FaultTrace`, and `DivergesTrace` equivalence of the arbitrarily reentrant
     linked machine `M_anneal ⊕_stack I_anneal ~ M_ref ⊕_stack I_ref` — with
     ZERO Iris COFEs and ZERO step-indexing.
-/

namespace ReentrantFfiAndOracleProbe

/-! ## Part A: Heterogeneous MIR↔ISA Interleaved Call Stack, Tree Borrows & Provenance -/

abbrev AllocId := Nat
abbrev BorTag := Nat
abbrev FrameId := Nat
abbrev Addr := Nat

/-- Allocator ownership domain in a shared flat ISA virtual address space. -/
inductive AllocDomain where
  | rustGlobal (size : Nat) (align : Nat)
  | foreignC (size : Nat)
  | rustStack (owner : FrameId)

/-- Tree Borrows 6-variant (7-state) permission lattice (`Miri/TreeBorrows/Permissions.lean`). -/
inductive TbPerm where
  | cell
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | unique
  | frozen
  | disabled

inductive AccessKind where
  | read
  | write

inductive AccessRel where
  | local_
  | foreign

inductive TbStepOut where
  | ok (p : TbPerm)
  | ub

/-- Exact single-location Tree Borrows transition (`Miri/TreeBorrows/Permissions.lean:62-112`),
including protected `Disabled` UB for accessed protected tags (`TreeState.lean`). -/
def tbStep (kind : AccessKind) (rel : AccessRel) (old : TbPerm)
    (isProtected : Bool) (accessed : Bool) : TbStepOut :=
  match kind, rel with
  | .read, .local_ =>
    match old with
    | .disabled => .ub
    | p => .ok p
  | .write, .local_ =>
    match old with
    | .cell => .ok .cell
    | .reservedFrz true => if isProtected then .ub else .ok .unique
    | .reservedFrz false => .ok .unique
    | .reservedIM => .ok .unique
    | .unique => .ok .unique
    | .frozen => .ub
    | .disabled => .ub
  | .read, .foreign =>
    match old with
    | .cell => .ok .cell
    | .frozen => .ok .frozen
    | .disabled => .ok .disabled
    | .reservedFrz _ =>
      if isProtected then .ok (.reservedFrz true) else .ok old
    | .reservedIM => .ok .reservedIM
    | .unique =>
      if isProtected then
        if accessed then .ub else .ok .disabled
      else .ok .frozen
  | .write, .foreign =>
    match old with
    | .cell => .ok .cell
    | .reservedIM => .ok .reservedIM
    | .disabled => .ok .disabled
    | _ =>
      if isProtected && accessed then .ub else .ok .disabled

/-- ABI unwinding category (`rust-lang/reference` `r[items.fn.extern.unwind.behavior]`). -/
inductive AbiUnwind where
  | nonUnwindingC     -- `extern "C"`
  | unwindingC        -- `extern "C-unwind"`

inductive UnwindOrigin where
  | rustPanic
  | foreignException

inductive UnwindBoundaryOutcome where
  | propagateUnwind
  | deterministicAbort
  | ub

/-- Normative Rust Reference unwinding table across FFI ABI boundaries (`panic=unwind`). -/
def evalUnwindBoundary (abi : AbiUnwind) (origin : UnwindOrigin) : UnwindBoundaryOutcome :=
  match abi, origin with
  | .unwindingC, .rustPanic => .propagateUnwind
  | .unwindingC, .foreignException => .propagateUnwind
  | .nonUnwindingC, .rustPanic => .deterministicAbort
  | .nonUnwindingC, .foreignException => .ub

/-- A single node in an allocation's borrow tree (simplified single-range per alloc). -/
structure BorrowNode where
  tag : BorTag
  parent : Option BorTag
  perm : TbPerm
  accessed : Bool
  isExposed : Bool

/-- Allocation record combining flat ISA base address, allocator tag, and borrow tree. -/
structure SharedAlloc where
  allocId : AllocId
  baseAddr : Addr
  size : Nat
  domain : AllocDomain
  live : Bool
  nodes : List BorrowNode

/-- Active FnEntry protector bound to a specific Rust MIR call frame. -/
structure ActiveProtector where
  frameId : FrameId
  allocId : AllocId
  tag : BorTag

/-- Minimal pointer provenance: concrete `(allocId, tag)`, `wildcard`, or `none` (`dangling`). -/
inductive PtrProv where
  | concrete (allocId : AllocId) (tag : BorTag)
  | wildcard
  | none

structure PtrVal where
  addr : Addr
  prov : PtrProv

structure MixedHeap where
  allocs : List SharedAlloc
  exposed : List AllocId
  protectors : List ActiveProtector

/-- Check whether `allocId` is in the global `exposed` set (`GlobalState.lean:347`). -/
def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if Nat.beq x y then true else memNat x ys

/-- Resolve a raw address under PNVI-ae-udi / Miri `allocIdFromAddr` (`GlobalState.lean:324-351`):
an unexposed allocation can NEVER be recovered from a guessed integer address. -/
def resolveWildcardAddr (h : MixedHeap) (a : Addr) : Option AllocId :=
  let rec go : List SharedAlloc → Option AllocId
    | [] => none
    | al :: rest =>
      if al.live && Nat.ble al.baseAddr a && Nat.blt a (al.baseAddr + al.size) then
        if memNat al.allocId h.exposed then some al.allocId else none
      else
        go rest
  go h.allocs

/-- Check if `target` has an active protector in `protectors`. -/
def hasActiveProtector (ps : List ActiveProtector) (aid : AllocId) (t : BorTag) : Bool :=
  match ps with
  | [] => false
  | p :: rest =>
    if Nat.beq p.allocId aid && Nat.beq p.tag t then true else hasActiveProtector rest aid t

/-- Retire ONLY the protectors owned by `fid` when MIR frame `fid` returns/unwinds. -/
def releaseFrameProtectors (fid : FrameId) (ps : List ActiveProtector) : List ActiveProtector :=
  match ps with
  | [] => []
  | p :: rest =>
    if Nat.beq p.frameId fid then releaseFrameProtectors fid rest
    else p :: releaseFrameProtectors fid rest

/-- Deallocation domain check mirroring `Miri/Memory/MemoryState.lean:1127-1134`. -/
inductive DeallocReq where
  | rustGlobalDealloc (size : Nat) (align : Nat)
  | cFree

inductive DeallocOutcome where
  | ok
  | ubDangling
  | ubDoubleFree
  | ubMemoryKindMismatch
  | ubLayoutMismatch

private def findDealloc (aid : AllocId) (req : DeallocReq) : List SharedAlloc → DeallocOutcome
  | [] => .ubDangling
  | al :: rest =>
    if Nat.beq al.allocId aid then
      if !al.live then .ubDoubleFree
      else
        match al.domain, req with
        | .rustGlobal sz aln, .rustGlobalDealloc rsz raln =>
          if Nat.beq sz rsz && Nat.beq aln raln then .ok else .ubLayoutMismatch
        | .foreignC _, .cFree => .ok
        | _, _ => .ubMemoryKindMismatch
    else findDealloc aid req rest

def checkDealloc (h : MixedHeap) (ptr : PtrVal) (req : DeallocReq) : DeallocOutcome :=
  match req, ptr.addr, ptr.prov with
  | .cFree, 0, _ => .ok  -- C `free(NULL)` is a legal no-op (`ForeignItems.lean:231`)
  | _, _, .none => .ubDangling
  | _, _, .concrete aid _ => findDealloc aid req h.allocs
  | _, a, .wildcard =>
    match resolveWildcardAddr h a with
    | none => .ubDangling
    | some aid => findDealloc aid req h.allocs

/-! ### Part A Theorems: Impossibility of Single-Frame Big-Step Bridge & Reentrancy Soundness -/

/-- A single-step big-step bridge maps an entry MIR state + ISA kernel directly to
an exit MIR state without inspecting or dispatching arbitrary Rust callback bodies. -/
structure BigStepBridge (MirState IsaProg : Type) where
  runIsa : IsaProg → MirState → MirState

theorem big_step_bridge_blind_to_callback_semantics
    {MirState IsaProg CallbackSem : Type}
    (bridge : BigStepBridge MirState IsaProg)
    (isaProg : IsaProg) (s0 : MirState)
    (cb1 cb2 : CallbackSem)
    (evalWithCb : CallbackSem → MirState → MirState)
    (h_distinct : evalWithCb cb1 s0 ≠ evalWithCb cb2 s0) :
    bridge.runIsa isaProg s0 ≠ evalWithCb cb1 s0 ∨
    bridge.runIsa isaProg s0 ≠ evalWithCb cb2 s0 := by
  by_cases h1 : bridge.runIsa isaProg s0 = evalWithCb cb1 s0
  · right
    intro h2
    exact h_distinct (h1.symm.trans h2)
  · left
    exact h1

/-- Theorem A1: Nested reentrant stack `Rust₀ (frame 1) → ISA₁ (frame 2) → Rust₂ (frame 3)`
preserves `Rust₀`'s `FnEntry` protector when `Rust₂` exits and releases only frame 3's
protectors. -/
theorem reentrant_stack_preserves_outer_protector
    (aidOuter aidInner : AllocId) (tagOuter tagInner : BorTag) :
    let ps : List ActiveProtector := [
      ⟨3, aidInner, tagInner⟩,
      ⟨1, aidOuter, tagOuter⟩
    ]
    hasActiveProtector (releaseFrameProtectors 3 ps) aidOuter tagOuter = true ∧
    (aidOuter ≠ aidInner ∨ tagOuter ≠ tagInner →
      hasActiveProtector (releaseFrameProtectors 3 ps) aidInner tagInner = false) := by
  refine ⟨?_, ?_⟩
  · simp [releaseFrameProtectors, hasActiveProtector]
  · intro hne
    simp [releaseFrameProtectors, hasActiveProtector]
    intro ha ht
    cases hne with
    | inl h => exact h ha
    | inr h => exact h ht

/-- Theorem A2: Reentrant callback writing through a child `user_data` pointer
derived from outer `&mut T` (`ReservedFrz false`, protected, accessed) is a `LocalAccess`
write that validly activates `ReservedFrz false → Unique`. -/
theorem reentrant_callback_child_write_activates_outer :
    tbStep .write .local_ (.reservedFrz false) true true = .ok .unique := rfl

/-- Theorem A3: Reentrant callback writing through a sibling/global pointer while outer
`&mut T` (`ReservedFrz false`, protected, accessed) is still on the stack is immediate UB. -/
theorem reentrant_callback_sibling_write_triggers_outer_protector_ub :
    tbStep .write .foreign (.reservedFrz false) true true = .ub := rfl

/-- Theorem A4: Reentrant callback reading through a sibling/global pointer conflicts an
unactivated outer `&mut T` (`ReservedFrz false → ReservedFrz true`), so a subsequent
outer write before `outer` returns triggers immediate Tree Borrows UB. -/
theorem reentrant_callback_foreign_read_then_outer_write_ub :
    tbStep .read .foreign (.reservedFrz false) true true = .ok (.reservedFrz true) ∧
    tbStep .write .local_ (.reservedFrz true) true true = .ub :=
  ⟨rfl, rfl⟩

/-- Theorem A5 (Local-State Encapsulation / Stack Scanning Defense):
If a Rust stack-local allocation `aid` at `[base, base + size)` is NOT in `h.exposed`,
no guessed integer address `a` inside `[base, base + size)` can resolve to `some aid`
via wildcard provenance—preventing foreign assembly from forging pointers to private
Rust locals via `sp` arithmetic. -/
theorem unexposed_stack_local_guess_is_ub
    (base size a : Addr) (fid : FrameId) (aid : AllocId) :
    let h : MixedHeap := {
      allocs := [⟨aid, base, size, .rustStack fid, true, []⟩]
      exposed := []
      protectors := []
    }
    resolveWildcardAddr h a = none := by
  simp [resolveWildcardAddr, resolveWildcardAddr.go, memNat]

/-- Theorem A6: Cross-allocator deallocation (`RustGlobal` freed by C `free`, or `ForeignC`
freed by `__rust_dealloc`) fails closed with `ubMemoryKindMismatch`, and `malloc(0)`
(live 0-byte `foreignC` alloc) is distinct from Rust `NonNull::dangling()` (`prov = none`). -/
theorem cross_allocator_and_malloc_zero_laws :
    let h : MixedHeap := {
      allocs := [
        ⟨1, 0x1000, 8, .rustGlobal 8 8, true, []⟩,
        ⟨2, 0x2000, 0, .foreignC 0, true, []⟩
      ]
      exposed := []
      protectors := []
    }
    checkDealloc h ⟨0x1000, .concrete 1 1⟩ .cFree = .ubMemoryKindMismatch ∧
    checkDealloc h ⟨0x2000, .concrete 2 2⟩ (.rustGlobalDealloc 0 1) = .ubMemoryKindMismatch ∧
    checkDealloc h ⟨0x2000, .concrete 2 2⟩ .cFree = .ok ∧
    checkDealloc h ⟨8, .none⟩ .cFree = .ubDangling ∧
    checkDealloc h ⟨0, .none⟩ .cFree = .ok :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem A7: Unwinding across `"C"` vs. `"C-unwind"` boundaries. -/
theorem ffi_unwind_abi_laws :
    evalUnwindBoundary .nonUnwindingC .foreignException = .ub ∧
    evalUnwindBoundary .nonUnwindingC .rustPanic = .deterministicAbort ∧
    evalUnwindBoundary .unwindingC .foreignException = .propagateUnwind ∧
    evalUnwindBoundary .unwindingC .rustPanic = .propagateUnwind :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Part B: Generic Trace-Bearing LTS, Parameterized Leaf Oracle & Negative Canary -/

/-- Fault classification matching `Trusted.MirSemantics.FaultKind` and `RefOutcome`. -/
inductive Fault where
  | ub
  | unsupported

/-- Trace-bearing small-step outcome for a machine interacting with external events. -/
inductive StepOut (State Event Val : Type) where
  | tau (next : State)
  | ext (ev : Event) (next : State)
  | done (v : Val)
  | fault (f : Fault)

/-- Trace-accumulating multi-step reachability over a trace-bearing step function. -/
inductive TraceReaches {S E V : Type} (step : S → StepOut S E V) :
    S → List E → S → Prop where
  | refl (s : S) : TraceReaches step s [] s
  | tau {s1 s2 s3 : S} {tr : List E} :
      step s1 = .tau s2 →
      TraceReaches step s2 tr s3 →
      TraceReaches step s1 tr s3
  | ext {s1 s2 s3 : S} {ev : E} {tr : List E} :
      step s1 = .ext ev s2 →
      TraceReaches step s2 tr s3 →
      TraceReaches step s1 (ev :: tr) s3

def BehaviorTrace {S E V : Type} (step : S → StepOut S E V)
    (s0 : S) (tr : List E) (v : V) : Prop :=
  ∃ sf, TraceReaches step s0 tr sf ∧ step sf = .done v

def FaultTrace {S E V : Type} (step : S → StepOut S E V)
    (s0 : S) (tr : List E) (f : Fault) : Prop :=
  ∃ sf, TraceReaches step s0 tr sf ∧ step sf = .fault f

def DivergesTrace {S E V : Type} (step : S → StepOut S E V)
    (s0 : S) (evs : Nat → Option E) : Prop :=
  ∃ run : Nat → S, run 0 = s0 ∧
    ∀ n,
      (evs n = none ∧ step (run n) = .tau (run (n + 1))) ∨
      (∃ e, evs n = some e ∧ step (run n) = .ext e (run (n + 1)))

/-- Generic lockstep bisimulation over any two trace-bearing deterministic step functions. -/
structure StepBisim {S1 S2 E V : Type}
    (step1 : S1 → StepOut S1 E V)
    (step2 : S2 → StepOut S2 E V)
    (Rel : S1 → S2 → Prop) : Prop where
  tau_fwd : ∀ s1 s2 s1', Rel s1 s2 → step1 s1 = .tau s1' →
    ∃ s2', step2 s2 = .tau s2' ∧ Rel s1' s2'
  tau_rev : ∀ s1 s2 s2', Rel s1 s2 → step2 s2 = .tau s2' →
    ∃ s1', step1 s1 = .tau s1' ∧ Rel s1' s2'
  ext_fwd : ∀ s1 s2 ev s1', Rel s1 s2 → step1 s1 = .ext ev s1' →
    ∃ s2', step2 s2 = .ext ev s2' ∧ Rel s1' s2'
  ext_rev : ∀ s1 s2 ev s2', Rel s1 s2 → step2 s2 = .ext ev s2' →
    ∃ s1', step1 s1 = .ext ev s1' ∧ Rel s1' s2'
  done_iff : ∀ s1 s2 v, Rel s1 s2 → (step1 s1 = .done v ↔ step2 s2 = .done v)
  fault_iff : ∀ s1 s2 f, Rel s1 s2 → (step1 s1 = .fault f ↔ step2 s2 = .fault f)

theorem stepBisim_symm {S1 S2 E V : Type}
    {step1 : S1 → StepOut S1 E V} {step2 : S2 → StepOut S2 E V}
    {Rel : S1 → S2 → Prop}
    (h : StepBisim step1 step2 Rel) :
    StepBisim step2 step1 (fun s2 s1 => Rel s1 s2) where
  tau_fwd := fun _ _ _ hr hs => h.tau_rev _ _ _ hr hs
  tau_rev := fun _ _ _ hr hs => h.tau_fwd _ _ _ hr hs
  ext_fwd := fun _ _ _ _ hr hs => h.ext_rev _ _ _ _ hr hs
  ext_rev := fun _ _ _ _ hr hs => h.ext_fwd _ _ _ _ hr hs
  done_iff := fun _ _ _ hr => (h.done_iff _ _ _ hr).symm
  fault_iff := fun _ _ _ hr => (h.fault_iff _ _ _ hr).symm

theorem stepBisim_traceReaches_fwd {S1 S2 E V : Type}
    {step1 : S1 → StepOut S1 E V} {step2 : S2 → StepOut S2 E V}
    {Rel : S1 → S2 → Prop}
    (h : StepBisim step1 step2 Rel)
    {s1 s1' : S1} {tr : List E}
    (htr : TraceReaches step1 s1 tr s1') :
    ∀ {s2 : S2}, Rel s1 s2 →
      ∃ s2', TraceReaches step2 s2 tr s2' ∧ Rel s1' s2' := by
  induction htr with
  | refl _ =>
    intro s2 hr
    exact ⟨s2, TraceReaches.refl s2, hr⟩
  | tau hst _ ih =>
    intro s2 hr
    rcases h.tau_fwd _ _ _ hr hst with ⟨s2', hst2, hr'⟩
    rcases ih hr' with ⟨s2'', htr2, hr''⟩
    exact ⟨s2'', TraceReaches.tau hst2 htr2, hr''⟩
  | ext hst _ ih =>
    intro s2 hr
    rcases h.ext_fwd _ _ _ _ hr hst with ⟨s2', hst2, hr'⟩
    rcases ih hr' with ⟨s2'', htr2, hr''⟩
    exact ⟨s2'', TraceReaches.ext hst2 htr2, hr''⟩

theorem stepBisim_diverges_fwd {S1 S2 E V : Type}
    {step1 : S1 → StepOut S1 E V} {step2 : S2 → StepOut S2 E V}
    {Rel : S1 → S2 → Prop}
    (h : StepBisim step1 step2 Rel)
    {s1 : S1} {s2 : S2} {evs : Nat → Option E}
    (hr0 : Rel s1 s2)
    (hdiv : DivergesTrace step1 s1 evs) :
    DivergesTrace step2 s2 evs := by
  rcases hdiv with ⟨run1, h0, hsteps⟩
  subst h0
  have hnext : ∀ n (s2n : S2), Rel (run1 n) s2n →
      ∃ s2next, Rel (run1 (n + 1)) s2next ∧
        ((evs n = none ∧ step2 s2n = .tau s2next) ∨
         (∃ e, evs n = some e ∧ step2 s2n = .ext e s2next)) := by
    intro n s2n hrn
    cases hsteps n with
    | inl htau =>
      rcases h.tau_fwd _ _ _ hrn htau.2 with ⟨s2', hst2, hr'⟩
      exact ⟨s2', hr', Or.inl ⟨htau.1, hst2⟩⟩
    | inr hext =>
      rcases hext with ⟨e, hev, hst⟩
      rcases h.ext_fwd _ _ _ _ hrn hst with ⟨s2', hst2, hr'⟩
      exact ⟨s2', hr', Or.inr ⟨e, hev, hst2⟩⟩
  let build : (n : Nat) → { s2n : S2 // Rel (run1 n) s2n } :=
    Nat.rec ⟨s2, hr0⟩ (fun n prev =>
      let ex := hnext n prev.val prev.property
      ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩)
  refine ⟨fun n => (build n).val, rfl, ?_⟩
  intro n
  exact (Classical.choose_spec (hnext n (build n).val (build n).property)).2

/-- Lifting `StepBisim` to full equivalence of `BehaviorTrace`, `FaultTrace`, and `DivergesTrace`. -/
theorem stepBisim_sound {S1 S2 E V : Type}
    {step1 : S1 → StepOut S1 E V} {step2 : S2 → StepOut S2 E V}
    {Rel : S1 → S2 → Prop} {s1_0 : S1} {s2_0 : S2}
    (h : StepBisim step1 step2 Rel) (hr0 : Rel s1_0 s2_0) :
    (∀ tr v, BehaviorTrace step1 s1_0 tr v ↔ BehaviorTrace step2 s2_0 tr v) ∧
    (∀ tr f, FaultTrace step1 s1_0 tr f ↔ FaultTrace step2 s2_0 tr f) ∧
    (∀ evs, DivergesTrace step1 s1_0 evs ↔ DivergesTrace step2 s2_0 evs) := by
  have hsym := stepBisim_symm h
  refine ⟨?_, ?_, ?_⟩
  · intro tr v
    constructor
    · rintro ⟨sf1, htr1, hd1⟩
      rcases stepBisim_traceReaches_fwd h htr1 hr0 with ⟨sf2, htr2, hrf⟩
      exact ⟨sf2, htr2, (h.done_iff _ _ v hrf).mp hd1⟩
    · rintro ⟨sf2, htr2, hd2⟩
      rcases stepBisim_traceReaches_fwd hsym htr2 hr0 with ⟨sf1, htr1, hrf⟩
      exact ⟨sf1, htr1, (h.done_iff _ _ v hrf).mpr hd2⟩
  · intro tr f
    constructor
    · rintro ⟨sf1, htr1, hf1⟩
      rcases stepBisim_traceReaches_fwd h htr1 hr0 with ⟨sf2, htr2, hrf⟩
      exact ⟨sf2, htr2, (h.fault_iff _ _ f hrf).mp hf1⟩
    · rintro ⟨sf2, htr2, hf2⟩
      rcases stepBisim_traceReaches_fwd hsym htr2 hr0 with ⟨sf1, htr1, hrf⟩
      exact ⟨sf1, htr1, (h.fault_iff _ _ f hrf).mpr hf2⟩
  · intro evs
    exact ⟨stepBisim_diverges_fwd h hr0, stepBisim_diverges_fwd hsym hr0⟩

/-- An atomic external call / inline-assembly oracle `O`. -/
structure ExternalOracle (ExtQuery ExtReply ExtEvent SharedMem : Type) where
  exec : ExtQuery → SharedMem → StepOut (ExtReply × SharedMem) ExtEvent Empty

/-- An open MIR semantics parameterized by a leaf external oracle `O`. -/
structure OpenMirMachine (State SharedMem ExtQuery ExtReply Val : Type) where
  init : State
  isExternal : State → Option (ExtQuery × SharedMem × (ExtReply × SharedMem → State))
  stepInternal : State → StepOut State Empty Val

def closedStep {S M Q R E V : Type}
    (mach : OpenMirMachine S M Q R V)
    (oracle : ExternalOracle Q R E M)
    (s : S) : StepOut S E V :=
  match mach.isExternal s with
  | some (q, m, resume) =>
    match oracle.exec q m with
    | .tau rm => .tau (resume rm)
    | .ext ev rm => .ext ev (resume rm)
    | .done empty => nomatch empty
    | .fault f => .fault f
  | none =>
    match mach.stepInternal s with
    | .tau s' => .tau s'
    | .ext empty _ => nomatch empty
    | .done v => .done v
    | .fault f => .fault f

structure OpenMirSim {SA SR M Q R V : Type}
    (mA : OpenMirMachine SA M Q R V)
    (mR : OpenMirMachine SR M Q R V)
    (Rel : SA → SR → Prop) : Prop where
  init_rel : Rel mA.init mR.init
  ext_match : ∀ sa sr, Rel sa sr →
    (mA.isExternal sa = none ∧ mR.isExternal sr = none) ∨
    (∃ q m resA resR,
      mA.isExternal sa = some (q, m, resA) ∧
      mR.isExternal sr = some (q, m, resR) ∧
      ∀ rm, Rel (resA rm) (resR rm))
  internal_match : ∀ sa sr, Rel sa sr →
    mA.isExternal sa = none →
    (∀ sa', mA.stepInternal sa = .tau sa' →
      ∃ sr', mR.stepInternal sr = .tau sr' ∧ Rel sa' sr') ∧
    (∀ sr', mR.stepInternal sr = .tau sr' →
      ∃ sa', mA.stepInternal sa = .tau sa' ∧ Rel sa' sr') ∧
    (∀ v, mA.stepInternal sa = .done v ↔ mR.stepInternal sr = .done v) ∧
    (∀ f, mA.stepInternal sa = .fault f ↔ mR.stepInternal sr = .fault f)

def OracleEquiv {Q R E M : Type}
    (o1 o2 : ExternalOracle Q R E M) : Prop :=
  ∀ q m, o1.exec q m = o2.exec q m

theorem closedStep_bisim {SA SR M Q R E V : Type}
    {mA : OpenMirMachine SA M Q R V}
    {mR : OpenMirMachine SR M Q R V}
    {oA oR : ExternalOracle Q R E M}
    {Rel : SA → SR → Prop}
    (hsim : OpenMirSim mA mR Rel)
    (hor : OracleEquiv oA oR) :
    StepBisim (closedStep mA oA) (closedStep mR oR) Rel where
  tau_fwd := by
    intro sa sr sa' hrel hst
    cases hsim.ext_match sa sr hrel with
    | inl hnone =>
      rcases hnone with ⟨hA, hR⟩
      have hint := hsim.internal_match sa sr hrel hA
      simp only [closedStep, hA] at hst
      cases hs : mA.stepInternal sa with
      | tau s' =>
        simp only [hs] at hst; injection hst with heq; subst heq
        rcases hint.1 s' hs with ⟨sr', hsr', hrel'⟩
        exact ⟨sr', by simp [closedStep, hR, hsr'], hrel'⟩
      | ext e _ => nomatch e
      | done _ => simp only [hs] at hst; cases hst
      | fault _ => simp only [hs] at hst; cases hst
    | inr hext =>
      rcases hext with ⟨q, m, resA, resR, hA, hR, hres⟩
      have ho := hor q m
      simp only [closedStep, hA] at hst
      cases hx : oA.exec q m with
      | tau rm =>
        simp only [hx] at hst; injection hst with heq; subst heq
        exact ⟨resR rm, by simp [closedStep, hR, ← ho, hx], hres rm⟩
      | ext _ _ => simp only [hx] at hst; cases hst
      | done e => nomatch e
      | fault _ => simp only [hx] at hst; cases hst
  tau_rev := by
    intro sa sr sr' hrel hst
    cases hsim.ext_match sa sr hrel with
    | inl hnone =>
      rcases hnone with ⟨hA, hR⟩
      have hint := hsim.internal_match sa sr hrel hA
      simp only [closedStep, hR] at hst
      cases hs : mR.stepInternal sr with
      | tau s' =>
        simp only [hs] at hst; injection hst with heq; subst heq
        rcases hint.2.1 s' hs with ⟨sa', hsa', hrel'⟩
        exact ⟨sa', by simp [closedStep, hA, hsa'], hrel'⟩
      | ext e _ => nomatch e
      | done _ => simp only [hs] at hst; cases hst
      | fault _ => simp only [hs] at hst; cases hst
    | inr hext =>
      rcases hext with ⟨q, m, resA, resR, hA, hR, hres⟩
      have ho := hor q m
      simp only [closedStep, hR, ← ho] at hst
      cases hx : oA.exec q m with
      | tau rm =>
        simp only [hx] at hst; injection hst with heq; subst heq
        exact ⟨resA rm, by simp [closedStep, hA, hx], hres rm⟩
      | ext _ _ => simp only [hx] at hst; cases hst
      | done e => nomatch e
      | fault _ => simp only [hx] at hst; cases hst
  ext_fwd := by
    intro sa sr ev sa' hrel hst
    cases hsim.ext_match sa sr hrel with
    | inl hnone =>
      rcases hnone with ⟨hA, _⟩
      simp only [closedStep, hA] at hst
      cases hs : mA.stepInternal sa with
      | tau _ => simp only [hs] at hst; cases hst
      | ext e _ => nomatch e
      | done _ => simp only [hs] at hst; cases hst
      | fault _ => simp only [hs] at hst; cases hst
    | inr hext =>
      rcases hext with ⟨q, m, resA, resR, hA, hR, hres⟩
      have ho := hor q m
      simp only [closedStep, hA] at hst
      cases hx : oA.exec q m with
      | tau _ => simp only [hx] at hst; cases hst
      | ext ev' rm =>
        simp only [hx] at hst; injection hst with h1 h2; subst h1; subst h2
        exact ⟨resR rm, by simp [closedStep, hR, ← ho, hx], hres rm⟩
      | done e => nomatch e
      | fault _ => simp only [hx] at hst; cases hst
  ext_rev := by
    intro sa sr ev sr' hrel hst
    cases hsim.ext_match sa sr hrel with
    | inl hnone =>
      rcases hnone with ⟨_, hR⟩
      simp only [closedStep, hR] at hst
      cases hs : mR.stepInternal sr with
      | tau _ => simp only [hs] at hst; cases hst
      | ext e _ => nomatch e
      | done _ => simp only [hs] at hst; cases hst
      | fault _ => simp only [hs] at hst; cases hst
    | inr hext =>
      rcases hext with ⟨q, m, resA, resR, hA, hR, hres⟩
      have ho := hor q m
      simp only [closedStep, hR, ← ho] at hst
      cases hx : oA.exec q m with
      | tau _ => simp only [hx] at hst; cases hst
      | ext ev' rm =>
        simp only [hx] at hst; injection hst with h1 h2; subst h1; subst h2
        exact ⟨resA rm, by simp [closedStep, hA, hx], hres rm⟩
      | done e => nomatch e
      | fault _ => simp only [hx] at hst; cases hst
  done_iff := by
    intro sa sr v hrel
    cases hsim.ext_match sa sr hrel with
    | inl hnone =>
      rcases hnone with ⟨hA, hR⟩
      have hd := (hsim.internal_match sa sr hrel hA).2.2.1 v
      constructor
      · intro hst
        simp only [closedStep, hA] at hst
        cases hs : mA.stepInternal sa with
        | tau _ => simp only [hs] at hst; cases hst
        | ext e _ => nomatch e
        | done v' =>
          simp only [hs] at hst; injection hst with heq; subst heq
          simp [closedStep, hR, hd.mp hs]
        | fault _ => simp only [hs] at hst; cases hst
      · intro hst
        simp only [closedStep, hR] at hst
        cases hs : mR.stepInternal sr with
        | tau _ => simp only [hs] at hst; cases hst
        | ext e _ => nomatch e
        | done v' =>
          simp only [hs] at hst; injection hst with heq; subst heq
          simp [closedStep, hA, hd.mpr hs]
        | fault _ => simp only [hs] at hst; cases hst
    | inr hext =>
      rcases hext with ⟨q, m, _, _, hA, hR, _⟩
      have ho := hor q m
      simp only [closedStep, hA, hR, ← ho]
      cases oA.exec q m with
      | tau _ => simp
      | ext _ _ => simp
      | done e => nomatch e
      | fault _ => simp
  fault_iff := by
    intro sa sr f hrel
    cases hsim.ext_match sa sr hrel with
    | inl hnone =>
      rcases hnone with ⟨hA, hR⟩
      have hf := (hsim.internal_match sa sr hrel hA).2.2.2 f
      constructor
      · intro hst
        simp only [closedStep, hA] at hst
        cases hs : mA.stepInternal sa with
        | tau _ => simp [hs] at hst
        | ext e _ => nomatch e
        | done _ => simp [hs] at hst
        | fault f' =>
          simp only [hs] at hst; injection hst with heq; subst heq
          simp [closedStep, hR, hf.mp hs]
      · intro hst
        simp only [closedStep, hR] at hst
        cases hs : mR.stepInternal sr with
        | tau _ => simp [hs] at hst
        | ext e _ => nomatch e
        | done _ => simp [hs] at hst
        | fault f' =>
          simp only [hs] at hst; injection hst with heq; subst heq
          simp [closedStep, hA, hf.mpr hs]
    | inr hext =>
      rcases hext with ⟨q, m, _, _, hA, hR, _⟩
      have ho := hor q m
      simp only [closedStep, hA, hR, ← ho]
      cases oA.exec q m with
      | tau _ => simp
      | ext _ _ => simp
      | done e => nomatch e
      | fault _ => simp

/-- Theorem B1 (Two-Oracle Horizontal Pass-2 Composition for Leaf Oracles):
Preserves `BehaviorTrace`, `FaultTrace`, AND `DivergesTrace`. -/
theorem horizontal_two_oracle_composition {SA SR M Q R E V : Type}
    {mA : OpenMirMachine SA M Q R V}
    {mR : OpenMirMachine SR M Q R V}
    {oA oR : ExternalOracle Q R E M}
    {Rel : SA → SR → Prop}
    (hsim : OpenMirSim mA mR Rel)
    (hor : OracleEquiv oA oR) :
    (∀ tr v,
      BehaviorTrace (closedStep mA oA) mA.init tr v ↔
      BehaviorTrace (closedStep mR oR) mR.init tr v) ∧
    (∀ tr f,
      FaultTrace (closedStep mA oA) mA.init tr f ↔
      FaultTrace (closedStep mR oR) mR.init tr f) ∧
    (∀ evs,
      DivergesTrace (closedStep mA oA) mA.init evs ↔
      DivergesTrace (closedStep mR oR) mR.init evs) :=
  stepBisim_sound (closedStep_bisim hsim hor) hsim.init_rel

/-- Corollary B2 (Parameterized Shared External Oracle `O`). -/
theorem parametric_oracle_correspondence {SA SR M Q R E V : Type}
    {mA : OpenMirMachine SA M Q R V}
    {mR : OpenMirMachine SR M Q R V}
    {Rel : SA → SR → Prop}
    (hsim : OpenMirSim mA mR Rel)
    (oracle : ExternalOracle Q R E M) :
    (∀ tr v,
      BehaviorTrace (closedStep mA oracle) mA.init tr v ↔
      BehaviorTrace (closedStep mR oracle) mR.init tr v) ∧
    (∀ tr f,
      FaultTrace (closedStep mA oracle) mA.init tr f ↔
      FaultTrace (closedStep mR oracle) mR.init tr f) ∧
    (∀ evs,
      DivergesTrace (closedStep mA oracle) mA.init evs ↔
      DivergesTrace (closedStep mR oracle) mR.init evs) :=
  horizontal_two_oracle_composition hsim (fun _ _ => rfl)

/-- Theorem B3 (Negative Canary — Closed `TerminalOut` Is Unsound With External Effects). -/
private def stepA : Nat → StepOut Nat Nat Unit
  | 0 => .ext 1 1
  | _ => .done ()

private def stepB : Nat → StepOut Nat Nat Unit
  | 0 => .ext 2 1
  | _ => .done ()

theorem closed_terminal_out_insufficient_for_effectful_ffi :
    (∃ tr, BehaviorTrace stepA 0 tr ()) ∧
    (∃ tr, BehaviorTrace stepB 0 tr ()) ∧
    BehaviorTrace stepA 0 [1] () ∧
    ¬ BehaviorTrace stepB 0 [1] () := by
  refine ⟨⟨[1], 1, TraceReaches.ext rfl (TraceReaches.refl 1), rfl⟩,
          ⟨[2], 1, TraceReaches.ext rfl (TraceReaches.refl 1), rfl⟩,
          ⟨1, TraceReaches.ext rfl (TraceReaches.refl 1), rfl⟩, ?_⟩
  rintro ⟨sf, htr, _⟩
  cases htr with
  | tau h => cases h
  | ext h _ => cases h

/-! ## Part C: Arbitrarily Reentrant Heterogeneous MIR↔ISA Stack Composition (`M ⊕_stack I`) -/

/-- Step outcome of a single open component (either MIR or ISA) communicating over a
CompCertO/CompCertM-style call/return/memory interface `(CallQuery, RetReply, SharedMem)`. -/
inductive OpenCompStep (LocalState SharedMem CallQuery RetReply Event : Type) where
  | internal (s' : LocalState) (m' : SharedMem)
  | extEvent (ev : Event) (s' : LocalState) (m' : SharedMem)
  | callOther (q : CallQuery) (m' : SharedMem) (resume : RetReply × SharedMem → LocalState)
  | ret (r : RetReply) (m' : SharedMem)
  | fault (f : Fault)

/-- An open language component (`MIR` or `ISA`) that can be entered via `enter`, stepped via
`step`, call the other component (`callOther`), return (`ret`), emit events, or fault. -/
structure OpenComponent (LocalState SharedMem CallQuery RetReply Event : Type) where
  enter : CallQuery → SharedMem → Option LocalState
  step : LocalState → SharedMem → OpenCompStep LocalState SharedMem CallQuery RetReply Event

/-- Heterogeneous call-stack frames interleaving MIR and ISA activations to arbitrary depth
(CompCertO `SmallstepLinking.v` / CompCertM `Sem.v` pattern). -/
inductive LinkFrame (SM SI M Q R : Type) where
  | mirActive (s : SM)
  | isaActive (s : SI)
  | mirSuspended (resume : R × M → SM)
  | isaSuspended (resume : R × M → SI)

/-- State of the horizontally linked reentrant machine `M ⊕_stack I`. -/
structure LinkedState (SM SI M Q R : Type) where
  stack : List (LinkFrame SM SI M Q R)
  mem : M

/-- Single small step of the arbitrarily reentrant linked machine `M ⊕_stack I`. -/
def linkStep {SM SI M Q R E : Type}
    (mir : OpenComponent SM M Q R E)
    (isa : OpenComponent SI M Q R E)
    (st : LinkedState SM SI M Q R) :
    StepOut (LinkedState SM SI M Q R) E (R × M) :=
  match st.stack with
  | [] => .fault .ub
  | .mirSuspended _ :: _ => .fault .ub
  | .isaSuspended _ :: _ => .fault .ub
  | .mirActive sm :: rest =>
    match mir.step sm st.mem with
    | .internal sm' m' => .tau ⟨.mirActive sm' :: rest, m'⟩
    | .extEvent ev sm' m' => .ext ev ⟨.mirActive sm' :: rest, m'⟩
    | .callOther q m' res =>
      match isa.enter q m' with
      | some si' => .tau ⟨.isaActive si' :: .mirSuspended res :: rest, m'⟩
      | none => .fault .unsupported
    | .ret r m' =>
      match rest with
      | [] => .done (r, m')
      | .isaSuspended res :: rest' => .tau ⟨.isaActive (res (r, m')) :: rest', m'⟩
      | _ => .fault .ub
    | .fault f => .fault f
  | .isaActive si :: rest =>
    match isa.step si st.mem with
    | .internal si' m' => .tau ⟨.isaActive si' :: rest, m'⟩
    | .extEvent ev si' m' => .ext ev ⟨.isaActive si' :: rest, m'⟩
    | .callOther q m' res =>
      match mir.enter q m' with
      | some sm' => .tau ⟨.mirActive sm' :: .isaSuspended res :: rest, m'⟩
      | none => .fault .unsupported
    | .ret r m' =>
      match rest with
      | [] => .done (r, m')
      | .mirSuspended res :: rest' => .tau ⟨.mirActive (res (r, m')) :: rest', m'⟩
      | _ => .fault .ub
    | .fault f => .fault f

/-- Open component bisimulation invariant (`M_anneal ~ M_ref` or `I_anneal ~ I_ref`)
parameterized over the shared call/return/memory boundary `(Q, R, M)`. -/
structure OpenCompSim {S1 S2 M Q R E : Type}
    (c1 : OpenComponent S1 M Q R E)
    (c2 : OpenComponent S2 M Q R E)
    (Rel : S1 → S2 → Prop) : Prop where
  enter_match : ∀ q m,
    (c1.enter q m = none ∧ c2.enter q m = none) ∨
    (∃ s1 s2, c1.enter q m = some s1 ∧ c2.enter q m = some s2 ∧ Rel s1 s2)
  step_match : ∀ s1 s2 m, Rel s1 s2 →
    (∀ s1' m', c1.step s1 m = .internal s1' m' →
      ∃ s2', c2.step s2 m = .internal s2' m' ∧ Rel s1' s2') ∧
    (∀ s2' m', c2.step s2 m = .internal s2' m' →
      ∃ s1', c1.step s1 m = .internal s1' m' ∧ Rel s1' s2') ∧
    (∀ ev s1' m', c1.step s1 m = .extEvent ev s1' m' →
      ∃ s2', c2.step s2 m = .extEvent ev s2' m' ∧ Rel s1' s2') ∧
    (∀ ev s2' m', c2.step s2 m = .extEvent ev s2' m' →
      ∃ s1', c1.step s1 m = .extEvent ev s1' m' ∧ Rel s1' s2') ∧
    (∀ q m' res1, c1.step s1 m = .callOther q m' res1 →
      ∃ res2, c2.step s2 m = .callOther q m' res2 ∧ ∀ rm, Rel (res1 rm) (res2 rm)) ∧
    (∀ q m' res2, c2.step s2 m = .callOther q m' res2 →
      ∃ res1, c1.step s1 m = .callOther q m' res1 ∧ ∀ rm, Rel (res1 rm) (res2 rm)) ∧
    (∀ r m', c1.step s1 m = .ret r m' ↔ c2.step s2 m = .ret r m') ∧
    (∀ f, c1.step s1 m = .fault f ↔ c2.step s2 m = .fault f)

inductive FrameRel {SMA SMR SIA SIR M Q R : Type}
    (RelM : SMA → SMR → Prop) (RelI : SIA → SIR → Prop) :
    LinkFrame SMA SIA M Q R → LinkFrame SMR SIR M Q R → Prop where
  | mirActive (sa : SMA) (sr : SMR) : RelM sa sr → FrameRel RelM RelI (.mirActive sa) (.mirActive sr)
  | isaActive (ia : SIA) (ir : SIR) : RelI ia ir → FrameRel RelM RelI (.isaActive ia) (.isaActive ir)
  | mirSuspended (resA : R × M → SMA) (resR : R × M → SMR) :
      (∀ rm, RelM (resA rm) (resR rm)) →
      FrameRel RelM RelI (.mirSuspended resA) (.mirSuspended resR)
  | isaSuspended (resA : R × M → SIA) (resR : R × M → SIR) :
      (∀ rm, RelI (resA rm) (resR rm)) →
      FrameRel RelM RelI (.isaSuspended resA) (.isaSuspended resR)

inductive StackRel {SMA SMR SIA SIR M Q R : Type}
    (RelM : SMA → SMR → Prop) (RelI : SIA → SIR → Prop) :
    List (LinkFrame SMA SIA M Q R) → List (LinkFrame SMR SIR M Q R) → Prop where
  | nil : StackRel RelM RelI [] []
  | cons {fA fR restA restR} :
      FrameRel RelM RelI fA fR →
      StackRel RelM RelI restA restR →
      StackRel RelM RelI (fA :: restA) (fR :: restR)

def LinkedRel {SMA SMR SIA SIR M Q R : Type}
    (RelM : SMA → SMR → Prop) (RelI : SIA → SIR → Prop)
    (stA : LinkedState SMA SIA M Q R) (stR : LinkedState SMR SIR M Q R) : Prop :=
  stA.mem = stR.mem ∧ StackRel RelM RelI stA.stack stR.stack

theorem openCompSim_symm {S1 S2 M Q R E : Type}
    {c1 : OpenComponent S1 M Q R E} {c2 : OpenComponent S2 M Q R E}
    {Rel : S1 → S2 → Prop}
    (h : OpenCompSim c1 c2 Rel) :
    OpenCompSim c2 c1 (fun s2 s1 => Rel s1 s2) where
  enter_match := by
    intro q m
    cases h.enter_match q m with
    | inl hn => exact Or.inl ⟨hn.2, hn.1⟩
    | inr hs =>
      rcases hs with ⟨s1, s2, h1, h2, hr⟩
      exact Or.inr ⟨s2, s1, h2, h1, hr⟩
  step_match := by
    intro s2 s1 m hr
    have hs := h.step_match s1 s2 m hr
    exact ⟨hs.2.1, hs.1, hs.2.2.2.1, hs.2.2.1,
           fun q m' res2 hq => by
             rcases hs.2.2.2.2.2.1 q m' res2 hq with ⟨res1, h1, hres⟩
             exact ⟨res1, h1, hres⟩,
           fun q m' res1 hq => by
             rcases hs.2.2.2.2.1 q m' res1 hq with ⟨res2, h2, hres⟩
             exact ⟨res2, h2, hres⟩,
           fun r m' => (hs.2.2.2.2.2.2.1 r m').symm,
           fun f => (hs.2.2.2.2.2.2.2 f).symm⟩

theorem stackRel_symm {SMA SMR SIA SIR M Q R : Type}
    {RelM : SMA → SMR → Prop} {RelI : SIA → SIR → Prop}
    {stkA : List (LinkFrame SMA SIA M Q R)} {stkR : List (LinkFrame SMR SIR M Q R)}
    (h : StackRel RelM RelI stkA stkR) :
    StackRel (fun sr sa => RelM sa sr) (fun ir ia => RelI ia ir) stkR stkA := by
  induction h with
  | nil => exact StackRel.nil
  | cons hf _ ih =>
    apply StackRel.cons _ ih
    cases hf with
    | mirActive sa sr hr => exact FrameRel.mirActive sr sa hr
    | isaActive ia ir hr => exact FrameRel.isaActive ir ia hr
    | mirSuspended resA resR hr => exact FrameRel.mirSuspended resR resA hr
    | isaSuspended resA resR hr => exact FrameRel.isaSuspended resR resA hr

theorem linkedRel_symm {SMA SMR SIA SIR M Q R : Type}
    {RelM : SMA → SMR → Prop} {RelI : SIA → SIR → Prop}
    {stA : LinkedState SMA SIA M Q R} {stR : LinkedState SMR SIR M Q R}
    (h : LinkedRel RelM RelI stA stR) :
    LinkedRel (fun sr sa => RelM sa sr) (fun ir ia => RelI ia ir) stR stA :=
  ⟨h.1.symm, stackRel_symm h.2⟩

/-- One-directional forward step simulation for `linkStep` (symmetric direction follows
immediately by `openCompSim_symm` + `linkedRel_symm`, eliminating duplicate proofs). -/
private theorem linkStep_fwd {SMA SMR SIA SIR M Q R E : Type}
    {mA : OpenComponent SMA M Q R E} {mR : OpenComponent SMR M Q R E}
    {iA : OpenComponent SIA M Q R E} {iR : OpenComponent SIR M Q R E}
    {RelM : SMA → SMR → Prop} {RelI : SIA → SIR → Prop}
    (hm : OpenCompSim mA mR RelM)
    (hi : OpenCompSim iA iR RelI)
    {stA : LinkedState SMA SIA M Q R} {stR : LinkedState SMR SIR M Q R}
    (hrel : LinkedRel RelM RelI stA stR) :
    (∀ stA', linkStep mA iA stA = .tau stA' →
      ∃ stR', linkStep mR iR stR = .tau stR' ∧ LinkedRel RelM RelI stA' stR') ∧
    (∀ ev stA', linkStep mA iA stA = .ext ev stA' →
      ∃ stR', linkStep mR iR stR = .ext ev stR' ∧ LinkedRel RelM RelI stA' stR') ∧
    (∀ v, linkStep mA iA stA = .done v → linkStep mR iR stR = .done v) ∧
    (∀ f, linkStep mA iA stA = .fault f → linkStep mR iR stR = .fault f) := by
  rcases hrel with ⟨hmem, hstk⟩
  cases stA with | mk stkA memA =>
  cases stR with | mk stkR memR =>
  dsimp only at hmem hstk
  subst hmem
  cases hstk with
  | nil =>
    refine ⟨fun _ h => by simp [linkStep] at h,
            fun _ _ h => by simp [linkStep] at h,
            fun _ h => by simp [linkStep] at h,
            fun _ h => by simp [linkStep] at h; simp [linkStep, h]⟩
  | cons hf hrest =>
    cases hf with
    | mirSuspended _ _ _ =>
      refine ⟨fun _ h => by simp [linkStep] at h,
              fun _ _ h => by simp [linkStep] at h,
              fun _ h => by simp [linkStep] at h,
              fun _ h => by simp [linkStep] at h; simp [linkStep, h]⟩
    | isaSuspended _ _ _ =>
      refine ⟨fun _ h => by simp [linkStep] at h,
              fun _ _ h => by simp [linkStep] at h,
              fun _ h => by simp [linkStep] at h,
              fun _ h => by simp [linkStep] at h; simp [linkStep, h]⟩
    | mirActive sa sr hrm =>
      have hstep := hm.step_match sa sr memA hrm
      cases hs : mA.step sa memA with
      | internal sm' m' =>
        rcases hstep.1 sm' m' hs with ⟨sr', hsr', hrm'⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro stA' hst
          simp only [linkStep, hs] at hst; injection hst with heq; subst heq
          exact ⟨⟨.mirActive sr' :: _, m'⟩, by simp [linkStep, hsr'],
            ⟨rfl, StackRel.cons (FrameRel.mirActive sm' sr' hrm') hrest⟩⟩
        · intro _ _ hst; simp [linkStep, hs] at hst
        · intro _ hst; simp [linkStep, hs] at hst
        · intro _ hst; simp [linkStep, hs] at hst
      | extEvent ev' sm' m' =>
        rcases hstep.2.2.1 ev' sm' m' hs with ⟨sr', hsr', hrm'⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro _ hst; simp [linkStep, hs] at hst
        · intro ev stA' hst
          simp only [linkStep, hs] at hst; injection hst with h1 h2; subst h1; subst h2
          exact ⟨⟨.mirActive sr' :: _, m'⟩, by simp [linkStep, hsr'],
            ⟨rfl, StackRel.cons (FrameRel.mirActive sm' sr' hrm') hrest⟩⟩
        · intro _ hst; simp [linkStep, hs] at hst
        · intro _ hst; simp [linkStep, hs] at hst
      | callOther q m' resA =>
        rcases hstep.2.2.2.2.1 q m' resA hs with ⟨resR, hsr', hres⟩
        cases hi.enter_match q m' with
        | inl hnone =>
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro _ hst; simp [linkStep, hs, hnone.1] at hst
          · intro _ _ hst; simp [linkStep, hs, hnone.1] at hst
          · intro _ hst; simp [linkStep, hs, hnone.1] at hst
          · intro f hst
            simp only [linkStep, hs, hnone.1] at hst; injection hst with heq; subst heq
            simp [linkStep, hsr', hnone.2]
        | inr hsome =>
          rcases hsome with ⟨ia', ir', hia', hir', hri'⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro stA' hst
            simp only [linkStep, hs, hia'] at hst; injection hst with heq; subst heq
            exact ⟨⟨.isaActive ir' :: .mirSuspended resR :: _, m'⟩,
              by simp [linkStep, hsr', hir'],
              ⟨rfl, StackRel.cons (FrameRel.isaActive ia' ir' hri')
                (StackRel.cons (FrameRel.mirSuspended resA resR hres) hrest)⟩⟩
          · intro _ _ hst; simp [linkStep, hs, hia'] at hst
          · intro _ hst; simp [linkStep, hs, hia'] at hst
          · intro _ hst; simp [linkStep, hs, hia'] at hst
      | ret r m' =>
        have hsr' := (hstep.2.2.2.2.2.2.1 r m').mp hs
        cases hrest with
        | nil =>
          refine ⟨fun _ h => by simp [linkStep, hs] at h,
                  fun _ _ h => by simp [linkStep, hs] at h,
                  fun v h => by
                    simp only [linkStep, hs] at h; injection h with heq; subst heq
                    simp [linkStep, hsr'],
                  fun _ h => by simp [linkStep, hs] at h⟩
        | cons hf2 hrest2 =>
          cases hf2 with
          | isaSuspended resIA resIR hresI =>
            refine ⟨?_, fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h⟩
            intro stA' hst
            simp only [linkStep, hs] at hst; injection hst with heq; subst heq
            exact ⟨⟨.isaActive (resIR (r, m')) :: _, m'⟩, by simp [linkStep, hsr'],
              ⟨rfl, StackRel.cons (FrameRel.isaActive _ _ (hresI (r, m'))) hrest2⟩⟩
          | mirActive _ _ _ =>
            refine ⟨fun _ h => by simp [linkStep, hs] at h,
                    fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun f h => by
                      simp only [linkStep, hs] at h; injection h with heq; subst heq
                      simp [linkStep, hsr']⟩
          | isaActive _ _ _ =>
            refine ⟨fun _ h => by simp [linkStep, hs] at h,
                    fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun f h => by
                      simp only [linkStep, hs] at h; injection h with heq; subst heq
                      simp [linkStep, hsr']⟩
          | mirSuspended _ _ _ =>
            refine ⟨fun _ h => by simp [linkStep, hs] at h,
                    fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun f h => by
                      simp only [linkStep, hs] at h; injection h with heq; subst heq
                      simp [linkStep, hsr']⟩
      | fault f' =>
        have hsr' := (hstep.2.2.2.2.2.2.2 f').mp hs
        refine ⟨fun _ h => by simp [linkStep, hs] at h,
                fun _ _ h => by simp [linkStep, hs] at h,
                fun _ h => by simp [linkStep, hs] at h,
                fun f h => by
                  simp only [linkStep, hs] at h; injection h with heq; subst heq
                  simp [linkStep, hsr']⟩
    | isaActive ia ir hri =>
      have hstep := hi.step_match ia ir memA hri
      cases hs : iA.step ia memA with
      | internal si' m' =>
        rcases hstep.1 si' m' hs with ⟨ir', hir', hri'⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro stA' hst
          simp only [linkStep, hs] at hst; injection hst with heq; subst heq
          exact ⟨⟨.isaActive ir' :: _, m'⟩, by simp [linkStep, hir'],
            ⟨rfl, StackRel.cons (FrameRel.isaActive si' ir' hri') hrest⟩⟩
        · intro _ _ hst; simp [linkStep, hs] at hst
        · intro _ hst; simp [linkStep, hs] at hst
        · intro _ hst; simp [linkStep, hs] at hst
      | extEvent ev' si' m' =>
        rcases hstep.2.2.1 ev' si' m' hs with ⟨ir', hir', hri'⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro _ hst; simp [linkStep, hs] at hst
        · intro ev stA' hst
          simp only [linkStep, hs] at hst; injection hst with h1 h2; subst h1; subst h2
          exact ⟨⟨.isaActive ir' :: _, m'⟩, by simp [linkStep, hir'],
            ⟨rfl, StackRel.cons (FrameRel.isaActive si' ir' hri') hrest⟩⟩
        · intro _ hst; simp [linkStep, hs] at hst
        · intro _ hst; simp [linkStep, hs] at hst
      | callOther q m' resA =>
        rcases hstep.2.2.2.2.1 q m' resA hs with ⟨resR, hir', hres⟩
        cases hm.enter_match q m' with
        | inl hnone =>
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro _ hst; simp [linkStep, hs, hnone.1] at hst
          · intro _ _ hst; simp [linkStep, hs, hnone.1] at hst
          · intro _ hst; simp [linkStep, hs, hnone.1] at hst
          · intro f hst
            simp only [linkStep, hs, hnone.1] at hst; injection hst with heq; subst heq
            simp [linkStep, hir', hnone.2]
        | inr hsome =>
          rcases hsome with ⟨ma', mr', hma', hmr', hrm'⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro stA' hst
            simp only [linkStep, hs, hma'] at hst; injection hst with heq; subst heq
            exact ⟨⟨.mirActive mr' :: .isaSuspended resR :: _, m'⟩,
              by simp [linkStep, hir', hmr'],
              ⟨rfl, StackRel.cons (FrameRel.mirActive ma' mr' hrm')
                (StackRel.cons (FrameRel.isaSuspended resA resR hres) hrest)⟩⟩
          · intro _ _ hst; simp [linkStep, hs, hma'] at hst
          · intro _ hst; simp [linkStep, hs, hma'] at hst
          · intro _ hst; simp [linkStep, hs, hma'] at hst
      | ret r m' =>
        have hir' := (hstep.2.2.2.2.2.2.1 r m').mp hs
        cases hrest with
        | nil =>
          refine ⟨fun _ h => by simp [linkStep, hs] at h,
                  fun _ _ h => by simp [linkStep, hs] at h,
                  fun v h => by
                    simp only [linkStep, hs] at h; injection h with heq; subst heq
                    simp [linkStep, hir'],
                  fun _ h => by simp [linkStep, hs] at h⟩
        | cons hf2 hrest2 =>
          cases hf2 with
          | mirSuspended resMA resMR hresM =>
            refine ⟨?_, fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h⟩
            intro stA' hst
            simp only [linkStep, hs] at hst; injection hst with heq; subst heq
            exact ⟨⟨.mirActive (resMR (r, m')) :: _, m'⟩, by simp [linkStep, hir'],
              ⟨rfl, StackRel.cons (FrameRel.mirActive _ _ (hresM (r, m'))) hrest2⟩⟩
          | mirActive _ _ _ =>
            refine ⟨fun _ h => by simp [linkStep, hs] at h,
                    fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun f h => by
                      simp only [linkStep, hs] at h; injection h with heq; subst heq
                      simp [linkStep, hir']⟩
          | isaActive _ _ _ =>
            refine ⟨fun _ h => by simp [linkStep, hs] at h,
                    fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun f h => by
                      simp only [linkStep, hs] at h; injection h with heq; subst heq
                      simp [linkStep, hir']⟩
          | isaSuspended _ _ _ =>
            refine ⟨fun _ h => by simp [linkStep, hs] at h,
                    fun _ _ h => by simp [linkStep, hs] at h,
                    fun _ h => by simp [linkStep, hs] at h,
                    fun f h => by
                      simp only [linkStep, hs] at h; injection h with heq; subst heq
                      simp [linkStep, hir']⟩
      | fault f' =>
        have hir' := (hstep.2.2.2.2.2.2.2 f').mp hs
        refine ⟨fun _ h => by simp [linkStep, hs] at h,
                fun _ _ h => by simp [linkStep, hs] at h,
                fun _ h => by simp [linkStep, hs] at h,
                fun f h => by
                  simp only [linkStep, hs] at h; injection h with heq; subst heq
                  simp [linkStep, hir']⟩

theorem linkStep_bisim {SMA SMR SIA SIR M Q R E : Type}
    {mA : OpenComponent SMA M Q R E} {mR : OpenComponent SMR M Q R E}
    {iA : OpenComponent SIA M Q R E} {iR : OpenComponent SIR M Q R E}
    {RelM : SMA → SMR → Prop} {RelI : SIA → SIR → Prop}
    (hm : OpenCompSim mA mR RelM)
    (hi : OpenCompSim iA iR RelI) :
    StepBisim (linkStep mA iA) (linkStep mR iR) (LinkedRel RelM RelI) where
  tau_fwd := fun _ _ stA' hr hst => (linkStep_fwd hm hi hr).1 stA' hst
  tau_rev := fun _ _ stR' hr hst => by
    rcases (linkStep_fwd (openCompSim_symm hm) (openCompSim_symm hi) (linkedRel_symm hr)).1 stR' hst
      with ⟨stA', hstA', hrel'⟩
    exact ⟨stA', hstA', linkedRel_symm hrel'⟩
  ext_fwd := fun _ _ ev stA' hr hst => (linkStep_fwd hm hi hr).2.1 ev stA' hst
  ext_rev := fun _ _ ev stR' hr hst => by
    rcases (linkStep_fwd (openCompSim_symm hm) (openCompSim_symm hi) (linkedRel_symm hr)).2.1 ev stR' hst
      with ⟨stA', hstA', hrel'⟩
    exact ⟨stA', hstA', linkedRel_symm hrel'⟩
  done_iff := fun _ _ v hr =>
    ⟨(linkStep_fwd hm hi hr).2.2.1 v,
     (linkStep_fwd (openCompSim_symm hm) (openCompSim_symm hi) (linkedRel_symm hr)).2.2.1 v⟩
  fault_iff := fun _ _ f hr =>
    ⟨(linkStep_fwd hm hi hr).2.2.2 f,
     (linkStep_fwd (openCompSim_symm hm) (openCompSim_symm hi) (linkedRel_symm hr)).2.2.2 f⟩

/-- Theorem C1 (Arbitrarily Reentrant Heterogeneous Stack Horizontal Composition):
Composing open MIR correspondence (`M_anneal ~ M_ref`) and open ISA correspondence
(`I_anneal ~ I_ref`) over a shared call/return/memory boundary yields exact equivalence
of `BehaviorTrace`, `FaultTrace`, and `DivergesTrace` for the arbitrarily reentrant
linked machine `M ⊕_stack I` — with ZERO Iris COFEs and ZERO step-indexing. -/
theorem reentrant_heterogeneous_stack_composition {SMA SMR SIA SIR M Q R E : Type}
    {mA : OpenComponent SMA M Q R E} {mR : OpenComponent SMR M Q R E}
    {iA : OpenComponent SIA M Q R E} {iR : OpenComponent SIR M Q R E}
    {RelM : SMA → SMR → Prop} {RelI : SIA → SIR → Prop}
    {sa0 : SMA} {sr0 : SMR} {m0 : M}
    (hm : OpenCompSim mA mR RelM)
    (hi : OpenCompSim iA iR RelI)
    (hr0 : RelM sa0 sr0) :
    let initA : LinkedState SMA SIA M Q R := ⟨[.mirActive sa0], m0⟩
    let initR : LinkedState SMR SIR M Q R := ⟨[.mirActive sr0], m0⟩
    (∀ tr v, BehaviorTrace (linkStep mA iA) initA tr v ↔
             BehaviorTrace (linkStep mR iR) initR tr v) ∧
    (∀ tr f, FaultTrace (linkStep mA iA) initA tr f ↔
             FaultTrace (linkStep mR iR) initR tr f) ∧
    (∀ evs, DivergesTrace (linkStep mA iA) initA evs ↔
            DivergesTrace (linkStep mR iR) initR evs) :=
  stepBisim_sound (linkStep_bisim hm hi)
    ⟨rfl, StackRel.cons (FrameRel.mirActive sa0 sr0 hr0) StackRel.nil⟩

end ReentrantFfiAndOracleProbe

#print axioms ReentrantFfiAndOracleProbe.big_step_bridge_blind_to_callback_semantics
#print axioms ReentrantFfiAndOracleProbe.reentrant_stack_preserves_outer_protector
#print axioms ReentrantFfiAndOracleProbe.reentrant_callback_child_write_activates_outer
#print axioms ReentrantFfiAndOracleProbe.reentrant_callback_sibling_write_triggers_outer_protector_ub
#print axioms ReentrantFfiAndOracleProbe.reentrant_callback_foreign_read_then_outer_write_ub
#print axioms ReentrantFfiAndOracleProbe.unexposed_stack_local_guess_is_ub
#print axioms ReentrantFfiAndOracleProbe.cross_allocator_and_malloc_zero_laws
#print axioms ReentrantFfiAndOracleProbe.ffi_unwind_abi_laws
#print axioms ReentrantFfiAndOracleProbe.horizontal_two_oracle_composition
#print axioms ReentrantFfiAndOracleProbe.parametric_oracle_correspondence
#print axioms ReentrantFfiAndOracleProbe.closed_terminal_out_insufficient_for_effectful_ffi
#print axioms ReentrantFfiAndOracleProbe.reentrant_heterogeneous_stack_composition
