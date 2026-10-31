-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mid-Level IR Optimization and Lowering Failure Canaries

Standalone, zero-axiom Lean 4 mechanization of the historical IR optimization
and lowering failure classes analyzed in
`anneal-mid-level-ir-optimizations-lowering-verification-failures-2026`,
demonstrating how Anneal's four `trusted/` primitives (`Language`/`BehaviorCodec`/
`Compiles`, `ProductiveOn`/`InhabitedPre`, `SmallStepMachine`/`EventualBehaviorOf`/
`StepResult.externalCall`, and `VerificationResult`) structurally reject each
unsound transformation while accepting its repaired counterpart.
-/

namespace MidLevelIrFailureCanaries

/-! ## 1. Core `trusted/` Primitives (Self-Contained Reference Definitions) -/

structure Partial (α : Type) where
  defined : Prop
  val : defined → α

abbrev Partial.ub {α : Type} : Partial α :=
  { defined := False, val := False.elim }

abbrev Partial.pure {α : Type} (x : α) : Partial α :=
  { defined := True, val := fun _ => x }

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

def Behavior.Refines {Query Out : Type} (b₂ b₁ : Behavior Query Out) : Prop :=
  ∀ q, ∀ h₁ : (b₁ q).defined,
    ∃ h₂ : (b₂ q).defined, ∀ o, (b₂ q).val h₂ o → (b₁ q).val h₁ o

infix:50 " ≤ᵇ " => Behavior.Refines

theorem Behavior.Refines.refl {Query Out : Type} (b : Behavior Query Out) :
    b ≤ᵇ b := by
  intro q h₁
  exact ⟨h₁, fun _ ho => ho⟩

theorem Behavior.Refines.trans {Query Out : Type}
    {b₁ b₂ b₃ : Behavior Query Out} (h₁₂ : b₂ ≤ᵇ b₁) (h₂₃ : b₃ ≤ᵇ b₂) :
    b₃ ≤ᵇ b₁ := by
  intro q h₁
  obtain ⟨h₂, hsub₁₂⟩ := h₁₂ q h₁
  obtain ⟨h₃, hsub₂₃⟩ := h₂₃ q h₂
  exact ⟨h₃, fun o ho₃ => hsub₁₂ o (hsub₂₃ o ho₃)⟩

structure Language (SemObs : Type) where
  Prog : Type
  Query : Type
  Out : Type
  obs : Out → SemObs
  sem : Prog → Behavior Query Out

structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decodeOut_encodeOut : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encodeOut_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

abbrev BehaviorCodec.id {SemObs : Type} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery := fun q => q
  decodeQuery := fun q => q
  decodeQuery_encodeQuery := fun _ => rfl
  encodeOut := fun o => o
  decodeOut := some
  decodeOut_encodeOut := fun _ => rfl
  encodeOut_decodeOut := fun h => (Option.some.inj h).symm
  obs_decodeOut := fun h => congrArg L.obs (Option.some.inj h)

def Compiles {SemObs : Type} (L₁ L₂ : Language SemObs)
    (codec : BehaviorCodec L₁ L₂) (s : L₁.Prog) (t : L₂.Prog) : Prop :=
  ∀ q₁, ∀ h₁ : (L₁.sem s q₁).defined,
    ∃ h₂ : (L₂.sem t (codec.encodeQuery q₁)).defined,
      ∀ o₂, (L₂.sem t (codec.encodeQuery q₁)).val h₂ o₂ →
        ∃ o₁, codec.decodeOut o₂ = some o₁ ∧ (L₁.sem s q₁).val h₁ o₁

def InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

inductive Terminal (Val : Type) where
  | normal (v : Val)
  | panic (msg : Nat)
  | abort
  deriving DecidableEq

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : Terminal Val)
  | diverges
  deriving DecidableEq

def EventualOut.toSemObs {Obs Val : Type} (o : EventualOut Obs Val) :
    EventualOut Obs Unit :=
  match o with
  | .terminated trace (.normal _) => .terminated trace (.normal ())
  | .terminated trace (.panic m) => .terminated trace (.panic m)
  | .terminated trace .abort => .terminated trace .abort
  | .diverges => .diverges

/-! ## 2. Finding 1.1: `LoopUnswitch` Without `freeze` vs. With `freeze` (PLDI 2017) -/

inductive IrVal where
  | bit (b : Bool)
  | poison
  deriving DecidableEq

structure UnswitchQuery where
  tripCountZero : Bool
  condVal : IrVal
  deriving DecidableEq

/-- Source loop: only branches on `condVal` when `tripCountZero = false`. -/
abbrev srcLoopBeh : Behavior UnswitchQuery Bool :=
  fun q =>
    if q.tripCountZero then
      Partial.pure (fun out => out = false)
    else
      match q.condVal with
      | .bit b => Partial.pure (fun out => out = b)
      | .poison => Partial.ub

/-- Buggy unswitched loop: branches on `condVal` unconditionally before checking trip count! -/
abbrev buggyUnswitchedBeh : Behavior UnswitchQuery Bool :=
  fun q =>
    match q.condVal with
    | .bit b =>
      if q.tripCountZero then
        Partial.pure (fun out => out = false)
      else
        Partial.pure (fun out => out = b)
    | .poison => Partial.ub

/-- Repaired unswitched loop: wraps `condVal` in `freeze` before hoisting the branch. -/
abbrev freezeUnswitchedBeh : Behavior UnswitchQuery Bool :=
  fun q =>
    if q.tripCountZero then
      Partial.pure (fun out => out = false)
    else
      match q.condVal with
      | .bit b => Partial.pure (fun out => out = b)
      | .poison => Partial.pure (fun out => out = true ∨ out = false)

abbrev UnswitchLang : Language Unit where
  Prog := Behavior UnswitchQuery Bool
  Query := UnswitchQuery
  Out := Bool
  obs := fun _ => ()
  sem := fun p => p

/-- Canary 1a: Hoisting a potentially-poison branch condition above a 0-trip loop
    without `freeze` violates `Compiles`. -/
theorem loopUnswitch_without_freeze_violates_compiles :
    ¬ Compiles UnswitchLang UnswitchLang (BehaviorCodec.id UnswitchLang)
        srcLoopBeh buggyUnswitchedBeh := by
  intro hComp
  let q₀ : UnswitchQuery := { tripCountZero := true, condVal := .poison }
  have hDef₁ : (srcLoopBeh q₀).defined := trivial
  obtain ⟨hDef₂, _⟩ := hComp q₀ hDef₁
  exact hDef₂

/-- Canary 1b: Wrapping the hoisted condition in `freeze` satisfies `Compiles`. -/
theorem loopUnswitch_with_freeze_satisfies_compiles :
    Compiles UnswitchLang UnswitchLang (BehaviorCodec.id UnswitchLang)
        srcLoopBeh freezeUnswitchedBeh := by
  intro q hDef₁
  cases q with
  | mk trip cond =>
    cases trip
    · cases cond
      · exact ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩
      · exact False.elim hDef₁
    · exact ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩

/-! ## 3. Finding 1.2: `GVN` Pointer-Integer Provenance Substitution (OOPSLA 2018) -/

structure PtrVal where
  allocId : Nat
  offset : Nat
  deriving DecidableEq

structure AdjacentAllocQuery where
  qInitialVal : Nat
  deriving DecidableEq

abbrev derefWriteQ (ptr : PtrVal) : Partial (Nat → Prop) :=
  if ptr.allocId == 2 && ptr.offset == 0 then
    Partial.pure (fun out => out = 10)
  else
    Partial.ub

abbrev pOnePastEnd : PtrVal := { allocId := 1, offset := 1 }
abbrev qBase : PtrVal := { allocId := 2, offset := 0 }

abbrev ProvenanceLang : Language Unit where
  Prog := PtrVal
  Query := AdjacentAllocQuery
  Out := Nat
  obs := fun _ => ()
  sem := fun targetPtr _ => derefWriteQ targetPtr

/-- Canary 2: Replacing `qBase` with `pOnePastEnd` under numeric equality `101 = 101`
    turns a defined write to `q[0]` into out-of-bounds UB and violates `Compiles`. -/
theorem gvn_provenance_substitution_rejected :
    ¬ Compiles ProvenanceLang ProvenanceLang (BehaviorCodec.id ProvenanceLang)
        qBase pOnePastEnd := by
  intro hComp
  obtain ⟨hDef₂, _⟩ := hComp ⟨0⟩ trivial
  exact hDef₂

/-! ## 4. Finding 2.2: Coroutine `StorageLive` Overlap Across `Yield` (`#63616`) -/

structure CoroutineLayout where
  offsetX : Nat
  offsetY : Nat
  deriving DecidableEq

/-- In pre-lowering `L_CoroutineMIR`, `x` (assigned `v₁`) and `y` (assigned `v₂`)
    are both live across `yield` and summed upon resumption (`v₁ + v₂`). -/
abbrev CoroutineSpecLang : Language Unit where
  Prog := Unit
  Query := Nat × Nat
  Out := Nat
  obs := fun _ => ()
  sem := fun _ (v₁, v₂) => Partial.pure (fun out => out = v₁ + v₂)

/-- In lowered `L_MIR`, writing `x` at `offsetX` and `y` at `offsetY` in
    `CoroutineState` clobbers `x` if `offsetX = offsetY`! -/
abbrev CoroutineLoweredLang : Language Unit where
  Prog := CoroutineLayout
  Query := Nat × Nat
  Out := Nat
  obs := fun _ => ()
  sem := fun layout (v₁, v₂) =>
    let savedX := if layout.offsetX = layout.offsetY then v₂ else v₁
    let savedY := v₂
    Partial.pure (fun out => out = savedX + savedY)

abbrev coroutineIdCodec : BehaviorCodec CoroutineSpecLang CoroutineLoweredLang where
  encodeQuery := fun q => q
  decodeQuery := fun q => q
  decodeQuery_encodeQuery := fun _ => rfl
  encodeOut := fun o => o
  decodeOut := some
  decodeOut_encodeOut := fun _ => rfl
  encodeOut_decodeOut := fun h => (Option.some.inj h).symm
  obs_decodeOut := fun _ => rfl

/-- Canary 3: Overlapping two co-live coroutine locals (`offsetX = offsetY = 0`)
    across a yield point violates `Compiles`. -/
theorem coroutine_overlapping_live_fields_rejected :
    ¬ Compiles CoroutineSpecLang CoroutineLoweredLang coroutineIdCodec
        () { offsetX := 0, offsetY := 0 } := by
  intro hComp
  obtain ⟨_, hVal⟩ := hComp (1, 2) trivial
  obtain ⟨o₁, hDec, hEq₁⟩ := hVal 4 rfl
  injection hDec with hO₁
  subst hO₁
  revert hEq₁
  decide

/-! ## 5. Finding 3.1: Tree Borrows Protector DSE Across Diverging External Calls -/

inductive ProtectorKind where
  | weakExitOnly
  | strongImmediate
  deriving DecidableEq

structure ExtCallQuery where
  initialMem : Nat
  extReadsAliasAndDiverges : Bool
  deriving DecidableEq

/-- Source program `foo(x: &mut i32)`: writes `*x = 1`, calls `ext()`, writes `*x = 2`. -/
abbrev dseSourceBeh (pk : ProtectorKind) : Behavior ExtCallQuery (EventualOut Nat Nat) :=
  fun q =>
    if q.extReadsAliasAndDiverges then
      match pk with
      | .weakExitOnly =>
        Partial.pure (fun out => out = .terminated [1] .abort ∨ out = .diverges)
      | .strongImmediate =>
        Partial.ub
    else
      Partial.pure (fun out => out = .terminated [] (.normal 2))

/-- Target program after DSE (`*x = 1` deleted before `ext()`). -/
abbrev dseTargetBeh (pk : ProtectorKind) : Behavior ExtCallQuery (EventualOut Nat Nat) :=
  fun q =>
    if q.extReadsAliasAndDiverges then
      match pk with
      | .weakExitOnly =>
        Partial.pure (fun out => out = .terminated [q.initialMem] .abort)
      | .strongImmediate =>
        Partial.ub
    else
      Partial.pure (fun out => out = .terminated [] (.normal 2))

abbrev ProtectorLang : Language (EventualOut Nat Unit) where
  Prog := Behavior ExtCallQuery (EventualOut Nat Nat)
  Query := ExtCallQuery
  Out := EventualOut Nat Nat
  obs := EventualOut.toSemObs
  sem := fun p => p

/-- Canary 4a: Under a weak (exit-only) or unactivated protector, eliminating
    `*x = 1` before a diverging/aborting external call violates `Compiles`. -/
theorem dse_across_diverging_call_unsound_under_weak_or_unactivated_protector :
    ¬ Compiles ProtectorLang ProtectorLang (BehaviorCodec.id ProtectorLang)
        (dseSourceBeh .weakExitOnly) (dseTargetBeh .weakExitOnly) := by
  intro hComp
  let q₀ : ExtCallQuery := { initialMem := 0, extReadsAliasAndDiverges := true }
  obtain ⟨_, hVal⟩ := hComp q₀ trivial
  obtain ⟨o₁, hDec, hEq₁⟩ := hVal (.terminated [0] .abort) rfl
  injection hDec with hO₁
  subst hO₁
  rcases hEq₁ with h | h <;> nomatch h

/-- Canary 4b: Under a strong active function-entry protector, eliminating
    `*x = 1` before `ext()` satisfies `Compiles` even when `ext()` diverges. -/
theorem dse_across_diverging_call_sound_under_strong_active_protector :
    Compiles ProtectorLang ProtectorLang (BehaviorCodec.id ProtectorLang)
        (dseSourceBeh .strongImmediate) (dseTargetBeh .strongImmediate) := by
  intro q hDef₁
  cases q with
  | mk initMem div =>
    cases div
    · exact ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩
    · exact False.elim hDef₁

/-! ## 6. Finding 4.1 & 4.2: Infinite-Loop Deletion (`#28728`) and `LICM` Trap Hoisting -/

abbrev LoopLang : Language (EventualOut Unit Unit) where
  Prog := Behavior Nat (EventualOut Unit Nat)
  Query := Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSemObs
  sem := fun p => p

abbrev rustInfiniteLoopProg : Behavior Nat (EventualOut Unit Nat) :=
  fun _ => Partial.pure (fun out => out = .diverges)

abbrev llvmDeletedLoopProg : Behavior Nat (EventualOut Unit Nat) :=
  fun _ => Partial.pure (fun out => out = .terminated [] (.normal 42))

/-- Canary 5a (`rust-lang/rust#28728`): Deleting a side-effect-free infinite
    `loop {}` and falling through to return `42` violates `Compiles`. -/
theorem infinite_loop_deletion_violates_compiles :
    ¬ Compiles LoopLang LoopLang (BehaviorCodec.id LoopLang)
        rustInfiniteLoopProg llvmDeletedLoopProg := by
  intro hComp
  obtain ⟨_, hVal⟩ := hComp 0 trivial
  obtain ⟨o₁, hDec, hEq₁⟩ := hVal (.terminated [] (.normal 42)) rfl
  injection hDec with hO₁
  subst hO₁
  revert hEq₁
  decide

/-- Source loop with a trapping/panicking division `100 / d` inside a loop that
    takes 0 iterations when `d = 0`. -/
abbrev licmSourceLoop : Behavior Nat (EventualOut Unit Nat) :=
  fun d =>
    if d = 0 then
      Partial.pure (fun out => out = .terminated [] (.normal 0))
    else
      Partial.pure (fun out => out = .terminated [] (.normal (100 / d)))

/-- Buggy `LICM` target: hoists `100 / d` unconditionally into the preheader,
    panicking when `d = 0`! -/
abbrev licmBuggyPreheaderHoist : Behavior Nat (EventualOut Unit Nat) :=
  fun d =>
    if d = 0 then
      Partial.pure (fun out => out = .terminated [] (.panic 1))
    else
      Partial.pure (fun out => out = .terminated [] (.normal (100 / d)))

/-- Canary 5b: Hoisting a panicking/trapping division into the preheader of a
    potentially 0-trip loop violates `Compiles`. -/
theorem licm_hoisting_trapping_div_above_zero_trip_or_diverging_loop_rejected :
    ¬ Compiles LoopLang LoopLang (BehaviorCodec.id LoopLang)
        licmSourceLoop licmBuggyPreheaderHoist := by
  intro hComp
  obtain ⟨_, hVal⟩ := hComp 0 trivial
  obtain ⟨o₁, hDec, hEq₁⟩ := hVal (.terminated [] (.panic 1)) rfl
  injection hDec with hO₁
  subst hO₁
  nomatch hEq₁

/-! ## 7. Finding 5.1: Briggs/Boissinot `Swap` Bug in Out-of-SSA Lowering -/

abbrev SwapLang : Language Unit where
  Prog := (Nat × Nat) → (Nat × Nat)
  Query := Nat × Nat
  Out := Nat × Nat
  obs := fun _ => ()
  sem := fun f q => Partial.pure (fun out => out = f q)

/-- Parallel SSA block-argument transfer `Goto(hdr, [b, a])`. -/
abbrev parallelSwap (q : Nat × Nat) : Nat × Nat :=
  (q.2, q.1)

/-- Naive sequential lowering `a := b; b := a` (clobbers `a` before reading it!). -/
abbrev naiveSequentialSwap (q : Nat × Nat) : Nat × Nat :=
  let a' := q.2
  let b' := a'
  (a', b')

/-- Scratch-temporary sequential lowering `tmp := a; a := b; b := tmp`. -/
abbrev tempSequentialSwap (q : Nat × Nat) : Nat × Nat :=
  let tmp := q.1
  let a' := q.2
  let b' := tmp
  (a', b')

/-- Canary 6a: Naive SSA swap lowering `a := b; b := a` violates `Compiles`. -/
theorem naive_ssa_swap_lowering_violates_compiles :
    ¬ Compiles SwapLang SwapLang (BehaviorCodec.id SwapLang)
        parallelSwap naiveSequentialSwap := by
  intro hComp
  obtain ⟨_, hVal⟩ := hComp (10, 20) trivial
  obtain ⟨o₁, hDec, hEq₁⟩ := hVal (20, 20) rfl
  injection hDec with hO₁
  subst hO₁
  revert hEq₁
  decide

/-- Canary 6b: Cycle-breaking scratch-temporary swap lowering satisfies `Compiles`. -/
theorem temp_ssa_swap_lowering_satisfies_compiles :
    Compiles SwapLang SwapLang (BehaviorCodec.id SwapLang)
        parallelSwap tempSequentialSwap := by
  intro q _
  exact ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩

/-! ## 8. Finding 5.2 & 5.3: Tail-Call Stack Escape and `ElaborateDrops` Double-Free -/

abbrev TailCallLang : Language Unit where
  Prog := Bool -- `false` = normal call (frame live), `true` = TCO (frame deallocated)
  Query := Nat
  Out := Nat
  obs := fun _ => ()
  sem := fun isTailCall localVal =>
    if isTailCall then
      Partial.ub
    else
      Partial.pure (fun out => out = localVal)

/-- Canary 7a: Tail-call elimination when a reference to a caller stack local
    escapes to the callee triggers `StorageDead` UB and violates `Compiles`. -/
theorem tail_call_with_escaping_stack_ref_violates_compiles :
    ¬ Compiles TailCallLang TailCallLang (BehaviorCodec.id TailCallLang)
        false true := by
  intro hComp
  obtain ⟨hDef₂, _⟩ := hComp 99 trivial
  exact hDef₂

abbrev DropElabLang : Language Unit where
  Prog := Bool -- `false` = clear drop_flag BEFORE drop, `true` = clear AFTER drop
  Query := Bool -- `true` = destructor panics during first drop and unwinds to landing pad
  Out := EventualOut Unit Unit
  obs := fun _ => ()
  sem := fun clearAfterDrop dropPanics =>
    if dropPanics then
      if clearAfterDrop then
        Partial.ub
      else
        Partial.pure (fun out => out = .terminated [] (.panic 1))
    else
      Partial.pure (fun out => out = .terminated [] (.normal ()))

/-- Canary 7b: Clearing `drop_flag` after `drop_in_place` instead of before
    causes a double-drop on unwind when the destructor panics, violating `Compiles`. -/
theorem drop_elaboration_clear_after_drop_double_frees_on_unwind :
    ¬ Compiles DropElabLang DropElabLang (BehaviorCodec.id DropElabLang)
        false true := by
  intro hComp
  obtain ⟨hDef₂, _⟩ := hComp true trivial
  exact hDef₂

/-! ## 9. Finding 6.3: `C2Rust` Signed-Overflow Vacuity and `(NULL, 0)` Slice UB -/

/-- C function with signed overflow UB at `q = 2147483647` (`INT32_MAX`). -/
abbrev cSignedOverflowProg : Behavior Nat Nat :=
  fun q =>
    if q = 2147483647 then
      Partial.ub
    else
      Partial.pure (fun out => out = q + 1)

abbrev CLang : Language Unit where
  Prog := Behavior Nat Nat
  Query := Nat
  Out := Nat
  obs := fun _ => ()
  sem := fun p => p

/-- Canary 8a: `ProductiveOn` blocks vacuous C-to-Rust compilation proofs on
    preconditions where the C source exhibits signed-overflow UB. -/
theorem c2rust_vacuous_c_ub_blocked_by_productiveOn :
    ¬ CLang.ProductiveOn (fun q => q = 2147483647) cSignedOverflowProg := by
  intro hProd
  obtain ⟨hDef, _⟩ := hProd 2147483647 rfl
  exact hDef

structure SliceQuery where
  ptrAddr : Nat
  len : Nat
  deriving DecidableEq

/-- In C, looping `0..len` over `(ptrAddr = 0, len = 0)` without dereferencing
    `ptrAddr` is well-defined and returns `0`. -/
abbrev cEmptyBufferLoop : Behavior SliceQuery Nat :=
  fun q =>
    if q.len = 0 then
      Partial.pure (fun out => out = 0)
    else if q.ptrAddr = 0 then
      Partial.ub
    else
      Partial.pure (fun out => out = q.len)

/-- In Rust, constructing `&[u8]` via `slice::from_raw_parts(ptr, len)` requires
    `ptrAddr != 0` even when `len = 0`! -/
abbrev rustSliceFromRawPartsLoop : Behavior SliceQuery Nat :=
  fun q =>
    if q.ptrAddr = 0 then
      Partial.ub
    else
      Partial.pure (fun out => out = q.len)

abbrev SliceLang : Language Unit where
  Prog := Behavior SliceQuery Nat
  Query := SliceQuery
  Out := Nat
  obs := fun _ => ()
  sem := fun p => p

/-- Canary 8b: Translating a C `(ptr, len)` parameter unconditionally into a Rust
    slice `slice::from_raw_parts(ptr, len)` violates `Compiles` at `(NULL, 0)`. -/
theorem c2rust_null_zero_len_slice_violates_compiles :
    ¬ Compiles SliceLang SliceLang (BehaviorCodec.id SliceLang)
        cEmptyBufferLoop rustSliceFromRawPartsLoop := by
  intro hComp
  let qNullZero : SliceQuery := { ptrAddr := 0, len := 0 }
  obtain ⟨hDef₂, _⟩ := hComp qNullZero trivial
  exact hDef₂

end MidLevelIrFailureCanaries
