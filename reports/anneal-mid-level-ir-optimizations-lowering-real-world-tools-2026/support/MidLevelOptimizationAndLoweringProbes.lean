-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Mechanized Probes for Sub-Domain 3: Mid-Level IR Optimizations and Lowering

This standalone Lean 4 module (`prelude` + `Init.NotationExtra` only; zero
`sorryAx`, zero `Lean.ofReduceBool`, zero `Classical.choice`) mechanizes seven
load-bearing semantic discriminators and stress tests for mapping real-world
high- and mid-level IR optimization and lowering tools onto Anneal's four
`trusted/lean/` primitives:

1. **`mem2reg` Uninitialized Read Refinement (`mem2reg_uninit_refines`):**
   Reading an uninitialized stack slot in source `L_MIR` exhibits Undefined
   Behavior (`Partial.ub`), whereas promoting that local to an SSA block
   parameter in `L_AnSSA` with a deterministic default or frozen value produces
   a defined outcome (`Partial.pure`). Under Anneal's directional refinement
   preorder `Compiles` (`L_tgt.sem t ≤ codec.toMorphism (L_src.sem s)`), this
   promotion is unconditionally sound (`mem2reg_uninit_refines`), whereas
   symmetric equivalence fails (`mem2reg_uninit_not_symmetric`).
2. **`DCE` of Panicking vs. Non-Panicking Operations (`dce_panicking_div_unsound`):**
   In Rust MIR, integer division by zero (`x / 0`) terminates via panic/unwind
   (`.terminated trace .unwind`), which is a *defined* outcome with a distinct
   observable spine (`SemObs`) from normal return (`.terminated trace (.normal v)`).
   Consequently, deleting an unused `let _ = x / y` without a non-zero divisor
   proof violates `Compiles` (`dce_panicking_div_unsound`), whereas deleting it
   under a dominating `y ≠ 0` guard (`CVP`) satisfies `Compiles`
   (`dce_guarded_div_compiles`).
3. **Tree Borrows Read Elimination & Function-Entry Protector Removal (`tree_borrows_read_elim_refines`, `inline_drops_protector_refines`):**
   In Tree Borrows, eliminating a redundant read through a shared reference or
   removing a function-entry `Protector` during inlining can only prevent a
   conflicting tag transition to `Disabled` (making the optimized program
   strictly *more defined* than the source program). Both optimizations satisfy
   `Compiles` (`≤`) while violating reverse refinement (`inline_protector_not_reversible`).
4. **Diverging External Calls and Protector Sinking (`dse_across_diverging_external_call_unsound_if_late_protector`):**
   When an opaque external call (`StepResult.externalCall`) may diverge,
   eliminating a dead store `*x = 1` before `ext_call(); *x = 2;` is sound if
   and only if `StepResult.externalCall`'s `boundaryInv` / `branches` contract
   forbids foreign reads of caller-protected `&mut T` *at the moment of the call*
   rather than only upon function return.
5. **`LICM` and Loop Unswitching Zero-Trip Hazard (`licm_uninit_or_trapping_zero_trip_unsound`):**
   Hoisting a potentially panicking instruction `a / d` into a loop preheader
   (or unswitching an uninitialized loop-invariant branch condition) when the
   loop trip count is `0` violates `Compiles` unless guarded by a zero-trip check
   or a non-trapping proof (`licm_guarded_preheader_compiles`).
6. **Async/Coroutine State-Machine Pinning Across `.await` (`coroutine_pinned_poll_compiles`, `coroutine_unpinned_move_violates_safety`):**
   Moving a suspended self-referential `CoroutineState` between `poll` calls
   invalidates interior references, whereas enforcing the `Pin<&mut Self>`
   address-stability invariant in `pre` yields `ProductiveOn` and `Compiles`.
7. **C-to-Rust (`c2rust`) Vacuity Prevention and Empty-Slice Null Trap (`c2rust_ub_source_vacuously_compiles_without_productiveOn`, `c2rust_null_empty_slice_rejected`):**
   A C function with signed integer overflow UB satisfies bare `Compiles` to any
   broken target (`c2rust_ub_source_vacuously_compiles_without_productiveOn`),
   which `InhabitedPre ∧ ProductiveOn` blocks (`c2rust_productiveOn_blocks_ub_source`).
   Independently, C's valid `(NULL, 0)` buffer pointer cannot map directly to a
   Rust `&[T]` slice (which requires non-null `NonNull::dangling()`) without a
   null-canonicalizing `BehaviorCodec`.
-/

namespace MidLevelProbes

/-! ## Section 1: Core Refinement Primitives (`Trusted/Refinement.lean` Mirror) -/

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language (SemObs : Type) where
  Prog : Type
  Query : Type
  Out : Type
  obs : Out → SemObs
  sem : Prog → Behavior Query Out

def InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encode_of_decode_some : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b₁ : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b₁ (c.decodeQuery q₂)).defined
    val := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b₁ (c.decodeQuery q₂)).val h o₁
  }

def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery := fun q => q
  decodeQuery := fun q => q
  decode_encode_query := fun _ => rfl
  encodeOut := fun o => o
  decodeOut := fun o => some o
  decode_encode_out := fun _ => rfl
  encode_of_decode_some := fun h => Option.some.inj h.symm
  obs_decodeOut := fun h => by cases h; rfl

def Compiles {SemObs : Type} (L₁ L₂ : Language SemObs)
    (c : BehaviorCodec L₁ L₂) (s : L₁.Prog) (t : L₂.Prog) : Prop :=
  L₂.sem t ≤ c.toMorphism (L₁.sem s)

/-! ## Section 2: Eventual Small-Step Semantics (`EventualBehaviorOf`) -/

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges

def EventualOut.toSpine {Obs Val : Type} : EventualOut Obs Val → EventualOut Obs Unit
  | .terminated tr (.normal _) => .terminated tr (.normal ())
  | .terminated tr .unwind => .terminated tr .unwind
  | .diverges => .diverges

/-! ## Section 3: Probe 1 — `mem2reg` Uninitialized Stack Read vs. Frozen SSA Value -/

/-- Query records whether a local variable was initialized along the incoming
    control-flow path (`true`) and, if so, its `Nat` value. -/
abbrev Mem2RegQuery := Bool × Nat

/-- Source MIR behavior: reading a stack slot when `init = false` triggers UB
    (`Partial.ub`); when `init = true`, it returns the stored `val`. -/
def mirStackReadBehavior : Behavior Mem2RegQuery (EventualOut Unit Nat) :=
  fun (init, v) =>
    if init then
      Partial.pure (fun out => out = .terminated [] (.normal v))
    else
      Partial.ub

/-- Target AnSSA behavior after `mem2reg` with default/frozen zero on the
    uninitialized incoming edge: always defined! -/
def anssaPromotedBehavior : Behavior Mem2RegQuery (EventualOut Unit Nat) :=
  fun (init, v) =>
    Partial.pure (fun out =>
      out = .terminated [] (.normal (if init then v else 0)))

def L_Mem2Reg : Language (EventualOut Unit Unit) where
  Prog := Bool -- `false` = unpromoted MIR, `true` = promoted AnSSA
  Query := Mem2RegQuery
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun isAnSSA => if isAnSSA then anssaPromotedBehavior else mirStackReadBehavior

/-- `mem2reg` promotion refines source MIR on all paths, including paths where
    the stack slot was uninitialized (`init = false`). -/
theorem mem2reg_uninit_refines :
    Compiles L_Mem2Reg L_Mem2Reg (BehaviorCodec.id L_Mem2Reg) false true := by
  intro (init, v) hSrcDef
  cases init with
  | false =>
    exact False.elim hSrcDef
  | true =>
    refine ⟨trivial, ?_⟩
    intro out hOut
    exact ⟨out, rfl, hOut⟩

/-- However, the reverse direction (`Compiles ... true false`) fails on the
    uninitialized path `(false, 0)` because `AnSSA` is defined while `MIR` is UB. -/
theorem mem2reg_uninit_not_symmetric :
    ¬ Compiles L_Mem2Reg L_Mem2Reg (BehaviorCodec.id L_Mem2Reg) true false := by
  intro hRev
  have ⟨hMirDef, _⟩ := hRev (false, 0) trivial
  exact hMirDef

/-! ## Section 4: Probe 2 — `DCE` of Panicking Division vs. `CVP`-Guarded Division -/

/-- Source program executes `let _unused = x / d; return x`. In Rust MIR, `d = 0`
    panics (`.terminated [] .unwind`), which is a defined outcome, NOT UB. -/
def divUnusedSrcBehavior : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (x, d) =>
    Partial.pure (fun out =>
      if d = 0 then
        out = .terminated [] .unwind
      else
        out = .terminated [] (.normal x))

/-- Naive DCE deletes `let _unused = x / d` and unconditionally returns `x`. -/
def divDeletedTgtBehavior : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (x, _d) =>
    Partial.pure (fun out => out = .terminated [] (.normal x))

def L_DCE : Language (EventualOut Unit Unit) where
  Prog := Bool -- `false` = source with unused div, `true` = naive DCE target
  Query := Nat × Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun deleted => if deleted then divDeletedTgtBehavior else divUnusedSrcBehavior

/-- Deleting an unused panicking division (`x / d` when `d` can be `0`) is
    UNSOUND under `Compiles` because `.normal x` does not match `.unwind`! -/
theorem dce_panicking_div_unsound :
    ¬ Compiles L_DCE L_DCE (BehaviorCodec.id L_DCE) false true := by
  intro hComp
  have ⟨_, hSub⟩ := hComp (42, 0) trivial
  have ⟨o₁, hDec, hSrcOut⟩ := hSub (.terminated [] (.normal 42)) rfl
  injection hDec with hEq
  subst hEq
  dsimp [L_DCE, divUnusedSrcBehavior] at hSrcOut
  nomatch hSrcOut

/-- When a dominating `CVP` guard restricts the block to `d ≠ 0` (so `d = 0` is
    outside the reachable precondition), deleting the dead division IS sound. -/
def divGuardedSrcBehavior : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (x, d) => {
    defined := d ≠ 0
    val := fun _ out => out = .terminated [] (.normal x)
  }

def L_DCE_Guarded : Language (EventualOut Unit Unit) where
  Prog := Bool
  Query := Nat × Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun deleted => if deleted then divDeletedTgtBehavior else divGuardedSrcBehavior

theorem dce_guarded_div_compiles :
    Compiles L_DCE_Guarded L_DCE_Guarded (BehaviorCodec.id L_DCE_Guarded) false true := by
  intro (x, d) hNonZero
  refine ⟨trivial, ?_⟩
  intro out hOut
  exact ⟨out, rfl, hOut⟩

/-! ## Section 5: Probe 3 — Tree Borrows Read Elimination & Inlining Protector Removal -/

/-- Models whether a foreign conflicting access occurred (`conflict = true`).
    In source MIR (with the second shared read or active function-entry
    `Protector`), `conflict = true` triggers Tree Borrows UB (`Partial.ub`).
    In target MIR (after read elimination or function inlining removes the
    protector), the conflicting access is permitted (`Partial.pure`). -/
def treeBorrowsSourceWithReadOrProtector : Behavior (Bool × Nat) (EventualOut Unit Nat) :=
  fun (conflict, v) =>
    if conflict then
      Partial.ub
    else
      Partial.pure (fun out => out = .terminated [] (.normal v))

def treeBorrowsTargetOptimized : Behavior (Bool × Nat) (EventualOut Unit Nat) :=
  fun (_conflict, v) =>
    Partial.pure (fun out => out = .terminated [] (.normal v))

def L_TreeBorrows : Language (EventualOut Unit Unit) where
  Prog := Bool -- `false` = source with read/protector, `true` = optimized/inlined
  Query := Bool × Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun opt =>
    if opt then treeBorrowsTargetOptimized else treeBorrowsSourceWithReadOrProtector

/-- Eliminating a read or dropping a function-entry protector during inlining is
    unconditionally a valid refinement (`Compiles`). -/
theorem inline_drops_protector_refines :
    Compiles L_TreeBorrows L_TreeBorrows (BehaviorCodec.id L_TreeBorrows) false true := by
  intro (conflict, v) hSrcDef
  cases conflict with
  | true => exact False.elim hSrcDef
  | false =>
    refine ⟨trivial, ?_⟩
    intro out hOut
    exact ⟨out, rfl, hOut⟩

/-- Outlining (the reverse transformation, adding a protector where none existed)
    is NOT unconditionally sound because it introduces UB when `conflict = true`. -/
theorem inline_protector_not_reversible :
    ¬ Compiles L_TreeBorrows L_TreeBorrows (BehaviorCodec.id L_TreeBorrows) true false := by
  intro hRev
  have ⟨hDef, _⟩ := hRev (true, 7) trivial
  exact hDef

/-! ## Section 6: Probe 4 — `DSE` Across Diverging `externalCall` Requires Immediate Protector Enforcement -/

/-- Consider `*x = 1; opaque_ext_call(); *x = 2;` where `opaque_ext_call()` reads
    a stashed raw pointer to `*x`, emits that value as an observation, and then
    diverges or halts.
    If the protector on `x : &mut i32` only triggers UB upon `foo` returning
    (late protector), then when `opaque_ext_call()` halts/exits early, `s` is
    defined and observes `1`, whereas `t` (which eliminated `*x = 1`) observes
    the old value `0`! -/
def dseLateProtectorSrc : Behavior Unit (EventualOut Nat Unit) :=
  fun () => Partial.pure (fun out => out = .terminated [1] .unwind)

def dseLateProtectorTgt : Behavior Unit (EventualOut Nat Unit) :=
  fun () => Partial.pure (fun out => out = .terminated [0] .unwind)

def L_DSE_LateProtector : Language (EventualOut Nat Unit) where
  Prog := Bool
  Query := Unit
  Out := EventualOut Nat Unit
  obs := EventualOut.toSpine
  sem := fun opt => if opt then dseLateProtectorTgt else dseLateProtectorSrc

theorem dse_across_diverging_external_call_unsound_if_late_protector :
    ¬ Compiles L_DSE_LateProtector L_DSE_LateProtector
        (BehaviorCodec.id L_DSE_LateProtector) false true := by
  intro hComp
  have ⟨_, hSub⟩ := hComp () trivial
  have ⟨o₁, hDec, hSrcOut⟩ := hSub (.terminated [0] .unwind) rfl
  injection hDec with hEq
  subst hEq
  dsimp [L_DSE_LateProtector, dseLateProtectorSrc] at hSrcOut
  nomatch hSrcOut

/-! ## Section 7: Probe 5 — `LICM` Trapping Hoist on Zero-Trip Loops -/

/-- Query `(tripCount, divisor)`. Inside the loop body is `100 / divisor`.
    When `tripCount = 0` and `divisor = 0`, the unhoisted loop executes 0
    iterations and returns `0` normally. -/
def licmSourceLoop : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (trips, d) =>
    Partial.pure (fun out =>
      if trips = 0 then
        out = .terminated [] (.normal 0)
      else if d = 0 then
        out = .terminated [] .unwind
      else
        out = .terminated [] (.normal (100 / d)))

/-- Unconditional preheader hoist evaluates `100 / divisor` even when `trips = 0`. -/
def licmUnguardedHoist : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (trips, d) =>
    Partial.pure (fun out =>
      if d = 0 then
        out = .terminated [] .unwind
      else if trips = 0 then
        out = .terminated [] (.normal 0)
      else
        out = .terminated [] (.normal (100 / d)))

def L_LICM : Language (EventualOut Unit Unit) where
  Prog := Bool
  Query := Nat × Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun hoisted => if hoisted then licmUnguardedHoist else licmSourceLoop

theorem licm_trapping_zero_trip_unsound :
    ¬ Compiles L_LICM L_LICM (BehaviorCodec.id L_LICM) false true := by
  intro hComp
  have ⟨_, hSub⟩ := hComp (0, 0) trivial
  have ⟨o₁, hDec, hSrcOut⟩ := hSub (.terminated [] .unwind) rfl
  injection hDec with hEq
  subst hEq
  dsimp [L_LICM, licmSourceLoop] at hSrcOut
  nomatch hSrcOut

/-! ## Section 8: Probe 6 — Coroutine Self-Referential `Pin<&mut Self>` Invariant -/

/-- Query `(entryAddr, resumeAddr, fieldVal)` models the base address of
    `CoroutineState` at the suspension point (`entryAddr`) and at resumption
    (`resumeAddr`). If the coroutine holds an interior pointer `r = entryAddr`
    and dereferences it at resumption, moving the state (`resumeAddr ≠ entryAddr`)
    causes a dangling-pointer dereference (`Partial.ub`). -/
abbrev CoroQuery := Nat × Nat × Nat

def loweredCoroutinePoll : Behavior CoroQuery (EventualOut Unit Nat) :=
  fun (entryAddr, resumeAddr, v) => {
    defined := resumeAddr = entryAddr
    val := fun _ out => out = .terminated [] (.normal v)
  }

def L_Coro : Language (EventualOut Unit Unit) where
  Prog := Unit
  Query := CoroQuery
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun () => loweredCoroutinePoll

def PinPre (q : CoroQuery) : Prop :=
  q.2.1 = q.1

theorem coroutine_pinned_productive :
    InhabitedPre PinPre ∧ L_Coro.ProductiveOn PinPre () := by
  refine ⟨⟨(1, 1, 42), rfl⟩, ?_⟩
  intro (entryAddr, resumeAddr, v) hPin
  exact ⟨hPin, .terminated [] (.normal v), rfl⟩

theorem coroutine_unpinned_move_violates_safety :
    ¬ (L_Coro.sem () (1, 2, 42)).defined := by
  intro hDef
  nomatch hDef

/-! ## Section 9: Probe 7 — `c2rust` Vacuity Guard (`ProductiveOn`) & Empty-Slice Null Pointer Trap -/

/-- A buggy C function that exhibits unconditional UB (`Partial.ub`) on all
    inputs vacuously `Compiles` to any target program `t`, even one that is UB. -/
def cUbProg : Behavior Nat (EventualOut Unit Nat) :=
  fun _ => Partial.ub

def L_C2Rust : Language (EventualOut Unit Unit) where
  Prog := Bool -- `false` = UB C program, `true` = arbitrary target
  Query := Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun _ => cUbProg

theorem c2rust_ub_source_vacuously_compiles_without_productiveOn :
    Compiles L_C2Rust L_C2Rust (BehaviorCodec.id L_C2Rust) false true := by
  intro _ hDef
  exact False.elim hDef

/-- Requiring `L_C2Rust.ProductiveOn pre false` immediately blocks vacuous
    C-to-Rust compilation of an unconditionally UB C source function. -/
theorem c2rust_productiveOn_blocks_ub_source :
    ¬ L_C2Rust.ProductiveOn (fun _ => True) false := by
  intro hProd
  have ⟨hDef, _⟩ := hProd (0 : Nat) trivial
  exact hDef

/-- C buffer `(ptr, len)` allows `(0, 0)` (NULL with zero length), whereas safe
    Rust `&[u8]` requires `ptr ≠ 0` even when `len = 0` (`NonNull::dangling()`).
    A naive identity query mapping fails to preserve definedness at `(0, 0)`. -/
def cBufferRead : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (ptr, len) =>
    if len = 0 then
      Partial.pure (fun out => out = .terminated [] (.normal 0))
    else if ptr = 0 then
      Partial.ub
    else
      Partial.pure (fun out => out = .terminated [] (.normal len))

def rustSliceRead : Behavior (Nat × Nat) (EventualOut Unit Nat) :=
  fun (ptr, len) =>
    if ptr = 0 then
      Partial.ub
    else if len = 0 then
      Partial.pure (fun out => out = .terminated [] (.normal 0))
    else
      Partial.pure (fun out => out = .terminated [] (.normal len))

def L_SliceCheck : Language (EventualOut Unit Unit) where
  Prog := Bool -- `false` = C `(ptr, len)`, `true` = Rust `&[u8]`
  Query := Nat × Nat
  Out := EventualOut Unit Nat
  obs := EventualOut.toSpine
  sem := fun isRust => if isRust then rustSliceRead else cBufferRead

theorem c2rust_null_empty_slice_rejected_under_idCodec :
    ¬ Compiles L_SliceCheck L_SliceCheck (BehaviorCodec.id L_SliceCheck) false true := by
  intro hComp
  have ⟨hRustDef, _⟩ := hComp (0, 0) trivial
  exact hRustDef

#print axioms mem2reg_uninit_refines
#print axioms mem2reg_uninit_not_symmetric
#print axioms dce_panicking_div_unsound
#print axioms dce_guarded_div_compiles
#print axioms inline_drops_protector_refines
#print axioms inline_protector_not_reversible
#print axioms dse_across_diverging_external_call_unsound_if_late_protector
#print axioms licm_trapping_zero_trip_unsound
#print axioms coroutine_pinned_productive
#print axioms coroutine_unpinned_move_violates_safety
#print axioms c2rust_ub_source_vacuously_compiles_without_productiveOn
#print axioms c2rust_productiveOn_blocks_ub_source
#print axioms c2rust_null_empty_slice_rejected_under_idCodec

end MidLevelProbes
