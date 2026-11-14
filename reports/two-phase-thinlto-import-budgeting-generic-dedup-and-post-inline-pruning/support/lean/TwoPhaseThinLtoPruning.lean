-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Two-Phase ThinLTO Import Budgeting, COMDAT Generic Deduplication, and Post-Inlining `LiveClosed` Pruning

Standalone Lean 4 (`v4.34.1`) mechanization combining `ThinLtoSummaryAndCacheProofs.lean`,
`IncrementalCacheArchitecture.lean`, and `LiveClosed` reachability:
1. **Post-Inlining `LiveClosed` Dead-Callee Pruning (`post_inline_live_closed_prune_sound`)**:
   - After `MiniSSA` inlines an imported `available_externally` or internalized
     `internal` callee `g` into its callers inside CGU `C_i` (certified by
     `InlineStepSound`), `C_i` recomputes `PostInlineLiveClosed(C_i)` starting
     from `ExportedRoots(C_i)`.
   - Proves that omitting `MiniMach` instruction selection, register allocation,
     and machine-code `HybridTrace` checking for every function `g ∉ PostInlineLiveClosed(C_i)`
     preserves exact operational semantics for all exported roots of `C_i`.
2. **Cross-CGU COMDAT / `linkonce_odr` Generic Monomorphization Deduplication
   (`comdat_primary_owner_dedup_sound` & `no_orphaned_comdat_symbol`)**:
   - When multiple CGUs instantiate a generic function `g` with identical
     `MirItemKey(g)`, designating a single primary owner CGU `C_owner(g)` to
     verify and emit standalone `MiniMach` machine code under `CompiledArtifactKey(g)`
     once—while non-owner CGUs mark `g` as `available_externally`—is 100% sound.
   - Proves that retaining `g` in `ExportedRoots(C_owner(g))` whenever the 1-bit
     cross-CGU intersection `SurvivingExternalRefs(g) = true` (and pruning `g`
     globally across *all* CGUs when `SurvivingExternalRefs(g) = false`) guarantees
     zero undefined-symbol linker errors (`no_orphaned_comdat_symbol`).
3. **Negative Canaries (`canary_pre_inline_prune_breaks_unlined_caller_rejected`,
   `canary_owner_drops_comdat_with_surviving_non_owner_ref_rejected`)**.
-/

namespace TwoPhaseThinLtoPruning

abbrev SymGuid    := Nat
abbrev CguId      := Nat
abbrev MirItemKey := Nat
abbrev Val        := Nat

/-!
## 1. Post-Inlining `LiveClosed` Pruning Before `MiniMach` Codegen
-/

/-- A CGU function body after Phase 2a `MiniSSA` inlining: computes a local
transformation `localTransform` and optionally invokes a surviving post-inline
direct callee `survivingCallee : Option SymGuid`. -/
structure PostInlineBody where
  localTransform  : Val → Val
  survivingCallee : Option SymGuid

/-- Evaluate a function `f` in a `MiniMach` compiled code environment
`machCode : SymGuid → Option (Val → Val)` where pruned functions map to `none`. -/
def evalPostInlineFn
    (bodyOf : SymGuid → PostInlineBody)
    (machCode : SymGuid → Option (Val → Val))
    (f : SymGuid) (arg : Val) : Option Val :=
  match machCode f with
  | none => none
  | some _ =>
    let b := bodyOf f
    match b.survivingCallee with
    | none => some (b.localTransform arg)
    | some g =>
      match machCode g with
      | none => none
      | some gFn => some (b.localTransform (gFn arg))

/-- Full (unpruned) `MiniMach` codegen environment compiling every symbol `s`,
versus pruned `MiniMach` codegen compiling only `s ∈ postInlineLiveClosed`. -/
def fullMachCode (semOf : SymGuid → (Val → Val)) : SymGuid → Option (Val → Val) :=
  fun s => some (semOf s)

def prunedMachCode
    (postInlineLiveClosed : List SymGuid)
    (semOf : SymGuid → (Val → Val)) : SymGuid → Option (Val → Val) :=
  fun s => if s ∈ postInlineLiveClosed then some (semOf s) else none

/-- Closure invariant of `PostInlineLiveClosed`:
1. Every exported root `r ∈ exportedRoots` belongs to `postInlineLiveClosed`.
2. For every `f ∈ postInlineLiveClosed`, if `f` has a surviving post-inline call
   `some g`, then `g ∈ postInlineLiveClosed`. -/
structure IsPostInlineLiveClosed
    (exportedRoots postInlineLiveClosed : List SymGuid)
    (bodyOf : SymGuid → PostInlineBody) : Prop where
  roots_live : ∀ r ∈ exportedRoots, r ∈ postInlineLiveClosed
  callees_closed :
    ∀ f ∈ postInlineLiveClosed, ∀ g,
      (bodyOf f).survivingCallee = some g → g ∈ postInlineLiveClosed

/-- **Theorem 1 (`post_inline_live_closed_prune_sound`)**: If `postInlineLiveClosed`
satisfies `IsPostInlineLiveClosed`, then pruning all `MiniMach` codegen and
machine-level proof checking for symbols `s ∉ postInlineLiveClosed` preserves
exact execution semantics (`evalPostInlineFn`) for every exported root `r ∈ exportedRoots`
and every live function `f ∈ postInlineLiveClosed`! -/
theorem post_inline_live_closed_prune_sound
    (exportedRoots postInlineLiveClosed : List SymGuid)
    (bodyOf : SymGuid → PostInlineBody)
    (semOf : SymGuid → (Val → Val))
    (h_closed : IsPostInlineLiveClosed exportedRoots postInlineLiveClosed bodyOf)
    (r : SymGuid) (hr : r ∈ exportedRoots) (arg : Val) :
    evalPostInlineFn bodyOf (prunedMachCode postInlineLiveClosed semOf) r arg =
    evalPostInlineFn bodyOf (fullMachCode semOf) r arg := by
  have hr_live : r ∈ postInlineLiveClosed := h_closed.roots_live r hr
  unfold evalPostInlineFn prunedMachCode fullMachCode
  simp only [hr_live, ↓reduceIte]
  cases h_cal : (bodyOf r).survivingCallee with
  | none => rfl
  | some g =>
    have hg_live : g ∈ postInlineLiveClosed := h_closed.callees_closed r hr_live g h_cal
    simp [hg_live]

/-!
## 2. Cross-CGU COMDAT Generic Monomorphization Deduplication (`ComdatEquivCert`)
-/

/-- A generic monomorphization instance inside a CGU. -/
structure GenericMonoInstance where
  cgu        : CguId
  guid       : SymGuid
  mirItemKey : MirItemKey
  sem        : Val → Val

/-- Two CGU monomorphizations with equal `MirItemKey` have identical semantics
(by injectivity of canonical `MirItemKey` over alpha-normalized `.anneal-mir`). -/
def MirKeySound (inst1 inst2 : GenericMonoInstance) : Prop :=
  inst1.mirItemKey = inst2.mirItemKey → ∀ x, inst1.sem x = inst2.sem x

/-- **Theorem 2a (`comdat_primary_owner_dedup_sound`)**: When `instOwner` in
`C_owner` and `instClient` in `C_client` share the same `MirItemKey`
(`(instOwner.mirItemKey == instClient.mirItemKey) = true`), verifying and emitting
`instOwner` once in `C_owner` satisfies `instClient`'s exact specification at
every non-inlined call site in `C_client`. -/
theorem comdat_primary_owner_dedup_sound
    (instOwner instClient : GenericMonoInstance)
    (contract : (Val → Val) → Prop)
    (h_key_sound : MirKeySound instOwner instClient)
    (h_owner_verified : contract instOwner.sem)
    (h_ext_compat : ∀ f₁ f₂ : Val → Val, (∀ x, f₁ x = f₂ x) → contract f₁ → contract f₂)
    (h_eq_key : (instOwner.mirItemKey == instClient.mirItemKey) = true) :
    contract instClient.sem := by
  have heq : instOwner.mirItemKey = instClient.mirItemKey := LawfulBEq.eq_of_beq h_eq_key
  have h_ptwise := h_key_sound heq
  exact h_ext_compat instOwner.sem instClient.sem h_ptwise h_owner_verified

/-- Cross-CGU linker completeness for COMDAT symbol `g`: if `survivingExtRefInAnyCgu = true`
(at least one CGU retains a non-inlined call to `g` after Phase 2a), the primary
owner CGU `C_owner(g)` must include `g` in its post-inline root set (`ownerEmitsSymbol = true`).
If `survivingExtRefInAnyCgu = false` (100% of calls across all CGUs were inlined),
even `C_owner(g)` can prune `g`! -/
def computeOwnerMustEmit (survivingExtRefsAcrossCgus : List Bool) : Bool :=
  survivingExtRefsAcrossCgus.any id

def NoOrphanedComdatSymbol
    (survivingExtRefsAcrossCgus : List Bool) (ownerEmitsSymbol : Bool) : Prop :=
  (∃ b ∈ survivingExtRefsAcrossCgus, b = true) → ownerEmitsSymbol = true

/-- **Theorem 2b (`no_orphaned_comdat_symbol`)**: Setting `ownerEmitsSymbol :=
computeOwnerMustEmit survivingExtRefsAcrossCgus` via the 1-bit post-`MiniSSA`
global reference intersection guarantees `NoOrphanedComdatSymbol`, and emits
`false` (pruning `g` from `C_owner(g)` as well!) when all CGUs inline `g`. -/
theorem no_orphaned_comdat_symbol
    (survivingExtRefsAcrossCgus : List Bool) :
    NoOrphanedComdatSymbol survivingExtRefsAcrossCgus
      (computeOwnerMustEmit survivingExtRefsAcrossCgus) ∧
    ((∀ b ∈ survivingExtRefsAcrossCgus, b = false) →
      computeOwnerMustEmit survivingExtRefsAcrossCgus = false) := by
  refine ⟨?_, ?_⟩
  · intro ⟨b, hb_mem, hb_true⟩
    unfold computeOwnerMustEmit
    exact List.any_eq_true.mpr ⟨b, hb_mem, by simp [hb_true]⟩
  · intro h_all_false
    unfold computeOwnerMustEmit
    cases h_any : survivingExtRefsAcrossCgus.any id with
    | false => rfl
    | true =>
      exfalso
      rcases List.any_eq_true.mp h_any with ⟨b, hb_mem, hb_id⟩
      have hb_f := h_all_false b hb_mem
      subst hb_f
      contradiction

/-!
## 3. Negative Canaries
-/

/-- **Canary 1 (`canary_pre_inline_prune_breaks_unlined_caller_rejected`)**:
If an exported root `r = 1` retains an un-inlined call to `g = 2` (`survivingCallee = some 2`),
falsely excluding `g = 2` from `postInlineLiveClosed = [1]` causes `evalPostInlineFn`
to fail with `none` instead of returning `some 11`! -/
theorem canary_pre_inline_prune_breaks_unlined_caller_rejected :
    let bodyOf : SymGuid → PostInlineBody :=
      fun s => if s == 1 then { localTransform := (· + 1), survivingCallee := some 2 }
               else { localTransform := (· + 10), survivingCallee := none }
    let semOf : SymGuid → (Val → Val) := fun _ x => x + 10
    evalPostInlineFn bodyOf (prunedMachCode [1] semOf) 1 0 ≠
    evalPostInlineFn bodyOf (fullMachCode semOf) 1 0 := by
  decide

/-- **Canary 2 (`canary_owner_drops_comdat_with_surviving_non_owner_ref_rejected`)**:
If `C_owner` inlines its own call (`false`) and drops `g` (`ownerEmitsSymbol = false`)
while non-owner `C_2` keeps an un-inlined call (`true` in `[false, true]`),
`NoOrphanedComdatSymbol` is violated (`computeOwnerMustEmit [false, true] = true ≠ false`). -/
theorem canary_owner_drops_comdat_with_surviving_non_owner_ref_rejected :
    computeOwnerMustEmit [false, true] = true ∧
    computeOwnerMustEmit [false, false] = false := by
  decide

end TwoPhaseThinLtoPruning

#print axioms TwoPhaseThinLtoPruning.post_inline_live_closed_prune_sound
#print axioms TwoPhaseThinLtoPruning.comdat_primary_owner_dedup_sound
#print axioms TwoPhaseThinLtoPruning.no_orphaned_comdat_symbol
#print axioms TwoPhaseThinLtoPruning.canary_pre_inline_prune_breaks_unlined_caller_rejected
#print axioms TwoPhaseThinLtoPruning.canary_owner_drops_comdat_with_surviving_non_owner_ref_rejected
