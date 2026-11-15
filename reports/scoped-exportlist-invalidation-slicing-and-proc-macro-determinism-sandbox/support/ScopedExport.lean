-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Per-Trait and Per-Symbol Scoped `ExportList` Certificates (`ScopedExportCert`)

Mechanizes the compositional soundness theorem (`scopedExport_implies_wpo_sound`)
for `AnnealCacheKey` Tier 2 (`CalleeSummaryKey`):
Instead of hashing the monolithic whole-program `ExportList` across all symbols
and traits in a workspace, each function's WPO certificate (`WholeProgramDevirt`,
`GlobalOpt`, `DeadArgElim`) records a fine-grained `ScopedExportSlice` listing
only the specific `SymbolId` and `TraitId` entries it relies upon.

Whenever the global linker `ExportList` changes (`tbl₁ → tbl₂`), any function
whose cited `ScopedExportSlice` agrees between `tbl₁` and `tbl₂` preserves its
whole-program soundness (`WpoGlobalSound`) with zero certificate re-checking.
-/

namespace Anneal.ScopedExport

abbrev SymbolId := Nat
abbrev TraitId := Nat
abbrev VtableId := Nat

/-- Per-symbol export and address-escape metadata in the linker `ExportList`. -/
structure SymbolExportMeta where
  isExported : Bool
  addressTaken : Bool
  inUsedSet : Bool
  deriving Repr, DecidableEq

/-- Decidable projection of a trait's vtable metadata for a single method slot. -/
structure ScopedTraitEntry where
  traitId : TraitId
  slotIdx : Nat
  vtableEscapesDylib : Bool
  closedVtableCount : Nat
  uniqueImpl : Option SymbolId
  deriving Repr, DecidableEq

/-- Decidable projection of a symbol's export metadata. -/
structure ScopedSymbolEntry where
  symId : SymbolId
  info : SymbolExportMeta
  deriving Repr, DecidableEq

/-- Whole-program linker export and vtable table (`GlobalExportTable`). -/
structure GlobalExportTable where
  symMeta : SymbolId → SymbolExportMeta
  traitMeta : TraitId → Nat → (Bool × Nat × Option SymbolId)

/-- Lookup helper returning the canonical `ScopedSymbolEntry` from `tbl`. -/
def querySymbol (tbl : GlobalExportTable) (s : SymbolId) : ScopedSymbolEntry :=
  { symId := s, info := tbl.symMeta s }

/-- Lookup helper returning the canonical `ScopedTraitEntry` from `tbl`. -/
def queryTrait (tbl : GlobalExportTable) (t : TraitId) (slot : Nat) : ScopedTraitEntry :=
  let (esc, cnt, impl) := tbl.traitMeta t slot
  { traitId := t, slotIdx := slot, vtableEscapesDylib := esc, closedVtableCount := cnt, uniqueImpl := impl }

/-- A function's Tier 2 `ScopedExportSlice` records only the symbols and trait
slots actually cited by its `HybridTrace` WPO derivation steps. -/
structure ScopedExportSlice where
  citedSymbols : List ScopedSymbolEntry
  citedTraits : List ScopedTraitEntry
  deriving Repr, DecidableEq

/-- Decidable check that every symbol entry in `entries` matches `tbl`. -/
def symbolsMatchTable (entries : List ScopedSymbolEntry) (tbl : GlobalExportTable) : Bool :=
  entries.all (fun e => querySymbol tbl e.symId == e)

/-- Decidable check that every trait slot entry in `entries` matches `tbl`. -/
def traitsMatchTable (entries : List ScopedTraitEntry) (tbl : GlobalExportTable) : Bool :=
  entries.all (fun e => queryTrait tbl e.traitId e.slotIdx == e)

/-- Decidable Tier 2 cache validation predicate: checks whether `slice` matches `tbl`. -/
def sliceMatchesTable (slice : ScopedExportSlice) (tbl : GlobalExportTable) : Bool :=
  symbolsMatchTable slice.citedSymbols tbl && traitsMatchTable slice.citedTraits tbl

/-- Three canonical WPO step schemas governed by `ExportList` side conditions. -/
inductive WpoStepCert where
  | devirtSingleImpl (traitId : TraitId) (slotIdx : Nat) (targetFn : SymbolId)
  | globalOptConstPromote (staticSym : SymbolId) (hasMutatingStore : Bool)
  | deadArgElim (fnSym : SymbolId) (paramIdx : Nat)
  deriving Repr, DecidableEq

/-- Local certificate checker operating purely on the cached `ScopedExportSlice`
without inspecting the full `GlobalExportTable`. -/
def checkWpoWithSlice (step : WpoStepCert) (slice : ScopedExportSlice) : Bool :=
  match step with
  | .devirtSingleImpl t slot targetFn =>
      let expected : ScopedTraitEntry := {
        traitId := t
        slotIdx := slot
        vtableEscapesDylib := false
        closedVtableCount := 1
        uniqueImpl := some targetFn
      }
      slice.citedTraits.contains expected
  | .globalOptConstPromote s hasStore =>
      let internalMeta : SymbolExportMeta := {
        isExported := false
        addressTaken := false
        inUsedSet := false
      }
      (!hasStore) && slice.citedSymbols.contains { symId := s, info := internalMeta }
  | .deadArgElim f _ =>
      let internalMeta : SymbolExportMeta := {
        isExported := false
        addressTaken := false
        inUsedSet := false
      }
      slice.citedSymbols.contains { symId := f, info := internalMeta }

/-- Semantic validity of `step` against the whole-program `GlobalExportTable`. -/
def WpoGlobalSound (step : WpoStepCert) (tbl : GlobalExportTable) : Prop :=
  match step with
  | .devirtSingleImpl t slot targetFn =>
      queryTrait tbl t slot = {
        traitId := t
        slotIdx := slot
        vtableEscapesDylib := false
        closedVtableCount := 1
        uniqueImpl := some targetFn
      }
  | .globalOptConstPromote s hasStore =>
      hasStore = false ∧
      querySymbol tbl s = {
        symId := s
        info := { isExported := false, addressTaken := false, inUsedSet := false }
      }
  | .deadArgElim f _ =>
      querySymbol tbl f = {
        symId := f
        info := { isExported := false, addressTaken := false, inUsedSet := false }
      }

theorem list_all_mem_eq {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {p : α → Bool} {x : α}
    (hall : xs.all p = true) (hmem : xs.contains x = true) : p x = true := by
  rw [List.all_eq_true] at hall
  rw [List.contains_iff_mem] at hmem
  exact hall x hmem

/-- Soundness of `checkWpoWithSlice`: if `step` checks against `slice` and `slice`
matches `tbl`, then `WpoGlobalSound step tbl` holds. -/
theorem checkWpoWithSlice_sound (step : WpoStepCert) (slice : ScopedExportSlice) (tbl : GlobalExportTable)
    (hcheck : checkWpoWithSlice step slice = true)
    (hmatch : sliceMatchesTable slice tbl = true) :
    WpoGlobalSound step tbl := by
  unfold sliceMatchesTable symbolsMatchTable traitsMatchTable at hmatch
  revert hcheck
  cases step with
  | devirtSingleImpl t slot targetFn =>
      intro hcheck
      unfold checkWpoWithSlice at hcheck
      have htraits : (slice.citedTraits.all fun e => queryTrait tbl e.traitId e.slotIdx == e) = true := by
        cases h1 : slice.citedSymbols.all (fun e => querySymbol tbl e.symId == e) <;>
        cases h2 : slice.citedTraits.all (fun e => queryTrait tbl e.traitId e.slotIdx == e) <;>
        simp_all
      have hq := list_all_mem_eq htraits hcheck
      simp only [beq_iff_eq] at hq
      exact hq
  | globalOptConstPromote s hasStore =>
      intro hcheck
      unfold checkWpoWithSlice at hcheck
      have hsyms : (slice.citedSymbols.all fun e => querySymbol tbl e.symId == e) = true := by
        cases h1 : slice.citedSymbols.all (fun e => querySymbol tbl e.symId == e) <;>
        cases h2 : slice.citedTraits.all (fun e => queryTrait tbl e.traitId e.slotIdx == e) <;>
        simp_all
      cases hasStore with
      | true => simp at hcheck
      | false =>
          simp only [Bool.not_false, Bool.true_and] at hcheck
          have hq := list_all_mem_eq hsyms hcheck
          simp only [beq_iff_eq] at hq
          exact ⟨rfl, hq⟩
  | deadArgElim f paramIdx =>
      intro hcheck
      unfold checkWpoWithSlice at hcheck
      have hsyms : (slice.citedSymbols.all fun e => querySymbol tbl e.symId == e) = true := by
        cases h1 : slice.citedSymbols.all (fun e => querySymbol tbl e.symId == e) <;>
        cases h2 : slice.citedTraits.all (fun e => queryTrait tbl e.traitId e.slotIdx == e) <;>
        simp_all
      have hq := list_all_mem_eq hsyms hcheck
      simp only [beq_iff_eq] at hq
      exact hq

/-- Two `GlobalExportTable` instances agree on a `ScopedExportSlice` when they return
identical metadata for all symbols and trait slots recorded in `slice`. -/
def AgreeOnSlice (slice : ScopedExportSlice) (tbl1 tbl2 : GlobalExportTable) : Prop :=
  (∀ e ∈ slice.citedSymbols, querySymbol tbl1 e.symId = querySymbol tbl2 e.symId) ∧
  (∀ e ∈ slice.citedTraits, queryTrait tbl1 e.traitId e.slotIdx = queryTrait tbl2 e.traitId e.slotIdx)

theorem all_congr_mem {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.all_cons]
      have hhd : p hd = q hd := h hd (by simp)
      have htl : tl.all p = tl.all q := ih (fun x hx => h x (by simp [hx]))
      rw [hhd, htl]

/-- Frame invariance of `sliceMatchesTable` under unrelated `ExportList` edits. -/
theorem scopedExport_frame_invariance (slice : ScopedExportSlice) (tbl1 tbl2 : GlobalExportTable)
    (hagree : AgreeOnSlice slice tbl1 tbl2) :
    sliceMatchesTable slice tbl1 = sliceMatchesTable slice tbl2 := by
  rcases hagree with ⟨hsym, htrait⟩
  unfold sliceMatchesTable symbolsMatchTable traitsMatchTable
  have h1 : (slice.citedSymbols.all fun e => querySymbol tbl1 e.symId == e) =
            (slice.citedSymbols.all fun e => querySymbol tbl2 e.symId == e) := by
    apply all_congr_mem
    intro e he
    rw [hsym e he]
  have h2 : (slice.citedTraits.all fun e => queryTrait tbl1 e.traitId e.slotIdx == e) =
            (slice.citedTraits.all fun e => queryTrait tbl2 e.traitId e.slotIdx == e) := by
    apply all_congr_mem
    intro e he
    rw [htrait e he]
  rw [h1, h2]

/-- Main compositional caching theorem (`K5_`): if a function's WPO certificate was
verified against `slice` under `tbl1`, and an `ExportList` edit produces `tbl2`
that agrees with `tbl1` on `slice` (`AgreeOnSlice slice tbl1 tbl2`), then `step`
remains globally sound under `tbl2` with zero re-verification steps. -/
theorem scopedExport_implies_wpo_sound
    (step : WpoStepCert) (slice : ScopedExportSlice) (tbl1 tbl2 : GlobalExportTable)
    (hcheck : checkWpoWithSlice step slice = true)
    (hmatch1 : sliceMatchesTable slice tbl1 = true)
    (hagree : AgreeOnSlice slice tbl1 tbl2) :
    WpoGlobalSound step tbl2 := by
  have hmatch2 : sliceMatchesTable slice tbl2 = true := by
    rw [← scopedExport_frame_invariance slice tbl1 tbl2 hagree]
    exact hmatch1
  exact checkWpoWithSlice_sound step slice tbl2 hcheck hmatch2

/-- Negative canary 1: if an edited `ExportList` newly exports symbol `42` (`isExported = true`),
a `ScopedExportSlice` requiring symbol `42` to be internal (`isExported = false`)
evaluates `sliceMatchesTable` to `false`, preventing unsound DAE or GlobalOpt reuse. -/
def canarySliceSym42 : ScopedExportSlice := {
  citedSymbols := [{
    symId := 42
    info := { isExported := false, addressTaken := false, inUsedSet := false }
  }]
  citedTraits := []
}

def canaryTblExported42 : GlobalExportTable := {
  symMeta := fun s => if s == 42 then { isExported := true, addressTaken := false, inUsedSet := false }
                      else { isExported := false, addressTaken := false, inUsedSet := false }
  traitMeta := fun _ _ => (false, 1, some 100)
}

theorem canary_exported_symbol_invalidates_slice :
    sliceMatchesTable canarySliceSym42 canaryTblExported42 = false := rfl

/-- Negative canary 2: if a trait `7` has its vtable exported to a dynamic library
(`vtableEscapesDylib = true`), the closed-world `WPD` slice for trait `7` is rejected. -/
def canarySliceTrait7 : ScopedExportSlice := {
  citedSymbols := []
  citedTraits := [{
    traitId := 7
    slotIdx := 0
    vtableEscapesDylib := false
    closedVtableCount := 1
    uniqueImpl := some 200
  }]
}

def canaryTblOpenTrait7 : GlobalExportTable := {
  symMeta := fun _ => { isExported := false, addressTaken := false, inUsedSet := false }
  traitMeta := fun t _ => if t == 7 then (true, 1, some 200) else (false, 1, some 200)
}

theorem canary_open_trait_dylib_invalidates_devirt :
    sliceMatchesTable canarySliceTrait7 canaryTblOpenTrait7 = false := rfl

#print axioms checkWpoWithSlice_sound
#print axioms scopedExport_frame_invariance
#print axioms scopedExport_implies_wpo_sound
#print axioms canary_exported_symbol_invalidates_slice
#print axioms canary_open_trait_dylib_invalidates_devirt

end Anneal.ScopedExport
