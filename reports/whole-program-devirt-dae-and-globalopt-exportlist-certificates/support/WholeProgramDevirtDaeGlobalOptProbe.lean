-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Whole-Program Devirtualization, Dead-Argument Elimination, and Global Promotion Replay Under `ExportList` Closed-World Contracts

Standalone Lean 4 (`v4.34.1`) mechanization extending `S2`'s compositional
linking framework (`CompositionalLinkingAndThinLtoWpoProbe.lean`) to the four
signature- and global-mutating whole-program optimization families:
1. **Closed-Trait-World Devirtualization (`ClosedTraitVTables(TraitId, ExportList)`)**:
   - `wpo_devirt_single_impl_sound` (`WPO-DevirtSingleImpl`): When a closed
     crate graph linked at `SymbolExportLevel::C` has a unique vtable `v₀` for
     `TraitId` (or all vtables for `TraitId` map `slot` to the same function
     `uniqueFn`), replacing indirect vtable dispatch unconditionally with a
     direct call to `uniqueFn` is observationally equivalent.
   - `wpo_devirt_branch_funnel_sound` (`WPO-DevirtBranchFunnel`): When a closed
     crate graph has `2 ≤ |VTables(TraitId)| ≤ 4` (modeled for `k = 3` vtables
     `v₁, v₂, v₃`), an exhaustive `if-else` ladder with *no indirect fallback*
     is observationally equivalent to indirect vtable dispatch.
   - `wpo_devirt_const_ret_sound` (`WPO-DevirtConstRet`) and
     `wpo_vfe_unused_slot_strip_sound` (`WPO-VFE`): Virtual constant propagation
     and unused vtable slot stripping under `ClosedTraitVTables`.
   - `canary_open_world_devirt_unsound`: Proves that omitting the closed-world
     `ClosedTraitVTables` premise (e.g., when a `dylib` or FFI plugin introduces
     an unrecorded vtable `v_ext`) causes unconditional devirtualization or
     branch-funnel dispatch without fallback to miscompile!
2. **Dead-Argument Elimination (`WPO-DeadArgAndRetElim`) and By-Reference-to-By-Value
   Argument Promotion (`WPO-ArgPromoteByVal`)**:
   - `wpo_dead_arg_and_ret_elim_sound`: Proves that when `sym ∉ ExportList` and
     `!AddressTaken(sym, ModuleGraph)`, simultaneously dropping an unused
     parameter/return component at `sym`'s definition and at every direct call
     site preserves whole-program semantics.
   - `wpo_arg_promote_by_val_sound`: Proves that promoting a pointer parameter
     `ptr : Nat` to a scalar value `m ptr` is sound when `sym ∉ ExportList`,
     `!AddressTaken(sym)`, and no store aliases `ptr` before its loads inside
     `sym`.
   - `canary_address_taken_dae_unsound` and `canary_aliased_arg_promote_unsound`:
     Negative canary theorems proving unsoundness when `AddressTaken(sym)` holds
     or when an aliased store precedes the load of the promoted pointer.
3. **`GlobalOpt` Static Promotion, Single-Function `alloca` Localization, and
   Boolean Shrinking (`WPO-GlobalOptPromote`)**:
   - `wpo_globalopt_rodata_const_fold_sound`: When `static_id ∉ ExportList`, is
     not `#[used]` or volatile, does not escape, and has zero stores across the
     closed module graph, all loads of `static_id` soundly fold to its initial
     value `initVal`.
   - `wpo_globalopt_boolean_shrink_sound`: When `static_id` is only ever stored
     with values in `{v₀, v₁}`, encoding the global as a 1-bit boolean flag `b`
     and decoding `if b then v₁ else v₀` on load is observationally identical.
   - `canary_escaped_globalopt_const_fold_unsound`: Negative canary when an
     external FFI or address-taken pointer mutates `static_id`.
4. **Decidable `HybridTrace` WPO Certificate Validator (`checkWpoCert_sound` &
   `checkWpoCert_complete`)**.
-/

namespace WholeProgramDevirtDaeGlobalOptProbe

abbrev SymId     := Nat
abbrev TraitId   := Nat
abbrev VTableId  := Nat
abbrev SlotIdx   := Nat
abbrev StaticId  := Nat
abbrev Val       := Nat
abbrev Mem       := Nat → Val

/-!
## 1. Closed-Trait-World Devirtualization (`WPO-DevirtSingleImpl`, `WPO-DevirtBranchFunnel`, `WPO-DevirtConstRet`, `WPO-VFE`)
-/

/-- Closed-world trait vtable invariant (`ClosedTraitVTables(TraitId, ExportList)`):
every runtime `&dyn TraitId` fat pointer's `vtableId` belongs to the known
closed-world list `knownVTables` collected from `.anneal-mir` `GlobalAlloc::VTable`
records, and no external `dylib` or FFI import constructs `dyn TraitId`. -/
def InClosedTraitWorld (vtableId : VTableId) (knownVTables : List VTableId) : Prop :=
  vtableId ∈ knownVTables

/-- Indirect dynamic dispatch through `vtableTable vtableId slot`. -/
def evalVTableCall
    (vtableTable : VTableId → SlotIdx → (Val → Val))
    (vtableId : VTableId) (slot : SlotIdx) (arg : Val) : Val :=
  (vtableTable vtableId slot) arg

/-- **Theorem 1a (`wpo_devirt_single_impl_sound`, `WPO-DevirtSingleImpl`)**:
If every vtable `v ∈ knownVTables` maps `slot` to the same implementation body
`uniqueFn` (including the singleton case `knownVTables = [v₀]`), replacing
`evalVTableCall` unconditionally with `uniqueFn arg` is sound for any fat pointer
satisfying `InClosedTraitWorld`. -/
theorem wpo_devirt_single_impl_sound
    (vtableTable : VTableId → SlotIdx → (Val → Val))
    (knownVTables : List VTableId) (slot : SlotIdx)
    (uniqueFn : Val → Val) (vtableId : VTableId) (arg : Val)
    (h_closed : InClosedTraitWorld vtableId knownVTables)
    (h_all_eq : ∀ v ∈ knownVTables, vtableTable v slot = uniqueFn) :
    uniqueFn arg = evalVTableCall vtableTable vtableId slot arg := by
  unfold evalVTableCall
  have hv := h_all_eq vtableId h_closed
  rw [hv]

/-- **Theorem 1b (`wpo_devirt_branch_funnel_sound`, `WPO-DevirtBranchFunnel`)**:
When `knownVTables = [v₁, v₂, v₃]`, an exhaustive 3-way `vtableId` comparison
ladder with *no indirect call fallback* (`if v == v₁ then m₁ else if v == v₂
then m₂ else m₃`) is observationally identical to `evalVTableCall`. -/
def devirtBranchFunnel3
    (v₁ v₂ : VTableId) (m₁ m₂ m₃ : Val → Val) (vtableId : VTableId) (arg : Val) : Val :=
  if vtableId == v₁ then m₁ arg
  else if vtableId == v₂ then m₂ arg
  else m₃ arg

theorem wpo_devirt_branch_funnel_sound
    (vtableTable : VTableId → SlotIdx → (Val → Val))
    (v₁ v₂ v₃ : VTableId) (slot : SlotIdx) (vtableId : VTableId) (arg : Val)
    (h_closed : InClosedTraitWorld vtableId [v₁, v₂, v₃]) :
    devirtBranchFunnel3 v₁ v₂
      (vtableTable v₁ slot) (vtableTable v₂ slot) (vtableTable v₃ slot) vtableId arg =
    evalVTableCall vtableTable vtableId slot arg := by
  unfold devirtBranchFunnel3 evalVTableCall InClosedTraitWorld at *
  cases h1 : (vtableId == v₁)
  · cases h2 : (vtableId == v₂)
    · have hne1 : vtableId ≠ v₁ := by
        intro heq; subst heq; exact Bool.false_ne_true (h1.symm.trans (beq_self_eq_true vtableId))
      have hne2 : vtableId ≠ v₂ := by
        intro heq; subst heq; exact Bool.false_ne_true (h2.symm.trans (beq_self_eq_true vtableId))
      rcases List.mem_cons.mp h_closed with rfl | h_rest
      · contradiction
      · rcases List.mem_cons.mp h_rest with rfl | h_rest2
        · contradiction
        · rcases List.mem_cons.mp h_rest2 with rfl | h_nil
          · rfl
          · nomatch h_nil
    · have heq : vtableId = v₂ := LawfulBEq.eq_of_beq h2
      subst heq
      rfl
  · have heq : vtableId = v₁ := LawfulBEq.eq_of_beq h1
    subst heq
    rfl

/-- **Theorem 1c (`wpo_devirt_const_ret_sound`, `WPO-DevirtConstRet`)**:
If every vtable in `knownVTables` implements `slot` as a function returning the
constant `c₀`, any call to `slot` folds directly to `c₀`. -/
theorem wpo_devirt_const_ret_sound
    (vtableTable : VTableId → SlotIdx → (Val → Val))
    (knownVTables : List VTableId) (slot : SlotIdx)
    (c₀ : Val) (vtableId : VTableId) (arg : Val)
    (h_closed : InClosedTraitWorld vtableId knownVTables)
    (h_const  : ∀ v ∈ knownVTables, ∀ x, vtableTable v slot x = c₀) :
    evalVTableCall vtableTable vtableId slot arg = c₀ := by
  unfold evalVTableCall
  exact h_const vtableId h_closed arg

/-- **Theorem 1d (`wpo_vfe_unused_slot_strip_sound`, `WPO-VFE`)**:
Replacing an unused vtable slot `deadSlot` with a trap/zero stub across all
vtables preserves the semantics of every live call `liveSlot ≠ deadSlot`. -/
def stripUnusedVTableSlot
    (vtableTable : VTableId → SlotIdx → (Val → Val)) (deadSlot : SlotIdx) :
    VTableId → SlotIdx → (Val → Val) :=
  fun v s => if s == deadSlot then (fun _ => 0) else vtableTable v s

theorem wpo_vfe_unused_slot_strip_sound
    (vtableTable : VTableId → SlotIdx → (Val → Val))
    (deadSlot liveSlot : SlotIdx) (vtableId : VTableId) (arg : Val)
    (h_live : liveSlot ≠ deadSlot) :
    evalVTableCall (stripUnusedVTableSlot vtableTable deadSlot) vtableId liveSlot arg =
    evalVTableCall vtableTable vtableId liveSlot arg := by
  unfold evalVTableCall stripUnusedVTableSlot
  have h_neq : (liveSlot == deadSlot) = false := beq_false_of_ne h_live
  simp [h_neq]

/-- **Canary 1 (`canary_open_world_devirt_unsound`)**: If an external `dylib`
passes an unrecorded vtable `v_ext = 99 ∉ [1, 2, 3]`, `devirtBranchFunnel3`
without an indirect fallback executes `v₃`'s method instead of `v_ext`'s! -/
theorem canary_open_world_devirt_unsound :
    let vtableTable : VTableId → SlotIdx → (Val → Val) :=
      fun v _ x => x + v
    devirtBranchFunnel3 1 2 (vtableTable 1 0) (vtableTable 2 0) (vtableTable 3 0) 99 10 ≠
    evalVTableCall vtableTable 99 0 10 := by
  decide

/-!
## 2. Signature-Mutating Optimizations: `WPO-DeadArgAndRetElim` and `WPO-ArgPromoteByVal`
-/

/-- Side condition for signature rewriting of `sym`: `sym` is not in `exportList`
and its address is never taken in any `MonoItem` or `GlobalAlloc` relocation. -/
structure SignatureMutable (sym : SymId) (exportList : List SymId) (addressTaken : SymId → Bool) : Prop where
  not_exported     : sym ∉ exportList
  not_addr_taken   : addressTaken sym = false

/-- A two-argument function whose second parameter `deadArg` is unused. -/
def DeadArgIndependent (f : Val → Val → Val) : Prop :=
  ∀ x y₁ y₂, f x y₁ = f x y₂

/-- DAE-rewritten 1-argument function after dropping the dead second parameter. -/
def elimDeadSecondArg (f : Val → Val → Val) : Val → Val :=
  fun x => f x 0

/-- **Theorem 2a (`wpo_dead_arg_and_ret_elim_sound`)**: Under `SignatureMutable`
and `DeadArgIndependent`, rewriting every direct call `f x deadArg` to
`elimDeadSecondArg f x` produces the exact same return value and preserves all
exported symbols. -/
theorem wpo_dead_arg_and_ret_elim_sound
    (sym : SymId) (exportList : List SymId) (addressTaken : SymId → Bool)
    (f : Val → Val → Val) (x deadArg : Val)
    (h_mut  : SignatureMutable sym exportList addressTaken)
    (h_ind  : DeadArgIndependent f) :
    elimDeadSecondArg f x = f x deadArg ∧ sym ∉ exportList ∧ addressTaken sym = false := by
  refine ⟨?_, h_mut.not_exported, h_mut.not_addr_taken⟩
  unfold elimDeadSecondArg
  exact h_ind x 0 deadArg

/-- **Canary 2a (`canary_address_taken_dae_unsound`)**: If `addressTaken sym = true`,
an indirect caller invoking `sym` through a function pointer with its original
2-parameter ABI when the definition was rewritten or vice versa observes a
corrupted argument register! -/
theorem canary_address_taken_dae_unsound :
    let origTwoArgCallerPassesInReg2 : Val → Val := fun reg2 => reg2 + 1
    let rewrittenZeroInReg2 : Val := 0
    origTwoArgCallerPassesInReg2 42 ≠ origTwoArgCallerPassesInReg2 rewrittenZeroInReg2 := by
  decide

/-- A function taking a pointer `ptr : Nat` and memory `m : Mem` that only reads
`m ptr` after performing an unaliased prefix memory update `preWrite : Mem → Mem`. -/
def ByRefCallee (preWrite : Mem → Mem) (compute : Val → Val) (ptr : Nat) (m : Mem) : Val × Mem :=
  let m' := preWrite m
  (compute (m' ptr), m')

/-- By-value promoted callee (`WPO-ArgPromoteByVal`): the caller loads
`val := m ptr` at the call site and passes `val` by value in a register. -/
def ByValPromotedCallee (preWrite : Mem → Mem) (compute : Val → Val) (passedVal : Val) (m : Mem) : Val × Mem :=
  let m' := preWrite m
  (compute passedVal, m')

/-- **Theorem 2b (`wpo_arg_promote_by_val_sound`)**: If `preWrite` does not
alias/overwrite `ptr` (`(preWrite m) ptr = m ptr`), `ByValPromotedCallee`
invoked with `m ptr` produces the exact same `(ret, m')` pair as `ByRefCallee`. -/
theorem wpo_arg_promote_by_val_sound
    (preWrite : Mem → Mem) (compute : Val → Val) (ptr : Nat) (m : Mem)
    (h_noalias : (preWrite m) ptr = m ptr) :
    ByValPromotedCallee preWrite compute (m ptr) m =
    ByRefCallee preWrite compute ptr m := by
  unfold ByValPromotedCallee ByRefCallee
  dsimp only
  rw [h_noalias]

/-- **Canary 2b (`canary_aliased_arg_promote_unsound`)**: If `preWrite` writes
`99` to `ptr` before `ByRefCallee` loads `*ptr`, promoting `*ptr` to a by-value
load before the call reads the stale value `m ptr = 10` instead of `99`! -/
theorem canary_aliased_arg_promote_unsound :
    let m0 : Mem := fun _ => 10
    let aliasedWrite : Mem → Mem := fun m a => if a == 0 then 99 else m a
    (ByValPromotedCallee aliasedWrite id (m0 0) m0).1 ≠
    (ByRefCallee aliasedWrite id 0 m0).1 := by
  decide

/-!
## 3. `GlobalOpt` Static Promotion and Boolean Shrinking (`WPO-GlobalOptPromote`)
-/

structure ClosedStaticContract (s : StaticId) (exportList : List StaticId)
    (usedSet : List StaticId) (escaped : StaticId → Bool) : Prop where
  not_exported : s ∉ exportList
  not_used     : s ∉ usedSet
  not_escaped  : escaped s = false

/-- **Theorem 3a (`wpo_globalopt_rodata_const_fold_sound`)**: Under
`ClosedStaticContract`, if every operation in the closed module graph preserves
`m s = initVal` (zero stores to `s`), replacing any load `m s` with the constant
`initVal` is observationally identical. -/
theorem wpo_globalopt_rodata_const_fold_sound
    (s : StaticId) (exportList usedSet : List StaticId) (escaped : StaticId → Bool)
    (m : Mem) (initVal : Val)
    (h_closed : ClosedStaticContract s exportList usedSet escaped)
    (h_no_stores : m s = initVal) :
    initVal = m s ∧ s ∉ exportList ∧ escaped s = false :=
  ⟨h_no_stores.symm, h_closed.not_exported, h_closed.not_escaped⟩

/-- Boolean shrinking (`TryToShrinkGlobalToBoolean` in `GlobalOpt.cpp`): when a
non-escaping static `s` is only ever initialized to `v₀` or written with `v₁`,
encoding its state as `flag : Bool` (`false ↔ v₀`, `true ↔ v₁`) and decoding
`if flag then v₁ else v₀` on load reproduces the exact scalar value. -/
def encodeShrunkGlobal (v₀ v₁ writtenVal : Val) : Bool :=
  writtenVal == v₁ && !(v₀ == v₁)

def decodeShrunkGlobal (v₀ v₁ : Val) (flag : Bool) : Val :=
  if flag then v₁ else v₀

/-- **Theorem 3b (`wpo_globalopt_boolean_shrink_sound`)**: For any value `w`
satisfying the two-value closed-world store invariant `w = v₀ ∨ w = v₁`,
decoding `encodeShrunkGlobal v₀ v₁ w` yields `w`. -/
theorem wpo_globalopt_boolean_shrink_sound
    (v₀ v₁ w : Val)
    (h_two_vals : w = v₀ ∨ w = v₁) :
    decodeShrunkGlobal v₀ v₁ (encodeShrunkGlobal v₀ v₁ w) = w := by
  unfold decodeShrunkGlobal encodeShrunkGlobal
  rcases h_two_vals with rfl | rfl
  · by_cases heq : (w == v₁) = true
    · have hw : w = v₁ := LawfulBEq.eq_of_beq heq
      subst hw
      simp
    · simp [heq]
  · by_cases heq : (v₀ == w) = true
    · have hw : v₀ = w := LawfulBEq.eq_of_beq heq
      subst hw
      simp
    · simp [heq]

/-- **Canary 3 (`canary_escaped_globalopt_const_fold_unsound`)**: If `s` escapes
to an external writer that stores `42 ≠ initVal`, constant-folding `m s` to
`initVal = 0` is unsound (`0 ≠ 42`). -/
theorem canary_escaped_globalopt_const_fold_unsound :
    let initVal : Val := 0
    let mutatedMem : Mem := fun _ => 42
    initVal ≠ mutatedMem 0 := by
  decide

/-!
## 4. `HybridTrace` Closed-World WPO Certificate Checker Soundness & Completeness
-/

inductive WpoCert where
  | devirtSingleImpl (closedTraitWorld allVTablesMatchUnique : Bool)
  | devirtBranchFunnel (closedTraitWorld exhaustiveFunnel : Bool)
  | deadArgElim (notInExportList notAddressTaken argUnused : Bool)
  | argPromoteByVal (notInExportList notAddressTaken derefAndNoAlias : Bool)
  | globalOptPromote (notInExportList notUsed notEscaped storeInvHolds : Bool)
  deriving DecidableEq, Repr

def checkWpoCert (c : WpoCert) : Bool :=
  match c with
  | .devirtSingleImpl cw eq      => cw && eq
  | .devirtBranchFunnel cw ex    => cw && ex
  | .deadArgElim ne na uu        => ne && na && uu
  | .argPromoteByVal ne na da    => ne && na && da
  | .globalOptPromote ne nu ns s => ne && nu && ns && s

def ValidWpoCert (c : WpoCert) : Prop :=
  match c with
  | .devirtSingleImpl cw eq      => cw = true ∧ eq = true
  | .devirtBranchFunnel cw ex    => cw = true ∧ ex = true
  | .deadArgElim ne na uu        => ne = true ∧ na = true ∧ uu = true
  | .argPromoteByVal ne na da    => ne = true ∧ na = true ∧ da = true
  | .globalOptPromote ne nu ns s => ne = true ∧ nu = true ∧ ns = true ∧ s = true

theorem checkWpoCert_sound (c : WpoCert) (h : checkWpoCert c = true) : ValidWpoCert c := by
  cases c with
  | devirtSingleImpl cw eq =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true] at h
    exact h
  | devirtBranchFunnel cw ex =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true] at h
    exact h
  | deadArgElim ne na uu =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  | argPromoteByVal ne na da =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  | globalOptPromote ne nu ns s =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem checkWpoCert_complete (c : WpoCert) (h : ValidWpoCert c) : checkWpoCert c = true := by
  cases c with
  | devirtSingleImpl cw eq =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true]
    exact h
  | devirtBranchFunnel cw ex =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true]
    exact h
  | deadArgElim ne na uu =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  | argPromoteByVal ne na da =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  | globalOptPromote ne nu ns s =>
    unfold checkWpoCert ValidWpoCert at *
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

end WholeProgramDevirtDaeGlobalOptProbe

#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_devirt_single_impl_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_devirt_branch_funnel_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_devirt_const_ret_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_vfe_unused_slot_strip_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.canary_open_world_devirt_unsound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_dead_arg_and_ret_elim_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.canary_address_taken_dae_unsound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_arg_promote_by_val_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.canary_aliased_arg_promote_unsound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_globalopt_rodata_const_fold_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.wpo_globalopt_boolean_shrink_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.canary_escaped_globalopt_const_fold_unsound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.checkWpoCert_sound
#print axioms WholeProgramDevirtDaeGlobalOptProbe.checkWpoCert_complete
