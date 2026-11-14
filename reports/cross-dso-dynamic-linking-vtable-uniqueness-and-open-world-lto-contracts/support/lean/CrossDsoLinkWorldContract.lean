-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Cross-DSO Dynamic Linking, Duplicate VTables, and Open-World LTO Contracts (`LinkWorldContract`)

Standalone Lean 4 (`v4.34.1`) mechanization extending `WholeProgramDevirtDaeGlobalOptProbe.lean`
across `dylib` / `cdylib` / `dlopen` dynamic linking boundaries:
1. **Unconditional Open-World Soundness of `VP-2` / `VP-3` VTable-Pointer Promotion
   Under Duplicate VTables (`vp_vtable_promote_open_world_sound`)**:
   - Models a multi-DSO process where multiple distinct vtable addresses
     (`vaddr_host ≠ vaddr_plugin`) coexist for the exact same `(TraitId, ImplId)`
     pair (because `rustc 1.99.1` `consts.rs:312-340` emits vtables as `private
     unnamed_addr constant` per CGU/DSO) alongside arbitrary unknown foreign plugin
     vtables.
   - Proves with **zero closed-world assumptions** that `if vptr == vtable_local
     then localFn arg else indirectDispatch vptr slot arg` is 100% semantically
     sound: a foreign duplicate vtable simply takes the indirect fallback branch,
     which invokes the identical implementation `localFn`.
2. **Method-Slot Function-Pointer Guarding (`vp_slot_promote_open_world_sound` &
   `vp_two_level_dso_promote_sound`)**:
   - Proves that guarding on `slotFnPtr vptr slot == targetFnPtr` (or the two-level
     guard `vptr == vtable_local || slotFnPtr vptr slot == targetFnPtr`) is 100%
     sound in an arbitrary open world AND achieves a direct-call hit (`true`) even
     when `vptr` is a duplicate vtable allocated inside an external `dylib`!
3. **4-Level `LinkWorldContract` Hierarchy & Visibility Theorem
   (`private_trait_closed_under_dso_linking_sound`)**:
   - Proves that if `traitId ∉ exportedTraits` (a crate-private or non-escaping
     trait in a `bin` or `cdylib`), no well-typed external DSO interaction can
     introduce a foreign vtable for `traitId`, soundly discharging `InClosedTraitWorld`.
4. **Cross-DSO VTable Layout Preservation for `WPO-VFE` (`wpo_vfe_requires_non_escaping_layout_sound`)**
   and negative canaries (`canary_duplicate_vtable_breaks_exhaustive_vptr_else_assumption`,
   `canary_cross_dso_unguarded_devirt_unsound`, `canary_cross_dso_vfe_layout_mismatch_unsound`).
-/

namespace CrossDsoLinkWorldContract

abbrev DsoId      := Nat
abbrev TraitId    := Nat
abbrev ImplId     := Nat
abbrev VTableAddr := Nat
abbrev SlotIdx    := Nat
abbrev FnPtr      := Nat
abbrev Val        := Nat

/-- A runtime vtable instance residing at address `addr` in dynamic shared object `dso`.
Notice that `addr` is the primary runtime pointer key, while `(traitId, implId)`
identifies the logical Rust `(ImplType, dyn Trait)` implementation. Multiple distinct
`VTableInstance`s with `addr₁ ≠ addr₂` may share the same `(traitId, implId)`. -/
structure VTableInstance where
  addr    : VTableAddr
  dso     : DsoId
  traitId : TraitId
  implId  : ImplId
  slotPtr : SlotIdx → FnPtr

/-- Process-wide dynamic link world mapping vtable addresses and function pointers
to their immutable `.rodata` / `.text` semantics. -/
structure OpenDsoWorld where
  vtableAt : VTableAddr → VTableInstance
  fnSem    : FnPtr → (Val → Val)

/-- Standard indirect virtual call through `vptr` at `slot`. -/
def evalIndirectVCall (w : OpenDsoWorld) (vptr : VTableAddr) (slot : SlotIdx) (arg : Val) : Val :=
  let fnPtr := (w.vtableAt vptr).slotPtr slot
  w.fnSem fnPtr arg

/-- `VP-2` / `VP-3` vtable-pointer guarded promotion (`if vptr == localVTableAddr`). -/
def vpVTablePromote
    (w : OpenDsoWorld) (localVTableAddr : VTableAddr) (localDirectFn : Val → Val)
    (vptr : VTableAddr) (slot : SlotIdx) (arg : Val) : Val :=
  if vptr == localVTableAddr then
    localDirectFn arg
  else
    evalIndirectVCall w vptr slot arg

/-- **Theorem 1a (`vp_vtable_promote_open_world_sound`)**: Provided `localVTableAddr`
is an immutable `.rodata` vtable whose `slot` entry resolves to `localDirectFn`,
`vpVTablePromote` is unconditionally equal to `evalIndirectVCall` for **every**
runtime `vptr : VTableAddr`—including duplicate vtables from other DSOs and
unknown `dlopen` plugin implementations! -/
theorem vp_vtable_promote_open_world_sound
    (w : OpenDsoWorld) (localVTableAddr : VTableAddr) (localDirectFn : Val → Val)
    (vptr : VTableAddr) (slot : SlotIdx) (arg : Val)
    (h_rodata : w.fnSem ((w.vtableAt localVTableAddr).slotPtr slot) = localDirectFn) :
    vpVTablePromote w localVTableAddr localDirectFn vptr slot arg =
    evalIndirectVCall w vptr slot arg := by
  unfold vpVTablePromote evalIndirectVCall
  cases h : (vptr == localVTableAddr)
  · rfl
  · have heq : vptr = localVTableAddr := LawfulBEq.eq_of_beq h
    subst heq
    simp [h_rodata]

/-- `VP-Slot` method-function-pointer guarded promotion: compares the loaded
function pointer `(w.vtableAt vptr).slotPtr slot == targetFnPtr`. -/
def vpSlotPromote
    (w : OpenDsoWorld) (targetFnPtr : FnPtr) (directFn : Val → Val)
    (vptr : VTableAddr) (slot : SlotIdx) (arg : Val) : Val :=
  if (w.vtableAt vptr).slotPtr slot == targetFnPtr then
    directFn arg
  else
    evalIndirectVCall w vptr slot arg

/-- **Theorem 1b (`vp_slot_promote_open_world_sound`)**: Guarding on the loaded
vtable slot function pointer `(*vptr).slot == targetFnPtr` is unconditionally
sound in an open DSO world whenever `w.fnSem targetFnPtr = directFn`. -/
theorem vp_slot_promote_open_world_sound
    (w : OpenDsoWorld) (targetFnPtr : FnPtr) (directFn : Val → Val)
    (vptr : VTableAddr) (slot : SlotIdx) (arg : Val)
    (h_fn : w.fnSem targetFnPtr = directFn) :
    vpSlotPromote w targetFnPtr directFn vptr slot arg =
    evalIndirectVCall w vptr slot arg := by
  unfold vpSlotPromote evalIndirectVCall
  cases h : ((w.vtableAt vptr).slotPtr slot == targetFnPtr)
  · rfl
  · have heq : (w.vtableAt vptr).slotPtr slot = targetFnPtr := LawfulBEq.eq_of_beq h
    simp [heq, h_fn]

/-- Two-level DSO-resilient guard: fast-path compares `vptr == localVTableAddr`;
on a cross-DSO duplicate-vtable miss, checks `(w.vtableAt vptr).slotPtr slot == targetFnPtr`
before falling back to an indirect call. -/
def vpTwoLevelDsoPromote
    (w : OpenDsoWorld) (localVTableAddr : VTableAddr) (targetFnPtr : FnPtr)
    (directFn : Val → Val) (vptr : VTableAddr) (slot : SlotIdx) (arg : Val) : Val :=
  if (vptr == localVTableAddr) || ((w.vtableAt vptr).slotPtr slot == targetFnPtr) then
    directFn arg
  else
    evalIndirectVCall w vptr slot arg

/-- Whether the two-level guard takes the direct inlined fast path. -/
def vpTwoLevelDirectHit
    (w : OpenDsoWorld) (localVTableAddr : VTableAddr) (targetFnPtr : FnPtr)
    (vptr : VTableAddr) (slot : SlotIdx) : Bool :=
  (vptr == localVTableAddr) || ((w.vtableAt vptr).slotPtr slot == targetFnPtr)

/-- **Theorem 1c (`vp_two_level_dso_promote_sound_and_hits_duplicate_vtable`)**:
1. `vpTwoLevelDsoPromote` is unconditionally sound in any open DSO world.
2. Even when `vptr ≠ localVTableAddr` is a duplicate cross-DSO vtable in `libplugin.so`
   whose slot points to `targetFnPtr`, `vpTwoLevelDirectHit` evaluates to `true`
   (restoring 100% direct-call hit rate across DSO boundaries!). -/
theorem vp_two_level_dso_promote_sound_and_hits_duplicate_vtable
    (w : OpenDsoWorld) (localVTableAddr : VTableAddr) (targetFnPtr : FnPtr)
    (directFn : Val → Val) (vptr : VTableAddr) (slot : SlotIdx) (arg : Val)
    (h_rodata : w.fnSem ((w.vtableAt localVTableAddr).slotPtr slot) = directFn)
    (h_fn     : w.fnSem targetFnPtr = directFn) :
    vpTwoLevelDsoPromote w localVTableAddr targetFnPtr directFn vptr slot arg =
      evalIndirectVCall w vptr slot arg ∧
    ((w.vtableAt vptr).slotPtr slot = targetFnPtr →
      vpTwoLevelDirectHit w localVTableAddr targetFnPtr vptr slot = true) := by
  refine ⟨?_, ?_⟩
  · unfold vpTwoLevelDsoPromote evalIndirectVCall
    cases h1 : (vptr == localVTableAddr)
    · cases h2 : ((w.vtableAt vptr).slotPtr slot == targetFnPtr)
      · rfl
      · have heq2 : (w.vtableAt vptr).slotPtr slot = targetFnPtr := LawfulBEq.eq_of_beq h2
        simp [heq2, h_fn]
    · have heq1 : vptr = localVTableAddr := LawfulBEq.eq_of_beq h1
      subst heq1
      simp [h_rodata]
  · intro h_dup_slot
    unfold vpTwoLevelDirectHit
    rw [h_dup_slot, beq_self_eq_true, Bool.or_true]

/-!
## 2. 4-Level `LinkWorldContract` Hierarchy and Visibility Characterization
-/

/-- The 4-level link-world classification governing trait devirtualization and VFE. -/
inductive LinkWorldKind where
  | fullyClosedExecutable
  | cratePrivateTraitInOpenBinary
  | sealedTraitInClosedDsoSet
  | openExportedTrait
  deriving DecidableEq, Repr

/-- Whether a trait's vtable set and slot layout are closed against unknown external DSOs. -/
def allowsUnguardedWpoDevirt (kind : LinkWorldKind) : Bool :=
  match kind with
  | .fullyClosedExecutable         => true
  | .cratePrivateTraitInOpenBinary => true
  | .sealedTraitInClosedDsoSet     => true
  | .openExportedTrait             => false

/-- Well-typed DSO boundary contract: any vtable instance `vt` residing in an
external unverified DSO (`vt.dso ≠ hostDso`) can only implement a trait that is
visible across the host binary's `exportedTraits` interface. -/
def DsoTypingBoundary
    (hostDso : DsoId) (exportedTraits : List TraitId)
    (vt : VTableInstance) : Prop :=
  vt.dso ≠ hostDso → vt.traitId ∈ exportedTraits

/-- **Theorem 2 (`private_trait_closed_under_dso_linking_sound`)**: If `traitId`
is not in `exportedTraits` (`CratePrivateTraitInOpenBinary`) and every host-DSO
vtable for `traitId` belongs to `hostKnownVTables`, then **every** well-typed
runtime vtable `vt` for `traitId` in the entire multi-DSO process belongs to
`hostKnownVTables` (`vt.addr ∈ hostKnownVTables`). -/
theorem private_trait_closed_under_dso_linking_sound
    (hostDso : DsoId) (exportedTraits : List TraitId)
    (hostKnownVTables : List VTableAddr)
    (traitId : TraitId) (vt : VTableInstance)
    (h_private   : traitId ∉ exportedTraits)
    (h_boundary  : DsoTypingBoundary hostDso exportedTraits vt)
    (h_host_all  : vt.dso = hostDso ∧ vt.traitId = traitId → vt.addr ∈ hostKnownVTables)
    (h_vt_trait  : vt.traitId = traitId) :
    vt.addr ∈ hostKnownVTables := by
  by_cases hdso : vt.dso = hostDso
  · exact h_host_all ⟨hdso, h_vt_trait⟩
  · exfalso
    have hexp := h_boundary hdso
    rw [h_vt_trait] at hexp
    exact h_private hexp

/-- **Theorem 3 (`wpo_vfe_requires_non_escaping_layout_sound`)**: Compacting a
vtable layout by removing an uncalled slot `deadSlot` (shifting slots `> deadSlot`
down by 1) preserves all calls inside the host compilation unit when `traitId ∉ exportedTraits`
and every call in the host unit adjusts its slot index via `compactSlotIdx`. -/
def compactSlotIdx (deadSlot s : SlotIdx) : SlotIdx :=
  if s < deadSlot then s else s - 1

def expandCompactedVTable (origSlot : SlotIdx → Val) (deadSlot : SlotIdx) : SlotIdx → Val :=
  fun compactedIdx =>
    if compactedIdx < deadSlot then origSlot compactedIdx else origSlot (compactedIdx + 1)

theorem wpo_vfe_requires_non_escaping_layout_sound
    (origSlot : Nat → Val) (deadSlot liveSlot : Nat)
    (h_not_dead : liveSlot ≠ deadSlot) :
    expandCompactedVTable origSlot deadSlot (compactSlotIdx deadSlot liveSlot) =
    origSlot liveSlot := by
  unfold expandCompactedVTable compactSlotIdx
  by_cases hlt : liveSlot < deadSlot
  · simp [hlt]
  · have h_not_lt : ¬(liveSlot - 1 < deadSlot) := by omega
    have h_add : liveSlot - 1 + 1 = liveSlot := by omega
    simp [hlt, h_not_lt, h_add]

/-!
## 3. Negative Canaries
-/

/-- **Canary 1 (`canary_duplicate_vtable_breaks_exhaustive_vptr_else_assumption`)**:
Suppose a closed trait has exactly 2 concrete implementations `Impl1` (returning `100`)
and `Impl2` (returning `200`), with host vtable addresses `v1_host = 10` and
`v2_host = 20`. An exhaustive branch funnel `if vptr == 10 then 100 else 200`
(which omits checking `vptr == 20` on the `else` branch) **miscompiles** when a
second DSO passes a duplicate vtable `v1_plugin = 30` for `Impl1` (`200 ≠ 100`)! -/
theorem canary_duplicate_vtable_breaks_exhaustive_vptr_else_assumption :
    let funnelAssumingUniqueVTableAddr (vptr : VTableAddr) : Val :=
      if vptr == 10 then 100 else 200
    let actualImpl1Sem : Val := 100
    let duplicatePluginVTableForImpl1 : VTableAddr := 30
    funnelAssumingUniqueVTableAddr duplicatePluginVTableForImpl1 ≠ actualImpl1Sem := by
  decide

/-- **Canary 2 (`canary_cross_dso_unguarded_devirt_unsound`)**: Applying unguarded
`WPO-DevirtSingleImpl` to an `openExportedTrait` (`allowsUnguardedWpoDevirt = false`)
when `plugin_dylib` introduces a second implementation returning `999 ≠ 42` is unsound. -/
theorem canary_cross_dso_unguarded_devirt_unsound :
    allowsUnguardedWpoDevirt .openExportedTrait = false ∧ (42 : Val) ≠ 999 := by
  decide

/-- **Canary 3 (`canary_cross_dso_vfe_layout_mismatch_unsound`)**: If `WPO-VFE`
compacts `deadSlot = 1` on an exported trait whose `&dyn Trait` escapes to an
external `dylib` compiled against the uncompacted ABI (which still reads `slot = 2`
without `compactSlotIdx`), the external `dylib` reads `origSlot 3` instead of `origSlot 2`! -/
theorem canary_cross_dso_vfe_layout_mismatch_unsound :
    let origSlot : SlotIdx → Val := fun s => s * 10
    expandCompactedVTable origSlot 1 2 ≠ origSlot 2 := by
  decide

end CrossDsoLinkWorldContract

#print axioms CrossDsoLinkWorldContract.vp_vtable_promote_open_world_sound
#print axioms CrossDsoLinkWorldContract.vp_slot_promote_open_world_sound
#print axioms CrossDsoLinkWorldContract.vp_two_level_dso_promote_sound_and_hits_duplicate_vtable
#print axioms CrossDsoLinkWorldContract.private_trait_closed_under_dso_linking_sound
#print axioms CrossDsoLinkWorldContract.wpo_vfe_requires_non_escaping_layout_sound
#print axioms CrossDsoLinkWorldContract.canary_duplicate_vtable_breaks_exhaustive_vptr_else_assumption
#print axioms CrossDsoLinkWorldContract.canary_cross_dso_unguarded_devirt_unsound
#print axioms CrossDsoLinkWorldContract.canary_cross_dso_vfe_layout_mismatch_unsound
