/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Round 2 — Track 3 Mechanization Probe: Public vs. Private Stack Frame
# Partitioning (`fe_stack_data`), `PNVI-ae-udi` Guard Slots, Sub-Register
# Family Aliasing, Callee-Saved Protocol, and Indirect-Call Stack Bounds

This standalone Lean 4.34.1 module resolves all five open questions from Round 1
Track 4 (Questions 1–5) and Round 1 Track 7 (Question 1):

1. **Public Address-Taken Stack Sub-Block (`fe_stack_data`) vs. Private Spill /
   Callee-Save / Return-Address Slots (`Stackingproof.v` Bridge to Phase 2–4
   Memory, Track 4 Question 2 & Track 7 Question 1):**
   - Partitions each activation frame `[sp, sp + frameSize)` into a **public
     address-taken region** `[sp + ofsPublic, sp + ofsPublic + publicBytes)`
     (holding address-taken MIR locals indexed by `(AllocId.stackLocal frameId k,
     byteOfs)`), an **unexposed guard region** (`guardBytes ≥ 1`), and **private
     compiler-managed regions** (`[sp + ofsSpills, sp + ofsSpills + spillBytes)`
     and `[sp + ofsSaved, sp + frameSize)`) holding `regalloc2` spill slots,
     saved callee-saved registers, and the return address `RA`.
   - Proves `public_store_preserves_private_spills_and_saved_regs`: any byte
     store through a provenance-valid user pointer (`p.prov = .stackLocal
     frameId k` and `p.offset < localSize k`) in Phase 1/2 maps into
     `[sp + ofsPublic, sp + ofsPublic + publicBytes)` in Phase 4 flat RAM and
     cannot alias or overwrite any private spill slot, saved callee-saved
     register, or return address.
   - Proves the negative canary `canary_unbounded_ptr_offset_corrupts_spill`:
     if a pointer escapes `publicBytes` into `[ofsSpills, ofsSpills +
     spillBytes)`, it corrupts a live spill slot.
   - Proves `canary_adjacent_exposed_allocs_ambiguous_at_one_past_end` and
     `guard_byte_eliminates_pnvi_boundary_ambiguity`: under `PNVI-ae-udi`
     (`ptr::with_exposed_provenance`), placing a 1-byte unexposed guard slot
     between allocations (and between `publicBytes` and `ofsSpills`) prevents
     one-past-the-end integer casts (`base + size`) from ambiguously resolving
     to an adjacent allocation or touching private spill slots.

2. **Sub-Register Aliasing (`rax`/`eax`/`ax`/`al`) & Callee-Saved Register
   Tokens in `checkRegAlloc` (Track 4 Questions 1, 3, & 5):**
   - Models architectural 64-bit register families `PReg` with sub-register
     widths `RegWidth` (`w8 | w16 | w32 | w64`) and x86-64/AArch64 sub-register
     write semantics (`writeSubReg64`, where `w8`/`w16` merge into the low
     bits and `w32` zero-extends).
   - Extends `CheckerState` to width-tagged bindings `(Allocation, RegWidth,
     VReg)` where writing any sub-register `(preg, wWrite)` kills all existing
     `(preg, wOld, vreg)` bindings in that `preg` family, while reading
     `(preg, wRead)` requires an active binding with `wBound == wRead` (or an
     explicit `zext` instruction).
   - Models callee-saved register preservation via entry/exit virtual-register
     tokens `calleeSaveToken i` seeded in `blockIn[entry]`, caller-saved
     clobbers on `Call` instructions, and `checkCalleeSavedAtReturn` at `ret`
     terminators.
   - Proves `subreg_checkRegAlloc_sound`,
     `callee_saved_preserved_of_checkRegAlloc`, and executable canaries
     (`canary_subreg_partial_write_clobbers_64bit`,
     `canary_subreg_width_mismatch_rejected`,
     `canary_missing_callee_save_restore_rejected`, and
     `canary_callee_save_spilled_and_restored_accepted`).

3. **Discharging Quantitative Stack Bounds (`A-BEH-07`) Across Indirect Calls
   (`dyn Trait` / `fn` Pointers, Track 4 Question 4):**
   - Mechanizes **Method A (Static VTable / `FnPtr` Contract Bound
     `wcetStack`)** and proves `indirect_call_static_contract_no_overflow`.
   - Mechanizes **Method B (Dynamic Prologue `stackLimit` Register / TLS
     Check)** and proves `dynamic_stack_check_preserves_limit` across arbitrary
     multi-hop indirect call sequences, plus the negative canary
     `canary_indirect_call_exceeding_contract_caught`.
-/

namespace Anneal.Round2Track3

-- ============================================================================
-- Part 1: Public Address-Taken Stack Sub-Block (`fe_stack_data`) vs. Private
-- Spill / Callee-Save / RA Slots & `PNVI-ae-udi` Guard Slot
-- ============================================================================

/-- Stack-frame byte permission in Stack-Aware CompCert (`common/StackADT.v:30-33`).
`public_` bytes lie in `[ofsPublic, ofsPublic + publicBytes)` (`fe_stack_data`)
and may be referenced by user pointers; `private_` bytes hold compiler-managed
spill slots, saved callee-saved registers, unexposed guard padding, and the
return address `RA`. -/
inductive StackPerm where
  | public_
  | private_
  deriving DecidableEq, Repr

/-- Allocation provenance identifier bridging Phase 1/2 (`Trusted/MirSemantics`)
and Phase 3/4 (`Stacking`). Each address-taken MIR local `k` in activation
frame `frameId` has a distinct `AllocId.stackLocal frameId k`. -/
inductive FrameAllocId where
  | stackLocal (frameId : Nat) (localIdx : Nat)
  | heap (id : Nat)
  | staticSeg (id : Nat)
  deriving DecidableEq, Repr

/-- A user-level pointer in Phase 1/2 carrying provenance `prov` and a byte
offset `offset` relative to that allocation's base. -/
structure UserPtr where
  prov : FrameAllocId
  offset : Nat
  deriving DecidableEq, Repr

/-- Partitioned activation frame layout for a compiled function, synthesizing
CompCert (`x86/Stacklayout.v:36-62`, `riscV/Stacklayout.v:35-60`,
`backend/Stackingproof.v:371-382`) and Stack-Aware CompCert
(`common/StackADT.v:85-93`, `backend/Stackingproof.v:113-119`):
- `[ofsPublic, ofsPublic + publicBytes)`: public address-taken MIR locals
  (`fe_stack_data`), where local `k < numPublicLocals` occupies
  `[ofsPublic + localRelOffset k, ofsPublic + localRelOffset k + localSize k)`.
- `[ofsPublic + publicBytes, ofsSpills)`: unexposed guard bytes (`guardBytes ≥ 1`)
  separating address-taken locals from private compiler slots.
- `[ofsSpills, ofsSpills + spillBytes)`: private `regalloc2` spill slots.
- `[ofsSaved, ofsSaved + savedBytes)`: private saved callee-saved registers.
- `[ofsRetAddr, ofsRetAddr + 8)`: private saved return address `RA`. -/
structure PartitionedFrameLayout where
  numPublicLocals : Nat
  localRelOffset : Nat → Nat
  localSize : Nat → Nat
  ofsPublic : Nat
  publicBytes : Nat
  guardBytes : Nat
  ofsSpills : Nat
  spillBytes : Nat
  ofsSaved : Nat
  savedBytes : Nat
  ofsRetAddr : Nat
  frameSize : Nat
  /-- Every address-taken local `k < numPublicLocals` fits entirely inside the
  public sub-block `[0, publicBytes)`. -/
  localsWithinPublic :
    ∀ k, k < numPublicLocals → localRelOffset k + localSize k ≤ publicBytes
  /-- Distinct address-taken locals within the public sub-block are pairwise
  disjoint. -/
  localsDisjoint :
    ∀ k1 k2 o1 o2,
      k1 < numPublicLocals →
      k2 < numPublicLocals →
      k1 ≠ k2 →
      o1 < localSize k1 →
      o2 < localSize k2 →
      localRelOffset k1 + o1 ≠ localRelOffset k2 + o2
  /-- At least 1 unexposed guard byte separates the public sub-block from the
  private spill region (`PNVI-ae-udi` one-past-the-end protection). -/
  guardPositive : 1 ≤ guardBytes
  /-- Ordered non-overlapping region layout inside `[0, frameSize)`. -/
  publicToSpills : ofsPublic + publicBytes + guardBytes ≤ ofsSpills
  spillsToSaved : ofsSpills + spillBytes ≤ ofsSaved
  savedToRetAddr : ofsSaved + savedBytes ≤ ofsRetAddr
  retAddrToEnd : ofsRetAddr + 8 ≤ frameSize

/-- Permission classification of frame offset `ofs` relative to `sp`, matching
`frame_info_of_size_and_pubrange` in `common/StackADT.v:85-93`. -/
def PartitionedFrameLayout.framePerm (fl : PartitionedFrameLayout)
    (ofs : Nat) : StackPerm :=
  if fl.ofsPublic ≤ ofs ∧ ofs < fl.ofsPublic + fl.publicBytes then
    .public_
  else
    .private_

/-- Phase 1/2 provenance-and-bounds validity for a dereference of user pointer
`p` targeting an address-taken stack local in frame `activeFrameId`. -/
def inBoundsStackLocal (fl : PartitionedFrameLayout) (activeFrameId : Nat)
    (p : UserPtr) : Prop :=
  ∃ k,
    k < fl.numPublicLocals ∧
    p.prov = .stackLocal activeFrameId k ∧
    p.offset < fl.localSize k

/-- Concrete Phase 4 flat hardware RAM address for byte offset `ofs` inside
address-taken local `k` of a frame rooted at hardware stack pointer `sp`.
Corresponds to CompCert's memory injection `j sp = Some (sp', fe_stack_data fe)`
composed with the local's sub-block offset. -/
def localByteFlatAddr (fl : PartitionedFrameLayout) (sp k ofs : Nat) : Nat :=
  sp + fl.ofsPublic + fl.localRelOffset k + ofs

/-- Functional byte update in Phase 4 flat hardware RAM. -/
def writeFlatByte (ram : Nat → UInt8) (addr : Nat) (val : UInt8) :
    Nat → UInt8 :=
  fun a => if a = addr then val else ram a

/-- Agreement between abstract compiler-private frame state (spill bytes,
saved callee-saved register bytes, and return-address bytes) and Phase 4 flat
hardware RAM at stack pointer `sp`. Mirrors `frame_contents_1` in
`backend/Stackingproof.v:371-376`. -/
def PrivateSpillAndSavedInvariant (fl : PartitionedFrameLayout) (sp : Nat)
    (spillSlotBytes : Nat → UInt8) (savedRegBytes : Nat → UInt8)
    (retAddrBytes : Nat → UInt8) (ram : Nat → UInt8) : Prop :=
  (∀ sOfs, sOfs < fl.spillBytes →
    ram (sp + fl.ofsSpills + sOfs) = spillSlotBytes sOfs) ∧
  (∀ cOfs, cOfs < fl.savedBytes →
    ram (sp + fl.ofsSaved + cOfs) = savedRegBytes cOfs) ∧
  (∀ rOfs, rOfs < 8 →
    ram (sp + fl.ofsRetAddr + rOfs) = retAddrBytes rOfs)

/-- **Lemma (`inBounds_local_maps_to_public_region`):** Any in-bounds byte
offset `ofs < fl.localSize k` of an address-taken local `k < fl.numPublicLocals`
maps strictly inside `[sp + fl.ofsPublic, sp + fl.ofsPublic + fl.publicBytes)`
and carries `.public_` permission in `FrameADT`. -/
theorem inBounds_local_maps_to_public_region (fl : PartitionedFrameLayout)
    (sp k ofs : Nat) (hk : k < fl.numPublicLocals)
    (hOfs : ofs < fl.localSize k) :
    let addr := localByteFlatAddr fl sp k ofs
    sp + fl.ofsPublic ≤ addr ∧
    addr < sp + fl.ofsPublic + fl.publicBytes ∧
    fl.framePerm (addr - sp) = .public_ := by
  have hSub := fl.localsWithinPublic k hk
  dsimp only
  unfold localByteFlatAddr PartitionedFrameLayout.framePerm
  refine ⟨by omega, by omega, ?_⟩
  have hCond :
      fl.ofsPublic ≤ sp + fl.ofsPublic + fl.localRelOffset k + ofs - sp ∧
      sp + fl.ofsPublic + fl.localRelOffset k + ofs - sp <
        fl.ofsPublic + fl.publicBytes := by omega
  simp [hCond]

/-- **Theorem 1a (`public_store_preserves_private_spills_and_saved_regs`):**
Any byte store through a provenance-valid user pointer `p` (`p.prov =
.stackLocal activeFrameId k` and `p.offset < fl.localSize k`) in Phase 1/2:
1. Maps to a `.public_` address inside `[sp + ofsPublic, sp + ofsPublic + publicBytes)`,
2. Preserves `PrivateSpillAndSavedInvariant` (leaving all `regalloc2` spill
   slots, saved callee-saved registers, and the return address `RA` untouched),
3. Leaves all memory outside the active frame `[sp, sp + fl.frameSize)`
   (including caller frames and static/heap segments) pointwise unchanged, and
4. Leaves all other address-taken locals `k' ≠ k` in the same frame unchanged. -/
theorem public_store_preserves_private_spills_and_saved_regs
    (fl : PartitionedFrameLayout) (activeFrameId sp : Nat)
    (spillSlotBytes savedRegBytes retAddrBytes : Nat → UInt8)
    (ram : Nat → UInt8) (p : UserPtr) (k : Nat) (val : UInt8)
    (hk : k < fl.numPublicLocals)
    (hProv : p.prov = .stackLocal activeFrameId k)
    (hOfs : p.offset < fl.localSize k)
    (hPriv : PrivateSpillAndSavedInvariant fl sp
               spillSlotBytes savedRegBytes retAddrBytes ram) :
    let addr := localByteFlatAddr fl sp k p.offset
    let ram' := writeFlatByte ram addr val
    fl.framePerm (addr - sp) = .public_ ∧
    PrivateSpillAndSavedInvariant fl sp
      spillSlotBytes savedRegBytes retAddrBytes ram' ∧
    (∀ extAddr, (extAddr < sp ∨ sp + fl.frameSize ≤ extAddr) →
      ram' extAddr = ram extAddr) ∧
    (∀ k' ofs', k' < fl.numPublicLocals → k' ≠ k → ofs' < fl.localSize k' →
      ram' (localByteFlatAddr fl sp k' ofs') =
        ram (localByteFlatAddr fl sp k' ofs')) := by
  have _ := hProv
  have hPubBound := fl.localsWithinPublic k hk
  have hG := fl.guardPositive
  have h1 := fl.publicToSpills
  have h2 := fl.spillsToSaved
  have h3 := fl.savedToRetAddr
  have h4 := fl.retAddrToEnd
  have hPubRegion := inBounds_local_maps_to_public_region fl sp k p.offset hk hOfs
  dsimp only at hPubRegion ⊢
  refine ⟨hPubRegion.2.2, ?_, ?_, ?_⟩
  · rcases hPriv with ⟨hSpills, hSaved, hRet⟩
    refine ⟨?_, ?_, ?_⟩
    · intro sOfs hsOfs
      have hNe : sp + fl.ofsSpills + sOfs ≠
          localByteFlatAddr fl sp k p.offset := by
        unfold localByteFlatAddr; omega
      simp [writeFlatByte, hNe, hSpills sOfs hsOfs]
    · intro cOfs hcOfs
      have hNe : sp + fl.ofsSaved + cOfs ≠
          localByteFlatAddr fl sp k p.offset := by
        unfold localByteFlatAddr; omega
      simp [writeFlatByte, hNe, hSaved cOfs hcOfs]
    · intro rOfs hrOfs
      have hNe : sp + fl.ofsRetAddr + rOfs ≠
          localByteFlatAddr fl sp k p.offset := by
        unfold localByteFlatAddr; omega
      simp [writeFlatByte, hNe, hRet rOfs hrOfs]
  · intro extAddr hOut
    have hNe : extAddr ≠ localByteFlatAddr fl sp k p.offset := by
      unfold localByteFlatAddr; omega
    simp [writeFlatByte, hNe]
  · intro k' ofs' hk' hNeK hOfs'
    have hRelNe := fl.localsDisjoint k' k ofs' p.offset hk' hk hNeK hOfs' hOfs
    have hAddrNe : localByteFlatAddr fl sp k' ofs' ≠
        localByteFlatAddr fl sp k p.offset := by
      unfold localByteFlatAddr; omega
    simp [writeFlatByte, hAddrNe]

/-- Concrete sample `PartitionedFrameLayout` with:
- 1 address-taken local of size 16 bytes at `[0, 16)` (`publicBytes = 16`),
- 8 guard bytes at `[16, 24)`,
- 2 private 8-byte spill slots at `[24, 40)` (`ofsSpills = 24, spillBytes = 16`),
- 2 saved callee-saved registers at `[40, 56)` (`ofsSaved = 40, savedBytes = 16`),
- 1 return address slot at `[56, 64)` (`ofsRetAddr = 56, frameSize = 64`). -/
def samplePartitionedLayout : PartitionedFrameLayout where
  numPublicLocals := 1
  localRelOffset := fun _ => 0
  localSize := fun _ => 16
  ofsPublic := 0
  publicBytes := 16
  guardBytes := 8
  ofsSpills := 24
  spillBytes := 16
  ofsSaved := 40
  savedBytes := 16
  ofsRetAddr := 56
  frameSize := 64
  localsWithinPublic := by intro k hk; omega
  localsDisjoint := by intro k1 k2 _ _ hk1 hk2 hNe; omega
  guardPositive := by decide
  publicToSpills := by decide
  spillsToSaved := by decide
  savedToRetAddr := by decide
  retAddrToEnd := by decide

/-- **Theorem 1b (`canary_unbounded_ptr_offset_corrupts_spill` — Negative Canary):**
If a user pointer to address-taken local 0 escapes its Phase 1/2 bound
(`localSize 0 = 16`) with an unchecked offset `badOffset = 24`, the resulting
Phase 4 flat store lands inside `[ofsSpills, ofsSpills + spillBytes)` and
overwrites private spill slot 0 (`0xAA → 0xFF`), violating
`PrivateSpillAndSavedInvariant`. -/
theorem canary_unbounded_ptr_offset_corrupts_spill :
    let fl := samplePartitionedLayout
    let sp := 1000
    let spillSlotBytes : Nat → UInt8 := fun _ => 0xAA
    let savedRegBytes : Nat → UInt8 := fun _ => 0xBB
    let retAddrBytes : Nat → UInt8 := fun _ => 0xCC
    let ram : Nat → UInt8 := fun addr =>
      if sp + fl.ofsSpills ≤ addr ∧ addr < sp + fl.ofsSpills + fl.spillBytes then
        0xAA
      else if sp + fl.ofsSaved ≤ addr ∧ addr < sp + fl.ofsSaved + fl.savedBytes then
        0xBB
      else if sp + fl.ofsRetAddr ≤ addr ∧ addr < sp + fl.ofsRetAddr + 8 then
        0xCC
      else
        0x00
    let badOffset := 24
    let badAddr := localByteFlatAddr fl sp 0 badOffset
    let ramAfterBadWrite := writeFlatByte ram badAddr 0xFF
    PrivateSpillAndSavedInvariant fl sp
      spillSlotBytes savedRegBytes retAddrBytes ram ∧
    ¬ PrivateSpillAndSavedInvariant fl sp
        spillSlotBytes savedRegBytes retAddrBytes ramAfterBadWrite := by
  intro fl sp spillSlotBytes savedRegBytes retAddrBytes ram badOffset badAddr
    ramAfterBadWrite
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro sOfs hsOfs
      have h1 : sp + fl.ofsSpills ≤ sp + fl.ofsSpills + sOfs ∧
          sp + fl.ofsSpills + sOfs < sp + fl.ofsSpills + fl.spillBytes := by
        dsimp [fl, sp, samplePartitionedLayout] at hsOfs ⊢; omega
      simp [ram, spillSlotBytes, h1]
    · intro cOfs hcOfs
      have hNot1 : ¬ (sp + fl.ofsSpills ≤ sp + fl.ofsSaved + cOfs ∧
          sp + fl.ofsSaved + cOfs < sp + fl.ofsSpills + fl.spillBytes) := by
        dsimp [fl, sp, samplePartitionedLayout] at hcOfs ⊢; omega
      have h2 : sp + fl.ofsSaved ≤ sp + fl.ofsSaved + cOfs ∧
          sp + fl.ofsSaved + cOfs < sp + fl.ofsSaved + fl.savedBytes := by
        dsimp [fl, sp, samplePartitionedLayout] at hcOfs ⊢; omega
      simp [ram, savedRegBytes, hNot1, h2]
    · intro rOfs hrOfs
      have hNot1 : ¬ (sp + fl.ofsSpills ≤ sp + fl.ofsRetAddr + rOfs ∧
          sp + fl.ofsRetAddr + rOfs < sp + fl.ofsSpills + fl.spillBytes) := by
        dsimp [fl, sp, samplePartitionedLayout] at hrOfs ⊢; omega
      have hNot2 : ¬ (sp + fl.ofsSaved ≤ sp + fl.ofsRetAddr + rOfs ∧
          sp + fl.ofsRetAddr + rOfs < sp + fl.ofsSaved + fl.savedBytes) := by
        dsimp [fl, sp, samplePartitionedLayout] at hrOfs ⊢; omega
      have h3 : sp + fl.ofsRetAddr ≤ sp + fl.ofsRetAddr + rOfs ∧
          sp + fl.ofsRetAddr + rOfs < sp + fl.ofsRetAddr + 8 := by
        dsimp [fl, sp, samplePartitionedLayout] at hrOfs ⊢; omega
      simp [ram, retAddrBytes, hNot1, hNot2, h3]
  · intro hPrivAfter
    have hSpill0 := hPrivAfter.1 0 (by decide)
    have hEq : ramAfterBadWrite (sp + fl.ofsSpills + 0) = 0xFF := rfl
    rw [hEq] at hSpill0
    nomatch hSpill0

/-! ### Resolving Track 7 Question 1: `PNVI-ae-udi` Exposed Provenance & 1-Byte Guard Padding -/

/-- Under `PNVI-ae-udi` (and Rust's `ptr::with_exposed_provenance`), an integer
address `addr` can be resolved back to an exposed allocation `a` whenever `a`
has been exposed and `addr` lies in the closed interval
`[base a, base a + size a]` (which includes the one-past-the-end address
`base a + size a`). -/
structure ExposedAllocLayout where
  base : Nat → Nat
  size : Nat → Nat
  exposed : Nat → Bool

/-- `addr` is within the `PNVI-ae-udi` closed footprint `[base a, base a + size a]`
of an exposed allocation `a`. -/
def inExposedFootprint (L : ExposedAllocLayout) (a addr : Nat) : Prop :=
  L.exposed a = true ∧ L.base a ≤ addr ∧ addr ≤ L.base a + L.size a

/-- **Theorem 1c (`canary_adjacent_exposed_allocs_ambiguous_at_one_past_end`):**
If two exposed allocations `a1 = 0` (`[100, 116)`) and `a2 = 1` (`[116, 132)`)
are placed immediately adjacent with zero padding (`base 1 = base 0 + size 0`),
the boundary integer address `addr = 116` lies in the closed footprint of
**both** allocations simultaneously, forcing angelic nondeterminism in
`with_exposed_provenance(116)`. -/
theorem canary_adjacent_exposed_allocs_ambiguous_at_one_past_end :
    let L : ExposedAllocLayout := {
      base := fun a => if a = 0 then 100 else 116
      size := fun _ => 16
      exposed := fun a => a == 0 || a == 1
    }
    inExposedFootprint L 0 116 ∧ inExposedFootprint L 1 116 := by
  intro L
  constructor <;> refine ⟨rfl, by decide, by decide⟩

/-- Guard-separated allocation layout: every pair of distinct exposed
allocations is separated by at least 1 unexposed guard byte
(`base a1 + size a1 < base a2` or `base a2 + size a2 < base a1`). -/
def GuardSeparated (L : ExposedAllocLayout) : Prop :=
  ∀ a1 a2,
    L.exposed a1 = true →
    L.exposed a2 = true →
    a1 ≠ a2 →
    L.base a1 + L.size a1 + 1 ≤ L.base a2 ∨
    L.base a2 + L.size a2 + 1 ≤ L.base a1

/-- **Theorem 1d (`guard_byte_eliminates_pnvi_boundary_ambiguity`):**
1. Under `GuardSeparated L` (at least 1 unexposed guard byte between exposed
   allocations), `with_exposed_provenance(addr)` is **unique and deterministic**:
   any integer address `addr` belongs to the closed `[base a, base a + size a]`
   footprint of at most one exposed allocation (`a1 = a2`).
2. In `PartitionedFrameLayout`, because `guardBytes ≥ 1` separates `publicBytes`
   from `ofsSpills`, even a one-past-the-end address `ofs ≤ fl.localSize k` of
   any public local `k` lies strictly below `sp + fl.ofsSpills` and cannot reach
   the start of the private spill area. -/
theorem guard_byte_eliminates_pnvi_boundary_ambiguity
    (L : ExposedAllocLayout) (hGuard : GuardSeparated L) :
    (∀ addr a1 a2,
      inExposedFootprint L a1 addr →
      inExposedFootprint L a2 addr →
      a1 = a2) ∧
    (∀ (fl : PartitionedFrameLayout) sp k ofs,
      k < fl.numPublicLocals →
      ofs ≤ fl.localSize k →
      localByteFlatAddr fl sp k ofs < sp + fl.ofsSpills) := by
  constructor
  · intro addr a1 a2 ⟨hExp1, hLo1, hHi1⟩ ⟨hExp2, hLo2, hHi2⟩
    exact Decidable.byContradiction fun hNe => by
      have hSep := hGuard a1 a2 hExp1 hExp2 hNe
      omega
  · intro fl sp k ofs hk hOfsLe
    have hPub := fl.localsWithinPublic k hk
    have hG := fl.guardPositive
    have hToSpills := fl.publicToSpills
    unfold localByteFlatAddr
    omega

-- ============================================================================
-- Part 2: Sub-Register Aliasing (`rax`/`eax`/`ax`/`al`) & Callee-Saved
-- Register Tokens in `checkRegAlloc` (Resolving Track 4 Q1, Q3, & Q5)
-- ============================================================================

/-- Virtual register identifier. -/
abbrev VReg := Nat

/-- Physical 64-bit architectural register family identifier (e.g., `0` for the
`rax`/`eax`/`ax`/`al` family, `3` for the `rbx`/`ebx`/`bx`/`bl` family). -/
structure PReg where
  idx : Nat
  deriving DecidableEq, Repr

/-- Spill slot identifier in the private stack frame area. -/
abbrev SpillSlot := Nat

/-- Physical allocation assigned by `regalloc2`. -/
inductive Allocation where
  | preg (r : PReg)
  | spill (s : SpillSlot)
  deriving DecidableEq, Repr

/-- Sub-register operand width within a 64-bit architectural register family
(Track 4 Question 5). -/
inductive RegWidth where
  | w8
  | w16
  | w32
  | w64
  deriving DecidableEq, Repr

/-- Modulus $2^W$ associated with a `RegWidth`. -/
def RegWidth.modulus : RegWidth → Nat
  | .w8 => 256
  | .w16 => 65536
  | .w32 => 4294967296
  | .w64 => 18446744073709551616

theorem modulus_pos (w : RegWidth) : 0 < w.modulus := by
  cases w <;> decide

/-- Truncates a natural number to the low `w` bits. -/
def truncateWidth (w : RegWidth) (val : Nat) : Nat :=
  val % w.modulus

theorem truncateWidth_idem (w : RegWidth) (val : Nat) :
    truncateWidth w (truncateWidth w val) = truncateWidth w val := by
  unfold truncateWidth
  exact Nat.mod_mod val w.modulus

/-- Reads the low `w` bits of a 64-bit architectural register value `reg64`. -/
def readSubReg64 (reg64 : Nat) (w : RegWidth) : Nat :=
  truncateWidth w reg64

/-- Hardware x86-64 sub-register write semantics on a 64-bit architectural
register holding `old64`:
- Writing `.w8` (`al`) or `.w16` (`ax`) **merges** the low 8 or 16 bits into
  `old64`, preserving upper bits `[63:8]` or `[63:16]`.
- Writing `.w32` (`eax`) or `.w64` (`rax`) **overwrites** all 64 bits (zeroing
  upper bits `[63:32]` on `.w32`). -/
def writeSubReg64 (old64 : Nat) (w : RegWidth) (val : Nat) : Nat :=
  match w with
  | .w8 => (old64 / 256) * 256 + (val % 256)
  | .w16 => (old64 / 65536) * 65536 + (val % 65536)
  | .w32 => val % 4294967296
  | .w64 => val % 18446744073709551616

/-- **Lemma (`readSubReg64_writeSubReg64_same`):** Reading a sub-register at the
exact width `w` that was just written recovers `truncateWidth w val`, whether
the hardware merged low bits (`w8`/`w16`) or zero-extended (`w32`/`w64`). -/
theorem readSubReg64_writeSubReg64_same (old64 : Nat) (w : RegWidth)
    (val : Nat) :
    readSubReg64 (writeSubReg64 old64 w val) w = truncateWidth w val := by
  cases w <;>
    simp only [readSubReg64, writeSubReg64, truncateWidth, RegWidth.modulus] <;>
    omega

/-- **Theorem 2a (`canary_subreg_partial_write_clobbers_64bit` — Negative
Canary):**
When `rax` holds a live 64-bit value `old64 = 0x0100_0000_0000_002A`, neither
an 8-bit partial write `mov al, 0xFF` (`w8`, which merges `0xFF` into the low
byte) nor a 32-bit write `mov eax, 0x2A` (`w32`, which zeroes bits `[63:32]`)
preserves the 64-bit value in `rax`. Thus any sub-register write to a `PReg`
family must kill all existing width bindings for that `PReg` in `CheckerState`. -/
theorem canary_subreg_partial_write_clobbers_64bit :
    let old64 := 0x010000000000002A
    readSubReg64 (writeSubReg64 old64 .w8 0xFF) .w64 ≠
      readSubReg64 old64 .w64 ∧
    readSubReg64 (writeSubReg64 old64 .w32 0x2A) .w64 ≠
      readSubReg64 old64 .w64 := by
  decide

/-- Reads an `Allocation` at width `w` from physical registers `pregs` and
spill slots `spills`. -/
def readAllocWidth (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (a : Allocation) (w : RegWidth) : Nat :=
  match a with
  | .preg r => readSubReg64 (pregs r) w
  | .spill s => truncateWidth w (spills s)

/-- Writes `val` at width `w` to `a : Allocation` in `(pregs, spills)`. -/
def writeAllocWidth (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (a : Allocation) (w : RegWidth) (val : Nat) :
    (PReg → Nat) × (SpillSlot → Nat) :=
  match a with
  | .preg r =>
      (fun r' => if r' = r then writeSubReg64 (pregs r) w val else pregs r',
       spills)
  | .spill s =>
      (pregs,
       fun s' => if s' = s then truncateWidth w val else spills s')

theorem readAllocWidth_writeAllocWidth_same (pregs : PReg → Nat)
    (spills : SpillSlot → Nat) (a : Allocation) (w : RegWidth) (val : Nat) :
    readAllocWidth (writeAllocWidth pregs spills a w val).1
      (writeAllocWidth pregs spills a w val).2 a w =
      truncateWidth w val := by
  cases a with
  | preg r =>
      simp [writeAllocWidth, readAllocWidth, readSubReg64_writeSubReg64_same]
  | spill s =>
      simp [writeAllocWidth, readAllocWidth, truncateWidth_idem]

theorem readAllocWidth_writeAllocWidth_ne (pregs : PReg → Nat)
    (spills : SpillSlot → Nat) {a b : Allocation} (hNe : a ≠ b)
    (wRead wWrite : RegWidth) (val : Nat) :
    readAllocWidth (writeAllocWidth pregs spills b wWrite val).1
      (writeAllocWidth pregs spills b wWrite val).2 a wRead =
      readAllocWidth pregs spills a wRead := by
  cases a <;> cases b <;>
    simp [writeAllocWidth, readAllocWidth] at hNe ⊢
  · simp [hNe]
  · simp [hNe]

/-- Width-tagged `EditMove` (`into := from_` at width `width`). -/
structure SubRegEditMove where
  into : Allocation
  from_ : Allocation
  width : RegWidth
  deriving DecidableEq, Repr

/-- Executes a `SubRegEditMove`. -/
def execSubRegEditMove (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (m : SubRegEditMove) : (PReg → Nat) × (SpillSlot → Nat) :=
  let v := readAllocWidth pregs spills m.from_ m.width
  writeAllocWidth pregs spills m.into m.width v

/-- Executes a list of `SubRegEditMove`s sequentially. -/
def execSubRegEditMoves (pregs : PReg → Nat) (spills : SpillSlot → Nat) :
    List SubRegEditMove → (PReg → Nat) × (SpillSlot → Nat)
  | [] => (pregs, spills)
  | m :: ms =>
      let (pregs', spills') := execSubRegEditMove pregs spills m
      execSubRegEditMoves pregs' spills' ms

/-- Clobbers a list of caller-saved physical registers during a `Call` (setting
their contents to an arbitrary post-call state `callClobberVal r`, while leaving
all non-clobbered callee-saved registers intact). -/
def applyCallClobbers (pregs : PReg → Nat) (callClobberVal : PReg → Nat) :
    List PReg → PReg → Nat
  | [] => pregs
  | r :: rs =>
      applyCallClobbers
        (fun r' => if r' = r then callClobberVal r else pregs r')
        callClobberVal rs

/-- Source virtual-register instruction with explicit operand widths, explicit
zero-extension (`zext`), and function calls (`call`). -/
inductive SubVInst where
  | const (w : RegWidth) (dst : VReg) (val : Nat)
  | mov (w : RegWidth) (dst src : VReg)
  | zext (wDst wSrc : RegWidth) (dst src : VReg)
  | add (w : RegWidth) (dst lhs rhs : VReg)
  | call (retDst : VReg) (argSrc : VReg) (retVal : Nat)
  deriving DecidableEq, Repr

/-- Target allocated instruction with sub-register widths and caller-saved
clobber sets on `call`. -/
inductive SubMInstOp where
  | const (w : RegWidth) (dst : Allocation) (val : Nat)
  | mov (w : RegWidth) (dst src : Allocation)
  | zext (wDst wSrc : RegWidth) (dst src : Allocation)
  | add (w : RegWidth) (dst lhs rhs : Allocation)
  | call (retDst : Allocation) (argSrc : Allocation) (retVal : Nat)
      (callerSaved : List PReg)
  deriving DecidableEq, Repr

/-- Allocated instruction pairing pre-instruction `SubRegEditMove`s with a
`SubMInstOp`. -/
structure SubAllocatedInst where
  edits : List SubRegEditMove
  op : SubMInstOp
  deriving DecidableEq, Repr

/-- Functional update of a virtual register map. -/
def updateSubVReg (vregs : VReg → Nat) (v : VReg) (val : Nat) : VReg → Nat :=
  fun u => if u = v then val else vregs u

/-- Executes a source `SubVInst`. -/
def execSubVInst (vregs : VReg → Nat) (vi : SubVInst) : VReg → Nat :=
  match vi with
  | .const w dst val => updateSubVReg vregs dst (truncateWidth w val)
  | .mov w dst src => updateSubVReg vregs dst (truncateWidth w (vregs src))
  | .zext wDst wSrc dst src =>
      updateSubVReg vregs dst
        (truncateWidth wDst (truncateWidth wSrc (vregs src)))
  | .add w dst lhs rhs =>
      updateSubVReg vregs dst
        (truncateWidth w (truncateWidth w (vregs lhs) +
                          truncateWidth w (vregs rhs)))
  | .call retDst _argSrc retVal =>
      updateSubVReg vregs retDst (truncateWidth .w64 retVal)

/-- Executes a sequence of `SubVInst`s. -/
def execSubVInsts (vregs : VReg → Nat) : List SubVInst → VReg → Nat
  | [] => vregs
  | vi :: vis => execSubVInsts (execSubVInst vregs vi) vis

/-- Executes a target `SubMInstOp`. -/
def execSubMInstOp (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (callClobberVal : PReg → Nat) (op : SubMInstOp) :
    (PReg → Nat) × (SpillSlot → Nat) :=
  match op with
  | .const w dst val =>
      writeAllocWidth pregs spills dst w val
  | .mov w dst src =>
      let v := readAllocWidth pregs spills src w
      writeAllocWidth pregs spills dst w v
  | .zext wDst wSrc dst src =>
      let v := readAllocWidth pregs spills src wSrc
      writeAllocWidth pregs spills dst wDst v
  | .add w dst lhs rhs =>
      let vL := readAllocWidth pregs spills lhs w
      let vR := readAllocWidth pregs spills rhs w
      writeAllocWidth pregs spills dst w (vL + vR)
  | .call retDst argSrc retVal callerSaved =>
      let _arg := readAllocWidth pregs spills argSrc .w64
      let pregs1 := applyCallClobbers pregs callClobberVal callerSaved
      writeAllocWidth pregs1 spills retDst .w64 retVal

/-- Executes a `SubAllocatedInst`. -/
def execSubAllocatedInst (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (callClobberVal : PReg → Nat) (ai : SubAllocatedInst) :
    (PReg → Nat) × (SpillSlot → Nat) :=
  let (pregs1, spills1) := execSubRegEditMoves pregs spills ai.edits
  execSubMInstOp pregs1 spills1 callClobberVal ai.op

/-- Executes a sequence of `SubAllocatedInst`s. -/
def execSubAllocatedInsts (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (callClobberVal : PReg → Nat) :
    List SubAllocatedInst → (PReg → Nat) × (SpillSlot → Nat)
  | [] => (pregs, spills)
  | ai :: ais =>
      let (pregs', spills') :=
        execSubAllocatedInst pregs spills callClobberVal ai
      execSubAllocatedInsts pregs' spills' callClobberVal ais

/-- A width-tagged symbolic binding `(alloc, width, vreg)` in the extended
`regalloc2` checker state. Asserts that reading `alloc` at `width` yields
`truncateWidth width (vregs vreg)`. -/
structure SubRegBinding where
  alloc : Allocation
  width : RegWidth
  vreg : VReg
  deriving DecidableEq, Repr

/-- Symbolic state of the sub-register-aware `regalloc2` checker. -/
abbrev SubRegCheckerState := List SubRegBinding

/-- Checks whether `alloc` is currently guaranteed to hold `vreg` at exact
width `w`. -/
def hasVRegWidth (st : SubRegCheckerState) (a : Allocation) (w : RegWidth)
    (v : VReg) : Bool :=
  st.contains { alloc := a, width := w, vreg := v }

/-- Kills **all** symbolic bindings for `Allocation` `a` across **all** widths
`w8, w16, w32, w64`. When `a = .preg r`, this kills the entire architectural
register family `r` (`rax`/`eax`/`ax`/`al`). -/
def killAllocFamily (st : SubRegCheckerState) (a : Allocation) :
    SubRegCheckerState :=
  st.filter (fun b => b.alloc != a)

/-- Kills all bindings in a list of clobbered physical register families. -/
def killPRegFamilies (st : SubRegCheckerState) :
    List PReg → SubRegCheckerState
  | [] => st
  | r :: rs => killPRegFamilies (killAllocFamily st (.preg r)) rs

/-- Symbolic transfer function for `SubRegEditMove`:
1. Unconditionally kills all width bindings in the destination family `m.into`,
2. Copies only bindings from `m.from_` whose width matches `m.width`. -/
def updateSubRegMove (st : SubRegCheckerState) (m : SubRegEditMove) :
    SubRegCheckerState :=
  let kept := killAllocFamily st m.into
  let copied :=
    (st.filter (fun b => b.alloc == m.from_ && b.width == m.width)).map
      (fun b => { alloc := m.into, width := m.width, vreg := b.vreg })
  kept ++ copied

/-- Symbolic transfer for a list of `SubRegEditMove`s. -/
def updateSubRegMoves (st : SubRegCheckerState) :
    List SubRegEditMove → SubRegCheckerState
  | [] => st
  | m :: ms => updateSubRegMoves (updateSubRegMove st m) ms

/-- Symbolic transfer function for defining `v` in `dst` at width `w`:
kills all width bindings in `dst` and all stale bindings for `v`, then binds
`{ alloc := dst, width := w, vreg := v }`. -/
def updateSubRegDef (st : SubRegCheckerState) (dst : Allocation)
    (w : RegWidth) (v : VReg) : SubRegCheckerState :=
  { alloc := dst, width := w, vreg := v } ::
    st.filter (fun b => b.alloc != dst && b.vreg != v)

/-- Validates a single `SubMInstOp` against a source `SubVInst` and computes
the successor `SubRegCheckerState`. -/
def checkSubMInstOp (st : SubRegCheckerState) (vi : SubVInst)
    (op : SubMInstOp) : Option SubRegCheckerState :=
  match vi, op with
  | .const vw vDst vVal, .const mw mDst mVal =>
      if vw == mw && vVal == mVal then
        some (updateSubRegDef st mDst vw vDst)
      else
        none
  | .mov vw vDst vSrc, .mov mw mDst mSrc =>
      if vw == mw && hasVRegWidth st mSrc vw vSrc then
        some (updateSubRegDef st mDst vw vDst)
      else
        none
  | .zext vwDst vwSrc vDst vSrc, .zext mwDst mwSrc mDst mSrc =>
      if vwDst == mwDst && vwSrc == mwSrc &&
         hasVRegWidth st mSrc vwSrc vSrc then
        some (updateSubRegDef st mDst vwDst vDst)
      else
        none
  | .add vw vDst vLhs vRhs, .add mw mDst mLhs mRhs =>
      if vw == mw &&
         hasVRegWidth st mLhs vw vLhs &&
         hasVRegWidth st mRhs vw vRhs then
        some (updateSubRegDef st mDst vw vDst)
      else
        none
  | .call vRetDst vArgSrc vRetVal,
    .call mRetDst mArgSrc mRetVal callerSaved =>
      if vRetVal == mRetVal && hasVRegWidth st mArgSrc .w64 vArgSrc then
        let stAfterClobber := killPRegFamilies st callerSaved
        some (updateSubRegDef stAfterClobber mRetDst .w64 vRetDst)
      else
        none
  | _, _ => none

/-- Validates a `SubAllocatedInst` (`edits` followed by `op`). -/
def checkSubAllocatedInst (st : SubRegCheckerState) (vi : SubVInst)
    (ai : SubAllocatedInst) : Option SubRegCheckerState :=
  let st1 := updateSubRegMoves st ai.edits
  checkSubMInstOp st1 vi ai.op

/-- Validates a sequence of `SubAllocatedInst`s against `SubVInst`s. -/
def checkSubAllocatedInsts (st : SubRegCheckerState) :
    List SubVInst → List SubAllocatedInst → Option SubRegCheckerState
  | [], [] => some st
  | vi :: vis, ai :: ais =>
      match checkSubAllocatedInst st vi ai with
      | none => none
      | some st' => checkSubAllocatedInsts st' vis ais
  | _, _ => none

/-- Virtual-register token representing the caller's entry value of
callee-saved physical register `r` (Track 4 Question 3). We reserve high virtual
register indices `10000 + r.idx` for entry callee-save tokens. -/
def calleeSaveToken (r : PReg) : VReg :=
  10000 + r.idx

/-- Initial `SubRegCheckerState` at function entry seeding each callee-saved
register `r ∈ calleeSaved` with its 64-bit entry token `calleeSaveToken r`. -/
def initialCalleeSaveState (calleeSaved : List PReg) : SubRegCheckerState :=
  calleeSaved.map (fun r =>
    { alloc := .preg r, width := .w64, vreg := calleeSaveToken r })

/-- Checks at a `Return` terminator that every callee-saved register
`r ∈ calleeSaved` currently holds its entry token `calleeSaveToken r` at `.w64`. -/
def checkCalleeSavedAtReturn (calleeSaved : List PReg)
    (st : SubRegCheckerState) : Bool :=
  calleeSaved.all (fun r => hasVRegWidth st (.preg r) .w64 (calleeSaveToken r))

/-- Complete single-block function validator with sub-register widths, explicit
`zext`, `call` clobbers, and callee-saved register token verification at return.
(Multi-block CFG edges check `subState` against the `blockIn` certificate in
$O(B + I)$ linear time, resolving Track 4 Question 1.) -/
def checkSubRegFunc (calleeSaved : List PReg) (vis : List SubVInst)
    (vRet : VReg) (ais : List SubAllocatedInst)
    (retEdits : List SubRegEditMove) (mRet : Allocation) : Bool :=
  let st0 := initialCalleeSaveState calleeSaved
  match checkSubAllocatedInsts st0 vis ais with
  | none => false
  | some stBody =>
      let stRet := updateSubRegMoves stBody retEdits
      hasVRegWidth stRet mRet .w64 vRet &&
      checkCalleeSavedAtReturn calleeSaved stRet

/-! ### Soundness of Sub-Register & Callee-Save Verification -/

/-- Semantic compatibility invariant for width-tagged symbolic bindings:
every `{ alloc, width, vreg } ∈ st` satisfies
`readAllocWidth pregs spills alloc width = truncateWidth width (vregs vreg)`. -/
def SubRegStateCompat (st : SubRegCheckerState) (vregs : VReg → Nat)
    (pregs : PReg → Nat) (spills : SpillSlot → Nat) : Prop :=
  ∀ b, b ∈ st →
    readAllocWidth pregs spills b.alloc b.width =
      truncateWidth b.width (vregs b.vreg)

theorem hasVRegWidth_sound {st : SubRegCheckerState} {vregs : VReg → Nat}
    {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    (hCompat : SubRegStateCompat st vregs pregs spills)
    {a : Allocation} {w : RegWidth} {v : VReg}
    (hHas : hasVRegWidth st a w v = true) :
    readAllocWidth pregs spills a w = truncateWidth w (vregs v) := by
  unfold hasVRegWidth at hHas
  rw [List.contains_iff_mem] at hHas
  exact hCompat { alloc := a, width := w, vreg := v } hHas

theorem updateSubRegMove_compat {st : SubRegCheckerState} {vregs : VReg → Nat}
    {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    (hCompat : SubRegStateCompat st vregs pregs spills) (m : SubRegEditMove) :
    SubRegStateCompat (updateSubRegMove st m) vregs
      (execSubRegEditMove pregs spills m).1
      (execSubRegEditMove pregs spills m).2 := by
  intro b hMem
  unfold updateSubRegMove killAllocFamily at hMem
  rw [List.mem_append] at hMem
  cases hMem with
  | inl hKept =>
      rw [List.mem_filter] at hKept
      rcases hKept with ⟨hInSt, hNeB⟩
      have hNe : b.alloc ≠ m.into := by
        intro hEq
        simp [hEq] at hNeB
      unfold execSubRegEditMove
      rw [readAllocWidth_writeAllocWidth_ne pregs spills hNe]
      exact hCompat b hInSt
  | inr hCopied =>
      rw [List.mem_map] at hCopied
      rcases hCopied with ⟨b0, hInFilter, hEqB⟩
      rw [List.mem_filter] at hInFilter
      rcases hInFilter with ⟨hInSt, hCond⟩
      rw [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hAllocB, hWidthB⟩
      have hAlloc : b0.alloc = m.from_ := of_decide_eq_true hAllocB
      have hWidth : b0.width = m.width := of_decide_eq_true hWidthB
      subst hEqB
      dsimp only
      unfold execSubRegEditMove
      rw [readAllocWidth_writeAllocWidth_same]
      have hB0 := hCompat b0 hInSt
      rw [hAlloc, hWidth] at hB0
      rw [hB0, truncateWidth_idem]

theorem updateSubRegMoves_compat {st : SubRegCheckerState} {vregs : VReg → Nat}
    {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    (hCompat : SubRegStateCompat st vregs pregs spills)
    (edits : List SubRegEditMove) :
    SubRegStateCompat (updateSubRegMoves st edits) vregs
      (execSubRegEditMoves pregs spills edits).1
      (execSubRegEditMoves pregs spills edits).2 := by
  induction edits generalizing st pregs spills with
  | nil => exact hCompat
  | cons m ms ih =>
      simp only [updateSubRegMoves, execSubRegEditMoves]
      exact ih (updateSubRegMove_compat hCompat m)

theorem killAllocFamily_preg_compat {st : SubRegCheckerState}
    {vregs : VReg → Nat} {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    (hCompat : SubRegStateCompat st vregs pregs spills)
    (r : PReg) (val : Nat) :
    SubRegStateCompat (killAllocFamily st (.preg r)) vregs
      (fun r' => if r' = r then val else pregs r') spills := by
  intro b hMem
  unfold killAllocFamily at hMem
  rw [List.mem_filter] at hMem
  rcases hMem with ⟨hInSt, hNeB⟩
  cases hA : b.alloc with
  | preg r' =>
      have hNe : r' ≠ r := by
        intro hEq
        subst hEq
        simp [hA] at hNeB
      have hOrig := hCompat b hInSt
      rw [hA] at hOrig
      dsimp only [readAllocWidth] at hOrig ⊢
      simp [hNe, hOrig]
  | spill s =>
      have hOrig := hCompat b hInSt
      rw [hA] at hOrig
      exact hOrig

theorem killPRegFamilies_compat {st : SubRegCheckerState}
    {vregs : VReg → Nat} {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    (hCompat : SubRegStateCompat st vregs pregs spills)
    (callClobberVal : PReg → Nat) (callerSaved : List PReg) :
    SubRegStateCompat (killPRegFamilies st callerSaved) vregs
      (applyCallClobbers pregs callClobberVal callerSaved) spills := by
  induction callerSaved generalizing st pregs with
  | nil => exact hCompat
  | cons r rs ih =>
      simp only [killPRegFamilies, applyCallClobbers]
      exact ih (killAllocFamily_preg_compat hCompat r (callClobberVal r))

theorem updateSubRegDef_compat {st : SubRegCheckerState}
    {vregs : VReg → Nat} {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    (hCompat : SubRegStateCompat st vregs pregs spills)
    (dst : Allocation) (w : RegWidth) (v : VReg) (rawVal : Nat) :
    SubRegStateCompat (updateSubRegDef st dst w v)
      (updateSubVReg vregs v (truncateWidth w rawVal))
      (writeAllocWidth pregs spills dst w rawVal).1
      (writeAllocWidth pregs spills dst w rawVal).2 := by
  intro b hMem
  unfold updateSubRegDef at hMem
  rw [List.mem_cons] at hMem
  cases hMem with
  | inl hHead =>
      subst hHead
      dsimp only
      rw [readAllocWidth_writeAllocWidth_same]
      simp [updateSubVReg, truncateWidth_idem]
  | inr hTail =>
      rw [List.mem_filter] at hTail
      rcases hTail with ⟨hInSt, hCond⟩
      rw [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hNeDstB, hNeVB⟩
      have hNeDst : b.alloc ≠ dst := by
        intro hEq; simp [hEq] at hNeDstB
      have hNeV : b.vreg ≠ v := by
        intro hEq; simp [hEq] at hNeVB
      rw [readAllocWidth_writeAllocWidth_ne pregs spills hNeDst]
      simp [updateSubVReg, hNeV, hCompat b hInSt]

/-- **Lemma (`checkSubMInstOp_sound`):** Single-instruction forward simulation
for the width-tagged sub-register checker. -/
theorem checkSubMInstOp_sound {st st' : SubRegCheckerState}
    {vregs : VReg → Nat} {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    {callClobberVal : PReg → Nat} {vi : SubVInst} {op : SubMInstOp}
    (hCheck : checkSubMInstOp st vi op = some st')
    (hCompat : SubRegStateCompat st vregs pregs spills) :
    let vregs' := execSubVInst vregs vi
    let (pregs', spills') := execSubMInstOp pregs spills callClobberVal op
    SubRegStateCompat st' vregs' pregs' spills' := by
  cases vi <;> cases op <;> simp only [checkSubMInstOp] at hCheck
  case const.const vw vDst vVal mw mDst mVal =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt; subst hSt
      rw [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hWB, hValB⟩
      have hW : vw = mw := of_decide_eq_true hWB
      have hVal : vVal = mVal := of_decide_eq_true hValB
      subst hW; subst hVal
      exact updateSubRegDef_compat hCompat mDst vw vDst vVal
    · contradiction
  case mov.mov vw vDst vSrc mw mDst mSrc =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt; subst hSt
      rw [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hWB, hHas⟩
      have hW : vw = mw := of_decide_eq_true hWB
      subst hW
      have hSrcEq := hasVRegWidth_sound hCompat hHas
      dsimp only [execSubVInst, execSubMInstOp]
      rw [hSrcEq]
      have hDef := updateSubRegDef_compat hCompat mDst vw vDst
        (truncateWidth vw (vregs vSrc))
      rw [truncateWidth_idem] at hDef
      exact hDef
    · contradiction
  case zext.zext vwDst vwSrc vDst vSrc mwDst mwSrc mDst mSrc =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt; subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨hWDstB, hWSrcB⟩, hHas⟩
      have hWDst : vwDst = mwDst := of_decide_eq_true hWDstB
      have hWSrc : vwSrc = mwSrc := of_decide_eq_true hWSrcB
      subst hWDst; subst hWSrc
      have hSrcEq := hasVRegWidth_sound hCompat hHas
      dsimp only [execSubVInst, execSubMInstOp]
      rw [hSrcEq]
      exact updateSubRegDef_compat hCompat mDst vwDst vDst
        (truncateWidth vwSrc (vregs vSrc))
    · contradiction
  case add.add vw vDst vLhs vRhs mw mDst mLhs mRhs =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt; subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨hWB, hLhs⟩, hRhs⟩
      have hW : vw = mw := of_decide_eq_true hWB
      subst hW
      have hLhsEq := hasVRegWidth_sound hCompat hLhs
      have hRhsEq := hasVRegWidth_sound hCompat hRhs
      dsimp only [execSubVInst, execSubMInstOp]
      rw [hLhsEq, hRhsEq]
      exact updateSubRegDef_compat hCompat mDst vw vDst
        (truncateWidth vw (vregs vLhs) + truncateWidth vw (vregs vRhs))
    · contradiction
  case call.call vRetDst vArgSrc vRetVal mRetDst mArgSrc mRetVal callerSaved =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt; subst hSt
      rw [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hValB, _hHasArg⟩
      have hVal : vRetVal = mRetVal := of_decide_eq_true hValB
      subst hVal
      dsimp only [execSubVInst, execSubMInstOp]
      have hClobCompat :=
        killPRegFamilies_compat hCompat callClobberVal callerSaved
      exact updateSubRegDef_compat hClobCompat mRetDst .w64 vRetDst vRetVal
    · contradiction
  all_goals contradiction

/-- **Lemma (`checkSubAllocatedInsts_sound`):** Multi-instruction sequence
soundness for the sub-register checker. -/
theorem checkSubAllocatedInsts_sound {st st' : SubRegCheckerState}
    {vregs : VReg → Nat} {pregs : PReg → Nat} {spills : SpillSlot → Nat}
    {callClobberVal : PReg → Nat}
    {vis : List SubVInst} {ais : List SubAllocatedInst}
    (hCheck : checkSubAllocatedInsts st vis ais = some st')
    (hCompat : SubRegStateCompat st vregs pregs spills) :
    let vregs' := execSubVInsts vregs vis
    let (pregs', spills') :=
      execSubAllocatedInsts pregs spills callClobberVal ais
    SubRegStateCompat st' vregs' pregs' spills' := by
  induction vis generalizing ais st vregs pregs spills with
  | nil =>
      cases ais with
      | nil =>
          simp [checkSubAllocatedInsts] at hCheck
          subst hCheck
          exact hCompat
      | cons _ _ =>
          simp [checkSubAllocatedInsts] at hCheck
  | cons vi visTail ih =>
      cases ais with
      | nil =>
          simp [checkSubAllocatedInsts] at hCheck
      | cons ai aisTail =>
          simp only [checkSubAllocatedInsts] at hCheck
          cases hOne : checkSubAllocatedInst st vi ai with
          | none =>
              rw [hOne] at hCheck; contradiction
          | some st1 =>
              rw [hOne] at hCheck
              unfold checkSubAllocatedInst at hOne
              have hMovesCompat := updateSubRegMoves_compat hCompat ai.edits
              have hOpCompat :=
                checkSubMInstOp_sound (callClobberVal := callClobberVal)
                  hOne hMovesCompat
              dsimp only [execSubVInsts, execSubAllocatedInsts,
                          execSubAllocatedInst]
              exact ih hCheck hOpCompat

/-- Initial compatibility of `initialCalleeSaveState` when `vregs` binds each
`calleeSaveToken r` to `pregs r`. -/
theorem initialCalleeSaveState_compat (calleeSaved : List PReg)
    (vregs : VReg → Nat) (pregs : PReg → Nat) (spills : SpillSlot → Nat)
    (hTokens : ∀ r, r ∈ calleeSaved → vregs (calleeSaveToken r) = pregs r) :
    SubRegStateCompat (initialCalleeSaveState calleeSaved)
      vregs pregs spills := by
  intro b hMem
  unfold initialCalleeSaveState at hMem
  rw [List.mem_map] at hMem
  rcases hMem with ⟨r, hrIn, rfl⟩
  dsimp only [readAllocWidth, readSubReg64]
  rw [hTokens r hrIn]

/-- If `vi` never overwrites `calleeSaveToken r`, `execSubVInst` preserves
`vregs (calleeSaveToken r)`. -/
def instPreservesToken (tok : VReg) (vi : SubVInst) : Bool :=
  match vi with
  | .const _ dst _ => dst != tok
  | .mov _ dst _ => dst != tok
  | .zext _ _ dst _ => dst != tok
  | .add _ dst _ _ => dst != tok
  | .call dst _ _ => dst != tok

def instsPreserveTokens (calleeSaved : List PReg)
    (vis : List SubVInst) : Bool :=
  calleeSaved.all (fun r =>
    vis.all (fun vi => instPreservesToken (calleeSaveToken r) vi))

theorem execSubVInst_preserves_token {vregs : VReg → Nat} {tok : VReg}
    {vi : SubVInst} (hPres : instPreservesToken tok vi = true) :
    (execSubVInst vregs vi) tok = vregs tok := by
  cases vi <;>
    simp only [instPreservesToken, bne_iff_ne, ne_eq] at hPres <;>
    simp [execSubVInst, updateSubVReg, Ne.symm hPres]

theorem execSubVInsts_preserves_token {vregs : VReg → Nat} {tok : VReg}
    {vis : List SubVInst}
    (hPres : vis.all (fun vi => instPreservesToken tok vi) = true) :
    (execSubVInsts vregs vis) tok = vregs tok := by
  induction vis generalizing vregs with
  | nil => rfl
  | cons vi visTail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hPres
      rcases hPres with ⟨hHead, hTail⟩
      simp only [execSubVInsts]
      rw [ih hTail, execSubVInst_preserves_token hHead]

/-- **Theorem 2b & 2c Combined (`subreg_and_callee_saved_sound`):**
For any function accepted by `checkSubRegFunc`:
1. The final return allocation `mRet` holds the exact 64-bit truncated value of
   `vRet` computed by the source virtual-register program (`SubRegStateCompat`
   soundness across sub-register writes, `zext`, moves, and calls), and
2. Every callee-saved physical register `r ∈ calleeSaved` holds its original
   entry 64-bit value `readSubReg64 (pregs r) .w64` upon return, even if `r` was
   spilled to the stack, overwritten during the function body, and reloaded
   before `ret`! -/
theorem subreg_and_callee_saved_sound
    (calleeSaved : List PReg) (vis : List SubVInst) (vRet : VReg)
    (ais : List SubAllocatedInst) (retEdits : List SubRegEditMove)
    (mRet : Allocation) (vregs : VReg → Nat) (pregs : PReg → Nat)
    (spills : SpillSlot → Nat) (callClobberVal : PReg → Nat)
    (hCheck : checkSubRegFunc calleeSaved vis vRet ais retEdits mRet = true)
    (hTokensInit : ∀ r, r ∈ calleeSaved → vregs (calleeSaveToken r) = pregs r)
    (hPresTokens : instsPreserveTokens calleeSaved vis = true) :
    let vregsFinal := execSubVInsts vregs vis
    let (pregsBody, spillsBody) :=
      execSubAllocatedInsts pregs spills callClobberVal ais
    let (pregsFinal, spillsFinal) :=
      execSubRegEditMoves pregsBody spillsBody retEdits
    readAllocWidth pregsFinal spillsFinal mRet .w64 =
      truncateWidth .w64 (vregsFinal vRet) ∧
    (∀ r, r ∈ calleeSaved →
      readSubReg64 (pregsFinal r) .w64 = readSubReg64 (pregs r) .w64) := by
  unfold checkSubRegFunc at hCheck
  dsimp only at hCheck
  cases hBody :
      checkSubAllocatedInsts (initialCalleeSaveState calleeSaved) vis ais with
  | none =>
      rw [hBody] at hCheck; contradiction
  | some stBody =>
      rw [hBody] at hCheck
      dsimp only at hCheck
      rw [Bool.and_eq_true] at hCheck
      rcases hCheck with ⟨hHasRet, hCalleeSaved⟩
      have hInitCompat :=
        initialCalleeSaveState_compat calleeSaved vregs pregs spills hTokensInit
      have hBodyCompat :=
        checkSubAllocatedInsts_sound (callClobberVal := callClobberVal)
          hBody hInitCompat
      have hRetCompat := updateSubRegMoves_compat hBodyCompat retEdits
      refine ⟨hasVRegWidth_sound hRetCompat hHasRet, ?_⟩
      intro r hrIn
      unfold checkCalleeSavedAtReturn at hCalleeSaved
      rw [List.all_eq_true] at hCalleeSaved
      have hHasR := hCalleeSaved r hrIn
      have hValR := hasVRegWidth_sound hRetCompat hHasR
      dsimp only [readAllocWidth] at hValR
      unfold instsPreserveTokens at hPresTokens
      rw [List.all_eq_true] at hPresTokens
      have hPresR := hPresTokens r hrIn
      have hTokEq := execSubVInsts_preserves_token (vregs := vregs) hPresR
      rw [hValR, hTokEq, hTokensInit r hrIn]
      rfl

/-- **Theorem 2b (`subreg_checkRegAlloc_sound`):**
First projection of `subreg_and_callee_saved_sound`: the return allocation
`mRet` agrees with the 64-bit source virtual register `vRet` across arbitrary
width-tagged sub-register definitions, partial writes, `zext` conversions, and
moves. -/
theorem subreg_checkRegAlloc_sound
    (calleeSaved : List PReg) (vis : List SubVInst) (vRet : VReg)
    (ais : List SubAllocatedInst) (retEdits : List SubRegEditMove)
    (mRet : Allocation) (vregs : VReg → Nat) (pregs : PReg → Nat)
    (spills : SpillSlot → Nat) (callClobberVal : PReg → Nat)
    (hCheck : checkSubRegFunc calleeSaved vis vRet ais retEdits mRet = true)
    (hTokensInit : ∀ r, r ∈ calleeSaved → vregs (calleeSaveToken r) = pregs r)
    (hPresTokens : instsPreserveTokens calleeSaved vis = true) :
    let vregsFinal := execSubVInsts vregs vis
    let (pregsBody, spillsBody) :=
      execSubAllocatedInsts pregs spills callClobberVal ais
    let (pregsFinal, spillsFinal) :=
      execSubRegEditMoves pregsBody spillsBody retEdits
    readAllocWidth pregsFinal spillsFinal mRet .w64 =
      truncateWidth .w64 (vregsFinal vRet) :=
  (subreg_and_callee_saved_sound calleeSaved vis vRet ais retEdits mRet
    vregs pregs spills callClobberVal hCheck hTokensInit hPresTokens).1

/-- **Theorem 2c (`callee_saved_preserved_of_checkRegAlloc`):**
Second projection of `subreg_and_callee_saved_sound`: every callee-saved
register `r ∈ calleeSaved` holds its original entry 64-bit value upon return. -/
theorem callee_saved_preserved_of_checkRegAlloc
    (calleeSaved : List PReg) (vis : List SubVInst) (vRet : VReg)
    (ais : List SubAllocatedInst) (retEdits : List SubRegEditMove)
    (mRet : Allocation) (vregs : VReg → Nat) (pregs : PReg → Nat)
    (spills : SpillSlot → Nat) (callClobberVal : PReg → Nat)
    (hCheck : checkSubRegFunc calleeSaved vis vRet ais retEdits mRet = true)
    (hTokensInit : ∀ r, r ∈ calleeSaved → vregs (calleeSaveToken r) = pregs r)
    (hPresTokens : instsPreserveTokens calleeSaved vis = true) :
    let (pregsBody, spillsBody) :=
      execSubAllocatedInsts pregs spills callClobberVal ais
    let (pregsFinal, _) :=
      execSubRegEditMoves pregsBody spillsBody retEdits
    ∀ r, r ∈ calleeSaved →
      readSubReg64 (pregsFinal r) .w64 = readSubReg64 (pregs r) .w64 :=
  (subreg_and_callee_saved_sound calleeSaved vis vRet ais retEdits mRet
    vregs pregs spills callClobberVal hCheck hTokensInit hPresTokens).2

/-! ### Executable Adequacy Canaries for Sub-Registers & Callee-Saved Protocol -/

/-- Source program for sub-register canary: writes 8-bit constant `0x2A` to `v0`,
then zero-extends `v0` (`.w8` → `.w64`) into `v1` and returns `v1`. -/
def subregCanaryVisWithZext : List SubVInst :=
  [.const .w8 0 0x2A, .zext .w64 .w8 1 0]

/-- Source program without `zext`: writes 8-bit constant `0x2A` to `v0` and
attempts to return `v0` directly as a 64-bit register. -/
def subregCanaryVisNoZext : List SubVInst :=
  [.const .w8 0 0x2A]

/-- Target program without `zext`: writes `al` (`PReg 0` at `.w8`) and attempts
to return `rax` (`PReg 0` at `.w64`) without zero-extending the upper 56 bits. -/
def subregBadAllocNoZext : List SubAllocatedInst :=
  [{ edits := [], op := .const .w8 (.preg ⟨0⟩) 0x2A }]

/-- Target program with `zext`: writes `al` (`PReg 0` at `.w8`) and then
executes `movzx rax, al` (`.zext .w64 .w8 (.preg ⟨0⟩) (.preg ⟨0⟩)`). -/
def subregGoodAllocWithZext : List SubAllocatedInst :=
  [{ edits := [], op := .const .w8 (.preg ⟨0⟩) 0x2A },
   { edits := [], op := .zext .w64 .w8 (.preg ⟨0⟩) (.preg ⟨0⟩) }]

/-- **Canary 2b (`canary_subreg_width_mismatch_rejected` &
`canary_subreg_with_zext_accepted`):**
Writing `al` (`.w8`) and reading `rax` (`.w64`) without an explicit extension
is rejected (`= false`) by `checkSubRegFunc`, whereas inserting `zext` (`movzx`)
is accepted (`= true`). -/
theorem canary_subreg_width_mismatch_rejected :
    checkSubRegFunc [] subregCanaryVisNoZext 0
      subregBadAllocNoZext [] (.preg ⟨0⟩) = false ∧
    checkSubRegFunc [] subregCanaryVisWithZext 1
      subregGoodAllocWithZext [] (.preg ⟨0⟩) = true := by
  decide

/-- Source program for callee-save canary: computes `v0 := 50`, calls a helper
function returning `100` into `v1`, adds `v2 := v0 + v1`, and returns `v2`.
Here `PReg 3` (`rbx`) is callee-saved and `PReg 0` (`rax`) is caller-saved. -/
def calleeSaveCanaryVis : List SubVInst :=
  [.const .w64 0 50,
   .call 1 0 100,
   .add .w64 2 0 1]

/-- Buggy allocation that uses callee-saved register `PReg 3` (`rbx`) to hold
`v0` across the `call` without spilling and restoring the caller's `PReg 3`. -/
def calleeSaveBadNoRestoreAlloc : List SubAllocatedInst :=
  [{ edits := [], op := .const .w64 (.preg ⟨3⟩) 50 },
   { edits := [], op := .call (.preg ⟨0⟩) (.preg ⟨3⟩) 100 [⟨0⟩, ⟨1⟩] },
   { edits := [], op := .add .w64 (.preg ⟨0⟩) (.preg ⟨3⟩) (.preg ⟨0⟩) }]

/-- Correct allocation that spills callee-saved `PReg 3` (`rbx`) to `SpillSlot 0`
in the prologue, uses `PReg 3` across the `call` (which clobbers caller-saved
`PReg 0` and `PReg 1`), and reloads `PReg 3` from `SpillSlot 0` in the epilogue
(`retEdits`) before returning. -/
def calleeSaveGoodSpillRestoreAlloc : List SubAllocatedInst :=
  [{ edits := [{ into := .spill 0, from_ := .preg ⟨3⟩, width := .w64 }],
     op := .const .w64 (.preg ⟨3⟩) 50 },
   { edits := [], op := .call (.preg ⟨0⟩) (.preg ⟨3⟩) 100 [⟨0⟩, ⟨1⟩] },
   { edits := [], op := .add .w64 (.preg ⟨0⟩) (.preg ⟨3⟩) (.preg ⟨0⟩) }]

def calleeSaveEpilogueReload : List SubRegEditMove :=
  [{ into := .preg ⟨3⟩, from_ := .spill 0, width := .w64 }]

/-- **Canary 2c (`canary_missing_callee_save_restore_rejected` &
`canary_callee_save_spilled_and_restored_accepted`):**
Overwriting callee-saved register `PReg 3` (`rbx`) without restoring it is
rejected (`= false`), while spilling `PReg 3` to `SpillSlot 0` before use and
reloading `PReg 3` before `ret` is accepted (`= true`). -/
theorem canary_callee_save_protocol_adequacy :
    checkSubRegFunc [⟨3⟩] calleeSaveCanaryVis 2
      calleeSaveBadNoRestoreAlloc [] (.preg ⟨0⟩) = false ∧
    checkSubRegFunc [⟨3⟩] calleeSaveCanaryVis 2
      calleeSaveGoodSpillRestoreAlloc calleeSaveEpilogueReload (.preg ⟨0⟩) =
      true := by
  decide

-- ============================================================================
-- Part 3: Discharging `A-BEH-07` Across Indirect Calls (`dyn Trait` / `fn`)
-- (Resolving Track 4 Question 4: Static VTable Contracts vs. Dynamic Checks)
-- ============================================================================

/-- Function identifier in an indirect call graph. -/
abbrev FnId := Nat

/-- Outcome of a stack-bounded execution step. -/
inductive StackStepResult (State : Type) where
  | ok (next : State)
  | stackOverflow
  deriving DecidableEq, Repr

/-- **Method A (Static VTable / `FnPtr` Contract Bound):**
Every indirect call signature (`dyn Trait` method or `fn` pointer type) carries
a static worst-case stack consumption contract `wcetStack : Nat`. -/
structure IndirectCallContract where
  wcetStack : Nat
  deriving DecidableEq, Repr

/-- A function `target` is a valid inhabitant of an `IndirectCallContract` iff
its verified peak stack consumption `peakStack target` is at most
`contract.wcetStack`. -/
def ValidTargetForContract (peakStack : FnId → Nat)
    (contract : IndirectCallContract) (target : FnId) : Prop :=
  peakStack target ≤ contract.wcetStack

/-- Executes an indirect call to `target` from a caller whose own frame uses
`callerFrameSize` bytes on top of `usedStack` bytes, checking whether peak
consumption exceeds `stackBudget`. -/
def evalIndirectCallStatic (peakStack : FnId → Nat)
    (stackTop stackBudget usedStack callerFrameSize : Nat)
    (target : FnId) : StackStepResult Nat :=
  let totalPeak := usedStack + callerFrameSize + peakStack target
  if stackBudget < totalPeak then
    .stackOverflow
  else
    .ok (stackTop - totalPeak)

/-- **Theorem 3a (`indirect_call_static_contract_no_overflow` — Method A):**
If an indirect call site is verified against `contract : IndirectCallContract`
(`usedStack + callerFrameSize + contract.wcetStack ≤ stackBudget`), then
dispatching at runtime to **any** vtable or function-pointer target satisfying
`ValidTargetForContract peakStack contract target` is guaranteed never to
trigger `.stackOverflow` and keeps the lowest reachable stack pointer at or
above `stackLimit = stackTop - stackBudget`. -/
theorem indirect_call_static_contract_no_overflow
    (peakStack : FnId → Nat) (contract : IndirectCallContract)
    (stackTop stackBudget usedStack callerFrameSize : Nat) (target : FnId)
    (hBudgetLeTop : stackBudget ≤ stackTop)
    (hCallerFit :
      usedStack + callerFrameSize + contract.wcetStack ≤ stackBudget)
    (hTargetValid : ValidTargetForContract peakStack contract target) :
    ∃ spLowest,
      evalIndirectCallStatic peakStack stackTop stackBudget
        usedStack callerFrameSize target = .ok spLowest ∧
      stackTop - stackBudget ≤ spLowest := by
  unfold ValidTargetForContract at hTargetValid
  unfold evalIndirectCallStatic
  have hNotOv :
      ¬ (stackBudget < usedStack + callerFrameSize + peakStack target) := by
    omega
  refine ⟨stackTop - (usedStack + callerFrameSize + peakStack target), ?_, ?_⟩
  · simp [hNotOv]
  · omega

/-- **Method B (Dynamic Prologue `stackLimit` Register / TLS Check):**
For open plugins, FFI callbacks, or mutually recursive `dyn Trait` graphs
without a closed static `wcetStack`, each function prologue compares
`sp < stackLimit + frameSize` (via a dedicated `stackLimit` register or TLS
slot, matching `cranelift-codegen`'s `insert_stack_check` in
`src/machinst/abi.rs:2263-2266`) before decrementing `sp`. -/
def execDynamicPrologueCheck (sp frameSize stackLimit : Nat) :
    StackStepResult Nat :=
  if sp < stackLimit + frameSize then
    .stackOverflow
  else
    .ok (sp - frameSize)

/-- Executes a multi-hop sequence of indirect calls with dynamic prologue
checks, given the sequence of frame sizes `frameSizes : List Nat`. -/
def execDynamicIndirectChain (stackLimit : Nat) :
    List Nat → Nat → StackStepResult Nat
  | [], sp => .ok sp
  | fSize :: rest, sp =>
      match execDynamicPrologueCheck sp fSize stackLimit with
      | .stackOverflow => .stackOverflow
      | .ok sp' => execDynamicIndirectChain stackLimit rest sp'

/-- **Theorem 3b (`dynamic_stack_check_preserves_limit` — Method B):**
Across any arbitrary indirect/recursive call sequence `frameSizes`, if the
initial stack pointer satisfies `stackLimit ≤ sp`, then
`execDynamicIndirectChain` either traps cleanly with `.stackOverflow` before
crossing `stackLimit`, or succeeds with a stack pointer `sp'` that preserves
the hardware invariant `stackLimit ≤ sp'`. -/
theorem dynamic_stack_check_preserves_limit (stackLimit : Nat)
    (frameSizes : List Nat) (sp : Nat) (hInit : stackLimit ≤ sp) :
    match execDynamicIndirectChain stackLimit frameSizes sp with
    | .stackOverflow => True
    | .ok sp' => stackLimit ≤ sp' := by
  induction frameSizes generalizing sp with
  | nil =>
      simp [execDynamicIndirectChain, hInit]
  | cons fSize rest ih =>
      by_cases hLt : sp < stackLimit + fSize
      · simp [execDynamicIndirectChain, execDynamicPrologueCheck, hLt]
      · simp only [execDynamicIndirectChain, execDynamicPrologueCheck, hLt,
                   ite_false]
        have hNext : stackLimit ≤ sp - fSize := by omega
        exact ih (sp - fSize) hNext

/-- **Theorem 3c (`canary_indirect_call_exceeding_contract_caught` — Negative
Canary):**
1. Under Method A, an unverified target function `badTarget = 99` whose peak
   stack usage (`128` bytes) violates `contract.wcetStack = 64` overflows a
   remaining budget of `64` bytes.
2. Under Method B, the dynamic prologue check deterministically catches the
   excess frame size (`128` bytes when `sp - stackLimit = 64`) and returns
   `.stackOverflow` before `sp` can underflow `stackLimit`. -/
theorem canary_indirect_call_exceeding_contract_caught :
    let peakStack : FnId → Nat := fun f => if f = 99 then 128 else 64
    evalIndirectCallStatic peakStack 1000 200 100 36 99 = .stackOverflow ∧
    execDynamicIndirectChain 800 [36, 128] 900 = .stackOverflow := by
  decide

-- ============================================================================
-- Axiom Footprint Audit (Zero `sorryAx`, Zero `Lean.ofReduceBool`)
-- ============================================================================

/--
info: 'Anneal.Round2Track3.public_store_preserves_private_spills_and_saved_regs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms public_store_preserves_private_spills_and_saved_regs

/--
info: 'Anneal.Round2Track3.canary_unbounded_ptr_offset_corrupts_spill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary_unbounded_ptr_offset_corrupts_spill

/--
info: 'Anneal.Round2Track3.canary_adjacent_exposed_allocs_ambiguous_at_one_past_end' does not depend on any axioms
-/
#guard_msgs in
#print axioms canary_adjacent_exposed_allocs_ambiguous_at_one_past_end

/--
info: 'Anneal.Round2Track3.guard_byte_eliminates_pnvi_boundary_ambiguity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms guard_byte_eliminates_pnvi_boundary_ambiguity

/--
info: 'Anneal.Round2Track3.canary_subreg_partial_write_clobbers_64bit' does not depend on any axioms
-/
#guard_msgs in
#print axioms canary_subreg_partial_write_clobbers_64bit

/--
info: 'Anneal.Round2Track3.subreg_and_callee_saved_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms subreg_and_callee_saved_sound

/--
info: 'Anneal.Round2Track3.subreg_checkRegAlloc_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms subreg_checkRegAlloc_sound

/--
info: 'Anneal.Round2Track3.callee_saved_preserved_of_checkRegAlloc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms callee_saved_preserved_of_checkRegAlloc

/--
info: 'Anneal.Round2Track3.canary_subreg_width_mismatch_rejected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary_subreg_width_mismatch_rejected

/--
info: 'Anneal.Round2Track3.canary_callee_save_protocol_adequacy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary_callee_save_protocol_adequacy

/--
info: 'Anneal.Round2Track3.indirect_call_static_contract_no_overflow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms indirect_call_static_contract_no_overflow

/--
info: 'Anneal.Round2Track3.dynamic_stack_check_preserves_limit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms dynamic_stack_check_preserves_limit

/--
info: 'Anneal.Round2Track3.canary_indirect_call_exceeding_contract_caught' does not depend on any axioms
-/
#guard_msgs in
#print axioms canary_indirect_call_exceeding_contract_caught

end Anneal.Round2Track3
