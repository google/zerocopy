/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Post-Link `--gc-sections` `.debug_anneal_sites` Tombstone Protocol,
# Dual-Query `stdarch` Interception, and `SpecCone` Pointee-Validity Closure
# (`Init.*`-Only Lean `v4.34.1`)

This self-contained `Init.*`-only Lean `v4.34.1` module mechanizes nine
theorems (`0` `sorry`, `0` custom axioms) covering the three compiler/linker
seams investigated in this report:

1. `non_debug_gc_sections_bfd_loss_and_lld_phantom_span_unsound`:
   Non-`.debug_*`, non-`SHF_EXCLUDE` `.anneal.asm_sites,"",@progbits` fails on
   both major ELF linker families under `rustc`'s default `-Wl,--gc-sections`:
   GNU `ld.bfd` sweeps non-`SEC_DEBUGGING` sections to `0` bytes (`100%`
   attestation loss), whereas `rust-lld` and `ld.mold` retain records from
   GC-discarded functions and resolve `STT_SECTION + r_addend` to phantom
   non-zero-length spans `[r_addend_s, r_addend_e)`.
2. `postlink_debug_tombstone_filter_sound_and_complete`:
   Emitting `.debug_anneal_sites,"",@progbits` exploits ELF `.debug_*` GC root
   preservation and DWARF dead-section tombstoning (`0`, `1`, `UINT64_MAX`):
   `acceptDebugSiteRecord` rejects `100%` of GC-discarded / ICF-tombstoned
   records across all tombstone encodings while retaining `100%` of surviving
   `PT_LOAD_X` records and recovering exact post-`R_RISCV_RELAX` byte slices via
   `ADD64`/`SUB64` span lengths.
3. `unannotated_icf_leader_absorbs_debug_record_unless_sym_gated`:
   Under `--icf=all`, folding an attested Rust section into an unannotated C
   leader tombstones the follower's `.debug_anneal_sites` entry, leaving zero
   surviving records at the live symbol VA unless gated by
   `verifyLiveAsmSymbolCoverage` (which rejects unannotated absorption while
   admitting verified-twin ICF folding).
4. `gc_relax_icf_postlink_composition_sound`:
   Master post-link soundness composition across `--gc-sections` x
   `R_RISCV_RELAX` x `--icf=all`: combining `filterDebugSiteRecords` with
   `verifyLiveAsmSymbolCoverage` guarantees that every live `PT_LOAD_X` `asm!`
   function executes spec-verified post-relaxation machine bytes.
5. `local_only_query_misses_extern_stdarch_and_dual_query_complete`:
   Hooking `providers.queries.optimized_mir` (`LocalDefId`) alone misses
   prebuilt sysroot `libcore` `stdarch` `asm!` (`__writeeflags` `RFLAGS.DF = 1`
   UB, `_mm256_stream_si256`, `_bittestandset64`), whereas hooking both
   `queries.optimized_mir` and `extern_queries.optimized_mir` with an
   idempotence guard achieves `100%` single-wrap coverage without
   double-wrapping instrumented upstream `.rmeta` crates.
6. `ref_pointee_niche_omission_unsound`:
   Constructive refutation of `Adt`-only `SpecCone` traversal (`v1`): mutating
   `BoundedByte(NonZeroU8)` to `BoundedByte(u8)` behind `r: &BoundedByte`
   preserves `hot_ref`'s tokens and `&BoundedByte`'s 8-byte pointer layout while
   widening valid inputs to `*r = 0` and invalidating `TotalMirAsmEquiv`.
7. `compound_tuple3_fnptr_and_extern_static_omission_unsound`:
   Constructive refutations when `SpecConeEq` omits 3-tuple (`BackendRepr::Memory`)
   element niches, `ty::FnPtr` argument `PassMode` ABI, or `extern` `Static`
   type/symbol metadata.
8. `evalMir_wellClosedTypeGraph_noninterference`:
   Full type-graph (`ty.walk()`) and pointee-validity operational
   non-interference for `evalMir`.
9. `wellClosedSpecConeEq_preserves_totalMirAsmEquiv`:
   End-to-end relational transfer of `TotalMirAsmEquiv` across arbitrary
   out-of-cone edits and crate-global `AllocId` renumberings under
   `WellClosedSpecConeEq`.
-/

namespace PostLinkGcTombstoneAndSpecConeClosure

/-! ## Part I: `--gc-sections` x `.debug_anneal_sites` Tombstones x `R_RISCV_RELAX` x `--icf=all` -/

def uint64Max : Nat := 18446744073709551615

/-- Pre-link relocation record emitted for one `TerminatorKind::InlineAsm` site. -/
structure PreLinkSiteReloc where
  siteId : Nat
  sessionNonce : Nat
  sectionAlive : Bool
  sectionBaseVA : Nat
  startAddend : Nat
  endAddend : Nat
  usesSymbolReloc : Bool
  usesAddSubSpanReloc : Bool
  deriving DecidableEq, Repr

/-- Post-link 7-word `.anneal.asm_sites` / `.debug_anneal_sites` record header. -/
structure PostLinkSiteRecord where
  startVA : Nat
  endVA : Nat
  relocatedSpanLen : Nat
  siteId : Nat
  sessionNonce : Nat
  deriving DecidableEq, Repr

inductive NonDebugLinkerKind where
  | bfdGc
  | lldOrMoldSttSection
  deriving DecidableEq, Repr

/-- Relocation semantics of non-`.debug_*` `.anneal.asm_sites,"",@progbits`
    under `-Wl,--gc-sections`:
    - GNU `ld.bfd` discards the entire non-`SEC_DEBUGGING` section (`[]`);
    - `rust-lld` / `ld.mold` retain all records and evaluate `0 + r_addend` on
      `STT_SECTION` relocations (`!usesSymbolReloc`) into GC-discarded sections. -/
def relocateNonDebugSection
    (lk : NonDebugLinkerKind)
    (inputs : List PreLinkSiteReloc) : List PostLinkSiteRecord :=
  match lk with
  | .bfdGc => []
  | .lldOrMoldSttSection =>
      inputs.map fun r =>
        let base := if r.sectionAlive then r.sectionBaseVA else 0
        let sVA :=
          if r.sectionAlive then base + r.startAddend
          else if r.usesSymbolReloc then 0 else r.startAddend
        let eVA :=
          if r.sectionAlive then base + r.endAddend
          else if r.usesSymbolReloc then 0 else r.endAddend
        let sLen :=
          if !r.sectionAlive && r.usesAddSubSpanReloc then 0
          else r.endAddend - r.startAddend
        { startVA := sVA, endVA := eVA, relocatedSpanLen := sLen,
          siteId := r.siteId, sessionNonce := r.sessionNonce }

def naiveSpanNonEmpty (r : PostLinkSiteRecord) : Bool :=
  decide (r.startVA < r.endVA)

/-- Theorem 1: Non-`.debug_*` `.anneal.asm_sites,"",@progbits` fractures under
    `--gc-sections`: `ld.bfd` loses `100%` of live records, whereas `lld`/`mold`
    resolve a dead x86-64/AArch64 function (`startAddend = 4, endAddend = 7`) to
    a phantom non-empty `[0x4, 0x7)` span (`naiveSpanNonEmpty = true`). -/
theorem non_debug_gc_sections_bfd_loss_and_lld_phantom_span_unsound :
    let deadRec : PreLinkSiteReloc := {
      siteId := 0x1111, sessionNonce := 0xAA, sectionAlive := false,
      sectionBaseVA := 0, startAddend := 4, endAddend := 7,
      usesSymbolReloc := false, usesAddSubSpanReloc := false
    }
    let liveRec : PreLinkSiteReloc := {
      siteId := 0x2222, sessionNonce := 0xAA, sectionAlive := true,
      sectionBaseVA := 0x201120, startAddend := 7, endAddend := 10,
      usesSymbolReloc := false, usesAddSubSpanReloc := false
    }
    let bfdOut := relocateNonDebugSection .bfdGc [deadRec, liveRec]
    let lldOut := relocateNonDebugSection .lldOrMoldSttSection [deadRec, liveRec]
    bfdOut = [] ∧
    (∃ r ∈ lldOut, r.siteId = 0x1111 ∧ r.startVA = 4 ∧ r.endVA = 7 ∧
      naiveSpanNonEmpty r = true) := by
  decide

/-- Executable `PT_LOAD` (`PF_X`) / `SHF_ALLOC | SHF_EXECINSTR` segment image. -/
structure ExecSegment where
  vaddr : Nat
  bytes : List UInt8
  deriving DecidableEq, Repr

def WellPlacedExecSegments (segs : List ExecSegment) : Prop :=
  ∀ seg ∈ segs,
    0x1000 <= seg.vaddr ∧
    seg.vaddr + seg.bytes.length < uint64Max

def inSingleExecSeg (seg : ExecSegment) (sVA eVA : Nat) : Bool :=
  decide (seg.vaddr <= sVA) &&
  decide (sVA <= eVA) &&
  decide (eVA <= seg.vaddr + seg.bytes.length)

def inExecSegments (segs : List ExecSegment) (sVA eVA : Nat) : Bool :=
  segs.any (fun seg => inSingleExecSeg seg sVA eVA)

/-- DWARF dead-section tombstone sentinels (`0` default across `ld.bfd 2.47`,
    `rust-lld 21..23`, and `ld.mold 2.42.1`; `1` legacy DWARF4 `.debug_loc` /
    `.debug_ranges`; `uint64Max` `-z dead-reloc-in-nonalloc=...=0xffffffffffffffff`). -/
def isDwarfTombstone (va : Nat) : Bool :=
  (va == 0) || (va == 1) || (va == uint64Max)

def acceptDebugSiteRecord (segs : List ExecSegment) (r : PostLinkSiteRecord) : Bool :=
  (!isDwarfTombstone r.startVA) &&
  (!isDwarfTombstone r.endVA) &&
  inExecSegments segs r.startVA r.endVA &&
  decide (r.endVA - r.startVA = r.relocatedSpanLen)

def filterDebugSiteRecords
    (segs : List ExecSegment)
    (recs : List PostLinkSiteRecord) : List PostLinkSiteRecord :=
  recs.filter (acceptDebugSiteRecord segs)

/-- Byte-shrinking relaxation model (`R_RISCV_RELAX` / `R_RISCV_ALIGN`). -/
inductive SectionAtom where
  | fixed (bytes : List UInt8)
  | relaxable (preBytes postBytes : List UInt8)
  deriving DecidableEq, Repr

def atomPreBytes : SectionAtom -> List UInt8
  | .fixed bs => bs
  | .relaxable pre _ => pre

def atomPostBytes : SectionAtom -> List UInt8
  | .fixed bs => bs
  | .relaxable _ post => post

def atomWellFormed : SectionAtom -> Bool
  | .fixed _ => true
  | .relaxable pre post => decide (post.length <= pre.length)

def atomsWellFormed (atoms : List SectionAtom) : Bool :=
  atoms.all atomWellFormed

noncomputable def postSectionBytes : List SectionAtom -> List UInt8
  | [] => []
  | a :: rest => atomPostBytes a ++ postSectionBytes rest

noncomputable def postAtomOffset (atoms : List SectionAtom) (idx : Nat) : Nat :=
  (postSectionBytes (atoms.take idx)).length

def extractSlice (bytes : List UInt8) (off len : Nat) : List UInt8 :=
  (bytes.drop off).take len

def extractSegmentBytes (seg : ExecSegment) (sVA len : Nat) : List UInt8 :=
  extractSlice seg.bytes (sVA - seg.vaddr) len

def relocateTombstonedRecord
    (tombVal spanLen siteId nonce : Nat) : PostLinkSiteRecord :=
  { startVA := tombVal, endVA := tombVal, relocatedSpanLen := spanLen,
    siteId := siteId, sessionNonce := nonce }

noncomputable def relocateLiveAtomRecord
    (segBaseVA : Nat) (atoms : List SectionAtom) (idx siteId nonce : Nat) :
    PostLinkSiteRecord :=
  let sVA := segBaseVA + postAtomOffset atoms idx
  let eVA := segBaseVA + postAtomOffset atoms (idx + 1)
  { startVA := sVA, endVA := eVA, relocatedSpanLen := eVA - sVA,
    siteId := siteId, sessionNonce := nonce }

private theorem postSectionBytes_append (xs ys : List SectionAtom) :
    postSectionBytes (xs ++ ys) = postSectionBytes xs ++ postSectionBytes ys := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp [postSectionBytes, ih, List.append_assoc]

private theorem take_succ_eq_snoc (atoms : List SectionAtom) (idx : Nat) (a : SectionAtom)
    (hget : atoms[idx]? = some a) :
    atoms.take (idx + 1) = atoms.take idx ++ [a] := by
  induction atoms generalizing idx with
  | nil => simp at hget
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp at hget
          subst hget
          rfl
      | succ k =>
          simp only [List.getElem?_cons_succ] at hget
          simp [List.take_succ_cons, ih k hget]

private theorem postSectionBytes_split_at
    (atoms : List SectionAtom) (idx : Nat) (a : SectionAtom)
    (hget : atoms[idx]? = some a) :
    postSectionBytes atoms =
      postSectionBytes (atoms.take idx) ++ atomPostBytes a ++
      postSectionBytes (atoms.drop (idx + 1)) := by
  have hlist : atoms = atoms.take (idx + 1) ++ atoms.drop (idx + 1) :=
    (List.take_append_drop (idx + 1) atoms).symm
  conv => lhs; rw [hlist]
  rw [take_succ_eq_snoc atoms idx a hget, postSectionBytes_append, postSectionBytes_append]
  simp [postSectionBytes, List.append_assoc]

private theorem extractSlice_mid (pre mid suf : List UInt8) :
    extractSlice (pre ++ mid ++ suf) pre.length mid.length = mid := by
  unfold extractSlice
  rw [List.append_assoc, List.drop_left, List.take_left]

private theorem any_true_of_mem {α : Type} (p : α -> Bool) (xs : List α) (x : α)
    (hmem : x ∈ xs) (hp : p x = true) : xs.any p = true := by
  induction xs with
  | nil => cases hmem
  | cons hd tl ih =>
      cases hmem with
      | head => simp [List.any_cons, hp]
      | tail _ htl => simp [List.any_cons, ih htl]

/-- Theorem 2: Post-link `.debug_anneal_sites` tombstone filter soundness and
    completeness across all three DWARF tombstone encodings (`0`, `1`,
    `uint64Max`) and `R_RISCV_RELAX` byte-shrinking `SectionAtom` streams. -/
theorem postlink_debug_tombstone_filter_sound_and_complete
    (segs : List ExecSegment)
    (h_placed : WellPlacedExecSegments segs) :
    (∀ tombVal spanLen siteId nonce,
      tombVal ∈ [0, 1, uint64Max] ->
      acceptDebugSiteRecord segs
        (relocateTombstonedRecord tombVal spanLen siteId nonce) = false) ∧
    (∀ seg atoms idx a siteId nonce,
      seg ∈ segs ->
      seg.bytes = postSectionBytes atoms ->
      atoms[idx]? = some a ->
      let r := relocateLiveAtomRecord seg.vaddr atoms idx siteId nonce
      acceptDebugSiteRecord segs r = true ∧
      r.endVA - r.startVA = (atomPostBytes a).length ∧
      extractSegmentBytes seg r.startVA (r.endVA - r.startVA) = atomPostBytes a) := by
  refine ⟨?_, ?_⟩
  · intro tombVal spanLen siteId nonce htomb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htomb
    rcases htomb with rfl | rfl | rfl <;>
      simp [acceptDebugSiteRecord, relocateTombstonedRecord, isDwarfTombstone]
  · intro seg atoms idx a siteId nonce hseg hbytes hget
    have hbounds := h_placed seg hseg
    have hsplit := postSectionBytes_split_at atoms idx a hget
    have hoff_succ :
        postAtomOffset atoms (idx + 1) =
          postAtomOffset atoms idx + (atomPostBytes a).length := by
      unfold postAtomOffset
      rw [take_succ_eq_snoc atoms idx a hget, postSectionBytes_append]
      simp [postSectionBytes]
    have htot_len :
        (postSectionBytes atoms).length =
          postAtomOffset atoms idx + (atomPostBytes a).length +
          (postSectionBytes (atoms.drop (idx + 1))).length := by
      rw [hsplit]
      simp [postAtomOffset, List.length_append, Nat.add_assoc]
    have h_seg_len : seg.bytes.length = (postSectionBytes atoms).length := by
      rw [hbytes]
    intro r
    have hs_not_tomb : isDwarfTombstone r.startVA = false := by
      unfold isDwarfTombstone r relocateLiveAtomRecord uint64Max
      unfold uint64Max at hbounds
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have he_not_tomb : isDwarfTombstone r.endVA = false := by
      unfold isDwarfTombstone r relocateLiveAtomRecord uint64Max
      unfold uint64Max at hbounds
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have h_in_single : inSingleExecSeg seg r.startVA r.endVA = true := by
      unfold inSingleExecSeg r relocateLiveAtomRecord
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have h_in_any : inExecSegments segs r.startVA r.endVA = true :=
      any_true_of_mem (fun sg => inSingleExecSeg sg r.startVA r.endVA) segs seg hseg h_in_single
    refine ⟨?_, ?_, ?_⟩
    · unfold acceptDebugSiteRecord
      rw [hs_not_tomb, he_not_tomb, h_in_any]
      simp [r, relocateLiveAtomRecord]
    · dsimp only [r, relocateLiveAtomRecord]
      omega
    · unfold extractSegmentBytes
      dsimp only [r, relocateLiveAtomRecord]
      have hsub1 :
          seg.vaddr + postAtomOffset atoms idx - seg.vaddr =
            postAtomOffset atoms idx := by omega
      have hsub2 :
          (seg.vaddr + postAtomOffset atoms (idx + 1)) -
            (seg.vaddr + postAtomOffset atoms idx) =
            (atomPostBytes a).length := by omega
      rw [hsub1, hsub2, hbytes, hsplit]
      exact extractSlice_mid
        (postSectionBytes (atoms.take idx))
        (atomPostBytes a)
        (postSectionBytes (atoms.drop (idx + 1)))

/-- Post-link live-symbol coverage gate preventing unannotated ICF leaders from
    silently absorbing attested `asm!` followers via DWARF ICF tombstoning. -/
structure ManifestAsmFn where
  fnSym : Nat
  relSiteOff : Nat
  deriving DecidableEq, Repr

def symInExec (segs : List ExecSegment) (va : Nat) : Bool :=
  (!isDwarfTombstone va) && inExecSegments segs va va

def verifyLiveAsmSymbolCoverage
    (segs : List ExecSegment)
    (symAddr : Nat -> Nat)
    (manifestFns : List ManifestAsmFn)
    (acceptedRecs : List PostLinkSiteRecord) : Bool :=
  manifestFns.all fun mf =>
    if symInExec segs (symAddr mf.fnSym) then
      acceptedRecs.any (fun r => r.startVA == symAddr mf.fnSym + mf.relSiteOff)
    else
      true

/-- Theorem 3: Constructive proof that when `--icf=all` folds an attested
    section (`rustFollower`, `fnSym = 2`) into an unannotated leader (`cLeader`,
    `fnSym = 1`) at `0x201120`, DWARF tombstoning zeroes `rustFollower`'s
    `.debug_anneal_sites` record (`[]`), which `verifyLiveAsmSymbolCoverage`
    deterministically catches (`= false`), whereas verified-twin ICF folding
    (`twinA` + `twinB`) passes (`= true`). -/
theorem unannotated_icf_leader_absorbs_debug_record_unless_sym_gated :
    let segs : List ExecSegment :=
      [{ vaddr := 0x201120, bytes := [0x48, 0x8d, 0x47, 0x09, 0xc3] }]
    let symAddr : Nat -> Nat := fun _ => 0x201120
    let manifestUnannotated : List ManifestAsmFn :=
      [{ fnSym := 2, relSiteOff := 0 }]
    let recsUnannotatedLeader : List PostLinkSiteRecord :=
      [relocateTombstonedRecord 0 4 7777 0xAA]
    let manifestVerifiedTwins : List ManifestAsmFn :=
      [{ fnSym := 1, relSiteOff := 0 }, { fnSym := 2, relSiteOff := 0 }]
    let recsVerifiedLeader : List PostLinkSiteRecord :=
      [ { startVA := 0x201120, endVA := 0x201124, relocatedSpanLen := 4,
          siteId := 0xAAAA, sessionNonce := 0xAA },
        relocateTombstonedRecord 0 4 0xBBBB 0xAA ]
    filterDebugSiteRecords segs recsUnannotatedLeader = [] ∧
    verifyLiveAsmSymbolCoverage segs symAddr manifestUnannotated
      (filterDebugSiteRecords segs recsUnannotatedLeader) = false ∧
    (filterDebugSiteRecords segs recsVerifiedLeader).length = 1 ∧
    verifyLiveAsmSymbolCoverage segs symAddr manifestVerifiedTwins
      (filterDebugSiteRecords segs recsVerifiedLeader) = true := by
  decide

/-- Extract code slice at `[startVA, endVA)` from the first matching `ExecSegment`. -/
noncomputable def lookupExecSlice : List ExecSegment -> Nat -> Nat -> Option (List UInt8)
  | [], _, _ => none
  | seg :: rest, sVA, eVA =>
      if inSingleExecSeg seg sVA eVA then
        some (extractSegmentBytes seg sVA (eVA - sVA))
      else
        lookupExecSlice rest sVA eVA

/-- Post-link record verifier checking authorized session nonces and the
    post-relaxation allowed byte-encoding envelope (`RelocRelaxEnvelope`). -/
noncomputable def verifyPostLinkSlice
    (validNonces : List Nat)
    (allowedPostBytes : Nat -> List (List UInt8))
    (segs : List ExecSegment)
    (r : PostLinkSiteRecord) : Bool :=
  validNonces.elem r.sessionNonce &&
  match lookupExecSlice segs r.startVA r.endVA with
  | none => false
  | some bs => (allowedPostBytes r.siteId).elem bs

def AddressObliviousSiteSound
    (execSlice : List UInt8 -> Nat -> Nat)
    (spec : Nat -> Nat -> Prop)
    (segs : List ExecSegment)
    (siteVA siteEndVA : Nat) : Prop :=
  ∃ bs, lookupExecSlice segs siteVA siteEndVA = some bs ∧
    ∀ x, spec x (execSlice bs x)

private theorem elem_true_mem_generic {α : Type} [BEq α] [LawfulBEq α]
    {x : α} {xs : List α} (h : xs.elem x = true) : x ∈ xs := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
      unfold List.elem at h
      cases hbeq : (x == hd) with
      | true =>
          have heq : x = hd := eq_of_beq hbeq
          subst heq
          exact List.Mem.head tl
      | false =>
          rw [hbeq] at h
          exact List.Mem.tail hd (ih h)

private theorem all_mem_true {α : Type} (p : α -> Bool) (xs : List α)
    (hall : xs.all p = true) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons hd tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      intro x hx
      cases hx with
      | head => exact hall.1
      | tail _ htl => exact ih hall.2 x htl

private theorem any_true_exists {α : Type} (p : α -> Bool) (xs : List α)
    (hany : xs.any p = true) : ∃ x ∈ xs, p x = true := by
  induction xs with
  | nil => cases hany
  | cons hd tl ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hany
      cases hany with
      | inl hhd => exact ⟨hd, List.Mem.head tl, hhd⟩
      | inr htl =>
          rcases ih htl with ⟨w, hw, hpw⟩
          exact ⟨w, List.Mem.tail hd hw, hpw⟩

/-- Theorem 4: Universal Post-Link Composition Across `--gc-sections` x
    `R_RISCV_RELAX` x `--icf=all`.
    Whenever every surviving `.debug_anneal_sites` record in
    `filterDebugSiteRecords` passes `verifyPostLinkSlice` and
    `verifyLiveAsmSymbolCoverage` holds, every live `PT_LOAD_X` `asm!` function
    in the manifest (including `--icf=all` followers whose own records were
    DWARF-tombstoned onto a verified leader!) executes an authorized
    post-relaxation byte slice satisfying its `AddressObliviousSiteSound`
    contract, while zero tombstoned dead records are admitted. -/
theorem gc_relax_icf_postlink_composition_sound
    (segs : List ExecSegment)
    (validNonces : List Nat)
    (allowedPostBytes : Nat -> List (List UInt8))
    (execSlice : List UInt8 -> Nat -> Nat)
    (siteSpec : Nat -> Nat -> Nat -> Prop)
    (h_envelope_sound :
      ∀ sId bs, bs ∈ allowedPostBytes sId -> ∀ x, siteSpec sId x (execSlice bs x))
    (symAddr : Nat -> Nat)
    (manifestFns : List ManifestAsmFn)
    (rawDebugRecs : List PostLinkSiteRecord)
    (h_slices_ok :
      (filterDebugSiteRecords segs rawDebugRecs).all
        (verifyPostLinkSlice validNonces allowedPostBytes segs) = true)
    (h_sym_cov :
      verifyLiveAsmSymbolCoverage segs symAddr manifestFns
        (filterDebugSiteRecords segs rawDebugRecs) = true) :
    (∀ r ∈ filterDebugSiteRecords segs rawDebugRecs,
      isDwarfTombstone r.startVA = false ∧ isDwarfTombstone r.endVA = false) ∧
    (∀ mf ∈ manifestFns,
      symInExec segs (symAddr mf.fnSym) = true ->
      ∃ r ∈ filterDebugSiteRecords segs rawDebugRecs,
        r.startVA = symAddr mf.fnSym + mf.relSiteOff ∧
        r.sessionNonce ∈ validNonces ∧
        AddressObliviousSiteSound execSlice (siteSpec r.siteId) segs r.startVA r.endVA) := by
  let accepted := filterDebugSiteRecords segs rawDebugRecs
  refine ⟨?_, ?_⟩
  · intro r hr
    have hacc : acceptDebugSiteRecord segs r = true := (List.mem_filter.mp hr).2
    unfold acceptDebugSiteRecord at hacc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hacc
    exact ⟨hacc.1.1.1, hacc.1.1.2⟩
  · intro mf hmf hlive
    unfold verifyLiveAsmSymbolCoverage at h_sym_cov
    have hcov_mf := all_mem_true _ manifestFns h_sym_cov mf hmf
    rw [hlive] at hcov_mf
    simp only [↓reduceIte] at hcov_mf
    rcases any_true_exists _ accepted hcov_mf with ⟨r, hr_mem, hr_va_beq⟩
    have hr_va : r.startVA = symAddr mf.fnSym + mf.relSiteOff := eq_of_beq hr_va_beq
    have hv : verifyPostLinkSlice validNonces allowedPostBytes segs r = true :=
      all_mem_true (verifyPostLinkSlice validNonces allowedPostBytes segs)
        accepted h_slices_ok r hr_mem
    unfold verifyPostLinkSlice at hv
    cases h_nonce : validNonces.elem r.sessionNonce
    · rw [h_nonce] at hv; cases hv
    · cases h_lu : lookupExecSlice segs r.startVA r.endVA with
      | none =>
          rw [h_nonce, h_lu] at hv; cases hv
      | some bs =>
          rw [h_nonce, h_lu] at hv
          simp only [Bool.true_and] at hv
          have hbs_mem : bs ∈ allowedPostBytes r.siteId := elem_true_mem_generic hv
          refine ⟨r, hr_mem, hr_va, elem_true_mem_generic h_nonce, bs, h_lu, ?_⟩
          intro x
          exact h_envelope_sound r.siteId bs hbs_mem x

/-! ## Part II: Dual-Query (`queries` + `extern_queries`) `stdarch` Interception -/

inductive CrateOrigin where
  | localCrate
  | prebuiltSysrootCore
  | instrumentedUpstreamRmeta
  deriving DecidableEq, Repr

inductive AsmHazardKind where
  | safePure
  | nonTemporalStreamStore
  | setDirectionFlagDF
  deriving DecidableEq, Repr

structure MonomorphizedAsmItem where
  defId : Nat
  origin : CrateOrigin
  hazard : AsmHazardKind
  wrapCount : Nat
  deriving DecidableEq, Repr

/-- `v1` `LocalDefId`-only query hook (`providers.queries.optimized_mir` only). -/
def rewriteLocalQueryOnly (item : MonomorphizedAsmItem) : MonomorphizedAsmItem :=
  match item.origin with
  | .localCrate =>
      if item.wrapCount == 0 then { item with wrapCount := 1 } else item
  | .prebuiltSysrootCore | .instrumentedUpstreamRmeta => item

/-- `v2` Dual-query hook (`providers.queries.optimized_mir` +
    `providers.extern_queries.optimized_mir` with idempotence guard). -/
def rewriteDualQueriesIdempotent (item : MonomorphizedAsmItem) : MonomorphizedAsmItem :=
  if item.wrapCount == 0 then
    { item with wrapCount := 1 }
  else
    item

def emittedToAttestationManifest (items : List MonomorphizedAsmItem) :
    List MonomorphizedAsmItem :=
  items.filter (fun i => i.wrapCount > 0)

def auditAttestedHazards (attested : List MonomorphizedAsmItem) : Bool :=
  attested.all (fun i => i.hazard != .setDirectionFlagDF)

/-- Theorem 5: `LocalDefId`-only `optimized_mir` misses prebuilt sysroot
    `libcore` `stdarch` `asm!` (`__writeeflags` `popfq` setting `RFLAGS.DF = 1`),
    falsely passing `auditAttestedHazards`, whereas `rewriteDualQueriesIdempotent`
    wraps `100%` of local, sysroot `stdarch`, and upstream `.rmeta` items with
    exact `wrapCount = 1` (zero double-wrapping) and rejects `__writeeflags`. -/
theorem local_only_query_misses_extern_stdarch_and_dual_query_complete :
    let localSite : MonomorphizedAsmItem :=
      { defId := 1, origin := .localCrate, hazard := .safePure, wrapCount := 0 }
    let upRmetaSite : MonomorphizedAsmItem :=
      { defId := 2, origin := .instrumentedUpstreamRmeta, hazard := .safePure, wrapCount := 1 }
    let stdarchStream : MonomorphizedAsmItem :=
      { defId := 3, origin := .prebuiltSysrootCore, hazard := .nonTemporalStreamStore, wrapCount := 0 }
    let stdarchWriteEflags : MonomorphizedAsmItem :=
      { defId := 4, origin := .prebuiltSysrootCore, hazard := .setDirectionFlagDF, wrapCount := 0 }
    let crateGraph := [localSite, upRmetaSite, stdarchStream, stdarchWriteEflags]
    let v1Out := crateGraph.map rewriteLocalQueryOnly
    let v2Out := crateGraph.map rewriteDualQueriesIdempotent
    (emittedToAttestationManifest v1Out).length = 2 ∧
    auditAttestedHazards (emittedToAttestationManifest v1Out) = true ∧
    (∀ it ∈ v2Out, it.wrapCount = 1) ∧
    (emittedToAttestationManifest v2Out).length = 4 ∧
    auditAttestedHazards (emittedToAttestationManifest v2Out) = false := by
  decide

/-! ## Part III: Complete `TyCtxt` Type-Graph & Pointee-Validity Closure (`SpecCone` v2) -/

inductive AByte where
  | uninit
  | init (val : Nat)
  deriving DecidableEq, Repr

def byteRefines (refB : AByte) (asmB : Nat) : Prop :=
  match refB with
  | .uninit => True
  | .init b => asmB = b

def bytesRefine (rbs : List AByte) (abs : List Nat) : Prop :=
  List.rec
    (motive := fun _ => List Nat -> Prop)
    (fun ys => match ys with | [] => True | _ :: _ => False)
    (fun rb _ ih ys =>
      match ys with
      | [] => False
      | ab :: abs' => byteRefines rb ab ∧ ih abs')
    rbs abs

inductive PassMode where
  | directReg
  | indirectStackPtr
  deriving DecidableEq, Repr

/-- Recursive type syntax covering `Adt`, `Ref`, `RawPtr`, `Slice`, `Array`,
    3-element `Tuple3` (`BackendRepr::Memory`), and `FnPtr`. -/
inductive Ty where
  | primU64
  | adt (adtId : Nat)
  | sharedRef (pointee : Ty)
  | rawPtr (pointee : Ty)
  | slice (elem : Ty)
  | array (elem : Ty) (len : Nat)
  | tuple3 (t0 t1 t2 : Ty)
  | fnPtr (sigId : Nat) (argTy : Ty) (retTy : Ty)

structure AdtSem where
  size : Nat
  align : Nat
  field0Off : Nat
  validRangeLo : Nat
  validRangeHi : Nat
  initByteMask : List Bool
  fieldTys : List Ty
  dropEffect : Nat

structure FnPtrAbiSem where
  argPassMode : PassMode
  canUnwind : Bool
  deriving DecidableEq, Repr

structure ExternStaticSem where
  linkSymbolId : Nat
  isMutable : Bool
  valTy : Ty

inductive Expr where
  | constVal (allocKey : Nat)
  | derefRefArg
  | tuple0Arg
  | callFnPtrArg (sub : Expr)
  | readExternStatic (statId : Nat)
  | callDirect (callee : Nat) (sub : Expr)

structure FnSem where
  argRefTy : Ty
  argTupleTy : Ty
  argFnPtrTy : Ty
  retAdtId : Nat
  body : Expr

structure CrateEnvV2 where
  fns : Nat -> FnSem
  adts : Nat -> AdtSem
  fnPtrAbis : Nat -> FnPtrAbiSem
  externStatics : Nat -> ExternStaticSem
  externSymbolVals : Nat -> Nat
  constAllocs : Nat -> Nat
  rawAllocIds : Nat -> Nat

structure InputV2 where
  refDerefVal : Nat
  tupleElem0Val : Nat
  fnPtrCodeBehavior : PassMode -> Nat -> Nat

inductive MirOutV2 where
  | invalidInput
  | returned (acc : Nat) (structBytes : List AByte) (dropLog : Nat)
  | outOfFuel
  deriving DecidableEq, Repr

inductive IsaOutV2 where
  | halted (acc : Nat) (structBytes : List Nat) (dropLog : Nat)
  | trap
  deriving DecidableEq, Repr

/-- Operational value-validity predicate enforced at function entry on arguments
    (including pointees of shared references `&T` and elements of compound
    `[T; N]` / `(T, u8, u8)` values). -/
noncomputable def checkScalarValid (env : CrateEnvV2) (ty : Ty) (v : Nat) : Bool :=
  match ty with
  | .primU64 => true
  | .adt id =>
      let a := env.adts id
      decide (a.validRangeLo <= v) && decide (v <= a.validRangeHi)
  | .sharedRef inner => checkScalarValid env inner v
  | .rawPtr _ => true
  | .slice _ => true
  | .array elem _ => checkScalarValid env elem v
  | .tuple3 t0 _ _ => checkScalarValid env t0 v
  | .fnPtr _ _ _ => true

def buildMaskedBytes (val : Nat) (mask : List Bool) : List AByte :=
  mask.map (fun isInit => if isInit then .init (val % 256) else .uninit)

noncomputable def evalExprV2 (fuel : Nat) (env : CrateEnvV2) (fnDef : FnSem) (inp : InputV2) :
    Expr -> Option Nat
  | .constVal k => some (env.constAllocs k)
  | .derefRefArg => some inp.refDerefVal
  | .tuple0Arg => some inp.tupleElem0Val
  | .callFnPtrArg sub =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
          match evalExprV2 fuel' env fnDef inp sub with
          | none => none
          | some x =>
              match fnDef.argFnPtrTy with
              | .fnPtr sigId _ _ =>
                  let abi := env.fnPtrAbis sigId
                  some (inp.fnPtrCodeBehavior abi.argPassMode x)
              | _ => some x
  | .readExternStatic statId =>
      let st := env.externStatics statId
      some (env.externSymbolVals st.linkSymbolId)
  | .callDirect callee sub =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
          match evalExprV2 fuel' env fnDef inp sub with
          | none => none
          | some v =>
              let cDef := env.fns callee
              evalExprV2 fuel' env cDef { inp with refDerefVal := v } cDef.body

noncomputable def evalMirV2 (fuel : Nat) (env : CrateEnvV2) (fnId : Nat) (inp : InputV2) :
    MirOutV2 :=
  let fd := env.fns fnId
  if !(checkScalarValid env fd.argRefTy inp.refDerefVal &&
       checkScalarValid env fd.argTupleTy inp.tupleElem0Val) then
    .invalidInput
  else
    match evalExprV2 fuel env fd inp fd.body with
    | none => .outOfFuel
    | some acc =>
        let retAdt := env.adts fd.retAdtId
        .returned acc (buildMaskedBytes acc retAdt.initByteMask) retAdt.dropEffect

def TotalMirAsmEquiv
    (fuel : Nat) (env : CrateEnvV2) (refId : Nat) (opt : InputV2 -> IsaOutV2) : Prop :=
  ∀ inp,
    match evalMirV2 fuel env refId inp with
    | .invalidInput => True
    | .outOfFuel => False
    | .returned acc rBytes d =>
        ∃ aBytes, opt inp = .halted acc aBytes d ∧ bytesRefine rBytes aBytes

/-- Legacy `v1` `Adt`-only cone equality: compares `fns`, `constAllocs`, and
    ONLY those `adtId`s reached directly as top-level `Ty.adt id` parameters or
    returns (never traversing inside `Ty.sharedRef`, `Ty.tuple3`, `Ty.array`,
    `Ty.fnPtr`, or `externStatics`!). -/
def AdtOnlyConeEq (p1 p2 : CrateEnvV2) (fnIds directAdtIds allocKeys : List Nat) : Prop :=
  (∀ f ∈ fnIds, p1.fns f = p2.fns f) ∧
  (∀ a ∈ directAdtIds, p1.adts a = p2.adts a) ∧
  (∀ k ∈ allocKeys, p1.constAllocs k = p2.constAllocs k)

def baseAdtU8 : AdtSem := {
  size := 1, align := 1, field0Off := 0,
  validRangeLo := 0, validRangeHi := 255,
  initByteMask := [true], fieldTys := [], dropEffect := 0
}

def baseEnvV2 : CrateEnvV2 := {
  fns := fun _ => {
    argRefTy := .sharedRef (.adt 1),
    argTupleTy := .tuple3 (.adt 2) .primU64 .primU64,
    argFnPtrTy := .fnPtr 0 (.adt 3) .primU64,
    retAdtId := 0,
    body := .derefRefArg
  },
  adts := fun _ => baseAdtU8,
  fnPtrAbis := fun _ => { argPassMode := .directReg, canUnwind := false },
  externStatics := fun _ => { linkSymbolId := 10, isMutable := false, valTy := .primU64 },
  externSymbolVals := fun sym => if sym = 10 then 42 else 999,
  constAllocs := fun _ => 7,
  rawAllocIds := fun k => k
}

/-- Theorem 6 (`ref_pointee_niche_omission_unsound`):
    In `hot_ref(r: &BoundedByte)`, `&BoundedByte` is `Ty.sharedRef (.adt 1)`, so
    `directAdtIds = [0]` (only `retAdtId = 0`, never `1`). Widening `adt 1` from
    `NonZeroU8` (`1..255`) in `p1` to `u8` (`0..255`) in `p2` satisfies
    `AdtOnlyConeEq p1 p2 [0] [0] []` with identical `hot_ref` MIR, yet breaks
    `TotalMirAsmEquiv` when `opt` traps on `*r = 0`! -/
theorem ref_pointee_niche_omission_unsound :
    ∃ (p1 p2 : CrateEnvV2) (opt : InputV2 -> IsaOutV2),
      AdtOnlyConeEq p1 p2 [0] [0] [] ∧
      TotalMirAsmEquiv 1 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 1 p2 0 opt := by
  let p1 : CrateEnvV2 := {
    baseEnvV2 with
    adts := fun id =>
      if id == 1 then { baseAdtU8 with validRangeLo := 1, validRangeHi := 255 }
      else baseAdtU8
  }
  let p2 := baseEnvV2
  let opt : InputV2 -> IsaOutV2 := fun inp =>
    if inp.refDerefVal = 0 then .trap
    else .halted inp.refDerefVal [inp.refDerefVal % 256] 0
  refine ⟨p1, p2, opt, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro f hf; simp at hf; subst hf; rfl
    · intro a ha; simp at ha; subst ha; rfl
    · intro k hk; cases hk
  · rintro ⟨rVal, tVal, fpBeh⟩
    change
      match evalMirV2 1 p1 0 ⟨rVal, tVal, fpBeh⟩ with
      | .invalidInput => True
      | .outOfFuel => False
      | .returned acc rBytes d => ∃ aBytes, opt ⟨rVal, tVal, fpBeh⟩ = .halted acc aBytes d ∧ bytesRefine rBytes aBytes
    dsimp only [evalMirV2]
    cases hvalid :
        (checkScalarValid p1 (p1.fns 0).argRefTy rVal &&
         checkScalarValid p1 (p1.fns 0).argTupleTy tVal) with
    | false =>
        trivial
    | true =>
        have hr_ge1 : 1 <= rVal := by
          simp [p1, baseEnvV2, baseAdtU8, checkScalarValid] at hvalid
          exact hvalid.1.1
        have hnz : rVal ≠ 0 := by omega
        change ∃ aBytes, opt ⟨rVal, tVal, fpBeh⟩ = .halted rVal aBytes 0 ∧ bytesRefine [AByte.init (rVal % 256)] aBytes
        exact ⟨[rVal % 256], by simp [opt, hnz], by simp [bytesRefine, byteRefines]⟩
  · intro h_bad
    let wInp : InputV2 := {
      refDerefVal := 0, tupleElem0Val := 1, fnPtrCodeBehavior := fun _ x => x
    }
    have hw := h_bad wInp
    dsimp only [evalMirV2, p2, baseEnvV2, baseAdtU8, checkScalarValid, evalExprV2, opt] at hw
    rcases hw with ⟨aBytes, h_opt, _⟩
    cases h_opt

/-- Theorem 7: Constructive refutations when `SpecConeEq` omits:
    (a) 3-tuple (`BackendRepr::Memory`) inner element niches (`V15`),
    (b) `ty::FnPtr` argument `PassMode` ABI (`V16`), or
    (c) `extern` `Static` `link_name` / symbol binding (`V17`). -/
theorem compound_tuple3_fnptr_and_extern_static_omission_unsound :
    -- (a) 3-tuple element niche (`adt 2` inside `.tuple3 (.adt 2) .primU64 .primU64`)
    (∃ (p1 p2 : CrateEnvV2) (opt : InputV2 -> IsaOutV2),
      AdtOnlyConeEq p1 p2 [0] [0, 1] [] ∧
      TotalMirAsmEquiv 1 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 1 p2 0 opt) ∧
    -- (b) `FnPtr` `PassMode` ABI (`Direct` vs `Indirect`)
    (∃ (p1 p2 : CrateEnvV2) (opt : InputV2 -> IsaOutV2),
      AdtOnlyConeEq p1 p2 [0] [0, 1, 2, 3] [] ∧
      TotalMirAsmEquiv 2 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 2 p2 0 opt) ∧
    -- (c) `extern "C" { static ... }` `#[link_name]` / foreign symbol binding
    (∃ (p1 p2 : CrateEnvV2) (opt : InputV2 -> IsaOutV2),
      AdtOnlyConeEq p1 p2 [0] [0, 1, 2, 3] [] ∧
      p1.externSymbolVals = p2.externSymbolVals ∧
      TotalMirAsmEquiv 1 p1 0 opt ∧
      ¬ TotalMirAsmEquiv 1 p2 0 opt) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) Tuple3 niche witness
    let p1 : CrateEnvV2 := {
      baseEnvV2 with
      adts := fun id =>
        if id == 2 then { baseAdtU8 with validRangeLo := 1, validRangeHi := 255 }
        else baseAdtU8
    }
    let p2 := baseEnvV2
    let opt : InputV2 -> IsaOutV2 := fun inp =>
      if inp.tupleElem0Val = 0 then .trap
      else .halted inp.refDerefVal [inp.refDerefVal % 256] 0
    refine ⟨p1, p2, opt, ?_, ?_, ?_⟩
    · refine ⟨fun f hf => ?_, fun a ha => ?_, fun k hk => by cases hk⟩
      · simp at hf; subst hf; rfl
      · simp at ha; rcases ha with rfl | rfl <;> rfl
    · rintro ⟨rVal, tVal, fpBeh⟩
      change
        match evalMirV2 1 p1 0 ⟨rVal, tVal, fpBeh⟩ with
        | .invalidInput => True
        | .outOfFuel => False
        | .returned acc rBytes d => ∃ aBytes, opt ⟨rVal, tVal, fpBeh⟩ = .halted acc aBytes d ∧ bytesRefine rBytes aBytes
      dsimp only [evalMirV2]
      cases hvalid :
          (checkScalarValid p1 (p1.fns 0).argRefTy rVal &&
           checkScalarValid p1 (p1.fns 0).argTupleTy tVal) with
      | false =>
          trivial
      | true =>
          have ht_ge1 : 1 <= tVal := by
            simp [p1, baseEnvV2, baseAdtU8, checkScalarValid] at hvalid
            exact hvalid.2.1
          have hnz : tVal ≠ 0 := by omega
          change ∃ aBytes, opt ⟨rVal, tVal, fpBeh⟩ = .halted rVal aBytes 0 ∧ bytesRefine [AByte.init (rVal % 256)] aBytes
          exact ⟨[rVal % 256], by simp [opt, hnz], by simp [bytesRefine, byteRefines]⟩
    · intro h_bad
      have hw := h_bad { refDerefVal := 1, tupleElem0Val := 0, fnPtrCodeBehavior := fun _ x => x }
      dsimp only [evalMirV2, p2, baseEnvV2, baseAdtU8, checkScalarValid, evalExprV2, opt] at hw
      rcases hw with ⟨_, h_opt, _⟩
      cases h_opt
  · -- (b) FnPtr PassMode witness
    let fnBodyFp : FnSem := {
      argRefTy := .primU64, argTupleTy := .primU64,
      argFnPtrTy := .fnPtr 0 (.adt 3) .primU64, retAdtId := 0,
      body := .callFnPtrArg .derefRefArg
    }
    let p1 : CrateEnvV2 := { baseEnvV2 with fns := fun _ => fnBodyFp }
    let p2 : CrateEnvV2 := {
      p1 with
      fnPtrAbis := fun _ => { argPassMode := .indirectStackPtr, canUnwind := false }
    }
    let opt : InputV2 -> IsaOutV2 := fun inp =>
      let v := inp.fnPtrCodeBehavior .directReg inp.refDerefVal
      .halted v [v % 256] 0
    refine ⟨p1, p2, opt, ?_, ?_, ?_⟩
    · refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun k hk => by cases hk⟩
    · intro inp
      dsimp only [evalMirV2, p1, fnBodyFp, baseEnvV2, baseAdtU8, checkScalarValid, evalExprV2]
      simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨[(inp.fnPtrCodeBehavior .directReg inp.refDerefVal) % 256], rfl,
        by simp [buildMaskedBytes, bytesRefine, byteRefines]⟩
    · intro h_bad
      let wInp : InputV2 := {
        refDerefVal := 5, tupleElem0Val := 0,
        fnPtrCodeBehavior := fun m x => match m with | .directReg => x + 1 | .indirectStackPtr => x + 99
      }
      have hw := h_bad wInp
      dsimp only [evalMirV2, p2, p1, fnBodyFp, baseEnvV2, baseAdtU8, checkScalarValid, evalExprV2, opt, wInp] at hw
      rcases hw with ⟨_, h_opt, _⟩
      cases h_opt
  · -- (c) Extern static link_name witness
    let fnBodyExt : FnSem := {
      argRefTy := .primU64, argTupleTy := .primU64,
      argFnPtrTy := .primU64, retAdtId := 0,
      body := .readExternStatic 0
    }
    let p1 : CrateEnvV2 := { baseEnvV2 with fns := fun _ => fnBodyExt }
    let p2 : CrateEnvV2 := {
      p1 with
      externStatics := fun _ => { linkSymbolId := 20, isMutable := false, valTy := .primU64 }
    }
    let opt : InputV2 -> IsaOutV2 := fun _ => .halted 42 [42] 0
    refine ⟨p1, p2, opt, ⟨fun _ _ => rfl, fun _ _ => rfl, fun k hk => by cases hk⟩, rfl, ?_, ?_⟩
    · intro inp
      dsimp only [evalMirV2, p1, fnBodyExt, baseEnvV2, baseAdtU8, checkScalarValid, evalExprV2]
      simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨[42], rfl, by simp [buildMaskedBytes, bytesRefine, byteRefines]⟩
    · intro h_bad
      have hw := h_bad { refDerefVal := 0, tupleElem0Val := 0, fnPtrCodeBehavior := fun _ x => x }
      dsimp only [evalMirV2, p2, p1, fnBodyExt, baseEnvV2, baseAdtU8, checkScalarValid, evalExprV2, opt] at hw
      rcases hw with ⟨_, h_opt, _⟩
      cases h_opt

/-- Complete `SpecCone` footprint collected by `SpecConeCollector` v2 (`ty.walk()`
    + `FnPtr` ABIs + foreign/local `Static` definitions). -/
structure SpecConeV2 where
  fns : List Nat
  adts : List Nat
  fnPtrSigs : List Nat
  externStatics : List Nat
  externSymIds : List Nat
  allocKeys : List Nat

/-- Recursive `ty.walk()` closure invariant on `Ty`. -/
def TyInCone (cone : SpecConeV2) (ty : Ty) : Prop :=
  Ty.rec
    (motive := fun _ => Prop)
    True
    (fun id => id ∈ cone.adts)
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ _ ih => ih)
    (fun _ _ _ ih0 ih1 ih2 => ih0 ∧ ih1 ∧ ih2)
    (fun sigId _ _ ihArg ihRet => sigId ∈ cone.fnPtrSigs ∧ ihArg ∧ ihRet)
    ty

def ExprInCone (env : CrateEnvV2) (cone : SpecConeV2) (e : Expr) : Prop :=
  Expr.rec
    (motive := fun _ => Prop)
    (fun k => k ∈ cone.allocKeys)
    True
    True
    (fun _ ih => ih)
    (fun statId =>
      statId ∈ cone.externStatics ∧
      (env.externStatics statId).linkSymbolId ∈ cone.externSymIds ∧
      TyInCone cone (env.externStatics statId).valTy)
    (fun callee _ ih => callee ∈ cone.fns ∧ ih)
    e

def WellClosedSpecCone (env : CrateEnvV2) (cone : SpecConeV2) (rootFn : Nat) : Prop :=
  rootFn ∈ cone.fns ∧
  ∀ f ∈ cone.fns,
    let fd := env.fns f
    TyInCone cone fd.argRefTy ∧
    TyInCone cone fd.argTupleTy ∧
    TyInCone cone fd.argFnPtrTy ∧
    fd.retAdtId ∈ cone.adts ∧
    ExprInCone env cone fd.body

/-- Complete `SpecCone` semantic equality (`rawAllocIds` remains unconstrained). -/
def WellClosedSpecConeEq (p1 p2 : CrateEnvV2) (cone : SpecConeV2) : Prop :=
  (∀ f ∈ cone.fns, p1.fns f = p2.fns f) ∧
  (∀ a ∈ cone.adts, p1.adts a = p2.adts a) ∧
  (∀ s ∈ cone.fnPtrSigs, p1.fnPtrAbis s = p2.fnPtrAbis s) ∧
  (∀ st ∈ cone.externStatics, p1.externStatics st = p2.externStatics st) ∧
  (∀ sym ∈ cone.externSymIds, p1.externSymbolVals sym = p2.externSymbolVals sym) ∧
  (∀ k ∈ cone.allocKeys, p1.constAllocs k = p2.constAllocs k)

theorem checkScalarValid_noninterference
    (p1 p2 : CrateEnvV2)
    (cone : SpecConeV2)
    (h_eq : WellClosedSpecConeEq p1 p2 cone) :
    ∀ (ty : Ty) (v : Nat),
      TyInCone cone ty ->
      checkScalarValid p1 ty v = checkScalarValid p2 ty v := by
  intro ty
  induction ty with
  | primU64 => intro _ _; rfl
  | adt id =>
      intro v hin
      simp only [checkScalarValid, h_eq.2.1 id hin]
  | sharedRef inner ih =>
      intro v hin
      exact ih v hin
  | rawPtr _ => intro _ _; rfl
  | slice _ => intro _ _; rfl
  | array elem _ ih =>
      intro v hin
      exact ih v hin
  | tuple3 t0 t1 t2 ih0 _ _ =>
      intro v hin
      exact ih0 v hin.1
  | fnPtr _ _ _ => intro _ _; rfl

theorem evalExprV2_noninterference
    (fuel : Nat)
    (p1 p2 : CrateEnvV2)
    (cone : SpecConeV2)
    (rootFn : Nat)
    (h_closed : WellClosedSpecCone p1 cone rootFn)
    (h_eq : WellClosedSpecConeEq p1 p2 cone) :
    ∀ (fnDef : FnSem) (e : Expr) (inp : InputV2),
      TyInCone cone fnDef.argFnPtrTy ->
      ExprInCone p1 cone e ->
      evalExprV2 fuel p1 fnDef inp e = evalExprV2 fuel p2 fnDef inp e := by
  induction fuel with
  | zero =>
      intro fnDef e inp _ h_use
      cases e with
      | constVal k =>
          simp only [evalExprV2, h_eq.2.2.2.2.2 k h_use]
      | derefRefArg => rfl
      | tuple0Arg => rfl
      | callFnPtrArg _ => rfl
      | readExternStatic statId =>
          rcases h_use with ⟨hst_in, hsym_in, _⟩
          have hst_eq := h_eq.2.2.2.1 statId hst_in
          have hsym_eq := h_eq.2.2.2.2.1 (p1.externStatics statId).linkSymbolId hsym_in
          dsimp only [evalExprV2]
          rw [← hst_eq, hsym_eq]
      | callDirect _ _ => rfl
  | succ fuel' ih =>
      intro fnDef e inp h_fp_cone h_use
      cases e with
      | constVal k =>
          simp only [evalExprV2, h_eq.2.2.2.2.2 k h_use]
      | derefRefArg => rfl
      | tuple0Arg => rfl
      | callFnPtrArg sub =>
          have hsub := ih fnDef sub inp h_fp_cone h_use
          dsimp only [evalExprV2]
          rw [hsub]
          cases evalExprV2 fuel' p2 fnDef inp sub with
          | none => rfl
          | some x =>
              cases hfp : fnDef.argFnPtrTy with
              | fnPtr sigId argTy retTy =>
                  rw [hfp] at h_fp_cone
                  have hsig_eq := h_eq.2.2.1 sigId h_fp_cone.1
                  simp only [hsig_eq]
              | primU64 | adt _ | sharedRef _ | rawPtr _ | slice _ | array _ _ | tuple3 _ _ _ =>
                  rfl
      | readExternStatic statId =>
          rcases h_use with ⟨hst_in, hsym_in, _⟩
          have hst_eq := h_eq.2.2.2.1 statId hst_in
          have hsym_eq := h_eq.2.2.2.2.1 (p1.externStatics statId).linkSymbolId hsym_in
          dsimp only [evalExprV2]
          rw [← hst_eq, hsym_eq]
      | callDirect callee sub =>
          rcases h_use with ⟨h_cal_in, h_sub_use⟩
          have hsub := ih fnDef sub inp h_fp_cone h_sub_use
          dsimp only [evalExprV2]
          rw [hsub]
          cases evalExprV2 fuel' p2 fnDef inp sub with
          | none => rfl
          | some v =>
              have h_fn_eq := h_eq.1 callee h_cal_in
              have h_cal_closed := h_closed.2 callee h_cal_in
              rw [← h_fn_eq]
              exact ih (p1.fns callee) (p1.fns callee).body
                { inp with refDerefVal := v } h_cal_closed.2.2.1 h_cal_closed.2.2.2.2

/-- Theorem 8: Operational `evalMirV2` non-interference under `WellClosedSpecCone`
    and `WellClosedSpecConeEq` (invariant to out-of-cone items and `rawAllocIds`). -/
theorem evalMir_wellClosedTypeGraph_noninterference
    (fuel : Nat)
    (p1 p2 : CrateEnvV2)
    (cone : SpecConeV2)
    (rootFn : Nat)
    (inp : InputV2)
    (h_closed : WellClosedSpecCone p1 cone rootFn)
    (h_eq : WellClosedSpecConeEq p1 p2 cone) :
    evalMirV2 fuel p1 rootFn inp = evalMirV2 fuel p2 rootFn inp := by
  dsimp only [evalMirV2]
  have h_root_eq := h_eq.1 rootFn h_closed.1
  have h_root_closed := h_closed.2 rootFn h_closed.1
  rw [← h_root_eq]
  have hv_ref :=
    checkScalarValid_noninterference p1 p2 cone h_eq
      (p1.fns rootFn).argRefTy inp.refDerefVal h_root_closed.1
  have hv_tup :=
    checkScalarValid_noninterference p1 p2 cone h_eq
      (p1.fns rootFn).argTupleTy inp.tupleElem0Val h_root_closed.2.1
  rw [hv_ref, hv_tup]
  cases (!(checkScalarValid p2 (p1.fns rootFn).argRefTy inp.refDerefVal &&
           checkScalarValid p2 (p1.fns rootFn).argTupleTy inp.tupleElem0Val)) with
  | true =>
      simp only [↓reduceIte]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hexpr :=
        evalExprV2_noninterference fuel p1 p2 cone rootFn h_closed h_eq
          (p1.fns rootFn) (p1.fns rootFn).body inp
          h_root_closed.2.2.1 h_root_closed.2.2.2.2
      rw [hexpr]
      have h_ret_eq := h_eq.2.1 (p1.fns rootFn).retAdtId h_root_closed.2.2.2.1
      rw [← h_ret_eq]

/-- Theorem 9 (`wellClosedSpecConeEq_preserves_totalMirAsmEquiv`):
    Under full `ty.walk()` type-graph closure, `FnPtr` ABI closure, and
    `GlobalAlloc::Static` closure, `WellClosedSpecConeEq p1 p2 cone` soundly
    transfers `TotalMirAsmEquiv` from `p1` to `p2`. -/
theorem wellClosedSpecConeEq_preserves_totalMirAsmEquiv
    (fuel : Nat)
    (p1 p2 : CrateEnvV2)
    (cone : SpecConeV2)
    (rootFn : Nat)
    (opt : InputV2 -> IsaOutV2)
    (h_closed : WellClosedSpecCone p1 cone rootFn)
    (h_eq : WellClosedSpecConeEq p1 p2 cone)
    (h_equiv : TotalMirAsmEquiv fuel p1 rootFn opt) :
    TotalMirAsmEquiv fuel p2 rootFn opt := by
  intro inp
  have h_mir :=
    evalMir_wellClosedTypeGraph_noninterference fuel p1 p2 cone rootFn inp h_closed h_eq
  have h1 := h_equiv inp
  rw [h_mir] at h1
  exact h1

#print axioms non_debug_gc_sections_bfd_loss_and_lld_phantom_span_unsound
#print axioms postlink_debug_tombstone_filter_sound_and_complete
#print axioms unannotated_icf_leader_absorbs_debug_record_unless_sym_gated
#print axioms gc_relax_icf_postlink_composition_sound
#print axioms local_only_query_misses_extern_stdarch_and_dual_query_complete
#print axioms ref_pointee_niche_omission_unsound
#print axioms compound_tuple3_fnptr_and_extern_static_omission_unsound
#print axioms evalMir_wellClosedTypeGraph_noninterference
#print axioms wellClosedSpecConeEq_preserves_totalMirAsmEquiv

end PostLinkGcTombstoneAndSpecConeClosure
