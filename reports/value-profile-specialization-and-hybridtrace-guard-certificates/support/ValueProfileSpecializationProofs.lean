-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Value-Profile Specialization (`IPVK_MemOPSize`, `IPVK_IndirectCallTarget`, `IPVK_VTableTarget`) and Speculative Guard Certificates in `HybridTrace`

Standalone Lean 4 (`v4.34.1`) mechanization of the three value-profiling
specialization schemas in `HybridTrace`:
1. **Schema VP-1 (`VP-MemOpSizeSpecialize`)**:
   - Proves that tautological diamond splitting of `memcpy(dst, src, len)` on a
     profile-predicted byte length `S` (`if len = S then memcpy(dst, src, S)
     else multi_size_fallback(dst, src, len)`) is 100% observationally equivalent
     to `memcpy(dst, src, len)` for every runtime `len`, preserving byte-level
     values, poison bits, pointer provenance, and Tree Borrows permissions with
     zero trust in the profile (`vp1_memcpy_diamond_sound`, `vp1_multi_size_ladder_sound`).
   - Proves that for non-power-of-two sizes `S` with `8 ≤ S ≤ 16` (e.g., `S = 12`
     or `S = 15`), lowering `memcpy(dst, src, S)` into two overlapping 8-byte
     unaligned loads (`head = src[0..8)`, `tail = src[S-8..S)`) into temporaries
     *before* storing both to `dst` produces the exact same post-state memory as
     a sequential `S`-byte non-overlapping copy (`vp1_overlapping_head_tail_sound`),
     and proves a negative canary (`canary_unbuffered_overlapping_copy_clobbers`)
     when the head store executes before the tail load on partially overlapping
     buffers.
2. **Schema VP-2 (`VP-IndirectCallPromote`)**:
   - Proves that speculative indirect-call promotion (`if fn_ptr = symAddr(hotSym)
     then callDirect(hotSym, arg) else callIndirect(fn_ptr, arg)`) is sound
     under disjoint code-block allocation and `FnAbi` compatibility, including
     when `MergeFunctions` (`T12`) merges alpha-equivalent `unnamed_addr`
     functions (`vp2_indirect_call_promote_sound`), and proves a negative canary
     (`canary_vp2_abi_mismatch_unsound`) when the promoted target's `FnAbi`
     disagrees with the call site.
3. **Schema VP-3 (`VP-VTablePromote`)**:
   - Proves that comparing `vtable_ptr = vtableAddr(hotVTable)` on a `&dyn Trait`
     fat pointer `(data_ptr, vtable_ptr)` under the `.rodata` read-only global
     invariant (`RoDataVTableInv`) soundly specializes both single and multiple
     sequential trait method calls (`vp3_vtable_promote_sound`,
     `vp3_multi_method_promote_sound`) without loading the function pointer from
     the vtable on the fast path, and proves a negative canary
     (`canary_vp3_writable_vtable_unsound`) when the vtable resides in writable
     memory.
4. **Certificate Checker Soundness and Completeness**:
   - Mechanizes `checkVPSpecCert` and proves both `checkVPSpecCert_sound` and
     `checkVPSpecCert_complete`.
-/

namespace ValueProfileSpecializationProofs

/-!
## 1. Byte-Level Memory Model with Poison, Provenance, and Tree Borrows Tags
-/

abbrev Addr   := Nat
abbrev ProvId := Nat
abbrev TbPerm := Nat

/-- A single memory byte carrying a concrete value (or poison), optional pointer
provenance fragment, and Tree Borrows permission state. -/
structure MemCell where
  byteVal : Option UInt8
  prov    : Option ProvId
  tbPerm  : TbPerm
  deriving DecidableEq, Repr

/-- Abstract byte-addressed memory state. -/
abbrev Mem := Nat → MemCell

/-- Read a single byte at `a`. -/
def readByte (m : Mem) (a : Nat) : MemCell := m a

/-- Write a single cell `c` at address `a`. -/
def writeByte (m : Mem) (a : Nat) (c : MemCell) : Mem :=
  fun addr => if addr == a then c else m addr

/-- Simultaneous parallel byte-range copy of `len` bytes from `src` to `dst`
(`@llvm.memcpy.p0.p0.i64(dst, src, len, isvolatile=false)`). -/
def memcpySem (m : Mem) (dst src len : Nat) : Mem :=
  fun addr =>
    if dst ≤ addr ∧ addr < dst + len then
      m (src + (addr - dst))
    else
      m addr

/-!
## 2. Schema VP-1: `VP-MemOpSizeSpecialize` Soundness & Overlapping Slice Lowering
-/

/-- Specializing `memcpySem` for a profile-predicted constant size `S` via a
guarded diamond `if len == S then memcpySem m dst src S else memcpySem m dst src len`. -/
def vp1DiamondMemcpy (m : Mem) (dst src len S : Nat) : Mem :=
  if len == S then
    memcpySem m dst src S
  else
    memcpySem m dst src len

/-- **Theorem VP-1a (`vp1_memcpy_diamond_sound`)**: Guarded size specialization
is a tautological semantic identity for every `m`, `dst`, `src`, `len`, and
predicted size `S` (even if the profile is 100% wrong or adversarial). -/
theorem vp1_memcpy_diamond_sound (m : Mem) (dst src len S : Nat) :
    vp1DiamondMemcpy m dst src len S = memcpySem m dst src len := by
  unfold vp1DiamondMemcpy
  by_cases h : (len == S) = true
  · simp [h]
    have heq : len = S := LawfulBEq.eq_of_beq h
    subst heq
    rfl
  · simp [h]

/-- Multi-size `SwitchInt` specialization ladder for up to `k` hot sizes `sizes`. -/
def vp1LadderMemcpy (m : Mem) (dst src len : Nat) (sizes : List Nat) : Mem :=
  match sizes with
  | [] => memcpySem m dst src len
  | s :: rest =>
    if len == s then
      memcpySem m dst src s
    else
      vp1LadderMemcpy m dst src len rest

/-- **Theorem VP-1b (`vp1_multi_size_ladder_sound`)**: A `k`-target `SwitchInt`
size specialization ladder is observationally identical to `memcpySem`. -/
theorem vp1_multi_size_ladder_sound (m : Mem) (dst src len : Nat) (sizes : List Nat) :
    vp1LadderMemcpy m dst src len sizes = memcpySem m dst src len := by
  induction sizes with
  | nil => rfl
  | cons s rest ih =>
    unfold vp1LadderMemcpy
    by_cases h : (len == s) = true
    · simp [h]
      have heq : len = s := LawfulBEq.eq_of_beq h
      subst heq
      rfl
    · simp [h, ih]

/-- Overlapping two-load (`[0..8)` and `[S-8..S)`) into temporaries followed by
two-store lowering used by `x86_64` / `aarch64` backends for `8 ≤ S ≤ 16`. -/
def overlappingHeadTailCopy (m : Mem) (dst src S : Nat) : Mem :=
  fun addr =>
    if dst + (S - 8) ≤ addr ∧ addr < dst + S then
      m (src + (S - 8) + (addr - (dst + (S - 8))))
    else if dst ≤ addr ∧ addr < dst + 8 then
      m (src + (addr - dst))
    else
      m addr

/-- **Theorem VP-1c (`vp1_overlapping_head_tail_sound`)**: Whenever `8 ≤ S` and
`S ≤ 16`, reading the two overlapping 8-byte slices `[0..8)` and `[S-8..S)` into
register temporaries *before* storing both to `dst` produces the exact same
memory state at every address as `memcpySem m dst src S` (even on the overlapped
middle bytes `[dst + (S - 8) .. dst + 8)`!). -/
theorem vp1_overlapping_head_tail_sound
    (m : Mem) (dst src S : Nat)
    (h_lo : 8 ≤ S) (h_hi : S ≤ 16) :
    overlappingHeadTailCopy m dst src S = memcpySem m dst src S := by
  funext (addr : Nat)
  unfold overlappingHeadTailCopy memcpySem
  split
  · next h_tail =>
    split
    · congr 1
      omega
    · next h_not_in =>
      exfalso
      apply h_not_in
      exact ⟨by omega, h_tail.2⟩
  · next h_not_tail =>
    split
    · next h_head =>
      split
      · rfl
      · next h_not_in =>
        exfalso
        apply h_not_in
        exact ⟨h_head.1, by omega⟩
    · next h_not_head =>
      split
      · next h_in =>
        exfalso
        apply h_not_tail
        exact ⟨by omega, h_in.2⟩
      · rfl

/-- **Canary VP-1 (`canary_unbuffered_overlapping_copy_clobbers`)**: If the
backend writes the head 8-byte slice `[dst..dst+8)` *before* reading the tail
8-byte slice `[src+(S-8)..src+S)` on an aliased buffer where `dst = src + 2` and
`S = 12`, byte `src + 4` is overwritten before the tail load reads it. -/
def unbufferedHeadThenTailCopy (m : Mem) (dst src S : Nat) : Mem :=
  let m1 : Mem := fun addr =>
    if dst ≤ addr ∧ addr < dst + 8 then m (src + (addr - dst)) else m addr
  fun addr =>
    if dst + (S - 8) ≤ addr ∧ addr < dst + S then
      m1 (src + (S - 8) + (addr - (dst + (S - 8))))
    else
      m1 addr

theorem canary_unbuffered_overlapping_copy_clobbers :
    let m0 : Mem := fun a => { byteVal := some (UInt8.ofNat a), prov := none, tbPerm := 0 }
    (unbufferedHeadThenTailCopy m0 2 0 12 6).byteVal ≠ (memcpySem m0 2 0 12 6).byteVal := by
  decide

/-!
## 3. Schema VP-2: `VP-IndirectCallPromote` (`IPVK_IndirectCallTarget`)
-/

abbrev SymId   := Nat
abbrev CodePtr := Nat
abbrev FnAbiId := Nat
abbrev Val     := Nat

structure CodeEntry where
  sym  : SymId
  abi  : FnAbiId
  body : Val → Option Val

/-- Code memory mapping function pointers to `CodeEntry` blocks, together with a
symbol address table `symAddr : SymId → CodePtr`. -/
structure CodeWorld where
  symAddr   : SymId → CodePtr
  codeTable : CodePtr → Option CodeEntry

/-- Coherent symbol-to-code mapping (allowing `MergeFunctions` (`T12`) to alias
two symbols to the same `CodePtr` only when their bodies and ABIs are identical). -/
def CodeWorldCoherent (w : CodeWorld) (hotSym : SymId) (expectedAbi : FnAbiId) : Prop :=
  ∃ e, w.codeTable (w.symAddr hotSym) = some e ∧ e.abi = expectedAbi

/-- Indirect call semantics checking `FnAbiId` compatibility at runtime. -/
def evalIndirectCall (w : CodeWorld) (callAbi : FnAbiId) (fnPtr : CodePtr) (arg : Val) : Option Val :=
  match w.codeTable fnPtr with
  | some e => if e.abi == callAbi then e.body arg else none
  | none   => none

/-- Direct call semantics to `hotSym` when `fnPtr == w.symAddr hotSym`. -/
def evalPromotedDirectCall (w : CodeWorld) (callAbi : FnAbiId) (hotSym : SymId) (arg : Val) : Option Val :=
  evalIndirectCall w callAbi (w.symAddr hotSym) arg

/-- Guarded indirect-call promotion (`VP-IndirectCallPromote`). -/
def vp2IndirectCallPromote
    (w : CodeWorld) (callAbi : FnAbiId) (fnPtr : CodePtr) (hotSym : SymId) (arg : Val) : Option Val :=
  if fnPtr == w.symAddr hotSym then
    evalPromotedDirectCall w callAbi hotSym arg
  else
    evalIndirectCall w callAbi fnPtr arg

/-- **Theorem VP-2 (`vp2_indirect_call_promote_sound`)**: Guarded indirect-call
promotion is observationally identical to `evalIndirectCall` for every runtime
`fnPtr` and `arg`, even if `MergeFunctions` (`T12`) merged `hotSym` with an
alpha-equivalent function body. -/
theorem vp2_indirect_call_promote_sound
    (w : CodeWorld) (callAbi : FnAbiId) (fnPtr : CodePtr) (hotSym : SymId) (arg : Val) :
    vp2IndirectCallPromote w callAbi fnPtr hotSym arg = evalIndirectCall w callAbi fnPtr arg := by
  unfold vp2IndirectCallPromote evalPromotedDirectCall
  by_cases h : (fnPtr == w.symAddr hotSym) = true
  · simp [h]
    have heq : fnPtr = w.symAddr hotSym := LawfulBEq.eq_of_beq h
    subst heq
    rfl
  · simp [h]

/-- **Canary VP-2 (`canary_vp2_abi_mismatch_unsound`)**: If a compiler bypasses
the `FnAbi` check when promoting and inlining a direct body whose ABI differs
from `callAbi`, calling the unchecked body diverges from `evalIndirectCall`
(which traps on ABI mismatch). -/
theorem canary_vp2_abi_mismatch_unsound :
    let w : CodeWorld := {
      symAddr := fun _ => 100,
      codeTable := fun ptr =>
        if ptr == 100 then some { sym := 1, abi := 2, body := fun x => some (x + 1) } else none
    }
    evalIndirectCall w 1 100 42 = none ∧ (some (42 + 1) ≠ evalIndirectCall w 1 100 42) := by
  decide

/-!
## 4. Schema VP-3: `VP-VTablePromote` (`IPVK_VTableTarget`) Under `.rodata` Invariant
-/

abbrev VTablePtr := Nat
abbrev SlotIdx   := Nat

/-- Read-only `.rodata` invariant for a compiled `GlobalAlloc::VTable`: whenever
`vtablePtr = hotVTableAddr`, reading slot `slot` from `vtableMem` yields
`hotMethodPtr`. -/
def RoDataVTableSlotInv
    (vtableMem : VTablePtr → SlotIdx → CodePtr)
    (hotVTableAddr : VTablePtr) (slot : SlotIdx) (hotMethodPtr : CodePtr) : Prop :=
  vtableMem hotVTableAddr slot = hotMethodPtr

/-- Dynamic trait dispatch: loads `fnPtr = vtableMem vtablePtr slot` and invokes
`evalIndirectCall`. -/
def evalDynTraitCall
    (w : CodeWorld) (vtableMem : VTablePtr → SlotIdx → CodePtr)
    (callAbi : FnAbiId) (vtablePtr : VTablePtr) (slot : SlotIdx) (arg : Val) : Option Val :=
  let fnPtr := vtableMem vtablePtr slot
  evalIndirectCall w callAbi fnPtr arg

/-- `VP-VTablePromote` guarded specialization: compares `vtablePtr == hotVTableAddr`
directly (breaking the `vtablePtr -> fnPtr` load-to-branch latency chain) and
calls `hotMethodPtr` directly on the fast path. -/
def vp3VTablePromote
    (w : CodeWorld) (vtableMem : VTablePtr → SlotIdx → CodePtr)
    (callAbi : FnAbiId) (vtablePtr hotVTableAddr : VTablePtr)
    (slot : SlotIdx) (hotMethodPtr : CodePtr) (arg : Val) : Option Val :=
  if vtablePtr == hotVTableAddr then
    evalIndirectCall w callAbi hotMethodPtr arg
  else
    evalDynTraitCall w vtableMem callAbi vtablePtr slot arg

/-- **Theorem VP-3a (`vp3_vtable_promote_sound`)**: Under `RoDataVTableSlotInv`,
promoting a `&dyn Trait` call by comparing `vtablePtr == hotVTableAddr` is
observationally identical to `evalDynTraitCall`. -/
theorem vp3_vtable_promote_sound
    (w : CodeWorld) (vtableMem : VTablePtr → SlotIdx → CodePtr)
    (callAbi : FnAbiId) (vtablePtr hotVTableAddr : VTablePtr)
    (slot : SlotIdx) (hotMethodPtr : CodePtr) (arg : Val)
    (h_ro : RoDataVTableSlotInv vtableMem hotVTableAddr slot hotMethodPtr) :
    vp3VTablePromote w vtableMem callAbi vtablePtr hotVTableAddr slot hotMethodPtr arg =
    evalDynTraitCall w vtableMem callAbi vtablePtr slot arg := by
  unfold vp3VTablePromote evalDynTraitCall
  by_cases h : (vtablePtr == hotVTableAddr) = true
  · simp [h]
    have heq : vtablePtr = hotVTableAddr := LawfulBEq.eq_of_beq h
    subst heq
    rw [h_ro]
  · simp [h]

/-- **Theorem VP-3b (`vp3_multi_method_promote_sound`)**: A single
`vtablePtr == hotVTableAddr` guard soundly specializes *two* sequential trait
method calls (`slot₁` and `slot₂`) on the same `&dyn Trait` fat pointer. -/
theorem vp3_multi_method_promote_sound
    (w : CodeWorld) (vtableMem : VTablePtr → SlotIdx → CodePtr)
    (abi₁ abi₂ : FnAbiId) (vtablePtr hotVTableAddr : VTablePtr)
    (slot₁ slot₂ : SlotIdx) (mPtr₁ mPtr₂ : CodePtr) (arg : Val)
    (h_ro₁ : RoDataVTableSlotInv vtableMem hotVTableAddr slot₁ mPtr₁)
    (h_ro₂ : RoDataVTableSlotInv vtableMem hotVTableAddr slot₂ mPtr₂) :
    (if vtablePtr == hotVTableAddr then
       match evalIndirectCall w abi₁ mPtr₁ arg with
       | some v1 => evalIndirectCall w abi₂ mPtr₂ v1
       | none    => none
     else
       match evalDynTraitCall w vtableMem abi₁ vtablePtr slot₁ arg with
       | some v1 => evalDynTraitCall w vtableMem abi₂ vtablePtr slot₂ v1
       | none    => none) =
    (match evalDynTraitCall w vtableMem abi₁ vtablePtr slot₁ arg with
     | some v1 => evalDynTraitCall w vtableMem abi₂ vtablePtr slot₂ v1
     | none    => none) := by
  by_cases h : (vtablePtr == hotVTableAddr) = true
  · simp [h]
    have heq : vtablePtr = hotVTableAddr := LawfulBEq.eq_of_beq h
    subst heq
    unfold evalDynTraitCall
    rw [h_ro₁, h_ro₂]
  · simp [h]

/-- **Canary VP-3 (`canary_vp3_writable_vtable_unsound`)**: If `vtableMem` is
mutated in writable memory so `vtableMem hotVTableAddr slot ≠ hotMethodPtr`,
`vp3VTablePromote` invokes the stale `hotMethodPtr` instead of the current slot
target. -/
theorem canary_vp3_writable_vtable_unsound :
    let w : CodeWorld := {
      symAddr := id,
      codeTable := fun ptr =>
        if ptr == 10 then some { sym := 10, abi := 1, body := fun x => some (x + 10) }
        else if ptr == 20 then some { sym := 20, abi := 1, body := fun x => some (x + 20) }
        else none
    }
    let mutatedVTableMem : VTablePtr → SlotIdx → CodePtr := fun _ _ => 20
    vp3VTablePromote w mutatedVTableMem 1 500 500 0 10 1 ≠
    evalDynTraitCall w mutatedVTableMem 1 500 0 1 := by
  decide

/-!
## 5. `HybridTrace` Value-Profile Certificate Checker Soundness and Completeness
-/

inductive VPCertSchema where
  | memOpSize (predictedSize : Nat) (useOverlapping8x2 : Bool)
  | indirectCallPromote (callAbi targetAbi : FnAbiId) (guardMatchesTarget : Bool)
  | vtablePromote (callAbi targetAbi : FnAbiId) (vtableInRodata slotMatchesMethod : Bool)
  deriving DecidableEq, Repr

/-- Decidable `HybridTrace` certificate validator for Schemas VP-1, VP-2, VP-3. -/
def checkVPSpecCert (cert : VPCertSchema) : Bool :=
  match cert with
  | .memOpSize sz useOverlap =>
    if useOverlap then decide (8 ≤ sz ∧ sz ≤ 16) else decide (0 < sz)
  | .indirectCallPromote cAbi tAbi guardOk =>
    (cAbi == tAbi) && guardOk
  | .vtablePromote cAbi tAbi roOk slotOk =>
    (cAbi == tAbi) && roOk && slotOk

/-- Semantic validity specification for a `VPCertSchema` certificate. -/
def ValidVPSpecCert (cert : VPCertSchema) : Prop :=
  match cert with
  | .memOpSize sz useOverlap =>
    if useOverlap = true then 8 ≤ sz ∧ sz ≤ 16 else 0 < sz
  | .indirectCallPromote cAbi tAbi guardOk =>
    cAbi = tAbi ∧ guardOk = true
  | .vtablePromote cAbi tAbi roOk slotOk =>
    cAbi = tAbi ∧ roOk = true ∧ slotOk = true

theorem checkVPSpecCert_sound (cert : VPCertSchema)
    (h : checkVPSpecCert cert = true) : ValidVPSpecCert cert := by
  cases cert with
  | memOpSize sz useOverlap =>
    unfold checkVPSpecCert ValidVPSpecCert at *
    cases useOverlap <;> simp at h ⊢ <;> omega
  | indirectCallPromote cAbi tAbi guardOk =>
    unfold checkVPSpecCert ValidVPSpecCert at *
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h
  | vtablePromote cAbi tAbi roOk slotOk =>
    unfold checkVPSpecCert ValidVPSpecCert at *
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

theorem checkVPSpecCert_complete (cert : VPCertSchema)
    (h : ValidVPSpecCert cert) : checkVPSpecCert cert = true := by
  cases cert with
  | memOpSize sz useOverlap =>
    unfold checkVPSpecCert ValidVPSpecCert at *
    cases useOverlap <;> simp at h ⊢ <;> omega
  | indirectCallPromote cAbi tAbi guardOk =>
    unfold checkVPSpecCert ValidVPSpecCert at *
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact h
  | vtablePromote cAbi tAbi roOk slotOk =>
    unfold checkVPSpecCert ValidVPSpecCert at *
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

end ValueProfileSpecializationProofs

#print axioms ValueProfileSpecializationProofs.vp1_memcpy_diamond_sound
#print axioms ValueProfileSpecializationProofs.vp1_multi_size_ladder_sound
#print axioms ValueProfileSpecializationProofs.vp1_overlapping_head_tail_sound
#print axioms ValueProfileSpecializationProofs.canary_unbuffered_overlapping_copy_clobbers
#print axioms ValueProfileSpecializationProofs.vp2_indirect_call_promote_sound
#print axioms ValueProfileSpecializationProofs.canary_vp2_abi_mismatch_unsound
#print axioms ValueProfileSpecializationProofs.vp3_vtable_promote_sound
#print axioms ValueProfileSpecializationProofs.vp3_multi_method_promote_sound
#print axioms ValueProfileSpecializationProofs.canary_vp3_writable_vtable_unsound
#print axioms ValueProfileSpecializationProofs.checkVPSpecCert_sound
#print axioms ValueProfileSpecializationProofs.checkVPSpecCert_complete
