/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Standalone Lean 4 Probe: `InitSubsumes` Simulation & `ByteProvFrag` Reassembly

Self-contained, kernel-checked formalization of:
1. **`InitSubsumes` forward simulation for `Operand::Move` deinitialization**:
   - Byte-level `AbsByte` (`.uninit` | `.init val frag`) and `ByteProvFrag`
     (`prov`, `origAddr`, `byteIdx`);
   - `ByteSubsumes` and `InitSubsumes` relating a strict machine `M_strict`
     (`deinitOnMove = true`, which resets moved-from source bytes to `.uninit`
     via `deinitRange` without performing a Tree Borrows `.Write` transition)
     to a permissive machine `M_perm` (`deinitOnMove = false`, matching
     `rustc_const_eval`'s `eval_operand` and `proofs-rs/lean-miri`'s
     `Operand.lean`);
   - Proof that if `deinitOnMove = true` instead performed a Tree Borrows
     `.Write` access on move (`tb_write_on_move_breaks_borrow_tree_equiv`), it
     would prematurely activate `ReservedFrz false → Unique` and break lockstep
     `BorrowTree` equivalence under a subsequent foreign read + child write;
   - Forward simulation of `InitSubsumes` / `StateSubsumes` across:
     - `readScalarAt` in both `.Initialized` mode (exact result equality) and
       `.Union` mode (`MaybeUninit<u8>`, preserving `InitSubsumes` on the raw
       byte slice);
     - `writeScalarAt` (preserving `InitSubsumes`);
     - `copyBytes` (memory-to-memory `copyOp` / `copyNonOverlapping`, preserving
       `InitSubsumes`);
     - `retagPlace` (confirming that `FreezeVisitor` / `retag` inspects only the
       pointer scalar and static type layout, never pointee byte
       initialization);
     - `deallocateAlloc` (confirming that `deallocateBorrowRange` inspects only
       `tbTree` and `protectedTags`, never byte initialization).
2. **`ByteProvFrag` / `PointerFrag` reassembly vs. chimeric splicing**:
   - `byte_by_byte_maybe_uninit_copy_preserves_prov`: copying an 8-byte pointer
     one byte at a time via 1-byte `copyBytes` (`MaybeUninit<u8>`) to a shifted
     destination offset preserves all 8 `ByteProvFrag` entries and reconstructs
     the original provenance on `readScalarInitializedAt ... 8 true`;
   - `u8_copy_strips_prov`: copying an 8-byte pointer one byte at a time via
     1-byte `readScalarInitializedAt ... 1 false` (`u8`) strips provenance;
   - `chimeric_splice_strips_prov` and `chimeric_splice_general_strips_prov`:
     splicing bytes `0..4` of `p1` and bytes `4..8` of `p2`—even when `p1` and
     `p2` share the **exact same provenance `(allocId, tag)`** at different
     offsets `origAddr1 ≠ origAddr2`—fails the `origAddr` consistency check in
     `reconstructProv` and strips provenance.
-/

namespace LeanMiriInitSubsumesAndFragProbe

/-! ## 1. Provenance, `ByteProvFrag`, and `AbsByte` -/

structure Provenance where
  allocId : Nat
  tag : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Per-byte provenance fragment corresponding to `Miri.Memory.PointerFrag`
(`Miri/Memory/ProvenanceMap.lean:15-20`), which snapshots the pointer's
provenance `prov`, full 8-byte original address `origAddr` (`bytes : [u8; 8]`),
and byte index `byteIdx ∈ 0..7` (`idx : u8`). -/
structure ByteProvFrag where
  prov : Provenance
  origAddr : Nat
  byteIdx : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Abstract byte representation combining `Allocation.rawBytes`,
`Allocation.initMask`, and `Allocation.provenance`. -/
inductive AbsByte where
  | uninit
  | init (val : UInt8) (frag : Option ByteProvFrag)
  deriving DecidableEq, Repr, Inhabited

/-- Scalar values produced by `readScalar` / consumed by `writeScalar` under
`offsetIsAddr = true`. -/
inductive ScalarVal where
  | int (bits : Nat) (size : Nat)
  | ptr (addr : Nat) (size : Nat) (prov : Provenance)
  deriving DecidableEq, Repr, Inhabited

/-- Load mode distinguishing `BackendRepr::Scalar(Scalar::Initialized)` from
`BackendRepr::Scalar(Scalar::Union)` (such as `MaybeUninit<u8>`). -/
inductive ScalarLoadMode where
  | Initialized (readProv : Bool) (size : Nat)
  | Union (size : Nat)
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Slice Extraction, Little-Endian Decoding, and Fragment Reassembly -/

def extractSlice (mem : List AbsByte) (offset size : Nat) : Option (List AbsByte) :=
  if offset + size ≤ mem.length then
    some ((mem.drop offset).take size)
  else
    none

/-- Extract initialized byte values from a slice; returns `none` if any byte in
the slice is `.uninit` (modeling `Allocation.checkInit` / `isRangeInitialized`). -/
def decodeInitBytes : List AbsByte → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init b _ :: rest => do
      let tail ← decodeInitBytes rest
      some (b :: tail)

def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * bytesToNatLE rest

def natToBytesLE (val : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat (val % 256) :: natToBytesLE (val / 256) n

/-- Check whether `slice` (of length 8) has matching `ByteProvFrag`s at indices
`idx .. idx + slice.length - 1` all agreeing on `(expectedProv, expectedAddr)`.
Corresponds to `ProvenanceMap.inspectFragments` (`ProvenanceMap.lean:117-135`). -/
def checkFragsFrom (expectedProv : Provenance) (expectedAddr : Nat) :
    Nat → List AbsByte → Bool
  | _, [] => true
  | idx, .init _ (some f) :: rest =>
      (f.prov == expectedProv) &&
      (f.origAddr == expectedAddr) &&
      (f.byteIdx == idx) &&
      checkFragsFrom expectedProv expectedAddr (idx + 1) rest
  | _, _ => false

/-- Reassemble pointer provenance from an 8-byte slice if and only if all 8
bytes carry fragments with matching `(prov, origAddr)` and sequential indices
`0..7`. -/
def reconstructProv (slice : List AbsByte) : Option Provenance :=
  if slice.length == 8 then
    match slice with
    | .init _ (some f0) :: _ =>
        if checkFragsFrom f0.prov f0.origAddr 0 slice then
          some f0.prov
        else
          none
    | _ => none
  else
    none

/-! ## 3. Memory Operations: `readScalarAt`, `writeScalarAt`, `copyBytes`, `deinitRange` -/

def readScalarInitializedAt (mem : List AbsByte) (offset size : Nat) (readProv : Bool) :
    Option ScalarVal := do
  let slice ← extractSlice mem offset size
  let rawBytes ← decodeInitBytes slice
  let bits := bytesToNatLE rawBytes
  if readProv && size == 8 then
    match reconstructProv slice with
    | some prov => some (.ptr bits 8 prov)
    | none => some (.int bits 8)
  else
    some (.int bits size)

def readScalarUnionAt (mem : List AbsByte) (offset size : Nat) : Option (List AbsByte) :=
  extractSlice mem offset size

def readScalarAt (mem : List AbsByte) (offset : Nat) (mode : ScalarLoadMode) :
    Option (ScalarVal ⊕ List AbsByte) :=
  match mode with
  | .Initialized readProv size => Sum.inl <$> readScalarInitializedAt mem offset size readProv
  | .Union size => Sum.inr <$> readScalarUnionAt mem offset size

def encodeScalarBytes (v : ScalarVal) : List AbsByte :=
  match v with
  | .int bits size =>
      (natToBytesLE bits size).map (fun b => .init b none)
  | .ptr addr size prov =>
      let raw := natToBytesLE addr size
      (List.range size).zipWith
        (fun i b => .init b (some { prov := prov, origAddr := addr, byteIdx := i }))
        raw

def spliceAt (mem : List AbsByte) (offset : Nat) (newBytes : List AbsByte) : List AbsByte :=
  mem.take offset ++ newBytes ++ mem.drop (offset + newBytes.length)

def writeScalarAt (mem : List AbsByte) (offset : Nat) (v : ScalarVal) : Option (List AbsByte) :=
  let encoded := encodeScalarBytes v
  if offset + encoded.length ≤ mem.length then
    some (spliceAt mem offset encoded)
  else
    none

def copyBytes (src dest : List AbsByte) (srcOff destOff size : Nat) : Option (List AbsByte) := do
  let slice ← extractSlice src srcOff size
  if destOff + size ≤ dest.length then
    some (spliceAt dest destOff slice)
  else
    none

def deinitRange (mem : List AbsByte) (offset size : Nat) : List AbsByte :=
  spliceAt mem offset (List.replicate size .uninit)

/-! ## 4. Provenance Fragment Proofs: `MaybeUninit<u8>` Copy vs. `u8` Copy vs. Chimeric Splice -/

def sampleProv : Provenance := { allocId := 1, tag := 42 }
def samplePtr1 : ScalarVal := .ptr 0x1000 8 sampleProv
def samplePtr2 : ScalarVal := .ptr 0x1008 8 sampleProv

def blankMem (n : Nat) : List AbsByte := List.replicate n .uninit

/-- Copying an 8-byte pointer byte-by-byte (1 byte at a time via `copyBytes`,
which is how `rustc_const_eval` / `lean-miri` lowers `MaybeUninit<u8>` copies
because `BackendRepr::Scalar(Scalar::Union)` takes the `mem_copy` path) to a
shifted offset (`destOff = 3`) preserves all 8 `ByteProvFrag` entries and
reconstructs the exact pointer provenance on load. -/
def copyByteByByte (src dest : List AbsByte) (srcOff destOff : Nat) : Nat → Option (List AbsByte)
  | 0 => some dest
  | k + 1 => do
      let dest' ← copyByteByByte src dest srcOff destOff k
      copyBytes src dest' (srcOff + k) (destOff + k) 1

theorem byte_by_byte_maybe_uninit_copy_preserves_prov :
    (do
      let src ← writeScalarAt (blankMem 16) 0 samplePtr1
      let dst ← copyByteByByte src (blankMem 16) 0 3 8
      readScalarInitializedAt dst 3 8 true) = some samplePtr1 := by
  decide

/-- Copying an 8-byte pointer byte-by-byte via 1-byte `u8` loads
(`readScalarInitializedAt ... 1 false`, because `u8` has
`BackendRepr::Scalar(Scalar::Initialized)` with `readProvenance = false`)
strips provenance and produces an integer scalar `.int 0x1000 8` when reloaded
as a pointer under `offsetIsAddr = true`. -/
def copyViaU8 (src dest : List AbsByte) (srcOff destOff : Nat) : Nat → Option (List AbsByte)
  | 0 => some dest
  | k + 1 => do
      let dest' ← copyViaU8 src dest srcOff destOff k
      let byteVal ← readScalarInitializedAt src (srcOff + k) 1 false
      writeScalarAt dest' (destOff + k) byteVal

theorem u8_copy_strips_prov :
    (do
      let src ← writeScalarAt (blankMem 16) 0 samplePtr1
      let dst ← copyViaU8 src (blankMem 16) 0 0 8
      readScalarInitializedAt dst 0 8 true) = some (.int 0x1000 8) := by
  decide

/-- Splicing the low 4 bytes (`0..4`) of `samplePtr1` and the high 4 bytes
(`4..8`) of `samplePtr2`—even though `samplePtr1` and `samplePtr2` have the
**exact same provenance `sampleProv` (`allocId = 1, tag = 42`)** and identical
high 4 address bytes (`0x00, 0x00, 0x00, 0x00`)—fails `reconstructProv` because
`f.origAddr` differs (`0x1000 ≠ 0x1008`), stripping provenance. -/
theorem chimeric_splice_strips_prov :
    (do
      let m1 ← writeScalarAt (blankMem 8) 0 samplePtr1
      let m2 ← writeScalarAt (blankMem 8) 0 samplePtr2
      let splice1 ← copyBytes m1 (blankMem 8) 0 0 4
      let splice2 ← copyBytes m2 splice1 4 4 4
      readScalarInitializedAt splice2 0 8 true) = some (.int 0x1000 8) := by
  decide

/-- General theorem: for any two pointers `p1 = .ptr addr1 8 prov` and
`p2 = .ptr addr2 8 prov` with `addr1 ≠ addr2`, any 8-byte slice whose byte 0
comes from byte 0 of `p1` and whose byte 4 comes from byte 4 of `p2` is
rejected by `reconstructProv` (`= none`). -/
theorem chimeric_splice_general_strips_prov
    (prov : Provenance) (addr1 addr2 : Nat) (h_ne : addr1 ≠ addr2)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    let f_lo (i : Nat) : Option ByteProvFrag :=
      some { prov := prov, origAddr := addr1, byteIdx := i }
    let f_hi (i : Nat) : Option ByteProvFrag :=
      some { prov := prov, origAddr := addr2, byteIdx := i }
    let chimericSlice : List AbsByte := [
      .init b0 (f_lo 0), .init b1 (f_lo 1), .init b2 (f_lo 2), .init b3 (f_lo 3),
      .init b4 (f_hi 4), .init b5 (f_hi 5), .init b6 (f_hi 6), .init b7 (f_hi 7)
    ]
    reconstructProv chimericSlice = none := by
  dsimp only [reconstructProv, checkFragsFrom]
  simp [Ne.symm h_ne]

/-! ## 5. `InitSubsumes` and Forward Simulation -/

/-- `ByteSubsumes b_strict b_perm` holds when `b_strict` is either `.uninit` or
identical to `b_perm`. -/
def ByteSubsumes (b_strict b_perm : AbsByte) : Prop :=
  b_strict = .uninit ∨ b_strict = b_perm

/-- Pointwise byte refinement across an allocation. -/
inductive InitSubsumes : List AbsByte → List AbsByte → Prop where
  | nil : InitSubsumes [] []
  | cons {b_s b_p : AbsByte} {rest_s rest_p : List AbsByte} :
      ByteSubsumes b_s b_p → InitSubsumes rest_s rest_p →
      InitSubsumes (b_s :: rest_s) (b_p :: rest_p)

theorem ByteSubsumes.refl (b : AbsByte) : ByteSubsumes b b :=
  Or.inr rfl

theorem ByteSubsumes.trans {b1 b2 b3 : AbsByte}
    (h12 : ByteSubsumes b1 b2) (h23 : ByteSubsumes b2 b3) :
    ByteSubsumes b1 b3 := by
  rcases h12 with rfl | rfl
  · exact Or.inl rfl
  · exact h23

theorem InitSubsumes.refl (m : List AbsByte) : InitSubsumes m m := by
  induction m with
  | nil => exact InitSubsumes.nil
  | cons b rest ih => exact InitSubsumes.cons (ByteSubsumes.refl b) ih

theorem InitSubsumes.trans {m1 m2 m3 : List AbsByte}
    (h12 : InitSubsumes m1 m2) (h23 : InitSubsumes m2 m3) :
    InitSubsumes m1 m3 := by
  induction h12 generalizing m3 with
  | nil =>
      cases h23
      exact InitSubsumes.nil
  | cons hb _ ih =>
      cases h23 with
      | cons hb2 hrest2 =>
          exact InitSubsumes.cons (ByteSubsumes.trans hb hb2) (ih hrest2)

theorem InitSubsumes.length_eq {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) :
    m_strict.length = m_perm.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem InitSubsumes.append {a1 a2 b1 b2 : List AbsByte}
    (ha : InitSubsumes a1 a2) (hb : InitSubsumes b1 b2) :
    InitSubsumes (a1 ++ b1) (a2 ++ b2) := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact InitSubsumes.cons h ih

theorem InitSubsumes.drop {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (n : Nat) :
    InitSubsumes (m_strict.drop n) (m_perm.drop n) := by
  induction h generalizing n with
  | nil =>
      simp only [List.drop_nil]
      exact InitSubsumes.nil
  | cons hb hrest ih =>
      cases n with
      | zero => exact InitSubsumes.cons hb hrest
      | succ k => exact ih k

theorem InitSubsumes.take {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (n : Nat) :
    InitSubsumes (m_strict.take n) (m_perm.take n) := by
  induction h generalizing n with
  | nil =>
      simp only [List.take_nil]
      exact InitSubsumes.nil
  | cons hb _ ih =>
      cases n with
      | zero => exact InitSubsumes.nil
      | succ k => exact InitSubsumes.cons hb (ih k)

/-- Crucial lemma for `.Initialized` scalar reads: if `decodeInitBytes s_strict`
succeeds (`= some bs`), then NO byte in `s_strict` is `.uninit`; therefore by
`InitSubsumes s_strict s_perm`, `s_strict = s_perm` identically. -/
theorem decodeInitBytes_eq_of_subsumes {s_strict s_perm : List AbsByte}
    (h : InitSubsumes s_strict s_perm) {bs : List UInt8}
    (h_dec : decodeInitBytes s_strict = some bs) :
    s_strict = s_perm := by
  induction h generalizing bs with
  | nil => rfl
  | @cons b_s b_p tail_s tail_p hb htail ih =>
      rcases hb with rfl | rfl
      · simp [decodeInitBytes] at h_dec
      · cases b_s with
        | uninit => simp [decodeInitBytes] at h_dec
        | init val frag =>
            simp only [decodeInitBytes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h_dec
            rcases h_dec with ⟨tail_bs, h_tail_dec, _⟩
            rw [ih h_tail_dec]

/-- Forward simulation of `readScalarUnionAt` (`Scalar::Union`, e.g.
`MaybeUninit<u8>`) under `InitSubsumes`: both machines return raw slices of the
same length related by `InitSubsumes`. -/
theorem readScalarUnionAt_simulation {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (offset size : Nat)
    {slice_s : List AbsByte}
    (h_read : readScalarUnionAt m_strict offset size = some slice_s) :
    ∃ slice_p,
      readScalarUnionAt m_perm offset size = some slice_p ∧
      InitSubsumes slice_s slice_p := by
  unfold readScalarUnionAt extractSlice at h_read ⊢
  rw [← h.length_eq]
  split at h_read
  · rename_i h_inbounds
    injection h_read with h_eq
    subst h_eq
    refine ⟨(m_perm.drop offset).take size, if_pos h_inbounds, ?_⟩
    exact (h.drop offset).take size
  · contradiction

/-- Forward simulation of `readScalarInitializedAt` under `InitSubsumes`:
whenever the strict machine succeeds in reading an initialized scalar (whether
integer or pointer), the permissive machine succeeds and returns the **exact
same** `ScalarVal` (with identical value and provenance). -/
theorem readScalarInitializedAt_simulation {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (offset size : Nat) (readProv : Bool)
    {v : ScalarVal}
    (h_read : readScalarInitializedAt m_strict offset size readProv = some v) :
    readScalarInitializedAt m_perm offset size readProv = some v := by
  unfold readScalarInitializedAt at h_read ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_read ⊢
  rcases h_read with ⟨slice_s, h_ext_s, rawBytes, h_dec, h_rest⟩
  rcases readScalarUnionAt_simulation h offset size h_ext_s with ⟨slice_p, h_ext_p, h_sub⟩
  have h_slice_eq := decodeInitBytes_eq_of_subsumes h_sub h_dec
  subst h_slice_eq
  exact ⟨slice_s, h_ext_p, rawBytes, h_dec, h_rest⟩

def ReadResultSubsumes : ScalarVal ⊕ List AbsByte → ScalarVal ⊕ List AbsByte → Prop
  | .inl v_s, .inl v_p => v_s = v_p
  | .inr sl_s, .inr sl_p => InitSubsumes sl_s sl_p
  | _, _ => False

/-- Unified forward simulation of `readScalarAt` across both `.Initialized` and
`.Union` modes. -/
theorem readScalarAt_simulation {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (offset : Nat) (mode : ScalarLoadMode)
    {res_s : ScalarVal ⊕ List AbsByte}
    (h_read : readScalarAt m_strict offset mode = some res_s) :
    ∃ res_p,
      readScalarAt m_perm offset mode = some res_p ∧
      ReadResultSubsumes res_s res_p := by
  cases mode with
  | Initialized readProv size =>
      simp only [readScalarAt, Functor.map, Option.map] at h_read ⊢
      cases hv : readScalarInitializedAt m_strict offset size readProv with
      | none => rw [hv] at h_read; contradiction
      | some v =>
          rw [hv] at h_read
          injection h_read with h_eq
          subst h_eq
          have hv_p := readScalarInitializedAt_simulation h offset size readProv hv
          rw [hv_p]
          exact ⟨.inl v, rfl, rfl⟩
  | Union size =>
      simp only [readScalarAt, Functor.map, Option.map] at h_read ⊢
      cases hsl : readScalarUnionAt m_strict offset size with
      | none => rw [hsl] at h_read; contradiction
      | some sl_s =>
          rw [hsl] at h_read
          injection h_read with h_eq
          subst h_eq
          rcases readScalarUnionAt_simulation h offset size hsl with ⟨sl_p, hsl_p, hsub⟩
          rw [hsl_p]
          exact ⟨.inr sl_p, rfl, hsub⟩

/-- Splicing `InitSubsumes`-related slices at the same offset preserves
`InitSubsumes`. -/
theorem spliceAt_subsumes {m_strict m_perm new_s new_p : List AbsByte}
    (hm : InitSubsumes m_strict m_perm)
    (hnew : InitSubsumes new_s new_p) (offset : Nat) :
    InitSubsumes (spliceAt m_strict offset new_s) (spliceAt m_perm offset new_p) := by
  unfold spliceAt
  rw [hnew.length_eq]
  exact ((hm.take offset).append hnew).append (hm.drop (offset + new_p.length))

/-- Forward simulation of `writeScalarAt` under `InitSubsumes`. -/
theorem writeScalarAt_simulation {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (offset : Nat) (v : ScalarVal)
    {m_strict' : List AbsByte}
    (h_write : writeScalarAt m_strict offset v = some m_strict') :
    ∃ m_perm',
      writeScalarAt m_perm offset v = some m_perm' ∧
      InitSubsumes m_strict' m_perm' := by
  dsimp only [writeScalarAt] at h_write ⊢
  rw [← h.length_eq]
  split at h_write
  · rename_i h_inbounds
    injection h_write with h_eq
    subst h_eq
    refine ⟨spliceAt m_perm offset (encodeScalarBytes v), if_pos h_inbounds, ?_⟩
    exact spliceAt_subsumes h (InitSubsumes.refl _) offset
  · contradiction

/-- Forward simulation of `copyBytes` (`copyOp` / `copyNonOverlapping`) under
`InitSubsumes`. -/
theorem copyBytes_simulation {src_s src_p dst_s dst_p : List AbsByte}
    (hsrc : InitSubsumes src_s src_p) (hdst : InitSubsumes dst_s dst_p)
    (srcOff destOff size : Nat) {dst_s' : List AbsByte}
    (h_copy : copyBytes src_s dst_s srcOff destOff size = some dst_s') :
    ∃ dst_p',
      copyBytes src_p dst_p srcOff destOff size = some dst_p' ∧
      InitSubsumes dst_s' dst_p' := by
  unfold copyBytes at h_copy ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_copy ⊢
  rcases h_copy with ⟨slice_s, h_ext_s, h_sp⟩
  rcases readScalarUnionAt_simulation hsrc srcOff size h_ext_s with ⟨slice_p, h_ext_p, h_slice_sub⟩
  rw [← hdst.length_eq]
  split at h_sp
  · rename_i h_inbounds
    injection h_sp with h_eq
    subst h_eq
    refine ⟨spliceAt dst_p destOff slice_p, ⟨slice_p, h_ext_p, if_pos h_inbounds⟩, ?_⟩
    exact spliceAt_subsumes hdst h_slice_sub destOff
  · contradiction

/-- Deinitializing a range in `m_strict` (on `Operand::Move` when
`deinitOnMove = true`) while leaving `m_perm` (`deinitOnMove = false`) untouched
preserves `InitSubsumes`. -/
theorem uninit_replicate_subsumes (l : List AbsByte) :
    InitSubsumes (List.replicate l.length .uninit) l := by
  induction l with
  | nil => exact InitSubsumes.nil
  | cons b rest ih =>
      simp only [List.length_cons, List.replicate_succ]
      exact InitSubsumes.cons (Or.inl rfl) ih

theorem uninit_replicate_subsumes_of_len {n : Nat} {l : List AbsByte}
    (h : l.length = n) :
    InitSubsumes (List.replicate n .uninit) l := by
  subst h
  exact uninit_replicate_subsumes l

theorem self_eq_spliceAt_slice (m : List AbsByte) (offset size : Nat)
    (h_bounds : offset + size ≤ m.length) :
    m = spliceAt m offset ((m.drop offset).take size) := by
  unfold spliceAt
  have h_slice_len : ((m.drop offset).take size).length = size := by
    simp [List.length_take, List.length_drop]
    omega
  rw [h_slice_len, List.append_assoc]
  have h_drop_add : m.drop (offset + size) = (m.drop offset).drop size := by
    rw [List.drop_drop, Nat.add_comm]
  rw [h_drop_add, List.take_append_drop, List.take_append_drop]

theorem deinitRange_preserves_InitSubsumes {m_strict m_perm : List AbsByte}
    (h : InitSubsumes m_strict m_perm) (offset size : Nat)
    (h_bounds : offset + size ≤ m_strict.length) :
    InitSubsumes (deinitRange m_strict offset size) m_perm := by
  have h_len := h.length_eq
  have h_bounds_p : offset + size ≤ m_perm.length := by omega
  have h_slice_len : ((m_perm.drop offset).take size).length = size := by
    simp [List.length_take, List.length_drop]
    omega
  have h_mid : InitSubsumes (List.replicate size .uninit) ((m_perm.drop offset).take size) :=
    uninit_replicate_subsumes_of_len h_slice_len
  rw [self_eq_spliceAt_slice m_perm offset size h_bounds_p]
  exact spliceAt_subsumes h h_mid offset

/-! ## 6. Tree Borrows Interaction: `Retag` Simulation & Why `deinitOnMove` Must Omit TB `.Write` -/

inductive TBPerm where
  | Cell
  | ReservedFrz (conflicted : Bool)
  | ReservedIM
  | Unique
  | Frozen
  | Disabled
  deriving DecidableEq, Repr, Inhabited

inductive TBAccessKind where
  | Read
  | Write
  deriving DecidableEq, Repr, Inhabited

inductive TBRelPos where
  | Local
  | Foreign
  deriving DecidableEq, Repr, Inhabited

/-- Per-node transition matching `Miri.TreeBorrows.performAccess`
(`Miri/TreeBorrows/Permissions.lean:105-111`). -/
def tbPerformAccess (kind : TBAccessKind) (rel : TBRelPos) (perm : TBPerm) (isProt : Bool) :
    Option TBPerm :=
  match kind, rel with
  | .Read, .Local =>
      match perm with
      | .Disabled => none
      | p => some p
  | .Write, .Local =>
      match perm with
      | .Cell => some .Cell
      | .ReservedFrz true => if isProt then none else some .Unique
      | .ReservedFrz false | .ReservedIM | .Unique => some .Unique
      | .Frozen | .Disabled => none
  | .Read, .Foreign =>
      match perm with
      | .Cell => some .Cell
      | .Frozen => some .Frozen
      | .Disabled => some .Disabled
      | .ReservedFrz _ => if isProt then some (.ReservedFrz true) else some perm
      | .ReservedIM => if isProt then none else some .ReservedIM
      | .Unique => if isProt then some .Disabled else some .Frozen
  | .Write, .Foreign =>
      match perm with
      | .Cell => some .Cell
      | .ReservedIM => if isProt then none else some .ReservedIM
      | _ => some .Disabled

/-- Proof that if `M_strict` (`deinitOnMove = true`) performed a Tree Borrows
`.Write` access when moving from a `*r` place (where `r` has permission
`ReservedFrz false`, `isProt = false`) while `M_perm` (`deinitOnMove = false`)
only performed the `.Read` access of `copyOp`:
- `M_strict` transitions `r` from `ReservedFrz false` to `Unique`;
- `M_perm` leaves `r` at `ReservedFrz false`;
- After a subsequent foreign `.Read` and a local `.Write` through `r`,
  `M_strict` transitions `Unique → Frozen` and **rejects** the local `.Write`
  (`none`), whereas `M_perm` keeps `ReservedFrz false` across the foreign `.Read`
  and **accepts** the local `.Write` (`some .Unique`)—breaking lockstep
  `BorrowTree` equivalence.
Therefore, `deinitOnMove = true` must deinitialize via `deinitRange` (`writeUninit`)
*without* a Tree Borrows `.Write` transition. -/
theorem tb_write_on_move_breaks_borrow_tree_equiv :
    let initPerm := TBPerm.ReservedFrz false
    -- Strict machine performs Read + TB Write on move:
    let strictAfterMove :=
      (tbPerformAccess .Read .Local initPerm false).bind
        (fun p => tbPerformAccess .Write .Local p false)
    -- Permissive machine performs only Read on move:
    let permAfterMove := tbPerformAccess .Read .Local initPerm false
    -- Then a foreign Read followed by a local Write occurs:
    let afterForeignReadAndChildWrite (st : Option TBPerm) : Option TBPerm :=
      st.bind (fun p => tbPerformAccess .Read .Foreign p false)
      |>.bind (fun p => tbPerformAccess .Write .Local p false)
    strictAfterMove ≠ permAfterMove ∧
    afterForeignReadAndChildWrite strictAfterMove = none ∧
    afterForeignReadAndChildWrite permAfterMove = some .Unique := by
  decide

/-- Machine state pairing byte memory with abstract Tree Borrows state. -/
structure MachineState where
  mem : List AbsByte
  tbTree : List (Provenance × TBPerm)
  nextTag : Nat

def StateSubsumes (s_strict s_perm : MachineState) : Prop :=
  InitSubsumes s_strict.mem s_perm.mem ∧
  s_strict.tbTree = s_perm.tbTree ∧
  s_strict.nextTag = s_perm.nextTag

/-- Move-deinitialization in `M_strict` (`deinitRange` without mutating
`tbTree`) preserves `StateSubsumes` relative to `M_perm`. -/
theorem moveDeinit_preserves_StateSubsumes {s_strict s_perm : MachineState}
    (h : StateSubsumes s_strict s_perm) (offset size : Nat)
    (h_bounds : offset + size ≤ s_strict.mem.length) :
    StateSubsumes
      { s_strict with mem := deinitRange s_strict.mem offset size }
      s_perm := by
  rcases h with ⟨hmem, htb, htag⟩
  exact ⟨deinitRange_preserves_InitSubsumes hmem offset size h_bounds, htb, htag⟩

/-- Model of `Retag` (`Miri/TreeBorrows/RetagPipeline.lean:178-300` and
`FreezeVisitor.lean:74-135`):
1. Reads the 8-byte pointer scalar at `ptrSlotOffset` using
   `readScalarInitializedAt ... 8 true`;
2. Computes the new tag's initial permission purely from the static type layout
   (`isMutable`, `pointeeIsFreeze`) without inspecting pointee bytes in `mem`;
3. Appends the new tag to `tbTree` and writes the retagged pointer scalar back
   to `ptrSlotOffset`. -/
def retagPlace (st : MachineState) (ptrSlotOffset : Nat) (isMutable pointeeIsFreeze : Bool) :
    Option (MachineState × ScalarVal) := do
  let v ← readScalarInitializedAt st.mem ptrSlotOffset 8 true
  match v with
  | .ptr addr 8 oldProv =>
      let newProv : Provenance := { allocId := oldProv.allocId, tag := st.nextTag }
      let initPerm : TBPerm :=
        if isMutable then
          if pointeeIsFreeze then .ReservedFrz false else .ReservedIM
        else
          if pointeeIsFreeze then .Frozen else .Cell
      let newPtr := ScalarVal.ptr addr 8 newProv
      let mem' ← writeScalarAt st.mem ptrSlotOffset newPtr
      let st' : MachineState := {
        mem := mem'
        tbTree := (newProv, initPerm) :: st.tbTree
        nextTag := st.nextTag + 1
      }
      some (st', newPtr)
  | _ => none

/-- Forward simulation of `retagPlace` under `StateSubsumes`: because `Retag`
and `FreezeVisitor` depend only on the pointer scalar at `ptrSlotOffset` and
the static type layout (`isMutable`, `pointeeIsFreeze`)—never inspecting the
initialization mask of the pointee allocation—`StateSubsumes` is preserved in
lockstep. -/
theorem retagPlace_simulation {s_strict s_perm : MachineState}
    (h : StateSubsumes s_strict s_perm)
    (ptrSlotOffset : Nat) (isMutable pointeeIsFreeze : Bool)
    {s_strict' : MachineState} {newPtr : ScalarVal}
    (h_retag : retagPlace s_strict ptrSlotOffset isMutable pointeeIsFreeze =
      some (s_strict', newPtr)) :
    ∃ s_perm',
      retagPlace s_perm ptrSlotOffset isMutable pointeeIsFreeze = some (s_perm', newPtr) ∧
      StateSubsumes s_strict' s_perm' := by
  rcases h with ⟨hmem, htb, htag⟩
  unfold retagPlace at h_retag ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_retag ⊢
  rcases h_retag with ⟨v, hv_s, h_rest⟩
  have hv_p := readScalarInitializedAt_simulation hmem ptrSlotOffset 8 true hv_s
  cases v with
  | int _ _ => simp at h_rest
  | ptr addr sz oldProv =>
      by_cases hsz : sz = 8
      · subst hsz
        simp only [Option.bind_eq_some_iff] at h_rest
        rcases h_rest with ⟨mem_s', hwrite_s, h_eq⟩
        injection h_eq with h_pair_eq
        injection h_pair_eq with h_st_eq h_ptr_eq
        subst h_st_eq h_ptr_eq
        rcases writeScalarAt_simulation hmem ptrSlotOffset
          (.ptr addr 8 { allocId := oldProv.allocId, tag := s_strict.nextTag }) hwrite_s
          with ⟨mem_p', hwrite_p, hmem_sub⟩
        refine ⟨{
          mem := mem_p'
          tbTree := ({ allocId := oldProv.allocId, tag := s_strict.nextTag },
            if isMutable then
              if pointeeIsFreeze then .ReservedFrz false else .ReservedIM
            else
              if pointeeIsFreeze then .Frozen else .Cell) :: s_perm.tbTree
          nextTag := s_perm.nextTag + 1
        }, ?_, ?_⟩
        · refine ⟨.ptr addr 8 oldProv, hv_p, ?_⟩
          simp only [Option.bind_eq_some_iff]
          rw [← htag]
          exact ⟨mem_p', hwrite_p, rfl⟩
        · exact ⟨hmem_sub, by rw [htb], by rw [htag]⟩
      · simp [hsz] at h_rest

/-- Model of `deallocate` (`Miri/TreeBorrows/TreeState.lean:1076-1156`
`BorrowTree.deallocateBorrowRange`): checks `tbTree` for any strongly protected
accessed tag in the allocation and resets the allocation's bytes, without
inspecting `mem` byte initialization. -/
def deallocateAlloc (st : MachineState) (hasActiveStrongProtector : Bool) :
    Option MachineState :=
  if hasActiveStrongProtector then
    none
  else
    some { st with mem := [], tbTree := [] }

theorem deallocateAlloc_simulation {s_strict s_perm : MachineState}
    (h : StateSubsumes s_strict s_perm) (hasActiveStrongProtector : Bool)
    {s_strict' : MachineState}
    (h_dealloc : deallocateAlloc s_strict hasActiveStrongProtector = some s_strict') :
    ∃ s_perm',
      deallocateAlloc s_perm hasActiveStrongProtector = some s_perm' ∧
      StateSubsumes s_strict' s_perm' := by
  rcases h with ⟨_, _, htag⟩
  unfold deallocateAlloc at h_dealloc ⊢
  split at h_dealloc
  · contradiction
  · rename_i h_not_prot
    injection h_dealloc with h_eq
    subst h_eq
    exact ⟨{ s_perm with mem := [], tbTree := [] }, if_neg h_not_prot, ⟨InitSubsumes.nil, rfl, htag⟩⟩

/-! ## 7. Axiom Audit (`#print axioms`) -/

#print axioms byte_by_byte_maybe_uninit_copy_preserves_prov
#print axioms u8_copy_strips_prov
#print axioms chimeric_splice_strips_prov
#print axioms chimeric_splice_general_strips_prov
#print axioms readScalarInitializedAt_simulation
#print axioms readScalarUnionAt_simulation
#print axioms readScalarAt_simulation
#print axioms writeScalarAt_simulation
#print axioms copyBytes_simulation
#print axioms deinitRange_preserves_InitSubsumes
#print axioms tb_write_on_move_breaks_borrow_tree_equiv
#print axioms moveDeinit_preserves_StateSubsumes
#print axioms retagPlace_simulation
#print axioms deallocateAlloc_simulation

end LeanMiriInitSubsumesAndFragProbe
