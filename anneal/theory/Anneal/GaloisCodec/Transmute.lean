-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Anneal.MirMemComp.Memory
public import Anneal.GaloisCodec.Laws

public section

/-!
# Zero-Copy Trait Laws, Transmute Composition, & Padded Products (`Transmute`)

Mechanizes `zerocopy` byte-conversion traits (`IntoBytes`, `FromZeros`,
`FromBytes`), provenance-discipline predicates (`CodecNoProv`, `CodecWithProv`),
zero-copy transmute totality/composition/round-trip laws under the 3-level
`OptProvLe` byte order, padded `#[repr(C)]` product codecs, and `MemoryState`
zero-copy view bridges over `ByteCodec`:

1. **`zerocopy` Trait Hierarchy & Provenance Discipline (`CodecIntoBytes`,
   `CodecFromZeros`, `CodecFromBytes`, `CodecNoProv`, `CodecWithProv`):**
   - `CodecIntoBytes c`: fixed length + `allBytesInit (c.encode v) = true` (zero
     `.uninit` padding bytes; `allBytesInit` defined via `List.foldr`, `0`
     `._unsafe_rec`).
   - `CodecFromZeros c`: `List.replicate c.byteSize (.init 0 none)` decodes.
   - `CodecFromBytes c`: every fully initialized slice of length `c.byteSize`
     decodes (`codecFromZeros_of_codecFromBytes`).
   - `CodecNoProv c`: every encoded byte carries `prov = none` (holds for all
     scalar/POD/struct-without-pointers codecs and `Trusted.MirSemantics`'s
     `encodeVal`).
   - `CodecWithProv c`: every encoded byte is `.init _ (some _)` (maximal
     elements of the 3-level `AllocByteLe` order).
2. **Transmute Totality, Composition, Round-Trip, & Valid-Slice Inclusion:**
   - `transmute_total_of_intoBytes_fromBytes`: equal-size `CodecIntoBytes ca`
     and `CodecFromBytes cb` guarantee total `codecTransmute ca cb`.
   - `encode_eq_of_transmute_intoBytes_encodeLeast_noProv`: when `ca` satisfies
     `CodecNoProv` and `cb` satisfies `CodecIntoBytes` + `CodecEncodeLeast`,
     any `cb.decode (ca.encode a) = some b` forces `cb.encode b = ca.encode a`.
   - `transmute_comp_of_total_intoBytes_encodeLeast_noProv`: total `A → B` with
     `CodecNoProv ca`, `CodecIntoBytes cb`, and `CodecEncodeLeast cb` composes
     `(A → B) >>= (B → C) = (A → C)` with zero hypotheses on `C` (and
     `transmute_roundtrip_of_total_intoBytes_encodeLeast_decodeEncode_noProv`
     recovers `some a` under `CodecDecodeEncode ca`).
   - `encode_eq_of_transmute_withProv_encodeLeast` &
     `transmute_comp_of_total_withProv_encodeLeast`: dual byte-preservation and
     composition laws when the middle codec `cb` preserves provenance
     (`CodecWithProv cb` + `CodecEncodeLeast cb`), without requiring
     `CodecNoProv ca`.
   - `transmuteTotal_iff_valid_subset_of_galois`: under `CodecDecodeEncode ca`,
     `CodecEncodeLeast ca`, and `CodecDecodeMono cb`, `A → B` is total iff
     every byte slice valid for `ca` is valid for `cb`.
3. **Disjoint Padded Product (`pairPaddedCodec`) & `MemoryState` Bridge:**
   - `pairPaddedCodec ca padLen cb` models `(A, [uninit; padLen], B)`: preserves
     `GaloisLayoutCodec`, `CodecFromBytes`, and `CodecNoProv` for any `padLen`,
     satisfies `CodecIntoBytes` when `padLen = 0`, and refutes `CodecIntoBytes`
     when `padLen > 0` on inhabited types.
   - `execReadDecode_after_execWriteEncode_eq_transmute`: for any positive byte
     size (`Nat.beq ca.byteSize 0 = false`), writing `ca.encode a` via
     `Anneal.MirMemComp.execWriteBytes` and reading via `execReadBytes` +
     `cb.decode` produces `.ok (codecTransmute ca cb a)`.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every declaration compiles using
at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.GaloisCodec

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirMemComp

/-! ## Part I: Byte Initialization, Provenance, & `zerocopy` Traits -/

private theorem natBeq_refl_tr : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | n + 1 => natBeq_refl_tr n

private theorem natEq_of_beq_tr : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq_tr h)

private theorem natLe_of_ble_tr : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, b, _ => Nat.zero_le b
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (natLe_of_ble_tr h)

/-- True iff `b` is an initialized byte `.init _ _`. -/
@[expose] def isInitByte (b : AllocByte) : Bool :=
  match b with
  | .uninit => false
  | .init _ _ => true

/-- True iff every byte in `bs` is initialized (`.init _ _`), defined via
`List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def allBytesInit (bs : List AllocByte) : Bool :=
  List.foldr (fun b ih => isInitByte b && ih) true bs

/-- True iff `b` carries no pointer provenance (`.uninit` or `.init _ none`). -/
@[expose] def isNoProvByte (b : AllocByte) : Bool :=
  match b with
  | .uninit => true
  | .init _ none => true
  | .init _ (some _) => false

/-- True iff no byte in `bs` carries pointer provenance, defined via
`List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def allBytesNoProv (bs : List AllocByte) : Bool :=
  List.foldr (fun b ih => isNoProvByte b && ih) true bs

/-- True iff `b` is an initialized byte carrying concrete provenance
(`.init _ (some _)`). -/
@[expose] def isWithProvByte (b : AllocByte) : Bool :=
  match b with
  | .uninit => false
  | .init _ none => false
  | .init _ (some _) => true

/-- True iff every byte in `bs` is initialized with concrete provenance
(`.init _ (some _)`), defined via `List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def allBytesWithProv (bs : List AllocByte) : Bool :=
  List.foldr (fun b ih => isWithProvByte b && ih) true bs

/-- `allBytesInit` distributes across list concatenation. -/
theorem allBytesInit_append :
    ∀ (xs ys : List AllocByte),
      allBytesInit (xs ++ ys) = (allBytesInit xs && allBytesInit ys)
  | [], _ => rfl
  | b :: xs, ys => by
    change (isInitByte b && allBytesInit (xs ++ ys)) =
      (isInitByte b && allBytesInit xs && allBytesInit ys)
    rw [allBytesInit_append xs ys, Bool.and_assoc]

/-- `allBytesNoProv` distributes across list concatenation. -/
theorem allBytesNoProv_append :
    ∀ (xs ys : List AllocByte),
      allBytesNoProv (xs ++ ys) = (allBytesNoProv xs && allBytesNoProv ys)
  | [], _ => rfl
  | b :: xs, ys => by
    change (isNoProvByte b && allBytesNoProv (xs ++ ys)) =
      (isNoProvByte b && allBytesNoProv xs && allBytesNoProv ys)
    rw [allBytesNoProv_append xs ys, Bool.and_assoc]

/-- Replicating any initialized byte produces an `allBytesInit = true` list. -/
theorem allBytesInit_replicate_init (val : UInt8) (prov : Option AllocId) :
    ∀ n : Nat, allBytesInit (List.replicate n (.init val prov)) = true
  | 0 => rfl
  | n + 1 => allBytesInit_replicate_init val prov n

/-- Replicating `.uninit` produces an `allBytesNoProv = true` list. -/
theorem allBytesNoProv_replicate_uninit :
    ∀ n : Nat, allBytesNoProv (List.replicate n .uninit) = true
  | 0 => rfl
  | n + 1 => allBytesNoProv_replicate_uninit n

/-- Maximality for initialized slices refining provenance-free targets (`[]`
zero axioms): if `allBytesInit xs = true`, `allBytesNoProv ys = true`, and
`AllocBytesLe xs ys`, then `xs = ys`. -/
theorem allocBytesLe_eq_of_allBytesInit_noProvTarget :
    ∀ {xs ys : List AllocByte},
      allBytesInit xs = true → allBytesNoProv ys = true →
      AllocBytesLe xs ys → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hLe => False.elim hLe
  | .uninit :: _, _, hInit, _, _ => Bool.noConfusion hInit
  | .init _ _ :: _, [], _, _, hLe => False.elim hLe
  | .init _ _ :: _, .uninit :: _, _, _, hLe => False.elim hLe.1
  | .init _ px :: xs, .init _ py :: ys, hInit, hNoProv, hLe => by
    cases py with
    | some _ => exact Bool.noConfusion hNoProv
    | none =>
      cases px with
      | some _ => exact False.elim hLe.1.2
      | none =>
        change allBytesInit xs = true at hInit
        change allBytesNoProv ys = true at hNoProv
        rw [hLe.1.1,
          allocBytesLe_eq_of_allBytesInit_noProvTarget hInit hNoProv hLe.2]

/-- Maximality for fully provenance-bearing byte vectors (`[]` zero axioms): if
`allBytesWithProv xs = true` and `AllocBytesLe xs ys`, then `xs = ys`. -/
theorem allocBytesLe_eq_of_allBytesWithProv :
    ∀ {xs ys : List AllocByte},
      allBytesWithProv xs = true → AllocBytesLe xs ys → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, hLe => False.elim hLe
  | .uninit :: _, _, hProv, _ => Bool.noConfusion hProv
  | .init _ none :: _, _, hProv, _ => Bool.noConfusion hProv
  | .init _ (some _) :: _, [], _, hLe => False.elim hLe
  | .init _ (some _) :: _, .uninit :: _, _, hLe => False.elim hLe.1
  | .init _ (some _) :: _, .init _ none :: _, _, hLe => False.elim hLe.1.2
  | .init _ (some _) :: xs, .init _ (some _) :: ys, hProv, hLe => by
    change allBytesWithProv xs = true at hProv
    rw [hLe.1.1, hLe.1.2, allocBytesLe_eq_of_allBytesWithProv hProv hLe.2]

/-- `zerocopy::IntoBytes` contract: every encoded value has length `c.byteSize`
and contains zero `.uninit` bytes. -/
structure CodecIntoBytes {V : Type} (c : ByteCodec V) : Prop where
  encodeLen : CodecEncodeLen c
  noUninit : ∀ v : V, allBytesInit (c.encode v) = true

/-- Provenance-free encoding discipline: `c.encode v` never emits pointer
provenance (satisfied by all scalar and POD codecs, matching
`Trusted.MirSemantics.encodeVal`). -/
@[expose] def CodecNoProv {V : Type} (c : ByteCodec V) : Prop :=
  ∀ v : V, allBytesNoProv (c.encode v) = true

/-- Strict-provenance encoding discipline: every byte emitted by `c.encode v`
carries concrete provenance `.init _ (some _)`. -/
@[expose] def CodecWithProv {V : Type} (c : ByteCodec V) : Prop :=
  ∀ v : V, allBytesWithProv (c.encode v) = true

/-- `zerocopy::FromZeros` contract: `c.byteSize` zero bytes without provenance
decode to some value `v₀ : V`. -/
@[expose] def CodecFromZeros {V : Type} (c : ByteCodec V) : Prop :=
  ∃ v₀ : V, c.decode (List.replicate c.byteSize (.init 0 none)) = some v₀

/-- `zerocopy::FromBytes` contract: every fully initialized slice of length
`c.byteSize` decodes to some `v : V`. -/
@[expose] def CodecFromBytes {V : Type} (c : ByteCodec V) : Prop :=
  ∀ bs : List AllocByte,
    bs.length = c.byteSize → allBytesInit bs = true →
      ∃ v : V, c.decode bs = some v

/-- `zerocopy` supertrait implication `CodecFromBytes c → CodecFromZeros c`. -/
theorem codecFromZeros_of_codecFromBytes {V : Type} {c : ByteCodec V}
    (hFB : CodecFromBytes c) : CodecFromZeros c :=
  hFB (List.replicate c.byteSize (.init 0 none))
    (List.length_replicate)
    (allBytesInit_replicate_init 0 none c.byteSize)

/-! ## Part II: Zero-Copy Transmute Totality, Composition, & Round-Trip -/

/-- Pure byte-level `try_transmute` (`cb.decode (ca.encode a)`). -/
@[expose] def codecTransmute {A B : Type} (ca : ByteCodec A) (cb : ByteCodec B)
    (a : A) : Option B :=
  cb.decode (ca.encode a)

/-- `codecTransmute ca cb` is total when every `a : A` decodes to `some b`. -/
@[expose] def CodecTransmuteTotal {A B : Type} (ca : ByteCodec A)
    (cb : ByteCodec B) : Prop :=
  ∀ a : A, ∃ b : B, codecTransmute ca cb a = some b

/-- `zerocopy::transmute!` soundness (`[]` zero axioms): equal-size
`CodecIntoBytes ca` and `CodecFromBytes cb` guarantee `CodecTransmuteTotal ca
cb` without requiring any representation law on `ca` or `cb`. -/
theorem transmute_total_of_intoBytes_fromBytes {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B}
    (hSize : ca.byteSize = cb.byteSize)
    (hIB : CodecIntoBytes ca) (hFB : CodecFromBytes cb) :
    CodecTransmuteTotal ca cb := by
  intro a
  have hLen : (ca.encode a).length = cb.byteSize := by
    rw [hIB.encodeLen a]
    exact hSize
  exact hFB (ca.encode a) hLen (hIB.noUninit a)

/-- Exact byte-preservation lemma for provenance-free sources (`[]` zero
axioms): when `ca` satisfies `CodecNoProv` and `cb` satisfies `CodecIntoBytes`
and `CodecEncodeLeast`, any `codecTransmute ca cb a = some b` forces
`cb.encode b = ca.encode a`. -/
theorem encode_eq_of_transmute_intoBytes_encodeLeast_noProv {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B}
    (hNoProv : CodecNoProv ca)
    (hIB : CodecIntoBytes cb) (hEL : CodecEncodeLeast cb)
    {a : A} {b : B} (hTr : codecTransmute ca cb a = some b) :
    cb.encode b = ca.encode a :=
  allocBytesLe_eq_of_allBytesInit_noProvTarget
    (hIB.noUninit b) (hNoProv a) (hEL (ca.encode a) b hTr)

/-- Transmute composition law for provenance-free sources (`[]` zero axioms):
if `ca` satisfies `CodecNoProv`, `ca → cb` is total, and the middle codec `cb`
satisfies `CodecIntoBytes` and `CodecEncodeLeast`, then transmuting `A → B → C`
equals transmuting `A → C` for every target codec `cc` (with nothing assumed
about `cc`). -/
theorem transmute_comp_of_total_intoBytes_encodeLeast_noProv {A B C : Type}
    {ca : ByteCodec A} {cb : ByteCodec B} (cc : ByteCodec C)
    (hNoProv : CodecNoProv ca)
    (hTot : CodecTransmuteTotal ca cb)
    (hIB : CodecIntoBytes cb) (hEL : CodecEncodeLeast cb) (a : A) :
    Option.bind (codecTransmute ca cb a) (codecTransmute cb cc) =
      codecTransmute ca cc a := by
  cases hTot a with
  | intro b hb =>
    have hEncEq : cb.encode b = ca.encode a :=
      encode_eq_of_transmute_intoBytes_encodeLeast_noProv hNoProv hIB hEL hb
    rw [hb]
    dsimp only [Option.bind, codecTransmute]
    rw [hEncEq]

/-- Round-trip `A → B → A` law for provenance-free sources (`[]` zero axioms):
if `ca` satisfies `CodecNoProv` and `CodecDecodeEncode`, `ca → cb` is total,
and `cb` satisfies `CodecIntoBytes` + `CodecEncodeLeast`, then transmuting
`a : A` to `B` and back to `A` yields `some a`. -/
theorem transmute_roundtrip_of_total_intoBytes_encodeLeast_decodeEncode_noProv
    {A B : Type} {ca : ByteCodec A} {cb : ByteCodec B}
    (hNoProv : CodecNoProv ca)
    (hTot : CodecTransmuteTotal ca cb)
    (hIB : CodecIntoBytes cb) (hEL : CodecEncodeLeast cb)
    (hDE : CodecDecodeEncode ca) (a : A) :
    Option.bind (codecTransmute ca cb a) (codecTransmute cb ca) = some a := by
  rw [transmute_comp_of_total_intoBytes_encodeLeast_noProv
    ca hNoProv hTot hIB hEL a]
  exact hDE a

/-- Exact byte-preservation lemma for provenance-preserving middle codecs (`[]`
zero axioms): when `cb` satisfies `CodecWithProv` and `CodecEncodeLeast`, any
`codecTransmute ca cb a = some b` forces `cb.encode b = ca.encode a` without
requiring `CodecNoProv ca`. -/
theorem encode_eq_of_transmute_withProv_encodeLeast {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B}
    (hWP : CodecWithProv cb) (hEL : CodecEncodeLeast cb)
    {a : A} {b : B} (hTr : codecTransmute ca cb a = some b) :
    cb.encode b = ca.encode a :=
  allocBytesLe_eq_of_allBytesWithProv (hWP b) (hEL (ca.encode a) b hTr)

/-- Transmute composition law for provenance-preserving middle codecs (`[]`
zero axioms): if `ca → cb` is total and `cb` satisfies `CodecWithProv` +
`CodecEncodeLeast`, then `A → B → C` equals `A → C` for every target `cc`. -/
theorem transmute_comp_of_total_withProv_encodeLeast {A B C : Type}
    {ca : ByteCodec A} {cb : ByteCodec B} (cc : ByteCodec C)
    (hTot : CodecTransmuteTotal ca cb)
    (hWP : CodecWithProv cb) (hEL : CodecEncodeLeast cb) (a : A) :
    Option.bind (codecTransmute ca cb a) (codecTransmute cb cc) =
      codecTransmute ca cc a := by
  cases hTot a with
  | intro b hb =>
    have hEncEq : cb.encode b = ca.encode a :=
      encode_eq_of_transmute_withProv_encodeLeast hWP hEL hb
    rw [hb]
    dsimp only [Option.bind, codecTransmute]
    rw [hEncEq]

/-- Valid-slice inclusion characterization (`[]` zero axioms): under
`CodecDecodeEncode ca`, `CodecEncodeLeast ca`, and `CodecDecodeMono cb`,
`CodecTransmuteTotal ca cb` holds iff every byte slice decoding under `ca` also
decodes under `cb`. -/
theorem transmuteTotal_iff_valid_subset_of_galois {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B}
    (hDEa : CodecDecodeEncode ca) (hELa : CodecEncodeLeast ca)
    (hMb : CodecDecodeMono cb) :
    CodecTransmuteTotal ca cb ↔
      (∀ (bs : List AllocByte) (a : A),
        ca.decode bs = some a → ∃ b : B, cb.decode bs = some b) := by
  refine ⟨?_, ?_⟩
  · intro hTot bs a hDecA
    cases hTot a with
    | intro b hb =>
      have hLe : AllocBytesLe (ca.encode a) bs := hELa bs a hDecA
      have hMono : OptValLe (cb.decode (ca.encode a)) (cb.decode bs) :=
        hMb (ca.encode a) bs hLe
      unfold codecTransmute at hb
      rw [hb] at hMono
      cases hDecB : cb.decode bs with
      | none =>
        rw [hDecB] at hMono
        exact False.elim hMono
      | some b' => exact ⟨b', rfl⟩
  · intro hSub a
    exact hSub (ca.encode a) a (hDEa a)

/-! ## Part III: Disjoint Padded Product Codec (`#[repr(C)]` Pair + Padding) -/

private theorem listTake_append_exact :
    ∀ (xs ys : List AllocByte), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys =>
    congrArg (List.cons x) (listTake_append_exact xs ys)

private theorem listDrop_append_exact :
    ∀ (xs ys : List AllocByte), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => listDrop_append_exact xs ys

private theorem allocBytesLe_take :
    ∀ (n : Nat) {xs ys : List AllocByte},
      AllocBytesLe xs ys → AllocBytesLe (xs.take n) (ys.take n)
  | 0, _, _, _ => True.intro
  | _ + 1, [], [], _ => True.intro
  | _ + 1, [], _ :: _, h => False.elim h
  | _ + 1, _ :: _, [], h => False.elim h
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, allocBytesLe_take n h.2⟩

private theorem allocBytesLe_drop :
    ∀ (n : Nat) {xs ys : List AllocByte},
      AllocBytesLe xs ys → AllocBytesLe (xs.drop n) (ys.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => True.intro
  | _ + 1, [], _ :: _, h => False.elim h
  | _ + 1, _ :: _, [], h => False.elim h
  | n + 1, _ :: _, _ :: _, h => allocBytesLe_drop n h.2

private theorem listSplit_take_drop :
    ∀ (n : Nat) (bs : List AllocByte), bs.take n ++ bs.drop n = bs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, b :: bs => congrArg (List.cons b) (listSplit_take_drop n bs)

private theorem listDrop_nil : ∀ k : Nat, ([] : List AllocByte).drop k = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem natZero_sub : ∀ k : Nat, 0 - k = 0
  | 0 => rfl
  | k + 1 => congrArg Nat.pred (natZero_sub k)

private theorem natSucc_sub_succ (a : Nat) :
    ∀ b : Nat, (a + 1) - (b + 1) = a - b
  | 0 => rfl
  | b + 1 => congrArg Nat.pred (natSucc_sub_succ a b)

private theorem listDrop_drop :
    ∀ (m n : Nat) (bs : List AllocByte),
      (bs.drop m).drop n = bs.drop (m + n)
  | 0, n, bs => by
    rw [Nat.zero_add]
    rfl
  | m + 1, n, [] => by
    change ([] : List AllocByte).drop n =
      ([] : List AllocByte).drop (m + 1 + n)
    rw [listDrop_nil, listDrop_nil]
  | m + 1, n, _ :: bs => by
    rw [Nat.succ_add]
    exact listDrop_drop m n bs

private theorem listLength_take_of_le :
    ∀ (n : Nat) (bs : List AllocByte),
      n ≤ bs.length → (bs.take n).length = n
  | 0, _, _ => rfl
  | _ + 1, [], hLe => nomatch hLe
  | n + 1, _ :: bs, hLe =>
    congrArg Nat.succ (listLength_take_of_le n bs (Nat.le_of_succ_le_succ hLe))

private theorem listLength_drop :
    ∀ (n : Nat) (bs : List AllocByte),
      (bs.drop n).length = bs.length - n
  | 0, _ => rfl
  | n + 1, [] => by
    change 0 = 0 - (n + 1)
    rw [natZero_sub]
  | n + 1, _ :: bs => by
    change (bs.drop n).length = (bs.length + 1) - (n + 1)
    rw [natSucc_sub_succ, listLength_drop n bs]

private theorem allBytesInit_take :
    ∀ (n : Nat) {bs : List AllocByte},
      allBytesInit bs = true → allBytesInit (bs.take n) = true
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | n + 1, b :: bs, h => by
    change (isInitByte b && allBytesInit bs) = true at h
    change (isInitByte b && allBytesInit (bs.take n)) = true
    cases hb : isInitByte b with
    | false =>
      rw [hb] at h
      exact Bool.noConfusion h
    | true =>
      rw [hb] at h
      exact allBytesInit_take n h

private theorem allBytesInit_drop :
    ∀ (n : Nat) {bs : List AllocByte},
      allBytesInit bs = true → allBytesInit (bs.drop n) = true
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | n + 1, b :: bs, h => by
    change (isInitByte b && allBytesInit bs) = true at h
    cases hb : isInitByte b with
    | false =>
      rw [hb] at h
      exact Bool.noConfusion h
    | true =>
      rw [hb] at h
      exact allBytesInit_drop n h

/-- Two-field `#[repr(C)]` product codec placing `ca` at `[0, ca.byteSize)`,
`padLen` `.uninit` padding bytes at `[ca.byteSize, ca.byteSize + padLen)`, and
`cb` at `[ca.byteSize + padLen, ca.byteSize + padLen + cb.byteSize)`. -/
@[expose] def pairPaddedCodec {A B : Type} (ca : ByteCodec A) (padLen : Nat)
    (cb : ByteCodec B) : ByteCodec (A × B) where
  byteSize := ca.byteSize + padLen + cb.byteSize
  encode p :=
    (ca.encode p.1 ++ List.replicate padLen .uninit) ++ cb.encode p.2
  decode bs :=
    if Nat.beq bs.length (ca.byteSize + padLen + cb.byteSize) then
      match ca.decode (bs.take ca.byteSize) with
      | none => none
      | some a =>
        match cb.decode (bs.drop (ca.byteSize + padLen)) with
        | none => none
        | some b => some (a, b)
    else
      none

/-- Product preservation (`[propext]` only): `pairPaddedCodec` preserves
`GaloisLayoutCodec` for any `padLen : Nat`. -/
theorem galoisLayoutCodec_pairPadded {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B} (padLen : Nat)
    (hGa : GaloisLayoutCodec ca) (hGb : GaloisLayoutCodec cb) :
    GaloisLayoutCodec (pairPaddedCodec ca padLen cb) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    dsimp only [pairPaddedCodec]
    rw [List.length_append, List.length_append, hGa.encodeLen p.1,
      List.length_replicate, hGb.encodeLen p.2]
  · intro bs p hDec
    dsimp only [pairPaddedCodec] at hDec
    cases hLen : Nat.beq bs.length (ca.byteSize + padLen + cb.byteSize) with
    | false =>
      rw [hLen] at hDec
      nomatch hDec
    | true => exact natEq_of_beq_tr hLen
  · intro xs ys hxy
    have hLenEq : xs.length = ys.length := allocBytesLe_length_eq hxy
    dsimp only [pairPaddedCodec]
    rw [← hLenEq]
    cases Nat.beq xs.length (ca.byteSize + padLen + cb.byteSize) with
    | false => exact True.intro
    | true =>
      have hMa := hGa.decodeMono (xs.take ca.byteSize) (ys.take ca.byteSize)
        (allocBytesLe_take ca.byteSize hxy)
      have hMb := hGb.decodeMono
        (xs.drop (ca.byteSize + padLen))
        (ys.drop (ca.byteSize + padLen))
        (allocBytesLe_drop (ca.byteSize + padLen) hxy)
      cases hXa : ca.decode (xs.take ca.byteSize) with
      | none => exact True.intro
      | some a =>
        rw [hXa] at hMa
        cases hXb : cb.decode (xs.drop (ca.byteSize + padLen)) with
        | none => exact True.intro
        | some b =>
          rw [hXb] at hMb
          cases hYa : ca.decode (ys.take ca.byteSize) with
          | none =>
            rw [hYa] at hMa
            exact False.elim hMa
          | some a' =>
            rw [hYa] at hMa
            cases hYb : cb.decode (ys.drop (ca.byteSize + padLen)) with
            | none =>
              rw [hYb] at hMb
              exact False.elim hMb
            | some b' =>
              rw [hYb] at hMb
              dsimp only [OptValLe]
              rw [hMa, hMb]
              rfl
  · intro p
    have hEncLen :
        ((ca.encode p.1 ++ List.replicate padLen AllocByte.uninit) ++
          cb.encode p.2).length = ca.byteSize + padLen + cb.byteSize := by
      rw [List.length_append, List.length_append, hGa.encodeLen p.1,
        List.length_replicate, hGb.encodeLen p.2]
    have hTakeA :
        (((ca.encode p.1 ++ List.replicate padLen AllocByte.uninit) ++
          cb.encode p.2).take ca.byteSize) = ca.encode p.1 := by
      rw [List.append_assoc, ← hGa.encodeLen p.1]
      exact listTake_append_exact (ca.encode p.1)
        (List.replicate padLen AllocByte.uninit ++ cb.encode p.2)
    have hDropB :
        (((ca.encode p.1 ++ List.replicate padLen AllocByte.uninit) ++
          cb.encode p.2).drop (ca.byteSize + padLen)) = cb.encode p.2 := by
      have hPreLen :
          (ca.encode p.1 ++ List.replicate padLen AllocByte.uninit).length =
            ca.byteSize + padLen := by
        rw [List.length_append, hGa.encodeLen p.1, List.length_replicate]
      rw [← hPreLen]
      exact listDrop_append_exact
        (ca.encode p.1 ++ List.replicate padLen AllocByte.uninit)
        (cb.encode p.2)
    dsimp only [pairPaddedCodec]
    rw [hEncLen, natBeq_refl_tr (ca.byteSize + padLen + cb.byteSize)]
    rw [hTakeA, hGa.decodeEncode p.1, hDropB, hGb.decodeEncode p.2]
    cases p
    rfl
  · intro bs p hDec
    dsimp only [pairPaddedCodec] at hDec
    cases hLenB : Nat.beq bs.length (ca.byteSize + padLen + cb.byteSize) with
    | false =>
      rw [hLenB] at hDec
      nomatch hDec
    | true =>
      rw [hLenB] at hDec
      have hLen : bs.length = ca.byteSize + padLen + cb.byteSize :=
        natEq_of_beq_tr hLenB
      cases hDa : ca.decode (bs.take ca.byteSize) with
      | none =>
        rw [hDa] at hDec
        nomatch hDec
      | some a =>
        rw [hDa] at hDec
        cases hDb : cb.decode (bs.drop (ca.byteSize + padLen)) with
        | none =>
          rw [hDb] at hDec
          nomatch hDec
        | some b =>
          rw [hDb] at hDec
          injection hDec with hpEq
          rw [← hpEq]
          dsimp only [pairPaddedCodec]
          let mid : List AllocByte := (bs.drop ca.byteSize).take padLen
          have hMidLen : mid.length = padLen := by
            apply listLength_take_of_le padLen (bs.drop ca.byteSize)
            rw [listLength_drop, hLen, Nat.add_assoc,
              Nat.add_sub_cancel_left]
            exact Nat.le_add_right padLen cb.byteSize
          have hPadLe :
              AllocBytesLe (List.replicate padLen AllocByte.uninit) mid := by
            rw [← hMidLen]
            exact allocBytesLe_uninit_replicate mid
          have hDecomp :
              (bs.take ca.byteSize ++ mid) ++
                bs.drop (ca.byteSize + padLen) = bs := by
            dsimp only [mid]
            rw [List.append_assoc, ← listDrop_drop ca.byteSize padLen bs,
              listSplit_take_drop padLen (bs.drop ca.byteSize),
              listSplit_take_drop ca.byteSize bs]
          rw [← hDecomp]
          exact allocBytesLe_append
            (allocBytesLe_append (hGa.encodeLeast _ a hDa) hPadLe)
            (hGb.encodeLeast _ b hDb)

/-- `CodecFromBytes` is preserved by `pairPaddedCodec` for any `padLen`
(`[propext]` only). -/
theorem codecFromBytes_pairPadded {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B} (padLen : Nat)
    (hFBa : CodecFromBytes ca) (hFBb : CodecFromBytes cb) :
    CodecFromBytes (pairPaddedCodec ca padLen cb) := by
  intro bs hLen hInit
  dsimp only [pairPaddedCodec] at hLen
  have hTakeLen : (bs.take ca.byteSize).length = ca.byteSize := by
    apply listLength_take_of_le ca.byteSize bs
    rw [hLen, Nat.add_assoc]
    exact Nat.le_add_right ca.byteSize (padLen + cb.byteSize)
  have hDropLen : (bs.drop (ca.byteSize + padLen)).length = cb.byteSize := by
    rw [listLength_drop, hLen, Nat.add_sub_cancel_left]
  cases hFBa (bs.take ca.byteSize) hTakeLen
      (allBytesInit_take ca.byteSize hInit) with
  | intro a ha =>
    cases hFBb (bs.drop (ca.byteSize + padLen)) hDropLen
        (allBytesInit_drop (ca.byteSize + padLen) hInit) with
    | intro b hb =>
      refine ⟨(a, b), ?_⟩
      dsimp only [pairPaddedCodec]
      rw [hLen, natBeq_refl_tr (ca.byteSize + padLen + cb.byteSize), ha, hb]
      rfl

/-- `CodecNoProv` is preserved by `pairPaddedCodec` for any `padLen` (`[]` zero
axioms). -/
theorem codecNoProv_pairPadded {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B} (padLen : Nat)
    (hNPa : CodecNoProv ca) (hNPb : CodecNoProv cb) :
    CodecNoProv (pairPaddedCodec ca padLen cb) := by
  intro p
  dsimp only [pairPaddedCodec]
  rw [allBytesNoProv_append, allBytesNoProv_append, hNPa p.1,
    allBytesNoProv_replicate_uninit padLen, hNPb p.2]
  rfl

/-- Padding-free (`padLen = 0`) product preserves `CodecIntoBytes` (`[propext]`
only). -/
theorem codecIntoBytes_pairPadded_zero {A B : Type}
    {ca : ByteCodec A} {cb : ByteCodec B}
    (hIBa : CodecIntoBytes ca) (hIBb : CodecIntoBytes cb) :
    CodecIntoBytes (pairPaddedCodec ca 0 cb) := by
  refine ⟨?_, ?_⟩
  · intro p
    dsimp only [pairPaddedCodec, List.replicate]
    rw [List.append_nil, List.length_append, hIBa.encodeLen p.1,
      hIBb.encodeLen p.2, Nat.add_zero]
  · intro p
    dsimp only [pairPaddedCodec, List.replicate]
    rw [List.append_nil, allBytesInit_append, hIBa.noUninit p.1,
      hIBb.noUninit p.2]
    rfl

/-- Any positive padding (`padLen + 1`) on an inhabited pair refutes
`CodecIntoBytes` (`[]` zero axioms). -/
theorem not_codecIntoBytes_pairPadded_succ {A B : Type}
    (ca : ByteCodec A) (padLen : Nat) (cb : ByteCodec B) (p₀ : A × B) :
    ¬ CodecIntoBytes (pairPaddedCodec ca (padLen + 1) cb) := by
  intro hIB
  have hAll := hIB.noUninit p₀
  dsimp only [pairPaddedCodec, List.replicate] at hAll
  rw [allBytesInit_append, allBytesInit_append] at hAll
  change (allBytesInit (ca.encode p₀.1) &&
    (false && allBytesInit (List.replicate padLen .uninit)) &&
    allBytesInit (cb.encode p₀.2)) = true at hAll
  rw [Bool.false_and, Bool.and_false, Bool.false_and] at hAll
  exact Bool.noConfusion hAll

/-! ## Part IV: `MemoryState` Zero-Copy Write/Read Transmute Bridge -/

private theorem listDrop_take_prefix :
    ∀ (off : Nat) (xs rest : List AllocByte),
      off ≤ xs.length →
      (xs.take off ++ rest).drop off = rest
  | 0, _, _, _ => rfl
  | _ + 1, [], _, hLe => nomatch hLe
  | off + 1, _ :: xs, rest, hLe =>
    listDrop_take_prefix off xs rest (Nat.le_of_succ_le_succ hLe)

private theorem listDropTake_splice (xs mid : List AllocByte) (off : Nat)
    (hInBounds : off + mid.length ≤ xs.length) :
    (((xs.take off ++ mid) ++ xs.drop (off + mid.length)).drop off).take
        mid.length = mid := by
  have hOffLe : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off mid.length) hInBounds
  rw [List.append_assoc,
    listDrop_take_prefix off xs (mid ++ xs.drop (off + mid.length)) hOffLe,
    listTake_append_exact mid (xs.drop (off + mid.length))]

/-- Computable typed write of `c.encode v` at `place` via `execWriteBytes`. -/
@[expose] def execWriteEncode {V : Type} (c : ByteCodec V) (m : MemoryState)
    (place : MemPlace) (alignLog2 : Nat) (v : V) :
    Except FaultKind MemoryState :=
  execWriteBytes m place alignLog2 (c.encode v)

/-- Computable typed read and decode of `c.byteSize` bytes at `place` via
`execReadBytes`. -/
@[expose] def execReadDecode {V : Type} (c : ByteCodec V) (m : MemoryState)
    (place : MemPlace) (alignLog2 : Nat) :
    Except FaultKind (Option V) :=
  match execReadBytes m place c.byteSize alignLog2 with
  | .error fk => .error fk
  | .ok bs => .ok (c.decode bs)

/-- Zero-copy `MemoryState` view law (`[propext]` only): for any positive byte
size (`Nat.beq ca.byteSize 0 = false`), writing `ca.encode a` onto a live,
mutable, in-bounds trailing allocation `alloc` (aligned to `alignWrite`) and
reading `cb.byteSize` (`= ca.byteSize`) bytes at any `alignRead` satisfied by
`place` produces `.ok (codecTransmute ca cb a)`. -/
theorem execReadDecode_after_execWriteEncode_eq_transmute {A B : Type}
    (ca : ByteCodec A) (cb : ByteCodec B) (m : MemoryState)
    (alloc : Allocation) (offset alignWrite alignRead : Nat) (a : A)
    (hEncLen : (ca.encode a).length = ca.byteSize)
    (hSizeEq : cb.byteSize = ca.byteSize)
    (hPos : Nat.beq ca.byteSize 0 = false)
    (hFresh : memAllocIdsLt m.allocations alloc.allocId = true)
    (hLive : alloc.live = true)
    (hMut : alloc.mutability = .mut)
    (hBounds : execIsInBounds alloc offset ca.byteSize = true)
    (hAlignW : execIsAligned alloc offset alignWrite = true)
    (hAlignR : execIsAligned alloc offset alignRead = true) :
    let m₀ : MemoryState :=
      { m with allocations := m.allocations ++ [alloc] }
    let place : MemPlace := ⟨alloc.allocId, offset⟩
    (match execWriteEncode ca m₀ place alignWrite a with
     | .error fk => Except.error fk
     | .ok m₁ => execReadDecode cb m₁ place alignRead) =
      Except.ok (codecTransmute ca cb a) := by
  dsimp only [execWriteEncode, execReadDecode, codecTransmute]
  have hFind₀ :
      execFindAllocation alloc.allocId (m.allocations ++ [alloc]) =
        some alloc :=
    execFindAllocation_append_lt m.allocations alloc hFresh
  let bytes' : List AllocByte :=
    (alloc.bytes.take offset ++ ca.encode a) ++
      alloc.bytes.drop (offset + (ca.encode a).length)
  let alloc' : Allocation :=
    { alloc with mutability := .mut, bytes := bytes', live := true }
  have hRep :
      execReplaceAllocation alloc' (m.allocations ++ [alloc]) =
        m.allocations ++ [alloc'] :=
    execReplaceAllocation_append_lt m.allocations alloc alloc' hFresh rfl
  have hFind₁ :
      execFindAllocation alloc.allocId (m.allocations ++ [alloc']) =
        some alloc' :=
    execFindAllocation_append_lt m.allocations alloc' hFresh
  have hLeBounds : offset + ca.byteSize ≤ alloc.bytes.length :=
    natLe_of_ble_tr hBounds
  have hBytesLenEq : bytes'.length = alloc.bytes.length := by
    dsimp only [bytes']
    rw [List.length_append, List.length_append, hEncLen,
      listLength_take_of_le offset alloc.bytes
        (Nat.le_trans (Nat.le_add_right offset ca.byteSize) hLeBounds),
      listLength_drop, Nat.add_sub_of_le hLeBounds]
  have hBounds' : execIsInBounds alloc' offset ca.byteSize = true := by
    dsimp only [execIsInBounds, alloc']
    rw [hBytesLenEq]
    exact hBounds
  have hAlignR' : execIsAligned alloc' offset alignRead = true := by
    dsimp only [execIsAligned, alloc']
    exact hAlignR
  unfold execWriteBytes
  rw [hEncLen, hPos]
  rw [hFind₀]
  dsimp only
  rw [hLive, hBounds, hAlignW, hMut]
  change
    (match execReadBytes
        { m with
          allocations :=
            execReplaceAllocation
              { alloc with
                mutability := .mut
                bytes :=
                  (alloc.bytes.take offset ++ ca.encode a) ++
                    alloc.bytes.drop (offset + ca.byteSize)
                live := true }
              (m.allocations ++ [alloc]) }
        ⟨alloc.allocId, offset⟩ cb.byteSize alignRead with
     | .error fk => Except.error fk
     | .ok bs => Except.ok (cb.decode bs)) =
      Except.ok (cb.decode (ca.encode a))
  have hBytes'Def :
      (alloc.bytes.take offset ++ ca.encode a) ++
        alloc.bytes.drop (offset + ca.byteSize) = bytes' := by
    dsimp only [bytes']
    rw [hEncLen]
  rw [hBytes'Def, hRep, hSizeEq]
  unfold execReadBytes
  rw [hPos]
  rw [hFind₁]
  dsimp only
  have hLive' : alloc'.live = true := rfl
  rw [hLive', hBounds', hAlignR']
  have hSplice :
      ((alloc'.bytes.drop offset).take ca.byteSize) = ca.encode a := by
    dsimp only [alloc', bytes']
    rw [← hEncLen]
    apply listDropTake_splice alloc.bytes (ca.encode a) offset
    rw [hEncLen]
    exact hLeBounds
  rw [hSplice]
  rfl

end Anneal.GaloisCodec

end
