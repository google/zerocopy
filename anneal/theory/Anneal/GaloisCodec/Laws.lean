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
public import Trusted.MirAst
public import Trusted.MirModel

public section

/-!
# Byte-Representation Galois Laws (`Anneal.GaloisCodec.Laws`)

Proof-free `ByteCodec` data carrier and separate `Prop`-valued
`GaloisLayoutCodec` laws over `Trusted.MirSemantics.AllocByte`
(`List AllocByte`):

1. **MiniRust-Aligned Definedness Partial Orders (`OptProvLe`, `AllocByteLe`,
   `AllocBytesLe`, `OptValLe`):**
   3-level provenance-aware byte definedness order (`.uninit ≤ y` always;
   `.init b₁ p₁ ≤ .init b₂ p₂ ↔ b₁ = b₂ ∧ OptProvLe p₁ p₂` where `none ≤ p` and
   `some id₁ ≤ some id₂ ↔ id₁ = id₂`) matching `Trusted.MirSemantics`'s
   provenance-stripping scalar decoders (`initBytes?`) while keeping distinct
   provenances incomparable, lifted pointwise via `List.foldr` (`0`
   `._unsafe_rec`) to equal-length `List AllocByte` slices, paired with
   computable boolean checkers (`optProvLeBool`, `allocByteLeBool`,
   `allocBytesLeBool`) and full reflexivity, transitivity, and antisymmetry
   proofs.
2. **Data/Proof Split (`ByteCodec` vs. `GaloisLayoutCodec`):**
   `ByteCodec V : Type` stores only `byteSize`, `encode`, and `decode` (zero
   embedded proof fields, avoiding proof-tuple WHNF bloat), while
   `GaloisLayoutCodec c : Prop` bundles fixed-size discipline (`encodeLen`,
   `decodeLen`) with the three representation laws `CodecDecodeMono`,
   `CodecDecodeEncode`, and `CodecEncodeLeast`.
3. **Lower-Adjoint Equivalence, Pointwise Uniqueness, & Padding Laws:**
   - `galoisLayoutCodec_iff_lowerAdjoint`: `GaloisLayoutCodec c ↔
     LowerAdjointCodec c` (`encode v ≤ bs ↔ decode bs = some v` on
     length-`byteSize` byte slices).
   - `encode_unique_of_decodeEncode_encodeLeast`: `CodecDecodeEncode` and
     `CodecEncodeLeast` uniquely pin `encode v` pointwise (`0` `funext` /
     `0` `Quot.sound`).
   - `decode_unique_of_galoisLayoutCodec`: `GaloisLayoutCodec` uniquely pins
     `decode bs` pointwise across all byte slices.
   - `padding_uninit_of_decodeIgnores` & `decodeIgnores_of_encode_uninit`:
     under `GaloisLayoutCodec`, byte positions ignored by `decode` are
     characterized as the positions that every `encode v` leaves `.uninit`.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration in
this module compiles with zero axioms (`[]`; Lean's auto-generated
`ByteCodec.mk.injEq` uses `[propext]`).
-/

namespace Anneal.GaloisCodec

open Trusted.MirAst Trusted.MirSemantics

/-! ## Part I: `Option AllocId` & `UInt8` Equality Helpers -/

private theorem natBeq_refl : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | n + 1 => natBeq_refl n

private theorem natEq_of_beq : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq h)

private theorem uint8Eq_of_toNat_eq {x y : UInt8} (h : x.toNat = y.toNat) :
    x = y := by
  cases x with
  | ofBitVec bvx =>
    cases y with
    | ofBitVec bvy =>
      cases bvx with
      | ofFin fx =>
        cases bvy with
        | ofFin fy =>
          cases fx with
          | mk vx _ =>
            cases fy with
            | mk vy _ =>
              dsimp only [UInt8.toNat, BitVec.toNat] at h
              subst h
              rfl

/-- Definedness partial order on optional provenance tags (`Option AllocId`):
`none ≤ p` always (provenance-free scalar bytes refine into provenance-carrying
bytes), and `some id₁ ≤ some id₂ ↔ id₁ = id₂`. -/
@[expose] def OptProvLe (p₁ p₂ : Option AllocId) : Prop :=
  match p₁ with
  | none => True
  | some id₁ =>
    match p₂ with
    | none => False
    | some id₂ => id₁ = id₂

/-- Computable boolean decision procedure for `OptProvLe`. -/
@[expose] def optProvLeBool (p₁ p₂ : Option AllocId) : Bool :=
  match p₁ with
  | none => true
  | some id₁ =>
    match p₂ with
    | none => false
    | some id₂ => Nat.beq id₁ id₂

/-- Boolean reflection equivalence
`optProvLeBool p₁ p₂ = true ↔ OptProvLe p₁ p₂`. -/
theorem optProvLeBool_iff (p₁ p₂ : Option AllocId) :
    optProvLeBool p₁ p₂ = true ↔ OptProvLe p₁ p₂ := by
  cases p₁ with
  | none => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | some id₁ =>
    cases p₂ with
    | none => exact ⟨fun h => Bool.noConfusion h, fun h => False.elim h⟩
    | some id₂ =>
      dsimp only [optProvLeBool, OptProvLe]
      refine ⟨fun h => natEq_of_beq h, fun h => ?_⟩
      rw [h]
      exact natBeq_refl id₂

/-- Reflexivity of `OptProvLe`. -/
theorem optProvLe_refl (p : Option AllocId) : OptProvLe p p := by
  cases p with
  | none => exact True.intro
  | some _ => rfl

/-- Transitivity of `OptProvLe`. -/
theorem optProvLe_trans {p₁ p₂ p₃ : Option AllocId}
    (h₁₂ : OptProvLe p₁ p₂) (h₂₃ : OptProvLe p₂ p₃) : OptProvLe p₁ p₃ := by
  cases p₁ with
  | none => exact True.intro
  | some _ =>
    cases p₂ with
    | none => exact False.elim h₁₂
    | some _ =>
      cases p₃ with
      | none => exact False.elim h₂₃
      | some _ => exact Eq.trans h₁₂ h₂₃

/-- Antisymmetry of `OptProvLe`. -/
theorem optProvLe_antisymm {p₁ p₂ : Option AllocId}
    (h₁₂ : OptProvLe p₁ p₂) (h₂₁ : OptProvLe p₂ p₁) : p₁ = p₂ := by
  cases p₁ with
  | none =>
    cases p₂ with
    | none => rfl
    | some _ => exact False.elim h₂₁
  | some _ =>
    cases p₂ with
    | none => exact False.elim h₁₂
    | some _ => exact congrArg some h₁₂

/-! ## Part II: `AllocByte` & `List AllocByte` Definedness Partial Orders -/

/-- MiniRust-aligned definedness partial order on `AllocByte`: `.uninit` is
refined by any byte, `.init b none` is refined by `.init b p` for any `p`, and
`.init b (some id)` is refined only by `.init b (some id)`. -/
@[expose] def AllocByteLe (x y : AllocByte) : Prop :=
  match x with
  | .uninit => True
  | .init b₁ p₁ =>
    match y with
    | .uninit => False
    | .init b₂ p₂ => b₁ = b₂ ∧ OptProvLe p₁ p₂

/-- Computable boolean decision procedure for `AllocByteLe`. -/
@[expose] def allocByteLeBool (x y : AllocByte) : Bool :=
  match x with
  | .uninit => true
  | .init b₁ p₁ =>
    match y with
    | .uninit => false
    | .init b₂ p₂ => Nat.beq b₁.toNat b₂.toNat && optProvLeBool p₁ p₂

/-- Boolean reflection equivalence
`allocByteLeBool x y = true ↔ AllocByteLe x y`. -/
theorem allocByteLeBool_iff (x y : AllocByte) :
    allocByteLeBool x y = true ↔ AllocByteLe x y := by
  cases x with
  | uninit =>
    exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | init b₁ p₁ =>
    cases y with
    | uninit =>
      exact ⟨fun h => Bool.noConfusion h, fun h => False.elim h⟩
    | init b₂ p₂ =>
      dsimp only [allocByteLeBool, AllocByteLe]
      refine ⟨?_, ?_⟩
      · intro h
        cases hB : Nat.beq b₁.toNat b₂.toNat with
        | false =>
          rw [hB] at h
          exact Bool.noConfusion h
        | true =>
          rw [hB] at h
          exact ⟨uint8Eq_of_toNat_eq (natEq_of_beq hB),
            (optProvLeBool_iff p₁ p₂).mp h⟩
      · intro h
        rw [h.1, natBeq_refl b₂.toNat, (optProvLeBool_iff p₁ p₂).mpr h.2]
        rfl

/-- Reflexivity of `AllocByteLe`. -/
theorem allocByteLe_refl (x : AllocByte) : AllocByteLe x x := by
  cases x with
  | uninit => exact True.intro
  | init _ p => exact ⟨rfl, optProvLe_refl p⟩

/-- Transitivity of `AllocByteLe`. -/
theorem allocByteLe_trans {x y z : AllocByte}
    (hxy : AllocByteLe x y) (hyz : AllocByteLe y z) : AllocByteLe x z := by
  cases x with
  | uninit => exact True.intro
  | init _ _ =>
    cases y with
    | uninit => exact False.elim hxy
    | init _ _ =>
      cases z with
      | uninit => exact False.elim hyz
      | init _ _ =>
        exact ⟨Eq.trans hxy.1 hyz.1, optProvLe_trans hxy.2 hyz.2⟩

/-- Antisymmetry of `AllocByteLe`. -/
theorem allocByteLe_antisymm {x y : AllocByte}
    (hxy : AllocByteLe x y) (hyx : AllocByteLe y x) : x = y := by
  cases x with
  | uninit =>
    cases y with
    | uninit => rfl
    | init _ _ => exact False.elim hyx
  | init _ _ =>
    cases y with
    | uninit => exact False.elim hxy
    | init _ _ =>
      rw [hxy.1, optProvLe_antisymm hxy.2 hyx.2]

/-- Pointwise equal-length definedness partial order on `List AllocByte`,
defined via `List.foldr` so zero `._unsafe_rec` constants are emitted. -/
@[expose] def AllocBytesLe (xs ys : List AllocByte) : Prop :=
  List.foldr
    (fun x ih ys' =>
      match ys' with
      | [] => False
      | y :: yt => AllocByteLe x y ∧ ih yt)
    (fun ys' =>
      match ys' with
      | [] => True
      | _ :: _ => False)
    xs ys

/-- Computable boolean decision procedure for `AllocBytesLe` (`0`
`._unsafe_rec`). -/
@[expose] def allocBytesLeBool (xs ys : List AllocByte) : Bool :=
  List.foldr
    (fun x ih ys' =>
      match ys' with
      | [] => false
      | y :: yt => allocByteLeBool x y && ih yt)
    (fun ys' =>
      match ys' with
      | [] => true
      | _ :: _ => false)
    xs ys

/-- Boolean reflection equivalence `allocBytesLeBool xs ys = true ↔
AllocBytesLe xs ys`. -/
theorem allocBytesLeBool_iff :
    ∀ (xs ys : List AllocByte),
      allocBytesLeBool xs ys = true ↔ AllocBytesLe xs ys
  | [], [] => ⟨fun _ => True.intro, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => Bool.noConfusion h, fun h => False.elim h⟩
  | _ :: _, [] => ⟨fun h => Bool.noConfusion h, fun h => False.elim h⟩
  | x :: xs, y :: ys => by
    change (allocByteLeBool x y && allocBytesLeBool xs ys) = true ↔
      (AllocByteLe x y ∧ AllocBytesLe xs ys)
    refine ⟨?_, ?_⟩
    · intro h
      cases hHead : allocByteLeBool x y with
      | false =>
        rw [hHead] at h
        exact Bool.noConfusion h
      | true =>
        rw [hHead] at h
        exact ⟨(allocByteLeBool_iff x y).mp hHead,
          (allocBytesLeBool_iff xs ys).mp h⟩
    · intro h
      have hHead : allocByteLeBool x y = true :=
        (allocByteLeBool_iff x y).mpr h.1
      have hTail : allocBytesLeBool xs ys = true :=
        (allocBytesLeBool_iff xs ys).mpr h.2
      rw [hHead, hTail]
      rfl

/-- `AllocBytesLe xs ys` implies `xs.length = ys.length`. -/
theorem allocBytesLe_length_eq :
    ∀ {xs ys : List AllocByte}, AllocBytesLe xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, _ :: _, h => congrArg Nat.succ (allocBytesLe_length_eq h.2)

/-- Reflexivity of `AllocBytesLe`. -/
theorem allocBytesLe_refl : ∀ (xs : List AllocByte), AllocBytesLe xs xs
  | [] => True.intro
  | x :: xs => ⟨allocByteLe_refl x, allocBytesLe_refl xs⟩

/-- Transitivity of `AllocBytesLe`. -/
theorem allocBytesLe_trans :
    ∀ {xs ys zs : List AllocByte},
      AllocBytesLe xs ys → AllocBytesLe ys zs → AllocBytesLe xs zs
  | [], [], [], _, _ => True.intro
  | [], [], _ :: _, _, hyz => False.elim hyz
  | [], _ :: _, _, hxy, _ => False.elim hxy
  | _ :: _, [], _, hxy, _ => False.elim hxy
  | _ :: _, _ :: _, [], _, hyz => False.elim hyz
  | _ :: _, _ :: _, _ :: _, hxy, hyz =>
    ⟨allocByteLe_trans hxy.1 hyz.1, allocBytesLe_trans hxy.2 hyz.2⟩

/-- Antisymmetry of `AllocBytesLe`. -/
theorem allocBytesLe_antisymm :
    ∀ {xs ys : List AllocByte},
      AllocBytesLe xs ys → AllocBytesLe ys xs → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hxy, _ => False.elim hxy
  | _ :: _, [], hxy, _ => False.elim hxy
  | _ :: _, _ :: _, hxy, hyx => by
    rw [allocByteLe_antisymm hxy.1 hyx.1, allocBytesLe_antisymm hxy.2 hyx.2]

/-- Appending two `AllocBytesLe` byte slices preserves `AllocBytesLe`. -/
theorem allocBytesLe_append :
    ∀ {xs₁ ys₁ xs₂ ys₂ : List AllocByte},
      AllocBytesLe xs₁ ys₁ → AllocBytesLe xs₂ ys₂ →
      AllocBytesLe (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  | [], [], _, _, _, h₂ => h₂
  | [], _ :: _, _, _, h₁, _ => False.elim h₁
  | _ :: _, [], _, _, h₁, _ => False.elim h₁
  | _ :: _, _ :: _, _, _, h₁, h₂ =>
    ⟨h₁.1, allocBytesLe_append h₁.2 h₂⟩

/-- Every length-`n` slice of `.uninit` bytes refines into any length-`n` byte
slice. -/
theorem allocBytesLe_uninit_replicate :
    ∀ (bs : List AllocByte),
      AllocBytesLe (List.replicate bs.length .uninit) bs
  | [] => True.intro
  | _ :: bs => ⟨True.intro, allocBytesLe_uninit_replicate bs⟩

/-! ## Part III: Flat `Option V` Order & Proof-Free `ByteCodec` Carrier -/

/-- Flat definedness partial order on decoded values `Option V`: `none` is below
everything, and `some v ≤ some w ↔ v = w`. -/
@[expose] def OptValLe {V : Type} (o₁ o₂ : Option V) : Prop :=
  match o₁ with
  | none => True
  | some v₁ =>
    match o₂ with
    | none => False
    | some v₂ => v₁ = v₂

/-- Reflexivity of `OptValLe`. -/
theorem optValLe_refl {V : Type} (o : Option V) : OptValLe o o := by
  cases o with
  | none => exact True.intro
  | some _ => rfl

/-- Transitivity of `OptValLe`. -/
theorem optValLe_trans {V : Type} {o₁ o₂ o₃ : Option V}
    (h₁₂ : OptValLe o₁ o₂) (h₂₃ : OptValLe o₂ o₃) : OptValLe o₁ o₃ := by
  cases o₁ with
  | none => exact True.intro
  | some _ =>
    cases o₂ with
    | none => exact False.elim h₁₂
    | some _ =>
      cases o₃ with
      | none => exact False.elim h₂₃
      | some _ => exact Eq.trans h₁₂ h₂₃

/-- Antisymmetry of `OptValLe`. -/
theorem optValLe_antisymm {V : Type} {o₁ o₂ : Option V}
    (h₁₂ : OptValLe o₁ o₂) (h₂₁ : OptValLe o₂ o₁) : o₁ = o₂ := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some _ => exact False.elim h₂₁
  | some _ =>
    cases o₂ with
    | none => exact False.elim h₁₂
    | some _ => exact congrArg some h₁₂

/-- Proof-free byte representation codec for `V`: carries only `byteSize`,
`encode`, and `decode` without embedded proof terms so codec combinators reduce
in WHNF without proof-tuple blowup. -/
structure ByteCodec (V : Type) where
  byteSize : Nat
  encode : V → List AllocByte
  decode : List AllocByte → Option V

/-- Every `encode v` has exact byte length `c.byteSize`. -/
@[expose] def CodecEncodeLen {V : Type} (c : ByteCodec V) : Prop :=
  ∀ v : V, (c.encode v).length = c.byteSize

/-- Every successfully decoded byte slice has exact length `c.byteSize`. -/
@[expose] def CodecDecodeLen {V : Type} (c : ByteCodec V) : Prop :=
  ∀ (bs : List AllocByte) (v : V),
    c.decode bs = some v → bs.length = c.byteSize

/-- Monotone decoding: initializing `.uninit` bytes never changes a successful
decode into `none` or a different value. -/
@[expose] def CodecDecodeMono {V : Type} (c : ByteCodec V) : Prop :=
  ∀ (xs ys : List AllocByte),
    AllocBytesLe xs ys → OptValLe (c.decode xs) (c.decode ys)

/-- Round-trip decoding of canonical encodings: `decode (encode v) = some v`. -/
@[expose] def CodecDecodeEncode {V : Type} (c : ByteCodec V) : Prop :=
  ∀ v : V, c.decode (c.encode v) = some v

/-- Least-definedness of canonical encodings: `encode v` leaves every byte not
required by `decode bs = some v` as `.uninit`. -/
@[expose] def CodecEncodeLeast {V : Type} (c : ByteCodec V) : Prop :=
  ∀ (bs : List AllocByte) (v : V),
    c.decode bs = some v → AllocBytesLe (c.encode v) bs

/-- Separate `Prop`-valued Galois byte-layout contract for a `ByteCodec V`. -/
structure GaloisLayoutCodec {V : Type} (c : ByteCodec V) : Prop where
  encodeLen : CodecEncodeLen c
  decodeLen : CodecDecodeLen c
  decodeMono : CodecDecodeMono c
  decodeEncode : CodecDecodeEncode c
  encodeLeast : CodecEncodeLeast c

/-- Lower-adjoint characterization of `c`: fixed-size discipline plus
`AllocBytesLe (c.encode v) bs ↔ c.decode bs = some v` for all `v` and `bs`. -/
structure LowerAdjointCodec {V : Type} (c : ByteCodec V) : Prop where
  encodeLen : CodecEncodeLen c
  decodeLen : CodecDecodeLen c
  adjoint : ∀ (v : V) (bs : List AllocByte),
    AllocBytesLe (c.encode v) bs ↔ c.decode bs = some v

/-! ## Part IV: Galois Lower-Adjoint Equivalence & Uniqueness Theorems -/

/-- Exact equivalence (`[]` zero axioms): `GaloisLayoutCodec c` holds iff
`c.encode` is a lower adjoint of `c.decode` (`LowerAdjointCodec c`). -/
theorem galoisLayoutCodec_iff_lowerAdjoint {V : Type} (c : ByteCodec V) :
    GaloisLayoutCodec c ↔ LowerAdjointCodec c := by
  refine ⟨?_, ?_⟩
  · intro hG
    refine ⟨hG.encodeLen, hG.decodeLen, fun v bs => ⟨?_, ?_⟩⟩
    · intro hLe
      have hMono := hG.decodeMono (c.encode v) bs hLe
      rw [hG.decodeEncode v] at hMono
      cases hDec : c.decode bs with
      | none =>
        rw [hDec] at hMono
        exact False.elim hMono
      | some _ =>
        rw [hDec] at hMono
        exact congrArg some hMono.symm
    · intro hDec
      exact hG.encodeLeast bs v hDec
  · intro hLA
    refine ⟨hLA.encodeLen, hLA.decodeLen, ?_, ?_, ?_⟩
    · intro xs ys hxy
      cases hx : c.decode xs with
      | none => exact True.intro
      | some v =>
        have hEncX : AllocBytesLe (c.encode v) xs :=
          (hLA.adjoint v xs).mpr hx
        have hEncY : AllocBytesLe (c.encode v) ys :=
          allocBytesLe_trans hEncX hxy
        have hy : c.decode ys = some v :=
          (hLA.adjoint v ys).mp hEncY
        rw [hy]
        rfl
    · intro v
      exact (hLA.adjoint v (c.encode v)).mp (allocBytesLe_refl (c.encode v))
    · intro bs v hDec
      exact (hLA.adjoint v bs).mpr hDec

/-- Pointwise encoder uniqueness (`[]` zero axioms, `0` `funext`):
`CodecDecodeEncode` and `CodecEncodeLeast` uniquely determine `encode v` from
`decode` (`CodecDecodeMono` is not required). -/
theorem encode_unique_of_decodeEncode_encodeLeast {V : Type}
    (c₁ c₂ : ByteCodec V) (hSameDec : ∀ bs, c₁.decode bs = c₂.decode bs)
    (hDE₁ : CodecDecodeEncode c₁) (hEL₁ : CodecEncodeLeast c₁)
    (hDE₂ : CodecDecodeEncode c₂) (hEL₂ : CodecEncodeLeast c₂) (v : V) :
    c₁.encode v = c₂.encode v := by
  have hDec₁On₂ : c₁.decode (c₂.encode v) = some v := by
    rw [hSameDec (c₂.encode v)]
    exact hDE₂ v
  have hDec₂On₁ : c₂.decode (c₁.encode v) = some v := by
    rw [← hSameDec (c₁.encode v)]
    exact hDE₁ v
  exact allocBytesLe_antisymm
    (hEL₁ (c₂.encode v) v hDec₁On₂)
    (hEL₂ (c₁.encode v) v hDec₂On₁)

/-- Pointwise decoder uniqueness (`[]` zero axioms): two `GaloisLayoutCodec`s
sharing the same `encode` agree on `decode bs` for every `bs`. -/
theorem decode_unique_of_galoisLayoutCodec {V : Type}
    (c₁ c₂ : ByteCodec V) (hSameEnc : ∀ v, c₁.encode v = c₂.encode v)
    (hG₁ : GaloisLayoutCodec c₁) (hG₂ : GaloisLayoutCodec c₂)
    (bs : List AllocByte) :
    c₁.decode bs = c₂.decode bs := by
  have hLA₁ := (galoisLayoutCodec_iff_lowerAdjoint c₁).mp hG₁
  have hLA₂ := (galoisLayoutCodec_iff_lowerAdjoint c₂).mp hG₂
  cases h₁ : c₁.decode bs with
  | some v =>
    have hLe₁ : AllocBytesLe (c₁.encode v) bs := (hLA₁.adjoint v bs).mpr h₁
    rw [hSameEnc v] at hLe₁
    exact ((hLA₂.adjoint v bs).mp hLe₁).symm
  | none =>
    cases h₂ : c₂.decode bs with
    | none => rfl
    | some w =>
      have hLe₂ : AllocBytesLe (c₂.encode w) bs := (hLA₂.adjoint w bs).mpr h₂
      rw [← hSameEnc w] at hLe₂
      have h₁' : c₁.decode bs = some w := (hLA₁.adjoint w bs).mp hLe₂
      rw [h₁] at h₁'
      nomatch h₁'

/-- Under `CodecDecodeMono` and `CodecDecodeEncode`, comparable encodings
belong to equal values (`[]` zero axioms). -/
theorem eq_of_encode_le_encode {V : Type} (c : ByteCodec V)
    (hMono : CodecDecodeMono c) (hDE : CodecDecodeEncode c) {v₁ v₂ : V}
    (hLe : AllocBytesLe (c.encode v₁) (c.encode v₂)) :
    v₁ = v₂ := by
  have hm := hMono (c.encode v₁) (c.encode v₂) hLe
  rw [hDE v₁, hDE v₂] at hm
  exact hm

/-! ## Part V: Indexed Byte Access & Padding-Byte Characterization -/

/-- Computable total indexed lookup on `List AllocByte` via `@Nat.rec` (`0`
`noncomputable`, `0` `._unsafe_rec`). -/
@[expose] def listGetByte? (bs : List AllocByte) (idx : Nat) :
    Option AllocByte :=
  @Nat.rec (fun _ => List AllocByte → Option AllocByte)
    (fun xs =>
      match xs with
      | [] => none
      | x :: _ => some x)
    (fun _ ih xs =>
      match xs with
      | [] => none
      | _ :: xt => ih xt)
    idx bs

/-- Computable total indexed byte update on `List AllocByte` via `@Nat.rec`
(`0` `._unsafe_rec`). -/
@[expose] def listSetByte (bs : List AllocByte) (idx : Nat) (b' : AllocByte) :
    List AllocByte :=
  @Nat.rec (fun _ => List AllocByte → List AllocByte)
    (fun xs =>
      match xs with
      | [] => []
      | _ :: xt => b' :: xt)
    (fun _ ih xs =>
      match xs with
      | [] => []
      | x :: xt => x :: ih xt)
    idx bs

private theorem listGetByte?_nil : ∀ k : Nat, listGetByte? [] k = none
  | 0 => rfl
  | _ + 1 => rfl

private theorem listSetByte_nil (b' : AllocByte) :
    ∀ k : Nat, listSetByte [] k b' = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem listGetByte?_lt :
    ∀ (bs : List AllocByte) {idx : Nat},
      idx < bs.length → ∃ b, listGetByte? bs idx = some b
  | [], _, hLt => nomatch hLt
  | b :: _, 0, _ => ⟨b, rfl⟩
  | _ :: bs, _ + 1, hLt => listGetByte?_lt bs (Nat.lt_of_succ_lt_succ hLt)

private theorem allocByteLe_getByte? :
    ∀ {xs ys : List AllocByte} {idx : Nat} {bx by_ : AllocByte},
      AllocBytesLe xs ys →
      listGetByte? xs idx = some bx →
      listGetByte? ys idx = some by_ →
      AllocByteLe bx by_
  | [], _, k, _, _, _, hx, _ => by
    rw [listGetByte?_nil k] at hx
    nomatch hx
  | _ :: _, [], _, _, _, hLe, _, _ => False.elim hLe
  | _ :: _, _ :: _, 0, _, _, hLe, hx, hy => by
    injection hx with hxEq
    injection hy with hyEq
    rw [← hxEq, ← hyEq]
    exact hLe.1
  | _ :: _, _ :: _, _ + 1, _, _, hLe, hx, hy =>
    allocByteLe_getByte? hLe.2 hx hy

private theorem listGetByte?_setByte_same :
    ∀ (bs : List AllocByte) {idx : Nat} (b' : AllocByte),
      idx < bs.length → listGetByte? (listSetByte bs idx b') idx = some b'
  | [], _, _, hLt => nomatch hLt
  | _ :: _, 0, _, _ => rfl
  | _ :: bs, _ + 1, b', hLt =>
    listGetByte?_setByte_same bs b' (Nat.lt_of_succ_lt_succ hLt)

private theorem allocBytesLe_setByte_of_get_uninit :
    ∀ (bs : List AllocByte) {idx : Nat} (b' : AllocByte),
      listGetByte? bs idx = some .uninit →
      AllocBytesLe bs (listSetByte bs idx b')
  | [], k, _, hGet => by
    rw [listGetByte?_nil k] at hGet
    nomatch hGet
  | _ :: xs, 0, _, hGet => by
    injection hGet with hx
    rw [hx]
    exact ⟨True.intro, allocBytesLe_refl xs⟩
  | x :: xs, _ + 1, b', hGet =>
    ⟨allocByteLe_refl x, allocBytesLe_setByte_of_get_uninit xs b' hGet⟩

private theorem allocBytesLe_of_setByte_uninit :
    ∀ (bs : List AllocByte) (idx : Nat),
      AllocBytesLe (listSetByte bs idx .uninit) bs
  | [], k => by
    rw [listSetByte_nil .uninit k]
    exact True.intro
  | _ :: xs, 0 => ⟨True.intro, allocBytesLe_refl xs⟩
  | x :: xs, idx + 1 =>
    ⟨allocByteLe_refl x, allocBytesLe_of_setByte_uninit xs idx⟩

private theorem listSetByte_mono_uninit :
    ∀ {as bs : List AllocByte} (k : Nat),
      AllocBytesLe as bs →
      AllocBytesLe (listSetByte as k .uninit) (listSetByte bs k .uninit)
  | [], [], k, _ => by
    rw [listSetByte_nil .uninit k]
    exact True.intro
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h
  | _ :: _, _ :: _, 0, h => ⟨True.intro, h.2⟩
  | _ :: _, _ :: _, k + 1, h => ⟨h.1, listSetByte_mono_uninit k h.2⟩

private theorem listSetByte_idem_uninit :
    ∀ (xs : List AllocByte) (idx : Nat) (b' : AllocByte),
      listSetByte (listSetByte xs idx b') idx .uninit =
        listSetByte xs idx .uninit
  | [], k, b' => by
    rw [listSetByte_nil b' k, listSetByte_nil .uninit k]
  | _ :: _, 0, _ => rfl
  | b :: xs, idx + 1, b' =>
    congrArg (List.cons b) (listSetByte_idem_uninit xs idx b')

/-- `c.decode` ignores byte position `idx` iff overwriting index `idx` with any
`AllocByte` never changes `c.decode bs`. -/
@[expose] def DecodeIgnoresAt {V : Type} (c : ByteCodec V) (idx : Nat) : Prop :=
  ∀ (bs : List AllocByte) (b' : AllocByte),
    c.decode (listSetByte bs idx b') = c.decode bs

/-- Padding-is-`.uninit` law (`[]` zero axioms): under `CodecEncodeLen`,
`CodecDecodeEncode`, and `CodecEncodeLeast`, any in-bounds byte position ignored
by `c.decode` is encoded as `.uninit` for every value `v`. -/
theorem padding_uninit_of_decodeIgnores {V : Type} (c : ByteCodec V)
    (hLen : CodecEncodeLen c) (hDE : CodecDecodeEncode c)
    (hEL : CodecEncodeLeast c) {idx : Nat} (hLt : idx < c.byteSize)
    (hIgn : DecodeIgnoresAt c idx) (v : V) :
    listGetByte? (c.encode v) idx = some .uninit := by
  have hEncLt : idx < (c.encode v).length := by
    rw [hLen v]
    exact hLt
  cases listGetByte?_lt (c.encode v) hEncLt with
  | intro b hb =>
    have hDecUninit :
        c.decode (listSetByte (c.encode v) idx .uninit) = some v := by
      rw [hIgn (c.encode v) .uninit]
      exact hDE v
    have hLe : AllocBytesLe (c.encode v)
        (listSetByte (c.encode v) idx .uninit) :=
      hEL (listSetByte (c.encode v) idx .uninit) v hDecUninit
    have hGetSet :
        listGetByte? (listSetByte (c.encode v) idx .uninit) idx =
          some .uninit :=
      listGetByte?_setByte_same (c.encode v) .uninit hEncLt
    have hByteLe : AllocByteLe b .uninit :=
      allocByteLe_getByte? hLe hb hGetSet
    cases b with
    | uninit => exact hb
    | init _ _ => exact False.elim hByteLe

/-- Converse padding law (`[]` zero axioms): under `GaloisLayoutCodec`,
any byte position that every `c.encode v` leaves `.uninit` is ignored by
`c.decode`. -/
theorem decodeIgnores_of_encode_uninit {V : Type} (c : ByteCodec V)
    (hG : GaloisLayoutCodec c) {idx : Nat}
    (hUninit : ∀ v : V, listGetByte? (c.encode v) idx = some .uninit) :
    DecodeIgnoresAt c idx := by
  have hLA := (galoisLayoutCodec_iff_lowerAdjoint c).mp hG
  intro bs b'
  have hSubToUninit :
      ∀ (xs : List AllocByte),
        c.decode xs = c.decode (listSetByte xs idx .uninit) := by
    intro xs
    cases hDecX : c.decode xs with
    | some v =>
      have hLe : AllocBytesLe (c.encode v) xs :=
        (hLA.adjoint v xs).mpr hDecX
      have hSetEnc :
          listSetByte (c.encode v) idx .uninit = c.encode v :=
        allocBytesLe_antisymm
          (allocBytesLe_of_setByte_uninit (c.encode v) idx)
          (allocBytesLe_setByte_of_get_uninit (c.encode v) .uninit (hUninit v))
      have hLeSet :
          AllocBytesLe (c.encode v) (listSetByte xs idx .uninit) := by
        rw [← hSetEnc]
        exact listSetByte_mono_uninit idx hLe
      exact ((hLA.adjoint v (listSetByte xs idx .uninit)).mp hLeSet).symm
    | none =>
      cases hDecU : c.decode (listSetByte xs idx .uninit) with
      | none => rfl
      | some w =>
        have hLeU : AllocBytesLe (c.encode w) (listSetByte xs idx .uninit) :=
          (hLA.adjoint w (listSetByte xs idx .uninit)).mpr hDecU
        have hLeX : AllocBytesLe (c.encode w) xs :=
          allocBytesLe_trans hLeU (allocBytesLe_of_setByte_uninit xs idx)
        have hX' : c.decode xs = some w := (hLA.adjoint w xs).mp hLeX
        rw [hDecX] at hX'
        nomatch hX'
  rw [hSubToUninit (listSetByte bs idx b'),
    listSetByte_idem_uninit bs idx b', ← hSubToUninit bs]

end Anneal.GaloisCodec

end
