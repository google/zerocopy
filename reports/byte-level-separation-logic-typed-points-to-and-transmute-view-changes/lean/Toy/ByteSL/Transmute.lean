import Toy.ByteSL.PointsTo

/-!
# Result group 3: transmute as a view change

For two representations `rA`, `rB` of the same size `n` (`transmute rA rB v = rB.decode
(rA.encode v)`), a *view change* is an entailment between typed points-to assertions over the
same bytes: the heap is unchanged, only the type through which it is viewed changes.

Results:

* `ptsEnc_entails_ptsDec_iff_transmute_eq_some` (R3a): the encode-based points-to of `v` at type
  `A` entails the decode-based points-to of `b` at type `B` exactly when `transmute rA rB v =
  some b`. No representation law is needed.
* `ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono` (R3b): if
  `A` satisfies `DecodeEncode` and `EncodeLeast` and `B` satisfies `DecodeMono`, the decode-based
  points-to of `v` at `A` entails the decode-based points-to of `b` at `B` exactly when
  `transmute rA rB v = some b`.
* `ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast` (R3c): if `A` is
  `IntoBytes` and satisfies `EncodeLeast`, then whenever `transmute rA rB v = some b`, the
  decode-based points-to of `v` at `A` entails that of `b` at `B`; nothing is assumed about `B`.
* `exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes` (R3f): if moreover `B` is
  `FromBytes`, then for every `v` such a `b` exists (it is the transmute result).
* `niche_viewChange_one_directional` (R3d, counterexample): `boolRep → u8Rep` is a view change for
  every value, but `u8Rep → boolRep` is not (the byte value `2` is a niche of `boolRep`).
* `padding_viewChange_one_directional` (R3e, counterexample): `pairRep → u8PadRep` is a view change
  for every value, but the reverse is not (the padding byte would be read as data).

A view change here is a heap entailment at one permission, one address and the same bytes. At
permission `full` it models a *consuming* reinterpretation (the `A` view is given up); it says
nothing about temporarily reborrowing a `&mut A` as `&mut B`, which must restore a valid `A`
afterwards, and alignment is not modeled.
-/

namespace Toy.ByteSL

open SepStruct

/-! ## R3a: encode-based source -/

/-- **R3a.** For representations `rA`, `rB` of equal size (no laws assumed), a value `v` of `A`
and a value `b` of `B`: the encode-based points-to of `v` at `A` entails the decode-based
points-to of `b` at `B` (at every permission, address and heap) exactly when
`transmute rA rB v = some b`. -/
theorem ptsEnc_entails_ptsDec_iff_transmute_eq_some {D A B : Type} {n : Nat}
    (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (v : A) (b : B) :
    (∀ (p : Perm) (a : Nat) (h : BHeap D), ptsEnc p rA a v h → ptsDec p rB a b h) ↔
      transmute rA rB v = some b := by
  refine ⟨fun H => ?_, fun ht _ _ _ hh => ⟨_, hh, ht⟩⟩
  obtain ⟨_, hx, hd⟩ := H .full 0 _ rfl
  dsimp [transmute]
  rw [Heap.block_inj hx]
  exact hd

/-- Non-vacuity for R3a: `transmute u8Rep boolRep 1 = some true`. -/
theorem ptsEnc_entails_ptsDec_iff_transmute_eq_some_nonvacuous :
    transmute u8Rep boolRep 1 = some true ∧
      ptsEnc .full u8Rep 0 1 (Heap.block .full 0 #v[.init 1]) :=
  ⟨rfl, rfl⟩

/-! ## R3b: decode-based source, under laws -/

/-- **R3b.** For representations `rA`, `rB` of equal size, if `A` satisfies `DecodeEncode` and
`EncodeLeast` and `B` satisfies `DecodeMono`, then for every `v` and `b`: the decode-based
points-to of `v` at `A` entails the decode-based points-to of `b` at `B` (at every permission,
address and heap) exactly when `transmute rA rB v = some b`. -/
theorem ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono
    {D A B : Type} {n : Nat}
    (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B)
    (hDE_A : rA.DecodeEncode) (hEL_A : rA.EncodeLeast) (hM_B : rB.DecodeMono) (v : A) (b : B) :
    (∀ (p : Perm) (a : Nat) (h : BHeap D), ptsDec p rA a v h → ptsDec p rB a b h) ↔
      transmute rA rB v = some b := by
  refine ⟨fun H => ?_, fun ht _ _ _ ⟨x, hx, hdA⟩ =>
    ⟨x, hx, OptLe.some_le_iff.mp (ht ▸ hM_B _ _ (hEL_A x v hdA))⟩⟩
  obtain ⟨_, hx, hd⟩ := H .full 0 _ ⟨_, rfl, hDE_A v⟩
  dsimp [transmute]
  rw [Heap.block_inj hx]
  exact hd

/-- Non-vacuity for R3b: `A` = two-byte integer, `B` = padded `u8` struct; all hypotheses hold
and `transmute pairRep u8PadRep (5, 7) = some 5`. -/
theorem ptsDec_entails_ptsDec_iff_transmute_eq_some_nonvacuous :
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).DecodeEncode ∧
      (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).EncodeLeast ∧ u8PadRep.DecodeMono ∧
      transmute pairRep u8PadRep ((5 : Byte), (7 : Byte)) = some 5 :=
  ⟨pairRep_decodeEncode, pairRep_encodeLeast, u8PadRep_decodeMono, rfl⟩

/-- Tightness of `hDE_A` in R3b: with `A` = the always-failing decoder over the `u8` encoder and
`B` = `u8`, `EncodeLeast A` and `DecodeMono B` hold; the left-hand side holds vacuously for
`v = 0, b = 1`, but `transmute` gives `some 0`, not `some 1`. -/
theorem ptsDec_entails_ptsDec_tight_hDE_A :
    (noneRep u8Rep.encode).EncodeLeast ∧ u8Rep.DecodeMono ∧
      ¬ ((∀ (p : Perm) (a : Nat) (h : BHeap Byte),
            ptsDec p (noneRep u8Rep.encode) a (0 : Byte) h → ptsDec p u8Rep a (1 : Byte) h) ↔
          transmute (noneRep u8Rep.encode) u8Rep (0 : Byte) = some (1 : Byte)) := by
  refine ⟨noneRep_encodeLeast _, u8Rep_decodeMono, fun H => ?_⟩
  have := H.mp fun _ _ _ ⟨_, _, hd⟩ => by cases hd
  cases this

/-- Tightness of `hEL_A` in R3b: `A` = `boolNZRep` (every nonzero byte decodes to `true`),
`B` = `boolRep`; `DecodeEncode A` and `DecodeMono B` hold and `transmute` sends `true` to
`some true`, but the block `[init 2]` satisfies the decode-based points-to of `true` at `A` and
not at `B`. -/
theorem ptsDec_entails_ptsDec_tight_hEL_A :
    boolNZRep.DecodeEncode ∧ boolRep.DecodeMono ∧
      ¬ ((∀ (p : Perm) (a : Nat) (h : BHeap Byte),
            ptsDec p boolNZRep a true h → ptsDec p boolRep a true h) ↔
          transmute boolNZRep boolRep true = some true) := by
  refine ⟨boolNZRep_decodeEncode, boolRep_decodeMono, fun H => ?_⟩
  obtain ⟨x, hx, hd⟩ := H.mpr rfl .full 0 (Heap.block .full 0 #v[.init 2]) ⟨_, rfl, rfl⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-- Tightness of `hM_B` in R3b: `A` = one byte of pure padding (`padUnitRep`), `B` =
`exactUnitRep` (only `[uninit]` decodes); `DecodeEncode A` and `EncodeLeast A` hold and
`transmute` sends `()` to `some ()`, but the block `[init 0]` satisfies the decode-based
points-to at `A` and not at `B`. -/
theorem ptsDec_entails_ptsDec_tight_hM_B :
    padUnitRep.DecodeEncode ∧ padUnitRep.EncodeLeast ∧
      ¬ ((∀ (p : Perm) (a : Nat) (h : BHeap Byte),
            ptsDec p padUnitRep a () h → ptsDec p exactUnitRep a () h) ↔
          transmute padUnitRep exactUnitRep () = some ()) := by
  refine ⟨padUnitRep_decodeEncode, padUnitRep_encodeLeast, fun H => ?_⟩
  obtain ⟨x, hx, hd⟩ := H.mpr rfl .full 0 (Heap.block .full 0 #v[.init 0]) ⟨_, rfl, rfl⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-! ## A `FromBytes` target that violates `DecodeMono` -/

/-- A one-byte `Bool` representation whose decoder is not monotone: `[uninit]` decodes to
`false`, every initialized byte decodes to `true`; `b` is encoded as `[init (boolEnc b)]`. It is
`FromBytes` but violates `DecodeMono` (and `DecodeEncode` at `false`); it serves as a view-change
target to show that no law is needed on the target. -/
def nonMonoBoolRep : Rep (Bytes Byte 1) Bool where
  encode b := #v[.init (boolEnc b)]
  decode x := match x[0] with
    | .uninit => some false
    | .init _ => some true

theorem nonMonoBoolRep_fromBytes : nonMonoBoolRep.FromBytes := by
  intro x hx
  have h0 := hx 0 (by decide)
  cases e : x[0] with
  | uninit => rw [e] at h0; cases h0
  | init d => exact ⟨true, by simp [nonMonoBoolRep, e]⟩

theorem nonMonoBoolRep_not_decodeMono : ¬ nonMonoBoolRep.DecodeMono := by
  intro h
  have hle : (#v[.uninit] : Bytes Byte 1) ⊑ #v[.init 0] := Bytes.le_one trivial
  have hdec := h #v[.uninit] #v[.init 0] hle
  exact absurd hdec (by decide)

/-! ## R3c: the view change from an `IntoBytes`, `EncodeLeast` source, any target -/

/-- `transmute` is total when `A` is `IntoBytes` and `B` is `FromBytes` (copied from the
published package, result R2a there, with its proof). -/
theorem transmuteTotal_of_intoBytes_of_fromBytes {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hA : ra.IntoBytes) (hB : rb.FromBytes) : TransmuteTotal ra rb := by
  intro a
  exact hB _ (hA a)

/-- **R3c.** For representations `rA`, `rB` of equal size: if `A` is `IntoBytes` (no encoding
contains `uninit`) and satisfies `EncodeLeast`, then for every `v` and every `b` with
`transmute rA rB v = some b`, the decode-based points-to of `v` at `A` entails the decode-based
points-to of `b` at `B` (at every permission, address and heap). Nothing is assumed about `B`:
none of `DecodeMono`, `DecodeEncode`, `EncodeLeast`, `FromBytes`. -/
theorem ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast
    {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B)
    (hIB_A : rA.IntoBytes) (hEL_A : rA.EncodeLeast) (v : A) (b : B)
    (ht : transmute rA rB v = some b) :
    ∀ (p : Perm) (a : Nat) (h : BHeap D), ptsDec p rA a v h → ptsDec p rB a b h := by
  rintro p a h ⟨x, hx, hdA⟩
  have hxeq : x = rA.encode v := Bytes.eq_of_le_of_isInit (hEL_A x v hdA) (hIB_A v)
  rw [hxeq] at hx
  exact ⟨rA.encode v, hx, ht⟩

/-- Non-vacuity for R3c: `u8Rep` is `IntoBytes` and `EncodeLeast`; the targets `nonMonoBoolRep`
(`FromBytes`, not `DecodeMono`) and `boolRep` (not `FromBytes`) both receive a successful
transmute of `1`, and the source points-to is inhabited. -/
theorem ptsDec_entails_ptsDec_of_transmute_eq_some_nonvacuous :
    u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧
      transmute u8Rep nonMonoBoolRep (1 : Byte) = some true ∧ ¬ nonMonoBoolRep.DecodeMono ∧
      transmute u8Rep boolRep (1 : Byte) = some true ∧ ¬ boolRep.FromBytes ∧
      ptsDec .full u8Rep 0 (1 : Byte) (Heap.block .full 0 #v[.init 1]) :=
  ⟨u8Rep_intoBytes, u8Rep_encodeLeast, rfl, nonMonoBoolRep_not_decodeMono, rfl,
    boolRep_not_fromBytes, ⟨_, rfl, rfl⟩⟩

/-- Tightness of `hIB_A` in R3c: `A` = one byte of pure padding (`padUnitRep`: `EncodeLeast`,
not `IntoBytes`), `B` = `nonMonoBoolRep`; `transmute` sends `()` to `some false`, but the block
`[init 0]` satisfies the decode-based points-to of `()` at `A` and not that of `false` at `B`. -/
theorem ptsDec_entails_ptsDec_of_transmute_tight_hIB_A :
    padUnitRep.EncodeLeast ∧ transmute padUnitRep nonMonoBoolRep () = some false ∧
      ¬ padUnitRep.IntoBytes ∧
      ¬ ∀ (p : Perm) (a : Nat) (h : BHeap Byte),
          ptsDec p padUnitRep a () h → ptsDec p nonMonoBoolRep a false h := by
  refine ⟨padUnitRep_encodeLeast, rfl, padUnitRep_not_intoBytes, fun H => ?_⟩
  obtain ⟨x, hx, hd⟩ := H .full 0 (Heap.block .full 0 #v[.init 0]) ⟨#v[.init 0], rfl, rfl⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-- Tightness of `hEL_A` in R3c: `A` = `boolNZRep` (`IntoBytes`, not `EncodeLeast`), `B` = `u8Rep`;
`transmute` sends `true` to `some 1`, but the block `[init 2]` satisfies the decode-based
points-to of `true` at `A` and not that of `1` at `B`. -/
theorem ptsDec_entails_ptsDec_of_transmute_tight_hEL_A :
    boolNZRep.IntoBytes ∧ transmute boolNZRep u8Rep true = some (1 : Byte) ∧
      ¬ boolNZRep.EncodeLeast ∧
      ¬ ∀ (p : Perm) (a : Nat) (h : BHeap Byte),
          ptsDec p boolNZRep a true h → ptsDec p u8Rep a (1 : Byte) h := by
  refine ⟨boolNZRep_intoBytes, rfl, boolNZRep_not_encodeLeast, fun H => ?_⟩
  obtain ⟨x, hx, hd⟩ := H .full 0 (Heap.block .full 0 #v[.init 2]) ⟨_, rfl, rfl⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-- Tightness of `ht` in R3c: with `A = B = u8Rep` (both `IntoBytes` and `EncodeLeast`), `v = 0`
and `b = 1` (so `transmute` does not return `some b`), the entailment fails at the block `[init 0]`. -/
theorem ptsDec_entails_ptsDec_of_transmute_tight_ht :
    u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧ transmute u8Rep u8Rep (0 : Byte) ≠ some (1 : Byte) ∧
      ¬ ∀ (p : Perm) (a : Nat) (h : BHeap Byte),
          ptsDec p u8Rep a (0 : Byte) h → ptsDec p u8Rep a (1 : Byte) h := by
  refine ⟨u8Rep_intoBytes, u8Rep_encodeLeast, by decide, fun H => ?_⟩
  obtain ⟨x, hx, hd⟩ := H .full 0 (Heap.block .full 0 #v[.init 0]) ⟨_, rfl, rfl⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-! ## R3f: the view change for every value, with a `FromBytes` target -/

/-- **R3f.** For representations `rA`, `rB` of equal size: if `A` is `IntoBytes` and satisfies
`EncodeLeast`, and `B` is `FromBytes` (every fully initialized byte vector decodes), then for every
`v` there is a `b` — namely the result of `transmute rA rB v` — such that the decode-based
points-to of `v` at `A` entails the decode-based points-to of `b` at `B` (at every permission,
address and heap). None of `DecodeMono`, `DecodeEncode`, `EncodeLeast` is assumed for `B`. -/
theorem exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes
    {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B)
    (hIB_A : rA.IntoBytes) (hEL_A : rA.EncodeLeast) (hFB_B : rB.FromBytes) :
    ∀ v : A, ∃ b : B, transmute rA rB v = some b ∧
      ∀ (p : Perm) (a : Nat) (h : BHeap D), ptsDec p rA a v h → ptsDec p rB a b h := by
  intro v
  obtain ⟨b, hb⟩ := transmuteTotal_of_intoBytes_of_fromBytes rA rB hIB_A hFB_B v
  exact ⟨b, hb, ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast
    rA rB hIB_A hEL_A v b hb⟩

/-- Non-vacuity for R3f: `pairRep` (two-byte integer) is `IntoBytes` and `EncodeLeast`, `u8PadRep`
is `FromBytes`, `transmute` sends `(5, 7)` to `some 5`, and the source points-to is inhabited; in
addition `u8Rep → nonMonoBoolRep` satisfies all hypotheses with a target violating `DecodeMono`. -/
theorem exists_ptsDec_viewChange_nonvacuous :
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).IntoBytes ∧
      (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).EncodeLeast ∧ u8PadRep.FromBytes ∧
      transmute pairRep u8PadRep ((5 : Byte), (7 : Byte)) = some 5 ∧
      ptsDec .full (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) 0 ((5 : Byte), (7 : Byte))
        (Heap.block .full 0 #v[.init 5, .init 7]) ∧
      (u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧ nonMonoBoolRep.FromBytes ∧
        ¬ nonMonoBoolRep.DecodeMono) :=
  ⟨pairRep_intoBytes, pairRep_encodeLeast, u8PadRep_fromBytes, rfl, ⟨_, rfl, rfl⟩,
    u8Rep_intoBytes, u8Rep_encodeLeast, nonMonoBoolRep_fromBytes, nonMonoBoolRep_not_decodeMono⟩

/-- Tightness of `hIB_A` in R3f ("padding read as data"): `A` = `u8PadRep` (`EncodeLeast`, not
`IntoBytes`), `B` = `pairRep` (`FromBytes`); `transmute` never succeeds (the encoding's padding
byte is `uninit`), so no `b` exists for `v = 0`. -/
theorem exists_ptsDec_viewChange_tight_hIB_A :
    u8PadRep.EncodeLeast ∧ (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).FromBytes ∧
      ¬ u8PadRep.IntoBytes ∧
      ¬ ∀ v : Byte, ∃ b : Byte × Byte, transmute u8PadRep pairRep v = some b ∧
          ∀ (p : Perm) (a : Nat) (h : BHeap Byte),
            ptsDec p u8PadRep a v h → ptsDec p (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) a b h := by
  refine ⟨u8PadRep_encodeLeast, pairRep_fromBytes, u8PadRep_not_intoBytes, fun H => ?_⟩
  obtain ⟨b, hb, _⟩ := H 0
  cases hb

/-- Tightness of `hEL_A` in R3f: `A` = `boolNZRep` (`IntoBytes`, not `EncodeLeast`), `B` = `u8Rep`
(`FromBytes`); for `v = true` the only candidate is `b = 1` (the transmute result), and the block
`[init 2]` satisfies the decode-based points-to of `true` at `A` and not that of `1` at `B`. -/
theorem exists_ptsDec_viewChange_tight_hEL_A :
    boolNZRep.IntoBytes ∧ u8Rep.FromBytes ∧ ¬ boolNZRep.EncodeLeast ∧
      ¬ ∀ v : Bool, ∃ b : Byte, transmute boolNZRep u8Rep v = some b ∧
          ∀ (p : Perm) (a : Nat) (h : BHeap Byte), ptsDec p boolNZRep a v h → ptsDec p u8Rep a b h := by
  refine ⟨boolNZRep_intoBytes, u8Rep_fromBytes, boolNZRep_not_encodeLeast, fun H => ?_⟩
  obtain ⟨b, hb, he⟩ := H true
  have hb1 : b = 1 := by
    have : transmute boolNZRep u8Rep true = some (1 : Byte) := rfl
    rw [this] at hb
    injection hb with hb
    exact hb.symm
  subst hb1
  obtain ⟨x, hx, hd⟩ := he .full 0 (Heap.block .full 0 #v[.init 2]) ⟨_, rfl, rfl⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-- Tightness of `hFB_B` in R3f ("a niche value"): `A` = `u8Rep` (`IntoBytes`, `EncodeLeast`),
`B` = `boolRep` (not `FromBytes`); `transmute` fails at `2`, so no `b` exists. -/
theorem exists_ptsDec_viewChange_tight_hFB_B :
    u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧ ¬ boolRep.FromBytes ∧
      ¬ ∀ v : Byte, ∃ b : Bool, transmute u8Rep boolRep v = some b ∧
          ∀ (p : Perm) (a : Nat) (h : BHeap Byte), ptsDec p u8Rep a v h → ptsDec p boolRep a b h := by
  refine ⟨u8Rep_intoBytes, u8Rep_encodeLeast, boolRep_not_fromBytes, fun H => ?_⟩
  obtain ⟨b, hb, _⟩ := H 2
  cases hb

/-! ## R3d, R3e: view changes are one-directional -/

/-- **R3d (counterexample: niche).** Viewing `boolRep` as `u8Rep` is a view change for every value
(`boolRep` value `v` becomes the byte `boolEnc v`), but viewing `u8Rep` as `boolRep` is not: the
block `[init 2]` satisfies the decode-based points-to of `2` at `u8Rep` and of no value at
`boolRep`. -/
theorem niche_viewChange_one_directional :
    (∀ (v : Bool) (p : Perm) (a : Nat) (h : BHeap Byte),
        ptsDec p boolRep a v h → ptsDec p u8Rep a (boolEnc v) h) ∧
      ptsDec .full u8Rep 0 (2 : Byte) (Heap.block .full 0 #v[.init 2]) ∧
      (∀ b : Bool, ¬ ptsDec .full boolRep 0 b (Heap.block .full 0 #v[.init 2])) ∧
      ¬ (∀ (p : Perm) (a : Nat) (h : BHeap Byte),
          ptsDec p u8Rep a (2 : Byte) h → ∃ b, ptsDec p boolRep a b h) := by
  have hno : ∀ b : Bool, ¬ ptsDec .full boolRep 0 b (Heap.block .full 0 #v[.init 2]) := by
    rintro b ⟨x, hx, hd⟩
    have hx' := Heap.block_inj hx
    subst hx'
    revert hd
    cases b <;> decide
  refine ⟨?_, ⟨_, rfl, rfl⟩, hno, ?_⟩
  · rintro v p a h ⟨x, hx, hd⟩
    refine ⟨x, hx, ?_⟩
    have hle := boolRep_encodeLeast x v hd
    have hx0 : x[0] = .init (boolEnc v) := (AByte.init_le_iff).mp (hle 0 (by decide))
    rw [u8Rep, byteRep_decode, hx0]
  · intro H
    obtain ⟨b, hb⟩ := H .full 0 (Heap.block .full 0 #v[.init 2]) ⟨_, rfl, rfl⟩
    exact hno b hb

/-- **R3e (counterexample: padding read as data).** Viewing `pairRep` (a two-byte integer
`(x, y)`) as `u8PadRep` (a `u8` followed by a padding byte) is a view change for every value (the
padded struct holds `x`), but the reverse is not: the block `[init 5, uninit]` satisfies the
decode-based points-to of `5` at `u8PadRep` and of no value at `pairRep`. -/
theorem padding_viewChange_one_directional :
    (∀ (x y : Byte) (p : Perm) (a : Nat) (h : BHeap Byte),
        ptsDec p (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) a (x, y) h →
          ptsDec p u8PadRep a x h) ∧
      ptsDec .full u8PadRep 0 (5 : Byte) (Heap.block .full 0 #v[.init 5, .uninit]) ∧
      (∀ w : Byte × Byte, ¬ ptsDec .full (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) 0 w
          (Heap.block .full 0 #v[.init 5, .uninit])) ∧
      ¬ (∀ (p : Perm) (a : Nat) (h : BHeap Byte),
          ptsDec p u8PadRep a (5 : Byte) h →
            ∃ w, ptsDec p (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) a w h) := by
  have hno : ∀ w : Byte × Byte, ¬ ptsDec .full (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) 0 w
      (Heap.block .full 0 #v[.init 5, .uninit]) := by
    rintro w ⟨z, hz, hd⟩
    have hz' := Heap.block_inj hz
    subst hz'
    cases hd
  refine ⟨?_, ⟨_, rfl, rfl⟩, hno, ?_⟩
  · rintro x y p a h ⟨z, hz, hd⟩
    refine ⟨z, hz, ?_⟩
    have hle := pairRep_encodeLeast z (x, y) hd
    have hz0 : z[0] = .init x := (AByte.init_le_iff).mp (hle 0 (by decide))
    rw [u8PadRep, padRep_decode, hz0]
  · intro H
    obtain ⟨w, hw⟩ := H .full 0 (Heap.block .full 0 #v[.init 5, .uninit]) ⟨_, rfl, rfl⟩
    exact hno w hw

/-! ## Vacuity boundary shared by R3c and R3f -/

/-- R3c and R3f do not assume `DecodeEncode` of the source. For the always-failing source decoder
`noneRep u8Rep.encode` (the `u8` encoder, a decoder that accepts nothing) every hypothesis of R3c
and R3f holds — the source is `IntoBytes` and `EncodeLeast`, the target `u8Rep` is `FromBytes`,
and `transmute` is total — yet the decode-based points-to at the source holds for no value,
permission, address or heap, so both entailments hold vacuously. -/
theorem viewChange_hyps_hold_and_source_ptsDec_empty_noneRep :
    (noneRep u8Rep.encode).IntoBytes ∧
      (noneRep u8Rep.encode).EncodeLeast ∧
      u8Rep.FromBytes ∧
      TransmuteTotal (noneRep u8Rep.encode) u8Rep ∧
      ∀ (v : Byte) (p : Perm) (a : Nat) (h : BHeap Byte),
        ¬ ptsDec p (noneRep u8Rep.encode) a v h :=
  ⟨u8Rep_intoBytes, noneRep_encodeLeast _, u8Rep_fromBytes,
    fun v => ⟨v, rfl⟩, fun _ _ _ _ ⟨_, _, hd⟩ => by cases hd⟩

end Toy.ByteSL
