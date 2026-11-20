import Toy.ByteSL.Heap

/-!
# Result group 1: typed points-to from byte points-to, two candidate definitions

For a representation `r : Rep (Bytes D n) V` (an `n`-byte encoding of values of type `V`):

* **encode-based** typed points-to `ptsEnc p r a v`: the `n` bytes at `a` are exactly
  `r.encode v` (`a ↦[r] v := a ↦ᵦ r.encode v`);
* **decode-based** typed points-to `ptsDec p r a v`: the `n` bytes at `a` are *some* byte vector
  `x` with `r.decode x = some v` (`∃ x, a ↦ᵦ x ∧ decode x = some v`).

Results:

* `ptsEnc_entails_ptsDec_iff_decodeEncode` (R1a): encode-based entails decode-based (at every
  permission, address, value and heap) exactly when `DecodeEncode` holds.
* `ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast` (R1b): decode-based
  typed points-to is exactly the *byte-definedness upward closure* of the encode-based one (the
  heaps obtained from the encoding by initializing zero or more `uninit` bytes, same cells, same
  permissions) at every permission, address, value and heap, if and only if the representation
  satisfies the three laws `DecodeMono`, `DecodeEncode`, `EncodeLeast`.
* `ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty` (R1c): under
  the three laws and a nonempty byte payload type, the two definitions coincide exactly when the
  representation is `IntoBytes` (no encoding contains `uninit`).
* `u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding` (R1d, counterexample): for a padded
  struct satisfying all three laws, a heap whose padding byte is initialized satisfies the
  decode-based but not the encode-based typed points-to.
-/

namespace Toy.ByteSL

open SepStruct

/-! ## Definitions -/

/-- **Encode-based typed points-to** `a ↦enc[r, p] v`: the heap is exactly the `n` cells at
`a, …, a + n - 1` with permission `p`, holding the bytes `r.encode v`. Captures "the memory holds
the bytes a typed store of `v` writes", including `uninit` padding. -/
def ptsEnc {D V : Type} {n : Nat} (p : Perm) (r : Rep (Bytes D n) V) (a : Nat) (v : V) :
    Assn (BHeap D) :=
  ptsB p a (r.encode v)

/-- **Decode-based typed points-to** `a ↦dec[r, p] v`: the heap is exactly the `n` cells at
`a, …, a + n - 1` with permission `p`, holding some bytes `x` that decode to `v`. Captures "a
typed load of the memory yields `v`"; padding bytes may hold anything the decoder accepts. -/
def ptsDec {D V : Type} {n : Nat} (p : Perm) (r : Rep (Bytes D n) V) (a : Nat) (v : V) :
    Assn (BHeap D) :=
  fun h => ∃ x : Bytes D n, ptsB p a x h ∧ r.decode x = some v

/-! ## Helper lemmas -/

theorem Bytes.eq_one {D : Type} (x : Bytes D 1) : x = #v[x[0]] := by
  apply Vector.ext
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  rfl

theorem heapByteLe_refl_block {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) :
    HeapByteLe (Heap.block p a x) (Heap.block p a x) :=
  heapByteLe_block_of_le p a (Bytes.le_refl x)

/-- From `HeapByteLe` between two blocks at the same address and permission, read off the byte
order at one offset. -/
theorem le_of_heapByteLe_block {D : Type} {n : Nat} {p : Perm} {a : Nat} {x y : Bytes D n}
    (hle : HeapByteLe (Heap.block p a x) (Heap.block p a y)) {i : Nat} (hi : i < n) :
    x[i] ⊑ y[i] :=
  ((hle (a + i)).2 _ _ (Heap.block_val_add p a x hi) (Heap.block_val_add p a y hi)).2

/-! ## R1a: encode-based entails decode-based iff `DecodeEncode` -/

/-- **R1a.** For every representation `r` in `n`-byte vectors: the encode-based typed points-to
entails the decode-based one, at every permission, address, value and heap, exactly when `r`
satisfies `DecodeEncode` (`decode (encode v) = some v` for all `v`). No other law is involved.
(R1a is the special case `rA = rB = r`, `b = v`, quantified over all `v`, of R3a.) -/
theorem ptsEnc_entails_ptsDec_iff_decodeEncode {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    (∀ (p : Perm) (a : Nat) (v : V) (h : BHeap D), ptsEnc p r a v h → ptsDec p r a v h) ↔
      r.DecodeEncode := by
  exact ⟨fun H v => let ⟨_, hx, hd⟩ := H .full 0 v _ rfl; Heap.block_inj hx ▸ hd,
    fun hDE _ _ v _ hh => ⟨_, hh, hDE v⟩⟩

/-- Non-vacuity for R1a: the padded struct `u8PadRep` satisfies `DecodeEncode`, and its
encode-based points-to is satisfied by the block holding its encoding. -/
theorem ptsEnc_entails_ptsDec_iff_decodeEncode_nonvacuous :
    u8PadRep.DecodeEncode ∧
      ptsEnc .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .uninit] : Bytes Byte 2)) :=
  ⟨u8PadRep_decodeEncode, rfl⟩

/-- Tightness illustration for R1a (the right-hand side fails, and so does the entailment): the
always-failing decoder `noneRep u8Rep.encode`. -/
theorem ptsEnc_entails_ptsDec_fails_noneRep :
    ¬ (noneRep u8Rep.encode).DecodeEncode ∧
      ptsEnc .full (noneRep u8Rep.encode) 0 (0 : Byte) (Heap.block .full 0 #v[.init 0]) ∧
      ¬ ptsDec .full (noneRep u8Rep.encode) 0 (0 : Byte) (Heap.block .full 0 #v[.init 0]) :=
  ⟨noneRep_not_decodeEncode _ 0, rfl, fun ⟨_, _, hd⟩ => by cases hd⟩

theorem option_get_eq_of_eq {α : Type} {o : Option α} {x : α}
    (his : o.isSome = true) (ho : o = some x) : o.get his = x := by
  subst ho
  rfl

theorem option_eq_some_get {α : Type} {o : Option α} (his : o.isSome = true) :
    o = some (o.get his) := by
  cases o with
  | none => cases his
  | some a => rfl

/-- The "if" direction of R1b, pointwise: under the three laws, the decode-based points-to holds
exactly on the byte-definedness upward closure of the encode-based one. -/
theorem ptsDec_iff_byteUpClose_ptsEnc_of_laws {D V : Type} {n : Nat}
    (r : Rep (Bytes D n) V) (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast)
    (p : Perm) (a : Nat) (v : V) (h : BHeap D) :
    ptsDec p r a v h ↔ byteUpClose (ptsEnc p r a v) h := by
  constructor
  · rintro ⟨x, rfl, hd⟩
    exact ⟨_, rfl, heapByteLe_block_of_le p a (hEL x v hd)⟩
  · rintro ⟨_, rfl, hle⟩
    have hall : ∀ i, i < n → (h.val (a + i)).isSome = true := by
      intro i hi
      cases e : h.val (a + i) with
      | some _ => rfl
      | none =>
        have e0 := (hle (a + i)).1.mpr e
        rw [Heap.block_val_add p a _ hi] at e0
        cases e0
    let y : Bytes D n := Vector.ofFn fun i => ((h.val (a + i.val)).get (hall i.val i.isLt)).byte
    have hxy : r.encode v ⊑ y := by
      intro i hi
      simp only [y, Vector.getElem_ofFn]
      exact ((hle (a + i)).2 _ _ (Heap.block_val_add p a _ hi) (option_eq_some_get (hall i hi))).2
    have heq : h = Heap.block p a y := by
      apply Heap.ext
      intro k
      by_cases hk : a ≤ k ∧ k < a + n
      · obtain ⟨i, rfl⟩ : ∃ i, k = a + i := ⟨k - a, by omega⟩
        have hi : i < n := by omega
        have ec := option_eq_some_get (hall i hi)
        have hp := ((hle (a + i)).2 _ _ (Heap.block_val_add p a _ hi) ec).1
        rw [Heap.block_val_add p a y hi]
        simp only [y, Vector.getElem_ofFn]
        exact ec.trans (congrArg (fun p' : Perm =>
          (some ⟨p', ((h.val (a + i)).get (hall i hi)).byte⟩ : Option (Cell D))) hp.symm)
      · have e0 : (Heap.block p a (r.encode v)).val k = none := by
          unfold Heap.block
          rw [Heap.blockOn_val]
          simp only [hk, dite_false]
        have eh : h.val k = none := (hle k).1.mp e0
        have ey : (Heap.block p a y).val k = none := by
          unfold Heap.block
          rw [Heap.blockOn_val]
          simp only [hk, dite_false]
        rw [eh, ey]
    exact ⟨y, heq, OptLe.some_le_iff.mp (hDE v ▸ hM _ _ hxy)⟩

/-! ## R1b: decode-based = byte-definedness upward closure of encode-based, iff the three laws -/

/-- **R1b.** For every representation `r` in `n`-byte vectors (no law assumed): the decode-based
typed points-to coincides with the byte-definedness upward closure of the encode-based one, at
every permission `p`, address `a`, value `v` and heap `h` (i.e. `h` satisfies `ptsDec p r a v` iff
`h` is obtained from the block holding `r.encode v` at `a` by initializing zero or more of its
`uninit` bytes, same cells and permissions), if and only if `r` satisfies `DecodeMono`,
`DecodeEncode` and `EncodeLeast`. The heap-assertion form of the lower-adjoint characterization of
the three laws. -/
theorem ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast {D V : Type} {n : Nat}
    (r : Rep (Bytes D n) V) :
    (∀ (p : Perm) (a : Nat) (v : V) (h : BHeap D),
        ptsDec p r a v h ↔ byteUpClose (ptsEnc p r a v) h) ↔
      (r.DecodeMono ∧ r.DecodeEncode ∧ r.EncodeLeast) := by
  constructor
  · intro H
    have hEL : r.EncodeLeast := by
      intro x v hd
      obtain ⟨h₀, hh₀, hle⟩ := (H .full 0 v (Heap.block .full 0 x)).mp ⟨x, rfl, hd⟩
      have hh₀' : h₀ = Heap.block .full 0 (r.encode v) := hh₀
      subst hh₀'
      exact fun i hi => le_of_heapByteLe_block hle hi
    have hDE : r.DecodeEncode := by
      intro v
      obtain ⟨x, hx, hd⟩ := (H .full 0 v (Heap.block .full 0 (r.encode v))).mpr
        ⟨_, rfl, heapByteLe_refl_block _ _ _⟩
      rw [← Heap.block_inj hx] at hd
      exact hd
    refine ⟨?_, hDE, hEL⟩
    intro x y hxy
    cases hdx : r.decode x with
    | none => exact OptLe.none_le _
    | some v =>
      have h1 : r.encode v ⊑ y := Bytes.le_trans (hEL x v hdx) hxy
      obtain ⟨y', hy', hd'⟩ := (H .full 0 v (Heap.block .full 0 y)).mpr
        ⟨_, rfl, heapByteLe_block_of_le .full 0 h1⟩
      rw [← Heap.block_inj hy'] at hd'
      rw [hd']
      exact OptLe.refl _
  · rintro ⟨hM, hDE, hEL⟩ p a v h
    exact ptsDec_iff_byteUpClose_ptsEnc_of_laws r hM hDE hEL p a v h

/-- Non-vacuity for R1b: `u8PadRep` satisfies all three laws (so both sides of R1b hold for it),
and the block whose padding byte is initialized lies in the byte-definedness upward closure of the
encode-based points-to without being the encoding itself (so the closure is not trivial). -/
theorem ptsDec_eq_byteUpClose_nonvacuous :
    u8PadRep.DecodeMono ∧ u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧
      byteUpClose (ptsEnc .full u8PadRep 0 5)
        (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) ∧
      ptsDec .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) ∧
      ¬ ptsEnc .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) := by
  refine ⟨u8PadRep_decodeMono, u8PadRep_decodeEncode, u8PadRep_encodeLeast,
    ⟨Heap.block .full 0 #v[.init 5, .uninit], rfl,
      heapByteLe_block_of_le .full 0 (Bytes.le_two rfl trivial)⟩, ⟨_, rfl, rfl⟩, fun h => ?_⟩
  have := Heap.block_inj h
  have := congrArg (fun x : Bytes Byte 2 => x[1]) this
  cases this

/-- Independence of `DecodeMono` in R1b: `exactUnitRep` (only `[uninit]` decodes) satisfies
`DecodeEncode` and `EncodeLeast` but not `DecodeMono`, and the coincidence fails: the block
`[init 0]` lies in the byte-definedness upward closure of its encoding `[uninit]` but does not
decode. -/
theorem ptsDec_eq_byteUpClose_fails_exactUnitRep :
    exactUnitRep.DecodeEncode ∧ exactUnitRep.EncodeLeast ∧ ¬ exactUnitRep.DecodeMono ∧
      ¬ ∀ (p : Perm) (a : Nat) (v : Unit) (h : BHeap Byte),
        (ptsDec p exactUnitRep a v h ↔ byteUpClose (ptsEnc p exactUnitRep a v) h) := by
  refine ⟨exactUnitRep_decodeEncode, exactUnitRep_encodeLeast, exactUnitRep_not_decodeMono,
    fun H => ?_⟩
  obtain ⟨x, hx, hd⟩ := (H .full 0 () (Heap.block .full 0 #v[.init 0])).mpr
    ⟨Heap.block .full 0 #v[.uninit], rfl, heapByteLe_block_of_le .full 0 (Bytes.le_one trivial)⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-- Independence of `DecodeEncode` in R1b: the always-failing decoder `noneRep u8Rep.encode`
satisfies `DecodeMono` and `EncodeLeast` but not `DecodeEncode`, and the coincidence fails: the
block holding the encoding of `0` lies in the byte-definedness upward closure but does not
decode. -/
theorem ptsDec_eq_byteUpClose_fails_noneRep :
    (noneRep u8Rep.encode).DecodeMono ∧ (noneRep u8Rep.encode).EncodeLeast ∧
      ¬ (noneRep u8Rep.encode).DecodeEncode ∧
      ¬ ∀ (p : Perm) (a : Nat) (v : Byte) (h : BHeap Byte),
        (ptsDec p (noneRep u8Rep.encode) a v h ↔
          byteUpClose (ptsEnc p (noneRep u8Rep.encode) a v) h) := by
  refine ⟨noneRep_decodeMono _, noneRep_encodeLeast _, noneRep_not_decodeEncode _ 0, fun H => ?_⟩
  obtain ⟨x, _, hd⟩ := (H .full 0 0 (Heap.block .full 0 #v[.init 0])).mpr
    ⟨Heap.block .full 0 #v[.init 0], rfl, heapByteLe_refl_block _ _ _⟩
  cases hd

/-- Independence of `EncodeLeast` in R1b: `boolNZRep` (every nonzero byte decodes to `true`,
`true` is encoded as `1`) satisfies `DecodeMono` and `DecodeEncode` but not `EncodeLeast`, and the
coincidence fails: the block `[init 2]` satisfies the decode-based points-to of `true` but is not
an upward change of the encoding `[init 1]`. -/
theorem ptsDec_eq_byteUpClose_fails_boolNZRep :
    boolNZRep.DecodeMono ∧ boolNZRep.DecodeEncode ∧ ¬ boolNZRep.EncodeLeast ∧
      ¬ ∀ (p : Perm) (a : Nat) (v : Bool) (h : BHeap Byte),
        (ptsDec p boolNZRep a v h ↔ byteUpClose (ptsEnc p boolNZRep a v) h) := by
  refine ⟨boolNZRep_decodeMono, boolNZRep_decodeEncode, boolNZRep_not_encodeLeast, fun H => ?_⟩
  obtain ⟨h₀, hh₀, hle⟩ := (H .full 0 true (Heap.block .full 0 #v[.init 2])).mp
    ⟨#v[.init 2], rfl, rfl⟩
  have hh₀' : h₀ = Heap.block .full 0 #v[.init 1] := hh₀
  subst hh₀'
  have := le_of_heapByteLe_block hle (i := 0) (by decide)
  exact absurd ((AByte.init_le_init_iff _ _).mp this) (by decide)

/-! ## R1c: the two definitions coincide iff `IntoBytes`, under the three laws -/

/-- **R1c.** If `r` satisfies `DecodeMono`, `DecodeEncode` and `EncodeLeast`, and the byte payload
type `D` is nonempty, then the decode-based and encode-based typed points-to coincide (at every
permission, address, value and heap) exactly when `r` is `IntoBytes`, i.e. no encoding of `r`
contains an `uninit` byte. -/
theorem ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty
    {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (hD : Nonempty D) :
    (∀ (p : Perm) (a : Nat) (v : V) (h : BHeap D), ptsDec p r a v h ↔ ptsEnc p r a v h) ↔
      r.IntoBytes := by
  constructor
  · intro H v i hi
    cases hb : (r.encode v)[i] with
    | init d => rfl
    | uninit =>
      obtain ⟨d⟩ := hD
      let y : Bytes D n := (r.encode v).set i (.init d) hi
      have hle : r.encode v ⊑ y := by
        intro j hj
        by_cases hij : i = j
        · subst hij
          simp [y, hb]
        · simp [y, hij, AByte.le_refl]
      have hd : r.decode y = some v := OptLe.some_le_iff.mp (hDE v ▸ hM _ _ hle)
      have he : ptsEnc .full r 0 v (Heap.block .full 0 y) :=
        (H .full 0 v _).mp ⟨y, rfl, hd⟩
      have hy := congrArg (fun z : Bytes D n => z[i]) (Heap.block_inj he)
      simp [y, hb] at hy
  · intro hIB p a v h
    constructor
    · rintro ⟨x, hx, hd⟩
      rw [Bytes.eq_of_le_of_isInit (hEL x v hd) (hIB v)] at hx
      exact hx
    · intro hh
      exact ⟨_, hh, hDE v⟩

/-- Non-vacuity for R1c: all hypotheses hold for `u8Rep` (which is `IntoBytes`) and for the
padded struct `u8PadRep` (which is not). -/
theorem ptsDec_iff_ptsEnc_iff_intoBytes_nonvacuous :
    (u8Rep.DecodeMono ∧ u8Rep.DecodeEncode ∧ u8Rep.EncodeLeast ∧ Nonempty Byte ∧
      u8Rep.IntoBytes) ∧
    (u8PadRep.DecodeMono ∧ u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧ Nonempty Byte ∧
      ¬ u8PadRep.IntoBytes) :=
  ⟨⟨u8Rep_decodeMono, u8Rep_decodeEncode, u8Rep_encodeLeast, ⟨0⟩, u8Rep_intoBytes⟩,
   ⟨u8PadRep_decodeMono, u8PadRep_decodeEncode, u8PadRep_encodeLeast, ⟨0⟩,
    u8PadRep_not_intoBytes⟩⟩

/-- `exactUnitRep`: the decode-based and encode-based points-to coincide (only `[uninit]`
decodes). -/
theorem exactUnitRep_ptsDec_iff_ptsEnc (p : Perm) (a : Nat) (v : Unit) (h : BHeap Byte) :
    ptsDec p exactUnitRep a v h ↔ ptsEnc p exactUnitRep a v h := by
  constructor
  · rintro ⟨x, hx, hd⟩
    have hx0 : x[0] = .uninit := by
      revert hd
      show (match x[0] with | .uninit => some () | .init _ => none) = some v → x[0] = .uninit
      cases x[0] with
      | uninit => intro _; rfl
      | init b => intro hd; cases hd
    have : x = #v[.uninit] := by rw [Bytes.eq_one x, hx0]
    subst this
    exact hx
  · intro hh
    exact ⟨_, hh, rfl⟩

/-- Tightness of `hM` in R1c: `exactUnitRep` satisfies `DecodeEncode`, `EncodeLeast` and the
payload type is nonempty; the two points-to coincide, yet `exactUnitRep` is not `IntoBytes`. -/
theorem ptsDec_iff_ptsEnc_iff_intoBytes_tight_hM :
    exactUnitRep.DecodeEncode ∧ exactUnitRep.EncodeLeast ∧ Nonempty Byte ∧
      ¬ ((∀ (p : Perm) (a : Nat) (v : Unit) (h : BHeap Byte),
            ptsDec p exactUnitRep a v h ↔ ptsEnc p exactUnitRep a v h) ↔
          exactUnitRep.IntoBytes) := by
  refine ⟨exactUnitRep_decodeEncode, exactUnitRep_encodeLeast, ⟨0⟩, fun H => ?_⟩
  have hIB := H.mp exactUnitRep_ptsDec_iff_ptsEnc
  have := hIB () 0 (by decide)
  cases this

/-- `noneRep u8Rep.encode` is `IntoBytes` (it has the `u8` encoder). -/
theorem noneRep_u8_intoBytes : (noneRep u8Rep.encode).IntoBytes := u8Rep_intoBytes

/-- Tightness of `hDE` in R1c: `noneRep u8Rep.encode` satisfies `DecodeMono` and `EncodeLeast`, the
payload type is nonempty, and it is `IntoBytes`; but the two points-to differ (only the
encode-based one holds at the block holding the encoding of `0`). -/
theorem ptsDec_iff_ptsEnc_iff_intoBytes_tight_hDE :
    (noneRep u8Rep.encode).DecodeMono ∧ (noneRep u8Rep.encode).EncodeLeast ∧ Nonempty Byte ∧
      ¬ ((∀ (p : Perm) (a : Nat) (v : Byte) (h : BHeap Byte),
            ptsDec p (noneRep u8Rep.encode) a v h ↔ ptsEnc p (noneRep u8Rep.encode) a v h) ↔
          (noneRep u8Rep.encode).IntoBytes) := by
  refine ⟨noneRep_decodeMono _, noneRep_encodeLeast _, ⟨0⟩, fun H => ?_⟩
  obtain ⟨_, _, hd⟩ := (H.mpr noneRep_u8_intoBytes .full 0 0 (Heap.block .full 0 #v[.init 0])).mpr rfl
  cases hd

/-- Tightness of `hEL` in R1c: `boolNZRep` satisfies `DecodeMono` and `DecodeEncode`, the payload
type is nonempty, and it is `IntoBytes`; but the block `[init 2]` satisfies the decode-based
points-to for `true` and not the encode-based one (`true` is encoded as `[init 1]`). -/
theorem ptsDec_iff_ptsEnc_iff_intoBytes_tight_hEL :
    boolNZRep.DecodeMono ∧ boolNZRep.DecodeEncode ∧ Nonempty Byte ∧
      ¬ ((∀ (p : Perm) (a : Nat) (v : Bool) (h : BHeap Byte),
            ptsDec p boolNZRep a v h ↔ ptsEnc p boolNZRep a v h) ↔
          boolNZRep.IntoBytes) := by
  refine ⟨boolNZRep_decodeMono, boolNZRep_decodeEncode, ⟨0⟩, fun H => ?_⟩
  have hc := H.mpr boolNZRep_intoBytes .full 0 true (Heap.block .full 0 #v[.init 2])
  have he : ptsEnc .full boolNZRep 0 true (Heap.block .full 0 #v[.init 2]) :=
    hc.mp ⟨#v[.init 2], rfl, rfl⟩
  have := congrArg (fun x : Bytes Byte 1 => x[0]) (Heap.block_inj he)
  exact absurd this (by decide)

/-- A one-byte representation over the *empty* payload type: the only byte vector is `[uninit]`;
it represents `Unit`. -/
def emptyPadRep : Rep (Bytes Empty 1) Unit := ⟨fun _ => #v[.uninit], fun _ => some ()⟩

theorem emptyPadRep_decodeMono : emptyPadRep.DecodeMono := fun _ _ _ => OptLe.refl _
theorem emptyPadRep_decodeEncode : emptyPadRep.DecodeEncode := fun _ => rfl
theorem emptyPadRep_encodeLeast : emptyPadRep.EncodeLeast := fun x _ _ => Bytes.uninit_le x
theorem emptyPadRep_not_intoBytes : ¬ emptyPadRep.IntoBytes := fun h => by
  have := h () 0 (by decide)
  cases this

/-- Every byte vector over the empty payload type is all-`uninit`. -/
theorem Bytes.eq_uninit_of_empty (x : Bytes Empty 1) : x = #v[.uninit] := by
  rw [Bytes.eq_one x]
  cases x[0] with
  | uninit => rfl
  | init e => exact e.elim

/-- Tightness of `hD` in R1c: over the empty payload type, `emptyPadRep` satisfies all three laws
and the two points-to coincide, yet it is not `IntoBytes`. -/
theorem ptsDec_iff_ptsEnc_iff_intoBytes_tight_hD :
    emptyPadRep.DecodeMono ∧ emptyPadRep.DecodeEncode ∧ emptyPadRep.EncodeLeast ∧
      ¬ Nonempty Empty ∧
      ¬ ((∀ (p : Perm) (a : Nat) (v : Unit) (h : BHeap Empty),
            ptsDec p emptyPadRep a v h ↔ ptsEnc p emptyPadRep a v h) ↔
          emptyPadRep.IntoBytes) := by
  refine ⟨emptyPadRep_decodeMono, emptyPadRep_decodeEncode, emptyPadRep_encodeLeast,
    fun ⟨e⟩ => e.elim, fun H => emptyPadRep_not_intoBytes (H.mp fun p a v h => ?_)⟩
  constructor
  · rintro ⟨x, hx, _⟩
    rw [Bytes.eq_uninit_of_empty x] at hx
    exact hx
  · intro hh
    exact ⟨_, hh, rfl⟩

/-! ## R1d: counterexample — initialized padding -/

/-- **R1d (counterexample).** The representation `u8PadRep` (modeling a `u8` followed by one
padding byte, encoded with `uninit` padding) satisfies `DecodeMono`, `DecodeEncode` and
`EncodeLeast`; the block `[init 5, init 7]` (padding byte initialized to `7`) satisfies the
decode-based typed points-to for `5` but not the encode-based one. -/
theorem u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding :
    u8PadRep.DecodeMono ∧ u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧
      ptsDec .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) ∧
      ¬ ptsEnc .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) :=
  ⟨u8PadRep_decodeMono, u8PadRep_decodeEncode, u8PadRep_encodeLeast, ⟨_, rfl, rfl⟩,
    (ptsDec_eq_byteUpClose_nonvacuous).2.2.2.2.2⟩

/-- Contrast for R1d: when the padding byte is `uninit`, the block is the encoding itself and both
typed points-to hold. -/
theorem u8PadRep_uninit_padding_ptsDec_and_ptsEnc :
    ptsDec .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .uninit] : Bytes Byte 2)) ∧
      ptsEnc .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .uninit] : Bytes Byte 2)) :=
  ⟨⟨_, rfl, rfl⟩, rfl⟩

end Toy.ByteSL
