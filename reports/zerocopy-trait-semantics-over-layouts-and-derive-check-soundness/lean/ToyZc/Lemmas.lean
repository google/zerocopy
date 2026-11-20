import ToyZc.Bridge

/-!
# Supporting lemmas (fully proved)

List-level facts about `fit`, `writeAt`, `allInit`, and the encoder, plus the semantic trait
predicates of the primitive types. These are the positive and negative examples of the semantic
predicates, and they are used by the fully proved results of groups 4 and 7.
-/

namespace Toy.Zc

@[simp] theorem allInit_map_init (bs : List Byte) : allInit (bs.map AByte.init) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [allInit, ih]

theorem fit_length (n : Nat) (l : List AB) : (fit n l).length = n := by
  simp [fit]

theorem fit_of_length {n : Nat} {l : List AB} (h : l.length = n) : fit n l = l := by
  subst h
  simp [fit]

theorem writeAt_length : ∀ (buf : List AB) (o : Nat) (src : List AB),
    (writeAt buf o src).length = buf.length
  | buf, _, [] => by simp [writeAt]
  | [], _, _ :: _ => by simp [writeAt]
  | _ :: bs, 0, s :: ss => by simp [writeAt, writeAt_length bs 0 ss]
  | b :: bs, n + 1, s :: ss => by simp [writeAt, writeAt_length bs n (s :: ss)]

theorem getD_writeAt_zero : ∀ (buf src : List AB) (i : Nat), i < buf.length →
    (writeAt buf 0 src).getD i .uninit =
      if i < src.length then src.getD i .uninit else buf.getD i .uninit
  | buf, [], i, _ => by simp [writeAt]
  | [], _ :: _, i, hi => by simp at hi
  | b :: bs, s :: ss, 0, _ => by simp [writeAt]
  | b :: bs, s :: ss, k + 1, hi => by
    simp only [writeAt, List.getD_cons_succ, List.length_cons]
    rw [getD_writeAt_zero bs ss k (by simp at hi; omega)]
    by_cases hk : k < ss.length
    · simp [hk]
    · have : ¬ (k + 1 < ss.length + 1) := by omega
      simp [hk, this]

theorem getD_replicate_uninit (n i : Nat) :
    (List.replicate n (AByte.uninit : AB)).getD i .uninit = .uninit := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- Every encoding has exactly `d.size` bytes. -/
theorem encodeL_length : ∀ (d : Desc) (v : Val), (d.encodeL v).length = d.size
  | .int t, v => by cases v <;> simp [Desc.encodeL, fit_length, Desc.size, Desc.layout]
  | .bool, v => by cases v <;> simp [Desc.encodeL, Desc.size, Desc.layout]
  | .array e n, v => by cases v <;> simp [Desc.encodeL, fit_length, Desc.size, Desc.layout]
  | .strct r fs, v => by cases v <;> simp [Desc.encodeL, fit_length, Desc.size, Desc.layout]
  | .enm r vs, v => by cases v <;> simp [Desc.encodeL, fit_length, Desc.size, Desc.layout]
  | .union r fs, v => by cases v <;> simp [Desc.encodeL, fit_length, Desc.size, Desc.layout]
  | .cell t, v => by
    simp only [Desc.encodeL]
    exact encodeL_length t v

theorem getD_isInit_lt_length {l : List AB} {i : Nat}
    (h : (l.getD i .uninit).isInit = true) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · exact hlt
  · exfalso
    have : l.getD i .uninit = .uninit := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rw [this] at h
    cases h

/-! ## Semantic predicates of the primitive types (positive and negative examples) -/

theorem validInit_int (t : IntTy) (bs : List Byte) :
    validInit (.int t) bs = (bs.length == t.width) := by
  unfold validInit
  by_cases h : bs.length = t.width
  · simp [Desc.decodeL, h, Desc.hasType]
  · simp [Desc.decodeL, h]

theorem semFromBytes_int (t : IntTy) : SemFromBytes (.int t) :=
  (semFromBytes_iff_validInit_total _).mpr fun bs h => by
    rw [validInit_int]
    simpa [Desc.size, Desc.layout] using h

theorem semFromZeros_int (t : IntTy) : SemFromZeros (.int t) :=
  (semFromZeros_iff_validInit_zeros _).mpr (by rw [validInit_int]; simp [Desc.size, Desc.layout])

theorem semIntoBytes_int (t : IntTy) : SemIntoBytes (.int t) := by
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv i hi
  cases v with
  | int bs =>
    simp only [Desc.hasType, beq_iff_eq] at hv
    have hl : (bs.map AByte.init).length = t.width := by simpa using hv
    simp only [Desc.encodeL]
    rw [fit_of_length hl]
    have hi' : i < bs.length := by simp [Desc.size, Desc.layout] at hi; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  | _ => simp [Desc.hasType] at hv

theorem semFromZeros_bool : SemFromZeros .bool :=
  (semFromZeros_iff_validInit_zeros _).mpr (by decide)

theorem not_semFromBytes_bool : ¬ SemFromBytes .bool := by
  rw [semFromBytes_iff_validInit_total]
  intro h
  have := h [2] rfl
  revert this
  decide

theorem semIntoBytes_bool : SemIntoBytes .bool := by
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv i hi
  cases v with
  | bool b =>
    have hi0 : i = 0 := by simp [Desc.size, Desc.layout] at hi; omega
    subst hi0
    simp [Desc.encodeL]
  | _ => simp [Desc.hasType] at hv

/-- An enum `repr(u8) enum E { A = 1 }`: not `FromZeros` (no zero discriminant). -/
abbrev Desc.noZero : Desc := .enm (.prim .u8) [(.lit 1, [])]

theorem not_semFromZeros_noZero : ¬ SemFromZeros Desc.noZero := by
  rw [semFromZeros_iff_validInit_zeros]
  decide

theorem not_semIntoBytes_paddedPair : ¬ SemIntoBytes Desc.paddedPair := by
  rw [semIntoBytes_iff_encodeL_init]
  intro h
  have := h (.strct [.int [0], .int [0, 0]]) (by decide) 1 (by decide)
  revert this
  decide

theorem semIntoBytes_fullTriple_bytes :
    Desc.fullTriple.encodeL (.strct [.int [1, 2], .int [3], .int [4]]) =
      [.init 1, .init 2, .init 3, .init 4] := by decide

theorem ex_validInit_pos : validInit Desc.paddedPair [1, 0xAA, 2, 3] = true := by decide
theorem ex_validInit_neg : validInit (.array .bool 2) [1, 2] = false := by decide
theorem ex_hasType_pos : Desc.paddedPair.hasType (.strct [.int [1], .int [2, 3]]) = true := by
  decide
theorem ex_hasType_neg : Desc.paddedPair.hasType (.strct [.int [1], .int [2]]) = false := by decide
theorem ex_encodeL_pos : Desc.paddedPair.encodeL (.strct [.int [1], .int [2, 3]]) =
    [.init 1, .uninit, .init 2, .init 3] := by decide
theorem ex_encodeL_neg : Desc.paddedPair.encodeL (.strct [.int [1], .int [2, 3]]) ≠
    [.init 1, .init 0, .init 2, .init 3] := by decide
theorem ex_decodeL_pos : (Desc.bool.decodeL [.init 1]).isSome = true := by decide
theorem ex_decodeL_neg : (Desc.bool.decodeL [.uninit]).isSome = false := by decide
theorem ex_rep_pos : (Desc.u8.rep.decode #v[.init 7]).isSome = true := by decide
theorem ex_rep_neg : (Desc.u8.rep.decode #v[.uninit]).isSome = false := by decide
theorem ex_semUnaligned_pos : SemUnaligned (.strct (.c (.packed 1)) [.u8, .u16]) := by
  unfold SemUnaligned; decide
theorem ex_semUnaligned_neg : ¬ SemUnaligned Desc.paddedPair := by
  unfold SemUnaligned; decide

end Toy.Zc
