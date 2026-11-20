import ToyZc.Derive

/-!
# Result group 1: the semantic trait predicates and their list-level characterizations

The semantic predicates are defined through the representation `Desc.rep` (in the
byte-representation vocabulary of `ToyZc.Basic`). This module proves that each of them is equivalent to a
statement about the list-level encoder/decoder, which is what the later results and all the
concrete examples use:

* `semFromBytes_iff_validInit_total`: `FromBytes` ⟺ the validity check accepts every
  initialized byte list of the right length;
* `semFromZeros_iff_validInit_zeros`: `FromZeros` ⟺ the validity check accepts all zeros;
* `semIntoBytes_iff_encodeL_init`: `IntoBytes` ⟺ every byte of every encoding is initialized.

All three are fully proved.
-/

namespace Toy.Zc

theorem toBytesN_getElem (n : Nat) (l : List AB) (i : Nat) (h : i < n) :
    (toBytesN n l)[i] = l.getD i .uninit := by
  simp [toBytesN]

theorem toList_ofData {n : Nat} (ds : Vector Byte n) :
    (Bytes.ofData ds).toList = ds.toList.map AByte.init := by
  unfold Bytes.ofData
  exact Vector.toList_map

theorem rep_decode_eq_some_iff (d : Desc) (bs : List Byte) (x : Bytes Byte d.size)
    (hx : x.toList = bs.map AByte.init) :
    (∃ v, d.rep.decode x = some v) ↔ validInit d bs = true := by
  unfold Desc.rep validInit
  simp only
  rw [hx]
  cases hd : d.decodeL (bs.map AByte.init) with
  | none => simp
  | some w =>
    by_cases hw : d.hasType w = true
    · simp [hw]
    · simp [hw]

/-- **R1, `FromBytes` part.** Semantic `FromBytes` (every fully initialized byte vector decodes, in the
representation `Desc.rep`) holds iff the validity check `validInit` accepts every byte list of
length `d.size`. -/
theorem semFromBytes_iff_validInit_total (d : Desc) :
    SemFromBytes d ↔ ∀ bs : List Byte, bs.length = d.size → validInit d bs = true := by
  constructor
  · intro h bs hlen
    let ds : Vector Byte d.size := ⟨bs.toArray, by simpa using hlen⟩
    have hx : (Bytes.ofData ds).toList = bs.map AByte.init := by
      rw [toList_ofData]
      rfl
    exact (rep_decode_eq_some_iff d bs _ hx).mp (h _ (Bytes.isInit_ofData ds))
  · intro h x hx
    obtain ⟨ds, rfl⟩ := Bytes.exists_ofData_of_isInit hx
    exact (rep_decode_eq_some_iff d ds.toList _ (toList_ofData ds)).mpr
      (h ds.toList (by simp))

/-- **R1, `FromZeros` part.** Semantic `FromZeros` (the all-zero bytes decode) holds iff the validity check accepts
the all-zero byte list of length `d.size`. -/
theorem semFromZeros_iff_validInit_zeros (d : Desc) :
    SemFromZeros d ↔ validInit d (List.replicate d.size 0) = true := by
  unfold SemFromZeros Rep.tryFrom
  have hx : (Bytes.ofData (Vector.replicate d.size (0 : Byte))).toList =
      (List.replicate d.size (0 : Byte)).map AByte.init := by
    rw [toList_ofData, Vector.toList_replicate]
  rw [← rep_decode_eq_some_iff d _ _ hx]
  cases d.rep.decode (Bytes.ofData (Vector.replicate d.size 0)) with
  | none => simp
  | some v => simp

/-- **R1, `IntoBytes` part.** Semantic `IntoBytes` (no encoding contains `uninit`, in `Desc.rep`) holds iff, for
every well-typed value, every byte of `encodeL` below `d.size` is initialized. -/
theorem semIntoBytes_iff_encodeL_init (d : Desc) :
    SemIntoBytes d ↔
      ∀ v, d.hasType v = true → ∀ i, i < d.size → ((d.encodeL v).getD i .uninit).isInit = true := by
  constructor
  · intro h v hv i hi
    have := h ⟨v, hv⟩ i hi
    simpa [Desc.rep, toBytesN_getElem] using this
  · intro h v i hi
    have := h v.val v.property i hi
    simpa [Desc.rep, toBytesN_getElem] using this

end Toy.Zc
