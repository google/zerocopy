import ToyReprLower.Basic

/-!
# Auxiliary lemmas about abstract bytes, segments and placement
-/

namespace Toy.ReprLower

namespace AByte

@[simp] theorem leb_refl (a : AByte) : a.leb a = true := by
  cases a <;> simp [leb]

@[simp] theorem uninit_leb (a : AByte) : AByte.uninit.leb a = true := by
  cases a <;> rfl

theorem leb_uninit_iff (a : AByte) : a.leb .uninit = true ↔ a = .uninit := by
  cases a <;> simp [leb]

end AByte

theorem bytesLeb_refl (x : List AByte) : bytesLeb x x = true := by
  induction x with
  | nil => rfl
  | cons a as ih => simp [bytesLeb, ih]

theorem bytesLe_refl (x : List AByte) : BytesLe x x := bytesLeb_refl x

theorem bytesLeb_iff_getD (x y : List AByte) :
    bytesLeb x y = true ↔ x.length = y.length ∧
      ∀ i, i < x.length → (x.getD i .uninit).leb (y.getD i .uninit) = true := by
  induction x generalizing y with
  | nil => cases y <;> simp [bytesLeb]
  | cons a as ih =>
    cases y with
    | nil => simp [bytesLeb]
    | cons b bs =>
      simp only [bytesLeb, Bool.and_eq_true, ih, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨hab, hl, h⟩
        refine ⟨hl, fun i hi => ?_⟩
        cases i with
        | zero => simpa using hab
        | succ i => simpa using h i (by omega)
      · rintro ⟨hl, h⟩
        refine ⟨by simpa using h 0 (by omega), hl, fun i hi => ?_⟩
        simpa using h (i + 1) (by omega)

theorem length_seg (x : List AByte) (o w : Nat) : (seg x o w).length = min w (x.length - o) := by
  simp [seg]

theorem getD_seg (x : List AByte) (o w k : Nat) :
    (seg x o w).getD k .uninit = if k < w then x.getD (o + k) .uninit else .uninit := by
  simp only [seg, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  split <;> simp

theorem length_place (n : Nat) (cs : List (Nat × List AByte)) : (place n cs).length = n := by
  simp [place]

theorem getD_place (n : Nat) (cs : List (Nat × List AByte)) (i : Nat) :
    (place n cs).getD i .uninit = if i < n then chunkAt cs i else .uninit := by
  by_cases h : i < n
  · simp [place, h]
  · simp [place, h, List.getD_eq_getElem?_getD]

theorem chunkAt_one (o : Nat) (c : List AByte) (i : Nat) :
    chunkAt [(o, c)] i = if o ≤ i ∧ i < o + c.length then c.getD (i - o) .uninit else .uninit := by
  simp [chunkAt]

theorem chunkAt_two (o₁ o₂ : Nat) (c₁ c₂ : List AByte) (i : Nat) :
    chunkAt [(o₁, c₁), (o₂, c₂)] i =
      if o₁ ≤ i ∧ i < o₁ + c₁.length then c₁.getD (i - o₁) .uninit
      else if o₂ ≤ i ∧ i < o₂ + c₂.length then c₂.getD (i - o₂) .uninit else .uninit := by
  simp [chunkAt]

theorem allUninit_any_isFrag {bs : List AByte} (h : allUninit bs = true) :
    bs.any AByte.isFrag = false := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [allUninit, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [AByte.isFrag, ih h2]

theorem bytesLeb_replicate_uninit (bs : List AByte) :
    bytesLeb bs (List.replicate bs.length .uninit) = allUninit bs := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.replicate_succ, bytesLeb, ih, allUninit, List.all_cons]
    cases a <;> simp [AByte.leb]

theorem bytesLeb_map_bits_datas {bs : List AByte} (h : allInit bs = true) :
    bytesLeb bs ((datas bs).map .bits) = !bs.any AByte.isFrag := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [allInit, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ha, h2⟩ := h
    simp only [datas, List.map_cons, bytesLeb, List.any_cons] at ih ⊢
    rw [ih h2]
    cases a <;> simp_all [AByte.leb, AByte.isFrag, AByte.data, AByte.isInit]

theorem allBits_allInit {bs : List AByte} (h : allBits bs = true) : allInit bs = true := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [allBits, List.all_cons, Bool.and_eq_true] at h
    simp only [allInit, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    cases a <;> simp_all [AByte.isBits, AByte.isInit]

theorem map_bits_datas_of_allBits {bs : List AByte} (h : allBits bs = true) :
    (datas bs).map .bits = bs := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [allBits, List.all_cons, Bool.and_eq_true] at h
    simp only [datas, List.map_cons] at ih ⊢
    rw [ih h.2]
    cases a <;> simp_all [AByte.isBits, AByte.data]

theorem fragsList_datas {p k : Nat} {bs : List AByte} (h : fragsFrom p k bs = true) :
    fragsList p k (datas bs) = bs := by
  induction bs generalizing k with
  | nil => rfl
  | cons a as ih =>
    cases a with
    | uninit => simp [fragsFrom] at h
    | bits b => simp [fragsFrom] at h
    | ptrFrag b q i =>
      simp only [fragsFrom, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, h2⟩ := h
      simp only [datas, List.map_cons, AByte.data, fragsList] at ih ⊢
      rw [ih h2]

theorem fragsFrom_allInit {p k : Nat} {bs : List AByte} (h : fragsFrom p k bs = true) :
    allInit bs = true := by
  induction bs generalizing k with
  | nil => rfl
  | cons a as ih =>
    cases a with
    | uninit => simp [fragsFrom] at h
    | bits b => simp [fragsFrom] at h
    | ptrFrag b q i =>
      simp only [fragsFrom, Bool.and_eq_true] at h
      have := ih h.2
      simp only [allInit, List.all_cons, AByte.isInit, Bool.true_and] at this ⊢
      exact this

theorem length_fragsList (p k : Nat) (ds : List Nat) : (fragsList p k ds).length = ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih => simp [fragsList, ih]

/-- What `ptrProv` returns: none, or a provenance whose fragments the bytes are, in order from
position `0`. -/
theorem ptrProv_cases (bs : List AByte) :
    ptrProv bs = none ∨ (∃ p, fragsFrom p 0 bs = true ∧ ptrProv bs = some p) := by
  unfold ptrProv
  cases hp : fragProv bs with
  | none => exact Or.inl rfl
  | some p =>
    cases hf : fragsFrom p 0 bs
    · exact Or.inl (by simp [hf])
    · exact Or.inr ⟨p, hf, by simp [hf]⟩

/-- Raising a lowered pointer register gives back the bytes if they are one pointer's fragments,
and their plain data bytes otherwise. -/
theorem raiseScalar_ptrLower_cases (s : Scalar) (bs : List AByte) :
    (ptrProv bs = none ∧ raiseScalar s (ptrLower bs) = (datas bs).map .bits) ∨
    (∃ p, fragsFrom p 0 bs = true ∧ ptrProv bs = some p ∧ raiseScalar s (ptrLower bs) = bs) := by
  rcases ptrProv_cases bs with h1 | ⟨q, hf, h1⟩
  · exact Or.inl ⟨h1, by simp [ptrLower, h1, raiseScalar]⟩
  · exact Or.inr ⟨q, hf, h1, by simp [ptrLower, h1, raiseScalar, fragsList_datas hf]⟩

theorem length_raiseScalar_ptrLower (s : Scalar) (bs : List AByte) :
    (raiseScalar s (ptrLower bs)).length = bs.length := by
  rcases raiseScalar_ptrLower_cases s bs with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> simp [h, datas]

theorem length_raiseScalar_lowerScalar (s : Scalar) (bs : List AByte) (h : bs.length = s.size) :
    (raiseScalar s (lowerScalar s bs)).length = bs.length := by
  cases s with
  | union p => simp [lowerScalar, raiseScalar]
  | initialized p rng =>
    simp only [lowerScalar]
    split
    · cases p with
      | int w => simp [raiseScalar, datas]
      | ptr w => exact length_raiseScalar_ptrLower _ bs
    · simp [raiseScalar, h]

/-- Lowering then raising a byte list no longer than the scalar gives at least its length. -/
theorem length_le_raiseScalar_lowerScalar (s : Scalar) (bs : List AByte) (h : bs.length ≤ s.size) :
    bs.length ≤ (raiseScalar s (lowerScalar s bs)).length := by
  cases s with
  | union p => simp [lowerScalar, raiseScalar]
  | initialized p rng =>
    simp only [lowerScalar]
    split
    · cases p with
      | int w => simp [raiseScalar, datas]
      | ptr w => rw [length_raiseScalar_ptrLower]; exact Nat.le_refl _
    · simpa [raiseScalar] using h

/-- Lowering then raising a byte list no longer than the scalar gives at most the scalar's width. -/
theorem length_raiseScalar_lowerScalar_le (s : Scalar) (bs : List AByte) (h : bs.length ≤ s.size) :
    (raiseScalar s (lowerScalar s bs)).length ≤ s.size := by
  cases s with
  | union p => simpa [lowerScalar, raiseScalar] using h
  | initialized p rng =>
    simp only [lowerScalar]
    split
    · cases p with
      | int w => simpa [raiseScalar, datas] using h
      | ptr w => rw [length_raiseScalar_ptrLower]; exact h
    · simp [raiseScalar]

end Toy.ReprLower
