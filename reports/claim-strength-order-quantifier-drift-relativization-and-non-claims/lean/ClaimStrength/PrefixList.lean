import ClaimStrength.Prefix

/-! # List lemmas for prefixes: lookup, erasure of a binder, precedence -/

namespace Toy.ClaimStrength

variable {n : Nat} {K : Type} {α : Type}

/-- Delete the binders of `y`. -/
def eraseVar (φ : List (Binder n K)) (y : Fin n) : List (Binder n K) :=
  φ.filter (fun b => decide (b.var ≠ y))

theorem eraseVar_cons_eq {b : Binder n K} {rest : List (Binder n K)} {y : Fin n}
    (h : b.var = y) : eraseVar (b :: rest) y = eraseVar rest y := by
  simp [eraseVar, h]

theorem eraseVar_cons_ne {b : Binder n K} {rest : List (Binder n K)} {y : Fin n}
    (h : b.var ≠ y) : eraseVar (b :: rest) y = b :: eraseVar rest y := by
  simp [eraseVar, h]

theorem bvars_cons (b : Binder n K) (rest : List (Binder n K)) :
    bvars (b :: rest) = b.var :: bvars rest := rfl

theorem mem_bvars_eraseVar {φ : List (Binder n K)} {y v : Fin n} :
    v ∈ bvars (eraseVar φ y) ↔ v ∈ bvars φ ∧ v ≠ y := by
  induction φ with
  | nil => simp [eraseVar, bvars]
  | cons b rest ih =>
    by_cases h : b.var = y
    · rw [eraseVar_cons_eq h, ih, bvars_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with h1 | h1
        · exact absurd (h1.trans h) h2
        · exact ⟨h1, h2⟩
    · rw [eraseVar_cons_ne h, bvars_cons, bvars_cons, List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · subst h1; exact ⟨Or.inl rfl, h⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2⟩

theorem eraseVar_of_not_mem {φ : List (Binder n K)} {y : Fin n} (h : y ∉ bvars φ) :
    eraseVar φ y = φ := by
  induction φ with
  | nil => rfl
  | cons b rest ih =>
    have hb : b.var ≠ y := fun e => h (e ▸ List.mem_cons_self)
    rw [eraseVar_cons_ne hb, ih (fun h' => h (List.mem_cons_of_mem _ h'))]

theorem nodup_cons_iff {a : Fin n} {l : List (Fin n)} : (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup :=
  List.nodup_cons

theorem nodup_eraseVar {φ : List (Binder n K)} (y : Fin n) (h : (bvars φ).Nodup) :
    (bvars (eraseVar φ y)).Nodup := by
  induction φ with
  | nil => simp [eraseVar, bvars]
  | cons b rest ih =>
    rw [bvars_cons, nodup_cons_iff] at h
    by_cases hb : b.var = y
    · rw [eraseVar_cons_eq hb]; exact ih h.2
    · rw [eraseVar_cons_ne hb, bvars_cons, nodup_cons_iff]
      exact ⟨fun hm => h.1 (mem_bvars_eraseVar.1 hm).1, ih h.2⟩

theorem length_eraseVar_le (φ : List (Binder n K)) (y : Fin n) :
    (eraseVar φ y).length ≤ φ.length := List.length_filter_le _ _

theorem length_eraseVar_lt {φ : List (Binder n K)} {y : Fin n} (h : y ∈ bvars φ) :
    (eraseVar φ y).length < φ.length := by
  induction φ with
  | nil => simp [bvars] at h
  | cons b rest ih =>
    by_cases hb : b.var = y
    · rw [eraseVar_cons_eq hb]
      exact Nat.lt_succ_of_le (length_eraseVar_le rest y)
    · rw [eraseVar_cons_ne hb, List.length_cons, List.length_cons]
      rw [bvars_cons] at h
      rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hb
      · exact Nat.succ_lt_succ (ih h)

/-! ### Lookup -/

theorem bOf_cons_eq {b : Binder n K} {rest : List (Binder n K)} {v : Fin n} (h : b.var = v) :
    bOf (b :: rest) v = some b := by simp [bOf, h]

theorem bOf_cons_ne {b : Binder n K} {rest : List (Binder n K)} {v : Fin n} (h : b.var ≠ v) :
    bOf (b :: rest) v = bOf rest v := by simp [bOf, h]

theorem bOf_some {φ : List (Binder n K)} {v : Fin n} {b : Binder n K} (h : bOf φ v = some b) :
    b ∈ φ ∧ b.var = v := by
  induction φ with
  | nil => simp [bOf] at h
  | cons c rest ih =>
    by_cases hc : c.var = v
    · rw [bOf_cons_eq hc] at h; cases h; exact ⟨List.mem_cons_self, hc⟩
    · rw [bOf_cons_ne hc] at h; exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem bOf_of_mem {φ : List (Binder n K)} {v : Fin n} (h : v ∈ bvars φ) :
    ∃ b, bOf φ v = some b := by
  induction φ with
  | nil => simp [bvars] at h
  | cons c rest ih =>
    by_cases hc : c.var = v
    · exact ⟨c, bOf_cons_eq hc⟩
    · rw [bOf_cons_ne hc]
      rw [bvars_cons] at h
      rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hc
      · exact ih h

theorem mem_bvars_of_bOf {φ : List (Binder n K)} {v : Fin n} {b : Binder n K}
    (h : bOf φ v = some b) : v ∈ bvars φ := by
  obtain ⟨hm, hv⟩ := bOf_some h
  exact hv ▸ List.mem_map_of_mem hm

theorem bOf_eq_none {φ : List (Binder n K)} {v : Fin n} (h : v ∉ bvars φ) : bOf φ v = none := by
  cases hb : bOf φ v with
  | none => rfl
  | some b => exact absurd (mem_bvars_of_bOf hb) h

theorem bOf_eraseVar_ne {φ : List (Binder n K)} {y v : Fin n} (h : v ≠ y) :
    bOf (eraseVar φ y) v = bOf φ v := by
  induction φ with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : c.var = y
    · rw [eraseVar_cons_eq hc, ih, bOf_cons_ne (fun e => h (e.symm.trans hc))]
    · rw [eraseVar_cons_ne hc]
      by_cases hcv : c.var = v
      · rw [bOf_cons_eq hcv, bOf_cons_eq hcv]
      · rw [bOf_cons_ne hcv, bOf_cons_ne hcv, ih]

theorem bOf_eraseVar_self (φ : List (Binder n K)) (y : Fin n) : bOf (eraseVar φ y) y = none :=
  bOf_eq_none (fun h => (mem_bvars_eraseVar.1 h).2 rfl)

theorem qOf_eraseVar_ne {φ : List (Binder n K)} {y v : Fin n} (h : v ≠ y) :
    qOf (eraseVar φ y) v = qOf φ v := by
  simp [qOf, bOf_eraseVar_ne h]

theorem qOf_eraseVar_self (φ : List (Binder n K)) (y : Fin n) : qOf (eraseVar φ y) y = none := by
  simp [qOf, bOf_eraseVar_self]

theorem qOf_eq_some {φ : List (Binder n K)} {v : Fin n} {q : Quant} :
    qOf φ v = some q ↔ ∃ b, bOf φ v = some b ∧ b.q = q := by
  simp [qOf]

theorem qOf_of_bOf {φ : List (Binder n K)} {v : Fin n} {b : Binder n K} (h : bOf φ v = some b) :
    qOf φ v = some b.q := by
  simp [qOf, h]

/-- Under nodup, the head binder is the binder of its variable, and erasing it gives the tail. -/
theorem eraseVar_head {b : Binder n K} {rest : List (Binder n K)} (h : (bvars (b :: rest)).Nodup) :
    eraseVar (b :: rest) b.var = rest := by
  rw [bvars_cons, nodup_cons_iff] at h
  rw [eraseVar_cons_eq rfl, eraseVar_of_not_mem h.1]

/-! ### Precedence -/

theorem precL_mem_left {l : List (Fin n)} {u v : Fin n} (h : precL l u v = true) : u ∈ l := by
  induction l with
  | nil => simp [precL] at h
  | cons x rest ih =>
    simp only [precL] at h
    by_cases hx : x = u
    · subst hx; exact List.mem_cons_self
    · rw [ite_eq_right hx] at h
      by_cases hxv : x = v
      · rw [ite_eq_left hxv] at h; cases h
      · rw [ite_eq_right hxv] at h; exact List.mem_cons_of_mem _ (ih h)

theorem precL_mem_right {l : List (Fin n)} {u v : Fin n} (h : precL l u v = true) : v ∈ l := by
  induction l with
  | nil => simp [precL] at h
  | cons x rest ih =>
    simp only [precL] at h
    by_cases hx : x = u
    · rw [ite_eq_left hx] at h; exact List.mem_cons_of_mem _ (List.contains_iff_mem.1 h)
    · rw [ite_eq_right hx] at h
      by_cases hxv : x = v
      · rw [ite_eq_left hxv] at h; cases h
      · rw [ite_eq_right hxv] at h; exact List.mem_cons_of_mem _ (ih h)

theorem precL_antisymm {l : List (Fin n)} {u v : Fin n} (huv : u ≠ v)
    (h1 : precL l u v = true) (h2 : precL l v u = true) : False := by
  induction l with
  | nil => simp [precL] at h1
  | cons x rest ih =>
    simp only [precL] at h1 h2
    by_cases hxu : x = u
    · rw [ite_eq_right (fun e => huv (hxu.symm.trans e)), ite_eq_left hxu] at h2; cases h2
    · by_cases hxv : x = v
      · rw [ite_eq_right hxu, ite_eq_left hxv] at h1; cases h1
      · rw [ite_eq_right hxu, ite_eq_right hxv] at h1
        rw [ite_eq_right hxv, ite_eq_right hxu] at h2
        exact ih h1 h2

theorem precL_total {l : List (Fin n)} {u v : Fin n} (huv : u ≠ v) (hu : u ∈ l) (hv : v ∈ l) :
    precL l u v = true ∨ precL l v u = true := by
  induction l with
  | nil => simp at hu
  | cons x rest ih =>
    simp only [precL]
    by_cases hxu : x = u
    · subst hxu
      rw [ite_eq_left rfl]
      left
      rcases List.mem_cons.1 hv with hv | hv
      · exact absurd hv.symm huv
      · exact List.contains_iff_mem.2 hv
    · by_cases hxv : x = v
      · subst hxv
        rw [ite_eq_right hxu, ite_eq_left rfl, ite_eq_left rfl]
        right
        rcases List.mem_cons.1 hu with hu | hu
        · exact absurd hu.symm hxu
        · exact List.contains_iff_mem.2 hu
      · rw [ite_eq_right hxu, ite_eq_right hxv, ite_eq_right hxv, ite_eq_right hxu]
        have hu' : u ∈ rest := (List.mem_cons.1 hu).resolve_left (fun e => hxu e.symm)
        have hv' : v ∈ rest := (List.mem_cons.1 hv).resolve_left (fun e => hxv e.symm)
        exact ih hu' hv'

theorem precL_head {x : Fin n} {rest : List (Fin n)} {v : Fin n} (hv : v ∈ rest) :
    precL (x :: rest) x v = true := by
  simp only [precL]; exact List.contains_iff_mem.2 hv

theorem precL_cons_ne {x : Fin n} {rest : List (Fin n)} {u v : Fin n} (hu : x ≠ u) (hv : x ≠ v) :
    precL (x :: rest) u v = precL rest u v := by
  simp [precL, hu, hv]

theorem precL_filter {l : List (Fin n)} {y u v : Fin n} (hu : u ≠ y) (hv : v ≠ y) :
    precL (l.filter (fun x => decide (x ≠ y))) u v = precL l u v := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    by_cases hxy : x = y
    · rw [List.filter_cons_of_neg (by simp [hxy]), ih]
      rw [precL_cons_ne (fun e => hu (e.symm.trans hxy)) (fun e => hv (e.symm.trans hxy))]
    · rw [List.filter_cons_of_pos (by simp [hxy])]
      simp only [precL]
      by_cases hxu : x = u
      · rw [ite_eq_left hxu, ite_eq_left hxu]
        have : (rest.filter (fun x => decide (x ≠ y))).contains v = rest.contains v := by
          rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_filter]
          simp [hv]
        exact this
      · rw [ite_eq_right hxu, ite_eq_right hxu]
        by_cases hxv : x = v
        · rw [ite_eq_left hxv, ite_eq_left hxv]
        · rw [ite_eq_right hxv, ite_eq_right hxv, ih]

theorem bvars_eraseVar (φ : List (Binder n K)) (y : Fin n) :
    bvars (eraseVar φ y) = (bvars φ).filter (fun x => decide (x ≠ y)) := by
  induction φ with
  | nil => rfl
  | cons b rest ih =>
    by_cases hb : b.var = y
    · rw [eraseVar_cons_eq hb, ih, bvars_cons, List.filter_cons_of_neg (by simp [hb])]
    · rw [eraseVar_cons_ne hb, bvars_cons, bvars_cons, ih,
        List.filter_cons_of_pos (by simp [hb])]

theorem precedes_eraseVar {φ : List (Binder n K)} {y u v : Fin n} (hu : u ≠ y) (hv : v ≠ y) :
    Precedes (eraseVar φ y) u v ↔ Precedes φ u v := by
  unfold Precedes; rw [bvars_eraseVar, precL_filter hu hv]

end Toy.ClaimStrength
