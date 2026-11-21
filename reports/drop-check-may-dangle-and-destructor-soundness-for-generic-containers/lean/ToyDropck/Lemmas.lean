import ToyDropck.Checker

/-!
# Auxiliary lemmas for the soundness theorems
-/

namespace Toy.Dropck

theorem observeAll_eq_true {L : Nat → Bool} :
    ∀ {vs : List Val}, observeAll L vs = true ↔ ∀ v ∈ vs, observe L v = true
  | [] => by simp [observeAll]
  | v :: vs => by simp [observeAll, observeAll_eq_true]

theorem dropAll_eq_true {beh : Nat → DropBehavior} {L : Nat → Bool} :
    ∀ {vs : List Val}, dropAll beh L vs = true ↔ ∀ v ∈ vs, dropVal beh L v = true
  | [] => by simp [dropAll]
  | v :: vs => by simp [dropAll, dropAll_eq_true]

theorem hasTyAll_eq_true {t : Ty} :
    ∀ {vs : List Val}, hasTyAll vs t = true ↔ ∀ v ∈ vs, hasTy v t = true
  | [] => by simp [hasTyAll]
  | v :: vs => by simp [hasTyAll, hasTyAll_eq_true]

theorem hasTy_int {v : Val} (h : hasTy v .int = true) : ∃ n, v = .int n := by
  cases v with
  | int n => exact ⟨n, rfl⟩
  | ref j => simp [hasTy] at h
  | obj c vs => simp [hasTy] at h

theorem hasTy_ref {v : Val} {k : Nat} (h : hasTy v (.ref k) = true) : v = .ref k := by
  cases v with
  | int n => simp [hasTy] at h
  | ref j => simp [hasTy] at h; rw [h]
  | obj c vs => simp [hasTy] at h

theorem hasTy_app {v : Val} {c : Nat} {t : Ty} (h : hasTy v (.app c t) = true) :
    ∃ vs, v = .obj c vs ∧ ∀ w ∈ vs, hasTy w t = true := by
  cases v with
  | int n => simp [hasTy] at h
  | ref j => simp [hasTy] at h
  | obj d vs =>
    simp only [hasTy, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨vs, by rw [h.1], hasTyAll_eq_true.mp h.2⟩

/-- Using a well-typed value whose type's lifetimes are all live is defined. -/
theorem observe_of_lifetimes_live {L : Nat → Bool} :
    ∀ (t : Ty) (v : Val), hasTy v t = true → (∀ j ∈ lifetimes t, L j = true) →
      observe L v = true
  | .int, v, hv, _ => by
    obtain ⟨n, rfl⟩ := hasTy_int hv
    simp [observe]
  | .ref k, v, hv, hl => by
    rw [hasTy_ref hv]
    simpa [observe, lifetimes] using hl
  | .app c t, v, hv, hl => by
    obtain ⟨vs, rfl, hvs⟩ := hasTy_app hv
    simp only [observe]
    exact observeAll_eq_true.mpr fun w hw =>
      observe_of_lifetimes_live t w (hvs w hw) (by simpa [lifetimes] using hl)

/-- Dropping a well-typed value whose type's lifetimes are all live is defined, whatever the
destructors do. -/
theorem dropVal_of_lifetimes_live {beh : Nat → DropBehavior} {L : Nat → Bool} :
    ∀ (t : Ty) (v : Val), hasTy v t = true → (∀ j ∈ lifetimes t, L j = true) →
      dropVal beh L v = true
  | .int, v, hv, _ => by
    obtain ⟨n, rfl⟩ := hasTy_int hv
    simp [dropVal]
  | .ref k, v, hv, _ => by
    rw [hasTy_ref hv]
    simp [dropVal]
  | .app c t, v, hv, hl => by
    obtain ⟨vs, rfl, hvs⟩ := hasTy_app hv
    have hl' : ∀ j ∈ lifetimes t, L j = true := by simpa [lifetimes] using hl
    have hobs : observeAll L vs = true := observeAll_eq_true.mpr fun w hw =>
      observe_of_lifetimes_live t w (hvs w hw) hl'
    have hdrop : dropAll beh L vs = true := dropAll_eq_true.mpr fun w hw =>
      dropVal_of_lifetimes_live t w (hvs w hw) hl'
    simp [dropVal, hobs, hdrop]

/-- Dropping a well-typed value whose type contains no `Drop` impl is defined. -/
theorem dropVal_of_deepHasNoDrop {impls : ImplTable} {L : Nat → Bool} :
    ∀ (t : Ty) (v : Val), hasTy v t = true → deepHasNoDrop impls t = true →
      dropVal (behOf impls) L v = true
  | .int, v, hv, _ => by
    obtain ⟨n, rfl⟩ := hasTy_int hv
    simp [dropVal]
  | .ref k, v, hv, _ => by
    rw [hasTy_ref hv]
    simp [dropVal]
  | .app c t, v, hv, hd => by
    obtain ⟨vs, rfl, hvs⟩ := hasTy_app hv
    simp only [deepHasNoDrop, Bool.and_eq_true, Bool.not_eq_true'] at hd
    have hdrop : dropAll (behOf impls) L vs = true := dropAll_eq_true.mpr fun w hw =>
      dropVal_of_deepHasNoDrop t w (hvs w hw) hd.2
    simp [dropVal, behOf, hd.1, hdrop]

/-- The core single-drop lemma. It covers the policy `ownsRecurse` under `OwnsDeclared`, the
policy `deepNoDrop`, and every policy when no `#[may_dangle]` impl drops its elements. -/
theorem dropVal_of_dropckP {pol : DanglePolicy} {impls : ImplTable} {ok L : Nat → Bool} {n : Nat}
    (hpol : (pol = .ownsRecurse ∧ ∀ c, OwnsDeclared (impls c)) ∨ pol = .deepNoDrop ∨
      (∀ c, MayDangleDropsNothing (impls c)))
    (hmd : ∀ c, MayDangleHonest (impls c)) (hglue : ∀ c, GlueVisible (impls c))
    (hokL : ∀ j, j < n → ok j = true → L j = true) :
    ∀ (t : Ty) (v : Val), hasTy v t = true → (∀ j ∈ lifetimes t, j < n) →
      dropckP pol impls ok t = true → dropVal (behOf impls) L v = true
  | .int, v, hv, _, _ => by
    obtain ⟨m, rfl⟩ := hasTy_int hv
    simp [dropVal]
  | .ref k, v, hv, _, _ => by
    rw [hasTy_ref hv]
    simp [dropVal]
  | .app c t, v, hv, hn, hck => by
    obtain ⟨vs, rfl, hvs⟩ := hasTy_app hv
    have hn' : ∀ j ∈ lifetimes t, j < n := by simpa [lifetimes] using hn
    have ih : dropckP pol impls ok t = true → dropAll (behOf impls) L vs = true := fun h =>
      dropAll_eq_true.mpr fun w hw => dropVal_of_dropckP hpol hmd hglue hokL t w (hvs w hw) hn' h
    have hmdc := hmd c
    have hgluec := hglue c
    unfold MayDangleHonest at hmdc
    unfold GlueVisible at hgluec
    cases hD : (impls c).beh.hasDrop <;> cases hM : (impls c).decl.mayDangle
    · -- no `Drop` impl
      simp only [dropckP, hD, hM, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.true_or, Bool.true_and] at hck
      cases hE : (impls c).beh.dropsElems
      · simp [dropVal, behOf, hD, hE]
      · have hO := hgluec hD hE
        simp only [hO, Bool.not_true, Bool.false_or] at hck
        simp [dropVal, behOf, hD, hE, ih hck]
    · simp only [dropckP, hD, hM, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.true_or, Bool.true_and] at hck
      cases hE : (impls c).beh.dropsElems
      · simp [dropVal, behOf, hD, hE]
      · have hO := hgluec hD hE
        simp only [hO, Bool.not_true, Bool.false_or] at hck
        simp [dropVal, behOf, hD, hE, ih hck]
    · -- strict `Drop` impl: every lifetime of `t` strictly outlives the drop
      simp only [dropckP, hD, hM, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hck
      exact dropVal_of_lifetimes_live (.app c t) _ hv fun j hj =>
        hokL j (hn j hj) (hck.1 j (by simpa [lifetimes] using hj))
    · -- `may_dangle` impl
      have hU := hmdc hD hM
      cases hE : (impls c).beh.dropsElems
      · simp [dropVal, behOf, hD, hU, hE]
      · rcases hpol with ⟨rfl, hown⟩ | rfl | hnd
        · have hO := hown c hD hM hE
          simp only [dropckP, hD, hM, Bool.and_self, ↓reduceIte, hO, Bool.not_true,
            Bool.false_or] at hck
          simp [dropVal, behOf, hD, hU, hE, ih hck]
        · simp only [dropckP, hD, hM, Bool.and_self, ↓reduceIte, Bool.or_eq_true] at hck
          rcases hck with hck | hck
          · have hdrop : dropAll (behOf impls) L vs = true := dropAll_eq_true.mpr fun w hw =>
              dropVal_of_deepHasNoDrop t w (hvs w hw) hck
            simp [dropVal, behOf, hD, hU, hE, hdrop]
          · rw [List.all_eq_true] at hck
            exact dropVal_of_lifetimes_live (.app c t) _ hv fun j hj =>
              hokL j (hn j hj) (hck j (by simpa [lifetimes] using hj))
        · have h := hnd c hD hM
          rw [hE] at h
          cases h

theorem takeWhile_ne_append_of_not_mem (k : Nat) :
    ∀ (pre ks : List Nat), k ∉ pre → (pre ++ k :: ks).takeWhile (· != k) = pre
  | [], ks, _ => by simp
  | a :: pre, ks, h => by
    have hak : a ≠ k := fun hak => h (by simp [hak])
    have hk : k ∉ pre := fun hk => h (List.mem_cons_of_mem a hk)
    simp [hak, takeWhile_ne_append_of_not_mem k pre ks hk]

theorem acceptsFrom_getElem? {pol : DanglePolicy} {impls : ImplTable} {ord : List Nat} :
    ∀ (l : List (Ty × Val)) (i0 : Nat), acceptsFrom pol impls ord i0 l = true →
      ∀ (i : Nat) (t : Ty) (v : Val), l[i]? = some (t, v) → ord.contains (i0 + i) = true →
        dropckP pol impls (outlives ord (i0 + i)) t = true
  | [], _, _, i, t, v, hget, _ => by simp at hget
  | (t', v') :: rest, i0, hacc, i, t, v, hget, hc => by
    simp only [acceptsFrom, Bool.and_eq_true] at hacc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
      obtain ⟨rfl, rfl⟩ := hget
      simp only [Nat.add_zero] at hc ⊢
      simp only [hc, Bool.not_true, Bool.false_or] at hacc
      exact hacc.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      have e : i0 + (i + 1) = i0 + 1 + i := by omega
      rw [e] at hc ⊢
      exact acceptsFrom_getElem? rest (i0 + 1) hacc.2 i t v hget hc

theorem typed_getElem? {p : Prog} (hval : ValuesHaveTypes p) (hscope : LifetimesInScope p)
    {k : Nat} {t : Ty} {v : Val} (h : p.locals[k]? = some (t, v)) :
    hasTy v t = true ∧ ∀ j ∈ lifetimes t, j < p.locals.length := by
  unfold ValuesHaveTypes at hval
  unfold LifetimesInScope at hscope
  rw [List.all_eq_true] at hval hscope
  have hmem : (t, v) ∈ p.locals := List.mem_of_getElem? h
  have h2 := hscope _ hmem
  simp only [List.all_eq_true, decide_eq_true_eq] at h2
  exact ⟨hval _ hmem, h2⟩

/-- The drop loop never reaches undefined behaviour if each individual drop of a local `k` is
defined whenever every existing local that strictly outlives it lies outside `k :: dead`. -/
theorem runDrops_of_each {beh : Nat → DropBehavior} {p : Prog} {ord : List Nat}
    (hone : ∀ (k : Nat) (t : Ty) (v : Val) (dead : List Nat), p.locals[k]? = some (t, v) →
      ord.contains k = true →
      (∀ j, outlives ord k j = true → j < p.locals.length → j ∉ k :: dead) →
      dropVal beh (live p.locals.length (k :: dead)) v = true) :
    ∀ (ks pre dead : List Nat), ord = pre ++ ks →
      (∀ j, j ∈ dead ↔ (j ∈ pre ∧ j < p.locals.length)) → runDrops beh p ks dead = true
  | [], _, _, _, _ => by simp [runDrops]
  | k :: ks, pre, dead, hord, hdead => by
    have hrest : ord = (pre ++ [k]) ++ ks := by simp [hord]
    by_cases hk : dead.contains k = true
    · simp only [runDrops, hk, ↓reduceIte]
      refine runDrops_of_each hone ks (pre ++ [k]) dead hrest fun j => ?_
      have hkd : k ∈ dead := by simpa using hk
      constructor
      · intro hj
        have := (hdead j).mp hj
        exact ⟨List.mem_append_left _ this.1, this.2⟩
      · rintro ⟨hj, hjn⟩
        rcases List.mem_append.mp hj with hj | hj
        · exact (hdead j).mpr ⟨hj, hjn⟩
        · simp at hj; rw [hj]; exact hkd
    · have hk' : dead.contains k = false := by simpa using hk
      have hkd : k ∉ dead := by simpa using hk
      simp only [runDrops, hk', Bool.false_eq_true, ↓reduceIte]
      cases hget : p.locals[k]? with
      | none =>
        have hkn : ¬ k < p.locals.length := by
          intro hlt; rw [List.getElem?_eq_getElem hlt] at hget; cases hget
        refine runDrops_of_each hone ks (pre ++ [k]) dead hrest fun j => ?_
        constructor
        · intro hj
          have := (hdead j).mp hj
          exact ⟨List.mem_append_left _ this.1, this.2⟩
        · rintro ⟨hj, hjn⟩
          rcases List.mem_append.mp hj with hj | hj
          · exact (hdead j).mpr ⟨hj, hjn⟩
          · simp at hj; subst hj; exact absurd hjn hkn
      | some e =>
        obtain ⟨t, v⟩ := e
        have hkn : k < p.locals.length := by
          rcases Nat.lt_or_ge k p.locals.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hget; cases hget
        have hkpre : k ∉ pre := fun hkp => hkd ((hdead k).mpr ⟨hkp, hkn⟩)
        have hone' := hone k t v dead hget (by simp [hord]) fun j hj hjn hjd => by
          simp only [outlives, hord, takeWhile_ne_append_of_not_mem k pre ks hkpre,
            Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hj
          have hjnp : j ∉ pre := by simpa using hj.2
          rcases List.mem_cons.mp hjd with hjk | hjd'
          · exact hj.1 hjk
          · exact hjnp ((hdead j).mp hjd').1
        simp only [hone', Bool.true_and]
        refine runDrops_of_each hone ks (pre ++ [k]) (k :: dead) hrest fun j => ?_
        constructor
        · intro hj
          rcases List.mem_cons.mp hj with hj | hj
          · subst hj; exact ⟨by simp, hkn⟩
          · have := (hdead j).mp hj
            exact ⟨List.mem_append_left _ this.1, this.2⟩
        · rintro ⟨hj, hjn⟩
          rcases List.mem_append.mp hj with hj | hj
          · exact List.mem_cons_of_mem _ ((hdead j).mpr ⟨hj, hjn⟩)
          · simp at hj; subst hj; exact List.mem_cons_self

/-- Soundness of a checker policy from the core single-drop lemma. It covers the policy
`ownsRecurse` under `OwnsDeclared`, the policy `deepNoDrop`, and every policy when no
`#[may_dangle]` impl drops its elements. -/
theorem dropSafe_of_acceptsP {pol : DanglePolicy} {impls : ImplTable} {ord : List Nat} {p : Prog}
    (hpol : (pol = .ownsRecurse ∧ ∀ c, OwnsDeclared (impls c)) ∨ pol = .deepNoDrop ∨
      (∀ c, MayDangleDropsNothing (impls c)))
    (hmd : ∀ c, MayDangleHonest (impls c)) (hglue : ∀ c, GlueVisible (impls c))
    (hval : ValuesHaveTypes p) (hscope : LifetimesInScope p)
    (hacc : acceptsP pol impls ord p = true) : DropSafe impls ord p := by
  unfold DropSafe
  refine runDrops_of_each (beh := behOf impls) (p := p) (ord := ord)
    (fun k t v dead hget hc hout => ?_) ord [] [] (by simp) (by simp)
  obtain ⟨hv, hn⟩ := typed_getElem? hval hscope hget
  have hck := acceptsFrom_getElem? p.locals 0 hacc k t v hget (by simpa using hc)
  simp only [Nat.zero_add] at hck
  refine dropVal_of_dropckP hpol hmd hglue (n := p.locals.length) (fun j hjn hok => ?_) t v hv hn hck
  have := hout j hok hjn
  simp only [List.mem_cons, not_or] at this
  simp [live, hjn, this.1, this.2]

/-- The drop loop does not read declarations (`DropDecl`), so erasing `may_dangle` annotations does
not change it. -/
theorem dropSafe_stripDangle (impls : ImplTable) (ord : List Nat) (p : Prog) :
    DropSafe (stripDangle impls) ord p ↔ DropSafe impls ord p := Iff.rfl

end Toy.Dropck
