import ToyZc.Union

/-!
# Proof support: induction over descriptions and list-level facts

Auxiliary lemmas used by the proofs of the result groups 2, 3, 5 and the closure results. None of
them is a result card of the package.
-/

namespace Toy.Zc

/-- Induction over descriptions, with the induction hypothesis available for every element of the
nested field and variant lists. -/
theorem Desc.induct' (P : Desc → Prop)
    (hint : ∀ t, P (.int t)) (hbool : P .bool)
    (harr : ∀ e n, P e → P (.array e n))
    (hstrct : ∀ r fs, (∀ f ∈ fs, P f) → P (.strct r fs))
    (henm : ∀ r vs, (∀ v ∈ vs, ∀ f ∈ v.2, P f) → P (.enm r vs))
    (hunion : ∀ r fs, (∀ f ∈ fs, P f) → P (.union r fs))
    (hcell : ∀ t, P t → P (.cell t)) : ∀ d, P d := fun d =>
  @Desc.rec P (fun fs => ∀ f ∈ fs, P f) (fun vs => ∀ v ∈ vs, ∀ f ∈ v.2, P f)
    (fun v => ∀ f ∈ v.2, P f) hint hbool harr hstrct henm hunion hcell
    (fun _ h => nomatch h)
    (fun f fs ihf ihfs g hg => by
      cases hg with
      | head => exact ihf
      | tail _ h => exact ihfs g h)
    (fun _ h => nomatch h)
    (fun v vs ihv ihvs w hw => by
      cases hw with
      | head => exact ihv
      | tail _ h => exact ihvs w h)
    (fun _ _ ih => ih) d

/-! ## Arithmetic of `alignUp` and `roundDown` -/

theorem roundDown_le (x a : Nat) : roundDown x a ≤ x := by
  unfold roundDown
  split
  · exact Nat.zero_le x
  · exact Nat.div_mul_le_self x a

theorem dvd_roundDown (x a : Nat) : a ∣ roundDown x a := by
  unfold roundDown
  split
  · rename_i ha
    subst ha
    exact Nat.dvd_refl 0
  · exact ⟨x / a, Nat.mul_comm _ _⟩

theorem dvd_sub_of_dvd {a x y : Nat} (hx : a ∣ x) (hy : a ∣ y) : a ∣ x - y := by
  rcases hx with ⟨p, rfl⟩
  rcases hy with ⟨q, rfl⟩
  exact ⟨p - q, (Nat.mul_sub_left_distrib a p q).symm⟩

theorem dvd_alignUp {x a : Nat} (ha : 0 < a) : a ∣ alignUp x a := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  unfold alignUp paddingNeeded
  simp only [ha0, ↓reduceIte]
  split
  · rename_i hr
    simp only [Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero hr
  · rename_i hr
    have hlt : x % a < a := Nat.mod_lt x ha
    have hdiv := Nat.div_add_mod x a
    refine ⟨x / a + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem alignUp_le_of_dvd {x a m : Nat} (ha : 0 < a) (hm : a ∣ m) (hxm : x ≤ m) :
    alignUp x a ≤ m := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  rcases hm with ⟨q, rfl⟩
  unfold alignUp paddingNeeded
  simp only [ha0, ↓reduceIte]
  split
  · omega
  · rename_i hr
    have hdiv := Nat.div_add_mod x a
    have hlt : x % a < a := Nat.mod_lt x ha
    have hq : x / a < q := by
      rcases Nat.lt_or_ge (x / a) q with h1 | h1
      · exact h1
      · exfalso
        have hge : a * q ≤ a * (x / a) := Nat.mul_le_mul_left a h1
        omega
    have hq1 : x / a + 1 ≤ q := hq
    have hmul : a * (x / a + 1) ≤ a * q := Nat.mul_le_mul_left a hq1
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

theorem alignUp_le_iff_le_roundDown {x L a : Nat} (ha : 0 < a) :
    alignUp x a ≤ L ↔ x ≤ roundDown L a := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  constructor
  · intro h
    rcases dvd_alignUp (x := x) ha with ⟨q, hq⟩
    have hqL : q * a ≤ L := by rw [Nat.mul_comm, ← hq]; exact h
    have hqd : q ≤ L / a := (Nat.le_div_iff_mul_le ha).mpr hqL
    have hmul : q * a ≤ (L / a) * a := Nat.mul_le_mul_right a hqd
    have hx : x ≤ q * a := by
      rw [Nat.mul_comm, ← hq]
      exact le_alignUp x a
    unfold roundDown
    simp only [ha0, ↓reduceIte]
    exact Nat.le_trans hx hmul
  · intro h
    have hm : a ∣ roundDown L a := dvd_roundDown L a
    exact Nat.le_trans (alignUp_le_of_dvd ha hm h) (roundDown_le L a)

theorem alignUp_phase_eq {p a : Nat} (ha : 0 < a) (hp : p ≤ a) :
    alignUp p a = if p = 0 then 0 else a := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  by_cases hp0 : p = 0
  · subst hp0
    simp [alignUp, paddingNeeded, ha0]
  · simp only [hp0, ↓reduceIte]
    rcases Nat.eq_or_lt_of_le hp with rfl | hlt
    · simp [alignUp, paddingNeeded, ha0]
    · have hmod : p % a = p := Nat.mod_eq_of_lt hlt
      unfold alignUp paddingNeeded
      simp only [ha0, ↓reduceIte, hmod, hp0]
      omega

theorem roundDown_add_mul_self (y c a : Nat) (ha : 0 < a) :
    roundDown (y + c * a) a = roundDown y a + c * a := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  unfold roundDown
  simp only [ha0, ↓reduceIte]
  rw [Nat.add_mul_div_right y c ha, Nat.add_mul]

theorem sub_roundDown_eq_alignUp {x u m a : Nat} (ha : 0 < a) (hm : a ∣ m) (hxu : x + u = m) :
    m - roundDown u a = alignUp x a := by
  apply Nat.le_antisymm
  · have hxm : x ≤ m := by omega
    have hax_le_m : alignUp x a ≤ m := alignUp_le_of_dvd ha hm hxm
    have hdvd_diff : a ∣ m - alignUp x a := dvd_sub_of_dvd hm (dvd_alignUp ha)
    have hle_u : m - alignUp x a ≤ u := by
      have hx_le : x ≤ alignUp x a := le_alignUp x a
      omega
    have hle_rd : m - alignUp x a ≤ roundDown u a := by
      have h1 : alignUp (m - alignUp x a) a ≤ u := by
        have heq : alignUp (m - alignUp x a) a = m - alignUp x a :=
          Nat.le_antisymm (alignUp_le_of_dvd ha hdvd_diff (Nat.le_refl _)) (le_alignUp _ _)
        omega
      exact (alignUp_le_iff_le_roundDown ha).mp h1
    omega
  · have hrd_le : roundDown u a ≤ u := roundDown_le u a
    have hx_le : x ≤ m - roundDown u a := by omega
    have hdvd_diff : a ∣ m - roundDown u a := dvd_sub_of_dvd hm (dvd_roundDown u a)
    exact alignUp_le_of_dvd ha hdvd_diff hx_le

theorem alignUp_add_mul (x q a : Nat) (ha : 0 < a) :
    alignUp (x + q * a) a = alignUp x a + q * a := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hm : (x + q * a) % a = x % a := Nat.add_mul_mod_self_right x q a
  unfold alignUp paddingNeeded
  simp only [ha0, ↓reduceIte, hm]
  split <;> omega

theorem alignUp_eq_of_dvd {x a : Nat} (h : a ∣ x) : alignUp x a = x := by
  unfold alignUp paddingNeeded
  split
  · rfl
  · simp [Nat.mod_eq_zero_of_dvd h]

theorem alignUp_zero_left (a : Nat) : alignUp 0 a = 0 := by
  unfold alignUp paddingNeeded
  split <;> simp

theorem alignUp_one (x : Nat) : alignUp x 1 = x := alignUp_eq_of_dvd (Nat.one_dvd x)

theorem alignUp_zero_right (x : Nat) : alignUp x 0 = x := by
  simp [alignUp, paddingNeeded]

/-! ## Initialized byte lists -/

theorem exists_map_init_of_forall_isInit : ∀ (l : List AB), (∀ b ∈ l, b.isInit = true) →
    ∃ bs : List Byte, l = bs.map AByte.init
  | [], _ => ⟨[], rfl⟩
  | .uninit :: _, h => absurd (h _ List.mem_cons_self) (by simp)
  | .init d :: l, h => by
    obtain ⟨bs, hbs⟩ := exists_map_init_of_forall_isInit l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact ⟨d :: bs, by simp [hbs]⟩

theorem forall_isInit_of_getD {l : List AB} {n : Nat} (hlen : l.length = n)
    (h : ∀ i, i < n → (l.getD i .uninit).isInit = true) : ∀ b ∈ l, b.isInit = true := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have := h i (hlen ▸ hi)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem encodeL_forall_isInit {d : Desc} (hI : SemIntoBytes d) {v : Val} (hv : d.hasType v = true) :
    ∀ b ∈ d.encodeL v, b.isInit = true :=
  forall_isInit_of_getD (encodeL_length d v) ((semIntoBytes_iff_encodeL_init d).mp hI v hv)

theorem fit_eq_take {n : Nat} {l : List AB} (h : n ≤ l.length) : fit n l = l.take n := by
  unfold fit
  exact List.take_append_of_le_length h

/-! ## `mapM` in `Option` -/

theorem mapM_option_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (vs : List β),
    l.mapM f = some vs → vs.length = l.length ∧ ∀ v ∈ vs, ∃ a ∈ l, f a = some v
  | [], vs, h => by
    simp at h; subst h; simp
  | a :: l, vs, h => by
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp [hfa, hl] at h
        subst h
        obtain ⟨h1, h2⟩ := mapM_option_some f l bs hl
        refine ⟨by simp [h1], ?_⟩
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ⟨a, List.mem_cons_self, hfa⟩
        · obtain ⟨a', ha', hfa'⟩ := h2 v hv
          exact ⟨a', List.mem_cons_of_mem _ ha', hfa'⟩

theorem mapM_option_isSome {α β : Type} (f : α → Option β) : ∀ (l : List α),
    (l.mapM f).isSome = true ↔ ∀ a ∈ l, (f a).isSome = true
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, List.mem_cons, forall_eq_or_imp]
    rw [← mapM_option_isSome f l]
    cases f a <;> cases l.mapM f <;> simp

/-! ## Decoding produces well-typed values -/

theorem allInit_length : ∀ (x : List AB) (bs : List Byte), allInit x = some bs → bs.length = x.length
  | [], bs, h => by simp [allInit] at h; subst h; rfl
  | .uninit :: _, bs, h => by simp [allInit] at h
  | .init d :: xs, bs, h => by
    simp only [allInit] at h
    cases hx : allInit xs with
    | none => simp [hx] at h
    | some cs =>
      simp [hx] at h
      subst h
      simp [allInit_length xs cs hx]

theorem decodeFields_hasTypes (P : Desc → Prop)
    (hP : ∀ f, P f ↔ ∀ x v, f.decodeL x = some v → f.hasType v = true) :
    ∀ (fs : List Desc), (∀ f ∈ fs, P f) → ∀ (os : List Nat) (x : List AB) (vs : List Val),
      Desc.decodeFields fs os x = some vs → Desc.hasTypes fs vs = true
  | [], _, os, x, vs, h => by
    simp [Desc.decodeFields] at h; subst h; simp [Desc.hasTypes]
  | f :: fs, ih, [], x, vs, h => by simp [Desc.decodeFields] at h
  | f :: fs, ih, o :: os, x, vs, h => by
    simp only [Desc.decodeFields] at h
    cases hf : f.decodeL (slice x o f.size) with
    | none => simp [hf] at h
    | some v =>
      cases hfs : Desc.decodeFields fs os x with
      | none => simp [hf, hfs] at h
      | some ws =>
        simp [hf, hfs] at h
        subst h
        simp only [Desc.hasTypes, Bool.and_eq_true]
        exact ⟨(hP f).mp (ih f List.mem_cons_self) _ _ hf,
          decodeFields_hasTypes P hP fs (fun g hg => ih g (List.mem_cons_of_mem _ hg)) os x ws hfs⟩

theorem decodeVariant_hasTypeVariant (P : Desc → Prop)
    (hP : ∀ f, P f ↔ ∀ x v, f.decodeL x = some v → f.hasType v = true) :
    ∀ (vs : List (DiscrSyn × List Desc)), (∀ v ∈ vs, ∀ f ∈ v.2, P f) →
      ∀ (i : Nat) (oss : List (List Nat)) (x : List AB) (fvs : List Val),
      Desc.decodeVariant vs i oss x = some fvs → Desc.hasTypeVariant vs i fvs = true
  | [], _, i, oss, x, fvs, h => by simp [Desc.decodeVariant] at h
  | (_, fs) :: vs, ih, 0, [], x, fvs, h => by simp [Desc.decodeVariant] at h
  | (_, fs) :: vs, ih, 0, os :: oss, x, fvs, h => by
    simp only [Desc.decodeVariant] at h
    simp only [Desc.hasTypeVariant]
    exact decodeFields_hasTypes P hP fs (ih _ List.mem_cons_self) os x fvs h
  | (_, fs) :: vs, ih, i + 1, [], x, fvs, h => by simp [Desc.decodeVariant] at h
  | (_, fs) :: vs, ih, i + 1, _ :: oss, x, fvs, h => by
    simp only [Desc.decodeVariant] at h
    simp only [Desc.hasTypeVariant]
    exact decodeVariant_hasTypeVariant P hP vs (fun v hv => ih v (List.mem_cons_of_mem _ hv)) i oss x
      fvs h

theorem decodeField_hasTypeField (P : Desc → Prop)
    (hP : ∀ f, P f ↔ ∀ x v, f.decodeL x = some v → f.hasType v = true) :
    ∀ (fs : List Desc), (∀ f ∈ fs, P f) → ∀ (j : Nat) (x : List AB) (u : Val),
      Desc.decodeField fs j x = some u → ∃ k w, u = .union (j + k) w ∧ Desc.hasTypeField fs k w = true
  | [], _, j, x, u, h => by simp [Desc.decodeField] at h
  | f :: fs, ih, j, x, u, h => by
    simp only [Desc.decodeField] at h
    cases hf : f.decodeL (x.take f.size) with
    | some v =>
      simp [hf] at h
      subst h
      exact ⟨0, v, rfl, by simpa [Desc.hasTypeField] using (hP f).mp (ih f List.mem_cons_self) _ _ hf⟩
    | none =>
      simp [hf] at h
      obtain ⟨k, w, hu, hw⟩ := decodeField_hasTypeField P hP fs
        (fun g hg => ih g (List.mem_cons_of_mem _ hg)) (j + 1) x u h
      exact ⟨k + 1, w, by rw [hu]; congr 1; omega, by simpa [Desc.hasTypeField] using hw⟩

theorem decodeL_hasType : ∀ (d : Desc) (x : List AB) (v : Val), d.decodeL x = some v →
    d.hasType v = true := by
  refine Desc.induct' (fun d => ∀ x v, d.decodeL x = some v → d.hasType v = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x v h
    simp only [Desc.decodeL] at h
    split at h
    · rename_i hl
      cases ha : allInit x with
      | none => simp [ha] at h
      | some bs =>
        simp [ha] at h
        subst h
        simp [Desc.hasType, allInit_length x bs ha, hl]
    · cases h
  · intro x v h
    simp only [Desc.decodeL] at h
    split at h
    · split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · cases h
    · cases h
  · intro e n ih x v h
    simp only [Desc.decodeL] at h
    split at h
    · cases hm : (List.range n).mapM (fun k => e.decodeL (slice x (k * e.size) e.size)) with
      | none => simp [hm] at h
      | some vs =>
        simp [hm] at h
        subst h
        obtain ⟨h1, h2⟩ := mapM_option_some _ _ _ hm
        simp only [Desc.hasType, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        refine ⟨by simpa using h1, fun w hw => ?_⟩
        obtain ⟨k, _, hk⟩ := h2 w hw
        exact ih _ _ hk
    · cases h
  · intro r fs ih x v h
    simp only [Desc.decodeL] at h
    split at h
    · cases hd : Desc.decodeFields fs (r.layout (Desc.layouts fs)).offsets x with
      | none => simp [hd] at h
      | some vs =>
        simp [hd] at h
        subst h
        simp only [Desc.hasType]
        exact decodeFields_hasTypes (fun f => ∀ x v, f.decodeL x = some v → f.hasType v = true)
          (fun _ => Iff.rfl) fs ih _ x vs hd
    · cases h
  · intro r vs ih x v h
    simp only [Desc.decodeL] at h
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i i _
          cases hd : Desc.decodeVariant vs i (r.layout (Desc.variantLayouts vs)).variantFieldOffsets x with
          | none => simp [hd] at h
          | some fvs =>
            simp [hd] at h
            subst h
            simp only [Desc.hasType]
            exact decodeVariant_hasTypeVariant
              (fun f => ∀ x v, f.decodeL x = some v → f.hasType v = true) (fun _ => Iff.rfl) vs ih
              i _ x fvs hd
    · cases h
  · intro r fs ih x v h
    simp only [Desc.decodeL] at h
    split at h
    · obtain ⟨k, w, rfl, hw⟩ := decodeField_hasTypeField
        (fun f => ∀ x v, f.decodeL x = some v → f.hasType v = true) (fun _ => Iff.rfl) fs ih 0 x v h
      simpa [Desc.hasType] using hw
    · cases h
  · intro t ih x v h
    exact ih x v h

theorem validInit_eq_isSome (d : Desc) (bs : List Byte) :
    validInit d bs = (d.decodeL (bs.map AByte.init)).isSome := by
  unfold validInit
  cases h : d.decodeL (bs.map AByte.init) with
  | none => rfl
  | some v => simp [decodeL_hasType d _ v h]

/-! ## `writeAt` -/

theorem getD_writeAt : ∀ (buf : List AB) (o : Nat) (src : List AB) (p : Nat),
    (writeAt buf o src).getD p .uninit =
      if o ≤ p ∧ p < o + src.length ∧ p < buf.length then src.getD (p - o) .uninit
      else buf.getD p .uninit
  | buf, o, [], p => by
    have : ¬ (o ≤ p ∧ p < o + 0 ∧ p < buf.length) := by omega
    simp [writeAt]
    omega
  | [], o, s :: ss, p => by simp [writeAt]
  | b :: bs, 0, s :: ss, 0 => by simp [writeAt]
  | b :: bs, 0, s :: ss, q + 1 => by
    simp only [writeAt, List.getD_cons_succ, List.length_cons]
    rw [getD_writeAt bs 0 ss q]
    by_cases h : q < ss.length ∧ q < bs.length
    · have h1 : 0 ≤ q ∧ q < 0 + ss.length ∧ q < bs.length := by omega
      have h2 : 0 ≤ q + 1 ∧ q + 1 < 0 + (ss.length + 1) ∧ q + 1 < bs.length + 1 := by omega
      simp only [h1, h2, and_self, ↓reduceIte, Nat.sub_zero, List.getD_cons_succ]
    · have h1 : ¬ (0 ≤ q ∧ q < 0 + ss.length ∧ q < bs.length) := by omega
      have h2 : ¬ (0 ≤ q + 1 ∧ q + 1 < 0 + (ss.length + 1) ∧ q + 1 < bs.length + 1) := by omega
      simp only [h1, h2, ↓reduceIte]
  | b :: bs, n + 1, s :: ss, 0 => by simp [writeAt]
  | b :: bs, n + 1, s :: ss, q + 1 => by
    simp only [writeAt, List.getD_cons_succ, List.length_cons]
    rw [getD_writeAt bs n (s :: ss) q]
    by_cases h : n ≤ q ∧ q < n + (ss.length + 1) ∧ q < bs.length
    · have h2 : n + 1 ≤ q + 1 ∧ q + 1 < n + 1 + (ss.length + 1) ∧ q + 1 < bs.length + 1 := by omega
      simp only [List.length_cons, h, h2, and_self, ↓reduceIte]
      congr 1
      omega
    · have h2 : ¬ (n + 1 ≤ q + 1 ∧ q + 1 < n + 1 + (ss.length + 1) ∧ q + 1 < bs.length + 1) := by
        omega
      simp only [List.length_cons, h, h2, ↓reduceIte]

theorem getD_writeAt_of_lt {buf src : List AB} {o p : Nat} (h : p < o) :
    (writeAt buf o src).getD p .uninit = buf.getD p .uninit := by
  rw [getD_writeAt]
  have : ¬ (o ≤ p ∧ p < o + src.length ∧ p < buf.length) := by omega
  simp [this]

theorem getD_writeAt_of_ge {buf src : List AB} {o p : Nat} (h : o + src.length ≤ p) :
    (writeAt buf o src).getD p .uninit = buf.getD p .uninit := by
  rw [getD_writeAt]
  have : ¬ (o ≤ p ∧ p < o + src.length ∧ p < buf.length) := by omega
  simp [this]

theorem getD_writeAt_of_mem {buf src : List AB} {o p : Nat} (h1 : o ≤ p) (h2 : p < o + src.length)
    (h3 : p < buf.length) :
    (writeAt buf o src).getD p .uninit = src.getD (p - o) .uninit := by
  rw [getD_writeAt]
  simp [h1, h2, h3]

/-! ## `placeFields` -/

theorem placeFields_cons (m : ReprModifier) (c : Nat) (l : FieldLayout) (ls : List FieldLayout) :
    placeFields m c (l :: ls) =
      (alignUp c (effFieldAlign m l.align) ::
          (placeFields m (alignUp c (effFieldAlign m l.align) + l.size) ls).1,
        (placeFields m (alignUp c (effFieldAlign m l.align) + l.size) ls).2) := rfl

theorem placeFields_end_ge (m : ReprModifier) : ∀ (ls : List FieldLayout) (c : Nat),
    c + (ls.map FieldLayout.size).sum ≤ (placeFields m c ls).2
  | [], c => by simp [placeFields]
  | l :: ls, c => by
    rw [placeFields_cons]
    have := placeFields_end_ge m ls (alignUp c (effFieldAlign m l.align) + l.size)
    have := le_alignUp c (effFieldAlign m l.align)
    simp only [List.map_cons, List.sum_cons]
    omega

theorem layouts_cons (f : Desc) (fs : List Desc) : Desc.layouts (f :: fs) = f.layout :: Desc.layouts fs :=
  rfl

theorem layouts_map_size (fs : List Desc) : (Desc.layouts fs).map FieldLayout.size = fs.map Desc.size := by
  rw [Desc.layouts_eq_map, List.map_map]
  rfl

/-! ## Field writes and reads along a `placeFields` placement -/

theorem writeFields_length : ∀ (fs : List Desc) (os : List Nat) (vs : List Val) (buf : List AB),
    (Desc.writeFields fs os vs buf).length = buf.length
  | [], _, _, _ => by simp [Desc.writeFields]
  | _ :: _, [], _, _ => by simp [Desc.writeFields]
  | _ :: _, _ :: _, [], _ => by simp [Desc.writeFields]
  | f :: fs, o :: os, v :: vs, buf => by
    simp only [Desc.writeFields]
    rw [writeFields_length fs os vs, writeAt_length]

theorem writeFields_getD_lt (m : ReprModifier) : ∀ (fs : List Desc) (c : Nat) (vs : List Val)
    (buf : List AB) (p : Nat), p < c →
    (Desc.writeFields fs (placeFields m c (Desc.layouts fs)).1 vs buf).getD p .uninit =
      buf.getD p .uninit
  | [], c, vs, buf, p, _ => by simp [Desc.writeFields]
  | f :: fs, c, [], buf, p, _ => by
    rw [layouts_cons, placeFields_cons]
    simp [Desc.writeFields]
  | f :: fs, c, v :: vs, buf, p, h => by
    rw [layouts_cons, placeFields_cons]
    simp only [Desc.writeFields]
    have := le_alignUp c (effFieldAlign m f.layout.align)
    rw [writeFields_getD_lt m fs _ vs _ p (by omega)]
    exact getD_writeAt_of_lt (by omega)

theorem writeFields_getD_ge (m : ReprModifier) : ∀ (fs : List Desc) (c : Nat) (vs : List Val)
    (buf : List AB) (p : Nat), (placeFields m c (Desc.layouts fs)).2 ≤ p →
    (Desc.writeFields fs (placeFields m c (Desc.layouts fs)).1 vs buf).getD p .uninit =
      buf.getD p .uninit
  | [], c, vs, buf, p, _ => by simp [Desc.writeFields]
  | f :: fs, c, [], buf, p, _ => by
    rw [layouts_cons, placeFields_cons]
    simp [Desc.writeFields]
  | f :: fs, c, v :: vs, buf, p, h => by
    rw [layouts_cons, placeFields_cons] at *
    simp only [Desc.writeFields]
    have h1 := placeFields_end_ge m (Desc.layouts fs) (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    have hfs : f.layout.size = f.size := rfl
    rw [writeFields_getD_ge m fs _ vs _ p h]
    exact getD_writeAt_of_ge (by rw [encodeL_length]; omega)

theorem writeFields_getD_head (m : ReprModifier) (f : Desc) (fs : List Desc) (c : Nat) (v : Val)
    (vs : List Val) (buf : List AB) (p : Nat)
    (h1 : alignUp c (effFieldAlign m f.align) ≤ p) (h2 : p < alignUp c (effFieldAlign m f.align) + f.size)
    (h3 : p < buf.length) :
    (Desc.writeFields (f :: fs) (placeFields m c (Desc.layouts (f :: fs))).1 (v :: vs) buf).getD p
        .uninit = (f.encodeL v).getD (p - alignUp c (effFieldAlign m f.align)) .uninit := by
  rw [layouts_cons, placeFields_cons]
  simp only [Desc.writeFields]
  rw [writeFields_getD_lt m fs _ vs _ p h2]
  exact getD_writeAt_of_mem h1 (by rw [encodeL_length]; exact h2) h3

theorem writeFields_gap (m : ReprModifier) : ∀ (fs : List Desc) (c : Nat),
    c + (fs.map Desc.size).sum < (placeFields m c (Desc.layouts fs)).2 →
    ∃ p, c ≤ p ∧ p < (placeFields m c (Desc.layouts fs)).2 ∧ ∀ vs buf,
      (Desc.writeFields fs (placeFields m c (Desc.layouts fs)).1 vs buf).getD p .uninit =
        buf.getD p .uninit
  | [], c, h => by simp [Desc.layouts, placeFields] at h
  | f :: fs, c, h => by
    have hfs : f.layout.size = f.size := rfl
    have hle := le_alignUp c (effFieldAlign m f.layout.align)
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    rw [layouts_cons, placeFields_cons] at *
    simp only [List.map_cons, List.sum_cons] at h
    rcases Nat.lt_or_ge c (alignUp c (effFieldAlign m f.layout.align)) with hlt | hge
    · refine ⟨c, Nat.le_refl _, ?_, ?_⟩
      · rw [layouts_map_size] at hend
        omega
      · intro vs buf
        cases vs with
        | nil => simp [Desc.writeFields]
        | cons v vs =>
          simp only [Desc.writeFields]
          rw [writeFields_getD_lt m fs _ vs _ c (by omega)]
          exact getD_writeAt_of_lt hlt
    · obtain ⟨p, hp1, hp2, hp3⟩ := writeFields_gap m fs
        (alignUp c (effFieldAlign m f.layout.align) + f.layout.size) (by omega)
      refine ⟨p, by omega, hp2, ?_⟩
      intro vs buf
      cases vs with
      | nil => simp [Desc.writeFields]
      | cons v vs =>
        simp only [Desc.writeFields]
        rw [hp3 vs]
        exact getD_writeAt_of_ge (by rw [encodeL_length]; omega)

theorem writeFields_init_of_tight (m : ReprModifier) : ∀ (fs : List Desc) (c : Nat) (vs : List Val)
    (buf : List AB),
    (placeFields m c (Desc.layouts fs)).2 = c + (fs.map Desc.size).sum →
    (∀ f ∈ fs, SemIntoBytes f) → Desc.hasTypes fs vs = true →
    (placeFields m c (Desc.layouts fs)).2 ≤ buf.length →
    ∀ p, p < buf.length →
      (p < c ∨ (placeFields m c (Desc.layouts fs)).2 ≤ p → (buf.getD p .uninit).isInit = true) →
      ((Desc.writeFields fs (placeFields m c (Desc.layouts fs)).1 vs buf).getD p .uninit).isInit = true
  | [], c, vs, buf, ht, _, hty, _, p, _, hb => by
    cases vs with
    | nil =>
      simp only [Desc.writeFields]
      exact hb (by simp at ht ⊢; omega)
    | cons v vs => simp [Desc.hasTypes] at hty
  | f :: fs, c, [], buf, ht, _, hty, _, p, _, hb => by simp [Desc.hasTypes] at hty
  | f :: fs, c, v :: vs, buf, ht, hI, hty, hlen, p, hp, hb => by
    simp only [Desc.hasTypes, Bool.and_eq_true] at hty
    have hfs : f.layout.size = f.size := rfl
    have hle := le_alignUp c (effFieldAlign m f.layout.align)
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    rw [layouts_map_size] at hend
    rw [layouts_cons, placeFields_cons] at *
    simp only [List.map_cons, List.sum_cons] at ht
    simp only [Desc.writeFields]
    have hfI := hI f List.mem_cons_self
    have hencI := (semIntoBytes_iff_encodeL_init f).mp hfI v hty.1
    refine writeFields_init_of_tight m fs _ vs _ (by omega)
      (fun g hg => hI g (List.mem_cons_of_mem _ hg)) hty.2 (by rw [writeAt_length]; omega) p
      (by rw [writeAt_length]; exact hp) ?_
    intro hcase
    by_cases hin : alignUp c (effFieldAlign m f.layout.align) ≤ p ∧
        p < alignUp c (effFieldAlign m f.layout.align) + f.size
    · rw [getD_writeAt_of_mem hin.1 (by rw [encodeL_length]; exact hin.2) hp]
      exact hencI _ (by omega)
    · rw [getD_writeAt]
      have : ¬ (alignUp c (effFieldAlign m f.layout.align) ≤ p ∧
          p < alignUp c (effFieldAlign m f.layout.align) + (f.encodeL v).length ∧ p < buf.length) := by
        rw [encodeL_length]; omega
      simp only [this, ↓reduceIte]
      exact hb (by omega)

theorem exists_hasTypes : ∀ (fs : List Desc), (∀ f ∈ fs, f.Inhabited) →
    ∃ vs, Desc.hasTypes fs vs = true
  | [], _ => ⟨[], by simp [Desc.hasTypes]⟩
  | f :: fs, h => by
    obtain ⟨v, hv⟩ := h f List.mem_cons_self
    obtain ⟨vs, hvs⟩ := exists_hasTypes fs (fun g hg => h g (List.mem_cons_of_mem _ hg))
    exact ⟨v :: vs, by simp [Desc.hasTypes, hv, hvs]⟩

theorem fields_intoBytes_of_writeFields (m : ReprModifier) : ∀ (fs : List Desc) (c : Nat)
    (buf : List AB), (∀ f ∈ fs, f.Inhabited) → (placeFields m c (Desc.layouts fs)).2 ≤ buf.length →
    (∀ vs, Desc.hasTypes fs vs = true → ∀ p, c ≤ p → p < buf.length →
      ((Desc.writeFields fs (placeFields m c (Desc.layouts fs)).1 vs buf).getD p .uninit).isInit =
        true) →
    ∀ f ∈ fs, SemIntoBytes f
  | [], _, _, _, _, _ => fun _ h => nomatch h
  | f :: fs, c, buf, hInh, hlen, H => by
    have hfs : f.layout.size = f.size := rfl
    have hfa : alignUp c (effFieldAlign m f.align) = alignUp c (effFieldAlign m f.layout.align) := rfl
    have hle := le_alignUp c (effFieldAlign m f.layout.align)
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    obtain ⟨rest, hrest⟩ := exists_hasTypes fs (fun g hg => hInh g (List.mem_cons_of_mem _ hg))
    obtain ⟨w0, hw0⟩ := hInh f List.mem_cons_self
    have hlen' : (placeFields m (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
        (Desc.layouts fs)).2 ≤ buf.length := by
      rw [layouts_cons, placeFields_cons] at hlen; exact hlen
    intro g hg
    cases hg with
    | head =>
      rw [semIntoBytes_iff_encodeL_init]
      intro w hw i hi
      have := H (w :: rest) (by simp [Desc.hasTypes, hw, hrest])
        (alignUp c (effFieldAlign m f.layout.align) + i) (by omega) (by omega)
      rw [writeFields_getD_head m f fs c w rest buf _ (by omega) (by omega) (by omega)] at this
      simpa using this
    | tail _ hg =>
      refine fields_intoBytes_of_writeFields m fs
        (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
        (writeAt buf (alignUp c (effFieldAlign m f.layout.align)) (f.encodeL w0))
        (fun g hg => hInh g (List.mem_cons_of_mem _ hg)) (by rw [writeAt_length]; exact hlen') ?_ g hg
      intro vs hvs p hp1 hp2
      rw [writeAt_length] at hp2
      have := H (w0 :: vs) (by simp [Desc.hasTypes, hw0, hvs]) p (by omega) hp2
      rw [layouts_cons, placeFields_cons] at this
      simpa only [Desc.writeFields] using this

theorem decodeFields_isSome_of (m : ReprModifier) (S : AB → Prop) : ∀ (fs : List Desc) (c : Nat)
    (x : List AB), (placeFields m c (Desc.layouts fs)).2 ≤ x.length → (∀ b ∈ x, S b) →
    (∀ f ∈ fs, ∀ y : List AB, y.length = f.size → (∀ b ∈ y, S b) → (f.decodeL y).isSome = true) →
    (Desc.decodeFields fs (placeFields m c (Desc.layouts fs)).1 x).isSome = true
  | [], _, _, _, _, _ => by simp [Desc.decodeFields]
  | f :: fs, c, x, hlen, hS, hF => by
    have hfs : f.layout.size = f.size := rfl
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    rw [layouts_cons, placeFields_cons] at *
    simp only [Desc.decodeFields]
    have h1 : (f.decodeL (slice x (alignUp c (effFieldAlign m f.layout.align)) f.size)).isSome = true :=
      hF f List.mem_cons_self _ (by simp [slice]; omega)
        (fun b hb => hS b (List.mem_of_mem_drop (List.mem_of_mem_take hb)))
    have h2 := decodeFields_isSome_of m S fs _ x hlen hS (fun g hg => hF g (List.mem_cons_of_mem _ hg))
    revert h1 h2
    cases f.decodeL (slice x (alignUp c (effFieldAlign m f.layout.align)) f.size) <;>
      cases Desc.decodeFields fs _ x <;> simp

theorem decodeFields_field (m : ReprModifier) : ∀ (fs : List Desc) (c : Nat), ∀ f ∈ fs, ∃ o,
    c ≤ o ∧ o + f.size ≤ (placeFields m c (Desc.layouts fs)).2 ∧
    ∀ x, (Desc.decodeFields fs (placeFields m c (Desc.layouts fs)).1 x).isSome = true →
      (f.decodeL (slice x o f.size)).isSome = true
  | [], _ => fun _ h => nomatch h
  | f :: fs, c => by
    have hfs : f.layout.size = f.size := rfl
    have hle := le_alignUp c (effFieldAlign m f.layout.align)
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    intro g hg
    rw [layouts_cons, placeFields_cons]
    cases hg with
    | head =>
      refine ⟨alignUp c (effFieldAlign m f.layout.align), hle, by omega, fun x hx => ?_⟩
      simp only [Desc.decodeFields] at hx
      revert hx
      cases f.decodeL (slice x (alignUp c (effFieldAlign m f.layout.align)) f.size) <;>
        cases Desc.decodeFields fs _ x <;> simp
    | tail _ hg =>
      obtain ⟨o, ho1, ho2, ho3⟩ := decodeFields_field m fs
        (alignUp c (effFieldAlign m f.layout.align) + f.layout.size) g hg
      refine ⟨o, by omega, ho2, fun x hx => ho3 x ?_⟩
      simp only [Desc.decodeFields] at hx
      revert hx
      cases f.decodeL (slice x (alignUp c (effFieldAlign m f.layout.align)) f.size) <;>
        cases Desc.decodeFields fs _ x <;> simp

/-! ## Struct layouts -/

theorem structRepr_layout_eq (r : StructRepr) : ∃ m, ∀ ls, r.layout ls = reprCStruct m ls := by
  cases r with
  | c m => exact ⟨m, fun _ => rfl⟩
  | transparent => exact ⟨.none, fun _ => rfl⟩

theorem reprCStruct_offsets (m : ReprModifier) (ls : List FieldLayout) :
    (reprCStruct m ls).offsets = (placeFields m 0 ls).1 := rfl

theorem reprCStruct_endOffset (m : ReprModifier) (ls : List FieldLayout) :
    (reprCStruct m ls).endOffset = (placeFields m 0 ls).2 := rfl

theorem reprCStruct_size (m : ReprModifier) (ls : List FieldLayout) :
    (reprCStruct m ls).size = alignUp (placeFields m 0 ls).2 (structAlign m ls) := rfl

theorem reprCStruct_align (m : ReprModifier) (ls : List FieldLayout) :
    (reprCStruct m ls).align = structAlign m ls := rfl

end Toy.Zc
