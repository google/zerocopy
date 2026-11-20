import ToyUB.Lemmas

/-!
# Monotonicity lemmas

Lifting lemmas for `OutRef` through `bind1`, `++` and conditionals; monotonicity of the
semantics in the environment (both models); nonemptiness of undef-model value sets.
These are the ingredients of the congruence theorems in `ToyUB.Refinement`.
-/

namespace Toy.UB

variable {V α : Type}

theorem outRef_nil {R : V → V → Prop} (S : List (Outcome V)) : OutRef R [] S :=
  Or.inr (by simp)

theorem outRef_singleton_val {R : V → V → Prop} {t s : V} (h : R t s) :
    OutRef R [Outcome.val t] [Outcome.val s] :=
  Or.inr (by simpa [Outcome.LeVal] using h)

theorem outRef_append {R : V → V → Prop} {T1 T2 S1 S2 : List (Outcome V)}
    (h1 : OutRef R T1 S1) (h2 : OutRef R T2 S2) : OutRef R (T1 ++ T2) (S1 ++ S2) := by
  by_cases hS : MayUB (S1 ++ S2)
  · exact Or.inl hS
  · rw [mayUB_iff, List.mem_append, not_or] at hS
    rcases h1 with h1 | h1
    · exact absurd (mayUB_iff.mp h1) hS.1
    rcases h2 with h2 | h2
    · exact absurd (mayUB_iff.mp h2) hS.2
    right
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨o', h, hle⟩ := h1 o ho
      exact ⟨o', List.mem_append_left _ h, hle⟩
    · obtain ⟨o', h, hle⟩ := h2 o ho
      exact ⟨o', List.mem_append_right _ h, hle⟩

theorem outRef_ite_branch {R : V → V → Prop} {b' b : Bool} {T' T : List (Outcome V)}
    (hb : b' = true → b = true) (h : OutRef R T' T) :
    OutRef R (if b' = true then T' else []) (if b = true then T else []) := by
  cases b' with
  | false => simpa using outRef_nil _
  | true => simpa [hb rfl] using h

theorem outRef_bind1 {R : V → V → Prop} {R' : α → α → Prop} {A' A : List (Outcome α)}
    {f' f : α → List (Outcome V)} (hA : OutRef R' A' A)
    (hf : ∀ a' a, Outcome.val a' ∈ A' → Outcome.val a ∈ A → R' a' a → OutRef R (f' a') (f a)) :
    OutRef R (bind1 A' f') (bind1 A f) := by
  by_cases hS : MayUB (bind1 A f)
  · exact Or.inl hS
  · right
    have hAub : Outcome.ub ∉ A := fun h => hS (mayUB_iff.mpr (ub_mem_bind1_of_ub_mem h))
    rcases hA with hA | hA
    · exact absurd (mayUB_iff.mp hA) hAub
    intro o ho
    rcases mem_bind1.mp ho with ⟨rfl, h⟩ | ⟨a', ha', ho⟩
    · obtain ⟨o', _, hle⟩ := hA _ h
      cases o' <;> simp [Outcome.LeVal] at hle
    · obtain ⟨o', ho', hle⟩ := hA _ ha'
      cases o' with
      | ub => simp [Outcome.LeVal] at hle
      | val a =>
        have hfa : ¬ MayUB (f a) := fun h =>
          hS (mayUB_iff.mpr (mem_bind1.mpr (Or.inr ⟨a, ho', mayUB_iff.mp h⟩)))
        rcases hf a' a ha' ho' hle with h | h
        · exact absurd h hfa
        · obtain ⟨o'', ho'', hle'⟩ := h o ho
          exact ⟨o'', mem_bind1.mpr (Or.inr ⟨a, ho', ho''⟩), hle'⟩

/-! ### Undef model -/

theorem USet.map2_mono {w : Nat} {f : BitVec w → BitVec w → BitVec w} {A' A B' B : USet w}
    (hA : USet.Sub A' A) (hB : USet.Sub B' B) : USet.Sub (USet.map2 f A' B') (USet.map2 f A B) := by
  intro z hz
  simp only [USet.map2, decide_eq_true_eq] at hz ⊢
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  exact ⟨a, b, hA a ha, hB b hb, rfl⟩

theorem USet.hasNonzero_mono {w : Nat} {C' C : USet w} (h : USet.Sub C' C) :
    C'.HasNonzero = true → C.HasNonzero = true := by
  simp only [USet.HasNonzero, decide_eq_true_eq]
  rintro ⟨z, hz, hz0⟩
  exact ⟨z, h z hz, hz0⟩

theorem freezeU_mono {w : Nat} {A' A : USet w} (hA : USet.Sub A' A) :
    OutRef USet.Sub
      ((allBV w).filterMap fun v => if A' v then some (Outcome.val (USet.single v)) else none)
      ((allBV w).filterMap fun v => if A v then some (Outcome.val (USet.single v)) else none) := by
  apply outRef_of_subset USet.Sub.refl
  intro o ho
  rw [List.mem_filterMap] at ho ⊢
  obtain ⟨v, hv, h⟩ := ho
  refine ⟨v, hv, ?_⟩
  by_cases hA'v : A' v = true
  · simp only [hA'v, ite_true] at h
    simp [hA v hA'v, h]
  · simp [hA'v] at h

theorem update_sub {w : Nat} {ρ' ρ : Var → USet w} (h : ∀ y, USet.Sub (ρ' y) (ρ y)) (x : Var)
    {A' A : USet w} (hA : USet.Sub A' A) : ∀ y, USet.Sub (update ρ' x A' y) (update ρ x A y) := by
  intro y
  simp only [update]
  split
  · exact hA
  · exact h y

/-- The undef-model semantics is monotone in the environment. -/
theorem semU_mono (w : Nat) (e : Expr) :
    ∀ ρ' ρ : Var → USet w, (∀ y, USet.Sub (ρ' y) (ρ y)) →
      OutRef USet.Sub (semU w ρ' e) (semU w ρ e) := by
  induction e with
  | var x => intro ρ' ρ h; exact outRef_singleton_val (h x)
  | const n => intro _ _ _; exact outRef_refl USet.Sub.refl _
  | add a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ hA =>
      outRef_bind1 (ihb ρ' ρ h) fun _ _ _ _ hB => outRef_singleton_val (USet.map2_mono hA hB)
  | mul a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ hA =>
      outRef_bind1 (ihb ρ' ρ h) fun _ _ _ _ hB => outRef_singleton_val (USet.map2_mono hA hB)
  | eq a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ hA =>
      outRef_bind1 (ihb ρ' ρ h) fun _ _ _ _ hB => outRef_singleton_val (USet.map2_mono hA hB)
  | ite c t e ihc iht ihe =>
    intro ρ' ρ h
    exact outRef_bind1 (ihc ρ' ρ h) fun _ _ _ _ hC =>
      outRef_append (outRef_ite_branch (USet.hasNonzero_mono hC) (iht ρ' ρ h))
        (outRef_ite_branch (hC _) (ihe ρ' ρ h))
  | letE x a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ hA => ihb _ _ (update_sub h x hA)
  | freeze a iha =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ hA => freezeU_mono hA
  | ub => intro _ _ _; exact outRef_refl USet.Sub.refl _

/-- From an environment of nonempty sets, every value outcome is a nonempty set. -/
theorem semU_val_nonempty (w : Nat) (e : Expr) :
    ∀ ρ : Var → USet w, UInhabited ρ → ∀ A, Outcome.val A ∈ semU w ρ e → A.Nonempty := by
  induction e with
  | var x => intro ρ hρ A hA; simp [semU] at hA; subst hA; exact hρ x
  | const n =>
    intro ρ _ A hA
    simp [semU] at hA
    subst hA
    exact ⟨BitVec.ofNat w n, by simp [USet.single]⟩
  | add a b iha ihb =>
    intro ρ hρ A hA
    simp only [semU, bind2] at hA
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨A1, h1, hA⟩
    · cases h
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨B1, h2, hA⟩
    · cases h
    simp only [List.mem_singleton, Outcome.val.injEq] at hA
    subst hA
    obtain ⟨x, hx⟩ := iha ρ hρ A1 h1
    obtain ⟨y, hy⟩ := ihb ρ hρ B1 h2
    exact ⟨_, decide_eq_true ⟨x, y, hx, hy, rfl⟩⟩
  | mul a b iha ihb =>
    intro ρ hρ A hA
    simp only [semU, bind2] at hA
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨A1, h1, hA⟩
    · cases h
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨B1, h2, hA⟩
    · cases h
    simp only [List.mem_singleton, Outcome.val.injEq] at hA
    subst hA
    obtain ⟨x, hx⟩ := iha ρ hρ A1 h1
    obtain ⟨y, hy⟩ := ihb ρ hρ B1 h2
    exact ⟨_, decide_eq_true ⟨x, y, hx, hy, rfl⟩⟩
  | eq a b iha ihb =>
    intro ρ hρ A hA
    simp only [semU, bind2] at hA
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨A1, h1, hA⟩
    · cases h
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨B1, h2, hA⟩
    · cases h
    simp only [List.mem_singleton, Outcome.val.injEq] at hA
    subst hA
    obtain ⟨x, hx⟩ := iha ρ hρ A1 h1
    obtain ⟨y, hy⟩ := ihb ρ hρ B1 h2
    exact ⟨_, decide_eq_true ⟨x, y, hx, hy, rfl⟩⟩
  | ite c t e _ iht ihe =>
    intro ρ hρ A hA
    simp only [semU] at hA
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨C, _, hA⟩
    · cases h
    rcases List.mem_append.mp hA with hA | hA
    · split at hA
      · exact iht ρ hρ A hA
      · simp at hA
    · split at hA
      · exact ihe ρ hρ A hA
      · simp at hA
  | letE x a b iha ihb =>
    intro ρ hρ A hA
    simp only [semU] at hA
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨A1, h1, hA⟩
    · cases h
    refine ihb (update ρ x A1) ?_ A hA
    intro y
    simp only [update]
    split
    · exact iha ρ hρ A1 h1
    · exact hρ y
  | freeze a _ =>
    intro ρ _ A hA
    simp only [semU] at hA
    rcases mem_bind1.mp hA with ⟨h, _⟩ | ⟨A1, _, hA⟩
    · cases h
    rw [List.mem_filterMap] at hA
    obtain ⟨v, _, hv⟩ := hA
    split at hv
    · simp only [Option.some.injEq, Outcome.val.injEq] at hv
      subst hv
      exact ⟨v, by simp [USet.single]⟩
    · simp at hv
  | ub => intro ρ _ A hA; simp [semU] at hA

/-! ### Poison model -/

theorem PVal.lift2_mono {w : Nat} {f : BitVec w → BitVec w → BitVec w} {a' a b' b : PVal w}
    (ha : PVal.Refines a' a) (hb : PVal.Refines b' b) :
    PVal.Refines (PVal.lift2 f a' b') (PVal.lift2 f a b) := by
  cases a with
  | poison => cases b <;> simp [PVal.lift2, PVal.Refines]
  | int x =>
    simp only [PVal.Refines] at ha
    subst ha
    cases b with
    | poison => cases b' <;> simp [PVal.lift2, PVal.Refines]
    | int y =>
      simp only [PVal.Refines] at hb
      subst hb
      simp [PVal.lift2, PVal.Refines]

theorem update_refines {w : Nat} {ρ' ρ : Var → PVal w} (h : ∀ y, PVal.Refines (ρ' y) (ρ y))
    (x : Var) {v' v : PVal w} (hv : PVal.Refines v' v) :
    ∀ y, PVal.Refines (update ρ' x v' y) (update ρ x v y) := by
  intro y
  simp only [update]
  split
  · exact hv
  · exact h y

/-- The poison-model semantics is monotone in the environment. -/
theorem semP_mono (w : Nat) (e : Expr) :
    ∀ ρ' ρ : Var → PVal w, (∀ y, PVal.Refines (ρ' y) (ρ y)) →
      OutRef PVal.Refines (semP w ρ' e) (semP w ρ e) := by
  induction e with
  | var x => intro ρ' ρ h; exact outRef_singleton_val (h x)
  | const n => intro _ _ _; exact outRef_refl PVal.Refines.refl _
  | add a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ ha =>
      outRef_bind1 (ihb ρ' ρ h) fun _ _ _ _ hb => outRef_singleton_val (PVal.lift2_mono ha hb)
  | mul a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ ha =>
      outRef_bind1 (ihb ρ' ρ h) fun _ _ _ _ hb => outRef_singleton_val (PVal.lift2_mono ha hb)
  | eq a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ ha =>
      outRef_bind1 (ihb ρ' ρ h) fun _ _ _ _ hb => outRef_singleton_val (PVal.lift2_mono ha hb)
  | ite c t e ihc iht ihe =>
    intro ρ' ρ h
    refine outRef_bind1 (ihc ρ' ρ h) fun c' c _ _ hc => ?_
    cases c with
    | poison => exact Or.inl (mayUB_iff.mpr (by simp))
    | int z =>
      simp only [PVal.Refines] at hc
      subst hc
      dsimp only
      split
      · exact iht ρ' ρ h
      · exact ihe ρ' ρ h
  | letE x a b iha ihb =>
    intro ρ' ρ h
    exact outRef_bind1 (iha ρ' ρ h) fun _ _ _ _ hv => ihb _ _ (update_refines h x hv)
  | freeze a iha =>
    intro ρ' ρ h
    refine outRef_bind1 (iha ρ' ρ h) fun v' v _ _ hv => ?_
    cases v with
    | poison =>
      apply outRef_of_subset PVal.Refines.refl
      intro o ho
      cases v' with
      | poison => exact ho
      | int u =>
        simp at ho
        subst ho
        simp [mem_allBV]
    | int u =>
      simp only [PVal.Refines] at hv
      subst hv
      exact outRef_refl PVal.Refines.refl _
  | ub => intro _ _ _; exact outRef_refl PVal.Refines.refl _

/-! ### Totality: outcome lists are never empty

`OutRef` accepts an empty target list. The lemmas below show that this case never arises:
in every admissible environment every expression has at least one outcome, so refinement
coincides with the variant `OutRefNE` that demands a nonempty target. -/

/-- `bind1` preserves non-emptiness of outcome lists. -/
theorem bind1_ne_nil {β : Type} {A : List (Outcome α)} {f : α → List (Outcome β)}
    (hA : A ≠ []) (hf : ∀ a, Outcome.val a ∈ A → f a ≠ []) : bind1 A f ≠ [] := by
  cases A with
  | nil => exact absurd rfl hA
  | cons o rest =>
    cases o with
    | ub => simp [bind1]
    | val a =>
      have hfa : f a ≠ [] := hf a (by simp)
      intro h
      simp [bind1] at h
      exact hfa h.1

/-- **Totality (poison(+freeze) model).** Every expression has at least one outcome in
every environment. -/
theorem semP_ne_nil (w : Nat) (e : Expr) : ∀ ρ : Var → PVal w, semP w ρ e ≠ [] := by
  induction e with
  | var x => intro ρ; simp [semP]
  | const n => intro ρ; simp [semP]
  | add a b iha ihb =>
    intro ρ
    exact bind1_ne_nil (iha ρ) fun _ _ => bind1_ne_nil (ihb ρ) fun _ _ => by simp
  | mul a b iha ihb =>
    intro ρ
    exact bind1_ne_nil (iha ρ) fun _ _ => bind1_ne_nil (ihb ρ) fun _ _ => by simp
  | eq a b iha ihb =>
    intro ρ
    exact bind1_ne_nil (iha ρ) fun _ _ => bind1_ne_nil (ihb ρ) fun _ _ => by simp
  | ite c t e ihc iht ihe =>
    intro ρ
    refine bind1_ne_nil (ihc ρ) fun vc _ => ?_
    cases vc with
    | poison => simp
    | int z =>
      dsimp only
      split
      · exact iht ρ
      · exact ihe ρ
  | letE x a b iha ihb =>
    intro ρ
    exact bind1_ne_nil (iha ρ) fun v _ => ihb (update ρ x v)
  | freeze a iha =>
    intro ρ
    refine bind1_ne_nil (iha ρ) fun v _ => ?_
    cases v with
    | int u => simp
    | poison =>
      intro h
      dsimp only at h
      have hm : Outcome.val (PVal.int 0#w) ∈ (allBV w).map (fun u => Outcome.val (PVal.int u)) :=
        List.mem_map.mpr ⟨0#w, mem_allBV 0#w, rfl⟩
      rw [h] at hm
      cases hm
  | ub => intro ρ; simp [semP]

/-- **Totality (undef model).** Every expression has at least one outcome in every
environment of nonempty sets. (With an empty input set, `if` on that input has no
outcome at all; see `undef_unswitch_empty_input_target_has_no_outcomes`.) -/
theorem semU_ne_nil (w : Nat) (e : Expr) :
    ∀ ρ : Var → USet w, UInhabited ρ → semU w ρ e ≠ [] := by
  induction e with
  | var x => intro ρ _; simp [semU]
  | const n => intro ρ _; simp [semU]
  | add a b iha ihb =>
    intro ρ hρ
    exact bind1_ne_nil (iha ρ hρ) fun _ _ => bind1_ne_nil (ihb ρ hρ) fun _ _ => by simp
  | mul a b iha ihb =>
    intro ρ hρ
    exact bind1_ne_nil (iha ρ hρ) fun _ _ => bind1_ne_nil (ihb ρ hρ) fun _ _ => by simp
  | eq a b iha ihb =>
    intro ρ hρ
    exact bind1_ne_nil (iha ρ hρ) fun _ _ => bind1_ne_nil (ihb ρ hρ) fun _ _ => by simp
  | ite c t e ihc iht ihe =>
    intro ρ hρ
    refine bind1_ne_nil (ihc ρ hρ) fun C hC => ?_
    obtain ⟨z, hz⟩ := semU_val_nonempty w c ρ hρ C hC
    by_cases hz0 : z = 0#w
    · subst hz0
      intro h
      simp [hz] at h
      exact ihe ρ hρ (by
        cases hCn : C.HasNonzero <;> simp_all)
    · have hCn : C.HasNonzero = true := decide_eq_true ⟨z, hz, hz0⟩
      intro h
      simp [hCn] at h
      exact iht ρ hρ h.1
  | letE x a b iha ihb =>
    intro ρ hρ
    refine bind1_ne_nil (iha ρ hρ) fun A hA => ihb (update ρ x A) ?_
    intro y
    simp only [update]
    split
    · exact semU_val_nonempty w a ρ hρ A hA
    · exact hρ y
  | freeze a iha =>
    intro ρ hρ
    refine bind1_ne_nil (iha ρ hρ) fun A hA => ?_
    obtain ⟨v, hv⟩ := semU_val_nonempty w a ρ hρ A hA
    intro h
    have hm : Outcome.val (USet.single v) ∈
        (allBV w).filterMap (fun u => if A u then some (Outcome.val (USet.single u)) else none) :=
      List.mem_filterMap.mpr ⟨v, mem_allBV v, by simp [hv]⟩
    rw [h] at hm
    cases hm
  | ub => intro ρ _; simp [semU]

/-- With a nonempty target list, `OutRef` and `OutRefNE` agree. -/
theorem outRef_iff_outRefNE {R : V → V → Prop} {T S : List (Outcome V)} (hT : T ≠ []) :
    OutRef R T S ↔ OutRefNE R T S := by
  unfold OutRef OutRefNE
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨fun _ => hT, h⟩
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h

/-- **The empty-target case of `OutRef` is never used (poison(+freeze) model).** Poison-model
refinement is equivalent to refinement with `OutRefNE`, which demands a nonempty target. -/
theorem refinesP_iff_outRefNE (w : Nat) (tgt src : Expr) :
    RefinesP w tgt src ↔ ∀ ρ : Var → PVal w, OutRefNE PVal.Refines (semP w ρ tgt) (semP w ρ src) :=
  forall_congr' fun ρ => outRef_iff_outRefNE (semP_ne_nil w tgt ρ)

/-- **The empty-target case of `OutRef` is never used (undef model).** Undef-model
refinement is equivalent to refinement with `OutRefNE`, which demands a nonempty target. -/
theorem refinesU_iff_outRefNE (w : Nat) (tgt src : Expr) :
    RefinesU w tgt src ↔
      ∀ ρ : Var → USet w, UInhabited ρ → OutRefNE USet.Sub (semU w ρ tgt) (semU w ρ src) :=
  forall_congr' fun ρ => imp_congr_right fun hρ => outRef_iff_outRefNE (semU_ne_nil w tgt ρ hρ)

end Toy.UB
