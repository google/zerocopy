import ToyLink.Basic

/-!
# Main theorem statements

Contextual refinement (preorder, precongruence, what it observes), assume-guarantee
modular verification (partial and total correctness), specification refinement at link
time, and separate compilation (verifiability preservation and behavioural refinement).
-/

namespace Toy.Link

/-! ## Contextual refinement is a preorder and a precongruence for linking -/

/-- Contextual refinement is reflexive (reference point; immediate from the definition). -/
theorem ctxRefines_refl (M : Module) : CtxRefines M M :=
  fun _ _ _ _ _ _ _ h => h

/-- Contextual refinement is transitive.
Notice that no extra `Linkable` or `SameDom` hypothesis is needed because
`CtxRefines M₁ M₂` and `CtxRefines M₂ M₃` entail `SameDom M₁ M₂` and
`SameDom M₂ M₃`, so every context linkable with `M₁` and `M₃` is also
linkable with `M₂`. -/
theorem ctxRefines_trans {M₁ M₂ M₃ : Module}
    (h₁₂ : CtxRefines M₁ M₂) (h₂₃ : CtxRefines M₂ M₃) : CtxRefines M₁ M₃ := by
  intro C hC₁ hC₃ entry fuel arg out hOut
  have hC₂ : Linkable C M₂ := linkable_of_sameDom_right (ctxRefines_sameDom h₁₂) hC₁
  exact h₁₂ C hC₁ hC₂ entry fuel arg out (h₂₃ C hC₂ hC₃ entry fuel arg out hOut)

/-- Contextual refinement is a precongruence for disjoint linking:
linking two contextually refining modules preserves contextual refinement.
Notice that `Linkable M₁' M₂'` is derivable via `ctxRefines_sameDom`. -/
theorem ctxRefines_link_congr {M₁ M₁' M₂ M₂' : Module}
    (h₁ : CtxRefines M₁ M₁') (h₂ : CtxRefines M₂ M₂') (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link M₁' M₂') := by
  intro C hC₁₂ hC₁₂' entry fuel arg out hOut
  have hs₁ : SameDom M₁ M₁' := ctxRefines_sameDom h₁
  have hs₂ : SameDom M₂ M₂' := ctxRefines_sameDom h₂
  have hC₁ : Linkable C M₁ := (linkable_link_iff C M₁ M₂).1 hC₁₂ |>.1
  have hC₂ : Linkable C M₂ := (linkable_link_iff C M₁ M₂).1 hC₁₂ |>.2
  have hC₁' : Linkable C M₁' := linkable_of_sameDom_right hs₁ hC₁
  have hC₂' : Linkable C M₂' := linkable_of_sameDom_right hs₂ hC₂
  have hLink₁₂' : Linkable M₁ M₂' := linkable_of_sameDom_right hs₂ hLink
  have hLink₁'₂' : Linkable M₁' M₂' := linkable_of_sameDom_both hs₁ hs₂ hLink
  have hCtx₁ : Linkable (link C M₂') M₁ := by
    rw [linkable_symm_iff]
    exact (linkable_link_iff M₁ C M₂').2 ⟨linkable_symm hC₁, hLink₁₂'⟩
  have hCtx₁' : Linkable (link C M₂') M₁' := by
    have : Linkable M₁' (link C M₂') :=
      (linkable_link_iff M₁' C M₂').2 ⟨linkable_symm hC₁', hLink₁'₂'⟩
    exact linkable_symm this
  have hStep1 : HasBehavior entry (link (link C M₂') M₁') fuel arg out := by
    refine (entryRefines_of_lookup_eq ?_ entry) fuel arg out hOut
    intro fn
    rw [lookup_link_assoc, lookup_link, lookup_link, lookup_link]
    cases hC : C.lookup fn with
    | some b => rfl
    | none => simpa [lookup_link] using lookup_link_comm (linkable_symm hLink₁'₂') fn
  have hStep2 : HasBehavior entry (link (link C M₂') M₁) fuel arg out :=
    h₁ (link C M₂') hCtx₁ hCtx₁' entry fuel arg out hStep1
  have hCtx₂ : Linkable (link C M₁) M₂ :=
    linkable_symm ((linkable_link_iff M₂ C M₁).2 ⟨linkable_symm hC₂, linkable_symm hLink⟩)
  have hCtx₂' : Linkable (link C M₁) M₂' :=
    linkable_symm ((linkable_link_iff M₂' C M₁).2 ⟨linkable_symm hC₂', linkable_symm hLink₁₂'⟩)
  have hStep3 : HasBehavior entry (link (link C M₁) M₂') fuel arg out := by
    refine (entryRefines_of_lookup_eq ?_ entry) fuel arg out hStep2
    intro fn
    rw [lookup_link_assoc, lookup_link_assoc, lookup_link, lookup_link, lookup_link]
    cases hC : C.lookup fn with
    | some b => rfl
    | none => simpa [lookup_link] using lookup_link_comm hLink₁₂' fn
  have hStep4 : HasBehavior entry (link (link C M₁) M₂) fuel arg out :=
    h₂ (link C M₁) hCtx₂ hCtx₂' entry fuel arg out hStep3
  refine (entryRefines_of_lookup_eq ?_ entry) fuel arg out hStep4
  intro fn
  exact (lookup_link_assoc C M₁ M₂ fn).symm
where
  linkable_symm_iff {A B : Module} : Linkable A B ↔ Linkable B A :=
    ⟨linkable_symm, linkable_symm⟩

/-- Left congruence corollary for linking. -/
theorem ctxRefines_link_left {M₁ M₁' M₂ : Module}
    (h₁ : CtxRefines M₁ M₁') (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link M₁' M₂) :=
  ctxRefines_link_congr h₁ (ctxRefines_refl M₂) hLink

/-- Right congruence corollary for linking. -/
theorem ctxRefines_link_right {M₁ M₂ M₂' : Module}
    (h₂ : CtxRefines M₂ M₂') (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link M₁ M₂') :=
  ctxRefines_link_congr (ctxRefines_refl M₁) h₂ hLink

/-! ## What contextual refinement observes -/

/-- **Collapse when one side is closed.** If the source module `M` or the target module
`M'` is closed (`ClosedModule`), contextual refinement coincides with standalone
refinement at every entry point: no context can observe more than direct calls of the
module's own functions. Contexts can only matter when *both* modules are open. -/
theorem ctxRefines_iff_standaloneRefines_of_closed_source_or_target {M M' : Module}
    (hClosed : ClosedModule M ∨ ClosedModule M') :
    CtxRefines M M' ↔ StandaloneRefines M M' := by
  constructor
  · exact standaloneRefines_of_ctxRefines
  · intro h C hC hC' entry fuel
    have hDom := sameDom_of_standaloneRefines h
    induction fuel generalizing entry with
    | zero => intro arg out ho; simpa [HasBehavior, eval] using ho
    | succ n ih =>
      intro arg out ho
      cases hCl : C.lookup entry with
      | some cb =>
        have hl1 : (link C M').lookup entry = some cb := by simp [lookup_link, hCl]
        have hl2 : (link C M).lookup entry = some cb := by simp [lookup_link, hCl]
        simp only [HasBehavior, eval, hl1, hl2] at ho ⊢
        exact evalExprWith_mono_mem (fun g a o h' => ih g a o h') arg cb ho
      | none =>
        by_cases hd' : M'.Defines entry
        · have hd : M.Defines entry := (hDom entry).2 hd'
          simp only [HasBehavior] at ho ⊢
          rcases hClosed with hM | hM'
          · have hNoU : .undefinedCall ∉ eval (n + 1) M' entry arg := fun hu =>
              closedModule_no_undefinedCall hM (n + 1) entry arg hd (h entry (n + 1) arg _ hu)
            rw [eval_link_right_of_no_undefinedCall hC' (n + 1) entry arg hNoU] at ho
            rw [eval_link_closed hC hM (n + 1) entry arg hd]
            exact h entry (n + 1) arg out ho
          · rw [eval_link_closed hC' hM' (n + 1) entry arg hd'] at ho
            have hne : out ≠ .undefinedCall := fun he =>
              closedModule_no_undefinedCall hM' (n + 1) entry arg hd' (he ▸ ho)
            exact eval_link_superset_non_undefinedCall hC (n + 1) entry arg out
              (h entry (n + 1) arg out ho) hne
        · have hd : ¬ M.Defines entry := fun hd => hd' ((hDom entry).1 hd)
          have hl1 : (link C M').lookup entry = none := by
            simp [lookup_link, hCl, lookup_none_of_not_defines hd']
          have hl2 : (link C M).lookup entry = none := by
            simp [lookup_link, hCl, lookup_none_of_not_defines hd]
          simp only [HasBehavior, eval, hl1, hl2] at ho ⊢
          exact ho

/-- **Contextual refinement reflects may-divergence.** If `M'` contextually refines `M`,
then in every context disjoint from `M`, wherever the target may diverge (exceed every
call-depth bound) the source may diverge too. Linkability of `C` with `M'` is derived
(`ctxRefines_sameDom`). -/
theorem ctxRefines_reflects_mayDiverge {M M' C : Module} {entry : Fname} {arg : Int}
    (h : CtxRefines M M') (hC : Linkable C M) :
    MayDiverge (link C M') entry arg → MayDiverge (link C M) entry arg :=
  fun hd fuel =>
    h C hC (linkable_of_sameDom_right (ctxRefines_sameDom h) hC) entry fuel arg _ (hd fuel)

/-! ## Assume-guarantee modular verification (partial and total correctness) -/

/-- **Circular assume-guarantee rule for partial correctness (no termination measure).**
If every function with a satisfiable precondition is defined in `P`, and every defined
function body satisfies its spec assuming every callee satisfies its spec, then `P` is
partially correct for all functions in `S` (by induction on fuel, i.e. call depth). -/
theorem ag_partial_correctness {P : Module} {S : SpecEnv}
    (hImpl : SpecsImplemented P S)
    (hVer : ModuleVerifiedPartial P S S) :
    ProgramPartialCorrect P S := by
  intro fn fuel
  induction fuel generalizing fn with
  | zero =>
    intro x out _ h
    exact .inl (by simpa [HasBehavior, eval] using h)
  | succ n ih =>
    intro x out hpre h
    simp only [HasBehavior, eval] at h
    cases hlu : P.lookup fn with
    | none =>
      exact absurd (hImpl fn x hpre) (by simp [Module.Defines, hlu])
    | some body =>
      rw [hlu] at h
      exact wpPartial_sound_evalExprWith (A := S)
        (fun g v o hp ho => ih g v o hp ho) (hVer fn body hlu x hpre) out h

/-- Linked-module corollary of circular assume-guarantee partial correctness. -/
theorem link_ag_partial_correctness {M₁ M₂ : Module} {S : SpecEnv}
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hVer₁ : ModuleVerifiedPartial M₁ S S)
    (hVer₂ : ModuleVerifiedPartial M₂ S S) :
    ProgramPartialCorrect (link M₁ M₂) S :=
  ag_partial_correctness hImpl (moduleVerifiedPartial_link hVer₁ hVer₂)

/-! Proof-internal helpers for the total-correctness rule. -/

private theorem list_flatMap_congr_local {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ a ∈ xs, f a = g a) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.Mem.head _), ih (fun a ha => h a (List.Mem.tail _ ha))]

private theorem exists_uniform_fuel_list {xs : List Outcome} {R : Int → Nat → Prop}
    (hMono : ∀ v k₁ k₂, k₁ ≤ k₂ → R v k₁ → R v k₂)
    (hAll : ∀ o ∈ xs, ∃ v, o = .val v ∧ ∃ k, R v k) :
    ∃ K, ∀ o ∈ xs, ∃ v, o = .val v ∧ R v K := by
  induction xs with
  | nil =>
    exact ⟨0, fun _ h => by cases h⟩
  | cons hd tl ih =>
    obtain ⟨v₀, rfl, k₀, hk₀⟩ := hAll hd (List.Mem.head _)
    obtain ⟨k₁, hk₁⟩ := ih (fun o ho => hAll o (List.Mem.tail _ ho))
    refine ⟨max k₀ k₁, fun o ho => ?_⟩
    simp only [List.mem_cons] at ho
    rcases ho with rfl | htl
    · exact ⟨v₀, rfl, hMono v₀ k₀ (max k₀ k₁) (Nat.le_max_left k₀ k₁) hk₀⟩
    · obtain ⟨v, rfl, hv⟩ := hk₁ o htl
      exact ⟨v, rfl, hMono v k₁ (max k₀ k₁) (Nat.le_max_right k₀ k₁) hv⟩

/-- Proof-internal invariant: from fuel `K` on, evaluating `e` is stable and every outcome
is a value satisfying `Q`. -/
private def StabAndGood (P : Module) (x : Int) (e : Expr) (Q : Int → Prop) (K : Nat) : Prop :=
  (∀ F, K ≤ F → evalExprWith (eval F P) x e = evalExprWith (eval K P) x e) ∧
  (∀ o ∈ evalExprWith (eval K P) x e, ∃ v, o = .val v ∧ Q v)

private theorem stabAndGood_mono {P : Module} {x : Int} {e : Expr} {Q : Int → Prop}
    {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) (h : StabAndGood P x e Q k₁) :
    StabAndGood P x e Q k₂ := by
  have heq : evalExprWith (eval k₂ P) x e = evalExprWith (eval k₁ P) x e := h.1 k₂ hle
  refine ⟨fun F hF => ?_, fun o ho => ?_⟩
  · rw [h.1 F (Nat.le_trans hle hF), heq]
  · rw [heq] at ho
    exact h.2 o ho

private theorem wpCallDec_sound_evalExprWith {α : Type} {rel : α → α → Prop}
    {μ : Fname → Int → α} {P : Module} {S : SpecEnv} {cur : α}
    (hCalls : ∀ g vArg, rel (μ g vArg) cur → (S g).pre vArg →
      ∃ fuel, ∀ out ∈ eval fuel P g vArg, ∃ vRes, out = .val vRes ∧ (S g).post vArg vRes)
    (x : Int) (e : Expr) :
    ∀ {Q : Int → Prop}, wpCallDec rel μ S cur x e Q → ∃ K, StabAndGood P x e Q K := by
  induction e with
  | lit n =>
    intro Q hwp
    exact ⟨0, ⟨fun _ _ => rfl, fun o ho => ⟨n, by simpa [evalExprWith] using ho, hwp⟩⟩⟩
  | var =>
    intro Q hwp
    exact ⟨0, ⟨fun _ _ => rfl, fun o ho => ⟨x, by simpa [evalExprWith] using ho, hwp⟩⟩⟩
  | add e₁ e₂ ih₁ ih₂ =>
    intro Q hwp
    obtain ⟨k₁, h₁⟩ := ih₁ hwp
    obtain ⟨k₂, hk₂⟩ := exists_uniform_fuel_list
      (R := fun (v₁ : Int) (k : Nat) => StabAndGood P x e₂ (fun v₂ => Q (v₁ + v₂)) k)
      (fun _ _ _ hle h => stabAndGood_mono hle h)
      (fun o ho => by
        obtain ⟨v₁, rfl, hwp₂⟩ := h₁.2 o ho
        exact ⟨v₁, rfl, ih₂ hwp₂⟩)
    let K := max k₁ k₂
    have h₁K := stabAndGood_mono (Nat.le_max_left k₁ k₂) h₁
    refine ⟨K, ⟨fun F hF => ?_, fun o ho => ?_⟩⟩
    · simp only [evalExprWith, h₁K.1 F hF]
      refine list_flatMap_congr_local fun o₁ ho₁ => ?_
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h₂⟩ := hk₂ o₁ ho₁
      have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
      simp only [h₂K.1 F hF]; rfl
    · simp only [evalExprWith, List.mem_flatMap] at ho
      rcases ho with ⟨o₁, ho₁, hr⟩
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h₂⟩ := hk₂ o₁ ho₁
      have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
      simp only [List.mem_map] at hr
      rcases hr with ⟨o₂, ho₂, rfl⟩
      obtain ⟨v₂, rfl, hq⟩ := h₂K.2 o₂ ho₂
      exact ⟨v₁ + v₂, rfl, hq⟩
  | sub e₁ e₂ ih₁ ih₂ =>
    intro Q hwp
    obtain ⟨k₁, h₁⟩ := ih₁ hwp
    obtain ⟨k₂, hk₂⟩ := exists_uniform_fuel_list
      (R := fun (v₁ : Int) (k : Nat) => StabAndGood P x e₂ (fun v₂ => Q (v₁ - v₂)) k)
      (fun _ _ _ hle h => stabAndGood_mono hle h)
      (fun o ho => by
        obtain ⟨v₁, rfl, hwp₂⟩ := h₁.2 o ho
        exact ⟨v₁, rfl, ih₂ hwp₂⟩)
    let K := max k₁ k₂
    have h₁K := stabAndGood_mono (Nat.le_max_left k₁ k₂) h₁
    refine ⟨K, ⟨fun F hF => ?_, fun o ho => ?_⟩⟩
    · simp only [evalExprWith, h₁K.1 F hF]
      refine list_flatMap_congr_local fun o₁ ho₁ => ?_
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h₂⟩ := hk₂ o₁ ho₁
      have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
      simp only [h₂K.1 F hF]; rfl
    · simp only [evalExprWith, List.mem_flatMap] at ho
      rcases ho with ⟨o₁, ho₁, hr⟩
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h₂⟩ := hk₂ o₁ ho₁
      have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
      simp only [List.mem_map] at hr
      rcases hr with ⟨o₂, ho₂, rfl⟩
      obtain ⟨v₂, rfl, hq⟩ := h₂K.2 o₂ ho₂
      exact ⟨v₁ - v₂, rfl, hq⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    intro Q hwp
    obtain ⟨k₁, h₁⟩ := ih₁ hwp
    obtain ⟨k₂, hk₂⟩ := exists_uniform_fuel_list
      (R := fun (v₁ : Int) (k : Nat) => StabAndGood P x e₂ (fun v₂ => Q (v₁ * v₂)) k)
      (fun _ _ _ hle h => stabAndGood_mono hle h)
      (fun o ho => by
        obtain ⟨v₁, rfl, hwp₂⟩ := h₁.2 o ho
        exact ⟨v₁, rfl, ih₂ hwp₂⟩)
    let K := max k₁ k₂
    have h₁K := stabAndGood_mono (Nat.le_max_left k₁ k₂) h₁
    refine ⟨K, ⟨fun F hF => ?_, fun o ho => ?_⟩⟩
    · simp only [evalExprWith, h₁K.1 F hF]
      refine list_flatMap_congr_local fun o₁ ho₁ => ?_
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h₂⟩ := hk₂ o₁ ho₁
      have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
      simp only [h₂K.1 F hF]; rfl
    · simp only [evalExprWith, List.mem_flatMap] at ho
      rcases ho with ⟨o₁, ho₁, hr⟩
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h₂⟩ := hk₂ o₁ ho₁
      have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
      simp only [List.mem_map] at hr
      rcases hr with ⟨o₂, ho₂, rfl⟩
      obtain ⟨v₂, rfl, hq⟩ := h₂K.2 o₂ ho₂
      exact ⟨v₁ * v₂, rfl, hq⟩
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    intro Q hwp
    obtain ⟨k₁, h₁⟩ := ih₁ hwp
    have hBranch : ∀ (v₁ v₂ : Int),
        ((v₁ ≤ v₂ → wpCallDec rel μ S cur x eT Q) ∧ (¬ v₁ ≤ v₂ → wpCallDec rel μ S cur x eE Q)) →
        ∃ kb, StabAndGood P x (if v₁ ≤ v₂ then eT else eE) Q kb := by
      intro v₁ v₂ hbr
      by_cases hle : v₁ ≤ v₂
      · simp only [hle, ite_true]; exact ihT (hbr.1 hle)
      · simp only [hle, ite_false]; exact ihE (hbr.2 hle)
    obtain ⟨k₂, hk₂⟩ := exists_uniform_fuel_list
      (R := fun (v₁ : Int) (k : Nat) =>
        StabAndGood P x e₂
          (fun v₂ => (v₁ ≤ v₂ → wpCallDec rel μ S cur x eT Q) ∧
                     (¬ v₁ ≤ v₂ → wpCallDec rel μ S cur x eE Q)) k ∧
        ∀ o₂ ∈ evalExprWith (eval k P) x e₂,
          ∃ v₂, o₂ = .val v₂ ∧ StabAndGood P x (if v₁ ≤ v₂ then eT else eE) Q k)
      (fun v₁ a b hab ⟨h2a, hba⟩ => by
        refine ⟨stabAndGood_mono hab h2a, fun o₂ ho₂ => ?_⟩
        rw [h2a.1 b hab] at ho₂
        obtain ⟨v₂, rfl, hb⟩ := hba o₂ ho₂
        exact ⟨v₂, rfl, stabAndGood_mono hab hb⟩)
      (fun o₁ ho₁ => by
        obtain ⟨v₁, rfl, hwp₂⟩ := h₁.2 o₁ ho₁
        obtain ⟨ka, h2a⟩ := ih₂ hwp₂
        obtain ⟨kb, hkb⟩ := exists_uniform_fuel_list
          (R := fun (v₂ : Int) (k : Nat) => StabAndGood P x (if v₁ ≤ v₂ then eT else eE) Q k)
          (fun _ _ _ hle h => stabAndGood_mono hle h)
          (fun o₂ ho₂ => by
            obtain ⟨v₂, rfl, hbr⟩ := h2a.2 o₂ ho₂
            exact ⟨v₂, rfl, hBranch v₁ v₂ hbr⟩)
        refine ⟨v₁, rfl, max ka kb, stabAndGood_mono (Nat.le_max_left ka kb) h2a, fun o₂ ho₂ => ?_⟩
        rw [h2a.1 (max ka kb) (Nat.le_max_left ka kb)] at ho₂
        obtain ⟨v₂, rfl, hb⟩ := hkb o₂ ho₂
        exact ⟨v₂, rfl, stabAndGood_mono (Nat.le_max_right ka kb) hb⟩)
    let K := max k₁ k₂
    have h₁K := stabAndGood_mono (Nat.le_max_left k₁ k₂) h₁
    refine ⟨K, ⟨fun F hF => ?_, fun o ho => ?_⟩⟩
    · simp only [evalExprWith, h₁K.1 F hF]
      refine list_flatMap_congr_local fun o₁ ho₁ => ?_
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h2, hbr⟩ := hk₂ o₁ ho₁
      have h2K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h2
      simp only [h2K.1 F hF]
      refine list_flatMap_congr_local fun o₂ ho₂ => ?_
      rw [h2.1 K (Nat.le_max_right k₁ k₂)] at ho₂
      obtain ⟨v₂, rfl, hb⟩ := hbr o₂ ho₂
      have hbK := stabAndGood_mono (Nat.le_max_right k₁ k₂) hb
      have hbf := hbK.1 F hF
      have hbk := hb.1 K (Nat.le_max_right k₁ k₂)
      by_cases hle : v₁ ≤ v₂ <;> simp [hle] at hbf hbk ⊢ <;> rw [hbf]
    · simp only [evalExprWith, List.mem_flatMap] at ho
      rcases ho with ⟨o₁, ho₁, hr⟩
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨v₁, rfl, h2, hbr⟩ := hk₂ o₁ ho₁
      simp only [List.mem_flatMap] at hr
      rcases hr with ⟨o₂, ho₂, hr₂⟩
      rw [h2.1 K (Nat.le_max_right k₁ k₂)] at ho₂
      obtain ⟨v₂, rfl, hb⟩ := hbr o₂ ho₂
      have hbK := stabAndGood_mono (Nat.le_max_right k₁ k₂) hb
      by_cases hle : v₁ ≤ v₂
      · simp only [hle, ite_true] at hbK hr₂
        exact hbK.2 o hr₂
      · simp only [hle, ite_false] at hbK hr₂
        exact hbK.2 o hr₂
  | choose e₁ e₂ ih₁ ih₂ =>
    intro Q hwp
    obtain ⟨k₁, h₁⟩ := ih₁ hwp.1
    obtain ⟨k₂, h₂⟩ := ih₂ hwp.2
    let K := max k₁ k₂
    have h₁K := stabAndGood_mono (Nat.le_max_left k₁ k₂) h₁
    have h₂K := stabAndGood_mono (Nat.le_max_right k₁ k₂) h₂
    refine ⟨K, ⟨fun F hF => ?_, fun o ho => ?_⟩⟩
    · simp only [evalExprWith, h₁K.1 F hF, h₂K.1 F hF]; rfl
    · simp only [evalExprWith, List.mem_append] at ho
      rcases ho with ho₁ | ho₂
      · exact h₁K.2 o ho₁
      · exact h₂K.2 o ho₂
  | call fn eArg ihArg =>
    intro Q hwp
    obtain ⟨k₁, h₁⟩ := ihArg hwp
    obtain ⟨k₂, hk₂⟩ := exists_uniform_fuel_list
      (R := fun (vArg : Int) (k : Nat) =>
        (∀ F, k ≤ F → eval F P fn vArg = eval k P fn vArg) ∧
        (∀ o ∈ eval k P fn vArg, ∃ vRes, o = .val vRes ∧ Q vRes))
      (fun vArg a b hab ⟨hSt, hGd⟩ => by
        have heq := hSt b hab
        refine ⟨fun F hF => by rw [hSt F (Nat.le_trans hab hF), heq], fun o ho => ?_⟩
        rw [heq] at ho
        exact hGd o ho)
      (fun o₁ ho₁ => by
        obtain ⟨vArg, rfl, hrel, hpre, hpost⟩ := h₁.2 o₁ ho₁
        obtain ⟨fc, hfc⟩ := hCalls fn vArg hrel hpre
        have hNoOf : .outOfFuel ∉ eval fc P fn vArg := by
          intro hMem
          obtain ⟨_, heq, _⟩ := hfc .outOfFuel hMem
          cases heq
        refine ⟨vArg, rfl, fc, fun F hF => eval_stabilizes_of_no_outOfFuel fc F hF fn vArg hNoOf,
          fun o ho => ?_⟩
        obtain ⟨vRes, rfl, hp⟩ := hfc o ho
        exact ⟨vRes, rfl, hpost vRes hp⟩)
    let K := max k₁ k₂
    have h₁K := stabAndGood_mono (Nat.le_max_left k₁ k₂) h₁
    refine ⟨K, ⟨fun F hF => ?_, fun o ho => ?_⟩⟩
    · simp only [evalExprWith, h₁K.1 F hF]
      refine list_flatMap_congr_local fun o₁ ho₁ => ?_
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨vArg, rfl, hSt, _⟩ := hk₂ o₁ ho₁
      have hFK := hSt F (Nat.le_trans (Nat.le_max_right k₁ k₂) hF)
      have hKK := hSt K (Nat.le_max_right k₁ k₂)
      dsimp only; rw [hFK, hKK]
    · simp only [evalExprWith, List.mem_flatMap] at ho
      rcases ho with ⟨o₁, ho₁, hr⟩
      rw [h₁.1 K (Nat.le_max_left k₁ k₂)] at ho₁
      obtain ⟨vArg, rfl, hSt, hGd⟩ := hk₂ o₁ ho₁
      dsimp only at hr; rw [hSt K (Nat.le_max_right k₁ k₂)] at hr
      exact hGd o hr

/-- **Assume-guarantee rule for total correctness with a well-founded call measure.**
With a well-founded relation `rel` and a call measure `μ` that strictly decreases across
every call in `wpCallDec`, interface completeness and per-function modular verification
yield whole-program total correctness (a uniform finite fuel bound per argument). -/
theorem ag_total_correctness_of_wf_call_measure {α : Type} {rel : α → α → Prop}
    {μ : Fname → Int → α} {P : Module} {S : SpecEnv}
    (hwf : WellFounded rel)
    (hImpl : SpecsImplemented P S)
    (hVer : ModuleVerifiedTotal rel μ P S S) :
    ProgramTotalCorrect P S := by
  have hMain : ∀ a : α, ∀ fn x, μ fn x = a → (S fn).pre x →
      ∃ fuel, ∀ out, HasBehavior fn P fuel x out → ∃ v, out = .val v ∧ (S fn).post x v := by
    intro a
    induction a using hwf.induction with
    | h cur ih =>
      intro fn x hcur hpre
      subst hcur
      have hDef : P.Defines fn := hImpl fn x hpre
      obtain ⟨body, hlu⟩ : ∃ body, P.lookup fn = some body := by
        cases h : P.lookup fn with
        | none => simp [Module.Defines, h] at hDef
        | some b => exact ⟨b, rfl⟩
      have hwp := hVer fn body hlu x hpre
      obtain ⟨K, _, hGd⟩ := wpCallDec_sound_evalExprWith (P := P) (S := S)
        (fun g vArg hrel hp => ih (μ g vArg) hrel g vArg rfl hp) x body hwp
      refine ⟨K + 1, fun out hout => ?_⟩
      simp only [HasBehavior, eval, hlu] at hout
      exact hGd out hout
  intro fn x hpre
  exact hMain (μ fn x) fn x rfl hpre

/-- Linked-module corollary of the total-correctness rule. -/
theorem link_ag_total_correctness_of_wf_call_measure {α : Type} {rel : α → α → Prop}
    {μ : Fname → Int → α} {M₁ M₂ : Module} {S : SpecEnv}
    (hwf : WellFounded rel)
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hVer₁ : ModuleVerifiedTotal rel μ M₁ S S)
    (hVer₂ : ModuleVerifiedTotal rel μ M₂ S S) :
    ProgramTotalCorrect (link M₁ M₂) S := by
  refine ag_total_correctness_of_wf_call_measure (μ := μ) hwf hImpl ?_
  intro fn body hlu
  rw [lookup_link] at hlu
  cases hm₁ : M₁.lookup fn with
  | some b₁ =>
    rw [hm₁] at hlu
    injection hlu with heq
    subst heq
    exact hVer₁ fn b₁ hm₁
  | none =>
    rw [hm₁] at hlu
    exact hVer₂ fn body hlu

/-! ## Specification refinement at link time -/

/-- **Spec refinement at link time, for callers with internal (recursive) calls.**
A caller module `M` is verified against its own guarantee `G`, assuming `G` for calls to
its own functions and the external interface `S` for all other calls (`mixEnv M G S`).
Then `M` composes with any disjoint callee module `N` that is partially correct for a spec
`S'` refining `S` at every name `M` does not define (weaker precondition, postcondition
strengthened under the precondition): every function of `M` is partially correct for `G`
in `link M N`. -/
theorem verified_recursive_caller_links_with_refined_callee
    {M N : Module} {S S' G : SpecEnv}
    (hLink : Linkable M N)
    (hVerM : ModuleVerifiedPartial M (mixEnv M G S) G)
    (hSatN : ProgramPartialCorrect N S')
    (hWeak : ∀ g, ¬ M.Defines g → WeakensPre (S g) (S' g))
    (hStrong : ∀ g, ¬ M.Defines g → StrengthensPostUnderPre (S g) (S' g)) :
    ∀ f, M.Defines f → FnPartialCorrect (link M N) f (G f) := by
  intro f hf fuel
  induction fuel generalizing f with
  | zero =>
    intro x out _ h
    left
    simpa [HasBehavior, eval] using h
  | succ n ih =>
    intro x out hpre hbeh
    obtain ⟨body, hM⟩ : ∃ body, M.lookup f = some body := by
      cases h : M.lookup f with
      | none => simp [Module.Defines, h] at hf
      | some b => exact ⟨b, rfl⟩
    have hMN : (link M N).lookup f = some body := by simp [lookup_link, hM]
    have hbehBody : out ∈ evalExprWith (eval n (link M N)) x body := by
      simpa [HasBehavior, eval, hMN] using hbeh
    refine wpPartial_sound_evalExprWith (A := mixEnv M G S) ?_
      (hVerM f body hM x hpre) out hbehBody
    intro g vArg o hpreA ho
    by_cases hg : M.Defines g
    · have hA : mixEnv M G S g = G g := by simp [mixEnv, hg]
      rw [hA] at hpreA ⊢
      exact ih g hg vArg o hpreA ho
    · have hA : mixEnv M G S g = S g := by simp [mixEnv, hg]
      rw [hA] at hpreA ⊢
      have hS'gPre := hWeak g hg vArg hpreA
      have hNoUndef : .undefinedCall ∉ eval n N g vArg := by
        intro hMem
        rcases hSatN g n vArg .undefinedCall hS'gPre hMem with h1 | ⟨_, h2, _⟩
        · cases h1
        · cases h2
      rw [eval_link_right_of_no_undefinedCall hLink n g vArg hNoUndef] at ho
      rcases hSatN g n vArg o hS'gPre ho with rfl | ⟨vRes, rfl, hS'Post⟩
      · exact .inl rfl
      · exact .inr ⟨vRes, rfl, hStrong g hg vArg vRes hpreA hS'Post⟩

/-- The flat variant (callee assumptions `S` for *every* call, refinement required at
every name). It follows from `verified_recursive_caller_links_with_refined_callee`;
its hypotheses force `(S f).pre` to be unsatisfiable at every `f` that `M` defines
(`caller_spec_unsat_on_own_symbols`), so it only covers callers that make no verifiable
call to their own functions. -/
theorem verified_flat_caller_links_with_refined_callee {M N : Module} {S S' G : SpecEnv}
    (hLink : Linkable M N)
    (hVerM : ModuleVerifiedPartial M S G)
    (hSatN : ProgramPartialCorrect N S')
    (hWeak : ∀ g, WeakensPre (S g) (S' g))
    (hStrong : ∀ g, StrengthensPostUnderPre (S g) (S' g)) :
    ∀ f, M.Defines f → FnPartialCorrect (link M N) f (G f) := by
  have hUnsat := caller_spec_unsat_on_own_symbols hLink hSatN hWeak
  refine verified_recursive_caller_links_with_refined_callee hLink ?_ hSatN
    (fun g _ => hWeak g) (fun g _ => hStrong g)
  refine moduleVerifiedPartial_mono_assume (A := S) ?_ ?_ hVerM
  · intro g x hx
    by_cases hg : M.Defines g
    · exact absurd hx (hUnsat g hg x)
    · show (mixEnv M G S g).pre x
      rw [show mixEnv M G S g = S g by simp [mixEnv, hg]]; exact hx
  · intro g x v hx hv
    by_cases hg : M.Defines g
    · exact absurd hx (hUnsat g hg x)
    · rw [show mixEnv M G S g = S g by simp [mixEnv, hg]] at hv; exact hv

/-! ## Separate compilation -/

/-- **Separate compilation preserves verifiability (and hence partial correctness).**
If a per-module pass `compile` maps modules verified against the interface `S` to
modules verified against `S` (`PreservesVerifiedPartial`) and keeps every defined name
(`PreservesDefines`), then compiling two verified modules separately and linking them
gives a program that is partially correct for `S`. No behavioural relation between the
compiled and the source program is claimed (see
`Cex.cex_verifiability_preservation_not_behavioural`). -/
theorem separate_compilation_partial_correct_of_preserves_verified
    {M₁ M₂ : Module} {S : SpecEnv} {compile : Module → Module}
    (hVer₁ : ModuleVerifiedPartial M₁ S S)
    (hVer₂ : ModuleVerifiedPartial M₂ S S)
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hPresVer : PreservesVerifiedPartial compile S)
    (hPresDef : PreservesDefines compile) :
    ProgramPartialCorrect (link (compile M₁) (compile M₂)) S :=
  link_ag_partial_correctness (specsImplemented_link_compile hImpl hPresDef)
    (hPresVer M₁ hVer₁) (hPresVer M₂ hVer₂)

/-- **Separate compilation as behavioural refinement.** If a per-module pass is a
contextual refinement on every module (`PassCtxRefines`), then linking separately
compiled disjoint modules contextually refines linking the sources. -/
theorem separate_compilation_ctxRefines_of_pass_ctxRefines
    {M₁ M₂ : Module} {compile : Module → Module}
    (hPass : PassCtxRefines compile) (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link (compile M₁) (compile M₂)) :=
  ctxRefines_link_congr (hPass M₁) (hPass M₂) hLink

/-- Corollary: under a contextually refining pass, partial correctness of the linked
source program transfers to the linked compiled program (for the same specs). -/
theorem separate_compilation_preserves_partial_correctness_of_pass_ctxRefines
    {M₁ M₂ : Module} {S : SpecEnv} {compile : Module → Module}
    (hPass : PassCtxRefines compile) (hLink : Linkable M₁ M₂)
    (hSrc : ProgramPartialCorrect (link M₁ M₂) S) :
    ProgramPartialCorrect (link (compile M₁) (compile M₂)) S := fun fn =>
  entryRefines_preserves_fnPartialCorrect
    (standaloneRefines_of_ctxRefines
      (separate_compilation_ctxRefines_of_pass_ctxRefines hPass hLink) fn) (hSrc fn)

end Toy.Link
