import ToyLink.Spec

/-!
# Structural lemmas, fuel monotonicity, and derivable-hypothesis facts

Provides fully proved supporting lemmas about module linking, evaluator congruence
and totality, fuel monotonicity and stabilization, total-implies-partial correctness,
domain observability (`ctxRefines_sameDom`), WP monotonicity, and single-frame WP
soundness.
-/

namespace Toy.Link

/-! ## Module lookup and linking algebra -/

theorem lookup_link (M₁ M₂ : Module) (fn : Fname) :
    (link M₁ M₂).lookup fn =
      match M₁.lookup fn with
      | some body => some body
      | none => M₂.lookup fn := by
  induction M₁ with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [link, List.cons_append, Module.lookup]
    by_cases hk : k = fn
    · simp [hk]
    · simp only [hk, ite_false]
      exact ih

theorem defines_link_iff (M₁ M₂ : Module) (fn : Fname) :
    (link M₁ M₂).Defines fn ↔ M₁.Defines fn ∨ M₂.Defines fn := by
  simp only [Module.Defines, lookup_link]
  cases h₁ : M₁.lookup fn <;> simp [Option.isSome]

theorem defines_of_lookup_some {M : Module} {fn : Fname} {body : Expr}
    (h : M.lookup fn = some body) : M.Defines fn := by
  simp [Module.Defines, h]

theorem lookup_none_of_not_defines {M : Module} {fn : Fname}
    (h : ¬ M.Defines fn) : M.lookup fn = none := by
  simp only [Module.Defines] at h
  cases hl : M.lookup fn with
  | none => rfl
  | some b => simp [hl] at h

theorem linkable_symm {M₁ M₂ : Module} (h : Linkable M₁ M₂) : Linkable M₂ M₁ :=
  fun fn ⟨h₂, h₁⟩ => h fn ⟨h₁, h₂⟩

theorem linkable_link_iff (C M₁ M₂ : Module) :
    Linkable C (link M₁ M₂) ↔ Linkable C M₁ ∧ Linkable C M₂ := by
  constructor
  · intro h
    refine ⟨fun fn ⟨hc, h₁⟩ => h fn ⟨hc, (defines_link_iff M₁ M₂ fn).2 (.inl h₁)⟩,
            fun fn ⟨hc, h₂⟩ => h fn ⟨hc, (defines_link_iff M₁ M₂ fn).2 (.inr h₂)⟩⟩
  · rintro ⟨h₁, h₂⟩ fn ⟨hc, hm⟩
    rcases (defines_link_iff M₁ M₂ fn).1 hm with hm₁ | hm₂
    · exact h₁ fn ⟨hc, hm₁⟩
    · exact h₂ fn ⟨hc, hm₂⟩

theorem linkable_of_sameDom_right {M M' C : Module} (hs : SameDom M M')
    (h : Linkable C M) : Linkable C M' :=
  fun fn ⟨hc, hm'⟩ => h fn ⟨hc, (hs fn).2 hm'⟩

theorem linkable_iff_of_sameDom {M M' C : Module} (hs : SameDom M M') :
    Linkable C M ↔ Linkable C M' :=
  ⟨linkable_of_sameDom_right hs, linkable_of_sameDom_right (fun fn => (hs fn).symm)⟩

theorem lookup_link_comm {M₁ M₂ : Module} (h : Linkable M₁ M₂) (fn : Fname) :
    (link M₁ M₂).lookup fn = (link M₂ M₁).lookup fn := by
  simp only [lookup_link]
  cases h₁ : M₁.lookup fn <;> cases h₂ : M₂.lookup fn <;> simp
  exact absurd ⟨defines_of_lookup_some h₁, defines_of_lookup_some h₂⟩ (h fn)

theorem lookup_link_assoc (M₁ M₂ M₃ : Module) (fn : Fname) :
    (link (link M₁ M₂) M₃).lookup fn = (link M₁ (link M₂ M₃)).lookup fn := by
  simp only [lookup_link]
  cases M₁.lookup fn <;> simp

theorem sameDom_link_congr {M₁ M₁' M₂ M₂' : Module}
    (hs₁ : SameDom M₁ M₁') (hs₂ : SameDom M₂ M₂') :
    SameDom (link M₁ M₂) (link M₁' M₂') := by
  intro fn
  simp only [defines_link_iff, hs₁ fn, hs₂ fn]

theorem linkable_of_sameDom_both {M₁ M₁' M₂ M₂' : Module}
    (hs₁ : SameDom M₁ M₁') (hs₂ : SameDom M₂ M₂') (h : Linkable M₁ M₂) :
    Linkable M₁' M₂' :=
  fun fn ⟨h₁', h₂'⟩ => h fn ⟨(hs₁ fn).2 h₁', (hs₂ fn).2 h₂'⟩

/-! ## Evaluator congruence, non-emptiness, and domain observability -/

theorem evalExprWith_congr {f g : Fname → Int → List Outcome}
    (hfg : ∀ fn arg, f fn arg = g fn arg) (x : Int) (e : Expr) :
    evalExprWith f x e = evalExprWith g x e := by
  induction e with
  | lit _ => rfl
  | var => rfl
  | add e₁ e₂ ih₁ ih₂ => simp only [evalExprWith, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ => simp only [evalExprWith, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp only [evalExprWith, ih₁, ih₂]
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE => simp only [evalExprWith, ih₁, ih₂, ihT, ihE]
  | choose e₁ e₂ ih₁ ih₂ => simp only [evalExprWith, ih₁, ih₂]
  | call fn eArg ih =>
    simp only [evalExprWith, ih]
    congr 1
    funext o
    cases o <;> simp [hfg]

theorem eval_congr_lookup {P₁ P₂ : Module}
    (hl : ∀ fn, P₁.lookup fn = P₂.lookup fn) (fuel : Nat) (fn : Fname) (arg : Int) :
    eval fuel P₁ fn arg = eval fuel P₂ fn arg := by
  induction fuel generalizing fn arg with
  | zero => rfl
  | succ n ih =>
    simp only [eval, hl fn]
    cases P₂.lookup fn with
    | none => rfl
    | some body => exact evalExprWith_congr ih arg body

theorem entryRefines_of_lookup_eq {P₁ P₂ : Module}
    (hl : ∀ fn, P₁.lookup fn = P₂.lookup fn) (entry : Fname) :
    EntryRefines entry P₁ P₂ := by
  intro fuel arg out h
  simpa [HasBehavior, eval_congr_lookup hl fuel entry arg] using h

theorem evalExprWith_mono_mem {f g : Fname → Int → List Outcome}
    (hfg : ∀ fn arg o, o ∈ f fn arg → o ∈ g fn arg)
    (x : Int) (e : Expr) {o : Outcome}
    (ho : o ∈ evalExprWith f x e) : o ∈ evalExprWith g x e := by
  induction e generalizing o with
  | lit _ => exact ho
  | var => exact ho
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at ho ⊢
    rcases ho with ⟨o₁, ho₁, hr⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hr
      rcases hr with ⟨o₂, ho₂, rfl⟩
      exact ⟨.val v₁, ih₁ ho₁, List.mem_map.2 ⟨o₂, ih₂ ho₂, rfl⟩⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.undefinedCall, ih₁ ho₁, by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.outOfFuel, ih₁ ho₁, by simp⟩
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at ho ⊢
    rcases ho with ⟨o₁, ho₁, hr⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hr
      rcases hr with ⟨o₂, ho₂, rfl⟩
      exact ⟨.val v₁, ih₁ ho₁, List.mem_map.2 ⟨o₂, ih₂ ho₂, rfl⟩⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.undefinedCall, ih₁ ho₁, by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.outOfFuel, ih₁ ho₁, by simp⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at ho ⊢
    rcases ho with ⟨o₁, ho₁, hr⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hr
      rcases hr with ⟨o₂, ho₂, rfl⟩
      exact ⟨.val v₁, ih₁ ho₁, List.mem_map.2 ⟨o₂, ih₂ ho₂, rfl⟩⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.undefinedCall, ih₁ ho₁, by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.outOfFuel, ih₁ ho₁, by simp⟩
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    simp only [evalExprWith, List.mem_flatMap] at ho ⊢
    rcases ho with ⟨o₁, ho₁, hr⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_flatMap] at hr
      rcases hr with ⟨o₂, ho₂, hr₂⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁, List.mem_flatMap.2 ⟨.val v₂, ih₂ ho₂, ?_⟩⟩
        by_cases hle : v₁ ≤ v₂
        · simp only [hle, ite_true] at hr₂ ⊢; exact ihT hr₂
        · simp only [hle, ite_false] at hr₂ ⊢; exact ihE hr₂
      | undefinedCall =>
        simp only [List.mem_singleton] at hr₂; subst hr₂
        exact ⟨.val v₁, ih₁ ho₁, List.mem_flatMap.2 ⟨.undefinedCall, ih₂ ho₂, by simp⟩⟩
      | outOfFuel =>
        simp only [List.mem_singleton] at hr₂; subst hr₂
        exact ⟨.val v₁, ih₁ ho₁, List.mem_flatMap.2 ⟨.outOfFuel, ih₂ ho₂, by simp⟩⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.undefinedCall, ih₁ ho₁, by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.outOfFuel, ih₁ ho₁, by simp⟩
  | choose e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_append] at ho ⊢
    rcases ho with h₁ | h₂
    · exact .inl (ih₁ h₁)
    · exact .inr (ih₂ h₂)
  | call fn eArg ihArg =>
    simp only [evalExprWith, List.mem_flatMap] at ho ⊢
    rcases ho with ⟨o₁, ho₁, hr⟩
    cases o₁ with
    | val vArg => exact ⟨.val vArg, ihArg ho₁, hfg fn vArg o hr⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.undefinedCall, ihArg ho₁, by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨.outOfFuel, ihArg ho₁, by simp⟩

theorem ctxRefines_of_pointwise_body_subset {M M' : Module}
    (hBody : ∀ fn,
      (M.lookup fn = M'.lookup fn) ∨
      (∃ b b', M.lookup fn = some b ∧ M'.lookup fn = some b' ∧
        ∀ f₁ f₂ : Fname → Int → List Outcome,
          (∀ g a o, o ∈ f₂ g a → o ∈ f₁ g a) →
          ∀ x o, o ∈ evalExprWith f₂ x b' → o ∈ evalExprWith f₁ x b)) :
    CtxRefines M M' := by
  intro C hC₁ hC₂ entry fuel arg out hOut
  induction fuel generalizing entry arg out with
  | zero => simpa [HasBehavior, eval] using hOut
  | succ n ih =>
    simp only [HasBehavior, eval] at hOut ⊢
    rw [lookup_link] at hOut ⊢
    cases hClu : C.lookup entry with
    | some cbody =>
      rw [hClu] at hOut
      exact evalExprWith_mono_mem ih arg cbody hOut
    | none =>
      rw [hClu] at hOut
      rcases hBody entry with heq | ⟨b, b', hm, hm', hsub⟩
      · rw [heq]
        cases hlu : M'.lookup entry with
        | none =>
          rw [hlu] at hOut
          exact hOut
        | some body =>
          rw [hlu] at hOut
          exact evalExprWith_mono_mem ih arg body hOut
      · rw [hm'] at hOut
        rw [hm]
        exact hsub (eval n (link C M)) (eval n (link C M')) ih arg out hOut

private theorem list_flatMap_nonempty {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs ≠ []) (hf : ∀ a ∈ xs, f a ≠ []) : xs.flatMap f ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons a rest =>
    simp only [List.flatMap_cons]
    intro hnil
    have hfa := hf a (List.Mem.head _)
    cases hfa_eq : f a with
    | nil => exact hfa hfa_eq
    | cons _ _ => simp [hfa_eq] at hnil

private theorem list_flatMap_congr {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ a ∈ xs, f a = g a) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.Mem.head _), ih (fun a ha => h a (List.Mem.tail _ ha))]

theorem evalExprWith_nonempty {callFn : Fname → Int → List Outcome}
    (hcall : ∀ fn arg, callFn fn arg ≠ []) (x : Int) (e : Expr) :
    evalExprWith callFn x e ≠ [] := by
  induction e with
  | lit _ => simp [evalExprWith]
  | var => simp [evalExprWith]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith]
    refine list_flatMap_nonempty ih₁ fun o _ => ?_
    cases o <;> simp [ih₂]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith]
    refine list_flatMap_nonempty ih₁ fun o _ => ?_
    cases o <;> simp [ih₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith]
    refine list_flatMap_nonempty ih₁ fun o _ => ?_
    cases o <;> simp [ih₂]
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    simp only [evalExprWith]
    refine list_flatMap_nonempty ih₁ fun o₁ _ => ?_
    cases o₁ with
    | val v₁ =>
      refine list_flatMap_nonempty ih₂ fun o₂ _ => ?_
      cases o₂ with
      | val v₂ =>
        by_cases hle : v₁ ≤ v₂ <;> simp [hle, ihT, ihE]
      | undefinedCall => simp
      | outOfFuel => simp
    | undefinedCall => simp
    | outOfFuel => simp
  | choose e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith]
    intro hnil
    cases h₁ : evalExprWith callFn x e₁ with
    | nil => exact ih₁ h₁
    | cons _ _ => simp [h₁] at hnil
  | call fn eArg ih =>
    simp only [evalExprWith]
    refine list_flatMap_nonempty ih fun o _ => ?_
    cases o with
    | val vArg => exact hcall fn vArg
    | undefinedCall => simp
    | outOfFuel => simp

theorem eval_nonempty (fuel : Nat) (P : Module) (fn : Fname) (arg : Int) :
    eval fuel P fn arg ≠ [] := by
  induction fuel generalizing fn arg with
  | zero => simp [eval]
  | succ n ih =>
    simp only [eval]
    cases P.lookup fn with
    | none => simp
    | some body => exact evalExprWith_nonempty ih arg body

theorem evalExprWith_zero_no_undefinedCall (P : Module) (x : Int) (e : Expr) :
    .undefinedCall ∉ evalExprWith (eval 0 P) x e := by
  induction e with
  | lit _ => simp [evalExprWith]
  | var => simp [evalExprWith]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap, not_exists, not_and]
    intro o ho
    cases o with
    | val v₁ =>
      simp only [List.mem_map, not_exists, not_and]
      intro o₂ ho₂ heq
      cases o₂ with
      | val _ => cases heq
      | undefinedCall => exact ih₂ ho₂
      | outOfFuel => cases heq
    | undefinedCall => exact absurd ho ih₁
    | outOfFuel => simp
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap, not_exists, not_and]
    intro o ho
    cases o with
    | val v₁ =>
      simp only [List.mem_map, not_exists, not_and]
      intro o₂ ho₂ heq
      cases o₂ with
      | val _ => cases heq
      | undefinedCall => exact ih₂ ho₂
      | outOfFuel => cases heq
    | undefinedCall => exact absurd ho ih₁
    | outOfFuel => simp
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap, not_exists, not_and]
    intro o ho
    cases o with
    | val v₁ =>
      simp only [List.mem_map, not_exists, not_and]
      intro o₂ ho₂ heq
      cases o₂ with
      | val _ => cases heq
      | undefinedCall => exact ih₂ ho₂
      | outOfFuel => cases heq
    | undefinedCall => exact absurd ho ih₁
    | outOfFuel => simp
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    simp only [evalExprWith, List.mem_flatMap, not_exists, not_and]
    intro o₁ ho₁
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_flatMap, not_exists, not_and]
      intro o₂ ho₂
      cases o₂ with
      | val v₂ =>
        by_cases hle : v₁ ≤ v₂
        · simpa [hle] using ihT
        · simpa [hle] using ihE
      | undefinedCall => exact absurd ho₂ ih₂
      | outOfFuel => simp
    | undefinedCall => exact absurd ho₁ ih₁
    | outOfFuel => simp
  | choose e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_append, not_or]
    exact ⟨ih₁, ih₂⟩
  | call fn eArg ih =>
    simp only [evalExprWith, List.mem_flatMap, not_exists, not_and]
    intro o ho
    cases o with
    | val vArg => simp [eval]
    | undefinedCall => exact absurd ho ih
    | outOfFuel => simp

theorem eval_one_undefinedCall_iff (P : Module) (fn : Fname) (arg : Int) :
    .undefinedCall ∈ eval 1 P fn arg ↔ ¬ P.Defines fn := by
  simp only [eval, Module.Defines]
  cases hl : P.lookup fn with
  | none => simp [Option.isSome]
  | some body =>
    simp only [Option.isSome, not_true_eq_false, iff_false]
    exact evalExprWith_zero_no_undefinedCall P arg body

/-! ## Derivable-hypothesis lemmas: domain equality and link soundness -/

/-- Any two modules related by `CtxRefines` must define the exact same set of
function names (`SameDom`). Proof: probe the empty context `[]` at `fuel = 1`. -/
theorem ctxRefines_sameDom {M M' : Module} (h : CtxRefines M M') : SameDom M M' := by
  intro fn
  have hEmptyM : Linkable ([] : Module) M := fun _ ⟨h1, _⟩ => by simp [Module.Defines, Module.lookup] at h1
  have hEmptyM' : Linkable ([] : Module) M' := fun _ ⟨h1, _⟩ => by simp [Module.Defines, Module.lookup] at h1
  have hClosed := h [] hEmptyM hEmptyM' fn
  have hLinkM : link ([] : Module) M = M := rfl
  have hLinkM' : link ([] : Module) M' = M' := rfl
  rw [hLinkM, hLinkM'] at hClosed
  constructor
  · intro hm
    by_cases hm' : M'.Defines fn
    · exact hm'
    · exfalso
      have hUndef' : HasBehavior fn M' 1 0 .undefinedCall :=
        (eval_one_undefinedCall_iff M' fn 0).2 hm'
      have hUndef : HasBehavior fn M 1 0 .undefinedCall := hClosed 1 0 .undefinedCall hUndef'
      exact (eval_one_undefinedCall_iff M fn 0).1 hUndef hm
  · intro hm'
    by_cases hm : M.Defines fn
    · exact hm
    · exfalso
      cases hne : eval 1 M' fn 0 with
      | nil => exact absurd hne (eval_nonempty 1 M' fn 0)
      | cons out _ =>
        have hIn' : HasBehavior fn M' 1 0 out := by simp [HasBehavior, hne]
        have hIn : HasBehavior fn M 1 0 out := hClosed 1 0 out hIn'
        have hM : eval 1 M fn 0 = [.undefinedCall] := by
          simp [eval, lookup_none_of_not_defines hm]
        have hout : out = .undefinedCall := by
          simpa [HasBehavior, hM] using hIn
        subst hout
        have hInUndef' : .undefinedCall ∈ eval 1 M' fn 0 := by simp [hne]
        exact (eval_one_undefinedCall_iff M' fn 0).1 hInUndef' hm'

/-- `ProgramPartialCorrect N S'` automatically entails `SpecsImplemented N S'` because an
unimplemented function produces `.undefinedCall` at `fuel = 1`. -/
theorem programPartialCorrect_implies_specsImplemented {N : Module} {S' : SpecEnv}
    (hSat : ProgramPartialCorrect N S') : SpecsImplemented N S' := by
  intro fn x hpre
  by_cases hdef : N.Defines fn
  · exact hdef
  · exfalso
    have hUndef : HasBehavior fn N 1 x .undefinedCall :=
      (eval_one_undefinedCall_iff N fn x).2 hdef
    rcases hSat fn 1 x .undefinedCall hpre hUndef with h1 | ⟨_, h2, _⟩
    · cases h1
    · cases h2

private theorem evalExprWith_eq_of_avoid {bad : Outcome} (hBadNotVal : ∀ v, bad ≠ .val v)
    {f g : Fname → Int → List Outcome}
    (hfg : ∀ fn arg, bad ∉ g fn arg → f fn arg = g fn arg)
    (x : Int) (e : Expr) (hNoBad : bad ∉ evalExprWith g x e) :
    evalExprWith f x e = evalExprWith g x e := by
  induction e with
  | lit _ => rfl
  | var => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    have h1 : bad ∉ evalExprWith g x e₁ := by
      intro hMem
      apply hNoBad
      simp only [evalExprWith, List.mem_flatMap]
      refine ⟨bad, hMem, ?_⟩
      cases hbad : bad with
      | val v => exact absurd hbad (hBadNotVal v)
      | undefinedCall => simp
      | outOfFuel => simp
    have heq1 := ih₁ h1
    simp only [evalExprWith, heq1]
    refine list_flatMap_congr fun o₁ ho₁ => ?_
    cases o₁ with
    | val v₁ =>
      have h2 : bad ∉ evalExprWith g x e₂ := by
        intro hMem
        apply hNoBad
        simp only [evalExprWith, List.mem_flatMap]
        refine ⟨.val v₁, ho₁, List.mem_map.2 ⟨bad, hMem, ?_⟩⟩
        cases hbad : bad with
        | val v => exact absurd hbad (hBadNotVal v)
        | undefinedCall => rfl
        | outOfFuel => rfl
      rw [ih₂ h2]
    | undefinedCall => rfl
    | outOfFuel => rfl
  | sub e₁ e₂ ih₁ ih₂ =>
    have h1 : bad ∉ evalExprWith g x e₁ := by
      intro hMem
      apply hNoBad
      simp only [evalExprWith, List.mem_flatMap]
      refine ⟨bad, hMem, ?_⟩
      cases hbad : bad with
      | val v => exact absurd hbad (hBadNotVal v)
      | undefinedCall => simp
      | outOfFuel => simp
    have heq1 := ih₁ h1
    simp only [evalExprWith, heq1]
    refine list_flatMap_congr fun o₁ ho₁ => ?_
    cases o₁ with
    | val v₁ =>
      have h2 : bad ∉ evalExprWith g x e₂ := by
        intro hMem
        apply hNoBad
        simp only [evalExprWith, List.mem_flatMap]
        refine ⟨.val v₁, ho₁, List.mem_map.2 ⟨bad, hMem, ?_⟩⟩
        cases hbad : bad with
        | val v => exact absurd hbad (hBadNotVal v)
        | undefinedCall => rfl
        | outOfFuel => rfl
      rw [ih₂ h2]
    | undefinedCall => rfl
    | outOfFuel => rfl
  | mul e₁ e₂ ih₁ ih₂ =>
    have h1 : bad ∉ evalExprWith g x e₁ := by
      intro hMem
      apply hNoBad
      simp only [evalExprWith, List.mem_flatMap]
      refine ⟨bad, hMem, ?_⟩
      cases hbad : bad with
      | val v => exact absurd hbad (hBadNotVal v)
      | undefinedCall => simp
      | outOfFuel => simp
    have heq1 := ih₁ h1
    simp only [evalExprWith, heq1]
    refine list_flatMap_congr fun o₁ ho₁ => ?_
    cases o₁ with
    | val v₁ =>
      have h2 : bad ∉ evalExprWith g x e₂ := by
        intro hMem
        apply hNoBad
        simp only [evalExprWith, List.mem_flatMap]
        refine ⟨.val v₁, ho₁, List.mem_map.2 ⟨bad, hMem, ?_⟩⟩
        cases hbad : bad with
        | val v => exact absurd hbad (hBadNotVal v)
        | undefinedCall => rfl
        | outOfFuel => rfl
      rw [ih₂ h2]
    | undefinedCall => rfl
    | outOfFuel => rfl
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    have h1 : bad ∉ evalExprWith g x e₁ := by
      intro hMem
      apply hNoBad
      simp only [evalExprWith, List.mem_flatMap]
      refine ⟨bad, hMem, ?_⟩
      cases hbad : bad with
      | val v => exact absurd hbad (hBadNotVal v)
      | undefinedCall => simp
      | outOfFuel => simp
    have heq1 := ih₁ h1
    simp only [evalExprWith, heq1]
    refine list_flatMap_congr fun o₁ ho₁ => ?_
    cases o₁ with
    | val v₁ =>
      have h2 : bad ∉ evalExprWith g x e₂ := by
        intro hMem
        apply hNoBad
        simp only [evalExprWith, List.mem_flatMap]
        refine ⟨.val v₁, ho₁, List.mem_flatMap.2 ⟨bad, hMem, ?_⟩⟩
        cases hbad : bad with
        | val v => exact absurd hbad (hBadNotVal v)
        | undefinedCall => simp
        | outOfFuel => simp
      rw [ih₂ h2]
      refine list_flatMap_congr fun o₂ ho₂ => ?_
      cases o₂ with
      | val v₂ =>
        by_cases hle : v₁ ≤ v₂
        · simp only [hle, ite_true]
          refine ihT fun hMem => hNoBad ?_
          simp only [evalExprWith, List.mem_flatMap]
          exact ⟨.val v₁, ho₁, List.mem_flatMap.2 ⟨.val v₂, ho₂, by simpa [hle] using hMem⟩⟩
        · simp only [hle, ite_false]
          refine ihE fun hMem => hNoBad ?_
          simp only [evalExprWith, List.mem_flatMap]
          exact ⟨.val v₁, ho₁, List.mem_flatMap.2 ⟨.val v₂, ho₂, by simpa [hle] using hMem⟩⟩
      | undefinedCall => rfl
      | outOfFuel => rfl
    | undefinedCall => rfl
    | outOfFuel => rfl
  | choose e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_append, not_or] at hNoBad ⊢
    rw [ih₁ hNoBad.1, ih₂ hNoBad.2]
  | call fn eArg ihArg =>
    have hArg : bad ∉ evalExprWith g x eArg := by
      intro hMem
      apply hNoBad
      simp only [evalExprWith, List.mem_flatMap]
      refine ⟨bad, hMem, ?_⟩
      cases hbad : bad with
      | val v => exact absurd hbad (hBadNotVal v)
      | undefinedCall => simp
      | outOfFuel => simp
    simp only [evalExprWith, ihArg hArg]
    refine list_flatMap_congr fun o ho => ?_
    cases o with
    | val vArg =>
      refine hfg fn vArg fun hMem => hNoBad ?_
      simp only [evalExprWith, List.mem_flatMap]
      exact ⟨.val vArg, ho, hMem⟩
    | undefinedCall => rfl
    | outOfFuel => rfl

/-- If `N` evaluates `fn(arg)` at `fuel` without hitting `.undefinedCall`, then prepending
any disjoint module `M` (`Linkable M N`) leaves `eval fuel (link M N) fn arg` unchanged. -/
theorem eval_link_right_of_no_undefinedCall {M N : Module} (hLink : Linkable M N) :
    ∀ fuel fn arg, .undefinedCall ∉ eval fuel N fn arg →
      eval fuel (link M N) fn arg = eval fuel N fn arg := by
  intro fuel
  induction fuel with
  | zero =>
    intro fn arg _
    rfl
  | succ n ih =>
    intro fn arg hNoUndef
    simp only [eval] at hNoUndef ⊢
    cases hN : N.lookup fn with
    | none =>
      exfalso
      apply hNoUndef
      simp [hN]
    | some body =>
      have hDefN : N.Defines fn := defines_of_lookup_some hN
      have hNotM : ¬ M.Defines fn := fun hDefM => hLink fn ⟨hDefM, hDefN⟩
      have hM : M.lookup fn = none := lookup_none_of_not_defines hNotM
      have hMN : (link M N).lookup fn = some body := by
        simp [lookup_link, hM, hN]
      rw [hMN]
      exact evalExprWith_eq_of_avoid (bad := .undefinedCall) (fun _ h => by cases h)
        ih arg body (by simpa [hN] using hNoUndef)

/-! ## Fuel monotonicity, stabilization, and total-implies-partial correctness -/

theorem evalExprWith_mono_non_outOfFuel {f g : Fname → Int → List Outcome}
    (hfg : ∀ fn arg out, out ∈ f fn arg → out ≠ .outOfFuel → out ∈ g fn arg)
    (x : Int) (e : Expr) {out : Outcome}
    (hout : out ∈ evalExprWith f x e) (hne : out ≠ .outOfFuel) :
    out ∈ evalExprWith g x e := by
  induction e generalizing out with
  | lit n => simpa [evalExprWith] using hout
  | var => simpa [evalExprWith] using hout
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.val v₂, ih₂ ho₂ (by simp), rfl⟩⟩
      | undefinedCall =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.undefinedCall, ih₂ ho₂ (by simp), rfl⟩⟩
      | outOfFuel => exact absurd rfl hne
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.undefinedCall, ih₁ ho₁ (by simp), by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.val v₂, ih₂ ho₂ (by simp), rfl⟩⟩
      | undefinedCall =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.undefinedCall, ih₂ ho₂ (by simp), rfl⟩⟩
      | outOfFuel => exact absurd rfl hne
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.undefinedCall, ih₁ ho₁ (by simp), by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.val v₂, ih₂ ho₂ (by simp), rfl⟩⟩
      | undefinedCall =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.undefinedCall, ih₂ ho₂ (by simp), rfl⟩⟩
      | outOfFuel => exact absurd rfl hne
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.undefinedCall, ih₁ ho₁ (by simp), by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_flatMap] at hrest
      rcases hrest with ⟨o₂, ho₂, hrest2⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_flatMap.2 ⟨.val v₂, ih₂ ho₂ (by simp), ?_⟩⟩
        by_cases hle : v₁ ≤ v₂
        · simp only [hle, ite_true] at hrest2 ⊢
          exact ihT hrest2 hne
        · simp only [hle, ite_false] at hrest2 ⊢
          exact ihE hrest2 hne
      | undefinedCall =>
        simp only [List.mem_singleton] at hrest2
        subst hrest2
        exact ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_flatMap.2 ⟨.undefinedCall, ih₂ ho₂ (by simp), by simp⟩⟩
      | outOfFuel =>
        simp only [List.mem_singleton] at hrest2
        exact absurd hrest2.symm (Ne.symm hne)
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.undefinedCall, ih₁ ho₁ (by simp), by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | choose e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_append] at hout ⊢
    rcases hout with h₁ | h₂
    · exact .inl (ih₁ h₁ hne)
    · exact .inr (ih₂ h₂ hne)
  | call fn eArg ihArg =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o, ho, hrest⟩
    cases o with
    | val vArg =>
      exact ⟨.val vArg, ihArg ho (by simp), hfg fn vArg out hrest hne⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.undefinedCall, ihArg ho (by simp), by simp⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)

theorem eval_mono_non_outOfFuel {P : Module} {fuel fuel' : Nat} (hle : fuel ≤ fuel') :
    ∀ fn arg out, out ∈ eval fuel P fn arg → out ≠ .outOfFuel → out ∈ eval fuel' P fn arg := by
  induction fuel generalizing fuel' with
  | zero =>
    intro fn arg out hout hne
    simp only [eval, List.mem_singleton] at hout
    exact absurd hout hne
  | succ n ih =>
    intro fn arg out hout hne
    cases fuel' with
    | zero => omega
    | succ m =>
      have hnm : n ≤ m := by omega
      simp only [eval] at hout ⊢
      cases hlu : P.lookup fn with
      | none => simpa [hlu] using hout
      | some body =>
        rw [hlu] at hout
        exact evalExprWith_mono_non_outOfFuel (fun g v o => ih hnm g v o) arg body hout hne

theorem eval_stabilizes_of_no_outOfFuel {P : Module} :
    ∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ → ∀ fn arg,
      .outOfFuel ∉ eval fuel₁ P fn arg →
      eval fuel₂ P fn arg = eval fuel₁ P fn arg := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
    intro fuel₂ _ fn arg hNo
    exfalso
    exact hNo (by simp [eval])
  | succ n ih =>
    intro fuel₂ hle fn arg hNo
    cases fuel₂ with
    | zero => omega
    | succ m =>
      have hnm : n ≤ m := by omega
      simp only [eval] at hNo ⊢
      cases hlu : P.lookup fn with
      | none => rfl
      | some body =>
        rw [hlu] at hNo
        exact evalExprWith_eq_of_avoid (bad := .outOfFuel) (fun _ h => by cases h)
          (fun g v => ih m hnm g v) arg body hNo

theorem fnTotalCorrect_implies_fnPartialCorrect {P : Module} {fn : Fname} {spec : FnSpec}
    (hTot : FnTotalCorrect P fn spec) : FnPartialCorrect P fn spec := by
  intro fuel x out hpre hbeh
  by_cases hof : out = .outOfFuel
  · exact .inl hof
  · right
    obtain ⟨fuel', hTot'⟩ := hTot x hpre
    have hNoOf : .outOfFuel ∉ eval fuel' P fn x := by
      intro hMem
      rcases hTot' .outOfFuel hMem with ⟨_, hEq, _⟩
      cases hEq
    have hbehMax : HasBehavior fn P (max fuel fuel') x out :=
      eval_mono_non_outOfFuel (Nat.le_max_left fuel fuel') fn x out hbeh hof
    have hStab : eval (max fuel fuel') P fn x = eval fuel' P fn x :=
      eval_stabilizes_of_no_outOfFuel fuel' (max fuel fuel') (Nat.le_max_right fuel fuel') fn x hNoOf
    have hbeh' : HasBehavior fn P fuel' x out := by
      simpa [HasBehavior, hStab] using hbehMax
    exact hTot' out hbeh'

theorem programTotalCorrect_implies_programPartialCorrect {P : Module} {S : SpecEnv}
    (hTot : ProgramTotalCorrect P S) : ProgramPartialCorrect P S :=
  fun fn => fnTotalCorrect_implies_fnPartialCorrect (hTot fn)

/-! ## WP monotonicity, soundness over a single frame, and module linking -/

theorem wpPartial_mono_post {A : SpecEnv} {x : Int} {e : Expr} {Q Q' : Int → Prop}
    (hQQ' : ∀ v, Q v → Q' v) (h : wpPartial A x e Q) : wpPartial A x e Q' := by
  induction e generalizing Q Q' with
  | lit _ => exact hQQ' _ h
  | var => exact hQQ' _ h
  | add e₁ e₂ ih₁ ih₂ =>
    exact ih₁ (fun v₁ h₁ => ih₂ (fun v₂ h₂ => hQQ' _ h₂) h₁) h
  | sub e₁ e₂ ih₁ ih₂ =>
    exact ih₁ (fun v₁ h₁ => ih₂ (fun v₂ h₂ => hQQ' _ h₂) h₁) h
  | mul e₁ e₂ ih₁ ih₂ =>
    exact ih₁ (fun v₁ h₁ => ih₂ (fun v₂ h₂ => hQQ' _ h₂) h₁) h
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    exact ih₁ (fun v₁ h₁ => ih₂ (fun v₂ ⟨hT, hE⟩ =>
      ⟨fun hle => ihT hQQ' (hT hle), fun hle => ihE hQQ' (hE hle)⟩) h₁) h
  | choose e₁ e₂ ih₁ ih₂ =>
    exact ⟨ih₁ hQQ' h.1, ih₂ hQQ' h.2⟩
  | call fn eArg ihArg =>
    exact ihArg (fun vArg ⟨hpre, hpost⟩ => ⟨hpre, fun vRes hres => hQQ' _ (hpost vRes hres)⟩) h

theorem wpPartial_mono_assume {A A' : SpecEnv}
    (hWeak : ∀ g, WeakensPre (A g) (A' g))
    (hStrong : ∀ g, StrengthensPostUnderPre (A g) (A' g))
    {x : Int} {e : Expr} {Q : Int → Prop}
    (h : wpPartial A x e Q) : wpPartial A' x e Q := by
  induction e generalizing Q with
  | lit _ => exact h
  | var => exact h
  | add e₁ e₂ ih₁ ih₂ =>
    exact ih₁ (wpPartial_mono_post (fun _ => ih₂) h)
  | sub e₁ e₂ ih₁ ih₂ =>
    exact ih₁ (wpPartial_mono_post (fun _ => ih₂) h)
  | mul e₁ e₂ ih₁ ih₂ =>
    exact ih₁ (wpPartial_mono_post (fun _ => ih₂) h)
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    exact ih₁ (wpPartial_mono_post (fun _ h₂ => ih₂ (wpPartial_mono_post (fun _ ⟨hT, hE⟩ =>
      ⟨fun hle => ihT (hT hle), fun hle => ihE (hE hle)⟩) h₂)) h)
  | choose e₁ e₂ ih₁ ih₂ =>
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | call fn eArg ihArg =>
    refine ihArg (wpPartial_mono_post (fun vArg ⟨hpre, hpost⟩ => ?_) h)
    exact ⟨hWeak fn vArg hpre, fun vRes hres' => hpost vRes (hStrong fn vArg vRes hpre hres')⟩

theorem moduleVerifiedPartial_mono_assume {M : Module} {A A' G : SpecEnv}
    (hWeak : ∀ g, WeakensPre (A g) (A' g))
    (hStrong : ∀ g, StrengthensPostUnderPre (A g) (A' g))
    (hVer : ModuleVerifiedPartial M A G) : ModuleVerifiedPartial M A' G :=
  fun fn body hlu x hpre => wpPartial_mono_assume hWeak hStrong (hVer fn body hlu x hpre)

theorem wpPartial_sound_evalExprWith {A : SpecEnv} {callFn : Fname → Int → List Outcome}
    (hCalls : ∀ g vArg o, (A g).pre vArg → o ∈ callFn g vArg →
      o = .outOfFuel ∨ ∃ vRes, o = .val vRes ∧ (A g).post vArg vRes)
    {x : Int} {e : Expr} {Q : Int → Prop}
    (hwp : wpPartial A x e Q) :
    ∀ out ∈ evalExprWith callFn x e, out = .outOfFuel ∨ ∃ v, out = .val v ∧ Q v := by
  induction e generalizing Q with
  | lit n =>
    intro out ho
    simp only [evalExprWith, List.mem_singleton] at ho
    subst ho
    exact .inr ⟨n, rfl, hwp⟩
  | var =>
    intro out ho
    simp only [evalExprWith, List.mem_singleton] at ho
    subst ho
    exact .inr ⟨x, rfl, hwp⟩
  | add e₁ e₂ ih₁ ih₂ =>
    intro out ho
    simp only [evalExprWith, List.mem_flatMap] at ho
    rcases ho with ⟨o₁, ho₁, hrest⟩
    rcases ih₁ hwp o₁ ho₁ with rfl | ⟨v₁, rfl, hwp₂⟩
    · simp only [List.mem_singleton] at hrest
      exact .inl hrest
    · simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      rcases ih₂ hwp₂ o₂ ho₂ with rfl | ⟨v₂, rfl, hq⟩
      · exact .inl rfl
      · exact .inr ⟨v₁ + v₂, rfl, hq⟩
  | sub e₁ e₂ ih₁ ih₂ =>
    intro out ho
    simp only [evalExprWith, List.mem_flatMap] at ho
    rcases ho with ⟨o₁, ho₁, hrest⟩
    rcases ih₁ hwp o₁ ho₁ with rfl | ⟨v₁, rfl, hwp₂⟩
    · simp only [List.mem_singleton] at hrest
      exact .inl hrest
    · simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      rcases ih₂ hwp₂ o₂ ho₂ with rfl | ⟨v₂, rfl, hq⟩
      · exact .inl rfl
      · exact .inr ⟨v₁ - v₂, rfl, hq⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    intro out ho
    simp only [evalExprWith, List.mem_flatMap] at ho
    rcases ho with ⟨o₁, ho₁, hrest⟩
    rcases ih₁ hwp o₁ ho₁ with rfl | ⟨v₁, rfl, hwp₂⟩
    · simp only [List.mem_singleton] at hrest
      exact .inl hrest
    · simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      rcases ih₂ hwp₂ o₂ ho₂ with rfl | ⟨v₂, rfl, hq⟩
      · exact .inl rfl
      · exact .inr ⟨v₁ * v₂, rfl, hq⟩
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    intro out ho
    simp only [evalExprWith, List.mem_flatMap] at ho
    rcases ho with ⟨o₁, ho₁, hrest⟩
    rcases ih₁ hwp o₁ ho₁ with rfl | ⟨v₁, rfl, hwp₂⟩
    · simp only [List.mem_singleton] at hrest
      exact .inl hrest
    · simp only [List.mem_flatMap] at hrest
      rcases hrest with ⟨o₂, ho₂, hrest2⟩
      rcases ih₂ hwp₂ o₂ ho₂ with rfl | ⟨v₂, rfl, ⟨hT, hE⟩⟩
      · simp only [List.mem_singleton] at hrest2
        exact .inl hrest2
      · by_cases hle : v₁ ≤ v₂
        · simp only [hle, ite_true] at hrest2
          exact ihT (hT hle) out hrest2
        · simp only [hle, ite_false] at hrest2
          exact ihE (hE hle) out hrest2
  | choose e₁ e₂ ih₁ ih₂ =>
    intro out ho
    simp only [evalExprWith, List.mem_append] at ho
    rcases ho with h₁ | h₂
    · exact ih₁ hwp.1 out h₁
    · exact ih₂ hwp.2 out h₂
  | call fn eArg ihArg =>
    intro out ho
    simp only [evalExprWith, List.mem_flatMap] at ho
    rcases ho with ⟨o, ho, hrest⟩
    rcases ihArg hwp o ho with rfl | ⟨vArg, rfl, ⟨hpre, hpost⟩⟩
    · simp only [List.mem_singleton] at hrest
      exact .inl hrest
    · rcases hCalls fn vArg out hpre hrest with rfl | ⟨vRes, rfl, hres⟩
      · exact .inl rfl
      · exact .inr ⟨vRes, rfl, hpost vRes hres⟩

theorem moduleVerifiedPartial_link {M₁ M₂ : Module} {A G : SpecEnv}
    (h₁ : ModuleVerifiedPartial M₁ A G) (h₂ : ModuleVerifiedPartial M₂ A G) :
    ModuleVerifiedPartial (link M₁ M₂) A G := by
  intro fn body hlu
  rw [lookup_link] at hlu
  cases hm₁ : M₁.lookup fn with
  | some b =>
    rw [hm₁] at hlu
    injection hlu with heq
    subst heq
    exact h₁ fn b hm₁
  | none =>
    rw [hm₁] at hlu
    exact h₂ fn body hlu

theorem specsImplemented_link_compile {M₁ M₂ : Module} {S : SpecEnv}
    {compile : Module → Module}
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hPres : PreservesDefines compile) :
    SpecsImplemented (link (compile M₁) (compile M₂)) S := by
  intro fn x hpre
  rcases (defines_link_iff M₁ M₂ fn).1 (hImpl fn x hpre) with hm₁ | hm₂
  · exact (defines_link_iff (compile M₁) (compile M₂) fn).2 (.inl (hPres M₁ fn hm₁))
  · exact (defines_link_iff (compile M₁) (compile M₂) fn).2 (.inr (hPres M₂ fn hm₂))

/-! ## Standalone versus contextual behaviour; closed modules -/

/-- The empty module is linkable with every module. -/
theorem linkable_nil (M : Module) : Linkable [] M :=
  fun _ ⟨h, _⟩ => by simp [Module.Defines, Module.lookup] at h

theorem evalExprWith_mono_non_undefinedCall {f g : Fname → Int → List Outcome}
    (hfg : ∀ fn arg out, out ∈ f fn arg → out ≠ .undefinedCall → out ∈ g fn arg)
    (x : Int) (e : Expr) {out : Outcome}
    (hout : out ∈ evalExprWith f x e) (hne : out ≠ .undefinedCall) :
    out ∈ evalExprWith g x e := by
  induction e generalizing out with
  | lit n => simpa [evalExprWith] using hout
  | var => simpa [evalExprWith] using hout
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.val v₂, ih₂ ho₂ (by simp), rfl⟩⟩
      | outOfFuel =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.outOfFuel, ih₂ ho₂ (by simp), rfl⟩⟩
      | undefinedCall => exact absurd rfl hne
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.outOfFuel, ih₁ ho₁ (by simp), by simp⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.val v₂, ih₂ ho₂ (by simp), rfl⟩⟩
      | outOfFuel =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.outOfFuel, ih₂ ho₂ (by simp), rfl⟩⟩
      | undefinedCall => exact absurd rfl hne
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.outOfFuel, ih₁ ho₁ (by simp), by simp⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hrest
      rcases hrest with ⟨o₂, ho₂, rfl⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.val v₂, ih₂ ho₂ (by simp), rfl⟩⟩
      | outOfFuel =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_map.2 ⟨.outOfFuel, ih₂ ho₂ (by simp), rfl⟩⟩
      | undefinedCall => exact absurd rfl hne
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.outOfFuel, ih₁ ho₁ (by simp), by simp⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o₁, ho₁, hrest⟩
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_flatMap] at hrest
      rcases hrest with ⟨o₂, ho₂, hrest2⟩
      cases o₂ with
      | val v₂ =>
        refine ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_flatMap.2 ⟨.val v₂, ih₂ ho₂ (by simp), ?_⟩⟩
        by_cases hle : v₁ ≤ v₂
        · simp only [hle, ite_true] at hrest2 ⊢
          exact ihT hrest2 hne
        · simp only [hle, ite_false] at hrest2 ⊢
          exact ihE hrest2 hne
      | outOfFuel =>
        simp only [List.mem_singleton] at hrest2
        subst hrest2
        exact ⟨.val v₁, ih₁ ho₁ (by simp), List.mem_flatMap.2 ⟨.outOfFuel, ih₂ ho₂ (by simp), by simp⟩⟩
      | undefinedCall =>
        simp only [List.mem_singleton] at hrest2
        exact absurd hrest2.symm (Ne.symm hne)
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.outOfFuel, ih₁ ho₁ (by simp), by simp⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)
  | choose e₁ e₂ ih₁ ih₂ =>
    simp only [evalExprWith, List.mem_append] at hout ⊢
    rcases hout with h₁ | h₂
    · exact .inl (ih₁ h₁ hne)
    · exact .inr (ih₂ h₂ hne)
  | call fn eArg ihArg =>
    simp only [evalExprWith, List.mem_flatMap] at hout ⊢
    rcases hout with ⟨o, ho, hrest⟩
    cases o with
    | val vArg =>
      exact ⟨.val vArg, ihArg ho (by simp), hfg fn vArg out hrest hne⟩
    | outOfFuel =>
      simp only [List.mem_singleton] at hrest
      subst hrest
      exact ⟨.outOfFuel, ihArg ho (by simp), by simp⟩
    | undefinedCall =>
      simp only [List.mem_singleton] at hrest
      exact absurd hrest.symm (Ne.symm hne)


/-- Linking a disjoint context `C` in front of `M` keeps every outcome of `M` other than
`undefinedCall`: whatever `M` computes without reaching an unresolved name, it still
computes when the context supplies those names. -/
theorem eval_link_superset_non_undefinedCall {C M : Module} (hC : Linkable C M) :
    ∀ fuel fn arg out, out ∈ eval fuel M fn arg → out ≠ .undefinedCall →
      out ∈ eval fuel (link C M) fn arg := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h _; simpa [eval] using h
  | succ n ih =>
    intro fn arg out hout hne
    simp only [eval] at hout ⊢
    cases hm : M.lookup fn with
    | none =>
      rw [hm] at hout
      simp only [List.mem_singleton] at hout
      exact absurd hout hne
    | some body =>
      rw [hm] at hout
      have hCn : C.lookup fn = none :=
        lookup_none_of_not_defines (fun hc => hC fn ⟨hc, defines_of_lookup_some hm⟩)
      have hl : (link C M).lookup fn = some body := by simp [lookup_link, hCn, hm]
      rw [hl]
      exact evalExprWith_mono_non_undefinedCall (fun g a o h h' => ih g a o h h') arg body
        hout hne

/-- Congruence of `evalExprWith` restricted to the callees that syntactically occur. -/
theorem evalExprWith_congr_on {P : Fname → Prop} {f g : Fname → Int → List Outcome}
    (hfg : ∀ fn arg, P fn → f fn arg = g fn arg) (x : Int) :
    ∀ e : Expr, e.CalleesIn P → evalExprWith f x e = evalExprWith g x e := by
  intro e
  induction e with
  | lit _ => intro _; rfl
  | var => intro _; rfl
  | add e₁ e₂ ih₁ ih₂ => intro h; simp only [evalExprWith, ih₁ h.1, ih₂ h.2]
  | sub e₁ e₂ ih₁ ih₂ => intro h; simp only [evalExprWith, ih₁ h.1, ih₂ h.2]
  | mul e₁ e₂ ih₁ ih₂ => intro h; simp only [evalExprWith, ih₁ h.1, ih₂ h.2]
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    intro h; simp only [evalExprWith, ih₁ h.1, ih₂ h.2.1, ihT h.2.2.1, ihE h.2.2.2]
  | choose e₁ e₂ ih₁ ih₂ => intro h; simp only [evalExprWith, ih₁ h.1, ih₂ h.2]
  | call fn eArg ih =>
    intro h
    simp only [evalExprWith, ih h.2]
    congr 1
    funext o
    cases o <;> simp [hfg fn _ h.1]

/-- A closed module's own functions are unaffected by any disjoint context. -/
theorem eval_link_closed {C M : Module} (hC : Linkable C M) (hM : ClosedModule M) :
    ∀ n g v, M.Defines g → eval n (link C M) g v = eval n M g v := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro g v hg
    obtain ⟨body, hlu⟩ : ∃ body, M.lookup g = some body := by
      cases h : M.lookup g with
      | none => simp [Module.Defines, h] at hg
      | some b => exact ⟨b, rfl⟩
    have hCg : C.lookup g = none :=
      lookup_none_of_not_defines (fun hc => hC g ⟨hc, hg⟩)
    have hL : (link C M).lookup g = some body := by simp [lookup_link, hCg, hlu]
    simp only [eval, hL, hlu]
    exact evalExprWith_congr_on (P := M.Defines) (fun fn arg hfn => ih fn arg hfn) v body
      (hM g body hlu)

/-- If every callee that syntactically occurs in `e` avoids `undefinedCall`, so does `e`. -/
theorem evalExprWith_no_undefinedCall {P : Fname → Prop} {f : Fname → Int → List Outcome}
    (hf : ∀ fn arg, P fn → .undefinedCall ∉ f fn arg) (x : Int) :
    ∀ e : Expr, e.CalleesIn P → .undefinedCall ∉ evalExprWith f x e := by
  intro e
  induction e with
  | lit _ => intro _; simp [evalExprWith]
  | var => intro _; simp [evalExprWith]
  | add e₁ e₂ ih₁ ih₂ =>
    intro h hm
    simp only [evalExprWith, List.mem_flatMap] at hm
    obtain ⟨o₁, ho₁, hr⟩ := hm
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hr
      obtain ⟨o₂, ho₂, he⟩ := hr
      cases o₂ with
      | val _ => cases he
      | undefinedCall => exact ih₂ h.2 ho₂
      | outOfFuel => cases he
    | undefinedCall => exact ih₁ h.1 ho₁
    | outOfFuel => simp at hr
  | sub e₁ e₂ ih₁ ih₂ =>
    intro h hm
    simp only [evalExprWith, List.mem_flatMap] at hm
    obtain ⟨o₁, ho₁, hr⟩ := hm
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hr
      obtain ⟨o₂, ho₂, he⟩ := hr
      cases o₂ with
      | val _ => cases he
      | undefinedCall => exact ih₂ h.2 ho₂
      | outOfFuel => cases he
    | undefinedCall => exact ih₁ h.1 ho₁
    | outOfFuel => simp at hr
  | mul e₁ e₂ ih₁ ih₂ =>
    intro h hm
    simp only [evalExprWith, List.mem_flatMap] at hm
    obtain ⟨o₁, ho₁, hr⟩ := hm
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_map] at hr
      obtain ⟨o₂, ho₂, he⟩ := hr
      cases o₂ with
      | val _ => cases he
      | undefinedCall => exact ih₂ h.2 ho₂
      | outOfFuel => cases he
    | undefinedCall => exact ih₁ h.1 ho₁
    | outOfFuel => simp at hr
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    intro h hm
    simp only [evalExprWith, List.mem_flatMap] at hm
    obtain ⟨o₁, ho₁, hr⟩ := hm
    cases o₁ with
    | val v₁ =>
      simp only [List.mem_flatMap] at hr
      obtain ⟨o₂, ho₂, hr2⟩ := hr
      cases o₂ with
      | val v₂ =>
        by_cases hle : v₁ ≤ v₂
        · simp only [hle, ite_true] at hr2; exact ihT h.2.2.1 hr2
        · simp only [hle, ite_false] at hr2; exact ihE h.2.2.2 hr2
      | undefinedCall => exact ih₂ h.2.1 ho₂
      | outOfFuel => simp at hr2
    | undefinedCall => exact ih₁ h.1 ho₁
    | outOfFuel => simp at hr
  | choose e₁ e₂ ih₁ ih₂ =>
    intro h hm
    simp only [evalExprWith, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ih₁ h.1 hm
    · exact ih₂ h.2 hm
  | call fn eArg ih =>
    intro h hm
    simp only [evalExprWith, List.mem_flatMap] at hm
    obtain ⟨o, ho, hr⟩ := hm
    cases o with
    | val v => exact hf fn v h.1 hr
    | undefinedCall => exact ih h.2 ho
    | outOfFuel => simp at hr

/-- A closed module never reaches an unresolved name from a function it defines. -/
theorem closedModule_no_undefinedCall {M : Module} (hM : ClosedModule M) :
    ∀ fuel fn arg, M.Defines fn → .undefinedCall ∉ eval fuel M fn arg := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; simp [eval]
  | succ n ih =>
    intro fn arg hdef
    obtain ⟨body, hlu⟩ : ∃ body, M.lookup fn = some body := by
      cases h : M.lookup fn with
      | none => simp [Module.Defines, h] at hdef
      | some b => exact ⟨b, rfl⟩
    simp only [eval, hlu]
    exact evalExprWith_no_undefinedCall (P := M.Defines) (fun g a hg => ih g a hg) arg body
      (hM fn body hlu)

/-- Standalone refinement at every entry already forces equal domains
(probe each name with the empty context at fuel `1`). -/
theorem sameDom_of_standaloneRefines {M M' : Module} (h : StandaloneRefines M M') :
    SameDom M M' := by
  intro fn
  constructor
  · intro hm
    by_cases hm' : M'.Defines fn
    · exact hm'
    · exfalso
      have hU' : HasBehavior fn M' 1 0 .undefinedCall :=
        (eval_one_undefinedCall_iff M' fn 0).2 hm'
      exact (eval_one_undefinedCall_iff M fn 0).1 (h fn 1 0 _ hU') hm
  · intro hm'
    by_cases hm : M.Defines fn
    · exact hm
    · exfalso
      cases hne : eval 1 M' fn 0 with
      | nil => exact absurd hne (eval_nonempty 1 M' fn 0)
      | cons out _ =>
        have hIn : HasBehavior fn M 1 0 out := h fn 1 0 out (by simp [HasBehavior, hne])
        have hM : eval 1 M fn 0 = [.undefinedCall] := by
          simp [eval, lookup_none_of_not_defines hm]
        have hout : out = .undefinedCall := by simpa [HasBehavior, hM] using hIn
        subst hout
        exact (eval_one_undefinedCall_iff M' fn 0).1 (by simp [hne]) hm'

/-- Contextual refinement implies standalone refinement (take the empty context). -/
theorem standaloneRefines_of_ctxRefines {M M' : Module} (h : CtxRefines M M') :
    StandaloneRefines M M' :=
  fun entry => h [] (linkable_nil M) (linkable_nil M') entry

/-- Behavioural refinement transports partial correctness from source to target. -/
theorem entryRefines_preserves_fnPartialCorrect {P P' : Module} {fn : Fname}
    {spec : FnSpec} (hRef : EntryRefines fn P P') (hP : FnPartialCorrect P fn spec) :
    FnPartialCorrect P' fn spec :=
  fun fuel x out hpre hbeh => hP fuel x out hpre (hRef fuel x out hbeh)

/-- Under the hypotheses of the flat spec-refinement rule (`∀ g`, not only external `g`),
the assumed interface `S` has an unsatisfiable precondition at every function the caller
`M` defines; hence `M` can make no verifiable call to any of its own functions. -/
theorem caller_spec_unsat_on_own_symbols {M N : Module} {S S' : SpecEnv}
    (hLink : Linkable M N) (hSatN : ProgramPartialCorrect N S')
    (hWeak : ∀ g, WeakensPre (S g) (S' g)) :
    ∀ f, M.Defines f → ∀ x, ¬ (S f).pre x := fun f hf x hx =>
  hLink f ⟨hf, programPartialCorrect_implies_specsImplemented hSatN f x (hWeak f x hx)⟩

end Toy.Link
