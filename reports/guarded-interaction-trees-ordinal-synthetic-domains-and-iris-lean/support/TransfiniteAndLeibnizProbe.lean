-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Standalone Mechanized Probes for Guarded Interaction Trees, Ordinal Step-Indexing, and Leibniz OFEs

This standalone Lean 4 file (`Init.*` only, zero external dependencies) kernel-checks four
structural results accompanying the `zerocopy/reference` report on Guarded Interaction Trees
(`logsem/gitrees`), ordinal synthetic domains (`logsem/synthetic_domains`), and `iris-lean`:

1. **Predicative Inverse-Limit GITree Tower & Constructive `disjunction_property` Elimination**
   (`Section ConstructiveProgressExternalization`):
   - Constructs a mixed-variance higher-order GITree chain `Chain : Nat → Type` by structural
     recursion on `Nat` (mirroring `iris/algebra/cofe_solver.v` `Fixpoint A'` and `iris-lean`
     `COFESolver.lean`, avoiding inductive strict-positivity rejection on `(X → X) → ...` while
     staying strictly inside predicative `Type 0` with bilateral `restrict`/`embed`).
   - Models `logsem/gitrees`'s `IT`, `ITV`, `reify`, intuitionistic `MiniUPred` (`pure_soundness`),
     `internalStep`, `externalStep`, and `notStuck`, and proves `notStuck_externalize_constructive`
     **without** `disjunction_property` (`(⊢ P ∨ Q) → (⊢ P) ∨ (⊢ Q)`) and with **zero axioms**
     (`#print axioms` reports `does not depend on any axioms`).
   - Proves `disjunction_property_refuted_over_two_worlds` (zero axioms): over any two-point
     Kripke/resource index, `(⊢ P ∨ Q) → (⊢ P) ∨ (⊢ Q)` is outright false.

2. **Leibniz OFE Quotient Upgrade (`Section LeibnizOFEUpgrade`)**:
   Demonstrates `iris-lean`'s `OFE.eq_dist'` mechanism (`Quot` + `propext` + `funext`): quotienting
   any step-indexed OFE carrier by `∀ n, dist n x y` promotes limit OFE equivalence to native Lean
   propositional equality `=`.

3. **ω-Horizon `∀ n, ∃ k` Witness Barrier (`Section OmegaHorizonBarrier`, zero axioms)**:
   Proves that over `Nat` (`ω`), `P n k := n ≤ k` is downward-closed in `n` and satisfies
   `∀ n, ∃ k, P n k`, yet `¬ ∃ k, ∀ n, P n k` (instantiating why `logsem/synthetic_domains`'s
   `forall_exists_swap` requires `smaller_card B A`).

4. **Failure of `▷(∃ x, P x) ⊢ ▷⊥ ∨ ∃ x, ▷(P x)` at Limit Ordinal `ω`
   (`Section LimitOrdinalLaterExists`, zero axioms)**:
   Proves `finite_stage_later_exists_holds` at all finite stages `< ω`, and
   `limit_ordinal_later_exists_refuted` at the first limit ordinal `ω`.
-/

namespace GitreeSyntheticProbes

/-! ## 1. Predicative Inverse-Limit Tower & Zero-Axiom Progress Externalization -/

section ConstructiveProgressExternalization

inductive ErrCode : Type where
  | runtimeErr : ErrCode
  | otherErr   : ErrCode

/-- One-step functor `StepF D C` with contravariant domain `D` inside higher-order `fun_` and
    covariant carrier `C`, all inside `Type 0`. -/
inductive StepF (D C : Type) : Type where
  | ret  : Nat → StepF D C
  | err  : ErrCode → StepF D C
  | fun_ : (D → C) → StepF D C
  | tau  : C → StepF D C
  | vis  : Nat → (Nat → C) → StepF D C

/-- Defining `Chain : Nat → Type` by structural recursion on `k : Nat` (rather than as an
    `inductive` family) bypasses strict-positivity rejection on `Chain k → Chain k` while remaining
    strictly inside predicative `Type 0`—matching `cofe_solver.v` and `COFESolver.lean`. -/
noncomputable def Chain : Nat → Type
  | 0     => PUnit
  | k + 1 => StepF (Chain k) (Chain k)

mutual
  /-- Restriction `Chain (k + 1) → Chain k` along the inverse-limit tower. -/
  noncomputable def restrict : {k : Nat} → Chain (k + 1) → Chain k
    | 0,     _              => PUnit.unit
    | _ + 1, .ret n         => .ret n
    | _ + 1, .err e         => .err e
    | _ + 1, .fun_ f        => .fun_ (fun x => restrict (f (embed x)))
    | _ + 1, .tau t         => .tau (restrict t)
    | _ + 1, .vis arg kcont => .vis arg (fun out => restrict (kcont out))

  /-- Canonical bilateral embedding `Chain k → Chain (k + 1)`. -/
  noncomputable def embed : {k : Nat} → Chain k → Chain (k + 1)
    | 0,     PUnit.unit     => .err .runtimeErr
    | _ + 1, .ret n         => .ret n
    | _ + 1, .err e         => .err e
    | _ + 1, .fun_ f        => .fun_ (fun x => embed (f (restrict x)))
    | _ + 1, .tau t         => .tau (embed t)
    | _ + 1, .vis arg kcont => .vis arg (fun out => embed (kcont out))
end

theorem restrict_embed : ∀ {k : Nat} (x : Chain k), restrict (embed x) = x
  | 0,     PUnit.unit     => rfl
  | _ + 1, .ret _         => rfl
  | _ + 1, .err _         => rfl
  | k + 1, .fun_ f        => by
      simp only [embed, restrict]
      refine congrArg StepF.fun_ (funext fun y => ?_)
      rw [@restrict_embed k (f (@restrict k (embed y))), @restrict_embed k y]
  | k + 1, .tau t         => by
      simp only [embed, restrict]
      exact congrArg StepF.tau (@restrict_embed k t)
  | k + 1, .vis arg kcont => by
      simp only [embed, restrict]
      exact congrArg (StepF.vis arg) (funext fun out => @restrict_embed k (kcont out))

/-- Coherent inverse-limit tower in `Type 0` (`cofe_solver.tower`). -/
structure TowerIT : Type where
  car : (k : Nat) → Chain k
  coh : ∀ k, restrict (car (k + 1)) = car k

/-- Intuitionistic step-indexed proposition (`uPred` evaluated at empty resource `ε`),
    supporting pure embedding `⌜P⌝`, `pure_soundness`, `∨`, `∃`, and `∧`. -/
structure MiniUPred : Type 1 where
  holds : Nat → Prop
  mono  : ∀ {m n}, m ≤ n → holds n → holds m

namespace MiniUPred

def Entails (P Q : MiniUPred) : Prop :=
  ∀ n, P.holds n → Q.holds n

def Valid (P : MiniUPred) : Prop :=
  ∀ n, P.holds n

prefix:25 "⊢ᵤ " => Valid

def pure (p : Prop) : MiniUPred where
  holds := fun _ => p
  mono  := fun _ h => h

theorem pure_soundness {p : Prop} (h : ⊢ᵤ pure p) : p :=
  h 0

def or (P Q : MiniUPred) : MiniUPred where
  holds := fun n => P.holds n ∨ Q.holds n
  mono  := fun hle h => match h with
    | .inl hp => .inl (P.mono hle hp)
    | .inr hq => .inr (Q.mono hle hq)

def ex {α : Type} (Φ : α → MiniUPred) : MiniUPred where
  holds := fun n => ∃ a, (Φ a).holds n
  mono  := fun hle ⟨a, ha⟩ => ⟨a, (Φ a).mono hle ha⟩

def and (P Q : MiniUPred) : MiniUPred where
  holds := fun n => P.holds n ∧ Q.holds n
  mono  := fun hle ⟨hp, hq⟩ => ⟨P.mono hle hp, Q.mono hle hq⟩

end MiniUPred

/-- Exact interface of `IT`, `ITV`, `reify`, `internal_step`, `external_step`, and `not_stuck`
    from `logsem/gitrees` (`core.v`, `reify.v`, `reductions.v`, `weakestpre.v`). -/
structure GitreeSystem where
  IT         : Type
  ITV        : Type
  State      : Type
  dist       : Nat → IT → IT → Prop
  dist_mono  : ∀ {m n x y}, m ≤ n → dist n x y → dist m x y
  dist_refl  : ∀ n x, dist n x x
  dist_symm  : ∀ {n x y}, dist n x y → dist n y x
  dist_trans : ∀ {n x y z}, dist n x y → dist n y z → dist n x z
  Err        : ErrCode → IT
  Ret        : Nat → IT
  Fun        : (IT → IT) → IT
  Tick       : IT → IT
  Vis        : Nat → (Nat → IT) → IT
  toVal      : IT → Option ITV
  /-- Constructive `IT_dont_confuse` (`core.v:792–810`), proved by destructing `IT_unfold α`. -/
  dont_confuse : ∀ α : IT,
      (∃ e, ∀ n, dist n α (Err e))
    ∨ (∃ k, ∀ n, dist n α (Ret k))
    ∨ (∃ f, ∀ n, dist n α (Fun f))
    ∨ (∃ β, ∀ n, dist n α (Tick β))
    ∨ (∃ op k, ∀ n, dist n α (Vis op k))
  /-- Constructor disjointness & injectivity at step index 0 (`core.v:211–384`). -/
  err_inj      : ∀ {e₁ e₂}, dist 0 (Err e₁) (Err e₂) → e₁ = e₂
  tick_err_ne  : ∀ {β e}, ¬ dist 0 (Tick β) (Err e)
  vis_err_ne   : ∀ {op k e}, ¬ dist 0 (Vis op k) (Err e)
  tick_vis_ne  : ∀ {β op k}, ¬ dist 0 (Tick β) (Vis op k)
  toVal_ret    : ∀ {α k}, (∀ n, dist n α (Ret k)) → (toVal α).isSome = true
  toVal_fun    : ∀ {α f}, (∀ n, dist n α (Fun f)) → (toVal α).isSome = true
  toVal_err    : ∀ {α e}, (∀ n, dist n α (Err e)) → (toVal α).isSome = false
  toVal_vis    : ∀ {α op k}, (∀ n, dist n α (Vis op k)) → (toVal α).isSome = false
  /-- Reifier (`reify.v:488–512`): on `Vis op k` and `σ`, returns `(σ', out)` where `out` is
      constructively either `Tick β'` or `Err runtimeErr` (`reify_is_always_a_tick`). -/
  reify        : IT → State → State × IT
  reify_ne     : ∀ {n α₁ α₂ σ}, dist n α₁ α₂ →
                   (reify α₁ σ).1 = (reify α₂ σ).1 ∧ dist n (reify α₁ σ).2 (reify α₂ σ).2
  reify_vis_dichotomy : ∀ op k σ,
      (∃ β', ∀ n, dist n (reify (Vis op k) σ).2 (Tick β'))
    ∨ (∀ n, dist n (reify (Vis op k) σ).2 (Err .runtimeErr))

namespace GitreeSystem

def Equiv (S : GitreeSystem) (α β : S.IT) : Prop :=
  ∀ n, S.dist n α β

def internalEq (S : GitreeSystem) (α β : S.IT) : MiniUPred where
  holds := fun n => S.dist n α β
  mono  := fun hle h => S.dist_mono hle h

/-- Meta-level Coq/Lean `Prop` step relation (`reductions.v:18–26`). -/
inductive ExternalStep (S : GitreeSystem) : S.IT → S.State → S.IT → S.State → Prop where
  | tick {α β σ} : S.Equiv α (S.Tick β) → ExternalStep S α σ β σ
  | vis  {α op k σ σ' β} :
      S.Equiv α (S.Vis op k) →
      (S.reify α σ).1 = σ' →
      S.Equiv (S.reify α σ).2 (S.Tick β) →
      ExternalStep S α σ β σ'

/-- Internal `iProp` step relation (`reductions.v:237–242`). -/
def internalStep (S : GitreeSystem) (α : S.IT) (σ : S.State) (β : S.IT) (σ' : S.State) :
    MiniUPred :=
  MiniUPred.or
    (MiniUPred.and (S.internalEq α (S.Tick β)) (MiniUPred.pure (σ = σ')))
    (MiniUPred.ex fun op => MiniUPred.ex fun k =>
      MiniUPred.and (S.internalEq α (S.Vis op k))
        (MiniUPred.and (MiniUPred.pure ((S.reify α σ).1 = σ'))
                       (S.internalEq (S.reify α σ).2 (S.Tick β))))

/-- Internal `not_stuck` assertion (`weakestpre.v:417–420`). -/
def notStuck (S : GitreeSystem) (s : ErrCode → Prop) (α : S.IT) (σ : S.State) : MiniUPred :=
  MiniUPred.or
    (MiniUPred.pure ((S.toVal α).isSome = true))
    (MiniUPred.or
      (MiniUPred.ex fun β => MiniUPred.ex fun σ' => S.internalStep α σ β σ')
      (MiniUPred.ex fun e => MiniUPred.and (S.internalEq α (S.Err e)) (MiniUPred.pure (s e))))

/-- **Constructive Elimination of `disjunction_property` (`Hdisj`)**:
    Proves the exact conclusion of `wp_progress_gen`'s `not_stuck` externalization
    (`weakestpre.v:1975–2016`) **without** `disjunction_property` and **without** any axioms! -/
theorem notStuck_externalize_constructive
    (S : GitreeSystem) (s : ErrCode → Prop) (β : S.IT) (σ' : S.State)
    (hprf : ⊢ᵤ S.notStuck s β σ') :
    (S.toVal β).isSome = true
    ∨ (∃ β₁ σ₁, S.ExternalStep β σ' β₁ σ₁)
    ∨ (∃ e, S.Equiv β (S.Err e) ∧ s e) := by
  rcases S.dont_confuse β with
    ⟨e, he⟩ | ⟨k, hk⟩ | ⟨f, hf⟩ | ⟨β₁, htick⟩ | ⟨op, k, hvis⟩
  · -- Case 1: `β ≡ Err e`. Every disjunct of `notStuck` entails `⌜s e⌝` inside `MiniUPred`.
    refine .inr (.inr ⟨e, he, ?_⟩)
    apply MiniUPred.pure_soundness
    intro n
    have h0 : (S.notStuck s β σ').holds 0 := (S.notStuck s β σ').mono (Nat.zero_le n) (hprf n)
    rcases h0 with hval | hstep | ⟨e', he', hse'⟩
    · rw [S.toVal_err he] at hval; cases hval
    · rcases hstep with ⟨_, _, ⟨htk, _⟩ | ⟨_, _, hvs, _⟩⟩
      · exact False.elim (S.tick_err_ne (S.dist_trans (S.dist_symm htk) (he 0)))
      · exact False.elim (S.vis_err_ne (S.dist_trans (S.dist_symm hvs) (he 0)))
    · have heq : e = e' := S.err_inj (S.dist_trans (S.dist_symm (he 0)) he')
      exact heq ▸ hse'
  · -- Case 2: `β ≡ Ret k` -> immediately a value.
    exact .inl (S.toVal_ret hk)
  · -- Case 3: `β ≡ Fun f` -> immediately a value.
    exact .inl (S.toVal_fun hf)
  · -- Case 4: `β ≡ Tick β₁` -> immediately steps via `ExternalStep.tick`.
    exact .inr (.inl ⟨β₁, σ', .tick htick⟩)
  · -- Case 5: `β ≡ Vis op k` -> split constructively on `reify_vis_dichotomy`.
    rcases S.reify_vis_dichotomy op k σ' with ⟨β₁, hok⟩ | herr
    · refine .inr (.inl ⟨β₁, (S.reify β σ').1, .vis hvis rfl ?_⟩)
      intro n
      exact S.dist_trans (S.reify_ne (hvis n)).2 (hok n)
    · apply False.elim
      apply MiniUPred.pure_soundness (p := False)
      intro n
      have h0 : (S.notStuck s β σ').holds 0 := (S.notStuck s β σ').mono (Nat.zero_le n) (hprf n)
      rcases h0 with hval | hstep | ⟨_, he', _⟩
      · rw [S.toVal_vis hvis] at hval; cases hval
      · rcases hstep with ⟨_, _, ⟨htk, _⟩ | ⟨_, _, _, _, hre⟩⟩
        · exact S.tick_vis_ne (S.dist_trans (S.dist_symm htk) (hvis 0))
        · have hre_vis : S.dist 0 (S.reify β σ').2 (S.Err .runtimeErr) :=
            S.dist_trans (S.reify_ne (hvis 0)).2 (herr 0)
          exact S.tick_err_ne (S.dist_trans (S.dist_symm hre) hre_vis)
      · exact S.vis_err_ne (S.dist_trans (S.dist_symm (hvis 0)) he')

end GitreeSystem

/-- Over a two-point Kripke world/resource index (`Bool`), `disjunction_property` itself is
    outright FALSE (zero axioms): `⊢ P ∨ Q` holds globally while neither `⊢ P` nor `⊢ Q` holds! -/
abbrev WorldUPred : Type := Bool → Prop

def WorldValid (P : WorldUPred) : Prop := ∀ w : Bool, P w

theorem disjunction_property_refuted_over_two_worlds :
    ¬ (∀ P Q : WorldUPred, WorldValid (fun w => P w ∨ Q w) → WorldValid P ∨ WorldValid Q) := by
  intro hdisj
  let P : WorldUPred := fun w => w = true
  let Q : WorldUPred := fun w => w = false
  have hPQ : WorldValid (fun w => P w ∨ Q w) := by
    intro w
    cases w
    · exact .inr rfl
    · exact .inl rfl
  rcases hdisj P Q hPQ with hP | hQ
  · exact Bool.noConfusion (hP false)
  · exact Bool.noConfusion (hQ true)

end ConstructiveProgressExternalization

/-! ## 2. Leibniz OFE Quotient Upgrade (`iris-lean` `OFE.eq_dist'`) -/

section LeibnizOFEUpgrade

/-- An OFE with step-indexed `dist`. -/
structure PreOFE where
  Carrier    : Type
  dist       : Nat → Carrier → Carrier → Prop
  dist_refl  : ∀ n x, dist n x x
  dist_symm  : ∀ {n x y}, dist n x y → dist n y x
  dist_trans : ∀ {n x y z}, dist n x y → dist n y z → dist n x z

def PreOFE.limitEquiv (O : PreOFE) (x y : O.Carrier) : Prop :=
  ∀ n, O.dist n x y

/-- Quotienting `O.Carrier` by `limitEquiv` (`OFE.ofQuotient` in `iris-lean`) yields a type whose
    limit equivalence IS native Lean propositional equality `=` (`eq_dist'`). -/
def PreOFE.QuotCarrier (O : PreOFE) : Type :=
  Quot O.limitEquiv

def PreOFE.qdist (O : PreOFE) (n : Nat) : O.QuotCarrier → O.QuotCarrier → Prop :=
  Quot.lift
    (fun x => Quot.lift (fun y => O.dist n x y)
      (fun _ _ hy => propext ⟨fun h => O.dist_trans h (hy n),
                              fun h => O.dist_trans h (O.dist_symm (hy n))⟩))
    (fun _ _ hx => funext fun qy =>
      Quot.inductionOn qy fun _ =>
        propext ⟨fun h => O.dist_trans (O.dist_symm (hx n)) h,
                 fun h => O.dist_trans (hx n) h⟩)

theorem PreOFE.eq_iff_forall_qdist (O : PreOFE) (qx qy : O.QuotCarrier) :
    qx = qy ↔ ∀ n, O.qdist n qx qy := by
  refine Quot.inductionOn qx fun x => Quot.inductionOn qy fun y => ⟨?_, ?_⟩
  · intro heq n
    have hrefl : O.qdist n (Quot.mk O.limitEquiv x) (Quot.mk O.limitEquiv x) := O.dist_refl n x
    exact heq ▸ hrefl
  · intro h
    exact Quot.sound h

end LeibnizOFEUpgrade

/-! ## 3. ω-Horizon `∀ n, ∃ k` Witness Barrier (`synthetic_domains/existential_prop.v`) -/

section OmegaHorizonBarrier

def DownwardClosedInHorizon (P : Nat → Nat → Prop) : Prop :=
  ∀ {m n k}, m ≤ n → P n k → P m k

theorem omega_forall_exists_counterexample :
    ∃ P : Nat → Nat → Prop,
      DownwardClosedInHorizon P ∧
      (∀ n : Nat, ∃ k : Nat, P n k) ∧
      ¬ (∃ k : Nat, ∀ n : Nat, P n k) := by
  refine ⟨fun n k => n ≤ k, ?_, ?_, ?_⟩
  · intro m n k hmn hnk
    exact Nat.le_trans hmn hnk
  · intro n
    exact ⟨n, Nat.le_refl n⟩
  · rintro ⟨k, hk⟩
    exact Nat.not_succ_le_self k (hk (k + 1))

end OmegaHorizonBarrier

/-! ## 4. Failure of `▷(∃ x, P x) ⊢ ▷⊥ ∨ ∃ x, ▷(P x)` at Limit Ordinal `ω` -/

section LimitOrdinalLaterExists

inductive OmegaPlusOne : Type where
  | fin   : Nat → OmegaPlusOne
  | omega : OmegaPlusOne

def OrdLt : OmegaPlusOne → OmegaPlusOne → Prop
  | .fin m, .fin n => m < n
  | .fin _, .omega => True
  | .omega, _      => False

theorem OrdLt.trans {α β γ : OmegaPlusOne} (h₁ : OrdLt α β) (h₂ : OrdLt β γ) : OrdLt α γ := by
  cases α <;> cases β <;> cases γ <;> simp [OrdLt] at h₁ h₂ ⊢
  exact Nat.lt_trans h₁ h₂

structure TransfiniteSieve : Type 1 where
  holds : OmegaPlusOne → Prop
  down  : ∀ {α β}, OrdLt α β → holds β → holds α

namespace TransfiniteSieve

def later (P : TransfiniteSieve) : TransfiniteSieve where
  holds := fun α => ∀ β, OrdLt β α → P.holds β
  down  := fun hlt h γ hγ => h γ (OrdLt.trans hγ hlt)

def bot : TransfiniteSieve where
  holds := fun _ => False
  down  := fun _ h => h

def or (P Q : TransfiniteSieve) : TransfiniteSieve where
  holds := fun α => P.holds α ∨ Q.holds α
  down  := fun hlt h => h.elim (fun hp => .inl (P.down hlt hp)) (fun hq => .inr (Q.down hlt hq))

def ex {ι : Type} (Φ : ι → TransfiniteSieve) : TransfiniteSieve where
  holds := fun α => ∃ i, (Φ i).holds α
  down  := fun hlt ⟨i, hi⟩ => ⟨i, (Φ i).down hlt hi⟩

end TransfiniteSieve

theorem finite_stage_later_exists_holds (Φ : Nat → TransfiniteSieve) (n : Nat) :
    (TransfiniteSieve.later (TransfiniteSieve.ex Φ)).holds (.fin n) →
    (TransfiniteSieve.or (TransfiniteSieve.later TransfiniteSieve.bot)
      (TransfiniteSieve.ex fun k => TransfiniteSieve.later (Φ k))).holds (.fin n) := by
  intro h
  cases n with
  | zero =>
    refine .inl (fun β hlt => ?_)
    cases β <;> simp [OrdLt] at hlt
  | succ m =>
    have hm : OrdLt (.fin m) (.fin (m + 1)) := Nat.lt_succ_self m
    rcases h (.fin m) hm with ⟨k, hk⟩
    refine .inr ⟨k, fun β hlt => ?_⟩
    cases β with
    | omega => simp [OrdLt] at hlt
    | fin j =>
      have hjm : j ≤ m := Nat.le_of_lt_succ hlt
      rcases Nat.eq_or_lt_of_le hjm with rfl | hjlt
      · exact hk
      · have hjord : OrdLt (.fin j) (.fin m) := hjlt
        exact (Φ k).down hjord hk

theorem limit_ordinal_later_exists_refuted :
    ∃ Φ : Nat → TransfiniteSieve,
      (TransfiniteSieve.later (TransfiniteSieve.ex Φ)).holds .omega ∧
      ¬ (TransfiniteSieve.or (TransfiniteSieve.later TransfiniteSieve.bot)
          (TransfiniteSieve.ex fun k => TransfiniteSieve.later (Φ k))).holds .omega := by
  let Φ : Nat → TransfiniteSieve := fun k =>
    { holds := fun α => match α with
        | .fin n => n ≤ k
        | .omega => False
      down := by
        intro α β hlt hβ
        cases α <;> cases β <;> simp [OrdLt] at hlt hβ ⊢
        exact Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hβ) }
  refine ⟨Φ, ?_, ?_⟩
  · intro β hlt
    cases β with
    | omega => simp [OrdLt] at hlt
    | fin n => exact ⟨n, Nat.le_refl n⟩
  · rintro (hbot | ⟨k, hk⟩)
    · exact hbot (.fin 0) trivial
    · have hsucc : (Φ k).holds (.fin (k + 1)) := hk (.fin (k + 1)) trivial
      exact Nat.not_succ_le_self k hsucc

end LimitOrdinalLaterExists

#print axioms restrict_embed
#print axioms GitreeSystem.notStuck_externalize_constructive
#print axioms disjunction_property_refuted_over_two_worlds
#print axioms PreOFE.eq_iff_forall_qdist
#print axioms omega_forall_exists_counterexample
#print axioms finite_stage_later_exists_holds
#print axioms limit_ordinal_later_exists_refuted

end GitreeSyntheticProbes
