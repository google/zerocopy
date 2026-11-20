import ToyDirCC.Cert
import ToyDirCC.Outcome

/-!
# The profile restrictions are necessary

* `monoCong_refuted_at_nonMono`: for every signature, profile `P`, operator `f` and
  position `i` that `P` does **not** declare `mono`, the explicit model
  `flipModel f i` satisfies all four laws for `P`, makes the fact `x₀ ≤ x₁` true, and makes
  the conclusion of the one-sided congruence step at `(f, i)` false.
* `eqCong_refuted_at_opaque`: for every position declared `opaqueArg`, the explicit model
  `splitModel f i` satisfies all four laws, makes `x₀ ≤ x₁` and `x₁ ≤ x₀` true, and makes
  the conclusion of the two-sided congruence step false.
* `policySound_iff_admissibleFor`: a checker policy is sound for all models satisfying the
  four laws for `P` exactly when it is admissible for `P`.
* `pickMin_monoCong_counterexample`, `pickFirst_eqCong_counterexample`: the same failures
  in the set-of-outcomes model, with a least-outcome commitment (`pickMin`, declared
  `eqOnly`) and a first-listed-outcome commitment (`pickFirst`, declared `opaqueArg`).
-/

namespace Toy.DirCC

variable {Op : Type}

/-! ## A generic countermodel for one-sided congruence -/

/-- `Bool` with `false ≤ true`; `f` negates its `i`-th argument (missing: `false`); every
other operator is constantly `false`. -/
abbrev flipModel [DecidableEq Op] (f : Op) (i : Nat) : Model Op where
  C := Bool
  le a b := a = true → b = true
  interp g args := if g = f then !(args.getD i false) else false

/-- The valuation `x₀ ↦ false`, every other variable `↦ true`. -/
def flipVal : Nat → Bool := fun n => n != 0

theorem flipModel_refl [DecidableEq Op] (f : Op) (i : Nat) : LeRefl (flipModel f i) :=
  fun _ h => h

theorem flipModel_trans [DecidableEq Op] (f : Op) (i : Nat) : LeTrans (flipModel f i) :=
  fun _ _ _ h1 h2 h => h2 (h1 h)

theorem flipModel_monoAt [DecidableEq Op] (P : Profile Op) (f : Op) (i : Nat)
    (h : P f i ≠ .mono) : MonoAt P (flipModel f i) := by
  intro g pre post x y hP _
  show ((if g = f then _ else _) = true → (if g = f then _ else _) = true)
  by_cases hg : g = f
  · subst hg
    have hi : i ≠ pre.length := by intro e; rw [← e] at hP; exact h hP
    rw [getD_hole_ne pre post x y false hi]
    exact id
  · simp [hg]

theorem flipModel_kerAt [DecidableEq Op] (P : Profile Op) (f : Op) (i : Nat) :
    KerAt P (flipModel f i) := by
  intro g pre post x y _ hxy hyx
  have : x = y := by
    cases x <;> cases y
    · rfl
    · exact absurd (hyx rfl) (by simp)
    · exact absurd (hxy rfl) (by simp)
    · rfl
  subst this
  exact id

/-- **One-sided congruence at a non-`mono` position is refutable.** For every profile `P`
and every context `f(pre, □, post)` whose hole position `pre.length` is not declared
`mono`, the model `flipModel f pre.length` satisfies `LeRefl`, `LeTrans`, `MonoAt P` and
`KerAt P`, the fact `x₀ ≤ x₁` holds under `flipVal`, and
`f(pre, x₀, post) ≤ f(pre, x₁, post)` fails. -/
theorem monoCong_refuted_at_nonMono [DecidableEq Op] (P : Profile Op) (f : Op)
    (pre post : List (Term Op)) (h : P f pre.length ≠ .mono) :
    LeRefl (flipModel f pre.length) ∧ LeTrans (flipModel f pre.length) ∧
    MonoAt P (flipModel f pre.length) ∧ KerAt P (flipModel f pre.length) ∧
    (flipModel f pre.length).le (flipVal 0) (flipVal 1) ∧
    ¬ (flipModel f pre.length).le
        (eval (flipModel f pre.length) flipVal (.app f (pre ++ .var 0 :: post)))
        (eval (flipModel f pre.length) flipVal (.app f (pre ++ .var 1 :: post))) := by
  refine ⟨flipModel_refl _ _, flipModel_trans _ _, flipModel_monoAt P f _ h,
    flipModel_kerAt P f _, fun _ => rfl, ?_⟩
  rw [eval_app, eval_app, List.map_append, List.map_append, List.map_cons, List.map_cons]
  have e0 := getD_hole_self (pre.map (eval (flipModel f pre.length) flipVal))
    (post.map (eval (flipModel f pre.length) flipVal)) (eval (flipModel f pre.length) flipVal (.var 0)) false
  have e1 := getD_hole_self (pre.map (eval (flipModel f pre.length) flipVal))
    (post.map (eval (flipModel f pre.length) flipVal)) (eval (flipModel f pre.length) flipVal (.var 1)) false
  rw [List.length_map] at e0 e1
  show ¬ ((if f = f then _ else _) = true → (if f = f then _ else _) = true)
  rw [e0, e1]
  simp [eval, flipVal]

/-! ## A generic countermodel for two-sided congruence -/

/-- Three points: `a` and `a'` refine each other, `b` is related only to itself. -/
inductive Tri where
  | a
  | a'
  | b
deriving Repr, DecidableEq

/-- The relation on `Tri`. -/
def triLe : Tri → Tri → Prop
  | .b, .b => True
  | .b, _ => False
  | _, .b => False
  | _, _ => True

instance : DecidableRel triLe := fun x y => by
  cases x <;> cases y <;> simp [triLe] <;> infer_instance

/-- `f` maps its `i`-th argument `a'` to `b` and everything else to `a`; every other
operator is constantly `a`. -/
abbrev splitModel [DecidableEq Op] (f : Op) (i : Nat) : Model Op where
  C := Tri
  le := triLe
  interp g args := if g = f then (if args.getD i .a = .a' then .b else .a) else .a

/-- The valuation `x₀ ↦ a`, every other variable `↦ a'`. -/
def splitVal : Nat → Tri := fun n => if n = 0 then .a else .a'

theorem splitModel_refl [DecidableEq Op] (f : Op) (i : Nat) : LeRefl (splitModel f i) := by
  intro x; cases x <;> trivial

theorem splitModel_trans [DecidableEq Op] (f : Op) (i : Nat) : LeTrans (splitModel f i) := by
  intro x y z h1 h2
  cases x <;> cases y <;> cases z <;> simp_all [triLe]

theorem splitModel_monoAt [DecidableEq Op] (P : Profile Op) (f : Op) (i : Nat)
    (h : P f i ≠ .mono) : MonoAt P (splitModel f i) := by
  intro g pre post x y hP _
  show triLe (if g = f then _ else _) (if g = f then _ else _)
  by_cases hg : g = f
  · subst hg
    have hi : i ≠ pre.length := by intro e; rw [← e] at hP; exact h hP
    rw [getD_hole_ne pre post x y Tri.a hi]
    exact splitModel_refl g i _
  · simp [hg, triLe]

theorem splitModel_kerAt [DecidableEq Op] (P : Profile Op) (f : Op) (i : Nat)
    (h : P f i ≠ .eqOnly) : KerAt P (splitModel f i) := by
  intro g pre post x y hP _ _
  show triLe (if g = f then _ else _) (if g = f then _ else _)
  by_cases hg : g = f
  · subst hg
    have hi : i ≠ pre.length := by intro e; rw [← e] at hP; exact h hP
    rw [getD_hole_ne pre post x y Tri.a hi]
    exact splitModel_refl g i _
  · simp [hg, triLe]

/-- **Two-sided congruence at an `opaqueArg` position is refutable.** For every profile `P`
and every context `f(pre, □, post)` whose hole position is declared `opaqueArg`, the model
`splitModel f pre.length` satisfies all four laws for `P`, both `x₀ ≤ x₁` and `x₁ ≤ x₀`
hold under `splitVal`, and `f(pre, x₀, post) ≤ f(pre, x₁, post)` fails. -/
theorem eqCong_refuted_at_opaque [DecidableEq Op] (P : Profile Op) (f : Op)
    (pre post : List (Term Op)) (h : P f pre.length = .opaqueArg) :
    LeRefl (splitModel f pre.length) ∧ LeTrans (splitModel f pre.length) ∧
    MonoAt P (splitModel f pre.length) ∧ KerAt P (splitModel f pre.length) ∧
    (splitModel f pre.length).le (splitVal 0) (splitVal 1) ∧
    (splitModel f pre.length).le (splitVal 1) (splitVal 0) ∧
    ¬ (splitModel f pre.length).le
        (eval (splitModel f pre.length) splitVal (.app f (pre ++ .var 0 :: post)))
        (eval (splitModel f pre.length) splitVal (.app f (pre ++ .var 1 :: post))) := by
  refine ⟨splitModel_refl _ _, splitModel_trans _ _,
    splitModel_monoAt P f _ (by rw [h]; decide), splitModel_kerAt P f _ (by rw [h]; decide),
    trivial, trivial, ?_⟩
  rw [eval_app, eval_app, List.map_append, List.map_append, List.map_cons, List.map_cons]
  have e0 := getD_hole_self (pre.map (eval (splitModel f pre.length) splitVal))
    (post.map (eval (splitModel f pre.length) splitVal)) (eval (splitModel f pre.length) splitVal (.var 0)) Tri.a
  have e1 := getD_hole_self (pre.map (eval (splitModel f pre.length) splitVal))
    (post.map (eval (splitModel f pre.length) splitVal)) (eval (splitModel f pre.length) splitVal (.var 1)) Tri.a
  rw [List.length_map] at e0 e1
  show ¬ triLe (if f = f then _ else _) (if f = f then _ else _)
  rw [e0, e1]
  simp [eval, splitVal, triLe]

/-! ## Positive controls: the permitted steps are sound -/

/-- Positive control for `monoCong_refuted_at_nonMono`: at a position declared `mono`, the
one-sided congruence step is sound in every model satisfying `MonoAt P` (in particular in
every model satisfying the four laws). -/
theorem monoCong_sound_at_mono (P : Profile Op) (f : Op)
    (pre post : List (Term Op)) (h : P f pre.length = .mono) (M : Model Op) (ρ : Nat → M.C)
    (hMono : MonoAt P M) (h01 : M.le (ρ 0) (ρ 1)) :
    M.le (eval M ρ (.app f (pre ++ .var 0 :: post))) (eval M ρ (.app f (pre ++ .var 1 :: post))) := by
  rw [eval_app_hole, eval_app_hole]
  exact hMono f _ _ _ _ (by rw [List.length_map]; exact h) h01

/-- Positive control for `eqCong_refuted_at_opaque`: at a position not declared `opaqueArg`
(that is, `mono` or `eqOnly`), the two-sided congruence step is sound in every model
satisfying `MonoAt P` and `KerAt P` (in particular in every model satisfying the four
laws). -/
theorem eqCong_sound_at_nonOpaque (P : Profile Op) (f : Op)
    (pre post : List (Term Op)) (h : P f pre.length ≠ .opaqueArg) (M : Model Op)
    (ρ : Nat → M.C) (hMono : MonoAt P M) (hKer : KerAt P M)
    (h01 : M.le (ρ 0) (ρ 1)) (h10 : M.le (ρ 1) (ρ 0)) :
    M.le (eval M ρ (.app f (pre ++ .var 0 :: post))) (eval M ρ (.app f (pre ++ .var 1 :: post))) := by
  rw [eval_app_hole, eval_app_hole]
  cases hm : P f pre.length with
  | mono => exact hMono f _ _ _ _ (by rw [List.length_map]; exact hm) h01
  | eqOnly => exact hKer f _ _ _ _ (by rw [List.length_map]; exact hm) h01 h10
  | opaqueArg => exact absurd hm h

/-! ## Antisymmetric models: where `opaqueArg` and `eqOnly` coincide -/

/-- The relation of a model is antisymmetric (a partial order when also reflexive and
transitive): mutual refinement is equality. -/
def LeAntisymm (M : Model Op) : Prop := ∀ x y : M.C, M.le x y → M.le y x → x = y

/-- Equal argument values give equal results at every position, including `opaqueArg`
positions: models interpret operators as functions of argument values. -/
theorem eval_hole_congr_of_eval_eq (M : Model Op) (ρ : Nat → M.C) (f : Op)
    (pre post : List (Term Op)) (s t : Term Op) (h : eval M ρ s = eval M ρ t) :
    eval M ρ (.app f (pre ++ s :: post)) = eval M ρ (.app f (pre ++ t :: post)) := by
  rw [eval_app_hole, eval_app_hole, h]

/-- In a reflexive antisymmetric model, `KerAt` holds for every profile. -/
theorem kerAt_of_antisymm (P : Profile Op) (M : Model Op) (hR : LeRefl M)
    (hA : LeAntisymm M) : KerAt P M := by
  intro f pre post x y _ hxy hyx
  rw [hA x y hxy hyx]
  exact hR _

/-- In a reflexive antisymmetric model, the two-sided congruence step is sound at every
position, `opaqueArg` included. -/
theorem eqCong_sound_of_antisymm (f : Op) (pre post : List (Term Op)) (M : Model Op)
    (ρ : Nat → M.C) (hR : LeRefl M) (hA : LeAntisymm M)
    (h01 : M.le (ρ 0) (ρ 1)) (h10 : M.le (ρ 1) (ρ 0)) :
    M.le (eval M ρ (.app f (pre ++ .var 0 :: post))) (eval M ρ (.app f (pre ++ .var 1 :: post))) := by
  rw [eval_hole_congr_of_eval_eq M ρ f pre post (.var 0) (.var 1) (hA _ _ h01 h10)]
  exact hR _

/-- The one-sided countermodel `flipModel` is antisymmetric, so one-sided congruence at a
non-`mono` position stays refutable within partial-order models. -/
theorem flipModel_antisymm [DecidableEq Op] (f : Op) (i : Nat) : LeAntisymm (flipModel f i) := by
  intro x y hxy hyx
  cases x <;> cases y
  · rfl
  · exact absurd (hyx rfl) (by simp)
  · exact absurd (hxy rfl) (by simp)
  · rfl

/-- The two-sided countermodel `splitModel` is not antisymmetric (`a` and `a'` refine each
other). -/
theorem splitModel_not_antisymm [DecidableEq Op] (f : Op) (i : Nat) :
    ¬ LeAntisymm (splitModel f i) := fun h => Tri.noConfusion (h .a .a' trivial trivial)

/-- In the one-sided countermodel the *reversed* conclusion holds: `f` is anti-monotone at
the hole (it negates the hole argument). -/
theorem flipModel_reversed_conclusion [DecidableEq Op] (f : Op) (pre post : List (Term Op)) :
    (flipModel f pre.length).le
      (eval (flipModel f pre.length) flipVal (.app f (pre ++ .var 1 :: post)))
      (eval (flipModel f pre.length) flipVal (.app f (pre ++ .var 0 :: post))) := by
  rw [eval_app, eval_app, List.map_append, List.map_append, List.map_cons, List.map_cons]
  have e0 := getD_hole_self (pre.map (eval (flipModel f pre.length) flipVal))
    (post.map (eval (flipModel f pre.length) flipVal)) (eval (flipModel f pre.length) flipVal (.var 0)) false
  have e1 := getD_hole_self (pre.map (eval (flipModel f pre.length) flipVal))
    (post.map (eval (flipModel f pre.length) flipVal)) (eval (flipModel f pre.length) flipVal (.var 1)) false
  rw [List.length_map] at e0 e1
  show ((if f = f then _ else _) = true → (if f = f then _ else _) = true)
  rw [e0, e1]
  simp [eval, flipVal]

/-- `monoCong_refuted_at_nonMono` needs its hypothesis: when the hole position is declared
`mono` (here: every position, `succ`, empty context), the named countermodel
`flipModel succ 0` violates `MonoAt`, so the conclusion fails. -/
theorem monoCong_refuted_needs_nonMono :
    allMono UOp .succ ([] : List (Term UOp)).length = .mono ∧
    ¬ MonoAt (allMono UOp) (flipModel UOp.succ ([] : List (Term UOp)).length) := by
  refine ⟨rfl, fun h => ?_⟩
  have := h .succ [] [] false true rfl (fun e => absurd e (by decide))
  exact absurd (this rfl) (by decide)

/-- The profile declaring every position `eqOnly`. -/
def allEqOnly (Op : Type) : Profile Op := fun _ _ => .eqOnly

/-- `eqCong_refuted_at_opaque` needs its hypothesis: when the hole position is declared
`eqOnly` (resp. `mono`), the named countermodel `splitModel succ 0` violates `KerAt`
(resp. `MonoAt`), so the conclusion fails. -/
theorem eqCong_refuted_needs_opaque :
    allEqOnly UOp .succ ([] : List (Term UOp)).length = .eqOnly ∧
    ¬ KerAt (allEqOnly UOp) (splitModel UOp.succ ([] : List (Term UOp)).length) ∧
    allMono UOp .succ ([] : List (Term UOp)).length = .mono ∧
    ¬ MonoAt (allMono UOp) (splitModel UOp.succ ([] : List (Term UOp)).length) := by
  refine ⟨rfl, fun h => ?_, rfl, fun h => ?_⟩
  · have := h .succ [] [] .a .a' rfl trivial trivial
    exact absurd this (by decide)
  · have := h .succ [] [] .a .a' rfl trivial
    exact absurd this (by decide)

/-! ## Characterization of sound policies -/

/-- A policy is sound for profile `P` if, for every model satisfying `LeRefl`, `LeTrans`,
`MonoAt P` and `KerAt P`, every valuation and every list of facts true under it, every
certificate the policy's checker accepts proves a true refinement. -/
def PolicySound (Op : Type) [DecidableEq Op] (P : Profile Op) (pol : Policy) : Prop :=
  ∀ (M : Model Op), LeRefl M → LeTrans M → MonoAt P M → KerAt P M →
    ∀ (ρ : Nat → M.C) (facts : List (Term Op × Term Op)), FactsHold M ρ facts →
      ∀ (c : Cert Op) (s t : Term Op), check pol P facts c s t = true →
        M.le (eval M ρ s) (eval M ρ t)

/-- **Characterization.** A checker policy is sound for profile `P` iff it permits
one-sided congruence only at positions `P` declares `mono` and two-sided congruence only at
positions `P` does not declare `opaqueArg`. -/
theorem policySound_iff_admissibleFor [DecidableEq Op] (P : Profile Op) (pol : Policy) :
    PolicySound Op P pol ↔ pol.AdmissibleFor P := by
  constructor
  · intro hS
    refine ⟨fun f i hc => ?_, fun f i hc hop => ?_⟩
    · by_cases hm : P f i = .mono
      · exact hm
      · exfalso
        let pre : List (Term Op) := List.replicate i (.var 0)
        have hlen : pre.length = i := List.length_replicate
        have hm' : P f pre.length ≠ .mono := by rw [hlen]; exact hm
        obtain ⟨hR, hT, hMo, hK, h01, hbad⟩ := monoCong_refuted_at_nonMono P f pre [] hm'
        apply hbad
        refine hS _ hR hT hMo hK flipVal [(.var 0, .var 1)] ?_ (.cong f pre [] (.fact 0)) _ _ ?_
        · intro s t hst
          simp only [List.mem_singleton, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          exact h01
        · have hc' : pol.cong (P f pre.length) = true := by rw [hlen]; exact hc
          simp [check, concl, hc']
    · let pre : List (Term Op) := List.replicate i (.var 0)
      have hlen : pre.length = i := List.length_replicate
      have hop' : P f pre.length = .opaqueArg := by rw [hlen]; exact hop
      obtain ⟨hR, hT, hMo, hK, h01, h10, hbad⟩ := eqCong_refuted_at_opaque P f pre [] hop'
      apply hbad
      refine hS _ hR hT hMo hK splitVal [(.var 0, .var 1), (.var 1, .var 0)] ?_
        (.congEq f pre [] (.fact 0) (.fact 1)) _ _ ?_
      · intro s t hst
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hst
        rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h01
        · exact h10
      · have hc' : pol.congEq (P f pre.length) = true := by rw [hlen]; exact hc
        simp [check, concl, hc']
  · intro hA M hR hT hMo hK ρ facts hF c s t hc
    exact check_sound_of_admissible hA hR hT hMo hK hF hc

/-! ## Concrete failures in the set-of-outcomes model -/

/-- The policy permitting both congruence rules at every position. -/
def Policy.permissive : Policy where
  cong _ := true
  congEq _ := true

/-- Valuation for the outcome counterexamples: `x₀ ↦ [0, 1]`, `x₁ ↦ [1]`,
`x₂ ↦ [1, 0]`, others `↦ []`. -/
def oVal : Nat → List Nat := fun n => [[0, 1], [1], [1, 0]].getD n []

/-- Positive example (`FactsHold`): `x₀ ≤ x₁`, `x₀ ≤ x₂` and `x₂ ≤ x₀` hold under `oVal`. -/
theorem factsHold_example :
    FactsHold oModel oVal [(.var 0, .var 1), (.var 0, .var 2), (.var 2, .var 0)] := by
  intro s t h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Negative example (`FactsHold`): `x₁ ≤ x₀` fails under `oVal` (`[0, 1]` does not refine
`[1]`). -/
theorem not_factsHold_example : ¬ FactsHold oModel oVal [(.var 1, .var 0)] := by
  intro h
  have := h (.var 1) (.var 0) (by simp)
  exact absurd this (by decide)

/-- **Least-outcome commitment is not monotone.** In the outcome model (which satisfies all
four laws for `oProfile`, where `pickMin`'s argument is `eqOnly`), the fact
`x₀ ≤ x₁` (`[1]` refines `[0, 1]`) holds, the permissive checker accepts the one-sided
congruence certificate for `pickMin x₀ ≤ pickMin x₁`, the standard checker rejects it, and
the conclusion is false (`[1]` does not refine `[0]`). -/
theorem pickMin_monoCong_counterexample :
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal [(.var 0, .var 1)] ∧
    check Policy.permissive oProfile [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0))
      (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = true ∧
    check Policy.standard oProfile [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0))
      (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = false ∧
    ¬ oModel.le (eval oModel oVal (.app .pickMin [.var 0]))
      (eval oModel oVal (.app .pickMin [.var 1])) := by
  refine ⟨oModel_refl, oModel_trans, oModel_monoAt, oModel_kerAt, ?_, by decide, by decide,
    by decide⟩
  intro s t hst
  simp only [List.mem_singleton, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  decide

/-- **First-listed-outcome commitment does not respect mutual refinement.** In the
outcome model (all four laws for `oProfile`, where `pickFirst`'s argument is `opaqueArg`),
`x₀ = [0, 1]` and `x₂ = [1, 0]` refine each other, the permissive checker accepts the
two-sided congruence certificate for `pickFirst x₀ ≤ pickFirst x₂`, the standard checker
rejects it, and the conclusion is false (`[1]` does not refine `[0]`). -/
theorem pickFirst_eqCong_counterexample :
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal [(.var 0, .var 2), (.var 2, .var 0)] ∧
    check Policy.permissive oProfile [(.var 0, .var 2), (.var 2, .var 0)]
      (.congEq .pickFirst [] [] (.fact 0) (.fact 1))
      (.app .pickFirst [.var 0]) (.app .pickFirst [.var 2]) = true ∧
    check Policy.standard oProfile [(.var 0, .var 2), (.var 2, .var 0)]
      (.congEq .pickFirst [] [] (.fact 0) (.fact 1))
      (.app .pickFirst [.var 0]) (.app .pickFirst [.var 2]) = false ∧
    ¬ oModel.le (eval oModel oVal (.app .pickFirst [.var 0]))
      (eval oModel oVal (.app .pickFirst [.var 2])) := by
  refine ⟨oModel_refl, oModel_trans, oModel_monoAt, oModel_kerAt, ?_, by decide, by decide,
    by decide⟩
  intro s t hst
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hst
  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end Toy.DirCC
