import Toy.StoreLaws.Results

/-!
# Store laws: tightness counterexamples, non-vacuity witnesses, positive controls

Every tightness counterexample is stated in canonical form: a concrete
instance satisfying all the other hypotheses of the result, in which the
conclusion fails.  Every non-vacuity theorem exhibits a concrete instance
satisfying all hypotheses of the result.
-/

namespace Toy.StoreLaws

open Prog

/-! ## `getGet_of_getPut_of_putGet` -/

/-- Tightness of `hGP`: `faultingCounter` satisfies put–get, and get–get fails. -/
theorem getGet_of_tight_getPut :
    PutGet (faultingCounter Bool Bool) ∧ ¬ GetGet (faultingCounter Bool Bool) :=
  ⟨faultingCounter_putGet, faultingCounter_not_getGet⟩

/-- Tightness of `hPG`: `readToClear` satisfies get–put, and get–get fails. -/
theorem getGet_of_tight_putGet :
    GetPut (readToClear Bool Bool false) ∧ ¬ GetGet (readToClear Bool Bool false) :=
  ⟨readToClear_getPut false, readToClear_not_getGet⟩

/-- Non-vacuity: `inertHidden` (not the intended model) satisfies get–put and
put–get. -/
theorem nv_getGet_of_getPut_of_putGet :
    GetPut (inertHidden Bool Bool Bool) ∧ PutGet (inertHidden Bool Bool Bool) :=
  ⟨inertHidden_lawful.2.1, inertHidden_lawful.2.2.1⟩

/-! ## `entailsBool_iff` -/

/-- Non-vacuity of both sides of `entailsBool_iff`: `{get–put, put–get}`
entails get–get, and the other three laws do not entail put–put. -/
theorem nv_entailsBool_iff :
    EntailsBool (fun l => l = .getPut ∨ l = .putGet) .getGet ∧
    ¬ EntailsBool (lawsExcept .putPut) .putPut := by
  constructor
  · exact (entailsBool_iff _ _).2 (Or.inr ⟨rfl, Or.inl rfl, Or.inr rfl⟩)
  · intro h
    rcases (entailsBool_iff _ _).1 h with h' | ⟨h', _⟩
    · exact h' rfl
    · cases h'

/-! ## Normal forms -/

/-- Non-vacuity of `derivable_nf_of_getPut_putGet_putPut` and
`derivable_iff_obsEq_of_getPut_putGet_putPut`: the law set without get–get
contains get–put, put–get and put–put. -/
theorem nv_derivable_nf :
    lawsExcept .getGet .getPut ∧ lawsExcept .getGet .putGet ∧ lawsExcept .getGet .putPut := by
  decide

/-- Non-vacuity of both sides of `derivable_lawsExcept_getGet_iff`: a get–get
instance is derivable from the laws other than get–get (hence from all four),
and `ret true = ret false` is derivable from neither (Boolean cell). -/
theorem nv_derivable_lawsExcept_getGet_iff :
    Derivable (lawsExcept .getGet)
      (get fun s => get fun s' => ret (s, s') : Prog Bool (Bool × Bool)) (get fun s => ret (s, s)) ∧
    ¬ Derivable (lawsExcept .getGet) (ret true : Prog Bool Bool) (ret false) := by
  refine ⟨Derivable.getGet_of (by decide) (by decide) _, fun h => ?_⟩
  exact absurd (congrFun h.run_eq false) (by decide)

/-- Non-vacuity of `canon_eq_of_derivable`: the premise is satisfiable (here by
reflexivity, for a canonical program that negates the cell and returns the
value read). -/
theorem nv_canon_eq_of_derivable :
    Derivable allLaws (canon (fun s : Bool => !s) (fun s => s))
      (canon (fun s : Bool => !s) (fun s => s)) :=
  .refl _

/-- Tightness of the premise of `canon_eq_of_derivable`: without it the
conclusion fails for two canonical programs with different write maps. -/
theorem canon_eq_tight :
    ¬ ((fun s : Bool => s) = (fun s => !s) ∧ (fun s : Bool => s) = (fun s => s)) := by
  intro h
  have := congrFun h.1 true
  exact absurd this (by decide)

/-! ## Representation up to observation -/

/-- Tightness of `hGP` in the representation results: `dirtyBit` satisfies
put–get and put–put; `ret true` and its canonical program are observationally
equivalent but interpreted differently, and the factorization through `run`
fails. -/
theorem interp_factor_tight_getPut :
    PutGet (dirtyBit Bool Bool) ∧ PutPut (dirtyBit Bool Bool) ∧
    ObsEq (ret true : Prog Bool Bool) (nf (run (ret true))) ∧
    (dirtyBit Bool Bool).interp pairRet (ret true : Prog Bool Bool) ≠
      (dirtyBit Bool Bool).interp pairRet (nf (run (ret true : Prog Bool Bool))) ∧
    (dirtyBit Bool Bool).interp pairRet (ret true : Prog Bool Bool) ≠
      (dirtyBit Bool Bool).fromObs pairRet (run (ret true : Prog Bool Bool)) := by
  refine ⟨dirtyBit_putGet, dirtyBit_putPut, rfl, fun h => ?_, fun h => ?_⟩
  · exact absurd (congrFun h (false, false)) (by decide)
  · exact absurd (congrFun h (false, false)) (by decide)

/-- Tightness of `hPG` in the representation results: `writesIgnored`
satisfies get–put and put–put; `put true (get ret)` and its canonical program
are observationally equivalent but interpreted differently. -/
theorem interp_factor_tight_putGet :
    GetPut (writesIgnored Bool Bool) ∧ PutPut (writesIgnored Bool Bool) ∧
    ObsEq (put true (get ret) : Prog Bool Bool) (nf (run (put true (get ret)))) ∧
    (writesIgnored Bool Bool).interp intendedRet (put true (get ret) : Prog Bool Bool) ≠
      (writesIgnored Bool Bool).interp intendedRet
        (nf (run (put true (get ret) : Prog Bool Bool))) ∧
    (writesIgnored Bool Bool).interp intendedRet (put true (get ret) : Prog Bool Bool) ≠
      (writesIgnored Bool Bool).fromObs intendedRet
        (run (put true (get ret) : Prog Bool Bool)) := by
  refine ⟨writesIgnored_getPut, writesIgnored_putPut, rfl, fun h => ?_, fun h => ?_⟩
  · exact absurd (congrFun h false) (by decide)
  · exact absurd (congrFun h false) (by decide)

/-- Tightness of `hPP` in the representation results: `changeLog` satisfies
get–put and put–get; `put true (put false (ret true))` and its canonical
program are observationally equivalent but interpreted differently. -/
theorem interp_factor_tight_putPut :
    GetPut (changeLog Bool Bool) ∧ PutGet (changeLog Bool Bool) ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool)
      (nf (run (put true (put false (ret true))))) ∧
    (changeLog Bool Bool).interp logRet (put true (put false (ret true)) : Prog Bool Bool) ≠
      (changeLog Bool Bool).interp logRet
        (nf (run (put true (put false (ret true)) : Prog Bool Bool))) ∧
    (changeLog Bool Bool).interp logRet (put true (put false (ret true)) : Prog Bool Bool) ≠
      (changeLog Bool Bool).fromObs logRet
        (run (put true (put false (ret true)) : Prog Bool Bool)) := by
  refine ⟨changeLog_getPut, changeLog_putGet, rfl, fun h => ?_, fun h => ?_⟩
  · exact absurd (congrFun h false) (by decide)
  · exact absurd (congrFun h false) (by decide)

/-- Non-vacuity of the representation results: `inertHidden` (not the
intended model, and with a hidden component) satisfies get–put, put–get and
put–put. -/
theorem nv_interp_factor :
    GetPut (inertHidden Bool Bool Bool) ∧ PutGet (inertHidden Bool Bool Bool) ∧
    PutPut (inertHidden Bool Bool Bool) :=
  ⟨inertHidden_lawful.2.1, inertHidden_lawful.2.2.1, inertHidden_lawful.2.2.2⟩

/-- Non-vacuity of `interp_eq_of_obsEq_of_getPut_putGet_putPut`: all four
hypotheses hold for `inertHidden` (not the intended model, and with a hidden
component) and the observationally equivalent programs
`put true (put false (ret true))` and `put false (ret true)`. -/
theorem nv_interp_eq_of_obsEq :
    GetPut (inertHidden Bool Bool Bool) ∧ PutGet (inertHidden Bool Bool Bool) ∧
    PutPut (inertHidden Bool Bool Bool) ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool) (put false (ret true)) :=
  ⟨inertHidden_lawful.2.1, inertHidden_lawful.2.2.1, inertHidden_lawful.2.2.2, rfl⟩

/-- Tightness of `h : ObsEq p q` in
`interp_eq_of_obsEq_of_getPut_putGet_putPut`: the intended model satisfies
get–put, put–get and put–put, and interprets `ret true` and `ret false`
differently. -/
theorem interp_eq_tight_obsEq :
    GetPut (intended Bool Bool) ∧ PutGet (intended Bool Bool) ∧ PutPut (intended Bool Bool) ∧
    (intended Bool Bool).interp intendedRet (ret true : Prog Bool Bool) ≠
      (intended Bool Bool).interp intendedRet (ret false) := by
  refine ⟨intended_lawful.2.1, intended_lawful.2.2.1, intended_lawful.2.2.2, fun h => ?_⟩
  exact absurd (congrFun h false) (by decide)

/-! ## The intended model is free -/

/-- Tightness of `hGP` in `fromObs_isHom_unique_of_getPut_putGet_putPut`:
`dirtyBit` satisfies put–get and put–put, and `fromObs` is not a homomorphism
(it fails on returns). -/
theorem fromObs_tight_getPut :
    PutGet (dirtyBit Bool Bool) ∧ PutPut (dirtyBit Bool Bool) ∧
    ¬ IsHom (dirtyBit Bool Bool) pairRet ((dirtyBit Bool Bool).fromObs (V := Bool) pairRet) := by
  refine ⟨dirtyBit_putGet, dirtyBit_putPut, fun ⟨hret, _, _⟩ => ?_⟩
  exact absurd (congrFun (hret true) (false, false)) (by decide)

/-- Tightness of `hPG` in `fromObs_isHom_unique_of_getPut_putGet_putPut`:
`writesIgnored` satisfies get–put and put–put, and `fromObs` does not commute
with `put`. -/
theorem fromObs_tight_putGet :
    GetPut (writesIgnored Bool Bool) ∧ PutPut (writesIgnored Bool Bool) ∧
    ¬ IsHom (writesIgnored Bool Bool) intendedRet
      ((writesIgnored Bool Bool).fromObs (V := Bool) intendedRet) := by
  refine ⟨writesIgnored_getPut, writesIgnored_putPut, fun ⟨_, _, hput⟩ => ?_⟩
  exact absurd (congrFun (hput true (fun s => (s, s))) false) (by decide)

/-- Tightness of `hPP` in `fromObs_isHom_unique_of_getPut_putGet_putPut`:
`changeLog` satisfies get–put and put–get, and `fromObs` does not commute with
`put`. -/
theorem fromObs_tight_putPut :
    GetPut (changeLog Bool Bool) ∧ PutGet (changeLog Bool Bool) ∧
    ¬ IsHom (changeLog Bool Bool) logRet ((changeLog Bool Bool).fromObs (V := Bool) logRet) := by
  refine ⟨changeLog_getPut, changeLog_putGet, fun ⟨_, _, hput⟩ => ?_⟩
  exact absurd (congrFun (hput true (fun _ => (true, false))) false) (by decide)

/-- Non-vacuity of `fromObs_isHom_unique_of_getPut_putGet_putPut`: `valueOnly`
satisfies get–put, put–get and put–put. -/
theorem nv_fromObs_isHom :
    GetPut (valueOnly Bool Bool) ∧ PutGet (valueOnly Bool Bool) ∧ PutPut (valueOnly Bool Bool) :=
  ⟨valueOnly_lawful.2.1, valueOnly_lawful.2.2.1, valueOnly_lawful.2.2.2⟩

/-- The comparison map need not be surjective: for the strictly lawful
`inertHidden Bool Bool Bool` and the valuation `pairRet`, the carrier element
that returns `true` and flips the hidden bit is not `fromObs pairRet o` for any
intended observation `o`. -/
theorem fromObs_not_surjective_inertHidden :
    Lawful (inertHidden Bool Bool Bool) ∧
    ∃ x : Bool × Bool → Bool × (Bool × Bool),
      ∀ o : Bool → Bool × Bool, (inertHidden Bool Bool Bool).fromObs pairRet o ≠ x := by
  refine ⟨inertHidden_lawful, fun st => (true, (st.1, !st.2)), fun o h => ?_⟩
  have h2 := congrArg (fun r => r.2.2) (congrFun h (false, false))
  simp [Model.fromObs, inertHidden, pairRet] at h2

/-! ## Representation: homomorphic images of the intended model -/

/-- Non-vacuity of both sides of
`getPut_putGet_putPut_iff_exists_surjective_isHom`: `inertHidden` has a
surjective homomorphism from the intended model extending the identity, and
`dirtyBit` has none. -/
theorem nv_getPut_putGet_putPut_iff_exists_surjective_isHom :
    (∃ h, IsHom (inertHidden Bool Bool Bool) id h ∧ ∀ x, ∃ o, h o = x) ∧
    ¬ (∃ h, IsHom (dirtyBit Bool Bool) id h ∧ ∀ x, ∃ o, h o = x) := by
  refine ⟨(getPut_putGet_putPut_iff_exists_surjective_isHom _).1
    ⟨inertHidden_lawful.2.1, inertHidden_lawful.2.2.1, inertHidden_lawful.2.2.2⟩, fun h => ?_⟩
  exact dirtyBit_not_getPut ((getPut_putGet_putPut_iff_exists_surjective_isHom _).2 h).1

/-! ## Faithfulness across all valuations -/

/-- Non-vacuity of
`forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`:
`valueOnly Bool Bool` satisfies get–put, put–get and put–put and its carrier has
two distinct elements. -/
theorem nv_forall_interp_eq_iff_obsEq :
    GetPut (valueOnly Bool Bool) ∧ PutGet (valueOnly Bool Bool) ∧
    PutPut (valueOnly Bool Bool) ∧ ∃ x y : Bool → Bool, x ≠ y :=
  ⟨valueOnly_lawful.2.1, valueOnly_lawful.2.2.1, valueOnly_lawful.2.2.2,
   fun _ => true, fun _ => false, fun h => absurd (congrFun h false) (by decide)⟩

/-- Tightness of `hnt`: the one-point model satisfies get–put, put–get and
put–put, interprets `ret true` and `ret false` equally under every valuation,
and they are not observationally equivalent. -/
theorem forall_interp_tight_nontrivial :
    GetPut (unitModel Bool) ∧ PutGet (unitModel Bool) ∧ PutPut (unitModel Bool) ∧
    ¬ ((∀ ρ : Bool → Unit, (unitModel Bool).interp ρ (ret true : Prog Bool Bool) =
          (unitModel Bool).interp ρ (ret false)) ↔
        ObsEq (ret true : Prog Bool Bool) (ret false)) := by
  refine ⟨unitModel_lawful.2.1, unitModel_lawful.2.2.1, unitModel_lawful.2.2.2, fun h => ?_⟩
  exact absurd (congrFun (h.1 fun _ => rfl) false) (by decide)

/-- Tightness of `hGP`: `dirtyBit` satisfies put–get and put–put and has two
distinct carrier elements; `ret true` and its canonical program are
observationally equivalent but not interpreted equally under every valuation. -/
theorem forall_interp_tight_getPut :
    PutGet (dirtyBit Bool Bool) ∧ PutPut (dirtyBit Bool Bool) ∧
    (∃ x y : Bool × Bool → Bool × (Bool × Bool), x ≠ y) ∧
    ¬ ((∀ ρ : Bool → (Bool × Bool → Bool × (Bool × Bool)),
          (dirtyBit Bool Bool).interp ρ (ret true : Prog Bool Bool) =
            (dirtyBit Bool Bool).interp ρ (nf (run (ret true : Prog Bool Bool)))) ↔
        ObsEq (ret true : Prog Bool Bool) (nf (run (ret true)))) := by
  refine ⟨dirtyBit_putGet, dirtyBit_putPut,
    ⟨pairRet true, pairRet false, fun h => absurd (congrFun h (false, false)) (by decide)⟩,
    fun h => interp_factor_tight_getPut.2.2.2.1 (h.2 rfl pairRet)⟩

/-- Tightness of `hPG`: `writesIgnored` satisfies get–put and put–put and has
two distinct carrier elements; `put true (get ret)` and its canonical program
are observationally equivalent but not interpreted equally under every
valuation. -/
theorem forall_interp_tight_putGet :
    GetPut (writesIgnored Bool Bool) ∧ PutPut (writesIgnored Bool Bool) ∧
    (∃ x y : Bool → Bool × Bool, x ≠ y) ∧
    ¬ ((∀ ρ : Bool → (Bool → Bool × Bool),
          (writesIgnored Bool Bool).interp ρ (put true (get ret) : Prog Bool Bool) =
            (writesIgnored Bool Bool).interp ρ
              (nf (run (put true (get ret) : Prog Bool Bool)))) ↔
        ObsEq (put true (get ret) : Prog Bool Bool) (nf (run (put true (get ret))))) := by
  refine ⟨writesIgnored_getPut, writesIgnored_putPut,
    ⟨intendedRet true, intendedRet false, fun h => absurd (congrFun h false) (by decide)⟩,
    fun h => interp_factor_tight_putGet.2.2.2.1 (h.2 rfl intendedRet)⟩

/-- Tightness of `hPP`: `changeLog` satisfies get–put and put–get and has two
distinct carrier elements; `put true (put false (ret true))` and its canonical
program are observationally equivalent but not interpreted equally under every
valuation. -/
theorem forall_interp_tight_putPut :
    GetPut (changeLog Bool Bool) ∧ PutGet (changeLog Bool Bool) ∧
    (∃ x y : Bool → Bool × Bool × List Bool, x ≠ y) ∧
    ¬ ((∀ ρ : Bool → (Bool → Bool × Bool × List Bool),
          (changeLog Bool Bool).interp ρ (put true (put false (ret true)) : Prog Bool Bool) =
            (changeLog Bool Bool).interp ρ
              (nf (run (put true (put false (ret true)) : Prog Bool Bool)))) ↔
        ObsEq (put true (put false (ret true)) : Prog Bool Bool)
          (nf (run (put true (put false (ret true)))))) := by
  refine ⟨changeLog_getPut, changeLog_putGet,
    ⟨logRet true, logRet false, fun h => absurd (congrFun h false) (by decide)⟩,
    fun h => interp_factor_tight_putPut.2.2.2.1 (h.2 rfl logRet)⟩

/-! ## Hilbert–Post completeness -/

/-- Non-vacuity of `extDerivable_total_of_not_derivable`: `ret true = ret false`
is not derivable from the four laws. -/
theorem nv_extDerivable_total : ¬ Derivable allLaws (ret true : Prog Bool Bool) (ret false) := by
  intro h
  exact absurd (congrFun h.run_eq false) (by decide)

/-- Tightness of `h` in `extDerivable_total_of_not_derivable`: adding the
derivable equation `ret true = ret true` does not identify `ret true` with
`ret false`. -/
theorem extDerivable_tight :
    Derivable allLaws (ret true : Prog Bool Bool) (ret true) ∧
    ¬ ExtDerivable (ret true : Prog Bool Bool) (ret true) (ret true) (ret false) := by
  refine ⟨.refl _, fun h => ?_⟩
  have := h.run_eq_of (fun _ => rfl)
  exact absurd (congrFun this false) (by decide)

/-- Positive control for `extDerivable_total_of_not_derivable`: without
substitution instances the extension does not collapse.  `ret true = ret false`
is not derivable from the four laws, and adding it alone (`ExtDerivableNoSubst`,
closed under symmetry, transitivity and congruence) does not identify
`put true (ret true)` with `put false (ret true)` (soundness in the intended
model under the constant valuation `fun _ => intendedRet true`). -/
theorem extDerivableNoSubst_not_total :
    ¬ Derivable allLaws (ret true : Prog Bool Bool) (ret false) ∧
    ¬ ExtDerivableNoSubst (ret true : Prog Bool Bool) (ret false)
        (put true (ret true)) (put false (ret true)) := by
  refine ⟨nv_extDerivable_total, fun h => ?_⟩
  have := congrFun (h.sound (intended Bool Bool) intended_lawful (fun _ => intendedRet true) rfl)
    false
  exact absurd this (by decide)

end Toy.StoreLaws
