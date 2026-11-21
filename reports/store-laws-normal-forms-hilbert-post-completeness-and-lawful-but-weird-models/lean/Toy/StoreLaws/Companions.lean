import Toy.StoreLaws.Witnesses

/-!
# Store laws: companion lemmas

Supplementary lemmas that sharpen how the main results read. None of them
changes a main result.

* `isHom_id_surjective`: in `getPut_putGet_putPut_iff_exists_surjective_isHom`
  the surjectivity conjunct is implied by `IsHom M id h`, because the return
  clause sends `intendedRet x` to `x`.
* `getPut_putGet_putPut_iff_exists_isHom`: the same characterization with the
  surjectivity conjunct omitted.
* `empty_carrier_breaks_forall_interp_iff`: the hypothesis `hnt` of
  `forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial` excludes
  the empty carrier as well as one-point carriers.
* `empty_cell_getPut_not_nontrivial`: on an empty cell, get–put forces the
  carrier to have at most one element, so `hGP` and `hnt` of that result
  cannot hold together there.
* `writeLog_lawful_of_empty_cell`, `writeLog_lawful_of_empty_result`,
  `readCounter_lawful_of_empty_cell`, `readCounter_lawful_of_empty_result`:
  with an empty cell type or an empty result type, the write-log and
  read-counter models satisfy all four laws strictly, so the violations in
  `writeLog_strict_profile_bool` and `readCounter_strict_profile_bool` depend
  on inhabited cell and result types.
* `nv_inertHidden_interp_eq`: the instance `S = H = V = Bool` of
  `inertHidden_interp_eq`.
-/

namespace Toy.StoreLaws

open Prog

/-- `IsHom M id h` implies that `h` is surjective onto the carrier: the return
clause gives `h (intendedRet x) = x` for every `x`. -/
theorem isHom_id_surjective {S X : Type} (M : Model S X) (h : (S → X × S) → X)
    (hh : IsHom M id h) : ∀ x : X, ∃ o, h o = x :=
  fun x => ⟨intendedRet x, hh.1 x⟩

/-- The representation theorem without the (implied) surjectivity conjunct: a
model satisfies get–put, put–get and put–put strictly iff some map from intended
observations to its carrier is a homomorphism from the intended model with result
type `X` that sends `intendedRet x` to `x`. -/
theorem getPut_putGet_putPut_iff_exists_isHom {S X : Type} (M : Model S X) :
    (GetPut M ∧ PutGet M ∧ PutPut M) ↔ ∃ h : (S → X × S) → X, IsHom M id h := by
  rw [getPut_putGet_putPut_iff_exists_surjective_isHom]
  constructor
  · rintro ⟨h, hh, -⟩
    exact ⟨h, hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, hh, isHom_id_surjective M h hh⟩

/-- A model on a Boolean cell with the empty carrier satisfies get–put, put–get
and put–put strictly, yet interprets `ret true` and `ret false` equally under every
valuation `Bool → Empty` (there is none), although the two programs are not
observationally equivalent. -/
theorem empty_carrier_breaks_forall_interp_iff :
    ∃ M : Model Bool Empty, GetPut M ∧ PutGet M ∧ PutPut M ∧
      ¬ ((∀ ρ : Bool → Empty, M.interp ρ (ret true : Prog Bool Bool) =
            M.interp ρ (ret false)) ↔
          ObsEq (ret true : Prog Bool Bool) (ret false)) := by
  refine ⟨⟨fun k => k false, fun _ x => x⟩, fun x => Empty.elim x,
    fun _ k => Empty.elim (k false), fun _ _ x => Empty.elim x, fun h => ?_⟩
  have hobs : ObsEq (ret true : Prog Bool Bool) (ret false) :=
    h.1 (fun ρ => Empty.elim (ρ false))
  exact absurd (congrFun hobs false) (by decide)

/-- On an empty cell, a model satisfying get–put strictly has no two distinct
carrier elements. -/
theorem empty_cell_getPut_not_nontrivial {X : Type} (M : Model Empty X)
    (hGP : GetPut M) : ¬ ∃ x y : X, x ≠ y := by
  rintro ⟨x, y, hne⟩
  exact hne (empty_cell_subsingleton_of_getPut M hGP x y)

/-- With an empty cell type, the write-log model satisfies all four laws
strictly (its carrier `Empty → V × Empty × List Empty` has one element). -/
theorem writeLog_lawful_of_empty_cell {V : Type} : Lawful (writeLog Empty V) :=
  ⟨fun _ => funext fun s => Empty.elim s,
   fun _ => funext fun s => Empty.elim s,
   fun s => Empty.elim s,
   fun s => Empty.elim s⟩

/-- With an empty result type, the write-log model satisfies all four laws
strictly, for every cell type. -/
theorem writeLog_lawful_of_empty_result {S : Type} : Lawful (writeLog S Empty) :=
  ⟨fun k => funext fun s => Empty.elim (k s s s).1,
   fun x => funext fun s => Empty.elim (x s).1,
   fun _ k => funext fun s => Empty.elim (k s s).1,
   fun _ _ x => funext fun s => Empty.elim (x s).1⟩

/-- With an empty cell type, the read-counter model satisfies all four laws
strictly (its carrier `Empty → V × Empty × Nat` has one element). -/
theorem readCounter_lawful_of_empty_cell {V : Type} : Lawful (readCounter Empty V) :=
  ⟨fun _ => funext fun s => Empty.elim s,
   fun _ => funext fun s => Empty.elim s,
   fun s => Empty.elim s,
   fun s => Empty.elim s⟩

/-- With an empty result type, the read-counter model satisfies all four laws
strictly, for every cell type. -/
theorem readCounter_lawful_of_empty_result {S : Type} : Lawful (readCounter S Empty) :=
  ⟨fun k => funext fun s => Empty.elim (k s s s).1,
   fun x => funext fun s => Empty.elim (x s).1,
   fun _ k => funext fun s => Empty.elim (k s s).1,
   fun _ _ x => funext fun s => Empty.elim (x s).1⟩

/-- The instance `S = H = V = Bool` of `inertHidden_interp_eq`. -/
theorem nv_inertHidden_interp_eq :
    Lawful (inertHidden Bool Bool Bool) ∧
    ∀ (p : Prog Bool Bool) (s h : Bool),
      (inertHidden Bool Bool Bool).interp pairRet p (s, h) = ((run p s).1, ((run p s).2, h)) :=
  inertHidden_interp_eq

end Toy.StoreLaws
