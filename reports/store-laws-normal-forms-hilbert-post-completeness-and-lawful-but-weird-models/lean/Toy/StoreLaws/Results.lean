import Toy.StoreLaws.Profiles

/-!
# Store laws: main results

Results are grouped by the question they answer.

* Law structure: get–get follows from get–put and put–get
  (`getGet_of_getPut_of_putGet`); get–put, put–get and put–put are mutually
  independent (`getPut_putGet_putPut_independent_bool`); get–get is not implied
  by either of the other two pairs that contain put–put
  (`getGet_not_entailed_by_pairs_with_putPut_bool`); together these give the
  full entailment relation among the four laws for a Boolean cell
  (`entailsBool_iff`).
* Normal forms: every program is derivably equal to the canonical program of
  its intended observation (`derivable_nf_of_getPut_putGet_putPut`); canonical
  programs are unique up to derivability (`canon_eq_of_derivable`);
  derivability coincides with observational equivalence
  (`derivable_iff_obsEq_of_getPut_putGet_putPut`).
* Representation: in every model satisfying get–put, put–get and put–put
  strictly, interpretation factors through the intended observation
  (`interp_eq_fromObs_run_of_getPut_putGet_putPut`), so such models never
  distinguish observationally equivalent programs
  (`interp_eq_of_obsEq_of_getPut_putGet_putPut`); the comparison map is the
  unique homomorphism out of the intended model
  (`fromObs_isHom_unique_of_getPut_putGet_putPut`); a model satisfies the three
  laws strictly iff it is a homomorphic image of the intended model on its own
  carrier (`getPut_putGet_putPut_iff_exists_surjective_isHom`); at a fixed
  valuation lawful models need not be faithful (`valueOnly_lawful_not_faithful`,
  `unitModel_lawful_not_faithful`), but across all valuations every lawful model
  with two distinct carrier elements is
  (`forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`).
* Hilbert–Post completeness (`extDerivable_total_of_not_derivable`).
* Hidden state: a write log satisfies all four laws through the log-forgetting
  observation and distinguishes observationally equivalent programs
  (`writeLog_via_distinguishes_obsEq`), but violates get–put and put–put
  strictly (`writeLog_strict_profile_bool`); a read counter violates all laws but
  put–put (`readCounter_strict_profile_bool`); an inert hidden component is
  strictly lawful (`inertHidden_interp_eq`).
* Dropping a law: dropping get–get changes no derivability
  (`derivable_lawsExcept_getGet_iff`); dropping any other law loses an
  equation between observationally equivalent programs
  (`dropGetPut_loses_nf`, `dropPutGet_loses_nf`, `dropPutPut_loses_nf`).
-/

namespace Toy.StoreLaws

open Prog

/-! ## Law structure -/

/-- In every model on every carrier, get–put and put–get (strictly) imply
get–get (strictly). -/
theorem getGet_of_getPut_of_putGet {S X : Type} (M : Model S X) (hGP : GetPut M)
    (hPG : PutGet M) : GetGet M := by
  intro k
  rw [← hGP (M.get fun s => M.get fun s' => k s s'), ← hGP (M.get fun s => k s s)]
  have hPG' : ∀ (s : S) (k : S → X), M.put s (M.get k) = M.put s (k s) := hPG
  congr 1
  funext t
  simp only [hPG']

/-- On a Boolean cell with Boolean results, get–put, put–get and put–put are
mutually independent, even in the presence of get–get: `changeLog` satisfies
all laws but put–put, `writesIgnored` all but put–get, `dirtyBit` all but
get–put. -/
theorem getPut_putGet_putPut_independent_bool :
    (GetGet (changeLog Bool Bool) ∧ GetPut (changeLog Bool Bool) ∧
      PutGet (changeLog Bool Bool) ∧ ¬ PutPut (changeLog Bool Bool)) ∧
    (GetGet (writesIgnored Bool Bool) ∧ GetPut (writesIgnored Bool Bool) ∧
      PutPut (writesIgnored Bool Bool) ∧ ¬ PutGet (writesIgnored Bool Bool)) ∧
    (GetGet (dirtyBit Bool Bool) ∧ PutGet (dirtyBit Bool Bool) ∧
      PutPut (dirtyBit Bool Bool) ∧ ¬ GetPut (dirtyBit Bool Bool)) :=
  ⟨⟨changeLog_getGet, changeLog_getPut, changeLog_putGet, changeLog_not_putPut⟩,
   ⟨writesIgnored_getGet, writesIgnored_getPut, writesIgnored_putPut, writesIgnored_not_putGet⟩,
   ⟨dirtyBit_getGet, dirtyBit_putGet, dirtyBit_putPut, dirtyBit_not_getPut⟩⟩

/-- On a Boolean cell with Boolean results, get–get follows neither from
get–put with put–put (`readToClear`) nor from put–get with put–put
(`faultingCounter`). -/
theorem getGet_not_entailed_by_pairs_with_putPut_bool :
    (GetPut (readToClear Bool Bool false) ∧ PutPut (readToClear Bool Bool false) ∧
      ¬ GetGet (readToClear Bool Bool false)) ∧
    (PutGet (faultingCounter Bool Bool) ∧ PutPut (faultingCounter Bool Bool) ∧
      ¬ GetGet (faultingCounter Bool Bool)) :=
  ⟨⟨readToClear_getPut false, readToClear_putPut false, readToClear_not_getGet⟩,
   ⟨faultingCounter_putGet, faultingCounter_putPut, faultingCounter_not_getGet⟩⟩

/-- The complete entailment relation among the four laws for models on a
Boolean cell (any carrier): a set of laws `Γ` entails law `l` iff `l ∈ Γ`, or
`l` is get–get and both get–put and put–get are in `Γ`. -/
theorem entailsBool_iff (Γ : LawSet) (l : Law) :
    EntailsBool Γ l ↔ (Γ l ∨ (l = .getGet ∧ Γ .getPut ∧ Γ .putGet)) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hl : ¬ Γ l := fun hl => hn (Or.inl hl)
    cases l with
    | putPut =>
      have hsat : SatisfiesAll Γ (changeLog Bool Bool) := by
        intro l' hl'
        cases l' with
        | getGet => exact changeLog_getGet
        | getPut => exact changeLog_getPut
        | putGet => exact changeLog_putGet
        | putPut => exact absurd hl' hl
      exact changeLog_not_putPut (h _ _ hsat)
    | putGet =>
      have hsat : SatisfiesAll Γ (writesIgnored Bool Bool) := by
        intro l' hl'
        cases l' with
        | getGet => exact writesIgnored_getGet
        | getPut => exact writesIgnored_getPut
        | putGet => exact absurd hl' hl
        | putPut => exact writesIgnored_putPut
      exact writesIgnored_not_putGet (h _ _ hsat)
    | getPut =>
      have hsat : SatisfiesAll Γ (dirtyBit Bool Bool) := by
        intro l' hl'
        cases l' with
        | getGet => exact dirtyBit_getGet
        | getPut => exact absurd hl' hl
        | putGet => exact dirtyBit_putGet
        | putPut => exact dirtyBit_putPut
      exact dirtyBit_not_getPut (h _ _ hsat)
    | getGet =>
      have hpair : ¬ (Γ .getPut ∧ Γ .putGet) := fun hp => hn (Or.inr ⟨rfl, hp⟩)
      by_cases hPG : Γ .putGet
      · have hGP : ¬ Γ .getPut := fun hGP => hpair ⟨hGP, hPG⟩
        have hsat : SatisfiesAll Γ (faultingCounter Bool Bool) := by
          intro l' hl'
          cases l' with
          | getGet => exact absurd hl' hl
          | getPut => exact absurd hl' hGP
          | putGet => exact faultingCounter_putGet
          | putPut => exact faultingCounter_putPut
        exact faultingCounter_not_getGet (h _ _ hsat)
      · have hsat : SatisfiesAll Γ (readToClear Bool Bool false) := by
          intro l' hl'
          cases l' with
          | getGet => exact absurd hl' hl
          | getPut => exact readToClear_getPut false
          | putGet => exact absurd hl' hPG
          | putPut => exact readToClear_putPut false
        exact readToClear_not_getGet (h _ _ hsat)
  · rintro (hl | ⟨rfl, hGP, hPG⟩) X M hM
    · exact hM l hl
    · exact getGet_of_getPut_of_putGet M (hM _ hGP) (hM _ hPG)

/-! ## Normal forms -/

/-- From any law set containing get–put, put–get and put–put, every program
`p` is derivably equal to the canonical program
`get (fun s => put (run p s).2 (ret (run p s).1))` of its intended
observation. -/
theorem derivable_nf_of_getPut_putGet_putPut {S V : Type} (L : LawSet) (hGP : L .getPut)
    (hPG : L .putGet) (hPP : L .putPut) (p : Prog S V) : Derivable L p (nf (run p)) := by
  induction p with
  | ret v => exact (Derivable.getPut hGP (ret v)).symm
  | get k ih =>
    exact (Derivable.get_congr ih).trans
      (Derivable.getGet_of hGP hPG fun s s' => put (run (k s) s').2 (ret (run (k s) s').1))
  | put t p ih =>
    exact (Derivable.put_congr t ih).trans <|
      (Derivable.putGet hPG t _).trans <|
      (Derivable.putPut hPP t _ _).trans (Derivable.get_const_put hGP hPP _ _).symm

/-- Canonical programs are unique up to derivability: for any law set `L`, if
`canon f g` and `canon f' g'` are derivably equal from `L`, then `f = f'` and
`g = g'`. -/
theorem canon_eq_of_derivable {S V : Type} {L : LawSet} {f f' : S → S} {g g' : S → V}
    (h : Derivable L (canon f g) (canon f' g')) : f = f' ∧ g = g' := by
  have hr := h.run_eq
  refine ⟨funext fun s => ?_, funext fun s => ?_⟩
  · exact congrArg Prod.snd (congrFun hr s)
  · exact congrArg Prod.fst (congrFun hr s)

/-- For any law set containing get–put, put–get and put–put, derivability
coincides with observational equivalence in the intended model. -/
theorem derivable_iff_obsEq_of_getPut_putGet_putPut {S V : Type} (L : LawSet)
    (hGP : L .getPut) (hPG : L .putGet) (hPP : L .putPut) (p q : Prog S V) :
    Derivable L p q ↔ ObsEq p q := by
  constructor
  · exact Derivable.run_eq
  · intro h
    have hp := derivable_nf_of_getPut_putGet_putPut L hGP hPG hPP p
    have hq := derivable_nf_of_getPut_putGet_putPut L hGP hPG hPP q
    unfold ObsEq at h
    rw [h] at hp
    exact hp.trans hq.symm

/-! ## Representation up to observation -/

/-- In every model satisfying get–put, put–get and put–put strictly, under every
valuation `ρ`, the interpretation of a program is the comparison map applied to
its intended observation:
`M.interp ρ p = M.get (fun s => M.put (run p s).2 (ρ (run p s).1))`. -/
theorem interp_eq_fromObs_run_of_getPut_putGet_putPut {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) (p : Prog S V) :
    M.interp ρ p = M.fromObs ρ (run p) := by
  have hM : SatisfiesAll allLaws M :=
    lawful_satisfiesAll ⟨getGet_of_getPut_of_putGet M hGP hPG, hGP, hPG, hPP⟩ allLaws
  exact (derivable_nf_of_getPut_putGet_putPut allLaws trivial trivial trivial p).sound M hM ρ

/-- No model satisfying get–put, put–get and put–put strictly distinguishes two
observationally equivalent programs, under any valuation. -/
theorem interp_eq_of_obsEq_of_getPut_putGet_putPut {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) {p q : Prog S V}
    (h : ObsEq p q) : M.interp ρ p = M.interp ρ q := by
  rw [interp_eq_fromObs_run_of_getPut_putGet_putPut M hGP hPG hPP ρ p,
    interp_eq_fromObs_run_of_getPut_putGet_putPut M hGP hPG hPP ρ q]
  unfold ObsEq at h
  rw [h]

/-- For every model satisfying get–put, put–get and put–put strictly and every
valuation `ρ`, the comparison map `M.fromObs ρ` is a homomorphism from the
intended model (returns `intendedRet`) to `M` (returns `ρ`), and it is the only
one: the intended model is the free model of the laws. -/
theorem fromObs_isHom_unique_of_getPut_putGet_putPut {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) :
    IsHom M ρ (M.fromObs ρ) ∧ ∀ h, IsHom M ρ h → h = M.fromObs ρ := by
  refine ⟨⟨fun v => hGP (ρ v), fun k => ?_, fun t o => ?_⟩, ?_⟩
  · exact (getGet_of_getPut_of_putGet M hGP hPG
      (fun s s' => M.put (k s s').2 (ρ (k s s').1))).symm
  · show M.get (fun _ => M.put (o t).2 (ρ (o t).1)) =
      M.put t (M.get fun s => M.put (o s).2 (ρ (o s).1))
    rw [hPG, hPP, get_const_put_of hGP hPP]
  · rintro h ⟨hret, hget, hput⟩
    funext o
    show h ((intended S V).get
        (fun s => (intended S V).put (o s).2 (intendedRet (o s).1))) = M.fromObs ρ o
    rw [hget]
    show M.get (fun s => h ((intended S V).put (o s).2 (intendedRet (o s).1))) =
      M.get (fun s => M.put (o s).2 (ρ (o s).1))
    simp only [hput, hret]

/-- For a model satisfying get–put, put–get and put–put strictly and any
valuation `ρ`, the elements of the carrier reached by the comparison map
`M.fromObs ρ` are exactly the interpretations of programs under `ρ`. -/
theorem fromObs_range_eq_interp_range {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) (x : X) :
    (∃ o : S → V × S, M.fromObs ρ o = x) ↔ (∃ p : Prog S V, M.interp ρ p = x) := by
  constructor
  · rintro ⟨o, rfl⟩
    refine ⟨nf o, ?_⟩
    rw [interp_eq_fromObs_run_of_getPut_putGet_putPut M hGP hPG hPP ρ (nf o), run_nf]
  · rintro ⟨p, rfl⟩
    exact ⟨run p, (interp_eq_fromObs_run_of_getPut_putGet_putPut M hGP hPG hPP ρ p).symm⟩

/-- Representation theorem: a model `M` on carrier `X` satisfies get–put,
put–get and put–put strictly iff there is a homomorphism from the intended model
with result type `X` (returns `intendedRet`) to `M` that maps returns by the
identity and is surjective; that is, iff `M` is a homomorphic image (a quotient)
of the intended model `intended S X`. -/
theorem getPut_putGet_putPut_iff_exists_surjective_isHom {S X : Type} (M : Model S X) :
    (GetPut M ∧ PutGet M ∧ PutPut M) ↔
      ∃ h : (S → X × S) → X, IsHom M id h ∧ ∀ x : X, ∃ o, h o = x := by
  constructor
  · rintro ⟨hGP, hPG, hPP⟩
    exact ⟨M.fromObs id, (fromObs_isHom_unique_of_getPut_putGet_putPut M hGP hPG hPP id).1,
      fun x => ⟨intendedRet x, hGP x⟩⟩
  · rintro ⟨h, ⟨hret, hget, hput⟩, -⟩
    have hx : ∀ x : X, h (intendedRet x) = x := hret
    refine ⟨fun x => ?_, fun s k => ?_, fun s s' x => ?_⟩
    · calc M.get (fun s => M.put s x)
          = M.get (fun s => M.put s (h (intendedRet x))) := by simp only [hx]
        _ = M.get (fun s => h ((intended S X).put s (intendedRet x))) := by simp only [hput]
        _ = h ((intended S X).get (fun s => (intended S X).put s (intendedRet x))) :=
            (hget _).symm
        _ = h (intendedRet x) := rfl
        _ = x := hx x
    · calc M.put s (M.get k)
          = M.put s (M.get (fun t => h (intendedRet (k t)))) := by simp only [hx]
        _ = M.put s (h ((intended S X).get (fun t => intendedRet (k t)))) := by rw [hget]
        _ = h ((intended S X).put s ((intended S X).get (fun t => intendedRet (k t)))) :=
            (hput _ _).symm
        _ = h ((intended S X).put s (intendedRet (k s))) := rfl
        _ = M.put s (h (intendedRet (k s))) := hput _ _
        _ = M.put s (k s) := by rw [hx]
    · calc M.put s (M.put s' x)
          = M.put s (M.put s' (h (intendedRet x))) := by rw [hx]
        _ = h ((intended S X).put s ((intended S X).put s' (intendedRet x))) := by
            rw [hput, hput]
        _ = h ((intended S X).put s' (intendedRet x)) := rfl
        _ = M.put s' (h (intendedRet x)) := hput _ _
        _ = M.put s' x := by rw [hx]

/-- Lawful does not imply faithful at a fixed valuation: on a Boolean cell with
Boolean results, `valueOnly` (final cell content not observed) satisfies all
four laws strictly and, under the valuation `valueOnlyRet`, distinguishes
`ret true` from `ret false` yet identifies `put true (ret true)` and
`put false (ret true)`, which are not observationally equivalent. -/
theorem valueOnly_lawful_not_faithful :
    Lawful (valueOnly Bool Bool) ∧
    ¬ ObsEq (put true (ret true) : Prog Bool Bool) (put false (ret true)) ∧
    (valueOnly Bool Bool).interp valueOnlyRet (put true (ret true) : Prog Bool Bool) =
      (valueOnly Bool Bool).interp valueOnlyRet (put false (ret true)) ∧
    (valueOnly Bool Bool).interp valueOnlyRet (ret true : Prog Bool Bool) ≠
      (valueOnly Bool Bool).interp valueOnlyRet (ret false) := by
  refine ⟨valueOnly_lawful, ?_, rfl, ?_⟩
  · intro h
    exact absurd (congrFun h false) (by decide)
  · intro h
    exact absurd (congrFun h false) (by decide)

/-- The identification in `valueOnly_lawful_not_faithful` depends on the
valuation and is not closed under substitution: under the valuation that
returns the cell content, and for the substitution instance that replaces each
returned value by `get ret`, `valueOnly Bool Bool` separates
`put true (ret true)` from `put false (ret true)`. -/
theorem valueOnly_separates_other_valuation_and_substitution :
    (valueOnly Bool Bool).interp (fun _ s => s) (put true (ret true) : Prog Bool Bool) ≠
      (valueOnly Bool Bool).interp (fun _ s => s) (put false (ret true)) ∧
    (valueOnly Bool Bool).interp valueOnlyRet
        ((put true (ret true) : Prog Bool Bool).bind (fun _ => get ret)) ≠
      (valueOnly Bool Bool).interp valueOnlyRet
        ((put false (ret true) : Prog Bool Bool).bind (fun _ => get ret)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd (congrFun h false) (by decide)
  · exact absurd (congrFun h false) (by decide)

/-- The one-point model satisfies all four laws strictly and identifies
`ret true` and `ret false`, which are not observationally equivalent. -/
theorem unitModel_lawful_not_faithful :
    Lawful (unitModel Bool) ∧
    ¬ ObsEq (ret true : Prog Bool Bool) (ret false) ∧
    (unitModel Bool).interp (fun _ => ()) (ret true : Prog Bool Bool) =
      (unitModel Bool).interp (fun _ => ()) (ret false) := by
  refine ⟨unitModel_lawful, ?_, rfl⟩
  intro h
  have := congrFun h false
  exact absurd this (by decide)

/-- Across all valuations, lawful models are faithful unless trivial: for every
model `M` on a carrier `X` with two distinct elements that satisfies get–put,
put–get and put–put strictly, two programs are interpreted equally under every
valuation `ρ : V → X` iff they are observationally equivalent. -/
theorem forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial {S X V : Type}
    (M : Model S X) (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M)
    (hnt : ∃ x y : X, x ≠ y) (p q : Prog S V) :
    (∀ ρ : V → X, M.interp ρ p = M.interp ρ q) ↔ ObsEq p q := by
  classical
  constructor
  · intro hall
    apply Classical.byContradiction
    intro hne
    have hex : ∃ s₀, run p s₀ ≠ run q s₀ :=
      Classical.byContradiction fun hc =>
        hne (funext fun s => Classical.byContradiction fun hh => hc ⟨s, hh⟩)
    obtain ⟨s₀, hs⟩ := hex
    obtain ⟨x₀, y₀, hxy⟩ := hnt
    have hkey : ∀ ρ : V → X,
        M.put (run p s₀).2 (ρ (run p s₀).1) = M.put (run q s₀).2 (ρ (run q s₀).1) := by
      intro ρ
      have h1 := congrArg (M.put s₀) (hall ρ)
      rw [interp_eq_fromObs_run_of_getPut_putGet_putPut M hGP hPG hPP ρ p,
          interp_eq_fromObs_run_of_getPut_putGet_putPut M hGP hPG hPP ρ q] at h1
      unfold Model.fromObs at h1
      rw [hPG, hPG, hPP, hPP] at h1
      exact h1
    have hput_eq : ∀ a : S, M.put a x₀ = M.put a y₀ := by
      intro a
      by_cases hv : (run p s₀).1 = (run q s₀).1
      · have ht : (run p s₀).2 ≠ (run q s₀).2 := fun ht => hs (Prod.ext hv ht)
        let k : S → X := fun s => if s = (run p s₀).2 then M.put a x₀ else M.put a y₀
        have hk := hkey (fun _ => M.get k)
        rw [hPG, hPG] at hk
        simp only [k, ↓reduceIte, Ne.symm ht] at hk
        rw [hPP, hPP] at hk
        exact hk
      · let ρ : V → X := fun v => if v = (run p s₀).1 then M.put a x₀ else M.put a y₀
        have hρ := hkey ρ
        simp only [ρ, ↓reduceIte, Ne.symm hv] at hρ
        rw [hPP, hPP] at hρ
        exact hρ
    have hxy_eq : x₀ = y₀ := by
      rw [← hGP x₀, ← hGP y₀]
      exact congrArg M.get (funext hput_eq)
    exact hxy hxy_eq
  · intro hobs ρ
    exact interp_eq_of_obsEq_of_getPut_putGet_putPut M hGP hPG hPP ρ hobs

/-! ## Hilbert–Post completeness -/

/-- Hilbert–Post completeness of the four laws: if `p₀ = q₀` is not derivable
from the four laws, then adding it (with all its substitution instances
`p₀.bind σ = q₀.bind σ`, `σ : V → Prog S V`) makes every two programs of type
`Prog S V` derivably equal. -/
theorem extDerivable_total_of_not_derivable {S V : Type} (p₀ q₀ : Prog S V)
    (h : ¬ Derivable allLaws p₀ q₀) (p q : Prog S V) : ExtDerivable p₀ q₀ p q := by
  classical
  have hiff := derivable_iff_obsEq_of_getPut_putGet_putPut (S := S) (V := V) allLaws
    trivial trivial trivial
  have hne : run p₀ ≠ run q₀ := fun he => h ((hiff p₀ q₀).2 he)
  have hex : ∃ s₀, run p₀ s₀ ≠ run q₀ s₀ :=
    Classical.byContradiction fun hc =>
      hne (funext fun s => Classical.byContradiction fun hh => hc ⟨s, hh⟩)
  obtain ⟨s₀, hs⟩ := hex
  -- `put s₀ p₀ = put s₀ q₀` reduces, by completeness, to an equation between
  -- two "write then return" programs.
  have hp : Derivable allLaws (put s₀ p₀) (put (run p₀ s₀).2 (ret (run p₀ s₀).1)) :=
    (hiff _ _).2 rfl
  have hq : Derivable allLaws (put s₀ q₀) (put (run q₀ s₀).2 (ret (run q₀ s₀).1)) :=
    (hiff _ _).2 rfl
  have hkey : ExtDerivable p₀ q₀ (put (run p₀ s₀).2 (ret (run p₀ s₀).1))
      (put (run q₀ s₀).2 (ret (run q₀ s₀).1)) :=
    (ExtDerivable.of_derivable hp.symm).trans
      ((ExtDerivable.put_congr s₀ (ExtDerivable.base p₀ q₀)).trans (.of_derivable hq))
  apply ExtDerivable.total_of_put
  intro a z z'
  suffices hsuff :
      ExtDerivable p₀ q₀ (put (run p₀ s₀).2 (put a z)) (put (run q₀ s₀).2 (put a z')) from
    (ExtDerivable.of_derivable (Derivable.putPut trivial _ _ _).symm).trans
      (hsuff.trans (.of_derivable (Derivable.putPut trivial _ _ _)))
  by_cases hv : (run p₀ s₀).1 = (run q₀ s₀).1
  · -- Same returned value, different final cell: substitute a read that
    -- branches on the final cell.
    have ht : (run p₀ s₀).2 ≠ (run q₀ s₀).2 := fun ht => hs (Prod.ext hv ht)
    let k : S → Prog S V := fun s => if s = (run p₀ s₀).2 then put a z else put a z'
    have hsub := hkey.bind_left (fun _ => get k)
    change ExtDerivable p₀ q₀ (put (run p₀ s₀).2 (get k)) (put (run q₀ s₀).2 (get k)) at hsub
    have e₁ : k (run p₀ s₀).2 = put a z := by simp [k]
    have e₂ : k (run q₀ s₀).2 = put a z' := by simp [k, Ne.symm ht]
    have h₁ := Derivable.putGet (L := allLaws) trivial (run p₀ s₀).2 k
    have h₂ := Derivable.putGet (L := allLaws) trivial (run q₀ s₀).2 k
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact (ExtDerivable.of_derivable h₁.symm).trans (hsub.trans (.of_derivable h₂))
  · -- Different returned values: substitute different writes for them.
    let σ : V → Prog S V := fun v => if v = (run p₀ s₀).1 then put a z else put a z'
    have hsub := hkey.bind_left σ
    change ExtDerivable p₀ q₀ (put (run p₀ s₀).2 (σ (run p₀ s₀).1))
      (put (run q₀ s₀).2 (σ (run q₀ s₀).1)) at hsub
    have e₁ : σ (run p₀ s₀).1 = put a z := by simp [σ]
    have e₂ : σ (run q₀ s₀).1 = put a z' := by simp [σ, Ne.symm hv]
    rw [e₁, e₂] at hsub
    exact hsub

/-- On an empty cell every two programs are derivably equal from the four laws. -/
theorem empty_cell_all_derivable {V : Type} (p q : Prog Empty V) : Derivable allLaws p q :=
  (derivable_iff_obsEq_of_getPut_putGet_putPut allLaws trivial trivial trivial p q).2
    (funext fun s => Empty.elim s)

/-- On a one-element cell with one-element results every two programs are
derivably equal from the four laws. -/
theorem unit_cell_unit_result_all_derivable (p q : Prog Unit Unit) : Derivable allLaws p q :=
  (derivable_iff_obsEq_of_getPut_putGet_putPut allLaws trivial trivial trivial p q).2
    (funext fun _ => Prod.ext rfl rfl)

/-! ## Hidden state: strict versus observational satisfaction -/

/-- The write-log model satisfies all four laws when they are checked through
the observation `dropLog` that forgets the log. -/
theorem writeLog_laws_via_dropLog {S V : Type} :
    GetGetVia dropLog (writeLog S V) ∧ GetPutVia dropLog (writeLog S V) ∧
    PutGetVia dropLog (writeLog S V) ∧ PutPutVia dropLog (writeLog S V) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Satisfaction through a non-injective observation does not prevent hidden
state from distinguishing programs: on a Boolean cell with Boolean results, the
write log satisfies all four laws through the log-forgetting observation
`dropLog`, yet under the valuation `logRet` it interprets the observationally
equivalent programs `put true (put false (ret true))` and `put false (ret true)`
differently. -/
theorem writeLog_via_distinguishes_obsEq :
    (GetGetVia dropLog (writeLog Bool Bool) ∧ GetPutVia dropLog (writeLog Bool Bool) ∧
      PutGetVia dropLog (writeLog Bool Bool) ∧ PutPutVia dropLog (writeLog Bool Bool)) ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool) (put false (ret true)) ∧
    (writeLog Bool Bool).interp logRet (put true (put false (ret true)) : Prog Bool Bool) ≠
      (writeLog Bool Bool).interp logRet (put false (ret true)) := by
  refine ⟨writeLog_laws_via_dropLog, rfl, fun h => ?_⟩
  exact absurd (congrFun h false) (by decide)

/-- Strictly (as equations in its carrier, which includes the log), the
write-log model on a Boolean cell with Boolean results satisfies get–get and
put–get and violates get–put and put–put. -/
theorem writeLog_strict_profile_bool :
    GetGet (writeLog Bool Bool) ∧ PutGet (writeLog Bool Bool) ∧
    ¬ GetPut (writeLog Bool Bool) ∧ ¬ PutPut (writeLog Bool Bool) :=
  ⟨writeLog_getGet, writeLog_putGet, writeLog_not_getPut, writeLog_not_putPut⟩

/-- Strictly (as equations in its carrier, which includes the read count), the
read-counter model on a Boolean cell with Boolean results satisfies put–put and
violates get–get, get–put and put–get. -/
theorem readCounter_strict_profile_bool :
    PutPut (readCounter Bool Bool) ∧ ¬ GetGet (readCounter Bool Bool) ∧
    ¬ GetPut (readCounter Bool Bool) ∧ ¬ PutGet (readCounter Bool Bool) :=
  ⟨readCounter_putPut, readCounter_not_getGet, readCounter_not_getPut, readCounter_not_putGet⟩

/-- A hidden component that no operation reads or writes is compatible with all
four laws strictly, and it is inert: from `(s, h)`, every program returns
`(run p s).1`, leaves the cell at `(run p s).2`, and leaves the hidden component
at `h`. -/
theorem inertHidden_interp_eq {S H V : Type} :
    Lawful (inertHidden S H V) ∧
    ∀ (p : Prog S V) (s : S) (h : H),
      (inertHidden S H V).interp pairRet p (s, h) = ((run p s).1, ((run p s).2, h)) := by
  refine ⟨inertHidden_lawful, fun p => ?_⟩
  induction p with
  | ret v => intro s h; rfl
  | get k ih => intro s h; exact ih s s h
  | put t p ih => intro s h; exact ih t h

/-- Under a valuation other than `pairRet`, the strictly lawful `inertHidden`
model can change the hidden component: with `pairFlipRet`, `ret true` run from
`(false, false)` ends with hidden component `true`. -/
theorem inertHidden_pairFlipRet_changes_hidden :
    Lawful (inertHidden Bool Bool Bool) ∧
    (inertHidden Bool Bool Bool).interp pairFlipRet (ret true : Prog Bool Bool) (false, false) =
      (true, (false, true)) :=
  ⟨inertHidden_lawful, rfl⟩

/-- Strictly lawful hidden state need not be left untouched by `put`: the
coupled hidden bit satisfies all four laws strictly, and under `pairRet` the
program `put true (ret true)` run from `(false, false)` ends with hidden
component `true`. -/
theorem coupledHidden_lawful_changes_hidden :
    Lawful (coupledHidden Bool) ∧
    (coupledHidden Bool).interp pairRet (put true (ret true) : Prog Bool Bool) (false, false) =
      (true, (true, true)) :=
  ⟨coupledHidden_lawful, rfl⟩

/-- Effects carried by the valuation are compatible with strict satisfaction:
the intended model with results `Bool × List Bool` (a log carried with the
returned value, as in a state-over-writer monad) satisfies all four laws
strictly, and with a valuation that logs `true` at every return, the program
`put true (ret false)` run from `false` returns `(false, [true])` and ends with
cell `true`. -/
theorem intended_leafLog_lawful_and_logs :
    Lawful (intended Bool (Bool × List Bool)) ∧
    (intended Bool (Bool × List Bool)).interp (fun v s => ((v, [true]), s))
      (put true (ret false) : Prog Bool Bool) false = ((false, [true]), true) :=
  ⟨intended_lawful, rfl⟩

/-! ## Dropping one law -/

/-- Dropping get–get changes no derivability: from get–put, put–get and
put–put exactly the same equations between programs are derivable as from all
four laws. -/
theorem derivable_lawsExcept_getGet_iff {S V : Type} (p q : Prog S V) :
    Derivable (lawsExcept .getGet) p q ↔ Derivable allLaws p q := by
  constructor
  · exact Derivable.mono (fun _ _ => trivial)
  · intro h
    induction h with
    | refl p => exact .refl p
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | get_congr _ ih => exact .get_congr ih
    | put_congr s _ ih => exact .put_congr s ih
    | getGet _ k => exact Derivable.getGet_of (by decide) (by decide) k
    | getPut _ p => exact .getPut (by decide) p
    | putGet _ s k => exact .putGet (by decide) s k
    | putPut _ s s' p => exact .putPut (by decide) s s' p

/-- Get–get is not derivable from get–put and put–put: on a Boolean cell the
get–get instance `get (fun s => get (fun s' => ret s')) = get (fun s => ret s)`
is not derivable from the law set `{get–put, put–put}`, although its two sides
are observationally equivalent. -/
theorem getGet_not_derivable_from_getPut_putPut :
    ObsEq (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) ∧
    ¬ Derivable (fun l => l = .getPut ∨ l = .putPut)
      (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) := by
  refine ⟨rfl, fun h => ?_⟩
  have hsat : SatisfiesAll (fun l => l = .getPut ∨ l = .putPut) (readToClear Bool Bool false) := by
    intro l hl
    rcases hl with rfl | rfl
    · exact readToClear_getPut false
    · exact readToClear_putPut false
  have := congrFun (h.sound (readToClear Bool Bool false) hsat intendedRet) true
  exact absurd this (by decide)

/-- Get–get is not derivable from put–get and put–put: on a Boolean cell the
same get–get instance is not derivable from the law set `{put–get, put–put}`. -/
theorem getGet_not_derivable_from_putGet_putPut :
    ObsEq (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) ∧
    ¬ Derivable (fun l => l = .putGet ∨ l = .putPut)
      (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) := by
  refine ⟨rfl, fun h => ?_⟩
  have hsat : SatisfiesAll (fun l => l = .putGet ∨ l = .putPut) (faultingCounter Bool Bool) := by
    intro l hl
    rcases hl with rfl | rfl
    · exact faultingCounter_putGet
    · exact faultingCounter_putPut
  have := congrFun (h.sound (faultingCounter Bool Bool) hsat faultingRet) false
  exact absurd this (by decide)

/-- Dropping get–put loses an equation between observationally equivalent
programs: from put–get, put–put and get–get, `ret true` is not derivably equal
to its canonical program `get (fun s => put s (ret true))` (Boolean cell). -/
theorem dropGetPut_loses_nf :
    lawsExcept .getPut .putGet ∧ lawsExcept .getPut .putPut ∧
    ObsEq (ret true : Prog Bool Bool) (nf (run (ret true))) ∧
    ¬ Derivable (lawsExcept .getPut) (ret true : Prog Bool Bool) (nf (run (ret true))) := by
  refine ⟨by decide, by decide, rfl, fun h => ?_⟩
  have hsat : SatisfiesAll (lawsExcept .getPut) (dirtyBit Bool Bool) := by
    intro l hl
    cases l with
    | getGet => exact dirtyBit_getGet
    | getPut => exact absurd rfl hl
    | putGet => exact dirtyBit_putGet
    | putPut => exact dirtyBit_putPut
  have := congrFun (h.sound (dirtyBit Bool Bool) hsat pairRet) (false, false)
  exact absurd this (by decide)

/-- Dropping put–get loses an equation between observationally equivalent
programs: from get–put, put–put and get–get, `put true (get ret)` is not
derivably equal to its canonical program (Boolean cell). -/
theorem dropPutGet_loses_nf :
    lawsExcept .putGet .getPut ∧ lawsExcept .putGet .putPut ∧
    ObsEq (put true (get ret) : Prog Bool Bool) (nf (run (put true (get ret)))) ∧
    ¬ Derivable (lawsExcept .putGet) (put true (get ret) : Prog Bool Bool)
      (nf (run (put true (get ret)))) := by
  refine ⟨by decide, by decide, rfl, fun h => ?_⟩
  have hsat : SatisfiesAll (lawsExcept .putGet) (writesIgnored Bool Bool) := by
    intro l hl
    cases l with
    | getGet => exact writesIgnored_getGet
    | getPut => exact writesIgnored_getPut
    | putGet => exact absurd rfl hl
    | putPut => exact writesIgnored_putPut
  have := congrFun (h.sound (writesIgnored Bool Bool) hsat intendedRet) false
  exact absurd this (by decide)

/-- Dropping put–put loses an equation between observationally equivalent
programs: from get–get, get–put and put–get, `put true (put false (ret true))`
is not derivably equal to its canonical program (Boolean cell). -/
theorem dropPutPut_loses_nf :
    lawsExcept .putPut .getPut ∧ lawsExcept .putPut .putGet ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool)
      (nf (run (put true (put false (ret true))))) ∧
    ¬ Derivable (lawsExcept .putPut) (put true (put false (ret true)) : Prog Bool Bool)
      (nf (run (put true (put false (ret true))))) := by
  refine ⟨by decide, by decide, rfl, fun h => ?_⟩
  have hsat : SatisfiesAll (lawsExcept .putPut) (changeLog Bool Bool) := by
    intro l hl
    cases l with
    | getGet => exact changeLog_getGet
    | getPut => exact changeLog_getPut
    | putGet => exact changeLog_putGet
    | putPut => exact absurd rfl hl
  have := congrFun (h.sound (changeLog Bool Bool) hsat logRet) false
  exact absurd this (by decide)

end Toy.StoreLaws
