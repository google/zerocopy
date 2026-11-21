import ToyUnify.Orphan

/-!
# Overlap checking without the occurs check

The occurs-check-free checker `overlapCheckSaysDisjointNoOC` uses `unifyNoOC` in place of
`unify`. For the algorithm as defined (the same passes and fuel, only the occurs check removed):

* it can report overlap for headers with no common finite instance
  (`noOC_check_reports_false_overlap`);
* it never reports "disjoint" for headers that overlap, provided the self types are renamed
  apart (`not_headersOverlap_of_overlapCheckSaysDisjointNoOC`); more generally, any verdict
  computed from the unifier output that is sound with `unify` remains sound with `unifyNoOC`
  (`noOC_verdict_sound_of_unify_verdict_sound`, pointwise, and
  `noOC_verdict_sound_of_unify_verdict_sound_uniform`, for all inputs);
* the fuel bound matters: on some renamed-apart pairs the occurs-check-free run never finishes,
  and `unifyNoOC` returns `none` only because the fuel runs out (`unifyNoOC_outOfFuel_example`).
-/

namespace Toy.Unify

/-- The occurs-check-free checker's verdict "disjoint": traits differ or `unifyNoOC` fails. -/
def overlapCheckSaysDisjointNoOC (i j : Impl) : Bool :=
  i.trait != j.trait || (unifyNoOC i.selfTy j.selfTy).isNone

theorem overlapCheckSaysDisjointNoOC_example :
    overlapCheckSaysDisjointNoOC ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by decide
theorem overlapCheckSaysDisjointNoOC_false_example :
    overlapCheckSaysDisjointNoOC i1 i2 = false := by decide

/-- `impl<T> Tr for (T, T)`. -/
def iPairSame : Impl := ⟨10, pair (.var 0) (.var 0), []⟩
/-- `impl<U> Tr for (U, Box<U>)`. -/
def iPairBox : Impl := ⟨10, pair (.var 1) (box (.var 1)), []⟩

/-- False overlap: `impl<T> Tr for (T, T)` and `impl<U> Tr for (U, Box<U>)` (renamed apart) have
no common ground instance (it would need `t = Box t`); the checker with the occurs check says
disjoint, the checker without it says they may overlap. -/
theorem noOC_check_reports_false_overlap :
    VarsDisjoint iPairSame.selfTy iPairBox.selfTy ∧ ¬ HeadersOverlap iPairSame iPairBox ∧
      overlapCheckSaysDisjoint iPairSame iPairBox = true ∧
      overlapCheckSaysDisjointNoOC iPairSame iPairBox = false := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  rintro ⟨_, θ₁, θ₂, _, h⟩
  simp only [iPairSame, iPairBox, pair, box, subst_con, List.map_cons, List.map_nil,
    Term.con.injEq, List.cons.injEq, true_and, and_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact ne_box_self _ (by simpa [box] using h2)

/-- No false disjointness: for self types renamed apart, if the occurs-check-free checker says
disjoint, the headers have no common ground instance. -/
theorem not_headersOverlap_of_overlapCheckSaysDisjointNoOC {i j : Impl}
    (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjointNoOC i j = true) :
    ¬ HeadersOverlap i j := by
  apply not_headersOverlap_of_overlapCheckSaysDisjoint hdisj
  unfold overlapCheckSaysDisjointNoOC at h
  unfold overlapCheckSaysDisjoint
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hu : unify i.selfTy j.selfTy with
    | none => rfl
    | some σ =>
      rw [unifyNoOC_eq_some_of_unify_eq_some hu] at h
      cases h

/-- Transfer for arbitrary checkers, at one input pair `(s, t)`: let `chk` be any verdict computed
from a unifier output (`true` meaning "disjoint") and `P` any overlap notion that implies
`Unifiable s t`. If `chk` fed `unify s t` says "disjoint" only when `¬ P`, and `chk` fed
`unifyNoOC s t` says "disjoint", then `¬ P`. -/
theorem noOC_verdict_sound_of_unify_verdict_sound {s t : Term} (chk : Option Subst → Bool)
    (P : Prop) (hP : P → Unifiable s t) (hchk : chk (unify s t) = true → ¬ P)
    (h : chk (unifyNoOC s t) = true) : ¬ P := by
  intro hp
  obtain ⟨τ, hτ⟩ := hP hp
  obtain ⟨σ, hσ⟩ := unify_complete hτ
  rw [unifyNoOC_eq_some_of_unify_eq_some hσ] at h
  exact hchk (by rw [hσ]; exact h) hp

/-- Uniform transfer: if a checker `chk` is sound for an overlap relation `P` (implying
unifiability) on every input when fed `unify`, it is sound on every input when fed `unifyNoOC`. -/
theorem noOC_verdict_sound_of_unify_verdict_sound_uniform (chk : Option Subst → Bool)
    (P : Term → Term → Prop) (hP : ∀ s t, P s t → Unifiable s t)
    (hchk : ∀ s t, chk (unify s t) = true → ¬ P s t) :
    ∀ s t, chk (unifyNoOC s t) = true → ¬ P s t :=
  fun s t h => noOC_verdict_sound_of_unify_verdict_sound chk (P s t) (hP s t) (hchk s t) h

/-- Non-vacuity for the uniform transfer: `chk := Option.isNone` and `P := Unifiable` satisfy
both hypotheses (the second is the soundness of `unify`'s failure, `unify_eq_none_iff`). The
checker fed `unifyNoOC` fires on `u8 =? u32`, so the antecedent `chk (unifyNoOC s t) = true` of
the conclusion is satisfiable; it does not fire on `X =? Vec Y` or on `X =? Box X`, where
`unifyNoOC` returns a substitution. -/
theorem noOC_verdict_sound_of_unify_verdict_sound_uniform_nonvacuous :
    (∀ s t, Unifiable s t → Unifiable s t) ∧
      (∀ s t, (unify s t).isNone = true → ¬ Unifiable s t) ∧
      (unifyNoOC u8 u32).isNone = true ∧
      (unifyNoOC (.var 0) (vec (.var 1))).isNone = false ∧
      (unifyNoOC (.var 0) (box (.var 0))).isNone = false := by
  refine ⟨fun _ _ h => h, fun s t h => ?_, by decide, by decide, by decide⟩
  rw [← unify_eq_none_iff]
  simpa using h

/-! ## Non-vacuity and positive controls -/

/-- Hypotheses of `not_headersOverlap_of_overlapCheckSaysDisjointNoOC` hold for
`impl<T> Tr for Vec<T>` and `impl<U> Tr for Box<U>`. -/
theorem not_headersOverlap_of_overlapCheckSaysDisjointNoOC_nonvacuous :
    VarsDisjoint (vec (.var 0)) (box (.var 1)) ∧
      overlapCheckSaysDisjointNoOC ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ = true := by
  decide

/-- Positive control (renaming apart dropped): with a shared variable name, the
occurs-check-free checker says disjoint although the headers overlap. -/
theorem noOC_check_false_disjoint_without_renaming :
    ¬ VarsDisjoint iShared1.selfTy iShared2.selfTy ∧
      overlapCheckSaysDisjointNoOC iShared1 iShared2 = true ∧ HeadersOverlap iShared1 iShared2 :=
  ⟨by decide, by decide, overlapCheck_needs_renaming_apart.2.2.1⟩

/-- Without `h`: `impl<T: A> Tr for T` and `impl<U: B> Tr for U` (renamed apart) overlap as
headers and the occurs-check-free checker does not say disjoint. -/
theorem noOC_disjoint_needs_verdict :
    VarsDisjoint i1.selfTy i2.selfTy ∧ overlapCheckSaysDisjointNoOC i1 i2 = false ∧
      HeadersOverlap i1 i2 :=
  ⟨by decide, by decide, headersOverlap_example⟩

/-- All three hypotheses of `noOC_verdict_sound_of_unify_verdict_sound` hold together for the
self-type check `chk := Option.isNone` on `Vec<T>` and `Box<U>` with `P` the header overlap
(including `h`: the occurs-check-free checker says disjoint). In every instance satisfying all
hypotheses `P` is false, since that is the theorem's conclusion. -/
theorem noOC_verdict_sound_of_unify_verdict_sound_nonvacuous :
    (HeadersOverlap ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩ →
        Unifiable (vec (.var 0)) (box (.var 1))) ∧
      ((unify (vec (.var 0)) (box (.var 1))).isNone = true →
        ¬ HeadersOverlap ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩) ∧
      (unifyNoOC (vec (.var 0)) (box (.var 1))).isNone = true := by
  refine ⟨fun h => ?_, fun _ => ?_, by decide⟩
  · exfalso
    obtain ⟨_, θ₁, θ₂, _, h⟩ := h
    simp [vec, box, subst_con] at h
  · rintro ⟨_, θ₁, θ₂, _, h⟩
    simp [vec, box, subst_con] at h

/-- Without `h` (instance: `chk := Option.isNone`, `P := Unifiable`, one variable against one
nullary constructor): `hP` and `hchk` hold, the occurs-check-free checker does not say disjoint
on `X =? u8`, and `P` holds. -/
theorem noOC_verdict_transfer_needs_noOC_verdict :
    (Unifiable (.var 0) u8 → Unifiable (.var 0) u8) ∧
      ((unify (.var 0) u8).isNone = true → ¬ Unifiable (.var 0) u8) ∧
      (unifyNoOC (.var 0) u8).isNone = false ∧ Unifiable (.var 0) u8 :=
  ⟨id, fun h => absurd h (by decide), by decide, ⟨[(0, u8)], by decide⟩⟩

/-- Positive control for the pointwise transfer `noOC_verdict_sound_of_unify_verdict_sound`
(`hP` dropped; instance: `P := True`, `chk := Option.isSome`, the pair `(T, T) =? (U, Box U)`):
`chk` is vacuously sound for `unify` on this pair, fires on `unifyNoOC`, and `P` holds. For the
uniform transfer see `noOC_verdict_transfer_uniform_needs_hP`. -/
theorem noOC_verdict_transfer_needs_hP :
    ¬ (True → Unifiable iPairSame.selfTy iPairBox.selfTy) ∧
      ((unify iPairSame.selfTy iPairBox.selfTy).isSome = true → ¬ True) ∧
      (unifyNoOC iPairSame.selfTy iPairBox.selfTy).isSome = true ∧ True := by
  refine ⟨fun h => ?_, by decide, by decide, trivial⟩
  obtain ⟨τ, hτ⟩ := h trivial
  simp only [Unifies, iPairSame, iPairBox, pair, box, subst_con, List.map_cons, List.map_nil,
    Term.con.injEq, List.cons.injEq, true_and, and_true] at hτ
  obtain ⟨h1, h2⟩ := hτ
  rw [h1] at h2
  exact absurd (by simpa [box] using h2) (ne_box_self _)

/-- Positive control for the pointwise transfer `noOC_verdict_sound_of_unify_verdict_sound`
(`hchk` dropped; instance: the constant verdict `true`, `P := Unifiable`, one variable against one
nullary constructor): `hP` and `h` hold, `hchk` fails, and `P` holds. For the uniform transfer see
`noOC_verdict_transfer_uniform_needs_hchk`. -/
theorem noOC_verdict_transfer_needs_hchk :
    (Unifiable (.var 0) u8 → Unifiable (.var 0) u8) ∧
      ¬ ((fun _ : Option Subst => true) (unify (.var 0) u8) = true → ¬ Unifiable (.var 0) u8) ∧
      (fun _ : Option Subst => true) (unifyNoOC (.var 0) u8) = true ∧ Unifiable (.var 0) u8 :=
  ⟨id, fun h => h rfl ⟨[(0, u8)], by decide⟩, rfl, ⟨[(0, u8)], by decide⟩⟩

/-- Positive control for the uniform transfer `noOC_verdict_sound_of_unify_verdict_sound_uniform`
(`hP` dropped; instance: `chk := Option.isSome` and `P s t := ¬ Unifiable s t`): `hchk` holds on
every input (by soundness of `unify`), `hP` fails (at `u8 =? u32`), and the conclusion fails at
`X =? Box X`, where `unifyNoOC` returns a substitution although the pair has no unifier. -/
theorem noOC_verdict_transfer_uniform_needs_hP :
    ¬ (∀ s t, ¬ Unifiable s t → Unifiable s t) ∧
      (∀ s t, (unify s t).isSome = true → ¬ ¬ Unifiable s t) ∧
      ¬ (∀ s t, (unifyNoOC s t).isSome = true → ¬ ¬ Unifiable s t) ∧
      (unifyNoOC (.var 0) (box (.var 0))).isSome = true ∧
      ¬ Unifiable (.var 0) (box (.var 0)) := by
  refine ⟨fun h => not_unifiable_u8_u32 (h u8 u32 not_unifiable_u8_u32), fun s t hsome hnu => ?_,
    fun h => h (.var 0) (box (.var 0)) (by decide) not_unifiable_var_box, by decide,
    not_unifiable_var_box⟩
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hsome
  exact hnu ⟨σ, unify_sound hσ⟩

/-- Positive control for the uniform transfer `noOC_verdict_sound_of_unify_verdict_sound_uniform`
(`hchk` dropped; instance: the constant verdict `true` and `P := Unifiable`): `hP` holds on every
input, `hchk` fails at `X =? u8`, and the conclusion fails at `X =? u8`. -/
theorem noOC_verdict_transfer_uniform_needs_hchk :
    (∀ s t, Unifiable s t → Unifiable s t) ∧
      ¬ (∀ s t, (fun _ : Option Subst => true) (unify s t) = true → ¬ Unifiable s t) ∧
      ¬ (∀ s t, (fun _ : Option Subst => true) (unifyNoOC s t) = true → ¬ Unifiable s t) :=
  ⟨fun _ _ h => h, fun h => h (.var 0) u8 rfl ⟨[(0, u8)], by decide⟩,
    fun h => h (.var 0) u8 rfl ⟨[(0, u8)], by decide⟩⟩

/-! ## The fuel bound hides non-termination -/

/-- `(T, (T, T))`. -/
def loopS : Term := pair (.var 0) (pair (.var 0) (.var 0))
/-- `(U, ((U, U), (U, U)))`, renamed apart from `loopS`. -/
def loopT : Term := pair (.var 1) (pair (pair (.var 1) (.var 1)) (pair (.var 1) (.var 1)))
/-- The pending equation `(U, U) =? ((U, U), (U, U))`, reached after two passes. -/
def loopEqs : List (Term × Term) :=
  [(pair (.var 1) (.var 1), pair (pair (.var 1) (.var 1)) (pair (.var 1) (.var 1)))]

theorem run_false_loopEqs : ∀ (fuel : Nat) (σ : Subst), run false fuel loopEqs σ = .outOfFuel
  | 0, σ => by
    obtain ⟨σ', h⟩ : ∃ σ', step false loopEqs σ = .next loopEqs σ' := ⟨_, rfl⟩
    unfold run; rw [h]
  | n + 1, σ => by
    obtain ⟨σ', h⟩ : ∃ σ', step false loopEqs σ = .next loopEqs σ' := ⟨_, rfl⟩
    unfold run; rw [h]
    exact run_false_loopEqs n σ'

/-- Without the occurs check, the run on the renamed-apart pair `(T, (T, T)) =? (U, ((U, U),
(U, U)))` runs out of fuel for every fuel: after two passes the pending equations repeat
forever, so an implementation without the fuel bound would not terminate. With the fuel bound,
`unifyNoOC` returns `none`, and the occurs-check-free checker says "disjoint" — correctly, since
the pair has no unifier — only because the fuel ran out. -/
theorem unifyNoOC_outOfFuel_example :
    VarsDisjoint loopS loopT ∧ ¬ Unifiable loopS loopT ∧
      (∀ fuel, run false fuel [(loopS, loopT)] [] = .outOfFuel) ∧ unifyNoOC loopS loopT = none ∧
      overlapCheckSaysDisjointNoOC ⟨10, loopS, []⟩ ⟨10, loopT, []⟩ = true := by
  refine ⟨by decide, ?_, ?_, by decide, by decide⟩
  · rw [← unify_eq_none_iff]
    decide
  · intro fuel
    obtain ⟨e1, σ1, h1⟩ : ∃ e1 σ1, step false [(loopS, loopT)] [] = .next e1 σ1 ∧
        ∃ σ2, step false e1 σ1 = .next loopEqs σ2 := ⟨_, _, rfl, _, rfl⟩
    obtain ⟨h1, σ2, h2⟩ := h1
    match fuel with
    | 0 => unfold run; rw [h1]
    | 1 => unfold run; rw [h1]; simp only; unfold run; rw [h2]
    | n + 2 =>
      unfold run; rw [h1]; simp only; unfold run; rw [h2]; simp only
      exact run_false_loopEqs n σ2

end Toy.Unify
