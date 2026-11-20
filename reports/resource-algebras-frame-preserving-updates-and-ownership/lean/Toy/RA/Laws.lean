import Toy.RA.Core
import Toy.RA.Excl
import Toy.RA.Agree
import Toy.RA.Auth

/-!
# Algebraic Laws of Frame-Preserving Updates and Tightness Counterexamples

Catalogs the discrete RA laws (`OpAssoc`, `OpComm`, `ValidOpL`,
`IsRightUnit`, `HasRightIdOnValid`, `HasLocalRightUnits`) used and sufficient
(with each hypothesis irredundant / tight) for each general
right-frame-preserving update theorem:
- Right-framing (`fpUpdate_frame_right`): `OpAssoc` only.
- Parallel update composition (`fpUpdate_op`, `fpUpdateP_op`): `OpAssoc` and
  `OpComm`.
- Resource dropping / weakening (`fpUpdate_drop_right`): `OpAssoc`, `OpComm`,
  and `ValidOpL`.
- Equivalence between optional-frame `fpUpdate` and bare `fpUpdateBare`:
  `IsRightUnit` alone, OR `HasRightIdOnValid` together with `ValidOpL`.

Also records boundary theorems clarifying:
- Left-frame breakage when `OpComm` is absent (`pathCat_fpUpdate_breaks_left_frame`,
  `auth_pathCat_localUpdate_breaks_left_frame`) and simultaneous two-sided frame
  breakage under `OpComm` without `OpAssoc` (`opComm_alone_not_two_sided`,
  `auth_opComm_alone_not_two_sided`, vs. `fpUpdate2_of_assoc_comm`);
- Tightness vs. global necessity (`validOpL_of_fpUpdate_drop_right_all`,
  `drop_right_holds_without_opComm_example`, `drop_right_holds_without_opAssoc_example`,
  `frame_right_holds_without_opAssoc_example`);
- Separation between `HasRightIdOnValid` and `HasLocalRightUnits` (`rightIdOnValidOnlyRA`);
- Sufficiency of idempotence + `OpComm` without `ValidOpL` (`fpUpdate_iff_bare_of_idemp_opComm`),
  together with 2-element `ValidOpL` tightness witnesses
  (`idempotent_noncomm_validOpL_witness`, `two_element_comm_validOpL_witness`).
-/

namespace Toy.RA

/-! ## Counterexample Algebras for Dropping Individual RA Laws -/

/-- A 4-element commutative, `ValidOpL`-satisfying, non-associative raw algebra
(`e3` is the unique absorbing invalid element). Breaks right-framing
(`e0 ⤳ e1` holds, `e0 · e1 ⤳ e1 · e1` fails at frame `e2`), parallel update
composition, and resource dropping (`e2 · e0 ⤳ e2` fails at frame `e2`). -/
def nonAssocCommValidRA : RawRA Four where
  op
    | .e0, .e0 => .e0 | .e0, .e1 => .e0 | .e0, .e2 => .e0 | .e0, .e3 => .e3
    | .e1, .e0 => .e0 | .e1, .e1 => .e2 | .e1, .e2 => .e2 | .e1, .e3 => .e3
    | .e2, .e0 => .e0 | .e2, .e1 => .e2 | .e2, .e2 => .e3 | .e2, .e3 => .e3
    | .e3, _ => .e3
  valid x := x ≠ .e3

theorem nonAssocCommValidRA_opComm : OpComm nonAssocCommValidRA := by
  intro x y
  cases x <;> cases y <;> rfl

theorem nonAssocCommValidRA_validOpL : ValidOpL nonAssocCommValidRA := by
  intro x y hxy
  cases x <;> cases y <;> simp [nonAssocCommValidRA] at hxy ⊢

theorem nonAssocCommValidRA_not_opAssoc : ¬ OpAssoc nonAssocCommValidRA := by
  intro h
  have h0 := h .e1 .e1 .e2
  cases h0

theorem nonAssocCommValidRA_upd_0_1 : fpUpdate nonAssocCommValidRA .e0 .e1 := by
  intro mf hmf
  cases mf with
  | none => intro h; cases h
  | some f =>
    cases f <;> simp [opOpt, nonAssocCommValidRA] at hmf ⊢

/-- A 5-element associative, `ValidOpL`-satisfying, non-commutative raw algebra:
partial composition of arrows in the indiscrete 2-object category (`Bool × Bool`)
adjoined with an absorbing invalid element `none`.
- Breaks left-framing / parallel update composition: `(true, false)` composes
  validly with `(false, true)` but not `(true, true)`, even though
  `(false, true) ⤳ (true, true)` holds.
- Breaks resource dropping: `(false, true) · (true, false) · (false, true)` is
  valid while `(false, true) · (false, true)` is invalid. -/
def pathCatRA : RawRA (Option (Bool × Bool)) where
  op x y :=
    match x, y with
    | some (s₁, t₁), some (s₂, t₂) => if t₁ = s₂ then some (s₁, t₂) else none
    | _, _ => none
  valid x := x.isSome = true

theorem pathCatRA_opAssoc : OpAssoc pathCatRA := by
  intro x y z
  cases x with
  | none => rfl
  | some p =>
    cases y with
    | none => rfl
    | some q =>
      cases z with
      | none =>
        rcases p with ⟨s₁, t₁⟩
        rcases q with ⟨s₂, t₂⟩
        cases s₁ <;> cases t₁ <;> cases s₂ <;> cases t₂ <;> rfl
      | some r =>
        rcases p with ⟨s₁, t₁⟩
        rcases q with ⟨s₂, t₂⟩
        rcases r with ⟨s₃, t₃⟩
        cases s₁ <;> cases t₁ <;> cases s₂ <;> cases t₂ <;> cases s₃ <;> cases t₃ <;> rfl

theorem pathCatRA_validOpL : ValidOpL pathCatRA := by
  intro x y hxy
  cases x with
  | none => simp [pathCatRA] at hxy
  | some _ => rfl

theorem pathCatRA_not_opComm : ¬ OpComm pathCatRA := by
  intro h
  have h0 := h (some (true, false)) (some (false, true))
  simp [pathCatRA] at h0

theorem pathCatRA_upd_01_11 :
    fpUpdate pathCatRA (some (false, true)) (some (true, true)) := by
  intro mf hmf
  cases mf with
  | none => rfl
  | some f =>
    cases f with
    | none => simp [opOpt, pathCatRA] at hmf
    | some p =>
      rcases p with ⟨s, t⟩
      cases s <;> cases t <;> simp [opOpt, pathCatRA] at hmf ⊢

theorem xorValidFalseRA_opAssoc : OpAssoc xorValidFalseRA := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

theorem xorValidFalseRA_opComm : OpComm xorValidFalseRA := by
  intro x y
  cases x <;> cases y <;> rfl

/-- Five-element carrier for a commutative, associative semigroup with local
right units on every element (`HasLocalRightUnits`) that fails `ValidOpL` and
breaks `fpUpdateBare → fpUpdate` (nothing is claimed about smaller witnesses;
under `HasRightIdOnValid` alone, a 2-element commutative associative witness
exists: `two_element_comm_validOpL_witness`). -/
inductive Five where
  | z0 | z1 | z2 | z3 | z4
  deriving DecidableEq, Repr

/-- Five-element commutative, associative raw algebra where every element
admits a right identity (`z0·z0=z0`, `z1·z4=z1`, `z2·z2=z2`, `z3·z3=z3`,
`z4·z4=z4`), validity holds solely on `{z1, z2}`, `ValidOpL` fails (`z3·z4 = z2`
is valid while `z3` is invalid), and `fpUpdateBare z1 z3` holds (the only
valid right frame of `z1` is `z4`, and `z3·z4 = z2` is valid) while
`fpUpdate z1 z3` fails at `mf = none`. -/
def fiveLocalUnitsNoValidOpLRA : RawRA Five where
  op
    | .z0, _   => .z0 | _,   .z0 => .z0
    | .z1, .z1 => .z0 | .z1, .z2 => .z0 | .z1, .z3 => .z0 | .z1, .z4 => .z1
    | .z2, .z1 => .z0 | .z2, .z2 => .z2 | .z2, .z3 => .z2 | .z2, .z4 => .z2
    | .z3, .z1 => .z0 | .z3, .z2 => .z2 | .z3, .z3 => .z3 | .z3, .z4 => .z2
    | .z4, .z1 => .z1 | .z4, .z2 => .z2 | .z4, .z3 => .z2 | .z4, .z4 => .z4
  valid x := x = .z1 ∨ x = .z2

theorem fiveLocalUnitsNoValidOpLRA_opAssoc : OpAssoc fiveLocalUnitsNoValidOpLRA := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl

theorem fiveLocalUnitsNoValidOpLRA_opComm : OpComm fiveLocalUnitsNoValidOpLRA := by
  intro x y
  cases x <;> cases y <;> rfl

theorem fiveLocalUnitsNoValidOpLRA_hasLocalRightUnits :
    HasLocalRightUnits fiveLocalUnitsNoValidOpLRA := by
  intro x
  cases x with
  | z0 => exact ⟨.z0, rfl⟩
  | z1 => exact ⟨.z4, rfl⟩
  | z2 => exact ⟨.z2, rfl⟩
  | z3 => exact ⟨.z3, rfl⟩
  | z4 => exact ⟨.z4, rfl⟩

theorem fiveLocalUnitsNoValidOpLRA_hasRightIdOnValid :
    HasRightIdOnValid fiveLocalUnitsNoValidOpLRA :=
  hasRightIdOnValid_of_hasLocalRightUnits fiveLocalUnitsNoValidOpLRA_hasLocalRightUnits

theorem fiveLocalUnitsNoValidOpLRA_not_validOpL : ¬ ValidOpL fiveLocalUnitsNoValidOpLRA := by
  intro h
  have h3 := h .z3 .z4 (Or.inr rfl)
  rcases h3 with h1 | h1 <;> cases h1

/-- Direct counterexample showing `HasLocalRightUnits` alone (even with `OpAssoc`
and `OpComm`) does not make `fpUpdate` coincide with `fpUpdateBare`. -/
theorem localRightUnits_alone_not_iff_bare :
    HasLocalRightUnits fiveLocalUnitsNoValidOpLRA ∧
    OpAssoc fiveLocalUnitsNoValidOpLRA ∧
    OpComm fiveLocalUnitsNoValidOpLRA ∧
    ¬ (∀ x y : Five,
        fpUpdate fiveLocalUnitsNoValidOpLRA x y ↔ fpUpdateBare fiveLocalUnitsNoValidOpLRA x y) := by
  refine ⟨fiveLocalUnitsNoValidOpLRA_hasLocalRightUnits,
          fiveLocalUnitsNoValidOpLRA_opAssoc, fiveLocalUnitsNoValidOpLRA_opComm, ?_⟩
  intro h
  have hbare : fpUpdateBare fiveLocalUnitsNoValidOpLRA .z1 .z3 := by
    intro f hf
    cases f <;> simp [fiveLocalUnitsNoValidOpLRA] at hf ⊢
  have hupd := (h .z1 .z3).mpr hbare none (Or.inl rfl)
  rcases hupd with h1 | h1 <;> cases h1

/-- Three-element carrier separating `HasRightIdOnValid` from `HasLocalRightUnits`. -/
inductive ThreeRightIdValid where
  | e | z | w
  deriving DecidableEq, Repr

/-- Three-element commutative, associative, `ValidOpL`-satisfying algebra where
only `.e` is valid (`.e · .e = .e`, all other products `.w`), so valid elements
have a right identity (`HasRightIdOnValid`) while invalid element `.z` has none
(`¬ HasLocalRightUnits`). -/
def rightIdOnValidOnlyRA : RawRA ThreeRightIdValid where
  op
    | .e, .e => .e
    | _, _   => .w
  valid x := x = .e

theorem rightIdOnValidOnlyRA_props :
    OpAssoc rightIdOnValidOnlyRA ∧ OpComm rightIdOnValidOnlyRA ∧
    ValidOpL rightIdOnValidOnlyRA ∧ HasRightIdOnValid rightIdOnValidOnlyRA ∧
    ¬ HasLocalRightUnits rightIdOnValidOnlyRA := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y u
    cases x <;> cases y <;> cases u <;> rfl
  · intro x y
    cases x <;> cases y <;> rfl
  · intro x y h
    cases x <;> cases y <;> first | rfl | cases h
  · intro x hx
    cases hx
    exact ⟨.e, rfl⟩
  · intro h
    rcases h .z with ⟨c, hc⟩
    cases c <;> cases hc

/-! ## Left-Frame Breakage Without `OpComm` (Boundary Examples) -/

/-- In the associative, `ValidOpL`-satisfying, non-commutative algebra `pathCatRA`,
`(false, true) ⤳ (true, true)` preserves all right-composed frames, yet the
left-composed frame `(true, false)` is compatible with `(false, true)` and
incompatible with `(true, true)`. -/
theorem pathCat_fpUpdate_breaks_left_frame :
    OpAssoc pathCatRA ∧ ValidOpL pathCatRA ∧ ¬ OpComm pathCatRA ∧
    fpUpdate pathCatRA (some (false, true)) (some (true, true)) ∧
    pathCatRA.valid (pathCatRA.op (some (true, false)) (some (false, true))) ∧
    ¬ pathCatRA.valid (pathCatRA.op (some (true, false)) (some (true, true))) := by
  refine ⟨pathCatRA_opAssoc, pathCatRA_validOpL, pathCatRA_not_opComm,
          pathCatRA_upd_01_11, rfl, ?_⟩
  simp [pathCatRA]

/-- In `authRA pathCatRA`, `(ff, ff) → (tf, tf)` is a valid `LocalUpdate` over
associative `pathCatRA` and lifts to a right-frame `fpUpdate`, yet a fragment
frame `frag ff` composed on the left is compatible with `auth ff · frag ff` and
incompatible with `auth tf · frag tf`. Shows that without `OpComm`, `fpUpdate` in
`auth_localUpdate_fpUpdate` protects right-composed frames only. -/
theorem auth_pathCat_localUpdate_breaks_left_frame :
    OpAssoc pathCatRA ∧ ValidOpL pathCatRA ∧ ¬ OpComm pathCatRA ∧
    LocalUpdate pathCatRA (some (false, false)) (some (false, false))
      (some (true, false)) (some (true, false)) ∧
    fpUpdate (authRA pathCatRA)
      ((authRA pathCatRA).op (authElem (some (false, false))) (fragElem (some (false, false))))
      ((authRA pathCatRA).op (authElem (some (true, false))) (fragElem (some (true, false)))) ∧
    (authRA pathCatRA).valid
      ((authRA pathCatRA).op (fragElem (some (false, false)))
        ((authRA pathCatRA).op (authElem (some (false, false))) (fragElem (some (false, false))))) ∧
    ¬ (authRA pathCatRA).valid
      ((authRA pathCatRA).op (fragElem (some (false, false)))
        ((authRA pathCatRA).op (authElem (some (true, false))) (fragElem (some (true, false))))) ∧
    ¬ fpUpdate (authRA pathCatRA)
      ((authRA pathCatRA).op (fragElem (some (false, false)))
        ((authRA pathCatRA).op (authElem (some (false, false))) (fragElem (some (false, false)))))
      ((authRA pathCatRA).op (fragElem (some (false, false)))
        ((authRA pathCatRA).op (authElem (some (true, false))) (fragElem (some (true, false))))) := by
  have hloc : LocalUpdate pathCatRA (some (false, false)) (some (false, false))
      (some (true, false)) (some (true, false)) := by
    intro mz _ h
    refine ⟨rfl, ?_⟩
    cases mz with
    | none => rfl
    | some z =>
      rcases z with _ | ⟨s, t⟩
      · simp [opOpt, pathCatRA] at h
      · cases s <;> cases t <;> simp [opOpt, pathCatRA] at h ⊢
  have hrfp : fpUpdate (authRA pathCatRA)
      ((authRA pathCatRA).op (authElem (some (false, false))) (fragElem (some (false, false))))
      ((authRA pathCatRA).op (authElem (some (true, false))) (fragElem (some (true, false)))) := by
    intro mf hmf
    rcases mf with _ | ⟨pf, mbf⟩
    · exact ⟨rfl, none, rfl⟩
    · cases pf with
      | excl _ => exact False.elim hmf
      | conflict => exact False.elim hmf
      | none =>
        rcases mbf with _ | bf
        · exact ⟨rfl, none, rfl⟩
        · rcases hmf with ⟨_, mc, hmc⟩
          rcases bf with _ | ⟨s, t⟩
          · rcases mc with _ | c
            · simp [opOpt, pathCatRA] at hmc
            · rcases c with _ | ⟨s', t'⟩ <;> simp [opOpt, pathCatRA] at hmc
          · rcases mc with _ | c
            · cases s <;> cases t <;> simp [opOpt, pathCatRA] at hmc ⊢ <;>
                exact ⟨rfl, none, rfl⟩
            · rcases c with _ | ⟨s', t'⟩
              · cases s <;> cases t <;> simp [opOpt, pathCatRA] at hmc
              · cases s <;> cases t <;> cases s' <;> cases t' <;>
                  simp [opOpt, pathCatRA] at hmc ⊢ <;>
                  first
                    | exact ⟨rfl, none, rfl⟩
                    | exact ⟨rfl, some (some (s', t')), rfl⟩
                    | exact ⟨rfl, some (some (true, false)), rfl⟩
                    | exact ⟨rfl, some (some (false, false)), rfl⟩
  have hv : (authRA pathCatRA).valid
      ((authRA pathCatRA).op (fragElem (some (false, false)))
        ((authRA pathCatRA).op (authElem (some (false, false))) (fragElem (some (false, false))))) :=
    ⟨rfl, none, rfl⟩
  have hnv : ¬ (authRA pathCatRA).valid
      ((authRA pathCatRA).op (fragElem (some (false, false)))
        ((authRA pathCatRA).op (authElem (some (true, false))) (fragElem (some (true, false))))) := by
    rintro ⟨_, mc, hmc⟩
    cases mc with
    | none => cases hmc
    | some c => cases hmc
  exact ⟨pathCatRA_opAssoc, pathCatRA_validOpL, pathCatRA_not_opComm,
         hloc, hrfp, hv, hnv, fun h => hnv (h none hv)⟩

/-! ## Tightness vs. Global Necessity Boundary Lemmas -/

/-- True global necessity for universal right-dropping: if `a · b ⤳ a` holds for
all `a b : α`, then `ValidOpL R` must hold (by checking `mf = none`). Neither
`OpAssoc` nor `OpComm` is globally necessary for universal right-dropping. -/
theorem validOpL_of_fpUpdate_drop_right_all {α : Type} (R : RawRA α)
    (h : ∀ a b : α, fpUpdate R (R.op a b) a) : ValidOpL R :=
  fun x y hxy => h x y none hxy

/-- Universal right-dropping holds without `OpComm` in `boolLeftProjRA`. -/
theorem drop_right_holds_without_opComm_example :
    ¬ OpComm boolLeftProjRA ∧ ∀ a b : Bool, fpUpdate boolLeftProjRA (boolLeftProjRA.op a b) a :=
  ⟨opComm_neg_example, fun _ _ _ _ => trivial⟩

/-- Universal right-dropping holds without `OpAssoc` in `natSubRA`. -/
theorem drop_right_holds_without_opAssoc_example :
    ¬ OpAssoc natSubRA ∧ ∀ a b : Nat, fpUpdate natSubRA (natSubRA.op a b) a :=
  ⟨opAssoc_neg_example, fun _ _ _ _ => trivial⟩

/-- Universal right-framing holds without `OpAssoc` in `natSubRA`. -/
theorem frame_right_holds_without_opAssoc_example :
    ¬ OpAssoc natSubRA ∧
    ∀ a b c : Nat, fpUpdate natSubRA a b → fpUpdate natSubRA (natSubRA.op a c) (natSubRA.op b c) :=
  ⟨opAssoc_neg_example, fun _ _ _ _ _ _ => trivial⟩

/-! ## Result 5a: Right-Framing of Frame-Preserving Updates -/

/-- Right-framing of right-frame-preserving updates: in any associative raw
algebra, `a ⤳ b` implies `a · c ⤳ b · c`. Neither `OpComm` nor `ValidOpL` is
used, though without `OpComm`, `fpUpdate` preserves right-composed frames only.
Captures the right-framing specialization of Iris's `cmra_update_op`. -/
theorem fpUpdate_frame_right {α : Type} (R : RawRA α) (hAssoc : OpAssoc R)
    {a b : α} (c : α) (hab : fpUpdate R a b) :
    fpUpdate R (R.op a c) (R.op b c) := by
  intro mf hmf
  cases mf with
  | none => exact hab (some c) hmf
  | some f =>
    have h1 : R.valid (opOpt R a (some (R.op c f))) := by
      show R.valid (R.op a (R.op c f)); rw [← hAssoc]; exact hmf
    have h2 := hab (some (R.op c f)) h1
    show R.valid (R.op (R.op b c) f); rw [hAssoc]; exact h2

theorem fpUpdate_frame_right_nonvacuity :
    OpAssoc (authRA counterRA) ∧
    fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem 2) (fragElem 1))
      ((authRA counterRA).op (authElem 3) (fragElem 2)) ∧
    (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 2) (fragElem 1)) (fragElem 1)) ∧
    ¬ fpUpdate (authRA counterRA) (fragElem 1) (fragElem 2) :=
  ⟨authRA_opAssoc counterRA counterRA_opAssoc,
   auth_counter_inc_fpUpdate 2 1 1,
   ⟨trivial, (counter_includedRefl_iff 2 2).mpr (Nat.le_refl 2)⟩,
   auth_counter_inc_frag_only_fails.2.2⟩

/-- Canonical tightness counterexample for `hAssoc` in `fpUpdate_frame_right`:
`nonAssocCommValidRA` satisfies `OpComm`, `ValidOpL`, and `fpUpdate .e0 .e1`,
fails `OpAssoc`, and breaks `fpUpdate (.e0 · .e1) (.e1 · .e1)` at frame `.e2`. -/
theorem fpUpdate_frame_right_nonAssoc_counterexample :
    OpComm nonAssocCommValidRA ∧ ValidOpL nonAssocCommValidRA ∧
    ¬ OpAssoc nonAssocCommValidRA ∧
    fpUpdate nonAssocCommValidRA .e0 .e1 ∧
    ¬ fpUpdate nonAssocCommValidRA
        (nonAssocCommValidRA.op .e0 .e1) (nonAssocCommValidRA.op .e1 .e1) := by
  refine ⟨nonAssocCommValidRA_opComm, nonAssocCommValidRA_validOpL,
          nonAssocCommValidRA_not_opAssoc, nonAssocCommValidRA_upd_0_1, ?_⟩
  intro hupd
  have hv : nonAssocCommValidRA.valid
      (opOpt nonAssocCommValidRA (nonAssocCommValidRA.op .e0 .e1) (some .e2)) :=
    fun h => by cases h
  have hv' := hupd (some .e2) hv
  exact hv' rfl

/-- Canonical tightness counterexample for `hab` in `fpUpdate_frame_right`: in
`agreeRA Bool`, `OpAssoc` holds, `ag false ⤳ ag true` fails, and right-framing
with `ag false` also fails. -/
theorem fpUpdate_frame_right_noUpdate_counterexample :
    OpAssoc (agreeRA Bool) ∧
    ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag true) ∧
    ¬ fpUpdate (agreeRA Bool)
        ((agreeRA Bool).op (.ag false) (.ag false))
        ((agreeRA Bool).op (.ag true) (.ag false)) := by
  refine ⟨agreeRA_opAssoc Bool, (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2, ?_⟩
  intro hupd
  have hv : (agreeRA Bool).valid
      (opOpt (agreeRA Bool) ((agreeRA Bool).op (.ag false) (.ag false)) none) :=
    (agree_ag_op_valid_iff false false).mpr rfl
  have hv' := hupd none hv
  exact Bool.false_ne_true ((agree_ag_op_valid_iff true false).mp hv').symm

/-! ## Result 5b: Parallel Composition of Deterministic Updates -/

/-- Parallel composition of deterministic frame-preserving updates: under
`OpAssoc` and `OpComm`, `a₁ ⤳ b₁` and `a₂ ⤳ b₂` yield `a₁ · a₂ ⤳ b₁ · b₂`.
`ValidOpL` is not needed. Captures Iris's `cmra_update_op`. -/
theorem fpUpdate_op {α : Type} (R : RawRA α) (hAssoc : OpAssoc R) (hComm : OpComm R)
    {a₁ b₁ a₂ b₂ : α}
    (h₁ : fpUpdate R a₁ b₁) (h₂ : fpUpdate R a₂ b₂) :
    fpUpdate R (R.op a₁ a₂) (R.op b₁ b₂) := by
  have s1 := fpUpdate_frame_right R hAssoc a₂ h₁
  have s2 := fpUpdate_frame_right R hAssoc b₁ h₂
  rw [hComm a₂ b₁, hComm b₂ b₁] at s2
  exact fpUpdate_trans R s1 s2

theorem fpUpdate_op_nonvacuity :
    OpAssoc (authRA counterRA) ∧ OpComm (authRA counterRA) ∧
    fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem 2) (fragElem 1))
      ((authRA counterRA).op (authElem 3) (fragElem 2)) ∧
    fpUpdate (authRA counterRA) (fragElem 1) (fragElem 1) ∧
    (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 2) (fragElem 1)) (fragElem 1)) ∧
    ¬ fpUpdate (authRA counterRA) (fragElem 1) (fragElem 2) :=
  ⟨authRA_opAssoc counterRA counterRA_opAssoc,
   authRA_opComm counterRA counterRA_opComm,
   auth_counter_inc_fpUpdate 2 1 1,
   fpUpdate_refl (authRA counterRA) (fragElem 1),
   ⟨trivial, (counter_includedRefl_iff 2 2).mpr (Nat.le_refl 2)⟩,
   auth_counter_inc_frag_only_fails.2.2⟩

/-- Canonical tightness counterexample for `hAssoc` in `fpUpdate_op`. -/
theorem fpUpdate_op_nonAssoc_counterexample :
    OpComm nonAssocCommValidRA ∧ ValidOpL nonAssocCommValidRA ∧
    ¬ OpAssoc nonAssocCommValidRA ∧
    fpUpdate nonAssocCommValidRA .e0 .e1 ∧
    fpUpdate nonAssocCommValidRA .e1 .e1 ∧
    ¬ fpUpdate nonAssocCommValidRA
        (nonAssocCommValidRA.op .e0 .e1) (nonAssocCommValidRA.op .e1 .e1) :=
  ⟨nonAssocCommValidRA_opComm, nonAssocCommValidRA_validOpL,
   nonAssocCommValidRA_not_opAssoc, nonAssocCommValidRA_upd_0_1,
   fpUpdate_refl nonAssocCommValidRA .e1,
   fpUpdate_frame_right_nonAssoc_counterexample.2.2.2.2⟩

/-- Canonical tightness counterexample for `hComm` in `fpUpdate_op`: in
`pathCatRA`, `OpAssoc` and `ValidOpL` hold, `(true, false) ⤳ (true, false)` and
`(false, true) ⤳ (true, true)` hold, yet their composition fails at `mf = none`. -/
theorem fpUpdate_op_nonComm_counterexample :
    OpAssoc pathCatRA ∧ ValidOpL pathCatRA ∧
    ¬ OpComm pathCatRA ∧
    fpUpdate pathCatRA (some (true, false)) (some (true, false)) ∧
    fpUpdate pathCatRA (some (false, true)) (some (true, true)) ∧
    ¬ fpUpdate pathCatRA
        (pathCatRA.op (some (true, false)) (some (false, true)))
        (pathCatRA.op (some (true, false)) (some (true, true))) := by
  refine ⟨pathCatRA_opAssoc, pathCatRA_validOpL, pathCatRA_not_opComm,
          fpUpdate_refl pathCatRA (some (true, false)), pathCatRA_upd_01_11, ?_⟩
  intro hupd
  have hv : pathCatRA.valid
      (opOpt pathCatRA (pathCatRA.op (some (true, false)) (some (false, true))) none) := rfl
  have hv' := hupd none hv
  simp [opOpt, pathCatRA] at hv'

/-- Canonical tightness counterexample for `h₁` in `fpUpdate_op`. -/
theorem fpUpdate_op_noUpdate1_counterexample :
    OpAssoc (agreeRA Bool) ∧ OpComm (agreeRA Bool) ∧
    ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag true) ∧
    fpUpdate (agreeRA Bool) (.ag false) (.ag false) ∧
    ¬ fpUpdate (agreeRA Bool)
        ((agreeRA Bool).op (.ag false) (.ag false))
        ((agreeRA Bool).op (.ag true) (.ag false)) :=
  ⟨agreeRA_opAssoc Bool, agreeRA_opComm Bool,
   (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2,
   fpUpdate_refl (agreeRA Bool) (.ag false),
   fpUpdate_frame_right_noUpdate_counterexample.2.2⟩

/-- Canonical tightness counterexample for `h₂` in `fpUpdate_op`. -/
theorem fpUpdate_op_noUpdate2_counterexample :
    OpAssoc (agreeRA Bool) ∧ OpComm (agreeRA Bool) ∧
    fpUpdate (agreeRA Bool) (.ag false) (.ag false) ∧
    ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag true) ∧
    ¬ fpUpdate (agreeRA Bool)
        ((agreeRA Bool).op (.ag false) (.ag false))
        ((agreeRA Bool).op (.ag false) (.ag true)) := by
  refine ⟨agreeRA_opAssoc Bool, agreeRA_opComm Bool,
          fpUpdate_refl (agreeRA Bool) (.ag false),
          (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2, ?_⟩
  intro hupd
  have hv : (agreeRA Bool).valid
      (opOpt (agreeRA Bool) ((agreeRA Bool).op (.ag false) (.ag false)) none) :=
    (agree_ag_op_valid_iff false false).mpr rfl
  have hv' := hupd none hv
  exact Bool.false_ne_true ((agree_ag_op_valid_iff false true).mp hv')

/-! ## Result 5c: Parallel Composition of Set-Valued Updates (`fpUpdateP_op`) -/

/-- Parallel composition of non-deterministic (set-valued) frame-preserving
updates: under `OpAssoc` and `OpComm`, `a₁ ⤳: P₁`, `a₂ ⤳: P₂`, and pointwise
postcondition closure `∀ b₁ b₂, P₁ b₁ → P₂ b₂ → Q (b₁ · b₂)` imply
`a₁ · a₂ ⤳: Q`. `ValidOpL` is not needed. Captures Iris's `cmra_updateP_op`. -/
theorem fpUpdateP_op {α : Type} (R : RawRA α) (hAssoc : OpAssoc R) (hComm : OpComm R)
    {a₁ a₂ : α} {P₁ P₂ Q : α → Prop}
    (h₁ : fpUpdateP R a₁ P₁) (h₂ : fpUpdateP R a₂ P₂)
    (hQ : ∀ b₁ b₂, P₁ b₁ → P₂ b₂ → Q (R.op b₁ b₂)) :
    fpUpdateP R (R.op a₁ a₂) Q := by
  intro mf hmf
  cases mf with
  | none =>
    rcases h₁ (some a₂) hmf with ⟨b₁, hP₁, hv₁⟩
    have hv₁' : R.valid (opOpt R a₂ (some b₁)) := by
      show R.valid (R.op a₂ b₁); rw [hComm]; exact hv₁
    rcases h₂ (some b₁) hv₁' with ⟨b₂, hP₂, hv₂⟩
    refine ⟨R.op b₁ b₂, hQ b₁ b₂ hP₁ hP₂, ?_⟩
    show R.valid (R.op b₁ b₂); rw [hComm]; exact hv₂
  | some f =>
    have h0 : R.valid (opOpt R a₁ (some (R.op a₂ f))) := by
      show R.valid (R.op a₁ (R.op a₂ f)); rw [← hAssoc]; exact hmf
    rcases h₁ _ h0 with ⟨b₁, hP₁, hv₁⟩
    have hv₁' : R.valid (opOpt R a₂ (some (R.op b₁ f))) := by
      show R.valid (R.op a₂ (R.op b₁ f))
      have : R.op b₁ (R.op a₂ f) = R.op a₂ (R.op b₁ f) := by
        rw [← hAssoc, hComm b₁ a₂, hAssoc]
      rw [← this]; exact hv₁
    rcases h₂ _ hv₁' with ⟨b₂, hP₂, hv₂⟩
    refine ⟨R.op b₁ b₂, hQ b₁ b₂ hP₁ hP₂, ?_⟩
    show R.valid (R.op (R.op b₁ b₂) f)
    have : R.op (R.op b₁ b₂) f = R.op b₂ (R.op b₁ f) := by
      rw [hComm b₁ b₂, hAssoc]
    rw [this]; exact hv₂

theorem fpUpdateP_op_nonvacuity :
    OpAssoc (authRA counterRA) ∧ OpComm (authRA counterRA) ∧
    fpUpdateP (authRA counterRA)
      ((authRA counterRA).op (authElem 2) (fragElem 1))
      (· = (authRA counterRA).op (authElem 3) (fragElem 2)) ∧
    fpUpdateP (authRA counterRA) (fragElem 1) (· = fragElem 1) ∧
    (∀ b₁ b₂,
      b₁ = (authRA counterRA).op (authElem 3) (fragElem 2) →
      b₂ = fragElem 1 →
      (authRA counterRA).op b₁ b₂ =
        (authRA counterRA).op ((authRA counterRA).op (authElem 3) (fragElem 2)) (fragElem 1)) ∧
    (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 2) (fragElem 1)) (fragElem 1)) ∧
    ¬ fpUpdateP (authRA counterRA) (fragElem 1) (· = fragElem 2) :=
  ⟨authRA_opAssoc counterRA counterRA_opAssoc,
   authRA_opComm counterRA counterRA_opComm,
   (fpUpdate_iff_fpUpdateP _ _ _).mp (auth_counter_inc_fpUpdate 2 1 1),
   (fpUpdate_iff_fpUpdateP _ _ _).mp (fpUpdate_refl _ _),
   fun _ _ h1 h2 => by subst h1; subst h2; rfl,
   ⟨trivial, (counter_includedRefl_iff 2 2).mpr (Nat.le_refl 2)⟩,
   fun h => auth_counter_inc_frag_only_fails.2.2 ((fpUpdate_iff_fpUpdateP _ _ _).mpr h)⟩

/-- Canonical tightness counterexample for `hAssoc` in `fpUpdateP_op`. -/
theorem fpUpdateP_op_nonAssoc_counterexample :
    OpComm nonAssocCommValidRA ∧ ValidOpL nonAssocCommValidRA ∧
    ¬ OpAssoc nonAssocCommValidRA ∧
    fpUpdateP nonAssocCommValidRA .e0 (· = .e1) ∧
    fpUpdateP nonAssocCommValidRA .e1 (· = .e1) ∧
    (∀ b₁ b₂, b₁ = .e1 → b₂ = .e1 → nonAssocCommValidRA.op b₁ b₂ = .e2) ∧
    ¬ fpUpdateP nonAssocCommValidRA
        (nonAssocCommValidRA.op .e0 .e1) (· = .e2) := by
  refine ⟨nonAssocCommValidRA_opComm, nonAssocCommValidRA_validOpL,
          nonAssocCommValidRA_not_opAssoc,
          (fpUpdate_iff_fpUpdateP nonAssocCommValidRA .e0 .e1).mp nonAssocCommValidRA_upd_0_1,
          (fpUpdate_iff_fpUpdateP nonAssocCommValidRA .e1 .e1).mp (fpUpdate_refl _ Four.e1),
          fun _ _ h1 h2 => by subst h1; subst h2; rfl, ?_⟩
  intro hupd
  have hdet : fpUpdate nonAssocCommValidRA
      (nonAssocCommValidRA.op .e0 .e1) (nonAssocCommValidRA.op .e1 .e1) :=
    (fpUpdate_iff_fpUpdateP nonAssocCommValidRA _ _).mpr hupd
  exact fpUpdate_frame_right_nonAssoc_counterexample.2.2.2.2 hdet

/-- Canonical tightness counterexample for `hComm` in `fpUpdateP_op`. -/
theorem fpUpdateP_op_nonComm_counterexample :
    OpAssoc pathCatRA ∧ ValidOpL pathCatRA ∧
    ¬ OpComm pathCatRA ∧
    fpUpdateP pathCatRA (some (true, false)) (· = some (true, false)) ∧
    fpUpdateP pathCatRA (some (false, true)) (· = some (true, true)) ∧
    (∀ b₁ b₂, b₁ = some (true, false) → b₂ = some (true, true) →
      pathCatRA.op b₁ b₂ = none) ∧
    ¬ fpUpdateP pathCatRA
        (pathCatRA.op (some (true, false)) (some (false, true))) (· = none) := by
  refine ⟨pathCatRA_opAssoc, pathCatRA_validOpL, pathCatRA_not_opComm,
          (fpUpdate_iff_fpUpdateP pathCatRA _ _).mp (fpUpdate_refl _ _),
          (fpUpdate_iff_fpUpdateP pathCatRA _ _).mp pathCatRA_upd_01_11,
          fun _ _ h1 h2 => by subst h1; subst h2; rfl, ?_⟩
  intro hupd
  have hdet : fpUpdate pathCatRA
      (pathCatRA.op (some (true, false)) (some (false, true)))
      (pathCatRA.op (some (true, false)) (some (true, true))) :=
    (fpUpdate_iff_fpUpdateP pathCatRA _ _).mpr hupd
  exact fpUpdate_op_nonComm_counterexample.2.2.2.2.2 hdet

/-- Canonical tightness counterexample for `h₁` in `fpUpdateP_op`. -/
theorem fpUpdateP_op_noUpdate1_counterexample :
    OpAssoc (agreeRA Bool) ∧ OpComm (agreeRA Bool) ∧
    ¬ fpUpdateP (agreeRA Bool) (.ag false) (· = .ag true) ∧
    fpUpdateP (agreeRA Bool) (.ag false) (· = .ag false) ∧
    (∀ b₁ b₂, b₁ = .ag true → b₂ = .ag false →
      (agreeRA Bool).op b₁ b₂ = (agreeRA Bool).op (.ag true) (.ag false)) ∧
    ¬ fpUpdateP (agreeRA Bool)
        ((agreeRA Bool).op (.ag false) (.ag false))
        (· = (agreeRA Bool).op (.ag true) (.ag false)) := by
  refine ⟨agreeRA_opAssoc Bool, agreeRA_opComm Bool, ?_,
          (fpUpdate_iff_fpUpdateP _ _ _).mp (fpUpdate_refl _ _),
          fun _ _ h1 h2 => by subst h1; subst h2; rfl, ?_⟩
  · intro h
    exact (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2
      ((fpUpdate_iff_fpUpdateP _ _ _).mpr h)
  · intro h
    exact fpUpdate_frame_right_noUpdate_counterexample.2.2
      ((fpUpdate_iff_fpUpdateP _ _ _).mpr h)

/-- Canonical tightness counterexample for `h₂` in `fpUpdateP_op`. -/
theorem fpUpdateP_op_noUpdate2_counterexample :
    OpAssoc (agreeRA Bool) ∧ OpComm (agreeRA Bool) ∧
    fpUpdateP (agreeRA Bool) (.ag false) (· = .ag false) ∧
    ¬ fpUpdateP (agreeRA Bool) (.ag false) (· = .ag true) ∧
    (∀ b₁ b₂, b₁ = .ag false → b₂ = .ag true →
      (agreeRA Bool).op b₁ b₂ = (agreeRA Bool).op (.ag false) (.ag true)) ∧
    ¬ fpUpdateP (agreeRA Bool)
        ((agreeRA Bool).op (.ag false) (.ag false))
        (· = (agreeRA Bool).op (.ag false) (.ag true)) := by
  refine ⟨agreeRA_opAssoc Bool, agreeRA_opComm Bool,
          (fpUpdate_iff_fpUpdateP _ _ _).mp (fpUpdate_refl _ _), ?_,
          fun _ _ h1 h2 => by subst h1; subst h2; rfl, ?_⟩
  · intro h
    exact (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2
      ((fpUpdate_iff_fpUpdateP _ _ _).mpr h)
  · intro h
    exact fpUpdate_op_noUpdate2_counterexample.2.2.2.2
      ((fpUpdate_iff_fpUpdateP _ _ _).mpr h)

/-- Canonical tightness counterexample for `hQ` in `fpUpdateP_op`: even when
the target predicate `Q := (· = .ag true)` is inhabited by a valid element
`.ag true` in `agreeRA Bool`, all other hypotheses hold while `hQ` and
`fpUpdateP` fail. -/
theorem fpUpdateP_op_noPost_counterexample :
    OpAssoc (agreeRA Bool) ∧ OpComm (agreeRA Bool) ∧
    fpUpdateP (agreeRA Bool) (.ag false) (· = .ag false) ∧
    fpUpdateP (agreeRA Bool) (.ag false) (· = .ag false) ∧
    (∃ q : Agree Bool, q = .ag true ∧ (agreeRA Bool).valid q) ∧
    ¬ (∀ b₁ b₂ : Agree Bool, b₁ = .ag false → b₂ = .ag false →
        (agreeRA Bool).op b₁ b₂ = .ag true) ∧
    ¬ fpUpdateP (agreeRA Bool)
        ((agreeRA Bool).op (.ag false) (.ag false)) (· = .ag true) := by
  refine ⟨agreeRA_opAssoc Bool, agreeRA_opComm Bool,
          (fpUpdate_iff_fpUpdateP _ _ _).mp (fpUpdate_refl _ _),
          (fpUpdate_iff_fpUpdateP _ _ _).mp (fpUpdate_refl _ _),
          ⟨_, rfl, agree_ag_valid true⟩, ?_, ?_⟩
  · intro h
    have h1 := h (.ag false) (.ag false) rfl rfl
    rw [agree_ag_idemp] at h1
    have hm := congrArg (fun s : Agree Bool => s.mem false) h1
    cases (Eq.mp hm rfl)
  · intro hupd
    have hv : (agreeRA Bool).valid
        (opOpt (agreeRA Bool) ((agreeRA Bool).op (.ag false) (.ag false)) (some (.ag false))) := by
      show (agreeRA Bool).valid ((agreeRA Bool).op ((agreeRA Bool).op (.ag false) (.ag false)) (.ag false))
      rw [agree_ag_idemp, agree_ag_idemp]
      exact agree_ag_valid false
    rcases hupd (some (.ag false)) hv with ⟨b, hb, hvb⟩
    subst hb
    exact Bool.false_ne_true ((agree_ag_op_valid_iff true false).mp hvb).symm

/-! ## Result 5d: Resource Dropping / Weakening (`fpUpdate_drop_right`) -/

/-- Dropping a component of an owned composite resource (`a · b ⤳ a`): holds
for all `a b` under `OpAssoc`, `OpComm`, and `ValidOpL`. Captures Iris's
`cmra_update_op_l`. Globally only `ValidOpL` is necessary for universal
dropping (`validOpL_of_fpUpdate_drop_right_all`). -/
theorem fpUpdate_drop_right {α : Type} (R : RawRA α)
    (hAssoc : OpAssoc R) (hComm : OpComm R) (hValidOpL : ValidOpL R)
    (a b : α) :
    fpUpdate R (R.op a b) a := by
  intro mf hmf
  cases mf with
  | none => exact hValidOpL a b hmf
  | some f =>
    show R.valid (R.op a f)
    have hmf' : R.valid (R.op (R.op a b) f) := hmf
    have : R.op (R.op a b) f = R.op (R.op a f) b := by
      rw [hAssoc, hComm b f, ← hAssoc]
    rw [this] at hmf'
    exact hValidOpL _ _ hmf'

theorem fpUpdate_drop_right_nonvacuity :
    OpAssoc (authRA counterRA) ∧ OpComm (authRA counterRA) ∧ ValidOpL (authRA counterRA) ∧
    (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 1)) ∧
    ¬ (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 3)) :=
  ⟨authRA_opAssoc counterRA counterRA_opAssoc,
   authRA_opComm counterRA counterRA_opComm,
   authRA_validOpL counterRA counterRA_opAssoc counterRA_validOpL,
   (auth_counter_both_valid_iff 2 1).mpr (by omega),
   authRA_neg_example.1⟩

/-- Canonical tightness counterexample for `hAssoc` in `fpUpdate_drop_right`: in
`nonAssocCommValidRA`, `OpComm` and `ValidOpL` hold, `OpAssoc` fails, and
`.e2 · .e0 ⤳ .e2` fails at frame `.e2`. -/
theorem fpUpdate_drop_right_nonAssoc_counterexample :
    OpComm nonAssocCommValidRA ∧ ValidOpL nonAssocCommValidRA ∧
    ¬ OpAssoc nonAssocCommValidRA ∧
    ¬ fpUpdate nonAssocCommValidRA (nonAssocCommValidRA.op .e2 .e0) .e2 := by
  refine ⟨nonAssocCommValidRA_opComm, nonAssocCommValidRA_validOpL,
          nonAssocCommValidRA_not_opAssoc, ?_⟩
  intro hupd
  have hv : nonAssocCommValidRA.valid
      (opOpt nonAssocCommValidRA (nonAssocCommValidRA.op .e2 .e0) (some .e2)) :=
    fun h => by cases h
  have hv' := hupd (some .e2) hv
  exact hv' rfl

/-- Canonical tightness counterexample for `hComm` in `fpUpdate_drop_right`: in
`pathCatRA`, `OpAssoc` and `ValidOpL` hold, `OpComm` fails, and dropping the
middle arrow `(true, false)` from `(false, true) · (true, false)` breaks
compatibility with frame `(false, true)`. -/
theorem fpUpdate_drop_right_nonComm_counterexample :
    OpAssoc pathCatRA ∧ ValidOpL pathCatRA ∧
    ¬ OpComm pathCatRA ∧
    ¬ fpUpdate pathCatRA
        (pathCatRA.op (some (false, true)) (some (true, false)))
        (some (false, true)) := by
  refine ⟨pathCatRA_opAssoc, pathCatRA_validOpL, pathCatRA_not_opComm, ?_⟩
  intro hupd
  have hv : pathCatRA.valid
      (opOpt pathCatRA
        (pathCatRA.op (some (false, true)) (some (true, false)))
        (some (false, true))) := rfl
  have hv' := hupd (some (false, true)) hv
  simp [opOpt, pathCatRA] at hv'

/-- Canonical tightness counterexample for `hValidOpL` in `fpUpdate_drop_right`:
in `xorValidFalseRA`, `OpAssoc` and `OpComm` hold, `ValidOpL` fails, and
`true · true ⤳ true` fails at `mf = none` (`true ^^ true = false` is valid
while `true` is invalid). -/
theorem fpUpdate_drop_right_noValidOpL_counterexample :
    OpAssoc xorValidFalseRA ∧ OpComm xorValidFalseRA ∧
    ¬ ValidOpL xorValidFalseRA ∧
    ¬ fpUpdate xorValidFalseRA (xorValidFalseRA.op true true) true := by
  refine ⟨xorValidFalseRA_opAssoc, xorValidFalseRA_opComm, validOpL_neg_example, ?_⟩
  intro hupd
  have hv' := hupd none rfl
  simp [opOpt, xorValidFalseRA] at hv'

/-! ## Result 5e & 5f: When Bare Non-Empty-Frame Updates Coincide with `fpUpdate` -/

/-- Over a raw RA with a global right unit `e`, optional-frame `fpUpdate`
coincides with bare non-empty-frame `fpUpdateBare`, requiring none of
`OpAssoc`, `OpComm`, or `ValidOpL`. -/
theorem fpUpdate_iff_bare_of_rightUnit {α : Type} (R : RawRA α) (e : α)
    (hUnit : IsRightUnit R e) (a b : α) :
    fpUpdate R a b ↔ fpUpdateBare R a b := by
  refine ⟨fpUpdate_imp_fpUpdateBare R, fun h mf hmf => ?_⟩
  cases mf with
  | none =>
    have h1 := h e (by rw [hUnit]; exact hmf)
    rw [hUnit] at h1; exact h1
  | some f => exact h f hmf

theorem fpUpdate_iff_bare_of_rightUnit_nonvacuity :
    IsRightUnit (authRA counterRA) authUnit ∧ IsCoreFreeRA (authRA counterRA) ∧
    (authRA counterRA).valid ((authRA counterRA).op (authElem 2) (fragElem 1)) ∧
    ¬ fpUpdate (authRA counterRA) (fragElem 1) (fragElem 2) :=
  ⟨authRA_rightUnit counterRA, authRA_isCoreFreeRA counterRA counterRA_isCoreFreeRA,
   (auth_counter_both_valid_iff 2 1).mpr (by omega),
   auth_counter_inc_frag_only_fails.2.2⟩

/-- Canonical tightness counterexample for `hUnit` in
`fpUpdate_iff_bare_of_rightUnit`: in `exclRA Bool`, all three core-free RA laws
hold, no right unit exists, `fpUpdateBare (.excl false) .invalid` holds
vacuously, and `fpUpdate (.excl false) .invalid` fails at `mf = none`. -/
theorem fpUpdate_bare_noUnit_counterexample :
    IsCoreFreeRA (exclRA Bool) ∧
    (¬ ∃ e : Excl Bool, IsRightUnit (exclRA Bool) e) ∧
    fpUpdateBare (exclRA Bool) (.excl false) .invalid ∧
    ¬ fpUpdate (exclRA Bool) (.excl false) .invalid ∧
    ¬ (fpUpdate (exclRA Bool) (.excl false) .invalid ↔
        fpUpdateBare (exclRA Bool) (.excl false) .invalid) := by
  refine ⟨exclRA_isCoreFreeRA Bool, ?_, fun _ hf => False.elim hf, excl_invalid_target_fails false, ?_⟩
  · rintro ⟨e, he⟩
    have h0 := he (.excl false)
    cases h0
  · intro hiff
    exact excl_invalid_target_fails false (hiff.mpr fun _ hf => False.elim hf)

/-- Over a raw RA where every valid element admits a right identity
(`HasRightIdOnValid`) and validity is downward closed (`ValidOpL`),
optional-frame `fpUpdate` coincides with bare non-empty-frame `fpUpdateBare`.
Captures Iris's `cmra_discrete_total_update` (weakened from total core laws to
right identities on valid elements only). -/
theorem fpUpdate_iff_bare_of_rightIdOnValid_validOpL {α : Type} (R : RawRA α)
    (hRightId : HasRightIdOnValid R) (hValidOpL : ValidOpL R) (a b : α) :
    fpUpdate R a b ↔ fpUpdateBare R a b := by
  refine ⟨fpUpdate_imp_fpUpdateBare R, fun h mf hmf => ?_⟩
  cases mf with
  | none =>
    rcases hRightId a hmf with ⟨c, hc⟩
    have h1 := h c (by rw [hc]; exact hmf)
    exact hValidOpL b c h1
  | some f => exact h f hmf

theorem fpUpdate_iff_bare_of_rightIdOnValid_validOpL_nonvacuity :
    HasRightIdOnValid (agreeRA Bool) ∧ ValidOpL (agreeRA Bool) ∧
    (¬ ∃ e : Agree Bool, IsRightUnit (agreeRA Bool) e) ∧
    ¬ fpUpdate (agreeRA Bool) (.ag false) (.ag true) :=
  ⟨agree_hasRightIdOnValid Bool, agreeRA_validOpL Bool,
   agreeRA_bool_no_rightUnit, (agree_distinct_not_fpUpdate Bool.false_ne_true).2.2⟩

/-- Canonical tightness counterexample for `hRightId` in
`fpUpdate_iff_bare_of_rightIdOnValid_validOpL`: `exclRA Bool` satisfies
`IsCoreFreeRA` (hence `ValidOpL`), fails `HasRightIdOnValid`, and separates
`fpUpdateBare` from `fpUpdate` on `(.excl false, .invalid)`. -/
theorem fpUpdate_bare_noRightIdOnValid_counterexample :
    IsCoreFreeRA (exclRA Bool) ∧
    ValidOpL (exclRA Bool) ∧
    ¬ HasRightIdOnValid (exclRA Bool) ∧
    fpUpdateBare (exclRA Bool) (.excl false) .invalid ∧
    ¬ fpUpdate (exclRA Bool) (.excl false) .invalid ∧
    ¬ (fpUpdate (exclRA Bool) (.excl false) .invalid ↔
        fpUpdateBare (exclRA Bool) (.excl false) .invalid) := by
  refine ⟨exclRA_isCoreFreeRA Bool, exclRA_validOpL Bool, ?_,
          fun _ hf => False.elim hf, excl_invalid_target_fails false, ?_⟩
  · intro hcore
    rcases hcore (.excl false) trivial with ⟨c, hc⟩
    cases hc
  · intro hiff
    exact excl_invalid_target_fails false (hiff.mpr fun _ hf => False.elim hf)

/-- Canonical tightness counterexample for `hValidOpL` in
`fpUpdate_iff_bare_of_rightIdOnValid_validOpL`: the 5-element algebra
`fiveLocalUnitsNoValidOpLRA` (nothing is claimed about smaller witnesses; under
`HasRightIdOnValid` alone, see the 2-element witness
`two_element_comm_validOpL_witness`) satisfies `OpAssoc`,
`OpComm`, `HasLocalRightUnits` (hence `HasRightIdOnValid`), fails `ValidOpL`,
and satisfies `fpUpdateBare .z1 .z3` while failing `fpUpdate .z1 .z3` at
`mf = none`. -/
theorem fpUpdate_bare_rightIdOnValid_noValidOpL_counterexample :
    OpAssoc fiveLocalUnitsNoValidOpLRA ∧ OpComm fiveLocalUnitsNoValidOpLRA ∧
    HasLocalRightUnits fiveLocalUnitsNoValidOpLRA ∧
    HasRightIdOnValid fiveLocalUnitsNoValidOpLRA ∧
    ¬ ValidOpL fiveLocalUnitsNoValidOpLRA ∧
    fpUpdateBare fiveLocalUnitsNoValidOpLRA .z1 .z3 ∧
    ¬ fpUpdate fiveLocalUnitsNoValidOpLRA .z1 .z3 ∧
    ¬ (fpUpdate fiveLocalUnitsNoValidOpLRA .z1 .z3 ↔
        fpUpdateBare fiveLocalUnitsNoValidOpLRA .z1 .z3) := by
  have hbare : fpUpdateBare fiveLocalUnitsNoValidOpLRA .z1 .z3 := by
    intro f hf
    cases f <;> simp [fiveLocalUnitsNoValidOpLRA] at hf ⊢
  have hnupd : ¬ fpUpdate fiveLocalUnitsNoValidOpLRA .z1 .z3 := by
    intro hupd
    have hv' := hupd none (Or.inl rfl)
    rcases hv' with h | h <;> cases h
  refine ⟨fiveLocalUnitsNoValidOpLRA_opAssoc, fiveLocalUnitsNoValidOpLRA_opComm,
          fiveLocalUnitsNoValidOpLRA_hasLocalRightUnits,
          fiveLocalUnitsNoValidOpLRA_hasRightIdOnValid,
          fiveLocalUnitsNoValidOpLRA_not_validOpL,
          hbare, hnupd, fun hiff => hnupd (hiff.mpr hbare)⟩

/-- When every element is idempotent (`x · x = x`) and `OpComm` holds,
`fpUpdate` coincides with `fpUpdateBare` without requiring `ValidOpL`. So no
commutative algebra in which every element is idempotent is a tightness witness
for `ValidOpL` in `fpUpdate_iff_bare_of_rightIdOnValid_validOpL`; a commutative
witness may still contain idempotent elements (in `zeroBoolRA`,
`false · false = false`). Without `OpComm`, a 2-element witness in which every
element is idempotent exists: `idempotent_noncomm_validOpL_witness`. -/
theorem fpUpdate_iff_bare_of_idemp_opComm {α : Type} (R : RawRA α)
    (hIdem : ∀ x : α, R.op x x = x) (hComm : OpComm R) (a b : α) :
    fpUpdate R a b ↔ fpUpdateBare R a b := by
  refine ⟨fpUpdate_imp_fpUpdateBare R, fun h mf hmf => ?_⟩
  cases mf with
  | none =>
    have h2 := h a (by rw [hIdem]; exact hmf)
    rw [hComm] at h2
    have h3 := h b h2
    rw [hIdem] at h3
    exact h3
  | some f => exact h f hmf

/-! ## Simultaneous Two-Sided Frames Need `OpAssoc` as well as `OpComm` -/

/-- Left composition with an optional frame (`none` leaves `x` unchanged;
`some l` composes `l` on the left). -/
def opOptL {α : Type} (R : RawRA α) : Option α → α → α
  | none, x => x
  | some l, x => R.op l x

/-- Simultaneous two-sided frame preservation (optional left frame `ml`,
optional right frame `mr` under `ml ·? (a ·? mr)`). -/
def fpUpdate2 {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∀ ml mr : Option α, R.valid (opOptL R ml (opOpt R a mr)) → R.valid (opOptL R ml (opOpt R b mr))

/-- With `OpAssoc` and `OpComm`, right-frame preservation implies simultaneous
two-sided frame preservation. -/
theorem fpUpdate2_of_assoc_comm {α : Type} (R : RawRA α) (hAssoc : OpAssoc R)
    (hComm : OpComm R) {a b : α} (h : fpUpdate R a b) : fpUpdate2 R a b := by
  intro ml mr hv
  cases ml with
  | none => exact h mr hv
  | some l =>
    cases mr with
    | none =>
      show R.valid (R.op l b)
      have hv' : R.valid (R.op l a) := hv
      rw [hComm] at hv' ⊢
      exact h (some l) hv'
    | some r =>
      show R.valid (R.op l (R.op b r))
      have hv' : R.valid (R.op l (R.op a r)) := hv
      have e1 : ∀ x, R.op l (R.op x r) = R.op x (R.op r l) := by
        intro x; rw [hComm l, hAssoc]
      rw [e1] at hv' ⊢
      exact h (some (R.op r l)) hv'

/-- Positive example for `fpUpdate2`: in `cappedNatRA` (`OpAssoc ∧ OpComm`),
`2 ⤳ 1` preserves all simultaneous left and right frames. -/
theorem fpUpdate2_pos_example : fpUpdate2 cappedNatRA 2 1 :=
  fpUpdate2_of_assoc_comm cappedNatRA opAssoc_cappedNatRA opComm_cappedNatRA fpUpdate_pos_example

/-- Negative example for `fpUpdate2`: `1` does not two-sidedly update to `2`
in `cappedNatRA`. -/
theorem fpUpdate2_neg_example : ¬ fpUpdate2 cappedNatRA 1 2 :=
  fun h => fpUpdate_neg_example (fun mr hmr => h none mr hmr)

/-- With `OpComm` alone (without `OpAssoc`), a right-frame-preserving update
need not preserve simultaneous two-sided frames: in the commutative, `ValidOpL`,
non-associative `nonAssocCommValidRA`, `e0 ⤳ e1` holds, yet the two-sided
context `e2 · (_ · e1)` is valid around `e0` and invalid around `e1`
(and likewise `(e1 · _) · e2`). -/
theorem opComm_alone_not_two_sided :
    OpComm nonAssocCommValidRA ∧ ValidOpL nonAssocCommValidRA ∧
    ¬ OpAssoc nonAssocCommValidRA ∧
    fpUpdate nonAssocCommValidRA .e0 .e1 ∧
    nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op .e2 (nonAssocCommValidRA.op .e0 .e1)) ∧
    ¬ nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op .e2 (nonAssocCommValidRA.op .e1 .e1)) ∧
    nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op (nonAssocCommValidRA.op .e1 .e0) .e2) ∧
    ¬ nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op (nonAssocCommValidRA.op .e1 .e1) .e2) ∧
    ¬ fpUpdate2 nonAssocCommValidRA .e0 .e1 := by
  have hv : nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op .e2 (nonAssocCommValidRA.op .e0 .e1)) := by
    show Four.e0 ≠ Four.e3; intro h; cases h
  have hnv : ¬ nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op .e2 (nonAssocCommValidRA.op .e1 .e1)) := by
    intro h; exact h rfl
  have hv7 : nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op (nonAssocCommValidRA.op .e1 .e0) .e2) := by
    show Four.e0 ≠ Four.e3; intro h; cases h
  have hnv8 : ¬ nonAssocCommValidRA.valid
      (nonAssocCommValidRA.op (nonAssocCommValidRA.op .e1 .e1) .e2) := by
    intro h; exact h rfl
  have hn2 : ¬ fpUpdate2 nonAssocCommValidRA .e0 .e1 := by
    intro h2
    exact hnv (h2 (some .e2) (some .e1) hv)
  exact ⟨nonAssocCommValidRA_opComm, nonAssocCommValidRA_validOpL,
          nonAssocCommValidRA_not_opAssoc, nonAssocCommValidRA_upd_0_1, hv, hnv,
          hv7, hnv8, hn2⟩

/-- Simultaneous two-sided frame failure inside `authRA`: over the commutative,
non-associative base `nonAssocCommValidRA`, `auth e0 · frag e0 ⤳ auth e0 · frag e1`
holds for right frames, yet the two-sided fragment context
`frag e2 · (_ · frag e1)` is valid around the source and invalid around the target. -/
theorem auth_opComm_alone_not_two_sided :
    OpComm nonAssocCommValidRA ∧ ¬ OpAssoc nonAssocCommValidRA ∧
    OpComm (authRA nonAssocCommValidRA) ∧
    fpUpdate (authRA nonAssocCommValidRA)
      ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e0))
      ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e1)) ∧
    (authRA nonAssocCommValidRA).valid
      ((authRA nonAssocCommValidRA).op (fragElem .e2)
        ((authRA nonAssocCommValidRA).op
          ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e0)) (fragElem .e1))) ∧
    ¬ (authRA nonAssocCommValidRA).valid
      ((authRA nonAssocCommValidRA).op (fragElem .e2)
        ((authRA nonAssocCommValidRA).op
          ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e1)) (fragElem .e1))) ∧
    ¬ fpUpdate2 (authRA nonAssocCommValidRA)
      ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e0))
      ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e1)) := by
  have hv0 : nonAssocCommValidRA.valid .e0 := by
    show Four.e0 ≠ Four.e3; intro h; cases h
  have hv2s : (authRA nonAssocCommValidRA).valid
      ((authRA nonAssocCommValidRA).op (fragElem .e2)
        ((authRA nonAssocCommValidRA).op
          ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e0)) (fragElem .e1))) :=
    ⟨hv0, none, rfl⟩
  have hnv2s : ¬ (authRA nonAssocCommValidRA).valid
      ((authRA nonAssocCommValidRA).op (fragElem .e2)
        ((authRA nonAssocCommValidRA).op
          ((authRA nonAssocCommValidRA).op (authElem .e0) (fragElem .e1)) (fragElem .e1))) := by
    rintro ⟨_, mc, hmc⟩
    cases mc with
    | none => exact absurd hmc (by decide)
    | some c => cases c <;> exact absurd hmc (by decide)
  refine ⟨nonAssocCommValidRA_opComm, nonAssocCommValidRA_not_opAssoc,
          authRA_opComm _ nonAssocCommValidRA_opComm, ?_, hv2s, hnv2s,
          fun h2 => hnv2s (h2 (some (fragElem .e2)) (some (fragElem .e1)) hv2s)⟩
  refine (auth_both_fpUpdate_iff nonAssocCommValidRA .e0 .e0 .e0 .e1).mpr ?_
  rintro mbf ⟨_, mc, hmc⟩
  refine ⟨hv0, ?_⟩
  cases mbf with
  | none => exact ⟨some .e0, rfl⟩
  | some f =>
    cases f with
    | e0 => exact ⟨none, rfl⟩
    | e1 => exact ⟨some .e0, rfl⟩
    | e2 => exact ⟨some .e0, rfl⟩
    | e3 =>
      exfalso
      cases mc with
      | none => exact absurd hmc (by decide)
      | some c => cases c <;> exact absurd hmc (by decide)

/-! ## Two-Element Witnesses Clarifying `ValidOpL` Tightness Boundaries -/

/-- Right-zero band on `Bool` (`x · y = y`), with only `true` valid. -/
def rightZeroBoolRA : RawRA Bool where
  op _ y := y
  valid b := b = true

/-- An idempotent, associative, non-commutative 2-element canonical tightness
witness for `hValidOpL` in `fpUpdate_iff_bare_of_rightIdOnValid_validOpL`: every
element is idempotent and has a right identity (`HasLocalRightUnits` and
`HasRightIdOnValid`), `ValidOpL` fails, and `fpUpdateBare true false` holds
while `fpUpdate true false` fails. Shows that without `OpComm` a tightness
witness can have every element idempotent. -/
theorem idempotent_noncomm_validOpL_witness :
    OpAssoc rightZeroBoolRA ∧ ¬ OpComm rightZeroBoolRA ∧
    (∀ x : Bool, rightZeroBoolRA.op x x = x) ∧
    HasLocalRightUnits rightZeroBoolRA ∧ HasRightIdOnValid rightZeroBoolRA ∧
    ¬ ValidOpL rightZeroBoolRA ∧
    fpUpdateBare rightZeroBoolRA true false ∧
    ¬ fpUpdate rightZeroBoolRA true false ∧
    ¬ (fpUpdate rightZeroBoolRA true false ↔ fpUpdateBare rightZeroBoolRA true false) := by
  have hbare : fpUpdateBare rightZeroBoolRA true false := fun _ h => h
  have hn : ¬ fpUpdate rightZeroBoolRA true false := fun h => by
    have := h none rfl; cases this
  refine ⟨fun _ _ _ => rfl, ?_, fun _ => rfl, fun x => ⟨x, rfl⟩,
          fun x _ => ⟨x, rfl⟩, ?_, hbare, hn, fun hiff => hn (hiff.mpr hbare)⟩
  · intro h; have := h true false; cases this
  · intro h; have := h false true rfl; cases this

/-- Zero semigroup on `Bool` (`x · y = false`), with only `false` valid. -/
def zeroBoolRA : RawRA Bool where
  op _ _ := false
  valid b := b = false

/-- A 2-element commutative, associative canonical tightness witness for
`hValidOpL` in `fpUpdate_iff_bare_of_rightIdOnValid_validOpL` under its actual
hypothesis `HasRightIdOnValid` (where `HasLocalRightUnits` fails on the invalid
element `true`): `fpUpdateBare false true` holds while `fpUpdate false true`
fails. The 5-element witness `fiveLocalUnitsNoValidOpLRA` additionally
satisfies `HasLocalRightUnits` on every element alongside `OpAssoc` and
`OpComm`; nothing is claimed about smaller witnesses with that property. -/
theorem two_element_comm_validOpL_witness :
    OpAssoc zeroBoolRA ∧ OpComm zeroBoolRA ∧
    HasRightIdOnValid zeroBoolRA ∧ ¬ HasLocalRightUnits zeroBoolRA ∧
    ¬ ValidOpL zeroBoolRA ∧
    fpUpdateBare zeroBoolRA false true ∧
    ¬ fpUpdate zeroBoolRA false true ∧
    ¬ (fpUpdate zeroBoolRA false true ↔ fpUpdateBare zeroBoolRA false true) := by
  have hbare : fpUpdateBare zeroBoolRA false true := fun _ _ => rfl
  have hn : ¬ fpUpdate zeroBoolRA false true := fun h => by
    have := h none rfl; cases this
  refine ⟨fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, hbare, hn,
          fun hiff => hn (hiff.mpr hbare)⟩
  · intro x hx; exact ⟨false, by cases hx; rfl⟩
  · intro h; rcases h true with ⟨c, hc⟩; cases hc
  · intro h; have := h true false rfl; cases this

end Toy.RA
