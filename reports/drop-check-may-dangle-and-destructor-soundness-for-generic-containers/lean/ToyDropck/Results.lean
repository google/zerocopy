import ToyDropck.Examples
import ToyDropck.Lemmas
import ToyDropck.Inclusions
import ToyDropck.Collapse

/-!
# Results

These are statements about the toy model of `ToyDropck.Basic` and `ToyDropck.Checker`; they
neither establish nor refute the corresponding claims about Rust's drop checker or standard
library. Model–system relation: none proved.

Every concrete counterexample below is stated in canonical form: a concrete instance satisfies
the listed hypotheses and the stated conclusion fails (or, for rejection examples, holds).
-/

namespace Toy.Dropck

/-! ## R1. Soundness of the strict rule -/

/-- **R1.** For every implementation table whose types without `Drop` impl declare ownership of
the elements their glue drops (`GlueVisible`), every drop order `ord`, and every scope `p` whose
values have their declared types (`ValuesHaveTypes`) and in whose declared types every lifetime
names an existing local (`LifetimesInScope`): if the strict checker (no `may_dangle`; every type
parameter of every `Drop` impl must strictly outlive the dropped value) accepts `p` for `ord`, then
dropping the locals of `p` in the order `ord` never observes a dead or nonexistent local. -/
theorem acceptsStrict_sound_of_glueVisible (impls : ImplTable) (ord : List Nat) (p : Prog)
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : acceptsStrict impls ord p = true) :
    DropSafe impls ord p :=
  (dropSafe_stripDangle impls ord p).mp
    (dropSafe_of_acceptsP (Or.inl ⟨rfl, fun c _ h => by simp [stripDangle] at h⟩)
      (fun c _ h => by simp [stripDangle] at h) (fun c => hglue c) hval hscope hacc)

/-- Non-vacuity of R1: all hypotheses hold for `pReferentFirst` (`let x = 0; let v = vec![&x];`)
in reverse declaration order. -/
theorem acceptsStrict_sound_hypotheses_hold_pReferentFirst :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ValuesHaveTypes pReferentFirst ∧
      LifetimesInScope pReferentFirst ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pReferentFirst = true := by
  refine ⟨honest_vecStrict.2.2, ?_⟩; decide

/-- R1 without `GlueVisible`: a `Drop`-less container whose glue drops an undeclared `D<&x>`
element. -/
theorem acceptsStrict_unsound_without_glueVisible :
    ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsStrict (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := by
  refine ⟨fun h => absurd (h 0) (by decide), ?_⟩; decide

/-- R1 without `ValuesHaveTypes`: a local declared `int` that holds `D(&x)`. -/
theorem acceptsStrict_unsound_without_valuesHaveTypes :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ¬ ValuesHaveTypes pIllTyped ∧
      LifetimesInScope pIllTyped ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl vecStrict) (revDeclOrder 2) pIllTyped := by
  refine ⟨honest_vecStrict.2.2, ?_⟩; decide

/-- R1 without `LifetimesInScope`: `D(&local5)` in a scope with one local. -/
theorem acceptsStrict_unsound_without_lifetimesInScope :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ValuesHaveTypes pOutOfScopeReader ∧
      ¬ LifetimesInScope pOutOfScopeReader ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl vecStrict) (revDeclOrder 1) pOutOfScopeReader := by
  refine ⟨honest_vecStrict.2.2, ?_⟩; decide

/-- R1 without acceptance: the strict checker rejects `pOwnedReader`, which is unsafe. -/
theorem acceptsStrict_rejects_unsafe_pOwnedReader :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pOwnedReader = false ∧
      ¬ DropSafe (mkTbl vecStrict) (revDeclOrder 2) pOwnedReader := by
  refine ⟨honest_vecStrict.2.2, ?_⟩; decide

/-- The strict conjunct `j != i` of `outlives` matters: for the self-referential local
`pSelfReader`, the per-local judgment computed with the non-strict comparator `outlivesNonStrict`
accepts, both checkers reject, and the drop observes the local itself, which is dead during its
own drop. -/
theorem nonStrictOutlives_accepts_unsafe_pSelfReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pSelfReader ∧
      LifetimesInScope pSelfReader ∧
      dropckP .ownsRecurse (mkTbl vecMD) (outlivesNonStrict (revDeclOrder 1) 0)
        (.app 1 (.ref 0)) = true ∧
      acceptsStrict (mkTbl vecMD) (revDeclOrder 1) pSelfReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 1) pSelfReader = false ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pSelfReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-- A reference to a local whose own value is a reference: `Ty.ref` records the referent local
and not its type, and `observe` does not read that local's value, so in `pRefToRef`, where `x` is
dead when `d` is dropped, both checkers accept and the drops in reverse declaration order are
`DropSafe`. -/
theorem pRefToRef_accepted_and_dropSafe :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pRefToRef ∧
      LifetimesInScope pRefToRef ∧
      acceptsStrict (mkTbl vecMD) (revDeclOrder 3) pRefToRef = true ∧
      accepts (mkTbl vecMD) (revDeclOrder 3) pRefToRef = true ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 3) pRefToRef := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-! ## R2. The strict rule rejects the container pattern -/

/-- **R2.** For `pContainer` (`let mut v = Vec::new(); let x = 0; v.push(&x);`, so `v` is dropped
after `x` in reverse declaration order) and the single table `mkTbl vecMD` (a `may_dangle` `Vec`
whose destructor drops its elements and does not otherwise use them): the three honesty
conditions hold, the table has the same runtime behaviour as `mkTbl vecStrict` (the same `Vec`
without `#[may_dangle]`), `ValuesHaveTypes` and `LifetimesInScope` hold, the drops in reverse
declaration order are safe, the strict checker rejects the scope, and the `may_dangle` checker
accepts it. -/
theorem acceptsStrict_rejects_dropSafe_pContainer :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      behOf (mkTbl vecMD) = behOf (mkTbl vecStrict) ∧
      ValuesHaveTypes pContainer ∧ LifetimesInScope pContainer ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pContainer ∧
      acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pContainer = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, behOf_mkTbl_vecMD_eq_vecStrict, ?_⟩
  decide

/-- With the referent declared first (`let x = 0; let v = vec![&x];`), `v` is dropped first and
the strict checker already accepts. -/
theorem acceptsStrict_accepts_pReferentFirst :
    acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pReferentFirst = true ∧
      DropSafe (mkTbl vecStrict) (revDeclOrder 2) pReferentFirst := by
  decide

/-! ## R3. Soundness of `may_dangle` with the ownership condition -/

/-- **R3.** For every implementation table in which every `#[may_dangle]` claim is truthful (the
destructor does not use `T`: `MayDangleHonest`), every `may_dangle` impl that drops its elements
declares ownership of `T` (`OwnsDeclared`), and every type without `Drop` impl declares ownership
of the elements its glue drops (`GlueVisible`); every drop order `ord`; and every scope `p`
satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the `may_dangle` checker accepts `p` for
`ord`, then dropping the locals of `p` in the order `ord` never observes a dead or nonexistent
local. In this one-parameter model the proof reduces R3 to R1 by replacing every `#[may_dangle]`
impl with a `Drop`-less type (`eraseMayDangle`). -/
theorem accepts_sound_of_mayDangleHonest_ownsDeclared_glueVisible (impls : ImplTable)
    (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hown : ∀ c, OwnsDeclared (impls c))
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : accepts impls ord p = true) :
    DropSafe impls ord p := by
  rw [accepts_eq_acceptsStrict_eraseMayDangle] at hacc
  exact (dropSafe_eraseMayDangle_iff hmd ord p).mp
    (acceptsStrict_sound_of_glueVisible (eraseMayDangle impls) ord p
      ((glueVisible_eraseMayDangle_iff impls).mpr ⟨hown, hglue⟩) hval hscope hacc)

/-- Non-vacuity of R3: all hypotheses hold for `pContainer` with the `may_dangle` `Vec`. -/
theorem accepts_sound_hypotheses_hold_pContainer :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pContainer ∧
      LifetimesInScope pContainer ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-- R3 without `MayDangleHonest`: a `may_dangle` destructor that uses its dangling `&x`. -/
theorem accepts_unsound_without_mayDangleHonest :
    ¬ (∀ c, MayDangleHonest (mkTbl liar c)) ∧ (∀ c, OwnsDeclared (mkTbl liar c)) ∧
      (∀ c, GlueVisible (mkTbl liar c)) ∧ ValuesHaveTypes pContainer ∧
      LifetimesInScope pContainer ∧
      accepts (mkTbl liar) (revDeclOrder 2) pContainer = true ∧
      ¬ DropSafe (mkTbl liar) (revDeclOrder 2) pContainer := by
  refine ⟨fun h => absurd (h 0) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  decide

/-- R3 without `OwnsDeclared`: a truthful `may_dangle` container that drops its elements without
declaring ownership of `T` holds a `D<&x>` whose own destructor dereferences `&x`. -/
theorem accepts_unsound_without_ownsDeclared :
    (∀ c, MayDangleHonest (mkTbl vecNoOwn c)) ∧ ¬ (∀ c, OwnsDeclared (mkTbl vecNoOwn c)) ∧
      (∀ c, GlueVisible (mkTbl vecNoOwn c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      accepts (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader := by
  refine ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    fun h => absurd (h 0) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  decide

/-- R3 without `GlueVisible`: a `Drop`-less container whose glue drops an undeclared `D<&x>`. -/
theorem accepts_unsound_without_glueVisible :
    (∀ c, MayDangleHonest (mkTbl hiddenGlue c)) ∧ (∀ c, OwnsDeclared (mkTbl hiddenGlue c)) ∧
      ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      accepts (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := by
  refine ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    fun h => absurd (h 0) (by decide), ?_⟩
  decide

/-- R3 without `ValuesHaveTypes`: a local declared `int` that holds `D(&x)`. -/
theorem accepts_unsound_without_valuesHaveTypes :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ¬ ValuesHaveTypes pIllTyped ∧
      LifetimesInScope pIllTyped ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pIllTyped := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-- R3 without `LifetimesInScope`: `D(&local5)` in a scope with one local. -/
theorem accepts_unsound_without_lifetimesInScope :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOutOfScopeReader ∧
      ¬ LifetimesInScope pOutOfScopeReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-- R3 without acceptance, and the ownership recursion at work: with ownership declared, the
`may_dangle` checker rejects `pOwnedReader` (a `Vec<D<&x>>` dropped after `x`), which is unsafe. -/
theorem accepts_rejects_unsafe_pOwnedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pOwnedReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-! ## R4. Relaxations of the ownership recursion -/

/-- **R4a.** "The destructor never uses `T`" without the ownership recursion is unsound: with all
three honesty conditions holding and `pOwnedReader` satisfying `ValuesHaveTypes` and
`LifetimesInScope`, the `noUseSuffices` checker accepts `pOwnedReader` for reverse declaration
order, and its drops in that order observe a dead local. -/
theorem noUseSuffices_accepts_unsafe_pOwnedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pOwnedReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-- Positive control for R4a: the same scope with a `may_dangle` container that does not drop its
elements (`rawVec`) is accepted by `noUseSuffices` and is safe. -/
theorem noUseSuffices_accepts_safe_pOwnedReader_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 2) pOwnedReader = true ∧
      DropSafe (mkTbl rawVec) (revDeclOrder 2) pOwnedReader := by
  refine ⟨honest_rawVec.1, honest_rawVec.2.1, honest_rawVec.2.2, ?_⟩; decide

/-- **R4b.** "`T: !Drop`" checked on the outermost type constructor is unsound: with all three
honesty conditions holding and `pNestedReader` (`Vec<W<D<&x>>>`, `W` without `Drop` impl)
satisfying `ValuesHaveTypes` and `LifetimesInScope`, the `headNoDrop` checker accepts
`pNestedReader` for reverse declaration order, and its drops in that order observe a dead
local. -/
theorem headNoDrop_accepts_unsafe_pNestedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pNestedReader ∧
      LifetimesInScope pNestedReader ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-- Control for R4a and R4b: on the same programs and table, the `ownsRecurse` and `deepNoDrop`
checkers reject. -/
theorem sound_policies_reject_pOwnedReader_pNestedReader :
    accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false := by
  decide

/-- **R4c.** "`T: !Drop`" checked deeply, with the outlives requirement as fallback, is sound
without the ownership condition: for every implementation table satisfying `MayDangleHonest` and
`GlueVisible`, every drop order `ord`, and every scope `p` satisfying `ValuesHaveTypes` and
`LifetimesInScope`: if the `deepNoDrop` checker accepts `p` for `ord`, then dropping the locals of
`p` in the order `ord` never observes a dead or nonexistent local. -/
theorem acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible (impls : ImplTable)
    (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hglue : ∀ c, GlueVisible (impls c))
    (hval : ValuesHaveTypes p) (hscope : LifetimesInScope p)
    (hacc : acceptsP .deepNoDrop impls ord p = true) : DropSafe impls ord p :=
  dropSafe_of_acceptsP (Or.inr (Or.inl rfl)) hmd hglue hval hscope hacc

/-- Non-vacuity of R4c, with a table that violates `OwnsDeclared`. -/
theorem deepNoDrop_sound_hypotheses_hold_pContainer_vecNoOwn :
    (∀ c, MayDangleHonest (mkTbl vecNoOwn c)) ∧ (∀ c, GlueVisible (mkTbl vecNoOwn c)) ∧
      ValuesHaveTypes pContainer ∧ LifetimesInScope pContainer ∧
      acceptsP .deepNoDrop (mkTbl vecNoOwn) (revDeclOrder 2) pContainer = true ∧
      ¬ (∀ c, OwnsDeclared (mkTbl vecNoOwn c)) := by
  refine ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide), by decide, by decide, by decide,
    fun h => absurd (h 0) (by decide)⟩

/-- R4c without `MayDangleHonest`: "`T: !Drop`" does not help when the destructor uses `T`. -/
theorem deepNoDrop_unsound_without_mayDangleHonest :
    ¬ (∀ c, MayDangleHonest (mkTbl liar c)) ∧ (∀ c, GlueVisible (mkTbl liar c)) ∧
      ValuesHaveTypes pContainer ∧ LifetimesInScope pContainer ∧
      acceptsP .deepNoDrop (mkTbl liar) (revDeclOrder 2) pContainer = true ∧
      ¬ DropSafe (mkTbl liar) (revDeclOrder 2) pContainer := by
  refine ⟨fun h => absurd (h 0) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  decide

/-- R4c without `GlueVisible`. -/
theorem deepNoDrop_unsound_without_glueVisible :
    (∀ c, MayDangleHonest (mkTbl hiddenGlue c)) ∧ ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧
      ValuesHaveTypes pOwnedReader ∧ LifetimesInScope pOwnedReader ∧
      acceptsP .deepNoDrop (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := by
  refine ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    fun h => absurd (h 0) (by decide), ?_⟩
  decide

/-- R4c without `ValuesHaveTypes`. -/
theorem deepNoDrop_unsound_without_valuesHaveTypes :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      ¬ ValuesHaveTypes pIllTyped ∧ LifetimesInScope pIllTyped ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pIllTyped := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.2, ?_⟩; decide

/-- R4c without `LifetimesInScope`. -/
theorem deepNoDrop_unsound_without_lifetimesInScope :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      ValuesHaveTypes pOutOfScopeReader ∧ ¬ LifetimesInScope pOutOfScopeReader ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.2, ?_⟩; decide

/-- R4c without acceptance. -/
theorem deepNoDrop_rejects_unsafe_pNestedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      ValuesHaveTypes pNestedReader ∧ LifetimesInScope pNestedReader ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedReader := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.2, ?_⟩; decide

/-- The `deepNoDrop` checker rejects a safe container of containers holding a dangling reference
(`Vec<Vec<&x>>` declared before `x`), which the `ownsRecurse` checker accepts. -/
theorem deepNoDrop_rejects_accepted_safe_pNestedVec :
    ValuesHaveTypes pNestedVec ∧ LifetimesInScope pNestedVec ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pNestedVec = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedVec = false ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedVec := by
  decide

/-- The `deepNoDrop` checker rejects a safe `Vec<ManuallyDrop<D<&x>>>`-like scope (the wrapper
`3` has no `Drop` impl and drops nothing), which the `ownsRecurse` checker accepts. -/
theorem deepNoDrop_rejects_accepted_safe_pManuallyDropReader :
    ValuesHaveTypes pManuallyDropReader ∧ LifetimesInScope pManuallyDropReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pManuallyDropReader = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pManuallyDropReader = false ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pManuallyDropReader := by
  decide

/-! ## R5. Drop order matters -/

/-- **R5.** For `pReaderAfter` (`let x = 0; let d = D(&x);`, `D`'s destructor using `&x`), with all
three honesty conditions holding and `ValuesHaveTypes`, `LifetimesInScope` holding: the
`may_dangle` checker accepts it for reverse declaration order and its drops in that order are
safe; its drops in declaration order observe a dead local; and the checker, given declaration
order, rejects it. -/
theorem dropOrder_matters_pReaderAfter :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pReaderAfter ∧
      LifetimesInScope pReaderAfter ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pReaderAfter = true ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pReaderAfter ∧
      ¬ DropSafe (mkTbl vecMD) (declOrder 2) pReaderAfter ∧
      accepts (mkTbl vecMD) (declOrder 2) pReaderAfter = false := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-! ## R6. The checker is incomplete -/

/-- **R6.** For `pEmptyOwnedReader` (an empty `Vec<D<&x>>` declared before `x`), with all three
honesty conditions holding and `ValuesHaveTypes`, `LifetimesInScope` holding: its drops in reverse
declaration order are safe, but the `may_dangle` checker rejects it for that order. -/
theorem accepts_incomplete_pEmptyOwnedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pEmptyOwnedReader ∧
      LifetimesInScope pEmptyOwnedReader ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pEmptyOwnedReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pEmptyOwnedReader = false := by
  refine ⟨honest_vecMD.1, honest_vecMD.2.1, honest_vecMD.2.2, ?_⟩; decide

/-! ## R7. Inclusions among the checker policies -/

/-- **R7 (i).** For every policy `pol`, table, drop order and scope: if the strict checker accepts,
the checker under `pol` accepts. -/
theorem acceptsP_of_acceptsStrict (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat)
    (p : Prog) (h : acceptsStrict impls ord p = true) : acceptsP pol impls ord p = true :=
  acceptsFrom_mono (fun _ t => dropckP_of_strip pol t) p.locals 0 h

/-- **R7 (i), `ownsRecurse` instance.** If the strict checker accepts, the `may_dangle` checker
accepts. -/
theorem accepts_of_acceptsStrict (impls : ImplTable) (ord : List Nat) (p : Prog)
    (h : acceptsStrict impls ord p = true) : accepts impls ord p = true :=
  acceptsP_of_acceptsStrict .ownsRecurse impls ord p h

/-- **R7 (ii).** If the `deepNoDrop` checker accepts, the `may_dangle` (`ownsRecurse`) checker
accepts. -/
theorem accepts_of_acceptsP_deepNoDrop (impls : ImplTable) (ord : List Nat) (p : Prog)
    (h : acceptsP .deepNoDrop impls ord p = true) : accepts impls ord p = true :=
  acceptsFrom_mono (fun _ t => dropckP_ownsRecurse_of_deepNoDrop t) p.locals 0 h

/-- **R7 (iii).** If the `deepNoDrop` checker accepts, the `headNoDrop` checker accepts. -/
theorem acceptsP_headNoDrop_of_deepNoDrop (impls : ImplTable) (ord : List Nat) (p : Prog)
    (h : acceptsP .deepNoDrop impls ord p = true) : acceptsP .headNoDrop impls ord p = true :=
  acceptsFrom_mono (fun _ t => dropckP_headNoDrop_of_deepNoDrop t) p.locals 0 h

/-- **R7 (iv).** If the checker under any policy accepts, the `noUseSuffices` checker accepts. -/
theorem acceptsP_noUseSuffices_of_acceptsP (pol : DanglePolicy) (impls : ImplTable)
    (ord : List Nat) (p : Prog) (h : acceptsP pol impls ord p = true) :
    acceptsP .noUseSuffices impls ord p = true :=
  acceptsFrom_mono (fun _ t => dropckP_noUseSuffices_of_dropckP pol t) p.locals 0 h

/-- Non-vacuity of R7: each premise holds for a concrete instance. -/
theorem policy_inclusion_premises_hold :
    acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pReferentFirst = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pContainer = true ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := by
  decide

/-- Every inclusion of R7 is strict, and `headNoDrop` and `ownsRecurse` are incomparable, on the
single table `mkTbl vecMD` with reverse declaration order: `pContainer` separates the strict
checker from `deepNoDrop`; `pNestedVec` separates `deepNoDrop` (and `headNoDrop`) from
`ownsRecurse`; `pNestedReader` separates `deepNoDrop` (and `ownsRecurse`) from `headNoDrop`;
`pOwnedReader` separates `ownsRecurse` and `headNoDrop` from `noUseSuffices`. -/
theorem policy_separations_mkTbl_vecMD :
    (acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pContainer = false ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pContainer = true) ∧
    (accepts (mkTbl vecMD) (revDeclOrder 2) pNestedVec = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedVec = false ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedVec = false) ∧
    (acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false) ∧
    (acceptsP .noUseSuffices (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = true ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false) := by
  decide

/-- Tightness of the premise of R7 (i): for `pOwnedReader` both the strict and the `may_dangle`
checker reject. -/
theorem accepts_of_acceptsStrict_counterexample_pOwnedReader :
    acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false := by
  decide

/-- Tightness of the premises of R7 (ii) and (iii): for `pOwnedReader` the `deepNoDrop`, the
`may_dangle` and the `headNoDrop` checkers reject. -/
theorem deepNoDrop_inclusions_counterexample_pOwnedReader :
    acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false := by
  decide

/-- Tightness of the premise of R7 (iv): for `pReaderAfter` in declaration order the `may_dangle`
and the `noUseSuffices` checkers reject. -/
theorem noUseSuffices_inclusion_counterexample_pReaderAfter :
    accepts (mkTbl vecMD) (declOrder 2) pReaderAfter = false ∧
      acceptsP .noUseSuffices (mkTbl vecMD) (declOrder 2) pReaderAfter = false := by
  decide

/-! ## R8. Every policy is sound when no `may_dangle` impl drops its elements -/

/-- **R8.** For every policy `pol`, every implementation table satisfying `MayDangleHonest`,
`MayDangleDropsNothing` (no `#[may_dangle]` impl drops its elements) and `GlueVisible`, every drop
order `ord`, and every scope `p` satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the
checker under `pol` accepts `p` for `ord`, then dropping the locals of `p` in the order `ord` never
observes a dead or nonexistent local. -/
theorem acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible (pol : DanglePolicy)
    (impls : ImplTable) (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : acceptsP pol impls ord p = true) :
    DropSafe impls ord p :=
  dropSafe_of_acceptsP (Or.inr (Or.inr hnodrop)) hmd hglue hval hscope hacc

/-- Non-vacuity of R8: all hypotheses hold for `pOwnedReader` with `rawVec` and the policy
`noUseSuffices`. -/
theorem dropsNothing_sound_hypotheses_hold_pOwnedReader_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 2) pOwnedReader = true := by
  refine ⟨honest_rawVec.1, honest_rawVec.2.1, honest_rawVec.2.2, ?_⟩; decide

/-- R8 without `MayDangleHonest`: a `may_dangle` destructor that drops nothing but uses its
dangling `&x`. -/
theorem dropsNothing_unsound_without_mayDangleHonest :
    ¬ (∀ c, MayDangleHonest (mkTbl liarRaw c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl liarRaw c)) ∧
      (∀ c, GlueVisible (mkTbl liarRaw c)) ∧ ValuesHaveTypes pContainer ∧
      LifetimesInScope pContainer ∧
      acceptsP .noUseSuffices (mkTbl liarRaw) (revDeclOrder 2) pContainer = true ∧
      ¬ DropSafe (mkTbl liarRaw) (revDeclOrder 2) pContainer := by
  refine ⟨fun h => absurd (h 0) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  decide

/-- R8 without `MayDangleDropsNothing`: the honest `may_dangle` `Vec` that drops its elements
(this is the instance of R4a). -/
theorem dropsNothing_unsound_without_mayDangleDropsNothing :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ ¬ (∀ c, MayDangleDropsNothing (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pOwnedReader := by
  refine ⟨honest_vecMD.1, fun h => absurd (h 0) (by decide), honest_vecMD.2.2, ?_⟩; decide

/-- R8 without `GlueVisible`. -/
theorem dropsNothing_unsound_without_glueVisible :
    (∀ c, MayDangleHonest (mkTbl hiddenGlue c)) ∧
      (∀ c, MayDangleDropsNothing (mkTbl hiddenGlue c)) ∧
      ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := by
  refine ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    fun h => absurd (h 0) (by decide), ?_⟩
  decide

/-- R8 without `ValuesHaveTypes`. -/
theorem dropsNothing_unsound_without_valuesHaveTypes :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ¬ ValuesHaveTypes pIllTyped ∧
      LifetimesInScope pIllTyped ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl rawVec) (revDeclOrder 2) pIllTyped := by
  refine ⟨honest_rawVec.1, honest_rawVec.2.1, honest_rawVec.2.2, ?_⟩; decide

/-- R8 without `LifetimesInScope`. -/
theorem dropsNothing_unsound_without_lifetimesInScope :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pOutOfScopeReader ∧
      ¬ LifetimesInScope pOutOfScopeReader ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl rawVec) (revDeclOrder 1) pOutOfScopeReader := by
  refine ⟨honest_rawVec.1, honest_rawVec.2.1, honest_rawVec.2.2, ?_⟩; decide

/-- R8 without acceptance: in declaration order the `noUseSuffices` checker rejects
`pReaderAfter`, whose drops in that order are unsafe. -/
theorem dropsNothing_rejects_unsafe_pReaderAfter :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pReaderAfter ∧
      LifetimesInScope pReaderAfter ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (declOrder 2) pReaderAfter = false ∧
      ¬ DropSafe (mkTbl rawVec) (declOrder 2) pReaderAfter := by
  refine ⟨honest_rawVec.1, honest_rawVec.2.1, honest_rawVec.2.2, ?_⟩; decide

end Toy.Dropck
