import ToyDropck.Results

/-!
# Companion facts

Additional concrete facts about the policies and an alternative proof of R8, stated about the toy
model of `ToyDropck.Basic` and `ToyDropck.Checker`. These are statements about the toy model; they
neither establish nor refute the corresponding claims about Rust's drop checker or standard
library. Model–system relation: none proved.
-/

namespace Toy.Dropck

/-! ## The escape hatch of R4b on the scope of R4b -/

/-- With a `may_dangle` container that does not drop its elements (`rawVec`), the `headNoDrop`
checker accepts `pNestedReader` (`Vec<W<D<&x>>>` declared before `x`) for reverse declaration
order, and those drops are safe. -/
theorem headNoDrop_accepts_safe_pNestedReader_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pNestedReader ∧
      LifetimesInScope pNestedReader ∧
      acceptsP .headNoDrop (mkTbl rawVec) (revDeclOrder 2) pNestedReader = true ∧
      DropSafe (mkTbl rawVec) (revDeclOrder 2) pNestedReader := by
  refine ⟨honest_rawVec.1, honest_rawVec.2.1, honest_rawVec.2.2, ?_⟩; decide

/-! ## R8 without `MayDangleDropsNothing`, for further policies -/

/-- R8 without `MayDangleDropsNothing`, under the policy `headNoDrop`: the honest `may_dangle`
`Vec` that drops its elements, on `pNestedReader` (the instance of R4b). -/
theorem dropsNothing_unsound_without_mayDangleDropsNothing_headNoDrop :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ ¬ (∀ c, MayDangleDropsNothing (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pNestedReader ∧
      LifetimesInScope pNestedReader ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedReader := by
  refine ⟨honest_vecMD.1, fun h => absurd (h 0) (by decide), honest_vecMD.2.2, ?_⟩; decide

/-- R8 without `MayDangleDropsNothing`, under the policy `ownsRecurse`: a truthful `may_dangle`
`Vec` that drops its elements without declaring ownership of `T` (`vecNoOwn`), on `pOwnedReader`.
R8 does not assume `OwnsDeclared`. -/
theorem dropsNothing_unsound_without_mayDangleDropsNothing_ownsRecurse :
    (∀ c, MayDangleHonest (mkTbl vecNoOwn c)) ∧
      ¬ (∀ c, MayDangleDropsNothing (mkTbl vecNoOwn c)) ∧
      (∀ c, GlueVisible (mkTbl vecNoOwn c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .ownsRecurse (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader := by
  refine ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
    fun h => absurd (h 0) (by decide),
    mkTbl_all _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  decide

/-! ## R8 from R1 and R7 (iv) -/

/-- Replace every `may_dangle` `Drop` impl by `plain` (no `Drop` impl, drops nothing, declares
nothing); every other entry is unchanged. -/
def eraseMayDangleToPlain (impls : ImplTable) : ImplTable := fun c =>
  if (impls c).beh.hasDrop && (impls c).decl.mayDangle then plain else impls c

mutual
private theorem dropVal_eq_eraseMayDangleToPlain {impls : ImplTable}
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (L : Nat → Bool) :
    ∀ v : Val, dropVal (behOf impls) L v = dropVal (behOf (eraseMayDangleToPlain impls)) L v
  | .int _ => rfl
  | .ref _ => rfl
  | .obj c vs => by
    have ih := dropAll_eq_eraseMayDangleToPlain hmd hnodrop L vs
    have hmdc := hmd c
    have hndc := hnodrop c
    unfold MayDangleHonest at hmdc
    unfold MayDangleDropsNothing at hndc
    rcases hc : impls c with ⟨⟨hD, hU, hE⟩, ⟨hM, hO⟩⟩
    rw [hc] at hmdc hndc
    cases hD <;> cases hM
    · simp [dropVal, behOf, eraseMayDangleToPlain, hc, ih]
    · simp [dropVal, behOf, eraseMayDangleToPlain, hc, ih]
    · simp [dropVal, behOf, eraseMayDangleToPlain, hc, ih]
    · have hu : hU = false := hmdc rfl rfl
      have he : hE = false := hndc rfl rfl
      simp [dropVal, behOf, eraseMayDangleToPlain, plain, hc, hu, he]

private theorem dropAll_eq_eraseMayDangleToPlain {impls : ImplTable}
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (L : Nat → Bool) :
    ∀ vs : List Val,
      dropAll (behOf impls) L vs = dropAll (behOf (eraseMayDangleToPlain impls)) L vs
  | [] => rfl
  | v :: vs => by
    simp only [dropAll, dropVal_eq_eraseMayDangleToPlain hmd hnodrop L v,
      dropAll_eq_eraseMayDangleToPlain hmd hnodrop L vs]
end

private theorem runDrops_eq_eraseMayDangleToPlain {impls : ImplTable}
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (p : Prog) :
    ∀ ks dead : List Nat,
      runDrops (behOf impls) p ks dead =
        runDrops (behOf (eraseMayDangleToPlain impls)) p ks dead
  | [], _ => rfl
  | k :: ks, dead => by
    simp only [runDrops]
    split
    · exact runDrops_eq_eraseMayDangleToPlain hmd hnodrop p ks dead
    · cases p.locals[k]? with
      | none => exact runDrops_eq_eraseMayDangleToPlain hmd hnodrop p ks dead
      | some e =>
        simp [dropVal_eq_eraseMayDangleToPlain hmd hnodrop _ e.2,
          runDrops_eq_eraseMayDangleToPlain hmd hnodrop p ks (k :: dead)]

/-- Under `MayDangleHonest` and `MayDangleDropsNothing`, replacing every `may_dangle` impl by
`plain` does not change `DropSafe`. -/
theorem dropSafe_eraseMayDangleToPlain_iff {impls : ImplTable}
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (ord : List Nat) (p : Prog) :
    DropSafe (eraseMayDangleToPlain impls) ord p ↔ DropSafe impls ord p := by
  unfold DropSafe
  rw [runDrops_eq_eraseMayDangleToPlain hmd hnodrop p ord []]

/-- Replacing every `may_dangle` impl by `plain` preserves `GlueVisible`. -/
theorem glueVisible_eraseMayDangleToPlain {impls : ImplTable}
    (hglue : ∀ c, GlueVisible (impls c)) : ∀ c, GlueVisible (eraseMayDangleToPlain impls c) := by
  intro c
  unfold GlueVisible eraseMayDangleToPlain
  split
  · intro _ hE; simp [plain] at hE
  · exact hglue c

/-- Acceptance by the `noUseSuffices` checker implies acceptance by the strict checker on the
table with every `may_dangle` impl replaced by `plain`. -/
theorem acceptsStrict_eraseMayDangleToPlain_of_noUseSuffices (impls : ImplTable)
    (ord : List Nat) (p : Prog) (h : acceptsP .noUseSuffices impls ord p = true) :
    acceptsStrict (eraseMayDangleToPlain impls) ord p = true := by
  refine acceptsFrom_mono (fun _ t h => ?_) p.locals 0 h
  induction t with
  | int => rfl
  | ref _ => rfl
  | app c t ih =>
    rcases hc : impls c with ⟨⟨hD, hU, hE⟩, ⟨hM, hO⟩⟩
    cases hD <;> cases hM
    · simp only [dropckP, stripDangle, eraseMayDangleToPlain, hc, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.true_and,
        Bool.or_eq_true] at h ⊢
      exact h.imp_right ih
    · simp only [dropckP, stripDangle, eraseMayDangleToPlain, hc, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.true_and,
        Bool.or_eq_true] at h ⊢
      exact h.imp_right ih
    · simp only [dropckP, stripDangle, eraseMayDangleToPlain, hc, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true] at h ⊢
      exact ⟨h.1, h.2.imp_right ih⟩
    · simp [dropckP, stripDangle, eraseMayDangleToPlain, plain, hc]

/-- R8 (same statement as `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible`), proved
from R1 (`acceptsStrict_sound_of_glueVisible`) and R7 (iv) (`acceptsP_noUseSuffices_of_acceptsP`)
through `eraseMayDangleToPlain`. -/
theorem acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible_via_acceptsStrict
    (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : acceptsP pol impls ord p = true) :
    DropSafe impls ord p :=
  (dropSafe_eraseMayDangleToPlain_iff hmd hnodrop ord p).1
    (acceptsStrict_sound_of_glueVisible _ ord p (glueVisible_eraseMayDangleToPlain hglue) hval
      hscope (acceptsStrict_eraseMayDangleToPlain_of_noUseSuffices impls ord p
        (acceptsP_noUseSuffices_of_acceptsP pol impls ord p hacc)))

end Toy.Dropck
