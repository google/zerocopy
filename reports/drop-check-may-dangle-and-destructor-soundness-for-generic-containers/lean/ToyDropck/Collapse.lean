import ToyDropck.Lemmas

/-!
# What the one-parameter model can and cannot express

Every container type constructor has one type parameter and no lifetime parameters, and the
model gives a destructor two possible actions on that parameter: using its values (`usesT`) and
dropping them (`dropsElems`). The lemmas below make the consequences precise: every type mentions
at most one lifetime, and under `MayDangleHonest` a `#[may_dangle]` `Drop` impl is interchangeable,
for both the `may_dangle` checker and the drop loop, with a type that has no `Drop` impl.
-/

namespace Toy.Dropck

/-- Every type mentions at most one lifetime. -/
theorem lifetimes_length_le_one : ∀ t : Ty, (lifetimes t).length ≤ 1
  | .int => by simp [lifetimes]
  | .ref _ => by simp [lifetimes]
  | .app _ t => by simpa [lifetimes] using lifetimes_length_le_one t

/-- Replace every `Drop` impl that carries `#[may_dangle]` by a type without `Drop` impl that has
the same element drops (`dropsElems`) and the same ownership declaration (`ownsT`). -/
def eraseMayDangle (impls : ImplTable) : ImplTable := fun c =>
  if (impls c).beh.hasDrop && (impls c).decl.mayDangle then
    ⟨⟨false, (impls c).beh.usesT, (impls c).beh.dropsElems⟩, ⟨false, (impls c).decl.ownsT⟩⟩
  else
    impls c

theorem dropckP_ownsRecurse_eq_strict_eraseMayDangle (impls : ImplTable) (ok : Nat → Bool) :
    ∀ t : Ty, dropckP .ownsRecurse impls ok t =
      dropckP .ownsRecurse (stripDangle (eraseMayDangle impls)) ok t
  | .int => rfl
  | .ref _ => rfl
  | .app c t => by
    have ih := dropckP_ownsRecurse_eq_strict_eraseMayDangle impls ok t
    rcases hc : impls c with ⟨⟨hasDrop, usesT, dropsElems⟩, ⟨mayDangle, ownsT⟩⟩
    cases hasDrop <;> cases mayDangle <;> simp [dropckP, stripDangle, eraseMayDangle, hc, ih]

theorem acceptsFrom_eq_strict_eraseMayDangle (impls : ImplTable) (ord : List Nat) :
    ∀ (l : List (Ty × Val)) (i : Nat),
      acceptsFrom .ownsRecurse impls ord i l =
        acceptsFrom .ownsRecurse (stripDangle (eraseMayDangle impls)) ord i l
  | [], _ => rfl
  | (t, _) :: rest, i => by
    rw [acceptsFrom, acceptsFrom, dropckP_ownsRecurse_eq_strict_eraseMayDangle,
      acceptsFrom_eq_strict_eraseMayDangle]

/-- The `may_dangle` checker on a table equals the strict checker on the table with every
`#[may_dangle]` impl replaced by a `Drop`-less type. -/
theorem accepts_eq_acceptsStrict_eraseMayDangle (impls : ImplTable) (ord : List Nat) (p : Prog) :
    accepts impls ord p = acceptsStrict (eraseMayDangle impls) ord p :=
  acceptsFrom_eq_strict_eraseMayDangle impls ord p.locals 0

mutual
theorem dropVal_eq_eraseMayDangle {impls : ImplTable} (hmd : ∀ c, MayDangleHonest (impls c))
    (L : Nat → Bool) :
    ∀ v : Val, dropVal (behOf impls) L v = dropVal (behOf (eraseMayDangle impls)) L v
  | .int _ => rfl
  | .ref _ => rfl
  | .obj c vs => by
    have ih := dropAll_eq_eraseMayDangle hmd L vs
    have hmdc := hmd c
    unfold MayDangleHonest at hmdc
    rcases hc : impls c with ⟨⟨hasDrop, usesT, dropsElems⟩, ⟨mayDangle, ownsT⟩⟩
    rw [hc] at hmdc
    cases hasDrop <;> cases mayDangle
    · simp [dropVal, behOf, eraseMayDangle, hc, ih]
    · simp [dropVal, behOf, eraseMayDangle, hc, ih]
    · simp [dropVal, behOf, eraseMayDangle, hc, ih]
    · have hU : usesT = false := hmdc rfl rfl
      simp [dropVal, behOf, eraseMayDangle, hc, hU, ih]

theorem dropAll_eq_eraseMayDangle {impls : ImplTable} (hmd : ∀ c, MayDangleHonest (impls c))
    (L : Nat → Bool) :
    ∀ vs : List Val,
      dropAll (behOf impls) L vs = dropAll (behOf (eraseMayDangle impls)) L vs
  | [] => rfl
  | v :: vs => by
    simp only [dropAll, dropVal_eq_eraseMayDangle hmd L v, dropAll_eq_eraseMayDangle hmd L vs]
end

theorem runDrops_eq_eraseMayDangle {impls : ImplTable} (hmd : ∀ c, MayDangleHonest (impls c))
    (p : Prog) :
    ∀ ks dead : List Nat,
      runDrops (behOf impls) p ks dead = runDrops (behOf (eraseMayDangle impls)) p ks dead
  | [], _ => rfl
  | k :: ks, dead => by
    simp only [runDrops]
    split
    · exact runDrops_eq_eraseMayDangle hmd p ks dead
    · cases p.locals[k]? with
      | none => exact runDrops_eq_eraseMayDangle hmd p ks dead
      | some e =>
        simp [dropVal_eq_eraseMayDangle hmd _ e.2, runDrops_eq_eraseMayDangle hmd p ks (k :: dead)]

/-- Under `MayDangleHonest`, replacing every `#[may_dangle]` impl by a `Drop`-less type does not
change the drop loop. -/
theorem dropSafe_eraseMayDangle_iff {impls : ImplTable} (hmd : ∀ c, MayDangleHonest (impls c))
    (ord : List Nat) (p : Prog) :
    DropSafe (eraseMayDangle impls) ord p ↔ DropSafe impls ord p := by
  simp only [DropSafe, runDrops_eq_eraseMayDangle hmd p ord []]

/-- `GlueVisible` of the erased table is exactly `OwnsDeclared` and `GlueVisible` of the original
table. -/
theorem glueVisible_eraseMayDangle_iff (impls : ImplTable) :
    (∀ c, GlueVisible (eraseMayDangle impls c)) ↔
      (∀ c, OwnsDeclared (impls c)) ∧ (∀ c, GlueVisible (impls c)) := by
  constructor
  · intro h
    refine ⟨fun c hD hM hE => ?_, fun c hD hE => ?_⟩
    · simpa [GlueVisible, eraseMayDangle, hD, hM, hE] using h c
    · simpa [GlueVisible, eraseMayDangle, hD, hE] using h c
  · rintro ⟨hown, hglue⟩ c
    unfold GlueVisible eraseMayDangle
    cases hD : (impls c).beh.hasDrop <;> cases hM : (impls c).decl.mayDangle
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      intro _ hE; exact hglue c hD hE
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      intro _ hE; exact hglue c hD hE
    · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      intro hF; rw [hD] at hF; cases hF
    · simp only [Bool.and_self, ↓reduceIte]
      intro _ hE; exact hown c hD hM hE

end Toy.Dropck
