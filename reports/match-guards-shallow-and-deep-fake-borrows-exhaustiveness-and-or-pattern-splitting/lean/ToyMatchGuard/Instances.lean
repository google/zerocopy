/-
Concrete instances: value domains, arm lists, definition examples, non-vacuity witnesses and
counterexamples for the freezing theorems.
-/
import ToyMatchGuard.Exhaust

namespace Toy.MatchGuard

/-! ### Value domains -/

/-- The values of the toy type `Option<bool>`. -/
def OptBoolDom (v : Val) : Prop := v = vNone ∨ v = vSome vFalse ∨ v = vSome vTrue

/-- The values of the toy type `&Option<bool>` (a reference modelled as a box). -/
def RefOptBoolDom (v : Val) : Prop :=
  v = .box vNone ∨ v = .box (vSome vFalse) ∨ v = .box (vSome vTrue)

/-- The values of the toy type `Box<bool>`. -/
def BoxBoolDom (v : Val) : Prop := v = .box vFalse ∨ v = .box vTrue

/-- The values of the toy type `Option<i32>` (integers unbounded in the toy). -/
def OptIntDom (v : Val) : Prop := v = vNone ∨ ∃ n : Int, v = vSome (.int n)

/-- The values of the toy struct `(Box<bool>, i32)`. -/
def PairBoxDom (v : Val) : Prop :=
  ∃ b n, (b = vFalse ∨ b = vTrue) ∧ v = .ctor 0 [.box b, .int n]

/-- The values of the toy struct `(bool, i32)`. -/
def PairBoolIntDom (v : Val) : Prop :=
  ∃ b n, (b = vFalse ∨ b = vTrue) ∧ v = .ctor 0 [b, .int n]

/-- The values of the toy type `Option<(Box<bool>, bool)>`. -/
def OptPairBoxBoolDom (v : Val) : Prop :=
  v = vNone ∨
    ∃ b c, (b = vFalse ∨ b = vTrue) ∧ (c = vFalse ∨ c = vTrue) ∧
      v = vSome (.ctor 0 [.box b, c])

/-- The values of the toy struct `(Option<bool>, Option<bool>)`. -/
def PairOptBoolDom (v : Val) : Prop :=
  ∃ x y, OptBoolDom x ∧ OptBoolDom y ∧ v = .ctor 0 [x, y]

/-! ### Arm lists -/

/-- Adapted from the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (),
Some(_) => () }` (where `x : &Option<i32>`): here `x : &Option<bool>`, and the last arm is split
into `Some(true)` and `Some(false)` so that a test runs after the guard. The guard reassigns the
reference `x`, a prefix of the switched place `*x`. -/
def reassignArms : List Arm :=
  [ { tests := [.switch [.deref] (.ctor 0)] },
    { tests := [.switch [.deref] (.ctor 1)],
      guard := some { writes := [([], fun _ _ => .box vNone)], cond := fun _ _ => false } },
    { tests := [.switch [.deref] (.ctor 1), .switch [.deref, .field 1 0] (.ctor 1)] },
    { tests := [.switch [.deref] (.ctor 1), .switch [.deref, .field 1 0] (.ctor 0)] } ]

/-- Toy form of the `Box<bool>` deref-pattern example `match b { deref!(true) => {},
_ if { *b = true; false } => {}, deref!(false) => {} }`. The guard writes `*b`, which lies
strictly inside the deref-pattern scrutinee `b`. -/
def boxBoolArms : List Arm :=
  [ { tests := [.derefSwitch [] [] (.ctor 1)] },
    { tests := [], guard := some { writes := [([.deref], fun _ _ => vTrue)], cond := fun _ _ => false } },
    { tests := [.derefSwitch [] [] (.ctor 0)] } ]

/-- `match x { None => .., Some(_) if { (x as Some).0 = 7; false } => .., Some(true) => ..,
Some(false) => .. }` on `x : Option<bool>`, where the guard writes an integer into a `bool`
field: an ill-typed write to a place that is switched on only by later arms. -/
def illTypedArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0], fun _ _ => .int 7)], cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 0)] } ]

/-- As `illTypedArms`, but the guard writes `true` (well-typed) into the field that later arms
switch on. -/
def laterTestedArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0], fun _ _ => vTrue)], cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 0)] } ]

/-- The value written by `*y += 1` for `y = &mut (x as Some).0` (unchanged if the field is
absent or not an integer). -/
def incrSomeField (v : Val) : Val :=
  match lookup v [.field 1 0] with
  | some (.int n) => .int (n + 1)
  | some w => w
  | none => .int 0

/-- Toy form of the allowed example in rustc's `FakeBorrowKind::Shallow` documentation:
`match x { Some(_) if { if let Some(ref mut y) = x { *y += 1 }; true } => {}, _ => {} }` on
`x : Option<i32>`. The guard increments the field inside the matched variant without touching
the discriminant (on `None` the toy write targets a nonexistent place and is skipped). -/
def shallowGuardArms : List Arm :=
  [ { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0], fun _ v => incrSomeField v)],
                      cond := fun _ _ => true } },
    { tests := [] } ]

/-- Deref patterns on the first field of a struct `(Box<bool>, i32)`, with a guard that writes
the second field (disjoint from the deref-pattern scrutinee). -/
def pairBoxArms : List Arm :=
  [ { tests := [.derefSwitch [.field 0 0] [] (.ctor 1)] },
    { tests := [], guard := some { writes := [([.field 0 1], fun _ _ => .int 5)], cond := fun _ _ => false } },
    { tests := [.derefSwitch [.field 0 0] [] (.ctor 0)] } ]

/-- `match x { None => .., Some(_) if { x = Some(5); false } => .., Some(_) => .. }` on
`x : Option<i32>`: the guard reassigns the scrutinee but keeps its variant. -/
def sameVariantArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([], fun _ _ => vSome (.int 5))], cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1)] } ]

/-- `match x { (true, _) if { x.1 = 9; false } => .., (true, _) => .., (false, _) => .. }` on
`x : (bool, i32)`: the guard writes the second field, disjoint from the switched first field. -/
def disjointSwitchWriteArms : List Arm :=
  [ { tests := [.switch [.field 0 0] (.ctor 1)],
      guard := some { writes := [([.field 0 1], fun _ _ => .int 9)], cond := fun _ _ => false } },
    { tests := [.switch [.field 0 0] (.ctor 1)] },
    { tests := [.switch [.field 0 0] (.ctor 0)] } ]

/-- A match on `x : Option<(Box<bool>, bool)>` with switches, deref-pattern tests and a guard:
`None`, `Some((deref!(true), _))`, `Some(_) if { (x as Some).0.1 = true; false }`,
`Some((deref!(false), _))`. The guard writes strictly inside the switched place `x` and is
disjoint from the deref-pattern scrutinee `(x as Some).0.0`. -/
def mixedStaticArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0, .field 0 1], fun _ _ => vTrue)],
                      cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 0)] } ]

/-- As `mixedStaticArms`, but the last arm is split on the second field, so the place
`(x as Some).0.1` that the guard writes is switched on by the two arms after the guard (and by no
arm up to the guard's own). -/
def mixedLaterTestedArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0, .field 0 1], fun _ _ => vTrue)],
                      cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 0),
                .switch [.field 1 0, .field 0 1] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 0),
                .switch [.field 1 0, .field 0 1] (.ctor 0)] } ]

/-- The value written by `x.1 = Some(b)` for the binding `b` named `0`; when `b` is unbound
(`none`, i.e. the bound place does not exist) it writes the integer `-1`. -/
def writeBoundOptBool (env : Env) (_ : Val) : Val :=
  match env.lookup 0 with
  | some (some b) => vSome b
  | _ => .int (-1)

/-- `match x { (None, _) => .., (Some(b), _) if { x.1 = Some(b); false } => .., (Some(_), None) => ..,
(Some(_), Some(true)) => .., (Some(_), Some(false)) => .. }` on
`x : (Option<bool>, Option<bool>)`: the guard writes a value computed from its pattern binding. -/
def copyBoundFieldArms : List Arm :=
  [ { tests := [.switch [.field 0 0] (.ctor 0)] },
    { tests := [.switch [.field 0 0] (.ctor 1)],
      binds := [(0, [.field 0 0, .field 1 0])],
      guard := some { writes := [([.field 0 1], writeBoundOptBool)], cond := fun _ _ => false } },
    { tests := [.switch [.field 0 0] (.ctor 1), .switch [.field 0 1] (.ctor 0)] },
    { tests := [.switch [.field 0 0] (.ctor 1), .switch [.field 0 1] (.ctor 1),
                .switch [.field 0 1, .field 1 0] (.ctor 1)] },
    { tests := [.switch [.field 0 0] (.ctor 1), .switch [.field 0 1] (.ctor 1),
                .switch [.field 0 1, .field 1 0] (.ctor 0)] } ]

/-! ### Exhaustiveness and domain facts -/

theorem reassignArms_exhaustive : Exhaustive RefOptBoolDom reassignArms := by
  intro v hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨reassignArms[0], by unfold reassignArms; simp, rfl, by decide⟩
  · exact ⟨reassignArms[3], by unfold reassignArms; simp, rfl, by decide⟩
  · exact ⟨reassignArms[2], by unfold reassignArms; simp, rfl, by decide⟩

theorem reassignArms_guardsPreserveDom : GuardsPreserveDom RefOptBoolDom reassignArms := by
  intro a ha g hg v _ _
  unfold reassignArms at ha
  simp at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp at hg
  subst hg
  exact Or.inl rfl

theorem boxBoolArms_exhaustive : Exhaustive BoxBoolDom boxBoolArms := by
  intro v hv
  rcases hv with rfl | rfl
  · exact ⟨boxBoolArms[2], by unfold boxBoolArms; simp, rfl, by decide⟩
  · exact ⟨boxBoolArms[0], by unfold boxBoolArms; simp, rfl, by decide⟩

theorem boxBoolArms_guardsPreserveDom : GuardsPreserveDom BoxBoolDom boxBoolArms := by
  intro a ha g hg v hv _
  unfold boxBoolArms at ha
  simp at ha
  rcases ha with rfl | rfl | rfl <;> simp at hg
  subst hg
  rcases hv with rfl | rfl <;> exact Or.inr rfl

theorem optBool_arms_exhaustive (arms : List Arm) (h0 : arms[0]? = some (illTypedArms[0]))
    (h2 : arms[2]? = some (illTypedArms[2])) (h3 : arms[3]? = some (illTypedArms[3])) :
    Exhaustive OptBoolDom arms := by
  intro v hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨_, List.mem_of_getElem? h0, rfl, by decide⟩
  · exact ⟨_, List.mem_of_getElem? h3, rfl, by decide⟩
  · exact ⟨_, List.mem_of_getElem? h2, rfl, by decide⟩

theorem illTypedArms_exhaustive : Exhaustive OptBoolDom illTypedArms :=
  optBool_arms_exhaustive _ rfl rfl rfl

theorem laterTestedArms_exhaustive : Exhaustive OptBoolDom laterTestedArms :=
  optBool_arms_exhaustive _ rfl rfl rfl

theorem laterTestedArms_guardsPreserveDom : GuardsPreserveDom OptBoolDom laterTestedArms := by
  intro a ha g hg v hv _
  unfold laterTestedArms at ha
  simp at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp at hg
  subst hg
  rcases hv with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)

theorem illTypedArms_not_guardsPreserveDom : ¬ GuardsPreserveDom OptBoolDom illTypedArms := by
  intro h
  have := h illTypedArms[1] (by unfold illTypedArms; simp) _ rfl (vSome vTrue)
    (Or.inr (Or.inr rfl)) (by decide)
  unfold OptBoolDom at this
  revert this
  decide

theorem shallowGuardArms_exhaustive : Exhaustive OptIntDom shallowGuardArms := by
  intro v _
  exact ⟨shallowGuardArms[1], by unfold shallowGuardArms; simp, rfl, rfl⟩

theorem pairBoxArms_exhaustive : Exhaustive PairBoxDom pairBoxArms := by
  intro v hv
  obtain ⟨b, n, hb, rfl⟩ := hv
  rcases hb with rfl | rfl
  · exact ⟨pairBoxArms[2], by unfold pairBoxArms; simp, rfl, rfl⟩
  · exact ⟨pairBoxArms[0], by unfold pairBoxArms; simp, rfl, rfl⟩

theorem sameVariantArms_exhaustive : Exhaustive OptIntDom sameVariantArms := by
  intro v hv
  rcases hv with rfl | ⟨n, rfl⟩
  · exact ⟨sameVariantArms[0], by unfold sameVariantArms; simp, rfl, rfl⟩
  · exact ⟨sameVariantArms[2], by unfold sameVariantArms; simp, rfl, rfl⟩

theorem disjointSwitchWriteArms_exhaustive : Exhaustive PairBoolIntDom disjointSwitchWriteArms := by
  intro v hv
  obtain ⟨b, n, hb, rfl⟩ := hv
  rcases hb with rfl | rfl
  · exact ⟨disjointSwitchWriteArms[2], by unfold disjointSwitchWriteArms; simp, rfl, rfl⟩
  · exact ⟨disjointSwitchWriteArms[1], by unfold disjointSwitchWriteArms; simp, rfl, rfl⟩

theorem mixedStaticArms_exhaustive : Exhaustive OptPairBoxBoolDom mixedStaticArms := by
  intro v hv
  rcases hv with rfl | ⟨b, c, hb, _, rfl⟩
  · exact ⟨mixedStaticArms[0], by unfold mixedStaticArms; simp, rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact ⟨mixedStaticArms[3], by unfold mixedStaticArms; simp, rfl, rfl⟩
    · exact ⟨mixedStaticArms[1], by unfold mixedStaticArms; simp, rfl, rfl⟩

theorem mixedLaterTestedArms_exhaustive : Exhaustive OptPairBoxBoolDom mixedLaterTestedArms := by
  intro v hv
  rcases hv with rfl | ⟨b, c, hb, hc, rfl⟩
  · exact ⟨mixedLaterTestedArms[0], by unfold mixedLaterTestedArms; simp, rfl, rfl⟩
  · rcases hb with rfl | rfl
    · rcases hc with rfl | rfl
      · exact ⟨mixedLaterTestedArms[4], by unfold mixedLaterTestedArms; simp, rfl, rfl⟩
      · exact ⟨mixedLaterTestedArms[3], by unfold mixedLaterTestedArms; simp, rfl, rfl⟩
    · exact ⟨mixedLaterTestedArms[1], by unfold mixedLaterTestedArms; simp, rfl, rfl⟩

theorem mixedLaterTestedArms_guardsPreserveDom :
    GuardsPreserveDom OptPairBoxBoolDom mixedLaterTestedArms := by
  intro a ha g hg v hv _
  unfold mixedLaterTestedArms at ha
  simp at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp at hg
  subst hg
  rcases hv with rfl | ⟨b, c, hb, hc, rfl⟩
  · exact Or.inl rfl
  · rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
    · exact Or.inr ⟨vFalse, vTrue, Or.inl rfl, Or.inr rfl, rfl⟩
    · exact Or.inr ⟨vFalse, vTrue, Or.inl rfl, Or.inr rfl, rfl⟩
    · exact Or.inr ⟨vTrue, vTrue, Or.inr rfl, Or.inr rfl, rfl⟩
    · exact Or.inr ⟨vTrue, vTrue, Or.inr rfl, Or.inr rfl, rfl⟩

/-! ### Definition examples -/

/-- Negative example (`Exhaustive`): without its last arm, `reassignArms` misses
`&Some(false)`. -/
theorem reassignArms_take3_not_exhaustive : ¬ Exhaustive RefOptBoolDom (reassignArms.take 3) := by
  intro h
  obtain ⟨a, ha, hg, hm⟩ := h (.box (vSome vFalse)) (Or.inr (Or.inl rfl))
  unfold reassignArms at ha
  simp at ha
  rcases ha with rfl | rfl | rfl
  · revert hm; decide
  · simp at hg
  · revert hm; decide

/-- Negative example (`Exhaustive`): a guarded arm does not count, so
`[Some(_) if { true } => .., None => ..]` is not exhaustive on `Option<i32>`. -/
theorem guarded_arm_not_counted :
    ¬ Exhaustive OptIntDom
      [ { tests := [.switch [] (.ctor 1)], guard := some { writes := [], cond := fun _ _ => true } },
        { tests := [.switch [] (.ctor 0)] } ] := by
  intro h
  obtain ⟨a, ha, hg, hm⟩ := h (vSome (.int 0)) (Or.inr ⟨0, rfl⟩)
  simp at ha
  rcases ha with rfl | rfl
  · simp at hg
  · revert hm; decide

/-- Positive example (`ShallowFrozenAll`): writing inside the matched variant. -/
theorem shallowGuardArms_shallowFrozenAll : ShallowFrozenAll shallowGuardArms := by decide

/-- Negative example (`ShallowFrozenAll`): reassigning the reference `x` while `*x` is switched. -/
theorem reassignArms_not_shallowFrozenAll : ¬ ShallowFrozenAll reassignArms := by decide

/-- Positive example (`DeepFrozenAll`): the guard writes a place disjoint from the deref-pattern
scrutinee. -/
theorem pairBoxArms_deepFrozenAll : DeepFrozenAll pairBoxArms := by decide

/-- Negative example (`DeepFrozenAll`): the guard writes inside the deref-pattern scrutinee. -/
theorem boxBoolArms_not_deepFrozenAll : ¬ DeepFrozenAll boxBoolArms := by decide

/-- Positive example (`ShallowFrozenDerefAll`): a write strictly inside a deref-pattern
scrutinee does not shallow-conflict with it. -/
theorem boxBoolArms_shallowFrozenDerefAll : ShallowFrozenDerefAll boxBoolArms := by decide

/-- Negative example (`ShallowFrozenDerefAll`): reassigning the deref-pattern scrutinee itself. -/
theorem reassignBox_not_shallowFrozenDerefAll :
    ¬ ShallowFrozenDerefAll
      [ { tests := [.derefSwitch [] [] (.ctor 1)] },
        { tests := [], guard := some { writes := [([], fun _ _ => .box vTrue)], cond := fun _ _ => false } } ] := by
  decide

/-- Positive example (`DeepFrozenSwitchAll`): `disjointSwitchWriteArms` has a guard write and a
switched place, and the write is disjoint from every switched place. -/
theorem disjointSwitchWriteArms_deepFrozenSwitchAll :
    DeepFrozenSwitchAll disjointSwitchWriteArms ∧
      disjointSwitchWriteArms.map Arm.guardWrites = [[[.field 0 1]], [], []] ∧
      disjointSwitchWriteArms.map Arm.switchPlaces = [[[.field 0 0]], [[.field 0 0]], [[.field 0 0]]] := by
  decide

/-- Negative example (`DeepFrozenSwitchAll`): writing inside the matched variant. -/
theorem shallowGuardArms_not_deepFrozenSwitchAll : ¬ DeepFrozenSwitchAll shallowGuardArms := by
  decide

/-- Positive example (`ShallowFrozenBefore`): the guard writes a place switched on by later arms and
by no arm up to its own. -/
theorem laterTestedArms_shallowFrozenBefore : ShallowFrozenBefore laterTestedArms := by decide

/-- Negative example (`ShallowFrozenBefore`): reassigning `x` while `*x` was switched before. -/
theorem reassignArms_not_shallowFrozenBefore : ¬ ShallowFrozenBefore reassignArms := by decide

/-- Positive example (`DeepFrozenBefore`). -/
theorem pairBoxArms_deepFrozenBefore : DeepFrozenBefore pairBoxArms := by decide

/-- Negative example (`DeepFrozenBefore`). -/
theorem boxBoolArms_not_deepFrozenBefore : ¬ DeepFrozenBefore boxBoolArms := by decide

/-- Positive example (`GuardsPreserveDom`) with a guard that reads its pattern binding:
`copyBoundFieldArms` satisfies `GuardsPreserveDom PairOptBoolDom`; and from `(None, None)`, on
which the guarded arm does not match (so its binding is unbound), running that guard's writes
would leave `PairOptBoolDom`, which `GuardsPreserveDom` does not forbid. -/
theorem copyBoundFieldArms_guardsPreserveDom_and_unmatched_write_leaves_dom :
    GuardsPreserveDom PairOptBoolDom copyBoundFieldArms ∧
      PairOptBoolDom (.ctor 0 [vNone, vNone]) ∧
      ¬ PairOptBoolDom
        (runWrites (bindEnv (.ctor 0 [vNone, vNone]) [(0, [.field 0 0, .field 1 0])])
          (.ctor 0 [vNone, vNone]) [([.field 0 1], writeBoundOptBool)]) := by
  refine ⟨?_, ⟨vNone, vNone, Or.inl rfl, Or.inl rfl, rfl⟩, ?_⟩
  · intro a ha g hg v hv hm
    obtain ⟨x, y, hx, _, rfl⟩ := hv
    unfold copyBoundFieldArms at ha
    simp at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp at hg
    subst hg
    rcases hx with rfl | rfl | rfl
    · cases hm
    · exact ⟨vSome vFalse, vSome vFalse, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨vSome vTrue, vSome vTrue, Or.inr (Or.inr rfl), Or.inr (Or.inr rfl), rfl⟩
  · intro h
    obtain ⟨x, y, _, hy, heq⟩ := h
    simp [runWrites, writeOrSkip, write, step, setChild, bindEnv, lookup, writeBoundOptBool] at heq
    obtain ⟨_, rfl⟩ := heq
    rcases hy with hy | hy | hy <;> cases hy

/-- Positive example (`NoDerefPatterns`). -/
theorem reassignArms_noDerefPatterns : NoDerefPatterns reassignArms := by decide

/-- Negative example (`NoDerefPatterns`). -/
theorem boxBoolArms_not_noDerefPatterns : ¬ NoDerefPatterns boxBoolArms := by decide

/-- Positive example (`runMatch`): on `&None`, `reassignArms` selects arm `0`. -/
theorem runMatch_reassignArms_none : (runMatch reassignArms (.box vNone)).selected = some 0 := by
  decide

/-- Example (`runMatch`): on `Some(false)`, `laterTestedArms` selects arm `2` (`Some(true)`),
because the guard of arm `1` wrote `true` into the field before arm `2` read it. -/
theorem runMatch_laterTestedArms_someFalse :
    (runMatch laterTestedArms (vSome vFalse)).selected = some 2 := by decide

/-! ### Counterexamples and non-vacuity witnesses -/

/-- **Counterexample (shallow freezing, static form).** `reassignArms` has no deref-pattern test,
is exhaustive on `RefOptBoolDom`, satisfies `DeepFrozenAll` (vacuously), violates
`ShallowFrozenAll`, and on `&Some(true)`, a value in the domain, its lowered execution reaches
`Unreachable`. -/
theorem reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable :
    NoDerefPatterns reassignArms ∧ Exhaustive RefOptBoolDom reassignArms ∧
      DeepFrozenAll reassignArms ∧ ¬ ShallowFrozenAll reassignArms ∧
      RefOptBoolDom (.box (vSome vTrue)) ∧
      (runMatch reassignArms (.box (vSome vTrue))).reachesUnreachable = true :=
  ⟨by decide, reassignArms_exhaustive, by decide, by decide, Or.inr (Or.inr rfl), by decide⟩

/-- **Counterexample (shallow freezing, per-guard form).** `reassignArms` is exhaustive on
`RefOptBoolDom`, its guard keeps memory in the domain, it satisfies `DeepFrozenBefore`, violates
`ShallowFrozenBefore`, and reaches `Unreachable` on `&Some(true)`. -/
theorem reassignArms_exhaustive_guardsPreserveDom_deepFrozenBefore_and_reaches_unreachable :
    Exhaustive RefOptBoolDom reassignArms ∧ GuardsPreserveDom RefOptBoolDom reassignArms ∧
      DeepFrozenBefore reassignArms ∧ ¬ ShallowFrozenBefore reassignArms ∧
      RefOptBoolDom (.box (vSome vTrue)) ∧
      (runMatch reassignArms (.box (vSome vTrue))).reachesUnreachable = true :=
  ⟨reassignArms_exhaustive, reassignArms_guardsPreserveDom, by decide, by decide,
    Or.inr (Or.inr rfl), by decide⟩

/-- **Counterexample (deep freezing of deref-pattern scrutinees, static form).** `boxBoolArms` is
exhaustive on `BoxBoolDom`, satisfies `ShallowFrozenAll` and even shallow freezing of its
deref-pattern scrutinee (`ShallowFrozenDerefAll`), violates `DeepFrozenAll`, and on `Box(false)`
its lowered execution reaches `Unreachable`. -/
theorem boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable :
    Exhaustive BoxBoolDom boxBoolArms ∧ ShallowFrozenAll boxBoolArms ∧
      ShallowFrozenDerefAll boxBoolArms ∧ ¬ DeepFrozenAll boxBoolArms ∧
      BoxBoolDom (.box vFalse) ∧
      (runMatch boxBoolArms (.box vFalse)).reachesUnreachable = true :=
  ⟨boxBoolArms_exhaustive, by decide, by decide, by decide, Or.inl rfl, by decide⟩

/-- **Counterexample (deep freezing, per-guard form).** `boxBoolArms` is exhaustive on
`BoxBoolDom`, its guard keeps memory in the domain, it satisfies `ShallowFrozenBefore`, violates
`DeepFrozenBefore`, and reaches `Unreachable` on `Box(false)`. -/
theorem boxBoolArms_exhaustive_guardsPreserveDom_shallowFrozenBefore_and_reaches_unreachable :
    Exhaustive BoxBoolDom boxBoolArms ∧ GuardsPreserveDom BoxBoolDom boxBoolArms ∧
      ShallowFrozenBefore boxBoolArms ∧ ¬ DeepFrozenBefore boxBoolArms ∧
      BoxBoolDom (.box vFalse) ∧
      (runMatch boxBoolArms (.box vFalse)).reachesUnreachable = true :=
  ⟨boxBoolArms_exhaustive, boxBoolArms_guardsPreserveDom, by decide, by decide, Or.inl rfl,
    by decide⟩

/-- **Counterexample (no deref patterns).** `boxBoolArms` has a deref-pattern test, is
exhaustive on `BoxBoolDom`, satisfies `ShallowFrozenAll`, and reaches `Unreachable` on
`Box(false)`. -/
theorem boxBoolArms_not_noDerefPatterns_exhaustive_shallowFrozenAll_and_reaches_unreachable :
    ¬ NoDerefPatterns boxBoolArms ∧ Exhaustive BoxBoolDom boxBoolArms ∧
      ShallowFrozenAll boxBoolArms ∧ BoxBoolDom (.box vFalse) ∧
      (runMatch boxBoolArms (.box vFalse)).reachesUnreachable = true :=
  ⟨by decide, boxBoolArms_exhaustive, by decide, Or.inl rfl, by decide⟩

/-- **Counterexample (well-typed guards, per-guard form).** `illTypedArms` is exhaustive on
`OptBoolDom` and satisfies `ShallowFrozenBefore` and `DeepFrozenBefore`, its guard does not keep
memory in the domain, and on `Some(true)` its lowered execution reaches `Unreachable`. -/
theorem illTypedArms_exhaustive_frozenBefore_and_reaches_unreachable :
    Exhaustive OptBoolDom illTypedArms ∧ ShallowFrozenBefore illTypedArms ∧
      DeepFrozenBefore illTypedArms ∧ ¬ GuardsPreserveDom OptBoolDom illTypedArms ∧
      OptBoolDom (vSome vTrue) ∧
      (runMatch illTypedArms (vSome vTrue)).reachesUnreachable = true :=
  ⟨illTypedArms_exhaustive, by decide, by decide, illTypedArms_not_guardsPreserveDom,
    Or.inr (Or.inr rfl), by decide⟩

/-- `illTypedArms` violates static shallow freezing (its guard writes a place that a later arm
switches on), so it is not a counterexample to the static theorem. -/
theorem illTypedArms_not_shallowFrozenAll : ¬ ShallowFrozenAll illTypedArms := by decide

/-- **Non-vacuity (static theorem, joint).** `mixedStaticArms` is exhaustive on
`OptPairBoxBoolDom`, satisfies `ShallowFrozenAll` and `DeepFrozenAll`, and `OptPairBoxBoolDom`
is inhabited; its arms switch on `[]`, deref-switch on `[.field 1 0, .field 0 0]`, and its guard
writes `[.field 1 0, .field 0 1]`, which lies strictly inside the switched place `[]` (so
`DeepFrozenSwitchAll` fails). -/
theorem mixedStaticArms_satisfy_static_hypotheses :
    Exhaustive OptPairBoxBoolDom mixedStaticArms ∧ ShallowFrozenAll mixedStaticArms ∧
      DeepFrozenAll mixedStaticArms ∧ OptPairBoxBoolDom (vSome (.ctor 0 [.box vFalse, vFalse])) ∧
      mixedStaticArms.map Arm.switchPlaces = [[[]], [[]], [[]], [[]]] ∧
      mixedStaticArms.map Arm.derefScrutinees =
        [[], [[.field 1 0, .field 0 0]], [], [[.field 1 0, .field 0 0]]] ∧
      mixedStaticArms.map Arm.guardWrites = [[], [], [[.field 1 0, .field 0 1]], []] ∧
      ¬ DeepFrozenSwitchAll mixedStaticArms :=
  ⟨mixedStaticArms_exhaustive, by decide, by decide,
    Or.inr ⟨vFalse, vFalse, Or.inl rfl, Or.inl rfl, rfl⟩, by decide, by decide, by decide, by decide⟩

/-- **Non-vacuity (deref-free static theorem, with a guard write).** `shallowGuardArms` has no
deref-pattern test, is exhaustive on `OptIntDom`, satisfies `ShallowFrozenAll` and
`DeepFrozenAll`, and `OptIntDom` is inhabited. -/
theorem shallowGuardArms_satisfy_static_hypotheses :
    NoDerefPatterns shallowGuardArms ∧ Exhaustive OptIntDom shallowGuardArms ∧
      ShallowFrozenAll shallowGuardArms ∧ DeepFrozenAll shallowGuardArms ∧
      OptIntDom (vSome (.int 0)) :=
  ⟨by decide, shallowGuardArms_exhaustive, by decide, by decide, Or.inr ⟨0, rfl⟩⟩

/-- **Non-vacuity (per-guard theorem, joint) and refinement witness.** `mixedLaterTestedArms` is
exhaustive on `OptPairBoxBoolDom`, satisfies `GuardsPreserveDom`, `ShallowFrozenBefore` and
`DeepFrozenBefore`, violates `ShallowFrozenAll` (its guard writes a place switched on by later
arms), and `OptPairBoxBoolDom` is inhabited; the arms up to the guard's own switch on `[]` and
deref-switch on `[.field 1 0, .field 0 0]`, and the guard writes `[.field 1 0, .field 0 1]`. -/
theorem mixedLaterTestedArms_satisfy_frozenBefore_hypotheses_and_not_shallowFrozenAll :
    Exhaustive OptPairBoxBoolDom mixedLaterTestedArms ∧
      GuardsPreserveDom OptPairBoxBoolDom mixedLaterTestedArms ∧
      ShallowFrozenBefore mixedLaterTestedArms ∧ DeepFrozenBefore mixedLaterTestedArms ∧
      ¬ ShallowFrozenAll mixedLaterTestedArms ∧
      OptPairBoxBoolDom (vSome (.ctor 0 [.box vFalse, vFalse])) ∧
      (mixedLaterTestedArms.take 3).map Arm.switchPlaces = [[[]], [[]], [[]]] ∧
      (mixedLaterTestedArms.take 3).map Arm.derefScrutinees = [[], [[.field 1 0, .field 0 0]], []] ∧
      mixedLaterTestedArms.map Arm.guardWrites = [[], [], [[.field 1 0, .field 0 1]], [], []] :=
  ⟨mixedLaterTestedArms_exhaustive, mixedLaterTestedArms_guardsPreserveDom, by decide, by decide,
    by decide, Or.inr ⟨vFalse, vFalse, Or.inl rfl, Or.inl rfl, rfl⟩, by decide, by decide, by decide⟩

/-- **Deep freezing of switched places is strictly stronger than shallow freezing.** For every arm
list, `DeepFrozenSwitchAll` implies `ShallowFrozenAll`; and `shallowGuardArms` has no
deref-pattern test, is exhaustive on `OptIntDom`, satisfies `ShallowFrozenAll`, and violates
`DeepFrozenSwitchAll` (its guard writes strictly inside a switched place). -/
theorem shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms :
    (∀ arms, DeepFrozenSwitchAll arms → ShallowFrozenAll arms) ∧
      NoDerefPatterns shallowGuardArms ∧ Exhaustive OptIntDom shallowGuardArms ∧
      ShallowFrozenAll shallowGuardArms ∧ ¬ DeepFrozenSwitchAll shallowGuardArms :=
  ⟨shallowFrozenAll_of_deepFrozenSwitchAll, by decide, shallowGuardArms_exhaustive, by decide,
    by decide⟩

/-! ### Further counterexamples (exhaustiveness and domain hypotheses) -/

/-- The values of the toy type `bool`. -/
def BoolDom (v : Val) : Prop := v = vFalse ∨ v = vTrue

/-- `match x { None => .., Some(true) => .. }` on `x : Option<bool>`: misses `Some(false)`. -/
def missingArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 1)] } ]

/-- `match x { false => .., true => .. }` on `x : bool`, without guards. -/
def boolArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] }, { tests := [.switch [] (.ctor 1)] } ]

/-- **Counterexample (exhaustiveness).** `missingArms` has no guard and no deref-pattern test, so
it satisfies every freezing hypothesis, `GuardsPreserveDom` and the borrow check vacuously; it is
not exhaustive on `OptBoolDom`, and on `Some(false)`, a value in the domain, its lowered
execution reaches `Unreachable`. -/
theorem missingArms_frozen_not_exhaustive_and_reaches_unreachable :
    ¬ Exhaustive OptBoolDom missingArms ∧ NoDerefPatterns missingArms ∧
      ShallowFrozenAll missingArms ∧ DeepFrozenAll missingArms ∧
      GuardsPreserveDom OptBoolDom missingArms ∧ ShallowFrozenBefore missingArms ∧
      DeepFrozenBefore missingArms ∧ OptBoolDom (vSome vFalse) ∧
      (runMatch missingArms (vSome vFalse)).reachesUnreachable = true := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, Or.inr (Or.inl rfl),
    by decide⟩
  · intro h
    obtain ⟨a, ha, _, hm⟩ := h (vSome vFalse) (Or.inr (Or.inl rfl))
    unfold missingArms at ha
    simp at ha
    rcases ha with rfl | rfl <;> revert hm <;> decide
  · intro a ha g hg
    unfold missingArms at ha
    simp at ha
    rcases ha with rfl | rfl <;> simp at hg

theorem boolArms_exhaustive : Exhaustive BoolDom boolArms := by
  intro v hv
  rcases hv with rfl | rfl
  · exact ⟨boolArms[0], by unfold boolArms; simp, rfl, by decide⟩
  · exact ⟨boolArms[1], by unfold boolArms; simp, rfl, by decide⟩

/-- **Counterexample (domain membership of the scrutinee).** `boolArms` has no guard and no
deref-pattern test and is exhaustive on `BoolDom`; on the integer `0`, which is not in
`BoolDom`, its lowered execution reaches `Unreachable`. -/
theorem boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom :
    Exhaustive BoolDom boolArms ∧ NoDerefPatterns boolArms ∧ ShallowFrozenAll boolArms ∧
      DeepFrozenAll boolArms ∧ GuardsPreserveDom BoolDom boolArms ∧
      ShallowFrozenBefore boolArms ∧ DeepFrozenBefore boolArms ∧ ¬ BoolDom (.int 0) ∧
      (runMatch boolArms (.int 0)).reachesUnreachable = true := by
  refine ⟨boolArms_exhaustive, by decide, by decide, by decide, ?_, by decide, by decide, ?_,
    by decide⟩
  · intro a ha g hg
    unfold boolArms at ha
    simp at ha
    rcases ha with rfl | rfl <;> simp at hg
  · unfold BoolDom; decide

/-- The literal shape of the E0510 example, `match *x { None => (), Some(_) if { x = &None;
false } => (), Some(_) => () }` on `x : &Option<bool>`: the last arm runs no test after the
guard. -/
def e0510Arms : List Arm := reassignArms.take 3 |>.set 2 { tests := [.switch [.deref] (.ctor 1)] }

/-- On `&Some(true)`, the toy lowering of the literal E0510 shape does not reach `Unreachable`: it
selects the last arm from the recorded variant, with memory `&None` (the toy does not model the
arm then running on a value whose variant changed). -/
theorem e0510Arms_selects_last_arm_with_changed_memory :
    ¬ ShallowFrozenAll e0510Arms ∧
      (runMatch e0510Arms (.box (vSome vTrue))).selected = some 2 ∧
      (match runMatch e0510Arms (.box (vSome vTrue)) with
        | .arm _ _ mem => decide (mem = .box vNone)
        | .unreachable _ => false) = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- Example (`runMatch`): on `Some(41)`, `shallowGuardArms` selects arm `0`, and its guard has
incremented the field. -/
theorem runMatch_shallowGuardArms :
    (match runMatch shallowGuardArms (vSome (.int 41)) with
      | .arm i _ mem => decide (i = 0 ∧ mem = vSome (.int 42))
      | .unreachable _ => false) = true := by decide

end Toy.MatchGuard
