/-
Toy values, places, reads and writes.

These are definitions of a toy model. They are meant to capture the parts of a Rust
scrutinee that a `match` lowering inspects: enum variants with fields, boxes that can be
dereferenced, and places (paths built from variant-field projections and dereferences).
They are not Rust's definitions.
-/

namespace Toy.MatchGuard

/-- Toy runtime values.
* `int n`: an integer scalar.
* `ctor tag fields`: an enum value whose active variant is `tag`, with the given fields
  (a struct is an enum with one variant; `bool` is `ctor 0 []` / `ctor 1 []`;
  `Option T` is `ctor 0 []` (`None`) / `ctor 1 [x]` (`Some x`)).
* `box v`: a box (or reference) owning the pointee `v`. -/
inductive Val where
  | int (n : Int)
  | ctor (tag : Nat) (fields : List Val)
  | box (v : Val)

mutual
/-- Decidable equality on toy values (written by hand because the derive handler does not
apply to this nested inductive). -/
def Val.decEq : (a b : Val) → Decidable (a = b)
  | .int n, .int m =>
    if h : n = m then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .ctor t fs, .ctor u gs =>
    if h : t = u then
      match Val.decEqList fs gs with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse (by intro e; cases e; exact h' rfl)
    else isFalse (by intro e; cases e; exact h rfl)
  | .box a, .box b =>
    match Val.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .int _, .ctor _ _ => isFalse (by intro e; cases e)
  | .int _, .box _ => isFalse (by intro e; cases e)
  | .ctor _ _, .int _ => isFalse (by intro e; cases e)
  | .ctor _ _, .box _ => isFalse (by intro e; cases e)
  | .box _, .int _ => isFalse (by intro e; cases e)
  | .box _, .ctor _ _ => isFalse (by intro e; cases e)
/-- Decidable equality on lists of toy values. -/
def Val.decEqList : (as bs : List Val) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Val.decEq a b, Val.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h' => isFalse (by intro e; cases e; exact h' rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq Val := Val.decEq

/-- Toy `false`. -/
def vFalse : Val := .ctor 0 []
/-- Toy `true`. -/
def vTrue : Val := .ctor 1 []
/-- Toy `None`. -/
def vNone : Val := .ctor 0 []
/-- Toy `Some x`. -/
def vSome (x : Val) : Val := .ctor 1 [x]

/-- One projection step of a place.
* `field variant idx`: the field `idx` of variant `variant` (Rust's `(_ as variant).idx`);
  it exists only while `variant` is the active variant.
* `deref`: the pointee of a box (Rust's `*_`). -/
inductive Proj where
  | field (variant idx : Nat)
  | deref
  deriving DecidableEq, Repr

/-- A place: a path of projections from the scrutinee root. `[]` is the scrutinee itself;
`w <+: p` (list prefix) means that `p` lies inside `w` (or equals it). -/
abbrev Place := List Proj

/-- One projection step; `none` if the projection does not exist in this value
(wrong variant, missing field, or not a box). -/
def step : Val → Proj → Option Val
  | .ctor t fs, .field k i => if t = k then fs[i]? else none
  | .box v, .deref => some v
  | _, _ => none

/-- The value stored at a place, or `none` if the place does not exist in this value. -/
def lookup : Val → Place → Option Val
  | v, [] => some v
  | v, p :: ps =>
    match step v p with
    | some c => lookup c ps
    | none => none

/-- Replaces the child selected by one projection; `none` if that child does not exist. -/
def setChild : Val → Proj → Val → Option Val
  | .ctor t fs, .field k i, c => if t = k ∧ i < fs.length then some (.ctor t (fs.set i c)) else none
  | .box _, .deref, c => some (.box c)
  | _, _, _ => none

/-- Writes `new` at place `w`; `none` if `w` does not exist in `v`. -/
def write : Val → Place → Val → Option Val
  | _, [], new => some new
  | v, p :: ps, new =>
    match step v p with
    | none => none
    | some c =>
      match write c ps new with
      | none => none
      | some c' => setChild v p c'

/-- The toy's write statement: a write to a place that does not exist leaves the value
unchanged (Rust code would first have to establish the variant, e.g. with `if let`). -/
def writeOrSkip (v : Val) (w : Place) (new : Val) : Val := (write v w new).getD v

/-- What a switch on a place reads: the integer, the active variant, or "a box". -/
inductive Head where
  | int (n : Int)
  | ctor (tag : Nat)
  | box
  deriving DecidableEq, Repr

/-- The head of a value. -/
def Val.head : Val → Head
  | .int n => .int n
  | .ctor t _ => .ctor t
  | .box _ => .box

/-- The head at a place (`none` if the place does not exist). -/
def headAt (v : Val) (p : Place) : Option Head := (lookup v p).map Val.head

/-! ### Examples -/

/-- Positive example (`lookup`): the place `(*x as Some).0` exists in `Box(Some(true))`. -/
theorem lookup_example_some :
    lookup (.box (vSome vTrue)) [.deref, .field 1 0] = some vTrue := by decide

/-- Negative example (`lookup`): the place `(*x as Some).0` does not exist in `Box(None)`. -/
theorem lookup_example_none :
    lookup (.box vNone) [.deref, .field 1 0] = none := by decide

/-- Positive example (`writeOrSkip`): writing inside the active variant. -/
theorem writeOrSkip_example_inside :
    writeOrSkip (vSome (.int 0)) [.field 1 0] (.int 1) = vSome (.int 1) := by decide

/-- Negative example (`writeOrSkip`): a write to a field of an inactive variant is skipped. -/
theorem writeOrSkip_example_skip :
    writeOrSkip vNone [.field 1 0] (.int 1) = vNone := by decide

/-- Positive example (`headAt`): the head of `Some(_)` is variant `1`. -/
theorem headAt_example : headAt (vSome (.int 3)) [] = some (.ctor 1) := by decide

/-- Negative example (`headAt`): a nonexistent place has no head. -/
theorem headAt_example_none : headAt vNone [.field 1 0] = none := by decide

/-! ### Frame lemmas for writes -/

theorem setChild_head {v c v' : Val} {a : Proj} (h : setChild v a c = some v') :
    v'.head = v.head := by
  cases v <;> cases a <;> simp [setChild] at h
  · rename_i t fs k i
    obtain ⟨⟨rfl, _⟩, rfl⟩ := h
    rfl
  · subst h; rfl

theorem step_setChild_same {v c v' : Val} {a : Proj} (h : setChild v a c = some v') :
    step v' a = some c := by
  cases v <;> cases a <;> simp [setChild] at h
  · rename_i t fs k i
    obtain ⟨⟨rfl, hi⟩, rfl⟩ := h
    simp [step, hi]
  · subst h; rfl

theorem step_setChild_ne {v c v' : Val} {a b : Proj} (h : setChild v a c = some v')
    (hab : a ≠ b) : step v' b = step v b := by
  cases v <;> cases a <;> simp [setChild] at h
  · rename_i t fs k i
    obtain ⟨⟨rfl, hi⟩, rfl⟩ := h
    cases b with
    | field k' j =>
      by_cases hk : t = k'
      · subst hk
        have hij : i ≠ j := by intro e; exact hab (by rw [e])
        simp [step, List.getElem?_set_ne hij]
      · simp [step, hk]
    | deref => rfl
  · subst h
    cases b with
    | field k' j => rfl
    | deref => exact absurd rfl hab

theorem lookup_cons_congr {v v' : Val} {b : Proj} (ps : Place) (h : step v' b = step v b) :
    lookup v' (b :: ps) = lookup v (b :: ps) := by
  simp only [lookup, h]

/-- A write at `w` leaves the head at `p` unchanged unless `w` is a prefix of `p`
(i.e. unless `p` lies inside `w` or equals it). This is the frame property behind
shallow freezing. -/
theorem headAt_writeOrSkip_of_not_prefix (w : Place) :
    ∀ (v x : Val) (p : Place), ¬ w <+: p → headAt (writeOrSkip v w x) p = headAt v p := by
  induction w with
  | nil => intro v x p h; exact absurd (List.nil_prefix) h
  | cons a w ih =>
    intro v x p hp
    unfold writeOrSkip
    simp only [write]
    split
    · rfl
    · rename_i c hc
      split
      · rfl
      · rename_i c' hc'
        cases hs : setChild v a c' with
        | none => rfl
        | some v' =>
          simp only [Option.getD_some]
          cases p with
          | nil => simp [headAt, lookup, setChild_head hs]
          | cons b p =>
            by_cases hab : a = b
            · subst hab
              have hp' : ¬ w <+: p := by
                intro h'; exact hp (List.cons_prefix_cons.mpr ⟨rfl, h'⟩)
              have e := ih c x p hp'
              have hw : writeOrSkip c w x = c' := by simp [writeOrSkip, hc']
              rw [hw] at e
              simp only [headAt, lookup, step_setChild_same hs, hc]
              simpa [headAt] using e
            · simp only [headAt]
              rw [lookup_cons_congr p (step_setChild_ne hs hab)]

/-- A write at `w` leaves the whole value at `p` unchanged when neither place is a prefix
of the other (the places are disjoint). This is the frame property behind deep freezing. -/
theorem lookup_writeOrSkip_of_disjoint (w : Place) :
    ∀ (v x : Val) (p : Place), ¬ w <+: p → ¬ p <+: w →
      lookup (writeOrSkip v w x) p = lookup v p := by
  induction w with
  | nil => intro v x p h; exact absurd (List.nil_prefix) h
  | cons a w ih =>
    intro v x p hp hp2
    unfold writeOrSkip
    simp only [write]
    split
    · rfl
    · rename_i c hc
      split
      · rfl
      · rename_i c' hc'
        cases hs : setChild v a c' with
        | none => rfl
        | some v' =>
          simp only [Option.getD_some]
          cases p with
          | nil => exact absurd (List.nil_prefix) hp2
          | cons b p =>
            by_cases hab : a = b
            · subst hab
              have hp' : ¬ w <+: p := by
                intro h'; exact hp (List.cons_prefix_cons.mpr ⟨rfl, h'⟩)
              have hp2' : ¬ p <+: w := by
                intro h'; exact hp2 (List.cons_prefix_cons.mpr ⟨rfl, h'⟩)
              have e := ih c x p hp' hp2'
              have hw : writeOrSkip c w x = c' := by simp [writeOrSkip, hc']
              rw [hw] at e
              simp only [lookup, step_setChild_same hs, hc]
              exact e
            · exact lookup_cons_congr p (step_setChild_ne hs hab)

end Toy.MatchGuard
