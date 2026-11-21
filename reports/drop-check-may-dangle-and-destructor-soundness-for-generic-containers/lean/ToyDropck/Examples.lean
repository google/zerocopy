import ToyDropck.Checker

/-!
# Concrete container types, programs, and definition examples

Container type constructors used throughout (by number, through `mkTbl`):
* `0`: the container under study (`Vec<T>`-like), whose `DropImpl` varies per example;
* `1`: `reader`, a `D<T>` whose destructor uses its `T` element (like an `Inspector` that prints
  the data it borrows);
* `2`: `wrap`, a plain struct `W<T>` with a by-value `T` field and no `Drop` impl;
* everything else, in particular `3`: `plain` (no `Drop` impl, drops nothing, declares nothing;
  at index `3` it plays a `ManuallyDrop<T>`-like wrapper).
-/

namespace Toy.Dropck

/-- `Vec<T>` with `unsafe impl<#[may_dangle] T> Drop for Vec<T>` and a `PhantomData<T>`: the
destructor drops the elements but does not otherwise use them. -/
def vecMD : DropImpl := ⟨⟨true, false, true⟩, ⟨true, true⟩⟩
/-- `Vec<T>` with a plain `impl<T> Drop for Vec<T>` (no `may_dangle`). -/
def vecStrict : DropImpl := ⟨⟨true, false, true⟩, ⟨false, true⟩⟩
/-- `D<T>`: a `Drop` impl (without `may_dangle`) that uses its `T` element, owning it by value. -/
def reader : DropImpl := ⟨⟨true, true, true⟩, ⟨false, true⟩⟩
/-- `W<T>`: a plain struct with a by-value `T` field and no `Drop` impl. -/
def wrap : DropImpl := ⟨⟨false, false, true⟩, ⟨false, true⟩⟩
/-- A `may_dangle` container that drops its elements but declares no ownership of `T` (for
example a raw pointer to the buffer without `PhantomData<T>`). -/
def vecNoOwn : DropImpl := ⟨⟨true, false, true⟩, ⟨true, false⟩⟩
/-- A `Drop` impl that claims `may_dangle` on `T` but uses its elements. -/
def liar : DropImpl := ⟨⟨true, true, true⟩, ⟨true, true⟩⟩
/-- A type without `Drop` impl whose drop glue drops its elements but which declares no ownership
of `T`: a toy-level configuration chosen to violate `GlueVisible`. -/
def hiddenGlue : DropImpl := ⟨⟨false, false, true⟩, ⟨false, false⟩⟩
/-- No `Drop` impl, drops nothing, declares nothing. -/
def plain : DropImpl := ⟨⟨false, false, false⟩, ⟨false, false⟩⟩
/-- A `may_dangle` handle whose destructor frees its buffer without dropping or using the
elements, and which declares no ownership of `T` (compare a raw-buffer type such as `RawVec<T>`). -/
def rawVec : DropImpl := ⟨⟨true, false, false⟩, ⟨true, false⟩⟩
/-- A `Drop` impl that claims `may_dangle` on `T`, uses its elements, and does not drop them. -/
def liarRaw : DropImpl := ⟨⟨true, true, false⟩, ⟨true, false⟩⟩

/-- The implementation table with container `0` described by `v`, `1 ↦ reader`, `2 ↦ wrap`, and
`plain` elsewhere. -/
def mkTbl (v : DropImpl) : ImplTable
  | 0 => v
  | 1 => reader
  | 2 => wrap
  | _ => plain

/-- `let mut v = Vec::new(); let x = 0; v.push(&x);` — `v` (local 0) is declared first, so in
reverse declaration order `x` (local 1) is dropped first and `v` is dropped holding a dangling
reference. -/
def pContainer : Prog := ⟨[(.app 0 (.ref 1), .obj 0 [.ref 1]), (.int, .int 0)]⟩

/-- `let x = 0; let v = vec![&x];` — the referent is declared first, so `v` is dropped first. -/
def pReferentFirst : Prog := ⟨[(.int, .int 0), (.app 0 (.ref 0), .obj 0 [.ref 0])]⟩

/-- `let mut v = Vec::new(); let x = 0; v.push(D(&x));` — the element's own destructor uses `&x`. -/
def pOwnedReader : Prog :=
  ⟨[(.app 0 (.app 1 (.ref 1)), .obj 0 [.obj 1 [.ref 1]]), (.int, .int 0)]⟩

/-- `let mut v = Vec::new(); let x = 0; v.push(W(D(&x)));` — the destructor that uses `&x` sits
under a type without `Drop` impl. -/
def pNestedReader : Prog :=
  ⟨[(.app 0 (.app 2 (.app 1 (.ref 1))), .obj 0 [.obj 2 [.obj 1 [.ref 1]]]), (.int, .int 0)]⟩

/-- `let mut v = Vec::new(); let x = 0; v.push(D(&x)); v.clear();` — at scope exit `v` is empty
but its element type is `D<&x>`. -/
def pEmptyOwnedReader : Prog :=
  ⟨[(.app 0 (.app 1 (.ref 1)), .obj 0 []), (.int, .int 0)]⟩

/-- `let y = 0; let v = vec![D(&y)];` — the referent is declared first, so `v` is dropped first. -/
def pOwnedReaderAfter : Prog :=
  ⟨[(.int, .int 0), (.app 0 (.app 1 (.ref 0)), .obj 0 [.obj 1 [.ref 0]])]⟩

/-- `let mut vv = Vec::new(); let x = 0; vv.push(vec![&x]);` — a container of containers holding a
reference that dangles when `vv` is dropped. -/
def pNestedVec : Prog :=
  ⟨[(.app 0 (.app 0 (.ref 1)), .obj 0 [.obj 0 [.ref 1]]), (.int, .int 0)]⟩

/-- `let mut v = Vec::new(); let x = 0; v.push(ManuallyDrop::new(D(&x)));` — the reader sits
under the `ManuallyDrop`-like wrapper `3` (`plain`), whose drop does nothing. -/
def pManuallyDropReader : Prog :=
  ⟨[(.app 0 (.app 3 (.app 1 (.ref 1))), .obj 0 [.obj 3 [.obj 1 [.ref 1]]]), (.int, .int 0)]⟩

/-- `let x = 0; let d = D(&x);` — the reader is declared after its referent. -/
def pReaderAfter : Prog := ⟨[(.int, .int 0), (.app 1 (.ref 0), .obj 1 [.ref 0])]⟩

/-- A single local holding a reader whose element refers to the local itself. -/
def pSelfReader : Prog := ⟨[(.app 1 (.ref 0), .obj 1 [.ref 0])]⟩

/-- `let r; let d; let x = 0; r = &x; d = D(&r);` — `d`'s element is a reference to the local `r`,
whose own value is a reference to `x`. -/
def pRefToRef : Prog :=
  ⟨[(.ref 2, .ref 2), (.app 1 (.ref 0), .obj 1 [.ref 0]), (.int, .int 0)]⟩

/-- Local 0 is declared `int` but holds `D(&x)`: values disagree with declared types. -/
def pIllTyped : Prog := ⟨[(.int, .obj 1 [.ref 1]), (.int, .int 0)]⟩

/-- A reference to local 5 in a scope with one local. -/
def pOutOfScope : Prog := ⟨[(.ref 5, .ref 5)]⟩

/-- `D(&local5)` in a scope with one local: the referenced local does not exist. -/
def pOutOfScopeReader : Prog := ⟨[(.app 1 (.ref 5), .obj 1 [.ref 5])]⟩

/-- The non-strict variant of `outlives`, without the conjunct `j != i`. It is not used by any
checker; it serves to show what that conjunct excludes. -/
def outlivesNonStrict (ord : List Nat) (i j : Nat) : Bool :=
  !(ord.takeWhile (· != i)).contains j

/-! ## Definition examples -/

theorem revDeclOrder_three : revDeclOrder 3 = [2, 1, 0] := by decide
theorem declOrder_three : declOrder 3 = [0, 1, 2] := by decide

-- `live`
theorem live_pos : live 2 [1] 0 = true := by decide
theorem live_neg_dead : live 2 [1] 1 = false := by decide
theorem live_neg_absent : live 2 [] 2 = false := by decide

-- `observe`
theorem observe_pos : observe (live 2 [1]) (.obj 1 [.ref 0]) = true := by decide
theorem observe_neg : observe (live 2 [1]) (.obj 1 [.ref 1]) = false := by decide

-- `dropVal`: a destructor that uses a dangling element is UB; one that ignores it is not.
theorem dropVal_pos_ignoring :
    dropVal (behOf (mkTbl vecMD)) (live 2 [1]) (.obj 0 [.ref 1]) = true := by decide
theorem dropVal_neg_using :
    dropVal (behOf (mkTbl vecMD)) (live 2 [1]) (.obj 1 [.ref 1]) = false := by decide
theorem dropVal_neg_glue :
    dropVal (behOf (mkTbl vecMD)) (live 2 [1]) (.obj 0 [.obj 1 [.ref 1]]) = false := by decide

-- `DropSafe`
theorem dropSafe_pos : DropSafe (mkTbl vecMD) (revDeclOrder 2) pContainer := by decide
theorem dropSafe_neg : ¬ DropSafe (mkTbl liar) (revDeclOrder 2) pContainer := by decide
/-- A local counts as dead during its own drop. -/
theorem dropSafe_neg_self : ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pSelfReader := by decide
/-- Locals that the order never names are never dropped, so any table is safe for `ord = []`. -/
theorem dropSafe_ignores_undropped : DropSafe (mkTbl liar) [] pContainer := by decide

-- `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `MayDangleDropsNothing`
theorem mayDangleHonest_pos : MayDangleHonest vecMD := by decide
theorem mayDangleHonest_neg : ¬ MayDangleHonest liar := by decide
theorem ownsDeclared_pos : OwnsDeclared vecMD := by decide
theorem ownsDeclared_neg : ¬ OwnsDeclared vecNoOwn := by decide
theorem glueVisible_pos : GlueVisible wrap := by decide
theorem glueVisible_neg : ¬ GlueVisible hiddenGlue := by decide
theorem mayDangleDropsNothing_pos : MayDangleDropsNothing rawVec := by decide
theorem mayDangleDropsNothing_neg : ¬ MayDangleDropsNothing vecMD := by decide

-- `hasTy`, `ValuesHaveTypes`, `LifetimesInScope`
theorem hasTy_pos : hasTy (.obj 0 [.ref 1, .ref 1]) (.app 0 (.ref 1)) = true := by decide
theorem hasTy_neg : hasTy (.obj 0 [.ref 1]) (.app 0 (.ref 0)) = false := by decide
theorem valuesHaveTypes_pos : ValuesHaveTypes pContainer := by decide
theorem valuesHaveTypes_neg : ¬ ValuesHaveTypes pIllTyped := by decide
theorem lifetimesInScope_pos : LifetimesInScope pContainer := by decide
theorem lifetimesInScope_neg : ¬ LifetimesInScope pOutOfScope := by decide

-- `outlives`: with order `[1, 0]`, local 0 strictly outlives the drop of local 1, not conversely,
-- and no local strictly outlives its own drop (whereas the non-strict variant admits it).
theorem outlives_pos : outlives (revDeclOrder 2) 1 0 = true := by decide
theorem outlives_neg : outlives (revDeclOrder 2) 0 1 = false := by decide
theorem outlives_neg_self : outlives (revDeclOrder 2) 0 0 = false := by decide
theorem outlivesNonStrict_self : outlivesNonStrict (revDeclOrder 2) 0 0 = true := by decide

-- `headHasNoDrop`, `deepHasNoDrop`
theorem headHasNoDrop_pos : headHasNoDrop (mkTbl vecMD) (.app 2 (.app 1 (.ref 1))) = true := by decide
theorem headHasNoDrop_neg : headHasNoDrop (mkTbl vecMD) (.app 1 (.ref 1)) = false := by decide
theorem deepHasNoDrop_pos : deepHasNoDrop (mkTbl vecMD) (.app 2 (.ref 1)) = true := by decide
theorem deepHasNoDrop_neg : deepHasNoDrop (mkTbl vecMD) (.app 2 (.app 1 (.ref 1))) = false := by decide

-- `dropckP`, for each policy. With order `[1, 0]`, local 0 strictly outlives the drop of local 1,
-- and local 1 does not strictly outlive the drop of local 0.
theorem dropck_pos :
    dropckP .ownsRecurse (mkTbl vecMD) (outlives (revDeclOrder 2) 0) (.app 0 (.ref 1)) = true := by
  decide
theorem dropck_neg :
    dropckP .ownsRecurse (mkTbl vecMD) (outlives (revDeclOrder 2) 0) (.app 1 (.ref 1)) = false := by
  decide
theorem dropck_noUseSuffices_pos :
    dropckP .noUseSuffices (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 1 (.ref 1))) = true := by
  decide
theorem dropck_headNoDrop_pos :
    dropckP .headNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 2 (.app 1 (.ref 1)))) = true := by
  decide
theorem dropck_headNoDrop_neg :
    dropckP .headNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 1 (.ref 1))) = false := by
  decide
/-- `deepNoDrop` exempts `T = &x` (no `Drop` impl in `T`) although `x` does not outlive the drop. -/
theorem dropck_deepNoDrop_exempt :
    dropckP .deepNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0) (.app 0 (.ref 1)) = true := by
  decide
/-- `deepNoDrop` accepts `T = D<&y>` (a `Drop` impl in `T`) when `y` strictly outlives the drop. -/
theorem dropck_deepNoDrop_fallback :
    dropckP .deepNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 1)
      (.app 0 (.app 1 (.ref 0))) = true := by
  decide
/-- `deepNoDrop` rejects `T = W<D<&x>>` when `x` does not outlive the drop. -/
theorem dropck_deepNoDrop_neg :
    dropckP .deepNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 2 (.app 1 (.ref 1)))) = false := by
  decide

-- `accepts`, `acceptsStrict`, `stripDangle`
theorem accepts_pos : accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := by decide
theorem accepts_neg : accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false := by decide
theorem acceptsStrict_pos : acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pReferentFirst = true := by
  decide
theorem acceptsStrict_neg : acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pContainer = false := by
  decide
theorem stripDangle_erases : stripDangle (mkTbl vecMD) 0 = vecStrict := by decide
/-- Locals that the order never drops are not constrained. -/
theorem accepts_ignores_undropped : accepts (mkTbl vecStrict) [] pContainer = true := by decide

/-! ## The example tables satisfy (or violate) the honesty conditions -/

/-- A property of every entry of `mkTbl v` follows from the property of its four distinct
entries. -/
theorem mkTbl_all {P : DropImpl → Prop} (v : DropImpl) (hv : P v) (hr : P reader) (hw : P wrap)
    (hp : P plain) : ∀ c, P (mkTbl v c) := by
  intro c
  match c with
  | 0 => exact hv
  | 1 => exact hr
  | 2 => exact hw
  | _ + 3 => exact hp

/-- `mkTbl vecMD` satisfies all three honesty conditions. -/
theorem honest_vecMD :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) :=
  ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
   mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
   mkTbl_all _ (by decide) (by decide) (by decide) (by decide)⟩

/-- `mkTbl vecStrict` satisfies all three honesty conditions. -/
theorem honest_vecStrict :
    (∀ c, MayDangleHonest (mkTbl vecStrict c)) ∧ (∀ c, OwnsDeclared (mkTbl vecStrict c)) ∧
      (∀ c, GlueVisible (mkTbl vecStrict c)) :=
  ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
   mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
   mkTbl_all _ (by decide) (by decide) (by decide) (by decide)⟩

/-- `mkTbl rawVec` satisfies `MayDangleHonest`, `MayDangleDropsNothing` and `GlueVisible`. -/
theorem honest_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) :=
  ⟨mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
   mkTbl_all _ (by decide) (by decide) (by decide) (by decide),
   mkTbl_all _ (by decide) (by decide) (by decide) (by decide)⟩

/-- The runtime parts of `mkTbl vecMD` and `mkTbl vecStrict` coincide. -/
theorem behOf_mkTbl_vecMD_eq_vecStrict : behOf (mkTbl vecMD) = behOf (mkTbl vecStrict) := by
  funext c
  match c with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

end Toy.Dropck
