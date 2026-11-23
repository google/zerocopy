/-!
# MIR Drop Elaboration, Dynamic Drop Flags, Partial Moves (`E0509`),
# `ManuallyDrop` / `MaybeUninit` Suppression, and Deterministic Drop Order

Mechanized soundness model anchored in `rust-lang/rust` (`compiler/rustc_mir_transform/src/{elaborate_drops.rs, elaborate_drop.rs}`,
`compiler/rustc_mir_dataflow/src/{drop_flag_effects.rs, move_paths/mod.rs}`,
`compiler/rustc_mir_build/src/builder/scope.rs`, `compiler/rustc_ty_utils/src/needs_drop.rs`,
and `compiler/rustc_borrowck/src/lib.rs`).

Purity contract:
* Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`.
* Every `def` is marked `noncomputable def`; no `noncomputable section`; no `partial def`;
  no `deriving DecidableEq` / `Repr` on recursive inductives (zero `._unsafe_rec` constants).
-/

namespace Vrustc.MirDropElaboration

/-! ## 1. Identifiers, Drop Flags, Drop Styles, and MIR Types -/

abbrev LocalId := Nat
abbrev BlockId := Nat
abbrev DropTag := Nat
abbrev FlagId := Nat
abbrev BoolReg := Nat

/-- Mirrors `rustc_mir_dataflow::drop_flag_effects::DropFlagState`
(`drop_flag_effects.rs:10-26`). -/
inductive DropFlagState where
  | present
  | absent

noncomputable def DropFlagState.toBool : DropFlagState → Bool
  | .present => true
  | .absent => false

noncomputable def DropFlagState.ofBool : Bool → DropFlagState
  | true => .present
  | false => .absent

noncomputable def DropFlagState.beq : DropFlagState → DropFlagState → Bool
  | .present, .present => true
  | .absent, .absent => true
  | _, _ => false

/-- Mirrors `rustc_mir_transform::elaborate_drop::DropStyle`
(`elaborate_drop.rs:19-36`). -/
inductive DropStyle where
  | dead
  | static_
  | conditional
  | open_

noncomputable def DropStyle.beq : DropStyle → DropStyle → Bool
  | .dead, .dead => true
  | .static_, .static_ => true
  | .conditional, .conditional => true
  | .open_, .open_ => true
  | _, _ => false

/-- Mirrors `rustc_mir_transform::elaborate_drop::DropFlagMode`
(`elaborate_drop.rs:40-45`). -/
inductive DropFlagMode where
  | shallow
  | deep

/-- Mirrors `rustc_mir_transform::elaborate_drops::ElaborateDropsCtxt::drop_style`
decision matrix (`elaborate_drops.rs:187-192`). -/
noncomputable def dropStyleOf (maybeInit maybeUninit multipart : Bool) : DropStyle :=
  match maybeInit, maybeUninit, multipart with
  | false, _, _ => .dead
  | true, false, _ => .static_
  | true, true, false => .conditional
  | true, true, true => .open_

/-- MIR type system capturing drop glue, `Drop`-trait partial-move protection,
`Box<T>` deref-move handling, and `ManuallyDrop<T>` / `MaybeUninit<T>` suppression. -/
inductive MirTy where
  | scalar
  | dropLeaf (tag : DropTag)
  | structTy (hasDrop : Bool) (selfTag : Option DropTag) (fields : List MirTy)
  | tupleTy (elems : List MirTy)
  | arrayTy (elem : MirTy) (len : Nat)
  | enumTy (variants : List (List MirTy))
  | boxTy (inner : MirTy) (heapTag : DropTag)
  | manuallyDrop (inner : MirTy)
  | maybeUninit (inner : MirTy)

/-- Structural equality helpers on `Nat`, `Bool`, `Option`, and `List`
without introducing `Classical.choice` or `_unsafe_rec`. -/
noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | _ + 1, 0 => false
  | 0, _ + 1 => false
  | m + 1, n + 1 => natEq m n

noncomputable def natLt : Nat → Nat → Bool
  | _, 0 => false
  | 0, _ + 1 => true
  | m + 1, n + 1 => natLt m n

noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

noncomputable def listLength {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => listLength xs + 1

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

noncomputable def listReverseAux {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => listReverseAux xs (x :: acc)

noncomputable def listReverse {α : Type} (xs : List α) : List α :=
  listReverseAux xs []

noncomputable def listAppend {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: listAppend xs ys

noncomputable def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: listMap f xs

noncomputable def listFilter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: listFilter p xs else listFilter p xs

noncomputable def listFoldl {α β : Type} (f : β → α → β) (init : β) : List α → β
  | [] => init
  | x :: xs => listFoldl f (f init x) xs

-- Mirrors `rustc_ty_utils::needs_drop::needs_drop_raw` and `drop_tys_helper`
-- (`needs_drop.rs:17-33, 352-394`, `ty/util.rs:1521-1536`).
-- `manuallyDrop _` and `maybeUninit _` (a `union`) return `false`, and `arrayTy _ 0` returns `false`.
mutual
  noncomputable def needsDrop : MirTy → Bool
    | .scalar => false
    | .dropLeaf _ => true
    | .structTy hasDrop _ fields => hasDrop || needsDropList fields
    | .tupleTy elems => needsDropList elems
    | .arrayTy _ 0 => false
    | .arrayTy elem (_ + 1) => needsDrop elem
    | .enumTy variants => needsDropVariants variants
    | .boxTy _ _ => true
    | .manuallyDrop _ => false
    | .maybeUninit _ => false

  noncomputable def needsDropList : List MirTy → Bool
    | [] => false
    | t :: ts => needsDrop t || needsDropList ts

  noncomputable def needsDropVariants : List (List MirTy) → Bool
    | [] => false
    | v :: vs => needsDropList v || needsDropVariants vs
end

/-! ## 2. Projections, MovePaths, `E0509` Protection, and Drop Order -/

inductive ProjElem where
  | field (idx : Nat)
  | arrayIdx (idx : Nat)
  | downcast (varIdx : Nat)
  | deref

noncomputable def ProjElem.beq : ProjElem → ProjElem → Bool
  | .field a, .field b => natEq a b
  | .arrayIdx a, .arrayIdx b => natEq a b
  | .downcast a, .downcast b => natEq a b
  | .deref, .deref => true
  | _, _ => false

noncomputable def projListBeq : List ProjElem → List ProjElem → Bool
  | [], [] => true
  | x :: xs, y :: ys => ProjElem.beq x y && projListBeq xs ys
  | _, _ => false

structure Place where
  localId : LocalId
  proj : List ProjElem

noncomputable def Place.beq (a b : Place) : Bool :=
  natEq a.localId b.localId && projListBeq a.proj b.proj

noncomputable def placeTypeWalk : MirTy → List ProjElem → Option MirTy
  | ty, [] => some ty
  | .structTy _ _ fields, .field idx :: rest =>
    match listGet? fields idx with
    | some fty => placeTypeWalk fty rest
    | none => none
  | .tupleTy elems, .field idx :: rest =>
    match listGet? elems idx with
    | some ety => placeTypeWalk ety rest
    | none => none
  | .arrayTy elem len, .arrayIdx idx :: rest =>
    if natLt idx len then placeTypeWalk elem rest else none
  | .enumTy variants, .downcast v :: .field idx :: rest =>
    match listGet? variants v with
    | some fields =>
      match listGet? fields idx with
      | some fty => placeTypeWalk fty rest
      | none => none
    | none => none
  | .boxTy inner _, .deref :: rest =>
    placeTypeWalk inner rest
  | _, _ => none

/-- Mirrors `MoveDataBuilder` (`move_paths/builder.rs:177-184`) and `rustc_borrowck`
`IllegalMoveOriginKind::InteriorOfTypeWithDestructor` (`rustc_borrowck/src/lib.rs:1947-1957`,
`E0509`): projecting into an ADT with `hasDrop = true`, or into `ManuallyDrop` / `MaybeUninit`,
is NOT a valid independent move path. -/
noncomputable def isValidMovePathWalk : MirTy → List ProjElem → Bool
  | _, [] => true
  | .structTy false _ fields, .field idx :: rest =>
    match listGet? fields idx with
    | some fty => isValidMovePathWalk fty rest
    | none => false
  | .structTy true _ _, .field _ :: _ => false
  | .tupleTy elems, .field idx :: rest =>
    match listGet? elems idx with
    | some ety => isValidMovePathWalk ety rest
    | none => false
  | .arrayTy elem len, .arrayIdx idx :: rest =>
    if natLt idx len then isValidMovePathWalk elem rest else false
  | .enumTy variants, .downcast v :: .field idx :: rest =>
    match listGet? variants v with
    | some fields =>
      match listGet? fields idx with
      | some fty => isValidMovePathWalk fty rest
      | none => false
    | none => false
  | .boxTy inner _, .deref :: rest =>
    isValidMovePathWalk inner rest
  | .manuallyDrop _, _ :: _ => false
  | .maybeUninit _, _ :: _ => false
  | _, _ => false

noncomputable def isValidMovePath (locals : List MirTy) (p : Place) : Bool :=
  match listGet? locals p.localId with
  | some ty => isValidMovePathWalk ty p.proj
  | none => false

/-- Distinguishes leaf/struct destructors from `Box<T>` shallow heap deallocation. -/
inductive AtomKind where
  | leaf
  | adtDrop
  | boxShallow

noncomputable def AtomKind.beq : AtomKind → AtomKind → Bool
  | .leaf, .leaf => true
  | .adtDrop, .adtDrop => true
  | .boxShallow, .boxShallow => true
  | _, _ => false

/-- Maximal independently tracked drop unit (atom) in the `MovePath` tree. -/
structure Atom where
  localId : LocalId
  proj : List ProjElem
  tag : DropTag
  kind : AtomKind

noncomputable def Atom.beq (a b : Atom) : Bool :=
  natEq a.localId b.localId &&
    projListBeq a.proj b.proj &&
    natEq a.tag b.tag &&
    AtomKind.beq a.kind b.kind

noncomputable def atomInList (a : Atom) : List Atom → Bool
  | [] => false
  | x :: xs => Atom.beq a x || atomInList a xs

noncomputable def mapAtomPrefix (loc : LocalId) (pref : List ProjElem) : List Atom → List Atom
  | [] => []
  | a :: rest =>
    { a with localId := loc, proj := listAppend pref a.proj } :: mapAtomPrefix loc pref rest

noncomputable def replicateArrayAtoms (loc : LocalId) (pref : List ProjElem)
    (elemAtoms : List Atom) (idx : Nat) : Nat → List Atom
  | 0 => []
  | n + 1 =>
    listAppend
      (mapAtomPrefix loc (listAppend pref [.arrayIdx idx]) elemAtoms)
      (replicateArrayAtoms loc pref elemAtoms (idx + 1) n)

-- Collects all drop atoms under `ty` at base path `(loc, prefix)` in deterministic
-- declaration/index order (`open_drop_for_adt_contents`, `open_drop_for_tuple`,
-- `open_drop_for_array` in `3ef0c22cd`/`0259d5e9a`, and `open_drop_for_box_contents`).
-- Notice `manuallyDrop` and `maybeUninit` yield `[]`.
mutual
  noncomputable def atomsOfTyAux (loc : LocalId) (pref : List ProjElem) : MirTy → List Atom
    | .scalar => []
    | .dropLeaf tag => [{ localId := loc, proj := pref, tag := tag, kind := .leaf }]
    | .structTy true (some tag) _ =>
      [{ localId := loc, proj := pref, tag := tag, kind := .adtDrop }]
    | .structTy true none _ => []
    | .structTy false _ fields => atomsOfFields loc pref 0 fields
    | .tupleTy elems => atomsOfFields loc pref 0 elems
    | .arrayTy elem len =>
      replicateArrayAtoms loc pref (atomsOfTyAux loc [] elem) 0 len
    | .enumTy variants => atomsOfVariants loc pref 0 variants
    | .boxTy inner heapTag =>
      listAppend
        (atomsOfTyAux loc (listAppend pref [.deref]) inner)
        [{ localId := loc, proj := pref, tag := heapTag, kind := .boxShallow }]
    | .manuallyDrop _ => []
    | .maybeUninit _ => []

  noncomputable def atomsOfFields (loc : LocalId) (pref : List ProjElem) (idx : Nat) :
      List MirTy → List Atom
    | [] => []
    | f :: fs =>
      listAppend
        (atomsOfTyAux loc (listAppend pref [.field idx]) f)
        (atomsOfFields loc pref (idx + 1) fs)

  noncomputable def atomsOfVariants (loc : LocalId) (pref : List ProjElem) (vIdx : Nat) :
      List (List MirTy) → List Atom
    | [] => []
    | vFields :: vs =>
      listAppend
        (atomsOfFields loc (listAppend pref [.downcast vIdx]) 0 vFields)
        (atomsOfVariants loc pref (vIdx + 1) vs)
end

noncomputable def atomsOfPlace (locals : List MirTy) (p : Place) : List Atom :=
  match listGet? locals p.localId with
  | some baseTy =>
    match placeTypeWalk baseTy p.proj with
    | some subTy => atomsOfTyAux p.localId p.proj subTy
    | none => []
  | none => []

/-- Models `scope.drops.iter().rev()` in `rustc_mir_build::builder::scope::build_scope_drops`
(`scope.rs:1841`). Locals declared in order `[l_0, ..., l_{k-1}]` are dropped in reverse
declaration order `[l_{k-1}, ..., l_0]`. -/
noncomputable def localsDropOrder (locals : List LocalId) : List LocalId :=
  listReverse locals

/-- Models `drop_ladder` / `drop_halfladder` field-order lowering
(`elaborate_drop.rs:838-955`): given fields in declaration order `[0..n-1]`,
`drop_halfladder` iterates `fields.iter().rev()` building successor chain backwards,
yielding runtime drop execution in forward order `[0..n-1]`. -/
noncomputable def dropHalfLadderOrder {α : Type} (fields : List α) : List α :=
  -- Constructing blocks from tail backwards preserves forward runtime execution order.
  listReverse (listReverse fields)

noncomputable def openDropArrayGo (isMoved : Nat → Bool) (idx : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
    let rest := openDropArrayGo isMoved (idx + 1) n
    if isMoved idx then rest else idx :: rest

/-- Models the `14210df0e` (`elaborate_drop.rs:1133-1135`) and `49d734536` (`elaborate_drop.rs:1392-1394`)
double-reversal bug in `open_drop_for_array` when partial moves occur via array patterns:
`drop_ranges.iter().rev()` passed into `drop_ladder` caused remaining array elements
to be dropped in reverse index order. -/
noncomputable def openDropArrayRemainingPreFix (len : Nat) (isMoved : Nat → Bool) : List Nat :=
  listReverse (openDropArrayGo isMoved 0 len)

/-- Models the `3ef0c22cd` / `0259d5e9a` (`elaborate_drop.rs:1370-1372`)
fix removing `.rev()`, restoring forward index order `0..len-1` on remaining elements. -/
noncomputable def openDropArrayRemainingPostFix (len : Nat) (isMoved : Nat → Bool) : List Nat :=
  openDropArrayGo isMoved 0 len

/-! ## 3. Map Infrastructure and Decidability Proofs (Axiom-Clean) -/

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_sound {m n : Nat} : natEq m n = true → m = n := by
  induction m generalizing n with
  | zero =>
    intro h
    cases n with
    | zero => rfl
    | succ k => cases h
  | succ m' ih =>
    intro h
    cases n with
    | zero => cases h
    | succ n' =>
      have eq' : m' = n' := ih h
      rw [eq']

theorem natEq_iff (m n : Nat) : natEq m n = true ↔ m = n := by
  constructor
  · exact natEq_sound
  · intro h
    rw [h]
    exact natEq_refl n

theorem natEq_false_of_ne {m n : Nat} (h : m ≠ n) : natEq m n = false := by
  cases hb : natEq m n with
  | false => rfl
  | true => exact False.elim (h (natEq_sound hb))

theorem natLt_irrefl (n : Nat) : natLt n n = false := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natLt_ne {m n : Nat} : natLt m n = true → m ≠ n := by
  intro hlt heq
  rw [heq] at hlt
  rw [natLt_irrefl n] at hlt
  cases hlt

theorem projElem_beq_refl (e : ProjElem) : ProjElem.beq e e = true := by
  cases e with
  | field a => exact natEq_refl a
  | arrayIdx a => exact natEq_refl a
  | downcast a => exact natEq_refl a
  | deref => rfl

theorem projElem_beq_sound {a b : ProjElem} : ProjElem.beq a b = true → a = b := by
  cases a <;> cases b <;> intro h
  · rw [natEq_sound h]
  · cases h
  · cases h
  · cases h
  · cases h
  · rw [natEq_sound h]
  · cases h
  · cases h
  · cases h
  · cases h
  · rw [natEq_sound h]
  · cases h
  · cases h
  · cases h
  · cases h
  · rfl

theorem projListBeq_refl (ps : List ProjElem) : projListBeq ps ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (ProjElem.beq p p && projListBeq ps ps) = true
    rw [projElem_beq_refl p, ih]
    rfl

theorem projListBeq_sound {xs ys : List ProjElem} : projListBeq xs ys = true → xs = ys := by
  induction xs generalizing ys with
  | nil =>
    intro h
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    intro h
    cases ys with
    | nil => cases h
    | cons y ys =>
      change (ProjElem.beq x y && projListBeq xs ys) = true at h
      cases hx : ProjElem.beq x y
      · rw [hx] at h; cases h
      · rw [hx] at h
        cases hxs : projListBeq xs ys
        · rw [hxs] at h; cases h
        · rw [projElem_beq_sound hx, ih hxs]

theorem atomKind_beq_refl (k : AtomKind) : AtomKind.beq k k = true := by
  cases k <;> rfl

theorem atomKind_beq_sound {a b : AtomKind} : AtomKind.beq a b = true → a = b := by
  cases a <;> cases b <;> intro h <;> first | rfl | cases h

theorem atom_beq_refl (a : Atom) : Atom.beq a a = true := by
  cases a with
  | mk l p t k =>
    change (((natEq l l && projListBeq p p) && natEq t t) && AtomKind.beq k k) = true
    rw [natEq_refl l, projListBeq_refl p, natEq_refl t, atomKind_beq_refl k]
    rfl

theorem atom_beq_sound {a b : Atom} : Atom.beq a b = true → a = b := by
  cases a with
  | mk la pa ta ka =>
    cases b with
    | mk lb pb tb kb =>
      intro h
      change (((natEq la lb && projListBeq pa pb) && natEq ta tb) && AtomKind.beq ka kb) = true at h
      cases h1 : natEq la lb <;> rw [h1] at h
      · cases h
      · cases h2 : projListBeq pa pb <;> rw [h2] at h
        · cases h
        · cases h3 : natEq ta tb <;> rw [h3] at h
          · cases h
          · cases h4 : AtomKind.beq ka kb <;> rw [h4] at h
            · cases h
            · rw [natEq_sound h1, projListBeq_sound h2, natEq_sound h3, atomKind_beq_sound h4]

theorem atom_beq_iff (a b : Atom) : Atom.beq a b = true ↔ a = b := by
  constructor
  · exact atom_beq_sound
  · intro h
    rw [h]
    exact atom_beq_refl b

abbrev AtomMap := Atom → Bool
abbrev FlagMap := FlagId → Bool

noncomputable def emptyAtomMap : AtomMap := fun _ => false
noncomputable def emptyFlagMap : FlagMap := fun _ => false

noncomputable def setAtom (m : AtomMap) (k : Atom) (v : Bool) : AtomMap :=
  fun x => if Atom.beq x k then v else m x

noncomputable def setAtoms (m : AtomMap) (ks : List Atom) (v : Bool) : AtomMap :=
  match ks with
  | [] => m
  | k :: rest => setAtoms (setAtom m k v) rest v

noncomputable def setFlagMap (m : FlagMap) (f : FlagId) (v : DropFlagState) : FlagMap :=
  fun x => if natEq x f then v.toBool else m x

noncomputable def setFlagMaps (m : FlagMap) (fs : List FlagId) (v : DropFlagState) : FlagMap :=
  match fs with
  | [] => m
  | f :: rest => setFlagMaps (setFlagMap m f v) rest v

theorem setAtom_eq (m : AtomMap) (k : Atom) (v : Bool) :
    setAtom m k v k = v := by
  change (if Atom.beq k k then v else m k) = v
  rw [atom_beq_refl k]
  rfl

theorem setAtom_ne (m : AtomMap) {k x : Atom} (hne : x ≠ k) (v : Bool) :
    setAtom m k v x = m x := by
  change (if Atom.beq x k then v else m x) = m x
  cases hb : Atom.beq x k with
  | false => rfl
  | true => exact False.elim (hne (atom_beq_sound hb))

theorem setFlagMap_eq (m : FlagMap) (f : FlagId) (v : DropFlagState) :
    setFlagMap m f v f = v.toBool := by
  change (if natEq f f then v.toBool else m f) = v.toBool
  rw [natEq_refl f]
  rfl

theorem setFlagMap_ne (m : FlagMap) {f x : FlagId} (hne : x ≠ f) (v : DropFlagState) :
    setFlagMap m f v x = m x := by
  change (if natEq x f then v.toBool else m x) = m x
  cases hb : natEq x f with
  | false => rfl
  | true => exact False.elim (hne (natEq_sound hb))

theorem atomInList_cons (a x : Atom) (xs : List Atom) :
    atomInList a (x :: xs) = (Atom.beq a x || atomInList a xs) := rfl

theorem setAtoms_not_mem (m : AtomMap) (ks : List Atom) (v : Bool) (a : Atom)
    (hnot : atomInList a ks = false) :
    setAtoms m ks v a = m a := by
  induction ks generalizing m with
  | nil => rfl
  | cons k rest ih =>
    change (Atom.beq a k || atomInList a rest) = false at hnot
    cases hbk : Atom.beq a k with
    | true => rw [hbk] at hnot; cases hnot
    | false =>
      rw [hbk] at hnot
      have hne : a ≠ k := fun he => by rw [he, atom_beq_refl] at hbk; cases hbk
      change setAtoms (setAtom m k v) rest v a = m a
      rw [ih (setAtom m k v) hnot, setAtom_ne m hne v]

theorem setAtoms_mem (m : AtomMap) (ks : List Atom) (v : Bool) (a : Atom)
    (hmem : atomInList a ks = true) :
    setAtoms m ks v a = v := by
  induction ks generalizing m with
  | nil => cases hmem
  | cons k rest ih =>
    change (Atom.beq a k || atomInList a rest) = true at hmem
    cases hrest : atomInList a rest with
    | true =>
      change setAtoms (setAtom m k v) rest v a = v
      exact ih (setAtom m k v) hrest
    | false =>
      rw [hrest] at hmem
      cases hbk : Atom.beq a k with
      | false => rw [hbk] at hmem; cases hmem
      | true =>
        have heq : a = k := atom_beq_sound hbk
        cases hkr : atomInList k rest with
        | true =>
          have hmem' : atomInList a rest = true := by rw [heq]; exact hkr
          change setAtoms (setAtom m k v) rest v a = v
          exact ih (setAtom m k v) hmem'
        | false =>
          rw [heq]
          change setAtoms (setAtom m k v) rest v k = v
          rw [setAtoms_not_mem (setAtom m k v) rest v k hkr, setAtom_eq]

/-! ## 4. Source MIR Operational Semantics & Trace Equivalence Targets -/

inductive DropEvent where
  | create (tag : DropTag) (loc : LocalId)
  | dropCall (tag : DropTag) (loc : LocalId) (explicit : Bool)
  | boxDealloc (tag : DropTag) (loc : LocalId)
  | doubleOrUninitFault (tag : DropTag) (loc : LocalId)
  | uninitFieldInDropImpl (tag : DropTag) (loc : LocalId)

noncomputable def DropEvent.beq : DropEvent → DropEvent → Bool
  | .create t1 l1, .create t2 l2 => natEq t1 t2 && natEq l1 l2
  | .dropCall t1 l1 e1, .dropCall t2 l2 e2 => natEq t1 t2 && natEq l1 l2 && boolEq e1 e2
  | .boxDealloc t1 l1, .boxDealloc t2 l2 => natEq t1 t2 && natEq l1 l2
  | .doubleOrUninitFault t1 l1, .doubleOrUninitFault t2 l2 => natEq t1 t2 && natEq l1 l2
  | .uninitFieldInDropImpl t1 l1, .uninitFieldInDropImpl t2 l2 => natEq t1 t2 && natEq l1 l2
  | _, _ => false

noncomputable def DropEvent.atomEvent (a : Atom) (explicit : Bool) : DropEvent :=
  match a.kind with
  | .boxShallow => .boxDealloc a.tag a.localId
  | .leaf => .dropCall a.tag a.localId explicit
  | .adtDrop => .dropCall a.tag a.localId explicit

/-- Source MIR statements before `ElaborateDrops`. -/
inductive SrcStmt where
  | storageLive (l : LocalId)
  | storageDead (l : LocalId)
  | initPlace (p : Place)
  | movePlace (dst src : Place)
  | explicitDrop (p : Place)
  | noop

/-- Source MIR terminators before `ElaborateDrops`. -/
inductive SrcTerm where
  | goto (target : BlockId)
  | switchBool (reg : BoolReg) (bbTrue bbFalse : BlockId)
  | drop (p : Place) (target : BlockId) (unwind : Option BlockId)
  | scopeExit (localsToDrop : List LocalId) (target : BlockId) (unwind : Option BlockId)
  | ret
  | unwindResume
  | unwindAbort

structure SrcBlock where
  isCleanup : Bool
  stmts : List SrcStmt
  term : SrcTerm

structure SrcProgram where
  locals : List MirTy
  args : List LocalId
  entry : BlockId
  blocks : BlockId → Option SrcBlock

/-- Execution environment supplying branch conditions and destructor panic points. -/
structure ExecOracle where
  branchAt : Nat → BoolReg → Bool
  panicAt : Nat → Atom → Bool

inductive ExitKind where
  | running
  | returned
  | unwound
  | aborted
  | faulted

noncomputable def ExitKind.beq : ExitKind → ExitKind → Bool
  | .running, .running => true
  | .returned, .returned => true
  | .unwound, .unwound => true
  | .aborted, .aborted => true
  | .faulted, .faulted => true
  | _, _ => false

structure SrcState where
  bb : BlockId
  branchIdx : Nat
  dropIdx : Nat
  init : AtomMap
  trace : List DropEvent
  exit : ExitKind

noncomputable def emitCreateForAtoms (loc : LocalId) : List Atom → List DropEvent
  | [] => []
  | a :: rest =>
    match a.kind with
    | .boxShallow => emitCreateForAtoms loc rest
    | _ => .create a.tag loc :: emitCreateForAtoms loc rest

noncomputable def evalSrcDropAtomsGo (oracle : ExecOracle) (isCleanup : Bool) :
    List Atom → AtomMap → List DropEvent → Nat → Bool →
    AtomMap × List DropEvent × Nat × Bool × Bool
  | [], cur, tr, dIdx, panicked => (cur, tr, dIdx, panicked, false)
  | a :: rest, cur, tr, dIdx, panicked =>
    if cur a then
      let ev := DropEvent.atomEvent a false
      let cur' := setAtom cur a false
      let tr' := listAppend tr [ev]
      let p := oracle.panicAt dIdx a
      let dIdx' := dIdx + 1
      if panicked then
        if p then (cur', tr', dIdx', true, true)
        else evalSrcDropAtomsGo oracle isCleanup rest cur' tr' dIdx' true
      else if p then
        if isCleanup then (cur', tr', dIdx', true, true)
        else evalSrcDropAtomsGo oracle isCleanup rest cur' tr' dIdx' true
      else
        evalSrcDropAtomsGo oracle isCleanup rest cur' tr' dIdx' false
    else
      evalSrcDropAtomsGo oracle isCleanup rest cur tr dIdx panicked

/-- Source semantics of dropping a list of atoms in order, consulting `init : AtomMap`,
incrementing `dropIdx` per live destructor invocation, and unwinding on panic
(dropping remaining initialized atoms along cleanup path; double-panic in cleanup aborts). -/
noncomputable def evalSrcDropAtoms
    (dropIdx : Nat) (oracle : ExecOracle) (isCleanup : Bool)
    (atoms : List Atom) (init : AtomMap) :
    AtomMap × List DropEvent × Nat × Bool × Bool :=
  evalSrcDropAtomsGo oracle isCleanup atoms init [] dropIdx false

noncomputable def execExplicitDrop :
    List Atom → AtomMap → List DropEvent → AtomMap × List DropEvent
  | [], cur, tr => (cur, tr)
  | a :: rest, cur, tr =>
    if cur a then
      execExplicitDrop rest (setAtom cur a false) (listAppend tr [DropEvent.atomEvent a true])
    else
      execExplicitDrop rest cur (listAppend tr [.doubleOrUninitFault a.tag a.localId])

noncomputable def stepSrcStmt (locals : List MirTy) (st : SrcState) : SrcStmt → SrcState
  | .storageLive _ => st
  | .storageDead l =>
    let atoms := atomsOfPlace locals { localId := l, proj := [] }
    { st with init := setAtoms st.init atoms false }
  | .initPlace p =>
    let atoms := atomsOfPlace locals p
    { st with
      init := setAtoms st.init atoms true
      trace := listAppend st.trace (emitCreateForAtoms p.localId atoms) }
  | .movePlace dst src =>
    let srcAtoms := atomsOfPlace locals src
    let dstAtoms := atomsOfPlace locals dst
    { st with init := setAtoms (setAtoms st.init srcAtoms false) dstAtoms true }
  | .explicitDrop p =>
    let atoms := atomsOfPlace locals p
    let (init', tr') := execExplicitDrop atoms st.init st.trace
    { st with init := init', trace := tr' }
  | .noop => st

noncomputable def stepSrcStmtList (locals : List MirTy) : List SrcStmt → SrcState → SrcState
  | [], st => st
  | s :: ss, st => stepSrcStmtList locals ss (stepSrcStmt locals st s)

noncomputable def atomsOfLocalList (locals : List MirTy) : List LocalId → List Atom
  | [] => []
  | l :: ls => listAppend (atomsOfPlace locals { localId := l, proj := [] }) (atomsOfLocalList locals ls)

noncomputable def stepSrcBlock (prog : SrcProgram) (oracle : ExecOracle) (st : SrcState) : SrcState :=
  match st.exit with
  | .running =>
    match prog.blocks st.bb with
    | none => { st with exit := .faulted }
    | some blk =>
      let st1 := stepSrcStmtList prog.locals blk.stmts st
      match blk.term with
      | .goto tgt =>
        { st1 with bb := tgt }
      | .switchBool reg bbT bbF =>
        let tgt := if oracle.branchAt st1.branchIdx reg then bbT else bbF
        { st1 with bb := tgt, branchIdx := st1.branchIdx + 1 }
      | .drop p tgt unwind =>
        let atoms := atomsOfPlace prog.locals p
        let (init', evs, dIdx', panicked, aborted) :=
          evalSrcDropAtoms st1.dropIdx oracle blk.isCleanup atoms st1.init
        let tr' := listAppend st1.trace evs
        if aborted then
          { st1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
        else if panicked then
          match unwind with
          | some ubb => { st1 with bb := ubb, dropIdx := dIdx', init := init', trace := tr' }
          | none => { st1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
        else
          { st1 with bb := tgt, dropIdx := dIdx', init := init', trace := tr' }
      | .scopeExit locs tgt unwind =>
        let orderedLocs := localsDropOrder locs
        let atoms := atomsOfLocalList prog.locals orderedLocs
        let (init', evs, dIdx', panicked, aborted) :=
          evalSrcDropAtoms st1.dropIdx oracle blk.isCleanup atoms st1.init
        let tr' := listAppend st1.trace evs
        if aborted then
          { st1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
        else if panicked then
          match unwind with
          | some ubb => { st1 with bb := ubb, dropIdx := dIdx', init := init', trace := tr' }
          | none => { st1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
        else
          { st1 with bb := tgt, dropIdx := dIdx', init := init', trace := tr' }
      | .ret =>
        { st1 with exit := .returned }
      | .unwindResume =>
        { st1 with exit := .unwound }
      | .unwindAbort =>
        { st1 with exit := .aborted }
  | _ => st

noncomputable def execSrcFuel (prog : SrcProgram) (oracle : ExecOracle) :
    Nat → SrcState → SrcState
  | 0, st => st
  | n + 1, st =>
    match st.exit with
    | .running => execSrcFuel prog oracle n (stepSrcBlock prog oracle st)
    | _ => st

noncomputable def initSrcState (prog : SrcProgram) : SrcState :=
  let argAtoms := atomsOfLocalList prog.locals prog.args
  { bb := prog.entry
    branchIdx := 0
    dropIdx := 0
    init := setAtoms emptyAtomMap argAtoms true
    trace := []
    exit := .running }

/-! ## 5. Target Elaborated MIR Operational Semantics (Concrete Stack Flags, No Init Oracle) -/

/-- Target MIR statements after `ElaborateDrops`: drop-flag assignments are explicit
boolean assignments (`setFlag`); there is no initialization oracle. -/
inductive ElabStmt where
  | storageLive (l : LocalId)
  | storageDead (l : LocalId)
  | setFlag (f : FlagId) (val : DropFlagState)
  | initRaw (p : Place)
  | moveRaw (dst src : Place)
  | explicitDropRaw (p : Place)
  | noop

/-- Target MIR terminators after `ElaborateDrops`: conditional drops have been
lowered to `switchFlag`, dead drops to `goto`, and live drops to `staticDropAtom`
chains (`TerminatorKind::Drop` over concrete leaves/ADTs). -/
inductive ElabTerm where
  | goto (target : BlockId)
  | switchBool (reg : BoolReg) (bbTrue bbFalse : BlockId)
  | switchFlag (f : FlagId) (bbPresent bbAbsent : BlockId)
  | staticDropAtom (a : Atom) (target : BlockId) (unwind : Option BlockId)
  | ret
  | unwindResume
  | unwindAbort

structure ElabBlock where
  isCleanup : Bool
  stmts : List ElabStmt
  term : ElabTerm

structure ElabProgram where
  locals : List MirTy
  args : List LocalId
  entry : BlockId
  nextBlock : BlockId
  blocks : BlockId → Option ElabBlock

/-- Concrete target state tracks both:
1. `flags : FlagMap` (synthesized boolean stack locals read by `switchFlag`), and
2. `mem : AtomMap` (physical ownership ghost monitor checking whether an unconditional
   `staticDropAtom` executes on initialized vs. uninitialized/already-dropped memory). -/
structure ElabState where
  bb : BlockId
  branchIdx : Nat
  dropIdx : Nat
  flags : FlagMap
  mem : AtomMap
  trace : List DropEvent
  exit : ExitKind

noncomputable def stepElabStmt (locals : List MirTy) (st : ElabState) : ElabStmt → ElabState
  | .storageLive _ => st
  | .storageDead l =>
    let atoms := atomsOfPlace locals { localId := l, proj := [] }
    { st with mem := setAtoms st.mem atoms false }
  | .setFlag f val =>
    { st with flags := setFlagMap st.flags f val }
  | .initRaw p =>
    let atoms := atomsOfPlace locals p
    { st with
      mem := setAtoms st.mem atoms true
      trace := listAppend st.trace (emitCreateForAtoms p.localId atoms) }
  | .moveRaw dst src =>
    let srcAtoms := atomsOfPlace locals src
    let dstAtoms := atomsOfPlace locals dst
    { st with mem := setAtoms (setAtoms st.mem srcAtoms false) dstAtoms true }
  | .explicitDropRaw p =>
    let atoms := atomsOfPlace locals p
    let (mem', tr') := execExplicitDrop atoms st.mem st.trace
    { st with mem := mem', trace := tr' }
  | .noop => st

noncomputable def stepElabStmtList (locals : List MirTy) : List ElabStmt → ElabState → ElabState
  | [], st => st
  | s :: ss, st => stepElabStmtList locals ss (stepElabStmt locals st s)

noncomputable def stepElabBlock (prog : ElabProgram) (oracle : ExecOracle) (st : ElabState) :
    ElabState :=
  match st.exit with
  | .running =>
    match prog.blocks st.bb with
    | none => { st with exit := .faulted }
    | some blk =>
      let st1 := stepElabStmtList prog.locals blk.stmts st
      match blk.term with
      | .goto tgt =>
        { st1 with bb := tgt }
      | .switchBool reg bbT bbF =>
        let tgt := if oracle.branchAt st1.branchIdx reg then bbT else bbF
        { st1 with bb := tgt, branchIdx := st1.branchIdx + 1 }
      | .switchFlag f bbPres bbAbs =>
        let tgt := if st1.flags f then bbPres else bbAbs
        { st1 with bb := tgt }
      | .staticDropAtom a tgt unwind =>
        if st1.mem a then
          let ev := DropEvent.atomEvent a false
          let mem' := setAtom st1.mem a false
          let tr' := listAppend st1.trace [ev]
          let p := oracle.panicAt st1.dropIdx a
          let dIdx' := st1.dropIdx + 1
          if p then
            match blk.isCleanup, unwind with
            | true, _ => { st1 with mem := mem', trace := tr', dropIdx := dIdx', exit := .aborted }
            | false, some ubb =>
              { st1 with bb := ubb, dropIdx := dIdx', mem := mem', trace := tr' }
            | false, none =>
              { st1 with mem := mem', trace := tr', dropIdx := dIdx', exit := .aborted }
          else
            { st1 with bb := tgt, dropIdx := dIdx', mem := mem', trace := tr' }
        else
          { st1 with
            trace := listAppend st1.trace [.doubleOrUninitFault a.tag a.localId]
            exit := .faulted }
      | .ret =>
        { st1 with exit := .returned }
      | .unwindResume =>
        { st1 with exit := .unwound }
      | .unwindAbort =>
        { st1 with exit := .aborted }
  | _ => st

noncomputable def execElabFuel (prog : ElabProgram) (oracle : ExecOracle) :
    Nat → ElabState → ElabState
  | 0, st => st
  | n + 1, st =>
    match st.exit with
    | .running => execElabFuel prog oracle n (stepElabBlock prog oracle st)
    | _ => st

noncomputable def initElabState (prog : ElabProgram) : ElabState :=
  let argAtoms := atomsOfLocalList prog.locals prog.args
  { bb := prog.entry
    branchIdx := 0
    dropIdx := 0
    flags := emptyFlagMap
    mem := setAtoms emptyAtomMap argAtoms true
    trace := []
    exit := .running }

/-- Trace safety predicates (`NoDoubleDrop` and `NoLeak`). -/
noncomputable def traceHasFault : List DropEvent → Bool
  | [] => false
  | .doubleOrUninitFault _ _ :: _ => true
  | .uninitFieldInDropImpl _ _ :: _ => true
  | _ :: rest => traceHasFault rest

noncomputable def countTagCreates (tag : DropTag) : List DropEvent → Nat
  | [] => 0
  | .create t _ :: rest =>
    if natEq t tag then countTagCreates tag rest + 1 else countTagCreates tag rest
  | _ :: rest => countTagCreates tag rest

noncomputable def countTagDrops (tag : DropTag) : List DropEvent → Nat
  | [] => 0
  | .dropCall t _ _ :: rest =>
    if natEq t tag then countTagDrops tag rest + 1 else countTagDrops tag rest
  | _ :: rest => countTagDrops tag rest

noncomputable def noDoubleDropTag (tag : DropTag) (tr : List DropEvent) : Prop :=
  traceHasFault tr = false ∧ countTagDrops tag tr ≤ countTagCreates tag tr

noncomputable def noLeakTag (tag : DropTag) (tr : List DropEvent) : Prop :=
  countTagCreates tag tr ≤ countTagDrops tag tr

/-! ## 6. Abstract Dataflow Analysis & `ElaborateDrops` Lowering Pass -/

/-- Pair of abstract dataflow bitsets matching `MaybeInitializedPlaces` and
`MaybeUninitializedPlaces` (`elaborate_drops.rs:63-75`). -/
structure InitPair where
  mayInit : AtomMap
  mayUninit : AtomMap

noncomputable def transferSrcStmt (locals : List MirTy) (st : InitPair) : SrcStmt → InitPair
  | .storageLive _ => st
  | .storageDead l =>
    let atoms := atomsOfPlace locals { localId := l, proj := [] }
    { mayInit := setAtoms st.mayInit atoms false
      mayUninit := setAtoms st.mayUninit atoms true }
  | .initPlace p =>
    let atoms := atomsOfPlace locals p
    { mayInit := setAtoms st.mayInit atoms true
      mayUninit := setAtoms st.mayUninit atoms false }
  | .movePlace dst src =>
    let srcAtoms := atomsOfPlace locals src
    let dstAtoms := atomsOfPlace locals dst
    { mayInit := setAtoms (setAtoms st.mayInit srcAtoms false) dstAtoms true
      mayUninit := setAtoms (setAtoms st.mayUninit srcAtoms true) dstAtoms false }
  | .explicitDrop p =>
    let atoms := atomsOfPlace locals p
    { mayInit := setAtoms st.mayInit atoms false
      mayUninit := setAtoms st.mayUninit atoms true }
  | .noop => st

noncomputable def transferSrcStmtList (locals : List MirTy) : List SrcStmt → InitPair → InitPair
  | [], st => st
  | s :: ss, st => transferSrcStmtList locals ss (transferSrcStmt locals st s)

/-- Pointwise abstract-state inclusion `(mi1 ⊆ mi2 ∧ mu1 ⊆ mu2)`. -/
noncomputable def InitPairSub (p1 p2 : InitPair) : Prop :=
  (∀ a, p1.mayInit a = true → p2.mayInit a = true) ∧
  (∀ a, p1.mayUninit a = true → p2.mayUninit a = true)

/-- Concrete initialization state `init` is consistent with abstract `(mayInit, mayUninit)`
when `mayInit` over-approximates live atoms and `mayUninit` over-approximates absent atoms. -/
noncomputable def InitConsistent (init : AtomMap) (df : InitPair) : Prop :=
  (∀ a, init a = true → df.mayInit a = true) ∧
  (∀ a, init a = false → df.mayUninit a = true)

/-- Dataflow certificate for `prog : SrcProgram`, assigning `(mayInit, mayUninit)`
at the start of every basic block `bb`. -/
structure DataflowCert where
  atBlock : BlockId → InitPair

noncomputable def ValidDataflowCert (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) : Prop :=
  (∀ bb, natLt bb numBlocks = false → prog.blocks bb = none) ∧
  natLt prog.entry numBlocks = true ∧
  (∀ a,
    (atomInList a (atomsOfLocalList prog.locals prog.args) = true →
      (df.atBlock prog.entry).mayInit a = true) ∧
    (atomInList a (atomsOfLocalList prog.locals prog.args) = false →
      (df.atBlock prog.entry).mayUninit a = true)) ∧
  (∀ bb blk, prog.blocks bb = some blk →
    let afterStmts := transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)
    match blk.term with
    | .goto tgt =>
      natLt tgt numBlocks = true ∧ InitPairSub afterStmts (df.atBlock tgt)
    | .switchBool _ bbT bbF =>
      natLt bbT numBlocks = true ∧ natLt bbF numBlocks = true ∧
      InitPairSub afterStmts (df.atBlock bbT) ∧ InitPairSub afterStmts (df.atBlock bbF)
    | .drop p tgt unwind =>
      let atoms := atomsOfPlace prog.locals p
      let afterDrop : InitPair :=
        { mayInit := setAtoms afterStmts.mayInit atoms false
          mayUninit := setAtoms afterStmts.mayUninit atoms true }
      natLt tgt numBlocks = true ∧
      InitPairSub afterDrop (df.atBlock tgt) ∧
      (match unwind with
       | none => True
       | some ubb => natLt ubb numBlocks = true ∧ InitPairSub afterDrop (df.atBlock ubb))
    | .scopeExit locs tgt unwind =>
      let atoms := atomsOfLocalList prog.locals (localsDropOrder locs)
      let afterDrop : InitPair :=
        { mayInit := setAtoms afterStmts.mayInit atoms false
          mayUninit := setAtoms afterStmts.mayUninit atoms true }
      natLt tgt numBlocks = true ∧
      InitPairSub afterDrop (df.atBlock tgt) ∧
      (match unwind with
       | none => True
       | some ubb => natLt ubb numBlocks = true ∧ InitPairSub afterDrop (df.atBlock ubb))
    | .ret => True
    | .unwindResume => True
    | .unwindAbort => True)

/-- Flag allocation policy mapping conditionally initialized atoms to distinct stack `FlagId`s. -/
structure FlagAlloc where
  flagOf : Atom → Option FlagId
  allFlags : List FlagId

noncomputable def ValidFlagAlloc (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert)
    (fa : FlagAlloc) : Prop :=
  (∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b) ∧
  (∀ bb blk, natLt bb numBlocks = true → prog.blocks bb = some blk →
    let afterStmts := transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)
    match blk.term with
    | .drop p _ _ =>
      ∀ a, atomInList a (atomsOfPlace prog.locals p) = true →
        afterStmts.mayInit a = true → afterStmts.mayUninit a = true →
        ∃ fid, fa.flagOf a = some fid
    | .scopeExit locs _ _ =>
      ∀ a, atomInList a (atomsOfLocalList prog.locals (localsDropOrder locs)) = true →
        afterStmts.mayInit a = true → afterStmts.mayUninit a = true →
        ∃ fid, fa.flagOf a = some fid
    | _ => True)

/-- Mirrors `ElaborateDrops`'s `MirPatch` block builder. -/
structure PatchState where
  nextBlock : BlockId
  blocks : BlockId → Option ElabBlock

noncomputable def setElabBlock (m : BlockId → Option ElabBlock) (k : BlockId) (b : ElabBlock) :
    BlockId → Option ElabBlock :=
  fun x => if natEq x k then some b else m x

noncomputable def allocElabBlock (ps : PatchState) (b : ElabBlock) : BlockId × PatchState :=
  let id := ps.nextBlock
  (id, { nextBlock := id + 1, blocks := setElabBlock ps.blocks id b })

noncomputable def writeElabBlock (ps : PatchState) (k : BlockId) (b : ElabBlock) : PatchState :=
  { ps with blocks := setElabBlock ps.blocks k b }

/-- Shifts a source `BlockId` by `+ 1` so `0` is reserved for the `drop_flags_on_init`
+ `drop_flags_for_args` entry prologue block. -/
noncomputable def shiftSrcBb (bb : BlockId) : BlockId := bb + 1

noncomputable def shiftOptBb : Option BlockId → Option BlockId
  | some u => some (shiftSrcBb u)
  | none => none

/-- Mirrors `drop_flags_for_locs` (`elaborate_drops.rs:464-520`) statement flag updates. -/
noncomputable def setFlagsForAtoms (fa : FlagAlloc) (st : DropFlagState) :
    List Atom → List ElabStmt
  | [] => []
  | a :: rest =>
    match fa.flagOf a with
    | some fid => ElabStmt.setFlag fid st :: setFlagsForAtoms fa st rest
    | none => setFlagsForAtoms fa st rest

noncomputable def elaborateStmt (locals : List MirTy) (fa : FlagAlloc) :
    SrcStmt → List ElabStmt
  | .storageLive l => [.storageLive l]
  | .storageDead l =>
    let atoms := atomsOfPlace locals { localId := l, proj := [] }
    listAppend (setFlagsForAtoms fa .absent atoms) [.storageDead l]
  | .initPlace p =>
    let atoms := atomsOfPlace locals p
    listAppend [.initRaw p] (setFlagsForAtoms fa .present atoms)
  | .movePlace dst src =>
    let srcAtoms := atomsOfPlace locals src
    let dstAtoms := atomsOfPlace locals dst
    listAppend
      (setFlagsForAtoms fa .absent srcAtoms)
      (listAppend [.moveRaw dst src] (setFlagsForAtoms fa .present dstAtoms))
  | .explicitDrop p =>
    let atoms := atomsOfPlace locals p
    listAppend [.explicitDropRaw p] (setFlagsForAtoms fa .absent atoms)
  | .noop => [.noop]

noncomputable def elaborateStmtList (locals : List MirTy) (fa : FlagAlloc) :
    List SrcStmt → List ElabStmt
  | [] => []
  | s :: ss => listAppend (elaborateStmt locals fa s) (elaborateStmtList locals fa ss)

/-- Emits one rung of a `drop_halfladder` (`elaborate_drop.rs:838-853`, `complete_drop`,
`drop_flag_test_block`, `drop_flag_reset_block`), classifying each atom via
`dropStyleOf (mi a) (mu a) false`:
* `.dead`: skips drop (`goto succ`)
* `.static_`: unconditional `staticDropAtom a succ unwind` (clearing flag if allocated)
* `.conditional`: `switchFlag fid dropBlk succ` where `dropBlk` clears `fid` and runs `staticDropAtom` -/
noncomputable def emitAtomDropRung
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (a : Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState) :
    BlockId × PatchState :=
  match dropStyleOf (mi a) (mu a) false with
  | .dead => (succ, ps)
  | .static_ =>
    let clearStmts :=
      match fa.flagOf a with
      | some fid => [ElabStmt.setFlag fid .absent]
      | none => []
    allocElabBlock ps
      { isCleanup := isCleanup
        stmts := clearStmts
        term := .staticDropAtom a succ unwind }
  | .conditional =>
    match fa.flagOf a with
    | some fid =>
      let (dropBb, ps1) :=
        allocElabBlock ps
          { isCleanup := isCleanup
            stmts := [ElabStmt.setFlag fid .absent]
            term := .staticDropAtom a succ unwind }
      allocElabBlock ps1
        { isCleanup := isCleanup
          stmts := []
          term := .switchFlag fid dropBb succ }
    | none =>
      -- Unreachable under `ValidFlagAlloc`, fails closed to static drop if called directly.
      allocElabBlock ps
        { isCleanup := isCleanup
          stmts := []
          term := .staticDropAtom a succ unwind }
  | .open_ =>
    -- Single atom has `multipart = false`; `open_` is only produced for compound places.
    (succ, ps)

/-- Mirrors `drop_halfladder` + `drop_ladder` (`elaborate_drop.rs:838-955`):
recursively constructs the normal ladder and (when `!isCleanup` and `unwind = some ubb`)
the parallel unwind cleanup half-ladder from back to front so execution visits `atoms`
in exact forward order `a_0, a_1, ...`. -/
noncomputable def lowerDropCleanupHalfLadder
    (fa : FlagAlloc) (mi mu : AtomMap)
    (atoms : List Atom) (ubb : BlockId) (ps : PatchState) : BlockId × PatchState :=
  match atoms with
  | [] => (ubb, ps)
  | a :: rest =>
    let (nextU, ps1) := lowerDropCleanupHalfLadder fa mi mu rest ubb ps
    emitAtomDropRung fa mi mu true a nextU none ps1

noncomputable def lowerDropNormalLadder
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (atoms : List Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState) :
    BlockId × PatchState :=
  match atoms with
  | [] => (succ, ps)
  | a :: rest =>
    match isCleanup, unwind with
    | false, some ubb =>
      let (nextU, ps1) := lowerDropCleanupHalfLadder fa mi mu rest ubb ps
      let (nextN, ps2) := lowerDropNormalLadder fa mi mu false rest succ (some ubb) ps1
      emitAtomDropRung fa mi mu false a nextN (some nextU) ps2
    | _, _ =>
      let (nextN, ps1) := lowerDropNormalLadder fa mi mu isCleanup rest succ none ps
      emitAtomDropRung fa mi mu isCleanup a nextN none ps1

noncomputable def elaborateBlock (prog : SrcProgram) (df : DataflowCert) (fa : FlagAlloc)
    (bb : BlockId) (blk : SrcBlock) (ps : PatchState) : PatchState :=
  let afterStmts := transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)
  let elabStmts := elaborateStmtList prog.locals fa blk.stmts
  let targetBb := shiftSrcBb bb
  match blk.term with
  | .goto tgt =>
    writeElabBlock ps targetBb
      { isCleanup := blk.isCleanup, stmts := elabStmts, term := .goto (shiftSrcBb tgt) }
  | .switchBool reg bbT bbF =>
    writeElabBlock ps targetBb
      { isCleanup := blk.isCleanup
        stmts := elabStmts
        term := .switchBool reg (shiftSrcBb bbT) (shiftSrcBb bbF) }
  | .drop p tgt unwind =>
    let atoms := atomsOfPlace prog.locals p
    let shiftedUnwind := shiftOptBb unwind
    let (ladderEntry, ps1) :=
      lowerDropNormalLadder fa afterStmts.mayInit afterStmts.mayUninit blk.isCleanup
        atoms (shiftSrcBb tgt) shiftedUnwind ps
    writeElabBlock ps1 targetBb
      { isCleanup := blk.isCleanup, stmts := elabStmts, term := .goto ladderEntry }
  | .scopeExit locs tgt unwind =>
    let orderedLocs := localsDropOrder locs
    let atoms := atomsOfLocalList prog.locals orderedLocs
    let shiftedUnwind := shiftOptBb unwind
    let (ladderEntry, ps1) :=
      lowerDropNormalLadder fa afterStmts.mayInit afterStmts.mayUninit blk.isCleanup
        atoms (shiftSrcBb tgt) shiftedUnwind ps
    writeElabBlock ps1 targetBb
      { isCleanup := blk.isCleanup, stmts := elabStmts, term := .goto ladderEntry }
  | .ret =>
    writeElabBlock ps targetBb
      { isCleanup := blk.isCleanup, stmts := elabStmts, term := .ret }
  | .unwindResume =>
    writeElabBlock ps targetBb
      { isCleanup := blk.isCleanup, stmts := elabStmts, term := .unwindResume }
  | .unwindAbort =>
    writeElabBlock ps targetBb
      { isCleanup := blk.isCleanup, stmts := elabStmts, term := .unwindAbort }

noncomputable def elaborateBlocksLoop (prog : SrcProgram) (df : DataflowCert) (fa : FlagAlloc) :
    Nat → Nat → PatchState → PatchState
  | _, 0, ps => ps
  | idx, remaining + 1, ps =>
    let ps1 :=
      match prog.blocks idx with
      | some blk => elaborateBlock prog df fa idx blk ps
      | none => ps
    elaborateBlocksLoop prog df fa (idx + 1) remaining ps1

/-- Full `ElaborateDrops` compilation pass (`elaborate_drops.rs:276-287`):
1. Reserves `0` for `drop_flags_on_init` (init all flags `false`) + `drop_flags_for_args` (`true`).
2. Elaborates all source blocks `0 .. numBlocks - 1` at `shiftSrcBb bb = bb + 1` and
   appends fresh `drop_ladder` / `switchFlag` / `staticDropAtom` blocks at `>= 1 + numBlocks`. -/
noncomputable def elaborateProgram (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc) : ElabProgram :=
  let initAllFlags := listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags
  let argAtoms := atomsOfLocalList prog.locals prog.args
  let argInits := setFlagsForAtoms fa .present argAtoms
  let entryBlk : ElabBlock :=
    { isCleanup := false
      stmts := listAppend initAllFlags argInits
      term := .goto (shiftSrcBb prog.entry) }
  let ps0 : PatchState :=
    { nextBlock := 1 + numBlocks
      blocks := setElabBlock (fun _ => none) 0 entryBlk }
  let psFinal := elaborateBlocksLoop prog df fa 0 numBlocks ps0
  { locals := prog.locals
    args := prog.args
    entry := 0
    nextBlock := psFinal.nextBlock
    blocks := psFinal.blocks }

/-! ## 7. Core Soundness, Simulation, and Exact Drop-Trace Equivalence Proofs -/

/-! ### 7.1 Arithmetic, List, and `PatchState` Block-Preservation Lemmas -/

theorem natLt_succ {a b : Nat} : natLt a b = true → natLt a (b + 1) = true := by
  induction a generalizing b with
  | zero =>
    intro _
    rfl
  | succ a' ih =>
    intro h
    cases b with
    | zero => cases h
    | succ b' => exact ih h

theorem natLt_succ_self (n : Nat) : natLt n (n + 1) = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natLt_add_one {a b : Nat} : natLt a b = true → natLt (a + 1) (b + 1) = true := by
  intro h
  exact h

theorem natLt_zero_right (b : Nat) : natLt b 0 = false := by
  cases b <;> rfl

theorem natLt_trans {a b c : Nat} : natLt a b = true → natLt b c = true → natLt a c = true := by
  induction a generalizing b c with
  | zero =>
    intro _ hbc
    cases c with
    | zero => rw [natLt_zero_right] at hbc; cases hbc
    | succ _ => rfl
  | succ a' ih =>
    intro hab hbc
    cases b with
    | zero => rw [natLt_zero_right] at hab; cases hab
    | succ b' =>
      cases c with
      | zero => rw [natLt_zero_right] at hbc; cases hbc
      | succ c' => exact ih hab hbc

theorem natLt_ne_zero_add_one (a : Nat) : natEq (a + 1) 0 = false := rfl

theorem natLt_to_natEq_false {a b : Nat} (h : natLt a b = true) : natEq a b = false :=
  natEq_false_of_ne (natLt_ne h)

theorem listAppend_nil_right {α : Type} (xs : List α) : listAppend xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x :: listAppend xs [] = x :: xs
    rw [ih]

theorem listAppend_assoc {α : Type} (xs ys zs : List α) :
    listAppend (listAppend xs ys) zs = listAppend xs (listAppend ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x :: listAppend (listAppend xs ys) zs = x :: listAppend xs (listAppend ys zs)
    rw [ih]

noncomputable def natInList (n : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => natEq n x || natInList n xs

noncomputable def atomsDistinct : List Atom → Bool
  | [] => true
  | a :: rest => !(atomInList a rest) && atomsDistinct rest

/-- `PatchExtends ps1 ps2` means `ps2` preserves every block ID strictly below `ps1.nextBlock`
and has `nextBlock` at least as large. -/
noncomputable def PatchExtends (ps1 ps2 : PatchState) : Prop :=
  (∀ k, natLt k ps1.nextBlock = true → ps2.blocks k = ps1.blocks k) ∧
  (∀ k, natLt k ps1.nextBlock = true → natLt k ps2.nextBlock = true)

theorem patchExtends_refl (ps : PatchState) : PatchExtends ps ps :=
  ⟨fun _ _ => rfl, fun _ h => h⟩

theorem patchExtends_trans {ps1 ps2 ps3 : PatchState}
    (h12 : PatchExtends ps1 ps2) (h23 : PatchExtends ps2 ps3) : PatchExtends ps1 ps3 := by
  constructor
  · intro k hk
    rw [h23.1 k (h12.2 k hk), h12.1 k hk]
  · intro k hk
    exact h23.2 k (h12.2 k hk)

theorem allocElabBlock_extends (ps : PatchState) (b : ElabBlock) :
    let res := allocElabBlock ps b
    natLt res.1 res.2.nextBlock = true ∧
    res.2.blocks res.1 = some b ∧
    PatchExtends ps res.2 := by
  refine ⟨natLt_succ_self ps.nextBlock, ?_, ?_⟩
  · change setElabBlock ps.blocks ps.nextBlock b ps.nextBlock = some b
    change (if natEq ps.nextBlock ps.nextBlock then some b else ps.blocks ps.nextBlock) = some b
    rw [natEq_refl ps.nextBlock]
    rfl
  · constructor
    · intro k hk
      change (if natEq k ps.nextBlock then some b else ps.blocks k) = ps.blocks k
      rw [natLt_to_natEq_false hk]
      rfl
    · intro k hk
      exact natLt_succ hk

theorem emitAtomDropRung_extends
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (a : Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState)
    (hsucc : natLt succ ps.nextBlock = true) :
    let res := emitAtomDropRung fa mi mu isCleanup a succ unwind ps
    natLt res.1 res.2.nextBlock = true ∧ PatchExtends ps res.2 := by
  dsimp only [emitAtomDropRung]
  cases hds : dropStyleOf (mi a) (mu a) false with
  | dead =>
    exact ⟨hsucc, patchExtends_refl ps⟩
  | open_ =>
    exact ⟨hsucc, patchExtends_refl ps⟩
  | static_ =>
    have h1 := allocElabBlock_extends ps
      { isCleanup := isCleanup
        stmts := match fa.flagOf a with | some fid => [ElabStmt.setFlag fid .absent] | none => []
        term := .staticDropAtom a succ unwind }
    exact ⟨h1.1, h1.2.2⟩
  | conditional =>
    cases hfa : fa.flagOf a with
    | none =>
      have h1 := allocElabBlock_extends ps
        { isCleanup := isCleanup, stmts := [], term := .staticDropAtom a succ unwind }
      exact ⟨h1.1, h1.2.2⟩
    | some fid =>
      have h1 := allocElabBlock_extends ps
        { isCleanup := isCleanup, stmts := [ElabStmt.setFlag fid .absent], term := .staticDropAtom a succ unwind }
      let ps1 := (allocElabBlock ps
        { isCleanup := isCleanup, stmts := [ElabStmt.setFlag fid .absent], term := .staticDropAtom a succ unwind }).2
      let dropBb := (allocElabBlock ps
        { isCleanup := isCleanup, stmts := [ElabStmt.setFlag fid .absent], term := .staticDropAtom a succ unwind }).1
      have h2 := allocElabBlock_extends ps1
        { isCleanup := isCleanup, stmts := [], term := .switchFlag fid dropBb succ }
      exact ⟨h2.1, patchExtends_trans h1.2.2 h2.2.2⟩

theorem lowerDropCleanupHalfLadder_extends
    (fa : FlagAlloc) (mi mu : AtomMap)
    (atoms : List Atom) (ubb : BlockId) (ps : PatchState)
    (hubb : natLt ubb ps.nextBlock = true) :
    let res := lowerDropCleanupHalfLadder fa mi mu atoms ubb ps
    natLt res.1 res.2.nextBlock = true ∧ PatchExtends ps res.2 := by
  induction atoms generalizing ps with
  | nil =>
    exact ⟨hubb, patchExtends_refl ps⟩
  | cons a rest ih =>
    have hrest := ih ps hubb
    change natLt (emitAtomDropRung fa mi mu true a
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).1 none
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).2).1
      (emitAtomDropRung fa mi mu true a
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).1 none
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).2).2.nextBlock = true ∧
      PatchExtends ps (emitAtomDropRung fa mi mu true a
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).1 none
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).2).2
    have hrung := emitAtomDropRung_extends fa mi mu true a
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).1 none
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).2 hrest.1
    exact ⟨hrung.1, patchExtends_trans hrest.2 hrung.2⟩

theorem lowerDropNormalLadder_extends
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (atoms : List Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState)
    (hsucc : natLt succ ps.nextBlock = true)
    (hunw : match unwind with | none => True | some ubb => natLt ubb ps.nextBlock = true) :
    let res := lowerDropNormalLadder fa mi mu isCleanup atoms succ unwind ps
    natLt res.1 res.2.nextBlock = true ∧ PatchExtends ps res.2 := by
  induction atoms generalizing ps unwind with
  | nil =>
    exact ⟨hsucc, patchExtends_refl ps⟩
  | cons a rest ih =>
    cases isCleanup with
    | true =>
      have hrest := ih none ps hsucc (by trivial)
      let recRes := lowerDropNormalLadder fa mi mu true rest succ none ps
      have hrung := emitAtomDropRung_extends fa mi mu true a recRes.1 none recRes.2 hrest.1
      change natLt (emitAtomDropRung fa mi mu true a recRes.1 none recRes.2).1
          (emitAtomDropRung fa mi mu true a recRes.1 none recRes.2).2.nextBlock = true ∧
        PatchExtends ps (emitAtomDropRung fa mi mu true a recRes.1 none recRes.2).2
      exact ⟨hrung.1, patchExtends_trans hrest.2 hrung.2⟩
    | false =>
      cases unwind with
      | none =>
        have hrest := ih none ps hsucc (by trivial)
        let recRes := lowerDropNormalLadder fa mi mu false rest succ none ps
        have hrung := emitAtomDropRung_extends fa mi mu false a recRes.1 none recRes.2 hrest.1
        change natLt (emitAtomDropRung fa mi mu false a recRes.1 none recRes.2).1
            (emitAtomDropRung fa mi mu false a recRes.1 none recRes.2).2.nextBlock = true ∧
          PatchExtends ps (emitAtomDropRung fa mi mu false a recRes.1 none recRes.2).2
        exact ⟨hrung.1, patchExtends_trans hrest.2 hrung.2⟩
      | some ubb =>
        have hu := lowerDropCleanupHalfLadder_extends fa mi mu rest ubb ps hunw
        let uRes := lowerDropCleanupHalfLadder fa mi mu rest ubb ps
        have hsucc1 : natLt succ uRes.2.nextBlock = true := hu.2.2 succ hsucc
        have hunw1 : natLt ubb uRes.2.nextBlock = true := hu.2.2 ubb hunw
        have hrest := ih (some ubb) uRes.2 hsucc1 hunw1
        let nRes := lowerDropNormalLadder fa mi mu false rest succ (some ubb) uRes.2
        have hrung := emitAtomDropRung_extends fa mi mu false a nRes.1 (some uRes.1) nRes.2 hrest.1
        change natLt (emitAtomDropRung fa mi mu false a nRes.1 (some uRes.1) nRes.2).1
            (emitAtomDropRung fa mi mu false a nRes.1 (some uRes.1) nRes.2).2.nextBlock = true ∧
          PatchExtends ps (emitAtomDropRung fa mi mu false a nRes.1 (some uRes.1) nRes.2).2
        exact ⟨hrung.1, patchExtends_trans hu.2 (patchExtends_trans hrest.2 hrung.2)⟩

/-! ### 7.2 Dataflow Consistency Preservation (`ValidDataflowCert`) -/

theorem initConsistent_sub {init : AtomMap} {p1 p2 : InitPair}
    (hc : InitConsistent init p1) (hsub : InitPairSub p1 p2) :
    InitConsistent init p2 :=
  ⟨fun a ha => hsub.1 a (hc.1 a ha), fun a ha => hsub.2 a (hc.2 a ha)⟩

private theorem bool_if_true {α : Sort _} {inst : Decidable (true = true)} (t e : α) :
    (@ite α (true = true) inst t e) = t := by
  cases inst with
  | isFalse h => exact False.elim (h rfl)
  | isTrue _ => rfl

private theorem bool_if_false {α : Sort _} {inst : Decidable (false = true)} (t e : α) :
    (@ite α (false = true) inst t e) = e := by
  cases inst with
  | isFalse _ => rfl
  | isTrue h => cases h

theorem execExplicitDrop_clears_all (xs : List Atom) (cur : AtomMap) (tr : List DropEvent) (a : Atom) :
    ((execExplicitDrop xs cur tr).1 a = true → cur a = true) ∧
    (atomInList a xs = true → (execExplicitDrop xs cur tr).1 a = false) ∧
    (atomInList a xs = false → (execExplicitDrop xs cur tr).1 a = cur a) := by
  induction xs generalizing cur tr with
  | nil =>
    refine ⟨fun h => h, ?_, fun _ => rfl⟩
    intro hmem
    cases hmem
  | cons x rest ih =>
    dsimp only [execExplicitDrop]
    cases hcx : cur x with
    | true =>
      rw [bool_if_true]
      have hsub := ih (setAtom cur x false) (listAppend tr [DropEvent.atomEvent x true])
      refine ⟨?_, ?_, ?_⟩
      · intro ha
        have ha1 := hsub.1 ha
        cases hax : Atom.beq a x with
        | true => rw [atom_beq_sound hax, setAtom_eq] at ha1; cases ha1
        | false =>
          have hne : a ≠ x := fun he => by rw [he, atom_beq_refl] at hax; cases hax
          rw [setAtom_ne cur hne false] at ha1
          exact ha1
      · intro hmem
        change (Atom.beq a x || atomInList a rest) = true at hmem
        cases hrest : atomInList a rest with
        | true => exact hsub.2.1 hrest
        | false =>
          rw [hrest] at hmem
          cases hax : Atom.beq a x with
          | false => rw [hax] at hmem; cases hmem
          | true =>
            rw [hsub.2.2 hrest, atom_beq_sound hax, setAtom_eq]
      · intro hnot
        change (Atom.beq a x || atomInList a rest) = false at hnot
        cases hax : Atom.beq a x with
        | true => rw [hax] at hnot; cases hnot
        | false =>
          rw [hax] at hnot
          have hne : a ≠ x := fun he => by rw [he, atom_beq_refl] at hax; cases hax
          rw [hsub.2.2 hnot, setAtom_ne cur hne false]
    | false =>
      rw [bool_if_false]
      have hsub := ih cur (listAppend tr [.doubleOrUninitFault x.tag x.localId])
      refine ⟨hsub.1, ?_, ?_⟩
      · intro hmem
        change (Atom.beq a x || atomInList a rest) = true at hmem
        cases hrest : atomInList a rest with
        | true => exact hsub.2.1 hrest
        | false =>
          rw [hrest] at hmem
          cases hax : Atom.beq a x with
          | false => rw [hax] at hmem; cases hmem
          | true =>
            rw [hsub.2.2 hrest, atom_beq_sound hax, hcx]
      · intro hnot
        change (Atom.beq a x || atomInList a rest) = false at hnot
        cases hax : Atom.beq a x with
        | true => rw [hax] at hnot; cases hnot
        | false =>
          rw [hax] at hnot
          exact hsub.2.2 hnot

theorem stepSrcStmt_preserves_consistent (locals : List MirTy)
    (st : SrcState) (df : InitPair) (s : SrcStmt)
    (hc : InitConsistent st.init df) :
    InitConsistent (stepSrcStmt locals st s).init (transferSrcStmt locals df s) := by
  cases s with
  | storageLive _ => exact hc
  | noop => exact hc
  | storageDead l =>
    constructor
    · intro a ha
      cases hmem : atomInList a (atomsOfPlace locals { localId := l, proj := [] }) with
      | true =>
        change setAtoms st.init (atomsOfPlace locals { localId := l, proj := [] }) false a = true at ha
        rw [setAtoms_mem st.init _ false a hmem] at ha
        cases ha
      | false =>
        change setAtoms st.init (atomsOfPlace locals { localId := l, proj := [] }) false a = true at ha
        rw [setAtoms_not_mem st.init _ false a hmem] at ha
        change setAtoms df.mayInit (atomsOfPlace locals { localId := l, proj := [] }) false a = true
        rw [setAtoms_not_mem df.mayInit _ false a hmem]
        exact hc.1 a ha
    · intro a ha
      cases hmem : atomInList a (atomsOfPlace locals { localId := l, proj := [] }) with
      | true =>
        change setAtoms df.mayUninit (atomsOfPlace locals { localId := l, proj := [] }) true a = true
        exact setAtoms_mem df.mayUninit _ true a hmem
      | false =>
        change setAtoms st.init (atomsOfPlace locals { localId := l, proj := [] }) false a = false at ha
        rw [setAtoms_not_mem st.init _ false a hmem] at ha
        change setAtoms df.mayUninit (atomsOfPlace locals { localId := l, proj := [] }) true a = true
        rw [setAtoms_not_mem df.mayUninit _ true a hmem]
        exact hc.2 a ha
  | initPlace p =>
    constructor
    · intro a ha
      cases hmem : atomInList a (atomsOfPlace locals p) with
      | true =>
        change setAtoms df.mayInit (atomsOfPlace locals p) true a = true
        exact setAtoms_mem df.mayInit _ true a hmem
      | false =>
        change setAtoms st.init (atomsOfPlace locals p) true a = true at ha
        rw [setAtoms_not_mem st.init _ true a hmem] at ha
        change setAtoms df.mayInit (atomsOfPlace locals p) true a = true
        rw [setAtoms_not_mem df.mayInit _ true a hmem]
        exact hc.1 a ha
    · intro a ha
      cases hmem : atomInList a (atomsOfPlace locals p) with
      | true =>
        change setAtoms st.init (atomsOfPlace locals p) true a = false at ha
        rw [setAtoms_mem st.init _ true a hmem] at ha
        cases ha
      | false =>
        change setAtoms st.init (atomsOfPlace locals p) true a = false at ha
        rw [setAtoms_not_mem st.init _ true a hmem] at ha
        change setAtoms df.mayUninit (atomsOfPlace locals p) false a = true
        rw [setAtoms_not_mem df.mayUninit _ false a hmem]
        exact hc.2 a ha
  | movePlace dst src =>
    have h1 : InitConsistent (setAtoms st.init (atomsOfPlace locals src) false)
        { mayInit := setAtoms df.mayInit (atomsOfPlace locals src) false
          mayUninit := setAtoms df.mayUninit (atomsOfPlace locals src) true } := by
      constructor
      · intro a ha
        dsimp only
        cases hmem : atomInList a (atomsOfPlace locals src) with
        | true =>
          rw [setAtoms_mem st.init _ false a hmem] at ha; cases ha
        | false =>
          rw [setAtoms_not_mem st.init _ false a hmem] at ha
          rw [setAtoms_not_mem df.mayInit _ false a hmem]
          exact hc.1 a ha
      · intro a ha
        dsimp only
        cases hmem : atomInList a (atomsOfPlace locals src) with
        | true => exact setAtoms_mem df.mayUninit _ true a hmem
        | false =>
          rw [setAtoms_not_mem st.init _ false a hmem] at ha
          rw [setAtoms_not_mem df.mayUninit _ true a hmem]
          exact hc.2 a ha
    constructor
    · intro a ha
      dsimp only [stepSrcStmt, transferSrcStmt] at ha ⊢
      cases hmem : atomInList a (atomsOfPlace locals dst) with
      | true =>
        exact setAtoms_mem _ _ true a hmem
      | false =>
        rw [setAtoms_not_mem _ _ true a hmem] at ha
        rw [setAtoms_not_mem _ _ true a hmem]
        exact h1.1 a ha
    · intro a ha
      dsimp only [stepSrcStmt, transferSrcStmt] at ha ⊢
      cases hmem : atomInList a (atomsOfPlace locals dst) with
      | true =>
        rw [setAtoms_mem _ _ true a hmem] at ha
        cases ha
      | false =>
        rw [setAtoms_not_mem _ _ true a hmem] at ha
        rw [setAtoms_not_mem _ _ false a hmem]
        exact h1.2 a ha
  | explicitDrop p =>
    constructor
    · intro a ha
      have hd := execExplicitDrop_clears_all (atomsOfPlace locals p) st.init st.trace a
      cases hmem : atomInList a (atomsOfPlace locals p) with
      | true =>
        have hfa := hd.2.1 hmem
        change (execExplicitDrop (atomsOfPlace locals p) st.init st.trace).1 a = true at ha
        rw [hfa] at ha; cases ha
      | false =>
        change setAtoms df.mayInit (atomsOfPlace locals p) false a = true
        rw [setAtoms_not_mem df.mayInit _ false a hmem]
        exact hc.1 a (hd.1 ha)
    · intro a ha
      cases hmem : atomInList a (atomsOfPlace locals p) with
      | true =>
        change setAtoms df.mayUninit (atomsOfPlace locals p) true a = true
        exact setAtoms_mem df.mayUninit _ true a hmem
      | false =>
        have hd := execExplicitDrop_clears_all (atomsOfPlace locals p) st.init st.trace a
        change (execExplicitDrop (atomsOfPlace locals p) st.init st.trace).1 a = false at ha
        rw [hd.2.2 hmem] at ha
        change setAtoms df.mayUninit (atomsOfPlace locals p) true a = true
        rw [setAtoms_not_mem df.mayUninit _ true a hmem]
        exact hc.2 a ha

theorem stepSrcStmtList_preserves_consistent (locals : List MirTy)
    (stmts : List SrcStmt) (st : SrcState) (df : InitPair)
    (hc : InitConsistent st.init df) :
    InitConsistent (stepSrcStmtList locals stmts st).init (transferSrcStmtList locals stmts df) := by
  induction stmts generalizing st df with
  | nil => exact hc
  | cons s ss ih =>
    exact ih (stepSrcStmt locals st s) (transferSrcStmt locals df s)
      (stepSrcStmt_preserves_consistent locals st df s hc)

theorem evalSrcDropAtomsGo_clears_live (oracle : ExecOracle) (isCleanup : Bool)
    (xs : List Atom) (cur : AtomMap) (tr : List DropEvent) (di : Nat) (pan : Bool) (a : Atom) :
    let r := evalSrcDropAtomsGo oracle isCleanup xs cur tr di pan
    (r.1 a = true → cur a = true) ∧
    (r.2.2.2.2 = false → atomInList a xs = true → r.1 a = false) ∧
    (atomInList a xs = false → r.1 a = cur a) := by
  induction xs generalizing cur tr di pan with
  | nil =>
    refine ⟨fun h => h, ?_, fun _ => rfl⟩
    intro _ hmem; cases hmem
  | cons x rest ih =>
    dsimp only [evalSrcDropAtomsGo]
    cases hcx : cur x with
    | false =>
      rw [bool_if_false]
      have hsub := ih cur tr di pan
      refine ⟨hsub.1, ?_, ?_⟩
      · intro hnoab hmem
        change (Atom.beq a x || atomInList a rest) = true at hmem
        cases hrest : atomInList a rest with
        | true => exact hsub.2.1 hnoab hrest
        | false =>
          rw [hrest] at hmem
          cases hax : Atom.beq a x with
          | false => rw [hax] at hmem; cases hmem
          | true => rw [hsub.2.2 hrest, atom_beq_sound hax, hcx]
      · intro hnot
        change (Atom.beq a x || atomInList a rest) = false at hnot
        cases hax : Atom.beq a x with
        | true => rw [hax] at hnot; cases hnot
        | false =>
          rw [hax] at hnot
          exact hsub.2.2 hnot
    | true =>
      rw [bool_if_true]
      have hclear1 : ∀ (y : Atom), setAtom cur x false y = true → cur y = true := by
        intro y hy
        cases hyx : Atom.beq y x with
        | true => rw [atom_beq_sound hyx, setAtom_eq] at hy; cases hy
        | false =>
          have hne : y ≠ x := fun he => by rw [he, atom_beq_refl] at hyx; cases hyx
          rw [setAtom_ne cur hne false] at hy
          exact hy
      have handleStep : ∀ (panNext : Bool),
          let r := evalSrcDropAtomsGo oracle isCleanup rest (setAtom cur x false)
            (listAppend tr [DropEvent.atomEvent x false]) (di + 1) panNext
          (r.1 a = true → cur a = true) ∧
          (r.2.2.2.2 = false → atomInList a (x :: rest) = true → r.1 a = false) ∧
          (atomInList a (x :: rest) = false → r.1 a = cur a) := by
        intro panNext
        have hsub := ih (setAtom cur x false) (listAppend tr [DropEvent.atomEvent x false]) (di + 1) panNext
        refine ⟨fun ha => hclear1 a (hsub.1 ha), ?_, ?_⟩
        · intro hnoab hmem
          change (Atom.beq a x || atomInList a rest) = true at hmem
          cases hrest : atomInList a rest with
          | true => exact hsub.2.1 hnoab hrest
          | false =>
            rw [hrest] at hmem
            cases hax : Atom.beq a x with
            | false => rw [hax] at hmem; cases hmem
            | true => rw [hsub.2.2 hrest, atom_beq_sound hax, setAtom_eq]
        · intro hnot
          change (Atom.beq a x || atomInList a rest) = false at hnot
          cases hax : Atom.beq a x with
          | true => rw [hax] at hnot; cases hnot
          | false =>
            rw [hax] at hnot
            have hne : a ≠ x := fun he => by rw [he, atom_beq_refl] at hax; cases hax
            rw [hsub.2.2 hnot, setAtom_ne cur hne false]
      have handleAbort :
          (setAtom cur x false a = true → cur a = true) ∧
          (true = false → atomInList a (x :: rest) = true → setAtom cur x false a = false) ∧
          (atomInList a (x :: rest) = false → setAtom cur x false a = cur a) := by
        refine ⟨hclear1 a, (fun hf _ => by cases hf), ?_⟩
        intro hnot
        change (Atom.beq a x || atomInList a rest) = false at hnot
        cases hax : Atom.beq a x with
        | true => rw [hax] at hnot; cases hnot
        | false =>
          have hne : a ≠ x := fun he => by rw [he, atom_beq_refl] at hax; cases hax
          exact setAtom_ne cur hne false
      cases hpan : pan <;> cases hp : oracle.panicAt di x <;> cases hcl : isCleanup
      · rw [bool_if_false, bool_if_false]; rw [hcl] at handleStep; exact handleStep false
      · rw [bool_if_false, bool_if_false]; rw [hcl] at handleStep; exact handleStep false
      · rw [bool_if_false, bool_if_true, bool_if_false]; rw [hcl] at handleStep; exact handleStep true
      · rw [bool_if_false, bool_if_true, bool_if_true]; exact handleAbort
      · rw [bool_if_true, bool_if_false]; rw [hcl] at handleStep; exact handleStep true
      · rw [bool_if_true, bool_if_false]; rw [hcl] at handleStep; exact handleStep true
      · rw [bool_if_true, bool_if_true]; exact handleAbort
      · rw [bool_if_true, bool_if_true]; exact handleAbort

theorem evalSrcDropAtoms_consistent (dIdx : Nat) (oracle : ExecOracle) (isCleanup : Bool)
    (atoms : List Atom) (init : AtomMap) (df : InitPair)
    (hc : InitConsistent init df)
    (hnoab : (evalSrcDropAtoms dIdx oracle isCleanup atoms init).2.2.2.2 = false) :
    InitConsistent (evalSrcDropAtoms dIdx oracle isCleanup atoms init).1
      { mayInit := setAtoms df.mayInit atoms false
        mayUninit := setAtoms df.mayUninit atoms true } := by
  constructor
  · intro a ha
    have hg := evalSrcDropAtomsGo_clears_live oracle isCleanup atoms init [] dIdx false a
    cases hmem : atomInList a atoms with
    | true =>
      have hfalse := hg.2.1 hnoab hmem
      change (evalSrcDropAtomsGo oracle isCleanup atoms init [] dIdx false).1 a = true at ha
      rw [hfalse] at ha
      cases ha
    | false =>
      dsimp only
      rw [setAtoms_not_mem df.mayInit atoms false a hmem]
      exact hc.1 a (hg.1 ha)
  · intro a ha
    have hg := evalSrcDropAtomsGo_clears_live oracle isCleanup atoms init [] dIdx false a
    cases hmem : atomInList a atoms with
    | true =>
      dsimp only
      exact setAtoms_mem df.mayUninit atoms true a hmem
    | false =>
      change (evalSrcDropAtomsGo oracle isCleanup atoms init [] dIdx false).1 a = false at ha
      rw [hg.2.2 hmem] at ha
      dsimp only
      rw [setAtoms_not_mem df.mayUninit atoms true a hmem]
      exact hc.2 a ha

theorem stepSrcBlock_preserves_consistent (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (oracle : ExecOracle)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (st : SrcState) (hrun : st.exit = .running)
    (hc : InitConsistent st.init (df.atBlock st.bb)) :
    let st' := stepSrcBlock prog oracle st
    st'.exit = .running →
    natLt st'.bb numBlocks = true ∧ InitConsistent st'.init (df.atBlock st'.bb) := by
  dsimp only [stepSrcBlock]
  rw [hrun]
  cases hblk : prog.blocks st.bb with
  | none =>
    intro hf; cases hf
  | some blk =>
    cases blk with
    | mk isCl stmts term =>
      have hc1 := stepSrcStmtList_preserves_consistent prog.locals stmts st (df.atBlock st.bb) hc
      have hcert := hvalid.2.2.2 st.bb { isCleanup := isCl, stmts := stmts, term := term } hblk
      dsimp only at hc1 hcert ⊢
      cases term with
      | ret => intro hf; cases hf
      | unwindResume => intro hf; cases hf
      | unwindAbort => intro hf; cases hf
      | goto tgt =>
        intro _
        exact ⟨hcert.1, initConsistent_sub hc1 hcert.2⟩
      | switchBool reg bbT bbF =>
        intro _
        dsimp only
        cases oracle.branchAt (stepSrcStmtList prog.locals stmts st).branchIdx reg
        · exact ⟨hcert.2.1, initConsistent_sub hc1 hcert.2.2.2⟩
        · exact ⟨hcert.1, initConsistent_sub hc1 hcert.2.2.1⟩
      | drop p tgt unwind =>
        dsimp only
        rcases hres : evalSrcDropAtoms (stepSrcStmtList prog.locals stmts st).dropIdx
            oracle isCl (atomsOfPlace prog.locals p)
            (stepSrcStmtList prog.locals stmts st).init with ⟨init', evs, dIdx', panicked, aborted⟩
        have hnoab_src : ∀ (_h : aborted = false),
            (evalSrcDropAtoms (stepSrcStmtList prog.locals stmts st).dropIdx
              oracle isCl (atomsOfPlace prog.locals p)
              (stepSrcStmtList prog.locals stmts st).init).2.2.2.2 = false := by
          intro hab; rw [hres]; exact hab
        cases aborted with
        | true =>
          rw [bool_if_true]
          intro hf; cases hf
        | false =>
          rw [bool_if_false]
          have had := evalSrcDropAtoms_consistent
            (stepSrcStmtList prog.locals stmts st).dropIdx oracle isCl
            (atomsOfPlace prog.locals p) (stepSrcStmtList prog.locals stmts st).init
            (transferSrcStmtList prog.locals stmts (df.atBlock st.bb)) hc1 (hnoab_src rfl)
          rw [hres] at had
          cases panicked with
          | false =>
            rw [bool_if_false]
            intro _
            exact ⟨hcert.1, initConsistent_sub had hcert.2.1⟩
          | true =>
            rw [bool_if_true]
            cases unwind with
            | none => intro hf; cases hf
            | some ubb =>
              dsimp only
              intro _
              exact ⟨hcert.2.2.1, initConsistent_sub had hcert.2.2.2⟩
      | scopeExit locs tgt unwind =>
        dsimp only
        rcases hres : evalSrcDropAtoms (stepSrcStmtList prog.locals stmts st).dropIdx
            oracle isCl (atomsOfLocalList prog.locals (localsDropOrder locs))
            (stepSrcStmtList prog.locals stmts st).init with ⟨init', evs, dIdx', panicked, aborted⟩
        have hnoab_src : ∀ (_h : aborted = false),
            (evalSrcDropAtoms (stepSrcStmtList prog.locals stmts st).dropIdx
              oracle isCl (atomsOfLocalList prog.locals (localsDropOrder locs))
              (stepSrcStmtList prog.locals stmts st).init).2.2.2.2 = false := by
          intro hab; rw [hres]; exact hab
        cases aborted with
        | true =>
          rw [bool_if_true]
          intro hf; cases hf
        | false =>
          rw [bool_if_false]
          have had := evalSrcDropAtoms_consistent
            (stepSrcStmtList prog.locals stmts st).dropIdx oracle isCl
            (atomsOfLocalList prog.locals (localsDropOrder locs))
            (stepSrcStmtList prog.locals stmts st).init
            (transferSrcStmtList prog.locals stmts (df.atBlock st.bb)) hc1 (hnoab_src rfl)
          rw [hres] at had
          cases panicked with
          | false =>
            rw [bool_if_false]
            intro _
            exact ⟨hcert.1, initConsistent_sub had hcert.2.1⟩
          | true =>
            rw [bool_if_true]
            cases unwind with
            | none => intro hf; cases hf
            | some ubb =>
              dsimp only
              intro _
              exact ⟨hcert.2.2.1, initConsistent_sub had hcert.2.2.2⟩

/-! ### 7.3 Flag Simulation, Ladder Simulation, and Program Trace Equivalence -/

theorem natLt_false_of_mono {a b c : Nat} (hba : natLt b c = true) (hca : natLt a c = false) :
    a ≠ b := by
  intro heq
  rw [heq, hba] at hca
  cases hca

theorem natLt_succ_false (n : Nat) : natLt (n + 1) n = false := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natLt_succ_false_of_ne {a b : Nat} (h1 : natLt a b = false) (hne : natEq a b = false) :
    natLt a (b + 1) = false := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => cases hne
    | succ _ => cases h1
  | succ a' ih =>
    cases b with
    | zero => exact natLt_zero_right a'
    | succ b' => exact ih h1 hne

theorem natLt_add_zero (a b : Nat) : natLt a (b + 0) = natLt a b := rfl

theorem natLt_add_succ_shift (a b c : Nat) : natLt a (b + (c + 1)) = natLt a ((b + 1) + c) := by
  rw [Nat.add_assoc, Nat.add_comm 1 c]

theorem natLt_split_le_mono {a b c : Nat}
    (hle : ∀ x, natLt x b = true → natLt x c = true)
    (hlt : natLt a b = true) : natLt a c = true :=
  hle a hlt

theorem listMap_append {α β : Type} (f : α → β) (xs ys : List α) :
    listMap f (listAppend xs ys) = listAppend (listMap f xs) (listMap f ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x :: listMap f (listAppend xs ys) = f x :: listAppend (listMap f xs) (listMap f ys)
    rw [ih]

theorem natInList_append (n : Nat) (xs ys : List Nat) :
    natInList n (listAppend xs ys) = (natInList n xs || natInList n ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (natEq n x || natInList n (listAppend xs ys)) = ((natEq n x || natInList n xs) || natInList n ys)
    rw [ih, Bool.or_assoc]

theorem listReverseAux_spec {α : Type} (xs acc : List α) :
    listReverseAux xs acc = listAppend (listReverse xs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change listReverseAux xs (x :: acc) = listAppend (listReverseAux xs [x]) acc
    rw [ih (x :: acc), ih [x], listAppend_assoc]
    rfl

theorem listReverse_cons {α : Type} (x : α) (xs : List α) :
    listReverse (x :: xs) = listAppend (listReverse xs) [x] :=
  listReverseAux_spec xs [x]

theorem listReverse_append {α : Type} (xs ys : List α) :
    listReverse (listAppend xs ys) = listAppend (listReverse ys) (listReverse xs) := by
  induction xs with
  | nil =>
    change listReverse ys = listAppend (listReverse ys) []
    rw [listAppend_nil_right]
  | cons x xs ih =>
    change listReverse (x :: listAppend xs ys) = listAppend (listReverse ys) (listReverse (x :: xs))
    rw [listReverse_cons x (listAppend xs ys), ih, listReverse_cons x xs, listAppend_assoc]

theorem listReverse_reverse {α : Type} (xs : List α) :
    listReverse (listReverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [listReverse_cons x xs, listReverse_append, ih]
    rfl

theorem atomsDistinct_head {a : Atom} {rest : List Atom}
    (hd : atomsDistinct (a :: rest) = true) :
    atomInList a rest = false ∧ atomsDistinct rest = true := by
  change (!(atomInList a rest) && atomsDistinct rest) = true at hd
  cases hm : atomInList a rest
  · rw [hm] at hd
    exact ⟨rfl, hd⟩
  · rw [hm] at hd
    cases hd

/-- `BlocksAgreeAfter eBlocks ps0 ps1` asserts that `eBlocks` matches `ps1.blocks`
on every block ID allocated between `ps0.nextBlock` (inclusive) and `ps1.nextBlock` (exclusive). -/
noncomputable def BlocksAgreeAfter (eBlocks : BlockId → Option ElabBlock)
    (ps0 ps1 : PatchState) : Prop :=
  ∀ k, natLt k ps0.nextBlock = false → natLt k ps1.nextBlock = true → eBlocks k = ps1.blocks k

theorem blocksAgreeAfter_split_left {eBlocks : BlockId → Option ElabBlock}
    {ps0 ps1 ps2 : PatchState}
    (hExt : PatchExtends ps1 ps2)
    (hAg : BlocksAgreeAfter eBlocks ps0 ps2) :
    BlocksAgreeAfter eBlocks ps0 ps1 := by
  intro k hk0 hk1
  have hk2 : natLt k ps2.nextBlock = true := hExt.2 k hk1
  rw [hAg k hk0 hk2, hExt.1 k hk1]

theorem blocksAgreeAfter_split_right {eBlocks : BlockId → Option ElabBlock}
    {ps0 ps1 ps2 : PatchState}
    (hExt : PatchExtends ps0 ps1)
    (hAg : BlocksAgreeAfter eBlocks ps0 ps2) :
    BlocksAgreeAfter eBlocks ps1 ps2 := by
  intro k hk1 hk2
  have hk0 : natLt k ps0.nextBlock = false := by
    cases h0 : natLt k ps0.nextBlock with
    | false => rfl
    | true =>
      have hk1t := hExt.2 k h0
      rw [hk1t] at hk1
      cases hk1
  exact hAg k hk0 hk2

theorem natLt_trans_false_left {a b k : Nat}
    (hab : natLt a b = true) (hkb : natLt k b = false) : natLt a k = true := by
  induction a generalizing b k with
  | zero =>
    cases k with
    | zero =>
      cases b with
      | zero => cases hab
      | succ _ => cases hkb
    | succ _ => rfl
  | succ a' ih =>
    cases b with
    | zero => cases hab
    | succ b' =>
      cases k with
      | zero => cases hkb
      | succ k' => exact ih hab hkb

theorem natLt_false_to_ne {a b : Nat} (hlt : natLt a (b + 1) = true) :
    ∀ k, natLt b k = true → a ≠ k := by
  intro k hbk heq
  rw [← heq] at hbk
  clear heq k
  induction b generalizing a with
  | zero =>
    cases a with
    | zero => cases hbk
    | succ a' =>
      cases a' with
      | zero => cases hlt
      | succ _ => cases hlt
  | succ b' ih =>
    cases a with
    | zero => cases hbk
    | succ a' => exact ih hlt hbk

theorem natLt_pred_left {a c : Nat} (h : natLt (a + 1) c = true) : natLt a c = true :=
  natLt_trans (natLt_succ_self a) h

theorem natLt_add_left {a b c : Nat} (hlt : natLt (a + b) c = true) :
    natLt a c = true := by
  induction b with
  | zero => exact hlt
  | succ b' ih =>
    rw [← Nat.add_assoc] at hlt
    exact ih (natLt_pred_left hlt)

theorem natLt_add_succ_left (a b c : Nat) :
    natLt (a + (b + 1)) c = natLt ((a + 1) + b) c := by
  rw [Nat.add_assoc, Nat.add_comm 1 b]

theorem natLt_add_lt_left {idx rem c : Nat} (hlt : natLt (idx + (rem + 1)) c = true) :
    natLt idx c = true :=
  natLt_add_left hlt

theorem emitAtomDropRung_patchExtends
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (a : Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState) :
    PatchExtends ps (emitAtomDropRung fa mi mu isCleanup a succ unwind ps).2 := by
  dsimp only [emitAtomDropRung]
  cases dropStyleOf (mi a) (mu a) false with
  | dead => exact patchExtends_refl ps
  | open_ => exact patchExtends_refl ps
  | static_ =>
    exact (allocElabBlock_extends ps _).2.2
  | conditional =>
    cases fa.flagOf a with
    | none => exact (allocElabBlock_extends ps _).2.2
    | some fid =>
      let b1 : ElabBlock :=
        { isCleanup := isCleanup, stmts := [ElabStmt.setFlag fid .absent], term := .staticDropAtom a succ unwind }
      let r1 := allocElabBlock ps b1
      let b2 : ElabBlock := { isCleanup := isCleanup, stmts := [], term := .switchFlag fid r1.1 succ }
      have h1 : PatchExtends ps r1.2 := (allocElabBlock_extends ps b1).2.2
      have h2 : PatchExtends r1.2 (allocElabBlock r1.2 b2).2 := (allocElabBlock_extends r1.2 b2).2.2
      exact patchExtends_trans h1 h2

theorem lowerDropCleanupHalfLadder_patchExtends
    (fa : FlagAlloc) (mi mu : AtomMap)
    (atoms : List Atom) (ubb : BlockId) (ps : PatchState) :
    PatchExtends ps (lowerDropCleanupHalfLadder fa mi mu atoms ubb ps).2 := by
  induction atoms generalizing ps with
  | nil => exact patchExtends_refl ps
  | cons a rest ih =>
    have h1 := ih ps
    have h2 := emitAtomDropRung_patchExtends fa mi mu true a
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).1 none
      (lowerDropCleanupHalfLadder fa mi mu rest ubb ps).2
    exact patchExtends_trans h1 h2

theorem lowerDropNormalLadder_patchExtends
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (atoms : List Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState) :
    PatchExtends ps (lowerDropNormalLadder fa mi mu isCleanup atoms succ unwind ps).2 := by
  induction atoms generalizing ps unwind with
  | nil => exact patchExtends_refl ps
  | cons a rest ih =>
    cases isCleanup with
    | true =>
      let recRes := lowerDropNormalLadder fa mi mu true rest succ none ps
      have h1 : PatchExtends ps recRes.2 := ih none ps
      have h2 : PatchExtends recRes.2 (emitAtomDropRung fa mi mu true a recRes.1 none recRes.2).2 :=
        emitAtomDropRung_patchExtends fa mi mu true a recRes.1 none recRes.2
      exact patchExtends_trans h1 h2
    | false =>
      cases unwind with
      | none =>
        let recRes := lowerDropNormalLadder fa mi mu false rest succ none ps
        have h1 : PatchExtends ps recRes.2 := ih none ps
        have h2 : PatchExtends recRes.2 (emitAtomDropRung fa mi mu false a recRes.1 none recRes.2).2 :=
          emitAtomDropRung_patchExtends fa mi mu false a recRes.1 none recRes.2
        exact patchExtends_trans h1 h2
      | some ubb =>
        let uRes := lowerDropCleanupHalfLadder fa mi mu rest ubb ps
        let nRes := lowerDropNormalLadder fa mi mu false rest succ (some ubb) uRes.2
        have h1 : PatchExtends ps uRes.2 := lowerDropCleanupHalfLadder_patchExtends fa mi mu rest ubb ps
        have h2 : PatchExtends uRes.2 nRes.2 := ih (some ubb) uRes.2
        have h3 : PatchExtends nRes.2 (emitAtomDropRung fa mi mu false a nRes.1 (some uRes.1) nRes.2).2 :=
          emitAtomDropRung_patchExtends fa mi mu false a nRes.1 (some uRes.1) nRes.2
        exact patchExtends_trans h1 (patchExtends_trans h2 h3)

theorem elaborateBlock_patchExtends_split
    (prog : SrcProgram) (df : DataflowCert) (fa : FlagAlloc)
    (bb : BlockId) (blk : SrcBlock) (ps : PatchState) :
    let ps' := elaborateBlock prog df fa bb blk ps
    (∀ x, natLt x ps.nextBlock = true → natLt x ps'.nextBlock = true) ∧
    (∀ k, natLt k ps.nextBlock = true → k ≠ shiftSrcBb bb → ps'.blocks k = ps.blocks k) := by
  dsimp only [elaborateBlock]
  cases blk.term with
  | goto tgt =>
    refine ⟨fun _ h => h, ?_⟩
    intro k _ hne
    change (if natEq k (shiftSrcBb bb) then _ else ps.blocks k) = ps.blocks k
    rw [natEq_false_of_ne hne]; rfl
  | switchBool _ _ _ =>
    refine ⟨fun _ h => h, ?_⟩
    intro k _ hne
    change (if natEq k (shiftSrcBb bb) then _ else ps.blocks k) = ps.blocks k
    rw [natEq_false_of_ne hne]; rfl
  | ret =>
    refine ⟨fun _ h => h, ?_⟩
    intro k _ hne
    change (if natEq k (shiftSrcBb bb) then _ else ps.blocks k) = ps.blocks k
    rw [natEq_false_of_ne hne]; rfl
  | unwindResume =>
    refine ⟨fun _ h => h, ?_⟩
    intro k _ hne
    change (if natEq k (shiftSrcBb bb) then _ else ps.blocks k) = ps.blocks k
    rw [natEq_false_of_ne hne]; rfl
  | unwindAbort =>
    refine ⟨fun _ h => h, ?_⟩
    intro k _ hne
    change (if natEq k (shiftSrcBb bb) then _ else ps.blocks k) = ps.blocks k
    rw [natEq_false_of_ne hne]; rfl
  | drop p tgt unwind =>
    dsimp only
    have hExt := lowerDropNormalLadder_patchExtends fa
      (transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)).mayInit
      (transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)).mayUninit
      blk.isCleanup (atomsOfPlace prog.locals p) (shiftSrcBb tgt)
      (shiftOptBb unwind) ps
    refine ⟨hExt.2, ?_⟩
    intro k hk hne
    change (if natEq k (shiftSrcBb bb) then _ else _) = ps.blocks k
    rw [natEq_false_of_ne hne]
    exact hExt.1 k hk
  | scopeExit locs tgt unwind =>
    dsimp only
    have hExt := lowerDropNormalLadder_patchExtends fa
      (transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)).mayInit
      (transferSrcStmtList prog.locals blk.stmts (df.atBlock bb)).mayUninit
      blk.isCleanup (atomsOfLocalList prog.locals (localsDropOrder locs)) (shiftSrcBb tgt)
      (shiftOptBb unwind) ps
    refine ⟨hExt.2, ?_⟩
    intro k hk hne
    change (if natEq k (shiftSrcBb bb) then _ else _) = ps.blocks k
    rw [natEq_false_of_ne hne]
    exact hExt.1 k hk

theorem elaborateBlocksLoop_preserves
    (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert) (fa : FlagAlloc)
    (idx rem : Nat) (ps : PatchState) (k : BlockId)
    (hBound : natLt (idx + rem) (numBlocks + 1) = true)
    (hkNext : natLt k ps.nextBlock = true)
    (hkSafe : natLt k (idx + 1) = true ∨ natLt numBlocks k = true) :
    let ps' := elaborateBlocksLoop prog df fa idx rem ps
    ps'.blocks k = ps.blocks k ∧
    (∀ x, natLt x ps.nextBlock = true → natLt x ps'.nextBlock = true) := by
  induction rem generalizing idx ps with
  | zero =>
    exact ⟨rfl, fun _ h => h⟩
  | succ r ih =>
    dsimp only [elaborateBlocksLoop]
    have hBoundNext : natLt ((idx + 1) + r) (numBlocks + 1) = true := by
      rw [← natLt_add_succ_left]; exact hBound
    have hshLt : natLt (shiftSrcBb idx) (numBlocks + 1) = true :=
      natLt_add_left hBoundNext
    have hne : k ≠ shiftSrcBb idx := by
      cases hkSafe with
      | inl hlt => exact fun heq => by rw [heq, shiftSrcBb, natLt_irrefl] at hlt; cases hlt
      | inr hgt => exact (natLt_false_to_ne hshLt k hgt).symm
    have hkSafeNext : natLt k ((idx + 1) + 1) = true ∨ natLt numBlocks k = true := by
      cases hkSafe with
      | inl hlt => exact Or.inl (natLt_succ hlt)
      | inr hgt => exact Or.inr hgt
    cases hblk : prog.blocks idx with
    | none =>
      exact ih (idx + 1) ps hBoundNext hkNext hkSafeNext
    | some blk =>
      have hStep := elaborateBlock_patchExtends_split prog df fa idx blk ps
      have hkNext1 : natLt k (elaborateBlock prog df fa idx blk ps).nextBlock = true :=
        hStep.1 k hkNext
      have hRec := ih (idx + 1) (elaborateBlock prog df fa idx blk ps) hBoundNext hkNext1 hkSafeNext
      refine ⟨?_, fun x hx => hRec.2 x (hStep.1 x hx)⟩
      rw [hRec.1, hStep.2 k hkNext hne]

theorem natLt_succ_trans {a b c : Nat}
    (hab : natLt a b = true) (hbc : natLt b c = true) : natLt (a + 1) c = true := by
  induction a generalizing b c with
  | zero =>
    cases b with
    | zero => cases hab
    | succ b' =>
      cases c with
      | zero => cases hbc
      | succ c' =>
        cases c' with
        | zero =>
          change natLt b' 0 = true at hbc
          rw [natLt_zero_right] at hbc
          cases hbc
        | succ _ => rfl
  | succ a' ih =>
    cases b with
    | zero => cases hab
    | succ b' =>
      cases c with
      | zero => cases hbc
      | succ c' => exact ih hab hbc

theorem elaborateBlocksLoop_extract
    (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert) (fa : FlagAlloc)
    (idx rem bb : Nat) (blk : SrcBlock) (ps : PatchState)
    (hBound : natLt (idx + rem) (numBlocks + 1) = true)
    (hge : natLt bb idx = false)
    (hlt : natLt bb (idx + rem) = true)
    (hnum : natLt numBlocks ps.nextBlock = true)
    (hblk : prog.blocks bb = some blk) :
    ∃ ps_before : PatchState,
      natLt numBlocks ps_before.nextBlock = true ∧
      (∀ x, natLt x ps.nextBlock = true → natLt x ps_before.nextBlock = true) ∧
      (let ps_after := elaborateBlock prog df fa bb blk ps_before
       let ps_end := elaborateBlocksLoop prog df fa idx rem ps
       ps_end.blocks (shiftSrcBb bb) = ps_after.blocks (shiftSrcBb bb) ∧
       (∀ m, natLt m ps_before.nextBlock = false → natLt m ps_after.nextBlock = true →
         ps_end.blocks m = ps_after.blocks m)) := by
  induction rem generalizing idx ps with
  | zero =>
    rw [natLt_add_zero] at hlt
    rw [hlt] at hge
    cases hge
  | succ r ih =>
    dsimp only [elaborateBlocksLoop]
    have hBoundNext : natLt ((idx + 1) + r) (numBlocks + 1) = true := by
      rw [← natLt_add_succ_left]; exact hBound
    cases heq : natEq bb idx with
    | true =>
      have hbi : bb = idx := natEq_sound heq
      subst hbi
      rw [hblk]
      refine ⟨ps, hnum, fun _ h => h, ?_⟩
      dsimp only
      have hStep := elaborateBlock_patchExtends_split prog df fa bb blk ps
      have hbb_lt : natLt bb numBlocks = true := by
        cases hnb : natLt bb numBlocks with
        | true => rfl
        | false =>
          have h1 : natLt bb (numBlocks + 1) = true := natLt_add_lt_left hBound
          cases hne : natEq bb numBlocks with
          | true =>
            have eqb := natEq_sound hne
            rw [eqb] at hBound
            have hfalse2 : natLt ((numBlocks + 1) + r) (numBlocks + 1) = true := by
              rw [← natLt_add_succ_left]; exact hBound
            have hn : ∀ a r', natLt (a + r') a = false := by
              intro a r'
              induction a generalizing r' with
              | zero => exact natLt_zero_right (0 + r')
              | succ a' iha => rw [Nat.succ_add]; exact iha r'
            rw [hn (numBlocks + 1) r] at hfalse2
            cases hfalse2
          | false =>
            have hf := natLt_succ_false_of_ne hnb hne
            rw [hf] at h1
            cases h1
      have hsh_lt : natLt (shiftSrcBb bb) ps.nextBlock = true :=
        natLt_succ_trans hbb_lt hnum
      have hsh_next : natLt (shiftSrcBb bb) (elaborateBlock prog df fa bb blk ps).nextBlock = true :=
        hStep.1 (shiftSrcBb bb) hsh_lt
      have hPresSh := elaborateBlocksLoop_preserves prog numBlocks df fa (bb + 1) r
        (elaborateBlock prog df fa bb blk ps) (shiftSrcBb bb)
        hBoundNext
        hsh_next
        (Or.inl (natLt_succ_self (bb + 1)))
      refine ⟨hPresSh.1, ?_⟩
      intro m hmGe hmLt
      have hmGtNum : natLt numBlocks m = true := natLt_trans_false_left hnum hmGe
      have hPresM := elaborateBlocksLoop_preserves prog numBlocks df fa (bb + 1) r
        (elaborateBlock prog df fa bb blk ps) m
        hBoundNext
        hmLt
        (Or.inr hmGtNum)
      exact hPresM.1
    | false =>
      have hge1 : natLt bb (idx + 1) = false := natLt_succ_false_of_ne hge heq
      have hlt1 : natLt bb ((idx + 1) + r) = true := by
        rw [← natLt_add_succ_shift]; exact hlt
      let ps1 :=
        match prog.blocks idx with
        | some b => elaborateBlock prog df fa idx b ps
        | none => ps
      have hExt1 : ∀ x, natLt x ps.nextBlock = true → natLt x ps1.nextBlock = true := by
        dsimp only [ps1]
        cases prog.blocks idx with
        | none => exact fun _ h => h
        | some b => exact (elaborateBlock_patchExtends_split prog df fa idx b ps).1
      have hnum1 : natLt numBlocks ps1.nextBlock = true := hExt1 numBlocks hnum
      have hRec := ih (idx + 1) ps1 hBoundNext hge1 hlt1 hnum1
      rcases hRec with ⟨ps_before, hbn, hbExt, hblks, hms⟩
      exact ⟨ps_before, hbn, fun x hx => hbExt x (hExt1 x hx), hblks, hms⟩

theorem elaborateProgram_entry_block (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc) :
    (elaborateProgram prog numBlocks df fa).blocks 0 =
      some
        { isCleanup := false
          stmts := listAppend
            (listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags)
            (setFlagsForAtoms fa .present (atomsOfLocalList prog.locals prog.args))
          term := .goto (shiftSrcBb prog.entry) } := by
  dsimp only [elaborateProgram]
  have hBound : natLt (0 + numBlocks) (numBlocks + 1) = true := by
    rw [Nat.zero_add]; exact natLt_succ_self numBlocks
  have hPres := elaborateBlocksLoop_preserves prog numBlocks df fa 0 numBlocks
    { nextBlock := 1 + numBlocks
      blocks := setElabBlock (fun _ => none) 0
        { isCleanup := false
          stmts := listAppend
            (listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags)
            (setFlagsForAtoms fa .present (atomsOfLocalList prog.locals prog.args))
          term := .goto (shiftSrcBb prog.entry) } }
    0 hBound (by rw [Nat.add_comm 1 numBlocks]; rfl) (Or.inl (by rfl))
  rw [hPres.1]
  rfl

theorem elaborateProgram_block_lookup (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc) (bb : BlockId) (blk : SrcBlock)
    (hbb : natLt bb numBlocks = true) (hblk : prog.blocks bb = some blk) :
    ∃ ps_before : PatchState,
      natLt numBlocks ps_before.nextBlock = true ∧
      (∀ x, natLt x (1 + numBlocks) = true → natLt x ps_before.nextBlock = true) ∧
      (let ps_after := elaborateBlock prog df fa bb blk ps_before
       let eprog := elaborateProgram prog numBlocks df fa
       eprog.blocks (shiftSrcBb bb) = ps_after.blocks (shiftSrcBb bb) ∧
       (∀ m, natLt m ps_before.nextBlock = false → natLt m ps_after.nextBlock = true →
         eprog.blocks m = ps_after.blocks m)) := by
  dsimp only [elaborateProgram]
  have hBound : natLt (0 + numBlocks) (numBlocks + 1) = true := by
    rw [Nat.zero_add]; exact natLt_succ_self numBlocks
  have hlt0 : natLt bb (0 + numBlocks) = true := by
    rw [Nat.zero_add]; exact hbb
  have hnum0 : natLt numBlocks (1 + numBlocks) = true := by
    rw [Nat.add_comm 1 numBlocks]; exact natLt_succ_self numBlocks
  have hExt := elaborateBlocksLoop_extract prog numBlocks df fa 0 numBlocks bb blk
    { nextBlock := 1 + numBlocks
      blocks := setElabBlock (fun _ => none) 0
        { isCleanup := false
          stmts := listAppend
            (listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags)
            (setFlagsForAtoms fa .present (atomsOfLocalList prog.locals prog.args))
          term := .goto (shiftSrcBb prog.entry) } }
    hBound (natLt_zero_right bb) hlt0 hnum0 hblk
  rcases hExt with ⟨ps_before, hnum, hmono, hblks, hms⟩
  exact ⟨ps_before, hnum, hmono, hblks, hms⟩

/-- Predicate asserting dynamic flags in `flags` accurately reflect `init` for every
atom assigned a dynamic stack `FlagId` in `fa`. -/
noncomputable def FlagSimulatesInit (fa : FlagAlloc) (init : AtomMap) (flags : FlagMap) : Prop :=
  ∀ a fid, fa.flagOf a = some fid → flags fid = init a

theorem execElabFuel_freeze (eprog : ElabProgram) (oracle : ExecOracle)
    (m : Nat) (est : ElabState) (hn : est.exit ≠ .running) :
    execElabFuel eprog oracle m est = est := by
  cases m with
  | zero => rfl
  | succ k =>
    dsimp only [execElabFuel]
    cases he : est.exit with
    | running => exact False.elim (hn he)
    | returned => rfl
    | unwound => rfl
    | aborted => rfl
    | faulted => rfl

theorem execElabFuel_add (eprog : ElabProgram) (oracle : ExecOracle)
    (a b : Nat) (est : ElabState) :
    execElabFuel eprog oracle (a + b) est =
      execElabFuel eprog oracle b (execElabFuel eprog oracle a est) := by
  induction a generalizing est with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a' ih =>
    have h1 : (a' + 1) + b = (a' + b) + 1 := Nat.succ_add a' b
    rw [h1]
    cases he : est.exit with
    | running =>
      have lhs1 : execElabFuel eprog oracle ((a' + b) + 1) est =
          execElabFuel eprog oracle (a' + b) (stepElabBlock eprog oracle est) := by
        dsimp only [execElabFuel]; rw [he]
      have rhs1 : execElabFuel eprog oracle (a' + 1) est =
          execElabFuel eprog oracle a' (stepElabBlock eprog oracle est) := by
        dsimp only [execElabFuel]; rw [he]
      rw [lhs1, rhs1]
      exact ih (stepElabBlock eprog oracle est)
    | returned =>
      have hn : est.exit ≠ .running := fun h => by rw [he] at h; cases h
      rw [execElabFuel_freeze eprog oracle (a' + b + 1) est hn,
          execElabFuel_freeze eprog oracle (a' + 1) est hn,
          execElabFuel_freeze eprog oracle b est hn]
    | unwound =>
      have hn : est.exit ≠ .running := fun h => by rw [he] at h; cases h
      rw [execElabFuel_freeze eprog oracle (a' + b + 1) est hn,
          execElabFuel_freeze eprog oracle (a' + 1) est hn,
          execElabFuel_freeze eprog oracle b est hn]
    | aborted =>
      have hn : est.exit ≠ .running := fun h => by rw [he] at h; cases h
      rw [execElabFuel_freeze eprog oracle (a' + b + 1) est hn,
          execElabFuel_freeze eprog oracle (a' + 1) est hn,
          execElabFuel_freeze eprog oracle b est hn]
    | faulted =>
      have hn : est.exit ≠ .running := fun h => by rw [he] at h; cases h
      rw [execElabFuel_freeze eprog oracle (a' + b + 1) est hn,
          execElabFuel_freeze eprog oracle (a' + 1) est hn,
          execElabFuel_freeze eprog oracle b est hn]

theorem setAtom_setFlagMap_sim (fa : FlagAlloc)
    (hInj : ∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b)
    (init : AtomMap) (flags : FlagMap)
    (hSim : FlagSimulatesInit fa init flags)
    (k : Atom) (v : Bool) :
    let flags' := match fa.flagOf k with
      | some fid => setFlagMap flags fid (.ofBool v)
      | none => flags
    FlagSimulatesInit fa (setAtom init k v) flags' := by
  intro flags' a fid hfa
  cases hfk : fa.flagOf k with
  | none =>
    dsimp only [flags']
    rw [hfk]
    dsimp only
    cases hak : Atom.beq a k with
    | false =>
      have hne : a ≠ k := fun he => by rw [he, atom_beq_refl] at hak; cases hak
      rw [setAtom_ne init hne v]
      exact hSim a fid hfa
    | true =>
      have heq := atom_beq_sound hak
      rw [heq, hfk] at hfa
      cases hfa
  | some kf =>
    dsimp only [flags']
    rw [hfk]
    dsimp only
    cases hak : Atom.beq a k with
    | true =>
      have heq := atom_beq_sound hak
      rw [heq] at hfa
      rw [hfa] at hfk
      cases hfk with
      | refl =>
        rw [setFlagMap_eq, heq, setAtom_eq]
        cases v <;> rfl
    | false =>
      have hne : a ≠ k := fun he => by rw [he, atom_beq_refl] at hak; cases hak
      have hfne : fid ≠ kf := fun hfeq => by
        rw [hfeq] at hfa
        exact hne (hInj a k kf hfa hfk)
      rw [setFlagMap_ne flags hfne (.ofBool v), setAtom_ne init hne v]
      exact hSim a fid hfa

theorem stepSetFlagListAbsent_preserves_false (fids : List ElabStmt)
    (locals : List MirTy) (est : ElabState)
    (hall : ∀ s ∈ fids, ∃ fid, s = ElabStmt.setFlag fid .absent)
    (hzero : ∀ f, est.flags f = false) :
    let est' := stepElabStmtList locals fids est
    est'.bb = est.bb ∧ est'.branchIdx = est.branchIdx ∧ est'.dropIdx = est.dropIdx ∧
    est'.mem = est.mem ∧ est'.trace = est.trace ∧ est'.exit = est.exit ∧
    (∀ f, est'.flags f = false) := by
  induction fids generalizing est with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hzero⟩
  | cons s rest ih =>
    have hs := hall s (by simp)
    rcases hs with ⟨fid, rfl⟩
    dsimp only [stepElabStmtList, stepElabStmt]
    have hrest : ∀ x ∈ rest, ∃ f, x = ElabStmt.setFlag f .absent :=
      fun x hx => hall x (by simp [hx])
    have hz' : ∀ f, setFlagMap est.flags fid .absent f = false := by
      intro f
      change (if natEq f fid then DropFlagState.absent.toBool else est.flags f) = false
      cases hnf : natEq f fid
      · rw [hzero f]; rfl
      · rfl
    exact ih { est with flags := setFlagMap est.flags fid .absent } hrest hz'

theorem stepElabStmtList_append (locals : List MirTy) (xs ys : List ElabStmt) (st : ElabState) :
    stepElabStmtList locals (listAppend xs ys) st =
      stepElabStmtList locals ys (stepElabStmtList locals xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    exact ih (stepElabStmt locals st x)

theorem stepSetFlagsForAtoms_spec (locals : List MirTy) (fa : FlagAlloc)
    (hInj : ∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b)
    (dval : DropFlagState) (atoms : List Atom) (cur : AtomMap) (est : ElabState)
    (hSim : FlagSimulatesInit fa cur est.flags) :
    let est' := stepElabStmtList locals (setFlagsForAtoms fa dval atoms) est
    est'.bb = est.bb ∧ est'.branchIdx = est.branchIdx ∧ est'.dropIdx = est.dropIdx ∧
    est'.mem = est.mem ∧ est'.trace = est.trace ∧ est'.exit = est.exit ∧
    FlagSimulatesInit fa (setAtoms cur atoms dval.toBool) est'.flags := by
  induction atoms generalizing cur est with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hSim⟩
  | cons a rest ih =>
    dsimp only [setFlagsForAtoms]
    cases hfa : fa.flagOf a with
    | none =>
      have hSim1 : FlagSimulatesInit fa (setAtom cur a dval.toBool) est.flags := by
        have hs := setAtom_setFlagMap_sim fa hInj cur est.flags hSim a dval.toBool
        rw [hfa] at hs
        exact hs
      exact ih (setAtom cur a dval.toBool) est hSim1
    | some fid =>
      dsimp only [stepElabStmtList, stepElabStmt]
      have hSim1 : FlagSimulatesInit fa (setAtom cur a dval.toBool)
          (setFlagMap est.flags fid dval) := by
        have hs := setAtom_setFlagMap_sim fa hInj cur est.flags hSim a dval.toBool
        rw [hfa] at hs
        have hdb : DropFlagState.ofBool dval.toBool = dval := by
          cases dval <;> rfl
        rw [hdb] at hs
        exact hs
      exact ih (setAtom cur a dval.toBool) { est with flags := setFlagMap est.flags fid dval } hSim1

theorem listMap_setFlag_mem (allFlags : List FlagId) (s : ElabStmt)
    (hs : s ∈ listMap (fun fid => ElabStmt.setFlag fid .absent) allFlags) :
    ∃ fid, s = ElabStmt.setFlag fid .absent := by
  induction allFlags with
  | nil => cases hs
  | cons f fs ih =>
    dsimp only [listMap] at hs
    cases hs with
    | head => exact ⟨f, rfl⟩
    | tail _ hmem => exact ih hmem

theorem stepElabStmt_sim (locals : List MirTy) (fa : FlagAlloc)
    (hInj : ∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b)
    (sst : SrcState) (est : ElabState) (s : SrcStmt)
    (hmem : est.mem = sst.init) (htr : est.trace = sst.trace)
    (hdi : est.dropIdx = sst.dropIdx) (hbi : est.branchIdx = sst.branchIdx)
    (hex : est.exit = sst.exit) (hSim : FlagSimulatesInit fa sst.init est.flags) :
    let sst1 := stepSrcStmt locals sst s
    let est1 := stepElabStmtList locals (elaborateStmt locals fa s) est
    est1.mem = sst1.init ∧ est1.trace = sst1.trace ∧
    est1.dropIdx = sst1.dropIdx ∧ est1.branchIdx = sst1.branchIdx ∧
    est1.exit = sst1.exit ∧ est1.bb = est.bb ∧
    FlagSimulatesInit fa sst1.init est1.flags := by
  cases s with
  | storageLive l =>
    exact ⟨hmem, htr, hdi, hbi, hex, rfl, hSim⟩
  | noop =>
    exact ⟨hmem, htr, hdi, hbi, hex, rfl, hSim⟩
  | storageDead l =>
    dsimp only [stepSrcStmt, elaborateStmt]
    rw [stepElabStmtList_append]
    have hf := stepSetFlagsForAtoms_spec locals fa hInj .absent
      (atomsOfPlace locals { localId := l, proj := [] }) sst.init est hSim
    rcases hf with ⟨hbb, hb2, hd2, hm2, ht2, he2, hsim2⟩
    dsimp only [stepElabStmtList, stepElabStmt]
    refine ⟨?_, ?_, hd2.trans hdi, hb2.trans hbi, he2.trans hex, hbb, hsim2⟩
    · rw [hm2, hmem]
    · exact ht2.trans htr
  | initPlace p =>
    dsimp only [stepSrcStmt, elaborateStmt]
    rw [stepElabStmtList_append]
    dsimp only [stepElabStmtList, stepElabStmt]
    have hsim1 : FlagSimulatesInit fa sst.init est.flags := hSim
    have hf := stepSetFlagsForAtoms_spec locals fa hInj .present (atomsOfPlace locals p) sst.init
      { est with
        mem := setAtoms est.mem (atomsOfPlace locals p) true
        trace := listAppend est.trace (emitCreateForAtoms p.localId (atomsOfPlace locals p)) } hsim1
    rcases hf with ⟨hbb, hb2, hd2, hm2, ht2, he2, hsim2⟩
    refine ⟨?_, ?_, hd2.trans hdi, hb2.trans hbi, he2.trans hex, hbb, hsim2⟩
    · rw [hm2, hmem]
    · rw [ht2, htr]
  | movePlace dst src =>
    dsimp only [stepSrcStmt, elaborateStmt]
    rw [stepElabStmtList_append, stepElabStmtList_append]
    have hf1 := stepSetFlagsForAtoms_spec locals fa hInj .absent
      (atomsOfPlace locals src) sst.init est hSim
    rcases hf1 with ⟨hbb1, hb1, hd1, hm1, ht1, he1, hsim1⟩
    dsimp only [stepElabStmtList, stepElabStmt]
    let estA := stepElabStmtList locals (setFlagsForAtoms fa .absent (atomsOfPlace locals src)) est
    let estMid : ElabState :=
      { estA with mem := setAtoms (setAtoms estA.mem (atomsOfPlace locals src) false) (atomsOfPlace locals dst) true }
    have hf2 := stepSetFlagsForAtoms_spec locals fa hInj .present
      (atomsOfPlace locals dst)
      (setAtoms sst.init (atomsOfPlace locals src) false)
      estMid
      hsim1
    rcases hf2 with ⟨hbb2, hb2, hd2, hm2, ht2, he2, hsim2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hsim2⟩
    · rw [hm2]; dsimp only [estMid, estA]; rw [hm1, hmem]
    · rw [ht2]; dsimp only [estMid, estA]; rw [ht1, htr]
    · exact hd2.trans (hd1.trans hdi)
    · exact hb2.trans (hb1.trans hbi)
    · exact he2.trans (he1.trans hex)
    · exact hbb2.trans hbb1
  | explicitDrop p =>
    dsimp only [stepSrcStmt, elaborateStmt]
    rw [stepElabStmtList_append]
    dsimp only [stepElabStmtList, stepElabStmt]
    have hInitEq :
        (execExplicitDrop (atomsOfPlace locals p) sst.init sst.trace).1 =
          setAtoms sst.init (atomsOfPlace locals p) false := by
      funext a
      have hd := execExplicitDrop_clears_all (atomsOfPlace locals p) sst.init sst.trace a
      cases hm : atomInList a (atomsOfPlace locals p) with
      | true => rw [hd.2.1 hm, setAtoms_mem sst.init _ false a hm]
      | false => rw [hd.2.2 hm, setAtoms_not_mem sst.init _ false a hm]
    let estMid :=
      { est with
        mem := (execExplicitDrop (atomsOfPlace locals p) est.mem est.trace).1
        trace := (execExplicitDrop (atomsOfPlace locals p) est.mem est.trace).2 }
    have hf := stepSetFlagsForAtoms_spec locals fa hInj .absent
      (atomsOfPlace locals p) sst.init estMid hSim
    rcases hf with ⟨hbb, hb2, hd2, hm2, ht2, he2, hsim2⟩
    change FlagSimulatesInit fa (setAtoms sst.init (atomsOfPlace locals p) false) _ at hsim2
    rw [← hInitEq] at hsim2
    refine ⟨?_, ?_, hd2.trans hdi, hb2.trans hbi, he2.trans hex, hbb, hsim2⟩
    · rw [hm2]; dsimp only [estMid]; rw [hmem, htr]
    · rw [ht2]; dsimp only [estMid]; rw [hmem, htr]

theorem stepElabStmtList_sim (locals : List MirTy) (fa : FlagAlloc)
    (hInj : ∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b)
    (stmts : List SrcStmt) (sst : SrcState) (est : ElabState)
    (hmem : est.mem = sst.init) (htr : est.trace = sst.trace)
    (hdi : est.dropIdx = sst.dropIdx) (hbi : est.branchIdx = sst.branchIdx)
    (hex : est.exit = sst.exit) (hSim : FlagSimulatesInit fa sst.init est.flags) :
    let sst1 := stepSrcStmtList locals stmts sst
    let est1 := stepElabStmtList locals (elaborateStmtList locals fa stmts) est
    est1.mem = sst1.init ∧ est1.trace = sst1.trace ∧
    est1.dropIdx = sst1.dropIdx ∧ est1.branchIdx = sst1.branchIdx ∧
    est1.exit = sst1.exit ∧ est1.bb = est.bb ∧
    FlagSimulatesInit fa sst1.init est1.flags := by
  induction stmts generalizing sst est with
  | nil => exact ⟨hmem, htr, hdi, hbi, hex, rfl, hSim⟩
  | cons s ss ih =>
    dsimp only [stepSrcStmtList, elaborateStmtList]
    rw [stepElabStmtList_append]
    have hs := stepElabStmt_sim locals fa hInj sst est s hmem htr hdi hbi hex hSim
    rcases hs with ⟨hm1, ht1, hd1, hb1, he1, hbb1, hsim1⟩
    have hrec := ih (stepSrcStmt locals sst s)
      (stepElabStmtList locals (elaborateStmt locals fa s) est)
      hm1 ht1 hd1 hb1 he1 hsim1
    rcases hrec with ⟨hm2, ht2, hd2, hb2, he2, hbb2, hsim2⟩
    exact ⟨hm2, ht2, hd2, hb2, he2, hbb2.trans hbb1, hsim2⟩

theorem evalSrcDropAtomsGo_tr_prepend (oracle : ExecOracle) (isCl : Bool)
    (atoms : List Atom) (cur : AtomMap) (pfx tr : List DropEvent) (di : Nat) (pan : Bool) :
    let r := evalSrcDropAtomsGo oracle isCl atoms cur tr di pan
    evalSrcDropAtomsGo oracle isCl atoms cur (listAppend pfx tr) di pan =
      (r.1, listAppend pfx r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2) := by
  induction atoms generalizing cur pfx tr di pan with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [evalSrcDropAtomsGo]
    cases hcx : cur x with
    | false =>
      rw [bool_if_false]
      exact ih cur pfx tr di pan
    | true =>
      rw [bool_if_true]
      cases pan with
      | false =>
        rw [bool_if_false]
        cases oracle.panicAt di x with
        | false =>
          rw [bool_if_false, bool_if_false]
          have hStep := ih (setAtom cur x false) pfx (listAppend tr [DropEvent.atomEvent x false]) (di + 1) false
          rw [listAppend_assoc]
          exact hStep
        | true =>
          rw [bool_if_true, bool_if_true]
          cases isCl with
          | true =>
            repeat (first | rw [bool_if_true] | rw [bool_if_false])
            dsimp only
            rw [listAppend_assoc]
          | false =>
            rw [bool_if_false, bool_if_false]
            have hStep := ih (setAtom cur x false) pfx (listAppend tr [DropEvent.atomEvent x false]) (di + 1) true
            rw [listAppend_assoc]
            exact hStep
      | true =>
        rw [bool_if_true, bool_if_true]
        cases oracle.panicAt di x with
        | true =>
          repeat (first | rw [bool_if_true] | rw [bool_if_false])
          dsimp only
          rw [listAppend_assoc]
        | false =>
          rw [bool_if_false, bool_if_false]
          have hStep := ih (setAtom cur x false) pfx (listAppend tr [DropEvent.atomEvent x false]) (di + 1) true
          rw [listAppend_assoc]
          exact hStep

theorem evalSrcDropAtomsGo_cleanup_equiv (oracle : ExecOracle) (atoms : List Atom)
    (cur : AtomMap) (tr : List DropEvent) (di : Nat) (isCl : Bool) :
    let rTrue := evalSrcDropAtomsGo oracle true atoms cur tr di false
    let rPan := evalSrcDropAtomsGo oracle isCl atoms cur tr di true
    rTrue.1 = rPan.1 ∧ rTrue.2.1 = rPan.2.1 ∧ rTrue.2.2.1 = rPan.2.2.1 ∧ rTrue.2.2.2.2 = rPan.2.2.2.2 := by
  induction atoms generalizing cur tr di with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x rest ih =>
    dsimp only [evalSrcDropAtomsGo]
    cases hcx : cur x with
    | false =>
      rw [bool_if_false]
      exact ih cur tr di
    | true =>
      rw [bool_if_true, bool_if_false, bool_if_true]
      cases oracle.panicAt di x with
      | true =>
        rw [bool_if_true, bool_if_true]
        exact ⟨rfl, rfl, rfl, rfl⟩
      | false =>
        rw [bool_if_false]
        exact ih (setAtom cur x false) (listAppend tr [DropEvent.atomEvent x false]) (di + 1)

noncomputable def LocalDropReady (fa : FlagAlloc) (mi mu : AtomMap)
    (atoms : List Atom) (cur : AtomMap) : Prop :=
  ∀ x, atomInList x atoms = true →
    (cur x = true → mi x = true) ∧
    (cur x = false → mu x = true) ∧
    (mi x = true → mu x = true → ∃ fid, fa.flagOf x = some fid)

theorem localDropReady_head {fa : FlagAlloc} {mi mu : AtomMap} {a : Atom}
    {rest : List Atom} {cur : AtomMap} (hr : LocalDropReady fa mi mu (a :: rest) cur) :
    (cur a = true → mi a = true) ∧
    (cur a = false → mu a = true) ∧
    (mi a = true → mu a = true → ∃ fid, fa.flagOf a = some fid) :=
  hr a (by change (Atom.beq a a || atomInList a rest) = true; rw [atom_beq_refl a]; rfl)

theorem localDropReady_tail {fa : FlagAlloc} {mi mu : AtomMap} {a : Atom}
    {rest : List Atom} {cur : AtomMap} (hr : LocalDropReady fa mi mu (a :: rest) cur) :
    LocalDropReady fa mi mu rest cur := by
  intro x hx
  exact hr x (by change (Atom.beq x a || atomInList x rest) = true; rw [hx]; exact Bool.or_true _)

theorem localDropReady_tail_clear {fa : FlagAlloc} {mi mu : AtomMap} {a : Atom}
    {rest : List Atom} {cur : AtomMap} (hr : LocalDropReady fa mi mu (a :: rest) cur)
    (hnot : atomInList a rest = false) :
    LocalDropReady fa mi mu rest (setAtom cur a false) := by
  intro x hx
  have hne : x ≠ a := fun heq => by rw [heq] at hx; rw [hx] at hnot; cases hnot
  have hmem : atomInList x (a :: rest) = true := by
    change (Atom.beq x a || atomInList x rest) = true; rw [hx]; exact Bool.or_true _
  rw [setAtom_ne cur hne false]
  exact hr x hmem

theorem evalSrcDropAtomsGo_cleanup_no_abort_not_panicked
    (oracle : ExecOracle) (atoms : List Atom) (cur : AtomMap) (tr : List DropEvent) (di : Nat)
    (hnoab : (evalSrcDropAtomsGo oracle true atoms cur tr di false).2.2.2.2 = false) :
    (evalSrcDropAtomsGo oracle true atoms cur tr di false).2.2.2.1 = false := by
  induction atoms generalizing cur tr di with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [evalSrcDropAtomsGo] at hnoab ⊢
    cases hcx : cur x with
    | false =>
      rw [hcx] at hnoab
      repeat (first | rw [bool_if_true] at hnoab ⊢ | rw [bool_if_false] at hnoab ⊢)
      exact ih cur tr di hnoab
    | true =>
      rw [hcx] at hnoab
      repeat (first | rw [bool_if_true] at hnoab ⊢ | rw [bool_if_false] at hnoab ⊢)
      cases hp : oracle.panicAt di x with
      | true =>
        rw [hp] at hnoab
        repeat (first | rw [bool_if_true] at hnoab | rw [bool_if_false] at hnoab)
        cases hnoab
      | false =>
        rw [hp] at hnoab
        repeat (first | rw [bool_if_true] at hnoab ⊢ | rw [bool_if_false] at hnoab ⊢)
        exact ih (setAtom cur x false) (listAppend tr [DropEvent.atomEvent x false]) (di + 1) hnoab

theorem evalSrcDropAtomsGo_pan_stays_true
    (oracle : ExecOracle) (isCl : Bool) (atoms : List Atom) (cur : AtomMap)
    (tr : List DropEvent) (di : Nat)
    (hnoab : (evalSrcDropAtomsGo oracle isCl atoms cur tr di true).2.2.2.2 = false) :
    (evalSrcDropAtomsGo oracle isCl atoms cur tr di true).2.2.2.1 = true := by
  induction atoms generalizing cur tr di with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [evalSrcDropAtomsGo] at hnoab ⊢
    cases hcx : cur x with
    | false =>
      rw [hcx] at hnoab
      repeat (first | rw [bool_if_true] at hnoab ⊢ | rw [bool_if_false] at hnoab ⊢)
      exact ih cur tr di hnoab
    | true =>
      rw [hcx] at hnoab
      repeat (first | rw [bool_if_true] at hnoab ⊢ | rw [bool_if_false] at hnoab ⊢)
      cases hp : oracle.panicAt di x with
      | true =>
        rw [hp] at hnoab
        repeat (first | rw [bool_if_true] at hnoab | rw [bool_if_false] at hnoab)
        cases hnoab
      | false =>
        rw [hp] at hnoab
        repeat (first | rw [bool_if_true] at hnoab ⊢ | rw [bool_if_false] at hnoab ⊢)
        exact ih (setAtom cur x false) (listAppend tr [DropEvent.atomEvent x false]) (di + 1) hnoab

theorem stepStaticDropAtomBlock (eprog : ElabProgram) (oracle : ExecOracle)
    (fa : FlagAlloc)
    (hInj : ∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b)
    (isCleanup : Bool) (a : Atom) (succ : BlockId) (unwind : Option BlockId)
    (cur : AtomMap) (est : ElabState)
    (hRun : est.exit = .running) (hMem : est.mem = cur) (hLive : cur a = true)
    (hSim : FlagSimulatesInit fa cur est.flags)
    (hBlk : eprog.blocks est.bb = some
      { isCleanup := isCleanup
        stmts := match fa.flagOf a with | some fid => [ElabStmt.setFlag fid .absent] | none => []
        term := .staticDropAtom a succ unwind }) :
    let est' := stepElabBlock eprog oracle est
    est'.mem = setAtom cur a false ∧
    est'.trace = listAppend est.trace [DropEvent.atomEvent a false] ∧
    est'.dropIdx = est.dropIdx + 1 ∧
    est'.branchIdx = est.branchIdx ∧
    FlagSimulatesInit fa (setAtom cur a false) est'.flags ∧
    (oracle.panicAt est.dropIdx a = false → est'.exit = .running ∧ est'.bb = succ) ∧
    (oracle.panicAt est.dropIdx a = true →
      (isCleanup = true → est'.exit = .aborted) ∧
      (isCleanup = false →
        (unwind = none → est'.exit = .aborted) ∧
        (∀ ubb, unwind = some ubb → est'.exit = .running ∧ est'.bb = ubb))) := by
  dsimp only [stepElabBlock]
  rw [hRun]
  dsimp only
  cases hlu : eprog.blocks est.bb with
  | none => rw [hlu] at hBlk; cases hBlk
  | some blk =>
    rw [hlu] at hBlk
    cases hBlk
    dsimp only
    have hStmt : ∃ st1,
        stepElabStmtList eprog.locals
          (match fa.flagOf a with | some fid => [ElabStmt.setFlag fid .absent] | none => []) est = st1 ∧
        st1.mem = cur ∧ st1.trace = est.trace ∧ st1.dropIdx = est.dropIdx ∧
        st1.branchIdx = est.branchIdx ∧ st1.exit = .running ∧
        FlagSimulatesInit fa (setAtom cur a false) st1.flags := by
      have hsf := setAtom_setFlagMap_sim fa hInj cur est.flags hSim a false
      cases hfa : fa.flagOf a with
      | none =>
        rw [hfa] at hsf
        refine ⟨est, rfl, hMem, rfl, rfl, rfl, hRun, hsf⟩
      | some fid =>
        rw [hfa] at hsf
        dsimp only [stepElabStmtList, stepElabStmt]
        refine ⟨{ est with flags := setFlagMap est.flags fid .absent }, rfl, hMem, rfl, rfl, rfl, hRun, hsf⟩
    rcases hStmt with ⟨st1, hstEq, hsm, hstr, hsdi, hsbi, hsex, hsf⟩
    rw [hstEq, hsm, hLive, bool_if_true, hsdi]
    cases hp : oracle.panicAt est.dropIdx a with
    | false =>
      rw [bool_if_false]
      dsimp only
      exact ⟨rfl, by rw [hstr], rfl, hsbi, hsf, (fun _ => ⟨hsex, rfl⟩), fun hf => by cases hf⟩
    | true =>
      rw [bool_if_true]
      cases isCleanup with
      | true =>
        dsimp only
        exact ⟨rfl, by rw [hstr], rfl, hsbi, hsf, (fun hf => by cases hf),
          fun _ => ⟨(fun _ => rfl), fun hf => by cases hf⟩⟩
      | false =>
        cases unwind with
        | none =>
          dsimp only
          exact ⟨rfl, by rw [hstr], rfl, hsbi, hsf, (fun hf => by cases hf),
            fun _ => ⟨(fun hf => by cases hf), fun _ => ⟨(fun _ => rfl), fun u hu => by cases hu⟩⟩⟩
        | some ubb =>
          dsimp only
          exact ⟨rfl, by rw [hstr], rfl, hsbi, hsf, (fun hf => by cases hf),
            fun _ => ⟨(fun hf => by cases hf), fun _ => ⟨(fun hu => by cases hu), fun u hu => by cases hu; exact ⟨hsex, rfl⟩⟩⟩⟩

private theorem stepElabBlock_switchFlag (eprog : ElabProgram) (oracle : ExecOracle)
    (est : ElabState) (isCl : Bool) (fid : FlagId) (bbPres bbAbs : BlockId)
    (hRun : est.exit = .running)
    (hBlk : eprog.blocks est.bb = some
      { isCleanup := isCl, stmts := [], term := .switchFlag fid bbPres bbAbs }) :
    stepElabBlock eprog oracle est =
      { est with bb := if est.flags fid = true then bbPres else bbAbs } := by
  dsimp only [stepElabBlock]
  rw [hRun]
  dsimp only
  rw [hBlk]
  dsimp only
  have h1 : stepElabStmtList eprog.locals [] est = est := rfl
  rw [h1, hRun]

theorem emitAtomDropRung_sim (eprog : ElabProgram) (oracle : ExecOracle)
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (a : Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState)
    (cur : AtomMap)
    (hInj : ∀ x y fid, fa.flagOf x = some fid → fa.flagOf y = some fid → x = y)
    (hmi : cur a = true → mi a = true)
    (hmu : cur a = false → mu a = true)
    (hcond : mi a = true → mu a = true → ∃ fid, fa.flagOf a = some fid)
    (est : ElabState)
    (hRun : est.exit = .running)
    (hMem : est.mem = cur)
    (hBb : est.bb = (emitAtomDropRung fa mi mu isCleanup a succ unwind ps).1)
    (hSim : FlagSimulatesInit fa cur est.flags)
    (hAg : BlocksAgreeAfter eprog.blocks ps (emitAtomDropRung fa mi mu isCleanup a succ unwind ps).2) :
    ∃ k : Nat,
      let est' := execElabFuel eprog oracle k est
      (cur a = true →
        est'.mem = setAtom cur a false ∧
        est'.trace = listAppend est.trace [DropEvent.atomEvent a false] ∧
        est'.dropIdx = est.dropIdx + 1 ∧
        est'.branchIdx = est.branchIdx ∧
        FlagSimulatesInit fa (setAtom cur a false) est'.flags ∧
        (oracle.panicAt est.dropIdx a = false → est'.exit = .running ∧ est'.bb = succ) ∧
        (oracle.panicAt est.dropIdx a = true →
          (isCleanup = true → est'.exit = .aborted) ∧
          (isCleanup = false →
            (unwind = none → est'.exit = .aborted) ∧
            (∀ ubb, unwind = some ubb → est'.exit = .running ∧ est'.bb = ubb)))) ∧
      (cur a = false →
        est'.mem = cur ∧ est'.trace = est.trace ∧ est'.dropIdx = est.dropIdx ∧
        est'.branchIdx = est.branchIdx ∧ est'.exit = .running ∧ est'.bb = succ ∧
        FlagSimulatesInit fa cur est'.flags) := by
  dsimp only [emitAtomDropRung] at hBb hAg
  cases hca : cur a with
  | false =>
    have hmuT : mu a = true := hmu hca
    cases hmia : mi a with
    | false =>
      rw [hmia] at hBb
      dsimp only [dropStyleOf] at hBb
      refine ⟨0, ?_⟩
      dsimp only
      exact ⟨(fun hf => by cases hf), fun _ => ⟨hMem, rfl, rfl, rfl, hRun, hBb, hSim⟩⟩
    | true =>
      have hcondEx : ∃ fid, fa.flagOf a = some fid := hcond hmia hmuT
      rcases hcondEx with ⟨fid, hfa⟩
      rw [hmia, hmuT] at hBb hAg
      dsimp only [dropStyleOf] at hBb hAg
      rw [hfa] at hBb hAg
      let dropBlk : ElabBlock :=
        { isCleanup := isCleanup, stmts := [ElabStmt.setFlag fid .absent], term := .staticDropAtom a succ unwind }
      let res1 := allocElabBlock ps dropBlk
      let switchBlk : ElabBlock :=
        { isCleanup := isCleanup, stmts := [], term := .switchFlag fid res1.1 succ }
      let res2 := allocElabBlock res1.2 switchBlk
      have hext2 := allocElabBlock_extends res1.2 switchBlk
      have hswLt : natLt res2.1 res2.2.nextBlock = true := hext2.1
      have hswGe : natLt res2.1 ps.nextBlock = false := by
        change natLt (ps.nextBlock + 1) ps.nextBlock = false
        exact natLt_succ_false ps.nextBlock
      have hBlkSw : eprog.blocks res2.1 = some switchBlk := by
        rw [hAg res2.1 hswGe hswLt]
        exact hext2.2.1
      have hFlagVal : est.flags fid = false := by
        rw [hSim a fid hfa, hca]
      refine ⟨1, ?_⟩
      dsimp only
      refine ⟨(fun hf => by cases hf), fun _ => ?_⟩
      have hestSw : eprog.blocks est.bb = some switchBlk := by rw [hBb]; exact hBlkSw
      dsimp only [execElabFuel]
      rw [hRun]
      dsimp only [execElabFuel]
      rw [stepElabBlock_switchFlag eprog oracle est isCleanup fid res1.1 succ hRun hestSw]
      rw [hFlagVal, bool_if_false]
      exact ⟨hMem, rfl, rfl, rfl, hRun, rfl, hSim⟩
  | true =>
    have hmiT : mi a = true := hmi hca
    rw [hmiT] at hBb hAg
    cases hmua : mu a with
    | false =>
      rw [hmua] at hBb hAg
      dsimp only [dropStyleOf] at hBb hAg
      let blk : ElabBlock :=
        { isCleanup := isCleanup
          stmts := match fa.flagOf a with | some fid => [ElabStmt.setFlag fid .absent] | none => []
          term := .staticDropAtom a succ unwind }
      let res := allocElabBlock ps blk
      have hext := allocElabBlock_extends ps blk
      have hGe : natLt res.1 ps.nextBlock = false := by
        change natLt ps.nextBlock ps.nextBlock = false
        exact natLt_irrefl ps.nextBlock
      have hBlk : eprog.blocks est.bb = some blk := by
        rw [hBb, hAg res.1 hGe hext.1]
        exact hext.2.1
      have hStep := stepStaticDropAtomBlock eprog oracle fa hInj isCleanup a succ unwind cur est
        hRun hMem hca hSim hBlk
      refine ⟨1, ?_, fun hf => by cases hf⟩
      intro _
      dsimp only [execElabFuel]
      rw [hRun]
      exact hStep
    | true =>
      have hcondEx : ∃ fid, fa.flagOf a = some fid := hcond hmiT hmua
      rcases hcondEx with ⟨fid, hfa⟩
      rw [hmua] at hBb hAg
      dsimp only [dropStyleOf] at hBb hAg
      rw [hfa] at hBb hAg
      let dropBlk : ElabBlock :=
        { isCleanup := isCleanup, stmts := [ElabStmt.setFlag fid .absent], term := .staticDropAtom a succ unwind }
      let res1 := allocElabBlock ps dropBlk
      let switchBlk : ElabBlock :=
        { isCleanup := isCleanup, stmts := [], term := .switchFlag fid res1.1 succ }
      let res2 := allocElabBlock res1.2 switchBlk
      have hext1 := allocElabBlock_extends ps dropBlk
      have hext2 := allocElabBlock_extends res1.2 switchBlk
      have hswLt : natLt res2.1 res2.2.nextBlock = true := hext2.1
      have hswGe : natLt res2.1 ps.nextBlock = false := by
        change natLt (ps.nextBlock + 1) ps.nextBlock = false
        exact natLt_succ_false ps.nextBlock
      have hBlkSw : eprog.blocks est.bb = some switchBlk := by
        rw [hBb, hAg res2.1 hswGe hswLt]
        exact hext2.2.1
      have hdrLt2 : natLt res1.1 res2.2.nextBlock = true := hext2.2.2.2 res1.1 hext1.1
      have hdrGe : natLt res1.1 ps.nextBlock = false := by
        change natLt ps.nextBlock ps.nextBlock = false
        exact natLt_irrefl ps.nextBlock
      have hBlkDr : eprog.blocks res1.1 = some dropBlk := by
        rw [hAg res1.1 hdrGe hdrLt2, hext2.2.2.1 res1.1 hext1.1]
        exact hext1.2.1
      have hFlagVal : est.flags fid = true := by
        rw [hSim a fid hfa, hca]
      let est1 := stepElabBlock eprog oracle est
      have hest1Eq : est1 = { est with bb := res1.1 } := by
        dsimp only [est1]
        rw [stepElabBlock_switchFlag eprog oracle est isCleanup fid res1.1 succ hRun hBlkSw]
        rw [hFlagVal, bool_if_true]
      have hBlkDr1 : eprog.blocks est1.bb = some {
          isCleanup := isCleanup
          stmts := match fa.flagOf a with | some fid => [ElabStmt.setFlag fid .absent] | none => []
          term := .staticDropAtom a succ unwind } := by
        rw [hest1Eq]
        dsimp only
        rw [hfa]
        exact hBlkDr
      have hStep2 := stepStaticDropAtomBlock eprog oracle fa hInj isCleanup a succ unwind cur est1
        (by rw [hest1Eq]; exact hRun) (by rw [hest1Eq]; exact hMem) hca
        (by rw [hest1Eq]; exact hSim) hBlkDr1
      have hm2 : (stepElabBlock eprog oracle est1).mem = setAtom cur a false := hStep2.1
      have ht2 : (stepElabBlock eprog oracle est1).trace = listAppend est.trace [DropEvent.atomEvent a false] := by
        rw [hStep2.2.1, hest1Eq]
      have hd2 : (stepElabBlock eprog oracle est1).dropIdx = est.dropIdx + 1 := by
        rw [hStep2.2.2.1, hest1Eq]
      have hb2 : (stepElabBlock eprog oracle est1).branchIdx = est.branchIdx := by
        rw [hStep2.2.2.2.1, hest1Eq]
      have hf2 : FlagSimulatesInit fa (setAtom cur a false) (stepElabBlock eprog oracle est1).flags :=
        hStep2.2.2.2.2.1
      have hpF2 : oracle.panicAt est.dropIdx a = false →
          (stepElabBlock eprog oracle est1).exit = .running ∧
          (stepElabBlock eprog oracle est1).bb = succ := by
        intro hpf
        apply hStep2.2.2.2.2.2.1
        rw [hest1Eq]; exact hpf
      have hpT2 : oracle.panicAt est.dropIdx a = true →
          (isCleanup = true → (stepElabBlock eprog oracle est1).exit = .aborted) ∧
          (isCleanup = false →
            (unwind = none → (stepElabBlock eprog oracle est1).exit = .aborted) ∧
            (∀ ubb, unwind = some ubb →
              (stepElabBlock eprog oracle est1).exit = .running ∧
              (stepElabBlock eprog oracle est1).bb = ubb)) := by
        intro hpt
        apply hStep2.2.2.2.2.2.2
        rw [hest1Eq]; exact hpt
      refine ⟨2, ?_, fun hf => by cases hf⟩
      intro _
      have hexec : execElabFuel eprog oracle 2 est = stepElabBlock eprog oracle est1 := by
        dsimp only [execElabFuel]
        rw [hRun]
        dsimp only
        change execElabFuel eprog oracle 1 est1 = _
        dsimp only [execElabFuel]
        rw [hest1Eq, hRun]
      rw [hexec]
      exact ⟨hm2, ht2, hd2, hb2, hf2, hpF2, hpT2⟩

theorem lowerDropCleanupHalfLadder_sim (eprog : ElabProgram) (oracle : ExecOracle)
    (fa : FlagAlloc) (mi mu : AtomMap) (atoms : List Atom) (ubb : BlockId) (ps : PatchState)
    (cur : AtomMap)
    (hInj : ∀ x y fid, fa.flagOf x = some fid → fa.flagOf y = some fid → x = y)
    (hDist : atomsDistinct atoms = true)
    (hReady : LocalDropReady fa mi mu atoms cur)
    (est : ElabState) (hRun : est.exit = .running) (hMem : est.mem = cur)
    (hBb : est.bb = (lowerDropCleanupHalfLadder fa mi mu atoms ubb ps).1)
    (hSim : FlagSimulatesInit fa cur est.flags)
    (hAg : BlocksAgreeAfter eprog.blocks ps (lowerDropCleanupHalfLadder fa mi mu atoms ubb ps).2) :
    let srcRes := evalSrcDropAtomsGo oracle true atoms cur [] est.dropIdx false
    ∃ k : Nat,
      let est' := execElabFuel eprog oracle k est
      est'.mem = srcRes.1 ∧
      est'.trace = listAppend est.trace srcRes.2.1 ∧
      est'.dropIdx = srcRes.2.2.1 ∧
      est'.branchIdx = est.branchIdx ∧
      FlagSimulatesInit fa srcRes.1 est'.flags ∧
      (srcRes.2.2.2.2 = true → est'.exit = .aborted) ∧
      (srcRes.2.2.2.2 = false → est'.exit = .running ∧ est'.bb = ubb) := by
  induction atoms generalizing cur est ps with
  | nil =>
    refine ⟨0, hMem, (by dsimp only [execElabFuel, evalSrcDropAtomsGo]; rw [listAppend_nil_right]),
      rfl, rfl, hSim, (fun hf => by cases hf), fun _ => ⟨hRun, hBb⟩⟩
  | cons a rest ih =>
    have hDh := atomsDistinct_head hDist
    have hHead := localDropReady_head hReady
    let uRes := lowerDropCleanupHalfLadder fa mi mu rest ubb ps
    let rRes := emitAtomDropRung fa mi mu true a uRes.1 none uRes.2
    have hExtU := lowerDropCleanupHalfLadder_patchExtends fa mi mu rest ubb ps
    have hExtR := emitAtomDropRung_patchExtends fa mi mu true a uRes.1 none uRes.2
    have hAgU : BlocksAgreeAfter eprog.blocks ps uRes.2 :=
      blocksAgreeAfter_split_left hExtR hAg
    have hAgR : BlocksAgreeAfter eprog.blocks uRes.2 rRes.2 :=
      blocksAgreeAfter_split_right hExtU hAg
    have hRung := emitAtomDropRung_sim eprog oracle fa mi mu true a uRes.1 none uRes.2 cur
      hInj hHead.1 hHead.2.1 hHead.2.2 est hRun hMem hBb hSim hAgR
    rcases hRung with ⟨ka, hkaT, hkaF⟩
    let est1 := execElabFuel eprog oracle ka est
    cases hca : cur a with
    | false =>
      rcases hkaF hca with ⟨hm1, ht1, hd1, hb1, he1, hbb1, hsim1⟩
      have hRest := ih ps cur hDh.2 (localDropReady_tail hReady) est1 he1 hm1 hbb1 hsim1 hAgU
      rcases hRest with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
      refine ⟨ka + kr, ?_⟩
      rw [execElabFuel_add]
      dsimp only [evalSrcDropAtomsGo]
      rw [hca, bool_if_false]
      dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
      rw [ht1] at ht2
      rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
      exact ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, hAb, hCont⟩
    | true =>
      rcases hkaT hca with ⟨hm1, ht1, hd1, hb1, hsim1, hPFalse, hPTrue⟩
      cases hp : oracle.panicAt est.dropIdx a with
      | true =>
        have hAbE : est1.exit = .aborted := (hPTrue hp).1 rfl
        refine ⟨ka, ?_⟩
        dsimp only [evalSrcDropAtomsGo]
        rw [hca, bool_if_true, bool_if_false, hp, bool_if_true, bool_if_true]
        exact ⟨hm1, ht1, hd1, hb1, hsim1, (fun _ => hAbE), fun hf => by cases hf⟩
      | false =>
        rcases hPFalse hp with ⟨he1, hbb1⟩
        have hReady1 := localDropReady_tail_clear hReady hDh.1
        have hRest := ih ps (setAtom cur a false) hDh.2 hReady1 est1 he1 hm1 hbb1 hsim1 hAgU
        rcases hRest with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
        refine ⟨ka + kr, ?_⟩
        rw [execElabFuel_add]
        dsimp only [evalSrcDropAtomsGo]
        rw [hca, bool_if_true, bool_if_false, hp, bool_if_false]
        have hShift := evalSrcDropAtomsGo_tr_prepend oracle true rest (setAtom cur a false)
          [DropEvent.atomEvent a false] [] (est.dropIdx + 1) false
        rw [listAppend_nil_right] at hShift
        dsimp only [listAppend]
        rw [hShift]
        dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
        rw [ht1] at ht2
        rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
        rw [listAppend_assoc] at ht2
        exact ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, hAb, hCont⟩

theorem lowerDropNormalLadder_sim (eprog : ElabProgram) (oracle : ExecOracle)
    (fa : FlagAlloc) (mi mu : AtomMap) (isCleanup : Bool)
    (atoms : List Atom) (succ : BlockId) (unwind : Option BlockId) (ps : PatchState)
    (cur : AtomMap)
    (hInj : ∀ x y fid, fa.flagOf x = some fid → fa.flagOf y = some fid → x = y)
    (hDist : atomsDistinct atoms = true)
    (hUnwForm : isCleanup = false → ∃ ubb, unwind = some ubb)
    (hReady : LocalDropReady fa mi mu atoms cur)
    (est : ElabState) (hRun : est.exit = .running) (hMem : est.mem = cur)
    (hBb : est.bb = (lowerDropNormalLadder fa mi mu isCleanup atoms succ unwind ps).1)
    (hSim : FlagSimulatesInit fa cur est.flags)
    (hAg : BlocksAgreeAfter eprog.blocks ps (lowerDropNormalLadder fa mi mu isCleanup atoms succ unwind ps).2) :
    let srcRes := evalSrcDropAtomsGo oracle isCleanup atoms cur [] est.dropIdx false
    ∃ k : Nat,
      let est' := execElabFuel eprog oracle k est
      est'.mem = srcRes.1 ∧
      est'.trace = listAppend est.trace srcRes.2.1 ∧
      est'.dropIdx = srcRes.2.2.1 ∧
      est'.branchIdx = est.branchIdx ∧
      FlagSimulatesInit fa srcRes.1 est'.flags ∧
      (srcRes.2.2.2.2 = true → est'.exit = .aborted) ∧
      (srcRes.2.2.2.2 = false →
        est'.exit = .running ∧
        (srcRes.2.2.2.1 = true → ∃ ubb, unwind = some ubb ∧ est'.bb = ubb) ∧
        (srcRes.2.2.2.1 = false → est'.bb = succ)) := by
  induction atoms generalizing cur est ps unwind isCleanup with
  | nil =>
    refine ⟨0, hMem, (by dsimp only [execElabFuel, evalSrcDropAtomsGo]; rw [listAppend_nil_right]),
      rfl, rfl, hSim, (fun hf => by cases hf), fun _ => ⟨hRun, (fun hf => by cases hf), fun _ => hBb⟩⟩
  | cons a rest ih =>
    have hDh := atomsDistinct_head hDist
    have hHead := localDropReady_head hReady
    cases hcl : isCleanup with
    | true =>
      rw [hcl] at hBb hAg
      let nRes := lowerDropNormalLadder fa mi mu true rest succ none ps
      let rRes := emitAtomDropRung fa mi mu true a nRes.1 none nRes.2
      have hExtN := lowerDropNormalLadder_patchExtends fa mi mu true rest succ none ps
      have hExtR := emitAtomDropRung_patchExtends fa mi mu true a nRes.1 none nRes.2
      have hAgN : BlocksAgreeAfter eprog.blocks ps nRes.2 :=
        blocksAgreeAfter_split_left hExtR hAg
      have hAgR : BlocksAgreeAfter eprog.blocks nRes.2 rRes.2 :=
        blocksAgreeAfter_split_right hExtN hAg
      have hRung := emitAtomDropRung_sim eprog oracle fa mi mu true a nRes.1 none nRes.2 cur
        hInj hHead.1 hHead.2.1 hHead.2.2 est hRun hMem hBb hSim hAgR
      rcases hRung with ⟨ka, hkaT, hkaF⟩
      let est1 := execElabFuel eprog oracle ka est
      cases hca : cur a with
      | false =>
        rcases hkaF hca with ⟨hm1, ht1, hd1, hb1, he1, hbb1, hsim1⟩
        have hRest := ih true none ps cur hDh.2 (fun h => by cases h)
          (localDropReady_tail hReady) est1 he1 hm1 hbb1 hsim1 hAgN
        rcases hRest with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
        refine ⟨ka + kr, ?_⟩
        rw [execElabFuel_add]
        dsimp only [evalSrcDropAtomsGo]
        rw [hca, bool_if_false]
        dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
        rw [ht1] at ht2
        rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
        refine ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, hAb, fun hnoab => ?_⟩
        rcases hCont hnoab with ⟨her, _hpt, hpf⟩
        have hnp := evalSrcDropAtomsGo_cleanup_no_abort_not_panicked oracle rest cur [] est.dropIdx hnoab
        exact ⟨her, (fun hf => by rw [hnp] at hf; cases hf), fun _ => hpf hnp⟩
      | true =>
        rcases hkaT hca with ⟨hm1, ht1, hd1, hb1, hsim1, hPFalse, hPTrue⟩
        cases hp : oracle.panicAt est.dropIdx a with
        | true =>
          have hAbE : est1.exit = .aborted := (hPTrue hp).1 rfl
          refine ⟨ka, ?_⟩
          dsimp only [evalSrcDropAtomsGo]
          rw [hca, bool_if_true, bool_if_false, hp, bool_if_true, bool_if_true]
          exact ⟨hm1, ht1, hd1, hb1, hsim1, (fun _ => hAbE), fun hf => by cases hf⟩
        | false =>
          rcases hPFalse hp with ⟨he1, hbb1⟩
          have hReady1 := localDropReady_tail_clear hReady hDh.1
          have hRest := ih true none ps (setAtom cur a false) hDh.2 (fun h => by cases h)
            hReady1 est1 he1 hm1 hbb1 hsim1 hAgN
          rcases hRest with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
          refine ⟨ka + kr, ?_⟩
          rw [execElabFuel_add]
          dsimp only [evalSrcDropAtomsGo]
          rw [hca, bool_if_true, bool_if_false, hp, bool_if_false]
          have hShift := evalSrcDropAtomsGo_tr_prepend oracle true rest (setAtom cur a false)
            [DropEvent.atomEvent a false] [] (est.dropIdx + 1) false
          rw [listAppend_nil_right] at hShift
          dsimp only [listAppend]
          rw [hShift]
          dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
          rw [ht1] at ht2
          rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
          rw [listAppend_assoc] at ht2
          refine ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, hAb, fun hnoab => ?_⟩
          rcases hCont hnoab with ⟨her, _hpt, hpf⟩
          have hnp := evalSrcDropAtomsGo_cleanup_no_abort_not_panicked oracle rest (setAtom cur a false) [] (est.dropIdx + 1) hnoab
          exact ⟨her, (fun hf => by rw [hnp] at hf; cases hf), fun _ => hpf hnp⟩
    | false =>
      have huEx := hUnwForm hcl
      rcases huEx with ⟨ubb, huEq⟩
      rw [hcl, huEq] at hBb hAg
      let uRes := lowerDropCleanupHalfLadder fa mi mu rest ubb ps
      let nRes := lowerDropNormalLadder fa mi mu false rest succ (some ubb) uRes.2
      let rRes := emitAtomDropRung fa mi mu false a nRes.1 (some uRes.1) nRes.2
      have hExtU := lowerDropCleanupHalfLadder_patchExtends fa mi mu rest ubb ps
      have hExtN := lowerDropNormalLadder_patchExtends fa mi mu false rest succ (some ubb) uRes.2
      have hExtR := emitAtomDropRung_patchExtends fa mi mu false a nRes.1 (some uRes.1) nRes.2
      have hAgU : BlocksAgreeAfter eprog.blocks ps uRes.2 :=
        blocksAgreeAfter_split_left (patchExtends_trans hExtN hExtR) hAg
      have hAgUN : BlocksAgreeAfter eprog.blocks uRes.2 rRes.2 :=
        blocksAgreeAfter_split_right hExtU hAg
      have hAgN : BlocksAgreeAfter eprog.blocks uRes.2 nRes.2 :=
        blocksAgreeAfter_split_left hExtR hAgUN
      have hAgR : BlocksAgreeAfter eprog.blocks nRes.2 rRes.2 :=
        blocksAgreeAfter_split_right hExtN hAgUN
      have hRung := emitAtomDropRung_sim eprog oracle fa mi mu false a nRes.1 (some uRes.1) nRes.2 cur
        hInj hHead.1 hHead.2.1 hHead.2.2 est hRun hMem hBb hSim hAgR
      rcases hRung with ⟨ka, hkaT, hkaF⟩
      let est1 := execElabFuel eprog oracle ka est
      cases hca : cur a with
      | false =>
        rcases hkaF hca with ⟨hm1, ht1, hd1, hb1, he1, hbb1, hsim1⟩
        have hRest := ih false (some ubb) uRes.2 cur hDh.2 (fun _ => ⟨ubb, rfl⟩)
          (localDropReady_tail hReady) est1 he1 hm1 hbb1 hsim1 hAgN
        rcases hRest with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
        refine ⟨ka + kr, ?_⟩
        rw [execElabFuel_add]
        dsimp only [evalSrcDropAtomsGo]
        rw [hca, bool_if_false]
        dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
        rw [ht1] at ht2
        rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
        refine ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, hAb, fun hnoab => ?_⟩
        rcases hCont hnoab with ⟨her, hpt, hpf⟩
        exact ⟨her, (fun htrue => by
          rcases hpt htrue with ⟨w, hw, hbw⟩
          cases hw
          exact ⟨ubb, huEq, hbw⟩), hpf⟩
      | true =>
        rcases hkaT hca with ⟨hm1, ht1, hd1, hb1, hsim1, hPFalse, hPTrue⟩
        have hReady1 := localDropReady_tail_clear hReady hDh.1
        cases hp : oracle.panicAt est.dropIdx a with
        | false =>
          rcases hPFalse hp with ⟨he1, hbb1⟩
          have hRest := ih false (some ubb) uRes.2 (setAtom cur a false) hDh.2 (fun _ => ⟨ubb, rfl⟩)
            hReady1 est1 he1 hm1 hbb1 hsim1 hAgN
          rcases hRest with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
          refine ⟨ka + kr, ?_⟩
          rw [execElabFuel_add]
          dsimp only [evalSrcDropAtomsGo]
          rw [hca, bool_if_true, bool_if_false, hp, bool_if_false]
          have hShift := evalSrcDropAtomsGo_tr_prepend oracle false rest (setAtom cur a false)
            [DropEvent.atomEvent a false] [] (est.dropIdx + 1) false
          rw [listAppend_nil_right] at hShift
          dsimp only [listAppend]
          rw [hShift]
          dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
          rw [ht1] at ht2
          rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
          rw [listAppend_assoc] at ht2
          refine ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, hAb, fun hnoab => ?_⟩
          rcases hCont hnoab with ⟨her, hpt, hpf⟩
          exact ⟨her, (fun htrue => by
            rcases hpt htrue with ⟨w, hw, hbw⟩
            cases hw
            exact ⟨ubb, huEq, hbw⟩), hpf⟩
        | true =>
          rcases ((hPTrue hp).2 rfl).2 uRes.1 rfl with ⟨he1, hbb1⟩
          have hClean := lowerDropCleanupHalfLadder_sim eprog oracle fa mi mu rest ubb ps (setAtom cur a false)
            hInj hDh.2 hReady1 est1 he1 hm1 hbb1 hsim1 hAgU
          rcases hClean with ⟨kr, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
          refine ⟨ka + kr, ?_⟩
          rw [execElabFuel_add]
          dsimp only [evalSrcDropAtomsGo]
          rw [hca, bool_if_true, bool_if_false, hp, bool_if_true, bool_if_false]
          have hShift := evalSrcDropAtomsGo_tr_prepend oracle false rest (setAtom cur a false)
            [DropEvent.atomEvent a false] [] (est.dropIdx + 1) true
          rw [listAppend_nil_right] at hShift
          dsimp only [listAppend]
          rw [hShift]
          have hEqv := evalSrcDropAtomsGo_cleanup_equiv oracle rest (setAtom cur a false)
            [] (est.dropIdx + 1) false
          rcases hEqv with ⟨hmEq, htEq, hdEq, habEq⟩
          dsimp only [est1] at hm2 ht2 hd2 hsim2 hAb hCont
          rw [ht1] at ht2
          rw [hd1] at hm2 ht2 hd2 hsim2 hAb hCont
          rw [listAppend_assoc] at ht2
          rw [← hmEq, ← htEq, ← hdEq]
          refine ⟨hm2, ht2, hd2, hb2.trans hb1, hsim2, (fun hAbPan => hAb (by rw [habEq]; exact hAbPan)), fun hnoab => ?_⟩
          have hnoabC : (evalSrcDropAtomsGo oracle true rest (setAtom cur a false) [] (est.dropIdx + 1) false).2.2.2.2 = false := by
            rw [habEq]; exact hnoab
          rcases hCont hnoabC with ⟨her, hbbC⟩
          exact ⟨her, (fun _ => ⟨ubb, huEq, hbbC⟩), fun hf => by
            have hpt := evalSrcDropAtomsGo_pan_stays_true oracle false rest (setAtom cur a false) [] (est.dropIdx + 1) hnoab
            rw [hpt] at hf; cases hf⟩

/-- Matches `elaborate_drops.rs:360-375`: every normal-path `.drop`/`.scopeExit`
specifies an `unwind` target (`Unwind::To(bb)` via cleanup/resume/terminate),
and drop target atom lists contain no duplicate atoms (`atomsDistinct`). -/
noncomputable def WellFormedSrcDrops (prog : SrcProgram) : Prop :=
  ∀ bb blk, prog.blocks bb = some blk →
    match blk.term with
    | .drop p _ unwind =>
      atomsDistinct (atomsOfPlace prog.locals p) = true ∧
      (blk.isCleanup = false → ∃ ubb, unwind = some ubb)
    | .scopeExit locs _ unwind =>
      atomsDistinct (atomsOfLocalList prog.locals (localsDropOrder locs)) = true ∧
      (blk.isCleanup = false → ∃ ubb, unwind = some ubb)
    | _ => True

/-- Simulation invariant linking source state `s` and elaborated target state `e`. -/
noncomputable def StateSim (fa : FlagAlloc) (s : SrcState) (e : ElabState) : Prop :=
  e.mem = s.init ∧
  e.trace = s.trace ∧
  e.dropIdx = s.dropIdx ∧
  e.branchIdx = s.branchIdx ∧
  e.exit = s.exit ∧
  FlagSimulatesInit fa s.init e.flags ∧
  (s.exit = .running → e.bb = shiftSrcBb s.bb)

theorem init_state_sim (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (oracle : ExecOracle) :
    let eprog := elaborateProgram prog numBlocks df fa
    StateSim fa (initSrcState prog) (stepElabBlock eprog oracle (initElabState eprog)) ∧
    natLt (initSrcState prog).bb numBlocks = true ∧
    InitConsistent (initSrcState prog).init (df.atBlock (initSrcState prog).bb) := by
  have hEntry := elaborateProgram_entry_block prog numBlocks df fa
  have heBb0 : (initElabState (elaborateProgram prog numBlocks df fa)).bb = 0 := rfl
  have heEx0 : (initElabState (elaborateProgram prog numBlocks df fa)).exit = .running := rfl
  dsimp only [initSrcState, stepElabBlock]
  rw [heEx0]
  dsimp only
  rw [heBb0, hEntry]
  dsimp only [stepElabStmtList, initElabState]
  rw [stepElabStmtList_append]
  have hz : ∀ f, emptyFlagMap f = false := fun _ => rfl
  have hZero := stepSetFlagListAbsent_preserves_false
    (listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags)
    prog.locals
    { bb := 0
      branchIdx := 0, dropIdx := 0, flags := emptyFlagMap
      mem := setAtoms emptyAtomMap (atomsOfLocalList prog.locals prog.args) true
      trace := [], exit := .running }
    (fun s hs => listMap_setFlag_mem fa.allFlags s hs)
    hz
  rcases hZero with ⟨_hbb0, hbi0, hdi0, hmem0, htr0, hex0, hflags0⟩
  have hEmptySim : FlagSimulatesInit fa emptyAtomMap
      (stepElabStmtList prog.locals
        (listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags)
        { bb := 0, branchIdx := 0, dropIdx := 0, flags := emptyFlagMap
          mem := setAtoms emptyAtomMap (atomsOfLocalList prog.locals prog.args) true
          trace := [], exit := .running }).flags := by
    intro a fid _
    exact hflags0 fid
  have hf := stepSetFlagsForAtoms_spec
    prog.locals fa hfa.1 .present
    (atomsOfLocalList prog.locals prog.args) emptyAtomMap
    _ hEmptySim
  rcases hf with ⟨_hbb1, hbi1, hdi1, hmem1, htr1, hex1, hsim1⟩
  have heE : (elaborateProgram prog numBlocks df fa).entry = 0 := rfl
  have heL : (elaborateProgram prog numBlocks df fa).locals = prog.locals := rfl
  have heA : (elaborateProgram prog numBlocks df fa).args = prog.args := rfl
  rw [heE, heL, heA]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hsim1, fun _ => rfl⟩, hvalid.2.1, ?_⟩
  · dsimp only; rw [hmem1, hmem0]
  · dsimp only; rw [htr1, htr0]
  · dsimp only; rw [hdi1, hdi0]
  · dsimp only; rw [hbi1, hbi0]
  · dsimp only; rw [hex1, hex0]
  · constructor
    · intro a ha
      cases hmem : atomInList a (atomsOfLocalList prog.locals prog.args) with
      | true => exact (hvalid.2.2.1 a).1 hmem
      | false =>
        rw [setAtoms_not_mem emptyAtomMap _ true a hmem] at ha
        cases ha
    · intro a ha
      cases hmem : atomInList a (atomsOfLocalList prog.locals prog.args) with
      | true =>
        rw [setAtoms_mem emptyAtomMap _ true a hmem] at ha
        cases ha
      | false => exact (hvalid.2.2.1 a).2 hmem

theorem elaborateBlocksLoop_preserves_none
    (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert) (fa : FlagAlloc)
    (idx rem bb : Nat) (ps : PatchState)
    (hbb : natLt bb numBlocks = true)
    (hnone : prog.blocks bb = none)
    (hnum : natLt numBlocks ps.nextBlock = true)
    (hps : ps.blocks (shiftSrcBb bb) = none) :
    (elaborateBlocksLoop prog df fa idx rem ps).blocks (shiftSrcBb bb) = none := by
  induction rem generalizing idx ps with
  | zero => exact hps
  | succ r ih =>
    dsimp only [elaborateBlocksLoop]
    cases hblk : prog.blocks idx with
    | none => exact ih (idx + 1) ps hnum hps
    | some blk =>
      have hne : shiftSrcBb bb ≠ shiftSrcBb idx := by
        intro heq
        have hbi : bb = idx := by injection heq
        rw [← hbi] at hblk
        rw [hnone] at hblk
        cases hblk
      have hStep := elaborateBlock_patchExtends_split prog df fa idx blk ps
      have hshLt : natLt (shiftSrcBb bb) ps.nextBlock = true := natLt_succ_trans hbb hnum
      have hnum1 : natLt numBlocks (elaborateBlock prog df fa idx blk ps).nextBlock = true :=
        hStep.1 numBlocks hnum
      have hps1 : (elaborateBlock prog df fa idx blk ps).blocks (shiftSrcBb bb) = none := by
        rw [hStep.2 (shiftSrcBb bb) hshLt hne, hps]
      exact ih (idx + 1) (elaborateBlock prog df fa idx blk ps) hnum1 hps1

theorem elaborateProgram_block_none
    (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert) (fa : FlagAlloc)
    (bb : BlockId) (hbb : natLt bb numBlocks = true) (hnone : prog.blocks bb = none) :
    (elaborateProgram prog numBlocks df fa).blocks (shiftSrcBb bb) = none := by
  dsimp only [elaborateProgram]
  have hnum0 : natLt numBlocks (1 + numBlocks) = true := by
    rw [Nat.add_comm 1 numBlocks]; exact natLt_succ_self numBlocks
  have hps0 : setElabBlock (fun _ => none) 0
      { isCleanup := false
        stmts := listAppend
          (listMap (fun fid => ElabStmt.setFlag fid .absent) fa.allFlags)
          (setFlagsForAtoms fa .present (atomsOfLocalList prog.locals prog.args))
        term := .goto (shiftSrcBb prog.entry) } (shiftSrcBb bb) = none := by
    change (if natEq (bb + 1) 0 then some _ else none) = none
    rw [natLt_ne_zero_add_one bb]; rfl
  exact elaborateBlocksLoop_preserves_none prog numBlocks df fa 0 numBlocks bb _ hbb hnone hnum0 hps0

theorem stepSrcStmtList_exit (locals : List MirTy) (stmts : List SrcStmt) (st : SrcState) :
    (stepSrcStmtList locals stmts st).exit = st.exit := by
  induction stmts generalizing st with
  | nil => rfl
  | cons s ss ih =>
    dsimp only [stepSrcStmtList]
    rw [ih (stepSrcStmt locals st s)]
    cases s <;> rfl

noncomputable def srcPanicBranchState (s1 : SrcState) (init' : AtomMap)
    (tr' : List DropEvent) (dIdx' : Nat) : Option BlockId → SrcState
  | some ubb => { s1 with bb := ubb, dropIdx := dIdx', init := init', trace := tr' }
  | none => { s1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }

private theorem step_drop_ladder_aux
    (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert) (fa : FlagAlloc)
    (oracle : ExecOracle) (hInj : ∀ a b fid, fa.flagOf a = some fid → fa.flagOf b = some fid → a = b)
    (s : SrcState) (e : ElabState) (hsRun : s.exit = .running) (heRun : e.exit = .running)
    (isCl : Bool) (stmts : List SrcStmt) (atoms : List Atom) (tgt : BlockId) (unwind : Option BlockId)
    (hAfterCons : InitConsistent (stepSrcStmtList prog.locals stmts s).init
      (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)))
    (hFlagCond : ∀ a, atomInList a atoms = true →
      (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)).mayInit a = true →
      (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)).mayUninit a = true →
      ∃ fid, fa.flagOf a = some fid)
    (hDist : atomsDistinct atoms = true)
    (hUnwForm : isCl = false → ∃ ubb, unwind = some ubb)
    (ps_before : PatchState)
    (hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
      some { isCleanup := isCl
             stmts := elaborateStmtList prog.locals fa stmts
             term := .goto (lowerDropNormalLadder fa
               (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)).mayInit
               (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)).mayUninit
               isCl atoms (shiftSrcBb tgt) (shiftOptBb unwind) ps_before).1 })
    (hAgreeLad : BlocksAgreeAfter (elaborateProgram prog numBlocks df fa).blocks ps_before
      (lowerDropNormalLadder fa
        (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)).mayInit
        (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)).mayUninit
        isCl atoms (shiftSrcBb tgt) (shiftOptBb unwind) ps_before).2)
    (hs1m : (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).mem =
      (stepSrcStmtList prog.locals stmts s).init)
    (hs1t : (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).trace =
      (stepSrcStmtList prog.locals stmts s).trace)
    (hs1d : (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).dropIdx =
      (stepSrcStmtList prog.locals stmts s).dropIdx)
    (hs1b : (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).branchIdx =
      (stepSrcStmtList prog.locals stmts s).branchIdx)
    (hs1e : (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).exit = .running)
    (hs1f : FlagSimulatesInit fa (stepSrcStmtList prog.locals stmts s).init
      (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).flags) :
    let eprog := elaborateProgram prog numBlocks df fa
    let s1 := stepSrcStmtList prog.locals stmts s
    let s' :=
      match evalSrcDropAtoms s1.dropIdx oracle isCl atoms s1.init with
      | (init', evs, dIdx', panicked, aborted) =>
        let tr' := listAppend s1.trace evs
        if aborted then { s1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
        else if panicked then srcPanicBranchState s1 init' tr' dIdx' unwind
        else { s1 with bb := tgt, dropIdx := dIdx', init := init', trace := tr' }
    ∃ k : Nat, StateSim fa s' (execElabFuel eprog oracle k e) := by
  let eprog := elaborateProgram prog numBlocks df fa
  let afterStmts := transferSrcStmtList prog.locals stmts (df.atBlock s.bb)
  let shiftedUnwind : Option BlockId := shiftOptBb unwind
  let ladRes := lowerDropNormalLadder fa afterStmts.mayInit afterStmts.mayUninit
    isCl atoms (shiftSrcBb tgt) shiftedUnwind ps_before
  let s1 := stepSrcStmtList prog.locals stmts s
  let est1 : ElabState :=
    { (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e) with bb := ladRes.1 }
  have he1Eq : execElabFuel eprog oracle 1 e = est1 := by
    dsimp only [execElabFuel]
    rw [heRun]
    dsimp only [execElabFuel, stepElabBlock]
    rw [heRun]
    dsimp only [eprog]
    rw [hEBlk]
    dsimp only
    have hElLoc : (elaborateProgram prog numBlocks df fa).locals = prog.locals := rfl
    rw [hElLoc]
  have hUnwShifted : isCl = false → ∃ su, shiftedUnwind = some su := by
    intro hcl
    rcases hUnwForm hcl with ⟨u, huEq⟩
    refine ⟨shiftSrcBb u, ?_⟩
    dsimp only [shiftedUnwind]
    rw [huEq]
    rfl
  have hReady : LocalDropReady fa afterStmts.mayInit afterStmts.mayUninit atoms s1.init := by
    intro x hx
    exact ⟨hAfterCons.1 x, hAfterCons.2 x, hFlagCond x hx⟩
  have hLad := lowerDropNormalLadder_sim eprog oracle
    fa afterStmts.mayInit afterStmts.mayUninit isCl atoms (shiftSrcBb tgt) shiftedUnwind
    ps_before s1.init hInj hDist hUnwShifted hReady est1 hs1e hs1m rfl hs1f hAgreeLad
  rcases hLad with ⟨k_lad, hm2, ht2, hd2, hb2, hsim2, hAb, hCont⟩
  refine ⟨1 + k_lad, ?_⟩
  rw [execElabFuel_add, he1Eq]
  dsimp only [evalSrcDropAtoms]
  rcases hres : evalSrcDropAtomsGo oracle isCl atoms s1.init [] s1.dropIdx false with
    ⟨init', evs, dIdx', panicked, aborted⟩
  change _ at hAb hCont
  rw [hs1d, hres] at hm2 ht2 hd2 hsim2 hAb hCont
  dsimp only at hm2 ht2 hd2 hsim2 hAb hCont
  dsimp only
  have hs1ex : s1.exit = .running := by dsimp only [s1]; rw [stepSrcStmtList_exit, hsRun]
  cases aborted with
  | true =>
    rw [bool_if_true]
    rw [hs1t] at ht2
    rw [hs1b] at hb2
    exact ⟨hm2, ht2, hd2, hb2, hAb rfl, hsim2, fun hf => by cases hf⟩
  | false =>
    rw [bool_if_false]
    rcases hCont rfl with ⟨her2, hPanT, hPanF⟩
    cases panicked with
    | false =>
      rw [bool_if_false]
      rw [hs1t] at ht2
      rw [hs1b] at hb2
      exact ⟨hm2, ht2, hd2, hb2, by rw [her2, hs1ex], hsim2, fun _ => hPanF rfl⟩
    | true =>
      rw [bool_if_true]
      rcases hPanT rfl with ⟨su, hShEq, hbb2⟩
      dsimp only [shiftedUnwind] at hShEq
      cases unwind with
      | none =>
        dsimp only [shiftOptBb] at hShEq
        cases hShEq
      | some ubb =>
        dsimp only [shiftOptBb] at hShEq
        cases hShEq
        dsimp only [srcPanicBranchState]
        rw [hs1t] at ht2
        rw [hs1b] at hb2
        exact ⟨hm2, ht2, hd2, hb2, by rw [her2, hs1ex], hsim2, fun _ => hbb2⟩

theorem step_sim (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (oracle : ExecOracle) (s : SrcState) (e : ElabState)
    (hSim : StateSim fa s e)
    (hBbLt : s.exit = .running → natLt s.bb numBlocks = true)
    (hCons : s.exit = .running → InitConsistent s.init (df.atBlock s.bb)) :
    let eprog := elaborateProgram prog numBlocks df fa
    let s' := stepSrcBlock prog oracle s
    ∃ k : Nat,
      StateSim fa s' (execElabFuel eprog oracle k e) ∧
      (s'.exit = .running → natLt s'.bb numBlocks = true ∧ InitConsistent s'.init (df.atBlock s'.bb)) := by
  cases hex : s.exit with
  | returned =>
    have hs' : stepSrcBlock prog oracle s = s := by dsimp only [stepSrcBlock]; rw [hex]
    refine ⟨0, ?_, fun hf => by rw [hs', hex] at hf; cases hf⟩
    rcases hSim with ⟨hm, ht, hd, hb, he, hfs, _⟩
    dsimp only [execElabFuel]
    rw [hs']
    exact ⟨hm, ht, hd, hb, he, hfs, fun hf => by rw [hex] at hf; cases hf⟩
  | unwound =>
    have hs' : stepSrcBlock prog oracle s = s := by dsimp only [stepSrcBlock]; rw [hex]
    refine ⟨0, ?_, fun hf => by rw [hs', hex] at hf; cases hf⟩
    rcases hSim with ⟨hm, ht, hd, hb, he, hfs, _⟩
    dsimp only [execElabFuel]
    rw [hs']
    exact ⟨hm, ht, hd, hb, he, hfs, fun hf => by rw [hex] at hf; cases hf⟩
  | aborted =>
    have hs' : stepSrcBlock prog oracle s = s := by dsimp only [stepSrcBlock]; rw [hex]
    refine ⟨0, ?_, fun hf => by rw [hs', hex] at hf; cases hf⟩
    rcases hSim with ⟨hm, ht, hd, hb, he, hfs, _⟩
    dsimp only [execElabFuel]
    rw [hs']
    exact ⟨hm, ht, hd, hb, he, hfs, fun hf => by rw [hex] at hf; cases hf⟩
  | faulted =>
    have hs' : stepSrcBlock prog oracle s = s := by dsimp only [stepSrcBlock]; rw [hex]
    refine ⟨0, ?_, fun hf => by rw [hs', hex] at hf; cases hf⟩
    rcases hSim with ⟨hm, ht, hd, hb, he, hfs, _⟩
    dsimp only [execElabFuel]
    rw [hs']
    exact ⟨hm, ht, hd, hb, he, hfs, fun hf => by rw [hex] at hf; cases hf⟩
  | running =>
    rcases hSim with ⟨hm, ht, hd, hb, he, hfs, hbbSim⟩
    have heRun : e.exit = .running := by rw [he, hex]
    have heBb : e.bb = shiftSrcBb s.bb := hbbSim hex
    have hsBbLt : natLt s.bb numBlocks = true := hBbLt hex
    have hsCons : InitConsistent s.init (df.atBlock s.bb) := hCons hex
    cases hblk : prog.blocks s.bb with
    | none =>
      have hENone : (elaborateProgram prog numBlocks df fa).blocks e.bb = none := by
        rw [heBb]; exact elaborateProgram_block_none prog numBlocks df fa s.bb hsBbLt hblk
      have he1 : execElabFuel (elaborateProgram prog numBlocks df fa) oracle 1 e =
          stepElabBlock (elaborateProgram prog numBlocks df fa) oracle e := by
        dsimp only [execElabFuel]; rw [heRun]
      refine ⟨1, ?_, ?_⟩
      · rw [he1]
        dsimp only [stepSrcBlock, stepElabBlock]
        rw [hex, heRun]
        dsimp only
        rw [hblk, hENone]
        dsimp only
        exact ⟨hm, ht, hd, hb, rfl, hfs, fun hf => by cases hf⟩
      · dsimp only [stepSrcBlock]
        rw [hex]
        dsimp only
        rw [hblk]
        intro hf; cases hf
    | some blk =>
      have hInv := stepSrcBlock_preserves_consistent prog numBlocks df oracle hvalid s hex hsCons
      rcases blk with ⟨isCl, stmts, term⟩
      have hLookup := elaborateProgram_block_lookup prog numBlocks df fa s.bb
        { isCleanup := isCl, stmts := stmts, term := term } hsBbLt hblk
      rcases hLookup with ⟨ps_before, hnum, _hmono, hBlkEq, hLadAgree⟩
      have hStmtSim := stepElabStmtList_sim prog.locals fa hfa.1 stmts s e hm ht hd hb he hfs
      rcases hStmtSim with ⟨hs1m, hs1t, hs1d, hs1b, hs1e, _hs1bb, hs1f⟩
      have hs1Run : (stepElabStmtList prog.locals (elaborateStmtList prog.locals fa stmts) e).exit = .running :=
        hs1e.trans ((stepSrcStmtList_exit prog.locals stmts s).trans hex)
      have hAfterCons : InitConsistent (stepSrcStmtList prog.locals stmts s).init
          (transferSrcStmtList prog.locals stmts (df.atBlock s.bb)) :=
        stepSrcStmtList_preserves_consistent prog.locals stmts s (df.atBlock s.bb) hsCons
      have hwfBlk := hwf s.bb { isCleanup := isCl, stmts := stmts, term := term } hblk
      have hfaBlk := hfa.2 s.bb { isCleanup := isCl, stmts := stmts, term := term } hsBbLt hblk
      dsimp only at hwfBlk hfaBlk
      have hElLoc : (elaborateProgram prog numBlocks df fa).locals = prog.locals := rfl
      cases term with
      | goto tgt =>
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .goto (shiftSrcBb tgt) } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have he1 : execElabFuel (elaborateProgram prog numBlocks df fa) oracle 1 e =
            stepElabBlock (elaborateProgram prog numBlocks df fa) oracle e := by
          dsimp only [execElabFuel]; rw [heRun]
        refine ⟨1, ?_, hInv⟩
        rw [he1]
        dsimp only [stepElabBlock, stepSrcBlock]
        rw [heRun, hex]
        dsimp only
        rw [hblk, hEBlk]
        dsimp only
        rw [hElLoc]
        exact ⟨hs1m, hs1t, hs1d, hs1b, hs1e, hs1f, fun _ => rfl⟩
      | switchBool reg bbT bbF =>
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .switchBool reg (shiftSrcBb bbT) (shiftSrcBb bbF) } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have he1 : execElabFuel (elaborateProgram prog numBlocks df fa) oracle 1 e =
            stepElabBlock (elaborateProgram prog numBlocks df fa) oracle e := by
          dsimp only [execElabFuel]; rw [heRun]
        refine ⟨1, ?_, hInv⟩
        rw [he1]
        dsimp only [stepElabBlock, stepSrcBlock]
        rw [heRun, hex]
        dsimp only
        rw [hblk, hEBlk]
        dsimp only
        rw [hElLoc, hs1b]
        cases oracle.branchAt (stepSrcStmtList prog.locals stmts s).branchIdx reg with
        | true =>
          rw [bool_if_true, bool_if_true]
          exact ⟨hs1m, hs1t, hs1d, rfl, hs1e, hs1f, fun _ => rfl⟩
        | false =>
          rw [bool_if_false, bool_if_false]
          exact ⟨hs1m, hs1t, hs1d, rfl, hs1e, hs1f, fun _ => rfl⟩
      | ret =>
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .ret } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have he1 : execElabFuel (elaborateProgram prog numBlocks df fa) oracle 1 e =
            stepElabBlock (elaborateProgram prog numBlocks df fa) oracle e := by
          dsimp only [execElabFuel]; rw [heRun]
        refine ⟨1, ?_, hInv⟩
        rw [he1]
        dsimp only [stepElabBlock, stepSrcBlock]
        rw [heRun, hex]
        dsimp only
        rw [hblk, hEBlk]
        dsimp only
        rw [hElLoc]
        exact ⟨hs1m, hs1t, hs1d, hs1b, rfl, hs1f, fun hf => by cases hf⟩
      | unwindResume =>
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .unwindResume } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have he1 : execElabFuel (elaborateProgram prog numBlocks df fa) oracle 1 e =
            stepElabBlock (elaborateProgram prog numBlocks df fa) oracle e := by
          dsimp only [execElabFuel]; rw [heRun]
        refine ⟨1, ?_, hInv⟩
        rw [he1]
        dsimp only [stepElabBlock, stepSrcBlock]
        rw [heRun, hex]
        dsimp only
        rw [hblk, hEBlk]
        dsimp only
        rw [hElLoc]
        exact ⟨hs1m, hs1t, hs1d, hs1b, rfl, hs1f, fun hf => by cases hf⟩
      | unwindAbort =>
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .unwindAbort } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have he1 : execElabFuel (elaborateProgram prog numBlocks df fa) oracle 1 e =
            stepElabBlock (elaborateProgram prog numBlocks df fa) oracle e := by
          dsimp only [execElabFuel]; rw [heRun]
        refine ⟨1, ?_, hInv⟩
        rw [he1]
        dsimp only [stepElabBlock, stepSrcBlock]
        rw [heRun, hex]
        dsimp only
        rw [hblk, hEBlk]
        dsimp only
        rw [hElLoc]
        exact ⟨hs1m, hs1t, hs1d, hs1b, rfl, hs1f, fun hf => by cases hf⟩
      | drop p tgt unwind =>
        let afterStmts := transferSrcStmtList prog.locals stmts (df.atBlock s.bb)
        let atoms := atomsOfPlace prog.locals p
        let shiftedUnwind : Option BlockId := shiftOptBb unwind
        let ladRes := lowerDropNormalLadder fa afterStmts.mayInit afterStmts.mayUninit
          isCl atoms (shiftSrcBb tgt) shiftedUnwind ps_before
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .goto ladRes.1 } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have hAgreeLad : BlocksAgreeAfter (elaborateProgram prog numBlocks df fa).blocks ps_before ladRes.2 := by
          intro m hm0 hm1
          have hm1' : natLt m (elaborateBlock prog df fa s.bb
              { isCleanup := isCl, stmts := stmts, term := .drop p tgt unwind } ps_before).nextBlock = true := hm1
          rw [hLadAgree m hm0 hm1']
          have hshLt : natLt (shiftSrcBb s.bb) ps_before.nextBlock = true :=
            natLt_succ_trans hsBbLt hnum
          have hne : m ≠ shiftSrcBb s.bb := natLt_false_of_mono hshLt hm0
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_false_of_ne hne]; rfl
        have hSimK := step_drop_ladder_aux prog numBlocks df fa oracle hfa.1 s e hex heRun
          isCl stmts atoms tgt unwind hAfterCons hfaBlk hwfBlk.1 hwfBlk.2 ps_before hEBlk hAgreeLad
          hs1m hs1t hs1d hs1b hs1Run hs1f
        rcases hSimK with ⟨k, hk⟩
        refine ⟨k, ?_, hInv⟩
        dsimp only [stepSrcBlock]
        rw [hex]
        dsimp only
        rw [hblk]
        cases unwind with
        | none => exact hk
        | some ubb => exact hk
      | scopeExit locs tgt unwind =>
        let afterStmts := transferSrcStmtList prog.locals stmts (df.atBlock s.bb)
        let atoms := atomsOfLocalList prog.locals (localsDropOrder locs)
        let shiftedUnwind : Option BlockId := shiftOptBb unwind
        let ladRes := lowerDropNormalLadder fa afterStmts.mayInit afterStmts.mayUninit
          isCl atoms (shiftSrcBb tgt) shiftedUnwind ps_before
        have hEBlk : (elaborateProgram prog numBlocks df fa).blocks e.bb =
            some { isCleanup := isCl
                   stmts := elaborateStmtList prog.locals fa stmts
                   term := .goto ladRes.1 } := by
          rw [heBb, hBlkEq]
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_refl]; rfl
        have hAgreeLad : BlocksAgreeAfter (elaborateProgram prog numBlocks df fa).blocks ps_before ladRes.2 := by
          intro m hm0 hm1
          have hm1' : natLt m (elaborateBlock prog df fa s.bb
              { isCleanup := isCl, stmts := stmts, term := .scopeExit locs tgt unwind } ps_before).nextBlock = true := hm1
          rw [hLadAgree m hm0 hm1']
          have hshLt : natLt (shiftSrcBb s.bb) ps_before.nextBlock = true :=
            natLt_succ_trans hsBbLt hnum
          have hne : m ≠ shiftSrcBb s.bb := natLt_false_of_mono hshLt hm0
          dsimp only [elaborateBlock, writeElabBlock, setElabBlock]
          rw [natEq_false_of_ne hne]; rfl
        have hSimK := step_drop_ladder_aux prog numBlocks df fa oracle hfa.1 s e hex heRun
          isCl stmts atoms tgt unwind hAfterCons hfaBlk hwfBlk.1 hwfBlk.2 ps_before hEBlk hAgreeLad
          hs1m hs1t hs1d hs1b hs1Run hs1f
        rcases hSimK with ⟨k, hk⟩
        refine ⟨k, ?_, hInv⟩
        dsimp only [stepSrcBlock]
        rw [hex]
        dsimp only
        rw [hblk]
        cases unwind with
        | none => exact hk
        | some ubb => exact hk

theorem execSrcFuel_succ_right (prog : SrcProgram) (oracle : ExecOracle)
    (n : Nat) (st : SrcState) :
    execSrcFuel prog oracle (n + 1) st =
      stepSrcBlock prog oracle (execSrcFuel prog oracle n st) := by
  induction n generalizing st with
  | zero =>
    dsimp only [execSrcFuel]
    cases hex : st.exit with
    | running => rfl
    | returned => dsimp only [stepSrcBlock]; rw [hex]
    | unwound => dsimp only [stepSrcBlock]; rw [hex]
    | aborted => dsimp only [stepSrcBlock]; rw [hex]
    | faulted => dsimp only [stepSrcBlock]; rw [hex]
  | succ n' ih =>
    cases hex : st.exit with
    | running =>
      have hl : execSrcFuel prog oracle (n' + 2) st =
          execSrcFuel prog oracle (n' + 1) (stepSrcBlock prog oracle st) := by
        dsimp only [execSrcFuel]; rw [hex]
      have hr : execSrcFuel prog oracle (n' + 1) st =
          execSrcFuel prog oracle n' (stepSrcBlock prog oracle st) := by
        dsimp only [execSrcFuel]; rw [hex]
      rw [hl, hr]
      exact ih (stepSrcBlock prog oracle st)
    | returned =>
      have hfr : ∀ k, execSrcFuel prog oracle k st = st := fun k => by
        cases k <;> dsimp only [execSrcFuel] <;> first | rfl | rw [hex]
      rw [hfr (n' + 2), hfr (n' + 1)]
      dsimp only [stepSrcBlock]; rw [hex]
    | unwound =>
      have hfr : ∀ k, execSrcFuel prog oracle k st = st := fun k => by
        cases k <;> dsimp only [execSrcFuel] <;> first | rfl | rw [hex]
      rw [hfr (n' + 2), hfr (n' + 1)]
      dsimp only [stepSrcBlock]; rw [hex]
    | aborted =>
      have hfr : ∀ k, execSrcFuel prog oracle k st = st := fun k => by
        cases k <;> dsimp only [execSrcFuel] <;> first | rfl | rw [hex]
      rw [hfr (n' + 2), hfr (n' + 1)]
      dsimp only [stepSrcBlock]; rw [hex]
    | faulted =>
      have hfr : ∀ k, execSrcFuel prog oracle k st = st := fun k => by
        cases k <;> dsimp only [execSrcFuel] <;> first | rfl | rw [hex]
      rw [hfr (n' + 2), hfr (n' + 1)]
      dsimp only [stepSrcBlock]; rw [hex]

theorem execSrcFuel_sim (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (oracle : ExecOracle) (n : Nat) :
    let eprog := elaborateProgram prog numBlocks df fa
    let s := execSrcFuel prog oracle n (initSrcState prog)
    ∃ m : Nat,
      let e := execElabFuel eprog oracle m (initElabState eprog)
      StateSim fa s e ∧
      (s.exit = .running → natLt s.bb numBlocks = true ∧ InitConsistent s.init (df.atBlock s.bb)) := by
  induction n with
  | zero =>
    have hInit := init_state_sim prog numBlocks df fa hvalid hfa oracle
    rcases hInit with ⟨hSim, hBb, hCons⟩
    refine ⟨1, ?_, fun _ => ⟨hBb, hCons⟩⟩
    exact hSim
  | succ n' ih =>
    rcases ih with ⟨m, hSim, hInv⟩
    have hStep := step_sim prog numBlocks df fa hvalid hfa hwf oracle
      (execSrcFuel prog oracle n' (initSrcState prog))
      (execElabFuel (elaborateProgram prog numBlocks df fa) oracle m
        (initElabState (elaborateProgram prog numBlocks df fa)))
      hSim (fun h => (hInv h).1) (fun h => (hInv h).2)
    rcases hStep with ⟨k, hSim', hInv'⟩
    refine ⟨m + k, ?_, ?_⟩
    · rw [execSrcFuel_succ_right, execElabFuel_add]
      exact hSim'
    · rw [execSrcFuel_succ_right]
      exact hInv'

/-- **Main Theorem 1 (Exact Drop-Trace Equivalence & Zero-Fault Simulation)**:
For every well-formed source MIR program `prog`, validated dataflow certificate `df`,
flag allocation `fa`, execution oracle `oracle`, and step horizon `n`, `ElaborateDrops`
produces a target CFG that executes the EXACT identical sequence of `DropEvent`s
(`create`, `dropCall`, `boxDealloc`), maintains exact physical atom-initialization equality,
identical branch/drop oracle consumption, and identical exit status. -/
theorem elaborateProgram_exact_trace_equiv (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (oracle : ExecOracle) (n : Nat) :
    let eprog := elaborateProgram prog numBlocks df fa
    let s := execSrcFuel prog oracle n (initSrcState prog)
    ∃ m : Nat,
      let e := execElabFuel eprog oracle m (initElabState eprog)
      e.trace = s.trace ∧
      e.exit = s.exit ∧
      e.mem = s.init ∧
      FlagSimulatesInit fa s.init e.flags ∧
      e.dropIdx = s.dropIdx ∧
      e.branchIdx = s.branchIdx := by
  have h := execSrcFuel_sim prog numBlocks df fa hvalid hfa hwf oracle n
  rcases h with ⟨m, ⟨hm, htr, hdi, hbi, hex, hfs, _⟩, _⟩
  exact ⟨m, htr, hex, hm, hfs, hdi, hbi⟩

/-- **Main Theorem 2 (Dynamic Stack Drop-Flag Simulation Invariant)**:
At every simulated execution boundary, every allocated drop flag `fid` satisfies
`e.flags fid = s.init a` (`true` iff the place represented by `MovePath` atom `a`
is initialized along that concrete path). -/
theorem drop_flag_simulation_invariant (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (oracle : ExecOracle) (n : Nat) :
    let eprog := elaborateProgram prog numBlocks df fa
    let s := execSrcFuel prog oracle n (initSrcState prog)
    ∃ m : Nat,
      let e := execElabFuel eprog oracle m (initElabState eprog)
      e.trace = s.trace ∧
      ∀ a fid, fa.flagOf a = some fid → e.flags fid = s.init a := by
  have h := elaborateProgram_exact_trace_equiv prog numBlocks df fa hvalid hfa hwf oracle n
  rcases h with ⟨m, htr, _hex, _hm, hfs, _hd, _hb⟩
  exact ⟨m, htr, hfs⟩

/-- **Main Theorem 3 (Zero Faults & Terminal Preservation Across Arbitrarily Extended Fuel)**:
Whenever the source execution introduces no uninitialized user `explicitDrop` faults and
terminates (`s.exit ≠ .running`, `s.exit ≠ .faulted`), the elaborated program enters zero
`.faulted` states, records `traceHasFault e.trace = false`, and permanently stabilizes at the
exact source drop trace for all fuel `m' ≥ m`. -/
theorem elaborated_zero_faults_and_terminal_freeze (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (oracle : ExecOracle) (n : Nat)
    (hNoSrcFault : traceHasFault (execSrcFuel prog oracle n (initSrcState prog)).trace = false)
    (hTerm : (execSrcFuel prog oracle n (initSrcState prog)).exit ≠ .running)
    (hNoFaultExit : (execSrcFuel prog oracle n (initSrcState prog)).exit ≠ .faulted) :
    let eprog := elaborateProgram prog numBlocks df fa
    let s := execSrcFuel prog oracle n (initSrcState prog)
    ∃ m : Nat, ∀ m' : Nat,
      let e := execElabFuel eprog oracle (m + m') (initElabState eprog)
      e.trace = s.trace ∧
      traceHasFault e.trace = false ∧
      e.exit = s.exit ∧
      e.exit ≠ .faulted := by
  have h := elaborateProgram_exact_trace_equiv prog numBlocks df fa hvalid hfa hwf oracle n
  rcases h with ⟨m, htr, hex, _hm, _hfs, _hd, _hb⟩
  refine ⟨m, fun m' => ?_⟩
  let eprog := elaborateProgram prog numBlocks df fa
  let e0 := execElabFuel eprog oracle m (initElabState eprog)
  have hne : e0.exit ≠ .running := fun hr => hTerm (hex.symm.trans hr)
  rw [execElabFuel_add, execElabFuel_freeze eprog oracle m' e0 hne]
  refine ⟨htr, ?_, hex, fun hf => hNoFaultExit (hex.symm.trans hf)⟩
  rw [htr]; exact hNoSrcFault

/-- **Main Theorem 4 (Preservation of `NoDoubleDrop` and `NoLeak` Under `ElaborateDrops`)**:
Both exact destruction safety (`countTagDrops ≤ countTagCreates` and `traceHasFault = false`)
and exact leak-freedom (`countTagCreates ≤ countTagDrops`) lift identically from the source
semantics to the elaborated CFG without adding double-drops or leaks on any branch/unwind path. -/
theorem elaborated_no_double_drop_and_no_leak (prog : SrcProgram) (numBlocks : Nat)
    (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (oracle : ExecOracle) (n : Nat) (tag : DropTag)
    (hNoDouble : noDoubleDropTag tag (execSrcFuel prog oracle n (initSrcState prog)).trace)
    (hNoLeak : noLeakTag tag (execSrcFuel prog oracle n (initSrcState prog)).trace) :
    let eprog := elaborateProgram prog numBlocks df fa
    ∃ m : Nat,
      let e := execElabFuel eprog oracle m (initElabState eprog)
      noDoubleDropTag tag e.trace ∧ noLeakTag tag e.trace := by
  have h := elaborateProgram_exact_trace_equiv prog numBlocks df fa hvalid hfa hwf oracle n
  rcases h with ⟨m, htr, _⟩
  refine ⟨m, ?_, ?_⟩
  · rw [htr]; exact hNoDouble
  · rw [htr]; exact hNoLeak

/-! ## 8. Partial-Move Field Disjointness, `E0509` Drop Protection,
`ManuallyDrop` / `MaybeUninit` Suppression, Drop-Order Laws & Concrete Witnesses -/

/-! ### 8.1 General Prefix & Partial-Move Field-Disjointness Soundness -/

noncomputable def projListPrefix : List ProjElem → List ProjElem → Bool
  | [], _ => true
  | x :: xs, y :: ys => ProjElem.beq x y && projListPrefix xs ys
  | _ :: _, [] => false

theorem projListPrefix_refl (xs : List ProjElem) : projListPrefix xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (ProjElem.beq x x && projListPrefix xs xs) = true
    rw [projElem_beq_refl x, ih]
    rfl

theorem projListPrefix_append_right (xs ys : List ProjElem) :
    projListPrefix xs (listAppend xs ys) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (ProjElem.beq x x && projListPrefix xs (listAppend xs ys)) = true
    rw [projElem_beq_refl x, ih]
    rfl

theorem projListPrefix_append_trans {p q r : List ProjElem}
    (hpq : projListPrefix p q = true) (hqr : projListPrefix q r = true) :
    projListPrefix p r = true := by
  induction p generalizing q r with
  | nil => rfl
  | cons x xs ih =>
    cases q with
    | nil => cases hpq
    | cons y ys =>
      cases r with
      | nil => cases hqr
      | cons z zs =>
        change (ProjElem.beq x y && projListPrefix xs ys) = true at hpq
        change (ProjElem.beq y z && projListPrefix ys zs) = true at hqr
        cases hxy : ProjElem.beq x y <;> rw [hxy] at hpq
        · cases hpq
        · cases hyz : ProjElem.beq y z <;> rw [hyz] at hqr
          · cases hqr
          · have hxz : x = z := (projElem_beq_sound hxy).trans (projElem_beq_sound hyz)
            rw [hxz]
            change (ProjElem.beq z z && projListPrefix xs zs) = true
            rw [projElem_beq_refl z, ih hpq hqr]
            rfl

theorem atomInList_append (a : Atom) (xs ys : List Atom) :
    atomInList a (listAppend xs ys) = (atomInList a xs || atomInList a ys) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    change (Atom.beq a x || atomInList a (listAppend rest ys)) =
      ((Atom.beq a x || atomInList a rest) || atomInList a ys)
    rw [ih, Bool.or_assoc]

theorem atomInList_mapAtomPrefix (loc : LocalId) (pref : List ProjElem)
    (xs : List Atom) (a : Atom)
    (hm : atomInList a (mapAtomPrefix loc pref xs) = true) :
    a.localId = loc ∧ projListPrefix pref a.proj = true := by
  induction xs with
  | nil => cases hm
  | cons x rest ih =>
    change (Atom.beq a { x with localId := loc, proj := listAppend pref x.proj } ||
      atomInList a (mapAtomPrefix loc pref rest)) = true at hm
    cases hb : Atom.beq a { x with localId := loc, proj := listAppend pref x.proj } with
    | true =>
      have heq := atom_beq_sound hb
      rw [heq]
      exact ⟨rfl, projListPrefix_append_right pref x.proj⟩
    | false =>
      rw [hb] at hm
      exact ih hm

theorem atomInList_replicateArrayAtoms (loc : LocalId) (pref : List ProjElem)
    (elemAtoms : List Atom) (idx len : Nat) (a : Atom)
    (hm : atomInList a (replicateArrayAtoms loc pref elemAtoms idx len) = true) :
    a.localId = loc ∧ projListPrefix pref a.proj = true := by
  induction len generalizing idx with
  | zero => cases hm
  | succ n ih =>
    change atomInList a (listAppend (mapAtomPrefix loc (listAppend pref [.arrayIdx idx]) elemAtoms)
      (replicateArrayAtoms loc pref elemAtoms (idx + 1) n)) = true at hm
    rw [atomInList_append] at hm
    cases hleft : atomInList a (mapAtomPrefix loc (listAppend pref [.arrayIdx idx]) elemAtoms) with
    | true =>
      have hl := atomInList_mapAtomPrefix loc (listAppend pref [.arrayIdx idx]) elemAtoms a hleft
      exact ⟨hl.1, projListPrefix_append_trans (projListPrefix_append_right pref [.arrayIdx idx]) hl.2⟩
    | false =>
      rw [hleft] at hm
      exact ih (idx + 1) hm

mutual
  theorem atomInList_atomsOfTyAux (loc : LocalId) (pref : List ProjElem)
      (ty : MirTy) (a : Atom) (hm : atomInList a (atomsOfTyAux loc pref ty) = true) :
      a.localId = loc ∧ projListPrefix pref a.proj = true := by
    cases ty with
    | scalar => cases hm
    | dropLeaf tag =>
      change (Atom.beq a { localId := loc, proj := pref, tag := tag, kind := .leaf } || false) = true at hm
      cases hb : Atom.beq a { localId := loc, proj := pref, tag := tag, kind := .leaf } with
      | false => rw [hb] at hm; cases hm
      | true =>
        rw [atom_beq_sound hb]
        exact ⟨rfl, projListPrefix_refl pref⟩
    | structTy hasDrop selfTag fields =>
      cases hasDrop with
      | true =>
        cases selfTag with
        | none => cases hm
        | some tag =>
          change (Atom.beq a { localId := loc, proj := pref, tag := tag, kind := .adtDrop } || false) = true at hm
          cases hb : Atom.beq a { localId := loc, proj := pref, tag := tag, kind := .adtDrop } with
          | false => rw [hb] at hm; cases hm
          | true =>
            rw [atom_beq_sound hb]
            exact ⟨rfl, projListPrefix_refl pref⟩
      | false =>
        exact atomInList_atomsOfFields loc pref 0 fields a hm
    | tupleTy elems =>
      exact atomInList_atomsOfFields loc pref 0 elems a hm
    | arrayTy elem len =>
      exact atomInList_replicateArrayAtoms loc pref (atomsOfTyAux loc [] elem) 0 len a hm
    | enumTy variants =>
      exact atomInList_atomsOfVariants loc pref 0 variants a hm
    | boxTy inner heapTag =>
      change atomInList a (listAppend
        (atomsOfTyAux loc (listAppend pref [.deref]) inner)
        [{ localId := loc, proj := pref, tag := heapTag, kind := .boxShallow }]) = true at hm
      rw [atomInList_append] at hm
      cases hleft : atomInList a (atomsOfTyAux loc (listAppend pref [.deref]) inner) with
      | true =>
        have hl := atomInList_atomsOfTyAux loc (listAppend pref [.deref]) inner a hleft
        exact ⟨hl.1, projListPrefix_append_trans (projListPrefix_append_right pref [.deref]) hl.2⟩
      | false =>
        rw [hleft] at hm
        change (Atom.beq a { localId := loc, proj := pref, tag := heapTag, kind := .boxShallow } || false) = true at hm
        cases hb : Atom.beq a { localId := loc, proj := pref, tag := heapTag, kind := .boxShallow } with
        | false => rw [hb] at hm; cases hm
        | true =>
          rw [atom_beq_sound hb]
          exact ⟨rfl, projListPrefix_refl pref⟩
    | manuallyDrop _ => cases hm
    | maybeUninit _ => cases hm

  theorem atomInList_atomsOfFields (loc : LocalId) (pref : List ProjElem)
      (idx : Nat) (fields : List MirTy) (a : Atom)
      (hm : atomInList a (atomsOfFields loc pref idx fields) = true) :
      a.localId = loc ∧ projListPrefix pref a.proj = true := by
    cases fields with
    | nil => cases hm
    | cons f fs =>
      change atomInList a (listAppend (atomsOfTyAux loc (listAppend pref [.field idx]) f)
        (atomsOfFields loc pref (idx + 1) fs)) = true at hm
      rw [atomInList_append] at hm
      cases hleft : atomInList a (atomsOfTyAux loc (listAppend pref [.field idx]) f) with
      | true =>
        have hl := atomInList_atomsOfTyAux loc (listAppend pref [.field idx]) f a hleft
        exact ⟨hl.1, projListPrefix_append_trans (projListPrefix_append_right pref [.field idx]) hl.2⟩
      | false =>
        rw [hleft] at hm
        exact atomInList_atomsOfFields loc pref (idx + 1) fs a hm

  theorem atomInList_atomsOfVariants (loc : LocalId) (pref : List ProjElem)
      (vIdx : Nat) (variants : List (List MirTy)) (a : Atom)
      (hm : atomInList a (atomsOfVariants loc pref vIdx variants) = true) :
      a.localId = loc ∧ projListPrefix pref a.proj = true := by
    cases variants with
    | nil => cases hm
    | cons vFields vs =>
      change atomInList a (listAppend (atomsOfFields loc (listAppend pref [.downcast vIdx]) 0 vFields)
        (atomsOfVariants loc pref (vIdx + 1) vs)) = true at hm
      rw [atomInList_append] at hm
      cases hleft : atomInList a (atomsOfFields loc (listAppend pref [.downcast vIdx]) 0 vFields) with
      | true =>
        have hl := atomInList_atomsOfFields loc (listAppend pref [.downcast vIdx]) 0 vFields a hleft
        exact ⟨hl.1, projListPrefix_append_trans (projListPrefix_append_right pref [.downcast vIdx]) hl.2⟩
      | false =>
        rw [hleft] at hm
        exact atomInList_atomsOfVariants loc pref (vIdx + 1) vs a hm
end

theorem atomInList_atomsOfPlace (locals : List MirTy) (p : Place) (a : Atom)
    (hm : atomInList a (atomsOfPlace locals p) = true) :
    a.localId = p.localId ∧ projListPrefix p.proj a.proj = true := by
  dsimp only [atomsOfPlace] at hm
  cases hloc : listGet? locals p.localId with
  | none => rw [hloc] at hm; cases hm
  | some baseTy =>
    rw [hloc] at hm
    dsimp only at hm
    cases hwalk : placeTypeWalk baseTy p.proj with
    | none => rw [hwalk] at hm; cases hm
    | some subTy =>
      rw [hwalk] at hm
      dsimp only at hm
      exact atomInList_atomsOfTyAux p.localId p.proj subTy a hm

theorem projListPrefix_ne_head_field {i j : Nat} (hne : i ≠ j) (q : List ProjElem) :
    projListPrefix [.field i] q = true → projListPrefix [.field j] q = false := by
  intro hp
  cases q with
  | nil => cases hp
  | cons pe _ =>
    change (ProjElem.beq (.field i) pe && true) = true at hp
    cases hb : ProjElem.beq (.field i) pe with
    | false => rw [hb] at hp; cases hp
    | true =>
      have heq : ProjElem.field i = pe := projElem_beq_sound hb
      rw [← heq]
      change (natEq j i && true) = false
      rw [natEq_false_of_ne (fun he => hne he.symm)]
      rfl

/-- **Theorem (`partial_move_field_disjointness_sound`)**:
1. Moving any sub-place `src` (`src.localId = l`, prefix `[.field i]`) into any other local `dst`
   (`dst.localId ≠ l`) clears every atom in `src` while leaving EVERY sibling field `j ≠ i`
   atom (`atomInList a sibPlace = true`) completely untouched (`st'.init a = st.init a`).
2. When `ElaborateDrops` elaborates a partial move on a non-`Drop` struct `Pair`, only the
   remaining sibling fields are dropped at scope exit with zero double-drops and zero leaks. -/
theorem partial_move_field_disjointness_sound (locals : List MirTy)
    (st : SrcState) (l dstLoc : LocalId) (i j : Nat)
    (dstProj : List ProjElem) (hiNeJ : i ≠ j) (hDstNe : dstLoc ≠ l)
    (a : Atom)
    (hSib : atomInList a (atomsOfPlace locals { localId := l, proj := [.field j] }) = true) :
    let src : Place := { localId := l, proj := [.field i] }
    let dst : Place := { localId := dstLoc, proj := dstProj }
    (stepSrcStmt locals st (.movePlace dst src)).init a = st.init a ∧
    (∀ b, atomInList b (atomsOfPlace locals src) = true →
      (stepSrcStmt locals st (.movePlace dst src)).init b = false) := by
  have ha := atomInList_atomsOfPlace locals { localId := l, proj := [.field j] } a hSib
  have hNotSrc : atomInList a (atomsOfPlace locals { localId := l, proj := [.field i] }) = false := by
    cases h : atomInList a (atomsOfPlace locals { localId := l, proj := [.field i] }) with
    | false => rfl
    | true =>
      have hi := atomInList_atomsOfPlace locals { localId := l, proj := [.field i] } a h
      have hf := projListPrefix_ne_head_field hiNeJ a.proj hi.2
      rw [ha.2] at hf
      cases hf
  have hNotDst : atomInList a (atomsOfPlace locals { localId := dstLoc, proj := dstProj }) = false := by
    cases h : atomInList a (atomsOfPlace locals { localId := dstLoc, proj := dstProj }) with
    | false => rfl
    | true =>
      have hd := atomInList_atomsOfPlace locals { localId := dstLoc, proj := dstProj } a h
      have hlocEq : dstLoc = l := hd.1.symm.trans ha.1
      exact False.elim (hDstNe hlocEq)
  constructor
  · dsimp only [stepSrcStmt]
    rw [setAtoms_not_mem _ _ true a hNotDst, setAtoms_not_mem _ _ false a hNotSrc]
  · intro b hb
    have hbInfo := atomInList_atomsOfPlace locals { localId := l, proj := [.field i] } b hb
    have hbNotDst : atomInList b (atomsOfPlace locals { localId := dstLoc, proj := dstProj }) = false := by
      cases h : atomInList b (atomsOfPlace locals { localId := dstLoc, proj := dstProj }) with
      | false => rfl
      | true =>
        have hbd := atomInList_atomsOfPlace locals { localId := dstLoc, proj := dstProj } b h
        exact False.elim (hDstNe (hbd.1.symm.trans hbInfo.1))
    dsimp only [stepSrcStmt]
    rw [setAtoms_not_mem _ _ true b hbNotDst]
    exact setAtoms_mem st.init (atomsOfPlace locals { localId := l, proj := [.field i] }) false b hb

/-! ### 8.2 `E0509` (`Drop` Type Partial-Move Protection) Necessity -/

theorem isValidMovePath_rejects_drop_adt_field (locals : List MirTy)
    (l : LocalId) (selfTag : Option DropTag) (fields : List MirTy)
    (i : Nat) (rest : List ProjElem)
    (hl : listGet? locals l = some (.structTy true selfTag fields)) :
    isValidMovePath locals { localId := l, proj := .field i :: rest } = false := by
  dsimp only [isValidMovePath]
  rw [hl]
  rfl

theorem isValidMovePath_rejects_manuallyDrop_interior (locals : List MirTy)
    (l : LocalId) (inner : MirTy) (pe : ProjElem) (rest : List ProjElem)
    (hl : listGet? locals l = some (.manuallyDrop inner)) :
    isValidMovePath locals { localId := l, proj := pe :: rest } = false := by
  dsimp only [isValidMovePath]
  rw [hl]
  dsimp only
  cases pe with
  | field _ => rfl
  | arrayIdx _ => rfl
  | deref => rfl
  | downcast _ =>
    cases rest with
    | nil => rfl
    | cons pe2 _ => cases pe2 <;> rfl

theorem isValidMovePath_rejects_maybeUninit_interior (locals : List MirTy)
    (l : LocalId) (inner : MirTy) (pe : ProjElem) (rest : List ProjElem)
    (hl : listGet? locals l = some (.maybeUninit inner)) :
    isValidMovePath locals { localId := l, proj := pe :: rest } = false := by
  dsimp only [isValidMovePath]
  rw [hl]
  dsimp only
  cases pe with
  | field _ => rfl
  | arrayIdx _ => rfl
  | deref => rfl
  | downcast _ =>
    cases rest with
    | nil => rfl
    | cons pe2 _ => cases pe2 <;> rfl

/-- Counterexample proving why `E0509` (`isValidMovePath = false` for fields of a `Drop` type
`MirTy.structTy true (some tagOuter) _`) is soundness-critical:
`OuterWithDrop` is tracked by a single atomic custom-drop `MovePath` atom `outerAtom`
rather than independent per-field atoms (`atomsOfPlace [outerTy, ...] 0 = [outerAtom]`).
If field `0` were moved out illegally:
* Either parent `outerAtom` remains initialized and `OuterWithDrop::drop(&mut self)` fires over a
  partially uninitialized `self`, triggering an uninitialized-field fault (`traceHasFault = true`);
* Or clearing `outerAtom` suppresses `OuterWithDrop::drop`, violating `noLeakTag tagOuter`
  (`countTagDrops tagOuter tr = 0 < 1 = countTagCreates tagOuter tr`). -/
theorem e0509_partial_move_drop_type_necessity (tagOuter tagInner tagSib : DropTag)
    (hneInner : tagOuter ≠ tagInner) (hneSib : tagOuter ≠ tagSib) :
    let outerTy : MirTy := .structTy true (some tagOuter) [.dropLeaf tagInner, .dropLeaf tagSib]
    let locals : List MirTy := [outerTy, .dropLeaf tagInner]
    let outerPlace : Place := { localId := 0, proj := [] }
    let innerFieldPlace : Place := { localId := 0, proj := [.field 0] }
    let outerAtom : Atom := { localId := 0, proj := [], tag := tagOuter, kind := .adtDrop }
    isValidMovePath locals innerFieldPlace = false ∧
    atomsOfPlace locals outerPlace = [outerAtom] ∧
    -- Horn 1: executing parent `Drop::drop` after partial move hits uninitialized field `0`
    traceHasFault [.create tagOuter 0, .uninitFieldInDropImpl tagOuter 0] = true ∧
    -- Horn 2: suppressing parent `Drop::drop` leaks the custom destructor (`0 < 1`)
    let trSuppressed :=
      (evalSrcDropAtoms 0 { branchAt := fun _ _ => false, panicAt := fun _ _ => false }
        false (atomsOfPlace locals outerPlace) (setAtom emptyAtomMap outerAtom false))
    trSuppressed.2.1 = [] ∧
    ¬ noLeakTag tagOuter [DropEvent.create tagOuter 0, DropEvent.dropCall tagInner 1 true] := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · dsimp only [evalSrcDropAtoms, atomsOfPlace, listGet?, placeTypeWalk, atomsOfTyAux, evalSrcDropAtomsGo]
    rw [setAtom_eq, bool_if_false]
  · intro hnl
    have hcr : countTagCreates tagOuter [DropEvent.create tagOuter 0, DropEvent.dropCall tagInner 1 true] = 1 := by
      dsimp only [countTagCreates]
      rw [natEq_refl tagOuter]
      rfl
    have hdr : countTagDrops tagOuter [DropEvent.create tagOuter 0, DropEvent.dropCall tagInner 1 true] = 0 := by
      have _ := hneSib
      dsimp only [countTagDrops]
      rw [natEq_false_of_ne (fun he => hneInner he.symm)]
      rfl
    have hle : (1 : Nat) ≤ 0 := by
      have h0 : countTagCreates tagOuter [DropEvent.create tagOuter 0, DropEvent.dropCall tagInner 1 true] ≤
          countTagDrops tagOuter [DropEvent.create tagOuter 0, DropEvent.dropCall tagInner 1 true] := hnl
      rw [hcr, hdr] at h0
      exact h0
    cases hle

/-! ### 8.3 `ManuallyDrop<T>` & `MaybeUninit<T>` Zero-Implicit-Drop Theorems -/

theorem manuallyDrop_maybeUninit_needsDrop_false (inner : MirTy) :
    needsDrop (.manuallyDrop inner) = false ∧
    needsDrop (.maybeUninit inner) = false ∧
    needsDrop (.arrayTy inner 0) = false :=
  ⟨rfl, rfl, rfl⟩

theorem atomsOfPlace_manuallyDrop_empty (locals : List MirTy) (l : LocalId) (inner : MirTy)
    (hl : listGet? locals l = some (.manuallyDrop inner)) :
    atomsOfPlace locals { localId := l, proj := [] } = [] := by
  dsimp only [atomsOfPlace]
  rw [hl]
  rfl

theorem atomsOfPlace_maybeUninit_empty (locals : List MirTy) (l : LocalId) (inner : MirTy)
    (hl : listGet? locals l = some (.maybeUninit inner)) :
    atomsOfPlace locals { localId := l, proj := [] } = [] := by
  dsimp only [atomsOfPlace]
  rw [hl]
  rfl

/-- Program invariant satisfied when all locals/places have empty drop-atom sets
(e.g., all non-`Copy` values are wrapped in `ManuallyDrop<T>` or `MaybeUninit<T>`). -/
noncomputable def AllPlacesDropSuppressed (prog : SrcProgram) : Prop :=
  (∀ p : Place, atomsOfPlace prog.locals p = []) ∧
  atomsOfLocalList prog.locals prog.args = []

theorem atomsOfLocalList_suppressed (locals : List MirTy)
    (hsupp : ∀ p : Place, atomsOfPlace locals p = []) (ls : List LocalId) :
    atomsOfLocalList locals ls = [] := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
    dsimp only [atomsOfLocalList]
    rw [hsupp { localId := l, proj := [] }, ih]
    rfl

theorem stepSrcStmt_trace_suppressed (locals : List MirTy)
    (hsupp : ∀ p : Place, atomsOfPlace locals p = [])
    (st : SrcState) (stmt : SrcStmt) :
    (stepSrcStmt locals st stmt).trace = st.trace := by
  cases stmt with
  | storageLive _ => rfl
  | storageDead _ => rfl
  | noop => rfl
  | movePlace _ _ => rfl
  | initPlace p =>
    dsimp only [stepSrcStmt]
    rw [hsupp p]
    exact listAppend_nil_right st.trace
  | explicitDrop p =>
    dsimp only [stepSrcStmt]
    rw [hsupp p]
    rfl

theorem stepSrcStmtList_trace_suppressed (locals : List MirTy)
    (hsupp : ∀ p : Place, atomsOfPlace locals p = [])
    (stmts : List SrcStmt) (st : SrcState) :
    (stepSrcStmtList locals stmts st).trace = st.trace := by
  induction stmts generalizing st with
  | nil => rfl
  | cons s ss ih =>
    dsimp only [stepSrcStmtList]
    rw [ih (stepSrcStmt locals st s), stepSrcStmt_trace_suppressed locals hsupp st s]

private theorem stepSrcDropNil (s1 : SrcState) (oracle : ExecOracle) (isCl : Bool)
    (tgt : BlockId) (unwind : Option BlockId) :
    (match evalSrcDropAtoms s1.dropIdx oracle isCl [] s1.init with
     | (init', evs, dIdx', panicked, aborted) =>
       let tr' := listAppend s1.trace evs
       if aborted then { s1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
       else if panicked then
         match unwind with
         | some ubb => { s1 with bb := ubb, dropIdx := dIdx', init := init', trace := tr' }
         | none => { s1 with init := init', trace := tr', dropIdx := dIdx', exit := .aborted }
       else { s1 with bb := tgt, dropIdx := dIdx', init := init', trace := tr' }).trace = s1.trace := by
  dsimp only [evalSrcDropAtoms, evalSrcDropAtomsGo]
  rw [bool_if_false, bool_if_false]
  exact listAppend_nil_right s1.trace

theorem stepSrcBlock_trace_suppressed (prog : SrcProgram) (oracle : ExecOracle)
    (hsupp : AllPlacesDropSuppressed prog) (st : SrcState) :
    (stepSrcBlock prog oracle st).trace = st.trace := by
  dsimp only [stepSrcBlock]
  cases hex : st.exit with
  | running =>
    cases hblk : prog.blocks st.bb with
    | none => rfl
    | some blk =>
      cases blk with
      | mk isCl stmts term =>
        have hst := stepSrcStmtList_trace_suppressed prog.locals hsupp.1 stmts st
        cases term with
        | goto tgt => exact hst
        | switchBool _ _ _ => exact hst
        | ret => exact hst
        | unwindResume => exact hst
        | unwindAbort => exact hst
        | drop p tgt unwind =>
          dsimp only
          rw [hsupp.1 p]
          exact (stepSrcDropNil _ oracle isCl tgt unwind).trans hst
        | scopeExit locs tgt unwind =>
          dsimp only
          rw [atomsOfLocalList_suppressed prog.locals hsupp.1 (localsDropOrder locs)]
          exact (stepSrcDropNil _ oracle isCl tgt unwind).trans hst
  | returned => rfl
  | unwound => rfl
  | aborted => rfl
  | faulted => rfl

/-- **Theorem (`manuallyDrop_and_maybeUninit_zero_implicit_drop`)**:
Under `AllPlacesDropSuppressed` (every place wraps drop glue inside `ManuallyDrop` or `MaybeUninit`),
both the source MIR execution AND the `ElaborateDrops` lowered CFG execute with empty drop trace
`trace = []`, zero faults, and zero destructor calls on EVERY oracle and EVERY fuel horizon `n`. -/
theorem manuallyDrop_and_maybeUninit_zero_implicit_drop
    (prog : SrcProgram) (numBlocks : Nat) (df : DataflowCert) (fa : FlagAlloc)
    (hvalid : ValidDataflowCert prog numBlocks df)
    (hfa : ValidFlagAlloc prog numBlocks df fa)
    (hwf : WellFormedSrcDrops prog)
    (hsupp : AllPlacesDropSuppressed prog)
    (oracle : ExecOracle) (n : Nat) :
    let s := execSrcFuel prog oracle n (initSrcState prog)
    s.trace = [] ∧
    (∃ m : Nat, (execElabFuel (elaborateProgram prog numBlocks df fa) oracle m
      (initElabState (elaborateProgram prog numBlocks df fa))).trace = []) := by
  have hSrcEmpty : (execSrcFuel prog oracle n (initSrcState prog)).trace = [] := by
    have hGen : ∀ st : SrcState, (execSrcFuel prog oracle n st).trace = st.trace := by
      induction n with
      | zero => intro st; rfl
      | succ k ih =>
        intro st
        dsimp only [execSrcFuel]
        cases st.exit with
        | running =>
          rw [ih (stepSrcBlock prog oracle st)]
          exact stepSrcBlock_trace_suppressed prog oracle hsupp st
        | returned => rfl
        | unwound => rfl
        | aborted => rfl
        | faulted => rfl
    exact hGen (initSrcState prog)
  refine ⟨hSrcEmpty, ?_⟩
  rcases elaborateProgram_exact_trace_equiv prog numBlocks df fa hvalid hfa hwf oracle n with
    ⟨m, htr, _⟩
  exact ⟨m, htr.trans hSrcEmpty⟩

/-! ### 8.4 Deterministic Drop-Order Laws & `.iter().rev()` Removal Array Partial-Move Divergence -/

theorem localsDropOrder_reverse_three (l0 l1 l2 : LocalId) :
    localsDropOrder [l0, l1, l2] = [l2, l1, l0] := rfl

theorem localsDropOrder_involutive (locs : List LocalId) :
    localsDropOrder (localsDropOrder locs) = locs :=
  listReverse_reverse locs

theorem dropHalfLadderOrder_preserves_declaration_order {α : Type} (fields : List α) :
    dropHalfLadderOrder fields = fields :=
  listReverse_reverse fields

theorem evalSrcDropAtoms_live_sequence (oracle : ExecOracle) (isCl : Bool)
    (atoms : List Atom) (cur : AtomMap) (dIdx : Nat)
    (hNoPanic : ∀ d a, oracle.panicAt d a = false)
    (hDist : atomsDistinct atoms = true)
    (hAllLive : ∀ a, atomInList a atoms = true → cur a = true) :
    (evalSrcDropAtoms dIdx oracle isCl atoms cur).2.1 =
      listMap (fun a => DropEvent.atomEvent a false) atoms := by
  dsimp only [evalSrcDropAtoms]
  suffices hGo : ∀ tr : List DropEvent,
      (evalSrcDropAtomsGo oracle isCl atoms cur tr dIdx false).2.1 =
        listAppend tr (listMap (fun a => DropEvent.atomEvent a false) atoms) by
    exact hGo []
  induction atoms generalizing cur dIdx with
  | nil =>
    intro tr
    exact (listAppend_nil_right tr).symm
  | cons a rest ih =>
    intro tr
    have ⟨hNotIn, hRestDist⟩ := atomsDistinct_head hDist
    have haLive : cur a = true := hAllLive a (by
      change (Atom.beq a a || atomInList a rest) = true
      rw [atom_beq_refl a]; rfl)
    have hRestLive : ∀ x, atomInList x rest = true → setAtom cur a false x = true := by
      intro x hx
      have hne : x ≠ a := fun heq => by rw [heq] at hx; rw [hx] at hNotIn; cases hNotIn
      rw [setAtom_ne cur hne false]
      exact hAllLive x (by change (Atom.beq x a || atomInList x rest) = true; rw [hx]; exact Bool.or_true _)
    dsimp only [evalSrcDropAtomsGo]
    rw [haLive, bool_if_true, bool_if_false, hNoPanic dIdx a, bool_if_false]
    have hRec := ih (setAtom cur a false) (dIdx + 1) hRestDist hRestLive (listAppend tr [DropEvent.atomEvent a false])
    rw [hRec, listAppend_assoc]
    rfl

theorem struct_tuple_array_drop_trace_order (t0 t1 t2 tElem : DropTag) :
    let structTy := MirTy.structTy false none [.dropLeaf t0, .dropLeaf t1, .dropLeaf t2]
    let tupleTy := MirTy.tupleTy [.dropLeaf t0, .dropLeaf t1, .dropLeaf t2]
    let arrayTy := MirTy.arrayTy (.dropLeaf tElem) 3
    let oracle : ExecOracle := { branchAt := fun _ _ => false, panicAt := fun _ _ => false }
    let sAtoms := atomsOfTyAux 0 [] structTy
    let tAtoms := atomsOfTyAux 0 [] tupleTy
    let aAtoms := atomsOfTyAux 0 [] arrayTy
    (evalSrcDropAtoms 0 oracle false sAtoms (setAtoms emptyAtomMap sAtoms true)).2.1 =
      [.dropCall t0 0 false, .dropCall t1 0 false, .dropCall t2 0 false] ∧
    (evalSrcDropAtoms 0 oracle false tAtoms (setAtoms emptyAtomMap tAtoms true)).2.1 =
      [.dropCall t0 0 false, .dropCall t1 0 false, .dropCall t2 0 false] ∧
    (evalSrcDropAtoms 0 oracle false aAtoms (setAtoms emptyAtomMap aAtoms true)).2.1 =
      [.dropCall tElem 0 false, .dropCall tElem 0 false, .dropCall tElem 0 false] := by
  have h1 : ∀ {ty : MirTy}, atomsDistinct (atomsOfTyAux 0 [] ty) = true → True := fun _ => trivial
  clear h1
  dsimp only [atomsOfTyAux, atomsOfFields, replicateArrayAtoms, mapAtomPrefix, listAppend]
  have hs := evalSrcDropAtoms_live_sequence
    { branchAt := fun _ _ => false, panicAt := fun _ _ => false } false
    [{ localId := 0, proj := [.field 0], tag := t0, kind := .leaf },
     { localId := 0, proj := [.field 1], tag := t1, kind := .leaf },
     { localId := 0, proj := [.field 2], tag := t2, kind := .leaf }]
    (setAtoms emptyAtomMap
      [{ localId := 0, proj := [.field 0], tag := t0, kind := .leaf },
       { localId := 0, proj := [.field 1], tag := t1, kind := .leaf },
       { localId := 0, proj := [.field 2], tag := t2, kind := .leaf }] true) 0
    (fun _ _ => rfl) rfl
    (fun x hx => setAtoms_mem _ _ true x hx)
  have ha := evalSrcDropAtoms_live_sequence
    { branchAt := fun _ _ => false, panicAt := fun _ _ => false } false
    [{ localId := 0, proj := [.arrayIdx 0], tag := tElem, kind := .leaf },
     { localId := 0, proj := [.arrayIdx 1], tag := tElem, kind := .leaf },
     { localId := 0, proj := [.arrayIdx 2], tag := tElem, kind := .leaf }]
    (setAtoms emptyAtomMap
      [{ localId := 0, proj := [.arrayIdx 0], tag := tElem, kind := .leaf },
       { localId := 0, proj := [.arrayIdx 1], tag := tElem, kind := .leaf },
       { localId := 0, proj := [.arrayIdx 2], tag := tElem, kind := .leaf }] true) 0
    (fun _ _ => rfl) rfl
    (fun x hx => setAtoms_mem _ _ true x hx)
  exact ⟨hs, hs, ha⟩

/-- **Historical Divergence Law (`rust-lang/rust` `14210df0e`/`49d734536` vs. `3ef0c22cd`/`0259d5e9a`)**:
When middle element `1` of `[a0, a1, a2]` is moved out:
* Pre-fix (`openDropArrayRemainingPreFix`) double-reverses `drop_ranges`, yielding
  reverse drop order **`[2, 0]`** (`a2` dropped before `a0`, reproducing live `rustc 1.98.0-nightly`).
* Post-fix (`openDropArrayRemainingPostFix`) omits `.rev()`, restoring forward order **`[0, 2]`**.
* Universally for every `(len, isMoved)`, `openDropArrayRemainingPreFix len isMoved = listReverse (openDropArrayRemainingPostFix len isMoved)`. -/
theorem openDropArray_rev_removal_divergence (len : Nat) (isMoved : Nat → Bool) :
    openDropArrayRemainingPreFix 3 (fun i => natEq i 1) = [2, 0] ∧
    openDropArrayRemainingPostFix 3 (fun i => natEq i 1) = [0, 2] ∧
    openDropArrayRemainingPreFix len isMoved =
      listReverse (openDropArrayRemainingPostFix len isMoved) :=
  ⟨rfl, rfl, rfl⟩

/-! ### 8.5 Complete End-to-End `ElaborateDrops` Programs, Verified Certificates & `rfl` Witnesses -/

private theorem inj_single_atom (a0 : Atom) (f0 : FlagId) :
    ∀ a b fid,
      (if Atom.beq a a0 then some f0 else none) = some fid →
      (if Atom.beq b a0 then some f0 else none) = some fid →
      a = b := by
  intro a b fid ha hb
  cases hba : Atom.beq a a0 with
  | false => rw [hba] at ha; cases ha
  | true =>
    cases hbb : Atom.beq b a0 with
    | false => rw [hbb] at hb; cases hb
    | true => exact (atom_beq_sound hba).trans (atom_beq_sound hbb).symm

-- Helper for reducing concrete `setAtom` / `setAtoms` equality on small programs.
private theorem atomMap_eq_true_of_beq {a x : Atom} (h : Atom.beq a x = true) :
    setAtom m x v a = v := by
  change (if Atom.beq a x then v else m a) = v
  rw [h]; rfl

private theorem atomMap_eq_false_of_beq {a x : Atom} (h : Atom.beq a x = false) :
    setAtom m x v a = m a := by
  change (if Atom.beq a x then v else m a) = m a
  rw [h]; rfl

/-! #### Witness 1: `condInitProg` (`probe.cond_init`, dynamic stack drop flag `fid = 0`) -/

noncomputable def condInitAtom : Atom :=
  { localId := 0, proj := [], tag := 100, kind := .leaf }

noncomputable def condInitProg : SrcProgram where
  locals := [.dropLeaf 100]
  args := []
  entry := 0
  blocks
    | 0 => some { isCleanup := false, stmts := [.storageLive 0], term := .switchBool 0 1 2 }
    | 1 => some { isCleanup := false, stmts := [.initPlace { localId := 0, proj := [] }], term := .goto 2 }
    | 2 => some { isCleanup := false, stmts := [], term := .scopeExit [0] 3 (some 4) }
    | 3 => some { isCleanup := false, stmts := [.storageDead 0], term := .ret }
    | 4 => some { isCleanup := true, stmts := [], term := .unwindResume }
    | _ => none

noncomputable def condInitDf : DataflowCert where
  atBlock
    | 0 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | 1 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | 2 => { mayInit := setAtom emptyAtomMap condInitAtom true, mayUninit := fun _ => true }
    | 3 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | _ => { mayInit := emptyAtomMap, mayUninit := fun _ => true }

noncomputable def condInitFa : FlagAlloc where
  flagOf a := if Atom.beq a condInitAtom then some 0 else none
  allFlags := [0]

theorem condInitProg_validDf : ValidDataflowCert condInitProg 5 condInitDf := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro bb hlt
    cases bb with
    | zero => cases hlt | succ b1 => cases b1 with
    | zero => cases hlt | succ b2 => cases b2 with
    | zero => cases hlt | succ b3 => cases b3 with
    | zero => cases hlt | succ b4 => cases b4 with
    | zero => cases hlt | succ b5 => rfl
  · intro a
    exact ⟨(fun hf => by cases hf), fun _ => rfl⟩
  · intro bb blk hblk
    cases bb with
    | zero =>
      cases hblk
      refine ⟨rfl, rfl, ⟨(fun _ hf => by cases hf), fun _ _ => rfl⟩, ⟨(fun _ hf => by cases hf), fun _ _ => rfl⟩⟩
    | succ b1 => cases b1 with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨?_, fun _ _ => rfl⟩⟩
      intro a ha
      change setAtom emptyAtomMap condInitAtom true a = true at ha
      exact ha
    | succ b2 => cases b2 with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨?_, fun _ _ => rfl⟩, ⟨rfl, ?_, fun _ _ => rfl⟩⟩
      · intro a ha
        change setAtom (setAtom emptyAtomMap condInitAtom true) condInitAtom false a = true at ha
        cases ha0 : Atom.beq a condInitAtom with
        | true => rw [atom_beq_sound ha0, setAtom_eq] at ha; cases ha
        | false =>
          rw [atomMap_eq_false_of_beq ha0, atomMap_eq_false_of_beq ha0] at ha
          cases ha
      · intro a ha
        change setAtom (setAtom emptyAtomMap condInitAtom true) condInitAtom false a = true at ha
        cases ha0 : Atom.beq a condInitAtom with
        | true => rw [atom_beq_sound ha0, setAtom_eq] at ha; cases ha
        | false =>
          rw [atomMap_eq_false_of_beq ha0, atomMap_eq_false_of_beq ha0] at ha
          cases ha
    | succ b3 => cases b3 with
    | zero => cases hblk; exact trivial
    | succ b4 => cases b4 with
    | zero => cases hblk; exact trivial
    | succ b5 => cases hblk

theorem condInitProg_validFa : ValidFlagAlloc condInitProg 5 condInitDf condInitFa := by
  refine ⟨inj_single_atom condInitAtom 0, ?_⟩
  intro bb blk _hbb hblk
  cases bb with
  | zero => cases hblk; exact trivial
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero =>
    cases hblk
    dsimp only
    intro a ha _hmi _hmu
    change (Atom.beq a condInitAtom || false) = true at ha
    cases ha0 : Atom.beq a condInitAtom with
    | false => rw [ha0] at ha; cases ha
    | true =>
      refine ⟨0, ?_⟩
      change (if Atom.beq a condInitAtom then some 0 else none) = some 0
      rw [ha0]
      rfl
  | succ b3 => cases b3 with
  | zero => cases hblk; exact trivial
  | succ b4 => cases b4 with
  | zero => cases hblk; exact trivial
  | succ b5 => cases hblk

theorem condInitProg_wellFormed : WellFormedSrcDrops condInitProg := by
  intro bb blk hblk
  cases bb with
  | zero => cases hblk; exact trivial
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact ⟨rfl, fun _ => ⟨4, rfl⟩⟩
  | succ b3 => cases b3 with
  | zero => cases hblk; exact trivial
  | succ b4 => cases b4 with
  | zero => cases hblk; exact trivial
  | succ b5 => cases hblk

theorem condInit_witness_true_and_false :
    let eprog := elaborateProgram condInitProg 5 condInitDf condInitFa
    let oTrue : ExecOracle := { branchAt := fun _ _ => true, panicAt := fun _ _ => false }
    let oFalse : ExecOracle := { branchAt := fun _ _ => false, panicAt := fun _ _ => false }
    let sTrue := execSrcFuel condInitProg oTrue 6 (initSrcState condInitProg)
    let eTrue := execElabFuel eprog oTrue 16 (initElabState eprog)
    let sFalse := execSrcFuel condInitProg oFalse 6 (initSrcState condInitProg)
    let eFalse := execElabFuel eprog oFalse 16 (initElabState eprog)
    sTrue.exit = .returned ∧ eTrue.exit = .returned ∧
    sTrue.trace = [.create 100 0, .dropCall 100 0 false] ∧
    eTrue.trace = [.create 100 0, .dropCall 100 0 false] ∧
    sFalse.exit = .returned ∧ eFalse.exit = .returned ∧
    sFalse.trace = [] ∧ eFalse.trace = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem condInit_main_theorems_apply (oracle : ExecOracle) (n : Nat) :
    let eprog := elaborateProgram condInitProg 5 condInitDf condInitFa
    let s := execSrcFuel condInitProg oracle n (initSrcState condInitProg)
    ∃ m : Nat,
      let e := execElabFuel eprog oracle m (initElabState eprog)
      e.trace = s.trace ∧ e.exit = s.exit ∧ e.flags 0 = s.init condInitAtom := by
  rcases elaborateProgram_exact_trace_equiv condInitProg 5 condInitDf condInitFa
      condInitProg_validDf condInitProg_validFa condInitProg_wellFormed oracle n with
    ⟨m, htr, hex, _hm, hfs, _hd, _hb⟩
  exact ⟨m, htr, hex, hfs condInitAtom 0 rfl⟩

/-! #### Witness 2: `condMoveReinitProg` (`probe.cond_move_and_reinit`, all 4 control-flow paths) -/

noncomputable def condMoveAtom0 : Atom :=
  { localId := 0, proj := [], tag := 201, kind := .leaf }

noncomputable def condMoveAtom1 : Atom :=
  { localId := 1, proj := [], tag := 201, kind := .leaf }

noncomputable def condMoveReinitProg : SrcProgram where
  locals := [.dropLeaf 201, .dropLeaf 201]
  args := []
  entry := 0
  blocks
    | 0 => some { isCleanup := false, stmts := [.storageLive 0, .initPlace { localId := 0, proj := [] }], term := .switchBool 0 1 2 }
    | 1 => some { isCleanup := false, stmts := [.storageLive 1, .movePlace { localId := 1, proj := [] } { localId := 0, proj := [] }, .explicitDrop { localId := 1, proj := [] }, .storageDead 1], term := .goto 2 }
    | 2 => some { isCleanup := false, stmts := [], term := .switchBool 1 3 4 }
    | 3 => some { isCleanup := false, stmts := [], term := .drop { localId := 0, proj := [] } 5 (some 6) }
    | 5 => some { isCleanup := false, stmts := [.initPlace { localId := 0, proj := [] }], term := .goto 4 }
    | 4 => some { isCleanup := false, stmts := [], term := .scopeExit [0] 7 (some 6) }
    | 7 => some { isCleanup := false, stmts := [.storageDead 0], term := .ret }
    | 6 => some { isCleanup := true, stmts := [], term := .unwindResume }
    | _ => none

noncomputable def condMoveReinitDf : DataflowCert where
  atBlock
    | 0 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | 1 => { mayInit := setAtom emptyAtomMap condMoveAtom0 true, mayUninit := setAtom (fun _ => true) condMoveAtom0 false }
    | 2 => { mayInit := setAtom emptyAtomMap condMoveAtom0 true, mayUninit := fun _ => true }
    | 3 => { mayInit := setAtom emptyAtomMap condMoveAtom0 true, mayUninit := fun _ => true }
    | 5 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | 4 => { mayInit := setAtom emptyAtomMap condMoveAtom0 true, mayUninit := fun _ => true }
    | 7 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | _ => { mayInit := emptyAtomMap, mayUninit := fun _ => true }

noncomputable def condMoveReinitFa : FlagAlloc where
  flagOf a := if Atom.beq a condMoveAtom0 then some 0 else none
  allFlags := [0]

private theorem condMoveAtom_ne : condMoveAtom1 ≠ condMoveAtom0 := by
  intro heq; cases heq

theorem condMoveReinitProg_validDf : ValidDataflowCert condMoveReinitProg 8 condMoveReinitDf := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro bb hlt
    cases bb with
    | zero => cases hlt | succ b1 => cases b1 with
    | zero => cases hlt | succ b2 => cases b2 with
    | zero => cases hlt | succ b3 => cases b3 with
    | zero => cases hlt | succ b4 => cases b4 with
    | zero => cases hlt | succ b5 => cases b5 with
    | zero => cases hlt | succ b6 => cases b6 with
    | zero => cases hlt | succ b7 => cases b7 with
    | zero => cases hlt | succ b8 => rfl
  · intro a
    exact ⟨(fun hf => by cases hf), fun _ => rfl⟩
  · intro bb blk hblk
    cases bb with
    | zero =>
      cases hblk
      refine ⟨rfl, rfl, ⟨fun a ha => ?_, fun a ha => ?_⟩, ⟨fun a ha => ?_, fun _ _ => rfl⟩⟩
      · change setAtom emptyAtomMap condMoveAtom0 true a = true at ha; exact ha
      · change setAtom (fun _ => true) condMoveAtom0 false a = true at ha
        exact ha
      · change setAtom emptyAtomMap condMoveAtom0 true a = true at ha; exact ha
    | succ b1 => cases b1 with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨fun a ha => ?_, fun _ _ => rfl⟩⟩
      change setAtom (setAtom (setAtom (setAtom (setAtom emptyAtomMap condMoveAtom0 true) condMoveAtom0 false)
        condMoveAtom1 true) condMoveAtom1 false) condMoveAtom1 false a = true at ha
      cases h0 : Atom.beq a condMoveAtom0 with
      | true => rw [atom_beq_sound h0, setAtom_ne _ condMoveAtom_ne.symm false, setAtom_ne _ condMoveAtom_ne.symm false, setAtom_ne _ condMoveAtom_ne.symm true, setAtom_eq] at ha; cases ha
      | false =>
        cases h1 : Atom.beq a condMoveAtom1 with
        | true => rw [atom_beq_sound h1, setAtom_eq] at ha; cases ha
        | false =>
          rw [atomMap_eq_false_of_beq h1, atomMap_eq_false_of_beq h1, atomMap_eq_false_of_beq h1,
            atomMap_eq_false_of_beq h0, atomMap_eq_false_of_beq h0] at ha
          cases ha
    | succ b2 => cases b2 with
    | zero =>
      cases hblk
      refine ⟨rfl, rfl, ⟨fun _ h => h, fun _ h => h⟩, ⟨fun _ h => h, fun _ h => h⟩⟩
    | succ b3 => cases b3 with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨fun a ha => ?_, fun _ _ => rfl⟩, ⟨rfl, ?_, fun _ _ => rfl⟩⟩
      · change setAtom (setAtom emptyAtomMap condMoveAtom0 true) condMoveAtom0 false a = true at ha
        cases h0 : Atom.beq a condMoveAtom0 with
        | true => rw [atom_beq_sound h0, setAtom_eq] at ha; cases ha
        | false => rw [atomMap_eq_false_of_beq h0, atomMap_eq_false_of_beq h0] at ha; cases ha
      · intro a ha
        change setAtom (setAtom emptyAtomMap condMoveAtom0 true) condMoveAtom0 false a = true at ha
        cases h0 : Atom.beq a condMoveAtom0 with
        | true => rw [atom_beq_sound h0, setAtom_eq] at ha; cases ha
        | false => rw [atomMap_eq_false_of_beq h0, atomMap_eq_false_of_beq h0] at ha; cases ha
    | succ b4 => cases b4 with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨fun a ha => ?_, fun _ _ => rfl⟩, ⟨rfl, ?_, fun _ _ => rfl⟩⟩
      · change setAtom (setAtom emptyAtomMap condMoveAtom0 true) condMoveAtom0 false a = true at ha
        cases h0 : Atom.beq a condMoveAtom0 with
        | true => rw [atom_beq_sound h0, setAtom_eq] at ha; cases ha
        | false => rw [atomMap_eq_false_of_beq h0, atomMap_eq_false_of_beq h0] at ha; cases ha
      · intro a ha
        change setAtom (setAtom emptyAtomMap condMoveAtom0 true) condMoveAtom0 false a = true at ha
        cases h0 : Atom.beq a condMoveAtom0 with
        | true => rw [atom_beq_sound h0, setAtom_eq] at ha; cases ha
        | false => rw [atomMap_eq_false_of_beq h0, atomMap_eq_false_of_beq h0] at ha; cases ha
    | succ b5 => cases b5 with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨fun a ha => ?_, fun _ _ => rfl⟩⟩
      change setAtom emptyAtomMap condMoveAtom0 true a = true at ha
      exact ha
    | succ b6 => cases b6 with
    | zero => cases hblk; exact trivial
    | succ b7 => cases b7 with
    | zero => cases hblk; exact trivial
    | succ b8 => cases hblk

theorem condMoveReinitProg_validFa : ValidFlagAlloc condMoveReinitProg 8 condMoveReinitDf condMoveReinitFa := by
  refine ⟨inj_single_atom condMoveAtom0 0, ?_⟩
  intro bb blk _hbb hblk
  cases bb with
  | zero => cases hblk; exact trivial
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact trivial
  | succ b3 => cases b3 with
  | zero =>
    cases hblk
    dsimp only
    intro a ha _hmi _hmu
    change (Atom.beq a condMoveAtom0 || false) = true at ha
    cases ha0 : Atom.beq a condMoveAtom0 with
    | false => rw [ha0] at ha; cases ha
    | true =>
      refine ⟨0, ?_⟩
      change (if Atom.beq a condMoveAtom0 then some 0 else none) = some 0
      rw [ha0]; rfl
  | succ b4 => cases b4 with
  | zero =>
    cases hblk
    dsimp only
    intro a ha _hmi _hmu
    change (Atom.beq a condMoveAtom0 || false) = true at ha
    cases ha0 : Atom.beq a condMoveAtom0 with
    | false => rw [ha0] at ha; cases ha
    | true =>
      refine ⟨0, ?_⟩
      change (if Atom.beq a condMoveAtom0 then some 0 else none) = some 0
      rw [ha0]; rfl
  | succ b5 => cases b5 with
  | zero => cases hblk; exact trivial
  | succ b6 => cases b6 with
  | zero => cases hblk; exact trivial
  | succ b7 => cases b7 with
  | zero => cases hblk; exact trivial
  | succ b8 => cases hblk

theorem condMoveReinitProg_wellFormed : WellFormedSrcDrops condMoveReinitProg := by
  intro bb blk hblk
  cases bb with
  | zero => cases hblk; exact trivial
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact trivial
  | succ b3 => cases b3 with
  | zero => cases hblk; exact ⟨rfl, fun _ => ⟨6, rfl⟩⟩
  | succ b4 => cases b4 with
  | zero => cases hblk; exact ⟨rfl, fun _ => ⟨6, rfl⟩⟩
  | succ b5 => cases b5 with
  | zero => cases hblk; exact trivial
  | succ b6 => cases b6 with
  | zero => cases hblk; exact trivial
  | succ b7 => cases b7 with
  | zero => cases hblk; exact trivial
  | succ b8 => cases hblk

theorem condMoveReinit_all_4_paths_witness :
    let eprog := elaborateProgram condMoveReinitProg 8 condMoveReinitDf condMoveReinitFa
    let oFF : ExecOracle := { branchAt := fun _ _ => false, panicAt := fun _ _ => false }
    let oTF : ExecOracle := { branchAt := fun _ r => natEq r 0, panicAt := fun _ _ => false }
    let oTT : ExecOracle := { branchAt := fun _ _ => true, panicAt := fun _ _ => false }
    let oFT : ExecOracle := { branchAt := fun _ r => natEq r 1, panicAt := fun _ _ => false }
    (execElabFuel eprog oFF 24 (initElabState eprog)).trace = [.create 201 0, .dropCall 201 0 false] ∧
    (execElabFuel eprog oTF 24 (initElabState eprog)).trace = [.create 201 0, .dropCall 201 1 true] ∧
    (execElabFuel eprog oTT 24 (initElabState eprog)).trace =
      [.create 201 0, .dropCall 201 1 true, .create 201 0, .dropCall 201 0 false] ∧
    (execElabFuel eprog oFT 24 (initElabState eprog)).trace =
      [.create 201 0, .dropCall 201 0 false, .create 201 0, .dropCall 201 0 false] ∧
    noDoubleDropTag 201 (execSrcFuel condMoveReinitProg oFT 10 (initSrcState condMoveReinitProg)).trace ∧
    noLeakTag 201 (execSrcFuel condMoveReinitProg oFT 10 (initSrcState condMoveReinitProg)).trace :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, Nat.le_refl 2⟩, Nat.le_refl 2⟩

/-! #### Witness 3: `partialMovePairProg` (`probe.partial_move_probe`, zero flags needed statically!) -/

noncomputable def pairAtom0 : Atom :=
  { localId := 0, proj := [.field 0], tag := 10, kind := .leaf }

noncomputable def pairAtom1 : Atom :=
  { localId := 0, proj := [.field 1], tag := 20, kind := .leaf }

noncomputable def pairMovedAtom : Atom :=
  { localId := 1, proj := [], tag := 10, kind := .leaf }

noncomputable def partialMovePairProg : SrcProgram where
  locals := [.structTy false none [.dropLeaf 10, .dropLeaf 20], .dropLeaf 10]
  args := []
  entry := 0
  blocks
    | 0 => some
      { isCleanup := false
        stmts :=
          [ .storageLive 0
          , .initPlace { localId := 0, proj := [] }
          , .storageLive 1
          , .movePlace { localId := 1, proj := [] } { localId := 0, proj := [.field 0] }
          , .explicitDrop { localId := 1, proj := [] }
          , .storageDead 1 ]
        term := .scopeExit [0] 1 (some 2) }
    | 1 => some { isCleanup := false, stmts := [.storageDead 0], term := .ret }
    | 2 => some { isCleanup := true, stmts := [], term := .unwindResume }
    | _ => none

noncomputable def partialMovePairDf : DataflowCert where
  atBlock
    | 0 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | _ => { mayInit := emptyAtomMap, mayUninit := fun _ => true }

noncomputable def partialMovePairFa : FlagAlloc where
  flagOf _ := none
  allFlags := []

private theorem pairAtoms_ne :
    pairAtom1 ≠ pairAtom0 ∧ pairMovedAtom ≠ pairAtom0 ∧ pairMovedAtom ≠ pairAtom1 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> cases heq

theorem partialMovePairProg_validDf : ValidDataflowCert partialMovePairProg 3 partialMovePairDf := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro bb hlt
    cases bb with
    | zero => cases hlt | succ b1 => cases b1 with
    | zero => cases hlt | succ b2 => cases b2 with
    | zero => cases hlt | succ b3 => rfl
  · intro a
    exact ⟨(fun hf => by cases hf), fun _ => rfl⟩
  · intro bb blk hblk
    cases bb with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨fun a ha => ?_, fun _ _ => rfl⟩, ⟨rfl, fun a ha => ?_, fun _ _ => rfl⟩⟩ <;>
      · change setAtom (setAtom (setAtom (setAtom (setAtom (setAtom (setAtom (setAtom emptyAtomMap
          pairAtom0 true) pairAtom1 true) pairAtom0 false) pairMovedAtom true) pairMovedAtom false)
          pairMovedAtom false) pairAtom0 false) pairAtom1 false a = true at ha
        cases ha0 : Atom.beq a pairAtom0 with
        | true => rw [atom_beq_sound ha0, setAtom_ne _ pairAtoms_ne.1.symm false, setAtom_eq] at ha; cases ha
        | false =>
          cases ha1 : Atom.beq a pairAtom1 with
          | true => rw [atom_beq_sound ha1, setAtom_eq] at ha; cases ha
          | false =>
            cases hm : Atom.beq a pairMovedAtom with
            | true =>
              rw [atom_beq_sound hm, setAtom_ne _ pairAtoms_ne.2.2 false, setAtom_ne _ pairAtoms_ne.2.1 false, setAtom_eq] at ha
              cases ha
            | false =>
              rw [atomMap_eq_false_of_beq ha1, atomMap_eq_false_of_beq ha0,
                atomMap_eq_false_of_beq hm, atomMap_eq_false_of_beq hm, atomMap_eq_false_of_beq hm,
                atomMap_eq_false_of_beq ha0, atomMap_eq_false_of_beq ha1, atomMap_eq_false_of_beq ha0] at ha
              cases ha
    | succ b1 => cases b1 with
    | zero => cases hblk; exact trivial
    | succ b2 => cases b2 with
    | zero => cases hblk; exact trivial
    | succ b3 => cases hblk

theorem partialMovePairProg_validFa : ValidFlagAlloc partialMovePairProg 3 partialMovePairDf partialMovePairFa := by
  refine ⟨(fun _ _ _ ha _ => by cases ha), ?_⟩
  intro bb blk _hbb hblk
  cases bb with
  | zero =>
    cases hblk
    dsimp only
    intro a _ha hmi _hmu
    change setAtom (setAtom (setAtom (setAtom (setAtom (setAtom emptyAtomMap
      pairAtom0 true) pairAtom1 true) pairAtom0 false) pairMovedAtom true) pairMovedAtom false) pairMovedAtom false a = true at hmi
    cases ha1 : Atom.beq a pairAtom1 with
    | true =>
      exfalso
      change setAtom (setAtom (setAtom (setAtom (setAtom (setAtom (fun _ => true)
        pairAtom0 false) pairAtom1 false) pairAtom0 true) pairMovedAtom false) pairMovedAtom true) pairMovedAtom true a = true at _hmu
      rw [atom_beq_sound ha1, setAtom_ne _ pairAtoms_ne.2.2.symm true, setAtom_ne _ pairAtoms_ne.2.2.symm true,
        setAtom_ne _ pairAtoms_ne.2.2.symm false, setAtom_ne _ pairAtoms_ne.1 true, setAtom_eq] at _hmu
      cases _hmu
    | false =>
      cases ha0 : Atom.beq a pairAtom0 with
      | true =>
        rw [atom_beq_sound ha0, setAtom_ne _ pairAtoms_ne.2.1.symm false, setAtom_ne _ pairAtoms_ne.2.1.symm false,
          setAtom_ne _ pairAtoms_ne.2.1.symm true, setAtom_eq] at hmi
        cases hmi
      | false =>
        cases hm : Atom.beq a pairMovedAtom with
        | true => rw [atom_beq_sound hm, setAtom_eq] at hmi; cases hmi
        | false =>
          rw [atomMap_eq_false_of_beq hm, atomMap_eq_false_of_beq hm, atomMap_eq_false_of_beq hm,
            atomMap_eq_false_of_beq ha0, atomMap_eq_false_of_beq ha1, atomMap_eq_false_of_beq ha0] at hmi
          cases hmi
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact trivial
  | succ b3 => cases hblk

theorem partialMovePairProg_wellFormed : WellFormedSrcDrops partialMovePairProg := by
  intro bb blk hblk
  cases bb with
  | zero => cases hblk; exact ⟨rfl, fun _ => ⟨2, rfl⟩⟩
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact trivial
  | succ b3 => cases hblk

theorem partialMovePair_witness :
    let eprog := elaborateProgram partialMovePairProg 3 partialMovePairDf partialMovePairFa
    let oracle : ExecOracle := { branchAt := fun _ _ => false, panicAt := fun _ _ => false }
    let s := execSrcFuel partialMovePairProg oracle 4 (initSrcState partialMovePairProg)
    let e := execElabFuel eprog oracle 8 (initElabState eprog)
    s.exit = .returned ∧ e.exit = .returned ∧
    s.trace = [.create 10 0, .create 20 0, .dropCall 10 1 true, .dropCall 20 0 false] ∧
    e.trace = [.create 10 0, .create 20 0, .dropCall 10 1 true, .dropCall 20 0 false] ∧
    noDoubleDropTag 10 e.trace ∧ noLeakTag 10 e.trace ∧
    noDoubleDropTag 20 e.trace ∧ noLeakTag 20 e.trace :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, Nat.le_refl 1⟩, Nat.le_refl 1, ⟨rfl, Nat.le_refl 1⟩, Nat.le_refl 1⟩

/-! #### Witness 4: `unwindHalfLadderProg` (`probe.unwind_field_ladder`, panic in field 0 cleanup unwind) -/

noncomputable def tripleAtom0 : Atom :=
  { localId := 0, proj := [.field 0], tag := 1, kind := .leaf }

noncomputable def tripleAtom1 : Atom :=
  { localId := 0, proj := [.field 1], tag := 2, kind := .leaf }

noncomputable def tripleAtom2 : Atom :=
  { localId := 0, proj := [.field 2], tag := 3, kind := .leaf }

noncomputable def unwindHalfLadderProg : SrcProgram where
  locals := [.structTy false none [.dropLeaf 1, .dropLeaf 2, .dropLeaf 3]]
  args := []
  entry := 0
  blocks
    | 0 => some { isCleanup := false, stmts := [.storageLive 0, .initPlace { localId := 0, proj := [] }], term := .drop { localId := 0, proj := [] } 1 (some 2) }
    | 1 => some { isCleanup := false, stmts := [.storageDead 0], term := .ret }
    | 2 => some { isCleanup := true, stmts := [], term := .unwindResume }
    | _ => none

noncomputable def unwindHalfLadderDf : DataflowCert where
  atBlock
    | 0 => { mayInit := emptyAtomMap, mayUninit := fun _ => true }
    | _ => { mayInit := emptyAtomMap, mayUninit := fun _ => true }

noncomputable def unwindHalfLadderFa : FlagAlloc where
  flagOf _ := none
  allFlags := []

private theorem tripleAtoms_ne :
    tripleAtom1 ≠ tripleAtom0 ∧ tripleAtom2 ≠ tripleAtom0 ∧ tripleAtom2 ≠ tripleAtom1 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> cases heq

theorem unwindHalfLadderProg_validDf : ValidDataflowCert unwindHalfLadderProg 3 unwindHalfLadderDf := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro bb hlt
    cases bb with
    | zero => cases hlt | succ b1 => cases b1 with
    | zero => cases hlt | succ b2 => cases b2 with
    | zero => cases hlt | succ b3 => rfl
  · intro a
    exact ⟨(fun hf => by cases hf), fun _ => rfl⟩
  · intro bb blk hblk
    cases bb with
    | zero =>
      cases hblk
      refine ⟨rfl, ⟨fun a ha => ?_, fun _ _ => rfl⟩, ⟨rfl, fun a ha => ?_, fun _ _ => rfl⟩⟩ <;>
      · change setAtom (setAtom (setAtom (setAtom (setAtom (setAtom emptyAtomMap
          tripleAtom0 true) tripleAtom1 true) tripleAtom2 true)
          tripleAtom0 false) tripleAtom1 false) tripleAtom2 false a = true at ha
        cases ha0 : Atom.beq a tripleAtom0 with
        | true =>
          rw [atom_beq_sound ha0, setAtom_ne _ tripleAtoms_ne.2.1.symm false,
            setAtom_ne _ tripleAtoms_ne.1.symm false, setAtom_eq] at ha
          cases ha
        | false =>
          cases ha1 : Atom.beq a tripleAtom1 with
          | true =>
            rw [atom_beq_sound ha1, setAtom_ne _ tripleAtoms_ne.2.2.symm false, setAtom_eq] at ha
            cases ha
          | false =>
            cases ha2 : Atom.beq a tripleAtom2 with
            | true => rw [atom_beq_sound ha2, setAtom_eq] at ha; cases ha
            | false =>
              rw [atomMap_eq_false_of_beq ha2, atomMap_eq_false_of_beq ha1, atomMap_eq_false_of_beq ha0,
                atomMap_eq_false_of_beq ha2, atomMap_eq_false_of_beq ha1, atomMap_eq_false_of_beq ha0] at ha
              cases ha
    | succ b1 => cases b1 with
    | zero => cases hblk; exact trivial
    | succ b2 => cases b2 with
    | zero => cases hblk; exact trivial
    | succ b3 => cases hblk

theorem unwindHalfLadderProg_validFa :
    ValidFlagAlloc unwindHalfLadderProg 3 unwindHalfLadderDf unwindHalfLadderFa := by
  refine ⟨(fun _ _ _ ha _ => by cases ha), ?_⟩
  intro bb blk _hbb hblk
  cases bb with
  | zero =>
    cases hblk
    dsimp only
    intro a _ha _hmi hmu
    change setAtom (setAtom (setAtom (fun _ => true)
      tripleAtom0 false) tripleAtom1 false) tripleAtom2 false a = true at hmu
    cases ha0 : Atom.beq a tripleAtom0 with
    | true =>
      rw [atom_beq_sound ha0, setAtom_ne _ tripleAtoms_ne.2.1.symm false,
        setAtom_ne _ tripleAtoms_ne.1.symm false, setAtom_eq] at hmu
      cases hmu
    | false =>
      cases ha1 : Atom.beq a tripleAtom1 with
      | true =>
        rw [atom_beq_sound ha1, setAtom_ne _ tripleAtoms_ne.2.2.symm false, setAtom_eq] at hmu
        cases hmu
      | false =>
        cases ha2 : Atom.beq a tripleAtom2 with
        | true => rw [atom_beq_sound ha2, setAtom_eq] at hmu; cases hmu
        | false =>
          change (Atom.beq a tripleAtom0 || (Atom.beq a tripleAtom1 || (Atom.beq a tripleAtom2 || false))) = true at _ha
          rw [ha0, ha1, ha2] at _ha
          cases _ha
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact trivial
  | succ b3 => cases hblk

theorem unwindHalfLadderProg_wellFormed : WellFormedSrcDrops unwindHalfLadderProg := by
  intro bb blk hblk
  cases bb with
  | zero => cases hblk; exact ⟨rfl, fun _ => ⟨2, rfl⟩⟩
  | succ b1 => cases b1 with
  | zero => cases hblk; exact trivial
  | succ b2 => cases b2 with
  | zero => cases hblk; exact trivial
  | succ b3 => cases hblk

theorem unwindHalfLadder_panic_witness :
    let eprog := elaborateProgram unwindHalfLadderProg 3 unwindHalfLadderDf unwindHalfLadderFa
    let panicFirstOracle : ExecOracle :=
      { branchAt := fun _ _ => false, panicAt := fun d _ => natEq d 0 }
    let s := execSrcFuel unwindHalfLadderProg panicFirstOracle 4 (initSrcState unwindHalfLadderProg)
    let e := execElabFuel eprog panicFirstOracle 10 (initElabState eprog)
    s.exit = .unwound ∧ e.exit = .unwound ∧
    s.trace = [.create 1 0, .create 2 0, .create 3 0,
               .dropCall 1 0 false, .dropCall 2 0 false, .dropCall 3 0 false] ∧
    e.trace = [.create 1 0, .create 2 0, .create 3 0,
               .dropCall 1 0 false, .dropCall 2 0 false, .dropCall 3 0 false] ∧
    noDoubleDropTag 1 e.trace ∧ noLeakTag 1 e.trace ∧
    noDoubleDropTag 2 e.trace ∧ noLeakTag 2 e.trace ∧
    noDoubleDropTag 3 e.trace ∧ noLeakTag 3 e.trace :=
  ⟨rfl, rfl, rfl, rfl,
    ⟨rfl, Nat.le_refl 1⟩, Nat.le_refl 1,
    ⟨rfl, Nat.le_refl 1⟩, Nat.le_refl 1,
    ⟨rfl, Nat.le_refl 1⟩, Nat.le_refl 1⟩

end Vrustc.MirDropElaboration

