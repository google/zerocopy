/-!
# Scoped views: the toy state model

A *view* is a handle through which a region of raw-pointer-owned memory is accessed. Root views
(no parent) stand for memory owned through a raw pointer; child views stand for references lent
out of a parent view (exclusive reborrows, like `&mut`, or shared reborrows, like `&`), possibly
nested to any depth.

Each view records its parent, its *mode* (how it obtained its cells), an `active` flag, and, for
each address it covers, a per-view *cell*:

* `own d b`  — the view can access the byte `b`; depth `0` means read/write, depth `d + 1` means
  read-only. The depth counts sharing: a view's depth is its mode baseline (`0` for an exclusive
  view, `1` for a shared view) plus the number of shared children currently reading that cell.
* `loaned c` — the cell is exclusively lent to child view `c`; it cannot be accessed through this
  view until the loan ends.

View ids are positions in a list, so `s.views.length` is the next fresh id and ids are never
reused. Inactive (retired) views keep their metadata but grant no access.

This is a toy model. It has no allocation or deallocation of roots, no notion of allocation
lifetime separate from view activity, no addresses or layout beyond natural-number cell indices,
and no typed values. Bytes held by different views for the same address are not required to agree
(only permissions are tracked, not value coherence).
-/

namespace Toy.Views

/-- View identifiers: positions in `State.views`. -/
abbrev ViewId := Nat
/-- Cell addresses: positions in `View.cells`. -/
abbrev Addr := Nat
/-- Byte contents (uninterpreted). -/
abbrev Byte := Nat

/-- How a view obtained its cells: exclusively (`excl`, read/write while no child holds them) or
shared (`shared`, read-only). Root views use the mode to say whether the raw memory they expose is
writable (`excl`) or read-only (`shared`). -/
inductive Mode where
  | excl
  | shared
  deriving DecidableEq, Repr

/-- A per-view cell: `own depth byte` (accessible; writable iff `depth = 0`) or `loaned child`
(exclusively lent to `child`; inaccessible here). -/
inductive Cell where
  | own (depth : Nat) (byte : Byte)
  | loaned (child : ViewId)
  deriving DecidableEq, Repr

/-- A view: parent link (`none` for a root), mode, activity flag, and address-indexed cells
(`none` = address not covered by this view). -/
structure View where
  parent : Option ViewId
  mode : Mode
  active : Bool
  cells : List (Option Cell)
  deriving DecidableEq, Repr

/-- A state: the list of all views ever created; the view with id `v` is `views[v]`. -/
structure State where
  views : List View
  deriving DecidableEq, Repr

/-- The depth of a cell, if it is accessible (`own`). -/
def Cell.depth? : Cell → Option Nat
  | .own d _ => some d
  | .loaned _ => none

/-- The mode baseline depth: `0` for exclusive views, `1` for shared views. -/
def Mode.baseline : Mode → Nat
  | .excl => 0
  | .shared => 1

/-- The cell of a view at address `a`, if covered. -/
def View.cell? (vw : View) (a : Addr) : Option Cell := vw.cells.getD a none

/-- The addresses a view covers, in increasing order. -/
def View.domain (vw : View) : List Addr :=
  (List.range vw.cells.length).filter (fun a => (vw.cell? a).isSome)

namespace State

/-- Number of views ever created (= the next fresh id). -/
def size (s : State) : Nat := s.views.length

/-- An upper bound on all covered addresses: the longest cell list. -/
def width (s : State) : Nat := s.views.foldr (fun vw m => max vw.cells.length m) 0

/-- The view with id `v`, if it exists. -/
def view? (s : State) (v : ViewId) : Option View := s.views[v]?

/-- The cell of view `v` at address `a`, if `v` exists and covers `a`. -/
def cell? (s : State) (v : ViewId) (a : Addr) : Option Cell := (s.view? v).bind (·.cell? a)

/-- The depth of view `v`'s cell at `a`, if that cell exists and is accessible. -/
def depth? (s : State) (v : ViewId) (a : Addr) : Option Nat := (s.cell? v a).bind Cell.depth?

/-- The parent of view `v` (`none` if `v` is a root or does not exist). -/
def parentOf (s : State) (v : ViewId) : Option ViewId := (s.view? v).bind View.parent

/-- The mode of view `v`, if it exists. -/
def modeOf (s : State) (v : ViewId) : Option Mode := (s.view? v).map View.mode

/-- Whether view `v` exists and is active. -/
def isActive (s : State) (v : ViewId) : Bool := ((s.view? v).map View.active).getD false

/-- Whether view `v` exists and covers address `a`. -/
def covers (s : State) (v : ViewId) (a : Addr) : Bool := (s.cell? v a).isSome

/-- The mode baseline of view `v` (`0` if `v` does not exist). -/
def baselineOf (s : State) (v : ViewId) : Nat := ((s.modeOf v).map Mode.baseline).getD 0

/-- Read access: `v` is active and holds `a` as an `own` cell (any depth). Access through an
inactive view is impossible by construction. -/
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome

/-- Write access: `v` is active and holds `a` as an `own` cell of depth `0`. -/
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0

/-- Access level of `v` at `a`: `2` write, `1` read-only, `0` none. -/
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0

/-- Number of active shared-mode children of `v` that cover `a` (the readers `v` has lent `a`
to). -/
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length

/-- Replace view `v` (no effect if `v` does not exist). -/
def setView (s : State) (v : ViewId) (vw : View) : State := ⟨s.views.set v vw⟩

end State

/-! ## Operations -/

/-- Rewrite every cell of a view through `f` (applied to all addresses below `n`). -/
def View.mapCells (vw : View) (n : Nat) (f : Addr → Option Cell → Option Cell) : View :=
  { vw with cells := (List.range n).map (fun a => f a (vw.cell? a)) }

/-- Is `x` an `own` cell of depth `0`? -/
def Cell.isWritable : Option Cell → Bool
  | some (.own 0 _) => true
  | _ => false

/-- Is `x` an `own` cell (any depth)? -/
def Cell.isOwn : Option Cell → Bool
  | some (.own _ _) => true
  | _ => false

/-- The byte of an `own` cell (`0` otherwise; only used on `own` cells). -/
def Cell.byteOf : Option Cell → Byte
  | some (.own _ b) => b
  | _ => 0

/-- Create an exclusive child of active exclusive-mode view `p` covering addresses `A` (all of
which `p` must hold writable). The parent's cells become `loaned c` for the fresh id `c`; the child
holds them at depth `0` with the same bytes. -/
def borrow (s : State) (p : ViewId) (A : List Addr) : Option State :=
  match s.view? p with
  | none => none
  | some vp =>
    if vp.active && vp.mode == .excl && A.all (fun a => Cell.isWritable (vp.cell? a)) then
      let c := s.size
      let n := vp.cells.length
      let vp' := vp.mapCells n (fun a x => if A.contains a then some (.loaned c) else x)
      let vc : View :=
        { parent := some p, mode := .excl, active := true,
          cells := (List.range n).map (fun a =>
            if A.contains a then some (.own 0 (Cell.byteOf (vp.cell? a))) else none) }
      some ⟨(s.views.set p vp') ++ [vc]⟩
    else none

/-- Create a shared child of active view `p` covering addresses `A` (all of which `p` must hold as
`own` cells). The parent's depth at each address goes up by one; the child holds the cells at its
baseline depth `1` with the same bytes. -/
def share (s : State) (p : ViewId) (A : List Addr) : Option State :=
  match s.view? p with
  | none => none
  | some vp =>
    if vp.active && A.all (fun a => Cell.isOwn (vp.cell? a)) then
      let n := vp.cells.length
      let vp' := vp.mapCells n (fun a x =>
        if A.contains a then
          match x with
          | some (.own d b) => some (.own (d + 1) b)
          | y => y
        else x)
      let vc : View :=
        { parent := some p, mode := .shared, active := true,
          cells := (List.range n).map (fun a =>
            if A.contains a then some (.own 1 (Cell.byteOf (vp.cell? a))) else none) }
      some ⟨(s.views.set p vp') ++ [vc]⟩
    else none

/-- Write byte `b` at `a` through `v`; enabled iff `v` can write `a`. -/
def write (s : State) (v : ViewId) (a : Addr) (b : Byte) : Option State :=
  match s.view? v with
  | none => none
  | some vw =>
    if s.canWrite v a then
      some (s.setView v (vw.mapCells vw.cells.length (fun a' x => if a' = a then some (.own 0 b) else x)))
    else none

/-- Read the byte at `a` through `v`; enabled iff `v` can read `a`. -/
def read (s : State) (v : ViewId) (a : Addr) : Option Byte :=
  if s.canRead v a then some (Cell.byteOf (s.cell? v a)) else none

/-- Is parent view `vp` active, and does it hold every cell covered by child view `vc` (with id
`c`) as an *outstanding loan* — `loaned c` if `vc` is exclusive, and an `own` cell whose depth is
strictly above `vp`'s own mode baseline (so at least one shared loan is outstanding) if `vc` is
shared? This is the only check the raw end operation performs: the parent that is active and holds
the child's cells in loaned-out form may take them back. Nothing about the child's own cells or
descendants is inspected. -/
def returnable (vc vp : View) (c : ViewId) : Bool :=
  vp.active && (List.range vc.cells.length).all fun a =>
    match vc.cell? a with
    | none => true
    | some _ =>
      match vc.mode, vp.cell? a with
      | .excl, some (.loaned c') => c' == c
      | .shared, some (.own d _) => decide (vp.mode.baseline < d)
      | _, _ => false

/-- The parent's cells after child `vc` returns: each cell covered by an exclusive child becomes
writable again with the supplied byte `r a` (the value handed back by the borrow's continuation);
each cell covered by a shared child has its depth decremented. -/
def restoreCells (vc vp : View) (r : Addr → Byte) : View :=
  vp.mapCells (max vp.cells.length vc.cells.length) fun a x =>
    match vc.cell? a with
    | none => x
    | some _ =>
      match vc.mode, x with
      | .excl, _ => some (.own 0 (r a))
      | .shared, some (.own (d + 1) b) => some (.own d b)
      | .shared, y => y

/-- Raw end of view `c`: retire `c` and give its cells back to its parent. Enabled iff `c` is
active, has an existing parent, and that parent is active and holds all of `c`'s cells as
outstanding loans (`returnable`). Nothing about `c`'s own cells or descendants is checked: this is
the *naive* rule "the parent holding the loaned-out cells may end the borrow". Root views (no
parent) can never be ended by this operation. Sound uses must additionally establish
`ReturnAuthority`. -/
def endRaw (s : State) (c : ViewId) (r : Addr → Byte) : Option State :=
  match s.view? c with
  | none => none
  | some vc =>
    match vc.parent with
    | none => none
    | some p =>
      match s.view? p with
      | none => none
      | some vp =>
        if vc.active && returnable vc vp c then
          let s₁ := s.setView p (restoreCells vc vp r)
          match s₁.view? c with
          | none => none
          | some vc₁ => some (s₁.setView c { vc₁ with active := false })
        else none

end Toy.Views
