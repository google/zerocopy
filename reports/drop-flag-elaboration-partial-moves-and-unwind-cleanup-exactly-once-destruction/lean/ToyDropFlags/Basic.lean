/-!
# Ownership trees, places, destructor logs

A toy model of affine values with destructors. A local variable has a type that is an
ownership tree: leaves are owned resources with a destructor; binary products ("structs" with
two named fields `.0` and `.1`) either have their own destructor (a user `Drop` impl) or not.

* A **unit** is a node whose destruction is logged: every leaf, and every struct node that has
  its own destructor (its `Drop::drop` call).
* An **atom** is a maximal move path: a leaf not inside a struct with a destructor, or a struct
  with a destructor not inside another one. Initialization is tracked per atom, because a struct
  with its own destructor cannot be partially moved.

Values carry identities: every initialization writes fresh ids into the units it covers. The
destructor log records creations, hand-offs to a consumer (a move into a sink or into a callee,
which then owns and destroys the value), destructor calls, and destructor calls on memory that
was never written ("garbage").
-/

namespace Toy.DropFlags

/-- Ownership-tree types. `pair d a b` is a struct with fields `.0 : a` and `.1 : b`; `d = true`
means the struct has its own destructor (captures a Rust struct with a `Drop` impl). -/
inductive Ty where
  | leaf : Ty
  | pair (hasDrop : Bool) (a b : Ty) : Ty
  deriving DecidableEq, Repr

/-- A path into a type: `false` selects field `.0`, `true` selects field `.1`. -/
abbrev Path := List Bool

/-- Destructor units of a type, as paths, in drop-glue order: a struct with its own destructor
contributes its own path first (its destructor runs before its fields are dropped), then its
fields' units. A struct without a destructor contributes only its fields' units. -/
def Ty.units : Ty → List Path
  | .leaf => [[]]
  | .pair d a b =>
      (if d then [[]] else []) ++ (a.units.map (false :: ·) ++ b.units.map (true :: ·))

/-- Atoms of a type: maximal move paths. A struct with its own destructor is atomic. -/
def Ty.atoms : Ty → List Path
  | .leaf => [[]]
  | .pair true _ _ => [[]]
  | .pair false a b => a.atoms.map (false :: ·) ++ b.atoms.map (true :: ·)

/-- `t.isMovePath p`: `p` follows the shape of `t` and never enters a struct that has its own
destructor (it may end at one). These are the places that may be moved or initialized. -/
def Ty.isMovePath : Ty → Path → Bool
  | _, [] => true
  | .leaf, _ :: _ => false
  | .pair true _ _, _ :: _ => false
  | .pair false a _, false :: p => a.isMovePath p
  | .pair false _ b, true :: p => b.isMovePath p

/-- A place: a local (by index) and a path into its type. -/
structure Place where
  loc : Nat
  path : Path
  deriving DecidableEq, Repr

/-- `p.covers q`: `q` lies inside `p` (same local, `p.path` a prefix of `q.path`). -/
def Place.covers (p q : Place) : Bool :=
  p.loc == q.loc && p.path.isPrefixOf q.path

/-- Two places overlap when one covers the other. -/
def Place.overlaps (p q : Place) : Bool :=
  p.covers q || q.covers p

/-- All places of a list of locals selected by `f`, with local indices starting at `i`. -/
def placesFrom (f : Ty → List Path) : Nat → List Ty → List Place
  | _, [] => []
  | i, t :: ts => (f t).map (Place.mk i) ++ placesFrom f (i + 1) ts

/-- All destructor units of the locals. -/
def allUnits (ls : List Ty) : List Place := placesFrom Ty.units 0 ls

/-- All atoms of the locals. -/
def allAtoms (ls : List Ty) : List Place := placesFrom Ty.atoms 0 ls

/-- Units lying inside place `p` (in drop-glue order). -/
def unitsUnder (ls : List Ty) (p : Place) : List Place :=
  (allUnits ls).filter (p.covers ·)

/-- Atoms overlapping place `p`. For a move path `p` these are the atoms inside `p`; for a place
strictly inside a struct with a destructor, it is that struct's atom. -/
def atomsOf (ls : List Ty) (p : Place) : List Place :=
  (allAtoms ls).filter (p.overlaps ·)

/-- `p` is a valid move path of the locals `ls`. -/
def isMovePlace (ls : List Ty) (p : Place) : Bool :=
  match ls[p.loc]? with
  | some t => t.isMovePath p.path
  | none => false

/-! ## Destructor logs -/

/-- Logged events. `create v`: a value with id `v` was written. `consume v`: ownership of `v`
was handed to a consumer (a sink or callee), which is then responsible for destroying it.
`drop v`: the destructor of `v` ran. `garbage`: a destructor or consumer ran on memory that was
never written. -/
inductive Event where
  | create (v : Nat)
  | consume (v : Nat)
  | drop (v : Nat)
  | garbage
  deriving DecidableEq, Repr

/-- Number of destruction events for id `v`: hand-offs to a consumer plus destructor calls. -/
def destroyCount (log : List Event) (v : Nat) : Nat :=
  log.countP fun e => e == .consume v || e == .drop v

/-- Ids that occur in a destruction event. -/
def destroyedIds (log : List Event) : List Nat :=
  log.filterMap fun
    | .consume v => some v
    | .drop v => some v
    | _ => none

/-- Ids that were created. -/
def createdIds (log : List Event) : List Nat :=
  log.filterMap fun
    | .create v => some v
    | _ => none

/-- **NoDoubleDrop**: (1) no value is destroyed twice (a hand-off to a consumer counts as a
destruction, so dropping a moved-out value violates it); (2) every destroyed id occurs in a
`create` event of the log; (3) no destructor or consumer runs on memory that was never written
(`garbage`). Ids not occurring in a destruction event have count 0, so quantifying over
`destroyedIds` is the same as quantifying over all ids. The order of events is not checked: a
log in which a destruction precedes the creation of the same id is admitted. -/
def NoDoubleDrop (log : List Event) : Prop :=
  (∀ v ∈ destroyedIds log, destroyCount log v ≤ 1) ∧
  (∀ v ∈ destroyedIds log, v ∈ createdIds log) ∧
  Event.garbage ∉ log

/-- **NoLeak**: every created value is destroyed (dropped or handed to a consumer). -/
def NoLeak (log : List Event) : Prop :=
  ∀ v ∈ createdIds log, 1 ≤ destroyCount log v

instance (log : List Event) : Decidable (NoDoubleDrop log) := by
  unfold NoDoubleDrop; exact inferInstance

instance (log : List Event) : Decidable (NoLeak log) := by
  unfold NoLeak; exact inferInstance

end Toy.DropFlags
