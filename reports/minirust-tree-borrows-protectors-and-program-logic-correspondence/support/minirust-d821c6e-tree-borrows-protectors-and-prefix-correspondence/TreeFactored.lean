import AnnealResearch.TreePermissions

/-!
Independent topology/store encoding of the selected MiniRust Tree Borrows
operations, source d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed.

The recursive ordered topology is separate from per-path permission arrays and
protector flags.  This module shares only the disclosed scalar tables in
TreePermissions, and does not import or run the recursive reference encoding.
Only paths represented by the topology have semantic payloads; total-store
values at absent paths are outside the representation relation.

The parent alone compiles.  Manual interpretation of helper mutation/value
semantics remains audited, not a generated-interpreter or Rust adequacy theorem.
-/
namespace AnnealResearch.TreeFactored

open TreePermissions

abbrev Path := List Nat

mutual
  inductive Topology where
    | node (children : Forest)
  inductive Forest where
    | nil
    | cons (child : Topology) (rest : Forest)
end

structure Entry where
  permissions : List Permission
  protection : Protected

abbrev Store := Path → Entry

structure State where
  topology : Topology
  store : Store

inductive Structural where
  | invalidPath | arrayLength | range | missingProtector | unprotectUnprotected
  deriving DecidableEq, Repr

inductive Result (A S : Type) where
  | ok (value : A) (state : S)
  | ub (fault : Fault) (state : S)
  | unsupported (reason : Structural) (state : S)

def Result.mapState {A S T : Type} (f : S → T) : Result A S → Result A T
  | .ok value state => .ok value (f state)
  | .ub fault state => .ub fault (f state)
  | .unsupported reason state => .unsupported reason (f state)

def Result.bind {A B S : Type} (result : Result A S)
    (next : A → S → Result B S) : Result B S :=
  match result with
  | .ok value state => next value state
  | .ub fault state => .ub fault state
  | .unsupported reason state => .unsupported reason state

def overwrite (store : Store) (path : Path) (entry : Entry) : Store :=
  fun selected => if selected = path then entry else store selected

def setPermissions (store : Store) (path : Path) (permissions : List Permission) : Store :=
  overwrite store path { store path with permissions := permissions }

def setProtected (store : Store) (path : Path) (protection : Protected) : Store :=
  overwrite store path { store path with protection := protection }

def nodeRelation : Option Path → NodeRelation
  | none => .foreignNode
  | some _ => .localNode

def childPath (path : Option Path) (index : Nat) : Option Path :=
  match path with
  | some (head :: tail) => if head = index then some tail else none
  | _ => none

theorem overwrite_same (store : Store) (path : Path) (entry : Entry) :
    overwrite store path entry path = entry := by simp [overwrite]

theorem overwrite_other (store : Store) (path other : Path) (entry : Entry)
    (different : other ≠ path) : overwrite store path entry other = store other := by
  simp [overwrite, different]

theorem selected_node_children_are_foreign (index : Nat) : childPath (some []) index = none := rfl

#print axioms overwrite_same
#print axioms overwrite_other
#print axioms selected_node_children_are_foreign

def permissionAt : List Permission → Nat → Option Permission
  | [], _ => none
  | permission :: _, 0 => some permission
  | _ :: rest, index + 1 => permissionAt rest index

def replacePermission : List Permission → Nat → Permission → List Permission
  | [], _, _ => []
  | _ :: rest, 0, permission => permission :: rest
  | head :: rest, index + 1, permission => head :: replacePermission rest index permission

/-- One atomic scalar update. Failure leaves this byte unchanged; earlier
updates already present in the supplied store remain present. -/
def transitionAt (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset : Nat) : Result Unit Store :=
  let permissions := (store here).permissions
  match permissionAt permissions offset with
  | none => .unsupported .range store
  | some permission =>
    match permission.transition kind relation with
    | .error fault => .ub fault store
    | .ok next => .ok () (setPermissions store here
        (replacePermission permissions offset next))

def transitionOffsets (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset : Nat) : Nat → Result Unit Store
  | 0 => .ok () store
  | count + 1 =>
      Result.bind (transitionAt store here kind relation offset) fun _ changed =>
        transitionOffsets changed here kind relation (offset + 1) count

def releaseOffsets (store : Store) (here : Path) (relation : NodeRelation)
    (offset : Nat) : List (Option AccessKind) → Result Unit Store
  | [] => .ok () store
  | none :: rest => releaseOffsets store here relation (offset + 1) rest
  | some kind :: rest =>
      Result.bind (transitionAt store here kind relation offset) fun _ changed =>
        releaseOffsets changed here relation (offset + 1) rest

mutual
  def accessTree (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (kind : AccessKind) (offset size : Nat) : Result Unit Store :=
    match topology with
    | .node children =>
      Result.bind (transitionOffsets store here kind (nodeRelation path) offset size)
        fun _ changed => accessForest children here 0 changed path kind offset size
  termination_by structural topology

  def accessForest (children : Forest) (parent : Path) (index : Nat) (store : Store)
      (path : Option Path) (kind : AccessKind) (offset size : Nat) : Result Unit Store :=
    match children with
    | .nil => .ok () store
    | .cons child rest =>
      Result.bind (accessTree child (parent ++ [index]) store (childPath path index)
        kind offset size) fun _ changed =>
          accessForest rest parent (index + 1) changed path kind offset size
  termination_by structural children
end

mutual
  def releaseTree (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (accesses : List (Option AccessKind)) : Result Unit Store :=
    match topology with
    | .node children =>
      match path with
      | some [] => .ok () (setProtected store here .no)
      | _ =>
        Result.bind (releaseOffsets store here (nodeRelation path) 0 accesses)
          fun _ changed => releaseForest children here 0 changed path accesses
  termination_by structural topology

  def releaseForest (children : Forest) (parent : Path) (index : Nat) (store : Store)
      (path : Option Path) (accesses : List (Option AccessKind)) : Result Unit Store :=
    match children with
    | .nil => .ok () store
    | .cons child rest =>
      Result.bind (releaseTree child (parent ++ [index]) store (childPath path index)
        accesses) fun _ changed =>
          releaseForest rest parent (index + 1) changed path accesses
  termination_by structural children
end

def accessCore (state : State) (path : Option Path) (kind : AccessKind)
    (offset size : Nat) : Result Unit State :=
  Result.mapState (fun store => { state with store := store })
    (accessTree state.topology [] state.store path kind offset size)

def releaseCore (state : State) (path : Option Path)
    (accesses : List (Option AccessKind)) : Result Unit State :=
  Result.mapState (fun store => { state with store := store })
    (releaseTree state.topology [] state.store path accesses)

mutual
  def containsStrongTree (topology : Topology) (here : Path) (store : Store) : Bool :=
    match topology with
    | .node children =>
      let own := match (store here).protection with
        | .strong => (store here).permissions.any Permission.preventsDeallocation
        | _ => false
      own || containsStrongForest children here 0 store
  termination_by structural topology

  def containsStrongForest (children : Forest) (parent : Path) (index : Nat)
      (store : Store) : Bool :=
    match children with
    | .nil => false
    | .cons child rest =>
      containsStrongTree child (parent ++ [index]) store ||
        containsStrongForest rest parent (index + 1) store
  termination_by structural children
end

def containsStrong (state : State) : Bool :=
  containsStrongTree state.topology [] state.store

mutual
  def arrayLengthsTree (topology : Topology) (here : Path) (store : Store)
      (width : Nat) : Bool :=
    match topology with
    | .node children =>
      decide ((store here).permissions.length = width) &&
        arrayLengthsForest children here 0 store width
  termination_by structural topology

  def arrayLengthsForest (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (width : Nat) : Bool :=
    match children with
    | .nil => true
    | .cons child rest =>
      arrayLengthsTree child (parent ++ [index]) store width &&
        arrayLengthsForest rest parent (index + 1) store width
  termination_by structural children
end

mutual
  def matchingTree (topology : Topology) (here : Path) (store : Store) : Bool :=
    match topology with
    | .node children =>
      (store here).permissions.all (fun permission =>
        permission.matchesProtector (store here).protection) &&
        matchingForest children here 0 store
  termination_by structural topology

  def matchingForest (children : Forest) (parent : Path) (index : Nat)
      (store : Store) : Bool :=
    match children with
    | .nil => true
    | .cons child rest => matchingTree child (parent ++ [index]) store &&
        matchingForest rest parent (index + 1) store
  termination_by structural children
end

/-- This invariant is exposed for proofs, and is never an execution guard. -/
def matchesProtectors (state : State) : Bool := matchingTree state.topology [] state.store

def Forest.length : Forest → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

def Forest.get? : Forest → Nat → Option Topology
  | .nil, _ => none
  | .cons child _, 0 => some child
  | .cons _ rest, index + 1 => rest.get? index

def Forest.replace : Forest → Nat → Topology → Forest
  | .nil, _, _ => .nil
  | .cons _ rest, 0, child => .cons child rest
  | .cons head rest, index + 1, child => .cons head (rest.replace index child)

def Forest.snoc : Forest → Topology → Forest
  | .nil, child => .cons child .nil
  | .cons head rest, child => .cons head (rest.snoc child)

def findTopology (topology : Topology) (path : Path) : Option Topology :=
  match path, topology with
  | [], _ => some topology
  | index :: rest, .node children =>
    match children.get? index with
    | none => none
    | some child => findTopology child rest
termination_by structural path

def modifyTopology (topology : Topology) (path : Path)
    (update : Topology → Topology) : Option Topology :=
  match path, topology with
  | [], _ => some (update topology)
  | index :: rest, .node children =>
    match children.get? index with
    | none => none
    | some child =>
      match modifyTopology child rest update with
      | none => none
      | some changed => some (.node (children.replace index changed))
termination_by structural path

def findNode (state : State) (path : Path) : Option State :=
  match findTopology state.topology path with
  | none => none
  | some topology => some { topology := topology, store := fun rest => state.store (path ++ rest) }

def arrayLengths (state : State) : Bool :=
  arrayLengthsTree state.topology [] state.store (state.store []).permissions.length

/-- Validation is structural only. Matching permission/protector kinds and
scalar access success are deliberately not checked as admission conditions. -/
def access (state : State) (path : Path) (kind : AccessKind)
    (offset size : Nat) : Result Unit State :=
  match findTopology state.topology path with
  | none => .unsupported .invalidPath state
  | some _ =>
    if arrayLengths state then
      if (state.store []).permissions.length < offset + size then .unsupported .range state
      else accessCore state (some path) kind offset size
    else .unsupported .arrayLength state

def releaseTraverse (state : State) (path : Path)
    (accesses : List (Option AccessKind)) : Result Unit State :=
  match findTopology state.topology path with
  | none => .unsupported .invalidPath state
  | some _ =>
    if arrayLengths state then
      if accesses.length = (state.store []).permissions.length then
        releaseCore state (some path) accesses
      else .unsupported .arrayLength state
    else .unsupported .arrayLength state

def unprotectPermissions : List Permission → Option (List Permission × List (Option AccessKind))
  | [] => some ([], [])
  | permission :: rest =>
    match permission.unprotect with
    | none => none
    | some (changed, access) =>
      match unprotectPermissions rest with
      | none => none
      | some (permissions, accesses) => some (changed :: permissions, access :: accesses)

/-- Memory-stage unprotection commits the complete converted permission list,
but keeps the flag. A subsequent dead-allocation branch need not run traversal. -/
def unprotectAt (state : State) (path : Path) : Result (List (Option AccessKind)) State :=
  match findTopology state.topology path with
  | none => .unsupported .invalidPath state
  | some _ =>
    if (state.store path).protection.yes then
      match unprotectPermissions (state.store path).permissions with
      | none => .unsupported .unprotectUnprotected state
      | some (permissions, accesses) =>
        .ok accesses { state with store := setPermissions state.store path permissions }
    else .unsupported .missingProtector state

def stripPrefix : Path → Path → Option Path
  | [], path => some path
  | _ :: _, [] => none
  | expected :: stem, actual :: path =>
    if expected = actual then stripPrefix stem path else none

def addNode (state : State) (parent : Path) (child : State) : Result Path State :=
  match findTopology state.topology parent with
  | none => .unsupported .invalidPath state
  | some (.node children) =>
    match modifyTopology state.topology parent (fun current =>
      match current with | .node old => .node (old.snoc child.topology)) with
    | none => .unsupported .invalidPath state
    | some topology =>
      let path := parent ++ [children.length]
      let store : Store := fun selected =>
        match stripPrefix path selected with
        | none => state.store selected
        | some rest => child.store rest
      .ok path { topology := topology, store := store }

def initialAccessLoop (state : State) (path : Path) (offset index : Nat) :
    List Permission → Result Unit State
  | [] => .ok () state
  | permission :: rest =>
    match permission.initAccess with
    | none => initialAccessLoop state path offset (index + 1) rest
    | some kind =>
      Result.bind (access state path kind (offset + index) 1) fun _ changed =>
        initialAccessLoop changed path offset (index + 1) rest

def initialAccesses (state : State) (path : Path) (offset : Nat)
    (permissions : List Permission) : Result Unit State :=
  initialAccessLoop state path offset 0 permissions

def Result.residual {A S : Type} : Result A S → S
  | .ok _ state => state
  | .ub _ state => state
  | .unsupported _ state => state

theorem nodeRelation_some (path : Path) : nodeRelation (some path) = .localNode := rfl
theorem nodeRelation_none : nodeRelation none = .foreignNode := rfl

theorem childPath_selected (index : Nat) (tail : Path) :
    childPath (some (index :: tail)) index = some tail := by simp [childPath]

theorem transitionOffsets_zero (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset : Nat) :
    transitionOffsets store here kind relation offset 0 = .ok () store := rfl

theorem transitionOffsets_succ (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset count : Nat) :
    transitionOffsets store here kind relation offset (count + 1) =
      Result.bind (transitionAt store here kind relation offset) (fun _ changed =>
        transitionOffsets changed here kind relation (offset + 1) count) := rfl

theorem releaseOffsets_none (store : Store) (here : Path) (relation : NodeRelation)
    (offset : Nat) (rest : List (Option AccessKind)) :
    releaseOffsets store here relation offset (none :: rest) =
      releaseOffsets store here relation (offset + 1) rest := rfl

/-- No matching-kind assertion, permission transition, or descendant visit is
performed at the selected release node, even for arbitrary syntactic entries. -/
theorem releaseTree_selected (topology : Topology) (here : Path) (store : Store)
    (accesses : List (Option AccessKind)) :
    releaseTree topology here store (some []) accesses = .ok () (setProtected store here .no) := by
  cases topology
  rfl

theorem accessCore_topology (state : State) (path : Option Path) (kind : AccessKind)
    (offset size : Nat) :
    (Result.residual (accessCore state path kind offset size)).topology = state.topology := by
  unfold accessCore
  cases accessTree state.topology [] state.store path kind offset size <;> rfl

theorem releaseCore_topology (state : State) (path : Option Path)
    (accesses : List (Option AccessKind)) :
    (Result.residual (releaseCore state path accesses)).topology = state.topology := by
  unfold releaseCore
  cases releaseTree state.topology [] state.store path accesses <;> rfl

theorem unprotectAt_converted (state : State) (path : Path) (topology : Topology)
    (permissions : List Permission) (accesses : List (Option AccessKind))
    (found : findTopology state.topology path = some topology)
    (protection : (state.store path).protection.yes = true)
    (converted : unprotectPermissions (state.store path).permissions = some (permissions, accesses)) :
    unprotectAt state path = .ok accesses
      { state with store := setPermissions state.store path permissions } := by
  simp [unprotectAt, found, protection, converted]

theorem initialAccesses_nil (state : State) (path : Path) (offset : Nat) :
    initialAccesses state path offset [] = .ok () state := rfl

#print axioms nodeRelation_some
#print axioms nodeRelation_none
#print axioms childPath_selected
#print axioms transitionOffsets_zero
#print axioms transitionOffsets_succ
#print axioms releaseOffsets_none
#print axioms releaseTree_selected
#print axioms accessCore_topology
#print axioms releaseCore_topology
#print axioms unprotectAt_converted
#print axioms initialAccesses_nil

end AnnealResearch.TreeFactored
