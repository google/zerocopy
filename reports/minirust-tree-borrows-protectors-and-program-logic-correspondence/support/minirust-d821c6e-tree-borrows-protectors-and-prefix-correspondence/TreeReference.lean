import AnnealResearch.TreePermissions

/-!
An owned recursive reference for the selected MiniRust Node helpers. Ordered
children and per-byte arrays are retained rather than flattened. This file
binds the executable equations in tree.md at MiniRust d821c6e3; in particular,
Some path means Local at ancestors/self, while descendants below the selected
node receive None/Foreign. The nearby source prose uses a different wording.

Ordinary scalar UB retains prior trial changes under the inspected Specr
List.mutate_at callback interpretation. This is NOT the BasicMemory commit
wrapper: that wrapper can discard a failed copied trial allocation. Source
assertion/unreachable/panic inputs are explicitly unsupported, not Rust UB.
No generated-code/helper-adequacy or Rust/whole-language safety claim is made.
-/

namespace AnnealResearch.TreeReference

open TreePermissions

abbrev Path := List Nat

/-- Paths use the nonnegative indices minted by the selected source helpers.
Negative Specr Int indices and malformed host inputs are outside this core. -/
inductive Node where
  | mk (permissions : List Permission) (protection : Protected) (children : List Node)

namespace Node

def permissions : Node → List Permission
  | .mk permissions _ _ => permissions

def protection : Node → Protected
  | .mk _ protection _ => protection

def children : Node → List Node
  | .mk _ _ children => children

end Node

inductive Structural where
  | invalidPath
  | arrayLength
  | range
  | missingProtector
  | unprotectUnprotected
  deriving DecidableEq, Repr

/-- UB and unsupported both retain the explicitly modeled trial state. An
unsupported result specifies no behavior for the corresponding source panic. -/
inductive Result (A S : Type) where
  | ok (value : A) (state : S)
  | ub (fault : Fault) (state : S)
  | unsupported (fault : Structural) (state : S)

namespace Result

def mapState (f : S → T) : Result A S → Result A T
  | .ok value state => .ok value (f state)
  | .ub fault state => .ub fault (f state)
  | .unsupported fault state => .unsupported fault (f state)

def bind (answer : Result A S) (next : A → S → Result B S) : Result B S :=
  match answer with
  | .ok value state => next value state
  | .ub fault state => .ub fault state
  | .unsupported fault state => .unsupported fault state

def state : Result A S → S
  | .ok _ state | .ub _ state | .unsupported _ state => state

end Result

def replaceNth : List A → Nat → A → List A
  | [], _, _ => []
  | _ :: rest, 0, value => value :: rest
  | first :: rest, index + 1, value => first :: replaceNth rest index value

def findNode (node : Node) : Path → Option Node
  | [] => some node
  | index :: rest =>
    match node.children[index]? with
    | none => none
    | some child => findNode child rest

/-- access_node with explicit invalid-path handling. Reconstruction commits the
changed child even when the callback returns an ordinary modeled error. -/
def modifyAt (node : Node) (path : Path) (f : Node → Result A Node) : Result A Node :=
  match path with
  | [] => f node
  | index :: rest =>
    match node with
    | .mk permissions protection children =>
      match children[index]? with
      | none => .unsupported .invalidPath node
      | some child =>
        (modifyAt child rest f).mapState fun changed =>
          .mk permissions protection (replaceNth children index changed)

def nodeRelation : Option Path → NodeRelation
  | none => .foreignNode
  | some _ => .localNode

/-- Executable subpath equation: even when the current node is selected,
its children receive None and hence Foreign. -/
def childPath (path : Option Path) (index : Nat) : Option Path :=
  match path with
  | some (first :: rest) => if first = index then some rest else none
  | _ => none

/-- Process count consecutive bytes from the head; failure leaves the failed
permission and all later bytes unchanged. -/
def transitionPrefix (permissions : List Permission) (count : Nat)
    (kind : AccessKind) (relation : NodeRelation) : Result Unit (List Permission) :=
  match count, permissions with
  | 0, _ => .ok () permissions
  | _ + 1, [] => .unsupported .range []
  | count + 1, permission :: rest =>
    match permission.transition kind relation with
    | .error fault => .ub fault (permission :: rest)
    | .ok changed =>
      (transitionPrefix rest count kind relation).mapState (changed :: ·)

def transitionRange (permissions : List Permission) (offset size : Nat)
    (kind : AccessKind) (relation : NodeRelation) : Result Unit (List Permission) :=
  match offset, permissions with
  | 0, _ => transitionPrefix permissions size kind relation
  | _ + 1, [] => if size = 0 then .ok () [] else .unsupported .range []
  | offset + 1, permission :: rest =>
    (transitionRange rest offset size kind relation).mapState (permission :: ·)

/-- The release walk visits every access-list offset in order. The selected
structural domain uses equal allocation-sized arrays, even for None entries. -/
def applyAccesses (permissions : List Permission) (accesses : List (Option AccessKind))
    (relation : NodeRelation) : Result Unit (List Permission) :=
  match permissions, accesses with
  | [], [] => .ok () []
  | [], _ :: _ => .unsupported .arrayLength []
  | _ :: _, [] => .unsupported .arrayLength permissions
  | permission :: rest, access :: more =>
    match access with
    | none => (applyAccesses rest more relation).mapState (permission :: ·)
    | some kind =>
      match permission.transition kind relation with
      | .error fault => .ub fault permissions
      | .ok changed => (applyAccesses rest more relation).mapState (changed :: ·)

mutual
  /-- Raw current-node-before-children traversal. No flag/kind compatibility
  guard is inserted: constructor mismatches remain representable states. -/
  def accessCore (node : Node) (path : Option Path) (kind : AccessKind)
      (offset size : Nat) : Result Unit Node :=
    match node with
    | .mk permissions protection children =>
      match transitionRange permissions offset size kind (nodeRelation path) with
      | .ok () changed =>
        (accessChildren children path kind offset size 0).mapState fun nextChildren =>
          .mk changed protection nextChildren
      | .ub fault changed => .ub fault (.mk changed protection children)
      | .unsupported fault changed => .unsupported fault (.mk changed protection children)
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  /-- The index is the original ordered child index, including after earlier
  successful children; a failing child retains its own partial trial state. -/
  def accessChildren (children : List Node) (path : Option Path) (kind : AccessKind)
      (offset size index : Nat) : Result Unit (List Node) :=
    match children with
    | [] => .ok () []
    | child :: rest =>
      match accessCore child (childPath path index) kind offset size with
      | .ok () changed =>
        (accessChildren rest path kind offset size (index + 1)).mapState (changed :: ·)
      | .ub fault changed => .ub fault (changed :: rest)
      | .unsupported fault changed => .unsupported fault (changed :: rest)
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  /-- Plain Node.release_protector only. Some [] clears the flag and returns,
  without an assertion, unprotect conversion, current transition or child walk.
  The Memory wrapper's distinct conversion stage is unprotectAt below. -/
  def releaseCore (node : Node) (path : Option Path)
      (accesses : List (Option AccessKind)) : Result Unit Node :=
    match node with
    | .mk permissions protection children =>
      match path with
      | some [] => .ok () (.mk permissions .no children)
      | _ =>
        match applyAccesses permissions accesses (nodeRelation path) with
        | .ok () changed =>
          (releaseChildren children path accesses 0).mapState fun nextChildren =>
            .mk changed protection nextChildren
        | .ub fault changed => .ub fault (.mk changed protection children)
        | .unsupported fault changed => .unsupported fault (.mk changed protection children)
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  def releaseChildren (children : List Node) (path : Option Path)
      (accesses : List (Option AccessKind)) (index : Nat) : Result Unit (List Node) :=
    match children with
    | [] => .ok () []
    | child :: rest =>
      match releaseCore child (childPath path index) accesses with
      | .ok () changed =>
        (releaseChildren rest path accesses (index + 1)).mapState (changed :: ·)
      | .ub fault changed => .ub fault (changed :: rest)
      | .unsupported fault changed => .unsupported fault (changed :: rest)
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  /-- Structural array admission only; it asserts neither constructor matching
  nor access success, liveness, absence of UB, or a frame-list correspondence. -/
  def arraysSized (node : Node) (size : Nat) : Bool :=
    match node with
    | .mk permissions _ children =>
      (permissions.length == size) && childrenSized children size
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  def childrenSized (children : List Node) (size : Nat) : Bool :=
    match children with
    | [] => true
    | child :: rest => arraysSized child size && childrenSized rest size
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  /-- A separate invariant predicate, deliberately never an execution guard. -/
  def kindsMatch (node : Node) : Bool :=
    match node with
    | .mk permissions protection children =>
      permissions.all (·.matchesProtector protection) && childrenMatch children
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  def childrenMatch (children : List Node) : Bool :=
    match children with
    | [] => true
    | child :: rest => kindsMatch child && childrenMatch rest
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  /-- Recursive Strong search, with no invented compatibility check. -/
  def containsStrong (node : Node) : Bool :=
    match node with
    | .mk permissions protection children =>
      (decide (protection = .strong) && permissions.any Permission.preventsDeallocation) ||
        childrenContainStrong children
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  def childrenContainStrong (children : List Node) : Bool :=
    match children with
    | [] => false
    | child :: rest => containsStrong child || childrenContainStrong rest
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

def pathPresent (node : Node) : Option Path → Bool
  | none => true
  | some path => (findNode node path).isSome

/-- Public structural boundary. Raw accessCore is also exposed so a later
operation wrapper can state the preconditions separately from execution. -/
def access (node : Node) (path : Option Path) (kind : AccessKind)
    (offset size : Nat) : Result Unit Node :=
  if !arraysSized node node.permissions.length then .unsupported .arrayLength node
  else if !pathPresent node path then .unsupported .invalidPath node
  else if offset + size > node.permissions.length then .unsupported .range node
  else accessCore node path kind offset size

/-- Equal-length admission is an owned structural domain restriction, including
the selected-node case where the raw source walk would not inspect the arrays. -/
def releaseTraverse (node : Node) (path : Option Path)
    (accesses : List (Option AccessKind)) : Result Unit Node :=
  if !arraysSized node accesses.length then .unsupported .arrayLength node
  else if !pathPresent node path then .unsupported .invalidPath node
  else releaseCore node path accesses

/-- Source map/unzip stage, before assignment to the selected node. If a source
unreachable Unprot constructor is found, this owned helper reports unsupported;
no partial map is assigned to the node and no source panic behavior is claimed. -/
def unprotectPermissions : List Permission →
    Except Structural (List Permission × List (Option AccessKind))
  | [] => .ok ([], [])
  | permission :: rest =>
    match permission.unprotect with
    | none => .error .unprotectUnprotected
    | some (changed, accessKind) =>
      match unprotectPermissions rest with
      | .error fault => .error fault
      | .ok (changedRest, accesses) => .ok (changed :: changedRest, accessKind :: accesses)

/-- Only the selected Memory.release_protector assertion and unprotect stage.
It intentionally leaves the flag unchanged. The later live/dead branch and
outer allocation mutation are absent from this node-only core. -/
def unprotectAt (node : Node) (path : Path) : Result (List (Option AccessKind)) Node :=
  modifyAt node path fun selected =>
    match selected with
    | .mk permissions protection children =>
      if !protection.yes then .unsupported .missingProtector selected
      else match unprotectPermissions permissions with
      | .error fault => .unsupported fault selected
      | .ok (changed, accesses) => .ok accesses (.mk changed protection children)

/-- Add at the source's next child index. Uniform allocation-size admission is
separate from protector compatibility and from the later initial accesses. -/
def addNode (node : Node) (parentPath : Path) (child : Node) : Result Path Node :=
  let size := node.permissions.length
  if !arraysSized node size || !arraysSized child size then .unsupported .arrayLength node
  else modifyAt node parentPath fun parent =>
    match parent with
    | .mk permissions protection children =>
      .ok (parentPath ++ [children.length]) (.mk permissions protection (children ++ [child]))

/-- Process the original reborrow inside-permission list in order; these are
settings, not permissions re-read after each changing tree access. -/
def initialAccesses (node : Node) (path : Path) (offset : Nat)
    (inside : List Permission) : Result Unit Node :=
  match inside with
  | [] => .ok () node
  | permission :: rest =>
    match permission.initAccess with
    | none => initialAccesses node path (offset + 1) rest
    | some kind =>
      (access node (some path) kind offset 1).bind fun () changed =>
        initialAccesses changed path (offset + 1) rest

/-! Small equation and residual controls for the core. These arbitrary owned
trees are not claimed to have been constructed by full source reborrows. -/

theorem find_root (node : Node) : findNode node [] = some node := rfl

theorem modify_root (node : Node) (f : Node → Result A Node) :
    modifyAt node [] f = f node := rfl

theorem selected_children_are_foreign (index : Nat) : childPath (some []) index = none := rfl

theorem selected_path_ancestor_is_local (path : Path) :
    nodeRelation (some path) = .localNode := rfl

theorem release_selected_stops (permissions : List Permission) (protection : Protected)
    (children : List Node) (accesses : List (Option AccessKind)) :
    releaseCore (.mk permissions protection children) (some []) accesses =
      .ok () (.mk permissions .no children) := by
  simp only [releaseCore]

theorem release_no_flag_assert (permissions : List Permission) (children : List Node)
    (accesses : List (Option AccessKind)) :
    releaseCore (.mk permissions .no children) (some []) accesses =
      .ok () (.mk permissions .no children) := release_selected_stops _ _ _ _

theorem unprotect_then_flag_still_set :
    unprotectAt (.mk [.prot (.reserved true false)] .strong []) [] =
      .ok [some .read] (.mk [.unprot .reserved] .strong []) := rfl

theorem unprotect_no_flag_unsupported :
    unprotectAt (.mk [.unprot .reserved] .no []) [] =
      .unsupported .missingProtector (.mk [.unprot .reserved] .no []) := rfl

theorem unprotect_unprot_unsupported :
    unprotectAt (.mk [.unprot .reserved] .weak []) [] =
      .unsupported .unprotectUnprotected (.mk [.unprot .reserved] .weak []) := rfl

theorem byte_prefix_failure_retains_prior_change :
    transitionPrefix [.unprot .reserved, .unprot .frozen, .unprot .reserved] 3
      .write .localNode =
      .ub .unprotectedLocalWriteFrozen
        [.unprot .unique, .unprot .frozen, .unprot .reserved] := rfl

theorem release_access_prefix_failure_retains_prior_change :
    applyAccesses [.prot (.reserved false false), .prot .unique]
      [some .read, some .read] .foreignNode =
      .ub .protectedForeignReadUnique
        [.prot (.reserved false true), .prot .unique] := rfl

/-- Root and the earlier sibling change before the later sibling fails; the
last sibling is not visited. This is the raw trial tree, before any enclosing
BasicMemory copied-allocation commit policy. -/
theorem ordered_children_failure_retains_trial :
    accessCore
      (.mk [.unprot .unique] .no
        [.mk [.unprot .unique] .no [], .mk [.prot .unique] .strong [],
          .mk [.unprot .unique] .no []])
      none .read 0 1 =
    .ub .protectedForeignReadUnique
      (.mk [.unprot .frozen] .no
        [.mk [.unprot .frozen] .no [], .mk [.prot .unique] .strong [],
          .mk [.unprot .unique] .no []]) := by
  simp [accessCore, accessChildren, transitionRange, transitionPrefix, nodeRelation,
    childPath, Permission.transition, UPermission.transition, UPermission.foreignRead,
    PPermission.transition, PPermission.foreignRead, Result.mapState]

/-- An owned shape-level control only: actual source-style node creation and
initial accesses are separate later witnesses. Ancestors and T are Local;
off-path B is Foreign and is disabled by the write. -/
theorem path_write_visits_grandchild_and_sibling :
    accessCore
      (.mk [.unprot .unique] .no
        [.mk [.unprot .reserved] .no
          [.mk [.prot (.reserved true false)] .strong []],
          .mk [.unprot .reserved] .no []])
      (some [0, 0]) .write 0 1 =
    .ok ()
      (.mk [.unprot .unique] .no
        [.mk [.unprot .unique] .no [.mk [.prot .unique] .strong []],
          .mk [.unprot .disabled] .no []]) := by
  simp [accessCore, accessChildren, transitionRange, transitionPrefix, nodeRelation,
    childPath, Permission.transition, UPermission.transition, UPermission.localWrite,
    UPermission.foreignWrite, PPermission.transition, PPermission.localWrite,
    Result.mapState]

theorem absent_path_is_structural :
    access (.mk [.unprot .unique] .no []) (some [0]) .read 0 1 =
      .unsupported .invalidPath (.mk [.unprot .unique] .no []) := by
  simp [access, arraysSized, childrenSized, pathPresent, findNode, Node.permissions,
    Node.children]

theorem mixed_lengths_are_structural :
    access (.mk [.unprot .unique] .no [.mk [] .no []]) (some []) .read 0 1 =
      .unsupported .arrayLength (.mk [.unprot .unique] .no [.mk [] .no []]) := by
  simp [access, arraysSized, childrenSized, Node.permissions]

/-- A mismatched Strong flag is represented and executed, not filtered away. -/
theorem compatibility_is_not_an_access_guard :
    access (.mk [.unprot .reserved] .strong []) (some []) .write 0 1 =
      .ok () (.mk [.unprot .unique] .strong []) := by
  simp [access, arraysSized, childrenSized, pathPresent, findNode, Node.permissions,
    accessCore, accessChildren, transitionRange, transitionPrefix, nodeRelation,
    Permission.transition, UPermission.transition, UPermission.localWrite, Result.mapState]

theorem strong_search_reaches_grandchild :
    containsStrong
      (.mk [.unprot .unique] .no
        [.mk [.unprot .reserved] .no
          [.mk [.prot .unique] .strong []], .mk [.unprot .disabled] .no []]) = true := by
  simp [containsStrong, childrenContainStrong, Permission.preventsDeallocation,
    PPermission.preventsDeallocation, UPermission.preventsDeallocation]

theorem weak_unique_does_not_block :
    containsStrong (.mk [.prot .unique] .weak []) = false := by
  simp [containsStrong, childrenContainStrong]

theorem strong_cell_and_empty_do_not_block :
    containsStrong (.mk [.prot .cell] .strong []) = false ∧
    containsStrong (.mk [] .strong []) = false := by
  simp [containsStrong, childrenContainStrong, Permission.preventsDeallocation,
    PPermission.preventsDeallocation]

theorem empty_array_matching_is_vacuous (protection : Protected) :
    kindsMatch (.mk [] protection []) = true := by
  simp [kindsMatch, childrenMatch]

#print axioms find_root
#print axioms modify_root
#print axioms selected_children_are_foreign
#print axioms selected_path_ancestor_is_local
#print axioms release_selected_stops
#print axioms release_no_flag_assert
#print axioms unprotect_then_flag_still_set
#print axioms unprotect_no_flag_unsupported
#print axioms unprotect_unprot_unsupported
#print axioms byte_prefix_failure_retains_prior_change
#print axioms release_access_prefix_failure_retains_prior_change
#print axioms ordered_children_failure_retains_trial
#print axioms path_write_visits_grandchild_and_sibling
#print axioms absent_path_is_structural
#print axioms mixed_lengths_are_structural
#print axioms compatibility_is_not_an_access_guard
#print axioms strong_search_reaches_grandchild
#print axioms weak_unique_does_not_block
#print axioms strong_cell_and_empty_do_not_block
#print axioms empty_array_matching_is_vacuous

end AnnealResearch.TreeReference
