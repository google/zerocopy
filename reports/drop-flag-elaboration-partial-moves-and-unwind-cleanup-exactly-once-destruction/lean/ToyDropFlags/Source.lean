import ToyDropFlags.Basic

/-!
# Source CFG language, initialization analyses, move checker

A source program is a list of nodes; node `0` is the entry. Nodes are single instructions with
explicit successors. Calls have a normal successor and a cleanup (unwind) successor. Scope exits
are the `ret` (normal return) and `resume` (continue unwinding) terminators, at which every
still-owned part of every local must be destroyed; the source language has no explicit drops,
so `ret` and `resume` are the **drop points** that elaboration resolves.

The may-init and must-init analyses are forward dataflow analyses over atoms, computed in one
pass in node order. The pass only follows *index-increasing* edges `i → j` with `i < j`; on a
*forward* program (`Forward`: every edge goes to a larger, in-range node index, so the CFG is
acyclic and node order is a topological order) these are all edges, and the analyses and
`ForwardReachable` coincide with their path-based meaning. On other programs they describe
index-increasing paths only. Nodes not forward-reachable get must-init = all atoms (top) and
may-init = no atoms (bottom), as in a standard dataflow initialisation.
-/

namespace Toy.DropFlags

/-- Source instructions. `init p` writes a fresh value into `p`; `move p` hands the value in `p`
to a consumer (a sink that cannot panic); `call args dest` hands the values in `args` to a
callee, which may panic; on normal return it writes a fresh value into `dest`. `branch` is a
choice made by the environment. -/
inductive SNode where
  | init (p : Place) (next : Nat)
  | move (p : Place) (next : Nat)
  | branch (l₁ l₂ : Nat)
  | call (args : List Place) (dest : Option Place) (next unwind : Nat)
  | ret
  | resume
  | abort
  deriving DecidableEq, Repr

/-- A source program: its locals (with their types) and its nodes; node `0` is the entry. -/
structure SProg where
  locals : List Ty
  nodes : List SNode
  deriving DecidableEq, Repr

/-- The node at index `i` (`abort` when out of range). -/
def SProg.node (s : SProg) (i : Nat) : SNode := s.nodes.getD i .abort

/-- Normal-flow successors and unwind successors of a node. -/
def SNode.succs : SNode → List Nat
  | .init _ n | .move _ n => [n]
  | .branch a b => [a, b]
  | .call _ _ n u => [n, u]
  | _ => []

/-- **Forward**: the program is non-empty and every edge goes to a strictly larger, in-range
node index. This makes the CFG acyclic. -/
def Forward (s : SProg) : Prop :=
  0 < s.nodes.length ∧
  ∀ i < s.nodes.length, ∀ j ∈ (s.node i).succs, i < j ∧ j < s.nodes.length

instance (s : SProg) : Decidable (Forward s) := by unfold Forward; exact inferInstance

/-! ## Initialization analyses -/

/-- Granularity of initialization tracking. `fine`: per atom (what the elaboration must use).
`wholeKill`: a move of any part of a local is tracked as a move of the whole local.
`wholeKeep`: a move of a proper part of a local is not tracked at all (only whole-local moves
are). Initializations are tracked per atom in all modes. -/
inductive Granularity where
  | fine
  | wholeKill
  | wholeKeep
  deriving DecidableEq, Repr

/-- Atoms whose tracked state a move of `p` clears, at granularity `g`. -/
def killSet (ls : List Ty) (g : Granularity) (p : Place) : List Place :=
  match g with
  | .fine => atomsOf ls p
  | .wholeKill => atomsOf ls ⟨p.loc, []⟩
  | .wholeKeep => if p.path = [] then atomsOf ls p else []

/-- Set difference on atom lists. -/
def minus (s k : List Place) : List Place := s.filter (fun a => !k.contains a)

/-- Edge transfer: the successor indices of node `n` paired with the tracked initialized-atom set
on that edge, given the set `s` on entry to `n`. A call's arguments are moved out on both its
normal and its unwind edge; its destination is initialized only on the normal edge. -/
def edgeOut (ls : List Ty) (g : Granularity) (n : SNode) (s : List Place) :
    List (Nat × List Place) :=
  match n with
  | .init p nx => [(nx, s ++ atomsOf ls p)]
  | .move p nx => [(nx, minus s (killSet ls g p))]
  | .branch a b => [(a, s), (b, s)]
  | .call args dest nx un =>
      let s' := minus s (args.flatMap (killSet ls g))
      [(nx, s' ++ (match dest with | some d => atomsOf ls d | none => [])), (un, s')]
  | _ => []

/-- One pass in node order: node `j` is marked if it is the entry or some marked node `i < j`
has `j` among its successors (normal or unwind). -/
def reachableAux (s : SProg) : Nat → List Bool → List Bool
  | 0, acc => acc
  | k + 1, acc =>
      let j := acc.length
      let r := j = 0 ||
        (List.range j).any fun i => acc.getD i false && (s.node i).succs.contains j
      reachableAux s k (acc ++ [r])

/-- Reachability flags of all nodes, in node order. -/
def reachList (s : SProg) : List Bool := reachableAux s s.nodes.length []

/-- **ForwardReachable**: node `j` is reachable from the entry along a path of *index-increasing*
edges (normal or unwind). For a forward program (`Forward s`) every edge is index-increasing, so
this is ordinary CFG reachability; for other programs it may miss nodes reachable only through
an edge `i → j` with `j ≤ i`. -/
def ForwardReachable (s : SProg) (j : Nat) : Bool := (reachList s).getD j false

/-- The sets flowing into node `j` along edges from forward-reachable nodes `i < j`, given the in-sets
`prev` of nodes `0 … j-1`. Unreachable nodes do not propagate (as in a worklist analysis
seeded at the entry). -/
def flowIn (s : SProg) (g : Granularity) (reach : List Bool) (j : Nat)
    (prev : List (List Place)) : List (List Place) :=
  (List.range j).flatMap fun i =>
    if reach.getD i false then
      ((edgeOut s.locals g (s.node i) (prev.getD i [])).filter (·.1 == j)).map (·.2)
    else []

/-- One forward pass. `may = true`: may-init (join = union, unreachable = no atoms).
`may = false`: must-init (join = intersection, unreachable = all atoms). Entry: no atoms. -/
def analysisAux (s : SProg) (g : Granularity) (may : Bool) (reach : List Bool) :
    Nat → List (List Place) → List (List Place)
  | 0, acc => acc
  | k + 1, acc =>
      let j := acc.length
      let ins := flowIn s g reach j acc
      let here : List Place :=
        if j = 0 then []
        else match ins with
          | [] => if may then [] else allAtoms s.locals
          | x :: xs =>
              if may then xs.foldl (· ++ ·) x
              else xs.foldl (fun acc' y => acc'.filter (y.contains ·)) x
      analysisAux s g may reach k (acc ++ [here])

/-- In-sets of all nodes for the chosen analysis. -/
def analysis (s : SProg) (g : Granularity) (may : Bool) : List (List Place) :=
  analysisAux s g may (reachList s) s.nodes.length []

/-- `mayInit s g j a`: the one-pass may-init analysis at granularity `g` contains atom `a` on
entry to node `j`. On a forward program this means: on some path from the entry to node `j`,
`a` is initialized on arrival. In general it describes index-increasing paths only. -/
def mayInit (s : SProg) (g : Granularity) (j : Nat) (a : Place) : Bool :=
  ((analysis s g true).getD j []).contains a

/-- `mustInit s g j a`: the one-pass must-init analysis at granularity `g` contains atom `a` on
entry to node `j`. On a forward program this means: on every path from the entry to node `j`,
`a` is initialized on arrival (vacuously true at nodes that are not forward-reachable). In
general it describes index-increasing paths only. -/
def mustInit (s : SProg) (g : Granularity) (j : Nat) (a : Place) : Bool :=
  ((analysis s g false).getD j (allAtoms s.locals)).contains a


/-! ## Move checker

Each component is a separate named property, so results can name the ones they use. All use
the fine-grained analyses. -/

/-- Places mentioned by a node (moved, initialized, call arguments and destination). -/
def SNode.places : SNode → List Place
  | .init p _ | .move p _ => [p]
  | .call args dest _ _ => args ++ dest.toList
  | _ => []

/-- **PlacesAreMovePaths**: every place mentioned is a valid move path of its local: it follows
the local's type and does not enter a struct that has its own destructor. In particular nothing
is moved out of (or initialized inside) a struct with a destructor. -/
def PlacesAreMovePaths (s : SProg) : Prop :=
  ∀ i < s.nodes.length, ∀ p ∈ (s.node i).places, isMovePlace s.locals p = true

/-- Pairwise non-overlap of a list of places. -/
def pairwiseDisjoint : List Place → Bool
  | [] => true
  | p :: ps => ps.all (fun q => !p.overlaps q) && pairwiseDisjoint ps

/-- **MovesFromInit** ("no use after move"): at every `move p` and every call, each moved place
is definitely initialized (all its atoms are must-init), and the arguments of a call are
pairwise disjoint (no value is handed to the callee twice). -/
def MovesFromInit (s : SProg) : Prop :=
  ∀ i < s.nodes.length,
    match s.node i with
    | .move p _ => ∀ a ∈ atomsOf s.locals p, mustInit s .fine i a = true
    | .call args _ _ _ =>
        (∀ p ∈ args, ∀ a ∈ atomsOf s.locals p, mustInit s .fine i a = true) ∧
        pairwiseDisjoint args = true
    | _ => True

/-- **InitsIntoUninit** ("no overwrite of an owned value"): at every `init p`, each atom of `p`
is definitely uninitialized (not may-init); at every call with a destination, each atom of the
destination is definitely uninitialized once the arguments have been moved out. -/
def InitsIntoUninit (s : SProg) : Prop :=
  ∀ i < s.nodes.length,
    match s.node i with
    | .init p _ => ∀ a ∈ atomsOf s.locals p, mayInit s .fine i a = false
    | .call args (some d) _ _ =>
        ∀ a ∈ atomsOf s.locals d,
          mayInit s .fine i a = false ∨ (args.any fun q => q.overlaps a) = true
    | _ => True

/-- Normal-flow successors of a node (a call's unwind successor is excluded). -/
def SNode.normalSuccs : SNode → List Nat
  | .init _ n | .move _ n => [n]
  | .branch a b => [a, b]
  | .call _ _ n _ => [n]
  | _ => []

/-- One pass in node order over normal edges only: node `j` is marked if it is the entry or some
marked node `i < j` has `j` among its normal successors. -/
def normalReachAux (s : SProg) : Nat → List Bool → List Bool
  | 0, acc => acc
  | k + 1, acc =>
      let j := acc.length
      let r := j = 0 ||
        (List.range j).any fun i => acc.getD i false && (s.node i).normalSuccs.contains j
      normalReachAux s k (acc ++ [r])

/-- `NormalReachable s j`: node `j` is reachable from the entry along index-increasing *normal*
edges only (no call's unwind edge is taken). On a forward program: reachable without any panic. -/
def NormalReachable (s : SProg) (j : Nat) : Bool := (normalReachAux s s.nodes.length []).getD j false

/-- **NoNormalPathToResume**: no `resume` node is reachable from the entry along normal edges
only, so (on a forward program) every path to a `resume` node takes at least one call's unwind
edge and a `resume` ladder runs only while unwinding. Unwind edges may lead to arbitrary cleanup
code (several nodes, branches, moves, calls, merges with normal code) before a `resume`. It is meant
to capture MIR's rule that cleanup blocks are entered only by unwinding. -/
def NoNormalPathToResume (s : SProg) : Prop :=
  ∀ i < s.nodes.length, NormalReachable s i = true → s.node i ≠ .resume

instance (s : SProg) : Decidable (PlacesAreMovePaths s) := by
  unfold PlacesAreMovePaths; exact inferInstance

instance (s : SProg) : Decidable (MovesFromInit s) := by
  unfold MovesFromInit
  refine @Nat.decidableBallLT _ _ (fun i _ => ?_)
  split <;> exact inferInstance

instance (s : SProg) : Decidable (InitsIntoUninit s) := by
  unfold InitsIntoUninit
  refine @Nat.decidableBallLT _ _ (fun i _ => ?_)
  split <;> exact inferInstance

instance (s : SProg) : Decidable (NoNormalPathToResume s) := by
  unfold NoNormalPathToResume; exact inferInstance

/-- The move checker: the conjunction of the three move-checking components. -/
def MoveChecked (s : SProg) : Prop :=
  PlacesAreMovePaths s ∧ MovesFromInit s ∧ InitsIntoUninit s

instance (s : SProg) : Decidable (MoveChecked s) := by unfold MoveChecked; exact inferInstance

end Toy.DropFlags
