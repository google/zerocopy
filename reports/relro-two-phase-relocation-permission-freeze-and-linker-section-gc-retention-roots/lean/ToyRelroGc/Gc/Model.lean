/-
Toy model of linker section garbage collection (`--gc-sections`) and of compiler-then-linker
retention of statics. It is a toy: it neither establishes nor refutes claims about any real
linker or compiler.
-/
namespace Toy.RelroGc

/-- Reachability in a directed graph with edge list `E` from the nodes satisfying `R`. -/
inductive Reach (E : List (Nat × Nat)) (R : Nat → Prop) : Nat → Prop where
  | root {i : Nat} : R i → Reach E R i
  | step {i j : Nat} : Reach E R i → (i, j) ∈ E → Reach E R j

/-- Attributes of an input section. `name` stands for the section name (the `X` of
`__start_X`/`__stop_X`), as a number. The root classes: `entry` (holds the entry symbol),
`exported` (defines a symbol that must stay visible, e.g. referenced by a dynamic object),
`keep` (matched by a `KEEP` pattern in the linker script), `retain` (carries the ELF
`SHF_GNU_RETAIN` flag). -/
structure Sec where
  name : Nat
  entry : Bool
  exported : Bool
  keep : Bool
  retain : Bool
  deriving DecidableEq, Repr

/-- The section belongs to at least one root class. -/
def Sec.isRoot (s : Sec) : Bool := s.entry || s.exported || s.keep || s.retain

/-- A GC input: sections `0 .. secs.length - 1`; relocation edges `(i, j)` (section `i`
references section `j`); start/stop references `(i, X)` (section `i` references `__start_X`
or `__stop_X`). Edge and reference endpoints are not required to be `< secs.length`: an index
past the end names no section, is never a root and has no name, but it can still be reached
along a dangling edge (`phantom_section_live`). -/
structure GcIn where
  secs : List Sec
  edges : List (Nat × Nat)
  ss : List (Nat × Nat)

/-- Treatment of start/stop references: `conservative` keeps every section named `X` when a
live section references `__start_X`/`__stop_X`; `precise` gives such references no retaining
effect. -/
inductive SSPolicy where
  | conservative
  | precise
  deriving DecidableEq, Repr

/-- Section `i` exists and belongs to a root class (Boolean form). -/
def GcIn.isRootB (g : GcIn) (i : Nat) : Bool :=
  match g.secs[i]? with
  | some s => s.isRoot
  | none => false

/-- Section `i` exists and belongs to a root class. -/
def GcIn.IsRoot (g : GcIn) (i : Nat) : Prop := g.isRootB i = true

/-- The name of section `i`, if it exists. -/
def GcIn.nameOf (g : GcIn) (i : Nat) : Option Nat := (g.secs[i]?).map Sec.name

/-- The edges contributed by start/stop references under a policy: under `conservative`, an
edge from `i` to every section named `X`, for each `(i, X) ∈ ss`; under `precise`, none. -/
def GcIn.ssEdges (g : GcIn) : SSPolicy → List (Nat × Nat)
  | .conservative => g.ss.flatMap fun e =>
      ((List.range g.secs.length).filter fun j => g.nameOf j == some e.2).map fun j => (e.1, j)
  | .precise => []

/-- The sections `--gc-sections` keeps under a policy: those reachable from the roots along
relocation edges and start/stop edges. -/
def GcIn.Live (g : GcIn) (pol : SSPolicy) : Nat → Prop := Reach (g.edges ++ g.ssEdges pol) g.IsRoot

/-! ### Runs and access completeness -/

/-- A runtime access to a section, classified by how the program obtains the address. The
classification describes the program, not the GC policy, so one run is encoded the same way
under both start/stop policies.
* `edge i j`: section `i` uses an address of section `j` that a relocation of `i` supplies
  (a relocation edge `(i, j)`).
* `bounds i X j`: section `i` iterates from `__start_X` to `__stop_X` and reaches section `j`,
  which is named `X`.
* `implicit j`: an address of section `j` that the linker cannot see (computed at run time, or
  supplied by neither a relocation nor a start/stop reference). -/
inductive Acc where
  | edge (i j : Nat)
  | bounds (i X j : Nat)
  | implicit (j : Nat)
  deriving DecidableEq, Repr

/-- The section an access reaches. -/
def Acc.dst : Acc → Nat
  | .edge _ j => j
  | .bounds _ _ j => j
  | .implicit j => j

/-- Section `i` is a root or was reached by an access of `run` before position `k`. -/
def ReachedBefore (R : Nat → Prop) (run : List Acc) (k i : Nat) : Prop :=
  R i ∨ ∃ k' < k, ∃ a : Acc, run[k']? = some a ∧ a.dst = i

/-- (A1) Every edge access follows an edge of `E` from a section that is a root or was reached
by an earlier access of the run. -/
def EdgeAccessesFollowEdges (E : List (Nat × Nat)) (R : Nat → Prop) (run : List Acc) : Prop :=
  ∀ k i j : Nat, run[k]? = some (Acc.edge i j) → (i, j) ∈ E ∧ ReachedBefore R run k i

/-- (A2) Every implicit access reaches a root. -/
def ImplicitAccessesHitRoots (R : Nat → Prop) (run : List Acc) : Prop :=
  ∀ k j : Nat, run[k]? = some (Acc.implicit j) → R j

/-- (A3) Every bounds access `bounds i X j` comes from a section `i` that references the bounds
of `X` (`(i, X) ∈ g.ss`) and is a root or was reached earlier in the run, reaches a section `j`
named `X`, and the start/stop rule retains `j`: the policy is conservative, or `j` is a root. -/
def BoundsAccessesRetained (g : GcIn) (pol : SSPolicy) (run : List Acc) : Prop :=
  ∀ k i X j : Nat, run[k]? = some (Acc.bounds i X j) →
    (i, X) ∈ g.ss ∧ g.nameOf j = some X ∧ ReachedBefore g.IsRoot run k i ∧
      (pol = .conservative ∨ g.IsRoot j)

/-- GC preserves a run: every section the run accesses is kept. -/
def RunPreserved (g : GcIn) (pol : SSPolicy) (run : List Acc) : Prop :=
  ∀ a ∈ run, g.Live pol a.dst

/-! ### Section granularity -/

/-- Section-level edges induced by item-level references `E` and an assignment `sec` of items
(functions, objects or bytes) to sections. -/
def secEdges (sec : Nat → Nat) (E : List (Nat × Nat)) : List (Nat × Nat) :=
  E.map fun e => (sec e.1, sec e.2)

/-- Section-level roots: sections containing a root item. -/
def secRoot (sec : Nat → Nat) (R : Nat → Prop) : Nat → Prop := fun s => ∃ i, R i ∧ sec i = s

/-- Item `i` is kept: its section is reachable at section granularity. -/
def KeptItem (sec : Nat → Nat) (E : List (Nat × Nat)) (R : Nat → Prop) (i : Nat) : Prop :=
  Reach (secEdges sec E) (secRoot sec R) (sec i)

/-! ### Start/stop registries -/

/-- Every section named `X` is kept. -/
def RegistryKept (g : GcIn) (pol : SSPolicy) (X : Nat) : Prop :=
  ∀ j, g.nameOf j = some X → g.Live pol j

/-- The run in which section `i` iterates from `__start_X` to `__stop_X` and reaches every
section named `X`, in index order. -/
def registryScan (g : GcIn) (i X : Nat) : List Acc :=
  ((List.range g.secs.length).filter fun j => g.nameOf j == some X).map (Acc.bounds i X)

/-- A kept section references `__start_X`/`__stop_X` but no section named `X` is kept; the
toy treats this as a link failure (the bounds symbols are not synthesized). -/
def StartStopUndefined (g : GcIn) (pol : SSPolicy) (X : Nat) : Prop :=
  (∃ i, g.Live pol i ∧ (i, X) ∈ g.ss) ∧ ∀ j, g.nameOf j = some X → ¬ g.Live pol j

/-- No relocation edge reaches a section named `X` (its sections are reached at run time only
through the bounds symbols). -/
def NoEdgeIntoName (g : GcIn) (X : Nat) : Prop := ∀ e ∈ g.edges, g.nameOf e.2 ≠ some X

/-! ### Compiler-then-linker retention -/

/-- A static as seen by the two stages. `cref`: some code the compiler keeps refers to it.
`cused`: it is in the compiler-used set (a compiler-level "used" mark). `retain`: its output
section carries the retain flag. `lroot`: its section is a link root by another class (entry,
exported, `KEEP`). The four flags are independent: the model does not derive one from another. -/
structure Static where
  cref : Bool
  cused : Bool
  retain : Bool
  lroot : Bool
  deriving DecidableEq, Repr

/-- A program: statics, each emitted into its own input section (as with data sections), and
link-time relocation edges between those sections. -/
structure Prog2 where
  statics : List Static
  ledges : List (Nat × Nat)

/-- The compiler stage keeps a static iff it is referenced at compile time or compiler-used. -/
def compileKeeps (s : Static) : Bool := s.cref || s.cused

/-- Static `i` exists and survives the compiler stage. -/
def Prog2.compiled (p : Prog2) (i : Nat) : Bool :=
  match p.statics[i]? with
  | some s => compileKeeps s
  | none => false

/-- The relocation edges of the object the linker sees: those between surviving statics. -/
def Prog2.objEdges (p : Prog2) : List (Nat × Nat) :=
  p.ledges.filter fun e => p.compiled e.1 && p.compiled e.2

/-- The link roots of that object: surviving statics whose section is a link root or retained. -/
def Prog2.objRoot (p : Prog2) (i : Nat) : Prop :=
  p.compiled i = true ∧ ∃ s, p.statics[i]? = some s ∧ (s.lroot || s.retain) = true

/-- Link-time reachability, evaluated on the object the compiler produced. -/
def Prog2.LinkReach (p : Prog2) (i : Nat) : Prop := Reach p.objEdges p.objRoot i

/-- End-to-end survival: the compiler emits static `i` and linker GC keeps its section. -/
def Prog2.Survives (p : Prog2) (i : Nat) : Prop := p.compiled i = true ∧ p.LinkReach i

/-- A path in the source-level link graph `p.ledges` that starts at a static whose section is a
link root or retained and visits statics that all survive the compiler stage. -/
inductive Prog2.CompiledPath (p : Prog2) : Nat → Prop where
  | root {i : Nat} {s : Static} :
      p.statics[i]? = some s → compileKeeps s = true → (s.lroot || s.retain) = true →
      Prog2.CompiledPath p i
  | step {i j : Nat} {sj : Static} :
      Prog2.CompiledPath p i → (i, j) ∈ p.ledges → p.statics[j]? = some sj →
      compileKeeps sj = true → Prog2.CompiledPath p j

end Toy.RelroGc
