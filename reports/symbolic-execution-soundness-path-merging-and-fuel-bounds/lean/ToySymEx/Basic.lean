/-
Toy model of symbolic execution over a tiny MIR-style control-flow graph.

Everything here is a generic toy: a CFG of basic blocks with assignments and
assertions (assertions are statements inside a block, not terminators),
`goto` / `switchInt` / `return` terminators, a fuel-indexed concrete
interpreter, and a forking symbolic executor that produces a list of
`(path condition, outcome)` leaves.

Deliberate simplifications: values are dynamically typed and every operation
is total (coercing); one variable namespace serves both for program locals and
for symbolic inputs (input `x` is the initial value of local `x`); the executor
never prunes, simplifies or merges; and the leaf checks quantify semantically
over all valuations, which models an ideal (sound and complete) solver.
-/

namespace Toy.SymEx

/-! ## Values, stores, and terms -/

/-- Runtime values: mathematical integers and booleans. Operations coerce
(`Val.toInt`, `Val.toBool`) so that evaluation is total; type errors are out of
scope for this model. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Integer view of a value (`true ↦ 1`, `false ↦ 0`), used by `+`. -/
def Val.toInt : Val → Int
  | .int i => i
  | .bool b => if b then 1 else 0

/-- Truth view of a value (nonzero integers are true), used by `ite`, `assert`,
and path conditions. -/
def Val.toBool : Val → Bool
  | .int i => i != 0
  | .bool b => b

/-- Program locals and symbolic input variables are both named by naturals. -/
abbrev Var := Nat

/-- A concrete store: the value of every local. -/
abbrev Store := Var → Val

/-- A valuation of the symbolic input variables. The symbolic input variable `x`
stands for the initial value of local `x`. -/
abbrev Valuation := Var → Val

/-- Update one local of a concrete store. -/
def Store.set (st : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else st y

/-- Terms. The same syntax serves as program expressions (where `var x` reads
local `x`) and as symbolic values (where `var x` is the symbolic input
variable `x`). -/
inductive Term where
  | var (x : Var)
  | lit (v : Val)
  | add (a b : Term)
  | eq (a b : Term)
  | ite (c t e : Term)
  deriving DecidableEq, Repr, Inhabited

namespace Term

/-- Integer literal. -/
def int (k : Int) : Term := lit (.int k)
/-- The literal `true`. -/
def tt : Term := lit (.bool true)
/-- The literal `false`. -/
def ff : Term := lit (.bool false)
/-- Negation, encoded with `ite`. -/
def not (a : Term) : Term := ite a ff tt
/-- Conjunction, encoded with `ite`. -/
def and (a b : Term) : Term := ite a b ff
/-- Disjunction, encoded with `ite`. -/
def or (a b : Term) : Term := ite a tt b

/-- Interpretation of a term under a valuation (or, for program expressions,
under a concrete store). `eq` is structural equality of values. -/
def eval (ρ : Valuation) : Term → Val
  | var x => ρ x
  | lit v => v
  | add a b => .int ((eval ρ a).toInt + (eval ρ b).toInt)
  | eq a b => .bool (decide (eval ρ a = eval ρ b))
  | ite c t e => if (eval ρ c).toBool then eval ρ t else eval ρ e

/-- Simultaneous substitution of terms for variables. Symbolic evaluation of a
program expression in a symbolic store `σ` is `e.subst σ`. -/
def subst (σ : Var → Term) : Term → Term
  | var x => σ x
  | lit v => lit v
  | add a b => add (subst σ a) (subst σ b)
  | eq a b => eq (subst σ a) (subst σ b)
  | ite c t e => ite (subst σ c) (subst σ t) (subst σ e)

/-- Replace one variable by a term (a path-condition-driven rewrite such as
"under `x == 0`, replace `x` by `0`"). -/
def substVar (x : Var) (t : Term) : Term → Term :=
  subst (fun y => if y = x then t else var y)

end Term

/-- A Boolean term `c` holds under `ρ` when it evaluates to a true value. -/
def holds (c : Term) (ρ : Valuation) : Prop := (c.eval ρ).toBool = true

instance (c : Term) (ρ : Valuation) : Decidable (holds c ρ) :=
  inferInstanceAs (Decidable ((c.eval ρ).toBool = true))

/-- `c` is satisfiable. -/
def Sat (c : Term) : Prop := ∃ ρ, holds c ρ

/-- `c₁` and `c₂` are never true together (their conjunction is unsatisfiable). -/
def Disjoint (c₁ c₂ : Term) : Prop := ∀ ρ, ¬ (holds c₁ ρ ∧ holds c₂ ρ)

/-! ## Programs -/

/-- Statements: assignment to a local, and assertion (panics when false). -/
inductive Stmt where
  | assign (x : Var) (e : Term)
  | assert (e : Term)
  deriving DecidableEq, Repr

/-- Block terminators. `switchInt x targets otherwise` jumps to the block of the
first `(v, b)` in `targets` with `x = v`, and to `otherwise` if there is none. -/
inductive Terminator where
  | goto (b : Nat)
  | switchInt (x : Var) (targets : List (Val × Nat)) (otherwise : Nat)
  | ret
  deriving DecidableEq, Repr

/-- A basic block: straight-line statements followed by a terminator. -/
structure Block where
  stmts : List Stmt
  term : Terminator
  deriving DecidableEq, Repr

/-- A control-flow graph; block `i` is the `i`-th element, block `0` is the entry. -/
abbrev Cfg := List Block

/-- A program location: block index and statement index within the block. -/
structure Loc where
  blk : Nat
  idx : Nat
  deriving DecidableEq, Repr

/-- Concrete outcomes of a fuel-bounded run. -/
inductive Outcome where
  | ok (st : Store)
  | panic (loc : Loc)
  | outOfFuel

/-- The block a `switchInt` selects for scrutinee value `v`. -/
def select (v : Val) : List (Val × Nat) → Nat → Nat
  | [], d => d
  | (w, b) :: rest, d => if v = w then b else select v rest d

/-- Successor block indices named by a terminator. -/
def Terminator.targetsOf : Terminator → List Nat
  | .goto b => [b]
  | .switchInt _ tgts d => tgts.map Prod.snd ++ [d]
  | .ret => []

/-- Concrete fuel-indexed interpreter. `runBlock p fuel b i ss t st` executes the
remaining statements `ss` (the first of which is statement `i` of block `b`),
then the terminator `t`. Every statement and every terminator consumes one unit
of fuel; entering a block is free. A failing `assert` at location `(b, i)` yields
`panic ⟨b, i⟩`. A jump to a nonexistent block `b'` yields `panic ⟨b', 0⟩` (a
convention; well-formed CFGs never do this). -/
def runBlock (p : Cfg) : Nat → Nat → Nat → List Stmt → Terminator → Store → Outcome
  | 0, _, _, _, _, _ => .outOfFuel
  | f + 1, b, i, .assign x e :: ss, t, st => runBlock p f b (i + 1) ss t (st.set x (e.eval st))
  | f + 1, b, i, .assert e :: ss, t, st =>
      if (e.eval st).toBool then runBlock p f b (i + 1) ss t st else .panic ⟨b, i⟩
  | _ + 1, _, _, [], .ret, st => .ok st
  | f + 1, _, _, [], .goto b', st =>
      match p[b']? with
      | some blk => runBlock p f b' 0 blk.stmts blk.term st
      | none => .panic ⟨b', 0⟩
  | f + 1, _, _, [], .switchInt x tgts d, st =>
      match p[select (st x) tgts d]? with
      | some blk => runBlock p f (select (st x) tgts d) 0 blk.stmts blk.term st
      | none => .panic ⟨select (st x) tgts d, 0⟩

/-- Run a CFG from its entry block with the given fuel and initial store. -/
def exec (p : Cfg) (fuel : Nat) (st : Store) : Outcome :=
  match p[0]? with
  | some blk => runBlock p fuel 0 0 blk.stmts blk.term st
  | none => .panic ⟨0, 0⟩

/-! ## Symbolic states and the forking symbolic executor -/

/-- A symbolic store: a term for every local. -/
abbrev SymStore := Var → Term

/-- The initial symbolic store: local `x` holds the symbolic input variable `x`. -/
def SymStore.init : SymStore := Term.var

/-- Update one local of a symbolic store. -/
def SymStore.set (σ : SymStore) (x : Var) (t : Term) : SymStore :=
  fun y => if y = x then t else σ y

/-- Instantiate a symbolic store under a valuation, giving a concrete store. -/
def SymStore.inst (σ : SymStore) (ρ : Valuation) : Store := fun x => (σ x).eval ρ

/-- Symbolic outcomes recorded at the leaves of symbolic execution. -/
inductive SymOutcome where
  | ok (σ : SymStore)
  | panic (loc : Loc)
  | outOfFuel
  deriving Inhabited

/-- Instantiate a symbolic outcome under a valuation. -/
def SymOutcome.inst : SymOutcome → Valuation → Outcome
  | .ok σ, ρ => .ok (σ.inst ρ)
  | .panic l, _ => .panic l
  | .outOfFuel, _ => .outOfFuel

/-- A leaf of symbolic execution: a path condition and the outcome on that path. -/
structure Leaf where
  pc : Term
  res : SymOutcome
  deriving Inhabited

/-- Forking at `switchInt` with symbolic scrutinee `s` under path condition `c`:
one `(path condition, target)` pair per target, in order, plus the `otherwise`
branch. Branch `j` carries `s == vⱼ` and the negations of all earlier tests. -/
def forkSwitch (s : Term) : List (Val × Nat) → Nat → Term → List (Term × Nat)
  | [], d, c => [(c, d)]
  | (v, b) :: rest, d, c =>
      (Term.and c (Term.eq s (Term.lit v)), b) ::
        forkSwitch s rest d (Term.and c (Term.not (Term.eq s (Term.lit v))))

/-- Forking symbolic executor, mirroring `runBlock` step for step and fuel unit
for fuel unit. Assignments update the symbolic store; an `assert e` forks a
panic leaf (path condition `c ∧ ¬e`) and continues under `c ∧ e`; `switchInt`
forks via `forkSwitch`. No path is pruned, even when its path condition is
unsatisfiable. -/
def symBlock (p : Cfg) : Nat → Nat → Nat → List Stmt → Terminator → Term → SymStore → List Leaf
  | 0, _, _, _, _, c, _ => [⟨c, .outOfFuel⟩]
  | f + 1, b, i, .assign x e :: ss, t, c, σ => symBlock p f b (i + 1) ss t c (σ.set x (e.subst σ))
  | f + 1, b, i, .assert e :: ss, t, c, σ =>
      ⟨Term.and c (Term.not (e.subst σ)), .panic ⟨b, i⟩⟩ ::
        symBlock p f b (i + 1) ss t (Term.and c (e.subst σ)) σ
  | _ + 1, _, _, [], .ret, c, σ => [⟨c, .ok σ⟩]
  | f + 1, _, _, [], .goto b', c, σ =>
      match p[b']? with
      | some blk => symBlock p f b' 0 blk.stmts blk.term c σ
      | none => [⟨c, .panic ⟨b', 0⟩⟩]
  | f + 1, _, _, [], .switchInt x tgts d, c, σ =>
      (forkSwitch (σ x) tgts d c).flatMap fun cb =>
        match p[cb.2]? with
        | some blk => symBlock p f cb.2 0 blk.stmts blk.term cb.1 σ
        | none => [⟨cb.1, .panic ⟨cb.2, 0⟩⟩]

/-- Symbolic execution of a CFG from its entry block, path condition `true`,
and the initial symbolic store. -/
def symExec (p : Cfg) (fuel : Nat) : List Leaf :=
  match p[0]? with
  | some blk => symBlock p fuel 0 0 blk.stmts blk.term Term.tt SymStore.init
  | none => [⟨Term.tt, .panic ⟨0, 0⟩⟩]

/-! ## Postconditions, leaf checks, and leaf-set properties -/

/-- Concrete success: the run returned and its final store satisfies `Q`. -/
def OkWith (Q : Store → Prop) : Outcome → Prop
  | .ok st => Q st
  | _ => False

/-- Concrete success or fuel exhaustion (bounded safety at this fuel): the run
did not panic within the given fuel, and if it returned then `Q` holds. This is
not Hoare-style partial correctness: a run counted here may still panic after
more steps. -/
def OkWithOrOutOfFuel (Q : Store → Prop) : Outcome → Prop
  | .ok st => Q st
  | .outOfFuel => True
  | .panic _ => False

/-- The strict leaf check: on every leaf, every valuation satisfying the leaf's
path condition gives a successful outcome satisfying `Q`. `outOfFuel` and
`panic` leaves fail the check unless their path condition is unsatisfiable. -/
def LeavesProve (L : List Leaf) (Q : Store → Prop) : Prop :=
  ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWith Q (l.res.inst ρ)

/-- The lax leaf check: like `LeavesProve`, but `outOfFuel` leaves are accepted
("fuel exhaustion read as success"). -/
def LeavesProveLax (L : List Leaf) (Q : Store → Prop) : Prop :=
  ∀ l ∈ L, ∀ ρ, holds l.pc ρ → OkWithOrOutOfFuel Q (l.res.inst ρ)

/-- Strict symbolic success of `p` at fuel `f` for postcondition `Q`. -/
def ProvesStrict (p : Cfg) (f : Nat) (Q : Store → Prop) : Prop :=
  LeavesProve (symExec p f) Q

/-- Lax symbolic "success" of `p` at fuel `f` (out-of-fuel leaves accepted). -/
def ProvesLax (p : Cfg) (f : Nat) (Q : Store → Prop) : Prop :=
  LeavesProveLax (symExec p f) Q

/-- Per-leaf soundness of a leaf list for `p` at fuel `f`: for every leaf and
every valuation satisfying its path condition, the concrete run from the
instantiated initial store with the same fuel has exactly the leaf's outcome. -/
def LeavesSound (p : Cfg) (f : Nat) (L : List Leaf) : Prop :=
  ∀ l ∈ L, ∀ ρ, holds l.pc ρ → exec p f (SymStore.init.inst ρ) = l.res.inst ρ

/-- Exhaustiveness (coverage) of a leaf list: every valuation satisfies the path
condition of at least one leaf. -/
def LeavesExhaustive (L : List Leaf) : Prop :=
  ∀ ρ, ∃ l ∈ L, holds l.pc ρ

/-- Erase every path condition (replace it by `true`). -/
def dropPcs (L : List Leaf) : List Leaf := L.map fun l => ⟨Term.tt, l.res⟩

/-! ## Guarded states and merging -/

/-- A guarded symbolic state `(c, σ)` is sound for a reference `R` (what the
concrete semantics produces from each valuation) and a continuation `K` (what the
remaining computation produces from a concrete store at the merge point) when
every valuation satisfying `c` has `R ρ = K (σ.inst ρ)`. For final leaves,
`R ρ = exec p f (init.inst ρ)` and `K = Outcome.ok`; for a join point, `K` runs
the rest of the program from that point with the remaining fuel. -/
def GuardedSound {α : Type} (R : Valuation → α) (K : Store → α) (c : Term) (σ : SymStore) : Prop :=
  ∀ ρ, holds c ρ → R ρ = K (σ.inst ρ)

/-- The guarded merge of two stores: `x ↦ ite c₁ (σ₁ x) (σ₂ x)`. -/
def mergeStore (c₁ : Term) (σ₁ σ₂ : SymStore) : SymStore :=
  fun x => Term.ite c₁ (σ₁ x) (σ₂ x)

/-- Merge two successful leaves `(c₁, σ₁)`, `(c₂, σ₂)` into
`(c₁ ∨ c₂, x ↦ ite c₁ (σ₁ x) (σ₂ x))`. -/
def mergeLeaf (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore) : Leaf :=
  ⟨Term.or c₁ c₂, .ok (mergeStore c₁ σ₁ σ₂)⟩

/-- The unguarded "merge" that keeps `σ₁` (a shortcut, not a sound merge). -/
def mergeLeafUnguarded (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (_σ₂ : SymStore) : Leaf :=
  ⟨Term.or c₁ c₂, .ok σ₁⟩

/-- A set of guarded states (with common continuation `K`) covers a behaviour
relation `B` when every behaviour `a` of every valuation `ρ` is produced by some
state whose guard holds at `ρ`. `B` may relate one valuation to several
behaviours (nondeterminism, or several visits of one program point). -/
def Covers {α : Type} (B : Valuation → α → Prop) (K : Store → α) (L : List (Term × SymStore)) : Prop :=
  ∀ ρ a, B ρ a → ∃ cs ∈ L, holds cs.1 ρ ∧ K (cs.2.inst ρ) = a

/-! ## Simplification -/

/-- A term simplifier `S` is sound under path condition `c` when it preserves
interpretation under every valuation satisfying `c`. -/
def SimpSoundUnder (c : Term) (S : Term → Term) : Prop :=
  ∀ t ρ, holds c ρ → (S t).eval ρ = t.eval ρ

/-! ## Shapes of CFGs and the fuel bound -/

/-- Acyclicity of the block graph: some ranking of block indices strictly
increases along every edge between existing blocks. On a finite graph this is
equivalent to having no cycle. Edges that name a nonexistent block are not
constrained, because such a jump ends the run with a panic. -/
def Acyclic (p : Cfg) : Prop :=
  ∃ rank : Nat → Nat, ∀ i (h : i < p.length), ∀ b ∈ (p[i]'h).term.targetsOf,
    b < p.length → rank i < rank b

/-- Forward-edge numbering, a decidable sufficient condition for `Acyclic`:
every successor named by the terminator of block `i` has index strictly greater
than `i` (the identity ranking works). Acyclic CFGs whose blocks are not
numbered in topological order fail it. -/
def ForwardEdges (p : Cfg) : Prop :=
  ∀ i (h : i < p.length), ∀ b ∈ (p[i]'h).term.targetsOf, i < b

instance (p : Cfg) : Decidable (ForwardEdges p) := by
  unfold ForwardEdges; exact inferInstance

/-- Straight-line: nonempty, block `i` ends in `goto (i+1)` except the last
block, which ends in `return`. Such a CFG has no branches and no unreachable
blocks. -/
def StraightLine (p : Cfg) : Prop :=
  p ≠ [] ∧ ∀ i (h : i < p.length),
    (p[i]'h).term = if i + 1 < p.length then .goto (i + 1) else .ret

instance (p : Cfg) : Decidable (StraightLine p) := by
  unfold StraightLine; exact inferInstance

/-- The fuel bound `#statements + #blocks`. -/
def fuelBound (p : Cfg) : Nat := (p.map fun blk => blk.stmts.length).sum + p.length

end Toy.SymEx
