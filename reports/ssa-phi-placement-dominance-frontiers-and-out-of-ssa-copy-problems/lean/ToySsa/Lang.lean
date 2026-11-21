import ToySsa.Cfg

/-!
A toy imperative language over a CFG, its SSA form with parallel φ-functions, naive
out-of-SSA translation by copy insertion, and SSA construction by φ placement plus renaming.
Values are natural numbers; a store maps variables to values.
-/
namespace Toy.Ssa

variable {n : Nat}

/-- Expressions over variables of type `V`. -/
inductive Exp (V : Type) where
  | lit (k : Nat)
  | var (x : V)
  | add (a b : Exp V)
  deriving Repr

/-- Expression evaluation in a store. -/
def Exp.eval {V : Type} (σ : V → Nat) : Exp V → Nat
  | .lit k => k
  | .var x => σ x
  | .add a b => a.eval σ + b.eval σ

/-- Store update. -/
def upd {V : Type} [DecidableEq V] (σ : V → Nat) (x : V) (v : Nat) : V → Nat :=
  fun y => if y = x then v else σ y

/-- Parallel copy `(d₁, …, dₖ) := (s₁, …, sₖ)`: every destination receives the value its source
had *before* the copy (all reads precede all writes); a repeated destination takes its first
entry. A move is a pair `(destination, source)`. -/
def parCopy {V : Type} [DecidableEq V] (ms : List (V × V)) (σ : V → Nat) : V → Nat :=
  fun y => match ms.find? (fun m => decide (m.1 = y)) with
    | some m => σ m.2
    | none => σ y

/-- Instructions: an assignment `x := e`, or a parallel copy. -/
inductive Instr (V : Type) where
  | assign (x : V) (e : Exp V)
  | pcopy (moves : List (V × V))

/-- Instruction execution. -/
def Instr.exec {V : Type} [DecidableEq V] : Instr V → (V → Nat) → (V → Nat)
  | .assign x e, σ => upd σ x (e.eval σ)
  | .pcopy ms, σ => parCopy ms σ

/-- Sequential execution of a block body. -/
def execBody {V : Type} [DecidableEq V] (is : List (Instr V)) (σ : V → Nat) : V → Nat :=
  is.foldl (fun σ i => i.exec σ) σ

/-- A (non-SSA) program: a CFG and one straight-line body per block. Branch conditions are not
modeled: an execution is any walk of the CFG (all paths are considered feasible). -/
structure Prog (V : Type) (n : Nat) where
  cfg : Cfg n
  body : Fin n → List (Instr V)

/-- Run the bodies of the blocks of a walk in order. -/
def Prog.run {V : Type} [DecidableEq V] (P : Prog V n) : (V → Nat) → List (Fin n) → (V → Nat)
  | σ, [] => σ
  | σ, b :: bs => P.run (execBody (P.body b) σ) bs

/-- Store on entry to the last block of a walk: the bodies of all earlier blocks have run. -/
def Prog.atTop {V : Type} [DecidableEq V] (P : Prog V n) (σ : V → Nat) (path : List (Fin n)) :
    V → Nat :=
  P.run σ path.dropLast

/-- An SSA-form program, as syntax: each block has a list of φ-functions `(dest, operand)` where
`operand p` is the source variable for the edge from predecessor `p`, followed by a body. The
type imposes no well-formedness: single assignment (`SsaProg.SingleAssignment`), distinct φ
destinations, strictness (definitions dominating uses), and the absence of φs at the entry are
not built in, and `operand p` is also defined for non-predecessors `p` (unused there). -/
structure SsaProg (V : Type) (n : Nat) where
  cfg : Cfg n
  phis : Fin n → List (V × (Fin n → V))
  body : Fin n → List (Instr V)

/-- The φ-copies of block `b` for the edge from `p`, as moves `(dest, source)`. -/
def SsaProg.phiMoves {V : Type} (P : SsaProg V n) (p b : Fin n) : List (V × V) :=
  (P.phis b).map (fun φ => (φ.1, φ.2 p))

/-- Entering block `b` from `p`: all φ-functions of `b` execute as one parallel copy. -/
def SsaProg.enter {V : Type} [DecidableEq V] (P : SsaProg V n) (p b : Fin n) (σ : V → Nat) :
    V → Nat :=
  parCopy (P.phiMoves p b) σ

/-- Continue a run whose current block is `cur` (body already executed). -/
def SsaProg.runFrom {V : Type} [DecidableEq V] (P : SsaProg V n) :
    Fin n → (V → Nat) → List (Fin n) → (V → Nat)
  | _, σ, [] => σ
  | cur, σ, b :: bs => P.runFrom b (execBody (P.body b) (P.enter cur b σ)) bs

/-- Run along a walk: the first block runs its body only (no incoming edge); each later block
first executes its φs for the edge just taken, then its body. -/
def SsaProg.run {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat) :
    List (Fin n) → (V → Nat)
  | [] => σ
  | b :: bs => P.runFrom b (execBody (P.body b) σ) bs

/-- Store on entry to the last block of a walk, after that block's φs. -/
def SsaProg.atTop {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (path : List (Fin n)) : V → Nat :=
  match path.reverse with
  | b :: p :: _ => P.enter p b (P.run σ path.dropLast)
  | _ => σ

/-! ### Naive out-of-SSA translation -/

/-- How the φ-copies of one edge are emitted. -/
inductive CopyMode where
  /-- one parallel copy instruction -/
  | parallel
  /-- one assignment per φ, in φ order -/
  | sequential

/-- The copy instructions realizing the moves `ms`. -/
def copyInstrs {V : Type} : CopyMode → List (V × V) → List (Instr V)
  | .parallel, ms => [.pcopy ms]
  | .sequential, ms => ms.map (fun m => .assign m.1 (.var m.2))

/-- Successors of `p`, in increasing node order. -/
def succs (G : Cfg n) (p : Fin n) : List (Fin n) := (List.finRange n).filter (fun b => G.edge p b)

/-- Naive out-of-SSA translation: delete all φs and append to the end of every block `p`, for
every successor `b` of `p`, the copies for the φs of `b` on the edge `p → b`. The copies run
whenever `p` runs, whichever successor is taken next. -/
def naiveOutOfSsa {V : Type} (mode : CopyMode) (P : SsaProg V n) : Prog V n where
  cfg := P.cfg
  body p := P.body p ++ (succs P.cfg p).flatMap (fun b => copyInstrs mode (P.phiMoves p b))

/-- Critical edge (Briggs et al.): an edge from a block with several successors to a block with
several predecessors. `NoCriticalEdges` says every edge `a → b` has `b` as the only successor
of `a` or `a` as the only predecessor of `b`. -/
def NoCriticalEdges (G : Cfg n) : Prop :=
  ∀ a b, G.edge a b = true → (∀ c, G.edge a c = true → c = b) ∨ (∀ c, G.edge c b = true → c = a)

/-- φ-functions occur only at join blocks (blocks with two distinct predecessors). -/
def PhisOnlyAtJoins {V : Type} (P : SsaProg V n) : Prop :=
  ∀ b, 0 < (P.phis b).length → ∃ a c, a ≠ c ∧ P.cfg.edge a b = true ∧ P.cfg.edge c b = true

/-- Every predecessor of a block that carries φs has that block as its only successor. -/
def PhiPredsSingleSucc {V : Type} (P : SsaProg V n) : Prop :=
  ∀ p b, 0 < (P.phis b).length → P.cfg.edge p b = true → ∀ c, P.cfg.edge p c = true → c = b

/-! ### SSA construction -/

/-- Source programs for SSA construction: one list of assignments `x := e` per block, over
variables `Nat`. -/
structure Src (n : Nat) where
  cfg : Cfg n
  body : Fin n → List (Nat × Exp Nat)

/-- The source program as a `Prog`. -/
def Src.toProg (S : Src n) : Prog Nat n where
  cfg := S.cfg
  body b := (S.body b).map (fun xe => .assign xe.1 xe.2)

/-- Definition points of `x`: the entry block (initial value) and every block assigning `x`. -/
def Src.defPts (S : Src n) (x : Nat) (b : Fin n) : Prop :=
  b = S.cfg.entry ∨ x ∈ (S.body b).map Prod.fst

/-- SSA names: `(x, b, 0)` is the φ for `x` at block `b` (at the entry block: the initial value
of `x`); `(x, b, i + 1)` is the value assigned to `x` by instruction `i` of block `b`. -/
abbrev SName (n : Nat) := Nat × Fin n × Nat

/-- Index of the last assignment to `x` in a body. -/
def lastDefAux (x : Nat) : Nat → List (Nat × Exp Nat) → Option Nat → Option Nat
  | _, [], acc => acc
  | i, xe :: rest, acc => lastDefAux x (i + 1) rest (if xe.1 = x then some i else acc)

/-- Index of the last assignment to `x` in a body, if any. -/
def lastDef (x : Nat) (body : List (Nat × Exp Nat)) : Option Nat := lastDefAux x 0 body none

/-- The SSA name of the value of `x` leaving definition point `d`. -/
def outName (S : Src n) (x : Nat) (d : Fin n) : SName n :=
  match lastDef x (S.body d) with
  | some i => (x, d, i + 1)
  | none => (x, d, 0)

/-- The SSA name read by an upward-exposed use of `x` at the top of `b`: the initial value at
the entry, the φ at `b` if `phi x b`, and otherwise the value leaving `idom x b` (intended: the
nearest strictly dominating definition point, i.e. dominator-tree renaming). -/
def topName (S : Src n) (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n) (x : Nat)
    (b : Fin n) : SName n :=
  if b = S.cfg.entry ∨ phi x b = true then (x, b, 0) else outName S x (idom x b)

/-- The SSA name of `x` at the end of block `p`. -/
def liveOutName (S : Src n) (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n) (x : Nat)
    (p : Fin n) : SName n :=
  match lastDef x (S.body p) with
  | some i => (x, p, i + 1)
  | none => topName S phi idom x p

/-- Renaming of an expression under an environment mapping each variable to its current name. -/
def renameExp {W : Type} (env : Nat → W) : Exp Nat → Exp W
  | .lit k => .lit k
  | .var x => .var (env x)
  | .add a b => .add (renameExp env a) (renameExp env b)

/-- Renaming of the body of block `b`, starting at instruction index `i` with environment
`env`; each assignment defines a fresh name and updates the environment. -/
def renameBody (b : Fin n) : (Nat → SName n) → Nat → List (Nat × Exp Nat) → List (Instr (SName n))
  | _, _, [] => []
  | env, i, xe :: rest =>
      .assign (xe.1, b, i + 1) (renameExp env xe.2) ::
        renameBody b (fun y => if y = xe.1 then (xe.1, b, i + 1) else env y) (i + 1) rest

/-- SSA construction from a φ placement `phi` and a renaming source `idom`: a φ for each
`x ∈ vars` with `phi x b` at each non-entry block `b`, with operand `liveOutName x p` on the edge
from `p`; bodies renamed starting from `topName · b`. -/
def ssaConstruct (S : Src n) (vars : List Nat) (phi : Nat → Fin n → Bool)
    (idom : Nat → Fin n → Fin n) : SsaProg (SName n) n where
  cfg := S.cfg
  phis b := if b = S.cfg.entry then [] else
    (vars.filter (fun x => phi x b)).map (fun x => ((x, b, 0), fun p => liveOutName S phi idom x p))
  body b := renameBody b (fun x => topName S phi idom x b) 0 (S.body b)

/-! ### Static definitions and single assignment -/

/-- The variables an instruction writes. -/
def Instr.dests {V : Type} : Instr V → List V
  | .assign x _ => [x]
  | .pcopy ms => ms.map Prod.fst

/-- The static definitions of block `b`: its φ destinations, then the destinations of its
instructions. -/
def SsaProg.defsAt {V : Type} (P : SsaProg V n) (b : Fin n) : List V :=
  (P.phis b).map Prod.fst ++ (P.body b).flatMap Instr.dests

/-- **Static single assignment (syntactic).** Every name has at most one static definition (a φ
destination or an instruction destination) in the whole program: within a block the
definitions are pairwise distinct, and no name is defined in two different blocks. -/
def SsaProg.SingleAssignment {V : Type} (P : SsaProg V n) : Prop :=
  (∀ b, (P.defsAt b).Nodup) ∧ ∀ b b' v, v ∈ P.defsAt b → v ∈ P.defsAt b' → b = b'

/-! ### Copy sequences -/

/-- The copy instructions that the naive translation appends to block `p`: for every successor
`b` of `p` (in increasing node order), the copies for the φs of `b` on the edge `p → b`. -/
def outCopies {V : Type} (mode : CopyMode) (P : SsaProg V n) (p : Fin n) : List (Instr V) :=
  (succs P.cfg p).flatMap (fun b => copyInstrs mode (P.phiMoves p b))

theorem naiveOutOfSsa_body {V : Type} (mode : CopyMode) (P : SsaProg V n) (p : Fin n) :
    (naiveOutOfSsa mode P).body p = P.body p ++ outCopies mode P p := rfl

/-- A move list that may be executed one move at a time, in list order, with the effect of the
parallel copy: no destination of a move is the destination or the source of a later move. -/
def SeqSafe {V : Type} : List (V × V) → Prop
  | [] => True
  | m :: rest => m.1 ∉ rest.map Prod.fst ∧ m.1 ∉ rest.map Prod.snd ∧ SeqSafe rest

/-! ### Execution lemmas -/

theorem execBody_nil {V : Type} [DecidableEq V] (σ : V → Nat) : execBody [] σ = σ := rfl

theorem execBody_cons {V : Type} [DecidableEq V] (i : Instr V) (is : List (Instr V))
    (σ : V → Nat) : execBody (i :: is) σ = execBody is (i.exec σ) := rfl

theorem execBody_append {V : Type} [DecidableEq V] (l₁ l₂ : List (Instr V)) (σ : V → Nat) :
    execBody (l₁ ++ l₂) σ = execBody l₂ (execBody l₁ σ) := by
  simp [execBody, List.foldl_append]

theorem upd_apply {V : Type} [DecidableEq V] (σ : V → Nat) (x : V) (v : Nat) (y : V) :
    upd σ x v y = if y = x then v else σ y := rfl

theorem parCopy_cons {V : Type} [DecidableEq V] (d s : V) (ms : List (V × V)) (σ : V → Nat)
    (y : V) : parCopy ((d, s) :: ms) σ y = if y = d then σ s else parCopy ms σ y := by
  unfold parCopy
  by_cases h : y = d
  · subst h; simp
  · have h' : ¬ d = y := fun e => h e.symm
    simp [h, h']

theorem parCopy_nil {V : Type} [DecidableEq V] (σ : V → Nat) : parCopy ([] : List (V × V)) σ = σ := by
  funext y; simp [parCopy]

/-- A parallel copy leaves every non-destination unchanged. -/
theorem parCopy_of_not_mem {V : Type} [DecidableEq V] (ms : List (V × V)) (σ : V → Nat) (y : V)
    (hy : y ∉ ms.map Prod.fst) : parCopy ms σ y = σ y := by
  unfold parCopy
  have : ms.find? (fun m => decide (m.1 = y)) = none := by
    rw [List.find?_eq_none]
    intro m hm
    simp only [decide_eq_true_eq]
    intro h; exact hy (List.mem_map.mpr ⟨m, hm, h⟩)
  rw [this]

theorem Prog.run_append_singleton {V : Type} [DecidableEq V] (P : Prog V n) (σ : V → Nat)
    (l : List (Fin n)) (c : Fin n) : P.run σ (l ++ [c]) = execBody (P.body c) (P.run σ l) := by
  induction l generalizing σ with
  | nil => rfl
  | cons b bs ih => exact ih _

theorem Prog.atTop_append_singleton {V : Type} [DecidableEq V] (P : Prog V n) (σ : V → Nat)
    (l : List (Fin n)) (c : Fin n) : P.atTop σ (l ++ [c]) = P.run σ l := by
  simp [Prog.atTop]

theorem SsaProg.runFrom_append_pair {V : Type} [DecidableEq V] (P : SsaProg V n) (cur : Fin n)
    (σ : V → Nat) (l : List (Fin n)) (p c : Fin n) :
    P.runFrom cur σ (l ++ [p, c]) = execBody (P.body c) (P.enter p c (P.runFrom cur σ (l ++ [p]))) := by
  induction l generalizing cur σ with
  | nil => rfl
  | cons b bs ih => exact ih _ _

theorem SsaProg.run_append_pair {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (l : List (Fin n)) (p c : Fin n) :
    P.run σ (l ++ [p, c]) = execBody (P.body c) (P.enter p c (P.run σ (l ++ [p]))) := by
  cases l with
  | nil => rfl
  | cons b bs => exact P.runFrom_append_pair b _ bs p c

theorem SsaProg.atTop_append_pair {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (l : List (Fin n)) (p c : Fin n) :
    P.atTop σ (l ++ [p, c]) = P.enter p c (P.run σ (l ++ [p])) := by
  have h1 : (l ++ [p, c]).reverse = c :: p :: l.reverse := by simp
  have h2 : (l ++ [p, c]).dropLast = l ++ [p] := by
    have : l ++ [p, c] = (l ++ [p]) ++ [c] := by simp
    rw [this, List.dropLast_concat]
  unfold SsaProg.atTop
  rw [h1]
  simp only
  rw [h2]

theorem SsaProg.run_snoc {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (l : List (Fin n)) (p c : Fin n) :
    P.run σ (l ++ [p] ++ [c]) = execBody (P.body c) (P.enter p c (P.run σ (l ++ [p]))) := by
  rw [List.append_assoc]; exact P.run_append_pair σ l p c

theorem SsaProg.atTop_snoc {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (l : List (Fin n)) (p c : Fin n) :
    P.atTop σ (l ++ [p] ++ [c]) = P.enter p c (P.run σ (l ++ [p])) := by
  rw [List.append_assoc]; exact P.atTop_append_pair σ l p c

theorem SsaProg.atTop_singleton {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (c : Fin n) : P.atTop σ [c] = σ := rfl

theorem SsaProg.run_singleton {V : Type} [DecidableEq V] (P : SsaProg V n) (σ : V → Nat)
    (c : Fin n) : P.run σ [c] = execBody (P.body c) σ := rfl

end Toy.Ssa
