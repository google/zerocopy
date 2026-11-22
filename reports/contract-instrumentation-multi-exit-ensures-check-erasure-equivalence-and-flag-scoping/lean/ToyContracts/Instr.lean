import ToyContracts.Semantics

/-!
# Lowering, instrumentation, erasure, and the obligations they are compared against
-/

namespace Toy.Contracts

/-! ## Lowering of `?` -/

/-- Is the terminator the source form of `?`? -/
def Term.isTryQ : Term → Bool
  | .tryQ .. => true
  | _ => false

/-- Jump targets of a terminator. -/
def Term.targets : Term → List Nat
  | .goto b => [b]
  | .branch _ b₁ b₀ => [b₁, b₀]
  | .tryQ _ _ b => [b]
  | .ret .. => []
  | .panic => []

/-- Lowered terminator of block `i` when the function has `base` blocks: `?` becomes a `branch`
whose zero side goes to the fresh block `base + i`. -/
def lowerTerm (base i : Nat) : Term → Term
  | .tryQ o _ b => .branch o b (base + i)
  | t => t

/-- The fresh block placed at index `base + i` for block `i`: a `ret .tryErr e` return edge if
block `i` ends in `tryQ _ e _`, and a `panic` block otherwise (no jump of a function whose jumps
are all in range reaches it). -/
def errBlock (blk : Block) : Block :=
  match blk.term with
  | .tryQ _ e _ => ⟨[], .ret .tryErr e⟩
  | _ => ⟨[], .panic⟩

/-- Lowering of `?` into explicit return edges: every `tryQ o e b` in block `i` becomes
`branch o b (n + i)` (with `n` the number of blocks), and block `n + i` is `ret .tryErr e`.
Lowering always appends exactly `n` blocks, one per original block (a `panic` block for every block
that does not end in `?`), so `lower f ≠ f` whenever `f` has at least one block, even if `f`
contains no `?`. Early returns are already explicit `ret .early` edges. -/
def lower (f : Fn) : Fn :=
  { f with
    blocks := (f.blocks.mapIdx fun i blk =>
                { blk with term := lowerTerm f.blocks.length i blk.term })
              ++ f.blocks.map errBlock }

/-- `g` is lowered: no block of `g`, reachable or not, ends in the source form of `?`, so every
normal return is a `ret` edge. -/
def Lowered (g : Fn) : Prop :=
  g.blocks.all (fun blk => !blk.term.isTryQ) = true

/-- Every jump target of every block, reachable or not, and the entry are block indices of `f`.
A function with no blocks never satisfies it (its entry is not a block index). -/
def JumpsInRange (f : Fn) : Prop :=
  f.entry < f.blocks.length ∧
    f.blocks.all (fun blk => blk.term.targets.all (· < f.blocks.length)) = true

instance (g : Fn) : Decidable (Lowered g) := inferInstanceAs (Decidable (_ = true))
instance (f : Fn) : Decidable (JumpsInRange f) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Instrumentation and erasure -/

/-- Placement policy for `ensures` checks: at every return edge, or at the return edge of the tail
expression only (the naive policy). -/
inductive Placement where
  | allExits
  | tailOnly
  deriving DecidableEq, Repr

/-- Does the policy put an `ensures` check on a return edge of the given provenance? -/
def Placement.selects : Placement → ExitKind → Bool
  | .allExits, _ => true
  | .tailOnly, k => k == .tail

/-- Instrument one block: append `checkEns o` before a selected `ret k o`. -/
def instrBlock (p : Placement) (blk : Block) : Block :=
  match blk.term with
  | .ret k o => if p.selects k then { blk with stmts := blk.stmts ++ [.checkEns o] } else blk
  | _ => blk

/-- Runtime contract instrumentation: a `requires` check first in the prologue, and an `ensures`
check (on the returned value) immediately before every return edge the policy selects. Blocks
keep their indices; panics and `?` terminators get no check. -/
def instr (p : Placement) (g : Fn) : Fn :=
  { prologue := .checkReq :: g.prologue
    entry := g.entry
    blocks := g.blocks.map (instrBlock p) }

/-- Contract statements: runtime checks and the `requires` assumption. -/
def Stmt.isContract : Stmt → Bool
  | .checkReq => true
  | .checkEns _ => true
  | .assumeReq => true
  | _ => false

/-- `g` contains no contract statement (`checkReq`, `checkEns`, `assumeReq`) in its prologue or in
any block, reachable or not. -/
def NoChecks (g : Fn) : Prop :=
  g.prologue.all (fun s => !s.isContract) = true ∧
    g.blocks.all (fun blk => blk.stmts.all (fun s => !s.isContract)) = true

instance (g : Fn) : Decidable (NoChecks g) := inferInstanceAs (Decidable (_ ∧ _))

/-- Erasure: delete every contract statement, whether instrumentation inserted it or the function
as written already contained it. -/
def erase (p : Fn) : Fn :=
  { prologue := p.prologue.filter (fun s => !s.isContract)
    entry := p.entry
    blocks := p.blocks.map fun blk =>
      { blk with stmts := blk.stmts.filter (fun s => !s.isContract) } }

/-- Erasure plus an assumption of the `requires` clause on entry (UB when it is false). -/
def assumeErase (p : Fn) : Fn :=
  { erase p with prologue := .assumeReq :: (erase p).prologue }

/-! ## The abstract contract wrapper -/

/-- Post-check of a final value: a normal return of `r` stays a return if `Ens x r` holds and
becomes `checkFail .post` (with the same events) otherwise; every other observation (panic, failed
check, UB, stuck, fuel exhausted) is unchanged. -/
def wrapObs (c : Contract) (x : Nat) : Obs → Obs
  | ⟨tr, .ret r⟩ => if c.ens x r then ⟨tr, .ret r⟩ else ⟨tr, .checkFail .post⟩
  | o => o

/-- The contract wrapper on observations: if `Req x` fails, a `requires` failure with no events;
otherwise the post-check of the unchecked observation. -/
def instrObs (c : Contract) (x : Nat) (o : Obs) : Obs :=
  if c.req x then wrapObs c x o else ⟨[], .checkFail .pre⟩

/-! ## Obligations and refinement -/

/-- Every normal return of `g` on `x` (for some fuel) satisfies the `ensures` clause. -/
def EnsOnReturnsAt (c : Contract) (g : Fn) (x : Nat) : Prop :=
  ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true

/-- The static obligation at `x`: if `Req x`, every normal return of `g` on `x` satisfies `Ens`. -/
def StaticObligationAt (c : Contract) (g : Fn) (x : Nat) : Prop :=
  c.req x = true → EnsOnReturnsAt c g x

/-- The static obligation: `∀ x, Req x → g x returns r → Ens x r`. -/
def StaticObligation (c : Contract) (g : Fn) : Prop :=
  ∀ x, StaticObligationAt c g x

/-- UB-licensed refinement of halting observations at `x`, with `tgt` the refining (target)
program and `src` the refined (source) program: every halting observation of `tgt` is one of
`src`, or `src` reaches UB after a prefix of its events. Replacing `src` by `tgt` can thus remove
UB but not add it. Runs of `tgt` that do not halt are not compared: a `tgt` with no halting
observation at `x` refines every `src` at `x` (`ubRefinesAt_of_forall_not_halts`). -/
def UBRefinesAt (c : Contract) (tgt src : Fn) (x : Nat) : Prop :=
  ∀ o, Halts c tgt x o →
    Halts c src x o ∨ ∃ tr, Halts c src x ⟨tr, .ub⟩ ∧ tr <+: o.events

end Toy.Contracts
