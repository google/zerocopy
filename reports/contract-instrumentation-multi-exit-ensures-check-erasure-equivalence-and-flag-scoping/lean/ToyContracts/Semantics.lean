import ToyContracts.Syntax

/-!
# Fuel-indexed reference semantics

`run c f x n` runs function `f` under contract `c` on argument `x` with fuel `n`. Fuel counts
block executions; statements (including checks) consume no fuel. The prologue runs before any
fuel is consumed. The result is always an observation; `fuelOut` carries the events emitted
before the fuel ran out.
-/

namespace Toy.Contracts

/-- The store of locals: total, zero-initialised. -/
abbrev Store := Nat → Nat

/-- Point update of a store. -/
def Store.set (σ : Store) (i v : Nat) : Store := fun j => if j = i then v else σ j

/-- Operand evaluation. -/
def evalOp (x : Nat) (σ : Store) : Operand → Nat
  | .arg => x
  | .lit n => n
  | .loc i => σ i

/-- Right-hand-side evaluation (`sub` is truncated subtraction). -/
def evalRv (x : Nat) (σ : Store) : Rvalue → Nat
  | .use o => evalOp x σ o
  | .add a b => evalOp x σ a + evalOp x σ b
  | .sub a b => evalOp x σ a - evalOp x σ b

/-- Result of executing a statement list: continue with a store and events, or stop with an
outcome (a failed check or UB) and the events emitted so far. -/
inductive SR where
  | cont (σ : Store) (ev : List Nat)
  | stop (ev : List Nat) (o : Outcome)

/-- Execute a statement list. A `checkReq` (resp. `checkEns o`) whose clause is false stops with
`checkFail .pre` (resp. `checkFail .post`); an `assumeReq` whose clause is false stops with `ub`. -/
def execStmts (c : Contract) (x : Nat) : List Stmt → Store → List Nat → SR
  | [], σ, ev => .cont σ ev
  | .assign i rv :: ss, σ, ev => execStmts c x ss (σ.set i (evalRv x σ rv)) ev
  | .emit o :: ss, σ, ev => execStmts c x ss σ (ev ++ [evalOp x σ o])
  | .checkReq :: ss, σ, ev =>
      if c.req x then execStmts c x ss σ ev else .stop ev (.checkFail .pre)
  | .checkEns o :: ss, σ, ev =>
      if c.ens x (evalOp x σ o) then execStmts c x ss σ ev else .stop ev (.checkFail .post)
  | .assumeReq :: ss, σ, ev =>
      if c.req x then execStmts c x ss σ ev else .stop ev .ub

/-- Run from block `b` with fuel `n`, store `σ` and events `ev`. -/
def runFrom (c : Contract) (f : Fn) (x : Nat) : Nat → Nat → Store → List Nat → Obs
  | 0, _, _, ev => ⟨ev, .fuelOut⟩
  | n + 1, b, σ, ev =>
    match f.blocks[b]? with
    | none => ⟨ev, .stuck⟩
    | some blk =>
      match execStmts c x blk.stmts σ ev with
      | .stop ev' o => ⟨ev', o⟩
      | .cont σ' ev' =>
        match blk.term with
        | .goto b' => runFrom c f x n b' σ' ev'
        | .branch o b₁ b₀ => runFrom c f x n (if evalOp x σ' o = 0 then b₀ else b₁) σ' ev'
        | .tryQ o e b' =>
            if evalOp x σ' o = 0 then ⟨ev', .ret (evalOp x σ' e)⟩ else runFrom c f x n b' σ' ev'
        | .ret _ o => ⟨ev', .ret (evalOp x σ' o)⟩
        | .panic => ⟨ev', .panic⟩

/-- Run a function on argument `x` with fuel `n`: the prologue (no fuel), then the entry block. -/
def run (c : Contract) (f : Fn) (x n : Nat) : Obs :=
  match execStmts c x f.prologue (fun _ => 0) [] with
  | .stop ev o => ⟨ev, o⟩
  | .cont σ ev => runFrom c f x n f.entry σ ev

/-- `f` halts on `x` with the final (non-`fuelOut`) observation `o`, for some fuel. -/
def Halts (c : Contract) (f : Fn) (x : Nat) (o : Obs) : Prop :=
  o.outcome ≠ .fuelOut ∧ ∃ n, run c f x n = o

/-- Fuel-exact observational identity at `x`: at every fuel the two runs give the same
observation (final outcome with its events, or the events emitted before the fuel ran out). -/
def RunEqAt (c : Contract) (p q : Fn) (x : Nat) : Prop :=
  ∀ n, run c p x n = run c q x n

/-- Identity of final observations at `x`: the same halting observations (events and outcome). -/
def HaltsEqAt (c : Contract) (p q : Fn) (x : Nat) : Prop :=
  ∀ o, Halts c p x o ↔ Halts c q x o

end Toy.Contracts
