import ToyDropScope.Syntax

/-
Elaboration and execution of the toy drop-scope language, the toy borrow check, the
`if let` to `match` rewrite, and the syntactic classes used by the results.
-/

namespace Toy.DropScope

/-- Drop pending temporaries at the end of their temporary scope: in reverse creation order. -/
def dropAll (ps : List Pending) : List Act :=
  ps.reverse.map fun q => .dropTemp q.tag q.bs q.dt

/-- Close a temporary scope: the actions so far, then the drops of every temporary that is
still pending. -/
def closeScope (r : List Act × List Pending) : List Act :=
  r.1 ++ dropAll r.2

mutual
/-- Elaboration and execution in one pass. `eval R p e` returns the actions executed while
evaluating `e` (at syntax position `p`) under the rule settings `R`, together with the
temporaries that are still live when `e` finishes and whose temporary scope is an enclosing
one (they are dropped when that enclosing scope closes).

Temporary scopes in the toy: the whole program, every statement (`letS` initializer,
`exprS`), every `if let` branch and `match` arm body; with `R.tail2024`, every block's tail
expression; with `R.ifLet2024`, the scrutinee plus consequent of every `if let`. The scrutinee
of a `match` is never a temporary scope. -/
def eval (R : Rules) (p : Tag) : Expr → List Act × List Pending
  | .unit => ([], [])
  | .out n => ([.out p n], [])
  | .temp dt bs => ([.mkTemp p bs], [⟨p, bs, dt⟩])
  | .seq a b =>
      let ra := eval R (0 :: p) a
      let rb := eval R (1 :: p) b
      (ra.1 ++ rb.1, ra.2 ++ rb.2)
  | .block b => evalBlock R (0 :: p) b
  | .ifLet hit s a b =>
      let rs := eval R (0 :: p) s
      let body := if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b)
      if R.ifLet2024 then
        (if hit then rs.1 ++ body ++ dropAll rs.2 else rs.1 ++ dropAll rs.2 ++ body, [])
      else
        (rs.1 ++ body, rs.2)
  | .matchE hit s a b =>
      let rs := eval R (0 :: p) s
      let body := if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b)
      (rs.1 ++ body, rs.2)

/-- Block elaboration: see `eval`. Locals are dropped at the end of the block, after the rest
of the block (so in reverse declaration order). In `letS`, the initializer's temporaries are dropped
(end of the `let` statement) before the local is bound (`mkLocal`); since binding emits no event, this
order is visible to the toy borrow check only. Without `R.tail2024` the tail expression's
pending temporaries stay pending past the block's end (so they are dropped after the block's
locals); with `R.tail2024` they are dropped right after the tail expression, before the
locals. -/
def evalBlock (R : Rules) (p : Tag) : Block → List Act × List Pending
  | .tail e =>
      let r := eval R (0 :: p) e
      if R.tail2024 then (closeScope r, []) else r
  | .letS x dl i rest =>
      let rr := evalBlock R (1 :: p) rest
      (closeScope (eval R (0 :: p) i) ++ [.mkLocal p x] ++ rr.1 ++ [.dropLocal p x dl], rr.2)
  | .exprS e rest =>
      let rr := evalBlock R (1 :: p) rest
      (closeScope (eval R (0 :: p) e) ++ rr.1, rr.2)
end

/-- Executing a whole program `e`: `e` is treated as an entire function body, whose outermost
temporary scope closes at the end. (A Rust function body is a block; in the toy a block is written
`.block b`, and `run` does not add one around `e`.) -/
def run (R : Rules) (e : Expr) : List Act :=
  closeScope (eval R [] e)

/-- The observable event trace of a whole program. -/
def trace (R : Rules) (e : Expr) : List Ev :=
  (run R e).flatMap Act.events

/-- `a.isDropTemp`: the action `a` drops a temporary (`dropTemp`). -/
def Act.isDropTemp : Act → Bool
  | .dropTemp _ _ _ => true
  | _ => false

/-- The creation key of a temporary-creating action: its tag and borrow list. -/
def Act.mkTempKey? : Act → Option (Tag × List Nat)
  | .mkTemp t bs => some (t, bs)
  | _ => none

/-- The drop key of a temporary-dropping action: its tag and borrow list. -/
def Act.dropTempKey? : Act → Option (Tag × List Nat)
  | .dropTemp t bs _ => some (t, bs)
  | _ => none

/-- The temporaries created in an action list (tag and borrow list of every `mkTemp`, in order). -/
def mkTemps (l : List Act) : List (Tag × List Nat) := l.filterMap Act.mkTempKey?

/-- The temporaries dropped in an action list (tag and borrow list of every `dropTemp`, in
order). -/
def dropTemps (l : List Act) : List (Tag × List Nat) := l.filterMap Act.dropTempKey?

/-- The toy borrow check over an executed action list: the check fails if a temporary is created
or dropped while some local it borrows is not live (not bound, or already dropped). `live` is the
multiset of live local names.

Limitation: borrows refer to local *names* (`Nat`), not to binders. If an inner local shadows an
outer local of the same name, dropping the inner local leaves the outer one's name in `live`, so a
temporary that borrows the name and outlives the inner local is still accepted (see
`borrowOK_shadowing_limitation`). Every result that mentions `accepts` is about this name-based
check. -/
def borrowOK : List Nat → List Act → Bool
  | _, [] => true
  | live, .mkLocal _ x :: as => borrowOK (x :: live) as
  | live, .dropLocal _ x _ :: as => borrowOK (live.erase x) as
  | live, .mkTemp _ bs :: as => bs.all live.contains && borrowOK live as
  | live, .dropTemp _ bs _ :: as => bs.all live.contains && borrowOK live as
  | live, .out _ _ :: as => borrowOK live as

/-- The toy borrow check accepts a program under rule settings `R`. -/
def accepts (R : Rules) (e : Expr) : Bool :=
  borrowOK [] (run R e)

/-- The behaviour of a program: its trace if the toy borrow check accepts it, `none` if it is
rejected. -/
def beh (R : Rules) (e : Expr) : Option (List Ev) :=
  if accepts R e then some (trace R e) else none

/-- Behaviour inclusion between rule settings: every program accepted under `R₁` is accepted
under `R₂` with the same trace. (For this deterministic toy this is the refinement relation
"every behaviour under `R₁` is a behaviour under `R₂`".) -/
def BehIncl (R₁ R₂ : Rules) : Prop :=
  ∀ e tr, beh R₁ e = some tr → beh R₂ e = some tr

mutual
/-- The migration rewrite: every `if let P = s { a } else { b }` becomes
`match s { P => a, _ => b }` (applied everywhere in the program). -/
def toMatch : Expr → Expr
  | .unit => .unit
  | .out n => .out n
  | .temp dt bs => .temp dt bs
  | .seq a b => .seq (toMatch a) (toMatch b)
  | .block b => .block (toMatchBlock b)
  | .ifLet hit s a b => .matchE hit (toMatch s) (toMatch a) (toMatch b)
  | .matchE hit s a b => .matchE hit (toMatch s) (toMatch a) (toMatch b)

/-- `toMatch` on blocks. -/
def toMatchBlock : Block → Block
  | .tail e => .tail (toMatch e)
  | .letS x dl i r => .letS x dl (toMatch i) (toMatchBlock r)
  | .exprS e r => .exprS (toMatch e) (toMatchBlock r)
end

mutual
/-- `noEscape e`: a syntactic check that no `temp` node of `e` sits in a position from which,
under the 2021 rules, its temporary is still pending when `e` finishes. Positions that count:
`e` itself, both operands of a `seq`, the tail expression of a nested block, and the scrutinee of
a nested `if let` or `match` (recursively). Positions that do not count: statements of nested
blocks, `if let` branches and `match` arms. -/
def noEscape : Expr → Bool
  | .unit => true
  | .out _ => true
  | .temp _ _ => false
  | .seq a b => noEscape a && noEscape b
  | .block b => noEscapeBlock b
  | .ifLet _ s _ _ => noEscape s
  | .matchE _ s _ _ => noEscape s

/-- `noEscape` on blocks: statements close their temporaries, so the tail decides. -/
def noEscapeBlock : Block → Bool
  | .tail e => noEscape e
  | .letS _ _ _ r => noEscapeBlock r
  | .exprS _ r => noEscapeBlock r
end

mutual
/-- `tailsClean e`: every block tail expression `t` occurring in `e` satisfies `noEscape t`. -/
def tailsClean : Expr → Bool
  | .unit => true
  | .out _ => true
  | .temp _ _ => true
  | .seq a b => tailsClean a && tailsClean b
  | .block b => tailsCleanBlock b
  | .ifLet _ s a b => tailsClean s && tailsClean a && tailsClean b
  | .matchE _ s a b => tailsClean s && tailsClean a && tailsClean b

/-- `tailsClean` on blocks. -/
def tailsCleanBlock : Block → Bool
  | .tail e => noEscape e && tailsClean e
  | .letS _ _ i r => tailsClean i && tailsCleanBlock r
  | .exprS e r => tailsClean e && tailsCleanBlock r
end

mutual
/-- `ifLetsClean e`: every `if let` scrutinee `s` occurring in `e` satisfies `noEscape s`. -/
def ifLetsClean : Expr → Bool
  | .unit => true
  | .out _ => true
  | .temp _ _ => true
  | .seq a b => ifLetsClean a && ifLetsClean b
  | .block b => ifLetsCleanBlock b
  | .ifLet _ s a b => noEscape s && ifLetsClean s && ifLetsClean a && ifLetsClean b
  | .matchE _ s a b => ifLetsClean s && ifLetsClean a && ifLetsClean b

/-- `ifLetsClean` on blocks. -/
def ifLetsCleanBlock : Block → Bool
  | .tail e => ifLetsClean e
  | .letS _ _ i r => ifLetsClean i && ifLetsCleanBlock r
  | .exprS e r => ifLetsClean e && ifLetsCleanBlock r
end

/-- Every block tail expression `t` occurring in the program passes `noEscape t`: no temporary
created by a tail expression would, under the 2021 rules, outlive that tail expression. -/
def NoTailEscapingTemps (e : Expr) : Prop := tailsClean e = true

/-- Every `if let` scrutinee `s` occurring in the program passes `noEscape s`: no temporary
created by an `if let` scrutinee would, under the 2021 rules, outlive that scrutinee. -/
def NoIfLetEscapingTemps (e : Expr) : Prop := ifLetsClean e = true

/-- `a` occurs before `b` in the action list `l` (at two distinct positions). -/
def Before (l : List Act) (a b : Act) : Prop :=
  ∃ i j : Nat, i < j ∧ l[i]? = some a ∧ l[j]? = some b

/-- `a` and `b` are executed in opposite orders under the 2021 and the 2024 rules
(`a` first under 2021, `b` first under 2024). -/
def Flipped (e : Expr) (a b : Act) : Prop :=
  Before (run Edition.e2021.rules e) a b ∧ Before (run Edition.e2024.rules e) b a

/-- The event lists of two actions commute (as words). -/
def Commute (a b : Act) : Prop :=
  a.events ++ b.events = b.events ++ a.events

end Toy.DropScope

namespace Toy.DropScope

instance : DecidablePred NoTailEscapingTemps := fun e => inferInstanceAs (Decidable (tailsClean e = true))
instance : DecidablePred NoIfLetEscapingTemps := fun e => inferInstanceAs (Decidable (ifLetsClean e = true))
instance (a b : Act) : Decidable (Commute a b) :=
  inferInstanceAs (Decidable (a.events ++ b.events = b.events ++ a.events))

end Toy.DropScope
