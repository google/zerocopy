/-
Toy drop-scope language: syntax, observable events, editions and executed actions.

These are definitions of a toy model. They are meant to capture the documented
temporary-scope rules of Rust's 2021 and 2024 editions for block tail expressions,
`if let` scrutinees and `match` scrutinees; they are not Rust's definitions.
-/

namespace Toy.DropScope

/-- Observable events. `out n` is an ordinary side effect (for example a print);
`dtor n` is an event emitted by a destructor. Execution traces are lists of events. -/
inductive Ev where
  | out (n : Nat)
  | dtor (n : Nat)
  deriving DecidableEq, Repr

/-- The two editions whose temporary-scope rules the toy compares. -/
inductive Edition where
  | e2021
  | e2024
  deriving DecidableEq, Repr

/-- The two independent rule switches that distinguish the editions in the toy:
`tail2024` makes the tail expression of every block a temporary scope (its temporaries are
dropped before the block's locals); `ifLet2024` makes the scrutinee and consequent of every
`if let` a temporary scope (scrutinee temporaries are dropped after the consequent, or before
the `else` block runs). -/
structure Rules where
  tail2024 : Bool
  ifLet2024 : Bool
  deriving DecidableEq, Repr

/-- The rule settings of each edition: 2021 has neither narrowing rule, 2024 has both. -/
def Edition.rules : Edition → Rules
  | .e2021 => ⟨false, false⟩
  | .e2024 => ⟨true, true⟩

mutual
/-- Toy expressions.
* `unit`: evaluates to a value without effects.
* `out n`: emits the output event `Ev.out n`.
* `temp dt bs`: a call evaluated in a place context; it creates a temporary whose destructor
  emits the events `dt` when the temporary is dropped. The temporary borrows the locals named
  in `bs` (used by the toy borrow check and by nothing else).
* `seq a b`: evaluates `a`, then `b`, within one expression (as in `a.f(b)`); temporaries of
  both stay live until their temporary scope ends.
* `block b`: a block expression.
* `ifLet hit s a b`: `if let P = s { a } else { b }`; the pattern outcome is fixed by `hit`
  (`true`: the pattern matches and `a` runs; `false`: `b` runs).
* `matchE hit s a₁ a₂`: `match s { P => a₁, _ => a₂ }` with the arm fixed by `hit`. -/
inductive Expr where
  | unit
  | out (n : Nat)
  | temp (dt : List Ev) (bs : List Nat)
  | seq (a b : Expr)
  | block (b : Block)
  | ifLet (hit : Bool) (scrut thn els : Expr)
  | matchE (hit : Bool) (scrut arm₁ arm₂ : Expr)

/-- The statements and tail of a block.
* `tail e`: the block's tail expression.
* `letS x dl i rest`: `let x = i;` declaring a local named `x` whose destructor emits `dl`
  when the local is dropped at the end of the block (locals drop in reverse declaration order);
  then the rest of the block.
* `exprS e rest`: the expression statement `e;`, then the rest of the block. -/
inductive Block where
  | tail (e : Expr)
  | letS (x : Nat) (dl : List Ev) (init : Expr) (rest : Block)
  | exprS (e : Expr) (rest : Block)
end

/-- A tag identifies a syntax position (a reversed path from the root); every executed action
carries the tag of the syntax node that produced it. -/
abbrev Tag := List Nat

/-- Executed actions. Each action carries the tag of the syntax node that produced it.
`mkLocal`/`dropLocal` bind and drop a local; `mkTemp`/`dropTemp` create and drop a temporary
(`bs` are the locals it borrows); `out` is an output side effect. -/
inductive Act where
  | out (tag : Tag) (n : Nat)
  | mkLocal (tag : Tag) (x : Nat)
  | dropLocal (tag : Tag) (x : Nat) (dl : List Ev)
  | mkTemp (tag : Tag) (bs : List Nat)
  | dropTemp (tag : Tag) (bs : List Nat) (dt : List Ev)
  deriving DecidableEq, Repr

/-- The observable events of an action: outputs emit their event, drops emit their
destructor's events, binding and creation emit nothing. -/
def Act.events : Act → List Ev
  | .out _ n => [.out n]
  | .mkLocal _ _ => []
  | .dropLocal _ _ dl => dl
  | .mkTemp _ _ => []
  | .dropTemp _ _ dt => dt

/-- A temporary that is live and waits for the end of its temporary scope. -/
structure Pending where
  tag : Tag
  bs : List Nat
  dt : List Ev
  deriving DecidableEq, Repr

end Toy.DropScope
