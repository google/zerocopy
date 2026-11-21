import Toy.ZstAssume.Semantics

/-!
# Program transformations

Each transformation edits one block. `List.set` leaves the program unchanged when the
label is out of range (such a label already denotes `Block.unreach`).
-/

namespace Toy.ZstAssume

/-- Delete the `i`-th statement of block `l`. -/
def deleteStmt (P : Prog) (l : Label) (i : Nat) : Prog :=
  P.set l { P.blk l with stmts := (P.blk l).stmts.eraseIdx i }

/-- Insert statement `s` before the `i`-th statement of block `l` (at the end when `i`
is at least the number of statements). -/
def insertStmt (P : Prog) (l : Label) (i : Nat) (s : Stmt) : Prog :=
  P.set l { P.blk l with stmts := (P.blk l).stmts.take i ++ s :: (P.blk l).stmts.drop i }

/-- Replace block `b` by `Block.unreach` (backward propagation of unreachability). -/
def replaceUnreachable (P : Prog) (b : Label) : Prog :=
  P.set b Block.unreach

/-- Replace the terminator of block `l`. -/
def setTerm (P : Prog) (l : Label) (t : Term) : Prog :=
  P.set l { P.blk l with term := t }

/-- `IsUnreachableBlock P b`: label `b` denotes a block with no statements and an
`unreachable` terminator. -/
def IsUnreachableBlock (P : Prog) (b : Label) : Prop := P.blk b = Block.unreach

instance (P : Prog) (b : Label) : Decidable (IsUnreachableBlock P b) :=
  inferInstanceAs (Decidable (P.blk b = Block.unreach))

/-- Remove every arm with value `v` from a switch. Since a switch takes the *first*
matching arm, removing the later duplicates of `v` changes nothing. -/
def dropArms (arms : List (Int × Label)) (v : Int) : List (Int × Label) :=
  arms.filter (fun a => a.1 != v)

/-- Prune the arms with value `v` from the switch terminating block `l`, without an
`assume`. Values `x = v` are then sent to the `otherwise` label. Identity if block `l`
does not end in a switch. -/
def pruneArm (P : Prog) (l : Label) (v : Int) : Prog :=
  match (P.blk l).term with
  | .switch x arms ow => setTerm P l (.switch x (dropArms arms v) ow)
  | _ => P

/-- Prune the arms with value `v` from the switch terminating block `l`, inserting
`assume (x ≠ v)` at the end of the block (immediately before the switch). -/
def pruneArmAssume (P : Prog) (l : Label) (v : Int) : Prog :=
  match (P.blk l).term with
  | .switch x arms ow =>
      P.set l ⟨(P.blk l).stmts ++ [.assume (.ne x v)], .switch x (dropArms arms v) ow⟩
  | _ => P

/-- For a switch `switch x [(v, b)] ow` terminating block `l`, replace it by
`assume (x = v); goto b`. Identity for other terminators. -/
def pruneOtherwiseAssume (P : Prog) (l : Label) : Prog :=
  match (P.blk l).term with
  | .switch x [(v, b)] _ => P.set l ⟨(P.blk l).stmts ++ [.assume (.eq x v)], .goto b⟩
  | _ => P

/-- Fact-based folding: replace the terminator of block `l` by `goto b`. It models a
pass that, from a fact such as "`x ≠ v` holds at block `l`", resolves the switch at
`l` to its `otherwise` label `b`. -/
def foldToGoto (P : Prog) (l : Label) (b : Label) : Prog := setTerm P l (.goto b)

/-- A one-block program performing `copy (var s) (var d) τ n` and halting. -/
def copyProg (s d : Var) (τ : Ty) (n : Nat) : Prog :=
  [⟨[.copy (.var s) (.var d) τ n], .halt⟩]

/-- The element-loop lowering of `copyProg s d τ n`: counter `i := n`; while `i ≠ 0`,
copy one element and advance both pointers by `τ.size`. Local `i` is overwritten; `s`
and `d` change only when the loop body runs (at count `n = 0` they keep their values). -/
def copyLoopProg (s d i : Var) (τ : Ty) (n : Nat) : Prog :=
  [ ⟨[.assign i (.const n)], .goto 1⟩,
    ⟨[], .switch i [(0, 3)] 2⟩,
    ⟨[.copy (.var s) (.var d) τ 1,
      .assign s (.add (.var s) (.const τ.size)),
      .assign d (.add (.var d) (.const τ.size)),
      .assign i (.add (.var i) (.const (-1)))], .goto 1⟩,
    ⟨[], .halt⟩ ]

end Toy.ZstAssume
