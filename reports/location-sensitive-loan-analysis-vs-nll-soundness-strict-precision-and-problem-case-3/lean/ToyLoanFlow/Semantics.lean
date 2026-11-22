import ToyLoanFlow.Syntax

/-!
# Walks and the reference semantics (ground truth)

The reference semantics follows the loan model of the package
`two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges`
(published on branch `reference` of `google/zerocopy`, added at commit
`a92dad5d362315aa1e07acade3aeedb183dd2d18`): a permission machine in the style of Stacked
Borrows and Tree Borrows, walks from `entry`, UB as a distinct outcome. Here it is extended from
one loan to one *record* per local.

A reference value is a record: target local, mutability, *tag* (the node of the borrow that
created it; copies keep the tag) and a validity bit. Effects:

* a *place write* to local `t` (a direct write, the destination of `borrow`/`copy`, or a mutable
  borrow of `t`) invalidates every record targeting `t`;
* a *place read* of `t` (every other mention of `t`, including a shared borrow of `t`)
  invalidates every `mut` record targeting `t`;
* a write through a record `R` invalidates the records targeting `R.tgt` whose tag differs
  from `R.tag`; a read through `R` invalidates the `mut` records targeting `R.tgt` whose tag
  differs from `R.tag`.

UB is a read or write through an invalid record (`deref`, `store`) or returning one (`ret`).
`ret` ends the run. Dereferencing, storing through or returning a local that holds no record
halts without UB (`.halt`), and so does writing through a shared record. `WellTyped` rules out
writes through shared references but performs no definite-initialization check, so a
well-typed program may dereference a local that holds no record; `Safe` does not count that as
UB.
-/

namespace Toy.LoanFlow

variable {n m : Nat}

/-- `IsWalk E π`: `π` is a nonempty list of nodes in which each node is followed by one of
its `E`-successors. (Copied from `lean/ToyTwoPhase/Graph.lean:20-25` of the package cited above,
git blob `d80d4d0f36d0386d3ec3d32cdba33afb4e5e4a8d` at the commit cited above.) -/
def IsWalk (E : Edges n) : List (Fin n) → Prop
  | [] => False
  | [_] => True
  | a :: b :: rest => b ∈ E a ∧ IsWalk E (b :: rest)

instance instDecidableIsWalk (E : Edges n) : (π : List (Fin n)) → Decidable (IsWalk E π)
  | [] => isFalse (fun h => h)
  | [_] => isTrue trivial
  | a :: b :: rest =>
    haveI := instDecidableIsWalk E (b :: rest)
    if h : b ∈ E a then
      if h' : IsWalk E (b :: rest) then isTrue ⟨h, h'⟩ else isFalse (fun hw => h' hw.2)
    else isFalse (fun hw => h hw.1)

/-- Reflexive-transitive reachability along `E`. -/
inductive Reach (E : Edges n) : Fin n → Fin n → Prop
  | refl (u : Fin n) : Reach E u u
  | step {u v w : Fin n} : v ∈ E u → Reach E v w → Reach E u w

/-- A reference value. -/
structure Rec (n m : Nat) where
  tgt : Fin m
  mu : Mutbl
  tag : Fin n
  valid : Bool
  deriving DecidableEq, Repr

/-- Machine state: the record (if any) held by each local, as a list indexed by the local's
number (entries beyond the list read as `none`). -/
abbrev RState (n m : Nat) := List (Option (Rec n m))

/-- The record held by local `v`. -/
def RState.get (σ : RState n m) (v : Fin m) : Option (Rec n m) := (σ[v.val]?).getD none

/-- Initial state: no local holds a reference. -/
def RState.init : RState n m := List.replicate m none

/-- Result of executing one node. -/
inductive Outcome (n m : Nat)
  | ok (σ : RState n m)
  | halt
  | ub

/-- Invalidate the records selected by `sel`. -/
def invalidate (sel : Rec n m → Bool) (σ : RState n m) : RState n m :=
  σ.map fun x => x.map fun R => if sel R then { R with valid := false } else R

/-- Place write to local `t`. -/
def placeWrite (t : Fin m) : RState n m → RState n m :=
  invalidate fun R => R.tgt == t

/-- Place read of local `t`. -/
def placeRead (t : Fin m) : RState n m → RState n m :=
  invalidate fun R => R.tgt == t && R.mu == .mut

/-- Write through record `R`. -/
def thruWrite (R : Rec n m) : RState n m → RState n m :=
  invalidate fun R' => R'.tgt == R.tgt && R'.tag != R.tag

/-- Read through record `R`. -/
def thruRead (R : Rec n m) : RState n m → RState n m :=
  invalidate fun R' => R'.tgt == R.tgt && R'.mu == .mut && R'.tag != R.tag

/-- Update one local. -/
def RState.set (σ : RState n m) (v : Fin m) (x : Option (Rec n m)) : RState n m :=
  List.set σ v.val x

/-- One step of the reference semantics at node `q`. -/
def exec (p : Prog n m) (q : Fin n) (σ : RState n m) : Outcome n m :=
  match p.stmt q with
  | .nop => .ok σ
  | .borrow mu d s =>
      let σ1 := (match mu with | .mut => placeWrite s σ | .shr => placeRead s σ)
      .ok ((placeWrite d σ1).set d (some ⟨s, mu, q, true⟩))
  | .copy d s =>
      let σ1 := placeRead s σ
      .ok ((placeWrite d σ1).set d (σ1.get s))
  | .deref a v =>
      let σ1 := placeRead v σ
      match σ1.get v with
      | none => .halt
      | some R =>
        if R.valid = false then .ub
        else match a, R.mu with
          | .rd, _ => .ok (thruRead R σ1)
          | .wr, .mut => .ok (thruWrite R σ1)
          | .wr, .shr => .halt
  | .access a v =>
      match a with
      | .rd => .ok (placeRead v σ)
      | .wr => .ok (placeWrite v σ)
  | .store q' s =>
      let σ1 := placeRead s (placeRead q' σ)
      match σ1.get q' with
      | none => .halt
      | some R =>
        if R.valid = false then .ub
        else match R.mu with
          | .shr => .halt
          | .mut => .ok ((thruWrite R σ1).set R.tgt (σ1.get s))
  | .ret v =>
      let σ1 := placeRead v σ
      match σ1.get v with
      | none => .halt
      | some R => if R.valid = false then .ub else .halt

/-- Execute the nodes of a list in order from state `σ`. -/
def run (p : Prog n m) : RState n m → List (Fin n) → Outcome n m
  | σ, [] => .ok σ
  | σ, i :: rest =>
    match exec p i σ with
    | .ok σ' => run p σ' rest
    | .halt => .halt
    | .ub => .ub

/-- `run` reaches UB. -/
def Outcome.isUB : Outcome n m → Bool
  | .ub => true
  | _ => false

/-- `Safe p`: no walk from `entry` reaches UB. -/
def Safe (p : Prog n m) : Prop :=
  ∀ π : List (Fin n), IsWalk p.succ π → π.head? = some p.entry → (run p RState.init π).isUB = false

/-- `ReachesUB p π`: `π` is a walk from `entry` whose execution reaches UB. -/
def ReachesUB (p : Prog n m) (π : List (Fin n)) : Prop :=
  IsWalk p.succ π ∧ π.head? = some p.entry ∧ (run p RState.init π).isUB = true

instance (p : Prog n m) (π : List (Fin n)) : Decidable (ReachesUB p π) := by
  unfold ReachesUB; infer_instance

theorem not_safe_of_reachesUB {p : Prog n m} {π : List (Fin n)} (h : ReachesUB p π) :
    ¬ Safe p := by
  intro hs
  have := hs π h.1 h.2.1
  rw [h.2.2] at this
  exact Bool.noConfusion this

end Toy.LoanFlow
