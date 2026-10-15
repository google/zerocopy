import Sail.Attr
import Sail.ArchSem
import Sail.ArchSemSequential
import Sail.ConcurrencyInterfaceV1

namespace Sail

/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/
def print_int : String → Int → Unit := fun _ _ => ()
def prerr_int : String → Int → Unit := fun _ _ => ()
def prerr_bits: String → BitVec n → Unit := fun _ _ => ()
def print_endline : String → Unit := fun _  => ()
def prerr_endline : String → Unit := fun _ => ()
def print : String → Unit := fun _ => ()
def prerr : String → Unit := fun _ => ()

end Sail

/-
The lean backend wants to import this (as of Mar 2026) so I'll
let it even though its not used any more. TODO: update the backend.
-/
namespace PreSail
end PreSail

abbrev ExceptM α := ExceptT α Id

def ExceptM.run (m : ExceptM α α) : α :=
  match (ExceptT.run m) with
    | .error e => e
    | .ok e => e

namespace Sail.ConcurrencyInterfaceV1

open Sail.ConcurrencyInterfaceV1.PreSail

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

def main_of_sail_main (initialState : SequentialState RegisterType trivialChoiceSource)
    (main : Unit → PreSailM RegisterType trivialChoiceSource ue Unit) : IO UInt32 := do
  let res := main () |>.run initialState
  match res with
  | .ok _ s => do
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1

end Sail.ConcurrencyInterfaceV1

def whileFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      if ←cond x then go (←f x) n else pure x
  go init fuel

def untilFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      let x ← f x
      if ←cond x then pure x else go x n
  go init fuel


instance : CoeT Int x Nat where
  coe := x.toNat

instance : CoeT (BitVec n) x (BitVec m) where
  coe := x.setWidth m

instance: CoeT (Vector (BitVec n₁) m) x (Vector (BitVec n₂) m) where
  coe := x.map fun (bv : BitVec n₁) => bv.setWidth n₂

instance {α α' β : Type u} (x : α × β) [CoeT α x.1 α'] : CoeT (α × β) x (α' × β) where
  coe := (x.1, x.2)

instance {α α' β : Type u} (x : β × α) [CoeT α x.2 α'] : CoeT (β × α) x (β × α') where
  coe := (x.1, x.2)

instance {α α' β β' : Type u} (x : α × β) [CoeT α x.1 α'] [CoeT β x.2 β'] : CoeT (α × β) x (α' × β') where
  coe := (x.1, x.2)

instance {α α' : Type u} [∀ x, CoeT α x α'] (xs : List α) : CoeT (List α) xs (List α') where
  coe := List.map (α := α) (β := α') (fun x => x) xs

instance (priority := low) : HAdd (BitVec n) (BitVec m) (BitVec n) where
  hAdd x y := x + y

instance (priority := low) : HSub (BitVec n) (BitVec m) (BitVec n) where
  hSub x y := x - y

instance (priority := low) : HAnd (BitVec n) (BitVec m) (BitVec n) where
  hAnd x y := x &&& y

instance (priority := low) : HOr (BitVec n) (BitVec m) (BitVec n) where
  hOr x y := x ||| y

instance (priority := low) : HXor (BitVec n) (BitVec m) (BitVec n) where
  hXor x y := x ^^^ y

instance [GetElem? coll Nat elem valid] : GetElem? coll Int elem (λ c i ↦ valid c i.toNat) where
  getElem c i h := c[i.toNat]'h
  getElem? c i := c[i.toNat]?

instance : HPow Int Int Int where
  hPow x n := x ^ n.toNat

infixl:65 " +i "   => fun (x y : Int) => x + y
infixl:65 " -i "   => fun (x y : Int) => x - y
infixl:65 " ^i "   => fun (x y : Int) => x ^ y
infixl:65 " *i "   => fun (x y : Int) => x * y

notation:50 x "≤b" y => decide (x ≤ y)
notation:50 x "<b" y => decide (x < y)
notation:50 x "≥b" y => decide (x ≥ y)
notation:50 x ">b" y => decide (x > y)

-- for termination measures, since they're almost always `Int`s but not always
abbrev Nat.toNat (x : Nat) := x

set_option grind.warning false
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide)

-- This lemma replaces `bif` by `if` in functions when Lean is trying to prove
-- termination.
@[wf_preprocess]
theorem cond_eq_ite (b : Bool) (x y : α) : cond b x y = ite b x y := by cases b <;> rfl
