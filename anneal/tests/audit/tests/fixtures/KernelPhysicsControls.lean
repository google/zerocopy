-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.MirAst
import Anneal.PTree

/-!
Positive controls for `kernel_physics_census.lean`. The census must report
each declaration below; `tests/audit/tests/kernel_physics.rs` fails if a
detector stops firing on its control.
-/

namespace KernelPhysicsControls

/-- `QUOT_ENTRY`: `eq_of_beq` at `Int` goes through `Int.instLawfulBEq`. -/
theorem int_eq_of_beq (a b : Int) (h : (a == b) = true) : a = b :=
  eq_of_beq h

/-- `AST_REC`: structural recursion over `MirTy` into `Type`. -/
def tyDepth : Trusted.MirAst.MirTy → Nat
  | .ref _ t => tyDepth t + 1
  | _ => 0

/-- `AST_REC` through a nested occurrence: recursion into the fields of
`MirTy.tuple`, which uses the auxiliary `brecOn_1`. -/
def tySize : Trusted.MirAst.MirTy → Nat
  | .tuple fields => fieldsSize fields + 1
  | _ => 1
where
  fieldsSize : List Trusted.MirAst.MirTy → Nat
    | [] => 0
    | t :: ts => tySize t + fieldsSize ts

/-- A parameterized alias for `PTree`. -/
abbrev MapOf (α : Type) := Anneal.PTree.PTree α

/-- A composed alias, wrapping `MapOf`. -/
abbrev State (α : Type) := Option (MapOf α)

/-- `PTREE_FUN`: a `PTree` of functions behind two aliases. -/
def handlers : Type := State (Nat → Nat)

/-- `PTREE_FUN` through a point-free alias. -/
abbrev EtaMap := Anneal.PTree.PTree

def etaHandlers : Type := EtaMap (Nat → Nat)

/-- `PTREE_FUN` through an identity alias inside an alias. -/
abbrev IdTy (α : Type) := α

abbrev IdMap (α : Type) := Anneal.PTree.PTree (IdTy α)

def idHandlers : Type := IdMap (Nat → Nat)

/-- `PTREE_FUN` through a `let` inside an alias. -/
abbrev LetMap (α : Type) := let T := α; Anneal.PTree.PTree T

def letHandlers : Type := LetMap (Nat → Nat)

/-- `PTREE_FUN` through a `let`-bound function type. -/
def letBodyHandlers : Type := let F := Nat → Nat; Anneal.PTree.PTree F

end KernelPhysicsControls
