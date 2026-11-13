-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace W6Proto

/-- Register or local variable identifier. -/
abbrev RegId := Nat

/-- Stack slot or memory allocation identifier. -/
abbrev SlotId := Nat

/-- Scoped aliasing tag (`NoAliasTag` models Rust `&mut`/`&` disjoint scopes). -/
abbrev AliasTag := Nat

/-- Expressions in the unified `MIRLike` / `SSALike` core representation. -/
inductive Expr where
  | const (v : Int)
  | var (r : RegId)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  deriving DecidableEq, Repr

/-- Statements in the `MIRLike` source and `SSALike` target languages.
Includes checked arithmetic assertions (`assertNonNeg` modeling overflow/bounds
checks that trap/panic on failure vs. `assertInBounds` modeling UB on failure),
stack-slot memory operations with explicit `AliasTag`, and pure SSA bindings. -/
inductive Stmt where
  | skip
  | assign (dst : RegId) (e : Expr)
  | storeSlot (slot : SlotId) (tag : AliasTag) (e : Expr)
  | loadSlot (dst : RegId) (slot : SlotId) (tag : AliasTag)
  | checkBoundsPanic (r : RegId) (bound : Int)
  | assumeNoOverflowUB (r : RegId) (limit : Int)
  | seq (s1 s2 : Stmt)
  deriving DecidableEq, Repr

/-- Top-level program with a statement body and designated return register. -/
structure Prog where
  body : Stmt
  retReg : RegId
  deriving DecidableEq, Repr

end W6Proto
