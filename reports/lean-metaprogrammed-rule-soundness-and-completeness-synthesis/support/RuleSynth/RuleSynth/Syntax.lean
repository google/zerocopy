-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace RuleSynth

/-- Virtual register identifier in `MiniSSA`. -/
abbrev RegId := Nat

/-- Stack or heap allocation slot identifier. -/
abbrev SlotId := Nat

/-- Scoped aliasing tag (`NoAliasTag` modeling Rust `&mut`/`&` disjoint scopes). -/
abbrev AliasTag := Nat

/-- 64-bit integer expression AST with bitwise, shift, negation, and `freeze` operations. -/
inductive Expr where
  | const (v : Int)
  | var (r : RegId)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  | bitAnd (a b : Expr)
  | bitOr (a b : Expr)
  | bitXor (a b : Expr)
  | shiftLeftZero (a : Expr)
  | freezeVal (a : Expr)
  deriving DecidableEq, Repr

/-- 15-constructor `Stmt` AST modeling middle-end and backend `-O3` statements
(arithmetic assignments, stack-slot memory with `AliasTag`, atomic loads/stores,
checked bounds panics, UB assumptions, `KnownBits` guards, `ReadOnly` calls,
unwind landing-pad merges, fences, conditional branches, and sequential composition).
Having 15 constructors exercises the $K^2 = 225$ off-diagonal congruence case
explosion (`PITFALL-4`) when decomposing `.seq` and `.ifZero`. -/
inductive Stmt where
  | skip
  | assign (dst : RegId) (e : Expr)
  | storeSlot (slot : SlotId) (tag : AliasTag) (e : Expr)
  | loadSlot (dst : RegId) (slot : SlotId) (tag : AliasTag)
  | atomicStore (slot : SlotId) (tag : AliasTag) (e : Expr)
  | atomicLoad (dst : RegId) (slot : SlotId) (tag : AliasTag)
  | checkBoundsPanic (r : RegId) (bound : Int)
  | assumeNoOverflowUB (r : RegId) (limit : Int)
  | assumeKnownNonNegUB (r : RegId)
  | callReadOnly (dst : RegId) (arg : Expr)
  | landingPadClean (tag : Nat)
  | dbgValue (r : RegId) (metaId : Nat)
  | fenceAcq
  | ifZeroCond (cond : Int) (thenBr elseBr : Stmt)
  | seq (s1 s2 : Stmt)
  deriving DecidableEq, Repr

/-- Top-level function body and designated return register. -/
structure Prog where
  body : Stmt
  retReg : RegId
  deriving DecidableEq, Repr

end RuleSynth
