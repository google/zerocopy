-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import W6Proto.Semantics

namespace W6Proto

/-- Expression-level algebraic rewrite certificates (`AddZero`, `SubSelf`,
`MulOne`, `ConstAddFold`, and congruence). -/
inductive ExprRewrite where
  | refl (e : Expr)
  | addZeroRight (e : Expr)
  | addZeroLeft (e : Expr)
  | subSelf (e : Expr)
  | mulOneRight (e : Expr)
  | constAdd (a b : Int)
  | constMul (a b : Int)
  | congAdd (r1 r2 : ExprRewrite)
  | congSub (r1 r2 : ExprRewrite)
  | congMul (r1 r2 : ExprRewrite)
  deriving DecidableEq, Repr

/-- Statement-level `HybridTrace` derivation steps covering the 5 core rule
families required by `W6`:
  1. Pure constant folding & algebraic congruence (`rewriteAssign`)
  2. `mem2reg` / stack-slot store-to-load promotion (`promoteSlotToAssign`)
  3. Disjoint `noalias` store-over-load forwarding (`forwardStoreAcrossNoAlias`)
  4. Dead code / redundant `skip` & UB-relaxation elimination (`elimSkipLeft`,
     `elimSkipRight`, `elimAssumeUB`, `elimOverwrittenStore`)
  5. Sequential congruence and transitive step composition (`seqCong`, `trans`) -/
inductive StmtDeriv where
  | refl (s : Stmt)
  | rewriteAssign (dst : RegId) (rw : ExprRewrite)
  | promoteSlotToAssign (slot : SlotId) (tag : AliasTag) (dst : RegId) (e : Expr)
  | forwardStoreAcrossNoAlias
      (s1 s2 : SlotId) (t1 t2 : AliasTag) (dst : RegId) (e1 e2 : Expr)
  | elimOverwrittenStore (slot : SlotId) (t1 t2 : AliasTag) (e1 e2 : Expr)
  | elimSkipLeft (s : Stmt)
  | elimSkipRight (s : Stmt)
  | elimAssumeUB (r : RegId) (limit : Int)
  | seqCong (d1 d2 : StmtDeriv)
  | trans (mid : Stmt) (d1 d2 : StmtDeriv)
  deriving DecidableEq, Repr

/-- Program-level derivation certificate. -/
structure Derivation where
  bodyDeriv : StmtDeriv
  retReg : RegId
  deriving DecidableEq, Repr

end W6Proto
