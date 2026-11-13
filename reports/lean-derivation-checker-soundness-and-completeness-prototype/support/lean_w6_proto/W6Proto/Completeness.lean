-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import W6Proto.Soundness

namespace W6Proto

/-- Declarative specification of valid statement derivations (`ValidStmtDeriv`). -/
inductive ValidStmtDeriv : Stmt → Stmt → StmtDeriv → Prop where
  | refl (s : Stmt) :
      ValidStmtDeriv s s (.refl s)
  | rewriteAssign (dst : RegId) (rw : ExprRewrite) :
      ValidStmtDeriv
        (.assign dst (inferExprRewrite rw).1)
        (.assign dst (inferExprRewrite rw).2)
        (.rewriteAssign dst rw)
  | promoteSlotToAssign (slot : SlotId) (tag : AliasTag) (dst : RegId) (e : Expr) :
      ValidStmtDeriv
        (.seq (.storeSlot slot tag e) (.loadSlot dst slot tag))
        (.seq (.storeSlot slot tag e) (.assign dst e))
        (.promoteSlotToAssign slot tag dst e)
  | forwardStoreAcrossNoAlias
      (s1 s2 : SlotId) (t1 t2 : AliasTag) (dst : RegId) (e1 e2 : Expr)
      (h_slot : s1 ≠ s2) (h_tag : t1 ≠ t2) :
      ValidStmtDeriv
        (.seq (.seq (.storeSlot s1 t1 e1) (.storeSlot s2 t2 e2)) (.loadSlot dst s1 t1))
        (.seq (.seq (.storeSlot s1 t1 e1) (.storeSlot s2 t2 e2)) (.assign dst e1))
        (.forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2)
  | elimOverwrittenStore (slot : SlotId) (t1 t2 : AliasTag) (e1 e2 : Expr) :
      ValidStmtDeriv
        (.seq (.storeSlot slot t1 e1) (.storeSlot slot t2 e2))
        (.storeSlot slot t2 e2)
        (.elimOverwrittenStore slot t1 t2 e1 e2)
  | elimSkipLeft (s : Stmt) :
      ValidStmtDeriv (.seq .skip s) s (.elimSkipLeft s)
  | elimSkipRight (s : Stmt) :
      ValidStmtDeriv (.seq s .skip) s (.elimSkipRight s)
  | elimAssumeUB (r : RegId) (limit : Int) :
      ValidStmtDeriv (.assumeNoOverflowUB r limit) .skip (.elimAssumeUB r limit)
  | seqCong {s1 t1 s2 t2 : Stmt} {d1 d2 : StmtDeriv}
      (h1 : ValidStmtDeriv s1 t1 d1) (h2 : ValidStmtDeriv s2 t2 d2) :
      ValidStmtDeriv (.seq s1 s2) (.seq t1 t2) (.seqCong d1 d2)
  | trans {src mid tgt : Stmt} {d1 d2 : StmtDeriv}
      (h1 : ValidStmtDeriv src mid d1) (h2 : ValidStmtDeriv mid tgt d2) :
      ValidStmtDeriv src tgt (.trans mid d1 d2)

/-- Declarative specification of valid program derivations (`ValidDeriv`). -/
structure ValidDeriv (src tgt : Prog) (d : Derivation) : Prop where
  src_ret : src.retReg = d.retReg
  tgt_ret : tgt.retReg = d.retReg
  valid_body : ValidStmtDeriv src.body tgt.body d.bodyDeriv

/-- Statement-level checker completeness: every declaratively valid derivation is
accepted by the executable boolean checker `checkStmtDeriv`. -/
theorem checkStmtDeriv_complete {src tgt : Stmt} {d : StmtDeriv}
    (h : ValidStmtDeriv src tgt d) : checkStmtDeriv src tgt d = true := by
  induction h with
  | refl s =>
    simp [checkStmtDeriv]
  | rewriteAssign dst rw =>
    simp [checkStmtDeriv]
  | promoteSlotToAssign slot tag dst e =>
    simp [checkStmtDeriv]
  | forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 h_slot h_tag =>
    simp [checkStmtDeriv, checkDisjointNoAlias, h_slot, h_tag]
  | elimOverwrittenStore slot t1 t2 e1 e2 =>
    simp [checkStmtDeriv]
  | elimSkipLeft s =>
    simp [checkStmtDeriv]
  | elimSkipRight s =>
    simp [checkStmtDeriv]
  | elimAssumeUB r limit =>
    simp [checkStmtDeriv]
  | seqCong _ _ ih1 ih2 =>
    simp [checkStmtDeriv, ih1, ih2]
  | trans _ _ ih1 ih2 =>
    simp [checkStmtDeriv, ih1, ih2]

/-- Top-level checker completeness theorem (`checkDeriv_complete`). -/
theorem checkDeriv_complete (src tgt : Prog) (d : Derivation)
    (h_valid : ValidDeriv src tgt d) : checkDeriv src tgt d = true := by
  rcases h_valid with ⟨hs, ht, hb⟩
  simp [checkDeriv, hs, ht, checkStmtDeriv_complete hb]

/-- Bidirectional equivalence between declarative validity and executable checking. -/
theorem checkStmtDeriv_iff_valid {src tgt : Stmt} {d : StmtDeriv} :
    checkStmtDeriv src tgt d = true ↔ ValidStmtDeriv src tgt d := by
  constructor
  · intro h
    induction d generalizing src tgt with
    | refl s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .refl _
    | rewriteAssign dst rw =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .rewriteAssign dst rw
    | promoteSlotToAssign slot tag dst e =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .promoteSlotToAssign slot tag dst e
    | forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
      simp only [checkStmtDeriv, Bool.and_eq_true, checkDisjointNoAlias, decide_eq_true_eq] at h
      rcases h with ⟨⟨hs, ht⟩, ⟨rfl, rfl⟩⟩
      exact .forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 hs ht
    | elimOverwrittenStore slot t1 t2 e1 e2 =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimOverwrittenStore slot t1 t2 e1 e2
    | elimSkipLeft s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimSkipLeft _
    | elimSkipRight s =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimSkipRight _
    | elimAssumeUB r limit =>
      simp only [checkStmtDeriv, decide_eq_true_eq] at h
      rcases h with ⟨rfl, rfl⟩
      exact .elimAssumeUB r limit
    | seqCong d1 d2 ih1 ih2 =>
      cases src <;> cases tgt <;> simp only [checkStmtDeriv, Bool.and_eq_true] at h <;> try contradiction
      exact .seqCong (ih1 h.1) (ih2 h.2)
    | trans mid d1 d2 ih1 ih2 =>
      simp only [checkStmtDeriv, Bool.and_eq_true] at h
      exact .trans (ih1 h.1) (ih2 h.2)
  · exact checkStmtDeriv_complete

-- ============================================================================
-- Four Concrete W5 Micro-Benchmarks Discharged by Kernel `rfl` + `checkDeriv_sound`
-- ============================================================================

/-- Micro-benchmark 1: SROA + mem2reg slot promotion followed by algebraic fold. -/
def bench1Src : Prog :=
  { body := .seq (.storeSlot 0 1 (.add (.var 1) (.const 0))) (.loadSlot 2 0 1)
    retReg := 2 }

def bench1Mid : Stmt :=
  .seq (.storeSlot 0 1 (.add (.var 1) (.const 0))) (.assign 2 (.add (.var 1) (.const 0)))

def bench1Tgt : Prog :=
  { body := .seq (.storeSlot 0 1 (.add (.var 1) (.const 0))) (.assign 2 (.var 1))
    retReg := 2 }

def bench1Deriv : Derivation :=
  { bodyDeriv := .trans bench1Mid
      (.promoteSlotToAssign 0 1 2 (.add (.var 1) (.const 0)))
      (.seqCong (.refl (.storeSlot 0 1 (.add (.var 1) (.const 0))))
                (.rewriteAssign 2 (.addZeroRight (.var 1))))
    retReg := 2 }

theorem bench1_checked : checkDeriv bench1Src bench1Tgt bench1Deriv = true := rfl

theorem bench1_refines (st : State) :
    refines (evalProg st bench1Src) (evalProg st bench1Tgt) :=
  checkDeriv_sound bench1Src bench1Tgt bench1Deriv bench1_checked st

/-- Micro-benchmark 2: GVN + LICM load forwarding across a disjoint `noalias` store. -/
def bench2Src : Prog :=
  { body := .seq (.seq (.storeSlot 10 100 (.var 0)) (.storeSlot 20 200 (.const 99)))
                 (.loadSlot 3 10 100)
    retReg := 3 }

def bench2Tgt : Prog :=
  { body := .seq (.seq (.storeSlot 10 100 (.var 0)) (.storeSlot 20 200 (.const 99)))
                 (.assign 3 (.var 0))
    retReg := 3 }

def bench2Deriv : Derivation :=
  { bodyDeriv := .forwardStoreAcrossNoAlias 10 20 100 200 3 (.var 0) (.const 99)
    retReg := 3 }

theorem bench2_checked : checkDeriv bench2Src bench2Tgt bench2Deriv = true := rfl

theorem bench2_refines (st : State) :
    refines (evalProg st bench2Src) (evalProg st bench2Tgt) :=
  checkDeriv_sound bench2Src bench2Tgt bench2Deriv bench2_checked st

/-- Micro-benchmark 3: Dead store elimination + constant folding (`13 * 3 + 0`). -/
def bench3Src : Prog :=
  { body := .seq (.seq (.storeSlot 5 1 (.const 10)) (.storeSlot 5 1 (.const 20)))
                 (.assign 0 (.add (.mul (.const 13) (.const 3)) (.const 0)))
    retReg := 0 }

def bench3Tgt : Prog :=
  { body := .seq (.storeSlot 5 1 (.const 20))
                 (.assign 0 (.const 39))
    retReg := 0 }

def bench3Deriv : Derivation :=
  { bodyDeriv := .seqCong
      (.elimOverwrittenStore 5 1 1 (.const 10) (.const 20))
      (.trans (.assign 0 (.mul (.const 13) (.const 3)))
        (.rewriteAssign 0 (.addZeroRight (.mul (.const 13) (.const 3))))
        (.rewriteAssign 0 (.constMul 13 3)))
    retReg := 0 }

theorem bench3_checked : checkDeriv bench3Src bench3Tgt bench3Deriv = true := rfl

theorem bench3_refines (st : State) :
    refines (evalProg st bench3Src) (evalProg st bench3Tgt) :=
  checkDeriv_sound bench3Src bench3Tgt bench3Deriv bench3_checked st

/-- Micro-benchmark 4: Eliminating a proven-in-bounds `assumeNoOverflowUB` check
followed by `skip` elimination (`x - x -> 0`). -/
def bench4Src : Prog :=
  { body := .seq (.assumeNoOverflowUB 1 1000) (.assign 0 (.sub (.var 1) (.var 1)))
    retReg := 0 }

def bench4Tgt : Prog :=
  { body := .assign 0 (.const 0)
    retReg := 0 }

def bench4Deriv : Derivation :=
  { bodyDeriv := .trans
      (.seq .skip (.assign 0 (.const 0)))
      (.seqCong (.elimAssumeUB 1 1000) (.rewriteAssign 0 (.subSelf (.var 1))))
      (.elimSkipLeft (.assign 0 (.const 0)))
    retReg := 0 }

theorem bench4_checked : checkDeriv bench4Src bench4Tgt bench4Deriv = true := rfl

theorem bench4_refines (st : State) :
    refines (evalProg st bench4Src) (evalProg st bench4Tgt) :=
  checkDeriv_sound bench4Src bench4Tgt bench4Deriv bench4_checked st

#print axioms checkDeriv_sound
#print axioms checkDeriv_complete
#print axioms checkStmtDeriv_iff_valid
#print axioms bench1_refines
#print axioms bench2_refines
#print axioms bench3_refines
#print axioms bench4_refines

end W6Proto
