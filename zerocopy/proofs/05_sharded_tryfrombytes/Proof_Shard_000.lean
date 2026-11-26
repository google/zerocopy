-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.MirWp
public import Anneal.SccSharding
public import Captured.Shard_000
public import Proof.IdTree
public import Spec

@[expose] public section

namespace Proof.Shard_000

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.SccSharding
open Captured.Shard_000

theorem b0_id : body_0.identity = Spec.unitFromId := by rfl
theorem b1_id : body_1.identity = Spec.unitToId := by rfl
theorem b2_id : body_2.identity = Spec.usizeFromId := by rfl
theorem b3_id : body_3.identity = Spec.usizeToId := by rfl
theorem b4_id : body_4.identity = Spec.i16FromBytesId := by rfl
theorem b5_id : body_5.identity = Spec.i8FromBytesId := by rfl
theorem b6_id : body_6.identity = Spec.u16FromBytesId := by rfl
theorem b7_id : body_7.identity = Spec.u8FromBytesId := by rfl
theorem b8_id : body_8.identity = Spec.usizeFromBytesId := by rfl
theorem b9_id : body_9.identity = Spec.i16FromZerosId := by rfl
theorem b10_id : body_10.identity = Spec.i8FromZerosId := by rfl
theorem b11_id : body_11.identity = Spec.u16FromZerosId := by rfl
theorem b12_id : body_12.identity = Spec.u8FromZerosId := by rfl

theorem b0_safe : body_0.isUnsafe = false := rfl
theorem b1_safe : body_1.isUnsafe = false := rfl
theorem b2_safe : body_2.isUnsafe = false := rfl
theorem b3_safe : body_3.isUnsafe = false := rfl
theorem b4_safe : body_4.isUnsafe = false := rfl
theorem b5_safe : body_5.isUnsafe = false := rfl
theorem b6_safe : body_6.isUnsafe = false := rfl
theorem b7_safe : body_7.isUnsafe = false := rfl
theorem b8_safe : body_8.isUnsafe = false := rfl
theorem b9_safe : body_9.isUnsafe = false := rfl
theorem b10_safe : body_10.isUnsafe = false := rfl
theorem b11_safe : body_11.isUnsafe = false := rfl
theorem b12_safe : body_12.isUnsafe = false := rfl

theorem b4_argc : body_4.argumentCount = 0 := rfl
theorem b5_argc : body_5.argumentCount = 0 := rfl
theorem b6_argc : body_6.argumentCount = 0 := rfl
theorem b7_argc : body_7.argumentCount = 0 := rfl
theorem b8_argc : body_8.argumentCount = 0 := rfl
theorem b9_argc : body_9.argumentCount = 0 := rfl
theorem b10_argc : body_10.argumentCount = 0 := rfl
theorem b11_argc : body_11.argumentCount = 0 := rfl
theorem b12_argc : body_12.argumentCount = 0 := rfl

theorem b4_valid : ValidEntryArgs body_4 [] := rfl
theorem b5_valid : ValidEntryArgs body_5 [] := rfl
theorem b6_valid : ValidEntryArgs body_6 [] := rfl
theorem b7_valid : ValidEntryArgs body_7 [] := rfl
theorem b8_valid : ValidEntryArgs body_8 [] := rfl
theorem b9_valid : ValidEntryArgs body_9 [] := rfl
theorem b10_valid : ValidEntryArgs body_10 [] := rfl
theorem b11_valid : ValidEntryArgs body_11 [] := rfl
theorem b12_valid : ValidEntryArgs body_12 [] := rfl
theorem b1_valid : ValidEntryArgs body_1 [.unit] := rfl
theorem b0_arg_tys : (body_0.locals.drop 1).take body_0.argumentCount = [.int .isize false] := rfl
theorem b2_arg_tys : (body_2.locals.drop 1).take body_2.argumentCount = [.int .isize false] := rfl
theorem b3_arg_tys : (body_3.locals.drop 1).take body_3.argumentCount = [.int .isize false] := rfl

abbrev mkBranch2 (a b : Body) : BinChunkTree Body :=
  .branch 1 (.leaf a) (.leaf b)

abbrev mkBranch3 (a b c : Body) : BinChunkTree Body :=
  .branch 1 (.leaf a) (.branch 1 (.leaf b) (.leaf c))

abbrev mkBranch4 (a b c d : Body) : BinChunkTree Body :=
  .branch 2 (mkBranch2 a b) (mkBranch2 c d)

abbrev mkBranch6 (a b c d e f : Body) : BinChunkTree Body :=
  .branch 3 (mkBranch3 a b c) (mkBranch3 d e f)

abbrev mkBranch7 (a b c d e f g : Body) : BinChunkTree Body :=
  .branch 3 (mkBranch3 a b c) (mkBranch4 d e f g)

/-- Balanced midpoint `BinChunkTree` matching `Captured.Shard_000.shard_bodies`
node-for-node (`toList shardTree = shard_bodies` by `rfl`, `13` bodies at
global `DefId` range `[0, 12]`). -/
def shardTree : BinChunkTree Body :=
  .branch 6
    (mkBranch6 body_0 body_1 body_2 body_3 body_4 body_5)
    (mkBranch7 body_6 body_7 body_8 body_9 body_10 body_11 body_12)

theorem shardBodies_eq :
    Captured.Shard_000.shard_bodies = BinChunkTree.toList shardTree :=
  rfl

theorem shardSize : BinChunkTree.size shardTree = 13 :=
  rfl

theorem shardWf : BinChunkTree.wf shardTree = true :=
  rfl

private theorem allIdx_leaf_body {b : Body} {idx : Nat}
    (h : checkBodyIdentityAt Proof.IdTree.idDecisionTree idx b = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (.leaf b) idx = true :=
  BinChunkTree.allIdx_leaf h

private theorem allIdx_b2 {a b : Body} {base : Nat}
    (ha : checkBodyIdentityAt Proof.IdTree.idDecisionTree base a = true)
    (hb : checkBodyIdentityAt Proof.IdTree.idDecisionTree (base + 1) b = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch2 a b) base = true :=
  BinChunkTree.allIdx_branch rfl (allIdx_leaf_body ha) (allIdx_leaf_body hb)

private theorem allIdx_b3 {a b c : Body} {base : Nat}
    (ha : checkBodyIdentityAt Proof.IdTree.idDecisionTree base a = true)
    (hb : checkBodyIdentityAt Proof.IdTree.idDecisionTree (base + 1) b = true)
    (hc : checkBodyIdentityAt Proof.IdTree.idDecisionTree (base + 2) c = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 a b c) base = true :=
  BinChunkTree.allIdx_branch rfl (allIdx_leaf_body ha)
    (BinChunkTree.allIdx_branch rfl (allIdx_leaf_body hb) (allIdx_leaf_body hc))

private theorem allIdx_b4 {a b c d : Body} {base : Nat}
    (hL : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch2 a b) base = true)
    (hR : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch2 c d) (base + 2) = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch4 a b c d) base = true :=
  BinChunkTree.allIdx_branch rfl hL hR

private theorem allIdx_b6 {a b c d e f : Body} {base : Nat}
    (hL : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 a b c) base = true)
    (hR : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 d e f) (base + 3) = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch6 a b c d e f) base = true :=
  BinChunkTree.allIdx_branch rfl hL hR

private theorem allIdx_b7 {a b c d e f g : Body} {base : Nat}
    (hL : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 a b c) base = true)
    (hR : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch4 d e f g) (base + 3) = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch7 a b c d e f g) base = true :=
  BinChunkTree.allIdx_branch rfl hL hR

theorem shardUniq :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      shardTree 0 = true := by
  refine BinChunkTree.allIdx_branch rfl (allIdx_b6 ?_ ?_) (allIdx_b7 ?_ ?_)
  · exact allIdx_b3 rfl rfl rfl
  · exact allIdx_b3 rfl rfl rfl
  · exact allIdx_b3 rfl rfl rfl
  · exact allIdx_b4 (allIdx_b2 rfl rfl) (allIdx_b2 rfl rfl)

theorem get_0 : BinChunkTree.get? shardTree 0 = some body_0 := rfl
theorem get_1 : BinChunkTree.get? shardTree 1 = some body_1 := rfl
theorem get_2 : BinChunkTree.get? shardTree 2 = some body_2 := rfl
theorem get_3 : BinChunkTree.get? shardTree 3 = some body_3 := rfl
theorem get_4 : BinChunkTree.get? shardTree 4 = some body_4 := rfl
theorem get_5 : BinChunkTree.get? shardTree 5 = some body_5 := rfl
theorem get_6 : BinChunkTree.get? shardTree 6 = some body_6 := rfl
theorem get_7 : BinChunkTree.get? shardTree 7 = some body_7 := rfl
theorem get_8 : BinChunkTree.get? shardTree 8 = some body_8 := rfl
theorem get_9 : BinChunkTree.get? shardTree 9 = some body_9 := rfl
theorem get_10 : BinChunkTree.get? shardTree 10 = some body_10 := rfl
theorem get_11 : BinChunkTree.get? shardTree 11 = some body_11 := rfl
theorem get_12 : BinChunkTree.get? shardTree 12 = some body_12 := rfl

theorem b0_intr : BodyStaticIntrinsic body_0 = true := rfl
theorem b1_intr : BodyStaticIntrinsic body_1 = true := rfl
theorem b2_intr : BodyStaticIntrinsic body_2 = true := rfl
theorem b3_intr : BodyStaticIntrinsic body_3 = true := rfl
theorem b4_intr : BodyStaticIntrinsic body_4 = true := rfl
theorem b5_intr : BodyStaticIntrinsic body_5 = true := rfl
theorem b6_intr : BodyStaticIntrinsic body_6 = true := rfl
theorem b7_intr : BodyStaticIntrinsic body_7 = true := rfl
theorem b8_intr : BodyStaticIntrinsic body_8 = true := rfl
theorem b9_intr : BodyStaticIntrinsic body_9 = true := rfl
theorem b10_intr : BodyStaticIntrinsic body_10 = true := rfl
theorem b11_intr : BodyStaticIntrinsic body_11 = true := rfl
theorem b12_intr : BodyStaticIntrinsic body_12 = true := rfl

theorem b0_runs (v : Val) : Runs body_0 2 [v] .unit := rfl
theorem b1_runs : Runs body_1 2 [.unit] (Spec.usizeVal 0) := rfl

private theorem writePlace_isize {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    writePlace [.immediate none, .immediate (some v)] entryMemory 0
        (.int .isize false) v =
      .ok ([.immediate (some v), .immediate (some v)], entryMemory) := by
  unfold writePlace
  rw [hv]
  rfl

private theorem step_copy_isize (body : Body) {v : Val}
    (hLoc : initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (hRval : evalRvalue body.locals
        [.immediate none, .immediate (some v)]
        entryMemory (.int .isize false) (.use (.copy ⟨1, []⟩)) =
      .ok (v, [.immediate none, .immediate (some v)], entryMemory))
    (hStep : evalStep (bodyProg body) 0
        (mkState 0 0 [.immediate none, .immediate (some v)]) =
      match evalRvalue body.locals
          [.immediate none, .immediate (some v)]
          entryMemory (.int .isize false) (.use (.copy ⟨1, []⟩)) with
      | .error k => .fault k
      | .ok (val, l1, m1) =>
        match writePlace l1 m1 0 (.int .isize false) val with
        | .error k => .fault k
        | .ok (l2, m2) =>
          .step
            { frames :=
                [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := l2 }],
              callerMem := ⟨[]⟩, mem := m2 })
    (hv : checkVal v (.int .isize false) = true) :
    evalStep (bodyProg body) 0
      (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) =
    .step (mkState 0 1 [.immediate (some v), .immediate (some v)]) := by
  rw [hLoc, hStep, hRval]
  dsimp only
  rw [writePlace_isize hv]
  rfl

theorem b2_exec {v : Val} (hv : checkVal v (.int .isize false) = true) :
    Executes body_2
      (mkState 0 0 (initLocalsLoop body_2 [v] 0 body_2.locals)) v :=
  .next (step_copy_isize body_2 rfl rfl rfl hv) (.ret rfl)

theorem b3_exec {v : Val} (hv : checkVal v (.int .isize false) = true) :
    Executes body_3
      (mkState 0 0 (initLocalsLoop body_3 [v] 0 body_3.locals)) v :=
  .next (step_copy_isize body_3 rfl rfl rfl hv) (.ret rfl)

theorem b4_runs : Runs body_4 2 [] .unit := rfl
theorem b5_runs : Runs body_5 2 [] .unit := rfl
theorem b6_runs : Runs body_6 2 [] .unit := rfl
theorem b7_runs : Runs body_7 2 [] .unit := rfl
theorem b8_runs : Runs body_8 2 [] .unit := rfl
theorem b9_runs : Runs body_9 2 [] .unit := rfl
theorem b10_runs : Runs body_10 2 [] .unit := rfl
theorem b11_runs : Runs body_11 2 [] .unit := rfl
theorem b12_runs : Runs body_12 2 [] .unit := rfl

private theorem mkMarkerLoc {b : Body}
    (hAdm : BodyStaticIntrinsic b = true)
    (hTys : (b.locals.drop 1).take b.argumentCount = [])
    (hRuns : Runs b 2 [] .unit) :
    LocalBodyVerified b (Spec.specs.safety b.identity) :=
  localBodyVerified_of_runs0 hAdm hTys hRuns

private theorem tvBranch {half : Nat} {l r : BinChunkTree Body}
    (hL : TreeLocalVerified Spec.specs l)
    (hR : TreeLocalVerified Spec.specs r) :
    TreeLocalVerified Spec.specs (.branch half l r) :=
  And.intro hL hR

private theorem tv2 {a b : Body}
    (ha : LocalBodyVerified a (Spec.specs.safety a.identity))
    (hb : LocalBodyVerified b (Spec.specs.safety b.identity)) :
    TreeLocalVerified Spec.specs (mkBranch2 a b) :=
  tvBranch ha hb

private theorem tv3 {a b c : Body}
    (ha : LocalBodyVerified a (Spec.specs.safety a.identity))
    (hb : LocalBodyVerified b (Spec.specs.safety b.identity))
    (hc : LocalBodyVerified c (Spec.specs.safety c.identity)) :
    TreeLocalVerified Spec.specs (mkBranch3 a b c) :=
  tvBranch ha (tvBranch hb hc)

private theorem tv4 {a b c d : Body}
    (hL : TreeLocalVerified Spec.specs (mkBranch2 a b))
    (hR : TreeLocalVerified Spec.specs (mkBranch2 c d)) :
    TreeLocalVerified Spec.specs (mkBranch4 a b c d) :=
  tvBranch hL hR

private theorem tv6 {a b c d e f : Body}
    (hL : TreeLocalVerified Spec.specs (mkBranch3 a b c))
    (hR : TreeLocalVerified Spec.specs (mkBranch3 d e f)) :
    TreeLocalVerified Spec.specs (mkBranch6 a b c d e f) :=
  tvBranch hL hR

private theorem tv7 {a b c d e f g : Body}
    (hL : TreeLocalVerified Spec.specs (mkBranch3 a b c))
    (hR : TreeLocalVerified Spec.specs (mkBranch4 d e f g)) :
    TreeLocalVerified Spec.specs (mkBranch7 a b c d e f g) :=
  tvBranch hL hR

theorem shardVerified : TreeLocalVerified Spec.specs shardTree :=
  tvBranch
    (tv6
      (tv3
        (localBodyVerified_of_runs1 b0_intr rfl (fun v _ => b0_runs v))
        (localBodyVerified_of_runs_unit1 b1_intr rfl b1_runs)
        (localBodyVerified_isize_identity b2_intr rfl
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
      (tv3
        (localBodyVerified_isize_identity b3_intr rfl
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
        (mkMarkerLoc b4_intr rfl b4_runs)
        (mkMarkerLoc b5_intr rfl b5_runs)))
    (tv7
      (tv3
        (mkMarkerLoc b6_intr rfl b6_runs)
        (mkMarkerLoc b7_intr rfl b7_runs)
        (mkMarkerLoc b8_intr rfl b8_runs))
      (tv4
        (tv2 (mkMarkerLoc b9_intr rfl b9_runs)
          (mkMarkerLoc b10_intr rfl b10_runs))
        (tv2 (mkMarkerLoc b11_intr rfl b11_runs)
          (mkMarkerLoc b12_intr rfl b12_runs))))

end Proof.Shard_000

end
