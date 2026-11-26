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
public import Captured.Shard_001
public import Proof.IdTree
public import Spec

@[expose] public section

namespace Proof.Shard_001

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.SccSharding
open Captured.Shard_001

theorem b0_id : body_0.identity = Spec.usizeFromZerosId := by rfl
theorem b1_id : body_1.identity = Spec.i16ImmutableId := by rfl
theorem b2_id : body_2.identity = Spec.i8ImmutableId := by rfl
theorem b3_id : body_3.identity = Spec.u16ImmutableId := by rfl
theorem b4_id : body_4.identity = Spec.u8ImmutableId := by rfl
theorem b5_id : body_5.identity = Spec.usizeImmutableId := by rfl
theorem b6_id : body_6.identity = Spec.i16TryFromBytesId := by rfl
theorem b7_id : body_7.identity = Spec.i8TryFromBytesId := by rfl
theorem b8_id : body_8.identity = Spec.u16TryFromBytesId := by rfl
theorem b9_id : body_9.identity = Spec.u8TryFromBytesId := by rfl
theorem b10_id : body_10.identity = Spec.usizeTryFromBytesId := by rfl
theorem b11_id : body_11.identity = Spec.unsafeId := by rfl

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
theorem b11_unsafe : body_11.isUnsafe = true := rfl

theorem b0_argc : body_0.argumentCount = 0 := rfl
theorem b1_argc : body_1.argumentCount = 0 := rfl
theorem b2_argc : body_2.argumentCount = 0 := rfl
theorem b3_argc : body_3.argumentCount = 0 := rfl
theorem b4_argc : body_4.argumentCount = 0 := rfl
theorem b5_argc : body_5.argumentCount = 0 := rfl
theorem b6_argc : body_6.argumentCount = 0 := rfl
theorem b7_argc : body_7.argumentCount = 0 := rfl
theorem b8_argc : body_8.argumentCount = 0 := rfl
theorem b9_argc : body_9.argumentCount = 0 := rfl
theorem b10_argc : body_10.argumentCount = 0 := rfl
theorem b11_argc : body_11.argumentCount = 0 := rfl

theorem b0_valid : ValidEntryArgs body_0 [] := rfl
theorem b1_valid : ValidEntryArgs body_1 [] := rfl
theorem b2_valid : ValidEntryArgs body_2 [] := rfl
theorem b3_valid : ValidEntryArgs body_3 [] := rfl
theorem b4_valid : ValidEntryArgs body_4 [] := rfl
theorem b5_valid : ValidEntryArgs body_5 [] := rfl
theorem b6_valid : ValidEntryArgs body_6 [] := rfl
theorem b7_valid : ValidEntryArgs body_7 [] := rfl
theorem b8_valid : ValidEntryArgs body_8 [] := rfl
theorem b9_valid : ValidEntryArgs body_9 [] := rfl
theorem b10_valid : ValidEntryArgs body_10 [] := rfl
theorem b11_valid : ValidEntryArgs body_11 [] := rfl

abbrev mkBranch3 (a b c : Body) : BinChunkTree Body :=
  .branch 1 (.leaf a) (.branch 1 (.leaf b) (.leaf c))

abbrev mkBranch6 (a b c d e f : Body) : BinChunkTree Body :=
  .branch 3 (mkBranch3 a b c) (mkBranch3 d e f)

/-- Balanced midpoint `BinChunkTree` matching `Captured.Shard_001.shard_bodies`
(`12` bodies at global `DefId` range `[13, 24]`). -/
def shardTree : BinChunkTree Body :=
  .branch 6
    (mkBranch6 body_0 body_1 body_2 body_3 body_4 body_5)
    (mkBranch6 body_6 body_7 body_8 body_9 body_10 body_11)

theorem shardBodies_eq :
    Captured.Shard_001.shard_bodies = BinChunkTree.toList shardTree :=
  rfl

theorem shardSize : BinChunkTree.size shardTree = 12 :=
  rfl

theorem shardWf : BinChunkTree.wf shardTree = true :=
  rfl

private theorem allIdx_leaf_body {b : Body} {idx : Nat}
    (h : checkBodyIdentityAt Proof.IdTree.idDecisionTree idx b = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (.leaf b) idx = true :=
  BinChunkTree.allIdx_leaf h

private theorem allIdx_b3 {a b c : Body} {base : Nat}
    (ha : checkBodyIdentityAt Proof.IdTree.idDecisionTree base a = true)
    (hb : checkBodyIdentityAt Proof.IdTree.idDecisionTree (base + 1) b = true)
    (hc : checkBodyIdentityAt Proof.IdTree.idDecisionTree (base + 2) c = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 a b c) base = true :=
  BinChunkTree.allIdx_branch rfl (allIdx_leaf_body ha)
    (BinChunkTree.allIdx_branch rfl (allIdx_leaf_body hb) (allIdx_leaf_body hc))

private theorem allIdx_b6 {a b c d e f : Body} {base : Nat}
    (hL : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 a b c) base = true)
    (hR : BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch3 d e f) (base + 3) = true) :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      (mkBranch6 a b c d e f) base = true :=
  BinChunkTree.allIdx_branch rfl hL hR

theorem shardUniq :
    BinChunkTree.allIdx (checkBodyIdentityAt Proof.IdTree.idDecisionTree)
      shardTree 13 = true :=
  BinChunkTree.allIdx_branch rfl
    (allIdx_b6 (allIdx_b3 rfl rfl rfl) (allIdx_b3 rfl rfl rfl))
    (allIdx_b6 (allIdx_b3 rfl rfl rfl) (allIdx_b3 rfl rfl rfl))

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

theorem b0_runs : Runs body_0 2 [] .unit := rfl
theorem b1_runs : Runs body_1 2 [] .unit := rfl
theorem b2_runs : Runs body_2 2 [] .unit := rfl
theorem b3_runs : Runs body_3 2 [] .unit := rfl
theorem b4_runs : Runs body_4 2 [] .unit := rfl
theorem b5_runs : Runs body_5 2 [] .unit := rfl
theorem b6_runs : Runs body_6 2 [] .unit := rfl
theorem b7_runs : Runs body_7 2 [] .unit := rfl
theorem b8_runs : Runs body_8 2 [] .unit := rfl
theorem b9_runs : Runs body_9 2 [] .unit := rfl
theorem b10_runs : Runs body_10 2 [] .unit := rfl
theorem b11_runs : Runs body_11 2 [] .unit := rfl

private theorem mkMarkerLoc {b : Body}
    (hAdm : BodyStaticIntrinsic b = true)
    (hTys : (b.locals.drop 1).take b.argumentCount = [])
    (hRuns : Runs b 2 [] .unit) :
    LocalBodyVerified b (Spec.specs.safety b.identity) :=
  localBodyVerified_of_runs0 hAdm hTys hRuns

private theorem tv3 {a b c : Body}
    (ha : LocalBodyVerified a (Spec.specs.safety a.identity))
    (hb : LocalBodyVerified b (Spec.specs.safety b.identity))
    (hc : LocalBodyVerified c (Spec.specs.safety c.identity)) :
    TreeLocalVerified Spec.specs (mkBranch3 a b c) :=
  ⟨ha, ⟨hb, hc⟩⟩

private theorem tv6 {a b c d e f : Body}
    (hL : TreeLocalVerified Spec.specs (mkBranch3 a b c))
    (hR : TreeLocalVerified Spec.specs (mkBranch3 d e f)) :
    TreeLocalVerified Spec.specs (mkBranch6 a b c d e f) :=
  ⟨hL, hR⟩

theorem shardVerified : TreeLocalVerified Spec.specs shardTree :=
  ⟨tv6
     (tv3 (mkMarkerLoc b0_intr rfl b0_runs)
       (mkMarkerLoc b1_intr rfl b1_runs)
       (mkMarkerLoc b2_intr rfl b2_runs))
     (tv3 (mkMarkerLoc b3_intr rfl b3_runs)
       (mkMarkerLoc b4_intr rfl b4_runs)
       (mkMarkerLoc b5_intr rfl b5_runs)),
   tv6
     (tv3 (mkMarkerLoc b6_intr rfl b6_runs)
       (mkMarkerLoc b7_intr rfl b7_runs)
       (mkMarkerLoc b8_intr rfl b8_runs))
     (tv3 (mkMarkerLoc b9_intr rfl b9_runs)
       (mkMarkerLoc b10_intr rfl b10_runs)
       (mkMarkerLoc b11_intr rfl b11_runs))⟩

end Proof.Shard_001

end
