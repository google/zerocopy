-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Trusted.Framework
public import Anneal.InitLemmas
public import Anneal.NatBitwise
public import Anneal.Framework.StepWp
public import Anneal.Hybrid
public import Anneal.Backend

public section

/-!
# Expression-Block Proofs and Soundness Refutations (`Anneal.Backend.Canaries`)

Exercises `Anneal.Backend` across standalone 64-bit `PoisonOr Nat` expression-
block models (not `cargo-anneal` MIR captures of Rust source) together with ten
negative soundness refutations:

1. **Ten Negative Refutations (`neg1`..`neg10`):** `.symm` on `.refines`
   (checker rejection + `.poison` witness), `.refines` congruence under
   `SsaOp.freeze` and `LetBody.freeze`, `blockOptGate` rejection of `.fuzz` and
   `.sorryStub` candidates, $O(1)$ `witnessOversized` rejection, semantic
   refutation of unconditional `SemRefines` when eliding a guard (`align = 0`
   aborts with `.aborted ()` while the 0-guard target returns `0`), missing
   shift-bound fact rejection, wrong guarded-node rejection, and reversed
   `dropSubNuw` rejection.
2. **Model 1 (`dstLayoutSize`, slice byte-size scaling
   `elems * 4 + 0 -> elems <<< 2`):** `BoolCertCut` refinement, `firstAccepted`
   + `baselineIdentityPass` fallback, `composePassGates` +
   `verifiedPassToGate`, and `liftContractAlongRefinement`.
3. **Model 2 (`paddingNeededFor`, expression model of `zerocopy`'s
   `!(len.wrapping_sub(1)) & (align.get() - 1)`):** guarded `align - 1`
   underflow elision under `1 ≤ align`, `notSubOneToNeg` + `andComm` rewrite,
   satisfiability witness (`∃ env, SourceEntryPre paddingSrc env`), and
   `SimpleContract` lifting.
4. **Model 3 (`ueGolomb`, 16-guard Exp-Golomb bit-cursor expression block):**
   16 value-evaluated `GuardCond`s discharged via `.proven` range and
   non-overflow facts (`∃ env, SourceEntryPre ueGolombSrc env`) plus shift
   coalescing `((bitIdx >>> 6) >>> 3) -> (bitIdx >>> 9)`.
5. **Model 4 (`idct4Fit`, stride-mask and 4-point butterfly expression block):**
   `mask61` elision + `* 4 -> <<< 2` + shift coalescing under `firstAccepted`
   portfolio, `foldHintSteps_preserves_inv`, and satisfiability witness.
6. **Abstract Cost-Model Independence (`abstractCost_boolCertCut_shrink`):**
   simplified expression- and guard-cost estimator illustrating that
   `blockOptGate` checks `SemRefinesUnder` independently of a producer's
   extraction objective.
-/

namespace Anneal.Backend.Canaries

open Trusted.Framework Anneal.InitLemmas Anneal.Hybrid Anneal.Backend

/-! ## 1. Negative Soundness Refutations (1..4) and Freeze Positive Control -/

/-- Shared arena exercising `.landZero`, `.mul4ToShl2`, `.dropSubNuw`, and
`.freeze 7`. -/
@[expose] def freezeTestArena : List DagNode :=
  [ { op := .var 0, args := [] },       -- 0: x
    { op := .lit 0, args := [] },       -- 1: 0
    { op := .lit 4, args := [] },       -- 2: 4
    { op := .lit 2, args := [] },       -- 3: 2
    { op := .land, args := [0, 1] },    -- 4: x & 0
    { op := .mulWrap, args := [0, 2] }, -- 5: x * 4
    { op := .shl, args := [0, 3] },     -- 6: x <<< 2
    { op := .freeze 7, args := [4] },   -- 7: freeze 7 (x & 0)
    { op := .freeze 7, args := [1] },   -- 8: freeze 7 0
    { op := .freeze 7, args := [5] },   -- 9: freeze 7 (x * 4)
    { op := .freeze 7, args := [6] },   -- 10: freeze 7 (x <<< 2)
    { op := .subWrap, args := [0, 3] }, -- 11: x -_w 2
    { op := .subNuw, args := [0, 3] } ] -- 12: x -_nuw 2

/-- Refutation 1: `.symm` on directional `.refines` (`x & 0 ⊑ 0`) is rejected.
-/
theorem neg1_symmOnDirRefine_rejected :
    verifyDagGoal freezeTestArena []
      [.dirRule .landZero [0, 1] 4 1, .symm 0] 1 4 .refines = false :=
  rfl

/-- Refutation 2: Inverting `x & 0 ⊑ 0` to `0 ⊑ x & 0` is semantically unsound
at `x = .poison`. -/
theorem neg2_symmOnDirRefine_unsound_witness :
    ¬ (∀ x : PoisonOr Nat,
        refinesPoison (.val 0) (evalSsaOp (fun _ => 0) .land [x, .val 0])) :=
  fun h => h .poison

/-- Refutation 3: Congruence lifting `.refines` (`x & 0 ⊑ 0`) under `.freeze 7`
is rejected. -/
theorem neg3_dirRefineUnderFreeze_rejected :
    verifyDagGoal freezeTestArena []
      [.dirRule .landZero [0, 1] 4 1, .cong 7 8 [0]] 7 8 .refines = false :=
  rfl

/-- Refutation 4: Lifting `.refines` into `let y = [.] in y + (freeze 7 y)`
(`isFreezeFree = false`) is rejected by `LetBody.isFreezeFree`. -/
theorem neg4_dirRefineInLetFreeze_rejected :
    (LetBody.addWrap .boundVar (.freeze 7 .boundVar)).isFreezeFree = false :=
  rfl

/-- Refutation 10: Reversing `dropSubNuw` (`subWrap ⊑ subNuw`) is rejected. -/
theorem neg10_reversedDropSubNuw_rejected :
    verifyDagGoal freezeTestArena []
      [.dirRule .dropSubNuw [0, 3] 11 12] 11 12 .refines = false :=
  rfl

/-- Positive counterpart: Bidirectional `BiEqRule` (`x * 4 = x <<< 2`) IS
accepted inside `.freeze 7`, and `LetBody.isFreezeFree` accepts `freeze`-free
bodies. -/
theorem posBiEqUnderFreeze_accepted :
    verifyDagGoal freezeTestArena []
      [.biRule .mul4ToShl2 [0, 2, 3] 5 6, .cong 9 10 [0]]
      9 10 .eqExact = true ∧
    (LetBody.addWrap .boundVar (.constVal 1)).isFreezeFree = true :=
  ⟨rfl, rfl⟩

/-! ## 2. Model 1: Slice Byte-Size Scaling (`elems * 4 + 0 -> elems <<< 2`) -/

@[expose] def dstLayoutSizeSrc : SourceBlockUnit :=
  { guards := []
    arena :=
      [ { op := .var 0, args := [] },       -- 0: elems
        { op := .lit 4, args := [] },       -- 1: 4
        { op := .lit 0, args := [] },       -- 2: 0
        { op := .lit 2, args := [] },       -- 3: 2
        { op := .mulWrap, args := [0, 1] }, -- 4: elems * 4
        { op := .addWrap, args := [4, 2] }, -- 5: src = elems * 4 + 0
        { op := .shl, args := [0, 3] } ]    -- 6: opt = elems <<< 2
    srcRetId := 5
    candidates := [] }

@[expose] def dstLayoutSizeOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := dstLayoutSizeSrc.arena
    retId := 6 }

@[expose] def dstLayoutSizeSteps : List DagStep :=
  [ .biRule .addZero [4, 2] 5 4,
    .biRule .mul4ToShl2 [0, 1, 3] 4 6,
    .trans 0 1 ]

theorem dstLayoutSize_entry_satisfiable :
    ∃ env : Nat → Nat, SourceEntryPre dstLayoutSizeSrc env :=
  ⟨fun _ => 3, allCtxFactsHold_of_evalConcrete _ _ rfl⟩

/-- Refutation 6: Witness-bomb defense—a 17-step trace exceeds
`blockOptGate 2`'s cap (`2 * (7 + 1) = 16`) and is rejected in $O(1)$ with
`HybridErr.witnessOversized 17 16`. -/
@[expose] def oversizedBombSteps : List DagStep :=
  [ .refl 0, .refl 0, .refl 0, .refl 0, .refl 0, .refl 0, .refl 0, .refl 0,
    .refl 0, .refl 0, .refl 0, .refl 0, .refl 0, .refl 0, .refl 0, .refl 0,
    .refl 0 ]

theorem neg6_witnessOversized_rejected :
    evalGate (E := Unit) (blockOptGate 2) dstLayoutSizeSrc
      (.candidate dstLayoutSizeOpt oversizedBombSteps) =
      .error (.witnessOversized 17 16) :=
  rfl

/-- `dstLayoutSize` certified via `BoolCertCut.seal _ _ rfl` and resilient under
`firstAccepted` + `baselineIdentityPass` fallback. -/
theorem dstLayoutSize_refines :
    SemRefinesUnder (SourceEntryPre dstLayoutSizeSrc)
      (evalSourceBlockUnit dstLayoutSizeSrc)
      (evalCompiledBlockUnit dstLayoutSizeOpt) ∧
    withFallback dstLayoutSizeSrc
      (firstAccepted (E := Unit) (blockOptGate 2) dstLayoutSizeSrc
        [ .candidate dstLayoutSizeOpt oversizedBombSteps,
          .trapped,
          .candidate dstLayoutSizeOpt dstLayoutSizeSteps ])
      baselineIdentityPass.run = dstLayoutSizeOpt :=
  ⟨certGateCut_sound (blockOptGate 2)
      (x := dstLayoutSizeSrc) (y := dstLayoutSizeOpt)
      (w := dstLayoutSizeSteps) True.intro
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   rfl⟩

/-- Contract lifting for `dstLayoutSize`: transfers `ret = word64 (elems * 4)`
onto `dstLayoutSizeOpt`. -/
@[expose] def dstLayoutSizeContract :
    SimpleContract (Nat → Nat) Nat Unit :=
  { pre := fun _ => True
    effects := { terminates := true, noUnwind := true, noAbort := true }
    postReturn := fun env ret _ => ret = word64 (word64 (env 0) * 4) }

theorem dstLayoutSize_contract_lifted :
    SatisfiesContract (evalCompiledBlockUnit dstLayoutSizeOpt)
      dstLayoutSizeContract := by
  refine liftContractAlongRefinement
    (fun _ _ => fun _ _ hNth => by nomatch hNth)
    ?_ dstLayoutSize_refines.1
  intro env _
  have hNode4 :
      evalArenaNode env dstLayoutSizeSrc.arena 4 =
        .val (word64 (word64 (env 0) * 4)) := by
    change evalSsaOp env .mulWrap [.val (word64 (env 0)), .val 4] = _
    dsimp only [evalSsaOp, evalBinaryPoison]
    have h4 : word64 4 = 4 := rfl
    rw [word64_idem, h4]
  have hNode5 :
      evalArenaNode env dstLayoutSizeSrc.arena 5 =
        .val (word64 (word64 (env 0) * 4)) := by
    have h5 :
        evalArenaNode env dstLayoutSizeSrc.arena 5 =
          evalSsaOp env .addWrap
            [evalArenaNode env dstLayoutSizeSrc.arena 4, .val 0] :=
      rfl
    rw [h5, hNode4]
    exact biEq_addZero_sound env (.val (word64 (word64 (env 0) * 4)))
      (word64_lt _)
  refine ⟨fun hUb => ?_, fun _ hDiv => ?_, fun _ hAb => ?_, fun v _ hRet => ?_⟩
  · change evalBlockWithGuards [] dstLayoutSizeSrc.arena 5 env .faultUB at hUb
    dsimp only [evalBlockWithGuards, evalGuards, List.foldr] at hUb
    rw [hNode5] at hUb
    nomatch hUb
  · change evalBlockWithGuards [] dstLayoutSizeSrc.arena 5 env .diverged at hDiv
    dsimp only [evalBlockWithGuards, evalGuards, List.foldr] at hDiv
    rw [hNode5] at hDiv
    nomatch hDiv
  · change evalBlockWithGuards [] dstLayoutSizeSrc.arena 5 env (.aborted _)
      at hAb
    dsimp only [evalBlockWithGuards, evalGuards, List.foldr] at hAb
    rw [hNode5] at hAb
    nomatch hAb
  · change evalBlockWithGuards [] dstLayoutSizeSrc.arena 5 env (.returned v _)
      at hRet
    dsimp only [evalBlockWithGuards, evalGuards, List.foldr] at hRet
    rw [hNode5] at hRet
    injection hRet

/-! ## 3. Model 2: `padding_needed_for(len, align)` Expression Block -/

/-- Expression-block model of `zerocopy/src/util/mod.rs` `padding_needed_for`:
- Source (`node 7`, guarded by `GuardCond.subNoUnderflow 1 2`):
  `!(len -_w 1) & (align -_w 1)` where `align == 0` aborts cleanly
  (`.aborted ()`) via the guard rather than causing undefined behavior.
- Optimized (`node 11`, `guardsOut := []`):
  `(align -_w 1) & (0 -_w len)` under `.proven` `subNoUnderflow 1 2`. -/
@[expose] def paddingArena : List DagNode :=
  [ { op := .var 0, args := [] },       -- 0: len
    { op := .var 1, args := [] },       -- 1: align
    { op := .lit 1, args := [] },       -- 2: 1
    { op := .lit 0, args := [] },       -- 3: 0
    { op := .subWrap, args := [0, 2] }, -- 4: len -_w 1
    { op := .bitNot, args := [4] },     -- 5: !(len -_w 1)
    { op := .subWrap, args := [1, 2] }, -- 6: align -_w 1
    { op := .land, args := [5, 6] },    -- 7: src = !(len -_w 1) & (align -_w 1)
    { op := .subWrap, args := [3, 0] }, -- 8: 0 -_w len
    { op := .subNuw, args := [1, 2] },  -- 9: align -_nuw 1
    { op := .land, args := [8, 6] },    -- 10: (0 -_w len) & (align -_w 1)
    { op := .land, args := [6, 8] } ]   -- 11: (align -_w 1) & (0 -_w len)

@[expose] def paddingSrc : SourceBlockUnit :=
  { guards := [.subNoUnderflow 1 2]
    arena := paddingArena
    srcRetId := 7
    candidates := [{ tier := .proven, fact := .subNoUnderflow 1 2 }] }

@[expose] def paddingFuzzOnlySrc : SourceBlockUnit :=
  { guards := [.subNoUnderflow 1 2]
    arena := paddingArena
    srcRetId := 7
    candidates :=
      [ { tier := .fuzz, fact := .subNoUnderflow 1 2 },
        { tier := .sorryStub, fact := .subNoUnderflow 1 2 } ] }

@[expose] def paddingOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := paddingArena
    retId := 11 }

@[expose] def paddingSteps : List DagStep :=
  [ .biRule .notSubOneToNeg [0, 4, 2, 3] 5 8, -- 0: !(len -_w 1) = (0 -_w len)
    .biRule (.promoteSubNuw 0) [1, 2] 6 9,    -- 1: subWrap = subNuw
    .dirRule .dropSubNuw [1, 2] 9 6,          -- 2: subNuw ⊑ subWrap
    .trans 1 2,                               -- 3: node 6 ⊑ node 6
    .cong 7 10 [0, 3],                        -- 4: src ⊑ node 10
    .biRule .andComm [8, 6] 10 11,            -- 5: node 10 = opt
    .trans 4 5 ]                              -- 6: src ⊑ opt

/-- Refutation 5: When `subNoUnderflow 1 2` is tagged only `.fuzz` and
`.sorryStub`, `blockOptGate` filters both out via `extractProvenFacts` and
rejects guard elision on the live gate path. -/
theorem neg5_fuzzAndSorryCandidatesRejectedByGate :
    evalGate (E := Unit) (blockOptGate 4) paddingFuzzOnlySrc
      (.candidate paddingOpt paddingSteps) = .error .rejectedByChecker :=
  rfl

/-- Refutation 7: Unconditional `SemRefines` (without `SourceEntryPre`) is
genuinely FALSE when eliding `GuardCond.subNoUnderflow 1 2`: at `align = 0`
(`env := fun _ => 0`), `paddingSrc` aborts cleanly with `.aborted ()` (not
`.faultUB`) while `paddingOpt` returns `0`. -/
theorem neg7_unconditionalGuardElision_unsound :
    evalSourceBlockUnit paddingSrc (fun _ => 0) (.aborted ()) ∧
    evalCompiledBlockUnit paddingOpt (fun _ => 0) (.returned 0 ()) ∧
    ¬ SemRefines (evalSourceBlockUnit paddingSrc)
        (evalCompiledBlockUnit paddingOpt) := by
  refine ⟨rfl, rfl, fun hUncond => ?_⟩
  have hNoUb : ¬ evalSourceBlockUnit paddingSrc (fun _ => 0) .faultUB :=
    fun h => by nomatch h
  have hSub :=
    (hUncond (fun _ => 0) True.intro hNoUb).2 (.returned 0 ()) rfl
  nomatch hSub

/-- Non-vacuity witness: `SourceEntryPre paddingSrc` holds at `align = 8`. -/
theorem padding_entry_satisfiable :
    ∃ env : Nat → Nat, SourceEntryPre paddingSrc env :=
  ⟨fun _ => 8, allCtxFactsHold_of_evalConcrete _ _ rfl⟩

/-- Certified conditional refinement for `padding_needed_for` via `BoolCertCut`
with zero hypotheses. -/
theorem zc_padding_needed_for_refines :
    SemRefinesUnder (SourceEntryPre paddingSrc)
      (evalSourceBlockUnit paddingSrc)
      (evalCompiledBlockUnit paddingOpt) :=
  certGateCut_sound (blockOptGate 4)
    (x := paddingSrc) (y := paddingOpt) (w := paddingSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- Contract lifting for `padding_needed_for`: any caller guaranteeing
`1 ≤ word64 (env 1)` (`NonZeroUsize`) transfers `noAbort` and exact return
agreement from `paddingSrc` onto `paddingOpt`. -/
@[expose] def paddingContract : SimpleContract (Nat → Nat) Nat Unit :=
  { pre := fun env => 1 ≤ word64 (env 1)
    effects := { terminates := true, noUnwind := true, noAbort := true }
    postReturn := fun env ret _ =>
      evalArenaNode env paddingArena 7 = .val ret }

theorem zc_padding_needed_for_contract_lifted :
    SatisfiesContract (evalCompiledBlockUnit paddingOpt) paddingContract := by
  refine liftContractAlongRefinement ?_ ?_ zc_padding_needed_for_refines
  · intro env hPre idx f hNth
    cases idx with
    | succ _ => nomatch hNth
    | zero =>
      injection hNth with hf
      rw [← hf]
      intro a b hVa hVb
      have hN1 :
          listNthOpt (evalArena env paddingArena) 1 =
            some (.val (word64 (env 1))) := by
        have hEq := (evalArenaNode_eq env paddingArena rfl rfl (nid := 1)
          (d := { op := .var 1, args := [] })).1
        exact hEq
      have hN2 :
          listNthOpt (evalArena env paddingArena) 2 = some (.val 1) := by
        have hEq := (evalArenaNode_eq env paddingArena rfl rfl (nid := 2)
          (d := { op := .lit 1, args := [] })).1
        exact hEq
      dsimp only [paddingSrc] at hVa hVb
      rw [hN1] at hVa
      rw [hN2] at hVb
      injection hVa with hPa
      injection hPa with hEqA
      injection hVb with hPb
      injection hPb with hEqB
      rw [← hEqA, ← hEqB]
      exact hPre
  · intro env hPre
    have hGuardOk :
        evalGuards (evalArena env paddingArena) [.subNoUnderflow 1 2] =
          some true := by
      have hN1 :
          listNthOpt (evalArena env paddingArena) 1 =
            some (.val (word64 (env 1))) :=
        (evalArenaNode_eq env paddingArena rfl rfl (nid := 1)
          (d := { op := .var 1, args := [] })).1
      have hN2 :
          listNthOpt (evalArena env paddingArena) 2 = some (.val 1) :=
        (evalArenaNode_eq env paddingArena rfl rfl (nid := 2)
          (d := { op := .lit 1, args := [] })).1
      dsimp only [evalGuards, List.foldr, evalGuard]
      rw [hN1, hN2]
      dsimp only
      rw [(nat_ble_iff 1 (word64 (env 1))).2 hPre]
    have ⟨v7, hV7⟩ :
        ∃ v7, evalArenaNode env paddingArena 7 = .val v7 := by
      have hEv7 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 7)
        (d := { op := .land, args := [5, 6] })).2
      have hEv5 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 5)
        (d := { op := .bitNot, args := [4] })).2
      have hEv4 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 4)
        (d := { op := .subWrap, args := [0, 2] })).2
      have hEv6 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 6)
        (d := { op := .subWrap, args := [1, 2] })).2
      have hEv0 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 0)
        (d := { op := .var 0, args := [] })).2
      have hEv1 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 1)
        (d := { op := .var 1, args := [] })).2
      have hEv2 := (evalArenaNode_eq env paddingArena rfl rfl (nid := 2)
        (d := { op := .lit 1, args := [] })).2
      dsimp only [List.map] at hEv7 hEv5 hEv4 hEv6
      rw [hEv0, hEv2] at hEv4
      rw [hEv4] at hEv5
      rw [hEv1, hEv2] at hEv6
      rw [hEv5, hEv6] at hEv7
      exact ⟨_, hEv7⟩
    refine ⟨fun hUb => ?_, fun _ hDiv => ?_, fun _ hAb => ?_,
      fun v _ hRet => ?_⟩
    · dsimp only [evalSourceBlockUnit, paddingSrc, evalBlockWithGuards] at hUb
      rw [hGuardOk, hV7] at hUb
      nomatch hUb
    · dsimp only [evalSourceBlockUnit, paddingSrc, evalBlockWithGuards] at hDiv
      rw [hGuardOk, hV7] at hDiv
      nomatch hDiv
    · dsimp only [evalSourceBlockUnit, paddingSrc, evalBlockWithGuards] at hAb
      rw [hGuardOk, hV7] at hAb
      nomatch hAb
    · dsimp only [evalSourceBlockUnit, paddingSrc, evalBlockWithGuards] at hRet
      rw [hGuardOk, hV7] at hRet
      injection hRet with hv _
      dsimp only [paddingContract]
      rw [hv]
      exact hV7

/-! ## 4. Model 3: 16-Guard Exp-Golomb Expression Block (`ueGolomb`) -/

/-- Expression arena for Exp-Golomb bit-cursor and codeNum calculation using
wrapping arithmetic paired with 16 value-evaluated `GuardCond`s. -/
@[expose] def ueGolombArena : List DagNode :=
  [ { op := .var 0, args := [] },        -- 0: lz
    { op := .var 1, args := [] },        -- 1: suffix
    { op := .var 2, args := [] },        -- 2: bitIdx
    { op := .lit 1, args := [] },        -- 3: 1
    { op := .lit 6, args := [] },        -- 4: 6
    { op := .lit 3, args := [] },        -- 5: 3
    { op := .lit 9, args := [] },        -- 6: 9
    { op := .shl, args := [3, 0] },      -- 7: 1 <<< lz
    { op := .subWrap, args := [7, 3] },  -- 8: (1 <<< lz) -_w 1
    { op := .addWrap, args := [8, 1] },  -- 9: ((1 <<< lz) -_w 1) +_w suffix
    { op := .lshr, args := [2, 4] },     -- 10: bitIdx >>> 6
    { op := .lshr, args := [10, 5] },    -- 11: (bitIdx >>> 6) >>> 3
    { op := .addWrap, args := [9, 11] }, -- 12: src
    { op := .subNuw, args := [7, 3] },   -- 13: (1 <<< lz) -_nuw 1
    { op := .addNuw, args := [8, 1] },   -- 14: ((1 <<< lz) -_w 1) +_nuw suffix
    { op := .lshr, args := [2, 6] },     -- 15: bitIdx >>> 9
    { op := .addWrap, args := [9, 15] } ]-- 16: opt

/-- 16 value-evaluated shift, underflow, overflow, and range guards. -/
@[expose] def ueGolomb16Guards : List GuardCond :=
  [ .shiftLt64 0, .shiftLt64 4, .shiftLt64 5,
    .subNoUnderflow 7 3, .addNoOverflow 8 1,
    .ltPow2 0 5, .ltPow2 0 6, .ltPow2 0 7, .ltPow2 0 8, .ltPow2 0 9,
    .ltPow2 0 10, .ltPow2 0 11, .ltPow2 0 12, .ltPow2 0 13, .ltPow2 0 14,
    .ltPow2 0 15 ]

@[expose] def ueGolombCandidates : List CandidateFact :=
  [ { tier := .proven, fact := .ltPow2 0 5 },
    { tier := .proven, fact := .ltPow2 4 3 },
    { tier := .proven, fact := .ltPow2 5 3 },
    { tier := .proven, fact := .subNoUnderflow 7 3 },
    { tier := .proven, fact := .addNoOverflow 8 1 } ]

/-- Incomplete manifest where `.ltPow2 0 5` (`lz < 32`) was only fuzzed rather
than proven, leaving `shiftLt64 0` and the `ltPow2 0 *` guards undischarged. -/
@[expose] def ueGolombIncompleteCandidates : List CandidateFact :=
  [ { tier := .fuzz, fact := .ltPow2 0 5 },
    { tier := .proven, fact := .ltPow2 4 3 },
    { tier := .proven, fact := .ltPow2 5 3 },
    { tier := .proven, fact := .subNoUnderflow 7 3 },
    { tier := .proven, fact := .addNoOverflow 8 1 } ]

@[expose] def ueGolombSrc : SourceBlockUnit :=
  { guards := ueGolomb16Guards
    arena := ueGolombArena
    srcRetId := 12
    candidates := ueGolombCandidates }

@[expose] def ueGolombOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := ueGolombArena
    retId := 16 }

@[expose] def ueGolombSteps : List DagStep :=
  [ .biRule (.promoteSubNuw 3) [7, 3] 8 13,   -- 0: subWrap = subNuw
    .dirRule .dropSubNuw [7, 3] 13 8,         -- 1: subNuw ⊑ subWrap
    .trans 0 1,                               -- 2: node 8 ⊑ node 8
    .biRule (.promoteAddNuw 4) [8, 1] 9 14,   -- 3: addWrap = addNuw
    .dirRule .dropAddNuw [8, 1] 14 9,         -- 4: addNuw ⊑ addWrap
    .trans 3 4,                               -- 5: node 9 ⊑ node 9
    .biRule .shrShrAdd [2, 10, 4, 5, 6] 11 15,-- 6: shr2 = bitIdx >>> 9
    .cong 12 16 [5, 6] ]                      -- 7: src ⊑ opt

/-- Non-vacuity witness: all `ueGolombCandidates` hold at `env := fun _ => 2`.
-/
theorem ueGolomb_entry_satisfiable :
    ueGolomb16Guards.length = 16 ∧
    ∃ env : Nat → Nat, SourceEntryPre ueGolombSrc env :=
  ⟨rfl, ⟨fun _ => 2, allCtxFactsHold_of_evalConcrete _ _ rfl⟩⟩

/-- Positive receipt: all 16 value-evaluated guards in `ueGolombSrc` discharge
via `BoolCertCut`, establishing `SemRefinesUnder` with zero hypotheses. -/
theorem h264_read_ue_golomb_16assert_collapse :
    SemRefinesUnder (SourceEntryPre ueGolombSrc)
      (evalSourceBlockUnit ueGolombSrc)
      (evalCompiledBlockUnit ueGolombOpt) :=
  certGateCut_sound (blockOptGate 4)
    (x := ueGolombSrc) (y := ueGolombOpt) (w := ueGolombSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- Refutation 8: Demoting `.ltPow2 0 5` from `.proven` to `.fuzz` causes
`blockOptGate` to reject `ueGolombOpt`. -/
theorem neg8_ueGolombMissingShiftFact_rejected :
    evalGate (E := Unit) (blockOptGate 4)
      { ueGolombSrc with candidates := ueGolombIncompleteCandidates }
      (.candidate ueGolombOpt ueGolombSteps) = .error .rejectedByChecker :=
  rfl

/-! ## 5. Model 4: Stride-Mask and Butterfly Portfolio (`idct4Fit`) -/

@[expose] def idct4FitArena : List DagNode :=
  [ { op := .var 0, args := [] },        -- 0: stride
    { op := .var 1, args := [] },        -- 1: bitIdx
    { op := .var 2, args := [] },        -- 2: acc
    { op := .lit 1, args := [] },        -- 3: 1
    { op := .lit mask61, args := [] },   -- 4: mask61 (2^61 - 1)
    { op := .lit 4, args := [] },        -- 5: 4
    { op := .lit 2, args := [] },        -- 6: 2
    { op := .lit 6, args := [] },        -- 7: 6
    { op := .lit 3, args := [] },        -- 8: 3
    { op := .lit 9, args := [] },        -- 9: 9
    { op := .lshr, args := [0, 3] },     -- 10: s = stride >>> 1
    { op := .land, args := [10, 4] },    -- 11: s & mask61
    { op := .mulWrap, args := [11, 5] }, -- 12: (s & mask61) * 4
    { op := .mulWrap, args := [10, 5] }, -- 13: s * 4
    { op := .shl, args := [10, 6] },     -- 14: s <<< 2
    { op := .lshr, args := [1, 7] },     -- 15: bitIdx >>> 6
    { op := .lshr, args := [15, 8] },    -- 16: (bitIdx >>> 6) >>> 3
    { op := .lshr, args := [1, 9] },     -- 17: bitIdx >>> 9
    { op := .addWrap, args := [12, 16] },-- 18: (s & mask61)*4 + shr2
    { op := .addWrap, args := [14, 16] },-- 19: (s <<< 2) + shr2
    { op := .addWrap, args := [14, 17] },-- 20: (s <<< 2) + (bitIdx >>> 9)
    { op := .addWrap, args := [17, 14] },-- 21: (bitIdx >>> 9) + (s <<< 2)
    { op := .addWrap, args := [18, 2] }, -- 22: src = idxExpr +_w acc
    { op := .addNuw, args := [21, 2] },  -- 23: mid = optIdx +_nuw acc
    { op := .addWrap, args := [21, 2] }, -- 24: opt = optIdx +_w acc
    { op := .addNuw, args := [18, 2] } ] -- 25: idxExpr +_nuw acc

@[expose] def idct4FitCandidates : List CandidateFact :=
  [ { tier := .proven, fact := .ltPow2 10 61 },
    { tier := .proven, fact := .addNoOverflow 18 2 },
    { tier := .proven, fact := .ltPow2 3 3 },
    { tier := .proven, fact := .ltPow2 7 3 } ]

@[expose] def idct4FitCtx : List CtxFact :=
  extractProvenFacts idct4FitCandidates

@[expose] def idct4FitSrc : SourceBlockUnit :=
  { guards :=
      [ .ltPow2 10 61, .addNoOverflow 18 2, .shiftLt64 3, .shiftLt64 7 ]
    arena := idct4FitArena
    srcRetId := 22
    candidates := idct4FitCandidates }

@[expose] def idct4FitEgglogOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := idct4FitArena
    retId := 24 }

@[expose] def idct4FitAegraphOpt : CompiledBlockUnit :=
  { guardsOut := []
    arenaOut := idct4FitArena
    retId := 23 }

@[expose] def idct4FitAegraphSteps : List DagStep :=
  [ .biRule (.promoteAddNuw 1) [18, 2] 22 25,    -- 0: node 22 = node 25
    .biRule (.maskPow2Elide 0 61) [10, 4] 11 10, -- 1: (s & mask61) = s
    .refl 5,                                     -- 2: 4 = 4
    .cong 12 13 [1, 2],                          -- 3: (s & mask61)*4 = s*4
    .biRule .mul4ToShl2 [10, 5, 6] 13 14,        -- 4: s*4 = s<<<2
    .trans 3 4,                                  -- 5: (s & mask61)*4 = s<<<2
    .refl 16,                                    -- 6: shr2 = shr2
    .cong 18 19 [5, 6],                          -- 7: node 18 = node 19
    .biRule .shrShrAdd [1, 15, 7, 8, 9] 16 17,   -- 8: shr2 = bitIdx >>> 9
    .refl 14,                                    -- 9: s<<<2 = s<<<2
    .cong 19 20 [9, 8],                          -- 10: node 19 = node 20
    .trans 7 10,                                 -- 11: node 18 = node 20
    .biRule .addComm [14, 17] 20 21,             -- 12: node 20 = node 21
    .trans 11 12,                                -- 13: node 18 = node 21
    .refl 2,                                     -- 14: acc = acc
    .cong 25 23 [13, 14],                        -- 15: node 25 = node 23
    .trans 0 15 ]                                -- 16: src = mid (node 23)

@[expose] def idct4FitEgglogSteps : List DagStep :=
  idct4FitAegraphSteps ++
  [ .dirRule .dropAddNuw [21, 2] 23 24,          -- 17: node 23 ⊑ node 24
    .trans 16 17 ]                               -- 18: src ⊑ opt (node 24)

/-- Non-vacuity witness: `SourceEntryPre idct4FitSrc` holds at `env := 0`,
proved via `evalArenaNode_eq` without unfolding the 26-node arena. -/
theorem idct4Fit_entry_satisfiable :
    ∃ env : Nat → Nat, SourceEntryPre idct4FitSrc env := by
  refine ⟨fun _ => 0, ?_⟩
  let e0 : Nat → Nat := fun _ => 0
  have hN0 : listNthOpt (evalArena e0 idct4FitArena) 0 = some (.val 0) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 0) (d := { op := .var 0, args := [] })).1
  have hN1 : listNthOpt (evalArena e0 idct4FitArena) 1 = some (.val 0) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 1) (d := { op := .var 1, args := [] })).1
  have hN2 : listNthOpt (evalArena e0 idct4FitArena) 2 = some (.val 0) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 2) (d := { op := .var 2, args := [] })).1
  have hN3 : listNthOpt (evalArena e0 idct4FitArena) 3 = some (.val 1) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 3) (d := { op := .lit 1, args := [] })).1
  have hN4 : listNthOpt (evalArena e0 idct4FitArena) 4 = some (.val mask61) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 4) (d := { op := .lit mask61, args := [] })).1
  have hN5 : listNthOpt (evalArena e0 idct4FitArena) 5 = some (.val 4) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 5) (d := { op := .lit 4, args := [] })).1
  have hN7 : listNthOpt (evalArena e0 idct4FitArena) 7 = some (.val 6) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 7) (d := { op := .lit 6, args := [] })).1
  have hN8 : listNthOpt (evalArena e0 idct4FitArena) 8 = some (.val 3) :=
    (evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 8) (d := { op := .lit 3, args := [] })).1
  have hN10 : listNthOpt (evalArena e0 idct4FitArena) 10 = some (.val 0) := by
    have ⟨hEq, _⟩ := evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 10) (d := { op := .lshr, args := [0, 3] })
    dsimp only [List.map, evalArenaNode] at hEq
    rw [hN0, hN3] at hEq
    exact hEq
  have hN11 : listNthOpt (evalArena e0 idct4FitArena) 11 = some (.val 0) := by
    have ⟨hEq, _⟩ := evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 11) (d := { op := .land, args := [10, 4] })
    dsimp only [List.map, evalArenaNode] at hEq
    rw [hN10, hN4] at hEq
    exact hEq
  have hN12 : listNthOpt (evalArena e0 idct4FitArena) 12 = some (.val 0) := by
    have ⟨hEq, _⟩ := evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 12) (d := { op := .mulWrap, args := [11, 5] })
    dsimp only [List.map, evalArenaNode] at hEq
    rw [hN11, hN5] at hEq
    exact hEq
  have hN15 : listNthOpt (evalArena e0 idct4FitArena) 15 = some (.val 0) := by
    have ⟨hEq, _⟩ := evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 15) (d := { op := .lshr, args := [1, 7] })
    dsimp only [List.map, evalArenaNode] at hEq
    rw [hN1, hN7] at hEq
    exact hEq
  have hN16 : listNthOpt (evalArena e0 idct4FitArena) 16 = some (.val 0) := by
    have ⟨hEq, _⟩ := evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 16) (d := { op := .lshr, args := [15, 8] })
    dsimp only [List.map, evalArenaNode] at hEq
    rw [hN15, hN8] at hEq
    exact hEq
  have hN18 : listNthOpt (evalArena e0 idct4FitArena) 18 = some (.val 0) := by
    have ⟨hEq, _⟩ := evalArenaNode_eq e0 idct4FitArena rfl rfl
      (nid := 18) (d := { op := .addWrap, args := [12, 16] })
    dsimp only [List.map, evalArenaNode] at hEq
    rw [hN12, hN16] at hEq
    exact hEq
  intro idx f hNth
  cases idx with
  | zero =>
    dsimp only [SourceEntryPre, EntryFactsHold, idct4FitSrc,
      idct4FitCandidates, extractProvenFacts, List.foldr, listNthOpt] at hNth
    injection hNth with hF
    rw [← hF]
    intro v hV
    dsimp only [idct4FitSrc] at hV
    rw [hN10] at hV
    injection hV with hPv
    injection hPv with hEqV
    rw [← hEqV]
    exact (nat_blt_iff 0 (Nat.pow 2 61)).1 rfl
  | succ k1 =>
    cases k1 with
    | zero =>
      dsimp only [SourceEntryPre, EntryFactsHold, idct4FitSrc,
        idct4FitCandidates, extractProvenFacts, List.foldr, listNthOpt] at hNth
      injection hNth with hF
      rw [← hF]
      intro a b hVa hVb
      dsimp only [idct4FitSrc] at hVa hVb
      rw [hN18] at hVa
      rw [hN2] at hVb
      injection hVa with hPa
      injection hPa with hEqA
      injection hVb with hPb
      injection hPb with hEqB
      rw [← hEqA, ← hEqB]
      exact (nat_blt_iff 0 u64Mod).1 rfl
    | succ k2 =>
      cases k2 with
      | zero =>
        dsimp only [SourceEntryPre, EntryFactsHold, idct4FitSrc,
          idct4FitCandidates, extractProvenFacts, List.foldr,
          listNthOpt] at hNth
        injection hNth with hF
        rw [← hF]
        intro v hV
        dsimp only [idct4FitSrc] at hV
        rw [hN3] at hV
        injection hV with hPv
        injection hPv with hEqV
        rw [← hEqV]
        exact (nat_blt_iff 1 8).1 rfl
      | succ k3 =>
        cases k3 with
        | zero =>
          dsimp only [SourceEntryPre, EntryFactsHold, idct4FitSrc,
            idct4FitCandidates, extractProvenFacts, List.foldr,
            listNthOpt] at hNth
          injection hNth with hF
          rw [← hF]
          intro v hV
          dsimp only [idct4FitSrc] at hV
          rw [hN7] at hV
          injection hV with hPv
          injection hPv with hEqV
          rw [← hEqV]
          exact (nat_blt_iff 6 8).1 rfl
        | succ _ =>
          dsimp only [SourceEntryPre, EntryFactsHold, idct4FitSrc,
            idct4FitCandidates, extractProvenFacts, List.foldr,
            listNthOpt] at hNth
          nomatch hNth

/-- Refutation 9: `maskPow2Elide` fails closed when `.ltPow2` guards node `1`
instead of node `10`. -/
theorem neg9_wrongGuardedNode_rejected :
    verifyDagGoal idct4FitArena [.ltPow2 1 61]
      [.biRule (.maskPow2Elide 0 61) [10, 4] 11 10] 11 10 .eqExact = false :=
  rfl

/-- Portfolio receipt for `idct4Fit`: skips a wrong proof (`.refl 0`) and a
trapped producer, selects `idct4FitEgglogOpt`, and establishes `SemRefinesUnder`
with zero hypotheses. -/
theorem h264_idct4_fit_portfolio_refines :
    let portfolio :=
      [ RawOutcome.candidate idct4FitEgglogOpt ([.refl 0] : List DagStep),
        RawOutcome.trapped (E := Unit),
        RawOutcome.candidate idct4FitEgglogOpt idct4FitEgglogSteps,
        RawOutcome.candidate idct4FitAegraphOpt idct4FitAegraphSteps ]
    let selected :=
      withFallback idct4FitSrc
        (firstAccepted (blockOptGate 4) idct4FitSrc portfolio)
        baselineIdentityPass.run
    selected = idct4FitEgglogOpt ∧
    SemRefinesUnder (SourceEntryPre idct4FitSrc)
      (evalSourceBlockUnit idct4FitSrc)
      (evalCompiledBlockUnit selected) :=
  ⟨rfl,
   withFallback_firstAccepted_sound (blockOptGate 4) idct4FitSrc
     [ RawOutcome.candidate idct4FitEgglogOpt [.refl 0],
       RawOutcome.trapped (E := Unit),
       RawOutcome.candidate idct4FitEgglogOpt idct4FitEgglogSteps,
       RawOutcome.candidate idct4FitAegraphOpt idct4FitAegraphSteps ]
     baselineIdentityPass.run True.intro baselineIdentityPass.sound⟩

@[expose] def SsaNodeBounded (arena : List DagNode) (s : Nat) : Prop :=
  s < arena.length

@[expose] def SsaStepRefines (arena : List DagNode) (ctx : List CtxFact)
    (s : Nat) (_ : Nat × List DagStep) (s' : Nat) : Prop :=
  ∀ env : Nat → Nat,
    AllCtxFactsHold (evalArena env arena) ctx →
    refinesPoison (evalArenaNode env arena s) (evalArenaNode env arena s')

/-- Pass-sequence gate parameterized over `arena` and `ctx` for `foldHintSteps`.
-/
@[expose] def ssaPassStepGate (arena : List DagNode) (ctx : List CtxFact) :
    CertifiedGate (Nat × (Nat × List DagStep)) Nat Unit
      (fun su => SsaNodeBounded arena su.1)
      (fun su s' =>
        SsaNodeBounded arena s' ∧
        SsaStepRefines arena ctx su.1 su.2 s') where
  maxWitness := fun _ => 0
  wSize := fun _ => 0
  check := fun su s' _ =>
    Nat.beq s' su.2.1 &&
    Nat.blt s' arena.length &&
    verifyDagGoal arena ctx su.2.2 su.1 s' .refines
  sound := by
    intro su s' _ _ _ hChk
    have hDag := bool_and_right hChk
    have hLt := (nat_blt_iff _ _).1 (bool_and_right (bool_and_left hChk))
    exact ⟨hLt, fun env hCtx =>
      verifyDagGoal_sound env arena ctx su.2.2 su.1 s' .refines hCtx hDag⟩

theorem ssaFallback_sound (arena : List DagNode) (ctx : List CtxFact)
    (su : Nat × (Nat × List DagStep)) (hInv : SsaNodeBounded arena su.1) :
    SsaNodeBounded arena su.1 ∧ SsaStepRefines arena ctx su.1 su.2 su.1 :=
  ⟨hInv, fun env _ => refinesPoison_refl (evalArenaNode env arena su.1)⟩

/-- `foldHintSteps` canary: proves both exact step selection (`= 24` across a
rejected mid-sequence step `(99, [.refl 0])`) and invariant preservation
(`SsaNodeBounded`) via `Anneal.Hybrid.foldHintSteps_preserves_inv`. -/
theorem h264_idct4_foldHintSteps_preserves_inv_and_selects :
    let hints : List (Nat × List DagStep) :=
      [ (23, idct4FitAegraphSteps),
        (99, [.refl 0]),
        (24, [.dirRule .dropAddNuw [21, 2] 23 24]) ]
    let out :=
      foldHintSteps
        (Inv := SsaNodeBounded idct4FitArena)
        (StepRel := SsaStepRefines idct4FitArena idct4FitCtx)
        (ssaPassStepGate idct4FitArena idct4FitCtx)
        (fun _ u => RawOutcome.candidate (E := Unit) u.1 ())
        (fun su => su.1) 22 hints
    out = 24 ∧ SsaNodeBounded idct4FitArena out :=
  ⟨rfl,
   foldHintSteps_preserves_inv
     (Inv := SsaNodeBounded idct4FitArena)
     (StepRel := SsaStepRefines idct4FitArena idct4FitCtx)
     (ssaPassStepGate idct4FitArena idct4FitCtx)
     (fun _ u => RawOutcome.candidate (E := Unit) u.1 ())
     (fun su => su.1)
     (ssaFallback_sound idct4FitArena idct4FitCtx)
     [ (23, idct4FitAegraphSteps),
       (99, [.refl 0]),
       (24, [.dirRule .dropAddNuw [21, 2] 23 24]) ]
     22 (@Nat.le_of_ble_eq_true 23 26 rfl)⟩

/-! ## 6. Two-Pass `composePassGates` + `verifiedPassToGate` Canary -/

@[expose] def identityBlockPass :
    VerifiedPass CompiledBlockUnit CompiledBlockUnit (fun _ => True)
      (fun m z =>
        SemRefines (evalCompiledBlockUnit m) (evalCompiledBlockUnit z)) where
  run := fun m => m
  sound := fun _ _ => semRefines_refl _

@[expose] def twoPassDstLayoutGate :
    CertifiedGate SourceBlockUnit CompiledBlockUnit
      (CompiledBlockUnit × List DagStep × Unit)
      (fun _ => True)
      (fun src z =>
        SemRefinesUnder (SourceEntryPre src)
          (evalSourceBlockUnit src) (evalCompiledBlockUnit z)) :=
  composePassGates
    { maxWitness := (blockOptGate 2).maxWitness
      wSize := (blockOptGate 2).wSize
      check := (blockOptGate 2).check
      sound := fun x m w hPre hCap hChk =>
        ⟨trivial, (blockOptGate 2).sound x m w hPre hCap hChk⟩ }
    (verifiedPassToGate identityBlockPass CompiledBlockUnit.beq
      compiledBlockUnit_eq_of_beq)
    (fun m => m.arenaOut.length)
    (fun src => src.arena.length)
    (fun src _ _ h12 h23 env hEnt hNoUb => by
      have ⟨hMidNoUb, hSub12⟩ := h12 env hEnt hNoUb
      have ⟨hZNoUb, hSub23⟩ := h23 env True.intro hMidNoUb
      exact ⟨hZNoUb, fun out hZ => hSub12 out (hSub23 out hZ)⟩)

theorem dstLayoutSize_twoPass_composed_refines :
    SemRefinesUnder (SourceEntryPre dstLayoutSizeSrc)
      (evalSourceBlockUnit dstLayoutSizeSrc)
      (evalCompiledBlockUnit dstLayoutSizeOpt) :=
  certGateCut_sound twoPassDstLayoutGate
    (x := dstLayoutSizeSrc) (y := dstLayoutSizeOpt)
    (w := (dstLayoutSizeOpt, dstLayoutSizeSteps, ())) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-! ## 7. Simplified Abstract Expression and Guard Cost Canary -/

/-- Simplified abstract operator weight (wide 64-bit constants `>= 2 ^ 32`
carry weight `10`, 32-bit constants `5`, variables `0`, `mulWrap` `4`, `nuw`
operators `6`, and other ALU ops `3`). -/
@[expose] def abstractOpCost : SsaOp → Nat
  | .var _ => 0
  | .lit w =>
    match Nat.blt w (Nat.pow 2 32) with
    | true => 5
    | false => 10
  | .mulWrap => 4
  | .addNuw => 6
  | .subNuw => 6
  | _ => 3

/-- Simplified abstract penalty per surviving runtime assertion guard. -/
@[expose] def abstractGuardCost : Nat := 44

@[expose] def natMemList (x : Nat) (xs : List Nat) : Bool :=
  List.foldr (fun y acc => Nat.beq x y || acc) false xs

@[expose] def addUniqueNats (xs acc0 : List Nat) : List Nat :=
  List.foldr
    (fun x acc =>
      match natMemList x acc with
      | true => acc
      | false => x :: acc)
    acc0 xs

/-- Single-pass reverse-topological live-cone collector from `retId` (`0`
`._unsafe_rec`). -/
@[expose] def liveNodeIds (arena : List DagNode) (retId : Nat) : List Nat :=
  List.foldl
    (fun live nid =>
      match natMemList nid live with
      | false => live
      | true =>
        match listNthOpt arena nid with
        | none => live
        | some d => addUniqueNats d.args live)
    [retId]
    (@Nat.rec (fun _ => List Nat) [] (fun k xs => k :: xs) arena.length)

/-- Simplified abstract cost over surviving guards and live DAG nodes. This is
an abstract model illustrating that `blockOptGate` certifies `SemRefinesUnder`
independently of an untrusted producer's cost function, not a measurement of
compiled machine-code bytes. -/
@[expose] def estimateAbstractBlockCost (u : CompiledBlockUnit) : Nat :=
  u.guardsOut.length * abstractGuardCost +
  List.foldl
    (fun acc nid =>
      match listNthOpt u.arenaOut nid with
      | none => acc
      | some d => acc + abstractOpCost d.op)
    0
    (liveNodeIds u.arenaOut u.retId)

@[expose] def checkNatBlt (p : Nat × Nat) : Bool :=
  Nat.blt p.1 p.2

theorem lt_of_boolCertCut {a b : Nat}
    (h : Anneal.Framework.StepWp.BoolCertCut checkNatBlt (a, b)) :
    a < b := by
  have h0 := Anneal.Framework.StepWp.BoolCertCut.unseal h
  exact (nat_blt_iff a b).1 h0

theorem abstractCost_boolCertCut_shrink :
    SemRefinesUnder (SourceEntryPre paddingSrc)
      (evalSourceBlockUnit paddingSrc)
      (evalCompiledBlockUnit paddingOpt) ∧
    SemRefinesUnder (SourceEntryPre ueGolombSrc)
      (evalSourceBlockUnit ueGolombSrc)
      (evalCompiledBlockUnit ueGolombOpt) ∧
    SemRefinesUnder (SourceEntryPre idct4FitSrc)
      (evalSourceBlockUnit idct4FitSrc)
      (evalCompiledBlockUnit idct4FitEgglogOpt) ∧
    estimateAbstractBlockCost paddingOpt <
      estimateAbstractBlockCost (baselineIdentityPass.run paddingSrc) ∧
    estimateAbstractBlockCost ueGolombOpt <
      estimateAbstractBlockCost (baselineIdentityPass.run ueGolombSrc) ∧
    estimateAbstractBlockCost idct4FitEgglogOpt <
      estimateAbstractBlockCost (baselineIdentityPass.run idct4FitSrc) :=
  ⟨zc_padding_needed_for_refines,
   h264_read_ue_golomb_16assert_collapse,
   certGateCut_sound (blockOptGate 4)
     (x := idct4FitSrc) (y := idct4FitEgglogOpt) (w := idct4FitEgglogSteps)
     True.intro (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   lt_of_boolCertCut
     (Anneal.Framework.StepWp.BoolCertCut.seal checkNatBlt (_, _) rfl),
   lt_of_boolCertCut
     (Anneal.Framework.StepWp.BoolCertCut.seal checkNatBlt (_, _) rfl),
   lt_of_boolCertCut
     (Anneal.Framework.StepWp.BoolCertCut.seal checkNatBlt (_, _) rfl)⟩

end Anneal.Backend.Canaries

end
