import ToyPacked.Instances

/-!
# Positive and negative examples for the definitions (all fully proved)
-/

namespace Toy.Packed

/-! `resolve` and `typeAt` -/

/-- `resolve` sums offsets along the whole path: `x.1.0` of `Q` is the `R4` at offset `1 + 0`. -/
theorem resolve_pos : resolve envQ LQ 3 [1, 0] = some (1, 1) := by decide
/-- `resolve` rejects a path that does not follow the types (`Q` has no field 2). -/
theorem resolve_neg : resolve envQ LQ 3 [2] = none := by decide
/-- `typeAt` follows field types. -/
theorem typeAt_pos : typeAt envQ 3 [1, 0] = some 1 := by decide
/-- `typeAt` rejects projecting out of a non-aggregate. -/
theorem typeAt_neg : typeAt envQ 1 [0] = none := by decide

/-! `effAlign` and `typeGA` -/

/-- A `packed(2)` parent caps an `align(8)` field at 2. -/
theorem effAlign_pos : effAlign envP2 3 1 = 2 := by decide
/-- A non-packed parent does not cap: the `R4` field of `S` keeps alignment 4. -/
theorem effAlign_neg : effAlign envQ 2 0 = 4 := by decide
/-- A field index out of range has effective alignment 0 (no field to position). -/
theorem effAlign_out_of_range : effAlign envQ 2 5 = 0 := by decide
/-- A packed grandparent caps the guaranteed alignment of a field of a non-packed struct. -/
theorem typeGA_pos : typeGA envQ 3 [1, 0] (envQ.align 3) = 1 := by decide
/-- Without a packed parent there is no cap. -/
theorem typeGA_neg : typeGA envQ 2 [0] (envQ.align 2) = 4 := by decide

/-! `Misalignable`, `IsPow2`, `PowTwoAligns`, `RespectsPacking`, `pathSteps`, `NoRepeatStep`,
`FieldIdsDecreasing` -/

/-- Offset 1 from a base aligned to 1 can be misaligned for alignment 4. -/
theorem misalignable_pos : Misalignable 1 4 1 := ⟨0, Nat.dvd_zero 1, by decide⟩
/-- Offset 8 from a base aligned to 4 is always aligned for alignment 4. -/
theorem misalignable_neg : ¬ Misalignable 4 4 8 := by decide
/-- Degenerate alignment 0: only address 0 is aligned, so offset 1 is misalignable. -/
theorem misalignable_align_zero : Misalignable 1 0 1 := by decide
theorem isPow2_pos : IsPow2 8 := by decide
theorem isPow2_neg_zero : ¬ IsPow2 0 := by decide
theorem isPow2_neg_three : ¬ IsPow2 3 := by decide
theorem powTwoAligns_pos : PowTwoAligns envP2 := by decide
theorem powTwoAligns_neg : ¬ PowTwoAligns envW := by decide
theorem respectsPacking_pos : RespectsPacking envQ LQ := by decide
theorem respectsPacking_neg : ¬ RespectsPacking envRP LRP := by decide
/-- The steps of `x.1.0` in `Q`: field 1 of `Q` (id 3), then field 0 of `S` (id 2). -/
theorem pathSteps_pos : pathSteps envQ 3 [1, 0] = [(3, 1), (2, 0)] := by decide
/-- Steps stop where the path leaves the types. -/
theorem pathSteps_stop : pathSteps envQ 3 [2, 0] = [] := by decide
theorem noRepeatStep_pos : NoRepeatStep envQ 3 [1, 0] := by decide
/-- In the cyclic `C = packed { C }`, the path `[0]` repeats no step ... -/
theorem noRepeatStep_cyc_short : NoRepeatStep envCyc 0 [0] := by decide
/-- ... but the path `[0, 0]` takes step `(0, 0)` twice. -/
theorem noRepeatStep_neg : ¬ NoRepeatStep envCyc 0 [0, 0] := by decide
theorem fieldIdsDecreasing_pos : FieldIdsDecreasing envQ := by decide
theorem fieldIdsDecreasing_neg : ¬ FieldIdsDecreasing envCyc := by decide
/-- An acyclic environment listed out of topological order is rejected by `FieldIdsDecreasing`,
while its path repeats no step. -/
theorem fieldIdsDecreasing_rejects_envRev :
    ¬ FieldIdsDecreasing envRev ∧ NoRepeatStep envRev 0 [0] := by decide

/-! `needsDrop`, `AddrBlind` -/

/-- A packed struct containing a value with a destructor needs drop glue. -/
theorem needsDrop_pos : needsDrop envA 4 2 = true := by decide
/-- A struct of scalars has no drop glue. -/
theorem needsDrop_neg : needsDrop [tU8, ⟨1, true, .agg none [0, 0]⟩] 3 1 = false := by decide
theorem addrBlind_pos : AddrBlind envA 4 2 = true := by decide
theorem addrBlind_neg : AddrBlind envObs 4 2 = false := by decide
/-- A box is address-blind even if its pointee's destructor prints its address: the pointee does
not move with the box. -/
theorem addrBlind_box_pos : AddrBlind envBoxObs 5 2 = true := by decide

/-! `shimExists`, `callsShim`, `reach`, positions -/

theorem shimExists_pos : shimExists envB .boxFree 2 = true := by decide
/-- There is no box-free shim for a non-box type. -/
theorem shimExists_neg : shimExists envA .boxFree 1 = false := by decide
theorem callsShim_pos : callsShim envA 4 .dropGlue 2 = true := by decide
/-- Dropping a scalar calls no shim. -/
theorem callsShim_neg : callsShim envA 4 .dropGlue 0 = false := by decide
/-- Dropping `packed { u8, R4 }` may enter its drop glue and the drop glue of `R4`, not the
drop glue of `u8` (no drop glue) and no clone shim. -/
theorem reach_pos : reach envA 4 .dropGlue 2 = [(.dropGlue, 2), (.dropGlue, 1)] := by decide
/-- A program that only drops `x` has no clone positions: its positions are the source drop of
`x` and the drop of field 1 inside the drop glue of `packed { u8, R4 }`. -/
theorem positions_progInPlace :
    positions progInPlace =
      [⟨.src, 0, .dropGlue, 1, 2, [], 2, 0⟩, ⟨.shim .dropGlue 2, 2, .dropGlue, 1, 2, [1], 1, 1⟩] := by
  decide
/-- An empty source body has no positions. -/
theorem positions_empty : positions progEmptyU = [] := by decide
/-- The positions of `progBox`: the source drop of `z`, the source free of `x.1`, the source drop
of `y`, and the drop of the box field `z.1` (offset 1) inside the drop glue of
`packed { u8, Box<R4> }`. -/
theorem positions_progBox :
    positions progBox =
      [⟨.src, 0, .dropGlue, 1, 3, [], 3, 0⟩, ⟨.src, 2, .boxFree, 1, 3, [1], 2, 1⟩,
        ⟨.src, 3, .dropGlue, 4, 1, [], 1, 0⟩, ⟨.shim .dropGlue 3, 2, .dropGlue, 1, 3, [1], 2, 1⟩] := by
  decide
/-- The positions of `progEscape` (and of `progUserRef`): the source drop of `w` and the drop of
the field `w.1` (offset 1) inside the drop glue of `packed { u8, R4 }`; the raw client call (the
user reference) adds none. -/
theorem positions_progEscape :
    positions progEscape =
      [⟨.src, 0, .dropGlue, 1, 2, [], 2, 0⟩, ⟨.shim .dropGlue 2, 2, .dropGlue, 1, 2, [1], 1, 1⟩] ∧
    positions progUserRef =
      [⟨.src, 0, .dropGlue, 1, 2, [], 2, 0⟩, ⟨.shim .dropGlue 2, 2, .dropGlue, 1, 2, [1], 1, 1⟩] := by
  decide

/-! `refStep`, `obs`, `copies`, `NoUB`, `NoShimUB` -/

/-- An aligned reference creation produces no event in the reference semantics. -/
theorem refStep_pos : refStep .ref cfgNone .src 0 4 8 = ⟨[], true⟩ := by decide
/-- A misaligned unchecked reference creation is a UB event. -/
theorem refStep_neg : refStep .ref cfgNone .src 0 4 1 = ⟨[.ub .src 0], false⟩ := by decide
/-- A misaligned checked reference creation traps. -/
theorem refStep_trap :
    refStep .ref ⟨critNone, fun _ _ => 0, instrAll⟩ .src 0 4 1 = ⟨[.trap .src 0], false⟩ := by
  decide
/-- The ideal semantics never fails a reference creation. -/
theorem refStep_ideal : refStep .ideal cfgNone .src 0 4 1 = ⟨[], true⟩ := by decide
/-- An unaligned read through a raw pointer is not an alignment-relevant operation. -/
theorem readUnaligned_no_ub :
    (run .ref cfgNone ⟨envA, LA, [], [], [.readUnaligned 1 1]⟩).evs = [] := by decide
theorem obs_pos : obs [.copy ⟨.loc 0, []⟩, .dtor ⟨.loc 0, []⟩] = [.dtor ⟨.loc 0, []⟩] := by decide
theorem obs_neg : obs [.addrObs ⟨.loc 0, []⟩ 3] = [.addrObs ⟨.loc 0, []⟩ 3] := by decide
theorem copies_pos : copies [.copy ⟨.loc 0, []⟩, .dtor ⟨.loc 0, []⟩] = 1 := by decide
theorem noUB_pos : NoUB ⟨[.dtor ⟨.loc 0, []⟩, .trap .src 1], false⟩ := by decide
theorem noUB_neg : ¬ NoUB ⟨[.ub .src 0], false⟩ := by decide
theorem noShimUB_pos : NoShimUB ⟨[.ub .src 0], false⟩ := by decide
theorem noShimUB_neg : ¬ NoShimUB ⟨[.ub (.shim .dropGlue 1) 0], false⟩ := by decide
theorem noStuck_pos : NoStuck ⟨[.ub .src 0], false⟩ := by decide
theorem noStuck_neg : ¬ NoStuck ⟨[.stuck .src 0], false⟩ := by decide
/-- A raw call of a box-free shim for a non-box type is a no-op (the shim does not exist). -/
theorem rawCall_missing_shim_noop :
    (run .ref cfgNone ⟨envA, LA, [], [], [.rawCall .boxFree 1 1]⟩).evs = [] := by decide
/-- The same no-op call with a misaligned address satisfies `ClientPtrsAligned`, and it adds no
shim to `reachableShims`. -/
theorem rawCall_missing_shim_admitted :
    ClientPtrsAligned ⟨envA, LA, [], [], [.rawCall .boxFree 1 1]⟩ ∧
    reachableShims ⟨envA, LA, [], [], [.rawCall .boxFree 1 1]⟩ = [] := by decide

/-! Criteria -/

theorem critExact_pos : critExact envQ LQ .dropGlue 1 3 [1, 0] = true := by decide
theorem critExact_neg : critExact envOuter LOuter .dropGlue 2 3 [1, 2] = false := by decide
theorem critType_pos : critType envQ .dropGlue 1 3 [1, 0] = true := by decide
theorem critType_neg : critType envQ .dropGlue 4 2 [0] = false := by decide
theorem critLeaf_pos : critLeaf envA .dropGlue 1 2 [1] = true := by decide
theorem critLeaf_neg : critLeaf envQ .dropGlue 1 3 [1, 0] = false := by decide
/-- `packed(2)` containing an `align(8)` struct (which the toy permits): the type-based and the
offset-aware criteria agree on the nested `u64`, both staging it. -/
theorem critType_eq_critExact_packed2_align8 :
    PowTwoAligns envP2 ∧ RespectsPacking envP2 LP2 ∧
    critType envP2 .dropGlue 2 3 [1, 0] = true ∧ critExact envP2 LP2 .dropGlue 2 3 [1, 0] = true := by
  decide
theorem dropsOnly_pos : dropsOnly (critType envB) .dropGlue 1 3 [1] = true := by decide
theorem dropsOnly_neg : dropsOnly (critType envB) .boxFree 1 3 [1] = false := by decide

/-! Hypothesis predicates -/

theorem critCovers_pos : CritCovers progInPlace (cfgType envA) := by decide
theorem critCovers_neg : ¬ CritCovers progInPlace cfgNone := by decide
theorem stagedSized_pos : StagedSized progInPlace (cfgType envA) := by decide
theorem stagedSized_neg : ¬ StagedSized progU (cfgType envU) := by decide
theorem stagedAddrBlind_pos : StagedAddrBlind progInPlace (cfgType envA) := by decide
theorem stagedAddrBlind_neg : ¬ StagedAddrBlind progObs (cfgType envObs) := by decide
theorem tempsAligned_pos : TempsAligned progInPlace (cfgType envA) := by decide
theorem tempsAligned_neg :
    ¬ TempsAligned progInPlace ⟨critType envA, fun _ _ => 2, instrNone⟩ := by decide
theorem frameAligned_pos : FrameAligned progInPlace := by decide
theorem frameAligned_neg : ¬ FrameAligned progMisFrame := by decide
theorem safeSrc_pos : SafeSrc progInPlace := by decide
theorem safeSrc_neg : ¬ SafeSrc progClient := by decide
theorem clientPtrsAligned_pos : ClientPtrsAligned progMixed := by decide
theorem clientPtrsAligned_neg : ¬ ClientPtrsAligned progClient := by decide
theorem srcRefsInstrumented_pos :
    SrcRefsInstrumented progMixed ⟨critType envA, fun _ _ => 16, instrSrc⟩ := by decide
theorem srcRefsInstrumented_neg : ¬ SrcRefsInstrumented progUserRef (cfgType envA) := by decide
theorem alignRelevantCovered_pos : AlignRelevantCovered envA instrAll :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
theorem alignRelevantCovered_neg : ¬ AlignRelevantCovered envA instrSrc := by
  intro h
  have := h.1 .dropGlue 1 (by decide) (by decide) rfl
  exact absurd this (by decide)

/-- An environment whose alignments are all 1 is covered by the empty policy. -/
theorem alignRelevantCovered_trivial_align_one : AlignRelevantCovered [tU8] instrNone := by
  refine ⟨fun k t ht h _ => ?_, fun ⟨t, ht, h⟩ => ?_⟩
  · have : t = 0 := by simp at ht; omega
    subst this; exact absurd rfl h
  · have : t = 0 := by simp at ht; omega
    subst this; exact absurd rfl h

/-- Checks at every source position and in every existing shim, and none in the (nonexistent)
box-free shims of non-box types, cover `envA`. -/
theorem alignRelevantCovered_existing_shims :
    AlignRelevantCovered envA (fun b _ => match b with
      | .shim .boxFree _ => false
      | _ => true) := by
  refine ⟨fun k t ht _ hex => ?_, fun _ _ => rfl⟩
  cases k with
  | boxFree =>
    have : t < 3 := ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl <;> exact absurd hex (by decide)
  | dropGlue => rfl
  | clone => rfl

end Toy.Packed
