import ToyPacked.Instances
import ToyPacked.Results

/-!
# Counterexamples, non-vacuity witnesses and positive controls (all fully proved)

Canonical form for a counterexample to hypothesis `H` of a result: a concrete instance satisfying
all the other hypotheses in which the conclusion fails.
-/

namespace Toy.Packed

/-! ## Result `in-place`: dropping a packed field in place is UB without any source `&` -/

/-- Dropping `x : packed { u8, R4 }` in place at scope end: the source body has no raw-pointer
operation (in particular no reference creation), the ideal run destroys the field, and the
reference run creates a misaligned `&mut` at op 0 of the drop glue of `R4` (a UB event). -/
theorem inPlaceDrop_packedField_ub_though_source_has_no_ref :
    SafeSrc progInPlace ∧
    (run .ideal cfgNone progInPlace).evs = [.dtor ⟨.loc 0, [1]⟩] ∧
    (run .ref cfgNone progInPlace).evs = [.ub (.shim .dropGlue 1) 0] := by
  decide

/-! ## Result `staging` -/

/-- Non-vacuity: `progInPlace` with type-based staging into temporaries at address 16 satisfies
every hypothesis of the staging theorem, and it stages the drop of the packed field. -/
theorem staging_hyps_hold_progInPlace :
    FrameAligned progInPlace ∧ SafeSrc progInPlace ∧ CritCovers progInPlace (cfgType envA) ∧
    StagedSized progInPlace (cfgType envA) ∧ StagedAddrBlind progInPlace (cfgType envA) ∧
    TempsAligned progInPlace (cfgType envA) ∧
    (∃ q, q ∈ positions progInPlace ∧ q.staged (cfgType envA) = true) := by
  decide

/-- The conclusion of the staging theorem on the non-vacuity instance. -/
theorem staging_conclusion_progInPlace :
    NoUB (run .ref (cfgType envA) progInPlace) ∧
    obs (run .ref (cfgType envA) progInPlace).evs =
      obs (run .ideal (cfgType envA).unstaged progInPlace).evs := by
  decide

/-- (H1) tight, in an instance with an unsized packed tail: staging the tail gets stuck. -/
theorem staging_fails_without_stagedSized :
    FrameAligned progU ∧ SafeSrc progU ∧ CritCovers progU (cfgType envU) ∧
    StagedAddrBlind progU (cfgType envU) ∧ TempsAligned progU (cfgType envU) ∧
    ¬ StagedSized progU (cfgType envU) ∧
    ¬ (NoUB (run .ref (cfgType envU) progU) ∧
      obs (run .ref (cfgType envU) progU).evs = obs (run .ideal (cfgType envU).unstaged progU).evs) := by
  decide

/-- (H2) tight, in an instance with an address-printing destructor: it prints the temporary's
address 16 instead of the in-place address 1. -/
theorem staging_fails_without_stagedAddrBlind :
    FrameAligned progObs ∧ SafeSrc progObs ∧ CritCovers progObs (cfgType envObs) ∧
    StagedSized progObs (cfgType envObs) ∧ TempsAligned progObs (cfgType envObs) ∧
    ¬ StagedAddrBlind progObs (cfgType envObs) ∧
    ¬ (NoUB (run .ref (cfgType envObs) progObs) ∧
      obs (run .ref (cfgType envObs) progObs).evs =
        obs (run .ideal (cfgType envObs).unstaged progObs).evs) := by
  decide

/-- Staging into temporaries at the misaligned address 2. -/
def cfgTmp2 : Cfg := ⟨critType envA, fun _ _ => 2, instrNone⟩

/-- (H3) tight: a temporary at address 2 (misaligned for alignment 4) reintroduces UB. -/
theorem staging_fails_without_tempsAligned :
    FrameAligned progInPlace ∧ SafeSrc progInPlace ∧ CritCovers progInPlace cfgTmp2 ∧
    StagedSized progInPlace cfgTmp2 ∧ StagedAddrBlind progInPlace cfgTmp2 ∧
    ¬ TempsAligned progInPlace cfgTmp2 ∧
    ¬ (NoUB (run .ref cfgTmp2 progInPlace) ∧
      obs (run .ref cfgTmp2 progInPlace).evs = obs (run .ideal cfgTmp2.unstaged progInPlace).evs) := by
  decide

/-- Coverage tight: with no staging the packed field's drop is UB. -/
theorem staging_fails_without_critCovers :
    FrameAligned progInPlace ∧ SafeSrc progInPlace ∧ StagedSized progInPlace cfgNone ∧
    StagedAddrBlind progInPlace cfgNone ∧ TempsAligned progInPlace cfgNone ∧
    ¬ CritCovers progInPlace cfgNone ∧
    ¬ (NoUB (run .ref cfgNone progInPlace) ∧
      obs (run .ref cfgNone progInPlace).evs = obs (run .ideal cfgNone.unstaged progInPlace).evs) := by
  decide

/-- Frame alignment tight: a local `R4` at address 2. -/
theorem staging_fails_without_frameAligned :
    SafeSrc progMisFrame ∧ CritCovers progMisFrame (cfgType [tR4]) ∧
    StagedSized progMisFrame (cfgType [tR4]) ∧ StagedAddrBlind progMisFrame (cfgType [tR4]) ∧
    TempsAligned progMisFrame (cfgType [tR4]) ∧ ¬ FrameAligned progMisFrame ∧
    ¬ (NoUB (run .ref (cfgType [tR4]) progMisFrame) ∧
      obs (run .ref (cfgType [tR4]) progMisFrame).evs =
        obs (run .ideal (cfgType [tR4]).unstaged progMisFrame).evs) := by
  decide

/-- Staging hypotheses are about the shims a program may enter: a program that only drops `x`
satisfies them with drops-only staging (no clone shim is reachable). -/
theorem staging_hyps_hold_dropsOnly_progInPlace :
    CritCovers progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ ∧
    StagedSized progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ ∧
    StagedAddrBlind progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ ∧
    TempsAligned progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ := by
  decide

/-- An unused local of a type with an unsized packed tail imposes nothing: with an empty source
body every staging hypothesis holds. -/
theorem staging_hyps_hold_progEmptyU :
    FrameAligned progEmptyU ∧ SafeSrc progEmptyU ∧ CritCovers progEmptyU (cfgType envU) ∧
    StagedSized progEmptyU (cfgType envU) ∧ StagedAddrBlind progEmptyU (cfgType envU) ∧
    TempsAligned progEmptyU (cfgType envU) := by
  decide

/-- Staging a packed `Box<R4obs>` field: all staging hypotheses hold (a box is address-blind
whatever its pointee), and the staged run has no UB and the ideal observable trace, in which the
pointee's destructor prints its heap address 4 in both runs. -/
theorem staging_box_of_addrObs_pointee :
    FrameAligned progBoxObs ∧ SafeSrc progBoxObs ∧ CritCovers progBoxObs (cfgType envBoxObs) ∧
    StagedSized progBoxObs (cfgType envBoxObs) ∧ StagedAddrBlind progBoxObs (cfgType envBoxObs) ∧
    TempsAligned progBoxObs (cfgType envBoxObs) ∧
    NoUB (run .ref (cfgType envBoxObs) progBoxObs) ∧
    obs (run .ref (cfgType envBoxObs) progBoxObs).evs =
      [.addrObs ⟨.loc 0, [1, 0]⟩ 4, .dtor ⟨.loc 0, [1, 0]⟩, .free ⟨.loc 0, [1]⟩] ∧
    obs (run .ideal (cfgType envBoxObs).unstaged progBoxObs).evs =
      [.addrObs ⟨.loc 0, [1, 0]⟩ 4, .dtor ⟨.loc 0, [1, 0]⟩, .free ⟨.loc 0, [1]⟩] := by
  decide

/-- Safe-source tight: in `progEscape` the compiler drop of `w` is staged (a misalignable position,
see `srcInstrumented_rawDropInPlace_misaligned_escapes`), and then an unsafe client passes a
misaligned raw pointer to a drop glue. -/
theorem staging_fails_without_safeSrc :
    FrameAligned progEscape ∧ CritCovers progEscape (cfgType envA) ∧
    StagedSized progEscape (cfgType envA) ∧ StagedAddrBlind progEscape (cfgType envA) ∧
    TempsAligned progEscape (cfgType envA) ∧ ¬ SafeSrc progEscape ∧
    ¬ (NoUB (run .ref (cfgType envA) progEscape) ∧
      obs (run .ref (cfgType envA) progEscape).evs =
        obs (run .ideal (cfgType envA).unstaged progEscape).evs) := by
  decide

/-! ## Results `criterion-type-sound`, `criterion-type-covers`, `criterion-type-exact-over-layouts` -/

/-- Non-vacuity of `not_misalignable_of_powTwo_respectsPacking_dvd_typeGA`: field 0 of
`S = { R4 }` in `envQ`. -/
theorem typeGA_sound_hyps_hold :
    PowTwoAligns envQ ∧ RespectsPacking envQ LQ ∧ resolve envQ LQ 2 [0] = some (1, 0) ∧
    envQ.align 1 ∣ typeGA envQ 2 [0] (envQ.align 2) := by
  decide

/-- Powers of two tight for soundness: base alignment 3, field alignment 2 at offset 2;
`typeGA = 2` but address `3 + 2` is odd. -/
theorem typeGA_sound_fails_without_powTwo :
    RespectsPacking envW LW ∧ resolve envW LW 1 [0] = some (0, 2) ∧
    envW.align 0 ∣ typeGA envW 1 [0] (envW.align 1) ∧ ¬ PowTwoAligns envW ∧
    Misalignable (envW.align 1) (envW.align 0) 2 := by
  decide

/-- Divisibility tight for soundness: field 1 (`R4`, alignment 4) of `packed { u8, R4 }` at
offset 1, where `typeGA = 1`. -/
theorem typeGA_sound_fails_without_dvd :
    PowTwoAligns envA ∧ RespectsPacking envA LA ∧ resolve envA LA 2 [1] = some (1, 1) ∧
    ¬ envA.align 1 ∣ typeGA envA 2 [1] (envA.align 2) ∧ Misalignable (envA.align 2) (envA.align 1) 1 := by
  decide

/-- Resolution tight for soundness: the path `[0]` does not follow the types from `R4` (no field),
`typeGA` falls back to the base alignment 4, and offset 1 from a base aligned to 4 is
misalignable for alignment 4. -/
theorem typeGA_sound_fails_without_resolve :
    PowTwoAligns envA ∧ RespectsPacking envA LA ∧ resolve envA LA 1 [0] ≠ some (1, 1) ∧
    envA.align 1 ∣ typeGA envA 1 [0] (envA.align 1) ∧ Misalignable (envA.align 1) (envA.align 1) 1 := by
  decide

/-- Packing-respecting layout tight for soundness: `R4` at offset 1 in a non-packed struct. -/
theorem typeGA_sound_fails_without_respectsPacking :
    PowTwoAligns envRP ∧ resolve envRP LRP 1 [0] = some (0, 1) ∧
    envRP.align 0 ∣ typeGA envRP 1 [0] (envRP.align 1) ∧ ¬ RespectsPacking envRP LRP ∧
    Misalignable (envRP.align 1) (envRP.align 0) 1 := by
  decide

/-- Non-vacuity of
`exists_respectsPacking_layout_misalignable_iff_not_dvd_typeGA_of_noRepeatStep_powTwo`: the nested
place `x.1.0` of `Q = packed { u8, S }`. -/
theorem typeGA_exact_hyps_hold :
    PowTwoAligns envQ ∧ typeAt envQ 3 [1, 0] = some 1 ∧ NoRepeatStep envQ 3 [1, 0] := by
  decide

/-- Non-vacuity of `critCovers_critType_of_powTwo_respectsPacking` (and the conclusion on the
instance): `progNested` over `envQ`. -/
theorem critCovers_critType_hyps_hold :
    PowTwoAligns progNested.env ∧ RespectsPacking progNested.env progNested.layout ∧
    CritCovers progNested ⟨critType progNested.env, fun _ _ => 16, instrNone⟩ := by
  decide

/-- A clone of field 0 of a local `w : W` (alignment 3) at address 3, in `envW`. -/
def progW : Prog := ⟨envW, LW, [1], [3], [.comp .clone ⟨0, [0]⟩]⟩

/-- A drop of field 0 of a local `s : S` at address 0, in `envRP` (`R4` at offset 1). -/
def progRP : Prog := ⟨envRP, LRP, [1], [0], [.comp .dropGlue ⟨0, [0]⟩]⟩

/-- Powers of two tight for coverage by `critType`. -/
theorem critCovers_critType_fails_without_powTwo :
    RespectsPacking progW.env progW.layout ∧ ¬ PowTwoAligns progW.env ∧
    ¬ CritCovers progW ⟨critType progW.env, fun _ _ => 16, instrNone⟩ := by
  decide

/-- Packing-respecting layout tight for coverage by `critType`. -/
theorem critCovers_critType_fails_without_respectsPacking :
    PowTwoAligns progRP.env ∧ ¬ RespectsPacking progRP.env progRP.layout ∧
    ¬ CritCovers progRP ⟨critType progRP.env, fun _ _ => 16, instrNone⟩ := by
  decide

/-- No-repeated-step tight for exactness: in the cyclic `C = packed { C }` (alignment 2), the
path `[0, 0]` takes step `(0, 0)` twice; `typeGA` is 1, yet under every layout the offset is
`2 * L 0 0`, never misaligned. -/
theorem typeGA_exact_fails_without_noRepeatStep :
    PowTwoAligns envCyc ∧ typeAt envCyc 0 [0, 0] = some 0 ∧ ¬ NoRepeatStep envCyc 0 [0, 0] ∧
    ¬ envCyc.align 0 ∣ typeGA envCyc 0 [0, 0] (envCyc.align 0) ∧
    ¬ (∃ L : Layout, RespectsPacking envCyc L ∧ ∃ o, resolve envCyc L 0 [0, 0] = some (0, o) ∧
        Misalignable (envCyc.align 0) (envCyc.align 0) o) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨L, _, o, hres, hmis⟩
  have ho : o = L 0 0 + (L 0 0 + 0) := by
    simp [resolve, Env.field?, Env.fields, Env.ty, envCyc] at hres
    omega
  rw [misalignable_iff_not_dvd_gcd] at hmis
  apply hmis
  subst ho
  exact Nat.dvd_gcd (Nat.dvd_refl _) ⟨L 0 0, by simp [Env.align, Env.ty, envCyc]; omega⟩

/-- Powers of two tight for exactness: in `envW` the layout `LW` respects packing and makes the
place misalignable, although its type alignment divides `typeGA`. -/
theorem typeGA_exact_fails_without_powTwo :
    NoRepeatStep envW 1 [0] ∧ typeAt envW 1 [0] = some 0 ∧ ¬ PowTwoAligns envW ∧
    (∃ L : Layout, RespectsPacking envW L ∧ ∃ o, resolve envW L 1 [0] = some (0, o) ∧
        Misalignable (envW.align 1) (envW.align 0) o) ∧
    envW.align 0 ∣ typeGA envW 1 [0] (envW.align 1) := by
  refine ⟨by decide, by decide, by decide, ⟨LW, by decide, 2, by decide, by decide⟩, by decide⟩

/-- Type-at tight for exactness: the path `[99]` does not follow the types from
`packed { u8, R4 }`, so no layout resolves it, while `typeGA` falls back to the base alignment 1,
which alignment 4 does not divide. -/
theorem typeGA_exact_fails_without_typeAt :
    PowTwoAligns envA ∧ NoRepeatStep envA 2 [99] ∧ typeAt envA 2 [99] ≠ some 1 ∧
    ¬ ((∃ L : Layout, RespectsPacking envA L ∧ ∃ o, resolve envA L 2 [99] = some (1, o) ∧
        Misalignable (envA.align 2) (envA.align 1) o) ↔
      ¬ envA.align 1 ∣ typeGA envA 2 [99] (envA.align 2)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro h
  have hr : ¬ envA.align 1 ∣ typeGA envA 2 [99] (envA.align 2) := by decide
  obtain ⟨L, _, o, hres, _⟩ := h.mpr hr
  simp [resolve, Env.field?, Env.fields, Env.ty, envA] at hres

/-! ## Result `criterion-leaf-misses` -/

/-- The leaf-only criterion (stage iff the immediate parent is `packed(n)` and the field's
alignment does not divide `n`) misses the field of a non-packed struct nested in a packed field:
it does not stage `x.1.0` of `Q = packed { u8, S }`, the place is misalignable, and the unstaged
drop is UB; the type-based criterion stages it and the run has no UB. -/
theorem leafOnlyCrit_misses_nested_field :
    critLeaf envQ .dropGlue 1 3 [1, 0] = false ∧ Misalignable 1 (envQ.align 1) 1 ∧
    (run .ref ⟨critLeaf envQ, fun _ _ => 16, instrNone⟩ progNested).evs =
      [.ub (.shim .dropGlue 1) 0] ∧
    critType envQ .dropGlue 1 3 [1, 0] = true ∧
    NoUB (run .ref (cfgType envQ) progNested) := by
  decide

/-- The leaf-only criterion also misses a one-step path when the parent's declared alignment is
below its field's alignment (the toy permits this): `S = { R4 }` with alignment 1 in `envUnder`,
a local `s : S` at address 1 (aligned for `S`), and the drop of `s.0`. The parent is not packed,
so `critLeaf` does not stage; the unstaged drop is UB; `critType` stages it and the run has no
UB. The environment's alignments are powers of two and the layout respects packing. -/
theorem leafOnlyCrit_misses_one_step_underaligned_parent :
    PowTwoAligns envUnder ∧ RespectsPacking envUnder (fun _ _ => 0) ∧ FrameAligned progUnder ∧
    critLeaf envUnder .dropGlue 1 1 [0] = false ∧
    (run .ref ⟨critLeaf envUnder, fun _ _ => 16, instrNone⟩ progUnder).evs =
      [.ub (.shim .dropGlue 0) 0] ∧
    critType envUnder .dropGlue 1 1 [0] = true ∧
    NoUB (run .ref (cfgType envUnder) progUnder) := by
  decide

/-- For the whole-value drop of `x : Q = packed { u8, S }`, the drop glue of `Q` drops its field
`S` (one projection per shim) and `critLeaf` stages it; the run has no UB. -/
theorem leafOnlyCrit_stages_field_in_whole_drop :
    critLeaf envQ .dropGlue 1 3 [1] = true ∧
    NoUB (run .ref ⟨critLeaf envQ, fun _ _ => 16, instrNone⟩ progWholeQ) := by
  decide

/-! ## Result `criterion-type-overstages-fixed-layout` -/

/-- Positive control (fixed layout): the type-based criterion stages a place that can never be
misaligned under the given layout (`Outer.1.2`, offset 4 from a base aligned to 2), while the
offset-aware criterion does not. -/
theorem typeCrit_overstages_fixed_layout :
    PowTwoAligns envOuter ∧ RespectsPacking envOuter LOuter ∧
    critType envOuter .dropGlue 2 3 [1, 2] = true ∧
    critExact envOuter LOuter .dropGlue 2 3 [1, 2] = false ∧
    resolve envOuter LOuter 3 [1, 2] = some (1, 4) ∧ ¬ Misalignable 2 (envOuter.align 1) 4 := by
  decide

/-! ## Result `overstaging-aligned` -/

/-- Over-staging an aligned place whose destructor prints its address changes the observable
trace: with `critAll` the drop of `y : R4obs` at the aligned address 8 runs at the temporary's
address 16, so the staged run prints 16 where the ideal run prints 8 (the run has no UB). -/
theorem overstaging_aligned_addrObs_changes_trace :
    NoUB (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAlignedObs) ∧
    obs (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAlignedObs).evs =
      [.addrObs ⟨.loc 0, []⟩ 16, .dtor ⟨.loc 0, []⟩] ∧
    obs (run .ideal cfgNone progAlignedObs).evs = [.addrObs ⟨.loc 0, []⟩ 8, .dtor ⟨.loc 0, []⟩] := by
  decide

/-- Positive control: over-staging an aligned place is sound but costs a copy. With `critAll`
the drop of an aligned local is staged; the run has no UB, the observable trace equals the
ideal trace, and it has one more staging copy. -/
theorem overstaging_aligned_place_sound_costs_copy :
    NoUB (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAligned) ∧
    obs (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAligned).evs =
      obs (run .ideal cfgNone progAligned).evs ∧
    copies (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAligned).evs = 1 ∧
    copies (run .ideal cfgNone progAligned).evs = 0 := by
  decide

/-! ## Result `box-free`: staging only the moved-out value leaves the deallocation misaligned -/

/-- Staging only drops (the moved-out value) into aligned temporaries. -/
def cfgDropsOnly : Cfg := ⟨dropsOnly (critType envB), fun _ _ => 16, instrNone⟩

/-- `progBox` drops `z : packed { u8, Box<R4> }`, deref-moves out of the box field of
`x : packed { u8, Box<R4> }`, frees that box through the field, and drops `y : R4`. Drops-only
staging (`cfgDropsOnly`) stages every misalignable drop position, and there is one (the drop of
the box field of `z` inside the drop glue of `packed { u8, Box<R4> }`), so the staged run copies
`z.1` and runs its drop glue at the aligned temporary; it does not stage the misalignable free of
`x.1`, which leaves a misaligned `&mut Box` at op 0 of the box-free shim (UB). Staging the box
field itself before freeing (`cfgType envB`) gives a run without UB whose observable trace equals
the ideal trace. -/
theorem boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok :
    (∀ q, q ∈ positions progBox → q.k = .dropGlue →
      Misalignable q.A (envB.align q.u) q.o → q.staged cfgDropsOnly = true) ∧
    (∃ q, q ∈ positions progBox ∧ q.k = .dropGlue ∧
      Misalignable q.A (envB.align q.u) q.o ∧ q.staged cfgDropsOnly = true) ∧
    (∃ q, q ∈ positions progBox ∧ q.k = .boxFree ∧
      Misalignable q.A (envB.align q.u) q.o ∧ q.staged cfgDropsOnly = false) ∧
    (run .ref cfgDropsOnly progBox).evs =
      [.copy ⟨.loc 2, [1]⟩, .dtor ⟨.loc 2, [1, 0]⟩, .free ⟨.loc 2, [1]⟩,
        .ub (.shim .boxFree 2) 0] ∧
    NoUB (run .ref (cfgType envB) progBox) ∧
    obs (run .ref (cfgType envB) progBox).evs = obs (run .ideal cfgNone progBox).evs := by
  decide

/-- `moveOut` is a no-op marker: removing it from `progBox` leaves both runs of
`boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok` unchanged. -/
theorem progBox_moveOut_irrelevant :
    (run .ref cfgDropsOnly progBox).evs = (run .ref cfgDropsOnly progBoxNoMove).evs ∧
    (run .ref (cfgType envB) progBox).evs = (run .ref (cfgType envB) progBoxNoMove).evs := by
  decide

/-! ## Result `completeness` -/

/-- An operation whose required alignment is 1 never traps and never raises UB, so a policy
need not cover it. -/
theorem refStep_align_one (m : Mode) (cfg : Cfg) (b : BodyId) (i a : Nat) :
    refStep m cfg b i 1 a = ⟨[], true⟩ := by
  cases m <;> simp [refStep]

/-- Non-vacuity of the completeness theorem: checks everywhere cover `envA`, and on
`progClient` the instrumented run traps where the uninstrumented run has UB. -/
theorem completeness_witness :
    AlignRelevantCovered envA instrAll ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrAll⟩ progClient).evs =
      [.trap (.shim .dropGlue 1) 0] ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrNone⟩ progClient).evs =
      [.ub (.shim .dropGlue 1) 0] := by
  refine ⟨⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, by decide, by decide⟩

/-! ## Result `escape`: UB escapes through an uninstrumented shim -/

/-- Every source position is instrumented, and type-based staging stages every misalignable
compiler-operation position of `progEscape`, of which there is one (the drop of the field `R4` of
`w` inside the drop glue of `packed { u8, R4 }`), but the drop glue of `R4` is not instrumented:
after the staged drop of `w`, an unsafe client passes the misaligned raw pointer with address 9
(the address of `x.1`) to the drop glue of `R4`, which creates a misaligned `&mut` (UB, no trap).
Instrumenting op 0 of the shim turns it into a trap. -/
theorem srcInstrumented_rawDropInPlace_misaligned_escapes :
    (∀ i, instrSrc .src i = true) ∧ instrSrc (.shim .dropGlue 1) 0 = false ∧
    CritCovers progEscape (cfgType envA) ∧
    (∃ q, q ∈ positions progEscape ∧ Misalignable q.A (envA.align q.u) q.o ∧
      q.staged (cfgType envA) = true) ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrSrc⟩ progEscape).evs =
      [.copy ⟨.loc 0, [1]⟩, .dtor ⟨.loc 0, [1]⟩, .ub (.shim .dropGlue 1) 0] ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrAll⟩ progEscape).evs =
      [.copy ⟨.loc 0, [1]⟩, .dtor ⟨.loc 0, [1]⟩, .trap (.shim .dropGlue 1) 0] := by
  refine ⟨fun _ => rfl, rfl, by decide, by decide, by decide, by decide⟩

/-! ## Result `sufficiency` -/

/-- Type-based staging, checks in the source body only. -/
def cfgSrc : Cfg := ⟨critType envA, fun _ _ => 16, instrSrc⟩

/-- Non-vacuity: `progMixed` satisfies all premises; its run executes all three operations (a
staged field drop, an aligned client call, and a misaligned user reference that traps). -/
theorem sufficiency_hyps_hold_progMixed :
    FrameAligned progMixed ∧ CritCovers progMixed cfgSrc ∧ TempsAligned progMixed cfgSrc ∧
    ClientPtrsAligned progMixed ∧ SrcRefsInstrumented progMixed cfgSrc ∧
    (run .ref cfgSrc progMixed).evs =
      [.copy ⟨.loc 0, [1]⟩, .dtor ⟨.loc 0, [1]⟩, .dtor ⟨.raw 1, []⟩, .trap .src 2] := by
  decide

/-- Premise (a) tight (the counterexample of result `box-free`): drops-only staging stages the
misalignable drop of `z.1` (so `TempsAligned` holds at a staged position), and the free of the box
field of `x` is not staged. -/
theorem sufficiency_fails_without_critCovers :
    FrameAligned progBox ∧ TempsAligned progBox cfgDropsOnly ∧ ClientPtrsAligned progBox ∧
    SrcRefsInstrumented progBox cfgDropsOnly ∧ ¬ CritCovers progBox cfgDropsOnly ∧
    ¬ NoUB (run .ref cfgDropsOnly progBox) ∧ ¬ NoShimUB (run .ref cfgDropsOnly progBox) := by
  decide

/-- Temporary alignment tight. -/
theorem sufficiency_fails_without_tempsAligned :
    FrameAligned progInPlace ∧ CritCovers progInPlace cfgTmp2 ∧ ClientPtrsAligned progInPlace ∧
    SrcRefsInstrumented progInPlace cfgTmp2 ∧ ¬ TempsAligned progInPlace cfgTmp2 ∧
    ¬ NoUB (run .ref cfgTmp2 progInPlace) ∧ ¬ NoShimUB (run .ref cfgTmp2 progInPlace) := by
  decide

/-- Frame alignment tight. -/
theorem sufficiency_fails_without_frameAligned :
    CritCovers progMisFrame (cfgType [tR4]) ∧ TempsAligned progMisFrame (cfgType [tR4]) ∧
    ClientPtrsAligned progMisFrame ∧ SrcRefsInstrumented progMisFrame (cfgType [tR4]) ∧
    ¬ FrameAligned progMisFrame ∧
    ¬ NoUB (run .ref (cfgType [tR4]) progMisFrame) ∧
    ¬ NoShimUB (run .ref (cfgType [tR4]) progMisFrame) := by
  decide

/-- Premise (b) tight (the program of result `escape`: a staged drop, then a misaligned client
call). -/
theorem sufficiency_fails_without_clientPtrsAligned :
    FrameAligned progEscape ∧ CritCovers progEscape cfgSrc ∧ TempsAligned progEscape cfgSrc ∧
    SrcRefsInstrumented progEscape cfgSrc ∧ ¬ ClientPtrsAligned progEscape ∧
    ¬ NoUB (run .ref cfgSrc progEscape) ∧ ¬ NoShimUB (run .ref cfgSrc progEscape) := by
  decide

/-- `progUserRef` has a misalignable compiler-operation position that type-based staging stages
(the drop of the field `R4` of `w` inside the drop glue of `packed { u8, R4 }`), so the
`CritCovers` and `TempsAligned` conjuncts of `sufficiency_fails_without_srcRefsInstrumented` hold
at a staged position. -/
theorem progUserRef_stages_misalignable_position :
    ∃ q, q ∈ positions progUserRef ∧ Misalignable q.A (envA.align q.u) q.o ∧
      q.staged (cfgType envA) = true := by
  decide

/-- Premise (c) tight: after a staged drop, an uninstrumented misaligned user reference in the
source body. -/
theorem sufficiency_fails_without_srcRefsInstrumented :
    FrameAligned progUserRef ∧ CritCovers progUserRef (cfgType envA) ∧
    TempsAligned progUserRef (cfgType envA) ∧ ClientPtrsAligned progUserRef ∧
    ¬ SrcRefsInstrumented progUserRef (cfgType envA) ∧
    ¬ NoUB (run .ref (cfgType envA) progUserRef) ∧
    NoShimUB (run .ref (cfgType envA) progUserRef) := by
  decide

/-- The coverage and frame-alignment counterexamples of `staging` and `sufficiency` stage no
position: with `cfgNone` no position of `progInPlace` is staged, and the single position of
`progMisFrame` is not misalignable and is not staged by `cfgType [tR4]`. So their staged-position
hypotheses (and, for `progMisFrame`, `CritCovers`) hold vacuously. -/
theorem critCovers_and_frameAligned_counterexamples_stage_nothing :
    (∀ q, q ∈ positions progInPlace → q.staged cfgNone = false) ∧
    (∀ q, q ∈ positions progMisFrame →
      ¬ Misalignable q.A (progMisFrame.env.align q.u) q.o ∧ q.staged (cfgType [tR4]) = false) := by
  decide

/-! ## Result `no-stuck` -/

/-- Non-vacuity of `noStuck_of_stagedSized`: `progInPlace` with type-based staging stages a
position, every staged position is sized, and the run has no `stuck` event. -/
theorem noStuck_hyps_hold_progInPlace :
    StagedSized progInPlace (cfgType envA) ∧
    (∃ q, q ∈ positions progInPlace ∧ q.staged (cfgType envA) = true) ∧
    NoStuck (run .ref (cfgType envA) progInPlace) := by
  decide

/-- (H1) tight for `noStuck_of_stagedSized`: staging the unsized tail of `progU` is `stuck`. -/
theorem noStuck_fails_without_stagedSized :
    ¬ StagedSized progU (cfgType envU) ∧ ¬ NoStuck (run .ref (cfgType envU) progU) := by
  decide

/-- The premises of `sufficiency` hold for `progU` with type-based staging, whose run ends with
`stuck` (no UB event): `sufficiency` does not exclude `stuck`. -/
theorem sufficiency_hyps_hold_progU_stuck :
    FrameAligned progU ∧ CritCovers progU (cfgType envU) ∧ TempsAligned progU (cfgType envU) ∧
    ClientPtrsAligned progU ∧ SrcRefsInstrumented progU (cfgType envU) ∧
    (run .ref (cfgType envU) progU).evs = [.stuck (.shim .dropGlue 2) 2] := by
  decide

end Toy.Packed
