/-
  Positive and negative examples for every core definition in `Toy.SubstStable`.
  Every theorem in this file is kernel-checked with zero `sorry`.
-/
import Toy.SubstStable.Basic
import Toy.SubstStable.Lemmas

namespace Toy.SubstStable

/-! ## Shared concrete types, substitutions, and environments -/

/-- Closed 1-byte alignment-1 scalar (`u8`). -/
def tyU8 : ClosedTy := .base 1 1

/-- Closed 2-byte alignment-2 scalar (`u16`). -/
def tyU16 : ClosedTy := .base 2 2

/-- Closed 4-byte alignment-4 scalar (`u32`). -/
def tyU32 : ClosedTy := .base 4 4

/-- Closed 8-byte alignment-8 scalar (`u64`). -/
def tyU64 : ClosedTy := .base 8 8

/-- Closed explicitly aligned `#[repr(align(16))]` wrapper over `u8`. -/
def align16U8 : ClosedTy := .align 16 tyU8

/-- Empty associated-type environment (`none` everywhere). -/
def emptyAssoc : AssocEnv := fun _ _ => none

/-- Associated-type environment mapping `(0, tyU8)` to `align16U8` and `(1, tyU8)` to `tyU32`. -/
def sampleAssoc : AssocEnv
  | 0, .base 1 1 => some align16U8
  | 1, .base 1 1 => some tyU32
  | _, _ => none

/-- Substitution mapping all type parameters to `tyU8` and all const parameters to `2`. -/
def substU8 : Subst where
  ty _ := tyU8
  cnst _ := 2

/-- Substitution mapping type parameter `0` to `align16U8` (others `tyU8`) and consts to `0`. -/
def substAlign16 : Subst where
  ty i := if i = 0 then align16U8 else tyU8
  cnst _ := 0

/-- Default `FullNoAlignBound`-conforming witness environment (`all no-align` `tyU8` assoc + subst). -/
def defaultNoAlignEnv : AssocEnv × Subst :=
  (fun _ _ => some tyU8, substU8)

/-! ## 1. Examples for const-index definitions -/

theorem isCtorIdx_pos_nested_ctor :
    isCtorIdx (.ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) = true := rfl

theorem isCtorIdx_neg_add :
    isCtorIdx (.add (.cparam 0) (.lit 1)) = false := rfl

theorem isCtorIdxList_pos :
    isCtorIdxList [.lit 0, .cparam 1] = true := rfl

theorem isCtorIdxList_neg :
    isCtorIdxList [.lit 0, .sub (.cparam 0) (.lit 1)] = false := rfl

theorem evalIdx_pos_checked_sub :
    evalIdx (fun _ => 5) (.sub (.cparam 0) (.lit 2)) = some (.nat 3) := rfl

theorem evalIdx_neg_underflow_sub :
    evalIdx (fun _ => 0) (.sub (.cparam 0) (.lit 1)) = none := rfl

theorem evalIdx_neg_div_zero :
    evalIdx (fun _ => 0) (.div (.lit 16) (.cparam 0)) = none := rfl

theorem evalIdxList_pos :
    evalIdxList (fun _ => 3) [.cparam 0, .lit 7] = some [.nat 3, .nat 7] := rfl

theorem evalIdxList_neg :
    evalIdxList (fun _ => 0) [.lit 7, .sub (.cparam 0) (.lit 1)] = none := rfl

theorem idxSemEq_pos_comm_add :
    IdxSemEq (.add (.cparam 0) (.lit 1)) (.add (.lit 1) (.cparam 0)) := by
  intro γ
  simp [evalIdx, Nat.add_comm]

theorem idxSemEq_neg_partial_sub :
    ¬ IdxSemEq (.sub (.cparam 0) (.lit 1)) (.lit 0) := by
  intro h
  have h0 := h (fun _ => 0)
  simp [evalIdx] at h0

theorem idxTotal_pos_add :
    IdxTotal (.add (.cparam 0) (.lit 1)) := by
  intro γ
  rfl

theorem idxTotal_neg_sub :
    ¬ IdxTotal (.sub (.cparam 0) (.lit 1)) := by
  intro h
  have h0 := h (fun _ => 0)
  simp [evalIdx] at h0

/-- Total addition is `IdxTotal` while excluded from `isCtorIdx` (`isCtorIdx` is sufficient, not necessary, for `IdxTotal`). -/
theorem add_idxTotal_yet_not_isCtorIdx :
    IdxTotal (.add (.cparam 0) (.lit 1)) ∧
      isCtorIdx (.add (.cparam 0) (.lit 1)) = false :=
  ⟨idxTotal_pos_add, rfl⟩

/-! ## 2. Examples for closed-type layout and `packedNoAlignWf` -/

theorem byteSize_pos_arr_nat :
    (ClosedTy.arr tyU32 (.nat 3)).byteSize = 12 := rfl

theorem byteSize_pos_arr_ctor :
    (ClosedTy.arr tyU32 (.ctor 0 [.nat 9])).byteSize = 4 := rfl

theorem byteSize_neg_arr_zero :
    (ClosedTy.arr tyU32 (.nat 0)).byteSize = 0 ∧
      (ClosedTy.arr tyU32 (.nat 0)).byteSize ≠ 4 := by
  decide

theorem byteSize_ignores_align_and_padding :
    align16U8.byteSize = 1 ∧
      align16U8.effAlign = 16 ∧
      (ClosedTy.prod tyU8 tyU32).byteSize = 5 :=
  ⟨rfl, rfl, rfl⟩

theorem effAlign_pos_align_raises :
    (ClosedTy.align 16 tyU8).effAlign = 16 := rfl

theorem effAlign_neg_packed_caps :
    (ClosedTy.packed 1 tyU64).effAlign = 1 ∧
      (ClosedTy.packed 1 tyU64).effAlign ≠ 8 := by
  decide

theorem sizeLe_pos_u32 :
    sizeLe 4 tyU32 = true := rfl

theorem sizeLe_neg_u64 :
    sizeLe 4 tyU64 = false := rfl

theorem eqProdByteSize_pos_same :
    eqProdByteSize (.prod tyU16 (.arr tyU8 (.nat 2))) = true := rfl

theorem eqProdByteSize_neg_mismatch :
    eqProdByteSize (.prod tyU16 tyU8) = false := rfl

theorem eqProdByteSize_neg_nonprod :
    eqProdByteSize tyU16 = false := rfl

theorem hasAlignWrapper_pos_nested :
    hasAlignWrapper (.prod tyU8 align16U8) = true := rfl

theorem hasAlignWrapper_neg_natural_u64 :
    hasAlignWrapper tyU64 = false := rfl

theorem packedNoAlignWf_pos_outer_align :
    packedNoAlignWf (.align 16 (.packed 1 tyU64)) = true := rfl

theorem packedNoAlignWf_pos_natural_u64 :
    packedNoAlignWf (.packed 1 tyU64) = true := rfl

theorem packedNoAlignWf_neg_inner_align :
    packedNoAlignWf (.packed 1 align16U8) = false := rfl

theorem packedNoAlignWf_neg_zero_len_arr :
    packedNoAlignWf (.packed 1 (.arr align16U8 (.nat 0))) = false := rfl

/-! ## 3. Examples for instantiation, bounds, and stability predicates -/

theorem instTy_pos_proj_and_arr :
    instTy sampleAssoc substU8 (.arr (.proj 1 (.tparam 0)) (.cparam 0)) =
      some (.arr tyU32 (.nat 2)) := rfl

theorem instTy_neg_unresolved_proj :
    instTy emptyAssoc substU8 (.proj 0 (.tparam 0)) = none := rfl

theorem instTy_neg_failed_idx :
    instTy emptyAssoc substAlign16 (.arr (.tparam 0) (.sub (.cparam 0) (.lit 1))) = none := rfl

theorem boundEntails_pos_full_to_empty :
    BoundEntails FullNoAlignBound (DeclBounds.sat emptyBounds) := by
  intro A σ hF
  refine ⟨fun i => (hF.1 i).1, fun tr src rhs hA => (hF.2 tr src rhs hA).1, ?_, ?_⟩
  · intro i hi; cases hi
  · intro tr htr; cases htr

/-- `substAlign16` satisfies `DeclBounds.sat emptyBounds` under `emptyAssoc`. -/
theorem substAlign16_sat_emptyBounds :
    DeclBounds.sat emptyBounds emptyAssoc substAlign16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [substAlign16]
    split <;> rfl
  · intro _ _ _ hA
    cases hA
  · intro _ hi
    cases hi
  · intro _ htr _ _ _
    cases htr

theorem boundEntails_neg_empty_to_full :
    ¬ BoundEntails (DeclBounds.sat emptyBounds) FullNoAlignBound := by
  intro hEnt
  have hFull := hEnt emptyAssoc substAlign16 substAlign16_sat_emptyBounds
  have h0 := (hFull.1 0).2
  simp [substAlign16, align16U8, hasAlignWrapper] at h0

theorem defCheckSound_pos_const_false :
    DefCheckSound unbounded (sizeLe 4) (fun _ => false) := by
  intro t _ _ _ hC
  cases hC

theorem defCheckSound_neg_const_true :
    ¬ DefCheckSound unbounded (sizeLe 4) (fun _ => true) := by
  intro hS
  have h := hS (.base 8 8) emptyAssoc substU8 tyU64 rfl trivial rfl
  cases h

theorem defCheckComplete_pos_const_true :
    DefCheckComplete unbounded (sizeLe 4) (fun _ => true) := by
  intro _ _ _ _ _ _ _
  rfl

theorem defCheckComplete_neg_const_false :
    ¬ DefCheckComplete unbounded (sizeLe 4) (fun _ => false) := by
  intro hC
  have h := hC (.base 1 1) emptyAssoc substU8 tyU8 trivial rfl rfl
  cases h

theorem allInstSat_pos_packed_under_full :
    AllInstSat FullNoAlignBound packedNoAlignWf (.packed 1 (.tparam 0)) := by
  intro A σ τ hB hi
  rw [packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hi]
  rfl

theorem allInstSat_neg_packed_under_empty :
    ¬ AllInstSat (DeclBounds.sat emptyBounds) packedNoAlignWf (.packed 1 (.tparam 0)) := by
  intro hAll
  have h := hAll emptyAssoc substAlign16 (.packed 1 align16U8) substAlign16_sat_emptyBounds rfl
  cases h

theorem allInstSat_pos_zero_len_arr_sizeLe (k : Nat) :
    AllInstSat unbounded (sizeLe k) (.arr (.tparam 0) (.lit 0)) := by
  intro _ σ τ _ hi
  simp only [instTy, evalIdx] at hi
  injection hi with hτ
  subst hτ
  simp [sizeLe, ClosedTy.byteSize]

theorem substStable_pos_const_true :
    SubstStable unbounded (fun _ => true) := by
  intro _ _ _ _ _ _ _ _ _ _ _
  rfl

theorem substStable_neg_sizeLe_unbounded :
    ¬ SubstStable unbounded (sizeLe 4) := by
  intro hStab
  have h := hStab (.tparam 0)
    emptyAssoc substU8 tyU8
    emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ tyU64
    trivial rfl trivial rfl
  cases h

theorem hasInstWitness_pos_fixed_const :
    HasInstWitness FixedConstNoAlignBound constZeroNoAlignWitness := by
  rintro t ⟨A, σ, τ, ⟨_, hc⟩, hi⟩
  refine ⟨⟨⟨fun _ => ⟨rfl, rfl⟩, fun _ _ rhs hA => ?_⟩, rfl⟩,
    instTy_constZeroNoAlignWitness_isSome hc hi⟩
  injection hA with hr
  subst hr
  exact ⟨rfl, rfl⟩

theorem hasInstWitness_neg_const_map_fullNoAlign (env : AssocEnv × Subst) :
    ¬ HasInstWitness FullNoAlignBound (fun _ => env) := by
  intro hw
  have hFullDef : FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 := by
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ rhs hA => ?_⟩
    injection hA with hr
    subst hr
    exact ⟨rfl, rfl⟩
  cases hn : env.2.cnst 0 with
  | zero =>
      let tPos : OpenTy := .arr (.base 1 1) (.div (.lit 1) (.cparam 0))
      have hInstPos :
          instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 tPos = some (.arr tyU8 (.nat 0)) := rfl
      have hSome :=
        (hw tPos ⟨defaultNoAlignEnv.1, defaultNoAlignEnv.2, .arr tyU8 (.nat 0),
          hFullDef, hInstPos⟩).2
      simp [tPos, instTy, evalIdx, hn] at hSome
  | succ _ =>
      let tZero : OpenTy := .arr (.base 1 1) (.sub (.lit 0) (.cparam 0))
      let env0 : AssocEnv × Subst := (fun _ _ => some tyU8, ⟨fun _ => tyU8, fun _ => 0⟩)
      have hFull0 : FullNoAlignBound env0.1 env0.2 := by
        refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ rhs hA => ?_⟩
        injection hA with hr
        subst hr
        exact ⟨rfl, rfl⟩
      have hInst0 : instTy env0.1 env0.2 tZero = some (.arr tyU8 (.nat 0)) := rfl
      have hSome :=
        (hw tZero ⟨env0.1, env0.2, .arr tyU8 (.nat 0), hFull0, hInst0⟩).2
      simp [tZero, instTy, evalIdx, hn] at hSome

theorem hasInstWitness_pos_singleton_bound :
    HasInstWitness (fun A σ => A = emptyAssoc ∧ σ = substU8) (fun _ => (emptyAssoc, substU8)) := by
  rintro t ⟨A, σ, τ, ⟨rfl, rfl⟩, hi⟩
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [hi]
  rfl

theorem hasInstWitness_neg_bad_subst :
    ¬ HasInstWitness FullNoAlignBound (fun _ => (emptyAssoc, substAlign16)) := by
  intro hw
  have hF : FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 := by
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ rhs hA => ?_⟩
    injection hA with hr; subst hr
    exact ⟨rfl, rfl⟩
  have h := (hw (.base 1 1) ⟨defaultNoAlignEnv.1, defaultNoAlignEnv.2, tyU8, hF, rfl⟩).1
  have h0 := (h.1 0).2
  simp [substAlign16, align16U8, hasAlignWrapper] at h0

theorem witnessDefCheck_pos_u8 :
    witnessDefCheck (sizeLe 4) (fun _ => (emptyAssoc, substU8)) (.tparam 0) = true := rfl

theorem witnessDefCheck_neg_over_size :
    witnessDefCheck (sizeLe 4) (fun _ => (emptyAssoc, ⟨fun _ => tyU64, fun _ => 0⟩)) (.tparam 0) =
      false := rfl

/-! ## 4. Examples for syntactic `DeclBounds` and `packed`/`align` checks -/

theorem declBoundsSat_pos_selective :
    DeclBounds.sat ⟨[0], []⟩ emptyAssoc
      ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    dsimp
    split <;> rfl
  · intro _ _ _ hA
    cases hA
  · intro i hi
    simp at hi
    subst hi
    rfl
  · intro _ htr _ _ _
    cases htr

theorem declBoundsSat_neg_param_has_align :
    ¬ DeclBounds.sat ⟨[0], []⟩ emptyAssoc substAlign16 := by
  intro h
  have h0 := h.2.2.1 0 (by simp)
  simp [substAlign16, align16U8, hasAlignWrapper] at h0

theorem fullNoAlignBound_pos_scalars :
    FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ rhs hA => ?_⟩
  injection hA with hr; subst hr
  exact ⟨rfl, rfl⟩

theorem fullNoAlignBound_neg_align_subst :
    ¬ FullNoAlignBound emptyAssoc substAlign16 := by
  intro h
  have h0 := (h.1 0).2
  simp [substAlign16, align16U8, hasAlignWrapper] at h0

theorem naiveOpenHasAlign_pos_literal :
    naiveOpenHasAlign (.align 8 (.tparam 0)) = true := rfl

theorem naiveOpenHasAlign_neg_tparam :
    naiveOpenHasAlign (.tparam 0) = false := rfl

theorem naiveDefPackedCheck_pos_tparam :
    naiveDefPackedCheck (.packed 1 (.tparam 0)) = true := rfl

theorem naiveDefPackedCheck_neg_literal_align :
    naiveDefPackedCheck (.packed 1 (.align 16 (.base 1 1))) = false := rfl

theorem mayHaveAlignUnder_pos_unbounded_param :
    mayHaveAlignUnder emptyBounds (.tparam 0) = true := rfl

theorem mayHaveAlignUnder_neg_bounded_param :
    mayHaveAlignUnder ⟨[0], []⟩ (.tparam 0) = false := rfl

theorem boundedDefPackedCheck_pos_bounded_param :
    boundedDefPackedCheck ⟨[0], []⟩ (.prod (.packed 1 (.tparam 0)) (.tparam 1)) = true := rfl

theorem boundedDefPackedCheck_neg_unbounded_param :
    boundedDefPackedCheck emptyBounds (.packed 1 (.tparam 0)) = false := rfl

theorem boundedDefPackedCheck_pos_erased_proj_arg :
    boundedDefPackedCheck ⟨[], [0]⟩
      (.packed 1 (.proj 0 (.packed 1 (.align 16 (.base 1 1))))) = true := rfl

/-! ## 5. Examples for PME evaluation, collection, and capture predicates -/

theorem evalPmeCheck_pos_sizeEq :
    evalPmeCheck emptyAssoc substU8 (.sizeEq (.tparam 0) (.base 1 1)) = true := rfl

theorem evalPmeCheck_neg_sizeMismatch :
    evalPmeCheck emptyAssoc substU8 (.sizeEq (.tparam 0) (.base 2 2)) = false := rfl

theorem substOfKey_pos_in_bounds :
    (substOfKey ⟨0, [tyU32], [7]⟩).ty 0 = tyU32 ∧
      (substOfKey ⟨0, [tyU32], [7]⟩).cnst 0 = 7 :=
  ⟨rfl, rfl⟩

theorem substOfKey_neg_out_of_bounds_default :
    (substOfKey ⟨0, [tyU32], [7]⟩).ty 3 = tyU8 ∧
      (substOfKey ⟨0, [tyU32], [7]⟩).ty 3 ≠ tyU32 := by
  decide

/-- Sample 2-function crate: `fn 0` local with no PME calling `fn 1`; `fn 1` external (`localMir = false`)
    with a `sizeEq(T0, u16)` PME. -/
def sampleMixedCrate : CrateProg where
  fns := [
    ⟨emptyBounds, [], true, .call 1 [.tparam 0] []⟩,
    ⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], false, .skip⟩
  ]
  assoc := emptyAssoc

theorem isLocalFn_pos :
    isLocalFn sampleMixedCrate ⟨0, [tyU8], []⟩ = true := rfl

theorem isLocalFn_neg_external :
    isLocalFn sampleMixedCrate ⟨1, [tyU8], []⟩ = false := rfl

theorem allLocalMir_pos :
    AllLocalMir sampleMixedCrate [⟨0, [tyU8], []⟩] := by
  intro k hk
  simp at hk
  subst hk
  rfl

theorem allLocalMir_neg :
    ¬ AllLocalMir sampleMixedCrate [⟨0, [tyU8], []⟩, ⟨1, [tyU8], []⟩] := by
  intro h
  have h1 := h ⟨1, [tyU8], []⟩ (by simp)
  cases h1

theorem passesLocalPme_pos_external_mir :
    passesLocalPme sampleMixedCrate ⟨1, [tyU8], []⟩ = true := rfl

theorem passesLocalPme_neg_local_fail :
    passesLocalPme
      ⟨[⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩], emptyAssoc⟩
      ⟨0, [tyU8], []⟩ = false := rfl

theorem passesIntrinsicPme_pos_valid :
    passesIntrinsicPme sampleMixedCrate ⟨1, [tyU16], []⟩ = true := rfl

theorem passesIntrinsicPme_neg_external_fail :
    passesIntrinsicPme sampleMixedCrate ⟨1, [tyU8], []⟩ = false := rfl

theorem instTyList_pos :
    instTyList emptyAssoc substU8 [.tparam 0, .base 4 4] = some [tyU8, tyU32] := rfl

theorem instTyList_neg :
    instTyList emptyAssoc substU8 [.proj 0 (.tparam 0)] = none := rfl

theorem evalNatArgs_pos :
    evalNatArgs (fun _ => 3) [.cparam 0, .add (.cparam 0) (.lit 1)] = some [3, 4] := rfl

theorem evalNatArgs_neg_ctor :
    evalNatArgs (fun _ => 3) [.ctor 0 [.lit 1]] = none := rfl

theorem usedStmtRefs_pos_call :
    usedStmtRefs emptyAssoc substU8 (.call 1 [.tparam 0] [.lit 5]) =
      some [⟨1, [tyU8], [5]⟩] := rfl

theorem usedStmtRefs_neg_erases_deadBranch :
    usedStmtRefs emptyAssoc substU8 (.deadBranch (.call 1 [.tparam 0] [])) = some [] ∧
      usedStmtRefs emptyAssoc substU8 (.deadBranch (.call 1 [.tparam 0] [])) ≠
        some [⟨1, [tyU8], []⟩] := by
  decide

theorem mentionedStmtRefs_pos_keeps_deadBranch :
    mentionedStmtRefs emptyAssoc substU8 (.deadBranch (.call 1 [.tparam 0] [])) =
      some [⟨1, [tyU8], []⟩] := rfl

theorem mentionedStmtRefs_neg_bad_idx :
    mentionedStmtRefs emptyAssoc substAlign16
      (.deadBranch (.call 1 [] [.sub (.cparam 0) (.lit 1)])) = none := rfl

theorem monoEdges_pos_local :
    monoEdges false sampleMixedCrate ⟨0, [tyU16], []⟩ = some [⟨1, [tyU16], []⟩] := rfl

theorem monoEdges_neg_undef :
    monoEdges false sampleMixedCrate ⟨9, [], []⟩ = none := rfl

theorem collectAndCheck_pos_valid :
    collectAndCheck true
      ⟨[⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩], emptyAssoc⟩
      [⟨0, [tyU16], []⟩] 2 = .ok [⟨0, [tyU16], []⟩] := rfl

theorem collectAndCheck_neg_pmeError :
    collectAndCheck true
      ⟨[⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩], emptyAssoc⟩
      [⟨0, [tyU8], []⟩] 2 = .pmeError ⟨0, [tyU8], []⟩ := rfl

theorem collectAndCheck_neg_outOfFuel :
    collectAndCheck true sampleMixedCrate [⟨0, [tyU16], []⟩] 0 = .outOfFuel := rfl

theorem reachable_pos_step :
    Reachable false sampleMixedCrate [⟨0, [tyU16], []⟩] ⟨1, [tyU16], []⟩ :=
  @Reachable.step false sampleMixedCrate [⟨0, [tyU16], []⟩]
    ⟨0, [tyU16], []⟩ ⟨1, [tyU16], []⟩ [⟨1, [tyU16], []⟩]
    (Reachable.root (List.Mem.head _)) rfl (List.Mem.head _)

theorem reachable_neg_deadBranch_in_used :
    ¬ Reachable false
      ⟨[⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩,
        ⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ := by
  let P0 : CrateProg :=
    ⟨[⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩,
      ⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
  have hOnlyRoot : ∀ x, Reachable false P0 [⟨0, [], []⟩] x → x = ⟨0, [], []⟩ := by
    intro x hx
    induction hx with
    | root hmem =>
        simpa using hmem
    | step _ hm hk' ih =>
        subst ih
        simp [P0, monoEdges, usedStmtRefs] at hm
        subst hm
        cases hk'
  intro h
  have heq := hOnlyRoot _ h
  cases heq

theorem intrinsicEdges_pos_external_body :
    intrinsicEdges true
      ⟨[⟨emptyBounds, [], false, .call 0 [.base 1 1] []⟩], emptyAssoc⟩
      ⟨0, [], []⟩ = some [⟨0, [tyU8], []⟩] := rfl

theorem intrinsicEdges_neg_undef :
    intrinsicEdges false sampleMixedCrate ⟨9, [], []⟩ = none := rfl

theorem intrinsicReachable_pos_step :
    IntrinsicReachable false sampleMixedCrate [⟨0, [tyU16], []⟩] ⟨1, [tyU16], []⟩ :=
  @IntrinsicReachable.step false sampleMixedCrate [⟨0, [tyU16], []⟩]
    ⟨0, [tyU16], []⟩ ⟨1, [tyU16], []⟩ [⟨1, [tyU16], []⟩]
    (IntrinsicReachable.root (List.Mem.head _)) rfl (List.Mem.head _)

theorem intrinsicReachable_neg_deadBranch_in_used :
    ¬ IntrinsicReachable false
      ⟨[⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩,
        ⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ := by
  let P0 : CrateProg :=
    ⟨[⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩,
      ⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
  have hOnlyRoot : ∀ x, IntrinsicReachable false P0 [⟨0, [], []⟩] x → x = ⟨0, [], []⟩ := by
    intro x hx
    induction hx with
    | root hmem =>
        simpa using hmem
    | step _ hm hk' ih =>
        subst ih
        simp [P0, intrinsicEdges, usedStmtRefs] at hm
        subst hm
        cases hk'
  intro h
  have heq := hOnlyRoot _ h
  cases heq

theorem genericBodySafeUnconditional_pos_bounded :
    GenericBodySafeUnconditional
      ⟨⟨[0], []⟩, [], true, .skip⟩ (.packed 1 (.tparam 0)) packedNoAlignWf := by
  intro A σ τ hSat hi
  simp only [instTy, Option.map] at hi
  injection hi with hτ
  subst hτ
  simp [packedNoAlignWf, hSat.2.2.1 0 (by simp), hSat.1 0]

theorem genericBodySafeUnconditional_neg_emptyBounds :
    ¬ GenericBodySafeUnconditional
      ⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩
      (.packed 1 (.tparam 0)) packedNoAlignWf := by
  intro hSafe
  have h := hSafe emptyAssoc substAlign16 (.packed 1 align16U8) substAlign16_sat_emptyBounds rfl
  cases h

theorem genericBodySafeUnderPme_pos_sizeEq :
    GenericBodySafeUnderPme
      ⟨emptyBounds, [.sizeEq (.tparam 0) (.tparam 1)], true, .skip⟩
      (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by
  intro A σ τ _ hPme hi
  simp only [instTy] at hi
  injection hi with hτ
  subst hτ
  simpa [List.all, evalPmeCheck, instTy, eqProdByteSize] using hPme

theorem genericBodySafeUnderPme_neg_unguarded :
    ¬ GenericBodySafeUnderPme
      ⟨emptyBounds, [], true, .skip⟩ (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by
  intro hSafe
  have hEmpty : DeclBounds.sat emptyBounds emptyAssoc
      ⟨fun i => if i = 0 then tyU16 else tyU8, fun _ => 0⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      dsimp
      split <;> rfl
    · intro _ _ _ hA
      cases hA
    · intro _ hi
      cases hi
    · intro _ htr _ _ _
      cases htr
  have h := hSafe emptyAssoc ⟨fun i => if i = 0 then tyU16 else tyU8, fun _ => 0⟩
    (.prod tyU16 tyU8) hEmpty rfl rfl
  cases h

theorem checkMonoTarget_pos_pair :
    checkMonoTarget emptyAssoc eqProdByteSize
      (fun id => if id = 0 then some (.prod (.tparam 0) (.tparam 1)) else none)
      [⟨0, [tyU16, tyU16], []⟩] = true := rfl

theorem checkMonoTarget_neg_bad_inst :
    checkMonoTarget emptyAssoc eqProdByteSize
      (fun id => if id = 0 then some (.prod (.tparam 0) (.tparam 1)) else none)
      [⟨0, [tyU16, tyU8], []⟩] = false := rfl

theorem monoCaptureCertifiedOn_pos_pair :
    MonoCaptureCertifiedOn emptyAssoc eqProdByteSize
      (fun id => if id = 0 then some (.prod (.tparam 0) (.tparam 1)) else none)
      [⟨0, [tyU16, tyU16], []⟩] := by
  intro k hk
  simp at hk
  subst hk
  exact ⟨.prod (.tparam 0) (.tparam 1), .prod tyU16 tyU16, rfl, rfl, rfl⟩

theorem monoCaptureCertifiedOn_neg_missing_target :
    ¬ MonoCaptureCertifiedOn emptyAssoc eqProdByteSize
      (fun _ => none) [⟨0, [tyU16, tyU16], []⟩] := by
  intro h
  rcases h ⟨0, [tyU16, tyU16], []⟩ (by simp) with ⟨t, _, ht, _, _⟩
  cases ht

theorem fixedConstNoAlignBound_pos :
    FixedConstNoAlignBound (constZeroNoAlignWitness (.base 1 1)).1
      (constZeroNoAlignWitness (.base 1 1)).2 := by
  refine ⟨⟨fun _ => ⟨rfl, rfl⟩, fun _ _ rhs hA => ?_⟩, rfl⟩
  injection hA with hr; subst hr
  exact ⟨rfl, rfl⟩

theorem fixedConstNoAlignBound_neg_nonzero_cnst :
    ¬ FixedConstNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 := by
  intro h
  have hc := congrFun h.2 0
  cases hc

theorem keyHasPackedGuard_pos :
    keyHasPackedGuard
      ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      ⟨0, [tyU8], []⟩ = true := rfl

theorem keyHasPackedGuard_neg_missing_pme :
    keyHasPackedGuard
      ⟨[⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      ⟨0, [tyU8], []⟩ = false := rfl

theorem hasPackedPmeGuard_pos :
    HasPackedPmeGuard
      ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      [⟨0, [tyU8], []⟩] := by
  intro k hk
  simp at hk
  subst hk
  rfl

theorem hasPackedPmeGuard_neg :
    ¬ HasPackedPmeGuard
      ⟨[⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      [⟨0, [tyU8], []⟩] := by
  intro h
  have h0 := h ⟨0, [tyU8], []⟩ (by simp)
  cases h0

end Toy.SubstStable
