/-
  Canonical tightness counterexamples, headline counterexamples, non-vacuity witnesses,
  and positive controls for `Toy.SubstStable`.
  Every theorem in this file is kernel-checked with zero `sorry`.
-/
import Toy.SubstStable.Basic
import Toy.SubstStable.Lemmas
import Toy.SubstStable.Examples

namespace Toy.SubstStable

/-! ## Shared concrete expressions and crate programs -/

/-- Index expression `N + 1`. -/
def idxAddN1 : IdxTerm := .add (.cparam 0) (.lit 1)

/-- Index expression `1 + N`. -/
def idxAdd1N : IdxTerm := .add (.lit 1) (.cparam 0)

/-- Partial index expression `N - 1` (checked subtraction). -/
def idxSub1 : IdxTerm := .sub (.cparam 0) (.lit 1)

/-- Partial index expression `16 / N` (checked floor division). -/
def idxDiv0 : IdxTerm := .div (.lit 16) (.cparam 0)

/-- Crate checking `.idxValid (N - 1)` on `fn 0`. -/
def progSub1 : CrateProg :=
  ⟨[⟨emptyBounds, [.idxValid idxSub1], true, .skip⟩], emptyAssoc⟩

/-- Crate checking `.idxValid (16 / N)` on `fn 0`. -/
def progDiv0 : CrateProg :=
  ⟨[⟨emptyBounds, [.idxValid idxDiv0], true, .skip⟩], emptyAssoc⟩

/-- Local generic function asserting `size(T0) = size(u16)`. -/
def fnSizeEqU16 : GenFn :=
  ⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩

/-- External generic function (`localMir = false`) asserting `size(T0) = size(u16)`. -/
def fnExtSizeEqU16 : GenFn :=
  ⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], false, .skip⟩

/-- Caller mentioning `fn 1::<u8>` only inside a dead branch (`if false { ... }`). -/
def fnDeadCaller : GenFn :=
  ⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩

/-- Caller invoking `fn 1::<u8>` on a live path. -/
def fnLiveCaller : GenFn :=
  ⟨emptyBounds, [], true, .call 1 [.base 1 1] []⟩

/-- Crate with a dead-branch call to an ill-sized `fnSizeEqU16` instance. -/
def progDeadBranch : CrateProg := ⟨[fnDeadCaller, fnSizeEqU16], emptyAssoc⟩

/-- Crate with a live local `fnSizeEqU16` callee (for positive control). -/
def progLiveLocal : CrateProg := ⟨[fnLiveCaller, fnSizeEqU16], emptyAssoc⟩

/-- Crate where `fn 0` never calls or mentions `fn 1` (`fnSizeEqU16`). -/
def progUnreachedLib : CrateProg :=
  ⟨[⟨emptyBounds, [], true, .skip⟩, fnSizeEqU16], emptyAssoc⟩

/-- Crate calling external `fnExtSizeEqU16` (`localMir = false`) at invalid `u8`. -/
def progExtHole : CrateProg := ⟨[fnLiveCaller, fnExtSizeEqU16], emptyAssoc⟩

/-- 3-function callback crate: local `fn 0` calls external `fn 1` (`localMir = false`), whose
    body calls back into local `fn 2` (`localMir = true`) at invalid `u8`. -/
def progExtCallbackHole : CrateProg :=
  ⟨[fnLiveCaller, ⟨emptyBounds, [], false, .call 2 [.base 1 1] []⟩, fnSizeEqU16], emptyAssoc⟩

/-- Sound conservative definition-site check accepting closed scalar base types with `sz ≤ 4`. -/
def cClosedBaseLe4 : OpenTy → Bool
  | .base sz _ => decide (sz ≤ 4)
  | _ => false

/-- Generic `transmute_ref<Src, Dst>`-style function guarded only by `.sizeEq(T0, T1)`. -/
def fnTransmuteLike : GenFn :=
  ⟨emptyBounds, [.sizeEq (.tparam 0) (.tparam 1)], true, .skip⟩

/-- Out-of-bound witness map sending every open type to `(emptyAssoc, substAlign16)`. -/
def badAlign16Witness (_ : OpenTy) : AssocEnv × Subst :=
  (emptyAssoc, substAlign16)

/-- Complement of `packedNoAlignWf`. -/
def notPackedNoAlignWf (τ : ClosedTy) : Bool := !packedNoAlignWf τ

/-- Complement of `naiveDefPackedCheck`. -/
def notNaiveDefPackedCheck (t : OpenTy) : Bool := !naiveDefPackedCheck t

/-! ## 1. Tightness, non-vacuity, and positive controls for substitution stability -/

/-- Positive control: under `FullNoAlignBound`, `packedNoAlignWf` is substitution-stable and
    `naiveDefPackedCheck` is both sound and instance-complete. -/
theorem pc_fullNoAlign_naiveCheck_sound_and_complete :
    SubstStable FullNoAlignBound packedNoAlignWf ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck := by
  refine ⟨?_, ?_, ?_⟩
  · intro t A1 σ1 τ1 A2 σ2 τ2 hB1 hi1 hB2 hi2
    rw [packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB1 hi1,
      packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB2 hi2]
  · intro t A σ τ hC hB hi
    rw [packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hi]
    exact hC
  · intro t A σ τ hB hi hΦ
    rw [← packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hi]
    exact hΦ

/-- Dual soundness and completeness of `notNaiveDefPackedCheck` for `notPackedNoAlignWf`
    under `FullNoAlignBound` (used for symmetric tightness witnesses). -/
theorem notNaiveCheck_sound_and_complete_of_fullNoAlign :
    DefCheckSound FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck := by
  refine ⟨?_, ?_⟩
  · intro t A σ τ hC hB hi
    unfold notPackedNoAlignWf
    rw [packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hi]
    exact hC
  · intro t A σ τ hB hi hΦ
    unfold notNaiveDefPackedCheck
    rw [← packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign hB hi]
    exact hΦ

/-- Tightness of `hw : HasInstWitness B w` in `witnessDefCheck_sound_and_complete_iff_substStable`:
    `SubstStable FullNoAlignBound packedNoAlignWf` holds, `badAlign16Witness` violates
    `HasInstWitness`, and `witnessDefCheck` with `badAlign16Witness` fails `DefCheckComplete`. -/
theorem cex_witnessDefCheck_without_hasInstWitness :
    ¬ HasInstWitness FullNoAlignBound badAlign16Witness ∧
      SubstStable FullNoAlignBound packedNoAlignWf ∧
      ¬ (DefCheckSound FullNoAlignBound packedNoAlignWf
            (witnessDefCheck packedNoAlignWf badAlign16Witness) ∧
          DefCheckComplete FullNoAlignBound packedNoAlignWf
            (witnessDefCheck packedNoAlignWf badAlign16Witness)) := by
  refine ⟨hasInstWitness_neg_bad_subst, pc_fullNoAlign_naiveCheck_sound_and_complete.1, ?_⟩
  rintro ⟨_, hComp⟩
  have h := hComp (.packed 1 (.tparam 0)) defaultNoAlignEnv.1 defaultNoAlignEnv.2
    (.packed 1 tyU8) fullNoAlignBound_pos_scalars rfl rfl
  cases h

/-- Non-vacuity witness for `exists_sound_complete_defCheck_iff_substStable` and
    `witnessDefCheck_sound_and_complete_iff_substStable`. -/
theorem nonvacuity_substStable_witness :
    HasInstWitness FixedConstNoAlignBound constZeroNoAlignWitness ∧
      SubstStable FixedConstNoAlignBound packedNoAlignWf ∧
      witnessDefCheck packedNoAlignWf constZeroNoAlignWitness (.packed 1 (.tparam 0)) = true ∧
      witnessDefCheck packedNoAlignWf constZeroNoAlignWitness
        (.packed 1 (.align 16 (.tparam 0))) = false := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rintro t ⟨A, σ, τ, ⟨_, hc⟩, hi⟩
    exact ⟨fixedConstNoAlignBound_pos, instTy_constZeroNoAlignWitness_isSome hc hi⟩
  · intro t A1 σ1 τ1 A2 σ2 τ2 hB1 hi1 hB2 hi2
    exact pc_fullNoAlign_naiveCheck_sound_and_complete.1 t A1 σ1 τ1 A2 σ2 τ2 hB1.1 hi1 hB2.1 hi2

/-! ## 2. Tightness and non-vacuity for instability-forces-incompleteness -/

/-- Non-vacuity witness for `not_defCheckComplete_of_defCheckSound_of_unstable_witness` and
    `sizeLe_not_substStable_and_incomplete_of_defCheckSound` using the non-vacuous conservative
    check `cClosedBaseLe4` (which accepts closed scalars with `sz ≤ 4` and rejects `.tparam 0`). -/
theorem nonvacuity_unstable_sizeLe :
    DefCheckSound unbounded (sizeLe 4) cClosedBaseLe4 ∧
      cClosedBaseLe4 (.base 1 1) = true ∧
      cClosedBaseLe4 (.tparam 0) = false ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      sizeLe 4 tyU8 = true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      sizeLe 4 tyU64 = false := by
  refine ⟨?_, rfl, rfl, trivial, rfl, rfl, trivial, rfl, rfl⟩
  intro t _ _ τ hC _ hi
  cases t <;> simp [cClosedBaseLe4] at hC
  injection hi with hτ
  subst hτ
  exact decide_eq_true hC

/-- Tightness of `hS : DefCheckSound B Φ C`: without soundness, `fun _ => true` accepts
    `.tparam 0` and satisfies `DefCheckComplete` despite the instability witness. -/
theorem cex_incompleteness_without_soundness :
    ¬ DefCheckSound unbounded (sizeLe 4) (fun _ => true) ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      sizeLe 4 tyU8 = true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      sizeLe 4 tyU64 = false ∧
      (fun _ : OpenTy => true) (.tparam 0) = true ∧
      DefCheckComplete unbounded (sizeLe 4) (fun _ => true) ∧
      ¬ ((fun _ : OpenTy => true) (.tparam 0) = false ∧
          ¬ DefCheckComplete unbounded (sizeLe 4) (fun _ => true)) := by
  refine ⟨defCheckSound_neg_const_true, trivial, rfl, rfl, trivial, rfl, rfl,
    rfl, defCheckComplete_pos_const_true, ?_⟩
  rintro ⟨hF, _⟩
  cases hF

/-- Tightness of `hB1 : B A1 σ1` in `not_defCheckComplete_of_defCheckSound_of_unstable_witness`. -/
theorem cex_incompleteness_without_pos_bound :
    DefCheckSound FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      ¬ FullNoAlignBound emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      notPackedNoAlignWf (.packed 1 align16U8) = true ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      notPackedNoAlignWf (.packed 1 tyU8) = false ∧
      DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      ¬ (notNaiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck) := by
  refine ⟨notNaiveCheck_sound_and_complete_of_fullNoAlign.1,
    fullNoAlignBound_neg_align_subst, rfl, rfl, fullNoAlignBound_pos_scalars, rfl, rfl,
    notNaiveCheck_sound_and_complete_of_fullNoAlign.2, ?_⟩
  rintro ⟨_, hInc⟩
  exact hInc notNaiveCheck_sound_and_complete_of_fullNoAlign.2

/-- Tightness of `hi1 : instTy A1 σ1 t = some τ1`. -/
theorem cex_incompleteness_without_pos_inst :
    DefCheckSound FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) ≠
        some (.packed 1 align16U8) ∧
      notPackedNoAlignWf (.packed 1 align16U8) = true ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      notPackedNoAlignWf (.packed 1 tyU8) = false ∧
      DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      ¬ (notNaiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck) := by
  refine ⟨notNaiveCheck_sound_and_complete_of_fullNoAlign.1,
    fullNoAlignBound_pos_scalars, by decide, rfl, fullNoAlignBound_pos_scalars, rfl, rfl,
    notNaiveCheck_sound_and_complete_of_fullNoAlign.2, ?_⟩
  rintro ⟨_, hInc⟩
  exact hInc notNaiveCheck_sound_and_complete_of_fullNoAlign.2

/-- Tightness of `hΦ1 : Φ τ1 = true`. -/
theorem cex_incompleteness_without_pos_prop :
    DefCheckSound unbounded (fun _ => false) (fun _ => false) ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      (fun _ : ClosedTy => false) tyU8 ≠ true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      (fun _ : ClosedTy => false) tyU64 = false ∧
      DefCheckComplete unbounded (fun _ => false) (fun _ => false) ∧
      ¬ ((fun _ : OpenTy => false) (.tparam 0) = false ∧
          ¬ DefCheckComplete unbounded (fun _ => false) (fun _ => false)) := by
  have hComp : DefCheckComplete unbounded (fun _ => false) (fun _ => false) :=
    fun _ _ _ _ _ _ hΦ => (by cases hΦ)
  refine ⟨fun _ _ _ _ hC => (by cases hC), trivial, rfl, (by decide), trivial, rfl, rfl,
    hComp, ?_⟩
  rintro ⟨_, hInc⟩
  exact hInc hComp

/-- Tightness of `hB2 : B A2 σ2`. -/
theorem cex_incompleteness_without_neg_bound :
    DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      packedNoAlignWf (.packed 1 tyU8) = true ∧
      ¬ FullNoAlignBound emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ (naiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck) := by
  refine ⟨pc_fullNoAlign_naiveCheck_sound_and_complete.2.1,
    fullNoAlignBound_pos_scalars, rfl, rfl, fullNoAlignBound_neg_align_subst, rfl, rfl,
    rfl, pc_fullNoAlign_naiveCheck_sound_and_complete.2.2, ?_⟩
  rintro ⟨hF, _⟩
  cases hF

/-- Tightness of `hi2 : instTy A2 σ2 t = some τ2`. -/
theorem cex_incompleteness_without_neg_inst :
    DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      packedNoAlignWf (.packed 1 tyU8) = true ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) ≠
        some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ (naiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck) := by
  refine ⟨pc_fullNoAlign_naiveCheck_sound_and_complete.2.1,
    fullNoAlignBound_pos_scalars, rfl, rfl, fullNoAlignBound_pos_scalars, by decide, rfl,
    rfl, pc_fullNoAlign_naiveCheck_sound_and_complete.2.2, ?_⟩
  rintro ⟨hF, _⟩
  cases hF

/-- Tightness of `hΦ2 : Φ τ2 = false`. -/
theorem cex_incompleteness_without_neg_prop :
    DefCheckSound unbounded (fun _ => true) (fun _ => true) ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      (fun _ : ClosedTy => true) tyU8 = true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      (fun _ : ClosedTy => true) tyU64 ≠ false ∧
      (fun _ : OpenTy => true) (.tparam 0) = true ∧
      DefCheckComplete unbounded (fun _ => true) (fun _ => true) ∧
      ¬ ((fun _ : OpenTy => true) (.tparam 0) = false ∧
          ¬ DefCheckComplete unbounded (fun _ => true) (fun _ => true)) := by
  refine ⟨fun _ _ _ _ _ _ _ => rfl, trivial, rfl, rfl, trivial, rfl, by decide,
    rfl, fun _ _ _ _ _ _ _ => rfl, ?_⟩
  rintro ⟨hF, _⟩
  cases hF

/-! ## 3. Packed/over-aligned counterexamples, tightness, and non-vacuity -/

/-- `sampleAssoc` with `substU8` satisfies `DeclBounds.sat emptyBounds` (all parameters and
    associated types are themselves `packedNoAlignWf`). -/
theorem sampleAssoc_substU8_sat_emptyBounds :
    DeclBounds.sat emptyBounds sampleAssoc substU8 := by
  refine ⟨fun _ => rfl, ?_, fun _ hi => (by cases hi), fun _ htr _ _ _ => (by cases htr)⟩
  intro tr src rhs hA
  unfold sampleAssoc at hA
  split at hA
  · injection hA with hr; subst hr; rfl
  · injection hA with hr; subst hr; rfl
  · cases hA

/-- Under `emptyBounds`, `naiveDefPackedCheck` accepts both `Packed<T0>` and
    `Packed<<T0 as Trait0>::Assoc>`, yet legal instantiations normalize both to
    `.packed 1 align16U8`, violating `packedNoAlignWf`; hence `naiveDefPackedCheck`
    is unsound under `DeclBounds.sat emptyBounds`. -/
theorem cex_naiveDefPackedCheck_tparam_and_proj :
    naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      naiveDefPackedCheck (.packed 1 (.proj 0 (.tparam 0))) = true ∧
      DeclBounds.sat emptyBounds sampleAssoc substU8 ∧
      instTy sampleAssoc substU8 (.packed 1 (.proj 0 (.tparam 0))) =
        some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck := by
  refine ⟨rfl, substAlign16_sat_emptyBounds, rfl, rfl, sampleAssoc_substU8_sat_emptyBounds,
    rfl, rfl, ?_⟩
  intro hS
  have h := hS (.packed 1 (.tparam 0)) emptyAssoc substAlign16 (.packed 1 align16U8)
    rfl substAlign16_sat_emptyBounds rfl
  cases h

/-- `packedNoAlignWf` is not substitution-stable under `DeclBounds.sat emptyBounds`. -/
theorem packedNoAlignWf_not_substStable_emptyBounds :
    ¬ SubstStable (DeclBounds.sat emptyBounds) packedNoAlignWf := by
  intro hStab
  have hEmptyU8 : DeclBounds.sat emptyBounds emptyAssoc substU8 :=
    ⟨fun _ => rfl, fun _ _ _ hA => (by cases hA),
      fun _ hi => (by cases hi), fun _ htr _ _ _ => (by cases htr)⟩
  have h := hStab (.packed 1 (.tparam 0))
    emptyAssoc substU8 (.packed 1 tyU8)
    emptyAssoc substAlign16 (.packed 1 align16U8)
    hEmptyU8 rfl substAlign16_sat_emptyBounds rfl
  cases h

/-- Tightness of `hchk : boundedDefPackedCheck d t = true` in `boundedDefPackedCheck_sound`. -/
theorem cex_boundedDefPackedCheck_without_check :
    boundedDefPackedCheck emptyBounds (.packed 1 (.tparam 0)) = false ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false :=
  ⟨rfl, substAlign16_sat_emptyBounds, rfl, rfl⟩

/-- Tightness of `hsat : DeclBounds.sat d A σ` in `boundedDefPackedCheck_sound`. -/
theorem cex_boundedDefPackedCheck_without_boundsSat :
    boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      ¬ DeclBounds.sat ⟨[0], []⟩ emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false :=
  ⟨rfl, declBoundsSat_neg_param_has_align, rfl, rfl⟩

/-- Tightness of `hinst : instTy A σ t = some τ` in `boundedDefPackedCheck_sound`. -/
theorem cex_boundedDefPackedCheck_without_inst :
    boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat ⟨[0], []⟩ emptyAssoc
        ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
        (.packed 1 (.tparam 0)) ≠ some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false :=
  ⟨rfl, declBoundsSat_pos_selective, by decide, rfl⟩

/-- Non-vacuity witness for `boundedDefPackedCheck_sound` and `evalPmeCheck_packedWf_iff`:
    selective bound `⟨[0], []⟩` accepts `(Packed<T0>, T1)` even when `T1 := align16U8`. -/
theorem nonvacuity_boundedDefPackedCheck_selective :
    boundedDefPackedCheck ⟨[0], []⟩ (.prod (.packed 1 (.tparam 0)) (.tparam 1)) = true ∧
      DeclBounds.sat ⟨[0], []⟩ emptyAssoc
        ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
        (.prod (.packed 1 (.tparam 0)) (.tparam 1)) =
        some (.prod (.packed 1 tyU8) align16U8) ∧
      evalPmeCheck emptyAssoc ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
        (.packedWf (.prod (.packed 1 (.tparam 0)) (.tparam 1))) = true :=
  ⟨rfl, declBoundsSat_pos_selective, rfl, rfl⟩

/-! ## 4. Const-index counterexamples, tightness, and non-vacuity -/

/-- Commutativity counterexample for rigid syntactic AST equality: `N + 1` and `1 + N` are
    semantically equal across all const valuations (`IdxSemEq`), yet rigid syntactic AST
    equality rejects them (`decide (idxAddN1 = idxAdd1N) = false`). -/
theorem cex_rigid_ast_eq_incomplete_comm_add :
    IdxSemEq idxAddN1 idxAdd1N ∧
      decide (idxAddN1 = idxAdd1N) = false :=
  ⟨idxSemEq_pos_comm_add, rfl⟩

/-- Partial checked-subtraction PME counterexample: `N - 1` succeeds at `N = 1` (admitting
    valid closed array instance `[u8; 0]` and passing `collectAndCheck`), yet fails evaluation
    at `N = 0` (`evalIdx = none`, `instTy = none`, and `collectAndCheck` yields `.pmeError`). -/
theorem cex_partial_sub_post_mono_error :
    isCtorIdx idxSub1 = false ∧
      ¬ IdxTotal idxSub1 ∧
      evalIdx (fun _ => 1) idxSub1 = some (.nat 0) ∧
      instTy emptyAssoc ⟨fun _ => tyU8, fun _ => 1⟩ (.arr (.base 1 1) idxSub1) =
        some (.arr tyU8 (.nat 0)) ∧
      collectAndCheck true progSub1 [⟨0, [], [1]⟩] 2 = .ok [⟨0, [], [1]⟩] ∧
      evalIdx (fun _ => 0) idxSub1 = none ∧
      instTy emptyAssoc ⟨fun _ => tyU8, fun _ => 0⟩ (.arr (.base 1 1) idxSub1) = none ∧
      collectAndCheck true progSub1 [⟨0, [], [0]⟩] 2 = .pmeError ⟨0, [], [0]⟩ :=
  ⟨rfl, idxTotal_neg_sub, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Companion partial-division PME counterexample: `16 / N` succeeds at `N = 2` and fails with
    a post-monomorphization error at `N = 0`. -/
theorem cex_partial_div_zero_post_mono_error :
    isCtorIdx idxDiv0 = false ∧
      ¬ IdxTotal idxDiv0 ∧
      evalIdx (fun _ => 2) idxDiv0 = some (.nat 8) ∧
      collectAndCheck true progDiv0 [⟨0, [], [2]⟩] 2 = .ok [⟨0, [], [2]⟩] ∧
      evalIdx (fun _ => 0) idxDiv0 = none ∧
      collectAndCheck true progDiv0 [⟨0, [], [0]⟩] 2 = .pmeError ⟨0, [], [0]⟩ := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro h
  have h0 := h (fun _ => 0)
  simp [idxDiv0, evalIdx] at h0

/-- Tightness of `h1 : isCtorIdx e1 = true` in `idxSemEq_iff_eq_of_isCtorIdx`:
    `0 + N` and `N` satisfy `isCtorIdx (.cparam 0) = true` and `IdxSemEq`, yet are unequal. -/
theorem cex_idxSemEq_drop_left_isCtorIdx :
    isCtorIdx (.add (.lit 0) (.cparam 0)) = false ∧
      isCtorIdx (.cparam 0) = true ∧
      IdxSemEq (.add (.lit 0) (.cparam 0)) (.cparam 0) ∧
      ¬ (IdxSemEq (.add (.lit 0) (.cparam 0)) (.cparam 0) ↔
          (.add (.lit 0) (.cparam 0) : IdxTerm) = .cparam 0) := by
  have hSem : IdxSemEq (.add (.lit 0) (.cparam 0)) (.cparam 0) := by
    intro γ
    simp [evalIdx]
  refine ⟨rfl, rfl, hSem, ?_⟩
  intro hIff
  have hEq := hIff.mp hSem
  cases hEq

/-- Tightness of `h2 : isCtorIdx e2 = true` in `idxSemEq_iff_eq_of_isCtorIdx`:
    `N` and `N + 0` satisfy `isCtorIdx (.cparam 0) = true` and `IdxSemEq`, yet are unequal. -/
theorem cex_idxSemEq_drop_right_isCtorIdx :
    isCtorIdx (.cparam 0) = true ∧
      isCtorIdx (.add (.cparam 0) (.lit 0)) = false ∧
      IdxSemEq (.cparam 0) (.add (.cparam 0) (.lit 0)) ∧
      ¬ (IdxSemEq (.cparam 0) (.add (.cparam 0) (.lit 0)) ↔
          (.cparam 0 : IdxTerm) = .add (.cparam 0) (.lit 0)) := by
  have hSem : IdxSemEq (.cparam 0) (.add (.cparam 0) (.lit 0)) := by
    intro γ
    simp [evalIdx]
  refine ⟨rfl, rfl, hSem, ?_⟩
  intro hIff
  have hEq := hIff.mp hSem
  cases hEq

/-- Non-vacuity and positive control for `idxTotal_of_isCtorIdx` and
    `idxSemEq_iff_eq_of_isCtorIdx`: nested constructor index expression over canonical values. -/
theorem nonvacuity_ctor_indices :
    isCtorIdx (.ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) = true ∧
      isCtorIdx (.ctor 2 [.cparam 1, .ctor 1 [.lit 4]]) = true ∧
      evalIdx (fun i => i + 10) (.ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) =
        some (.ctor 2 [.nat 10, .ctor 1 [.nat 4]]) ∧
      decide ((.ctor 2 [.cparam 0, .ctor 1 [.lit 4]] : IdxTerm) =
        .ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) = true ∧
      decide ((.ctor 2 [.cparam 0, .ctor 1 [.lit 4]] : IdxTerm) =
        .ctor 2 [.cparam 1, .ctor 1 [.lit 4]]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. Post-monomorphization assertion collection counterexamples & witnesses -/

/-- Dead-branch PME contrast: on `progDeadBranch`, used-only collection (`false`) erases the
    dead branch and returns `.ok`, whereas mentioned-items collection (`true`) visits the
    dead-branch callee `⟨1, [tyU8], []⟩` and reports `.pmeError`. -/
theorem cex_deadBranch_pme_caught_by_mentioned_missed_by_used :
    collectAndCheck false progDeadBranch [⟨0, [], []⟩] 4 = .ok [⟨0, [], []⟩] ∧
      collectAndCheck true progDeadBranch [⟨0, [], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ ∧
      passesIntrinsicPme progDeadBranch ⟨1, [tyU8], []⟩ = false :=
  ⟨rfl, rfl, rfl⟩

/-- Uncollected-instance gap (and tightness of `hReach` in
    `collectAndCheck_ok_intrinsicPme_of_allLocalMir`): `progUnreachedLib` passes mentioned-mode
    collection with all-local MIR, yet the unreached instance `⟨1, [tyU8], []⟩` is neither
    `IntrinsicReachable` nor `Reachable` and violates `passesIntrinsicPme`. -/
theorem cex_uncollected_instance_violates_pme :
    collectAndCheck true progUnreachedLib [⟨0, [], []⟩] 4 = .ok [⟨0, [], []⟩] ∧
      AllLocalMir progUnreachedLib [⟨0, [], []⟩] ∧
      ¬ IntrinsicReachable true progUnreachedLib [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      ¬ Reachable true progUnreachedLib [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      passesIntrinsicPme progUnreachedLib ⟨1, [tyU8], []⟩ = false := by
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · intro k hk
    simp at hk
    subst hk
    rfl
  · have hOnlyRoot :
        ∀ x, IntrinsicReachable true progUnreachedLib [⟨0, [], []⟩] x → x = ⟨0, [], []⟩ := by
      intro x hx
      induction hx with
      | root hmem => simpa using hmem
      | step _ hm hk' ih =>
          subst ih
          simp [progUnreachedLib, intrinsicEdges, mentionedStmtRefs] at hm
          subst hm
          cases hk'
    intro h
    have heq := hOnlyRoot _ h
    cases heq
  · have hOnlyRoot : ∀ x, Reachable true progUnreachedLib [⟨0, [], []⟩] x → x = ⟨0, [], []⟩ := by
      intro x hx
      induction hx with
      | root hmem => simpa using hmem
      | step _ hm hk' ih =>
          subst ih
          simp [progUnreachedLib, monoEdges, mentionedStmtRefs] at hm
          subst hm
          cases hk'
    intro h
    have heq := hOnlyRoot _ h
    cases heq

/-- Direct external-MIR per-crate hole: when `fn 1` has `localMir = false` (`progExtHole`),
    collection succeeds and inserts `⟨1, [tyU8], []⟩` with `passesLocalPme = true`, yet
    `passesIntrinsicPme` is `false`. -/
theorem cex_external_mir_pme_hole :
    collectAndCheck true progExtHole [⟨0, [], []⟩] 4 =
        .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      ¬ AllLocalMir progExtHole [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      IntrinsicReachable true progExtHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      Reachable true progExtHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      passesLocalPme progExtHole ⟨1, [tyU8], []⟩ = true ∧
      passesIntrinsicPme progExtHole ⟨1, [tyU8], []⟩ = false := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro hLoc
    have h1 := hLoc ⟨1, [tyU8], []⟩ (by simp)
    cases h1
  · exact @IntrinsicReachable.step true progExtHole [⟨0, [], []⟩]
      ⟨0, [], []⟩ ⟨1, [tyU8], []⟩ [⟨1, [tyU8], []⟩]
      (IntrinsicReachable.root (List.Mem.head _)) rfl (List.Mem.head _)
  · exact @Reachable.step true progExtHole [⟨0, [], []⟩]
      ⟨0, [], []⟩ ⟨1, [tyU8], []⟩ [⟨1, [tyU8], []⟩]
      (Reachable.root (List.Mem.head _)) rfl (List.Mem.head _)

/-- External-to-local callback hole (and tightness of crate-wide `hLoc : AllLocalMir P T` in
    `intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir` and
    `collectAndCheck_ok_intrinsicPme_of_allLocalMir` even when `isLocalFn P k = true`):
    on `progExtCallbackHole`, external `fn 1` (`localMir = false`) truncates `monoEdges`, so
    local callback `⟨2, [tyU8], []⟩` (`isLocalFn = true`) is `IntrinsicReachable`, not
    `Reachable`, skipped by `collectAndCheck`, and falsifies `passesIntrinsicPme`. -/
theorem cex_external_callback_local_pme_hole :
    collectAndCheck true progExtCallbackHole [⟨0, [], []⟩] 6 =
        .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      ¬ AllLocalMir progExtCallbackHole [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      isLocalFn progExtCallbackHole ⟨2, [tyU8], []⟩ = true ∧
      IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ (IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ↔
          Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩) ∧
      passesIntrinsicPme progExtCallbackHole ⟨2, [tyU8], []⟩ = false := by
  have hIntr : IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ := by
    have h1 : IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ :=
      @IntrinsicReachable.step true progExtCallbackHole [⟨0, [], []⟩]
        ⟨0, [], []⟩ ⟨1, [tyU8], []⟩ [⟨1, [tyU8], []⟩]
        (IntrinsicReachable.root (List.Mem.head _)) rfl (List.Mem.head _)
    exact @IntrinsicReachable.step true progExtCallbackHole [⟨0, [], []⟩]
      ⟨1, [tyU8], []⟩ ⟨2, [tyU8], []⟩ [⟨2, [tyU8], []⟩]
      h1 rfl (List.Mem.head _)
  have hNotReach : ¬ Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ := by
    have hBound :
        ∀ x, Reachable true progExtCallbackHole [⟨0, [], []⟩] x →
          x = ⟨0, [], []⟩ ∨ x = ⟨1, [tyU8], []⟩ := by
      intro x hx
      induction hx with
      | root hmem =>
          left
          simpa using hmem
      | step _ hm hk' ih =>
          rcases ih with rfl | rfl
          · simp [progExtCallbackHole, fnLiveCaller, monoEdges, mentionedStmtRefs,
              instTyList, instTy, evalNatArgs] at hm
            subst hm
            right
            simpa [tyU8] using hk'
          · simp [progExtCallbackHole, monoEdges] at hm
            subst hm
            cases hk'
    intro hR
    rcases hBound _ hR with h0 | h1
    · cases h0
    · cases h1
  refine ⟨rfl, ?_, rfl, hIntr, hNotReach, fun hIff => hNotReach (hIff.mp hIntr), rfl⟩
  intro hLoc
  have h1 := hLoc ⟨1, [tyU8], []⟩ (by simp)
  cases h1

/-- Tightness of `hOk : collectAndCheck ... = .ok T` across `collectAndCheck_ok_mem_and_localPme`,
    `intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir`, and
    `collectAndCheck_ok_intrinsicPme_of_allLocalMir`: when collection fails (with `.pmeError` or
    `.outOfFuel` rather than `.ok []`), `AllLocalMir P []` holds vacuously while membership,
    adequacy (`IntrinsicReachable ↔ Reachable`), and `passesIntrinsicPme` all fail. -/
theorem cex_pme_collection_not_ok :
    collectAndCheck true progLiveLocal [⟨1, [tyU8], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ ∧
      collectAndCheck true progExtCallbackHole [⟨0, [], []⟩] 0 ≠ .ok [] ∧
      AllLocalMir progExtCallbackHole [] ∧
      (⟨0, [], []⟩ : MonoKey) ∉ ([] : List MonoKey) ∧
      Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨0, [], []⟩ ∧
      IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ (IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ↔
          Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩) ∧
      passesIntrinsicPme progExtCallbackHole ⟨2, [tyU8], []⟩ = false :=
  ⟨rfl, by decide, fun _ hk => (by cases hk), by simp, Reachable.root (List.Mem.head _),
    cex_external_callback_local_pme_hole.2.2.2.1,
    cex_external_callback_local_pme_hole.2.2.2.2.2.1, rfl⟩

/-- Non-vacuity and positive control for PME collection: with `includeMentioned = true` and
    local MIR on all functions, valid dead-branch and live calls pass collection, are both
    `IntrinsicReachable` and `Reachable`, and satisfy `passesIntrinsicPme`, while invalid local
    calls fail with `.pmeError`. -/
theorem nonvacuity_pme_collection_mentioned :
    let Pvalid : CrateProg :=
      ⟨[⟨emptyBounds, [], true,
          .seq (.call 1 [.base 2 2] []) (.deadBranch (.call 1 [.arr (.base 1 1) (.lit 2)] []))⟩,
        fnSizeEqU16], emptyAssoc⟩
    let Tvalid : List MonoKey :=
      [⟨0, [], []⟩, ⟨1, [tyU16], []⟩, ⟨1, [.arr tyU8 (.nat 2)], []⟩]
    collectAndCheck true Pvalid [⟨0, [], []⟩] 6 = .ok Tvalid ∧
      AllLocalMir Pvalid Tvalid ∧
      IntrinsicReachable true Pvalid [⟨0, [], []⟩] ⟨1, [.arr tyU8 (.nat 2)], []⟩ ∧
      Reachable true Pvalid [⟨0, [], []⟩] ⟨1, [.arr tyU8 (.nat 2)], []⟩ ∧
      passesIntrinsicPme Pvalid ⟨1, [.arr tyU8 (.nat 2)], []⟩ = true ∧
      collectAndCheck true progLiveLocal [⟨0, [], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl | rfl <;> rfl
  · exact @IntrinsicReachable.step true _ [⟨0, [], []⟩]
      ⟨0, [], []⟩ ⟨1, [.arr tyU8 (.nat 2)], []⟩
      [⟨1, [tyU16], []⟩, ⟨1, [.arr tyU8 (.nat 2)], []⟩]
      (IntrinsicReachable.root (List.Mem.head _)) rfl (by simp)
  · exact @Reachable.step true _ [⟨0, [], []⟩]
      ⟨0, [], []⟩ ⟨1, [.arr tyU8 (.nat 2)], []⟩
      [⟨1, [tyU16], []⟩, ⟨1, [.arr tyU8 (.nat 2)], []⟩]
      (Reachable.root (List.Mem.head _)) rfl (by simp)

/-! ## 6. Generic vs. monomorphic IR capture counterexamples & witnesses -/

private theorem mayHaveAlignUnder_false_sound_aux
    {d : DeclBounds} {A : AssocEnv} {σ : Subst} (hsat : DeclBounds.sat d A σ) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      mayHaveAlignUnder d t = false → instTy A σ t = some τ → hasAlignWrapper τ = false
  | .base _ _, _, _, hi => by injection hi with h; subst h; rfl
  | .tparam i, _, hm, hi => by
      injection hi with h; subst h
      simp [mayHaveAlignUnder] at hm
      exact hsat.2.2.1 i hm
  | .prod a b, _, hm, hi => by
      simp [mayHaveAlignUnder] at hm
      simp only [instTy] at hi
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hi
      subst hi
      simp [hasAlignWrapper, mayHaveAlignUnder_false_sound_aux hsat hm.1 ha,
        mayHaveAlignUnder_false_sound_aux hsat hm.2 hb]
  | .packed _ inner, _, hm, hi => by
      simp only [mayHaveAlignUnder] at hm
      simp only [instTy, Option.map] at hi
      cases hin : instTy A σ inner <;> simp [hin] at hi
      subst hi
      simpa [hasAlignWrapper] using mayHaveAlignUnder_false_sound_aux hsat hm hin
  | .align _ _, _, hm, _ => by cases hm
  | .arr elem idx, _, hm, hi => by
      simp only [mayHaveAlignUnder] at hm
      simp only [instTy] at hi
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hi
      subst hi
      simpa [hasAlignWrapper] using mayHaveAlignUnder_false_sound_aux hsat hm he
  | .proj tr arg, _, hm, hi => by
      simp [mayHaveAlignUnder] at hm
      simp only [instTy] at hi
      cases ha : instTy A σ arg <;> simp [ha] at hi
      exact hsat.2.2.2 tr hm _ _ hi

private theorem boundedDefPackedCheck_defCheckSound_aux (d : DeclBounds) :
    DefCheckSound (DeclBounds.sat d) packedNoAlignWf (boundedDefPackedCheck d) := by
  intro t A σ τ hchk hsat hinst
  induction t generalizing τ with
  | base _ _ => injection hinst with h; subst h; rfl
  | tparam i => injection hinst with h; subst h; exact hsat.1 i
  | prod a b iha ihb =>
      simp [boundedDefPackedCheck] at hchk
      simp only [instTy] at hinst
      cases ha : instTy A σ a <;> cases hb : instTy A σ b <;> simp [ha, hb] at hinst
      subst hinst
      simp [packedNoAlignWf, iha _ hchk.1 ha, ihb _ hchk.2 hb]
  | packed _ inner ih =>
      simp [boundedDefPackedCheck] at hchk
      simp only [instTy, Option.map] at hinst
      cases hin : instTy A σ inner <;> simp [hin] at hinst
      subst hinst
      simp [packedNoAlignWf, mayHaveAlignUnder_false_sound_aux hsat hchk.1 hin, ih _ hchk.2 hin]
  | align _ inner ih =>
      simp only [boundedDefPackedCheck] at hchk
      simp only [instTy, Option.map] at hinst
      cases hin : instTy A σ inner <;> simp [hin] at hinst
      subst hinst
      simpa [packedNoAlignWf] using ih _ hchk hin
  | arr elem idx ih =>
      simp only [boundedDefPackedCheck] at hchk
      simp only [instTy] at hinst
      cases he : instTy A σ elem <;> cases hv : evalIdx σ.cnst idx <;> simp [he, hv] at hinst
      subst hinst
      simpa [packedNoAlignWf] using ih _ hchk he
  | proj tr arg _ =>
      simp only [instTy] at hinst
      cases ha : instTy A σ arg <;> simp [ha] at hinst
      exact hsat.2.1 tr _ _ hinst

/-- Unstated-bound counterexample for generic IR capture (and tightness of `hEntails` in
    `defCheckSound_of_boundEntails` and
    `genericBodySafeUnconditional_of_defCheckSound_of_boundEntails`): `packedNoAlignWf` is
    substitution-stable and `naiveDefPackedCheck` is sound under the unstated `FullNoAlignBound`,
    yet when the generic source declares only `emptyBounds`, `emptyBounds` does not entail
    `FullNoAlignBound`, and relying on `naiveDefPackedCheck` fails both `DefCheckSound` and
    `GenericBodySafeUnconditional`. -/
theorem cex_generic_capture_unstated_bound_unsound :
    SubstStable FullNoAlignBound packedNoAlignWf ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ BoundEntails (DeclBounds.sat emptyBounds) FullNoAlignBound ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck ∧
      ¬ GenericBodySafeUnconditional ⟨emptyBounds, [], true, .skip⟩
          (.packed 1 (.tparam 0)) packedNoAlignWf := by
  refine ⟨pc_fullNoAlign_naiveCheck_sound_and_complete.1,
    pc_fullNoAlign_naiveCheck_sound_and_complete.2.1,
    boundEntails_neg_empty_to_full,
    rfl,
    substAlign16_sat_emptyBounds,
    rfl,
    rfl,
    cex_naiveDefPackedCheck_tparam_and_proj.2.2.2.2.2.2.2,
    ?_⟩
  intro hUnc
  have h := hUnc emptyAssoc substAlign16 (.packed 1 align16U8) substAlign16_sat_emptyBounds rfl
  cases h

/-- PME-guarded generic-capture gap: `fnTransmuteLike` (`transmute_ref<Src, Dst>` guarded by
    `.sizeEq(T0, T1)`) satisfies `GenericBodySafeUnderPme` for `eqProdByteSize`, yet fails
    `GenericBodySafeUnconditional` when generic IR is captured without assuming PME admission. -/
theorem cex_pme_guarded_fn_unsound_without_pme_assumption :
    GenericBodySafeUnderPme fnTransmuteLike (.prod (.tparam 0) (.tparam 1)) eqProdByteSize ∧
      ¬ GenericBodySafeUnconditional fnTransmuteLike
          (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by
  refine ⟨genericBodySafeUnderPme_pos_sizeEq, ?_⟩
  intro hUnc
  have hEmpty : DeclBounds.sat emptyBounds emptyAssoc
      ⟨fun i => if i = 0 then tyU16 else tyU8, fun _ => 0⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; dsimp; split <;> rfl
    · intro _ _ _ hA; cases hA
    · intro _ hi; cases hi
    · intro _ htr _ _ _; cases htr
  have h := hUnc emptyAssoc ⟨fun i => if i = 0 then tyU16 else tyU8, fun _ => 0⟩
    (.prod tyU16 tyU8) hEmpty rfl
  cases h

/-- Tightness of `hSound` in `defCheckSound_accepted_true_and_substStable_of_complete`,
    `defCheckSound_of_boundEntails`, and
    `genericBodySafeUnconditional_of_defCheckSound_of_boundEntails`: without `DefCheckSound`,
    `naiveDefPackedCheck` accepts `Packed<T0>` under `emptyBounds`, violating invariance,
    `DefCheckSound` on the source bound, and `GenericBodySafeUnconditional`. -/
theorem cex_boundEntails_without_soundness :
    BoundEntails (DeclBounds.sat emptyBounds) (DeclBounds.sat emptyBounds) ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      ¬ (∀ t A1 σ1 τ1 A2 σ2 τ2,
          naiveDefPackedCheck t = true →
          DeclBounds.sat emptyBounds A1 σ1 → instTy A1 σ1 t = some τ1 →
          DeclBounds.sat emptyBounds A2 σ2 → instTy A2 σ2 t = some τ2 →
          packedNoAlignWf τ1 = true ∧ packedNoAlignWf τ1 = packedNoAlignWf τ2) ∧
      ¬ GenericBodySafeUnconditional ⟨emptyBounds, [], true, .skip⟩
          (.packed 1 (.tparam 0)) packedNoAlignWf := by
  refine ⟨fun _ _ h => h, cex_naiveDefPackedCheck_tparam_and_proj.2.2.2.2.2.2.2, rfl, ?_,
    cex_generic_capture_unstated_bound_unsound.2.2.2.2.2.2.2.2⟩
  intro hInv
  have hEmptyU8 : DeclBounds.sat emptyBounds emptyAssoc substU8 :=
    ⟨fun _ => rfl, fun _ _ _ hA => (by cases hA),
      fun _ hi => (by cases hi), fun _ htr _ _ _ => (by cases htr)⟩
  have heq := (hInv (.packed 1 (.tparam 0))
    emptyAssoc substU8 (.packed 1 tyU8)
    emptyAssoc substAlign16 (.packed 1 align16U8)
    rfl hEmptyU8 rfl substAlign16_sat_emptyBounds rfl).2
  cases heq

/-- Tightness of `DefCheckComplete B Φ C` in the second conjunct of
    `defCheckSound_accepted_true_and_substStable_of_complete`: conservative
    `boundedDefPackedCheck ⟨[0], []⟩` is `DefCheckSound` under `DeclBounds.sat ⟨[0], []⟩`
    (accepting `Packed<T0>` and rejecting `Packed<T1>`), yet fails `DefCheckComplete` and
    `packedNoAlignWf` is not `SubstStable` under `DeclBounds.sat ⟨[0], []⟩`. -/
theorem cex_defCheckSound_without_complete_not_substStable :
    DefCheckSound (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
        (boundedDefPackedCheck ⟨[0], []⟩) ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      ¬ DefCheckComplete (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
          (boundedDefPackedCheck ⟨[0], []⟩) ∧
      ¬ SubstStable (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf := by
  have hSatU8 : DeclBounds.sat ⟨[0], []⟩ emptyAssoc substU8 :=
    ⟨fun _ => rfl, fun _ _ _ hA => (by cases hA),
      fun _ _ => rfl, fun _ htr _ _ _ => (by cases htr)⟩
  refine ⟨boundedDefPackedCheck_defCheckSound_aux ⟨[0], []⟩, rfl, ?_, ?_⟩
  · intro hComp
    have hC := hComp (.packed 1 (.tparam 1)) emptyAssoc substU8 (.packed 1 tyU8) hSatU8 rfl rfl
    cases hC
  · intro hStab
    let σSel : Subst := ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
    have heq := hStab (.packed 1 (.tparam 1))
      emptyAssoc substU8 (.packed 1 tyU8)
      emptyAssoc σSel (.packed 1 align16U8)
      hSatU8 rfl declBoundsSat_pos_selective rfl
    cases heq

/-- Tightness of `hAccept : C openTarget = true` in
    `genericBodySafeUnconditional_of_defCheckSound_of_boundEntails`: `boundedDefPackedCheck ⟨[0], []⟩`
    is sound under `DeclBounds.sat ⟨[0], []⟩` and `BoundEntails` holds reflexively, yet
    `Packed<T1>` is rejected (`= false`) and fails `GenericBodySafeUnconditional`. -/
theorem cex_genericBodySafeUnconditional_without_accept :
    BoundEntails (DeclBounds.sat ⟨[0], []⟩) (DeclBounds.sat ⟨[0], []⟩) ∧
      DefCheckSound (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
        (boundedDefPackedCheck ⟨[0], []⟩) ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 1)) = false ∧
      ¬ GenericBodySafeUnconditional ⟨⟨[0], []⟩, [], true, .skip⟩
          (.packed 1 (.tparam 1)) packedNoAlignWf := by
  refine ⟨fun _ _ h => h, boundedDefPackedCheck_defCheckSound_aux ⟨[0], []⟩, rfl, ?_⟩
  intro hUnc
  let σSel : Subst := ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
  have h := hUnc emptyAssoc σSel (.packed 1 align16U8) declBoundsSat_pos_selective rfl
  cases h

/-- Non-vacuity witness for `defCheckSound_accepted_true_and_substStable_of_complete`,
    `defCheckSound_of_boundEntails`, and
    `genericBodySafeUnconditional_of_defCheckSound_of_boundEntails`: source bound `⟨[0, 1], []⟩`
    strictly entails assumed bound `⟨[0], []⟩`, `boundedDefPackedCheck ⟨[0], []⟩` is genuinely
    `DefCheckSound` under `DeclBounds.sat ⟨[0], []⟩` while accepting `Packed<T0>` and rejecting
    `Packed<T1>`, and `(FullNoAlignBound, naiveDefPackedCheck)` simultaneously witnesses both
    `DefCheckSound` and `DefCheckComplete`. -/
theorem nonvacuity_defCheckSound_boundEntails :
    BoundEntails (DeclBounds.sat ⟨[0, 1], []⟩) (DeclBounds.sat ⟨[0], []⟩) ∧
      DefCheckSound (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
        (boundedDefPackedCheck ⟨[0], []⟩) ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 1)) = false ∧
      DeclBounds.sat ⟨[0, 1], []⟩ emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.packed 1 (.tparam 0)) = some (.packed 1 tyU8) ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true := by
  refine ⟨?_, boundedDefPackedCheck_defCheckSound_aux ⟨[0], []⟩, rfl, rfl, ?_, rfl,
    pc_fullNoAlign_naiveCheck_sound_and_complete.2.1,
    pc_fullNoAlign_naiveCheck_sound_and_complete.2.2,
    fullNoAlignBound_pos_scalars, rfl⟩
  · intro A σ hSat
    refine ⟨hSat.1, hSat.2.1, ?_, hSat.2.2.2⟩
    intro i hi
    simp at hi
    subst hi
    exact hSat.2.2.1 0 (by simp)
  · exact ⟨fun _ => rfl, fun _ _ _ hA => (by cases hA),
      fun _ _ => rfl, fun _ htr _ _ _ => (by cases htr)⟩

/-- Crate with local `packedWf`-guarded generic function `fn 0` instantiated at `tyU8` and `tyU64`. -/
def progMonoPacked : CrateProg :=
  ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩], emptyAssoc⟩

/-- Target map assigning `.packed 1 (.tparam 0)` to `fn 0`. -/
def targetPacked0 (id : Nat) : Option OpenTy :=
  if id = 0 then some (.packed 1 (.tparam 0)) else none

/-- Tightness of `hOk` in `monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard`. -/
theorem cex_monoCapture_without_collectOk :
    collectAndCheck true progMonoPacked [⟨0, [align16U8], []⟩] 2 ≠ .ok [⟨0, [align16U8], []⟩] ∧
      AllLocalMir progMonoPacked [⟨0, [align16U8], []⟩] ∧
      HasPackedPmeGuard progMonoPacked targetPacked0 [⟨0, [align16U8], []⟩] ∧
      ¬ MonoCaptureCertifiedOn progMonoPacked.assoc packedNoAlignWf targetPacked0
          [⟨0, [align16U8], []⟩] := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro k hk; simp at hk; subst hk; rfl
  · intro k hk; simp at hk; subst hk; rfl
  · intro hCert
    rcases hCert ⟨0, [align16U8], []⟩ (by simp) with ⟨t, τ, ht, hi, hΦ⟩
    simp [targetPacked0] at ht
    subst ht
    simp [substOfKey, instTy] at hi
    subst hi
    cases hΦ

/-- Tightness of `hLoc : AllLocalMir P T` in
    `monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard`. -/
theorem cex_monoCapture_without_allLocalMir :
    let Pext : CrateProg :=
      ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], false, .skip⟩], emptyAssoc⟩
    collectAndCheck true Pext [⟨0, [align16U8], []⟩] 2 = .ok [⟨0, [align16U8], []⟩] ∧
      ¬ AllLocalMir Pext [⟨0, [align16U8], []⟩] ∧
      HasPackedPmeGuard Pext targetPacked0 [⟨0, [align16U8], []⟩] ∧
      ¬ MonoCaptureCertifiedOn Pext.assoc packedNoAlignWf targetPacked0
          [⟨0, [align16U8], []⟩] := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hLoc
    have h0 := hLoc ⟨0, [align16U8], []⟩ (by simp)
    cases h0
  · intro k hk; simp at hk; subst hk; rfl
  · intro hCert
    rcases hCert ⟨0, [align16U8], []⟩ (by simp) with ⟨t, τ, ht, hi, hΦ⟩
    simp [targetPacked0] at ht
    subst ht
    simp [substOfKey, instTy] at hi
    subst hi
    cases hΦ

/-- Tightness of `hGuard : HasPackedPmeGuard P targetOf T` in
    `monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard`. -/
theorem cex_monoCapture_without_packedGuard :
    let Punguarded : CrateProg := ⟨[⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
    collectAndCheck true Punguarded [⟨0, [align16U8], []⟩] 2 = .ok [⟨0, [align16U8], []⟩] ∧
      AllLocalMir Punguarded [⟨0, [align16U8], []⟩] ∧
      ¬ HasPackedPmeGuard Punguarded targetPacked0 [⟨0, [align16U8], []⟩] ∧
      ¬ MonoCaptureCertifiedOn Punguarded.assoc packedNoAlignWf targetPacked0
          [⟨0, [align16U8], []⟩] := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro k hk; simp at hk; subst hk; rfl
  · intro hG
    have h0 := hG ⟨0, [align16U8], []⟩ (by simp)
    cases h0
  · intro hCert
    rcases hCert ⟨0, [align16U8], []⟩ (by simp) with ⟨t, τ, ht, hi, hΦ⟩
    simp [targetPacked0] at ht
    subst ht
    simp [substOfKey, instTy] at hi
    subst hi
    cases hΦ

/-- Non-vacuity witness for `checkMonoTarget_iff_monoCaptureCertifiedOn` and
    `monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard`: `packedNoAlignWf` is NOT
    substitution-stable under `emptyBounds`, yet monomorphic capture of `[⟨0, [tyU8], []⟩,
    ⟨0, [tyU64], []⟩]` succeeds and certifies every captured instance. -/
theorem nonvacuity_monoCapture_packed :
    let roots : List MonoKey := [⟨0, [tyU8], []⟩, ⟨0, [tyU64], []⟩]
    ¬ SubstStable (DeclBounds.sat emptyBounds) packedNoAlignWf ∧
      collectAndCheck true progMonoPacked roots 4 = .ok roots ∧
      AllLocalMir progMonoPacked roots ∧
      HasPackedPmeGuard progMonoPacked targetPacked0 roots ∧
      checkMonoTarget progMonoPacked.assoc packedNoAlignWf targetPacked0 roots = true := by
  refine ⟨packedNoAlignWf_not_substStable_emptyBounds, rfl, ?_, ?_, rfl⟩
  · intro k hk; simp at hk; rcases hk with rfl | rfl <;> rfl
  · intro k hk; simp at hk; rcases hk with rfl | rfl <;> rfl

end Toy.SubstStable
