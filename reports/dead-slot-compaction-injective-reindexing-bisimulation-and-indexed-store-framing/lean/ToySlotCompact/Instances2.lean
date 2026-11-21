import ToySlotCompact.Instances

/-!
# Concrete instances, continued

Entry merges, dead-slot pre/postconditions, a mask failing transfer closure for the
verification-condition result, and the positive instances (straight-line code with markers and a
debug read, a non-injective slot sharing, and a loop).
-/

namespace Toy.SlotCompact

/-! ## `pE`: two entry-live slots merged -/

/-- `halt [x0, x1]`: both slots are inputs and outputs. -/
def pE : Prog 2 := [.halt [0, 1]]
/-- Mask of `pE`: both slots live at the halt. -/
def LE : Ann 2 := fun pc _ => decide (pc = 0)
/-- Merges both slots of `pE`. -/
def πEm : Compaction pE LE 1 := fun _ => 0

theorem pE_cert : ReadsLive pE LE ∧ TransferClosed pE LE :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pE_dbg : DbgReadsLive pE LE := dbgReadsLive_of_check (by decide)
theorem pE_assign : NoAssignClobber pE LE πEm := noAssignClobber_of_check (by decide)
theorem pE_marker : NoMarkerClobber pE LE πEm := noMarkerClobber_of_check (by decide)
theorem pE_not_inj0 : ¬ InjOnLiveAt pE LE πEm 0 := by
  intro h
  have := h 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  revert this
  decide
theorem pE_exec (σ : Store 2) : exec pE 1 ⟨0, σ⟩ = some ⟨0, σ⟩ := rfl
theorem pE_exec_c (σ' : Store 1) : exec (compact pE LE πEm) 1 ⟨0, σ'⟩ = some ⟨0, σ'⟩ := rfl

/-- Postcondition of `pE`: the two outputs are equal. -/
def postE : State 2 → Prop := fun s => s.st 0 = s.st 1
theorem postE_dep : DependsOnlyOnLive pE LE postE := by
  rintro ⟨pc, σ⟩ ⟨pc', τ⟩ ⟨outs, hh⟩ hpc hag
  simp only at hpc hag
  subst hpc
  have hpc0 : pc = 0 := by
    rcases pc with _ | pc
    · rfl
    · simp [pE] at hh
  subst hpc0
  unfold postE
  simp only
  rw [hag 0 (by decide), hag 1 (by decide)]

theorem pE_vc_bwd_fails :
    (∀ σ', preTrue (pullStore πEm σ') → wp (compact pE LE πEm) (pullPost πEm postE) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preTrue σ → wp pE postE ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' _
    rw [wp_iff_of_exec (pE_exec_c σ')]
    show pullStore πEm σ' 0 = pullStore πEm σ' 1
    rw [pullStore_kept πEm _ (i := 0) (by decide), pullStore_kept πEm _ (i := 1) (by decide)]
    rfl
  · have := H (fun i => i.val) trivial
    rw [wp_iff_of_exec (pE_exec _)] at this
    revert this
    unfold postE
    decide

/-! ## `pE3`: merged live slots and a postcondition on a dead slot -/

/-- `halt [x0, x1]` over three slots; `x2` is dead. -/
def pE3 : Prog 3 := [.halt [0, 1]]
/-- Mask of `pE3`: `{x0, x1}` at the halt. -/
def LE3 : Ann 3 := fun pc i => decide (pc = 0 ∧ i.val < 2)
/-- Merges `x0` and `x1`. -/
def πE3 : Compaction pE3 LE3 1 := fun _ => 0
/-- A postcondition that reads the dead slot `x2`, guarded by `x0 ≠ x1`. -/
def postE3 : State 3 → Prop := fun s => s.st 0 ≠ s.st 1 ∧ s.st 2 = 0

theorem pE3_not_injAtHalt : ¬ InjOnLiveAt pE3 LE3 πE3 0 := by
  intro h
  have := h 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  revert this
  decide

theorem pE3_postCorr_false : PostCorr pE3 LE3 πE3 postE3 (fun _ => False) := by
  rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨outs, hh⟩ ⟨hpc, hst⟩
  simp only at hpc hst hh
  subst hpc
  have hpc0 : pc' = 0 := by
    rcases pc' with _ | pc'
    · rfl
    · simp [pE3] at hh
  subst hpc0
  have h0 := hst 0 (by decide) (by decide)
  have h1 := hst 1 (by decide) (by decide)
  unfold postE3
  simp only [iff_false, not_and]
  intro hne
  exact absurd (h0.symm.trans h1) hne

theorem pE3_not_dep : ¬ DependsOnlyOnLive pE3 LE3 postE3 := by
  intro h
  have := h ⟨0, fun i => if i = 1 then 1 else 0⟩ ⟨0, fun i => if i = 0 then 0 else 1⟩
    ⟨[0, 1], rfl⟩ rfl (by decide)
  revert this
  unfold postE3
  decide

/-! ## `pV`: a mask failing transfer closure, for verification conditions -/

/-- `x1 := 5; nop; halt [x0, x1]`. -/
def pV : Prog 2 := [.assign 1 (.const 5), .nop, .halt [0, 1]]
/-- Mask of `pV` omitting the input `x0` before the halt: `{}`, `{x1}`, `{x0, x1}`. -/
def LV : Ann 2 := fun pc i => if pc = 0 then false else if pc = 1 then decide (i = 1)
  else decide (pc = 2)
/-- Merges both slots of `pV`. -/
def πVm : Compaction pV LV 1 := fun _ => 0

theorem pV_reads : ReadsLive pV LV := (checkReads_eq_true_iff _ _).mp (by decide)
theorem pV_not_transfer : ¬ TransferClosed pV LV := by
  intro h
  have := h 1 _ rfl 2 (by decide) 0 rfl rfl
  revert this
  decide
theorem pV_assign : NoAssignClobber pV LV πVm := noAssignClobber_of_check (by decide)
theorem pV_marker : NoMarkerClobber pV LV πVm := noMarkerClobber_of_check (by decide)
theorem pV_inj0 : InjOnLiveAt pV LV πVm 0 := injOnLiveAt_of_check (by decide)
theorem pV_exec (σ : Store 2) : exec pV 3 ⟨0, σ⟩ = some ⟨2, upd σ 1 5⟩ := rfl
theorem pV_exec_c (σ' : Store 1) :
    exec (compact pV LV πVm) 3 ⟨0, σ'⟩ = some ⟨2, upd σ' 0 5⟩ := rfl

/-- Postcondition used with `pV`: `x0 = 5` at the halt. -/
def postV : State 2 → Prop := postAt 2 0 5
theorem postV_dep : DependsOnlyOnLive pV LV postV := dependsOnlyOnLive_postAt 5 (by decide)

theorem pV_vc_bwd_fails :
    (∀ σ', preTrue (pullStore πVm σ') → wp (compact pV LV πVm) (pullPost πVm postV) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preTrue σ → wp pV postV ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' _
    rw [wp_iff_of_exec (pV_exec_c σ')]
    intro _
    show pullStore πVm (upd σ' 0 5) 0 = 5
    rw [pullStore_kept πVm _ (by decide)]
    exact upd_same _ _ _
  · have := H (fun _ => 0) trivial
    rw [wp_iff_of_exec (pV_exec _)] at this
    revert this
    unfold postV postAt
    decide

/-! ## `pH`: pre- and postconditions mentioning a dead slot -/

/-- `halt []` over one slot: nothing is live. -/
def pH : Prog 1 := [.halt []]
/-- Mask of `pH`: nothing live. -/
def LH : Ann 1 := fun _ _ => false
/-- The (empty) compaction of `pH`. -/
def πH : Compaction pH LH 1 := fun _ => 0

theorem pH_cert : ReadsLive pH LH ∧ TransferClosed pH LH :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pH_assign : NoAssignClobber pH LH πH := noAssignClobber_of_check (by decide)
theorem pH_marker : NoMarkerClobber pH LH πH := noMarkerClobber_of_check (by decide)
theorem pH_inj0 : InjOnLiveAt pH LH πH 0 := injOnLiveAt_of_check (by decide)
theorem pH_exec (σ : Store 1) : exec pH 1 ⟨0, σ⟩ = some ⟨0, σ⟩ := rfl
theorem pH_exec_c (σ' : Store 1) : exec (compact pH LH πH) 1 ⟨0, σ'⟩ = some ⟨0, σ'⟩ := rfl

/-- A precondition reading the dead slot. -/
def preH : Store 1 → Prop := fun σ => σ 0 = 1
/-- The unsatisfiable postcondition. -/
def postFalse {N : Nat} : State N → Prop := fun _ => False
/-- The trivially true postcondition. -/
def postTrue {N : Nat} : State N → Prop := fun _ => True
/-- A postcondition reading the dead slot. -/
def postH : State 1 → Prop := fun s => s.st 0 = 0

theorem postFalse_dep {N : Nat} {p : Prog N} {L : Ann N} : DependsOnlyOnLive p L postFalse :=
  fun _ _ _ _ _ => Iff.rfl
theorem preH_not_dep : ¬ DependsOnlyOnEntryLive pH LH preH := by
  intro h
  have := h (fun _ => 1) (fun _ => 0) (by decide)
  revert this
  unfold preH
  decide
theorem postH_not_dep : ¬ DependsOnlyOnLive pH LH postH := by
  intro h
  have := h ⟨0, fun _ => 0⟩ ⟨0, fun _ => 1⟩ ⟨[], rfl⟩ rfl (by decide)
  revert this
  unfold postH
  decide

theorem pH_vc_pre_bwd_fails :
    (∀ σ', preH (pullStore πH σ') → wp (compact pH LH πH) (pullPost πH postFalse) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preH σ → wp pH postFalse ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' hpre
    revert hpre
    unfold preH pullStore
    simp [Compaction.get?_of_not_kept πH (i := 0) (by decide)]
  · have := H (fun _ => 1) rfl
    rw [wp_iff_of_exec (pH_exec _)] at this
    exact this

theorem pH_vc_post_bwd_fails :
    (∀ σ', preTrue (pullStore πH σ') → wp (compact pH LH πH) (pullPost πH postH) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preTrue σ → wp pH postH ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' _
    rw [wp_iff_of_exec (pH_exec_c σ')]
    show pullStore πH σ' 0 = 0
    unfold pullStore
    simp [Compaction.get?_of_not_kept πH (i := 0) (by decide)]
  · have := H (fun _ => 1) trivial
    rw [wp_iff_of_exec (pH_exec _)] at this
    revert this
    unfold postH
    decide

theorem pH_wp_ne :
    ¬ (wp pH postTrue ⟨0, fun _ => 0⟩ ↔ wp (compact pH LH πH) postFalse ⟨0, fun _ => 0⟩) := by
  rw [wp_iff_of_exec (pH_exec _), wp_iff_of_exec (pH_exec_c _)]
  simp [postTrue, postFalse]

theorem pH_not_postCorr : ¬ PostCorr pH LH πH postTrue postFalse := by
  intro h
  exact (h ⟨0, fun _ => 0⟩ ⟨0, fun _ => 0⟩ ⟨[], rfl⟩ ⟨rfl, by decide⟩).mp trivial

theorem pH_rel : CompactRel pH LH πH ⟨0, fun _ => 0⟩ ⟨0, fun _ => 0⟩ := ⟨rfl, by decide⟩

/-! ## `pU`: a mask missing a slot read by the halt -/

/-- `halt [x0]`. -/
def pU : Prog 1 := [.halt [0]]
/-- The empty mask. -/
def LU : Ann 1 := fun _ _ => false

theorem pU_transfer : TransferClosed pU LU := (checkTransfer_eq_true_iff _ _).mp (by decide)
theorem pU_not_reads : ¬ ReadsLive pU LU := by
  intro h
  have := h 0 _ rfl 0 (by decide)
  revert this
  decide
theorem pU_pathLive : PathLive pU 0 0 := PathLive.use (ins := .halt [0]) rfl (by decide)

/-! ## Positive instances -/

/-- Straight-line code over three slots with storage markers, a debug read of a live slot, and a
dead store to `x2`:
`x2 := 9; StorageLive(x1); x1 := x0 + 1; dbg x1; StorageDead(x0); halt [x1]`. -/
def pS : Prog 3 :=
  [.assign 2 (.const 9), .storageLive 1, .assign 1 (.add (.slot 0) (.const 1)), .dbg (.slot 1),
    .storageDead 0, .halt [1]]
/-- Path liveness of `pS`: `{x0}` up to the read, then `{x1}`. -/
def LS : Ann 3 := fun pc i => if pc ≤ 2 then decide (i = 0) else decide (pc ≤ 5 ∧ i = 1)
/-- Injective compaction of `pS` onto two slots (`x0 ↦ 0`, `x1 ↦ 1`; `x2` is dropped). -/
def πS : Compaction pS LS 2 := fun x => ⟨x.1.val % 2, Nat.mod_lt _ (by decide)⟩

theorem pS_cert : ReadsLive pS LS ∧ TransferClosed pS LS :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pS_dbg : DbgReadsLive pS LS := dbgReadsLive_of_check (by decide)
theorem pS_inj : Function.Injective πS := injective_of_check (by decide)
theorem pS_not_kept2 : Kept pS LS 2 = false := by decide
/-- The compacted `pS`: the dead store became `nop`, every other slot is renamed. -/
theorem pS_compact :
    compact pS LS πS = [.nop, .storageLive 1, .assign 1 (.add (.slot 0) (.const 1)),
      .dbg (.slot 1), .storageDead 0, .halt [1]] := by decide

/-- `pC`: like `pS` without markers; `x0` and `x1` are never simultaneously live. -/
def pC : Prog 3 := [.assign 2 (.const 9), .assign 1 (.add (.slot 0) (.const 1)), .dbg (.slot 1),
  .halt [1]]
/-- Path liveness of `pC`. -/
def LC : Ann 3 := fun pc i => if pc ≤ 1 then decide (i = 0) else decide (pc ≤ 3 ∧ i = 1)
/-- Non-injective slot sharing: `x0` and `x1` share one slot. -/
def πCm : Compaction pC LC 1 := fun _ => 0

theorem pC_cert : ReadsLive pC LC ∧ TransferClosed pC LC :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pC_dbg : DbgReadsLive pC LC := dbgReadsLive_of_check (by decide)
theorem pC_assign : NoAssignClobber pC LC πCm := noAssignClobber_of_check (by decide)
theorem pC_marker : NoMarkerClobber pC LC πCm := noMarkerClobber_of_check (by decide)
theorem pC_inj0 : InjOnLiveAt pC LC πCm 0 := injOnLiveAt_of_check (by decide)
theorem pC_not_inj : ¬ Function.Injective πCm := by
  intro h
  have := h (a₁ := ⟨0, by decide⟩) (a₂ := ⟨1, by decide⟩) rfl
  simp at this
/-- The compacted `pC` uses a single slot. -/
theorem pC_compact :
    compact pC LC πCm = [.nop, .assign 0 (.add (.slot 0) (.const 1)), .dbg (.slot 0), .halt [0]] := by
  decide

/-- `pB`: a loop. `0: if x0 ≠ 0 goto 1 else goto 4; 1: x1 := x1 + 2; 2: x0 := 0; 3: goto 0;
4: halt [x1]`; slot `x2` is unused. -/
def pB : Prog 3 :=
  [.branch (.slot 0) 1 4, .assign 1 (.add (.slot 1) (.const 2)), .assign 0 (.const 0),
    .branch (.const 1) 0 0, .halt [1]]
/-- Path liveness of `pB`: `{x0, x1}` at points 0 and 3, `{x1}` elsewhere. -/
def LB : Ann 3 := fun pc i =>
  if pc = 0 ∨ pc = 3 then decide (i.val < 2) else decide (pc ≤ 4 ∧ i = 1)
/-- Injective compaction of `pB` onto two slots. -/
def πB : Compaction pB LB 2 := fun x => ⟨x.1.val % 2, Nat.mod_lt _ (by decide)⟩

theorem pB_cert : ReadsLive pB LB ∧ TransferClosed pB LB :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pB_dbg : DbgReadsLive pB LB := dbgReadsLive_of_check (by decide)
theorem pB_inj : Function.Injective πB := injective_of_check (by decide)
theorem pB_injAtHalts : ∀ pc, IsHalt pB pc → InjOnLiveAt pB LB πB pc :=
  injAtHalts_of_check (by decide)
/-- Running `pB` from `x0 = 1, x1 = 10` goes once around the loop and halts with `x1 = 12`. -/
theorem pB_exec :
    exec pB 6 ⟨0, fun i => if i = 0 then 1 else if i = 1 then 10 else 0⟩ =
      some ⟨4, upd (upd (fun i => if i = 0 then 1 else if i = 1 then 10 else 0) 1 12) 0 0⟩ := rfl

/-- Postcondition used with `pB`: `x1 = 12` at the halt. -/
def postB : State 3 → Prop := postAt 4 1 12
theorem postB_dep : DependsOnlyOnLive pB LB postB := dependsOnlyOnLive_postAt 12 (by decide)

/-! ## Further verification-condition instances -/

/-- Postcondition for the backward failure on `pA`: `x0 = 5` at the halt. -/
def postA5 : State 2 → Prop := postAt 1 0 5
theorem postA5_dep : DependsOnlyOnLive pA LA postA5 := dependsOnlyOnLive_postAt 5 (by decide)

theorem pA_vc_bwd_fails :
    (∀ σ', preTrue (pullStore πAm σ') → wp (compact pA LA πAm) (pullPost πAm postA5) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preTrue σ → wp pA postA5 ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' _
    rw [wp_iff_of_exec (pA_exec_c σ')]
    intro _
    show pullStore πAm (upd σ' 0 5) 0 = 5
    rw [pullStore_kept πAm _ (i := 0) (by decide)]
    exact upd_same _ _ _
  · have := H (fun _ => 0) trivial
    rw [wp_iff_of_exec (pA_exec _)] at this
    revert this
    unfold postA5 postAt
    decide

/-- Postcondition for the backward failure on `pM`: `x1 = 0` at the halt. -/
def postM0 : State 2 → Prop := postAt 2 1 0
theorem postM0_dep : DependsOnlyOnLive pM LM postM0 := dependsOnlyOnLive_postAt 0 (by decide)

theorem pM_vc_bwd_fails :
    (∀ σ', preTrue (pullStore πMm σ') → wp (compact pM LM πMm) (pullPost πMm postM0) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preTrue σ → wp pM postM0 ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' _
    rw [wp_iff_of_exec (pM_exec_c σ')]
    intro _
    show pullStore πMm (upd (upd σ' 0 0) 0 0) 1 = 0
    rw [pullStore_kept πMm _ (i := 1) (by decide)]
    exact upd_same _ _ _
  · have := H (fun _ => 1) trivial
    rw [wp_iff_of_exec (pM_exec _)] at this
    revert this
    unfold postM0 postAt
    decide

/-- Postcondition for the forward failure on `pV`: `x0 = 3` at the halt. -/
def postV3 : State 2 → Prop := postAt 2 0 3
theorem postV3_dep : DependsOnlyOnLive pV LV postV3 := dependsOnlyOnLive_postAt 3 (by decide)

theorem pV_vc_fwd_fails :
    (∀ σ, preA σ → wp pV postV3 ⟨0, σ⟩) ∧
      ¬ (∀ σ', preA (pullStore πVm σ') → wp (compact pV LV πVm) (pullPost πVm postV3) ⟨0, σ'⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ hσ
    rw [wp_iff_of_exec (pV_exec σ)]
    intro _
    show upd σ 1 5 0 = 3
    rw [upd_other _ _ (by decide)]
    exact hσ
  · have := H (fun _ => 3) (by unfold preA; decide)
    rw [wp_iff_of_exec (pV_exec_c _)] at this
    revert this
    unfold postV3 postAt pullPost
    decide

/-- `pX`: `x1 := 5; x1 := x0; halt [x1]`, with a mask that omits `x0` at its read. -/
def pX : Prog 2 := [.assign 1 (.const 5), .assign 1 (.slot 0), .halt [1]]
/-- Mask of `pX`: `{x0}`, `{}`, `{x1}`. -/
def LX : Ann 2 := fun pc i => if pc = 0 then decide (i = 0) else decide (pc = 2 ∧ i = 1)
/-- Merges both slots of `pX`. -/
def πXm : Compaction pX LX 1 := fun _ => 0

theorem pX_transfer : TransferClosed pX LX := (checkTransfer_eq_true_iff _ _).mp (by decide)
theorem pX_not_reads : ¬ ReadsLive pX LX := by
  intro h
  have := h 1 _ rfl 0 rfl
  revert this
  decide
theorem pX_assign : NoAssignClobber pX LX πXm := noAssignClobber_of_check (by decide)
theorem pX_marker : NoMarkerClobber pX LX πXm := noMarkerClobber_of_check (by decide)
theorem pX_exec (σ : Store 2) : exec pX 3 ⟨0, σ⟩ = some ⟨2, upd (upd σ 1 5) 1 (σ 0)⟩ := rfl
theorem pX_exec_c (σ' : Store 1) :
    exec (compact pX LX πXm) 3 ⟨0, σ'⟩ = some ⟨2, upd (upd σ' 0 5) 0 5⟩ := rfl

/-- Postcondition used with `pX`: `x1 = 3` at the halt. -/
def postX : State 2 → Prop := postAt 2 1 3
theorem postX_dep : DependsOnlyOnLive pX LX postX := dependsOnlyOnLive_postAt 3 (by decide)

theorem pX_vc_fwd_fails :
    (∀ σ, preA σ → wp pX postX ⟨0, σ⟩) ∧
      ¬ (∀ σ', preA (pullStore πXm σ') → wp (compact pX LX πXm) (pullPost πXm postX) ⟨0, σ'⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ hσ
    rw [wp_iff_of_exec (pX_exec σ)]
    intro _
    show upd (upd σ 1 5) 1 (σ 0) 1 = 3
    rw [upd_same]
    exact hσ
  · have := H (fun _ => 3) (by unfold preA; decide)
    rw [wp_iff_of_exec (pX_exec_c _)] at this
    revert this
    unfold postX postAt pullPost
    decide

/-- `pK`: a dead store `x0 := 1; halt []`. -/
def pK : Prog 1 := [.assign 0 (.const 1), .halt []]
/-- Mask of `pK`: nothing live. -/
def LK : Ann 1 := fun _ _ => false
/-- The (empty) compaction of `pK`; the dead store is dropped. -/
def πK : Compaction pK LK 1 := fun _ => 0
/-- A postcondition reading the dead slot. -/
def postK : State 1 → Prop := fun s => s.st 0 = 1

theorem pK_cert : ReadsLive pK LK ∧ TransferClosed pK LK :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pK_assign : NoAssignClobber pK LK πK := noAssignClobber_of_check (by decide)
theorem pK_marker : NoMarkerClobber pK LK πK := noMarkerClobber_of_check (by decide)
theorem pK_exec (σ : Store 1) : exec pK 2 ⟨0, σ⟩ = some ⟨1, upd σ 0 1⟩ := rfl
theorem pK_exec_c (σ' : Store 1) : exec (compact pK LK πK) 2 ⟨0, σ'⟩ = some ⟨1, σ'⟩ := rfl
theorem postK_not_dep : ¬ DependsOnlyOnLive pK LK postK := by
  intro h
  have := h ⟨1, fun _ => 1⟩ ⟨1, fun _ => 0⟩ ⟨[], rfl⟩ rfl (by decide)
  revert this
  unfold postK
  decide

theorem pK_vc_fwd_fails :
    (∀ σ, preTrue σ → wp pK postK ⟨0, σ⟩) ∧
      ¬ (∀ σ', preTrue (pullStore πK σ') → wp (compact pK LK πK) (pullPost πK postK) ⟨0, σ'⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ _
    rw [wp_iff_of_exec (pK_exec σ)]
    show upd σ 0 1 0 = 1
    exact upd_same _ _ _
  · have := H (fun _ => 0) trivial
    rw [wp_iff_of_exec (pK_exec_c _)] at this
    revert this
    unfold postK pullPost pullStore
    simp [Compaction.get?_of_not_kept πK (i := 0) (by decide)]

/-! ## `pO`: an unsound empty mask that would erase an output -/

/-- `x0 := 42; halt [x0]`. -/
def pO : Prog 1 := [.assign 0 (.const 42), .halt [0]]
/-- The empty mask; it is not a certificate, because the `halt` reads `x0`. -/
def LO : Ann 1 := fun _ _ => false
/-- The compaction of `pO` onto zero slots (nothing is kept). -/
def πO : Compaction pO LO 0 := fun x => nomatch x.2

theorem pO_compact : compact pO LO πO = [.nop, .halt []] := by decide
theorem pO_not_reads : ¬ ReadsLive pO LO := by
  intro h
  have := h 1 _ rfl 0 (by decide)
  revert this
  decide
/-- The compacted `pO` emits no output at the halt, while `pO` emits the value of `x0`; since `halt`
outputs are observed, the bisimulation fails. -/
theorem pO_not_bisim : ¬ LockstepBisim pO (compact pO LO πO) (CompactRel pO LO πO) := by
  intro h
  obtain ⟨hout, -⟩ := h ⟨1, fun _ => 7⟩ ⟨1, Fin.elim0⟩ ⟨rfl, fun _ hk _ => nomatch hk⟩
  revert hout
  decide

/-! ## `pKD`: a debug read of a kept slot at a point where it is dead -/

/-- `dbg x0; x0 := 5; halt [x0]`. -/
def pKD : Prog 1 := [.dbg (.slot 0), .assign 0 (.const 5), .halt [0]]
/-- Path liveness of `pKD`: `x0` is live only at the halt. -/
def LKD : Ann 1 := fun pc _ => decide (pc = 2)
/-- The identity compaction of `pKD`. -/
def πKD : Compaction pKD LKD 1 := fun x => x.val

theorem pKD_cert : ReadsLive pKD LKD ∧ TransferClosed pKD LKD :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pKD_inj : Function.Injective πKD := injective_of_check (by decide)
theorem pKD_dbgKept : DbgReadsKept pKD LKD := dbgReadsKept_of_check (by decide)
theorem pKD_not_dbg : ¬ DbgReadsLive pKD LKD := by
  intro h
  have := h 0 (.slot 0) rfl 0 rfl
  revert this
  decide

/-! ## `pNK`: a write-free program with two merged kept slots -/

/-- `nop; halt [x0, x1]`. -/
def pNK : Prog 2 := [.nop, .halt [0, 1]]
/-- Mask of `pNK`: both slots live at the halt only. -/
def LNK : Ann 2 := fun pc _ => decide (pc = 1)
/-- Merges both slots of `pNK`. -/
def πNK : Compaction pNK LNK 1 := fun _ => 0

theorem pNK_not_inj : ¬ Function.Injective πNK := by
  intro h
  have := h (a₁ := ⟨0, by decide⟩) (a₂ := ⟨1, by decide⟩) rfl
  simp at this
theorem pNK_readsKept : ReadsKept pNK LNK :=
  readsKept_of_readsLive ((checkReads_eq_true_iff _ _).mp (by decide))
theorem pNK_dbgKept : DbgReadsKept pNK LNK := dbgReadsKept_of_check (by decide)

/-! ## `pF`: a read whose only effect is a dead assignment -/

/-- `x1 := x0; halt []`: the value read from `x0` is assigned to `x1`, which is never used. -/
def pF : Prog 2 := [.assign 1 (.slot 0), .halt []]
/-- The empty mask. -/
def LF : Ann 2 := fun _ _ => false
/-- The (empty) compaction of `pF`. -/
def πF : Compaction pF LF 1 := fun _ => 0

theorem pF_not_kept (i : Fin 2) : Kept pF LF i = false := by revert i; decide
theorem pF_not_reads : ¬ ReadsLive pF LF := by
  intro h
  have := h 0 _ rfl 0 rfl
  revert this
  decide

/-! ## `pI`: a use behind a branch that is never taken -/

/-- `0: if 0 goto 1 else goto 2; 1: halt [x0]; 2: halt []`. The branch condition is the constant
`0`, so control always goes to `2`. -/
def pI : Prog 1 := [.branch (.const 0) 1 2, .halt [0], .halt []]

end Toy.SlotCompact
