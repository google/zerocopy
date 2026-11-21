import ToySlotCompact.NonVacuity

/-!
# Boundary theorems

Concrete instances that delimit the main results. Each is cited by a non-claim: it shows a
tempting stronger reading to be false, or shows that a hypothesis is not necessary outside the
witness class of its counterexample.
-/

namespace Toy.SlotCompact

/-! ## Observation of outputs -/

/-- A compaction that erases a `halt` output is not a lockstep bisimulation, because `halt`
emits its output values (`pO`, with an empty mask that is not a certificate). -/
theorem bisim_observes_halt_outputs :
    ¬ ReadsLive pO LO ∧ compact pO LO πO = [.nop, .halt []] ∧
      ¬ LockstepBisim pO (compact pO LO πO) (CompactRel pO LO πO) :=
  ⟨pO_not_reads, pO_compact, pO_not_bisim⟩

/-! ## The kept-slot relation -/

/-- Under `KeptRel` a debug read of a kept slot at a point where it is dead is harmless, while
under `CompactRel` the same compaction is not a lockstep bisimulation, although the mask is a
certificate (`pKD`). -/
theorem keptBisim_kept_dead_dbg :
    Kept pKD LKD 0 = true ∧ LKD 0 0 = false ∧
      ReadsLive pKD LKD ∧ TransferClosed pKD LKD ∧ ¬ DbgReadsLive pKD LKD ∧
      ReadsKept pKD LKD ∧ DbgReadsKept pKD LKD ∧ Function.Injective πKD ∧
      LockstepBisim pKD (compact pKD LKD πKD) (KeptRel pKD LKD πKD) ∧
      ¬ LockstepBisim pKD (compact pKD LKD πKD) (CompactRel pKD LKD πKD) := by
  refine ⟨by decide, rfl, pKD_cert.1, pKD_cert.2, pKD_not_dbg, readsKept_of_readsLive pKD_cert.1,
    pKD_dbgKept, pKD_inj,
    compact_keptRel_lockstepBisim_of_injective pKD LKD πKD pKD_inj
      (readsKept_of_readsLive pKD_cert.1) pKD_dbgKept, ?_⟩
  intro h
  obtain ⟨hev, -⟩ := h ⟨0, fun _ => 7⟩ ⟨0, fun _ => 0⟩ ⟨rfl, by decide⟩
  revert hev
  decide

/-- Injectivity is not necessary for the `KeptRel` bisimulation on write-free programs: merging two
kept slots of `nop; halt [x0, x1]` still gives a lockstep bisimulation (`KeptRel` then relates only
original stores in which the merged slots are equal). -/
theorem keptBisim_noninjective_writeFree :
    ¬ Function.Injective πNK ∧ ReadsKept pNK LNK ∧ DbgReadsKept pNK LNK ∧
      LockstepBisim pNK (compact pNK LNK πNK) (KeptRel pNK LNK πNK) := by
  refine ⟨pNK_not_inj, pNK_readsKept, pNK_dbgKept, ?_⟩
  rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨hpc, hst⟩
  simp only at hpc hst
  subst pc'
  have h0 : σ' 0 = σ 0 := hst 0 (by decide)
  have h1 : σ' 0 = σ 1 := hst 1 (by decide)
  rcases pc with _ | _ | pc
  · exact ⟨rfl, rfl, hst⟩
  · refine ⟨?_, rfl, hst⟩
    show [σ 0, σ 1] = [σ' 0, σ' 0]
    rw [← h0, ← h1]
  · simp [step, pNK, compact, ResRel]

/-! ## Path liveness versus other notions of liveness -/

/-- Path liveness counts the operand of a dead assignment as a use (`x0` in `x1 := x0; halt []`),
yet dropping every slot of that program, with the empty mask (which violates `ReadsLive` and
`ReadsKept`), still gives a lockstep bisimulation for both relations. So neither `ReadsLive` nor
`ReadsKept` is necessary for the conclusion of the bisimulation theorems in general. -/
theorem pathLive_faint_operand :
    PathLive pF 0 0 ∧ ¬ ReadsLive pF LF ∧ ¬ ReadsKept pF LF ∧
      LockstepBisim pF (compact pF LF πF) (CompactRel pF LF πF) ∧
      LockstepBisim pF (compact pF LF πF) (KeptRel pF LF πF) := by
  refine ⟨PathLive.use (ins := .assign 1 (.slot 0)) rfl (by decide), pF_not_reads, ?_, ?_, ?_⟩
  · intro h
    have := h 0 _ rfl 0 rfl
    revert this
    decide
  · rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨hpc, _⟩
    simp only at hpc
    subst pc'
    rcases pc with _ | _ | pc
    · exact ⟨rfl, rfl, fun i h _ => by rw [pF_not_kept i] at h; contradiction⟩
    · exact ⟨rfl, rfl, fun i h _ => by rw [pF_not_kept i] at h; contradiction⟩
    · simp [step, pF, compact, ResRel]
  · rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨hpc, _⟩
    simp only at hpc
    subst pc'
    rcases pc with _ | _ | pc
    · exact ⟨rfl, rfl, fun i h => by rw [pF_not_kept i] at h; contradiction⟩
    · exact ⟨rfl, rfl, fun i h => by rw [pF_not_kept i] at h; contradiction⟩
    · simp [step, pF, compact, ResRel]

/-- Path liveness follows branch successors that can never be taken: `x0` is path-live at entry of
`pI`, although every run takes the branch to the `halt []` that outputs nothing. -/
theorem pathLive_infeasible_branch :
    PathLive pI 0 0 ∧ ∀ σ : Store 1, step pI ⟨0, σ⟩ = .running ⟨2, σ⟩ none :=
  ⟨PathLive.pass (ins := .branch (.const 0) 1 2) (s := 1) rfl (by decide) rfl
      (PathLive.use (ins := .halt [0]) rfl (by decide)),
    fun _ => rfl⟩

/-! ## The checker does not certify the debug condition -/

/-- The checker accepts the path-liveness mask of `pD` and `πD` is injective, yet the compaction is
not a lockstep bisimulation, because a debug read observes a dead slot: `checkLive` does not
check `DbgReadsLive`. -/
theorem checkLive_pathLiveMask_not_sufficient_with_dbg :
    checkLive pD LD = true ∧ (∀ pc i, LD pc i = pathLiveMask pD pc i) ∧
      Function.Injective πD ∧ ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := by
  refine ⟨by decide, fun pc i => ?_, pD_inj, pD_not_bisim⟩
  have hnu : ¬ PathLive pD pc i :=
    not_pathLive_of_unused fun pc' ins hins => by
      have := (all_points_iff pD (fun _ ins => !ins.uses i)).mp (by revert i; decide) pc' ins hins
      simpa using this
  cases h : pathLiveMask pD pc i
  · rfl
  · exact absurd (pathLiveMask_eq_true.mp h) hnu

/-! ## Interference conditions versus disjoint live ranges -/

/-- `0: x1 := 5; 1: dbg x1; 2: x0 := 42; 3: x1 := 99; 4: halt [x0]`. -/
def pDisj : Prog 2 :=
  [.assign 1 (.const 5), .dbg (.slot 1), .assign 0 (.const 42), .assign 1 (.const 99), .halt [0]]
/-- Mask of `pDisj`: `x1` live only at `1`, `x0` live only at `3` and `4`. -/
def LDisj : Ann 2 := fun pc i =>
  if pc = 1 then decide (i = 1) else decide ((pc = 3 ∨ pc = 4) ∧ i = 0)
/-- Merges both slots of `pDisj`. -/
def πDisj : Compaction pDisj LDisj 1 := fun _ => 0

/-- Pointwise disjoint live ranges (`π` injective on the live slots at every point) do not imply
`NoAssignClobber`: `compact` keeps a write to a kept slot even where that slot is dead (`3: x1 :=
99`), and that write clobbers the live `x0` sharing its target. -/
theorem disjoint_live_ranges_not_noAssignClobber :
    ReadsLive pDisj LDisj ∧ TransferClosed pDisj LDisj ∧ DbgReadsLive pDisj LDisj ∧
      (∀ pc, InjOnLiveAt pDisj LDisj πDisj pc) ∧
      ¬ NoAssignClobber pDisj LDisj πDisj ∧
      ¬ LockstepBisim pDisj (compact pDisj LDisj πDisj) (CompactRel pDisj LDisj πDisj) := by
  have hcert : ReadsLive pDisj LDisj ∧ TransferClosed pDisj LDisj :=
    (checkLive_eq_true_iff _ _).mp (by decide)
  refine ⟨hcert.1, hcert.2, dbgReadsLive_of_check (by decide), ?_, ?_, ?_⟩
  · intro pc
    match pc with
    | 0 | 1 | 2 | 3 | 4 => exact injOnLiveAt_of_check (by decide)
    | n + 5 =>
      intro i j _ _ hli _ _
      simp [LDisj] at hli
  · intro h
    exact h 3 1 (.const 99) rfl (by decide) 0 (by decide) (by decide) (by decide) rfl
  · have hex : exec pDisj 5 ⟨0, fun _ => 0⟩ =
        some ⟨4, upd (upd (upd (fun _ => 0) 1 5) 0 42) 1 99⟩ := rfl
    have hexc : exec (compact pDisj LDisj πDisj) 5 ⟨0, fun _ => 0⟩ =
        some ⟨4, upd (upd (upd (fun _ => 0) 0 5) 0 42) 0 99⟩ := rfl
    have hdep : DependsOnlyOnLive pDisj LDisj (postAt 4 0 42) :=
      dependsOnlyOnLive_postAt 42 (by decide)
    apply not_lockstepBisim_of_wp_ne (postCorr_pullPost πDisj hdep) (s := ⟨0, fun _ => 0⟩)
      (s' := ⟨0, fun _ => 0⟩) ⟨rfl, by decide⟩
    rw [wp_iff_of_exec hex, wp_iff_of_exec hexc]
    unfold postAt pullPost
    decide

/-! ## Vacuous transported preconditions -/

/-- The forward verification-condition transfer can be vacuous: on `pH` all hypotheses of
`vc_forward_of_noClobber` hold and `preH` is satisfiable, but `preH` reads a dropped slot, which
the pulled-back store reads as `0`, so the transported precondition is unsatisfiable. -/
theorem vc_forward_vacuous_dropped :
    ReadsLive pH LH ∧ TransferClosed pH LH ∧ NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧ DependsOnlyOnLive pH LH postTrue ∧
      (∃ σ, preH σ) ∧ (∀ σ, preH σ → wp pH postTrue ⟨0, σ⟩) ∧
      (∀ σ', ¬ preH (pullStore πH σ')) := by
  refine ⟨pH_cert.1, pH_cert.2, pH_assign, pH_marker, fun _ _ _ _ _ => Iff.rfl,
    ⟨fun _ => 1, rfl⟩, fun σ _ => ⟨1, ⟨0, σ⟩, rfl, trivial⟩, fun σ' => ?_⟩
  unfold preH pullStore
  simp [Compaction.get?_of_not_kept πH (i := 0) (by decide)]

/-- "The two inputs differ." -/
def preNe : Store 2 → Prop := fun σ => σ 0 ≠ σ 1

/-- The forward verification-condition transfer can be vacuous: on `pE` all hypotheses of
`vc_forward_of_noClobber` hold and `preNe` is satisfiable, but `πEm` merges the two entry-live
slots, so every pulled-back store has equal inputs and the transported precondition is
unsatisfiable. -/
theorem vc_forward_vacuous_merged :
    ReadsLive pE LE ∧ TransferClosed pE LE ∧ NoAssignClobber pE LE πEm ∧
      NoMarkerClobber pE LE πEm ∧ DependsOnlyOnLive pE LE postTrue ∧
      (∃ σ, preNe σ) ∧ (∀ σ, preNe σ → wp pE postTrue ⟨0, σ⟩) ∧
      (∀ σ', ¬ preNe (pullStore πEm σ')) := by
  refine ⟨pE_cert.1, pE_cert.2, pE_assign, pE_marker, fun _ _ _ _ _ => Iff.rfl,
    ⟨fun i => i.val, by unfold preNe; decide⟩, fun σ _ => ⟨1, ⟨0, σ⟩, rfl, trivial⟩,
    fun σ' h => ?_⟩
  unfold preNe at h
  rw [pullStore_kept πEm _ (i := 0) (by decide), pullStore_kept πEm _ (i := 1) (by decide)] at h
  exact h rfl

/-- Injectivity on the entry-live slots is not necessary for the backward verification-condition
transfer in general: with the postcondition `True` the conclusion holds on `pE`, where `πEm`
merges both entry-live slots. -/
theorem vc_backward_without_inj0_postTrue :
    ¬ InjOnLiveAt pE LE πEm 0 ∧
      ((∀ σ', preTrue (pullStore πEm σ') → wp (compact pE LE πEm) (pullPost πEm postTrue) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pE postTrue ⟨0, σ⟩)) :=
  ⟨pE_not_inj0, fun _ σ _ => ⟨1, ⟨0, σ⟩, rfl, trivial⟩⟩

/-! ## Stores -/

/-- A complete association list may repeat keys, so its length can exceed the number of slots. -/
theorem complete_with_repeated_keys :
    Complete (List.replicate 3 ((0 : Fin 1), (0 : Nat))) ∧
      (List.replicate 3 ((0 : Fin 1), (0 : Nat))).length = 3 :=
  ⟨fun k => by revert k; decide, rfl⟩

/-! ## Concrete runs of the counterexample instances -/

/-- On `pD` the compaction is a silent bisimulation (debug events ignored) but not a lockstep
bisimulation: only the debug event differs. -/
theorem pD_silent_not_lockstep :
    SilentBisim pD (compact pD LD πD) (CompactRel pD LD πD) ∧
      ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) :=
  ⟨compact_silentBisim_of_noClobber pD LD πD pD_cert.1 pD_cert.2 pD_assign pD_marker,
    pD_not_bisim⟩

/-- The debug event of `pD` at entry is the value of `x0`; the compacted program reads the dropped
slot as the constant `0`. -/
theorem pD_events (σ σ' : Store 1) :
    (step pD ⟨0, σ⟩).ev = some (σ 0) ∧ (step (compact pD LD πD) ⟨0, σ'⟩).ev = some 0 :=
  ⟨rfl, rfl⟩

/-- One `nop` step of `pT` and of its compaction from entry states that differ on `x0` (which the
mask leaves unconstrained at entry) leads to states that are not `CompactRel`-related, because the
mask declares `x0` live at the next point. -/
theorem pT_first_step :
    CompactRel pT LT πT ⟨0, fun _ => 7⟩ ⟨0, fun _ => 0⟩ ∧
      step pT ⟨0, fun _ => 7⟩ = .running ⟨1, fun _ => 7⟩ none ∧
      step (compact pT LT πT) ⟨0, fun _ => 0⟩ = .running ⟨1, fun _ => 0⟩ none ∧
      ¬ CompactRel pT LT πT ⟨1, fun _ => 7⟩ ⟨1, fun _ => 0⟩ := by
  refine ⟨pT_rel, rfl, rfl, ?_⟩
  rintro ⟨-, h⟩
  have := h 0 (by decide) (by decide)
  revert this
  decide

end Toy.SlotCompact
