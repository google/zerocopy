import ToySlotCompact.Instances2
import ToySlotCompact.Stores

/-!
# Counterexamples in canonical form

Each theorem exhibits a concrete instance that satisfies every hypothesis of a main result except
one, and in which the conclusion of that result fails. The theorem name records the main result
and the violated hypothesis.
-/

namespace Toy.SlotCompact

/-! ## `compact_lockstepBisim_of_noClobber` -/

theorem cex_bisim_noClobber_readsLive :
    ¬ ReadsLive pR LR ∧ TransferClosed pR LR ∧ DbgReadsLive pR LR ∧ NoAssignClobber pR LR πR ∧
      NoMarkerClobber pR LR πR ∧
      ¬ LockstepBisim pR (compact pR LR πR) (CompactRel pR LR πR) :=
  ⟨pR_not_reads, pR_transfer, pR_dbg, pR_assign, pR_marker, pR_not_bisim⟩

theorem cex_bisim_noClobber_transferClosed :
    ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ DbgReadsLive pT LT ∧ NoAssignClobber pT LT πT ∧
      NoMarkerClobber pT LT πT ∧
      ¬ LockstepBisim pT (compact pT LT πT) (CompactRel pT LT πT) :=
  ⟨pT_reads, pT_not_transfer, pT_dbg, pT_assign, pT_marker, pT_not_bisim⟩

theorem cex_bisim_noClobber_dbgReadsLive :
    ReadsLive pD LD ∧ TransferClosed pD LD ∧ ¬ DbgReadsLive pD LD ∧ NoAssignClobber pD LD πD ∧
      NoMarkerClobber pD LD πD ∧
      ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) :=
  ⟨pD_cert.1, pD_cert.2, pD_not_dbg, pD_assign, pD_marker, pD_not_bisim⟩

theorem cex_bisim_noClobber_noAssignClobber :
    ReadsLive pA LA ∧ TransferClosed pA LA ∧ DbgReadsLive pA LA ∧ ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧
      ¬ LockstepBisim pA (compact pA LA πAm) (CompactRel pA LA πAm) :=
  ⟨pA_cert.1, pA_cert.2, pA_dbg, pA_not_assign, pA_marker, pA_not_bisim⟩

theorem cex_bisim_noClobber_noMarkerClobber :
    ReadsLive pM LM ∧ TransferClosed pM LM ∧ DbgReadsLive pM LM ∧ NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧
      ¬ LockstepBisim pM (compact pM LM πMm) (CompactRel pM LM πMm) :=
  ⟨pM_cert.1, pM_cert.2, pM_dbg, pM_assign, pM_not_marker, pM_not_bisim⟩

/-! ## `compact_lockstepBisim_of_injective` -/

theorem cex_bisim_injective_injective :
    ¬ Function.Injective πAm ∧ ReadsLive pA LA ∧ TransferClosed pA LA ∧ DbgReadsLive pA LA ∧
      ¬ LockstepBisim pA (compact pA LA πAm) (CompactRel pA LA πAm) :=
  ⟨pA_not_inj, pA_cert.1, pA_cert.2, pA_dbg, pA_not_bisim⟩

theorem cex_bisim_injective_readsLive :
    Function.Injective πR ∧ ¬ ReadsLive pR LR ∧ TransferClosed pR LR ∧ DbgReadsLive pR LR ∧
      ¬ LockstepBisim pR (compact pR LR πR) (CompactRel pR LR πR) :=
  ⟨pR_inj, pR_not_reads, pR_transfer, pR_dbg, pR_not_bisim⟩

theorem cex_bisim_injective_transferClosed :
    Function.Injective πT ∧ ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ DbgReadsLive pT LT ∧
      ¬ LockstepBisim pT (compact pT LT πT) (CompactRel pT LT πT) :=
  ⟨pT_inj, pT_reads, pT_not_transfer, pT_dbg, pT_not_bisim⟩

theorem cex_bisim_injective_dbgReadsLive :
    Function.Injective πD ∧ ReadsLive pD LD ∧ TransferClosed pD LD ∧ ¬ DbgReadsLive pD LD ∧
      ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) :=
  ⟨pD_inj, pD_cert.1, pD_cert.2, pD_not_dbg, pD_not_bisim⟩

/-! ## `compact_keptRel_lockstepBisim_of_injective` -/

theorem cex_keptBisim_injective :
    ¬ Function.Injective πAm ∧ ReadsKept pA LA ∧ DbgReadsKept pA LA ∧
      ¬ LockstepBisim pA (compact pA LA πAm) (KeptRel pA LA πAm) :=
  ⟨pA_not_inj, readsKept_of_readsLive pA_cert.1, pA_dbgKept, pA_not_keptBisim⟩

theorem cex_keptBisim_readsKept :
    Function.Injective πR ∧ ¬ ReadsKept pR LR ∧ DbgReadsKept pR LR ∧
      ¬ LockstepBisim pR (compact pR LR πR) (KeptRel pR LR πR) :=
  ⟨pR_inj, pR_not_readsKept, pR_dbgKept, pR_not_keptBisim⟩

theorem cex_keptBisim_dbgReadsKept :
    Function.Injective πD ∧ ReadsKept pD LD ∧ ¬ DbgReadsKept pD LD ∧
      ¬ LockstepBisim pD (compact pD LD πD) (KeptRel pD LD πD) :=
  ⟨pD_inj, pD_readsKept, pD_not_dbgKept, pD_not_keptBisim⟩

/-! ## `wp_transport_of_noClobber` -/

theorem cex_wp_readsLive :
    ¬ ReadsLive pR LR ∧ TransferClosed pR LR ∧ NoAssignClobber pR LR πR ∧
      NoMarkerClobber pR LR πR ∧ PostCorr pR LR πR postR7 (pullPost πR postR7) ∧
      ¬ (∀ s s', CompactRel pR LR πR s s' →
        (wp pR postR7 s ↔ wp (compact pR LR πR) (pullPost πR postR7) s')) :=
  ⟨pR_not_reads, pR_transfer, pR_assign, pR_marker, postCorr_pullPost πR postR7_dep,
    fun h => pR_wp_ne (h _ _ pR_rel)⟩

theorem cex_wp_transferClosed :
    ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ NoAssignClobber pT LT πT ∧
      NoMarkerClobber pT LT πT ∧ PostCorr pT LT πT postT (pullPost πT postT) ∧
      ¬ (∀ s s', CompactRel pT LT πT s s' →
        (wp pT postT s ↔ wp (compact pT LT πT) (pullPost πT postT) s')) :=
  ⟨pT_reads, pT_not_transfer, pT_assign, pT_marker, postCorr_pullPost πT postT_dep,
    fun h => pT_wp_ne (h _ _ pT_rel)⟩

theorem cex_wp_noAssignClobber :
    ReadsLive pA LA ∧ TransferClosed pA LA ∧ ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧ PostCorr pA LA πAm postA (pullPost πAm postA) ∧
      ¬ (∀ s s', CompactRel pA LA πAm s s' →
        (wp pA postA s ↔ wp (compact pA LA πAm) (pullPost πAm postA) s')) :=
  ⟨pA_cert.1, pA_cert.2, pA_not_assign, pA_marker, postCorr_pullPost πAm postA_dep,
    fun h => pA_wp_ne (h _ _ pA_rel)⟩

theorem cex_wp_noMarkerClobber :
    ReadsLive pM LM ∧ TransferClosed pM LM ∧ NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧ PostCorr pM LM πMm postM (pullPost πMm postM) ∧
      ¬ (∀ s s', CompactRel pM LM πMm s s' →
        (wp pM postM s ↔ wp (compact pM LM πMm) (pullPost πMm postM) s')) :=
  ⟨pM_cert.1, pM_cert.2, pM_assign, pM_not_marker, postCorr_pullPost πMm postM_dep,
    fun h => pM_wp_ne (h _ _ pM_rel)⟩

theorem cex_wp_postCorr :
    ReadsLive pH LH ∧ TransferClosed pH LH ∧ NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧ ¬ PostCorr pH LH πH postTrue postFalse ∧
      ¬ (∀ s s', CompactRel pH LH πH s s' →
        (wp pH postTrue s ↔ wp (compact pH LH πH) postFalse s')) :=
  ⟨pH_cert.1, pH_cert.2, pH_assign, pH_marker, pH_not_postCorr, fun h => pH_wp_ne (h _ _ pH_rel)⟩

/-! ## `exists_postCorr_iff_dependsOnlyOnLive` -/

theorem cex_postClass_injAtHalts :
    ¬ (∀ pc, IsHalt pE3 pc → InjOnLiveAt pE3 LE3 πE3 pc) ∧
      ¬ ((∃ Q', PostCorr pE3 LE3 πE3 postE3 Q') ↔ DependsOnlyOnLive pE3 LE3 postE3) :=
  ⟨fun h => pE3_not_injAtHalt (h 0 ⟨[0, 1], rfl⟩),
    fun h => pE3_not_dep (h.mp ⟨_, pE3_postCorr_false⟩)⟩

/-! ## `compactRel_pushStore` -/

/-- Without injectivity on the live slots, the push-forward need not be related: on `pE` both
entry-live slots are merged and `pushStore` can hold only one of their values. -/
theorem cex_pushStore_injOnLiveAt :
    ¬ InjOnLiveAt pE LE πEm 0 ∧
      ¬ CompactRel pE LE πEm ⟨0, fun i => i.val⟩ ⟨0, pushStore πEm 0 (fun i => i.val)⟩ := by
  refine ⟨pE_not_inj0, ?_⟩
  rintro ⟨-, h⟩
  have := h 1 (by decide) (by decide)
  revert this
  decide

/-! ## `postCorr_pullPost` -/

/-- Without `DependsOnlyOnLive`, `pullPost π Q` need not correspond to `Q`: on `pH`, `postH` reads
the dropped slot, which the pulled-back store always reads as `0`. -/
theorem cex_postCorr_pullPost_dependsOnlyOnLive :
    ¬ DependsOnlyOnLive pH LH postH ∧ ¬ PostCorr pH LH πH postH (pullPost πH postH) := by
  refine ⟨postH_not_dep, fun h => ?_⟩
  have := (h ⟨0, fun _ => 1⟩ ⟨0, fun _ => 0⟩ ⟨[], rfl⟩ ⟨rfl, by decide⟩).mpr (by
    show pullStore πH (fun _ => 0) 0 = 0
    unfold pullStore
    simp [Compaction.get?_of_not_kept πH (i := 0) (by decide)])
  revert this
  unfold postH
  decide

/-! ## `vc_forward_of_noClobber` -/

theorem cex_vcFwd_readsLive :
    ¬ ReadsLive pX LX ∧
      TransferClosed pX LX ∧
      NoAssignClobber pX LX πXm ∧
      NoMarkerClobber pX LX πXm ∧
      DependsOnlyOnLive pX LX postX ∧
      ¬ ((∀ σ, preA σ → wp pX postX ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πXm σ') → wp (compact pX LX πXm) (pullPost πXm postX) ⟨0, σ'⟩)) :=
  ⟨pX_not_reads, pX_transfer, pX_assign, pX_marker, postX_dep, fun h => pX_vc_fwd_fails.2 (h pX_vc_fwd_fails.1)⟩

theorem cex_vcFwd_transferClosed :
    ReadsLive pV LV ∧
      ¬ TransferClosed pV LV ∧
      NoAssignClobber pV LV πVm ∧
      NoMarkerClobber pV LV πVm ∧
      DependsOnlyOnLive pV LV postV3 ∧
      ¬ ((∀ σ, preA σ → wp pV postV3 ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πVm σ') → wp (compact pV LV πVm) (pullPost πVm postV3) ⟨0, σ'⟩)) :=
  ⟨pV_reads, pV_not_transfer, pV_assign, pV_marker, postV3_dep, fun h => pV_vc_fwd_fails.2 (h pV_vc_fwd_fails.1)⟩

theorem cex_vcFwd_noAssignClobber :
    ReadsLive pA LA ∧
      TransferClosed pA LA ∧
      ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧
      DependsOnlyOnLive pA LA postA ∧
      ¬ ((∀ σ, preA σ → wp pA postA ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πAm σ') → wp (compact pA LA πAm) (pullPost πAm postA) ⟨0, σ'⟩)) :=
  ⟨pA_cert.1, pA_cert.2, pA_not_assign, pA_marker, postA_dep, fun h => pA_vc_fwd_fails.2 (h pA_vc_fwd_fails.1)⟩

theorem cex_vcFwd_noMarkerClobber :
    ReadsLive pM LM ∧
      TransferClosed pM LM ∧
      NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧
      DependsOnlyOnLive pM LM postM ∧
      ¬ ((∀ σ, preA σ → wp pM postM ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πMm σ') → wp (compact pM LM πMm) (pullPost πMm postM) ⟨0, σ'⟩)) :=
  ⟨pM_cert.1, pM_cert.2, pM_assign, pM_not_marker, postM_dep, fun h => pM_vc_fwd_fails.2 (h pM_vc_fwd_fails.1)⟩

theorem cex_vcFwd_post :
    ReadsLive pK LK ∧
      TransferClosed pK LK ∧
      NoAssignClobber pK LK πK ∧
      NoMarkerClobber pK LK πK ∧
      ¬ DependsOnlyOnLive pK LK postK ∧
      ¬ ((∀ σ, preTrue σ → wp pK postK ⟨0, σ⟩) →
        (∀ σ', preTrue (pullStore πK σ') → wp (compact pK LK πK) (pullPost πK postK) ⟨0, σ'⟩)) :=
  ⟨pK_cert.1, pK_cert.2, pK_assign, pK_marker, postK_not_dep, fun h => pK_vc_fwd_fails.2 (h pK_vc_fwd_fails.1)⟩

/-! ## `vc_backward_of_noClobber` -/

theorem cex_vcBwd_readsLive :
    ¬ ReadsLive pR LR ∧
      TransferClosed pR LR ∧
      NoAssignClobber pR LR πR ∧
      NoMarkerClobber pR LR πR ∧
      InjOnLiveAt pR LR πR 0 ∧
      DependsOnlyOnEntryLive pR LR preTrue ∧
      DependsOnlyOnLive pR LR postR0 ∧
      ¬ ((∀ σ', preTrue (pullStore πR σ') → wp (compact pR LR πR) (pullPost πR postR0) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pR postR0 ⟨0, σ⟩)) :=
  ⟨pR_not_reads, pR_transfer, pR_assign, pR_marker, pR_inj0, preTrue_dep, postR0_dep, fun h => pR_vc_bwd_fails.2 (h pR_vc_bwd_fails.1)⟩

theorem cex_vcBwd_transferClosed :
    ReadsLive pV LV ∧
      ¬ TransferClosed pV LV ∧
      NoAssignClobber pV LV πVm ∧
      NoMarkerClobber pV LV πVm ∧
      InjOnLiveAt pV LV πVm 0 ∧
      DependsOnlyOnEntryLive pV LV preTrue ∧
      DependsOnlyOnLive pV LV postV ∧
      ¬ ((∀ σ', preTrue (pullStore πVm σ') → wp (compact pV LV πVm) (pullPost πVm postV) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pV postV ⟨0, σ⟩)) :=
  ⟨pV_reads, pV_not_transfer, pV_assign, pV_marker, pV_inj0, preTrue_dep, postV_dep, fun h => pV_vc_bwd_fails.2 (h pV_vc_bwd_fails.1)⟩

theorem cex_vcBwd_noAssignClobber :
    ReadsLive pA LA ∧
      TransferClosed pA LA ∧
      ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧
      InjOnLiveAt pA LA πAm 0 ∧
      DependsOnlyOnEntryLive pA LA preTrue ∧
      DependsOnlyOnLive pA LA postA5 ∧
      ¬ ((∀ σ', preTrue (pullStore πAm σ') → wp (compact pA LA πAm) (pullPost πAm postA5) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pA postA5 ⟨0, σ⟩)) :=
  ⟨pA_cert.1, pA_cert.2, pA_not_assign, pA_marker, pA_inj0, preTrue_dep, postA5_dep, fun h => pA_vc_bwd_fails.2 (h pA_vc_bwd_fails.1)⟩

theorem cex_vcBwd_noMarkerClobber :
    ReadsLive pM LM ∧
      TransferClosed pM LM ∧
      NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧
      InjOnLiveAt pM LM πMm 0 ∧
      DependsOnlyOnEntryLive pM LM preTrue ∧
      DependsOnlyOnLive pM LM postM0 ∧
      ¬ ((∀ σ', preTrue (pullStore πMm σ') → wp (compact pM LM πMm) (pullPost πMm postM0) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pM postM0 ⟨0, σ⟩)) :=
  ⟨pM_cert.1, pM_cert.2, pM_assign, pM_not_marker, pM_inj0, preTrue_dep, postM0_dep, fun h => pM_vc_bwd_fails.2 (h pM_vc_bwd_fails.1)⟩

theorem cex_vcBwd_injOnLiveAt :
    ReadsLive pE LE ∧
      TransferClosed pE LE ∧
      NoAssignClobber pE LE πEm ∧
      NoMarkerClobber pE LE πEm ∧
      ¬ InjOnLiveAt pE LE πEm 0 ∧
      DependsOnlyOnEntryLive pE LE preTrue ∧
      DependsOnlyOnLive pE LE postE ∧
      ¬ ((∀ σ', preTrue (pullStore πEm σ') → wp (compact pE LE πEm) (pullPost πEm postE) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pE postE ⟨0, σ⟩)) :=
  ⟨pE_cert.1, pE_cert.2, pE_assign, pE_marker, pE_not_inj0, preTrue_dep, postE_dep, fun h => pE_vc_bwd_fails.2 (h pE_vc_bwd_fails.1)⟩

theorem cex_vcBwd_pre :
    ReadsLive pH LH ∧
      TransferClosed pH LH ∧
      NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧
      InjOnLiveAt pH LH πH 0 ∧
      ¬ DependsOnlyOnEntryLive pH LH preH ∧
      DependsOnlyOnLive pH LH postFalse ∧
      ¬ ((∀ σ', preH (pullStore πH σ') → wp (compact pH LH πH) (pullPost πH postFalse) ⟨0, σ'⟩) →
        (∀ σ, preH σ → wp pH postFalse ⟨0, σ⟩)) :=
  ⟨pH_cert.1, pH_cert.2, pH_assign, pH_marker, pH_inj0, preH_not_dep, postFalse_dep, fun h => pH_vc_pre_bwd_fails.2 (h pH_vc_pre_bwd_fails.1)⟩

theorem cex_vcBwd_post :
    ReadsLive pH LH ∧
      TransferClosed pH LH ∧
      NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧
      InjOnLiveAt pH LH πH 0 ∧
      DependsOnlyOnEntryLive pH LH preTrue ∧
      ¬ DependsOnlyOnLive pH LH postH ∧
      ¬ ((∀ σ', preTrue (pullStore πH σ') → wp (compact pH LH πH) (pullPost πH postH) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pH postH ⟨0, σ⟩)) :=
  ⟨pH_cert.1, pH_cert.2, pH_assign, pH_marker, pH_inj0, preTrue_dep, postH_not_dep, fun h => pH_vc_post_bwd_fails.2 (h pH_vc_post_bwd_fails.1)⟩

/-! ## `pathLive_imp_mask_of_cert` -/

theorem cex_cert_readsLive :
    ¬ ReadsLive pU LU ∧ TransferClosed pU LU ∧ PathLive pU 0 0 ∧ LU 0 0 = false :=
  ⟨pU_not_reads, pU_transfer, pU_pathLive, rfl⟩

theorem cex_cert_transferClosed :
    ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ PathLive pT 0 0 ∧ LT 0 0 = false :=
  ⟨pT_reads, pT_not_transfer, pT_pathLive, rfl⟩

/-! ## Store interface -/

/-- A store whose `put` is ignored: satisfies `GetPutOther` but not `GetPutSame`. -/
def ignorePutOps (N : Nat) : StoreOps (Fin N → Nat) N Nat := ⟨fun σ k => σ k, fun σ _ _ => σ⟩
/-- A store whose `put` zeroes every other key: satisfies `GetPutSame` but not `GetPutOther`. -/
def clobberOps (N : Nat) : StoreOps (Fin N → Nat) N Nat :=
  ⟨fun σ k => σ k, fun _ k v => fun j => if j = k then v else 0⟩

theorem ignorePutOps_getPutOther (N : Nat) : GetPutOther (ignorePutOps N) := fun _ _ _ _ _ => rfl
theorem ignorePutOps_not_getPutSame : ¬ GetPutSame (ignorePutOps 1) := by
  intro h
  have := h (fun _ => 0) 0 1
  simp [ignorePutOps] at this
theorem clobberOps_getPutSame (N : Nat) : GetPutSame (clobberOps N) := by
  intro s k v
  simp [clobberOps]
theorem clobberOps_not_getPutOther : ¬ GetPutOther (clobberOps 2) := by
  intro h
  have := h (fun _ => 5) 0 1 0 (by decide)
  simp [clobberOps] at this

theorem cex_repInd_h1s :
    ¬ GetPutSame (ignorePutOps 1) ∧ GetPutOther (ignorePutOps 1) ∧ GetPutSame (funOps 1 Nat) ∧
      GetPutOther (funOps 1 Nat) ∧
      (∀ k, (ignorePutOps 1).get (fun _ => 0) k = (funOps 1 Nat).get (fun _ => 0) k) ∧
      runCheck (ignorePutOps 1) (fun _ => 0) [.incr 0 0 1, .check 0 1] ≠
        runCheck (funOps 1 Nat) (fun _ => 0) [.incr 0 0 1, .check 0 1] :=
  ⟨ignorePutOps_not_getPutSame, ignorePutOps_getPutOther 1, (funOps_laws 1 Nat).1,
    (funOps_laws 1 Nat).2.1, fun _ => rfl, by decide⟩

theorem cex_repInd_h1o :
    GetPutSame (clobberOps 2) ∧ ¬ GetPutOther (clobberOps 2) ∧ GetPutSame (funOps 2 Nat) ∧
      GetPutOther (funOps 2 Nat) ∧
      (∀ k, (clobberOps 2).get (fun _ => 5) k = (funOps 2 Nat).get (fun _ => 5) k) ∧
      runCheck (clobberOps 2) (fun _ => 5) [.incr 0 0 1, .check 1 5] ≠
        runCheck (funOps 2 Nat) (fun _ => 5) [.incr 0 0 1, .check 1 5] :=
  ⟨clobberOps_getPutSame 2, clobberOps_not_getPutOther, (funOps_laws 2 Nat).1,
    (funOps_laws 2 Nat).2.1, fun _ => rfl, by decide⟩

theorem cex_repInd_h2s :
    GetPutSame (funOps 1 Nat) ∧ GetPutOther (funOps 1 Nat) ∧ ¬ GetPutSame (ignorePutOps 1) ∧
      GetPutOther (ignorePutOps 1) ∧
      (∀ k, (funOps 1 Nat).get (fun _ => 0) k = (ignorePutOps 1).get (fun _ => 0) k) ∧
      runCheck (funOps 1 Nat) (fun _ => 0) [.incr 0 0 1, .check 0 1] ≠
        runCheck (ignorePutOps 1) (fun _ => 0) [.incr 0 0 1, .check 0 1] :=
  ⟨(funOps_laws 1 Nat).1, (funOps_laws 1 Nat).2.1, ignorePutOps_not_getPutSame,
    ignorePutOps_getPutOther 1, fun _ => rfl, by decide⟩

theorem cex_repInd_h2o :
    GetPutSame (funOps 2 Nat) ∧ GetPutOther (funOps 2 Nat) ∧ GetPutSame (clobberOps 2) ∧
      ¬ GetPutOther (clobberOps 2) ∧
      (∀ k, (funOps 2 Nat).get (fun _ => 5) k = (clobberOps 2).get (fun _ => 5) k) ∧
      runCheck (funOps 2 Nat) (fun _ => 5) [.incr 0 0 1, .check 1 5] ≠
        runCheck (clobberOps 2) (fun _ => 5) [.incr 0 0 1, .check 1 5] :=
  ⟨(funOps_laws 2 Nat).1, (funOps_laws 2 Nat).2.1, clobberOps_getPutSame 2,
    clobberOps_not_getPutOther, fun _ => rfl, by decide⟩

theorem cex_repInd_view :
    GetPutSame (funOps 1 Nat) ∧ GetPutOther (funOps 1 Nat) ∧
      ¬ (∀ k, (funOps 1 Nat).get (fun _ => 0) k = (funOps 1 Nat).get (fun _ => 1) k) ∧
      runCheck (funOps 1 Nat) (fun _ => 0) [.check 0 0] ≠
        runCheck (funOps 1 Nat) (fun _ => 1) [.check 0 0] :=
  ⟨(funOps_laws 1 Nat).1, (funOps_laws 1 Nat).2.1, fun h => absurd (h 0) (by decide), by decide⟩

/-- `runCheck_funOps_eq_alistOps` needs equal views: with the indexed store holding `1` and the
empty association list reading the default `0`, the verdicts differ. -/
theorem cex_repInd_funOps_alistOps_view :
    alistGet 0 ([] : List (Fin 1 × Nat)) ≠ (fun _ => 1) ∧
      runCheck (funOps 1 Nat) (fun _ => 1) [.check 0 1] ≠ runCheck (alistOps 1 0) [] [.check 0 1] :=
  ⟨fun h => absurd (congrFun h 0) (by decide), by decide⟩

/-- Without completeness the association list grows and the `2 S L` bound (with `L` the initial
length) fails. -/
theorem cex_alistCost_complete :
    ¬ Complete ([] : List (Fin 1 × Nat)) ∧
      ¬ runCost (alistOps 1 0) (alistCost 1 Nat) [] [.incr 0 0 0, .incr 0 0 0] ≤
        2 * [Cmd.incr (0 : Fin 1) 0 0, .incr 0 0 0].length * ([] : List (Fin 1 × Nat)).length :=
  ⟨fun h => by simpa using h 0, by decide⟩

end Toy.SlotCompact
