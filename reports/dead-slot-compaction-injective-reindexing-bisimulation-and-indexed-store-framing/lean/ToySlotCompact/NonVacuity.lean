import ToySlotCompact.Counterexamples

/-!
# Non-vacuity witnesses and positive controls

Each theorem exhibits a concrete instance satisfying all hypotheses of a main result (and, where
useful, shows that the conclusion has content on that instance).
-/

namespace Toy.SlotCompact

/-- `compact_lockstepBisim_of_noClobber` applies to a non-injective slot sharing (`pC`). -/
theorem nonvacuous_bisim_noClobber_sharing :
    ReadsLive pC LC ∧ TransferClosed pC LC ∧ DbgReadsLive pC LC ∧ NoAssignClobber pC LC πCm ∧
      NoMarkerClobber pC LC πCm ∧ ¬ Function.Injective πCm :=
  ⟨pC_cert.1, pC_cert.2, pC_dbg, pC_assign, pC_marker, pC_not_inj⟩

/-- `compact_lockstepBisim_of_noClobber` applies to a loop (`pB`). -/
theorem nonvacuous_bisim_noClobber_loop :
    ReadsLive pB LB ∧ TransferClosed pB LB ∧ DbgReadsLive pB LB ∧ NoAssignClobber pB LB πB ∧
      NoMarkerClobber pB LB πB :=
  ⟨pB_cert.1, pB_cert.2, pB_dbg, noAssignClobber_of_injective pB_inj,
    noMarkerClobber_of_injective pB_inj⟩

/-- `compact_lockstepBisim_of_injective` applies to straight-line code with resetting storage
markers, a debug read of a live slot, and a dropped dead store (`pS`). -/
theorem nonvacuous_bisim_injective_straightLine :
    Function.Injective πS ∧ ReadsLive pS LS ∧ TransferClosed pS LS ∧ DbgReadsLive pS LS ∧
      Kept pS LS 2 = false :=
  ⟨pS_inj, pS_cert.1, pS_cert.2, pS_dbg, pS_not_kept2⟩

/-- `compact_lockstepBisim_of_injective` applies to a loop (`pB`). -/
theorem nonvacuous_bisim_injective_loop :
    Function.Injective πB ∧ ReadsLive pB LB ∧ TransferClosed pB LB ∧ DbgReadsLive pB LB :=
  ⟨pB_inj, pB_cert.1, pB_cert.2, pB_dbg⟩

/-- `compact_keptRel_lockstepBisim_of_injective` applies to `pS`. -/
theorem nonvacuous_keptBisim :
    Function.Injective πS ∧ ReadsKept pS LS ∧ DbgReadsKept pS LS :=
  ⟨pS_inj, readsKept_of_readsLive pS_cert.1, dbgReadsKept_of_dbgReadsLive pS_dbg⟩

/-- Both sides of `forall_exists_compactRel_iff_injOnLiveAt` occur: true for `pB` at entry,
false for `pE` at entry. -/
theorem nonvacuous_entry_iff : InjOnLiveAt pB LB πB 0 ∧ ¬ InjOnLiveAt pE LE πEm 0 :=
  ⟨injOnLiveAt_of_injective pB_inj 0, pE_not_inj0⟩

/-- `wp_transport_of_noClobber` applies to the loop `pB` with a postcondition that genuinely
holds on a run around the loop. -/
theorem nonvacuous_wp_transport :
    ReadsLive pB LB ∧ TransferClosed pB LB ∧ NoAssignClobber pB LB πB ∧
      NoMarkerClobber pB LB πB ∧ PostCorr pB LB πB postB (pullPost πB postB) ∧
      wp pB postB ⟨0, fun i => if i = 0 then 1 else if i = 1 then 10 else 0⟩ := by
  refine ⟨pB_cert.1, pB_cert.2, noAssignClobber_of_injective pB_inj,
    noMarkerClobber_of_injective pB_inj, postCorr_pullPost πB postB_dep, ?_⟩
  rw [wp_iff_of_exec pB_exec]
  unfold postB postAt
  decide

/-- `wp_transport_of_noClobber` relates actual state pairs on `pB`: the push-forward of the entry
store used above is `CompactRel`-related to it. -/
theorem nonvacuous_wp_transport_rel :
    CompactRel pB LB πB ⟨0, fun i => if i = 0 then 1 else if i = 1 then 10 else 0⟩
      ⟨0, pushStore πB 0 (fun i => if i = 0 then 1 else if i = 1 then 10 else 0)⟩ :=
  compactRel_pushStore (injOnLiveAt_of_injective pB_inj 0) _

/-- `exists_postCorr_iff_dependsOnlyOnLive` applies to `pB`, with both sides true for `postB`. -/
theorem nonvacuous_postClass :
    (∀ pc, IsHalt pB pc → InjOnLiveAt pB LB πB pc) ∧ DependsOnlyOnLive pB LB postB :=
  ⟨pB_injAtHalts, postB_dep⟩

/-- Precondition for `pS`: the input `x0` is `0`. -/
def preS : Store 3 → Prop := fun σ => σ 0 = 0
/-- Postcondition for `pS`: at the halt, `x1 = 1`. -/
def postS : State 3 → Prop := postAt 5 1 1

theorem pS_exec (σ : Store 3) :
    exec pS 6 ⟨0, σ⟩ = some ⟨5, upd (upd (upd (upd σ 2 9) 1 0) 1 (σ 0 + 1)) 0 0⟩ := rfl

/-- `vc_forward_of_noClobber` applies to `pS`: its hypotheses hold, the precondition is
satisfiable, and the original verification condition (the premise) holds. -/
theorem nonvacuous_vc :
    ReadsLive pS LS ∧ TransferClosed pS LS ∧ NoAssignClobber pS LS πS ∧
      NoMarkerClobber pS LS πS ∧ InjOnLiveAt pS LS πS 0 ∧ DependsOnlyOnEntryLive pS LS preS ∧
      DependsOnlyOnLive pS LS postS ∧ (∃ σ, preS σ) ∧ (∃ σ', preS (pullStore πS σ')) ∧
      (∀ σ, preS σ → wp pS postS ⟨0, σ⟩) := by
  refine ⟨pS_cert.1, pS_cert.2, noAssignClobber_of_injective pS_inj,
    noMarkerClobber_of_injective pS_inj, injOnLiveAt_of_injective pS_inj 0, ?_,
    dependsOnlyOnLive_postAt 1 (by decide), ⟨fun _ => 0, rfl⟩, ⟨fun _ => 0, by unfold preS; decide⟩, ?_⟩
  · intro σ τ h
    unfold preS
    rw [h 0 (by decide) (by decide)]
  · intro σ hσ
    rw [wp_iff_of_exec (pS_exec σ)]
    intro _
    show upd (upd (upd (upd σ 2 9) 1 0) 1 (σ 0 + 1)) 0 0 1 = 1
    unfold preS at hσ
    simp [upd, hσ]

/-- Precondition for `pC`: the input `x0` is `4`. -/
def preC : Store 3 → Prop := fun σ => σ 0 = 4
/-- Postcondition for `pC`: at the halt, `x1 = 5`. -/
def postC : State 3 → Prop := postAt 3 1 5

theorem pC_exec_c (σ' : Store 1) :
    exec (compact pC LC πCm) 4 ⟨0, σ'⟩ = some ⟨3, upd σ' 0 (σ' 0 + 1)⟩ := rfl

/-- `vc_backward_of_noClobber` applies to the non-injective sharing `pC`: all its hypotheses hold,
the transported precondition is satisfiable, and the compacted verification condition (the
premise) holds. -/
theorem nonvacuous_vc_bwd_sharing :
    ReadsLive pC LC ∧ TransferClosed pC LC ∧ NoAssignClobber pC LC πCm ∧
      NoMarkerClobber pC LC πCm ∧ InjOnLiveAt pC LC πCm 0 ∧
      DependsOnlyOnEntryLive pC LC preC ∧ DependsOnlyOnLive pC LC postC ∧
      ¬ Function.Injective πCm ∧
      (∃ σ', preC (pullStore πCm σ')) ∧
      (∀ σ', preC (pullStore πCm σ') →
        wp (compact pC LC πCm) (pullPost πCm postC) ⟨0, σ'⟩) := by
  refine ⟨pC_cert.1, pC_cert.2, pC_assign, pC_marker, pC_inj0, ?_,
    dependsOnlyOnLive_postAt 5 (by decide), pC_not_inj, ⟨fun _ => 4, rfl⟩, ?_⟩
  · intro σ τ h
    unfold preC
    rw [h 0 (by decide) (by decide)]
  · intro σ' hpre
    rw [wp_iff_of_exec (pC_exec_c σ')]
    intro _
    unfold preC at hpre
    rw [pullStore_kept πCm σ' (i := 0) (by decide)] at hpre
    change σ' 0 = 4 at hpre
    show pullStore πCm (upd σ' 0 (σ' 0 + 1)) 1 = 5
    rw [pullStore_kept πCm _ (i := 1) (by decide)]
    change upd σ' 0 (σ' 0 + 1) 0 = 5
    rw [upd_same, hpre]

/-- `pathLive_imp_mask_of_cert` applies to the loop `pB`, where `x0` is path-live at entry. -/
theorem nonvacuous_cert : ReadsLive pB LB ∧ TransferClosed pB LB ∧ PathLive pB 0 0 :=
  ⟨pB_cert.1, pB_cert.2, PathLive.use (ins := .branch (.slot 0) 1 4) rfl (by decide)⟩

/-- A path-live slot omitted by a mask (the hypotheses of `checkLive_eq_false_of_missing`), and
the checker indeed rejects that mask. -/
theorem checkLive_rejects_underapprox : PathLive pR 0 0 ∧ LR 0 0 = false ∧ checkLive pR LR = false :=
  ⟨PathLive.use (ins := .assign 1 (.slot 0)) rfl (by decide), rfl, by decide⟩

/-- Slots that no instruction uses are never path-live. -/
theorem not_pathLive_of_unused {N : Nat} {p : Prog N} {i : Fin N}
    (h : ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ins.uses i = false) {pc : Nat} :
    ¬ PathLive p pc i := by
  intro hl
  induction hl with
  | use hins hu => rw [h _ _ hins] at hu; exact absurd hu (by decide)
  | pass _ _ _ _ ih => exact ih h

/-- **Positive control for checker precision.** The checker accepts the all-live mask on `pB`,
although slot `x2` is not live anywhere: acceptance certifies over-approximation only. -/
theorem checkLive_accepts_overapprox :
    checkLive pB (fun _ _ => true) = true ∧ ∀ pc, ¬ PathLive pB pc 2 := by
  refine ⟨by decide, fun pc => not_pathLive_of_unused ?_⟩
  intro pc' ins hins
  have := (all_points_iff pB (fun _ ins => !ins.uses 2)).mp (by decide) pc' ins hins
  simpa using this

/-- `pathLive_imp_mask_of_cert` needs the slot to be path-live: on `pB` the certificate `LB` omits
the never-used slot `x2`. -/
theorem cex_cert_pathLive :
    ReadsLive pB LB ∧ TransferClosed pB LB ∧ ¬ PathLive pB 0 2 ∧ LB 0 2 = false :=
  ⟨pB_cert.1, pB_cert.2, checkLive_accepts_overapprox.2 0, by decide⟩

/-- `checkLive_sound` applies to `pB`: the mask is accepted and `x0` is path-live at entry. -/
theorem nonvacuous_checkLive_sound : checkLive pB LB = true ∧ PathLive pB 0 0 ∧ LB 0 0 = true :=
  ⟨by decide, nonvacuous_cert.2.2, by decide⟩

/-- Both verdicts of `checkLive` occur (`checkLive_eq_true_iff` relates nonempty classes). -/
theorem checkLive_both_verdicts : checkLive pB LB = true ∧ checkLive pR LR = false :=
  ⟨by decide, by decide⟩

/-- `checkLive_sound` needs acceptance: on `pU` the empty mask omits the path-live output `x0`. -/
theorem cex_checkLive_sound_accepted :
    checkLive pU LU = false ∧ PathLive pU 0 0 ∧ LU 0 0 = false :=
  ⟨by decide, pU_pathLive, rfl⟩

/-- `checkLive_sound` needs the slot to be path-live: the accepted `LB` omits the unused `x2`. -/
theorem cex_checkLive_sound_pathLive :
    checkLive pB LB = true ∧ ¬ PathLive pB 0 2 ∧ LB 0 2 = false :=
  ⟨by decide, checkLive_accepts_overapprox.2 0, by decide⟩

/-- `checkLive_eq_false_of_missing` needs the omitted slot to be path-live: `pB`'s mask omits the
never-used slot `x2` and is accepted. -/
theorem cex_missing_requires_pathLive :
    ¬ PathLive pB 0 2 ∧ LB 0 2 = false ∧ checkLive pB LB = true :=
  ⟨checkLive_accepts_overapprox.2 0, by decide, by decide⟩

/-- `checkLive_eq_false_of_missing` needs the slot to be omitted: a path-live slot that the mask
contains does not force rejection. -/
theorem cex_missing_requires_omission :
    PathLive pB 0 0 ∧ LB 0 0 = true ∧ checkLive pB LB = true :=
  ⟨nonvacuous_cert.2.2, by decide, by decide⟩

/-- `compact_keptRel_lockstepBisim_of_injective` applies to a mask that is not closed under the
backward transfer (`pT`). -/
theorem nonvacuous_keptBisim_not_transferClosed :
    Function.Injective πT ∧ ReadsKept pT LT ∧ DbgReadsKept pT LT ∧ ¬ TransferClosed pT LT :=
  ⟨pT_inj, readsKept_of_readsLive pT_reads, dbgReadsKept_of_dbgReadsLive pT_dbg, pT_not_transfer⟩

/-- `compact_keptRel_lockstepBisim_of_injective` applies to a debug read of a kept slot at a point
where the slot is dead (`pKD`). -/
theorem nonvacuous_keptBisim_kept_dead_dbg :
    Function.Injective πKD ∧ ReadsKept pKD LKD ∧ DbgReadsKept pKD LKD ∧ ¬ DbgReadsLive pKD LKD :=
  ⟨pKD_inj, readsKept_of_readsLive pKD_cert.1, pKD_dbgKept, pKD_not_dbg⟩

/-- `runCheck_funOps_eq_alistOps` applies: the indexed store `x0 = 4, x1 = 7` is the view of the
association list `[(0, 4), (1, 7)]`, and the verdict on the script is `true`. -/
theorem nonvacuous_repInd_funOps_alistOps :
    alistGet 0 [((0 : Fin 2), 4), (1, 7)] = (fun k : Fin 2 => if k = 0 then 4 else 7) ∧
      runCheck (funOps 2 Nat) (fun k : Fin 2 => if k = 0 then 4 else 7)
        [.incr 1 0 3, .check 1 7, .check 0 4] = true := by
  refine ⟨?_, by decide⟩
  funext k
  revert k
  decide

/-- Representation independence applies to the indexed store and a complete association list
with the same view, on a script where the verdict is `true`. -/
theorem nonvacuous_repInd :
    GetPutSame (funOps 2 Nat) ∧ GetPutOther (funOps 2 Nat) ∧ GetPutSame (alistOps 2 0) ∧
      GetPutOther (alistOps 2 0) ∧
      (∀ k, (funOps 2 Nat).get (alistGet 0 [(0, 4), (1, 7)]) k =
        (alistOps 2 0).get [(0, 4), (1, 7)] k) ∧
      runCheck (alistOps 2 0) [(0, 4), (1, 7)] [.incr 1 0 3, .check 1 7, .check 0 4] = true :=
  ⟨(funOps_laws 2 Nat).1, (funOps_laws 2 Nat).2.1, (alistOps_laws 2 0).1,
    (alistOps_laws 2 0).2.1, fun _ => rfl, by decide⟩

/-- The family inputs are complete association lists (the hypothesis of the general upper
bound). -/
theorem famAlist_complete (L : Nat) : Complete (famAlist L) := by
  intro k
  simp [famAlist, List.map_map, Function.comp_def]

end Toy.SlotCompact
