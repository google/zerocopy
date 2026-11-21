import ToySlotCompact.Decide

/-!
# Concrete instances

Small programs used by the definition examples, the counterexamples (each violating exactly one
hypothesis of the result it refutes) and the non-vacuity witnesses. Facts are established by
evaluation (`decide`, `rfl`) or by the Boolean checks of `ToySlotCompact.Decide`.
-/

namespace Toy.SlotCompact

/-- Boolean check that `π` is injective on the live slots at every `halt` point. -/
def checkInjAtHalts {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => match ins with
      | .halt _ => checkInjOnLiveAt p L π pc
      | _ => true

theorem injAtHalts_of_check {N M : Nat} {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : checkInjAtHalts p L π = true) : ∀ pc, IsHalt p pc → InjOnLiveAt p L π pc := by
  rintro pc ⟨outs, hins⟩
  exact injOnLiveAt_of_check ((all_points_iff p _).mp h pc _ hins)

/-- The trivial precondition. -/
def preTrue {N : Nat} : Store N → Prop := fun _ => True
theorem preTrue_dep {N : Nat} {p : Prog N} {L : Ann N} : DependsOnlyOnEntryLive p L preTrue :=
  fun _ _ _ => Iff.rfl

/-! ## `pA`: an assignment clobbers a merged live slot -/

/-- `x1 := 5; halt [x0, x1]`. Slot `x0` is an input that stays live to the end. -/
def pA : Prog 2 := [.assign 1 (.const 5), .halt [0, 1]]
/-- Live-in masks of `pA` (path liveness): `{x0}` then `{x0, x1}`. -/
def LA : Ann 2 := fun pc i => if pc = 0 then decide (i = 0) else decide (pc = 1)
/-- Merges both slots of `pA` into one. -/
def πAm : Compaction pA LA 1 := fun _ => 0

theorem pA_cert : ReadsLive pA LA ∧ TransferClosed pA LA :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pA_dbg : DbgReadsLive pA LA := dbgReadsLive_of_check (by decide)
theorem pA_dbgKept : DbgReadsKept pA LA := dbgReadsKept_of_check (by decide)
theorem pA_marker : NoMarkerClobber pA LA πAm := noMarkerClobber_of_check (by decide)
theorem pA_inj0 : InjOnLiveAt pA LA πAm 0 := injOnLiveAt_of_check (by decide)
theorem pA_not_assign : ¬ NoAssignClobber pA LA πAm := by
  intro h
  exact h 0 1 (.const 5) rfl (by decide) 0 (by decide) (by decide) (by decide) rfl
theorem pA_not_inj : ¬ Function.Injective πAm := by
  intro h
  have := h (a₁ := ⟨0, by decide⟩) (a₂ := ⟨1, by decide⟩) rfl
  simp at this
theorem pA_exec (σ : Store 2) : exec pA 2 ⟨0, σ⟩ = some ⟨1, upd σ 1 5⟩ := rfl
theorem pA_exec_c (σ' : Store 1) :
    exec (compact pA LA πAm) 2 ⟨0, σ'⟩ = some ⟨1, upd σ' 0 5⟩ := rfl

/-- Precondition used with `pA` and `pM`. -/
def preA : Store 2 → Prop := fun σ => σ 0 = 3
/-- Postcondition used with `pA`: at the halt, slot `x0` holds `3`. -/
def postA : State 2 → Prop := postAt 1 0 3

theorem postA_dep : DependsOnlyOnLive pA LA postA := dependsOnlyOnLive_postAt 3 (by decide)
theorem preA_dep : DependsOnlyOnEntryLive pA LA preA := by
  intro σ τ h
  unfold preA
  rw [h 0 (by decide) (by decide)]

/-- On `pA` with the merging `πAm`, the original keeps `x0 = 3` but the compacted run does not. -/
theorem pA_wp_ne :
    ¬ (wp pA postA ⟨0, fun i => if i = 0 then 3 else 0⟩ ↔
      wp (compact pA LA πAm) (pullPost πAm postA) ⟨0, fun _ => 3⟩) := by
  rw [wp_iff_of_exec (pA_exec _), wp_iff_of_exec (pA_exec_c _)]
  unfold postA postAt pullPost
  decide

theorem pA_rel : CompactRel pA LA πAm ⟨0, fun i => if i = 0 then 3 else 0⟩ ⟨0, fun _ => 3⟩ :=
  ⟨rfl, by decide⟩

theorem pA_not_bisim : ¬ LockstepBisim pA (compact pA LA πAm) (CompactRel pA LA πAm) :=
  not_lockstepBisim_of_wp_ne (postCorr_pullPost πAm postA_dep) pA_rel pA_wp_ne

theorem pA_keptRel : KeptRel pA LA πAm ⟨0, fun _ => 3⟩ ⟨0, fun _ => 3⟩ := ⟨rfl, by decide⟩

theorem pA_not_keptBisim : ¬ LockstepBisim pA (compact pA LA πAm) (KeptRel pA LA πAm) := by
  apply not_lockstepBisim_of_wp_ne (keptRel_postAt_iff (h := 1) (j := 0) 3 (by decide)) pA_keptRel
  rw [wp_iff_of_exec (pA_exec _), wp_iff_of_exec (pA_exec_c _)]
  unfold postAt pullPost
  decide

theorem pA_vc_fwd_fails :
    (∀ σ, preA σ → wp pA postA ⟨0, σ⟩) ∧
      ¬ (∀ σ', preA (pullStore πAm σ') → wp (compact pA LA πAm) (pullPost πAm postA) ⟨0, σ'⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ hσ
    rw [wp_iff_of_exec (pA_exec σ)]
    intro _
    show upd σ 1 5 0 = 3
    rw [upd_other _ _ (by decide)]
    exact hσ
  · have := H (fun _ => 3) (by unfold preA; decide)
    rw [wp_iff_of_exec (pA_exec_c _)] at this
    revert this
    unfold postA postAt pullPost
    decide

/-! ## `pM`: a storage marker clobbers a merged live slot -/

/-- `StorageLive(x1); x1 := x0; halt [x1]`. Slots `x0` and `x1` are never assigned while the other
is live, but the marker of `x1` fires while `x0` is still live. -/
def pM : Prog 2 := [.storageLive 1, .assign 1 (.slot 0), .halt [1]]
/-- Live-in masks of `pM` (path liveness): `{x0}`, `{x0}`, `{x1}`. -/
def LM : Ann 2 := fun pc i => if pc ≤ 1 then decide (i = 0) else decide (pc = 2 ∧ i = 1)
/-- Merges both slots of `pM` into one. -/
def πMm : Compaction pM LM 1 := fun _ => 0

theorem pM_cert : ReadsLive pM LM ∧ TransferClosed pM LM :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pM_dbg : DbgReadsLive pM LM := dbgReadsLive_of_check (by decide)
theorem pM_assign : NoAssignClobber pM LM πMm := noAssignClobber_of_check (by decide)
theorem pM_inj0 : InjOnLiveAt pM LM πMm 0 := injOnLiveAt_of_check (by decide)
theorem pM_not_marker : ¬ NoMarkerClobber pM LM πMm := by
  intro h
  exact h 0 1 (Or.inl rfl) (by decide) 0 (by decide) (by decide) (by decide) rfl
theorem pM_exec (σ : Store 2) : exec pM 3 ⟨0, σ⟩ = some ⟨2, upd (upd σ 1 0) 1 (σ 0)⟩ := rfl
theorem pM_exec_c (σ' : Store 1) :
    exec (compact pM LM πMm) 3 ⟨0, σ'⟩ = some ⟨2, upd (upd σ' 0 0) 0 0⟩ := rfl

/-- Postcondition used with `pM`: at the halt, slot `x1` holds `3`. -/
def postM : State 2 → Prop := postAt 2 1 3
theorem postM_dep : DependsOnlyOnLive pM LM postM := dependsOnlyOnLive_postAt 3 (by decide)
theorem preA_depM : DependsOnlyOnEntryLive pM LM preA := by
  intro σ τ h
  unfold preA
  rw [h 0 (by decide) (by decide)]

theorem pM_rel : CompactRel pM LM πMm ⟨0, fun i => if i = 0 then 3 else 0⟩ ⟨0, fun _ => 3⟩ :=
  ⟨rfl, by decide⟩

theorem pM_wp_ne :
    ¬ (wp pM postM ⟨0, fun i => if i = 0 then 3 else 0⟩ ↔
      wp (compact pM LM πMm) (pullPost πMm postM) ⟨0, fun _ => 3⟩) := by
  rw [wp_iff_of_exec (pM_exec _), wp_iff_of_exec (pM_exec_c _)]
  unfold postM postAt pullPost
  decide

theorem pM_not_bisim : ¬ LockstepBisim pM (compact pM LM πMm) (CompactRel pM LM πMm) :=
  not_lockstepBisim_of_wp_ne (postCorr_pullPost πMm postM_dep) pM_rel pM_wp_ne

theorem pM_vc_fwd_fails :
    (∀ σ, preA σ → wp pM postM ⟨0, σ⟩) ∧
      ¬ (∀ σ', preA (pullStore πMm σ') → wp (compact pM LM πMm) (pullPost πMm postM) ⟨0, σ'⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ hσ
    rw [wp_iff_of_exec (pM_exec σ)]
    intro _
    show upd (upd σ 1 0) 1 (σ 0) 1 = 3
    rw [upd_same]
    exact hσ
  · have := H (fun _ => 3) (by unfold preA; decide)
    rw [wp_iff_of_exec (pM_exec_c _)] at this
    revert this
    unfold postM postAt pullPost
    decide

/-! ## `pR`: a read of a slot the mask does not declare live -/

/-- `x1 := x0; halt [x1]`, with a mask that omits `x0` at the read. -/
def pR : Prog 2 := [.assign 1 (.slot 0), .halt [1]]
/-- Mask of `pR` missing the read slot: `{}` then `{x1}`. -/
def LR : Ann 2 := fun pc i => decide (pc = 1 ∧ i = 1)
/-- The only kept slot of `pR` is `x1`. -/
def πR : Compaction pR LR 1 := fun _ => 0

theorem pR_transfer : TransferClosed pR LR := (checkTransfer_eq_true_iff _ _).mp (by decide)
theorem pR_not_reads : ¬ ReadsLive pR LR := by
  intro h
  have := h 0 _ rfl 0 rfl
  revert this
  decide
theorem pR_not_readsKept : ¬ ReadsKept pR LR := by
  intro h
  have := h 0 _ rfl 0 rfl
  revert this
  decide
theorem pR_dbg : DbgReadsLive pR LR := dbgReadsLive_of_check (by decide)
theorem pR_dbgKept : DbgReadsKept pR LR := dbgReadsKept_of_check (by decide)
theorem pR_assign : NoAssignClobber pR LR πR := noAssignClobber_of_check (by decide)
theorem pR_marker : NoMarkerClobber pR LR πR := noMarkerClobber_of_check (by decide)
theorem pR_inj : Function.Injective πR := injective_of_check (by decide)
theorem pR_inj0 : InjOnLiveAt pR LR πR 0 := injOnLiveAt_of_check (by decide)
theorem pR_exec (σ : Store 2) : exec pR 2 ⟨0, σ⟩ = some ⟨1, upd σ 1 (σ 0)⟩ := rfl
theorem pR_exec_c (σ' : Store 1) :
    exec (compact pR LR πR) 2 ⟨0, σ'⟩ = some ⟨1, upd σ' 0 0⟩ := rfl

/-- Postcondition for the bisimulation failure on `pR`: `x1 = 7` at the halt. -/
def postR7 : State 2 → Prop := postAt 1 1 7
/-- Postcondition for the verification-condition failure on `pR`: `x1 = 0` at the halt. -/
def postR0 : State 2 → Prop := postAt 1 1 0
theorem postR7_dep : DependsOnlyOnLive pR LR postR7 := dependsOnlyOnLive_postAt 7 (by decide)
theorem postR0_dep : DependsOnlyOnLive pR LR postR0 := dependsOnlyOnLive_postAt 0 (by decide)

theorem pR_rel : CompactRel pR LR πR ⟨0, fun i => if i = 0 then 7 else 0⟩ ⟨0, fun _ => 0⟩ :=
  ⟨rfl, by decide⟩
theorem pR_keptRel : KeptRel pR LR πR ⟨0, fun i => if i = 0 then 7 else 0⟩ ⟨0, fun _ => 0⟩ :=
  ⟨rfl, by decide⟩

theorem pR_wp_ne :
    ¬ (wp pR postR7 ⟨0, fun i => if i = 0 then 7 else 0⟩ ↔
      wp (compact pR LR πR) (pullPost πR postR7) ⟨0, fun _ => 0⟩) := by
  rw [wp_iff_of_exec (pR_exec _), wp_iff_of_exec (pR_exec_c _)]
  unfold postR7 postAt pullPost
  decide

theorem pR_not_bisim : ¬ LockstepBisim pR (compact pR LR πR) (CompactRel pR LR πR) :=
  not_lockstepBisim_of_wp_ne (postCorr_pullPost πR postR7_dep) pR_rel pR_wp_ne

theorem pR_not_keptBisim : ¬ LockstepBisim pR (compact pR LR πR) (KeptRel pR LR πR) :=
  not_lockstepBisim_of_wp_ne (keptRel_postAt_iff 7 (by decide)) pR_keptRel pR_wp_ne

theorem pR_vc_bwd_fails :
    (∀ σ', preTrue (pullStore πR σ') → wp (compact pR LR πR) (pullPost πR postR0) ⟨0, σ'⟩) ∧
      ¬ (∀ σ, preTrue σ → wp pR postR0 ⟨0, σ⟩) := by
  refine ⟨?_, fun H => ?_⟩
  · intro σ' _
    rw [wp_iff_of_exec (pR_exec_c σ')]
    intro _
    show pullStore πR (upd σ' 0 0) 1 = 0
    rw [pullStore_kept πR _ (by decide)]
    exact upd_same _ _ _
  · have := H (fun _ => 1) trivial
    rw [wp_iff_of_exec (pR_exec _)] at this
    revert this
    unfold postR0 postAt
    decide

/-! ## `pT`: a mask that is not closed under the backward transfer -/

/-- `nop; halt [x0]`, with a mask that omits `x0` before the `nop`. -/
def pT : Prog 1 := [.nop, .halt [0]]
/-- Mask of `pT`: `{}` then `{x0}`. -/
def LT : Ann 1 := fun pc _ => decide (pc = 1)
/-- The identity compaction of `pT`. -/
def πT : Compaction pT LT 1 := fun x => x.val

theorem pT_reads : ReadsLive pT LT := (checkReads_eq_true_iff _ _).mp (by decide)
theorem pT_not_transfer : ¬ TransferClosed pT LT := by
  intro h
  have := h 0 _ rfl 1 (by decide) 0 rfl rfl
  revert this
  decide
theorem pT_dbg : DbgReadsLive pT LT := dbgReadsLive_of_check (by decide)
theorem pT_assign : NoAssignClobber pT LT πT := noAssignClobber_of_check (by decide)
theorem pT_marker : NoMarkerClobber pT LT πT := noMarkerClobber_of_check (by decide)
theorem pT_inj : Function.Injective πT := injective_of_check (by decide)
theorem pT_exec (σ : Store 1) : exec pT 2 ⟨0, σ⟩ = some ⟨1, σ⟩ := rfl
theorem pT_exec_c (σ' : Store 1) : exec (compact pT LT πT) 2 ⟨0, σ'⟩ = some ⟨1, σ'⟩ := rfl

/-- Postcondition used with `pT`: `x0 = 7` at the halt. -/
def postT : State 1 → Prop := postAt 1 0 7
theorem postT_dep : DependsOnlyOnLive pT LT postT := dependsOnlyOnLive_postAt 7 (by decide)

theorem pT_rel : CompactRel pT LT πT ⟨0, fun _ => 7⟩ ⟨0, fun _ => 0⟩ := ⟨rfl, by decide⟩

theorem pT_wp_ne :
    ¬ (wp pT postT ⟨0, fun _ => 7⟩ ↔ wp (compact pT LT πT) (pullPost πT postT) ⟨0, fun _ => 0⟩) := by
  rw [wp_iff_of_exec (pT_exec _), wp_iff_of_exec (pT_exec_c _)]
  unfold postT postAt pullPost
  decide

theorem pT_not_bisim : ¬ LockstepBisim pT (compact pT LT πT) (CompactRel pT LT πT) :=
  not_lockstepBisim_of_wp_ne (postCorr_pullPost πT postT_dep) pT_rel pT_wp_ne

/-- `x0` is path-live before the `nop` of `pT`, yet the mask omits it. -/
theorem pT_pathLive : PathLive pT 0 0 :=
  PathLive.pass (ins := .nop) (s := 1) rfl (by decide) rfl
    (PathLive.use (pc := 1) (ins := .halt [0]) rfl (by decide))

/-! ## `pD`: a debug read of a slot that is not live -/

/-- `dbg x0; halt []`: the debug read observes a dead slot. -/
def pD : Prog 1 := [.dbg (.slot 0), .halt []]
/-- Mask of `pD`: nothing is live (path liveness; debug reads are not uses). -/
def LD : Ann 1 := fun _ _ => false
/-- The (empty) compaction of `pD`. -/
def πD : Compaction pD LD 1 := fun _ => 0

theorem pD_cert : ReadsLive pD LD ∧ TransferClosed pD LD :=
  (checkLive_eq_true_iff _ _).mp (by decide)
theorem pD_readsKept : ReadsKept pD LD := readsKept_of_readsLive pD_cert.1
theorem pD_assign : NoAssignClobber pD LD πD := noAssignClobber_of_check (by decide)
theorem pD_marker : NoMarkerClobber pD LD πD := noMarkerClobber_of_check (by decide)
theorem pD_inj : Function.Injective πD := injective_of_check (by decide)
theorem pD_not_dbg : ¬ DbgReadsLive pD LD := by
  intro h
  have := h 0 _ rfl 0 rfl
  revert this
  decide
theorem pD_not_dbgKept : ¬ DbgReadsKept pD LD := by
  intro h
  have := h 0 _ rfl 0 rfl
  revert this
  decide

theorem pD_not_bisim : ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := by
  intro h
  obtain ⟨hev, -⟩ := h ⟨0, fun _ => 7⟩ ⟨0, fun _ => 0⟩ ⟨rfl, by decide⟩
  revert hev
  decide

theorem pD_not_keptBisim : ¬ LockstepBisim pD (compact pD LD πD) (KeptRel pD LD πD) := by
  intro h
  obtain ⟨hev, -⟩ := h ⟨0, fun _ => 7⟩ ⟨0, fun _ => 0⟩ ⟨rfl, by decide⟩
  revert hev
  decide

end Toy.SlotCompact
