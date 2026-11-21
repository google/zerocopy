import ToySlotCompact.Boundaries

/-!
# Definition examples

For each core definition: at least one intended instance it admits and one it rejects.
-/

namespace Toy.SlotCompact

/-! ## Expressions, stores, steps -/

example : (Expr.add (.slot 0) (.const 2)).eval (fun _ => 3 : Store 1) = 5 := rfl
example : (Expr.add (.slot 0) (.const 2) : Expr 1).reads 0 = true := rfl
example : (Expr.const 3 : Expr 1).reads 0 = false := rfl
example : upd (fun _ => 0 : Store 2) 1 5 1 = 5 := rfl
example : upd (fun _ => 0 : Store 2) 1 5 0 = 0 := rfl

example (σ : Store 2) : step pA ⟨0, σ⟩ = .running ⟨1, upd σ 1 5⟩ none := rfl
/-- A `halt` emits the values of its output slots. -/
example (σ : Store 2) : step pA ⟨1, σ⟩ = .halted ⟨1, σ⟩ [σ 0, σ 1] := rfl
/-- Negative: outside the program the machine is stuck. -/
example (σ : Store 2) : step pA ⟨2, σ⟩ = .stuck := rfl
/-- A debug read emits the slot's value as an event. -/
example (σ : Store 1) : step pD ⟨0, σ⟩ = .running ⟨1, σ⟩ (some (σ 0)) := rfl
/-- Storage markers reset the slot. -/
example (σ : Store 2) : step pM ⟨0, σ⟩ = .running ⟨1, upd σ 1 0⟩ none := rfl

/-! ## Uses, defs, successors -/

example : (Instr.assign 1 (.slot 0) : Instr 2).uses 0 = true := rfl
example : (Instr.assign 1 (.slot 0) : Instr 2).uses 1 = false := rfl
/-- Debug reads are not liveness uses. -/
example : (Instr.dbg (.slot 0) : Instr 1).uses 0 = false := rfl
example : (Instr.halt [1] : Instr 2).uses 1 = true := rfl
example : (Instr.storageDead 0 : Instr 2).defs 0 = true := rfl
example : (Instr.dbg (.slot 0) : Instr 1).defs 0 = false := rfl
example : (Instr.branch (.slot 0) 1 4 : Instr 3).succs 0 = [1, 4] := rfl
example : (Instr.halt [1] : Instr 3).succs 4 = [] := rfl

/-! ## Liveness predicates -/

example : ReadsLive pA LA := pA_cert.1
example : ¬ ReadsLive pR LR := pR_not_reads
example : TransferClosed pB LB := pB_cert.2
example : ¬ TransferClosed pT LT := pT_not_transfer
example : DbgReadsLive pS LS := pS_dbg
example : ¬ DbgReadsLive pD LD := pD_not_dbg
example : ReadsKept pD LD := pD_readsKept
example : ¬ ReadsKept pR LR := pR_not_readsKept
example : DbgReadsKept pS LS := dbgReadsKept_of_dbgReadsLive pS_dbg
example : ¬ DbgReadsKept pD LD := pD_not_dbgKept
example : Kept pS LS 0 = true := by decide
example : Kept pS LS 2 = false := pS_not_kept2

/-! ## Compaction -/

example : πS.get? 1 = some 1 := by decide
example : πS.get? 2 = none := by decide
example : compactExpr πS (.add (.slot 0) (.slot 2)) = .add (.slot 0) (.const 0) := by decide
/-- The dead store to the dropped slot `x2` becomes `nop`. -/
example : compactInstr πS (.assign 2 (.const 9)) = .nop := by decide
example : compactInstr πS (.storageLive 1) = .storageLive 1 := by decide
example : compact pS LS πS = [.nop, .storageLive 1, .assign 1 (.add (.slot 0) (.const 1)),
    .dbg (.slot 1), .storageDead 0, .halt [1]] := pS_compact

/-! ## Relations -/

example : CompactRel pA LA πAm ⟨0, fun i => if i = 0 then 3 else 0⟩ ⟨0, fun _ => 3⟩ := pA_rel
/-- Negative: a live slot disagrees. -/
example : ¬ CompactRel pA LA πAm ⟨0, fun _ => 3⟩ ⟨0, fun _ => 4⟩ := by
  rintro ⟨-, h⟩
  have := h 0 (by decide) (by decide)
  revert this
  decide
/-- Negative: the program counters differ. -/
example : ¬ CompactRel pA LA πAm ⟨0, fun _ => 3⟩ ⟨1, fun _ => 3⟩ := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)
/-- `CompactRel` ignores dead slots; `KeptRel` does not. -/
example : CompactRel pA LA πAm ⟨0, fun i => if i = 0 then 3 else 0⟩ ⟨0, fun _ => 3⟩ ∧
    ¬ KeptRel pA LA πAm ⟨0, fun i => if i = 0 then 3 else 0⟩ ⟨0, fun _ => 3⟩ := by
  refine ⟨pA_rel, ?_⟩
  rintro ⟨-, h⟩
  have := h 1 (by decide)
  revert this
  decide
example : KeptRel pA LA πAm ⟨0, fun _ => 3⟩ ⟨0, fun _ => 3⟩ := pA_keptRel

/-! ## Bisimulation -/

/-- Equality is a lockstep bisimulation between a program and itself. -/
theorem lockstepBisim_eq {N : Nat} (p : Prog N) : LockstepBisim p p (fun s s' => s = s') := by
  rintro s s' rfl
  cases step p s <;> simp [ResRel]

example : LockstepBisim pB pB (fun s s' => s = s') := lockstepBisim_eq pB
example : ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := pD_not_bisim
/-- A silent bisimulation that is not a lockstep bisimulation: only the debug event differs. -/
example : SilentBisim pD (compact pD LD πD) (CompactRel pD LD πD) ∧
    ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := pD_silent_not_lockstep
/-- Negative: a compaction that erases a `halt` output is not a lockstep bisimulation. -/
example : ¬ LockstepBisim pO (compact pO LO πO) (CompactRel pO LO πO) := pO_not_bisim

/-! ## Interference conditions -/

example : NoAssignClobber pC LC πCm := pC_assign
example : ¬ NoAssignClobber pA LA πAm := pA_not_assign
example : NoMarkerClobber pS LS πS := noMarkerClobber_of_injective pS_inj
example : ¬ NoMarkerClobber pM LM πMm := pM_not_marker
example : InjOnLiveAt pA LA πAm 0 := pA_inj0
example : ¬ InjOnLiveAt pE LE πEm 0 := pE_not_inj0

/-! ## Store transport -/

example : pullStore πS (fun k => k.val + 10) 1 = 11 := by decide
example : pullStore πS (fun k => k.val + 10) 2 = 0 := by decide
example : pushStore πB 0 (fun i => i.val + 10) 1 = 11 := by decide

/-! ## Execution and weakest preconditions -/

example : IsHalt pA 1 := ⟨[0, 1], rfl⟩
example : ¬ IsHalt pA 0 := by
  rintro ⟨outs, h⟩
  simp [pA] at h
example : wp pB postB ⟨0, fun i => if i = 0 then 1 else if i = 1 then 10 else 0⟩ :=
  nonvacuous_wp_transport.2.2.2.2.2
example (σ : Store 1) : ¬ wp pH postFalse ⟨0, σ⟩ := by
  rw [wp_iff_of_exec (pH_exec σ)]
  exact id
example : PostCorr pA LA πAm postA (pullPost πAm postA) := postCorr_pullPost πAm postA_dep
example : ¬ PostCorr pH LH πH postTrue postFalse := pH_not_postCorr
example : DependsOnlyOnLive pA LA postA := postA_dep
example : ¬ DependsOnlyOnLive pH LH postH := postH_not_dep
example : DependsOnlyOnEntryLive pA LA preA := preA_dep
example : ¬ DependsOnlyOnEntryLive pH LH preH := preH_not_dep

/-! ## Path liveness and the checker -/

example : PathLive pT 0 0 := pT_pathLive
example : ¬ PathLive pB 0 2 := (checkLive_accepts_overapprox.2 0)
example : checkLive pB LB = true := by decide
example : checkLive pR LR = false := by decide
example : checkLive pT LT = false := by decide

/-! ## Stores -/

example : GetPutSame (funOps 1 Nat) := (funOps_laws 1 Nat).1
example : ¬ GetPutSame (ignorePutOps 1) := ignorePutOps_not_getPutSame
example : GetPutOther (alistOps 2 0) := (alistOps_laws 2 0).2.1
example : ¬ GetPutOther (clobberOps 2) := clobberOps_not_getPutOther
example : PutGetId (funOps 2 Nat) := (funOps_laws 2 Nat).2.2.1
example : ¬ PutGetId (alistOps 1 (0 : Nat)) := alistOps_not_putGetId 0 0
example : PutGetId (alistOps 0 (0 : Nat)) := alistOps_zero_putGetId 0
example : PutPut (alistOps 2 (0 : Nat)) := (alistOps_laws 2 0).2.2.1

example : GetPutSame (consPutOps 1) := consPutOps_getPutSame 1
example : ¬ PutPut (consPutOps 1) := consPutOps_not_putPut 0

example : Complete (famAlist 2) := famAlist_complete 2
example : ¬ Complete ([] : List (Fin 1 × Nat)) := cex_alistCost_complete.1
example : alistGet 0 [((0 : Fin 2), 4), (1, 7)] 1 = 7 := rfl
example : alistGet 0 [((0 : Fin 2), 4)] 1 = 0 := rfl
example : alistPut [((0 : Fin 2), 4), (1, 7)] 1 9 = [(0, 4), (1, 9)] := rfl
example : alistPut [((0 : Fin 2), 4)] 1 9 = [(0, 4), (1, 9)] := rfl
example : runCheck (funOps 2 Nat) (fun _ => 0) [.incr 1 0 3, .check 1 3] = true := by decide
example : runCheck (funOps 2 Nat) (fun _ => 0) [.incr 1 0 3, .check 1 4] = false := by decide
example : scanCost [(0 : Fin 3), 1, 2] 2 = 3 := rfl
example : scanCost [(0 : Fin 3), 1] 2 = 2 := rfl
example : runCost (alistOps 3 0) (alistCost 3 Nat) (famAlist 2) (famScript 4 2) = 24 := by decide
example : runCost (funOps 3 Nat) (unitCost _ 3) (fun _ => 0) (famScript 4 2) = 8 := by decide
/-- `runCost`, like `runCheck`, stops at the first failing check. -/
example : runCost (funOps 1 Nat) (unitCost _ 1) (fun _ => 0) [.check 0 99, .incr 0 0 1] = 1 := by
  decide
example : runCost (funOps 1 Nat) (unitCost _ 1) (fun _ => 0) [.check 0 0, .incr 0 0 1] = 3 := by
  decide

end Toy.SlotCompact
