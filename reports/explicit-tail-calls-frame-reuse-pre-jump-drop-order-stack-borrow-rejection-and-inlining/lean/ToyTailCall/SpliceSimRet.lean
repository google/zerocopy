import ToyTailCall.SpliceSimInl

/-!
# Proof support: return from, and unwinding through, a spliced callee
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}
variable {a b : State} {G C M : Frame} {os ss : List Frame}

theorem run_one' (sem : Sem) (D : Option Nat) (p : Prog) (st : State) :
    run sem D p 1 (.running st) = step sem D p st := rfl

theorem T_lt (S : Site) : S.nC + S.nG < S.nC + S.nG + S.nT := by
  simp only [Site.nT]; omega

/-- From a merged frame whose callee slots are finalized, return to a plain frame of `ci`. -/
theorem InlCtx.toPlain (c : InlCtx S ρ a b G C M os ss) {a' b' : State} {G' M' C1 M1 : Frame}
    (ha' : a'.stack = C1 :: os) (hb' : b'.stack = M1 :: ss)
    (hI' : InlRel S ρ G' C M') (hna : (dropList S.gf G' (pendingDrops S.gf G') false).2.2 ≠ .abort)
    {Mf : Frame} (hIf : InlRel S ρ (dropList S.gf G' (pendingDrops S.gf G') false).1 C Mf)
    (hP1 : PlainRel S ρ C Mf → PlainRel S ρ C1 M1)
    (hpc : a'.unwinding = false → M1.pc = C1.pc)
    (hfC : C1.fid = C.fid) (hfM : M1.fid = M.fid) (hvC : ∀ v ∈ C1.vals, PtrLt a.nextFid v)
    (hn : a'.nextFid = a.nextFid) (hn' : b'.nextFid = b.nextFid) (hu : b'.unwinding = a'.unwinding)
    (he : b'.events = a'.events) : Match S (.running a') (.running b') := by
  have hG : ∀ s, s < S.nG → Mf.isLive (s + S.nC) = true → S.gf.dtor s = .none := by
    intro s hs hl
    have hlen : s < (dropList S.gf G' (pendingDrops S.gf G') false).1.vals.length := by
      rw [(dropList_frame _ _ _ _).1, hI'.lenG]; exact hs
    rw [hIf.embG.live s hlen] at hl
    exact dropped_g hI' hna s hs hl
  have hP := hP1 (plain_of_inl hIf hG)
  refine match_running (relAt_plain hP hpc c.hB ha' hb' ?_ ?_ ?_ hu he)
  · rw [hn]
    exact bounded_head (fun Y hY => c.bA Y (List.mem_cons_of_mem _ hY))
      ⟨by rw [hfC]; exact (c.bA C (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1, hvC⟩
  · rw [hn']; exact fresh_head c.bB hfM
  · exact pairwise_head c.pw hfM

theorem sim_inl_ret {D : Option Nat} (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = false)
    {op : Operand} (hq : S.gf.code[G.pc]? = some (.ret op)) :
    ∃ m, Match S (step .frameReuse D S.p a) (run .frameReuse D S.p' m (.running b)) := by
  have hu' : b.unwinding = false := by rw [c.hr.uw, hu]
  have hGb := c.bA G (List.mem_cons_self ..)
  have hCb := c.bA C (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hlenM := c.hI.vlen'
  have hlenC := c.hI.lenC
  rw [step_exec c.ha c.fnG hu c.hI.owfG.ret hq]
  simp only [execI]
  cases hev : evalOp (C :: os) G op with
  | none => exact ⟨0, match_ub a⟩
  | some vf =>
    obtain ⟨v, G1⟩ := vf
    obtain ⟨e1, e2⟩ := evalOp_sim c.hI.embG c.hI.fidG c.look hev
    have hv := evalOp_ptrLt hGb.1 c.vals hev
    have ho : ∀ s, op = .move s → s < G.vals.length := by
      intro s hs; subst hs; exact evalOp_move_lt hev
    subst e2
    simp only
    have hpcM := c.hpc hu
    have hc0 := c.code0 hu hq rfl
    have hc1 : S.c'.code[M.pc + 1]? = some (.dropSlots ((List.range S.nG).reverse.map (· + S.nC))
        (S.gStart + S.K * G.pc + 2)) := by
      rw [c.code hu hq (by simp [spliceInstr])]; rfl
    have hc2 : S.c'.code[M.pc + 2]? = some (.assign S.dst (.move (S.nC + S.nG)) S.next) := by
      rw [c.code hu hq (by simp [spliceInstr])]; rfl
    -- spliced step 1
    have hT : S.nC + S.nG < (killOf S.nC op M).vals.length := by
      simp only [killOf_vals, hlenM]; exact T_lt S
    have st1 : step .frameReuse D S.p' b = .running { b with stack :=
        { (killOf S.nC op M).write (S.nC + S.nG) (rv ρ v) with pc := S.gStart + S.K * G.pc + 1 } ::
          ss } := by
      rw [step_exec c.hb c.fnM hu' c.hI.ret' hc0]
      simp only [execI, e1, hT, ↓reduceIte]
    let M2 : Frame :=
      { (killOf S.nC op M).write (S.nC + S.nG) (rv ρ v) with pc := S.gStart + S.K * G.pc + 1 }
    have hI2 : InlRel S ρ (killOf 0 op G) C M2 :=
      (((c.hI.killOf op ho).writeT (Nat.le_refl _) (T_lt S) (rv ρ v))).congr rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hM2T : M2.get (S.nC + S.nG) = rv ρ v := by
      change ((killOf S.nC op M).write (S.nC + S.nG) (rv ρ v)).get (S.nC + S.nG) = _
      rw [get_write _ _ hT]; simp
    have hl : ∀ s ∈ pendingDrops S.gf (killOf 0 op G), s < (killOf 0 op G).vals.length :=
      fun s hs => mem_pendingDrops_lt hs
    obtain ⟨hd, hI3⟩ := hI2.dropListG _ hl false
    have hfl := filter_gslots hI2
    have hpc1 : M2.pc = M.pc + 1 := by simp [M2, hpcM]
    have st2 : step .frameReuse D S.p' { b with stack := M2 :: ss } =
        execI .frameReuse D S.p' { b with stack := M2 :: ss } S.c' M2 ss
          (.dropSlots ((List.range S.nG).reverse.map (· + S.nC)) (S.gStart + S.K * G.pc + 2)) :=
      step_exec rfl (by simpa [M2] using c.fnM) (by simpa using hu') (by simpa [M2] using c.hI.ret')
        (by rw [hpc1]; exact hc1)
    simp only [execI, hfl, hd] at st2
    have hfr' := dropList_frame S.c' M2 ((pendingDrops S.gf (killOf 0 op G)).map (· + S.nC)) false
    simp only [doReturn]
    cases hend : (dropList S.gf (killOf 0 op G) (pendingDrops S.gf (killOf 0 op G)) false).2.2 with
    | abort =>
      rw [hend] at st2
      refine ⟨2, ?_⟩
      rw [run_succ, st1, run_succ, st2]
      exact match_halt _ (by simp [c.hr.ev])
    | unwind =>
      rw [hend] at st2
      refine ⟨2, ?_⟩
      rw [run_succ, st1, run_succ, st2]
      simp only [unwindBelow]
      exact c.toPlain rfl rfl hI2 (by rw [hend]; simp) hI3 id (fun h => by simp at h) rfl
        (by rw [hfr'.2.1]; simp [M2]) hCb.2 rfl rfl rfl (by simp [c.hr.ev])
    | ok =>
      rw [hend] at st2
      refine ⟨3, ?_⟩
      let M3 : Frame := { (dropList S.c' M2 ((pendingDrops S.gf (killOf 0 op G)).map (· + S.nC))
        false).1 with pc := S.gStart + S.K * G.pc + 2 }
      have hM3v : M3.vals = M2.vals := by simp [M3, hfr'.1]
      have hT3 : S.nC + S.nG < M3.vals.length := by rw [hM3v]; simpa [M2] using hT
      have hM3T : M3.get (S.nC + S.nG) = rv ρ v := by
        unfold Frame.get; rw [hM3v]; exact hM2T
      have hdst : S.dst < (M3.kill (S.nC + S.nG)).vals.length := by
        simp only [kill_vals]; rw [hM3v]; simp only [M2, write_vals_length, killOf_vals, hlenM]
        have := S.hdst; simp only [Site.nC] at *; omega
      have st3 : ∀ ev, step .frameReuse D S.p' { b with stack := M3 :: ss, events := ev } =
          .running { b with stack := { (M3.kill (S.nC + S.nG)).write S.dst (rv ρ v) with
            pc := S.next } :: ss, events := ev } := by
        intro ev
        have hpc3 : M3.pc = M.pc + 2 := by simp only [M3]; omega
        have hfn3 : S.p'.fns[M3.fn]? = some S.c' := by
          simp only [M3]; rw [hfr'.2.2.1]; simpa [M2] using c.fnM
        have hret3 : M3.pendingRet = none := by
          simp only [M3]; rw [hfr'.2.2.2]; simpa [M2] using c.hI.ret'
        rw [step_exec rfl hfn3 (by simpa using hu') hret3 (by rw [hpc3]; exact hc2)]
        simp only [execI, evalOp, hT3, ↓reduceIte, hM3T, hdst]
      rw [run_succ, st1, run_succ, st2, run_succ, st3]
      simp only [deliver, c.hc]
      have hdC : S.dst < C.vals.length := by rw [hlenC]; exact S.hdst
      have hI4 : InlRel S ρ (dropList S.gf (killOf 0 op G) (pendingDrops S.gf (killOf 0 op G)) false).1
          C (M3.kill (S.nC + S.nG)) :=
        InlRel.killT (hI3.congr (C1 := C) (M1 := M3) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl) (Nat.le_refl _)
      have hfr3 : (M3.kill (S.nC + S.nG)).fid = M.fid := by
        simp only [M3, kill_fid]; rw [hfr'.2.1]; simp [M2]
      refine c.toPlain rfl rfl hI2 (by rw [hend]; simp) hI4
        (fun hP => (hP.write hdC v).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        (fun _ => rfl) rfl (by simpa using hfr3) ?_ rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
      intro w hw
      rcases write_vals C S.dst v w hw with hw | rfl
      · exact hCb.2 w hw
      · exact hv

/-- Unwinding through a spliced callee: two original steps, one spliced step. -/
theorem sim_inl_unw {D : Option Nat} (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = true) :
    ∃ j m, 0 < j ∧ Match S (run .frameReuse D S.p j (.running a))
      (run .frameReuse D S.p' m (.running b)) := by
  have hu' : b.unwinding = true := by rw [c.hr.uw, hu]
  have hlenC := c.hI.lenC
  have hl1 : ∀ s ∈ pendingDrops S.gf G, s < G.vals.length := fun s hs => mem_pendingDrops_lt hs
  obtain ⟨hd1, hI1⟩ := c.hI.dropListG _ hl1 true
  have hpd := pendingDrops_merged c.hI
  have hstepB : step .frameReuse D S.p' b = unwStep b S.c' M ss := step_unw c.hb c.fnM hu'
  have hstepA : step .frameReuse D S.p a = unwStep a S.gf G (C :: os) := step_unw c.ha c.fnG hu
  -- the second part of the merged finalization
  have hl2 : ∀ s ∈ pendingDrops S.c C, s < C.vals.length := fun s hs => mem_pendingDrops_lt hs
  obtain ⟨hd2, -, -⟩ := dropList_sim (off := 0) S.c S.c' (pendingDrops S.c C) C
    (dropList S.c' M ((pendingDrops S.gf G).map (· + S.nC)) true).1 true hI1.embC hl2
    (fun s hs => S.c'_dtor_c (by rw [← hlenC]; exact hl2 s hs))
  rw [map_add_zero] at hd2
  have happ := dropList_append_true S.c' M ((pendingDrops S.gf G).map (· + S.nC)) (pendingDrops S.c C)
  rw [← hpd] at happ
  cases hend1 : (dropList S.gf G (pendingDrops S.gf G) true).2.2 with
  | ok => exact absurd hend1 (dropList_true_ne_ok _ _ _)
  | abort =>
    refine ⟨1, 1, Nat.one_pos, ?_⟩
    rw [run_one', run_one', hstepA, hstepB]
    have h1 : (dropList S.c' M ((pendingDrops S.gf G).map (· + S.nC)) true).2.2 = .abort := by
      rw [hd1, hend1]
    simp only [unwStep, happ, h1, ↓reduceIte, hend1]
    rw [hd1]
    exact match_halt _ (by simp [c.hr.ev])
  | unwind =>
    have h1 : (dropList S.c' M ((pendingDrops S.gf G).map (· + S.nC)) true).2.2 ≠ .abort := by
      rw [hd1, hend1]; simp
    have hA1 : step .frameReuse D S.p a = .running { a with stack := C :: os, events :=
        a.events ++ (dropList S.gf G (pendingDrops S.gf G) true).2.1 } := by
      rw [hstepA]; simp only [unwStep, hend1]
    have hA2 : ∀ ev, step .frameReuse D S.p { a with stack := C :: os, events := ev } =
        unwStep { a with stack := C :: os, events := ev } S.c C os :=
      fun ev => step_unw rfl c.fnC (by simpa using hu)
    refine ⟨2, 1, by omega, ?_⟩
    rw [run_succ, hA1, run_one', hA2, run_one', hstepB]
    simp only [unwStep, happ, h1, ↓reduceIte, hd2]
    rw [hd1]
    simp only [List.append_assoc]
    cases hend2 : (dropList S.c C (pendingDrops S.c C) true).2.2 with
    | ok => exact absurd hend2 (dropList_true_ne_ok _ _ _)
    | abort => simp only; exact match_halt _ (by simp [c.hr.ev])
    | unwind =>
      simp only
      have hbA : ∀ X ∈ os, Bounded a.nextFid X :=
        fun X hX => c.bA X (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX))
      have hbB : ∀ Y ∈ ss, Y.fid < b.nextFid := fun Y hY => c.bB Y (List.mem_cons_of_mem _ hY)
      cases os with
      | nil =>
        have : ss = [] := (below_nil_iff c.hB).1 rfl
        subst this
        simp only
        exact match_halt _ (by simp [c.hr.ev])
      | cons X os' =>
        cases ss with
        | nil => exact absurd ((below_nil_iff c.hB).2 rfl) (by simp)
        | cons Y ss' =>
          simp only
          exact match_running (relAt_below c.hB (by simp) hbA hbB (List.pairwise_cons.mp c.pw).2
            rfl rfl (by simp [hu]) (by simp [hu']) (by simp [c.hr.ev]))

end

end Toy.TailCall.SpliceProof
