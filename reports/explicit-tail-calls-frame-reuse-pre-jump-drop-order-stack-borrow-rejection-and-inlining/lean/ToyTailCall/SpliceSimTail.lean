import ToyTailCall.SpliceSimRet

/-!
# Proof support: a tail call of the spliced callee
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}
variable {a b : State} {G C M : Frame} {os ss : List Frame}

theorem evalOps_length {below : List Frame} :
    ∀ (os : List Operand) (fr : Frame) (vs : List Val) (fr1 : Frame),
      evalOps below fr os = some (vs, fr1) → vs.length = os.length
  | [], fr, vs, fr1, h => by
    simp only [evalOps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | o :: os, fr, vs, fr1, h => by
    simp only [evalOps] at h
    cases h1 : evalOp below fr o with
    | none => rw [h1] at h; cases h
    | some vf =>
      obtain ⟨v, fr2⟩ := vf
      rw [h1] at h
      simp only at h
      cases h2 : evalOps below fr2 os with
      | none => rw [h2] at h; cases h
      | some vf2 =>
        obtain ⟨vs2, fr3⟩ := vf2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp [evalOps_length os fr2 vs2 fr3 h2]

theorem match_bump_left {ca cb : Conf} (h : Match S ca cb) : Match S (bumpTail ca) cb := by
  rcases h with ⟨a, b, rfl, rfl, ρ, hr⟩ | ⟨ra, rb, rfl, rfl, ho, he⟩ | ⟨ra, rfl, ho⟩
  · exact Or.inl ⟨_, b, rfl, rfl, ρ, ⟨hr.top, hr.uw, hr.ev, hr.freshA, hr.freshB, hr.orderB⟩⟩
  · exact match_halted ho he
  · exact Or.inr (Or.inr ⟨ra, rfl, ho⟩)

/-- After `g`'s slots are finalized, the merged frame is a plain frame of `ci`. -/
theorem plain_after_drop {G' M' Mf : Frame} (hI' : InlRel S ρ G' C M')
    (hna : (dropList S.gf G' (pendingDrops S.gf G') false).2.2 ≠ .abort)
    (hIf : InlRel S ρ (dropList S.gf G' (pendingDrops S.gf G') false).1 C Mf) :
    PlainRel S ρ C Mf := by
  refine plain_of_inl hIf fun s hs hl => ?_
  have hlen : s < (dropList S.gf G' (pendingDrops S.gf G') false).1.vals.length := by
    rw [(dropList_frame _ _ _ _).1, hI'.lenG]; exact hs
  rw [hIf.embG.live s hlen] at hl
  exact dropped_g hI' hna s hs hl

theorem tail_code (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = false) {h : FnId}
    {targs : List Operand} (hq : S.gf.code[G.pc]? = some (.tailCall h targs)) {j : Nat}
    (hj : j < (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc
      (.tailCall h targs)).length) :
    S.c'.code[S.gStart + S.K * G.pc + j]? =
      (assignTemps S.nC (S.nC + S.nG + 1) (S.gStart + S.K * G.pc) 0 targs ++
        [.dropSlots ((List.range S.nG).reverse.map (· + S.nC))
          (S.gStart + S.K * G.pc + targs.length + 1),
         .call h ((List.range targs.length).map fun i => .move (S.nC + S.nG + 1 + i)) S.dst
          S.next])[j]? := by
  have := c.code hu hq hj
  rw [c.hpc hu] at this
  rw [this]; rfl

theorem sim_inl_tail {D : Option Nat} (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = false)
    {h : FnId} {targs : List Operand} (hq : S.gf.code[G.pc]? = some (.tailCall h targs)) :
    ∃ m, Match S (step .frameReuse D S.p a) (run .frameReuse D S.p' m (.running b)) := by
  have hu' : b.unwinding = false := by rw [c.hr.uw, hu]
  have hGb := c.bA G (List.mem_cons_self ..)
  have hCb := c.bA C (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hlenM := c.hI.vlen'
  have hlenC := c.hI.lenC
  have hlenG := c.hI.lenG
  have hpcM := c.hpc hu
  rw [step_exec c.ha c.fnG hu c.hI.owfG.ret hq]
  simp only [execI]
  cases hev : evalOps (C :: os) G targs with
  | none => exact ⟨0, match_ub a⟩
  | some vf =>
    obtain ⟨vs, G1⟩ := vf
    simp only
    obtain ⟨ks, hks, e2, -⟩ := evalOps_sim targs G M vs G1 c.hI.embG c.hI.fidG c.look hev
    have hvs := evalOps_ptrLt targs G vs G1 hGb.1 c.vals hev
    have hvlen := evalOps_length targs G vs G1 hev
    have hA : targs.length ≤ maxTailArity S.gf.code :=
      Site.maxTailArity_ge _ h targs (List.mem_of_getElem? hq)
    have hblk : (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc
        (.tailCall h targs)).length = targs.length + 2 := by
      simp [spliceInstr, Site.assignTemps_length]
    have hcodeT : ∀ j (hj : j < targs.length), S.c'.code[S.gStart + S.K * G.pc + (0 + j)]? =
        some (.assign (S.nC + S.nG + 1 + (0 + j)) (renOp S.nC targs[j])
          (S.gStart + S.K * G.pc + (0 + j) + 1)) := by
      intro j hj
      rw [Nat.zero_add, tail_code c hu hq (j := j) (by omega),
        List.getElem?_append_left (by rw [Site.assignTemps_length]; exact hj),
        Site.assignTemps_getElem?]
      simp [List.getElem?_eq_getElem hj]
    have hcodeD : S.c'.code[S.gStart + S.K * G.pc + targs.length]? =
        some (.dropSlots ((List.range S.nG).reverse.map (· + S.nC))
          (S.gStart + S.K * G.pc + targs.length + 1)) := by
      rw [tail_code c hu hq (j := targs.length) (by omega),
        List.getElem?_append_right (by simp [Site.assignTemps_length])]
      simp [Site.assignTemps_length]
    have hcodeC : S.c'.code[S.gStart + S.K * G.pc + targs.length + 1]? =
        some (.call h ((List.range targs.length).map fun i => .move (S.nC + S.nG + 1 + i)) S.dst
          S.next) := by
      rw [Nat.add_assoc, tail_code c hu hq (j := targs.length + 1) (by omega),
        List.getElem?_append_right (by rw [Site.assignTemps_length]; omega)]
      simp [Site.assignTemps_length]
    obtain ⟨M2, hrun, hpc2, hfid2, hfn2, hcont2, hret2, hvl2, hll2, hE2, htemp, hother⟩ :=
      run_assignTemps (D := D) (p0 := S.p') (fn0 := S.c') (ρ := ρ) (off := S.nC)
        (t := S.nC + S.nG + 1) (base := S.gStart + S.K * G.pc) (W := S.nC) (below := C :: os)
        (below' := ss) targs 0 G M b vs G1 c.hb hu' c.hI.ret' c.fnM (by rw [hpcM]; rfl) hcodeT
        c.hI.embG c.hI.fidG c.lookR (by omega) (by rw [hlenG]; omega)
        (by rw [hlenM]; simp only [Site.nT]; omega) c.hI.llen' hev
    subst e2
    have hk := foldl_kill_fields ks G
    have hI2 : InlRel S ρ (ks.foldl Frame.kill G) C M2 :=
      { fidG := by rw [hk.2.1, hfid2]; exact c.hI.fidG
        fidC := by rw [hfid2]; exact c.hI.fidC
        fnG := by rw [hk.2.2.1]; exact c.hI.fnG
        fnC := c.hI.fnC
        fnM := by rw [hfn2]; exact c.hI.fnM
        embG := hE2
        embC := c.hI.embC.transfer (by rw [hvl2]; exact Nat.le_refl _) (fun s hs => by
          have := hother s (Or.inl (by rw [hlenC] at hs; omega)) (Or.inl (by rw [hlenC] at hs; omega))
          simpa using this)
        owfG := ⟨(by rw [hk.2.2.1, hk.1]; exact c.hI.owfG.wf),
          (by rw [hk.2.2.2.2.2.2, hk.1]; exact c.hI.owfG.llen),
          (by rw [hk.2.2.2.2.2.1]; exact c.hI.owfG.ret)⟩
        owfC := c.hI.owfC
        ret' := by rw [hret2]; exact c.hI.ret'
        llen' := by rw [hll2, hvl2]; exact c.hI.llen'
        vlen' := by rw [hvl2]; exact hlenM }
    have hl : ∀ s ∈ pendingDrops S.gf (ks.foldl Frame.kill G), s < (ks.foldl Frame.kill G).vals.length :=
      fun s hs => mem_pendingDrops_lt hs
    obtain ⟨hd, hI3⟩ := hI2.dropListG _ hl false
    have hfl := filter_gslots hI2
    have st2 : step .frameReuse D S.p' { b with stack := M2 :: ss } =
        execI .frameReuse D S.p' { b with stack := M2 :: ss } S.c' M2 ss
          (.dropSlots ((List.range S.nG).reverse.map (· + S.nC))
            (S.gStart + S.K * G.pc + targs.length + 1)) :=
      step_exec rfl (by rw [hfn2]; exact c.fnM) (by simpa using hu') (by rw [hret2]; exact c.hI.ret')
        (by rw [hpc2, Nat.add_zero]; exact hcodeD)
    simp only [execI, hfl, hd] at st2
    have hfr' := dropList_frame S.c' M2
      ((pendingDrops S.gf (ks.foldl Frame.kill G)).map (· + S.nC)) false
    simp only [doTailCall]
    cases hend : (dropList S.gf (ks.foldl Frame.kill G)
        (pendingDrops S.gf (ks.foldl Frame.kill G)) false).2.2 with
    | abort =>
      rw [hend] at st2
      refine ⟨targs.length + 1, ?_⟩
      rw [run_add, hrun, run_one', st2]
      exact match_halt _ (by simp [c.hr.ev])
    | unwind =>
      rw [hend] at st2
      refine ⟨targs.length + 1, ?_⟩
      rw [run_add, hrun, run_one', st2]
      simp only [unwindBelow]
      exact c.toPlain rfl rfl hI2 (by rw [hend]; simp) hI3 id (fun h => by simp at h) rfl
        (by rw [hfr'.2.1, hfid2]) hCb.2 rfl rfl rfl (by simp [c.hr.ev])
    | ok =>
      rw [hend] at st2
      refine ⟨targs.length + 2, ?_⟩
      let M3 : Frame := { (dropList S.c' M2 ((pendingDrops S.gf (ks.foldl Frame.kill G)).map
        (· + S.nC)) false).1 with pc := S.gStart + S.K * G.pc + targs.length + 1 }
      have hM3v : M3.vals = M2.vals := by simp [M3, hfr'.1]
      have hmv : ∀ i ∈ List.range targs.length, S.nC + S.nG + 1 + i < M3.vals.length := by
        intro i hi
        rw [List.mem_range] at hi
        rw [hM3v, hvl2, hlenM]; simp only [Site.nT]; omega
      have hvals : (List.range targs.length).map (fun i => M3.get (S.nC + S.nG + 1 + i)) =
          vs.map (rv ρ) := by
        apply List.ext_getElem
        · simp [hvlen]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_range]
          have := (htemp i (by simpa using h1)).1
          rw [Nat.zero_add] at this
          unfold Frame.get at this ⊢
          rw [hM3v, this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [hvlen] using h1)]
          rfl
      have hdst : S.dst < ((List.range targs.length).map (S.nC + S.nG + 1 + ·)
          |>.foldl Frame.kill M3).vals.length := by
        rw [(foldl_kill_fields _ _).1, hM3v, hvl2, hlenM]
        have := S.hdst; simp only [Site.nC] at *; omega
      have hpc3 : M3.pc = S.gStart + S.K * G.pc + targs.length + 1 := rfl
      have hfn3 : S.p'.fns[M3.fn]? = some S.c' := by
        simp only [M3]; rw [hfr'.2.2.1, hfn2]; exact c.fnM
      have hret3 : M3.pendingRet = none := by
        simp only [M3]; rw [hfr'.2.2.2, hret2]; exact c.hI.ret'
      have st3 : ∀ ev, step .frameReuse D S.p' { b with stack := M3 :: ss, events := ev } =
          push D S.p' { b with stack := M3 :: ss, events := ev }
            ({ ((List.range targs.length).map (S.nC + S.nG + 1 + ·)).foldl Frame.kill M3 with
              cont := .store S.dst S.next } :: ss) h (vs.map (rv ρ)) := by
        intro ev
        rw [step_exec rfl hfn3 (by simpa using hu') hret3 (by rw [hpc3]; exact hcodeC)]
        simp only [execI, evalOps_moves ss _ _ M3 hmv, hvals, hdst, ↓reduceIte]
      rw [run_add .frameReuse D S.p' targs.length 2, hrun, run_succ, st2, run_one', st3]
      apply match_bump_left
      have hM4 := foldl_kill_fields ((List.range targs.length).map (S.nC + S.nG + 1 + ·)) M3
      have hI4 : InlRel S ρ (dropList S.gf (ks.foldl Frame.kill G)
          (pendingDrops S.gf (ks.foldl Frame.kill G)) false).1 C
          { ((List.range targs.length).map (S.nC + S.nG + 1 + ·)).foldl Frame.kill M3 with
            cont := .store S.dst S.next } :=
        (InlRel.killsT _ (hI3.congr (C1 := C) (M1 := M3) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl) (fun x hx => by
            simp only [List.mem_map, List.mem_range] at hx
            obtain ⟨i, -, rfl⟩ := hx; omega)).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl
      have hP4 := plain_after_drop hI2 (by rw [hend]; simp) hI4
      have hdC : S.dst < C.vals.length := by rw [hlenC]; exact S.hdst
      have hfidM4 : ({ ((List.range targs.length).map (S.nC + S.nG + 1 + ·)).foldl Frame.kill M3 with
          cont := .store S.dst S.next } : Frame).fid = M.fid := by
        simp only; rw [hM4.2.1]; simp only [M3]; rw [hfr'.2.1, hfid2]
      refine match_push (Below.plain hP4 (by rw [c.hc]) ⟨S.dst, S.next, c.hc, hdC⟩ c.hB) ?_ ?_ ?_ hvs
        (by simp [c.hr.ev]) (by simp [hu]) (by simp [hu'])
      · exact fun X hX => c.bA X (List.mem_cons_of_mem _ hX)
      · exact fresh_head c.bB hfidM4
      · exact pairwise_head c.pw hfidM4

end

end Toy.TailCall.SpliceProof
