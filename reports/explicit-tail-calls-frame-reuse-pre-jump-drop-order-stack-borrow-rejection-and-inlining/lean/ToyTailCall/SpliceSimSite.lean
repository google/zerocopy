import ToyTailCall.SpliceSimTail

/-!
# Proof support: entering the spliced callee at the call site
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}
variable {a b : State} {F F' : Frame} {os ss : List Frame}

theorem sim_site {D : Option Nat} (c : PlainCtx S ρ a b F F' os ss) (hpc : F'.pc = F.pc)
    (hci : F.fn = S.ci) (hk : F.pc = S.k) (hu : a.unwinding = false) :
    ∃ m, Match S (step .frameReuse D S.p a) (run .frameReuse D S.p' m (.running b)) := by
  have hu' : b.unwinding = false := by rw [c.hr.uw, hu]
  have hfn : S.p.fns[F.fn]? = some S.c := by rw [hci]; exact S.hc
  have hcode : S.c.code[F.pc]? = some (.call S.g S.args S.dst S.next) := by rw [hk]; exact S.hk
  have hFb := c.bA F (List.mem_cons_self ..)
  have hFlen : F.vals.length = S.nC := by
    obtain ⟨fn, h1, h2⟩ := c.hP.owf.wf
    rw [hfn] at h1; cases h1; exact h2
  have hfn' : S.p'.fns[F'.fn]? = some S.c' := by rw [c.hP.fn, hci]; exact S.p'_ci
  have hF'len : F'.vals.length = S.nC + S.nG + S.nT := by
    obtain ⟨fn', h1, h2⟩ := c.hP.wf'
    rw [hfn'] at h1; cases h1; rw [h2, S.c'_nSlots]
  rw [step_exec c.ha hfn hu c.hP.owf.ret hcode]
  simp only [execI]
  cases hev : evalOps os F S.args with
  | none => exact ⟨0, match_ub a⟩
  | some vf =>
    obtain ⟨vs, F1⟩ := vf
    obtain ⟨ks, e2, -, hvs⟩ := c.evalOps hev
    have hvlen := evalOps_length S.args F vs F1 hev
    subst e2
    have hk1 := foldl_kill_fields ks F
    have hd : S.dst < (ks.foldl Frame.kill F).vals.length := by rw [hk1.1, hFlen]; exact S.hdst
    simp only [hd, ↓reduceIte]
    unfold push
    rw [S.hg]
    simp only
    have hnp := S.hlen
    have hpar := S.hpar
    have hnG : S.nG = S.gf.nSlots := rfl
    have hbad : ¬ (vs.length != S.gf.nParams || decide (S.gf.nSlots < S.gf.nParams)) = true := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, Classical.not_not,
        Nat.not_lt]
      omega
    simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    cases hov : overflows D ({ ks.foldl Frame.kill F with cont := .store S.dst S.next } :: os).length with
    | true => simp only [↓reduceIte]; exact ⟨0, match_so a⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨2 + S.args.length, ?_⟩
      -- the two prologue steps
      have st1 : step .frameReuse D S.p' b = .running { b with stack := { F' with pc := S.L } :: ss } := by
        rw [step_exec c.hb hfn' hu' c.hP.ret' (by rw [hpc, hk]; exact S.code_k)]
        rfl
      let R : List Nat := (List.range (S.nG + S.nT)).map (· + S.nC)
      let M0 : Frame := { R.foldl Frame.clear { F' with pc := S.L } with pc := S.L + 1 }
      have hM0 := foldl_clear_fields R { F' with pc := S.L }
      have st2 : step .frameReuse D S.p' { b with stack := { F' with pc := S.L } :: ss } =
          .running { b with stack := M0 :: ss } := by
        rw [step_exec rfl (by simpa using hfn') (by simpa using hu') (by simpa using c.hP.ret')
          (by simpa using S.code_L)]
        rfl
      have hM0fid : M0.fid = F'.fid := by simp only [M0]; rw [hM0.1]
      have hM0len : M0.vals.length = S.nC + S.nG + S.nT := by
        simp only [M0]; rw [hM0.2.2.2.2.2.1]; exact hF'len
      have hM0ll : M0.live.length = M0.vals.length := by
        simp only [M0]; rw [hM0.2.2.2.2.2.2, hM0.2.2.2.2.2.1]; exact c.hP.llen'
      have hE0 : Emb ρ 0 F M0 :=
        (Emb.foldl_clear_out R _ (c.hP.emb.congr rfl rfl (M' := { F' with pc := S.L }) rfl rfl) (fun t ht => by
          simp only [R, List.mem_map, List.mem_range] at ht
          obtain ⟨x, -, rfl⟩ := ht
          right; rw [hFlen]; omega)).congr rfl rfl rfl rfl
      have hpw := List.pairwise_cons.mp c.pw
      obtain ⟨M2, hrun, hpc2, hfid2, hfn2, hcont2, hret2, hvl2, hll2, hE2, htemp, hother⟩ :=
        run_assignTemps (D := D) (p0 := S.p') (fn0 := S.c') (ρ := ρ) (off := 0) (t := S.nC)
          (base := S.L + 1) (W := 0) (below := os) (below' := ss) S.args 0 F M0
          { b with stack := M0 :: ss } vs (ks.foldl Frame.kill F) rfl (by simpa using hu')
          (by simp only [M0]; rw [hM0.2.2.2.2.1]; exact c.hP.ret')
          (by simp only [M0]; rw [hM0.2.1]; exact hfn') rfl
          (fun j hj => by
            have := S.code_pro hj
            simp only [Nat.zero_add] at this ⊢
            exact this)
          hE0 (by rw [hM0fid]; exact c.hP.fid)
          (fun M1 hf _ _ => look_plain c.hB hpw.2 (fun Y hY => by rw [hf, hM0fid]; exact hpw.1 Y hY))
          (Nat.zero_le _) (by rw [hFlen]; omega) (by rw [hM0len]; simp only [Site.nG] at *; omega)
          hM0ll hev
      rw [run_add .frameReuse D S.p' 2 S.args.length, run_succ, st1, run_succ, st2,
        show run .frameReuse D S.p' 0 (.running { b with stack := M0 :: ss }) =
          .running { b with stack := M0 :: ss } from rfl, hrun]
      -- the new renaming
      let ρ' : Nat → Nat × Nat := fun x => if x = a.nextFid then (F'.fid, S.nC) else ρ x
      have hρ' : ∀ x, x < a.nextFid → ρ' x = ρ x := by
        intro x hx; simp only [ρ', Nat.ne_of_lt hx, ↓reduceIte]
      have hbOs : ∀ X ∈ os, Bounded a.nextFid X := fun X hX => c.bA X (List.mem_cons_of_mem _ hX)
      have hgetM0 : ∀ s, s < S.nG → M0.get (s + S.nC) = .undef ∧ M0.isLive (s + S.nC) = false := by
        intro s hs
        have hmem : s + S.nC ∈ R := by
          simp only [R, List.mem_map, List.mem_range]; exact ⟨s, by omega, rfl⟩
        constructor
        · change (R.foldl Frame.clear { F' with pc := S.L }).get (s + S.nC) = _
          rw [foldl_clear_get]; simp [hmem]
        · change (R.foldl Frame.clear { F' with pc := S.L }).isLive (s + S.nC) = _
          rw [foldl_clear_isLive]; simp [hmem]
      have hvsρ : ∀ s, rv ρ' (vs.getD s .undef) = rv ρ (vs.getD s .undef) := by
        intro s
        refine rv_congr hρ' ?_
        rcases get_cases ⟨0, 0, 0, vs, [], .thenReturn, none⟩ s with hm | he
        · exact hvs _ hm
        · simp only [Frame.get] at he; rw [he]; trivial
      have hembG : Emb ρ' S.nC (⟨a.nextFid, S.g, 0,
          vs ++ List.replicate (S.gf.nSlots - S.gf.nParams) .undef,
          List.replicate S.gf.nParams true ++ List.replicate (S.gf.nSlots - S.gf.nParams) false,
          .thenReturn, none⟩ : Frame) M2 := by
        refine ⟨by simp; rw [hvl2, hM0len]; omega, fun s hs => ?_, fun s hs => ?_⟩
        · simp only [List.length_append, List.length_replicate] at hs
          simp only [Frame.get, getD_append_replicate]
          by_cases hsa : s < S.args.length
          · have := (htemp s hsa).1
            rw [show S.nC + (0 + s) = s + S.nC by omega] at this
            unfold Frame.get at this
            rw [this, hvsρ]
          · have h1 := hother (s + S.nC) (Or.inr (by rw [hFlen]; omega)) (Or.inr (by omega))
            unfold Frame.get at h1
            rw [h1.1]
            have h2 := (hgetM0 s (by omega)).1
            unfold Frame.get at h2
            rw [h2, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            rfl
        · simp only [List.length_append, List.length_replicate] at hs
          simp only [Frame.isLive, getD_append_replicate, getD_replicate]
          by_cases hsa : s < S.args.length
          · have := (htemp s hsa).2
            rw [show S.nC + (0 + s) = s + S.nC by omega] at this
            unfold Frame.isLive at this
            rw [this]; simp; omega
          · have h1 := hother (s + S.nC) (Or.inr (by rw [hFlen]; omega)) (Or.inr (by omega))
            unfold Frame.isLive at h1
            rw [h1.2]
            have h2 := (hgetM0 s (by omega)).2
            unfold Frame.isLive at h2
            rw [h2]; simp; omega
      have hI : InlRel S ρ' ⟨a.nextFid, S.g, 0, vs ++ List.replicate (S.gf.nSlots - S.gf.nParams) .undef,
          List.replicate S.gf.nParams true ++ List.replicate (S.gf.nSlots - S.gf.nParams) false,
          .thenReturn, none⟩ { ks.foldl Frame.kill F with cont := .store S.dst S.next } M2 :=
        { fidG := by simp only [ρ', ↓reduceIte, hfid2, hM0fid]
          fidC := by
            show ρ' (ks.foldl Frame.kill F).fid = _
            rw [hk1.2.1, hρ' _ hFb.1, c.hP.fid, hfid2, hM0fid]
          fnG := rfl
          fnC := by show (ks.foldl Frame.kill F).fn = _; rw [hk1.2.2.1, hci]
          fnM := by rw [hfn2]; simp only [M0]; rw [hM0.2.1]; rw [c.hP.fn, hci]
          embG := hembG
          embC := ((hE2.congr_rho hρ' (by rw [hk1.1]; exact hFb.2)).congr rfl rfl rfl rfl)
          owfG := ⟨⟨S.gf, S.hg, by simp; omega⟩, by simp; omega, rfl⟩
          owfC := ⟨by show ∃ fn, _ ∧ (ks.foldl Frame.kill F).vals.length = _
                      rw [hk1.2.2.1, hk1.1]; exact c.hP.owf.wf,
                    by show (ks.foldl Frame.kill F).live.length = (ks.foldl Frame.kill F).vals.length
                       rw [hk1.2.2.2.2.2.2, hk1.1]; exact c.hP.owf.llen,
                    by show (ks.foldl Frame.kill F).pendingRet = none
                       rw [hk1.2.2.2.2.2.1]; exact c.hP.owf.ret⟩
          ret' := by rw [hret2]; simp only [M0]; rw [hM0.2.2.2.2.1]; exact c.hP.ret'
          llen' := by rw [hll2, hvl2]; exact hM0ll
          vlen' := by rw [hvl2]; exact hM0len }
      refine match_running (relAt_inl hI rfl (fun _ => ?_) (c.hB.congr_rho hρ' hbOs) rfl rfl ?_ ?_ ?_
        (by simp [hu, hu']) (by simp [c.hr.ev]))
      · rw [hpc2]; simp [Site.gStart]
      · intro X hX
        simp only [List.mem_cons] at hX
        rcases hX with rfl | rfl | hX
        · refine ⟨by simp, fun v hv => ?_⟩
          simp only [List.mem_append] at hv
          rcases hv with hv | hv
          · exact ptrLt_mono (Nat.le_succ _) (hvs v hv)
          · rw [List.eq_of_mem_replicate hv]; trivial
        · exact (hFb.congr hk1.2.1 hk1.1).mono (Nat.le_succ _)
        · exact (hbOs X hX).mono (Nat.le_succ _)
      · exact fresh_head c.bB (by rw [hfid2, hM0fid])
      · exact pairwise_head c.pw (by rw [hfid2, hM0fid])

end

end Toy.TailCall.SpliceProof
