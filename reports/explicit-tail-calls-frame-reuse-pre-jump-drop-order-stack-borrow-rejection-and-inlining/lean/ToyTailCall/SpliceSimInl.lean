import ToyTailCall.SpliceLoop

/-!
# Proof support: steps of a merged running frame (the spliced callee)
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}

/-- Facts available about a related pair whose original running frame is a spliced callee. -/
structure InlCtx (S : Site) (ρ : Nat → Nat × Nat) (a b : State) (G C M : Frame)
    (os ss : List Frame) : Prop where
  hr : RelAt S ρ a b
  ha : a.stack = G :: C :: os
  hb : b.stack = M :: ss
  hI : InlRel S ρ G C M
  hc : C.cont = .store S.dst S.next
  hpc : a.unwinding = false → M.pc = S.gStart + S.K * G.pc
  hB : Below S ρ os ss

variable {a b : State} {G C M : Frame} {os ss : List Frame}

theorem InlCtx.bA (c : InlCtx S ρ a b G C M os ss) : ∀ X ∈ G :: C :: os, Bounded a.nextFid X := by
  rw [← c.ha]; exact c.hr.freshA

theorem InlCtx.bB (c : InlCtx S ρ a b G C M os ss) : ∀ Y ∈ M :: ss, Y.fid < b.nextFid := by
  rw [← c.hb]; exact c.hr.freshB

theorem InlCtx.pw (c : InlCtx S ρ a b G C M os ss) :
    (M :: ss).Pairwise (fun x y => y.fid < x.fid) := by
  rw [← c.hb]; exact c.hr.orderB

theorem InlCtx.lookR (c : InlCtx S ρ a b G C M os ss) (M1 : Frame) (hf : M1.fid = M.fid)
    (hl : M1.vals.length = M.vals.length) (hg : ∀ j, j < S.nC → M1.get j = M.get j) :
    Look ρ (C :: os) M1 ss := by
  have hpw := List.pairwise_cons.mp c.pw
  refine look_inl c.hB hpw.2 (fun Y hY => by rw [hf]; exact hpw.1 Y hY) (by rw [hf]; exact c.hI.fidC)
    ⟨by rw [hl]; exact c.hI.embC.len, fun j hj => ?_⟩
  have hj' : j < S.nC := by rw [c.hI.lenC] at hj; exact hj
  simp only [Nat.add_zero]
  rw [hg j hj']
  have := c.hI.embC.get j hj
  simpa using this

theorem InlCtx.look (c : InlCtx S ρ a b G C M os ss) : Look ρ (C :: os) M ss :=
  c.lookR M rfl rfl (fun _ _ => rfl)

theorem InlCtx.fnG (c : InlCtx S ρ a b G C M os ss) : S.p.fns[G.fn]? = some S.gf := by
  rw [c.hI.fnG]; exact S.hg

theorem InlCtx.fnC (c : InlCtx S ρ a b G C M os ss) : S.p.fns[C.fn]? = some S.c := by
  rw [c.hI.fnC]; exact S.hc

theorem InlCtx.fnM (c : InlCtx S ρ a b G C M os ss) : S.p'.fns[M.fn]? = some S.c' := by
  rw [c.hI.fnM]; exact S.p'_ci

theorem InlCtx.vals (c : InlCtx S ρ a b G C M os ss) :
    ∀ X ∈ G :: C :: os, ∀ w ∈ X.vals, PtrLt a.nextFid w :=
  fun X hX => (c.bA X hX).2

theorem InlCtx.code (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = false) {i : Instr}
    (hq : S.gf.code[G.pc]? = some i) {r : Nat}
    (hr : r < (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc i).length) :
    S.c'.code[M.pc + r]? = (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc i)[r]? := by
  rw [c.hpc hu]; exact S.code_body hq hr

theorem InlCtx.code0 (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = false) {i : Instr}
    (hq : S.gf.code[G.pc]? = some i) {j : Instr}
    (h0 : (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc i)[0]? = some j) :
    S.c'.code[M.pc]? = some j := by
  have hr : 0 < (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc i).length := by
    cases hl : (spliceInstr .corrected S.nC S.nG S.gStart S.K S.dst S.next G.pc i) with
    | nil => rw [hl] at h0; simp at h0
    | cons _ _ => simp
  have := c.code hu hq hr
  rw [Nat.add_zero] at this
  rw [this, h0]

/-- A local update of the merged running frame. -/
theorem InlCtx.local (c : InlCtx S ρ a b G C M os ss) {a' b' : State} {G1 C1 M1 : Frame}
    (ha' : a'.stack = G1 :: C1 :: os) (hb' : b'.stack = M1 :: ss) (hI1 : InlRel S ρ G1 C1 M1)
    (hc1 : C1.cont = .store S.dst S.next)
    (hpc : a'.unwinding = false → M1.pc = S.gStart + S.K * G1.pc)
    (hfG : G1.fid = G.fid) (hfC : C1.fid = C.fid) (hfM : M1.fid = M.fid)
    (hvG : ∀ v ∈ G1.vals, PtrLt a.nextFid v) (hvC : C1.vals = C.vals) (hn : a'.nextFid = a.nextFid)
    (hn' : b'.nextFid = b.nextFid) (hu : b'.unwinding = a'.unwinding) (he : b'.events = a'.events) :
    Match S (.running a') (.running b') := by
  refine match_running (relAt_inl hI1 hc1 hpc c.hB ha' hb' ?_ ?_ ?_ hu he)
  · rw [hn]
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact ⟨by rw [hfG]; exact (c.bA G (List.mem_cons_self ..)).1, hvG⟩
    · exact bounded_head (fun Y hY => c.bA Y (List.mem_cons_of_mem _ hY))
        ((c.bA C (List.mem_cons_of_mem _ (List.mem_cons_self ..))).congr hfC hvC) X hX
  · rw [hn']; exact fresh_head c.bB hfM
  · exact pairwise_head c.pw hfM

theorem InlRel.killOf {G C M : Frame} (h : InlRel S ρ G C M) (o : Operand)
    (ho : ∀ s, o = .move s → s < G.vals.length) :
    InlRel S ρ (Toy.TailCall.SpliceProof.killOf 0 o G) C (Toy.TailCall.SpliceProof.killOf S.nC o M) := by
  cases o with
  | move s => exact h.killG (ho s rfl)
  | _ => exact h

theorem lt_mid {d nG nC nT : Nat} (h : d < nG) : d + nC < nC + nG + nT := by omega

theorem ite_pc (p : Prop) [Decidable p] (g K t e : Nat) :
    (if p then g + K * t else g + K * e) = g + K * (if p then t else e) := by
  by_cases h : p <;> simp [h]

/-- The one-step instructions of a spliced callee. -/
theorem sim_inl_simple {D : Option Nat} (c : InlCtx S ρ a b G C M os ss) (hu : a.unwinding = false)
    {i : Instr} (hq : S.gf.code[G.pc]? = some i)
    (hi : ∀ op, i ≠ .ret op) (hi' : ∀ h as, i ≠ .tailCall h as) :
    Match S (step .frameReuse D S.p a) (step .frameReuse D S.p' b) := by
  have hu' : b.unwinding = false := by rw [c.hr.uw, hu]
  have hGb := c.bA G (List.mem_cons_self ..)
  have hlenG := c.hI.lenG
  have hlenM := c.hI.vlen'
  rw [step_exec c.ha c.fnG hu c.hI.owfG.ret hq]
  cases i with
  | assign d op n =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    cases hev : evalOp (C :: os) G op with
    | none => exact match_ub a
    | some vf =>
      obtain ⟨v, G1⟩ := vf
      obtain ⟨e1, e2⟩ := evalOp_sim c.hI.embG c.hI.fidG c.look hev
      have hv := evalOp_ptrLt hGb.1 c.vals hev
      have ho : ∀ s, op = .move s → s < G.vals.length := by
        intro s hs; subst hs; exact evalOp_move_lt hev
      simp only [e1]
      subst e2
      by_cases hd : d < (killOf 0 op G).vals.length
      · have hd' : d + S.nC < (killOf S.nC op M).vals.length := by
          simp only [killOf_vals] at hd ⊢; rw [hlenG] at hd; rw [hlenM]; exact lt_mid hd
        simp only [hd, hd', ↓reduceIte]
        refine c.local rfl rfl (((c.hI.killOf op ho).writeG hd v).congr rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) c.hc (fun _ => rfl) (by simp) rfl (by simp)
          ?_ rfl rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
        intro w hw
        rcases write_vals _ d v w hw with hw | rfl
        · simp only [killOf_vals] at hw; exact hGb.2 w hw
        · exact hv
      · simp only [hd, ↓reduceIte]; exact match_ub a
  | emit k n =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    exact c.local rfl rfl (c.hI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
      c.hc (fun _ => rfl) rfl rfl rfl hGb.2 rfl rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
  | branchLt s k t e =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    cases hget : G.get s with
    | int n =>
      have hs : s < G.vals.length := by
        rcases Nat.lt_or_ge s G.vals.length with hs | hs
        · exact hs
        · rw [get_of_ge G hs] at hget; cases hget
      have hget' : M.get (s + S.nC) = .int n := by
        rw [c.hI.embG.get s hs, hget]; rfl
      simp only [hget']
      exact c.local rfl rfl (c.hI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        c.hc (fun _ => ite_pc _ _ _ _ _) rfl rfl rfl hGb.2 rfl rfl rfl (by simp [hu, hu'])
        (by simp [c.hr.ev])
    | ptr x y => exact match_ub a
    | undef => exact match_ub a
  | goto n =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    exact c.local rfl rfl (c.hI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
      c.hc (fun _ => rfl) rfl rfl rfl hGb.2 rfl rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
  | reset rs n =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    have hf := foldl_clear_fields rs G
    have hf' := foldl_clear_fields (rs.map (· + S.nC)) M
    refine c.local rfl rfl ((c.hI.clearsG rs).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl) c.hc (fun _ => rfl) hf.1 rfl hf'.1 ?_ rfl rfl rfl (by simp [hu, hu'])
      (by simp [c.hr.ev])
    intro w hw
    rcases (foldl_clear_frame rs G).2.2.2.2.1 w hw with hw | rfl
    · exact hGb.2 w hw
    · trivial
  | dropSlots ds n =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI, filter_renamed c.hI ds]
    have hl : ∀ s ∈ ds.filter (fun s => G.isLive s && S.gf.dtor s != .none), s < G.vals.length :=
      fun s hs => filter_lt c.hI.owfG.llen hs
    obtain ⟨hd, hI1⟩ := c.hI.dropListG _ hl false
    simp only [hd]
    have hfr := dropList_frame S.gf G (ds.filter (fun s => G.isLive s && S.gf.dtor s != .none)) false
    have hfr' := dropList_frame S.c' M
      ((ds.filter (fun s => G.isLive s && S.gf.dtor s != .none)).map (· + S.nC)) false
    cases (dropList S.gf G (ds.filter (fun s => G.isLive s && S.gf.dtor s != .none)) false).2.2 with
    | ok =>
      exact c.local rfl rfl (hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        c.hc (fun _ => rfl) hfr.2.1 rfl hfr'.2.1 (by rw [hfr.1]; exact hGb.2) rfl rfl rfl
        (by simp [hu, hu']) (by simp [c.hr.ev])
    | unwind =>
      exact c.local rfl rfl hI1 c.hc (fun h => by simp at h) hfr.2.1 rfl hfr'.2.1
        (by rw [hfr.1]; exact hGb.2) rfl rfl rfl rfl (by simp [c.hr.ev])
    | abort => exact match_halt _ (by simp [c.hr.ev])
  | call f args d n =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    cases hev : evalOps (C :: os) G args with
    | none => exact match_ub a
    | some vf =>
      obtain ⟨vs, G1⟩ := vf
      obtain ⟨ks, hks, e2, e1⟩ := evalOps_sim args G M vs G1 c.hI.embG c.hI.fidG c.look hev
      have hvs := evalOps_ptrLt args G vs G1 hGb.1 c.vals hev
      simp only [e1]
      subst e2
      have hk := foldl_kill_fields ks G
      have hk' := foldl_kill_fields (ks.map (· + S.nC)) M
      by_cases hd : d < (ks.foldl Frame.kill G).vals.length
      · have hd' : d + S.nC < ((ks.map (· + S.nC)).foldl Frame.kill M).vals.length := by
          rw [hk.1, hlenG] at hd; rw [hk'.1, hlenM]; exact lt_mid hd
        simp only [hd, hd', ↓reduceIte]
        refine match_push (ρ := ρ) (Below.inl
          ((c.hI.killsG ks hks).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
          c.hc ⟨d, n, rfl, hd⟩ rfl c.hB) ?_ ?_ ?_ hvs c.hr.ev hu hu'
        · exact bounded_head c.bA (hGb.congr hk.2.1 hk.1)
        · exact fresh_head c.bB hk'.2.1
        · exact pairwise_head c.pw hk'.2.1
      · simp only [hd, ↓reduceIte]; exact match_ub a
  | ret op => exact absurd rfl (hi op)
  | tailCall h as => exact absurd rfl (hi' h as)
  | panic =>
    rw [step_exec c.hb c.fnM hu' c.hI.ret' (c.code0 hu hq rfl)]
    simp only [execI]
    exact c.local c.ha c.hb c.hI c.hc (fun h => by simp at h) rfl rfl rfl hGb.2 rfl rfl rfl
      (by simp [hu, hu']) (by simp [c.hr.ev])

end

end Toy.TailCall.SpliceProof
