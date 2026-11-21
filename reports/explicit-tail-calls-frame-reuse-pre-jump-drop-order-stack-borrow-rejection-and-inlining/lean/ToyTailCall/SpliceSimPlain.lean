import ToyTailCall.SpliceStep

/-!
# Proof support: step matching for a plain running frame
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}


theorem filter_lt {fn : Fn} {F : Frame} (hl : F.live.length = F.vals.length) {ss : List Nat}
    {s : Nat} (h : s ∈ ss.filter (fun s => F.isLive s && fn.dtor s != .none)) :
    s < F.vals.length := by
  rw [List.mem_filter] at h
  rcases Nat.lt_or_ge s F.vals.length with hs | hs
  · exact hs
  · rw [isLive_of_ge F (by rw [hl]; exact hs)] at h
    simp at h

theorem sim_instr {D : Option Nat} {a b : State} {F F' : Frame} {os ss : List Frame} {fn : Fn}
    (c : PlainCtx S ρ a b F F' os ss) (hfn : S.p.fns[F.fn]? = some fn)
    (hu : a.unwinding = false) (hu' : b.unwinding = false) (i : Instr) :
    Match S (execI .frameReuse D S.p a fn F os i)
      (execI .frameReuse D S.p' b (S.fnS F.fn fn) F' ss i) := by
  have hFb := c.bA F (List.mem_cons_self ..)
  have hbA : ∀ X ∈ os, Bounded a.nextFid X := fun X hX => c.bA X (List.mem_cons_of_mem _ hX)
  have hbB : ∀ Y ∈ ss, Y.fid < b.nextFid := fun Y hY => c.bB Y (List.mem_cons_of_mem _ hY)
  have hpw := (List.pairwise_cons.mp c.pw).2
  have hlen : F.vals.length ≤ F'.vals.length := Nat.le_trans (Nat.le_add_right _ 0) c.hP.emb.len
  cases i with
  | assign dst op next =>
    simp only [execI]
    cases hev : evalOp os F op with
    | none => exact match_ub a
    | some vf =>
      obtain ⟨v, F1⟩ := vf
      obtain ⟨e1, e2, hv⟩ := c.evalOp hev
      simp only [e1]
      subst e2
      by_cases hd : dst < (killOf 0 op F).vals.length
      · have hd' : dst < (killOf 0 op F').vals.length := by
          simp only [killOf_vals] at hd ⊢; exact Nat.lt_of_lt_of_le hd hlen
        simp only [hd, hd', ↓reduceIte]
        refine c.local rfl rfl (((c.hP.killOf op).write hd v).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
          (fun _ => rfl) (by simp) (by simp) ?_ rfl rfl (by simp [hu, hu'])
          (by simp [c.hr.ev])
        intro w hw
        rcases write_vals _ dst v w hw with hw | rfl
        · simp only [killOf_vals] at hw; exact hFb.2 w hw
        · exact hv
      · simp only [hd, ↓reduceIte]; exact match_ub a
  | emit k next =>
    simp only [execI]
    exact c.local rfl rfl (c.hP.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (fun _ => rfl) rfl rfl
      hFb.2 rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
  | branchLt s k t e =>
    simp only [execI]
    cases hget : F.get s with
    | int n =>
      have hs : s < F.vals.length := by
        rcases Nat.lt_or_ge s F.vals.length with hs | hs
        · exact hs
        · rw [get_of_ge F hs] at hget; cases hget
      have hget' : F'.get s = .int n := by
        have := c.hP.emb.get s hs
        simp only [Nat.add_zero] at this
        rw [this, hget]; rfl
      simp only [hget']
      exact c.local rfl rfl (c.hP.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (fun _ => rfl) rfl rfl
        hFb.2 rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
    | ptr x y => exact match_ub a
    | undef => exact match_ub a
  | goto next =>
    simp only [execI]
    exact c.local rfl rfl (c.hP.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (fun _ => rfl) rfl rfl
      hFb.2 rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
  | reset rs next =>
    simp only [execI]
    have hf := foldl_clear_fields rs F
    have hf' := foldl_clear_fields rs F'
    refine c.local rfl rfl ((c.hP.clears rs).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (fun _ => rfl)
      hf.1 hf'.1 ?_ rfl rfl (by simp [hu, hu']) (by simp [c.hr.ev])
    intro w hw
    rcases (foldl_clear_frame rs F).2.2.2.2.1 w hw with hw | rfl
    · exact hFb.2 w hw
    · trivial
  | dropSlots ds next =>
    simp only [execI, c.hP.filter hfn ds]
    have hl : ∀ s ∈ ds.filter (fun s => F.isLive s && fn.dtor s != .none), s < F.vals.length :=
      fun s hs => filter_lt c.hP.owf.llen hs
    obtain ⟨hd, hP1⟩ := c.hP.dropList hfn _ hl false
    simp only [hd]
    have hfr := dropList_frame fn F (ds.filter (fun s => F.isLive s && fn.dtor s != .none)) false
    have hfr' := dropList_frame (S.fnS F.fn fn) F'
      (ds.filter (fun s => F.isLive s && fn.dtor s != .none)) false
    cases (dropList fn F (ds.filter (fun s => F.isLive s && fn.dtor s != .none)) false).2.2 with
    | ok =>
      exact c.local rfl rfl (hP1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (fun _ => rfl)
        hfr.2.1 hfr'.2.1 (by rw [hfr.1]; exact hFb.2) rfl rfl (by simp [hu, hu'])
        (by simp [c.hr.ev])
    | unwind =>
      exact c.local rfl rfl hP1 (fun h => by simp at h) hfr.2.1 hfr'.2.1 (by rw [hfr.1]; exact hFb.2)
        rfl rfl rfl (by simp [c.hr.ev])
    | abort => exact match_halt _ (by simp [c.hr.ev])
  | call f args dst next =>
    simp only [execI]
    cases hev : evalOps os F args with
    | none => exact match_ub a
    | some vf =>
      obtain ⟨vs, F1⟩ := vf
      obtain ⟨ks, e2, e1, hvs⟩ := c.evalOps hev
      simp only [e1]
      subst e2
      have hk := foldl_kill_fields ks F
      have hk' := foldl_kill_fields ks F'
      by_cases hd : dst < (ks.foldl Frame.kill F).vals.length
      · have hd' : dst < (ks.foldl Frame.kill F').vals.length := by
          rw [hk.1] at hd; rw [hk'.1]; exact Nat.lt_of_lt_of_le hd hlen
        simp only [hd, hd', ↓reduceIte]
        refine match_push (ρ := ρ) (Below.plain
          ((c.hP.kills ks).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) rfl ⟨dst, next, rfl, hd⟩ c.hB)
          ?_ ?_ ?_ hvs c.hr.ev hu hu'
        · exact bounded_head c.bA (hFb.congr hk.2.1 hk.1)
        · exact fresh_head c.bB hk'.2.1
        · exact pairwise_head c.pw hk'.2.1
      · simp only [hd, ↓reduceIte]; exact match_ub a
  | ret op =>
    simp only [execI]
    cases hev : evalOp os F op with
    | none => exact match_ub a
    | some vf =>
      obtain ⟨v, F1⟩ := vf
      obtain ⟨e1, e2, hv⟩ := c.evalOp hev
      simp only [e1]
      subst e2
      have hfn1 : S.p.fns[(killOf 0 op F).fn]? = some fn := by simpa using hfn
      have h := c.doReturn hfn1 (c.hP.killOf op) hv hu
      simp only [killOf_fn] at h
      exact h
  | tailCall f args =>
    simp only [execI]
    cases hev : evalOps os F args with
    | none => exact match_ub a
    | some vf =>
      obtain ⟨vs, F1⟩ := vf
      obtain ⟨ks, e2, e1, hvs⟩ := c.evalOps hev
      simp only [e1]
      subst e2
      have hk := foldl_kill_fields ks F
      have hP1 := c.hP.kills ks
      have hfn1 : S.p.fns[(ks.foldl Frame.kill F).fn]? = some fn := by rw [hk.2.2.1]; exact hfn
      have hl : ∀ s ∈ pendingDrops fn (ks.foldl Frame.kill F), s < (ks.foldl Frame.kill F).vals.length :=
        fun s hs => mem_pendingDrops_lt hs
      have hpd := hP1.pending hfn1
      obtain ⟨hd, -⟩ := hP1.dropList hfn1 _ hl false
      rw [hk.2.2.1] at hpd hd
      simp only [doTailCall, hpd, hd]
      cases (dropList fn (ks.foldl Frame.kill F) (pendingDrops fn (ks.foldl Frame.kill F)) false).2.2 with
      | ok => exact match_bump (match_push c.hB hbA hbB hpw hvs (by simp [c.hr.ev]) hu hu')
      | unwind => exact match_unwindBelow c.hB hbA hbB hpw (by simp [c.hr.ev])
      | abort => exact match_halt _ (by simp [c.hr.ev])
  | panic =>
    simp only [execI]
    exact c.local c.ha c.hb c.hP (fun h => by simp at h) rfl rfl hFb.2 rfl rfl (by simp [hu, hu'])
      (by simp [c.hr.ev])

/-- A plain running frame not at the splice site steps in lockstep. -/
theorem sim_plain {D : Option Nat} {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) (hpc : a.unwinding = false → F'.pc = F.pc)
    (hnot : F.fn = S.ci → a.unwinding = false → F.pc ≠ S.k) :
    Match S (step .frameReuse D S.p a) (step .frameReuse D S.p' b) := by
  cases hfn : S.p.fns[F.fn]? with
  | none => rw [step_fn_none c.ha hfn]; exact match_ub a
  | some fn =>
    have hfn' : S.p'.fns[F'.fn]? = some (S.fnS F.fn fn) := c.hP.fnS hfn
    cases hu : a.unwinding with
    | true =>
      have hu' : b.unwinding = true := by rw [c.hr.uw, hu]
      rw [step_unw c.ha hfn hu, step_unw c.hb hfn' hu']
      have hl : ∀ s ∈ pendingDrops fn F, s < F.vals.length := fun s hs => mem_pendingDrops_lt hs
      refine match_unwStep (ρ := ρ) ?_ c.hB (fun X hX => c.bA X (List.mem_cons_of_mem _ hX))
        (fun Y hY => c.bB Y (List.mem_cons_of_mem _ hY)) (List.pairwise_cons.mp c.pw).2 c.hr.ev hu hu'
      rw [c.hP.pending hfn]
      exact (c.hP.dropList hfn _ hl true).1
    | false =>
      have hu' : b.unwinding = false := by rw [c.hr.uw, hu]
      have hpc' := hpc hu
      cases hc : fn.code[F.pc]? with
      | none => rw [step_code_none c.ha hfn hu c.hP.owf.ret hc]; exact match_ub a
      | some i =>
        have hc' : (S.fnS F.fn fn).code[F'.pc]? = some i := by
          rw [hpc']
          by_cases hci : F.fn = S.ci
          · have hfc : fn = S.c := S.fn_ci (by rw [← hci]; exact hfn)
            simp only [Site.fnS, hci, ↓reduceIte]
            subst hfc
            have hlt : F.pc < S.L := by
              have := hc
              rw [List.getElem?_eq_some_iff] at this
              exact this.1
            rw [S.code_lt hlt (hnot hci hu)]
            exact hc
          · simp only [Site.fnS, hci, ↓reduceIte]
            exact hc
        rw [step_exec c.ha hfn hu c.hP.owf.ret hc, step_exec c.hb hfn' hu' c.hP.ret' hc']
        exact sim_instr c hfn hu hu' i

end

end Toy.TailCall.SpliceProof
