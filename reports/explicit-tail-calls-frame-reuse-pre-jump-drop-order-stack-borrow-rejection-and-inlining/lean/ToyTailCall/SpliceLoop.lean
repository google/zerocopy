import ToyTailCall.SpliceSimPlain

/-!
# Proof support: running a block of argument assignments in the spliced code
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem Emb.transfer {ρ : Nat → Nat × Nat} {off : Nat} {X M M2 : Frame} (h : Emb ρ off X M)
    (hl : M.vals.length ≤ M2.vals.length)
    (hs : ∀ s, s < X.vals.length → M2.get (s + off) = M.get (s + off) ∧
      M2.isLive (s + off) = M.isLive (s + off)) : Emb ρ off X M2 :=
  ⟨Nat.le_trans h.len hl, fun s hsl => by rw [(hs s hsl).1]; exact h.get s hsl,
    fun s hsl => by rw [(hs s hsl).2]; exact h.live s hsl⟩

/-- Running `as.length` argument assignments `t + i := as[i]` (operands renamed by `off`) in the
running frame `M`, whose slots `off ..` hold the original frame `fr`. -/
theorem run_assignTemps {D : Option Nat} {p0 : Prog} {fn0 : Fn} {ρ : Nat → Nat × Nat}
    {off t base W : Nat} {below below' : List Frame} :
    ∀ (as : List Operand) (i0 : Nat) (fr M : Frame) (b : State) (vs : List Val) (fr2 : Frame),
      b.stack = M :: below' → b.unwinding = false → M.pendingRet = none →
      p0.fns[M.fn]? = some fn0 → M.pc = base + i0 →
      (∀ j (hj : j < as.length), fn0.code[base + (i0 + j)]? =
        some (.assign (t + (i0 + j)) (renOp off as[j]) (base + (i0 + j) + 1))) →
      Emb ρ off fr M → ρ fr.fid = (M.fid, off) →
      (∀ M1 : Frame, M1.fid = M.fid → M1.vals.length = M.vals.length →
        (∀ j, j < W → M1.get j = M.get j) → Look ρ below M1 below') →
      W ≤ t + i0 → fr.vals.length + off ≤ t + i0 →
      t + i0 + as.length ≤ M.vals.length → M.live.length = M.vals.length →
      evalOps below fr as = some (vs, fr2) →
      ∃ M2, run .frameReuse D p0 as.length (.running b) = .running { b with stack := M2 :: below' } ∧
        M2.pc = base + i0 + as.length ∧ M2.fid = M.fid ∧ M2.fn = M.fn ∧ M2.cont = M.cont ∧
        M2.pendingRet = M.pendingRet ∧ M2.vals.length = M.vals.length ∧
        M2.live.length = M.live.length ∧ Emb ρ off fr2 M2 ∧
        (∀ j, j < as.length → M2.get (t + (i0 + j)) = rv ρ (vs.getD j .undef) ∧
          M2.isLive (t + (i0 + j)) = true) ∧
        (∀ s, (s < off ∨ fr.vals.length + off ≤ s) → (s < t + i0 ∨ t + i0 + as.length ≤ s) →
          M2.get s = M.get s ∧ M2.isLive s = M.isLive s)
  | [], i0, fr, M, b, vs, fr2, hb, _, _, _, hpc, _, hE, _, _, _, _, _, _, h => by
    simp only [evalOps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨M, ?_, by simp [hpc], rfl, rfl, rfl, rfl, rfl, rfl, hE, fun j hj => by simp at hj,
      fun s _ _ => ⟨rfl, rfl⟩⟩
    obtain ⟨stk, nf, ev, md, tc, uw⟩ := b
    simp only at hb
    subst hb
    rfl
  | o :: as, i0, fr, M, b, vs, fr2, hb, hu, hr, hfn, hpc, hcode, hE, hfid, hlook, hW, hfr, hlenM,
      hll, h => by
    simp only [evalOps] at h
    cases h1 : evalOp below fr o with
    | none => rw [h1] at h; cases h
    | some vf =>
      obtain ⟨v, fr1⟩ := vf
      rw [h1] at h
      simp only at h
      cases h2 : evalOps below fr1 as with
      | none => rw [h2] at h; cases h
      | some vf2 =>
        obtain ⟨vs', fr3⟩ := vf2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlook0 := hlook M rfl rfl (fun _ _ => rfl)
        obtain ⟨e1, e2⟩ := evalOp_sim hE hfid hlook0 h1
        have hc0 := hcode 0 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero] at hc0
        replace hc0 : fn0.code[M.pc]? = some (.assign (t + i0) (renOp off o) (base + i0 + 1)) := by
          rw [hpc]; exact hc0
        have hdst : t + i0 < (killOf off o M).vals.length := by
          simp only [killOf_vals, List.length_cons] at hlenM ⊢; omega
        have hstep : step .frameReuse D p0 b = .running { b with stack :=
            { (killOf off o M).write (t + i0) (rv ρ v) with pc := base + i0 + 1 } :: below' } := by
          rw [step_exec hb hfn hu hr hc0]
          simp only [execI, e1, hdst, ↓reduceIte]
        let M' : Frame := { (killOf off o M).write (t + i0) (rv ρ v) with pc := base + i0 + 1 }
        have hM'v : ∀ s, s ≠ t + i0 → M'.get s = M.get s := by
          intro s hs
          simp only [M', Frame.get]
          change ((killOf off o M).write (t + i0) (rv ρ v)).get s = M.get s
          rw [get_write _ _ hdst]
          simp only [hs, ↓reduceIte]
          unfold Frame.get; rw [killOf_vals]
        have hlen1 : fr1.vals.length = fr.vals.length := by rw [e2]; cases o <;> rfl
        have hKl : (killOf off o M).live.length = (killOf off o M).vals.length := by
          cases o <;> simpa [killOf] using hll
        have hE1 : Emb ρ off fr1 M' := by
          have hk : Emb ρ off fr1 (killOf off o M) := by
            rw [e2]; cases o <;> first | exact hE | exact (by simpa [killOf] using hE.kill _)
          exact (hk.write_out (rv ρ v) (Or.inr (by rw [hlen1]; exact hfr)) hdst hKl).congr rfl rfl rfl rfl
        obtain ⟨M2, hrun, hpc2, hfid2, hfn2, hcont2, hret2, hvl2, hll2, hE2, htemp, hother⟩ :=
          run_assignTemps (D := D) (p0 := p0) (fn0 := fn0) (ρ := ρ) (off := off) (t := t)
            (base := base) (W := W) (below := below) (below' := below') as (i0 + 1) fr1 M' { b with stack := M' :: below' } vs' fr3 rfl
            (by simp [hu]) (by simp [M', hr]) (by simpa [M'] using hfn) (by simp [M']; omega)
            (fun j hj => by
              have := hcode (j + 1) (by simp; omega)
              simp only [List.getElem_cons_succ] at this
              rw [show i0 + 1 + j = i0 + (j + 1) by omega]
              exact this)
            hE1 (by rw [e2]; simp [M', hfid])
            (fun M1 hf1 hl1 hg1 => hlook M1 (by rw [hf1]; simp [M'])
              (by rw [hl1]; simp [M'])
              (fun j hj => by rw [hg1 j hj]; exact hM'v j (by omega)))
            (by omega) (by rw [hlen1]; omega) (by simp [M']; simp at hlenM; omega)
            (by simp [M']; exact hll)
            h2
        refine ⟨M2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE2, ?_, ?_⟩
        · simp only [List.length_cons]
          rw [run_succ, hstep, hrun]
        · rw [hpc2]; simp; omega
        · rw [hfid2]; simp [M']
        · rw [hfn2]; simp [M']
        · rw [hcont2]; simp [M']
        · rw [hret2]; simp [M']
        · rw [hvl2]; simp [M']
        · rw [hll2]; simp [M']
        · intro j hj
          cases j with
          | zero =>
            have := hother (t + i0) (Or.inr (by rw [hlen1]; omega)) (Or.inl (by omega))
            simp only [Nat.add_zero]
            rw [this.1, this.2]
            simp only [M', Frame.get, Frame.isLive]
            change ((killOf off o M).write (t + i0) (rv ρ v)).get (t + i0) = _ ∧
              ((killOf off o M).write (t + i0) (rv ρ v)).isLive (t + i0) = _
            rw [get_write _ _ hdst, isLive_write _ _ (by rw [hKl]; exact hdst)]
            simp
          | succ j =>
            have := htemp j (by simp at hj; omega)
            rw [show i0 + 1 + j = i0 + (j + 1) by omega] at this
            simpa using this
        · intro s hs1 hs2
          have h3 := hother s (by rw [hlen1]; exact hs1) (by simp at hs2; omega)
          rw [h3.1, h3.2]
          have hne : s ≠ t + i0 := by simp at hs2; omega
          refine ⟨hM'v s hne, ?_⟩
          simp only [M']
          change ((killOf off o M).write (t + i0) (rv ρ v)).isLive s = M.isLive s
          rw [isLive_write _ _ (by rw [hKl]; exact hdst)]
          simp only [hne, ↓reduceIte]
          cases o with
          | move x =>
            have hx : x < fr.vals.length := evalOp_move_lt h1
            simp only [killOf, isLive_kill]
            have : s ≠ x + off := fun e => out_ne hx hs1 e.symm
            simp [this]
          | _ => rfl

/-- Evaluating `move (t + i)` for each `i ∈ l`. -/
theorem evalOps_moves (below : List Frame) (t : Nat) :
    ∀ (l : List Nat) (M : Frame), (∀ i ∈ l, t + i < M.vals.length) →
      evalOps below M (l.map fun i => .move (t + i)) =
        some (l.map fun i => M.get (t + i), (l.map (t + ·)).foldl Frame.kill M)
  | [], M, _ => rfl
  | i :: l, M, h => by
    have hi : t + i < M.vals.length := h i (List.mem_cons_self ..)
    simp only [List.map_cons, evalOps, evalOp, hi, ↓reduceIte, List.foldl_cons]
    rw [evalOps_moves below t l (M.kill (t + i))
      (fun j hj => by simpa using h j (List.mem_cons_of_mem _ hj))]
    simp only [get_kill]

end Toy.TailCall.SpliceProof
