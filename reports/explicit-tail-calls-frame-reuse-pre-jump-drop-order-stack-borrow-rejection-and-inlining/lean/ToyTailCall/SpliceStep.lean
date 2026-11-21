import ToyTailCall.SpliceMatch

/-!
# Proof support: one-to-one steps of a plain running frame
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}

theorem renOp_zero (o : Operand) : renOp 0 o = o := by cases o <;> rfl

theorem map_renOp_zero (os : List Operand) : os.map (renOp 0) = os := by
  simp [funext renOp_zero]

theorem map_add_zero (ks : List Nat) : ks.map (· + 0) = ks := by simp

theorem PlainRel.killOf {F F' : Frame} (h : PlainRel S ρ F F') (o : Operand) :
    PlainRel S ρ (Toy.TailCall.SpliceProof.killOf 0 o F) (Toy.TailCall.SpliceProof.killOf 0 o F') := by
  cases o <;> first | exact h | exact h.kill _

theorem mem_pendingDrops_lt {fn : Fn} {F : Frame} {s : Nat} (h : s ∈ pendingDrops fn F) :
    s < F.vals.length := by
  unfold pendingDrops at h
  simp only [List.mem_filter, List.mem_reverse, List.mem_range] at h
  exact h.1

theorem relAt_plain {a' b' : State} {F1 F1' : Frame} {os ss : List Frame}
    (hP1 : PlainRel S ρ F1 F1') (hpc : a'.unwinding = false → F1'.pc = F1.pc)
    (hB : Below S ρ os ss) (ha' : a'.stack = F1 :: os) (hb' : b'.stack = F1' :: ss)
    (hbA : ∀ X ∈ F1 :: os, Bounded a'.nextFid X) (hbB : ∀ Y ∈ F1' :: ss, Y.fid < b'.nextFid)
    (hpw : (F1' :: ss).Pairwise (fun x y => y.fid < x.fid)) (hu : b'.unwinding = a'.unwinding)
    (he : b'.events = a'.events) : RelAt S ρ a' b' :=
  ⟨by rw [ha', hb']; exact .plain hP1 hpc hB, hu, he, by rw [ha']; exact hbA, by rw [hb']; exact hbB,
    by rw [hb']; exact hpw⟩

theorem relAt_inl {a' b' : State} {G1 C1 M1 : Frame} {os ss : List Frame}
    (hI1 : InlRel S ρ G1 C1 M1) (hc1 : C1.cont = .store S.dst S.next)
    (hpc : a'.unwinding = false → M1.pc = S.gStart + S.K * G1.pc)
    (hB : Below S ρ os ss) (ha' : a'.stack = G1 :: C1 :: os) (hb' : b'.stack = M1 :: ss)
    (hbA : ∀ X ∈ G1 :: C1 :: os, Bounded a'.nextFid X) (hbB : ∀ Y ∈ M1 :: ss, Y.fid < b'.nextFid)
    (hpw : (M1 :: ss).Pairwise (fun x y => y.fid < x.fid)) (hu : b'.unwinding = a'.unwinding)
    (he : b'.events = a'.events) : RelAt S ρ a' b' :=
  ⟨by rw [ha', hb']; exact .inl hI1 hc1 hpc hB, hu, he, by rw [ha']; exact hbA,
    by rw [hb']; exact hbB, by rw [hb']; exact hpw⟩

/-- Facts available about a related pair with a plain running frame. -/
structure PlainCtx (S : Site) (ρ : Nat → Nat × Nat) (a b : State) (F F' : Frame)
    (os ss : List Frame) : Prop where
  hr : RelAt S ρ a b
  ha : a.stack = F :: os
  hb : b.stack = F' :: ss
  hP : PlainRel S ρ F F'
  hB : Below S ρ os ss

theorem PlainCtx.bA {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) : ∀ X ∈ F :: os, Bounded a.nextFid X := by
  rw [← c.ha]; exact c.hr.freshA

theorem PlainCtx.bB {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) : ∀ Y ∈ F' :: ss, Y.fid < b.nextFid := by
  rw [← c.hb]; exact c.hr.freshB

theorem PlainCtx.pw {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) : (F' :: ss).Pairwise (fun x y => y.fid < x.fid) := by
  rw [← c.hb]; exact c.hr.orderB

theorem PlainCtx.look {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) : Look ρ os F' ss :=
  look_plain c.hB (List.pairwise_cons.mp c.pw).2 (List.pairwise_cons.mp c.pw).1

theorem PlainCtx.vals {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) : ∀ X ∈ F :: os, ∀ w ∈ X.vals, PtrLt a.nextFid w :=
  fun X hX => (c.bA X hX).2

theorem PlainCtx.evalOp {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) {o : Operand} {v : Val} {F1 : Frame}
    (h : Toy.TailCall.evalOp os F o = some (v, F1)) :
    Toy.TailCall.evalOp ss F' o = some (rv ρ v, killOf 0 o F') ∧ F1 = killOf 0 o F ∧
      PtrLt a.nextFid v := by
  obtain ⟨e1, e2⟩ := evalOp_sim c.hP.emb c.hP.fid c.look h
  rw [renOp_zero] at e1
  exact ⟨e1, e2, evalOp_ptrLt (c.bA F (List.mem_cons_self ..)).1 c.vals h⟩

theorem PlainCtx.evalOps {a b : State} {F F' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) {args : List Operand} {vs : List Val} {F1 : Frame}
    (h : Toy.TailCall.evalOps os F args = some (vs, F1)) :
    ∃ ks : List Nat, F1 = ks.foldl Frame.kill F ∧
      Toy.TailCall.evalOps ss F' args = some (vs.map (rv ρ), ks.foldl Frame.kill F') ∧
      ∀ v ∈ vs, PtrLt a.nextFid v := by
  obtain ⟨ks, -, e2, e1⟩ := evalOps_sim args F F' vs F1 c.hP.emb c.hP.fid c.look h
  rw [map_renOp_zero, map_add_zero] at e1
  exact ⟨ks, e2, e1, evalOps_ptrLt args F vs F1 (c.bA F (List.mem_cons_self ..)).1 c.vals h⟩

/-- A frame-local update of the plain running frame. -/
theorem PlainCtx.local {a b a' b' : State} {F F' F1 F1' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) (ha' : a'.stack = F1 :: os)
    (hb' : b'.stack = F1' :: ss) (hP1 : PlainRel S ρ F1 F1')
    (hpc : a'.unwinding = false → F1'.pc = F1.pc) (hf : F1.fid = F.fid) (hf' : F1'.fid = F'.fid)
    (hv : ∀ v ∈ F1.vals, PtrLt a.nextFid v) (hn : a'.nextFid = a.nextFid)
    (hn' : b'.nextFid = b.nextFid) (hu : b'.unwinding = a'.unwinding)
    (he : b'.events = a'.events) : Match S (.running a') (.running b') := by
  refine match_running (relAt_plain hP1 hpc c.hB ha' hb' ?_ ?_ ?_ hu he)
  · rw [hn]; exact bounded_head c.bA ⟨by rw [hf]; exact (c.bA F (List.mem_cons_self ..)).1, hv⟩
  · rw [hn']; exact fresh_head c.bB hf'
  · exact pairwise_head c.pw hf'

theorem PlainCtx.doReturn {a b : State} {F F' F1 F1' : Frame} {os ss : List Frame}
    (c : PlainCtx S ρ a b F F' os ss) {fn : Fn} (hfn : S.p.fns[F1.fn]? = some fn)
    (hP1 : PlainRel S ρ F1 F1') {v : Val} (hv : PtrLt a.nextFid v) (hu : a.unwinding = false) :
    Match S (Toy.TailCall.doReturn a fn F1 os v)
      (Toy.TailCall.doReturn b (S.fnS F1.fn fn) F1' ss (rv ρ v)) := by
  have hl : ∀ s ∈ pendingDrops fn F1, s < F1.vals.length := fun s hs => mem_pendingDrops_lt hs
  obtain ⟨hd, -⟩ := hP1.dropList hfn (pendingDrops fn F1) hl false
  have hpd := hP1.pending hfn
  simp only [Toy.TailCall.doReturn, hpd, hd]
  have hbA : ∀ X ∈ os, Bounded a.nextFid X := fun X hX => c.bA X (List.mem_cons_of_mem _ hX)
  have hbB : ∀ Y ∈ ss, Y.fid < b.nextFid := fun Y hY => c.bB Y (List.mem_cons_of_mem _ hY)
  have hpw := (List.pairwise_cons.mp c.pw).2
  cases (dropList fn F1 (pendingDrops fn F1) false).2.2 with
  | ok => exact match_deliver c.hB hbA hbB hpw hv (by simp [c.hr.ev]) hu (by rw [c.hr.uw]; exact hu)
  | unwind => exact match_unwindBelow c.hB hbA hbB hpw (by simp [c.hr.ev])
  | abort => exact match_halt _ (by simp [c.hr.ev])

end

end Toy.TailCall.SpliceProof
