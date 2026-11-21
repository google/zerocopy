import ToyTailCall.Machine
import ToyTailCall.Borrow
import ToyTailCall.Lemmas
import ToyTailCall.EscapeProof

/-!
# Proof support: frame reuse versus pre-jump finalization

`preJump` keeps each frame finalized by a tail call on the stack (continuation `thenReturn`, no
pending return, no pending drop); `frameReuse` removes it. In the running states of the unbounded
`preJump` run, the finalized frames are exactly the non-top frames with continuation
`thenReturn`. The related `frameReuse` state has the same top frame, the `preJump` frames below
it with the finalized ones removed, and the same `nextFid`, events and `unwinding` flag.

Every `frameReuse` step is matched by one `preJump` step followed by one further step per
finalized frame that a returned value or an unwinding passes (each emits no event). Loads agree
because, by an invariant that needs `NoStackBorrow` for its tail-call case, no frame holds a
pointer into a finalized frame. Under a bound, a `preJump` stack is at least as long as the
related `frameReuse` stack, so where `frameReuse` overflows `preJump` overflows too; a `preJump`
overflow is the one outcome the matching does not transfer.
-/

namespace Toy.TailCall.ReuseProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false

/-! ### The invariant of the `preJump` run -/

/-- The invariant of the running states of the unbounded `preJump` run of a program satisfying
`NoStackBorrow` (stack listed top first). -/
structure PInv (p : Prog) (st : State) : Prop where
  wf : ∀ f ∈ st.stack, WF p f
  fresh : ∀ f ∈ st.stack, f.fid < st.nextFid ∧ ∀ X, st.nextFid ≤ X → NoPtr X f
  order : st.stack.Pairwise fun a b => b.fid < a.fid
  down : st.stack.Pairwise fun a b => NoPtr a.fid b
  guard : st.stack.Pairwise fun a b => b.cont = .thenReturn → NoPtr b.fid a
  fin : ∀ f rest, st.stack = f :: rest → ∀ z ∈ rest, z.cont = .thenReturn →
    z.pendingRet = none ∧ ∃ fn, p.fns[z.fn]? = some fn ∧ pendingDrops fn z = []

/-- A value that may be stored in the running frame, which sits on the frames `rest`. -/
def PSafe (n : Nat) (rest : List Frame) (v : Val) : Prop :=
  (∀ X, n ≤ X → v.pointsInto X = false) ∧
    ∀ b ∈ rest, b.cont = .thenReturn → v.pointsInto b.fid = false

theorem pinv_congr {p : Prog} {st st' : State} (hinv : PInv p st) (hs : st'.stack = st.stack)
    (hn : st'.nextFid = st.nextFid) : PInv p st' := by
  obtain ⟨a, b, c, d, e, f⟩ := hinv
  exact ⟨by rw [hs]; exact a, by rw [hs, hn]; exact b, by rw [hs]; exact c, by rw [hs]; exact d,
    by rw [hs]; exact e, by rw [hs]; exact f⟩

theorem pinv_pop {p : Prog} {st st' : State} {fr : Frame} {rest : List Frame} (hinv : PInv p st)
    (hs : st.stack = fr :: rest) (hs' : st'.stack = rest) (hn : st'.nextFid = st.nextFid) :
    PInv p st' := by
  have hsub : ∀ f ∈ st'.stack, f ∈ st.stack := by
    intro f hf; rw [hs'] at hf; rw [hs]; exact List.mem_cons_of_mem _ hf
  have o := hinv.order; have d := hinv.down; have g := hinv.guard
  rw [hs, List.pairwise_cons] at o d g
  refine ⟨fun f hf => hinv.wf f (hsub f hf), fun f hf => by rw [hn]; exact hinv.fresh f (hsub f hf),
    by rw [hs']; exact o.2, by rw [hs']; exact d.2, by rw [hs']; exact g.2, ?_⟩
  intro f r hfr z hz hzc
  rw [hs'] at hfr
  subst hfr
  exact hinv.fin fr (f :: r) hs z (List.mem_cons_of_mem _ hz) hzc

theorem pinv_top {p : Prog} {st st' : State} {fr fr' : Frame} {rest : List Frame}
    (hinv : PInv p st) (hs : st.stack = fr :: rest) (hs' : st'.stack = fr' :: rest)
    (hn : st'.nextFid = st.nextFid) (hfid : fr'.fid = fr.fid) (hfn : fr'.fn = fr.fn)
    (hlen : fr'.vals.length = fr.vals.length)
    (hvals : ∀ v ∈ fr'.vals, v ∈ fr.vals ∨ PSafe st.nextFid rest v)
    (hret : ∀ v, fr'.pendingRet = some v → fr.pendingRet = some v ∨ PSafe st.nextFid rest v) :
    PInv p st' := by
  have o := hinv.order; have d := hinv.down; have g := hinv.guard
  rw [hs, List.pairwise_cons] at o d g
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  have hrest : ∀ f ∈ rest, f ∈ st.stack := by
    intro f hf; rw [hs]; exact List.mem_cons_of_mem _ hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf; rw [hs'] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨fn, hfn', hl⟩ := hinv.wf fr hfr
      exact ⟨fn, by rw [hfn]; exact hfn', by rw [hlen]; exact hl⟩
    · exact hinv.wf f (hrest f hf)
  · intro f hf; rw [hs'] at hf; rw [hn]
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨h1, h2⟩ := hinv.fresh fr hfr
      refine ⟨by rw [hfid]; exact h1, fun X hX => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
      · rcases hvals v hv with hv | hv
        · exact (h2 X hX).1 v hv
        · exact hv.1 X hX
      · rcases hret v hv with hv | hv
        · exact (h2 X hX).2 v hv
        · exact hv.1 X hX
    · exact hinv.fresh f (hrest f hf)
  · rw [hs', List.pairwise_cons]; exact ⟨fun b hb => by rw [hfid]; exact o.1 b hb, o.2⟩
  · rw [hs', List.pairwise_cons]; exact ⟨fun b hb => by rw [hfid]; exact d.1 b hb, d.2⟩
  · rw [hs', List.pairwise_cons]
    refine ⟨fun b hb hgb => ⟨fun v hv => ?_, fun v hv => ?_⟩, g.2⟩
    · rcases hvals v hv with hv | hv
      · exact (g.1 b hb hgb).1 v hv
      · exact hv.2 b hb hgb
    · rcases hret v hv with hv | hv
      · exact (g.1 b hb hgb).2 v hv
      · exact hv.2 b hb hgb
  · intro f r hfr z hz hzc
    rw [hs'] at hfr
    injection hfr with _ hr
    subst hr
    exact hinv.fin fr rest hs z hz hzc

theorem pinv_top_same {p : Prog} {st st' : State} {fr fr' : Frame} {rest : List Frame}
    (hinv : PInv p st) (hs : st.stack = fr :: rest) (hs' : st'.stack = fr' :: rest)
    (hn : st'.nextFid = st.nextFid) (hv : fr'.vals = fr.vals) (hfid : fr'.fid = fr.fid)
    (hfn : fr'.fn = fr.fn) (hret : fr'.pendingRet = fr.pendingRet) : PInv p st' :=
  pinv_top hinv hs hs' hn hfid hfn (by rw [hv]) (fun v h => Or.inl (by rw [← hv]; exact h))
    (fun v h => Or.inl (by rw [← hret]; exact h))

theorem phall_fresh {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : PInv p st)
    (hs : st.stack = fr :: rest) {X : Nat} (hX : st.nextFid ≤ X) :
    fr.fid ≠ X ∧ ∀ g ∈ fr :: rest, g.fid ≠ X → ∀ w ∈ g.vals, w.pointsInto X = false := by
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  refine ⟨by have := (hinv.fresh fr hfr).1; omega, fun g hg _ => ?_⟩
  rw [← hs] at hg
  exact ((hinv.fresh g hg).2 X hX).1

theorem phall_guard {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : PInv p st)
    (hs : st.stack = fr :: rest) {b : Frame} (hb : b ∈ rest) (hgb : b.cont = .thenReturn) :
    fr.fid ≠ b.fid ∧ ∀ g ∈ fr :: rest, g.fid ≠ b.fid → ∀ w ∈ g.vals, w.pointsInto b.fid = false := by
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hb
  have hst : st.stack = (fr :: l1) ++ b :: l2 := by rw [hs, hl]; rfl
  have o := hinv.order; have d := hinv.down; have g := hinv.guard
  rw [hst] at o d g
  have ho := pairwise_split o; have hd := pairwise_split d; have hg := pairwise_split g
  refine ⟨by have := ho.1 fr (List.mem_cons_self ..); omega, fun x hx hne => ?_⟩
  have hx' : x ∈ (fr :: l1) ++ b :: l2 := by rw [← hst, hs]; exact hx
  rcases List.mem_append.mp hx' with hx1 | hx2
  · exact (hg.1 x hx1 hgb).1
  · rcases List.mem_cons.mp hx2 with rfl | hx2
    · exact absurd rfl hne
    · exact (hd.2 x hx2).1

theorem psafe_eval {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : PInv p st)
    (hs : st.stack = fr :: rest) {o : Operand} {v : Val} {fr1 : Frame}
    (h : evalOp rest fr o = some (v, fr1)) : PSafe st.nextFid rest v :=
  ⟨fun _ hX => evalOp_noPtr (phall_fresh hinv hs hX).1 (phall_fresh hinv hs hX).2 h,
    fun _ hb hgb => evalOp_noPtr (phall_guard hinv hs hb hgb).1 (phall_guard hinv hs hb hgb).2 h⟩

theorem psafe_evals {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : PInv p st)
    (hs : st.stack = fr :: rest) {os : List Operand} {vs : List Val} {fr1 : Frame}
    (h : evalOps rest fr os = some (vs, fr1)) : ∀ v ∈ vs, PSafe st.nextFid rest v :=
  fun v hv =>
    ⟨fun _ hX => evalOps_noPtr (phall_fresh hinv hs hX).1 (phall_fresh hinv hs hX).2 h v hv,
      fun _ hb hgb => evalOps_noPtr (phall_guard hinv hs hb hgb).1 (phall_guard hinv hs hb hgb).2 h v hv⟩

theorem psafe_ret {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : PInv p st)
    (hs : st.stack = fr :: rest) {v : Val} (h : fr.pendingRet = some v) :
    PSafe st.nextFid rest v := by
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  have g := hinv.guard
  rw [hs, List.pairwise_cons] at g
  exact ⟨fun X hX => ((hinv.fresh fr hfr).2 X hX).2 v h, fun b hb hgb => (g.1 b hb hgb).2 v h⟩

theorem pinv_push {p : Prog} {D : Option Nat} {st st1 st' : State} {fr c : Frame}
    {rest : List Frame} {f : FnId} {vs : List Val} (hinv : PInv p st) (hs : st.stack = fr :: rest)
    (hn : st1.nextFid = st.nextFid)
    (hfid : c.fid = fr.fid) (hfn : c.fn = fr.fn) (hvals : c.vals = fr.vals)
    (hret : c.pendingRet = fr.pendingRet)
    (hfin : c.cont = .thenReturn → c.pendingRet = none ∧ ∃ fn, p.fns[c.fn]? = some fn ∧
      pendingDrops fn c = [])
    (hsafe : ∀ v ∈ vs, PSafe st.nextFid rest v)
    (hg : c.cont = .thenReturn → ∀ v ∈ vs, v.pointsInto c.fid = false)
    (h : push D p st1 (c :: rest) f vs = .running st') : PInv p st' := by
  obtain ⟨stk1, n1, ev1, md1, tc1, uw1⟩ := st1
  simp only at hn
  subst hn
  unfold push at h
  cases hf : p.fns[f]? with
  | none => rw [hf] at h; simp [State.halt] at h
  | some fn =>
    rw [hf] at h
    simp only at h
    split at h
    · simp [State.halt] at h
    · rename_i hok
      split at h
      · simp [State.halt] at h
      simp only [Conf.running.injEq] at h
      subst h
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
        Classical.not_not, Nat.not_lt] at hok
      obtain ⟨hlenp, hle⟩ := hok
      have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
      have hrest : ∀ x ∈ rest, x ∈ st.stack := by
        intro x hx; rw [hs]; exact List.mem_cons_of_mem _ hx
      have o := hinv.order; have d := hinv.down; have g := hinv.guard
      rw [hs, List.pairwise_cons] at o d g
      have hcfresh := hinv.fresh fr hfr
      have hnew : ∀ w ∈ vs ++ List.replicate (fn.nSlots - fn.nParams) Val.undef,
          w ∈ vs ∨ w = .undef := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (List.eq_of_mem_replicate hw)
      have hnoc : ∀ X, NoPtr X fr → NoPtr X c := fun X ⟨h1, h2⟩ =>
        ⟨by rw [hvals]; exact h1, by rw [hret]; exact h2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact ⟨fn, hf, by simp [hlenp]; omega⟩
        · obtain ⟨fn', h1, h2⟩ := hinv.wf fr hfr
          exact ⟨fn', by rw [hfn]; exact h1, by rw [hvals]; exact h2⟩
        · exact hinv.wf x (hrest x hx)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · refine ⟨by simp, fun X hX => ⟨fun w hw => ?_, fun w hw => by simp at hw⟩⟩
          rcases hnew w hw with hw | rfl
          · exact (hsafe w hw).1 X (by omega)
          · rfl
        · refine ⟨by rw [hfid]; omega, fun X hX => hnoc X (hcfresh.2 X (by omega))⟩
        · have := hinv.fresh x (hrest x hx)
          exact ⟨by omega, fun X hX => this.2 X (by omega)⟩
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, ⟨fun b hb => by rw [hfid]; exact o.1 b hb, o.2⟩⟩
        intro b hb
        rcases hb with rfl | hb
        · rw [hfid]; exact hcfresh.1
        · exact (hinv.fresh b (hrest b hb)).1
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, ⟨fun b hb => by rw [hfid]; exact d.1 b hb, d.2⟩⟩
        intro b hb
        rcases hb with rfl | hb
        · exact hnoc _ (hcfresh.2 _ (Nat.le_refl _))
        · exact (hinv.fresh b (hrest b hb)).2 _ (Nat.le_refl _)
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, ⟨fun b hb hgb => hnoc _ (g.1 b hb hgb), g.2⟩⟩
        intro b hb hgb
        refine ⟨fun w hw => ?_, fun w hw => by simp at hw⟩
        rcases hnew w hw with hw | rfl
        · rcases hb with rfl | hb
          · exact hg hgb w hw
          · exact (hsafe w hw).2 b hb hgb
        · rfl
      · intro x r hxr z hz hzc
        simp only [List.cons.injEq] at hxr
        obtain ⟨-, rfl⟩ := hxr
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hfin hzc
        · exact hinv.fin fr rest hs z hz hzc

theorem pinv_deliver {p : Prog} {st st1 st' : State} {fr : Frame} {rest : List Frame} {v : Val}
    (hinv : PInv p st) (hs : st.stack = fr :: rest) (hn : st1.nextFid = st.nextFid)
    (hv : PSafe st.nextFid rest v) (h : deliver st1 rest v = .running st') : PInv p st' := by
  have hpop : PInv p { st with stack := rest } := pinv_pop hinv hs rfl rfl
  cases rest with
  | nil => simp [deliver, State.halt] at h
  | cons g rest' =>
    have hv' : PSafe st.nextFid rest' v :=
      ⟨hv.1, fun b hb hgb => hv.2 b (List.mem_cons_of_mem _ hb) hgb⟩
    simp only [deliver] at h
    split at h
    · rename_i dst next hc
      simp only [Conf.running.injEq] at h
      subst h
      refine pinv_top hpop rfl rfl hn rfl rfl (by simp [Frame.write])
        (fun w hw => ?_) (fun w hw => Or.inl hw)
      rcases write_vals g dst v w hw with hw | rfl
      · exact Or.inl hw
      · exact Or.inr hv'
    · rename_i hc
      simp only [Conf.running.injEq] at h
      subst h
      refine pinv_top hpop rfl rfl hn rfl rfl rfl (fun w hw => Or.inl hw) ?_
      intro w hw
      simp only [Option.some.injEq] at hw
      subst hw
      exact Or.inr hv'

theorem pinv_doReturn {p : Prog} {st st' : State} {fr fr1 : Frame} {rest : List Frame} {fn : Fn}
    {v : Val} (hinv : PInv p st) (hs : st.stack = fr :: rest) (hv : PSafe st.nextFid rest v)
    (h : doReturn st fn fr1 rest v = .running st') : PInv p st' := by
  dsimp only [doReturn] at h
  split at h
  · exact pinv_deliver hinv hs (by rfl) hv h
  · unfold unwindBelow at h
    split at h
    · simp [State.halt] at h
    · simp only [Conf.running.injEq] at h
      subst h
      exact pinv_pop hinv hs rfl rfl
  · simp [State.halt] at h

/-! ### Preservation along the `preJump` run -/

theorem mem_pendingDrops' (fn : Fn) (fr : Frame) (s : Slot) :
    s ∈ pendingDrops fn fr ↔ s < fr.vals.length ∧ fr.isLive s = true ∧ fn.dtor s ≠ .none := by
  simp [pendingDrops, List.mem_filter, List.mem_reverse, List.mem_range]

theorem clears_pending (fn : Fn) (fr : Frame)
    (hna : (dropList fn fr (pendingDrops fn fr) false).2.2 ≠ .abort) :
    pendingDrops fn (dropList fn fr (pendingDrops fn fr) false).1 = [] := by
  have ⟨hv, hpres, hmem⟩ := dropList_kills_mem fn fr (pendingDrops fn fr) false hna
  rw [List.eq_nil_iff_forall_not_mem]
  intro s hs
  rw [mem_pendingDrops', hv] at hs
  have hlive_orig : fr.isLive s = true := by
    cases h0 : fr.isLive s
    · exfalso; have := hpres s h0; rw [this] at hs; cases hs.2.1
    · rfl
  have hin : s ∈ pendingDrops fn fr := (mem_pendingDrops' fn fr s).2 ⟨hs.1, hlive_orig, hs.2.2⟩
  rw [hmem s hin] at hs
  cases hs.2.1

theorem args_noBorrow {p : Prog} {st : State} {fr : Frame} {rest : List Frame} {fn : Fn}
    {g : FnId} {args : List Operand} {vs : List Val} {fr1 : Frame}
    (hnb : tailCallBorrowsFrame p st = false) (hs : st.stack = fr :: rest)
    (hu : st.unwinding = false) (hret : fr.pendingRet = none) (hfn : p.fns[fr.fn]? = some fn)
    (hcode : fn.code[fr.pc]? = some (.tailCall g args))
    (hev : evalOps rest fr args = some (vs, fr1)) : ∀ v ∈ vs, v.pointsInto fr.fid = false := by
  simp only [tailCallBorrowsFrame, hs, hu, hret, hfn, hcode, hev, Option.isSome_none,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hnb
  intro v hv
  cases h : v.pointsInto fr.fid
  · rfl
  · have := List.any_eq_true.mpr ⟨v, hv, h⟩
    rw [hnb] at this
    cases this

/-- One step of the `preJump` machine (any bound) preserves the invariant, provided the step
does not pass a pointer into the current frame to a tail call. -/
theorem pinv_step {p : Prog} {D : Option Nat} {st st' : State} (hinv : PInv p st)
    (hnb : tailCallBorrowsFrame p st = false) (h : step .preJump D p st = .running st') :
    PInv p st' := by
  cases hs : st.stack with
  | nil => simp [step, hs, State.halt] at h
  | cons fr rest =>
    cases hfn : p.fns[fr.fn]? with
    | none => simp [step, hs, hfn, State.halt] at h
    | some fn =>
    have hfnEq : ∀ fn', p.fns[fr.fn]? = some fn' → fn' = fn := by
      intro fn' h1; rw [hfn] at h1; exact (Option.some.inj h1).symm
    simp only [step, hs, hfn] at h
    by_cases hu : st.unwinding = true
    · simp only [hu, ↓reduceIte] at h
      try dsimp only at h
      split at h
      · simp [State.halt] at h
      · split at h
        · simp [State.halt] at h
        · simp only [Conf.running.injEq] at h
          subst h
          exact pinv_pop hinv hs rfl rfl
    · have hu' : st.unwinding = false := by simpa using hu
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      cases hret : fr.pendingRet with
      | some v =>
        rw [hret] at h
        simp only at h
        exact pinv_doReturn hinv hs (psafe_ret hinv hs hret) h
      | none =>
        rw [hret] at h
        simp only at h
        cases hcode : fn.code[fr.pc]? with
        | none => rw [hcode] at h; simp [State.halt] at h
        | some i =>
          rw [hcode] at h
          simp only at h
          cases i with
          | assign dst op next =>
            simp only at h
            cases hev : evalOp rest fr op with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨v, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              have hf := evalOp_frame hev
              split at h
              · simp only [Conf.running.injEq] at h
                subst h
                refine pinv_top hinv hs rfl rfl (by simp [Frame.write, hf.2.1])
                  (by simp [Frame.write, hf.2.2.1]) (by simp [Frame.write, hf.1])
                  (fun w hw => ?_) (fun w hw => ?_)
                · rcases write_vals fr1 dst v w hw with hw | rfl
                  · left; rw [← hf.1]; exact hw
                  · right; exact psafe_eval hinv hs hev
                · left; rw [← hf.2.2.2.2.2]; exact hw
              · simp [State.halt] at h
          | emit k next =>
            simp only [Conf.running.injEq] at h
            subst h
            exact pinv_top_same hinv hs rfl rfl rfl rfl rfl (by simp [hret])
          | branchLt s0 k t e =>
            simp only at h
            cases hget : fr.get s0 with
            | int n =>
              rw [hget] at h
              simp only [Conf.running.injEq] at h
              subst h
              exact pinv_top_same hinv hs rfl rfl rfl rfl rfl (by simp [hret])
            | ptr a b => rw [hget] at h; simp [State.halt] at h
            | undef => rw [hget] at h; simp [State.halt] at h
          | goto next =>
            simp only [Conf.running.injEq] at h
            subst h
            exact pinv_top_same hinv hs rfl rfl rfl rfl rfl (by simp [hret])
          | reset ss next =>
            simp only [Conf.running.injEq] at h
            subst h
            obtain ⟨h1, h2, h3, h4, h5, -⟩ := foldl_clear_frame ss fr
            refine pinv_top hinv hs rfl rfl h1 h2 h3 (fun w hw => ?_)
              (fun w hw => Or.inl (by rw [← h4]; exact hw))
            rcases h5 w hw with hw | rfl
            · exact Or.inl hw
            · exact Or.inr ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
          | dropSlots ss next =>
            dsimp only at h
            obtain ⟨d1, d2, d3, d4⟩ :=
              dropList_frame fn fr (ss.filter (fun s => fr.isLive s && fn.dtor s != .none)) false
            split at h
            · simp only [Conf.running.injEq] at h
              subst h
              exact pinv_top_same hinv hs rfl rfl d1 d2 d3 d4
            · simp only [Conf.running.injEq] at h
              subst h
              exact pinv_top_same hinv hs rfl rfl d1 d2 d3 d4
            · simp [State.halt] at h
          | call g args dst next =>
            simp only at h
            cases hev : evalOps rest fr args with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨vs, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              have hf := evalOps_frame hev
              split at h
              · exact pinv_push (c := { fr1 with cont := .store dst next }) hinv hs (by rfl)
                  hf.2.1 hf.2.2.1 hf.1 hf.2.2.2.2.2 (fun hc => by simp at hc)
                  (psafe_evals hinv hs hev) (fun hc => by simp at hc) h
              · simp [State.halt] at h
          | ret op =>
            simp only at h
            cases hev : evalOp rest fr op with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨v, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              exact pinv_doReturn hinv hs (psafe_eval hinv hs hev) h
          | tailCall g args =>
            simp only at h
            cases hev : evalOps rest fr args with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨vs, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              have hf := evalOps_frame hev
              have hno := args_noBorrow hnb hs hu' hret hfn hcode hev
              dsimp only [doTailCall] at h
              obtain ⟨d1, d2, d3, d4⟩ := dropList_frame fn fr1 (pendingDrops fn fr1) false
              split at h
              · rename_i hok
                obtain ⟨st'', hp, hs1, hn1⟩ := bumpTail_running h
                refine pinv_congr ?_ hs1 hn1
                refine pinv_push
                  (c := { (dropList fn fr1 (pendingDrops fn fr1) false).1 with cont := .thenReturn })
                  hinv hs (by rfl) (d2.trans hf.2.1) (d3.trans hf.2.2.1) (d1.trans hf.1)
                  (d4.trans hf.2.2.2.2.2) (fun _ => ⟨?_, fn, ?_, ?_⟩) (psafe_evals hinv hs hev) ?_ hp
                · show (dropList fn fr1 (pendingDrops fn fr1) false).1.pendingRet = none
                  rw [d4, hf.2.2.2.2.2, hret]
                · show p.fns[(dropList fn fr1 (pendingDrops fn fr1) false).1.fn]? = some fn
                  rw [d3, hf.2.2.1, hfn]
                · show pendingDrops fn (dropList fn fr1 (pendingDrops fn fr1) false).1 = []
                  exact clears_pending fn fr1 (by rw [hok]; simp)
                · intro _ w hw
                  show w.pointsInto (dropList fn fr1 (pendingDrops fn fr1) false).1.fid = false
                  rw [d2, hf.2.1]; exact hno w hw
              · unfold unwindBelow at h
                split at h
                · simp [State.halt] at h
                · simp only [Conf.running.injEq] at h
                  subst h
                  exact pinv_pop hinv hs rfl rfl
              · simp [State.halt] at h
          | panic =>
            simp only [Conf.running.injEq] at h
            subst h
            exact pinv_congr hinv hs.symm rfl

theorem push_none {D : Option Nat} {p : Prog} {st : State} {stk : List Frame} {f : FnId}
    {args : List Val} {st' : State} (h : push D p st stk f args = .running st') :
    push none p st stk f args = .running st' := by
  unfold push at h ⊢
  split at h
  · simp [State.halt] at h
  · rename_i fn hfn
    simp only [hfn]
    split at h
    · simp [State.halt] at h
    · rename_i hok
      simp only [hok, ↓reduceIte]
      split at h
      · simp [State.halt] at h
      · simpa [overflows] using h

theorem pinv_start (p : Prog) (st : State) (h : start none p = .running st) : PInv p st := by
  unfold start push at h
  cases hf : p.fns[0]? with
  | none => rw [hf] at h; simp [State.halt] at h
  | some fn =>
    rw [hf] at h
    simp only at h
    split at h
    · simp [State.halt] at h
    · rename_i hok
      simp only [overflows, Bool.false_eq_true, ↓reduceIte, Conf.running.injEq] at h
      subst h
      simp only [List.length_nil, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
        Classical.not_not, Nat.not_lt] at hok
      obtain ⟨h0, hle⟩ := hok
      have hv : ∀ w ∈ ([] : List Val) ++ List.replicate (fn.nSlots - fn.nParams) Val.undef,
          w = .undef := by
        intro w hw
        rw [List.nil_append] at hw
        exact List.eq_of_mem_replicate hw
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
      · intro f hf'
        rw [List.mem_singleton] at hf'
        subst hf'
        exact ⟨fn, hf, by simp; omega⟩
      · intro f hf'
        rw [List.mem_singleton] at hf'
        subst hf'
        refine ⟨by simp [State.empty], fun X _ => ⟨fun w hw => by rw [hv w hw]; rfl,
          fun w hw => by simp at hw⟩⟩
      · exact List.pairwise_singleton _ _
      · exact List.pairwise_singleton _ _
      · exact List.pairwise_singleton _ _
      · intro f r hfr z hz
        simp only [List.cons.injEq] at hfr
        rw [← hfr.2] at hz
        cases hz

/-- `a` is a running state of the unbounded `preJump` run. -/
def Reach (p : Prog) (a : State) : Prop := ∃ n, run .preJump none p n (start none p) = .running a

theorem run_succ_last (sem : Sem) (D : Option Nat) (p : Prog) (n : Nat) (c : Conf) :
    run sem D p (n + 1) c =
      (match run sem D p n c with
       | .running s => step sem D p s
       | .halted r => .halted r) := by
  rw [run_add]
  cases run sem D p n c with
  | running s => simp only [run]
  | halted r => rfl

theorem pinv_reach {p : Prog} (hnb : NoStackBorrow p) :
    ∀ n a, run .preJump none p n (start none p) = .running a → PInv p a
  | 0, a, h => pinv_start p a h
  | n + 1, a, h => by
    rw [run_succ_last] at h
    cases hc : run .preJump none p n (start none p) with
    | running s =>
      rw [hc] at h
      exact pinv_step (pinv_reach hnb n s hc) (hnb n s hc) h
    | halted r => rw [hc] at h; cases h

theorem bump_push_none {D : Option Nat} {p : Prog} {st : State} {stk : List Frame} {f : FnId}
    {args : List Val} {st' : State} (h : bumpTail (push D p st stk f args) = .running st') :
    bumpTail (push none p st stk f args) = .running st' := by
  obtain ⟨s, hs, -, -⟩ := bumpTail_running h
  rw [hs] at h
  rw [push_none hs]
  exact h

/-- A running step under a bound is also a step of the unbounded machine. -/
theorem step_none {sem : Sem} {D : Option Nat} {p : Prog} {st st' : State}
    (h : step sem D p st = .running st') : step sem none p st = .running st' := by
  revert h
  simp only [step, doTailCall]
  repeat' split
  all_goals first | exact id | exact push_none | exact bump_push_none

theorem run_none {sem : Sem} {D : Option Nat} {p : Prog} :
    ∀ (k : Nat) (c : Conf) (st' : State), run sem D p k c = .running st' →
      run sem none p k c = .running st'
  | 0, _, _, h => h
  | k + 1, .halted r, _, h => by rw [run_halted] at h; cases h
  | k + 1, .running s, st', h => by
    simp only [run] at h ⊢
    cases hs : step sem D p s with
    | running s1 => rw [hs] at h; rw [step_none hs]; exact run_none k _ st' h
    | halted r => rw [hs, run_halted] at h; cases h

theorem reach_run {p : Prog} {D : Option Nat} {a a' : State} {k : Nat} (hr : Reach p a)
    (h : run .preJump D p k (.running a) = .running a') : Reach p a' := by
  obtain ⟨n, hn⟩ := hr
  exact ⟨n + k, by rw [run_add, hn]; exact run_none k _ _ h⟩

/-! ### The step-matching relation -/

/-- Frames kept by `frameReuse`: all but the finalized ones. -/
def keep (f : Frame) : Bool := f.cont != .thenReturn

/-- The related states: same top frame; below it, the `preJump` frames without the finalized
ones; same `nextFid`, events and `unwinding` flag (depth and counters may differ). -/
structure Core (a b : State) : Prop where
  stk : (a.stack = [] ∧ b.stack = []) ∨ ∃ f ps, a.stack = f :: ps ∧ b.stack = f :: ps.filter keep
  nf : b.nextFid = a.nextFid
  ev : b.events = a.events
  uw : b.unwinding = a.unwinding

/-- Matched configurations (`preJump` first): related running states, or halted with the same
outcome and trace, or a `preJump` overflow. -/
def Match (ca cb : Conf) : Prop :=
  (∃ a b, ca = .running a ∧ cb = .running b ∧ Core a b) ∨
  (∃ ra rb, ca = .halted ra ∧ cb = .halted rb ∧ ra.outcome = rb.outcome ∧ ra.events = rb.events) ∨
  (∃ ra, ca = .halted ra ∧ ra.outcome = .stackOverflow)

theorem match_halted {ra rb : Result} (ho : ra.outcome = rb.outcome) (he : ra.events = rb.events) :
    Match (.halted ra) (.halted rb) :=
  Or.inr (Or.inl ⟨ra, rb, rfl, rfl, ho, he⟩)

theorem match_run {a' b' : State} (f : Frame) (ps : List Frame) (ha : a'.stack = f :: ps)
    (hb : b'.stack = f :: ps.filter keep) (hn : b'.nextFid = a'.nextFid)
    (he : b'.events = a'.events) (hu : b'.unwinding = a'.unwinding) :
    Match (.running a') (.running b') :=
  Or.inl ⟨a', b', rfl, rfl, ⟨Or.inr ⟨f, ps, ha, hb⟩, hn, he, hu⟩⟩

theorem match_bump {ca cb : Conf} (h : Match ca cb) : Match (bumpTail ca) (bumpTail cb) := by
  rcases h with ⟨a, b, rfl, rfl, hc⟩ | ⟨ra, rb, rfl, rfl, ho, he⟩ | ⟨ra, rfl, ho⟩
  · exact Or.inl ⟨_, _, rfl, rfl, ⟨hc.stk, hc.nf, hc.ev, hc.uw⟩⟩
  · exact match_halted ho he
  · exact Or.inr (Or.inr ⟨ra, rfl, ho⟩)

theorem filter_keep_fin {z : Frame} {ps : List Frame} (hz : z.cont = .thenReturn) :
    (z :: ps).filter keep = ps.filter keep :=
  List.filter_cons_of_neg (by simp [keep, hz])

theorem filter_keep_keep {z : Frame} {ps : List Frame} (hz : z.cont ≠ .thenReturn) :
    (z :: ps).filter keep = z :: ps.filter keep :=
  List.filter_cons_of_pos (by simp [keep, bne_iff_ne, hz])

theorem run_one (sem : Sem) (D : Option Nat) (p : Prog) (st : State) :
    run sem D p 1 (.running st) = step sem D p st := by
  cases h : step sem D p st with
  | running s => exact (congrArg (run sem D p 0) h : _)
  | halted r => exact (congrArg (run sem D p 0) h : _)

theorem deliver_congr {s1 s2 : State} (stk : List Frame) (v : Val) (hn : s1.nextFid = s2.nextFid)
    (he : s1.events = s2.events) (hm : s1.maxDepth = s2.maxDepth) (ht : s1.tailCalls = s2.tailCalls)
    (hu : s1.unwinding = s2.unwinding) : deliver s1 stk v = deliver s2 stk v := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := s1
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := s2
  simp only at hn he hm ht hu
  subst hn he hm ht hu
  cases stk with
  | nil => rfl
  | cons g rest => simp only [deliver]

/-- Matching an unwinding that continues below a popped frame: the `preJump` run passes the
finalized frames on top of `ps` without events. -/
theorem match_unwind {p : Prog} {D : Option Nat} (sem : Sem) :
    ∀ (ps : List Frame) (sa sb : State),
      (∀ z ∈ ps, z.cont = .thenReturn → ∃ fn, p.fns[z.fn]? = some fn ∧ pendingDrops fn z = []) →
      sb.nextFid = sa.nextFid → sb.events = sa.events →
      ∃ k, Match (run sem D p k (unwindBelow sa ps)) (unwindBelow sb (ps.filter keep))
  | [], sa, sb, _, _, he =>
    ⟨0, by simp only [List.filter_nil, unwindBelow, run, State.halt]; exact match_halted rfl he.symm⟩
  | z :: ps, sa, sb, hfin, hn, he => by
    by_cases hz : z.cont = .thenReturn
    · obtain ⟨fn, hfn, hpd⟩ := hfin z (List.mem_cons_self ..) hz
      rw [filter_keep_fin hz]
      obtain ⟨k, hk⟩ := match_unwind sem ps sa sb
        (fun z' hz' => hfin z' (List.mem_cons_of_mem _ hz')) hn he
      refine ⟨1 + k, ?_⟩
      have h1 : run sem D p 1 (unwindBelow sa (z :: ps)) = unwindBelow sa ps := by
        simp only [unwindBelow, run_one]
        simp only [step, hfn, ↓reduceIte, hpd, dropList]
        cases ps with
        | nil => simp [State.halt]
        | cons y ys => simp
      rw [run_add, h1]
      exact hk
    · rw [filter_keep_keep hz]
      exact ⟨0, by simp only [unwindBelow, run]; exact match_run z ps rfl rfl hn he rfl⟩

/-- Matching the delivery of a returned value: the `preJump` run forwards it through the
finalized frames on top of `ps` without events. -/
theorem match_deliver {p : Prog} {D : Option Nat} (sem : Sem) (v : Val) :
    ∀ (ps : List Frame) (sa sb : State),
      (∀ z ∈ ps, z.cont = .thenReturn → ∃ fn, p.fns[z.fn]? = some fn ∧ pendingDrops fn z = []) →
      sa.unwinding = false → sb.nextFid = sa.nextFid → sb.events = sa.events →
      sb.unwinding = sa.unwinding →
      ∃ k, Match (run sem D p k (deliver sa ps v)) (deliver sb (ps.filter keep) v)
  | [], sa, sb, _, _, _, he, _ =>
    ⟨0, by simp only [List.filter_nil, deliver, run, State.halt]; exact match_halted rfl he.symm⟩
  | z :: ps, sa, sb, hfin, hua, hn, he, hu => by
    by_cases hz : z.cont = .thenReturn
    · obtain ⟨fn, hfn, hpd⟩ := hfin z (List.mem_cons_self ..) hz
      rw [filter_keep_fin hz]
      obtain ⟨k, hk⟩ := match_deliver sem v ps sa sb
        (fun z' hz' => hfin z' (List.mem_cons_of_mem _ hz')) hua hn he hu
      refine ⟨1 + k, ?_⟩
      have h1 : run sem D p 1 (deliver sa (z :: ps) v) = deliver sa ps v := by
        have hd : deliver sa (z :: ps) v =
            .running { sa with stack := { z with pendingRet := some v } :: ps } := by
          simp only [deliver, hz]
        rw [hd, run_one]
        generalize hz' : ({ z with pendingRet := some v } : Frame) = z'
        have hfn' : p.fns[z'.fn]? = some fn := by rw [← hz']; exact hfn
        have hpd'' : pendingDrops fn z' = [] := by rw [← hz']; exact hpd
        have hret' : z'.pendingRet = some v := by rw [← hz']
        simp only [step, hfn', hua, Bool.false_eq_true, ↓reduceIte, hret', doReturn, hpd'', dropList]
        exact deliver_congr ps v (by simp) (by simp) (by simp) (by simp) (by simp [hua])
      rw [run_add, h1]
      exact hk
    · rw [filter_keep_keep hz]
      refine ⟨0, ?_⟩
      simp only [deliver, run]
      cases hc : z.cont with
      | thenReturn => exact absurd hc hz
      | store dst next => exact match_run _ ps rfl rfl hn he hu

theorem match_doReturn {p : Prog} {D : Option Nat} (sem : Sem) {a b : State} (fn : Fn)
    (fr : Frame) (ps : List Frame) (v : Val)
    (hfin : ∀ z ∈ ps, z.cont = .thenReturn → ∃ fn, p.fns[z.fn]? = some fn ∧ pendingDrops fn z = [])
    (hua : a.unwinding = false) (hn : b.nextFid = a.nextFid) (he : b.events = a.events)
    (hu : b.unwinding = a.unwinding) :
    ∃ k, Match (run sem D p k (doReturn a fn fr ps v)) (doReturn b fn fr (ps.filter keep) v) := by
  dsimp only [doReturn]
  cases hr : (dropList fn fr (pendingDrops fn fr) false).2.2 with
  | ok => exact match_deliver sem v ps _ _ hfin hua hn (by simp [he]) hu
  | unwind => exact match_unwind sem ps _ _ hfin hn (by simp [he])
  | abort => exact ⟨0, by simp only [run, State.halt]; exact match_halted rfl (by simp [he])⟩

theorem overflows_mono {D : Option Nat} {m n : Nat} (h : overflows D n = false) (hmn : m ≤ n) :
    overflows D m = false := by
  cases D with
  | none => rfl
  | some d => simp [overflows] at h ⊢; omega

theorem match_push {p : Prog} {D : Option Nat} {sa sb : State} {stka stkb : List Frame}
    {g : FnId} {vs : List Val} (hstk : stkb = stka.filter keep) (hn : sb.nextFid = sa.nextFid)
    (he : sb.events = sa.events) (hu : sb.unwinding = sa.unwinding) :
    Match (push D p sa stka g vs) (push D p sb stkb g vs) := by
  unfold push
  cases hf : p.fns[g]? with
  | none => exact match_halted rfl (by simp [he])
  | some fn =>
    simp only
    split
    · exact match_halted rfl (by simp [he])
    · cases hov : overflows D stka.length with
      | true => simp only [↓reduceIte]; exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)
      | false =>
        have hov' : overflows D stkb.length = false :=
          overflows_mono hov (by rw [hstk]; exact List.length_filter_le _ _)
        simp only [hov', Bool.false_eq_true, ↓reduceIte]
        rw [hn]
        exact match_run _ stka rfl (by rw [hstk]) rfl he hu

theorem find?_filter_of {P Q : Frame → Bool} :
    ∀ (l : List Frame), (∀ x ∈ l, P x = true → Q x = true) → (l.filter Q).find? P = l.find? P
  | [], _ => rfl
  | x :: l, h => by
    have ih := find?_filter_of l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : P x
    · cases hq : Q x
      · simp [List.filter_cons, hq, List.find?_cons, hp, ih]
      · simp [List.filter_cons, hq, List.find?_cons, hp, ih]
    · have hq := h x (List.mem_cons_self ..) hp
      simp [List.filter_cons, hq, List.find?_cons, hp]

theorem findFrame_filter {f : Frame} {ps : List Frame} {fid : Nat}
    (h : ∀ z ∈ ps, z.cont = .thenReturn → z.fid ≠ fid) :
    findFrame (f :: ps.filter keep) fid = findFrame (f :: ps) fid := by
  unfold findFrame
  simp only [List.find?_cons]
  split
  · rfl
  · apply find?_filter_of
    intro x hx hp
    simp only [beq_iff_eq] at hp
    simp only [keep, bne_iff_ne, ne_eq]
    intro hc
    exact h x hx hc hp

theorem evalOp_eq {ps : List Frame} {f : Frame}
    (hg : ∀ z ∈ ps, z.cont = .thenReturn → ∀ w ∈ f.vals, w.pointsInto z.fid = false) (o : Operand) :
    evalOp (ps.filter keep) f o = evalOp ps f o := by
  cases o with
  | deref s =>
    simp only [evalOp]
    cases hget : f.get s with
    | ptr fid j =>
      simp only
      rw [findFrame_filter]
      intro z hz hzc heq
      have := get_noPtr (hg z hz hzc) s
      rw [hget] at this
      simp [Val.pointsInto, heq] at this
    | int n => rfl
    | undef => rfl
  | _ => rfl

theorem evalOps_eq {ps : List Frame} :
    ∀ (f : Frame), (∀ z ∈ ps, z.cont = .thenReturn → ∀ w ∈ f.vals, w.pointsInto z.fid = false) →
      ∀ (os : List Operand), evalOps (ps.filter keep) f os = evalOps ps f os
  | _, _, [] => rfl
  | f, hg, o :: os => by
    simp only [evalOps]
    rw [evalOp_eq hg o]
    cases hev : evalOp ps f o with
    | none => rfl
    | some vf =>
      obtain ⟨v, f1⟩ := vf
      simp only
      have hf := evalOp_frame hev
      rw [evalOps_eq f1 (by rw [hf.1]; exact hg) os]

theorem step_unw {sem : Sem} {D : Option Nat} {p : Prog} {st : State} {f : Frame}
    {rest : List Frame} {fn : Fn} (hs : st.stack = f :: rest) (hfn : p.fns[f.fn]? = some fn)
    (hu : st.unwinding = true) (hr : (dropList fn f (pendingDrops fn f) true).2.2 ≠ .abort) :
    step sem D p st =
      unwindBelow { st with events := st.events ++ (dropList fn f (pendingDrops fn f) true).2.1 }
        rest := by
  simp only [step, hs, hfn, hu, ↓reduceIte]
  revert hr
  generalize dropList fn f (pendingDrops fn f) true = d
  obtain ⟨f', evs, e⟩ := d
  intro hr
  cases e with
  | abort => exact absurd rfl hr
  | ok =>
    cases rest with
    | nil => rfl
    | cons y ys => simp only [unwindBelow]
  | unwind =>
    cases rest with
    | nil => rfl
    | cons y ys => simp only [unwindBelow]

/-! ### Step matching -/

/-- Every `frameReuse` step from a related pair is matched by at least one `preJump` step. -/
theorem sim_step {p : Prog} {D : Option Nat} (hnb : NoStackBorrow p) {a b : State}
    (hr : Reach p a) (hc : Core a b) :
    ∃ k, 0 < k ∧ Match (run .preJump D p k (.running a)) (step .frameReuse D p b) := by
  obtain ⟨n0, hn0⟩ := hr
  have hinv := pinv_reach hnb n0 a hn0
  suffices h : ∃ k, Match (run .preJump D p k (step .preJump D p a)) (step .frameReuse D p b) by
    obtain ⟨k, hk⟩ := h
    exact ⟨1 + k, by omega, by rw [run_add, run_one]; exact hk⟩
  rcases hc.stk with ⟨ha, hb⟩ | ⟨f, ps, ha, hb⟩
  · exact ⟨0, by simp only [run, step, ha, hb]; exact match_halted rfl (by simp [State.halt, hc.ev])⟩
  have hfin : ∀ z ∈ ps, z.cont = .thenReturn →
      ∃ fn, p.fns[z.fn]? = some fn ∧ pendingDrops fn z = [] :=
    fun z hz hzc => (hinv.fin f ps ha z hz hzc).2
  have hg : ∀ z ∈ ps, z.cont = .thenReturn → ∀ w ∈ f.vals, w.pointsInto z.fid = false := by
    have g := hinv.guard
    rw [ha, List.pairwise_cons] at g
    exact fun z hz hzc => (g.1 z hz hzc).1
  have heo := evalOp_eq hg
  have heos := evalOps_eq f hg
  cases hfn : p.fns[f.fn]? with
  | none =>
    exact ⟨0, by simp only [run, step, ha, hb, hfn]; exact match_halted rfl (by simp [State.halt, hc.ev])⟩
  | some fn =>
  by_cases hu : a.unwinding = true
  · have hub : b.unwinding = true := by rw [hc.uw]; exact hu
    cases hr : (dropList fn f (pendingDrops fn f) true).2.2 with
    | abort =>
      exact ⟨0, by
        simp only [run, step, ha, hb, hfn, hu, hub, ↓reduceIte, hr]
        exact match_halted rfl (by simp [State.halt, hc.ev])⟩
    | ok =>
      rw [step_unw ha hfn hu (by rw [hr]; simp), step_unw hb hfn hub (by rw [hr]; simp)]
      exact match_unwind _ ps _ _ hfin hc.nf (by simp [hc.ev])
    | unwind =>
      rw [step_unw ha hfn hu (by rw [hr]; simp), step_unw hb hfn hub (by rw [hr]; simp)]
      exact match_unwind _ ps _ _ hfin hc.nf (by simp [hc.ev])
  · have hua : a.unwinding = false := by simpa using hu
    have hub : b.unwinding = false := by rw [hc.uw]; exact hua
    cases hret : f.pendingRet with
    | some v =>
      have e1 : step .preJump D p a = doReturn a fn f ps v := by
        simp only [step, ha, hfn, hua, Bool.false_eq_true, ↓reduceIte, hret]
      have e2 : step .frameReuse D p b = doReturn b fn f (ps.filter keep) v := by
        simp only [step, hb, hfn, hub, Bool.false_eq_true, ↓reduceIte, hret]
      rw [e1, e2]
      exact match_doReturn _ fn f ps v hfin hua hc.nf hc.ev hc.uw
    | none =>
      cases hcode : fn.code[f.pc]? with
      | none =>
        exact ⟨0, by
          simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
          exact match_halted rfl (by simp [State.halt, hc.ev])⟩
      | some i =>
        cases i with
        | assign dst op next =>
          refine ⟨0, ?_⟩
          simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode,
            heo]
          cases hev : evalOp ps f op with
          | none => exact match_halted rfl (by simp [State.halt, hc.ev])
          | some vf =>
            obtain ⟨v, f1⟩ := vf
            simp only
            by_cases hdst : dst < f1.vals.length
            · simp only [hdst, ↓reduceIte]
              exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])
            · simp only [hdst, ↓reduceIte]
              exact match_halted rfl (by simp [State.halt, hc.ev])
        | emit k next =>
          exact ⟨0, by
            simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
            exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])⟩
        | branchLt s0 k t e =>
          refine ⟨0, ?_⟩
          simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
          cases hget : f.get s0 with
          | int n => exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])
          | ptr x y => exact match_halted rfl (by simp [State.halt, hc.ev])
          | undef => exact match_halted rfl (by simp [State.halt, hc.ev])
        | goto next =>
          exact ⟨0, by
            simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
            exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])⟩
        | reset ss next =>
          exact ⟨0, by
            simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
            exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])⟩
        | dropSlots ss next =>
          refine ⟨0, ?_⟩
          simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
          cases hr : (dropList fn f (ss.filter (fun s => f.isLive s && fn.dtor s != .none)) false).2.2 with
          | ok => exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])
          | unwind => exact match_run _ ps rfl rfl (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])
          | abort => exact match_halted rfl (by simp [State.halt, hc.ev])
        | call g args dst next =>
          refine ⟨0, ?_⟩
          simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode,
            heos]
          cases hev : evalOps ps f args with
          | none => exact match_halted rfl (by simp [State.halt, hc.ev])
          | some vf =>
            obtain ⟨vs, f1⟩ := vf
            simp only
            by_cases hdst : dst < f1.vals.length
            · simp only [hdst, ↓reduceIte]
              exact match_push (filter_keep_keep (by simp)).symm hc.nf hc.ev hc.uw
            · simp only [hdst, ↓reduceIte]
              exact match_halted rfl (by simp [State.halt, hc.ev])
        | ret op =>
          cases hev : evalOp ps f op with
          | none =>
            exact ⟨0, by
              simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret,
                hcode, heo, hev]
              exact match_halted rfl (by simp [State.halt, hc.ev])⟩
          | some vf =>
            obtain ⟨v, f1⟩ := vf
            have e1 : step .preJump D p a = doReturn a fn f1 ps v := by
              simp only [step, ha, hfn, hua, Bool.false_eq_true, ↓reduceIte, hret, hcode, hev]
            have e2 : step .frameReuse D p b = doReturn b fn f1 (ps.filter keep) v := by
              simp only [step, hb, hfn, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode, heo, hev]
            rw [e1, e2]
            exact match_doReturn _ fn f1 ps v hfin hua hc.nf hc.ev hc.uw
        | tailCall g args =>
          cases hev : evalOps ps f args with
          | none =>
            exact ⟨0, by
              simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret,
                hcode, heos, hev]
              exact match_halted rfl (by simp [State.halt, hc.ev])⟩
          | some vf =>
            obtain ⟨vs, f1⟩ := vf
            have e1 : step .preJump D p a = doTailCall .preJump D p a fn f1 ps g vs := by
              simp only [step, ha, hfn, hua, Bool.false_eq_true, ↓reduceIte, hret, hcode, hev]
            have e2 : step .frameReuse D p b = doTailCall .frameReuse D p b fn f1 (ps.filter keep) g vs := by
              simp only [step, hb, hfn, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode, heos, hev]
            rw [e1, e2]
            dsimp only [doTailCall]
            cases hr : (dropList fn f1 (pendingDrops fn f1) false).2.2 with
            | ok =>
              refine ⟨0, ?_⟩
              simp only [run]
              exact match_bump (match_push (filter_keep_fin rfl).symm hc.nf (by simp [hc.ev]) hc.uw)
            | unwind => exact match_unwind _ ps _ _ hfin hc.nf (by simp [hc.ev])
            | abort => exact ⟨0, by simp only [run]; exact match_halted rfl (by simp [State.halt, hc.ev])⟩
        | panic =>
          exact ⟨0, by
            simp only [run, step, ha, hb, hfn, hua, hub, Bool.false_eq_true, ↓reduceIte, hret, hcode]
            exact match_run f ps (by simp [ha]) (by simp [hb]) (by simp [hc.nf]) (by simp [hc.ev]) (by simp [hc.uw])⟩

/-! ### Transfer of halted runs -/

theorem fwd {p : Prog} {D : Option Nat} (hnb : NoStackBorrow p) :
    ∀ (n : Nat) (a b : State) (rb : Result), Reach p a → Core a b →
      run .frameReuse D p n (.running b) = .halted rb →
      ∃ m ra, run .preJump D p m (.running a) = .halted ra ∧
        ((ra.outcome = rb.outcome ∧ ra.events = rb.events) ∨ ra.outcome = .stackOverflow)
  | 0, _, _, _, _, _, h => by simp [run] at h
  | n + 1, a, b, rb, hr, hc, h => by
    simp only [run] at h
    obtain ⟨k, -, hk⟩ := sim_step (D := D) hnb hr hc
    rcases hk with ⟨a', b', ha', hb', hc'⟩ | ⟨ra, rb', ha', hb', ho, he⟩ | ⟨ra, ha', ho⟩
    · rw [hb'] at h
      obtain ⟨m, ra, hm, hres⟩ := fwd hnb n a' b' rb (reach_run hr ha') hc' h
      exact ⟨k + m, ra, by rw [run_add, ha', hm], hres⟩
    · rw [hb', run_halted] at h
      cases h
      exact ⟨k, ra, ha', Or.inl ⟨ho, he⟩⟩
    · exact ⟨k, ra, ha', Or.inr ho⟩

theorem run_det {sem : Sem} {D : Option Nat} {p : Prog} {c : Conf} {m k : Nat} {r r' : Result}
    (h1 : run sem D p m c = .halted r) (h2 : run sem D p k c = .halted r') : r = r' := by
  rcases Nat.lt_or_ge m k with hlt | hge
  · have := run_mono sem D p m (k - m) _ _ h1
    rw [show m + (k - m) = k by omega, h2] at this
    exact (Conf.halted.inj this).symm
  · have := run_mono sem D p k (m - k) _ _ h2
    rw [show k + (m - k) = m by omega, h1] at this
    exact Conf.halted.inj this

theorem bwd {p : Prog} {D : Option Nat} (hnb : NoStackBorrow p) (M : Nat) :
    ∀ (m : Nat) (a b : State) (ra : Result), m ≤ M → Reach p a → Core a b →
      run .preJump D p m (.running a) = .halted ra → ra.outcome ≠ .stackOverflow →
      ∃ n rb, run .frameReuse D p n (.running b) = .halted rb ∧
        rb.outcome = ra.outcome ∧ rb.events = ra.events := by
  induction M with
  | zero =>
    intro m a b ra hm _ _ h _
    have : m = 0 := by omega
    subst this
    simp [run] at h
  | succ M ih =>
    intro m a b ra hmM hr hc hm hso
    obtain ⟨k, hk0, hk⟩ := sim_step (D := D) hnb hr hc
    rcases hk with ⟨a', b', ha', hb', hc'⟩ | ⟨ra', rb, ha', hb', ho, he⟩ | ⟨ra', ha', ho⟩
    · rcases Nat.lt_or_ge m k with hlt | hge
      · exfalso
        have := run_mono .preJump D p m (k - m) _ _ hm
        rw [show m + (k - m) = k by omega, ha'] at this
        cases this
      · have h2 : run .preJump D p (m - k) (.running a') = .halted ra := by
          rw [← ha', ← run_add, show k + (m - k) = m by omega]
          exact hm
        obtain ⟨n, rb, hn, ho, he⟩ :=
          ih (m - k) a' b' ra (by omega) (reach_run hr ha') hc' h2 hso
        exact ⟨n + 1, rb, by simp only [run]; rw [hb']; exact hn, ho, he⟩
    · have := run_det ha' hm
      subst this
      exact ⟨1, rb, by rw [run_one, hb'], ho.symm, he.symm⟩
    · have := run_det ha' hm
      subst this
      exact absurd ho hso

theorem start_shape {D : Option Nat} {p : Prog} {s : State} (h : start D p = .running s) :
    ∃ f, s.stack = [f] := by
  unfold start push at h
  split at h
  · simp [State.halt] at h
  · split at h
    · simp [State.halt] at h
    · split at h
      · simp [State.halt] at h
      · simp only [Conf.running.injEq] at h
        subst h
        exact ⟨_, rfl⟩

theorem core_refl {s : State} {f : Frame} (h : s.stack = [f]) : Core s s :=
  ⟨Or.inr ⟨f, [], h, by simp [h]⟩, rfl, rfl, rfl⟩

theorem reach_start {D : Option Nat} {p : Prog} {s : State} (h : start D p = .running s) :
    Reach p s :=
  ⟨0, push_none h⟩

/-- The bounded transfer (card R3). -/
theorem transfer {p : Prog} (hnb : NoStackBorrow p) (D : Option Nat) (o : Outcome)
    (es : List Event) (hso : o ≠ .stackOverflow) :
    Observes .preJump D p o es → Observes .frameReuse D p o es := by
  rintro ⟨ra, ⟨m, hm⟩, ho, he⟩
  cases hs : start D p with
  | halted r =>
    rw [hs, run_halted] at hm
    cases hm
    exact ⟨ra, ⟨0, by simp only [run, hs]⟩, ho, he⟩
  | running s =>
    rw [hs] at hm
    obtain ⟨f, hf⟩ := start_shape hs
    obtain ⟨n, rb, hn, ho', he'⟩ :=
      bwd hnb m m s s ra (Nat.le_refl _) (reach_start hs) (core_refl hf) hm (by rw [ho]; exact hso)
    exact ⟨rb, ⟨n, by rw [hs]; exact hn⟩, by rw [ho', ho], by rw [he', he]⟩

theorem step_none_ne_so {sem : Sem} {p : Prog} {st : State} {r : Result}
    (h : step sem none p st = .halted r) : r.outcome ≠ .stackOverflow := by
  simp only [step, doTailCall, doReturn, deliver, unwindBelow, State.halt, bumpTail, push,
    overflows] at h
  repeat' (split at h)
  all_goals first
    | (simp at h; done)
    | (simp only [Conf.halted.injEq] at h; subst h; simp)

theorem run_none_ne_so {sem : Sem} {p : Prog} :
    ∀ (n : Nat) (c : Conf) (r : Result), (∀ r', c = .halted r' → r'.outcome ≠ .stackOverflow) →
      run sem none p n c = .halted r → r.outcome ≠ .stackOverflow
  | 0, c, r, hc, h => hc r h
  | n + 1, .halted r', r, hc, h => by rw [run_halted] at h; cases h; exact hc _ rfl
  | n + 1, .running s, r, _, h => by
    simp only [run] at h
    exact run_none_ne_so n _ r (fun r' hr' => step_none_ne_so hr') h

theorem never_so {sem : Sem} {p : Prog} {r : Result} (h : RunsTo sem none p r) :
    r.outcome ≠ .stackOverflow := by
  obtain ⟨n, hn⟩ := h
  refine run_none_ne_so n _ r ?_ hn
  intro r' hr'
  unfold start push at hr'
  split at hr'
  · simp only [State.halt, Conf.halted.injEq] at hr'; subst hr'; simp
  · split at hr'
    · simp only [State.halt, Conf.halted.injEq] at hr'; subst hr'; simp
    · simp [overflows] at hr'

/-- The unbounded equivalence (card R1). -/
theorem equiv {p : Prog} (hnb : NoStackBorrow p) (o : Outcome) (es : List Event) :
    Observes .frameReuse none p o es ↔ Observes .preJump none p o es := by
  constructor
  · rintro ⟨rb, ⟨n, hn⟩, ho, he⟩
    cases hs : start none p with
    | halted r =>
      rw [hs, run_halted] at hn
      cases hn
      exact ⟨rb, ⟨0, by simp only [run, hs]⟩, ho, he⟩
    | running s =>
      rw [hs] at hn
      obtain ⟨f, hf⟩ := start_shape hs
      obtain ⟨m, ra, hm, hres⟩ := fwd hnb n s s rb (reach_start hs) (core_refl hf) hn
      have hra : RunsTo .preJump none p ra := ⟨m, by rw [hs]; exact hm⟩
      rcases hres with ⟨h1, h2⟩ | hso
      · exact ⟨ra, hra, by rw [h1, ho], by rw [h2, he]⟩
      · exact absurd hso (never_so hra)
  · rintro ⟨ra, hra, ho, he⟩
    have hso : o ≠ .stackOverflow := by rw [← ho]; exact never_so hra
    exact transfer hnb none o es hso ⟨ra, hra, ho, he⟩

end Toy.TailCall.ReuseProof
