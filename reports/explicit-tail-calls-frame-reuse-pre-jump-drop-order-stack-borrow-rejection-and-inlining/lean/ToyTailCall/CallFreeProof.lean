import ToyTailCall.Machine
import ToyTailCall.Lemmas

/-!
# Proof support: maximum depth of call-free programs
-/

namespace Toy.TailCall.CallFreeProof

open Toy.TailCall

set_option linter.unusedSimpArgs false


theorem bumpTail_running' {c : Conf} {st' : State} (h : bumpTail c = .running st') :
    ∃ st'', c = .running st'' ∧ st' = { st'' with tailCalls := st''.tailCalls + 1 } := by
  cases c with
  | running s => exact ⟨s, rfl, by simp [bumpTail] at h; exact h.symm⟩
  | halted r => simp [bumpTail] at h

theorem push_running' {D p st stk f args st'} (h : push D p st stk f args = .running st') :
    ∃ fr, st'.stack = fr :: stk ∧ fr.cont = .thenReturn ∧ fr.pendingRet = none ∧
      st'.maxDepth = max st.maxDepth (stk.length + 1) ∧ st'.tailCalls = st.tailCalls ∧
      st'.unwinding = st.unwinding := by
  unfold push at h
  split at h
  · simp [State.halt] at h
  · split at h
    · simp [State.halt] at h
    · split at h
      · simp [State.halt] at h
      · simp only [Conf.running.injEq] at h
        subst h
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

def Inv1 (st : State) : Prop := st.stack.length ≤ 1 ∧ st.maxDepth = 1

theorem inv1_step (p : Prog) (hcf : ∀ (i : Nat) (fn : Fn) (j : Nat) (c : Instr), p.fns[i]? = some fn → fn.code[j]? = some c →
      ∀ f a d n, c ≠ Instr.call f a d n)
    (st st' : State) (hinv : Inv1 st) (h : step .frameReuse none p st = .running st') : Inv1 st' := by
  obtain ⟨hlen, hmd⟩ := hinv
  simp only [step, doTailCall, doReturn, deliver, unwindBelow, State.halt] at h
  repeat' (split at h)
  all_goals (try (simp only [Conf.running.injEq] at h; subst h))
  all_goals (try (simp_all [Inv1]; done))
  all_goals (try (simp_all [Inv1]; omega))
  all_goals (try (exfalso; exact hcf _ _ _ _ ‹_› ‹_› _ _ _ _ rfl))
  all_goals (obtain ⟨st'', hp, rfl⟩ := bumpTail_running' h)
  all_goals (obtain ⟨fr, hs', -, -, hmd', -, -⟩ := push_running' hp)
  all_goals (first | (simp_all [Inv1]; done) | (simp_all [Inv1]; omega))

theorem evalOp_meta {below fr op v fr'} (h : evalOp below fr op = some (v, fr')) :
    fr'.cont = fr.cont ∧ fr'.pendingRet = fr.pendingRet := by
  unfold evalOp at h
  repeat' split at h
  all_goals (first | (simp at h; done) | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp [Frame.kill]))

theorem evalOps_meta {below fr os vs fr'} (h : evalOps below fr os = some (vs, fr')) :
    fr'.cont = fr.cont ∧ fr'.pendingRet = fr.pendingRet := by
  induction os generalizing fr vs with
  | nil => simp [evalOps] at h; obtain ⟨-, rfl⟩ := h; simp
  | cons o os ih =>
    simp only [evalOps] at h
    split at h
    · simp at h
    · rename_i v fr1 h1
      split at h
      · simp at h
      · rename_i vs' fr2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have a := evalOp_meta h1
        have b := ih h2
        exact ⟨b.1.trans a.1, b.2.trans a.2⟩

theorem dropList_meta (fn : Fn) (fr : Frame) (ss : List Slot) (unw : Bool) :
    (dropList fn fr ss unw).1.cont = fr.cont ∧ (dropList fn fr ss unw).1.pendingRet = fr.pendingRet := by
  induction ss generalizing fr unw with
  | nil => simp [dropList]
  | cons s ss ih =>
    simp only [dropList]
    split
    · split
      · simp [Frame.kill]
      · have := ih (fr.kill s) true; simpa [Frame.kill] using this
    · have := ih (fr.kill s) unw; simpa [Frame.kill] using this

theorem foldl_clear_meta (ss : List Slot) (fr : Frame) :
    (ss.foldl Frame.clear fr).cont = fr.cont ∧ (ss.foldl Frame.clear fr).pendingRet = fr.pendingRet := by
  induction ss generalizing fr with
  | nil => simp
  | cons s ss ih => have := ih (fr.clear s); simpa [Frame.clear] using this

def Inv2 (st : State) : Prop :=
  st.maxDepth = st.tailCalls + 1 ∧ st.stack.length ≤ st.maxDepth ∧
    (st.unwinding = false → ∀ fr rest, st.stack = fr :: rest → fr.pendingRet = none →
      st.stack.length = st.maxDepth) ∧
    (∀ fr ∈ st.stack, fr.cont = .thenReturn)

theorem inv2_step (p : Prog) (hcf : ∀ (i : Nat) (fn : Fn) (j : Nat) (c : Instr), p.fns[i]? = some fn → fn.code[j]? = some c →
      ∀ f a d n, c ≠ Instr.call f a d n)
    (st st' : State) (hinv : Inv2 st) (h : step .preJump none p st = .running st') : Inv2 st' := by
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  simp only [step, doTailCall, doReturn, deliver, unwindBelow, State.halt] at h
  repeat' (split at h)
  all_goals (try (exfalso; exact hcf _ _ _ _ ‹_› ‹_› _ _ _ _ rfl))
  all_goals (try (simp only [Conf.running.injEq] at h; subst h))
  all_goals (try (simp at h; done))
  all_goals (try (obtain ⟨st'', hp, rfl⟩ := bumpTail_running' h; obtain ⟨frn, hs', hc', hp', hmd', htc', hu'⟩ := push_running' hp))
  all_goals (try (have hm1 := evalOp_meta ‹evalOp _ _ _ = some _›))
  all_goals (try (have hm2 := evalOps_meta ‹evalOps _ _ _ = some _›))
  all_goals (first
    | (simp_all [Inv2, dropList_meta, foldl_clear_meta, Frame.write, Frame.kill]; done)
    | (simp_all [Inv2, dropList_meta, foldl_clear_meta, Frame.write, Frame.kill]; omega))

theorem step_halted_meta (sem : Sem) (D : Option Nat) (p : Prog) (st : State) (r : Result)
    (h : step sem D p st = .halted r) : r.maxDepth = st.maxDepth ∧ r.tailCalls = st.tailCalls := by
  simp only [step, doTailCall, doReturn, deliver, unwindBelow, State.halt, bumpTail, push] at h
  repeat' (split at h)
  all_goals (first | (simp at h; done) | (simp only [Conf.halted.injEq] at h; subst h; simp) | skip)

theorem callFree_spec {p : Prog} (hcf : CallFree p = true) :
    ∀ (i : Nat) (fn : Fn) (j : Nat) (c : Instr), p.fns[i]? = some fn → fn.code[j]? = some c →
      ∀ f a d n, c ≠ Instr.call f a d n := by
  intro i fn j c hfn hc f a d n hcall
  subst hcall
  simp only [CallFree, List.all_eq_true] at hcf
  have h1 := hcf fn (List.mem_of_getElem? hfn) _ (List.mem_of_getElem? hc)
  simp at h1

theorem start_eq {p : Prog} (he : EntryOk p) :
    ∃ fr, start none p = .running ⟨[fr], 1, [], 1, 0, false⟩ ∧ fr.cont = .thenReturn ∧
      fr.pendingRet = none := by
  obtain ⟨fn, hfn, hnp⟩ := he
  have h : start none p = .running ⟨[⟨0, 0, 0, List.replicate fn.nSlots .undef,
      List.replicate fn.nSlots false, .thenReturn, none⟩], 1, [], 1, 0, false⟩ := by
    simp [start, push, hfn, hnp, overflows, State.empty]
  exact ⟨_, h, rfl, rfl⟩

theorem run_inv (Inv : State → Prop) (sem : Sem) (p : Prog)
    (hstep : ∀ st st', Inv st → step sem none p st = .running st' → Inv st') :
    ∀ n st r, Inv st → run sem none p n (.running st) = .halted r →
      ∃ st', Inv st' ∧ r.maxDepth = st'.maxDepth ∧ r.tailCalls = st'.tailCalls := by
  intro n
  induction n with
  | zero => intro st r _ h; simp [run] at h
  | succ n ih =>
    intro st r hinv h
    simp only [run] at h
    cases hs : step sem none p st with
    | running st' => rw [hs] at h; exact ih st' r (hstep st st' hinv hs) h
    | halted r' =>
      rw [hs, run_halted] at h
      cases h
      exact ⟨st, hinv, step_halted_meta sem none p st r hs⟩

theorem frameReuse_maxDepth (p : Prog) (hcf : CallFree p = true) (he : EntryOk p) (r : Result)
    (hr : RunsTo .frameReuse none p r) : r.maxDepth = 1 := by
  obtain ⟨fr, hst, -, -⟩ := start_eq he
  obtain ⟨n, hn⟩ := hr
  rw [hst] at hn
  cases n with
  | zero => simp [run] at hn
  | succ n =>
    obtain ⟨st', ⟨-, hmd⟩, hr', -⟩ := run_inv Inv1 .frameReuse p
      (inv1_step p (callFree_spec hcf)) (n + 1) _ r ⟨by simp, rfl⟩ hn
    rw [hr', hmd]

theorem preJump_maxDepth (p : Prog) (hcf : CallFree p = true) (he : EntryOk p) (r : Result)
    (hr : RunsTo .preJump none p r) : r.maxDepth = r.tailCalls + 1 := by
  obtain ⟨fr, hst, hc, hpr⟩ := start_eq he
  obtain ⟨n, hn⟩ := hr
  rw [hst] at hn
  obtain ⟨st', ⟨h1, -, -, -⟩, hr', htc⟩ := run_inv Inv2 .preJump p
    (inv2_step p (callFree_spec hcf)) n _ r
    ⟨rfl, by simp, fun _ _ _ hs _ => by simp at hs ⊢, by simp [hc]⟩ hn
  rw [hr', htc, h1]

end Toy.TailCall.CallFreeProof
