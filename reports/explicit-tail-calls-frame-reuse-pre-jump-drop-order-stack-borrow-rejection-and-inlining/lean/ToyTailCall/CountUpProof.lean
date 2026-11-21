import ToyTailCall.Machine
import ToyTailCall.Examples
import ToyTailCall.Lemmas

/-!
# Proof support: runs of `countUp N`
-/

namespace Toy.TailCall.CountUpProof

open Toy.TailCall

/-- `main`'s frame while it waits for `rec 0`. -/
def mainFr : Frame := ⟨0, 0, 0, [.undef], [false], .store 0 1, none⟩

/-- A fresh frame of `rec n` with identity `fid`. -/
def recFr (n fid : Nat) : Frame := ⟨fid, 1, 0, [.int n, .undef, .undef], [true, false, false], .thenReturn, none⟩

theorem range3_eq : List.range 3 = [0, 1, 2] := rfl

theorem start_eq (N : Nat) :
    start none (countUp N) =
      .running ⟨[⟨0, 0, 0, [.undef], [false], .thenReturn, none⟩], 1, [], 1, 0, false⟩ := by
  simp [start, push, countUp, overflows, Fn.nSlots, State.empty]

theorem first_step (sem : Sem) (N : Nat) :
    step sem none (countUp N) ⟨[⟨0, 0, 0, [.undef], [false], .thenReturn, none⟩], 1, [], 1, 0, false⟩ =
      .running ⟨[recFr 0 1, mainFr], 2, [], 2, 0, false⟩ := by
  simp [step, countUp, mainFr, recFr, evalOps, evalOp, push, overflows, Fn.nSlots]

/-! ### `frameReuse` -/

theorem frameReuse_iter (N n fid : Nat) (es : List Event) (tc : Nat) (hlt : n < N) :
    run .frameReuse none (countUp N) 4 (.running ⟨[recFr n fid, mainFr], fid + 1, es, 2, tc, false⟩) =
      .running ⟨[recFr (n + 1) (fid + 1), mainFr], fid + 2, es ++ [.drop n], 2, tc + 1, false⟩ := by
  simp [run, step, countUp, mainFr, recFr, Frame.get, hlt, evalOp, evalOps, Frame.write,
    Frame.kill, doTailCall, dropList, pendingDrops, range3_eq, Frame.isLive, Fn.dtor,
    Fn.nSlots, push, overflows, bumpTail, Val.obs]

theorem frameReuse_loop (N : Nat) :
    ∀ (k n fid : Nat) (es : List Event) (tc : Nat), n + k = N →
      run .frameReuse none (countUp N) (4 * k + 3)
        (.running ⟨[recFr n fid, mainFr], fid + 1, es, 2, tc, false⟩) =
      .halted ⟨.returned 0, es ++ (List.range' n k).map Event.drop, 2, tc + k⟩ := by
  intro k
  induction k with
  | zero =>
    intro n fid es tc hnk
    have hlt : ¬ n < N := by omega
    simp [run, step, countUp, mainFr, recFr, Frame.get, hlt, evalOp, doReturn, dropList,
      pendingDrops, range3_eq, Frame.isLive, Fn.dtor, deliver, Frame.write,
      Frame.kill, State.halt, Val.obs]
  | succ k ih =>
    intro n fid es tc hnk
    have hlt : n < N := by omega
    have h4 : 4 * (k + 1) + 3 = 4 + (4 * k + 3) := by omega
    rw [h4, run_add, frameReuse_iter N n fid es tc hlt]
    have := ih (n + 1) (fid + 1) (es ++ [.drop n]) (tc + 1) (by omega)
    simpa [List.range'_succ, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using this

theorem frameReuse_runsTo (N : Nat) :
    RunsTo .frameReuse none (countUp N) ⟨.returned 0, (List.range N).map Event.drop, 2, N⟩ := by
  refine ⟨1 + (4 * N + 3), ?_⟩
  rw [start_eq, run_add]
  have hrun1 : run .frameReuse none (countUp N) 1
      (.running ⟨[⟨0, 0, 0, [.undef], [false], .thenReturn, none⟩], 1, [], 1, 0, false⟩) =
      .running ⟨[recFr 0 1, mainFr], 2, [], 2, 0, false⟩ := by
    simp [run, first_step]
  rw [hrun1]
  have hloop := frameReuse_loop N N 0 1 [] 0 (Nat.zero_add N)
  simpa [List.range_eq_range'] using hloop

/-! ### `preJump` and `callReturn`: frames left below the running `rec` frame -/

/-- The frame of `rec m` (identity `fid`) left below its callee after `tailCall`: under
`preJump` its local has been dropped (`dropped = true`), under `callReturn` it still owns it. -/
def waitFr (dropped : Bool) (m fid : Nat) : Frame :=
  ⟨fid, 1, 3, [.int m, .int m, .int (m + 1)], [true, !dropped, false], .thenReturn, none⟩

/-- The frames left by `rec 0, …, rec (k - 1)` (innermost first). -/
def waits (dropped : Bool) : Nat → List Frame
  | 0 => []
  | k + 1 => waitFr dropped k (k + 1) :: waits dropped k

theorem waits_length (dropped : Bool) (k : Nat) : (waits dropped k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [waits, ih]

/-- The state with `rec m` running above the frames of `rec 0, …, rec (m - 1)`. -/
def upState (dropped : Bool) (m : Nat) (es : List Event) : State :=
  ⟨recFr m (m + 1) :: waits dropped m ++ [mainFr], m + 2, es, m + 2, m, false⟩

theorem preJump_iter (N m : Nat) (hlt : m < N) :
    Reaches .preJump none (countUp N)
      (.running (upState true m ((List.range m).map Event.drop)))
      (.running (upState true (m + 1) ((List.range (m + 1)).map Event.drop))) := by
  refine ⟨4, ?_⟩
  simp [upState, run, step, countUp, mainFr, recFr, Frame.get, hlt, evalOp, evalOps, Frame.write,
    Frame.kill, doTailCall, dropList, pendingDrops, Frame.isLive, Fn.dtor,
    Fn.nSlots, push, overflows, bumpTail, Val.obs, waits, waitFr, waits_length, List.range_succ]

theorem callReturn_iter (N m : Nat) (hlt : m < N) :
    Reaches .callReturn none (countUp N)
      (.running (upState false m []))
      (.running (upState false (m + 1) [])) := by
  refine ⟨4, ?_⟩
  simp [upState, run, step, countUp, mainFr, recFr, Frame.get, hlt, evalOp, evalOps, Frame.write,
    Frame.kill, doTailCall,
    Fn.nSlots, push, overflows, bumpTail, waits, waitFr, waits_length]

theorem up (dropped : Bool) (sem : Sem) (N : Nat)
    (hiter : ∀ m, m < N → Reaches sem none (countUp N)
      (.running (upState dropped m (if dropped then (List.range m).map Event.drop else [])))
      (.running (upState dropped (m + 1)
        (if dropped then (List.range (m + 1)).map Event.drop else [])))) :
    ∀ m, m ≤ N → Reaches sem none (countUp N) (.running (upState dropped 0 []))
      (.running (upState dropped m (if dropped then (List.range m).map Event.drop else []))) := by
  intro m
  induction m with
  | zero => intro _; cases dropped <;> exact Reaches.refl _ _ _ _
  | succ m ih => intro hm; exact (ih (by omega)).trans (hiter m (by omega))

/-- `main` after receiving `0` from `rec 0`. -/
def mainRecv : Frame := ⟨0, 0, 1, [.int 0], [true], .store 0 1, none⟩

/-- The return cascade: the frame of `rec (j - 1)` has received `0` (or, for `j = 0`, `main`
has). -/
def downState (dropped : Bool) (N j : Nat) (es : List Event) : State :=
  match j with
  | 0 => ⟨[mainRecv], N + 2, es, N + 2, N, false⟩
  | j + 1 => ⟨{ waitFr dropped j (j + 1) with pendingRet := some (.int 0) } :: waits dropped j ++
      [mainFr], N + 2, es, N + 2, N, false⟩

theorem top (dropped : Bool) (sem : Sem) (N : Nat) (es : List Event) :
    Reaches sem none (countUp N) (.running (upState dropped N es))
      (.running (downState dropped N N es)) := by
  refine ⟨2, ?_⟩
  cases N <;>
  simp [upState, downState, run, step, countUp, mainFr, mainRecv, recFr, Frame.get, evalOp,
    doReturn, dropList, pendingDrops, range3_eq, Frame.isLive, Fn.dtor, deliver, Frame.write,
    waits, waitFr]

theorem final (dropped : Bool) (sem : Sem) (N : Nat) (es : List Event) :
    Reaches sem none (countUp N) (.running (downState dropped N 0 es))
      (.halted ⟨.returned 0, es, N + 2, N⟩) := by
  refine ⟨1, ?_⟩
  simp [downState, run, step, countUp, mainRecv, Frame.get, evalOp, doReturn, dropList,
    pendingDrops, Frame.isLive, Fn.dtor, deliver, Frame.kill, State.halt, Val.obs]

theorem down_preJump (N : Nat) :
    ∀ j (es : List Event), Reaches .preJump none (countUp N) (.running (downState true N j es))
      (.halted ⟨.returned 0, es, N + 2, N⟩) := by
  intro j
  induction j with
  | zero => intro es; exact final true _ N es
  | succ j ih =>
    intro es
    refine Reaches.trans ⟨1, ?_⟩ (ih es)
    cases j <;>
    simp [downState, run, step, countUp, mainFr, mainRecv, doReturn, dropList,
      pendingDrops, range3_eq, Frame.isLive, Fn.dtor, deliver, Frame.write, waits, waitFr]

theorem down_callReturn (N : Nat) :
    ∀ j (es : List Event), Reaches .callReturn none (countUp N) (.running (downState false N j es))
      (.halted ⟨.returned 0, es ++ ((List.range j).reverse).map Event.drop, N + 2, N⟩) := by
  intro j
  induction j with
  | zero => intro es; simpa using final false _ N es
  | succ j ih =>
    intro es
    refine Reaches.trans ⟨1, ?_⟩ ((ih (es ++ [.drop j])).trans ?_)
    · cases j <;>
      simp [downState, run, step, countUp, mainFr, mainRecv, Frame.get, doReturn, dropList,
        pendingDrops, range3_eq, Frame.isLive, Fn.dtor, deliver, Frame.write, waits, waitFr,
        Frame.kill, Val.obs]
    · simp [List.range_succ]
      exact Reaches.refl _ _ _ _

theorem preJump_runsTo (N : Nat) :
    RunsTo .preJump none (countUp N) ⟨.returned 0, (List.range N).map Event.drop, N + 2, N⟩ := by
  have h0 : Reaches .preJump none (countUp N) (start none (countUp N)) (.running (upState true 0 [])) := by
    rw [start_eq]; exact Reaches.step (by simpa [upState, waits] using first_step .preJump N)
  have hup := up true .preJump N (fun m hm => by simpa using preJump_iter N m hm) N (Nat.le_refl N)
  simp only [ite_true] at hup
  exact h0.trans (hup.trans ((top true .preJump N _).trans (down_preJump N N _)))

theorem callReturn_runsTo (N : Nat) :
    RunsTo .callReturn none (countUp N)
      ⟨.returned 0, ((List.range N).reverse).map Event.drop, N + 2, N⟩ := by
  have h0 : Reaches .callReturn none (countUp N) (start none (countUp N)) (.running (upState false 0 [])) := by
    rw [start_eq]; exact Reaches.step (by simpa [upState, waits] using first_step .callReturn N)
  have hup := up false .callReturn N (fun m hm => by simpa using callReturn_iter N m hm) N (Nat.le_refl N)
  simp only [Bool.false_eq_true, ite_false] at hup
  have := h0.trans (hup.trans ((top false .callReturn N _).trans (down_callReturn N N _)))
  exact runsTo_of_reaches (by simpa using this)

end Toy.TailCall.CountUpProof
