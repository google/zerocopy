import ToyTailCall.Machine
import ToyTailCall.Inline
import ToyTailCall.Examples
import ToyTailCall.Lemmas

/-!
# Proof support: runs of `mutualRec N` and of its corrected tail-site splice
-/

namespace Toy.TailCall.MutualRecProof

open Toy.TailCall

/-- `main`'s frame while it waits for `c 0`. -/
def mainFr : Frame := ⟨0, 0, 0, [.undef], [false], .store 0 1, none⟩

theorem range1_eq : List.range 1 = [0] := rfl
theorem range2_eq : List.range 2 = [0, 1] := rfl
theorem range7_eq : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl

/-- `main` after receiving `0`. -/
def mainRecv : Frame := ⟨0, 0, 1, [.int 0], [true], .store 0 1, none⟩

theorem start_eq (D : Option Nat) (hD : overflows D 0 = false) (p : Prog)
    (hp : p.fns[0]? = some ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩) :
    start D p =
      .running ⟨[⟨0, 0, 0, [.undef], [false], .thenReturn, none⟩], 1, [], 1, 0, false⟩ := by
  simp [start, push, hp, hD, Fn.nSlots, State.empty]

/-! ### The original program under `frameReuse` -/

/-- A fresh frame of `c n` with identity `fid`. -/
def cFr (n fid : Nat) : Frame := ⟨fid, 1, 0, [.int n], [true], .thenReturn, none⟩

theorem orig_first (D : Option Nat) (hD : overflows D 1 = false) (N : Nat) :
    step .frameReuse D (mutualRec N) ⟨[⟨0, 0, 0, [.undef], [false], .thenReturn, none⟩], 1, [], 1, 0, false⟩ =
      .running ⟨[cFr 0 1, mainFr], 2, [], 2, 0, false⟩ := by
  simp [step, mutualRec, mainFr, cFr, evalOps, evalOp, push, hD, Fn.nSlots]

theorem orig_iter (D : Option Nat) (hD : overflows D 1 = false) (N n : Nat) (hlt : n < N) :
    Reaches .frameReuse D (mutualRec N)
      (.running ⟨[cFr n (2 * n + 1), mainFr], 2 * n + 2, [], 2, 2 * n, false⟩)
      (.running ⟨[cFr (n + 1) (2 * (n + 1) + 1), mainFr], 2 * (n + 1) + 2, [], 2, 2 * (n + 1), false⟩) := by
  refine ⟨4, ?_⟩
  simp [run, step, mutualRec, mainFr, cFr, Frame.get, hlt, evalOp, evalOps, Frame.write,
    Frame.kill, doTailCall, dropList, pendingDrops, Frame.isLive, Fn.dtor,
    Fn.nSlots, push, hD, bumpTail, range2_eq]
  omega

theorem orig_up (D : Option Nat) (hD : overflows D 1 = false) (N : Nat) :
    ∀ n, n ≤ N → Reaches .frameReuse D (mutualRec N)
    (.running ⟨[cFr 0 1, mainFr], 2, [], 2, 0, false⟩)
    (.running ⟨[cFr n (2 * n + 1), mainFr], 2 * n + 2, [], 2, 2 * n, false⟩) := by
  intro n
  induction n with
  | zero => intro _; exact Reaches.refl _ _ _ _
  | succ n ih => intro hn; exact (ih (by omega)).trans (orig_iter D hD N n (by omega))

theorem orig_end (D : Option Nat) (N : Nat) :
    Reaches .frameReuse D (mutualRec N)
      (.running ⟨[cFr N (2 * N + 1), mainFr], 2 * N + 2, [], 2, 2 * N, false⟩)
      (.halted ⟨.returned 0, [], 2, 2 * N⟩) := by
  refine ⟨4, ?_⟩
  simp [run, step, mutualRec, mainFr, cFr, Frame.get, evalOp, doReturn, dropList, pendingDrops,
    Frame.isLive, Fn.dtor, deliver, Frame.write, Frame.kill, State.halt, Val.obs]

theorem orig_runsTo (D : Option Nat) (hD0 : overflows D 0 = false) (hD1 : overflows D 1 = false)
    (N : Nat) : RunsTo .frameReuse D (mutualRec N) ⟨.returned 0, [], 2, 2 * N⟩ := by
  apply runsTo_of_reaches
  rw [start_eq D hD0 _ rfl]
  exact (Reaches.step (orig_first D hD1 N)).trans
    ((orig_up D hD1 N N (Nat.le_refl N)).trans (orig_end D N))

/-! ### The corrected tail-site splice -/

/-- Function `c` after `g` is spliced into its tail site. -/
def cInl (N : Nat) : Fn :=
  ⟨1, [.none, .none, .none, .none, .none, .none, .none],
    [.branchLt 0 N 1 2, .goto 3, .ret (.const 0), .assign 1 (.copy 0) 4, .dropSlots [0] 5,
     .goto 7, .ret (.move 2), .reset [3, 4, 5, 6] 8, .assign 3 (.move 1) 9,
     .assign 4 (.succ 3) 13, .panic, .panic, .panic, .assign 6 (.move 4) 14,
     .dropSlots [4, 3] 15, .call 1 [.move 6] 2 6, .panic]⟩

theorem inlineTailSite_eq (N : Nat) :
    inlineTailSite .corrected (mutualRec N) 1 1 =
      ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩, cInl N,
         ⟨1, [.none, .none], [.assign 1 (.succ 0) 1, .tailCall 1 [.move 1]]⟩ ]⟩ := by
  rfl

/-- A fresh frame of the spliced `c n`. -/
def iFr (n fid : Nat) : Frame :=
  ⟨fid, 1, 0, [.int n, .undef, .undef, .undef, .undef, .undef, .undef],
    [true, false, false, false, false, false, false], .thenReturn, none⟩

/-- The frame of the spliced `c n` waiting at its `call`. -/
def iWait (n fid : Nat) : Frame :=
  ⟨fid, 1, 15, [.int n, .int n, .undef, .int n, .int (n + 1), .undef, .int (n + 1)],
    [true, false, false, true, false, false, false], .store 2 6, none⟩

/-- The waiting frames of `c 0, …, c (k - 1)` (innermost first). -/
def iWaits : Nat → List Frame
  | 0 => []
  | k + 1 => iWait k (k + 1) :: iWaits k

theorem iWaits_length (k : Nat) : (iWaits k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iWaits, ih]

def P (N : Nat) : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩, cInl N,
     ⟨1, [.none, .none], [.assign 1 (.succ 0) 1, .tailCall 1 [.move 1]]⟩ ]⟩

theorem inl_first (D : Option Nat) (hD : overflows D 1 = false) (N : Nat) :
    step .frameReuse D (P N) ⟨[⟨0, 0, 0, [.undef], [false], .thenReturn, none⟩], 1, [], 1, 0, false⟩ =
      .running ⟨[iFr 0 1, mainFr], 2, [], 2, 0, false⟩ := by
  simp [step, P, cInl, mainFr, iFr, evalOps, evalOp, push, hD, Fn.nSlots]

/-- The spliced program with `c m` running above the waiting frames of `c 0, …, c (m - 1)`. -/
def upState (m : Nat) : State := ⟨iFr m (m + 1) :: iWaits m ++ [mainFr], m + 2, [], m + 2, 0, false⟩

theorem inl_iter (D : Option Nat) (N m : Nat) (hlt : m < N) (hD : overflows D (m + 2) = false) :
    Reaches .frameReuse D (P N) (.running (upState m)) (.running (upState (m + 1))) := by
  refine ⟨11, ?_⟩
  have hD' : overflows D (m + 1 + 1) = false := hD
  simp [upState, run, step, P, cInl, mainFr, iFr, iWait, iWaits, iWaits_length, Frame.get, hlt,
    evalOp, evalOps, Frame.write, Frame.kill, Frame.clear, Frame.isLive, Fn.dtor, dropList,
    Fn.nSlots, push, hD']

theorem inl_iter_overflow (D : Option Nat) (N m : Nat) (hlt : m < N)
    (hD : overflows D (m + 2) = true) :
    Reaches .frameReuse D (P N) (.running (upState m)) (.halted ⟨.stackOverflow, [], m + 2, 0⟩) := by
  refine ⟨11, ?_⟩
  have hD' : overflows D (m + 1 + 1) = true := hD
  simp [upState, run, step, P, cInl, mainFr, iFr, iWaits_length, Frame.get, hlt,
    evalOp, evalOps, Frame.write, Frame.kill, Frame.clear, Frame.isLive, Fn.dtor, dropList,
    Fn.nSlots, push, hD', State.halt]

theorem inl_up (D : Option Nat) (N : Nat) : ∀ m, m ≤ N → (∀ i, i < m → overflows D (i + 2) = false) →
    Reaches .frameReuse D (P N) (.running (upState 0)) (.running (upState m)) := by
  intro m
  induction m with
  | zero => intro _ _; exact Reaches.refl _ _ _ _
  | succ m ih =>
    intro hm hD
    exact (ih (by omega) fun i hi => hD i (by omega)).trans (inl_iter D N m (by omega) (hD m (by omega)))

/-- The return cascade of the spliced program. -/
def downState (N j : Nat) : State :=
  match j with
  | 0 => ⟨[mainRecv], N + 2, [], N + 2, 0, false⟩
  | j + 1 => ⟨{ (iWait j (j + 1)).write 2 (.int 0) with pc := 6 } :: iWaits j ++ [mainFr],
      N + 2, [], N + 2, 0, false⟩

theorem inl_top (D : Option Nat) (N : Nat) :
    Reaches .frameReuse D (P N) (.running (upState N)) (.running (downState N N)) := by
  refine ⟨2, ?_⟩
  cases N <;>
  simp [upState, downState, run, step, P, cInl, mainFr, mainRecv, iFr, Frame.get, evalOp,
    doReturn, dropList, pendingDrops, Frame.isLive, Fn.dtor, deliver, Frame.write, iWaits, iWait,
    range7_eq]

theorem inl_down (D : Option Nat) (N : Nat) : ∀ j, Reaches .frameReuse D (P N) (.running (downState N j))
    (.halted ⟨.returned 0, [], N + 2, 0⟩) := by
  intro j
  induction j with
  | zero =>
    refine ⟨1, ?_⟩
    simp [downState, run, step, P, mainRecv, Frame.get, evalOp, doReturn, dropList,
      pendingDrops, Frame.isLive, Fn.dtor, deliver, Frame.kill, State.halt, Val.obs]
  | succ j ih =>
    refine Reaches.trans ⟨1, ?_⟩ ih
    cases j <;>
    simp [downState, run, step, P, cInl, mainFr, mainRecv, Frame.get, evalOp, doReturn,
      dropList, pendingDrops, Frame.isLive, Fn.dtor, deliver, Frame.write, Frame.kill,
      iWaits, iWait, range7_eq]

theorem inl_runsTo (N : Nat) :
    RunsTo .frameReuse none (inlineTailSite .corrected (mutualRec N) 1 1)
      ⟨.returned 0, [], N + 2, 0⟩ := by
  rw [inlineTailSite_eq]
  apply runsTo_of_reaches
  show Reaches .frameReuse none (P N) _ _
  rw [start_eq none rfl _ rfl]
  exact (Reaches.step (by simpa [upState, iWaits] using inl_first none rfl N)).trans
    ((inl_up none N N (Nat.le_refl N) (fun _ _ => rfl)).trans ((inl_top none N).trans (inl_down none N N)))

/-- With bound `2 + C`, the spliced `mutualRec (C + 1)` overflows. -/
theorem inl_overflow (C : Nat) :
    RunsTo .frameReuse (some (2 + C)) (inlineTailSite .corrected (mutualRec (C + 1)) 1 1)
      ⟨.stackOverflow, [], C + 2, 0⟩ := by
  rw [inlineTailSite_eq]
  apply runsTo_of_reaches
  show Reaches .frameReuse (some (2 + C)) (P (C + 1)) _ _
  rw [start_eq (some (2 + C)) (by simp [overflows]) _ rfl]
  exact (Reaches.step (by simpa [upState, iWaits] using inl_first (some (2 + C)) (by simp [overflows]; omega) (C + 1))).trans
    ((inl_up (some (2 + C)) (C + 1) C (by omega) (fun i hi => by simp [overflows]; omega)).trans
      (inl_iter_overflow (some (2 + C)) (C + 1) C (by omega) (by simp [overflows]; omega)))

end Toy.TailCall.MutualRecProof
