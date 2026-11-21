import ToyCoalesce.VC

/-!
# Shared semantic lemmas (proof infrastructure)

Frame properties of the interpreter (which state fields each operation can change and how),
stickiness of failure, layout independence of everything but the event trace, a layout that
respects every recorded allocation pair, and helpers for proving refinements.
-/

namespace Toy.Coalesce

/-! ## Failure is sticky -/

theorem execBasic_of_not_running {sem : Sem} {P : Prog} {A : Layout} {s : St} (st : Stmt)
    (h : s.status ≠ .running) : execBasic sem P A s st = s := by
  unfold execBasic; simp [h]

theorem execStmt_of_not_running {sem : Sem} {P : Prog} {A : Layout} {s : St} (st : Stmt)
    (h : s.status ≠ .running) : execStmt sem P A s st = s := by
  unfold execStmt; simp [h]

theorem execCallee_of_not_running {sem : Sem} {P : Prog} {A : Layout} {s : St} (b : List Stmt)
    (h : s.status ≠ .running) : execCallee sem P A s b = s := by
  induction b with
  | nil => rfl
  | cons st b ih =>
    simp only [execCallee, List.foldl_cons, execBasic_of_not_running st h]
    exact ih

theorem foldl_execTop_of_not_running {sem : Sem} {P : Prog} {A : Layout} (l : List Stmt) :
    ∀ s : St, s.status ≠ .running →
      l.foldl (execTop sem P A) s = { s with tick := s.tick + l.length } := by
  induction l with
  | nil => intro s _; simp
  | cons st l ih =>
    intro s h
    simp only [List.foldl_cons]
    rw [ih _ (by simp [execTop, execStmt_of_not_running st h, h])]
    simp [execTop, execStmt_of_not_running st h]
    omega

/-! ## Frame properties

`Step s t`: `t` arises from `s` by operations that keep the tick, the in-call flag and the alias,
append log entries stamped with the current tick and in-call flag, append allocation pairs of
distinct locals, and append events. -/

structure Step (s t : St) : Prop where
  tick : t.tick = s.tick
  inCall : t.inCall = s.inCall
  alias : t.alias = s.alias
  log : ∃ d, t.log = s.log ++ d ∧ ∀ e ∈ d, e.tick = s.tick ∧ e.inCall = s.inCall
  conf : ∃ d, t.conflicts = s.conflicts ++ d ∧ ∀ c ∈ d, c.1 ≠ c.2
  trace : ∃ d, t.trace = s.trace ++ d

theorem Step.refl (s : St) : Step s s :=
  ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩, ⟨[], by simp⟩⟩

theorem Step.trans {s t u : St} (h1 : Step s t) (h2 : Step t u) : Step s u := by
  obtain ⟨t1, c1, a1, ⟨d1, hd1, he1⟩, ⟨e1, he1', hc1⟩, ⟨f1, hf1⟩⟩ := h1
  obtain ⟨t2, c2, a2, ⟨d2, hd2, he2⟩, ⟨e2, he2', hc2⟩, ⟨f2, hf2⟩⟩ := h2
  refine ⟨t2.trans t1, c2.trans c1, a2.trans a1, ⟨d1 ++ d2, by simp [hd2, hd1], ?_⟩,
    ⟨e1 ++ e2, by simp [he2', he1'], ?_⟩, ⟨f1 ++ f2, by simp [hf2, hf1]⟩⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact he1 e he
    · have := he2 e he; rw [t1, c1] at this; exact this
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hc1 c hc
    · exact hc2 c hc

theorem step_fail (s : St) (k : Status) : Step s (s.fail k) :=
  ⟨rfl, rfl, rfl, ⟨[], by simp [St.fail], by simp⟩, ⟨[], by simp [St.fail], by simp⟩,
    ⟨[], by simp [St.fail]⟩⟩

theorem step_logAcc (s : St) (loc off : Nat) (k : AccKind) : Step s (s.logAcc loc off k) :=
  ⟨rfl, rfl, rfl, ⟨[⟨s.tick, s.inCall, loc, off, k⟩], rfl, by simp⟩,
    ⟨[], by simp [St.logAcc], by simp⟩, ⟨[], by simp [St.logAcc]⟩⟩

theorem step_emit (s : St) (e : Event) : Step s (s.emit e) :=
  ⟨rfl, rfl, rfl, ⟨[], by simp [St.emit], by simp⟩, ⟨[], by simp [St.emit], by simp⟩,
    ⟨[e], rfl⟩⟩

theorem step_wr (s : St) (k : AccKind) (loc off : Nat) (v : Val) : Step s (s.wr k loc off v) :=
  let h := step_logAcc s loc off k
  ⟨h.tick, h.inCall, h.alias, h.log, h.conf, h.trace⟩

theorem step_writeCellsK (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    Step s (writeCellsK k s loc off vs) := by
  induction vs generalizing s off with
  | nil => exact Step.refl s
  | cons v vs ih => exact (step_wr s k loc off v).trans (ih _ _)

theorem step_writeCells (s : St) (loc off : Nat) (vs : List Val) :
    Step s (writeCells s loc off vs) := step_writeCellsK _ _ _ _ _

theorem step_resetCells (s : St) (loc n : Nat) : Step s (resetCells s loc n) :=
  step_writeCellsK _ _ _ _ _

theorem step_readCells (s : St) (loc off n : Nat) : Step s (readCells s loc off n).1 := by
  induction n generalizing s off with
  | zero => exact Step.refl s
  | succ n ih =>
    unfold readCells
    by_cases hv : s.mem loc off = .uninit
    · simp only [hv, ↓reduceIte]
      exact (step_logAcc _ _ _ _).trans (step_fail _ _)
    · simp only [hv, ↓reduceIte]
      have h := (step_logAcc s loc off .read).trans (ih (s.logAcc loc off .read) (off + 1))
      rcases hr : readCells (s.logAcc loc off .read) loc (off + 1) n with ⟨s', _ | vs⟩ <;>
        rw [hr] at h <;> exact h

theorem step_evalOp (ms : MoveSem) (P : Prog) (s : St) (o : Operand) :
    Step s (evalOp ms P s o).1 := by
  cases o with
  | lit n => exact Step.refl s
  | addrOf q =>
    simp only [evalOp]; split
    · exact Step.refl s
    · exact step_fail _ _
  | copy q =>
    simp only [evalOp]; split
    · exact step_readCells _ _ _ _
    · exact step_fail _ _
  | move q =>
    simp only [evalOp]; split
    · rename_i r _
      have h := step_readCells s r.base r.off r.len
      rcases hr : readCells s r.base r.off r.len with ⟨s', _ | vs⟩
      · rw [hr] at h; exact h
      · rw [hr] at h
        simp only
        split
        · exact h.trans (step_writeCells _ _ _ _)
        · exact h
    · exact step_fail _ _
  | load p len =>
    simp only [evalOp]; split
    · rename_i r _
      split
      · have h := step_readCells s r.base r.off 1
        split
        next s' l o heq =>
          rw [heq] at h
          split
          · exact h.trans (step_readCells _ _ _ _)
          · exact h.trans (step_fail _ _)
        next s' x _ heq => rw [heq] at h; exact h.trans (step_fail _ _)
        next s' heq => rw [heq] at h; exact h
      · exact step_fail _ _
    · exact step_fail _ _

theorem step_evalOps (ms : MoveSem) (P : Prog) (s : St) (os : List Operand) :
    Step s (evalOps ms P s os).1 := by
  induction os generalizing s with
  | nil => exact Step.refl s
  | cons o os ih =>
    simp only [evalOps]
    have h := step_evalOp ms P s o
    rcases hr : evalOp ms P s o with ⟨s', _ | vs⟩
    · rw [hr] at h; exact h
    · rw [hr] at h
      simp only
      have h2 := h.trans (ih s')
      rcases hr2 : evalOps ms P s' os with ⟨s'', _ | ws⟩ <;> rw [hr2] at h2 <;> exact h2

theorem step_writeInOrder (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat) (os : List Operand) :
    Step s (writeInOrder ms P s loc off os) := by
  induction os generalizing s off with
  | nil => exact Step.refl s
  | cons o os ih =>
    simp only [writeInOrder]
    have h := step_evalOp ms P s o
    rcases hr : evalOp ms P s o with ⟨s', _ | vs⟩
    · rw [hr] at h; exact h
    · rw [hr] at h
      exact (h.trans (step_writeCells _ _ _ _)).trans (ih _ _)

theorem step_allocate (P : Prog) (s : St) (x : Nat) : Step s (allocate P s x) := by
  unfold allocate
  split
  · refine Step.trans ?_ (step_resetCells _ _ _)
    refine ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, ⟨(liveOthers P s x).map fun z => (x, z), rfl, ?_⟩,
      ⟨[], by simp⟩⟩
    intro c hc
    simp only [List.mem_map, liveOthers, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hc
    obtain ⟨z, ⟨_, hz, _⟩, rfl⟩ := hc
    exact fun h => hz h.symm
  · exact step_fail _ _

theorem step_deallocate (P : Prog) (s : St) (x : Nat) : Step s (deallocate P s x) := by
  unfold deallocate
  split
  · have h := step_resetCells s x (P.size x)
    exact ⟨h.tick, h.inCall, h.alias, h.log, h.conf, h.trace⟩
  · exact Step.refl s

theorem step_cmpOp (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) : Step s (cmpOp ms P A s a b f) := by
  unfold cmpOp
  have h1 := step_evalOp ms P s a
  split
  next s1 va heq =>
    rw [heq] at h1
    have h2 := h1.trans (step_evalOp ms P s1 b)
    split
    next s2 vb heq2 =>
      rw [heq2] at h2
      split
      · exact h2.trans (step_emit _ _)
      · exact h2.trans (step_fail _ _)
    next s2 _ _ heq2 => rw [heq2] at h2; exact h2.trans (step_fail _ _)
    next s2 heq2 => rw [heq2] at h2; exact h2
  next s1 _ _ heq => rw [heq] at h1; exact h1.trans (step_fail _ _)
  next s1 heq => rw [heq] at h1; exact h1

theorem step_execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) :
    Step s (execBasic sem P A s st) := by
  unfold execBasic
  split
  · exact Step.refl s
  · cases st with
    | storageLive x =>
      simp only; split
      · exact step_fail _ _
      · exact step_allocate _ _ _
    | storageDead x =>
      simp only; split
      · exact step_fail _ _
      · exact step_deallocate _ _ _
    | assign lhs rhs =>
      simp only; split
      · exact step_fail _ _
      · split
        · exact step_fail _ _
        · split
          · have h := step_evalOps sem.move P s rhs
            rcases hr : evalOps sem.move P s rhs with ⟨s', _ | vs⟩
            · rw [hr] at h; exact h
            · rw [hr] at h; exact h.trans (step_writeCells _ _ _ _)
          · exact step_writeInOrder _ _ _ _ _ _
    | store p v =>
      simp only; split
      · rename_i r _
        split
        · have h := step_readCells s r.base r.off 1
          split
          next s1 l o heq =>
            rw [heq] at h
            have h2 := h.trans (step_evalOp sem.move P s1 v)
            split
            next s2 vs heq2 =>
              rw [heq2] at h2
              split
              · exact h2.trans (step_writeCells _ _ _ _)
              · exact h2.trans (step_fail _ _)
            next s2 heq2 => rw [heq2] at h2; exact h2
          next s1 _ _ heq => rw [heq] at h; exact h.trans (step_fail _ _)
          next s1 heq => rw [heq] at h; exact h
        · exact step_fail _ _
      · exact step_fail _ _
    | ptrEq a b => exact step_cmpOp _ _ _ _ _ _ _
    | ptrInRange a b n => exact step_cmpOp _ _ _ _ _ _ _
    | out o =>
      simp only
      have h := step_evalOp sem.move P s o
      rcases hr : evalOp sem.move P s o with ⟨s', _ | vs⟩
      · rw [hr] at h; exact h
      · rw [hr] at h; exact h.trans (step_emit _ _)
    | call fn a => exact step_fail _ _
    | nop => exact Step.refl s

theorem step_execCallee (sem : Sem) (P : Prog) (A : Layout) (s : St) (b : List Stmt) :
    Step s (execCallee sem P A s b) := by
  induction b generalizing s with
  | nil => exact Step.refl s
  | cons st b ih =>
    simp only [execCallee, List.foldl_cons]
    exact (step_execBasic sem P A s st).trans (ih _)

/-! ## Top-level statements -/

/-- Weak frame: same tick, log entries stamped with the tick of `s`, allocation pairs of distinct
locals and events appended. -/
structure StepT (s t : St) : Prop where
  tick : t.tick = s.tick
  log : ∃ d, t.log = s.log ++ d ∧ ∀ e ∈ d, e.tick = s.tick
  conf : ∃ d, t.conflicts = s.conflicts ++ d ∧ ∀ c ∈ d, c.1 ≠ c.2
  trace : ∃ d, t.trace = s.trace ++ d

theorem StepT.refl (s : St) : StepT s s :=
  ⟨rfl, ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩, ⟨[], by simp⟩⟩

theorem StepT.trans {s t u : St} (h1 : StepT s t) (h2 : StepT t u) : StepT s u := by
  obtain ⟨t1, ⟨d1, hd1, he1⟩, ⟨e1, he1', hc1⟩, ⟨f1, hf1⟩⟩ := h1
  obtain ⟨t2, ⟨d2, hd2, he2⟩, ⟨e2, he2', hc2⟩, ⟨f2, hf2⟩⟩ := h2
  refine ⟨t2.trans t1, ⟨d1 ++ d2, by simp [hd2, hd1], ?_⟩,
    ⟨e1 ++ e2, by simp [he2', he1'], ?_⟩, ⟨f1 ++ f2, by simp [hf2, hf1]⟩⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact he1 e he
    · have := he2 e he; rw [t1] at this; exact this
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hc1 c hc
    · exact hc2 c hc

theorem Step.toT {s t : St} (h : Step s t) : StepT s t :=
  ⟨h.tick, let ⟨d, h1, h2⟩ := h.log; ⟨d, h1, fun e he => (h2 e he).1⟩, h.conf, h.trace⟩

theorem StepT.setCtx (s : St) (al : Option (Nat × Place)) (c : Bool) :
    StepT s { s with alias := al, inCall := c } :=
  ⟨rfl, ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩, ⟨[], by simp⟩⟩

theorem StepT.setCtx' {s t : St} (al : Option (Nat × Place)) (c : Bool) (h : StepT s t) :
    StepT s { t with alias := al, inCall := c } :=
  h.trans (StepT.setCtx t al c)

theorem StepT.setInCall {s t : St} (c : Bool) (h : StepT s t) : StepT s { t with inCall := c } :=
  h.trans ⟨rfl, ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩, ⟨[], by simp⟩⟩

/-- Frame of the copy-passing branch of a top-level call. -/
theorem callCopy_frame (sem : Sem) (P : Prog) (A : Layout) (s : St) (arg : Operand) (c : Callee)
    (hc : s.inCall = false) (ha : s.alias = none) :
    let t := (match evalOp sem.move P s arg with
      | (s1, some vs) =>
        if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
        let s2 := allocate P s1 c.prm
        let s3 := writeCells s2 c.prm 0 vs
        let s4 := execCallee sem P A { s3 with inCall := true } c.body
        deallocate P { s4 with inCall := false } c.prm
      | (s1, none) => s1)
    StepT s t ∧ t.inCall = false ∧ t.alias = none := by
  intro t
  have h1 := step_evalOp sem.move P s arg
  simp only [t]
  split
  next s1 vs heq =>
    rw [heq] at h1
    split
    · have h := h1.trans (step_fail s1 .ub)
      exact ⟨h.toT, h.inCall.trans hc, h.alias.trans ha⟩
    · have h2 := h1.trans ((step_allocate P s1 c.prm).trans (step_writeCells _ c.prm 0 vs))
      have h3 := (h2.toT.setInCall true).trans (step_execCallee sem P A _ c.body).toT
      have h4 := (h3.setInCall false).trans (step_deallocate P _ c.prm).toT
      refine ⟨h4, ?_, ?_⟩
      · exact (step_deallocate P _ c.prm).inCall
      · rw [(step_deallocate P _ c.prm).alias]
        simp only
        rw [(step_execCallee sem P A _ c.body).alias]
        simp only
        rw [h2.alias, ha]
  next s1 heq =>
    rw [heq] at h1; exact ⟨h1.toT, h1.inCall.trans hc, h1.alias.trans ha⟩

/-- A top-level statement started in a top-level state (no alias, not in a call) ends in a
top-level state, keeps the tick, and stamps its log entries with that tick. -/
theorem execStmt_frame (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (hc : s.inCall = false) (ha : s.alias = none) :
    StepT s (execStmt sem P A s st) ∧ (execStmt sem P A s st).inCall = false ∧
      (execStmt sem P A s st).alias = none := by
  unfold execStmt
  split
  · exact ⟨StepT.refl s, hc, ha⟩
  · cases st with
    | call fn arg =>
      simp only
      split
      · next q =>
        split
        · have h := step_fail s .ub; exact ⟨h.toT, h.inCall.trans hc, h.alias.trans ha⟩
        · next r _ =>
          split
          · have h := step_fail s .ub; exact ⟨h.toT, h.inCall.trans hc, h.alias.trans ha⟩
          · exact ⟨(StepT.setCtx s _ _).trans (step_execCallee _ _ _ _ _).toT |>.setCtx' _ _,
              rfl, rfl⟩
      · exact callCopy_frame sem P A s _ _ hc ha
    | _ =>
      first
      | exact let h := step_execBasic sem P A s _; ⟨h.toT, h.inCall.trans hc, h.alias.trans ha⟩

/-- The state after the first `t` top-level statements. -/
def runAt (sem : Sem) (P : Prog) (A : Layout) (t : Nat) : St :=
  (P.code.take t).foldl (execTop sem P A) St.init

theorem run_eq_runAt (sem : Sem) (P : Prog) (A : Layout) :
    run sem P A = runAt sem P A P.code.length := by
  simp [run, runAt]

theorem runAt_zero (sem : Sem) (P : Prog) (A : Layout) : runAt sem P A 0 = St.init := by
  simp [runAt]

theorem runAt_succ (sem : Sem) (P : Prog) (A : Layout) (t : Nat) (ht : t < P.code.length) :
    runAt sem P A (t + 1) = execTop sem P A (runAt sem P A t) P.code[t] := by
  unfold runAt
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append]
  rfl

theorem runAt_of_le (sem : Sem) (P : Prog) (A : Layout) (t : Nat) (ht : P.code.length ≤ t) :
    runAt sem P A t = run sem P A := by
  simp [runAt, run, List.take_of_length_le ht]

/-- Top-level invariants: after `t ≤ length` statements the tick is `t`, there is no alias and the
run is not inside a call; every log entry so far has a tick `< t`. -/
theorem runAt_frame (sem : Sem) (P : Prog) (A : Layout) (t : Nat) (ht : t ≤ P.code.length) :
    (runAt sem P A t).tick = t ∧ (runAt sem P A t).inCall = false ∧
      (runAt sem P A t).alias = none ∧ ∀ e ∈ (runAt sem P A t).log, e.tick < t := by
  induction t with
  | zero => simp [runAt_zero, St.init]
  | succ t ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    rw [runAt_succ _ _ _ _ (by omega)]
    have hf := execStmt_frame sem P A (runAt sem P A t) P.code[t] h2 h3
    refine ⟨by simp [execTop, hf.1.tick, h1], hf.2.1, hf.2.2, ?_⟩
    intro e he
    obtain ⟨d, hd, hdt⟩ := hf.1.log
    simp only [execTop] at he
    rw [hd] at he
    rcases List.mem_append.1 he with he | he
    · have := h4 e he; omega
    · have := hdt e he; omega

/-- The log entries added by top-level statement `t` carry tick `t`. -/
theorem runAt_succ_log (sem : Sem) (P : Prog) (A : Layout) (t : Nat) (ht : t < P.code.length) :
    ∃ d, (runAt sem P A (t + 1)).log = (runAt sem P A t).log ++ d ∧ ∀ e ∈ d, e.tick = t := by
  obtain ⟨h1, h2, h3, _⟩ := runAt_frame sem P A t (by omega)
  have hf := execStmt_frame sem P A (runAt sem P A t) P.code[t] h2 h3
  obtain ⟨d, hd, hdt⟩ := hf.1.log
  refine ⟨d, ?_, fun e he => (hdt e he).trans h1⟩
  rw [runAt_succ _ _ _ _ ht]; simpa [execTop] using hd

/-- Every later state's log extends an earlier one; the added entries have ticks `≥ t`. -/
theorem runAt_log_extends (sem : Sem) (P : Prog) (A : Layout) (t u : Nat) (htu : t ≤ u) :
    ∃ d, (runAt sem P A u).log = (runAt sem P A t).log ++ d ∧ ∀ e ∈ d, t ≤ e.tick := by
  obtain ⟨k, rfl⟩ : ∃ k, u = t + k := ⟨u - t, by omega⟩
  clear htu
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, hdt⟩ := ih
    by_cases hu : t + k < P.code.length
    · obtain ⟨d', hd', hdt'⟩ := runAt_succ_log sem P A (t + k) hu
      refine ⟨d ++ d', by rw [← Nat.add_assoc, hd', hd]; simp, ?_⟩
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hdt e he
      · have := hdt' e he; omega
    · rw [runAt_of_le _ _ _ (t + (k + 1)) (by omega), ← runAt_of_le sem P A (t + k) (by omega)]
      exact ⟨d, hd, hdt⟩

/-- The final log splits at any `t ≤ length` into the entries of ticks `< t` and of ticks `≥ t`. -/
theorem run_log_split (sem : Sem) (P : Prog) (A : Layout) (t : Nat) (ht : t ≤ P.code.length) :
    ∃ d, (run sem P A).log = (runAt sem P A t).log ++ d ∧
      (∀ e ∈ (runAt sem P A t).log, e.tick < t) ∧ ∀ e ∈ d, t ≤ e.tick := by
  obtain ⟨d, hd, hdt⟩ := runAt_log_extends sem P A t P.code.length ht
  exact ⟨d, by rw [run_eq_runAt]; exact hd, (runAt_frame sem P A t ht).2.2.2, hdt⟩

/-! ## The event trace is never read: layout independence

Operations other than `out` and pointer comparisons commute with replacing the trace; the layout
reaches nothing but emitted events. -/

section TraceIrrelevance

variable (tr : List Event)

theorem logAcc_trace (s : St) (loc off : Nat) (k : AccKind) :
    ({ s with trace := tr } : St).logAcc loc off k = { s.logAcc loc off k with trace := tr } := rfl

theorem fail_trace (s : St) (k : Status) :
    ({ s with trace := tr } : St).fail k = { s.fail k with trace := tr } := rfl

theorem wr_trace (s : St) (k : AccKind) (loc off : Nat) (v : Val) :
    ({ s with trace := tr } : St).wr k loc off v = { s.wr k loc off v with trace := tr } := rfl

theorem writeCellsK_trace (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    writeCellsK k { s with trace := tr } loc off vs = { writeCellsK k s loc off vs with trace := tr } := by
  induction vs generalizing s off with
  | nil => rfl
  | cons v vs ih =>
    simp only [writeCellsK]
    rw [wr_trace]; exact ih _ _

theorem writeCells_trace (s : St) (loc off : Nat) (vs : List Val) :
    writeCells { s with trace := tr } loc off vs = { writeCells s loc off vs with trace := tr } :=
  writeCellsK_trace tr _ _ _ _ _

theorem readCells_trace (s : St) (loc off n : Nat) :
    readCells { s with trace := tr } loc off n =
      ({ (readCells s loc off n).1 with trace := tr }, (readCells s loc off n).2) := by
  induction n generalizing s off with
  | zero => rfl
  | succ n ih =>
    unfold readCells
    simp only [logAcc_trace, ih]
    by_cases hv : s.mem loc off = .uninit
    · simp [hv, St.fail]
    · simp only [hv, ↓reduceIte]
      rcases readCells (s.logAcc loc off .read) loc (off + 1) n with ⟨s', _ | vs⟩ <;> rfl

theorem resolvePlace_trace (P : Prog) (s : St) (q : Place) :
    resolvePlace P { s with trace := tr } q = resolvePlace P s q := rfl

theorem evalOp_trace (ms : MoveSem) (P : Prog) (s : St) (o : Operand) :
    evalOp ms P { s with trace := tr } o =
      ({ (evalOp ms P s o).1 with trace := tr }, (evalOp ms P s o).2) := by
  cases o with
  | lit n => rfl
  | addrOf q =>
    simp only [evalOp, resolvePlace_trace]
    cases resolvePlace P s q <;> rfl
  | copy q =>
    simp only [evalOp, resolvePlace_trace]
    cases resolvePlace P s q with
    | none => rfl
    | some r => exact readCells_trace tr _ _ _ _
  | move q =>
    simp only [evalOp, resolvePlace_trace]
    cases resolvePlace P s q with
    | none => rfl
    | some r =>
      simp only [readCells_trace]
      rcases readCells s r.base r.off r.len with ⟨s', _ | vs⟩
      · rfl
      · simp only
        split
        · simp only [writeCells_trace]
        · rfl
  | load p len =>
    simp only [evalOp, resolvePlace_trace]
    cases resolvePlace P s p with
    | none => rfl
    | some r =>
      simp only
      split
      · simp only [readCells_trace]
        rcases readCells s r.base r.off 1 with ⟨s', _ | vs⟩
        · rfl
        · simp only
          rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
          · rfl
          · cases v with
            | ptr l o =>
              simp only
              split
              · exact readCells_trace tr _ _ _ _
              · rfl
            | _ => rfl
          · cases v <;> rfl
      · rfl

theorem evalOps_trace (ms : MoveSem) (P : Prog) (s : St) (os : List Operand) :
    evalOps ms P { s with trace := tr } os =
      ({ (evalOps ms P s os).1 with trace := tr }, (evalOps ms P s os).2) := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [evalOps, evalOp_trace]
    rcases evalOp ms P s o with ⟨s', _ | vs⟩
    · rfl
    · simp only [ih]
      rcases evalOps ms P s' os with ⟨s'', _ | ws⟩ <;> rfl

theorem writeInOrder_trace (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat) (os : List Operand) :
    writeInOrder ms P { s with trace := tr } loc off os =
      { writeInOrder ms P s loc off os with trace := tr } := by
  induction os generalizing s off with
  | nil => rfl
  | cons o os ih =>
    simp only [writeInOrder, evalOp_trace]
    rcases evalOp ms P s o with ⟨s', _ | vs⟩
    · rfl
    · simp only [writeCells_trace, ih]

theorem allocate_trace (P : Prog) (s : St) (x : Nat) :
    allocate P { s with trace := tr } x = { allocate P s x with trace := tr } := by
  unfold allocate
  split
  · exact writeCellsK_trace tr .reset { s with
      conflicts := s.conflicts ++ (liveOthers P s x).map (fun z => (x, z)),
      live := fun z => if z = x then true else s.live z } x 0 _
  · rfl

theorem deallocate_trace (P : Prog) (s : St) (x : Nat) :
    deallocate P { s with trace := tr } x = { deallocate P s x with trace := tr } := by
  unfold deallocate
  split
  · simp only [resetCells, writeCellsK_trace]
  · rfl

end TraceIrrelevance

/-- Equality of all state fields except the event trace. -/
def TEq (s t : St) : Prop := { s with trace := [] } = { t with trace := [] }

theorem TEq.refl (s : St) : TEq s s := rfl

theorem TEq.symm {s t : St} (h : TEq s t) : TEq t s := Eq.symm h

theorem TEq.trans {s t u : St} (h1 : TEq s t) (h2 : TEq t u) : TEq s u := Eq.trans h1 h2

theorem TEq.eq {s t : St} (h : TEq s t) : t = { s with trace := t.trace } := by
  have : ({ t with trace := [] } : St) = { s with trace := [] } := h.symm
  cases s; cases t
  simp only [St.mk.injEq] at this ⊢
  simp [this]

theorem TEq.of_eq {s t : St} (h : t = { s with trace := t.trace }) : TEq s t := by
  unfold TEq; rw [h]

theorem TEq.with_trace (s : St) (tr : List Event) : TEq s { s with trace := tr } := rfl

theorem TEq.status {s t : St} (h : TEq s t) : s.status = t.status := by rw [h.eq]
theorem TEq.log {s t : St} (h : TEq s t) : s.log = t.log := by rw [h.eq]
theorem TEq.conflicts {s t : St} (h : TEq s t) : s.conflicts = t.conflicts := by rw [h.eq]
theorem TEq.mem {s t : St} (h : TEq s t) : s.mem = t.mem := by rw [h.eq]
theorem TEq.live {s t : St} (h : TEq s t) : s.live = t.live := by rw [h.eq]
theorem TEq.alias {s t : St} (h : TEq s t) : s.alias = t.alias := by rw [h.eq]
theorem TEq.tick {s t : St} (h : TEq s t) : s.tick = t.tick := by rw [h.eq]
theorem TEq.inCall {s t : St} (h : TEq s t) : s.inCall = t.inCall := by rw [h.eq]

theorem TEq.emit (s : St) (e : Event) : TEq s (s.emit e) := rfl

theorem cmpOp_teq (ms : MoveSem) (P : Prog) (A A' : Layout) (s t : St) (h : TEq s t) (a b : Operand)
    (f : Nat → Nat → Bool) : TEq (cmpOp ms P A s a b f) (cmpOp ms P A' t a b f) := by
  rw [h.eq]
  unfold cmpOp
  simp only [evalOp_trace]
  rcases evalOp ms P s a with ⟨s1, _ | va⟩
  · exact TEq.with_trace _ _
  · simp only
    rcases va with _ | ⟨va, _ | ⟨w, ws⟩⟩
    · exact TEq.with_trace _ _
    · simp only [evalOp_trace]
      rcases evalOp ms P s1 b with ⟨s2, _ | vb⟩
      · exact TEq.with_trace _ _
      · simp only
        rcases vb with _ | ⟨vb, _ | ⟨w', ws'⟩⟩
        · exact TEq.with_trace _ _
        · simp only
          cases va <;> cases vb <;> simp only [Val.addr?] <;>
            first
            | exact (TEq.emit _ _).trans ((TEq.with_trace _ _).trans (TEq.emit _ _).symm)
            | exact TEq.with_trace _ _
        · exact TEq.with_trace _ _
    · exact TEq.with_trace _ _

theorem execBasic_teq (sem : Sem) (P : Prog) (A A' : Layout) (s t : St) (h : TEq s t) (st : Stmt) :
    TEq (execBasic sem P A s st) (execBasic sem P A' t st) := by
  have hst := h.status
  rw [h.eq]
  unfold execBasic
  split
  · exact TEq.with_trace _ _
  · cases st with
    | storageLive x =>
      simp only; split
      · exact TEq.with_trace _ _
      · rw [allocate_trace t.trace]; exact TEq.with_trace _ _
    | storageDead x =>
      simp only; split
      · exact TEq.with_trace _ _
      · rw [deallocate_trace t.trace]; exact TEq.with_trace _ _
    | assign lhs rhs =>
      simp only [resolvePlace_trace]
      split
      · exact TEq.with_trace _ _
      · cases resolvePlace P s lhs with
        | none => exact TEq.with_trace _ _
        | some r =>
          simp only
          cases sem.assign with
          | atomic =>
            simp only [evalOps_trace]
            rcases evalOps sem.move P s rhs with ⟨s', _ | vs⟩
            · exact TEq.with_trace _ _
            · simp only [writeCells_trace]; exact TEq.with_trace _ _
          | inOrder => simp only [writeInOrder_trace]; exact TEq.with_trace _ _
    | store p v =>
      simp only [resolvePlace_trace]
      cases resolvePlace P s p with
      | none => exact TEq.with_trace _ _
      | some r =>
        simp only
        split
        · simp only [readCells_trace]
          rcases readCells s r.base r.off 1 with ⟨s1, _ | vs1⟩
          · exact TEq.with_trace _ _
          · simp only
            rcases vs1 with _ | ⟨v1, _ | ⟨w, ws⟩⟩
            · exact TEq.with_trace _ _
            · cases v1 with
              | ptr l o =>
                simp only [evalOp_trace]
                rcases evalOp sem.move P s1 v with ⟨s2, _ | vs⟩
                · exact TEq.with_trace _ _
                · simp only
                  split
                  · simp only [writeCells_trace]; exact TEq.with_trace _ _
                  · exact TEq.with_trace _ _
              | _ => exact TEq.with_trace _ _
            · cases v1 <;> exact TEq.with_trace _ _
        · exact TEq.with_trace _ _
    | ptrEq a b => exact cmpOp_teq _ _ _ _ _ _ (TEq.with_trace _ _) _ _ _
    | ptrInRange a b n => exact cmpOp_teq _ _ _ _ _ _ (TEq.with_trace _ _) _ _ _
    | out o =>
      simp only [evalOp_trace]
      rcases evalOp sem.move P s o with ⟨s', _ | vs⟩
      · exact TEq.with_trace _ _
      · exact (TEq.emit _ _).symm.trans ((TEq.with_trace _ _).trans (TEq.emit _ _))
    | call fn a => exact TEq.with_trace _ _
    | nop => exact TEq.with_trace _ _

theorem execCallee_teq (sem : Sem) (P : Prog) (A A' : Layout) (b : List Stmt) :
    ∀ s t : St, TEq s t → TEq (execCallee sem P A s b) (execCallee sem P A' t b) := by
  induction b with
  | nil => intro s t h; exact h
  | cons st b ih =>
    intro s t h
    simp only [execCallee, List.foldl_cons]
    exact ih _ _ (execBasic_teq sem P A A' s t h st)

theorem TEq.setCtx {s t : St} (h : TEq s t) (al : Option (Nat × Place)) (c : Bool) :
    TEq { s with alias := al, inCall := c } { t with alias := al, inCall := c } := by
  rw [h.eq]; rfl

theorem TEq.setInCall {s t : St} (h : TEq s t) (c : Bool) :
    TEq { s with inCall := c } { t with inCall := c } := by
  rw [h.eq]; rfl

theorem TEq.setTick {s t : St} (h : TEq s t) (n : Nat) :
    TEq { s with tick := n } { t with tick := n } := by
  rw [h.eq]; rfl

theorem allocate_teq (P : Prog) (s t : St) (h : TEq s t) (x : Nat) :
    TEq (allocate P s x) (allocate P t x) := by
  rw [h.eq, allocate_trace t.trace]; exact TEq.with_trace _ _

theorem deallocate_teq (P : Prog) (s t : St) (h : TEq s t) (x : Nat) :
    TEq (deallocate P s x) (deallocate P t x) := by
  rw [h.eq, deallocate_trace t.trace]; exact TEq.with_trace _ _

theorem writeCells_teq (s t : St) (h : TEq s t) (loc off : Nat) (vs : List Val) :
    TEq (writeCells s loc off vs) (writeCells t loc off vs) := by
  rw [h.eq, writeCells_trace t.trace]; exact TEq.with_trace _ _

theorem execStmt_teq (sem : Sem) (P : Prog) (A A' : Layout) (s t : St) (h : TEq s t) (st : Stmt) :
    TEq (execStmt sem P A s st) (execStmt sem P A' t st) := by
  have hst := h.status
  unfold execStmt
  simp only [← hst]
  split
  · exact h
  · cases st with
    | call fn arg =>
      simp only
      rw [h.eq]
      split
      · simp only [resolvePlace_trace]
        cases resolvePlace P s _ with
        | none => exact TEq.with_trace _ _
        | some r =>
          simp only
          split
          · exact TEq.with_trace _ _
          · exact (execCallee_teq sem P A A' (P.fn fn).body
              { s with alias := some ((P.fn fn).prm, r), inCall := true }
              { s with trace := t.trace, alias := some ((P.fn fn).prm, r), inCall := true } rfl).setCtx
              none false
      · simp only [evalOp_trace]
        rcases evalOp sem.move P s _ with ⟨s1, _ | vs⟩
        · exact TEq.with_trace _ _
        · simp only
          split
          · exact TEq.with_trace _ _
          · exact deallocate_teq P _ _ ((execCallee_teq sem P A A' _ _ _
              ((writeCells_teq _ _ (allocate_teq P _ _ (TEq.with_trace s1 t.trace) _) _ _ _).setInCall
                true)).setInCall false) _
    | _ => exact execBasic_teq sem P A A' s t h _

theorem execTop_teq (sem : Sem) (P : Prog) (A A' : Layout) (s t : St) (h : TEq s t) (st : Stmt) :
    TEq (execTop sem P A s st) (execTop sem P A' t st) := by
  have h1 := execStmt_teq sem P A A' s t h st
  have := h1.tick
  simp only [execTop, this]
  exact h1.setTick _

theorem foldl_execTop_teq (sem : Sem) (P : Prog) (A A' : Layout) (l : List Stmt) :
    ∀ s t : St, TEq s t → TEq (l.foldl (execTop sem P A) s) (l.foldl (execTop sem P A') t) := by
  induction l with
  | nil => intro s t h; exact h
  | cons st l ih =>
    intro s t h
    exact ih _ _ (execTop_teq sem P A A' s t h st)

/-- Everything but the trace of a run is independent of the layout. -/
theorem run_teq (sem : Sem) (P : Prog) (A A' : Layout) : TEq (run sem P A) (run sem P A') :=
  foldl_execTop_teq sem P A A' _ _ _ (TEq.refl _)

theorem runAt_teq (sem : Sem) (P : Prog) (A A' : Layout) (t : Nat) :
    TEq (runAt sem P A t) (runAt sem P A' t) :=
  foldl_execTop_teq sem P A A' _ _ _ (TEq.refl _)

/-! ## A layout respecting every allocation pair; refinement helpers -/

/-- Local `x` at address `x * (Σ sizes + 1)`: distinct locals get disjoint address ranges. -/
def goodLayout (P : Prog) : Layout := fun x => x * (P.sizes.sum + 1)

theorem getD_le_sum (l : List Nat) (x : Nat) : l.getD x 0 ≤ l.sum := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    cases x with
    | zero => simp
    | succ x => simp only [List.getD_cons_succ, List.sum_cons]; have := ih x; omega

theorem size_le_sum (P : Prog) (x : Nat) : P.size x ≤ P.sizes.sum := getD_le_sum _ _

theorem disj_goodLayout (P : Prog) (x z : Nat) (h : x ≠ z) :
    Disj (goodLayout P x) (P.size x) (goodLayout P z) (P.size z) := by
  unfold Disj goodLayout
  have hx := size_le_sum P x
  have hz := size_le_sum P z
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have h1 : (x + 1) * (P.sizes.sum + 1) ≤ z * (P.sizes.sum + 1) := Nat.mul_le_mul_right _ h
    have h2 : (x + 1) * (P.sizes.sum + 1) = x * (P.sizes.sum + 1) + (P.sizes.sum + 1) :=
      Nat.succ_mul _ _
    omega
  · have h1 : (z + 1) * (P.sizes.sum + 1) ≤ x * (P.sizes.sum + 1) := Nat.mul_le_mul_right _ h
    have h2 : (z + 1) * (P.sizes.sum + 1) = z * (P.sizes.sum + 1) + (P.sizes.sum + 1) :=
      Nat.succ_mul _ _
    omega

theorem layoutOK_goodLayout (P : Prog) (cs : List (Nat × Nat)) (h : ∀ c ∈ cs, c.1 ≠ c.2) :
    layoutOK P (goodLayout P) cs = true := by
  simp only [layoutOK, List.all_eq_true, decide_eq_true_eq]
  intro c hc
  exact disj_goodLayout P c.1 c.2 (h c hc)

theorem runAt_conflicts_ne (sem : Sem) (P : Prog) (A : Layout) (t : Nat) :
    ∀ c ∈ (runAt sem P A t).conflicts, c.1 ≠ c.2 := by
  induction t with
  | zero => simp [runAt_zero, St.init]
  | succ t ih =>
    by_cases ht : t < P.code.length
    · obtain ⟨_, h2, h3, _⟩ := runAt_frame sem P A t (by omega)
      have hf := execStmt_frame sem P A (runAt sem P A t) P.code[t] h2 h3
      obtain ⟨d, hd, hdc⟩ := hf.1.conf
      rw [runAt_succ _ _ _ _ ht]
      intro c hc
      simp only [execTop, hd] at hc
      rcases List.mem_append.1 hc with hc | hc
      · exact ih c hc
      · exact hdc c hc
    · rw [runAt_of_le _ _ _ _ (by omega), ← runAt_of_le sem P A t (by omega)]
      exact ih

theorem run_conflicts_ne (sem : Sem) (P : Prog) (A : Layout) :
    ∀ c ∈ (run sem P A).conflicts, c.1 ≠ c.2 := by
  rw [run_eq_runAt]; exact runAt_conflicts_ne _ _ _ _

theorem layoutOK_goodLayout_run (sem : Sem) (P : Prog) (A : Layout) :
    layoutOK P (goodLayout P) (run sem P A).conflicts = true :=
  layoutOK_goodLayout P _ (run_conflicts_ne sem P A)

theorem outcome_goodLayout_ne_badLayout (sem : Sem) (P : Prog) :
    outcome sem P (goodLayout P) ≠ .badLayout := by
  unfold outcome
  simp only [layoutOK_goodLayout_run, ↓reduceIte]
  cases (run sem P (goodLayout P)).status <;> simp

theorem status_eq_ub_of_ne_running {s : St} (h : s.status ≠ .running) : s.status = .ub := by
  cases hs : s.status <;> simp_all

/-- A run that fails on some layout gives the behaviour `ub` (on the good layout). -/
theorem beh_ub_of_status (sem : Sem) (P : Prog) (A : Layout) (h : (run sem P A).status = .ub) :
    Beh sem P .ub := by
  refine ⟨goodLayout P, ?_, by simp⟩
  have hs : (run sem P (goodLayout P)).status = .ub := (run_teq sem P A (goodLayout P)).status ▸ h
  unfold outcome
  simp [layoutOK_goodLayout_run, hs]

theorem run_status_running_iff (sem : Sem) (P : Prog) (A A' : Layout) :
    (run sem P A).status = .running ↔ (run sem P A').status = .running := by
  rw [(run_teq sem P A A').status]

/-- To prove a refinement it suffices to match every non-excluded target outcome by a source
behaviour, assuming the source run does not fail (on any layout). -/
theorem refines_of_running {semT semS : Sem} {T S : Prog}
    (h : ∀ A, outcome semT T A ≠ .badLayout → (∀ A', (run semS S A').status = .running) →
      Beh semS S (outcome semT T A)) : Refines semT T semS S := by
  intro o ⟨A, hA, hb⟩
  by_cases hs : (run semS S A).status = .running
  · right
    rw [← hA]
    exact h A (hA ▸ hb) fun A' => (run_status_running_iff semS S A A').1 hs
  · left
    exact beh_ub_of_status semS S A (status_eq_ub_of_ne_running hs)

/-- On a non-excluded layout, a non-failing run completes with its trace. -/
theorem outcome_of_running {sem : Sem} {P : Prog} {A : Layout}
    (hb : layoutOK P A (run sem P A).conflicts = true) (hs : (run sem P A).status = .running) :
    outcome sem P A = .done (run sem P A).trace := by
  unfold outcome; simp [hb, hs]

theorem layoutOK_of_outcome_ne {sem : Sem} {P : Prog} {A : Layout}
    (h : outcome sem P A ≠ .badLayout) : layoutOK P A (run sem P A).conflicts = true := by
  unfold outcome at h
  cases hc : layoutOK P A (run sem P A).conflicts
  · simp [hc] at h
  · rfl

/-- `layoutOK` of a sublist (in particular a prefix) of the recorded pairs. -/
theorem layoutOK_of_subset (P : Prog) (A : Layout) {cs cs' : List (Nat × Nat)}
    (hsub : ∀ c ∈ cs, c ∈ cs') (h : layoutOK P A cs' = true) : layoutOK P A cs = true := by
  simp only [layoutOK, List.all_eq_true] at h ⊢
  exact fun c hc => h c (hsub c hc)

/-! ## Exact effect of cell writes and reads -/

theorem writeCellsK_eq (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    writeCellsK k s loc off vs =
      { s with
        mem := fun l o => if l = loc ∧ off ≤ o ∧ o < off + vs.length then vs.getD (o - off) .uninit
          else s.mem l o
        log := s.log ++ (List.range vs.length).map fun i => ⟨s.tick, s.inCall, loc, off + i, k⟩ } := by
  induction vs generalizing s off with
  | nil =>
    cases s; simp only [writeCellsK, List.length_nil, List.range_zero, List.map_nil, List.append_nil, St.mk.injEq, and_true]
    funext l o
    split
    · omega
    · rfl
  | cons v vs ih =>
    simp only [writeCellsK]
    rw [ih]
    cases s
    simp only [St.wr, St.logAcc, St.mk.injEq, true_and, and_true, List.length_cons]
    constructor
    · funext l o
      by_cases hl : l = loc
      · subst hl
        by_cases ho : o = off
        · subst ho; simp; intros; omega
        · by_cases h2 : off + 1 ≤ o ∧ o < off + 1 + vs.length
          · have h3 : o - off = (o - (off + 1)) + 1 := by omega
            simp [h2, h3]
            omega
          · simp [h2, ho]; omega
      · simp [hl]
    · rw [List.range_succ_eq_map]
      simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem readCells_frame (s : St) (loc off n : Nat) :
    (readCells s loc off n).1 =
      { s with log := (readCells s loc off n).1.log, status := (readCells s loc off n).1.status } := by
  induction n generalizing s off with
  | zero => rfl
  | succ n ih =>
    unfold readCells
    by_cases hv : s.mem loc off = .uninit
    · simp only [hv, ↓reduceIte]; rfl
    · simp only [hv, ↓reduceIte]
      have := ih (s.logAcc loc off .read) (off + 1)
      rcases hr : readCells (s.logAcc loc off .read) loc (off + 1) n with ⟨s', _ | vs⟩ <;>
        rw [hr] at this <;> simp only at this ⊢ <;> exact this


theorem readCells_spec (s : St) (loc off n : Nat) :
    (readCells s loc off n).2 =
      (if ∀ i, i < n → s.mem loc (off + i) ≠ .uninit then
        some ((List.range n).map fun i => s.mem loc (off + i)) else none) ∧
    (readCells s loc off n).1.status =
      (if ∀ i, i < n → s.mem loc (off + i) ≠ .uninit then s.status else .ub) ∧
    ∃ m, m ≤ n ∧
      (readCells s loc off n).1.log =
        s.log ++ (List.range m).map (fun i => (⟨s.tick, s.inCall, loc, off + i, .read⟩ : Access)) ∧
      (∀ i, i + 1 < m → s.mem loc (off + i) ≠ .uninit) ∧
      ((∀ i, i < n → s.mem loc (off + i) ≠ .uninit) → m = n) ∧
      (¬ (∀ i, i < n → s.mem loc (off + i) ≠ .uninit) → 0 < m ∧ s.mem loc (off + (m - 1)) = .uninit) := by
  induction n generalizing s off with
  | zero => simp [readCells]
  | succ n ih =>
    unfold readCells
    by_cases hv : s.mem loc off = .uninit
    · have hn : ¬ ∀ i, i < n + 1 → s.mem loc (off + i) ≠ .uninit := fun h => h 0 (by omega) (by simpa using hv)
      simp only [hv, ↓reduceIte]
      rw [if_neg hn, if_neg hn]
      refine ⟨rfl, rfl, 1, by omega, by simp [St.fail, St.logAcc], by intro i hi; omega, by intro h; exact absurd h hn, fun _ => ⟨by omega, by simpa using hv⟩⟩
    · simp only [hv, ↓reduceIte]
      obtain ⟨h1, h2, m, hm, h3, h4, h5, h6⟩ := ih (s.logAcc loc off .read) (off + 1)
      have hiff : (∀ i, i < n + 1 → s.mem loc (off + i) ≠ .uninit) ↔
          (∀ i, i < n → s.mem loc (off + 1 + i) ≠ .uninit) := by
        constructor
        · intro h i hi; have := h (i + 1) (by omega); rwa [show off + (i + 1) = off + 1 + i by omega] at this
        · intro h i hi
          cases i with
          | zero => simpa using hv
          | succ i => have := h i (by omega); rwa [show off + 1 + i = off + (i + 1) by omega] at this
      have hmem : (s.logAcc loc off .read).mem = s.mem := rfl
      rw [hmem] at h1 h2 h4 h5 h6
      rcases hr : readCells (s.logAcc loc off .read) loc (off + 1) n with ⟨s', _ | vs⟩
      · rw [hr] at h1 h2 h3
        simp only at h1 h2 h3 ⊢
        have hn : ¬ ∀ i, i < n → s.mem loc (off + 1 + i) ≠ .uninit := by
          intro h; rw [if_pos h] at h1; cases h1
        rw [if_neg (fun h => hn (hiff.1 h)), if_neg (fun h => hn (hiff.1 h))]
        rw [if_neg hn] at h2
        obtain ⟨h7, h8⟩ := h6 hn
        refine ⟨rfl, h2, m + 1, by omega, ?_, ?_, fun h => absurd h ((fun h => hn (hiff.1 h))), fun _ => ⟨by omega, ?_⟩⟩
        · rw [h3, List.range_succ_eq_map]; simp [St.logAcc, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
        · intro i hi
          cases i with
          | zero => simpa using hv
          | succ i => have := h4 i (by omega); rwa [show off + 1 + i = off + (i + 1) by omega] at this
        · rw [show off + (m + 1 - 1) = off + 1 + (m - 1) by omega]; exact h8
      · rw [hr] at h1 h2 h3
        simp only at h1 h2 h3 ⊢
        have hy : ∀ i, i < n → s.mem loc (off + 1 + i) ≠ .uninit := by
          by_cases h : ∀ i, i < n → s.mem loc (off + 1 + i) ≠ .uninit
          · exact h
          · rw [if_neg h] at h1; cases h1
        rw [if_pos (hiff.2 hy)]
        rw [if_pos hy] at h1 h2
        rw [if_pos (hiff.2 hy)]
        have hm' := h5 hy
        refine ⟨?_, h2, n + 1, by omega, ?_, ?_, fun _ => rfl, fun h => absurd (hiff.2 hy) h⟩
        · cases h1; rw [List.range_succ_eq_map]; simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
        · rw [h3, hm', List.range_succ_eq_map]; simp [St.logAcc, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
        · intro i hi; exact (hiff.2 hy) i (by omega)


end Toy.Coalesce
