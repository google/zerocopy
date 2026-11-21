import ToyCoalesce.Inv

/-!
# Proofs: in-order versus atomic assignment, and staging
-/

namespace Toy.Coalesce

namespace Stage

/-! ### Equality up to the access log -/

/-- Equality of all state fields except the access log. -/
def LEq (s t : St) : Prop := { s with log := [] } = { t with log := [] }

theorem LEq.iff {s t : St} : LEq s t ↔ s.mem = t.mem ∧ s.live = t.live ∧ s.alias = t.alias ∧
    s.trace = t.trace ∧ s.tick = t.tick ∧ s.inCall = t.inCall ∧ s.status = t.status ∧
    s.conflicts = t.conflicts := by
  cases s; cases t; simp [LEq]

theorem LEq.refl (s : St) : LEq s s := rfl
theorem LEq.symm {s t : St} (h : LEq s t) : LEq t s := Eq.symm h
theorem LEq.trans {s t u : St} (h1 : LEq s t) (h2 : LEq t u) : LEq s u := Eq.trans h1 h2
theorem LEq.mem {s t : St} (h : LEq s t) : s.mem = t.mem := (LEq.iff.1 h).1
theorem LEq.live {s t : St} (h : LEq s t) : s.live = t.live := (LEq.iff.1 h).2.1
theorem LEq.alias {s t : St} (h : LEq s t) : s.alias = t.alias := (LEq.iff.1 h).2.2.1
theorem LEq.trace {s t : St} (h : LEq s t) : s.trace = t.trace := (LEq.iff.1 h).2.2.2.1
theorem LEq.tick {s t : St} (h : LEq s t) : s.tick = t.tick := (LEq.iff.1 h).2.2.2.2.1
theorem LEq.inCall {s t : St} (h : LEq s t) : s.inCall = t.inCall := (LEq.iff.1 h).2.2.2.2.2.1
theorem LEq.status {s t : St} (h : LEq s t) : s.status = t.status := (LEq.iff.1 h).2.2.2.2.2.2.1
theorem LEq.conflicts {s t : St} (h : LEq s t) : s.conflicts = t.conflicts :=
  (LEq.iff.1 h).2.2.2.2.2.2.2

theorem LEq.fail {s t : St} (h : LEq s t) (k : Status) : LEq (s.fail k) (t.fail k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8⟩ := LEq.iff.1 h
  exact LEq.iff.2 ⟨h1, h2, h3, h4, h5, h6, rfl, h8⟩

theorem LEq.emit {s t : St} (h : LEq s t) (e : Event) : LEq (s.emit e) (t.emit e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
  exact LEq.iff.2 ⟨h1, h2, h3, by simp [St.emit, h4], h5, h6, h7, h8⟩

theorem LEq.setCtx {s t : St} (h : LEq s t) (al : Option (Nat × Place)) (c : Bool) :
    LEq { s with alias := al, inCall := c } { t with alias := al, inCall := c } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
  exact LEq.iff.2 ⟨h1, h2, rfl, h4, h5, rfl, h7, h8⟩

theorem LEq.setInCall {s t : St} (h : LEq s t) (c : Bool) :
    LEq { s with inCall := c } { t with inCall := c } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
  exact LEq.iff.2 ⟨h1, h2, h3, h4, h5, rfl, h7, h8⟩

theorem LEq.setTick {s t : St} (h : LEq s t) (n : Nat) :
    LEq { s with tick := n } { t with tick := n } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
  exact LEq.iff.2 ⟨h1, h2, h3, h4, rfl, h6, h7, h8⟩

/-! ### Field lemmas -/

theorem wk_mem (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).mem = fun l o =>
      if l = loc ∧ off ≤ o ∧ o < off + vs.length then vs.getD (o - off) .uninit else s.mem l o := by
  rw [writeCellsK_eq]
@[simp] theorem wk_live (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).live = s.live := by rw [writeCellsK_eq]
@[simp] theorem wk_alias (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).alias = s.alias := by rw [writeCellsK_eq]
@[simp] theorem wk_trace (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).trace = s.trace := by rw [writeCellsK_eq]
@[simp] theorem wk_tick (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).tick = s.tick := by rw [writeCellsK_eq]
@[simp] theorem wk_inCall (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).inCall = s.inCall := by rw [writeCellsK_eq]
@[simp] theorem wk_status (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).status = s.status := by rw [writeCellsK_eq]
@[simp] theorem wk_conflicts (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).conflicts = s.conflicts := by rw [writeCellsK_eq]

@[simp] theorem rc_mem (s : St) (loc off n : Nat) : (readCells s loc off n).1.mem = s.mem := by
  rw [readCells_frame]
@[simp] theorem rc_live (s : St) (loc off n : Nat) : (readCells s loc off n).1.live = s.live := by
  rw [readCells_frame]
@[simp] theorem rc_alias (s : St) (loc off n : Nat) :
    (readCells s loc off n).1.alias = s.alias := by rw [readCells_frame]
@[simp] theorem rc_trace (s : St) (loc off n : Nat) :
    (readCells s loc off n).1.trace = s.trace := by rw [readCells_frame]
@[simp] theorem rc_tick (s : St) (loc off n : Nat) : (readCells s loc off n).1.tick = s.tick := by
  rw [readCells_frame]
@[simp] theorem rc_inCall (s : St) (loc off n : Nat) :
    (readCells s loc off n).1.inCall = s.inCall := by rw [readCells_frame]
@[simp] theorem rc_conflicts (s : St) (loc off n : Nat) :
    (readCells s loc off n).1.conflicts = s.conflicts := by rw [readCells_frame]

theorem LEq.writeCellsK {s t : St} (h : LEq s t) (k : AccKind) (loc off : Nat) (vs : List Val) :
    LEq (writeCellsK k s loc off vs) (writeCellsK k t loc off vs) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
  refine LEq.iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wk_mem, h1, h2, h3, h4, h5, h6, h7, h8]

theorem LEq.writeCells {s t : St} (h : LEq s t) (loc off : Nat) (vs : List Val) :
    LEq (writeCells s loc off vs) (writeCells t loc off vs) := h.writeCellsK _ _ _ _

theorem LEq.resetCells {s t : St} (h : LEq s t) (loc n : Nat) :
    LEq (resetCells s loc n) (resetCells t loc n) := h.writeCellsK _ _ _ _

/-- Reading cells depends only on the memory at the read cells and on the status. -/
theorem readCells_congr {s t : St} {loc off n : Nat}
    (hm : ∀ i, i < n → s.mem loc (off + i) = t.mem loc (off + i)) (hst : s.status = t.status) :
    (readCells s loc off n).2 = (readCells t loc off n).2 ∧
      (readCells s loc off n).1.status = (readCells t loc off n).1.status := by
  obtain ⟨h1, h2, -⟩ := readCells_spec s loc off n
  obtain ⟨h1', h2', -⟩ := readCells_spec t loc off n
  have hiff : (∀ i, i < n → s.mem loc (off + i) ≠ .uninit) ↔
      (∀ i, i < n → t.mem loc (off + i) ≠ .uninit) := by
    constructor
    · intro h i hi; rw [← hm i hi]; exact h i hi
    · intro h i hi; rw [hm i hi]; exact h i hi
  have hl : (List.range n).map (fun i => s.mem loc (off + i)) =
      (List.range n).map (fun i => t.mem loc (off + i)) :=
    List.map_congr_left (fun i hi => hm i (List.mem_range.1 hi))
  rw [h1, h2, h1', h2', hl, hst]
  by_cases h : ∀ i, i < n → t.mem loc (off + i) ≠ .uninit
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h, ite_eq_left (hiff.2 h), ite_eq_left h]; exact ⟨rfl, rfl⟩
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]
    exact ⟨rfl, rfl⟩

theorem LEq.readCells {s t : St} (h : LEq s t) (loc off n : Nat) :
    LEq (readCells s loc off n).1 (readCells t loc off n).1 ∧
      (readCells s loc off n).2 = (readCells t loc off n).2 := by
  have hc := readCells_congr (s := s) (t := t) (loc := loc) (off := off) (n := n)
    (fun i _ => by rw [h.mem]) h.status
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
  refine ⟨LEq.iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, hc.2, ?_⟩, hc.1⟩ <;>
    simp [h1, h2, h3, h4, h5, h6, h8]

theorem readCells_some {s : St} {loc off n : Nat} {s' : St} {vs : List Val}
    (h : readCells s loc off n = (s', some vs)) :
    s'.status = s.status ∧ vs.length = n ∧ (∀ v ∈ vs, v ≠ .uninit) ∧
      vs = (List.range n).map (fun i => s.mem loc (off + i)) := by
  obtain ⟨h1, h2, -⟩ := readCells_spec s loc off n
  rw [h] at h1 h2
  simp only at h1 h2
  by_cases hc : ∀ i, i < n → s.mem loc (off + i) ≠ .uninit
  · rw [ite_eq_left hc] at h1 h2
    cases h1
    refine ⟨h2, by simp, ?_, rfl⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact hc i (List.mem_range.1 hi)
  · rw [ite_eq_right hc] at h1; cases h1

theorem readCells_none {s : St} {loc off n : Nat} {s' : St}
    (h : readCells s loc off n = (s', none)) : s'.status = .ub := by
  obtain ⟨h1, h2, -⟩ := readCells_spec s loc off n
  rw [h] at h1 h2
  simp only at h1 h2
  by_cases hc : ∀ i, i < n → s.mem loc (off + i) ≠ .uninit
  · rw [ite_eq_left hc] at h1; cases h1
  · rw [ite_eq_right hc] at h2; exact h2

end Stage

namespace Stage

/-! ### Operations that change only memory, log and status -/

structure MemOnly (s t : St) : Prop where
  live : t.live = s.live
  alias : t.alias = s.alias
  trace : t.trace = s.trace
  tick : t.tick = s.tick
  inCall : t.inCall = s.inCall
  conflicts : t.conflicts = s.conflicts

theorem MemOnly.refl (s : St) : MemOnly s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MemOnly.trans {s t u : St} (h1 : MemOnly s t) (h2 : MemOnly t u) : MemOnly s u :=
  ⟨h2.live.trans h1.live, h2.alias.trans h1.alias, h2.trace.trans h1.trace,
    h2.tick.trans h1.tick, h2.inCall.trans h1.inCall, h2.conflicts.trans h1.conflicts⟩

theorem memOnly_fail (s : St) (k : Status) : MemOnly s (s.fail k) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem memOnly_writeCellsK (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    MemOnly s (writeCellsK k s loc off vs) := by
  rw [writeCellsK_eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem memOnly_readCells (s : St) (loc off n : Nat) : MemOnly s (readCells s loc off n).1 := by
  rw [readCells_frame]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem memOnly_evalOp (ms : MoveSem) (P : Prog) (s : St) (o : Operand) :
    MemOnly s (evalOp ms P s o).1 := by
  cases o with
  | lit n => exact MemOnly.refl s
  | addrOf q =>
    simp only [evalOp]; split
    · exact MemOnly.refl s
    · exact memOnly_fail _ _
  | copy q =>
    simp only [evalOp]; split
    · exact memOnly_readCells _ _ _ _
    · exact memOnly_fail _ _
  | move q =>
    simp only [evalOp]; split
    · rename_i r _
      have h := memOnly_readCells s r.base r.off r.len
      rcases hr : readCells s r.base r.off r.len with ⟨s', _ | vs⟩
      · rw [hr] at h; exact h
      · rw [hr] at h
        simp only
        split
        · exact h.trans (memOnly_writeCellsK _ _ _ _ _)
        · exact h
    · exact memOnly_fail _ _
  | load p len =>
    simp only [evalOp]; split
    · rename_i r _
      split
      · have h := memOnly_readCells s r.base r.off 1
        split
        next s' l o heq =>
          rw [heq] at h
          split
          · exact h.trans (memOnly_readCells _ _ _ _)
          · exact h.trans (memOnly_fail _ _)
        next s' x _ heq => rw [heq] at h; exact h.trans (memOnly_fail _ _)
        next s' heq => rw [heq] at h; exact h
      · exact memOnly_fail _ _
    · exact memOnly_fail _ _

theorem memOnly_evalOps (ms : MoveSem) (P : Prog) (s : St) (os : List Operand) :
    MemOnly s (evalOps ms P s os).1 := by
  induction os generalizing s with
  | nil => exact MemOnly.refl s
  | cons o os ih =>
    simp only [evalOps]
    have h := memOnly_evalOp ms P s o
    rcases hr : evalOp ms P s o with ⟨s', _ | vs⟩
    · rw [hr] at h; exact h
    · rw [hr] at h
      simp only
      have h2 := h.trans (ih s')
      rcases hr2 : evalOps ms P s' os with ⟨s'', _ | ws⟩ <;> rw [hr2] at h2 <;> exact h2

theorem memOnly_writeInOrder (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat)
    (os : List Operand) : MemOnly s (writeInOrder ms P s loc off os) := by
  induction os generalizing s off with
  | nil => exact MemOnly.refl s
  | cons o os ih =>
    simp only [writeInOrder]
    have h := memOnly_evalOp ms P s o
    rcases hr : evalOp ms P s o with ⟨s', _ | vs⟩
    · rw [hr] at h; exact h
    · rw [hr] at h
      exact (h.trans (memOnly_writeCellsK _ _ _ _ _)).trans (ih _ _)

/-! ### Results of operand evaluation -/

theorem resolvePlace_congr {P : Prog} {s t : St} (hl : s.live = t.live) (ha : s.alias = t.alias)
    (q : Place) : resolvePlace P s q = resolvePlace P t q := by
  unfold resolvePlace; rw [hl, ha]

theorem evalOp_some {ms : MoveSem} {P : Prog} {s s' : St} {o : Operand} {vs : List Val}
    (h : evalOp ms P s o = (s', some vs)) :
    s'.status = s.status ∧ vs.length = o.len ∧ ∀ v ∈ vs, v ≠ .uninit := by
  cases o with
  | lit n =>
    simp only [evalOp, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, by simp⟩
  | addrOf q =>
    simp only [evalOp] at h
    split at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, by simp⟩
    · simp at h
  | copy q =>
    simp only [evalOp] at h
    split at h
    · rename_i r hr
      obtain ⟨h1, h2, h3, -⟩ := readCells_some h
      exact ⟨h1, h2.trans (Inv.resolvePlace_spec hr).2.2, h3⟩
    · simp at h
  | move q =>
    simp only [evalOp] at h
    split at h
    · rename_i r hr
      rcases e : readCells s r.base r.off r.len with ⟨s1, _ | ws⟩
      · rw [e] at h; simp at h
      · rw [e] at h
        obtain ⟨h1, h2, h3, -⟩ := readCells_some e
        simp only at h
        split at h
        · simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [writeCells, h1], h2.trans (Inv.resolvePlace_spec hr).2.2, h3⟩
        · simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨h1, h2.trans (Inv.resolvePlace_spec hr).2.2, h3⟩
    · simp at h
  | load p len =>
    simp only [evalOp] at h
    split at h
    · rename_i r hr
      split at h
      · rcases e : readCells s r.base r.off 1 with ⟨s1, _ | ws⟩
        · rw [e] at h; simp at h
        · rw [e] at h
          obtain ⟨h1, -, -, -⟩ := readCells_some e
          split at h
          next x s'' l o heq =>
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            split at h
            · obtain ⟨h4, h5, h6, -⟩ := readCells_some h
              exact ⟨h4.trans h1, h5, h6⟩
            · simp at h
          next => simp at h
          next => simp at h
      · simp at h
    · simp at h

theorem evalOp_none {ms : MoveSem} {P : Prog} {s s' : St} {o : Operand}
    (h : evalOp ms P s o = (s', none)) : s'.status = .ub := by
  cases o with
  | lit n => simp [evalOp] at h
  | addrOf q =>
    simp only [evalOp] at h
    split at h
    · simp at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | copy q =>
    simp only [evalOp] at h
    split at h
    · exact readCells_none h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | move q =>
    simp only [evalOp] at h
    split at h
    · rename_i r hr
      rcases e : readCells s r.base r.off r.len with ⟨s1, _ | ws⟩
      · rw [e] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact readCells_none e
      · rw [e] at h
        simp only at h
        split at h <;> simp at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | load p len =>
    simp only [evalOp] at h
    split at h
    · rename_i r hr
      split at h
      · rcases e : readCells s r.base r.off 1 with ⟨s1, _ | ws⟩
        · rw [e] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact readCells_none e
        · rw [e] at h
          split at h
          next x s'' l o heq =>
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            split at h
            · exact readCells_none h
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
          next => simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
          next x s'' heq => simp at heq
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl

theorem evalOps_some {ms : MoveSem} {P : Prog} :
    ∀ {os : List Operand} {s s' : St} {vs : List Val}, evalOps ms P s os = (s', some vs) →
      s'.status = s.status ∧ vs.length = (os.map Operand.len).sum ∧ ∀ v ∈ vs, v ≠ .uninit
  | [], s, s', vs, h => by
    simp only [evalOps, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, by simp⟩
  | o :: os, s, s', vs, h => by
    simp only [evalOps] at h
    rcases e : evalOp ms P s o with ⟨s1, _ | v1⟩
    · rw [e] at h; simp at h
    · rw [e] at h
      simp only at h
      rcases e2 : evalOps ms P s1 os with ⟨s2, _ | v2⟩
      · rw [e2] at h; simp at h
      · rw [e2] at h
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := evalOp_some e
        obtain ⟨h4, h5, h6⟩ := evalOps_some e2
        refine ⟨h4.trans h1, by simp [h2, h5], ?_⟩
        intro v hv
        rcases List.mem_append.1 hv with hv | hv
        · exact h3 v hv
        · exact h6 v hv

theorem evalOps_none {ms : MoveSem} {P : Prog} :
    ∀ {os : List Operand} {s s' : St}, evalOps ms P s os = (s', none) → s'.status = .ub
  | [], s, s', h => by simp [evalOps] at h
  | o :: os, s, s', h => by
    simp only [evalOps] at h
    rcases e : evalOp ms P s o with ⟨s1, _ | v1⟩
    · rw [e] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact evalOp_none e
    · rw [e] at h
      simp only at h
      rcases e2 : evalOps ms P s1 os with ⟨s2, _ | v2⟩
      · rw [e2] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact evalOps_none e2
      · rw [e2] at h; simp at h

end Stage

namespace Stage

/-! ### Log irrelevance of the interpreter -/

theorem LEq.evalOp {s t : St} (h : LEq s t) (ms : MoveSem) (P : Prog) (o : Operand) :
    LEq (evalOp ms P s o).1 (evalOp ms P t o).1 ∧ (evalOp ms P s o).2 = (evalOp ms P t o).2 := by
  have hr : ∀ q, resolvePlace P s q = resolvePlace P t q := resolvePlace_congr h.live h.alias
  cases o with
  | lit n => exact ⟨h, rfl⟩
  | addrOf q =>
    simp only [_root_.Toy.Coalesce.evalOp, hr q]
    cases resolvePlace P t q with
    | some r => exact ⟨h, rfl⟩
    | none => exact ⟨h.fail _, rfl⟩
  | copy q =>
    simp only [_root_.Toy.Coalesce.evalOp, hr q]
    cases resolvePlace P t q with
    | some r => exact h.readCells _ _ _
    | none => exact ⟨h.fail _, rfl⟩
  | move q =>
    simp only [_root_.Toy.Coalesce.evalOp, hr q]
    cases resolvePlace P t q with
    | none => exact ⟨h.fail _, rfl⟩
    | some r =>
      simp only
      obtain ⟨h1, h2⟩ := h.readCells r.base r.off r.len
      rcases e1 : _root_.Toy.Coalesce.readCells s r.base r.off r.len with ⟨s1, v1⟩
      rcases e2 : _root_.Toy.Coalesce.readCells t r.base r.off r.len with ⟨t1, v2⟩
      rw [e1, e2] at h1 h2
      simp only at h1 h2
      subst h2
      cases v1 with
      | none => exact ⟨h1, rfl⟩
      | some vs =>
        simp only
        split
        · exact ⟨h1.writeCells _ _ _, rfl⟩
        · exact ⟨h1, rfl⟩
  | load p len =>
    simp only [_root_.Toy.Coalesce.evalOp, hr p]
    cases resolvePlace P t p with
    | none => exact ⟨h.fail _, rfl⟩
    | some r =>
      simp only
      split
      · obtain ⟨h1, h2⟩ := h.readCells r.base r.off 1
        rcases e1 : _root_.Toy.Coalesce.readCells s r.base r.off 1 with ⟨s1, v1⟩
        rcases e2 : _root_.Toy.Coalesce.readCells t r.base r.off 1 with ⟨t1, v2⟩
        rw [e1, e2] at h1 h2
        simp only at h1 h2
        subst h2
        rcases v1 with _ | ⟨_ | ⟨v, _ | ⟨w, ws⟩⟩⟩
        · exact ⟨h1, rfl⟩
        · exact ⟨h1.fail _, rfl⟩
        · cases v with
          | ptr l o =>
            simp only [h1.live]
            by_cases hc : t1.live l = true ∧ o + len ≤ P.size l
            · rw [ite_eq_left hc, ite_eq_left hc]; exact h1.readCells _ _ _
            · rw [ite_eq_right hc, ite_eq_right hc]; exact ⟨h1.fail _, rfl⟩
          | _ => exact ⟨h1.fail _, rfl⟩
        · cases v <;> exact ⟨h1.fail _, rfl⟩
      · exact ⟨h.fail _, rfl⟩

theorem LEq.evalOps {ms : MoveSem} {P : Prog} (os : List Operand) :
    ∀ {s t : St}, LEq s t →
      LEq (evalOps ms P s os).1 (evalOps ms P t os).1 ∧ (evalOps ms P s os).2 = (evalOps ms P t os).2 := by
  induction os with
  | nil => intro s t h; exact ⟨h, rfl⟩
  | cons o os ih =>
    intro s t h
    simp only [_root_.Toy.Coalesce.evalOps]
    obtain ⟨h1, h2⟩ := h.evalOp ms P o
    rcases e1 : _root_.Toy.Coalesce.evalOp ms P s o with ⟨s1, v1⟩
    rcases e2 : _root_.Toy.Coalesce.evalOp ms P t o with ⟨t1, v2⟩
    rw [e1, e2] at h1 h2
    simp only at h1 h2
    subst h2
    cases v1 with
    | none => exact ⟨h1, rfl⟩
    | some vs =>
      simp only
      obtain ⟨h3, h4⟩ := ih h1
      rcases e3 : _root_.Toy.Coalesce.evalOps ms P s1 os with ⟨s2, w1⟩
      rcases e4 : _root_.Toy.Coalesce.evalOps ms P t1 os with ⟨t2, w2⟩
      rw [e3, e4] at h3 h4
      simp only at h3 h4
      subst h4
      cases w1 <;> exact ⟨h3, rfl⟩

theorem LEq.writeInOrder {ms : MoveSem} {P : Prog} (loc : Nat) (os : List Operand) :
    ∀ {s t : St} (off : Nat), LEq s t →
      LEq (writeInOrder ms P s loc off os) (writeInOrder ms P t loc off os) := by
  induction os with
  | nil => intro s t off h; exact h
  | cons o os ih =>
    intro s t off h
    simp only [_root_.Toy.Coalesce.writeInOrder]
    obtain ⟨h1, h2⟩ := h.evalOp ms P o
    rcases e1 : _root_.Toy.Coalesce.evalOp ms P s o with ⟨s1, v1⟩
    rcases e2 : _root_.Toy.Coalesce.evalOp ms P t o with ⟨t1, v2⟩
    rw [e1, e2] at h1 h2
    simp only at h1 h2
    subst h2
    cases v1 with
    | none => exact h1
    | some vs => exact ih _ (h1.writeCells _ _ _)

theorem LEq.allocate {s t : St} (h : LEq s t) (P : Prog) (x : Nat) :
    LEq (allocate P s x) (allocate P t x) := by
  have hl : liveOthers P s x = liveOthers P t x := by simp only [liveOthers, h.live]
  simp only [_root_.Toy.Coalesce.allocate]
  split
  · rw [hl]
    apply LEq.resetCells
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 h
    exact LEq.iff.2 ⟨h1, by simp [h2], h3, h4, h5, h6, h7, by simp [h8]⟩
  · exact h.fail _

theorem LEq.deallocate {s t : St} (h : LEq s t) (P : Prog) (x : Nat) :
    LEq (deallocate P s x) (deallocate P t x) := by
  simp only [_root_.Toy.Coalesce.deallocate, h.live]
  split
  · have := h.resetCells x (P.size x)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := LEq.iff.1 this
    exact LEq.iff.2 ⟨h1, by simp [h2], h3, h4, h5, h6, h7, h8⟩
  · exact h

theorem LEq.cmpOp {s t : St} (h : LEq s t) (ms : MoveSem) (P : Prog) (A : Layout) (a b : Operand)
    (f : Nat → Nat → Bool) : LEq (cmpOp ms P A s a b f) (cmpOp ms P A t a b f) := by
  unfold _root_.Toy.Coalesce.cmpOp
  obtain ⟨h1, h2⟩ := h.evalOp ms P a
  rcases e1 : _root_.Toy.Coalesce.evalOp ms P s a with ⟨s1, v1⟩
  rcases e2 : _root_.Toy.Coalesce.evalOp ms P t a with ⟨t1, v2⟩
  rw [e1, e2] at h1 h2
  simp only at h1 h2
  subst h2
  rcases v1 with _ | ⟨_ | ⟨va, _ | ⟨w, ws⟩⟩⟩
  · exact h1
  · exact h1.fail _
  · simp only
    obtain ⟨h3, h4⟩ := h1.evalOp ms P b
    rcases e3 : _root_.Toy.Coalesce.evalOp ms P s1 b with ⟨s2, w1⟩
    rcases e4 : _root_.Toy.Coalesce.evalOp ms P t1 b with ⟨t2, w2⟩
    rw [e3, e4] at h3 h4
    simp only at h3 h4
    subst h4
    rcases w1 with _ | ⟨_ | ⟨vb, _ | ⟨w', ws'⟩⟩⟩
    · exact h3
    · exact h3.fail _
    · cases va <;> cases vb <;> simp only [Val.addr?] <;>
        first
        | exact h3.emit _
        | exact h3.fail _
    · exact h3.fail _
  · exact h1.fail _

theorem LEq.execBasic {s t : St} (h : LEq s t) (sem : Sem) (P : Prog) (A : Layout) (st : Stmt) :
    LEq (execBasic sem P A s st) (execBasic sem P A t st) := by
  by_cases hs : t.status = .running
  · have hss : s.status = .running := h.status.trans hs
    have hr : ∀ q, resolvePlace P s q = resolvePlace P t q := resolvePlace_congr h.live h.alias
    unfold _root_.Toy.Coalesce.execBasic
    rw [ite_eq_right (fun h' => h' hss), ite_eq_right (fun h' => h' hs)]
    cases st with
    | storageLive x =>
      simp only [h.inCall]
      split
      · exact h.fail _
      · exact h.allocate _ _
    | storageDead x =>
      simp only [h.inCall]
      split
      · exact h.fail _
      · exact h.deallocate _ _
    | assign lhs rhs =>
      simp only [hr]
      split
      · exact h.fail _
      · cases resolvePlace P t lhs with
        | none => exact h.fail _
        | some r =>
          simp only
          cases sem.assign with
          | atomic =>
            simp only
            obtain ⟨h1, h2⟩ := LEq.evalOps (ms := sem.move) (P := P) rhs h
            rcases e1 : _root_.Toy.Coalesce.evalOps sem.move P s rhs with ⟨s1, v1⟩
            rcases e2 : _root_.Toy.Coalesce.evalOps sem.move P t rhs with ⟨t1, v2⟩
            rw [e1, e2] at h1 h2; simp only at h1 h2; subst h2
            cases v1 with
            | none => exact h1
            | some vs => exact h1.writeCells _ _ _
          | inOrder => exact LEq.writeInOrder _ _ _ h
    | store p v =>
      simp only [hr]
      cases resolvePlace P t p with
      | none => exact h.fail _
      | some r =>
        simp only
        split
        · obtain ⟨h1, h2⟩ := h.readCells r.base r.off 1
          rcases e1 : _root_.Toy.Coalesce.readCells s r.base r.off 1 with ⟨s1, v1⟩
          rcases e2 : _root_.Toy.Coalesce.readCells t r.base r.off 1 with ⟨t1, v2⟩
          rw [e1, e2] at h1 h2
          simp only at h1 h2
          subst h2
          rcases v1 with _ | ⟨_ | ⟨v1, _ | ⟨w, ws⟩⟩⟩
          · exact h1
          · exact h1.fail _
          · cases v1 with
            | ptr l o =>
              simp only
              obtain ⟨h3, h4⟩ := h1.evalOp sem.move P v
              rcases e3 : _root_.Toy.Coalesce.evalOp sem.move P s1 v with ⟨s2, w1⟩
              rcases e4 : _root_.Toy.Coalesce.evalOp sem.move P t1 v with ⟨t2, w2⟩
              rw [e3, e4] at h3 h4
              simp only at h3 h4
              subst h4
              cases w1 with
              | none => exact h3
              | some vs =>
                simp only [h3.live]
                by_cases hc : t2.live l = true ∧ o + vs.length ≤ P.size l
                · rw [ite_eq_left hc, ite_eq_left hc]; exact h3.writeCells _ _ _
                · rw [ite_eq_right hc, ite_eq_right hc]; exact h3.fail _
            | _ => exact h1.fail _
          · cases v1 <;> exact h1.fail _
        · exact h.fail _
    | ptrEq a b => exact h.cmpOp _ _ _ _ _ _
    | ptrInRange a b n => exact h.cmpOp _ _ _ _ _ _
    | out o =>
      simp only
      obtain ⟨h1, h2⟩ := h.evalOp sem.move P o
      rcases e1 : _root_.Toy.Coalesce.evalOp sem.move P s o with ⟨s1, v1⟩
      rcases e2 : _root_.Toy.Coalesce.evalOp sem.move P t o with ⟨t1, v2⟩
      rw [e1, e2] at h1 h2
      simp only at h1 h2
      subst h2
      cases v1 with
      | none => exact h1
      | some vs => exact h1.emit _
    | call fn a => exact h.fail _
    | nop => exact h
  · rw [execBasic_of_not_running _ (by rw [h.status]; exact hs), execBasic_of_not_running _ hs]
    exact h

theorem LEq.execCallee {sem : Sem} {P : Prog} {A : Layout} (b : List Stmt) :
    ∀ {s t : St}, LEq s t → LEq (execCallee sem P A s b) (execCallee sem P A t b) := by
  induction b with
  | nil => intro s t h; exact h
  | cons st b ih =>
    intro s t h
    simp only [_root_.Toy.Coalesce.execCallee, List.foldl_cons]
    exact ih (h.execBasic sem P A st)

theorem execStmt_eq_execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : ∀ fn a, st ≠ .call fn a) : execStmt sem P A s st = execBasic sem P A s st := by
  by_cases hs : s.status = .running
  · unfold execStmt
    rw [ite_eq_right (fun h' => h' hs)]
    cases st <;> first | rfl | exact absurd rfl (h _ _)
  · rw [execStmt_of_not_running _ hs, execBasic_of_not_running _ hs]

theorem LEq.execStmt {s t : St} (h : LEq s t) (sem : Sem) (P : Prog) (A : Layout) (st : Stmt) :
    LEq (execStmt sem P A s st) (execStmt sem P A t st) := by
  by_cases hs : t.status = .running
  · cases st with
    | call fn arg =>
      have hss : s.status = .running := h.status.trans hs
      have hr : ∀ q, resolvePlace P s q = resolvePlace P t q := resolvePlace_congr h.live h.alias
      unfold _root_.Toy.Coalesce.execStmt
      rw [ite_eq_right (fun h' => h' hss), ite_eq_right (fun h' => h' hs)]
      simp only
      split
      · next _ _ q _ =>
        simp only [hr]
        cases resolvePlace P t q with
        | none => exact h.fail _
        | some r =>
          simp only
          by_cases hc : r.len ≠ P.size (P.fn fn).prm
          · rw [ite_eq_left hc, ite_eq_left hc]; exact h.fail _
          · rw [ite_eq_right hc, ite_eq_right hc]
            exact (LEq.execCallee _ (h.setCtx _ _)).setCtx none false
      · next a _ _ _ =>
        obtain ⟨h1, h2⟩ := h.evalOp sem.move P a
        rcases e1 : _root_.Toy.Coalesce.evalOp sem.move P s a with ⟨s1, v1⟩
        rcases e2 : _root_.Toy.Coalesce.evalOp sem.move P t a with ⟨t1, v2⟩
        rw [e1, e2] at h1 h2
        simp only at h1 h2
        subst h2
        cases v1 with
        | none => exact h1
        | some vs =>
          simp only [h1.live]
          by_cases hc : vs.length ≠ P.size (P.fn fn).prm ∨ t1.live (P.fn fn).prm = true
          · rw [ite_eq_left hc, ite_eq_left hc]; exact h1.fail _
          · rw [ite_eq_right hc, ite_eq_right hc]
            exact (LEq.execCallee _ (((h1.allocate _ _).writeCells _ _ _).setInCall true)).setInCall
              false |>.deallocate _ _
    | _ =>
      rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h),
        execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
      exact h.execBasic _ _ _ _
  · rw [execStmt_of_not_running _ (by rw [h.status]; exact hs), execStmt_of_not_running _ hs]
    exact h

end Stage

namespace Stage

/-! ### In-order versus atomic assignment -/

/-- The cells of `r` are disjoint from the window `[a, a + n)` of local `loc`. -/
def CellsDisj (loc a n : Nat) (r : Place) : Prop := r.base ≠ loc ∨ r.off + r.len ≤ a ∨ a + n ≤ r.off

/-- Operand `o`, evaluated in `s`, reads and writes no cell of the window `[a, a + n)` of `loc`. -/
def OpOK (P : Prog) (s : St) (loc a n : Nat) : Operand → Prop
  | .lit _ => True
  | .addrOf _ => True
  | .copy q => ∀ r, resolvePlace P s q = some r → CellsDisj loc a n r
  | .move q => ∀ r, resolvePlace P s q = some r → CellsDisj loc a n r
  | .load _ _ => False

theorem OpOK.mono {P : Prog} {s : St} {loc a n m : Nat} {o : Operand} (h : OpOK P s loc a n o)
    (hm : m ≤ n) : OpOK P s loc a m o := by
  cases o with
  | copy q => intro r hr; have := h r hr; unfold CellsDisj at this ⊢; omega
  | move q => intro r hr; have := h r hr; unfold CellsDisj at this ⊢; omega
  | lit n => trivial
  | addrOf q => trivial
  | load p l => exact h

theorem OpOK.congr {P : Prog} {s t : St} {loc a n : Nat} {o : Operand} (h : OpOK P s loc a n o)
    (hl : s.live = t.live) (ha : s.alias = t.alias) : OpOK P t loc a n o := by
  cases o with
  | copy q => intro r hr; rw [← resolvePlace_congr hl ha] at hr; exact h r hr
  | move q => intro r hr; rw [← resolvePlace_congr hl ha] at hr; exact h r hr
  | lit n => trivial
  | addrOf q => trivial
  | load p l => exact h

theorem writeCells_mem_disj (s : St) (loc a : Nat) (ws : List Val) (r : Place)
    (hd : CellsDisj loc a ws.length r) :
    ∀ i, i < r.len → (writeCells s loc a ws).mem r.base (r.off + i) = s.mem r.base (r.off + i) := by
  intro i hi
  simp only [writeCells, wk_mem]
  rw [ite_eq_right]
  rintro ⟨h1, h2, h3⟩
  unfold CellsDisj at hd
  omega

theorem fail_writeCells_comm (s : St) (k : Status) (loc a : Nat) (ws : List Val) :
    LEq ((writeCells s loc a ws).fail k) (writeCells (s.fail k) loc a ws) := by
  refine LEq.iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [writeCells, wk_mem, St.fail]

theorem writeCells_comm (s : St) (l1 o1 : Nat) (vs1 : List Val) (l2 o2 : Nat) (vs2 : List Val)
    (hd : l1 ≠ l2 ∨ o1 + vs1.length ≤ o2 ∨ o2 + vs2.length ≤ o1) :
    LEq (writeCells (writeCells s l1 o1 vs1) l2 o2 vs2) (writeCells (writeCells s l2 o2 vs2) l1 o1 vs1) := by
  refine LEq.iff.2 ⟨?_, by simp [writeCells], by simp [writeCells], by simp [writeCells],
    by simp [writeCells], by simp [writeCells], by simp [writeCells], by simp [writeCells]⟩
  simp only [writeCells]
  rw [wk_mem, wk_mem, wk_mem, wk_mem]
  funext l o
  dsimp only
  by_cases c1 : l = l1 ∧ o1 ≤ o ∧ o < o1 + vs1.length
  · by_cases c2 : l = l2 ∧ o2 ≤ o ∧ o < o2 + vs2.length
    · exfalso; omega
    · simp only [ite_eq_right c2, ite_eq_left c1]
  · by_cases c2 : l = l2 ∧ o2 ≤ o ∧ o < o2 + vs2.length
    · simp only [ite_eq_left c2, ite_eq_right c1]
    · simp only [ite_eq_right c2, ite_eq_right c1]

theorem writeCells_append (loc : Nat) (ws v : List Val) :
    ∀ (s : St) (a : Nat), writeCells (writeCells s loc a ws) loc (a + ws.length) v =
      writeCells s loc a (ws ++ v) := by
  induction ws with
  | nil => intro s a; rfl
  | cons w ws ih =>
    intro s a
    have := ih (s.wr .write loc a w) (a + 1)
    simp only [writeCells, writeCellsK, List.cons_append, List.length_cons] at this ⊢
    rw [show a + (ws.length + 1) = a + 1 + ws.length by omega]
    exact this

/-- Writing cells disjoint from those an operand touches commutes with evaluating it. -/
theorem evalOp_writeCells_comm (ms : MoveSem) (P : Prog) (s : St) (loc a : Nat) (ws : List Val)
    (o : Operand) (ho : OpOK P s loc a ws.length o) :
    LEq (evalOp ms P (writeCells s loc a ws) o).1 (writeCells (evalOp ms P s o).1 loc a ws) ∧
      (evalOp ms P (writeCells s loc a ws) o).2 = (evalOp ms P s o).2 := by
  have hres : ∀ q, resolvePlace P (writeCells s loc a ws) q = resolvePlace P s q :=
    resolvePlace_congr (by simp [writeCells]) (by simp [writeCells])
  have key : ∀ r, CellsDisj loc a ws.length r →
      LEq (readCells (writeCells s loc a ws) r.base r.off r.len).1
        (writeCells (readCells s r.base r.off r.len).1 loc a ws) ∧
      (readCells (writeCells s loc a ws) r.base r.off r.len).2 =
        (readCells s r.base r.off r.len).2 := by
    intro r hd
    obtain ⟨c1, c2⟩ := readCells_congr (writeCells_mem_disj s loc a ws r hd)
      (by simp [writeCells])
    refine ⟨LEq.iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, c1⟩
    · simp [writeCells, wk_mem]
    · simp [writeCells]
    · simp [writeCells]
    · simp [writeCells]
    · simp [writeCells]
    · simp [writeCells]
    · rw [c2]; simp [writeCells]
    · simp [writeCells]
  cases o with
  | lit n => exact ⟨LEq.refl _, rfl⟩
  | addrOf q =>
    simp only [evalOp, hres q]
    cases resolvePlace P s q with
    | some r => exact ⟨LEq.refl _, rfl⟩
    | none => exact ⟨fail_writeCells_comm _ _ _ _ _, rfl⟩
  | copy q =>
    simp only [evalOp, hres q]
    cases hr : resolvePlace P s q with
    | some r => exact key r (ho r hr)
    | none => exact ⟨fail_writeCells_comm _ _ _ _ _, rfl⟩
  | move q =>
    simp only [evalOp, hres q]
    cases hr : resolvePlace P s q with
    | none => exact ⟨fail_writeCells_comm _ _ _ _ _, rfl⟩
    | some r =>
      simp only
      have hd := ho r hr
      obtain ⟨k1, k2⟩ := key r hd
      rcases e1 : readCells (writeCells s loc a ws) r.base r.off r.len with ⟨w1, v1⟩
      rcases e2 : readCells s r.base r.off r.len with ⟨s1, v2⟩
      rw [e1, e2] at k1 k2
      simp only at k1 k2
      subst k2
      cases v1 with
      | none => exact ⟨k1, rfl⟩
      | some vs =>
        simp only
        by_cases hms : ms = .deinit
        · rw [ite_eq_left hms, ite_eq_left hms]
          refine ⟨(k1.writeCells _ _ _).trans (writeCells_comm _ _ _ _ _ _ _ ?_), rfl⟩
          unfold CellsDisj at hd
          simp only [List.length_replicate]
          omega
        · rw [ite_eq_right hms, ite_eq_right hms]
          exact ⟨k1, rfl⟩
  | load p l => exact absurd ho id

/-- Relation between the in-order and the atomic run: equal up to the log while running; once
failed, equal status, trace, allocation pairs and tick. -/
def RR (s t : St) : Prop :=
  (s.status = .running ∧ LEq s t) ∨
  (s.status ≠ .running ∧ t.status ≠ .running ∧ s.trace = t.trace ∧ s.conflicts = t.conflicts ∧
    s.tick = t.tick)

theorem RR.of_leq {s t : St} (h : LEq s t) : RR s t := by
  by_cases hs : s.status = .running
  · exact Or.inl ⟨hs, h⟩
  · exact Or.inr ⟨hs, by rw [← h.status]; exact hs, h.trace, h.conflicts, h.tick⟩

theorem RR.leq_left {s s' t : St} (h1 : LEq s' s) (h2 : RR s t) : RR s' t := by
  rcases h2 with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · exact Or.inl ⟨h1.status.trans hs, h1.trans h⟩
  · exact Or.inr ⟨by rw [h1.status]; exact hs, ht, h1.trace.trans h3, h1.conflicts.trans h4,
      h1.tick.trans h5⟩

theorem RR.leq_right {s t t' : St} (h1 : RR s t) (h2 : LEq t t') : RR s t' := by
  rcases h1 with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · exact Or.inl ⟨hs, h.trans h2⟩
  · exact Or.inr ⟨hs, by rw [← h2.status]; exact ht, h3.trans h2.trace, h4.trans h2.conflicts,
      h5.trans h2.tick⟩

theorem RR.status {s t : St} (h : RR s t) : s.status = t.status := by
  rcases h with ⟨_, h⟩ | ⟨hs, ht, -⟩
  · exact h.status
  · rw [status_eq_ub_of_ne_running hs, status_eq_ub_of_ne_running ht]

theorem RR.trace {s t : St} (h : RR s t) : s.trace = t.trace := by
  rcases h with ⟨_, h⟩ | ⟨_, _, h3, _, _⟩
  · exact h.trace
  · exact h3

theorem RR.conflicts {s t : St} (h : RR s t) : s.conflicts = t.conflicts := by
  rcases h with ⟨_, h⟩ | ⟨_, _, _, h4, _⟩
  · exact h.conflicts
  · exact h4

theorem RR.setCtx {s t : St} (h : RR s t) (al : Option (Nat × Place)) (c : Bool) :
    RR { s with alias := al, inCall := c } { t with alias := al, inCall := c } := by
  rcases h with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · exact Or.inl ⟨hs, h.setCtx al c⟩
  · exact Or.inr ⟨hs, ht, h3, h4, h5⟩

theorem RR.setInCall {s t : St} (h : RR s t) (c : Bool) :
    RR { s with inCall := c } { t with inCall := c } := by
  rcases h with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · exact Or.inl ⟨hs, h.setInCall c⟩
  · exact Or.inr ⟨hs, ht, h3, h4, h5⟩

theorem RR.bumpTick {s t : St} (h : RR s t) :
    RR { s with tick := s.tick + 1 } { t with tick := t.tick + 1 } := by
  rcases h with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · refine Or.inl ⟨hs, ?_⟩
    rw [h.tick]; exact h.setTick _
  · exact Or.inr ⟨hs, ht, h3, h4, by simp [h5]⟩

theorem deallocate_frame (P : Prog) (s : St) (x : Nat) :
    (deallocate P s x).status = s.status ∧ (deallocate P s x).trace = s.trace ∧
      (deallocate P s x).conflicts = s.conflicts ∧ (deallocate P s x).tick = s.tick := by
  unfold deallocate
  split
  · simp [resetCells]
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem RR.deallocate {s t : St} (h : RR s t) (P : Prog) (x : Nat) :
    RR (deallocate P s x) (deallocate P t x) := by
  rcases h with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · exact RR.of_leq (h.deallocate P x)
  · obtain ⟨a1, a2, a3, a4⟩ := deallocate_frame P s x
    obtain ⟨b1, b2, b3, b4⟩ := deallocate_frame P t x
    exact Or.inr ⟨by rw [a1]; exact hs, by rw [b1]; exact ht, by rw [a2, b2, h3],
      by rw [a3, b3, h4], by rw [a4, b4, h5]⟩

/-- In-order writes of disjoint operands agree with atomic evaluation followed by one write. -/
theorem writeInOrder_core (ms : MoveSem) (P : Prog) (loc a n : Nat) :
    ∀ (os : List Operand) (s : St) (ws : List Val), s.status = .running →
      (∀ o ∈ os, OpOK P s loc a n o) →
      ws.length + (os.map Operand.len).sum ≤ n →
      RR (writeInOrder ms P (writeCells s loc a ws) loc (a + ws.length) os)
        (match evalOps ms P s os with
         | (s', some vs) => writeCells s' loc a (ws ++ vs)
         | (s', none) => s')
  | [], s, ws, hs, _, _ => by
    simp only [writeInOrder, evalOps, List.append_nil]
    exact RR.of_leq (LEq.refl _)
  | o :: os, s, ws, hs, hok, hlen => by
    simp only [writeInOrder, evalOps]
    simp only [List.map_cons, List.sum_cons] at hlen
    have hok0 : OpOK P s loc a ws.length o :=
      (hok o (List.mem_cons_self ..)).mono (by omega)
    obtain ⟨k1, k2⟩ := evalOp_writeCells_comm ms P s loc a ws o hok0
    rcases e1 : evalOp ms P (writeCells s loc a ws) o with ⟨x, v1⟩
    rcases e2 : evalOp ms P s o with ⟨s1, v2⟩
    rw [e1, e2] at k1 k2
    simp only at k1 k2
    subst k2
    cases v1 with
    | none =>
      simp only
      have hs1 := evalOp_none e2
      refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [k1.status]; simp [writeCells, hs1]
      · rw [hs1]; simp
      · rw [k1.trace]; simp [writeCells]
      · rw [k1.conflicts]; simp [writeCells]
      · rw [k1.tick]; simp [writeCells]
    | some v =>
      simp only
      obtain ⟨hs1, hlv, -⟩ := evalOp_some e2
      have hmo := memOnly_evalOp ms P s o
      rw [e2] at hmo
      have ih := writeInOrder_core ms P loc a n os s1 (ws ++ v) (hs1.trans hs)
        (fun o' ho' => (hok o' (List.mem_cons_of_mem _ ho')).congr hmo.live.symm hmo.alias.symm)
        (by simp only [List.length_append]; omega)
      have hL : LEq (writeInOrder ms P (writeCells x loc (a + ws.length) v) loc
            (a + ws.length + v.length) os)
          (writeInOrder ms P (writeCells s1 loc a (ws ++ v)) loc (a + (ws ++ v).length) os) := by
        rw [List.length_append, ← Nat.add_assoc]
        apply LEq.writeInOrder
        rw [← writeCells_append]
        exact k1.writeCells _ _ _
      rcases e3 : evalOps ms P s1 os with ⟨s2, w⟩
      rw [e3] at ih
      cases w with
      | none => exact RR.leq_left hL ih
      | some w =>
        simp only [List.append_assoc] at ih ⊢
        exact RR.leq_left hL ih

theorem assign_core (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (lhs : Place)
    (rhs : List Operand) (hs : s.status = .running)
    (hc : rhs.length < 2 ∨
      ∀ r, resolvePlace P s lhs = some r → ∀ o ∈ rhs, OpOK P s r.base r.off r.len o) :
    RR (execBasic ⟨ms, .inOrder⟩ P A s (.assign lhs rhs))
      (execBasic ⟨ms, .atomic⟩ P A s (.assign lhs rhs)) := by
  unfold execBasic
  rw [ite_eq_right (fun h => h hs), ite_eq_right (fun h => h hs)]
  simp only
  split
  · exact RR.of_leq (LEq.refl _)
  · rename_i hlen
    cases hr : resolvePlace P s lhs with
    | none => exact RR.of_leq (LEq.refl _)
    | some r =>
      simp only
      rcases hc with hc | hc
      · match rhs, hc with
        | [], _ =>
          simp only [writeInOrder, evalOps]
          exact RR.of_leq (LEq.refl _)
        | [o], _ =>
          simp only [writeInOrder, evalOps]
          rcases evalOp ms P s o with ⟨s1, _ | v⟩
          · exact RR.of_leq (LEq.refl _)
          · simp only [List.append_nil]; exact RR.of_leq (LEq.refl _)
      · have hrl := (Inv.resolvePlace_spec hr).2.2
        have := writeInOrder_core ms P r.base r.off r.len rhs s [] hs (hc r hr)
          (by simp only [List.length_nil, Nat.zero_add]; omega)
        have e0 : writeCells s r.base r.off [] = s := rfl
        simp only [e0, List.length_nil, Nat.add_zero, List.nil_append] at this
        rcases e : evalOps ms P s rhs with ⟨s1, _ | vs⟩ <;> rw [e] at this <;> exact this

/-- Side condition on an assignment under alias `al` that makes in-order and atomic agree. -/
def AsgOK (al : Option (Nat × Place)) : Stmt → Prop
  | .assign lhs rhs => rhs.length < 2 ∨ (al = none ∧ ∀ o ∈ rhs, o.mayOverlap lhs = false) ∨
      (∃ prm T, al = some (prm, T) ∧ ∀ o ∈ rhs, o.mayOverlapParam prm lhs = false)
  | _ => True

theorem resolvePlace_of_alias_none {P : Prog} {s : St} {q r : Place} (ha : s.alias = none)
    (h : resolvePlace P s q = some r) : r = q := by
  unfold resolvePlace at h
  rw [ha] at h
  simp only at h
  split at h
  · cases h; rfl
  · cases h

theorem resolvePlace_of_alias_some {P : Prog} {s : St} {q r : Place} {prm : Nat} {T : Place}
    (ha : s.alias = some (prm, T)) (h : resolvePlace P s q = some r) :
    r = if q.base = prm then ⟨T.base, T.off + q.off, q.len⟩ else q := by
  unfold resolvePlace at h
  rw [ha] at h
  simp only at h
  by_cases hb : q.base = prm
  · rw [ite_eq_left hb]
    rw [ite_eq_left hb] at h
    by_cases hl : q.off + q.len ≤ T.len
    · rw [ite_eq_left hl] at h
      simp only at h
      split at h
      · cases h; rfl
      · cases h
    · rw [ite_eq_right hl] at h; cases h
  · rw [ite_eq_right hb]
    rw [ite_eq_right hb] at h
    simp only at h
    split at h
    · cases h; rfl
    · cases h

theorem opOK_of_none {P : Prog} {s : St} {lhs r : Place} {o : Operand} (ha : s.alias = none)
    (hr : resolvePlace P s lhs = some r) (ho : o.mayOverlap lhs = false) :
    OpOK P s r.base r.off r.len o := by
  have hr' := resolvePlace_of_alias_none ha hr
  subst hr'
  cases o with
  | copy q =>
    intro r' h'
    have := resolvePlace_of_alias_none ha h'
    subst this
    simp only [Operand.mayOverlap, Bool.not_eq_false', decide_eq_true_eq] at ho
    unfold WindowsDisjoint at ho
    unfold CellsDisj; omega
  | move q =>
    intro r' h'
    have := resolvePlace_of_alias_none ha h'
    subst this
    simp only [Operand.mayOverlap, Bool.not_eq_false', decide_eq_true_eq] at ho
    unfold WindowsDisjoint at ho
    unfold CellsDisj; omega
  | lit n => trivial
  | addrOf q => trivial
  | load p l => simp [Operand.mayOverlap] at ho

theorem opOK_of_param {P : Prog} {s : St} {lhs r : Place} {o : Operand} {prm : Nat} {T : Place}
    (ha : s.alias = some (prm, T)) (hr : resolvePlace P s lhs = some r)
    (ho : o.mayOverlapParam prm lhs = false) : OpOK P s r.base r.off r.len o := by
  have hr' := resolvePlace_of_alias_some ha hr
  subst hr'
  have aux : ∀ q, ¬ (decide (WindowsDisjoint lhs q) = false) → Place.paramSplit prm lhs q = false →
      ∀ r', resolvePlace P s q = some r' →
        CellsDisj (if lhs.base = prm then (⟨T.base, T.off + lhs.off, lhs.len⟩ : Place) else lhs).base
          (if lhs.base = prm then (⟨T.base, T.off + lhs.off, lhs.len⟩ : Place) else lhs).off
          (if lhs.base = prm then (⟨T.base, T.off + lhs.off, lhs.len⟩ : Place) else lhs).len r' := by
    intro q hw hp r' h'
    have := resolvePlace_of_alias_some ha h'
    subst this
    simp only [decide_eq_false_iff_not, Classical.not_not] at hw
    simp only [Place.paramSplit, bne_eq_false_iff_eq] at hp
    unfold WindowsDisjoint at hw
    unfold CellsDisj
    by_cases h1 : lhs.base = prm
    · have h2 : q.base = prm := by simpa [h1] using hp
      simp only [h1, h2, ite_true]
      omega
    · have h2 : ¬ q.base = prm := by
        intro h2; apply h1; rw [h2] at hp; simpa using hp
      simp only [h1, h2, ite_false]
      omega
  cases o with
  | copy q =>
    simp only [Operand.mayOverlapParam, Bool.or_eq_false_iff, Bool.not_eq_false'] at ho
    exact aux q (by simp [ho.1]) ho.2
  | move q =>
    simp only [Operand.mayOverlapParam, Bool.or_eq_false_iff, Bool.not_eq_false'] at ho
    exact aux q (by simp [ho.1]) ho.2
  | lit n => trivial
  | addrOf q => trivial
  | load p l => simp [Operand.mayOverlapParam] at ho

theorem execBasic_mode (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : ∀ lhs rhs, st ≠ .assign lhs rhs) :
    execBasic ⟨ms, .inOrder⟩ P A s st = execBasic ⟨ms, .atomic⟩ P A s st := by
  cases st <;> first | rfl | exact absurd rfl (h _ _)

theorem RR.execBasic {s t : St} (h : RR s t) (ms : MoveSem) (P : Prog) (A : Layout) (st : Stmt)
    (hok : AsgOK s.alias st) :
    RR (execBasic ⟨ms, .inOrder⟩ P A s st) (execBasic ⟨ms, .atomic⟩ P A t st) := by
  rcases h with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · cases st with
    | assign lhs rhs =>
      refine RR.leq_right (assign_core ms P A s lhs rhs hs ?_) (h.execBasic _ _ _ _)
      rcases hok with hl | ⟨ha, ho⟩ | ⟨prm, T, ha, ho⟩
      · exact Or.inl hl
      · exact Or.inr fun r hr o hmem => opOK_of_none ha hr (ho o hmem)
      · exact Or.inr fun r hr o hmem => opOK_of_param ha hr (ho o hmem)
    | _ =>
      refine RR.of_leq ?_
      rw [execBasic_mode _ _ _ _ _ (by intro lhs rhs h; cases h)]
      exact h.execBasic _ _ _ _
  · rw [execBasic_of_not_running _ hs, execBasic_of_not_running _ ht]
    exact Or.inr ⟨hs, ht, h3, h4, h5⟩

theorem RR.execCallee {ms : MoveSem} {P : Prog} {A : Layout} (al : Option (Nat × Place))
    (b : List Stmt) (hb : ∀ st ∈ b, AsgOK al st) :
    ∀ {s t : St}, RR s t → s.alias = al →
      RR (execCallee ⟨ms, .inOrder⟩ P A s b) (execCallee ⟨ms, .atomic⟩ P A t b) := by
  induction b with
  | nil => intro s t h _; exact h
  | cons st b ih =>
    intro s t h ha
    simp only [_root_.Toy.Coalesce.execCallee, List.foldl_cons]
    refine ih (fun st' h' => hb st' (List.mem_cons_of_mem _ h'))
      (h.execBasic ms P A st (by rw [ha]; exact hb st (List.mem_cons_self ..))) ?_
    rw [(step_execBasic _ _ _ _ _).alias, ha]

theorem mayOverlap_of_param {prm : Nat} {lhs : Place} {o : Operand}
    (h : o.mayOverlapParam prm lhs = false) : o.mayOverlap lhs = false := by
  cases o <;> simp_all [Operand.mayOverlapParam, Operand.mayOverlap]

theorem asgOK_callee (c : Callee) (hc : calleeNoStaging c = true) (al : Option (Nat × Place))
    (hal : al = none ∨ ∃ T, al = some (c.prm, T)) : ∀ st ∈ c.body, AsgOK al st := by
  intro st hst
  simp only [calleeNoStaging, List.all_eq_true] at hc
  have := hc st hst
  cases st with
  | assign lhs rhs =>
    simp only [NeedsStagingParam, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, List.any_eq_false] at this
    rcases this with h1 | h1
    · exact Or.inl (by omega)
    · rcases hal with rfl | ⟨T, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, fun o ho => mayOverlap_of_param (by simpa using h1 o ho)⟩)
      · exact Or.inr (Or.inr ⟨c.prm, T, rfl, fun o ho => by simpa using h1 o ho⟩)
  | _ => trivial

theorem asgOK_top (sts : List Stmt) (h : stmtsNoStaging sts = true) :
    ∀ st ∈ sts, AsgOK none st := by
  intro st hst
  simp only [stmtsNoStaging, List.all_eq_true] at h
  have := h st hst
  cases st with
  | assign lhs rhs =>
    simp only [NeedsStaging, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, List.any_eq_false] at this
    rcases this with h1 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨rfl, fun o ho => by simpa using h1 o ho⟩)
  | _ => trivial

theorem calleeNoStaging_fn (P : Prog) (hf : ∀ c ∈ P.fns, calleeNoStaging c = true) (fn : Nat) :
    calleeNoStaging (P.fn fn) = true := by
  unfold Prog.fn
  rw [List.getD_eq_getElem?_getD]
  cases h : P.fns[fn]? with
  | none => rfl
  | some c => exact hf c (List.mem_of_getElem? h)

theorem RR.execStmt {s t : St} (h : RR s t) (ms : MoveSem) (P : Prog) (A : Layout) (st : Stmt)
    (ha : s.alias = none) (hok : AsgOK none st) (hf : ∀ c ∈ P.fns, calleeNoStaging c = true) :
    RR (execStmt ⟨ms, .inOrder⟩ P A s st) (execStmt ⟨ms, .atomic⟩ P A t st) := by
  rcases h with ⟨hs, h⟩ | ⟨hs, ht, h3, h4, h5⟩
  · have hts : t.status = .running := h.status ▸ hs
    cases st with
    | call fn arg =>
      have hr : ∀ q, resolvePlace P s q = resolvePlace P t q := resolvePlace_congr h.live h.alias
      have hcf := calleeNoStaging_fn P hf fn
      unfold _root_.Toy.Coalesce.execStmt
      rw [ite_eq_right (fun h' => h' hs), ite_eq_right (fun h' => h' hts)]
      simp only
      split
      · next _ _ q =>
        simp only [hr]
        cases resolvePlace P t q with
        | none => exact RR.of_leq (h.fail _)
        | some r =>
          simp only
          by_cases hc : r.len ≠ P.size (P.fn fn).prm
          · rw [ite_eq_left hc, ite_eq_left hc]; exact RR.of_leq (h.fail _)
          · rw [ite_eq_right hc, ite_eq_right hc]
            refine RR.setCtx (RR.execCallee (some ((P.fn fn).prm, r)) (P.fn fn).body
              (asgOK_callee _ hcf _ (Or.inr ⟨r, rfl⟩)) (RR.of_leq (h.setCtx _ _)) rfl) none false
      · obtain ⟨h1, h2⟩ := h.evalOp ms P arg
        rcases e1 : _root_.Toy.Coalesce.evalOp ms P s arg with ⟨s1, v1⟩
        rcases e2 : _root_.Toy.Coalesce.evalOp ms P t arg with ⟨t1, v2⟩
        rw [e1, e2] at h1 h2
        simp only at h1 h2
        subst h2
        cases v1 with
        | none => exact RR.of_leq h1
        | some vs =>
          simp only [h1.live]
          by_cases hc : vs.length ≠ P.size (P.fn fn).prm ∨ t1.live (P.fn fn).prm = true
          · rw [ite_eq_left hc, ite_eq_left hc]; exact RR.of_leq (h1.fail _)
          · rw [ite_eq_right hc, ite_eq_right hc]
            have hm := memOnly_evalOp ms P s arg
            rw [e1] at hm
            have hal : (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias = none := by
              rw [(step_writeCells _ _ _ _).alias, (step_allocate _ _ _).alias, hm.alias, ha]
            refine RR.deallocate (RR.setInCall (RR.execCallee none (P.fn fn).body
              (asgOK_callee _ hcf _ (Or.inl rfl))
              (RR.of_leq (((h1.allocate _ _).writeCells _ _ _).setInCall true)) hal) false) _ _
    | _ =>
      rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h),
        execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
      exact RR.execBasic (Or.inl ⟨hs, h⟩) ms P A _ (by rw [ha]; exact hok)
  · rw [execStmt_of_not_running _ hs, execStmt_of_not_running _ ht]
    exact Or.inr ⟨hs, ht, h3, h4, h5⟩

theorem rr_runAt (ms : MoveSem) (P : Prog) (A : Layout) (hP : NoStagingNeeded P) :
    ∀ t, RR (runAt ⟨ms, .inOrder⟩ P A t) (runAt ⟨ms, .atomic⟩ P A t) := by
  have hP' := hP
  unfold NoStagingNeeded at hP'
  simp only [Bool.and_eq_true, List.all_eq_true] at hP'
  obtain ⟨hcode, hf⟩ := hP'
  intro t
  induction t with
  | zero => rw [runAt_zero, runAt_zero]; exact RR.of_leq (LEq.refl _)
  | succ t ih =>
    by_cases ht : t < P.code.length
    · rw [runAt_succ _ _ _ _ ht, runAt_succ _ _ _ _ ht]
      have ha := (runAt_frame ⟨ms, .inOrder⟩ P A t (by omega)).2.2.1
      exact (ih.execStmt ms P A P.code[t] ha (asgOK_top _ hcode _ (List.getElem_mem ht)) hf).bumpTick
    · rw [runAt_of_le _ _ _ (t + 1) (by omega), ← runAt_of_le ⟨ms, .inOrder⟩ P A t (by omega),
        runAt_of_le _ _ _ (t + 1) (by omega), ← runAt_of_le ⟨ms, .atomic⟩ P A t (by omega)]
      exact ih

end Stage

namespace Stage

/-! ### Simulation of a program by an extension with extra locals -/

/-- `P'` extends `P`: more locals, same sizes on the locals of `P`, same callees. -/
structure Ext (P P' : Prog) : Prop where
  nloc : P.nloc ≤ P'.nloc
  size : ∀ x, x < P.nloc → P'.size x = P.size x
  fns : P'.fns = P.fns

/-- Agreement of a source state `s` (of `P`) and a target state `t` (of an extension) on the
locals of `P`. -/
structure Agr (P : Prog) (s t : St) : Prop where
  mem : ∀ l, l < P.nloc → t.mem l = s.mem l
  live : ∀ l, l < P.nloc → t.live l = s.live l
  sdead : ∀ l, P.nloc ≤ l → s.live l = false
  alias : t.alias = s.alias
  salias : ∀ prm T, s.alias = some (prm, T) → T.base < P.nloc
  inCall : t.inCall = s.inCall
  status : t.status = s.status
  trace : t.trace = s.trace
  conf : ∀ c ∈ s.conflicts, c ∈ t.conflicts
  sconf : ∀ c ∈ s.conflicts, c.1 < P.nloc ∧ c.2 < P.nloc
  tconf : ∀ c ∈ t.conflicts, c ∈ s.conflicts ∨ (P.nloc ≤ c.1 ∧ c.2 < P.nloc)
  sptr : PtrsIn (· < P.nloc) s

/-- Agreement with every extra local of the target deallocated. -/
def Agree (P : Prog) (s t : St) : Prop := Agr P s t ∧ ∀ l, P.nloc ≤ l → t.live l = false

/-- Candidate place of `q` under alias `al` (before the allocation and bounds check). -/
def cand (al : Option (Nat × Place)) (q : Place) : Option Place :=
  match al with
  | some (prm, t) =>
    if q.base = prm then (if q.off + q.len ≤ t.len then some ⟨t.base, t.off + q.off, q.len⟩ else none)
    else some q
  | none => some q

theorem resolvePlace_eq (P : Prog) (s : St) (q : Place) :
    resolvePlace P s q = match cand s.alias q with
      | some r => if s.live r.base = true ∧ r.off + r.len ≤ P.size r.base then some r else none
      | none => none := rfl

theorem cand_base {al : Option (Nat × Place)} {q r : Place} (h : cand al q = some r) :
    r.base = q.base ∨ ∃ prm T, al = some (prm, T) ∧ r.base = T.base := by
  unfold cand at h
  split at h
  · rename_i prm T
    split at h
    · split at h
      · cases h; exact Or.inr ⟨prm, T, rfl, rfl⟩
      · cases h
    · cases h; exact Or.inl rfl
  · cases h; exact Or.inl rfl

theorem Agr.resolve {P P' : Prog} {s t : St} (hE : Ext P P') (h : Agr P s t) (q : Place)
    (hx : q.base < P.nloc ∨ resolvePlace P s q ≠ none) :
    resolvePlace P' t q = resolvePlace P s q ∧
      ∀ r, resolvePlace P s q = some r → r.base < P.nloc := by
  rw [resolvePlace_eq, resolvePlace_eq, h.alias]
  rw [resolvePlace_eq] at hx
  cases hc : cand s.alias q with
  | none => exact ⟨rfl, fun r hr => by simp at hr⟩
  | some r =>
    simp only
    rw [hc] at hx
    simp only at hx
    have hb : r.base < P.nloc := by
      rcases hx with hx | hx
      · rcases cand_base hc with hb | ⟨prm, T, ha, hb⟩
        · rw [hb]; exact hx
        · rw [hb]; exact h.salias prm T ha
      · by_cases hl : s.live r.base = true
        · exact Nat.lt_of_not_le (fun hn => by rw [h.sdead r.base hn] at hl; cases hl)
        · exfalso; apply hx; rw [ite_eq_right (fun hc => hl hc.1)]
    refine ⟨?_, fun r' hr' => ?_⟩
    · rw [h.live r.base hb, hE.size r.base hb]
    · split at hr'
      · cases hr'; exact hb
      · cases hr'

theorem Agr.fail {P : Prog} {s t : St} (h : Agr P s t) (k : Status) : Agr P (s.fail k) (t.fail k) :=
  { h with status := rfl }

theorem Agr.emit {P : Prog} {s t : St} (h : Agr P s t) (e : Event) : Agr P (s.emit e) (t.emit e) :=
  { h with trace := by simp [St.emit, h.trace] }

theorem agr_readCells {P : Prog} {s t : St} (h : Agr P s t) (loc off n : Nat) (hl : loc < P.nloc) :
    (readCells t loc off n).2 = (readCells s loc off n).2 ∧
      Agr P (readCells s loc off n).1 (readCells t loc off n).1 ∧
      ∀ vs, (readCells s loc off n).2 = some vs → ValsIn (· < P.nloc) vs := by
  obtain ⟨c1, c2⟩ := readCells_congr (s := t) (t := s) (loc := loc) (off := off) (n := n)
    (fun i _ => by rw [h.mem loc hl]) h.status
  refine ⟨c1, ?_, ?_⟩
  · exact { mem := fun l hl' => by simp [h.mem l hl']
            live := fun l hl' => by simp [h.live l hl']
            sdead := fun l hl' => by simp [h.sdead l hl']
            alias := by simp [h.alias]
            salias := fun prm T ha => h.salias prm T (by simpa using ha)
            inCall := by simp [h.inCall]
            status := c2
            trace := by simp [h.trace]
            conf := fun c hc => by simp only [rc_conflicts] at hc ⊢; exact h.conf c hc
            sconf := fun c hc => by simp only [rc_conflicts] at hc; exact h.sconf c hc
            tconf := fun c hc => by simp only [rc_conflicts] at hc ⊢; exact h.tconf c hc
            sptr := Inv.ptrsIn_congr (by simp) h.sptr }
  · intro vs hvs
    rcases e : readCells s loc off n with ⟨s1, v⟩
    rw [e] at hvs
    simp only at hvs
    subst hvs
    rw [(Inv.readCells_eq e).2.2.2 vs rfl]
    exact Inv.valsIn_read h.sptr _ _ _

theorem agr_writeCellsK {P : Prog} {s t : St} (h : Agr P s t) (k : AccKind) (loc off : Nat)
    (vs : List Val) (hv : ValsIn (· < P.nloc) vs) :
    Agr P (writeCellsK k s loc off vs) (writeCellsK k t loc off vs) :=
  { mem := fun l hl' => by simp only [wk_mem, h.mem l hl']
    live := fun l hl' => by simp [h.live l hl']
    sdead := fun l hl' => by simp [h.sdead l hl']
    alias := by simp [h.alias]
    salias := fun prm T ha => h.salias prm T (by simpa using ha)
    inCall := by simp [h.inCall]
    status := by simp [h.status]
    trace := by simp [h.trace]
    conf := fun c hc => by simp only [wk_conflicts] at hc ⊢; exact h.conf c hc
    sconf := fun c hc => by simp only [wk_conflicts] at hc; exact h.sconf c hc
    tconf := fun c hc => by simp only [wk_conflicts] at hc ⊢; exact h.tconf c hc
    sptr := Inv.ptrsIn_writeCellsK _ _ _ _ h.sptr hv }

/-- A target-only write to an extra local. -/
theorem agr_writeCellsK_extra {P : Prog} {s t : St} (h : Agr P s t) (k : AccKind) (loc off : Nat)
    (vs : List Val) (hl : P.nloc ≤ loc) : Agr P s (writeCellsK k t loc off vs) :=
  { h with
    mem := fun l hl' => by
      simp only [wk_mem]
      funext o
      rw [ite_eq_right (by omega)]
      exact congrFun (h.mem l hl') o
    live := fun l hl' => by simp [h.live l hl']
    alias := by simp [h.alias]
    inCall := by simp [h.inCall]
    status := by simp [h.status]
    trace := by simp [h.trace]
    conf := fun c hc => by simp only [wk_conflicts]; exact h.conf c hc
    tconf := fun c hc => by simp only [wk_conflicts] at hc; exact h.tconf c hc }

/-- Target-side log changes are irrelevant. -/
theorem Agr.leq_right {P : Prog} {s t t' : St} (h : Agr P s t) (h2 : LEq t t') : Agr P s t' :=
  { h with
    mem := fun l hl => by rw [← h2.mem]; exact h.mem l hl
    live := fun l hl => by rw [← h2.live]; exact h.live l hl
    alias := by rw [← h2.alias]; exact h.alias
    inCall := by rw [← h2.inCall]; exact h.inCall
    status := by rw [← h2.status]; exact h.status
    trace := by rw [← h2.trace]; exact h.trace
    conf := fun c hc => by rw [← h2.conflicts]; exact h.conf c hc
    tconf := fun c hc => by rw [← h2.conflicts] at hc; exact h.tconf c hc }

theorem Agr.setCtx {P : Prog} {s t : St} (h : Agr P s t) (al : Option (Nat × Place)) (c : Bool)
    (hal : ∀ prm T, al = some (prm, T) → T.base < P.nloc) :
    Agr P { s with alias := al, inCall := c } { t with alias := al, inCall := c } :=
  { h with alias := rfl, salias := hal, inCall := rfl }

theorem Agr.setInCall {P : Prog} {s t : St} (h : Agr P s t) (c : Bool) :
    Agr P { s with inCall := c } { t with inCall := c } :=
  { h with inCall := rfl }

theorem Agr.setTick {P : Prog} {s t : St} (h : Agr P s t) (n m : Nat) :
    Agr P { s with tick := n } { t with tick := m } := { h with }

end Stage

namespace Stage

theorem agr_evalOp {P P' : Prog} {s t : St} (hE : Ext P P') (h : Agr P s t) (ms : MoveSem)
    (o : Operand) (hx : (∀ x ∈ o.locals, x < P.nloc) ∨ (evalOp ms P s o).2 ≠ none) :
    (evalOp ms P' t o).2 = (evalOp ms P s o).2 ∧ Agr P (evalOp ms P s o).1 (evalOp ms P' t o).1 ∧
      (∀ vs, (evalOp ms P s o).2 = some vs → ValsIn (· < P.nloc) vs) ∧
      (∀ l, P.nloc ≤ l → (evalOp ms P' t o).1.mem l = t.mem l) := by
  cases o with
  | lit n =>
    refine ⟨rfl, h, ?_, fun l _ => rfl⟩
    intro vs hvs; simp only [evalOp, Option.some.injEq] at hvs; subst hvs
    intro v hv l' o' hp; simp at hv; subst hv; cases hp
  | addrOf q =>
    have hq : q.base < P.nloc ∨ resolvePlace P s q ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx _ (by simp [Operand.locals]))
      · right; intro hn; apply hx; simp [evalOp, hn]
    obtain ⟨e1, e2⟩ := h.resolve hE q hq
    simp only [evalOp, e1]
    cases hr : resolvePlace P s q with
    | none => exact ⟨rfl, h.fail _, by simp, fun l _ => rfl⟩
    | some r =>
      refine ⟨rfl, h, ?_, fun l _ => rfl⟩
      intro vs hvs; simp only [Option.some.injEq] at hvs; subst hvs
      intro v hv l' o' hp; simp at hv; subst hv; cases hp; exact e2 r hr
  | copy q =>
    have hq : q.base < P.nloc ∨ resolvePlace P s q ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx _ (by simp [Operand.locals]))
      · right; intro hn; apply hx; simp [evalOp, hn]
    obtain ⟨e1, e2⟩ := h.resolve hE q hq
    simp only [evalOp, e1]
    cases hr : resolvePlace P s q with
    | none => exact ⟨rfl, h.fail _, by simp, fun l _ => rfl⟩
    | some r =>
      obtain ⟨a1, a2, a3⟩ := agr_readCells h r.base r.off r.len (e2 r hr)
      exact ⟨a1, a2, a3, fun l _ => by simp⟩
  | move q =>
    have hq : q.base < P.nloc ∨ resolvePlace P s q ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx _ (by simp [Operand.locals]))
      · right; intro hn; apply hx; simp [evalOp, hn]
    obtain ⟨e1, e2⟩ := h.resolve hE q hq
    simp only [evalOp, e1]
    cases hr : resolvePlace P s q with
    | none => exact ⟨rfl, h.fail _, by simp, fun l _ => rfl⟩
    | some r =>
      simp only
      have hb := e2 r hr
      obtain ⟨a1, a2, a3⟩ := agr_readCells h r.base r.off r.len hb
      have fr : ∀ l, (readCells t r.base r.off r.len).1.mem l = t.mem l := fun l => by simp
      rcases c1 : readCells s r.base r.off r.len with ⟨s1, v1⟩
      rcases c2 : readCells t r.base r.off r.len with ⟨t1, v2⟩
      rw [c1, c2] at a1 a2
      rw [c1] at a3
      rw [c2] at fr
      simp only at a1 a2 a3 fr
      subst a1
      cases v2 with
      | none => exact ⟨rfl, a2, by simp, fun l _ => fr l⟩
      | some vs =>
        simp only
        by_cases hms : ms = .deinit
        · rw [ite_eq_left hms, ite_eq_left hms]
          refine ⟨rfl, agr_writeCellsK a2 _ _ _ _ (Inv.valsIn_replicate _), a3,
            fun l hl => ?_⟩
          simp only [writeCells, wk_mem]
          funext o
          rw [ite_eq_right (by omega)]
          exact congrFun (fr l) o
        · rw [ite_eq_right hms, ite_eq_right hms]
          exact ⟨rfl, a2, a3, fun l _ => fr l⟩
  | load p len =>
    have hq : p.base < P.nloc ∨ resolvePlace P s p ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx _ (by simp [Operand.locals]))
      · right; intro hn; apply hx; simp [evalOp, hn]
    obtain ⟨e1, e2⟩ := h.resolve hE p hq
    simp only [evalOp, e1]
    cases hr : resolvePlace P s p with
    | none => exact ⟨rfl, h.fail _, by simp, fun l _ => rfl⟩
    | some r =>
      simp only
      have hb := e2 r hr
      by_cases hl1 : r.len = 1
      · rw [ite_eq_left hl1, ite_eq_left hl1]
        obtain ⟨a1, a2, a3⟩ := agr_readCells h r.base r.off 1 hb
        have fr : ∀ l, (readCells t r.base r.off 1).1.mem l = t.mem l := fun l => by simp
        rcases c1 : readCells s r.base r.off 1 with ⟨s1, v1⟩
        rcases c2 : readCells t r.base r.off 1 with ⟨t1, v2⟩
        rw [c1, c2] at a1 a2
        rw [c1] at a3
        rw [c2] at fr
        simp only at a1 a2 a3 fr
        subst a1
        rcases v2 with _ | ⟨_ | ⟨v, _ | ⟨w, ws⟩⟩⟩
        · exact ⟨rfl, a2, by simp, fun l _ => fr l⟩
        · exact ⟨rfl, a2.fail _, by simp, fun l _ => fr l⟩
        · cases v with
          | ptr l o =>
            simp only
            have hl : l < P.nloc := a3 _ rfl (.ptr l o) (by simp) l o rfl
            rw [a2.live l hl, hE.size l hl]
            by_cases hc : s1.live l = true ∧ o + len ≤ P.size l
            · rw [ite_eq_left hc, ite_eq_left hc]
              obtain ⟨b1, b2, b3⟩ := agr_readCells a2 l o len hl
              exact ⟨b1, b2, b3, fun l' _ => by simp [fr l']⟩
            · rw [ite_eq_right hc, ite_eq_right hc]
              exact ⟨rfl, a2.fail _, by simp, fun l' _ => fr l'⟩
          | _ => exact ⟨rfl, a2.fail _, by simp, fun l _ => fr l⟩
        · cases v <;> exact ⟨rfl, a2.fail _, by simp, fun l _ => fr l⟩
      · rw [ite_eq_right hl1, ite_eq_right hl1]
        exact ⟨rfl, h.fail _, by simp, fun l _ => rfl⟩

theorem agr_evalOps {P P' : Prog} (hE : Ext P P') (ms : MoveSem) (os : List Operand) :
    ∀ {s t : St}, Agr P s t →
    ((∀ o ∈ os, ∀ x ∈ o.locals, x < P.nloc) ∨ (evalOps ms P s os).2 ≠ none) →
    (evalOps ms P' t os).2 = (evalOps ms P s os).2 ∧
      Agr P (evalOps ms P s os).1 (evalOps ms P' t os).1 ∧
      (∀ vs, (evalOps ms P s os).2 = some vs → ValsIn (· < P.nloc) vs) ∧
      (∀ l, P.nloc ≤ l → (evalOps ms P' t os).1.mem l = t.mem l) := by
  induction os with
  | nil => intro s t h _; exact ⟨rfl, h, fun vs hvs => by simp [evalOps] at hvs; subst hvs; simp [ValsIn], fun l _ => rfl⟩
  | cons o os ih =>
    intro s t h hx
    have hxo : (∀ x ∈ o.locals, x < P.nloc) ∨ (evalOp ms P s o).2 ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx o (List.mem_cons_self ..))
      · right; intro hn; apply hx
        simp only [evalOps]
        rcases e : evalOp ms P s o with ⟨s1, _ | v⟩
        · rfl
        · rw [e] at hn; simp at hn
    obtain ⟨a1, a2, a3, a4⟩ := agr_evalOp hE h ms o hxo
    simp only [evalOps]
    rcases c1 : evalOp ms P s o with ⟨s1, v1⟩
    rcases c2 : evalOp ms P' t o with ⟨t1, v2⟩
    rw [c1, c2] at a1 a2
    rw [c1] at a3
    rw [c2] at a4
    simp only at a1 a2 a3 a4
    subst a1
    cases v2 with
    | none => exact ⟨rfl, a2, by simp, a4⟩
    | some v =>
      simp only
      have hx2 : (∀ o ∈ os, ∀ x ∈ o.locals, x < P.nloc) ∨ (evalOps ms P s1 os).2 ≠ none := by
        rcases hx with hx | hx
        · exact Or.inl (fun o' ho' => hx o' (List.mem_cons_of_mem _ ho'))
        · right; intro hn; apply hx
          simp only [evalOps, c1]
          rcases e : evalOps ms P s1 os with ⟨s2, _ | w⟩
          · rfl
          · rw [e] at hn; simp at hn
      obtain ⟨b1, b2, b3, b4⟩ := ih a2 hx2
      rcases c3 : evalOps ms P s1 os with ⟨s2, w1⟩
      rcases c4 : evalOps ms P' t1 os with ⟨t2, w2⟩
      rw [c3, c4] at b1 b2
      rw [c3] at b3
      rw [c4] at b4
      simp only at b1 b2 b3 b4
      subst b1
      cases w2 with
      | none => exact ⟨rfl, b2, by simp, fun l hl => (b4 l hl).trans (a4 l hl)⟩
      | some w =>
        refine ⟨rfl, b2, ?_, fun l hl => (b4 l hl).trans (a4 l hl)⟩
        intro vs hvs
        simp only [Option.some.injEq] at hvs
        subst hvs
        exact Inv.valsIn_append (a3 v rfl) (b3 w rfl)

theorem liveOthers_ext {P P' : Prog} {s t : St} (hE : Ext P P') (h : Agree P s t) (x : Nat) :
    liveOthers P' t x = liveOthers P s x := by
  unfold liveOthers
  obtain ⟨k, hk⟩ : ∃ k, P'.nloc = P.nloc + k := ⟨P'.nloc - P.nloc, by have := hE.nloc; omega⟩
  rw [hk, List.range_add, List.filter_append]
  have h2 : List.filter (fun z => z != x && t.live z) (List.map (fun y => P.nloc + y) (List.range k)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨y, -, rfl⟩ := ha
    simp [h.2 (P.nloc + y) (by omega)]
  rw [h2, List.append_nil]
  apply List.filter_congr
  intro z hz
  rw [h.1.live z (List.mem_range.1 hz)]

theorem mem_liveOthers {P : Prog} {s : St} {x z : Nat} (h : z ∈ liveOthers P s x) :
    z < P.nloc ∧ z ≠ x ∧ s.live z = true := by
  simp only [liveOthers, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem agr_allocate {P P' : Prog} {s t : St} (hE : Ext P P') (h : Agree P s t) (x : Nat)
    (hx : x < P.nloc ∨ (allocate P s x).status = .running) :
    Agree P (allocate P s x) (allocate P' t x) := by
  have hxn : x < P.nloc := by
    rcases hx with hx | hx
    · exact hx
    · unfold allocate at hx
      split at hx
      · assumption
      · rename_i hn
        exfalso
        have : (s.fail .ub).status = .ub := rfl
        rw [this] at hx; cases hx
  have hlo := liveOthers_ext hE h x
  unfold allocate
  rw [ite_eq_left hxn, ite_eq_left (Nat.lt_of_lt_of_le hxn hE.nloc), hlo]
  have hsz := hE.size x hxn
  simp only [resetCells, hsz]
  have hA := h.1
  constructor
  · refine agr_writeCellsK ?_ _ _ _ _ (Inv.valsIn_replicate _)
    exact
      { mem := fun l hl => hA.mem l hl
        live := fun l hl => by simp only; split <;> simp [hA.live l hl]
        sdead := fun l hl => by
          simp only
          rw [ite_eq_right (by omega)]
          exact hA.sdead l hl
        alias := hA.alias
        salias := hA.salias
        inCall := hA.inCall
        status := hA.status
        trace := hA.trace
        conf := fun c hc => by
          simp only [List.mem_append] at hc ⊢
          rcases hc with hc | hc
          · exact Or.inl (hA.conf c hc)
          · exact Or.inr hc
        sconf := fun c hc => by
          simp only [List.mem_append, List.mem_map] at hc
          rcases hc with hc | ⟨z, hz, rfl⟩
          · exact hA.sconf c hc
          · exact ⟨hxn, (mem_liveOthers hz).1⟩
        tconf := fun c hc => by
          simp only [List.mem_append] at hc ⊢
          rcases hc with hc | hc
          · rcases hA.tconf c hc with h' | h'
            · exact Or.inl (Or.inl h')
            · exact Or.inr h'
          · exact Or.inl (Or.inr hc)
        sptr := hA.sptr }
  · intro l hl
    simp only [wk_live]
    rw [ite_eq_right (by omega)]
    exact h.2 l hl

theorem agr_deallocate {P P' : Prog} {s t : St} (hE : Ext P P') (h : Agree P s t) (x : Nat) :
    Agree P (deallocate P s x) (deallocate P' t x) := by
  by_cases hxn : x < P.nloc
  · have hl := h.1.live x hxn
    unfold deallocate
    rw [hl]
    by_cases hlx : s.live x = true
    · rw [ite_eq_left hlx, ite_eq_left hlx]
      have hsz := hE.size x hxn
      simp only [resetCells, hsz]
      have hw := agr_writeCellsK h.1 .reset x 0 (List.replicate (P.size x) .uninit)
        (Inv.valsIn_replicate _)
      constructor
      · exact { hw with
          live := fun l hl' => by simp only [wk_live]; split <;> simp [h.1.live l hl']
          sdead := fun l hl' => by
            simp only [wk_live]
            rw [ite_eq_right (by omega)]
            exact h.1.sdead l hl' }
      · intro l hl'
        simp only [wk_live]
        rw [ite_eq_right (by omega)]
        exact h.2 l hl'
    · rw [ite_eq_right hlx, ite_eq_right hlx]; exact h
  · have h1 : s.live x = false := h.1.sdead x (by omega)
    have h2 : t.live x = false := h.2 x (by omega)
    unfold deallocate
    rw [ite_eq_right (by simp [h1]), ite_eq_right (by simp [h2])]
    exact h

end Stage

namespace Stage

/-! ### Liveness is changed only by storage statements -/

theorem live_cmpOp (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) : (cmpOp ms P A s a b f).live = s.live := by
  unfold cmpOp
  have h1 := (memOnly_evalOp ms P s a).live
  split
  next s1 va heq =>
    rw [heq] at h1
    simp only at h1
    have h2 := (memOnly_evalOp ms P s1 b).live
    split
    next s2 vb heq2 =>
      rw [heq2] at h2; simp only at h2
      split
      · simp only [St.emit]; rw [h2, h1]
      · simp only [St.fail]; rw [h2, h1]
    next s2 _ _ heq2 => rw [heq2] at h2; simp only at h2; simp only [St.fail]; rw [h2, h1]
    next s2 heq2 => rw [heq2] at h2; simp only at h2; rw [h2, h1]
  next s1 _ _ heq => rw [heq] at h1; simp only at h1; simp only [St.fail]; rw [h1]
  next s1 heq => rw [heq] at h1; simp only at h1; rw [h1]

theorem live_execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h1 : ∀ x, st ≠ .storageLive x) (h2 : ∀ x, st ≠ .storageDead x) :
    (execBasic sem P A s st).live = s.live := by
  unfold execBasic
  split
  · rfl
  · cases st with
    | storageLive x => exact absurd rfl (h1 x)
    | storageDead x => exact absurd rfl (h2 x)
    | assign lhs rhs =>
      simp only; split
      · rfl
      · split
        · rfl
        · split
          · have h := (memOnly_evalOps sem.move P s rhs).live
            rcases hr : evalOps sem.move P s rhs with ⟨s', _ | vs⟩
            · rw [hr] at h; exact h
            · rw [hr] at h; simp only [writeCells, wk_live]; exact h
          · exact (memOnly_writeInOrder _ _ _ _ _ _).live
    | store p v =>
      simp only; split
      · rename_i r _
        split
        · have h := (memOnly_readCells s r.base r.off 1).live
          split
          next s1 l o heq =>
            rw [heq] at h
            have h' := (memOnly_evalOp sem.move P s1 v).live
            split
            next s2 vs heq2 =>
              rw [heq2] at h'
              split
              · simp only [writeCells, wk_live]; rw [h', h]
              · simp only [St.fail]; rw [h', h]
            next s2 heq2 => rw [heq2] at h'; simp only at h'; rw [h', h]
          next s1 _ _ heq => rw [heq] at h; exact h
          next s1 heq => rw [heq] at h; exact h
        · rfl
      · rfl
    | ptrEq a b => exact live_cmpOp _ _ _ _ _ _ _
    | ptrInRange a b n => exact live_cmpOp _ _ _ _ _ _ _
    | out o =>
      simp only
      have h := (memOnly_evalOp sem.move P s o).live
      rcases hr : evalOp sem.move P s o with ⟨s', _ | vs⟩
      · rw [hr] at h; exact h
      · rw [hr] at h; exact h
    | call fn a => rfl
    | nop => rfl

/-! ### Simulation of basic statements -/

theorem addr_eq {P : Prog} {A A' : Layout} (hA : ∀ l, l < P.nloc → A l = A' l) (v : Val)
    (hv : ∀ l o, v = .ptr l o → l < P.nloc) : v.addr? A = v.addr? A' := by
  cases v with
  | ptr l o => simp [Val.addr?, hA l (hv l o rfl)]
  | _ => rfl

theorem obs_eq {P : Prog} {A A' : Layout} (hA : ∀ l, l < P.nloc → A l = A' l) (vs : List Val)
    (hv : ValsIn (· < P.nloc) vs) : vs.map (Val.obs A) = vs.map (Val.obs A') := by
  apply List.map_congr_left
  intro v hm
  cases v with
  | ptr l o => simp [Val.obs, hA l (hv _ hm l o rfl)]
  | _ => rfl

theorem agr_cmpOp {P P' : Prog} {A A' : Layout} (hE : Ext P P') (hA : ∀ l, l < P.nloc → A l = A' l)
    {s t : St} (h : Agr P s t) (ms : MoveSem) (a b : Operand) (f : Nat → Nat → Bool)
    (hx : ((∀ x ∈ a.locals, x < P.nloc) ∧ (∀ x ∈ b.locals, x < P.nloc)) ∨
      (cmpOp ms P A s a b f).status = .running) :
    Agr P (cmpOp ms P A s a b f) (cmpOp ms P' A' t a b f) := by
  have hxa : (∀ x ∈ a.locals, x < P.nloc) ∨ (evalOp ms P s a).2 ≠ none := by
    rcases hx with hx | hx
    · exact Or.inl hx.1
    · right; intro hn
      unfold cmpOp at hx
      rcases e : evalOp ms P s a with ⟨s1, v⟩
      rw [e] at hn hx; simp only at hn; subst hn
      simp only at hx; rw [evalOp_none e] at hx; cases hx
  obtain ⟨a1, a2, a3, -⟩ := agr_evalOp hE h ms a hxa
  unfold cmpOp
  unfold cmpOp at hx
  rcases c1 : evalOp ms P s a with ⟨s1, v1⟩
  rcases c2 : evalOp ms P' t a with ⟨t1, v2⟩
  rw [c1, c2] at a1 a2
  rw [c1] at a3 hx
  simp only at a1 a2 a3
  subst a1
  rcases v2 with _ | ⟨_ | ⟨va, _ | ⟨w, ws⟩⟩⟩
  · exact a2
  · exact a2.fail _
  · simp only at hx ⊢
    have hxb : (∀ x ∈ b.locals, x < P.nloc) ∨ (evalOp ms P s1 b).2 ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl hx.2
      · right; intro hn
        rcases e : evalOp ms P s1 b with ⟨s2, v⟩
        rw [e] at hn hx; simp only at hn; subst hn
        simp only at hx; rw [evalOp_none e] at hx; cases hx
    obtain ⟨b1, b2, b3, -⟩ := agr_evalOp hE a2 ms b hxb
    rcases c3 : evalOp ms P s1 b with ⟨s2, w1⟩
    rcases c4 : evalOp ms P' t1 b with ⟨t2, w2⟩
    rw [c3, c4] at b1 b2
    rw [c3] at b3
    simp only at b1 b2 b3
    subst b1
    rcases w2 with _ | ⟨_ | ⟨vb, _ | ⟨w', ws'⟩⟩⟩
    · exact b2
    · exact b2.fail _
    · simp only
      have ea := addr_eq hA va (fun l o hv => a3 _ rfl va (by simp) l o hv)
      have eb := addr_eq hA vb (fun l o hv => b3 _ rfl vb (by simp) l o hv)
      rw [ea, eb]
      rcases (va.addr? A') with _ | x <;> rcases (vb.addr? A') with _ | y <;> simp only <;>
        first
        | exact b2.emit _
        | exact b2.fail _
    · exact b2.fail _
  · exact a2.fail _

theorem not_running_fail (s : St) : (s.fail .ub).status ≠ .running := by simp [St.fail]

/-- Simulation of an atomic non-storage basic statement. -/
theorem agr_execBasic_ns {P P' : Prog} {A A' : Layout} (hE : Ext P P')
    (hA : ∀ l, l < P.nloc → A l = A' l) {s t : St} (h : Agr P s t) (hs : s.status = .running)
    (ms : MoveSem) (st : Stmt) (h1 : ∀ x, st ≠ .storageLive x) (h2 : ∀ x, st ≠ .storageDead x)
    (hx : (∀ x ∈ st.locals P, x < P.nloc) ∨ (execBasic ⟨ms, .atomic⟩ P A s st).status = .running) :
    Agr P (execBasic ⟨ms, .atomic⟩ P A s st) (execBasic ⟨ms, .atomic⟩ P' A' t st) := by
  have ht : t.status = .running := h.status.trans hs
  unfold execBasic
  unfold execBasic at hx
  rw [ite_eq_right (fun h' => h' hs), ite_eq_right (fun h' => h' ht)]
  rw [ite_eq_right (fun h' => h' hs)] at hx
  cases st with
  | storageLive x => exact absurd rfl (h1 x)
  | storageDead x => exact absurd rfl (h2 x)
  | assign lhs rhs =>
    simp only at hx ⊢
    by_cases hlen : (rhs.map Operand.len).sum ≠ lhs.len
    · rw [ite_eq_left hlen, ite_eq_left hlen]; exact h.fail _
    · rw [ite_eq_right hlen, ite_eq_right hlen]
      rw [ite_eq_right hlen] at hx
      have hq : lhs.base < P.nloc ∨ resolvePlace P s lhs ≠ none := by
        rcases hx with hx | hx
        · exact Or.inl (hx _ (by simp [Stmt.locals]))
        · right; intro hn; rw [hn] at hx; exact not_running_fail s hx
      obtain ⟨e1, e2⟩ := h.resolve hE lhs hq
      rw [e1]
      cases hr : resolvePlace P s lhs with
      | none => exact h.fail _
      | some r =>
        rw [hr] at hx
        simp only at hx ⊢
        have hxr : (∀ o ∈ rhs, ∀ x ∈ o.locals, x < P.nloc) ∨ (evalOps ms P s rhs).2 ≠ none := by
          rcases hx with hx | hx
          · exact Or.inl fun o ho x hxo => hx x (by
              simp only [Stmt.locals, List.mem_cons, List.mem_flatMap]
              exact Or.inr ⟨o, ho, hxo⟩)
          · right; intro hn
            rcases e : evalOps ms P s rhs with ⟨s1, v⟩
            rw [e] at hn hx; simp only at hn; subst hn
            simp only at hx; rw [evalOps_none e] at hx; cases hx
        obtain ⟨a1, a2, a3, -⟩ := agr_evalOps hE ms rhs h hxr
        rcases c1 : evalOps ms P s rhs with ⟨s1, v1⟩
        rcases c2 : evalOps ms P' t rhs with ⟨t1, v2⟩
        rw [c1, c2] at a1 a2
        rw [c1] at a3
        simp only at a1 a2 a3
        subst a1
        cases v2 with
        | none => exact a2
        | some vs => exact agr_writeCellsK a2 _ _ _ _ (a3 vs rfl)
  | store p v =>
    simp only at hx ⊢
    have hq : p.base < P.nloc ∨ resolvePlace P s p ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx _ (by simp [Stmt.locals]))
      · right; intro hn; rw [hn] at hx; exact not_running_fail s hx
    obtain ⟨e1, e2⟩ := h.resolve hE p hq
    rw [e1]
    cases hr : resolvePlace P s p with
    | none => exact h.fail _
    | some r =>
      rw [hr] at hx
      simp only at hx ⊢
      have hb := e2 r hr
      by_cases hl1 : r.len = 1
      · rw [ite_eq_left hl1, ite_eq_left hl1]
        rw [ite_eq_left hl1] at hx
        obtain ⟨a1, a2, a3⟩ := agr_readCells h r.base r.off 1 hb
        rcases c1 : readCells s r.base r.off 1 with ⟨s1, v1⟩
        rcases c2 : readCells t r.base r.off 1 with ⟨t1, v2⟩
        rw [c1, c2] at a1 a2
        rw [c1] at a3 hx
        simp only at a1 a2 a3
        subst a1
        rcases v2 with _ | ⟨_ | ⟨w, _ | ⟨w', ws⟩⟩⟩
        · exact a2
        · exact a2.fail _
        · cases w with
          | ptr l o =>
            simp only at hx ⊢
            have hl : l < P.nloc := a3 _ rfl (.ptr l o) (by simp) l o rfl
            have hxv : (∀ x ∈ v.locals, x < P.nloc) ∨ (evalOp ms P s1 v).2 ≠ none := by
              rcases hx with hx | hx
              · exact Or.inl fun x hxo => hx x (by simp [Stmt.locals, hxo])
              · right; intro hn
                rcases e : evalOp ms P s1 v with ⟨s2, v'⟩
                rw [e] at hn hx; simp only at hn; subst hn
                simp only at hx; rw [evalOp_none e] at hx; cases hx
            obtain ⟨b1, b2, b3, -⟩ := agr_evalOp hE a2 ms v hxv
            rcases c3 : evalOp ms P s1 v with ⟨s2, w1⟩
            rcases c4 : evalOp ms P' t1 v with ⟨t2, w2⟩
            rw [c3, c4] at b1 b2
            rw [c3] at b3
            simp only at b1 b2 b3
            subst b1
            cases w2 with
            | none => exact b2
            | some vs =>
              simp only
              rw [b2.live l hl, hE.size l hl]
              by_cases hc : s2.live l = true ∧ o + vs.length ≤ P.size l
              · rw [ite_eq_left hc, ite_eq_left hc]; exact agr_writeCellsK b2 _ _ _ _ (b3 vs rfl)
              · rw [ite_eq_right hc, ite_eq_right hc]; exact b2.fail _
          | _ => exact a2.fail _
        · cases w <;> exact a2.fail _
      · rw [ite_eq_right hl1, ite_eq_right hl1]; exact h.fail _
  | ptrEq a b =>
    refine agr_cmpOp hE hA h ms a b _ ?_
    rcases hx with hx | hx
    · exact Or.inl ⟨fun x hxa => hx x (by simp [Stmt.locals, hxa]),
        fun x hxb => hx x (by simp [Stmt.locals, hxb])⟩
    · exact Or.inr hx
  | ptrInRange a b n =>
    refine agr_cmpOp hE hA h ms a b _ ?_
    rcases hx with hx | hx
    · exact Or.inl ⟨fun x hxa => hx x (by simp [Stmt.locals, hxa]),
        fun x hxb => hx x (by simp [Stmt.locals, hxb])⟩
    · exact Or.inr hx
  | out o =>
    simp only at hx ⊢
    have hxo : (∀ x ∈ o.locals, x < P.nloc) ∨ (evalOp ms P s o).2 ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl fun x hxo => hx x (by simp [Stmt.locals, hxo])
      · right; intro hn
        rcases e : evalOp ms P s o with ⟨s2, v'⟩
        rw [e] at hn hx; simp only at hn; subst hn
        simp only at hx; rw [evalOp_none e] at hx; cases hx
    obtain ⟨a1, a2, a3, -⟩ := agr_evalOp hE h ms o hxo
    rcases c1 : evalOp ms P s o with ⟨s1, v1⟩
    rcases c2 : evalOp ms P' t o with ⟨t1, v2⟩
    rw [c1, c2] at a1 a2
    rw [c1] at a3
    simp only at a1 a2 a3
    subst a1
    cases v2 with
    | none => exact a2
    | some vs =>
      simp only
      rw [obs_eq hA vs (a3 vs rfl)]
      exact a2.emit _
  | call fn a => exact h.fail _
  | nop => exact h

theorem Agree.fail {P : Prog} {s t : St} (h : Agree P s t) (k : Status) :
    Agree P (s.fail k) (t.fail k) := ⟨h.1.fail k, h.2⟩

theorem agr_execBasic {P P' : Prog} {A A' : Layout} (hE : Ext P P')
    (hA : ∀ l, l < P.nloc → A l = A' l) {s t : St} (h : Agree P s t) (ms : MoveSem) (st : Stmt)
    (hx : (∀ x ∈ st.locals P, x < P.nloc) ∨ (execBasic ⟨ms, .atomic⟩ P A s st).status = .running) :
    Agree P (execBasic ⟨ms, .atomic⟩ P A s st) (execBasic ⟨ms, .atomic⟩ P' A' t st) := by
  by_cases hs : s.status = .running
  · have ht : t.status = .running := h.1.status.trans hs
    cases st with
    | storageLive x =>
      unfold execBasic at hx ⊢
      rw [ite_eq_right (fun h' => h' hs), ite_eq_right (fun h' => h' ht)]
      rw [ite_eq_right (fun h' => h' hs)] at hx
      simp only at hx ⊢
      rw [h.1.inCall]
      by_cases hc : s.inCall = true
      · rw [ite_eq_left hc, ite_eq_left hc]; exact h.fail _
      · rw [ite_eq_right hc, ite_eq_right hc]
        rw [ite_eq_right hc] at hx
        refine agr_allocate hE h x ?_
        rcases hx with hx | hx
        · exact Or.inl (hx x (by simp [Stmt.locals]))
        · exact Or.inr hx
    | storageDead x =>
      unfold execBasic
      rw [ite_eq_right (fun h' => h' hs), ite_eq_right (fun h' => h' ht)]
      simp only
      rw [h.1.inCall]
      by_cases hc : s.inCall = true
      · rw [ite_eq_left hc, ite_eq_left hc]; exact h.fail _
      · rw [ite_eq_right hc, ite_eq_right hc]
        exact agr_deallocate hE h x
    | _ =>
      refine ⟨agr_execBasic_ns hE hA h.1 hs ms _ (by intro x h; cases h) (by intro x h; cases h) hx,
        fun l hl => ?_⟩
      rw [live_execBasic _ _ _ _ _ (by intro x h; cases h) (by intro x h; cases h)]
      exact h.2 l hl
  · rw [execBasic_of_not_running _ hs, execBasic_of_not_running _ (by rw [h.1.status]; exact hs)]
    exact h

theorem agr_execCallee {P P' : Prog} {A A' : Layout} (hE : Ext P P')
    (hA : ∀ l, l < P.nloc → A l = A' l) (ms : MoveSem) (b : List Stmt) :
    ∀ {s t : St}, Agree P s t →
      ((∀ st ∈ b, ∀ x ∈ st.locals P, x < P.nloc) ∨
        (execCallee ⟨ms, .atomic⟩ P A s b).status = .running) →
      Agree P (execCallee ⟨ms, .atomic⟩ P A s b) (execCallee ⟨ms, .atomic⟩ P' A' t b) := by
  induction b with
  | nil => intro s t h _; exact h
  | cons st b ih =>
    intro s t h hx
    simp only [_root_.Toy.Coalesce.execCallee, List.foldl_cons] at hx ⊢
    have hx1 : (∀ x ∈ st.locals P, x < P.nloc) ∨
        (execBasic ⟨ms, .atomic⟩ P A s st).status = .running := by
      rcases hx with hx | hx
      · exact Or.inl (hx st (List.mem_cons_self ..))
      · right
        refine Classical.byContradiction fun hn => ?_
        rw [show List.foldl (execBasic ⟨ms, .atomic⟩ P A) (execBasic ⟨ms, .atomic⟩ P A s st) b =
          execCallee ⟨ms, .atomic⟩ P A (execBasic ⟨ms, .atomic⟩ P A s st) b from rfl,
          execCallee_of_not_running _ hn] at hx
        exact hn hx
    refine ih (agr_execBasic hE hA h ms st hx1) ?_
    rcases hx with hx | hx
    · exact Or.inl fun st' h' => hx st' (List.mem_cons_of_mem _ h')
    · exact Or.inr hx

end Stage

namespace Stage

/-! ### Simulation of top-level statements -/

/-- The copy-passing branch of a top-level call. -/
def callCopy (sem : Sem) (P : Prog) (A : Layout) (s : St) (fn : Nat) (arg : Operand) : St :=
  match evalOp sem.move P s arg with
  | (s1, some vs) =>
    if vs.length ≠ P.size (P.fn fn).prm ∨ s1.live (P.fn fn).prm = true then s1.fail .ub else
    deallocate P { execCallee sem P A
      { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
      (P.fn fn).body with inCall := false } (P.fn fn).prm
  | (s1, none) => s1

/-- The in-place branch of a top-level call. -/
def callInPlace (sem : Sem) (P : Prog) (A : Layout) (s : St) (fn : Nat) (q : Place) : St :=
  match resolvePlace P s q with
  | none => s.fail .ub
  | some r =>
    if r.len ≠ P.size (P.fn fn).prm then s.fail .ub else
    { execCallee sem P A { s with alias := some ((P.fn fn).prm, r), inCall := true } (P.fn fn).body
      with alias := none, inCall := false }

theorem execStmt_call_inPlace (m : AssignMode) (P : Prog) (A : Layout) {s : St} (fn : Nat)
    (q : Place) (hs : s.status = .running) :
    execStmt ⟨.inPlaceCall, m⟩ P A s (.call fn (.move q)) = callInPlace ⟨.inPlaceCall, m⟩ P A s fn q := by
  unfold execStmt; rw [ite_eq_right (fun h => h hs)]; rfl

theorem execStmt_call_copy (ms : MoveSem) (m : AssignMode) (P : Prog) (A : Layout) {s : St}
    (fn : Nat) (arg : Operand) (hs : s.status = .running)
    (hc : ∀ q, ms = .inPlaceCall → arg ≠ .move q) :
    execStmt ⟨ms, m⟩ P A s (.call fn arg) = callCopy ⟨ms, m⟩ P A s fn arg := by
  unfold execStmt; rw [ite_eq_right (fun h => h hs)]
  cases ms <;> cases arg <;> first | rfl | exact absurd rfl (hc _ rfl)

theorem fn_ext {P P' : Prog} (hE : Ext P P') (fn : Nat) : P'.fn fn = P.fn fn := by
  simp [Prog.fn, hE.fns]

theorem prm_lt_of_callCopy_running {sem : Sem} {P : Prog} {A : Layout} {s1 : St} {vs : List Val}
    {fn : Nat}
    (h : (if vs.length ≠ P.size (P.fn fn).prm ∨ s1.live (P.fn fn).prm = true then s1.fail .ub else
      deallocate P { execCallee sem P A
        { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
        (P.fn fn).body with inCall := false } (P.fn fn).prm).status = .running) :
    (P.fn fn).prm < P.nloc := by
  split at h
  · exact absurd h (not_running_fail _)
  · refine Classical.byContradiction fun hn => ?_
    have h1 : allocate P s1 (P.fn fn).prm = s1.fail .ub := by unfold allocate; rw [ite_eq_right hn]
    rw [h1, (deallocate_frame _ _ _).1] at h
    simp only at h
    rw [execCallee_of_not_running] at h
    · simp [writeCells, St.fail] at h
    · simp [writeCells, St.fail]

theorem agr_callCopy {P P' : Prog} {A A' : Layout} (hE : Ext P P')
    (hA : ∀ l, l < P.nloc → A l = A' l) {s t : St} (h : Agree P s t) (ms : MoveSem) (fn : Nat)
    (arg : Operand)
    (hx : ((∀ x ∈ arg.locals, x < P.nloc) ∧ (P.fn fn).prm < P.nloc ∧
        ∀ st' ∈ (P.fn fn).body, ∀ x ∈ st'.locals P, x < P.nloc) ∨
      (callCopy ⟨ms, .atomic⟩ P A s fn arg).status = .running) :
    Agree P (callCopy ⟨ms, .atomic⟩ P A s fn arg) (callCopy ⟨ms, .atomic⟩ P' A' t fn arg) := by
  unfold callCopy at hx ⊢
  rw [fn_ext hE fn]
  have hxa : (∀ x ∈ arg.locals, x < P.nloc) ∨ (evalOp ms P s arg).2 ≠ none := by
    rcases hx with hx | hx
    · exact Or.inl hx.1
    · right; intro hn
      rcases e : evalOp ms P s arg with ⟨s1, v⟩
      rw [e] at hn hx; simp only at hn; subst hn
      simp only at hx; rw [evalOp_none e] at hx; cases hx
  obtain ⟨a1, a2, a3, -⟩ := agr_evalOp hE h.1 ms arg hxa
  have hlv : (evalOp ms P' t arg).1.live = t.live := (memOnly_evalOp ms P' t arg).live
  rcases c1 : evalOp ms P s arg with ⟨s1, v1⟩
  rcases c2 : evalOp ms P' t arg with ⟨t1, v2⟩
  rw [c1, c2] at a1 a2
  rw [c1] at a3 hx
  rw [c2] at hlv
  simp only at a1 a2 a3 hlv
  subst a1
  have a2' : Agree P s1 t1 := ⟨a2, fun l hl => by rw [hlv]; exact h.2 l hl⟩
  cases v2 with
  | none => exact a2'
  | some vs =>
    simp only at hx ⊢
    have hprm : (P.fn fn).prm < P.nloc := by
      rcases hx with hx | hx
      · exact hx.2.1
      · exact prm_lt_of_callCopy_running hx
    rw [hE.size _ hprm, a2.live _ hprm]
    by_cases hc : vs.length ≠ P.size (P.fn fn).prm ∨ s1.live (P.fn fn).prm = true
    · rw [ite_eq_left hc, ite_eq_left hc]; exact a2'.fail _
    · rw [ite_eq_right hc, ite_eq_right hc]
      rw [ite_eq_right hc] at hx
      have b1 := agr_allocate hE a2' (P.fn fn).prm (Or.inl hprm)
      have b2 : Agree P (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs)
          (writeCells (allocate P' t1 (P.fn fn).prm) (P.fn fn).prm 0 vs) :=
        ⟨agr_writeCellsK b1.1 _ _ _ _ (a3 vs rfl), fun l hl => by
          simp only [writeCells, wk_live]; exact b1.2 l hl⟩
      have b3 : Agree P { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
          { writeCells (allocate P' t1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true } :=
        ⟨b2.1.setInCall true, b2.2⟩
      have b4 := agr_execCallee hE hA ms (P.fn fn).body b3 (by
        rcases hx with hx | hx
        · exact Or.inl hx.2.2
        · right
          rw [(deallocate_frame _ _ _).1] at hx
          exact hx)
      exact agr_deallocate hE ⟨b4.1.setInCall false, b4.2⟩ _

theorem agr_callInPlace {P P' : Prog} {A A' : Layout} (hE : Ext P P')
    (hA : ∀ l, l < P.nloc → A l = A' l) {s t : St} (h : Agree P s t) (ms : MoveSem) (fn : Nat)
    (q : Place) (hprm : (P.fn fn).prm < P.nloc ∨ (P.fn fn).prm = 0)
    (hx : (q.base < P.nloc ∧ ∀ st' ∈ (P.fn fn).body, ∀ x ∈ st'.locals P, x < P.nloc) ∨
      (callInPlace ⟨ms, .atomic⟩ P A s fn q).status = .running) :
    Agree P (callInPlace ⟨ms, .atomic⟩ P A s fn q) (callInPlace ⟨ms, .atomic⟩ P' A' t fn q) := by
  unfold callInPlace at hx ⊢
  rw [fn_ext hE fn]
  have hq : q.base < P.nloc ∨ resolvePlace P s q ≠ none := by
    rcases hx with hx | hx
    · exact Or.inl hx.1
    · right; intro hn; rw [hn] at hx; exact not_running_fail s hx
  obtain ⟨e1, e2⟩ := h.1.resolve hE q hq
  rw [e1]
  cases hr : resolvePlace P s q with
  | none => exact h.fail _
  | some r =>
    rw [hr] at hx
    simp only at hx ⊢
    have hb := e2 r hr
    have hprm' : (P.fn fn).prm < P.nloc := by
      rcases hprm with hp | hp
      · exact hp
      · omega
    rw [hE.size _ hprm']
    by_cases hc : r.len ≠ P.size (P.fn fn).prm
    · rw [ite_eq_left hc, ite_eq_left hc]; exact h.fail _
    · rw [ite_eq_right hc, ite_eq_right hc]
      rw [ite_eq_right hc] at hx
      have b1 : Agree P { s with alias := some ((P.fn fn).prm, r), inCall := true }
          { t with alias := some ((P.fn fn).prm, r), inCall := true } :=
        ⟨h.1.setCtx _ _ (fun prm T hT => by
          simp only [Option.some.injEq, Prod.mk.injEq] at hT
          obtain ⟨-, rfl⟩ := hT
          exact hb), h.2⟩
      have b2 := agr_execCallee hE hA ms (P.fn fn).body b1 (by
        rcases hx with hx | hx
        · exact Or.inl hx.2
        · exact Or.inr hx)
      exact ⟨b2.1.setCtx none false (by intro _ _ h; cases h), b2.2⟩

theorem agr_execStmt {P P' : Prog} {A A' : Layout} (hE : Ext P P')
    (hA : ∀ l, l < P.nloc → A l = A' l) {s t : St} (h : Agree P s t) (ms : MoveSem) (st : Stmt)
    (hprm : ∀ fn a, st = .call fn a → (P.fn fn).prm < P.nloc ∨ (P.fn fn).prm = 0)
    (hx : ((∀ x ∈ st.locals P, x < P.nloc) ∧
        ∀ fn, ∀ st' ∈ (P.fn fn).body, ∀ x ∈ st'.locals P, x < P.nloc) ∨
      (execStmt ⟨ms, .atomic⟩ P A s st).status = .running) :
    Agree P (execStmt ⟨ms, .atomic⟩ P A s st) (execStmt ⟨ms, .atomic⟩ P' A' t st) := by
  by_cases hs : s.status = .running
  · have ht : t.status = .running := h.1.status.trans hs
    cases st with
    | call fn arg =>
      by_cases hip : ms = .inPlaceCall ∧ ∃ q, arg = .move q
      · obtain ⟨rfl, q, rfl⟩ := hip
        rw [execStmt_call_inPlace _ _ _ _ _ hs, execStmt_call_inPlace _ _ _ _ _ ht]
        rw [execStmt_call_inPlace _ _ _ _ _ hs] at hx
        refine agr_callInPlace hE hA h _ fn q (hprm fn _ rfl) ?_
        rcases hx with hx | hx
        · exact Or.inl ⟨hx.1 _ (by simp [Stmt.locals, Operand.locals]), hx.2 fn⟩
        · exact Or.inr hx
      · have hc : ∀ q, ms = .inPlaceCall → arg ≠ .move q := fun q h1 h2 => hip ⟨h1, q, h2⟩
        rw [execStmt_call_copy _ _ _ _ _ _ hs hc, execStmt_call_copy _ _ _ _ _ _ ht hc]
        rw [execStmt_call_copy _ _ _ _ _ _ hs hc] at hx
        refine agr_callCopy hE hA h ms fn arg ?_
        rcases hx with hx | hx
        · exact Or.inl ⟨fun x hxa => hx.1 x (by simp [Stmt.locals, hxa]),
            hx.1 _ (by simp [Stmt.locals]), hx.2 fn⟩
        · exact Or.inr hx
    | _ =>
      rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h),
        execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
      rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)] at hx
      exact agr_execBasic hE hA h ms _ (hx.imp (fun hx => hx.1) id)
  · rw [execStmt_of_not_running _ hs, execStmt_of_not_running _ (by rw [h.1.status]; exact hs)]
    exact h

end Stage

namespace Stage

/-! ### The staging window -/

def TopRel (Q : Prog) (X : Prop) (s t : St) : Prop :=
  (s.status = .running ∧ Agree Q s t) ∨ (s.status ≠ .running ∧ (X → t.status ≠ .running))

theorem execTop_status (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) :
    (execTop sem P A s st).status = (execStmt sem P A s st).status := rfl

theorem execTop_failed {sem : Sem} {P : Prog} {A : Layout} {s : St} (st : Stmt)
    (h : s.status ≠ .running) : (execTop sem P A s st).status ≠ .running := by
  rw [execTop_status, execStmt_of_not_running _ h]; exact h

theorem foldl_failed (sem : Sem) (P : Prog) (A : Layout) (l : List Stmt) (s : St)
    (h : s.status ≠ .running) : (l.foldl (execTop sem P A) s).status ≠ .running := by
  rw [foldl_execTop_of_not_running l s h]; exact h

theorem exec_storageLive (sem : Sem) (P : Prog) (A : Layout) {s : St} (x : Nat)
    (hs : s.status = .running) (hc : s.inCall = false) :
    execStmt sem P A s (.storageLive x) = allocate P s x := by
  rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
  unfold execBasic; rw [ite_eq_right (fun h => h hs)]; simp [hc]

theorem exec_storageDead (sem : Sem) (P : Prog) (A : Layout) {s : St} (x : Nat)
    (hs : s.status = .running) (hc : s.inCall = false) :
    execStmt sem P A s (.storageDead x) = deallocate P s x := by
  rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
  unfold execBasic; rw [ite_eq_right (fun h => h hs)]; simp [hc]

theorem exec_assign_inOrder (ms : MoveSem) (P : Prog) (A : Layout) {s : St} (lhs : Place)
    (rhs : List Operand) (hs : s.status = .running) :
    execStmt ⟨ms, .inOrder⟩ P A s (.assign lhs rhs) =
      if (rhs.map Operand.len).sum ≠ lhs.len then s.fail .ub else
      match resolvePlace P s lhs with
      | none => s.fail .ub
      | some r => writeInOrder ms P s r.base r.off rhs := by
  rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
  unfold execBasic; rw [ite_eq_right (fun h => h hs)]; rfl

theorem exec_assign_atomic (ms : MoveSem) (P : Prog) (A : Layout) {s : St} (lhs : Place)
    (rhs : List Operand) (hs : s.status = .running) :
    execStmt ⟨ms, .atomic⟩ P A s (.assign lhs rhs) =
      if (rhs.map Operand.len).sum ≠ lhs.len then s.fail .ub else
      match resolvePlace P s lhs with
      | none => s.fail .ub
      | some r =>
        match evalOps ms P s rhs with
        | (s', some vs) => writeCells s' r.base r.off vs
        | (s', none) => s' := by
  rw [execStmt_eq_execBasic _ _ _ _ _ (by intro fn a h; cases h)]
  unfold execBasic; rw [ite_eq_right (fun h => h hs)]; rfl

theorem resolve_tmp {T : Prog} {u : St} {tmp len : Nat} (ha : u.alias = none)
    (hl : u.live tmp = true) (hs : T.size tmp = len) :
    resolvePlace T u ⟨tmp, 0, len⟩ = some ⟨tmp, 0, len⟩ := by
  rw [resolvePlace_eq, ha]; simp [cand, hl, hs]

theorem map_getD_range (v : List Val) : (List.range v.length).map (fun i => v.getD i .uninit) = v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    rw [ih]

theorem readCells_known {u : St} {loc off n : Nat} {vs : List Val}
    (hm : (List.range n).map (fun i => u.mem loc (off + i)) = vs) (hne : ∀ v ∈ vs, v ≠ .uninit) :
    (readCells u loc off n).2 = some vs ∧ (readCells u loc off n).1.status = u.status := by
  obtain ⟨h1, h2, -⟩ := readCells_spec u loc off n
  have hall : ∀ i, i < n → u.mem loc (off + i) ≠ .uninit := fun i hi =>
    hne _ (hm ▸ List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  rw [ite_eq_left hall] at h1 h2
  exact ⟨h1.trans (congrArg some hm), h2⟩

theorem agr_alloc_tmp {Q T : Prog} {s t : St} (h : Agree Q s t) (tmp : Nat)
    (h1 : Q.nloc ≤ tmp) (h2 : tmp < T.nloc) :
    Agr Q s (allocate T t tmp) ∧ (allocate T t tmp).live tmp = true ∧
      (∀ l, Q.nloc ≤ l → l ≠ tmp → (allocate T t tmp).live l = false) ∧
      (allocate T t tmp).status = t.status ∧ (allocate T t tmp).alias = t.alias ∧
      (allocate T t tmp).inCall = t.inCall := by
  unfold allocate
  rw [ite_eq_left h2]
  simp only [resetCells]
  have hA := h.1
  refine ⟨?_, by simp, fun l hl hne => by simp [hne]; exact h.2 l hl, by simp, by simp, by simp⟩
  refine agr_writeCellsK_extra ?_ _ _ _ _ h1
  exact
    { hA with
      live := fun l hl => by simp only; rw [ite_eq_right (by omega)]; exact hA.live l hl
      conf := fun c hc => List.mem_append_left _ (hA.conf c hc)
      tconf := fun c hc => by
        simp only [List.mem_append, List.mem_map] at hc
        rcases hc with hc | ⟨z, hz, rfl⟩
        · exact hA.tconf c hc
        · obtain ⟨hz1, hz2, hz3⟩ := mem_liveOthers hz
          refine Or.inr ⟨h1, Nat.lt_of_not_le fun hn => ?_⟩
          rw [h.2 z hn] at hz3; cases hz3 }

theorem agr_dealloc_tmp {Q T : Prog} {s u : St} (h : Agr Q s u) (tmp : Nat) (h1 : Q.nloc ≤ tmp)
    (hl : u.live tmp = true) (hd : ∀ l, Q.nloc ≤ l → l ≠ tmp → u.live l = false) :
    Agree Q s (deallocate T u tmp) := by
  unfold deallocate
  rw [ite_eq_left hl]
  simp only [resetCells]
  have hw := agr_writeCellsK_extra h .reset tmp 0 (List.replicate (T.size tmp) .uninit) h1
  have hlv : ∀ l, l < Q.nloc →
      (fun z => if z = tmp then false
        else (writeCellsK .reset u tmp 0 (List.replicate (T.size tmp) .uninit)).live z) l = s.live l := by
    intro l hl'
    simp only [wk_live]
    rw [ite_eq_right (by omega)]
    exact h.live l hl'
  refine ⟨{ hw with live := hlv }, fun l hl' => ?_⟩
  simp only [wk_live]
  by_cases he : l = tmp
  · simp [he]
  · rw [ite_eq_right he]; exact hd l hl' he

theorem agr_writeInOrder_tmp {Q T : Prog} (hE : Ext Q T) (ms : MoveSem) (tmp : Nat)
    (htmp : Q.nloc ≤ tmp) (os : List Operand) :
    ∀ (s u : St) (off : Nat), Agr Q s u →
    ((∀ o ∈ os, ∀ x ∈ o.locals, x < Q.nloc) ∨ (evalOps ms Q s os).2 ≠ none) →
    Agr Q (evalOps ms Q s os).1 (writeInOrder ms T u tmp off os) ∧
    (∀ o', o' < off → (writeInOrder ms T u tmp off os).mem tmp o' = u.mem tmp o') ∧
    (∀ vs, (evalOps ms Q s os).2 = some vs →
      (List.range vs.length).map (fun i => (writeInOrder ms T u tmp off os).mem tmp (off + i)) = vs ∧
      ValsIn (· < Q.nloc) vs) := by
  induction os with
  | nil =>
    intro s u off h _
    refine ⟨h, fun _ _ => rfl, fun vs hvs => ?_⟩
    simp only [evalOps, Option.some.injEq] at hvs; subst hvs
    exact ⟨rfl, by simp [ValsIn]⟩
  | cons o os ih =>
    intro s u off h hx
    have hxo : (∀ x ∈ o.locals, x < Q.nloc) ∨ (evalOp ms Q s o).2 ≠ none := by
      rcases hx with hx | hx
      · exact Or.inl (hx o (List.mem_cons_self ..))
      · right; intro hn; apply hx
        simp only [evalOps]
        rcases e : evalOp ms Q s o with ⟨s1, _ | v⟩
        · rfl
        · rw [e] at hn; simp at hn
    obtain ⟨a1, a2, a3, a4⟩ := agr_evalOp hE h ms o hxo
    simp only [evalOps, writeInOrder]
    rcases c1 : evalOp ms Q s o with ⟨s1, v1⟩
    rcases c2 : evalOp ms T u o with ⟨u1, v2⟩
    rw [c1, c2] at a1 a2
    rw [c1] at a3
    rw [c2] at a4
    simp only at a1 a2 a3 a4
    subst a1
    cases v2 with
    | none => exact ⟨a2, fun o' _ => by rw [a4 tmp htmp], by simp⟩
    | some v =>
      simp only
      have hW : Agr Q s1 (writeCells u1 tmp off v) := agr_writeCellsK_extra a2 _ _ _ _ htmp
      have hx2 : (∀ o ∈ os, ∀ x ∈ o.locals, x < Q.nloc) ∨ (evalOps ms Q s1 os).2 ≠ none := by
        rcases hx with hx | hx
        · exact Or.inl (fun o' ho' => hx o' (List.mem_cons_of_mem _ ho'))
        · right; intro hn; apply hx
          simp only [evalOps, c1]
          rcases e : evalOps ms Q s1 os with ⟨s2, _ | w⟩
          · rfl
          · rw [e] at hn; simp at hn
      obtain ⟨b1, b2, b3⟩ := ih s1 (writeCells u1 tmp off v) (off + v.length) hW hx2
      have fr : ∀ o', o' < off →
          (writeInOrder ms T (writeCells u1 tmp off v) tmp (off + v.length) os).mem tmp o' =
            u.mem tmp o' := by
        intro o' ho'
        rw [b2 o' (by omega)]
        simp only [writeCells, wk_mem]
        rw [ite_eq_right (by omega), a4 tmp htmp]
      rcases c3 : evalOps ms Q s1 os with ⟨s2, w1⟩
      rw [c3] at b1 b3
      cases w1 with
      | none => exact ⟨b1, fr, by simp⟩
      | some w =>
        refine ⟨b1, fr, fun vs hvs => ?_⟩
        simp only [Option.some.injEq] at hvs
        subst hvs
        obtain ⟨b4, b5⟩ := b3 w rfl
        refine ⟨?_, Inv.valsIn_append (a3 v rfl) b5⟩
        rw [List.length_append, List.range_add, List.map_append]
        congr 1
        · conv => rhs; rw [← map_getD_range v]
          apply List.map_congr_left
          intro i hi
          have hi' := List.mem_range.1 hi
          rw [b2 (off + i) (by omega)]
          simp only [writeCells, wk_mem]
          rw [ite_eq_left (by first | omega | (simp only [true_and]; omega) | exact ⟨rfl, by omega, by omega⟩)]
          congr 1; omega
        · rw [List.map_map]
          conv => rhs; rw [← b4]
          apply List.map_congr_left
          intro i _
          simp only [Function.comp_def, Nat.add_assoc]

end Stage

namespace Stage

theorem Agr.tick_right {P : Prog} {s t : St} (h : Agr P s t) (n : Nat) :
    Agr P s { t with tick := n } := { h with }

theorem move_tmp_eval {Q T : Prog} (ms : MoveSem) {s' u : St} (h : Agr Q s' u) (tmp : Nat)
    (h1 : Q.nloc ≤ tmp) (len : Nat) (hsz : T.size tmp = len) (ha : u.alias = none)
    (hl : u.live tmp = true) (vs : List Val)
    (hm : (List.range len).map (fun i => u.mem tmp (0 + i)) = vs) (hne : ∀ v ∈ vs, v ≠ .uninit) :
    ∃ y, evalOp ms T u (.move ⟨tmp, 0, len⟩) = (y, some vs) ∧ Agr Q s' y ∧ y.live = u.live ∧
      y.alias = u.alias ∧ y.inCall = u.inCall ∧ y.status = u.status := by
  obtain ⟨k1, k2⟩ := readCells_known hm hne
  have hlq : LEq u (readCells u tmp 0 len).1 :=
    LEq.iff.2 ⟨by simp, by simp, by simp, by simp, by simp, by simp, k2.symm, by simp⟩
  simp only [evalOp, resolve_tmp ha hl hsz]
  rcases e : readCells u tmp 0 len with ⟨y0, v0⟩
  rw [e] at k1 hlq
  simp only at k1 hlq
  subst k1
  simp only
  by_cases hms : ms = .deinit
  · rw [ite_eq_left hms]
    refine ⟨_, rfl, agr_writeCellsK_extra (h.leq_right hlq) _ _ _ _ h1, ?_, ?_, ?_, ?_⟩
    · simp only [writeCells, wk_live]; exact hlq.live.symm
    · simp only [writeCells, wk_alias]; exact hlq.alias.symm
    · simp only [writeCells, wk_inCall]; exact hlq.inCall.symm
    · simp only [writeCells, wk_status]; exact hlq.status.symm
  · rw [ite_eq_right hms]
    exact ⟨_, rfl, h.leq_right hlq, hlq.live.symm, hlq.alias.symm, hlq.inCall.symm,
      hlq.status.symm⟩

theorem window_step {Q T : Prog} {A A' : Layout} (hE : Ext Q T)
    (X : Prop) (ms : MoveSem) (lhs : Place) (rhs : List Operand) (tmp : Nat)
    (h1 : Q.nloc ≤ tmp) (h2 : tmp < T.nloc) (h3 : T.size tmp = lhs.len)
    {s t : St} (hr : TopRel Q X s t) (ha : s.alias = none) (hic : s.inCall = false)
    (hx : X → ∀ x ∈ (Stmt.assign lhs rhs).locals Q, x < Q.nloc) :
    TopRel Q X (execTop ⟨ms, .atomic⟩ Q A s (.assign lhs rhs))
      ([.storageLive tmp, .assign ⟨tmp, 0, lhs.len⟩ rhs, .assign lhs [.move ⟨tmp, 0, lhs.len⟩],
        .storageDead tmp].foldl (execTop ⟨ms, .inOrder⟩ T A') t) := by
  rcases hr with ⟨hs, h⟩ | ⟨hs, hX⟩
  rotate_left
  · exact Or.inr ⟨execTop_failed _ hs, fun hXp => foldl_failed _ _ _ _ _ (hX hXp)⟩
  have ht : t.status = .running := h.1.status.trans hs
  have hta : t.alias = none := h.1.alias.trans ha
  have htc : t.inCall = false := h.1.inCall.trans hic
  simp only [List.foldl_cons, List.foldl_nil]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := agr_alloc_tmp h tmp h1 h2
  obtain ⟨u1, hu1⟩ : ∃ u, u = execTop ⟨ms, .inOrder⟩ T A' t (.storageLive tmp) := ⟨_, rfl⟩
  rw [← hu1]
  have hu1' : u1 = { allocate T t tmp with tick := (allocate T t tmp).tick + 1 } := by
    rw [hu1]; simp only [execTop]; rw [exec_storageLive _ _ _ _ ht htc]
  have b1 : Agr Q s u1 := by rw [hu1']; exact a1.tick_right _
  have b1l : u1.live tmp = true := by rw [hu1']; exact a2
  have b1d : ∀ l, Q.nloc ≤ l → l ≠ tmp → u1.live l = false := by rw [hu1']; exact a3
  have b1s : u1.status = .running := by rw [hu1']; exact a4.trans ht
  have b1a : u1.alias = none := by rw [hu1']; exact a5.trans hta
  have b1c : u1.inCall = false := by rw [hu1']; exact a6.trans htc
  have hsrc : execTop ⟨ms, .atomic⟩ Q A s (.assign lhs rhs) =
      { execStmt ⟨ms, .atomic⟩ Q A s (.assign lhs rhs) with
        tick := (execStmt ⟨ms, .atomic⟩ Q A s (.assign lhs rhs)).tick + 1 } := rfl
  rw [hsrc, exec_assign_atomic _ _ _ _ _ hs]
  obtain ⟨u2, hu2⟩ : ∃ u, u = execTop ⟨ms, .inOrder⟩ T A' u1 (.assign ⟨tmp, 0, lhs.len⟩ rhs) :=
    ⟨_, rfl⟩
  rw [← hu2]
  by_cases hlen : (rhs.map Operand.len).sum ≠ lhs.len
  · rw [ite_eq_left hlen]
    have hu2f : u2 = { u1.fail .ub with tick := (u1.fail .ub).tick + 1 } := by
      rw [hu2]; simp only [execTop]; rw [exec_assign_inOrder _ _ _ _ _ b1s, ite_eq_left hlen]
    refine Or.inr ⟨by simp [St.fail], fun _ => ?_⟩
    apply execTop_failed; apply execTop_failed
    rw [hu2f]; simp [St.fail]
  rw [ite_eq_right hlen]
  have hu2w : u2 = { writeInOrder ms T u1 tmp 0 rhs with
      tick := (writeInOrder ms T u1 tmp 0 rhs).tick + 1 } := by
    rw [hu2]; simp only [execTop]
    rw [exec_assign_inOrder _ _ _ _ _ b1s, ite_eq_right hlen, resolve_tmp b1a b1l h3]
  have wmo := memOnly_writeInOrder ms T u1 tmp 0 rhs
  have hsum : ¬ (([Operand.move ⟨tmp, 0, lhs.len⟩].map Operand.len).sum ≠ lhs.len) := by
    simp [Operand.len]
  -- resolution of `lhs` after evaluating the right side
  have hres2 : ∀ (hq : lhs.base < Q.nloc ∨ resolvePlace Q (evalOps ms Q s rhs).1 lhs ≠ none),
      Agr Q (evalOps ms Q s rhs).1 (writeInOrder ms T u1 tmp 0 rhs) →
      resolvePlace T u2 lhs = resolvePlace Q s lhs := by
    intro hq hW
    rw [hu2w]
    rw [show resolvePlace T { writeInOrder ms T u1 tmp 0 rhs with
        tick := (writeInOrder ms T u1 tmp 0 rhs).tick + 1 } lhs =
        resolvePlace T (writeInOrder ms T u1 tmp 0 rhs) lhs from rfl]
    rw [(hW.resolve hE lhs hq).1]
    have mo := memOnly_evalOps ms Q s rhs
    exact (resolvePlace_congr mo.live mo.alias lhs)
  cases hres : resolvePlace Q s lhs with
  | none =>
    simp only
    refine Or.inr ⟨by simp [St.fail], fun hXp => ?_⟩
    have hxl := hx hXp
    have W := agr_writeInOrder_tmp hE ms tmp h1 rhs s u1 0 b1 (Or.inl fun o ho x hxo =>
      hxl x (by simp only [Stmt.locals, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨o, ho, hxo⟩))
    by_cases hws : (writeInOrder ms T u1 tmp 0 rhs).status = .running
    · apply execTop_failed
      have hu2s : u2.status = .running := by rw [hu2w]; exact hws
      rw [execTop_status, exec_assign_inOrder _ _ _ _ _ hu2s, ite_eq_right hsum,
        hres2 (Or.inl (hxl _ (by simp [Stmt.locals]))) W.1, hres]
      simp [St.fail]
    · apply execTop_failed; apply execTop_failed
      rw [hu2w]; exact hws
  | some r =>
    simp only
    rcases hev : evalOps ms Q s rhs with ⟨s', _ | vs⟩
    · simp only
      have hs' := evalOps_none hev
      refine Or.inr ⟨by simp [hs'], fun hXp => ?_⟩
      have hxl := hx hXp
      have W := agr_writeInOrder_tmp hE ms tmp h1 rhs s u1 0 b1 (Or.inl fun o ho x hxo =>
        hxl x (by simp only [Stmt.locals, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨o, ho, hxo⟩))
      rw [hev] at W
      apply execTop_failed; apply execTop_failed
      rw [hu2w]
      show (writeInOrder ms T u1 tmp 0 rhs).status ≠ .running
      rw [W.1.status, hs']; simp
    · simp only
      obtain ⟨e1, e2, e3⟩ := evalOps_some hev
      have hs'r : s'.status = .running := e1.trans hs
      have hvl : vs.length = lhs.len := by rw [e2]; exact Classical.not_not.1 hlen
      have W := agr_writeInOrder_tmp hE ms tmp h1 rhs s u1 0 b1 (Or.inr (by rw [hev]; simp))
      rw [hev] at W
      obtain ⟨W1, -, W3⟩ := W
      obtain ⟨W3, W4⟩ := W3 vs rfl
      simp only at W1
      have hu2s : u2.status = .running := by rw [hu2w]; exact W1.status.trans hs'r
      have hu2a : u2.alias = none := by rw [hu2w]; exact wmo.alias.trans b1a
      have hu2c : u2.inCall = false := by rw [hu2w]; exact wmo.inCall.trans b1c
      have hu2l : u2.live = u1.live := by rw [hu2w]; exact wmo.live
      have hagr2 : Agr Q s' u2 := by rw [hu2w]; exact W1.tick_right _
      have hm2 : (List.range lhs.len).map (fun i => u2.mem tmp (0 + i)) = vs := by
        rw [← hvl, hu2w]; exact W3
      obtain ⟨y, hy, hyA, hyl, hya, hyc, hys⟩ := move_tmp_eval ms hagr2 tmp h1 lhs.len h3 hu2a
        (by rw [hu2l]; exact b1l) vs hm2 e3
      have hq2 : resolvePlace Q (evalOps ms Q s rhs).1 lhs ≠ none := by
        have mo := memOnly_evalOps ms Q s rhs
        rw [hev] at mo ⊢
        simp only at mo ⊢
        rw [resolvePlace_congr mo.live mo.alias lhs, hres]; simp
      have hr2 : resolvePlace T u2 lhs = some r := by
        rw [hres2 (Or.inr hq2) (by rw [hev]; exact W1), hres]
      obtain ⟨u3, hu3⟩ : ∃ u, u = execTop ⟨ms, .inOrder⟩ T A' u2
          (.assign lhs [.move ⟨tmp, 0, lhs.len⟩]) := ⟨_, rfl⟩
      rw [← hu3]
      have hu3' : u3 = { writeCells y r.base r.off vs with
          tick := (writeCells y r.base r.off vs).tick + 1 } := by
        rw [hu3]; simp only [execTop]
        rw [exec_assign_inOrder _ _ _ _ _ hu2s, ite_eq_right hsum, hr2]
        simp only [writeInOrder, hy]
      have hagr3 : Agr Q (writeCells s' r.base r.off vs) u3 := by
        rw [hu3']; exact (agr_writeCellsK hyA _ _ _ _ W4).tick_right _
      have hu3s : u3.status = .running := by
        rw [hu3']; show (writeCells y r.base r.off vs).status = .running
        simp only [writeCells, wk_status]; rw [hys, hu2s]
      have hu3c : u3.inCall = false := by
        rw [hu3']; show (writeCells y r.base r.off vs).inCall = false
        simp only [writeCells, wk_inCall]; rw [hyc, hu2c]
      have hu3l : u3.live = u1.live := by
        rw [hu3']; show (writeCells y r.base r.off vs).live = u1.live
        simp only [writeCells, wk_live]; rw [hyl, hu2l]
      refine Or.inl ⟨?_, ?_⟩
      · show (writeCells s' r.base r.off vs).status = .running
        simp only [writeCells, wk_status]; exact hs'r
      · simp only [execTop]
        rw [exec_storageDead _ _ _ _ hu3s hu3c]
        have hD := agr_dealloc_tmp (T := T) hagr3 tmp h1 (by rw [hu3l]; exact b1l)
          (fun l hl hne => by rw [hu3l]; exact b1d l hl hne)
        exact ⟨hD.1.setTick _ _, hD.2⟩

end Stage

namespace Stage

/-! ### Top-level simulation of staged code -/

theorem top_step {Q T : Prog} {A A' : Layout} (hE : Ext Q T) (hA : ∀ l, l < Q.nloc → A l = A' l)
    (hcT : ∀ c ∈ T.fns, calleeNoStaging c = true) (X : Prop) (ms : MoveSem) (st : Stmt)
    {s t : St} (hr : TopRel Q X s t) (ha : s.alias = none) (hok : AsgOK none st)
    (hprm : ∀ fn a, st = .call fn a → (Q.fn fn).prm < Q.nloc ∨ (Q.fn fn).prm = 0)
    (hx : X → ((∀ x ∈ st.locals Q, x < Q.nloc) ∧
      ∀ fn, ∀ st' ∈ (Q.fn fn).body, ∀ x ∈ st'.locals Q, x < Q.nloc)) :
    TopRel Q X (execTop ⟨ms, .atomic⟩ Q A s st) (execTop ⟨ms, .inOrder⟩ T A' t st) := by
  rcases hr with ⟨hs, h⟩ | ⟨hs, hX⟩
  rotate_left
  · exact Or.inr ⟨execTop_failed _ hs, fun hXp => execTop_failed _ (hX hXp)⟩
  have hta : t.alias = none := h.1.alias.trans ha
  have hRR := RR.execStmt (RR.of_leq (LEq.refl t)) ms T A' st hta hok hcT
  by_cases hs1 : (execStmt ⟨ms, .atomic⟩ Q A s st).status = .running
  · have hag := agr_execStmt hE hA h ms st hprm (Or.inr hs1)
    have ht1 : (execStmt ⟨ms, .atomic⟩ T A' t st).status = .running := hag.1.status.trans hs1
    rcases hRR with ⟨_, hL⟩ | ⟨_, h2', -⟩
    · refine Or.inl ⟨by rw [execTop_status]; exact hs1, ?_⟩
      refine ⟨(hag.1.leq_right hL.symm).setTick _ _, fun l hl => ?_⟩
      show (execStmt ⟨ms, .inOrder⟩ T A' t st).live l = false
      rw [hL.live]; exact hag.2 l hl
    · exact absurd ht1 h2'
  · refine Or.inr ⟨by rw [execTop_status]; exact hs1, fun hXp => ?_⟩
    have hag := agr_execStmt hE hA h ms st hprm (Or.inl (hx hXp))
    rw [execTop_status, hRR.status, hag.1.status]; exact hs1

theorem asgOK_of_not_needs {lhs : Place} {rhs : List Operand} (h : NeedsStaging lhs rhs = false) :
    AsgOK none (.assign lhs rhs) := by
  simp only [NeedsStaging, Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false] at h
  rcases h with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl ⟨rfl, fun o ho => by simpa using h1 o ho⟩)

theorem execTop_frame (sem : Sem) (P : Prog) (A : Layout) {s : St} (st : Stmt)
    (hc : s.inCall = false) (ha : s.alias = none) :
    (execTop sem P A s st).alias = none ∧ (execTop sem P A s st).inCall = false := by
  have := execStmt_frame sem P A s st hc ha
  exact ⟨this.2.2, this.2.1⟩

theorem sim_list {Q T : Prog} {A A' : Layout} (hE : Ext Q T) (hA : ∀ l, l < Q.nloc → A l = A' l)
    (hcT : ∀ c ∈ T.fns, calleeNoStaging c = true) (X : Prop) (ms : MoveSem)
    (hprmQ : ∀ fn a, Stmt.call fn a ∈ Q.code → (Q.fn fn).prm < Q.nloc ∨ (Q.fn fn).prm = 0)
    (hxQ : X → ∀ st ∈ Q.code, ∀ x ∈ st.locals Q, x < Q.nloc)
    (hxF : X → ∀ fn, ∀ st' ∈ (Q.fn fn).body, ∀ x ∈ st'.locals Q, x < Q.nloc) :
    ∀ (sts : List Stmt) (next : Nat), (∀ st ∈ sts, st ∈ Q.code) → Q.nloc ≤ next →
      (∀ i, i < (stageList next sts).2.length →
        next + i < T.nloc ∧ T.size (next + i) = (stageList next sts).2.getD i 0) →
      ∀ s t, TopRel Q X s t → s.alias = none → s.inCall = false →
        TopRel Q X (sts.foldl (execTop ⟨ms, .atomic⟩ Q A) s)
          ((stageList next sts).1.foldl (execTop ⟨ms, .inOrder⟩ T A') t) := by
  intro sts
  induction sts with
  | nil => intro next _ _ _ s t h _ _; exact h
  | cons st sts ih =>
    intro next hsub hnext hsz s t h ha hic
    have hst : st ∈ Q.code := hsub st (List.mem_cons_self ..)
    have hsub' : ∀ st' ∈ sts, st' ∈ Q.code := fun st' h' => hsub st' (List.mem_cons_of_mem _ h')
    obtain ⟨ha1, hic1⟩ := execTop_frame ⟨ms, .atomic⟩ Q A st hic ha
    have hgen : (∀ lhs rhs, st = .assign lhs rhs → NeedsStaging lhs rhs = false) →
        (stageList next (st :: sts)) = (st :: (stageList next sts).1, (stageList next sts).2) →
        TopRel Q X ((st :: sts).foldl (execTop ⟨ms, .atomic⟩ Q A) s)
          ((stageList next (st :: sts)).1.foldl (execTop ⟨ms, .inOrder⟩ T A') t) := by
      intro hns heq
      rw [heq]
      simp only [List.foldl_cons]
      refine ih next hsub' hnext ?_ _ _ ?_ ha1 hic1
      · intro i hi
        have := hsz i (by rw [heq]; exact hi)
        rw [heq] at this
        exact this
      · refine top_step hE hA hcT X ms st h ha ?_ (fun fn a he => hprmQ fn a (he ▸ hst))
          (fun hXp => ⟨hxQ hXp st hst, hxF hXp⟩)
        cases st with
        | assign lhs rhs => exact asgOK_of_not_needs (hns lhs rhs rfl)
        | _ => trivial
    cases st with
    | assign lhs rhs =>
      by_cases hn : NeedsStaging lhs rhs = true
      · have heq : stageList next (.assign lhs rhs :: sts) =
            ([.storageLive next, .assign ⟨next, 0, lhs.len⟩ rhs,
              .assign lhs [.move ⟨next, 0, lhs.len⟩], .storageDead next] ++
              (stageList (next + 1) sts).1, lhs.len :: (stageList (next + 1) sts).2) := by
          simp only [stageList, hn, ite_true]
        rw [heq]
        simp only [List.foldl_cons, List.foldl_append]
        have h0 := hsz 0 (by rw [heq]; simp)
        rw [heq] at h0
        simp only [Nat.add_zero, List.getD_cons_zero] at h0
        refine ih (next + 1) hsub' (by omega) ?_ _ _ ?_ ha1 hic1
        · intro i hi
          have := hsz (i + 1) (by rw [heq]; simp; omega)
          rw [heq] at this
          simp only [List.getD_cons_succ] at this
          rw [show next + 1 + i = next + (i + 1) by omega]
          exact this
        · exact window_step hE X ms lhs rhs next hnext h0.1 h0.2 h ha hic
            (fun hXp => hxQ hXp _ hst)
      · have hn' : NeedsStaging lhs rhs = false := by simpa using hn
        exact hgen (fun l r he => by cases he; exact hn')
          (by simp only [stageList, hn', Bool.false_eq_true, ite_false])
    | _ => exact hgen (fun l r he => by cases he) (by simp only [stageList])

theorem getD_append_left' (l l' : List Nat) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n 0 = l.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l l' : List Nat) (n : Nat) :
    (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem ext_stage (Q : Prog) : Ext Q (stage Q) where
  nloc := by simp [stage, Prog.nloc]
  size := fun x hx => by
    simp only [stage, Prog.size, List.append_assoc]
    exact getD_append_left' _ _ _ hx
  fns := rfl

theorem agree_init (Q : Prog) : Agree Q St.init St.init :=
  ⟨{ mem := fun _ _ => rfl
     live := fun _ _ => rfl
     sdead := fun _ _ => rfl
     alias := rfl
     salias := fun _ _ h => by cases h
     inCall := rfl
     status := rfl
     trace := rfl
     conf := fun _ h => h
     sconf := fun _ h => by cases h
     tconf := fun _ h => Or.inl h
     sptr := ptrsIn_init _ }, fun _ _ => rfl⟩

theorem sim_run (Q : Prog) {A A' : Layout} (hA : ∀ l, l < Q.nloc → A l = A' l)
    (hc : CalleesNoStaging Q) (X : Prop) (ms : MoveSem)
    (hprmQ : ∀ fn a, Stmt.call fn a ∈ Q.code → (Q.fn fn).prm < Q.nloc ∨ (Q.fn fn).prm = 0)
    (hxQ : X → ∀ st ∈ Q.code, ∀ x ∈ st.locals Q, x < Q.nloc)
    (hxF : X → ∀ fn, ∀ st' ∈ (Q.fn fn).body, ∀ x ∈ st'.locals Q, x < Q.nloc) :
    TopRel Q X (run ⟨ms, .atomic⟩ Q A) (run ⟨ms, .inOrder⟩ (stage Q) A') := by
  have hE := ext_stage Q
  have hcT : ∀ c ∈ (stage Q).fns, calleeNoStaging c = true := by
    unfold CalleesNoStaging at hc
    rw [List.all_eq_true] at hc
    exact hc
  unfold run Prog.code
  simp only [List.foldl_append]
  have hb := sim_list hE hA hcT X ms hprmQ hxQ hxF Q.body Q.nloc
    (fun st h => List.mem_append_left _ h) (Nat.le_refl _) ?_ St.init St.init
    (Or.inl ⟨rfl, agree_init Q⟩) rfl rfl
  · have hfr := runAt_frame ⟨ms, .atomic⟩ Q A Q.body.length (by simp [Prog.code])
    have e1 : runAt ⟨ms, .atomic⟩ Q A Q.body.length = Q.body.foldl (execTop ⟨ms, .atomic⟩ Q A) St.init := by
      simp [runAt, Prog.code]
    rw [e1] at hfr
    refine sim_list hE hA hcT X ms hprmQ hxQ hxF Q.dtors (Q.nloc + (stageList Q.nloc Q.body).2.length)
      (fun st h => List.mem_append_right _ h) (by omega) ?_ _ _ ?_ hfr.2.2.1 hfr.2.1
    · intro i hi
      constructor
      · simp only [stage, Prog.nloc, List.length_append] at hi ⊢; omega
      · simp only [stage, Prog.size]
        rw [show Q.nloc + (stageList Q.nloc Q.body).2.length + i =
          (Q.sizes ++ (stageList Q.nloc Q.body).2).length + i by simp [Prog.nloc]]
        exact getD_append_right' _ _ _
    · exact hb
  · intro i hi
    constructor
    · simp only [stage, Prog.nloc, List.length_append] at hi ⊢; omega
    · simp only [stage, Prog.size, List.append_assoc]
      rw [show Q.nloc + i = Q.sizes.length + i from rfl, getD_append_right']
      exact getD_append_left' _ _ _ hi

end Stage

namespace Stage

/-! ### Assembling the staging statements -/

theorem layoutOK_src {Q : Prog} {A : Layout} {s t : St} (h : Agr Q s t)
    (hl : layoutOK (stage Q) A t.conflicts = true) : layoutOK Q A s.conflicts = true := by
  simp only [layoutOK, List.all_eq_true, decide_eq_true_eq] at hl ⊢
  intro c hc
  have := hl c (h.conf c hc)
  obtain ⟨h1, h2⟩ := h.sconf c hc
  rwa [(ext_stage Q).size _ h1, (ext_stage Q).size _ h2] at this

theorem layoutOK_tgt {Q : Prog} {A : Layout} {s t : St} (h : Agr Q s t)
    (hl : layoutOK Q A s.conflicts = true) (M : Nat) (hM : ∀ z, z < Q.nloc → A z + Q.size z ≤ M) :
    layoutOK (stage Q) (fun l => if l < Q.nloc then A l else M) t.conflicts = true := by
  simp only [layoutOK, List.all_eq_true, decide_eq_true_eq] at hl ⊢
  intro c hc
  rcases h.tconf c hc with hc' | ⟨h1, h2⟩
  · have := hl c hc'
    obtain ⟨a1, a2⟩ := h.sconf c hc'
    rw [(ext_stage Q).size _ a1, (ext_stage Q).size _ a2, ite_eq_left a1, ite_eq_left a2]
    exact this
  · rw [ite_eq_right (by omega), ite_eq_left h2, (ext_stage Q).size _ h2]
    unfold Disj
    exact Or.inr (Or.inr (Or.inr (hM _ h2)))

theorem le_sum_range (f : Nat → Nat) : ∀ n z, z < n → f z ≤ ((List.range n).map f).sum
  | 0, z, h => absurd h (Nat.not_lt_zero _)
  | n + 1, z, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · have := le_sum_range f n z h; omega
    · subst h; omega

theorem prm_of_paramsInRange {Q : Prog} (hp : ParamsInRange Q) :
    ∀ fn a, Stmt.call fn a ∈ Q.code → (Q.fn fn).prm < Q.nloc ∨ (Q.fn fn).prm = 0 := by
  intro fn a _
  unfold ParamsInRange at hp
  rw [List.all_eq_true] at hp
  unfold Prog.fn
  rw [List.getD_eq_getElem?_getD]
  cases h : Q.fns[fn]? with
  | none => right; rfl
  | some c => left; simpa using hp c (List.mem_of_getElem? h)

theorem outcome_ub_of_failed {sem : Sem} {P : Prog} {A : Layout}
    (hb : outcome sem P A ≠ .badLayout) (hs : (run sem P A).status ≠ .running) :
    outcome sem P A = .ub := by
  have hl := layoutOK_of_outcome_ne hb
  unfold outcome
  simp [hl, status_eq_ub_of_ne_running hs]

end Stage

open Stage

/-- For a program in which no assignment needs staging (callee assignments checked against the
in-place binding of the callee's parameter), in-order and atomic assignment give the same outcome
on every layout, under every `move` semantics. -/
theorem outcome_inOrder_eq_atomic_of_noStagingNeeded (ms : MoveSem) (P : Prog)
    (h : NoStagingNeeded P) (A : Layout) :
    outcome ⟨ms, .inOrder⟩ P A = outcome ⟨ms, .atomic⟩ P A := by
  have h := rr_runAt ms P A h P.code.length
  rw [← run_eq_runAt, ← run_eq_runAt] at h
  simp only [outcome, h.conflicts, h.status, h.trace]

/-- Staging under in-order field writes refines the unstaged program under atomic assignment,
provided no callee assignment needs staging and every callee's parameter local exists. -/
theorem stage_inOrder_refines_atomic (ms : MoveSem) (Q : Prog) (hc : CalleesNoStaging Q)
    (hp : ParamsInRange Q) :
    Refines ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := by
  apply refines_of_running
  intro A hA hrun
  have hS := hrun A
  rcases sim_run Q (A := A) (A' := A) (fun _ _ => rfl) hc False ms (prm_of_paramsInRange hp)
    (fun h => h.elim) (fun h => h.elim) with ⟨_, hag⟩ | ⟨hns, _⟩
  · have hlay := layoutOK_of_outcome_ne hA
    have hts : (run ⟨ms, .inOrder⟩ (stage Q) A).status = .running := hag.1.status.trans hS
    rw [outcome_of_running hlay hts]
    refine ⟨A, ?_, by simp⟩
    rw [outcome_of_running (layoutOK_src hag.1 hlay) hS, hag.1.trace]
  · exact absurd hS hns

/-- Behavioural-equivalence form: if no callee assignment needs staging and every local `Q`
mentions exists (so the fresh temporaries are not mentioned by `Q`), the two behaviour sets are
equal. -/
theorem stage_inOrder_behEq_atomic_of_localsInRange (ms : MoveSem) (Q : Prog)
    (hc : CalleesNoStaging Q) (hl : LocalsInRange Q) :
    BehEq ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := by
  have hlr := hl
  unfold LocalsInRange at hlr
  rw [List.all_eq_true] at hlr
  have hxQ : ∀ st ∈ Q.code, ∀ x ∈ st.locals Q, x < Q.nloc := fun st h x hx => by
    have := hlr st (List.mem_append_left _ h)
    rw [List.all_eq_true] at this
    simpa using this x hx
  have hxF : ∀ fn, ∀ st' ∈ (Q.fn fn).body, ∀ x ∈ st'.locals Q, x < Q.nloc := by
    intro fn st' h x hx
    unfold Prog.fn at h
    rw [List.getD_eq_getElem?_getD] at h
    cases hc : Q.fns[fn]? with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.getD_some] at h
      have := hlr st' (List.mem_append_right _ (List.mem_flatMap.2 ⟨c, List.mem_of_getElem? hc, h⟩))
      rw [List.all_eq_true] at this
      simpa using this x hx
  have hprmQ : ∀ fn a, Stmt.call fn a ∈ Q.code → (Q.fn fn).prm < Q.nloc ∨ (Q.fn fn).prm = 0 :=
    fun fn a h => Or.inl (hxQ _ h _ (by simp [Stmt.locals]))
  intro o
  constructor
  · rintro ⟨A, hA, hb⟩
    have hne : outcome ⟨ms, .inOrder⟩ (stage Q) A ≠ .badLayout := hA ▸ hb
    rcases sim_run Q (A := A) (A' := A) (fun _ _ => rfl) hc True ms hprmQ (fun _ => hxQ)
      (fun _ => hxF) with ⟨hS, hag⟩ | ⟨hns, hX⟩
    · have hlay := layoutOK_of_outcome_ne hne
      have hts := hag.1.status.trans hS
      rw [outcome_of_running hlay hts] at hA
      refine ⟨A, ?_, hb⟩
      rw [outcome_of_running (layoutOK_src hag.1 hlay) hS, ← hA, hag.1.trace]
    · rw [outcome_ub_of_failed hne (hX trivial)] at hA
      subst hA
      exact beh_ub_of_status _ _ A (status_eq_ub_of_ne_running hns)
  · rintro ⟨A, hA, hb⟩
    have hne : outcome ⟨ms, .atomic⟩ Q A ≠ .badLayout := hA ▸ hb
    by_cases hS : (run ⟨ms, .atomic⟩ Q A).status = .running
    · have hM := le_sum_range (fun z => A z + Q.size z) Q.nloc
      have hA' : ∀ l, l < Q.nloc →
          A l = (fun l => if l < Q.nloc then A l else
            ((List.range Q.nloc).map (fun z => A z + Q.size z)).sum) l :=
        fun l hl => by simp [hl]
      rcases sim_run Q hA' hc True ms hprmQ (fun _ => hxQ) (fun _ => hxF) with
        ⟨_, hag⟩ | ⟨hns, _⟩
      · have hlayS := layoutOK_of_outcome_ne hne
        rw [outcome_of_running hlayS hS] at hA
        have hts := hag.1.status.trans hS
        refine ⟨fun l => if l < Q.nloc then A l else
          ((List.range Q.nloc).map (fun z => A z + Q.size z)).sum, ?_, hb⟩
        rw [outcome_of_running (layoutOK_tgt hag.1 hlayS _ hM) hts, hag.1.trace, ← hA]
      · exact absurd hS hns
    · rcases sim_run Q (A := A) (A' := A) (fun _ _ => rfl) hc True ms hprmQ (fun _ => hxQ)
        (fun _ => hxF) with ⟨hS', _⟩ | ⟨_, hX⟩
      · exact absurd hS' hS
      · rw [outcome_ub_of_failed hne hS] at hA
        subst hA
        exact beh_ub_of_status _ _ A (status_eq_ub_of_ne_running (hX trivial))

end Toy.Coalesce
