import ToyCoalesce.PfObs
import ToyCoalesce.PfInPlace

/-!
# Proof: certificate-licensed upgrades
-/

namespace Toy.Coalesce.Lic

open Toy.Coalesce

/-! ## Log bookkeeping -/

/-- Every log entry of `t` is an entry of `s` or satisfies `Q`. -/
def LogOK (s t : St) (Q : Access → Prop) : Prop := ∀ e ∈ t.log, e ∈ s.log ∨ Q e

theorem LogOK.refl (s : St) (Q : Access → Prop) : LogOK s s Q := fun _ he => Or.inl he

theorem LogOK.trans {s t w : St} {Q : Access → Prop} (h1 : LogOK s t Q) (h2 : LogOK t w Q) :
    LogOK s w Q := by
  intro e he
  rcases h2 e he with h | h
  · exact h1 e h
  · exact Or.inr h

theorem LogOK.trans' {s t t' w : St} {Q : Access → Prop} (h1 : LogOK s t Q) (h2 : LogOK t' w Q)
    (ht : t'.log = t.log) : LogOK s w Q := by
  intro e he
  rcases h2 e he with h | h
  · exact h1 e (ht ▸ h)
  · exact Or.inr h

theorem LogOK.mono {s t : St} {Q Q' : Access → Prop} (h : LogOK s t Q) (hQ : ∀ e, Q e → Q' e) :
    LogOK s t Q' := fun e he => (h e he).imp id (hQ e)

theorem logOK_of_step {s t : St} (h : Step s t) : LogOK s t (fun e => e.inCall = s.inCall) := by
  obtain ⟨d, hd, hdi⟩ := h.log
  intro e he
  rw [hd] at he
  rcases List.mem_append.1 he with he | he
  · exact Or.inl he
  · exact Or.inr (hdi e he).2

theorem readCells_log (s : St) (loc off n : Nat) :
    LogOK s (readCells s loc off n).1 (fun e => e.loc = loc ∧ e.kind = .read) := by
  obtain ⟨_, _, m, _, hl, _⟩ := readCells_spec s loc off n
  intro e he
  rw [hl] at he
  rcases List.mem_append.1 he with he | he
  · exact Or.inl he
  · right
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨i, _, rfl⟩ := he
    exact ⟨rfl, rfl⟩

theorem writeCellsK_log (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    LogOK s (writeCellsK k s loc off vs) (fun e => e.loc = loc ∧ e.kind = k) := by
  intro e he
  rw [writeCellsK_eq] at he
  rcases List.mem_append.1 he with he | he
  · exact Or.inl he
  · right
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨i, _, rfl⟩ := he
    exact ⟨rfl, rfl⟩

theorem resolvePlace_none {P : Prog} {s : St} {q r : Place} (ha : s.alias = none)
    (h : resolvePlace P s q = some r) : r = q := by
  unfold resolvePlace at h
  rw [ha] at h
  simp only at h
  split at h
  · cases h; rfl
  · cases h


theorem readCells_log' {s s' : St} {loc off n : Nat} {r : Option (List Val)}
    (he : readCells s loc off n = (s', r)) :
    LogOK s s' (fun e => e.loc = loc ∧ e.kind = .read) := by
  have h := readCells_log s loc off n
  rw [he] at h
  exact h

theorem logOK_fail (s : St) (k : Status) (Q : Access → Prop) : LogOK s (s.fail k) Q :=
  fun _ he => Or.inl he

theorem logOK_emit (s : St) (ev : Event) (Q : Access → Prop) : LogOK s (s.emit ev) Q :=
  fun _ he => Or.inl he

/-! ## Which cells of a local `u` an operation may touch -/

/-- A logged access of local `u` by an operation that evaluates the operands `ops` is a read
justified by a by-name read in `ops`, by a `load` in `ops` when `u ∈ S`, or by `R`; or it is a
non-read justified by a `deinit` move from `u` in `ops` or by `W`. -/
def EOK (ms : MoveSem) (S : Nat → Prop) (u : Nat) (ops : List Operand) (R W : Prop)
    (e : Access) : Prop :=
  e.loc = u →
    (e.kind = .read ∧ (ops.any (Operand.readsName u) = true ∨
      (S u ∧ ops.any Operand.isLoad = true) ∨ R)) ∨
    (e.kind ≠ .read ∧ ((ms = .deinit ∧ ops.any (Operand.readsName u) = true) ∨ W))

theorem EOK.mono {ms : MoveSem} {S : Nat → Prop} {u : Nat} {ops ops' : List Operand}
    {R R' W W' : Prop} {e : Access} (h : EOK ms S u ops R W e) (hops : ∀ o ∈ ops, o ∈ ops')
    (hR : R → R') (hW : W → W') : EOK ms S u ops' R' W' e := by
  intro hu
  have hany : ∀ f : Operand → Bool, ops.any f = true → ops'.any f = true := by
    intro f hf
    obtain ⟨o, ho, hfo⟩ := List.any_eq_true.1 hf
    exact List.any_eq_true.2 ⟨o, hops o ho, hfo⟩
  rcases h hu with ⟨hk, h1 | ⟨h2, h3⟩ | h4⟩ | ⟨hk, ⟨h5, h6⟩ | h7⟩
  · exact Or.inl ⟨hk, Or.inl (hany _ h1)⟩
  · exact Or.inl ⟨hk, Or.inr (Or.inl ⟨h2, hany _ h3⟩)⟩
  · exact Or.inl ⟨hk, Or.inr (Or.inr (hR h4))⟩
  · exact Or.inr ⟨hk, Or.inl ⟨h5, hany _ h6⟩⟩
  · exact Or.inr ⟨hk, Or.inr (hW h7)⟩

theorem evalOp_log {ms : MoveSem} {P : Prog} {S : Nat → Prop} {u : Nat} {s s' : St}
    {o : Operand} {r : Option (List Val)} (he : evalOp ms P s o = (s', r))
    (ha : s.alias = none) (hp : PtrsIn S s) :
    LogOK s s' (EOK ms S u [o] False False) := by
  cases o with
  | lit n =>
    simp only [evalOp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact LogOK.refl _ _
  | addrOf q =>
    simp only [evalOp] at he
    split at he
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact LogOK.refl _ _
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact logOK_fail _ _ _
  | copy q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      have := resolvePlace_none ha hr0; subst this
      refine (readCells_log' he).mono ?_
      rintro e ⟨hl, hk⟩ hu
      left
      refine ⟨hk, Or.inl ?_⟩
      simp [Operand.readsName, ← hl, hu]
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact logOK_fail _ _ _
  | move q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      have := resolvePlace_none ha hr0; subst this
      split at he
      · rename_i s1 vs1 hrd
        have h1 : LogOK s s1 (EOK ms S u [.move r0] False False) := by
          refine (readCells_log' hrd).mono ?_
          rintro e ⟨hl, hk⟩ hu
          left
          refine ⟨hk, Or.inl ?_⟩
          simp [Operand.readsName, ← hl, hu]
        split at he
        · rename_i hd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine h1.trans ((writeCellsK_log _ _ _ _ _).mono ?_)
          rintro e ⟨hl, hk⟩ hu
          right
          refine ⟨by rw [hk]; decide, Or.inl ⟨hd, ?_⟩⟩
          simp [Operand.readsName, ← hl, hu]
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact h1
      · rename_i s1 hrd
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine (readCells_log' hrd).mono ?_
        rintro e ⟨hl, hk⟩ hu
        left
        refine ⟨hk, Or.inl ?_⟩
        simp [Operand.readsName, ← hl, hu]
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact logOK_fail _ _ _
  | load p len =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      have := resolvePlace_none ha hr0; subst this
      have hread : ∀ {s1 : St} {x : Option (List Val)}, readCells s r0.base r0.off 1 = (s1, x) →
          LogOK s s1 (EOK ms S u [.load r0 len] False False) := by
        intro s1 x hrd
        refine (readCells_log' hrd).mono ?_
        rintro e ⟨hl, hk⟩ hu
        left
        refine ⟨hk, Or.inl ?_⟩
        simp [Operand.readsName, ← hl, hu]
      split at he
      · split at he
        · rename_i s1 l o hrd
          have h1 := hread hrd
          obtain ⟨hm, -, -, hv⟩ := Inv.readCells_eq hrd
          have hl : S l := by
            have := hv _ rfl
            simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
              List.cons.injEq, and_true] at this
            exact hp _ _ _ _ this.symm
          split at he
          · refine h1.trans ((readCells_log' he).mono ?_)
            rintro e ⟨hl', hk⟩ hu
            left
            refine ⟨hk, Or.inr (Or.inl ⟨?_, by simp [Operand.isLoad]⟩)⟩
            rw [← hu, hl']; exact hl
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact h1.trans (logOK_fail _ _ _)
        · rename_i s1 x _ hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact (hread hrd).trans (logOK_fail _ _ _)
        · rename_i s1 hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hread hrd
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact logOK_fail _ _ _
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact logOK_fail _ _ _


theorem EOK.cons {ms : MoveSem} {S : Nat → Prop} {u : Nat} {o : Operand} {os : List Operand}
    {R W : Prop} {e : Access} (h : EOK ms S u [o] False False e) :
    EOK ms S u (o :: os) R W e :=
  h.mono (fun _ ho' => by simp at ho'; simp [ho']) False.elim False.elim

theorem EOK.tail {ms : MoveSem} {S : Nat → Prop} {u : Nat} {o : Operand} {os : List Operand}
    {R W : Prop} {e : Access} (h : EOK ms S u os R W e) :
    EOK ms S u (o :: os) R W e :=
  h.mono (fun _ ho' => List.mem_cons_of_mem _ ho') id id

theorem evalOps_log {ms : MoveSem} {P : Prog} {S : Nat → Prop} {u : Nat} (os : List Operand) :
    ∀ {s s' : St} {r : Option (List Val)}, evalOps ms P s os = (s', r) → s.alias = none →
    PtrsIn S s → (∀ o ∈ os, ∀ x, o.takesAddr x = true → S x) →
    LogOK s s' (EOK ms S u os False False) := by
  induction os with
  | nil =>
    intro s s' r he _ _ _
    simp only [evalOps, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact LogOK.refl _ _
  | cons o os ih =>
    intro s s' r he ha hp hos
    simp only [evalOps] at he
    split at he
    · rename_i s1 vs1 he1
      have hl1 := (evalOp_log (S := S) (u := u) he1 ha hp).mono
        (fun e h => h.cons (os := os) (R := False) (W := False))
      have hal := Inv.evalOp_alias he1
      have hp1 := (Inv.ptrsIn_evalOp he1 hp (fun x hx => by
        rw [ha]; exact hos o (List.mem_cons_self ..) x hx)).1
      have ih' : ∀ {s2 : St} {r2 : Option (List Val)}, evalOps ms P s1 os = (s2, r2) →
          LogOK s s2 (EOK ms S u (o :: os) False False) := by
        intro s2 r2 he2
        exact hl1.trans ((ih he2 (hal.trans ha) hp1
          (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))).mono (fun e h => h.tail))
      split at he
      · rename_i s2 ws he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ih' he2
      · rename_i s2 he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ih' he2
    · rename_i s1 he1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact (evalOp_log (S := S) (u := u) he1 ha hp).mono (fun e h => h.cons)

theorem writeInOrder_log {ms : MoveSem} {P : Prog} {S : Nat → Prop} {u : Nat} (loc : Nat)
    (os : List Operand) : ∀ (s : St) (off : Nat), s.alias = none → PtrsIn S s →
    (∀ o ∈ os, ∀ x, o.takesAddr x = true → S x) →
    LogOK s (writeInOrder ms P s loc off os) (EOK ms S u os False (loc = u)) := by
  induction os with
  | nil => intro s off _ _ _; exact LogOK.refl _ _
  | cons o os ih =>
    intro s off ha hp hos
    simp only [writeInOrder]
    have hos' : ∀ x, o.takesAddr x = true → S (aliasBase s.alias x) := fun x hx => by
      rw [ha]; exact hos o (List.mem_cons_self ..) x hx
    split
    · rename_i s1 vs he
      have hl1 := (evalOp_log (S := S) (u := u) he ha hp).mono
        (fun e h => h.cons (os := os) (R := False) (W := loc = u))
      obtain ⟨hp1, hv⟩ := Inv.ptrsIn_evalOp he hp hos'
      have hal : (writeCells s1 loc off vs).alias = s.alias :=
        (step_writeCells s1 loc off vs).alias.trans (Inv.evalOp_alias he)
      have hw : LogOK s1 (writeCells s1 loc off vs) (EOK ms S u (o :: os) False (loc = u)) := by
        refine (writeCellsK_log _ _ _ _ _).mono ?_
        rintro e ⟨hl, hk⟩ hu
        right
        exact ⟨by rw [hk]; decide, Or.inr (hl ▸ hu)⟩
      refine (hl1.trans hw).trans ((ih _ _ (hal.trans ha)
        (Inv.ptrsIn_writeCellsK _ _ _ _ hp1 (hv vs rfl))
        (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))).mono (fun e h => h.tail))
    · rename_i s1 he
      exact (evalOp_log (S := S) (u := u) he ha hp).mono (fun e h => h.cons)

theorem cmpOp_log {ms : MoveSem} {P : Prog} {A : Layout} {S : Nat → Prop} {u : Nat} (s : St)
    (a b : Operand) (f : Nat → Nat → Bool) (ha : s.alias = none) (hp : PtrsIn S s)
    (hta : ∀ x, a.takesAddr x = true → S x) :
    LogOK s (cmpOp ms P A s a b f) (EOK ms S u [a, b] False False) := by
  have hA : ∀ {s1 : St} {r1 : Option (List Val)}, evalOp ms P s a = (s1, r1) →
      LogOK s s1 (EOK ms S u [a, b] False False) := fun he1 =>
    (evalOp_log (S := S) (u := u) he1 ha hp).mono (fun e h => h.cons)
  have hB : ∀ {s1 s2 : St} {r1 r2 : Option (List Val)}, evalOp ms P s a = (s1, r1) →
      evalOp ms P s1 b = (s2, r2) → LogOK s s2 (EOK ms S u [a, b] False False) := by
    intro s1 s2 r1 r2 he1 he2
    have hal := Inv.evalOp_alias he1
    have hp1 := (Inv.ptrsIn_evalOp he1 hp (fun x hx => by rw [ha]; exact hta x hx)).1
    exact (hA he1).trans ((evalOp_log (S := S) (u := u) he2 (hal.trans ha) hp1).mono
      (fun e h => h.mono (by simp) id id))
  unfold cmpOp
  split
  · rename_i s1 va he1
    split
    · rename_i s2 vb he2
      split
      · exact (hB he1 he2).trans (logOK_emit _ _ _)
      · exact (hB he1 he2).trans (logOK_fail _ _ _)
    · rename_i s2 _ _ he2; exact (hB he1 he2).trans (logOK_fail _ _ _)
    · rename_i s2 he2; exact hB he1 he2
  · rename_i s1 _ _ he1; exact (hA he1).trans (logOK_fail _ _ _)
  · rename_i s1 he1; exact hA he1


/-- `st` is a `store` whose pointer cell is based at `u`. -/
def RS (u : Nat) (st : Stmt) : Prop := ∃ p v, st = .store p v ∧ p.base = u

/-- `st` assigns a place based at `u`, or `st` is a `store` and `u ∈ S`. -/
def WS (S : Nat → Prop) (u : Nat) (st : Stmt) : Prop :=
  (∃ lhs rhs, st = .assign lhs rhs ∧ lhs.base = u) ∨ (S u ∧ ∃ p v, st = .store p v)

/-- Accesses of `u` by a statement run inside a callee without an alias, when every pointer in
memory has provenance in `S`. -/
theorem execBasic_log (sem : Sem) (P : Prog) (A : Layout) (S : Nat → Prop) (u : Nat) (s : St)
    (st : Stmt) (ha : s.alias = none) (hc : s.inCall = true) (hp : PtrsIn S s)
    (ht : ∀ x, st.takesAddr x = true → S x) :
    LogOK s (execBasic sem P A s st) (EOK sem.move S u st.operands (RS u st) (WS S u st)) := by
  unfold execBasic
  split
  · exact LogOK.refl _ _
  · cases st with
    | storageLive x => exact logOK_fail _ _ _
    | storageDead x => exact logOK_fail _ _ _
    | assign lhs rhs =>
      have hos : ∀ o ∈ rhs, ∀ x, o.takesAddr x = true → S x :=
        fun o ho x hx => ht x (List.any_eq_true.mpr ⟨o, ho, hx⟩)
      simp only
      split
      · exact logOK_fail _ _ _
      · split
        · exact logOK_fail _ _ _
        · rename_i r0 hr0
          have := resolvePlace_none ha hr0; subst this
          split
          · split
            · rename_i s' vs he
              refine ((evalOps_log (S := S) (u := u) rhs he ha hp hos).mono
                (fun e h => h.mono (fun _ h => h) False.elim False.elim)).trans
                ((writeCellsK_log _ _ _ _ _).mono ?_)
              rintro e ⟨hl, hk⟩ hu
              right
              exact ⟨by rw [hk]; decide, Or.inr (Or.inl ⟨r0, rhs, rfl, hl ▸ hu⟩)⟩
            · rename_i s' he
              exact (evalOps_log (S := S) (u := u) rhs he ha hp hos).mono
                (fun e h => h.mono (fun _ h => h) False.elim False.elim)
          · exact (writeInOrder_log (S := S) (u := u) _ rhs s _ ha hp hos).mono
              (fun e h => h.mono (fun _ h => h) False.elim (fun h => Or.inl ⟨r0, rhs, rfl, h⟩))
    | store p v =>
      simp only
      split
      · rename_i r0 hr0
        have := resolvePlace_none ha hr0; subst this
        have hread : ∀ {s1 : St} {x : Option (List Val)}, readCells s r0.base r0.off 1 = (s1, x) →
            LogOK s s1 (EOK sem.move S u (Stmt.store r0 v).operands (RS u (.store r0 v))
              (WS S u (.store r0 v))) := by
          intro s1 x hrd
          refine (readCells_log' hrd).mono ?_
          rintro e ⟨hl, hk⟩ hu
          left
          exact ⟨hk, Or.inr (Or.inr ⟨r0, v, rfl, hl ▸ hu⟩)⟩
        split
        · split
          · rename_i s1 l o he1
            have hl1 := hread he1
            obtain ⟨hm, -, hal1, hv⟩ := Inv.readCells_eq he1
            have hS : S l := by
              have := hv _ rfl
              simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
                List.cons.injEq, and_true] at this
              exact hp _ _ _ _ this.symm
            have hp1 : PtrsIn S s1 := Inv.ptrsIn_congr hm hp
            have hv2 : ∀ {s2 : St} {r2 : Option (List Val)}, evalOp sem.move P s1 v = (s2, r2) →
                LogOK s s2 (EOK sem.move S u (Stmt.store r0 v).operands (RS u (.store r0 v))
                  (WS S u (.store r0 v))) := by
              intro s2 r2 he2
              exact hl1.trans ((evalOp_log (S := S) (u := u) he2 (hal1.trans ha) hp1).mono
                (fun e h => h.mono (fun _ h => h) False.elim False.elim))
            split
            · rename_i s2 vs he2
              split
              · refine (hv2 he2).trans ((writeCellsK_log _ _ _ _ _).mono ?_)
                rintro e ⟨hl, hk⟩ hu
                right
                refine ⟨by rw [hk]; decide, Or.inr (Or.inr ⟨?_, r0, v, rfl⟩)⟩
                rw [← hu, hl]; exact hS
              · exact (hv2 he2).trans (logOK_fail _ _ _)
            · rename_i s2 he2
              exact hv2 he2
          · rename_i s1 _ _ he1
            exact (hread he1).trans (logOK_fail _ _ _)
          · rename_i s1 he1
            exact hread he1
        · exact logOK_fail _ _ _
      · exact logOK_fail _ _ _
    | ptrEq a b =>
      exact (cmpOp_log (S := S) (u := u) s a b _ ha hp
        (fun x hx => ht x (by simp [Stmt.takesAddr, hx]))).mono
        (fun e h => h.mono (fun _ h => h) False.elim False.elim)
    | ptrInRange a b n =>
      exact (cmpOp_log (S := S) (u := u) s a b _ ha hp
        (fun x hx => ht x (by simp [Stmt.takesAddr, hx]))).mono
        (fun e h => h.mono (fun _ h => h) False.elim False.elim)
    | out o =>
      simp only
      split
      · rename_i s' vs he
        exact ((evalOp_log (S := S) (u := u) he ha hp).mono
          (fun e h => h.mono (fun _ h => h) False.elim False.elim)).trans (logOK_emit _ _ _)
      · rename_i s' he
        exact (evalOp_log (S := S) (u := u) he ha hp).mono
          (fun e h => h.mono (fun _ h => h) False.elim False.elim)
    | call fn a => exact logOK_fail _ _ _
    | nop => exact LogOK.refl _ _


/-- Accesses of `u` by a callee body run without an alias. -/
theorem execCallee_log (sem : Sem) (P : Prog) (A : Layout) (S : Nat → Prop) (u : Nat)
    (b : List Stmt) : ∀ s : St, s.alias = none → s.inCall = true → PtrsIn S s →
    (∀ st ∈ b, ∀ x, st.takesAddr x = true → S x) →
    LogOK s (execCallee sem P A s b)
      (fun e => ∃ st ∈ b, EOK sem.move S u st.operands (RS u st) (WS S u st) e) := by
  induction b with
  | nil => intro s _ _ _ _; exact LogOK.refl _ _
  | cons st b ih =>
    intro s ha hc hp hb
    have h1 := execBasic_log sem P A S u s st ha hc hp (hb st (List.mem_cons_self ..))
    have hst := step_execBasic sem P A s st
    have hp1 := ptrsIn_execBasic S sem P A s st hp
      (fun x hx => by rw [ha]; exact hb st (List.mem_cons_self ..) x hx)
    have h2 := ih _ (hst.alias.trans ha) (hst.inCall.trans hc) hp1
      (fun st' h' => hb st' (List.mem_cons_of_mem _ h'))
    show LogOK s (execCallee sem P A (execBasic sem P A s st) b) _
    exact (h1.mono (fun e h => ⟨st, List.mem_cons_self .., h⟩)).trans
      (h2.mono (fun e ⟨st', h', h⟩ => ⟨st', List.mem_cons_of_mem _ h', h⟩))

theorem logOK_step_false {s t : St} {Q : Access → Prop} (h : Step s t) (hc : s.inCall = false) :
    LogOK s t (fun e => e.inCall = false ∨ Q e) :=
  (logOK_of_step h).mono (fun _ he => Or.inl (he.trans hc))

/-- Accesses of `u` by a top-level call passing its argument by copy: every new entry is made
outside the callee or is justified by a statement of the callee body. -/
theorem callCopy_log (sem : Sem) (P : Prog) (A : Layout) (S : Nat → Prop) (u : Nat) (s : St)
    (fn : Nat) (q : Place) (ha : s.alias = none) (hc : s.inCall = false) (hp : PtrsIn S s)
    (hb : ∀ st ∈ (P.fn fn).body, ∀ x, st.takesAddr x = true → S x) :
    LogOK s (execStmt sem P A s (.call fn (.copy q)))
      (fun e => e.inCall = false ∨
        ∃ st ∈ (P.fn fn).body, EOK sem.move S u st.operands (RS u st) (WS S u st) e) := by
  unfold execStmt
  split
  · exact LogOK.refl _ _
  · simp only
    split
    · rename_i h; cases h
    · split
      · rename_i s1 vs he
        have hs1 := step_evalOp sem.move P s (.copy q)
        rw [he] at hs1
        have hl1 : LogOK s s1 (fun e => e.inCall = false ∨
            ∃ st ∈ (P.fn fn).body, EOK sem.move S u st.operands (RS u st) (WS S u st) e) :=
          logOK_step_false hs1 hc
        split
        · exact hl1.trans (logOK_fail _ _ _)
        · obtain ⟨hp1, hv⟩ := Inv.ptrsIn_evalOp (S := S) he hp (fun x hx => by
            simp [Operand.takesAddr] at hx)
          have hs2 := (step_allocate P s1 (P.fn fn).prm).trans
            (step_writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs)
          have hc1 : s1.inCall = false := hs1.inCall.trans hc
          have hp3 := Inv.ptrsIn_writeCellsK (s := allocate P s1 (P.fn fn).prm) .write
            (P.fn fn).prm 0 vs (Inv.ptrsIn_allocate P s1 _ hp1) (hv vs rfl)
          have hl3 := execCallee_log sem P A S u (P.fn fn).body
            { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
            (hs2.alias.trans (hs1.alias.trans ha)) rfl hp3 hb
          have hs4 := step_deallocate P { execCallee sem P A
            { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
            (P.fn fn).body with inCall := false } (P.fn fn).prm
          exact (((hl1.trans (logOK_step_false hs2 hc1)).trans'
            (hl3.mono (fun e h => Or.inr h)) rfl).trans' (logOK_step_false hs4 rfl) rfl)
      · rename_i s1 he
        have hs1 := step_evalOp sem.move P s (.copy q)
        rw [he] at hs1
        exact logOK_step_false hs1 hc

theorem tick_entries (sem : Sem) (P : Prog) (A : Layout) (k : Nat) (hk : k < P.code.length)
    (Q : Access → Prop)
    (h : LogOK (runAt sem P A k) (execStmt sem P A (runAt sem P A k) P.code[k])
      (fun e => e.inCall = false ∨ Q e)) :
    ∀ e ∈ (run sem P A).log, e.tick = k → e.inCall = true → Q e := by
  intro e he het hec
  obtain ⟨d, hd, _, hd2⟩ := run_log_split sem P A (k + 1) (by omega)
  rw [hd] at he
  rcases List.mem_append.1 he with he | he
  · rw [runAt_succ sem P A k hk] at he
    rcases h e he with h1 | h1 | h1
    · have := (runAt_frame sem P A k (by omega)).2.2.2 e h1; omega
    · rw [hec] at h1; cases h1
    · exact h1
  · have := hd2 e he; omega

theorem code_get {P : Prog} {k : Nat} {st : Stmt} (h : P.body[k]? = some st) :
    ∃ hk : k < P.code.length, P.code[k] = st := by
  have hk : k < P.body.length := by
    rcases Nat.lt_or_ge k P.body.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  refine ⟨by simp [Prog.code]; omega, ?_⟩
  simp only [Prog.code]
  rw [List.getElem_append_left hk]
  rw [List.getElem?_eq_getElem hk] at h
  exact Option.some.inj h

theorem execStmt_noncall (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : ∀ fn a, st ≠ .call fn a) : execStmt sem P A s st = execBasic sem P A s st := by
  unfold execStmt
  split
  · rename_i hs; rw [execBasic_of_not_running st hs]
  · cases st with
    | call fn a => exact absurd rfl (h fn a)
    | _ => rfl

theorem firstTouch_true_of_false (k loc off : Nat) (L : List Access)
    (hL : ∀ e ∈ L, e.tick = k → e.inCall = true → e.loc = loc → e.off = off → e.kind ≠ .read)
    (h : firstTouchNotRead (afterUse false k) loc off L = true) :
    firstTouchNotRead (afterUse true k) loc off L = true := by
  induction L with
  | nil => rfl
  | cons e es ih =>
    have ih' := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
    simp only [firstTouchNotRead] at h ⊢
    by_cases hlt : k < e.tick
    · have h0 : afterUse false k e = true := by simp [afterUse, hlt]
      have h1 : afterUse true k e = true := by simp [afterUse, hlt]
      rw [h0] at h; rw [h1]
      split
      · rename_i hc; rw [ite_eq_left hc] at h; exact h
      · rename_i hc; rw [ite_eq_right hc] at h; exact ih' h
    · have h0 : afterUse false k e = false := by simp [afterUse, hlt]
      rw [h0] at h
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
      split
      · rename_i hc
        have hc' : e.tick = k ∧ e.inCall = true ∧ e.loc = loc ∧ e.off = off := by
          simp [afterUse, hlt] at hc; grind
        simpa using hL e (List.mem_cons_self ..) hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2
      · exact ih' h


/-- Under in-place passing, a licensed callee statement does not access `q.base`. -/
theorem eok_inPlace {P : Prog} {O : ObsMask} {k fn : Nat} {q : Place}
    (hlic : Licensed .inPlaceCall P O k q) (hfn : P.body[k]? = some (.call fn (.copy q)))
    {st : Stmt} (hst : st ∈ (P.fn fn).body) {e : Access}
    (h : EOK .inPlaceCall (AddrTaken P) q.base st.operands (RS q.base st)
      (WS (AddrTaken P) q.base st) e) : e.loc ≠ q.base := by
  obtain ⟨-, hnm, hld, -⟩ := hlic fn hfn
  have h1 := List.any_eq_false.1 hnm st hst
  intro hu
  rcases h hu with ⟨_, h3 | ⟨hS, hl⟩ | ⟨p, v, rfl, hp⟩⟩ | ⟨_, ⟨hd, _⟩ | ⟨lhs, rhs, rfl, hl⟩ | ⟨hS, p, v, rfl⟩⟩
  · simp [h3] at h1
  · rw [decide_eq_true hS, Bool.true_and] at hld
    have h2 := List.any_eq_false.1 hld st hst
    simp [hl] at h2
  · simp [hp] at h1
  · cases hd
  · simp [hl] at h1
  · rw [decide_eq_true hS, Bool.true_and] at hld
    have h2 := List.any_eq_false.1 hld _ hst
    simp at h2

/-- Under `deinit`, a licensed callee statement does not read `q.base`. -/
theorem eok_deinit {P : Prog} {O : ObsMask} {k fn : Nat} {q : Place}
    (hlic : Licensed .deinit P O k q) (hfn : P.body[k]? = some (.call fn (.copy q)))
    {st : Stmt} (hst : st ∈ (P.fn fn).body) {e : Access}
    (h : EOK .deinit (AddrTaken P) q.base st.operands (RS q.base st)
      (WS (AddrTaken P) q.base st) e) : e.loc = q.base → e.kind ≠ .read := by
  have h1 := List.any_eq_false.1 (hlic.2 fn hfn) st hst
  unfold Stmt.mayReadNoCall at h1
  intro hu
  rcases h hu with ⟨_, h3 | ⟨hS, hl⟩ | ⟨p, v, rfl, hp⟩⟩ | ⟨hk, _⟩
  · simp [h3] at h1
  · simp [hS, hl] at h1
  · simp [hp] at h1
  · exact hk

end Toy.Coalesce.Lic

namespace Toy.Coalesce

open Toy.Coalesce.Lic

/-- Upgrades licensed by a certificate are refinements, under each `move` semantics and either
assignment order. -/
theorem upgrade_refines_of_obsCert_licensed (sem : Sem) (P : Prog) (O : ObsMask) (k : Nat)
    (q : Place) (hsite : UpgradeSite P k q) (hcert : ObsCert P O)
    (hlic : Licensed sem.move P O k q) :
    Refines sem (P.upgradeAt k) sem P := by
  obtain ⟨ms, am⟩ := sem
  cases ms with
  | asCopy => exact refines_of_outcome_eq (fun A => upgrade_outcome_eq_moveAsCopy am P k A)
  | inPlaceCall =>
    by_cases hcall : ∃ fn, P.body[k]? = some (.call fn (.copy q))
    · obtain ⟨fn, hfn⟩ := hcall
      have hcs : CallSite P k fn q := by
        refine ⟨hfn, ?_⟩
        rcases hsite with ⟨lhs, h, _⟩ | ⟨fn', h, hprm⟩ | h
        · rw [hfn] at h; cases h
        · rw [hfn] at h; cases h; exact hprm
        · rw [hfn] at h; cases h
      obtain ⟨hO, -, -, hprm⟩ := hlic fn hfn
      apply upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_paramNotAddrTaken
        am P k fn q hcs
      · intro A _ _
        exact noReadBeforeReinit_of_obsCert _ P O hcert k q hO A
      · intro A _ _
        have hclaim : ∀ e ∈ (run ⟨.inPlaceCall, am⟩ P A).log, e.tick = k → e.inCall = true →
            e.loc ≠ q.base := by
          obtain ⟨hk, hck⟩ := code_get hfn
          apply tick_entries _ P A k hk
          rw [hck]
          obtain ⟨-, h2, h3, -⟩ := runAt_frame ⟨.inPlaceCall, am⟩ P A k (by omega)
          refine (callCopy_log _ P A (AddrTaken P) q.base _ fn q h3 h2
            (ptrsIn_runAt _ _ P A (addrDisc_addrTaken P) k)
            ((addrDisc_addrTaken P).2.1 fn)).mono ?_
          rintro e (h | ⟨st, hst, h⟩)
          · exact Or.inl h
          · exact Or.inr (eok_inPlace hlic hfn hst h)
        unfold CalleeAvoids
        rw [List.all_eq_true]
        intro e he
        by_cases ht : e.tick = k
        · by_cases hc : e.inCall = true
          · have := hclaim e he ht hc
            simp [this]
          · simp [hc]
        · simp [ht]
      · exact hprm
    · refine refines_of_outcome_eq (fun A => upgrade_outcome_eq_moveInPlaceCall_of_not_call am P k
        ?_ A)
      intro fn a h
      rcases hsite with ⟨lhs, h', _⟩ | ⟨fn', h', _⟩ | h'
      · rw [h] at h'; cases h'
      · exact hcall ⟨fn', h'⟩
      · rw [h] at h'; cases h'
  | deinit =>
    have hO : O (k + 1) q.base = false := hlic.1
    apply upgrade_moveDeinit_refines_of_noReadBeforeReinit am P k q hsite
    intro A _ _ j hj
    have hclaim : ∀ e ∈ (run ⟨.deinit, am⟩ P A).log, e.tick = k → e.inCall = true →
        e.loc = q.base → e.kind ≠ .read := by
      obtain ⟨st, hst⟩ : ∃ st, P.body[k]? = some st := by
        rcases hsite with ⟨_, h, _⟩ | ⟨_, h, _⟩ | h <;> exact ⟨_, h⟩
      obtain ⟨hk, hck⟩ := code_get hst
      apply tick_entries _ P A k hk
      rw [hck]
      obtain ⟨-, h2, h3, -⟩ := runAt_frame ⟨.deinit, am⟩ P A k (by omega)
      rcases hsite with ⟨lhs, h, _⟩ | ⟨fn, h, _⟩ | h
      · rw [hst] at h; cases h
        rw [execStmt_noncall _ _ _ _ _ (by intro fn a h; cases h)]
        exact logOK_step_false (step_execBasic _ P A _ _) h2
      · rw [hst] at h; cases h
        refine (callCopy_log _ P A (AddrTaken P) q.base _ fn q h3 h2
          (ptrsIn_runAt _ _ P A (addrDisc_addrTaken P) k)
          ((addrDisc_addrTaken P).2.1 fn)).mono ?_
        rintro e (h | ⟨st, hst', h⟩)
        · exact Or.inl h
        · exact Or.inr (eok_deinit hlic hst hst' h)
      · rw [hst] at h; cases h
        rw [execStmt_noncall _ _ _ _ _ (by intro fn a h; cases h)]
        exact logOK_step_false (step_execBasic _ P A _ _) h2
    exact firstTouch_true_of_false k q.base (q.off + j) _
      (fun e he het hec hel _ => hclaim e he het hec hel)
      (noReadBeforeReinit_of_obsCert _ P O hcert k q hO A j hj)

end Toy.Coalesce
