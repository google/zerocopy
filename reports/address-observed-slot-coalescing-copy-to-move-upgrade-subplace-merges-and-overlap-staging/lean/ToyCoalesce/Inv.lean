import ToyCoalesce.Infra

/-!
# Run invariants (proof infrastructure)

* `LiveInv`: an initialized cell belongs to an allocated local and lies within its size.
* `PtrsIn S`: every pointer value in memory has provenance in `S`; for `S = AddrTaken P` this holds
  in every run of `P` (`run_ptrsIn_addrTaken`).
-/

namespace Toy.Coalesce

/-! ## Allocation invariant -/

/-- Every initialized cell belongs to an allocated local and lies within its size. -/
def LiveInv (P : Prog) (s : St) : Prop :=
  ∀ l o, s.mem l o ≠ .uninit → s.live l = true ∧ o < P.size l

theorem liveInv_init (P : Prog) : LiveInv P St.init := by
  intro l o h; exact absurd rfl h

/-! ### Helper lemmas for the allocation invariant -/

namespace Inv

theorem readCells_eq {s s' : St} {loc off n : Nat} {r : Option (List Val)}
    (h : readCells s loc off n = (s', r)) :
    s'.mem = s.mem ∧ s'.live = s.live ∧ s'.alias = s.alias ∧
      (∀ vs, r = some vs → vs = (List.range n).map fun i => s.mem loc (off + i)) := by
  have hf := readCells_frame s loc off n
  have hs := (readCells_spec s loc off n).1
  rw [h] at hf hs
  have h1 := congrArg St.mem hf
  have h2 := congrArg St.live hf
  have h3 := congrArg St.alias hf
  refine ⟨h1, h2, h3, ?_⟩
  intro vs hvs
  subst hvs
  split at hs
  · exact (Option.some.inj hs)
  · cases hs

theorem readCells_len {s s' : St} {loc off n : Nat} {vs : List Val}
    (h : readCells s loc off n = (s', some vs)) : vs.length = n := by
  rw [(readCells_eq h).2.2.2 vs rfl]; simp

theorem resolvePlace_spec {P : Prog} {s : St} {q r : Place} (h : resolvePlace P s q = some r) :
    s.live r.base = true ∧ r.off + r.len ≤ P.size r.base ∧ r.len = q.len := by
  unfold resolvePlace at h
  split at h
  · rename_i prm t hal
    by_cases hb : q.base = prm
    · simp only [hb, ↓reduceIte] at h
      by_cases hl : q.off + q.len ≤ t.len
      · simp only [hl, ↓reduceIte] at h
        split at h
        · rename_i hc; cases h; exact ⟨hc.1, hc.2, rfl⟩
        · cases h
      · simp only [hl, ↓reduceIte] at h
        cases h
    · simp only [hb, ↓reduceIte] at h
      split at h
      · rename_i hc; cases h; exact ⟨hc.1, hc.2, rfl⟩
      · cases h
  · simp only at h
    split at h
    · rename_i hc; cases h; exact ⟨hc.1, hc.2, rfl⟩
    · cases h

theorem liveInv_congr {P : Prog} {s t : St} (hm : t.mem = s.mem)
    (hl : ∀ l, s.live l = true → t.live l = true) (h : LiveInv P s) : LiveInv P t := by
  intro l o ho
  rw [hm] at ho
  obtain ⟨h1, h2⟩ := h l o ho
  exact ⟨hl l h1, h2⟩

theorem liveInv_of_eq {P : Prog} {s t : St} (hm : t.mem = s.mem) (hl : t.live = s.live)
    (h : LiveInv P s) : LiveInv P t :=
  liveInv_congr hm (fun l hl' => by rw [hl]; exact hl') h

theorem liveInv_writeCellsK {P : Prog} {s : St} (k : AccKind) (loc off : Nat) (vs : List Val)
    (h : LiveInv P s)
    (hw : ∀ i, i < vs.length → vs.getD i .uninit ≠ .uninit → s.live loc = true ∧ off + i < P.size loc) :
    LiveInv P (writeCellsK k s loc off vs) := by
  rw [writeCellsK_eq]
  intro l o ho
  simp only at ho ⊢
  split at ho
  · rename_i hc
    obtain ⟨rfl, h1, h2⟩ := hc
    obtain ⟨h3, h4⟩ := hw (o - off) (by omega) ho
    exact ⟨h3, by omega⟩
  · exact h l o ho

theorem liveInv_writeCells {P : Prog} {s : St} (loc off : Nat) (vs : List Val)
    (h : LiveInv P s) (hl : s.live loc = true) (hb : off + vs.length ≤ P.size loc) :
    LiveInv P (writeCells s loc off vs) :=
  liveInv_writeCellsK _ _ _ _ h fun i hi _ => ⟨hl, by omega⟩

theorem getD_replicate_uninit (n i : Nat) : (List.replicate n Val.uninit).getD i .uninit = .uninit := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem liveInv_writeUninit {P : Prog} {s : St} (k : AccKind) (loc off n : Nat)
    (h : LiveInv P s) : LiveInv P (writeCellsK k s loc off (List.replicate n .uninit)) :=
  liveInv_writeCellsK _ _ _ _ h fun i _ hi => absurd (getD_replicate_uninit n i) hi

theorem writeCellsK_live (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).live = s.live := by
  rw [writeCellsK_eq]

theorem liveInv_evalOp {ms : MoveSem} {P : Prog} {s s' : St} {o : Operand} {r : Option (List Val)}
    (he : evalOp ms P s o = (s', r)) (h : LiveInv P s) :
    LiveInv P s' ∧ s'.live = s.live ∧ (∀ vs, r = some vs → vs.length = o.len) := by
  cases o with
  | lit n =>
    simp only [evalOp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨h, rfl, fun vs hvs => by cases hvs; rfl⟩
  | addrOf q =>
    simp only [evalOp] at he
    split at he
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, rfl, fun vs hvs => by cases hvs; rfl⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, rfl, fun vs hvs => by cases hvs⟩
  | copy q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      obtain ⟨hm, hl, -, hv⟩ := readCells_eq he
      refine ⟨liveInv_of_eq hm hl h, hl, ?_⟩
      intro vs hvs
      rw [hv vs hvs]; simp [(resolvePlace_spec hr0).2.2, Operand.len]
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, rfl, fun vs hvs => by cases hvs⟩
  | move q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      split at he
      · rename_i s1 vs1 hrd
        obtain ⟨hm, hl, -, hv⟩ := readCells_eq hrd
        have h1 : LiveInv P s1 := liveInv_congr hm (fun l hl' => by rw [hl]; exact hl') h
        have hlen : vs1.length = (Operand.move q).len := by
          rw [hv vs1 rfl]; simp [(resolvePlace_spec hr0).2.2, Operand.len]
        split at he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨liveInv_writeUninit _ _ _ _ h1, ?_, fun vs hvs => by cases hvs; exact hlen⟩
          rw [writeCells, writeCellsK_live, hl]
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨h1, hl, fun vs hvs => by cases hvs; exact hlen⟩
      · rename_i s1 hrd
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hm, hl, -, -⟩ := readCells_eq hrd
        exact ⟨liveInv_of_eq hm hl h, hl, fun vs hvs => by cases hvs⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, rfl, fun vs hvs => by cases hvs⟩
  | load p len =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      split at he
      · split at he
        · rename_i s1 l o hrd
          obtain ⟨hm, hl, -, -⟩ := readCells_eq hrd
          have h1 : LiveInv P s1 := liveInv_congr hm (fun l hl' => by rw [hl]; exact hl') h
          split at he
          · obtain ⟨hm2, hl2, -, hv2⟩ := readCells_eq he
            refine ⟨liveInv_of_eq hm2 hl2 h1, hl2.trans hl, ?_⟩
            intro vs hvs; rw [hv2 vs hvs]; simp [Operand.len]
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨h1, hl, fun vs hvs => by cases hvs⟩
        · rename_i s1 x _ hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hm, hl, -, -⟩ := readCells_eq hrd
          exact ⟨liveInv_of_eq hm hl h, hl, fun vs hvs => by cases hvs⟩
        · rename_i s1 hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hm, hl, -, -⟩ := readCells_eq hrd
          exact ⟨liveInv_of_eq hm hl h, hl, fun vs hvs => by cases hvs⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨h, rfl, fun vs hvs => by cases hvs⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, rfl, fun vs hvs => by cases hvs⟩

end Inv

open Toy.Coalesce.Inv

namespace Inv

theorem liveInv_evalOps {ms : MoveSem} {P : Prog} (os : List Operand) :
    ∀ {s s' : St} {r : Option (List Val)}, evalOps ms P s os = (s', r) → LiveInv P s →
    LiveInv P s' ∧ s'.live = s.live ∧ (∀ vs, r = some vs → vs.length = (os.map Operand.len).sum) := by
  induction os with
  | nil =>
    intro s s' r he h
    simp only [evalOps, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨h, rfl, fun vs hvs => by cases hvs; rfl⟩
  | cons o os ih =>
    intro s s' r he h
    simp only [evalOps] at he
    split at he
    · rename_i s1 vs1 he1
      obtain ⟨h1, hl1, hlen1⟩ := liveInv_evalOp he1 h
      split at he
      · rename_i s2 ws he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h2, hl2, hlen2⟩ := ih he2 h1
        refine ⟨h2, hl2.trans hl1, fun vs hvs => ?_⟩
        cases hvs
        simp [hlen1 vs1 rfl, hlen2 ws rfl]
      · rename_i s2 he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h2, hl2, -⟩ := ih he2 h1
        exact ⟨h2, hl2.trans hl1, fun vs hvs => by cases hvs⟩
    · rename_i s1 he1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, hl1, -⟩ := liveInv_evalOp he1 h
      exact ⟨h1, hl1, fun vs hvs => by cases hvs⟩

theorem liveInv_writeInOrder {ms : MoveSem} {P : Prog} (loc : Nat) (os : List Operand) :
    ∀ (s : St) (off : Nat), LiveInv P s → s.live loc = true →
    off + (os.map Operand.len).sum ≤ P.size loc → LiveInv P (writeInOrder ms P s loc off os) := by
  induction os with
  | nil => intro s off h _ _; exact h
  | cons o os ih =>
    intro s off h hl hb
    simp only [writeInOrder]
    split
    · rename_i s1 vs he
      obtain ⟨h1, hl1, hlen⟩ := liveInv_evalOp he h
      have hlen' := hlen vs rfl
      simp only [List.map_cons, List.sum_cons] at hb
      apply ih
      · exact liveInv_writeCells _ _ _ h1 (by rw [hl1]; exact hl) (by omega)
      · rw [writeCells, writeCellsK_live, hl1]; exact hl
      · omega
    · rename_i s1 he
      exact (liveInv_evalOp he h).1

theorem liveInv_allocate (P : Prog) (s : St) (x : Nat) (h : LiveInv P s) :
    LiveInv P (allocate P s x) := by
  unfold allocate
  split
  · refine liveInv_writeUninit _ _ _ _ (liveInv_congr (s := s) rfl (fun l hl => ?_) h)
    by_cases hlx : l = x <;> simp [hlx, hl]
  · exact h

theorem allocate_live_or (P : Prog) (s : St) (x : Nat) :
    (allocate P s x).live x = true ∨ P.size x = 0 := by
  unfold allocate
  split
  · left
    simp only [resetCells, writeCellsK_live, ↓reduceIte]
  · right
    rename_i hx
    simp only [Prog.size, Prog.nloc] at hx ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : P.sizes.length ≤ x)]

theorem liveInv_deallocate (P : Prog) (s : St) (x : Nat) (h : LiveInv P s) :
    LiveInv P (deallocate P s x) := by
  unfold deallocate
  split
  · intro l o ho
    have hr : (resetCells s x (P.size x)).mem l o =
        (if l = x ∧ 0 ≤ o ∧ o < 0 + (List.replicate (P.size x) Val.uninit).length then
          (List.replicate (P.size x) Val.uninit).getD (o - 0) .uninit else s.mem l o) := by
      unfold resetCells; rw [writeCellsK_eq]
    have hlv : (resetCells s x (P.size x)).live = s.live := writeCellsK_live _ _ _ _ _
    change (resetCells s x (P.size x)).mem l o ≠ .uninit at ho
    change (if l = x then false else (resetCells s x (P.size x)).live l) = true ∧ o < P.size l
    rw [hlv]
    rw [hr] at ho
    by_cases hlx : l = x
    · subst hlx
      exfalso
      split at ho
      · exact ho (getD_replicate_uninit _ _)
      · rename_i hc
        have := (h l o ho).2
        simp at hc; omega
    · simp only [hlx, false_and, ↓reduceIte] at ho ⊢
      exact h l o ho
  · exact h

theorem liveInv_cmpOp (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) (h : LiveInv P s) : LiveInv P (cmpOp ms P A s a b f) := by
  unfold cmpOp
  split
  · rename_i s1 va he1
    have h1 := (liveInv_evalOp he1 h).1
    split
    · rename_i s2 vb he2
      have h2 := (liveInv_evalOp he2 h1).1
      split
      · exact h2
      · exact h2
    · rename_i s2 _ _ he2; exact (liveInv_evalOp he2 h1).1
    · rename_i s2 he2; exact (liveInv_evalOp he2 h1).1
  · rename_i s1 _ _ he1; exact (liveInv_evalOp he1 h).1
  · rename_i s1 he1; exact (liveInv_evalOp he1 h).1

end Inv


theorem liveInv_execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : LiveInv P s) : LiveInv P (execBasic sem P A s st) := by
  unfold execBasic
  split
  · exact h
  · cases st with
    | storageLive x =>
      simp only; split
      · exact h
      · exact liveInv_allocate _ _ _ h
    | storageDead x =>
      simp only; split
      · exact h
      · exact liveInv_deallocate _ _ _ h
    | assign lhs rhs =>
      simp only; split
      · exact h
      · rename_i hsum
        split
        · exact h
        · rename_i r hr
          obtain ⟨hlr, hbr, hlenr⟩ := resolvePlace_spec hr
          split
          · split
            · rename_i s' vs he
              obtain ⟨h1, hl1, hlen⟩ := liveInv_evalOps rhs he h
              exact liveInv_writeCells _ _ _ h1 (by rw [hl1]; exact hlr) (by rw [hlen vs rfl]; omega)
            · rename_i s' he; exact (liveInv_evalOps rhs he h).1
          · exact liveInv_writeInOrder _ _ _ _ h hlr (by omega)
    | store p v =>
      simp only; split
      · rename_i r hr
        split
        · split
          · rename_i s1 l o he1
            obtain ⟨hm1, hl1, -, -⟩ := readCells_eq he1
            have h1 := liveInv_of_eq hm1 hl1 h
            split
            · rename_i s2 vs he2
              obtain ⟨h2, hl2, -⟩ := liveInv_evalOp he2 h1
              split
              · rename_i hc
                exact liveInv_writeCells _ _ _ h2 hc.1 hc.2
              · exact h2
            · rename_i s2 he2; exact (liveInv_evalOp he2 h1).1
          · rename_i s1 _ _ he1
            obtain ⟨hm1, hl1, -, -⟩ := readCells_eq he1; exact liveInv_of_eq hm1 hl1 h
          · rename_i s1 he1
            obtain ⟨hm1, hl1, -, -⟩ := readCells_eq he1; exact liveInv_of_eq hm1 hl1 h
        · exact h
      · exact h
    | ptrEq a b => exact liveInv_cmpOp _ _ _ _ _ _ _ h
    | ptrInRange a b n => exact liveInv_cmpOp _ _ _ _ _ _ _ h
    | out o =>
      simp only; split
      · rename_i s' vs he; exact (liveInv_evalOp he h).1
      · rename_i s' he; exact (liveInv_evalOp he h).1
    | call fn a => exact h
    | nop => exact h

theorem liveInv_execCallee (sem : Sem) (P : Prog) (A : Layout) (s : St) (b : List Stmt)
    (h : LiveInv P s) : LiveInv P (execCallee sem P A s b) := by
  induction b generalizing s with
  | nil => exact h
  | cons st b ih =>
    simp only [execCallee, List.foldl_cons]
    exact ih _ (liveInv_execBasic sem P A s st h)

theorem liveInv_execStmt (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : LiveInv P s) : LiveInv P (execStmt sem P A s st) := by
  unfold execStmt
  split
  · exact h
  · cases st with
    | call fn arg =>
      simp only
      split
      · next q =>
        split
        · exact h
        · next r _ =>
          split
          · exact h
          · exact liveInv_execCallee sem P A _ _ h
      · split
        · rename_i s1 vs he
          obtain ⟨h1, hl1, hlen⟩ := liveInv_evalOp he h
          split
          · exact h1
          · rename_i hc
            simp only [not_or, Ne, Decidable.not_not] at hc
            have h2 := liveInv_allocate P s1 (P.fn fn).prm h1
            have h3 : LiveInv P (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs) := by
              apply liveInv_writeCellsK _ _ _ _ h2
              intro i hi _
              rcases allocate_live_or P s1 (P.fn fn).prm with hlv | hz
              · exact ⟨hlv, by omega⟩
              · omega
            exact liveInv_deallocate P _ _ (liveInv_execCallee sem P A _ (P.fn fn).body h3)
        · rename_i s1 he; exact (liveInv_evalOp he h).1
    | _ => exact liveInv_execBasic sem P A s _ h

theorem liveInv_runAt (sem : Sem) (P : Prog) (A : Layout) (t : Nat) :
    LiveInv P (runAt sem P A t) := by
  induction t with
  | zero => rw [runAt_zero]; exact liveInv_init P
  | succ t ih =>
    by_cases ht : t < P.code.length
    · rw [runAt_succ _ _ _ _ ht]
      exact liveInv_execStmt sem P A _ _ ih
    · rw [runAt_of_le _ _ _ _ (by omega), ← runAt_of_le sem P A t (by omega)]; exact ih

/-! ## Pointer provenance -/

/-- Every pointer value stored in memory has provenance in `S`. -/
def PtrsIn (S : Nat → Prop) (s : St) : Prop := ∀ l o l' o', s.mem l o = .ptr l' o' → S l'

/-- Every pointer value in the list has provenance in `S`. -/
def ValsIn (S : Nat → Prop) (vs : List Val) : Prop := ∀ v ∈ vs, ∀ l' o', v = .ptr l' o' → S l'

/-- The local whose cells a place based at `b` denotes under the alias `al`. -/
def aliasBase (al : Option (Nat × Place)) (b : Nat) : Nat :=
  match al with
  | some (prm, t) => if b = prm then t.base else b
  | none => b

/-- Address-taking discipline of `P` with respect to `S`: top-level statements and callee bodies
take addresses only of places based at locals in `S`, and an in-place call `call fn (move q)` of the
top-level code passes a place based at a local in `S` whenever the callee takes the address of its
parameter. -/
def AddrDisc (S : Nat → Prop) (P : Prog) : Prop :=
  (∀ st ∈ P.code, ∀ b, st.takesAddr b = true → S b) ∧
  (∀ fn, ∀ st ∈ (P.fn fn).body, ∀ b, st.takesAddr b = true → S b) ∧
  (∀ fn q, Stmt.call fn (.move q) ∈ P.code →
    (P.fn fn).body.any (Stmt.takesAddr (P.fn fn).prm) = true → S q.base)

theorem addrDisc_addrTaken (P : Prog) : AddrDisc (AddrTaken P) P := by
  refine ⟨?_, ?_, ?_⟩
  · intro st hst b hb
    unfold AddrTaken
    simp only [Bool.or_eq_true]
    left; left
    exact List.any_eq_true.mpr ⟨st, hst, hb⟩
  · intro fn st hst b hb
    unfold AddrTaken
    simp only [Bool.or_eq_true]
    left; right
    apply List.any_eq_true.mpr
    by_cases hfn : fn < P.fns.length
    · refine ⟨P.fns[fn], List.getElem_mem hfn, ?_⟩
      have hf : P.fn fn = P.fns[fn] := by simp [Prog.fn, List.getD_eq_getElem?_getD, hfn]
      rw [← hf]
      exact List.any_eq_true.mpr ⟨st, hst, hb⟩
    · have hf : P.fn fn = ⟨0, []⟩ := by
        simp [Prog.fn, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega : P.fns.length ≤ fn)]
      rw [hf] at hst; cases hst
  · intro fn q hq hb
    unfold AddrTaken
    simp only [Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨_, hq, ?_⟩
    simp only [Stmt.escapesInPlace, beq_self_eq_true, Bool.true_and]
    exact hb

theorem ptrsIn_init (S : Nat → Prop) : PtrsIn S St.init := by
  intro l o l' o' h; cases h

/-! ### Helper lemmas for pointer provenance -/

namespace Inv

theorem resolvePlace_base {P : Prog} {s : St} {q r : Place} (h : resolvePlace P s q = some r) :
    r.base = aliasBase s.alias q.base := by
  unfold resolvePlace at h
  unfold aliasBase
  split at h
  · rename_i prm t hal
    rw [hal]
    by_cases hb : q.base = prm
    · simp only [hb, ↓reduceIte] at h
      simp only [hb, ↓reduceIte]
      by_cases hl : q.off + q.len ≤ t.len
      · simp only [hl, ↓reduceIte] at h
        split at h
        · cases h; rfl
        · cases h
      · simp only [hl, ↓reduceIte] at h
        cases h
    · simp only [hb, ↓reduceIte] at h
      simp only [hb, ↓reduceIte]
      split at h
      · cases h; rfl
      · cases h
  · rename_i hal
    rw [hal]
    simp only at h
    split at h
    · cases h; rfl
    · cases h

theorem evalOp_alias {ms : MoveSem} {P : Prog} {s s' : St} {o : Operand} {r : Option (List Val)}
    (he : evalOp ms P s o = (s', r)) : s'.alias = s.alias := by
  have h := (step_evalOp ms P s o).alias
  rw [he] at h
  exact h

theorem ptrsIn_congr {S : Nat → Prop} {s t : St} (hm : t.mem = s.mem) (h : PtrsIn S s) :
    PtrsIn S t := by
  intro l o l' o' he
  rw [hm] at he
  exact h l o l' o' he

theorem valsIn_read {S : Nat → Prop} {s : St} (h : PtrsIn S s) (loc off n : Nat) :
    ValsIn S ((List.range n).map fun i => s.mem loc (off + i)) := by
  intro v hv l' o' hvp
  simp only [List.mem_map] at hv
  obtain ⟨i, -, rfl⟩ := hv
  exact h _ _ _ _ hvp

theorem valsIn_replicate {S : Nat → Prop} (n : Nat) : ValsIn S (List.replicate n .uninit) := by
  intro v hv l' o' hvp
  rw [List.eq_of_mem_replicate hv] at hvp
  cases hvp

theorem valsIn_append {S : Nat → Prop} {vs ws : List Val} (h1 : ValsIn S vs) (h2 : ValsIn S ws) :
    ValsIn S (vs ++ ws) := by
  intro v hv
  rcases List.mem_append.1 hv with hv | hv
  · exact h1 v hv
  · exact h2 v hv

theorem ptrsIn_writeCellsK {S : Nat → Prop} {s : St} (k : AccKind) (loc off : Nat) (vs : List Val)
    (h : PtrsIn S s) (hv : ValsIn S vs) : PtrsIn S (writeCellsK k s loc off vs) := by
  rw [writeCellsK_eq]
  intro l o l' o' he
  simp only at he
  split at he
  · rw [List.getD_eq_getElem?_getD] at he
    cases hg : vs[o - off]? with
    | none => rw [hg] at he; cases he
    | some v =>
      rw [hg] at he
      simp only [Option.getD_some] at he
      exact hv v (List.mem_of_getElem? hg) l' o' he
  · exact h l o l' o' he

theorem ptrsIn_evalOp {S : Nat → Prop} {ms : MoveSem} {P : Prog} {s s' : St} {o : Operand}
    {r : Option (List Val)} (he : evalOp ms P s o = (s', r)) (h : PtrsIn S s)
    (ho : ∀ b, o.takesAddr b = true → S (aliasBase s.alias b)) :
    PtrsIn S s' ∧ ∀ vs, r = some vs → ValsIn S vs := by
  cases o with
  | lit n =>
    simp only [evalOp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨h, fun vs hvs => ?_⟩
    cases hvs
    intro v hv l' o' hvp
    simp only [List.mem_singleton] at hv
    subst hv; cases hvp
  | addrOf q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨h, fun vs hvs => ?_⟩
      cases hvs
      intro v hv l' o' hvp
      simp only [List.mem_singleton] at hv
      subst hv
      simp only [Val.ptr.injEq] at hvp
      obtain ⟨rfl, rfl⟩ := hvp
      rw [resolvePlace_base hr0]
      exact ho q.base (by simp [Operand.takesAddr])
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, fun vs hvs => by cases hvs⟩
  | copy q =>
    simp only [evalOp] at he
    split at he
    · obtain ⟨hm, -, -, hv⟩ := readCells_eq he
      refine ⟨ptrsIn_congr hm h, fun vs hvs => ?_⟩
      rw [hv vs hvs]; exact valsIn_read h _ _ _
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, fun vs hvs => by cases hvs⟩
  | move q =>
    simp only [evalOp] at he
    split at he
    · split at he
      · rename_i s1 vs1 hrd
        obtain ⟨hm, -, -, hv⟩ := readCells_eq hrd
        have h1 : PtrsIn S s1 := ptrsIn_congr hm h
        have hvs1 : ValsIn S vs1 := by rw [hv vs1 rfl]; exact valsIn_read h _ _ _
        split at he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨ptrsIn_writeCellsK _ _ _ _ h1 (valsIn_replicate _), fun vs hvs => by cases hvs; exact hvs1⟩
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨h1, fun vs hvs => by cases hvs; exact hvs1⟩
      · rename_i s1 hrd
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hm, -, -, -⟩ := readCells_eq hrd
        exact ⟨ptrsIn_congr hm h, fun vs hvs => by cases hvs⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, fun vs hvs => by cases hvs⟩
  | load p len =>
    simp only [evalOp] at he
    split at he
    · split at he
      · split at he
        · rename_i s1 l o hrd
          obtain ⟨hm, -, -, -⟩ := readCells_eq hrd
          have h1 : PtrsIn S s1 := ptrsIn_congr hm h
          split at he
          · obtain ⟨hm2, -, -, hv2⟩ := readCells_eq he
            refine ⟨ptrsIn_congr hm2 h1, fun vs hvs => ?_⟩
            rw [hv2 vs hvs]; exact valsIn_read h1 _ _ _
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨h1, fun vs hvs => by cases hvs⟩
        · rename_i s1 x _ hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hm, -, -, -⟩ := readCells_eq hrd
          exact ⟨ptrsIn_congr hm h, fun vs hvs => by cases hvs⟩
        · rename_i s1 hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hm, -, -, -⟩ := readCells_eq hrd
          exact ⟨ptrsIn_congr hm h, fun vs hvs => by cases hvs⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨h, fun vs hvs => by cases hvs⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h, fun vs hvs => by cases hvs⟩

theorem ptrsIn_evalOps {S : Nat → Prop} {ms : MoveSem} {P : Prog} (os : List Operand) :
    ∀ {s s' : St} {r : Option (List Val)}, evalOps ms P s os = (s', r) → PtrsIn S s →
    (∀ o ∈ os, ∀ b, o.takesAddr b = true → S (aliasBase s.alias b)) →
    PtrsIn S s' ∧ ∀ vs, r = some vs → ValsIn S vs := by
  induction os with
  | nil =>
    intro s s' r he h _
    simp only [evalOps, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨h, fun vs hvs => ?_⟩
    cases hvs
    intro v hv; cases hv
  | cons o os ih =>
    intro s s' r he h hos
    simp only [evalOps] at he
    split at he
    · rename_i s1 vs1 he1
      obtain ⟨h1, hv1⟩ := ptrsIn_evalOp he1 h (hos o (List.mem_cons_self ..))
      have hal := evalOp_alias he1
      split at he
      · rename_i s2 ws he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h2, hv2⟩ := ih he2 h1 (fun o' ho' b hb => by
          rw [hal]; exact hos o' (List.mem_cons_of_mem _ ho') b hb)
        exact ⟨h2, fun vs hvs => by cases hvs; exact valsIn_append (hv1 vs1 rfl) (hv2 ws rfl)⟩
      · rename_i s2 he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h2, -⟩ := ih he2 h1 (fun o' ho' b hb => by
          rw [hal]; exact hos o' (List.mem_cons_of_mem _ ho') b hb)
        exact ⟨h2, fun vs hvs => by cases hvs⟩
    · rename_i s1 he1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨(ptrsIn_evalOp he1 h (hos o (List.mem_cons_self ..))).1, fun vs hvs => by cases hvs⟩

theorem ptrsIn_writeInOrder {S : Nat → Prop} {ms : MoveSem} {P : Prog} (loc : Nat)
    (os : List Operand) : ∀ (s : St) (off : Nat), PtrsIn S s →
    (∀ o ∈ os, ∀ b, o.takesAddr b = true → S (aliasBase s.alias b)) →
    PtrsIn S (writeInOrder ms P s loc off os) := by
  induction os with
  | nil => intro s off h _; exact h
  | cons o os ih =>
    intro s off h hos
    simp only [writeInOrder]
    split
    · rename_i s1 vs he
      obtain ⟨h1, hv⟩ := ptrsIn_evalOp he h (hos o (List.mem_cons_self ..))
      have hal : (writeCells s1 loc off vs).alias = s.alias :=
        (step_writeCells s1 loc off vs).alias.trans (evalOp_alias he)
      apply ih
      · exact ptrsIn_writeCellsK _ _ _ _ h1 (hv vs rfl)
      · intro o' ho' b hb
        rw [hal]; exact hos o' (List.mem_cons_of_mem _ ho') b hb
    · rename_i s1 he
      exact (ptrsIn_evalOp he h (hos o (List.mem_cons_self ..))).1

theorem ptrsIn_allocate {S : Nat → Prop} (P : Prog) (s : St) (x : Nat) (h : PtrsIn S s) :
    PtrsIn S (allocate P s x) := by
  unfold allocate
  split
  · exact ptrsIn_writeCellsK _ _ _ _ (ptrsIn_congr (s := s) rfl h) (valsIn_replicate _)
  · exact h

theorem ptrsIn_deallocate {S : Nat → Prop} (P : Prog) (s : St) (x : Nat) (h : PtrsIn S s) :
    PtrsIn S (deallocate P s x) := by
  unfold deallocate
  split
  · exact ptrsIn_congr (s := resetCells s x (P.size x)) rfl
      (ptrsIn_writeCellsK _ _ _ _ h (valsIn_replicate _))
  · exact h

theorem ptrsIn_cmpOp {S : Nat → Prop} (ms : MoveSem) (P : Prog) (A : Layout) (s : St)
    (a b : Operand) (f : Nat → Nat → Bool) (h : PtrsIn S s)
    (ha : ∀ x, a.takesAddr x = true → S (aliasBase s.alias x))
    (hb : ∀ x, b.takesAddr x = true → S (aliasBase s.alias x)) :
    PtrsIn S (cmpOp ms P A s a b f) := by
  unfold cmpOp
  split
  · rename_i s1 va he1
    have h1 := (ptrsIn_evalOp he1 h ha).1
    have hb1 : ∀ x, b.takesAddr x = true → S (aliasBase s1.alias x) := by
      rw [evalOp_alias he1]; exact hb
    split
    · rename_i s2 vb he2
      have h2 := (ptrsIn_evalOp he2 h1 hb1).1
      split
      · exact h2
      · exact h2
    · rename_i s2 _ _ he2; exact (ptrsIn_evalOp he2 h1 hb1).1
    · rename_i s2 he2; exact (ptrsIn_evalOp he2 h1 hb1).1
  · rename_i s1 _ _ he1; exact (ptrsIn_evalOp he1 h ha).1
  · rename_i s1 he1; exact (ptrsIn_evalOp he1 h ha).1

end Inv


theorem ptrsIn_execBasic (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : PtrsIn S s) (hst : ∀ b, st.takesAddr b = true → S (aliasBase s.alias b)) :
    PtrsIn S (execBasic sem P A s st) := by
  unfold execBasic
  split
  · exact h
  · cases st with
    | storageLive x =>
      simp only; split
      · exact h
      · exact ptrsIn_allocate _ _ _ h
    | storageDead x =>
      simp only; split
      · exact h
      · exact ptrsIn_deallocate _ _ _ h
    | assign lhs rhs =>
      have hos : ∀ o ∈ rhs, ∀ b, o.takesAddr b = true → S (aliasBase s.alias b) :=
        fun o ho b hb => hst b (List.any_eq_true.mpr ⟨o, ho, hb⟩)
      simp only; split
      · exact h
      · split
        · exact h
        · split
          · split
            · rename_i s' vs he
              obtain ⟨h1, hv⟩ := ptrsIn_evalOps rhs he h hos
              exact ptrsIn_writeCellsK _ _ _ _ h1 (hv vs rfl)
            · rename_i s' he; exact (ptrsIn_evalOps rhs he h hos).1
          · exact ptrsIn_writeInOrder _ _ _ _ h hos
    | store p v =>
      have hv : ∀ b, v.takesAddr b = true → S (aliasBase s.alias b) := hst
      simp only; split
      · split
        · split
          · rename_i s1 l o he1
            obtain ⟨hm1, -, hal1, -⟩ := readCells_eq he1
            have h1 := ptrsIn_congr hm1 h
            have hv1 : ∀ b, v.takesAddr b = true → S (aliasBase s1.alias b) := by
              rw [hal1]; exact hv
            split
            · rename_i s2 vs he2
              obtain ⟨h2, hvs⟩ := ptrsIn_evalOp he2 h1 hv1
              split
              · exact ptrsIn_writeCellsK _ _ _ _ h2 (hvs vs rfl)
              · exact h2
            · rename_i s2 he2; exact (ptrsIn_evalOp he2 h1 hv1).1
          · rename_i s1 _ _ he1
            obtain ⟨hm1, -, -, -⟩ := readCells_eq he1; exact ptrsIn_congr hm1 h
          · rename_i s1 he1
            obtain ⟨hm1, -, -, -⟩ := readCells_eq he1; exact ptrsIn_congr hm1 h
        · exact h
      · exact h
    | ptrEq a b =>
      refine ptrsIn_cmpOp _ _ _ _ _ _ _ h (fun x hx => hst x ?_) (fun x hx => hst x ?_) <;>
        simp [Stmt.takesAddr, hx]
    | ptrInRange a b n =>
      refine ptrsIn_cmpOp _ _ _ _ _ _ _ h (fun x hx => hst x ?_) (fun x hx => hst x ?_) <;>
        simp [Stmt.takesAddr, hx]
    | out o =>
      have ho : ∀ b, o.takesAddr b = true → S (aliasBase s.alias b) := hst
      simp only; split
      · rename_i s' vs he; exact (ptrsIn_evalOp he h ho).1
      · rename_i s' he; exact (ptrsIn_evalOp he h ho).1
    | call fn a => exact h
    | nop => exact h

theorem ptrsIn_execCallee (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (s : St)
    (b : List Stmt) (h : PtrsIn S s)
    (hb : ∀ st ∈ b, ∀ x, st.takesAddr x = true → S (aliasBase s.alias x)) :
    PtrsIn S (execCallee sem P A s b) := by
  induction b generalizing s with
  | nil => exact h
  | cons st b ih =>
    simp only [execCallee, List.foldl_cons]
    have hal := (step_execBasic sem P A s st).alias
    apply ih
    · exact ptrsIn_execBasic S sem P A s st h (hb st (List.mem_cons_self ..))
    · intro st' hst' x hx
      rw [hal]; exact hb st' (List.mem_cons_of_mem _ hst') x hx

namespace Inv

theorem ptrsIn_execCallee_none (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (s : St)
    (b : List Stmt) (h : PtrsIn S s) (ha : s.alias = none)
    (hb : ∀ st ∈ b, ∀ x, st.takesAddr x = true → S x) :
    PtrsIn S (execCallee sem P A s b) :=
  ptrsIn_execCallee S sem P A s b h (fun st hst x hx => by rw [ha]; exact hb st hst x hx)

end Inv

/-- A top-level statement of the code, started without an alias, preserves `PtrsIn S` under the
address-taking discipline. -/
theorem ptrsIn_execStmt (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (hd : AddrDisc S P) (hst : st ∈ P.code) (ha : s.alias = none) (h : PtrsIn S s) :
    PtrsIn S (execStmt sem P A s st) := by
  unfold execStmt
  split
  · exact h
  · cases st with
    | call fn arg =>
      have harg : ∀ b, arg.takesAddr b = true → S (aliasBase s.alias b) := fun b hb => by
        rw [ha]; exact hd.1 _ hst b hb
      simp only
      split
      · split
        · exact h
        · next r hr =>
          split
          · exact h
          · refine ptrsIn_congr (s := execCallee sem P A
              { s with alias := some ((P.fn fn).prm, r), inCall := true } (P.fn fn).body) rfl
              (ptrsIn_execCallee S sem P A _ _ h ?_)
            intro st hst' x hx
            show S (aliasBase (some ((P.fn fn).prm, r)) x)
            simp only [aliasBase]
            split
            · rename_i hxe
              subst hxe
              rw [resolvePlace_base hr, ha]
              exact hd.2.2 fn _ hst (List.any_eq_true.mpr ⟨st, hst', hx⟩)
            · exact hd.2.1 fn st hst' x hx
      · split
        · rename_i s1 vs he
          obtain ⟨h1, hv⟩ := ptrsIn_evalOp he h harg
          have hal1 : s1.alias = none := (evalOp_alias he).trans ha
          split
          · exact h1
          · have h2 := ptrsIn_allocate P s1 (P.fn fn).prm h1
            have h3 := ptrsIn_writeCellsK .write (P.fn fn).prm 0 vs h2 (hv vs rfl)
            have hal3 : (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias = none := by
              rw [(step_writeCells _ _ _ _).alias, (step_allocate _ _ _).alias, hal1]
            exact ptrsIn_deallocate P _ _ (ptrsIn_execCallee_none S sem P A _ _ h3 hal3
              (fun st hst' x hx => hd.2.1 fn st hst' x hx))
        · rename_i s1 he
          exact (ptrsIn_evalOp he h harg).1
    | _ =>
      exact ptrsIn_execBasic S sem P A s _ h (fun b hb => by rw [ha]; exact hd.1 _ hst b hb)

theorem ptrsIn_runAt (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (hd : AddrDisc S P)
    (t : Nat) : PtrsIn S (runAt sem P A t) := by
  induction t with
  | zero => rw [runAt_zero]; exact ptrsIn_init S
  | succ t ih =>
    by_cases ht : t < P.code.length
    · rw [runAt_succ _ _ _ _ ht]
      exact ptrsIn_execStmt S sem P A _ _ hd (List.getElem_mem ht)
        (runAt_frame sem P A t (by omega)).2.2.1 ih
    · rw [runAt_of_le _ _ _ _ (by omega), ← runAt_of_le sem P A t (by omega)]; exact ih

theorem run_ptrsIn_addrTaken (sem : Sem) (P : Prog) (A : Layout) :
    PtrsIn (AddrTaken P) (run sem P A) := by
  rw [run_eq_runAt]; exact ptrsIn_runAt _ sem P A (addrDisc_addrTaken P) _

/-- The allocation invariant holds in the final state of every run. -/
theorem inv_run_liveInv (sem : Sem) (P : Prog) (A : Layout) : LiveInv P (run sem P A) := by
  rw [run_eq_runAt]; exact liveInv_runAt sem P A _

end Toy.Coalesce
