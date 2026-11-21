import ToyCoalesce.Inv

/-!
# Proof: in-place call-argument upgrades
-/

namespace Toy.Coalesce

namespace InPlace

open Toy.Coalesce.Inv

/-! ## Moving a local that is never address-taken does not change a run -/

section Layout

variable {S : Nat → Prop} {A A' : Layout} (hA : ∀ l, S l → A l = A' l)
include hA

theorem val_layout {vs : List Val} (hv : ValsIn S vs) :
    ∀ v ∈ vs, v.addr? A = v.addr? A' ∧ v.obs A = v.obs A' := by
  intro v hmem
  cases v with
  | uninit => exact ⟨rfl, rfl⟩
  | int n => exact ⟨rfl, rfl⟩
  | ptr l o =>
    have := hA l (hv _ hmem l o rfl)
    simp [Val.addr?, Val.obs, this]

theorem cmpOp_layout (ms : MoveSem) (P : Prog) (s : St) (a b : Operand) (f : Nat → Nat → Bool)
    (h : PtrsIn S s) (ha : ∀ x, a.takesAddr x = true → S (aliasBase s.alias x))
    (hb : ∀ x, b.takesAddr x = true → S (aliasBase s.alias x)) :
    cmpOp ms P A s a b f = cmpOp ms P A' s a b f := by
  unfold cmpOp
  rcases he1 : evalOp ms P s a with ⟨s1, _ | va⟩
  · rfl
  · obtain ⟨h1, hv1⟩ := ptrsIn_evalOp he1 h ha
    have hal : s1.alias = s.alias := evalOp_alias he1
    rcases va with _ | ⟨va, _ | ⟨w, ws⟩⟩
    · rfl
    · simp only
      rcases he2 : evalOp ms P s1 b with ⟨s2, _ | vb⟩
      · rfl
      · obtain ⟨_, hv2⟩ := ptrsIn_evalOp he2 h1 (by rw [hal]; exact hb)
        rcases vb with _ | ⟨vb, _ | ⟨w', ws'⟩⟩
        · rfl
        · simp only
          rw [(val_layout hA (hv1 _ rfl) va (by simp)).1,
            (val_layout hA (hv2 _ rfl) vb (by simp)).1]
        · rfl
    · rfl

theorem execBasic_layout (sem : Sem) (P : Prog) (s : St) (st : Stmt) (h : PtrsIn S s)
    (hst : ∀ b, st.takesAddr b = true → S (aliasBase s.alias b)) :
    execBasic sem P A s st = execBasic sem P A' s st := by
  unfold execBasic
  split
  · rfl
  · cases st with
    | ptrEq a b =>
      exact cmpOp_layout hA _ _ _ _ _ _ h (fun x hx => hst x (by simp [Stmt.takesAddr, hx]))
        (fun x hx => hst x (by simp [Stmt.takesAddr, hx]))
    | ptrInRange a b n =>
      exact cmpOp_layout hA _ _ _ _ _ _ h (fun x hx => hst x (by simp [Stmt.takesAddr, hx]))
        (fun x hx => hst x (by simp [Stmt.takesAddr, hx]))
    | out o =>
      simp only
      rcases he : evalOp sem.move P s o with ⟨s', _ | vs⟩
      · rfl
      · simp only
        obtain ⟨_, hv⟩ := ptrsIn_evalOp he h (fun x hx => hst x (by simp [Stmt.takesAddr, hx]))
        have : vs.map (Val.obs A) = vs.map (Val.obs A') :=
          List.map_congr_left (fun v hv' => (val_layout hA (hv vs rfl) v hv').2)
        rw [this]
    | _ => rfl

theorem execCallee_layout (sem : Sem) (P : Prog) (b : List Stmt) :
    ∀ s, PtrsIn S s → (∀ st ∈ b, ∀ x, st.takesAddr x = true → S (aliasBase s.alias x)) →
      execCallee sem P A s b = execCallee sem P A' s b := by
  induction b with
  | nil => intro s _ _; rfl
  | cons st b ih =>
    intro s h hb
    simp only [execCallee, List.foldl_cons]
    rw [execBasic_layout hA sem P s st h (hb st (by simp))]
    exact ih _ (ptrsIn_execBasic S sem P A' s st h (hb st (by simp)))
      (by rw [(step_execBasic sem P A' s st).alias]; exact fun st' h' => hb st' (by simp [h']))

theorem execStmt_layout (sem : Sem) (P : Prog) (hd : AddrDisc S P) (s : St) (st : Stmt)
    (hst : st ∈ P.code) (hal : s.alias = none) (h : PtrsIn S s) :
    execStmt sem P A s st = execStmt sem P A' s st := by
  unfold execStmt
  split
  · rfl
  · cases st with
    | call fn arg =>
      simp only
      split
      · rename_i q _
        split
        · rfl
        · rename_i r hr
          split
          · rfl
          · rw [execCallee_layout hA sem P _ { s with alias := some ((P.fn fn).prm, r), inCall := true }
              (ptrsIn_congr (s := s) rfl h)]
            intro st' hst' x hx
            simp only [aliasBase]
            split
            · rename_i hxe
              subst hxe
              rw [resolvePlace_base hr, hal]
              exact hd.2.2 fn q hst (List.any_eq_true.2 ⟨st', hst', hx⟩)
            · exact hd.2.1 fn st' hst' x hx
      · rename_i arg _ _ _
        rcases he : evalOp sem.move P s arg with ⟨s1, _ | vs⟩
        · rfl
        · simp only
          split
          · rfl
          · obtain ⟨h1, hv⟩ := ptrsIn_evalOp he h (fun x hx => by
              rw [hal]; exact hd.1 _ hst x (by simpa [Stmt.takesAddr] using hx))
            have hs1 : s1.alias = none := (evalOp_alias he).trans hal
            have hp : PtrsIn S { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with
                inCall := true } :=
              ptrsIn_congr (s := writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs) rfl
                (ptrsIn_writeCellsK _ _ _ _ (ptrsIn_allocate _ _ _ h1) (hv vs rfl))
            rw [execCallee_layout hA sem P _ _ hp]
            intro st' hst' x hx
            have : (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias = none := by
              rw [(step_writeCells _ _ _ _).alias, (step_allocate _ _ _).alias, hs1]
            simp only [this, aliasBase]
            exact hd.2.1 fn st' hst' x hx
    | _ => exact execBasic_layout hA sem P s _ h (fun b hb => by rw [hal]; exact hd.1 _ hst b hb)

theorem runAt_layout (sem : Sem) (P : Prog) (hd : AddrDisc S P) (t : Nat) :
    runAt sem P A t = runAt sem P A' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < P.code.length
    · rw [runAt_succ _ _ _ _ ht, runAt_succ _ _ _ _ ht, ih]
      simp only [execTop]
      rw [execStmt_layout hA sem P hd _ _ (List.getElem_mem ht)
        (runAt_frame sem P A' t (by omega)).2.2.1 (ptrsIn_runAt S sem P A' hd t)]
    · rw [runAt_of_le _ _ _ _ (by omega), runAt_of_le _ _ _ _ (by omega),
        ← runAt_of_le sem P A t (by omega), ← runAt_of_le sem P A' t (by omega), ih]

theorem run_layout (sem : Sem) (P : Prog) (hd : AddrDisc S P) : run sem P A = run sem P A' := by
  rw [run_eq_runAt, run_eq_runAt, runAt_layout hA sem P hd]

end Layout


/-! ## The upgraded code -/

theorem modifyAt_length (f : Stmt → Stmt) (l : List Stmt) (k : Nat) :
    (modifyAt f l k).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons st sts ih => cases k <;> simp [modifyAt, ih]

theorem modifyAt_getElem? (f : Stmt → Stmt) (l : List Stmt) (k i : Nat) :
    (modifyAt f l k)[i]? = if i = k then l[i]?.map f else l[i]? := by
  induction l generalizing k i with
  | nil => simp [modifyAt]
  | cons st sts ih =>
    cases k <;> cases i <;> simp [modifyAt, ih]

theorem code_length (P : Prog) (k : Nat) : (P.upgradeAt k).code.length = P.code.length := by
  simp [Prog.code, Prog.upgradeAt, modifyAt_length]

theorem code_getElem?_ne (P : Prog) (k i : Nat) (hi : i ≠ k) :
    (P.upgradeAt k).code[i]? = P.code[i]? := by
  simp only [Prog.code, Prog.upgradeAt, List.getElem?_append, modifyAt_length,
    modifyAt_getElem?, hi, ↓reduceIte]

theorem code_getElem?_self (P : Prog) (k : Nat) (st : Stmt) (h : P.body[k]? = some st) :
    (P.upgradeAt k).code[k]? = some st.upgradeCopy ∧ P.code[k]? = some st := by
  have hk : k < P.body.length := by
    rcases Nat.lt_or_ge k P.body.length with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none hk] at h; cases h
  constructor
  · simp only [Prog.code, Prog.upgradeAt, List.getElem?_append, modifyAt_length,
      modifyAt_getElem?, hk, ↓reduceIte, h, Option.map_some]
  · simp only [Prog.code, List.getElem?_append, hk, ↓reduceIte, h]

theorem execTop_upgrade (sem : Sem) (P : Prog) (k : Nat) (A : Layout) :
    execTop sem (P.upgradeAt k) A = execTop sem P A :=
  execTop_congr (P := P.upgradeAt k) (P' := P) rfl rfl sem A

theorem runAt_upgrade_le (sem : Sem) (P : Prog) (k : Nat) (A : Layout) (t : Nat) (ht : t ≤ k) :
    runAt sem (P.upgradeAt k) A t = runAt sem P A t := by
  unfold runAt
  rw [execTop_upgrade]
  congr 1
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take]
  split
  · exact code_getElem?_ne P k i (by omega)
  · rfl

/-- One step of the upgraded run away from the upgraded statement. -/
theorem runAt_upgrade_succ (sem : Sem) (P : Prog) (k : Nat) (A : Layout) (t : Nat)
    (ht : t < P.code.length) (htk : t ≠ k) :
    runAt sem (P.upgradeAt k) A (t + 1) = execTop sem P A (runAt sem (P.upgradeAt k) A t) P.code[t] := by
  rw [runAt_succ _ _ _ _ (by rw [code_length]; exact ht), execTop_upgrade]
  congr 1
  have h1 := code_getElem?_ne P k t htk
  rw [List.getElem?_eq_getElem (by rw [code_length]; exact ht), List.getElem?_eq_getElem ht] at h1
  exact Option.some.inj h1

/-! ## Log scanning -/

theorem ftnr_append_left (a : Access → Bool) (l o : Nat) (X Y : List Access)
    (h : firstTouchNotRead a l o (X ++ Y) = true) : firstTouchNotRead a l o X = true := by
  induction X with
  | nil => rfl
  | cons e X ih =>
    simp only [List.cons_append, firstTouchNotRead] at h ⊢
    split at h
    · rename_i hc; rw [ite_eq_left hc]; exact h
    · rename_i hc; rw [ite_eq_right hc]; exact ih h

theorem ftnr_append_untouched (a : Access → Bool) (l o : Nat) (X Y : List Access)
    (hX : ∀ e ∈ X, ¬ (e.loc = l ∧ e.off = o)) :
    firstTouchNotRead a l o (X ++ Y) = firstTouchNotRead a l o Y := by
  induction X with
  | nil => rfl
  | cons e X ih =>
    simp only [List.cons_append, firstTouchNotRead]
    have hne : ¬ (a e && e.loc == l && e.off == o) = true := by
      have := hX e (by simp)
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact fun h => this ⟨h.1.2, h.2⟩
    rw [ite_eq_right hne]
    exact ih (fun e' he' => hX e' (by simp [he']))

theorem ftnr_reads (tk : Nat) (ic : Bool) (l : Nat) : ∀ (m os i : Nat), i < m →
    firstTouchNotRead (fun _ => true) l (os + i)
      ((List.range m).map fun j => (⟨tk, ic, l, os + j, .read⟩ : Access)) = false := by
  intro m
  induction m with
  | zero => intro os i hi; omega
  | succ m ih =>
    intro os i hi
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases i with
    | zero => simp [firstTouchNotRead]
    | succ i =>
      simp only [firstTouchNotRead, Nat.add_zero]
      have hne : ¬ ((fun _ => true) (⟨tk, ic, l, os, .read⟩ : Access) && l == l &&
          os == os + (i + 1)) = true := by simp
      rw [ite_eq_right hne]
      have := ih (os + 1) i (by omega)
      rw [show os + 1 + i = os + (i + 1) by omega] at this
      rw [← this]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      congr 1
      omega

/-! ## Reading cells from two related states -/

theorem readCells_sim (s t : St) (ls os lt ot n : Nat) :
    ∃ m, m ≤ n ∧ (readCells s ls os n).1.log =
        s.log ++ (List.range m).map (fun i => (⟨s.tick, s.inCall, ls, os + i, .read⟩ : Access)) ∧
      ((∀ i, i < m → t.mem lt (ot + i) = s.mem ls (os + i)) →
        (readCells t lt ot n).2 = (readCells s ls os n).2 ∧
        (t.status = s.status → (readCells t lt ot n).1.status = (readCells s ls os n).1.status)) := by
  obtain ⟨h1, h2, m, hm, h3, h4, h5, h6⟩ := readCells_spec s ls os n
  obtain ⟨g1, g2, -⟩ := readCells_spec t lt ot n
  refine ⟨m, hm, h3, fun hag => ?_⟩
  by_cases hA : ∀ i, i < n → s.mem ls (os + i) ≠ .uninit
  · have hmn := h5 hA
    subst hmn
    have hB : ∀ i, i < m → t.mem lt (ot + i) ≠ .uninit := fun i hi => by
      rw [hag i hi]; exact hA i hi
    rw [h1, h2, g1, g2, ite_eq_left hA, ite_eq_left hB, ite_eq_left hA, ite_eq_left hB]
    refine ⟨?_, fun hst => hst⟩
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    exact hag i hi
  · obtain ⟨hm0, hu⟩ := h6 hA
    have hB : ¬ ∀ i, i < n → t.mem lt (ot + i) ≠ .uninit := fun hB =>
      hB (m - 1) (by omega) (by rw [hag (m - 1) (by omega)]; exact hu)
    rw [h1, h2, g1, g2, ite_eq_right hA, ite_eq_right hB, ite_eq_right hA, ite_eq_right hB]
    exact ⟨rfl, fun _ => rfl⟩



theorem Step.ext {s t : St} (h : Step s t) : ∃ d, t.log = s.log ++ d :=
  let ⟨d, h1, _⟩ := h.log; ⟨d, h1⟩

theorem pair_eta {α β : Type} (x : α × β) {b : β} (h : x.2 = b) : x = (x.1, b) := Prod.ext rfl h

/-! ## After the call: states that differ only on not-yet-retouched cells -/

/-- Source state `S` and target state `T` agree on everything except the log and the memory of
cells in `D` that the source has not touched since log position `n`. The source's allocation
pairs are the target's, plus pairs whose first local is `p`. -/
structure R3 (p : Nat) (D : Nat → Nat → Prop) (n : Nat) (S T : St) : Prop where
  live : T.live = S.live
  alias : T.alias = S.alias
  tick : T.tick = S.tick
  inCall : T.inCall = S.inCall
  status : T.status = S.status
  trace : T.trace = S.trace
  conf : ∀ c ∈ S.conflicts, c ∈ T.conflicts ∨ c.1 = p
  len : n ≤ S.log.length
  mem : ∀ l o, T.mem l o ≠ S.mem l o → D l o ∧ ∀ e ∈ S.log.drop n, ¬ (e.loc = l ∧ e.off = o)

/-- From log position `n` on, the first touch of every cell of `D` (if any) is not a read. -/
def Good3 (D : Nat → Nat → Prop) (n : Nat) (L : List Access) : Prop :=
  ∀ l o, D l o → firstTouchNotRead (fun _ => true) l o (L.drop n) = true

theorem good3_prefix {D : Nat → Nat → Prop} {n : Nat} {L1 L2 : List Access}
    (hext : ∃ d, L2 = L1 ++ d) (h : Good3 D n L2) : Good3 D n L1 := by
  obtain ⟨d, rfl⟩ := hext
  intro l o hD
  by_cases hn : n ≤ L1.length
  · have := h l o hD
    rw [List.drop_append_of_le_length hn] at this
    exact ftnr_append_left _ _ _ _ _ this
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

theorem good3_stepT {D : Nat → Nat → Prop} {n : Nat} {s t : St} (hs : StepT s t)
    (h : Good3 D n t.log) : Good3 D n s.log :=
  good3_prefix (let ⟨d, h1, _⟩ := hs.log; ⟨d, h1⟩) h

theorem good3_step {D : Nat → Nat → Prop} {n : Nat} {s t : St} (hs : Step s t)
    (h : Good3 D n t.log) : Good3 D n s.log := good3_prefix (Step.ext hs) h

namespace R3

variable {p : Nat} {D : Nat → Nat → Prop} {n : Nat} {S T : St}

theorem fail (h : R3 p D n S T) (k : Status) : R3 p D n (S.fail k) (T.fail k) :=
  ⟨h.live, h.alias, h.tick, h.inCall, rfl, h.trace, h.conf, h.len, h.mem⟩

theorem emit (h : R3 p D n S T) (e : Event) : R3 p D n (S.emit e) (T.emit e) :=
  ⟨h.live, h.alias, h.tick, h.inCall, h.status, by simp [St.emit, h.trace], h.conf, h.len, h.mem⟩

theorem ctx (h : R3 p D n S T) (a : Option (Nat × Place)) (c : Bool) :
    R3 p D n { S with alias := a, inCall := c } { T with alias := a, inCall := c } :=
  ⟨h.live, rfl, h.tick, rfl, h.status, h.trace, h.conf, h.len, h.mem⟩

theorem setInCall (h : R3 p D n S T) (c : Bool) :
    R3 p D n { S with inCall := c } { T with inCall := c } :=
  ⟨h.live, h.alias, h.tick, rfl, h.status, h.trace, h.conf, h.len, h.mem⟩

theorem setTick (h : R3 p D n S T) (k : Nat) :
    R3 p D n { S with tick := k } { T with tick := k } :=
  ⟨h.live, h.alias, rfl, h.inCall, h.status, h.trace, h.conf, h.len, h.mem⟩

theorem setLive (h : R3 p D n S T) (x : Nat) (b : Bool) :
    R3 p D n { S with live := fun z => if z = x then b else S.live z }
      { T with live := fun z => if z = x then b else T.live z } :=
  ⟨by rw [h.live], h.alias, h.tick, h.inCall, h.status, h.trace, h.conf, h.len, h.mem⟩

theorem addConf (h : R3 p D n S T) (L : List (Nat × Nat)) :
    R3 p D n { S with conflicts := S.conflicts ++ L } { T with conflicts := T.conflicts ++ L } := by
  refine ⟨h.live, h.alias, h.tick, h.inCall, h.status, h.trace, ?_, h.len, h.mem⟩
  intro c hc
  simp only [List.mem_append] at hc ⊢
  rcases hc with hc | hc
  · rcases h.conf c hc with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1
  · exact Or.inl (Or.inr hc)

theorem resolve (h : R3 p D n S T) (P : Prog) (q : Place) :
    resolvePlace P T q = resolvePlace P S q := by
  unfold resolvePlace; rw [h.alias, h.live]

theorem read (h : R3 p D n S T) (l o m : Nat) (hg : Good3 D n (readCells S l o m).1.log) :
    R3 p D n (readCells S l o m).1 (readCells T l o m).1 ∧
      (readCells T l o m).2 = (readCells S l o m).2 := by
  obtain ⟨k, hk, hlog, hsim⟩ := readCells_sim S T l o l o m
  have hag : ∀ i, i < k → T.mem l (o + i) = S.mem l (o + i) := by
    intro i hi
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨hD, hu⟩ := h.mem l (o + i) hne
    have := hg l (o + i) hD
    rw [hlog, List.drop_append_of_le_length h.len, ftnr_append_untouched _ _ _ _ _ hu,
      ftnr_reads _ _ _ _ _ _ hi] at this
    cases this
  obtain ⟨h2, h3⟩ := hsim hag
  refine ⟨?_, h2⟩
  have hst := h3 h.status
  rw [readCells_frame S l o m, readCells_frame T l o m] at hst ⊢
  refine ⟨h.live, h.alias, h.tick, h.inCall, hst, h.trace, h.conf, ?_, ?_⟩
  · simp only [hlog, List.length_append]; have := h.len; omega
  · intro l' o' hne
    obtain ⟨hD, hu⟩ := h.mem l' o' hne
    refine ⟨hD, ?_⟩
    simp only [hlog, List.drop_append_of_le_length h.len, List.mem_append, List.mem_map,
      List.mem_range]
    rintro e (he | ⟨i, hi, rfl⟩) ⟨h1, h2⟩
    · exact hu e he ⟨h1, h2⟩
    · simp only at h1 h2
      subst h1 h2
      exact hne (hag i hi)

theorem write (h : R3 p D n S T) (k : AccKind) (l o : Nat) (vs : List Val) :
    R3 p D n (writeCellsK k S l o vs) (writeCellsK k T l o vs) := by
  rw [writeCellsK_eq, writeCellsK_eq]
  refine ⟨h.live, h.alias, h.tick, h.inCall, h.status, h.trace, h.conf, ?_, ?_⟩
  · simp only [List.length_append]; have := h.len; omega
  · intro l' o' hne
    simp only at hne ⊢
    by_cases hc : l' = l ∧ o ≤ o' ∧ o' < o + vs.length
    · rw [ite_eq_left hc, ite_eq_left hc] at hne; exact absurd rfl hne
    · rw [ite_eq_right hc, ite_eq_right hc] at hne
      obtain ⟨hD, hu⟩ := h.mem l' o' hne
      refine ⟨hD, ?_⟩
      simp only [List.drop_append_of_le_length h.len, List.mem_append, List.mem_map,
        List.mem_range]
      rintro e (he | ⟨i, hi, rfl⟩) ⟨h1, h2⟩
      · exact hu e he ⟨h1, h2⟩
      · simp only at h1 h2
        exact hc ⟨h1.symm, by omega, by omega⟩

theorem allocate (h : R3 p D n S T) (P : Prog) (x : Nat) :
    R3 p D n (Toy.Coalesce.allocate P S x) (Toy.Coalesce.allocate P T x) := by
  unfold Toy.Coalesce.allocate
  split
  · have hlo : liveOthers P T x = liveOthers P S x := by unfold liveOthers; rw [h.live]
    rw [hlo]
    exact ((h.addConf _).setLive x true).write _ _ _ _
  · exact h.fail _

theorem deallocate (h : R3 p D n S T) (P : Prog) (x : Nat) :
    R3 p D n (Toy.Coalesce.deallocate P S x) (Toy.Coalesce.deallocate P T x) := by
  unfold Toy.Coalesce.deallocate
  rw [h.live]
  split
  · exact (h.write _ _ _ _).setLive x false
  · exact h

theorem evalOp (h : R3 p D n S T) (ms : MoveSem) (P : Prog) (o : Operand)
    (hg : Good3 D n (Toy.Coalesce.evalOp ms P S o).1.log) :
    R3 p D n (Toy.Coalesce.evalOp ms P S o).1 (Toy.Coalesce.evalOp ms P T o).1 ∧
      (Toy.Coalesce.evalOp ms P T o).2 = (Toy.Coalesce.evalOp ms P S o).2 := by
  cases o with
  | lit k => exact ⟨h, rfl⟩
  | addrOf q =>
    simp only [Toy.Coalesce.evalOp, h.resolve]
    cases resolvePlace P S q with
    | none => exact ⟨h.fail _, rfl⟩
    | some r => exact ⟨h, rfl⟩
  | copy q =>
    simp only [Toy.Coalesce.evalOp, h.resolve] at hg ⊢
    generalize resolvePlace P S q = rr at hg ⊢
    cases rr with
    | none => exact ⟨h.fail _, rfl⟩
    | some r => exact h.read _ _ _ hg
  | move q =>
    simp only [Toy.Coalesce.evalOp, h.resolve] at hg ⊢
    generalize resolvePlace P S q = rr at hg ⊢
    cases rr with
    | none => exact ⟨h.fail _, rfl⟩
    | some r =>
      simp only at hg ⊢
      rcases hrs : readCells S r.base r.off r.len with ⟨s', _ | vs⟩ <;> rw [hrs] at hg <;>
        simp only at hg
      · obtain ⟨h1, h2⟩ := h.read r.base r.off r.len (by rw [hrs]; exact hg)
        rw [hrs] at h1 h2
        rw [pair_eta (readCells T r.base r.off r.len) h2]
        exact ⟨h1, rfl⟩
      · have hg1 : Good3 D n s'.log := by
          split at hg
          · exact good3_step (step_writeCells _ _ _ _) hg
          · exact hg
        obtain ⟨h1, h2⟩ := h.read r.base r.off r.len (by rw [hrs]; exact hg1)
        rw [hrs] at h1 h2
        rw [pair_eta (readCells T r.base r.off r.len) h2]
        simp only
        split
        · exact ⟨h1.write _ _ _ _, rfl⟩
        · exact ⟨h1, rfl⟩
  | load pl len =>
    simp only [Toy.Coalesce.evalOp, h.resolve] at hg ⊢
    generalize resolvePlace P S pl = rr at hg ⊢
    cases rr with
    | none => exact ⟨h.fail _, rfl⟩
    | some r =>
      simp only at hg ⊢
      split
      · rename_i hr1
        simp only [hr1, ↓reduceIte] at hg
        rcases hrs : readCells S r.base r.off 1 with ⟨s', _ | vs⟩ <;> rw [hrs] at hg <;>
          (try simp only at hg)
        · obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact hg)
          rw [hrs] at h1 h2
          rw [pair_eta (readCells T r.base r.off 1) h2]
          exact ⟨h1, rfl⟩
        · rcases vs with _ | ⟨v, _ | ⟨w, ws⟩⟩
          · obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact good3_step (step_fail _ _) hg)
            rw [hrs] at h1 h2
            rw [pair_eta (readCells T r.base r.off 1) h2]
            exact ⟨h1.fail _, rfl⟩
          · cases v with
            | ptr l o =>
              simp only at hg
              have hg1 : Good3 D n s'.log := by
                split at hg
                · exact good3_step (step_readCells _ _ _ _) hg
                · exact good3_step (step_fail _ _) hg
              obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact hg1)
              rw [hrs] at h1 h2
              rw [pair_eta (readCells T r.base r.off 1) h2]
              simp only [h1.live]
              split
              · rename_i hc
                simp only [hc, and_self, ↓reduceIte] at hg
                exact h1.read _ _ _ hg
              · exact ⟨h1.fail _, rfl⟩
            | _ =>
              obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact good3_step (step_fail _ _) hg)
              rw [hrs] at h1 h2
              rw [pair_eta (readCells T r.base r.off 1) h2]
              exact ⟨h1.fail _, rfl⟩
          · cases v <;>
            · obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact good3_step (step_fail _ _) hg)
              rw [hrs] at h1 h2
              rw [pair_eta (readCells T r.base r.off 1) h2]
              exact ⟨h1.fail _, rfl⟩
      · exact ⟨h.fail _, rfl⟩

theorem evalOps (ms : MoveSem) (P : Prog) (os : List Operand) : ∀ {S T : St}, R3 p D n S T →
    Good3 D n (Toy.Coalesce.evalOps ms P S os).1.log →
    R3 p D n (Toy.Coalesce.evalOps ms P S os).1 (Toy.Coalesce.evalOps ms P T os).1 ∧
      (Toy.Coalesce.evalOps ms P T os).2 = (Toy.Coalesce.evalOps ms P S os).2 := by
  induction os with
  | nil => intro S T h _; exact ⟨h, rfl⟩
  | cons o os ih =>
    intro S T h hg
    simp only [Toy.Coalesce.evalOps] at hg ⊢
    rcases he : Toy.Coalesce.evalOp ms P S o with ⟨s1, _ | vs⟩ <;> rw [he] at hg <;>
      (try simp only at hg)
    · obtain ⟨h1, h2⟩ := h.evalOp ms P o (by rw [he]; exact hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      exact ⟨h1, rfl⟩
    · rcases he2 : Toy.Coalesce.evalOps ms P s1 os with ⟨s2, r2⟩
      have hs := step_evalOps ms P s1 os
      rw [he2] at hs hg
      have hg2 : Good3 D n s2.log := by cases r2 <;> exact hg
      obtain ⟨h1, h2⟩ := h.evalOp ms P o (by rw [he]; exact good3_step hs hg2)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      simp only
      obtain ⟨h3, h4⟩ := ih h1 (by rw [he2]; exact hg2)
      rw [he2] at h3 h4
      rw [pair_eta (Toy.Coalesce.evalOps ms P _ os) h4, he2]
      cases r2 <;> exact ⟨h3, rfl⟩

theorem writeInOrder (ms : MoveSem) (P : Prog) (loc : Nat) (os : List Operand) :
    ∀ {S T : St} (off : Nat), R3 p D n S T →
    Good3 D n (Toy.Coalesce.writeInOrder ms P S loc off os).log →
    R3 p D n (Toy.Coalesce.writeInOrder ms P S loc off os)
      (Toy.Coalesce.writeInOrder ms P T loc off os) := by
  induction os with
  | nil => intro S T off h _; exact h
  | cons o os ih =>
    intro S T off h hg
    simp only [Toy.Coalesce.writeInOrder] at hg ⊢
    rcases he : Toy.Coalesce.evalOp ms P S o with ⟨s1, _ | vs⟩ <;> rw [he] at hg <;>
      (try simp only at hg)
    · obtain ⟨h1, h2⟩ := h.evalOp ms P o (by rw [he]; exact hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      exact h1
    · have hg1 : Good3 D n s1.log :=
        good3_step ((step_writeCells _ _ _ _).trans (step_writeInOrder ms P _ loc _ os)) hg
      obtain ⟨h1, h2⟩ := h.evalOp ms P o (by rw [he]; exact hg1)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      simp only
      exact ih _ (h1.write _ _ _ _) hg

theorem cmpOp (h : R3 p D n S T) (ms : MoveSem) (P : Prog) (A : Layout) (a b : Operand)
    (f : Nat → Nat → Bool) (hg : Good3 D n (Toy.Coalesce.cmpOp ms P A S a b f).log) :
    R3 p D n (Toy.Coalesce.cmpOp ms P A S a b f) (Toy.Coalesce.cmpOp ms P A T a b f) := by
  unfold Toy.Coalesce.cmpOp at hg ⊢
  rcases he : Toy.Coalesce.evalOp ms P S a with ⟨s1, _ | va⟩ <;> rw [he] at hg <;>
    (try simp only at hg)
  · obtain ⟨h1, h2⟩ := h.evalOp ms P a (by rw [he]; exact hg)
    rw [he] at h1 h2
    rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
    exact h1
  · rcases va with _ | ⟨va, _ | ⟨w, ws⟩⟩
    · obtain ⟨h1, h2⟩ := h.evalOp ms P a (by rw [he]; exact good3_step (step_fail _ _) hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
      exact h1.fail _
    · simp only at hg
      rcases he2 : Toy.Coalesce.evalOp ms P s1 b with ⟨s2, r2⟩
      have hs := step_evalOp ms P s1 b
      rw [he2] at hs hg
      have hg2 : Good3 D n s2.log := by
        rcases r2 with _ | ⟨_ | ⟨vb, _ | ⟨w', ws'⟩⟩⟩
        · exact hg
        · exact good3_step (step_fail _ _) hg
        · simp only at hg
          generalize va.addr? A = xa at hg
          generalize vb.addr? A = xb at hg
          cases xa <;> cases xb <;> simp only at hg <;>
            first
            | exact good3_step (step_emit _ _) hg
            | exact good3_step (step_fail _ _) hg
        · exact good3_step (step_fail _ _) hg
      obtain ⟨h1, h2⟩ := h.evalOp ms P a (by rw [he]; exact good3_step hs hg2)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
      simp only
      obtain ⟨h3, h4⟩ := h1.evalOp ms P b (by rw [he2]; exact hg2)
      rw [he2] at h3 h4
      rw [pair_eta (Toy.Coalesce.evalOp ms P _ b) h4, he2]
      rcases r2 with _ | ⟨_ | ⟨vb, _ | ⟨w', ws'⟩⟩⟩
      · exact h3
      · exact h3.fail _
      · simp only
        generalize va.addr? A = xa
        generalize vb.addr? A = xb
        cases xa <;> cases xb <;> simp only <;>
          first
          | exact h3.emit _
          | exact h3.fail _
      · exact h3.fail _
    · obtain ⟨h1, h2⟩ := h.evalOp ms P a (by rw [he]; exact good3_step (step_fail _ _) hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
      exact h1.fail _

theorem execBasic (h : R3 p D n S T) (sem : Sem) (P : Prog) (A : Layout) (st : Stmt)
    (hg : Good3 D n (Toy.Coalesce.execBasic sem P A S st).log) :
    R3 p D n (Toy.Coalesce.execBasic sem P A S st) (Toy.Coalesce.execBasic sem P A T st) := by
  unfold Toy.Coalesce.execBasic at hg ⊢
  rw [h.status]
  by_cases hs : S.status ≠ .running
  · rw [ite_eq_left hs, ite_eq_left hs]; exact h
  · rw [ite_eq_right hs, ite_eq_right hs] at *
    cases st with
    | storageLive x =>
      simp only [h.inCall]
      split
      · exact h.fail _
      · exact h.allocate P x
    | storageDead x =>
      simp only [h.inCall]
      split
      · exact h.fail _
      · exact h.deallocate P x
    | assign lhs rhs =>
      simp only [h.resolve] at hg ⊢
      split
      · exact h.fail _
      · rename_i hlen
        simp only [hlen, ↓reduceIte] at hg
        generalize resolvePlace P S lhs = rr at hg ⊢
        cases rr with
        | none => exact h.fail _
        | some r =>
          simp only at hg ⊢
          generalize sem.assign = am at hg ⊢
          cases am with
          | atomic =>
            simp only at hg ⊢
            rcases he : Toy.Coalesce.evalOps sem.move P S rhs with ⟨s1, r1⟩
            rw [he] at hg
            have hg1 : Good3 D n s1.log := by
              cases r1 with
              | none => exact hg
              | some vs => exact good3_step (step_writeCells _ _ _ _) hg
            obtain ⟨h1, h2⟩ := h.evalOps sem.move P rhs (by rw [he]; exact hg1)
            rw [he] at h1 h2
            rw [pair_eta (Toy.Coalesce.evalOps sem.move P T rhs) h2]
            cases r1 with
            | none => exact h1
            | some vs => exact h1.write _ _ _ _
          | inOrder =>
            simp only at hg ⊢
            exact h.writeInOrder _ _ _ _ _ hg
    | store pl v =>
      simp only [h.resolve] at hg ⊢
      generalize resolvePlace P S pl = rr at hg ⊢
      cases rr with
      | none => exact h.fail _
      | some r =>
        simp only at hg ⊢
        split
        · rename_i hr1
          simp only [hr1, ↓reduceIte] at hg
          rcases hrs : readCells S r.base r.off 1 with ⟨s1, r1⟩
          rw [hrs] at hg
          have hfail : ∀ k, Good3 D n (s1.fail k).log → R3 p D n (readCells S r.base r.off 1).1
              (readCells T r.base r.off 1).1 ∧ (readCells T r.base r.off 1).2 = (readCells S r.base r.off 1).2 :=
            fun k hk => h.read r.base r.off 1 (by rw [hrs]; exact good3_step (step_fail _ _) hk)
          rcases r1 with _ | ⟨_ | ⟨v1, _ | ⟨w, ws⟩⟩⟩
          · obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact hg)
            rw [hrs] at h1 h2
            rw [pair_eta (readCells T r.base r.off 1) h2]
            exact h1
          · obtain ⟨h1, h2⟩ := hfail _ hg
            rw [hrs] at h1 h2
            rw [pair_eta (readCells T r.base r.off 1) h2]
            exact h1.fail _
          · cases v1 with
            | ptr l o =>
              simp only at hg ⊢
              rcases he : Toy.Coalesce.evalOp sem.move P s1 v with ⟨s2, r2⟩
              have hs := step_evalOp sem.move P s1 v
              rw [he] at hs hg
              have hg2 : Good3 D n s2.log := by
                cases r2 with
                | none => exact hg
                | some vs =>
                  simp only at hg
                  split at hg
                  · exact good3_step (step_writeCells _ _ _ _) hg
                  · exact good3_step (step_fail _ _) hg
              obtain ⟨h1, h2⟩ := h.read r.base r.off 1 (by rw [hrs]; exact good3_step hs hg2)
              rw [hrs] at h1 h2
              rw [pair_eta (readCells T r.base r.off 1) h2]
              simp only
              obtain ⟨h3, h4⟩ := h1.evalOp sem.move P v (by rw [he]; exact hg2)
              rw [he] at h3 h4
              rw [pair_eta (Toy.Coalesce.evalOp sem.move P _ v) h4]
              cases r2 with
              | none => exact h3
              | some vs =>
                simp only [h3.live]
                split
                · exact h3.write _ _ _ _
                · exact h3.fail _
            | _ =>
              obtain ⟨h1, h2⟩ := hfail _ hg
              rw [hrs] at h1 h2
              rw [pair_eta (readCells T r.base r.off 1) h2]
              exact h1.fail _
          · cases v1 <;>
            · obtain ⟨h1, h2⟩ := hfail _ hg
              rw [hrs] at h1 h2
              rw [pair_eta (readCells T r.base r.off 1) h2]
              exact h1.fail _
        · exact h.fail _
    | ptrEq a b => exact h.cmpOp _ _ _ _ _ _ hg
    | ptrInRange a b k => exact h.cmpOp _ _ _ _ _ _ hg
    | out o =>
      simp only at hg ⊢
      rcases he : Toy.Coalesce.evalOp sem.move P S o with ⟨s1, r1⟩
      rw [he] at hg
      have hg1 : Good3 D n s1.log := by
        cases r1 with
        | none => exact hg
        | some vs => exact good3_step (step_emit _ _) hg
      obtain ⟨h1, h2⟩ := h.evalOp sem.move P o (by rw [he]; exact hg1)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp sem.move P T o) h2]
      cases r1 with
      | none => exact h1
      | some vs => exact h1.emit _
    | call fn a => exact h.fail _
    | nop => exact h

theorem execCallee (sem : Sem) (P : Prog) (A : Layout) (b : List Stmt) :
    ∀ {S T : St}, R3 p D n S T → Good3 D n (Toy.Coalesce.execCallee sem P A S b).log →
      R3 p D n (Toy.Coalesce.execCallee sem P A S b) (Toy.Coalesce.execCallee sem P A T b) := by
  induction b with
  | nil => intro S T h _; exact h
  | cons st b ih =>
    intro S T h hg
    simp only [Toy.Coalesce.execCallee, List.foldl_cons] at hg ⊢
    exact ih (h.execBasic sem P A st (good3_step (step_execCallee sem P A _ b) hg)) hg

theorem callCopy (h : R3 p D n S T) (sem : Sem) (P : Prog) (A : Layout) (ms : MoveSem)
    (arg : Operand) (c : Callee)
    (hg : Good3 D n (match Toy.Coalesce.evalOp ms P S arg with
      | (s1, some vs) =>
        if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
        let s2 := Toy.Coalesce.allocate P s1 c.prm
        let s3 := writeCells s2 c.prm 0 vs
        let s4 := Toy.Coalesce.execCallee sem P A { s3 with inCall := true } c.body
        Toy.Coalesce.deallocate P { s4 with inCall := false } c.prm
      | (s1, none) => s1).log) :
    R3 p D n (match Toy.Coalesce.evalOp ms P S arg with
      | (s1, some vs) =>
        if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
        let s2 := Toy.Coalesce.allocate P s1 c.prm
        let s3 := writeCells s2 c.prm 0 vs
        let s4 := Toy.Coalesce.execCallee sem P A { s3 with inCall := true } c.body
        Toy.Coalesce.deallocate P { s4 with inCall := false } c.prm
      | (s1, none) => s1)
    (match Toy.Coalesce.evalOp ms P T arg with
      | (s1, some vs) =>
        if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
        let s2 := Toy.Coalesce.allocate P s1 c.prm
        let s3 := writeCells s2 c.prm 0 vs
        let s4 := Toy.Coalesce.execCallee sem P A { s3 with inCall := true } c.body
        Toy.Coalesce.deallocate P { s4 with inCall := false } c.prm
      | (s1, none) => s1) := by
  rcases he : Toy.Coalesce.evalOp ms P S arg with ⟨s1, r1⟩
  rw [he] at hg
  cases r1 with
  | none =>
    obtain ⟨h1, h2⟩ := h.evalOp ms P arg (by rw [he]; exact hg)
    rw [he] at h1 h2
    rw [pair_eta (Toy.Coalesce.evalOp ms P T arg) h2]
    exact h1
  | some vs =>
    simp only at hg ⊢
    have hg1 : Good3 D n s1.log := by
      split at hg
      · exact good3_step (step_fail _ _) hg
      · refine good3_stepT ?_ hg
        exact ((((step_allocate P s1 c.prm).trans (step_writeCells _ _ _ _)).toT.setInCall true).trans
          (step_execCallee _ _ _ _ _).toT |>.setInCall false).trans (step_deallocate _ _ _).toT
    obtain ⟨h1, h2⟩ := h.evalOp ms P arg (by rw [he]; exact hg1)
    rw [he] at h1 h2
    rw [pair_eta (Toy.Coalesce.evalOp ms P T arg) h2]
    simp only
    rw [h1.live]
    split
    · exact h1.fail _
    · rename_i hc
      simp only [hc, ↓reduceIte] at hg
      have hg2 := good3_step (step_deallocate _ _ _) hg
      exact ((((h1.allocate P _).write _ _ _ _).setInCall true).execCallee sem P A _
        hg2).setInCall false |>.deallocate P _

theorem execStmt (h : R3 p D n S T) (sem : Sem) (P : Prog) (A : Layout) (st : Stmt)
    (hg : Good3 D n (Toy.Coalesce.execStmt sem P A S st).log) :
    R3 p D n (Toy.Coalesce.execStmt sem P A S st) (Toy.Coalesce.execStmt sem P A T st) := by
  unfold Toy.Coalesce.execStmt at hg ⊢
  by_cases hs : S.status ≠ .running
  · have hs' : T.status ≠ .running := by rw [h.status]; exact hs
    rw [ite_eq_left hs, ite_eq_left hs']; exact h
  · have hs' : ¬ T.status ≠ .running := by rw [h.status]; exact hs
    rw [ite_eq_right hs] at hg
    rw [ite_eq_right hs, ite_eq_right hs']
    cases st with
    | call fn arg =>
      simp only at hg ⊢
      split at hg
      · rename_i _ q hm
        simp only [h.resolve] at hg ⊢
        generalize resolvePlace P S q = rr at hg ⊢
        cases rr with
        | none => exact h.fail _
        | some r =>
          simp only at hg ⊢
          split
          · exact h.fail _
          · rename_i hne
            simp only [hne, ↓reduceIte] at hg
            exact ((h.ctx _ true).execCallee sem P A _ hg).ctx none false
      · rename_i arg _ _ _
        exact h.callCopy sem P A sem.move arg (P.fn fn) hg
    | _ => exact h.execBasic sem P A _ hg

end R3


/-! ## During the call: the target parameter is an alias of the argument place -/

theorem evalOp_len (ms : MoveSem) (P : Prog) (s : St) (o : Operand) (vs : List Val)
    (h : (Toy.Coalesce.evalOp ms P s o).2 = some vs) : vs.length = o.len := by
  cases o with
  | lit k => simp only [Toy.Coalesce.evalOp, Option.some.injEq] at h; subst h; rfl
  | addrOf q =>
    simp only [Toy.Coalesce.evalOp] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases h
  | copy q =>
    simp only [Toy.Coalesce.evalOp] at h
    split at h
    · rename_i r hr
      rcases hrs : readCells s r.base r.off r.len with ⟨s', r'⟩
      rw [hrs] at h; simp only at h; subst h
      rw [readCells_len hrs, (resolvePlace_spec hr).2.2]; rfl
    · cases h
  | move q =>
    simp only [Toy.Coalesce.evalOp] at h
    split at h
    · rename_i r hr
      rcases hrs : readCells s r.base r.off r.len with ⟨s', _ | ws⟩
      · rw [hrs] at h; cases h
      · rw [hrs] at h
        simp only at h
        have : ws = vs := by split at h <;> simpa using h
        subst this
        rw [readCells_len hrs, (resolvePlace_spec hr).2.2]; rfl
    · cases h
  | load p len =>
    simp only [Toy.Coalesce.evalOp] at h
    split at h
    · rename_i r hr
      split at h
      · rcases hrs : readCells s r.base r.off 1 with ⟨s', _ | ws⟩
        · rw [hrs] at h; cases h
        · rw [hrs] at h
          rcases ws with _ | ⟨w, _ | ⟨w', ws'⟩⟩
          · cases h
          · cases w with
            | ptr l o =>
              simp only at h
              split at h
              · rcases hr2 : readCells s' l o len with ⟨s'', r''⟩
                rw [hr2] at h; simp only at h; subst h
                rw [readCells_len hr2]; rfl
              · cases h
            | _ => cases h
          · cases w <;> cases h
      · cases h
    · cases h

theorem evalOps_len (ms : MoveSem) (P : Prog) (os : List Operand) :
    ∀ (s : St) (vs : List Val), (Toy.Coalesce.evalOps ms P s os).2 = some vs →
      vs.length = (os.map Operand.len).sum := by
  induction os with
  | nil => intro s vs h; simp only [Toy.Coalesce.evalOps, Option.some.injEq] at h; subst h; rfl
  | cons o os ih =>
    intro s vs h
    simp only [Toy.Coalesce.evalOps] at h
    rcases he : Toy.Coalesce.evalOp ms P s o with ⟨s1, _ | v1⟩
    · rw [he] at h; cases h
    · rw [he] at h
      simp only at h
      rcases he2 : Toy.Coalesce.evalOps ms P s1 os with ⟨s2, _ | v2⟩
      · rw [he2] at h; cases h
      · rw [he2] at h
        simp only [Option.some.injEq] at h
        subst h
        have h1 := evalOp_len ms P s o v1 (by rw [he])
        have h2 := ih s1 v2 (by rw [he2])
        simp [h1, h2]

/-- Target view of a source place: a place based at the parameter `p` lies inside `q`. -/
def rho (p : Nat) (q : Place) (r : Place) : Place :=
  if r.base = p then ⟨q.base, q.off + r.off, r.len⟩ else r

theorem rho_len (p : Nat) (q r : Place) : (rho p q r).len = r.len := by
  unfold rho; split <;> rfl

theorem rho_of_ne {p : Nat} {q r : Place} (h : r.base ≠ p) : rho p q r = r := by
  unfold rho; simp [h]

/-- Cell `(l, o)` lies in the window of `q`. -/
def InWin (q : Place) (l o : Nat) : Prop := l = q.base ∧ q.off ≤ o ∧ o < q.off + q.len

/-- Static facts about the call site. -/
structure Ctx2 (P : Prog) (AT : Nat → Prop) (p : Nat) (q : Place) : Prop where
  pq : q.base ≠ p
  len : q.len = P.size p
  qb : q.off + q.len ≤ P.size q.base
  nat : ¬ AT p

/-- During the call: the source runs the callee with the parameter `p` allocated and holding the
argument, the target with `p` aliased to `q`. -/
structure R2 (AT : Nat → Prop) (p : Nat) (q : Place) (kk : Nat) (S T : St) : Prop where
  tick : T.tick = S.tick
  inCall : T.inCall = S.inCall
  status : T.status = S.status
  trace : T.trace = S.trace
  conf : ∀ c ∈ S.conflicts, c ∈ T.conflicts ∨ c.1 = p
  aliasS : S.alias = none
  aliasT : T.alias = some (p, q)
  live : ∀ z, z ≠ p → T.live z = S.live z
  liveSP : S.live p = true
  liveTP : T.live p = false
  liveQ : S.live q.base = true
  mem : ∀ l o, l ≠ p → ¬ InWin q l o → T.mem l o = S.mem l o
  memW : ∀ i, i < q.len → T.mem q.base (q.off + i) = S.mem p i
  ptrs : PtrsIn AT S
  inC : S.inCall = true
  tk : S.tick = kk

/-- No entry of tick `kk` made inside a callee touches a cell of `q`. -/
def Good2 (kk : Nat) (q : Place) (L : List Access) : Prop :=
  ∀ e ∈ L, e.tick = kk → e.inCall = true → ¬ InWin q e.loc e.off

theorem good2_prefix {kk : Nat} {q : Place} {L1 L2 : List Access} (hext : ∃ d, L2 = L1 ++ d)
    (h : Good2 kk q L2) : Good2 kk q L1 := by
  obtain ⟨d, rfl⟩ := hext
  exact fun e he => h e (List.mem_append_left _ he)

theorem good2_step {kk : Nat} {q : Place} {s t : St} (hs : Step s t) (h : Good2 kk q t.log) :
    Good2 kk q s.log := good2_prefix (Step.ext hs) h

namespace R2

variable {P : Prog} {AT : Nat → Prop} {p : Nat} {q : Place} {kk : Nat} {S T : St}

theorem fail (h : R2 AT p q kk S T) (k : Status) : R2 AT p q kk (S.fail k) (T.fail k) :=
  ⟨h.tick, h.inCall, rfl, h.trace, h.conf, h.aliasS, h.aliasT, h.live, h.liveSP, h.liveTP, h.liveQ,
    h.mem, h.memW, h.ptrs, h.inC, h.tk⟩

theorem emit (h : R2 AT p q kk S T) (e : Event) : R2 AT p q kk (S.emit e) (T.emit e) :=
  ⟨h.tick, h.inCall, h.status, by simp [St.emit, h.trace], h.conf, h.aliasS, h.aliasT, h.live,
    h.liveSP, h.liveTP, h.liveQ, h.mem, h.memW, h.ptrs, h.inC, h.tk⟩

theorem resolve (hc : Ctx2 P AT p q) (h : R2 AT p q kk S T) (pl : Place) :
    resolvePlace P T pl = (resolvePlace P S pl).map (rho p q) := by
  unfold resolvePlace
  rw [h.aliasS, h.aliasT]
  simp only
  by_cases hb : pl.base = p
  · simp only [hb, ↓reduceIte]
    have hq := hc.qb
    by_cases hl : pl.off + pl.len ≤ q.len
    · have h1 : (T.live q.base = true ∧ q.off + pl.off + pl.len ≤ P.size q.base) := by
        refine ⟨by rw [h.live _ hc.pq]; exact h.liveQ, by omega⟩
      have h2 : (S.live p = true ∧ pl.off + pl.len ≤ P.size p) := ⟨h.liveSP, by rw [← hc.len]; exact hl⟩
      simp only [hl, ↓reduceIte, h1, h2, and_self, Option.map_some]
      simp [rho, hb]
    · have h2 : ¬ (S.live p = true ∧ pl.off + pl.len ≤ P.size p) := fun h' => hl (by rw [hc.len]; exact h'.2)
      simp only [hl, ↓reduceIte, h2, Option.map_none]
  · simp only [hb, ↓reduceIte, h.live _ hb]
    split
    · simp [rho, hb]
    · rfl

theorem read (h : R2 AT p q kk S T) (r : Place) (n : Nat)
    (hn : r.base = p → r.off + n ≤ q.len) (hg : Good2 kk q (readCells S r.base r.off n).1.log) :
    R2 AT p q kk (readCells S r.base r.off n).1
        (readCells T (rho p q r).base (rho p q r).off n).1 ∧
      (readCells T (rho p q r).base (rho p q r).off n).2 = (readCells S r.base r.off n).2 := by
  obtain ⟨m, hm, hlog, hsim⟩ := readCells_sim S T r.base r.off (rho p q r).base (rho p q r).off n
  have hag : ∀ i, i < m →
      T.mem (rho p q r).base ((rho p q r).off + i) = S.mem r.base (r.off + i) := by
    intro i hi
    by_cases hb : r.base = p
    · have := hn hb
      simp only [rho, hb, ↓reduceIte]
      rw [Nat.add_assoc, h.memW (r.off + i) (by omega)]
    · rw [rho_of_ne hb]
      apply h.mem _ _ hb
      exact hg ⟨S.tick, S.inCall, r.base, r.off + i, .read⟩
        (by rw [hlog]; exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
        h.tk h.inC
  obtain ⟨h2, h3⟩ := hsim hag
  refine ⟨?_, h2⟩
  have hst := h3 h.status
  rw [readCells_frame S r.base r.off n, readCells_frame T (rho p q r).base (rho p q r).off n] at hst ⊢
  exact ⟨h.tick, h.inCall, hst, h.trace, h.conf, h.aliasS, h.aliasT, h.live, h.liveSP, h.liveTP,
    h.liveQ, h.mem, h.memW, h.ptrs, h.inC, h.tk⟩

theorem write (h : R2 AT p q kk S T) (k : AccKind) (ls os lt ot : Nat) (vs : List Val)
    (hcorr : (ls = p ∧ lt = q.base ∧ ot = q.off + os ∧ os + vs.length ≤ q.len) ∨
      (ls ≠ p ∧ lt = ls ∧ ot = os))
    (hg : Good2 kk q (writeCellsK k S ls os vs).log) (hv : ValsIn AT vs) :
    R2 AT p q kk (writeCellsK k S ls os vs) (writeCellsK k T lt ot vs) := by
  have hp := ptrsIn_writeCellsK k ls os vs h.ptrs hv
  rw [writeCellsK_eq] at hg hp ⊢
  rw [writeCellsK_eq]
  refine ⟨h.tick, h.inCall, h.status, h.trace, h.conf, h.aliasS, h.aliasT, h.live, h.liveSP,
    h.liveTP, h.liveQ, ?_, ?_, hp, h.inC, h.tk⟩
  · intro l o hl hw
    simp only
    rcases hcorr with ⟨e1, e2, e3, hb⟩ | ⟨hne, e2, e3⟩
    · subst lt ot
      have c1 : ¬ (l = q.base ∧ q.off + os ≤ o ∧ o < q.off + os + vs.length) := fun hc' =>
        hw ⟨hc'.1, by omega, by omega⟩
      have c2 : ¬ (l = ls ∧ os ≤ o ∧ o < os + vs.length) := fun hc' => hl (hc'.1.trans e1)
      rw [ite_eq_right c1, ite_eq_right c2]; exact h.mem l o hl hw
    · subst lt ot
      by_cases c : l = ls ∧ os ≤ o ∧ o < os + vs.length
      · rw [ite_eq_left c, ite_eq_left c]
      · rw [ite_eq_right c, ite_eq_right c]; exact h.mem l o hl hw
  · intro i hi
    simp only
    rcases hcorr with ⟨e1, e2, e3, hb⟩ | ⟨hne, e2, e3⟩
    · subst lt ot
      by_cases c : os ≤ i ∧ i < os + vs.length
      · rw [ite_eq_left ⟨rfl, by omega, by omega⟩, ite_eq_left ⟨e1.symm, c⟩]
        congr 1; omega
      · rw [ite_eq_right (fun hc' => c ⟨by omega, by omega⟩), ite_eq_right (fun hc' => c hc'.2)]
        exact h.memW i hi
    · subst lt ot
      have c1 : ¬ (q.base = ls ∧ os ≤ q.off + i ∧ q.off + i < os + vs.length) := by
        rintro ⟨h1, h2, h3⟩
        apply hg ⟨S.tick, S.inCall, ls, os + (q.off + i - os), k⟩
          (List.mem_append_right _ (List.mem_map.2 ⟨q.off + i - os, List.mem_range.2 (by omega), rfl⟩))
          h.tk h.inC
        exact ⟨h1.symm, show q.off ≤ os + (q.off + i - os) by omega,
          show os + (q.off + i - os) < q.off + q.len by omega⟩
      have c2 : ¬ (p = ls ∧ os ≤ i ∧ i < os + vs.length) := fun hc' => hne hc'.1.symm
      rw [ite_eq_right c1, ite_eq_right c2]; exact h.memW i hi

theorem evalOp (hc : Ctx2 P AT p q) (h : R2 AT p q kk S T) (ms : MoveSem) (hms : ms ≠ .deinit)
    (o : Operand) (hd : ∀ b, o.takesAddr b = true → AT b)
    (hg : Good2 kk q (Toy.Coalesce.evalOp ms P S o).1.log) :
    R2 AT p q kk (Toy.Coalesce.evalOp ms P S o).1 (Toy.Coalesce.evalOp ms P T o).1 ∧
      (Toy.Coalesce.evalOp ms P T o).2 = (Toy.Coalesce.evalOp ms P S o).2 := by
  have copyCase : ∀ pl, Good2 kk q (Toy.Coalesce.evalOp ms P S (.copy pl)).1.log →
      R2 AT p q kk (Toy.Coalesce.evalOp ms P S (.copy pl)).1
        (Toy.Coalesce.evalOp ms P T (.copy pl)).1 ∧
      (Toy.Coalesce.evalOp ms P T (.copy pl)).2 = (Toy.Coalesce.evalOp ms P S (.copy pl)).2 := by
    intro pl hg
    simp only [Toy.Coalesce.evalOp, h.resolve hc] at hg ⊢
    rcases hr : resolvePlace P S pl with _ | r
    · exact ⟨h.fail _, rfl⟩
    · rw [hr] at hg
      simp only [Option.map_some] at hg ⊢
      rw [rho_len]
      have hsp := resolvePlace_spec hr
      exact h.read r r.len (fun hb => by rw [hc.len, ← hb]; exact hsp.2.1) hg
  cases o with
  | lit k => exact ⟨h, rfl⟩
  | addrOf pl =>
    simp only [Toy.Coalesce.evalOp, h.resolve hc]
    rcases hr : resolvePlace P S pl with _ | r
    · exact ⟨h.fail _, rfl⟩
    · simp only [Option.map_some]
      have hb : r.base ≠ p := by
        rw [resolvePlace_base hr, h.aliasS]; simp only [aliasBase]
        intro he; exact hc.nat (he ▸ hd pl.base (by simp [Operand.takesAddr]))
      rw [rho_of_ne hb]; exact ⟨h, rfl⟩
  | copy pl => exact copyCase pl hg
  | move pl =>
    rw [evalOp_move_eq_copy ms hms] at hg ⊢
    rw [evalOp_move_eq_copy ms hms]
    exact copyCase pl hg
  | load pl len =>
    simp only [Toy.Coalesce.evalOp, h.resolve hc] at hg ⊢
    rcases hr : resolvePlace P S pl with _ | r
    · exact ⟨h.fail _, rfl⟩
    · rw [hr] at hg
      simp only [Option.map_some, rho_len] at hg ⊢
      have hsp := resolvePlace_spec hr
      split
      · rename_i hr1
        simp only [hr1, ↓reduceIte] at hg
        have hn : r.base = p → r.off + 1 ≤ q.len := fun hb => by
          rw [hc.len, ← hb]; have := hsp.2.1; omega
        rcases hrs : readCells S r.base r.off 1 with ⟨s', r1⟩
        rw [hrs] at hg
        have hg1 : Good2 kk q s'.log := by
          rcases r1 with _ | ⟨_ | ⟨v, _ | ⟨w, ws⟩⟩⟩
          · exact hg
          · exact good2_step (step_fail _ _) hg
          · cases v with
            | ptr l o =>
              simp only at hg
              split at hg
              · exact good2_step (step_readCells _ _ _ _) hg
              · exact good2_step (step_fail _ _) hg
            | _ => exact good2_step (step_fail _ _) hg
          · cases v <;> exact good2_step (step_fail _ _) hg
        obtain ⟨h1, h2⟩ := h.read r 1 hn (by rw [hrs]; exact hg1)
        rw [hrs] at h1 h2
        rw [pair_eta (readCells T _ _ 1) h2]
        rcases r1 with _ | ⟨_ | ⟨v, _ | ⟨w, ws⟩⟩⟩
        · exact ⟨h1, rfl⟩
        · exact ⟨h1.fail _, rfl⟩
        · cases v with
          | ptr l o =>
            simp only at hg ⊢
            have hl : l ≠ p := by
              have hv := (readCells_eq hrs).2.2.2 _ rfl
              have := valsIn_read h.ptrs r.base r.off 1
              rw [← hv] at this
              intro he; exact hc.nat (he ▸ this _ (by simp) l o rfl)
            rw [h1.live l hl]
            split
            · rename_i hcnd
              simp only [hcnd, and_self, ↓reduceIte] at hg
              have := h1.read ⟨l, o, len⟩ len (fun hb => absurd hb hl) hg
              rw [rho_of_ne (r := ⟨l, o, len⟩) hl] at this
              exact this
            · exact ⟨h1.fail _, rfl⟩
          | _ => exact ⟨h1.fail _, rfl⟩
        · cases v <;> exact ⟨h1.fail _, rfl⟩
      · exact ⟨h.fail _, rfl⟩

theorem evalOps (hc : Ctx2 P AT p q) (ms : MoveSem) (hms : ms ≠ .deinit) (os : List Operand) :
    ∀ {S T : St}, R2 AT p q kk S T → (∀ o ∈ os, ∀ b, o.takesAddr b = true → AT b) →
    Good2 kk q (Toy.Coalesce.evalOps ms P S os).1.log →
    R2 AT p q kk (Toy.Coalesce.evalOps ms P S os).1 (Toy.Coalesce.evalOps ms P T os).1 ∧
      (Toy.Coalesce.evalOps ms P T os).2 = (Toy.Coalesce.evalOps ms P S os).2 := by
  induction os with
  | nil => intro S T h _ _; exact ⟨h, rfl⟩
  | cons o os ih =>
    intro S T h hd hg
    simp only [Toy.Coalesce.evalOps] at hg ⊢
    rcases he : Toy.Coalesce.evalOp ms P S o with ⟨s1, _ | vs⟩ <;> rw [he] at hg <;>
      (try simp only at hg)
    · obtain ⟨h1, h2⟩ := h.evalOp hc ms hms o (hd o (by simp)) (by rw [he]; exact hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      exact ⟨h1, rfl⟩
    · rcases he2 : Toy.Coalesce.evalOps ms P s1 os with ⟨s2, r2⟩
      have hs := step_evalOps ms P s1 os
      rw [he2] at hs hg
      have hg2 : Good2 kk q s2.log := by cases r2 <;> exact hg
      obtain ⟨h1, h2⟩ := h.evalOp hc ms hms o (hd o (by simp)) (by rw [he]; exact good2_step hs hg2)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      simp only
      obtain ⟨h3, h4⟩ := ih h1 (fun o' ho' => hd o' (by simp [ho'])) (by rw [he2]; exact hg2)
      rw [he2] at h3 h4
      rw [pair_eta (Toy.Coalesce.evalOps ms P _ os) h4, he2]
      cases r2 <;> exact ⟨h3, rfl⟩

theorem writeInOrder (hc : Ctx2 P AT p q) (ms : MoveSem) (hms : ms ≠ .deinit) (os : List Operand) :
    ∀ {S T : St} (ls ofs lt oft : Nat), R2 AT p q kk S T →
    (∀ o ∈ os, ∀ b, o.takesAddr b = true → AT b) →
    ((ls = p ∧ lt = q.base ∧ oft = q.off + ofs ∧ ofs + (os.map Operand.len).sum ≤ q.len) ∨
      (ls ≠ p ∧ lt = ls ∧ oft = ofs)) →
    Good2 kk q (Toy.Coalesce.writeInOrder ms P S ls ofs os).log →
    R2 AT p q kk (Toy.Coalesce.writeInOrder ms P S ls ofs os)
      (Toy.Coalesce.writeInOrder ms P T lt oft os) := by
  induction os with
  | nil => intro S T ls ofs lt oft h _ _ _; exact h
  | cons o os ih =>
    intro S T ls ofs lt oft h hd hcorr hg
    simp only [Toy.Coalesce.writeInOrder] at hg ⊢
    rcases he : Toy.Coalesce.evalOp ms P S o with ⟨s1, _ | vs⟩ <;> rw [he] at hg <;>
      (try simp only at hg)
    · obtain ⟨h1, h2⟩ := h.evalOp hc ms hms o (hd o (by simp)) (by rw [he]; exact hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      exact h1
    · have hg1 : Good2 kk q s1.log :=
        good2_step ((step_writeCells _ _ _ _).trans (step_writeInOrder ms P _ ls _ os)) hg
      have hgw : Good2 kk q (writeCells s1 ls ofs vs).log :=
        good2_step (step_writeInOrder ms P _ ls _ os) hg
      obtain ⟨h1, h2⟩ := h.evalOp hc ms hms o (hd o (by simp)) (by rw [he]; exact hg1)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T o) h2]
      simp only
      have hlen := evalOp_len ms P S o vs (by rw [he])
      have hv := (ptrsIn_evalOp he h.ptrs
        (fun b hb => by rw [h.aliasS]; exact hd o (by simp) b hb)).2 vs rfl
      have hw := h1.write .write ls ofs lt oft vs (by
          rcases hcorr with ⟨e1, e2, e3, hb⟩ | hcorr
          · simp only [List.map_cons, List.sum_cons] at hb
            exact Or.inl ⟨e1, e2, e3, by omega⟩
          · exact Or.inr hcorr) hgw hv
      refine ih (ls := ls) (ofs := ofs + vs.length) (lt := lt) (oft := oft + vs.length) hw
        (fun o' ho' => hd o' (by simp [ho'])) ?_ hg
      rcases hcorr with ⟨e1, e2, e3, hb⟩ | ⟨hne, e2, e3⟩
      · simp only [List.map_cons, List.sum_cons] at hb
        exact Or.inl ⟨e1, e2, by omega, by omega⟩
      · exact Or.inr ⟨hne, e2, by omega⟩

theorem cmpOp (hc : Ctx2 P AT p q) (h : R2 AT p q kk S T) (ms : MoveSem) (hms : ms ≠ .deinit)
    (A : Layout) (a b : Operand) (f : Nat → Nat → Bool)
    (hda : ∀ x, a.takesAddr x = true → AT x) (hdb : ∀ x, b.takesAddr x = true → AT x)
    (hg : Good2 kk q (Toy.Coalesce.cmpOp ms P A S a b f).log) :
    R2 AT p q kk (Toy.Coalesce.cmpOp ms P A S a b f) (Toy.Coalesce.cmpOp ms P A T a b f) := by
  unfold Toy.Coalesce.cmpOp at hg ⊢
  rcases he : Toy.Coalesce.evalOp ms P S a with ⟨s1, _ | va⟩ <;> rw [he] at hg <;>
    (try simp only at hg)
  · obtain ⟨h1, h2⟩ := h.evalOp hc ms hms a hda (by rw [he]; exact hg)
    rw [he] at h1 h2
    rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
    exact h1
  · rcases va with _ | ⟨va, _ | ⟨w, ws⟩⟩
    · obtain ⟨h1, h2⟩ := h.evalOp hc ms hms a hda (by rw [he]; exact good2_step (step_fail _ _) hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
      exact h1.fail _
    · simp only at hg
      rcases he2 : Toy.Coalesce.evalOp ms P s1 b with ⟨s2, r2⟩
      have hs := step_evalOp ms P s1 b
      rw [he2] at hs hg
      have hg2 : Good2 kk q s2.log := by
        rcases r2 with _ | ⟨_ | ⟨vb, _ | ⟨w', ws'⟩⟩⟩
        · exact hg
        · exact good2_step (step_fail _ _) hg
        · simp only at hg
          generalize va.addr? A = xa at hg
          generalize vb.addr? A = xb at hg
          cases xa <;> cases xb <;> simp only at hg <;>
            first
            | exact good2_step (step_emit _ _) hg
            | exact good2_step (step_fail _ _) hg
        · exact good2_step (step_fail _ _) hg
      obtain ⟨h1, h2⟩ := h.evalOp hc ms hms a hda (by rw [he]; exact good2_step hs hg2)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
      simp only
      obtain ⟨h3, h4⟩ := h1.evalOp hc ms hms b hdb (by rw [he2]; exact hg2)
      rw [he2] at h3 h4
      rw [pair_eta (Toy.Coalesce.evalOp ms P _ b) h4, he2]
      rcases r2 with _ | ⟨_ | ⟨vb, _ | ⟨w', ws'⟩⟩⟩
      · exact h3
      · exact h3.fail _
      · simp only
        generalize va.addr? A = xa
        generalize vb.addr? A = xb
        cases xa <;> cases xb <;> simp only <;>
          first
          | exact h3.emit _
          | exact h3.fail _
      · exact h3.fail _
    · obtain ⟨h1, h2⟩ := h.evalOp hc ms hms a hda (by rw [he]; exact good2_step (step_fail _ _) hg)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp ms P T a) h2]
      exact h1.fail _

theorem execBasic (hc : Ctx2 P AT p q) (h : R2 AT p q kk S T) (sem : Sem)
    (hms : sem.move ≠ .deinit) (A : Layout) (st : Stmt) (hd : ∀ b, st.takesAddr b = true → AT b)
    (hg : Good2 kk q (Toy.Coalesce.execBasic sem P A S st).log) :
    R2 AT p q kk (Toy.Coalesce.execBasic sem P A S st) (Toy.Coalesce.execBasic sem P A T st) := by
  unfold Toy.Coalesce.execBasic at hg ⊢
  by_cases hs : S.status ≠ .running
  · have hs' : T.status ≠ .running := by rw [h.status]; exact hs
    rw [ite_eq_left hs, ite_eq_left hs']; exact h
  · have hs' : ¬ T.status ≠ .running := by rw [h.status]; exact hs
    rw [ite_eq_right hs] at hg
    rw [ite_eq_right hs, ite_eq_right hs']
    have hTc : T.inCall = true := h.inCall.trans h.inC
    cases st with
    | storageLive x => simp only [h.inC, hTc, ↓reduceIte]; exact h.fail _
    | storageDead x => simp only [h.inC, hTc, ↓reduceIte]; exact h.fail _
    | assign lhs rhs =>
      simp only [h.resolve hc] at hg ⊢
      split
      · exact h.fail _
      · rename_i hlen
        simp only [hlen, ↓reduceIte] at hg
        rcases hr : resolvePlace P S lhs with _ | r
        · exact h.fail _
        · rw [hr] at hg
          simp only [Option.map_some] at hg ⊢
          have hsp := resolvePlace_spec hr
          have hdo : ∀ o ∈ rhs, ∀ b, o.takesAddr b = true → AT b := fun o ho b hb =>
            hd b (by simp only [Stmt.takesAddr, List.any_eq_true]; exact ⟨o, ho, hb⟩)
          have hsum : (rhs.map Operand.len).sum = r.len := by
            rw [hsp.2.2]; exact Classical.byContradiction hlen
          have hcorr : ∀ L, L = r.len →
              ((r.base = p ∧ (rho p q r).base = q.base ∧ (rho p q r).off = q.off + r.off ∧
                r.off + L ≤ q.len) ∨
              (r.base ≠ p ∧ (rho p q r).base = r.base ∧ (rho p q r).off = r.off)) := by
            intro L hL
            by_cases hb : r.base = p
            · left
              have e : rho p q r = ⟨q.base, q.off + r.off, r.len⟩ := by simp [rho, hb]
              rw [e]
              refine ⟨hb, rfl, rfl, ?_⟩
              have := hsp.2.1
              rw [hb, ← hc.len] at this
              omega
            · right; rw [rho_of_ne hb]; exact ⟨hb, rfl, rfl⟩
          generalize sem.assign = am at hg ⊢
          cases am with
          | atomic =>
            simp only at hg ⊢
            rcases he : Toy.Coalesce.evalOps sem.move P S rhs with ⟨s1, r1⟩
            rw [he] at hg
            have hg1 : Good2 kk q s1.log := by
              cases r1 with
              | none => exact hg
              | some vs => exact good2_step (step_writeCells _ _ _ _) hg
            obtain ⟨h1, h2⟩ := h.evalOps hc sem.move hms rhs hdo (by rw [he]; exact hg1)
            rw [he] at h1 h2
            rw [pair_eta (Toy.Coalesce.evalOps sem.move P T rhs) h2]
            cases r1 with
            | none => exact h1
            | some vs =>
              have hlv := evalOps_len sem.move P rhs S vs (by rw [he])
              have hv := (ptrsIn_evalOps rhs he h.ptrs
                (fun o ho b hb => by rw [h.aliasS]; exact hdo o ho b hb)).2 vs rfl
              exact h1.write .write _ _ _ _ vs (hcorr vs.length (by rw [hlv, hsum])) hg hv
          | inOrder =>
            simp only at hg ⊢
            exact h.writeInOrder hc sem.move hms rhs _ _ _ _ hdo (hcorr _ hsum) hg
    | store pl v =>
      simp only [h.resolve hc] at hg ⊢
      rcases hr : resolvePlace P S pl with _ | r
      · exact h.fail _
      · rw [hr] at hg
        simp only [Option.map_some, rho_len] at hg ⊢
        have hsp := resolvePlace_spec hr
        have hdv : ∀ b, v.takesAddr b = true → AT b := fun b hb => hd b (by simpa [Stmt.takesAddr] using hb)
        split
        · rename_i hr1
          simp only [hr1, ↓reduceIte] at hg
          have hn : r.base = p → r.off + 1 ≤ q.len := fun hb => by
            rw [hc.len, ← hb]; have := hsp.2.1; omega
          rcases hrs : readCells S r.base r.off 1 with ⟨s1, r1⟩
          rw [hrs] at hg
          have hg1 : Good2 kk q s1.log := by
            rcases r1 with _ | ⟨_ | ⟨v1, _ | ⟨w, ws⟩⟩⟩
            · exact hg
            · exact good2_step (step_fail _ _) hg
            · cases v1 with
              | ptr l o =>
                simp only at hg
                rcases he : Toy.Coalesce.evalOp sem.move P s1 v with ⟨s2, r2⟩
                have hs := step_evalOp sem.move P s1 v
                rw [he] at hs hg
                refine good2_step hs ?_
                cases r2 with
                | none => exact hg
                | some vs =>
                  simp only at hg
                  split at hg
                  · exact good2_step (step_writeCells _ _ _ _) hg
                  · exact good2_step (step_fail _ _) hg
              | _ => exact good2_step (step_fail _ _) hg
            · cases v1 <;> exact good2_step (step_fail _ _) hg
          obtain ⟨h1, h2⟩ := h.read r 1 hn (by rw [hrs]; exact hg1)
          rw [hrs] at h1 h2
          rw [pair_eta (readCells T _ _ 1) h2]
          rcases r1 with _ | ⟨_ | ⟨v1, _ | ⟨w, ws⟩⟩⟩
          · exact h1
          · exact h1.fail _
          · cases v1 with
            | ptr l o =>
              simp only at hg ⊢
              have hl : l ≠ p := by
                have hv := (readCells_eq hrs).2.2.2 _ rfl
                have := valsIn_read h.ptrs r.base r.off 1
                rw [← hv] at this
                intro he; exact hc.nat (he ▸ this _ (by simp) l o rfl)
              rcases he : Toy.Coalesce.evalOp sem.move P s1 v with ⟨s2, r2⟩
              rw [he] at hg
              have hg2 : Good2 kk q s2.log := by
                cases r2 with
                | none => exact hg
                | some vs =>
                  simp only at hg
                  split at hg
                  · exact good2_step (step_writeCells _ _ _ _) hg
                  · exact good2_step (step_fail _ _) hg
              obtain ⟨h3, h4⟩ := h1.evalOp hc sem.move hms v hdv (by rw [he]; exact hg2)
              rw [he] at h3 h4
              rw [pair_eta (Toy.Coalesce.evalOp sem.move P _ v) h4]
              cases r2 with
              | none => exact h3
              | some vs =>
                simp only at hg ⊢
                rw [h3.live l hl]
                split
                · rename_i hcnd
                  simp only [hcnd, and_self, ↓reduceIte] at hg
                  have hv := (ptrsIn_evalOp he h1.ptrs
                    (fun b hb => by rw [h1.aliasS]; exact hdv b hb)).2 vs rfl
                  exact h3.write .write l o l o vs (Or.inr ⟨hl, rfl, rfl⟩) hg hv
                · exact h3.fail _
            | _ => exact h1.fail _
          · cases v1 <;> exact h1.fail _
        · exact h.fail _
    | ptrEq a b =>
      exact h.cmpOp hc sem.move hms A a b _ (fun x hx => hd x (by simp [Stmt.takesAddr, hx]))
        (fun x hx => hd x (by simp [Stmt.takesAddr, hx])) hg
    | ptrInRange a b k =>
      exact h.cmpOp hc sem.move hms A a b _ (fun x hx => hd x (by simp [Stmt.takesAddr, hx]))
        (fun x hx => hd x (by simp [Stmt.takesAddr, hx])) hg
    | out o =>
      simp only at hg ⊢
      rcases he : Toy.Coalesce.evalOp sem.move P S o with ⟨s1, r1⟩
      rw [he] at hg
      have hg1 : Good2 kk q s1.log := by
        cases r1 with
        | none => exact hg
        | some vs => exact good2_step (step_emit _ _) hg
      obtain ⟨h1, h2⟩ := h.evalOp hc sem.move hms o
        (fun x hx => hd x (by simpa [Stmt.takesAddr] using hx)) (by rw [he]; exact hg1)
      rw [he] at h1 h2
      rw [pair_eta (Toy.Coalesce.evalOp sem.move P T o) h2]
      cases r1 with
      | none => exact h1
      | some vs => exact h1.emit _
    | call fn a => exact h.fail _
    | nop => exact h

theorem execCallee (hc : Ctx2 P AT p q) (sem : Sem) (hms : sem.move ≠ .deinit) (A : Layout)
    (b : List Stmt) (hd : ∀ st ∈ b, ∀ x, st.takesAddr x = true → AT x) :
    ∀ {S T : St}, R2 AT p q kk S T → Good2 kk q (Toy.Coalesce.execCallee sem P A S b).log →
      R2 AT p q kk (Toy.Coalesce.execCallee sem P A S b) (Toy.Coalesce.execCallee sem P A T b) := by
  induction b with
  | nil => intro S T h _; exact h
  | cons st b ih =>
    intro S T h hg
    simp only [Toy.Coalesce.execCallee, List.foldl_cons] at hg ⊢
    exact ih (fun st' h' => hd st' (by simp [h']))
      (h.execBasic hc sem hms A st (hd st (by simp))
        (good2_step (step_execCallee sem P A _ b) hg)) hg

end R2


/-! ## The upgraded call -/

theorem rc_ok {s s1 : St} {l o n : Nat} {vs : List Val} (h : readCells s l o n = (s1, some vs)) :
    s1.mem = s.mem ∧ s1.live = s.live ∧ s1.alias = s.alias ∧ s1.tick = s.tick ∧
      s1.inCall = s.inCall ∧ s1.trace = s.trace ∧ s1.conflicts = s.conflicts ∧
      s1.status = s.status ∧ vs = (List.range n).map fun i => s.mem l (o + i) := by
  have hf := readCells_frame s l o n
  have hsp := readCells_spec s l o n
  rw [h] at hf hsp
  obtain ⟨h1, h2, -⟩ := hsp
  simp only at h1 h2
  have hall : ∀ i, i < n → s.mem l (o + i) ≠ .uninit := by
    refine Classical.byContradiction fun hn => ?_
    rw [ite_eq_right hn] at h1; cases h1
  rw [ite_eq_left hall] at h1 h2
  simp only at hf
  exact ⟨by rw [hf], by rw [hf], by rw [hf], by rw [hf], by rw [hf], by rw [hf], by rw [hf], h2,
    Option.some.inj h1⟩

theorem rc_none {s s1 : St} {l o n : Nat} (h : readCells s l o n = (s1, none)) :
    s1.status = .ub := by
  have hsp := readCells_spec s l o n
  rw [h] at hsp
  obtain ⟨h1, h2, -⟩ := hsp
  simp only at h1 h2
  by_cases hall : ∀ i, i < n → s.mem l (o + i) ≠ .uninit
  · rw [ite_eq_left hall] at h1; cases h1
  · rw [ite_eq_right hall] at h2; exact h2

theorem resolvePlace_noAlias {P : Prog} {s : St} (q : Place) (h : s.alias = none) :
    resolvePlace P s q =
      if s.live q.base = true ∧ q.off + q.len ≤ P.size q.base then some q else none := by
  unfold resolvePlace; rw [h]

theorem deallocate_status (P : Prog) (s : St) (x : Nat) : (deallocate P s x).status = s.status := by
  unfold deallocate; split
  · simp only [resetCells, writeCellsK_eq]
  · rfl

theorem mem_uninit_of_dead {P : Prog} {s : St} {l : Nat} (o : Nat) (h : LiveInv P s)
    (hl : s.live l = false) : s.mem l o = .uninit :=
  Classical.byContradiction fun hne => by
    have := (h l o hne).1; rw [hl] at this; cases this

theorem bridge (am : AssignMode) (P : Prog) (A : Layout) (fn : Nat) (q : Place) (k : Nat) (s : St)
    (hpq : q.base ≠ (P.fn fn).prm) (hnat : ¬ AddrTaken P (P.fn fn).prm)
    (htk : s.tick = k) (hal : s.alias = none)
    (hptr : PtrsIn (AddrTaken P) s)
    (hrunX : (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.copy q))).status = .running)
    (hgood : Good2 k q (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.copy q))).log)
    (hlS : LiveInv P (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.copy q))))
    (hlT : LiveInv P (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.move q)))) :
    R3 (P.fn fn).prm (InWin q) (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.copy q))).log.length
      (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.copy q)))
      (execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.move q))) := by
  have hsr : s.status = .running := by
    refine Classical.byContradiction fun hn => ?_
    rw [execStmt_of_not_running _ hn] at hrunX; exact hn hrunX
  generalize hX : execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.copy q)) = X at hrunX hgood hlS ⊢
  generalize hY : execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.move q)) = Y at hlT ⊢
  have hsrn : ¬ s.status ≠ .running := fun h => h hsr
  simp only [execStmt, hsrn, ↓reduceIte, evalOp, resolvePlace_noAlias q hal] at hX hY
  have hres : s.live q.base = true ∧ q.off + q.len ≤ P.size q.base := by
    refine Classical.byContradiction fun hres => ?_
    simp only [hres, ↓reduceIte] at hX
    rw [← hX] at hrunX; exact absurd hrunX (by simp [St.fail])
  simp only [hres, and_self, ↓reduceIte] at hX hY
  rcases hrc : readCells s q.base q.off q.len with ⟨s1, _ | vs⟩
  · rw [hrc] at hX; simp only at hX
    rw [← hX, rc_none hrc] at hrunX; cases hrunX
  rw [hrc] at hX
  simp only at hX
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := rc_ok hrc
  have hcond : ¬ (vs.length ≠ P.size (P.fn fn).prm ∨ s1.live (P.fn fn).prm = true) := by
    intro hcond
    rw [ite_eq_left hcond] at hX; rw [← hX] at hrunX; exact absurd hrunX (by simp [St.fail])
  rw [ite_eq_right hcond] at hX
  have hvl : vs.length = q.len := by rw [m9]; simp
  have hlen : q.len = P.size (P.fn fn).prm := by
    have := (not_or.1 hcond).1; omega
  have hlp : s.live (P.fn fn).prm = false := by
    have := (not_or.1 hcond).2; rw [m2] at this; simpa using this
  have hlenT : ¬ q.len ≠ P.size (P.fn fn).prm := fun h => h hlen
  simp only [hlenT, ↓reduceIte] at hY
  have hpn : (P.fn fn).prm < P.nloc := by
    refine Classical.byContradiction fun hpn => ?_
    have ha : allocate P s1 (P.fn fn).prm = s1.fail .ub := by simp [allocate, hpn]
    rw [ha] at hX
    rw [← hX, deallocate_status] at hrunX
    simp only at hrunX
    rw [execCallee_of_not_running] at hrunX
    · simp [writeCells, writeCellsK_eq, St.fail] at hrunX
    · simp [writeCells, writeCellsK_eq, St.fail]
  have hR2 : R2 (AddrTaken P) (P.fn fn).prm q k
      { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
      { s with alias := some ((P.fn fn).prm, q), inCall := true } := by
    have hptr3 : PtrsIn (AddrTaken P) (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs) :=
      ptrsIn_writeCellsK _ _ _ _ (ptrsIn_allocate _ _ _ (ptrsIn_congr m1 hptr))
        (by rw [m9]; exact valsIn_read hptr _ _ _)
    simp only [allocate, hpn, ↓reduceIte, resetCells, writeCells, writeCellsK_eq] at hptr3 ⊢
    refine ⟨m4.symm, rfl, m8.symm, m6.symm, ?_, m3.trans hal, rfl, ?_, ?_, hlp, ?_, ?_, ?_,
      hptr3, rfl, m4.trans htk⟩
    · intro c hc
      simp only [List.mem_append, List.mem_map] at hc
      rcases hc with hc | ⟨z, _, rfl⟩
      · exact Or.inl (m7 ▸ hc)
      · exact Or.inr rfl
    · intro z hz; simp [hz, m2]
    · simp
    · simp [hpq, m2, hres.1]
    · intro l o hl _
      simp [hl, m1]
    · intro i hi
      simp [hi, m9]
  have hc2 : Ctx2 P (AddrTaken P) (P.fn fn).prm q := ⟨hpq, hlen, hres.2, hnat⟩
  have hd : ∀ st ∈ (P.fn fn).body, ∀ x, st.takesAddr x = true → AddrTaken P x :=
    fun st hst x hx => (addrDisc_addrTaken P).2.1 fn st hst x hx
  subst hX hY
  have hg4 := good2_step (step_deallocate _ _ _) hgood
  have h4 := R2.execCallee hc2 ⟨.inPlaceCall, am⟩
    (show MoveSem.inPlaceCall ≠ MoveSem.deinit by decide) A (P.fn fn).body hd hR2 hg4
  generalize Toy.Coalesce.execCallee ⟨.inPlaceCall, am⟩ P A
    { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
    (P.fn fn).body = S4 at h4 hlS hrunX ⊢
  generalize Toy.Coalesce.execCallee ⟨.inPlaceCall, am⟩ P A
    { s with alias := some ((P.fn fn).prm, q), inCall := true } (P.fn fn).body = T4 at h4 hlT ⊢
  have hdl : deallocate P { S4 with inCall := false } (P.fn fn).prm =
      { resetCells { S4 with inCall := false } (P.fn fn).prm (P.size (P.fn fn).prm) with
        live := fun z => if z = (P.fn fn).prm then false else S4.live z } := by
    unfold deallocate; simp only [h4.liveSP, ↓reduceIte, resetCells, writeCellsK_eq]
  rw [hdl] at hlS ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
  · funext z
    by_cases hz : z = (P.fn fn).prm
    · simp [hz, h4.liveTP]
    · simp [hz, h4.live z hz]
  · simp [resetCells, writeCellsK_eq, h4.aliasS]
  · simp [resetCells, writeCellsK_eq, h4.tick]
  · simp [resetCells, writeCellsK_eq]
  · simp [resetCells, writeCellsK_eq, h4.status]
  · simp [resetCells, writeCellsK_eq, h4.trace]
  · simpa [resetCells, writeCellsK_eq] using h4.conf
  · intro l o hne
    refine ⟨?_, by simp⟩
    by_cases hl : l = (P.fn fn).prm
    · exfalso
      subst hl
      apply hne
      rw [mem_uninit_of_dead o hlS (by simp), mem_uninit_of_dead o hlT (by simp [h4.liveTP])]
    · by_cases hw : InWin q l o
      · exact hw
      · exfalso
        apply hne
        simp [resetCells, writeCellsK_eq, hl, h4.mem l o hl hw]


/-! ## Assembly -/

theorem runAt_running (sem : Sem) (P : Prog) (A : Layout) (h : (run sem P A).status = .running)
    (t : Nat) : (runAt sem P A t).status = .running := by
  refine Classical.byContradiction fun hn => ?_
  by_cases ht : t ≤ P.code.length
  · have e : run sem P A = (P.code.drop t).foldl (execTop sem P A) (runAt sem P A t) := by
      unfold run runAt
      conv => lhs; rw [← List.take_append_drop t P.code]
      rw [List.foldl_append]
    rw [e, foldl_execTop_of_not_running _ _ hn] at h
    exact hn h
  · rw [runAt_of_le _ _ _ _ (by omega)] at hn; exact hn h

theorem ftnr_skip (a : Access → Bool) (l o : Nat) (X Y : List Access) (hX : ∀ e ∈ X, a e = false) :
    firstTouchNotRead a l o (X ++ Y) = firstTouchNotRead a l o Y := by
  induction X with
  | nil => rfl
  | cons e X ih =>
    simp only [List.cons_append, firstTouchNotRead, hX e (by simp), Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    exact ih (fun e' he' => hX e' (by simp [he']))

theorem ftnr_congr (a b : Access → Bool) (l o : Nat) (X : List Access) (h : ∀ e ∈ X, a e = b e) :
    firstTouchNotRead a l o X = firstTouchNotRead b l o X := by
  induction X with
  | nil => rfl
  | cons e X ih =>
    simp only [firstTouchNotRead, h e (by simp)]
    rw [ih (fun e' he' => h e' (by simp [he']))]

theorem le_sum_range (f : Nat → Nat) : ∀ n z, z < n → f z ≤ ((List.range n).map f).sum := by
  intro n
  induction n with
  | zero => intro z hz; omega
  | succ n ih =>
    intro z hz
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : z < n
    · have := ih z h; omega
    · have : z = n := by omega
      subst this; omega

theorem size_of_ge (P : Prog) (z : Nat) (h : P.nloc ≤ z) : P.size z = 0 := by
  unfold Prog.size Prog.nloc at *
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- The layout `A` with local `p` moved above every other local. -/
def farLayout (P : Prog) (A : Layout) (p : Nat) : Layout :=
  fun z => if z = p then ((List.range P.nloc).map (fun y => A y + P.size y)).sum + 1 else A z

theorem disj_far (P : Prog) (A : Layout) (p z : Nat) (hz : z ≠ p) :
    Disj (farLayout P A p p) (P.size p) (farLayout P A p z) (P.size z) ∧
      Disj (farLayout P A p z) (P.size z) (farLayout P A p p) (P.size p) := by
  unfold Disj farLayout
  simp only [hz, ↓reduceIte]
  by_cases hn : z < P.nloc
  · have := le_sum_range (fun y => A y + P.size y) P.nloc z hn
    omega
  · have := size_of_ge P z (by omega)
    omega


theorem good2_of_calleeAvoids {L : List Access} {k : Nat} {q : Place} (h : CalleeAvoids L k q) :
    Good2 k q L := by
  intro e he h1 h2 hw
  unfold CalleeAvoids at h
  rw [List.all_eq_true] at h
  have := h e he
  obtain ⟨hw1, hw2, hw3⟩ := hw
  simp [h1, h2, hw1, hw2, hw3] at this

theorem main_sim (am : AssignMode) (P : Prog) (k fn : Nat) (q : Place) (hsite : CallSite P k fn q)
    (hnat : ¬ AddrTaken P (P.fn fn).prm) (A : Layout)
    (hrun : (run ⟨.inPlaceCall, am⟩ P A).status = .running)
    (hNR : NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ P A).log k false q)
    (hCA : CalleeAvoids (run ⟨.inPlaceCall, am⟩ P A).log k q) :
    (run ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A).status = (run ⟨.inPlaceCall, am⟩ P A).status ∧
      (run ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A).trace = (run ⟨.inPlaceCall, am⟩ P A).trace ∧
      ∀ c ∈ (run ⟨.inPlaceCall, am⟩ P A).conflicts,
        c ∈ (run ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A).conflicts ∨ c.1 = (P.fn fn).prm := by
  obtain ⟨hTk, hPk⟩ := code_getElem?_self P k _ hsite.1
  have hk : k < P.code.length := by
    rcases Nat.lt_or_ge k P.code.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hPk; cases hPk
  have hPk' : P.code[k] = .call fn (.copy q) := by
    rw [List.getElem?_eq_getElem hk] at hPk; exact Option.some.inj hPk
  have hTk' : (P.upgradeAt k).code[k]'(by rw [code_length]; exact hk) = .call fn (.move q) := by
    rw [List.getElem?_eq_getElem (by rw [code_length]; exact hk)] at hTk
    exact Option.some.inj hTk
  obtain ⟨htk, -, hal, -⟩ := runAt_frame ⟨.inPlaceCall, am⟩ P A k (by omega)
  have hptr := ptrsIn_runAt _ ⟨.inPlaceCall, am⟩ P A (addrDisc_addrTaken P) k
  have hS1 := runAt_succ ⟨.inPlaceCall, am⟩ P A k hk
  have hT1 := runAt_succ ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A k (by rw [code_length]; exact hk)
  rw [hPk'] at hS1
  rw [hTk', runAt_upgrade_le _ _ _ _ k (Nat.le_refl k), execTop_upgrade] at hT1
  obtain ⟨d, hd, hdt⟩ := runAt_log_extends ⟨.inPlaceCall, am⟩ P A (k + 1) P.code.length (by omega)
  rw [← run_eq_runAt] at hd
  have hS1run := runAt_running _ _ _ hrun (k + 1)
  have hgood : Good2 k q (runAt ⟨.inPlaceCall, am⟩ P A (k + 1)).log :=
    good2_prefix ⟨d, hd⟩ (good2_of_calleeAvoids hCA)
  have hlS := liveInv_runAt ⟨.inPlaceCall, am⟩ P A (k + 1)
  have hlT := liveInv_runAt ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A (k + 1)
  rw [hS1] at hS1run hgood hlS
  rw [hT1] at hlT
  have hB := bridge am P A fn q k _ (Ne.symm hsite.2) hnat htk hal hptr hS1run hgood
    (fun l o h => hlS l o h) (fun l o h => hlT l o h)
  have hB1 : R3 (P.fn fn).prm (InWin q) (runAt ⟨.inPlaceCall, am⟩ P A (k + 1)).log.length
      (runAt ⟨.inPlaceCall, am⟩ P A (k + 1)) (runAt ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A (k + 1)) := by
    rw [hS1, runAt_succ _ _ _ _ (by rw [code_length]; exact hk), hTk',
      runAt_upgrade_le _ _ _ _ k (Nat.le_refl k), execTop_upgrade]
    simp only [execTop]
    rw [hB.tick]
    exact hB.setTick _
  have hG3 : Good3 (InWin q) (runAt ⟨.inPlaceCall, am⟩ P A (k + 1)).log.length
      (run ⟨.inPlaceCall, am⟩ P A).log := by
    intro l o hw
    obtain ⟨hl, h1, h2⟩ := hw
    have := hNR (o - q.off) (by omega)
    rw [hd, ftnr_skip] at this
    · rw [hd, List.drop_left, hl, ← ftnr_congr _ _ _ _ _ (fun e he => ?_)]
      · rw [show q.off + (o - q.off) = o by omega] at this; exact this
      · have := hdt e he; simp [afterUse]; omega
    · intro e he
      have := (runAt_frame ⟨.inPlaceCall, am⟩ P A (k + 1) (by omega)).2.2.2 e he
      simp [afterUse]; omega
  have hstep : ∀ j, R3 (P.fn fn).prm (InWin q) (runAt ⟨.inPlaceCall, am⟩ P A (k + 1)).log.length
      (runAt ⟨.inPlaceCall, am⟩ P A (k + 1 + j)) (runAt ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A (k + 1 + j)) := by
    intro j
    induction j with
    | zero => exact hB1
    | succ j ih =>
      by_cases ht : k + 1 + j < P.code.length
      · rw [show k + 1 + (j + 1) = k + 1 + j + 1 by omega, runAt_succ _ _ _ _ ht,
          runAt_upgrade_succ _ _ _ _ _ ht (by omega)]
        obtain ⟨d', hd', -⟩ := runAt_log_extends ⟨.inPlaceCall, am⟩ P A (k + 1 + j + 1)
          P.code.length (by omega)
        rw [← run_eq_runAt, runAt_succ _ _ _ _ ht] at hd'
        have hg := good3_prefix ⟨d', hd'⟩ hG3
        have h2 := ih.execStmt ⟨.inPlaceCall, am⟩ P A P.code[k + 1 + j] hg
        simp only [execTop]
        rw [h2.tick]
        exact h2.setTick _
      · rw [runAt_of_le _ P A (k + 1 + (j + 1)) (by omega),
          runAt_of_le _ (P.upgradeAt k) A (k + 1 + (j + 1)) (by rw [code_length]; omega),
          ← runAt_of_le _ P A (k + 1 + j) (by omega),
          ← runAt_of_le _ (P.upgradeAt k) A (k + 1 + j) (by rw [code_length]; omega)]
        exact ih
  have hfin := hstep (P.code.length - (k + 1))
  rw [show k + 1 + (P.code.length - (k + 1)) = P.code.length by omega,
    ← run_eq_runAt, runAt_of_le _ (P.upgradeAt k) A P.code.length (Nat.le_of_eq (code_length P k))] at hfin
  exact ⟨hfin.status, hfin.trace, fun c hc => hfin.conf c hc⟩

end InPlace

open InPlace

/-- Under `MoveSem.inPlaceCall`, upgrading the call argument `copy q` of `call fn (copy q)` is a
refinement if, on every layout whose source run is neither excluded nor undefined, (a) no cell
of `q` is read after the call returns before it is re-initialized, (b) the callee does not access
any cell of `q` during the call, and (c) the callee's parameter local is not address-taken
anywhere in `P`. The parameter is a local of the caller's frame; condition (c) also excludes
pointers to it, and comparisons with its address, made outside the callee (copy passing allocates
the parameter during the call, in-place passing does not). -/
theorem upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_paramNotAddrTaken
    (am : AssignMode) (P : Prog) (k fn : Nat) (q : Place) (hsite : CallSite P k fn q)
    (ha : ∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ P A).log k false q)
    (hb : ∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
      CalleeAvoids (run ⟨.inPlaceCall, am⟩ P A).log k q)
    (hc : ¬ AddrTaken P (P.fn fn).prm) :
    Refines ⟨.inPlaceCall, am⟩ (P.upgradeAt k) ⟨.inPlaceCall, am⟩ P := by
  refine refines_of_running (fun A hA hrunAll => ?_)
  have hrun := hrunAll A
  have hg1 : outcome ⟨.inPlaceCall, am⟩ P (goodLayout P) =
      .done (run ⟨.inPlaceCall, am⟩ P (goodLayout P)).trace :=
    outcome_of_running (layoutOK_goodLayout_run _ P _) (hrunAll _)
  have hub : outcome ⟨.inPlaceCall, am⟩ P (goodLayout P) ≠ .ub := by rw [hg1]; simp
  have hbad := outcome_goodLayout_ne_badLayout ⟨.inPlaceCall, am⟩ P
  have hlog : (run ⟨.inPlaceCall, am⟩ P (goodLayout P)).log = (run ⟨.inPlaceCall, am⟩ P A).log :=
    (run_teq _ P _ A).log
  have hNR := ha _ hub hbad
  have hCA := hb _ hub hbad
  rw [hlog] at hNR hCA
  obtain ⟨hst, htr, hconf⟩ := main_sim am P k fn q hsite hc A hrun hNR hCA
  have hAA : ∀ l, AddrTaken P l → A l = farLayout P A (P.fn fn).prm l := by
    intro l hl
    have : l ≠ (P.fn fn).prm := fun h => hc (h ▸ hl)
    simp [farLayout, this]
  have hlay : run ⟨.inPlaceCall, am⟩ P A = run ⟨.inPlaceCall, am⟩ P (farLayout P A (P.fn fn).prm) :=
    run_layout hAA _ P (addrDisc_addrTaken P)
  have hTok := layoutOK_of_outcome_ne hA
  have hTst : (run ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A).status = .running := hst.trans hrun
  rw [outcome_of_running hTok hTst]
  have hok : layoutOK P (farLayout P A (P.fn fn).prm)
      (run ⟨.inPlaceCall, am⟩ P (farLayout P A (P.fn fn).prm)).conflicts = true := by
    rw [← hlay]
    simp only [layoutOK, List.all_eq_true, decide_eq_true_eq] at hTok ⊢
    intro c hcm
    have hne := run_conflicts_ne _ P A c hcm
    by_cases h1 : c.1 = (P.fn fn).prm
    · rw [h1]
      exact (disj_far P A _ c.2 (fun h => hne (h1.trans h.symm))).1
    · by_cases h2 : c.2 = (P.fn fn).prm
      · rw [h2]
        exact (disj_far P A _ c.1 h1).2
      · rcases hconf c hcm with hT | h
        · have := hTok c hT
          simp only [farLayout, h1, h2, ↓reduceIte]
          exact this
        · exact absurd h h1
  refine ⟨farLayout P A (P.fn fn).prm, ?_, by simp⟩
  rw [outcome_of_running hok (by rw [← hlay]; exact hrun), ← hlay, htr]

end Toy.Coalesce
