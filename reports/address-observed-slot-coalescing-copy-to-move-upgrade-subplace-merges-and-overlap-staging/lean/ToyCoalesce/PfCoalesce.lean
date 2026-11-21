import ToyCoalesce.Inv

/-!
# Proofs: coalescing merge forests
-/

namespace Toy.Coalesce

namespace Coal

/-! ## Forest facts -/

theorem parentOf_some {μ : Forest} {x : Nat} {e : Edge} (h : μ.parentOf x = some e) :
    e ∈ μ ∧ e.child = x := by
  unfold Forest.parentOf at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem parentOf_of_mem {μ : Forest} (hnd : (μ.map Edge.child).Nodup) {e : Edge} (he : e ∈ μ) :
    μ.parentOf e.child = some e := by
  unfold Forest.parentOf
  induction μ with
  | nil => simp at he
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp he with h | h
    · subst h; simp
    · have hne : a.child ≠ e.child := by
        intro hc; apply hnd.1; rw [hc]; exact List.mem_map.mpr ⟨e, h, rfl⟩
      have : (a.child == e.child) = false := by simpa using hne
      rw [this]; exact ih hnd.2 h

theorem resolveF_of_none {μ : Forest} {x : Nat} (h : μ.parentOf x = none) (k : Nat) :
    μ.resolveF k x = (x, 0) := by
  cases k with
  | zero => rfl
  | succ k => simp [Forest.resolveF, h]

theorem resolveF_succ_of_some {μ : Forest} {x : Nat} {e : Edge} (h : μ.parentOf x = some e)
    (k : Nat) :
    μ.resolveF (k + 1) x = ((μ.resolveF k e.parent).1, (μ.resolveF k e.parent).2 + e.off) := by
  simp [Forest.resolveF, h]

theorem resolveF_stable {μ : Forest} : ∀ (k x : Nat), μ.parentOf (μ.resolveF k x).1 = none →
    ∀ j, μ.resolveF (k + j) x = μ.resolveF k x := by
  intro k
  induction k with
  | zero =>
    intro x h j
    have h' : μ.parentOf x = none := h
    rw [Nat.zero_add, resolveF_of_none h' j, resolveF_of_none h' 0]
  | succ k ih =>
    intro x h j
    cases hx : μ.parentOf x with
    | none => rw [resolveF_of_none hx, resolveF_of_none hx]
    | some e =>
      rw [resolveF_succ_of_some hx] at h ⊢
      rw [show k + 1 + j = (k + j) + 1 by omega, resolveF_succ_of_some hx, ih e.parent h j]

theorem parentOf_eq_none_of_ge {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {x : Nat}
    (hx : P.nloc ≤ x) : μ.parentOf x = none := by
  cases h : μ.parentOf x with
  | none => rfl
  | some e =>
    obtain ⟨he, hc⟩ := parentOf_some h
    have := (hwf.2.1 e he).1
    omega

theorem parentOf_root {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (x : Nat) :
    μ.parentOf (μ.root x) = none := by
  by_cases hx : x < P.nloc
  · exact hwf.2.2.1 x hx
  · have h := parentOf_eq_none_of_ge hwf (by omega : P.nloc ≤ x)
    unfold Forest.root Forest.resolve; rw [resolveF_of_none h]; exact h

theorem resolve_root {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (x : Nat) :
    μ.resolve (μ.root x) = (μ.root x, 0) := by
  unfold Forest.resolve; rw [resolveF_of_none (parentOf_root hwf x)]

theorem root_root {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (x : Nat) :
    μ.root (μ.root x) = μ.root x := by
  show (μ.resolve (μ.root x)).1 = μ.root x
  rw [resolve_root hwf]

theorem offset_root {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (x : Nat) :
    μ.offset (μ.root x) = 0 := by
  show (μ.resolve (μ.root x)).2 = 0
  rw [resolve_root hwf]

theorem resolve_edge {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {e : Edge} (he : e ∈ μ) :
    μ.resolve e.child = ((μ.resolve e.parent).1, (μ.resolve e.parent).2 + e.off) := by
  obtain ⟨hnd, hedge, hroot, -, -⟩ := hwf
  have hpc := parentOf_of_mem hnd he
  obtain ⟨L, hL⟩ : ∃ L, μ.length = L + 1 :=
    ⟨μ.length - 1, by have := List.length_pos_of_mem he; omega⟩
  have h1 : μ.resolve e.child = ((μ.resolveF L e.parent).1, (μ.resolveF L e.parent).2 + e.off) := by
    unfold Forest.resolve; rw [hL, resolveF_succ_of_some hpc]
  have hnone : μ.parentOf (μ.resolveF L e.parent).1 = none := by
    have := hroot _ (hedge e he).1
    unfold Forest.root at this; rw [h1] at this; exact this
  have hst := resolveF_stable L e.parent hnone 1
  rw [h1]; unfold Forest.resolve; rw [hL, hst]

theorem root_edge {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {e : Edge} (he : e ∈ μ) :
    μ.root e.child = μ.root e.parent := by
  unfold Forest.root; rw [resolve_edge hwf he]

theorem resolveF_size {P : Prog} {μ : Forest} (hwf : ForestWF P μ) :
    ∀ k x, μ.parentOf (μ.resolveF k x).1 = none →
      (μ.resolveF k x).2 + P.size x ≤ P.size (μ.resolveF k x).1 := by
  intro k
  induction k with
  | zero => intro x _; simp [Forest.resolveF]
  | succ k ih =>
    intro x h
    cases hx : μ.parentOf x with
    | none => rw [resolveF_of_none hx]; simp
    | some e =>
      rw [resolveF_succ_of_some hx] at h ⊢
      obtain ⟨he, hc⟩ := parentOf_some hx
      have h1 := ih e.parent h
      have h2 := (hwf.2.1 e he).2.2.2
      rw [hc] at h2
      simp only at h1 ⊢
      omega

theorem offset_add_size_le {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (x : Nat) :
    μ.offset x + P.size x ≤ P.size (μ.root x) :=
  resolveF_size hwf μ.length x (parentOf_root hwf x)

theorem inClass_iff (μ : Forest) (x : Nat) :
    μ.inClass x = true ↔ ∃ e ∈ μ, e.child = x ∨ e.parent = x := by
  simp [Forest.inClass, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]

theorem lt_nloc_of_inClass {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {x : Nat}
    (h : μ.inClass x = true) : x < P.nloc := by
  obtain ⟨e, he, hc | hp⟩ := (inClass_iff μ x).1 h
  · rw [← hc]; exact (hwf.2.1 e he).1
  · rw [← hp]; exact (hwf.2.1 e he).2.1

theorem inClass_root {μ : Forest} {x : Nat} (h : μ.inClass x = true) :
    μ.inClass (μ.root x) = true := by
  rcases μ.resolveF_fst_eq_or_parent μ.length x with h1 | ⟨e, he, h1⟩
  · have : μ.root x = x := h1
    rw [this]; exact h
  · exact (inClass_iff μ _).2 ⟨e, he, Or.inr h1⟩

theorem root_of_not_inClass {μ : Forest} {x : Nat} (h : μ.inClass x = false) : μ.root x = x := by
  unfold Forest.root; rw [Forest.resolve_of_not_inClass μ x h]

theorem offset_of_not_inClass {μ : Forest} {x : Nat} (h : μ.inClass x = false) :
    μ.offset x = 0 := by
  unfold Forest.offset; rw [Forest.resolve_of_not_inClass μ x h]

theorem mem_nubNat (l : List Nat) (x : Nat) : x ∈ nubNat l ↔ x ∈ l := by
  induction l with
  | nil => simp [nubNat]
  | cons a l ih =>
    simp only [nubNat, List.mem_cons, List.mem_filter, ih, bne_iff_ne, ne_eq]
    by_cases h : x = a <;> simp [h]

theorem root_mem_roots {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {x : Nat}
    (h : μ.inClass x = true) : μ.root x ∈ μ.roots := by
  unfold Forest.roots
  rw [mem_nubNat, List.mem_map]
  obtain ⟨e, he, hc | hp⟩ := (inClass_iff μ x).1 h
  · exact ⟨e, he, by rw [hc]⟩
  · exact ⟨e, he, by rw [root_edge hwf he, hp]⟩

theorem mem_roots {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {r : Nat} (h : r ∈ μ.roots) :
    μ.inClass r = true ∧ μ.root r = r ∧ μ.offset r = 0 ∧ r < P.nloc := by
  unfold Forest.roots at h
  rw [mem_nubNat, List.mem_map] at h
  obtain ⟨e, he, rfl⟩ := h
  have hc : μ.inClass (μ.root e.child) = true :=
    inClass_root ((inClass_iff μ _).2 ⟨e, he, Or.inl rfl⟩)
  exact ⟨hc, root_root hwf _, offset_root hwf _, lt_nloc_of_inClass hwf hc⟩

/-- A local not in a class is the root of no other local. -/
theorem eq_of_root_eq_notClass {μ : Forest} {x l : Nat} (hx : μ.inClass x = false)
    (h : μ.root l = x) : l = x := by
  by_cases hl : l = x
  · exact hl
  · exact absurd h (Forest.root_ne_of_not_inClass μ x l hx hl)

theorem notClass_of_root_notClass {μ : Forest} {l : Nat} (h : μ.inClass (μ.root l) = false) :
    μ.inClass l = false := by
  cases hl : μ.inClass l
  · rfl
  · rw [inClass_root hl] at h; cases h

end Coal
namespace Coal

theorem iteP {c : Prop} [Decidable c] (h : c) {α : Sort _} {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem iteN {c : Prop} [Decidable c] (h : ¬ c) {α : Sort _} {a b : α} :
    (if c then a else b) = b := by simp [h]

end Coal

namespace Coal

/-! ## Values, layouts, the coalesced program -/

/-- Translation of a source value into the coalesced program. -/
def tr (μ : Forest) : Val → Val
  | .ptr l o => .ptr (μ.root l) (μ.offset l + o)
  | v => v

/-- The source layout induced by a target layout: each local at its root's address plus its
offset. -/
def hyb (μ : Forest) (A : Layout) : Layout := fun l => A (μ.root l) + μ.offset l

theorem obs_hyb (μ : Forest) (A : Layout) (v : Val) :
    Val.obs (hyb μ A) v = Val.obs A (tr μ v) := by
  cases v <;> simp [Val.obs, tr, hyb, Nat.add_assoc]

theorem addr_hyb (μ : Forest) (A : Layout) (v : Val) :
    Val.addr? (hyb μ A) v = Val.addr? A (tr μ v) := by
  cases v <;> simp [Val.addr?, tr, hyb, Nat.add_assoc]

theorem tr_ne_uninit {μ : Forest} {v : Val} (h : v ≠ .uninit) : tr μ v ≠ .uninit := by
  cases v <;> simp_all [tr]

theorem tr_uninit (μ : Forest) : tr μ .uninit = .uninit := rfl

theorem getD_map_tr (μ : Forest) (vs : List Val) (i : Nat) :
    (vs.map (tr μ)).getD i .uninit = tr μ (vs.getD i .uninit) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[i]? <;> rfl

theorem map_tr_replicate (μ : Forest) (n : Nat) :
    (List.replicate n Val.uninit).map (tr μ) = List.replicate n .uninit := by
  rw [List.map_replicate]; rfl

theorem evalOp_c (μ : Forest) (P : Prog) (ms : MoveSem) (s : St) (o : Operand) :
    evalOp ms (coalesce μ P) s o = evalOp ms P s o := by
  cases o <;> rfl

theorem evalOps_c (μ : Forest) (P : Prog) (ms : MoveSem) (os : List Operand) :
    ∀ s, evalOps ms (coalesce μ P) s os = evalOps ms P s os := by
  induction os with
  | nil => intro s; rfl
  | cons o os ih => intro s; simp only [evalOps, evalOp_c, ih]

theorem writeInOrder_c (μ : Forest) (P : Prog) (ms : MoveSem) (loc : Nat) (os : List Operand) :
    ∀ s off, writeInOrder ms (coalesce μ P) s loc off os = writeInOrder ms P s loc off os := by
  induction os with
  | nil => intro s off; rfl
  | cons o os ih => intro s off; simp only [writeInOrder, evalOp_c, ih]

theorem cmpOp_c (μ : Forest) (P : Prog) (ms : MoveSem) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) : cmpOp ms (coalesce μ P) A s a b f = cmpOp ms P A s a b f := by
  simp only [cmpOp, evalOp_c]

theorem execBasic_c (μ : Forest) (P : Prog) (sem : Sem) (A : Layout) (s : St) (st : Stmt) :
    execBasic sem (coalesce μ P) A s st = execBasic sem P A s st := by
  cases st <;> simp only [execBasic, evalOp_c, evalOps_c, writeInOrder_c, cmpOp_c] <;> rfl

theorem execCallee_c (μ : Forest) (P : Prog) (sem : Sem) (A : Layout) (s : St) (b : List Stmt) :
    execCallee sem (coalesce μ P) A s b = execCallee sem P A s b := by
  simp only [execCallee]
  congr 1
  funext s st
  exact execBasic_c μ P sem A s st

theorem allocate_c (μ : Forest) (P : Prog) (s : St) (x : Nat) :
    allocate (coalesce μ P) s x = allocate P s x := rfl

theorem deallocate_c (μ : Forest) (P : Prog) (s : St) (x : Nat) :
    deallocate (coalesce μ P) s x = deallocate P s x := rfl

theorem size_c (μ : Forest) (P : Prog) (x : Nat) : (coalesce μ P).size x = P.size x := rfl

theorem fn_c (μ : Forest) (P : Prog) (fn : Nat) :
    (coalesce μ P).fn fn = ⟨(P.fn fn).prm, (P.fn fn).body.map μ.coalesceStmt⟩ := by
  unfold Prog.fn coalesce
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P.fns[fn]? <;> rfl

theorem code_c (μ : Forest) (P : Prog) :
    (coalesce μ P).code = μ.roots.map Stmt.storageLive ++ P.code.map μ.coalesceStmt := by
  simp [coalesce, Prog.code, List.map_append, List.append_assoc]

theorem len_mapPlaces (μ : Forest) (o : Operand) : (o.mapPlaces μ.mapPlace).len = o.len := by
  cases o <;> rfl

/-! ## The scan state of `clobberFreeAux` -/

/-- The state of `clobberFreeAux` after a log: for each coalesced cell, the source cell of its last
data write. -/
def scan (μ : Forest) : List Access → (Nat × Nat → Option (Nat × Nat)) →
    (Nat × Nat → Option (Nat × Nat))
  | [], lw => lw
  | e :: es, lw =>
    match e.kind with
    | .read => scan μ es lw
    | .write => scan μ es fun t => if t = μ.tcell e.loc e.off then some (e.loc, e.off) else lw t
    | .reset => scan μ es lw

theorem scan_append (μ : Forest) (l1 l2 : List Access) (lw : Nat × Nat → Option (Nat × Nat)) :
    scan μ (l1 ++ l2) lw = scan μ l2 (scan μ l1 lw) := by
  induction l1 generalizing lw with
  | nil => rfl
  | cons e es ih => cases hk : e.kind <;> simp [scan, hk, ih]

theorem cfa_append (μ : Forest) (l1 l2 : List Access) (lw : Nat × Nat → Option (Nat × Nat)) :
    clobberFreeAux μ (l1 ++ l2) lw = (clobberFreeAux μ l1 lw && clobberFreeAux μ l2 (scan μ l1 lw)) := by
  induction l1 generalizing lw with
  | nil => simp [clobberFreeAux, scan]
  | cons e es ih => cases hk : e.kind <;> simp [clobberFreeAux, scan, hk, ih, Bool.and_assoc]

theorem nvc_prefix {μ : Forest} {l1 l2 : List Access} (h : NoValueClobber μ (l1 ++ l2)) :
    NoValueClobber μ l1 := by
  unfold NoValueClobber at h ⊢
  rw [cfa_append] at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem nvc_of_eq {μ : Forest} {l l1 : List Access} (h : NoValueClobber μ l)
    (he : ∃ d, l = l1 ++ d) : NoValueClobber μ l1 := by
  obtain ⟨d, rfl⟩ := he; exact nvc_prefix h

theorem nvc_suffix {μ : Forest} {l1 l2 : List Access} (h : NoValueClobber μ (l1 ++ l2)) :
    clobberFreeAux μ l2 (scan μ l1 fun _ => none) = true := by
  unfold NoValueClobber at h
  rw [cfa_append] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem scan_nonwrite (μ : Forest) (l : List Access) (h : ∀ e ∈ l, e.kind ≠ .write)
    (lw : Nat × Nat → Option (Nat × Nat)) : scan μ l lw = lw := by
  induction l generalizing lw with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hes : ∀ e ∈ es, e.kind ≠ .write := fun e' he' => h e' (by simp [he'])
    cases hk : e.kind
    · simp [scan, hk, ih hes]
    · exact absurd hk he
    · simp [scan, hk, ih hes]

theorem scan_block (μ : Forest) (tk : Nat) (ic : Bool) (loc off n : Nat) (k : AccKind)
    (lw : Nat × Nat → Option (Nat × Nat)) :
    scan μ ((List.range n).map fun i => (⟨tk, ic, loc, off + i, k⟩ : Access)) lw =
      if k = .write then
        (fun T => if T.1 = μ.root loc ∧ μ.offset loc + off ≤ T.2 ∧ T.2 < μ.offset loc + off + n then
          some (loc, T.2 - μ.offset loc) else lw T)
      else lw := by
  by_cases hk : k = .write
  · subst hk
    simp only [↓reduceIte]
    induction n with
    | zero =>
      funext T
      simp only [List.range_zero, List.map_nil, scan]
      rw [iteN (by omega)]
    | succ n ih =>
      rw [List.range_succ, List.map_append, scan_append, ih]
      funext T
      obtain ⟨a, b⟩ := T
      simp only [List.map_cons, List.map_nil, scan, Forest.tcell, Prod.mk.injEq]
      by_cases h1 : a = μ.root loc ∧ b = μ.offset loc + (off + n)
      · rw [iteP h1, iteP (by omega)]
        congr 2; omega
      · rw [iteN h1]
        by_cases h2 : a = μ.root loc ∧ μ.offset loc + off ≤ b ∧ b < μ.offset loc + off + n
        · rw [iteP h2, iteP (by omega)]
        · rw [iteN h2, iteN (by omega)]
  · rw [iteN hk]
    apply scan_nonwrite
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    exact hk

theorem cfa_reads (μ : Forest) (l : List Access) (lw : Nat × Nat → Option (Nat × Nat))
    (h : clobberFreeAux μ l lw = true) (hr : ∀ e ∈ l, e.kind = .read) :
    ∀ e ∈ l, ∀ c, lw (μ.tcell e.loc e.off) = some c → c = (e.loc, e.off) := by
  induction l with
  | nil => intro e he; simp at he
  | cons e es ih =>
    have hk := hr e (by simp)
    simp only [clobberFreeAux, hk, Bool.and_eq_true] at h
    intro e' he' c hc
    rcases List.mem_cons.1 he' with rfl | he'
    · rw [hc] at h
      simpa using h.1
    · exact ih h.2 (fun e'' h'' => hr e'' (by simp [h''])) e' he' c hc

end Coal
namespace Coal

/-! ## Frames: status monotonicity, unchanged liveness and allocation pairs -/

/-- `t` arises from `s` without recovering from failure, without changing liveness and without new
allocation pairs. -/
structure Fr (s t : St) : Prop where
  mono : t.status = .running → s.status = .running
  live : t.live = s.live
  conf : t.conflicts = s.conflicts

theorem Fr.refl (s : St) : Fr s s := ⟨id, rfl, rfl⟩

theorem Fr.trans {s t u : St} (h1 : Fr s t) (h2 : Fr t u) : Fr s u :=
  ⟨fun h => h1.mono (h2.mono h), h2.live.trans h1.live, h2.conf.trans h1.conf⟩

theorem fr_fail (s : St) : Fr s (s.fail .ub) := ⟨fun h => by simp [St.fail] at h, rfl, rfl⟩

theorem fr_emit (s : St) (e : Event) : Fr s (s.emit e) := ⟨id, rfl, rfl⟩

theorem wck_status (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).status = s.status := by rw [writeCellsK_eq]

theorem fr_writeCellsK (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    Fr s (writeCellsK k s loc off vs) := by
  rw [writeCellsK_eq]; exact ⟨id, rfl, rfl⟩

theorem fr_writeCells (s : St) (loc off : Nat) (vs : List Val) : Fr s (writeCells s loc off vs) :=
  fr_writeCellsK _ _ _ _ _

theorem readCells_status (s : St) (loc off n : Nat) :
    (readCells s loc off n).1.status = .running → s.status = .running := by
  intro h
  rw [(readCells_spec s loc off n).2.1] at h
  by_cases hc : ∀ i, i < n → s.mem loc (off + i) ≠ .uninit
  · rw [iteP hc] at h; exact h
  · rw [iteN hc] at h; cases h

theorem fr_readCells (s : St) (loc off n : Nat) : Fr s (readCells s loc off n).1 := by
  have hf := readCells_frame s loc off n
  refine ⟨readCells_status s loc off n, ?_, ?_⟩
  · rw [hf]
  · rw [hf]

/-- Running after a read means every read cell was initialized. -/
theorem readCells_running (s : St) (loc off n : Nat) (h : (readCells s loc off n).1.status = .running) :
    ∀ i, i < n → s.mem loc (off + i) ≠ .uninit := by
  rw [(readCells_spec s loc off n).2.1] at h
  by_cases hc : ∀ i, i < n → s.mem loc (off + i) ≠ .uninit
  · exact hc
  · rw [iteN hc] at h; cases h

theorem readCells_none_status {s s' : St} {loc off n : Nat} (h : readCells s loc off n = (s', none)) :
    s'.status = .ub := by
  have h1 := (readCells_spec s loc off n).1
  have h2 := (readCells_spec s loc off n).2.1
  rw [h] at h1 h2
  by_cases hc : ∀ i, i < n → s.mem loc (off + i) ≠ .uninit
  · rw [iteP hc] at h1; cases h1
  · rw [iteN hc] at h2; exact h2

theorem fr_evalOp (ms : MoveSem) (P : Prog) (s : St) (o : Operand) : Fr s (evalOp ms P s o).1 := by
  cases o with
  | lit n => exact Fr.refl s
  | addrOf q =>
    simp only [evalOp]; split
    · exact Fr.refl s
    · exact fr_fail _
  | copy q =>
    simp only [evalOp]; split
    · exact fr_readCells _ _ _ _
    · exact fr_fail _
  | move q =>
    simp only [evalOp]; split
    · rename_i r _
      have h := fr_readCells s r.base r.off r.len
      rcases hr : readCells s r.base r.off r.len with ⟨s', _ | vs⟩
      · rw [hr] at h; exact h
      · rw [hr] at h
        simp only
        split
        · exact h.trans (fr_writeCells _ _ _ _)
        · exact h
    · exact fr_fail _
  | load p len =>
    simp only [evalOp]; split
    · rename_i r _
      split
      · have h := fr_readCells s r.base r.off 1
        split
        next s' l o heq =>
          rw [heq] at h
          split
          · exact h.trans (fr_readCells _ _ _ _)
          · exact h.trans (fr_fail _)
        next s' x _ heq => rw [heq] at h; exact h.trans (fr_fail _)
        next s' heq => rw [heq] at h; exact h
      · exact fr_fail _
    · exact fr_fail _

theorem fr_evalOps (ms : MoveSem) (P : Prog) (s : St) (os : List Operand) :
    Fr s (evalOps ms P s os).1 := by
  induction os generalizing s with
  | nil => exact Fr.refl s
  | cons o os ih =>
    simp only [evalOps]
    have h := fr_evalOp ms P s o
    rcases hr : evalOp ms P s o with ⟨s', _ | vs⟩
    · rw [hr] at h; exact h
    · rw [hr] at h
      simp only
      have h2 := h.trans (ih s')
      rcases hr2 : evalOps ms P s' os with ⟨s'', _ | ws⟩ <;> rw [hr2] at h2 <;> exact h2

theorem fr_cmpOp (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) : Fr s (cmpOp ms P A s a b f) := by
  unfold cmpOp
  have h1 := fr_evalOp ms P s a
  split
  next s1 va heq =>
    rw [heq] at h1
    have h2 := h1.trans (fr_evalOp ms P s1 b)
    split
    next s2 vb heq2 =>
      rw [heq2] at h2
      split
      · exact h2.trans (fr_emit _ _)
      · exact h2.trans (fr_fail _)
    next s2 _ _ heq2 => rw [heq2] at h2; exact h2.trans (fr_fail _)
    next s2 heq2 => rw [heq2] at h2; exact h2
  next s1 _ _ heq => rw [heq] at h1; exact h1.trans (fr_fail _)
  next s1 heq => rw [heq] at h1; exact h1

theorem fr_writeInOrder (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat) (os : List Operand) :
    Fr s (writeInOrder ms P s loc off os) := by
  induction os generalizing s off with
  | nil => exact Fr.refl s
  | cons o os ih =>
    simp only [writeInOrder]
    have h := fr_evalOp ms P s o
    rcases hr : evalOp ms P s o with ⟨s', _ | vs⟩
    · rw [hr] at h; exact h
    · rw [hr] at h
      exact (h.trans (fr_writeCells _ _ _ _)).trans (ih _ _)

/-- Statements other than storage statements and calls. -/
def IsBasic : Stmt → Prop
  | .assign _ _ => True
  | .store _ _ => True
  | .ptrEq _ _ => True
  | .ptrInRange _ _ _ => True
  | .out _ => True
  | .nop => True
  | _ => False

theorem fr_execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : IsBasic st ∨ s.inCall = true) : Fr s (execBasic sem P A s st) := by
  unfold execBasic
  split
  · exact Fr.refl s
  · cases st with
    | storageLive x =>
      simp only [IsBasic, false_or] at h
      simp only [h, ↓reduceIte]; exact fr_fail _
    | storageDead x =>
      simp only [IsBasic, false_or] at h
      simp only [h, ↓reduceIte]; exact fr_fail _
    | assign lhs rhs =>
      simp only; split
      · exact fr_fail _
      · split
        · exact fr_fail _
        · split
          · have h := fr_evalOps sem.move P s rhs
            rcases hr : evalOps sem.move P s rhs with ⟨s', _ | vs⟩
            · rw [hr] at h; exact h
            · rw [hr] at h; exact h.trans (fr_writeCells _ _ _ _)
          · exact fr_writeInOrder _ _ _ _ _ _
    | store p v =>
      simp only; split
      · rename_i r _
        split
        · have h := fr_readCells s r.base r.off 1
          split
          next s1 l o heq =>
            rw [heq] at h
            have h2 := h.trans (fr_evalOp sem.move P s1 v)
            split
            next s2 vs heq2 =>
              rw [heq2] at h2
              split
              · exact h2.trans (fr_writeCells _ _ _ _)
              · exact h2.trans (fr_fail _)
            next s2 heq2 => rw [heq2] at h2; exact h2
          next s1 _ _ heq => rw [heq] at h; exact h.trans (fr_fail _)
          next s1 heq => rw [heq] at h; exact h
        · exact fr_fail _
      · exact fr_fail _
    | ptrEq a b => exact fr_cmpOp _ _ _ _ _ _ _
    | ptrInRange a b n => exact fr_cmpOp _ _ _ _ _ _ _
    | out o =>
      simp only
      have h := fr_evalOp sem.move P s o
      rcases hr : evalOp sem.move P s o with ⟨s', _ | vs⟩
      · rw [hr] at h; exact h
      · rw [hr] at h; exact h.trans (fr_emit _ _)
    | call fn a => exact fr_fail _
    | nop => exact Fr.refl s

theorem fr_execCallee (sem : Sem) (P : Prog) (A : Layout) (b : List Stmt) :
    ∀ s : St, s.inCall = true → Fr s (execCallee sem P A s b) := by
  induction b with
  | nil => intro s _; exact Fr.refl s
  | cons st b ih =>
    intro s hs
    simp only [execCallee, List.foldl_cons]
    have h1 := fr_execBasic sem P A s st (Or.inr hs)
    have hc : (execBasic sem P A s st).inCall = true := by
      rw [(step_execBasic sem P A s st).inCall]; exact hs
    exact h1.trans (ih _ hc)

theorem mono_execBasic {sem : Sem} {P : Prog} {A : Layout} {s : St} {st : Stmt}
    (h : (execBasic sem P A s st).status = .running) : s.status = .running := by
  by_cases hs : s.status = .running
  · exact hs
  · rw [execBasic_of_not_running st hs] at h; exact absurd h hs

theorem mono_execCallee {sem : Sem} {P : Prog} {A : Layout} {s : St} {b : List Stmt}
    (h : (execCallee sem P A s b).status = .running) : s.status = .running := by
  by_cases hs : s.status = .running
  · exact hs
  · rw [execCallee_of_not_running b hs] at h; exact absurd h hs

theorem mono_execStmt {sem : Sem} {P : Prog} {A : Layout} {s : St} {st : Stmt}
    (h : (execStmt sem P A s st).status = .running) : s.status = .running := by
  by_cases hs : s.status = .running
  · exact hs
  · rw [execStmt_of_not_running st hs] at h; exact absurd h hs

theorem allocate_status {P : Prog} {s : St} {x : Nat}
    (h : (allocate P s x).status = .running) : s.status = .running ∧ x < P.nloc := by
  unfold allocate at h
  split at h
  · rename_i hx
    rw [resetCells, wck_status] at h
    exact ⟨h, hx⟩
  · simp [St.fail] at h

theorem deallocate_status (P : Prog) (s : St) (x : Nat) :
    (deallocate P s x).status = s.status := by
  unfold deallocate
  split
  · simp only [resetCells, wck_status]
  · rfl

theorem execStmt_basic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : ∀ fn a, st ≠ .call fn a) : execStmt sem P A s st = execBasic sem P A s st := by
  unfold execStmt
  split
  · rename_i hs; rw [execBasic_of_not_running st hs]
  · cases st with
    | call fn a => exact absurd rfl (h fn a)
    | _ => rfl

end Coal
namespace Coal

/-! ## The simulation relation -/

/-- Simulation relation between a source state (run on the induced layout) and a coalesced state:
both running, equal traces and call context, aliases related by the place rewriting, equal liveness
of locals in no class, roots allocated, and the memory relation driven by the scan state `lw` of
the source log: every initialized source cell has a recorded last writer at its coalesced cell, and
a coalesced cell whose last writer is the source cell `c` holds the translation of `c`'s value
whenever `c` is initialized. -/
structure Rel (μ : Forest) (s t : St) : Prop where
  runS : s.status = .running
  runT : t.status = .running
  trace : t.trace = s.trace
  inCall : t.inCall = s.inCall
  alias : t.alias = s.alias.map (fun a => (a.1, μ.mapPlace a.2))
  aliasNC : ∀ a, s.alias = some a → μ.inClass a.1 = false
  liveNC : ∀ x, μ.inClass x = false → t.live x = s.live x
  liveR : ∀ r ∈ μ.roots, t.live r = true
  init : ∀ l o, s.mem l o ≠ .uninit → ∃ c, scan μ s.log (fun _ => none) (μ.tcell l o) = some c
  mem : ∀ l o, scan μ s.log (fun _ => none) (μ.tcell l o) = some (l, o) → s.mem l o ≠ .uninit →
    t.mem (μ.root l) (μ.offset l + o) = tr μ (s.mem l o)

theorem Rel.liveRoot {P : Prog} {μ : Forest} {s t : St} (hwf : ForestWF P μ) (hR : Rel μ s t)
    (l : Nat) (hl : s.live l = true) : t.live (μ.root l) = true := by
  cases hc : μ.inClass l
  · rw [root_of_not_inClass hc, hR.liveNC l hc]; exact hl
  · exact hR.liveR _ (root_mem_roots hwf hc)

theorem Rel.frame {μ : Forest} {s t s' t' : St} (hR : Rel μ s t) (hsS : s'.status = .running)
    (hsT : t'.status = .running) (htr : t'.trace = s'.trace)
    (hmS : s'.mem = s.mem) (hlS : s'.live = s.live) (haS : s'.alias = s.alias)
    (hiS : s'.inCall = s.inCall)
    (hmT : t'.mem = t.mem) (hlT : t'.live = t.live) (haT : t'.alias = t.alias)
    (hiT : t'.inCall = t.inCall)
    (hlog : scan μ s'.log (fun _ => none) = scan μ s.log (fun _ => none)) : Rel μ s' t' where
  runS := hsS
  runT := hsT
  trace := htr
  inCall := by rw [hiT, hiS, hR.inCall]
  alias := by rw [haT, haS, hR.alias]
  aliasNC := by rw [haS]; exact hR.aliasNC
  liveNC := by intro x hx; rw [hlT, hlS]; exact hR.liveNC x hx
  liveR := by intro r hr; rw [hlT]; exact hR.liveR r hr
  init := by intro l o h; rw [hlog]; rw [hmS] at h; exact hR.init l o h
  mem := by intro l o h1 h2; rw [hlog] at h1; rw [hmS] at h2 ⊢; rw [hmT]; exact hR.mem l o h1 h2

theorem readCells_fields (s : St) (loc off n : Nat) :
    (readCells s loc off n).1.mem = s.mem ∧ (readCells s loc off n).1.live = s.live ∧
    (readCells s loc off n).1.alias = s.alias ∧ (readCells s loc off n).1.trace = s.trace ∧
    (readCells s loc off n).1.inCall = s.inCall ∧
    (readCells s loc off n).1.conflicts = s.conflicts ∧ (readCells s loc off n).1.tick = s.tick := by
  have hf := readCells_frame s loc off n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hf]

theorem resolve_sim {P : Prog} {μ : Forest} {s t : St} (hwf : ForestWF P μ) (hR : Rel μ s t)
    {q r : Place} (h : resolvePlace P s q = some r) :
    resolvePlace P t (μ.mapPlace q) = some (μ.mapPlace r) := by
  have hspec := Inv.resolvePlace_spec h
  have hlive := hR.liveRoot hwf r.base hspec.1
  have hsz := offset_add_size_le hwf r.base
  have hfin : (if t.live (μ.mapPlace r).base = true ∧
      (μ.mapPlace r).off + (μ.mapPlace r).len ≤ P.size (μ.mapPlace r).base
      then some (μ.mapPlace r) else none) = some (μ.mapPlace r) := by
    apply iteP
    simp only [Forest.mapPlace]
    exact ⟨hlive, by omega⟩
  unfold resolvePlace at h ⊢
  rw [hR.alias]
  cases hal : s.alias with
  | none =>
    simp only [hal, Option.map] at h ⊢
    split at h
    · cases h; exact hfin
    · cases h
  | some a =>
    obtain ⟨prm, t0⟩ := a
    have hnc : μ.inClass prm = false := hR.aliasNC _ hal
    simp only [hal, Option.map] at h ⊢
    by_cases hb : q.base = prm
    · have hb' : (μ.mapPlace q).base = prm := by
        simp only [Forest.mapPlace, hb]; exact root_of_not_inClass hnc
      have ho : μ.offset q.base = 0 := by rw [hb]; exact offset_of_not_inClass hnc
      rw [iteP hb] at h
      rw [iteP hb']
      by_cases hl : q.off + q.len ≤ t0.len
      · rw [iteP hl] at h
        have hl' : (μ.mapPlace q).off + (μ.mapPlace q).len ≤ (μ.mapPlace t0).len := by
          simp only [Forest.mapPlace]; omega
        rw [iteP hl']
        simp only at h ⊢
        split at h
        · cases h
          simp only at hspec hlive hsz
          split
          · simp only [Forest.mapPlace, Option.some.injEq, Place.mk.injEq, true_and, and_true]
            omega
          · rename_i hc
            exfalso; apply hc
            simp only [Forest.mapPlace]
            exact ⟨hlive, by omega⟩
        · cases h
      · rw [iteN hl] at h; cases h
    · have hb' : ¬ (μ.mapPlace q).base = prm := by
        simp only [Forest.mapPlace]
        exact Forest.root_ne_of_not_inClass μ prm q.base hnc hb
      rw [iteN hb] at h
      rw [iteN hb']
      simp only at h ⊢
      split at h
      · cases h; exact hfin
      · cases h

theorem read_sim {μ : Forest} {s t : St} (hR : Rel μ s t) (loc off n : Nat)
    (hrun : (readCells s loc off n).1.status = .running)
    (hnvc : NoValueClobber μ (readCells s loc off n).1.log) :
    ∃ vs, (readCells s loc off n).2 = some vs ∧
      (readCells t (μ.root loc) (μ.offset loc + off) n).2 = some (vs.map (tr μ)) ∧
      Rel μ (readCells s loc off n).1 (readCells t (μ.root loc) (μ.offset loc + off) n).1 := by
  have hall := readCells_running s loc off n hrun
  obtain ⟨hv, -, m, -, hlog, -, hmn, -⟩ := readCells_spec s loc off n
  have hm' : m = n := hmn hall
  rw [hm'] at hlog
  rw [iteP hall] at hv
  rw [hlog] at hnvc
  have hcl := nvc_suffix hnvc
  have hreads := cfa_reads μ _ _ hcl (by
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    rfl)
  have hcell : ∀ i, i < n →
      t.mem (μ.root loc) (μ.offset loc + off + i) = tr μ (s.mem loc (off + i)) := by
    intro i hi
    obtain ⟨c, hc⟩ := hR.init loc (off + i) (hall i hi)
    have := hreads ⟨s.tick, s.inCall, loc, off + i, .read⟩
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩) c hc
    subst this
    rw [Nat.add_assoc]; exact hR.mem loc (off + i) hc (hall i hi)
  have hallT : ∀ i, i < n → t.mem (μ.root loc) (μ.offset loc + off + i) ≠ .uninit := by
    intro i hi; rw [hcell i hi]; exact tr_ne_uninit (hall i hi)
  obtain ⟨hvT, hstT, -⟩ := readCells_spec t (μ.root loc) (μ.offset loc + off) n
  rw [iteP hallT] at hvT hstT
  refine ⟨_, hv, ?_, ?_⟩
  · rw [hvT, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hcell i (List.mem_range.1 hi)
  · obtain ⟨m1, l1, a1, t1, i1, -, -⟩ := readCells_fields s loc off n
    obtain ⟨m2, l2, a2, t2, i2, -, -⟩ := readCells_fields t (μ.root loc) (μ.offset loc + off) n
    refine hR.frame hrun (hstT.trans hR.runT) (by rw [t1, t2, hR.trace]) m1 l1 a1 i1 m2 l2 a2 i2 ?_
    rw [hlog, scan_append, scan_block]
    simp

theorem write_sim {μ : Forest} {s t : St} (hR : Rel μ s t) (loc off : Nat) (vs : List Val) :
    Rel μ (writeCells s loc off vs)
      (writeCells t (μ.root loc) (μ.offset loc + off) (vs.map (tr μ))) := by
  unfold writeCells
  rw [writeCellsK_eq, writeCellsK_eq]
  have hscan : ∀ l' o', scan μ (s.log ++ (List.range vs.length).map
      fun i => (⟨s.tick, s.inCall, loc, off + i, .write⟩ : Access)) (fun _ => none) (μ.tcell l' o') =
      if μ.root l' = μ.root loc ∧ μ.offset loc + off ≤ μ.offset l' + o' ∧
          μ.offset l' + o' < μ.offset loc + off + vs.length
        then some (loc, μ.offset l' + o' - μ.offset loc)
        else scan μ s.log (fun _ => none) (μ.tcell l' o') := by
    intro l' o'
    rw [scan_append, scan_block]
    simp only [↓reduceIte]
    rfl
  refine ⟨hR.runS, hR.runT, hR.trace, hR.inCall, hR.alias, hR.aliasNC, hR.liveNC, hR.liveR, ?_, ?_⟩
  · intro l o hne
    simp only at hne
    rw [hscan]
    split
    · exact ⟨_, rfl⟩
    · rename_i hin2
      split at hne
      · rename_i hin
        obtain ⟨rfl, h1, h2⟩ := hin
        exact absurd ⟨rfl, by omega, by omega⟩ hin2
      · exact hR.init l o hne
  · intro l o hlw hne
    rw [hscan] at hlw
    simp only at hne ⊢
    rw [List.length_map]
    split at hlw
    · rename_i hin2
      simp only [Option.some.injEq, Prod.mk.injEq] at hlw
      obtain ⟨rfl, ho⟩ := hlw
      have hin : loc = loc ∧ off ≤ o ∧ o < off + vs.length := ⟨rfl, by omega, by omega⟩
      rw [iteP hin2, iteP hin, getD_map_tr]
      congr 2; omega
    · rename_i hin2
      have hnin : ¬ (l = loc ∧ off ≤ o ∧ o < off + vs.length) := by
        rintro ⟨rfl, h1, h2⟩; exact hin2 ⟨rfl, by omega, by omega⟩
      rw [iteN hnin] at hne ⊢
      rw [iteN hin2]
      exact hR.mem l o hlw hne

end Coal
namespace Coal

theorem nvc_step {μ : Forest} {s t : St} (h : NoValueClobber μ t.log) (hs : Step s t) :
    NoValueClobber μ s.log := by
  obtain ⟨d, hd, -⟩ := hs.log
  exact nvc_of_eq h ⟨d, hd⟩

theorem nvc_stepT {μ : Forest} {s t : St} (h : NoValueClobber μ t.log) (hs : StepT s t) :
    NoValueClobber μ s.log := by
  obtain ⟨d, hd, -⟩ := hs.log
  exact nvc_of_eq h ⟨d, hd⟩

theorem Rel.emit {μ : Forest} {s t : St} (hR : Rel μ s t) (e : Event) :
    Rel μ (s.emit e) (t.emit e) :=
  hR.frame hR.runS hR.runT (by simp [St.emit, hR.trace]) rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem fail_not_running (s : St) : (s.fail .ub).status ≠ .running := by simp [St.fail]

theorem evalOp_sim {P : Prog} {μ : Forest} {ms : MoveSem} {s t : St} (hwf : ForestWF P μ)
    (hR : Rel μ s t) (o : Operand)
    (hrun : (evalOp ms P s o).1.status = .running)
    (hnvc : NoValueClobber μ (evalOp ms P s o).1.log) :
    ∃ vs, (evalOp ms P s o).2 = some vs ∧
      (evalOp ms P t (o.mapPlaces μ.mapPlace)).2 = some (vs.map (tr μ)) ∧
      Rel μ (evalOp ms P s o).1 (evalOp ms P t (o.mapPlaces μ.mapPlace)).1 := by
  cases o with
  | lit n => exact ⟨_, rfl, rfl, hR⟩
  | addrOf q =>
    cases hres : resolvePlace P s q with
    | none => simp [evalOp, hres, St.fail] at hrun
    | some r =>
      have ht := resolve_sim hwf hR hres
      simp only [evalOp, Operand.mapPlaces, hres, ht]
      exact ⟨_, rfl, rfl, hR⟩
  | copy q =>
    cases hres : resolvePlace P s q with
    | none => simp [evalOp, hres, St.fail] at hrun
    | some r =>
      have ht := resolve_sim hwf hR hres
      simp only [evalOp, Operand.mapPlaces, hres, ht] at hrun hnvc ⊢
      exact read_sim hR r.base r.off r.len hrun hnvc
  | move q =>
    cases hres : resolvePlace P s q with
    | none => simp [evalOp, hres, St.fail] at hrun
    | some r =>
      have ht := resolve_sim hwf hR hres
      simp only [evalOp, Operand.mapPlaces, hres, ht] at hrun hnvc ⊢
      simp only [Forest.mapPlace]
      rcases hrd : readCells s r.base r.off r.len with ⟨s', _ | vs⟩
      · rw [hrd] at hrun; simp only at hrun
        rw [readCells_none_status hrd] at hrun; cases hrun
      · rw [hrd] at hrun hnvc
        try simp only at hrun hnvc ⊢
        have hrun' : (readCells s r.base r.off r.len).1.status = .running := by
          rw [hrd]; split at hrun
          · rwa [writeCells, wck_status] at hrun
          · exact hrun
        have hnvc' : NoValueClobber μ (readCells s r.base r.off r.len).1.log := by
          rw [hrd]; split at hnvc
          · exact nvc_step hnvc (step_writeCells s' _ _ _)
          · exact hnvc
        obtain ⟨vs', hvs', hvt, hrel⟩ := read_sim hR r.base r.off r.len hrun' hnvc'
        rw [hrd] at hvs' hrel
        simp only [Option.some.injEq] at hvs'
        subst hvs'
        rcases hrt : readCells t (μ.root r.base) (μ.offset r.base + r.off) r.len with ⟨t', ovt⟩
        rw [hrt] at hvt hrel
        simp only at hvt hrel
        subst hvt
        simp only
        by_cases hd : ms = .deinit
        · simp only [hd, ↓reduceIte]
          refine ⟨vs, rfl, rfl, ?_⟩
          have := write_sim hrel r.base r.off (List.replicate r.len .uninit)
          rw [map_tr_replicate] at this
          exact this
        · simp only [hd, ↓reduceIte]
          exact ⟨vs, rfl, rfl, hrel⟩
  | load p len =>
    cases hres : resolvePlace P s p with
    | none => simp [evalOp, hres, St.fail] at hrun
    | some r =>
      have ht := resolve_sim hwf hR hres
      simp only [evalOp, Operand.mapPlaces, hres, ht] at hrun hnvc ⊢
      simp only [Forest.mapPlace]
      by_cases hlen : r.len = 1
      · simp only [hlen, ↓reduceIte] at hrun hnvc ⊢
        rcases hrd : readCells s r.base r.off 1 with ⟨s1, _ | vs⟩
        · rw [hrd] at hrun; simp only at hrun
          rw [readCells_none_status hrd] at hrun; cases hrun
        · rw [hrd] at hrun hnvc
          rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
          · simp only at hrun; exact absurd hrun (fail_not_running _)
          · cases v with
            | ptr l o =>
              simp only at hrun hnvc
              by_cases hc : s1.live l = true ∧ o + len ≤ P.size l
              · rw [iteP hc] at hrun hnvc
                have hrun1 : (readCells s r.base r.off 1).1.status = .running := by
                  rw [hrd]; exact readCells_status _ _ _ _ hrun
                have hnvc1 : NoValueClobber μ (readCells s r.base r.off 1).1.log := by
                  rw [hrd]; exact nvc_step hnvc (step_readCells s1 l o len)
                obtain ⟨vs1, hvs1, hvt1, hrel1⟩ := read_sim hR r.base r.off 1 hrun1 hnvc1
                rw [hrd] at hvs1 hrel1
                simp only [Option.some.injEq] at hvs1
                subst hvs1
                rcases hrt : readCells t (μ.root r.base) (μ.offset r.base + r.off) 1 with ⟨t1, ovt⟩
                rw [hrt] at hvt1 hrel1
                simp only at hvt1 hrel1
                subst hvt1
                simp only [List.map, tr]
                have hcT : t1.live (μ.root l) = true ∧ μ.offset l + o + len ≤ P.size (μ.root l) :=
                  ⟨hrel1.liveRoot hwf l hc.1, by have := offset_add_size_le hwf l; omega⟩
                rw [iteP hc, iteP hcT]
                exact read_sim hrel1 l o len hrun hnvc
              · rw [iteN hc] at hrun; exact absurd hrun (fail_not_running _)
            | _ => simp only at hrun; exact absurd hrun (fail_not_running _)
          · simp only at hrun; exact absurd hrun (fail_not_running _)
      · simp only [hlen, ↓reduceIte] at hrun; exact absurd hrun (fail_not_running _)

theorem evalOps_sim {P : Prog} {μ : Forest} {ms : MoveSem} (hwf : ForestWF P μ)
    (os : List Operand) : ∀ {s t : St}, Rel μ s t →
    (evalOps ms P s os).1.status = .running → NoValueClobber μ (evalOps ms P s os).1.log →
    ∃ vs, (evalOps ms P s os).2 = some vs ∧
      (evalOps ms P t (os.map (Operand.mapPlaces μ.mapPlace))).2 = some (vs.map (tr μ)) ∧
      Rel μ (evalOps ms P s os).1 (evalOps ms P t (os.map (Operand.mapPlaces μ.mapPlace))).1 := by
  induction os with
  | nil => intro s t hR _ _; exact ⟨[], rfl, rfl, hR⟩
  | cons o os ih =>
    intro s t hR hrun hnvc
    simp only [evalOps, List.map_cons] at hrun hnvc ⊢
    rcases he : evalOp ms P s o with ⟨s1, _ | vs⟩
    · rw [he] at hrun hnvc
      simp only at hrun hnvc
      obtain ⟨vs, hvs, -⟩ := evalOp_sim hwf hR o (by rw [he]; exact hrun) (by rw [he]; exact hnvc)
      rw [he] at hvs; cases hvs
    · rw [he] at hrun hnvc
      simp only at hrun hnvc
      rcases he2 : evalOps ms P s1 os with ⟨s2, ows⟩
      rw [he2] at hrun hnvc
      have hrun2 : (evalOps ms P s1 os).1.status = .running := by
        rw [he2]; cases ows <;> exact hrun
      have hnvc2 : NoValueClobber μ (evalOps ms P s1 os).1.log := by
        rw [he2]; cases ows <;> exact hnvc
      have hrun1 : (evalOp ms P s o).1.status = .running := by
        rw [he]; exact (fr_evalOps ms P s1 os).mono hrun2
      have hnvc1 : NoValueClobber μ (evalOp ms P s o).1.log := by
        rw [he]; exact nvc_step hnvc2 (step_evalOps ms P s1 os)
      obtain ⟨vs', hvs', hvt, hrel⟩ := evalOp_sim hwf hR o hrun1 hnvc1
      rw [he] at hvs' hrel
      simp only [Option.some.injEq] at hvs'
      subst hvs'
      rcases het : evalOp ms P t (o.mapPlaces μ.mapPlace) with ⟨t1, ovt⟩
      rw [het] at hvt hrel
      simp only at hvt hrel
      subst hvt
      obtain ⟨ws', hws', hwt, hrel2⟩ := ih hrel hrun2 hnvc2
      rw [he2] at hws' hrel2
      simp only at hws'
      subst hws'
      rcases het2 : evalOps ms P t1 (os.map (Operand.mapPlaces μ.mapPlace)) with ⟨t2, owt⟩
      rw [het2] at hwt hrel2
      simp only at hwt hrel2
      subst hwt
      simp only [he2, het2]
      exact ⟨_, rfl, by simp [List.map_append], hrel2⟩

theorem evalOp_none {ms : MoveSem} {P : Prog} {s s' : St} {o : Operand}
    (h : evalOp ms P s o = (s', none)) : s'.status = .ub := by
  cases o with
  | lit n => simp [evalOp] at h
  | addrOf q =>
    simp only [evalOp] at h
    split at h
    · cases h
    · cases h; rfl
  | copy q =>
    simp only [evalOp] at h
    split at h
    · exact readCells_none_status h
    · cases h; rfl
  | move q =>
    simp only [evalOp] at h
    split at h
    · split at h
      · split at h <;> cases h
      · next heq => cases h; exact readCells_none_status heq
    · cases h; rfl
  | load p len =>
    simp only [evalOp] at h
    split at h
    · split at h
      · split at h
        · split at h
          · exact readCells_none_status h
          · cases h; rfl
        · cases h; rfl
        · next heq => cases h; exact readCells_none_status heq
      · cases h; rfl
    · cases h; rfl

theorem cmpOp_running {ms : MoveSem} {P : Prog} {A : Layout} {s : St} {a b : Operand}
    {f : Nat → Nat → Bool} (h : (cmpOp ms P A s a b f).status = .running) :
    ∃ s1 va s2 vb x y, evalOp ms P s a = (s1, some [va]) ∧ evalOp ms P s1 b = (s2, some [vb]) ∧
      va.addr? A = some x ∧ vb.addr? A = some y ∧ cmpOp ms P A s a b f = s2.emit (.cmp (f x y)) := by
  unfold cmpOp at h ⊢
  rcases he : evalOp ms P s a with ⟨s1, _ | va⟩
  · rw [he] at h; simp only at h; rw [evalOp_none he] at h; cases h
  · rw [he] at h
    rcases va with _ | ⟨va, _ | ⟨w, ws⟩⟩
    · exact absurd h (fail_not_running _)
    · simp only at h ⊢
      rcases he2 : evalOp ms P s1 b with ⟨s2, _ | vb⟩
      · rw [he2] at h; simp only at h; rw [evalOp_none he2] at h; cases h
      · rw [he2] at h
        rcases vb with _ | ⟨vb, _ | ⟨w, ws⟩⟩
        · exact absurd h (fail_not_running _)
        · simp only at h ⊢
          cases hx : va.addr? A with
          | none => rw [hx] at h; exact absurd h (fail_not_running _)
          | some x =>
            cases hy : vb.addr? A with
            | none => rw [hx, hy] at h; exact absurd h (fail_not_running _)
            | some y =>
              refine ⟨s1, va, s2, vb, x, y, ?_, ?_, ?_, ?_, ?_⟩
              · first | rfl | exact he
              · first | rfl | exact he2
              · first | rfl | exact hx
              · first | rfl | exact hy
              · first | rfl | simp only [hx, hy]
        · exact absurd h (fail_not_running _)
    · exact absurd h (fail_not_running _)

theorem cmpOp_sim {P : Prog} {μ : Forest} {ms : MoveSem} {s t : St} (hwf : ForestWF P μ)
    (hR : Rel μ s t) (A : Layout) (a b : Operand) (f : Nat → Nat → Bool)
    (hrun : (cmpOp ms P (hyb μ A) s a b f).status = .running)
    (hnvc : NoValueClobber μ (cmpOp ms P (hyb μ A) s a b f).log) :
    Rel μ (cmpOp ms P (hyb μ A) s a b f)
      (cmpOp ms P A t (a.mapPlaces μ.mapPlace) (b.mapPlaces μ.mapPlace) f) := by
  obtain ⟨s1, va, s2, vb, x, y, he, he2, hx, hy, hc⟩ := cmpOp_running hrun
  rw [hc] at hrun hnvc ⊢
  have hrun2 : (evalOp ms P s1 b).1.status = .running := by rw [he2]; exact hrun
  have hnvc2 : NoValueClobber μ (evalOp ms P s1 b).1.log := by rw [he2]; exact hnvc
  have hrun1 : (evalOp ms P s a).1.status = .running := by
    rw [he]; exact (fr_evalOp ms P s1 b).mono hrun2
  have hnvc1 : NoValueClobber μ (evalOp ms P s a).1.log := by
    rw [he]; exact nvc_step hnvc2 (step_evalOp ms P s1 b)
  obtain ⟨vs', hvs', hvt, hrel⟩ := evalOp_sim hwf hR a hrun1 hnvc1
  rw [he] at hvs' hrel
  simp only [Option.some.injEq] at hvs'
  subst hvs'
  rcases het : evalOp ms P t (a.mapPlaces μ.mapPlace) with ⟨t1, ovt⟩
  rw [het] at hvt hrel
  simp only at hvt hrel
  subst hvt
  obtain ⟨vs2, hvs2, hvt2, hrel2⟩ := evalOp_sim hwf hrel b hrun2 hnvc2
  rw [he2] at hvs2 hrel2
  simp only [Option.some.injEq] at hvs2
  subst hvs2
  rcases het2 : evalOp ms P t1 (b.mapPlaces μ.mapPlace) with ⟨t2, ovt2⟩
  rw [het2] at hvt2 hrel2
  simp only at hvt2 hrel2
  subst hvt2
  unfold cmpOp
  rw [het]
  simp only [List.map]
  rw [het2]
  simp only [List.map]
  rw [← addr_hyb, ← addr_hyb, hx, hy]
  exact hrel2.emit _

end Coal
namespace Coal

theorem basic_sim {P : Prog} {μ : Forest} {ms : MoveSem} {s t : St} (hwf : ForestWF P μ)
    (hR : Rel μ s t) (A : Layout) (st : Stmt) (hb : IsBasic st)
    (hrun : (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st).status = .running)
    (hnvc : NoValueClobber μ (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st).log) :
    Rel μ (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st)
      (execBasic ⟨ms, .atomic⟩ P A t (st.mapPlaces μ.mapPlace)) := by
  have hsr : ¬ s.status ≠ .running := fun h => h hR.runS
  have htr : ¬ t.status ≠ .running := fun h => h hR.runT
  cases st with
  | assign lhs rhs =>
    simp only [execBasic, hsr, htr, ↓reduceIte, Stmt.mapPlaces] at hrun hnvc ⊢
    have hlen : ((rhs.map (Operand.mapPlaces μ.mapPlace)).map Operand.len).sum =
        (rhs.map Operand.len).sum := by
      rw [List.map_map]; congr 1; apply List.map_congr_left; intro o _; exact len_mapPlaces μ o
    have hlhs : (μ.mapPlace lhs).len = lhs.len := rfl
    rw [hlen, hlhs]
    by_cases hl : (rhs.map Operand.len).sum ≠ lhs.len
    · rw [iteP hl] at hrun; exact absurd hrun (fail_not_running _)
    · rw [iteN hl] at hrun hnvc
      rw [iteN hl, iteN hl]
      cases hres : resolvePlace P s lhs with
      | none => simp only [hres] at hrun; exact absurd hrun (fail_not_running _)
      | some r =>
        have ht := resolve_sim hwf hR hres
        simp only [hres, ht] at hrun hnvc ⊢
        rcases he : evalOps ms P s rhs with ⟨s1, _ | vs⟩
        · rw [he] at hrun; simp only at hrun; rw [hrun.symm.trans hrun] at hrun
          obtain ⟨vs, hvs, -⟩ := evalOps_sim hwf rhs hR (by rw [he]; exact hrun)
            (by rw [he] at hnvc ⊢; exact hnvc)
          rw [he] at hvs; cases hvs
        · rw [he] at hrun hnvc
          simp only at hrun hnvc
          have hrun1 : (evalOps ms P s rhs).1.status = .running := by
            rw [he]; rwa [writeCells, wck_status] at hrun
          have hnvc1 : NoValueClobber μ (evalOps ms P s rhs).1.log := by
            rw [he]; exact nvc_step hnvc (step_writeCells _ _ _ _)
          obtain ⟨vs', hvs', hvt, hrel⟩ := evalOps_sim hwf rhs hR hrun1 hnvc1
          rw [he] at hvs' hrel
          simp only [Option.some.injEq] at hvs'
          subst hvs'
          rcases het : evalOps ms P t (rhs.map (Operand.mapPlaces μ.mapPlace)) with ⟨t1, ovt⟩
          rw [het] at hvt hrel
          simp only at hvt hrel
          subst hvt
          simp only
          exact write_sim hrel r.base r.off vs
  | store p op =>
    simp only [execBasic, hsr, htr, ↓reduceIte, Stmt.mapPlaces] at hrun hnvc ⊢
    cases hres : resolvePlace P s p with
    | none => simp only [hres] at hrun; exact absurd hrun (fail_not_running _)
    | some r =>
      have ht := resolve_sim hwf hR hres
      simp only [hres, ht] at hrun hnvc ⊢
      have hrl : (μ.mapPlace r).len = r.len := rfl
      rw [hrl]
      by_cases hl1 : r.len = 1
      · rw [iteP hl1] at hrun hnvc
        rw [iteP hl1, iteP hl1]
        rcases hrd : readCells s r.base r.off 1 with ⟨s1, _ | vs⟩
        · rw [hrd] at hrun; simp only at hrun
          rw [readCells_none_status hrd] at hrun; cases hrun
        · rw [hrd] at hrun hnvc
          rcases vs with _ | ⟨x, _ | ⟨w, vs⟩⟩
          · simp only at hrun; exact absurd hrun (fail_not_running _)
          · cases x with
            | ptr l o =>
              simp only at hrun hnvc
              rcases he : evalOp ms P s1 op with ⟨s2, _ | vs⟩
              · rw [he] at hrun; simp only at hrun
                rw [evalOp_none he] at hrun; cases hrun
              · rw [he] at hrun hnvc
                simp only at hrun hnvc
                by_cases hc : s2.live l = true ∧ o + vs.length ≤ P.size l
                · rw [iteP hc] at hrun hnvc
                  have hrun2 : (evalOp ms P s1 op).1.status = .running := by
                    rw [he]; rwa [writeCells, wck_status] at hrun
                  have hnvc2 : NoValueClobber μ (evalOp ms P s1 op).1.log := by
                    rw [he]; exact nvc_step hnvc (step_writeCells _ _ _ _)
                  have hrun1 : (readCells s r.base r.off 1).1.status = .running := by
                    rw [hrd]; exact (fr_evalOp ms P s1 op).mono hrun2
                  have hnvc1 : NoValueClobber μ (readCells s r.base r.off 1).1.log := by
                    rw [hrd]; exact nvc_step hnvc2 (step_evalOp ms P s1 op)
                  obtain ⟨vs1, hvs1, hvt1, hrel1⟩ := read_sim hR r.base r.off 1 hrun1 hnvc1
                  rw [hrd] at hvs1 hrel1
                  simp only [Option.some.injEq] at hvs1
                  subst hvs1
                  have hrt0 : (μ.mapPlace r).base = μ.root r.base := rfl
                  have hrt1 : (μ.mapPlace r).off = μ.offset r.base + r.off := rfl
                  rw [hrt0, hrt1]
                  rcases hrt : readCells t (μ.root r.base) (μ.offset r.base + r.off) 1 with ⟨t1, ovt⟩
                  rw [hrt] at hvt1 hrel1
                  simp only at hvt1 hrel1
                  subst hvt1
                  simp only [List.map, tr]
                  obtain ⟨vs2, hvs2, hvt2, hrel2⟩ := evalOp_sim hwf hrel1 op hrun2 hnvc2
                  rw [he] at hvs2 hrel2
                  simp only [Option.some.injEq] at hvs2
                  subst hvs2
                  rcases het : evalOp ms P t1 (op.mapPlaces μ.mapPlace) with ⟨t2, ovt⟩
                  rw [het] at hvt2 hrel2
                  simp only at hvt2 hrel2
                  subst hvt2
                  have hcT : t2.live (μ.root l) = true ∧
                      μ.offset l + o + (vs.map (tr μ)).length ≤ P.size (μ.root l) := by
                    rw [List.length_map]
                    exact ⟨hrel2.liveRoot hwf l hc.1, by have := offset_add_size_le hwf l; omega⟩
                  rw [he]
                  simp only
                  rw [iteP hc, iteP hcT]
                  exact write_sim hrel2 l o vs
                · rw [iteN hc] at hrun; exact absurd hrun (fail_not_running _)
            | _ => simp only at hrun; exact absurd hrun (fail_not_running _)
          · simp only at hrun; exact absurd hrun (fail_not_running _)
      · rw [iteN hl1] at hrun; exact absurd hrun (fail_not_running _)
  | ptrEq a b =>
    simp only [execBasic, hsr, htr, ↓reduceIte, Stmt.mapPlaces] at hrun hnvc ⊢
    exact cmpOp_sim hwf hR A a b _ hrun hnvc
  | ptrInRange a b n =>
    simp only [execBasic, hsr, htr, ↓reduceIte, Stmt.mapPlaces] at hrun hnvc ⊢
    exact cmpOp_sim hwf hR A a b _ hrun hnvc
  | out o =>
    simp only [execBasic, hsr, htr, ↓reduceIte, Stmt.mapPlaces] at hrun hnvc ⊢
    rcases he : evalOp ms P s o with ⟨s1, _ | vs⟩
    · rw [he] at hrun; simp only at hrun
      rw [evalOp_none he] at hrun; cases hrun
    · rw [he] at hrun hnvc
      simp only at hrun hnvc
      obtain ⟨vs', hvs', hvt, hrel⟩ := evalOp_sim hwf hR o (by rw [he]; exact hrun)
        (by rw [he]; exact nvc_step hnvc (step_emit _ _))
      rw [he] at hvs' hrel
      simp only [Option.some.injEq] at hvs'
      subst hvs'
      rcases het : evalOp ms P t (o.mapPlaces μ.mapPlace) with ⟨t1, ovt⟩
      rw [het] at hvt hrel
      simp only at hvt hrel
      subst hvt
      simp only
      have : (vs.map (tr μ)).map (Val.obs A) = vs.map (Val.obs (hyb μ A)) := by
        rw [List.map_map]; apply List.map_congr_left; intro v _; exact (obs_hyb μ A v).symm
      rw [this]
      exact hrel.emit _
  | nop =>
    simp only [execBasic, hsr, htr, ↓reduceIte, Stmt.mapPlaces]
    exact hR
  | storageLive x => exact absurd hb (by simp [IsBasic])
  | storageDead x => exact absurd hb (by simp [IsBasic])
  | call fn a => exact absurd hb (by simp [IsBasic])

theorem coalesceStmt_basic (μ : Forest) (st : Stmt) (hb : IsBasic st) :
    μ.coalesceStmt st = st.mapPlaces μ.mapPlace := by
  cases st <;> first | rfl | exact absurd hb (by simp [IsBasic])

theorem execBasic_inCall_sim {P : Prog} {μ : Forest} {ms : MoveSem} {s t : St}
    (hwf : ForestWF P μ) (hR : Rel μ s t) (A : Layout) (st : Stmt) (hc : s.inCall = true)
    (hrun : (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st).status = .running)
    (hnvc : NoValueClobber μ (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st).log) :
    Rel μ (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st)
      (execBasic ⟨ms, .atomic⟩ P A t (μ.coalesceStmt st)) := by
  have hsr : ¬ s.status ≠ .running := fun h => h hR.runS
  by_cases hb : IsBasic st
  · rw [coalesceStmt_basic μ st hb]; exact basic_sim hwf hR A st hb hrun hnvc
  · exfalso
    cases st with
    | storageLive x =>
      simp only [execBasic, hsr, hc, ↓reduceIte] at hrun; exact fail_not_running _ hrun
    | storageDead x =>
      simp only [execBasic, hsr, hc, ↓reduceIte] at hrun; exact fail_not_running _ hrun
    | call fn a =>
      simp only [execBasic, hsr, ↓reduceIte] at hrun; exact fail_not_running _ hrun
    | _ => exact hb trivial

theorem execCallee_sim {P : Prog} {μ : Forest} {ms : MoveSem} (hwf : ForestWF P μ) (A : Layout)
    (b : List Stmt) : ∀ s t : St, Rel μ s t → s.inCall = true →
    (execCallee ⟨ms, .atomic⟩ P (hyb μ A) s b).status = .running →
    NoValueClobber μ (execCallee ⟨ms, .atomic⟩ P (hyb μ A) s b).log →
    Rel μ (execCallee ⟨ms, .atomic⟩ P (hyb μ A) s b)
      (execCallee ⟨ms, .atomic⟩ P A t (b.map μ.coalesceStmt)) := by
  induction b with
  | nil => intro s t hR _ _ _; exact hR
  | cons st b ih =>
    intro s t hR hc hrun hnvc
    simp only [execCallee, List.foldl_cons, List.map_cons] at hrun hnvc ⊢
    have hrun1 := mono_execCallee (b := b) hrun
    have hnvc1 := nvc_step hnvc (step_execCallee _ _ _ _ b)
    have h1 := execBasic_inCall_sim hwf hR A st hc hrun1 hnvc1
    have hc1 : (execBasic ⟨ms, .atomic⟩ P (hyb μ A) s st).inCall = true := by
      rw [(step_execBasic _ _ _ s st).inCall]; exact hc
    exact ih _ _ h1 hc1 hrun hnvc

end Coal
namespace Coal

/-! ## Allocation and deallocation -/

theorem Rel.setLive {μ : Forest} {s t : St} (hR : Rel μ s t) (Ls Lt : Nat → Bool)
    (cs ct : List (Nat × Nat)) (h1 : ∀ y, μ.inClass y = false → Lt y = Ls y)
    (h2 : ∀ r ∈ μ.roots, Lt r = true) :
    Rel μ { s with live := Ls, conflicts := cs } { t with live := Lt, conflicts := ct } :=
  ⟨hR.runS, hR.runT, hR.trace, hR.inCall, hR.alias, hR.aliasNC, h1, h2, hR.init, hR.mem⟩

theorem Rel.setLiveSrc {μ : Forest} {s t : St} (hR : Rel μ s t) (Ls : Nat → Bool)
    (cs : List (Nat × Nat)) (h1 : ∀ y, μ.inClass y = false → t.live y = Ls y) :
    Rel μ { s with live := Ls, conflicts := cs } t :=
  ⟨hR.runS, hR.runT, hR.trace, hR.inCall, hR.alias, hR.aliasNC, h1, hR.liveR, hR.init, hR.mem⟩

theorem Rel.setCtx {μ : Forest} {s t : St} (hR : Rel μ s t) (al : Option (Nat × Place))
    (hal : ∀ a, al = some a → μ.inClass a.1 = false) (c : Bool) :
    Rel μ { s with alias := al, inCall := c }
      { t with alias := al.map (fun a => (a.1, μ.mapPlace a.2)), inCall := c } :=
  ⟨hR.runS, hR.runT, hR.trace, rfl, rfl, hal, hR.liveNC, hR.liveR, hR.init, hR.mem⟩

theorem Rel.setInCall {μ : Forest} {s t : St} (hR : Rel μ s t) (c : Bool) :
    Rel μ { s with inCall := c } { t with inCall := c } :=
  ⟨hR.runS, hR.runT, hR.trace, rfl, hR.alias, hR.aliasNC, hR.liveNC, hR.liveR, hR.init, hR.mem⟩

theorem resetCells_eq (s : St) (x n : Nat) :
    resetCells s x n = { s with
      mem := fun l o => if l = x ∧ 0 ≤ o ∧ o < 0 + n then .uninit else s.mem l o
      log := s.log ++ (List.range n).map fun i => ⟨s.tick, s.inCall, x, 0 + i, .reset⟩ } := by
  unfold resetCells
  rw [writeCellsK_eq]
  simp only [List.length_replicate]
  congr 1
  funext l o
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [show o - 0 < n by omega, ↓reduceIte, Option.getD_some]
  · rfl

theorem scan_reset (μ : Forest) (s : St) (x n : Nat) :
    scan μ (resetCells s x n).log (fun _ => none) = scan μ s.log (fun _ => none) := by
  rw [resetCells_eq]
  simp only
  rw [scan_append, scan_block]
  simp

theorem Rel.resetSrc {μ : Forest} {s t : St} (hR : Rel μ s t) (x n : Nat) :
    Rel μ (resetCells s x n) t := by
  have hs := scan_reset μ s x n
  rw [resetCells_eq] at hs ⊢
  refine ⟨hR.runS, hR.runT, hR.trace, hR.inCall, hR.alias, hR.aliasNC, hR.liveNC, hR.liveR, ?_, ?_⟩
  · intro l o hne
    simp only at hne hs ⊢
    rw [hs]
    split at hne
    · exact absurd rfl hne
    · exact hR.init l o hne
  · intro l o hlw hne
    simp only at hne hs hlw ⊢
    rw [hs] at hlw
    split at hne
    · exact absurd rfl hne
    · rw [iteN (by assumption)]; exact hR.mem l o hlw hne

theorem Rel.resetBoth {μ : Forest} {s t : St} (hR : Rel μ s t) {x : Nat}
    (hx : μ.inClass x = false) (n : Nat) : Rel μ (resetCells s x n) (resetCells t x n) := by
  have hs := scan_reset μ s x n
  rw [resetCells_eq] at hs ⊢
  rw [resetCells_eq]
  refine ⟨hR.runS, hR.runT, hR.trace, hR.inCall, hR.alias, hR.aliasNC, hR.liveNC, hR.liveR, ?_, ?_⟩
  · intro l o hne
    simp only at hne hs ⊢
    rw [hs]
    split at hne
    · exact absurd rfl hne
    · exact hR.init l o hne
  · intro l o hlw hne
    simp only at hne hs hlw ⊢
    rw [hs] at hlw
    split at hne
    · exact absurd rfl hne
    · rename_i hnin
      rw [iteN hnin]
      have hnin2 : ¬ (μ.root l = x ∧ 0 ≤ μ.offset l + o ∧ μ.offset l + o < 0 + n) := by
        rintro ⟨h1, -, h3⟩
        have hl := eq_of_root_eq_notClass hx h1
        subst hl
        rw [offset_of_not_inClass hx] at h3
        exact hnin ⟨rfl, by omega, by omega⟩
      rw [iteN hnin2]
      exact hR.mem l o hlw hne

theorem allocate_eq {P : Prog} {s : St} {x : Nat} (hx : x < P.nloc) :
    allocate P s x = resetCells { s with
      conflicts := s.conflicts ++ (liveOthers P s x).map fun z => (x, z),
      live := fun z => if z = x then true else s.live z } x (P.size x) := by
  unfold allocate; rw [iteP hx]

theorem resetCells_live (s : St) (x n : Nat) : (resetCells s x n).live = s.live := by
  rw [resetCells_eq]

theorem resetCells_conf (s : St) (x n : Nat) : (resetCells s x n).conflicts = s.conflicts := by
  rw [resetCells_eq]

theorem allocate_live {P : Prog} {s : St} {x : Nat} (hx : x < P.nloc) :
    (allocate P s x).live = fun z => if z = x then true else s.live z := by
  rw [allocate_eq hx, resetCells_live]

theorem allocate_conf {P : Prog} {s : St} {x : Nat} (hx : x < P.nloc) :
    (allocate P s x).conflicts = s.conflicts ++ (liveOthers P s x).map fun z => (x, z) := by
  rw [allocate_eq hx, resetCells_conf]

theorem deallocate_conf (P : Prog) (s : St) (x : Nat) :
    (deallocate P s x).conflicts = s.conflicts := by
  unfold deallocate; split
  · simp only; rw [resetCells_conf]
  · rfl

theorem deallocate_live (P : Prog) (s : St) (x : Nat) :
    (deallocate P s x).live = fun z => if z = x then false else s.live z := by
  unfold deallocate; split
  · simp only; rw [resetCells_live]
  · rename_i h
    funext z
    split
    · rename_i hz; subst hz; simpa using h
    · rfl

theorem alloc_src_sim {P : Prog} {μ : Forest} {s t : St} (hR : Rel μ s t) {x : Nat}
    (hx : μ.inClass x = true) (hrun : (allocate P s x).status = .running) :
    Rel μ (allocate P s x) t := by
  have hlt := (allocate_status hrun).2
  rw [allocate_eq hlt]
  refine (hR.setLiveSrc _ _ ?_).resetSrc _ _
  intro y hy
  have : y ≠ x := by intro h; rw [h, hx] at hy; cases hy
  simp only [this, ↓reduceIte]
  exact hR.liveNC y hy

theorem alloc_both_sim {P : Prog} {μ : Forest} {s t : St} (hR : Rel μ s t)
    {x : Nat} (hx : μ.inClass x = false) (hrun : (allocate P s x).status = .running) :
    Rel μ (allocate P s x) (allocate P t x) := by
  have hlt := (allocate_status hrun).2
  rw [allocate_eq hlt, allocate_eq hlt]
  refine (hR.setLive _ _ _ _ ?_ ?_).resetBoth hx _
  · intro y hy
    by_cases h : y = x
    · simp [h]
    · simp only [h, ↓reduceIte]; exact hR.liveNC y hy
  · intro r hr
    by_cases h : r = x
    · simp [h]
    · simp only [h, ↓reduceIte]; exact hR.liveR r hr

theorem dealloc_src_sim {P : Prog} {μ : Forest} {s t : St} (hR : Rel μ s t) {x : Nat}
    (hx : μ.inClass x = true) : Rel μ (deallocate P s x) t := by
  unfold deallocate
  split
  · simp only
    have h1 := hR.resetSrc x (P.size x)
    refine h1.setLiveSrc _ _ ?_
    intro y hy
    have : y ≠ x := by intro h; rw [h, hx] at hy; cases hy
    simp only [this, ↓reduceIte, resetCells_live]
    exact hR.liveNC y hy
  · exact hR

theorem dealloc_both_sim {P : Prog} {μ : Forest} {s t : St} (hwf : ForestWF P μ) (hR : Rel μ s t)
    {x : Nat} (hx : μ.inClass x = false) : Rel μ (deallocate P s x) (deallocate P t x) := by
  have hl := hR.liveNC x hx
  unfold deallocate
  rw [hl]
  split
  · simp only
    have h1 := hR.resetBoth hx (P.size x)
    refine h1.setLive _ _ _ _ ?_ ?_
    · intro y hy
      by_cases h : y = x
      · simp [h]
      · simp only [h, ↓reduceIte, resetCells_live]; exact hR.liveNC y hy
    · intro r hr
      have hrc := (mem_roots hwf hr).1
      have : r ≠ x := by intro h; rw [h, hx] at hrc; cases hrc
      simp only [this, ↓reduceIte, resetCells_live]; exact hR.liveR r hr
  · exact hR

end Coal
namespace Coal

/-! ## Allocation pairs: coverage of source pairs by coalesced pairs -/

/-- The pair `(a, b)` is recorded in either orientation. -/
def PairIn (t : St) (a b : Nat) : Prop := (a, b) ∈ t.conflicts ∨ (b, a) ∈ t.conflicts

/-- A source allocation pair `(x, z)` is covered by the coalesced allocation pairs: distinct
roots are recorded, and two members of one class are lexically allocated during a common tick
when both are address-taken and their windows intersect. -/
def Covered (P : Prog) (μ : Forest) (t : St) (x z : Nat) : Prop :=
  x < P.nloc ∧ z < P.nloc ∧ x ≠ z ∧
  (μ.root x ≠ μ.root z → PairIn t (μ.root x) (μ.root z)) ∧
  (μ.root x = μ.root z → AddrTaken P x → AddrTaken P z → μ.windowsOverlap P x z = true →
    LexOverlap P x z)

/-- Invariants about allocation pairs. -/
structure Ext (P : Prog) (μ : Forest) (s t : St) : Prop where
  cov : ∀ c ∈ s.conflicts, Covered P μ t c.1 c.2
  zr : ∀ z, μ.inClass z = false → s.live z = true → ∀ r ∈ μ.roots, PairIn t z r
  rr : ∀ r1 ∈ μ.roots, ∀ r2 ∈ μ.roots, r1 ≠ r2 → PairIn t r1 r2

def Grow (t t' : St) : Prop := ∃ d, t'.conflicts = t.conflicts ++ d

theorem Grow.refl (t : St) : Grow t t := ⟨[], by simp⟩

theorem Grow.trans {s t u : St} (h1 : Grow s t) (h2 : Grow t u) : Grow s u := by
  obtain ⟨d1, h1⟩ := h1; obtain ⟨d2, h2⟩ := h2
  exact ⟨d1 ++ d2, by rw [h2, h1, List.append_assoc]⟩

theorem step_grow {s t : St} (h : Step s t) : Grow s t :=
  let ⟨d, hd, _⟩ := h.conf; ⟨d, hd⟩

theorem stepT_grow {s t : St} (h : StepT s t) : Grow s t :=
  let ⟨d, hd, _⟩ := h.conf; ⟨d, hd⟩

theorem PairIn.mono {t t' : St} {a b : Nat} (h : PairIn t a b) (hg : Grow t t') : PairIn t' a b := by
  obtain ⟨d, hd⟩ := hg
  unfold PairIn at h ⊢
  rw [hd, List.mem_append, List.mem_append]
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

theorem PairIn.symm {t : St} {a b : Nat} (h : PairIn t a b) : PairIn t b a := Or.symm h

theorem Covered.mono {P : Prog} {μ : Forest} {t t' : St} {x z : Nat} (h : Covered P μ t x z)
    (hg : Grow t t') : Covered P μ t' x z :=
  ⟨h.1, h.2.1, h.2.2.1, fun hne => (h.2.2.2.1 hne).mono hg, h.2.2.2.2⟩

theorem Ext.mono {P : Prog} {μ : Forest} {s t s' t' : St} (h : Ext P μ s t)
    (hc : s'.conflicts = s.conflicts) (hl : ∀ z, s'.live z = true → s.live z = true)
    (hg : Grow t t') : Ext P μ s' t' :=
  ⟨fun c hc' => (h.cov c (hc ▸ hc')).mono hg,
   fun z hz hlz r hr => (h.zr z hz (hl z hlz) r hr).mono hg,
   fun r1 h1 r2 h2 hne => (h.rr r1 h1 r2 h2 hne).mono hg⟩

theorem Ext.of_fr {P : Prog} {μ : Forest} {s t s' t' : St} (h : Ext P μ s t) (hf : Fr s s')
    (hg : Grow t t') : Ext P μ s' t' :=
  h.mono hf.conf (fun z hz => by rw [hf.live] at hz; exact hz) hg

theorem mem_liveOthers {P : Prog} {s : St} {x z : Nat} :
    z ∈ liveOthers P s x ↔ z < P.nloc ∧ z ≠ x ∧ s.live z = true := by
  simp [liveOthers, List.mem_filter, List.mem_range]

theorem root_lt {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {z : Nat} (hz : z < P.nloc) :
    μ.root z < P.nloc := by
  cases hzc : μ.inClass z
  · rw [root_of_not_inClass hzc]; exact hz
  · exact (mem_roots hwf (root_mem_roots hwf hzc)).2.2.2

theorem ext_alloc_both {P : Prog} {μ : Forest} {s t : St} (hwf : ForestWF P μ)
    (hE : Ext P μ s t) (hR : Rel μ s t) {x : Nat} (hx : μ.inClass x = false) (hlt : x < P.nloc) :
    Ext P μ (allocate P s x) (allocate P t x) := by
  have hgrow : Grow t (allocate P t x) := ⟨_, allocate_conf hlt⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [allocate_conf hlt, List.mem_append] at hc
    rcases hc with hc | hc
    · exact (hE.cov c hc).mono hgrow
    · rw [List.mem_map] at hc
      obtain ⟨z, hz, rfl⟩ := hc
      obtain ⟨hzn, hzx, hzl⟩ := mem_liveOthers.1 hz
      refine ⟨hlt, hzn, fun h => hzx h.symm, ?_, ?_⟩
      · intro hne
        simp only [root_of_not_inClass hx] at hne ⊢
        left
        rw [allocate_conf hlt, List.mem_append, List.mem_map]
        right
        exact ⟨μ.root z, mem_liveOthers.2 ⟨root_lt hwf hzn, fun h => hne h.symm,
          hR.liveRoot hwf z hzl⟩, rfl⟩
      · intro heq
        simp only [root_of_not_inClass hx] at heq
        exact absurd (eq_of_root_eq_notClass hx heq.symm) hzx
  · intro z hz hlz r hr
    rw [allocate_live hlt] at hlz
    by_cases hzx : z = x
    · subst hzx
      left
      rw [allocate_conf hlt, List.mem_append, List.mem_map]
      right
      obtain ⟨hrc, -, -, hrn⟩ := mem_roots hwf hr
      exact ⟨r, mem_liveOthers.2 ⟨hrn, (fun h => by rw [h, hz] at hrc; cases hrc), hR.liveR r hr⟩, rfl⟩
    · simp only [hzx, ↓reduceIte] at hlz
      exact (hE.zr z hz hlz r hr).mono hgrow
  · intro r1 h1 r2 h2 hne; exact (hE.rr r1 h1 r2 h2 hne).mono hgrow

theorem ext_alloc_src {P : Prog} {μ : Forest} {s t : St} (hwf : ForestWF P μ)
    (hE : Ext P μ s t) {x : Nat} (hx : μ.inClass x = true) (hlt : x < P.nloc) (k : Nat)
    (hk : k < P.code.length) (hcode : P.code[k] = .storageLive x)
    (hlex : ∀ z, μ.inClass z = true → s.live z = lexLiveBefore P z k) :
    Ext P μ (allocate P s x) t := by
  refine ⟨?_, ?_, hE.rr⟩
  · intro c hc
    rw [allocate_conf hlt, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hE.cov c hc
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc
      obtain ⟨hzn, hzx, hzl⟩ := mem_liveOthers.1 hz
      refine ⟨hlt, hzn, fun h => hzx h.symm, ?_, ?_⟩
      · intro hne
        cases hzc : μ.inClass z
        · simp only [root_of_not_inClass hzc] at hne ⊢
          exact (hE.zr z hzc hzl (μ.root x) (root_mem_roots hwf hx)).symm
        · exact hE.rr _ (root_mem_roots hwf hx) _ (root_mem_roots hwf hzc) hne
      · intro heq _ _ _
        have hzc : μ.inClass z = true := by
          cases hzc : μ.inClass z
          · rw [root_of_not_inClass hzc] at heq
            have := inClass_root hx
            rw [heq, hzc] at this
            cases this
          · rfl
        refine ⟨2 * k, by omega, ?_, ?_⟩
        · simp only [InIv, LexLiveAt, show 2 * k / 2 = k by omega, Bool.or_eq_true]
          right
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, hcode]
        · simp only [InIv, LexLiveAt, show 2 * k / 2 = k by omega, Bool.or_eq_true]
          left
          rw [← hlex z hzc, hzl]
  · intro z hz hlz r hr
    rw [allocate_live hlt] at hlz
    have hzx : z ≠ x := by intro h; rw [h, hx] at hz; cases hz
    simp only [hzx, ↓reduceIte] at hlz
    exact hE.zr z hz hlz r hr

theorem ext_dealloc {P : Prog} {μ : Forest} {s t t' : St} (hE : Ext P μ s t) (x : Nat)
    (hg : Grow t t') : Ext P μ (deallocate P s x) t' := by
  refine hE.mono (deallocate_conf P s x) ?_ hg
  intro z hz
  rw [deallocate_live] at hz
  simp only at hz
  split at hz
  · cases hz
  · exact hz

/-! ## Lexical liveness -/

theorem lexLiveBefore_zero (P : Prog) (u : Nat) : lexLiveBefore P u 0 = false := by
  simp [lexLiveBefore]

theorem lexLiveBefore_succ (P : Prog) (u k : Nat) (hk : k < P.code.length) :
    lexLiveBefore P u (k + 1) =
      (match P.code[k] with
       | .storageLive x => if x == u then true else lexLiveBefore P u k
       | .storageDead x => if x == u then false else lexLiveBefore P u k
       | _ => lexLiveBefore P u k) := by
  unfold lexLiveBefore
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

end Coal
namespace Coal

/-! ## Top-level calls -/

/-- The in-place branch of a top-level call. -/
def callIP (sem : Sem) (P : Prog) (A : Layout) (s : St) (c : Callee) (q : Place) : St :=
  match resolvePlace P s q with
  | none => s.fail .ub
  | some r =>
    if r.len ≠ P.size c.prm then s.fail .ub else
    let s1 := execCallee sem P A { s with alias := some (c.prm, r), inCall := true } c.body
    { s1 with alias := none, inCall := false }

/-- The copy-passing branch of a top-level call. -/
def callCP (sem : Sem) (P : Prog) (A : Layout) (s : St) (c : Callee) (arg : Operand) : St :=
  match evalOp sem.move P s arg with
  | (s1, some vs) =>
    if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
    let s2 := allocate P s1 c.prm
    let s3 := writeCells s2 c.prm 0 vs
    let s4 := execCallee sem P A { s3 with inCall := true } c.body
    deallocate P { s4 with inCall := false } c.prm
  | (s1, none) => s1

theorem execStmt_callIP (am : AssignMode) (P : Prog) (A : Layout) (s : St) (fn : Nat) (q : Place)
    (hs : s.status = .running) :
    execStmt ⟨.inPlaceCall, am⟩ P A s (.call fn (.move q)) =
      callIP ⟨.inPlaceCall, am⟩ P A s (P.fn fn) q := by
  unfold execStmt
  rw [iteN (c := s.status ≠ .running) (by simp [hs])]
  rfl

theorem execStmt_callCP (sem : Sem) (P : Prog) (A : Layout) (s : St) (fn : Nat) (arg : Operand)
    (hs : s.status = .running) (h : ¬ (sem.move = .inPlaceCall ∧ ∃ q, arg = .move q)) :
    execStmt sem P A s (.call fn arg) = callCP sem P A s (P.fn fn) arg := by
  obtain ⟨ms, am⟩ := sem
  simp only [execStmt, hs, ne_eq, not_true_eq_false, ↓reduceIte]
  cases ms <;> cases arg <;> first | rfl | (exfalso; exact h ⟨rfl, _, rfl⟩)

theorem callIP_c (μ : Forest) (P : Prog) (sem : Sem) (A : Layout) (s : St) (c : Callee)
    (q : Place) : callIP sem (coalesce μ P) A s c q = callIP sem P A s c q := by
  unfold callIP; simp only [execCallee_c]; rfl

theorem callCP_c (μ : Forest) (P : Prog) (sem : Sem) (A : Layout) (s : St) (c : Callee)
    (arg : Operand) : callCP sem (coalesce μ P) A s c arg = callCP sem P A s c arg := by
  unfold callCP; simp only [evalOp_c, execCallee_c]; rfl

theorem Ext.setCtx {P : Prog} {μ : Forest} {s t : St} (h : Ext P μ s t) (a1 a2 : Option (Nat × Place))
    (c1 c2 : Bool) : Ext P μ { s with alias := a1, inCall := c1 } { t with alias := a2, inCall := c2 } :=
  ⟨h.cov, h.zr, h.rr⟩

theorem Ext.setInCall {P : Prog} {μ : Forest} {s t : St} (h : Ext P μ s t) (c1 c2 : Bool) :
    Ext P μ { s with inCall := c1 } { t with inCall := c2 } :=
  ⟨h.cov, h.zr, h.rr⟩

theorem callIP_sim {P : Prog} {μ : Forest} {ms : MoveSem} {s t : St} (hwf : ForestWF P μ)
    (hR : Rel μ s t) (c : Callee) (hprm : μ.inClass c.prm = false) (q : Place) (A : Layout)
    (hrun : (callIP ⟨ms, .atomic⟩ P (hyb μ A) s c q).status = .running)
    (hnvc : NoValueClobber μ (callIP ⟨ms, .atomic⟩ P (hyb μ A) s c q).log) :
    Rel μ (callIP ⟨ms, .atomic⟩ P (hyb μ A) s c q)
      (callIP ⟨ms, .atomic⟩ P A t ⟨c.prm, c.body.map μ.coalesceStmt⟩ (μ.mapPlace q)) ∧
    Fr s (callIP ⟨ms, .atomic⟩ P (hyb μ A) s c q) := by
  unfold callIP at hrun hnvc ⊢
  cases hres : resolvePlace P s q with
  | none => simp only [hres] at hrun; exact absurd hrun (fail_not_running _)
  | some r =>
    have ht := resolve_sim hwf hR hres
    simp only [hres, ht] at hrun hnvc ⊢
    have hl : (μ.mapPlace r).len = r.len := rfl
    rw [hl]
    by_cases hlen : r.len ≠ P.size c.prm
    · rw [iteP hlen] at hrun; exact absurd hrun (fail_not_running _)
    · rw [iteN hlen] at hrun hnvc
      rw [iteN hlen, iteN hlen]
      have hR1 := hR.setCtx (some (c.prm, r)) (by intro a ha; cases ha; exact hprm) true
      have h2 := execCallee_sim hwf A c.body _ _ hR1 rfl hrun hnvc
      refine ⟨h2.setCtx none (by intro a ha; cases ha) false, ?_⟩
      have hf := fr_execCallee ⟨ms, .atomic⟩ P (hyb μ A) c.body
        { s with alias := some (c.prm, r), inCall := true } rfl
      exact ⟨fun _ => hR.runS, hf.live, hf.conf⟩

theorem callCP_sim {P : Prog} {μ : Forest} {ms : MoveSem} {s t : St} (hwf : ForestWF P μ)
    (hR : Rel μ s t) (hE : Ext P μ s t) (c : Callee) (hprm : μ.inClass c.prm = false)
    (arg : Operand) (A : Layout)
    (hrun : (callCP ⟨ms, .atomic⟩ P (hyb μ A) s c arg).status = .running)
    (hnvc : NoValueClobber μ (callCP ⟨ms, .atomic⟩ P (hyb μ A) s c arg).log) :
    Rel μ (callCP ⟨ms, .atomic⟩ P (hyb μ A) s c arg)
      (callCP ⟨ms, .atomic⟩ P A t ⟨c.prm, c.body.map μ.coalesceStmt⟩ (arg.mapPlaces μ.mapPlace)) ∧
    Ext P μ (callCP ⟨ms, .atomic⟩ P (hyb μ A) s c arg)
      (callCP ⟨ms, .atomic⟩ P A t ⟨c.prm, c.body.map μ.coalesceStmt⟩ (arg.mapPlaces μ.mapPlace)) ∧
    (∀ z, μ.inClass z = true → (callCP ⟨ms, .atomic⟩ P (hyb μ A) s c arg).live z = s.live z) := by
  unfold callCP at hrun hnvc ⊢
  rcases he : evalOp ms P s arg with ⟨s1, _ | vs⟩
  · rw [he] at hrun; simp only at hrun; rw [evalOp_none he] at hrun; cases hrun
  · rw [he] at hrun hnvc
    simp only at hrun hnvc
    by_cases hck : vs.length ≠ P.size c.prm ∨ s1.live c.prm = true
    · rw [iteP hck] at hrun; exact absurd hrun (fail_not_running _)
    · rw [iteN hck] at hrun hnvc
      have r4 : (execCallee ⟨ms, .atomic⟩ P (hyb μ A)
          { writeCells (allocate P s1 c.prm) c.prm 0 vs with inCall := true } c.body).status =
          .running := by
        have := hrun; rw [deallocate_status] at this; exact this
      have r3 : (writeCells (allocate P s1 c.prm) c.prm 0 vs).status = .running := by
        have := mono_execCallee r4; exact this
      have r2 : (allocate P s1 c.prm).status = .running := by
        have := r3; simp only [writeCells, wck_status] at this; exact this
      obtain ⟨r1, hlt⟩ := allocate_status r2
      have n4 : NoValueClobber μ (execCallee ⟨ms, .atomic⟩ P (hyb μ A)
          { writeCells (allocate P s1 c.prm) c.prm 0 vs with inCall := true } c.body).log :=
        by have := nvc_step hnvc (step_deallocate P _ c.prm); exact this
      have n3 : NoValueClobber μ (writeCells (allocate P s1 c.prm) c.prm 0 vs).log :=
        by have := nvc_step n4 (step_execCallee _ _ _ _ c.body); exact this
      have n2 : NoValueClobber μ (allocate P s1 c.prm).log :=
        by have := nvc_step n3 (step_writeCells _ _ _ _); exact this
      have n1 : NoValueClobber μ s1.log := by have := nvc_step n2 (step_allocate _ _ _); exact this
      obtain ⟨vs', hvs', hvt, hrel1⟩ := evalOp_sim hwf hR arg (by rw [he]; exact r1)
        (by rw [he]; exact n1)
      rw [he] at hvs' hrel1
      simp only [Option.some.injEq] at hvs'
      subst hvs'
      have hfr1 := fr_evalOp ms P s arg
      rw [he] at hfr1
      have hst1 := step_evalOp ms P t (arg.mapPlaces μ.mapPlace)
      rcases het : evalOp ms P t (arg.mapPlaces μ.mapPlace) with ⟨t1, ovt⟩
      rw [het] at hvt hrel1 hst1
      simp only at hvt hrel1 hst1
      subst hvt
      simp only
      have hckT : ¬ ((vs.map (tr μ)).length ≠ P.size c.prm ∨ t1.live c.prm = true) := by
        rw [List.length_map, hrel1.liveNC c.prm hprm]; exact hck
      rw [iteN hck, iteN hckT]
      have R2 := alloc_both_sim hrel1 hprm r2
      have R3 := write_sim R2 c.prm 0 vs
      simp only [root_of_not_inClass hprm, offset_of_not_inClass hprm, Nat.add_zero] at R3
      have R4 := execCallee_sim hwf A c.body _ _ (R3.setInCall true) rfl r4 n4
      have R5 := dealloc_both_sim (P := P) hwf (R4.setInCall false) hprm
      refine ⟨R5, ?_, ?_⟩
      · have E1 : Ext P μ s1 t1 := hE.of_fr hfr1 (step_grow hst1)
        have E2 := ext_alloc_both hwf E1 hrel1 hprm hlt
        have E3 := (E2.of_fr (fr_writeCells _ c.prm 0 vs) (step_grow (step_writeCells _ c.prm 0 (vs.map (tr μ))))
          ).setInCall true true
        have E4 := (E3.of_fr (fr_execCallee ⟨ms, .atomic⟩ P (hyb μ A) c.body _ rfl)
          (step_grow (step_execCallee ⟨ms, .atomic⟩ P A _ (c.body.map μ.coalesceStmt)))).setInCall
            false false
        exact ext_dealloc E4 c.prm (step_grow (step_deallocate _ _ _))
      · intro z hz
        have hzx : z ≠ c.prm := by intro h; rw [h, hprm] at hz; cases hz
        rw [deallocate_live]
        simp only [hzx, ↓reduceIte]
        rw [(fr_execCallee ⟨ms, .atomic⟩ P (hyb μ A) c.body _ rfl).live]
        simp only
        rw [(fr_writeCells _ _ _ _).live, allocate_live hlt, hfr1.live]
        simp [hzx]

end Coal
namespace Coal

/-! ## Top-level statements -/

/-- The relation at top-level statement boundaries. -/
structure TopRel (P : Prog) (μ : Forest) (s t : St) : Prop where
  rel : Rel μ s t
  alias : s.alias = none
  inCall : s.inCall = false
  lex : ∀ z, μ.inClass z = true → s.live z = lexLiveBefore P z s.tick
  ext : Ext P μ s t

theorem callsInBounds_mem {P : Prog} (h : CallsInBounds P) {fn : Nat} {arg : Operand}
    (hm : Stmt.call fn arg ∈ P.code) : fn < P.fns.length := by
  unfold CallsInBounds at h
  rw [List.all_eq_true] at h
  have := h _ hm
  simpa using this

theorem fn_mem {P : Prog} {fn : Nat} (h : fn < P.fns.length) : P.fn fn ∈ P.fns := by
  unfold Prog.fn
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem not_call_of_basic {st : Stmt} (hb : IsBasic st) : ∀ fn a, st ≠ .call fn a := by
  intro fn a h; subst h; exact hb

theorem top_sim {P : Prog} {μ : Forest} {ms : MoveSem} (hwf : ForestWF P μ) (A : Layout)
    {s t : St} (hT : TopRel P μ s t) (k : Nat) (hk : k < P.code.length) (htk : s.tick = k)
    (st : Stmt) (hst : P.code[k] = st)
    (hrun : (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s st).status = .running)
    (hnvc : NoValueClobber μ (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s st).log) :
    Rel μ (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s st)
      (execStmt ⟨ms, .atomic⟩ (coalesce μ P) A t (μ.coalesceStmt st)) ∧
    (∀ z, μ.inClass z = true →
      (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s st).live z = lexLiveBefore P z (k + 1)) ∧
    Ext P μ (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s st)
      (execStmt ⟨ms, .atomic⟩ (coalesce μ P) A t (μ.coalesceStmt st)) := by
  have hmem : st ∈ P.code := hst ▸ List.getElem_mem hk
  have hlex := hT.lex
  rw [htk] at hlex
  have hsr := hT.rel.runS
  have htr := hT.rel.runT
  have hsr' : ¬ s.status ≠ .running := fun h => h hsr
  have htr' : ¬ t.status ≠ .running := fun h => h htr
  have hcT : t.inCall = false := hT.rel.inCall.trans hT.inCall
  have halT : t.alias = none := by rw [hT.rel.alias, hT.alias]; rfl
  have hlexs := fun z => lexLiveBefore_succ P z k hk
  rw [hst] at hlexs
  by_cases hb : IsBasic st
  · rw [execStmt_basic _ _ _ _ _ (not_call_of_basic hb)] at hrun hnvc ⊢
    have hb' : IsBasic (st.mapPlaces μ.mapPlace) := by
      cases st <;> simp_all [IsBasic, Stmt.mapPlaces]
    rw [coalesceStmt_basic μ _ hb, execStmt_basic _ _ _ _ _ (not_call_of_basic hb'), execBasic_c]
    refine ⟨basic_sim hwf hT.rel A _ hb hrun hnvc, ?_, ?_⟩
    · intro z hz
      have hk1 : lexLiveBefore P z (k + 1) = lexLiveBefore P z k := by
        rw [hlexs z]
        cases st <;> first | rfl | exact absurd hb (by simp [IsBasic])
      rw [(fr_execBasic _ _ _ _ _ (Or.inl hb)).live, hlex z hz, hk1]
    · exact hT.ext.of_fr (fr_execBasic _ _ _ _ _ (Or.inl hb))
        (step_grow (step_execBasic _ _ _ _ _))
  cases st with
  | storageLive x =>
    have hS : execStmt ⟨ms, .atomic⟩ P (hyb μ A) s (.storageLive x) = allocate P s x := by
      rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
      simp only [execBasic, hsr', hT.inCall, ↓reduceIte, Bool.false_eq_true]
    rw [hS] at hrun hnvc ⊢
    have hlt := (allocate_status hrun).2
    cases hx : μ.inClass x
    · have hcs : μ.coalesceStmt (.storageLive x) = .storageLive x := by
        simp [Forest.coalesceStmt, hx]
      have hT' : execStmt ⟨ms, .atomic⟩ (coalesce μ P) A t (.storageLive x) = allocate P t x := by
        rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
        simp only [execBasic, htr', hcT, ↓reduceIte, Bool.false_eq_true]
        rfl
      rw [hcs, hT']
      refine ⟨alloc_both_sim hT.rel hx hrun, ?_, ext_alloc_both hwf hT.ext hT.rel hx hlt⟩
      intro z hz
      have hzx : z ≠ x := by intro h; rw [h, hx] at hz; cases hz
      rw [allocate_live hlt, hlexs z]
      simp [hzx, Ne.symm hzx, hlex z hz]
    · have hcs : μ.coalesceStmt (.storageLive x) = .nop := by simp [Forest.coalesceStmt, hx]
      have hT' : execStmt ⟨ms, .atomic⟩ (coalesce μ P) A t .nop = t := by
        rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
        simp only [execBasic, htr', ↓reduceIte]
      rw [hcs, hT']
      refine ⟨alloc_src_sim hT.rel hx hrun, ?_, ext_alloc_src hwf hT.ext hx hlt k hk hst hlex⟩
      intro z hz
      rw [allocate_live hlt, hlexs z]
      by_cases hzx : z = x
      · subst hzx; simp
      · simp [hzx, Ne.symm hzx, hlex z hz]
  | storageDead x =>
    have hS : execStmt ⟨ms, .atomic⟩ P (hyb μ A) s (.storageDead x) = deallocate P s x := by
      rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
      simp only [execBasic, hsr', hT.inCall, ↓reduceIte, Bool.false_eq_true]
    rw [hS] at hrun hnvc ⊢
    cases hx : μ.inClass x
    · have hcs : μ.coalesceStmt (.storageDead x) = .storageDead x := by
        simp [Forest.coalesceStmt, hx]
      have hT' : execStmt ⟨ms, .atomic⟩ (coalesce μ P) A t (.storageDead x) =
          deallocate P t x := by
        rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
        simp only [execBasic, htr', hcT, ↓reduceIte, Bool.false_eq_true]
        rfl
      rw [hcs, hT']
      refine ⟨dealloc_both_sim hwf hT.rel hx, ?_,
        ext_dealloc hT.ext x ⟨[], by rw [deallocate_conf]; simp⟩⟩
      intro z hz
      have hzx : z ≠ x := by intro h; rw [h, hx] at hz; cases hz
      rw [deallocate_live, hlexs z]
      simp [hzx, Ne.symm hzx, hlex z hz]
    · have hcs : μ.coalesceStmt (.storageDead x) = .nop := by simp [Forest.coalesceStmt, hx]
      have hT' : execStmt ⟨ms, .atomic⟩ (coalesce μ P) A t .nop = t := by
        rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
        simp only [execBasic, htr', ↓reduceIte]
      rw [hcs, hT']
      refine ⟨dealloc_src_sim hT.rel hx, ?_, ext_dealloc hT.ext x (Grow.refl t)⟩
      intro z hz
      rw [deallocate_live, hlexs z]
      by_cases hzx : z = x
      · subst hzx; simp
      · simp [hzx, Ne.symm hzx, hlex z hz]
  | call fn arg =>
    have hfn := callsInBounds_mem hwf.2.2.2.2 hmem
    have hprm := hwf.2.2.2.1 _ (fn_mem hfn)
    have hcs : μ.coalesceStmt (.call fn arg) = .call fn (arg.mapPlaces μ.mapPlace) := rfl
    rw [hcs]
    have hgr := stepT_grow (execStmt_frame ⟨ms, .atomic⟩ (coalesce μ P) A t
      (.call fn (arg.mapPlaces μ.mapPlace)) hcT halT).1
    by_cases hip : ms = .inPlaceCall ∧ ∃ q, arg = .move q
    · obtain ⟨rfl, q, rfl⟩ := hip
      rw [execStmt_callIP _ _ _ _ _ _ hsr] at hrun hnvc ⊢
      have hm : Operand.mapPlaces μ.mapPlace (.move q) = .move (μ.mapPlace q) := rfl
      rw [hm] at hgr ⊢
      rw [execStmt_callIP _ _ _ _ _ _ htr, fn_c, callIP_c] at hgr ⊢
      obtain ⟨hR', hF⟩ := callIP_sim hwf hT.rel (P.fn fn) hprm q A hrun hnvc
      refine ⟨hR', ?_, hT.ext.of_fr hF hgr⟩
      intro z hz
      rw [hF.live, hlex z hz, hlexs z]
    · rw [execStmt_callCP _ _ _ _ _ _ hsr hip] at hrun hnvc ⊢
      have hip' : ¬ ((⟨ms, .atomic⟩ : Sem).move = .inPlaceCall ∧
          ∃ q, arg.mapPlaces μ.mapPlace = .move q) := by
        rintro ⟨h1, q, hq⟩
        apply hip
        refine ⟨h1, ?_⟩
        cases arg with
        | move q' => exact ⟨q', rfl⟩
        | _ => cases hq
      rw [execStmt_callCP _ _ _ _ _ _ htr hip', fn_c, callCP_c]
      obtain ⟨hR', hE', hL⟩ := callCP_sim hwf hT.rel hT.ext (P.fn fn) hprm arg A hrun hnvc
      refine ⟨hR', ?_, hE'⟩
      intro z hz
      rw [hL z hz, hlex z hz, hlexs z]
  | _ => exact absurd trivial hb

end Coal
namespace Coal

theorem Rel.setTick {μ : Forest} {s t : St} (hR : Rel μ s t) (a b : Nat) :
    Rel μ { s with tick := a } { t with tick := b } :=
  ⟨hR.runS, hR.runT, hR.trace, hR.inCall, hR.alias, hR.aliasNC, hR.liveNC, hR.liveR, hR.init, hR.mem⟩

theorem Ext.setTick {P : Prog} {μ : Forest} {s t : St} (h : Ext P μ s t) (a b : Nat) :
    Ext P μ { s with tick := a } { t with tick := b } := ⟨h.cov, h.zr, h.rr⟩

theorem top_step {P : Prog} {μ : Forest} {ms : MoveSem} (hwf : ForestWF P μ) (A : Layout)
    {s t : St} (hT : TopRel P μ s t) (k : Nat) (hk : k < P.code.length) (htk : s.tick = k)
    (hrun : (execTop ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k]).status = .running)
    (hnvc : NoValueClobber μ (execTop ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k]).log) :
    TopRel P μ (execTop ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k])
      (execTop ⟨ms, .atomic⟩ (coalesce μ P) A t (μ.coalesceStmt P.code[k])) := by
  have hrun' : (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k]).status = .running := hrun
  have hnvc' : NoValueClobber μ (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k]).log := hnvc
  obtain ⟨h1, h2, h3⟩ := top_sim hwf A hT k hk htk _ rfl hrun' hnvc'
  have hf := execStmt_frame ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k] hT.inCall hT.alias
  refine ⟨h1.setTick _ _, hf.2.2, hf.2.1, ?_, h3.setTick _ _⟩
  intro z hz
  show (execStmt ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k]).live z =
    lexLiveBefore P z ((execStmt ⟨ms, .atomic⟩ P (hyb μ A) s P.code[k]).tick + 1)
  rw [hf.1.tick, htk]; exact h2 z hz

theorem runAt_running {sem : Sem} {P : Prog} {A : Layout} (h : (run sem P A).status = .running)
    (k : Nat) : (runAt sem P A k).status = .running := by
  by_cases hne : (runAt sem P A k).status = .running
  · exact hne
  exfalso
  have : run sem P A = (P.code.drop k).foldl (execTop sem P A) (runAt sem P A k) := by
    unfold run runAt; rw [← List.foldl_append, List.take_append_drop]
  rw [this, foldl_execTop_of_not_running _ _ hne] at h
  exact hne h

/-! ## Entry: the roots are allocated -/

structure EntryInv (P : Prog) (D : List Nat) (t : St) : Prop where
  run : t.status = .running
  trace : t.trace = []
  inCall : t.inCall = false
  alias : t.alias = none
  live : ∀ z, t.live z = true ↔ z ∈ D
  lt : ∀ z ∈ D, z < P.nloc
  pairs : ∀ r1 ∈ D, ∀ r2 ∈ D, r1 ≠ r2 → PairIn t r1 r2

theorem entry_inv {P : Prog} (μ : Forest) (sem : Sem) (A : Layout) (L : List Nat)
    (hL : ∀ r ∈ L, r < P.nloc) : ∀ (D : List Nat) (t : St), EntryInv P D t →
    EntryInv P (D ++ L) ((L.map Stmt.storageLive).foldl (execTop sem (coalesce μ P) A) t) := by
  induction L with
  | nil => intro D t h; simpa using h
  | cons r L ih =>
    intro D t h
    have hr : r < P.nloc := hL r (by simp)
    simp only [List.map_cons, List.foldl_cons]
    have hst : ¬ t.status ≠ .running := fun hh => hh h.run
    have he : execTop sem (coalesce μ P) A t (.storageLive r) =
        { allocate P t r with tick := (allocate P t r).tick + 1 } := by
      simp only [execTop]
      rw [execStmt_basic _ _ _ _ _ (by intro fn a hh; cases hh)]
      simp only [execBasic, hst, h.inCall, ↓reduceIte, Bool.false_eq_true]
      rfl
    rw [he]
    have h2 : EntryInv P (D ++ [r]) { allocate P t r with tick := (allocate P t r).tick + 1 } := by
      have hgrow : Grow t (allocate P t r) := ⟨_, allocate_conf hr⟩
      have hfr := step_allocate P t r
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (allocate P t r).status = .running
        rw [allocate_eq hr, resetCells, wck_status]; exact h.run
      · show (allocate P t r).trace = []
        rw [allocate_eq hr, resetCells, writeCellsK_eq]; exact h.trace
      · show (allocate P t r).inCall = false
        rw [hfr.inCall]; exact h.inCall
      · show (allocate P t r).alias = none
        rw [hfr.alias]; exact h.alias
      · intro z
        show (allocate P t r).live z = true ↔ z ∈ D ++ [r]
        rw [allocate_live hr]
        by_cases hz : z = r
        · simp [hz]
        · simp only [hz, ↓reduceIte, h.live z, List.mem_append, List.mem_singleton, or_false]
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact h.lt z hz
        · rw [List.mem_singleton.1 hz]; exact hr
      · have key : ∀ r2 ∈ D, r2 ≠ r → PairIn (allocate P t r) r r2 := by
          intro r2 h2 hne
          left
          rw [allocate_conf hr, List.mem_append, List.mem_map]
          right
          exact ⟨r2, mem_liveOthers.2 ⟨h.lt r2 h2, hne, (h.live r2).2 h2⟩, rfl⟩
        intro r1 h1 r2 h2 hne
        show PairIn (allocate P t r) r1 r2
        rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
        · exact (h.pairs r1 h1 r2 h2 hne).mono hgrow
        · rw [List.mem_singleton.1 h2] at hne ⊢; exact (key r1 h1 hne).symm
        · rw [List.mem_singleton.1 h1] at hne ⊢; exact key r2 h2 (Ne.symm hne)
        · rw [List.mem_singleton.1 h1, List.mem_singleton.1 h2] at hne; exact absurd rfl hne
    have := ih (fun r' hr' => hL r' (by simp [hr'])) _ _ h2
    simpa [List.append_assoc] using this

/-- The coalesced state after the entry allocations. -/
def entry (μ : Forest) (P : Prog) (sem : Sem) (A : Layout) : St :=
  (μ.roots.map Stmt.storageLive).foldl (execTop sem (coalesce μ P) A) St.init

theorem topRel_init {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (sem : Sem) (A : Layout) :
    TopRel P μ St.init (entry μ P sem A) := by
  have h0 : EntryInv P [] St.init :=
    ⟨rfl, rfl, rfl, rfl, by simp [St.init], by simp, by simp⟩
  have hE : EntryInv P μ.roots (entry μ P sem A) :=
    entry_inv μ sem A μ.roots (fun r hr => (mem_roots hwf hr).2.2.2) [] St.init h0
  refine ⟨⟨rfl, hE.run, hE.trace, hE.inCall, by rw [hE.alias]; rfl, by simp [St.init], ?_,
    fun r hr => (hE.live r).2 hr, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
  · intro x hx
    show (entry μ P sem A).live x = false
    cases h : (entry μ P sem A).live x
    · rfl
    · have := (mem_roots hwf ((hE.live x).1 h)).1
      rw [hx] at this; cases this
  · intro l o h; exact absurd rfl h
  · intro l o _ h; exact absurd rfl h
  · intro z _; simp [St.init, lexLiveBefore_zero]
  · refine ⟨by simp [St.init], by simp [St.init], ?_⟩
    exact hE.pairs

/-! ## The core simulation -/

theorem run_coalesce (μ : Forest) (P : Prog) (sem : Sem) (A : Layout) :
    run sem (coalesce μ P) A = (P.code.map μ.coalesceStmt).foldl (execTop sem (coalesce μ P) A)
      (entry μ P sem A) := by
  unfold run entry
  rw [code_c, List.foldl_append]

theorem core_sim {P : Prog} {μ : Forest} {ms : MoveSem} (hwf : ForestWF P μ) (A : Layout)
    (hrun : (run ⟨ms, .atomic⟩ P (hyb μ A)).status = .running)
    (hnvc : NoValueClobber μ (run ⟨ms, .atomic⟩ P (hyb μ A)).log) :
    Rel μ (run ⟨ms, .atomic⟩ P (hyb μ A)) (run ⟨ms, .atomic⟩ (coalesce μ P) A) ∧
    Ext P μ (run ⟨ms, .atomic⟩ P (hyb μ A)) (run ⟨ms, .atomic⟩ (coalesce μ P) A) := by
  have key : ∀ k, k ≤ P.code.length →
      TopRel P μ (runAt ⟨ms, .atomic⟩ P (hyb μ A) k)
        (((P.code.map μ.coalesceStmt).take k).foldl (execTop ⟨ms, .atomic⟩ (coalesce μ P) A)
          (entry μ P ⟨ms, .atomic⟩ A)) := by
    intro k
    induction k with
    | zero => intro _; rw [runAt_zero]; exact topRel_init hwf _ A
    | succ k ih =>
      intro hk
      have hT := ih (by omega)
      rw [runAt_succ _ _ _ _ (by omega)]
      rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem (by omega),
        Option.map_some, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have htk := (runAt_frame ⟨ms, .atomic⟩ P (hyb μ A) k (by omega)).1
      have hr := runAt_running hrun (k + 1)
      rw [runAt_succ _ _ _ _ (by omega)] at hr
      obtain ⟨d, hd, -⟩ := runAt_log_extends ⟨ms, .atomic⟩ P (hyb μ A) (k + 1) P.code.length hk
      rw [← run_eq_runAt, runAt_succ _ _ _ _ (by omega)] at hd
      exact top_step hwf A hT k (by omega) htk hr (nvc_of_eq hnvc ⟨d, hd⟩)
  have h := key P.code.length (Nat.le_refl _)
  rw [← run_eq_runAt, List.take_of_length_le (by simp), ← run_coalesce] at h
  exact ⟨h.rel, h.ext⟩

end Coal
namespace Coal

/-! ## Traces of one program under two layouts -/

/-- Two traces agree after erasure, and are equal when the layouts agree on every address-taken
local. -/
def TR (P : Prog) (A A' : Layout) (l l' : List Event) : Prop :=
  l.map Event.erase = l'.map Event.erase ∧ ((∀ x, AddrTaken P x → A x = A' x) → l = l')

theorem TR.nil (P : Prog) (A A' : Layout) : TR P A A' [] [] := ⟨rfl, fun _ => rfl⟩

theorem TR.append {P : Prog} {A A' : Layout} {l1 l1' l2 l2' : List Event} (h1 : TR P A A' l1 l1')
    (h2 : TR P A A' l2 l2') : TR P A A' (l1 ++ l2) (l1' ++ l2') :=
  ⟨by rw [List.map_append, List.map_append, h1.1, h2.1],
   fun h => by rw [h1.2 h, h2.2 h]⟩

theorem tr_vals (P : Prog) (A A' : Layout) (vs : List Val) (hv : ValsIn (AddrTaken P) vs) :
    TR P A A' [.vals (vs.map (Val.obs A))] [.vals (vs.map (Val.obs A'))] := by
  refine ⟨?_, fun h => ?_⟩
  · simp only [List.map_cons, List.map_nil, Event.erase, List.map_map, List.cons.injEq,
      Event.vals.injEq, and_true]
    apply List.map_congr_left
    intro v _
    cases v <;> rfl
  · simp only [List.cons.injEq, Event.vals.injEq, and_true]
    apply List.map_congr_left
    intro v hvm
    cases v with
    | ptr l o => simp only [Val.obs, h l (hv _ hvm l o rfl)]
    | _ => rfl

theorem tr_cmp (P : Prog) (A A' : Layout) (b b' : Bool)
    (h : (∀ x, AddrTaken P x → A x = A' x) → b = b') : TR P A A' [.cmp b] [.cmp b'] :=
  ⟨rfl, fun hh => by rw [h hh]⟩

/-! ### Operations other than emission keep the trace -/

theorem evalOp_trace_eq (ms : MoveSem) (P : Prog) (s : St) (o : Operand) :
    (evalOp ms P s o).1.trace = s.trace := by
  have := congrArg (fun p => p.1.trace) (evalOp_trace s.trace ms P s o)
  exact this

theorem evalOps_trace_eq (ms : MoveSem) (P : Prog) (s : St) (os : List Operand) :
    (evalOps ms P s os).1.trace = s.trace := by
  have := congrArg (fun p => p.1.trace) (evalOps_trace s.trace ms P s os)
  exact this

theorem readCells_trace_eq (s : St) (loc off n : Nat) : (readCells s loc off n).1.trace = s.trace :=
  (readCells_fields s loc off n).2.2.2.1

theorem writeCellsK_trace_eq (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    (writeCellsK k s loc off vs).trace = s.trace := by rw [writeCellsK_eq]

theorem writeInOrder_trace_eq (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat) (os : List Operand) :
    (writeInOrder ms P s loc off os).trace = s.trace := by
  have := congrArg St.trace (writeInOrder_trace s.trace ms P s loc off os)
  exact this

theorem allocate_trace_eq (P : Prog) (s : St) (x : Nat) : (allocate P s x).trace = s.trace := by
  have := congrArg St.trace (allocate_trace s.trace P s x)
  exact this

theorem deallocate_trace_eq (P : Prog) (s : St) (x : Nat) : (deallocate P s x).trace = s.trace := by
  have := congrArg St.trace (deallocate_trace s.trace P s x)
  exact this

/-- Statements other than `out` and comparisons do not emit. -/
def NoEmit : Stmt → Prop
  | .out _ => False
  | .ptrEq _ _ => False
  | .ptrInRange _ _ _ => False
  | _ => True

theorem execBasic_trace_noemit (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : NoEmit st) : (execBasic sem P A s st).trace = s.trace := by
  unfold execBasic
  split
  · rfl
  · cases st with
    | storageLive x =>
      simp only; split
      · rfl
      · exact allocate_trace_eq _ _ _
    | storageDead x =>
      simp only; split
      · rfl
      · exact deallocate_trace_eq _ _ _
    | assign lhs rhs =>
      simp only; split
      · rfl
      · split
        · rfl
        · split
          · have h1 := evalOps_trace_eq sem.move P s rhs
            rcases hr : evalOps sem.move P s rhs with ⟨s', _ | vs⟩
            · rw [hr] at h1; exact h1
            · rw [hr] at h1; simp only; rw [writeCells, writeCellsK_trace_eq]; exact h1
          · exact writeInOrder_trace_eq _ _ _ _ _ _
    | store p v =>
      simp only; split
      · rename_i r _
        split
        · have h1 := readCells_trace_eq s r.base r.off 1
          split
          next s1 l o heq =>
            rw [heq] at h1
            have h2 := evalOp_trace_eq sem.move P s1 v
            split
            next s2 vs heq2 =>
              rw [heq2] at h2
              split
              · rw [writeCells, writeCellsK_trace_eq]; exact h2.trans h1
              · exact h2.trans h1
            next s2 heq2 => rw [heq2] at h2; exact h2.trans h1
          next s1 _ _ heq => rw [heq] at h1; exact h1
          next s1 heq => rw [heq] at h1; exact h1
        · rfl
      · rfl
    | call fn a => rfl
    | nop => rfl
    | out o => exact absurd h id
    | ptrEq a b => exact absurd h id
    | ptrInRange a b n => exact absurd h id

/-! ### Emission -/

theorem emit_cmpOp (ms : MoveSem) (P : Prog) (A A' : Layout) (s : St) (tr' : List Event)
    (a b : Operand) (f : Nat → Nat → Bool) (hp : PtrsIn (AddrTaken P) s)
    (ha : ∀ x, a.takesAddr x = true → AddrTaken P (aliasBase s.alias x))
    (hb : ∀ x, b.takesAddr x = true → AddrTaken P (aliasBase s.alias x)) :
    ∃ d d', (cmpOp ms P A s a b f).trace = s.trace ++ d ∧
      (cmpOp ms P A' { s with trace := tr' } a b f).trace = tr' ++ d' ∧ TR P A A' d d' := by
  unfold cmpOp
  rw [evalOp_trace tr' ms P s a]
  have h1 := evalOp_trace_eq ms P s a
  rcases he : evalOp ms P s a with ⟨s1, ova⟩
  rw [he] at h1
  simp only at h1 ⊢
  obtain ⟨hp1, hva⟩ := Inv.ptrsIn_evalOp he hp ha
  have hal1 := Inv.evalOp_alias he
  rcases ova with _ | vas
  · exact ⟨[], [], by simp [h1], by simp, TR.nil _ _ _⟩
  rcases vas with _ | ⟨va, _ | ⟨w, ws⟩⟩
  · exact ⟨[], [], by simp [St.fail, h1], by simp [St.fail], TR.nil _ _ _⟩
  · simp only
    rw [evalOp_trace tr' ms P s1 b]
    have h2 := evalOp_trace_eq ms P s1 b
    rcases he2 : evalOp ms P s1 b with ⟨s2, ovb⟩
    rw [he2] at h2
    simp only at h2 ⊢
    have hb1 : ∀ x, b.takesAddr x = true → AddrTaken P (aliasBase s1.alias x) := by
      rw [hal1]; exact hb
    obtain ⟨-, hvb⟩ := Inv.ptrsIn_evalOp he2 hp1 hb1
    rcases ovb with _ | vbs
    · exact ⟨[], [], by simp [h1, h2], by simp, TR.nil _ _ _⟩
    rcases vbs with _ | ⟨vb, _ | ⟨w', ws'⟩⟩
    · exact ⟨[], [], by simp [St.fail, h1, h2], by simp [St.fail], TR.nil _ _ _⟩
    · simp only
      have hva' := hva _ rfl va (by simp)
      have hvb' := hvb _ rfl vb (by simp)
      cases va with
      | ptr la oa =>
        cases vb with
        | ptr lb ob =>
          simp only [Val.addr?]
          refine ⟨[.cmp (f (A la + oa) (A lb + ob))], [.cmp (f (A' la + oa) (A' lb + ob))],
            by simp [St.emit, h1, h2], by simp [St.emit], tr_cmp _ _ _ _ _ ?_⟩
          intro hh
          rw [hh la (hva' la oa rfl), hh lb (hvb' lb ob rfl)]
        | _ => exact ⟨[], [], by simp [Val.addr?, St.fail, h1, h2], by simp [Val.addr?, St.fail],
            TR.nil _ _ _⟩
      | _ =>
        cases vb <;> exact ⟨[], [], by simp [Val.addr?, St.fail, h1, h2],
          by simp [Val.addr?, St.fail], TR.nil _ _ _⟩
    · exact ⟨[], [], by simp [St.fail, h1, h2], by simp [St.fail], TR.nil _ _ _⟩
  · exact ⟨[], [], by simp [St.fail, h1], by simp [St.fail], TR.nil _ _ _⟩

theorem emit_basic (sem : Sem) (P : Prog) (A A' : Layout) (s : St) (tr' : List Event) (st : Stmt)
    (hp : PtrsIn (AddrTaken P) s)
    (hd : ∀ x, st.takesAddr x = true → AddrTaken P (aliasBase s.alias x)) :
    ∃ d d', (execBasic sem P A s st).trace = s.trace ++ d ∧
      (execBasic sem P A' { s with trace := tr' } st).trace = tr' ++ d' ∧ TR P A A' d d' := by
  by_cases hne : NoEmit st
  · refine ⟨[], [], by rw [execBasic_trace_noemit _ _ _ _ _ hne]; simp,
      by rw [execBasic_trace_noemit _ _ _ _ _ hne]; simp, TR.nil _ _ _⟩
  · by_cases hs : s.status = .running
    · have hs' : ¬ s.status ≠ .running := fun h => h hs
      cases st with
      | out o =>
        simp only [execBasic, hs', ↓reduceIte]
        rw [evalOp_trace tr' sem.move P s o]
        have h1 := evalOp_trace_eq sem.move P s o
        have hd' : ∀ x, o.takesAddr x = true → AddrTaken P (aliasBase s.alias x) := hd
        rcases he : evalOp sem.move P s o with ⟨s1, _ | vs⟩
        · rw [he] at h1; simp only at h1; exact ⟨[], [], by simp [h1], by simp, TR.nil _ _ _⟩
        · rw [he] at h1
          simp only at h1
          obtain ⟨-, hv⟩ := Inv.ptrsIn_evalOp he hp hd'
          exact ⟨_, _, by simp [St.emit, h1], by simp [St.emit], tr_vals P A A' vs (hv vs rfl)⟩
      | ptrEq a b =>
        simp only [execBasic, hs', ↓reduceIte]
        exact emit_cmpOp _ _ _ _ _ _ _ _ _ hp
          (fun x hx => hd x (by simp [Stmt.takesAddr, hx]))
          (fun x hx => hd x (by simp [Stmt.takesAddr, hx]))
      | ptrInRange a b n =>
        simp only [execBasic, hs', ↓reduceIte]
        exact emit_cmpOp _ _ _ _ _ _ _ _ _ hp
          (fun x hx => hd x (by simp [Stmt.takesAddr, hx]))
          (fun x hx => hd x (by simp [Stmt.takesAddr, hx]))
      | _ => exact absurd trivial hne
    · rw [execBasic_of_not_running st hs,
        execBasic_of_not_running (s := { s with trace := tr' }) st hs]
      exact ⟨[], [], by simp, by simp, TR.nil _ _ _⟩

/-- Equality up to the trace, with related traces. -/
def TRel (P : Prog) (A A' : Layout) (s s' : St) : Prop := TEq s s' ∧ TR P A A' s.trace s'.trace

theorem trel_execBasic {sem : Sem} {P : Prog} {A A' : Layout} {s s' : St} (hR : TRel P A A' s s')
    (st : Stmt) (hp : PtrsIn (AddrTaken P) s)
    (hd : ∀ x, st.takesAddr x = true → AddrTaken P (aliasBase s.alias x)) :
    TRel P A A' (execBasic sem P A s st) (execBasic sem P A' s' st) := by
  refine ⟨execBasic_teq sem P A A' s s' hR.1 st, ?_⟩
  have hs' := hR.1.eq
  obtain ⟨d, d', h1, h2, h3⟩ := emit_basic sem P A A' s s'.trace st hp hd
  rw [hs', h1, h2]
  exact hR.2.append h3

theorem trel_execCallee {sem : Sem} {P : Prog} {A A' : Layout} (b : List Stmt) :
    ∀ s s' : St, TRel P A A' s s' → PtrsIn (AddrTaken P) s →
      (∀ st ∈ b, ∀ x, st.takesAddr x = true → AddrTaken P (aliasBase s.alias x)) →
      TRel P A A' (execCallee sem P A s b) (execCallee sem P A' s' b) := by
  induction b with
  | nil => intro s s' h _ _; exact h
  | cons st b ih =>
    intro s s' h hp hd
    simp only [execCallee, List.foldl_cons]
    apply ih
    · exact trel_execBasic h st hp (hd st (by simp))
    · exact ptrsIn_execBasic _ sem P A s st hp (hd st (by simp))
    · rw [(step_execBasic sem P A s st).alias]
      exact fun st' hst' => hd st' (by simp [hst'])

theorem TRel.of_teq {P : Prog} {A A' : Layout} {s s' t t' : St} (h : TRel P A A' s s')
    (ht : TEq t t') (h1 : t.trace = s.trace) (h2 : t'.trace = s'.trace) : TRel P A A' t t' :=
  ⟨ht, by rw [h1, h2]; exact h.2⟩

theorem trel_execStmt {sem : Sem} {P : Prog} {A A' : Layout} {s s' : St} (hR : TRel P A A' s s')
    (st : Stmt) (hst : st ∈ P.code) (hp : PtrsIn (AddrTaken P) s) (ha : s.alias = none) :
    TRel P A A' (execStmt sem P A s st) (execStmt sem P A' s' st) := by
  have hdisc := addrDisc_addrTaken P
  have hs' := hR.1.eq
  by_cases hs : s.status = .running
  · have hss : s'.status = .running := hR.1.status ▸ hs
    cases st with
    | call fn arg =>
      by_cases hip : sem.move = .inPlaceCall ∧ ∃ q, arg = .move q
      · obtain ⟨ms, am⟩ := sem
        obtain ⟨hms, q, rfl⟩ := hip
        simp only at hms
        subst hms
        rw [execStmt_callIP _ _ _ _ _ _ hs, execStmt_callIP _ _ _ _ _ _ hss]
        unfold callIP
        rw [hs']
        simp only [resolvePlace_trace]
        cases hres : resolvePlace P s q with
        | none => exact hR.of_teq (TEq.with_trace _ _) rfl rfl
        | some r =>
          simp only
          split
          · exact hR.of_teq (TEq.with_trace _ _) rfl rfl
          · have hrb : r.base = q.base := by rw [Inv.resolvePlace_base hres, ha]; rfl
            have hctx : TRel P A A' { s with alias := some ((P.fn fn).prm, r), inCall := true }
                { s with trace := s'.trace, alias := some ((P.fn fn).prm, r), inCall := true } :=
              ⟨rfl, hR.2⟩
            have hc := trel_execCallee (sem := ⟨.inPlaceCall, am⟩) (P.fn fn).body _ _ hctx hp
              (by
                intro st' hst' x hx
                simp only [aliasBase]
                split
                · rename_i hxp
                  rw [hrb]
                  exact hdisc.2.2 fn q hst (List.any_eq_true.2 ⟨st', hst', hxp ▸ hx⟩)
                · exact hdisc.2.1 fn st' hst' x hx)
            exact ⟨hc.1.setCtx none false, hc.2⟩
      · rw [execStmt_callCP _ _ _ _ _ _ hs hip, execStmt_callCP _ _ _ _ _ _ hss hip]
        unfold callCP
        rw [hs', evalOp_trace s'.trace sem.move P s arg]
        have hargd : ∀ x, arg.takesAddr x = true → AddrTaken P (aliasBase s.alias x) := by
          rw [ha]; intro x hx; exact hdisc.1 _ hst x (by simpa [Stmt.takesAddr] using hx)
        have h1 := evalOp_trace_eq sem.move P s arg
        rcases he : evalOp sem.move P s arg with ⟨s1, _ | vs⟩
        · rw [he] at h1
          simp only at h1
          exact hR.of_teq (TEq.with_trace _ _) h1 rfl
        · rw [he] at h1
          simp only at h1 ⊢
          obtain ⟨hp1, hv⟩ := Inv.ptrsIn_evalOp he hp hargd
          split
          · exact hR.of_teq (TEq.with_trace _ _) (by simp [St.fail, h1]) rfl
          · have hR1 : TRel P A A' s1 { s1 with trace := s'.trace } :=
              hR.of_teq (TEq.with_trace _ _) h1 rfl
            have hR2 := hR1.of_teq (allocate_teq P _ _ hR1.1 (P.fn fn).prm)
              (allocate_trace_eq _ _ _) (allocate_trace_eq _ _ _)
            have hR3 := hR2.of_teq (writeCells_teq _ _ hR2.1 (P.fn fn).prm 0 vs)
              (writeCellsK_trace_eq _ _ _ _ _) (writeCellsK_trace_eq _ _ _ _ _)
            have hR4 : TRel P A A' { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with
                inCall := true } { writeCells (allocate P { s1 with trace := s'.trace } (P.fn fn).prm)
                (P.fn fn).prm 0 vs with inCall := true } := ⟨hR3.1.setInCall true, hR3.2⟩
            have hp4 : PtrsIn (AddrTaken P) { writeCells (allocate P s1 (P.fn fn).prm)
                (P.fn fn).prm 0 vs with inCall := true } :=
              Inv.ptrsIn_writeCellsK _ _ _ _ (Inv.ptrsIn_allocate _ _ _ hp1) (hv vs rfl)
            have hal4 : ({ writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with
                inCall := true } : St).alias = none := by
              show (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias = none
              rw [(step_writeCells _ _ _ _).alias, (step_allocate _ _ _).alias, Inv.evalOp_alias he, ha]
            have hc := trel_execCallee (sem := sem) (P.fn fn).body _ _ hR4 hp4
              (by rw [hal4]; exact fun st' hst' x hx => hdisc.2.1 fn st' hst' x hx)
            have hR5 : TRel P A A' { execCallee sem P A { writeCells (allocate P s1 (P.fn fn).prm)
                (P.fn fn).prm 0 vs with inCall := true } (P.fn fn).body with inCall := false }
                { execCallee sem P A' { writeCells (allocate P { s1 with trace := s'.trace }
                (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true } (P.fn fn).body with
                inCall := false } := ⟨hc.1.setInCall false, hc.2⟩
            exact hR5.of_teq (deallocate_teq P _ _ hR5.1 _) (deallocate_trace_eq _ _ _)
              (deallocate_trace_eq _ _ _)
    | _ =>
      first
      | (rw [execStmt_basic _ _ _ _ _ (by intro fn a h; cases h),
            execStmt_basic _ _ _ _ _ (by intro fn a h; cases h)]
         refine trel_execBasic hR _ hp ?_
         rw [ha]
         exact fun x hx => hdisc.1 _ hst x hx)
  · rw [execStmt_of_not_running st hs,
      execStmt_of_not_running (s := s') st (by rw [← hR.1.status]; exact hs)]
    exact hR

theorem trel_run (sem : Sem) (P : Prog) (A A' : Layout) :
    TR P A A' (run sem P A).trace (run sem P A').trace := by
  have key : ∀ k, TRel P A A' (runAt sem P A k) (runAt sem P A' k) := by
    intro k
    induction k with
    | zero => rw [runAt_zero, runAt_zero]; exact ⟨rfl, TR.nil _ _ _⟩
    | succ k ih =>
      by_cases hk : k < P.code.length
      · rw [runAt_succ _ _ _ _ hk, runAt_succ _ _ _ _ hk]
        have hf := runAt_frame sem P A k (by omega)
        have h := trel_execStmt (sem := sem) ih P.code[k] (List.getElem_mem hk)
          (ptrsIn_runAt _ sem P A (addrDisc_addrTaken P) k) hf.2.2.1
        exact ⟨execTop_teq sem P A A' _ _ ih.1 _, h.2⟩
      · rw [runAt_of_le _ _ _ _ (by omega), runAt_of_le _ _ _ _ (by omega),
          ← runAt_of_le sem P A k (by omega), ← runAt_of_le sem P A' k (by omega)]
        exact ih
  rw [run_eq_runAt, run_eq_runAt]
  exact (key _).2

end Coal
namespace Coal

/-! ## Outcomes -/

theorem outcome_done {sem : Sem} {P : Prog} {A : Layout} {t : List Event}
    (h : outcome sem P A = .done t) :
    (run sem P A).status = .running ∧ (run sem P A).trace = t := by
  simp only [outcome] at h
  split at h
  · split at h
    · rename_i hs; cases h; exact ⟨hs, rfl⟩
    · cases h
  · cases h

theorem running_of_ubFree {sem : Sem} {P : Prog} (hsafe : ¬ Beh sem P .ub) (A : Layout) :
    (run sem P A).status = .running := by
  by_cases hs : (run sem P A).status = .running
  · exact hs
  · exact absurd (beh_ub_of_status sem P A (status_eq_ub_of_ne_running hs)) hsafe

theorem nvc_of_hi {ms : MoveSem} {μ : Forest} {P : Prog} (hi : NoValueClobberStmt ms μ P)
    {A : Layout} (hrun : (run ⟨ms, .atomic⟩ P A).status = .running) (A' : Layout) :
    NoValueClobber μ (run ⟨ms, .atomic⟩ P A').log := by
  have hrunG : (run ⟨ms, .atomic⟩ P (goodLayout P)).status = .running :=
    (run_status_running_iff _ P A _).1 hrun
  have hG := hi (goodLayout P)
    (by rw [outcome_of_running (layoutOK_goodLayout_run _ _ _) hrunG]; simp)
    (outcome_goodLayout_ne_badLayout _ _)
  rw [(run_teq ⟨ms, .atomic⟩ P (goodLayout P) A').log] at hG
  exact hG

/-! ## A source layout for a coalesced layout -/

theorem le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with h | h
    · subst h; simp
    · have := ih h; simp only [List.sum_cons]; omega

/-- A bound above every allocated window of the coalesced layout. -/
def bound (P : Prog) (A : Layout) : Nat := ((List.range P.nloc).map fun x => A x + P.size x).sum

theorem le_bound (P : Prog) (A : Layout) {x : Nat} (hx : x < P.nloc) : A x + P.size x ≤ bound P A :=
  le_sum_of_mem (List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩)

/-- Source layout: locals in no class and address-taken class members at their place inside the
root; the other class members far away. -/
def srcLayout (P : Prog) (μ : Forest) (A : Layout) : Layout := fun u =>
  if μ.inClass u = true then
    (if AddrTaken P u then A (μ.root u) + μ.offset u else bound P A + goodLayout P u)
  else A u

theorem srcLayout_agree (P : Prog) (μ : Forest) (A : Layout) (x : Nat) (hx : AddrTaken P x) :
    srcLayout P μ A x = hyb μ A x := by
  unfold srcLayout hyb
  cases hc : μ.inClass x
  · simp [root_of_not_inClass hc, offset_of_not_inClass hc]
  · simp [hx]

theorem disj_symm {a m b n : Nat} (h : Disj a m b n) : Disj b n a m := by
  unfold Disj at h ⊢; omega

theorem disj_pairIn {P : Prog} {A : Layout} {t : St} (hok : layoutOK P A t.conflicts = true)
    {a b : Nat} (h : PairIn t a b) : Disj (A a) (P.size a) (A b) (P.size b) := by
  simp only [layoutOK, List.all_eq_true, decide_eq_true_eq] at hok
  rcases h with h | h
  · exact hok _ h
  · exact disj_symm (hok _ h)

/-- Placement of a local in the source layout. -/
theorem srcLayout_cases {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (A : Layout) {x : Nat}
    (hx : x < P.nloc) :
    (srcLayout P μ A x = A (μ.root x) + μ.offset x ∧
      μ.offset x + P.size x ≤ P.size (μ.root x) ∧ μ.root x < P.nloc ∧
      (μ.inClass x = false ∨ AddrTaken P x)) ∨
    (srcLayout P μ A x = bound P A + goodLayout P x ∧ μ.inClass x = true ∧ ¬ AddrTaken P x) := by
  cases hc : μ.inClass x
  · left
    refine ⟨?_, offset_add_size_le hwf x, root_lt hwf hx, Or.inl rfl⟩
    simp [srcLayout, hc, root_of_not_inClass hc, offset_of_not_inClass hc]
  · by_cases ha : AddrTaken P x
    · left
      refine ⟨?_, offset_add_size_le hwf x, root_lt hwf hx, Or.inr ha⟩
      simp [srcLayout, hc, ha]
    · right
      refine ⟨?_, rfl, ha⟩
      simp [srcLayout, hc, ha]

theorem disj_covered {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (hii : ClassAddrDisjoint P μ)
    (A : Layout) {t : St} (hok : layoutOK P A t.conflicts = true) {x z : Nat}
    (hc : Covered P μ t x z) :
    Disj (srcLayout P μ A x) (P.size x) (srcLayout P μ A z) (P.size z) := by
  obtain ⟨hx, hz, hxz, hne, heq⟩ := hc
  have bx := le_bound P A (root_lt hwf hx)
  have bz := le_bound P A (root_lt hwf hz)
  have hg := disj_goodLayout P x z hxz
  unfold Disj at hg ⊢
  by_cases hr : μ.root x = μ.root z
  · have hxc : μ.inClass x = true := by
      cases h : μ.inClass x
      · rw [root_of_not_inClass h] at hr
        exact absurd (eq_of_root_eq_notClass h hr.symm).symm hxz
      · rfl
    have hzc : μ.inClass z = true := by
      cases h : μ.inClass z
      · rw [root_of_not_inClass h] at hr
        have := inClass_root hxc
        rw [hr, h] at this; cases this
      · rfl
    rcases srcLayout_cases hwf A hx with ⟨ex, sx, -, ax⟩ | ⟨ex, -, -⟩ <;>
      rcases srcLayout_cases hwf A hz with ⟨ez, sz, -, az⟩ | ⟨ez, -, -⟩
    · rw [hxc] at ax; rw [hzc] at az
      simp only [Bool.true_eq_false, false_or] at ax az
      by_cases hw : μ.windowsOverlap P x z = true
      · exact absurd (heq hr ax az hw) (hii x hx z hz hxz (by simp [Forest.sameClass, hxc, hzc, hr]) hw ax az)
      · simp only [Forest.windowsOverlap, decide_eq_true_eq] at hw
        rw [ex, ez, hr]; omega
    · rw [ex, ez]; rw [hr] at sx bx ⊢; omega
    · rw [ex, ez]; rw [← hr] at sz bz ⊢; omega
    · rw [ex, ez]; omega
  · have hp := disj_pairIn hok (hne hr)
    unfold Disj at hp
    rcases srcLayout_cases hwf A hx with ⟨ex, sx, -, -⟩ | ⟨ex, -, -⟩ <;>
      rcases srcLayout_cases hwf A hz with ⟨ez, sz, -, -⟩ | ⟨ez, -, -⟩
    · rw [ex, ez]; omega
    · rw [ex, ez]; omega
    · rw [ex, ez]; omega
    · rw [ex, ez]; omega

end Coal
open Coal

/-- Sufficiency for merge forests under atomic assignments and any `move` semantics: a
well-formed forest, the value-level condition `NoValueClobberStmt` and the root-level address check
`ClassAddrDisjoint` (pairs of address-taken class members with intersecting root-relative windows
are never lexically allocated during a common tick) give a refinement. -/
theorem coalesce_refines_of_noValueClobber_of_classAddrDisjoint (ms : MoveSem) (P : Prog)
    (μ : Forest) (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P)
    (hii : ClassAddrDisjoint P μ) :
    Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P := by
  apply refines_of_running
  intro A hA hrunAll
  have hrunH := hrunAll (hyb μ A)
  have hnvc := nvc_of_hi hi hrunH (hyb μ A)
  obtain ⟨hR, hE⟩ := core_sim hwf A hrunH hnvc
  have hokT := layoutOK_of_outcome_ne hA
  rw [outcome_of_running hokT hR.runT]
  refine ⟨srcLayout P μ A, ?_, by simp⟩
  have hokS : layoutOK P (srcLayout P μ A)
      (run ⟨ms, .atomic⟩ P (srcLayout P μ A)).conflicts = true := by
    rw [(run_teq ⟨ms, .atomic⟩ P (srcLayout P μ A) (hyb μ A)).conflicts]
    simp only [layoutOK, List.all_eq_true, decide_eq_true_eq]
    intro c hc
    exact disj_covered hwf hii A hokT (hE.cov c hc)
  rw [outcome_of_running hokS (hrunAll _), hR.trace]
  congr 1
  exact (trel_run _ P _ _).2 (srcLayout_agree P μ A)

/-- Address-free postconditions, original to coalesced: for a well-formed forest with the
value-level condition `NoValueClobberStmt` and no address condition at all, validity of an
address-free postcondition transfers from the source to the coalesced program (atomic
assignments). In this toy, absolute addresses reach nothing but printed pointer values and
comparison results; there is no address-dependent control flow, integer cast or indexing. -/
theorem vc_forward_addrFree_of_noValueClobber (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (Post : List Event → Prop)
    (hpost : AddrFree Post) (hv : Valid ⟨ms, .atomic⟩ P Post) :
    Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := by
  intro o ⟨A, hA, hb⟩
  obtain ⟨tS, htS, hPS⟩ := hv _ ⟨goodLayout P, rfl, outcome_goodLayout_ne_badLayout _ _⟩
  obtain ⟨hrunG, htrG⟩ := outcome_done htS
  have hrunH : (run ⟨ms, .atomic⟩ P (hyb μ A)).status = .running :=
    (run_status_running_iff _ P _ _).1 hrunG
  have hnvc := nvc_of_hi hi hrunG (hyb μ A)
  obtain ⟨hR, -⟩ := core_sim hwf A hrunH hnvc
  have hokT := layoutOK_of_outcome_ne
    (by rw [hA]; exact hb : outcome ⟨ms, .atomic⟩ (coalesce μ P) A ≠ .badLayout)
  refine ⟨(run ⟨ms, .atomic⟩ (coalesce μ P) A).trace, ?_, ?_⟩
  · rw [← hA, outcome_of_running hokT hR.runT]
  · rw [hR.trace]
    have he := (trel_run ⟨ms, .atomic⟩ P (hyb μ A) (goodLayout P)).1
    rw [htrG] at he
    exact (hpost _ _ he).2 hPS

/-- Address-free postconditions, coalesced to original: if moreover the source has no undefined
behaviour, validity of an address-free postcondition transfers back. -/
theorem vc_backward_addrFree_of_noValueClobber_of_ubFree (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hsafe : UBFree ⟨ms, .atomic⟩ P)
    (Post : List Event → Prop) (hpost : AddrFree Post)
    (hv : Valid ⟨ms, .atomic⟩ (coalesce μ P) Post) :
    Valid ⟨ms, .atomic⟩ P Post := by
  intro o ⟨A, hA, hb⟩
  have hrunA := running_of_ubFree hsafe A
  have hokA := layoutOK_of_outcome_ne
    (by rw [hA]; exact hb : outcome ⟨ms, .atomic⟩ P A ≠ .badLayout)
  have hnvc := nvc_of_hi hi hrunA (hyb μ (goodLayout (coalesce μ P)))
  have hrunH := (run_status_running_iff _ P A (hyb μ (goodLayout (coalesce μ P)))).1 hrunA
  obtain ⟨hR, -⟩ := core_sim hwf (goodLayout (coalesce μ P)) hrunH hnvc
  obtain ⟨tT, htT, hpostT⟩ :=
    hv _ ⟨goodLayout (coalesce μ P), rfl, outcome_goodLayout_ne_badLayout _ _⟩
  rw [outcome_of_running (layoutOK_goodLayout_run _ _ _) hR.runT] at htT
  simp only [Outcome.done.injEq] at htT
  subst htT
  refine ⟨(run ⟨ms, .atomic⟩ P A).trace, ?_, ?_⟩
  · rw [← hA, outcome_of_running hokA hrunA]
  · rw [hR.trace] at hpostT
    exact (hpost _ _ (trel_run ⟨ms, .atomic⟩ P (hyb μ (goodLayout (coalesce μ P))) A).1).1 hpostT

end Toy.Coalesce
