import Toy.PlaceEval.LazySim

/-!
# Storage-marker erasure: relating a run of `P` to a run of `eraseMarkers P x`

The source is a run of `P`, the target a run of `eraseMarkers P x`. Source allocations are
renamed to target allocations by a partial map `f`; every allocation of `x` in the source is
mapped to the target's single allocation of `x`. Source addresses are target addresses
shifted by `D` (`D = 0` for the refinement without address conditions; a large `D` when
addresses are not observed). Pointers satisfying `J` (pointers without provenance, and, with
a positive shift, pointer constants of the program) are related to themselves.

The relation is oriented for a forward simulation: whenever the source succeeds, the target
succeeds with a related result.
-/

namespace Toy.PlaceEval

/-! ## Relating lists pointwise -/

/-- Pointwise relation of two lists of the same length. -/
def LRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ LRel R as bs
  | _, _ => False

theorem lRel_map_range {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) (g : Nat → α) (h : Nat → β), (∀ i, i < n → R (g i) (h i)) →
      LRel R ((List.range n).map g) ((List.range n).map h)
  | 0, _, _, _ => trivial
  | n + 1, g, h, hr => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    exact ⟨hr 0 (Nat.succ_pos _), lRel_map_range n _ _ fun i hi => hr (i + 1) (by omega)⟩

/-! ## The value relation -/

/-- Related pointers: a source pointer into allocation `k` and a target pointer into `f k` at
the address shifted by `D` (the target address is positive when `D > 0`), or the same pointer
satisfying `J`. -/
def V1 (D : Nat) (J : Ptr → Prop) (f : Nat → Option Nat) (pS pT : Ptr) : Prop :=
  (∃ k k', f k = some k' ∧ pS = ⟨some k, pT.addr + D⟩ ∧ pT.prov = some k' ∧
      (D = 0 ∨ 0 < pT.addr)) ∨
  (pS = pT ∧ J pS)

/-- Related values. -/
def VV1 (D : Nat) (J : Ptr → Prop) (f : Nat → Option Nat) : Val → Val → Prop
  | .int n, .int m => n = m
  | .ptr p, .ptr q => V1 D J f p q
  | _, _ => False

/-- Related cells: an uninitialized source cell is related to every target cell. -/
def CR1 (D : Nat) (J : Ptr → Prop) (f : Nat → Option Nat) : Cell → Cell → Prop
  | .uninit, _ => True
  | .byte b, .byte b' => b = b'
  | .ptrFrag p i, .ptrFrag q j => i = j ∧ V1 D J f p q
  | _, _ => False

/-- Conditions on `D` and `J`: pointers without provenance satisfy `J`, and a pointer
satisfying `J` has no provenance or an address below `D`. -/
structure DJOk (D : Nat) (J : Ptr → Prop) : Prop where
  noprov : ∀ a, J ⟨none, a⟩
  small : ∀ p, J p → p.prov = none ∨ p.addr < D

/-- An alignment `al` is preserved by the shift `D`. -/
def AlOK (D al : Nat) : Prop := 0 < al → al ∣ D

/-- Related memories. -/
structure MRel (D : Nat) (J : Ptr → Prop) (f : Nat → Option Nat) (m n : Mem) : Prop where
  falloc : ∀ k k' (al : Alloc), f k = some k' → m.allocs[k]? = some al →
    ∃ al', n.allocs[k']? = some al' ∧ al.base = al'.base + D ∧ al.size = al'.size ∧
      (al.live = true → al'.live = true)
  cells : ∀ a, CR1 D J f (m.get (a + D)) (n.get a)
  junk : ∀ p, J p → ∀ k, 0 < k → m.inBounds p k = false
  tpos : D = 0 ∨ ∀ (k : Nat) (al : Alloc), n.allocs[k]? = some al → 0 < al.base

/-- Related frames: a source local backed by allocation `k` is backed by `f k` in the target. -/
def FrRel (f : Nat → Option Nat) (σ τ : State) : Prop :=
  ∀ y k, σ.allocOf y = some k → ∃ k', τ.allocOf y = some k' ∧ f k = some k'

section Transfer

variable {D : Nat} {J : Ptr → Prop} {f : Nat → Option Nat}

theorem Ptr.offset_zero (q : Ptr) : q.offset 0 = q := by
  cases q; simp [Ptr.offset]

theorem V1.functional (hdj : DJOk D J) {pS pT pT' : Ptr} (h : V1 D J f pS pT)
    (h' : V1 D J f pS pT') : pT = pT' := by
  rcases h with ⟨k, k', hk, rfl, hp, _⟩ | ⟨rfl, hj⟩ <;>
    rcases h' with ⟨l, l', hl, he, hp', _⟩ | ⟨he, hj'⟩
  · simp only [Ptr.mk.injEq, Option.some.injEq] at he
    obtain ⟨rfl, ha⟩ := he
    rw [hk] at hl
    cases hl
    cases pT; cases pT'
    simp only at hp hp' ha ⊢
    rw [hp, hp']
    simp only [Ptr.mk.injEq, true_and]
    omega
  · subst he
    rcases hdj.small _ hj' with h1 | h1
    · simp at h1
    · simp at h1; omega
  · subst he
    rcases hdj.small _ hj with h1 | h1
    · simp at h1
    · simp at h1; omega
  · exact he

theorem V1.offset {m : Mem} (hm : ∀ p, J p → ∀ k, 0 < k → m.inBounds p k = false) {pS pT : Ptr}
    (h : V1 D J f pS pT) {k : Nat} (hk : m.offsetInbounds pS k = true) :
    V1 D J f (pS.offset k) (pT.offset k) := by
  rcases h with ⟨k0, k', hk0, rfl, hp, hpos⟩ | ⟨rfl, hj⟩
  · refine Or.inl ⟨k0, k', hk0, ?_, hp, ?_⟩
    · simp only [Ptr.offset, Ptr.mk.injEq, true_and]; omega
    · rcases hpos with h | h
      · exact Or.inl h
      · right; simp only [Ptr.offset]; omega
  · by_cases hk0 : k = 0
    · subst hk0; rw [Ptr.offset_zero]; exact Or.inr ⟨rfl, hj⟩
    · have hk' : (k == 0) = false := by simp [hk0]
      simp only [Mem.offsetInbounds, hm _ hj k (Nat.pos_of_ne_zero hk0), hk', Bool.or_false] at hk
      cases hk

theorem inBounds_transfer {m n : Mem} (hm : MRel D J f m n) {pS pT : Ptr} (h : V1 D J f pS pT)
    {k : Nat} (hk : 0 < k) (hb : m.inBounds pS k = true) : n.inBounds pT k = true := by
  rcases h with ⟨k0, k', hk0, rfl, hp, _⟩ | ⟨rfl, hj⟩
  · simp only [Mem.inBounds] at hb
    cases hal : m.allocs[k0]? with
    | none => rw [hal] at hb; cases hb
    | some al =>
      rw [hal] at hb
      obtain ⟨al', hal', hb', hs', hl'⟩ := hm.falloc k0 k' al hk0 hal
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [Mem.inBounds, hp, hal', Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hl' hb.1.1, ?_⟩, ?_⟩ <;> omega
  · rw [hm.junk _ hj k hk] at hb; cases hb

theorem dereferenceable_transfer {m n : Mem} (hm : MRel D J f m n) {pS pT : Ptr}
    (h : V1 D J f pS pT) {k : Nat} (hb : m.dereferenceable pS k = true) :
    n.dereferenceable pT k = true := by
  by_cases hk : k = 0
  · subst hk; rfl
  · have hk' : (k == 0) = false := by simp [hk]
    simp only [Mem.dereferenceable, hk', Bool.false_or] at hb ⊢
    exact inBounds_transfer hm h (Nat.pos_of_ne_zero hk) hb

theorem aligned_shift {al a D : Nat} (hal : AlOK D al) (h : aligned al (a + D) = true) :
    aligned al a = true := by
  simp only [aligned, beq_iff_eq] at h ⊢
  by_cases h0 : al = 0
  · subst h0; simp at h ⊢; omega
  · obtain ⟨c, rfl⟩ := hal (Nat.pos_of_ne_zero h0)
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod] at h
    exact h

theorem aligned_transfer {pS pT : Ptr} (h : V1 D J f pS pT) {al : Nat} (hal : AlOK D al)
    (ha : aligned al pS.addr = true) : aligned al pT.addr = true := by
  rcases h with ⟨k0, k', _, rfl, _, _⟩ | ⟨rfl, _⟩
  · exact aligned_shift hal ha
  · exact ha

theorem readCells_transfer {m n : Mem} (hm : MRel D J f m n) {pS pT : Ptr} (h : V1 D J f pS pT)
    {k : Nat} (hb : m.dereferenceable pS k = true) :
    LRel (CR1 D J f) (m.readCells pS.addr k) (n.readCells pT.addr k) := by
  by_cases hk : k = 0
  · subst hk; trivial
  rcases h with ⟨k0, k', _, rfl, _, _⟩ | ⟨rfl, hj⟩
  · refine lRel_map_range k _ _ fun i _ => ?_
    have := hm.cells (pT.addr + i)
    rwa [show pT.addr + i + D = pT.addr + D + i by omega] at this
  · have hk' : (k == 0) = false := by simp [hk]
    have hj' := hm.junk _ hj k (Nat.pos_of_ne_zero hk)
    simp only [Mem.dereferenceable, hk', Bool.false_or] at hb
    rw [hj'] at hb; cases hb

theorem decodeLE_transfer : ∀ {cs ct : List Cell}, LRel (CR1 D J f) cs ct → ∀ {v : Nat},
    decodeLE cs = some v → decodeLE ct = some v
  | [], [], _, v, h => h
  | c :: cs, d :: ct, ⟨hc, hr⟩, v, h => by
    cases c with
    | byte b =>
      cases d with
      | byte b' =>
        simp only [CR1] at hc
        subst hc
        simp only [decodeLE] at h ⊢
        cases hd : decodeLE cs with
        | none => rw [hd] at h; cases h
        | some w => rw [hd] at h; rw [decodeLE_transfer hr hd]; exact h
      | _ => simp [CR1] at hc
    | _ => simp [decodeLE] at h
  | [], _ :: _, h, _, _ => absurd h id
  | _ :: _, [], h, _, _ => absurd h id

theorem decodePtr_bytes {c0 c1 : Cell} {p : Ptr} (h : decodePtr [c0, c1] = some p) :
    (∃ q, c0 = .ptrFrag q 0 ∧ c1 = .ptrFrag q 1 ∧ p = q) ∨
    (∃ b0 b1, c0 = .byte b0 ∧ c1 = .byte b1 ∧ p = ⟨none, b0 % 256 + 256 * (b1 % 256 + 256 * 0)⟩) := by
  cases c0 with
  | uninit => simp [decodePtr, decodeLE] at h
  | byte b0 =>
    cases c1 with
    | byte b1 =>
      right
      simp only [decodePtr, decodeLE, ptrSize, List.length_cons, List.length_nil, Option.map_some,
        ite_true] at h
      exact ⟨b0, b1, rfl, rfl, (Option.some.inj h).symm⟩
    | _ => simp [decodePtr, decodeLE] at h
  | ptrFrag q i =>
    cases c1 with
    | ptrFrag q' j =>
      cases i with
      | succ i => simp [decodePtr, decodeLE] at h
      | zero =>
        cases j with
        | zero => simp [decodePtr, decodeLE] at h
        | succ j =>
          cases j with
          | succ j => simp [decodePtr, decodeLE] at h
          | zero =>
            simp only [decodePtr] at h
            split at h
            · rename_i he
              subst he
              exact Or.inl ⟨q, rfl, rfl, (Option.some.inj h).symm⟩
            · cases h
    | _ => cases i <;> simp [decodePtr, decodeLE] at h

theorem decodePtr_length {cs : List Cell} {p : Ptr} (h : decodePtr cs = some p) : cs.length = 2 := by
  unfold decodePtr at h
  split at h
  · rfl
  · split at h
    · assumption
    · cases h

theorem decodePtr_transfer (hdj : DJOk D J) {cs ct : List Cell} (hr : LRel (CR1 D J f) cs ct)
    {p : Ptr} (h : decodePtr cs = some p) : ∃ q, decodePtr ct = some q ∧ V1 D J f p q := by
  have hlen := decodePtr_length h
  match cs, ct, hr, h, hlen with
  | [c0, c1], [d0, d1], ⟨h0, h1, _⟩, h, _ =>
    rcases decodePtr_bytes h with ⟨q, rfl, rfl, rfl⟩ | ⟨b0, b1, rfl, rfl, rfl⟩
    · cases d0 with
      | ptrFrag r i =>
        cases d1 with
        | ptrFrag r' j =>
          obtain ⟨rfl, h0⟩ := h0
          obtain ⟨rfl, h1⟩ := h1
          have := V1.functional hdj h0 h1
          subst this
          exact ⟨r, by simp [decodePtr], h0⟩
        | _ => simp [CR1] at h1
      | _ => simp [CR1] at h0
    · cases d0 with
      | byte b0' =>
        cases d1 with
        | byte b1' =>
          simp only [CR1] at h0 h1
          subst h0; subst h1
          exact ⟨_, by simp [decodePtr, decodeLE, ptrSize], Or.inr ⟨rfl, hdj.noprov _⟩⟩
        | _ => simp [CR1] at h1
      | _ => simp [CR1] at h0
  | [_, _], [], h', _, _ => exact absurd h' id
  | [_, _], [_], h', _, _ => exact absurd h'.2 id
  | [_, _], _ :: _ :: _ :: _, h', _, _ => exact absurd h'.2.2 id

theorem decode_transfer (hdj : DJOk D J) {cs ct : List Cell} (hr : LRel (CR1 D J f) cs ct)
    (τ : Ty) {v : Val} (h : τ.decode cs = some v) : ∃ v', τ.decode ct = some v' ∧ VV1 D J f v v' := by
  cases τ with
  | int s a =>
    simp only [Ty.decode] at h ⊢
    cases hd : decodeLE cs with
    | none => rw [hd] at h; cases h
    | some w =>
      rw [hd] at h; cases h
      exact ⟨.int w, by rw [decodeLE_transfer hr hd]; rfl, rfl⟩
  | ptr =>
    simp only [Ty.decode] at h ⊢
    cases hd : decodePtr cs with
    | none => rw [hd] at h; cases h
    | some w =>
      rw [hd] at h; cases h
      obtain ⟨q, hq, hv⟩ := decodePtr_transfer hdj hr hd
      exact ⟨.ptr q, by rw [hq]; rfl, hv⟩
  | enum s a valid =>
    simp only [Ty.decode] at h ⊢
    cases hd : decodeLE cs with
    | none => rw [hd] at h; cases h
    | some w =>
      rw [hd] at h
      rw [decodeLE_transfer hr hd]
      simp only at h ⊢
      split at h
      · cases h; rename_i hw; exact ⟨.int w, by simp [hw], rfl⟩
      · cases h

theorem load_transfer (hdj : DJOk D J) {m n : Mem} (hm : MRel D J f m n) {pS pT : Ptr}
    (h : V1 D J f pS pT) {τ : Ty} (hal : AlOK D τ.align) {v : Val} (hl : m.load pS τ = some v) :
    ∃ v', n.load pT τ = some v' ∧ VV1 D J f v v' := by
  simp only [Mem.load] at hl ⊢
  split at hl
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    have hc' : (n.dereferenceable pT τ.size && aligned τ.align pT.addr) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨dereferenceable_transfer hm h hc.1, aligned_transfer h hal hc.2⟩
    simp only [hc', ↓reduceIte]
    exact decode_transfer hdj (readCells_transfer hm h hc.1) τ hl
  · cases hl

theorem loadPtr_transfer (hdj : DJOk D J) {m n : Mem} (hm : MRel D J f m n) {pS pT : Ptr}
    (h : V1 D J f pS pT) (hal : AlOK D ptrAlign) {r : Ptr} (hl : m.loadPtr pS = some r) :
    ∃ r', n.loadPtr pT = some r' ∧ V1 D J f r r' := by
  simp only [Mem.loadPtr] at hl ⊢
  split at hl
  · rename_i r0 he
    cases hl
    obtain ⟨v', hv', hvv⟩ := load_transfer hdj hm h (τ := .ptr) hal he
    rw [hv']
    cases v' with
    | ptr r' => exact ⟨r', rfl, hvv⟩
    | int _ => simp [VV1] at hvv
  · cases hl

theorem basePtr_transfer {σ τ : State} (hm : MRel D J f σ.mem τ.mem) (hfr : FrRel f σ τ)
    {y : Local} {pS : Ptr} (h : σ.basePtr y = some pS) :
    ∃ pT, τ.basePtr y = some pT ∧ V1 D J f pS pT := by
  simp only [State.basePtr] at h
  split at h
  · cases h
  · rename_i k hk
    cases hal : σ.mem.allocs[k]? with
    | none => rw [hal] at h; cases h
    | some al =>
      rw [hal] at h
      cases h
      obtain ⟨k', hk', hf⟩ := hfr y k hk
      obtain ⟨al', hal', hb, _, _⟩ := hm.falloc k k' al hf hal
      refine ⟨⟨some k', al'.base⟩, by simp [State.basePtr, hk', hal'], Or.inl ⟨k, k', hf, ?_, rfl, ?_⟩⟩
      · simp [hb]
      · rcases hm.tpos with h0 | hpos
        · exact Or.inl h0
        · exact Or.inr (hpos k' al' hal')

theorem readIndex_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) {j : Local} {v : Nat} (h : σ.readIndex j = some v) :
    τ.readIndex j = some v := by
  simp only [State.readIndex, State.readLocal] at h ⊢
  cases hb : σ.basePtr j with
  | none => rw [hb] at h; simp at h
  | some pS =>
    obtain ⟨pT, hpT, hv⟩ := basePtr_transfer hm hfr hb
    rw [hpT]
    rw [hb] at h
    simp only [Option.bind_some] at h ⊢
    cases hl : σ.mem.load pS idxTy with
    | none => rw [hl] at h; simp at h
    | some w =>
      rw [hl] at h
      obtain ⟨w', hw', hww⟩ := load_transfer hdj hm hv (by simp [AlOK, idxTy, Ty.align]) hl
      rw [hw']
      cases w with
      | int a =>
        cases w' with
        | int b => simp only [VV1] at hww; subst hww; exact h
        | ptr _ => simp [VV1] at hww
      | ptr _ => simp at h

theorem projStep_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) (hal : AlOK D ptrAlign) {pS pT : Ptr} (h : V1 D J f pS pT) (π : Proj)
    {q : Ptr} (hq : projStep σ pS π = some q) : ∃ q', projStep τ pT π = some q' ∧ V1 D J f q q' := by
  cases π with
  | deref => exact loadPtr_transfer hdj hm h hal hq
  | field off =>
    simp only [projStep] at hq ⊢
    split at hq
    · rename_i hb
      cases hq
      have hb' : τ.mem.offsetInbounds pT off = true := dereferenceable_transfer hm h hb
      simp only [hb', ↓reduceIte]
      exact ⟨_, rfl, V1.offset hm.junk h hb⟩
    · cases hq
  | index j sz =>
    simp only [projStep] at hq ⊢
    cases hi : σ.readIndex j with
    | none => rw [hi] at hq; cases hq
    | some v =>
      rw [hi] at hq
      rw [readIndex_transfer hdj hm hfr hi]
      simp only at hq ⊢
      split at hq
      · rename_i hb
        cases hq
        have hb' : τ.mem.offsetInbounds pT (v * sz) = true := dereferenceable_transfer hm h hb
        simp only [hb', ↓reduceIte]
        exact ⟨_, rfl, V1.offset hm.junk h hb⟩
      · cases hq

theorem evalProjs_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) (hal : AlOK D ptrAlign) :
    ∀ (πs : List Proj) {pS pT : Ptr}, V1 D J f pS pT → ∀ {q : Ptr}, evalProjs σ pS πs = some q →
      ∃ q', evalProjs τ pT πs = some q' ∧ V1 D J f q q'
  | [], pS, pT, h, q, hq => by cases hq; exact ⟨pT, rfl, h⟩
  | π :: πs, pS, pT, h, q, hq => by
    simp only [evalProjs] at hq ⊢
    cases h1 : projStep σ pS π with
    | none => rw [h1] at hq; cases hq
    | some q1 =>
      rw [h1] at hq
      obtain ⟨q1', h1', hv1⟩ := projStep_transfer hdj hm hfr hal h π h1
      rw [h1']
      exact evalProjs_transfer hdj hm hfr hal πs hv1 hq

theorem evalPlace_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) (hal : AlOK D ptrAlign) (p : Place) {q : Ptr}
    (hq : evalPlace σ p = some q) : ∃ q', evalPlace τ p = some q' ∧ V1 D J f q q' := by
  simp only [evalPlace] at hq ⊢
  cases hb : σ.basePtr p.base with
  | none => rw [hb] at hq; cases hq
  | some pS =>
    rw [hb] at hq
    obtain ⟨pT, hpT, hv⟩ := basePtr_transfer hm hfr hb
    rw [hpT]
    exact evalProjs_transfer hdj hm hfr hal p.proj hv hq

end Transfer

/-! ## Operands, right-hand sides and stores -/

/-- A constant that is related to itself: an integer, or a pointer satisfying `J`. -/
def ConstOK (J : Ptr → Prop) : Val → Prop
  | .int _ => True
  | .ptr q => J q

/-- Conditions on an operand under which its evaluation transfers. -/
def OpOK (D : Nat) (J : Ptr → Prop) : Operand → Prop
  | .copy _ τ => AlOK D τ.align
  | .const v => ConstOK J v

/-- Conditions on a right-hand side: address observations need `D = 0`. -/
def RvOK (D : Nat) (J : Ptr → Prop) : Rvalue → Prop
  | .use o => OpOK D J o
  | .rawRef _ => True
  | .ref _ L => AlOK D L.align
  | .ptrEq a b => D = 0 ∧ OpOK D J a ∧ OpOK D J b
  | .addrOf a => D = 0 ∧ OpOK D J a

/-- Conditions on a statement. -/
def StmtOK (D : Nat) (J : Ptr → Prop) : Stmt → Prop
  | .assign _ τ rv => AlOK D τ.align ∧ RvOK D J rv
  | .emit rv => RvOK D J rv
  | _ => True

/-- Conditions on a terminator. -/
def TermOK (D : Nat) (J : Ptr → Prop) : Term → Prop
  | .switchInt o _ _ => OpOK D J o
  | _ => True

section Transfer2

variable {D : Nat} {J : Ptr → Prop} {f : Nat → Option Nat}

theorem V1.addr_ne_zero {pS pT : Ptr} (h : V1 D J f pS pT) (h0 : pS.addr ≠ 0) : pT.addr ≠ 0 := by
  rcases h with ⟨k, k', _, rfl, _, hpos⟩ | ⟨rfl, _⟩
  · rcases hpos with h | h
    · subst h; simpa using h0
    · omega
  · exact h0

theorem V1.addr_eq {pS pT : Ptr} (hD : D = 0) (h : V1 D J f pS pT) : pS.addr = pT.addr := by
  rcases h with ⟨k, k', _, rfl, _, _⟩ | ⟨rfl, _⟩
  · simp [hD]
  · rfl

theorem operand_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) (hal : AlOK D ptrAlign) {o : Operand} (ho : OpOK D J o) {v : Val}
    (h : o.eval σ = some v) : ∃ v', o.eval τ = some v' ∧ VV1 D J f v v' := by
  cases o with
  | copy p τ' =>
    simp only [Operand.eval] at h ⊢
    cases hp : evalPlace σ p with
    | none => rw [hp] at h; cases h
    | some q =>
      rw [hp] at h
      obtain ⟨q', hq', hv⟩ := evalPlace_transfer hdj hm hfr hal p hp
      rw [hq']
      exact load_transfer hdj hm hv ho h
  | const c =>
    simp only [Operand.eval] at h ⊢
    cases h
    refine ⟨v, rfl, ?_⟩
    cases v with
    | int n => rfl
    | ptr q => exact Or.inr ⟨rfl, ho⟩

theorem evalInt_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) (hal : AlOK D ptrAlign) {o : Operand} (ho : OpOK D J o) {n : Nat}
    (h : o.evalInt σ = some n) : o.evalInt τ = some n := by
  simp only [Operand.evalInt] at h ⊢
  cases he : o.eval σ with
  | none => rw [he] at h; cases h
  | some v =>
    rw [he] at h
    obtain ⟨v', hv', hvv⟩ := operand_transfer hdj hm hfr hal ho he
    rw [hv']
    cases v with
    | int a =>
      cases v' with
      | int b => simp only [VV1] at hvv; subst hvv; exact h
      | ptr _ => simp [VV1] at hvv
    | ptr _ => simp at h

theorem rvalue_transfer (hdj : DJOk D J) {σ τ : State} (hm : MRel D J f σ.mem τ.mem)
    (hfr : FrRel f σ τ) (hal : AlOK D ptrAlign) {rv : Rvalue} (hr : RvOK D J rv) {v : Val}
    (h : rv.eval σ = some v) : ∃ v', rv.eval τ = some v' ∧ VV1 D J f v v' := by
  cases rv with
  | use o => exact operand_transfer hdj hm hfr hal hr h
  | rawRef p =>
    simp only [Rvalue.eval] at h ⊢
    cases hp : evalPlace σ p with
    | none => rw [hp] at h; cases h
    | some q =>
      rw [hp] at h
      cases h
      obtain ⟨q', hq', hv⟩ := evalPlace_transfer hdj hm hfr hal p hp
      exact ⟨.ptr q', by rw [hq']; rfl, hv⟩
  | ref p L =>
    simp only [Rvalue.eval] at h ⊢
    cases hp : evalPlace σ p with
    | none => rw [hp] at h; cases h
    | some q =>
      rw [hp] at h
      obtain ⟨q', hq', hv⟩ := evalPlace_transfer hdj hm hfr hal p hp
      rw [hq']
      simp only [Option.bind_some] at h ⊢
      split at h
      · rename_i hok
        cases h
        have hok' : RefOk τ.mem q' L :=
          ⟨hv.addr_ne_zero hok.1, aligned_transfer hv hr hok.2.1,
            dereferenceable_transfer hm hv hok.2.2⟩
        simp only [hok', ↓reduceIte]
        exact ⟨.ptr q', rfl, hv⟩
      · cases h
  | ptrEq a b =>
    obtain ⟨hD, ha, hb⟩ := hr
    simp only [Rvalue.eval] at h ⊢
    cases hea : a.eval σ with
    | none => rw [hea] at h; cases h
    | some va =>
      cases heb : b.eval σ with
      | none => rw [hea, heb] at h; cases va <;> cases h
      | some vb =>
        obtain ⟨va', hva', hvva⟩ := operand_transfer hdj hm hfr hal ha hea
        obtain ⟨vb', hvb', hvvb⟩ := operand_transfer hdj hm hfr hal hb heb
        rw [hea, heb] at h
        rw [hva', hvb']
        cases va with
        | int _ => cases h
        | ptr q =>
          cases vb with
          | int _ => cases h
          | ptr r =>
            cases va' with
            | int _ => simp [VV1] at hvva
            | ptr q' =>
              cases vb' with
              | int _ => simp [VV1] at hvvb
              | ptr r' =>
                cases h
                simp only [VV1] at hvva hvvb
                rw [hvva.addr_eq hD, hvvb.addr_eq hD]
                exact ⟨_, rfl, rfl⟩
  | addrOf a =>
    obtain ⟨hD, ha⟩ := hr
    simp only [Rvalue.eval] at h ⊢
    cases hea : a.eval σ with
    | none => rw [hea] at h; cases h
    | some va =>
      obtain ⟨va', hva', hvva⟩ := operand_transfer hdj hm hfr hal ha hea
      rw [hea] at h
      rw [hva']
      cases va with
      | int _ => cases h
      | ptr q =>
        cases va' with
        | int _ => simp [VV1] at hvva
        | ptr q' =>
          cases h
          simp only [VV1] at hvva
          rw [hvva.addr_eq hD]
          exact ⟨_, rfl, rfl⟩

/-- The cell at `b` after writing `cs` from `a`. -/
theorem get_writeCells (m : Mem) (a : Nat) (cs : List Cell) (b : Nat) :
    (m.writeCells a cs).get b =
      if a ≤ b ∧ b < a + cs.length then (cs[b - a]?).getD .uninit else m.get b := by
  induction cs generalizing a with
  | nil =>
    simp only [Mem.writeCells, placeCells, List.nil_append, List.length_nil, Nat.add_zero,
      show ¬ (a ≤ b ∧ b < a) by omega, ↓reduceIte, Mem.get]
  | cons c cs ih =>
    have e : (m.writeCells a (c :: cs)).get b =
        if a = b then c else (m.writeCells (a + 1) cs).get b := by
      simp only [Mem.writeCells, Mem.get, placeCells, List.cons_append, List.find?_cons]
      by_cases h : a = b
      · subst h; simp
      · have hb : (a == b) = false := by simp [h]
        simp [hb, h]
    rw [e, ih]
    by_cases h : a = b
    · subst h; simp
    · simp only [h, ↓reduceIte, List.length_cons]
      by_cases h2 : a + 1 ≤ b ∧ b < a + 1 + cs.length
      · have h3 : a ≤ b ∧ b < a + (cs.length + 1) := by omega
        simp only [h2, h3, and_self, ↓reduceIte]
        have : b - a = (b - (a + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      · have h3 : ¬ (a ≤ b ∧ b < a + (cs.length + 1)) := by omega
        simp only [h2, h3, ↓reduceIte]

theorem encode_length (n : Nat) (v : Val) : (v.encode n).length = n := by
  cases v with
  | int w =>
    simp only [Val.encode]
    induction n generalizing w with
    | zero => rfl
    | succ n ih => simp [encodeLE, ih]
  | ptr q => simp [Val.encode]

theorem encodeLE_getElem? : ∀ (n w i : Nat), (encodeLE n w)[i]? = none ∨
    ∃ b, (encodeLE n w)[i]? = some (.byte b)
  | 0, _, _ => Or.inl rfl
  | n + 1, w, 0 => Or.inr ⟨_, rfl⟩
  | n + 1, w, i + 1 => by
    simp only [encodeLE, List.getElem?_cons_succ]
    exact encodeLE_getElem? n _ i

theorem encode_rel {vS vT : Val} (hv : VV1 D J f vS vT) (n i : Nat) :
    CR1 D J f (((vS.encode n)[i]?).getD .uninit) (((vT.encode n)[i]?).getD .uninit) := by
  cases vS with
  | int a =>
    cases vT with
    | int b =>
      simp only [VV1] at hv
      subst hv
      simp only [Val.encode]
      rcases encodeLE_getElem? n a i with h | ⟨c, h⟩ <;> rw [h] <;> simp [CR1]
    | ptr _ => simp [VV1] at hv
  | ptr q =>
    cases vT with
    | int _ => simp [VV1] at hv
    | ptr r =>
      simp only [VV1] at hv
      simp only [Val.encode, List.getElem?_map]
      by_cases hi : i < n <;> simp [hi, CR1, hv]

theorem store_transfer {m n : Mem} (hm : MRel D J f m n) {pS pT : Ptr} (h : V1 D J f pS pT)
    {vS vT : Val} (hv : VV1 D J f vS vT) {τ : Ty} (hal : AlOK D τ.align) {m' : Mem}
    (hs : m.store pS τ vS = some m') :
    ∃ n', n.store pT τ vT = some n' ∧ MRel D J f m' n' ∧ m'.allocs = m.allocs ∧
      n'.allocs = n.allocs := by
  simp only [Mem.store] at hs ⊢
  split at hs
  · rename_i hc
    cases hs
    simp only [Bool.and_eq_true] at hc
    have hc' : (n.dereferenceable pT τ.size && aligned τ.align pT.addr) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨dereferenceable_transfer hm h hc.1, aligned_transfer h hal hc.2⟩
    simp only [hc', ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hm.falloc, fun t => ?_, hm.junk, hm.tpos⟩, rfl, rfl⟩
    rw [get_writeCells, get_writeCells, encode_length, encode_length]
    rcases h with ⟨k, k', _, rfl, _, _⟩ | ⟨rfl, hj⟩
    · simp only
      by_cases hin : pT.addr ≤ t ∧ t < pT.addr + τ.size
      · have hin' : pT.addr + D ≤ t + D ∧ t + D < pT.addr + D + τ.size := by omega
        simp only [hin, hin', and_self, ↓reduceIte]
        rw [show t + D - (pT.addr + D) = t - pT.addr by omega]
        exact encode_rel hv _ _
      · have hin' : ¬ (pT.addr + D ≤ t + D ∧ t + D < pT.addr + D + τ.size) := by omega
        simp only [hin, hin', ↓reduceIte]
        exact hm.cells t
    · rcases Nat.eq_zero_or_pos τ.size with h0 | hpos
      · have e1 : ¬ (pS.addr ≤ t + D ∧ t + D < pS.addr + τ.size) := by omega
        have e2 : ¬ (pS.addr ≤ t ∧ t < pS.addr + τ.size) := by omega
        simp only [e1, e2, ↓reduceIte]
        exact hm.cells t
      · have hk' : (τ.size == 0) = false := by simp; omega
        have := hc.1
        have hj' := hm.junk _ hj _ hpos
        simp only [Mem.dereferenceable, hk', Bool.false_or] at this
        rw [hj'] at this
        cases this
  · cases hs

end Transfer2

end Toy.PlaceEval
