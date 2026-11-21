import Toy.PlaceEval.MarkerFwd

/-!
# Storage-marker erasure, reverse direction: memory relation and transfer lemmas

Here the source is a run of `eraseMarkers P x` and the target a run of `P`. A target
allocation `kT` is related by `g kT = some (kS, bS, bT)` to the source allocation `kS`, where
`bS` and `bT` are the two base addresses (the shift is not uniform: every allocation of `x`
in the target is related to the source's single allocation of `x`). Pointers satisfying `J`
are related to themselves.

The lemmas are stated for the case that both runs succeed: if the source and the target both
succeed, their results are related. (The target never reaches UB in this simulation; the
source may.)
-/

namespace Toy.PlaceEval

/-- Related pointers (source, target). -/
def V2 (J : Ptr → Prop) (g : Nat → Option (Nat × Nat × Nat)) (pS pT : Ptr) : Prop :=
  (∃ kT kS bS bT, g kT = some (kS, bS, bT) ∧ pT.prov = some kT ∧ pS.prov = some kS ∧
    pS.addr + bT = pT.addr + bS) ∨
  (pS = pT ∧ J pS)

/-- Related values. -/
def VV2 (J : Ptr → Prop) (g : Nat → Option (Nat × Nat × Nat)) : Val → Val → Prop
  | .int n, .int m => n = m
  | .ptr p, .ptr q => V2 J g p q
  | _, _ => False

/-- Related cells: an uninitialized cell on either side is related to everything. -/
def CR2 (J : Ptr → Prop) (g : Nat → Option (Nat × Nat × Nat)) : Cell → Cell → Prop
  | .uninit, _ => True
  | .byte _, .uninit => True
  | .ptrFrag _ _, .uninit => True
  | .byte b, .byte b' => b = b'
  | .ptrFrag p i, .ptrFrag q j => i = j ∧ V2 J g p q
  | _, _ => False

/-- Related memories (source `m`, target `n`). -/
structure MRel2 (J : Ptr → Prop) (g : Nat → Option (Nat × Nat × Nat)) (m n : Mem) : Prop where
  gbase : ∀ kT kS bS bT, g kT = some (kS, bS, bT) →
    (∃ alS : Alloc, m.allocs[kS]? = some alS ∧ alS.base = bS) ∧
    (∃ alT : Alloc, n.allocs[kT]? = some alT ∧ alT.base = bT)
  gsize : ∀ kT kS bS bT (alS alT : Alloc), g kT = some (kS, bS, bT) → m.allocs[kS]? = some alS →
    n.allocs[kT]? = some alT → alS.size = alT.size
  cells : ∀ kT kS bS bT (alS alT : Alloc), g kT = some (kS, bS, bT) → m.allocs[kS]? = some alS →
    n.allocs[kT]? = some alT → alS.live = true → alT.live = true → ∀ i, i < alT.size →
    CR2 J g (m.get (bS + i)) (n.get (bT + i))
  junk : ∀ p, J p → ∀ k, 0 < k → m.inBounds p k = false
  sdisj : TDisj (.fresh fun _ => 0) m
  tdisj : TDisj (.fresh fun _ => 0) n
  ginj : ∀ kT1 kT2 kS b1 b1' b2 b2' (a1 a2 : Alloc), g kT1 = some (kS, b1, b1') →
    g kT2 = some (kS, b2, b2') → n.allocs[kT1]? = some a1 → n.allocs[kT2]? = some a2 →
    a1.live = true → a2.live = true → kT1 = kT2

/-- Related frames: locals allocated in both are backed by related allocations. -/
def FrRel2 (g : Nat → Option (Nat × Nat × Nat)) (σ τ : State) : Prop :=
  ∀ y kS kT, σ.allocOf y = some kS → τ.allocOf y = some kT → ∃ bS bT, g kT = some (kS, bS, bT)

section Transfer

variable {J : Ptr → Prop} {g : Nat → Option (Nat × Nat × Nat)}

theorem V2.offset {m : Mem} (hm : ∀ p, J p → ∀ k, 0 < k → m.inBounds p k = false) {pS pT : Ptr}
    (h : V2 J g pS pT) {k : Nat} (hk : m.offsetInbounds pS k = true) :
    V2 J g (pS.offset k) (pT.offset k) := by
  rcases h with ⟨kT, kS, bS, bT, hg, h1, h2, h3⟩ | ⟨rfl, hj⟩
  · exact Or.inl ⟨kT, kS, bS, bT, hg, h1, h2, by simp only [Ptr.offset]; omega⟩
  · by_cases hk0 : k = 0
    · subst hk0; rw [Ptr.offset_zero]; exact Or.inr ⟨rfl, hj⟩
    · have hk' : (k == 0) = false := by simp [hk0]
      simp only [Mem.offsetInbounds, hm _ hj k (Nat.pos_of_ne_zero hk0), hk', Bool.or_false] at hk
      cases hk

theorem inBounds_some {m : Mem} {p : Ptr} {n : Nat} (h : m.inBounds p n = true) :
    ∃ (k : Nat) (al : Alloc), p.prov = some k ∧ m.allocs[k]? = some al ∧ al.live = true ∧
      al.base ≤ p.addr ∧ p.addr + n ≤ al.base + al.size := by
  unfold Mem.inBounds at h
  cases hp : p.prov with
  | none => rw [hp] at h; cases h
  | some k =>
    rw [hp] at h
    simp only at h
    cases ha : m.allocs[k]? with
    | none => rw [ha] at h; cases h
    | some al =>
      rw [ha] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨k, al, rfl, ha, h.1.1, h.1.2, h.2⟩

theorem readCells_transfer2 {m n : Mem} (hm : MRel2 J g m n) {pS pT : Ptr} (h : V2 J g pS pT)
    {k : Nat} (hbS : m.dereferenceable pS k = true) (hbT : n.dereferenceable pT k = true) :
    LRel (CR2 J g) (m.readCells pS.addr k) (n.readCells pT.addr k) := by
  by_cases hk : k = 0
  · subst hk; trivial
  have hk' : (k == 0) = false := by simp [hk]
  simp only [Mem.dereferenceable, hk', Bool.false_or] at hbS hbT
  rcases h with ⟨kT, kS, bS, bT, hg, h1, h2, h3⟩ | ⟨rfl, hj⟩
  · obtain ⟨kS', alS, e1, e2, e3, e4, e5⟩ := inBounds_some hbS
    obtain ⟨kT', alT, f1, f2, f3, f4, f5⟩ := inBounds_some hbT
    rw [h2] at e1; cases e1
    rw [h1] at f1; cases f1
    obtain ⟨⟨alS', g1, g2⟩, ⟨alT', g3, g4⟩⟩ := hm.gbase kT kS bS bT hg
    rw [e2] at g1; cases g1
    rw [f2] at g3; cases g3
    refine lRel_map_range k _ _ fun i hi => ?_
    have := hm.cells kT kS bS bT alS alT hg e2 f2 e3 f3 (pT.addr - bT + i) (by omega)
    rwa [show bS + (pT.addr - bT + i) = pS.addr + i by omega,
      show bT + (pT.addr - bT + i) = pT.addr + i by omega] at this
  · rw [hm.junk _ hj k (Nat.pos_of_ne_zero hk)] at hbS; cases hbS

theorem decodeLE_transfer2 : ∀ {cs ct : List Cell}, LRel (CR2 J g) cs ct → ∀ {v w : Nat},
    decodeLE cs = some v → decodeLE ct = some w → v = w
  | [], [], _, v, w, h1, h2 => by simp [decodeLE] at h1 h2; omega
  | c :: cs, d :: ct, ⟨hc, hr⟩, v, w, h1, h2 => by
    cases c with
    | byte b =>
      cases d with
      | byte b' =>
        simp only [CR2] at hc
        subst hc
        simp only [decodeLE] at h1 h2
        cases e1 : decodeLE cs with
        | none => rw [e1] at h1; cases h1
        | some v1 =>
          cases e2 : decodeLE ct with
          | none => rw [e2] at h2; cases h2
          | some w1 =>
            rw [e1] at h1; rw [e2] at h2
            cases h1; cases h2
            rw [decodeLE_transfer2 hr e1 e2]
      | _ => simp [decodeLE] at h2
    | _ => simp [decodeLE] at h1
  | [], _ :: _, h, _, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _, _ => absurd h id

theorem decodePtr_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {cs ct : List Cell}
    (hr : LRel (CR2 J g) cs ct) {p q : Ptr} (h1 : decodePtr cs = some p)
    (h2 : decodePtr ct = some q) : V2 J g p q := by
  have l1 := decodePtr_length h1
  have l2 := decodePtr_length h2
  match cs, ct, hr, h1, h2, l1, l2 with
  | [c0, c1], [d0, d1], ⟨e0, e1, _⟩, h1, h2, _, _ =>
    rcases decodePtr_bytes h1 with ⟨q1, rfl, rfl, rfl⟩ | ⟨b0, b1, rfl, rfl, rfl⟩ <;>
      rcases decodePtr_bytes h2 with ⟨q2, rfl, rfl, rfl⟩ | ⟨b0', b1', rfl, rfl, rfl⟩
    · exact e0.2
    · simp [CR2] at e0
    · simp [CR2] at e0
    · simp only [CR2] at e0 e1
      subst e0; subst e1
      exact Or.inr ⟨rfl, hJ _⟩

theorem decode_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {cs ct : List Cell} (hr : LRel (CR2 J g) cs ct)
    (τ : Ty) {v w : Val} (h1 : τ.decode cs = some v) (h2 : τ.decode ct = some w) : VV2 J g v w := by
  cases τ with
  | int s a =>
    simp only [Ty.decode] at h1 h2
    cases e1 : decodeLE cs with
    | none => rw [e1] at h1; cases h1
    | some v1 =>
      cases e2 : decodeLE ct with
      | none => rw [e2] at h2; cases h2
      | some w1 =>
        rw [e1] at h1; rw [e2] at h2
        cases h1; cases h2
        exact decodeLE_transfer2 hr e1 e2
  | ptr =>
    simp only [Ty.decode] at h1 h2
    cases e1 : decodePtr cs with
    | none => rw [e1] at h1; cases h1
    | some v1 =>
      cases e2 : decodePtr ct with
      | none => rw [e2] at h2; cases h2
      | some w1 =>
        rw [e1] at h1; rw [e2] at h2
        cases h1; cases h2
        exact decodePtr_transfer2 hJ hr e1 e2
  | enum s a valid =>
    simp only [Ty.decode] at h1 h2
    cases e1 : decodeLE cs with
    | none => rw [e1] at h1; cases h1
    | some v1 =>
      cases e2 : decodeLE ct with
      | none => rw [e2] at h2; cases h2
      | some w1 =>
        rw [e1] at h1; rw [e2] at h2
        simp only at h1 h2
        split at h1 <;> split at h2 <;> cases h1 <;> cases h2
        exact decodeLE_transfer2 hr e1 e2

theorem load_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {m n : Mem} (hm : MRel2 J g m n) {pS pT : Ptr}
    (h : V2 J g pS pT) {τ : Ty} {v w : Val} (h1 : m.load pS τ = some v)
    (h2 : n.load pT τ = some w) : VV2 J g v w := by
  simp only [Mem.load] at h1 h2
  split at h1
  · split at h2
    · rename_i c1 c2
      simp only [Bool.and_eq_true] at c1 c2
      exact decode_transfer2 hJ (readCells_transfer2 hm h c1.1 c2.1) τ h1 h2
    · cases h2
  · cases h1

theorem loadPtr_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {m n : Mem} (hm : MRel2 J g m n) {pS pT : Ptr}
    (h : V2 J g pS pT) {r r' : Ptr} (h1 : m.loadPtr pS = some r) (h2 : n.loadPtr pT = some r') :
    V2 J g r r' := by
  simp only [Mem.loadPtr] at h1 h2
  cases e1 : m.load pS .ptr with
  | none => rw [e1] at h1; cases h1
  | some v =>
    cases e2 : n.load pT .ptr with
    | none => rw [e2] at h2; cases h2
    | some w =>
      rw [e1] at h1; rw [e2] at h2
      have := load_transfer2 hJ hm h e1 e2
      cases v with
      | int _ => simp at h1
      | ptr r0 =>
        cases w with
        | int _ => simp at h2
        | ptr r1 => simp only at h1 h2; cases h1; cases h2; exact this

theorem basePtr_transfer2 {σ τ : State} (hm : MRel2 J g σ.mem τ.mem) (hfr : FrRel2 g σ τ)
    {y : Local} {pS pT : Ptr} (h1 : σ.basePtr y = some pS) (h2 : τ.basePtr y = some pT) :
    V2 J g pS pT := by
  simp only [State.basePtr] at h1 h2
  split at h1
  · cases h1
  · rename_i kS hkS
    split at h2
    · cases h2
    · rename_i kT hkT
      obtain ⟨bS, bT, hg⟩ := hfr y kS kT hkS hkT
      obtain ⟨⟨alS, g1, g2⟩, ⟨alT, g3, g4⟩⟩ := hm.gbase kT kS bS bT hg
      rw [g1] at h1; rw [g3] at h2
      cases h1; cases h2
      exact Or.inl ⟨kT, kS, bS, bT, hg, rfl, rfl, by simp only; omega⟩

theorem readIndex_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) {j : Local} {v w : Nat} (h1 : σ.readIndex j = some v)
    (h2 : τ.readIndex j = some w) : v = w := by
  simp only [State.readIndex, State.readLocal] at h1 h2
  cases e1 : σ.basePtr j with
  | none => rw [e1] at h1; simp at h1
  | some pS =>
    cases e2 : τ.basePtr j with
    | none => rw [e2] at h2; simp at h2
    | some pT =>
      rw [e1] at h1; rw [e2] at h2
      simp only [Option.bind_some] at h1 h2
      cases l1 : σ.mem.load pS idxTy with
      | none => rw [l1] at h1; simp at h1
      | some a =>
        cases l2 : τ.mem.load pT idxTy with
        | none => rw [l2] at h2; simp at h2
        | some b =>
          rw [l1] at h1; rw [l2] at h2
          have := load_transfer2 hJ hm (basePtr_transfer2 hm hfr e1 e2) l1 l2
          cases a with
          | ptr _ => simp at h1
          | int a =>
            cases b with
            | ptr _ => simp at h2
            | int b => simp only at h1 h2; cases h1; cases h2; exact this

theorem projStep_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) {pS pT : Ptr} (h : V2 J g pS pT) (π : Proj) {q q' : Ptr}
    (h1 : projStep σ pS π = some q) (h2 : projStep τ pT π = some q') : V2 J g q q' := by
  cases π with
  | deref => exact loadPtr_transfer2 hJ hm h h1 h2
  | field off =>
    simp only [projStep] at h1 h2
    split at h1
    · rename_i hb
      split at h2
      · cases h1; cases h2; exact V2.offset hm.junk h hb
      · cases h2
    · cases h1
  | index j sz =>
    simp only [projStep] at h1 h2
    cases i1 : σ.readIndex j with
    | none => rw [i1] at h1; cases h1
    | some v =>
      cases i2 : τ.readIndex j with
      | none => rw [i2] at h2; cases h2
      | some w =>
        rw [i1] at h1; rw [i2] at h2
        have e := readIndex_transfer2 hJ hm hfr i1 i2
        subst e
        simp only at h1 h2
        split at h1
        · rename_i hb
          split at h2
          · cases h1; cases h2; exact V2.offset hm.junk h hb
          · cases h2
        · cases h1

theorem evalProjs_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) :
    ∀ (πs : List Proj) {pS pT : Ptr}, V2 J g pS pT → ∀ {q q' : Ptr},
      evalProjs σ pS πs = some q → evalProjs τ pT πs = some q' → V2 J g q q'
  | [], pS, pT, h, q, q', h1, h2 => by cases h1; cases h2; exact h
  | π :: πs, pS, pT, h, q, q', h1, h2 => by
    simp only [evalProjs] at h1 h2
    cases e1 : projStep σ pS π with
    | none => rw [e1] at h1; cases h1
    | some r =>
      cases e2 : projStep τ pT π with
      | none => rw [e2] at h2; cases h2
      | some r' =>
        rw [e1] at h1; rw [e2] at h2
        exact evalProjs_transfer2 hJ hm hfr πs (projStep_transfer2 hJ hm hfr h π e1 e2) h1 h2

theorem evalPlace_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) (p : Place) {q q' : Ptr} (h1 : evalPlace σ p = some q)
    (h2 : evalPlace τ p = some q') : V2 J g q q' := by
  simp only [evalPlace] at h1 h2
  cases e1 : σ.basePtr p.base with
  | none => rw [e1] at h1; cases h1
  | some pS =>
    cases e2 : τ.basePtr p.base with
    | none => rw [e2] at h2; cases h2
    | some pT =>
      rw [e1] at h1; rw [e2] at h2
      exact evalProjs_transfer2 hJ hm hfr p.proj (basePtr_transfer2 hm hfr e1 e2) h1 h2

/-- An operand whose constants are related to themselves. -/
def OpOK2 (J : Ptr → Prop) : Operand → Prop
  | .copy _ _ => True
  | .const v => ConstOK J v

/-- A right-hand side that observes no address and whose constants satisfy `J`. -/
def RvOK2 (J : Ptr → Prop) : Rvalue → Prop
  | .use o => OpOK2 J o
  | .rawRef _ => True
  | .ref _ _ => True
  | .ptrEq _ _ => False
  | .addrOf _ => False

theorem operand_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) {o : Operand} (ho : OpOK2 J o) {v w : Val} (h1 : o.eval σ = some v)
    (h2 : o.eval τ = some w) : VV2 J g v w := by
  cases o with
  | copy p τ' =>
    simp only [Operand.eval] at h1 h2
    cases e1 : evalPlace σ p with
    | none => rw [e1] at h1; cases h1
    | some q =>
      cases e2 : evalPlace τ p with
      | none => rw [e2] at h2; cases h2
      | some q' =>
        rw [e1] at h1; rw [e2] at h2
        exact load_transfer2 hJ hm (evalPlace_transfer2 hJ hm hfr p e1 e2) h1 h2
  | const c =>
    simp only [Operand.eval] at h1 h2
    cases h1; cases h2
    cases v with
    | int n => rfl
    | ptr q => exact Or.inr ⟨rfl, ho⟩

theorem evalInt_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) {o : Operand} (ho : OpOK2 J o) {n n' : Nat}
    (h1 : o.evalInt σ = some n) (h2 : o.evalInt τ = some n') : n = n' := by
  simp only [Operand.evalInt] at h1 h2
  cases e1 : o.eval σ with
  | none => rw [e1] at h1; cases h1
  | some v =>
    cases e2 : o.eval τ with
    | none => rw [e2] at h2; cases h2
    | some w =>
      rw [e1] at h1; rw [e2] at h2
      have := operand_transfer2 hJ hm hfr ho e1 e2
      cases v with
      | ptr _ => simp at h1
      | int a =>
        cases w with
        | ptr _ => simp at h2
        | int b => simp only at h1 h2; cases h1; cases h2; exact this

theorem rvalue_transfer2 (hJ : ∀ a, J ⟨none, a⟩) {σ τ : State} (hm : MRel2 J g σ.mem τ.mem)
    (hfr : FrRel2 g σ τ) {rv : Rvalue} (hr : RvOK2 J rv) {v w : Val} (h1 : rv.eval σ = some v)
    (h2 : rv.eval τ = some w) : VV2 J g v w := by
  cases rv with
  | use o => exact operand_transfer2 hJ hm hfr hr h1 h2
  | rawRef p =>
    simp only [Rvalue.eval] at h1 h2
    cases e1 : evalPlace σ p with
    | none => rw [e1] at h1; cases h1
    | some q =>
      cases e2 : evalPlace τ p with
      | none => rw [e2] at h2; cases h2
      | some q' =>
        rw [e1] at h1; rw [e2] at h2
        cases h1; cases h2
        exact evalPlace_transfer2 hJ hm hfr p e1 e2
  | ref p L =>
    simp only [Rvalue.eval] at h1 h2
    cases e1 : evalPlace σ p with
    | none => rw [e1] at h1; cases h1
    | some q =>
      cases e2 : evalPlace τ p with
      | none => rw [e2] at h2; cases h2
      | some q' =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.bind_some] at h1 h2
        split at h1
        · split at h2
          · cases h1; cases h2; exact evalPlace_transfer2 hJ hm hfr p e1 e2
          · cases h2
        · cases h1
  | ptrEq _ _ => exact absurd hr id
  | addrOf _ => exact absurd hr id

theorem encode_rel2 {vS vT : Val} (hv : VV2 J g vS vT) (n i : Nat) :
    CR2 J g (((vS.encode n)[i]?).getD .uninit) (((vT.encode n)[i]?).getD .uninit) := by
  cases vS with
  | int a =>
    cases vT with
    | int b =>
      simp only [VV2] at hv
      subst hv
      simp only [Val.encode]
      rcases encodeLE_getElem? n a i with h | ⟨c, h⟩ <;> rw [h] <;> simp [CR2]
    | ptr _ => simp [VV2] at hv
  | ptr q =>
    cases vT with
    | int _ => simp [VV2] at hv
    | ptr r =>
      simp only [VV2] at hv
      simp only [Val.encode, List.getElem?_map]
      by_cases hi : i < n <;> simp [hi, CR2, hv]

/-- An address in the range of one live allocation is outside the range of another. -/
theorem not_mem_of_disjoint {b1 n1 b2 n2 a : Nat} (hd : disjointRanges b1 n1 b2 n2 = true)
    (h1 : b1 ≤ a ∧ a < b1 + n1) : ¬ (b2 ≤ a ∧ a < b2 + n2) := by
  simp only [disjointRanges, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
  omega

theorem store_transfer2 {m n : Mem} (hm : MRel2 J g m n) {pS pT : Ptr}
    (h : V2 J g pS pT) {vS vT : Val} (hv : VV2 J g vS vT) {τ : Ty} {m' n' : Mem}
    (h1 : m.store pS τ vS = some m') (h2 : n.store pT τ vT = some n') :
    MRel2 J g m' n' ∧ m'.allocs = m.allocs ∧ n'.allocs = n.allocs := by
  simp only [Mem.store] at h1 h2
  split at h1
  · split at h2
    · rename_i c1 c2
      cases h1; cases h2
      simp only [Bool.and_eq_true] at c1 c2
      refine ⟨⟨hm.gbase, hm.gsize, ?_, hm.junk, hm.sdisj, hm.tdisj, hm.ginj⟩, rfl, rfl⟩
      intro jT jS bS bT alS alT hg e1 e2 l1 l2 i hi
      change m.allocs[jS]? = some alS at e1
      change n.allocs[jT]? = some alT at e2
      have hc := hm.cells jT jS bS bT alS alT hg e1 e2 l1 l2 i hi
      change CR2 J g ((m.writeCells pS.addr (vS.encode τ.size)).get (bS + i))
        ((n.writeCells pT.addr (vT.encode τ.size)).get (bT + i))
      rw [get_writeCells, get_writeCells, encode_length, encode_length]
      by_cases hz : τ.size = 0
      · rw [ite_neg' (by omega), ite_neg' (by omega)]; exact hc
      have hk' : (τ.size == 0) = false := by simp [hz]
      simp only [Mem.dereferenceable, hk', Bool.false_or] at c1 c2
      obtain ⟨kS', aS, s1, s2, s3, s4, s5⟩ := inBounds_some c1.1
      obtain ⟨kT', aT, t1, t2, t3, t4, t5⟩ := inBounds_some c2.1
      obtain ⟨⟨alS', g1, g2⟩, ⟨alT', g3, g4⟩⟩ := hm.gbase jT jS bS bT hg
      rw [e1] at g1; cases g1
      rw [e2] at g3; cases g3
      subst g2; subst g4
      have hsz := hm.gsize jT jS _ _ alS alT hg e1 e2
      rcases h with ⟨kT, kS, cS, cT, hg', p1, p2, p3⟩ | ⟨rfl, hj⟩
      · have hk1 : kS' = kS := by rw [p2] at s1; exact (Option.some.inj s1).symm
        have hk2 : kT' = kT := by rw [p1] at t1; exact (Option.some.inj t1).symm
        subst kS'; subst kT'
        obtain ⟨⟨aS', g5, g6⟩, ⟨aT', g7, g8⟩⟩ := hm.gbase kT kS cS cT hg'
        rw [s2] at g5; cases g5
        rw [t2] at g7; cases g7
        by_cases hjk : jT = kT
        · subst hjk
          rw [hg] at hg'
          cases hg'
          rw [e1] at s2; cases s2
          rw [e2] at t2; cases t2
          by_cases hin : pT.addr ≤ alT.base + i ∧ alT.base + i < pT.addr + τ.size
          · have hin' : pS.addr ≤ alS.base + i ∧ alS.base + i < pS.addr + τ.size := by omega
            rw [ite_pos' hin', ite_pos' hin,
              show alS.base + i - pS.addr = alT.base + i - pT.addr by omega]
            exact encode_rel2 hv _ _
          · have hin' : ¬ (pS.addr ≤ alS.base + i ∧ alS.base + i < pS.addr + τ.size) := by omega
            rw [ite_neg' hin', ite_neg' hin]; exact hc
        · -- different target allocations: both writes miss the range of `jT ↦ jS`
          have hdT := hm.tdisj
          unfold TDisj at hdT
          have dT := hdT kT jT aT alT (Ne.symm hjk) t2 e2 t3 l2
          rw [disjointRanges_comm] at dT
          have nT := not_mem_of_disjoint (a := alT.base + i) dT ⟨by omega, by omega⟩
          by_cases hjS : jS = kS
          · subst hjS
            exact absurd (hm.ginj jT kT jS _ _ _ _ alT aT hg hg' e2 t2 l2 t3) hjk
          · have hdS := hm.sdisj
            unfold TDisj at hdS
            have dS := hdS kS jS aS alS (Ne.symm hjS) s2 e1 s3 l1
            rw [disjointRanges_comm] at dS
            have nS := not_mem_of_disjoint (a := alS.base + i) dS ⟨by omega, by omega⟩
            rw [ite_neg' (fun hc' => nS ⟨by omega, by omega⟩),
              ite_neg' (fun hc' => nT ⟨by omega, by omega⟩)]
            exact hc
      · rw [hm.junk _ hj _ (Nat.pos_of_ne_zero hz)] at c1; cases c1.1
    · cases h2
  · cases h1

end Transfer

end Toy.PlaceEval
