/-
Toy.SCT.Threads
===============

The thread semantics of composition. A label supports a thread step (`Label.Ok`); the composite
`G ; H` has an arc exactly when some intermediate parameter connects an arc of `G` to an arc of
`H`, strict exactly when one of the two is strict (`SCG.comp_ok`). Finite threads along a sequence
of graphs (`SegThread`) compose by concatenation (`segThread_append`), and every graph of the
composition closure is the composite of a nonempty path of call-site graphs whose threads it
records exactly (`hasFactorPath_of_inClosure`).
-/
import Toy.SCT.Semantics

namespace Toy.SCT

variable {nf k : Nat}

namespace Label

/-- `l.Ok b`: the label `l` supports a thread step, a strict one if `b = true`. -/
def Ok (l : Label) (b : Bool) : Prop := l ≠ Label.absent ∧ (b = true → l = Label.strict)

theorem ok_false (l : Label) : l.Ok false ↔ l ≠ Label.absent := by
  simp [Ok]

theorem ok_true (l : Label) : l.Ok true ↔ l = Label.strict := by
  cases l <;> simp [Ok]

/-- A label is determined by the thread steps it supports. -/
theorem eq_of_ok_iff {l l' : Label} (h : ∀ b, l.Ok b ↔ l'.Ok b) : l = l' := by
  have h0 := h false
  have h1 := h true
  rw [ok_false, ok_false] at h0
  rw [ok_true, ok_true] at h1
  cases l <;> cases l' <;> simp_all

theorem join_ne_absent (a b : Label) : join a b ≠ absent ↔ a ≠ absent ∨ b ≠ absent := by
  cases a <;> cases b <;> decide

theorem join_eq_strict (a b : Label) : join a b = strict ↔ a = strict ∨ b = strict := by
  cases a <;> cases b <;> decide

theorem seq_ne_absent (a b : Label) : seq a b ≠ absent ↔ a ≠ absent ∧ b ≠ absent := by
  cases a <;> cases b <;> decide

theorem seq_eq_strict (a b : Label) :
    seq a b = strict ↔ a ≠ absent ∧ b ≠ absent ∧ (a = strict ∨ b = strict) := by
  cases a <;> cases b <;> decide

end Label

theorem foldl_join_ne_absent {β : Type} (f : β → Label) :
    ∀ (xs : List β) (acc : Label),
      xs.foldl (fun acc m => Label.join acc (f m)) acc ≠ Label.absent ↔
        acc ≠ Label.absent ∨ ∃ m ∈ xs, f m ≠ Label.absent
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_join_ne_absent f xs, Label.join_ne_absent]
    constructor
    · rintro ((h | h) | ⟨m, hm, hfm⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, by simp, h⟩
      · exact Or.inr ⟨m, by simp [hm], hfm⟩
    · rintro (h | ⟨m, hm, hfm⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inl (Or.inr hfm)
        · exact Or.inr ⟨m, hm, hfm⟩

theorem foldl_join_eq_strict {β : Type} (f : β → Label) :
    ∀ (xs : List β) (acc : Label),
      xs.foldl (fun acc m => Label.join acc (f m)) acc = Label.strict ↔
        acc = Label.strict ∨ ∃ m ∈ xs, f m = Label.strict
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_join_eq_strict f xs, Label.join_eq_strict]
    constructor
    · rintro ((h | h) | ⟨m, hm, hfm⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, by simp, h⟩
      · exact Or.inr ⟨m, by simp [hm], hfm⟩
    · rintro (h | ⟨m, hm, hfm⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inl (Or.inr hfm)
        · exact Or.inr ⟨m, hm, hfm⟩

namespace SCG

/-- The composite has an arc `(i, j)` iff some intermediate parameter `m` connects an arc `(i, m)`
of `G` to an arc `(m, j)` of `H`. -/
theorem comp_lab_ne_absent (G H : SCG nf k) (i j : Fin k) :
    (G.compWith Label.seq H).lab i j ≠ Label.absent ↔
      ∃ m, G.lab i m ≠ Label.absent ∧ H.lab m j ≠ Label.absent := by
  refine (foldl_join_ne_absent (fun m => Label.seq (G.lab i m) (H.lab m j))
    (List.finRange k) Label.absent).trans ?_
  constructor
  · rintro (h | ⟨m, -, hm⟩)
    · exact absurd rfl h
    · exact ⟨m, (Label.seq_ne_absent _ _).mp hm⟩
  · rintro ⟨m, hm⟩
    exact Or.inr ⟨m, List.mem_finRange m, (Label.seq_ne_absent _ _).mpr hm⟩

/-- The composite has a strict arc `(i, j)` iff some intermediate parameter `m` connects arcs
`(i, m)` of `G` and `(m, j)` of `H`, at least one of them strict. -/
theorem comp_lab_eq_strict (G H : SCG nf k) (i j : Fin k) :
    (G.compWith Label.seq H).lab i j = Label.strict ↔
      ∃ m, G.lab i m ≠ Label.absent ∧ H.lab m j ≠ Label.absent ∧
        (G.lab i m = Label.strict ∨ H.lab m j = Label.strict) := by
  refine (foldl_join_eq_strict (fun m => Label.seq (G.lab i m) (H.lab m j))
    (List.finRange k) Label.absent).trans ?_
  constructor
  · rintro (h | ⟨m, -, hm⟩)
    · cases h
    · exact ⟨m, (Label.seq_eq_strict _ _).mp hm⟩
  · rintro ⟨m, hm⟩
    exact Or.inr ⟨m, List.mem_finRange m, (Label.seq_eq_strict _ _).mpr hm⟩

/-- **Thread semantics of composition.** -/
theorem comp_ok (G H : SCG nf k) (i j : Fin k) (b : Bool) :
    ((G.compWith Label.seq H).lab i j).Ok b ↔
      ∃ m b1 b2, (G.lab i m).Ok b1 ∧ (H.lab m j).Ok b2 ∧ b = (b1 || b2) := by
  cases b with
  | false =>
    rw [Label.ok_false, comp_lab_ne_absent]
    constructor
    · rintro ⟨m, h1, h2⟩
      exact ⟨m, false, false, (Label.ok_false _).mpr h1, (Label.ok_false _).mpr h2, rfl⟩
    · rintro ⟨m, b1, b2, h1, h2, hb⟩
      exact ⟨m, h1.1, h2.1⟩
  | true =>
    rw [Label.ok_true, comp_lab_eq_strict]
    constructor
    · rintro ⟨m, h1, h2, h3 | h3⟩
      · exact ⟨m, true, false, (Label.ok_true _).mpr h3, (Label.ok_false _).mpr h2, rfl⟩
      · exact ⟨m, false, true, (Label.ok_false _).mpr h1, (Label.ok_true _).mpr h3, rfl⟩
    · rintro ⟨m, b1, b2, h1, h2, hb⟩
      refine ⟨m, h1.1, h2.1, ?_⟩
      cases b1 with
      | true => exact Or.inl (h1.2 rfl)
      | false =>
        cases b2 with
        | true => exact Or.inr (h2.2 rfl)
        | false => cases hb

theorem comp_ok' (G H : SCG nf k) (i j : Fin k) (b : Bool) :
    ((G.comp H).lab i j).Ok b ↔
      ∃ m b1 b2, (G.lab i m).Ok b1 ∧ (H.lab m j).Ok b2 ∧ b = (b1 || b2) :=
  comp_ok G H i j b

end SCG

/-- `SegThread Gs a n q j b`: a thread along the `n` graphs `Gs a, …, Gs (a + n - 1)` from
parameter `q` to parameter `j` all of whose arcs are present, with a strict arc if `b = true`. -/
def SegThread (Gs : Nat → SCG nf k) : Nat → Nat → Fin k → Fin k → Bool → Prop
  | _, 0, q, j, b => q = j ∧ b = false
  | a, n + 1, q, j, b =>
    ∃ l b1 b2, ((Gs a).lab q l).Ok b1 ∧ SegThread Gs (a + 1) n l j b2 ∧ b = (b1 || b2)

theorem segThread_one (Gs : Nat → SCG nf k) (a : Nat) (q j : Fin k) (b : Bool) :
    SegThread Gs a 1 q j b ↔ ((Gs a).lab q j).Ok b := by
  constructor
  · rintro ⟨l, b1, b2, hok, ⟨rfl, rfl⟩, rfl⟩
    simpa using hok
  · intro h
    exact ⟨j, b, false, h, ⟨rfl, rfl⟩, by simp⟩

/-- Threads compose by concatenation. -/
theorem segThread_append (Gs : Nat → SCG nf k) :
    ∀ (n1 a n2 : Nat) (q j : Fin k) (b : Bool),
      SegThread Gs a (n1 + n2) q j b ↔
        ∃ l b1 b2, SegThread Gs a n1 q l b1 ∧ SegThread Gs (a + n1) n2 l j b2 ∧ b = (b1 || b2) := by
  intro n1
  induction n1 with
  | zero =>
    intro a n2 q j b
    rw [Nat.zero_add, Nat.add_zero]
    constructor
    · intro h
      exact ⟨q, false, b, ⟨rfl, rfl⟩, h, by simp⟩
    · rintro ⟨l, b1, b2, ⟨rfl, rfl⟩, h, rfl⟩
      simpa using h
  | succ n1 ih =>
    intro a n2 q j b
    rw [Nat.succ_add]
    constructor
    · rintro ⟨l, b1, b2, hok, hrest, rfl⟩
      obtain ⟨l', c1, c2, h1, h2, rfl⟩ := (ih (a + 1) n2 l j b2).mp hrest
      refine ⟨l', b1 || c1, c2, ⟨l, b1, c1, hok, h1, rfl⟩, ?_, by simp [Bool.or_assoc]⟩
      rwa [show a + (n1 + 1) = a + 1 + n1 by omega]
    · rintro ⟨l', d1, d2, ⟨l, b1, c1, hok, h1, rfl⟩, h2, rfl⟩
      refine ⟨l, b1, c1 || d2, hok, (ih (a + 1) n2 l j (c1 || d2)).mpr ⟨l', c1, d2, h1, ?_, rfl⟩,
        by simp [Bool.or_assoc]⟩
      rwa [show a + 1 + n1 = a + (n1 + 1) by omega]

/-- A finite thread as a function: positions `a … a + n`, consecutive arcs present, and a strict
arc if `b = true`. -/
theorem segThread_to_fun (Gs : Nat → SCG nf k) :
    ∀ (n a : Nat) (q j : Fin k) (b : Bool), SegThread Gs a n q j b →
      ∃ p : Nat → Fin k, p a = q ∧ p (a + n) = j ∧
        (∀ t, a ≤ t → t < a + n → (Gs t).lab (p t) (p (t + 1)) ≠ Label.absent) ∧
        (b = true → ∃ t, a ≤ t ∧ t < a + n ∧ (Gs t).lab (p t) (p (t + 1)) = Label.strict) := by
  intro n
  induction n with
  | zero =>
    rintro a q j b ⟨rfl, rfl⟩
    exact ⟨fun _ => q, rfl, rfl, fun t h1 h2 => absurd h2 (by omega), fun h => by cases h⟩
  | succ n ih =>
    rintro a q j b ⟨l, b1, b2, hok, hrest, rfl⟩
    obtain ⟨p, hp0, hpn, hpres, hpstr⟩ := ih (a + 1) l j b2 hrest
    refine ⟨fun t => if t = a then q else p t, by simp, ?_, ?_, ?_⟩
    · simp only [show a + (n + 1) ≠ a by omega, ite_false]
      rwa [show a + (n + 1) = a + 1 + n by omega]
    · intro t h1 h2
      by_cases ht : t = a
      · subst ht
        simp only [ite_true, show t + 1 ≠ t by omega, ite_false, hp0]
        exact hok.1
      · simp only [ht, ite_false, show t + 1 ≠ a by omega]
        exact hpres t (by omega) (by omega)
    · intro hb
      cases b1 with
      | true =>
        refine ⟨a, Nat.le_refl _, by omega, ?_⟩
        simp only [ite_true, show a + 1 ≠ a by omega, ite_false, hp0]
        exact hok.2 rfl
      | false =>
        obtain ⟨t, h1, h2, ht⟩ := hpstr (by simpa using hb)
        refine ⟨t, by omega, by omega, ?_⟩
        simp only [show t ≠ a by omega, show t + 1 ≠ a by omega, ite_false]
        exact ht

/-- `G` is the composite of a nonempty path `F 0, …, F (m - 1)` of call-site graphs of `P`, and the
arcs of `G` record exactly the threads along that path, wherever the path is placed. -/
def HasFactorPath (P : Prog nf k) (G : SCG nf k) : Prop :=
  ∃ (m : Nat) (F : Nat → SCG nf k), 0 < m ∧ (∀ t, t < m → F t ∈ P.calls) ∧
    (∀ t, t + 1 < m → (F t).dst = (F (t + 1)).src) ∧ (F 0).src = G.src ∧
    (F (m - 1)).dst = G.dst ∧
    ∀ (Gs : Nat → SCG nf k) (a : Nat), (∀ t, t < m → Gs (a + t) = F t) →
      ∀ q j b, (G.lab q j).Ok b ↔ SegThread Gs a m q j b

/-- Every graph of the composition closure has a factor path. -/
theorem hasFactorPath_of_inClosure {P : Prog nf k} {G : SCG nf k} (h : InClosure P G) :
    HasFactorPath P G := by
  induction h with
  | @gen G hG =>
    refine ⟨1, fun _ => G, Nat.one_pos, fun _ _ => hG, fun t ht => absurd ht (by omega), rfl, rfl,
      ?_⟩
    intro Gs a hGs q j b
    have h0 := hGs 0 Nat.one_pos
    simp only [Nat.add_zero] at h0
    rw [segThread_one, h0]
  | @comp G H _ _ hdst ihG ihH =>
    obtain ⟨m1, F1, hm1, hc1, hch1, hs1, hd1, hsem1⟩ := ihG
    obtain ⟨m2, F2, hm2, hc2, hch2, hs2, hd2, hsem2⟩ := ihH
    refine ⟨m1 + m2, fun t => if t < m1 then F1 t else F2 (t - m1), by omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      dsimp only
      split
      · exact hc1 t ‹_›
      · exact hc2 (t - m1) (by omega)
    · intro t ht
      dsimp only
      by_cases h1 : t + 1 < m1
      · rw [ite_eq_left (by omega), ite_eq_left h1]
        exact hch1 t h1
      · by_cases h2 : t + 1 = m1
        · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
          have e1 : t = m1 - 1 := by omega
          have e2 : t + 1 - m1 = 0 := by omega
          rw [e2, e1, hd1, hs2]
          exact hdst
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          have := hch2 (t - m1) (by omega)
          rwa [show t - m1 + 1 = t + 1 - m1 by omega] at this
    · dsimp only
      rw [ite_eq_left hm1]
      exact hs1
    · dsimp only
      rw [ite_eq_right (by omega), show m1 + m2 - 1 - m1 = m2 - 1 by omega]
      exact hd2
    · intro Gs a hGs q j b
      have hG1 : ∀ t, t < m1 → Gs (a + t) = F1 t := fun t ht => by
        rw [hGs t (by omega)]
        exact ite_eq_left ht
      have hG2 : ∀ t, t < m2 → Gs (a + m1 + t) = F2 t := fun t ht => by
        rw [show a + m1 + t = a + (m1 + t) by omega, hGs (m1 + t) (by omega)]
        show (if m1 + t < m1 then F1 (m1 + t) else F2 (m1 + t - m1)) = F2 t
        rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rw [SCG.comp_ok, segThread_append]
      constructor
      · rintro ⟨l, b1, b2, h1, h2, rfl⟩
        exact ⟨l, b1, b2, (hsem1 Gs a hG1 q l b1).mp h1, (hsem2 Gs (a + m1) hG2 l j b2).mp h2, rfl⟩
      · rintro ⟨l, b1, b2, h1, h2, rfl⟩
        exact ⟨l, b1, b2, (hsem1 Gs a hG1 q l b1).mpr h1, (hsem2 Gs (a + m1) hG2 l j b2).mpr h2,
          rfl⟩

end Toy.SCT
