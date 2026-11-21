import ToyCoalesce.Infra

/-!
# Proof: the union-find check
-/

namespace Toy.Coalesce

namespace UF

/-- Reachability along the edges of a list, following each edge from its child to its parent. -/
inductive Reach (E : List Edge) : Nat → Nat → Prop
  | refl (x : Nat) : Reach E x x
  | step (e : Edge) (y : Nat) : e ∈ E → Reach E e.parent y → Reach E e.child y

theorem Reach.trans {E : List Edge} {x y z : Nat} (h1 : Reach E x y) (h2 : Reach E y z) :
    Reach E x z := by
  induction h1 with
  | refl _ => exact h2
  | step e _ he _ ih => exact Reach.step e z he (ih h2)

theorem Reach.mono {E E' : List Edge} (hsub : ∀ e ∈ E, e ∈ E') {x y : Nat}
    (h : Reach E x y) : Reach E' x y := by
  induction h with
  | refl x => exact Reach.refl x
  | step e y he _ ih => exact Reach.step e y (hsub e he) ih

theorem Reach.eq_of_not_child {E : List Edge} {x y : Nat} (h : Reach E x y)
    (hnc : ∀ e ∈ E, e.child ≠ x) : x = y := by
  cases h with
  | refl _ => rfl
  | step e _ he _ => exact absurd rfl (hnc e he)

theorem Reach.child_of_ne {E : List Edge} {x y : Nat} (h : Reach E x y) (hne : x ≠ y) :
    ∃ e ∈ E, e.child = x := by
  cases h with
  | refl _ => exact absurd rfl hne
  | step e _ he _ => exact ⟨e, he, rfl⟩

theorem Reach.parent_of_ne {E : List Edge} {x y : Nat} (h : Reach E x y) (hne : x ≠ y) :
    ∃ e ∈ E, e.parent = y := by
  induction h with
  | refl _ => exact absurd rfl hne
  | step e y he _ ih =>
    by_cases hp : e.parent = y
    · exact ⟨e, he, hp⟩
    · exact ih hp

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

theorem resolveF_succ_of_some {μ : Forest} {x : Nat} {e : Edge} (h : μ.parentOf x = some e)
    (k : Nat) : (μ.resolveF (k + 1) x).1 = (μ.resolveF k e.parent).1 := by
  simp [Forest.resolveF, h]

theorem resolveF_of_none {μ : Forest} {x : Nat} (h : μ.parentOf x = none) (k : Nat) :
    (μ.resolveF k x).1 = x := by
  cases k with
  | zero => rfl
  | succ k => simp [Forest.resolveF, h]

theorem resolveF_stable {μ : Forest} : ∀ (k x : Nat), μ.parentOf (μ.resolveF k x).1 = none →
    ∀ j, (μ.resolveF (k + j) x).1 = (μ.resolveF k x).1 := by
  intro k
  induction k with
  | zero =>
    intro x h j
    have h' : μ.parentOf x = none := h
    rw [Nat.zero_add, resolveF_of_none h' j]
    rfl
  | succ k ih =>
    intro x h j
    cases hx : μ.parentOf x with
    | none =>
      rw [resolveF_of_none hx, resolveF_of_none hx]
    | some e =>
      rw [resolveF_succ_of_some hx] at h ⊢
      rw [show k + 1 + j = (k + j) + 1 by omega, resolveF_succ_of_some hx]
      exact ih e.parent h j

theorem root_edge {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {e : Edge} (he : e ∈ μ) :
    μ.root e.child = μ.root e.parent := by
  obtain ⟨hnd, hedge, hroot, -, -⟩ := hwf
  have hpc := parentOf_of_mem hnd he
  obtain ⟨L, hL⟩ : ∃ L, μ.length = L + 1 :=
    ⟨μ.length - 1, by have := List.length_pos_of_mem he; omega⟩
  have h1 : μ.root e.child = (μ.resolveF L e.parent).1 := by
    unfold Forest.root Forest.resolve; rw [hL, resolveF_succ_of_some hpc]
  have hnone := hroot _ (hedge e he).1
  rw [h1] at hnone
  have hst := resolveF_stable L e.parent hnone 1
  rw [h1]; unfold Forest.root Forest.resolve; rw [hL, hst]

theorem Reach.root_eq {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {E : List Edge}
    (hE : ∀ e ∈ E, e ∈ μ) {x y : Nat} (h : Reach E x y) : μ.root x = μ.root y := by
  induction h with
  | refl _ => rfl
  | step e y he _ ih => rw [root_edge hwf (hE e he), ih]

theorem reach_resolveF (μ : Forest) : ∀ k x, Reach μ x (μ.resolveF k x).1 := by
  intro k
  induction k with
  | zero => intro x; exact Reach.refl x
  | succ k ih =>
    intro x
    cases hx : μ.parentOf x with
    | none => rw [resolveF_of_none hx]; exact Reach.refl x
    | some e =>
      rw [resolveF_succ_of_some hx]
      obtain ⟨he, hc⟩ := parentOf_some hx
      rw [← hc]; exact Reach.step e _ he (ih e.parent)

theorem resolveF_closed {μ : Forest} (S : Nat → Prop)
    (hS : ∀ y, S y → ∃ e, μ.parentOf y = some e ∧ S e.parent) :
    ∀ k x, S x → S (μ.resolveF k x).1 := by
  intro k
  induction k with
  | zero => intro x hx; exact hx
  | succ k ih =>
    intro x hx
    obtain ⟨e, he, hpe⟩ := hS x hx
    rw [resolveF_succ_of_some he]; exact ih _ hpe

theorem no_cycle {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {E : List Edge}
    (hE : ∀ e ∈ E, e ∈ μ) {e : Edge} (he : e ∈ μ) (h : Reach E e.parent e.child) : False := by
  obtain ⟨hnd, hedge, hroot, -, -⟩ := hwf
  have hS : ∀ y, Reach E y e.child →
      ∃ e', μ.parentOf y = some e' ∧ Reach E e'.parent e.child := by
    intro y hy
    cases hy with
    | refl _ => exact ⟨e, parentOf_of_mem hnd he, h⟩
    | step e' _ he' hr => exact ⟨e', parentOf_of_mem hnd (hE e' he'), hr⟩
  have hr := resolveF_closed (fun y => Reach E y e.child) hS μ.length e.parent h
  obtain ⟨e', he', -⟩ := hS _ hr
  have := hroot e.parent (hedge e he).2.1
  unfold Forest.root Forest.resolve at this
  rw [this] at he'
  cases he'

theorem inClass_iff (μ : Forest) (x : Nat) :
    μ.inClass x = true ↔ ∃ e ∈ μ, e.child = x ∨ e.parent = x := by
  unfold Forest.inClass
  simp [List.any_eq_true]

theorem mem_aoTicks (P : Prog) (u t : Nat) :
    t ∈ aoTicks P u ↔ AddrTaken P u ∧ t < P.code.length + 1 ∧ LexLiveAt P u t = true := by
  unfold aoTicks
  split
  · rename_i h; simp [List.mem_filter, List.mem_range, h]
  · rename_i h; simp [h]

theorem common_tick (P : Prog) (u v : Nat) :
    (∃ t, t ∈ aoTicks P u ∧ t ∈ aoTicks P v) ↔
      AddrTaken P u ∧ AddrTaken P v ∧ LexOverlap P u v := by
  simp only [mem_aoTicks, LexOverlap, IvOverlap, InIv]
  constructor
  · rintro ⟨t, ⟨hau, ht, hu⟩, ⟨hav, -, hv⟩⟩
    refine ⟨hau, hav, 2 * t, by omega, ?_, ?_⟩
    · rw [show 2 * t / 2 = t by omega]; exact hu
    · rw [show 2 * t / 2 = t by omega]; exact hv
  · rintro ⟨hau, hav, p, hp, hu, hv⟩
    exact ⟨p / 2, ⟨hau, by omega, hu⟩, ⟨hav, by omega, hv⟩⟩

/-- Invariant of the union–find state `bs` after processing the edges `E`. -/
structure Inv (P : Prog) (E : List Edge) (bs : List UFBlock) : Prop where
  mem_lt : ∀ b ∈ bs, ∀ x ∈ b.members, x < P.nloc
  cover : ∀ x, x < P.nloc → ∃ b ∈ bs, x ∈ b.members
  uniq : ∀ b ∈ bs, ∀ b' ∈ bs, ∀ x, x ∈ b.members → x ∈ b'.members → b = b'
  ticks : ∀ b ∈ bs, ∀ t, t ∈ b.ticks ↔ ∃ x ∈ b.members, t ∈ aoTicks P x
  disj : ∀ b ∈ bs, ∀ x ∈ b.members, ∀ y ∈ b.members, x ≠ y →
    ∀ t, t ∈ aoTicks P x → t ∉ aoTicks P y
  edges : ∀ e ∈ E, ∃ b ∈ bs, e.child ∈ b.members ∧ e.parent ∈ b.members
  head : ∀ b ∈ bs, ∃ h ∈ b.members, (∀ e ∈ E, e.child ≠ h) ∧ ∀ x ∈ b.members, Reach E x h

theorem inv_init (P : Prog) : Inv P [] (ufInit P) := by
  have hmem : ∀ b, b ∈ ufInit P ↔ ∃ u, u < P.nloc ∧ b = ⟨[u], aoTicks P u⟩ := by
    intro b; unfold ufInit; simp [List.mem_map, List.mem_range, eq_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb x hx
    obtain ⟨u, hu, rfl⟩ := (hmem b).1 hb
    simp at hx; subst hx; exact hu
  · intro x hx
    exact ⟨_, (hmem _).2 ⟨x, hx, rfl⟩, List.mem_singleton_self x⟩
  · intro b hb b' hb' x hx hx'
    obtain ⟨u, hu, rfl⟩ := (hmem b).1 hb
    obtain ⟨u', hu', rfl⟩ := (hmem b').1 hb'
    simp at hx hx'; subst hx; subst hx'; rfl
  · intro b hb t
    obtain ⟨u, hu, rfl⟩ := (hmem b).1 hb
    simp
  · intro b hb x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := (hmem b).1 hb
    simp at hx hy; subst hx; subst hy; exact absurd rfl hne
  · intro e he; simp at he
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := (hmem b).1 hb
    refine ⟨u, List.mem_singleton_self u, by simp, ?_⟩
    intro x hx; simp at hx; subst hx; exact Reach.refl _

theorem find_block {P : Prog} {E : List Edge} {bs : List UFBlock} (hinv : Inv P E bs) {x : Nat}
    (hx : x < P.nloc) :
    ∃ b, bs.find? (·.members.contains x) = some b ∧ b ∈ bs ∧ x ∈ b.members := by
  cases h : bs.find? (·.members.contains x) with
  | none =>
    obtain ⟨b, hb, hxb⟩ := hinv.cover x hx
    have := List.find?_eq_none.mp h b hb
    simp [hxb] at this
  | some b =>
    refine ⟨b, rfl, List.mem_of_find?_eq_some h, ?_⟩
    have := List.find?_some h
    simpa using this

theorem inv_merge {P : Prog} {E : List Edge} {bs : List UFBlock} (hinv : Inv P E bs)
    {e : Edge} {b1 b2 B : UFBlock} {bs' : List UFBlock} (hb1 : b1 ∈ bs) (hb2 : b2 ∈ bs)
    (hne : b1 ≠ b2) (hc : e.child ∈ b1.members) (hp : e.parent ∈ b2.members)
    (hnc : ∀ e' ∈ E, e'.child ≠ e.child) (hdisj : ∀ t ∈ b1.ticks, t ∉ b2.ticks)
    (hBm : ∀ x, x ∈ B.members ↔ x ∈ b1.members ∨ x ∈ b2.members)
    (hBt : ∀ t, t ∈ B.ticks ↔ t ∈ b1.ticks ∨ t ∈ b2.ticks)
    (hmem : ∀ b, b ∈ bs' ↔ b = B ∨ (b ∈ bs ∧ b ≠ b1 ∧ b ≠ b2)) :
    Inv P (E ++ [e]) bs' := by
  have hBin : B ∈ bs' := (hmem B).2 (Or.inl rfl)
  have hsup : ∀ b ∈ bs, ∃ b' ∈ bs', ∀ x ∈ b.members, x ∈ b'.members := by
    intro b hb
    by_cases h1 : b = b1
    · subst h1; exact ⟨B, hBin, fun x hx => (hBm x).2 (Or.inl hx)⟩
    by_cases h2 : b = b2
    · subst h2; exact ⟨B, hBin, fun x hx => (hBm x).2 (Or.inr hx)⟩
    exact ⟨b, (hmem b).2 (Or.inr ⟨hb, h1, h2⟩), fun x hx => hx⟩
  obtain ⟨h1, -, -, hr1⟩ := hinv.head b1 hb1
  have hh1c : e.child = h1 := (hr1 _ hc).eq_of_not_child hnc
  obtain ⟨h2, hh2, hnc2, hr2⟩ := hinv.head b2 hb2
  have hsubE : ∀ e' ∈ E, e' ∈ E ++ [e] := fun e' he' => List.mem_append_left _ he'
  have heE : e ∈ E ++ [e] := List.mem_append_right _ (List.mem_singleton_self e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb x hx
    rcases (hmem b).1 hb with hbB | ⟨hb, -, -⟩
    · rw [hbB] at hx
      rcases (hBm x).1 hx with h | h
      · exact hinv.mem_lt b1 hb1 x h
      · exact hinv.mem_lt b2 hb2 x h
    · exact hinv.mem_lt b hb x hx
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := hinv.cover x hx
    obtain ⟨b', hb', hsub⟩ := hsup b hb
    exact ⟨b', hb', hsub x hxb⟩
  · have hcross : ∀ b ∈ bs, b ≠ b1 → b ≠ b2 → ∀ x, x ∈ B.members → x ∈ b.members → False := by
      intro b hb hn1 hn2 x hxB hxb
      rcases (hBm x).1 hxB with h | h
      · exact hn1 (hinv.uniq b hb b1 hb1 x hxb h)
      · exact hn2 (hinv.uniq b hb b2 hb2 x hxb h)
    intro b hb b' hb' x hx hx'
    rcases (hmem b).1 hb with hbB | ⟨hb, hn1, hn2⟩ <;>
      rcases (hmem b').1 hb' with hbB' | ⟨hb', hn1', hn2'⟩
    · rw [hbB, hbB']
    · rw [hbB] at hx; exact (hcross b' hb' hn1' hn2' x hx hx').elim
    · rw [hbB'] at hx'; exact (hcross b hb hn1 hn2 x hx' hx).elim
    · exact hinv.uniq b hb b' hb' x hx hx'
  · intro b hb t
    rcases (hmem b).1 hb with hbB | ⟨hb, -, -⟩
    · rw [hbB, hBt, hinv.ticks b1 hb1, hinv.ticks b2 hb2]
      constructor
      · rintro (⟨x, hx, ht⟩ | ⟨x, hx, ht⟩)
        · exact ⟨x, (hBm x).2 (Or.inl hx), ht⟩
        · exact ⟨x, (hBm x).2 (Or.inr hx), ht⟩
      · rintro ⟨x, hx, ht⟩
        rcases (hBm x).1 hx with h | h
        · exact Or.inl ⟨x, h, ht⟩
        · exact Or.inr ⟨x, h, ht⟩
    · exact hinv.ticks b hb t
  · intro b hb x hx y hy hxy t htx hty
    rcases (hmem b).1 hb with hbB | ⟨hb, -, -⟩
    · rw [hbB] at hx hy
      rcases (hBm x).1 hx with hx1 | hx2 <;> rcases (hBm y).1 hy with hy1 | hy2
      · exact hinv.disj b1 hb1 x hx1 y hy1 hxy t htx hty
      · exact hdisj t ((hinv.ticks b1 hb1 t).2 ⟨x, hx1, htx⟩)
          ((hinv.ticks b2 hb2 t).2 ⟨y, hy2, hty⟩)
      · exact hdisj t ((hinv.ticks b1 hb1 t).2 ⟨y, hy1, hty⟩)
          ((hinv.ticks b2 hb2 t).2 ⟨x, hx2, htx⟩)
      · exact hinv.disj b2 hb2 x hx2 y hy2 hxy t htx hty
    · exact hinv.disj b hb x hx y hy hxy t htx hty
  · intro e' he'
    rcases List.mem_append.1 he' with he' | he'
    · obtain ⟨b, hb, hcb, hpb⟩ := hinv.edges e' he'
      obtain ⟨b', hb', hsub⟩ := hsup b hb
      exact ⟨b', hb', hsub _ hcb, hsub _ hpb⟩
    · rw [List.mem_singleton] at he'
      subst he'
      exact ⟨B, hBin, (hBm _).2 (Or.inl hc), (hBm _).2 (Or.inr hp)⟩
  · intro b hb
    rcases (hmem b).1 hb with hbB | ⟨hb, hn1, hn2⟩
    · rw [hbB]
      refine ⟨h2, (hBm _).2 (Or.inr hh2), ?_, ?_⟩
      · intro e' he'
        rcases List.mem_append.1 he' with he' | he'
        · exact hnc2 e' he'
        · rw [List.mem_singleton] at he'
          subst he'
          intro heq
          rw [heq] at hc
          exact hne (hinv.uniq b1 hb1 b2 hb2 _ hc hh2)
      · intro x hx
        have hcp : Reach (E ++ [e]) e.child h2 := Reach.step e h2 heE ((hr2 _ hp).mono hsubE)
        rcases (hBm x).1 hx with hx1 | hx2
        · have hxc : Reach E x e.child := by rw [hh1c]; exact hr1 x hx1
          exact (hxc.mono hsubE).trans hcp
        · exact (hr2 x hx2).mono hsubE
    · obtain ⟨h, hh, hnch, hrh⟩ := hinv.head b hb
      refine ⟨h, hh, ?_, fun x hx => (hrh x hx).mono hsubE⟩
      intro e' he'
      rcases List.mem_append.1 he' with he' | he'
      · exact hnch e' he'
      · rw [List.mem_singleton] at he'
        subst he'
        intro heq
        rw [heq] at hc
        exact hn1 (hinv.uniq b hb b1 hb1 _ hh hc)

theorem mem_merged {bs : List UFBlock} {b1 b2 b : UFBlock} :
    b ∈ (⟨b1.members ++ b2.members, b1.ticks ++ b2.ticks⟩ : UFBlock) ::
      bs.filter (fun b => b != b1 && b != b2) ↔
    b = ⟨b1.members ++ b2.members, b1.ticks ++ b2.ticks⟩ ∨ (b ∈ bs ∧ b ≠ b1 ∧ b ≠ b2) := by
  simp

theorem not_child_of_split {μ : Forest} (hnd : (μ.map Edge.child).Nodup) {E rest : List Edge}
    {e : Edge} (hsplit : E ++ e :: rest = μ) : ∀ e' ∈ E, e'.child ≠ e.child := by
  subst hsplit
  rw [List.map_append, List.map_cons] at hnd
  intro e' he' heq
  exact (List.nodup_append.1 hnd).2.2 e'.child (List.mem_map.mpr ⟨e', he', rfl⟩) e.child
    (List.mem_cons_self) heq

theorem inv_step {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {E rest : List Edge} {e : Edge}
    (hsplit : E ++ e :: rest = μ) {bs bs' : List UFBlock} (hinv : Inv P E bs)
    (hstep : ufStep bs e = some bs') : Inv P (E ++ [e]) bs' := by
  have heμ : e ∈ μ := by rw [← hsplit]; simp
  have hnc := not_child_of_split hwf.1 hsplit
  obtain ⟨hc_lt, hp_lt, -, -⟩ := hwf.2.1 e heμ
  obtain ⟨b1, hf1, hb1, hc⟩ := find_block hinv hc_lt
  obtain ⟨b2, hf2, hb2, hp⟩ := find_block hinv hp_lt
  unfold ufStep at hstep
  rw [hf1, hf2] at hstep
  simp only at hstep
  split at hstep
  · cases hstep
  · rename_i hne
    split at hstep
    · cases hstep
    · rename_i hany
      cases hstep
      have hdisj : ∀ t ∈ b1.ticks, t ∉ b2.ticks := by
        intro t ht1 ht2
        apply hany
        rw [List.any_eq_true]
        exact ⟨t, ht1, by simpa using ht2⟩
      exact inv_merge hinv hb1 hb2 hne hc hp hnc hdisj (by intro x; simp) (by intro t; simp)
        (fun b => mem_merged)

theorem block_root {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {E : List Edge}
    (hE : ∀ e ∈ E, e ∈ μ) {bs : List UFBlock} (hinv : Inv P E bs) {b : UFBlock} (hb : b ∈ bs)
    {x y : Nat} (hx : x ∈ b.members) (hy : y ∈ b.members) : μ.root x = μ.root y := by
  obtain ⟨h, -, -, hr⟩ := hinv.head b hb
  rw [(hr x hx).root_eq hwf hE, (hr y hy).root_eq hwf hE]

theorem block_inClass {P : Prog} {E : List Edge} {bs : List UFBlock} (hinv : Inv P E bs)
    {b : UFBlock} (hb : b ∈ bs) {x y : Nat} (hx : x ∈ b.members) (hy : y ∈ b.members)
    (hxy : x ≠ y) : ∃ e ∈ E, e.child = x ∨ e.parent = x := by
  obtain ⟨h, -, -, hr⟩ := hinv.head b hb
  by_cases hxh : x = h
  · subst hxh
    have hyx : y ≠ x := fun h' => hxy h'.symm
    obtain ⟨e, he, hpe⟩ := (hr y hy).parent_of_ne hyx
    exact ⟨e, he, Or.inr hpe⟩
  · obtain ⟨e, he, hce⟩ := (hr x hx).child_of_ne hxh
    exact ⟨e, he, Or.inl hce⟩

theorem step_some {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (hcad : ClassAddrDisjointW P μ)
    {E rest : List Edge} {e : Edge} (hsplit : E ++ e :: rest = μ) {bs : List UFBlock}
    (hinv : Inv P E bs) : ∃ bs', ufStep bs e = some bs' := by
  have heμ : e ∈ μ := by rw [← hsplit]; simp
  have hEμ : ∀ e' ∈ E, e' ∈ μ := by
    intro e' he'; rw [← hsplit]; exact List.mem_append_left _ he'
  have hnc := not_child_of_split hwf.1 hsplit
  obtain ⟨hc_lt, hp_lt, -, -⟩ := hwf.2.1 e heμ
  obtain ⟨b1, hf1, hb1, hc⟩ := find_block hinv hc_lt
  obtain ⟨b2, hf2, hb2, hp⟩ := find_block hinv hp_lt
  have hne : b1 ≠ b2 := by
    intro h12
    subst h12
    obtain ⟨h, -, -, hr⟩ := hinv.head b1 hb1
    have hch : e.child = h := (hr _ hc).eq_of_not_child hnc
    have hpc : Reach E e.parent e.child := by rw [hch]; exact hr _ hp
    exact no_cycle hwf hEμ heμ hpc
  have hinc : ∀ z, (∃ e' ∈ E, e'.child = z ∨ e'.parent = z) → μ.inClass z = true := by
    intro z ⟨e', he', hz⟩
    exact (inClass_iff μ z).2 ⟨e', hEμ e' he', hz⟩
  have hany : ¬ (b1.ticks.any (b2.ticks.contains ·)) = true := by
    intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨t, ht1, ht2⟩ := hany
    have ht2' : t ∈ b2.ticks := by simpa using ht2
    obtain ⟨x, hx, htx⟩ := (hinv.ticks b1 hb1 t).1 ht1
    obtain ⟨y, hy, hty⟩ := (hinv.ticks b2 hb2 t).1 ht2'
    have hxy : x ≠ y := by
      intro h; subst h; exact hne (hinv.uniq b1 hb1 b2 hb2 x hx hy)
    obtain ⟨hax, hay, hov⟩ := (common_tick P x y).1 ⟨t, htx, hty⟩
    apply hcad x (hinv.mem_lt b1 hb1 x hx) y (hinv.mem_lt b2 hb2 y hy) hxy _ hax hay hov
    have hix : μ.inClass x = true := by
      by_cases hxc : x = e.child
      · exact (inClass_iff μ x).2 ⟨e, heμ, Or.inl hxc.symm⟩
      · exact hinc x (block_inClass hinv hb1 hx hc hxc)
    have hiy : μ.inClass y = true := by
      by_cases hyp : y = e.parent
      · exact (inClass_iff μ y).2 ⟨e, heμ, Or.inr hyp.symm⟩
      · exact hinc y (block_inClass hinv hb2 hy hp hyp)
    have hroot : μ.root x = μ.root y := by
      rw [block_root hwf hEμ hinv hb1 hx hc, root_edge hwf heμ,
        block_root hwf hEμ hinv hb2 hp hy]
    simp only [Forest.sameClass, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hix, hiy⟩, hroot⟩
  refine ⟨⟨b1.members ++ b2.members, b1.ticks ++ b2.ticks⟩ ::
    bs.filter (fun b => b != b1 && b != b2), ?_⟩
  unfold ufStep
  rw [hf1, hf2]
  simp only [hne, hany, Bool.false_eq_true, ite_false]

theorem fold_inv {P : Prog} {μ : Forest} (hwf : ForestWF P μ) :
    ∀ (rest E : List Edge) (bs bs' : List UFBlock), E ++ rest = μ → Inv P E bs →
      rest.foldlM ufStep bs = some bs' → Inv P μ bs' := by
  intro rest
  induction rest with
  | nil =>
    intro E bs bs' hsplit hinv hfold
    rw [List.append_nil] at hsplit
    subst hsplit
    rw [List.foldlM_nil] at hfold
    cases hfold
    exact hinv
  | cons e rest ih =>
    intro E bs bs' hsplit hinv hfold
    rw [List.foldlM_cons] at hfold
    cases hs : ufStep bs e with
    | none => rw [hs] at hfold; cases hfold
    | some bs'' =>
      rw [hs] at hfold
      exact ih (E ++ [e]) bs'' bs' (by rw [List.append_assoc, List.singleton_append]; exact hsplit)
        (inv_step hwf hsplit hinv hs) hfold

theorem fold_some {P : Prog} {μ : Forest} (hwf : ForestWF P μ) (hcad : ClassAddrDisjointW P μ) :
    ∀ (rest E : List Edge) (bs : List UFBlock), E ++ rest = μ → Inv P E bs →
      ∃ bs', rest.foldlM ufStep bs = some bs' := by
  intro rest
  induction rest with
  | nil =>
    intro E bs _ _
    exact ⟨bs, rfl⟩
  | cons e rest ih =>
    intro E bs hsplit hinv
    rw [List.foldlM_cons]
    obtain ⟨bs'', hs⟩ := step_some hwf hcad hsplit hinv
    rw [hs]
    exact ih (E ++ [e]) bs'' (by rw [List.append_assoc, List.singleton_append]; exact hsplit)
      (inv_step hwf hsplit hinv hs)

theorem reach_sameblock {P : Prog} {μ : Forest} (hwf : ForestWF P μ) {bs : List UFBlock}
    (hinv : Inv P μ bs) {x y : Nat} (h : Reach μ x y) (hx : x < P.nloc) :
    ∃ b ∈ bs, x ∈ b.members ∧ y ∈ b.members := by
  induction h with
  | refl x =>
    obtain ⟨b, hb, hxb⟩ := hinv.cover x hx
    exact ⟨b, hb, hxb, hxb⟩
  | step e y he _ ih =>
    obtain ⟨b, hb, hcb, hpb⟩ := hinv.edges e he
    obtain ⟨b', hb', hpb', hyb'⟩ := ih (hwf.2.1 e he).2.1
    have hbb := hinv.uniq b hb b' hb' _ hpb hpb'
    subst hbb
    exact ⟨b, hb, hcb, hyb'⟩

end UF

open UF

/-- The union–find with interval union decides the window-insensitive root-level check, for
well-formed forests. -/
theorem ufCheck_eq_true_iff_classAddrDisjointW (P : Prog) (μ : Forest) (hwf : ForestWF P μ) :
    ufCheck P μ = true ↔ ClassAddrDisjointW P μ := by
  constructor
  · intro h
    unfold ufCheck at h
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 h
    have hinv := fold_inv hwf μ [] (ufInit P) bs (List.nil_append μ) (inv_init P) hbs
    intro u hu v hv huv hsc hau hav hov
    obtain ⟨t, htu, htv⟩ := (common_tick P u v).2 ⟨hau, hav, hov⟩
    have hroot : μ.root u = μ.root v := by
      simp only [Forest.sameClass, Bool.and_eq_true, beq_iff_eq] at hsc
      exact hsc.2
    obtain ⟨b, hb, hub, hrb⟩ := reach_sameblock hwf hinv (reach_resolveF μ μ.length u) hu
    obtain ⟨b', hb', hvb', hrb'⟩ := reach_sameblock hwf hinv (reach_resolveF μ μ.length v) hv
    have hrb2 : μ.root u ∈ b'.members := by rw [hroot]; exact hrb'
    have hbb := hinv.uniq b hb b' hb' _ hrb hrb2
    subst hbb
    exact hinv.disj b hb u hub v hvb' huv t htu htv
  · intro hcad
    unfold ufCheck
    obtain ⟨bs, hbs⟩ := fold_some hwf hcad μ [] (ufInit P) (List.nil_append μ) (inv_init P)
    rw [hbs]
    rfl

end Toy.Coalesce
