import ToyPredTrans.Programs

/-!
# When finitary conjunctivity suffices: finite, `Nat → Bool`-injective, and arbitrary state types

Everything in this file is fully proved.

The transformer `eventually` shows that the finitary laws (monotone, binary conjunctive,
strict, top preserving) do not force a transformer on an infinite state type to be a `wp`.
This file records three complementary positive facts:

* on a *finite* state type, binary conjunctivity alone forces positive conjunctivity;
* on a state type that injects into `Nat → Bool` (in particular on every countable state
  type, and on the uncountable type `Nat → Bool` itself), binary conjunctivity together with
  ω-continuity forces positive conjunctivity;
* on *every* state type, binary conjunctivity together with continuity over directed
  families forces positive conjunctivity.

In each case the characterization of `wp` then yields a relational representation.  All
three proofs use classical logic, and each statement, restricted to the one-point state type,
already implies excluded middle (`lem_of_conjNonempty_of_conjBin_of_finiteState` and its
companions in `Witnesses`).
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-- The common finite-intersection step.  Fix a start state `s` and let `K` be the
intersection of all postconditions established from `s`.  If a binary conjunctive `T`
establishes `K` enlarged by finitely many states, it establishes `K` itself: each added state
outside `K` is excluded by some established postcondition, and finitely many of these can be
intersected. -/
theorem kernel_established_of_list {T : Transformer σ} (hb : ConjBin T) (s : σ) (l : List σ)
    (h : T (fun x => (∀ Q, T Q s → Q x) ∨ x ∈ l) s) :
    T (fun x => ∀ Q, T Q s → Q x) s := by
  have hm : Monotone T := monotone_of_conjBin hb
  induction l with
  | nil =>
    refine hm _ _ ?_ s h
    intro x hx
    rcases hx with hk | hmem
    · exact hk
    · cases hmem
  | cons a l ih =>
    apply ih
    by_cases hKa : ∀ Q, T Q s → Q a
    · refine hm _ (fun x => (∀ Q, T Q s → Q x) ∨ x ∈ l) ?_ s h
      intro x hx
      show (∀ Q, T Q s → Q x) ∨ x ∈ l
      rcases hx with hk | hmem
      · exact Or.inl hk
      · rcases List.mem_cons.mp hmem with e | hl
        · rw [e]
          exact Or.inl hKa
        · exact Or.inr hl
    · have hex : ∃ Q₀, T Q₀ s ∧ ¬ Q₀ a := by
        apply Classical.byContradiction
        intro hne
        apply hKa
        intro Q hQ
        apply Classical.byContradiction
        intro hq
        exact hne ⟨Q, hQ, hq⟩
      obtain ⟨Q₀, hQ₀, hnq⟩ := hex
      have hand := (hb (fun x => (∀ Q, T Q s → Q x) ∨ x ∈ a :: l) Q₀ s).mpr ⟨h, hQ₀⟩
      refine hm _ (fun x => (∀ Q, T Q s → Q x) ∨ x ∈ l) ?_ s hand
      intro x hx
      obtain ⟨hx1, hq⟩ := hx
      show (∀ Q, T Q s → Q x) ∨ x ∈ l
      rcases hx1 with hk | hmem
      · exact Or.inl hk
      · rcases List.mem_cons.mp hmem with e | hl
        · rw [e] at hq
          exact absurd hq hnq
        · exact Or.inr hl

/-- **On a finite state type, binary conjunctivity implies positive conjunctivity.**  So on a
finite state type the finitary law already characterizes the `wp`s. -/
theorem conjNonempty_of_conjBin_of_finiteState
    (hσ : FiniteState σ) {T : Transformer σ} (hb : ConjBin T) : ConjNonempty T := by
  obtain ⟨l, hl⟩ := hσ
  have hm : Monotone T := monotone_of_conjBin hb
  intro ι Q hι s
  constructor
  · intro h i
    exact hm _ _ (fun t ht => ht i) s h
  · intro h
    obtain ⟨i₀⟩ := hι
    have htop : T (fun _ => True) s := hm _ _ (fun _ _ => trivial) s (h i₀)
    have hK := kernel_established_of_list hb s l
      (hm _ (fun x => (∀ Q, T Q s → Q x) ∨ x ∈ l) (fun x _ => Or.inr (hl x)) s htop)
    exact hm _ _ (fun x hx i => hx (Q i) (h i)) s hK

/-- **On a countable state type, binary conjunctivity and ω-continuity imply positive
conjunctivity.**  (A special case of
`conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState`, proved directly.)

Proof idea: fix a start state `s` with `T True s`, and let `K` be the intersection of all
postconditions established from `s`.  Enumerate the states; the sets
`K ∪ {x | index x < n}` form a chain with union `True`, so by continuity one of them is
established.  Each of the finitely many states of index `< n` outside `K` is excluded by some
established postcondition; intersecting finitely many of them (binary conjunctivity) shows
that `K` itself is established. -/
theorem conjNonempty_of_conjBin_of_omegaContinuous_of_countable
    (hσ : CountableState σ) {T : Transformer σ} (hb : ConjBin T) (hc : OmegaContinuous T) :
    ConjNonempty T := by
  obtain ⟨f, hf⟩ := hσ
  have hm : Monotone T := monotone_of_conjBin hb
  have key : ∀ s, T (fun _ => True) s → T (fun x => ∀ Q, T Q s → Q x) s := by
    intro s htop
    have step : ∀ n, T (fun x => (∀ Q, T Q s → Q x) ∨ f x < n) s →
        T (fun x => ∀ Q, T Q s → Q x) s := by
      intro n
      induction n with
      | zero =>
        intro h
        refine hm _ _ ?_ s h
        intro x hx
        rcases hx with hk | h0
        · exact hk
        · exact absurd h0 (Nat.not_lt_zero _)
      | succ n ih =>
        intro h
        apply ih
        by_cases hx0 : ∃ x₀, f x₀ = n ∧ ¬ ∀ Q, T Q s → Q x₀
        · obtain ⟨x₀, hfx, hK⟩ := hx0
          have hex : ∃ Q₀, T Q₀ s ∧ ¬ Q₀ x₀ := by
            apply Classical.byContradiction
            intro hne
            apply hK
            intro Q hQ
            apply Classical.byContradiction
            intro hq
            exact hne ⟨Q, hQ, hq⟩
          obtain ⟨Q₀, hQ₀, hnq⟩ := hex
          have hand := (hb (fun x => (∀ Q, T Q s → Q x) ∨ f x < n + 1) Q₀ s).mpr ⟨h, hQ₀⟩
          refine hm _ (fun x => (∀ Q, T Q s → Q x) ∨ f x < n) ?_ s hand
          intro x hx
          obtain ⟨hx1, hq⟩ := hx
          show (∀ Q, T Q s → Q x) ∨ f x < n
          rcases hx1 with hk | hlt
          · exact Or.inl hk
          · have hlt' : f x < n + 1 := hlt
            by_cases hfn : f x = n
            · have e : x = x₀ := hf _ _ (hfn.trans hfx.symm)
              rw [e] at hq
              exact absurd hq hnq
            · have hlt'' : f x < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') hfn
              exact Or.inr hlt''
        · refine hm _ (fun x => (∀ Q, T Q s → Q x) ∨ f x < n) ?_ s h
          intro x hx
          show (∀ Q, T Q s → Q x) ∨ f x < n
          rcases hx with hk | hlt
          · exact Or.inl hk
          · have hlt' : f x < n + 1 := hlt
            by_cases hfn : f x = n
            · refine Or.inl ?_
              apply Classical.byContradiction
              intro hK
              exact hx0 ⟨x, hfn, hK⟩
            · have hlt'' : f x < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') hfn
              exact Or.inr hlt''
    have hchain : Chain (fun (n : Nat) (x : σ) => (∀ Q, T Q s → Q x) ∨ f x < n) := by
      intro n x hx
      show (∀ Q, T Q s → Q x) ∨ f x < n + 1
      rcases hx with hk | hlt
      · exact Or.inl hk
      · have hlt' : f x < n := hlt
        have hlt'' : f x < n + 1 := Nat.lt_succ_of_lt hlt'
        exact Or.inr hlt''
    have hall : T (fun x => ∃ n, (∀ Q, T Q s → Q x) ∨ f x < n) s :=
      hm _ _ (fun x _ => ⟨f x + 1, Or.inr (Nat.lt_succ_self _)⟩) s htop
    obtain ⟨n, hn⟩ := hc _ hchain s hall
    exact step n hn
  intro ι Q hι s
  constructor
  · intro h i
    exact hm _ _ (fun t ht => ht i) s h
  · intro h
    obtain ⟨i₀⟩ := hι
    have htop : T (fun _ => True) s := hm _ _ (fun _ _ => trivial) s (h i₀)
    exact hm _ _ (fun x hx i => hx (Q i) (h i)) s (key s htop)

/-! ## Directed continuity: no hypothesis on the state type -/

/-- **On every state type, binary conjunctivity and continuity over directed families imply
positive conjunctivity.**

Proof idea: fix `s` with `T True s` and let `K` be the intersection of all postconditions
established from `s`.  The sets `K ∪ l`, indexed by lists `l` of states, form a directed family
whose union is everything, so one of them is established; `kernel_established_of_list` removes
the finitely many extra states. -/
theorem conjNonempty_of_conjBin_of_dirContinuous
    {T : Transformer σ} (hb : ConjBin T) (hd : DirContinuous T) : ConjNonempty T := by
  have hm : Monotone T := monotone_of_conjBin hb
  have key : ∀ s, T (fun _ => True) s → T (fun x => ∀ Q, T Q s → Q x) s := by
    intro s htop
    let D : List σ → Pred σ := fun l x => (∀ Q, T Q s → Q x) ∨ x ∈ l
    have hdir : Directed D := by
      refine ⟨⟨[]⟩, fun l₁ l₂ => ⟨l₁ ++ l₂, fun x hx => ?_, fun x hx => ?_⟩⟩
      · rcases hx with hk | hmem
        · exact Or.inl hk
        · exact Or.inr (List.mem_append_left _ hmem)
      · rcases hx with hk | hmem
        · exact Or.inl hk
        · exact Or.inr (List.mem_append_right _ hmem)
    have hall : T (fun x => ∃ l, D l x) s :=
      hm _ _ (fun x _ => ⟨[x], Or.inr List.mem_cons_self⟩) s htop
    obtain ⟨l, hl⟩ := hd (List σ) D hdir s hall
    exact kernel_established_of_list hb s l hl
  intro ι Q hι s
  constructor
  · intro h i
    exact hm _ _ (fun t ht => ht i) s h
  · intro h
    obtain ⟨i₀⟩ := hι
    have htop : T (fun _ => True) s := hm _ _ (fun _ _ => trivial) s (h i₀)
    exact hm _ _ (fun x hx i => hx (Q i) (h i)) s (key s htop)

/-- Directed continuity of a `wp` forces bounded nondeterminism on the non-aborting states:
the lists of states form a directed family whose union is everything.  (No classical logic is
used.) -/
theorem finiteImage_on_term_of_dirContinuous_wp {R : Rel σ} {term : Pred σ}
    (h : DirContinuous (wp R term)) : ∀ s, term s → FiniteImage R s := by
  intro s hs
  let D : List σ → Pred σ := fun l x => x ∈ l
  have hdir : Directed D :=
    ⟨⟨[]⟩, fun l₁ l₂ => ⟨l₁ ++ l₂, fun x hx => List.mem_append_left _ hx,
      fun x hx => List.mem_append_right _ hx⟩⟩
  have hall : wp R term (fun x => ∃ l, D l x) s :=
    ⟨hs, fun x _ => ⟨[x], List.mem_cons_self⟩⟩
  obtain ⟨l, hl⟩ := h (List σ) D hdir s hall
  exact ⟨l, hl.2⟩

/-! ## State types of at most the cardinality of the continuum -/

/-- All bit lists of length `k`. -/
private def allBitLists : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 =>
    (allBitLists k).map (fun p => p ++ [false]) ++ (allBitLists k).map (fun p => p ++ [true])

/-- The first `k` bits of a bit sequence. -/
private def prefixBits (g : Nat → Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => prefixBits g k ++ [g k]

private theorem prefixBits_length (g : Nat → Bool) : ∀ k, (prefixBits g k).length = k
  | 0 => rfl
  | k + 1 => by simp [prefixBits, prefixBits_length g k]

private theorem prefixBits_mem_allBitLists (g : Nat → Bool) :
    ∀ k, prefixBits g k ∈ allBitLists k
  | 0 => by simp [prefixBits, allBitLists]
  | k + 1 => by
    simp only [prefixBits, allBitLists, List.mem_append, List.mem_map]
    cases hgk : g k
    · exact Or.inl ⟨prefixBits g k, prefixBits_mem_allBitLists g k, rfl⟩
    · exact Or.inr ⟨prefixBits g k, prefixBits_mem_allBitLists g k, rfl⟩

private theorem prefixBits_getElem (g : Nat → Bool) :
    ∀ (k i : Nat) (hi : i < (prefixBits g k).length), (prefixBits g k)[i] = g i
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    have hk : (prefixBits g k).length = k := prefixBits_length g k
    have hi' : i < k + 1 := by rw [prefixBits_length] at hi; exact hi
    simp only [prefixBits]
    by_cases hlt : i < k
    · rw [List.getElem_append_left (by omega)]
      exact prefixBits_getElem g k i (by omega)
    · have heq : i = k := by omega
      subst heq
      rw [List.getElem_append_right (by omega)]
      simp [hk]

/-- `p` is a prefix of `q`. -/
private def IsPrefix (p q : List Bool) : Prop :=
  ∃ h : p.length ≤ q.length, ∀ (i : Nat) (hi : i < p.length), q[i]'(Nat.lt_of_lt_of_le hi h) = p[i]

private theorem isPrefix_refl (p : List Bool) : IsPrefix p p :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem isPrefix_trans {p q r : List Bool} (h1 : IsPrefix p q) (h2 : IsPrefix q r) :
    IsPrefix p r := by
  obtain ⟨hl1, hf1⟩ := h1
  obtain ⟨hl2, hf2⟩ := h2
  refine ⟨Nat.le_trans hl1 hl2, fun i hi => ?_⟩
  rw [hf2 i (Nat.lt_of_lt_of_le hi hl1), hf1 i hi]

private theorem isPrefix_append_singleton (p : List Bool) (b : Bool) : IsPrefix p (p ++ [b]) :=
  ⟨by simp, fun i hi => by rw [List.getElem_append_left hi]⟩

private theorem isPrefix_step_cases {p q : List Bool} (hpq : IsPrefix p q)
    (hlt : p.length < q.length) :
    IsPrefix (p ++ [false]) q ∨ IsPrefix (p ++ [true]) q := by
  obtain ⟨hl, hf⟩ := hpq
  have hlen : (p ++ [false]).length ≤ q.length := by simp; omega
  have hlen' : (p ++ [true]).length ≤ q.length := by simp; omega
  cases hq : q[p.length]'hlt with
  | false =>
    left
    refine ⟨hlen, fun i hi => ?_⟩
    by_cases h : i < p.length
    · rw [List.getElem_append_left h]; exact hf i h
    · have heq : i = p.length := by simp at hi; omega
      subst heq; rw [List.getElem_append_right (Nat.le_refl _)]; simp [hq]
  | true =>
    right
    refine ⟨hlen', fun i hi => ?_⟩
    by_cases h : i < p.length
    · rw [List.getElem_append_left h]; exact hf i h
    · have heq : i = p.length := by simp at hi; omega
      subst heq; rw [List.getElem_append_right (Nat.le_refl _)]; simp [hq]

/-- The cylinder of states whose code begins with the bit list `p`. -/
private def Cyl (f : σ → Nat → Bool) (p : List Bool) (x : σ) : Prop :=
  ∀ (i : Nat) (hi : i < p.length), f x i = p[i]

private theorem cyl_prefixBits (f : σ → Nat → Bool) (x : σ) (k : Nat) :
    Cyl f (prefixBits (f x) k) x :=
  fun i hi => (prefixBits_getElem (f x) k i hi).symm

private theorem cyl_mono (f : σ → Nat → Bool) {p q : List Bool} (hpq : IsPrefix p q)
    {x : σ} (hx : Cyl f q x) : Cyl f p x := by
  obtain ⟨hl, hf⟩ := hpq
  intro i hi
  rw [← hf i hi]
  exact hx i (Nat.lt_of_lt_of_le hi hl)

private theorem cyl_append_iff (f : σ → Nat → Bool) (p : List Bool) (b : Bool)
    (x : σ) : Cyl f (p ++ [b]) x ↔ Cyl f p x ∧ f x p.length = b := by
  constructor
  · intro h
    refine ⟨cyl_mono f (isPrefix_append_singleton p b) h, ?_⟩
    have h1 := h p.length (by simp)
    rw [List.getElem_append_right (Nat.le_refl _)] at h1
    simpa using h1
  · rintro ⟨hp, hb⟩ i hi
    by_cases h : i < p.length
    · rw [List.getElem_append_left h]; exact hp i h
    · have heq : i = p.length := by simp at hi; omega
      subst heq; rw [List.getElem_append_right (Nat.le_refl _)]; simpa using hb

private theorem cyl_disjoint_of_sibling (f : σ → Nat → Bool)
    {q r₁ r₂ : List Bool} {b : Bool}
    (h1 : IsPrefix (q ++ [b]) r₁) (h2 : IsPrefix (q ++ [!b]) r₂)
    {x : σ} (hx1 : Cyl f r₁ x) (hx2 : Cyl f r₂ x) : False := by
  have hb1 : f x q.length = b := ((cyl_append_iff f q b x).mp (cyl_mono f h1 hx1)).2
  have hb2 : f x q.length = !b := ((cyl_append_iff f q (!b) x).mp (cyl_mono f h2 hx2)).2
  rw [hb1] at hb2
  cases b <;> cases hb2

private theorem conjBin_list {T : Transformer σ} (hb : ConjBin T) (s : σ)
    (htop : T (fun _ => True) s) :
    ∀ (L : List (List Bool)) (P : List Bool → Pred σ),
      (∀ p, p ∈ L → T (P p) s) → T (fun x => ∀ p, p ∈ L → P p x) s
  | [], _, _ => monotone_of_conjBin hb _ _ (fun _ _ _ hp => by cases hp) s htop
  | a :: L, P, h => by
    have ha : T (P a) s := h a List.mem_cons_self
    have hL : T (fun x => ∀ p, p ∈ L → P p x) s :=
      conjBin_list hb s htop L P fun p hp => h p (List.mem_cons_of_mem _ hp)
    have hand := (hb (P a) (fun x => ∀ p, p ∈ L → P p x) s).mpr ⟨ha, hL⟩
    refine monotone_of_conjBin hb _ _ ?_ s hand
    intro x ⟨hxa, hxL⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hxa
    · exact hxL p hp'

/-- **On a state type that injects into `Nat → Bool`, binary conjunctivity and ω-continuity
imply positive conjunctivity.**  This covers every countable state type and the uncountable
type `Nat → Bool` of infinite bit sequences.

Proof idea: code states by bit sequences and fix `s` with `T True s`.  Call a finite bit list
`p` *positive* when `T` does not establish "the code does not begin with `p`".  ω-continuity
rules out infinitely many splitting positive nodes along a branch (otherwise one obtains an
infinite family of pairwise disjoint positive cylinders, whose complements form a chain with
union everything); so beyond some depth `N` positive nodes do not split, and at most `2^N`
states have all their prefixes positive.  These finitely many states form a list, and a second
use of ω-continuity together with `kernel_established_of_list` shows that the intersection of
all established postconditions is established. -/
theorem conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState
    (hσ : ContinuumState σ) {T : Transformer σ} (hb : ConjBin T) (hc : OmegaContinuous T) :
    ConjNonempty T := by
  obtain ⟨f, hf⟩ := hσ
  have hm : Monotone T := monotone_of_conjBin hb
  have key : ∀ s, T (fun _ => True) s → T (fun x => ∀ Q, T Q s → Q x) s := by
    intro s htop
    let Pos (p : List Bool) : Prop := ¬ T (fun x => ¬ Cyl f p x) s
    have pos_mono : ∀ {p q : List Bool}, IsPrefix p q → Pos q → Pos p := fun hpq hq hp =>
      hq (hm _ _ (fun x hnp hq' => hnp (cyl_mono f hpq hq')) s hp)
    let Splits (p : List Bool) : Prop := Pos (p ++ [false]) ∧ Pos (p ++ [true])
    let Many (p : List Bool) : Prop := ∀ n : Nat, ∃ q, IsPrefix p q ∧ n ≤ q.length ∧ Splits q
    have many_child : ∀ p, Many p → Many (p ++ [false]) ∨ Many (p ++ [true]) := by
      intro p hmany
      apply Classical.byContradiction
      intro hneither
      have h0 : ∃ n0, ∀ q, IsPrefix (p ++ [false]) q → n0 ≤ q.length → ¬ Splits q := by
        apply Classical.byContradiction; intro h; apply hneither; left; intro n
        apply Classical.byContradiction; intro hn
        exact h ⟨n, fun q hq hlen hsp => hn ⟨q, hq, hlen, hsp⟩⟩
      have h1 : ∃ n1, ∀ q, IsPrefix (p ++ [true]) q → n1 ≤ q.length → ¬ Splits q := by
        apply Classical.byContradiction; intro h; apply hneither; right; intro n
        apply Classical.byContradiction; intro hn
        exact h ⟨n, fun q hq hlen hsp => hn ⟨q, hq, hlen, hsp⟩⟩
      obtain ⟨n0, hn0⟩ := h0
      obtain ⟨n1, hn1⟩ := h1
      obtain ⟨q, hpq, hlen, hsp⟩ := hmany (n0 + n1 + p.length + 1)
      rcases isPrefix_step_cases hpq (by omega) with hf0 | ht1
      · exact hn0 q hf0 (by omega) hsp
      · exact hn1 q ht1 (by omega) hsp
    have many_next : ∀ p, Many p →
        ∃ (q : List Bool) (b : Bool), IsPrefix p q ∧ Pos (q ++ [!b]) ∧ Many (q ++ [b]) := by
      intro p hmany
      obtain ⟨r, hpr, _, hspr⟩ := hmany 0
      suffices ∀ d p, Many p → ∀ r, IsPrefix p r → Splits r → r.length - p.length ≤ d →
          ∃ (q : List Bool) (b : Bool), IsPrefix p q ∧ Pos (q ++ [!b]) ∧ Many (q ++ [b]) from
        this (r.length - p.length) p hmany r hpr hspr (Nat.le_refl _)
      intro d
      induction d with
      | zero =>
        intro p hmany r hpr hspr hle
        by_cases hsp : Splits p
        · rcases many_child p hmany with hm0 | hm1
          · exact ⟨p, false, isPrefix_refl p, hsp.2, hm0⟩
          · exact ⟨p, true, isPrefix_refl p, hsp.1, hm1⟩
        · have heq : p.length = r.length := by have := hpr.1; omega
          have hpr_eq : p = r := List.ext_getElem heq fun i h1 _ => (hpr.2 i h1).symm
          rw [hpr_eq] at hsp; exact absurd hspr hsp
      | succ d ih =>
        intro p hmany r hpr hspr hle
        by_cases hsp : Splits p
        · rcases many_child p hmany with hm0 | hm1
          · exact ⟨p, false, isPrefix_refl p, hsp.2, hm0⟩
          · exact ⟨p, true, isPrefix_refl p, hsp.1, hm1⟩
        · have hlt : p.length < r.length := by
            have hle' := hpr.1
            by_cases heq : p.length = r.length
            · have hpr_eq : p = r := List.ext_getElem heq fun i h1 _ => (hpr.2 i h1).symm
              rw [hpr_eq] at hsp; exact absurd hspr hsp
            · omega
          rcases isPrefix_step_cases hpr hlt with hr0 | hr1
          · have hpos0 : Pos (p ++ [false]) :=
              pos_mono hr0 (pos_mono (isPrefix_append_singleton r false) hspr.1)
            have hnpos1 : ¬ Pos (p ++ [true]) := fun hp1 => hsp ⟨hpos0, hp1⟩
            have hmany0 : Many (p ++ [false]) := by
              rcases many_child p hmany with hm0 | hm1
              · exact hm0
              · obtain ⟨q, hq, _, hsq⟩ := hm1 0
                exact absurd (pos_mono hq (pos_mono (isPrefix_append_singleton q false) hsq.1))
                  hnpos1
            obtain ⟨q, b, hq, hpb, hmb⟩ := ih (p ++ [false]) hmany0 r hr0 hspr (by simp; omega)
            exact ⟨q, b, isPrefix_trans (isPrefix_append_singleton p false) hq, hpb, hmb⟩
          · have hpos1 : Pos (p ++ [true]) :=
              pos_mono hr1 (pos_mono (isPrefix_append_singleton r false) hspr.1)
            have hnpos0 : ¬ Pos (p ++ [false]) := fun hp0 => hsp ⟨hp0, hpos1⟩
            have hmany1 : Many (p ++ [true]) := by
              rcases many_child p hmany with hm0 | hm1
              · obtain ⟨q, hq, _, hsq⟩ := hm0 0
                exact absurd (pos_mono hq (pos_mono (isPrefix_append_singleton q false) hsq.1))
                  hnpos0
              · exact hm1
            obtain ⟨q, b, hq, hpb, hmb⟩ := ih (p ++ [true]) hmany1 r hr1 hspr (by simp; omega)
            exact ⟨q, b, isPrefix_trans (isPrefix_append_singleton p true) hq, hpb, hmb⟩
    have hnotMany : ¬ Many [] := by
      intro hmany0
      let stepFn : (st : { p : List Bool // Many p }) →
          { next : { p : List Bool // Many p } × (List Bool × Bool) //
              IsPrefix st.1 next.2.1 ∧
              next.1.1 = next.2.1 ++ [next.2.2] ∧
              Pos (next.2.1 ++ [!next.2.2]) } :=
        fun st =>
          let q := Classical.choose (many_next st.1 st.2)
          let hq := Classical.choose_spec (many_next st.1 st.2)
          let b := Classical.choose hq
          let hb := Classical.choose_spec hq
          ⟨(⟨q ++ [b], hb.2.2⟩, (q, b)), hb.1, rfl, hb.2.1⟩
      let seq : Nat → { p : List Bool // Many p } :=
        Nat.rec ⟨[], hmany0⟩ (fun _ st => (stepFn st).1.1)
      let qk (k : Nat) : List Bool := (stepFn (seq k)).1.2.1
      let bk (k : Nat) : Bool := (stepFn (seq k)).1.2.2
      let dk (k : Nat) : List Bool := qk k ++ [!bk k]
      have hseq_pref_q : ∀ k, IsPrefix (seq k).1 (qk k) := fun k => (stepFn (seq k)).2.1
      have hseq_succ : ∀ k, (seq (k + 1)).1 = qk k ++ [bk k] := fun k => (stepFn (seq k)).2.2.1
      have hdk_pos : ∀ k, Pos (dk k) := fun k => (stepFn (seq k)).2.2.2
      have hseq_mono : ∀ {i j}, i ≤ j → IsPrefix (seq i).1 (seq j).1 := by
        intro i j hij
        induction hij with
        | refl => exact isPrefix_refl _
        | step _ ih =>
          refine isPrefix_trans ih ?_
          rw [hseq_succ]
          exact isPrefix_trans (hseq_pref_q _) (isPrefix_append_singleton _ _)
      have hdisj : ∀ {i j : Nat}, i < j → ∀ x, Cyl f (dk i) x → Cyl f (dk j) x → False := by
        intro i j hij x hxi hxj
        have h1 : IsPrefix (qk i ++ [bk i]) (dk j) := by
          rw [← hseq_succ i]
          exact isPrefix_trans (hseq_mono hij)
            (isPrefix_trans (hseq_pref_q j) (isPrefix_append_singleton _ _))
        exact cyl_disjoint_of_sibling f h1 (isPrefix_refl (dk i)) hxj hxi
      let Q : Nat → Pred σ := fun n x => ∀ k, n ≤ k → ¬ Cyl f (dk k) x
      have hQchain : Chain Q := fun n x hx k hk => hx k (by omega)
      have hQall : ∀ x, ∃ n, Q n x := by
        intro x
        by_cases h : ∃ k, Cyl f (dk k) x
        · obtain ⟨k, hk⟩ := h
          exact ⟨k + 1, fun j hj hxj => hdisj (by omega) x hk hxj⟩
        · exact ⟨0, fun k _ hxk => h ⟨k, hxk⟩⟩
      obtain ⟨n, hn⟩ := hc Q hQchain s (hm _ _ (fun x _ => hQall x) s htop)
      exact hdk_pos n (hm _ _ (fun x hx => hx n (Nat.le_refl n)) s hn)
    have hbound : ∃ N : Nat, ∀ q : List Bool, N ≤ q.length → ¬ Splits q := by
      apply Classical.byContradiction; intro h; apply hnotMany; intro n
      apply Classical.byContradiction; intro hn
      exact h ⟨n, fun q hlen hsp =>
        hn ⟨q, ⟨Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩, hlen, hsp⟩⟩
    obtain ⟨N, hN⟩ := hbound
    let Good (x : σ) : Prop := ∀ k, Pos (prefixBits (f x) k)
    have unique_good : ∀ p (x y : σ), prefixBits (f x) N = p → prefixBits (f y) N = p →
        Good x → Good y → x = y := by
      intro p x y hxN hyN hgx hgy
      apply hf; funext k
      suffices ∀ d, prefixBits (f x) (N + d) = prefixBits (f y) (N + d) by
        have hm' := this (k + 1)
        have hkx := prefixBits_getElem (f x) (N + (k + 1)) k (by rw [prefixBits_length]; omega)
        have hky := prefixBits_getElem (f y) (N + (k + 1)) k (by rw [prefixBits_length]; omega)
        rw [← hkx, ← hky]; simp [hm']
      intro d
      induction d with
      | zero => exact hxN.trans hyN.symm
      | succ d ih =>
        have hpx : Pos (prefixBits (f x) (N + d) ++ [f x (N + d)]) := hgx (N + d + 1)
        have hpy : Pos (prefixBits (f y) (N + d) ++ [f y (N + d)]) := hgy (N + d + 1)
        rw [← ih] at hpy
        have hnosplit : ¬ Splits (prefixBits (f x) (N + d)) :=
          hN _ (by rw [prefixBits_length]; omega)
        have hbit : f x (N + d) = f y (N + d) := by
          cases hfxm : f x (N + d) <;> cases hfym : f y (N + d)
          · rfl
          · rw [hfxm] at hpx; rw [hfym] at hpy; exact absurd ⟨hpx, hpy⟩ hnosplit
          · rw [hfxm] at hpx; rw [hfym] at hpy; exact absurd ⟨hpy, hpx⟩ hnosplit
          · rfl
        show prefixBits (f x) (N + d) ++ [f x (N + d)] = prefixBits (f y) (N + d) ++ [f y (N + d)]
        rw [ih, hbit]
    let optList : List (List Bool) → List σ :=
      List.foldr (fun p acc =>
        @dite (List σ) (∃ x : σ, prefixBits (f x) N = p ∧ Good x) (Classical.propDecidable _)
          (fun h => Classical.choose h :: acc)
          (fun _ => acc)) []
    let L : List σ := optList (allBitLists N)
    have good_mem_L : ∀ x : σ, Good x → x ∈ L := by
      intro x hgx
      suffices ∀ ps : List (List Bool), prefixBits (f x) N ∈ ps → x ∈ optList ps from
        this (allBitLists N) (prefixBits_mem_allBitLists (f x) N)
      intro ps
      induction ps with
      | nil => intro h; cases h
      | cons p ps ih =>
        intro h
        simp only [optList, List.foldr_cons]
        rcases List.mem_cons.mp h with heq | htail
        · have hex : ∃ y : σ, prefixBits (f y) N = p ∧ Good y := ⟨x, heq, hgx⟩
          rw [dite_eq_left_of_eq_true (eq_true hex)]
          have hspec := Classical.choose_spec hex
          rw [unique_good p x (Classical.choose hex) heq hspec.1 hgx hspec.2]
          exact List.mem_cons_self
        · by_cases hex : ∃ y : σ, prefixBits (f y) N = p ∧ Good y
          · rw [dite_eq_left_of_eq_true (eq_true hex)]
            exact List.mem_cons_of_mem _ (ih htail)
          · rw [dite_eq_right_of_eq_false (eq_false hex)]
            exact ih htail
    let C : Nat → Pred σ := fun k x => x ∈ L ∨ ¬ Pos (prefixBits (f x) k)
    have hCchain : Chain C := by
      intro k x hx
      rcases hx with hL | hnp
      · exact Or.inl hL
      · exact Or.inr fun hp1 => hnp (pos_mono (isPrefix_append_singleton _ _) hp1)
    have hCall : ∀ x, ∃ k, C k x := by
      intro x
      by_cases hgx : Good x
      · exact ⟨0, Or.inl (good_mem_L x hgx)⟩
      · have hex : ∃ k, ¬ Pos (prefixBits (f x) k) := by
          apply Classical.byContradiction; intro hn; apply hgx; intro k
          exact Classical.byContradiction fun hnk => hn ⟨k, hnk⟩
        obtain ⟨k, hk⟩ := hex
        exact ⟨k, Or.inr hk⟩
    obtain ⟨k, hk⟩ := hc C hCchain s (hm _ _ (fun x _ => hCall x) s htop)
    have hTpos : T (fun x => Pos (prefixBits (f x) k)) s := by
      have hall := conjBin_list hb s htop (allBitLists k)
        (fun p x => Pos p ∨ ¬ Cyl f p x)
        (fun p _ => by
          by_cases hp : Pos p
          · exact hm _ _ (fun _ _ => Or.inl hp) s htop
          · exact hm _ _ (fun _ hx => Or.inr hx) s (Classical.byContradiction hp))
      refine hm _ _ ?_ s hall
      intro x hx
      rcases hx (prefixBits (f x) k) (prefixBits_mem_allBitLists (f x) k) with hp | hnc
      · exact hp
      · exact absurd (cyl_prefixBits f x k) hnc
    have hTL : T (fun x => (∀ Q, T Q s → Q x) ∨ x ∈ L) s := by
      have hand := (hb (C k) (fun x => Pos (prefixBits (f x) k)) s).mpr ⟨hk, hTpos⟩
      refine hm _ _ ?_ s hand
      intro x ⟨hcx, hpx⟩
      rcases hcx with hL | hnp
      · exact Or.inr hL
      · exact absurd hpx hnp
    exact kernel_established_of_list hb s L hTL
  intro ι Q hι s
  obtain ⟨i₀⟩ := hι
  constructor
  · intro h i; exact hm _ _ (fun t ht => ht i) s h
  · intro h
    have htop : T (fun _ => True) s := hm _ _ (fun _ _ => trivial) s (h i₀)
    exact hm _ _ (fun x hx i => hx (Q i) (h i)) s (key s htop)

end Toy.PredTrans
