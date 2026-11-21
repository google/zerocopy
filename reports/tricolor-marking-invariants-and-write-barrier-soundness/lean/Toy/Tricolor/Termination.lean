import Toy.Tricolor.Counterexamples

/-!
# Termination of marking

`markMeasure s = Σ_x weight (color x)` with `weight white = 2`, `weight grey = 1`,
`weight black = 0` (that is, `2·#white + #grey`).

* Collector scans of grey objects strictly decrease the measure; mutator steps other than
  allocation never increase it; an allocation of color `c` increases it by at most
  `weight c`.
* Paused mutator: every scans-only run has length at most `markMeasure s ≤ 2·n`, and some
  scans-only run reaches a state with no grey object.
* Active mutator: in every run, `#scans + markMeasure s' ≤ markMeasure s + Σ weight(allocation
  colors)`; when every allocation takes a cell that is white in the current state, the
  allocation term can be dropped.
* Termination: in an infinite execution in which, from some point on, no step increases the
  measure, a weakly fair collector reaches a state with no grey object, after which no object
  is ever grey again and no scan occurs. Eventually black-only allocation, or allocation of
  white cells only, gives this. Allocation that re-colors already marked cells grey can keep a
  collector-fair infinite execution grey forever.
-/

namespace Toy.Tricolor

variable {n : Nat}

/-- Weight of a color in the termination measure. -/
def weight : Color → Nat
  | .white => 2
  | .grey => 1
  | .black => 0

/-- The termination measure `2·#white + #grey`. -/
def markMeasure (s : St n) : Nat := ((List.finRange n).map (fun x => weight (s.color x))).sum

/-- The measure increase an allocation may cause (`weight c` for an allocation of color `c`,
zero for every other step). -/
def Op.allocWeight : Op n → Nat
  | .alloc _ c => weight c
  | _ => 0

/-! ## List sums -/

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_map_lt {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x)
    {a : α} (ha : a ∈ l) (hlt : f a < g a) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => cases ha
  | cons b t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := h b (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, f x ≤ g x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp ha with rfl | hat
    · have := sum_map_le t f g ht; omega
    · have := ih ht hat; omega

theorem sum_map_le_add_of_nodup {α : Type} (l : List α) (hl : l.Nodup) (f g : α → Nat)
    (a : α) (k : Nat) (h : ∀ x ∈ l, x ≠ a → f x ≤ g x) (ha : f a ≤ g a + k) :
    (l.map f).sum ≤ (l.map g).sum + k := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hnd := List.nodup_cons.mp hl
    by_cases hba : b = a
    · subst hba
      have : (t.map f).sum ≤ (t.map g).sum :=
        sum_map_le t f g (fun x hx => h x (List.mem_cons_of_mem _ hx)
          (fun e => hnd.1 (e ▸ hx)))
      omega
    · have hb := h b (List.mem_cons_self ..) hba
      have := ih hnd.2 (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega

theorem sum_map_le_mul {α : Type} (l : List α) (f : α → Nat) (k : Nat) (h : ∀ x, f x ≤ k) :
    (l.map f).sum ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    have := h a
    omega

theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup :=
  (List.pairwise_lt_finRange n).imp (fun {a b} h e => by subst e; exact Fin.lt_irrefl a h)

/-! ## The measure -/

theorem weight_le_two (c : Color) : weight c ≤ 2 := by cases c <;> decide

/-- The measure is at most `2·n`. -/
theorem markMeasure_le_two_mul (s : St n) : markMeasure s ≤ 2 * n := by
  have := sum_map_le_mul (List.finRange n) (fun x => weight (s.color x)) 2
    (fun x => weight_le_two _)
  simpa [markMeasure, List.length_finRange] using this

theorem sum_map_weight_eq (c : Fin n → Color) (l : List (Fin n)) :
    (l.map (fun x => weight (c x))).sum =
      2 * l.countP (fun x => c x == .white) + l.countP (fun x => c x == .grey) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons, List.countP_cons, ih]
    cases h : c a <;> simp [weight] <;> omega

/-- The measure is twice the number of white objects plus the number of grey objects. -/
theorem markMeasure_eq_two_mul_countWhite_add_countGrey (s : St n) :
    markMeasure s = 2 * (List.finRange n).countP (fun x => s.color x == .white) +
      (List.finRange n).countP (fun x => s.color x == .grey) :=
  sum_map_weight_eq s.color _

theorem markMeasure_le_of_shadeLe {s s' : St n} (h : ShadeLe s s') :
    markMeasure s' ≤ markMeasure s := by
  apply sum_map_le
  intro v _
  rcases h v with h | ⟨h1, h2⟩
  · rw [h]; exact Nat.le_refl _
  · rw [h1, h2]; decide

/-- **A collector scan of a grey object strictly decreases the measure.** -/
theorem markMeasure_scan_lt {s : St n} {g : Fin n} (hg : s.color g = .grey) :
    markMeasure (scan s g) < markMeasure s := by
  refine sum_map_lt _ _ _ ?_ (List.mem_finRange g) ?_
  · intro v _
    simp only [scan]
    by_cases hvg : v = g
    · simp only [hvg, ite_true]; exact Nat.zero_le _
    · simp only [hvg, ite_false]
      split
      · next h => rw [h.2]; decide
      · exact Nat.le_refl _
  · simp only [scan, ite_true, hg]; decide

theorem markMeasure_alloc_le (s : St n) (a : Fin n) (c : Color) :
    markMeasure (alloc s a c) ≤ markMeasure s + weight c := by
  apply sum_map_le_add_of_nodup _ (nodup_finRange n) _ _ a
  · intro x _ hxa
    simp [Tricolor.alloc, hxa]
  · simp [Tricolor.alloc]

/-- Allocating a cell that is white in the current state never increases the measure, whatever
the allocation color. -/
theorem markMeasure_alloc_le_of_white {s : St n} {a : Fin n} (hw : s.color a = .white)
    (c : Color) : markMeasure (alloc s a c) ≤ markMeasure s := by
  apply sum_map_le
  intro x _
  simp only [Tricolor.alloc]
  by_cases hxa : x = a
  · subst hxa
    simp only [ite_true, hw]
    exact weight_le_two c
  · simp [hxa]

theorem markMeasure_alloc_lt_of_white_of_ne_white {s : St n} {a : Fin n}
    (hw : s.color a = .white) {c : Color} (hc : c ≠ .white) :
    markMeasure (alloc s a c) < markMeasure s := by
  refine sum_map_lt _ _ _ ?_ (List.mem_finRange a) ?_
  · intro x _
    simp only [Tricolor.alloc]
    by_cases hxa : x = a
    · subst hxa; simp only [ite_true, hw]; exact weight_le_two c
    · simp [hxa]
  · simp only [Tricolor.alloc, ite_true, hw]
    cases c with
    | white => exact absurd rfl hc
    | grey => decide
    | black => decide

theorem markMeasure_lt_alloc_grey_of_black {s : St n} {a : Fin n} (hb : s.color a = .black) :
    markMeasure s < markMeasure (alloc s a .grey) := by
  refine sum_map_lt _ _ _ ?_ (List.mem_finRange a) ?_
  · intro x _
    simp only [Tricolor.alloc]
    by_cases hxa : x = a
    · subst hxa; simp only [ite_true, hb]; decide
    · simp [hxa]
  · simp only [Tricolor.alloc, ite_true, hb]; decide

/-- Per-step accounting: a scan pays one unit; other mutator steps are free; an allocation of
color `c` may add `weight c`. -/
theorem markMeasure_step {cfg : Config} {s : St n} {op : Op n} (hen : op.Enabled cfg s) :
    markMeasure (op.apply cfg s) + (if op.isScan then 1 else 0) ≤ markMeasure s + op.allocWeight := by
  cases op with
  | scan g =>
    have := markMeasure_scan_lt (s := s) hen
    simp only [Op.apply, Op.isScan, Op.allocWeight, ite_true]
    omega
  | store x y =>
    have := markMeasure_le_of_shadeLe (shadeLe_store cfg.barrier s x y)
    simp only [Op.apply, Op.isScan, Op.allocWeight]
    simp; omega
  | erase x z =>
    have := markMeasure_le_of_shadeLe (shadeLe_erase cfg.barrier s x z)
    simp only [Op.apply, Op.isScan, Op.allocWeight]
    simp; omega
  | load y =>
    have := markMeasure_le_of_shadeLe (shadeLe_load cfg.shadeLoads s y)
    simp only [Op.apply, Op.isScan, Op.allocWeight]
    simp; omega
  | drop r =>
    have : markMeasure (drop s r) ≤ markMeasure s :=
      markMeasure_le_of_shadeLe (s' := drop s r) (fun _ => Or.inl rfl)
    simp only [Op.apply, Op.isScan, Op.allocWeight]
    simp; omega
  | alloc a c =>
    have := markMeasure_alloc_le s a c
    simp only [Op.apply, Op.isScan, Op.allocWeight]
    simp; omega

/-! ## Paused mutator -/

/-- Every run consisting of collector scans only has at most `markMeasure s` steps. -/
theorem length_le_markMeasure_of_scansOnly_run {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hrun : Run cfg s ops s') (hscan : ScansOnly ops) :
    ops.length ≤ markMeasure s := by
  induction hrun with
  | nil => exact Nat.zero_le _
  | @cons s _ op _ hen _ ih =>
    obtain ⟨g, rfl⟩ := Op.eq_scan_of_isScan (hscan _ (List.mem_cons_self ..))
    have h1 := markMeasure_scan_lt (s := s) hen
    have h2 := ih (fun op h => hscan op (List.mem_cons_of_mem _ h))
    simp only [List.length_cons, Op.apply] at h2 ⊢
    omega

/-- **Paused-mutator termination bound.** Every run consisting of collector scans only has at
most `markMeasure s` steps and at most `2·n` steps. -/
theorem length_le_markMeasure_and_le_two_mul_of_scansOnly_run {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hrun : Run cfg s ops s') (hscan : ScansOnly ops) :
    ops.length ≤ markMeasure s ∧ ops.length ≤ 2 * n :=
  ⟨length_le_markMeasure_of_scansOnly_run hrun hscan,
    Nat.le_trans (length_le_markMeasure_of_scansOnly_run hrun hscan) (markMeasure_le_two_mul s)⟩

/-- **Paused-mutator termination.** From every state some scans-only run reaches a state with
no grey object. -/
theorem exists_scansOnly_run_to_noGrey (cfg : Config) (s : St n) :
    ∃ ops s', Run cfg s ops s' ∧ ScansOnly ops ∧ NoGrey s' := by
  suffices h : ∀ m (s : St n), markMeasure s ≤ m →
      ∃ ops s', Run cfg s ops s' ∧ ScansOnly ops ∧ NoGrey s' from h _ s (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro s hm
    refine ⟨[], s, Run.nil s, fun _ h => absurd h List.not_mem_nil, ?_⟩
    intro g hg
    have := markMeasure_scan_lt (s := s) hg
    omega
  | succ m ih =>
    intro s hm
    by_cases hng : NoGrey s
    · exact ⟨[], s, Run.nil s, fun _ h => absurd h List.not_mem_nil, hng⟩
    · have : ∃ g, s.color g = .grey := by
        apply Classical.byContradiction
        intro hne
        exact hng (fun g hg => hne ⟨g, hg⟩)
      obtain ⟨g, hg⟩ := this
      have hlt := markMeasure_scan_lt (s := s) hg
      obtain ⟨ops, s', hrun, hscan, hng'⟩ := ih (scan s g) (by omega)
      refine ⟨.scan g :: ops, s', Run.cons hg hrun, ?_, hng'⟩
      intro op h
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact hscan op h

/-! ## Active mutator -/

/-- **Collector work is bounded by the initial measure plus allocation weight.** In every run
(any barrier, any configuration), the number of scans plus the final measure is at most the
initial measure plus the summed weights of the allocation colors. -/
theorem scanCount_add_markMeasure_le {cfg : Config} {s s' : St n} {ops : List (Op n)}
    (hrun : Run cfg s ops s') :
    ops.countP Op.isScan + markMeasure s' ≤ markMeasure s + (ops.map Op.allocWeight).sum := by
  induction hrun with
  | nil => simp
  | @cons s _ op _ hen _ ih =>
    have h1 := markMeasure_step hen
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    split at h1 <;> simp_all <;> omega

/-! ### Allocation of white cells only -/

/-- Per-step accounting when an allocation takes a cell that is white in the current state:
no step increases the measure and a scan pays one unit. -/
theorem markMeasure_step_le_of_whiteTarget {cfg : Config} {s : St n} {op : Op n}
    (hen : op.Enabled cfg s) (hw : ∀ a c, op = .alloc a c → s.color a = .white) :
    markMeasure (op.apply cfg s) + (if op.isScan then 1 else 0) ≤ markMeasure s := by
  cases op with
  | alloc a c =>
    have := markMeasure_alloc_le_of_white (hw a c rfl) c
    simp only [Op.apply, Op.isScan]
    simp; omega
  | _ =>
    have := markMeasure_step (cfg := cfg) (s := s) hen
    simp only [Op.allocWeight] at this
    simpa using this

/-- `AllocTargetsWhite cfg s ops`: along the execution of `ops` from `s`, every allocation takes
a cell that is white in the state where it happens (a cell not yet reached in this marking
cycle), rather than re-coloring a grey or black cell. -/
def AllocTargetsWhite (cfg : Config) : St n → List (Op n) → Prop
  | _, [] => True
  | s, op :: ops =>
    (∀ a c, op = .alloc a c → s.color a = .white) ∧ AllocTargetsWhite cfg (op.apply cfg s) ops

/-- **Work bound without re-coloring allocation.** In every run whose allocations take white
cells only, the number of scans plus the final measure is at most the initial measure, for
every allocation color. -/
theorem scanCount_add_markMeasure_le_of_allocTargetsWhite {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hrun : Run cfg s ops s') (hw : AllocTargetsWhite cfg s ops) :
    ops.countP Op.isScan + markMeasure s' ≤ markMeasure s := by
  induction hrun with
  | nil => simp
  | @cons s _ op _ hen _ ih =>
    have h1 := markMeasure_step_le_of_whiteTarget hen hw.1
    have h2 := ih hw.2
    rw [List.countP_cons]
    cases hsc : op.isScan <;> simp [hsc] at h1 ⊢ <;> omega

/-! ### Infinite executions -/

/-- An infinite execution: every step is enabled and determines the next state. -/
def InfRun (cfg : Config) (ops : Nat → Op n) (st : Nat → St n) : Prop :=
  ∀ i, (ops i).Enabled cfg (st i) ∧ st (i + 1) = (ops i).apply cfg (st i)

/-- Weak fairness of the collector: if from some point on a grey object always exists (so a
scan is always enabled), then scans occur infinitely often. -/
def CollectorFair (ops : Nat → Op n) (st : Nat → St n) : Prop :=
  ∀ M, (∀ i, M ≤ i → ¬ NoGrey (st i)) → ∀ N, ∃ i, N ≤ i ∧ (ops i).isScan = true

/-- From some point on, every allocation is black (allocation weight zero). -/
def EventuallyOnlyBlackAllocs (ops : Nat → Op n) : Prop :=
  ∃ N, ∀ i, N ≤ i → (ops i).allocWeight = 0

/-- Every allocation of the infinite execution takes a cell that is white in the state where it
happens. -/
def WhiteTargetAllocs (ops : Nat → Op n) (st : Nat → St n) : Prop :=
  ∀ i a c, ops i = .alloc a c → (st i).color a = .white

/-- A non-increasing sequence of natural numbers is eventually constant. -/
theorem nat_seq_eventually_const (f : Nat → Nat) (N : Nat)
    (hmono : ∀ i, N ≤ i → f (i + 1) ≤ f i) :
    ∃ K, N ≤ K ∧ ∀ i, K ≤ i → f i = f K := by
  have hle : ∀ K₀, N ≤ K₀ → ∀ d, f (K₀ + d) ≤ f K₀ := by
    intro K₀ hK₀ d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      have := hmono (K₀ + d) (by omega)
      rw [← Nat.add_assoc]
      omega
  suffices h : ∀ v K₀, N ≤ K₀ → f K₀ ≤ v → ∃ K, K₀ ≤ K ∧ ∀ i, K ≤ i → f i = f K by
    obtain ⟨K, hNK, hK⟩ := h (f N) N (Nat.le_refl N) (Nat.le_refl _)
    exact ⟨K, hNK, hK⟩
  intro v
  induction v with
  | zero =>
    intro K₀ hNK₀ hf0
    refine ⟨K₀, Nat.le_refl _, ?_⟩
    intro i hi
    have := hle K₀ hNK₀ (i - K₀)
    rw [Nat.add_sub_cancel' hi] at this
    omega
  | succ v ih =>
    intro K₀ hNK₀ hfv
    by_cases hconst : ∀ i, K₀ ≤ i → f i = f K₀
    · exact ⟨K₀, Nat.le_refl _, hconst⟩
    · have hex : ∃ K₁, K₀ ≤ K₁ ∧ f K₁ < f K₀ := by
        apply Classical.byContradiction
        intro hno
        apply hconst
        intro i hi
        have h1 := hle K₀ hNK₀ (i - K₀)
        rw [Nat.add_sub_cancel' hi] at h1
        by_cases hlt : f i < f K₀
        · exact absurd ⟨i, hi, hlt⟩ hno
        · omega
      obtain ⟨K₁, hK₀₁, hlt⟩ := hex
      obtain ⟨K, hK₁K, hK⟩ := ih K₁ (by omega) (by omega)
      exact ⟨K, by omega, hK⟩

/-- If a measure-preserving shading step creates a grey object from a state with none, the
measure strictly drops. -/
theorem markMeasure_lt_of_shadeLe_of_noGrey_of_grey {s s' : St n}
    (hsh : ShadeLe s s') (hng : NoGrey s) {g : Fin n} (hg : s'.color g = .grey) :
    markMeasure s' < markMeasure s := by
  refine sum_map_lt (List.finRange n)
    (fun x => weight (s'.color x)) (fun x => weight (s.color x)) ?_ (List.mem_finRange g) ?_
  · intro x _
    rcases hsh x with heq | ⟨hw, hgr⟩
    · rw [heq]; exact Nat.le_refl _
    · rw [hw, hgr]; decide
  · rcases hsh g with heq | ⟨hw, _⟩
    · exfalso; rw [heq] at hg; exact hng g hg
    · rw [hw, hg]; decide

/-- An enabled step from a state with no grey object that leaves the measure unchanged is not a
scan and creates no grey object. -/
theorem noGrey_and_not_scan_of_step_of_markMeasure_eq {cfg : Config} {s : St n} {op : Op n}
    (hen : op.Enabled cfg s) (hng : NoGrey s)
    (heq : markMeasure (op.apply cfg s) = markMeasure s) :
    NoGrey (op.apply cfg s) ∧ op.isScan = false := by
  cases op with
  | scan g => exact absurd hen (hng g)
  | store x y =>
    refine ⟨fun g hg => ?_, rfl⟩
    have := markMeasure_lt_of_shadeLe_of_noGrey_of_grey (shadeLe_store cfg.barrier s x y) hng hg
    simp only [Op.apply] at heq
    omega
  | erase x z =>
    refine ⟨fun g hg => ?_, rfl⟩
    have := markMeasure_lt_of_shadeLe_of_noGrey_of_grey (shadeLe_erase cfg.barrier s x z) hng hg
    simp only [Op.apply] at heq
    omega
  | load y =>
    refine ⟨fun g hg => ?_, rfl⟩
    have := markMeasure_lt_of_shadeLe_of_noGrey_of_grey (shadeLe_load cfg.shadeLoads s y) hng hg
    simp only [Op.apply] at heq
    omega
  | drop r => exact ⟨hng, rfl⟩
  | alloc a c =>
    refine ⟨fun g hg => ?_, rfl⟩
    simp only [Op.apply] at heq hg
    by_cases hga : g = a
    · subst hga
      simp only [Tricolor.alloc, ite_true] at hg
      subst hg
      cases hca : s.color g with
      | white =>
        have := markMeasure_alloc_lt_of_white_of_ne_white hca (c := .grey) (by decide)
        omega
      | grey => exact hng g hca
      | black =>
        have := markMeasure_lt_alloc_grey_of_black hca
        omega
    · simp only [Tricolor.alloc, hga, ite_false] at hg
      exact hng g hg

/-- **Marking stops for good once the measure can no longer grow.** In an infinite execution in
which, from some point on, no step increases the measure, a weakly fair collector reaches a
state with no grey object, after which no object is ever grey again and no scan occurs. -/
theorem eventually_always_noGrey_of_collectorFair_of_eventually_markMeasure_antitone
    {cfg : Config} {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st)
    (hmono : ∃ N, ∀ i, N ≤ i → markMeasure (st (i + 1)) ≤ markMeasure (st i)) :
    ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false := by
  obtain ⟨N, hN⟩ := hmono
  obtain ⟨K₀, _, hconst⟩ := nat_seq_eventually_const (fun i => markMeasure (st i)) N hN
  have hc : ∀ i, K₀ ≤ i → markMeasure (st i) = markMeasure (st K₀) := hconst
  have heqAt : ∀ i, K₀ ≤ i → markMeasure ((ops i).apply cfg (st i)) = markMeasure (st i) := by
    intro i hi
    rw [← (hrun i).2, hc (i + 1) (by omega), hc i hi]
  have hex : ∃ K, K₀ ≤ K ∧ NoGrey (st K) := by
    apply Classical.byContradiction
    intro hno
    have hgrey : ∀ i, K₀ ≤ i → ¬ NoGrey (st i) := fun i hi h => hno ⟨i, hi, h⟩
    obtain ⟨i, hi, hsc⟩ := hfair K₀ hgrey K₀
    obtain ⟨g, hg⟩ := Op.eq_scan_of_isScan hsc
    have hen := (hrun i).1
    rw [hg] at hen
    have hlt := markMeasure_scan_lt (s := st i) hen
    have h1 := heqAt i hi
    rw [hg] at h1
    simp only [Op.apply] at h1
    omega
  obtain ⟨K, hK₀K, hngK⟩ := hex
  have hng : ∀ d, NoGrey (st (K + d)) := by
    intro d
    induction d with
    | zero => simpa using hngK
    | succ d ih =>
      have h := (noGrey_and_not_scan_of_step_of_markMeasure_eq (hrun (K + d)).1 ih
        (heqAt (K + d) (by omega))).1
      rw [← (hrun (K + d)).2] at h
      rwa [← Nat.add_assoc]
  refine ⟨K, fun i hi => ?_⟩
  have hi' : NoGrey (st i) := by
    have := hng (i - K)
    rwa [Nat.add_sub_cancel' hi] at this
  exact ⟨hi', (noGrey_and_not_scan_of_step_of_markMeasure_eq (hrun i).1 hi'
    (heqAt i (by omega))).2⟩

/-- **Active-mutator termination (fair collector, eventually black-only allocation).** In an
infinite execution where the collector is weakly fair and, from some point on, every allocation
is black, from some point on no object is grey and no scan occurs. -/
theorem eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (halloc : EventuallyOnlyBlackAllocs ops) :
    ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false := by
  obtain ⟨N, hN⟩ := halloc
  refine eventually_always_noGrey_of_collectorFair_of_eventually_markMeasure_antitone hrun hfair
    ⟨N, fun i hi => ?_⟩
  have h := markMeasure_step (hrun i).1
  rw [← (hrun i).2, hN i hi] at h
  split at h <;> omega

/-- Corollary: states with no grey object occur infinitely often. -/
theorem infinitely_often_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (halloc : EventuallyOnlyBlackAllocs ops) :
    ∀ M, ∃ i, M ≤ i ∧ NoGrey (st i) := by
  obtain ⟨K, hK⟩ :=
    eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs hrun hfair halloc
  intro M
  exact ⟨Nat.max M K, Nat.le_max_left M K, (hK _ (Nat.le_max_right M K)).1⟩

/-- **Active-mutator termination (fair collector, allocation of white cells only).** In an
infinite execution where the collector is weakly fair and every allocation takes a cell that is
white in the current state (any allocation color), from some point on no object is grey and no
scan occurs. -/
theorem eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (hw : WhiteTargetAllocs ops st) :
    ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false := by
  refine eventually_always_noGrey_of_collectorFair_of_eventually_markMeasure_antitone hrun hfair
    ⟨0, fun i _ => ?_⟩
  have h := markMeasure_step_le_of_whiteTarget (hrun i).1 (fun a c h => hw i a c h)
  rw [← (hrun i).2] at h
  split at h <;> omega

/-- The prefix `ops i, …, ops (i + k - 1)` of an infinite execution. -/
def opsFrom (ops : Nat → Op n) (i : Nat) : Nat → List (Op n)
  | 0 => []
  | k + 1 => ops i :: opsFrom ops (i + 1) k

theorem InfRun.run_opsFrom {cfg : Config} {ops : Nat → Op n} {st : Nat → St n}
    (h : InfRun cfg ops st) (k : Nat) : ∀ i, Run cfg (st i) (opsFrom ops i k) (st (i + k)) := by
  induction k with
  | zero => intro i; simpa [opsFrom] using Run.nil (cfg := cfg) (st i)
  | succ k ih =>
    intro i
    have h' := ih (i + 1)
    rw [show i + 1 + k = i + (k + 1) by omega, (h i).2] at h'
    exact Run.cons (h i).1 h'

theorem not_eventually_noGrey_of_forall_not_noGrey {ops : Nat → Op n} {st : Nat → St n}
    (h : ∀ i, ¬ NoGrey (st i)) :
    ¬ ∃ K, ∀ i, K ≤ i → NoGrey (st i) ∧ (ops i).isScan = false :=
  fun ⟨K, hK⟩ => h K (hK K (Nat.le_refl K)).1

/-! ## Counterexamples and non-vacuity for termination -/

theorem St.ext_of_forall {s t : St n} (he : ∀ u v, s.edge u v = t.edge u v)
    (hr : ∀ r, s.root r = t.root r) (hc : ∀ x, s.color x = t.color x) : s = t :=
  St.ext' (funext fun u => funext fun v => he u v) (funext hr) (funext hc)

/-- Grey allocation allowed. -/
def cfgGreyAlloc : Config := { barrier := .dijkstra, shadeLoads := true, allocOk := fun _ => true }

/-- A six-step cycle over two garbage objects that are repeatedly allocated grey, dropped from
the roots and scanned. -/
def cycSt : Nat → St 2
  | 0 => mk 2 [] [] [.grey, .black]
  | 1 => mk 2 [] [1] [.grey, .grey]
  | 2 => mk 2 [] [] [.grey, .grey]
  | 3 => mk 2 [] [] [.black, .grey]
  | 4 => mk 2 [] [0] [.grey, .grey]
  | _ => mk 2 [] [] [.grey, .grey]

def cycOp : Nat → Op 2
  | 0 => .alloc 1 .grey
  | 1 => .drop 1
  | 2 => .scan 0
  | 3 => .alloc 0 .grey
  | 4 => .drop 0
  | _ => .scan 1

def cycStates (i : Nat) : St 2 := cycSt (i % 6)
def cycOps (i : Nat) : Op 2 := cycOp (i % 6)

theorem cyc_step : ∀ j, j < 6 →
    (cycOp j).Enabled cfgGreyAlloc (cycSt j) ∧ cycSt ((j + 1) % 6) = (cycOp j).apply cfgGreyAlloc (cycSt j)
  | 0, _ => ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  | 1, _ => ⟨trivial, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  | 2, _ => ⟨rfl, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  | 3, _ => ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  | 4, _ => ⟨trivial, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  | 5, _ => ⟨rfl, St.ext_of_forall (by decide) (by decide) (by decide)⟩

theorem cyc_grey : ∀ j, j < 6 → ¬ NoGrey (cycSt j)
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide

/-- **Without the allocation assumption, collector fairness is not enough.** The six-step
cycle is an infinite execution in which allocation re-colors the black objects `1` and `0` grey
(they are isolated garbage cells, not swept), the collector scans every third step, yet a grey
object exists in every state. -/
theorem greyAllocCycle_collectorFair_never_noGrey :
    InfRun cfgGreyAlloc cycOps cycStates ∧ CollectorFair cycOps cycStates ∧
      ¬ EventuallyOnlyBlackAllocs cycOps ∧ ¬ WhiteTargetAllocs cycOps cycStates ∧
      (∀ i, ¬ NoGrey (cycStates i)) ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (cycStates i) ∧ (cycOps i).isScan = false := by
  have hgrey : ∀ i, ¬ NoGrey (cycStates i) := fun i => cyc_grey (i % 6) (Nat.mod_lt _ (by decide))
  refine ⟨?_, ?_, ?_, ?_, hgrey, not_eventually_noGrey_of_forall_not_noGrey hgrey⟩
  · intro i
    have h := cyc_step (i % 6) (Nat.mod_lt _ (by decide))
    have : (i + 1) % 6 = (i % 6 + 1) % 6 := by omega
    simp only [cycStates, cycOps, this]
    exact h
  · intro M _ N
    refine ⟨6 * N + 2, by omega, ?_⟩
    have : (6 * N + 2) % 6 = 2 := by omega
    simp only [cycOps, this]
    rfl
  · intro ⟨N, hN⟩
    have h := hN (6 * N) (by omega)
    have : (6 * N) % 6 = 0 := by omega
    simp only [cycOps, this] at h
    cases h
  · intro h
    have := h 0 1 .grey rfl
    exact absurd this (by decide)

/-- With re-coloring grey allocation the number of scans in a run exceeds `2·n`: the first 18
steps of the cycle (on `n = 2` objects) contain 6 scans. -/
theorem greyAllocCycle_scans_exceed_two_mul_n :
    Run cfgGreyAlloc (cycStates 0) (opsFrom cycOps 0 18) (cycStates 18) ∧
      2 * 2 < (opsFrom cycOps 0 18).countP Op.isScan := by
  have h := greyAllocCycle_collectorFair_never_noGrey.1.run_opsFrom 18 0
  rw [Nat.zero_add] at h
  exact ⟨h, by decide⟩

/-- The allocation term of the work bound cannot be dropped (a 2-object heap and a 6-step run):
over one cycle of the grey-allocation execution, the number of scans plus the final measure
exceeds the initial measure. -/
theorem allocWeight_needed_greyAllocCycle :
    Run cfgGreyAlloc (cycStates 0) (opsFrom cycOps 0 6) (cycStates 6) ∧
      markMeasure (cycStates 0) <
        (opsFrom cycOps 0 6).countP Op.isScan + markMeasure (cycStates 6) := by
  have h := greyAllocCycle_collectorFair_never_noGrey.1.run_opsFrom 6 0
  rw [Nat.zero_add] at h
  exact ⟨h, by decide⟩

/-- A single grey object that the mutator never lets the collector scan. -/
def sOneGrey : St 1 := mk 1 [] [] [.grey]

def starveOps : Nat → Op 1 := fun _ => .drop 0
def starveStates : Nat → St 1 := fun _ => sOneGrey

/-- **Collector fairness cannot be dropped** (an infinite execution over a 1-object heap). An
infinite execution of root drops only, with no allocation, keeps a grey object forever. -/
theorem starvedCollector_never_noGrey :
    InfRun cfgD starveOps starveStates ∧ EventuallyOnlyBlackAllocs starveOps ∧
      WhiteTargetAllocs starveOps starveStates ∧
      ¬ CollectorFair starveOps starveStates ∧ (∀ i, ¬ NoGrey (starveStates i)) ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (starveStates i) ∧ (starveOps i).isScan = false := by
  have hgrey : ∀ i, ¬ NoGrey (starveStates i) := fun _ => (by decide : ¬ NoGrey sOneGrey)
  refine ⟨?_, ⟨0, fun _ _ => rfl⟩, (fun _ _ _ h => by simp [starveOps] at h), ?_, hgrey,
    not_eventually_noGrey_of_forall_not_noGrey hgrey⟩
  · intro _
    show (Op.drop 0 : Op 1).Enabled cfgD sOneGrey ∧
      sOneGrey = (Op.drop 0 : Op 1).apply cfgD sOneGrey
    exact ⟨trivial, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  · intro h
    obtain ⟨_, _, hi⟩ := h 0 (fun _ _ => (by decide : ¬ NoGrey sOneGrey)) 0
    cases hi

/-! ### Enabledness of scans cannot be dropped from the termination results (1- and 2-object
states) -/

/-- One black object. -/
def sOneBlack : St 1 := mk 1 [] [] [.black]

/-- Enabled scans cannot be dropped from the paused-mutator bound (a 1-object state): a scan of
a black object is not enabled, and
the one-step scan list exceeds the measure `0`. -/
theorem length_bound_fails_without_enabled_scans :
    ScansOnly [(Op.scan 0 : Op 1)] ∧
      ¬ Run cfgD sOneBlack [.scan 0] (runOps cfgD [.scan 0] sOneBlack) ∧
      ¬ ([(Op.scan 0 : Op 1)].length ≤ markMeasure sOneBlack ∧
        [(Op.scan 0 : Op 1)].length ≤ 2 * 1) := by
  refine ⟨by simp [ScansOnly, Op.isScan], ?_, fun h => absurd h.1 (by decide)⟩
  intro h
  cases h with
  | cons hen _ => exact absurd hen (by decide : ¬ sOneBlack.color 0 = .grey)

/-- Enabled scans cannot be dropped from the work bound (a 1-object state and one scan). -/
theorem scanCount_bound_fails_without_enabled_scans :
    ¬ Run cfgD sOneBlack [.scan 0] (runOps cfgD [.scan 0] sOneBlack) ∧
      ¬ ([(Op.scan 0 : Op 1)].countP Op.isScan + markMeasure (runOps cfgD [.scan 0] sOneBlack) ≤
        markMeasure sOneBlack + ([(Op.scan 0 : Op 1)].map Op.allocWeight).sum) :=
  ⟨length_bound_fails_without_enabled_scans.2.1, by decide⟩

/-- Grey `0` and black `1`. -/
def sGreyAndBlack : St 2 := mk 2 [] [] [.grey, .black]
def badScanOps : Nat → Op 2 := fun _ => .scan 1
def badScanStates : Nat → St 2 := fun _ => sGreyAndBlack

/-- Enabled scans cannot be dropped from the termination results (an infinite execution over a
2-object heap): scanning the black object `1` forever satisfies
the state equations, collector fairness and both allocation assumptions, yet the grey object
`0` stays grey. -/
theorem unenabledScans_collectorFair_never_noGrey :
    (∀ i, badScanStates (i + 1) = (badScanOps i).apply cfgD (badScanStates i)) ∧
      ¬ InfRun cfgD badScanOps badScanStates ∧
      CollectorFair badScanOps badScanStates ∧ EventuallyOnlyBlackAllocs badScanOps ∧
      WhiteTargetAllocs badScanOps badScanStates ∧
      ¬ ∃ K, ∀ i, K ≤ i → NoGrey (badScanStates i) ∧ (badScanOps i).isScan = false := by
  have hgrey : ∀ i, ¬ NoGrey (badScanStates i) := fun _ => (by decide : ¬ NoGrey sGreyAndBlack)
  refine ⟨?_, ?_, ?_, ⟨0, fun _ _ => rfl⟩, (fun _ _ _ h => by simp [badScanOps] at h),
    not_eventually_noGrey_of_forall_not_noGrey hgrey⟩
  · intro _
    show sGreyAndBlack = (Op.scan 1 : Op 2).apply cfgD sGreyAndBlack
    exact St.ext_of_forall (by decide) (by decide) (by decide)
  · intro h
    exact absurd (h 0).1 (by decide : ¬ sGreyAndBlack.color 1 = .grey)
  · intro _ _ N
    exact ⟨N, Nat.le_refl N, rfl⟩

/-! ### Non-vacuity -/

/-- Scan a grey root, then allocate the free cell `1` black and drop it, forever (black
allocation occurs infinitely often). -/
def activeStates : Nat → St 2
  | 0 => mk 2 [] [0] [.grey, .white]
  | 1 => mk 2 [] [0] [.black, .white]
  | k + 2 => if k % 2 = 0 then mk 2 [] [0, 1] [.black, .black] else mk 2 [] [0] [.black, .black]

def activeOps : Nat → Op 2
  | 0 => .scan 0
  | k + 1 => if k % 2 = 0 then .alloc 1 .black else .drop 1

theorem eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs_nonvacuous :
    InfRun cfgD activeOps activeStates ∧ CollectorFair activeOps activeStates ∧
      EventuallyOnlyBlackAllocs activeOps ∧
      (∀ N, ∃ i, N ≤ i ∧ activeOps i = .alloc 1 .black) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | zero => exact ⟨rfl, St.ext_of_forall (by decide) (by decide) (by decide)⟩
    | succ k =>
      cases k with
      | zero =>
        show (Op.alloc 1 .black : Op 2).Enabled cfgD (activeStates 1) ∧
          activeStates 2 = (Op.alloc 1 .black : Op 2).apply cfgD (activeStates 1)
        exact ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
      | succ m =>
        by_cases hm : m % 2 = 0
        · have hm1 : (m + 1) % 2 = 1 := by omega
          simp only [activeOps, activeStates, hm, hm1]
          show (Op.drop 1 : Op 2).Enabled cfgD (mk 2 [] [0, 1] [.black, .black]) ∧
            mk 2 [] [0] [.black, .black] =
              (Op.drop 1 : Op 2).apply cfgD (mk 2 [] [0, 1] [.black, .black])
          exact ⟨trivial, St.ext_of_forall (by decide) (by decide) (by decide)⟩
        · have hm1 : (m + 1) % 2 = 0 := by omega
          simp only [activeOps, activeStates, hm, hm1]
          show (Op.alloc 1 .black : Op 2).Enabled cfgD (mk 2 [] [0] [.black, .black]) ∧
            mk 2 [] [0, 1] [.black, .black] =
              (Op.alloc 1 .black : Op 2).apply cfgD (mk 2 [] [0] [.black, .black])
          exact ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  · intro M hM
    exfalso
    have hng : NoGrey (activeStates (M + 1)) := by
      cases M with
      | zero => decide
      | succ m =>
        simp only [activeStates]
        split <;> decide
    exact hM (M + 1) (by omega) hng
  · refine ⟨0, fun i _ => ?_⟩
    cases i with
    | zero => rfl
    | succ k =>
      simp only [activeOps]
      split <;> rfl
  · intro N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have : (2 * N) % 2 = 0 := by omega
    simp [activeOps, this]

/-- Allocate the white free cell `1` white into the roots and drop it, forever: every allocation
takes a white cell, white allocation occurs infinitely often (so allocation is never eventually
black-only), and the collector is fair. -/
def wStates (i : Nat) : St 2 :=
  if i % 2 = 0 then mk 2 [] [0] [.black, .white] else mk 2 [] [0, 1] [.black, .white]
def wOps (i : Nat) : Op 2 := if i % 2 = 0 then .alloc 1 .white else .drop 1

theorem eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous :
    InfRun cfgGreyAlloc wOps wStates ∧ CollectorFair wOps wStates ∧
      WhiteTargetAllocs wOps wStates ∧ ¬ EventuallyOnlyBlackAllocs wOps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h1 : (i + 1) % 2 = 1 := by omega
      simp only [wOps, wStates, h, h1]
      exact ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
    · have h1 : (i + 1) % 2 = 0 := by omega
      simp only [wOps, wStates, h, h1]
      exact ⟨trivial, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  · intro M hM
    exfalso
    apply hM M (Nat.le_refl M)
    unfold wStates
    split <;> decide
  · intro i a c h
    unfold wOps at h
    split at h
    · next hi =>
      cases h
      simp only [wStates, hi]
      rfl
    · cases h
  · intro ⟨N, hN⟩
    have h := hN (2 * N) (by omega)
    have : (2 * N) % 2 = 0 := by omega
    simp [wOps, this, Op.allocWeight, weight] at h

theorem exists_scansOnly_run_to_noGrey_nonvacuous : ¬ NoGrey sGreyWhite := by decide

theorem markMeasure_scan_lt_nonvacuous : sGreyWhite.color 0 = .grey := rfl

theorem length_le_markMeasure_and_le_two_mul_of_scansOnly_run_nonvacuous :
    Run cfgD sGreyWhite [.scan 0, .scan 1] (scan (scan sGreyWhite 0) 1) ∧
      ScansOnly [(Op.scan 0 : Op 2), .scan 1] :=
  ⟨Run.cons rfl (Run.cons rfl (Run.nil _)), by simp [ScansOnly, Op.isScan]⟩

/-- Non-vacuity of the work bound on a run in which allocation re-colors black cells grey, so
that the allocation term cannot be dropped from the bound for that 2-object run
(`allocWeight_needed_greyAllocCycle`). -/
theorem scanCount_add_markMeasure_le_nonvacuous :
    Run cfgGreyAlloc (cycStates 0) (opsFrom cycOps 0 6) (cycStates 6) :=
  allocWeight_needed_greyAllocCycle.1

/-! ### Scope of the termination results -/

/-- In every execution satisfying the hypotheses of the eventually-black-allocation termination
theorem, the antecedent of `CollectorFair` is false from every point on: grey objects do not
persist from any point onward. -/
theorem collectorFair_antecedent_false_of_eventuallyOnlyBlackAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (halloc : EventuallyOnlyBlackAllocs ops) :
    ∀ M, ¬ (∀ i, M ≤ i → ¬ NoGrey (st i)) := by
  obtain ⟨K, hK⟩ :=
    eventually_always_noGrey_of_collectorFair_of_eventuallyOnlyBlackAllocs hrun hfair halloc
  intro M hM
  exact hM (Nat.max M K) (Nat.le_max_left M K) (hK _ (Nat.le_max_right M K)).1

/-- In every execution satisfying the hypotheses of the white-target-allocation termination
theorem, the antecedent of `CollectorFair` is false from every point on. -/
theorem collectorFair_antecedent_false_of_whiteTargetAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hfair : CollectorFair ops st) (hw : WhiteTargetAllocs ops st) :
    ∀ M, ¬ (∀ i, M ≤ i → ¬ NoGrey (st i)) := by
  obtain ⟨K, hK⟩ := eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs hrun hfair hw
  intro M hM
  exact hM (Nat.max M K) (Nat.le_max_left M K) (hK _ (Nat.le_max_right M K)).1

/-- In every infinite execution in which every allocation takes a white cell (no fairness
assumption), only finitely many allocations are grey or black: from some point on every
allocation is white. -/
theorem eventually_only_white_alloc_of_whiteTargetAllocs {cfg : Config}
    {ops : Nat → Op n} {st : Nat → St n} (hrun : InfRun cfg ops st)
    (hw : WhiteTargetAllocs ops st) :
    ∃ K, ∀ i, K ≤ i → ∀ a c, ops i = .alloc a c → c = .white := by
  have hmono : ∀ i, 0 ≤ i → markMeasure (st (i + 1)) ≤ markMeasure (st i) := by
    intro i _
    have h := markMeasure_step_le_of_whiteTarget (hrun i).1 (fun a c h => hw i a c h)
    rw [← (hrun i).2] at h
    split at h <;> omega
  obtain ⟨K, _, hconst⟩ := nat_seq_eventually_const (fun i => markMeasure (st i)) 0 hmono
  refine ⟨K, fun i hi a c hop => ?_⟩
  by_cases hc : c = .white
  · exact hc
  · exfalso
    have hlt := markMeasure_alloc_lt_of_white_of_ne_white (hw i a c hop) hc
    have hst : st (i + 1) = alloc (st i) a c := by
      have h2 := (hrun i).2
      rw [hop] at h2
      exact h2
    have heq : markMeasure (st (i + 1)) = markMeasure (st i) := by
      rw [hconst (i + 1) (by omega), hconst i hi]
    rw [hst] at heq
    omega

/-- The non-vacuity execution of the eventually-black-allocation theorem re-colors the black
cell `1` black at step `3`, so it is not an execution in which every allocation takes a white
cell. -/
theorem activeOps_not_whiteTargetAllocs : ¬ WhiteTargetAllocs activeOps activeStates := by
  intro hw
  exact absurd (hw 3 1 .black rfl) (by decide)

/-- Start with the grey root `0` and the free cells `1`, `2`; allocate the white cell `1` grey,
scan `0` and `1`, then allocate the white cell `2` white and drop it, forever. -/
def wtStates : Nat → St 3
  | 0 => mk 3 [] [0] [.grey, .white, .white]
  | 1 => mk 3 [] [0, 1] [.grey, .grey, .white]
  | 2 => mk 3 [] [0, 1] [.black, .grey, .white]
  | k + 3 =>
    if k % 2 = 0 then mk 3 [] [0, 1] [.black, .black, .white]
    else mk 3 [] [0, 1, 2] [.black, .black, .white]

def wtOps : Nat → Op 3
  | 0 => .alloc 1 .grey
  | 1 => .scan 0
  | 2 => .scan 1
  | k + 3 => if k % 2 = 0 then .alloc 2 .white else .drop 2

/-- Non-vacuity of the white-target-allocation theorem on an execution with collector work: all
hypotheses hold, the initial state has a grey object, the first allocation is grey (allocation
adds marking work), two scans occur, and white allocation occurs infinitely often (so
allocation is never eventually black-only). -/
theorem eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous_with_marking_work :
    InfRun cfgGreyAlloc wtOps wtStates ∧ CollectorFair wtOps wtStates ∧
      WhiteTargetAllocs wtOps wtStates ∧ ¬ EventuallyOnlyBlackAllocs wtOps ∧
      ¬ NoGrey (wtStates 0) ∧ wtOps 0 = .alloc 1 .grey ∧
      (wtOps 1).isScan = true ∧ (wtOps 2).isScan = true ∧
      (∀ N, ∃ i, N ≤ i ∧ wtOps i = .alloc 2 .white) := by
  refine ⟨?_, ?_, ?_, ?_, by decide, rfl, rfl, rfl, ?_⟩
  · intro i
    cases i with
    | zero => exact ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
    | succ i1 =>
      cases i1 with
      | zero => exact ⟨rfl, St.ext_of_forall (by decide) (by decide) (by decide)⟩
      | succ i2 =>
        cases i2 with
        | zero => exact ⟨rfl, St.ext_of_forall (by decide) (by decide) (by decide)⟩
        | succ k =>
          rcases Nat.mod_two_eq_zero_or_one k with hk | hk
          · have hk1 : (k + 1) % 2 = 1 := by omega
            simp only [wtOps, wtStates, hk, hk1]
            exact ⟨⟨rfl, rfl, by decide⟩, St.ext_of_forall (by decide) (by decide) (by decide)⟩
          · have hk1 : (k + 1) % 2 = 0 := by omega
            simp only [wtOps, wtStates, hk, hk1]
            exact ⟨trivial, St.ext_of_forall (by decide) (by decide) (by decide)⟩
  · intro M hM
    exfalso
    have hng : NoGrey (wtStates (M + 3)) := by
      simp only [wtStates]
      split <;> decide
    exact hM (M + 3) (by omega) hng
  · intro i a c hop
    cases i with
    | zero => cases hop; rfl
    | succ i1 =>
      cases i1 with
      | zero => cases hop
      | succ i2 =>
        cases i2 with
        | zero => cases hop
        | succ k =>
          simp only [wtOps] at hop
          split at hop
          · next hk =>
            cases hop
            simp only [wtStates, hk]
            rfl
          · cases hop
  · intro ⟨N, hN⟩
    have h2 : (2 * N + 2) % 2 = 0 := by omega
    have hop : wtOps (2 * N + 5) = .alloc 2 .white := by
      show wtOps ((2 * N + 2) + 3) = .alloc 2 .white
      simp [wtOps, h2]
    have h5 := hN (2 * N + 5) (by omega)
    rw [hop] at h5
    cases h5
  · intro N
    refine ⟨2 * N + 3, by omega, ?_⟩
    have h0 : (2 * N) % 2 = 0 := by omega
    show wtOps ((2 * N) + 3) = .alloc 2 .white
    simp [wtOps, h0]

end Toy.Tricolor
