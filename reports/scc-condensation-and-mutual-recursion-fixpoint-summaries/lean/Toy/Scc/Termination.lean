/-
Toy.Scc.Termination
===================

Termination measures for mutual recursion over an SCC decomposition (cards
`lex-iff`, `termination-intra`, `inner-alone`).  Calls are modeled at the level of
configurations `(function, argument state)`, so that recursion inside an SCC can
terminate even though the call graph has cycles.
-/
import Toy.Scc.Decomp

namespace Toy.Scc

/-- A configuration-level call relation: `C (f, x) (g, y)` means that `f` running on
argument state `x` makes a call to `g` with argument state `y`. -/
abbrev Calls (n : Nat) (S : Type) := Fin n × S → Fin n × S → Prop

/-- Every configuration-level call follows an edge of the call graph (the call graph
over-approximates the calls the program can make). -/
def CallsInGraph {n : Nat} {S : Type} (E : Graph n) (C : Calls n S) : Prop :=
  ∀ a b, C a b → E a.1 b.1 = true

/-- Calls inside a block strictly decrease the inner measure. -/
def IntraDecrease {n k : Nat} {S : Type} (comp : Fin n → Fin k) (inner : Fin n → S → Nat)
    (C : Calls n S) : Prop :=
  ∀ a b, C a b → comp a.1 = comp b.1 → inner b.1 b.2 < inner a.1 a.2

/-- Calls across blocks go to a block of strictly smaller rank. -/
def InterRankDecrease {n k : Nat} {S : Type} (rank : Fin k → Nat) (comp : Fin n → Fin k)
    (C : Calls n S) : Prop :=
  ∀ a b, C a b → comp a.1 ≠ comp b.1 → rank (comp b.1) < rank (comp a.1)

/-- Strict lexicographic order on pairs of naturals. -/
def LexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- The lexicographic measure of a configuration `(f, x)`: the rank of the block of `f`,
then the inner measure of `f` at `x`. -/
def lexMeasure {n k : Nat} {S : Type} (rank : Fin k → Nat) (comp : Fin n → Fin k)
    (inner : Fin n → S → Nat) (a : Fin n × S) : Nat × Nat :=
  (rank (comp a.1), inner a.1 a.2)

/-- The lexicographic measure strictly decreases along every call. -/
def LexDecreasing {n k : Nat} {S : Type} (rank : Fin k → Nat) (comp : Fin n → Fin k)
    (inner : Fin n → S → Nat) (C : Calls n S) : Prop :=
  ∀ a b, C a b → LexLt (lexMeasure rank comp inner b) (lexMeasure rank comp inner a)

/-- Every call chain is finite: every configuration is accessible for the converse of
the call relation. -/
def Terminates {n : Nat} {S : Type} (C : Calls n S) : Prop :=
  ∀ a, Acc (fun b a => C a b) a

/-! ## Helpers (fully proved) -/

/-- If every configuration makes some call, nothing terminates. -/
theorem not_acc_of_always_calls {α : Type} {R : α → α → Prop} (h : ∀ x, ∃ y, R y x) :
    ∀ x, ¬ Acc R x := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      obtain ⟨y, hy⟩ := h x
      exact ih y hy

/-! ## Fixtures -/

/-- One call from `0` to `1` (unit state). -/
def cPath : Calls 2 Unit := fun a b => a.1 = 0 ∧ b.1 = 1
/-- `0` and `1` call each other forever (unit state). -/
def cCycle : Calls 2 Unit := fun a b => a.1 ≠ b.1
/-- One function calls itself forever (unit state). -/
def cLoop : Calls 1 Unit := fun _ _ => True
/-- Self-recursion on a counter that decreases by one. -/
def cCount : Calls 1 Nat := fun a b => b.2 + 1 = a.2
/-- One call from `(0, 0)` to `(1, 5)`. -/
def cJump : Calls 2 Nat := fun a b => a = (0, 0) ∧ b = (1, 5)
/-- On `gPathLoop1`: `0` on state `0` calls `1` on any state `y` (unbounded fan-out across
blocks), and `1` on state `y + 1` calls itself on state `y`. -/
def cUnbounded : Calls 2 Nat :=
  fun a b => (a = (0, 0) ∧ b.1 = 1) ∨ (a.1 = 1 ∧ b.1 = 1 ∧ b.2 + 1 = a.2)

theorem not_terminates_cCycle : ¬ Terminates cCycle := fun h =>
  not_acc_of_always_calls (R := fun b a => cCycle a b)
    (fun x => ⟨(if x.1 = 0 then 1 else 0, ()), by
      show x.1 ≠ (if x.1 = 0 then 1 else 0)
      split <;> omega⟩) (0, ()) (h (0, ()))

theorem not_terminates_cLoop : ¬ Terminates cLoop := fun h =>
  not_acc_of_always_calls (R := fun b a => cLoop a b) (fun x => ⟨x, trivial⟩) (0, ())
    (h (0, ()))

theorem terminates_cCount : Terminates cCount := by
  intro ⟨f, x⟩
  induction x generalizing f with
  | zero => exact Acc.intro _ (fun b hb => by simp [cCount] at hb)
  | succ x ih =>
      refine Acc.intro _ (fun ⟨g, y⟩ hb => ?_)
      have : y = x := by simp [cCount] at hb; omega
      subst this; exact ih g

theorem terminates_cJump : Terminates cJump := by
  have h1 : ∀ s : Fin 2 × Nat, s.1 = 1 → Acc (fun b a => cJump a b) s := fun s hs =>
    Acc.intro _ (fun b hb => by
      obtain ⟨h, _⟩ := hb
      rw [h] at hs; exact absurd hs (by decide))
  intro a
  refine Acc.intro _ (fun b hb => h1 b ?_)
  rw [hb.2]

-- `CallsInGraph`, `IntraDecrease`, `InterRankDecrease`, `LexDecreasing`, `Terminates`:
-- positive and negative examples.
example : CallsInGraph gPath cPath := by
  rintro ⟨f, ⟨⟩⟩ ⟨g, ⟨⟩⟩ ⟨hf, hg⟩; simp only at hf hg; subst hf; subst hg; decide
example : ¬ CallsInGraph gEmpty cPath := fun h =>
  absurd (h (0, ()) (1, ()) ⟨rfl, rfl⟩) (by decide)
example : IntraDecrease oneComp (fun _ x => x) cCount := by
  rintro ⟨_, x⟩ ⟨_, y⟩ h _; simp only [cCount] at h ⊢; omega
example : ¬ IntraDecrease oneComp (fun _ _ => 0) cLoop := fun h =>
  absurd (h (0, ()) (0, ()) trivial rfl) (by decide)
example : InterRankDecrease (fun c : Fin 2 => 1 - c.val) idComp cPath := by
  rintro ⟨f, ⟨⟩⟩ ⟨g, ⟨⟩⟩ ⟨hf, hg⟩ _; simp only at hf hg; subst hf; subst hg; decide
example : ¬ InterRankDecrease (fun _ : Fin 2 => 0) idComp cPath := fun h =>
  absurd (h (0, ()) (1, ()) ⟨rfl, rfl⟩ (by decide)) (by decide)
example : LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ (_ : Unit) => 0) cPath := by
  rintro ⟨f, ⟨⟩⟩ ⟨g, ⟨⟩⟩ ⟨hf, hg⟩; simp only at hf hg; subst hf; subst hg
  exact Or.inl (by decide)
example : ¬ LexDecreasing (fun _ : Fin 1 => 0) oneComp (fun _ _ => 0) cLoop := fun h => by
  have := h (0, ()) (0, ()) trivial
  simp [LexLt, lexMeasure] at this
example : Terminates cCount := terminates_cCount
example : ¬ Terminates cLoop := not_terminates_cLoop

/-! ## Facts about the fixture `cUnbounded` (fully proved) -/

theorem callsInGraph_gPathLoop1_cUnbounded : CallsInGraph gPathLoop1 cUnbounded := by
  rintro ⟨f, x⟩ ⟨g, y⟩ (⟨h1, h2⟩ | ⟨h1, h2, _⟩)
  · simp only at h2; subst h2; show gPathLoop1 f 1 = true; simp [gPathLoop1]
  · simp only at h2; subst h2; show gPathLoop1 f 1 = true; simp [gPathLoop1]

theorem intraDecrease_cUnbounded : IntraDecrease idComp (fun _ x => x) cUnbounded := by
  rintro ⟨f, x⟩ ⟨g, y⟩ (⟨h1, h2⟩ | ⟨h1, h2, h3⟩) heq
  · have hf : f = 0 := congrArg Prod.fst h1
    simp only [idComp] at h2 heq; subst hf; subst h2; exact absurd heq (by decide)
  · simp only at h3 ⊢; omega

theorem lexDecreasing_cUnbounded :
    LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded := by
  rintro ⟨f, x⟩ ⟨g, y⟩ (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
  · have hf : f = 0 := congrArg Prod.fst h1
    simp only at h2; subst hf; subst h2
    exact Or.inl (by show 1 - (1 : Fin 2).val < 1 - (0 : Fin 2).val; decide)
  · simp only at h1 h2 h3; subst h1; subst h2
    exact Or.inr ⟨rfl, by show y < x; omega⟩

theorem interRankDecrease_cUnbounded :
    InterRankDecrease (fun c : Fin 2 => 1 - c.val) idComp cUnbounded := by
  rintro ⟨f, x⟩ ⟨g, y⟩ (⟨h1, h2⟩ | ⟨h1, h2, _⟩) hne
  · have hf : f = 0 := congrArg Prod.fst h1
    simp only at h2; subst hf; subst h2
    show 1 - (1 : Fin 2).val < 1 - (0 : Fin 2).val; decide
  · simp only [idComp] at h1 h2 hne; exact absurd (h1.trans h2.symm) hne

theorem terminates_cUnbounded : Terminates cUnbounded := by
  have h1 : ∀ y : Nat, Acc (fun b a => cUnbounded a b) (1, y) := by
    intro y
    induction y with
    | zero =>
      refine Acc.intro _ fun ⟨g, z⟩ hb => ?_
      rcases hb with ⟨h, _⟩ | ⟨_, _, h⟩
      · exact absurd (congrArg Prod.fst h) (by decide)
      · simp at h
    | succ y ih =>
      refine Acc.intro _ fun ⟨g, z⟩ hb => ?_
      rcases hb with ⟨h, _⟩ | ⟨_, hg, hz⟩
      · have hf : (1 : Fin 2) = 0 := congrArg Prod.fst h
        exact absurd hf (by decide)
      · simp only at hg hz; subst hg
        have : z = y := by omega
        subst this; exact ih
  intro ⟨f, x⟩
  match f with
  | ⟨0, _⟩ =>
    refine Acc.intro _ fun ⟨g, y⟩ hb => ?_
    rcases hb with ⟨_, hg⟩ | ⟨h, _, _⟩
    · simp only at hg; subst hg; exact h1 y
    · exact absurd h (by show (⟨0, by decide⟩ : Fin 2) ≠ 1; decide)
  | ⟨1, _⟩ => exact h1 x

/-- No measure into `Nat` on configurations decreases along every call of `cUnbounded`:
the configuration `(0, 0)` would have to exceed the measure of `(1, y)` for every `y`,
and the measure of `(1, y)` is at least `y`. -/
theorem no_nat_measure_cUnbounded :
    ∀ μ : Fin 2 × Nat → Nat, ¬ ∀ a b, cUnbounded a b → μ b < μ a := by
  intro μ hμ
  have hlow : ∀ y : Nat, y ≤ μ (1, y) := by
    intro y
    induction y with
    | zero => exact Nat.zero_le _
    | succ y ih =>
      have hstep : μ (1, y) < μ (1, y + 1) := hμ (1, y + 1) (1, y) (Or.inr ⟨rfl, rfl, rfl⟩)
      omega
  have hlt : μ (1, μ (0, 0)) < μ (0, 0) := hμ (0, 0) (1, μ (0, 0)) (Or.inl ⟨rfl, rfl⟩)
  have hge := hlow (μ (0, 0))
  omega

/-- With bounded (here: single) cross-block branching, a scalar measure can exist even when
the unmodified inner measure increases across blocks. -/
theorem cJump_has_nat_measure : ∃ μ : Fin 2 × Nat → Nat, ∀ a b, cJump a b → μ b < μ a := by
  refine ⟨fun a => if a.1 = 0 then 6 else a.2, ?_⟩
  rintro a b ⟨ha, hb⟩; subst ha; subst hb; decide

/-! ## Card `lex-iff` -/

/-- With a rank on blocks that is injective on the blocks used by `comp`, the
lexicographic measure decreases along every call iff calls inside a block decrease the
inner measure and calls across blocks go to a block of smaller rank.  (No SCC property
of `comp` is assumed.) -/
theorem lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks
    {n k : Nat} {S : Type} {rank : Fin k → Nat} {comp : Fin n → Fin k}
    {inner : Fin n → S → Nat} {C : Calls n S}
    (hinj : ∀ f g, rank (comp f) = rank (comp g) → comp f = comp g) :
    LexDecreasing rank comp inner C ↔ IntraDecrease comp inner C ∧ InterRankDecrease rank comp C := by
  refine ⟨fun h => ⟨fun a b hab heq => ?_, fun a b hab hne => ?_⟩, fun ⟨h1, h2⟩ a b hab => ?_⟩
  · rcases h a b hab with hlt | ⟨_, hlt⟩
    · simp [lexMeasure, heq] at hlt
    · exact hlt
  · rcases h a b hab with hlt | ⟨heq, _⟩
    · exact hlt
    · exact absurd (hinj a.1 b.1 heq.symm) hne
  · by_cases h : comp a.1 = comp b.1
    · exact Or.inr ⟨congrArg rank h.symm, h1 a b hab h⟩
    · exact Or.inl (h2 a b hab h)

/-- A decreasing lexicographic measure implies termination (well-foundedness of the
lexicographic order on `Nat × Nat`). -/
theorem terminates_of_lexDecreasing {n k : Nat} {S : Type} {rank : Fin k → Nat}
    {comp : Fin n → Fin k} {inner : Fin n → S → Nat} {C : Calls n S}
    (h : LexDecreasing rank comp inner C) : Terminates C := by
  have hwf : WellFounded (Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·)) :=
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  have hsub : ∀ {b a : Fin n × S}, C a b →
      InvImage (Prod.Lex (· < ·) (· < ·)) (lexMeasure rank comp inner) b a := by
    intro b a hab
    have hl := h a b hab
    simp only [LexLt, lexMeasure] at hl
    show Prod.Lex (· < ·) (· < ·) (rank (comp b.1), inner b.1 b.2) (rank (comp a.1), inner a.1 a.2)
    rcases hl with hlt | ⟨heq, hlt⟩
    · exact Prod.Lex.left _ _ hlt
    · rw [heq]; exact Prod.Lex.right _ hlt
  intro a
  exact (Subrelation.wf hsub (InvImage.wf (lexMeasure rank comp inner) hwf)).apply a

/-- Composition with `topo-order`: the position in a covering order is a rank that is
injective on used blocks, so `lex-iff` applies to it (fully proved corollary). -/
theorem lexDecreasing_pos_iff_of_covers {n k : Nat} {S : Type} {comp : Fin n → Fin k}
    {order : List (Fin k)} {inner : Fin n → S → Nat} {C : Calls n S}
    (hcover : Covers comp order) :
    LexDecreasing (pos order) comp inner C ↔
      IntraDecrease comp inner C ∧ InterRankDecrease (pos order) comp C :=
  lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks
    (pos_injective_on_used_blocks_of_covers hcover)

/-- Tightness of `hinj`: two blocks of equal rank, one call between them that decreases the
inner measure.  The lexicographic measure decreases, but the call does not go to a block of
smaller rank. -/
theorem lexIff_tight_injective :
    ¬ (∀ f g : Fin 2, (fun _ : Fin 2 => 0) (idComp f) = (fun _ : Fin 2 => 0) (idComp g) →
        idComp f = idComp g) ∧
      ¬ (LexDecreasing (fun _ : Fin 2 => 0) idComp (fun f (_ : Unit) => 1 - f.val) cPath ↔
        IntraDecrease idComp (fun f (_ : Unit) => 1 - f.val) cPath ∧
          InterRankDecrease (fun _ : Fin 2 => 0) idComp cPath) := by
  refine ⟨fun h => absurd (h 0 1 rfl) (by decide), fun h => ?_⟩
  have hlex : LexDecreasing (fun _ : Fin 2 => 0) idComp (fun f (_ : Unit) => 1 - f.val) cPath := by
    rintro ⟨f, ⟨⟩⟩ ⟨g, ⟨⟩⟩ ⟨hf, hg⟩; simp only at hf hg; subst hf; subst hg
    exact Or.inr ⟨rfl, by decide⟩
  exact absurd ((h.1 hlex).2 (0, ()) (1, ()) ⟨rfl, rfl⟩ (by decide)) (by decide)

/-- Non-vacuity: an injective rank, intra-block recursion that decreases the inner measure,
and a cross-block call to a lower-ranked block; both sides hold. -/
theorem lexIff_nonvacuous :
    (∀ f g : Fin 2, 1 - (idComp f).val = 1 - (idComp g).val → idComp f = idComp g) ∧
      LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded ∧
      IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      InterRankDecrease (fun c : Fin 2 => 1 - c.val) idComp cUnbounded ∧
      cUnbounded (1, 1) (1, 0) ∧ cUnbounded (0, 0) (1, 7) :=
  ⟨fun f g h => Fin.ext (by simp only [idComp] at h ⊢; have := f.isLt; have := g.isLt; omega),
    lexDecreasing_cUnbounded, intraDecrease_cUnbounded, interRankDecrease_cUnbounded,
    Or.inr ⟨rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- Tightness of the hypothesis of `terminates_of_lexDecreasing`: a non-terminating
self-loop, for which the lexicographic measure with constant components does not
decrease. -/
theorem lexTerminates_tight_lexDecreasing :
    ¬ LexDecreasing (fun _ : Fin 1 => 0) oneComp (fun _ (_ : Unit) => 0) cLoop ∧
      ¬ Terminates cLoop :=
  ⟨fun h => by have := h (0, ()) (0, ()) trivial; simp [LexLt, lexMeasure] at this,
    not_terminates_cLoop⟩

/-- Non-vacuity of `terminates_of_lexDecreasing` on a call relation with intra-block
recursion and unbounded cross-block fan-out. -/
theorem lexTerminates_nonvacuous :
    LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded :=
  lexDecreasing_cUnbounded

/-! ## Card `termination-intra` -/

/-- If the condensation is acyclic and every call follows the call graph, then decrease of
the inner measure on calls inside blocks alone implies termination: no rank on blocks has
to be supplied or checked. -/
theorem terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease
    {n k : Nat} {S : Type} {E : Graph n} {comp : Fin n → Fin k} {inner : Fin n → S → Nat}
    {C : Calls n S} (hacyc : CondensationAcyclic E comp) (hin : CallsInGraph E C)
    (hdec : IntraDecrease comp inner C) : Terminates C := by
  obtain ⟨order, _, _, hfirst⟩ :=
    (condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order E comp).mp hacyc
  apply terminates_of_lexDecreasing (rank := pos order) (comp := comp) (inner := inner)
  intro a b hab
  by_cases heq : comp a.1 = comp b.1
  · exact Or.inr ⟨by simp only [lexMeasure, heq], hdec a b hab heq⟩
  · exact Or.inl (hfirst a.1 b.1 (hin a b hab) heq).2.2

theorem terminationIntra_tight_acyclic :
    CallsInGraph gCycle cCycle ∧ IntraDecrease idComp (fun _ (_ : Unit) => 0) cCycle ∧
      ¬ CondensationAcyclic gCycle idComp ∧ ¬ Terminates cCycle := by
  refine ⟨?_, ?_, not_condensationAcyclic_gCycle_id, not_terminates_cCycle⟩
  · intro a b h; simpa [gCycle, cCycle] using h
  · intro a b h he; exact absurd he h

theorem terminationIntra_tight_callsInGraph :
    CondensationAcyclic gEmpty idComp ∧ IntraDecrease idComp (fun _ (_ : Unit) => 0) cCycle ∧
      ¬ CallsInGraph gEmpty cCycle ∧ ¬ Terminates cCycle := by
  refine ⟨condensationAcyclic_of_calleesFirst (order := [0]) (by decide), ?_, ?_,
    not_terminates_cCycle⟩
  · intro a b h he; exact absurd he h
  · intro h; exact absurd (h (0, ()) (1, ()) (show (0 : Fin 2) ≠ 1 by decide)) (by decide)

theorem terminationIntra_tight_intraDecrease :
    CondensationAcyclic gLoop oneComp ∧ CallsInGraph gLoop cLoop ∧
      ¬ IntraDecrease oneComp (fun _ (_ : Unit) => 0) cLoop ∧ ¬ Terminates cLoop :=
  ⟨condensationAcyclic_of_calleesFirst (order := [0]) (by decide), fun _ _ _ => rfl,
    fun h => absurd (h (0, ()) (0, ()) trivial rfl) (by decide), not_terminates_cLoop⟩

/-- Non-vacuity: two blocks with a condensation edge, a genuinely recursive callee block,
and unbounded cross-block fan-out. -/
theorem terminationIntra_nonvacuous :
    CondensationAcyclic gPathLoop1 idComp ∧ CondEdge gPathLoop1 idComp 0 1 ∧
      CallsInGraph gPathLoop1 cUnbounded ∧ IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      cUnbounded (1, 1) (1, 0) :=
  ⟨condensationAcyclic_of_calleesFirst (order := [1, 0]) (by decide),
    ⟨by decide, 0, 1, rfl, rfl, by decide⟩, callsInGraph_gPathLoop1_cUnbounded,
    intraDecrease_cUnbounded, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-! ## Card `inner-alone` -/

/-- With unbounded fan-out from a caller block into a recursive callee block, the inner
measure that decreases on every intra-block call does not decrease on the cross-block
calls, and no measure into `Nat` on configurations decreases along every call at all;
yet the call relation terminates, and the lexicographic measure `(block rank, inner)`
decreases. -/
theorem inner_alone_fails_and_no_nat_measure_of_unbounded_cross_block_fanout :
    IsSccDecomp gPathLoop1 idComp ∧ CallsInGraph gPathLoop1 cUnbounded ∧
      IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      ¬ (∀ a b, cUnbounded a b → b.2 < a.2) ∧
      (∀ μ : Fin 2 × Nat → Nat, ¬ ∀ a b, cUnbounded a b → μ b < μ a) ∧
      LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded ∧
      Terminates cUnbounded :=
  ⟨isSccDecomp_gPathLoop1_id, callsInGraph_gPathLoop1_cUnbounded, intraDecrease_cUnbounded,
    fun h => absurd (h (0, 0) (1, 5) (Or.inl ⟨rfl, rfl⟩)) (by decide),
    no_nat_measure_cUnbounded, lexDecreasing_cUnbounded, terminates_cUnbounded⟩

end Toy.Scc
