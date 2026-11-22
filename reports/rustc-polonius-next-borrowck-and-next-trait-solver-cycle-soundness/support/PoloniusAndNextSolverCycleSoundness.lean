/-
  Kernel-Checked Formalization:
  1. Polonius::Next Flow-Sensitive CFG x Region Loan Reachability (with Kill Edges
     and Bidirectional Invariant Edges) vs. Flow-Insensitive NLL.
  2. rustc_next_trait_solver SearchGraph 3-Valued Fixpoint Cycle Polarity across
     TypingMode::{Typeck, Coherence} (1.98/1.99 TypingMode dispatch and 1.102/main
     universal ambiguity on unproductive cycles).
  3. Higher-Ranked Implied-Bounds Well-Formedness Discipline (-Z assumptions-on-binders
     vs. rust-lang/rust#25860 arbitrary lifetime extension).

  Toolchain target: Lean 4 v4.34.1 (Init only, zero external imports).
  Audit profile: purely constructive structural proofs, zero classical axioms,
                 zero compiler-reflection shortcuts, zero unproved goals.
-/

namespace PoloniusAndNextSolverCycleSoundness

/-! ============================================================================
    SECTION 1: Polonius::Next Flow-Sensitive Loan Reachability vs. NLL
    Mirrors `compiler/rustc_borrowck/src/polonius/{mod.rs,constraints.rs,liveness.rs}`
============================================================================ -/

abbrev Point := Nat
abbrev Region := Nat
abbrev Loan := Nat

/-- Mirrors `rustc_borrowck::polonius::ConstraintDirection` (`polonius/mod.rs`). -/
inductive ConstraintDirection where
  | forward        -- covariant: `O@P1 -> O@P2`
  | backward       -- contravariant: `O@P2 -> O@P1`
  | bidirectional  -- invariant: `O@P1 <-> O@P2` (enables "flowing back in time")
  deriving DecidableEq

def ConstraintDirection.allowsForward : ConstraintDirection -> Bool
  | .forward => true
  | .bidirectional => true
  | .backward => false

def ConstraintDirection.allowsBackward : ConstraintDirection -> Bool
  | .backward => true
  | .bidirectional => true
  | .forward => false

/-- Localized graph node `(region, point)` mirroring `LocalizedNode` (`constraints.rs`). -/
structure LocalizedNode where
  region : Region
  point  : Point
  deriving DecidableEq

/-- Abstract MIR borrow-check constraint system combining CFG edges, localized
    and all-point outlives edges, region variances, region liveness, loan seeds,
    kill points, and invalidation points. -/
structure BorrowGraph where
  cfgEdges       : List (Point × Point)
  typeckSubsets  : List (Point × Region × Region)
  globalSubsets  : List (Region × Region)
  dirOf          : Region -> ConstraintDirection
  liveAt         : Region -> Point -> Bool
  issuedAt       : List (Loan × Region × Point)
  killedAt       : Loan -> Point -> Bool
  invalidatedAt  : Loan -> Point -> Bool

/-- Single transition in `Polonius::Next`'s `LocalizedConstraintGraph` traversal
    for a fixed loan `l`, incorporating kill-guarded forward CFG edges and
    variance-directed backward ("time-travel") CFG edges. -/
inductive PoloniusStep (g : BorrowGraph) (l : Loan) : LocalizedNode -> LocalizedNode -> Prop where
  | typeck (p : Point) (r1 r2 : Region)
      (h : (p, r1, r2) ∈ g.typeckSubsets) :
      PoloniusStep g l ⟨r1, p⟩ ⟨r2, p⟩
  | global (p : Point) (r1 r2 : Region)
      (h : (r1, r2) ∈ g.globalSubsets) :
      PoloniusStep g l ⟨r1, p⟩ ⟨r2, p⟩
  | fwdLiveness (r : Region) (p q : Point)
      (hEdge : (p, q) ∈ g.cfgEdges)
      (hDir : (g.dirOf r).allowsForward = true)
      (hLiveQ : g.liveAt r q = true)
      (hNotKilled : g.killedAt l p = false) :
      PoloniusStep g l ⟨r, p⟩ ⟨r, q⟩
  | bwdLiveness (r : Region) (p q : Point)
      (hEdge : (p, q) ∈ g.cfgEdges)
      (hDir : (g.dirOf r).allowsBackward = true)
      (hLiveQ : g.liveAt r q = true) :
      PoloniusStep g l ⟨r, q⟩ ⟨r, p⟩

/-- Reachability from a loan's introduction point `(r0, p0)` in `Polonius::Next`. -/
inductive PoloniusReach (g : BorrowGraph) (l : Loan) : LocalizedNode -> Prop where
  | seed (r0 : Region) (p0 : Point)
      (h : (l, r0, p0) ∈ g.issuedAt) :
      PoloniusReach g l ⟨r0, p0⟩
  | step {u v : LocalizedNode}
      (hReach : PoloniusReach g l u)
      (hStep : PoloniusStep g l u v) :
      PoloniusReach g l v

/-- Mirrors `LoanLivenessVisitor::on_node_traversed`:
    a loan `l` is recorded in `LiveLoans` at point `p` when it reaches some
    localized node `(r, p)` whose region `r` is live at `p`. -/
def PoloniusLiveLoan (g : BorrowGraph) (l : Loan) (p : Point) : Prop :=
  ∃ r : Region, PoloniusReach g l ⟨r, p⟩ ∧ g.liveAt r p = true

/-- `Polonius::Next` accepts a borrow graph iff no live loan is invalidated. -/
def PoloniusAccepts (g : BorrowGraph) : Prop :=
  ∀ (l : Loan) (p : Point), PoloniusLiveLoan g l p -> g.invalidatedAt l p = false

/-- Operational aliasing conflict trace: a concrete provenance chain carrying an
    active reference for loan `l` (via assignments/subtyping, forward execution
    without overwriting/killing the borrow, or invariant write-back through a
    mutable reference `&mut &mut T` to an earlier alias) to a live use at point
    `p` where `l`'s borrowed place is simultaneously invalidated. -/
inductive ProvenanceChain (g : BorrowGraph) (l : Loan) : LocalizedNode -> Prop where
  | origin (r0 : Region) (p0 : Point)
      (h : (l, r0, p0) ∈ g.issuedAt) :
      ProvenanceChain g l ⟨r0, p0⟩
  | assignLocal (p : Point) (r1 r2 : Region)
      (hPrev : ProvenanceChain g l ⟨r1, p⟩)
      (hSub : (p, r1, r2) ∈ g.typeckSubsets) :
      ProvenanceChain g l ⟨r2, p⟩
  | assignGlobal (p : Point) (r1 r2 : Region)
      (hPrev : ProvenanceChain g l ⟨r1, p⟩)
      (hSub : (r1, r2) ∈ g.globalSubsets) :
      ProvenanceChain g l ⟨r2, p⟩
  | execForward (r : Region) (p q : Point)
      (hPrev : ProvenanceChain g l ⟨r, p⟩)
      (hEdge : (p, q) ∈ g.cfgEdges)
      (hDir : (g.dirOf r).allowsForward = true)
      (hLiveQ : g.liveAt r q = true)
      (hNotKilled : g.killedAt l p = false) :
      ProvenanceChain g l ⟨r, q⟩
  | invariantWriteBack (r : Region) (p q : Point)
      (hPrev : ProvenanceChain g l ⟨r, q⟩)
      (hEdge : (p, q) ∈ g.cfgEdges)
      (hInv : (g.dirOf r).allowsBackward = true)
      (hLiveQ : g.liveAt r q = true) :
      ProvenanceChain g l ⟨r, p⟩

/-- Concrete aliasing undefined behavior: loan `l` has an active live capability
    at point `p` where `l` is invalidated. -/
def AliasingConflict (g : BorrowGraph) (l : Loan) (p : Point) : Prop :=
  (∃ r : Region, ProvenanceChain g l ⟨r, p⟩ ∧ g.liveAt r p = true) ∧
  g.invalidatedAt l p = true

def NoAliasingConflict (g : BorrowGraph) : Prop :=
  ∀ (l : Loan) (p : Point), ¬ AliasingConflict g l p

theorem provenanceChain_implies_poloniusReach
    (g : BorrowGraph) (l : Loan) (u : LocalizedNode)
    (h : ProvenanceChain g l u) :
    PoloniusReach g l u := by
  induction h with
  | origin r0 p0 hSeed =>
      exact PoloniusReach.seed r0 p0 hSeed
  | assignLocal p r1 r2 _ hSub ih =>
      exact PoloniusReach.step ih (PoloniusStep.typeck p r1 r2 hSub)
  | assignGlobal p r1 r2 _ hSub ih =>
      exact PoloniusReach.step ih (PoloniusStep.global p r1 r2 hSub)
  | execForward r p q _ hEdge hDir hLiveQ hNotKilled ih =>
      exact PoloniusReach.step ih (PoloniusStep.fwdLiveness r p q hEdge hDir hLiveQ hNotKilled)
  | invariantWriteBack r p q _ hEdge hInv hLiveQ ih =>
      exact PoloniusReach.step ih (PoloniusStep.bwdLiveness r p q hEdge hInv hLiveQ)

theorem polonius_accepts_implies_no_aliasing_ub
    (g : BorrowGraph) (hAcc : PoloniusAccepts g) :
    NoAliasingConflict g := by
  intro l p hConf
  rcases hConf with ⟨⟨r, hChain, hLive⟩, hInv⟩
  have hReach : PoloniusReach g l ⟨r, p⟩ :=
    provenanceChain_implies_poloniusReach g l ⟨r, p⟩ hChain
  have hFalse : g.invalidatedAt l p = false := hAcc l p ⟨r, hReach, hLive⟩
  rw [hFalse] at hInv
  cases hInv

/-- Flow-insensitive NLL region inclusion: collapses all localized typeck
    outlives edges `(p, r1, r2)` into global region subset edges `r1 ⊆ r2`. -/
inductive NllSubset (g : BorrowGraph) : Region -> Region -> Prop where
  | refl (r : Region) : NllSubset g r r
  | stepLocal {r1 r2 r3 : Region} (p : Point)
      (h12 : NllSubset g r1 r2)
      (h23 : (p, r2, r3) ∈ g.typeckSubsets) :
      NllSubset g r1 r3
  | stepGlobal {r1 r2 r3 : Region}
      (h12 : NllSubset g r1 r2)
      (h23 : (r2, r3) ∈ g.globalSubsets) :
      NllSubset g r1 r3

/-- In flow-insensitive NLL, a loan issued into `r0` is considered live at point
    `p` whenever any NLL-superregion `r` of `r0` is live at `p`. -/
def NllLiveLoan (g : BorrowGraph) (l : Loan) (p : Point) : Prop :=
  ∃ (r0 : Region) (p0 : Point) (r : Region),
    (l, r0, p0) ∈ g.issuedAt ∧ NllSubset g r0 r ∧ g.liveAt r p = true

def NllAccepts (g : BorrowGraph) : Prop :=
  ∀ (l : Loan) (p : Point), NllLiveLoan g l p -> g.invalidatedAt l p = false

theorem poloniusReach_implies_nllSubset
    (g : BorrowGraph) (l : Loan) (u : LocalizedNode)
    (h : PoloniusReach g l u) :
    ∃ (r0 : Region) (p0 : Point), (l, r0, p0) ∈ g.issuedAt ∧ NllSubset g r0 u.region := by
  induction h with
  | seed r0 p0 hSeed =>
      exact ⟨r0, p0, hSeed, NllSubset.refl r0⟩
  | step _ hStep ih =>
      rcases ih with ⟨r0, p0, hSeed, hSub⟩
      cases hStep with
      | typeck p r1 r2 hEdge =>
          exact ⟨r0, p0, hSeed, NllSubset.stepLocal p hSub hEdge⟩
      | global p r1 r2 hEdge =>
          exact ⟨r0, p0, hSeed, NllSubset.stepGlobal hSub hEdge⟩
      | fwdLiveness r p q _ _ _ _ =>
          exact ⟨r0, p0, hSeed, hSub⟩
      | bwdLiveness r p q _ _ _ =>
          exact ⟨r0, p0, hSeed, hSub⟩

theorem poloniusLiveLoan_implies_nllLiveLoan
    (g : BorrowGraph) (l : Loan) (p : Point)
    (h : PoloniusLiveLoan g l p) :
    NllLiveLoan g l p := by
  rcases h with ⟨r, hReach, hLive⟩
  rcases poloniusReach_implies_nllSubset g l ⟨r, p⟩ hReach with ⟨r0, p0, hSeed, hSub⟩
  exact ⟨r0, p0, r, hSeed, hSub, hLive⟩

theorem nllAccepts_implies_poloniusAccepts
    (g : BorrowGraph) (hNll : NllAccepts g) :
    PoloniusAccepts g := by
  intro l p hPol
  exact hNll l p (poloniusLiveLoan_implies_nllLiveLoan g l p hPol)

/-- Concrete NLL Problem Case #3 (`get_or_insert` HashMap):
    Points: 0 = entry (`map.get_mut`), 1 = `Some(v) => return v`, 2 = `None => map.insert`.
    Regions: 0 = `'loan` (covariant, live at 0 and 1, dead at 2),
             1 = `'ret`  (universal return lifetime, covariant, live at 0, 1, 2).
    CFG edges: `0 -> 1` (Some branch), `0 -> 2` (None branch).
    Localized subset edge: `(1, 0, 1)` (`'loan ⊆ 'ret` ONLY on the `Some` return branch!).
    Loan 0 issued into region 0 at point 0; invalidated at point 2 (`map.insert`). -/
def problemCase3Graph : BorrowGraph where
  cfgEdges := [(0, 1), (0, 2)]
  typeckSubsets := [(1, 0, 1)]
  globalSubsets := []
  dirOf := fun _ => .forward
  liveAt := fun r p =>
    match r, p with
    | 0, 0 => true
    | 0, 1 => true
    | 1, 0 => true
    | 1, 1 => true
    | 1, 2 => true
    | _, _ => false
  issuedAt := [(0, 0, 0)]
  killedAt := fun _ _ => false
  invalidatedAt := fun l p => (l == 0) && (p == 2)

/-- Reachable nodes of loan 0 in `problemCase3Graph` stay strictly within
    `{(0, 0), (0, 1), (1, 1)}`: loan 0 NEVER reaches point 2. -/
private def pc3Invariant (u : LocalizedNode) : Prop :=
  u = ⟨0, 0⟩ ∨ u = ⟨0, 1⟩ ∨ u = ⟨1, 1⟩

private theorem pc3_reach_invariant (l : Loan) (u : LocalizedNode)
    (h : PoloniusReach problemCase3Graph l u) :
    l = 0 ∧ pc3Invariant u := by
  induction h with
  | seed r0 p0 hSeed =>
      simp only [problemCase3Graph, List.mem_singleton, Prod.mk.injEq] at hSeed
      rcases hSeed with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
  | step _ hStep ih =>
      rcases ih with ⟨rfl, hInv⟩
      refine ⟨rfl, ?_⟩
      cases hStep with
      | typeck p r1 r2 hSub =>
          simp only [problemCase3Graph, List.mem_singleton, Prod.mk.injEq] at hSub
          rcases hSub with ⟨rfl, rfl, rfl⟩
          exact Or.inr (Or.inr rfl)
      | global p r1 r2 hGlob =>
          simp only [problemCase3Graph, List.not_mem_nil] at hGlob
      | fwdLiveness r p q hEdge _ hLiveQ _ =>
          simp only [problemCase3Graph, List.mem_cons, List.not_mem_nil, or_false,
                     Prod.mk.injEq] at hEdge
          rcases hInv with h0 | h1 | h2
          · injection h0 with hr hp
            subst hr; subst hp
            rcases hEdge with ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact Or.inr (Or.inl rfl)
            · simp [problemCase3Graph] at hLiveQ
          · injection h1 with hr hp
            subst hr; subst hp
            rcases hEdge with ⟨hContra, _⟩ | ⟨hContra, _⟩ <;> cases hContra
          · injection h2 with hr hp
            subst hr; subst hp
            rcases hEdge with ⟨hContra, _⟩ | ⟨hContra, _⟩ <;> cases hContra
      | bwdLiveness r p q _ hDir _ =>
          simp [problemCase3Graph, ConstraintDirection.allowsBackward] at hDir

theorem problemCase3_polonius_accepts : PoloniusAccepts problemCase3Graph := by
  intro l p hLive
  rcases hLive with ⟨r, hReach, _⟩
  rcases pc3_reach_invariant l ⟨r, p⟩ hReach with ⟨rfl, hInv⟩
  rcases hInv with h0 | h1 | h2
  · injection h0 with _ hp; subst hp; rfl
  · injection h1 with _ hp; subst hp; rfl
  · injection h2 with _ hp; subst hp; rfl

theorem problemCase3_nll_rejects : ¬ NllAccepts problemCase3Graph := by
  intro hNll
  have hSub : NllSubset problemCase3Graph 0 1 :=
    NllSubset.stepLocal 1 (NllSubset.refl 0) (by simp [problemCase3Graph])
  have hSeed : (0, 0, 0) ∈ problemCase3Graph.issuedAt := by simp [problemCase3Graph]
  have hLive : problemCase3Graph.liveAt 1 2 = true := rfl
  have hFalse : problemCase3Graph.invalidatedAt 0 2 = false :=
    hNll 0 2 ⟨0, 0, 1, hSeed, hSub, hLive⟩
  cases hFalse

/-- Main Theorem 1: `Polonius::Next` is sound against concrete aliasing conflicts
    and strictly more precise than flow-insensitive NLL. -/
theorem polonius_sound_and_strictly_more_precise_than_nll :
    (∀ g : BorrowGraph, PoloniusAccepts g -> NoAliasingConflict g) ∧
    (∀ g : BorrowGraph, NllAccepts g -> PoloniusAccepts g) ∧
    (∃ g : BorrowGraph, PoloniusAccepts g ∧ ¬ NllAccepts g) :=
  ⟨polonius_accepts_implies_no_aliasing_ub,
   nllAccepts_implies_poloniusAccepts,
   ⟨problemCase3Graph, problemCase3_polonius_accepts, problemCase3_nll_rejects⟩⟩

/-! ### Constructive Counterexample 1: Omitting Bidirectional Invariant Edges -/

/-- Buggy forward-only Polonius step relation that omits `bwdLiveness` ("time-travel")
    edges even for invariant (`ConstraintDirection.bidirectional`) regions. -/
inductive PoloniusNoBwdStep (g : BorrowGraph) (l : Loan) :
    LocalizedNode -> LocalizedNode -> Prop where
  | typeck (p : Point) (r1 r2 : Region)
      (h : (p, r1, r2) ∈ g.typeckSubsets) :
      PoloniusNoBwdStep g l ⟨r1, p⟩ ⟨r2, p⟩
  | global (p : Point) (r1 r2 : Region)
      (h : (r1, r2) ∈ g.globalSubsets) :
      PoloniusNoBwdStep g l ⟨r1, p⟩ ⟨r2, p⟩
  | fwdLiveness (r : Region) (p q : Point)
      (hEdge : (p, q) ∈ g.cfgEdges)
      (hDir : (g.dirOf r).allowsForward = true)
      (hLiveQ : g.liveAt r q = true)
      (hNotKilled : g.killedAt l p = false) :
      PoloniusNoBwdStep g l ⟨r, p⟩ ⟨r, q⟩

inductive PoloniusNoBwdReach (g : BorrowGraph) (l : Loan) : LocalizedNode -> Prop where
  | seed (r0 : Region) (p0 : Point)
      (h : (l, r0, p0) ∈ g.issuedAt) :
      PoloniusNoBwdReach g l ⟨r0, p0⟩
  | step {u v : LocalizedNode}
      (hReach : PoloniusNoBwdReach g l u)
      (hStep : PoloniusNoBwdStep g l u v) :
      PoloniusNoBwdReach g l v

def PoloniusNoBwdAccepts (g : BorrowGraph) : Prop :=
  ∀ (l : Loan) (p : Point),
    (∃ r : Region, PoloniusNoBwdReach g l ⟨r, p⟩ ∧ g.liveAt r p = true) ->
    g.invalidatedAt l p = false

/-- Concrete invariant write-back graph mirroring `invariant_time_travel`:
      p0: `let q: &mut &mut i32 = &mut p;`  -- localized invariant edge `(0, r_q, r_p)`
      p1: `*q = &mut b;`                     -- loan 0 issued into invariant `r_q` at `p1`
      p2: `b = 3; let _ = *p;`               -- invalidates loan 0 while `r_p` is live at `p2`
    Regions: 0 = `r_q` (bidirectional/invariant, live at 0, 1),
             1 = `r_p` (covariant/forward, live at 0, 1, 2).
    CFG: `0 -> 1 -> 2`. -/
def badInvariantGraph : BorrowGraph where
  cfgEdges := [(0, 1), (1, 2)]
  typeckSubsets := [(0, 0, 1)]
  globalSubsets := []
  dirOf := fun r => if r == 0 then .bidirectional else .forward
  liveAt := fun r p =>
    match r, p with
    | 0, 0 => true
    | 0, 1 => true
    | 1, 0 => true
    | 1, 1 => true
    | 1, 2 => true
    | _, _ => false
  issuedAt := [(0, 0, 1)]
  killedAt := fun _ _ => false
  invalidatedAt := fun l p => (l == 0) && (p == 2)

private theorem badInvariant_noBwd_stuck (l : Loan) (u : LocalizedNode)
    (h : PoloniusNoBwdReach badInvariantGraph l u) :
    l = 0 ∧ u = ⟨0, 1⟩ := by
  induction h with
  | seed r0 p0 hSeed =>
      simp only [badInvariantGraph, List.mem_singleton, Prod.mk.injEq] at hSeed
      rcases hSeed with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | step _ hStep ih =>
      rcases ih with ⟨rfl, hu⟩
      cases hStep with
      | typeck p r1 r2 hSub =>
          simp only [badInvariantGraph, List.mem_singleton, Prod.mk.injEq] at hSub
          rcases hSub with ⟨rfl, rfl, rfl⟩
          injection hu with _ hp
          cases hp
      | global p r1 r2 hGlob =>
          simp only [badInvariantGraph, List.not_mem_nil] at hGlob
      | fwdLiveness r p q hEdge _ hLiveQ _ =>
          injection hu with hr hp
          subst hr; subst hp
          simp only [badInvariantGraph, List.mem_cons, List.not_mem_nil, or_false,
                     Prod.mk.injEq] at hEdge
          rcases hEdge with ⟨hContra, _⟩ | ⟨_, rfl⟩
          · cases hContra
          · simp [badInvariantGraph] at hLiveQ

/-- Counterexample 1: Dropping bidirectional backward edges makes the buggy
    borrow checker ACCEPT `badInvariantGraph`, whereas true `Polonius::Next`
    REJECTS it and a concrete aliasing UB provenance chain exists at `(0, 2)`. -/
theorem ce1_omitting_bidirectional_invariant_edge_admits_aliasing_ub :
    PoloniusNoBwdAccepts badInvariantGraph ∧
    ¬ PoloniusAccepts badInvariantGraph ∧
    AliasingConflict badInvariantGraph 0 2 := by
  have hNoBwdAcc : PoloniusNoBwdAccepts badInvariantGraph := by
    intro l p ⟨r, hReach, _⟩
    rcases badInvariant_noBwd_stuck l ⟨r, p⟩ hReach with ⟨rfl, hu⟩
    injection hu with _ hp
    subst hp
    rfl
  have hChain : ProvenanceChain badInvariantGraph 0 ⟨1, 2⟩ := by
    have c0 : ProvenanceChain badInvariantGraph 0 ⟨0, 1⟩ :=
      ProvenanceChain.origin 0 1 (by simp [badInvariantGraph])
    have c1 : ProvenanceChain badInvariantGraph 0 ⟨0, 0⟩ :=
      ProvenanceChain.invariantWriteBack 0 0 1 c0 (by simp [badInvariantGraph]) rfl rfl
    have c2 : ProvenanceChain badInvariantGraph 0 ⟨1, 0⟩ :=
      ProvenanceChain.assignLocal 0 0 1 c1 (by simp [badInvariantGraph])
    have c3 : ProvenanceChain badInvariantGraph 0 ⟨1, 1⟩ :=
      ProvenanceChain.execForward 1 0 1 c2 (by simp [badInvariantGraph]) rfl rfl rfl
    exact ProvenanceChain.execForward 1 1 2 c3 (by simp [badInvariantGraph]) rfl rfl rfl
  have hConflict : AliasingConflict badInvariantGraph 0 2 :=
    ⟨⟨1, hChain, rfl⟩, rfl⟩
  have hPolRej : ¬ PoloniusAccepts badInvariantGraph := by
    intro hAcc
    exact polonius_accepts_implies_no_aliasing_ub badInvariantGraph hAcc 0 2 hConflict
  exact ⟨hNoBwdAcc, hPolRej, hConflict⟩


/-! ============================================================================
    SECTION 2: rustc_next_trait_solver SearchGraph Cycle Polarity & Coherence
    Mirrors `compiler/rustc_next_trait_solver/src/solve/search_graph.rs`
    and `compiler/rustc_type_ir/src/search_graph/mod.rs`
============================================================================ -/

abbrev GoalId := Nat

/-- 3-valued query outcome mirroring `QueryResult<I>` (`Yes`, `Overflow/Maybe`, `Err(NoSolution)`). -/
inductive SolveResult where
  | yes
  | ambiguous
  | noSolution
  deriving DecidableEq

/-- Cycle edge polarity mirroring `rustc_type_ir::search_graph::PathKind`. -/
inductive PathKind where
  | coinductive
  | inductive
  | unknown
  deriving DecidableEq

/-- Typing mode split mirroring `TypingMode::Coherence` vs. non-coherence modes (`Typeck`/`Codegen`). -/
inductive TypingMode where
  | typeck
  | coherence
  deriving DecidableEq

/-- Kleene-like 3-valued conjunction for clause premises (`noSolution` absorbs; `yes` is unit). -/
def SolveResult.and3 : SolveResult -> SolveResult -> SolveResult
  | .noSolution, _ => .noSolution
  | _, .noSolution => .noSolution
  | .yes, r        => r
  | r, .yes        => r
  | .ambiguous, .ambiguous => .ambiguous

/-- Kleene-like 3-valued disjunction across candidate impl clauses (`yes` absorbs; `noSolution` is unit). -/
def SolveResult.or3 : SolveResult -> SolveResult -> SolveResult
  | .yes, _        => .yes
  | _, .yes        => .yes
  | .noSolution, r => r
  | r, .noSolution => r
  | .ambiguous, .ambiguous => .ambiguous

/-- Combining step polarities along a cycle path: mirrors `PathsToNested` dominance
    where any inductive or unknown step prevents a cycle from being purely coinductive. -/
def PathKind.combine : PathKind -> PathKind -> PathKind
  | .coinductive, k => k
  | k, .coinductive => k
  | .unknown, _     => .unknown
  | _, .unknown     => .unknown
  | .inductive, .inductive => .inductive

/-- Initial provisional result policy mirroring `SearchGraphDelegate::initial_provisional_result`. -/
abbrev CyclePolicy := TypingMode -> PathKind -> SolveResult

/-- Exact `rustc 1.98.0-nightly / 1.99.1` (`search_graph.rs:52-79`) 3-way dispatch:
    coinductive -> `yes`; unknown -> `ambiguous`; inductive in `coherence` -> `ambiguous`;
    inductive in `typeck` -> `noSolution`. -/
def rustc1991Policy : CyclePolicy
  | _, .coinductive          => .yes
  | _, .unknown              => .ambiguous
  | .coherence, .inductive   => .ambiguous
  | .typeck, .inductive      => .noSolution

/-- Exact `rustc 1.102.0-nightly / main` (`622fd6a3f80f`, `search_graph.rs:50-70`):
    coinductive -> `yes`; all non-coinductive (`unknown` / `inductive`) cycles -> `ambiguous`. -/
def rustc1102Policy : CyclePolicy
  | _, .coinductive => .yes
  | _, .unknown     => .ambiguous
  | _, .inductive   => .ambiguous

/-- Unsound counterfactual policy: returns `noSolution` for inductive cycles even in
    `TypingMode.coherence`. -/
def unsoundCoherenceNoSolPolicy : CyclePolicy
  | _, .coinductive => .yes
  | _, .unknown     => .ambiguous
  | _, .inductive   => .noSolution

/-- A trait clause `head :- premises`, where each premise is tagged with the
    `PathKind` edge polarity taken when stepping from `head` into that subgoal. -/
structure TraitClause where
  head     : GoalId
  premises : List (PathKind × GoalId)
  deriving DecidableEq

abbrev TraitProgram := List TraitClause

/-- Look up whether `g` is already active on the search stack and compute the
    accumulated cycle polarity from the cycle head down to the back-edge. -/
noncomputable def stackCycleKind : List (GoalId × PathKind) -> GoalId -> PathKind -> Option PathKind
  | [], _, _ => none
  | (h, stepFromParent) :: rest, target, acc =>
      if h == target then
        some acc
      else
        stackCycleKind rest target (PathKind.combine stepFromParent acc)

/-- Evaluate all premises of a single clause structurally, delegating acyclic
    subgoals to `stepFn` and cycle back-edges to `policy mode cycleKind`. -/
noncomputable def evalPremisesWith (stepFn : List (GoalId × PathKind) -> GoalId -> SolveResult)
    (policy : CyclePolicy) (mode : TypingMode)
    (stack : List (GoalId × PathKind)) (parent : GoalId) :
    List (PathKind × GoalId) -> SolveResult
  | [] => .yes
  | (stepKind, sub) :: rest =>
      let rSub :=
        match stackCycleKind stack sub stepKind with
        | some cycleKind => policy mode cycleKind
        | none => stepFn ((parent, stepKind) :: stack) sub
      SolveResult.and3 rSub (evalPremisesWith stepFn policy mode stack parent rest)

/-- Evaluate all matching clauses of `prog` for goal `g` via 3-valued disjunction. -/
noncomputable def evalClausesWith (stepFn : List (GoalId × PathKind) -> GoalId -> SolveResult)
    (policy : CyclePolicy) (mode : TypingMode)
    (stack : List (GoalId × PathKind)) (g : GoalId) :
    List TraitClause -> SolveResult
  | [] => .noSolution
  | cl :: rest =>
      let rRest := evalClausesWith stepFn policy mode stack g rest
      match Nat.beq cl.head g with
      | true => SolveResult.or3 (evalPremisesWith stepFn policy mode stack g cl.premises) rRest
      | false => rRest

/-- Pure structurally recursive fuel-bounded evaluator for `SearchGraph` goal solving
    (total by structural recursion on `fuel`). Returns `ambiguous` (overflow) if fuel
    runs out. -/
noncomputable def evalGoal (policy : CyclePolicy) (mode : TypingMode) (prog : TraitProgram) :
    Nat -> List (GoalId × PathKind) -> GoalId -> SolveResult
  | 0, _, _ => .ambiguous
  | fuel + 1, stack, g =>
      evalClausesWith (evalGoal policy mode prog fuel) policy mode stack g prog

/-- In Rust coherence, two potentially overlapping impls (whose intersection reduces
    to obligation `overlapGoal`) are permitted to coexist ONLY if the trait solver
    proves `overlapGoal` has `noSolution` under `TypingMode.coherence`. -/
noncomputable def coherencePermitsBothImpls (policy : CyclePolicy) (prog : TraitProgram)
    (fuel : Nat) (overlapGoal : GoalId) : Bool :=
  evalGoal policy .coherence prog fuel [] overlapGoal == .noSolution

/-- A `CyclePolicy` is coherence-cycle-safe iff it never fabricates `noSolution`
    when breaking any cycle in `TypingMode.coherence`. -/
def CoherenceCycleSafe (policy : CyclePolicy) : Prop :=
  ∀ k : PathKind, policy .coherence k ≠ .noSolution

theorem rustc1991Policy_coherenceCycleSafe : CoherenceCycleSafe rustc1991Policy := by
  intro k
  cases k <;> intro h <;> cases h

theorem rustc1102Policy_coherenceCycleSafe : CoherenceCycleSafe rustc1102Policy := by
  intro k
  cases k <;> intro h <;> cases h

/-- Open-world / coinductive semantic inhabitance: a goal `g` is coinductively
    viable in `prog` if there exists a closed set of viable goals `S` containing `g`
    such that every goal in `S` has at least one clause whose premises all lie in `S`.
    In Rust coherence, any goal viable under a coinductive or downstream-extended
    reading MUST NOT be refuted as `noSolution`, lest overlapping impls be accepted. -/
def CoinductivelyViable (prog : TraitProgram) (g : GoalId) : Prop :=
  ∃ S : GoalId -> Prop,
    S g ∧
    ∀ x : GoalId, S x ->
      ∃ cl ∈ prog, cl.head = x ∧ ∀ p ∈ cl.premises, S p.2

private theorem and3_ne_noSolution {a b : SolveResult}
    (ha : a ≠ .noSolution) (hb : b ≠ .noSolution) :
    SolveResult.and3 a b ≠ .noSolution := by
  cases a with
  | yes =>
      cases b with
      | yes => intro h; cases h
      | ambiguous => intro h; cases h
      | noSolution => exact False.elim (hb rfl)
  | ambiguous =>
      cases b with
      | yes => intro h; cases h
      | ambiguous => intro h; cases h
      | noSolution => exact False.elim (hb rfl)
  | noSolution => exact False.elim (ha rfl)

private theorem or3_ne_noSolution_left {a b : SolveResult}
    (ha : a ≠ .noSolution) :
    SolveResult.or3 a b ≠ .noSolution := by
  cases a with
  | yes => intro h; cases h
  | ambiguous =>
      cases b with
      | yes => intro h; cases h
      | ambiguous => intro h; cases h
      | noSolution => intro h; cases h
  | noSolution => exact False.elim (ha rfl)

private theorem or3_ne_noSolution_right {a b : SolveResult}
    (hb : b ≠ .noSolution) :
    SolveResult.or3 a b ≠ .noSolution := by
  cases a with
  | yes => intro h; cases h
  | ambiguous =>
      cases b with
      | yes => intro h; cases h
      | ambiguous => intro h; cases h
      | noSolution => exact False.elim (hb rfl)
  | noSolution =>
      cases b with
      | yes => intro h; cases h
      | ambiguous => intro h; cases h
      | noSolution => exact False.elim (hb rfl)

private theorem solveResult_beq_noSolution_false {r : SolveResult}
    (h : r ≠ .noSolution) :
    (r == .noSolution) = false := by
  cases r with
  | yes => rfl
  | ambiguous => rfl
  | noSolution => exact False.elim (h rfl)

/-- Key monotonicity/soundness invariant: under ANY `CoherenceCycleSafe` policy,
    every `CoinductivelyViable` goal never evaluates to `.noSolution` in
    `TypingMode.coherence`, for any fuel and any call stack! -/
theorem evalGoal_coherence_never_noSolution_of_viable
    (policy : CyclePolicy) (hSafe : CoherenceCycleSafe policy)
    (prog : TraitProgram) (S : GoalId -> Prop)
    (hClosed : ∀ x : GoalId, S x ->
      ∃ cl ∈ prog, cl.head = x ∧ ∀ p ∈ cl.premises, S p.2) :
    ∀ (fuel : Nat) (stack : List (GoalId × PathKind)) (g : GoalId),
      S g -> evalGoal policy .coherence prog fuel stack g ≠ .noSolution := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack g _ h
      cases h
  | succ f ih =>
      intro stack g hSg
      rcases hClosed g hSg with ⟨cl, hClMem, hClHead, hClPrem⟩
      have hPremOk :
          ∀ (prems : List (PathKind × GoalId)),
            (∀ p ∈ prems, S p.2) ->
            evalPremisesWith (evalGoal policy .coherence prog f) policy .coherence stack g prems ≠ .noSolution := by
        intro prems
        induction prems with
        | nil =>
            intro _ h
            cases h
        | cons pr rest ihP =>
            intro hAll
            have hHeadS : S pr.2 := hAll pr (List.Mem.head rest)
            have hRestS : ∀ p ∈ rest, S p.2 := fun p hp => hAll p (List.Mem.tail pr hp)
            have hSubNe :
                (match stackCycleKind stack pr.2 pr.1 with
                 | some cycleKind => policy .coherence cycleKind
                 | none => evalGoal policy .coherence prog f ((g, pr.1) :: stack) pr.2)
                  ≠ .noSolution := by
              cases hCyc : stackCycleKind stack pr.2 pr.1 with
              | some ck => exact hSafe ck
              | none => exact ih ((g, pr.1) :: stack) pr.2 hHeadS
            have hRestNe := ihP hRestS
            exact and3_ne_noSolution hSubNe hRestNe
      have hClausesOk :
          ∀ (clauses : List TraitClause),
            cl ∈ clauses ->
            evalClausesWith (evalGoal policy .coherence prog f) policy .coherence stack g clauses ≠ .noSolution := by
        intro clauses
        induction clauses with
        | nil =>
            intro hMem
            cases hMem
        | cons c cs ihC =>
            intro hMem
            dsimp only [evalClausesWith]
            cases hMem with
            | head _ =>
                have hEq : Nat.beq cl.head g = true := by rw [hClHead]; exact Nat.beq_refl g
                rw [hEq]
                exact or3_ne_noSolution_left (hPremOk cl.premises hClPrem)
            | tail _ hIn =>
                have hTailNe := ihC hIn
                cases Nat.beq c.head g
                · exact hTailNe
                · exact or3_ne_noSolution_right hTailNe
      exact hClausesOk prog hClMem

/-- Concrete recursive auto-trait program (`struct Rec(Option<Box<Rec>>); Rec: Send`):
    Goal 0 (`Rec: Send`) depends coinductively on Goal 0. -/
def recSendProg : TraitProgram :=
  [{ head := 0, premises := [(.coinductive, 0)] }]

/-- Concrete inductive overlap program (`trait Loop {} impl<T: Loop> Loop for T {}`):
    Goal 0 (`u32: Loop`) depends inductively on Goal 0. -/
def inductiveOverlapProg : TraitProgram :=
  [{ head := 0, premises := [(.inductive, 0)] }]

/-- Main Theorem 2: Coherence ambiguity on inductive cycles prevents overlapping impls
    for ALL `CoherenceCycleSafe` policies (instantiated to both `rustc1991Policy` and
    `rustc1102Policy`), while still accepting coinductive `Rec: Send` and rejecting
    inductive `u32: Loop` in `TypingMode.typeck`. -/
theorem coherence_inductive_ambiguity_prevents_overlapping_impls :
    (∀ (policy : CyclePolicy) (prog : TraitProgram) (fuel : Nat) (g : GoalId),
        CoherenceCycleSafe policy ->
        CoinductivelyViable prog g ->
        coherencePermitsBothImpls policy prog fuel g = false) ∧
    (evalGoal rustc1991Policy .typeck recSendProg 4 [] 0 = .yes ∧
     evalGoal rustc1102Policy .typeck recSendProg 4 [] 0 = .yes) ∧
    (evalGoal rustc1991Policy .typeck inductiveOverlapProg 4 [] 0 ≠ .yes ∧
     evalGoal rustc1102Policy .typeck inductiveOverlapProg 4 [] 0 ≠ .yes) := by
  refine ⟨?_, ⟨rfl, rfl⟩, ⟨(fun h => by cases h), (fun h => by cases h)⟩⟩
  intro policy prog fuel g hSafe hViable
  rcases hViable with ⟨S, hSg, hClosed⟩
  have hNe := evalGoal_coherence_never_noSolution_of_viable policy hSafe prog S hClosed fuel [] g hSg
  exact solveResult_beq_noSolution_false hNe

/-- Counterexample 2: Returning `noSolution` for inductive cycles in `TypingMode.coherence`
    falsely declares `inductiveOverlapProg` disjoint (`coherencePermitsBothImpls = true`),
    admitting overlapping impls (`impl<T: Loop> Disjoint for T` and `impl Disjoint for u32`),
    even though `rustc1991Policy` and `rustc1102Policy` both reject the overlap and
    goal 0 is `CoinductivelyViable`. -/
theorem ce2_returning_no_solution_for_inductive_cycle_in_coherence_admits_overlapping_impls :
    coherencePermitsBothImpls unsoundCoherenceNoSolPolicy inductiveOverlapProg 4 0 = true ∧
    coherencePermitsBothImpls rustc1991Policy inductiveOverlapProg 4 0 = false ∧
    coherencePermitsBothImpls rustc1102Policy inductiveOverlapProg 4 0 = false ∧
    CoinductivelyViable inductiveOverlapProg 0 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  refine ⟨fun x => x = 0, rfl, ?_⟩
  intro x hx
  subst hx
  refine ⟨{ head := 0, premises := [(.inductive, 0)] }, List.Mem.head _, rfl, ?_⟩
  intro p hp
  cases hp with
  | head => rfl
  | tail _ hEmpty => cases hEmpty


/-! ============================================================================
    SECTION 3: Higher-Ranked Implied-Bounds Well-Formedness Discipline
    Mirrors `-Z assumptions-on-binders=yes` (`eval_ctxt/mod.rs:1427-1448`,
    `solver_region_constraints.rs:31-111`) vs. `rust-lang/rust#25860`
============================================================================ -/

/-- Lifetime syntactic terms: `'static`, outer free parameter `'a_k`, or bound var `'b_k`. -/
inductive Reg where
  | rStatic
  | rParam (id : Nat)
  | rBound (id : Nat)
  deriving DecidableEq

/-- Outlives constraint `lhs : rhs` (semantically `lhs` lives at least as long as `rhs`). -/
structure Outlives where
  lhs : Reg
  rhs : Reg
  deriving DecidableEq

/-- Valuation mapping each region to its lifetime extent bounded above by `staticEnd`. -/
structure LifetimeEnv where
  staticEnd : Nat
  evalParam : Nat -> Nat
  evalBound : Nat -> Nat
  paramLe   : ∀ k, evalParam k ≤ staticEnd
  boundLe   : ∀ k, evalBound k ≤ staticEnd

def LifetimeEnv.eval (env : LifetimeEnv) : Reg -> Nat
  | .rStatic  => env.staticEnd
  | .rParam k => env.evalParam k
  | .rBound k => env.evalBound k

def SemOutlives (env : LifetimeEnv) (c : Outlives) : Prop :=
  env.eval c.rhs ≤ env.eval c.lhs

def EnvSatisfies (env : LifetimeEnv) (ctx : List Outlives) : Prop :=
  ∀ c ∈ ctx, SemOutlives env c

/-- Outlives derivability from an assumption context `ctx`:
    includes reflexivity, `'static : r` for every region `r`, context assumptions,
    and transitivity. -/
inductive Derives (ctx : List Outlives) : Outlives -> Prop where
  | refl (r : Reg) :
      Derives ctx ⟨r, r⟩
  | staticTop (r : Reg) :
      Derives ctx ⟨.rStatic, r⟩
  | assume (c : Outlives) (h : c ∈ ctx) :
      Derives ctx c
  | trans {r1 r2 r3 : Reg}
      (h12 : Derives ctx ⟨r1, r2⟩)
      (h23 : Derives ctx ⟨r2, r3⟩) :
      Derives ctx ⟨r1, r3⟩

theorem derives_sound (ctx : List Outlives) (env : LifetimeEnv)
    (hCtx : EnvSatisfies env ctx) (c : Outlives) (hDer : Derives ctx c) :
    SemOutlives env c := by
  induction hDer with
  | refl r =>
      exact Nat.le_refl (env.eval r)
  | staticTop r =>
      cases r with
      | rStatic => exact Nat.le_refl env.staticEnd
      | rParam k => exact env.paramLe k
      | rBound k => exact env.boundLe k
  | assume c hMem =>
      exact hCtx c hMem
  | trans _ _ ih12 ih23 =>
      exact Nat.le_trans ih23 ih12

/-- A binder carrying syntactic implied outlives constraints extracted from its
    parameter types (e.g., `&'outer &'inner ()` syntactically implies `'inner : 'outer`). -/
structure BinderImplied where
  impliedOutlives : List Outlives

/-- Sound WF-guarded binder assumption rule: an implied outlives clause from a
    binder may enter the assumption set ONLY if it is already well-formed
    (derivable from the outer environment `outerCtx` without circularly assuming
    the binder's own unverified types). -/
def WfGuardedContext (outerCtx : List Outlives) (b : BinderImplied)
    (innerCtx : List Outlives) : Prop :=
  ∀ c ∈ innerCtx, c ∈ outerCtx ∨ (c ∈ b.impliedOutlives ∧ Derives outerCtx c)

/-- Unsound `-Z assumptions-on-binders=yes` rule: unconditionally prepends all
    syntactic `b.impliedOutlives` extracted by `RawAssumptions::visit_ty` without
    requiring them to be derivable from `outerCtx`. -/
def unwfBinderContext (outerCtx : List Outlives) (b : BinderImplied) : List Outlives :=
  b.impliedOutlives ++ outerCtx

/-- Concrete short-lifetime valuation witnessing use-after-free when `'a : 'static`
    is falsely derived: `'a` has extent 1 while `'static` has extent 100. -/
def shortLifetimeEnv : LifetimeEnv where
  staticEnd := 100
  evalParam := fun _ => 1
  evalBound := fun _ => 1
  paramLe   := fun _ => by decide
  boundLe   := fun _ => by decide

/-- Main Theorem 3: Under any WF-guarded binder discipline, every derived outlives
    judgment holds semantically in every lifetime valuation satisfying `outerCtx`,
    and from an unconstrained outer context (`[]`), arbitrary lifetime extension
    `'a : 'static` is NEVER derivable. -/
theorem wf_guarded_binder_assumptions_preserve_lifetime_soundness :
    (∀ (outerCtx innerCtx : List Outlives) (b : BinderImplied)
       (env : LifetimeEnv) (goal : Outlives),
        EnvSatisfies env outerCtx ->
        WfGuardedContext outerCtx b innerCtx ->
        Derives innerCtx goal ->
        SemOutlives env goal) ∧
    (∀ (innerCtx : List Outlives) (b : BinderImplied),
        WfGuardedContext [] b innerCtx ->
        ¬ Derives innerCtx ⟨.rParam 0, .rStatic⟩) := by
  have hSound :
      ∀ (outerCtx innerCtx : List Outlives) (b : BinderImplied)
        (env : LifetimeEnv) (goal : Outlives),
        EnvSatisfies env outerCtx ->
        WfGuardedContext outerCtx b innerCtx ->
        Derives innerCtx goal ->
        SemOutlives env goal := by
    intro outerCtx innerCtx b env goal hOuter hGuard hDer
    have hInnerSat : EnvSatisfies env innerCtx := by
      intro c hIn
      rcases hGuard c hIn with hInOuter | ⟨_, hDerOuter⟩
      · exact hOuter c hInOuter
      · exact derives_sound outerCtx env hOuter c hDerOuter
    exact derives_sound innerCtx env hInnerSat goal hDer
  refine ⟨hSound, ?_⟩
  intro innerCtx b hGuard hExtend
  have hOuterEmpty : EnvSatisfies shortLifetimeEnv [] := by
    intro c hMem
    cases hMem
  have hSem : SemOutlives shortLifetimeEnv ⟨.rParam 0, .rStatic⟩ :=
    hSound [] innerCtx b shortLifetimeEnv ⟨.rParam 0, .rStatic⟩ hOuterEmpty hGuard hExtend
  have hNot : ¬ (100 ≤ 1) := by decide
  exact hNot hSem

/-- Concrete `#25860` binder modeling `fn(&'static &'a (), &'a T) -> &'static T`:
    syntactic WF extraction of `&'static &'a ()` yields the unverified implied bound
    `'a : 'static`, i.e., `⟨.rParam 0, .rStatic⟩`. -/
def binder25860 : BinderImplied where
  impliedOutlives := [⟨.rParam 0, .rStatic⟩]

/-- Counterexample 3: Unconditionally admitting unverified binder implied bounds
    (as in `-Z assumptions-on-binders=yes`) derives `'a : 'static` from an empty
    outer context, violating `shortLifetimeEnv` (`1 < 100`, dangling reference / UAF). -/
theorem ce3_unwf_binder_assumption_derives_arbitrary_lifetime_extension_25860 :
    Derives (unwfBinderContext [] binder25860) ⟨.rParam 0, .rStatic⟩ ∧
    ¬ SemOutlives shortLifetimeEnv ⟨.rParam 0, .rStatic⟩ := by
  refine ⟨?_, ?_⟩
  · exact Derives.assume ⟨.rParam 0, .rStatic⟩ (List.Mem.head _)
  · intro hLe
    have hNot : ¬ (100 ≤ 1) := by decide
    exact hNot hLe

end PoloniusAndNextSolverCycleSoundness
