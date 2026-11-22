/-!
# Soundness & Completeness Formalization for `rustc_mir_transform`
  (`CtfeLimit`, `CheckForceInline`, `CrossCrateInline`, `RemoveUninitDrops`, `RemoveUnneededDrops`)

Target Toolchain: Lean v4.34.1 (zero `sorry`, zero `Classical.choice`, zero `omega`,
zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `_unsafe_rec`).

All three parts correspond directly to upstream `rust-lang/rust`
(`ce66487ebbd7541212d22d01c39a808057d69f1f` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
  - Part I:   `ctfe_limit.rs` (dominator back-edge omission on irreducible CFGs vs.
              DFS retreating-edge feedback-set completeness with `|V|` path-length bound).
  - Part II:  `check_inline.rs` (short-circuit definition-site rejection order) and
              `cross_crate_inline.rs` (12-stage priority lattice, version delta 1.98 vs HEAD,
              and `CostChecker` additivity, monotonicity, storage/nop invariance, and
              intrinsic-call exemption).
  - Part III: `remove_uninit_drops.rs` (`MaybeInitializedPlaces` recursive ADT/enum/tuple
              pruning soundness) and `remove_unneeded_drops.rs` (`!needs_drop` soundness).
-/

namespace RustcMirInlineCtfeDrop

-- ============================================================================
-- Helper Arithmetic & List Lemmas (no `omega`, no `Classical.choice`)
-- ============================================================================

section Helpers

theorem nat_lt_of_le_of_lt {a b c : Nat} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  Nat.lt_of_le_of_lt h1 h2

theorem nat_le_of_lt_succ {a b : Nat} (h : a < Nat.succ b) : a ≤ b :=
  Nat.le_of_lt_succ h

theorem nat_not_lt_zero (n : Nat) : ¬ (n < 0) :=
  Nat.not_lt_zero n

theorem nat_succ_le_of_lt {a b : Nat} (h : a < b) : Nat.succ a ≤ b :=
  h

theorem nat_lt_trans {a b c : Nat} (h1 : a < b) (h2 : b < c) : a < c :=
  Nat.lt_trans h1 h2

theorem nat_le_trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

theorem nat_add_le_add {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Nat.add_le_add h1 h2

theorem nat_add_eq_zero_iff {a b : Nat} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  Nat.add_eq_zero_iff

theorem nat_eq_zero_of_le_zero {a : Nat} (h : a ≤ 0) : a = 0 :=
  Nat.eq_zero_of_le_zero h

theorem nat_le_of_not_gt {a b : Nat} (h : ¬ (b < a)) : a ≤ b :=
  Nat.ge_of_not_lt h

theorem nat_not_le_of_gt {a b : Nat} (h : b < a) : ¬ (a ≤ b) :=
  Nat.not_le_of_gt h

theorem list_mem_append_left {α : Type} {x : α} {xs ys : List α} (h : x ∈ xs) :
    x ∈ xs ++ ys :=
  List.mem_append_left ys h

theorem list_mem_append_right {α : Type} {x : α} {xs ys : List α} (h : x ∈ ys) :
    x ∈ xs ++ ys :=
  List.mem_append_right xs h

theorem list_any_eq_false_iff {α : Type} {p : α → Bool} {xs : List α} :
    xs.any p = false ↔ ∀ x, x ∈ xs → p x = false := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; cases hx
    · intro _; rfl
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff]
    constructor
    · intro h x hx
      cases hx with
      | head => exact h.1
      | tail _ htl => exact ih.mp h.2 x htl
    · intro h
      refine ⟨h hd (List.Mem.head tl), ih.mpr (fun x hx => h x (List.Mem.tail hd hx))⟩

theorem list_any_eq_true_iff {α : Type} {p : α → Bool} {xs : List α} :
    xs.any p = true ↔ ∃ x, x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro ⟨x, hx, _⟩; cases hx
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_true]
    constructor
    · intro h
      cases h with
      | inl hhd => exact ⟨hd, List.Mem.head tl, hhd⟩
      | inr htl =>
        let ⟨x, hmem, hpx⟩ := ih.mp htl
        exact ⟨x, List.Mem.tail hd hmem, hpx⟩
    · intro ⟨x, hx, hpx⟩
      cases hx with
      | head => exact Or.inl hpx
      | tail _ htl => exact Or.inr (ih.mpr ⟨x, htl, hpx⟩)

end Helpers

-- ============================================================================
-- PART I: `CtfeLimit` — Dominator Back-Edge Omission vs. DFS Retreating Edges
-- ============================================================================

section CtfeLimit

/-- Terminator categories relevant to `CtfeLimit::run_pass` (`ctfe_limit.rs:23`). -/
inductive CtfeTermKind where
  | call
  | tailCall
  | goto
  | switchInt
  | ret
  | unreachable

def CtfeTermKind.isCallLike : CtfeTermKind → Bool
  | .call => true
  | .tailCall => true
  | .goto => false
  | .switchInt => false
  | .ret => false
  | .unreachable => false

/-- Finite MIR control-flow graph with entry block `0`. -/
structure MirCfg where
  numBlocks : Nat
  entryValid : 0 < numBlocks
  termKind : Nat → CtfeTermKind
  succs : Nat → List Nat
  succsValid : ∀ u v, u < numBlocks → v ∈ succs u → v < numBlocks

/-- Directed edge relation inside a `MirCfg`. -/
def CfgEdge (cfg : MirCfg) (u v : Nat) : Prop :=
  u < cfg.numBlocks ∧ v ∈ cfg.succs u

/-- Concrete directed path `p` from `u` to `v` (lists visited vertices including endpoints). -/
inductive CfgPath (cfg : MirCfg) : Nat → Nat → List Nat → Prop where
  | single {u : Nat} (hu : u < cfg.numBlocks) :
      CfgPath cfg u u [u]
  | step {u w v : Nat} {rest : List Nat}
      (hedge : CfgEdge cfg u w)
      (hpath : CfgPath cfg w v rest) :
      CfgPath cfg u v (u :: rest)

theorem cfgPath_nonempty {cfg : MirCfg} {u v : Nat} {p : List Nat}
    (hp : CfgPath cfg u v p) : 0 < p.length := by
  cases hp with
  | single _ => exact Nat.zero_lt_succ 0
  | step _ _ => exact Nat.zero_lt_succ _

theorem cfgPath_start_mem {cfg : MirCfg} {u v : Nat} {p : List Nat}
    (hp : CfgPath cfg u v p) : u ∈ p := by
  cases hp with
  | single _ => exact List.Mem.head []
  | step _ _ => exact List.Mem.head _

theorem cfgPath_end_mem {cfg : MirCfg} {u v : Nat} {p : List Nat}
    (hp : CfgPath cfg u v p) : v ∈ p := by
  induction hp with
  | single _ => exact List.Mem.head []
  | step _ _ ih => exact List.Mem.tail _ ih

theorem cfgPath_start_lt {cfg : MirCfg} {u v : Nat} {p : List Nat}
    (hp : CfgPath cfg u v p) : u < cfg.numBlocks := by
  cases hp with
  | single hu => exact hu
  | step hedge _ => exact hedge.1

theorem cfgPath_end_lt {cfg : MirCfg} {u v : Nat} {p : List Nat}
    (hp : CfgPath cfg u v p) : v < cfg.numBlocks := by
  induction hp with
  | single hu => exact hu
  | step _ _ ih => exact ih

/-- Reachability from entry block `0`. -/
def Reachable (cfg : MirCfg) (u : Nat) : Prop :=
  ∃ p, CfgPath cfg 0 u p

/-- Standard CFG dominance: `d` dominates `n` iff every path from entry `0` to `n` contains `d`. -/
def Dominates (cfg : MirCfg) (d n : Nat) : Prop :=
  ∀ p, CfgPath cfg 0 n p → d ∈ p

/-- Reflexivity of dominance on reachable blocks (`doms.dominates(n, n)`). -/
theorem dominates_refl (cfg : MirCfg) (n : Nat) : Dominates cfg n n :=
  fun _ hp => cfgPath_end_mem hp

/-- Entry block `0` dominates every block. -/
theorem dominates_entry (cfg : MirCfg) (n : Nat) : Dominates cfg 0 n :=
  fun _ hp => cfgPath_start_mem hp

/-- Upstream `CtfeLimit::has_back_edge` (`ctfe_limit.rs:48-58`):
    `doms.is_reachable(node) && node.successors().any(|succ| doms.dominates(succ, node))`. -/
def HasDomBackEdge (cfg : MirCfg) (u : Nat) : Prop :=
  Reachable cfg u ∧ ∃ s, s ∈ cfg.succs u ∧ Dominates cfg s u

/-- Upstream `CtfeLimit::run_pass` instrumentation predicate (`ctfe_limit.rs:23-26`). -/
def CtfeLimitMarks (cfg : MirCfg) (u : Nat) : Prop :=
  (cfg.termKind u).isCallLike = true ∨ HasDomBackEdge cfg u

-- ----------------------------------------------------------------------------
-- Concrete Witness 1: Non-collapsible 2-Header Irreducible CFG (`dialect="built"`)
--   bb0: SwitchInt -> [1, 2]
--   bb1: Goto      -> [2]
--   bb2: Goto      -> [1]
-- ----------------------------------------------------------------------------

def irrTermKind : Nat → CtfeTermKind
  | 0 => .switchInt
  | 1 => .goto
  | 2 => .goto
  | _ => .unreachable

def irrSuccs : Nat → List Nat
  | 0 => [1, 2]
  | 1 => [2]
  | 2 => [1]
  | _ => []

theorem irrSuccs_valid : ∀ u v, u < 3 → v ∈ irrSuccs u → v < 3 := by
  intro u v hu hv
  cases u with
  | zero =>
    simp only [irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
    cases hv with
    | inl h => subst h; decide
    | inr h => subst h; decide
  | succ u1 =>
    cases u1 with
    | zero =>
      simp only [irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv; decide
    | succ u2 =>
      cases u2 with
      | zero =>
        simp only [irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
        subst hv; decide
      | succ u3 =>
        have hlt : ¬ (Nat.succ (Nat.succ (Nat.succ u3)) < 3) := by
          intro h
          have h1 := Nat.lt_of_succ_lt_succ h
          have h2 := Nat.lt_of_succ_lt_succ h1
          have h3 := Nat.lt_of_succ_lt_succ h2
          exact Nat.not_lt_zero u3 h3
        exact False.elim (hlt hu)

def irreducibleTwoHeaderCfg : MirCfg where
  numBlocks := 3
  entryValid := by decide
  termKind := irrTermKind
  succs := irrSuccs
  succsValid := irrSuccs_valid

/-- Explicit witness path `[0, 1]` bypassing `2`. -/
theorem irr_path_0_1 : CfgPath irreducibleTwoHeaderCfg 0 1 [0, 1] :=
  CfgPath.step ⟨by decide, by decide⟩ (CfgPath.single (by decide))

/-- Explicit witness path `[0, 2]` bypassing `1`. -/
theorem irr_path_0_2 : CfgPath irreducibleTwoHeaderCfg 0 2 [0, 2] :=
  CfgPath.step ⟨by decide, by decide⟩ (CfgPath.single (by decide))

/-- Neither `bb2` dominates `bb1` nor `bb1` dominates `bb2`. -/
theorem irr_not_dom_2_1 : ¬ Dominates irreducibleTwoHeaderCfg 2 1 := by
  intro hdom
  have hmem : 2 ∈ [0, 1] := hdom [0, 1] irr_path_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  cases hmem with
  | inl h => cases h
  | inr h => cases h

theorem irr_not_dom_1_2 : ¬ Dominates irreducibleTwoHeaderCfg 1 2 := by
  intro hdom
  have hmem : 1 ∈ [0, 2] := hdom [0, 2] irr_path_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  cases hmem with
  | inl h => cases h
  | inr h => cases h

/-- Construct an arbitrarily long alternating cycle trace starting from `1` or `2`
    using `@Nat.rec` (zero `_unsafe_rec` / zero `partial`). -/
def irrCycleTrace (startAt1 : Bool) (k : Nat) : List Nat :=
  @Nat.rec (fun _ => Bool → List Nat)
    (fun b => if b then [1] else [2])
    (fun _ ih b => if b then 1 :: ih false else 2 :: ih true)
    k startAt1

def irrCycleEnd (startAt1 : Bool) (k : Nat) : Nat :=
  @Nat.rec (fun _ => Bool → Nat)
    (fun b => if b then 1 else 2)
    (fun _ ih b => ih (!b))
    k startAt1

theorem irrCycleTrace_length (startAt1 : Bool) (k : Nat) :
    (irrCycleTrace startAt1 k).length = k + 1 := by
  induction k generalizing startAt1 with
  | zero =>
    cases startAt1 <;> rfl
  | succ k ih =>
    cases startAt1 with
    | true =>
      change (1 :: irrCycleTrace false k).length = k + 1 + 1
      simp only [List.length_cons, ih false]
    | false =>
      change (2 :: irrCycleTrace true k).length = k + 1 + 1
      simp only [List.length_cons, ih true]

theorem irrCycleTrace_path (startAt1 : Bool) (k : Nat) :
    CfgPath irreducibleTwoHeaderCfg (if startAt1 then 1 else 2)
      (irrCycleEnd startAt1 k) (irrCycleTrace startAt1 k) := by
  induction k generalizing startAt1 with
  | zero =>
    cases startAt1 with
    | true => exact CfgPath.single (by decide)
    | false => exact CfgPath.single (by decide)
  | succ k ih =>
    cases startAt1 with
    | true =>
      exact CfgPath.step ⟨by decide, by decide⟩ (ih false)
    | false =>
      exact CfgPath.step ⟨by decide, by decide⟩ (ih true)

/-- **Core Counterexample Theorem (`ctfe_limit.rs:17-58`)**:
    On the non-collapsible 2-header irreducible CFG `irreducibleTwoHeaderCfg`:
    (1) Every block `0, 1, 2` is reachable from entry `0`.
    (2) `CtfeLimit` marks **ZERO** blocks (`∀ u, ¬ CtfeLimitMarks irreducibleTwoHeaderCfg u`).
    (3) For every `k : Nat`, there exists a valid execution path from entry `0` of length
        `k + 2` along which **zero** `ConstEvalCounter` blocks are visited (unbounded
        counter-free execution bypassing `#![deny(long_running_const_eval)]`). -/
theorem ctfeLimit_dominator_irreducible_counterexample :
    (Reachable irreducibleTwoHeaderCfg 0 ∧
     Reachable irreducibleTwoHeaderCfg 1 ∧
     Reachable irreducibleTwoHeaderCfg 2) ∧
    (∀ u, ¬ CtfeLimitMarks irreducibleTwoHeaderCfg u) ∧
    (∀ k : Nat, ∃ v p, CfgPath irreducibleTwoHeaderCfg 0 v p ∧
      p.length = k + 2 ∧ ∀ b, b ∈ p → ¬ CtfeLimitMarks irreducibleTwoHeaderCfg b) := by
  have hNoMark : ∀ u, ¬ CtfeLimitMarks irreducibleTwoHeaderCfg u := by
    intro u hmark
    cases hmark with
    | inl hcall =>
      cases u with
      | zero => cases hcall
      | succ u1 =>
        cases u1 with
        | zero => cases hcall
        | succ u2 =>
          cases u2 with
          | zero => cases hcall
          | succ _ => cases hcall
    | inr hback =>
      let ⟨_, s, hs, hdom⟩ := hback
      cases u with
      | zero =>
        simp only [irreducibleTwoHeaderCfg, irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hs
        cases hs with
        | inl h1 =>
          subst h1
          have hmem : 1 ∈ [0] := hdom [0] (CfgPath.single (by decide))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          cases hmem
        | inr h2 =>
          subst h2
          have hmem : 2 ∈ [0] := hdom [0] (CfgPath.single (by decide))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          cases hmem
      | succ u1 =>
        cases u1 with
        | zero =>
          simp only [irreducibleTwoHeaderCfg, irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hs
          subst hs
          exact irr_not_dom_2_1 hdom
        | succ u2 =>
          cases u2 with
          | zero =>
            simp only [irreducibleTwoHeaderCfg, irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hs
            subst hs
            exact irr_not_dom_1_2 hdom
          | succ _ =>
            simp only [irreducibleTwoHeaderCfg, irrSuccs, List.not_mem_nil] at hs
  refine ⟨⟨⟨[0], CfgPath.single (by decide)⟩, ⟨[0, 1], irr_path_0_1⟩, ⟨[0, 2], irr_path_0_2⟩⟩,
          hNoMark, ?_⟩
  intro k
  refine ⟨irrCycleEnd true k, 0 :: irrCycleTrace true k, ?_, ?_, ?_⟩
  · exact CfgPath.step ⟨by decide, by decide⟩ (irrCycleTrace_path true k)
  · simp only [List.length_cons, irrCycleTrace_length]
  · intro b _; exact hNoMark b

-- ----------------------------------------------------------------------------
-- Concrete Witness 2: Collapsed Self-Loop CFG after `SimplifyCfg::Initial`
--   bb0: Goto -> [1]
--   bb1: Goto -> [1]
-- ----------------------------------------------------------------------------

def collapsedSuccs : Nat → List Nat
  | 0 => [1]
  | 1 => [1]
  | _ => []

theorem collapsedSuccs_valid : ∀ u v, u < 2 → v ∈ collapsedSuccs u → v < 2 := by
  intro u v hu hv
  cases u with
  | zero =>
    simp only [collapsedSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv; decide
  | succ u1 =>
    cases u1 with
    | zero =>
      simp only [collapsedSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv; decide
    | succ u2 =>
      have hlt : ¬ (Nat.succ (Nat.succ u2) < 2) := by
        intro h
        exact Nat.not_lt_zero u2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
      exact False.elim (hlt hu)

def collapsedSelfLoopCfg : MirCfg where
  numBlocks := 2
  entryValid := by decide
  termKind := fun _ => .goto
  succs := collapsedSuccs
  succsValid := collapsedSuccs_valid

theorem collapsedSelfLoop_caught_by_ctfeLimit :
    CtfeLimitMarks collapsedSelfLoopCfg 1 := by
  apply Or.inr
  refine ⟨⟨[0, 1], CfgPath.step ⟨by decide, by decide⟩ (CfgPath.single (by decide))⟩,
          1, by decide, dominates_refl collapsedSelfLoopCfg 1⟩

-- ----------------------------------------------------------------------------
-- General Fix: DFS Retreating-Edge Feedback-Set Completeness (`≤ |V|`)
-- ----------------------------------------------------------------------------

/-- A valid DFS discovery/finish numbering over a `MirCfg`.
    By the DFS Parenthesis / White-Path Theorem, every graph edge `(u, v)` is either:
      - a **retreating (ancestor) edge** (`disc v ≤ disc u ∧ finish u ≤ finish v`), or
      - a **tree/forward/cross edge** strictly decreasing finish time (`finish v < finish u`).
    All finish times of valid vertices lie strictly below `cfg.numBlocks`. -/
structure ValidDfsNumbering (cfg : MirCfg) where
  disc : Nat → Nat
  finish : Nat → Nat
  finishBound : ∀ u, u < cfg.numBlocks → finish u < cfg.numBlocks
  edgeDichotomy : ∀ u v, CfgEdge cfg u v →
    (disc v ≤ disc u ∧ finish u ≤ finish v) ∨ finish v < finish u
  treePathAncestor : ∀ u, Reachable cfg u →
    ∃ p, CfgPath cfg 0 u p ∧ ∀ w, w ∈ p → disc w ≤ disc u ∧ finish u ≤ finish w

/-- An edge `(u, v)` is a DFS retreating edge iff `finish u ≤ finish v`. -/
def IsDfsRetreatingEdge (cfg : MirCfg) (dfs : ValidDfsNumbering cfg) (u v : Nat) : Prop :=
  CfgEdge cfg u v ∧ dfs.finish u ≤ dfs.finish v

/-- DFS retreating-edge block instrumentation predicate (replaces `has_back_edge`). -/
def DfsRetreatingMarks (cfg : MirCfg) (dfs : ValidDfsNumbering cfg) (u : Nat) : Prop :=
  (cfg.termKind u).isCallLike = true ∨ ∃ v, IsDfsRetreatingEdge cfg dfs u v

/-- Every non-retreating edge strictly decreases DFS finish time. -/
theorem finish_decreases_of_not_retreating {cfg : MirCfg} (dfs : ValidDfsNumbering cfg)
    {u v : Nat} (hedge : CfgEdge cfg u v)
    (hnot : ¬ IsDfsRetreatingEdge cfg dfs u v) :
    dfs.finish v < dfs.finish u := by
  cases dfs.edgeDichotomy u v hedge with
  | inl hret => exact False.elim (hnot ⟨hedge, hret.2⟩)
  | inr hdec => exact hdec

/-- A path is **counter-free** under DFS retreating-edge instrumentation if no edge
    on the path originates from a marked block (equivalently, no non-final vertex is marked). -/
inductive CounterFreePath (cfg : MirCfg) (dfs : ValidDfsNumbering cfg) :
    Nat → Nat → List Nat → Prop where
  | single {u : Nat} (hu : u < cfg.numBlocks) :
      CounterFreePath cfg dfs u u [u]
  | step {u w v : Nat} {rest : List Nat}
      (hedge : CfgEdge cfg u w)
      (hnotMarked : ¬ DfsRetreatingMarks cfg dfs u)
      (hrest : CounterFreePath cfg dfs w v rest) :
      CounterFreePath cfg dfs u v (u :: rest)

/-- Quantitative descent invariant: along any counter-free path `p` from `u` to `v`,
    `p.length ≤ dfs.finish u + 1`. -/
theorem counterFreePath_length_le_finish_succ {cfg : MirCfg} (dfs : ValidDfsNumbering cfg)
    {u v : Nat} {p : List Nat} (hp : CounterFreePath cfg dfs u v p) :
    p.length ≤ dfs.finish u + 1 := by
  induction hp with
  | single _ =>
    simp only [List.length_cons, List.length_nil]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | @step u w v rest hedge hnotMarked hrest ih =>
    have hnotRet : ¬ IsDfsRetreatingEdge cfg dfs u w := by
      intro hret
      exact hnotMarked (Or.inr ⟨w, hret⟩)
    have hdec : dfs.finish w < dfs.finish u :=
      finish_decreases_of_not_retreating dfs hedge hnotRet
    have hle : dfs.finish w + 1 ≤ dfs.finish u := hdec
    have h1 : rest.length ≤ dfs.finish u := nat_le_trans ih hle
    simp only [List.length_cons]
    exact Nat.succ_le_succ h1

/-- **Main Completeness Theorem (`dfsRetreatingEdge_bounds_counterFree_path_by_numBlocks`)**:
    For ANY finite CFG (reducible OR irreducible) and ANY valid DFS numbering,
    every counter-free execution path has vertex count `p.length ≤ cfg.numBlocks`
    (equivalently, at most `cfg.numBlocks - 1` transitions before executing a `ConstEvalCounter`). -/
theorem dfsRetreatingEdge_bounds_counterFree_path_by_numBlocks
    {cfg : MirCfg} (dfs : ValidDfsNumbering cfg)
    {u v : Nat} {p : List Nat}
    (hp : CounterFreePath cfg dfs u v p) :
    p.length ≤ cfg.numBlocks := by
  have hu : u < cfg.numBlocks := by
    cases hp with
    | single h => exact h
    | step hedge _ _ => exact hedge.1
  have hfin : dfs.finish u < cfg.numBlocks := dfs.finishBound u hu
  have hlen : p.length ≤ dfs.finish u + 1 := counterFreePath_length_le_finish_succ dfs hp
  exact nat_le_trans hlen hfin

/-- Corollary: No non-trivial cycle `(u ->+ u)` can be counter-free under DFS retreating-edge
    instrumentation (every cycle in ANY reducible or irreducible CFG contains a retreating edge). -/
theorem dfsRetreatingEdge_hits_every_cycle
    {cfg : MirCfg} (dfs : ValidDfsNumbering cfg)
    {u w : Nat} {rest : List Nat}
    (hedge : CfgEdge cfg u w)
    (hnotMarked : ¬ DfsRetreatingMarks cfg dfs u)
    (hrest : CounterFreePath cfg dfs w u rest) :
    False := by
  have hstrict : ∀ {a b : Nat} {q : List Nat},
      CounterFreePath cfg dfs a b q → dfs.finish b ≤ dfs.finish a := by
    intro a b q hq
    induction hq with
    | single _ => exact Nat.le_refl _
    | @step x y z r he hnm _ ihq =>
      have hdec := finish_decreases_of_not_retreating dfs he (fun hr => hnm (Or.inr ⟨y, hr⟩))
      exact nat_le_trans ihq (Nat.le_of_lt hdec)
  have h1 : dfs.finish w < dfs.finish u :=
    finish_decreases_of_not_retreating dfs hedge (fun hr => hnotMarked (Or.inr ⟨w, hr⟩))
  have h2 : dfs.finish u ≤ dfs.finish w := hstrict hrest
  exact nat_not_le_of_gt h1 h2

/-- Subsumption Theorem: Every dominator back-edge `(u, v)` on a reachable block `u`
    is automatically a DFS retreating edge (so DFS retreating-edge instrumentation
    strictly subsumes `CtfeLimit`'s dominator check on all CFGs). -/
theorem dominatorBackEdge_is_dfsRetreatingEdge
    {cfg : MirCfg} (dfs : ValidDfsNumbering cfg)
    {u v : Nat} (hreach : Reachable cfg u) (hedge : CfgEdge cfg u v)
    (hdom : Dominates cfg v u) :
    IsDfsRetreatingEdge cfg dfs u v := by
  let ⟨p, hp, hanc⟩ := dfs.treePathAncestor u hreach
  have hvmem : v ∈ p := hdom p hp
  have hvanc := hanc v hvmem
  exact ⟨hedge, hvanc.2⟩

/-- Concrete valid DFS numbering on `irreducibleTwoHeaderCfg`:
    DFS explores `0 -> 1 -> 2` (`disc`: `0 ↦ 0, 1 ↦ 1, 2 ↦ 2`; `finish`: `2 ↦ 0, 1 ↦ 1, 0 ↦ 2`).
    Edge `(2, 1)` satisfies `finish 2 = 0 ≤ 1 = finish 1`, so `bb2` is marked! -/
def irrDfsDisc : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def irrDfsFinish : Nat → Nat
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | _ => 0

def irrValidDfs : ValidDfsNumbering irreducibleTwoHeaderCfg where
  disc := irrDfsDisc
  finish := irrDfsFinish
  finishBound := by
    intro u hu
    cases u with
    | zero => decide
    | succ u1 =>
      cases u1 with
      | zero => decide
      | succ u2 =>
        cases u2 with
        | zero => decide
        | succ u3 =>
          have hlt : ¬ (Nat.succ (Nat.succ (Nat.succ u3)) < 3) := by
            intro h
            exact Nat.not_lt_zero u3 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)))
          exact False.elim (hlt hu)
  edgeDichotomy := by
    intro u v ⟨hu, hv⟩
    cases u with
    | zero =>
      simp only [irreducibleTwoHeaderCfg, irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
      cases hv with
      | inl h => subst h; exact Or.inr (by decide)
      | inr h => subst h; exact Or.inr (by decide)
    | succ u1 =>
      cases u1 with
      | zero =>
        simp only [irreducibleTwoHeaderCfg, irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
        subst hv; exact Or.inr (by decide)
      | succ u2 =>
        cases u2 with
        | zero =>
          simp only [irreducibleTwoHeaderCfg, irrSuccs, List.mem_cons, List.not_mem_nil, or_false] at hv
          subst hv; exact Or.inl ⟨by decide, by decide⟩
        | succ u3 =>
          simp only [irreducibleTwoHeaderCfg, irrSuccs, List.not_mem_nil] at hv
  treePathAncestor := by
    intro u hreach
    let ⟨p, hp⟩ := hreach
    have hu : u < 3 := cfgPath_end_lt hp
    cases u with
    | zero =>
      refine ⟨[0], CfgPath.single (by decide), ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; exact ⟨by decide, by decide⟩
    | succ u1 =>
      cases u1 with
      | zero =>
        refine ⟨[0, 1], irr_path_0_1, ?_⟩
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        cases hw with
        | inl h => subst h; exact ⟨by decide, by decide⟩
        | inr h => subst h; exact ⟨by decide, by decide⟩
      | succ u2 =>
        cases u2 with
        | zero =>
          refine ⟨[0, 1, 2], CfgPath.step ⟨by decide, by decide⟩
            (CfgPath.step ⟨by decide, by decide⟩ (CfgPath.single (by decide))), ?_⟩
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          cases hw with
          | inl h => subst h; exact ⟨by decide, by decide⟩
          | inr h1 =>
            cases h1 with
            | inl h => subst h; exact ⟨by decide, by decide⟩
            | inr h => subst h; exact ⟨by decide, by decide⟩
        | succ u3 =>
          have hlt : ¬ (Nat.succ (Nat.succ (Nat.succ u3)) < 3) := by
            intro h
            exact Nat.not_lt_zero u3 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)))
          exact False.elim (hlt hu)

/-- Strict separation witness: on `irreducibleTwoHeaderCfg`, `CtfeLimit` marks nothing,
    while DFS retreating-edge instrumentation marks `bb2` and bounds counter-free paths to `≤ 3`. -/
theorem irr_dfs_strict_separation :
    DfsRetreatingMarks irreducibleTwoHeaderCfg irrValidDfs 2 ∧
    ¬ CtfeLimitMarks irreducibleTwoHeaderCfg 2 ∧
    (∀ u v p, CounterFreePath irreducibleTwoHeaderCfg irrValidDfs u v p → p.length ≤ 3) := by
  refine ⟨Or.inr ⟨1, ⟨by decide, by decide⟩, by decide⟩,
          ctfeLimit_dominator_irreducible_counterexample.2.1 2,
          fun _ _ _ hp => dfsRetreatingEdge_bounds_counterFree_path_by_numBlocks irrValidDfs hp⟩

end CtfeLimit

-- ============================================================================
-- PART II: `CheckForceInline` Rejection Matrix & `CrossCrateInline` Lattice/Cost
-- ============================================================================

section InlineChecks

/-- `rustc_attr_ir::InlineAttr` (`check_inline.rs`, `cross_crate_inline.rs`). -/
inductive InlineAttr where
  | none
  | hint
  | always
  | never
  | force

/-- Exact rejection reasons emitted by `CheckForceInline` (`check_inline.rs:44-82`). -/
inductive ForceInlineErr where
  | noMirInline
  | cVariadic
  | cold
  | bodylessIntrinsic
  | hasTailCalls

/-- Function-level attributes inspected by `is_inline_valid_on_fn` (`check_inline.rs:38-70`). -/
structure ForceInlineFnInfo where
  isFnOrClosure : Bool
  isLocal : Bool
  inlineAttr : InlineAttr
  hasRustcNoMirInline : Bool
  isCVariadic : Bool
  isCold : Bool
  isBodylessIntrinsic : Bool

/-- Body-level summary inspected by `is_inline_valid_on_body` (`check_inline.rs:72-85`). -/
structure ForceInlineBodyInfo where
  hasTailCallTerminator : Bool

def isInlineValidOnFn (info : ForceInlineFnInfo) : Option ForceInlineErr :=
  if info.hasRustcNoMirInline then some .noMirInline
  else if info.isCVariadic then some .cVariadic
  else if info.isCold then some .cold
  else if info.isBodylessIntrinsic then some .bodylessIntrinsic
  else none

def isInlineValidOnBody (body : ForceInlineBodyInfo) : Option ForceInlineErr :=
  if body.hasTailCallTerminator then some .hasTailCalls
  else none

/-- Exact `CheckForceInline::run_lint` (`check_inline.rs:16-35`). -/
def checkForceInline (info : ForceInlineFnInfo) (body : ForceInlineBodyInfo) :
    Option ForceInlineErr :=
  if !info.isFnOrClosure || !info.isLocal then none
  else match info.inlineAttr with
    | .force =>
      match isInlineValidOnFn info with
      | some err => some err
      | none => isInlineValidOnBody body
    | _ => none

theorem checkForceInline_ok_iff (info : ForceInlineFnInfo) (body : ForceInlineBodyInfo)
    (hfn : info.isFnOrClosure = true) (hloc : info.isLocal = true)
    (hforce : info.inlineAttr = .force) :
    checkForceInline info body = none ↔
      info.hasRustcNoMirInline = false ∧
      info.isCVariadic = false ∧
      info.isCold = false ∧
      info.isBodylessIntrinsic = false ∧
      body.hasTailCallTerminator = false := by
  simp only [checkForceInline, isInlineValidOnFn, isInlineValidOnBody, hfn, hloc, hforce]
  cases info.hasRustcNoMirInline <;>
  cases info.isCVariadic <;>
  cases info.isCold <;>
  cases info.isBodylessIntrinsic <;>
  cases body.hasTailCallTerminator <;>
  simp

theorem checkForceInline_short_circuit_priority
    (info : ForceInlineFnInfo) (body : ForceInlineBodyInfo)
    (hfn : info.isFnOrClosure = true) (hloc : info.isLocal = true)
    (hforce : info.inlineAttr = .force) :
    (info.hasRustcNoMirInline = true → checkForceInline info body = some .noMirInline) ∧
    (info.hasRustcNoMirInline = false → info.isCVariadic = true →
      checkForceInline info body = some .cVariadic) ∧
    (info.hasRustcNoMirInline = false → info.isCVariadic = false → info.isCold = true →
      checkForceInline info body = some .cold) ∧
    (info.hasRustcNoMirInline = false → info.isCVariadic = false → info.isCold = false →
      info.isBodylessIntrinsic = true → checkForceInline info body = some .bodylessIntrinsic) ∧
    (info.hasRustcNoMirInline = false → info.isCVariadic = false → info.isCold = false →
      info.isBodylessIntrinsic = false → body.hasTailCallTerminator = true →
      checkForceInline info body = some .hasTailCalls) := by
  simp only [checkForceInline, isInlineValidOnFn, isInlineValidOnBody, hfn, hloc, hforce]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1; simp [h1]
  · intro h1 h2; simp [h1, h2]
  · intro h1 h2 h3; simp [h1, h2, h3]
  · intro h1 h2 h3 h4; simp [h1, h2, h3, h4]
  · intro h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]

-- ----------------------------------------------------------------------------
-- `CrossCrateInline` (`cross_crate_inline.rs:18-202`) & `CostChecker`
-- ----------------------------------------------------------------------------

inductive CrossDefKind where
  | ctor
  | closure
  | syntheticCoroutineBody
  | fn_
  | assocFn
  | other

inductive InliningThreshold where
  | never
  | sometimes (limit : Nat)
  | always

/-- Ordering on `InliningThreshold`: `never ≤ sometimes m ≤ sometimes n ≤ always` for `m ≤ n`. -/
def ThresholdLe : InliningThreshold → InliningThreshold → Prop
  | .never, _ => True
  | .sometimes _, .always => True
  | .sometimes m, .sometimes n => m ≤ n
  | .always, .always => True
  | _, _ => False

/-- MIR statement kinds classified by `CostChecker::visit_statement` (`cross_crate_inline.rs:138-144`). -/
inductive CostStmt where
  | storageLive
  | storageDead
  | nop
  | other

/-- MIR terminator kinds classified by `CostChecker::visit_terminator` (`cross_crate_inline.rs:146-201`). -/
inductive CostTerm where
  | drop (isTriviallyPureCloneCopy : Bool) (hasCleanup : Bool)
  | call (isRustcIntrinsic : Bool) (hasCleanup : Bool)
  | tailCall
  | assert_ (hasCleanup : Bool)
  | unwindResume
  | inlineAsm (hasCleanup : Bool)
  | controlOnly

structure CostBlock where
  stmts : List CostStmt
  term : CostTerm

structure CostState where
  calls : Nat
  statements : Nat
  landingPads : Nat
  resumes : Nat

def CostState.zero : CostState := ⟨0, 0, 0, 0⟩

def CostState.add (a b : CostState) : CostState :=
  ⟨a.calls + b.calls,
   a.statements + b.statements,
   a.landingPads + b.landingPads,
   a.resumes + b.resumes⟩

def CostState.le (a b : CostState) : Prop :=
  a.calls ≤ b.calls ∧
  a.statements ≤ b.statements ∧
  a.landingPads ≤ b.landingPads ∧
  a.resumes ≤ b.resumes

theorem costState_add_zero_left (s : CostState) : CostState.add CostState.zero s = s := by
  cases s; simp [CostState.add, CostState.zero]

theorem costState_add_zero_right (s : CostState) : CostState.add s CostState.zero = s := by
  cases s; simp [CostState.add, CostState.zero]

theorem costState_add_assoc (a b c : CostState) :
    CostState.add (CostState.add a b) c = CostState.add a (CostState.add b c) := by
  cases a; cases b; cases c
  simp [CostState.add, Nat.add_assoc]

def stmtCost : CostStmt → CostState
  | .storageLive => CostState.zero
  | .storageDead => CostState.zero
  | .nop => CostState.zero
  | .other => ⟨0, 1, 0, 0⟩

/-- Exact terminator accounting in `CostChecker::visit_terminator` (`cross_crate_inline.rs:146-200`).
    Note: `statements` ALWAYS increments by `1` at line 147 before matching on `terminator.kind`,
    even for exempted `#[rustc_intrinsic]` calls and `controlOnly` terminators. -/
def termCost : CostTerm → CostState
  | .drop true _ => ⟨0, 1, 0, 0⟩
  | .drop false false => ⟨1, 1, 0, 0⟩
  | .drop false true => ⟨1, 1, 1, 0⟩
  | .call true _ => ⟨0, 1, 0, 0⟩
  | .call false false => ⟨1, 1, 0, 0⟩
  | .call false true => ⟨1, 1, 1, 0⟩
  | .tailCall => ⟨1, 1, 0, 0⟩
  | .assert_ false => ⟨0, 1, 0, 0⟩
  | .assert_ true => ⟨0, 1, 1, 0⟩
  | .unwindResume => ⟨0, 1, 0, 1⟩
  | .inlineAsm false => ⟨0, 1, 0, 0⟩
  | .inlineAsm true => ⟨0, 1, 1, 0⟩
  | .controlOnly => ⟨0, 1, 0, 0⟩

def visitStmts (acc : CostState) (xs : List CostStmt) : CostState :=
  xs.foldl (fun a s => CostState.add a (stmtCost s)) acc

def visitBlock (acc : CostState) (blk : CostBlock) : CostState :=
  CostState.add (visitStmts acc blk.stmts) (termCost blk.term)

def visitBody (acc : CostState) (blks : List CostBlock) : CostState :=
  blks.foldl visitBlock acc

def checkBodyCost (blocks : List CostBlock) : CostState :=
  visitBody CostState.zero blocks

/-- `CostChecker` acceptance predicate (`cross_crate_inline.rs:113-116`). -/
def costAccepts (blocks : List CostBlock) (threshold : Nat) : Bool :=
  let c := checkBodyCost blocks
  Nat.beq c.calls 0 &&
  Nat.beq c.resumes 0 &&
  Nat.beq c.landingPads 0 &&
  Nat.ble c.statements threshold

theorem visitStmts_shift (acc : CostState) (xs : List CostStmt) :
    visitStmts acc xs = CostState.add acc (visitStmts CostState.zero xs) := by
  induction xs generalizing acc with
  | nil =>
    simp [visitStmts, costState_add_zero_right]
  | cons s rest ih =>
    simp only [visitStmts, List.foldl_cons]
    change visitStmts (CostState.add acc (stmtCost s)) rest =
      CostState.add acc (visitStmts (CostState.add CostState.zero (stmtCost s)) rest)
    rw [ih (CostState.add acc (stmtCost s))]
    rw [ih (CostState.add CostState.zero (stmtCost s))]
    rw [costState_add_zero_left]
    rw [costState_add_assoc]

theorem visitBlock_shift (acc : CostState) (blk : CostBlock) :
    visitBlock acc blk = CostState.add acc (visitBlock CostState.zero blk) := by
  simp only [visitBlock]
  rw [visitStmts_shift acc blk.stmts]
  rw [costState_add_assoc]

theorem visitBody_shift (acc : CostState) (blks : List CostBlock) :
    visitBody acc blks = CostState.add acc (visitBody CostState.zero blks) := by
  induction blks generalizing acc with
  | nil =>
    simp [visitBody, costState_add_zero_right]
  | cons b rest ih =>
    simp only [visitBody, List.foldl_cons]
    change visitBody (visitBlock acc b) rest =
      CostState.add acc (visitBody (visitBlock CostState.zero b) rest)
    rw [ih (visitBlock acc b)]
    rw [ih (visitBlock CostState.zero b)]
    rw [visitBlock_shift acc b]
    rw [costState_add_assoc]

/-- `CostChecker` is strictly additive across block list concatenation. -/
theorem checkBodyCost_append (b1 b2 : List CostBlock) :
    checkBodyCost (b1 ++ b2) = CostState.add (checkBodyCost b1) (checkBodyCost b2) := by
  simp only [checkBodyCost, visitBody, List.foldl_append]
  exact visitBody_shift (visitBody CostState.zero b1) b2

/-- `CostChecker` is monotone under appending blocks: adding blocks can never decrease any counter. -/
theorem checkBodyCost_mono_append (b1 b2 : List CostBlock) :
    CostState.le (checkBodyCost b1) (checkBodyCost (b1 ++ b2)) := by
  rw [checkBodyCost_append]
  simp only [CostState.le, CostState.add]
  exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Filtering out `StorageLive`, `StorageDead`, and `Nop` via `List.foldr` (zero `_unsafe_rec`). -/
def stripIgnoredStmts (xs : List CostStmt) : List CostStmt :=
  xs.foldr (fun s rest => match s with
    | .other => .other :: rest
    | _ => rest) []

theorem visitStmts_stripIgnored (acc : CostState) (xs : List CostStmt) :
    visitStmts acc (stripIgnoredStmts xs) = visitStmts acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | storageLive =>
      change visitStmts acc (stripIgnoredStmts rest) =
        visitStmts (CostState.add acc (stmtCost .storageLive)) rest
      simp only [stmtCost, costState_add_zero_right]
      exact ih acc
    | storageDead =>
      change visitStmts acc (stripIgnoredStmts rest) =
        visitStmts (CostState.add acc (stmtCost .storageDead)) rest
      simp only [stmtCost, costState_add_zero_right]
      exact ih acc
    | nop =>
      change visitStmts acc (stripIgnoredStmts rest) =
        visitStmts (CostState.add acc (stmtCost .nop)) rest
      simp only [stmtCost, costState_add_zero_right]
      exact ih acc
    | other =>
      change visitStmts (CostState.add acc (stmtCost .other)) (stripIgnoredStmts rest) =
        visitStmts (CostState.add acc (stmtCost .other)) rest
      exact ih (CostState.add acc (stmtCost .other))

/-- `StorageLive`/`StorageDead`/`Nop` invariance across an entire MIR body. -/
theorem checkBodyCost_stripIgnored (blks : List CostBlock) :
    checkBodyCost (blks.map (fun b => ⟨stripIgnoredStmts b.stmts, b.term⟩)) =
    checkBodyCost blks := by
  have h : ∀ acc,
      visitBody acc (blks.map (fun b => ⟨stripIgnoredStmts b.stmts, b.term⟩)) =
      visitBody acc blks := by
    induction blks with
    | nil => intro acc; rfl
    | cons b rest ih =>
      intro acc
      simp only [List.map_cons, visitBody, List.foldl_cons, visitBlock]
      rw [visitStmts_stripIgnored]
      exact ih _
  exact h CostState.zero

theorem visitStmts_calls_zero (stmts : List CostStmt) :
    ∀ acc, acc.calls = 0 → (visitStmts acc stmts).calls = 0 := by
  induction stmts with
  | nil => intro acc h; exact h
  | cons s rest ih =>
    intro acc h
    cases s <;> (
      change (visitStmts (CostState.add acc (stmtCost _)) rest).calls = 0
      apply ih
      simp [stmtCost, CostState.add, CostState.zero, h])

theorem visitStmts_landingPads_zero (stmts : List CostStmt) :
    ∀ acc, acc.landingPads = 0 → (visitStmts acc stmts).landingPads = 0 := by
  induction stmts with
  | nil => intro acc h; exact h
  | cons s rest ih =>
    intro acc h
    cases s <;> (
      change (visitStmts (CostState.add acc (stmtCost _)) rest).landingPads = 0
      apply ih
      simp [stmtCost, CostState.add, CostState.zero, h])

/-- `CostChecker` intrinsic-call exemption vs. ordinary call and `Drop` accounting. -/
theorem costChecker_intrinsic_and_drop_separation (stmts : List CostStmt) (hc : Bool) :
    (checkBodyCost [⟨stmts, .call true hc⟩]).calls = 0 ∧
    (checkBodyCost [⟨stmts, .call true hc⟩]).landingPads = 0 ∧
    (checkBodyCost [⟨stmts, .call true hc⟩]).statements =
      (checkBodyCost [⟨stmts, .call false hc⟩]).statements ∧
    (checkBodyCost [⟨stmts, .call false hc⟩]).calls = 1 ∧
    (checkBodyCost [⟨stmts, .drop true hc⟩]).calls = 0 ∧
    (checkBodyCost [⟨stmts, .drop false hc⟩]).calls = 1 := by
  have hst : ∀ t, checkBodyCost [⟨stmts, t⟩] =
      CostState.add (visitStmts CostState.zero stmts) (termCost t) := by
    intro t; rfl
  have hc0 : (visitStmts CostState.zero stmts).calls = 0 :=
    visitStmts_calls_zero stmts CostState.zero rfl
  have hlp0 : (visitStmts CostState.zero stmts).landingPads = 0 :=
    visitStmts_landingPads_zero stmts CostState.zero rfl
  rw [hst, hst, hst, hst]
  cases hc <;> simp [termCost, CostState.add, hc0, hlp0]

/-- Complete input record for `cross_crate_inlinable` (`cross_crate_inline.rs:18-117`). -/
structure CrossCrateInput where
  hasExternIndicator : Bool
  defKind : CrossDefKind
  threshold : InliningThreshold
  isRustcIntrinsic : Bool
  isAlwaysConst : Bool
  inlineAttr : InlineAttr
  hintMostlyUnused : Bool
  targetHasReliableF16 : Bool
  targetHasReliableF128 : Bool
  sigHasF16 : Bool
  sigHasF128 : Bool
  incremental : Bool
  optLevelNo : Bool
  inlinerWillRun : Bool
  mirAvailable : Bool
  body : List CostBlock

/-- Exact HEAD (`ce66487eb`) `cross_crate_inlinable` decision function (`cross_crate_inline.rs:18-117`). -/
def crossCrateInlinableHead (inp : CrossCrateInput) : Bool :=
  if inp.hasExternIndicator then false
  else match inp.defKind with
    | .ctor | .closure | .syntheticCoroutineBody => true
    | .other => false
    | .fn_ | .assocFn =>
      match inp.threshold with
      | .always => true
      | _ =>
        if inp.isRustcIntrinsic then true
        else if inp.isAlwaysConst then false
        else match inp.inlineAttr with
          | .never => false
          | .hint | .always | .force => true
          | .none =>
            if inp.hintMostlyUnused then true
            else if (!inp.targetHasReliableF16 && inp.sigHasF16) ||
                    (!inp.targetHasReliableF128 && inp.sigHasF128) then true
            else if inp.incremental then false
            else if inp.optLevelNo && !inp.inlinerWillRun then false
            else if !inp.mirAvailable then false
            else match inp.threshold with
              | .always => true
              | .never => false
              | .sometimes limit => costAccepts inp.body limit

/-- Exact `rustc 1.98.0-nightly` (`14210df0e`) `cross_crate_inlinable` decision function:
    no `Constness::Const { always: true }` gate and unconditional `f16`/`f128` bypass. -/
def crossCrateInlinable198 (inp : CrossCrateInput) : Bool :=
  if inp.hasExternIndicator then false
  else match inp.defKind with
    | .ctor | .closure | .syntheticCoroutineBody => true
    | .other => false
    | .fn_ | .assocFn =>
      match inp.threshold with
      | .always => true
      | _ =>
        if inp.isRustcIntrinsic then true
        else match inp.inlineAttr with
          | .never => false
          | .hint | .always | .force => true
          | .none =>
            if inp.hintMostlyUnused then true
            else if inp.sigHasF16 || inp.sigHasF128 then true
            else if inp.incremental then false
            else if inp.optLevelNo && !inp.inlinerWillRun then false
            else if !inp.mirAvailable then false
            else match inp.threshold with
              | .always => true
              | .never => false
              | .sometimes limit => costAccepts inp.body limit

/-- `costAccepts` is monotone in the statement threshold. -/
theorem costAccepts_mono {blks : List CostBlock} {t1 t2 : Nat}
    (hle : t1 ≤ t2) (hacc : costAccepts blks t1 = true) :
    costAccepts blks t2 = true := by
  simp only [costAccepts, Bool.and_eq_true, Nat.ble_eq] at hacc ⊢
  exact ⟨hacc.1, nat_le_trans hacc.2 hle⟩

/-- **Main `CrossCrateInline` Theorem (`crossCrateInline_priority_and_cost_soundness`)**:
    Establishes all key lattice priorities, threshold monotonicity, and `CostChecker` invariants
    on `crossCrateInlinableHead` (and the exact version delta from `crossCrateInlinable198`). -/
theorem crossCrateInline_priority_and_cost_soundness (inp : CrossCrateInput) :
    -- (1) Extern indicator (`#[no_mangle]`/`#[export_name]`) strictly dominates EVERYTHING.
    (inp.hasExternIndicator = true → crossCrateInlinableHead inp = false) ∧
    -- (2) `#[inline(never)]` strictly beats `hint_mostly_unused` and `f16`/`f128` bypass
    --     (for non-extern, non-always-threshold, non-intrinsic, non-always-const `Fn`/`AssocFn`).
    (inp.hasExternIndicator = false → inp.defKind = .fn_ →
      inp.threshold ≠ .always → inp.isRustcIntrinsic = false →
      inp.isAlwaysConst = false → inp.inlineAttr = .never →
      crossCrateInlinableHead inp = false) ∧
    -- (3) `f16` bypass (when target lacks `target_has_reliable_f16`) strictly beats
    --     `incremental = true` and `threshold = .never` (for unannotated non-always-const `Fn`).
    (inp.hasExternIndicator = false → inp.defKind = .fn_ →
      inp.isAlwaysConst = false → inp.inlineAttr = .none →
      inp.targetHasReliableF16 = false → inp.sigHasF16 = true →
      crossCrateInlinableHead inp = true) ∧
    -- (4) Threshold monotonicity: increasing `threshold` never flips `true` to `false`.
    (∀ t2, ThresholdLe inp.threshold t2 →
      crossCrateInlinableHead inp = true →
      crossCrateInlinableHead { inp with threshold := t2 } = true) ∧
    -- (5) Storage/Nop invariance: stripping `StorageLive`/`StorageDead`/`Nop` preserves decision.
    (crossCrateInlinableHead
      { inp with body := inp.body.map (fun b => ⟨stripIgnoredStmts b.stmts, b.term⟩) } =
      crossCrateInlinableHead inp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hext; simp [crossCrateInlinableHead, hext]
  · intro hext hdk hnotA hintr hconst hnev
    cases hth : inp.threshold with
    | always => exact False.elim (hnotA hth)
    | never => simp [crossCrateInlinableHead, hext, hdk, hth, hintr, hconst, hnev]
    | sometimes _ => simp [crossCrateInlinableHead, hext, hdk, hth, hintr, hconst, hnev]
  · intro hext hdk hconst hnone hrel hf16
    cases hth : inp.threshold with
    | always => simp [crossCrateInlinableHead, hext, hdk, hth]
    | never =>
      cases hintr : inp.isRustcIntrinsic <;>
      cases hmu : inp.hintMostlyUnused <;>
      simp [crossCrateInlinableHead, hext, hdk, hth, hintr, hconst, hnone, hmu, hrel, hf16]
    | sometimes _ =>
      cases hintr : inp.isRustcIntrinsic <;>
      cases hmu : inp.hintMostlyUnused <;>
      simp [crossCrateInlinableHead, hext, hdk, hth, hintr, hconst, hnone, hmu, hrel, hf16]
  · intro t2 htle htrue
    cases inp with
    | mk ext dk th intr aconst iattr hmu rf16 rf128 sf16 sf128 inc optno inl mirav bdy =>
      cases ext with
      | true => simp [crossCrateInlinableHead] at htrue
      | false =>
        cases dk with
        | ctor => rfl
        | closure => rfl
        | syntheticCoroutineBody => rfl
        | other => simp [crossCrateInlinableHead] at htrue
        | fn_ | assocFn =>
          cases th with
          | always =>
            cases t2 with
            | always => rfl
            | never => cases htle
            | sometimes _ => cases htle
          | never =>
            cases t2 with
            | always => rfl
            | never => exact htrue
            | sometimes _ =>
              simp only [crossCrateInlinableHead] at htrue ⊢
              cases intr <;> simp at htrue ⊢
              cases aconst <;> simp at htrue ⊢
              cases iattr <;> simp at htrue ⊢
              cases hmu <;> simp at htrue ⊢
              cases rf16 <;> cases sf16 <;> cases rf128 <;> cases sf128 <;> simp at htrue ⊢
              all_goals (
                cases inc <;> simp at htrue ⊢
                cases optno <;> cases inl <;> simp at htrue ⊢
                all_goals (cases mirav <;> simp at htrue ⊢))
          | sometimes m =>
            cases t2 with
            | always => rfl
            | never => cases htle
            | sometimes n =>
              simp only [crossCrateInlinableHead] at htrue ⊢
              cases intr <;> simp at htrue ⊢
              cases aconst <;> simp at htrue ⊢
              cases iattr <;> simp at htrue ⊢
              cases hmu <;> simp at htrue ⊢
              cases rf16 <;> cases sf16 <;> cases rf128 <;> cases sf128 <;> simp at htrue ⊢
              all_goals (
                cases inc <;> simp at htrue ⊢
                cases optno <;> cases inl <;> simp at htrue ⊢
                all_goals (cases mirav <;> simp at htrue ⊢; exact costAccepts_mono htle htrue))
  · cases hext : inp.hasExternIndicator <;>
    cases hdk : inp.defKind <;>
    cases ht : inp.threshold <;>
    simp only [crossCrateInlinableHead, hext, hdk, ht, costAccepts, checkBodyCost_stripIgnored]

/-- Exact 1.98-nightly (`14210df0e`) vs HEAD (`ce66487eb`) divergence theorem:
    On a target with `target_has_reliable_f16` enabled and incremental compilation enabled,
    a non-inlined `fn(f16) -> f16` returns `true` under 1.98 and `false` under HEAD. -/
theorem crossCrateInline_version_delta_reliable_f16 :
    ∃ inp : CrossCrateInput,
      crossCrateInlinable198 inp = true ∧ crossCrateInlinableHead inp = false := by
  refine ⟨{
    hasExternIndicator := false
    defKind := .fn_
    threshold := .sometimes 100
    isRustcIntrinsic := false
    isAlwaysConst := false
    inlineAttr := .none
    hintMostlyUnused := false
    targetHasReliableF16 := true
    targetHasReliableF128 := true
    sigHasF16 := true
    sigHasF128 := false
    incremental := true
    optLevelNo := false
    inlinerWillRun := true
    mirAvailable := true
    body := []
  }, rfl, rfl⟩

/-- Exact 1.98-nightly vs HEAD divergence for `Constness::Const { always: true }` (comptime fn). -/
theorem crossCrateInline_version_delta_always_const :
    ∃ inp : CrossCrateInput,
      crossCrateInlinable198 inp = true ∧ crossCrateInlinableHead inp = false := by
  refine ⟨{
    hasExternIndicator := false
    defKind := .fn_
    threshold := .sometimes 100
    isRustcIntrinsic := false
    isAlwaysConst := true
    inlineAttr := .always
    hintMostlyUnused := false
    targetHasReliableF16 := true
    targetHasReliableF128 := true
    sigHasF16 := false
    sigHasF128 := false
    incremental := false
    optLevelNo := false
    inlinerWillRun := true
    mirAvailable := true
    body := []
  }, rfl, rfl⟩

end InlineChecks

-- ============================================================================
-- PART III: `RemoveUninitDrops` & `RemoveUnneededDrops` Semantic Preservation
-- ============================================================================

section DropPruning

/-- Path steps inside a local's `MoveData` projection tree (`remove_uninit_drops.rs:88-145`). -/
inductive ProjStep where
  | downcast (variantIdx : Nat)
  | field (fieldIdx : Nat)

abbrev MovePath := List ProjStep

/-- Type shapes relevant to `is_needs_drop_and_init` (`remove_uninit_drops.rs:75-160`).
    No `deriving` clauses on recursive inductives (zero `_unsafe_rec`). -/
inductive DropTy where
  | leaf (hasDrop : Bool) (dtorId : Nat)
  | union_
  | manuallyDrop (inner : DropTy)
  | adtWithDtor (dtorId : Nat) (fields : List DropTy)
  | struct_ (fields : List DropTy)
  | enum_ (variants : List (List DropTy))
  | tuple (fields : List DropTy)

/-- Exact static `Ty::needs_drop` predicate over `DropTy` (`noncomputable` avoids
    Lean 4.34's `partial` `._unsafe_rec` VM helper, matching `Trusted.MirSemantics`). -/
noncomputable def tyNeedsDrop : DropTy → Bool
  | .leaf hasDrop _ => hasDrop
  | .union_ => false
  | .manuallyDrop _ => false
  | .adtWithDtor _ _ => true
  | .struct_ fs => listTyNeedsDrop fs
  | .enum_ vs => variantsTyNeedsDrop vs
  | .tuple fs => listTyNeedsDrop fs
where
  listTyNeedsDrop : List DropTy → Bool
    | [] => false
    | t :: ts => tyNeedsDrop t || listTyNeedsDrop ts
  variantsTyNeedsDrop : List (List DropTy) → Bool
    | [] => false
    | v :: vs => listTyNeedsDrop v || variantsTyNeedsDrop vs

/-- Concrete runtime value / initialization tree for a place of type `DropTy`.
    Matches `r[destructors.intro]` and `r[destructors.operation]`:
    uninitialized places or moved-out fields execute zero destructors. -/
inductive InitVal where
  | uninit
  | initLeaf
  | initFields (fields : List InitVal)
  | initEnum (activeVariant : Nat) (fields : List InitVal)

/-- Helper indexing into a `List` without partiality or `_unsafe_rec`. -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGet? xs n

/-- Operational drop trace: exact ordered list of custom destructor IDs executed when
    dropping runtime value `iv` at type `ty` (`r[destructors.operation]`). -/
noncomputable def execDrop : DropTy → InitVal → List Nat
  | _, .uninit => []
  | .leaf true id, .initLeaf => [id]
  | .leaf false _, _ => []
  | .leaf true _, _ => []
  | .union_, _ => []
  | .manuallyDrop _, _ => []
  | .adtWithDtor id fs, .initFields vs => id :: execDropFields fs vs
  | .adtWithDtor id _, _ => [id]
  | .struct_ fs, .initFields vs => execDropFields fs vs
  | .struct_ _, _ => []
  | .tuple fs, .initFields vs => execDropFields fs vs
  | .tuple _, _ => []
  | .enum_ variants, .initEnum vid vs =>
      match listGet? variants vid with
      | some fs => execDropFields fs vs
      | none => []
  | .enum_ _, _ => []
where
  execDropFields : List DropTy → List InitVal → List Nat
    | [], _ => []
    | _, [] => []
    | t :: ts, v :: vs => execDrop t v ++ execDropFields ts vs

mutual
/-- Fundamental `RemoveUnneededDrops` theorem:
    If `tyNeedsDrop ty = false`, then `execDrop ty iv = []` for EVERY runtime value `iv`! -/
theorem execDrop_eq_nil_of_not_needsDrop (ty : DropTy) (iv : InitVal)
    (h : tyNeedsDrop ty = false) : execDrop ty iv = [] :=
  match ty, iv with
  | _, .uninit => by simp [execDrop]
  | .leaf false _, .initLeaf => by simp [execDrop]
  | .leaf false _, .initFields _ => by simp [execDrop]
  | .leaf false _, .initEnum _ _ => by simp [execDrop]
  | .leaf true _, _ => by cases h
  | .union_, .initLeaf => by simp [execDrop]
  | .union_, .initFields _ => by simp [execDrop]
  | .union_, .initEnum _ _ => by simp [execDrop]
  | .manuallyDrop _, .initLeaf => by simp [execDrop]
  | .manuallyDrop _, .initFields _ => by simp [execDrop]
  | .manuallyDrop _, .initEnum _ _ => by simp [execDrop]
  | .adtWithDtor _ _, _ => by cases h
  | .struct_ fs, .initFields vs => by
    simp only [execDrop]
    exact execDropFields_eq_nil_of_not_needsDrop fs vs h
  | .struct_ _, .initLeaf => by simp [execDrop]
  | .struct_ _, .initEnum _ _ => by simp [execDrop]
  | .tuple fs, .initFields vs => by
    simp only [execDrop]
    exact execDropFields_eq_nil_of_not_needsDrop fs vs h
  | .tuple _, .initLeaf => by simp [execDrop]
  | .tuple _, .initEnum _ _ => by simp [execDrop]
  | .enum_ variants, .initEnum vid vs => by
    simp only [execDrop]
    exact execDropVariants_eq_nil_of_not_needsDrop variants vid vs h
  | .enum_ _, .initLeaf => by simp [execDrop]
  | .enum_ _, .initFields _ => by simp [execDrop]

theorem execDropFields_eq_nil_of_not_needsDrop (fs : List DropTy) (vs : List InitVal)
    (h : tyNeedsDrop.listTyNeedsDrop fs = false) :
    execDrop.execDropFields fs vs = [] :=
  match fs, vs with
  | [], _ => by simp [execDrop.execDropFields]
  | _ :: _, [] => by simp [execDrop.execDropFields]
  | t :: ts, v :: vs => by
    simp only [tyNeedsDrop.listTyNeedsDrop, Bool.or_eq_false_iff] at h
    simp only [execDrop.execDropFields,
               execDrop_eq_nil_of_not_needsDrop t v h.1,
               execDropFields_eq_nil_of_not_needsDrop ts vs h.2,
               List.nil_append]

theorem execDropVariants_eq_nil_of_not_needsDrop (variants : List (List DropTy))
    (vid : Nat) (vs : List InitVal)
    (h : tyNeedsDrop.variantsTyNeedsDrop variants = false) :
    (match listGet? variants vid with
     | some fs => execDrop.execDropFields fs vs
     | none => []) = [] :=
  match variants, vid with
  | [], _ => rfl
  | fs :: rest, 0 => by
    simp only [tyNeedsDrop.variantsTyNeedsDrop, Bool.or_eq_false_iff] at h
    exact execDropFields_eq_nil_of_not_needsDrop fs vs h.1
  | _ :: rest, Nat.succ k => by
    simp only [tyNeedsDrop.variantsTyNeedsDrop, Bool.or_eq_false_iff] at h
    exact execDropVariants_eq_nil_of_not_needsDrop rest k vs h.2
end

/-- Abstract state produced by `MoveData` + `MaybeInitializedPlaces::exclude_inactive_in_otherwise()`
    at a `TerminatorKind::Drop` location (`remove_uninit_drops.rs:24-55`):
    - `tracked p`: whether `MoveData` contains a move-path for projection `p` (`move_path_children_matching`).
    - `maybeInit p`: whether `p` is in `MaybeInitializedPlaces` (bit set). -/
structure MaybeInitDomain where
  tracked : MovePath → Bool
  maybeInit : MovePath → Bool

/-- Exact formalization of `is_needs_drop_and_init` (`remove_uninit_drops.rs:75-160`). -/
noncomputable def isNeedsDropAndInit (dom : MaybeInitDomain) : DropTy → MovePath → Bool
  | ty, p =>
    if !dom.maybeInit p || !tyNeedsDrop ty then false
    else match ty with
      | .union_ => true
      | .manuallyDrop _ => true
      | .adtWithDtor _ _ => true
      | .leaf _ _ => true
      | .struct_ fs => checkFields dom p 0 fs
      | .tuple fs => checkFields dom p 0 fs
      | .enum_ vs => checkVariants dom p 0 vs
where
  checkFields (dom : MaybeInitDomain) (parent : MovePath) (idx : Nat) : List DropTy → Bool
    | [] => false
    | fty :: rest =>
      let childPath := parent ++ [.field idx]
      let headNeeds :=
        if dom.tracked childPath then
          isNeedsDropAndInit dom fty childPath
        else
          tyNeedsDrop fty
      headNeeds || checkFields dom parent (Nat.succ idx) rest
  checkVariants (dom : MaybeInitDomain) (parent : MovePath) (vid : Nat) :
      List (List DropTy) → Bool
    | [] => false
    | vfields :: rest =>
      let dcPath := parent ++ [.downcast vid]
      let headNeeds :=
        if dom.tracked dcPath then
          checkFields dom dcPath 0 vfields
        else
          tyNeedsDrop.listTyNeedsDrop vfields
      headNeeds || checkVariants dom parent (Nat.succ vid) rest

/-- Soundness invariant linking concrete runtime initialization `iv` to the abstract
    `MaybeInitializedPlaces` domain `dom` at projection path `p`:
    1. If `iv` is NOT `.uninit` (i.e. some part is initialized) and `dom.tracked p = true`,
       then `dom.maybeInit p = true`.
    2. For structs/tuples with `.initFields vs`: if a field `i` has `dom.tracked (p ++ [.field i])`,
       the soundness invariant holds recursively for `(fs[i], vs[i])` at `p ++ [.field i]`.
    3. For enums with `.initEnum vid vs`:
       - If `dom.tracked (p ++ [.downcast vid])`, then for every field `i` of variant `vid`
         with `dom.tracked (p ++ [.downcast vid, .field i])`, soundness holds recursively!
       (Notice `exclude_inactive_in_otherwise()` is safe here because it ONLY kills
       variants `vid' ≠ vid` that are dynamically inactive along that control-flow edge!) -/
noncomputable def AnyInit : InitVal → Prop
  | .uninit => False
  | .initLeaf => True
  | .initFields vs => AnyInitList vs
  | .initEnum _ vs => AnyInitList vs
where
  AnyInitList : List InitVal → Prop
    | [] => False
    | v :: rest => AnyInit v ∨ AnyInitList rest

/-- Predicate asserting that `execDrop ty iv` is non-empty implies `AnyInit` (or `adtWithDtor`). -/
noncomputable def HasLiveDrop : DropTy → InitVal → Prop
  | _, .uninit => False
  | .leaf true _, .initLeaf => True
  | .leaf _ _, _ => False
  | .union_, _ => False
  | .manuallyDrop _, _ => False
  | .adtWithDtor _ _, _ => True
  | .struct_ fs, .initFields vs => HasLiveDropFields fs vs
  | .struct_ _, _ => False
  | .tuple fs, .initFields vs => HasLiveDropFields fs vs
  | .tuple _, _ => False
  | .enum_ variants, .initEnum vid vs =>
      match listGet? variants vid with
      | some fs => HasLiveDropFields fs vs
      | none => False
  | .enum_ _, _ => False
where
  HasLiveDropFields : List DropTy → List InitVal → Prop
    | [], _ => False
    | _, [] => False
    | t :: ts, v :: vs => HasLiveDrop t v ∨ HasLiveDropFields ts vs

mutual
theorem execDrop_eq_nil_of_not_hasLiveDrop (ty : DropTy) (iv : InitVal)
    (h : ¬ HasLiveDrop ty iv) : execDrop ty iv = [] :=
  match ty, iv with
  | _, .uninit => by simp [execDrop]
  | .leaf true _, .initLeaf => by simp [HasLiveDrop] at h
  | .leaf true _, .initFields _ => by simp [execDrop]
  | .leaf true _, .initEnum _ _ => by simp [execDrop]
  | .leaf false _, .initLeaf => by simp [execDrop]
  | .leaf false _, .initFields _ => by simp [execDrop]
  | .leaf false _, .initEnum _ _ => by simp [execDrop]
  | .union_, .initLeaf => by simp [execDrop]
  | .union_, .initFields _ => by simp [execDrop]
  | .union_, .initEnum _ _ => by simp [execDrop]
  | .manuallyDrop _, .initLeaf => by simp [execDrop]
  | .manuallyDrop _, .initFields _ => by simp [execDrop]
  | .manuallyDrop _, .initEnum _ _ => by simp [execDrop]
  | .adtWithDtor _ _, .initLeaf => by simp [HasLiveDrop] at h
  | .adtWithDtor _ _, .initFields _ => by simp [HasLiveDrop] at h
  | .adtWithDtor _ _, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .struct_ fs, .initFields vs => by
    simp only [execDrop]
    simp only [HasLiveDrop] at h
    exact execDropFields_eq_nil_of_not_hasLiveDrop fs vs h
  | .struct_ _, .initLeaf => by simp [execDrop]
  | .struct_ _, .initEnum _ _ => by simp [execDrop]
  | .tuple fs, .initFields vs => by
    simp only [execDrop]
    simp only [HasLiveDrop] at h
    exact execDropFields_eq_nil_of_not_hasLiveDrop fs vs h
  | .tuple _, .initLeaf => by simp [execDrop]
  | .tuple _, .initEnum _ _ => by simp [execDrop]
  | .enum_ variants, .initEnum vid vs => by
    simp only [execDrop]
    simp only [HasLiveDrop] at h
    exact execDropVariants_eq_nil_of_not_hasLiveDrop variants vid vs h
  | .enum_ _, .initLeaf => by simp [execDrop]
  | .enum_ _, .initFields _ => by simp [execDrop]

theorem execDropFields_eq_nil_of_not_hasLiveDrop (fs : List DropTy) (vs : List InitVal)
    (h : ¬ HasLiveDrop.HasLiveDropFields fs vs) :
    execDrop.execDropFields fs vs = [] :=
  match fs, vs with
  | [], _ => by simp [execDrop.execDropFields]
  | _ :: _, [] => by simp [execDrop.execDropFields]
  | t :: ts, v :: vs => by
    simp only [HasLiveDrop.HasLiveDropFields] at h
    have h1 : ¬ HasLiveDrop t v := fun ht => h (Or.inl ht)
    have h2 : ¬ HasLiveDrop.HasLiveDropFields ts vs := fun hts => h (Or.inr hts)
    simp only [execDrop.execDropFields,
               execDrop_eq_nil_of_not_hasLiveDrop t v h1,
               execDropFields_eq_nil_of_not_hasLiveDrop ts vs h2,
               List.nil_append]

theorem execDropVariants_eq_nil_of_not_hasLiveDrop (variants : List (List DropTy))
    (vid : Nat) (vs : List InitVal)
    (h : ¬ (match listGet? variants vid with
            | some fs => HasLiveDrop.HasLiveDropFields fs vs
            | none => False)) :
    (match listGet? variants vid with
     | some fs => execDrop.execDropFields fs vs
     | none => []) = [] :=
  match variants, vid with
  | [], _ => rfl
  | fs :: _, 0 => execDropFields_eq_nil_of_not_hasLiveDrop fs vs h
  | _ :: rest, Nat.succ k => execDropVariants_eq_nil_of_not_hasLiveDrop rest k vs h
end

/-- Soundness of `MaybeInitializedPlaces` dataflow result `dom` wrt concrete state `(ty, iv)`
    at move path `p`: whenever any live drop exists in `(ty, iv)` and `p` is tracked,
    `dom.maybeInit p = true`, and the invariant holds recursively on every tracked child
    field/active-variant downcast! -/
noncomputable def MaybeInitSound (dom : MaybeInitDomain) : DropTy → InitVal → MovePath → Prop
  | ty, iv, p =>
    (HasLiveDrop ty iv → dom.maybeInit p = true) ∧
    match ty, iv with
    | .struct_ fs, .initFields vs => SoundFields dom p 0 fs vs
    | .tuple fs, .initFields vs => SoundFields dom p 0 fs vs
    | .enum_ variants, .initEnum vid vs => SoundActiveVariant dom p 0 vid variants vs
    | _, _ => True
where
  SoundFields (dom : MaybeInitDomain) (parent : MovePath) (idx : Nat) :
      List DropTy → List InitVal → Prop
    | [], _ => True
    | _, [] => True
    | fty :: frest, v :: vrest =>
      (dom.tracked (parent ++ [.field idx]) = true →
        MaybeInitSound dom fty v (parent ++ [.field idx])) ∧
      SoundFields dom parent (Nat.succ idx) frest vrest
  SoundActiveVariant (dom : MaybeInitDomain) (parent : MovePath) (cur : Nat) (target : Nat) :
      List (List DropTy) → List InitVal → Prop
    | [], _ => True
    | vfields :: rest, vs =>
      (cur = target → dom.tracked (parent ++ [.downcast cur]) = true →
        SoundFields dom (parent ++ [.downcast cur]) 0 vfields vs) ∧
      SoundActiveVariant dom parent (Nat.succ cur) target rest vs

mutual
/-- Helper: if `HasLiveDrop ty iv` holds, then `tyNeedsDrop ty = true`. -/
theorem needsDrop_of_hasLiveDrop (ty : DropTy) (iv : InitVal)
    (h : HasLiveDrop ty iv) : tyNeedsDrop ty = true :=
  match ty, iv with
  | _, .uninit => by simp [HasLiveDrop] at h
  | .leaf true _, .initLeaf => rfl
  | .leaf true _, .initFields _ => by simp [HasLiveDrop] at h
  | .leaf true _, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .leaf false _, .initLeaf => by simp [HasLiveDrop] at h
  | .leaf false _, .initFields _ => by simp [HasLiveDrop] at h
  | .leaf false _, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .union_, .initLeaf => by simp [HasLiveDrop] at h
  | .union_, .initFields _ => by simp [HasLiveDrop] at h
  | .union_, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .manuallyDrop _, .initLeaf => by simp [HasLiveDrop] at h
  | .manuallyDrop _, .initFields _ => by simp [HasLiveDrop] at h
  | .manuallyDrop _, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .adtWithDtor _ _, _ => rfl
  | .struct_ fs, .initFields vs => by
    simp only [tyNeedsDrop]
    simp only [HasLiveDrop] at h
    exact needsDropFields_of_hasLiveDrop fs vs h
  | .struct_ _, .initLeaf => by simp [HasLiveDrop] at h
  | .struct_ _, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .tuple fs, .initFields vs => by
    simp only [tyNeedsDrop]
    simp only [HasLiveDrop] at h
    exact needsDropFields_of_hasLiveDrop fs vs h
  | .tuple _, .initLeaf => by simp [HasLiveDrop] at h
  | .tuple _, .initEnum _ _ => by simp [HasLiveDrop] at h
  | .enum_ variants, .initEnum vid vs => by
    simp only [tyNeedsDrop]
    simp only [HasLiveDrop] at h
    exact needsDropVariants_of_hasLiveDrop variants vid vs h
  | .enum_ _, .initLeaf => by simp [HasLiveDrop] at h
  | .enum_ _, .initFields _ => by simp [HasLiveDrop] at h

theorem needsDropFields_of_hasLiveDrop (fs : List DropTy) (vs : List InitVal)
    (h : HasLiveDrop.HasLiveDropFields fs vs) :
    tyNeedsDrop.listTyNeedsDrop fs = true :=
  match fs, vs with
  | [], _ => by simp [HasLiveDrop.HasLiveDropFields] at h
  | _ :: _, [] => by simp [HasLiveDrop.HasLiveDropFields] at h
  | t :: ts, v :: vs => by
    simp only [HasLiveDrop.HasLiveDropFields] at h
    simp only [tyNeedsDrop.listTyNeedsDrop, Bool.or_eq_true]
    cases h with
    | inl ht => exact Or.inl (needsDrop_of_hasLiveDrop t v ht)
    | inr hts => exact Or.inr (needsDropFields_of_hasLiveDrop ts vs hts)

theorem needsDropVariants_of_hasLiveDrop (variants : List (List DropTy))
    (vid : Nat) (vs : List InitVal)
    (h : match listGet? variants vid with
         | some fs => HasLiveDrop.HasLiveDropFields fs vs
         | none => False) :
    tyNeedsDrop.variantsTyNeedsDrop variants = true :=
  match variants, vid with
  | [], _ => False.elim h
  | fs :: rest, 0 => by
    simp only [tyNeedsDrop.variantsTyNeedsDrop, Bool.or_eq_true]
    exact Or.inl (needsDropFields_of_hasLiveDrop fs vs h)
  | _ :: rest, Nat.succ k => by
    simp only [tyNeedsDrop.variantsTyNeedsDrop, Bool.or_eq_true]
    exact Or.inr (needsDropVariants_of_hasLiveDrop rest k vs h)
end

mutual
/-- Core recursive soundness lemma: if `MaybeInitSound dom ty iv p` and `HasLiveDrop ty iv`,
    then `isNeedsDropAndInit dom ty p = true`. -/
theorem isNeedsDropAndInit_true_of_hasLiveDrop (dom : MaybeInitDomain)
    (ty : DropTy) (iv : InitVal) (p : MovePath)
    (hsound : MaybeInitSound dom ty iv p) (hlive : HasLiveDrop ty iv) :
    isNeedsDropAndInit dom ty p = true := by
  unfold MaybeInitSound at hsound
  have hmi : dom.maybeInit p = true := hsound.1 hlive
  have hnd : tyNeedsDrop ty = true := needsDrop_of_hasLiveDrop ty iv hlive
  match ty, iv with
  | _, .uninit => simp [HasLiveDrop] at hlive
  | .leaf true _, .initLeaf =>
    simp [isNeedsDropAndInit, hmi, hnd]
  | .leaf true _, .initFields _ => simp [HasLiveDrop] at hlive
  | .leaf true _, .initEnum _ _ => simp [HasLiveDrop] at hlive
  | .leaf false _, .initLeaf => simp [HasLiveDrop] at hlive
  | .leaf false _, .initFields _ => simp [HasLiveDrop] at hlive
  | .leaf false _, .initEnum _ _ => simp [HasLiveDrop] at hlive
  | .union_, .initLeaf => simp [HasLiveDrop] at hlive
  | .union_, .initFields _ => simp [HasLiveDrop] at hlive
  | .union_, .initEnum _ _ => simp [HasLiveDrop] at hlive
  | .manuallyDrop _, .initLeaf => simp [HasLiveDrop] at hlive
  | .manuallyDrop _, .initFields _ => simp [HasLiveDrop] at hlive
  | .manuallyDrop _, .initEnum _ _ => simp [HasLiveDrop] at hlive
  | .adtWithDtor _ _, .initLeaf => simp [isNeedsDropAndInit, hmi, hnd]
  | .adtWithDtor _ _, .initFields _ => simp [isNeedsDropAndInit, hmi, hnd]
  | .adtWithDtor _ _, .initEnum _ _ => simp [isNeedsDropAndInit, hmi, hnd]
  | .struct_ fs, .initFields vs =>
    simp only [isNeedsDropAndInit, hmi, hnd, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    simp only [HasLiveDrop] at hlive
    exact isNeedsDropAndInitFields_true_of_hasLiveDrop dom p 0 fs vs hsound.2 hlive
  | .struct_ _, .initLeaf => simp [HasLiveDrop] at hlive
  | .struct_ _, .initEnum _ _ => simp [HasLiveDrop] at hlive
  | .tuple fs, .initFields vs =>
    simp only [isNeedsDropAndInit, hmi, hnd, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    simp only [HasLiveDrop] at hlive
    exact isNeedsDropAndInitFields_true_of_hasLiveDrop dom p 0 fs vs hsound.2 hlive
  | .tuple _, .initLeaf => simp [HasLiveDrop] at hlive
  | .tuple _, .initEnum _ _ => simp [HasLiveDrop] at hlive
  | .enum_ variants, .initEnum vid vs =>
    simp only [isNeedsDropAndInit, hmi, hnd, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    simp only [HasLiveDrop] at hlive
    have hsound' : MaybeInitSound.SoundActiveVariant dom p 0 (0 + vid) variants vs := by
      rw [Nat.zero_add]; exact hsound.2
    exact isNeedsDropAndInitVariants_true_of_hasLiveDrop dom p 0 vid variants vs hsound' hlive
  | .enum_ _, .initLeaf => simp [HasLiveDrop] at hlive
  | .enum_ _, .initFields _ => simp [HasLiveDrop] at hlive

theorem isNeedsDropAndInitFields_true_of_hasLiveDrop (dom : MaybeInitDomain)
    (parent : MovePath) (idx : Nat) (fs : List DropTy) (vs : List InitVal)
    (hsound : MaybeInitSound.SoundFields dom parent idx fs vs)
    (hlive : HasLiveDrop.HasLiveDropFields fs vs) :
    isNeedsDropAndInit.checkFields dom parent idx fs = true :=
  match fs, vs with
  | [], _ => by simp [HasLiveDrop.HasLiveDropFields] at hlive
  | _ :: _, [] => by simp [HasLiveDrop.HasLiveDropFields] at hlive
  | fty :: frest, v :: vrest => by
    simp only [HasLiveDrop.HasLiveDropFields] at hlive
    simp only [MaybeInitSound.SoundFields] at hsound
    simp only [isNeedsDropAndInit.checkFields, Bool.or_eq_true]
    cases hlive with
    | inl hhead =>
      apply Or.inl
      cases htr : dom.tracked (parent ++ [.field idx]) with
      | true =>
        simp only [↓reduceIte]
        exact isNeedsDropAndInit_true_of_hasLiveDrop dom fty v (parent ++ [.field idx]) (hsound.1 htr) hhead
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact needsDrop_of_hasLiveDrop fty v hhead
    | inr htail =>
      exact Or.inr (isNeedsDropAndInitFields_true_of_hasLiveDrop dom parent (Nat.succ idx) frest vrest hsound.2 htail)

theorem isNeedsDropAndInitVariants_true_of_hasLiveDrop (dom : MaybeInitDomain)
    (parent : MovePath) (cur : Nat) (rem : Nat)
    (variants : List (List DropTy)) (vs : List InitVal)
    (hsound : MaybeInitSound.SoundActiveVariant dom parent cur (cur + rem) variants vs)
    (hlive : match listGet? variants rem with
             | some fs => HasLiveDrop.HasLiveDropFields fs vs
             | none => False) :
    isNeedsDropAndInit.checkVariants dom parent cur variants = true :=
  match variants, rem with
  | [], _ => False.elim hlive
  | vfields :: rest, 0 => by
    simp only [MaybeInitSound.SoundActiveVariant] at hsound
    simp only [isNeedsDropAndInit.checkVariants, Bool.or_eq_true]
    apply Or.inl
    cases htr : dom.tracked (parent ++ [.downcast cur]) with
    | true =>
      simp only [↓reduceIte]
      have hcurEq : cur = cur + 0 := (Nat.add_zero cur).symm
      exact isNeedsDropAndInitFields_true_of_hasLiveDrop dom (parent ++ [.downcast cur]) 0 vfields vs (hsound.1 hcurEq htr) hlive
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact needsDropFields_of_hasLiveDrop vfields vs hlive
  | _ :: rest, Nat.succ k => by
    simp only [MaybeInitSound.SoundActiveVariant] at hsound
    simp only [isNeedsDropAndInit.checkVariants, Bool.or_eq_true]
    apply Or.inr
    have hadd : cur + Nat.succ k = Nat.succ cur + k := by
      rw [Nat.add_succ, Nat.succ_add]
    have hsound2 : MaybeInitSound.SoundActiveVariant dom parent (Nat.succ cur) (Nat.succ cur + k) rest vs := by
      rw [← hadd]; exact hsound.2
    exact isNeedsDropAndInitVariants_true_of_hasLiveDrop dom parent (Nat.succ cur) k rest vs hsound2 hlive
end

/-- Small-step MIR terminator for `Drop` vs. `Goto` (`remove_uninit_drops.rs:64-65`). -/
inductive DropOrGotoTerm where
  | drop (ty : DropTy) (target : Nat) (unwind : Nat)
  | goto (target : Nat)

/-- Operational step result: `(nextBlock, executedDestructorTrace)`. -/
noncomputable def stepDropOrGoto (iv : InitVal) : DropOrGotoTerm → Nat × List Nat
  | .drop ty target _ => (target, execDrop ty iv)
  | .goto target => (target, [])

/-- Pass rewrite performed by `RemoveUninitDrops` (`remove_uninit_drops.rs:44-65`). -/
noncomputable def rewriteRemoveUninitDrops (dom : MaybeInitDomain) (rootPath : MovePath) :
    DropOrGotoTerm → DropOrGotoTerm
  | .drop ty target unwind =>
    if isNeedsDropAndInit dom ty rootPath then .drop ty target unwind
    else .goto target
  | .goto target => .goto target

/-- **Main `RemoveUninitDrops` Soundness Theorem (`removeUninitDrops_goto_sound_when_not_maybe_init`)**:
    Whenever `MaybeInitSound dom ty iv rootPath` holds:
    (1) If `isNeedsDropAndInit dom ty rootPath = false`, then `execDrop ty iv = []`
        (no runtime destructor can execute, and no unwind edge can trigger).
    (2) Rewriting `Drop { target, .. }` to `Goto { target }` preserves the exact operational
        step semantics (`stepDropOrGoto iv (rewrite ...) = stepDropOrGoto iv term`). -/
theorem removeUninitDrops_goto_sound_when_not_maybe_init
    (dom : MaybeInitDomain) (ty : DropTy) (iv : InitVal) (rootPath : MovePath)
    (target unwind : Nat)
    (hsound : MaybeInitSound dom ty iv rootPath) :
    (isNeedsDropAndInit dom ty rootPath = false → execDrop ty iv = []) ∧
    stepDropOrGoto iv (rewriteRemoveUninitDrops dom rootPath (.drop ty target unwind)) =
      stepDropOrGoto iv (.drop ty target unwind) := by
  have hNil : isNeedsDropAndInit dom ty rootPath = false → execDrop ty iv = [] := by
    intro hfalse
    apply execDrop_eq_nil_of_not_hasLiveDrop ty iv
    intro hlive
    have htrue := isNeedsDropAndInit_true_of_hasLiveDrop dom ty iv rootPath hsound hlive
    rw [htrue] at hfalse
    cases hfalse
  refine ⟨hNil, ?_⟩
  simp only [rewriteRemoveUninitDrops]
  cases hkeep : isNeedsDropAndInit dom ty rootPath with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, stepDropOrGoto, hNil hkeep]

/-- Corollary: `RemoveUnneededDrops` (`remove_unneeded_drops.rs:28-32`) preserves exact
    operational step semantics for ALL runtime values `iv` without needing dataflow analysis. -/
theorem removeUnneededDrops_goto_sound (ty : DropTy) (iv : InitVal) (target unwind : Nat)
    (hnot : tyNeedsDrop ty = false) :
    stepDropOrGoto iv (.goto target) = stepDropOrGoto iv (.drop ty target unwind) := by
  simp only [stepDropOrGoto, execDrop_eq_nil_of_not_needsDrop ty iv hnot]

/-- Concrete witness mirroring the live `Pair(NonConstDrop, NonConstDrop)` probes:
    - When BOTH fields `0` and `1` are moved out (`maybeInit` false on both field paths),
      `isNeedsDropAndInit` returns `false` and `execDrop = []`.
    - When field `0` is moved out but field `1` remains live (`maybeInit` true on field `1`),
      `isNeedsDropAndInit` returns `true` and `execDrop = [2]` (so `Drop` is preserved and
      `CheckLiveDrops` catches the non-const drop!). -/
def pairNonConstDropTy : DropTy :=
  .struct_ [.leaf true 1, .leaf true 2]

def pairBothMovedDom : MaybeInitDomain where
  tracked := fun p => match p with
    | [] => true
    | [.field 0] => true
    | [.field 1] => true
    | _ => false
  maybeInit := fun p => match p with
    | [] => true
    | [.field 0] => false
    | [.field 1] => false
    | _ => false

def pairOneLiveDom : MaybeInitDomain where
  tracked := fun p => match p with
    | [] => true
    | [.field 0] => true
    | [.field 1] => true
    | _ => false
  maybeInit := fun p => match p with
    | [] => true
    | [.field 0] => false
    | [.field 1] => true
    | _ => false

theorem pair_partial_move_discrimination :
    isNeedsDropAndInit pairBothMovedDom pairNonConstDropTy [] = false ∧
    execDrop pairNonConstDropTy (.initFields [.uninit, .uninit]) = [] ∧
    isNeedsDropAndInit pairOneLiveDom pairNonConstDropTy [] = true ∧
    execDrop pairNonConstDropTy (.initFields [.uninit, .initLeaf]) = [2] :=
  ⟨rfl, rfl, rfl, rfl⟩

end DropPruning

-- ============================================================================
-- Kernel Axiom Audits (must use ONLY `[]` or `[propext, Quot.sound]`,
-- ZERO `Classical.choice`, ZERO `sorryAx`, ZERO `Lean.ofReduceBool`)
-- ============================================================================

#print axioms ctfeLimit_dominator_irreducible_counterexample
#print axioms collapsedSelfLoop_caught_by_ctfeLimit
#print axioms dfsRetreatingEdge_bounds_counterFree_path_by_numBlocks
#print axioms dfsRetreatingEdge_hits_every_cycle
#print axioms dominatorBackEdge_is_dfsRetreatingEdge
#print axioms irr_dfs_strict_separation
#print axioms checkForceInline_ok_iff
#print axioms checkForceInline_short_circuit_priority
#print axioms checkBodyCost_append
#print axioms checkBodyCost_stripIgnored
#print axioms costChecker_intrinsic_and_drop_separation
#print axioms crossCrateInline_priority_and_cost_soundness
#print axioms crossCrateInline_version_delta_reliable_f16
#print axioms crossCrateInline_version_delta_always_const
#print axioms execDrop_eq_nil_of_not_needsDrop
#print axioms removeUninitDrops_goto_sound_when_not_maybe_init
#print axioms removeUnneededDrops_goto_sound
#print axioms pair_partial_move_discrimination

end RustcMirInlineCtfeDrop
