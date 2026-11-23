/-
  Mechanized Soundness and Boundary Characterization for `rustc_mir_transform::coverage`
  =====================================================================================

  Primary-source anchors:
  - `rust-lang/rust` (`5debe6a1244452beced762385f88a51857a915fc` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
      * `compiler/rustc_mir_transform/src/coverage/graph.rs`
      * `compiler/rustc_mir_transform/src/coverage/counters/balanced_flow.rs`
      * `compiler/rustc_mir_transform/src/coverage/counters/node_flow.rs`
      * `compiler/rustc_mir_transform/src/coverage/counters.rs`
      * `compiler/rustc_mir_transform/src/coverage/query.rs`
      * `compiler/rustc_mir_transform/src/coverage/spans.rs`
  - `llvm/llvm-project` (`dd54bc3427332702425782da54fe306cecd3cdb5`):
      * `llvm/lib/ProfileData/Coverage/CoverageMapping.cpp`
      * `llvm/tools/llvm-cov/CoverageExporterJson.cpp`

  Purity constraints:
  - Lean v4.34.1 core `Init` only (zero external imports).
  - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
    zero `native_decide`, zero `partial def`, and zero `._unsafe_rec` constants.
-/

namespace MirCoverageSoundness

/-! ## Section 1: Finite Node Sums & Integer Algebra Helpers -/

theorem natBeq_self (x : Nat) : (x == x) = true := by
  change decide (x = x) = true
  exact decide_eq_true rfl

theorem natBeq_ne {x y : Nat} (h : x ≠ y) : (x == y) = false := by
  change decide (x = y) = false
  exact decide_eq_false h

def sumNodes (n : Nat) (f : Nat → Int) : Int :=
  Nat.rec (motive := fun _ => Int) 0 (fun k acc => acc + f k) n

theorem sumNodes_zero_eq (f : Nat → Int) : sumNodes 0 f = 0 := rfl

theorem sumNodes_succ_eq (n : Nat) (f : Nat → Int) :
    sumNodes (n + 1) f = sumNodes n f + f n := rfl

theorem sumNodes_zero_fn (n : Nat) : sumNodes n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumNodes_succ_eq, ih, Int.add_zero]

theorem sumNodes_ext {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumNodes n f = sumNodes n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNodes_succ_eq]
    have hprev : sumNodes n f = sumNodes n g :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hlast : f n = g n := h n (Nat.lt_succ_self n)
    rw [hprev, hlast]

theorem sumNodes_add (n : Nat) (f g : Nat → Int) :
    sumNodes n (fun i => f i + g i) = sumNodes n f + sumNodes n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNodes_succ_eq, ih]
    rw [Int.add_assoc (sumNodes n f) (sumNodes n g) (f n + g n)]
    rw [← Int.add_assoc (sumNodes n g) (f n) (g n)]
    rw [Int.add_comm (sumNodes n g) (f n)]
    rw [Int.add_assoc (f n) (sumNodes n g) (g n)]
    rw [← Int.add_assoc (sumNodes n f) (f n) (sumNodes n g + g n)]

theorem sumNodes_neg (n : Nat) (f : Nat → Int) :
    sumNodes n (fun i => -f i) = -sumNodes n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNodes_succ_eq, ih, Int.neg_add]

theorem sumNodes_sub (n : Nat) (f g : Nat → Int) :
    sumNodes n (fun i => f i - g i) = sumNodes n f - sumNodes n g := by
  have h1 : (fun i => f i - g i) = (fun i => f i + -g i) := by
    funext i; rw [Int.sub_eq_add_neg]
  rw [h1, sumNodes_add, sumNodes_neg, ← Int.sub_eq_add_neg]

theorem sumNodes_single (n k : Nat) (c : Int) (hk : k < n) :
    sumNodes n (fun i => if i == k then c else 0) = c := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    simp only [sumNodes_succ_eq]
    by_cases hkn : k = n
    · subst hkn
      have hzero : sumNodes k (fun i => if i == k then c else 0) = 0 := by
        refine Eq.trans (sumNodes_ext ?_) (sumNodes_zero_fn k)
        intro i hi
        have hne : (i == k) = false := natBeq_ne (Nat.ne_of_lt hi)
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hself : (k == k) = true := natBeq_self k
      simp only [hzero, hself, ↓reduceIte, Int.zero_add]
    · have hklt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn
      have ihval := ih hklt
      have hne : (n == k) = false := natBeq_ne (Ne.symm hkn)
      simp only [ihval, hne, Bool.false_eq_true, ↓reduceIte, Int.add_zero]

theorem sumNodes_single_out (n k : Nat) (c : Int) (hk : ¬ (k < n)) :
    sumNodes n (fun i => if i == k then c else 0) = 0 := by
  refine Eq.trans (sumNodes_ext ?_) (sumNodes_zero_fn n)
  intro i hi
  have hne : i ≠ k := fun heq => hk (heq ▸ hi)
  have hbf : (i == k) = false := natBeq_ne hne
  simp only [hbf, Bool.false_eq_true, ↓reduceIte]

theorem sumNodes_swap (m n : Nat) (F : Nat → Nat → Int) :
    sumNodes m (fun i => sumNodes n (fun j => F i j)) =
      sumNodes n (fun j => sumNodes m (fun i => F i j)) := by
  induction m with
  | zero =>
    simp only [sumNodes_zero_eq]
    exact Eq.symm (sumNodes_zero_fn n)
  | succ m ih =>
    simp only [sumNodes_succ_eq]
    rw [ih, ← sumNodes_add]

theorem sumNodes_fiber {n m : Nat} (proj : Nat → Nat) (f : Nat → Int)
    (hbound : ∀ i, i < n → proj i < m) :
    sumNodes m (fun b => sumNodes n (fun a => if proj a == b then f a else 0)) =
      sumNodes n f := by
  rw [sumNodes_swap]
  apply sumNodes_ext
  intro a ha
  have hpa : proj a < m := hbound a ha
  have hswap : (fun b => if proj a == b then f a else 0) =
      (fun b => if b == proj a then f a else 0) := by
    funext b
    by_cases h : proj a = b
    · subst h; simp only [natBeq_self]
    · have h1 : (proj a == b) = false := natBeq_ne h
      have h2 : (b == proj a) = false := natBeq_ne (Ne.symm h)
      simp only [h1, h2]
  rw [hswap]
  exact sumNodes_single m (proj a) (f a) hpa

theorem sumNodes_mul_const (n : Nat) (f : Nat → Int) (c : Int) :
    sumNodes n (fun i => f i * c) = sumNodes n f * c := by
  induction n with
  | zero =>
    simp only [sumNodes_zero_eq, Int.zero_mul]
  | succ n ih =>
    simp only [sumNodes_succ_eq, ih, Int.add_mul]

/-! ## Section 2: MIR Terminators, Unwind Stripping (`graph.rs`), & Trace Kirchhoff Balance -/

/-- Subset of MIR `TerminatorKind` governing BCB chaining and successor filtering
(`compiler/rustc_mir_transform/src/coverage/graph.rs:366-406`). -/
inductive MirTerm where
  | goto (target : Nat)
  | switchInt (targets : List Nat)
  | assert (target : Nat) (unwind : Option Nat)
  | drop (target : Nat) (unwind : Option Nat)
  | call (target : Option Nat) (unwind : Option Nat)
  | falseEdge (realTarget : Nat) (imagTarget : Nat)
  | falseUnwind (realTarget : Nat) (unwind : Option Nat)
  | yield (resume : Nat) (dropTarget : Option Nat)
  | ret
  | unreachable
  | unwindResume
  | unwindTerminate

/-- Models `bcb_filtered_successors` + `CoverageSuccessors::is_out_summable`
(`graph.rs:338-406`). -/
def bcbFilteredSuccessors : MirTerm → List Nat × Bool
  | .switchInt targets => (targets, !(targets.isEmpty))
  | .yield resume _ => ([resume], false)
  | .assert target _ => ([target], true)
  | .drop target _ => ([target], true)
  | .falseEdge realTarget _ => ([realTarget], true)
  | .falseUnwind realTarget _ => ([realTarget], true)
  | .goto target => ([target], true)
  | .call (some target) _ => ([target], true)
  | .call none _ => ([], false)
  | .ret => ([], false)
  | .unreachable => ([], false)
  | .unwindResume => ([], false)
  | .unwindTerminate => ([], false)

def isOutChainable (t : MirTerm) : Bool :=
  let (succs, summable) := bcbFilteredSuccessors t
  summable && (succs.length == 1)

theorem bcb_strips_assert_unwind (tgt : Nat) (u : Option Nat) :
    bcbFilteredSuccessors (.assert tgt u) = ([tgt], true) ∧
      isOutChainable (.assert tgt u) = true := ⟨rfl, rfl⟩

theorem bcb_strips_drop_unwind (tgt : Nat) (u : Option Nat) :
    bcbFilteredSuccessors (.drop tgt u) = ([tgt], true) ∧
      isOutChainable (.drop tgt u) = true := ⟨rfl, rfl⟩

theorem bcb_strips_call_unwind (tgt : Nat) (u : Option Nat) :
    bcbFilteredSuccessors (.call (some tgt) u) = ([tgt], true) ∧
      isOutChainable (.call (some tgt) u) = true := ⟨rfl, rfl⟩

theorem bcb_strips_false_edges (r im : Nat) (u : Option Nat) :
    bcbFilteredSuccessors (.falseEdge r im) = ([r], true) ∧
      bcbFilteredSuccessors (.falseUnwind r u) = ([r], true) := ⟨rfl, rfl⟩

theorem bcb_yield_not_out_summable (res : Nat) (drp : Option Nat) :
    (bcbFilteredSuccessors (.yield res drp)).1 = [res] ∧
      (bcbFilteredSuccessors (.yield res drp)).2 = false ∧
      isOutChainable (.yield res drp) = false := ⟨rfl, rfl, rfl⟩

theorem bcb_exit_terminators_empty_succs :
    (bcbFilteredSuccessors .ret = ([], false)) ∧
      (bcbFilteredSuccessors .unreachable = ([], false)) ∧
      (bcbFilteredSuccessors .unwindResume = ([], false)) ∧
      (bcbFilteredSuccessors .unwindTerminate = ([], false)) := ⟨rfl, rfl, rfl, rfl⟩

/-- CoverageGraph abstraction matching `graph.rs:19-35`. -/
structure CoverageGraph where
  numNodes : Nat
  startNode : Nat
  succs : Nat → List Nat
  isOutSummable : Nat → Bool
  startLt : startNode < numNodes
  succsLt : ∀ u, u < numNodes → ∀ v, v ∈ succs u → v < numNodes

/-- BalancedFlowGraph abstraction matching `balanced_flow.rs:43-131`. -/
structure BalancedFlowGraph where
  base : CoverageGraph
  sinkEdgeNodes : Nat → Bool

def BalancedFlowGraph.sink (bf : BalancedFlowGraph) : Nat :=
  bf.base.numNodes

def BalancedFlowGraph.totalNodes (bf : BalancedFlowGraph) : Nat :=
  bf.base.numNodes + 1

def BalancedFlowGraph.succs (bf : BalancedFlowGraph) (u : Nat) : List Nat :=
  if u == bf.sink then
    [bf.base.startNode]
  else
    let realSuccs := bf.base.succs u
    if bf.sinkEdgeNodes u then realSuccs ++ [bf.sink] else realSuccs

theorem balanced_sink_succ (bf : BalancedFlowGraph) :
    bf.succs bf.sink = [bf.base.startNode] := by
  simp only [BalancedFlowGraph.succs, natBeq_self, ↓reduceIte]

theorem balanced_node_succs_bounded (bf : BalancedFlowGraph) (u : Nat)
    (hu : u < bf.totalNodes) :
    ∀ v, v ∈ bf.succs u → v < bf.totalNodes := by
  intro v hv
  unfold BalancedFlowGraph.succs at hv
  by_cases hus : u = bf.sink
  · subst hus
    simp only [natBeq_self, ↓reduceIte, List.mem_singleton] at hv
    subst hv
    exact Nat.lt_succ_of_lt bf.base.startLt
  · have hne : (u == bf.sink) = false := natBeq_ne hus
    have hubase : u < bf.base.numNodes := by
      unfold BalancedFlowGraph.totalNodes at hu
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hu) hus
    rw [hne] at hv
    dsimp only at hv
    by_cases hs : bf.sinkEdgeNodes u = true
    · rw [hs] at hv
      simp only [↓reduceIte] at hv
      rcases List.mem_append.mp hv with hreal | hvs
      · exact Nat.lt_succ_of_lt (bf.base.succsLt u hubase v hreal)
      · have hvs' : v = bf.sink := List.mem_singleton.mp hvs
        subst hvs'
        unfold BalancedFlowGraph.sink BalancedFlowGraph.totalNodes
        exact Nat.lt_succ_self bf.base.numNodes
    · have hsf : bf.sinkEdgeNodes u = false := Bool.eq_false_iff.mpr hs
      rw [hsf] at hv
      simp only [Bool.false_eq_true, ↓reduceIte] at hv
      exact Nat.lt_succ_of_lt (bf.base.succsLt u hubase v hv)

/-- Directed edge flow function on `Nat × Nat`. -/
abbrev EdgeFlow := Nat → Nat → Int

def inFlow (n : Nat) (ef : EdgeFlow) (v : Nat) : Int :=
  sumNodes n (fun u => ef u v)

def outFlow (n : Nat) (ef : EdgeFlow) (u : Nat) : Int :=
  sumNodes n (fun v => ef u v)

def netFlow (n : Nat) (ef : EdgeFlow) (v : Nat) : Int :=
  inFlow n ef v - outFlow n ef v

/-- Edge flow induced by a concrete list of directed transitions `(u, v)`. -/
def pathEdgeFlow (p : List (Nat × Nat)) (a b : Nat) : Int :=
  p.foldr (fun hd acc a' b' => acc a' b' + (if a' == hd.1 && b' == hd.2 then 1 else 0))
    (fun _ _ => 0) a b

theorem pathEdgeFlow_nil (a b : Nat) : pathEdgeFlow [] a b = 0 := rfl

theorem pathEdgeFlow_cons (u w : Nat) (rest : List (Nat × Nat)) :
    pathEdgeFlow ((u, w) :: rest) =
      (fun a b => pathEdgeFlow rest a b + (if a == u && b == w then 1 else 0)) := rfl

def indicator (k v : Nat) : Int :=
  if v == k then 1 else 0

theorem inFlow_cons_edge (n u v x : Nat) (ef : EdgeFlow) :
    inFlow n (fun a b => ef a b + (if a == u && b == v then 1 else 0)) x =
      inFlow n ef x + (if u < n then indicator v x else 0) := by
  unfold inFlow
  rw [sumNodes_add]
  congr 1
  by_cases hxv : x = v
  · subst hxv
    have hfn : (fun a => if a == u && x == x then (1 : Int) else 0) =
        (fun a => if a == u then 1 else 0) := by
      funext a
      simp only [natBeq_self, Bool.and_true]
    rw [hfn]
    unfold indicator
    by_cases hun : u < n
    · simp only [hun, ↓reduceIte, natBeq_self]
      exact sumNodes_single n u 1 hun
    · simp only [hun, ↓reduceIte]
      exact sumNodes_single_out n u 1 hun
  · have hxvf : (x == v) = false := natBeq_ne hxv
    have hfn : (fun a => if a == u && x == v then (1 : Int) else 0) = (fun _ => 0) := by
      funext a
      simp only [hxvf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rw [hfn, sumNodes_zero_fn]
    unfold indicator
    by_cases hun : u < n <;> simp only [hun, hxvf, Bool.false_eq_true, ↓reduceIte]

theorem outFlow_cons_edge (n u v x : Nat) (ef : EdgeFlow) :
    outFlow n (fun a b => ef a b + (if a == u && b == v then 1 else 0)) x =
      outFlow n ef x + (if v < n then indicator u x else 0) := by
  unfold outFlow
  rw [sumNodes_add]
  congr 1
  by_cases hxu : x = u
  · subst hxu
    have hfn : (fun b => if x == x && b == v then (1 : Int) else 0) =
        (fun b => if b == v then 1 else 0) := by
      funext b
      simp only [natBeq_self, Bool.true_and]
    rw [hfn]
    unfold indicator
    by_cases hvn : v < n
    · simp only [hvn, ↓reduceIte, natBeq_self]
      exact sumNodes_single n v 1 hvn
    · simp only [hvn, ↓reduceIte]
      exact sumNodes_single_out n v 1 hvn
  · have hxuf : (x == u) = false := natBeq_ne hxu
    have hfn : (fun b => if x == u && b == v then (1 : Int) else 0) = (fun _ => 0) := by
      funext b
      simp only [hxuf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hfn, sumNodes_zero_fn]
    unfold indicator
    by_cases hvn : v < n <;> simp only [hvn, hxuf, Bool.false_eq_true, ↓reduceIte]

/-- Well-chained directed path from `src` to `dst` within `{0..n-1}`. -/
inductive ValidPath (n : Nat) : Nat → Nat → List (Nat × Nat) → Prop where
  | nil (u : Nat) (hu : u < n) : ValidPath n u u []
  | cons {u w dst : Nat} {rest : List (Nat × Nat)}
      (hu : u < n) (hw : w < n)
      (hrest : ValidPath n w dst rest) :
      ValidPath n u dst ((u, w) :: rest)

theorem validPath_dst_lt {n src dst : Nat} {p : List (Nat × Nat)}
    (hp : ValidPath n src dst p) : dst < n := by
  induction hp with
  | nil u hu => exact hu
  | cons _ _ _ ih => exact ih

theorem validPath_src_lt {n src dst : Nat} {p : List (Nat × Nat)}
    (hp : ValidPath n src dst p) : src < n := by
  induction hp with
  | nil u hu => exact hu
  | cons hu _ _ _ => exact hu

/-- Fundamental path telescoping identity: for any valid directed path `p` from `src` to `dst`,
`inFlow n (pathEdgeFlow p) x - outFlow n (pathEdgeFlow p) x = indicator dst x - indicator src x`. -/
theorem path_netFlow_telescope {n src dst : Nat} {p : List (Nat × Nat)}
    (hp : ValidPath n src dst p) (x : Nat) :
    netFlow n (pathEdgeFlow p) x = indicator dst x - indicator src x := by
  induction hp with
  | nil u _ =>
    unfold netFlow inFlow outFlow
    simp only [pathEdgeFlow_nil, sumNodes_zero_fn, Int.sub_self]
  | @cons u w dst rest hu hw hrest ih =>
    unfold netFlow
    have hin := inFlow_cons_edge n u w x (pathEdgeFlow rest)
    have hout := outFlow_cons_edge n u w x (pathEdgeFlow rest)
    simp only [hu, hw, ↓reduceIte] at hin hout
    have hpath : pathEdgeFlow ((u, w) :: rest) =
        (fun a b => pathEdgeFlow rest a b + (if a == u && b == w then 1 else 0)) := rfl
    rw [hpath, hin, hout]
    have hnet : (inFlow n (pathEdgeFlow rest) x + indicator w x) -
        (outFlow n (pathEdgeFlow rest) x + indicator u x) =
        netFlow n (pathEdgeFlow rest) x + (indicator w x - indicator u x) := by
      rw [Int.sub_eq_add_neg]
      unfold netFlow
      rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg]
      rw [Int.neg_add]
      rw [Int.add_assoc (inFlow n (pathEdgeFlow rest) x) (indicator w x)
            (-outFlow n (pathEdgeFlow rest) x + -indicator u x)]
      rw [← Int.add_assoc (indicator w x) (-outFlow n (pathEdgeFlow rest) x) (-indicator u x)]
      rw [Int.add_comm (indicator w x) (-outFlow n (pathEdgeFlow rest) x)]
      rw [Int.add_assoc (-outFlow n (pathEdgeFlow rest) x) (indicator w x) (-indicator u x)]
      rw [← Int.add_assoc (inFlow n (pathEdgeFlow rest) x) (-outFlow n (pathEdgeFlow rest) x)
            (indicator w x + -indicator u x)]
    rw [hnet, ih]
    rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg]
    rw [Int.add_assoc, Int.add_left_comm (-indicator w x) (indicator w x) (-indicator u x)]
    rw [← Int.add_assoc (indicator w x) (-indicator w x) (-indicator u x)]
    rw [Int.add_right_neg, Int.zero_add]

theorem validPath_append {n a b c : Nat} {p q : List (Nat × Nat)}
    (hp : ValidPath n a b p) (hq : ValidPath n b c q) :
    ValidPath n a c (p ++ q) := by
  induction hp with
  | nil _ _ => exact hq
  | cons hu hw _ ih => exact ValidPath.cons hu hw (ih hq)

theorem validPath_lift {n m a b : Nat} {p : List (Nat × Nat)}
    (hnm : n ≤ m) (hp : ValidPath n a b p) : ValidPath m a b p := by
  induction hp with
  | nil u hu => exact ValidPath.nil u (Nat.lt_of_lt_of_le hu hnm)
  | cons hu hw _ ih =>
    exact ValidPath.cons (Nat.lt_of_lt_of_le hu hnm) (Nat.lt_of_lt_of_le hw hnm) ih

/-- Closing a normal execution path `p` from `startNode` to `exitNode` via
`exitNode -> sink` and `sink -> startNode` enforces exact Kirchhoff conservation at every node. -/
theorem kirchhoff_conservation_on_normal_trace (bf : BalancedFlowGraph)
    {exitNode : Nat} {p : List (Nat × Nat)}
    (hp : ValidPath bf.base.numNodes bf.base.startNode exitNode p)
    (x : Nat) :
    inFlow bf.totalNodes
      (pathEdgeFlow (p ++ [(exitNode, bf.sink), (bf.sink, bf.base.startNode)])) x =
    outFlow bf.totalNodes
      (pathEdgeFlow (p ++ [(exitNode, bf.sink), (bf.sink, bf.base.startNode)])) x := by
  have hle : bf.base.numNodes ≤ bf.totalNodes := Nat.le_succ bf.base.numNodes
  have hpLift : ValidPath bf.totalNodes bf.base.startNode exitNode p :=
    validPath_lift hle hp
  have hexit : exitNode < bf.totalNodes :=
    Nat.lt_of_lt_of_le (validPath_dst_lt hp) hle
  have hsink : bf.sink < bf.totalNodes := Nat.lt_succ_self bf.base.numNodes
  have hstart : bf.base.startNode < bf.totalNodes :=
    Nat.lt_of_lt_of_le bf.base.startLt hle
  have hclose : ValidPath bf.totalNodes exitNode bf.base.startNode
      [(exitNode, bf.sink), (bf.sink, bf.base.startNode)] :=
    ValidPath.cons hexit hsink
      (ValidPath.cons hsink hstart (ValidPath.nil bf.base.startNode hstart))
  have hcycle := validPath_append hpLift hclose
  have hnet := path_netFlow_telescope hcycle x
  rw [Int.sub_self] at hnet
  exact Int.sub_eq_zero.mp hnet

/-- Aggregate Kirchhoff conservation over an arbitrary finite batch of normal traces. -/
def batchBalancedEdgeFlow (bf : BalancedFlowGraph)
    (traces : List (Σ _exitNode : Nat, List (Nat × Nat))) (u v : Nat) : Int :=
  traces.foldr
    (fun tr acc u' v' =>
      acc u' v' +
        pathEdgeFlow (tr.2 ++ [(tr.1, bf.sink), (bf.sink, bf.base.startNode)]) u' v')
    (fun _ _ => 0) u v

theorem batchBalancedEdgeFlow_nil (bf : BalancedFlowGraph) (u v : Nat) :
    batchBalancedEdgeFlow bf [] u v = 0 := rfl

theorem batchBalancedEdgeFlow_cons (bf : BalancedFlowGraph)
    (tr : Σ _exitNode : Nat, List (Nat × Nat))
    (rest : List (Σ _exitNode : Nat, List (Nat × Nat))) :
    batchBalancedEdgeFlow bf (tr :: rest) =
      (fun u v =>
        batchBalancedEdgeFlow bf rest u v +
          pathEdgeFlow (tr.2 ++ [(tr.1, bf.sink), (bf.sink, bf.base.startNode)]) u v) := rfl

theorem kirchhoff_conservation_aggregate (bf : BalancedFlowGraph)
    (traces : List (Σ _exitNode : Nat, List (Nat × Nat)))
    (hvalid : ∀ tr, tr ∈ traces →
      ValidPath bf.base.numNodes bf.base.startNode tr.1 tr.2)
    (x : Nat) :
    inFlow bf.totalNodes (batchBalancedEdgeFlow bf traces) x =
      outFlow bf.totalNodes (batchBalancedEdgeFlow bf traces) x := by
  induction traces with
  | nil =>
    unfold inFlow outFlow
    simp only [batchBalancedEdgeFlow_nil, sumNodes_zero_fn]
  | cons tr rest ih =>
    have htr : ValidPath bf.base.numNodes bf.base.startNode tr.1 tr.2 :=
      hvalid tr List.mem_cons_self
    have hrest : ∀ r, r ∈ rest →
        ValidPath bf.base.numNodes bf.base.startNode r.1 r.2 :=
      fun r hr => hvalid r (List.mem_cons_of_mem tr hr)
    have ihv := ih hrest
    have hsingle := kirchhoff_conservation_on_normal_trace bf htr x
    rw [batchBalancedEdgeFlow_cons]
    unfold inFlow outFlow
    rw [sumNodes_add, sumNodes_add]
    unfold inFlow outFlow at ihv hsingle
    rw [ihv, hsingle]

/-- Exact Kirchhoff deficit on an unwinding execution trace that starts at `startNode`
and aborts/unwinds at `unwindNode` without reaching `sink`. -/
theorem unwind_trace_deficit_exact (bf : BalancedFlowGraph)
    {unwindNode : Nat} {p : List (Nat × Nat)}
    (hp : ValidPath bf.base.numNodes bf.base.startNode unwindNode p) :
    (unwindNode ≠ bf.base.startNode →
      netFlow bf.totalNodes (pathEdgeFlow p) unwindNode = 1 ∧
        netFlow bf.totalNodes (pathEdgeFlow p) bf.base.startNode = -1) ∧
      netFlow bf.totalNodes (pathEdgeFlow p) bf.sink = 0 := by
  have hle : bf.base.numNodes ≤ bf.totalNodes := Nat.le_succ bf.base.numNodes
  have hpLift : ValidPath bf.totalNodes bf.base.startNode unwindNode p :=
    validPath_lift hle hp
  have huLt : unwindNode < bf.base.numNodes := validPath_dst_lt hp
  have hsLt : bf.base.startNode < bf.base.numNodes := bf.base.startLt
  constructor
  · intro hne
    have h1 := path_netFlow_telescope hpLift unwindNode
    have h2 := path_netFlow_telescope hpLift bf.base.startNode
    have hneSym : bf.base.startNode ≠ unwindNode := Ne.symm hne
    have hiu : indicator unwindNode unwindNode = 1 := by
      unfold indicator; simp only [natBeq_self, ↓reduceIte]
    have hisu : indicator bf.base.startNode unwindNode = 0 := by
      unfold indicator; simp only [natBeq_ne hne, Bool.false_eq_true, ↓reduceIte]
    have hius : indicator unwindNode bf.base.startNode = 0 := by
      unfold indicator; simp only [natBeq_ne hneSym, Bool.false_eq_true, ↓reduceIte]
    have his : indicator bf.base.startNode bf.base.startNode = 1 := by
      unfold indicator; simp only [natBeq_self, ↓reduceIte]
    rw [hiu, hisu, Int.sub_zero] at h1
    rw [hius, his, Int.zero_sub] at h2
    exact ⟨h1, h2⟩
  · have h3 := path_netFlow_telescope hpLift bf.sink
    have hne1 : bf.sink ≠ unwindNode :=
      Nat.ne_of_gt huLt
    have hne2 : bf.sink ≠ bf.base.startNode :=
      Nat.ne_of_gt hsLt
    have h1 : indicator unwindNode bf.sink = 0 := by
      unfold indicator; simp only [natBeq_ne hne1, Bool.false_eq_true, ↓reduceIte]
    have h2 : indicator bf.base.startNode bf.sink = 0 := by
      unfold indicator; simp only [natBeq_ne hne2, Bool.false_eq_true, ↓reduceIte]
    rw [h1, h2, Int.sub_zero] at h3
    exact h3

/-- Intra-BCB post-call phantom execution error: when `bb_pre -> Call -> bb_post`
is chained into a single BCB (`bcb_filtered_successors`), a BCB counter records
`entries = normalReturns + unwinds` while `bb_post` executes only `normalReturns` times. -/
theorem intra_bcb_post_call_phantom_count (normalReturns unwinds : Nat) :
    ((normalReturns + unwinds : Nat) : Int) - (normalReturns : Int) = (unwinds : Int) := by
  rw [Int.natCast_add, Int.sub_eq_add_neg, Int.add_assoc,
      Int.add_comm (unwinds : Int) (-(normalReturns : Int)),
      ← Int.add_assoc, Int.add_right_neg, Int.zero_add]

/-! ## Section 3: Supernode Contraction & Knuth–Stevenson Spanning-Tree Reconstruction (`node_flow.rs`) -/

/-- A balanced node-flow state on `n` nodes where each node's flow equals both
its total incoming edge flow and its total outgoing edge flow. -/
structure BalancedNodeFlow where
  n : Nat
  edgeFlow : EdgeFlow
  nodeFlow : Nat → Int
  outEq : ∀ u, u < n → nodeFlow u = outFlow n edgeFlow u
  inEq : ∀ v, v < n → nodeFlow v = inFlow n edgeFlow v

/-- Supernode contraction satisfying `node_flow_data_for_balanced_graph` (`node_flow.rs:27-52`). -/
structure SupernodeContract (bnf : BalancedNodeFlow) where
  m : Nat
  supernode : Nat → Nat
  succSupernode : Nat → Nat
  snLt : ∀ u, u < bnf.n → supernode u < m
  ssnLt : ∀ u, u < bnf.n → succSupernode u < m
  edgeCompat : ∀ u v, u < bnf.n → v < bnf.n → bnf.edgeFlow u v ≠ 0 →
    supernode v = succSupernode u

theorem supernode_in_out_balanced (bnf : BalancedNodeFlow) (sc : SupernodeContract bnf)
    (s : Nat) :
    sumNodes bnf.n (fun u => if sc.succSupernode u == s then bnf.nodeFlow u else 0) =
      sumNodes bnf.n (fun u => if sc.supernode u == s then bnf.nodeFlow u else 0) := by
  have hLHS :
      sumNodes bnf.n (fun u => if sc.succSupernode u == s then bnf.nodeFlow u else 0) =
        sumNodes bnf.n (fun u =>
          if sc.succSupernode u == s then outFlow bnf.n bnf.edgeFlow u else 0) := by
    apply sumNodes_ext
    intro u hu
    by_cases heq : sc.succSupernode u = s
    · have ht : (sc.succSupernode u == s) = true := beq_iff_eq.mpr heq
      simp only [ht, ↓reduceIte, bnf.outEq u hu]
    · have hf : (sc.succSupernode u == s) = false := natBeq_ne heq
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
  have hRHS :
      sumNodes bnf.n (fun v => if sc.supernode v == s then bnf.nodeFlow v else 0) =
        sumNodes bnf.n (fun v =>
          if sc.supernode v == s then inFlow bnf.n bnf.edgeFlow v else 0) := by
    apply sumNodes_ext
    intro v hv
    by_cases heq : sc.supernode v = s
    · have ht : (sc.supernode v == s) = true := beq_iff_eq.mpr heq
      simp only [ht, ↓reduceIte, bnf.inEq v hv]
    · have hf : (sc.supernode v == s) = false := natBeq_ne heq
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [hLHS, hRHS]
  have hExpandLHS :
      sumNodes bnf.n (fun u =>
        if sc.succSupernode u == s then outFlow bnf.n bnf.edgeFlow u else 0) =
        sumNodes bnf.n (fun u => sumNodes bnf.n (fun v =>
          if sc.succSupernode u == s then bnf.edgeFlow u v else 0)) := by
    apply sumNodes_ext
    intro u _
    by_cases heq : sc.succSupernode u = s
    · have ht : (sc.succSupernode u == s) = true := beq_iff_eq.mpr heq
      simp only [ht, ↓reduceIte]
      rfl
    · have hf : (sc.succSupernode u == s) = false := natBeq_ne heq
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      symm
      exact sumNodes_zero_fn bnf.n
  have hExpandRHS :
      sumNodes bnf.n (fun v =>
        if sc.supernode v == s then inFlow bnf.n bnf.edgeFlow v else 0) =
        sumNodes bnf.n (fun v => sumNodes bnf.n (fun u =>
          if sc.supernode v == s then bnf.edgeFlow u v else 0)) := by
    apply sumNodes_ext
    intro v _
    by_cases heq : sc.supernode v = s
    · have ht : (sc.supernode v == s) = true := beq_iff_eq.mpr heq
      simp only [ht, ↓reduceIte]
      rfl
    · have hf : (sc.supernode v == s) = false := natBeq_ne heq
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      symm
      exact sumNodes_zero_fn bnf.n
  rw [hExpandLHS, hExpandRHS, sumNodes_swap bnf.n bnf.n]
  apply sumNodes_ext
  intro v hv
  apply sumNodes_ext
  intro u hu
  by_cases hnz : bnf.edgeFlow u v = 0
  · rw [hnz]
    split <;> split <;> rfl
  · have hcompat : sc.supernode v = sc.succSupernode u := sc.edgeCompat u v hu hv hnz
    rw [hcompat]

/-- Signed cut orientation for directed supernode edge `a -> b` relative to cut `S`.
Returns `+1` if entering `S` (`!S a ∧ S b`), `-1` if leaving `S` (`S a ∧ !S b`), `0` otherwise. -/
def cutSign (S : Nat → Bool) (a b : Nat) : Int :=
  (if S b then (1 : Int) else 0) - (if S a then (1 : Int) else 0)

theorem cutSign_anti (S : Nat → Bool) (a b : Nat) :
    cutSign S b a = -cutSign S a b := by
  unfold cutSign
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_comm]

theorem cutSign_same {S : Nat → Bool} {a b : Nat} (h : S a = S b) :
    cutSign S a b = 0 := by
  unfold cutSign
  rw [h, Int.sub_self]

/-- Fundamental Cut Conservation Theorem: for ANY balanced supernode-contracted flow
and ANY boolean subset `S : Nat → Bool` of supernodes, the cut-signed sum of node flows vanishes. -/
theorem supernode_cut_conservation (bnf : BalancedNodeFlow) (sc : SupernodeContract bnf)
    (S : Nat → Bool) :
    sumNodes bnf.n (fun u => cutSign S (sc.supernode u) (sc.succSupernode u) * bnf.nodeFlow u) = 0 := by
  have h1 :
      sumNodes bnf.n (fun u => cutSign S (sc.supernode u) (sc.succSupernode u) * bnf.nodeFlow u) =
        sumNodes bnf.n (fun u =>
          (if S (sc.succSupernode u) then bnf.nodeFlow u else 0) -
            (if S (sc.supernode u) then bnf.nodeFlow u else 0)) := by
    apply sumNodes_ext
    intro u _
    unfold cutSign
    cases hsb : S (sc.succSupernode u) <;> cases hsa : S (sc.supernode u) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.sub_self, Int.zero_mul,
        Int.sub_zero, Int.one_mul, Int.zero_sub, Int.neg_one_mul]
  rw [h1, sumNodes_sub]
  have hSucc :
      sumNodes bnf.n (fun u => if S (sc.succSupernode u) then bnf.nodeFlow u else 0) =
        sumNodes sc.m (fun s =>
          if S s then sumNodes bnf.n (fun u => if sc.succSupernode u == s then bnf.nodeFlow u else 0)
          else 0) := by
    rw [← sumNodes_fiber sc.succSupernode
            (fun u => if S (sc.succSupernode u) then bnf.nodeFlow u else 0) sc.ssnLt]
    apply sumNodes_ext
    intro s _
    by_cases hSs : S s = true
    · simp only [hSs, ↓reduceIte]
      apply sumNodes_ext
      intro u _
      by_cases heq : sc.succSupernode u = s
      · simp only [heq, natBeq_self, ↓reduceIte, hSs]
      · have hf : (sc.succSupernode u == s) = false := natBeq_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
    · have hSsf : S s = false := Bool.eq_false_iff.mpr hSs
      simp only [hSsf, Bool.false_eq_true, ↓reduceIte]
      refine Eq.trans (sumNodes_ext ?_) (sumNodes_zero_fn bnf.n)
      intro u _
      by_cases heq : sc.succSupernode u = s
      · simp only [heq, natBeq_self, ↓reduceIte, hSsf, Bool.false_eq_true]
      · have hf : (sc.succSupernode u == s) = false := natBeq_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
  have hPred :
      sumNodes bnf.n (fun u => if S (sc.supernode u) then bnf.nodeFlow u else 0) =
        sumNodes sc.m (fun s =>
          if S s then sumNodes bnf.n (fun u => if sc.supernode u == s then bnf.nodeFlow u else 0)
          else 0) := by
    rw [← sumNodes_fiber sc.supernode
            (fun u => if S (sc.supernode u) then bnf.nodeFlow u else 0) sc.snLt]
    apply sumNodes_ext
    intro s _
    by_cases hSs : S s = true
    · simp only [hSs, ↓reduceIte]
      apply sumNodes_ext
      intro u _
      by_cases heq : sc.supernode u = s
      · simp only [heq, natBeq_self, ↓reduceIte, hSs]
      · have hf : (sc.supernode u == s) = false := natBeq_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
    · have hSsf : S s = false := Bool.eq_false_iff.mpr hSs
      simp only [hSsf, Bool.false_eq_true, ↓reduceIte]
      refine Eq.trans (sumNodes_ext ?_) (sumNodes_zero_fn bnf.n)
      intro u _
      by_cases heq : sc.supernode u = s
      · simp only [heq, natBeq_self, ↓reduceIte, hSsf, Bool.false_eq_true]
      · have hf : (sc.supernode u == s) = false := natBeq_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [hSucc, hPred]
  have hEq :
      sumNodes sc.m (fun s =>
        if S s then sumNodes bnf.n (fun u => if sc.succSupernode u == s then bnf.nodeFlow u else 0)
        else 0) =
      sumNodes sc.m (fun s =>
        if S s then sumNodes bnf.n (fun u => if sc.supernode u == s then bnf.nodeFlow u else 0)
        else 0) := by
    apply sumNodes_ext
    intro s _
    by_cases hSs : S s = true
    · simp only [hSs, ↓reduceIte]
      exact supernode_in_out_balanced bnf sc s
    · have hSsf : S s = false := Bool.eq_false_iff.mpr hSs
      simp only [hSsf, Bool.false_eq_true, ↓reduceIte]
  rw [hEq, Int.sub_self]

/-- Counter expression operators (`rustc_middle::mir::coverage::Op`). -/
inductive CovOp where
  | add
  | subtract

def CovOp.beq : CovOp → CovOp → Bool
  | .add, .add => true
  | .subtract, .subtract => true
  | _, _ => false

structure CounterTerm where
  op : CovOp
  node : Nat

def evalCounterTerms (terms : List CounterTerm) (flow : Nat → Int) : Int :=
  terms.foldl (fun acc t =>
    match t.op with
    | .add => acc + flow t.node
    | .subtract => acc - flow t.node) 0

theorem evalCounterTerms_append (ts1 ts2 : List CounterTerm) (flow : Nat → Int) :
    evalCounterTerms (ts1 ++ ts2) flow =
      evalCounterTerms ts1 flow + evalCounterTerms ts2 flow := by
  unfold evalCounterTerms
  rw [List.foldl_append]
  have hshift : ∀ (xs : List CounterTerm) (init : Int),
      xs.foldl (fun acc t => match t.op with
        | .add => acc + flow t.node
        | .subtract => acc - flow t.node) init =
      init + xs.foldl (fun acc t => match t.op with
        | .add => acc + flow t.node
        | .subtract => acc - flow t.node) 0 := by
    intro xs
    induction xs with
    | nil =>
      intro init
      simp only [List.foldl_nil, Int.add_zero]
    | cons x rest ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih, ih (match x.op with | .add => 0 + flow x.node | .subtract => 0 - flow x.node)]
      cases x.op
      · simp only [Int.zero_add, Int.add_assoc]
      · simp only [Int.sub_eq_add_neg, Int.zero_add, Int.add_assoc]
  exact hshift ts2 _

theorem evalCounterTerms_single (t : CounterTerm) (flow : Nat → Int) :
    evalCounterTerms [t] flow =
      match t.op with | .add => flow t.node | .subtract => -flow t.node := by
  unfold evalCounterTerms
  simp only [List.foldl_cons, List.foldl_nil]
  cases t.op
  · exact Int.zero_add _
  · exact Int.zero_sub _

/-- Spanning-tree cut decomposition certificate:
each node `u < n` is either a chord (`isTreeEdge u = false`, owning a physical counter)
or a tree-edge claimant (`isTreeEdge u = true`) paired with a fundamental cut `treeCut u : Nat → Bool`
that separates `sn u` (`true`) from `ssn u` (`false`) and avoids crossing any other tree edge `v ≠ u`. -/
structure SpanTreeCutDecomposition (bnf : BalancedNodeFlow) (sc : SupernodeContract bnf) where
  isTreeEdge : Nat → Bool
  treeCut : Nat → Nat → Bool
  cutSeparates : ∀ t, t < bnf.n → isTreeEdge t = true →
    treeCut t (sc.supernode t) = true ∧ treeCut t (sc.succSupernode t) = false
  cutRespectsOtherTreeEdges : ∀ t v, t < bnf.n → v < bnf.n →
    isTreeEdge t = true → isTreeEdge v = true → v ≠ t →
    treeCut t (sc.supernode v) = treeCut t (sc.succSupernode v)

def cutSignToTerms {bnf : BalancedNodeFlow} {sc : SupernodeContract bnf}
    (decomp : SpanTreeCutDecomposition bnf sc) (t : Nat) (n : Nat) : List CounterTerm :=
  Nat.rec (motive := fun _ => List CounterTerm) []
    (fun k rest =>
      if decomp.isTreeEdge k then rest
      else
        let cs := cutSign (decomp.treeCut t) (sc.supernode k) (sc.succSupernode k)
        if cs == 1 then rest ++ [{ op := .add, node := k }]
        else if cs == -1 then rest ++ [{ op := .subtract, node := k }]
        else rest) n

theorem cutSignToTerms_succ {bnf : BalancedNodeFlow} {sc : SupernodeContract bnf}
    (decomp : SpanTreeCutDecomposition bnf sc) (t k : Nat) :
    cutSignToTerms decomp t (k + 1) =
      let rest := cutSignToTerms decomp t k
      if decomp.isTreeEdge k then rest
      else
        let cs := cutSign (decomp.treeCut t) (sc.supernode k) (sc.succSupernode k)
        if cs == 1 then rest ++ [{ op := .add, node := k }]
        else if cs == -1 then rest ++ [{ op := .subtract, node := k }]
        else rest := rfl

theorem eval_cutSignToTerms_eq {bnf : BalancedNodeFlow} {sc : SupernodeContract bnf}
    (decomp : SpanTreeCutDecomposition bnf sc) (t k : Nat) :
    evalCounterTerms (cutSignToTerms decomp t k) bnf.nodeFlow =
      sumNodes k (fun v =>
        if decomp.isTreeEdge v then 0
        else cutSign (decomp.treeCut t) (sc.supernode v) (sc.succSupernode v) * bnf.nodeFlow v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cutSignToTerms_succ, sumNodes_succ_eq]
    by_cases htk : decomp.isTreeEdge k = true
    · simp only [htk, ↓reduceIte, ih, Int.add_zero]
    · have htkf : decomp.isTreeEdge k = false := Bool.eq_false_iff.mpr htk
      simp only [htkf, Bool.false_eq_true, ↓reduceIte]
      have hcs : cutSign (decomp.treeCut t) (sc.supernode k) (sc.succSupernode k) = 1 ∨
          cutSign (decomp.treeCut t) (sc.supernode k) (sc.succSupernode k) = -1 ∨
          cutSign (decomp.treeCut t) (sc.supernode k) (sc.succSupernode k) = 0 := by
        unfold cutSign
        cases decomp.treeCut t (sc.succSupernode k) <;>
          cases decomp.treeCut t (sc.supernode k) <;> simp
      rcases hcs with h1 | hm1 | h0
      · rw [h1]
        have heq1 : ((1 : Int) == 1) = true := rfl
        simp only [heq1, ↓reduceIte, evalCounterTerms_append, ih, evalCounterTerms_single,
          Int.one_mul]
      · rw [hm1]
        have hne1 : ((-1 : Int) == 1) = false := rfl
        have heqm1 : ((-1 : Int) == -1) = true := rfl
        simp only [hne1, Bool.false_eq_true, ↓reduceIte, heqm1,
          evalCounterTerms_append, ih, evalCounterTerms_single, Int.neg_one_mul]
      · rw [h0]
        have hne1 : ((0 : Int) == 1) = false := rfl
        have hnem1 : ((0 : Int) == -1) = false := rfl
        simp only [hne1, hnem1, Bool.false_eq_true, ↓reduceIte, ih, Int.zero_mul, Int.add_zero]

/-- **Knuth–Stevenson Spanning-Tree Cut Reconstruction Theorem**:
Under balanced supernode flow, every tree-edge node `t` has its exact flow `nodeFlow t`
reconstructed by summing `+c` / `-c` over the chords crossing `treeCut t`. -/
theorem spantree_cut_reconstruction_exact (bnf : BalancedNodeFlow) (sc : SupernodeContract bnf)
    (decomp : SpanTreeCutDecomposition bnf sc) (t : Nat) (htLt : t < bnf.n)
    (htTree : decomp.isTreeEdge t = true) :
    evalCounterTerms (cutSignToTerms decomp t bnf.n) bnf.nodeFlow = bnf.nodeFlow t := by
  rw [eval_cutSignToTerms_eq]
  have hcons := supernode_cut_conservation bnf sc (decomp.treeCut t)
  have hSplit :
      sumNodes bnf.n (fun v =>
        cutSign (decomp.treeCut t) (sc.supernode v) (sc.succSupernode v) * bnf.nodeFlow v) =
      sumNodes bnf.n (fun v =>
        if decomp.isTreeEdge v then 0
        else cutSign (decomp.treeCut t) (sc.supernode v) (sc.succSupernode v) * bnf.nodeFlow v) +
      sumNodes bnf.n (fun v => if v == t then -bnf.nodeFlow v else 0) := by
    rw [← sumNodes_add]
    apply sumNodes_ext
    intro v hv
    by_cases hvt : v = t
    · subst hvt
      simp only [htTree, ↓reduceIte, natBeq_self, Int.zero_add]
      have hsep := decomp.cutSeparates v hv htTree
      unfold cutSign
      simp only [hsep.1, hsep.2, Bool.false_eq_true, ↓reduceIte, Int.zero_sub, Int.neg_one_mul]
    · have hvtf : (v == t) = false := natBeq_ne hvt
      simp only [hvtf, Bool.false_eq_true, ↓reduceIte, Int.add_zero]
      by_cases hvTree : decomp.isTreeEdge v = true
      · simp only [hvTree, ↓reduceIte]
        have hsame := decomp.cutRespectsOtherTreeEdges t v htLt hv htTree hvTree hvt
        rw [cutSign_same hsame, Int.zero_mul]
      · have hvTreef : decomp.isTreeEdge v = false := Bool.eq_false_iff.mpr hvTree
        simp only [hvTreef, Bool.false_eq_true, ↓reduceIte]
  rw [hSplit] at hcons
  have hsingle : sumNodes bnf.n (fun v => if v == t then -bnf.nodeFlow v else 0) =
      -bnf.nodeFlow t := by
    have hconst : sumNodes bnf.n (fun v => if v == t then -bnf.nodeFlow t else 0) =
        -bnf.nodeFlow t := sumNodes_single bnf.n t (-bnf.nodeFlow t) htLt
    rw [← hconst]
    apply sumNodes_ext
    intro v _
    by_cases hvt : v = t
    · subst hvt; rfl
    · have hvtf : (v == t) = false := natBeq_ne hvt
      simp only [hvtf, Bool.false_eq_true, ↓reduceIte]
  rw [hsingle] at hcons
  calc
    sumNodes bnf.n (fun v =>
      if decomp.isTreeEdge v then 0
      else cutSign (decomp.treeCut t) (sc.supernode v) (sc.succSupernode v) * bnf.nodeFlow v)
      = sumNodes bnf.n (fun v =>
          if decomp.isTreeEdge v then 0
          else cutSign (decomp.treeCut t) (sc.supernode v) (sc.succSupernode v) * bnf.nodeFlow v) +
          (-bnf.nodeFlow t + bnf.nodeFlow t) := by
            rw [Int.add_left_neg, Int.add_zero]
    _ = (sumNodes bnf.n (fun v =>
          if decomp.isTreeEdge v then 0
          else cutSign (decomp.treeCut t) (sc.supernode v) (sc.succSupernode v) * bnf.nodeFlow v) +
          -bnf.nodeFlow t) + bnf.nodeFlow t := by
            rw [← Int.add_assoc]
    _ = 0 + bnf.nodeFlow t := by rw [hcons]
    _ = bnf.nodeFlow t := Int.zero_add _

/-! ### Executable Knuth–Stevenson `SpantreeBuilder` (`node_flow.rs:112-275`) -/

structure SpantreeEdge where
  isReversed : Bool
  claimingNode : Nat
  spanParent : Nat

structure SpantreeState where
  numNodes : Nat
  supernodes : Nat → Nat
  succSupernodes : Nat → Nat
  spanEdges : Nat → Option SpantreeEdge
  terms : Nat → List CounterTerm

def spantreeRootFuel (fuel : Nat) (edges : Nat → Option SpantreeEdge) (curr : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun _ ih c =>
      match edges c with
      | none => c
      | some e => ih e.spanParent) fuel curr

def collectPathFuel (fuel : Nat) (edges : Nat → Option SpantreeEdge) (curr : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun c => [c])
    (fun _ ih c =>
      match edges c with
      | none => [c]
      | some e => c :: ih e.spanParent) fuel curr

def reversePairStep (a : Nat) (acc : Option Nat × (Nat → Option SpantreeEdge)) :
    Option Nat × (Nat → Option SpantreeEdge) :=
  match acc.1 with
  | none => (some a, acc.2)
  | some b =>
    let edges' := acc.2
    let edges'' :=
      match edges' a with
      | none => edges'
      | some ea =>
        fun x =>
          if x == a then none
          else if x == b then
            some { isReversed := !ea.isReversed, claimingNode := ea.claimingNode, spanParent := a }
          else edges' x
    (some a, edges'')

def reversePairList (path : List Nat) (edges : Nat → Option SpantreeEdge) :
    Nat → Option SpantreeEdge :=
  (path.foldr reversePairStep (none, edges)).2

def yankToRoot (st : SpantreeState) (thisSuper : Nat) : SpantreeState :=
  let path := collectPathFuel st.numNodes st.spanEdges thisSuper
  { st with spanEdges := reversePairList path st.spanEdges }

def appendTerm (terms : Nat → List CounterTerm) (node : Nat) (term : CounterTerm) :
    Nat → List CounterTerm :=
  fun x => if x == node then terms node ++ [term] else terms x

def walkCycleTermsFuel (fuel : Nat) (edges : Nat → Option SpantreeEdge)
    (curr targetRoot chordNode : Nat) (terms : Nat → List CounterTerm) :
    Nat → List CounterTerm :=
  Nat.rec (motive := fun _ => Nat → (Nat → List CounterTerm) → (Nat → List CounterTerm))
    (fun _ t => t)
    (fun _ ih c t =>
      if c == targetRoot then t
      else
        match edges c with
        | none => t
        | some e =>
          let op := if e.isReversed then CovOp.subtract else CovOp.add
          let t' := appendTerm t e.claimingNode { op := op, node := chordNode }
          ih e.spanParent t') fuel curr terms

def spantreeVisitNode (st : SpantreeState) (this : Nat) : SpantreeState :=
  let thisSuper := st.supernodes this
  let st1 := yankToRoot st thisSuper
  let succSuper := st1.succSupernodes this
  let rootSucc := spantreeRootFuel st1.numNodes st1.spanEdges succSuper
  if thisSuper != rootSucc then
    let newEdge : SpantreeEdge :=
      { isReversed := false, claimingNode := this, spanParent := succSuper }
    { st1 with spanEdges := fun x => if x == thisSuper then some newEdge else st1.spanEdges x }
  else
    let terms1 := appendTerm st1.terms this { op := .add, node := this }
    let terms2 := walkCycleTermsFuel st1.numNodes st1.spanEdges succSuper thisSuper this terms1
    { st1 with terms := terms2 }

def spantreeRunPriorityList (numNodes : Nat) (supernodes succSupernodes : Nat → Nat)
    (priorityList : List Nat) : SpantreeState :=
  let init : SpantreeState :=
    { numNodes := numNodes
      supernodes := supernodes
      succSupernodes := succSupernodes
      spanEdges := fun _ => none
      terms := fun _ => [] }
  priorityList.foldl spantreeVisitNode init

/-- Tree-root membership predicate: tests whether walking `fuel` parent steps from `x`
passes through `targetEdgeNode`. -/
def reachesThroughFuel (fuel : Nat) (edges : Nat → Option SpantreeEdge)
    (target x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => c == target)
    (fun _ ih c =>
      if c == target then true
      else
        match edges c with
        | none => false
        | some e => ih e.spanParent) fuel x

theorem reachesThroughFuel_zero (edges : Nat → Option SpantreeEdge) (target x : Nat) :
    reachesThroughFuel 0 edges target x = (x == target) := rfl

theorem reachesThroughFuel_succ (fuel : Nat) (edges : Nat → Option SpantreeEdge)
    (target x : Nat) :
    reachesThroughFuel (fuel + 1) edges target x =
      (if x == target then true
       else
         match edges x with
         | none => false
         | some e => reachesThroughFuel fuel edges target e.spanParent) := rfl

theorem reachesThroughFuel_self (fuel : Nat) (edges : Nat → Option SpantreeEdge) (a : Nat) :
    reachesThroughFuel fuel edges a a = true := by
  cases fuel with
  | zero => rw [reachesThroughFuel_zero]; exact natBeq_self a
  | succ f =>
    rw [reachesThroughFuel_succ]
    simp only [natBeq_self, ↓reduceIte]

theorem reachesThroughFuel_step_other {fuel : Nat} {edges : Nat → Option SpantreeEdge}
    {a c : Nat} {ec : SpantreeEdge} (hne : c ≠ a) (hed : edges c = some ec) :
    reachesThroughFuel (fuel + 1) edges a c = reachesThroughFuel fuel edges a ec.spanParent := by
  rw [reachesThroughFuel_succ]
  simp only [natBeq_ne hne, Bool.false_eq_true, ↓reduceIte, hed]

/-! ## Section 4: `transcribe_counters`, Dead-BCB Pruning (`query.rs`), & LLVM `int64_t -> uint64_t` Semantics -/

/-- Counter expression terms (`rustc_middle::mir::coverage::CovTerm`). -/
inductive CovTerm where
  | zero
  | physCounter (id : Nat)
  | exprAdd (lhs rhs : CovTerm)
  | exprSub (lhs rhs : CovTerm)

noncomputable def evalCovTerm (cnts : Nat → Int) (t : CovTerm) : Int :=
  CovTerm.rec (motive := fun _ => Int) 0 (fun id => cnts id)
    (fun _ _ vl vr => vl + vr) (fun _ _ vl vr => vl - vr) t

def makeSumTerm : List Nat → Option CovTerm
  | [] => none
  | x :: xs =>
    some (xs.foldl (fun acc y => CovTerm.exprAdd acc (CovTerm.physCounter y))
      (CovTerm.physCounter x))

def makeSubtractedSumTerm (lhs : CovTerm) (rhs : List Nat) : CovTerm :=
  match makeSumTerm rhs with
  | none => lhs
  | some rhsSum => CovTerm.exprSub lhs rhsSum

/-- Models `transcribe_counters` (`counters.rs:79-121`). -/
def transcribeTerms (seen : Nat → Bool) (terms : List CounterTerm) : CovTerm :=
  let filtered := terms.filter (fun t => seen t.node)
  let pos := (filtered.filter (fun t => t.op.beq .add)).map (·.node)
  let neg := (filtered.filter (fun t => t.op.beq .subtract)).map (·.node)
  let posTerm := (makeSumTerm pos).getD CovTerm.zero
  makeSubtractedSumTerm posTerm neg

theorem eval_makeSumTerm_foldl (xs : List Nat) (init : CovTerm) (cnts : Nat → Int) :
    evalCovTerm cnts
      (xs.foldl (fun acc y => CovTerm.exprAdd acc (CovTerm.physCounter y)) init) =
    evalCovTerm cnts init +
      xs.foldl (fun acc y => acc + cnts y) 0 := by
  have hgen : ∀ (ys : List Nat) (t0 : CovTerm) (z0 : Int),
      evalCovTerm cnts
        (ys.foldl (fun acc y => CovTerm.exprAdd acc (CovTerm.physCounter y)) t0) -
      evalCovTerm cnts t0 =
      ys.foldl (fun acc y => acc + cnts y) z0 - z0 := by
    intro ys
    induction ys with
    | nil =>
      intro t0 z0
      simp only [List.foldl_nil, Int.sub_self]
    | cons y rest ih =>
      intro t0 z0
      simp only [List.foldl_cons]
      have h1 := ih (CovTerm.exprAdd t0 (CovTerm.physCounter y)) (z0 + cnts y)
      have h2 : evalCovTerm cnts (CovTerm.exprAdd t0 (CovTerm.physCounter y)) =
          evalCovTerm cnts t0 + cnts y := rfl
      rw [h2] at h1
      rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg] at h1 ⊢
      have hcancelL :
          (evalCovTerm cnts
            (rest.foldl (fun acc y => CovTerm.exprAdd acc (CovTerm.physCounter y))
              (CovTerm.exprAdd t0 (CovTerm.physCounter y))) +
           -(evalCovTerm cnts t0 + cnts y)) + cnts y =
          evalCovTerm cnts
            (rest.foldl (fun acc y => CovTerm.exprAdd acc (CovTerm.physCounter y))
              (CovTerm.exprAdd t0 (CovTerm.physCounter y))) +
           -(evalCovTerm cnts t0) := by
        rw [Int.neg_add, Int.add_assoc, Int.add_assoc, Int.add_left_neg, Int.add_zero]
      have hcancelR :
          (rest.foldl (fun acc y => acc + cnts y) (z0 + cnts y) + -(z0 + cnts y)) + cnts y =
          rest.foldl (fun acc y => acc + cnts y) (z0 + cnts y) + -z0 := by
        rw [Int.neg_add, Int.add_assoc, Int.add_assoc, Int.add_left_neg, Int.add_zero]
      rw [← hcancelL, h1, hcancelR]
  have h0 := hgen xs init 0
  rw [Int.sub_zero] at h0
  rw [← h0, Int.add_comm, Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_neg, Int.add_zero]

def sumListInt (xs : List Nat) (cnts : Nat → Int) : Int :=
  xs.foldl (fun acc y => acc + cnts y) 0

theorem sumListInt_cons (x : Nat) (xs : List Nat) (cnts : Nat → Int) :
    sumListInt (x :: xs) cnts = cnts x + sumListInt xs cnts := by
  unfold sumListInt
  simp only [List.foldl_cons, Int.zero_add]
  have hshift : ∀ (ys : List Nat) (a : Int),
      ys.foldl (fun acc y => acc + cnts y) a =
        a + ys.foldl (fun acc y => acc + cnts y) 0 := by
    intro ys
    induction ys with
    | nil => intro a; simp only [List.foldl_nil, Int.add_zero]
    | cons y rest ih =>
      intro a
      simp only [List.foldl_cons, Int.zero_add]
      rw [ih (a + cnts y), ih (cnts y), Int.add_assoc]
  exact hshift xs (cnts x)

theorem eval_makeSumTerm_opt (xs : List Nat) (cnts : Nat → Int) :
    evalCovTerm cnts ((makeSumTerm xs).getD CovTerm.zero) = sumListInt xs cnts := by
  cases xs with
  | nil => rfl
  | cons x rest =>
    unfold makeSumTerm
    simp only [Option.getD_some]
    rw [eval_makeSumTerm_foldl, sumListInt_cons]
    rfl

theorem eval_makeSubtractedSumTerm (lhs : CovTerm) (rhs : List Nat) (cnts : Nat → Int) :
    evalCovTerm cnts (makeSubtractedSumTerm lhs rhs) =
      evalCovTerm cnts lhs - sumListInt rhs cnts := by
  unfold makeSubtractedSumTerm
  cases rhs with
  | nil =>
    unfold makeSumTerm sumListInt
    simp only [List.foldl_nil, Int.sub_zero]
  | cons y rest =>
    unfold makeSumTerm
    simp only []
    have h := eval_makeSumTerm_foldl rest (CovTerm.physCounter y) cnts
    change evalCovTerm cnts lhs -
        evalCovTerm cnts (rest.foldl (fun acc z => CovTerm.exprAdd acc (CovTerm.physCounter z))
          (CovTerm.physCounter y)) =
      evalCovTerm cnts lhs - sumListInt (y :: rest) cnts
    rw [h, sumListInt_cons]
    rfl

theorem eval_pos_minus_neg_eq_evalCounterTerms (ts : List CounterTerm) (cnts : Nat → Int) :
    sumListInt ((ts.filter (fun t => t.op.beq .add)).map (·.node)) cnts -
      sumListInt ((ts.filter (fun t => t.op.beq .subtract)).map (·.node)) cnts =
    evalCounterTerms ts cnts := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    have hstep : evalCounterTerms (t :: rest) cnts =
        evalCounterTerms [t] cnts + evalCounterTerms rest cnts := by
      have hcat : t :: rest = [t] ++ rest := rfl
      rw [hcat, evalCounterTerms_append]
    rw [hstep, ← ih, evalCounterTerms_single]
    cases t with
    | mk op node =>
      cases op
      · simp only [List.filter_cons, CovOp.beq, ↓reduceIte, Bool.false_eq_true,
          List.map_cons, sumListInt_cons]
        rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_assoc]
      · simp only [List.filter_cons, CovOp.beq, Bool.false_eq_true, ↓reduceIte,
          List.map_cons, sumListInt_cons]
        rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.neg_add,
          Int.add_comm (-cnts node) (-sumListInt _ cnts),
          ← Int.add_assoc, Int.add_comm _ (-cnts node)]

/-- **Transcription Correctness (`counters.rs:79-121`)**:
Partitioning filtered `CounterTerm`s into positive and negative sums and forming
`pos - neg` preserves exact integer evaluation. -/
theorem transcribeTerms_preserves_int_eval (seen : Nat → Bool) (terms : List CounterTerm)
    (cnts : Nat → Int) :
    evalCovTerm cnts (transcribeTerms seen terms) =
      evalCounterTerms (terms.filter (fun t => seen t.node)) cnts := by
  unfold transcribeTerms
  rw [eval_makeSubtractedSumTerm, eval_makeSumTerm_opt]
  exact eval_pos_minus_neg_eq_evalCounterTerms (terms.filter (fun t => seen t.node)) cnts

/-- **Dead-BCB Pruning Soundness (`query.rs:140-143`)**:
If every omitted node (`!seen node`) genuinely has zero execution count (`cnts node = 0`),
filtering by `seen` preserves `evalCounterTerms` identically. -/
theorem dead_bcb_filtering_sound (seen : Nat → Bool) (terms : List CounterTerm)
    (cnts : Nat → Int) (hzero : ∀ id, seen id = false → cnts id = 0) :
    evalCounterTerms (terms.filter (fun t => seen t.node)) cnts =
      evalCounterTerms terms cnts := by
  induction terms with
  | nil => rfl
  | cons t rest ih =>
    have hcat : t :: rest = [t] ++ rest := rfl
    by_cases hs : seen t.node = true
    · simp only [List.filter_cons, hs, ↓reduceIte]
      have hcatF : t :: rest.filter (fun x => seen x.node) =
          [t] ++ rest.filter (fun x => seen x.node) := rfl
      rw [hcatF, evalCounterTerms_append, ih, hcat, evalCounterTerms_append]
    · have hsf : seen t.node = false := Bool.eq_false_iff.mpr hs
      simp only [List.filter_cons, hsf, Bool.false_eq_true, ↓reduceIte]
      rw [ih, hcat, evalCounterTerms_append, evalCounterTerms_single]
      have htz : cnts t.node = 0 := hzero t.node hsf
      cases t.op <;> simp only [htz, Int.neg_zero, Int.zero_add]

theorem dead_bcb_wrong_omission_counterexample :
    ∃ (seen : Nat → Bool) (terms : List CounterTerm) (cnts : Nat → Int),
      evalCovTerm cnts (transcribeTerms seen terms) ≠ evalCounterTerms terms cnts := by
  refine ⟨fun id => id == 0,
    [{ op := .add, node := 0 }, { op := .add, node := 1 }],
    fun id => if id == 0 then 1 else 5, ?_⟩
  decide

/-- LLVM `CounterMappingContext::evaluate` (`CoverageMapping.cpp:194-248`) followed by
`CountedRegionEmitter` (`uint64_t` cast at `CoverageMapping.cpp:788`) and
`CoverageExporterJson::clamp_uint64_to_int64` (`CoverageExporterJson.cpp:80-86`). -/
def twoPow63 : Int := 9223372036854775808
def twoPow64 : Int := 18446744073709551616
def int64Max : Int := 9223372036854775807

def int64ToUint64 (x : Int) : Int :=
  x % twoPow64

def clampUint64ToInt64 (u : Int) : Int :=
  if u ≤ int64Max then u else int64Max

theorem llvm_eval_nonneg_exact (x : Int) (h0 : 0 ≤ x) (hlt : x < twoPow63) :
    int64ToUint64 x = x ∧ clampUint64ToInt64 (int64ToUint64 x) = x := by
  have hlt64 : x < twoPow64 := Int.lt_trans hlt (by decide)
  have hmod : x % twoPow64 = x := Int.emod_eq_of_lt h0 hlt64
  have hle : x ≤ int64Max := by
    have hstep : twoPow63 - 1 = int64Max := rfl
    rw [← hstep]
    exact Int.le_sub_one_of_lt hlt
  unfold int64ToUint64 clampUint64ToInt64
  simp only [hmod, hle, ↓reduceIte, and_self]

/-- **Signed-to-Unsigned Underflow Wraparound (`CoverageMapping.cpp:788` & `CoverageExporterJson.cpp:84`)**:
When an unwind conservation deficit causes `evalCovTerm` to evaluate to `-1` (as in `0 - 1`),
LLVM `CounterValues` stores `2^64 - 1 = 18446744073709551615` (`18.4E` in `llvm-cov show`),
while `llvm-cov export` clamps to `2^63 - 1 = 9223372036854775807`. -/
theorem llvm_eval_minus_one_wraparound :
    int64ToUint64 (-1) = 18446744073709551615 ∧
      clampUint64ToInt64 (int64ToUint64 (-1)) = 9223372036854775807 := by
  decide

/-! ## Section 5: Span Refinement & Disjoint Partition Invariants (`spans.rs`) -/

structure SourceSpan where
  lo : Nat
  hi : Nat

def SourceSpan.overlaps (a b : SourceSpan) : Bool :=
  (a.lo < b.hi) && (b.lo < a.hi)

def SourceSpan.overlapsOrAdjacent (a b : SourceSpan) : Bool :=
  (a.lo ≤ b.hi) && (b.lo ≤ a.hi)

def SourceSpan.to (a b : SourceSpan) : SourceSpan :=
  { lo := Nat.min a.lo b.lo, hi := Nat.max a.hi b.hi }

structure Covspan where
  span : SourceSpan
  bcb : Nat

/-- Models `compare_spans` (`spans.rs:245-254`): `lo` ascending, then `hi` descending. -/
def spanCmp (a b : SourceSpan) : Bool :=
  if a.lo < b.lo then true
  else if b.lo < a.lo then false
  else b.hi ≤ a.hi

/-- Models `remove_unwanted_overlapping_spans` (`spans.rs:189-217`). -/
def removeUnwantedOverlappingAux (pending refined rem : List Covspan) : List Covspan :=
  rem.foldr
    (fun curr ih p r =>
      let finished := p.filter (fun prev => prev.span.hi ≤ curr.span.lo)
      let stillPending := p.filter (fun prev =>
        !(prev.span.hi ≤ curr.span.lo) && (prev.bcb == curr.bcb))
      ih (stillPending ++ [curr]) (r ++ finished))
    (fun p r => r ++ p) pending refined

theorem removeUnwantedAux_nil (p r : List Covspan) :
    removeUnwantedOverlappingAux p r [] = r ++ p := rfl

theorem removeUnwantedAux_cons (p r : List Covspan) (curr : Covspan) (rest : List Covspan) :
    removeUnwantedOverlappingAux p r (curr :: rest) =
      let finished := p.filter (fun prev => prev.span.hi ≤ curr.span.lo)
      let stillPending := p.filter (fun prev =>
        !(prev.span.hi ≤ curr.span.lo) && (prev.bcb == curr.bcb))
      removeUnwantedOverlappingAux (stillPending ++ [curr]) (r ++ finished) rest := rfl

def removeUnwantedOverlappingSpans (sortedSpans : List Covspan) : List Covspan :=
  removeUnwantedOverlappingAux [] [] sortedSpans

def pairwiseCrossBcbDisjoint (xs : List Covspan) : Prop :=
  ∀ a b, a ∈ xs → b ∈ xs → a.bcb ≠ b.bcb →
    a.span.hi ≤ b.span.lo ∨ b.span.hi ≤ a.span.lo

def invOrdered (pending refined rem : List Covspan) : Prop :=
  (∀ x, x ∈ refined → ∀ y, y ∈ pending → x.bcb ≠ y.bcb → x.span.hi ≤ y.span.lo) ∧
  (∀ x, x ∈ refined → ∀ y, y ∈ rem → x.span.hi ≤ y.span.lo) ∧
  pairwiseCrossBcbDisjoint refined ∧
  (∀ a b, a ∈ pending → b ∈ pending → a.bcb = b.bcb) ∧
  (∀ p, p ∈ pending → ∀ r, r ∈ rem → p.span.lo ≤ r.span.lo) ∧
  List.Pairwise (fun a b => a.span.lo ≤ b.span.lo) rem

theorem pairwiseCrossBcbDisjoint_append {xs ys : List Covspan}
    (hxs : pairwiseCrossBcbDisjoint xs)
    (hys : pairwiseCrossBcbDisjoint ys)
    (hcross : ∀ x, x ∈ xs → ∀ y, y ∈ ys → x.bcb ≠ y.bcb →
      x.span.hi ≤ y.span.lo ∨ y.span.hi ≤ x.span.lo) :
    pairwiseCrossBcbDisjoint (xs ++ ys) := by
  intro a b ha hb hne
  rw [List.mem_append] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hxs a b ha hb hne
  · exact hcross a ha b hb hne
  · exact Or.symm (hcross b hb a ha (Ne.symm hne))
  · exact hys a b ha hb hne

theorem pairwiseCrossBcbDisjoint_same_bcb (xs : List Covspan)
    (hsame : ∀ a b, a ∈ xs → b ∈ xs → a.bcb = b.bcb) :
    pairwiseCrossBcbDisjoint xs := by
  intro a b ha hb hne
  exact absurd (hsame a b ha hb) hne

/-- Provenance preservation for `remove_unwanted_overlapping_spans`: every output span
comes directly from the input list (no spans are synthesized or altered). -/
theorem removeUnwanted_subset_aux (pending refined rem : List Covspan)
    (x : Covspan) (hx : x ∈ removeUnwantedOverlappingAux pending refined rem) :
    x ∈ pending ∨ x ∈ refined ∨ x ∈ rem := by
  induction rem generalizing pending refined with
  | nil =>
    rw [removeUnwantedAux_nil, List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  | cons curr rest ih =>
    rw [removeUnwantedAux_cons] at hx
    have hrec := ih _ _ hx
    rcases hrec with h1 | h2 | h3
    · rw [List.mem_append, List.mem_filter, List.mem_singleton] at h1
      rcases h1 with ⟨hp, _⟩ | hc
      · exact Or.inl hp
      · subst hc; exact Or.inr (Or.inr List.mem_cons_self)
    · rw [List.mem_append, List.mem_filter] at h2
      rcases h2 with hr | ⟨hp, _⟩
      · exact Or.inr (Or.inl hr)
      · exact Or.inl hp
    · exact Or.inr (Or.inr (List.mem_cons_of_mem curr h3))

theorem removeUnwanted_subset (sortedSpans : List Covspan) (x : Covspan)
    (hx : x ∈ removeUnwantedOverlappingSpans sortedSpans) :
    x ∈ sortedSpans := by
  have h := removeUnwanted_subset_aux [] [] sortedSpans x hx
  rcases h with h | h | h
  · exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil
  · exact h

theorem removeUnwanted_aux_disjoint (pending refined rem : List Covspan)
    (hinv : invOrdered pending refined rem) :
    pairwiseCrossBcbDisjoint (removeUnwantedOverlappingAux pending refined rem) := by
  induction rem generalizing pending refined with
  | nil =>
    rw [removeUnwantedAux_nil]
    rcases hinv with ⟨hRP, _, hDisjR, hSameP, _, _⟩
    apply pairwiseCrossBcbDisjoint_append hDisjR (pairwiseCrossBcbDisjoint_same_bcb pending hSameP)
    intro x hx y hy hne
    exact Or.inl (hRP x hx y hy hne)
  | cons curr rest ih =>
    rw [removeUnwantedAux_cons]
    rcases hinv with ⟨hRP, hRR, hDisjR, hSameP, hPR, hPW⟩
    rw [List.pairwise_cons] at hPW
    rcases hPW with ⟨hCurrRest, hPWRest⟩
    let finished := pending.filter (fun prev => prev.span.hi ≤ curr.span.lo)
    let stillPending := pending.filter (fun prev =>
      !(prev.span.hi ≤ curr.span.lo) && (prev.bcb == curr.bcb))
    apply ih (stillPending ++ [curr]) (refined ++ finished)
    refine ⟨?_, ?_, ?_, ?_, ?_, hPWRest⟩
    · intro x hx y hy hxy
      rw [List.mem_append] at hx hy
      rcases hx with hxR | hxF
      · rcases hy with hySP | hyC
        · rw [List.mem_filter] at hySP
          exact hRP x hxR y hySP.1 hxy
        · rcases List.mem_singleton.mp hyC with rfl
          exact hRR x hxR y List.mem_cons_self
      · rw [List.mem_filter] at hxF
        have hxHi : x.span.hi ≤ curr.span.lo := decide_eq_true_eq.mp hxF.2
        rcases hy with hySP | hyC
        · rw [List.mem_filter] at hySP
          exact absurd (hSameP x y hxF.1 hySP.1) hxy
        · rcases List.mem_singleton.mp hyC with rfl
          exact hxHi
    · intro x hx y hy
      rw [List.mem_append] at hx
      rcases hx with hxR | hxF
      · exact hRR x hxR y (List.mem_cons_of_mem curr hy)
      · rw [List.mem_filter] at hxF
        have hxHi : x.span.hi ≤ curr.span.lo := decide_eq_true_eq.mp hxF.2
        exact Nat.le_trans hxHi (hCurrRest y hy)
    · apply pairwiseCrossBcbDisjoint_append hDisjR
      · apply pairwiseCrossBcbDisjoint_same_bcb finished
        intro a b ha hb
        rw [List.mem_filter] at ha hb
        exact hSameP a b ha.1 hb.1
      · intro x hx y hy hxy
        rw [List.mem_filter] at hy
        exact Or.inl (hRP x hx y hy.1 hxy)
    · intro a b ha hb
      rw [List.mem_append] at ha hb
      rcases ha with haSP | haC <;> rcases hb with hbSP | hbC
      · rw [List.mem_filter] at haSP hbSP
        have haEq : a.bcb = curr.bcb := by
          have hb1 := (Bool.and_eq_true _ _).mp haSP.2
          exact beq_iff_eq.mp hb1.2
        have hbEq : b.bcb = curr.bcb := by
          have hb2 := (Bool.and_eq_true _ _).mp hbSP.2
          exact beq_iff_eq.mp hb2.2
        rw [haEq, hbEq]
      · rw [List.mem_filter] at haSP
        rcases List.mem_singleton.mp hbC with rfl
        exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp haSP.2).2
      · rcases List.mem_singleton.mp haC with rfl
        rw [List.mem_filter] at hbSP
        exact Eq.symm (beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hbSP.2).2)
      · rcases List.mem_singleton.mp haC with rfl
        rcases List.mem_singleton.mp hbC with rfl
        rfl
    · intro p hp r hr
      rw [List.mem_append] at hp
      rcases hp with hpSP | hpC
      · rw [List.mem_filter] at hpSP
        exact hPR p hpSP.1 r (List.mem_cons_of_mem curr hr)
      · rcases List.mem_singleton.mp hpC with rfl
        exact hCurrRest r hr

/-- **Disjoint Cross-BCB Partition Theorem (`spans.rs:189-217`)**:
For any `Covspan` list sorted by `lo` ascending, `removeUnwantedOverlappingSpans`
produces a subset of the input that is strictly disjoint across distinct BCBs. -/
theorem removeUnwanted_disjoint (sortedSpans : List Covspan)
    (hsorted : List.Pairwise (fun a b => a.span.lo ≤ b.span.lo) sortedSpans) :
    pairwiseCrossBcbDisjoint (removeUnwantedOverlappingSpans sortedSpans) := by
  apply removeUnwanted_aux_disjoint [] [] sortedSpans
  refine ⟨?_, ?_, ?_, ?_, ?_, hsorted⟩
  · intro x hx; exact absurd hx List.not_mem_nil
  · intro x hx; exact absurd hx List.not_mem_nil
  · intro a _ ha; exact absurd ha List.not_mem_nil
  · intro a _ ha; exact absurd ha List.not_mem_nil
  · intro p hp; exact absurd hp List.not_mem_nil

/-- Models `discard_spans_overlapping_holes` (`spans.rs:161-184`): any retained span
has zero overlap with every hole span. -/
def discardSpansOverlappingHoles (covspans : List Covspan) (holes : List SourceSpan) :
    List Covspan :=
  covspans.filter (fun cs => !(holes.any (fun h => h.overlaps cs.span)))

theorem discardSpansOverlappingHoles_sound (covspans : List Covspan) (holes : List SourceSpan) :
    ∀ cs, cs ∈ discardSpansOverlappingHoles covspans holes →
      cs ∈ covspans ∧ ∀ h, h ∈ holes → h.overlaps cs.span = false := by
  intro cs hmem
  unfold discardSpansOverlappingHoles at hmem
  rw [List.mem_filter] at hmem
  refine ⟨hmem.1, ?_⟩
  intro h hh
  have hany : holes.any (fun x => x.overlaps cs.span) = false := by
    cases hb : holes.any (fun x => x.overlaps cs.span)
    · rfl
    · rw [hb] at hmem
      exact absurd hmem.2 Bool.false_ne_true
  by_cases hov : h.overlaps cs.span = true
  · have htrue : holes.any (fun x => x.overlaps cs.span) = true :=
      List.any_eq_true.mpr ⟨h, hh, hov⟩
    rw [htrue] at hany
    exact Bool.noConfusion hany
  · exact Bool.eq_false_iff.mpr hov

/-- Models `Covspan::merge_if_eligible` (`spans.rs:231-241`). -/
def mergeStep (st : Option Covspan × List Covspan) (curr : Covspan) :
    Option Covspan × List Covspan :=
  match st.1 with
  | none => (some curr, st.2)
  | some prev =>
    if prev.bcb == curr.bcb && prev.span.overlapsOrAdjacent curr.span then
      (some { span := prev.span.to curr.span, bcb := prev.bcb }, st.2)
    else
      (some curr, st.2 ++ [prev])

def mergeAdjacentSameBcb (xs : List Covspan) : List Covspan :=
  let res := xs.foldl mergeStep (none, [])
  match res.1 with
  | none => res.2
  | some last => res.2 ++ [last]

def allValidSpan (xs : List Covspan) : Prop :=
  ∀ c, c ∈ xs → c.span.lo ≤ c.span.hi

theorem mergeAdjacentSameBcb_preserves_cross_bcb_disjoint_aux (a b : Covspan)
    (c : Covspan) (hdisjA : a.span.hi ≤ c.span.lo ∨ c.span.hi ≤ a.span.lo)
    (hdisjB : b.span.hi ≤ c.span.lo ∨ c.span.hi ≤ b.span.lo)
    (hadj : a.span.overlapsOrAdjacent b.span = true)
    (hcNonEmpty : c.span.lo < c.span.hi) :
    (a.span.to b.span).hi ≤ c.span.lo ∨ c.span.hi ≤ (a.span.to b.span).lo := by
  have hadj1 : a.span.lo ≤ b.span.hi ∧ b.span.lo ≤ a.span.hi := by
    unfold SourceSpan.overlapsOrAdjacent at hadj
    exact ⟨decide_eq_true_eq.mp (Bool.and_eq_true _ _ |>.mp hadj).1,
           decide_eq_true_eq.mp (Bool.and_eq_true _ _ |>.mp hadj).2⟩
  rcases hdisjA with hac | hca <;> rcases hdisjB with hbc | hcb
  · left
    unfold SourceSpan.to
    exact Nat.max_le.mpr ⟨hac, hbc⟩
  · -- `a.hi ≤ c.lo` and `c.hi ≤ b.lo`, contradicting `b.lo ≤ a.hi` and `c.lo < c.hi`!
    have hcontr : c.span.hi ≤ c.span.lo :=
      Nat.le_trans hcb (Nat.le_trans hadj1.2 hac)
    exact absurd hcNonEmpty (Nat.not_lt_of_le hcontr)
  · -- `c.hi ≤ a.lo` and `b.hi ≤ c.lo`, contradicting `a.lo ≤ b.hi` and `c.lo < c.hi`!
    have hcontr : c.span.hi ≤ c.span.lo :=
      Nat.le_trans hca (Nat.le_trans hadj1.1 hbc)
    exact absurd hcNonEmpty (Nat.not_lt_of_le hcontr)
  · right
    unfold SourceSpan.to
    exact Nat.le_min.mpr ⟨hca, hcb⟩

/-- Models `ensure_non_empty_span` (`spans.rs:256-277`) for adjacent `{` or `}`. -/
def expandEmptyBraceSpan (lo hi : Nat) (nextIsLBrace prevIsRBrace : Bool) : Option SourceSpan :=
  if lo < hi then some { lo := lo, hi := hi }
  else if nextIsLBrace then some { lo := lo, hi := hi + 1 }
  else if prevIsRBrace && (0 < lo) then some { lo := lo - 1, hi := hi }
  else none

theorem expandEmptyBraceSpan_nonempty (lo hi : Nat) (nextL prevR : Bool) (sp : SourceSpan)
    (hle : lo ≤ hi) (hres : expandEmptyBraceSpan lo hi nextL prevR = some sp) :
    sp.lo < sp.hi := by
  unfold expandEmptyBraceSpan at hres
  by_cases hlt : lo < hi
  · simp only [hlt, ↓reduceIte] at hres
    injection hres with hsp
    rw [← hsp]; exact hlt
  · simp only [hlt, ↓reduceIte] at hres
    have heq : lo = hi := Nat.le_antisymm hle (Nat.not_lt.mp hlt)
    subst heq
    by_cases hnl : nextL = true
    · simp only [hnl, ↓reduceIte] at hres
      injection hres with hsp
      rw [← hsp]
      exact Nat.lt_succ_self lo
    · have hnlf : nextL = false := Bool.eq_false_iff.mpr hnl
      simp only [hnlf, Bool.false_eq_true, ↓reduceIte] at hres
      by_cases hpr : (prevR && decide (0 < lo)) = true
      · simp only [hpr, ↓reduceIte] at hres
        injection hres with hsp
        rw [← hsp]
        have hpos : 0 < lo := decide_eq_true_eq.mp (Bool.and_eq_true _ _ |>.mp hpr).2
        exact Nat.sub_lt hpos Nat.zero_lt_one
      · have hprf : (prevR && decide (0 < lo)) = false := Bool.eq_false_iff.mpr hpr
        simp only [hprf, Bool.false_eq_true, ↓reduceIte] at hres
        contradiction

/-- Models bang-macro distillation (`spans.rs:128-155`): selects `minmax_bcbs.min`
(entry/dominating BCB) and truncates `call_site` through `!`. -/
inductive ExpnKindModel where
  | bangMacro
  | awaitDesugar
  | other

def distillChildExpansionBcb (kind : ExpnKindModel) (minBcb maxBcb : Nat) : Nat :=
  match kind with
  | .bangMacro | .awaitDesugar => minBcb
  | .other => maxBcb

theorem bang_macro_uses_min_dominator_bcb (minBcb maxBcb : Nat) :
    distillChildExpansionBcb .bangMacro minBcb maxBcb = minBcb ∧
      distillChildExpansionBcb .awaitDesugar minBcb maxBcb = minBcb := ⟨rfl, rfl⟩

/-! ## Section 6: Concrete Verified Witnesses Matching Live `rustc` & `node_flow/tests.rs` -/

/-- Exact 5-node example from Knuth & Stevenson (1973) and
`compiler/rustc_mir_transform/src/coverage/counters/node_flow/tests.rs::example_driver`:
edges `[(0,1),(0,3),(1,0),(1,2),(2,1),(2,4),(3,3),(3,4),(4,0)]`, yielding
supernode equivalence classes `{0, 2}` (representative `0`) and `{1, 3, 4}` (representative `1`). -/
def ksExampleSupernodes : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | x => x

def ksExampleSuccSupernodes : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | x => x

def ksExamplePriority : List Nat := [3, 1, 2, 0, 4]

def ksFlow : Nat → Int
  | 0 => 7
  | 1 => 5
  | 2 => 4
  | 3 => 12
  | 4 => 6
  | _ => 0

def ksState : SpantreeState :=
  spantreeRunPriorityList 5 ksExampleSupernodes ksExampleSuccSupernodes ksExamplePriority

/-- Verify executable `spantreeRunPriorityList` on Knuth–Stevenson (1973) reconstructs
ALL 5 node frequencies (`[7, 5, 4, 12, 6]`) with zero error, matching `node_flow/tests.rs`! -/
theorem knuth_stevenson_1973_exact :
    evalCounterTerms (ksState.terms 0) ksFlow = 7 ∧
      evalCounterTerms (ksState.terms 1) ksFlow = 5 ∧
      evalCounterTerms (ksState.terms 2) ksFlow = 4 ∧
      evalCounterTerms (ksState.terms 3) ksFlow = 12 ∧
      evalCounterTerms (ksState.terms 4) ksFlow = 6 := by
  decide

/-- Verify `transcribeTerms` on `ksState.terms 1` (`+c0 +c2 -c4`) evaluates identically to `5`. -/
theorem knuth_stevenson_node1_transcribed_exact :
    evalCovTerm ksFlow (transcribeTerms (fun _ => true) (ksState.terms 1)) = 5 := by
  decide

/-- Concrete live-probe witness for `unwind_underflow_loop(3, true, true)` from
`rustc 1.98.0-nightly`: `c0 = 1` (entry), `c1 = 1` (`if flag`), `c2 = 0` (`while` header never reached),
yielding `c2 - c0 = -1` -> `18446744073709551615` (`18.4E` in `llvm-cov show`) ->
`9223372036854775807` (`INT64_MAX` in `llvm-cov export`). -/
def unwindUnderflowExpr : CovTerm :=
  CovTerm.exprSub (CovTerm.physCounter 2) (CovTerm.physCounter 0)

def unwindUnderflowRawCounts : Nat → Int
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | _ => 0

theorem unwind_underflow_loop_live_witness :
    evalCovTerm unwindUnderflowRawCounts unwindUnderflowExpr = -1 ∧
      int64ToUint64 (evalCovTerm unwindUnderflowRawCounts unwindUnderflowExpr) =
        18446744073709551615 ∧
      clampUint64ToInt64 (int64ToUint64 (evalCovTerm unwindUnderflowRawCounts unwindUnderflowExpr)) =
        9223372036854775807 := by
  decide

end MirCoverageSoundness

#print axioms MirCoverageSoundness.bcb_strips_assert_unwind
#print axioms MirCoverageSoundness.kirchhoff_conservation_on_normal_trace
#print axioms MirCoverageSoundness.kirchhoff_conservation_aggregate
#print axioms MirCoverageSoundness.unwind_trace_deficit_exact
#print axioms MirCoverageSoundness.intra_bcb_post_call_phantom_count
#print axioms MirCoverageSoundness.supernode_in_out_balanced
#print axioms MirCoverageSoundness.supernode_cut_conservation
#print axioms MirCoverageSoundness.spantree_cut_reconstruction_exact
#print axioms MirCoverageSoundness.transcribeTerms_preserves_int_eval
#print axioms MirCoverageSoundness.dead_bcb_filtering_sound
#print axioms MirCoverageSoundness.dead_bcb_wrong_omission_counterexample
#print axioms MirCoverageSoundness.llvm_eval_nonneg_exact
#print axioms MirCoverageSoundness.llvm_eval_minus_one_wraparound
#print axioms MirCoverageSoundness.removeUnwanted_subset
#print axioms MirCoverageSoundness.removeUnwanted_disjoint
#print axioms MirCoverageSoundness.discardSpansOverlappingHoles_sound
#print axioms MirCoverageSoundness.mergeAdjacentSameBcb_preserves_cross_bcb_disjoint_aux
#print axioms MirCoverageSoundness.expandEmptyBraceSpan_nonempty
#print axioms MirCoverageSoundness.bang_macro_uses_min_dominator_bcb
#print axioms MirCoverageSoundness.knuth_stevenson_1973_exact
#print axioms MirCoverageSoundness.knuth_stevenson_node1_transcribed_exact
#print axioms MirCoverageSoundness.unwind_underflow_loop_live_witness
