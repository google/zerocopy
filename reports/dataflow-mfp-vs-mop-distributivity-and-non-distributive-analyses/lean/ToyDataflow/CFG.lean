import ToyDataflow.Lattice

/-!
# Control-flow graphs, paths, MOP and MFP (specifications)

* A finite CFG has nodes `Fin n`, an edge list, an entry node, an initial
  value at the entry, and one transfer function per node. The transfer function
  of node `u` is applied when leaving `u`, i.e. along each out-edge `u → w`.
* `Walk G v` is a path from the entry to `v` (a sequence of edges; nodes may
  repeat, so there can be unboundedly many). Its value `Walk.val` is the
  composition of the transfer functions of the nodes it leaves, applied to the
  initial value (`Walk.val_eq_foldl`).
* MOP ("join over all paths") at `v` is specified by a universal property:
  `IsMOPAt L G v m` says `m` is a least upper bound of the set of values of all
  paths from the entry to `v`. No bounded-length approximation is used. When no
  path reaches `v`, the set is empty and its least upper bound is `bot`.
* MFP is specified as the least solution of the inequations
  `init ≤ x entry` and `f u (x u) ≤ x w` for every edge `u → w`
  (`IsLeastSolution`), i.e. the least pre-fixpoint. With monotone transfers it
  also satisfies the equations `x w = eqRHS L G x w` with equality
  (`isEquationSolution_of_isLeastSolution_of_monotone` in `MopMfp.lean`); without
  monotonicity it need not. For a forward may-analysis on a join-semilattice this
  is the solution computed by a worklist algorithm (see `Kildall.lean`).

Modeling boundaries of this CFG model:
* `x v` and the MOP value at `v` are facts at the *entry* of `v`, before `f v` is
  applied. `f v` is applied only along out-edges of `v`, so at a node with no
  out-edges (a sink, such as a return block) `f v` occurs in none of `Walk.val`,
  `IsSolution`, `IsMOPAt` or the solver. The fact after a sink's transfer is
  modeled by adding an explicit exit node and edge.
* One transfer function per node is applied along every out-edge of that node.
  Edge-dependent (branch-sensitive) transfers need edge splitting through an
  intermediate node.
* There is a single entry node (so every `CFG n α` has `n ≥ 1`); several entries
  need a synthetic entry node.
* The edge list may contain duplicate edges; they do not change any of the
  specifications.
-/

namespace Toy.Dataflow

variable {n : Nat} {α : Type}

/-- A finite control-flow graph with a node-indexed transfer function. The value
`init` holds at the entry; `f u` is applied along every out-edge of `u`. -/
structure CFG (n : Nat) (α : Type) where
  edges : List (Fin n × Fin n)
  entry : Fin n
  init : α
  f : Fin n → α → α

/-- A path from the entry of `G` to `v`, built by appending edges. -/
inductive Walk (G : CFG n α) : Fin n → Type
  | nil : Walk G G.entry
  | snoc {u w : Fin n} : Walk G u → (u, w) ∈ G.edges → Walk G w

namespace Walk

variable {G : CFG n α}

/-- The value of a path: the transfer functions of the nodes it leaves, composed
in order and applied to `G.init`. -/
def val : {v : Fin n} → Walk G v → α
  | _, .nil => G.init
  | _, @Walk.snoc _ _ _ u _ p _ => G.f u p.val

/-- The nodes a path leaves, in order (all its nodes except the last). -/
def pre : {v : Fin n} → Walk G v → List (Fin n)
  | _, .nil => []
  | _, @Walk.snoc _ _ _ u _ p _ => p.pre ++ [u]

/-- The full node sequence of a path from the entry to `v`. -/
def nodes {v : Fin n} (p : Walk G v) : List (Fin n) := p.pre ++ [v]

/-- Fidelity: a path's value is the composition of the transfer functions of
the nodes it leaves, applied to the initial value. -/
theorem val_eq_foldl {v : Fin n} (p : Walk G v) :
    p.val = p.pre.foldl (fun a u => G.f u a) G.init := by
  induction p with
  | nil => rfl
  | snoc p _ ih => simp [val, pre, List.foldl_append, ih]

end Walk

/-- The set of values of all paths from the entry to `v`. -/
def pathVals (G : CFG n α) (v : Fin n) : α → Prop := fun b => ∃ p : Walk G v, p.val = b

/-- MOP (join over all paths) at `v`: `m` is a least upper bound of the values of
all paths from the entry to `v`. -/
def IsMOPAt (L : Lat α) (G : CFG n α) (v : Fin n) (m : α) : Prop :=
  L.IsLUB (pathVals G v) m

/-- `v` is reachable from the entry. -/
def Reachable (G : CFG n α) (v : Fin n) : Prop := Nonempty (Walk G v)

/-- Every node is reachable from the entry. -/
def AllReachable (G : CFG n α) : Prop := ∀ v, Reachable G v

/-- `x` solves the dataflow inequations: `init ≤ x entry`, and
`f u (x u) ≤ x w` for every edge `u → w`. -/
def IsSolution (L : Lat α) (G : CFG n α) (x : Fin n → α) : Prop :=
  L.le G.init (x G.entry) ∧ ∀ u w, (u, w) ∈ G.edges → L.le (G.f u (x u)) (x w)

/-- MFP: `x` is a solution that is pointwise below every solution. -/
def IsLeastSolution (L : Lat α) (G : CFG n α) (x : Fin n → α) : Prop :=
  IsSolution L G x ∧ ∀ y, IsSolution L G y → ∀ v, L.le (x v) (y v)

/-- Every node that is unreachable from the entry has a strict transfer function
(`f u bot = bot`). Holds vacuously when all nodes are reachable, and holds when
all transfer functions are strict. -/
def UnreachableStrict (L : Lat α) (G : CFG n α) : Prop :=
  ∀ u, ¬ Reachable G u → G.f u L.bot = L.bot

/-- Right-hand side of the dataflow equation at `w`: `init` (if `w` is the entry)
joined with `f u (x u)` for every edge `u → w` (listed with multiplicity). -/
def eqRHS (L : Lat α) (G : CFG n α) (x : Fin n → α) (w : Fin n) : α :=
  L.join (if w = G.entry then G.init else L.bot)
    (L.joinList ((G.edges.filter (fun e => decide (e.2 = w))).map (fun e => G.f e.1 (x e.1))))

/-- `x` satisfies the dataflow equations with equality (a fixed point of `eqRHS`). -/
def IsEquationSolution (L : Lat α) (G : CFG n α) (x : Fin n → α) : Prop :=
  ∀ w, x w = eqRHS L G x w

/-! ## Basic facts (all proved) -/

theorem eqRHS_le_iff {L : Lat α} (hL : L.IsJSL) (G : CFG n α) (x y : Fin n → α) :
    (pwLat n L).le (eqRHS L G x) y ↔
      L.le G.init (y G.entry) ∧ ∀ u w, (u, w) ∈ G.edges → L.le (G.f u (x u)) (y w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := ((hL.join_le_iff _ _ _).1 (h G.entry)).1
      simpa using h0
    · intro u w huw
      have hw := ((hL.join_le_iff _ _ _).1 (h w)).2
      have hw' := (Lat.joinList_le_iff hL _ _).1 hw
      exact hw' (G.f u (x u))
        (List.mem_map.2 ⟨(u, w), List.mem_filter.2 ⟨huw, decide_eq_true rfl⟩, rfl⟩)
  · rintro ⟨hinit, hedge⟩ w
    apply (hL.join_le_iff _ _ _).2
    constructor
    · by_cases hw : w = G.entry
      · subst hw; simpa using hinit
      · simp [hw]; exact hL.bot_le _
    · apply (Lat.joinList_le_iff hL _ _).2
      intro s hs
      rcases List.mem_map.1 hs with ⟨⟨u, w'⟩, hmem, rfl⟩
      rcases List.mem_filter.1 hmem with ⟨huw', hweq⟩
      have heq : w' = w := of_decide_eq_true hweq
      subst heq
      exact hedge u w' huw'

/-- `x` solves the inequations iff `eqRHS L G x ≤ x` pointwise (a pre-fixpoint). -/
theorem isSolution_iff_eqRHS_le {L : Lat α} (hL : L.IsJSL) (G : CFG n α) (x : Fin n → α) :
    IsSolution L G x ↔ (pwLat n L).le (eqRHS L G x) x :=
  (eqRHS_le_iff hL G x x).symm

theorem eqRHS_monotone {L : Lat α} (hL : L.IsJSL) (G : CFG n α)
    (hmono : ∀ u, Monotone L (G.f u)) : Monotone (pwLat n L) (eqRHS L G) := by
  intro x y hxy
  rw [eqRHS_le_iff hL]
  have hrefl := (eqRHS_le_iff hL G y (eqRHS L G y)).1 ((pwLat_isJSL n hL).refl _)
  exact ⟨hrefl.1, fun u w huw => hL.trans _ _ _ (hmono u _ _ (hxy u)) (hrefl.2 u w huw)⟩

theorem pathVals_init (G : CFG n α) : pathVals G G.entry G.init := ⟨.nil, rfl⟩

theorem pathVals_step {G : CFG n α} {u w : Fin n} {a : α} (h : (u, w) ∈ G.edges)
    (ha : pathVals G u a) : pathVals G w (G.f u a) := by
  obtain ⟨p, rfl⟩ := ha
  exact ⟨.snoc p h, rfl⟩

/-- One-step characterization of path values. -/
theorem pathVals_iff (G : CFG n α) (w : Fin n) (b : α) :
    pathVals G w b ↔ (w = G.entry ∧ b = G.init) ∨
      ∃ u a, (u, w) ∈ G.edges ∧ pathVals G u a ∧ b = G.f u a := by
  constructor
  · rintro ⟨p, rfl⟩
    cases p with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | snoc p h => exact Or.inr ⟨_, _, h, ⟨p, rfl⟩, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨u, a, h, ha, rfl⟩)
    · exact pathVals_init G
    · exact pathVals_step h ha

theorem reachable_iff_exists_pathVals (G : CFG n α) (v : Fin n) :
    Reachable G v ↔ ∃ b, pathVals G v b :=
  ⟨fun ⟨p⟩ => ⟨p.val, p, rfl⟩, fun ⟨_, p, _⟩ => ⟨p⟩⟩

/-- At a node with no path from the entry, MOP is `bot`. -/
theorem isMOPAt_bot_of_not_reachable {L : Lat α} (hL : L.IsJSL) {G : CFG n α} {v : Fin n}
    (hv : ¬ Reachable G v) : IsMOPAt L G v L.bot :=
  ⟨fun _ ⟨p, _⟩ => absurd ⟨p⟩ hv, fun u _ => hL.bot_le u⟩

/-- Least solutions are unique (antisymmetry). -/
theorem IsLeastSolution.unique {L : Lat α} (hL : L.IsJSL) {G : CFG n α} {x y : Fin n → α}
    (hx : IsLeastSolution L G x) (hy : IsLeastSolution L G y) : x = y := by
  funext v
  exact hL.antisymm _ _ (hx.2 y hy.1 v) (hy.2 x hx.1 v)

/-- MOP values are unique (antisymmetry). -/
theorem IsMOPAt.unique {L : Lat α} (hL : L.IsJSL) {G : CFG n α} {v : Fin n} {a b : α}
    (ha : IsMOPAt L G v a) (hb : IsMOPAt L G v b) : a = b :=
  Lat.IsLUB.unique hL ha hb

theorem unreachableStrict_of_allReachable (L : Lat α) {G : CFG n α} (h : AllReachable G) :
    UnreachableStrict L G := fun u hu => absurd (h u) hu

theorem unreachableStrict_of_strict (L : Lat α) {G : CFG n α} (h : ∀ u, Strict L (G.f u)) :
    UnreachableStrict L G := fun u _ => h u

end Toy.Dataflow
