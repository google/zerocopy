/-
Control-flow graphs, walks, dominance, dominance frontiers, iterated dominance frontiers,
join sets, and reaching definitions (toy model).
-/
namespace Toy.Ssa

/-- A finite control-flow graph: nodes are `Fin n` (basic blocks), `edge a b = true` means
control may pass from the end of block `a` to the start of block `b`, and `entry` is the
designated start block. Captures the CFG of a single procedure as a simple directed graph
(parallel edges between the same two blocks are collapsed). There is no built-in exit: a
procedure return, halt, or exceptional exit out of block `p` is represented only if it is
modeled as an edge from `p` to an explicit exit block. -/
structure Cfg (n : Nat) where
  edge : Fin n → Fin n → Bool
  entry : Fin n

/-- A concrete CFG from a list of edges `(a, b)` given by node numbers. -/
def Cfg.ofEdges (n : Nat) (es : List (Nat × Nat)) (entry : Fin n) : Cfg n where
  edge a b := es.contains (a.val, b.val)
  entry := entry

variable {n : Nat}

/-- `Walk G a b p`: `p` is the node sequence of a walk from `a` to `b` (both endpoints included;
nodes may repeat). The one-node list `[a]` is the null walk from `a` to `a`. -/
inductive Walk (G : Cfg n) : Fin n → Fin n → List (Fin n) → Prop
  | single (a : Fin n) : Walk G a a [a]
  | cons {a b c : Fin n} {p : List (Fin n)} :
      G.edge a b = true → Walk G b c p → Walk G a c (a :: p)

/-- `b` is reachable from the entry. -/
def Reachable (G : Cfg n) (b : Fin n) : Prop := ∃ p, Walk G G.entry b p

/-- Every block is reachable from the entry. -/
def AllReachable (G : Cfg n) : Prop := ∀ b, Reachable G b

/-- The entry block has no predecessors (no edge enters it). -/
def EntryNoPreds (G : Cfg n) : Prop := ∀ a, G.edge a G.entry = false

/-- No block reachable from the entry has an edge into the entry (edges into the entry from
unreachable blocks are allowed). Implied by `EntryNoPreds` and by acyclicity. -/
def EntryNoReachablePreds (G : Cfg n) : Prop := ∀ a, Reachable G a → G.edge a G.entry = false

theorem entryNoReachablePreds_of_entryNoPreds {G : Cfg n} (h : EntryNoPreds G) :
    EntryNoReachablePreds G := fun a _ => h a

/-- Semantic dominance: `a` dominates `b` iff every walk from the entry to `b` passes through `a`.
(For a block unreachable from the entry this holds vacuously for every `a`.) -/
def Dom (G : Cfg n) (a b : Fin n) : Prop := ∀ p, Walk G G.entry b p → a ∈ p

/-- Strict dominance: `a` dominates `b` and `a ≠ b`. -/
def SDom (G : Cfg n) (a b : Fin n) : Prop := Dom G a b ∧ a ≠ b

/-- Dominance frontier (Cytron et al.): `y ∈ DF(a)` iff `a` dominates some predecessor of `y`
but does not strictly dominate `y`. -/
def DF (G : Cfg n) (a y : Fin n) : Prop :=
  (∃ p, G.edge p y = true ∧ Dom G a p) ∧ ¬ SDom G a y

/-- Iterated dominance frontier `DF⁺(S)`: the least set `T` with `DF(S ∪ T) ⊆ T`
(the limit of `DF₁ = DF(S)`, `DFᵢ₊₁ = DF(S ∪ DFᵢ)`). -/
inductive IDF (G : Cfg n) (S : Fin n → Prop) : Fin n → Prop
  | base {x y : Fin n} : S x → DF G x y → IDF G S y
  | step {x y : Fin n} : IDF G S x → DF G x y → IDF G S y

/-- Convergence (Cytron et al., conditions (1)–(3)): `p` is a nonnull walk from `x` to `z`, `q` a
nonnull walk from `y` to `z`, `x ≠ y`, and any node occurring in both walks occurs at the end of
at least one of them. (One walk may be a cycle through `z`.) -/
def Converge (G : Cfg n) (x y z : Fin n) (p q : List (Fin n)) : Prop :=
  x ≠ y ∧ Walk G x z p ∧ Walk G y z q ∧ 2 ≤ p.length ∧ 2 ≤ q.length ∧
    ∀ (i : Fin p.length) (j : Fin q.length), p[i] = q[j] →
      i.val + 1 = p.length ∨ j.val + 1 = q.length

/-- Join set `J(S)`: the nodes at which two nonnull walks starting at two distinct nodes of `S`
converge. -/
def InJoin (G : Cfg n) (S : Fin n → Prop) (z : Fin n) : Prop :=
  ∃ x y p q, S x ∧ S y ∧ Converge G x y z p q

/-- `Clear G Defs v b`: there is a walk from `v` to `b` (possibly null) all of whose nodes before
its final node `b` lie outside `Defs`. -/
inductive Clear (G : Cfg n) (Defs : Fin n → Prop) : Fin n → Fin n → Prop
  | here (b : Fin n) : Clear G Defs b b
  | step {v w b : Fin n} : ¬ Defs v → G.edge v w = true → Clear G Defs w b → Clear G Defs v b

/-- Reaching definition at a block top: the definition point `u ∈ Defs` (the value of the variable
on exit from block `u`) reaches the top of block `b`: some nonnull walk from `u` to `b` has no
interior node in `Defs`. -/
def ReachesTop (G : Cfg n) (Defs : Fin n → Prop) (u b : Fin n) : Prop :=
  Defs u ∧ ∃ v, G.edge u v = true ∧ Clear G Defs v b

/-- Single reaching definitions for one variable defined in blocks `D` with φ-functions placed at
blocks `P`: at the top of every non-entry block that carries no φ, at most one definition point of
`D ∪ P` reaches. (A φ at `b` is itself the unique definition reaching the top of `b`; a use at the
top of the entry block reads the initial value.) -/
def SingleReachingDef (G : Cfg n) (D P : Fin n → Prop) : Prop :=
  ∀ b, ¬ P b → b ≠ G.entry → ∀ u v,
    ReachesTop G (fun w => D w ∨ P w) u b → ReachesTop G (fun w => D w ∨ P w) v b → u = v

/-- `d` is the nearest strict dominator of `b` among the definition points `Defs`: `d ∈ Defs`,
`d` strictly dominates `b`, and every definition point strictly dominating `b` dominates `d`.
This is the definition that a dominator-tree renaming walk assigns to an upward-exposed use at
the top of `b`. -/
def NearestSDomDef (G : Cfg n) (Defs : Fin n → Prop) (b d : Fin n) : Prop :=
  Defs d ∧ SDom G d b ∧ ∀ d', Defs d' → SDom G d' b → Dom G d' d

/-! ### Basic walk lemmas -/

theorem Walk.head_mem {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p) : a ∈ p := by
  cases h <;> simp

theorem Walk.last_mem {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p) : b ∈ p := by
  induction h with
  | single a => simp
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

theorem Walk.length_pos {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p) :
    0 < p.length := by
  cases h <;> simp

theorem Walk.getElem_zero {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p)
    (hp : 0 < p.length) : p[0] = a := by
  cases h <;> simp

theorem Walk.getElem_last {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p)
    (hp : p.length - 1 < p.length) : p[p.length - 1] = b := by
  induction h with
  | single a => simp
  | @cons a' b' c' p' _ hw ih =>
    have hl := hw.length_pos
    have : (a' :: p').length - 1 = (p'.length - 1) + 1 := by simp; omega
    simp only [this, List.getElem_cons_succ]
    exact ih (by omega)

theorem Walk.edge_getElem {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p) :
    ∀ (i : Nat) (hi : i + 1 < p.length), G.edge (p[i]'(by omega)) p[i + 1] = true := by
  induction h with
  | single a => intro i hi; simp at hi
  | @cons a' b' c' p' he hw ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hw.getElem_zero hw.length_pos]; exact he
    | succ k =>
      simp only [List.getElem_cons_succ]
      exact ih k (by simp at hi; omega)

/-- A nonnull walk ends with an edge from its penultimate node. -/
theorem Walk.edge_penultimate {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p)
    (hp : 2 ≤ p.length) : G.edge (p[p.length - 2]'(by omega)) b = true := by
  have he := h.edge_getElem (p.length - 2) (by omega)
  have : p.length - 2 + 1 = p.length - 1 := by omega
  simp only [this] at he
  rwa [h.getElem_last (by omega)] at he

/-- Every node is dominated by itself. -/
theorem dom_refl (G : Cfg n) (a : Fin n) : Dom G a a := fun _ hw => hw.last_mem

/-- The entry dominates every node. -/
theorem entry_dom (G : Cfg n) (b : Fin n) : Dom G G.entry b := fun _ hw => hw.head_mem

/-- A walk from the entry to `b` avoiding `a` refutes `Dom G a b`. -/
theorem not_dom_of_walk {G : Cfg n} {a b : Fin n} {p : List (Fin n)}
    (hw : Walk G G.entry b p) (ha : a ∉ p) : ¬ Dom G a b := fun h => ha (h p hw)

/-! ### Walks built one edge at a time, prefixes, and the dominance order -/

theorem Walk.append_edge {G : Cfg n} {a b c : Fin n} {p : List (Fin n)} (h : Walk G a b p)
    (he : G.edge b c = true) : Walk G a c (p ++ [c]) := by
  induction h with
  | single a => exact Walk.cons he (Walk.single c)
  | cons hab _ ih => exact Walk.cons hab (ih he)

/-- A walk is its list without the last node, followed by its end node. -/
theorem Walk.eq_dropLast_append {G : Cfg n} {a b : Fin n} {p : List (Fin n)} (h : Walk G a b p) :
    p = p.dropLast ++ [b] := by
  induction h with
  | single a => rfl
  | @cons a' b' c' p' _ hw ih =>
    have hne : p' ≠ [] := by
      intro h; have := hw.length_pos; simp [h] at this
    rw [List.dropLast_cons_of_ne_nil hne, List.cons_append, ← ih]

/-- A walk is either the null walk or a shorter walk followed by one edge. -/
theorem Walk.single_or_snoc {G : Cfg n} {a c : Fin n} {w : List (Fin n)} (h : Walk G a c w) :
    (w = [a] ∧ c = a) ∨ ∃ w' p, w = w' ++ [c] ∧ Walk G a p w' ∧ G.edge p c = true := by
  induction h with
  | single a => exact Or.inl ⟨rfl, rfl⟩
  | @cons a' b' c' p' he hw ih =>
    right
    rcases ih with ⟨rfl, rfl⟩ | ⟨w'', q, rfl, hw'', hq⟩
    · exact ⟨[a'], a', rfl, Walk.single _, he⟩
    · exact ⟨a' :: w'', q, rfl, Walk.cons he hw'', hq⟩

/-- Induction over the walks from `a`, extending a walk by one edge at its end. -/
theorem Walk.snoc_induction {G : Cfg n} {a : Fin n} (Q : Fin n → List (Fin n) → Prop)
    (h0 : Q a [a])
    (hs : ∀ w p c, Walk G a p w → G.edge p c = true → Q p w → Q c (w ++ [c])) :
    ∀ {c : Fin n} {w : List (Fin n)}, Walk G a c w → Q c w := by
  have key : ∀ k, ∀ {c : Fin n} {w : List (Fin n)}, w.length ≤ k + 1 → Walk G a c w → Q c w := by
    intro k
    induction k with
    | zero =>
      intro c w hl hw
      rcases hw.single_or_snoc with ⟨rfl, rfl⟩ | ⟨w', p, rfl, hw', _⟩
      · exact h0
      · have := hw'.length_pos; simp only [List.length_append, List.length_singleton] at hl; omega
    | succ k ih =>
      intro c w hl hw
      rcases hw.single_or_snoc with ⟨rfl, rfl⟩ | ⟨w', p, rfl, hw', hpc⟩
      · exact h0
      · exact hs w' p c hw' hpc
          (ih (by simp only [List.length_append, List.length_singleton] at hl; omega) hw')
  intro c w hw
  exact key w.length (by omega) hw

/-- The prefix of a walk up to the first occurrence of a node `v` on it: a walk to `v` that uses
only nodes of the original walk, is no longer, and is strictly shorter when `v` is not the end
node. -/
theorem Walk.prefix_to {G : Cfg n} {a b v : Fin n} {p : List (Fin n)} (h : Walk G a b p)
    (hv : v ∈ p) :
    ∃ q, Walk G a v q ∧ (∀ u ∈ q, u ∈ p) ∧ q.length ≤ p.length ∧
      (v ≠ b → q.length < p.length) := by
  induction h with
  | single a' =>
    have : v = a' := by simpa using hv
    subst this
    exact ⟨[v], Walk.single _, fun u hu => hu, Nat.le_refl _, fun h => absurd rfl h⟩
  | @cons a' b' c' p' he hw ih =>
    by_cases hva : v = a'
    · subst hva
      refine ⟨[v], Walk.single _, by simp, by simp, fun _ => ?_⟩
      have := hw.length_pos; simp; omega
    · have hv' : v ∈ p' := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h hva
        · exact h
      obtain ⟨q, hq, hsub, hl, hlt⟩ := ih hv'
      refine ⟨a' :: q, Walk.cons he hq, ?_, by simp; omega, fun h => by simp; have := hlt h; omega⟩
      intro u hu
      rcases List.mem_cons.mp hu with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub u h)

/-- A dominator of a reachable block is reachable. -/
theorem Reachable.of_dom {G : Cfg n} {a b : Fin n} (hd : Dom G a b) (hb : Reachable G b) :
    Reachable G a := by
  obtain ⟨p, hp⟩ := hb
  obtain ⟨q, hq, -⟩ := hp.prefix_to (hd p hp)
  exact ⟨q, hq⟩

/-- The end of a walk from a reachable block is reachable. -/
theorem Reachable.of_edge {G : Cfg n} {a b : Fin n} (ha : Reachable G a) (he : G.edge a b = true) :
    Reachable G b := by
  obtain ⟨p, hp⟩ := ha
  exact ⟨_, hp.append_edge he⟩

/-- Dominance is antisymmetric on reachable blocks. -/
theorem dom_antisymm {G : Cfg n} {a b : Fin n} (hab : Dom G a b) (hba : Dom G b a)
    (ha : Reachable G a) : a = b := by
  apply Classical.byContradiction
  intro hne
  have key : ∀ k, ∀ p, p.length ≤ k → Walk G G.entry a p → False := by
    intro k
    induction k with
    | zero => intro p hl hp; have := hp.length_pos; omega
    | succ k ih =>
      intro p hl hp
      obtain ⟨q, hq, _, _, hlt⟩ := hp.prefix_to (hba p hp)
      obtain ⟨r, hr, _, hrl, _⟩ := hq.prefix_to (hab q hq)
      have := hlt (fun h => hne h.symm)
      exact ih r (by omega) hr
  obtain ⟨p, hp⟩ := ha
  exact key p.length p (Nat.le_refl _) hp

/-- A strict dominator of `c` dominates every predecessor of `c`. -/
theorem dom_pred_of_sdom {G : Cfg n} {d c p : Fin n} (hd : SDom G d c) (he : G.edge p c = true) :
    Dom G d p := by
  intro w hw
  have := hd.1 _ (hw.append_edge he)
  rcases List.mem_append.mp this with h | h
  · exact h
  · exact absurd (List.mem_singleton.mp h) hd.2

/-- The dominance frontier of the entry is contained in `{entry}`. -/
theorem df_entry_eq {G : Cfg n} {y : Fin n} (h : DF G G.entry y) : y = G.entry :=
  Classical.byContradiction fun hne => h.2 ⟨entry_dom G y, fun h' => hne h'.symm⟩

/-- `DF⁺({entry}) ⊆ {entry}`. -/
theorem idf_entry_eq {G : Cfg n} {y : Fin n} (h : IDF G (fun x => x = G.entry) y) : y = G.entry := by
  induction h with
  | base hx hdf => subst hx; exact df_entry_eq hdf
  | step _ hdf ih => subst ih; exact df_entry_eq hdf

/-! ### Certificates for concrete graphs -/

/-- Closure certificate: along a walk that starts in `R` and avoids `a`, every node stays in `R`
when `R` is closed under edges except into `a`. -/
theorem mem_of_walk_closed (G : Cfg n) (a : Fin n) (R : Fin n → Bool)
    (hclosed : ∀ u v, R u = true → G.edge u v = true → v = a ∨ R v = true) :
    ∀ {u b : Fin n} {p : List (Fin n)}, Walk G u b p → R u = true → R b = false → a ∈ p := by
  intro u b p hw
  induction hw with
  | single c => intro h1 h2; simp_all
  | @cons a' b' c' p' hab hw ih =>
    intro hu hb
    rcases hclosed _ _ hu hab with h | h
    · subst h; exact List.mem_cons_of_mem _ hw.head_mem
    · exact List.mem_cons_of_mem _ (ih h hb)

/-- Dominance certificate: if `R` contains the entry (unless the entry is `a`), is closed under
edges except into `a`, and excludes `b`, then `a` dominates `b`. -/
theorem dom_of_cert (G : Cfg n) (a b : Fin n) (R : Fin n → Bool)
    (hentry : G.entry = a ∨ R G.entry = true)
    (hclosed : ∀ u v, R u = true → G.edge u v = true → v = a ∨ R v = true)
    (hb : R b = false) : Dom G a b := by
  intro p hw
  rcases hentry with h | h
  · rw [← h]; exact hw.head_mem
  · exact mem_of_walk_closed G a R hclosed hw h hb

/-- No-walk certificate: a set closed under edges that contains `u` but not `b` shows that there
is no walk from `u` to `b`. -/
theorem not_walk_of_closed (G : Cfg n) (R : Fin n → Bool)
    (hclosed : ∀ u v, R u = true → G.edge u v = true → R v = true) :
    ∀ {u b : Fin n} {p : List (Fin n)}, Walk G u b p → R u = true → R b = true := by
  intro u b p hw
  induction hw with
  | single c => exact id
  | cons hab _ ih => exact fun hu => ih (hclosed _ _ hu hab)

/-- Certificate refuting `Clear`: a set closed under edges out of non-definition nodes. -/
theorem clear_closed (G : Cfg n) (Defs : Fin n → Prop) (R : Fin n → Bool)
    (hclosed : ∀ v w, R v = true → ¬ Defs v → G.edge v w = true → R w = true) :
    ∀ {v b : Fin n}, Clear G Defs v b → R v = true → R b = true := by
  intro v b hc
  induction hc with
  | here => exact id
  | step hv he _ ih => exact fun h => ih (hclosed _ _ h hv he)

/-- Certificate refuting `ReachesTop G Defs u b`. -/
theorem not_reachesTop_of_cert (G : Cfg n) (Defs : Fin n → Prop) (u b : Fin n) (R : Fin n → Bool)
    (hstart : ∀ v, G.edge u v = true → R v = true)
    (hclosed : ∀ v w, R v = true → ¬ Defs v → G.edge v w = true → R w = true)
    (hb : R b = false) : ¬ ReachesTop G Defs u b := by
  rintro ⟨_, v, he, hc⟩
  have := clear_closed G Defs R hclosed hc (hstart v he)
  simp_all

/-- The penultimate nodes of two converging walks are two distinct predecessors of the
convergence node. -/
theorem converge_two_preds {G : Cfg n} {x y z : Fin n} {p q : List (Fin n)}
    (h : Converge G x y z p q) :
    ∃ a b, a ≠ b ∧ G.edge a z = true ∧ G.edge b z = true := by
  obtain ⟨_, hp, hq, lp, lq, hdis⟩ := h
  refine ⟨p[p.length - 2]'(by omega), q[q.length - 2]'(by omega), ?_,
    hp.edge_penultimate lp, hq.edge_penultimate lq⟩
  intro heq
  have := hdis ⟨p.length - 2, by omega⟩ ⟨q.length - 2, by omega⟩ heq
  simp at this; omega

/-- A join node has two distinct predecessors. -/
theorem inJoin_two_preds {G : Cfg n} {S : Fin n → Prop} {z : Fin n} (h : InJoin G S z) :
    ∃ a b, a ≠ b ∧ G.edge a z = true ∧ G.edge b z = true := by
  obtain ⟨_, _, _, _, _, _, hc⟩ := h
  exact converge_two_preds hc

/-- With no edge into the entry, the entry has an empty dominance frontier. -/
theorem not_df_entry {G : Cfg n} (h : EntryNoPreds G) (y : Fin n) : ¬ DF G G.entry y := by
  rintro ⟨⟨p, hp, _⟩, hns⟩
  apply hns
  refine ⟨entry_dom G y, ?_⟩
  intro hy; subst hy; simp [h p] at hp

/-- With no edge into the entry, `DF⁺({entry}) = ∅`. -/
theorem not_idf_entry {G : Cfg n} (h : EntryNoPreds G) (y : Fin n) :
    ¬ IDF G (fun x => x = G.entry) y := by
  intro hy
  induction hy with
  | base hx hdf => subst hx; exact not_df_entry h _ hdf
  | step _ _ ih => exact ih

end Toy.Ssa
