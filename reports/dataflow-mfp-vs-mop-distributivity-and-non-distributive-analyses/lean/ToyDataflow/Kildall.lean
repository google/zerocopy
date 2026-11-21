import ToyDataflow.MopMfp

/-!
# A fuel-bounded worklist (Kildall-style) solver

`kildall L G fuel` starts from `x = init` at the entry and `bot` elsewhere, with
every node on the worklist (so transfer functions of unreachable nodes are also
applied, as the equations require). Popping `u` propagates `f u (x u)` into
each successor `w`: if it is not already below `x w`, then `x w := x w ⊔ f u (x u)`
and `w` is pushed. Each pop costs one unit of fuel; running out of fuel returns
`none`.

One unit of fuel pays for one pop, which scans the whole edge list to find the
successors of `u` and performs one order test (and possibly one join) per listed
successor, duplicates included. Fuel bounds therefore count worklist pops, not
edge propagations or lattice operations.

Seeding the worklist with every node makes the result satisfy every inequation,
including those on edges out of unreachable nodes, even without monotonicity
(`kildall_isSolution_of_eq_some`). A solver seeded only with the entry is not
modeled here.
-/

namespace Toy.Dataflow

variable {n : Nat} {α : Type}

/-- Pointwise update. -/
def upd (x : Fin n → α) (w : Fin n) (b : α) : Fin n → α := fun v => if v = w then b else x v

/-- Successors of `u` in the edge list (with multiplicity). -/
def succs (G : CFG n α) (u : Fin n) : List (Fin n) :=
  (G.edges.filter (fun e => decide (e.1 = u))).map Prod.snd

/-- Propagate `out` into each listed successor, pushing every successor whose
value is updated. -/
def propagate (L : Lat α) [DecidableRel L.le] (out : α) :
    List (Fin n) → (Fin n → α) → List (Fin n) → (Fin n → α) × List (Fin n)
  | [], x, wl => (x, wl)
  | w :: ws, x, wl =>
    if L.le out (x w) then propagate L out ws x wl
    else propagate L out ws (upd x w (L.join (x w) out)) (w :: wl)

/-- The worklist loop; one unit of fuel per step (including the final step that
observes an empty worklist). -/
def kildallLoop (L : Lat α) [DecidableRel L.le] (G : CFG n α) :
    Nat → (Fin n → α) → List (Fin n) → Option (Fin n → α)
  | 0, _, _ => none
  | _ + 1, x, [] => some x
  | fuel + 1, x, u :: wl =>
    let r := propagate L (G.f u (x u)) (succs G u) x wl
    kildallLoop L G fuel r.1 r.2

/-- Initial assignment: `init` at the entry, `bot` elsewhere. -/
def kildallInit (L : Lat α) (G : CFG n α) : Fin n → α :=
  fun v => if v = G.entry then G.init else L.bot

/-- The solver: all nodes initially on the worklist. -/
def kildall (L : Lat α) [DecidableRel L.le] (G : CFG n α) (fuel : Nat) : Option (Fin n → α) :=
  kildallLoop L G fuel (kildallInit L G) (List.finRange n)

/-! ## Partial correctness (proved) -/

theorem mem_succs {G : CFG n α} {u w : Fin n} : w ∈ succs G u ↔ (u, w) ∈ G.edges := by
  simp only [succs, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨he, rfl⟩, rfl⟩; exact he
  · intro h; exact ⟨(u, w), ⟨h, rfl⟩, rfl⟩

theorem propagate_spec {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL) (out : α)
    (ws : List (Fin n)) (x : Fin n → α) (wl : List (Fin n)) :
    (∀ v, L.le (x v) ((propagate L out ws x wl).1 v)) ∧
    (∀ w ∈ ws, L.le out ((propagate L out ws x wl).1 w)) ∧
    (∀ v ∈ wl, v ∈ (propagate L out ws x wl).2) ∧
    (∀ v, (propagate L out ws x wl).1 v ≠ x v → v ∈ (propagate L out ws x wl).2) ∧
    (∀ z : Fin n → α, (∀ v, L.le (x v) (z v)) → (∀ w ∈ ws, L.le out (z w)) →
      ∀ v, L.le ((propagate L out ws x wl).1 v) (z v)) := by
  induction ws generalizing x wl with
  | nil =>
    refine ⟨fun v => hL.refl _, by simp, fun v hv => hv, fun v h => absurd rfl h,
      fun z hz _ v => hz v⟩
  | cons w ws ih =>
    by_cases hle : L.le out (x w)
    · have e : propagate L out (w :: ws) x wl = propagate L out ws x wl := by
        simp [propagate, hle]
      rw [e]
      obtain ⟨ha, hb, hc, hd, he⟩ := ih x wl
      refine ⟨ha, ?_, hc, hd, fun z hz hw => he z hz (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))⟩
      intro w' hw'
      rcases List.mem_cons.1 hw' with rfl | hw'
      · exact hL.trans _ _ _ hle (ha w')
      · exact hb w' hw'
    · have e : propagate L out (w :: ws) x wl =
          propagate L out ws (upd x w (L.join (x w) out)) (w :: wl) := by
        simp [propagate, hle]
      rw [e]
      obtain ⟨ha, hb, hc, hd, he⟩ := ih (upd x w (L.join (x w) out)) (w :: wl)
      have hx1 : ∀ v, L.le (x v) (upd x w (L.join (x w) out) v) := by
        intro v
        by_cases hv : v = w
        · subst hv; simpa [upd] using Lat.le_join_left hL (x v) out
        · simpa [upd, hv] using hL.refl (x v)
      refine ⟨fun v => hL.trans _ _ _ (hx1 v) (ha v), ?_, fun v hv => hc v (List.mem_cons_of_mem _ hv), ?_, ?_⟩
      · intro w' hw'
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact hL.trans _ _ _ (by simpa [upd] using Lat.le_join_right hL (x w') out) (ha w')
        · exact hb w' hw'
      · intro v hv
        by_cases h1 : (propagate L out ws (upd x w (L.join (x w) out)) (w :: wl)).1 v =
            upd x w (L.join (x w) out) v
        · have hvw : v = w := by
            apply Classical.byContradiction
            intro hvw
            rw [h1] at hv
            simp [upd, hvw] at hv
          subst hvw
          exact hc v (List.mem_cons_self ..)
        · exact hd v h1
      · intro z hz hw v
        apply he z _ (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
        intro v'
        by_cases hv : v' = w
        · subst hv
          simpa [upd] using Lat.join_le hL (hz v') (hw v' (List.mem_cons_self ..))
        · simpa [upd, hv] using hz v'

/-- Loop invariant: `x` is below every solution, `init ≤ x entry`, and every edge
whose source is off the worklist is satisfied. -/
def KildallInv (L : Lat α) (G : CFG n α) (x : Fin n → α) (wl : List (Fin n)) : Prop :=
  (∀ y, IsSolution L G y → ∀ v, L.le (x v) (y v)) ∧
  L.le G.init (x G.entry) ∧
  (∀ u w, (u, w) ∈ G.edges → u ∈ wl ∨ L.le (G.f u (x u)) (x w))

theorem kildallInv_init {L : Lat α} (hL : L.IsJSL) (G : CFG n α) :
    KildallInv L G (kildallInit L G) (List.finRange n) := by
  refine ⟨?_, by simpa [kildallInit] using hL.refl G.init, fun u _ _ => Or.inl (List.mem_finRange u)⟩
  intro y hy v
  by_cases hv : v = G.entry
  · subst hv; simpa [kildallInit] using hy.1
  · simpa [kildallInit, hv] using hL.bot_le (y v)

theorem kildallLoop_isLeastSolution {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL)
    (G : CFG n α) (hmono : ∀ u, Monotone L (G.f u)) :
    ∀ fuel x wl x', KildallInv L G x wl → kildallLoop L G fuel x wl = some x' →
      IsLeastSolution L G x' := by
  intro fuel
  induction fuel with
  | zero => intro x wl x' _ h; simp [kildallLoop] at h
  | succ fuel ih =>
    intro x wl x' hinv h
    cases wl with
    | nil =>
      simp only [kildallLoop, Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2, h3⟩ := hinv
      refine ⟨⟨h2, fun u w huw => ?_⟩, h1⟩
      rcases h3 u w huw with h | h
      · simp at h
      · exact h
    | cons u wl =>
      simp only [kildallLoop] at h
      refine ih _ _ x' ?_ h
      obtain ⟨h1, h2, h3⟩ := hinv
      obtain ⟨ha, hb, hc, hd, he⟩ := propagate_spec hL (G.f u (x u)) (succs G u) x wl
      refine ⟨?_, hL.trans _ _ _ h2 (ha _), ?_⟩
      · intro y hy
        apply he y (h1 y hy)
        intro w hw
        exact hL.trans _ _ _ (hmono u _ _ (h1 y hy u)) (hy.2 u w (mem_succs.1 hw))
      · intro v w hvw
        by_cases hch : (propagate L (G.f u (x u)) (succs G u) x wl).1 v = x v
        · rw [hch]
          by_cases hvu : v = u
          · subst hvu
            exact Or.inr (hb w (mem_succs.2 hvw))
          · rcases h3 v w hvw with hv | hv
            · rcases List.mem_cons.1 hv with hv | hv
              · exact absurd hv hvu
              · exact Or.inl (hc v hv)
            · exact Or.inr (hL.trans _ _ _ hv (ha w))
        · exact Or.inl (hd v hch)

/-- Partial correctness: for monotone transfer functions, whenever the solver
returns `some x`, `x` is the least solution (MFP). No height bound needed. -/
theorem kildall_isLeastSolution_of_monotone_of_eq_some {L : Lat α} [DecidableRel L.le]
    (hL : L.IsJSL) (G : CFG n α) (hmono : ∀ u, Monotone L (G.f u)) {fuel : Nat}
    {x : Fin n → α} (h : kildall L G fuel = some x) : IsLeastSolution L G x :=
  kildallLoop_isLeastSolution hL G hmono fuel _ _ x (kildallInv_init hL G) h

/-- The part of the loop invariant that does not need monotonicity: `init ≤ x entry`,
and every edge whose source is off the worklist is satisfied. -/
def KildallSolInv (L : Lat α) (G : CFG n α) (x : Fin n → α) (wl : List (Fin n)) : Prop :=
  L.le G.init (x G.entry) ∧
  (∀ u w, (u, w) ∈ G.edges → u ∈ wl ∨ L.le (G.f u (x u)) (x w))

theorem kildallLoop_isSolution {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL)
    (G : CFG n α) :
    ∀ fuel x wl x', KildallSolInv L G x wl → kildallLoop L G fuel x wl = some x' →
      IsSolution L G x' := by
  intro fuel
  induction fuel with
  | zero => intro x wl x' _ h; simp [kildallLoop] at h
  | succ fuel ih =>
    intro x wl x' hinv h
    cases wl with
    | nil =>
      simp only [kildallLoop, Option.some.injEq] at h
      subst h
      obtain ⟨h2, h3⟩ := hinv
      refine ⟨h2, fun u w huw => ?_⟩
      rcases h3 u w huw with h | h
      · simp at h
      · exact h
    | cons u wl =>
      simp only [kildallLoop] at h
      refine ih _ _ x' ?_ h
      obtain ⟨h2, h3⟩ := hinv
      obtain ⟨ha, hb, hc, hd, _⟩ := propagate_spec hL (G.f u (x u)) (succs G u) x wl
      refine ⟨hL.trans _ _ _ h2 (ha _), ?_⟩
      intro v w hvw
      by_cases hch : (propagate L (G.f u (x u)) (succs G u) x wl).1 v = x v
      · rw [hch]
        by_cases hvu : v = u
        · subst hvu
          exact Or.inr (hb w (mem_succs.2 hvw))
        · rcases h3 v w hvw with hv | hv
          · rcases List.mem_cons.1 hv with hv | hv
            · exact absurd hv hvu
            · exact Or.inl (hc v hv)
          · exact Or.inr (hL.trans _ _ _ hv (ha w))
      · exact Or.inl (hd v hch)

/-- Whatever the transfer functions (monotone or not), whenever the solver returns
`some x`, `x` satisfies every inequation, including those on edges out of
unreachable nodes. -/
theorem kildall_isSolution_of_eq_some {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL)
    (G : CFG n α) {fuel : Nat} {x : Fin n → α} (h : kildall L G fuel = some x) :
    IsSolution L G x :=
  kildallLoop_isSolution hL G fuel _ _ x (kildallInv_init hL G).2 h

/-! ## Termination with an explicit fuel bound -/

/-- Greatest `k ≤ m` satisfying `P` (or `0` if none). -/
def greatestLe (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | m + 1 => if P (m + 1) then m + 1 else greatestLe P m

theorem greatestLe_le (P : Nat → Prop) [DecidablePred P] (m : Nat) : greatestLe P m ≤ m := by
  induction m with
  | zero => simp [greatestLe]
  | succ m ih => simp only [greatestLe]; split <;> omega

theorem greatestLe_spec (P : Nat → Prop) [DecidablePred P] (h0 : P 0) (m : Nat) :
    P (greatestLe P m) := by
  induction m with
  | zero => simpa [greatestLe] using h0
  | succ m ih => simp only [greatestLe]; split <;> assumption

theorem le_greatestLe (P : Nat → Prop) [DecidablePred P] (m : Nat) :
    ∀ k, k ≤ m → P k → k ≤ greatestLe P m := by
  induction m with
  | zero => intro k hk _; omega
  | succ m ih =>
    intro k hk hPk
    simp only [greatestLe]
    split
    · exact hk
    · rename_i hP
      have : k ≠ m + 1 := fun e => hP (e ▸ hPk)
      exact ih k (by omega) hPk

/-- A height bound yields a strictly monotone rank function bounded by the height
(the length of a longest strict chain ending at each element). -/
theorem exists_rank_of_heightLe {L : Lat α} {h : Nat} (hh : L.HeightLe h) :
    ∃ r : α → Nat, (∀ a b, L.lt a b → r a < r b) ∧ ∀ a, r a ≤ h := by
  classical
  let ChainTo : α → Nat → Prop := fun a k =>
    ∃ c : Nat → α, (∀ i, i < k → L.lt (c i) (c (i + 1))) ∧ c k = a
  have h0 : ∀ a, ChainTo a 0 := fun a => ⟨fun _ => a, fun _ hi => absurd hi (by omega), rfl⟩
  have hbound : ∀ a k, ChainTo a k → k ≤ h := fun a k ⟨c, hc, _⟩ => hh k c hc
  have hext : ∀ a b k, ChainTo a k → L.lt a b → ChainTo b (k + 1) := by
    intro a b k ⟨c, hc, hck⟩ hab
    refine ⟨fun i => if i ≤ k then c i else b, ?_, by
      simp only [Nat.not_succ_le_self, ↓reduceIte]⟩
    intro i hi
    by_cases hik : i + 1 ≤ k
    · have := hc i (by omega)
      simpa [show i ≤ k by omega, hik] using this
    · have hik' : i = k := by omega
      subst hik'
      show L.lt (if i ≤ i then c i else b) (if i + 1 ≤ i then c (i + 1) else b)
      simp only [Nat.le_refl, Nat.not_succ_le_self, ↓reduceIte, hck]; exact hab
  refine ⟨fun a => greatestLe (ChainTo a) h, ?_, fun a => greatestLe_le _ h⟩
  intro a b hab
  have ha := greatestLe_spec (ChainTo a) (h0 a) h
  have hb := hext _ _ _ ha hab
  exact le_greatestLe (ChainTo b) h _ (hbound _ _ hb) hb

theorem sum_map_le {β : Type} (l : List β) (g g' : β → Nat) (hle : ∀ v ∈ l, g' v ≤ g v) :
    (l.map g').sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hle a (List.mem_cons_self ..)
    have := ih (fun v hv => hle v (List.mem_cons_of_mem _ hv))
    omega

theorem sum_map_lt {β : Type} (l : List β) (g g' : β → Nat) (hle : ∀ v ∈ l, g' v ≤ g v)
    (hlt : ∃ v ∈ l, g' v < g v) : (l.map g').sum < (l.map g).sum := by
  induction l with
  | nil => obtain ⟨v, hv, _⟩ := hlt; simp at hv
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨v, hv, hvlt⟩ := hlt
    have hsum := sum_map_le l g g' (fun v hv => hle v (List.mem_cons_of_mem _ hv))
    rcases List.mem_cons.1 hv with rfl | hv
    · omega
    · have := ih (fun v hv => hle v (List.mem_cons_of_mem _ hv)) ⟨v, hv, hvlt⟩
      have := hle a (List.mem_cons_self ..)
      omega

theorem sum_map_le_mul {β : Type} (l : List β) (g : β → Nat) (h : Nat) (hg : ∀ v, g v ≤ h) :
    (l.map g).sum ≤ l.length * h := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := hg a
    omega

/-- Potential: worklist length plus remaining rank headroom summed over nodes. -/
def kpot (r : α → Nat) (h : Nat) (x : Fin n → α) (wl : List (Fin n)) : Nat :=
  wl.length + ((List.finRange n).map (fun v => h - r (x v))).sum

theorem propagate_kpot {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL) (r : α → Nat)
    (hr : ∀ a b, L.lt a b → r a < r b) {h : Nat} (hb : ∀ a, r a ≤ h) (out : α)
    (ws : List (Fin n)) (x : Fin n → α) (wl : List (Fin n)) :
    kpot r h (propagate L out ws x wl).1 (propagate L out ws x wl).2 ≤ kpot r h x wl := by
  induction ws generalizing x wl with
  | nil => simp [propagate]
  | cons w ws ih =>
    by_cases hle : L.le out (x w)
    · have e : propagate L out (w :: ws) x wl = propagate L out ws x wl := by
        simp [propagate, hle]
      rw [e]; exact ih x wl
    · have e : propagate L out (w :: ws) x wl =
          propagate L out ws (upd x w (L.join (x w) out)) (w :: wl) := by
        simp [propagate, hle]
      rw [e]
      refine Nat.le_trans (ih _ _) ?_
      have hlt : L.lt (x w) (L.join (x w) out) := by
        refine ⟨Lat.le_join_left hL _ _, fun heq => hle ?_⟩
        rw [heq]; exact Lat.le_join_right hL _ _
      have hrw := hr _ _ hlt
      have hbw := hb (L.join (x w) out)
      have hs := sum_map_lt (List.finRange n) (fun v => h - r (x v))
        (fun v => h - r (upd x w (L.join (x w) out) v))
        (by
          intro v _
          by_cases hv : v = w
          · subst hv; simp [upd]; omega
          · simp [upd, hv])
        ⟨w, List.mem_finRange w, by simp [upd]; omega⟩
      simp only [kpot, List.length_cons]
      omega

theorem kildallLoop_isSome_of_kpot {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL)
    (G : CFG n α) (r : α → Nat) (hr : ∀ a b, L.lt a b → r a < r b) {h : Nat}
    (hb : ∀ a, r a ≤ h) :
    ∀ fuel x wl, kpot r h x wl + 1 ≤ fuel → (kildallLoop L G fuel x wl).isSome := by
  intro fuel
  induction fuel with
  | zero => intro x wl hf; omega
  | succ fuel ih =>
    intro x wl hf
    cases wl with
    | nil => simp [kildallLoop]
    | cons u wl =>
      simp only [kildallLoop]
      apply ih
      have := propagate_kpot hL r hr hb (G.f u (x u)) (succs G u) x wl
      simp only [kpot, List.length_cons] at hf this ⊢
      omega

/-- Termination: on a lattice of height at most `h`, the solver returns a value
(not `none`) whenever `fuel ≥ n * (h + 1) + 1`: at most `n` initial pops, at most
`h` strict increases (hence pushes) per node, and one final step. Monotonicity of
the transfer functions is not needed for termination. -/
theorem kildall_isSome_of_heightLe {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL)
    (G : CFG n α) {h : Nat} (hh : L.HeightLe h) {fuel : Nat}
    (hfuel : n * (h + 1) + 1 ≤ fuel) : (kildall L G fuel).isSome := by
  obtain ⟨r, hr, hb⟩ := exists_rank_of_heightLe hh
  apply kildallLoop_isSome_of_kpot hL G r hr hb
  have hs := sum_map_le_mul (List.finRange n) (fun v => h - r (kildallInit L G v)) h
    (fun v => Nat.sub_le _ _)
  simp only [kpot, List.length_finRange] at hs ⊢
  have : n * (h + 1) = n + n * h := by rw [Nat.mul_succ]; omega
  omega

/-- Kildall computes MFP: for monotone transfer functions on a lattice of height
at most `h`, with `fuel ≥ n * (h + 1) + 1`, the solver returns `some x` and `x` is
the least solution. -/
theorem kildall_eq_some_isLeastSolution_of_monotone_of_heightLe {L : Lat α}
    [DecidableRel L.le] (hL : L.IsJSL)
    (G : CFG n α) (hmono : ∀ u, Monotone L (G.f u)) {h : Nat} (hh : L.HeightLe h)
    {fuel : Nat} (hfuel : n * (h + 1) + 1 ≤ fuel) :
    ∃ x, kildall L G fuel = some x ∧ IsLeastSolution L G x := by
  have hs := kildall_isSome_of_heightLe hL G hh hfuel
  cases hk : kildall L G fuel with
  | none => rw [hk] at hs; simp at hs
  | some x => exact ⟨x, rfl, kildall_isLeastSolution_of_monotone_of_eq_some hL G hmono hk⟩

/-- End to end: for distributive transfer functions on a lattice of height at most
`h`, if every node unreachable from the entry has a strict transfer function, then
with `fuel ≥ n * (h + 1) + 1` the solver returns `some x`, `x` is the least
solution, and `x v` is the MOP value at every node `v`. -/
theorem kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe
    {L : Lat α} [DecidableRel L.le] (hL : L.IsJSL) (G : CFG n α)
    (hdist : ∀ u, Distributive L (G.f u)) (hstrict : UnreachableStrict L G)
    {h : Nat} (hh : L.HeightLe h) {fuel : Nat} (hfuel : n * (h + 1) + 1 ≤ fuel) :
    ∃ x, kildall L G fuel = some x ∧ IsLeastSolution L G x ∧ ∀ v, IsMOPAt L G v (x v) := by
  obtain ⟨x, hk, hx⟩ := kildall_eq_some_isLeastSolution_of_monotone_of_heightLe hL G
    (fun u => monotone_of_distributive hL (hdist u)) hh hfuel
  exact ⟨x, hk, hx, isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict L G hL
    (Lat.acc_of_heightLe hh) hdist hstrict hx⟩

end Toy.Dataflow
