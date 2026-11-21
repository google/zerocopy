import ToySsa.Decide

/-!
Concrete graphs and positive/negative examples for every graph-level definition.
-/
namespace Toy.Ssa

/-- Diamond: `0 → 1 → 3`, `0 → 2 → 3`. -/
def diamond : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (0, 2), (1, 3), (2, 3)] 0

/-- Chain: `0 → 1 → 2`. -/
def chain3 : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (1, 2)] 0

/-- While loop: entry `0`, header `1`, body `2` (back edge `2 → 1`), exit `3`. -/
def loop4 : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (1, 2), (2, 1), (1, 3)] 0

/-- Nested branches where `DF⁺` needs iteration: `0 → 1 → 2 → 3 → 4`, `1 → 3`, `0 → 4`. -/
def ladder5 : Cfg 5 := Cfg.ofEdges 5 [(0, 1), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)] 0

/-- Self-loop: `0 → 1`, `1 → 1`. -/
def selfLoop2 : Cfg 2 := Cfg.ofEdges 2 [(0, 1), (1, 1)] 0

/-! ### Walk -/

theorem walk_example : Walk diamond 0 3 [0, 1, 3] := walk_of_isWalkB (by decide)

theorem not_walk_example : ¬ Walk diamond 0 3 [0, 3] := by
  intro h
  cases h with
  | cons he hw => cases hw with
    | single => exact absurd he (by decide)
    | cons _ hw' => cases hw'

/-! ### Reachability and entry predecessors -/

theorem allReachable_diamond : AllReachable diamond := by
  intro b
  have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by revert b; decide
  rcases this with rfl | rfl | rfl | rfl
  · exact ⟨[0], walk_of_isWalkB (by decide)⟩
  · exact ⟨[0, 1], walk_of_isWalkB (by decide)⟩
  · exact ⟨[0, 2], walk_of_isWalkB (by decide)⟩
  · exact ⟨[0, 1, 3], walk_of_isWalkB (by decide)⟩

/-- Two nodes, no edges: node `1` is unreachable. -/
def isolated2 : Cfg 2 := Cfg.ofEdges 2 [] 0

theorem not_allReachable_isolated2 : ¬ AllReachable isolated2 := by
  intro h
  obtain ⟨p, hp⟩ := h 1
  have := not_walk_of_closed isolated2 (fun v => decide (v = 0)) (by decide) hp (by decide)
  exact absurd this (by decide)

theorem entryNoPreds_diamond : EntryNoPreds diamond := by unfold EntryNoPreds; decide

/-- Two nodes with an edge back into the entry. -/
def backToEntry2 : Cfg 2 := Cfg.ofEdges 2 [(0, 1), (1, 0)] 0

theorem not_entryNoPreds_backToEntry2 : ¬ EntryNoPreds backToEntry2 := fun h =>
  absurd (h 1) (by decide)

/-! ### Dominance and strict dominance -/

theorem dom_example : Dom diamond 0 3 := dom_of_domCheck (by decide)
theorem dom_chain_example : Dom chain3 1 2 := dom_of_domCheck (by decide)
theorem not_dom_example : ¬ Dom diamond 1 3 := not_dom_of_avoidSet (by decide)
theorem sdom_example : SDom diamond 0 3 := ⟨dom_of_domCheck (by decide), by decide⟩
theorem not_sdom_self_example : ¬ SDom diamond 3 3 := fun h => h.2 rfl

/-! ### Dominance frontiers -/

theorem df_example : DF diamond 1 3 := df_of_check (p := 1) (by decide)
theorem not_df_example : ¬ DF diamond 0 3 := not_df_of_check (by decide)
/-- The header of a loop is in the dominance frontier of the loop body. -/
theorem df_loop_example : DF loop4 2 1 := df_of_check (p := 2) (by decide)
/-- `4 ∉ DF(2)` in `ladder5`: one iteration of the frontier does not reach `4`. -/
theorem not_df_ladder_example : ¬ DF ladder5 2 4 := not_df_of_check (by decide)

/-! ### Iterated dominance frontiers -/

/-- In `ladder5`, `4 ∈ DF⁺({2})` although `4 ∉ DF(2)`: `3 ∈ DF(2)` and `4 ∈ DF(3)`. -/
theorem idf_iterates_example : IDF ladder5 (fun x => x = 2) 4 :=
  IDF.step (x := 3) (IDF.base (x := 2) rfl (df_of_check (p := 2) (by decide)))
    (df_of_check (p := 3) (by decide))

theorem not_idf_example (y : Fin 4) : ¬ IDF diamond (fun x => x = diamond.entry) y :=
  not_idf_entry entryNoPreds_diamond y

/-! ### Convergence and join sets -/

theorem inJoin_example : InJoin diamond (fun x => x = 1 ∨ x = 2) 3 :=
  ⟨1, 2, [1, 3], [2, 3], Or.inl rfl, Or.inr rfl,
    by decide, walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide,
    by decide⟩

/-- Cytron et al.'s "or" in condition (3): one walk may be a cycle through the join node. -/
theorem inJoin_cycle_example : InJoin selfLoop2 (fun x => x = 0 ∨ x = 1) 1 :=
  ⟨1, 0, [1, 1], [0, 1], Or.inr rfl, Or.inl rfl,
    by decide, walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide,
    by decide⟩

/-- Two walks sharing an interior node do not converge. -/
theorem not_converge_example : ¬ Converge diamond 0 1 3 [0, 1, 3] [1, 3] := by
  rintro ⟨_, _, _, _, _, h⟩
  have := h ⟨1, by decide⟩ ⟨0, by decide⟩ rfl
  simp at this

/-- A node with a single predecessor is never a join node. -/
theorem not_inJoin_example : ¬ InJoin chain3 (fun x => x = 0 ∨ x = 1) 2 := by
  intro h
  obtain ⟨a, b, hab, ha, hb⟩ := inJoin_two_preds h
  revert a b; decide

/-! ### Reaching definitions -/

theorem reachesTop_example : ReachesTop diamond (fun w => w = 0 ∨ w = 1) 0 3 :=
  ⟨Or.inl rfl, 2, by decide, Clear.step (by decide) (by decide) (Clear.here _)⟩

theorem not_reachesTop_example :
    ¬ ReachesTop diamond (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) 0 3 :=
  not_reachesTop_of_check (by decide)

/-- Diamond with a definition at the entry and in block `1` and a φ at the join `3`. -/
theorem srd_example :
    SingleReachingDef diamond (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => decide (w = 3) = true) := srd_of_check (by decide)

/-- Without the φ at `3`, two definitions (from `0` via `2`, and from `1`) reach the top of `3`. -/
theorem not_srd_example :
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) := by
  intro h
  have := h 3 id (by decide) 0 1
    ⟨Or.inl (Or.inl rfl), 2, by decide, Clear.step (by decide) (by decide) (Clear.here _)⟩
    ⟨Or.inl (Or.inr rfl), 3, by decide, Clear.here _⟩
  exact absurd this (by decide)

/-! ### Nearest strictly dominating definition -/

theorem nearestSDomDef_example : NearestSDomDef chain3 (fun w => w = 0 ∨ w = 1) 2 1 := by
  refine ⟨Or.inr rfl, ⟨dom_of_domCheck (by decide), by decide⟩, ?_⟩
  intro d' hd' _
  rcases hd' with rfl | rfl
  · exact dom_of_domCheck (by decide)
  · exact dom_refl _ _

/-- The entry definition is not the nearest one when block `1` also defines the variable. -/
theorem not_nearestSDomDef_example : ¬ NearestSDomDef chain3 (fun w => w = 0 ∨ w = 1) 2 0 := by
  rintro ⟨_, _, h⟩
  exact not_dom_of_avoidSet (a := 1) (b := 0) (by decide)
    (h 1 (Or.inr rfl) ⟨dom_of_domCheck (by decide), by decide⟩)

end Toy.Ssa
