import ToyViews.Authority

/-!
# Result 1: the naive return rule is unsound once reborrows nest

Rule under test (`NaiveAuthority`, implemented by `endRaw`): "the parent holding the loaned-out
cells may end the borrow" — the child is active, and its active parent holds every cell of the
child as an outstanding loan (`loaned child` for an exclusive child; a depth strictly above the
parent's own baseline for a shared child). Nothing is required of the child's own cells or of the
child's descendants.
-/

namespace Toy.Views
namespace Ex

/-- **R1a (impossibility, exclusive nesting).** Start from `s0` (root `A` owns address `0`,
writable). `A` lends `0` exclusively to `B` (`s1`), and `B` reborrows it exclusively to `C`
(`s2`). All seven loan-tree laws and write exclusivity hold in every state of this trace, and the
naive rule authorizes ending `B` in `s2` although `B` lacks return authority. For every byte the
continuation hands back, the resulting state `s3` has two active writers of address `0` (`A` and
`C`) and `A` regained access while its descendant `C` still covers the cell. -/
theorem naive_end_breaks_safety_of_nested_exclusive_reborrow (r : Addr → Byte) :
    borrow s0 0 [0] = some s1 ∧ borrow s1 1 [0] = some s2 ∧
    LoanTreeInv s0 ∧ LoanTreeInv s1 ∧ LoanTreeInv s2 ∧
    WriteExclusive s0 ∧ WriteExclusive s1 ∧ WriteExclusive s2 ∧
    NaiveAuthority s2 1 ∧ ¬ ReturnAuthority s2 1 ∧
    endRaw s2 1 r = some (s3 (r 0)) ∧
    (s3 (r 0)).canWrite 0 0 = true ∧ (s3 (r 0)).canWrite 2 0 = true ∧
    ¬ WriteExclusive (s3 (r 0)) ∧ ¬ NoResurrection s2 (s3 (r 0)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    naiveAuthority_s2_B, not_returnAuthority_s2_B, rfl, rfl, rfl, of_decide_eq_false rfl, ?_⟩
  intro h
  have := h 0 (of_decide_eq_true rfl) 0 (of_decide_eq_true rfl) (of_decide_eq_true rfl) 2
    (.step (x := 1) rfl (.child rfl)) rfl
  rw [show (s3 (r 0)).covers 2 0 = true from rfl] at this
  exact Bool.noConfusion this

/-- **R1a positive control.** Without the nested reborrow (state `s1`), the same naive end of `B`
is safe: the result is write-exclusive, satisfies all seven laws, and resurrects nothing. (Here the
naive rule and return authority agree.) -/
theorem naive_end_safe_without_nested_reborrow (r : Addr → Byte) :
    LoanTreeInv s1 ∧ NaiveAuthority s1 1 ∧ ReturnAuthority s1 1 ∧
    endRaw s1 1 r = some (s1e (r 0)) ∧ LoanTreeInv (s1e (r 0)) ∧
    WriteExclusive (s1e (r 0)) ∧ NoResurrection s1 (s1e (r 0)) := by
  refine ⟨by decide, ⟨_, 0, _, rfl, rfl, rfl, rfl, by decide⟩, returnAuthority_s1_B, rfl,
    of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  exact noResurrection_of_closed (fun u => if u = 0 then [1] else [])
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)

/-- **R1b (impossibility, shared nesting).** `A` lends `0` to a shared child `B` (`t1`), and `B`
re-shares it to `C` (`t2`). All laws and write exclusivity hold along the trace; the naive rule
authorizes ending `B` in `t2` (the active parent `A` holds the cell at depth `1`, above its
exclusive baseline `0`) although `B` lacks return authority. The result `t3` has `A` back at depth
`0` (writable) while `C` still reads. -/
theorem naive_end_breaks_safety_of_nested_shared_reborrow (r : Addr → Byte) :
    share s0 0 [0] = some t1 ∧ share t1 1 [0] = some t2 ∧
    LoanTreeInv t1 ∧ LoanTreeInv t2 ∧ WriteExclusive t1 ∧ WriteExclusive t2 ∧
    NaiveAuthority t2 1 ∧ ¬ ReturnAuthority t2 1 ∧
    endRaw t2 1 r = some t3 ∧ t3.canWrite 0 0 = true ∧ t3.canRead 2 0 = true ∧
    ¬ WriteExclusive t3 ∧ ¬ NoResurrection t2 t3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    naiveAuthority_t2_B, not_returnAuthority_t2_B, rfl, by decide, by decide,
    by decide, ?_⟩
  intro h
  have := h 0 (by decide) 0 (by decide) (by decide) 2 (.step (x := 1) rfl (.child rfl)) rfl
  exact absurd this (by decide)

/-- **R1b positive control.** Without the nested shared reborrow (state `t1`), the naive end of
`B` is safe. -/
theorem naive_end_safe_without_nested_shared_reborrow (r : Addr → Byte) :
    LoanTreeInv t1 ∧ NaiveAuthority t1 1 ∧ ReturnAuthority t1 1 ∧
    endRaw t1 1 r = some t1e ∧ LoanTreeInv t1e ∧ WriteExclusive t1e ∧ NoResurrection t1 t1e := by
  refine ⟨by decide, ⟨_, 0, _, rfl, rfl, rfl, rfl, by decide⟩,
    returnAuthority_of_closed [] (by decide) (by decide), rfl, by decide, by decide, ?_⟩
  exact noResurrection_of_closed (fun u => if u = 0 then [1] else []) (by decide) (by decide)

/-! ## A naive end that single-step checks do not catch -/

/-- `v2`: `A` has two shared children `B₁` (id 1) and `B₂` (id 2) (`A` at depth `2`), and `B₁`
has re-shared address `0` to `C` (id 3). -/
def v2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 2 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 2 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `v2e1`: the naive end of `B₁` in `v2` (`A` drops to depth `1`; `C` still reads under the
retired `B₁`). -/
def v2e1 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 2 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `v2e2`: the subsequent end of `B₂` in `v2e1` (`A` back at depth `0`). -/
def v2e2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 2 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

set_option synthInstance.maxSize 4096 in
/-- **Single-step write exclusivity and no-resurrection are not an inductive safety criterion.**
In `v2` all seven laws hold and `B₁` lacks return authority, yet its naive end yields a state
`v2e1` that is still write-exclusive, and the step satisfies `NoResurrection` (the coarse access
level of `A` stays at "read"); only `LoanTreeInv` detects the damage. The next end, of `B₂`, *has*
return authority in `v2e1`, but it makes `A` writable while `C` still reads. -/
theorem naive_shared_end_hidden_by_sibling_reader (r : Addr → Byte) :
    LoanTreeInv v2 ∧ ¬ ReturnAuthority v2 1 ∧ endRaw v2 1 r = some v2e1 ∧
    WriteExclusive v2e1 ∧ NoResurrection v2 v2e1 ∧ ¬ LoanTreeInv v2e1 ∧
    ReturnAuthority v2e1 2 ∧ endRaw v2e1 2 r = some v2e2 ∧
    ¬ WriteExclusive v2e2 ∧ ¬ NoResurrection v2e1 v2e2 := by
  refine ⟨by decide, ?_, rfl, by decide,
    noResurrection_of_closed (fun _ => [1, 2, 3]) (by decide) (by decide), by decide,
    returnAuthority_of_closed [] (by decide) (by decide), rfl, by decide, ?_⟩
  · intro h
    have := h 3 (.child (by decide)) (by decide) 0 (by decide)
    exact absurd this (by decide)
  · intro h
    have := h 0 (by decide) 0 (by decide) (by decide) 3 (.step (x := 1) rfl (.child rfl)) rfl
    exact absurd this (by decide)

end Ex
end Toy.Views
