import ToyViews.Closed

/-!
# Result 5: the sharing depth read as a counting permission

Under `DepthCounts`, the depth of an active view's accessible cell is its mode baseline plus the
number of its active shared children on that cell. For an exclusive-mode view this is a
source-with-counter reading (depth `n` = `n` outstanding read loans; depth `0` = full,
writable). Each view's counter counts only its *direct* shared children: a reader two levels down
is recorded in the intermediate view's counter, not in the root's. So a rule that consults only
the parent's counter when a child ends can be fooled (R5b), while a rule that also consults the
ending child's own counter (the local return check, R2d) cannot.
-/

namespace Toy.Views

/-- **R5a.** Under `DepthCounts`, an active view can write a cell it holds as `own` iff it is
exclusive-mode and no active shared child reads that cell. -/
theorem canWrite_iff_excl_and_no_active_shared_children_of_depthCounts
    {s : State} {v : ViewId} {a : Addr} (hdc : DepthCounts s)
    (hact : s.isActive v = true) (hown : (s.depth? v a).isSome = true) :
    s.canWrite v a = true ↔ (s.modeOf v = some .excl ∧ s.activeSharedChildren v a = 0) := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hown
  have hv := State.isActive_lt_size hact
  have hcov : s.covers v a = true := by
    unfold State.covers; unfold State.depth? at hd
    cases hc : s.cell? v a with
    | none => rw [hc] at hd; simp at hd
    | some _ => rfl
  have ha := State.covers_lt_width hcov
  have heq := hdc v hv a ha d hd hact
  cases hvw : s.view? v with
  | none => unfold State.isActive at hact; rw [hvw] at hact; simp at hact
  | some vw =>
    have hmode : s.modeOf v = some vw.mode := by unfold State.modeOf; rw [hvw]; rfl
    have hbase : s.baselineOf v = vw.mode.baseline := by
      unfold State.baselineOf; rw [hmode]; rfl
    rw [hbase] at heq
    unfold State.canWrite
    rw [hact, hd, hmode]
    cases hm : vw.mode with
    | excl =>
      rw [hm] at heq
      simp only [Mode.baseline, Nat.zero_add] at heq
      subst heq
      simp
    | shared =>
      rw [hm] at heq
      simp only [Mode.baseline] at heq
      subst heq
      simp only [Bool.true_and, beq_iff_eq, Option.some.injEq, reduceCtorEq, false_and,
        iff_false]
      omega

namespace Ex

/-- **R5a non-vacuity (both polarities).** Under `DepthCounts`: `A` in `t1` (one shared reader)
cannot write, and the right-hand side fails because of the counter; `B` in `w2` (exclusive, no
shared children) can write and the right-hand side holds; `B` in `t1` (shared-mode) cannot write,
and the right-hand side fails because of the mode. -/
theorem canWrite_iff_nonvacuous :
    (DepthCounts t1 ∧ t1.isActive 0 = true ∧ (t1.depth? 0 0).isSome = true ∧
      t1.canWrite 0 0 = false ∧ t1.activeSharedChildren 0 0 = 1) ∧
    (DepthCounts w2 ∧ w2.isActive 1 = true ∧ (w2.depth? 1 0).isSome = true ∧
      w2.canWrite 1 0 = true ∧ w2.modeOf 1 = some .excl ∧ w2.activeSharedChildren 1 0 = 0) ∧
    (DepthCounts t1 ∧ t1.isActive 1 = true ∧ (t1.depth? 1 0).isSome = true ∧
      t1.canWrite 1 0 = false ∧ t1.modeOf 1 = some .shared) := by decide

/-- R5a tightness, `DepthCounts`: in `weDepthCounts` the shared child `B` holds depth `0`: it can
write, though it is shared-mode. -/
theorem canWrite_iff_needs_depthCounts :
    ¬ DepthCounts weDepthCounts ∧ weDepthCounts.isActive 1 = true ∧
      (weDepthCounts.depth? 1 0).isSome = true ∧ weDepthCounts.canWrite 1 0 = true ∧
      weDepthCounts.modeOf 1 = some .shared := by decide

/-- R5a tightness, activity: the retired `B` in `s1e 0` holds depth `0`, is exclusive-mode with no
shared children, yet cannot write. -/
theorem canWrite_iff_needs_isActive :
    DepthCounts (s1e 0) ∧ (s1e 0).isActive 1 = false ∧ ((s1e 0).depth? 1 0).isSome = true ∧
      (s1e 0).canWrite 1 0 = false ∧ (s1e 0).modeOf 1 = some .excl ∧
      (s1e 0).activeSharedChildren 1 0 = 0 := by decide

/-- R5a tightness, `own` cell: `A` in `s1` holds address `0` as `loaned 1` (no depth): it is
exclusive-mode with no shared children, yet cannot write. -/
theorem canWrite_iff_needs_own :
    DepthCounts s1 ∧ s1.isActive 0 = true ∧ (s1.depth? 0 0).isSome = false ∧
      s1.canWrite 0 0 = false ∧ s1.modeOf 0 = some .excl ∧ s1.activeSharedChildren 0 0 = 0 := by
  decide

/-- **R5b (exact per-view counters do not prevent the nested shared failure).** In `t2` the
invariant holds and every counter is exact: `A` counts its one direct shared child `B`, and `B`
counts its one direct shared child `C` (so `B`'s own depth `2` is above its shared baseline `1`, and
`B` fails the local return check). The naive end of `B` — authorized because the rule consults the
parent `A`'s cell only — brings `A`'s counter to zero, and `A` can write while the grandchild `C`
still reads. Yet `DepthCounts` still holds in the result `t3`; what breaks is
`ParentCoversActive` (`C` is active under the retired `B`), and with it write exclusivity. -/
theorem depthCounts_survives_naive_shared_end_while_writeExclusive_fails (r : Addr → Byte) :
    LoanTreeInv t2 ∧ t2.activeSharedChildren 0 0 = 1 ∧ t2.activeSharedChildren 1 0 = 1 ∧
    ¬ LocalReturnCheck t2 1 ∧ NaiveAuthority t2 1 ∧
    endRaw t2 1 r = some t3 ∧ t3.activeSharedChildren 0 0 = 0 ∧ DepthCounts t3 ∧
    ¬ ParentCoversActive t3 ∧ t3.canWrite 0 0 = true ∧ t3.canRead 2 0 = true ∧
    ¬ WriteExclusive t3 :=
  ⟨by decide, by decide, by decide, by decide, naiveAuthority_t2_B, rfl, by decide, by decide,
   by decide, by decide, by decide, by decide⟩

/-- R5b positive control: without the nested reader (`t1`), the parent's counter reaching zero
after the end of `B` does mean that no reader remains, and the result is write-exclusive. -/
theorem parent_counter_zero_means_no_reader_without_nesting (r : Addr → Byte) :
    endRaw t1 1 r = some t1e ∧ t1e.activeSharedChildren 0 0 = 0 ∧ t1e.canWrite 0 0 = true ∧
      LoanTreeInv t1e ∧ WriteExclusive t1e :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

end Ex
end Toy.Views
