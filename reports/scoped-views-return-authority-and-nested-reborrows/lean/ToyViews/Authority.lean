import ToyViews.States

/-!
# Descendants, return authority, the naive rule, and no-resurrection
-/

namespace Toy.Views

/-- `ProperDesc s d c`: `d` is a proper descendant of `c`, i.e. following parent links from `d`
(through existing views) reaches `c` in one or more steps. Retired views still count: being
inactive does not cut a view out of the tree. -/
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c

/-- Refuting or enumerating descendants on concrete states: every proper descendant of `c` lies
in any list `S` that contains each view whose parent is `c` or is already in `S`. -/
theorem ProperDesc.mem_of_closed {s : State} {c : ViewId} {S : List ViewId}
    (h : ∀ d < s.size, ∀ p, s.parentOf d = some p → (p = c ∨ p ∈ S) → d ∈ S) :
    ∀ {d}, ProperDesc s d c → d ∈ S := by
  intro d hd
  induction hd with
  | child hp => exact h _ (State.lt_size_of_parentOf hp) _ hp (Or.inl rfl)
  | step hp _ ih => exact h _ (State.lt_size_of_parentOf hp) _ hp (Or.inr (ih h))

/-- **Return authority** for ending view `c`: no active proper descendant of `c` covers any cell
that `c` covers. -/
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false

/-- Proving return authority on a concrete state from a closed over-approximation `S` of the
descendants of `c`. -/
theorem returnAuthority_of_closed {s : State} {c : ViewId} (S : List ViewId)
    (hS : ∀ d < s.size, ∀ p, s.parentOf d = some p → (p = c ∨ p ∈ S) → d ∈ S)
    (hA : ∀ d ∈ S, s.isActive d = true → ∀ a < s.width, s.covers c a = true →
      s.covers d a = false) :
    ReturnAuthority s c := by
  intro d hd hact a hc
  exact hA d (ProperDesc.mem_of_closed hS hd) hact a (State.covers_lt_width hc) hc

/-- **The naive rule**: "the parent holding the loaned-out cells may end the borrow". View `c`
exists and is active, has an existing parent, and that parent is active and holds every cell `c`
covers as an outstanding loan (`loaned c` for an exclusive child; an `own` cell at a depth strictly
above the parent's own mode baseline for a shared child). Here "the parent owns the loaned-out
cells" refers to the *parent's* placeholder cells, not to the child's cells. Nothing is required of
`c`'s own cells or of `c`'s descendants. -/
def NaiveAuthority (s : State) (c : ViewId) : Prop :=
  ∃ vc p vp, s.view? c = some vc ∧ vc.active = true ∧ vc.parent = some p ∧
    s.view? p = some vp ∧ returnable vc vp c = true

theorem view?_setView_isSome {s : State} {p c : ViewId} {vw : View} (hc : c < s.size) :
    ((s.setView p vw).view? c).isSome = true := by
  unfold State.setView State.view?
  unfold State.size at hc
  simp [List.length_set, hc]

/-- `endRaw` implements exactly the naive rule: it is enabled iff `NaiveAuthority s c` holds. -/
theorem endRaw_isSome_iff (s : State) (c : ViewId) (r : Addr → Byte) :
    (endRaw s c r).isSome = true ↔ NaiveAuthority s c := by
  unfold endRaw NaiveAuthority
  cases hvc : s.view? c with
  | none => simp
  | some vc =>
    simp only
    cases hp : vc.parent with
    | none => simp [hp]
    | some p =>
      simp only
      cases hvp : s.view? p with
      | none => simp [hp, hvp]
      | some vp =>
        have hc : c < s.size := State.lt_size_of_view?_eq_some hvc
        have hs := view?_setView_isSome (s := s) (p := p) (vw := restoreCells vc vp r) hc
        simp only
        split
        · rename_i hret
          cases h1 : (s.setView p (restoreCells vc vp r)).view? c with
          | none => rw [h1] at hs; simp at hs
          | some vc₁ =>
            simp only [Bool.and_eq_true] at hret
            simp only [Option.isSome_some, true_iff]
            exact ⟨vc, p, vp, rfl, hret.1, hp, hvp, hret.2⟩
        · rename_i hret
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          rintro ⟨vc', p', vp', h1, hact, h2, h3, h4⟩
          cases h1; rw [hp] at h2; cases h2; rw [hvp] at h3; cases h3
          exact hret (by simp [hact, h4])

/-- Root views (no parent) can never be ended by `endRaw`. -/
theorem endRaw_eq_none_of_parentOf_eq_none {s : State} {c : ViewId} (h : s.parentOf c = none)
    (r : Addr → Byte) : endRaw s c r = none := by
  unfold endRaw
  unfold State.parentOf at h
  cases hvc : s.view? c with
  | none => rfl
  | some vc =>
    rw [hvc] at h
    simp only [Option.bind_some] at h
    simp [h]

/-- **Local return check** on view `c`: every cell `c` covers is held by `c` itself as an `own`
cell at exactly `c`'s mode baseline depth (`0` for an exclusive view, `1` for a shared view), i.e.
`c` has lent none of its cells onward, exclusively or shared. Unlike `ReturnAuthority`, it inspects
only `c`'s own cells, not `c`'s descendants. -/
def LocalReturnCheck (s : State) (c : ViewId) : Prop :=
  ∀ a < s.width, s.covers c a = true → s.depth? c a = some (s.baselineOf c)

instance (s : State) (c : ViewId) : Decidable (LocalReturnCheck s c) := by
  unfold LocalReturnCheck; infer_instance

/-- **No resurrection** across a step `s → s'`: whenever some view `u` gains access to a cell
(its access level goes up), no active proper descendant of `u` still covers that cell in `s'`. -/
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false

/-- Proving no-resurrection on concrete states from closed over-approximations `S u` of the
descendants of each view `u`. -/
theorem noResurrection_of_closed {s s' : State} (S : ViewId → List ViewId)
    (hS : ∀ u < s'.size, ∀ d < s'.size, ∀ p, s'.parentOf d = some p → (p = u ∨ p ∈ S u) →
      d ∈ S u)
    (hA : ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
      ∀ d ∈ S u, s'.isActive d = true → s'.covers d a = false) :
    NoResurrection s s' := by
  intro u hu a ha hlv d hd hact
  exact hA u hu a ha hlv d (ProperDesc.mem_of_closed (hS u hu) hd) hact

/-! ## Definition examples -/

namespace Ex

/-- Positive: `C` is a proper descendant of `A` in the nested state `s2` (via `B`). -/
theorem properDesc_s2_C_A : ProperDesc s2 2 0 :=
  .step (x := 1) (by decide) (.child (by decide))

/-- Negative: `A` is not a proper descendant of `C` in `s2`. -/
theorem not_properDesc_s2_A_C : ¬ ProperDesc s2 0 2 := by
  intro h
  have := ProperDesc.mem_of_closed (S := []) (by decide) h
  simp at this

/-- Positive: in `s2` the innermost view `C` has return authority (it has no descendants). -/
theorem returnAuthority_s2_C : ReturnAuthority s2 2 :=
  returnAuthority_of_closed [] (by decide) (by decide)

/-- Positive: in `s1`, `B` has return authority. -/
theorem returnAuthority_s1_B : ReturnAuthority s1 1 :=
  returnAuthority_of_closed [] (by decide) (by decide)

/-- Positive: in `t2`, the innermost shared view `C` has return authority. -/
theorem returnAuthority_t2_C : ReturnAuthority t2 2 :=
  returnAuthority_of_closed [] (by decide) (by decide)

/-- Negative: in `s2`, `B` lacks return authority: its active child `C` covers address `0`. -/
theorem not_returnAuthority_s2_B : ¬ ReturnAuthority s2 1 := by
  intro h
  have := h 2 (.child (by decide)) (by decide) 0 (by decide)
  exact absurd this (by decide)

/-- Negative: in `t2`, `B` lacks return authority: its active shared child `C` covers `0`. -/
theorem not_returnAuthority_t2_B : ¬ ReturnAuthority t2 1 := by
  intro h
  have := h 2 (.child (by decide)) (by decide) 0 (by decide)
  exact absurd this (by decide)

/-- Positive: the naive rule authorizes ending `B` in `s2` — even though `B`'s child `C` is still
active. -/
theorem naiveAuthority_s2_B : NaiveAuthority s2 1 :=
  ⟨_, 0, _, rfl, rfl, rfl, rfl, by decide⟩

/-- Positive: the naive rule authorizes ending the shared view `B` in `t2` (its parent `A` is at
depth `1`, above `A`'s exclusive baseline `0`) — even though `B`'s shared child `C` still reads. -/
theorem naiveAuthority_t2_B : NaiveAuthority t2 1 :=
  ⟨_, 0, _, rfl, rfl, rfl, rfl, by decide⟩

/-- Negative: the naive rule never authorizes ending a root (no parent), e.g. `A` in `s2`. -/
theorem not_naiveAuthority_s2_A : ¬ NaiveAuthority s2 0 := by
  rintro ⟨vc, p, vp, h1, -, h2, -, -⟩
  cases h1; cases h2

/-- Negative (parent holds no loan for the child): in `weExclChildLoaned` the active exclusive
child `B` covers address `0` but its parent `A` holds `own 0 0`, not `loaned 1`. -/
theorem not_naiveAuthority_weExclChildLoaned_B : ¬ NaiveAuthority weExclChildLoaned 1 :=
  fun h => absurd ((endRaw_isSome_iff _ _ (fun _ => 0)).mpr h) (by decide)

/-- Negative (shared parent at its own baseline): in `t2flat` the shared view `B` holds address
`0` at depth `1`, which is its own shared baseline, so it records no outstanding shared loan; the
naive rule does not authorize ending `B`'s shared child `C`. -/
theorem not_naiveAuthority_t2flat_C : ¬ NaiveAuthority t2flat 2 :=
  fun h => absurd ((endRaw_isSome_iff _ _ (fun _ => 0)).mpr h) (by decide)

/-- Negative (retired parent): in `s3 0` the view `C` is active and its parent `B` still holds
`loaned 2`, but `B` is retired, so nothing is restored into it. -/
theorem not_naiveAuthority_s3_C : ¬ NaiveAuthority (s3 0) 2 :=
  fun h => absurd ((endRaw_isSome_iff _ _ (fun _ => 0)).mpr h) (by decide)

/-- Negative (retired child): in `aS0` the parent `B` holds `loaned 2`, but the child `C` is
retired. -/
theorem not_naiveAuthority_aS0_C : ¬ NaiveAuthority aS0 2 :=
  fun h => absurd ((endRaw_isSome_iff _ _ (fun _ => 0)).mpr h) (by decide)

/-- Negative (child retired, parent no longer holds its loan): after the naive end of `B` in
`s2`, ending `B` again is refused: `B` is inactive, and `A` now holds `own 0 _` rather than
`loaned 1`. -/
theorem not_naiveAuthority_s3_B : ¬ NaiveAuthority (s3 0) 1 :=
  fun h => absurd ((endRaw_isSome_iff _ _ (fun _ => 0)).mpr h) (by decide)

/-- Positive: the local return check passes for views that have lent nothing onward: `B` in `s1`
(exclusive, depth `0`), `B` in `t1` (shared, depth `1`), and `C` in `s2`. -/
theorem localReturnCheck_examples_pos :
    LocalReturnCheck s1 1 ∧ LocalReturnCheck t1 1 ∧ LocalReturnCheck s2 2 := by decide

/-- Negative: the local return check refuses `B` in the nested states `s2` (`B`'s cell is
`loaned 2`) and `t2` (`B`'s depth is `2`, above its shared baseline `1`) — exactly the ends that
the naive rule wrongly authorizes. -/
theorem localReturnCheck_examples_neg : ¬ LocalReturnCheck s2 1 ∧ ¬ LocalReturnCheck t2 1 := by
  decide

/-- Positive: `NoResurrection` holds for the sound end of `B` in `s1`: `A` regains write access to
`0` and no active descendant of `A` covers `0` afterwards. -/
theorem noResurrection_s1_end_B : NoResurrection s1 (s1e 0) :=
  noResurrection_of_closed (fun u => if u = 0 then [1] else []) (by decide) (by decide)

/-- Negative: `NoResurrection` fails for the naive end of `B` in `s2`: `A` regains write access to
`0` while its descendant `C` (via the retired `B`) is active and covers `0`. -/
theorem not_noResurrection_s2_end_B : ¬ NoResurrection s2 (s3 0) := by
  intro h
  have := h 0 (by decide) 0 (by decide) (by decide) 2 (.step (x := 1) (by decide) (.child (by decide)))
    (by decide)
  exact absurd this (by decide)

/-- Operation examples: `borrow` and `share` succeed on writable/owned cells and fail otherwise. -/
theorem borrow_s0 : borrow s0 0 [0] = some s1 := by decide
theorem borrow_s1 : borrow s1 1 [0] = some s2 := by decide
theorem borrow_s1_A_none : borrow s1 0 [0] = none := by decide
theorem borrow_t1_B_none : borrow t1 1 [0] = none := by decide
theorem share_s0 : share s0 0 [0] = some t1 := by decide
theorem share_t1 : share t1 1 [0] = some t2 := by decide
theorem share_s1_A_none : share s1 0 [0] = none := by decide

/-- `endRaw` examples. -/
theorem endRaw_s1_B (r : Addr → Byte) : endRaw s1 1 r = some (s1e (r 0)) := rfl
theorem endRaw_s2_B (r : Addr → Byte) : endRaw s2 1 r = some (s3 (r 0)) := rfl
theorem endRaw_s2_C (r : Addr → Byte) : endRaw s2 2 r = some (s2e (r 0)) := rfl
theorem endRaw_t1_B (r : Addr → Byte) : endRaw t1 1 r = some t1e := rfl
theorem endRaw_t2_B (r : Addr → Byte) : endRaw t2 1 r = some t3 := rfl
theorem endRaw_u2_B (r : Addr → Byte) : endRaw u2 1 r = some u2e := rfl
theorem endRaw_s2_A_none (r : Addr → Byte) : endRaw s2 0 r = none := rfl

/-- Access-level examples: `B` writes in `s1` while `A` (loaned) has no access; in `t1` both `A`
(depth 1) and `B` (shared, depth 1) read and neither writes; the retired `B` in `s1e 0` has no
access. -/
theorem access_examples :
    s1.canWrite 1 0 = true ∧ s1.canRead 0 0 = false ∧ t1.canRead 0 0 = true ∧
    t1.canWrite 0 0 = false ∧ t1.canRead 1 0 = true ∧ t1.canWrite 1 0 = false ∧
    (s1e 0).canRead 1 0 = false ∧ s1.level 1 0 = 2 ∧ t1.level 0 0 = 1 ∧ s1.level 0 0 = 0 := by
  decide

/-- Counting and domain examples. -/
theorem count_domain_examples :
    u2.activeSharedChildren 0 0 = 2 ∧ u2e.activeSharedChildren 0 0 = 1 ∧
    t2.activeSharedChildren 0 0 = 1 ∧ (w2.view? 1).map View.domain = some [0] ∧
    (w2.view? 2).map View.domain = some [1] ∧ (w2.view? 0).map View.domain = some [0, 1] := by
  decide

/-- `read`/`write` examples: access through an active view succeeds; through a retired view or a
loaned cell it fails. -/
theorem read_s1_B : read s1 1 0 = some 0 := by decide
theorem read_s1_A_none : read s1 0 0 = none := by decide
theorem read_s1e_B_none : read (s1e 3) 1 0 = none := by decide
theorem write_t1_A_none : write t1 0 0 9 = none := by decide

end Ex
end Toy.Views
