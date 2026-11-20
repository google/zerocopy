import ToyChecker.DownSet

/-!
# Anchors, allowlists, and finite test suites

An *anchor set* is a finite list `A` of programs known to be good. The
anchored law asks for soundness plus acceptance of every anchor. It excludes
`rejectAll` exactly when `A` is nonempty, and it always admits the allowlist
checker of `A` (a lookup table) when the anchors are good. Beyond the
anchors it constrains nothing except through soundness: the programs every
admitted checker must accept are exactly the anchors, and the programs every
admitted checker must reject are exactly the bad ones.

The same phenomenon for arbitrary finite test suites with expected answers:
whenever some sound checker passes a finite suite, the lookup table built
from the suite's positive entries is sound, passes the suite, and is below
that checker. This is the exact strength of the informal remark "a lookup
table can pass any finite test".

These laws are *pointwise*: each constrains the answer on finitely many
individual programs. A law that relates answers on different programs (for
example "accepting `p` forces accepting `2 * p`") is still a law on
input–output behavior, yet a single anchor plus such a closure requirement
excludes every finite allowlist and lookup table while admitting
conservative, incomplete checkers (`positive_control_doubling_law_*`).
-/

namespace Toy.Checker

universe u

/-! ## Anchored soundness -/

/-- `AnchoredSound good A c`: `c` is sound and accepts every anchor in the
finite list `A`. Captures a framework law of the form "never accept a bad
program, and accept these known-good reference programs". -/
def AnchoredSound {P : Type u} (good : P → Prop) (A : List P) (c : P → Bool) : Prop :=
  Sound good c ∧ ∀ a ∈ A, c a = true

/-- Positive example: the exact parity checker satisfies the anchored law
with anchors `[0, 2]`. -/
theorem anchoredSound_example_evenExact : AnchoredSound evenGood [0, 2] evenExact :=
  ⟨sound_example_evenExact, by decide⟩

/-- Negative example: `rejectAll` violates the anchored law with anchor
`[0]`. -/
theorem not_anchoredSound_example_rejectAll : ¬ AnchoredSound evenGood [0] rejectAll := by
  rintro ⟨_, h⟩
  have := h 0 (by simp)
  simp [rejectAll] at this

/-- Negative example: an unsound checker violates the anchored law even if
it accepts the anchors. -/
theorem not_anchoredSound_example_acceptAll : ¬ AnchoredSound evenGood [0] acceptAll :=
  fun h => not_sound_example_acceptAll h.1

/-- R2a (part). The anchored law excludes `rejectAll` iff the anchor list is
nonempty. No assumption that the anchors are good is needed. -/
theorem not_anchoredSound_rejectAll_iff_anchors_ne_nil {P : Type u} (good : P → Prop)
    (A : List P) : ¬ AnchoredSound good A rejectAll ↔ A ≠ [] := by
  constructor
  · intro h hA
    subst hA
    exact h ⟨sound_rejectAll good, fun a ha => by simp at ha⟩
  · intro hA h
    cases A with
    | nil => exact hA rfl
    | cons a l =>
      have := h.2 a (by simp)
      simp [rejectAll] at this

/-- R2a (part). If all anchors are good, the anchored law admits the
allowlist checker of the anchors. -/
theorem allowlist_anchoredSound_of_anchors_good {P : Type u} [DecidableEq P]
    {good : P → Prop} {A : List P} (hA : ∀ a ∈ A, good a) :
    AnchoredSound good A (allowlist A) := by
  refine ⟨fun p hp => hA p ?_, fun a ha => ?_⟩
  · simpa [allowlist] using hp
  · simpa [allowlist] using ha

/-- R2c (part). Anchors constrain acceptance only on anchors: if all anchors
are good, a program is accepted by every checker admitted by the anchored law
iff it is an anchor. (Without `[DecidableEq P]` the witness allowlist is built
with classical decidable equality.) -/
theorem forced_accept_iff_mem_anchors_of_anchors_good {P : Type u} {good : P → Prop} {A : List P}
    (hA : ∀ a ∈ A, good a) (p : P) :
    (∀ c, AnchoredSound good A c → c p = true) ↔ p ∈ A := by
  classical
  constructor
  · intro h
    have := h (allowlist A) (allowlist_anchoredSound_of_anchors_good hA)
    simpa [allowlist] using this
  · intro hp c hc
    exact hc.2 p hp

/-- R2c (part). If all anchors are good, a program is rejected by every
checker admitted by the anchored law iff it is bad. (Classical, as above.) -/
theorem forced_reject_iff_not_good_of_anchors_good {P : Type u} {good : P → Prop} {A : List P}
    (hA : ∀ a ∈ A, good a) (p : P) :
    (∀ c, AnchoredSound good A c → c p = false) ↔ ¬ good p := by
  classical
  constructor
  · intro h hp
    have hA' : ∀ a ∈ p :: A, good a := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hp
      · exact hA a ha
    have h1 := allowlist_anchoredSound_of_anchors_good hA'
    have h2 : AnchoredSound good A (allowlist (p :: A)) :=
      ⟨h1.1, fun a ha => h1.2 a (List.mem_cons.mpr (Or.inr ha))⟩
    have := h _ h2
    simp [allowlist] at this
  · intro hp c hc
    cases h : c p with
    | false => rfl
    | true => exact absurd (hc.1 p h) hp

/-- R2c (part). The witness family behind the forced-acceptance statement:
for any good non-anchor `p`, the allowlists of `A` and of `p :: A` are both
admitted by the anchored law, and they disagree on `p`. -/
theorem anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good
    {P : Type u} [DecidableEq P] {good : P → Prop} {A : List P} {p : P}
    (hA : ∀ a ∈ A, good a) (hp : good p) (hpA : p ∉ A) :
    AnchoredSound good A (allowlist A) ∧ AnchoredSound good A (allowlist (p :: A)) ∧
    allowlist A p = false ∧ allowlist (p :: A) p = true := by
  have hA' : ∀ a ∈ p :: A, good a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hp
    · exact hA a ha
  have h1 := allowlist_anchoredSound_of_anchors_good hA'
  refine ⟨allowlist_anchoredSound_of_anchors_good hA,
    ⟨h1.1, fun a ha => h1.2 a (List.mem_cons.mpr (Or.inr ha))⟩, ?_, ?_⟩
  · simpa [allowlist] using hpA
  · simp [allowlist]

/-! ## Finite test suites and lookup tables -/

/-- A finite test suite: programs paired with the expected answer. -/
abbrev TestSuite (P : Type u) : Type u := List (P × Bool)

/-- `Passes c T`: the checker `c` gives the expected answer on every entry of
the suite `T`. Captures conformance testing of a tool against a fixed finite
set of reference inputs. -/
def Passes {P : Type u} (c : P → Bool) (T : TestSuite P) : Prop :=
  ∀ q ∈ T, c q.1 = q.2

instance {P : Type u} (c : P → Bool) (T : TestSuite P) : Decidable (Passes c T) :=
  inferInstanceAs (Decidable (∀ q ∈ T, c q.1 = q.2))

/-- The lookup table of a suite: accept exactly the programs listed in `T`
with expected answer `true`. -/
def tableChecker {P : Type u} [DecidableEq P] (T : TestSuite P) : P → Bool :=
  fun p => decide ((p, true) ∈ T)

/-- Anchors are a special case of test suites: the anchored law is soundness
plus passing the suite that expects `true` on every anchor. -/
theorem anchoredSound_iff_sound_passes_anchorSuite {P : Type u} (good : P → Prop)
    (A : List P) (c : P → Bool) :
    AnchoredSound good A c ↔ Sound good c ∧ Passes c (A.map (fun a => (a, true))) := by
  unfold AnchoredSound Passes
  constructor
  · rintro ⟨hs, ha⟩
    refine ⟨hs, fun q hq => ?_⟩
    obtain ⟨a, haA, rfl⟩ := List.mem_map.mp hq
    exact ha a haA
  · rintro ⟨hs, hp⟩
    exact ⟨hs, fun a ha => hp (a, true) (List.mem_map.mpr ⟨a, ha, rfl⟩)⟩

/-- Positive example: the exact parity checker passes a small suite with
both answers. -/
theorem passes_example_evenExact : Passes evenExact [(0, true), (1, false), (2, true)] := by
  decide

/-- Negative example: `rejectAll` fails a suite containing a positive
entry. -/
theorem not_passes_example_rejectAll : ¬ Passes rejectAll [((0 : Nat), true)] := by
  intro h
  have := h (0, true) (by simp)
  simp [rejectAll] at this

/-- Negative example: no checker passes an inconsistent suite. -/
theorem not_passes_example_inconsistent (c : Nat → Bool) :
    ¬ Passes c [(0, true), (0, false)] := by
  intro h
  have h1 := h (0, true) (by simp)
  have h2 := h (0, false) (by simp)
  simp at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Example for `tableChecker`: the table of a suite accepts its positive
entries and rejects everything else. -/
theorem tableChecker_examples :
    tableChecker [((0 : Nat), true), (1, false), (2, true)] 2 = true ∧
    tableChecker [((0 : Nat), true), (1, false), (2, true)] 1 = false ∧
    tableChecker [((0 : Nat), true), (1, false), (2, true)] 4 = false := by
  decide

/-- R2f (part). If some checker passes a finite suite, the lookup table of
the suite passes it and is pointwise below that checker (so the lookup table
is the least checker passing the suite). -/
theorem tableChecker_passes_and_le_of_passes {P : Type u} [DecidableEq P]
    {c : P → Bool} {T : TestSuite P} (hT : Passes c T) :
    Passes (tableChecker T) T ∧ CheckerLE (tableChecker T) c := by
  constructor
  · intro q hq
    obtain ⟨p, b⟩ := q
    cases b with
    | true => simpa [tableChecker] using hq
    | false =>
      have hcp : c p = false := hT (p, false) hq
      simp only [tableChecker]
      apply decide_eq_false
      intro hmem
      have := hT (p, true) hmem
      simp only at this
      rw [hcp] at this
      exact Bool.noConfusion this
  · intro p hp
    have hmem : (p, true) ∈ T := by simpa [tableChecker] using hp
    exact hT (p, true) hmem

/-- R2f. A lookup table passes every finite suite that some sound checker
passes: if a sound checker `c` passes `T`, then the lookup table of `T` is
sound, passes `T`, and is below `c`. Hence no law of the form "sound and
passes the finite suite `T`" can admit some checker while excluding the
lookup table of `T`. -/
theorem tableChecker_sound_passes_le_of_sound_passes {P : Type u} [DecidableEq P]
    {good : P → Prop} {c : P → Bool} {T : TestSuite P}
    (hc : Sound good c) (hT : Passes c T) :
    Sound good (tableChecker T) ∧ Passes (tableChecker T) T ∧ CheckerLE (tableChecker T) c := by
  obtain ⟨hpass, hle⟩ := tableChecker_passes_and_le_of_passes hT
  exact ⟨sound_of_checkerLE_of_sound hle hc, hpass, hle⟩

/-! ## Tightness counterexamples -/

/-- `allowlist_anchoredSound_of_anchors_good` without `hA`: with the bad anchor `1`, the allowlist of the anchors
is not admitted. -/
theorem cex_allowlist_anchoredSound_needs_anchors_good :
    ¬ AnchoredSound evenGood [1] (allowlist [1]) := by
  intro h
  have := h.1 1 (by decide)
  simp [evenGood] at this

/-- `forced_accept_iff_mem_anchors_of_anchors_good` without `hA`: with the
bad anchor `1` no checker is admitted, so the non-anchor `0` is vacuously
"forced", and the equivalence fails at `p = 0`. -/
theorem cex_forced_accept_needs_anchors_good :
    ¬ ((∀ c, AnchoredSound evenGood [1] c → c 0 = true) ↔ (0 : Nat) ∈ [1]) := by
  intro h
  have hforced : ∀ c, AnchoredSound evenGood [1] c → c 0 = true := by
    intro c hc
    have := hc.1 1 (hc.2 1 (by simp))
    simp [evenGood] at this
  exact absurd (h.mp hforced) (by decide)

/-- `forced_reject_iff_not_good_of_anchors_good` without `hA`: with the bad
anchor `1` the good program `0` is vacuously "forced to be rejected", and the
equivalence fails at `p = 0`. -/
theorem cex_forced_reject_needs_anchors_good :
    ¬ ((∀ c, AnchoredSound evenGood [1] c → c 0 = false) ↔ ¬ evenGood 0) := by
  intro h
  have hforced : ∀ c, AnchoredSound evenGood [1] c → c 0 = false := by
    intro c hc
    have := hc.1 1 (hc.2 1 (by simp))
    simp [evenGood] at this
  exact h.mp hforced rfl

/-- `anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good`
without `hA`: anchors `[1]`, `p = 0`; `hp` and `hpA` hold and the conclusion
fails (the allowlist of the anchors is not admitted). -/
theorem cex_admits_allowlists_needs_anchors_good :
    evenGood 0 ∧ (0 : Nat) ∉ [1] ∧
    ¬ (AnchoredSound evenGood [1] (allowlist [1]) ∧
       AnchoredSound evenGood [1] (allowlist (0 :: [1])) ∧
       allowlist [1] 0 = false ∧ allowlist (0 :: [1]) 0 = true) := by
  refine ⟨rfl, by decide, fun h => ?_⟩
  have := h.1.1 1 (by decide)
  simp [evenGood] at this

/-- Same theorem without `hp`: anchors `[0]`, `p = 1`; `hA` and `hpA` hold and
the conclusion fails (the allowlist of `p :: A` is unsound). -/
theorem cex_admits_allowlists_needs_good_p :
    (∀ a ∈ [0], evenGood a) ∧ (1 : Nat) ∉ [0] ∧
    ¬ (AnchoredSound evenGood [0] (allowlist [0]) ∧
       AnchoredSound evenGood [0] (allowlist (1 :: [0])) ∧
       allowlist [0] 1 = false ∧ allowlist (1 :: [0]) 1 = true) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h.2.1.1 1 (by decide)
  simp [evenGood] at this

/-- Same theorem without `hpA`: anchors `[0]`, `p = 0`; `hA` and `hp` hold and
the conclusion fails (the allowlist of `A` already accepts `p`). -/
theorem cex_admits_allowlists_needs_not_mem :
    (∀ a ∈ [0], evenGood a) ∧ evenGood 0 ∧
    ¬ (AnchoredSound evenGood [0] (allowlist [0]) ∧
       AnchoredSound evenGood [0] (allowlist (0 :: [0])) ∧
       allowlist [0] 0 = false ∧ allowlist (0 :: [0]) 0 = true) := by
  refine ⟨by decide, rfl, fun h => ?_⟩
  have h1 := h.2.2.1
  have h2 : allowlist [0] 0 = true := by decide
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- `tableChecker_passes_and_le_of_passes` without `hT`, in two instances:
for the consistent suite `[(0, true)]` and `c = rejectAll` the table is not
below `c`; for the inconsistent suite `[(0, true), (0, false)]` and
`c = acceptAll` the table does not pass the suite. In both the conclusion
fails. -/
theorem cex_tableChecker_passes_and_le_needs_passes :
    ¬ (Passes (tableChecker [((0 : Nat), true)]) [((0 : Nat), true)] ∧
       CheckerLE (tableChecker [((0 : Nat), true)]) rejectAll) ∧
    ¬ (Passes (tableChecker [((0 : Nat), true), (0, false)]) [((0 : Nat), true), (0, false)] ∧
       CheckerLE (tableChecker [((0 : Nat), true), (0, false)]) acceptAll) := by
  refine ⟨fun h => ?_, fun h => not_passes_example_inconsistent _ h.1⟩
  have := h.2 0 (by decide)
  simp [rejectAll] at this

/-- `tableChecker_sound_passes_le_of_sound_passes` without `hc`: `acceptAll`
passes `[(1, true)]` (so `hT` holds) and the conclusion fails (the lookup
table of that suite is not sound). -/
theorem cex_tableChecker_sound_needs_sound :
    Passes acceptAll [((1 : Nat), true)] ∧
    ¬ (Sound evenGood (tableChecker [((1 : Nat), true)]) ∧
       Passes (tableChecker [((1 : Nat), true)]) [((1 : Nat), true)] ∧
       CheckerLE (tableChecker [((1 : Nat), true)]) acceptAll) := by
  refine ⟨fun q hq => ?_, fun h => ?_⟩
  · simp at hq; subst hq; rfl
  · have := h.1 1 (by decide)
    simp [evenGood] at this

/-- `tableChecker_sound_passes_le_of_sound_passes` without `hT`: `rejectAll`
is sound (so `hc` holds) and the conclusion fails for the suite `[(1, true)]`
(its lookup table is not sound). -/
theorem cex_tableChecker_sound_needs_passes :
    Sound evenGood rejectAll ∧
    ¬ (Sound evenGood (tableChecker [((1 : Nat), true)]) ∧
       Passes (tableChecker [((1 : Nat), true)]) [((1 : Nat), true)] ∧
       CheckerLE (tableChecker [((1 : Nat), true)]) rejectAll) :=
  ⟨sound_rejectAll evenGood, fun h => cex_tableChecker_sound_needs_sound.2
    ⟨h.1, h.2.1, fun _ _ => rfl⟩⟩

/-- Positive control for R2f: the nearby law "sound, passes
`T = [(0, true), (1, false)]`, and complete on all programs" admits the
honest checker `evenExact` and excludes the lookup table of `T`, which is
sound and passes `T`. -/
theorem positive_control_completeOn_admits_evenExact_excludes_tableChecker :
    (Sound evenGood evenExact ∧ Passes evenExact [((0 : Nat), true), (1, false)] ∧
      CompleteOn evenGood (fun _ => True) evenExact) ∧
    (Sound evenGood (tableChecker [((0 : Nat), true), (1, false)]) ∧
      Passes (tableChecker [((0 : Nat), true), (1, false)]) [((0 : Nat), true), (1, false)] ∧
      ¬ CompleteOn evenGood (fun _ => True) (tableChecker [((0 : Nat), true), (1, false)])) := by
  refine ⟨⟨sound_example_evenExact, by decide, fun p hg _ => ?_⟩, ?_, by decide, ?_⟩
  · simpa [evenExact, evenGood] using hg
  · intro p hp
    have : (p, true) ∈ [((0 : Nat), true), (1, false)] := by simpa [tableChecker] using hp
    simp at this
    subst this
    rfl
  · intro h
    have := h 2 rfl trivial
    simp [tableChecker] at this

/-! ## A relational law: closure of acceptance under a transformation -/

/-- `ClosedUnderDoubling c`: whenever `c` accepts `p` it also accepts `2 * p`.
Captures a *relational* (metamorphic) law: acceptance must be preserved by a
fixed goodness-preserving program transformation (here doubling, which
preserves `evenGood`). It is a law on input–output behavior, but not a
pointwise one. -/
def ClosedUnderDoubling (c : Nat → Bool) : Prop :=
  ∀ p, c p = true → c (2 * p) = true

/-- A conservative, incomplete checker for `evenGood` closed under doubling:
accept the multiples of `4`, and `2`. -/
def fourOrTwo : Nat → Bool := fun n => n % 4 == 0 || n == 2

/-- Examples for `fourOrTwo`: it accepts `2`, `4`, `8` and rejects `6` and
`1`. -/
theorem fourOrTwo_examples :
    fourOrTwo 2 = true ∧ fourOrTwo 4 = true ∧ fourOrTwo 8 = true ∧
    fourOrTwo 6 = false ∧ fourOrTwo 1 = false := by
  decide

/-- Positive examples for `ClosedUnderDoubling`: `evenExact` and `fourOrTwo`. -/
theorem closedUnderDoubling_examples :
    ClosedUnderDoubling evenExact ∧ ClosedUnderDoubling fourOrTwo := by
  constructor
  · intro p hp
    simp only [evenExact, beq_iff_eq] at hp ⊢
    omega
  · intro p hp
    simp only [fourOrTwo, Bool.or_eq_true, beq_iff_eq] at hp ⊢
    left
    omega

/-- Negative examples for `ClosedUnderDoubling`: the allowlist `[2]` (accepts
`2`, rejects `4`) and `evenBelowTen` (accepts `8`, rejects `16`). -/
theorem not_closedUnderDoubling_examples :
    ¬ ClosedUnderDoubling (allowlist [2]) ∧ ¬ ClosedUnderDoubling evenBelowTen := by
  constructor
  · intro h
    have := h 2 (by decide)
    revert this
    decide
  · intro h
    have := h 8 (by decide)
    revert this
    decide

/-- A checker that accepts `2` and is closed under doubling accepts
arbitrarily large programs. -/
theorem exists_large_accepted_of_closedUnderDoubling {c : Nat → Bool} (h2 : c 2 = true)
    (hc : ClosedUnderDoubling c) : ∀ n, ∃ q, n + 2 ≤ q ∧ c q = true
  | 0 => ⟨2, Nat.le_refl _, h2⟩
  | n + 1 => by
    obtain ⟨q, hq, hcq⟩ := exists_large_accepted_of_closedUnderDoubling h2 hc n
    exact ⟨2 * q, by omega, hc q hcq⟩

/-- Second positive control for R2f (and a boundary for R2c and R6g): the
relational law "sound, passes `[(2, true)]`, and closed under doubling"
admits the conservative checker `fourOrTwo`, which is not complete on all
programs, and excludes the lookup table of every finite suite. -/
theorem positive_control_doubling_law_admits_fourOrTwo_excludes_every_tableChecker :
    (Sound evenGood fourOrTwo ∧ Passes fourOrTwo [((2 : Nat), true)] ∧
      ClosedUnderDoubling fourOrTwo ∧ ¬ CompleteOn evenGood (fun _ => True) fourOrTwo) ∧
    ∀ T : TestSuite Nat,
      ¬ (Passes (tableChecker T) [((2 : Nat), true)] ∧ ClosedUnderDoubling (tableChecker T)) := by
  refine ⟨⟨fun p hp => ?_, by decide, closedUnderDoubling_examples.2, fun h => ?_⟩, ?_⟩
  · simp only [fourOrTwo, Bool.or_eq_true, beq_iff_eq] at hp
    unfold evenGood
    omega
  · have := h 6 rfl trivial
    revert this
    decide
  · rintro T ⟨hpass, hcl⟩
    have h2 : tableChecker T 2 = true := hpass (2, true) (by simp)
    obtain ⟨q, hq, hacc⟩ :=
      exists_large_accepted_of_closedUnderDoubling h2 hcl ((T.map Prod.fst).sum)
    have hmem : (q, true) ∈ T := by simpa [tableChecker] using hacc
    have hmem' : q ∈ T.map Prod.fst := List.mem_map.mpr ⟨(q, true), hmem, rfl⟩
    have := le_sum_of_mem_nat hmem'
    omega

/-- The same relational law, stated with anchors: soundness, the anchor `2`,
and closure under doubling admit `fourOrTwo` and exclude every allowlist. -/
theorem doubling_law_admits_fourOrTwo_excludes_every_allowlist :
    (AnchoredSound evenGood [2] fourOrTwo ∧ ClosedUnderDoubling fourOrTwo) ∧
    ∀ A : List Nat, ¬ (AnchoredSound evenGood [2] (allowlist A) ∧ ClosedUnderDoubling (allowlist A)) := by
  obtain ⟨⟨hs, hp, hcl, _⟩, _⟩ :=
    positive_control_doubling_law_admits_fourOrTwo_excludes_every_tableChecker
  refine ⟨⟨⟨hs, fun a ha => ?_⟩, hcl⟩, ?_⟩
  · simp at ha; subst ha; exact hp (2, true) (by simp)
  · rintro A ⟨⟨_, hanc⟩, hcl'⟩
    obtain ⟨q, hq, hacc⟩ :=
      exists_large_accepted_of_closedUnderDoubling (hanc 2 (by simp)) hcl' A.sum
    have hmem : q ∈ A := by simpa [allowlist] using hacc
    have := le_sum_of_mem_nat hmem
    omega

/-! ## Non-vacuity witnesses -/

/-- `not_anchoredSound_rejectAll_iff_anchors_ne_nil` is non-degenerate: the anchored law with anchors `[0]` excludes
`rejectAll`, and with no anchors it admits it. -/
theorem nonvacuous_not_anchoredSound_rejectAll :
    ¬ AnchoredSound evenGood [0] rejectAll ∧ AnchoredSound evenGood [] rejectAll :=
  ⟨not_anchoredSound_example_rejectAll, sound_rejectAll evenGood, fun a ha => by simp at ha⟩

/-- The hypothesis `hA` of R2a and R2c holds: the anchors `[0, 2]` are good. -/
theorem nonvacuous_anchors_good : ∀ a ∈ [0, 2], evenGood a := by decide

/-- Hypotheses of the R2c witness family hold: anchors `[0]`, good non-anchor `2`. -/
theorem nonvacuous_admits_allowlists :
    (∀ a ∈ [0], evenGood a) ∧ evenGood 2 ∧ (2 : Nat) ∉ [0] :=
  ⟨by decide, rfl, by decide⟩

/-- R2f hypotheses hold: `evenExact` is sound and passes a two-sided
suite. -/
theorem nonvacuous_tableChecker :
    Sound evenGood evenExact ∧ Passes evenExact [(0, true), (1, false), (2, true)] :=
  ⟨sound_example_evenExact, passes_example_evenExact⟩

end Toy.Checker
