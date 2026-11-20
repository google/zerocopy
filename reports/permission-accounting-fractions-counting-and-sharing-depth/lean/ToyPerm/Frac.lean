import ToyPerm.PCM

/-!
# Fractional permissions

Fractional permissions (Boyland, SAS 2003) as a partial commutative monoid on
the rationals in `[0, 1]`: `0` is the empty permission (the unit), `1` is the
full (write) permission, and any positive amount grants read access. Two
fractions compose iff their sum is at most `1`, and the composite is the sum.
This is the fractional share model of Dockins, Hobor and Appel (APLAS 2009,
Definition 8); it differs from the model of Bornat et al. (POPL 2005, §10.3)
only by including `0` as an explicit unit.

Representation choice: values are Lean core `Rat`s, which are stored in
normalised form (coprime numerator and positive denominator), so Lean `=` on
`FracPerm` is equality of rational values and the cancellation and disjointness
laws below are stated with plain `=`. The fractions used in the splitting,
disjointness and holder-counting results are all dyadic (`k / 2^n`), so those
results also apply to the dyadic sub-algebra; the bounded-counting map of
`ToyPerm.Translate` uses multiples of `1/(3N+1)`.
-/

namespace Toy.Perm

/-- A fractional permission: a rational number in `[0, 1]`. `0` means no
permission, `1` means full (exclusive, write) permission, and any value in
`(0, 1)` means a shared read permission. -/
structure FracPerm where
  /-- The amount of permission held. -/
  val : Rat
  /-- Amounts are non-negative. -/
  nonneg : 0 ≤ val
  /-- No party holds more than the whole. -/
  le_one : val ≤ 1

namespace FracPerm

/-- Two fractional permissions are equal iff their amounts are equal. -/
@[ext] theorem ext {p q : FracPerm} (h : p.val = q.val) : p = q := by
  cases p; cases q; cases h; rfl

instance : DecidableEq FracPerm := fun p q =>
  if h : p.val = q.val then isTrue (ext h) else isFalse (fun e => h (e ▸ rfl))

/-- The empty permission `0`. -/
def zero : FracPerm := ⟨0, by grind, by grind⟩

/-- The full permission `1`. -/
def full : FracPerm := ⟨1, by grind, by grind⟩

/-- Half of a permission, `q / 2`. -/
def half (q : FracPerm) : FracPerm :=
  ⟨q.val / 2, by have := q.nonneg; grind, by have := q.nonneg; have := q.le_one; grind⟩

/-- The complement `1 - q`: what the other parties together hold when `q` is
held by one party and the whole has been accounted for. -/
def compl (q : FracPerm) : FracPerm :=
  ⟨1 - q.val, by have := q.le_one; grind, by have := q.nonneg; grind⟩

/-- `1 / 2^k`. -/
def halfPow : Nat → FracPerm
  | 0 => full
  | k + 1 => half (halfPow k)

/-- Clamp a rational into a fractional permission: `r` itself if `0 ≤ r ≤ 1`,
otherwise `0`. Used to define maps into fractions without proof obligations;
theorems about such maps state when clamping does not occur. -/
def ofRat (r : Rat) : FracPerm := if h : 0 ≤ r ∧ r ≤ 1 then ⟨r, h.1, h.2⟩ else zero

@[simp] theorem zero_val : zero.val = 0 := rfl
@[simp] theorem full_val : full.val = 1 := rfl
@[simp] theorem half_val (q : FracPerm) : (half q).val = q.val / 2 := rfl
@[simp] theorem compl_val (q : FracPerm) : (compl q).val = 1 - q.val := rfl

theorem ofRat_val_of {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) : (ofRat r).val = r := by
  simp [ofRat, h0, h1]

/-- Positive example: `1/2` is a fractional permission (and `ofRat` keeps it). -/
theorem ofRat_half_val : (ofRat (1 / 2)).val = 1 / 2 :=
  ofRat_val_of (by grind) (by grind)

/-- Negative examples: `3/2` and `-1/2` are not amounts of a fractional
permission (and `ofRat` clamps them to `0`). -/
theorem not_fracPerm_amounts :
    ¬ ((0 : Rat) ≤ 3 / 2 ∧ (3 / 2 : Rat) ≤ 1) ∧ ¬ ((0 : Rat) ≤ -1 / 2 ∧ (-1 / 2 : Rat) ≤ 1) ∧
      ofRat (3 / 2) = zero := by
  refine ⟨by grind, by grind, ?_⟩
  simp only [ofRat]; split
  · rename_i h; exact absurd h (by grind)
  · rfl

/-- Example values of `half`, `compl` and `halfPow`. -/
theorem half_compl_halfPow_examples :
    (half full).val = 1 / 2 ∧ (compl (half full)).val = 1 / 2 ∧ (halfPow 2).val = 1 / 4 ∧
      compl full = zero := by
  refine ⟨by simp <;> grind, by simp <;> grind, by simp [halfPow] <;> grind, ?_⟩
  ext; simp <;> grind

end FracPerm

open FracPerm

/-- Composition of fractional permissions: defined iff the amounts sum to at
most `1`, and then the composite holds the sum. -/
def fracOp (p q : FracPerm) : Option FracPerm :=
  if h : p.val + q.val ≤ 1 then
    some ⟨p.val + q.val, by have := p.nonneg; have := q.nonneg; grind, h⟩
  else none

/-- The fractional permission algebra on `[0, 1] ∩ ℚ`, with unit `0`. -/
def fracAlg : PartialAlg FracPerm where
  op := fracOp
  unit := zero

theorem fracOp_eq_some_iff {p q r : FracPerm} : fracOp p q = some r ↔ p.val + q.val = r.val := by
  unfold fracOp
  split
  · constructor
    · intro h; cases h; rfl
    · intro h; congr 1; ext; exact h
  · rename_i h
    constructor
    · intro h'; cases h'
    · intro h'; have := r.le_one; exact absurd (h' ▸ this) h

theorem fracOp_eq_none_iff {p q : FracPerm} : fracOp p q = none ↔ 1 < p.val + q.val := by
  unfold fracOp
  split
  · rename_i h; simp only [reduceCtorEq, false_iff]; grind
  · rename_i h; simp only [true_iff]; grind

theorem fracAlg_compat_iff {p q : FracPerm} : fracAlg.Compat p q ↔ p.val + q.val ≤ 1 := by
  simp only [PartialAlg.Compat, fracAlg, fracOp]
  split <;> simp_all

/-- Positive example: `1/2 · 1/2 = 1`. -/
theorem fracAlg_half_half : fracAlg.op (half full) (half full) = some full := by
  show fracOp _ _ = _
  rw [fracOp_eq_some_iff]; simp; grind

/-- Negative example: `1 · 1/2` is undefined. -/
theorem fracAlg_full_half : fracAlg.op full (half full) = none := by
  show fracOp _ _ = _
  rw [fracOp_eq_none_iff]; simp; grind

/-- The composite of a list of fractional permissions is defined iff the
amounts sum to at most `1`, and then it holds the sum. -/
theorem fracAlg_opList (ps : List FracPerm) :
    fracAlg.opList ps =
      if (ps.map FracPerm.val).sum ≤ 1 then some (ofRat (ps.map FracPerm.val).sum) else none := by
  have hnn : ∀ qs : List FracPerm, 0 ≤ (qs.map FracPerm.val).sum := by
    intro qs
    induction qs with
    | nil => simp
    | cons q qs ih => have := q.nonneg; simp; grind
  induction ps with
  | nil =>
    simp only [PartialAlg.opList, List.map_nil, List.sum_nil]
    have h01 : (0 : Rat) ≤ 1 := by grind
    simp only [h01, ↓reduceIte, Option.some.injEq]
    ext; rw [ofRat_val_of (by grind) (by grind)]; rfl
  | cons p ps ih =>
    simp only [PartialAlg.opList, ih, List.map_cons, List.sum_cons]
    have hp := p.nonneg
    have hs := hnn ps
    by_cases h1 : (ps.map FracPerm.val).sum ≤ 1
    · simp only [h1, ↓reduceIte, Option.bind_some]
      show fracOp _ _ = _
      by_cases h2 : p.val + (ps.map FracPerm.val).sum ≤ 1
      · simp only [h2, ↓reduceIte]
        rw [fracOp_eq_some_iff, ofRat_val_of hs h1, ofRat_val_of (by grind) h2]
      · simp only [h2, ↓reduceIte]
        rw [fracOp_eq_none_iff, ofRat_val_of hs h1]; grind
    · have h2 : ¬ (p.val + (ps.map FracPerm.val).sum ≤ 1) := by grind
      simp only [h1, h2, ↓reduceIte]; rfl

/-- In the fractional algebra the exclusive elements are exactly the full
permission `1`. -/
theorem fracAlg_exclusive_iff (p : FracPerm) : fracAlg.Exclusive p ↔ p = full := by
  constructor
  · intro h
    have hc : fracAlg.Compat p (compl p) := by rw [fracAlg_compat_iff]; simp <;> grind
    have := h _ hc
    ext
    have := congrArg FracPerm.val this
    simp [fracAlg] at this
    simp; grind
  · rintro rfl b hb
    rw [fracAlg_compat_iff] at hb
    have := b.nonneg
    ext; simp [fracAlg]; simp at hb; grind

/-! ## Laws -/

/-- **Fractional permissions form a cancellative, positive partial commutative
monoid.** The fractional algebra on `[0, 1] ∩ ℚ` (unit `0`, composite = sum when
the sum is at most `1`) is commutative, associative, has `0` as unit, is
cancellative, and is positive. -/
theorem fracAlg_isPCM_cancel_positive :
    fracAlg.IsPCM ∧ fracAlg.Cancel ∧ fracAlg.Positive := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b
    show fracOp a b = fracOp b a
    unfold fracOp
    by_cases h : a.val + b.val ≤ 1
    · have h' : b.val + a.val ≤ 1 := by grind
      simp only [h, h', ↓reduceDIte, Option.some.injEq]
      ext; grind
    · have h' : ¬ b.val + a.val ≤ 1 := by grind
      simp only [h, h', ↓reduceDIte]
  · intro a b c
    show (fracOp a b).bind (fun ab => fracOp ab c) = (fracOp b c).bind (fun bc => fracOp a bc)
    have ha := a.nonneg; have hb := b.nonneg; have hc := c.nonneg
    unfold fracOp
    by_cases hab : a.val + b.val ≤ 1 <;> by_cases hbc : b.val + c.val ≤ 1 <;>
      by_cases habc : a.val + b.val + c.val ≤ 1
    · have habc' : a.val + (b.val + c.val) ≤ 1 := by grind
      simp only [hab, hbc, habc, habc', ↓reduceDIte, Option.bind_some, Option.some.injEq]
      ext; grind
    · have habc' : ¬ a.val + (b.val + c.val) ≤ 1 := by grind
      simp only [hab, hbc, habc, habc', ↓reduceDIte, Option.bind_some]
    · grind
    · simp only [hab, hbc, habc, ↓reduceDIte, Option.bind_some, Option.bind_none]
    · grind
    · have habc' : ¬ a.val + (b.val + c.val) ≤ 1 := by grind
      simp only [hab, hbc, habc', ↓reduceDIte, Option.bind_some, Option.bind_none]
    · grind
    · simp only [hab, hbc, ↓reduceDIte, Option.bind_none]
  · intro a
    show fracOp zero a = some a
    rw [fracOp_eq_some_iff]; simp; grind
  · intro a b c d hab hac
    change fracOp a b = some d at hab
    change fracOp a c = some d at hac
    rw [fracOp_eq_some_iff] at hab hac
    ext; grind
  · intro a b h
    change fracOp a b = some zero at h
    rw [fracOp_eq_some_iff] at h
    have := a.nonneg; have := b.nonneg
    ext; simp [fracAlg] at h ⊢; grind

/-! ## Splitting and recombination -/

/-- The halving split of `q` into `n` pieces:
`[q/2, q/4, …, q/2^(n-1), q/2^(n-1)]` (and `[q]` for `n = 1`, `[]` for `n = 0`). -/
def halvingSplit (q : FracPerm) : Nat → List FracPerm
  | 0 => []
  | 1 => [q]
  | n + 2 => half q :: halvingSplit (half q) (n + 1)

/-- Example: the halving split of `1` into three pieces is `[1/2, 1/4, 1/4]`. -/
theorem halvingSplit_full_three :
    (halvingSplit full 3).map FracPerm.val = [1 / 2, 1 / 4, 1 / 4] := by
  simp [halvingSplit]; grind

/-- Halving a permission splits it into two equal halves that recompose to it. -/
theorem fracAlg_op_half_half (q : FracPerm) : fracAlg.op (half q) (half q) = some q := by
  show fracOp _ _ = _
  rw [fracOp_eq_some_iff]; simp; grind

/-- **Fractions are infinitely splittable without any bookkeeping (no atoms).**
Every non-empty fractional permission `q` is the composite of two non-empty
permissions, namely `half q · half q = q` with `half q ≠ 0`. -/
theorem fracAlg_nonzero_splits_into_two_nonzero_halves (q : FracPerm) (hq : q ≠ zero) :
    fracAlg.op (half q) (half q) = some q ∧ half q ≠ zero := by
  refine ⟨fracAlg_op_half_half q, ?_⟩
  intro h
  apply hq
  have := congrArg FracPerm.val h
  ext; simp at this ⊢; grind

/-- Non-vacuity of `fracAlg_nonzero_splits_into_two_nonzero_halves`: the full
permission is non-empty. -/
theorem fracAlg_nonzero_splits_nonvacuous : full ≠ zero := by
  intro h; have := congrArg FracPerm.val h; simp at this

/-- Halving the empty permission gives the empty permission. -/
theorem fracAlg_zero_half_is_zero : half zero = zero := by
  ext; simp <;> grind

/-- Tightness of `hq` in `fracAlg_nonzero_splits_into_two_nonzero_halves`
(canonical form; the theorem has no other hypothesis): for `q = 0` the
conclusion fails, because the halves are `0`. -/
theorem fracAlg_nonzero_splits_needs_hq :
    ¬ (zero ≠ zero) ∧ ¬ (fracAlg.op (half zero) (half zero) = some zero ∧ half zero ≠ zero) :=
  ⟨fun h => h rfl, fun h => h.2 fracAlg_zero_half_is_zero⟩

/-- **Fractions split into any number of read permissions that recombine
exactly.** For every fractional permission `q` and every `n ≥ 1`, the halving
split `halvingSplit q n` (`[q]` for `n = 1`, `[q/2, q/4, …, q/2^(n-1), q/2^(n-1)]`
for `n ≥ 2`) has exactly `n` pieces, its pieces compose (in list order) to
exactly `q`, and if `q ≠ 0` every piece is non-empty (grants read access). -/
theorem fracAlg_halvingSplit_composes (q : FracPerm) (n : Nat) (hn : 0 < n) :
    (halvingSplit q n).length = n ∧ fracAlg.opList (halvingSplit q n) = some q ∧
      (q ≠ zero → ∀ x ∈ halvingSplit q n, x ≠ zero) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction n generalizing q with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · simp only [halvingSplit, PartialAlg.opList, Option.bind_some]
      show fracOp _ _ = _
      rw [fracOp_eq_some_iff]; simp [fracAlg] <;> grind
    · intro hq x hx; simp [halvingSplit] at hx; subst hx; exact hq
  | succ n ih =>
    obtain ⟨hl, hc, hz⟩ := ih (half q)
    refine ⟨by simp [halvingSplit, hl], ?_, ?_⟩
    · show (fracAlg.opList (halvingSplit (half q) (n + 1))).bind (fracAlg.op (half q)) = _
      rw [hc]; exact fracAlg_op_half_half q
    · intro hq x hx
      have hh := (fracAlg_nonzero_splits_into_two_nonzero_halves q hq).2
      simp only [halvingSplit, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hh
      · exact hz hh x hx

/-- Tightness of `hn` in `fracAlg_halvingSplit_composes` and in
`fracAlg_halvingSplit_full_recombines_to_exclusive` (canonical form; neither
theorem has another hypothesis): for `q = 1` and `n = 0` both conclusions fail,
because the split into `0` pieces is empty and composes to `0`, not to `1`. -/
theorem fracAlg_halvingSplit_zero_pieces :
    ¬ (0 < 0) ∧
      ¬ ((halvingSplit full 0).length = 0 ∧ fracAlg.opList (halvingSplit full 0) = some full ∧
        (full ≠ zero → ∀ x ∈ halvingSplit full 0, x ≠ zero)) ∧
      ¬ (fracAlg.opList (halvingSplit full 0) = some full ∧ fracAlg.Exclusive full) := by
  have h : fracAlg.opList (halvingSplit full 0) ≠ some full := by
    intro h
    have := congrArg (Option.map FracPerm.val) h
    simp [halvingSplit, PartialAlg.opList, fracAlg] at this
  exact ⟨by decide, fun h' => h h'.2.1, fun h' => h h'.1⟩

/-- Tightness of the inner hypothesis `q ≠ 0` of the third conjunct of
`fracAlg_halvingSplit_composes` (canonical form): with `q = 0` and `n = 2` the
other hypothesis `0 < n` holds, but the conclusion with the inner hypothesis
dropped fails, because the pieces of a split of `0` are empty. -/
theorem fracAlg_halvingSplit_of_zero_has_empty_piece :
    0 < 2 ∧ ¬ ((halvingSplit zero 2).length = 2 ∧ fracAlg.opList (halvingSplit zero 2) = some zero ∧
      ∀ x ∈ halvingSplit zero 2, x ≠ zero) := by
  refine ⟨by decide, fun h => h.2.2 zero ?_ rfl⟩
  simp [halvingSplit, fracAlg_zero_half_is_zero]

/-- **Recombination to exclusive.** The `n` pieces of the halving split of the
full permission recompose to the full permission, which is exclusive. -/
theorem fracAlg_halvingSplit_full_recombines_to_exclusive (n : Nat) (hn : 0 < n) :
    fracAlg.opList (halvingSplit full n) = some full ∧ fracAlg.Exclusive full :=
  ⟨(fracAlg_halvingSplit_composes full n hn).2.1, (fracAlg_exclusive_iff full).2 rfl⟩

/-- Non-vacuity of `fracAlg_halvingSplit_composes`: its hypotheses hold for
`q = 1`, `n = 3`, and the split is `[1/2, 1/4, 1/4]`, all non-empty. -/
theorem fracAlg_halvingSplit_composes_nonvacuous :
    0 < 3 ∧ full ≠ zero ∧ (halvingSplit full 3).map FracPerm.val = [1 / 2, 1 / 4, 1 / 4] := by
  refine ⟨by decide, ?_, halvingSplit_full_three⟩
  intro h; have := congrArg FracPerm.val h; simp at this

end Toy.Perm
