import ToyPerm.Frac
import ToyPerm.Count

/-!
# Who knows how many readers are still out?

A *complete configuration* is a list of permissions held by distinct parties
that pools to the full (fractional `1`) or total (counting `some 0`)
permission. We compare what the holder of one piece can conclude, from that
piece alone, about the other non-empty pieces.

* Counting: in any consistent configuration (composite defined), a source with
  count `n` bounds the number of other non-empty pieces by `n`; in a complete
  configuration with `n > 0` at least one other piece is out; and if all other
  pieces are single tokens, completeness holds exactly when there are `n` of
  them. In particular, in a complete configuration a source with count `1` has
  exactly one other non-empty piece out.
* Fractions: for every non-full piece `p`, the remaining `1 - p` can be held as
  any number `n ≥ 1` of non-empty pieces. No non-exclusive fractional piece
  bounds the number of other holders.
* Either way, a returning reader's own piece does not tell it whether it is the
  last one out.

What fractions do *not* lose: the holder of `1` is exclusive, and whether a
given return completes the whole is decided by the two amounts alone
(`fracOp_eq_some_iff`).
-/

namespace Toy.Perm

open FracPerm Count PartialAlg

/-! ## Counting: the source knows -/

/-- **A counting source bounds the number of outstanding holders by its count.**
If `source n` together with a list `ts` of non-empty counting permissions has a
defined composite (the configuration is consistent; it need not account for the
whole permission), then `ts` has at most `n` elements. -/
theorem countAlg_source_count_bounds_outstanding_pieces (n : Nat) (ts : List Count)
    (hts : ∀ t ∈ ts, t ≠ none) (hdef : countAlg.opList (source n :: ts) ≠ none) :
    ts.length ≤ n := by
  simp only [PartialAlg.opList] at hdef
  cases hr : countAlg.opList ts with
  | none => simp [hr] at hdef
  | some r =>
    simp only [hr, Option.bind_some] at hdef
    rcases r with _ | w
    · have := countAlg_opList_eq_unit ts hts hr; subst this; simp
    · change countOp (some (n : Int)) (some w) ≠ none at hdef
      rw [countOp_some_some] at hdef
      split at hdef
      · rename_i hcond
        have := countAlg_opList_tokens_length_le ts hts w hr (by omega)
        omega
      · exact absurd rfl hdef

/-- Tightness of `hts` in `countAlg_source_count_bounds_outstanding_pieces`
(canonical form): empty pieces can pad a configuration (`source 0` with one
`none`); the composite is defined, yet the bound `1 ≤ 0` fails. -/
theorem countAlg_source_bound_needs_nonempty_pieces :
    countAlg.opList (source 0 :: [none]) ≠ none ∧ countAlg.opList (source 0 :: [none]) = some total ∧
      ¬ ([none] : List Count).length ≤ 0 := by
  decide

/-- Tightness of `hdef` in `countAlg_source_count_bounds_outstanding_pieces`
(canonical form): `source 0` with one read token has non-empty pieces, its
composite is undefined, and the bound `1 ≤ 0` fails. -/
theorem countAlg_source_bound_needs_defined :
    (∀ t ∈ [readToken], t ≠ none) ∧ countAlg.opList (source 0 :: [readToken]) = none ∧
      ¬ [readToken].length ≤ 0 := by
  decide

/-- Non-vacuity of `countAlg_source_count_bounds_outstanding_pieces`: `source 2`
with two read tokens is consistent (indeed complete), and `source 2` with one
read token is consistent but incomplete (it pools to `source 1`); the bound
covers both. -/
theorem countAlg_source_count_bounds_outstanding_pieces_nonvacuous :
    (∀ t ∈ [readToken, readToken], t ≠ none) ∧
      countAlg.opList (source 2 :: [readToken, readToken]) ≠ none ∧
      countAlg.opList (source 2 :: [readToken, readToken]) = some total ∧
      countAlg.opList (source 2 :: [readToken]) = some (source 1) := by
  decide

/-- **In a complete configuration, a source with a positive count is not alone.**
If `source n` with `n > 0` together with `ts` pools to the total permission,
then `ts` has at least one element. -/
theorem countAlg_complete_source_pos_has_outstanding_piece (n : Nat) (ts : List Count)
    (hc : countAlg.opList (source n :: ts) = some total) (hn : 0 < n) : 1 ≤ ts.length := by
  cases ts with
  | nil =>
    change some (source n) = some total at hc
    simp [source, total] at hc; omega
  | cons t ts => simp

/-- Tightness of `hc` in `countAlg_complete_source_pos_has_outstanding_piece`
(canonical form): `source 1` alone is a consistent but incomplete configuration
(it pools to `source 1`, not to `total`); `0 < 1` holds and the conclusion
`1 ≤ 0` fails. -/
theorem countAlg_complete_lower_bound_needs_complete :
    countAlg.opList (source 1 :: []) = some (source 1) ∧
      countAlg.opList (source 1 :: []) ≠ some total ∧ 0 < 1 ∧ ¬ 1 ≤ ([] : List Count).length := by
  decide

/-- Tightness of `hn` in `countAlg_complete_source_pos_has_outstanding_piece`
(canonical form): the total permission `source 0` alone is complete and the
conclusion `1 ≤ 0` fails. -/
theorem countAlg_complete_lower_bound_needs_pos :
    countAlg.opList (source 0 :: []) = some total ∧ ¬ 1 ≤ ([] : List Count).length := by
  decide

/-- **With count 1, a complete configuration has exactly one other non-empty
piece.** Corollary of `countAlg_source_count_bounds_outstanding_pieces` and
`countAlg_complete_source_pos_has_outstanding_piece`. -/
theorem countAlg_source_one_complete_exactly_one_piece (ts : List Count)
    (hts : ∀ t ∈ ts, t ≠ none) (hc : countAlg.opList (source 1 :: ts) = some total) :
    ts.length = 1 := by
  have h1 := countAlg_source_count_bounds_outstanding_pieces 1 ts hts (by rw [hc]; simp)
  have h2 := countAlg_complete_source_pos_has_outstanding_piece 1 ts hc (by decide)
  omega

/-- Tightness of `hts` in `countAlg_source_one_complete_exactly_one_piece`
(canonical form): `[readToken, none]` completes `source 1` but has two
elements. -/
theorem countAlg_source_one_exactly_one_needs_nonempty :
    countAlg.opList (source 1 :: [readToken, none]) = some total ∧
      ¬ ([readToken, none] : List Count).length = 1 := by
  decide

/-- Tightness of `hc` in `countAlg_source_one_complete_exactly_one_piece`
(canonical form): with `ts = []`, `hts` holds vacuously, the configuration is
not complete, and the conclusion `0 = 1` fails. -/
theorem countAlg_source_one_exactly_one_needs_complete :
    (∀ t ∈ ([] : List Count), t ≠ none) ∧ countAlg.opList (source 1 :: []) ≠ some total ∧
      ¬ ([] : List Count).length = 1 := by
  decide

/-- Non-vacuity of `countAlg_complete_source_pos_has_outstanding_piece` and
`countAlg_source_one_complete_exactly_one_piece`: `source 1` with one read
token is complete, `0 < 1`, and the read token is non-empty. -/
theorem countAlg_source_one_complete_nonvacuous :
    (∀ t ∈ [readToken], t ≠ none) ∧ countAlg.opList (source 1 :: [readToken]) = some total ∧
      0 < 1 := by
  decide

/-- **With single read tokens, completeness is exactly "count equals number of
tokens".** If every element of `ts` is a single read token, then `source n`
together with `ts` pools to the total permission iff `ts` has exactly `n`
elements. -/
theorem countAlg_readTokens_complete_iff_length_eq_count (n : Nat) (ts : List Count)
    (hatom : ∀ t ∈ ts, t = readToken) :
    countAlg.opList (source n :: ts) = some total ↔ ts.length = n := by
  have hts : ts = List.replicate ts.length readToken := List.eq_replicate_iff.mpr ⟨rfl, hatom⟩
  constructor
  · intro h
    rw [hts] at h
    simp only [PartialAlg.opList, countAlg_opList_replicate_readToken, Option.bind_some] at h
    by_cases hm : ts.length = 0
    · rw [hm] at h
      change some (source n) = some total at h
      simp [source, total] at h; omega
    · rw [tokens_of_pos (by omega)] at h
      change countOp (some (n : Int)) (some (-(ts.length : Int))) = some (some 0) at h
      rw [countOp_some_some_eq_some] at h
      obtain ⟨_, h3⟩ := h
      simp at h3; omega
  · intro h
    rw [hts, h]
    exact countAlg_total_splits_into_source_and_readTokens n

/-- Tightness of `hatom` in `countAlg_readTokens_complete_iff_length_eq_count`
(canonical form): with one bundle of two tokens, `source 2` is completed by a
single piece, so the equivalence fails. The count tracks tokens, not holders. -/
theorem countAlg_bundle_complete_length_ne_count :
    countAlg.opList (source 2 :: [tokens 2]) = some total ∧ ([tokens 2] : List Count).length ≠ 2 ∧
      ¬ (countAlg.opList (source 2 :: [tokens 2]) = some total ↔ ([tokens 2] : List Count).length = 2) := by
  decide

/-- Non-vacuity of `countAlg_readTokens_complete_iff_length_eq_count`: two single
tokens complete `source 2`. -/
theorem countAlg_readTokens_complete_iff_nonvacuous :
    (∀ t ∈ [readToken, readToken], t = readToken) ∧
      countAlg.opList (source 2 :: [readToken, readToken]) = some total := by
  decide

/-! ## Fractions: no piece knows -/

theorem compl_ne_zero_of_ne_full {p : FracPerm} (hp : p ≠ full) : compl p ≠ zero := by
  intro h
  apply hp
  have := congrArg FracPerm.val h
  ext; simp at this ⊢; grind

/-- **A non-full fractional piece is compatible with any number of other
holders.** For every fractional permission `p ≠ 1` and every `n ≥ 1`, the
halving split of the complement `1 - p` into `n` pieces consists of exactly `n`
non-empty pieces, and `p` together with them pools to the full permission. -/
theorem fracAlg_owner_complement_splits_into_any_number (p : FracPerm) (hp : p ≠ full) (n : Nat)
    (hn : 0 < n) :
    (halvingSplit (compl p) n).length = n ∧ (∀ x ∈ halvingSplit (compl p) n, x ≠ zero) ∧
      fracAlg.opList (p :: halvingSplit (compl p) n) = some full := by
  obtain ⟨hl, hc, hz⟩ := fracAlg_halvingSplit_composes (compl p) n hn
  refine ⟨hl, hz (compl_ne_zero_of_ne_full hp), ?_⟩
  simp only [PartialAlg.opList, hc, Option.bind_some]
  show fracOp p (compl p) = some full
  rw [fracOp_eq_some_iff]; simp; grind

/-- Tightness of `hp` in `fracAlg_owner_complement_splits_into_any_number`
(canonical form): for `p = 1` and `n = 1`, `0 < 1` holds, but the complement is
`0` and its single piece is empty, so the conclusion fails. -/
theorem fracAlg_full_complement_piece_is_zero :
    ¬ (full ≠ full) ∧ 0 < 1 ∧ ¬ ((halvingSplit (compl full) 1).length = 1 ∧
      (∀ x ∈ halvingSplit (compl full) 1, x ≠ zero) ∧
      fracAlg.opList (full :: halvingSplit (compl full) 1) = some full) := by
  refine ⟨fun h => h rfl, by decide, fun h => h.2.1 (compl full) (by simp [halvingSplit]) ?_⟩
  ext; simp <;> grind

/-- Tightness of `hn` in `fracAlg_owner_complement_splits_into_any_number`
(canonical form): with `p = 1/2` (so `p ≠ 1`) and `n = 0` there are no other
pieces and `1/2` alone is not the whole, so the conclusion fails. -/
theorem fracAlg_owner_complement_zero_pieces :
    half full ≠ full ∧ ¬ (0 < 0) ∧ ¬ ((halvingSplit (compl (half full)) 0).length = 0 ∧
      (∀ x ∈ halvingSplit (compl (half full)) 0, x ≠ zero) ∧
      fracAlg.opList (half full :: halvingSplit (compl (half full)) 0) = some full) := by
  refine ⟨?_, by decide, ?_⟩
  · intro h; have := congrArg FracPerm.val h; simp at this; grind
  · intro ⟨_, _, h⟩
    simp only [halvingSplit, PartialAlg.opList, Option.bind_some] at h
    change fracOp (half full) zero = some full at h
    rw [fracOp_eq_some_iff] at h; simp at h; grind

/-- Non-vacuity of `fracAlg_owner_complement_splits_into_any_number`: its
hypotheses hold for `p = 1/2` and `n = 3`, and the other pieces are
`[1/4, 1/8, 1/8]`. -/
theorem fracAlg_owner_complement_splits_nonvacuous :
    half full ≠ full ∧ 0 < 3 ∧
      (halvingSplit (compl (half full)) 3).map FracPerm.val = [1 / 4, 1 / 8, 1 / 8] := by
  refine ⟨fracAlg_owner_complement_zero_pieces.1, by decide, ?_⟩
  simp [halvingSplit]; grind

/-- **No non-exclusive fractional piece bounds the number of other holders.**
There is no fractional permission `p` that is not exclusive and a number `N`
such that every list of non-empty pieces completing `p` to the full permission
has at most `N` elements. -/
theorem fracAlg_no_nonexclusive_element_bounds_outstanding_pieces :
    ¬ ∃ p : FracPerm, ¬ fracAlg.Exclusive p ∧ ∃ N : Nat, ∀ ps : List FracPerm,
      (∀ x ∈ ps, x ≠ zero) → fracAlg.opList (p :: ps) = some full → ps.length ≤ N := by
  rintro ⟨p, hp, N, hN⟩
  have hp' : p ≠ full := fun h => hp ((fracAlg_exclusive_iff p).2 h)
  obtain ⟨hl, hz, hc⟩ := fracAlg_owner_complement_splits_into_any_number p hp' (N + 1) (by omega)
  have := hN _ hz hc
  omega

/-- Non-vacuity of the hypothesis of
`fracAlg_no_nonexclusive_element_bounds_outstanding_pieces`: the fraction `1/2`
is not exclusive. -/
theorem fracAlg_half_not_exclusive : ¬ fracAlg.Exclusive (half full) := by
  rw [fracAlg_exclusive_iff]; exact fracAlg_owner_complement_zero_pieces.1

/-- Positive control for `fracAlg_no_nonexclusive_element_bounds_outstanding_pieces`:
in the counting algebra the non-exclusive element `source 1` bounds the number
of other non-empty holders in any complete configuration by `1`. -/
theorem countAlg_source_one_bounds_outstanding_pieces :
    ∃ p : Count, ¬ countAlg.Exclusive p ∧ ∃ N : Nat, ∀ ts : List Count,
      (∀ t ∈ ts, t ≠ none) → countAlg.opList (p :: ts) = some total → ts.length ≤ N :=
  ⟨source 1, by rw [countAlg_exclusive_iff]; decide, 1,
    fun ts hts hc => countAlg_source_count_bounds_outstanding_pieces 1 ts hts (by rw [hc]; simp)⟩

/-- Tightness of `¬ Exclusive p` in
`fracAlg_no_nonexclusive_element_bounds_outstanding_pieces` (canonical form):
the exclusive piece `1` does bound the other non-empty holders, by `0`. -/
theorem fracAlg_full_bounds_outstanding_pieces :
    fracAlg.Exclusive full ∧ ∀ ps : List FracPerm, (∀ x ∈ ps, x ≠ zero) →
      fracAlg.opList (full :: ps) = some full → ps.length ≤ 0 := by
  refine ⟨(fracAlg_exclusive_iff full).2 rfl, ?_⟩
  intro ps hps hc
  cases ps with
  | nil => simp
  | cons x xs =>
    exfalso
    rw [fracAlg_opList] at hc
    split at hc
    · rename_i hle
      have hx := x.nonneg
      have hx0 : x.val ≠ 0 := fun h => hps x (by simp) (FracPerm.ext h)
      have hs : 0 ≤ (xs.map FracPerm.val).sum := by
        clear hc hle hps
        induction xs with
        | nil => simp
        | cons y ys ih => have := y.nonneg; simp; grind
      simp at hle; grind
    · simp at hc

/-! ## Readers do not know either -/

/-- **A reader's own piece does not tell it whether it is the last one out, in
either design.** For every token bundle `tokens k`: it completes `source k`
alone, it does not complete `source (k+1)` alone, and with one more read token
it does. For every fraction `q ≠ 1`: it completes `1 - q` alone, it does not
complete `(1 - q)/2` alone, and with a second piece `(1 - q)/2` it does. So the
same reader piece is the last return in one complete configuration and not the
last in another. -/
theorem reader_piece_does_not_determine_lastness :
    (∀ k : Nat,
      countAlg.opList [source k, tokens k] = some total ∧
        countAlg.opList [source (k + 1), tokens k] ≠ some total ∧
        countAlg.opList [source (k + 1), tokens k, readToken] = some total) ∧
    (∀ q : FracPerm, q ≠ full →
      fracAlg.opList [compl q, q] = some full ∧
        fracAlg.opList [half (compl q), q] ≠ some full ∧
        fracAlg.opList [half (compl q), q, half (compl q)] = some full) := by
  refine ⟨fun k => ?_, fun q hq => ?_⟩
  · cases k with
    | zero => decide
    | succ j =>
      refine ⟨?_, ?_, ?_⟩
      · show countOp (some ((j + 1 : Nat) : Int)) (some (-((j + 1 : Nat) : Int))) = some (some 0)
        rw [countOp_some_some_of (by omega)]; congr 2; omega
      · show countOp (some ((j + 1 + 1 : Nat) : Int)) (some (-((j + 1 : Nat) : Int))) ≠
          some (some 0)
        rw [countOp_some_some_of (by omega)]; simp; omega
      · show (countOp (some (-((j + 1 : Nat) : Int))) (some (-1))).bind
            (countOp (some ((j + 1 + 1 : Nat) : Int))) = some (some 0)
        rw [countOp_some_some_of (by omega), Option.bind_some, countOp_some_some_of (by omega)]
        congr 2; omega
  · have h0 := q.nonneg
    have h1 := q.le_one
    have hq1 : q.val ≠ 1 := fun h => hq (FracPerm.ext h)
    refine ⟨?_, ?_, ?_⟩
    · rw [fracAlg_opList]; simp
      constructor
      · grind
      · ext; rw [ofRat_val_of (by grind) (by grind)]; simp; grind
    · rw [fracAlg_opList]
      split
      · intro h
        simp only [Option.some.injEq] at h
        have := congrArg FracPerm.val h
        rw [ofRat_val_of (by simp; grind) (by assumption)] at this
        simp at this; grind
      · simp
    · rw [fracAlg_opList]; simp
      constructor
      · grind
      · ext; rw [ofRat_val_of (by grind) (by grind)]; simp; grind

/-- Tightness of `q ≠ 1` in `reader_piece_does_not_determine_lastness`
(canonical form): for `q = 1` the fraction conjunct fails, because `[0, 1]`
already composes to the full permission. -/
theorem reader_lastness_needs_ne_full :
    ¬ (fracAlg.opList [compl full, full] = some full ∧
        fracAlg.opList [half (compl full), full] ≠ some full ∧
        fracAlg.opList [half (compl full), full, half (compl full)] = some full) := by
  intro ⟨_, h, _⟩
  apply h
  rw [fracAlg_opList]; simp
  constructor
  · grind
  · ext; rw [ofRat_val_of (by grind) (by grind)]; simp; grind

/-- Non-vacuity of `reader_piece_does_not_determine_lastness`: the hypothesis
`q ≠ 1` holds for `q = 1/4`, and for `k = 1` and `q = 1/4` the configurations
are `[source 1, readToken]` (complete), `[source 2, readToken]` (incomplete),
`[3/4, 1/4]` (complete) and `[3/8, 1/4]` (incomplete). -/
theorem reader_lastness_nonvacuous :
    halfPow 2 ≠ full ∧ countAlg.opList [source 1, tokens 1] = some total ∧
      countAlg.opList [source 2, tokens 1] = some (source 1) := by
  refine ⟨?_, by decide, by decide⟩
  intro h; have := congrArg FracPerm.val h; simp [halfPow] at this; grind

end Toy.Perm
