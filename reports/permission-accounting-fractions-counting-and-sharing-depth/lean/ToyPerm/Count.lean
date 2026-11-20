import ToyPerm.PCM

/-!
# Counting permissions

Counting permissions (Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005, §6, §8
and §10.2) as a partial commutative monoid on `Option Int`, exactly in the form
of the counting share model of Dockins, Hobor and Appel (APLAS 2009,
Definition 9):

* `none` is the empty permission (the unit);
* `some n` with `n ≥ 0` is a *source* permission from which `n` read tokens have
  been split off; `some 0` is the total (write) permission;
* `some (-k)` with `k ≥ 1` is a bundle of `k` read tokens.

Two non-unit permissions compose iff at least one is a token bundle and either
both are bundles or the sum is non-negative (a source never absorbs more tokens
than it issued); the composite is the integer sum. Two sources never compose.
-/

namespace Toy.Perm

/-- A counting permission: `none` (no permission), a source `some n` (`n ≥ 0`,
with `n` outstanding read tokens; `some 0` is total permission), or a bundle of
`k ≥ 1` read tokens `some (-k)`. This is meant to capture permission counting
as used for readers–writers locks: a central authority hands out identical read
tokens and counts how many are outstanding. -/
abbrev Count := Option Int

namespace Count

/-- The total (write) permission: a source with no outstanding tokens. -/
def total : Count := some 0

/-- A source permission that has issued `n` read tokens (`source 0 = total`). -/
def source (n : Nat) : Count := some (n : Int)

/-- A single read token. -/
def readToken : Count := some (-1)

/-- A bundle of `k` read tokens; `tokens 0` is the empty permission `none` (an
empty bundle), and `tokens k = some (-k)` for `k ≥ 1`. -/
def tokens : Nat → Count
  | 0 => none
  | k + 1 => some (-((k + 1 : Nat) : Int))

@[simp] theorem tokens_zero : tokens 0 = none := rfl

theorem tokens_of_pos {k : Nat} (hk : 0 < k) : tokens k = some (-(k : Int)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- Examples of `tokens`: the empty bundle is the empty permission (not the
total permission `some 0`), and `tokens 2 = some (-2)`; a bundle of `k ≥ 1`
tokens is never the total permission. -/
theorem tokens_examples :
    tokens 0 = none ∧ tokens 2 = some (-2) ∧ tokens 0 ≠ total ∧ ∀ k, tokens k ≠ total := by
  refine ⟨rfl, rfl, by simp [total], fun k => ?_⟩
  cases k with
  | zero => simp [total]
  | succ k => simp [tokens, total]; omega

end Count

open Count

/-- Composition of counting permissions (Dockins–Hobor–Appel Definition 9;
Bornat et al. §10.2 with an explicit unit). -/
def countOp : Count → Count → Option Count
  | none, b => some b
  | a, none => some a
  | some i, some j =>
    if (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0)) then some (some (i + j)) else none

/-- The counting permission algebra, with unit `none`. -/
def countAlg : PartialAlg Count where
  op := countOp
  unit := none

theorem countOp_some_some (i j : Int) :
    countOp (some i) (some j) =
      if (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0)) then some (some (i + j)) else none := rfl

theorem countOp_some_some_of {i j : Int} (h : (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))) :
    countOp (some i) (some j) = some (some (i + j)) := by
  rw [countOp_some_some]; simp only [h, and_self, ↓reduceIte]

theorem countOp_some_some_eq_some {i j : Int} {c : Count} :
    countOp (some i) (some j) = some c ↔
      ((i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))) ∧ c = some (i + j) := by
  rw [countOp_some_some]
  by_cases h : (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))
  · simp only [h, ↓reduceIte, Option.some.injEq, true_and]; exact eq_comm
  · simp only [h, ↓reduceIte, false_and, iff_false]; simp

/-- Positive examples: a source with one outstanding token absorbs it and
becomes total; two tokens pool into a bundle of two. -/
theorem countAlg_examples :
    countAlg.op (source 1) readToken = some total ∧
      countAlg.op readToken readToken = some (tokens 2) := by
  decide

/-- Negative examples: two sources never compose (not even two totals), the
total permission cannot absorb a token it did not issue, and a source with one
outstanding token cannot absorb two. -/
theorem countAlg_negative_examples :
    countAlg.op total total = none ∧ countAlg.op total readToken = none ∧
      countAlg.op (source 1) (tokens 2) = none ∧ countAlg.op (source 3) (source 4) = none := by
  decide

/-- In the counting algebra the exclusive elements are exactly the total
permission `some 0`. -/
theorem countAlg_exclusive_iff (a : Count) : countAlg.Exclusive a ↔ a = total := by
  constructor
  · intro h
    rcases a with _ | z
    · have := h total rfl; simp [countAlg, total] at this
    · by_cases hz : z = 0
      · subst hz; rfl
      · exfalso
        by_cases hz' : 0 < z
        · have hc : countAlg.Compat (some z) readToken := by
            simp only [PartialAlg.Compat, countAlg, readToken]
            rw [countOp_some_some_of (by omega)]; rfl
          have := h _ hc; simp [countAlg, readToken] at this
        · have hc : countAlg.Compat (some z) (some (-z)) := by
            simp only [PartialAlg.Compat, countAlg]
            rw [countOp_some_some_of (by omega)]; rfl
          have := h _ hc; simp [countAlg] at this
  · rintro rfl b hb
    rcases b with _ | j
    · rfl
    · simp only [PartialAlg.Compat, countAlg, total, countOp_some_some] at hb
      split at hb
      · omega
      · simp at hb

/-! ## Laws -/

/-- **Counting permissions form a cancellative, positive partial commutative
monoid.** The counting algebra (unit `none`; sources `some n`, `n ≥ 0`; token
bundles `some (-k)`, `k ≥ 1`) is commutative, associative, has `none` as unit,
is cancellative, and is positive. -/
theorem countAlg_isPCM_cancel_positive :
    countAlg.IsPCM ∧ countAlg.Cancel ∧ countAlg.Positive := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b
    rcases a with _ | i <;> rcases b with _ | j
    · rfl
    · rfl
    · rfl
    · show countOp (some i) (some j) = countOp (some j) (some i)
      simp only [countOp_some_some]
      by_cases h : (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0))
      · have h' : (j < 0 ∨ i < 0) ∧ (0 ≤ j + i ∨ (j < 0 ∧ i < 0)) := by omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
        congr 2; omega
      · have h' : ¬ ((j < 0 ∨ i < 0) ∧ (0 ≤ j + i ∨ (j < 0 ∧ i < 0))) := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h')]
  · intro a b c
    rcases a with _ | i
    · show (countOp none b).bind (fun ab => countOp ab c) =
        (countOp b c).bind (fun bc => countOp none bc)
      change countOp b c = (countOp b c).bind (fun bc => some bc)
      cases countOp b c <;> rfl
    rcases b with _ | j
    · cases c <;> rfl
    rcases c with _ | k
    · show (countOp (some i) (some j)).bind (fun ab => countOp ab none) = countOp (some i) (some j)
      cases countOp (some i) (some j) with
      | none => rfl
      | some x => cases x <;> rfl
    show (countOp (some i) (some j)).bind (fun ab => countOp ab (some k)) =
      (countOp (some j) (some k)).bind (fun bc => countOp (some i) bc)
    simp only [countOp_some_some]
    split <;> split
    · simp only [Option.bind_some, countOp_some_some]
      split <;> split
      · congr 2; omega
      · omega
      · omega
      · rfl
    · simp only [Option.bind_some, Option.bind_none, countOp_some_some]
      split
      · omega
      · rfl
    · simp only [Option.bind_some, Option.bind_none, countOp_some_some]
      split
      · omega
      · rfl
    · rfl
  · intro a; rfl
  · intro a b c d hab hac
    rcases a with _ | i
    · cases hab; cases hac; rfl
    rcases b with _ | j <;> rcases c with _ | k
    · rfl
    · change some (some i) = some d at hab
      change countOp (some i) (some k) = some d at hac
      rw [countOp_some_some_eq_some] at hac
      cases hab; simp at hac; omega
    · change countOp (some i) (some j) = some d at hab
      change some (some i) = some d at hac
      rw [countOp_some_some_eq_some] at hab
      cases hac; simp at hab; omega
    · change countOp (some i) (some j) = some d at hab
      change countOp (some i) (some k) = some d at hac
      rw [countOp_some_some_eq_some] at hab hac
      obtain ⟨_, rfl⟩ := hab
      obtain ⟨_, h⟩ := hac
      simp only [Option.some.injEq] at h
      congr 1; omega
  · intro a b h
    rcases a with _ | i
    · rfl
    rcases b with _ | j
    · cases h
    · change countOp (some i) (some j) = some none at h
      rw [countOp_some_some_eq_some] at h
      cases h.2

/-! ## Splitting is source-mediated -/

/-- **A single read token cannot be split into two non-empty parts.** If a
composite equals one read token, one of the two parts is the empty permission. -/
theorem countAlg_readToken_atomic (a b : Count) (h : countAlg.op a b = some readToken) :
    a = none ∨ b = none := by
  rcases a with _ | i
  · exact .inl rfl
  · rcases b with _ | j
    · exact .inr rfl
    · exfalso
      simp only [countAlg, readToken] at h
      rw [countOp_some_some_eq_some] at h
      obtain ⟨⟨_, h2⟩, h3⟩ := h
      simp at h3; omega

/-- Non-vacuity of `countAlg_readToken_atomic`: its premise is satisfiable
(`none · readToken = readToken`). -/
theorem countAlg_readToken_atomic_nonvacuous : countAlg.op none readToken = some readToken := rfl

/-- Contrast for `countAlg_readToken_atomic`: a bundle of two tokens is the
composite of two non-empty parts, so atomicity is specific to single tokens. -/
theorem countAlg_two_tokens_split : countAlg.op readToken readToken = some (tokens 2) := by
  decide

/-- Tightness of `h` in `countAlg_readToken_atomic` (canonical form; the theorem
has no other hypothesis): with `a = b = readToken`, the premise fails (their
composite is the bundle `tokens 2`, not a single token) and so does the
conclusion. -/
theorem countAlg_readToken_atomic_needs_h :
    countAlg.op readToken readToken = some (tokens 2) ∧
      countAlg.op readToken readToken ≠ some readToken ∧
      ¬ (readToken = none ∨ readToken = none) := by
  decide

/-- **Every split of a source goes through the source's count.** If a source
permission `source n` is the composite of two non-empty parts, then one part is
a source with a strictly larger count `n + k` and the other is a bundle of
exactly `k ≥ 1` tokens. -/
theorem countAlg_split_of_source (n : Nat) (a b : Count) (h : countAlg.op a b = some (source n))
    (ha : a ≠ none) (hb : b ≠ none) :
    (∃ k : Nat, 0 < k ∧ a = source (n + k) ∧ b = tokens k) ∨
      (∃ k : Nat, 0 < k ∧ b = source (n + k) ∧ a = tokens k) := by
  rcases a with _ | i
  · exact absurd rfl ha
  rcases b with _ | j
  · exact absurd rfl hb
  simp only [countAlg, source] at h
  rw [countOp_some_some_eq_some] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Option.some.injEq] at h3
  rcases h1 with hi | hj
  · refine .inr ⟨(-i).toNat, by omega, ?_, ?_⟩
    · simp only [source, Option.some.injEq]; omega
    · rw [tokens_of_pos (by omega)]; simp only [Option.some.injEq]; omega
  · refine .inl ⟨(-j).toNat, by omega, ?_, ?_⟩
    · simp only [source, Option.some.injEq]; omega
    · rw [tokens_of_pos (by omega)]; simp only [Option.some.injEq]; omega

/-- Tightness of `ha` in `countAlg_split_of_source`: with `a = none` and
`b = source 0`, every other hypothesis holds and the conclusion fails. -/
theorem countAlg_split_of_source_needs_ha :
    countAlg.op none (source 0) = some (source 0) ∧ source 0 ≠ none ∧
      ¬ ((∃ k : Nat, 0 < k ∧ (none : Count) = source (0 + k) ∧ source 0 = tokens k) ∨
        (∃ k : Nat, 0 < k ∧ source 0 = source (0 + k) ∧ (none : Count) = tokens k)) := by
  refine ⟨rfl, by simp [source], ?_⟩
  rintro (⟨k, _, h, _⟩ | ⟨k, hk, _, h⟩)
  · simp [source] at h
  · rw [tokens_of_pos hk] at h; simp at h

/-- Tightness of `hb` in `countAlg_split_of_source`: with `a = source 0` and
`b = none`, every other hypothesis holds and the conclusion fails. -/
theorem countAlg_split_of_source_needs_hb :
    countAlg.op (source 0) none = some (source 0) ∧ source 0 ≠ none ∧
      ¬ ((∃ k : Nat, 0 < k ∧ source 0 = source (0 + k) ∧ (none : Count) = tokens k) ∨
        (∃ k : Nat, 0 < k ∧ (none : Count) = source (0 + k) ∧ source 0 = tokens k)) := by
  refine ⟨rfl, by simp [source], ?_⟩
  rintro (⟨k, hk, _, h⟩ | ⟨k, _, h, _⟩)
  · rw [tokens_of_pos hk] at h; simp at h
  · simp [source] at h

/-- Tightness of `h` in `countAlg_split_of_source` (canonical form): with
`n = 0` and `a = b = readToken`, the hypotheses `ha` and `hb` hold, the premise
`h` fails (two tokens pool to a bundle, not to a source), and the conclusion
fails. -/
theorem countAlg_split_of_source_needs_h :
    readToken ≠ none ∧ readToken ≠ none ∧ countAlg.op readToken readToken ≠ some (source 0) ∧
      ¬ ((∃ k : Nat, 0 < k ∧ readToken = source (0 + k) ∧ readToken = tokens k) ∨
        (∃ k : Nat, 0 < k ∧ readToken = source (0 + k) ∧ readToken = tokens k)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro (⟨k, _, h, _⟩ | ⟨k, _, h, _⟩) <;> simp [readToken, source] at h <;> omega

/-- Non-vacuity of `countAlg_split_of_source`: `source 1 · readToken = source 0`
with both parts non-empty. -/
theorem countAlg_split_of_source_nonvacuous :
    countAlg.op (source 1) readToken = some (source 0) ∧ source 1 ≠ none ∧ readToken ≠ none := by
  decide

/-- Composite of `m` single read tokens: the bundle `tokens m` (the empty
permission for `m = 0`). -/
theorem countAlg_opList_replicate_readToken (m : Nat) :
    countAlg.opList (List.replicate m readToken) = some (tokens m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, PartialAlg.opList, ih, Option.bind_some]
    cases m with
    | zero => rfl
    | succ m =>
      show countOp (some (-1)) (some (-((m + 1 : Nat) : Int))) =
        some (some (-((m + 1 + 1 : Nat) : Int)))
      rw [countOp_some_some_of (by omega)]
      congr 2; omega

/-- **Counting permissions split into any number of read permissions through
the source.** For every `n`, the total permission is the composite of
`source n` together with `n` single read tokens. -/
theorem countAlg_total_splits_into_source_and_readTokens (n : Nat) :
    countAlg.opList (source n :: List.replicate n readToken) = some total := by
  simp only [PartialAlg.opList, countAlg_opList_replicate_readToken, Option.bind_some]
  by_cases hn : n = 0
  · subst hn; rfl
  · rw [tokens_of_pos (by omega)]
    show countOp (some (n : Int)) (some (-(n : Int))) = some (some 0)
    rw [countOp_some_some_of (by omega)]
    congr 2; omega

/-- Instance of `countAlg_total_splits_into_source_and_readTokens` for `n = 2`:
`source 2`, `readToken`, `readToken` pool to the total permission. -/
theorem countAlg_total_splits_example :
    countAlg.opList [source 2, readToken, readToken] = some total := by
  decide

/-! ## Helper facts about complete configurations -/

theorem countAlg_opList_eq_unit (ts : List Count) (hts : ∀ t ∈ ts, t ≠ none)
    (h : countAlg.opList ts = some none) : ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    exfalso
    simp only [PartialAlg.opList] at h
    cases hr : countAlg.opList ts with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, Option.bind_some] at h
      rcases t with _ | i
      · exact hts none (by simp) rfl
      · rcases r with _ | j
        · simp [countAlg, countOp] at h
        · simp only [countAlg] at h
          rw [countOp_some_some] at h
          split at h <;> simp at h

theorem countAlg_opList_tokens_length_le (ts : List Count) (hts : ∀ t ∈ ts, t ≠ none) (w : Int)
    (h : countAlg.opList ts = some (some w)) (hw : w < 0) : (ts.length : Int) ≤ -w := by
  induction ts generalizing w with
  | nil => simp [PartialAlg.opList, countAlg] at h
  | cons t ts ih =>
    simp only [PartialAlg.opList] at h
    cases hr : countAlg.opList ts with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, Option.bind_some] at h
      rcases t with _ | i
      · exact absurd rfl (hts none (by simp))
      · have hts' : ∀ t ∈ ts, t ≠ none := fun t ht => hts t (by simp [ht])
        rcases r with _ | j
        · have := countAlg_opList_eq_unit ts hts' hr
          subst this
          simp [countAlg, countOp] at h
          simp; omega
        · simp only [countAlg] at h
          rw [countOp_some_some_eq_some] at h
          obtain ⟨⟨_, h2⟩, h3⟩ := h
          simp only [Option.some.injEq] at h3
          have := ih hts' j hr (by omega)
          simp; omega

end Toy.Perm
