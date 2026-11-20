import Toy.IFC.Core

/-!
# Hyperproperties, 2-Safety, Subset Closure, and Observation Encodings

This module formalizes hyperproperties over complete observations, defines
`SubsetClosed`, `IsOneSafety`, `IsTwoSafety`, and the bad-pair formulation
`CSTwoSafety`, proves `IsTwoSafety H ↔ CSTwoSafety H` and that `IsTwoSafety`
strictly implies `SubsetClosed`, proves that `tiniHyperprop Γ` is 2-safety (and
not 1-safety), and contrasts two observation encodings of termination-sensitive
noninterference:

- **Terminating-pairs encoding (`IOTrace`, `ioBehavior`, `tsniHyperprop`):**
  divergence is represented by absence of a pair. Whenever any `high` variable
  exists, `tsniHyperprop Γ` fails `SubsetClosed` and `IsTwoSafety`
  (`tsniHyperprop_termPairs_not_subsetClosed_of_high_var`,
  `tsniHyperprop_termPairs_not_twoSafety_of_high_var`).
- **Explicit-divergence outcome encoding (`OutTrace`, `outcomeBehavior`,
  `tsniOutHyperprop`):** divergence is represented explicitly as `none : Option (Store Var)`.
  Under this encoding, `TSNI Γ c ↔ tsniOutHyperprop Γ (outcomeBehavior c)` and
  `tsniOutHyperprop Γ` satisfies `IsTwoSafety` and `SubsetClosed`
  (`tsniOutHyperprop_isTwoSafety`, `tsniOutHyperprop_subsetClosed`), serving as
  the non-degenerate positive control / escape hatch showing that the
  non-subset-closure impossibility depends on the absence-of-pair encoding.
-/

namespace Toy.IFC

/-- A complete terminating input–output observation of a command: an initial store
    paired with its final store. Non-terminating runs produce no `IOTrace`. -/
abbrev IOTrace (Var : Type) := Store Var × Store Var

/-- An explicit-outcome input–output observation of a command: an initial store
    paired with `some σ'` for a terminating run or `none` for divergence
    (matching the `⊥`-augmented outcome view of Sabelfeld & Myers 2003, §IV-C). -/
abbrev OutTrace (Var : Type) := Store Var × Option (Store Var)

/-- A trace set (system behavior / trace property): a predicate on observations `α`. -/
abbrev TraceSet (α : Type) := α → Prop

/-- A hyperproperty over observations `α`: a predicate on sets of observations
    (Clarkson & Schneider 2010). -/
abbrev Hyperproperty (α : Type) := TraceSet α → Prop

/-- The terminating input–output behavior of command `c`: the set of all pairs
    `(σ, σ')` such that `Eval c σ σ'`. Non-terminating executions have no pair in
    `ioBehavior c`. -/
def ioBehavior {Var : Type} [DecidableEq Var] (c : Cmd Var) : TraceSet (IOTrace Var) :=
  fun p => Eval c p.1 p.2

/-- The explicit-outcome input–output behavior of command `c`: pairs `(σ, some σ')`
    when `Eval c σ σ'` and `(σ, none)` when `¬ Terminates c σ`. -/
def outcomeBehavior {Var : Type} [DecidableEq Var] (c : Cmd Var) : TraceSet (OutTrace Var) :=
  fun p =>
    match p.2 with
    | some σ' => Eval c p.1 σ'
    | none => ¬ Terminates c p.1

/-- Subset closure (downward closure under trace-set refinement) of a hyperproperty:
    if a trace set `S₂` satisfies `H` and `S₁ ⊆ S₂`, then `S₁` also satisfies `H`.
    In Clarkson & Schneider (2010, Theorem 1), every hypersafety property is
    subset-closed (`SHP ⊂ SSC`). -/
def SubsetClosed {α : Type} (H : Hyperproperty α) : Prop :=
  ∀ S₁ S₂ : TraceSet α, (∀ t, S₁ t → S₂ t) → H S₂ → H S₁

/-- A 1-safety (single-trace) hyperproperty over complete observations `α`: a
    trace set `S` satisfies `H` iff every singleton `{t} ⊆ S` satisfies `H`.
    Captures ordinary trace properties lifted to hyperproperties. -/
def IsOneSafety {α : Type} (H : Hyperproperty α) : Prop :=
  ∀ S : TraceSet α, H S ↔ ∀ t, S t → H (fun u => u = t)

/-- Package-specific pairwise-determinedness notion over complete observations `α`:
    a trace set `S` satisfies `H` iff every pair `{t₁, t₂} ⊆ S` jointly satisfies `H`.
    Proved equivalent to the non-empty bad-pair formulation `CSTwoSafety`
    (`isTwoSafety_iff_csTwoSafety`), and forces `H ∅` (`isTwoSafety_holds_empty`,
    `false_hyperprop_not_isTwoSafety`). Under a discrete-observation reading of
    Clarkson & Schneider (2010) (`M ≤ T` iff `M ⊆ T`) plus `H ∅`, it coincides
    with Clarkson & Schneider 2-hypersafety (the prefix-based infinite-trace
    topology of Clarkson & Schneider, the lower Vietoris construction applied to
    the Plotkin topology, is not formalized here; by their definitions, though not
    stated in their text, the empty hyperproperty is also hypersafety via the
    empty observation `M = ∅`; Terauchi & Aiken 2005 Def. 4 defines 2-safety as a
    set of programs using `⊥`). -/
def IsTwoSafety {α : Type} (H : Hyperproperty α) : Prop :=
  ∀ S : TraceSet α, H S ↔ ∀ t₁ t₂, S t₁ → S t₂ → H (fun t => t = t₁ ∨ t = t₂)

/-- Non-empty bad-pair characterization of 2-hypersafety over complete observations:
    every violating trace set `S` contains one or two observations `t₁, t₂` such
    that every superset `S'` containing both violates `H`. Matches Clarkson &
    Schneider's (2010) bad-observation-set definition specialized to discrete
    complete observations with non-empty bad sets (`|M| ∈ {1, 2}`). -/
def CSTwoSafety {α : Type} (H : Hyperproperty α) : Prop :=
  ∀ S : TraceSet α, ¬ H S →
    ∃ t₁ t₂, S t₁ ∧ S t₂ ∧ ∀ S' : TraceSet α, S' t₁ → S' t₂ → ¬ H S'

/-- Explicit binary relation characterizing pairwise termination-insensitive
    noninterference on two complete terminating I/O observations. -/
def tiniRel {Var : Type} (Γ : Var → Level) (t₁ t₂ : IOTrace Var) : Prop :=
  LowEq Γ t₁.1 t₂.1 → LowEq Γ t₁.2 t₂.2

/-- Termination-insensitive noninterference lifted to a hyperproperty over
    terminating I/O trace sets: every pair of observations in `S` satisfies `tiniRel Γ`. -/
def tiniHyperprop {Var : Type} (Γ : Var → Level) : Hyperproperty (IOTrace Var) :=
  fun S => ∀ t₁ t₂, S t₁ → S t₂ → tiniRel Γ t₁ t₂

/-- Termination-sensitive noninterference lifted to a hyperproperty over
    *terminating-pair* I/O trace sets `IOTrace Var = Store Var × Store Var`
    (where divergence is encoded solely by absence of a pair): whenever `S`
    contains a terminating run `(σ₁, σ₁')` and `σ₂` is low-equivalent to `σ₁`,
    `S` must also contain a terminating run `(σ₂, σ₂')` with `LowEq Γ σ₁' σ₂'`. -/
def tsniHyperprop {Var : Type} (Γ : Var → Level) : Hyperproperty (IOTrace Var) :=
  fun S =>
    ∀ σ₁ σ₂ σ₁',
      LowEq Γ σ₁ σ₂ →
      S (σ₁, σ₁') →
      ∃ σ₂', S (σ₂, σ₂') ∧ LowEq Γ σ₁' σ₂'

/-- Explicit pairwise relation characterizing termination-sensitive noninterference
    on two explicit-outcome observations `OutTrace Var = Store Var × Option (Store Var)`:
    low-equivalent initial stores must either both diverge (`none`, `none`) or both
    terminate in low-equivalent final stores (`some a`, `some b`). Matches the
    explicit-`⊥` low-view relation of Sabelfeld & Myers (2003, §IV-C). -/
def tsniOutRel {Var : Type} (Γ : Var → Level) (t₁ t₂ : OutTrace Var) : Prop :=
  LowEq Γ t₁.1 t₂.1 →
    match t₁.2, t₂.2 with
    | some a, some b => LowEq Γ a b
    | none, none => True
    | _, _ => False

/-- Termination-sensitive noninterference lifted to a hyperproperty over
    *explicit-outcome* trace sets `OutTrace Var`: every pair of outcome
    observations in `S` satisfies `tsniOutRel Γ`. -/
def tsniOutHyperprop {Var : Type} (Γ : Var → Level) : Hyperproperty (OutTrace Var) :=
  fun S => ∀ t₁ t₂, S t₁ → S t₂ → tsniOutRel Γ t₁ t₂

/-- Exact equivalence between command-level `TINI Γ c` and the hyperproperty
    `tiniHyperprop Γ` evaluated on `ioBehavior c`. -/
theorem tini_iff_tiniHyperprop {Var : Type} [DecidableEq Var]
    (Γ : Var → Level) (c : Cmd Var) :
    TINI Γ c ↔ tiniHyperprop Γ (ioBehavior c) := by
  constructor
  · intro hTini t₁ t₂ h₁ h₂ hLow
    exact hTini t₁.1 t₂.1 t₁.2 t₂.2 hLow h₁ h₂
  · intro hHyp σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
    exact hHyp (σ₁, σ₁') (σ₂, σ₂') h₁ h₂ hLow

/-- Exact equivalence between command-level `TSNI Γ c` and the terminating-pairs
    hyperproperty `tsniHyperprop Γ` evaluated on `ioBehavior c`. -/
theorem tsni_iff_tsniHyperprop {Var : Type} [DecidableEq Var]
    (Γ : Var → Level) (c : Cmd Var) :
    TSNI Γ c ↔ tsniHyperprop Γ (ioBehavior c) :=
  Iff.rfl

/-! ### Core Hyperproperty Results -/

/-- Every 2-safety hyperproperty (`IsTwoSafety H`) is subset-closed (closed
    under trace-set refinement). Generic supporting lemma analogous to
    Clarkson & Schneider (2010, Theorem 1, `SHP ⊂ SSC`). -/
theorem isTwoSafety_implies_subsetClosed {α : Type} {H : Hyperproperty α}
    (h2 : IsTwoSafety H) :
    SubsetClosed H := by
  intro S₁ S₂ hSub hS₂
  rw [h2] at hS₂ ⊢
  intro t₁ t₂ h₁ h₂
  exact hS₂ t₁ t₂ (hSub t₁ h₁) (hSub t₂ h₂)

/-- Definition-adequacy equivalence: `IsTwoSafety H` holds iff `H` satisfies the
    non-empty bad-pair condition `CSTwoSafety H`. -/
theorem isTwoSafety_iff_csTwoSafety {α : Type} (H : Hyperproperty α) :
    IsTwoSafety H ↔ CSTwoSafety H := by
  constructor
  · intro h2 S hnot
    refine Classical.byContradiction fun hex => hnot ?_
    rw [h2]
    intro t₁ t₂ h₁ h₂
    refine Classical.byContradiction fun hc =>
      hex ⟨t₁, t₂, h₁, h₂, fun S' h₁' h₂' hS' => hc ?_⟩
    exact isTwoSafety_implies_subsetClosed h2 _ S'
      (fun t ht => by rcases ht with rfl | rfl <;> assumption) hS'
  · intro hcs S
    constructor
    · intro hS t₁ t₂ h₁ h₂
      refine Classical.byContradiction fun hc => ?_
      rcases hcs _ hc with ⟨u₁, u₂, hu₁, hu₂, hbad⟩
      have m₁ : S u₁ := by rcases hu₁ with rfl | rfl <;> assumption
      have m₂ : S u₂ := by rcases hu₂ with rfl | rfl <;> assumption
      exact hbad S m₁ m₂ hS
    · intro hPairs
      refine Classical.byContradiction fun hc => ?_
      rcases hcs S hc with ⟨t₁, t₂, h₁, h₂, hbad⟩
      exact hbad _ (Or.inl rfl) (Or.inr rfl) (hPairs t₁ t₂ h₁ h₂)

/-- Every `IsTwoSafety` hyperproperty admits the empty trace set. -/
theorem isTwoSafety_admits_empty {α : Type} {H : Hyperproperty α}
    (h2 : IsTwoSafety H) : H (fun _ => False) :=
  (h2 (fun _ => False)).mpr (fun _ _ h => h.elim)

/-- Every `IsTwoSafety` hyperproperty holds of the empty trace set (`fun _ => False`). -/
theorem isTwoSafety_holds_empty {α : Type} {H : Hyperproperty α}
    (h2 : IsTwoSafety H) : H (fun _ => False) :=
  (h2 (fun _ => False)).mpr (fun _ _ h => h.elim)

/-- The empty hyperproperty (`fun _ => False`, which holds of no trace set) fails
    `IsTwoSafety`. Despite the name, this is not Clarkson & Schneider's (2010)
    hyperproperty `false`, which is `{∅}` (it holds of exactly the empty trace set)
    and, by a short informal argument, satisfies `IsTwoSafety`. Their hypersafety
    definition admits the empty hyperproperty via the empty observation `M = ∅`
    (derived from their definitions; the paper does not state it). -/
theorem false_hyperprop_not_isTwoSafety :
    ¬ IsTwoSafety (fun _ : TraceSet Unit => False) :=
  fun h2 => isTwoSafety_admits_empty h2

/-- `tiniHyperprop Γ` is a 2-safety hyperproperty (`IsTwoSafety`) for every
    security labeling `Γ`. -/
theorem tiniHyperprop_isTwoSafety {Var : Type} (Γ : Var → Level) :
    IsTwoSafety (tiniHyperprop Γ) := by
  intro S
  constructor
  · intro hS t₁ t₂ h₁ h₂ a b ha hb
    have haS : S a := by
      rcases ha with rfl | rfl <;> assumption
    have hbS : S b := by
      rcases hb with rfl | rfl <;> assumption
    exact hS a b haS hbS
  · intro hPairs t₁ t₂ h₁ h₂
    exact hPairs t₁ t₂ h₁ h₂ t₁ t₂ (Or.inl rfl) (Or.inr rfl)

/-- Corollary: `tiniHyperprop Γ` is subset-closed for every security labeling `Γ`. -/
theorem tiniHyperprop_subsetClosed {Var : Type} (Γ : Var → Level) :
    SubsetClosed (tiniHyperprop Γ) :=
  isTwoSafety_implies_subsetClosed (tiniHyperprop_isTwoSafety Γ)

/-- Impossibility result (terminating-pairs encoding): whenever `Γ` has at least
    one `high` variable (`Γ h = high`), `tsniHyperprop Γ` over terminating I/O
    trace sets (`Store Var × Store Var`, where divergence is absence of a pair)
    is NOT subset-closed.
    Witnessed by the identity behavior `S₂ = {(σ, σ)}` (which satisfies
    `tsniHyperprop Γ`) and its singleton subset `S₁ = {(zeroStore, zeroStore)}`
    (which violates `tsniHyperprop Γ` on the store setting all `high` variables
    to `1` and all `low` variables to `0`). Requires no `DecidableEq Var`.
    Note: this impossibility depends on encoding divergence as a missing pair;
    under explicit-outcome encoding (`tsniOutHyperprop`), TSNI is `IsTwoSafety`
    and `SubsetClosed` (`tsniOutHyperprop_isTwoSafety`, `tsni_iff_tsniOutHyperprop`). -/
theorem tsniHyperprop_termPairs_not_subsetClosed_of_high_var
    {Var : Type} {Γ : Var → Level} {h : Var}
    (hHigh : Γ h = .high) :
    ¬ SubsetClosed (tsniHyperprop Γ) := by
  intro hSub
  let S₂ : TraceSet (IOTrace Var) := fun p => p.1 = p.2
  let S₁ : TraceSet (IOTrace Var) := fun p => p = (zeroStore, zeroStore)
  let σHigh : Store Var := fun x => match Γ x with | .low => 0 | .high => 1
  have hS₂ : tsniHyperprop Γ S₂ := by
    intro σ₁ σ₂ σ₁' hLow hEq
    dsimp only [S₂] at hEq
    exact ⟨σ₂, rfl, hEq ▸ hLow⟩
  have hIncl : ∀ t, S₁ t → S₂ t := by
    intro t ht
    subst ht
    rfl
  have hS₁ : tsniHyperprop Γ S₁ := hSub S₁ S₂ hIncl hS₂
  have hLow : LowEq Γ zeroStore σHigh := by
    intro x hx
    simp [zeroStore, σHigh, hx]
  rcases hS₁ zeroStore σHigh zeroStore hLow rfl with ⟨σ₂', hMem, _⟩
  have hStoreEq : σHigh = zeroStore := congrArg Prod.fst hMem
  have hAt := congrFun hStoreEq h
  simp [zeroStore, σHigh, hHigh] at hAt

/-- Corollary (terminating-pairs encoding): whenever `Γ` has at least one `high`
    variable (`Γ h = high`), `tsniHyperprop Γ` over terminating I/O trace sets
    is not a 2-safety hyperproperty (`IsTwoSafety`). -/
theorem tsniHyperprop_termPairs_not_twoSafety_of_high_var
    {Var : Type} {Γ : Var → Level} {h : Var}
    (hHigh : Γ h = .high) :
    ¬ IsTwoSafety (tsniHyperprop Γ) :=
  fun h2 =>
    tsniHyperprop_termPairs_not_subsetClosed_of_high_var hHigh
      (isTwoSafety_implies_subsetClosed h2)

/-- Degenerate positive control for `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`
    (and tightness witness for `hHigh`): when every variable is `low`, `LowEq Γ`
    collapses to store equality, so `tsniHyperprop Γ` holds of every trace set
    and is trivially both 2-safety and subset-closed. -/
theorem tsniHyperprop_all_low_isTwoSafety
    {Var : Type} {Γ : Var → Level} (hAllLow : ∀ x, Γ x = .low) :
    IsTwoSafety (tsniHyperprop Γ) := by
  have hAll : ∀ S : TraceSet (IOTrace Var), tsniHyperprop Γ S := by
    intro S σ₁ σ₂ σ₁' hLow hMem
    have hEq : σ₁ = σ₂ := funext (fun x => hLow x (hAllLow x))
    subst hEq
    exact ⟨σ₁', hMem, LowEq.refl Γ σ₁'⟩
  intro S
  exact ⟨fun _ _ _ _ _ => hAll _, fun _ => hAll S⟩

theorem tsniHyperprop_all_low_subsetClosed
    {Var : Type} {Γ : Var → Level} (hAllLow : ∀ x, Γ x = .low) :
    SubsetClosed (tsniHyperprop Γ) :=
  isTwoSafety_implies_subsetClosed (tsniHyperprop_all_low_isTwoSafety hAllLow)

/-- Non-degenerate positive control / escape hatch for
    `tsniHyperprop_termPairs_not_subsetClosed_of_high_var`: when divergence is
    represented explicitly as `none : Option (Store Var)` (`OutTrace Var`),
    `tsniOutHyperprop Γ` is a 2-safety hyperproperty (`IsTwoSafety`) for every
    security labeling `Γ` (including nontrivial labelings with secrets). -/
theorem tsniOutHyperprop_isTwoSafety {Var : Type} (Γ : Var → Level) :
    IsTwoSafety (tsniOutHyperprop Γ) := by
  intro S
  constructor
  · intro hS t₁ t₂ h₁ h₂ a b ha hb
    have haS : S a := by rcases ha with rfl | rfl <;> assumption
    have hbS : S b := by rcases hb with rfl | rfl <;> assumption
    exact hS a b haS hbS
  · intro hPairs t₁ t₂ h₁ h₂
    exact hPairs t₁ t₂ h₁ h₂ t₁ t₂ (Or.inl rfl) (Or.inr rfl)

/-- Corollary: under explicit-divergence outcomes, `tsniOutHyperprop Γ` is
    subset-closed for every security labeling `Γ`. -/
theorem tsniOutHyperprop_subsetClosed {Var : Type} (Γ : Var → Level) :
    SubsetClosed (tsniOutHyperprop Γ) :=
  isTwoSafety_implies_subsetClosed (tsniOutHyperprop_isTwoSafety Γ)

/-- Exact characterization of command-level `TSNI Γ c` under the explicit-outcome
    encoding (`OutTrace Var`, `outcomeBehavior c`): a command satisfies `TSNI Γ c`
    iff its explicit-outcome behavior satisfies the 2-safety hyperproperty
    `tsniOutHyperprop Γ`. Uses determinism (`eval_deterministic`) and classical
    case split on `Terminates c σ₂`. -/
theorem tsni_iff_tsniOutHyperprop {Var : Type} [DecidableEq Var]
    (Γ : Var → Level) (c : Cmd Var) :
    TSNI Γ c ↔ tsniOutHyperprop Γ (outcomeBehavior c) := by
  constructor
  · intro hT ⟨σ₁, o₁⟩ ⟨σ₂, o₂⟩ h₁ h₂ hLow
    cases o₁ with
    | none =>
      cases o₂ with
      | none => exact True.intro
      | some b =>
        rcases hT σ₂ σ₁ b hLow.symm h₂ with ⟨a, ha, _⟩
        exact h₁ ⟨a, ha⟩
    | some a =>
      cases o₂ with
      | none =>
        rcases hT σ₁ σ₂ a hLow h₁ with ⟨b, hb, _⟩
        exact h₂ ⟨b, hb⟩
      | some b =>
        rcases hT σ₁ σ₂ a hLow h₁ with ⟨b', hb', hab⟩
        have hdet := eval_deterministic hb' h₂
        subst hdet
        exact hab
  · intro hH σ₁ σ₂ σ₁' hLow h₁
    by_cases hTerm : Terminates c σ₂
    · rcases hTerm with ⟨σ₂', h₂⟩
      exact ⟨σ₂', h₂, hH (σ₁, some σ₁') (σ₂, some σ₂') h₁ h₂ hLow⟩
    · exact False.elim (hH (σ₁, some σ₁') (σ₂, none) h₁ hTerm hLow)

/-! ### Auxiliary Hyperproperties & Definition Positive/Negative Examples -/

/-- A simple hyperliveness property: a trace set must be non-empty.
    Used to witness that `SubsetClosed` does not hold of all hyperproperties. -/
def nonEmptyTraceSet {α : Type} : Hyperproperty α :=
  fun S => ∃ t, S t

/-- A 3-safety cardinality property: a trace set contains at most two distinct traces.
    Used to witness that `SubsetClosed` is strictly weaker than `IsTwoSafety`. -/
def atMostTwoTraces {α : Type} : Hyperproperty α :=
  fun S => ∀ t₁ t₂ t₃, S t₁ → S t₂ → S t₃ → t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃

-- Positive & negative examples for `ioBehavior`

/-- Positive example for `ioBehavior`: `l := 1` relates `storeZero` to `storeLowOne`. -/
theorem ioBehavior_pos_assign :
    ioBehavior (.assign .l (.lit 1)) (storeZero, storeLowOne) := by
  have hEq : Store.update storeZero .l (eval storeZero (.lit 1)) = storeLowOne := rfl
  rw [ioBehavior, ← hEq]
  exact Eval.assign

/-- Negative example for `ioBehavior`: `l := 1` does not relate `storeZero` to `storeZero`. -/
theorem ioBehavior_neg_wrong_final :
    ¬ ioBehavior (.assign .l (.lit 1)) (storeZero, storeZero) :=
  eval_neg_wrong_final

-- Positive & negative examples for `outcomeBehavior`

/-- Positive example for `outcomeBehavior` (terminating): `l := 1` maps `storeZero`
    to `some storeLowOne`. -/
theorem outcomeBehavior_pos_assign :
    outcomeBehavior (.assign .l (.lit 1)) (storeZero, some storeLowOne) :=
  ioBehavior_pos_assign

/-- Positive example for `outcomeBehavior` (diverging): `while 1 do skip` maps
    `storeZero` to `none`. -/
theorem outcomeBehavior_pos_while_one :
    outcomeBehavior (.whileLoop (.lit 1) .skip) (storeZero, none) :=
  terminates_neg_while_one

/-- Negative example for `outcomeBehavior`: `l := 1` does not diverge from `storeZero`. -/
theorem outcomeBehavior_neg_assign_none :
    ¬ outcomeBehavior (.assign .l (.lit 1)) (storeZero, none) :=
  fun h => h terminates_pos_assign

/-- Negative example for `outcomeBehavior`: `l := 1` does not terminate in `storeZero`. -/
theorem outcomeBehavior_neg_wrong_final :
    ¬ outcomeBehavior (.assign .l (.lit 1)) (storeZero, some storeZero) :=
  eval_neg_wrong_final

-- Positive & negative examples for `SubsetClosed`

/-- Positive example for `SubsetClosed`: `tiniHyperprop twoVarEnv` is subset-closed. -/
theorem subsetClosed_pos_tiniHyperprop :
    SubsetClosed (tiniHyperprop twoVarEnv) :=
  tiniHyperprop_subsetClosed twoVarEnv

/-- Negative example for `SubsetClosed`: `nonEmptyTraceSet` on `Unit` is not subset-closed. -/
theorem subsetClosed_neg_nonEmpty :
    ¬ SubsetClosed (nonEmptyTraceSet (α := Unit)) := by
  intro hSub
  have hFull : nonEmptyTraceSet (fun _ : Unit => True) := ⟨(), trivial⟩
  have hEmpty : nonEmptyTraceSet (fun _ : Unit => False) :=
    hSub (fun _ => False) (fun _ => True) (fun _ h => False.elim h) hFull
  rcases hEmpty with ⟨_, hFalse⟩
  exact hFalse

/-- Negative example for `SubsetClosed`: `tsniHyperprop twoVarEnv` is not subset-closed. -/
theorem subsetClosed_neg_tsniHyperprop :
    ¬ SubsetClosed (tsniHyperprop twoVarEnv) :=
  tsniHyperprop_termPairs_not_subsetClosed_of_high_var (h := .h) rfl

-- Positive & negative examples for `tiniHyperprop`

/-- Positive example for `tiniHyperprop`: `ioBehavior .skip` satisfies `tiniHyperprop twoVarEnv`. -/
theorem tiniHyperprop_pos_skip :
    tiniHyperprop twoVarEnv (ioBehavior .skip) := by
  rintro ⟨σ₁, σ₁'⟩ ⟨σ₂, σ₂'⟩ h₁ h₂ hLow
  cases h₁
  cases h₂
  exact hLow

/-- Negative example for `tiniHyperprop`: `ioBehavior (l := h)` violates `tiniHyperprop twoVarEnv`. -/
theorem tiniHyperprop_neg_explicit_flow :
    ¬ tiniHyperprop twoVarEnv (ioBehavior (explicitFlowProg .l .h)) :=
  fun h => tini_neg_explicit_flow ((tini_iff_tiniHyperprop twoVarEnv (explicitFlowProg .l .h)).mpr h)

-- Positive & negative examples for `IsOneSafety`

/-- Positive example for `IsOneSafety`: any lifted single-trace predicate (here,
    final `l = 0`) is 1-safety. -/
theorem isOneSafety_pos_lowOutputZero :
    IsOneSafety (fun S : TraceSet (IOTrace TwoVar) => ∀ t, S t → t.2 .l = 0) := by
  intro S
  constructor
  · intro hS t ht u hu
    rw [hu]
    exact hS t ht
  · intro hSingle t ht
    exact hSingle t ht t rfl

/-- Negative example for `IsOneSafety`: `tiniHyperprop twoVarEnv` is genuinely
    not a 1-safety (single-trace) property, because every singleton trace set
    trivially satisfies it while `ioBehavior (l := h)` does not. -/
theorem tiniHyperprop_not_oneSafety :
    ¬ IsOneSafety (tiniHyperprop twoVarEnv) := by
  intro h1
  apply tiniHyperprop_neg_explicit_flow
  rw [h1]
  intro t _ a b ha hb _
  obtain rfl : a = t := ha
  obtain rfl : b = a := hb
  exact LowEq.refl _ _

-- Positive & negative examples for `IsTwoSafety`

/-- Positive example for `IsTwoSafety`: `tiniHyperprop twoVarEnv` is 2-safety. -/
theorem isTwoSafety_pos_tiniHyperprop :
    IsTwoSafety (tiniHyperprop twoVarEnv) :=
  tiniHyperprop_isTwoSafety twoVarEnv

/-- Negative example for `IsTwoSafety` (and separation from `SubsetClosed`):
    `atMostTwoTraces` on `Fin 3` is `SubsetClosed`, yet fails `IsTwoSafety`. -/
theorem atMostTwoTraces_subsetClosed_not_twoSafety :
    SubsetClosed (atMostTwoTraces (α := Fin 3)) ∧
    ¬ IsTwoSafety (atMostTwoTraces (α := Fin 3)) := by
  constructor
  · intro S₁ S₂ hSub hS₂ t₁ t₂ t₃ h₁ h₂ h₃
    exact hS₂ t₁ t₂ t₃ (hSub t₁ h₁) (hSub t₂ h₂) (hSub t₃ h₃)
  · intro h2
    have hPairs : ∀ t₁ t₂ : Fin 3, True → True →
        atMostTwoTraces (fun t => t = t₁ ∨ t = t₂) := by
      intro t₁ t₂ _ _ a b c ha hb hc
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    have hAll : atMostTwoTraces (fun _ : Fin 3 => True) :=
      (h2 (fun _ => True)).mpr hPairs
    have hContra := hAll ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ trivial trivial trivial
    rcases hContra with h01 | h02 | h12
    · cases h01
    · cases h02
    · cases h12

-- Positive & negative examples for `CSTwoSafety`

/-- Positive example for `CSTwoSafety`: `tiniHyperprop twoVarEnv` satisfies `CSTwoSafety`. -/
theorem csTwoSafety_pos_tiniHyperprop :
    CSTwoSafety (tiniHyperprop twoVarEnv) :=
  (isTwoSafety_iff_csTwoSafety (tiniHyperprop twoVarEnv)).mp (tiniHyperprop_isTwoSafety twoVarEnv)

/-- Negative example for `CSTwoSafety`: `atMostTwoTraces` on `Fin 3` fails `CSTwoSafety`. -/
theorem csTwoSafety_neg_atMostTwoTraces :
    ¬ CSTwoSafety (atMostTwoTraces (α := Fin 3)) :=
  fun h => atMostTwoTraces_subsetClosed_not_twoSafety.2
    ((isTwoSafety_iff_csTwoSafety _).mpr h)

-- Positive & negative examples for `tsniHyperprop`

/-- Positive example for `tsniHyperprop`: `ioBehavior .skip` satisfies `tsniHyperprop twoVarEnv`. -/
theorem tsniHyperprop_pos_skip :
    tsniHyperprop twoVarEnv (ioBehavior .skip) := by
  intro σ₁ σ₂ σ₁' hLow h₁
  cases h₁
  exact ⟨σ₂, Eval.skip, hLow⟩

/-- Negative example for `tsniHyperprop`: `ioBehavior (while h do skip)` violates `tsniHyperprop twoVarEnv`. -/
theorem tsniHyperprop_neg_while_h :
    ¬ tsniHyperprop twoVarEnv (ioBehavior (termChannelProg .h)) :=
  tsni_neg_while_h

-- Positive & negative examples for `tsniOutHyperprop`

/-- Positive example for `tsniOutHyperprop`: `outcomeBehavior .skip` satisfies
    `tsniOutHyperprop twoVarEnv`. -/
theorem tsniOutHyperprop_pos_skip :
    tsniOutHyperprop twoVarEnv (outcomeBehavior .skip) :=
  (tsni_iff_tsniOutHyperprop twoVarEnv .skip).mp (fun _ _ _ hLow h₁ => by cases h₁; exact ⟨_, Eval.skip, hLow⟩)

/-- Negative example for `tsniOutHyperprop`: `outcomeBehavior (while h do skip)`
    violates `tsniOutHyperprop twoVarEnv`. -/
theorem tsniOutHyperprop_neg_while_h :
    ¬ tsniOutHyperprop twoVarEnv (outcomeBehavior (termChannelProg .h)) :=
  fun h => tsni_neg_while_h ((tsni_iff_tsniOutHyperprop twoVarEnv (termChannelProg .h)).mpr h)

end Toy.IFC
