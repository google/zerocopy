import ToyLayoutDfa.Results
import ToyLayoutDfa.Examples

/-!
# Counterexamples and non-vacuity witnesses for the universal check

Every theorem here is fully proved. A counterexample `X_needs_H` states that a concrete
instance satisfies every hypothesis of theorem `X` other than `H`, fails `H`, and fails
`X`'s conclusion. A non-vacuity theorem `X_nonvacuous` states that a concrete instance
satisfies all of `X`'s hypotheses (and, for `↔` statements, exhibits both truth values
where noted).
-/

namespace Toy.LayoutDfa

open Layout

/-! ### Fixture facts -/

theorem b0L_fixedSize : b0L.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl
theorem b1L_fixedSize : b1L.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl
theorem uL_fixedSize : uL.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl
theorem boolL_fixedSize : boolL.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl
theorem unitL_fixedSize : unitL.FixedSize 0 :=
  fixedSize_of_rankCert' (rank := fun _ => 0) (by decide) rfl
theorem b0uL_fixedSize : b0uL.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => 2 - q) (by decide) rfl
theorem boolUL_fixedSize : boolUL.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => 2 - q) (by decide) rfl
theorem bool2L_fixedSize : bool2L.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => 2 - q) (by decide) rfl
theorem deadL_fixedSize : deadL.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => if q = 0 then 1 else 0) (by decide) rfl
theorem ndSrcL_fixedSize : ndSrcL.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => if q = 0 then 2 else if q = 3 then 0 else 1)
    (by decide) rfl
theorem ndDstL_fixedSize : ndDstL.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => if q = 0 then 2 else if q = 3 then 0 else 1)
    (by decide) rfl
theorem chainL_fixedSize : chainL.FixedSize 5 :=
  fixedSize_of_rankCert' (rank := fun q => 5 - q) (by decide) rfl
theorem u8L_fixedSize : u8L.FixedSize 1 :=
  fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide +kernel) rfl
theorem u16L_fixedSize : u16L.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => 2 - q) (by decide +kernel) rfl
theorem u8PadL_fixedSize : u8PadL.FixedSize 2 :=
  fixedSize_of_rankCert' (rank := fun q => 2 - q) (by decide +kernel) rfl

theorem b0L_live : b0L.ReachableLive :=
  reachableLive_of_liveCert (rank := fun q => 1 - q) (R := [0, 1]) (by decide)
theorem boolL_live : boolL.ReachableLive :=
  reachableLive_of_liveCert (rank := fun q => 1 - q) (R := [0, 1]) (by decide)
theorem unitL_live : unitL.ReachableLive :=
  reachableLive_of_liveCert (rank := fun _ => 0) (R := [0]) (by decide)
theorem ndSrcL_live : ndSrcL.ReachableLive :=
  reachableLive_of_liveCert (rank := fun q => if q = 0 then 2 else if q = 3 then 0 else 1)
    (R := [0, 1, 3]) (by decide)
theorem chainL_live : chainL.ReachableLive :=
  reachableLive_of_liveCert (rank := fun q => 5 - q) (R := [0, 1, 2, 3, 4, 5]) (by decide)

theorem unitL_not_fixedSize_one : ¬ unitL.FixedSize 1 :=
  not_fixedSize_of_lang (w := []) (by decide) (by decide)
theorem cycL_not_fixedSize_five : ¬ cycL.FixedSize 5 :=
  not_fixedSize_of_lang (w := [Sym.byte 0, Sym.byte 1]) (by decide) (by decide)
theorem b0L_not_fixedSize_zero : ¬ b0L.FixedSize 0 :=
  not_fixedSize_of_lang (w := [Sym.byte 0]) (by decide) (by decide)
theorem b0L_not_fixedSize_two : ¬ b0L.FixedSize 2 :=
  not_fixedSize_of_lang (w := [Sym.byte 0]) (by decide) (by decide)

/-- Both automata of the nondeterminism counterexample accept exactly the two words `[0, 1]`
and `[0, 2]`. -/
theorem ndSrcL_ndDstL_lang (s : List Sym) :
    (ndSrcL.Lang s ↔ s = [Sym.byte 0, Sym.byte 1] ∨ s = [Sym.byte 0, Sym.byte 2]) ∧
    (ndDstL.Lang s ↔ s = [Sym.byte 0, Sym.byte 1] ∨ s = [Sym.byte 0, Sym.byte 2]) := by
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · exact forall_lang_of_wordsFrom
      (P := fun s => s = [Sym.byte 0, Sym.byte 1] ∨ s = [Sym.byte 0, Sym.byte 2])
      ndSrcL_fixedSize (by decide) s h
  · rintro (rfl | rfl) <;> decide
  · exact forall_lang_of_wordsFrom
      (P := fun s => s = [Sym.byte 0, Sym.byte 1] ∨ s = [Sym.byte 0, Sym.byte 2])
      ndDstL_fixedSize (by decide) s h
  · rintro (rfl | rfl) <;> decide

theorem ndSrcL_subset_ndDstL : Subset ndSrcL ndDstL :=
  forall_lang_of_wordsFrom ndSrcL_fixedSize (by decide)

theorem ndSrcL_fitSubset_ndDstL : FitSubset ndSrcL ndDstL 2 :=
  forall_lang_of_wordsFrom (P := fun s => ndDstL.Lang (fit 2 s)) ndSrcL_fixedSize (by decide)

theorem deadL_subset_b1L : Subset deadL b1L :=
  forall_lang_of_wordsFrom deadL_fixedSize (by decide)

theorem deadL_fitSubset_b1L : FitSubset deadL b1L 1 :=
  forall_lang_of_wordsFrom (P := fun s => b1L.Lang (fit 1 s)) deadL_fixedSize (by decide)

theorem chainL_fitSubset_cycL : FitSubset chainL cycL 5 :=
  forall_lang_of_wordsFrom (P := fun s => cycL.Lang (fit 5 s)) chainL_fixedSize (by decide)

/-! ### Soundness of `forallCheck` -/

/-- Dropping `FixedSize B nB`: the destination `()` has its start state as accept state, so
the check succeeds at once (truncation) for the source `{[0]}`, but `fit 1 [0] = [0]` is not
accepted by `()`. -/
theorem forallCheck_sound_needs_fixedSize_dst :
    ¬ unitL.FixedSize 1 ∧ forallCheck b0L unitL = true ∧ ¬ FitSubset b0L unitL 1 :=
  ⟨unitL_not_fixedSize_one, by decide,
    fun h => absurd (h [Sym.byte 0] (by decide)) (by decide)⟩

theorem forallCheck_sound_fit_nonvacuous :
    boolL.FixedSize 1 ∧ forallCheck b0L boolL = true :=
  ⟨boolL_fixedSize, by decide⟩

theorem varDstL_not_fixedSize : ∀ n, ¬ varDstL.FixedSize n := by
  intro n h
  have h1 : [Sym.byte 0].length = n := h [Sym.byte 0] (by decide)
  have h2 : [Sym.byte 1, Sym.byte 1].length = n := h [Sym.byte 1, Sym.byte 1] (by decide)
  simp at h1 h2
  omega

/-- `varDstL` accepts exactly the two words `[0]` and `[1, 1]` (the forward direction). -/
theorem varDstL_lang {w : List Sym} (hw : varDstL.Lang w) :
    w = [Sym.byte 0] ∨ w = [Sym.byte 1, Sym.byte 1] := by
  cases w with
  | nil => exact absurd (path_nil_iff.mp hw) (by decide)
  | cons a w =>
    obtain ⟨_, q1, he1, hp1⟩ := path_cons_iff.mp hw
    simp [varDstL] at he1
    rcases he1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases w with
      | nil => left; rfl
      | cons b w' => exact absurd (path_cons_iff.mp hp1).1 (by decide)
    · cases w with
      | nil => exact absurd (path_nil_iff.mp hp1) (by decide)
      | cons b w' =>
        obtain ⟨_, q2, he2, hp2⟩ := path_cons_iff.mp hp1
        simp [varDstL] at he2
        obtain ⟨rfl, rfl⟩ := he2
        cases w' with
        | nil => right; rfl
        | cons c w'' => exact absurd (path_cons_iff.mp hp2).1 (by decide)

/-- Dropping `FixedSize B nB` with a genuinely variable-size destination: `varDstL`
(language `{[0], [1, 1]}`, no fixed size) is accepted by the check against the source
`pairSrcL` (language `{[0, 0], [1, 1]}`), yet for every `nB` some source word has a
size-`nB` view that `varDstL` rejects. -/
theorem forallCheck_sound_needs_fixedSize_dst_variable :
    (∀ n, ¬ varDstL.FixedSize n) ∧ forallCheck pairSrcL varDstL = true ∧
      ∀ n, ¬ FitSubset pairSrcL varDstL n := by
  refine ⟨varDstL_not_fixedSize, by decide, fun n h => ?_⟩
  have h0 := varDstL_lang (h [Sym.byte 0, Sym.byte 0] (by decide))
  have h1 := varDstL_lang (h [Sym.byte 1, Sym.byte 1] (by decide))
  have l0 := length_fit n [Sym.byte 0, Sym.byte 0]
  rcases h0 with h0' | h0'
  · rw [h0'] at l0
    simp at l0
    subst l0
    rcases h1 with h1' | h1' <;> simp [fit] at h1'
  · rw [h0'] at l0
    simp at l0
    subst l0
    simp [fit] at h0'

/-! ### Completeness of `forallCheck` -/

/-- Dropping `Deterministic B` (the headline counterexample for completeness of the
universal check): source and destination both have language `{[0, 1], [0, 2]}`
(`ndSrcL_ndDstL_lang`), the source is deterministic and live, both have fixed size 2, yet
the check fails because after byte 0 it must commit to one destination state, and neither
continues with both 1 and 2. -/
theorem forallCheck_complete_needs_deterministic :
    ndDstL.FixedSize 2 ∧ ndSrcL.ReachableLive ∧ FitSubset ndSrcL ndDstL 2 ∧
      ¬ ndDstL.Deterministic ∧ forallCheck ndSrcL ndDstL = false ∧
      ndSrcL.Deterministic ∧ ndSrcL.FixedSize 2 :=
  ⟨ndDstL_fixedSize, ndSrcL_live, ndSrcL_fitSubset_ndDstL, by decide, by decide, by decide,
    ndSrcL_fixedSize⟩

/-- Positive control for the nondeterministic counterexample: against the deterministic
source automaton with the same language, the check succeeds. -/
theorem forallCheck_ndSrcL_self : ndSrcL.Deterministic ∧ forallCheck ndSrcL ndSrcL = true := by
  decide

/-- Dropping `ReachableLive A`: the source has a dead branch (byte 0 to a state with no
edges); its language `{[1]}` is included in the destination's `{[1]}`, but the check
requires a destination edge for byte 0 and fails. -/
theorem forallCheck_complete_needs_reachableLive :
    b1L.FixedSize 1 ∧ b1L.Deterministic ∧ FitSubset deadL b1L 1 ∧ ¬ deadL.ReachableLive ∧
      forallCheck deadL b1L = false :=
  ⟨b1L_fixedSize, by decide, deadL_fitSubset_b1L, ex_not_reachableLive, by decide⟩

/-- Dropping `FixedSize B nB`: a cyclic deterministic destination `0 0* 1` with three
edges accepts the source word `[0, 0, 0, 0, 1]`, but the check's step budget
(`fuelFor cycL = 4`) is exhausted before the source word ends. -/
theorem forallCheck_complete_needs_fixedSize_dst :
    cycL.Deterministic ∧ chainL.ReachableLive ∧ FitSubset chainL cycL 5 ∧
      ¬ cycL.FixedSize 5 ∧ forallCheck chainL cycL = false :=
  ⟨by decide, chainL_live, chainL_fitSubset_cycL, cycL_not_fixedSize_five, by decide⟩

theorem forallCheck_complete_fit_nonvacuous :
    boolL.FixedSize 1 ∧ boolL.Deterministic ∧ b0L.ReachableLive ∧ FitSubset b0L boolL 1 :=
  ⟨boolL_fixedSize, by decide, b0L_live,
    forall_lang_of_wordsFrom (P := fun s => boolL.Lang (fit 1 s)) b0L_fixedSize (by decide)⟩

/-! ### Completeness of `forallCheck` without cycles through the reachable live part -/

/-- Dropping `ReachableLiveAcyclic B`: the destination `0 0* 1` has a self-loop at a reachable
live state and exhausts the step budget (`fuelFor cycL = 4`) before the five-symbol source
word ends. -/
theorem forallCheck_complete_needs_reachableLiveAcyclic :
    cycL.Deterministic ∧ chainL.ReachableLive ∧ FitSubset chainL cycL 5 ∧
      ¬ cycL.ReachableLiveAcyclic ∧ forallCheck chainL cycL = false :=
  ⟨by decide, chainL_live, chainL_fitSubset_cycL, cycL_not_reachableLiveAcyclic, by decide⟩

theorem forallCheck_complete_acyc_needs_deterministic :
    ndDstL.ReachableLiveAcyclic ∧ ndSrcL.ReachableLive ∧ FitSubset ndSrcL ndDstL 2 ∧
      ¬ ndDstL.Deterministic ∧ forallCheck ndSrcL ndDstL = false :=
  ⟨reachableLiveAcyclic_of_acyclic ndDstL_acyclic, ndSrcL_live, ndSrcL_fitSubset_ndDstL,
    by decide, by decide⟩

theorem forallCheck_complete_acyc_needs_reachableLive :
    b1L.ReachableLiveAcyclic ∧ b1L.Deterministic ∧ FitSubset deadL b1L 1 ∧
      ¬ deadL.ReachableLive ∧ forallCheck deadL b1L = false :=
  ⟨reachableLiveAcyclic_of_acyclic b1L_acyclic, by decide, deadL_fitSubset_b1L,
    ex_not_reachableLive, by decide⟩

/-- All hypotheses hold for a destination without a fixed size (`b0L` into the acyclic
`varDstL` at `nB = 1`) and for a destination that is not `Acyclic` (`b0L` into
`deadCycReachL`, whose reachable dead state has a self-loop, at `nB = 1`). -/
theorem forallCheck_complete_acyc_nonvacuous :
    (varDstL.ReachableLiveAcyclic ∧ varDstL.Deterministic ∧ b0L.ReachableLive ∧
      FitSubset b0L varDstL 1 ∧ (∀ n, ¬ varDstL.FixedSize n)) ∧
    (deadCycReachL.ReachableLiveAcyclic ∧ deadCycReachL.Deterministic ∧ b0L.ReachableLive ∧
      FitSubset b0L deadCycReachL 1 ∧ ¬ deadCycReachL.Acyclic) :=
  ⟨⟨reachableLiveAcyclic_of_acyclic varDstL_acyclic, by decide, b0L_live,
      forall_lang_of_wordsFrom (P := fun s => varDstL.Lang (fit 1 s)) b0L_fixedSize (by decide),
      varDstL_not_fixedSize⟩,
    ⟨reachableLiveAcyclic_of_fixedSize deadCycReachL_fixedSize, by decide, b0L_live,
      forall_lang_of_wordsFrom (P := fun s => deadCycReachL.Lang (fit 1 s)) b0L_fixedSize
        (by decide),
      deadCycReachL_not_acyclic⟩⟩

/-- `FixedSize` and `Acyclic` are incomparable: `deadCycReachL` is deterministic, inhabited and
of fixed size 1 but not `Acyclic`; `varDstL` is deterministic, inhabited and `Acyclic` but of
no fixed size. -/
theorem fixedSize_acyclic_incomparable :
    (deadCycReachL.FixedSize 1 ∧ deadCycReachL.Deterministic ∧ deadCycReachL.Lang [Sym.byte 0] ∧
      ¬ deadCycReachL.Acyclic) ∧
    (varDstL.Acyclic ∧ varDstL.Deterministic ∧ varDstL.Lang [Sym.byte 0] ∧
      ∀ n, ¬ varDstL.FixedSize n) :=
  ⟨⟨deadCycReachL_fixedSize, by decide, by decide, deadCycReachL_not_acyclic⟩,
    ⟨varDstL_acyclic, by decide, by decide, varDstL_not_fixedSize⟩⟩

/-- `ReachableLiveAcyclic` is strictly weaker than `Acyclic` (witness `deadCycReachL`) and than
`FixedSize` at every size (witness `varDstL`). -/
theorem reachableLiveAcyclic_strictly_weaker_than_both :
    (deadCycReachL.ReachableLiveAcyclic ∧ ¬ deadCycReachL.Acyclic) ∧
    (varDstL.ReachableLiveAcyclic ∧ ∀ n, ¬ varDstL.FixedSize n) :=
  ⟨⟨reachableLiveAcyclic_of_fixedSize deadCycReachL_fixedSize, deadCycReachL_not_acyclic⟩,
    ⟨reachableLiveAcyclic_of_acyclic varDstL_acyclic, varDstL_not_fixedSize⟩⟩

/-! ### The step budget counts list entries -/

theorem path_iff_of_edges_iff {A B : Layout} (ha : A.accept = B.accept)
    (he : ∀ e, e ∈ A.edges ↔ e ∈ B.edges) {q : Nat} {w : List Sym} {r : Nat} :
    A.Path q w r ↔ B.Path q w r := by
  constructor <;> intro hp
  · induction hp with
    | nil q => exact Path.nil q
    | cons hq hmem _ ih => exact Path.cons (ha ▸ hq) ((he _).mp hmem) ih
  · induction hp with
    | nil q => exact Path.nil q
    | cons hq hmem _ ih => exact Path.cons (ha.symm ▸ hq) ((he _).mpr hmem) ih

/-- `cycDupL` and `cycL` have the same start state, accept state, edge set and language,
but `cycDupL` lists one edge three times; the longer list raises the step budget, and both
checks change their answer for the source `chainL`. -/
theorem checks_depend_on_edge_list_representation :
    cycDupL.start = cycL.start ∧ cycDupL.accept = cycL.accept ∧
      (∀ e, e ∈ cycDupL.edges ↔ e ∈ cycL.edges) ∧ (∀ w, cycDupL.Lang w ↔ cycL.Lang w) ∧
      forallCheck chainL cycL = false ∧ forallCheck chainL cycDupL = true ∧
      existsCheck chainL cycL = false ∧ existsCheck chainL cycDupL = true := by
  have he : ∀ e, e ∈ cycDupL.edges ↔ e ∈ cycL.edges := by
    intro e
    simp [cycDupL, cycL]
  exact ⟨rfl, rfl, he, fun _ => path_iff_of_edges_iff (A := cycDupL) (B := cycL) rfl he, by decide, by decide, by decide,
    by decide⟩

/-! ### The equal-size characterization -/

/-- Dropping `FixedSize A n`: the source `()` (size 0) and the destination `{[uninit]}`
(size 1): the check succeeds by extension, but `[] ∉ {[uninit]}`. -/
theorem forallCheck_iff_subset_needs_fixedSize_src :
    uL.FixedSize 1 ∧ uL.Deterministic ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (forallCheck unitL uL = true ↔ Subset unitL uL) :=
  ⟨uL_fixedSize, by decide, unitL_live, unitL_not_fixedSize_one,
    fun h => absurd (h.mp (by decide) [] (by decide)) (by decide)⟩

/-- Dropping `FixedSize B n`: source `{[0]}` (size 1), destination `()` (size 0): the check
succeeds by truncation, but `[0] ∉ {[]}`. -/
theorem forallCheck_iff_subset_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ unitL.Deterministic ∧ b0L.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (forallCheck b0L unitL = true ↔ Subset b0L unitL) :=
  ⟨b0L_fixedSize, by decide, b0L_live, unitL_not_fixedSize_one,
    fun h => absurd (h.mp (by decide) [Sym.byte 0] (by decide)) (by decide)⟩

theorem forallCheck_iff_subset_needs_deterministic :
    ndSrcL.FixedSize 2 ∧ ndDstL.FixedSize 2 ∧ ndSrcL.ReachableLive ∧ ¬ ndDstL.Deterministic ∧
      ¬ (forallCheck ndSrcL ndDstL = true ↔ Subset ndSrcL ndDstL) :=
  ⟨ndSrcL_fixedSize, ndDstL_fixedSize, ndSrcL_live, by decide,
    fun h => absurd (h.mpr ndSrcL_subset_ndDstL) (by decide)⟩

theorem forallCheck_iff_subset_needs_reachableLive :
    deadL.FixedSize 1 ∧ b1L.FixedSize 1 ∧ b1L.Deterministic ∧ ¬ deadL.ReachableLive ∧
      ¬ (forallCheck deadL b1L = true ↔ Subset deadL b1L) :=
  ⟨deadL_fixedSize, b1L_fixedSize, by decide, ex_not_reachableLive,
    fun h => absurd (h.mpr deadL_subset_b1L) (by decide)⟩

/-- Both truth values occur under all hypotheses: `b0L → boolL` (accepted, included) and
`boolL → b0L` (rejected, not included). -/
theorem forallCheck_iff_subset_nonvacuous :
    (b0L.FixedSize 1 ∧ boolL.FixedSize 1 ∧ boolL.Deterministic ∧ b0L.ReachableLive ∧
      forallCheck b0L boolL = true ∧ Subset b0L boolL) ∧
    (boolL.FixedSize 1 ∧ b0L.FixedSize 1 ∧ b0L.Deterministic ∧ boolL.ReachableLive ∧
      forallCheck boolL b0L = false ∧ ¬ Subset boolL b0L) :=
  ⟨⟨b0L_fixedSize, boolL_fixedSize, by decide, b0L_live, by decide,
      forall_lang_of_wordsFrom b0L_fixedSize (by decide)⟩,
    ⟨boolL_fixedSize, b0L_fixedSize, by decide, boolL_live, by decide,
      fun h => absurd (h [Sym.byte 1] (by decide)) (by decide)⟩⟩

end Toy.LayoutDfa
