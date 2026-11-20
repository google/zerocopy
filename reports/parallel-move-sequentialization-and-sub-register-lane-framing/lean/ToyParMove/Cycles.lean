import ToyParMove.Necessity

/-!
Cycles. A `k`-cycle is realized by `k + 1` plain moves through one scratch location and needs
at least that many; it is realized by `k - 1` swaps and needs at least that many; and for
`k ≥ 2` no sequence of plain moves realizes it exactly (with no location allowed to be
clobbered), either from a given injective store or uniformly for all stores over a value type
with two distinct values.
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

section CycleDefs
variable {Loc : Type} [DecidableEq Loc]

/-- `chain h [y₁, …, yₙ]` is the move list `[(y₁, h), (y₂, y₁), …, (yₙ, yₙ₋₁)]`: each `yᵢ`
receives the old value of its predecessor. -/
def chain : Loc → List Loc → List (Loc × Loc)
  | _, [] => []
  | h, y :: ys => (y, h) :: chain y ys

/-- **The `k`-cycle** on the duplicate-free list `[l₀, l₁, …, lₖ₋₁]`: each `lᵢ₊₁` receives the
old value of `lᵢ`, and `l₀` receives the old value of `lₖ₋₁`. For `k = 1` it is the self-move
`[(l₀, l₀)]`. Captures a cyclic register shuffle. -/
def cycleMoves : List Loc → List (Loc × Loc)
  | [] => []
  | l₀ :: rest => (l₀, rest.getLastD l₀) :: chain l₀ rest

/-- The standard realization of a cycle through a scratch location:
`tmp := lₖ₋₁; lₖ₋₁ := lₖ₋₂; …; l₁ := l₀; l₀ := tmp` (`k + 1` moves). -/
def cycleSeqScratch (tmp : Loc) : List Loc → List (Loc × Loc)
  | [] => []
  | l₀ :: rest => (tmp, rest.getLastD l₀) :: (chain l₀ rest).reverse ++ [(l₀, tmp)]

end CycleDefs

/-! ### Facts about `chain` and `cycleMoves` -/

section CycleFacts
variable {Loc V : Type} [DecidableEq Loc]

theorem dsts_chain : ∀ (h : Loc) (ys : List Loc), dsts (chain h ys) = ys
  | _, [] => rfl
  | h, y :: ys => by simp [chain, dsts_chain y ys]

theorem length_chain (h : Loc) (ys : List Loc) : (chain h ys).length = ys.length := by
  rw [← length_dsts, dsts_chain]

theorem srcs_chain_subset : ∀ (h : Loc) (ys : List Loc), srcs (chain h ys) ⊆ h :: ys
  | _, [] => by simp [chain]
  | h, y :: ys => by
    intro x hx
    simp only [chain, srcs_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem _ (srcs_chain_subset y ys hx)

/-- Every element of `h :: ys` is a source of `chain h ys`, except possibly the last one. -/
theorem mem_srcs_chain_or_last : ∀ (h : Loc) (ys : List Loc) (x : Loc), x ∈ h :: ys →
    x ∈ srcs (chain h ys) ∨ x = ys.getLastD h
  | h, [], x, hx => Or.inr (by simpa using hx)
  | h, y :: ys, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl (by simp [chain])
    · rcases mem_srcs_chain_or_last y ys x hx with h' | h'
      · exact Or.inl (by simp [chain, h'])
      · exact Or.inr (by rw [List.getLastD_cons]; exact h')

theorem chain_no_self : ∀ (h : Loc) (ys : List Loc), (h :: ys).Nodup →
    ∀ m ∈ chain h ys, m.1 ≠ m.2
  | _, [], _ => by simp [chain]
  | h, y :: ys, hn => by
    intro m hm
    have hn' := List.nodup_cons.1 hn
    simp only [chain, List.mem_cons] at hm
    rcases hm with rfl | hm
    · intro e
      have e' : y = h := e
      exact hn'.1 (by rw [← e']; exact List.mem_cons_self ..)
    · exact chain_no_self y ys hn'.2 m hm

/-- The chain read backwards is a topological emission order. -/
theorem topological_chain_reverse : ∀ (h : Loc) (ys : List Loc), (h :: ys).Nodup →
    Topological (chain h ys).reverse
  | _, [], _ => by simp [chain, Topological]
  | h, y :: ys, hn => by
    have hn' := List.nodup_cons.1 hn
    unfold Topological
    rw [List.pairwise_reverse]
    simp only [chain, List.pairwise_cons]
    refine ⟨fun b hb e => ?_, ?_⟩
    · have : b.1 ∈ ys := by rw [← dsts_chain y ys]; exact mem_dsts.2 ⟨b.2, hb⟩
      exact hn'.1 (List.mem_cons_of_mem _ (e ▸ this))
    · have := topological_chain_reverse y ys hn'.2
      unfold Topological at this
      rwa [List.pairwise_reverse] at this

theorem getLastD_mem_of_ne_nil {ys : List Loc} (h : ys ≠ []) (a : Loc) : ys.getLastD a ∈ ys := by
  cases ys with
  | nil => exact absurd rfl h
  | cons y ys => rw [List.getLastD_cons]; exact List.getLastD_mem_cons

theorem dsts_cycleMoves (ls : List Loc) : dsts (cycleMoves ls) = ls := by
  cases ls with
  | nil => rfl
  | cons l₀ rest => simp [cycleMoves, dsts_chain]

theorem wellFormed_cycleMoves {ls : List Loc} (hn : ls.Nodup) : WellFormed (cycleMoves ls) := by
  unfold WellFormed; rw [dsts_cycleMoves]; exact hn

theorem srcs_cycleMoves_subset (ls : List Loc) : srcs (cycleMoves ls) ⊆ ls := by
  cases ls with
  | nil => simp [cycleMoves]
  | cons l₀ rest =>
    intro x hx
    simp only [cycleMoves, srcs_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.getLastD_mem_cons
    · exact srcs_chain_subset l₀ rest hx

theorem mem_srcs_cycleMoves {ls : List Loc} {x : Loc} (hx : x ∈ ls) : x ∈ srcs (cycleMoves ls) := by
  cases ls with
  | nil => simp at hx
  | cons l₀ rest =>
    rcases mem_srcs_chain_or_last l₀ rest x hx with h | h
    · simp [cycleMoves, h]
    · simp [cycleMoves, h]

theorem cycleMoves_no_self {ls : List Loc} (hn : ls.Nodup) (hk : 2 ≤ ls.length) :
    ∀ m ∈ cycleMoves ls, m.1 ≠ m.2 := by
  cases ls with
  | nil => simp at hk
  | cons l₀ rest =>
    intro m hm
    simp only [cycleMoves, List.mem_cons] at hm
    rcases hm with rfl | hm
    · have hne : rest ≠ [] := by intro e; subst e; simp at hk
      intro e
      have e' : l₀ = rest.getLastD l₀ := e
      have hm := getLastD_mem_of_ne_nil hne l₀
      rw [← e'] at hm
      exact (List.nodup_cons.1 hn).1 hm
    · exact chain_no_self l₀ rest hn m hm

/-- In the target of a `k`-cycle (`k ≥ 2`), every location of the cycle changes value (at an
injective store) and every old value is still needed somewhere. -/
theorem pmove_cycle_facts {ls : List Loc} (hn : ls.Nodup) (hk : 2 ≤ ls.length) {σ : Loc → V}
    (hσ : Function.Injective σ) :
    (∀ l ∈ ls, pmove (cycleMoves ls) σ l ≠ σ l) ∧
    (∀ l ∉ ls, pmove (cycleMoves ls) σ l = σ l) ∧
    (∀ l ∈ ls, ∃ d ∈ ls, pmove (cycleMoves ls) σ d = σ l) := by
  have hF := functional_of_wellFormed (wellFormed_cycleMoves hn)
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [← dsts_cycleMoves ls] at hl
    obtain ⟨s, hs⟩ := mem_dsts.1 hl
    rw [pmove_of_mem hF hs]
    exact fun e => cycleMoves_no_self hn hk _ hs (hσ e).symm
  · exact pmove_of_not_mem_dsts (by rw [dsts_cycleMoves]; exact hl) σ
  · obtain ⟨d, hd⟩ := mem_srcs.1 (mem_srcs_cycleMoves hl)
    refine ⟨d, ?_, pmove_of_mem hF hd σ⟩
    rw [← dsts_cycleMoves ls]; exact mem_dsts.2 ⟨l, hd⟩

end CycleFacts

/-! ### Upper bound with one scratch location: `k + 1` moves -/

section ScratchUpper
variable {Loc V : Type} [DecidableEq Loc]

theorem length_cycleSeqScratch (tmp l₀ : Loc) (rest : List Loc) :
    (cycleSeqScratch tmp (l₀ :: rest)).length = (l₀ :: rest).length + 1 := by
  simp [cycleSeqScratch, length_chain]

/-- **Cycle through one scratch location.** For a duplicate-free cycle `l₀ :: rest` and a
scratch location `tmp` outside it, the `k + 1` moves of `cycleSeqScratch` realize the cycle at
every location other than `tmp`, from every store. -/
theorem runSeq_cycleSeqScratch {l₀ : Loc} {rest : List Loc} {tmp : Loc}
    (hn : (l₀ :: rest).Nodup) (htmp : tmp ∉ l₀ :: rest) (σ : Loc → V) :
    ∀ l, l ≠ tmp →
      runSeq (cycleSeqScratch tmp (l₀ :: rest)) σ l = pmove (cycleMoves (l₀ :: rest)) σ l := by
  intro l hl
  have hFc := functional_of_wellFormed (wellFormed_cycleMoves hn)
  have hn' := List.nodup_cons.1 hn
  have hFch : Functional (chain l₀ rest) := functional_of_wellFormed (by
    unfold WellFormed; rw [dsts_chain]; exact hn'.2)
  have hlast : rest.getLastD l₀ ≠ tmp := fun e => htmp (e ▸ List.getLastD_mem_cons)
  have hσ2 : runSeq (chain l₀ rest).reverse (seqStep σ (tmp, rest.getLastD l₀)) =
      pmove (chain l₀ rest) (seqStep σ (tmp, rest.getLastD l₀)) := by
    rw [runSeq_eq_pmove_of_topological (functional_of_perm hFch (List.reverse_perm _).symm)
      (topological_chain_reverse l₀ rest hn)]
    exact (pmove_perm_invariant_of_functional hFch (List.reverse_perm _).symm _).symm
  simp only [cycleSeqScratch, runSeq_cons, runSeq_append, hσ2, runSeq_nil]
  have htd : tmp ∉ dsts (chain l₀ rest) := by
    rw [dsts_chain]; exact fun h => htmp (List.mem_cons_of_mem _ h)
  by_cases hl0 : l = l₀
  · subst hl0
    rw [pmove_of_mem hFc (show (l, rest.getLastD l) ∈ cycleMoves (l :: rest) by simp [cycleMoves])]
    simp only [seqStep, upd_same]
    rw [pmove_of_not_mem_dsts htd]
    simp [upd]
  · simp only [seqStep, upd, hl0, ite_false]
    by_cases hlc : l ∈ dsts (chain l₀ rest)
    · obtain ⟨s, hs⟩ := mem_dsts.1 hlc
      have hst : s ≠ tmp := fun e => htmp (e ▸ srcs_chain_subset l₀ rest (mem_srcs.2 ⟨l, hs⟩))
      rw [pmove_of_mem hFch hs, upd_ne _ _ hst,
        pmove_of_mem hFc (show (l, s) ∈ cycleMoves (l₀ :: rest) from List.mem_cons_of_mem _ hs)]
    · rw [pmove_of_not_mem_dsts hlc, upd_ne _ _ hl, pmove_of_not_mem_dsts]
      rw [dsts_cycleMoves]
      rw [dsts_chain] at hlc
      simp [hl0, hlc]

end ScratchUpper

/-! ### Values only travel: the value-loss argument -/

section ValueLoss
variable {Loc V : Type} [DecidableEq Loc]

/-- After any plain move sequence, every location holds some original value. -/
theorem runSeq_mem_image : ∀ (ms : List (Loc × Loc)) (τ : Loc → V) (l : Loc),
    ∃ l', runSeq ms τ l = τ l'
  | [], τ, l => ⟨l, rfl⟩
  | m :: ms, τ, l => by
    obtain ⟨l', h⟩ := runSeq_mem_image ms (seqStep τ m) l
    refine ⟨if l' = m.1 then m.2 else l', ?_⟩
    rw [runSeq_cons, h]
    by_cases e : l' = m.1 <;> simp [seqStep, upd, e]

theorem runSeq_of_not_mem_dsts : ∀ {ms : List (Loc × Loc)} {l : Loc}, l ∉ dsts ms →
    ∀ τ : Loc → V, runSeq ms τ l = τ l
  | [], _, _, _ => rfl
  | m :: ms, l, h, τ => by
    have hl : l ≠ m.1 := fun e => h (by simp [e])
    rw [runSeq_cons, runSeq_of_not_mem_dsts (fun h' => h (by simp [h'])) _]
    simp [seqStep, upd, hl]

theorem seqStep_eq_self {σ : Loc → V} {m : Loc × Loc} (h : σ m.2 = σ m.1) : seqStep σ m = σ := by
  funext l
  by_cases e : l = m.1
  · subst e; simp [seqStep, h]
  · simp [seqStep, upd, e]

/-- The first move that changes an injective store destroys the old value of its destination
for good. -/
theorem runSeq_ne_destroyed {σ : Loc → V} (hσ : Function.Injective σ) {m : Loc × Loc}
    (h : σ m.2 ≠ σ m.1) (ms : List (Loc × Loc)) (l : Loc) :
    runSeq ms (seqStep σ m) l ≠ σ m.1 := by
  obtain ⟨l', e⟩ := runSeq_mem_image ms (seqStep σ m) l
  rw [e]
  by_cases hl' : l' = m.1
  · subst hl'; simpa [seqStep] using h
  · simp only [seqStep, upd, hl', ite_false]
    exact fun e' => hl' (hσ e')

/-- **No exact realization without scratch (general form).** If `σ` is injective, the target
store `T` differs from `σ`, and every old value `σ l` still occurs somewhere in `T`, then no
sequence of plain moves turns `σ` into `T`. -/
theorem runSeq_ne_of_injective_of_values_needed {σ T : Loc → V} (hσ : Function.Injective σ)
    (hneed : ∀ l, ∃ l', T l' = σ l) (hT : T ≠ σ) :
    ∀ ms : List (Loc × Loc), runSeq ms σ ≠ T
  | [] => fun h => hT h.symm
  | m :: ms => by
    by_cases h : σ m.2 = σ m.1
    · rw [runSeq_cons, seqStep_eq_self h]
      exact runSeq_ne_of_injective_of_values_needed hσ hneed hT ms
    · intro e
      obtain ⟨l', hl'⟩ := hneed m.1
      rw [runSeq_cons] at e
      exact runSeq_ne_destroyed hσ h ms l' (by rw [e, hl'])

/-- Value-loss with one scratch location: if the target off `tmp` needs every old value except
possibly that of `tmp`, and the store changes somewhere, then some move writes `tmp`. -/
theorem exists_move_to_tmp {σ T : Loc → V} {tmp : Loc} (hσ : Function.Injective σ)
    (hneed : ∀ l, l ≠ tmp → ∃ l', l' ≠ tmp ∧ T l' = σ l) :
    ∀ ms : List (Loc × Loc), (∀ l, l ≠ tmp → runSeq ms σ l = T l) →
      (∃ l, runSeq ms σ l ≠ σ l) → ∃ s, (tmp, s) ∈ ms
  | [], _, ⟨l, hl⟩ => absurd rfl hl
  | m :: ms, hreal, hchg => by
    by_cases h : σ m.2 = σ m.1
    · rw [runSeq_cons, seqStep_eq_self h] at hreal hchg
      obtain ⟨s, hs⟩ := exists_move_to_tmp hσ hneed ms hreal hchg
      exact ⟨s, List.mem_cons_of_mem _ hs⟩
    · by_cases hm : m.1 = tmp
      · exact ⟨m.2, by rw [← hm]; simp⟩
      · exfalso
        obtain ⟨l', hl't, hl'⟩ := hneed m.1 hm
        have := hreal l' hl't
        rw [runSeq_cons] at this
        exact runSeq_ne_destroyed hσ h ms l' (by rw [this, hl'])

/-- Lower bound (general form): if `ms` realizes `T` off `tmp` from an injective store, every
old value other than that of `tmp` is needed off `tmp`, and the duplicate-free nonempty list
`ch` of locations other than `tmp` all change, then `ms` has at least `ch.length + 1` moves. -/
theorem length_ge_of_realizes_off_tmp {σ T : Loc → V} {tmp : Loc} {ms : List (Loc × Loc)}
    (hσ : Function.Injective σ) (hneed : ∀ l, l ≠ tmp → ∃ l', l' ≠ tmp ∧ T l' = σ l)
    (hreal : ∀ l, l ≠ tmp → runSeq ms σ l = T l) {ch : List Loc} (hch : ch.Nodup)
    (htmp : tmp ∉ ch) (hchg : ∀ l ∈ ch, T l ≠ σ l) (hne : ch ≠ []) :
    ch.length + 1 ≤ ms.length := by
  have hlt : tmp ∉ ch := htmp
  have hwritten : ∀ l ∈ ch, l ∈ dsts ms := by
    intro l hl
    apply Classical.byContradiction
    intro h
    have hlt' : l ≠ tmp := fun e => hlt (e ▸ hl)
    exact hchg l hl ((hreal l hlt').symm.trans (runSeq_of_not_mem_dsts h σ))
  obtain ⟨l₀, hl₀⟩ : ∃ l, l ∈ ch := by
    cases ch with
    | nil => exact absurd rfl hne
    | cons a _ => exact ⟨a, List.mem_cons_self ..⟩
  have hl₀t : l₀ ≠ tmp := fun e => hlt (e ▸ hl₀)
  obtain ⟨s, hs⟩ := exists_move_to_tmp hσ hneed ms hreal
    ⟨l₀, by rw [hreal l₀ hl₀t]; exact hchg l₀ hl₀⟩
  let p : Loc × Loc → Bool := fun m => decide (m.1 ≠ tmp)
  have hsub : ch ⊆ dsts (ms.filter p) := by
    intro l hl
    obtain ⟨s', hs'⟩ := mem_dsts.1 (hwritten l hl)
    have hlt' : l ≠ tmp := fun e => hlt (e ▸ hl)
    exact mem_dsts.2 ⟨s', List.mem_filter.2 ⟨hs', by simp [p, hlt']⟩⟩
  have h1 := length_le_of_nodup_of_subset hch hsub
  rw [length_dsts] at h1
  have h2 : (ms.filter p).length < ms.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨(tmp, s), hs, by simp [p]⟩
  omega

end ValueLoss

/-! ### Lower bound and impossibility for plain moves -/

section CyclePlain
variable {Loc V : Type} [DecidableEq Loc]

/-- **Lower bound with one scratch location: `k + 1` moves.** Let `ls` be a duplicate-free
cycle of length `k ≥ 2` and `tmp ∉ ls`. Any plain move sequence that, from an injective store
`σ`, produces the cycle's target at every location other than `tmp` has at least `k + 1`
moves. -/
theorem cycle_length_add_one_le_of_injective_of_realizes_off_tmp {ls : List Loc} {tmp : Loc}
    {σ : Loc → V} {ms : List (Loc × Loc)} (hn : ls.Nodup) (hk : 2 ≤ ls.length) (htmp : tmp ∉ ls)
    (hσ : Function.Injective σ)
    (hreal : ∀ l, l ≠ tmp → runSeq ms σ l = pmove (cycleMoves ls) σ l) :
    ls.length + 1 ≤ ms.length := by
  obtain ⟨hchg, hfix, hneed⟩ := pmove_cycle_facts hn hk hσ
  refine length_ge_of_realizes_off_tmp hσ ?_ hreal hn htmp hchg ?_
  · intro l hl
    by_cases hls : l ∈ ls
    · obtain ⟨d, hd, e⟩ := hneed l hls
      exact ⟨d, fun h => htmp (h ▸ hd), e⟩
    · exact ⟨l, hl, hfix l hls⟩
  · intro e; subst e; simp at hk

/-- **Impossibility without scratch.** For a duplicate-free cycle of length `k ≥ 2` and an
injective store `σ`, no sequence of plain moves (over any locations) produces exactly the
cycle's target at every location. -/
theorem runSeq_ne_pmove_cycle_of_injective {ls : List Loc} {σ : Loc → V} (hn : ls.Nodup)
    (hk : 2 ≤ ls.length) (hσ : Function.Injective σ) :
    ∀ ms : List (Loc × Loc), runSeq ms σ ≠ pmove (cycleMoves ls) σ := by
  obtain ⟨hchg, hfix, hneed⟩ := pmove_cycle_facts hn hk hσ
  apply runSeq_ne_of_injective_of_values_needed hσ
  · intro l
    by_cases hls : l ∈ ls
    · obtain ⟨d, _, e⟩ := hneed l hls
      exact ⟨d, e⟩
    · exact ⟨l, hfix l hls⟩
  · intro e
    obtain ⟨l₀, hl₀⟩ : ∃ l, l ∈ ls := by
      cases ls with
      | nil => simp at hk
      | cons a _ => exact ⟨a, List.mem_cons_self ..⟩
    exact hchg l₀ hl₀ (congrFun e l₀)

/-- The two-location case (a parallel swap): for `a ≠ b` and an injective store, no sequence of
plain moves realizes `[(a,b),(b,a)]` exactly. -/
theorem runSeq_ne_pmove_swap_of_injective {a b : Loc} {σ : Loc → V} (hab : a ≠ b)
    (hσ : Function.Injective σ) : ∀ ms : List (Loc × Loc), runSeq ms σ ≠ pmove [(a, b), (b, a)] σ :=
  runSeq_ne_pmove_cycle_of_injective (ls := [a, b]) (by simp [hab]) (by simp) hσ

/-- **No topological order for a cycle.** No reordering of the moves of a duplicate-free cycle of
length `k ≥ 2` is topological. -/
theorem not_topological_of_perm_cycleMoves {ls : List Loc} {ms : List (Loc × Loc)}
    (hn : ls.Nodup) (hk : 2 ≤ ls.length) (hp : ms.Perm (cycleMoves ls)) : ¬ Topological ms := by
  have hF := functional_of_wellFormed (wellFormed_cycleMoves hn)
  refine not_topological_of_dsts_read (C := cycleMoves ls) ?_ (fun m hm => hp.mem_iff.2 hm) ?_
  · intro e
    have := congrArg List.length (dsts_cycleMoves ls)
    rw [e] at this
    simp at this
    omega
  · intro m hm
    have hm1 : m.1 ∈ ls := by rw [← dsts_cycleMoves ls]; exact mem_dsts.2 ⟨m.2, hm⟩
    obtain ⟨d, hd⟩ := mem_srcs.1 (mem_srcs_cycleMoves hm1)
    refine ⟨(d, m.1), hd, fun e => ?_, rfl⟩
    have h2 : m.1 = m.2 := congrArg Prod.snd e
    exact cycleMoves_no_self hn hk m hm h2

/-- **Impossibility without scratch, uniformly in the store.** Over any location type and any
value type with two distinct values, for a duplicate-free cycle of length `k ≥ 2` no single
sequence of plain moves turns every store into the cycle's target. Unlike
`runSeq_ne_pmove_cycle_of_injective`, no injective store is needed, so the statement is not
vacuous when the location type is larger than the value type. -/
theorem runSeq_ne_pmove_cycle_of_two_values {ls : List Loc} (a b : V) (hab : a ≠ b)
    (hn : ls.Nodup) (hk : 2 ≤ ls.length) :
    ¬ ∃ ms : List (Loc × Loc), ∀ σ : Loc → V, runSeq ms σ = pmove (cycleMoves ls) σ := by
  rintro ⟨ms, hms⟩
  apply runSeq_ne_pmove_cycle_of_injective (V := Loc) (σ := id) hn hk (fun _ _ h => h) ms
  funext l
  exact runSeq_eq_pmove_at_id_of_forall a b hab (fun σ => congrFun (hms σ) l)

/-- **Lower bound with one scratch location, uniformly in the store.** Over a value type with two
distinct values, any plain move sequence that produces a duplicate-free cycle of length `k ≥ 2`
at every location other than `tmp ∉ ls`, from every store, has at least `k + 1` moves. -/
theorem cycle_length_add_one_le_of_two_values_of_realizes_off_tmp {ls : List Loc} {tmp : Loc}
    {ms : List (Loc × Loc)} (a b : V) (hab : a ≠ b) (hn : ls.Nodup) (hk : 2 ≤ ls.length)
    (htmp : tmp ∉ ls)
    (hreal : ∀ σ : Loc → V, ∀ l, l ≠ tmp → runSeq ms σ l = pmove (cycleMoves ls) σ l) :
    ls.length + 1 ≤ ms.length :=
  cycle_length_add_one_le_of_injective_of_realizes_off_tmp (V := Loc) (σ := id) hn hk htmp
    (fun _ _ h => h) (fun l hl => runSeq_eq_pmove_at_id_of_forall a b hab (fun σ => hreal σ l hl))

end CyclePlain

/-- Non-claim witness: over `Nat` locations and `Bool` values no store is injective, so the
injective-store statements are vacuous there; the uniform statements still apply. -/
theorem no_injective_store_nat_bool : ∀ σ : Nat → Bool, ¬ Function.Injective σ := by
  intro σ h
  have h01 : σ 0 ≠ σ 1 := fun e => absurd (h e) (by decide)
  have h02 : σ 0 ≠ σ 2 := fun e => absurd (h e) (by decide)
  have h12 : σ 1 ≠ σ 2 := fun e => absurd (h e) (by decide)
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;> simp_all

/-! ### Definition examples (`cycleMoves`, `cycleSeqScratch`) -/

/-- Positive example (`cycleMoves`): the 3-cycle on `[0,1,2]` and its direction (location `1`
receives the old value of `0`, not of `2`). -/
theorem cycleMoves_example :
    cycleMoves ([0, 1, 2] : List Nat) = [(0, 2), (1, 0), (2, 1)] ∧
    pmove (cycleMoves ([0, 1, 2] : List Nat)) (id : Nat → Nat) 1 = 0 ∧
    pmove (cycleMoves ([0, 1, 2] : List Nat)) (id : Nat → Nat) 1 ≠ 2 := by decide

/-- Negative example (`cycleMoves`): a list with a repeated location does not give a cycle in
which every listed location changes (location `0` keeps its value). -/
theorem cycleMoves_repeated_not_cycle :
    pmove (cycleMoves ([0, 1, 0] : List Nat)) (id : Nat → Nat) 0 = 0 := by decide

/-- Positive example (`cycleSeqScratch`): the 4-move scratch realization of the 3-cycle. -/
theorem cycleSeqScratch_example :
    cycleSeqScratch (9 : Nat) [0, 1, 2] = [(9, 2), (2, 1), (1, 0), (0, 9)] := by decide

end Toy.ParMove
