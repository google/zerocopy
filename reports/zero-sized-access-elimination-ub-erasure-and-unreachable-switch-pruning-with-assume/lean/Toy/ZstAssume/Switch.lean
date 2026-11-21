import Toy.ZstAssume.ZeroSize

/-!
# Unreachable switch arms: pruning with and without `assume`, and UB-derived facts

Pruning a switch arm whose target is an unreachable block, with an inserted `assume`
(equivalence) and without it (refinement; exact and sufficient conditions for
equivalence); weakest preconditions; and the transfer of facts that hold on the runs
that never reach UB.
-/

namespace Toy.ZstAssume

/-! ### Pruning with `assume` -/

/-- **Pruning an unreachable arm with `assume` is an equivalence.** If block `l` ends in
`switch x arms ow` and the label selected for value `v` is an unreachable block, then
removing the arms with value `v` and inserting `assume (x ≠ v)` before the switch is a
prefix-preserving equivalence. -/
theorem pruneArmAssume_equivPP (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivPP K P (pruneArmAssume P l v) := by
  exact paa_equivPP hterm hU

/-- Whole-trace version of `pruneArmAssume_equivPP` (a corollary through
`equivWT_of_equivPP`). -/
theorem pruneArmAssume_equivWT (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivWT K P (pruneArmAssume P l v) :=
  equivWT_of_equivPP (pruneArmAssume_equivPP K P l x arms ow v hterm hU)

/-- **Pruning with `assume` preserves the weakest precondition.** Under the hypotheses
of `pruneArmAssume_equivPP`, for every postcondition `Q` on trace and final state and
every input, `wp` of the target and of the source coincide. -/
theorem pruneArmAssume_wp_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v))
    (Q : List Int → State → Prop) (σ : State) :
    wp K (pruneArmAssume P l v) Q σ ↔ wp K P Q σ := by
  exact paa_wp_iff hterm hU Q σ

/-- **Single remaining arm, unreachable `otherwise`.** If block `l` ends in
`switch x [(v, b)] ow` and `ow` is an unreachable block, replacing the switch by
`assume (x = v); goto b` is a prefix-preserving equivalence. -/
theorem pruneOtherwiseAssume_equivPP (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (v : Int) (b ow : Label) (hterm : (P.blk l).term = .switch x [(v, b)] ow)
    (hU : IsUnreachableBlock P ow) :
    EquivPP K P (pruneOtherwiseAssume P l) := by
  exact poa_equivPP hterm hU

/-- **`wp` for the single-arm shape.** Under the hypotheses of
`pruneOtherwiseAssume_equivPP`, `wp` of target and source coincide. -/
theorem pruneOtherwiseAssume_wp_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (v : Int) (b ow : Label) (hterm : (P.blk l).term = .switch x [(v, b)] ow)
    (hU : IsUnreachableBlock P ow) (Q : List Int → State → Prop) (σ : State) :
    wp K (pruneOtherwiseAssume P l) Q σ ↔ wp K P Q σ := by
  exact poa_wp_iff hterm hU Q σ

/-! #### Pruning with `assume`: instances and tightness (fully proved) -/

/-- Switch on local `0`: value `5` goes to the unreachable block `1`, otherwise to
block `2`, which halts. -/
def pSw : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, Block.unreach, ⟨[], .halt⟩]

theorem pSw_hyps : (pSw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
    IsUnreachableBlock pSw (selectTarget [(5, 1)] 2 5) := by decide

theorem pruneArmAssume_pSw : pruneArmAssume pSw 0 5 =
    [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, Block.unreach, ⟨[], .halt⟩] := by decide

/-- Direct check of `pruneArmAssume_equivPP` and `pruneArmAssume_wp_iff` on `pSw`
(non-vacuity witness with the conclusion proved independently). -/
theorem pruneArmAssume_pSw_equivPP_and_wp (K : ZContract) :
    EquivPP K pSw (pruneArmAssume pSw 0 5) ∧
      ∀ Q σ, wp K (pruneArmAssume pSw 0 5) Q σ ↔ wp K pSw Q σ := by
  rw [pruneArmAssume_pSw]
  refine ⟨equivPP_of_sameBeh fun σ b => ?_, fun Q σ => ?_⟩
  · by_cases h : σ.locals 0 = 5
    · exact hasBeh_iff_of_runs_ub (n := 2) (m := 1) (t := []) (by simp_run [pSw, h])
        (by simp_run [h]) b
    · exact hasBeh_iff_of_runs_done (n := 3) (m := 3) (t := []) (s := σ) (s' := σ) (by simp_run [pSw, h])
        (by simp_run [h]) b
  · by_cases h : σ.locals 0 = 5
    · constructor
      · rintro ⟨n, t, s, hn, _⟩
        have := (hasBehFrom_iff_of_run_ub (n := 1) (t := []) (P := [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩,
          Block.unreach, ⟨[], .halt⟩]) (by simp_run [h]) (.term t)).1 ⟨n, s, hn⟩
        cases this
      · rintro ⟨n, t, s, hn, _⟩
        have := (hasBehFrom_iff_of_run_ub (n := 2) (t := []) (P := pSw) (by simp_run [pSw, h])
          (.term t)).1 ⟨n, s, hn⟩
        cases this
    · constructor
      · rintro ⟨n, t, s, hn, hq⟩
        have h₁ : run K [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, Block.unreach, ⟨[], .halt⟩] 3
            (Prog.init [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, Block.unreach, ⟨[], .halt⟩] σ) =
            .done [] σ := by simp_run [h]
        have e := run_done_mono hn (Nat.le_max_left n 3)
        rw [run_done_mono h₁ (Nat.le_max_right n 3)] at e
        cases e
        exact ⟨3, [], σ, by simp_run [pSw, h], hq⟩
      · rintro ⟨n, t, s, hn, hq⟩
        have h₁ : run K pSw 3 (pSw.init σ) = .done [] σ := by simp_run [pSw, h]
        have e := run_done_mono hn (Nat.le_max_left n 3)
        rw [run_done_mono h₁ (Nat.le_max_right n 3)] at e
        cases e
        exact ⟨3, [], σ, by simp_run [h], hq⟩

/-- Switch on local `0`: value `5` goes to block `1`, which emits `7` and then is
unreachable; otherwise block `2` halts. Block `1` is *not* an unreachable block. -/
def pSwEmitUnreach : Prog :=
  [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 7)], .unreachable⟩, ⟨[], .halt⟩]

/-- **Tightness of "the pruned target is an unreachable block" (prefix-preserving).**
Block `0` of `pSwEmitUnreach` ends in `switch 0 [(5, 1)] 2`, and the arm for `5` leads
to a block that emits before `unreachable` (so it is not an unreachable block). Pruning
it with `assume` is not a prefix-preserving refinement (the event `7` is lost before
the UB), although it is a whole-trace refinement. -/
theorem pruneArmAssume_emit_before_unreachable_not_refinesPP (K : ZContract) :
    (pSwEmitUnreach.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwEmitUnreach (selectTarget [(5, 1)] 2 5) ∧
      ¬ RefinesPP K pSwEmitUnreach (pruneArmAssume pSwEmitUnreach 0 5) ∧
      RefinesWT K pSwEmitUnreach (pruneArmAssume pSwEmitUnreach 0 5) := by
  have hp : pruneArmAssume pSwEmitUnreach 0 5 =
      [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, ⟨[.emit (.const 7)], .unreachable⟩,
        ⟨[], .halt⟩] := by decide
  rw [hp]
  refine ⟨by decide, by decide, fun h => ?_, fun σ bt hbt => ?_⟩
  · have hw : HasBeh K [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩,
        ⟨[.emit (.const 7)], .unreachable⟩, ⟨[], .halt⟩] (mkState [5]) (.wrong []) := ⟨1, rfl⟩
    obtain ⟨bs, hbs, himp⟩ := h _ _ hw
    have := (hasBehFrom_iff_of_run_ub (n := 3) (P := pSwEmitUnreach) rfl bs).1 hbs
    subst this
    rcases himp with h' | ⟨t, ht, hp⟩
    · cases h'
    · cases ht
      simp [Beh.HasPrefix] at hp
  · by_cases h : σ.locals 0 = 5
    · have := (hasBehFrom_iff_of_run_ub (n := 1) (t := []) (P := [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩,
        ⟨[.emit (.const 7)], .unreachable⟩, ⟨[], .halt⟩]) (by simp_run [h]) bt).1 hbt
      subst this
      exact ⟨.wrong [7], ⟨3, by simp_run [pSwEmitUnreach, h]⟩, Or.inr ⟨[7], rfl⟩⟩
    · have := (hasBehFrom_iff_of_run_done (n := 3) (t := []) (s := σ) (P := [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩,
        ⟨[.emit (.const 7)], .unreachable⟩, ⟨[], .halt⟩]) (by simp_run [h]) bt).1 hbt
      subst this
      exact ⟨.term [], ⟨3, σ, by simp_run [pSwEmitUnreach, h]⟩, Or.inl rfl⟩

/-- Switch on local `0`: value `5` goes to block `1`, which emits `1` and halts;
otherwise block `2` halts. -/
def pSwLive : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩]

/-- **Tightness of the unreachable-target hypothesis (both shapes of pruning).** When
the arm for `5` is live, pruning it with `assume` introduces UB and pruning it without
`assume` changes the trace; neither is a whole-trace refinement. -/
theorem pruneArm_live_arm_not_refinesWT (K : ZContract) :
    ¬ IsUnreachableBlock pSwLive (selectTarget [(5, 1)] 2 5) ∧
      ¬ RefinesWT K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ RefinesWT K pSwLive (pruneArm pSwLive 0 5) := by
  have ht : HasBeh K pSwLive (mkState [5]) (.term [1]) := ⟨3, _, rfl⟩
  refine ⟨by decide, ?_, ?_⟩
  · have hp : pruneArmAssume pSwLive 0 5 =
        [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩] := by
      decide
    rw [hp]
    exact not_refinesWT_of_term_wrong ht ⟨1, rfl⟩
  · have hp : pruneArm pSwLive 0 5 =
        [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩] := by decide
    rw [hp]
    exact not_refinesWT_of_term_term ht ⟨2, _, rfl⟩ (by decide)

/-- **The unreachable-target hypothesis is needed for the `wp` results.** With the live
arm of `pSwLive`, on local `0 = 5`: the source satisfies `wp` for `True` but pruning with
`assume` does not; and the source satisfies `wp` for "the trace is `[1]`" but pruning
without `assume` does not. -/
theorem pruneArm_live_arm_wp_not_transferred (K : ZContract) :
    ¬ IsUnreachableBlock pSwLive (selectTarget [(5, 1)] 2 5) ∧
      wp K pSwLive (fun _ _ => True) (mkState [5]) ∧
      ¬ wp K (pruneArmAssume pSwLive 0 5) (fun _ _ => True) (mkState [5]) ∧
      wp K pSwLive (fun t _ => t = [1]) (mkState [5]) ∧
      ¬ wp K (pruneArm pSwLive 0 5) (fun t _ => t = [1]) (mkState [5]) := by
  have hpa : pruneArmAssume pSwLive 0 5 =
      [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩] := by
    decide
  have hp : pruneArm pSwLive 0 5 =
      [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩] := by decide
  rw [hpa, hp]
  refine ⟨by decide, ⟨3, [1], _, rfl, trivial⟩, ?_, ⟨3, [1], _, rfl, rfl⟩, ?_⟩
  · rintro ⟨n, t, s, hn, _⟩
    have := (hasBehFrom_iff_of_run_ub (n := 1) (t := [])
      (P := [⟨[.assume (.ne 0 5)], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩])
      rfl (.term t)).1 ⟨n, s, hn⟩
    cases this
  · rintro ⟨n, t, s, hn, ht⟩
    have := (hasBehFrom_iff_of_run_done (n := 2) (t := []) (s := mkState [5])
      (P := [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩])
      rfl (.term t)).1 ⟨n, s, hn⟩
    cases this
    cases ht

/-- **Counterexample for the hypothesis `hU` of the pruning results.** Block `0` of
`pSwLive` ends in `switch 0 [(5, 1)] 2` and the arm for `5` is live. Pruning with
`assume` is then neither an equivalence nor a refinement and changes `wp`; pruning
without `assume` is not a refinement and does not transfer `wp` from the source. -/
theorem pruneArm_hU_counterexample (K : ZContract) :
    (pSwLive.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwLive (selectTarget [(5, 1)] 2 5) ∧
      ¬ EquivPP K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ EquivWT K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ (wp K (pruneArmAssume pSwLive 0 5) (fun _ _ => True) (mkState [5]) ↔
        wp K pSwLive (fun _ _ => True) (mkState [5])) ∧
      ¬ RefinesPP K pSwLive (pruneArm pSwLive 0 5) ∧
      ¬ (wp K pSwLive (fun t _ => t = [1]) (mkState [5]) →
        wp K (pruneArm pSwLive 0 5) (fun t _ => t = [1]) (mkState [5])) := by
  have h1 := pruneArm_live_arm_not_refinesWT K
  have hwp := pruneArm_live_arm_wp_not_transferred K
  exact ⟨by decide, h1.1, fun h => h1.2.1 (refinesWT_of_refinesPP h.1), fun h => h1.2.1 h.1,
    fun hiff => hwp.2.2.1 (hiff.2 hwp.2.1), fun h => h1.2.2 (refinesWT_of_refinesPP h),
    fun himp => hwp.2.2.2.2 (himp hwp.2.2.2.1)⟩

/-- **Counterexample for the terminator hypothesis `hterm`.** The theorems about pruning
take the switch `x arms ow` as parameters. With the stated arms `[(5, 3)]` and
`otherwise` label `2`, the label selected for `5` is the out-of-range label `3` (an
unreachable block), so `hU` holds for the stated switch; but block `0` of `pSwLive`
actually ends in `switch 0 [(5, 1)] 2` with a live arm, and every conclusion fails. -/
theorem pruneArm_hterm_counterexample (K : ZContract) :
    (pSwLive.blk 0).term ≠ .switch 0 [(5, 3)] 2 ∧
      IsUnreachableBlock pSwLive (selectTarget [(5, 3)] 2 5) ∧
      ¬ EquivPP K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ EquivWT K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ (wp K (pruneArmAssume pSwLive 0 5) (fun _ _ => True) (mkState [5]) ↔
        wp K pSwLive (fun _ _ => True) (mkState [5])) ∧
      ¬ RefinesPP K pSwLive (pruneArm pSwLive 0 5) ∧
      ¬ (wp K pSwLive (fun t _ => t = [1]) (mkState [5]) →
        wp K (pruneArm pSwLive 0 5) (fun t _ => t = [1]) (mkState [5])) := by
  have h := pruneArm_hU_counterexample K
  exact ⟨by decide, by decide, h.2.2⟩

/-- Switch on local `0`: value `5` goes to block `1` (emits `1`, halts); `otherwise` is the
unreachable block `2`. -/
def pSwLiveUnreachOw : Prog :=
  [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 1)], .halt⟩, Block.unreach]

/-- **Counterexample for `hU` and `hterm` in the characterizations of pruning without
`assume`, and in `pruneArm_equivPP_of_otherwise_unreachable`.** Block `0` of
`pSwLiveUnreachOw` ends in `switch 0 [(5, 1)] 2`; the arm for `5` is live and
`otherwise` is an unreachable block. From every state the redirected target reaches UB
with empty trace, so the right-hand sides of `pruneArm_equivPP_iff` and
`pruneArm_equivWT_iff` hold, and so does the hypothesis `hOw`; yet pruning is not even a
whole-trace refinement, and both characterizations fail. The stated arms `[(5, 3)]`
satisfy `hU` (the out-of-range label `3`) but not `hterm`, with the same conclusions. -/
theorem pruneArm_iff_counterexample (K : ZContract) :
    (pSwLiveUnreachOw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwLiveUnreachOw (selectTarget [(5, 1)] 2 5) ∧
      (pSwLiveUnreachOw.blk 0).term ≠ .switch 0 [(5, 3)] 2 ∧
      IsUnreachableBlock pSwLiveUnreachOw (selectTarget [(5, 3)] 2 5) ∧
      IsUnreachableBlock pSwLiveUnreachOw 2 ∧
      (∀ st, GoesWrongFrom K (pruneArm pSwLiveUnreachOw 0 5)
        ((pruneArm pSwLiveUnreachOw 0 5).entry 2 st) []) ∧
      ¬ RefinesWT K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ∧
      ¬ EquivPP K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ∧
      ¬ (EquivPP K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ↔
        ∀ st, ReachableAt K pSwLiveUnreachOw 0 (pSwLiveUnreachOw.blk 0).stmts.length st →
          st.locals 0 = 5 →
          GoesWrongFrom K (pruneArm pSwLiveUnreachOw 0 5)
            ((pruneArm pSwLiveUnreachOw 0 5).entry 2 st) []) ∧
      ¬ (EquivWT K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ↔
        ∀ st, ReachableAt K pSwLiveUnreachOw 0 (pSwLiveUnreachOw.blk 0).stmts.length st →
          st.locals 0 = 5 →
          ∃ t, GoesWrongFrom K (pruneArm pSwLiveUnreachOw 0 5)
            ((pruneArm pSwLiveUnreachOw 0 5).entry 2 st) t) := by
  have hp : pruneArm pSwLiveUnreachOw 0 5 =
      [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, Block.unreach] := by decide
  rw [hp]
  have hgw : ∀ st, GoesWrongFrom K
      [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, Block.unreach]
      (Prog.entry [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, Block.unreach] 2 st) [] :=
    fun st => ⟨1, rfl⟩
  have hn : ¬ RefinesWT K pSwLiveUnreachOw
      [⟨[], .switch 0 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, Block.unreach] :=
    not_refinesWT_of_term_wrong (σ := mkState [5]) ⟨3, _, rfl⟩ ⟨2, rfl⟩
  exact ⟨by decide, by decide, by decide, by decide, by decide, hgw, hn,
    fun h => hn (refinesWT_of_refinesPP h.1),
    fun h => hn (refinesWT_of_refinesPP (h.2 fun st _ _ => hgw st).1),
    fun h => hn (h.2 fun st _ _ => ⟨[], hgw st⟩).1⟩

/-- Single-arm shape: value `5` goes to block `1` (halts), `otherwise` is the
unreachable block `2`. -/
def pSwOne : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[], .halt⟩, Block.unreach]

theorem pSwOne_hyps : (pSwOne.blk 0).term = .switch 0 [(5, 1)] 2 ∧
    IsUnreachableBlock pSwOne 2 := by decide

/-- Direct check of `pruneOtherwiseAssume_equivPP` on `pSwOne`. -/
theorem pruneOtherwiseAssume_pSwOne_equivPP (K : ZContract) :
    EquivPP K pSwOne (pruneOtherwiseAssume pSwOne 0) := by
  have hp : pruneOtherwiseAssume pSwOne 0 =
      [⟨[.assume (.eq 0 5)], .goto 1⟩, ⟨[], .halt⟩, Block.unreach] := by decide
  rw [hp]
  refine equivPP_of_sameBeh fun σ b => ?_
  by_cases h : σ.locals 0 = 5
  · exact hasBeh_iff_of_runs_done (n := 3) (m := 3) (t := []) (s := σ) (s' := σ) (by simp_run [pSwOne, h])
      (by simp_run [h]) b
  · exact hasBeh_iff_of_runs_ub (n := 2) (m := 1) (t := []) (by simp_run [pSwOne, h])
      (by simp_run [h]) b

/-- **Counterexample for `hU` and `hterm` of the single-arm results.** Block `0` of `pSw`
ends in `switch 0 [(5, 1)] 2`, and the `otherwise` label `2` halts (it is not an
unreachable block); replacing the switch by `assume (x = 5); goto 1` introduces UB on
local `0 = 0`, so it is neither an equivalence nor a refinement, and `wp` for `True`
holds in the source but not in the target there. The stated `otherwise` label `3` is an
unreachable block (out of range) but is not the actual one, with the same
conclusions. -/
theorem pruneOtherwiseAssume_live_otherwise_not_refinesWT (K : ZContract) :
    (pSw.blk 0).term = .switch 0 [(5, 1)] 2 ∧ ¬ IsUnreachableBlock pSw 2 ∧
      (pSw.blk 0).term ≠ .switch 0 [(5, 1)] 3 ∧ IsUnreachableBlock pSw 3 ∧
      ¬ RefinesWT K pSw (pruneOtherwiseAssume pSw 0) ∧
      ¬ EquivPP K pSw (pruneOtherwiseAssume pSw 0) ∧
      wp K pSw (fun _ _ => True) (mkState [0]) ∧
      ¬ wp K (pruneOtherwiseAssume pSw 0) (fun _ _ => True) (mkState [0]) ∧
      ¬ (wp K (pruneOtherwiseAssume pSw 0) (fun _ _ => True) (mkState [0]) ↔
        wp K pSw (fun _ _ => True) (mkState [0])) := by
  have hp : pruneOtherwiseAssume pSw 0 =
      [⟨[.assume (.eq 0 5)], .goto 1⟩, Block.unreach, ⟨[], .halt⟩] := by decide
  rw [hp]
  have hn : ¬ RefinesWT K pSw [⟨[.assume (.eq 0 5)], .goto 1⟩, Block.unreach, ⟨[], .halt⟩] :=
    not_refinesWT_of_term_wrong (σ := mkState [0]) ⟨3, _, rfl⟩ ⟨1, rfl⟩
  have hs : wp K pSw (fun _ _ => True) (mkState [0]) := ⟨3, [], _, rfl, trivial⟩
  have ht : ¬ wp K [⟨[.assume (.eq 0 5)], .goto 1⟩, Block.unreach, ⟨[], .halt⟩]
      (fun _ _ => True) (mkState [0]) := by
    rintro ⟨n, t, s, hn, _⟩
    have := (hasBehFrom_iff_of_run_ub (n := 1) (t := [])
      (P := [⟨[.assume (.eq 0 5)], .goto 1⟩, Block.unreach, ⟨[], .halt⟩]) rfl (.term t)).1
      ⟨n, s, hn⟩
    cases this
  exact ⟨by decide, by decide, by decide, by decide, hn, fun h => hn (refinesWT_of_refinesPP h.1),
    hs, ht, fun h => ht (h.2 hs)⟩

/-! ### Pruning without `assume` -/

/-- **Pruning without `assume` refines.** If block `l` ends in `switch x arms ow` and
the label selected for value `v` is an unreachable block, removing the arms with value
`v` (so that `x = v` now goes to `ow`) is a prefix-preserving refinement. -/
theorem pruneArm_refinesPP (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    RefinesPP K P (pruneArm P l v) := by
  exact pa_refinesPP hterm hU

/-- **Exact condition for equivalence (prefix-preserving).** Under the hypotheses of
`pruneArm_refinesPP`, pruning without `assume` is a prefix-preserving equivalence iff,
for every reachable state at the switch with `x = v`, the target run from the entry of
`ow` (the redirected target) reaches UB before emitting any event. -/
theorem pruneArm_equivPP_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivPP K P (pruneArm P l v) ↔
      ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x = v →
        GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) [] := by
  exact pa_equivPP_iff hterm hU

/-- **Exact condition for equivalence (whole-trace).** Under the hypotheses of
`pruneArm_refinesPP`, pruning without `assume` is a whole-trace equivalence iff, for
every reachable state at the switch with `x = v`, the target run from the entry of `ow`
reaches UB (possibly after emitting events). -/
theorem pruneArm_equivWT_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivWT K P (pruneArm P l v) ↔
      ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x = v →
        ∃ t, GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) t := by
  exact pa_equivWT_iff hterm hU

/-- **Corollary: unreachable `otherwise`.** Under the hypotheses of
`pruneArm_refinesPP`, if `ow` is itself an unreachable block, pruning without `assume`
is a prefix-preserving equivalence. -/
theorem pruneArm_equivPP_of_otherwise_unreachable (K : ZContract) (P : Prog) (l : Label)
    (x : Var) (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) (hOw : IsUnreachableBlock P ow) :
    EquivPP K P (pruneArm P l v) := by
  exact (pruneArm_equivPP_iff K P l x arms ow v hterm hU).2
    fun st _ _ => pa_ow_wrong hterm hOw st

/-- **Invariant `x ≠ v`.** If block `l` ends in `switch x arms ow` and `x ≠ v` holds on
every reachable state at the switch (`ReachableAt`, which includes runs that reach UB
later), pruning the arms with value `v` without `assume` is a prefix-preserving
equivalence, whether or not the pruned label is an unreachable block. This is not a
special case of `pruneArm_equivPP_iff`, which assumes that the pruned label is an
unreachable block. -/
theorem pruneArm_equivPP_of_invariant_ne (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hinv : ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x ≠ v) :
    EquivPP K P (pruneArm P l v) := by
  exact pa_equivPP_of_invariant hterm hinv

/-- **`wp` transfers from source to target.** Under the hypotheses of
`pruneArm_refinesPP`, for every postcondition `Q` and input `σ`, `wp` of the source
implies `wp` of the pruned target. (The converse fails:
`pruneArm_pSw_wp_transfers_one_way`.) -/
theorem pruneArm_wp_of_wp_src (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v))
    (Q : List Int → State → Prop) (σ : State) :
    wp K P Q σ → wp K (pruneArm P l v) Q σ := by
  exact pa_wp hterm hU Q σ

/-! #### Pruning without `assume`: instances and counterexamples (fully proved) -/

theorem pruneArm_pSw : pruneArm pSw 0 5 = [⟨[], .switch 0 [] 2⟩, Block.unreach, ⟨[], .halt⟩] := by
  decide

/-- **VC counterexample.** For `pSw` and the postcondition `True`: `wp` of the pruned
target holds on every input, while `wp` of the source holds exactly when local `0 ≠ 5`.
So at local `0 = 5` the target's `wp` holds and the source's fails. -/
theorem pruneArm_pSw_wp_transfers_one_way (K : ZContract) :
    (∀ σ, wp K (pruneArm pSw 0 5) (fun _ _ => True) σ) ∧
      (∀ σ, wp K pSw (fun _ _ => True) σ ↔ σ.locals 0 ≠ 5) ∧
      wp K (pruneArm pSw 0 5) (fun _ _ => True) (mkState [5]) ∧
      ¬ wp K pSw (fun _ _ => True) (mkState [5]) := by
  rw [pruneArm_pSw]
  have htgt : ∀ σ, wp K [⟨[], .switch 0 [] 2⟩, Block.unreach, ⟨[], .halt⟩]
      (fun _ _ => True) σ := fun σ => ⟨2, [], σ, by simp_run, trivial⟩
  have hsrc : ∀ σ, wp K pSw (fun _ _ => True) σ ↔ σ.locals 0 ≠ 5 := by
    intro σ
    by_cases h : σ.locals 0 = 5
    · simp only [h, ne_eq, not_true_eq_false, iff_false]
      rintro ⟨n, t, s, hn, _⟩
      have := (hasBehFrom_iff_of_run_ub (n := 2) (t := []) (P := pSw)
        (by simp_run [pSw, h]) (.term t)).1 ⟨n, s, hn⟩
      cases this
    · simp only [h, ne_eq, not_false_eq_true, iff_true]
      exact ⟨2, [], σ, by simp_run [pSw, h], trivial⟩
  exact ⟨htgt, hsrc, htgt _, fun h => (hsrc _).1 h rfl⟩

/-- **Pruning without `assume` is not an equivalence on `pSw`.** The pruned program is
a prefix-preserving refinement of `pSw`, but on local `0 = 5` the source reaches UB
and the target halts, so it is not a whole-trace equivalence. -/
theorem pruneArm_pSw_refinesPP_not_equivWT (K : ZContract) :
    RefinesPP K pSw (pruneArm pSw 0 5) ∧ ¬ EquivWT K pSw (pruneArm pSw 0 5) := by
  rw [pruneArm_pSw]
  refine ⟨fun σ => ?_, fun h => not_refinesWT_of_term_wrong (σ := mkState [5])
    ⟨2, _, rfl⟩ ⟨2, rfl⟩ h.2⟩
  by_cases h : σ.locals 0 = 5
  · exact refinesPPAt_of_tgt_done (n := 2) (t := []) (s := σ) (by simp_run [h])
      (Or.inr ⟨2, [], by simp_run [pSw, h], prefix_nil _⟩)
  · exact refinesPPAt_of_tgt_done (n := 2) (t := []) (s := σ) (by simp_run [h])
      (Or.inl ⟨2, σ, by simp_run [pSw, h]⟩)

/-- **Counterexample for `hOw` and for `hinv` in the sufficient conditions for an
equivalent pruning without `assume`.** In `pSw`, `hterm` and `hU` hold, but the
`otherwise` label `2` halts (so `hOw` fails), local `0 = 5` is reachable at the switch
(so `hinv` fails for `x = 0`, `v = 5`), and pruning is not a prefix-preserving
equivalence. -/
theorem pruneArm_pSw_hyps_counterexample (K : ZContract) :
    (pSw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      IsUnreachableBlock pSw (selectTarget [(5, 1)] 2 5) ∧
      ¬ IsUnreachableBlock pSw 2 ∧
      ¬ (∀ st, ReachableAt K pSw 0 (pSw.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      ¬ EquivPP K pSw (pruneArm pSw 0 5) := by
  refine ⟨by decide, by decide, by decide, fun hinv => ?_, fun heq => ?_⟩
  · exact hinv (mkState [5]) (reachableAt_entry K pSw (mkState [5])) rfl
  · exact (pruneArm_pSw_refinesPP_not_equivWT K).2 (equivWT_of_equivPP heq)

/-- **A fact on the non-UB runs is not a reachable-state invariant.** In `pSw`, the arm
for `5` leads to an unreachable block, so `local 0 ≠ 5` holds at the switch on every run
that never reaches UB; it does not hold on every reachable state there (the
hypothesis `hinv` of `pruneArm_equivPP_of_invariant_ne` fails), and pruning the arm
without `assume` is not a whole-trace equivalence. -/
theorem pSw_fact_not_invariant (K : ZContract) :
    FactOnDefinedRuns K pSw 0 0 (fun st => st.locals 0 ≠ 5) ∧
      ¬ (∀ st, ReachableAt K pSw 0 (pSw.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      ¬ EquivWT K pSw (pruneArm pSw 0 5) := by
  refine ⟨?_, (pruneArm_pSw_hyps_counterexample K).2.2.2.1,
    (pruneArm_pSw_refinesPP_not_equivWT K).2⟩
  rintro σ st ⟨n, t, h⟩ hdef
  match n with
  | 0 =>
    simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pSw] at h
    obtain ⟨rfl, -⟩ := h
    intro h5
    exact hdef [] ⟨2, by simp_run [pSw, h5]⟩
  | n + 1 =>
    exfalso
    by_cases h5 : σ.locals 0 = 5
    · match n with
      | 0 => simp_run [pSw, h5, Prog.at] at h
      | n + 1 => simp_run [pSw, h5] at h
    · match n with
      | 0 => simp_run [pSw, h5, Prog.at] at h
      | n + 1 => simp_run [pSw, h5] at h

/-- Switch on local `0`: value `5` goes to the unreachable block `1`, otherwise to
block `2`, which starts with `assume (local 0 ≠ 5)` and halts. -/
def pSwAssumeOw : Prog :=
  [⟨[], .switch 0 [(5, 1)] 2⟩, Block.unreach, ⟨[.assume (.ne 0 5)], .halt⟩]

/-- Non-vacuity of `pruneArm_equivPP_iff` and `pruneArm_equivWT_iff`: `pSwAssumeOw`
satisfies `hterm` and `hU`. -/
theorem pSwAssumeOw_hyps : (pSwAssumeOw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
    IsUnreachableBlock pSwAssumeOw (selectTarget [(5, 1)] 2 5) := by decide

/-- **The exact condition of `pruneArm_equivPP_iff` beyond its corollaries.** In
`pSwAssumeOw` the value `5` is reachable at the switch and `otherwise` is not an
unreachable block, but the redirected target reaches UB before any event; pruning
without `assume` is then a prefix-preserving equivalence. -/
theorem pruneArm_pSwAssumeOw_equivPP (K : ZContract) :
    ReachableAt K pSwAssumeOw 0 0 (mkState [5]) ∧
      ¬ IsUnreachableBlock pSwAssumeOw 2 ∧
      GoesWrongFrom K (pruneArm pSwAssumeOw 0 5) ((pruneArm pSwAssumeOw 0 5).entry 2
        (mkState [5])) [] ∧
      EquivPP K pSwAssumeOw (pruneArm pSwAssumeOw 0 5) := by
  have hp : pruneArm pSwAssumeOw 0 5 =
      [⟨[], .switch 0 [] 2⟩, Block.unreach, ⟨[.assume (.ne 0 5)], .halt⟩] := by decide
  rw [hp]
  refine ⟨reachableAt_entry _ _ _, by decide, ⟨1, rfl⟩, equivPP_of_sameBeh fun σ b => ?_⟩
  by_cases h : σ.locals 0 = 5
  · exact hasBeh_iff_of_runs_ub (n := 2) (m := 2) (t := []) (by simp_run [pSwAssumeOw, h])
      (by simp_run [h]) b
  · exact hasBeh_iff_of_runs_done (n := 3) (m := 3) (t := []) (s := σ) (s' := σ)
      (by simp_run [pSwAssumeOw, h]) (by simp_run [h]) b

/-- `local 0 := 1`, then the switch of `pSw`: the value `5` is impossible at the
switch. -/
def pSwInv : Prog := [⟨[.assign 0 (.const 1)], .switch 0 [(5, 1)] 2⟩, Block.unreach, ⟨[], .halt⟩]

/-- Non-vacuity of `pruneArm_equivPP_of_invariant_ne`: in `pSwInv` every reachable
state at the switch has local `0 = 1 ≠ 5`. -/
theorem pSwInv_invariant (K : ZContract) :
    ∀ st, ReachableAt K pSwInv 0 (pSwInv.blk 0).stmts.length st → st.locals 0 ≠ 5 := by
  rintro st ⟨σ, n, t, h⟩
  match n with
  | 0 => simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pSwInv] at h
  | 1 =>
    simp_run [pSwInv, Prog.at] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | 2 => simp_run [pSwInv, Prog.at] at h
  | n + 3 =>
    have h₃ : run K pSwInv 3 (pSwInv.init σ) = .done [] (σ.set 0 1) := by simp_run [pSwInv]
    rw [run_done_mono h₃ (by omega : 3 ≤ n + 3)] at h
    cases h

/-- Non-vacuity of `pruneArm_equivPP_of_invariant_ne`: `pSwInv` satisfies both
hypotheses. -/
theorem pruneArm_equivPP_of_invariant_ne_nonvacuous (K : ZContract) :
    (pSwInv.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ∀ st, ReachableAt K pSwInv 0 (pSwInv.blk 0).stmts.length st → st.locals 0 ≠ 5 :=
  ⟨by decide, pSwInv_invariant K⟩

/-- Block `0` sets local `0 := 1` and then switches on local `1`: value `5` goes to block
`1`, which emits `1` and halts; otherwise block `2` halts. -/
def pSwDiffVar : Prog :=
  [⟨[.assign 0 (.const 1)], .switch 1 [(5, 1)] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩]

/-- **Counterexample for `hterm` in `pruneArm_equivPP_of_invariant_ne`.** For the stated
switch variable `x = 0`, local `0 ≠ 5` holds on every reachable state at the switch of
`pSwDiffVar` (so `hinv` holds), but block `0` actually switches on local `1`, and
pruning the arm for `5` is not an equivalence under either discipline. -/
theorem pruneArm_invariant_ne_hterm_counterexample (K : ZContract) :
    (pSwDiffVar.blk 0).term ≠ .switch 0 [(5, 1)] 2 ∧
      (∀ st, ReachableAt K pSwDiffVar 0 (pSwDiffVar.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      ¬ EquivPP K pSwDiffVar (pruneArm pSwDiffVar 0 5) ∧
      ¬ EquivWT K pSwDiffVar (pruneArm pSwDiffVar 0 5) := by
  have hp : pruneArm pSwDiffVar 0 5 =
      [⟨[.assign 0 (.const 1)], .switch 1 [] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩] := by
    decide
  have hn : ¬ EquivWT K pSwDiffVar (pruneArm pSwDiffVar 0 5) := by
    intro heq
    rw [hp] at heq
    exact not_refinesWT_of_term_term (σ := mkState [0, 5])
      (u := [1]) (u' := []) ⟨4, _, rfl⟩ ⟨3, _, rfl⟩ (by decide) heq.1
  refine ⟨by decide, ?_, fun h => hn (equivWT_of_equivPP h), hn⟩
  rintro st ⟨σ, n, t, h⟩
  match n with
  | 0 => simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pSwDiffVar] at h
  | 1 =>
    simp_run [pSwDiffVar, Prog.at] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | 2 =>
    by_cases h5 : σ.locals 1 = 5
    · simp_run [pSwDiffVar, Prog.at, h5] at h
    · simp_run [pSwDiffVar, Prog.at, h5] at h
  | 3 =>
    by_cases h5 : σ.locals 1 = 5
    · simp_run [pSwDiffVar, Prog.at, h5] at h
    · simp_run [pSwDiffVar, Prog.at, h5] at h
  | n + 4 =>
    by_cases h5 : σ.locals 1 = 5
    · have h₄ : run K pSwDiffVar 4 (pSwDiffVar.init σ) = .done [1] (σ.set 0 1) := by
        simp_run [pSwDiffVar, h5]
      rw [run_done_mono h₄ (by omega : 4 ≤ n + 4)] at h
      cases h
    · have h₃ : run K pSwDiffVar 3 (pSwDiffVar.init σ) = .done [] (σ.set 0 1) := by
        simp_run [pSwDiffVar, h5]
      rw [run_done_mono h₃ (by omega : 3 ≤ n + 4)] at h
      cases h

/-- A switch whose arm for `5` and whose `otherwise` label both lead to unreachable
blocks. -/
def pSwDead : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, Block.unreach, Block.unreach]

/-- Non-vacuity of `pruneArm_equivPP_of_otherwise_unreachable`: `pSwDead` satisfies its
three hypotheses. -/
theorem pruneArm_equivPP_of_otherwise_unreachable_nonvacuous :
    (pSwDead.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      IsUnreachableBlock pSwDead (selectTarget [(5, 1)] 2 5) ∧ IsUnreachableBlock pSwDead 2 := by
  decide

/-! ### UB-derived facts -/

/-- **With `assume`, UB-derived facts survive pruning.** For every program, block `l` and
value `v`, every state predicate that holds at a program point `(l', i')` on all non-UB
runs of the source also holds at `(l', i')` on all non-UB runs of
`pruneArmAssume P l v`. No hypothesis on the pruned arm is needed: the inserted
`assume` makes every run that would use a removed arm reach UB. For block `l` itself,
with `length` the number of statements of block `l` in `P`, the target points
`i' = length` and `i' = length + 1` lie before and after the inserted `assume`; both
correspond to the source's switch point. At `i' = length`, `F` holds in the target
because the runs that fail the inserted `assume` are excluded as UB runs. Preserving such
facts does not by itself make a transformation a refinement (`factOnDefinedRuns_unreach`). -/
theorem pruneArmAssume_preserves_factOnDefinedRuns (K : ZContract) (P : Prog) (l : Label)
    (v : Int) (l' : Label) (i' : Nat) (F : State → Prop)
    (hF : FactOnDefinedRuns K P l' i' F) : FactOnDefinedRuns K (pruneArmAssume P l v) l' i' F := by
  exact paa_fact hF

/-- **Facts on the non-UB runs are vacuous for an always-UB program.** Every state
predicate holds at every point on the (nonexistent) non-UB runs of `pUnreach`. So a
transformation that replaces a program by `pUnreach` preserves every such fact,
although it is not a refinement in general (`not_refinesWT_halt_unreach`). -/
theorem factOnDefinedRuns_unreach (K : ZContract) (l : Label) (i : Nat) (F : State → Prop) :
    FactOnDefinedRuns K pUnreach l i F :=
  fun σ _ _ hdef => absurd (hasBeh_unreach K σ) (hdef [])

/-- Switch on local `0`: value `5` goes to the unreachable block `2`, otherwise block `1`
emits local `0` and halts. -/
def pFact : Prog := [⟨[], .switch 0 [(5, 2)] 1⟩, ⟨[.emit (.var 0)], .halt⟩, Block.unreach]

theorem pruneArm_pFact : pruneArm pFact 0 5 =
    [⟨[], .switch 0 [] 1⟩, ⟨[.emit (.var 0)], .halt⟩, Block.unreach] := by decide

/-- In `pFact`, `local 0 ≠ 5` holds at the switch on every non-UB run (a UB-derived
fact: it fails on the runs that reach UB). -/
theorem pFact_fact (K : ZContract) :
    FactOnDefinedRuns K pFact 0 0 (fun st => st.locals 0 ≠ 5) := by
  rintro σ st ⟨n, t, h⟩ hdef
  match n with
  | 0 =>
    simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pFact] at h
    obtain ⟨rfl, -⟩ := h
    intro h5
    exact hdef [] ⟨2, by simp_run [pFact, h5]⟩
  | n + 1 =>
    exfalso
    by_cases h5 : σ.locals 0 = 5
    · match n with
      | 0 => simp_run [pFact, h5, Prog.at] at h
      | n + 1 => simp_run [pFact, h5] at h
    · match n with
      | 0 => simp_run [pFact, h5, Prog.at] at h
      | 1 => simp_run [pFact, h5, Prog.at] at h
      | n + 2 => simp_run [pFact, h5] at h

/-- **Without `assume`, the UB-derived fact is lost.** After pruning `pFact` without
`assume`, the input with local `0 = 5` reaches the switch, never reaches UB, and
violates `local 0 ≠ 5` there. -/
theorem pruneArm_breaks_ubDerivedFact (K : ZContract) :
    FactOnDefinedRuns K pFact 0 0 (fun st => st.locals 0 ≠ 5) ∧
      ¬ FactOnDefinedRuns K (pruneArm pFact 0 5) 0 0 (fun st => st.locals 0 ≠ 5) := by
  refine ⟨pFact_fact K, fun h => ?_⟩
  rw [pruneArm_pFact] at h
  refine h (mkState [5]) (mkState [5]) ⟨0, [], rfl⟩ (fun t hw => ?_) rfl
  have := (hasBehFrom_iff_of_run_done (n := 3)
    (P := [⟨[], .switch 0 [] 1⟩, ⟨[.emit (.var 0)], .halt⟩, Block.unreach]) rfl (.wrong t)).1 hw
  cases this

/-- Non-vacuity of `pruneArmAssume_preserves_factOnDefinedRuns`: `pFact` satisfies its
hypothesis with the UB-derived fact `local 0 ≠ 5` at point `(0, 0)`. -/
theorem pruneArmAssume_preserves_factOnDefinedRuns_nonvacuous (K : ZContract) :
    FactOnDefinedRuns K pFact 0 0 (fun st => st.locals 0 ≠ 5) :=
  pFact_fact K

/-- **Counterexample for the hypothesis `hF`.** The predicate `False` holds at point
`(0, 0)` on the non-UB runs neither of `pFact` nor of `pruneArmAssume pFact 0 5` (in
both, the input with local `0 = 0` reaches it and terminates). -/
theorem pruneArmAssume_fact_hypothesis_counterexample (K : ZContract) :
    ¬ FactOnDefinedRuns K pFact 0 0 (fun _ => False) ∧
      ¬ FactOnDefinedRuns K (pruneArmAssume pFact 0 5) 0 0 (fun _ => False) := by
  refine ⟨fun hf => ?_, ?_⟩
  · refine hf (mkState [0]) (mkState [0]) ⟨0, [], rfl⟩ (fun t hw => ?_)
    have hdone : run K pFact 3 (pFact.init (mkState [0])) = .done [0] (mkState [0]) := by
      simp_run [pFact]
    have := (hasBehFrom_iff_of_run_done hdone (.wrong t)).1 hw
    cases this
  have hp : pruneArmAssume pFact 0 5 =
      [⟨[.assume (.ne 0 5)], .switch 0 [] 1⟩, ⟨[.emit (.var 0)], .halt⟩, Block.unreach] := by
    decide
  rw [hp]
  intro h
  refine h (mkState [0]) (mkState [0]) ⟨0, [], rfl⟩ (fun t hw => ?_)
  have := (hasBehFrom_iff_of_run_done (n := 4) (t := [0]) (s := mkState [0])
    (P := [⟨[.assume (.ne 0 5)], .switch 0 [] 1⟩, ⟨[.emit (.var 0)], .halt⟩, Block.unreach])
    (by simp_run) (.wrong t)).1 hw
  cases this

/-- Two switches on local `0`: block `0` sends `5` to the unreachable block `3`, else to
block `1`; block `1` sends `5` to block `2` (emits `1`), else to block `4` (emits `0`). In
the source, `local 0 ≠ 5` holds at block `1`, so a fact-based pass may fold block `1`'s
switch to `goto 4`. -/
def pStale : Prog :=
  [⟨[], .switch 0 [(5, 3)] 1⟩, ⟨[], .switch 0 [(5, 2)] 4⟩, ⟨[.emit (.const 1)], .halt⟩,
    Block.unreach, ⟨[.emit (.const 0)], .halt⟩]

/-- **A fact computed before pruning is stale after it.** In `pStale`, `local 0 ≠ 5`
holds at block `1` on every non-UB run. Pruning block `0`'s arm for `5` without
`assume` (giving `T1`) is a prefix-preserving refinement of the source; folding block
`1` to `goto 4` using the stale fact (giving `T2`) is not a whole-trace refinement of
its actual input `T1`. In this instance the composite `T2` is still a
prefix-preserving refinement of the source. -/
theorem staleFact_fold_after_pruneArm (K : ZContract) :
    FactOnDefinedRuns K pStale 1 0 (fun st => st.locals 0 ≠ 5) ∧
      RefinesPP K pStale (pruneArm pStale 0 5) ∧
      ¬ RefinesWT K (pruneArm pStale 0 5) (foldToGoto (pruneArm pStale 0 5) 1 4) ∧
      RefinesPP K pStale (foldToGoto (pruneArm pStale 0 5) 1 4) := by
  have hT1 : pruneArm pStale 0 5 =
      [⟨[], .switch 0 [] 1⟩, ⟨[], .switch 0 [(5, 2)] 4⟩, ⟨[.emit (.const 1)], .halt⟩,
        Block.unreach, ⟨[.emit (.const 0)], .halt⟩] := by decide
  have hT2 : foldToGoto (pruneArm pStale 0 5) 1 4 =
      [⟨[], .switch 0 [] 1⟩, ⟨[], .goto 4⟩, ⟨[.emit (.const 1)], .halt⟩,
        Block.unreach, ⟨[.emit (.const 0)], .halt⟩] := by decide
  rw [hT2, hT1]
  refine ⟨?_, fun σ => ?_, ?_, fun σ => ?_⟩
  · rintro σ st ⟨n, t, h⟩ _
    by_cases h5 : σ.locals 0 = 5
    · match n with
      | 0 => simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pStale] at h
      | 1 => simp_run [pStale, h5, Prog.at] at h
      | n + 2 => simp_run [pStale, h5] at h
    · match n with
      | 0 => simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pStale] at h
      | 1 =>
        simp_run [pStale, h5, Prog.at] at h
        obtain ⟨rfl, -⟩ := h
        exact h5
      | 2 => simp_run [pStale, h5, Prog.at] at h
      | 3 => simp_run [pStale, h5, Prog.at] at h
      | n + 4 => simp_run [pStale, h5] at h
  · by_cases h5 : σ.locals 0 = 5
    · exact refinesPPAt_of_tgt_done (n := 5) (t := [1]) (s := σ) (by simp_run [h5])
        (Or.inr ⟨2, [], by simp_run [pStale, h5], prefix_nil _⟩)
    · exact refinesPPAt_of_tgt_done (n := 5) (t := [0]) (s := σ) (by simp_run [h5])
        (Or.inl ⟨5, σ, by simp_run [pStale, h5]⟩)
  · exact not_refinesWT_of_term_term (σ := mkState [5]) ⟨5, _, rfl⟩ ⟨5, _, rfl⟩ (by decide)
  · by_cases h5 : σ.locals 0 = 5
    · exact refinesPPAt_of_tgt_done (n := 5) (t := [0]) (s := σ) (by simp_run [h5])
        (Or.inr ⟨2, [], by simp_run [pStale, h5], prefix_nil _⟩)
    · exact refinesPPAt_of_tgt_done (n := 5) (t := [0]) (s := σ) (by simp_run [h5])
        (Or.inl ⟨5, σ, by simp_run [pStale, h5]⟩)

/-- **With `assume` retained, the same fact-based fold is a refinement of its input.**
Pruning block `0` of `pStale` with `assume (local 0 ≠ 5)` and then folding block `1`
to `goto 4` gives a prefix-preserving refinement of the pruned program. -/
theorem staleFact_fold_after_pruneArmAssume_refinesPP (K : ZContract) :
    RefinesPP K (pruneArmAssume pStale 0 5) (foldToGoto (pruneArmAssume pStale 0 5) 1 4) := by
  have hT1 : pruneArmAssume pStale 0 5 =
      [⟨[.assume (.ne 0 5)], .switch 0 [] 1⟩, ⟨[], .switch 0 [(5, 2)] 4⟩,
        ⟨[.emit (.const 1)], .halt⟩, Block.unreach, ⟨[.emit (.const 0)], .halt⟩] := by decide
  have hT2 : foldToGoto (pruneArmAssume pStale 0 5) 1 4 =
      [⟨[.assume (.ne 0 5)], .switch 0 [] 1⟩, ⟨[], .goto 4⟩,
        ⟨[.emit (.const 1)], .halt⟩, Block.unreach, ⟨[.emit (.const 0)], .halt⟩] := by decide
  rw [hT2, hT1]
  intro σ
  by_cases h5 : σ.locals 0 = 5
  · exact refinesPPAt_of_tgt_ub (n := 1) (m := 1) (t := []) (t' := []) (by simp_run [h5])
      (by simp_run [h5]) (prefix_nil _)
  · exact refinesPPAt_of_tgt_done (n := 6) (t := [0]) (s := σ) (by simp_run [h5])
      (Or.inl ⟨6, σ, by simp_run [h5]⟩)

/-- Block `0` switches on local `0`: `5` goes to block `2` (`emit 7; goto 1`), otherwise
to block `4` (`emit 0; halt`). Block `1` switches on local `0`: `5` goes to the
unreachable block `3`, otherwise to block `4`. -/
def pEmitFact : Prog :=
  [ ⟨[], .switch 0 [(5, 2)] 4⟩,
    ⟨[], .switch 0 [(5, 3)] 4⟩,
    ⟨[.emit (.const 7)], .goto 1⟩,
    Block.unreach,
    ⟨[.emit (.const 0)], .halt⟩ ]

/-- **A fact on the non-UB runs may rely on UB after an event.** In `pEmitFact`,
`local 0 ≠ 5` holds at point `(0, 0)` on every run that never reaches UB, because the
input with local `0 = 5` emits `7` and then reaches UB. Folding block `0` to its
`otherwise` label `4` using this fact is a whole-trace refinement but not a
prefix-preserving refinement of the source (the event `7` before the UB is lost). Both
facts also hold, again relative to the source `pEmitFact`, for the composite that first
prunes block `1`'s arm for `5` without `assume` (a refinement of the source) and folds. -/
theorem factOnDefinedRuns_fold_refinesWT_not_refinesPP (K : ZContract) :
    FactOnDefinedRuns K pEmitFact 0 0 (fun st => st.locals 0 ≠ 5) ∧
      ¬ RefinesPP K pEmitFact (foldToGoto pEmitFact 0 4) ∧
      RefinesWT K pEmitFact (foldToGoto pEmitFact 0 4) ∧
      RefinesPP K pEmitFact (pruneArm pEmitFact 1 5) ∧
      ¬ RefinesPP K pEmitFact (foldToGoto (pruneArm pEmitFact 1 5) 0 4) ∧
      RefinesWT K pEmitFact (foldToGoto (pruneArm pEmitFact 1 5) 0 4) := by
  have hT1 : pruneArm pEmitFact 1 5 =
      [ ⟨[], .switch 0 [(5, 2)] 4⟩,
        ⟨[], .switch 0 [] 4⟩,
        ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach,
        ⟨[.emit (.const 0)], .halt⟩ ] := by decide
  have hF0 : foldToGoto pEmitFact 0 4 =
      [ ⟨[], .goto 4⟩,
        ⟨[], .switch 0 [(5, 3)] 4⟩,
        ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach,
        ⟨[.emit (.const 0)], .halt⟩ ] := by decide
  have hT2 : foldToGoto (pruneArm pEmitFact 1 5) 0 4 =
      [ ⟨[], .goto 4⟩,
        ⟨[], .switch 0 [] 4⟩,
        ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach,
        ⟨[.emit (.const 0)], .halt⟩ ] := by decide
  rw [hT2, hF0, hT1]
  refine ⟨?_, ?_, fun σ bt hbt => ?_, fun σ => ?_, ?_, fun σ bt hbt => ?_⟩
  · rintro σ st ⟨n, t, h⟩ hdef
    match n with
    | 0 =>
      simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pEmitFact] at h
      obtain ⟨rfl, -⟩ := h
      intro h5
      exact hdef [7] ⟨5, by simp_run [pEmitFact, h5]⟩
    | n + 1 =>
      exfalso
      by_cases h5 : σ.locals 0 = 5
      · match n with
        | 0 => simp_run [pEmitFact, h5, Prog.at] at h
        | 1 => simp_run [pEmitFact, h5, Prog.at] at h
        | 2 => simp_run [pEmitFact, h5, Prog.at] at h
        | 3 => simp_run [pEmitFact, h5, Prog.at] at h
        | n + 4 => simp_run [pEmitFact, h5] at h
      · match n with
        | 0 => simp_run [pEmitFact, h5, Prog.at] at h
        | 1 => simp_run [pEmitFact, h5, Prog.at] at h
        | n + 2 => simp_run [pEmitFact, h5] at h
  · intro href
    obtain ⟨bs, hbs, himp⟩ := href (mkState [5]) (.term [0]) ⟨3, _, rfl⟩
    have := (hasBehFrom_iff_of_run_ub (n := 5) (t := [7]) (P := pEmitFact) rfl bs).1 hbs
    subst this
    rcases himp with h | ⟨t, ht, hp⟩
    · cases h
    · cases ht; simp [Beh.HasPrefix] at hp
  · have ht : run K [⟨[], .goto 4⟩, ⟨[], .switch 0 [(5, 3)] 4⟩, ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach, ⟨[.emit (.const 0)], .halt⟩] 3
        (Prog.init [⟨[], .goto 4⟩, ⟨[], .switch 0 [(5, 3)] 4⟩, ⟨[.emit (.const 7)], .goto 1⟩,
          Block.unreach, ⟨[.emit (.const 0)], .halt⟩] σ) = .done [0] σ := by simp_run
    have := (hasBehFrom_iff_of_run_done ht bt).1 hbt
    subst this
    by_cases h5 : σ.locals 0 = 5
    · exact ⟨.wrong [7], ⟨5, by simp_run [pEmitFact, h5]⟩, Or.inr ⟨[7], rfl⟩⟩
    · exact ⟨.term [0], ⟨3, σ, by simp_run [pEmitFact, h5]⟩, Or.inl rfl⟩
  · by_cases h5 : σ.locals 0 = 5
    · exact refinesPPAt_of_tgt_done (n := 6) (t := [7, 0]) (s := σ) (by simp_run [h5])
        (Or.inr ⟨5, [7], by simp_run [pEmitFact, h5], ⟨[0], rfl⟩⟩)
    · exact refinesPPAt_of_tgt_done (n := 3) (t := [0]) (s := σ) (by simp_run [h5])
        (Or.inl ⟨3, σ, by simp_run [pEmitFact, h5]⟩)
  · intro href
    obtain ⟨bs, hbs, himp⟩ := href (mkState [5]) (.term [0]) ⟨3, _, rfl⟩
    have := (hasBehFrom_iff_of_run_ub (n := 5) (t := [7]) (P := pEmitFact) rfl bs).1 hbs
    subst this
    rcases himp with h | ⟨t, ht, hp⟩
    · cases h
    · cases ht; simp [Beh.HasPrefix] at hp
  · have ht : run K [⟨[], .goto 4⟩, ⟨[], .switch 0 [] 4⟩, ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach, ⟨[.emit (.const 0)], .halt⟩] 3
        (Prog.init [⟨[], .goto 4⟩, ⟨[], .switch 0 [] 4⟩, ⟨[.emit (.const 7)], .goto 1⟩,
          Block.unreach, ⟨[.emit (.const 0)], .halt⟩] σ) = .done [0] σ := by simp_run
    have := (hasBehFrom_iff_of_run_done ht bt).1 hbt
    subst this
    by_cases h5 : σ.locals 0 = 5
    · exact ⟨.wrong [7], ⟨5, by simp_run [pEmitFact, h5]⟩, Or.inr ⟨[7], rfl⟩⟩
    · exact ⟨.term [0], ⟨3, σ, by simp_run [pEmitFact, h5]⟩, Or.inl rfl⟩

end Toy.ZstAssume
