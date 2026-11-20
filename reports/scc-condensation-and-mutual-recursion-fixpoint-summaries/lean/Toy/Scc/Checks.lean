/-
Toy.Scc.Checks
==============

Mechanical cross-checks between the main results and their witnesses.  Every
`example` below derives, from a tightness counterexample and the main theorem, that
the dropped hypothesis fails (so the counterexample really satisfies all other
hypotheses of that theorem, as stated, and refutes its conclusion), or instantiates a
main theorem at its non-vacuity witness.  This module adds no named declarations.
-/
import Toy.Scc.Decomp
import Toy.Scc.Fixpoint
import Toy.Scc.Transfer
import Toy.Scc.Termination

namespace Toy.Scc

/-! ## Non-vacuity witnesses instantiate the main theorems -/

example : reachFrom gPath3 0 2 2 = true ↔ Reach gPath3 0 2 :=
  reachFrom_eq_true_iff_reach_of_pred_le gPath3 0 2 reachFrom_nonvacuous.1
example : checkScc gPath idComp = true ↔ IsSccDecomp gPath idComp :=
  checkScc_eq_true_iff_isSccDecomp gPath idComp
example : BlocksMutuallyReachable gMix idComp ∧ CondensationAcyclic gMix idComp :=
  (isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic gMix idComp).1
    sccChar_nonvacuous.1
example : ∃ order : List (Fin 2), order.Nodup ∧ Covers (idComp (n := 2)) order ∧
    CalleesFirst gPath idComp order :=
  (condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order gPath idComp).1
    topoOrder_nonvacuous.1.1
example : IsLeastFixpoint seedCopyT (iter seedCopyT 4 bot) :=
  iter_bot_isLeastFixpoint_of_monotone_of_height_le kleene_nonvacuous.1 kleene_nonvacuous.2.1
example : IsGreatestFixpoint seedCopyT (iter seedCopyT 4 top) :=
  iter_top_isGreatestFixpoint_of_monotone_of_height_le kleene_nonvacuous.1
    kleene_nonvacuous.2.1
example : IsLeastFixpoint mixLfpT (bottomUpLfp mixLfpT idComp [1, 0] 2) :=
  let h := bottomUpLfp_nonvacuous
  bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
example : IsGreatestFixpoint mixGfpT (bottomUpGfp mixGfpT idComp [1, 0] 2) :=
  let h := bottomUpGfp_nonvacuous
  bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
example : Le (bottomUpLfp seedCopyT idComp [0, 1] 4) seedCopyPre :=
  let h := oneSided_nonvacuous
  bottomUpLfp_le_of_monotone_of_prefixpoint h.1 h.2.1 idComp [0, 1] 4
example : Le seedCopyPost (bottomUpGfp seedCopyT idComp [0, 1] 4) :=
  let h := oneSided_nonvacuous
  le_bottomUpGfp_of_monotone_of_postfixpoint h.1 h.2.2.2.1 idComp [0, 1] 4
example : HierSolution mixT idComp mixSign (bottomUp mixT idComp mixSign [1, 0] 2 bot) ∧
    ∀ σ, HierSolution mixT idComp mixSign σ → σ = bottomUp mixT idComp mixSign [1, 0] 2 bot :=
  let h := bottomUpHier_nonvacuous
  bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 mixSign bot
example : LexDecreasing (fun c : Fin 2 => 1 - c.val) idComp (fun _ x => x) cUnbounded ↔
    IntraDecrease idComp (fun _ x => x) cUnbounded ∧
      InterRankDecrease (fun c : Fin 2 => 1 - c.val) idComp cUnbounded :=
  lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks
    lexIff_nonvacuous.1
example : Terminates cUnbounded := terminates_of_lexDecreasing lexTerminates_nonvacuous
example : Terminates cUnbounded :=
  let h := terminationIntra_nonvacuous
  terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease h.1 h.2.2.1 h.2.2.2.1
example : Le seedCopyFix seedCopyPre :=
  let h := prefixPostfixSound_nonvacuous
  le_of_monotone_of_isLeastFixpoint_of_prefixpoint h.1 h.2.1 h.2.2.1
example : Le seedCopyPost seedCopyFix :=
  let h := prefixPostfixSound_nonvacuous
  le_of_monotone_of_isGreatestFixpoint_of_postfixpoint h.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
example : IsLeastFixpoint chainLfpT top :=
  let h := rankedCert_nonvacuous
  isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified h.1 h.2.1 h.2.2
example : RankedJustified chainLfpT top (kleeneRank chainLfpT) :=
  let h := rankedComplete_nonvacuous
  (prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint
    h.1 h.2.1).2.1

/-! ## Tightness counterexamples refute exactly the dropped hypothesis -/

-- scc-check
example : ¬ (3 - 1 ≤ 1) := fun h =>
  reachFrom_tight_fuel.2 (reachFrom_eq_true_iff_reach_of_pred_le gPath3 0 2 h)
-- scc-char
example : ¬ CondensationAcyclic gCycle idComp := fun h =>
  sccChar_tight_acyclic.2.2
    ((isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic gCycle idComp).2
      ⟨sccChar_tight_acyclic.1, h⟩)
example : ¬ BlocksMutuallyReachable gEmpty oneComp := fun h =>
  sccChar_tight_mutual.2.2
    ((isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic gEmpty oneComp).2
      ⟨h, sccChar_tight_mutual.1⟩)
-- kleene-bound
example : ¬ Monotone negT := fun h =>
  kleeneLfp_tight_monotone.2.2
    (iter_bot_isLeastFixpoint_of_monotone_of_height_le h kleeneLfp_tight_monotone.1)
example : ¬ (2 * 1 ≤ 1) := fun h =>
  kleeneLfp_tight_fuel.2.2
    (iter_bot_isLeastFixpoint_of_monotone_of_height_le kleeneLfp_tight_fuel.1 h)
example : ¬ Monotone negT := fun h =>
  kleeneGfp_tight_monotone.2.2
    (iter_top_isGreatestFixpoint_of_monotone_of_height_le h kleeneGfp_tight_monotone.1)
example : ¬ (2 * 1 ≤ 1) := fun h =>
  kleeneGfp_tight_fuel.2.2
    (iter_top_isGreatestFixpoint_of_monotone_of_height_le kleeneGfp_tight_fuel.1 h)
-- bottomup-lfp
example : ¬ Monotone negT := fun h =>
  let w := bottomUpLfp_tight_monotone
  w.2.2.2.2.2
    (bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      h w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1)
example : ¬ RespectsCalls gEmpty chainLfpT := fun h =>
  let w := bottomUpLfp_tight_respectsCalls
  w.2.2.2.2.2
    (bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 h w.2.1 w.2.2.1 w.2.2.2.1)
example : ¬ Covers (oneComp (n := 1)) [] := fun h =>
  let w := bottomUpLfp_tight_covers
  w.2.2.2.2.2
    (bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 w.2.1 h w.2.2.1 w.2.2.2.1)
example : ¬ CalleesFirst gPath idComp [0, 1] := fun h =>
  let w := bottomUpLfp_tight_calleesFirst
  w.2.2.2.2.2
    (bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 w.2.1 w.2.2.1 h w.2.2.2.1)
example : ¬ (2 * 1 ≤ 1) := fun h =>
  let w := bottomUpLfp_tight_fuel
  w.2.2.2.2.2.2
    (bottomUpLfp_isLeastFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 h)
-- bottomup-gfp
example : ¬ Monotone negT := fun h =>
  let w := bottomUpGfp_tight_monotone
  w.2.2.2.2.2
    (bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      h w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1)
example : ¬ RespectsCalls gEmpty chainGfpT := fun h =>
  let w := bottomUpGfp_tight_respectsCalls
  w.2.2.2.2.2
    (bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 h w.2.1 w.2.2.1 w.2.2.2.1)
example : ¬ Covers (oneComp (n := 1)) [] := fun h =>
  let w := bottomUpGfp_tight_covers
  w.2.2.2.2.2
    (bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 w.2.1 h w.2.2.1 w.2.2.2.1)
example : ¬ CalleesFirst gPath idComp [0, 1] := fun h =>
  let w := bottomUpGfp_tight_calleesFirst
  w.2.2.2.2.2
    (bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 w.2.1 w.2.2.1 h w.2.2.2.1)
example : ¬ (2 * 1 ≤ 1) := fun h =>
  let w := bottomUpGfp_tight_fuel
  w.2.2.2.2.2.2
    (bottomUpGfp_isGreatestFixpoint_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 h)
-- bottomup-one-sided
example : ¬ Monotone nmLfpT := fun h =>
  oneSidedLfp_tight_monotone.2.2
    (bottomUpLfp_le_of_monotone_of_prefixpoint h oneSidedLfp_tight_monotone.2.1 oneComp [0] 1)
example : ¬ Le (topT (bot : Summ 1 1)) bot := fun h =>
  oneSidedLfp_tight_prefixpoint.2.2
    (bottomUpLfp_le_of_monotone_of_prefixpoint oneSidedLfp_tight_prefixpoint.1 h oneComp [0] 1)
example : ¬ Monotone nmGfpT := fun h =>
  oneSidedGfp_tight_monotone.2.2
    (le_bottomUpGfp_of_monotone_of_postfixpoint h oneSidedGfp_tight_monotone.2.1 oneComp [0] 1)
example : ¬ Le (top : Summ 1 1) (botT top) := fun h =>
  oneSidedGfp_tight_postfixpoint.2.2
    (le_bottomUpGfp_of_monotone_of_postfixpoint oneSidedGfp_tight_postfixpoint.1 h oneComp [0] 1)
-- bottomup-mixed
example : ¬ Monotone negT := fun h =>
  let w := bottomUpHier_tight_monotone
  w.2.2.2.2.2
    (bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      h w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 (fun _ => true) bot)
example : ¬ RespectsCalls gEmpty chainLfpT := fun h =>
  let w := bottomUpHier_tight_respectsCalls
  w.2.2.2.2.2
    (bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 h w.2.1 w.2.2.1 w.2.2.2.1 (fun _ => true) bot)
example : ¬ Covers (oneComp (n := 1)) [] := fun h =>
  let w := bottomUpHier_tight_covers
  w.2.2.2.2.2
    (bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 w.2.1 h w.2.2.1 w.2.2.2.1 (fun _ => true) bot)
example : ¬ CalleesFirst gCycle idComp [0, 1] := fun h =>
  let w := bottomUpHier_tight_calleesFirst
  w.2.2.2.2.2
    (bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.1 w.2.1 w.2.2.1 h w.2.2.2.1 mixSign bot)
example : ¬ (2 * 1 ≤ 1) := fun h =>
  let w := bottomUpHier_tight_fuel
  w.2.2.2.2.2.2
    (bottomUp_hierSolution_and_unique_of_monotone_of_respectsCalls_of_covers_of_calleesFirst_of_height_le
      w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 h (fun _ => true) bot)
-- bottomup-mixed: betweenness lemma
example : Le bot mixResult ∧ Le mixResult top :=
  let h := hierBetween_nonvacuous
  le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint h.1 h.2.1 h.2.2.1
example : ¬ HierSolution chainLfpT idComp (fun _ => true) bot := fun h =>
  let w := hierBetween_tight_hierSolution
  w.2.2.2 (le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint w.1 w.2.1 h)
example : ¬ IsLeastFixpoint idT top := fun h =>
  let w := hierBetween_tight_least
  w.2.2.2 (le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint h w.2.1 w.2.2.1)
example : ¬ IsGreatestFixpoint idT bot := fun h =>
  let w := hierBetween_tight_greatest
  w.2.2.2 (le_and_le_of_hierSolution_of_isLeastFixpoint_of_isGreatestFixpoint w.1 h w.2.2.1)
-- lex-iff
example : ¬ (∀ f g : Fin 2, (fun _ : Fin 2 => 0) (idComp f) = (fun _ : Fin 2 => 0) (idComp g) →
    idComp f = idComp g) := fun h =>
  lexIff_tight_injective.2
    (lexDecreasing_iff_intraDecrease_and_interRankDecrease_of_rank_injective_on_used_blocks h)
example : ¬ LexDecreasing (fun _ : Fin 1 => 0) oneComp (fun _ (_ : Unit) => 0) cLoop := fun h =>
  lexTerminates_tight_lexDecreasing.2 (terminates_of_lexDecreasing h)
-- termination-intra
example : ¬ CondensationAcyclic gCycle idComp := fun h =>
  let w := terminationIntra_tight_acyclic
  w.2.2.2 (terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease h w.1 w.2.1)
example : ¬ CallsInGraph gEmpty cCycle := fun h =>
  let w := terminationIntra_tight_callsInGraph
  w.2.2.2 (terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease w.1 h w.2.1)
example : ¬ IntraDecrease oneComp (fun _ (_ : Unit) => 0) cLoop := fun h =>
  let w := terminationIntra_tight_intraDecrease
  w.2.2.2 (terminates_of_condensationAcyclic_of_callsInGraph_of_intraDecrease w.1 w.2.1 h)
-- prefix-postfix-sound
example : ¬ Monotone nmLfpT := fun h =>
  let w := prefixSound_tight_monotone
  w.2.2.2 (le_of_monotone_of_isLeastFixpoint_of_prefixpoint h w.2.1 w.2.2.1)
example : ¬ IsLeastFixpoint idT top := fun h =>
  let w := prefixSound_tight_least
  w.2.2.2 (le_of_monotone_of_isLeastFixpoint_of_prefixpoint w.1 h w.2.2.1)
example : ¬ Le (chainLfpT bot) bot := fun h =>
  let w := prefixSound_tight_prefixpoint
  w.2.2.2 (le_of_monotone_of_isLeastFixpoint_of_prefixpoint w.1 w.2.1 h)
example : ¬ Monotone nmGfpT := fun h =>
  let w := postfixSound_tight_monotone
  w.2.2.2 (le_of_monotone_of_isGreatestFixpoint_of_postfixpoint h w.2.1 w.2.2.1)
example : ¬ IsGreatestFixpoint idT bot := fun h =>
  let w := postfixSound_tight_greatest
  w.2.2.2 (le_of_monotone_of_isGreatestFixpoint_of_postfixpoint w.1 h w.2.2.1)
example : ¬ Le (top : Summ 2 1) (chainGfpT top) := fun h =>
  let w := postfixSound_tight_postfixpoint
  w.2.2.2 (le_of_monotone_of_isGreatestFixpoint_of_postfixpoint w.1 w.2.1 h)
-- ranked-cert
example : ¬ Monotone negT := fun h =>
  let w := rankedCert_tight_monotone
  w.2.2.2 (isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified h w.2.1 w.2.2.1)
example : ¬ Le (topT (bot : Summ 1 1)) bot := fun h =>
  let w := rankedCert_tight_prefixpoint
  w.2.2.2 (isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified w.1 h w.2.2.1)
example : ∀ r, ¬ RankedJustified idT top r := fun _r hr =>
  let w := rankedCert_tight_ranking
  w.2.2.2 (isLeastFixpoint_of_monotone_of_prefixpoint_of_rankedJustified w.1 w.2.1 hr)
-- ranked-cert-complete
example : ¬ Monotone nmRankT := fun h =>
  rankedComplete_tight_monotone.2.2
    (prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint h
      rankedComplete_tight_monotone.2.1)
example : ¬ IsLeastFixpoint idT top := fun h =>
  rankedComplete_tight_least.2.2.2
    (prefixpoint_and_rankedJustified_kleeneRank_lt_height_of_monotone_of_isLeastFixpoint
      rankedComplete_tight_least.1 h)

end Toy.Scc
