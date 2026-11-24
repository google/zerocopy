import HintAssumeBlackBoxAndInlineAttrsSoundness
import Lean

open Lean

#print axioms VerifiedRustcHintInline.constFoldExpr_sound
#print axioms VerifiedRustcHintInline.plainAddTwoThree_folds
#print axioms VerifiedRustcHintInline.boxedAddTwoThree_blocked
#print axioms VerifiedRustcHintInline.plain_and_boxed_same_runtime_value
#print axioms VerifiedRustcHintInline.exported_always_then_never_emits_both_diags
#print axioms VerifiedRustcHintInline.exported_never_then_always_skips_export_warning
#print axioms VerifiedRustcHintInline.abortOnFalse_soundly_refines_ubOnFalse
#print axioms VerifiedRustcHintInline.precompiled_core_o0_vs_opt1_boundary
#print axioms VerifiedRustcHintInline.assume_dead_branch_pruning_prog_sound
#print axioms VerifiedRustcHintInline.assume_pruning_without_contradiction_unsound
#print axioms VerifiedRustcHintInline.norm32_ne_zero_implies_add_one_ne_one
#print axioms VerifiedRustcHintInline.prune_unreachable_branch_range_excludes_one
#print axioms VerifiedRustcHintInline.blackBox_observational_identity
#print axioms VerifiedRustcHintInline.blackBox_statement_blocks_fold_while_preserving_outcome
#print axioms VerifiedRustcHintInline.fnAttrs_observational_equivalence_invariance
#print axioms VerifiedRustcHintInline.inlineCallOnce_sound
#print axioms VerifiedRustcHintInline.end_to_end_opt_and_refinement

#eval show MetaM Unit from do
  let env ← getEnv
  let mut theoremCount := 0
  let mut defCount := 0
  let mut violations := 0
  for (name, cinfo) in env.constants.map₁.toList do
    let s := name.toString
    if s.startsWith "VerifiedRustcHintInline." then
      if s.endsWith "._unsafe_rec" then
        IO.println s!"unsafe_rec helper: {s}"
        violations := violations + 1
      match cinfo with
      | .axiomInfo _ =>
          IO.println s!"axiom constant: {s}"
          violations := violations + 1
      | .opaqueInfo _ =>
          IO.println s!"opaque constant: {s}"
          violations := violations + 1
      | .quotInfo _ =>
          IO.println s!"quot constant: {s}"
          violations := violations + 1
      | .thmInfo _ =>
          theoremCount := theoremCount + 1
          let axioms ← collectAxioms name
          for ax in axioms do
            if ax != ``propext && ax != ``Quot.sound then
              IO.println s!"theorem {s} depends on forbidden axiom: {ax}"
              violations := violations + 1
      | .defnInfo val =>
          defCount := defCount + 1
          if val.safety != .safe then
            IO.println s!"non-safe definition: {s}"
            violations := violations + 1
      | _ => pure ()
  IO.println ("AUDIT {\"theorem_count\": " ++ toString theoremCount ++ ", \"def_count\": " ++ toString defCount ++ ", \"violations\": " ++ toString violations ++ "}")
