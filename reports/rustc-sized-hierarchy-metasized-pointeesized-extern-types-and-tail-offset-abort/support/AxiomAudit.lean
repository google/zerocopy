import Lean
import SizedHierarchyAndExternTailSoundness

/-!
# Kernel-level audit of `SizedHierarchyAndExternTailSoundness`

Walks every declaration that the compiled module contributes to the environment
and fails (non-zero exit) unless all of the following hold:

* no theorem or definition depends on an axiom outside the allow-list
  (`propext`, `Quot.sound`); in particular none depends on the axiom of choice,
  on the proof-hole axiom, or on the compiled-evaluation trust axioms;
* the module declares no axiom and no opaque constant;
* no declaration is `unsafe` or `partial`, and no declaration name contains an
  `_unsafe_rec` component;
* every theorem named in `requiredTheorems` exists.

Run after compiling the module to an `.olean` (see `verify_lean.sh`).
-/

open Lean

namespace SizedHierarchyAxiomAudit

def moduleName : Name := `SizedHierarchyAndExternTailSoundness

def allowedAxioms : List Name := [``propext, ``Quot.sound]

def requiredTheorems : List Name := [
  `SizedHierarchyAndExternTailSoundness.sized_implies_metaSized,
  `SizedHierarchyAndExternTailSoundness.metaSized_implies_pointeeSized,
  `SizedHierarchyAndExternTailSoundness.every_type_is_pointeeSized,
  `SizedHierarchyAndExternTailSoundness.slice_is_metaSized_not_sized,
  `SizedHierarchyAndExternTailSoundness.foreign_is_pointeeSized_not_metaSized,
  `SizedHierarchyAndExternTailSoundness.thin_pointer_iff_not_strictly_metaSized,
  `SizedHierarchyAndExternTailSoundness.metaSized_implies_total_runtime_layout,
  `SizedHierarchyAndExternTailSoundness.not_metaSized_implies_no_runtime_layout,
  `SizedHierarchyAndExternTailSoundness.runtime_layout_total_iff_metaSized,
  `SizedHierarchyAndExternTailSoundness.size_of_val_total_under_questionSized,
  `SizedHierarchyAndExternTailSoundness.extern_tail_offset_static_iff,
  `SizedHierarchyAndExternTailSoundness.extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization,
  `SizedHierarchyAndExternTailSoundness.unpacked_foreign_tail_aborts_iff_not_static,
  `SizedHierarchyAndExternTailSoundness.packed1_foreign_tail_static_but_refused,
  `SizedHierarchyAndExternTailSoundness.specialized_projection_sound_and_complete,
  `SizedHierarchyAndExternTailSoundness.codegen_foreign_tail_value_is_true_offset,
  `SizedHierarchyAndExternTailSoundness.tree_borrows_reborrow_sound_without_pointee_size,
  `SizedHierarchyAndExternTailSoundness.tree_borrows_extern_mut_and_box_retag_is_nop,
  `SizedHierarchyAndExternTailSoundness.tree_borrows_lazy_permission_matches_true_extent,
  `SizedHierarchyAndExternTailSoundness.precise_tree_borrows_header_retag_unsupported_iff_nonzero_offset,
  `SizedHierarchyAndExternTailSoundness.stacked_borrows_skips_non_metaSized_pointee,
  `SizedHierarchyAndExternTailSoundness.ce1_question_sized_as_pointee_sized_panics_size_of_val,
  `SizedHierarchyAndExternTailSoundness.ce2_nonzero_prefix_extern_tail_requires_unknown_align,
  `SizedHierarchyAndExternTailSoundness.ce3_stacked_borrows_eager_retag_requires_byte_span
]

def hasUnsafeRecComponent (n : Name) : Bool :=
  n.components.any fun c => (c.toString.splitOn "_unsafe_rec").length > 1

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def audit : CoreM Unit := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? moduleName
    | throwError "module {moduleName} is not imported"
  let mut decls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      decls := decls.push (n, ci)
  let mut problems : Array String := #[]
  let mut axiomsUsed : Array Name := #[]
  let mut counts : Std.HashMap String Nat := {}
  let mut userTheorems := 0
  for (n, ci) in decls do
    let k := kindOf ci
    counts := counts.insert k (counts.getD k 0 + 1)
    if hasUnsafeRecComponent n then
      problems := problems.push s!"{n}: name has an _unsafe_rec component"
    if ci.isUnsafe then
      problems := problems.push s!"{n}: unsafe declaration"
    if ci.isPartial then
      problems := problems.push s!"{n}: partial declaration"
    match ci with
    | .axiomInfo _ => problems := problems.push s!"{n}: module declares an axiom"
    | .opaqueInfo _ => problems := problems.push s!"{n}: module declares an opaque constant"
    | _ => pure ()
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      if ci matches .thmInfo _ then
        if !n.isInternal then userTheorems := userTheorems + 1
      let axs ← collectAxioms n
      for a in axs do
        if !axiomsUsed.contains a then axiomsUsed := axiomsUsed.push a
        if !allowedAxioms.contains a then
          problems := problems.push s!"{n}: depends on disallowed axiom {a}"
    | _ => pure ()
  for t in requiredTheorems do
    match env.find? t with
    | some (.thmInfo _) => pure ()
    | _ => problems := problems.push s!"{t}: required theorem is missing"
  let sortedAxioms := axiomsUsed.qsort (fun a b => a.toString < b.toString)
  let kinds := ["theorem", "def", "inductive", "constructor", "recursor", "axiom", "opaque"]
  let summary := ", ".intercalate (kinds.map fun k => s!"{k}={counts.getD k 0}")
  logInfo m!"AUDIT module={moduleName} declarations={decls.size} ({summary})"
  logInfo m!"AUDIT user_theorems={userTheorems} required_theorems_checked={requiredTheorems.length}"
  logInfo m!"AUDIT axioms_used={sortedAxioms}"
  if problems.isEmpty then
    logInfo m!"AUDIT RESULT: PASS (0 disallowed axioms, 0 axioms declared, 0 opaque, 0 unsafe, 0 partial, 0 _unsafe_rec)"
  else
    for p in problems do
      logError m!"AUDIT PROBLEM: {p}"
    throwError "AUDIT RESULT: FAIL ({problems.size} problem(s))"

end SizedHierarchyAxiomAudit

run_cmd Lean.Elab.Command.liftCoreM SizedHierarchyAxiomAudit.audit

#print axioms SizedHierarchyAndExternTailSoundness.metaSized_implies_total_runtime_layout
#print axioms SizedHierarchyAndExternTailSoundness.extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization
#print axioms SizedHierarchyAndExternTailSoundness.extern_tail_offset_static_iff
#print axioms SizedHierarchyAndExternTailSoundness.tree_borrows_reborrow_sound_without_pointee_size
#print axioms SizedHierarchyAndExternTailSoundness.ce1_question_sized_as_pointee_sized_panics_size_of_val
#print axioms SizedHierarchyAndExternTailSoundness.ce2_nonzero_prefix_extern_tail_requires_unknown_align
#print axioms SizedHierarchyAndExternTailSoundness.ce3_stacked_borrows_eager_retag_requires_byte_span
