import Lean
import AllocatorShimsAndBoxDropSoundness

/-!
# Audit of `AllocatorShimsAndBoxDropSoundness`

Run after compiling `AllocatorShimsAndBoxDropSoundness.lean` to an `.olean` (see `check_lean.py`).
It inspects every constant that the module itself declares and fails if any of them

* is an axiom, an `opaque` constant, or a definition whose safety is not `safe` (which covers
  non-terminating and non-kernel-checked definitions and the compiler helpers named
  `_unsafe_rec`);
* has a name containing `_unsafe_rec`;
* is a theorem whose proof depends on an axiom other than `propext` and `Quot.sound`
  (so the placeholder axiom, the choice axiom and the native-evaluation axiom are all rejected).

On success it prints one JSON object with the counts, followed by the axiom dependencies of the
headline theorems.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_allocator_box" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `AllocatorShimsAndBoxDropSoundness
    | throwError "module AllocatorShimsAndBoxDropSoundness is not imported"
  let mut theorems := 0
  let mut definitions := 0
  let mut inductives := 0
  let mut constructors := 0
  let mut recursors := 0
  let mut total := 0
  let mut violations : Array String := #[]
  let mut axiomsSeen : Array Name := #[]
  let mut axiomFree := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some modIdx then continue
    total := total + 1
    if (n.toString.splitOn "_unsafe_rec").length > 1 then
      violations := violations.push s!"unsafe_rec helper: {n}"
    match ci with
    | .axiomInfo _ => violations := violations.push s!"axiom: {n}"
    | .opaqueInfo _ => violations := violations.push s!"opaque constant: {n}"
    | .quotInfo _ => violations := violations.push s!"quot constant: {n}"
    | .defnInfo d =>
      definitions := definitions + 1
      if d.safety != .safe then violations := violations.push s!"non-safe definition: {n}"
    | .thmInfo _ =>
      theorems := theorems + 1
      let axs ← collectAxioms n
      if axs.isEmpty then axiomFree := axiomFree + 1
      for a in axs do
        if !axiomsSeen.contains a then axiomsSeen := axiomsSeen.push a
        if !allowedAxioms.contains a then
          violations := violations.push s!"theorem {n} depends on axiom {a}"
    | .inductInfo _ => inductives := inductives + 1
    | .ctorInfo _ => constructors := constructors + 1
    | .recInfo _ => recursors := recursors + 1
  let axiomNames := axiomsSeen.toList.map (fun a => s!"\"{a}\"")
  let json := "{" ++ s!"\"constants\": {total}, \"theorems\": {theorems}, " ++
    s!"\"theorems_without_axioms\": {axiomFree}, \"definitions\": {definitions}, " ++
    s!"\"inductive_types\": {inductives}, \"constructors\": {constructors}, " ++
    s!"\"recursors\": {recursors}, \"axioms_used\": [{", ".intercalate axiomNames}], " ++
    s!"\"violations\": {violations.size}" ++ "}"
  logInfo m!"AUDIT {json}"
  unless violations.isEmpty do
    throwError "audit failed:\n{"\n".intercalate violations.toList}"

#audit_allocator_box

#print axioms AllocBox.dropWhere_ok_iff_sound
#print axioms AllocBox.no_field_left_of_sound_complete
#print axioms AllocBox.field_left_of_not_complete
#print axioms AllocBox.cleanup_selective_leak_free_exactly_once
#print axioms AllocBox.cleanup_uninit_frees_block_runs_no_destructor
#print axioms AllocBox.cleanup_uninit_leaves_written_fields
#print axioms AllocBox.full_drop_ub_of_missing_field
#print axioms AllocBox.full_drop_eq_selective_of_all_init
#print axioms AllocBox.dangling_address_nonzero_and_aligned
#print axioms AllocBox.zst_box_lifecycle_never_reaches_allocator
#print axioms AllocBox.rustDealloc_dangling_ub
#print axioms AllocBox.rustAlloc_zero_size_ub
#print axioms AllocBox.dealloc_event_has_matching_alloc
#print axioms AllocBox.rustDealloc_ok_iff
#print axioms AllocBox.double_dealloc_ub
#print axioms AllocBox.rustDealloc_mismatch_ub
#print axioms AllocBox.rustAlloc_wf
#print axioms AllocBox.rustDealloc_wf
#print axioms AllocBox.box_lifecycle_dealloc_layout_eq_alloc_layout
#print axioms AllocBox.boxFree_wrong_layout_ub
#print axioms AllocBox.boxNewUninit_oom
#print axioms AllocBox.Example.sizedRoundTrip_summary
#print axioms AllocBox.Example.moveFirstThenUnwind_summary
#print axioms AllocBox.Example.uninitMidInitUnwind_summary
#print axioms AllocBox.Example.zstRoundTrip_summary
#print axioms AllocBox.Example.ce1_full_drop_after_partial_move_or_uninit_ub
#print axioms AllocBox.Example.ce2_zst_or_mismatched_align_dealloc_ub
