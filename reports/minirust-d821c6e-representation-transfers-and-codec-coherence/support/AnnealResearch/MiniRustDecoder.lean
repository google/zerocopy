import AnnealResearch.MiniRustReference
import AnnealResearch.Representation

/-!
Separately named transcription of MiniRust decode_ptr at
  d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed
spec/lang/representation.md:112-133 on its x86_64 little-endian 8-byte target.

This is an audited transcription assumption, not a verified import or a bridge
identifying the canonical decoder with MiniRust. The concrete comparisons call
the existing canonical decoder unchanged and exhibit its stricter behavior.
-/
namespace AnnealResearch.MiniRustDecoder

abbrev SourceByte := MiniRustReference.Byte
abbrev SourcePtr := MiniRustReference.Ptr
abbrev SourceFrag := MiniRustReference.Frag
abbrev Block := Fin 8 → SourceByte

/-- The caller's exact-length premise is enforced by Block's type. -/
def rawNumber : SourceByte → Option (Fin 256)
  | .uninit => none
  | .init number _ => some number

def rawFragment : SourceByte → Option SourceFrag
  | .uninit => none
  | .init _ fragment => fragment

def littleValue : List (Fin 256) → Nat
  | [] => 0
  | number :: rest => number.val + 256 * littleValue rest

/-- Physical byte positions are 0..7 in this fixed target. An incompatible
    fragment strips provenance; it never causes numeric decoding to fail. -/
def coherentProvenance (bytes : Block) : Option Nat :=
  let initial := (rawFragment (bytes ⟨0, by decide⟩)).map (fun fragment => fragment.allocId)
  (List.ofFn (fun index : Fin 8 => index)).foldl (fun acc index =>
    match rawFragment (bytes index) with
    | none => none
    | some fragment =>
      if fragment.position = index.val ∧ some fragment.allocId = acc then acc
      else none) initial

/-- MiniRust's initialized-data check precedes the provenance fold. -/
def decodeLE8 (bytes : Block) : Option SourcePtr := do
  let numbers ← (List.ofFn bytes).mapM rawNumber
  return { addr := littleValue numbers, provenance := coherentProvenance bytes }

def target8LE : Representation.Target :=
  { width := 8, width_pos := by decide, endian := .little }

/-- Inject source allocation IDs with fixed generation/tag zero. On LE8 the
    canonical significance index equals the source's physical fragment index.
    Out-of-range cells are uninit and neither selected decoder reads them. -/
def canonicalImage (bytes : Block) : Representation.Representation := fun index =>
  if inside : index < 8 then
    match bytes ⟨index, inside⟩ with
    | .uninit => .uninit
    | .init number fragment =>
      .init number (fragment.map fun frag =>
        { provenance := { allocation := frag.allocId, generation := 0, tag := 0 }
          significance := frag.position })
  else .uninit

/-- Actual canonical decoder, without replacing its coherence criterion. -/
def canonicalDecodeLE8 (bytes : Block) : Option (Representation.Ptr target8LE) :=
  Representation.decodePtr target8LE (canonicalImage bytes)

structure Observation where
  addr : Nat
  provenance : Option Nat
  deriving DecidableEq, Repr

def observeSource (decoded : Option SourcePtr) : Option Observation :=
  decoded.map fun pointer => ⟨pointer.addr, pointer.provenance⟩

/-- Concrete observations avoid asserting any equality between pointer types.
    No source decoder is called in this canonical comparison. -/
def observeCanonical (decoded : Option (Representation.Ptr target8LE)) :
    Option Observation :=
  decoded.map fun pointer =>
    { addr := littleValue (List.ofFn pointer.address)
      provenance := pointer.provenance.map Representation.Provenance.allocation }

def numericOne (index : Fin 8) : Fin 256 :=
  if index.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

def coherentBytes : Block := fun index =>
  .init (numericOne index) (some { allocId := 0, position := index.val })

/-- Initialized encoding of address 1. Byte 1 alone has no fragment. -/
def missingFragment : Block := fun index =>
  .init (numericOne index)
    (if index.val = 1 then none else some { allocId := 0, position := index.val })

/-- Initialized encoding of address 1. Byte 1 wrongly claims position 2. -/
def wrongPositionFragment : Block := fun index =>
  .init (numericOne index)
    (some { allocId := 0, position := if index.val = 1 then 2 else index.val })

def uniformNoProvenance : Block := fun index => .init (numericOne index) none

def withUninit : Block := fun index =>
  if index.val = 3 then .uninit else uniformNoProvenance index

 theorem missing_source_fallback :
    decodeLE8 missingFragment = some { addr := 1, provenance := none } := by
  decide

 theorem missing_canonical_failure :
    (canonicalDecodeLE8 missingFragment).isNone = true := by
  decide

 theorem wrong_position_source_fallback :
    decodeLE8 wrongPositionFragment = some { addr := 1, provenance := none } := by
  decide

 theorem wrong_position_canonical_failure :
    (canonicalDecodeLE8 wrongPositionFragment).isNone = true := by
  decide

 theorem missing_observations_differ :
    observeSource (decodeLE8 missingFragment) = some ⟨1, none⟩ ∧
    observeCanonical (canonicalDecodeLE8 missingFragment) = none := by
  decide

 theorem wrong_position_observations_differ :
    observeSource (decodeLE8 wrongPositionFragment) = some ⟨1, none⟩ ∧
    observeCanonical (canonicalDecodeLE8 wrongPositionFragment) = none := by
  decide

 theorem absent_provenance_agrees :
    observeSource (decodeLE8 uniformNoProvenance) = some ⟨1, none⟩ ∧
    observeCanonical (canonicalDecodeLE8 uniformNoProvenance) = some ⟨1, none⟩ := by
  decide

 theorem coherent_provenance_agrees :
    observeSource (decodeLE8 coherentBytes) = some ⟨1, some 0⟩ ∧
    observeCanonical (canonicalDecodeLE8 coherentBytes) = some ⟨1, some 0⟩ := by
  decide

 theorem uninit_fails_both :
    decodeLE8 withUninit = none ∧ (canonicalDecodeLE8 withUninit).isNone = true := by
  decide

/-- Shared numeric data and full initialized status do not imply equality of
    decoder acceptance. This is the specific mismatch, not a pointer bridge. -/
 theorem mixed_fragment_counterexample :
    (decodeLE8 missingFragment).isSome = true ∧
    (canonicalDecodeLE8 missingFragment).isSome = false := by
  decide

#print axioms missing_source_fallback
#print axioms missing_canonical_failure
#print axioms wrong_position_source_fallback
#print axioms wrong_position_canonical_failure
#print axioms missing_observations_differ
#print axioms absent_provenance_agrees
#print axioms coherent_provenance_agrees
#print axioms uninit_fails_both
#print axioms mixed_fragment_counterexample

end AnnealResearch.MiniRustDecoder
