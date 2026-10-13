/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelExportProducer
@[expose] public section

/-!
These consumer checks import, unfold, and inspect models produced in another
module. Successful and rejected decodings pin both calculation and admission;
the decomposition example exposes a child witness across the import boundary.
The axiom audit checks the exported decoder and bridge declarations themselves,
so successful elaboration cannot conceal an unchecked proof dependency.
-/

open AeneasSpecs Aeneas.Std
namespace ModelExportRegression
example (raw : Raw) : ∃ value, Raw.decode raw = some value := by
  simp [Raw.decode, Raw.decodeFields]
-- Consumer kernel checks must unfold proof-containing outputs across the import.
example : (Encoding.decode ⟨⟨13#usize⟩⟩).map (fun value => (value.align, value.phase)) =
    some (8, 5) := rfl
example : Encoding.decode ⟨⟨0#usize⟩⟩ = none := rfl
example : (Fallible.decode ⟨13#usize⟩).map (·.word) = some 12 := rfl
example : Fallible.decode ⟨0#usize⟩ = none := rfl
example (raw : Encoding) (value : Encoding.Value)
    (h : Encoding.decode raw = some value) :
    ∃ word, modelNonZeroUsize.decode raw.word = some word ∧
      Encoding.decodeFields ⟨word⟩ = some value := Encoding.decode_decompose raw value |>.mp h

run_meta do
  for owner in #[``Raw, ``Encoding, ``Fallible] do
    for suffix in #[`decodeFields, `decode, `aeneasModel, `decode_decompose] do
      let declName := owner ++ suffix
      for axiomName in ← Lean.collectAxioms declName do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Unexpected decoder axiom {axiomName} in {declName}"
end ModelExportRegression
