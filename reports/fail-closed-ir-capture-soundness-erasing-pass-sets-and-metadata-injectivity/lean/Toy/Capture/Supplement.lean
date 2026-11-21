import Toy.Capture.Examples
import Toy.Capture.Flags

/-!
# Supplementary examples (toy)

A negative example for the exempting source audit, and the fact that no sound
verifier for the `havoc` reading of `opaque` accepts UB-freedom of `qAsm`.
-/

namespace Toy.Capture

/-- Negative examples of `srcAuditExemptExternal`: it rejects a program consisting of
exactly one unsafe plain item, and a program consisting of exactly one non-external
macro whose expansion is unsafe. -/
theorem srcAuditExemptExternal_example_neg :
    srcAuditExemptExternal [.plain true] = false ∧
    srcAuditExemptExternal [.macro false [true]] = false := by
  decide

/-- Under the `havoc` reading of `opaque`, `qAsm` admits a run ending in UB (on input
`0`), so no verdict relation that is sound for `semV .havoc` accepts `ubFree` for
`qAsm`. -/
theorem qAsm_havoc_no_sound_verifier_accepts_ubFree :
    semV .havoc qAsm (0, ⟨[], .ub⟩) ∧
    ∀ verified : VProg → (Run → Prop) → Prop,
      VerifierSound (semV .havoc) verified → ¬ verified qAsm ubFree := by
  refine ⟨trivial, ?_⟩
  intro verified hV hver
  exact hV qAsm ubFree hver (0, ⟨[], .ub⟩) trivial rfl

end Toy.Capture
