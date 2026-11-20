import Miri.Interpreter.ExecutionChoices

/-! Named constructors for source execution choice tapes.

The strict finite tape remains the default input mode. `diagnosticTape` is an
explicit, bounded way to obtain one concrete, domain-valid diagnostic trace;
it is not an exploration of all source outcomes and makes no safety or
verification claim about other choices. Supplied inputs are always consumed
and validated as supplied, without falling back to generated choices. -/
namespace Miri.Input.ExecutionChoicePolicy
open Miri.Interpreter

/-- A strict finite tape. Exhaustion retains the source runner's existing
unknown-choice behavior. -/
def strictTape (inputs : Array ExecutionChoices.Input := #[]) : ExecutionChoices.Tape :=
  { inputs := inputs }

/-- Explicit bounded diagnostic source choices. `maxGeneratedChoices` bounds
the number of choices generated after the supplied prefix, and
`maxByteLength` bounds each generated random-byte vector before allocation. -/
def diagnosticTape (maxGeneratedChoices maxByteLength : Nat)
    (inputs : Array ExecutionChoices.Input := #[]) : ExecutionChoices.Tape :=
  { inputs := inputs,
    policy := .boundedDiagnostic maxGeneratedChoices maxByteLength }

/-- Explicit bounded diagnostic source choices selected by a deterministic
seeded stream. Generated values are appended to `inputs`, so the resulting
consumed tape is replayable. The seed chooses one trace only and does not
establish rand/Miri PRNG equivalence, uniformity, or safety for other traces. -/
def seededDiagnosticTape (maxGeneratedChoices maxByteLength : Nat) (seed : UInt64)
    (inputs : Array ExecutionChoices.Input := #[]) : ExecutionChoices.Tape :=
  { inputs := inputs,
    policy := .boundedSeededDiagnostic maxGeneratedChoices maxByteLength seed,
    diagnosticRngState := seed }

end Miri.Input.ExecutionChoicePolicy
