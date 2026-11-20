import Miri.Input.CompilerProviders
import Miri.Input.CompilerDiscriminantFacts
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.ExecutionScalar
import Miri.Interpreter.ExecutionLeaves

/-! Direct scalar/discriminant compiler providers. Canonical query identities
select result types; physical null/provenance checks remain actual operations.
-/
namespace Miri.Input.CompilerScalarLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported e)
private def physical (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw e

def boolLayout (p : CompilerProviders.Prepared) (_ : C) : EStateM StepError S LocalLayout :=
  lift (p.primitiveLayout "bool")

def runtimeChecks (p : CompilerProviders.Prepared) (_ : C) (kind : MIR.RuntimeChecks) :
    EStateM StepError S Bool :=
  lift (CompilerIntrinsicFacts.runtimeChecks p.intrinsics kind)

def scalar (p : CompilerProviders.Prepared) : ExecutionScalar.Leaves S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { classify := fun _ ty => physical (CompilerExecutionProviders.scalarClass context ty)
    boolLayout := fun _ => lift (context.primitiveLayout "bool")
    orderingLayout := fun _ => lift context.orderingLayout
    overflowLayout := fun _ element => lift (context.runtime.overflowTupleLayout element |>.mapError toString)
    metadataLayout := fun _ ty => physical (CompilerExecutionProviders.metadataLayout context ty)
    unitLayout := fun _ => lift (CompilerFacts.unitLayout context) }

def discriminant (p : CompilerProviders.Prepared)
    (scalarMayBeNull : C → Scalar Provenance → RvalueM S Bool) :
    ExecutionLeaves.Discriminant S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { discriminantLayout := fun _ ty => lift (CompilerDiscriminantFacts.discriminantLayout context ty)
    tagLayout := fun _ tag => lift (CompilerDiscriminantFacts.tagLayout context tag)
    discriminantValue := fun _ ty index => lift (CompilerDiscriminantFacts.discriminantValue context ty index)
    variantForDiscriminant := fun _ ty bits => lift (CompilerDiscriminantFacts.variantForDiscriminant context ty bits)
    adtVariantCount := fun _ ty => lift (CompilerDiscriminantFacts.adtVariantCount context ty)
    scalarMayBeNull := scalarMayBeNull }
end Miri.Input.CompilerScalarLeaves
