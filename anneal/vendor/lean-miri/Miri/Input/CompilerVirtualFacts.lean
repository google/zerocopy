import Miri.Input.CompilerFactAdapters
import Miri.Input.CompilerVTableFacts
import Miri.Input.CompilerScopes
import Miri.Input.CompilerRuntimeQueries
import Miri.Interpreter.VirtualCalls

/-! Bind only exported, exact compilation-local compiler query evidence to
runtime virtual-call drivers. Unexported trait-principal/instance-rebasing/drop
queries remain required leaves in the original dictionary. -/
namespace Miri.Input.CompilerVirtualFacts
open Miri.ABI Miri.Interpreter
abbrev Result := Except String

def receiverKind (context : CompilerFacts.Context) (id : TypeId) : Result VirtualCalls.ReceiverKind := do
  let node ← context.runtime.node id |>.mapError toString
  unless node.shapeStatus == .supported do throw "virtual receiver compiler shape unresolved"
  match node.shapeKind with
  | .reference => pure .reference
  | .rawPointer => pure .rawPointer
  | .dynamicTraitObject => pure .dynamic
  | .unknown _ => throw "virtual receiver compiler shape unknown"
  | _ => pure .other

/-- The compiler exports predicates.principal() through the same bound
existential-predicate interner as trait checking. Missing legacy fields fail. -/
def dynamicData (prepared : CompilerFactAdapters.Prepared) (id : TypeId) :
    Result (Option VirtualCalls.DynamicData) := do
  let node ← prepared.context.runtime.node id |>.mapError toString
  unless node.shapeStatus == .supported do throw "dynamic type compiler shape unresolved"
  if node.shapeKind != .dynamicTraitObject then return none
  let token ← match ← CompilerFactAdapters.validityKind prepared id with
    | .dynamic token => pure token
    | _ => throw "dynamic predicate-array identity mismatch"
  let shape ← node.payload.getObjVal? "shape"
  let principal ← shape.getObjVal? "principal_predicate"
  let principal : Option Nat ← if principal == Lean.Json.null then pure none else do
    pure (some (← (← principal.getObjVal? "predicate_id").getNat?))
  return some ⟨token,principal⟩

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler virtual call query: {error}")

/-- Every installed query is backed by an actual fully-monomorphized compiler
record or canonical type/layout evidence. This does not solve instances or
construct a raw-pointer/ref type by searching for a same-sized layout. -/
def compilerHooks (prepared : CompilerFactAdapters.Prepared)
    (base : VirtualCalls.CompilerHooks S C) : VirtualCalls.CompilerHooks S C :=
  { base with
    classifyReceiver := fun ty => lift (receiverKind prepared.context ty)
    dynamicData := fun ty => lift (dynamicData prepared ty)
    fieldLayout := fun layout index => lift ((prepared.context.runtime.field layout index).mapError toString)
    structTailForCodegen := fun ty => lift (CompilerFacts.requiredType prepared.context ty "metadata_tail")
    builtinDeref := fun ty => lift (CompilerFacts.builtinDeref prepared.context ty true)
    layoutOf := fun ty => lift (CompilerFacts.layoutOf prepared.context ty)
    unitLayout := lift (CompilerFacts.unitLayout prepared.context) }

/-- Source inlinecallee attribute evidence is optional only when that full
instance does not occur in any inline scope. Conflicts/unresolved entries are
errors; they must not be hidden by a fallback query. -/
def inlineAttribute (prepared : CompilerScopes.Prepared) (fnInstance : CallInstance) : Result (Option Bool) := do
  let mut found := none
  for scopes in prepared.scopes do
    for outcome in scopes do
      if let .ok entry := outcome then
        if let some (callee,_) := entry.scope.inlined then
          if callee == fnInstance then
            let some value := entry.trackCaller | throw "inlinecallee attribute evidence missing"
            if let some previous := found then
              unless previous == value do throw "conflicting full-instance inlinecallee attributes"
            found := some value
  return found

/-- The canonical body key comes directly from the saved frame. Body equality
is only a consistency assertion after indexing, never a body lookup strategy.
A non-inlined instance's attribute still uses the mandatory base query. -/
def scopeHooks (prepared : CompilerScopes.Prepared) (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    sourceScope := fun identity _ body scope => do
      let actual ← lift (match prepared.program.bundle.bodies[identity.index]? with
        | some value => .ok value
        | none => .error "canonical frame body identity is absent")
      unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
      lift (CompilerScopes.sourceScope prepared identity.index scope)
    requiresCallerLocation := fun fnInstance => do
      match ← lift (inlineAttribute prepared fnInstance) with
      | some value => pure value
      | none => base.requiresCallerLocation fnInstance }

/-- Actual compiler Ty::new_mut_ptr/new_mut_ref, resolve_drop_glue and
requires_caller_location evidence. Missing keys fail; no structural type search
or synthetic function/ABI is introduced. -/
def runtimeHooks (prepared : CompilerRuntimeQueries.Prepared) (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    mutPointerType := fun ty => lift (CompilerRuntimeQueries.mutPointerType prepared ty)
    mutReferenceType := fun ty => lift (CompilerRuntimeQueries.mutReferenceType prepared ty)
    resolveDropGlue := fun ty => lift (CompilerRuntimeQueries.resolveDropGlue prepared ty)
    requiresCallerLocation := fun fnInstance => lift (CompilerRuntimeQueries.requiresCallerLocation prepared fnInstance) }

/-- Both type and vtable trait predicates consume the same compiler predicate
array table; no principal identity is synthesized from a diagnostic string. -/
def hooks (prepared : CompilerFactAdapters.Prepared) (base : VirtualCalls.Hooks P S C E) :
    VirtualCalls.Hooks P S C E :=
  { base with
    compiler := compilerHooks prepared base.compiler
    vtable := CompilerVTableFacts.hooks prepared base.vtable }

end Miri.Input.CompilerVirtualFacts
