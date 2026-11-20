import Miri.Input.RuntimeArrayTypes
import Miri.Interpreter.OsStrings
import Miri.Interpreter.ValidityVisitor

/-! Stateful consumers of canonical runtime array constructors. The accessors
must refer to one persistent interpreter World; reconstruction per call loses
canonical allocation of type identities. Memory/host actions remain unchanged.
-/
namespace Miri.Input.RuntimeArrayQueries
open Miri.ABI Miri.Interpreter
structure Access (S : Type) where
  get : S → RuntimeArrayTypes.World
  set : S → RuntimeArrayTypes.World → S
private def failure : RuntimeArrayTypes.Error → StepError
  | .metadata reason => .unsupported s!"runtime array compiler metadata: {reason}"
  | .missingRuntimeType id => .unsupported s!"missing canonical runtime array type {id}"
  | error => .invalidProgram s!"runtime array constructor/layout: {reprStr error}"
private def lift (value : Except RuntimeArrayTypes.Error A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (failure error)

/-- Canonical constructor provider for EntryArguments and other runtime-sized
arrays, using the actual supplied element type identity and persistent World. -/
def arrayLayout (access : Access S) (element : MIR.TyId) (count : UInt64) :
    EStateM StepError S LocalLayout := do
  let state ← get
  let (layout,world) ← lift (RuntimeArrayTypes.internElement (access.get state) element count)
  set (access.set state world)
  pure layout

def osStringsHooks (access : Access S) (base : OsStrings.Hooks P S Os Kind) :
    OsStrings.Hooks P S Os Kind :=
  { base with arrayLayout := fun wide count => do
      let state ← get
      let (layout,world) ← lift (RuntimeArrayTypes.osStringArray (access.get state) wide count)
      set (access.set state world)
      pure layout }

def layoutOf (access : Access S) (id : MIR.TyId) : EStateM StepError S LocalLayout := do
  lift (RuntimeArrayTypes.lookup (access.get (← get)) id)

/-- Source array field type is the constructor's element type. This does not
infer an element from a stride, size, memory content or diagnostic spelling. -/
def fieldLayout (access : Access S) (base : LocalLayout → Nat → EStateM StepError S LocalLayout)
    (parent : LocalLayout) (index : Nat) : EStateM StepError S LocalLayout := do
  let world := access.get (← get)
  if world.entries.any (·.value.ty == parent.ty) then
    unless (← lift (RuntimeArrayTypes.lookup world parent.ty)) == parent do
      throw (.invalidProgram "canonical runtime array layout/type mismatch")
    lift (RuntimeArrayTypes.fieldLayout world parent.ty index)
  else base parent index

private def triviallyFreeze (world : RuntimeArrayTypes.World) (id : MIR.TyId) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    match world.entries.find? (·.value.ty == id) with
    | some entry => match entry.key.element with
      | .u8 | .u16 => true
      | .compiler element => triviallyFreeze world element fuel
    | none => match world.metadata.node id with
      | .error _ => false
      | .ok source => source.shapeStatus == .supported && match source.shapeKind with
        | .int | .uint | .float | .bool | .char | .str | .never | .reference
        | .rawPointer | .functionDefinition | .functionPointer | .errorType => true
        | _ => false

/-- Bind classification for interned arrays; all other compiler leaves remain
mandatory. Portable memory/validation actions still execute in the base hooks. -/
def validityHooks (access : Access S) (base : ValidityVisitor.Hooks P S C E Fn Abi Pad) :
    ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  { base with
    classify := fun choice ty => do
      let world := access.get (← get)
      if world.entries.any (·.value.ty == ty) then
        let (_,element) ← lift (RuntimeArrayTypes.arrayInfo world ty)
        pure (.sequence element.ty)
      else base.classify choice ty
    isFreeze := fun choice ty => do
      let world := access.get (← get)
      if world.entries.any (·.value.ty == ty) then
        -- Source's trivial-freeze path recurses through constructed arrays
        -- and accepts primitive scalars/references/pointers. Other element
        -- families still require the real compiler Freeze query.
        if triviallyFreeze world ty (world.entries.size + world.metadata.source.types.size + 1) then
          pure true
        else base.isFreeze choice ty
      else base.isFreeze choice ty }
end Miri.Input.RuntimeArrayQueries
