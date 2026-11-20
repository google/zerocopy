import Miri.MIR.Syntax

/-! Canonical source-shaped function instance identity from pinned
`rustc_middle/src/ty/instance.rs`. Saved frames retain every shim kind and
payload; a definition ID alone is not function-instance identity. -/
namespace Miri.Interpreter
open Miri.MIR

inductive CallReifyReason where
  | FnPtr | Vtable
  deriving Repr, DecidableEq

/-- All variants and payloads of pinned `ty::ShimKind`. -/
inductive CallShimKind where
  | VTable (definition : DefId)
  | Reify (definition : DefId) (reason : Option CallReifyReason)
  | FnPtr (definition : DefId) (ty : TyId)
  | ClosureOnce (callOnce closure : DefId) (trackCaller : Bool)
  | ConstructCoroutineInClosure (definition : DefId) (receiverByRef : Bool)
  | ThreadLocal (definition : DefId)
  | FutureDropPoll (definition : DefId) (proxy impl : TyId)
  | DropGlue (definition : DefId) (ty : Option TyId)
  | Clone (definition : DefId) (ty : TyId)
  | FnPtrAsPtr (definition : DefId) (ty : TyId)
  | FnPtrFromPtr (definition : DefId) (ty : TyId)
  | AsyncDropGlueCtor (definition : DefId) (ty : TyId)
  | AsyncDropGlue (definition : DefId) (ty : TyId)
  deriving Repr, DecidableEq

inductive CallInstanceKind where
  | Item (definition : DefId)
  | Intrinsic (definition : DefId)
  | LlvmIntrinsic (definition : DefId)
  | Virtual (definition : DefId) (index : Nat)
  | Shim (shim : CallShimKind)
  deriving Repr, DecidableEq

structure CallInstance where
  kind : CallInstanceKind
  args : Array GenericArg
  deriving Repr, DecidableEq

namespace CallShimKind

/-- Pinned `ShimKind::def_id`: ClosureOnce selects call_once, not closure. -/
def defId : CallShimKind → DefId
  | .VTable definition | .Reify definition _ | .FnPtr definition _
  | .ClosureOnce definition _ _ | .ConstructCoroutineInClosure definition _
  | .ThreadLocal definition | .FutureDropPoll definition _ _
  | .DropGlue definition _ | .Clone definition _ | .FnPtrAsPtr definition _
  | .FnPtrFromPtr definition _ | .AsyncDropGlueCtor definition _
  | .AsyncDropGlue definition _ => definition

end CallShimKind

namespace CallInstanceKind

def defId : CallInstanceKind → DefId
  | .Item definition | .Intrinsic definition | .LlvmIntrinsic definition
  | .Virtual definition _ => definition
  | .Shim shim => shim.defId

end CallInstanceKind

namespace CallInstance

def defId (self : CallInstance) : DefId := self.kind.defId

end CallInstance

end Miri.Interpreter
