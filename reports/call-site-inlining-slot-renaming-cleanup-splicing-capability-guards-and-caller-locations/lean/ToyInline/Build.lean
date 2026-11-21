import ToyInline.Props

/-!
# Small constructors for concrete programs
-/

namespace Toy.Inline

def blk (stmts : List Stmt) (t : Term) (cl : Bool := false) : Block := ⟨stmts, t, cl⟩

/-- The scope table of a function without nested or inlined scopes. -/
def rootScopes : List Scope := [⟨none, none⟩]

def mkFn (n : Nat) (blocks : List Block) (caps : CapSet := []) (tc : Bool := false)
    (scopes : List Scope := rootScopes) : Fn :=
  ⟨n, caps, tc, blocks, scopes⟩

def mkCallInfo (g : FnId) (args : List Operand) (dest : Local) (target : Option BlockId)
    (u : Unwind) (span : Span := 0) (scope : ScopeId := 0) (abiSens : Bool := false) :
    CallInfo :=
  ⟨g, args, dest, target, u, span, scope, abiSens⟩

def mkCall (g : FnId) (args : List Operand) (dest : Local) (target : Option BlockId)
    (u : Unwind) (span : Span := 0) (scope : ScopeId := 0) (abiSens : Bool := false) : Term :=
  .call (mkCallInfo g args dest target u span scope abiSens)

def mkProg (fns : List Fn) (abi : CapSet → Bool := fun _ => false) : Program := ⟨fns, abi⟩

/-- A configuration differing from the canonical one only in the given fields. -/
def cfgWith (hostN : Nat) (slot : Option (Nat → Local) := none) (ret : Option RetMode := none)
    (redirect : Bool := true) (rm : ResumeMap := .unwind) (link : LinkRule := .rustc) :
    InlineCfg where
  slot := slot.getD (fun i => hostN + i)
  ret := ret.getD (.temp hostN)
  redirectContinue := redirect
  resumeMap := rm
  link := link

end Toy.Inline
