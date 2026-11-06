module

public import Dep
meta import Dep

-- With `meta import Dep`, BOTH `[Dep:meta-init]` AND `[Dep:runtime-init]` execute,
-- and `depPublicVal` can be evaluated at compile time inside `meta def`:
syntax (name := callNonMetaOk) "call_nonmeta_ok" : term

@[term_elab callNonMetaOk]
public meta def elabCallNonMetaOk : Lean.Elab.Term.TermElab := fun _ _ => do
  let n := depPublicVal
  IO.println s!"[ConsumerMetaImport] evaluated non-meta depPublicVal at comptime: {n}"
  return Lean.mkNatLit n

public def valFromMeta : Nat := call_nonmeta_ok
