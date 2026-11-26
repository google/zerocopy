-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
Census of kernel-cost and axiom-hygiene patterns in the bundled theory, run by
`tests/audit/tests/kernel_physics.rs` as
`lean --run <this file> <scan prefix> <modules>...`
against freshly compiled `.olean` files. It prints one tab-separated record per
finding; the Rust test owns the policy.

* `QUOT_ENTRY <init> <decl>`: scanned declaration `<decl>` refers directly to
  constant `<init>` from outside the scanned modules, and `Quot.sound` is in
  `<init>`'s dependency closure.
* `PTREE_FUN <decl>`: the type of `<decl>`, or its body if it is a definition,
  mentions a `PTree` (or `RawTree`) whose payload is a function type, possibly
  behind a type alias.
* `AST_REC <decl> <rec>`: the type or body of user-written `<decl>` applies a
  `Trusted.MirAst` recursor (`rec`, `recOn`, `brecOn`, or a nested `rec_N` or
  `brecOn_N`) at a nonzero universe level, i.e. with a motive into
  `Sort (u + 1)`, which includes both `Type` and `Prop`-valued predicates.
* `SPARSE <n>`: number of compiler-generated `_sparseCasesOn` helpers.
* `DECLS <n>`: number of declarations scanned.
-/

open Lean

def bodyOf? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def depsOf (ci : ConstantInfo) : Array Name :=
  let body := ((bodyOf? ci).map (·.getUsedConstants)).getD #[]
  (body.foldl (·.insert ·) (ci.type.getUsedConstants.foldl (·.insert ·) NameSet.empty)).toArray

/-- Names recorded in an imported persistent environment extension. The
extensions' lookup functions read state that `importModules` only fills in
with `loadExts := true`, but the per-module entries are always present. -/
def importedNames {α σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α α σ)
    (env : Environment) (name : α → Name) : NameSet :=
  (ext.toEnvExtension.getState env).importedEntries.foldl
    (fun acc mod => mod.foldl (fun acc e => acc.insert (name e)) acc) {}

/-- Generated-declaration metadata gathered once per environment. -/
structure GenInfo where
  matchers : NameSet
  auxRecursors : NameSet

/-- Whether Lean generated `n`. A generated declaration has no source range
(user-written declarations always do, whatever their name) and is one of: a
matcher, an auxiliary recursor, a reserved equation or unfolding lemma, a
`_sparseCasesOn` helper, or a matcher's splitter or equation lemma. Equation
lemmas realized privately in an Anneal module for a matcher defined elsewhere
carry a `_private` prefix, so the matcher checks also try the name with that
prefix removed. -/
def isGenerated (env : Environment) (gen : GenInfo) (n : Name) : Bool :=
  let isMatcher := fun p => gen.matchers.contains p || gen.matchers.contains (privateToUserName p)
  (declRangeExt.find? env n).isNone &&
    (gen.auxRecursors.contains n || isMatcher n || isReservedName env n ||
      isReservedName env (privateToUserName n) ||
      (Meta.getSparseCasesOnInfoCore env n).isSome ||
      match n with
      | .str p s =>
        isMatcher p &&
          (s == "splitter" || Meta.isEqnReservedNameSuffix s ||
            Meta.Match.isCongrEqnReservedNameSuffix s)
      | _ => false)

partial def reachesQuotSound (env : Environment)
    (memo : IO.Ref (Std.HashMap Name Bool)) (n : Name) : IO Bool := do
  if let some b := (← memo.get)[n]? then return b
  memo.modify (·.insert n false)
  let b ← if n == ``Quot.sound then pure true else
    match env.find? n with
    | some ci => (depsOf ci).anyM (reachesQuotSound env memo)
    | none => pure false
  memo.modify (·.insert n b)
  return b

/-- Whether `s` is `pfx` followed by `_` and a number, as in `rec_1`. -/
def isNumberedAux (pfx s : String) : Bool :=
  match s.dropPrefix? (pfx ++ "_") with
  | some rest => !rest.isEmpty && rest.all Char.isDigit
  | none => false

/-- Whether `c` names a recursor: `rec`, `recOn`, `brecOn`, or the auxiliary
`rec_N` and `brecOn_N` that nested inductives (such as `MirTy`, through
`List MirTy`) use for their nested occurrences. -/
def isRecursorName (c : Name) : Bool :=
  match c with
  | .str _ s =>
    ["rec", "recOn", "brecOn"].contains s || isNumberedAux "rec" s || isNumberedAux "brecOn" s
  | _ => false

/-- A `Trusted.MirAst` recursor applied at a nonzero universe level somewhere
in `e`, if any. `Expr.find?` caches visited subterms, so shared subterms are
visited once. -/
def astRec? (e : Expr) : Option Name :=
  (e.find? fun
    | .const c (u :: _) => (`Trusted.MirAst).isPrefixOf c && isRecursorName c && !u.isZero
    | _ => false).bind Expr.constName?

/-- Whether `t`, after its leading binders, is a sort: the type of a type
former such as `abbrev MapOf (α : Type) := PTree α`. -/
partial def endsInSort : Expr → Bool
  | .forallE _ _ b _ => endsInSort b
  | .mdata _ b => endsInSort b
  | .sort _ => true
  | _ => false

/-- One step of head reduction on a type: zeta-reduce a `let`, beta-reduce an
applied `fun`, or unfold an applied type-former definition (such as an
`abbrev`). Only type formers are unfolded, so ordinary definitions with large
bodies are never expanded. -/
def reduceTypeHead? (env : Environment) (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .letE _ _ v b _ => some (b.instantiate1 v)
  | e =>
    match e.getAppFn.consumeMData with
    | .lam .. => some (e.getAppFn.consumeMData.beta e.getAppArgs)
    | .const c us =>
      match env.find? c with
      | some (.defnInfo v) =>
        if endsInSort v.type then
          some ((v.value.instantiateLevelParams v.levelParams us).beta e.getAppArgs)
        else none
      | _ => none
    | _ => none

/-- Whether `e` is a function type, head-reducing it up to `fuel` times. -/
def isFunType (env : Environment) : Expr → (fuel : Nat := 4) → Bool
  | e, fuel =>
    e.consumeMData.isForall ||
      match fuel, reduceTypeHead? env e with
      | fuel + 1, some e' => isFunType env e' fuel
      | _, _ => false

/-- Whether `c` is `PTree` or `RawTree`, or a declaration in either type's
namespace (such as `PTree.empty`), whose first argument is the payload type.
Matches the full names, so other declarations in the `Anneal.PTree` module
namespace are not mistaken for trees. -/
def isPTreeConst (c : Name) : Bool :=
  let trees := [`Anneal.PTree.PTree, `Anneal.PTree.RawTree]
  trees.contains c || trees.contains c.getPrefix

/-- `e` with every `let` substituted into its body. Used on declared types,
which are small, so that `let`-bound type aliases are seen through. -/
partial def zetaAll : Expr → Expr
  | .letE _ _ v b _ => zetaAll (b.instantiate1 v)
  | .app f a => .app (zetaAll f) (zetaAll a)
  | .lam n t b bi => .lam n (zetaAll t) (zetaAll b) bi
  | .forallE n t b bi => .forallE n (zetaAll t) (zetaAll b) bi
  | .mdata d b => .mdata d (zetaAll b)
  | .proj s i b => .proj s i (zetaAll b)
  | e => e


/-- For a type-former definition such as `abbrev MapOf (α : Type) := PTree α`,
the indices of its parameters that reach a `PTree` payload, directly or through
other type formers (`abbrev State (α : Type) := Option (MapOf α)` gives
`{0}`). Computed once per constant and memoized. -/
partial def ptreeParams (env : Environment) (memo : IO.Ref (Std.HashMap Name (Array Nat)))
    (c : Name) : IO (Array Nat) := do
  if let some r := (← memo.get)[c]? then return r
  memo.modify (·.insert c #[])  -- cycle guard
  let r ← match env.find? c with
    | some (.defnInfo v) =>
      if endsInSort v.type then
        let (n, body) := stripLams v.value 0
        -- Eta-expand point-free aliases such as `abbrev M := PTree`, so that
        -- every parameter in the type is a bound variable of the body.
        let m := forallArity v.type
        let (n, body) :=
          if n < m then
            (m, mkAppN (body.liftLooseBVars 0 (m - n))
              ((Array.range (m - n)).map fun j => .bvar (m - n - 1 - j)))
          else (n, body)
        let hits ← collect (zetaAll body) n 0
        pure (hits.foldl (fun acc i => if acc.contains i then acc else acc.push i) #[])
      else pure #[]
    | _ => pure #[]
  memo.modify (·.insert c r)
  return r
where
  stripLams : Expr → Nat → Nat × Expr
    | .lam _ _ b _, n => stripLams b (n + 1)
    | e, n => (n, e)
  forallArity : Expr → Nat
    | .forallE _ _ b _ => forallArity b + 1
    | .mdata _ b => forallArity b
    | _ => 0
  /-- Parameter index of `e` if it is, or head-reduces within `fuel` steps to
  (as with `abbrev IdTy (α : Type) := α`), a bound variable naming one of the
  `n` parameters, under `depth` further binders. -/
  paramIdx? (e : Expr) (n depth : Nat) (fuel : Nat := 4) : Option Nat :=
    match e.consumeMData with
    | .bvar j => if j ≥ depth && j - depth < n then some (n - 1 - (j - depth)) else none
    | e =>
      match fuel, reduceTypeHead? env e with
      | fuel + 1, some e' => paramIdx? e' n depth fuel
      | _, _ => none
  collect (e : Expr) (n depth : Nat) : IO (Array Nat) := do
    let mut acc := #[]
    match e.getAppFn.consumeMData with
    | .const d _ =>
      let args := e.getAppArgs
      if isPTreeConst d && args.size > 0 then
        if let some i := paramIdx? args[0]! n depth then acc := acc.push i
      for j in ← ptreeParams env memo d do
        if h : j < args.size then
          if let some i := paramIdx? args[j] n depth then acc := acc.push i
    | _ => pure ()
    match e with
    | .app f a => return acc ++ (← collect f n depth) ++ (← collect a n depth)
    | .lam _ t b _ | .forallE _ t b _ =>
      return acc ++ (← collect t n depth) ++ (← collect b n (depth + 1))
    | .letE _ t v b _ =>
      return acc ++ (← collect t n depth) ++ (← collect v n depth) ++ (← collect b n (depth + 1))
    | .mdata _ b | .proj _ _ b => return acc ++ (← collect b n depth)
    | _ => return acc

/-- Whether `e` itself puts a function type in a `PTree` payload: either it
applies `PTree`, `RawTree`, or a declaration in their namespaces to a function
type, or it applies a type former to a function type at one of the
`ptreeParams` positions. -/
def isPTreeOfFunApp (env : Environment) (params : Std.HashMap Name (Array Nat))
    (e : Expr) : Bool :=
  match e.getAppFn.consumeMData with
  | .const c _ =>
    let args := e.getAppArgs
    (isPTreeConst c && args.size > 0 && isFunType env args[0]!) ||
      (params.getD c #[]).any fun i => i < args.size && isFunType env args[i]!
  | _ => false

/-- Whether any subterm of `e` puts a function type in a `PTree` payload,
directly or through type aliases. `Expr.find?` caches visited subterms, so
shared subterms are visited once. -/
def hasPTreeOfFun (env : Environment) (params : Std.HashMap Name (Array Nat))
    (e : Expr) : Bool :=
  (e.find? (isPTreeOfFunApp env params)).isSome

/-- Arguments: the module-name prefix to scan (for example `Anneal`), then the
modules to import. -/
def main (args : List String) : IO Unit := do
  let (scanPrefix, mods) := match args with
    | p :: ms => (p.toName, ms)
    | [] => (`Anneal, [])
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map ({ module := ·.toName })) {}
  let isAnneal := fun (n : Name) => match env.getModuleIdxFor? n with
    | some i => scanPrefix.isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let memo ← IO.mkRef ({} : Std.HashMap Name Bool)
  let gen : GenInfo := {
    matchers := importedNames Meta.Match.Extension.extension env (·.name)
    auxRecursors := importedNames auxRecExt env id }
  -- `ptreeParams` for every type-former definition, so that the per-subterm
  -- check below is a table lookup.
  let paramMemo ← IO.mkRef ({} : Std.HashMap Name (Array Nat))
  for (c, ci) in env.constants.toList do
    if let .defnInfo v := ci then
      if endsInSort v.type then discard <| ptreeParams env paramMemo c
  let params ← paramMemo.get
  let mut sparse := 0
  let mut decls := 0
  for (n, ci) in env.constants.toList do
    unless isAnneal n do continue
    decls := decls + 1
    if (Meta.getSparseCasesOnInfoCore env n).isSome then sparse := sparse + 1
    for c in depsOf ci do
      if !isAnneal c && (← reachesQuotSound env memo c) then
        IO.println s!"QUOT_ENTRY\t{c}\t{n}"
    let exprs := #[ci.type] ++ (bodyOf? ci).toArray
    -- Theorem bodies are proofs; data that stores functions in a `PTree` has to
    -- appear in some definition or declared type, so skip them for speed.
    -- `let`-bound aliases are substituted in types, and in the bodies of
    -- definitions of types, which are small.
    let dataExprs := #[zetaAll ci.type] ++
      if ci matches .thmInfo _ then #[]
      else (bodyOf? ci).toArray.map fun b => if endsInSort ci.type then zetaAll b else b
    if dataExprs.any (hasPTreeOfFun env params) then IO.println s!"PTREE_FUN\t{n}"
    unless isGenerated env gen n do
      if let some r := exprs.findSome? astRec? then
        IO.println s!"AST_REC\t{n}\t{r}"
  IO.println s!"SPARSE\t{sparse}"
  IO.println s!"DECLS\t{decls}"
