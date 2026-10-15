/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat, Arthur Adjedj
-/

-- inspired from https://github.com/leanprover/LNSym/blob/main/Arm/BitVec.lean

import Lean.Elab.Term
import Lean.Meta.Reduce
import Std.Tactic.BVDecide

open BitVec

/- Bitvector pattern component syntax category, originally written by
Leonardo de Moura. -/
declare_syntax_cat bvpat_comp
syntax num (":" (num <|> term))? : bvpat_comp
syntax (ident <|> "_") (":" (num <|> term))? : bvpat_comp

/--
Bitvector pattern syntax category.
Example: [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5]
-/
declare_syntax_cat bvpat
syntax num ("if" term)?: bvpat
syntax ident ("if" term)?: bvpat
syntax "[" bvpat_comp,* "]" ("if" term)? : bvpat

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

open Lean Elab Term

/-- Return the number of bits in a bit-vector component pattern. -/
def BVPatComp.length (c : BVPatComp) :TermElabM Nat := do
  match c with
  | `(bvpat_comp| $n:num $[: $_]?) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num)
  | `(bvpat_comp| _ : $n:num) =>
    return n.raw.toNat
  | `(bvpat_comp| $_:ident : $t:term)
  | `(bvpat_comp| _ : $t:term) =>(do
    let t ← elabTerm t none
    let t ← Meta.whnf t
    match_expr t with
      | BitVec n =>
        let n ← Meta.whnf n
        let some n := n.rawNatLit? | unreachable!
        return n
      | _ => throwError "Unexpected type: {indentExpr t}, expected a bitvector"
    )
  | `(bvpat_comp| $_:ident ) | `(bvpat_comp| _) =>
    return 1
  | _ => throwError "Unexpected syntax: {c}"

/--
If the pattern component is a bitvector literal, convert it into a bit-vector term
denoting it.
-/
def BVPatComp.toBVLit? (c : BVPatComp) : TermElabM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num $[: $_]?) =>
    let len ← c.length
    let some str := n.raw.isLit? `num | throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

/--
If the pattern component is a pattern variable of the form `<id>:<size>` return
`some id`.
-/
def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident $[: $_]?) =>
    return some x
  | _ => return none

def BVPat.getComponents (p : BVPat) : MacroM ((Array BVPatComp) × Option Term) :=
  match p with
  | `(bvpat|$n:num $[if $t:term]?) => do
    let n ← `(bvpat_comp|$n:num)
    return (#[n],t)
  | `(bvpat| [$comp,*] $[if $t]?) => return (comp.getElems.reverse,t)
  | _ => return (#[],none)

/--
Return the number of bits in a bit-vector pattern.
-/
def BVPat.length (p : BVPat) : TermElabM (Option Nat) := do
  if let `(bvpat|$_:ident $[if $_:term]?) := p then return none else
  let mut sz := 0
  for c in (← liftMacroM <| p.getComponents).1 do
    let n ← c.length
    sz := sz + n
  return some sz

/--
Given a variable `var` representing a term that matches the pattern `pat`, and a term `rhs`,
return a term of the form
```
let y₁ := var.extract ..
...
let yₙ := var.extract ..
rhs
```
where `yᵢ`s are the pattern variables in `pat`.
-/
def declBVPatVars (vars : Array Term) (pats : Array BVPat) (rhs : Term) : TermElabM Term := do
  let mut result := rhs
  for (pat, var) in pats.zip vars do
    if let `(bvpat|$i:ident $[if $t:term]?) := pat then
      result ← `(let $i := $var; $result)
      break
    let mut shift  := 0
    for c in (← liftMacroM <| pat.getComponents).1 do
      let len ← c.length
      if let some y ← liftMacroM <| c.toBVVar? then
        let rhs ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var)
        result ← `(let $y := $rhs; $result)
      shift := shift + len
  return result


/--
Return a term that evaluates to `true` if `var` is an instance of the pattern `pat`.
-/
def genBVPatMatchTest (vars : Array Term) (pats : Array BVPat): TermElabM Term := do
  if vars.size != pats.size then
    throwError "incorrect number of patterns"
  let mut result ← `(true)

  for (pat, var) in pats.zip vars do
    if let `(bvpat|$i:ident if $t:term) := pat then
      result ← `($result && (let $i := $var; $t:term))
      break
    let mut shift := 0
    let (cs,if') ← liftMacroM <| pat.getComponents
    for c in cs do
      let len ← c.length
      if let some bv ← c.toBVLit? then
        let test ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var == $bv)
        result ← `($result && $test)
      shift := shift + len
    if let some t := if' then
      let t ← declBVPatVars vars pats t
      result ← `($result && $t)
  return result

/--
Define the `match_bv .. with | bvpat => rhs | _ => rhs`.
The last entry is the `else`-case since we currently do not check whether
the patterns are exhaustive or not.
-/
syntax (name := matchBv) "match_bv " term,+ "with" (atomic("| " bvpat,+) " => " term)* ("| " "_ " " => " term)? : term

def checkBVPatLengths (lens : Array (Option Nat)) (pss : Array (Array BVPat)) : TermElabM Unit := do
    for (len, i) in lens.zipIdx do
      let mut patLen := none
      for ps in pss do
        unless ps.size == lens.size do
          throwError "Expected {lens.size} patterns, found {ps.size}"
        let p := ps[i]!
        let some pLen ← p.length | break

        -- compare the length to that of the type of the discriminant
        if let some pLen' := len then
          unless pLen == pLen' do
            throwErrorAt p "Expected pattern of length {pLen'}, found {pLen} instead"

        -- compare the lengths of the patterns
        if let some pLen' := patLen then
          unless pLen == pLen' do
            throwErrorAt  p "Patterns have differrent lengths"
        else
          patLen := some pLen

-- We use this to gather all the conditions expressing that the
-- previous pattern matches failed. This allows in turn to prove
-- exaustivity of the pattern matching.
abbrev dite_gather {α : Sort u} {old : Prop} (c : Prop) [h : Decidable c]
        (t : old ∧ c → α) (e : old ∧ ¬ c → α) (ho : old) : α :=
  if hc : c then
    t (And.intro ho hc)
  else
    e (And.intro ho hc)

@[term_elab matchBv]
partial
def elabMatchBv : TermElab := fun stx typ? =>
  match stx with
  | `(match_bv $[$discrs:term],* with
      $[ | $[$pss:bvpat],* => $rhss:term ]*
         $[| _ => $rhsElse?:term]?) => do
    let xs := discrs

    -- try to get the length of the BV to error-out
    -- if a pattern has the wrong length
    -- TODO: is it the best way to do that?
    let lens ← discrs.mapM (fun x => do
      let x ← elabTerm x none
      let typ ← Meta.inferType x
      match_expr typ with
      | BitVec n  =>
        let n ← Meta.reduce n
        match n with
        | .lit (.natVal n) => return some n
        | _ => return none
      | _ => return none)

    checkBVPatLengths lens pss

    let mut result :=
      ← if let some rhsElse := rhsElse? then
          `(Function.const _ $rhsElse)
        else
          `(fun _ => by try bv_decide -enums)

    for ps in pss.reverse, rhs in rhss.reverse do
      let test ← genBVPatMatchTest xs ps
      let rhs  ← declBVPatVars xs ps rhs
      result ← `(dite_gather $test (Function.const _ $rhs) $result)
    let res ← liftMacroM <| `($result True.intro)
    elabTerm res typ?
  | _ => throwError "invalid syntax"
