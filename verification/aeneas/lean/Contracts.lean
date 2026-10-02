/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public meta import Lean
public section

open Lean Aeneas Aeneas.Std

namespace AeneasContracts

declare_syntax_cat contractRequirement
syntax "requires " ident " : " term : contractRequirement

/-- A total contract establishes successful termination and its postcondition.
Each named requirement becomes a proposition-valued theorem parameter.
Output binders use Aeneas's existing tuple-aware specification notation. -/
syntax "contract " ident bracketedBinder* " for " term
  contractRequirement* " ensures " term+ " => " term
  " proof:" tacticSeq : command

/-- A partial contract permits divergence, but still excludes failure.
Successful results must satisfy the postcondition. -/
syntax "partial " "contract " ident bracketedBinder* " for " term
  contractRequirement* " ensures " term+ " => " term
  " proof:" tacticSeq : command

/-- Refinement through a pure mathematical view. Optional `ensures` facts
remain facts about the concrete output, alongside the view equality. -/
syntax "contract " ident bracketedBinder* " for " term
  contractRequirement* " refines " term " to " term
  (" ensures " ident " => " term)? " proof:" tacticSeq : command

syntax "partial " "contract " ident bracketedBinder* " for " term
  contractRequirement* " refines " term " to " term
  (" ensures " ident " => " term)? " proof:" tacticSeq : command

private meta def requirementBinders (requirements : Array Syntax) :
    MacroM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :=
  requirements.mapM fun requirement => do
    match requirement with
    | `(contractRequirement| requires $id:ident : $pre:term) =>
      `(bracketedBinder| ($id : ($pre : Prop)))
    | _ => Macro.throwUnsupported

macro_rules
  | `(contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* refines $view:term to $model:term
      proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* :
      $call ⦃ r => $view r = $model ⦄ := by $body)
  | `(contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* refines $view:term to $model:term
      ensures $r:ident => $post:term proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* :
      $call ⦃ $r => $view $r = $model ∧ $post ⦄ := by $body)
  | `(partial contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* refines $view:term to $model:term
      proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* :
      $call ⦃ r => $view r = $model ⦄div := by $body)
  | `(partial contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* refines $view:term to $model:term
      ensures $r:ident => $post:term proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* :
      $call ⦃ $r => $view $r = $model ∧ $post ⦄div := by $body)
  | `(contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* ensures $x => $post:term
      proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* : $call ⦃ $x => $post ⦄ := by $body)
  | `(contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* ensures $x $xs:term* => $post:term
      proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* : $call ⦃ $x $xs* => $post ⦄ := by $body)
  | `(partial contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* ensures $x => $post:term
      proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* : $call ⦃ $x => $post ⦄div := by $body)
  | `(partial contract $id:ident $args:bracketedBinder* for $call:term
      $requirements:contractRequirement* ensures $x $xs:term* => $post:term
      proof: $body:tacticSeq) => do
    let premises ← requirementBinders requirements
    `(theorem $id $args* $premises* : $call ⦃ $x $xs* => $post ⦄div := by $body)

end AeneasContracts
