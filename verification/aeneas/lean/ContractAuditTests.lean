/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import SpecsSyntax
public import RequiredContracts
@[expose] public section

/-!
These adversarial families test the audits themselves. A family can agree with
a concrete specification yet ignore its outcome, add a premise, or hide the
extracted call in a helper's body or type. Each case below isolates one escape
route and checks its rejection. A wrong arbitrary return separately demonstrates
why narrowing the authored domain cannot imply a broader required promise.
-/

open Lean Aeneas Aeneas.Std AeneasSpecs
namespace ContractAuditTests

def identity (n : Nat) : Result Nat := .ok n

-- Concrete specialization can be correct even when a family ignores run.
@[aeneas_spec] abbrev ignored : Prop :=
  ∀ n : Nat, WP.spec (identity n) (fun output => output = n)
def ignored_contract (n : Nat) (_run : Result Nat) : Prop :=
  WP.spec (identity n) (fun output => output = n)
example : ∀ n : Nat, ignored_contract n (identity n) := by
  intro n
  exact WP.spec.ret rfl
/-- error: Abstract contract ContractAuditTests.ignored_contract does not use its execution outcome -/
#guard_msgs in
run_elab AeneasSpecs.checkSpecContract `ContractAuditTests.ignored

-- The family audit retains every premise of the authored contract.
@[aeneas_spec] abbrev narrowed : Prop :=
  ∀ n : Nat, WP.spec (identity n) (fun output => output = n)
def narrowed_contract (n : Nat) (run : Result Nat) : Prop :=
  n = 0 → WP.spec run (fun output => output = n)
/-- error: Abstract contract ContractAuditTests.narrowed_contract changed the specification's premises or postcondition -/
#guard_msgs in
run_elab AeneasSpecs.checkSpecContract `ContractAuditTests.narrowed

-- A narrowed authored domain does not imply a broader independent guarantee.
@[aeneas_spec] abbrev conditional : Prop :=
  ∀ n : Nat, n = 0 → WP.spec (identity n) (fun output => output = n)
def conditional_contract (n : Nat) (run : Result Nat) : Prop :=
  n = 0 → WP.spec run (fun output => output = n)
def broad_contract (n : Nat) (run : Result Nat) : Prop :=
  WP.spec run (fun output => output = n)
def broad : Prop := ∀ n : Nat, broad_contract n (identity n)
theorem conditional_proved : conditional := by
  intro n _
  exact WP.spec.ret rfl
theorem broad_proved : broad := by
  intro n
  exact WP.spec.ret rfl
run_elab AeneasSpecs.checkSpecContract `ContractAuditTests.conditional
example : (contract_adequacy% conditional implies broad) =
    (∀ n run, conditional_contract n run → broad_contract n run) := rfl
-- This is the exact type required by check_contract, with an explicit witness
-- showing why a concrete proof of identity cannot repair the missing domain.
theorem narrowing_fails_required_domain :
    ¬ (contract_adequacy% conditional implies broad) := by
  intro adequate
  have rejected := adequate 1 (.ok 2) (by intro impossible; contradiction)
  simp only [broad_contract, WP.spec_ok] at rejected
  contradiction

-- Independent expected families must also retain the abstract outcome.
def ignoredExpected_contract (n : Nat) (_run : Result Nat) : Prop :=
  WP.spec (identity n) (fun output => output = n)
def ignoredExpected : Prop :=
  ∀ n : Nat, ignoredExpected_contract n (identity n)
/-- error: Independent contract ContractAuditTests.ignoredExpected_contract must use its execution outcome -/
#guard_msgs in
run_elab do
  let _ ← AeneasContracts.contractAdequacyType
    `ContractAuditTests.conditional `ContractAuditTests.ignoredExpected

-- Outcome use alone does not protect against an embedded implementation proof.
-- Hide the call behind a helper to exercise the transitive dependency audit.
def hiddenCall (n : Nat) : Result Nat := identity n
def embeddedExpected_contract (n : Nat) (run : Result Nat) : Prop :=
  WP.spec run (fun output => output = n) ∧
    WP.spec (hiddenCall n) (fun output => output = n)
def embeddedExpected : Prop :=
  ∀ n : Nat, embeddedExpected_contract n (identity n)
/-- error: Independent contract ContractAuditTests.embeddedExpected_contract depends on its extracted operation -/
#guard_msgs in
run_elab do
  let _ ← AeneasContracts.contractAdequacyType
    `ContractAuditTests.conditional `ContractAuditTests.embeddedExpected

-- An opaque helper can retain the operation only in its unreduced type. Its
-- body is Nat.zero, so checking bodies alone misses this dependency.
opaque typeOnlyHelper : (fun _ : Result Nat => Nat) (identity 0) := Nat.zero

def typeOnlyExpected_contract (n : Nat) (run : Result Nat) : Prop :=
  WP.spec run (fun output => output = Nat.add n typeOnlyHelper)
def typeOnlyExpected : Prop :=
  ∀ n : Nat, typeOnlyExpected_contract n (identity n)
/-- error: Independent contract ContractAuditTests.typeOnlyExpected_contract depends on its extracted operation -/
#guard_msgs in
run_elab do
  let _ ← AeneasContracts.contractAdequacyType
    `ContractAuditTests.conditional `ContractAuditTests.typeOnlyExpected

end ContractAuditTests
