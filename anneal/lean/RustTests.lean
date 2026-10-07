/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
This module checks that the shared geometry is usable independently of a
frontend. Concrete examples exercise boundary behavior; parameterized examples
check that callers can use the universal lemmas without reproducing their proofs.
Lean checks each `example` as a theorem. `by decide` computes the small concrete
proposition and supplies a proof; it is not an unchecked runtime assertion.

The final command audits the assumptions of every compiled library declaration.
An abstract mathematical library should not acquire a Rust correspondence axiom
merely because one frontend needs that premise for its own operations.
-/

-- Cover a valid minimal alignment, exact multiples, padding, and empty objects.
-- Alignment zero is deliberately tested as an input to the total formula, not
-- admitted as a Rust alignment.
example : Rust.IsAlignment 1 := Rust.alignment_one
example : Rust.IsAlignment 16 := ⟨by decide, 4, by decide⟩
example : Rust.roundUpToAlign 0 8 = 0 := by decide
example : Rust.roundUpToAlign 9 8 = 16 := by decide
example : Rust.roundUpToAlign 16 8 = 16 := by decide
example : Rust.roundUpToAlign 9 0 = 0 := by decide
example (n a : Nat) (ha : 0 < a) : n ≤ Rust.roundUpToAlign n a :=
  Rust.roundUpToAlign_ge n a ha
example (a : Rust.Allocation) (addr : Nat) (h : a.addresses addr) :
    addr - a.base < a.size := a.offset_lt_size addr h
example (r : Rust.Referent) (a : Rust.Allocation) (h : Rust.FitsInAllocation r a)
    (addr : Nat) (ha : r.addresses addr) : addr < a.base + a.size :=
  Rust.FitsInAllocation.address_bounds_alloc r a h addr ha

-- These commands make representative dependencies visible in build output.
-- The complete audit below enforces the policy, including for unused helpers.
#print axioms Rust.roundUpToAlign_ge
#print axioms Rust.Allocation.offset_lt_size
#print axioms Rust.FitsInAllocation.address_bounds_alloc

-- Frontends can keep historical names as reducible aliases. Check that an
-- explicit unfolding through such a name still exposes the arithmetic; existing
-- proofs should not need to change their simplification lists after the move.
namespace Compatibility
abbrev roundUpToAlign := Rust.roundUpToAlign
example (v a : Nat) : roundUpToAlign v a = ((v + a - 1) / a) * a := by
  simp only [roundUpToAlign]
end Compatibility

-- `run_cmd` executes while Lean elaborates this file. Run it through
-- `lake env lean RustTests.lean` when the audit must run even if Lake could reuse
-- a previously compiled test module.
run_cmd do
  let env ← Lean.getEnv
  -- Select declarations by the module that defined them, not by namespace.
  -- A helper outside `Rust` still belongs to this library. Keep this roster in
  -- step with the library modules, and reject a missing import rather than
  -- accidentally auditing only part of the package.
  let libraryModules := #[`Rust, `Rust.Layout, `Rust.Memory, `Rust.Bytes, `Rust.Arithmetic]
  let owners ← libraryModules.mapM fun moduleName => do
    let some owner := env.getModuleIdx? moduleName
      | throwError "Shared library module was not imported: {moduleName}"
    pure owner
  -- Permit Lean's standard logical axioms only. The transitive dependency
  -- collection also catches an imported forbidden axiom used through a helper,
  -- including the `sorryAx` assumption produced by an unfinished proof.
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut audited := 0
  for (name, _) in env.constants.toList do
    if let some owner := env.getModuleIdxFor? name then
      if owners.contains owner then
        for assumption in ← Lean.collectAxioms name do
          unless allowed.contains assumption do
            throwError "Shared library declaration {name} depends on forbidden axiom {assumption}"
        audited := audited + 1
  -- An empty scan cannot establish that the compiled library was checked.
  unless audited > 0 do
    throwError "Shared library axiom audit found no declarations"
  Lean.logInfo m!"Shared library axiom audit checked {audited} declarations"
