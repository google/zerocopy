/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- Concrete edge cases plus the universal geometry lemmas are checked independently
-- of Aeneas and consumers. No Rust/compiler correspondence assumptions are imported.
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

#print axioms Rust.roundUpToAlign_ge
#print axioms Rust.Allocation.offset_lt_size
#print axioms Rust.FitsInAllocation.address_bounds_alloc

-- Consumer compatibility: explicit simplification through old names still exposes
-- arithmetic, so existing frontend proofs can keep their unfolding lists.
namespace Compatibility
abbrev roundUpToAlign := Rust.roundUpToAlign
example (v a : Nat) : roundUpToAlign v a = ((v + a - 1) / a) * a := by
  simp only [roundUpToAlign]
end Compatibility

-- Audit every compiled library declaration, including unused helpers and names
-- outside the Rust namespace. Module ownership defines the checked boundary.
run_cmd do
  let env ← Lean.getEnv
  let libraryModules := #[`Rust, `Rust.Layout, `Rust.Memory, `Rust.Bytes]
  let owners ← libraryModules.mapM fun moduleName => do
    let some owner := env.getModuleIdx? moduleName
      | throwError "Shared library module was not imported: {moduleName}"
    pure owner
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut audited := 0
  for (name, _) in env.constants.toList do
    if let some owner := env.getModuleIdxFor? name then
      if owners.contains owner then
        for assumption in ← Lean.collectAxioms name do
          unless allowed.contains assumption do
            throwError "Shared library declaration {name} depends on forbidden axiom {assumption}"
        audited := audited + 1
  unless audited > 0 do
    throwError "Shared library axiom audit found no declarations"
  Lean.logInfo m!"Shared library axiom audit checked {audited} declarations"
