-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Do
import Std.Tactic.Do
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashMap.Raw
import Std.Data.HashMap.RawLemmas
import Std.Data.ExtHashMap
import Std.Data.ExtHashMap.Lemmas
import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeMap.Raw
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

/-!
# Probe: `Std.Do` (`SPred`, `WP`, `Triple`, `mvcgen`) & `Std.Data` Containers

1. **Section 1 (`ProbeStdDo`):** Proves Hoare triples (`Std.Do.Triple`,
   `⦃P⦄ prog ⦃Q⦄`) for monadic programs over `StateM` and `EStateM` (modeling
   Anneal MIR statement execution with in-bounds checked indexing and state
   updates) using `@[spec]`, `mvcgen`, `omega`, and `grind`, and inspects
   `#print axioms`.
2. **Section 2 (`ProbeStdData`):**
   - Demonstrates why bundled `Std.TreeMap`, `Std.HashMap`, `Std.ExtTreeMap`,
     and `Std.ExtHashMap` are rejected by the kernel's nested-inductive
     translation inside recursive inductive types (verified via `#guard_msgs`),
     whereas `Std.TreeMap.Raw` and `Std.HashMap.Raw` succeed.
   - Compares `Std.TreeMap` / `Std.TreeMap.Raw` (which reduce in the kernel via
     `rfl` / `decide +kernel`) against `Std.HashMap` / `Std.HashMap.Raw` (which
     block kernel reduction at `Std.DHashMap.Internal.mkIdx`, `USize`, and
     `mixHash`).
   - Demonstrates extensional equality proofs on `Std.ExtTreeMap` and lookup
     simplification with `grind`.
-/

namespace ProbeStdDo

open Std.Do

set_option mvcgen.warning false

structure FrameState where
  sp : Nat
  limit : Nat
  acc : Nat
  deriving Repr, DecidableEq

/-- Allocate `bytes` on a bounded stack frame in `StateM FrameState`, returning
`true` on success. -/
def tryBumpAlloc (bytes : Nat) : StateM FrameState Bool := do
  let st ← get
  if st.sp + bytes ≤ st.limit then
    set { st with sp := st.sp + bytes, acc := st.acc + bytes }
    return true
  else
    return false

@[spec]
theorem tryBumpAlloc_spec (bytes : Nat) :
    ⦃fun s => ⌜s.sp ≤ s.limit⌝⦄
    tryBumpAlloc bytes
    ⦃⇓ ok s' => ⌜s'.sp ≤ s'.limit ∧ (ok = true → s'.acc = s'.acc) ∧
                (ok = true → s'.sp ≥ bytes)⌝⦄ := by
  mvcgen [tryBumpAlloc] <;> grind

#print axioms tryBumpAlloc_spec

/-- Two sequential allocations in `StateM FrameState` composed via `@[spec]` and
`mvcgen`. -/
def allocPair (n m : Nat) : StateM FrameState Bool := do
  let ok1 ← tryBumpAlloc n
  if ok1 then
    let ok2 ← tryBumpAlloc m
    return ok2
  else
    return false

theorem allocPair_spec (n m : Nat) :
    ⦃fun s => ⌜s.sp ≤ s.limit⌝⦄
    allocPair n m
    ⦃⇓ _ s' => ⌜s'.sp ≤ s'.limit⌝⦄ := by
  mvcgen [allocPair] <;> omega

#print axioms allocPair_spec

/-- Monadic evaluator with exceptions (`EStateM String FrameState`) modeling MIR
checked step. -/
def checkedStep (delta : Nat) : EStateM String FrameState Nat := do
  let st ← get
  if st.sp + delta ≤ st.limit then
    let nextSp := st.sp + delta
    set { st with sp := nextSp, acc := st.acc + 1 }
    return nextSp
  else
    throw "stack overflow"

theorem checkedStep_spec (delta : Nat) (initSp initLim initAcc : Nat) :
    ⦃fun s => ⌜s.sp = initSp ∧ s.limit = initLim ∧ s.acc = initAcc ∧ initSp + delta ≤ initLim⌝⦄
    checkedStep delta
    ⦃post⟨fun ret s' => ⌜ret = initSp + delta ∧ s'.sp = initSp + delta ∧ s'.acc = initAcc + 1⌝,
          fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [checkedStep] <;> omega

#print axioms checkedStep_spec

end ProbeStdDo

namespace ProbeStdData

open Std

-- Bundled `Std.TreeMap` (and likewise `Std.HashMap`, `Std.ExtTreeMap`, and
-- `Std.ExtHashMap`) cannot be nested inside a recursive inductive type: Lean's
-- nested-inductive translator specializes the inner container
-- `Impl Nat (fun _ => BadRecValue)` to `_nested.Std.DTreeMap.Internal.Impl_3`,
-- which then fails to typecheck against the bundled
-- `wf : DTreeMap.Internal.Impl.WF inner` field.
/--
error: (kernel) application type mismatch
  DTreeMap.Internal.Impl.WF inner
argument has type
  _nested.Std.DTreeMap.Internal.Impl_3
but function has type
  (DTreeMap.Internal.Impl Nat fun x => BadRecValue) → Prop
-/
#guard_msgs in
inductive BadRecValue where
  | scalar (v : UInt64)
  | structFields (fields : Std.TreeMap Nat BadRecValue)

/--
Using `Std.TreeMap.Raw` and `Std.HashMap.Raw` unbundles `WF` from the container
data, allowing recursive inductive types (such as Anneal MIR `Value` trees,
`Layout` trees, or `MemState` heap objects) to pass the kernel's
nested-inductive translation and strict positivity check.
-/
inductive GoodRecValue where
  | scalar (v : UInt64)
  | treeFields (fields : Std.TreeMap.Raw Nat GoodRecValue)
  | hashFields (fields : Std.HashMap.Raw Nat GoodRecValue)

/-- Kernel reduction (`decide +kernel` / `rfl`) works directly on `Std.TreeMap`
and `Std.TreeMap.Raw`. -/
theorem treemap_kernel_reduce :
    let m : Std.TreeMap Nat Nat := (∅ : Std.TreeMap Nat Nat).insert 10 42 |>.insert 20 99
    m[10]? = some 42 ∧ m[20]? = some 99 ∧ m[30]? = none := by
  decide +kernel

theorem treemap_raw_kernel_reduce :
    let m : Std.TreeMap.Raw Nat Nat := (∅ : Std.TreeMap.Raw Nat Nat).insert 10 42 |>.insert 20 99
    m[10]? = some 42 ∧ m[20]? = some 99 ∧ m[30]? = none := by
  decide +kernel

#print axioms treemap_kernel_reduce
#print axioms treemap_raw_kernel_reduce

/--
Symbolic lookup reasoning on `Std.TreeMap.Raw` (requiring `hwf : m.WF`, where
`Std.TreeMap.Raw.WF.insert` / `emptyc` discharge intermediate `WF` obligations)
and `Std.ExtTreeMap` via `grind`.
-/
theorem treemap_raw_lookup_insert (m : Std.TreeMap.Raw Nat Nat) (hwf : m.WF) (k k' v : Nat)
    (h : k ≠ k') :
    ((m.insert k v).insert k' 100)[k]? = some v := by
  grind [Std.TreeMap.Raw.WF.insert]

theorem exttreemap_ext_insert_comm (m : Std.ExtTreeMap Nat Nat) (k₁ k₂ v₁ v₂ : Nat) (h : k₁ ≠ k₂) :
    (m.insert k₁ v₁).insert k₂ v₂ = (m.insert k₂ v₂).insert k₁ v₁ := by
  ext k
  grind

#print axioms treemap_raw_lookup_insert
#print axioms exttreemap_ext_insert_comm

end ProbeStdData
