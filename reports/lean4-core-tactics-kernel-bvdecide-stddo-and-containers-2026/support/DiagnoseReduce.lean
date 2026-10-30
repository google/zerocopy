-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Tactic.BVDecide
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# Diagnostic Probe: Upstream `verifyBVExpr` and `Std.HashMap` Kernel-Reduction Blockers

This probe isolates the seven independent kernel-reduction blockers in
`Std.Tactic.BVDecide.Reflect.verifyBVExpr` and `Std.HashMap` in Lean `v4.34.1`,
contrasting them against `BVLogicalExpr.const false` (which reduces in the
kernel because it never touches a `Std.HashMap` cache) and `Std.TreeMap`
(which reduces in the kernel with zero axioms).
-/

namespace DiagnoseReduce

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

-- Baseline 0: `BVLogicalExpr.const false` has no `BVExpr` variables or binary
-- AIG gates, so `BVLogicalExpr.bitblast` returns `AIG.mkConstCached false` on
-- the initial `.false` leaf without probing `Std.HashMap`. Consequently, its
-- AIG size reduces in the kernel via `eagerReduce (Eq.refl 1)`.
def constFalseExpr : BVLogicalExpr := .const false

theorem constFalse_aig_size_reduces :
    constFalseExpr.bitblast.aig.decls.size = 1 :=
  eagerReduce (Eq.refl 1)

-- Blocker 1: `LRAT.parseLRATProof` and `LRAT.Parser.parseActions` cannot
-- reduce in the kernel because `String.toUTF8` is `opaque` and `parseActions`
-- is a `partial def` (compiled as `opaque`).
/--
error: Tactic `rfl` failed: The left-hand side
  (LRAT.parseLRATProof "1 0\n".toUTF8).isOk
is not definitionally equal to the right-hand side
  true

⊢ (LRAT.parseLRATProof "1 0\n".toUTF8).isOk = true
-/
#guard_msgs in
theorem blocker1_lrat_parser_cannot_reduce_in_kernel :
    (LRAT.parseLRATProof "1 0\n".toUTF8).isOk = true := by
  rfl

-- Blocker 2: `Std.DHashMap.Internal.mkIdx` (`@[irreducible]`), `USize`
-- (`opaque System.Platform.getNumBits`), and `opaque mixHash` block kernel
-- reduction on `Std.HashMap` even for a single lookup on an empty map, whereas
-- `Std.TreeMap` reduces in the kernel via `decide +kernel`.
theorem treeMap_empty_lookup_reduces_in_kernel :
    (∅ : Std.TreeMap Nat Nat)[0]? = none := by
  decide +kernel

/--
error: Tactic `rfl` failed: The left-hand side
  ∅[0]?
is not definitionally equal to the right-hand side
  none

⊢ ∅[0]? = none
-/
#guard_msgs in
theorem blocker2_hashmap_empty_lookup_blocks_rfl :
    (∅ : Std.HashMap Nat Nat)[0]? = none := by
  rfl

-- Blocker 3 & Blocker 4: `BVExpr.bitblast.go` (`Std.DHashMap` cache) and
-- `Std.Sat.AIG.Cache.get?` (`@[irreducible]` `Std.HashMap` wrapper) block
-- kernel reduction as soon as a single 1-bit variable is bitblasted.
def oneBitEqExpr : BVLogicalExpr :=
  .not (.literal (.bin (.var 0 : BVExpr 1) .eq (.var 0 : BVExpr 1)))

/--
error: Tactic `rfl` failed: The left-hand side
  oneBitEqExpr.bitblast.aig.decls.size
is not definitionally equal to the right-hand side
  2

⊢ oneBitEqExpr.bitblast.aig.decls.size = 2
-/
#guard_msgs in
theorem blocker3_and_4_bitblast_aig_cache_blocks_rfl :
    oneBitEqExpr.bitblast.aig.decls.size = 2 := by
  rfl

-- Blocker 5: `Std.Sat.AIG.denote.go` is defined by well-founded recursion
-- (`termination_by (x, 0)`) explicitly to prevent kernel reduction.
/--
error: Tactic `rfl` failed: The left-hand side
  ⟦fun x => false, constFalseExpr.bitblast⟧
is not definitionally equal to the right-hand side
  false

⊢ ⟦fun x => false, constFalseExpr.bitblast⟧ = false
-/
#guard_msgs in
theorem blocker5_aig_denote_wf_blocks_rfl :
    AIG.denote (fun (_ : BVBit) => false) constFalseExpr.bitblast = false := by
  rfl

-- Blocker 6: `AIG.Entrypoint.relabelNat` uses `Std.HashMap` to reindex atoms,
-- blocking kernel reduction even on the constant-false entrypoint.
/--
error: Tactic `rfl` failed: The left-hand side
  constFalseExpr.bitblast.relabelNat.aig.decls.size
is not definitionally equal to the right-hand side
  1

⊢ constFalseExpr.bitblast.relabelNat.aig.decls.size = 1
-/
#guard_msgs in
theorem blocker6_relabelNat_blocks_rfl :
    constFalseExpr.bitblast.relabelNat.aig.decls.size = 1 := by
  rfl

-- Blocker 7: `LRAT.Internal.DefaultClause.ofArray.folder` is marked
-- `@[irreducible]` and uses `Std.HashMap (PosFin n) Bool` to deduplicate
-- literals and detect tautologies during `LRAT.check`.
/--
error: Tactic `rfl` failed: The left-hand side
  (LRAT.Internal.DefaultClause.ofArray #[(⟨1, ⋯⟩, true)]).isSome
is not definitionally equal to the right-hand side
  true

⊢ (LRAT.Internal.DefaultClause.ofArray #[(⟨1, ⋯⟩, true)]).isSome = true
-/
#guard_msgs in
theorem blocker7_defaultClause_ofArray_blocks_rfl :
    (LRAT.Internal.DefaultClause.ofArray
      (#[(⟨1, ⟨Nat.zero_lt_one, by decide⟩⟩, true)] :
        Array (LRAT.Internal.PosFin 2 × Bool))).isSome = true := by
  rfl

-- Section 2: Axiom-Footprint Verification for `omega` and `grind`
-- Confirms that `omega` and `grind` (`lia`, `ring`, `ToInt`) emit zero
-- `Lean.trustCompiler` or `_native` axioms.
theorem omega_bounds_check (base len sub_off sub_len idx : Nat)
    (h_sub : sub_off + sub_len ≤ len) (h_idx : idx < sub_len) :
    base + sub_off + idx < base + len := by
  omega

/--
info: 'DiagnoseReduce.omega_bounds_check' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms omega_bounds_check

theorem grind_uint64_lia_check (off len : UInt64)
    (h_off : off ≤ 1024) (h_len : len ≤ 4096) :
    off + len ≤ 5120 := by
  grind

/--
info: 'DiagnoseReduce.grind_uint64_lia_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grind_uint64_lia_check

theorem grind_int_ring_check (base i j stride : Int) :
    base + (i + j) * stride = (base + i * stride) + j * stride := by
  grind

/--
info: 'DiagnoseReduce.grind_int_ring_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grind_int_ring_check

end DiagnoseReduce
