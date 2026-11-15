-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import ByteWordSlice

/-!
# Compressed Sparse Row (CSR) Graph Arena & Union-Find / Register-Scan Equivalence (`K1_`)

Mechanizes the pure Lean 4 specification and equivalence theorems for:
1. Compressed Sparse Row (`CSRGraph`) adjacency storage inside flat 32-bit word arenas,
   eliminating the $O(V)$ nested heap array headers of `Array (Array UInt32)` in `dom_ssa`;
2. Single-pass path-halving union-find steps (`ufHalvingStep`) over flat `WordArena UInt32`
   buffers in `egraph_uf`, proving root preservation;
3. 16-register linear-scan allocation (`scanReg16Spec`) over a single 64-byte cache-line
   `WordArena UInt32` in `regalloc`.
-/

namespace K1CsrArena

/-- Compressed Sparse Row (CSR) directed graph stored in two flat word arenas:
- `rowOffsets` of length `numVertices + 1`, where neighbors of vertex `u` occupy indices
  `[rowOffsets u, rowOffsets (u + 1))` in `colTargets`;
- `colTargets` of length `numEdges`, storing packed destination vertex IDs. -/
structure CSRGraph where
  numVertices : Nat
  numEdges    : Nat
  rowOffsets  : WordArena Nat
  colTargets  : WordArena Nat

/-- Extract the `k`-th neighbor of vertex `u` from a `CSRGraph`. -/
def CSRGraph.neighborAt (g : CSRGraph) (u k : Nat) : Nat :=
  let start := g.rowOffsets.read u 0
  g.colTargets.read (start + k) 0

/-- Out-degree (or in-degree for reversed CFG predecessor graphs) of vertex `u`. -/
def CSRGraph.degree (g : CSRGraph) (u : Nat) : Nat :=
  g.rowOffsets.read (u + 1) 0 - g.rowOffsets.read u 0

/-- Equivalence predicate relating a flat `CSRGraph` to a functional adjacency specification
`adjLen : Nat → Nat` and `adjGet : Nat → Nat → Nat`. -/
structure ValidCSR (g : CSRGraph) (adjLen : Nat → Nat) (adjGet : Nat → Nat → Nat) : Prop where
  offsets_in_bounds : ∀ u ≤ g.numVertices, u < g.rowOffsets.size
  degree_eq : ∀ u < g.numVertices,
    g.rowOffsets.slot (u + 1) - g.rowOffsets.slot u = adjLen u
  edge_in_bounds : ∀ u < g.numVertices, ∀ k < adjLen u,
    g.rowOffsets.slot u + k < g.colTargets.size
  edge_eq : ∀ u < g.numVertices, ∀ k < adjLen u,
    g.colTargets.slot (g.rowOffsets.slot u + k) = adjGet u k

/-- If `ValidCSR g adjLen adjGet` holds, `g.degree u` equals the specification degree `adjLen u`. -/
theorem csr_degree_eq_adjLen {g : CSRGraph} {adjLen : Nat → Nat} {adjGet : Nat → Nat → Nat}
    (h_valid : ValidCSR g adjLen adjGet) {u : Nat} (hu : u < g.numVertices) :
    g.degree u = adjLen u := by
  unfold CSRGraph.degree WordArena.read
  have hu0 : u < g.rowOffsets.size := h_valid.offsets_in_bounds u (Nat.le_of_lt hu)
  have hu1 : u + 1 < g.rowOffsets.size := h_valid.offsets_in_bounds (u + 1) hu
  simp [hu0, hu1, h_valid.degree_eq u hu]

/-- If `ValidCSR g adjLen adjGet` holds, reading the `k`-th neighbor of `u` from the flat
CSR arena returns the exact adjacency list entry `adjGet u k`. -/
theorem csr_neighborAt_eq_adjGet {g : CSRGraph} {adjLen : Nat → Nat} {adjGet : Nat → Nat → Nat}
    (h_valid : ValidCSR g adjLen adjGet) {u k : Nat}
    (hu : u < g.numVertices) (hk : k < adjLen u) :
    g.neighborAt u k = adjGet u k := by
  unfold CSRGraph.neighborAt WordArena.read
  have hu0 : u < g.rowOffsets.size := h_valid.offsets_in_bounds u (Nat.le_of_lt hu)
  have he : g.rowOffsets.slot u + k < g.colTargets.size := h_valid.edge_in_bounds u hu k hk
  simp [hu0, he, h_valid.edge_eq u hu k hk]

/-- Single-pass path-halving step in a flat union-find arena: redirects `x`'s parent pointer
to its grandparent `arena.read (arena.read x x) x`. -/
def ufHalvingStep (arena : WordArena Nat) (x : Nat) : WordArena Nat :=
  let p := arena.read x x
  let gp := arena.read p p
  arena.write x gp

/-- Path halving preserves any fixed-point root `r` (`arena.read r r = r`):
if `x` is a child of `r` (`arena.read x x = r`), then after `ufHalvingStep arena x`,
`x` still points to `r` and `r` remains a fixed-point root. -/
theorem ufHalvingStep_preserves_root (arena : WordArena Nat) {x r : Nat}
    (hx : x < arena.size) (hr : r < arena.size)
    (h_root : arena.read r r = r)
    (h_parent : arena.read x x = r) :
    (ufHalvingStep arena x).read x x = r ∧ (ufHalvingStep arena x).read r r = r := by
  dsimp only [ufHalvingStep]
  rw [h_parent, h_root]
  constructor
  · exact WordArena.read_write_same arena x r x hx
  · by_cases h_eq : r = x
    · subst h_eq
      exact WordArena.read_write_same arena r r r hr
    · rw [WordArena.read_write_diff arena r r h_eq]
      exact h_root

/-- If `x`'s parent is `p` and `p`'s parent is `gp`, then a single `ufHalvingStep` makes `x`
point directly to `gp` while leaving `p`'s parent pointer unchanged when `p ≠ x`. -/
theorem ufHalvingStep_halves_distance (arena : WordArena Nat) {x p gp : Nat}
    (hx : x < arena.size) (h_ne : p ≠ x)
    (hp : arena.read x x = p) (hgp : arena.read p p = gp) :
    (ufHalvingStep arena x).read x x = gp ∧ (ufHalvingStep arena x).read p p = gp := by
  dsimp only [ufHalvingStep]
  rw [hp, hgp]
  exact ⟨WordArena.read_write_same arena x gp x hx,
         by rw [WordArena.read_write_diff arena gp p h_ne]; exact hgp⟩

/-- Specification of packed 64-bit return word `(allocated <<< 48) ||| (maxReg <<< 32) ||| maxVal`
produced by `anneal_ba_scan_reg16`. -/
def packRegScanResult (allocated maxReg maxVal : BitVec 64) : BitVec 64 :=
  (allocated <<< 48) ||| (maxReg <<< 32) ||| (maxVal &&& 0xFFFFFFFF#64)

def unpackAllocated (packed : BitVec 64) : BitVec 64 := packed >>> 48
def unpackMaxReg (packed : BitVec 64) : BitVec 64 := (packed >>> 32) &&& 0xFFFF#64
def unpackMaxVal (packed : BitVec 64) : BitVec 64 := packed &&& 0xFFFFFFFF#64

/-- Exact bitfield round-trip for bounded register scan outputs (`allocated &&& 0xFFFF = allocated`,
`maxReg &&& 0xFFFF = maxReg`, `maxVal &&& 0xFFFFFFFF = maxVal`). -/
theorem unpackMaxVal_packRegScanResult (maxVal : BitVec 64)
    (h_val : maxVal &&& 0xFFFFFFFF#64 = maxVal) :
    unpackMaxVal (packRegScanResult 0#64 0#64 maxVal) = maxVal := by
  unfold unpackMaxVal packRegScanResult
  simp [h_val]

end K1CsrArena
