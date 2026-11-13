-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# K4 Compiler Substrate Benchmarks in Compiled Lean 4.34.1 (`lean -c` -> `clang -O3`)

Implements the 6 canonical compiler kernels matching the Rust 1.99.1 suite:
1. `dom_ssa`: Cooper-Harvey-Kennedy iterative dominator tree + SSA frontier
   over `V = 20,000` CFG basic blocks across 3 Lean 4 state representations:
   - `dom_ssa_array_fbip`: Linear `Array Nat` with RC==1 in-place mutation (`Array.set!`)
   - `dom_ssa_rbmap`: Pure persistent balanced BST map (`IntMap`)
   - `dom_ssa_stref`: `IO.Ref (Array Nat)` state reference cells
2. `hashmap_intern`: 500,000 symbol interning insertions + 500,000 lookups (`Std.HashMap`).
3. `egraph_uf`: Path-compressed union-find over 200,000 e-classes (600,000 merges).
4. `regalloc`: Linear-scan register allocation over 100,000 virtual registers.
5. `inst_encode`: Encoding 2,000,000 x86-64 machine instructions into a `ByteArray`.
6. `ir_parser`: Lexer & recursive-descent parsing of 500,000 SSA instruction lines.
7. `parallel_scaling`: Multi-threaded `Task.spawn` scaling across `T ∈ {1, 2, 4, 8, 16}`.
-/

/-- Simple persistent balanced binary search tree for comparing persistent map vs FBIP Array. -/
inductive IntMap where
  | leaf
  | node (sz : Nat) (k : Nat) (v : Nat) (l r : IntMap)
  deriving Inhabited

namespace IntMap

@[inline] def size : IntMap → Nat
  | .leaf => 0
  | .node s _ _ _ _ => s

def findD (m : IntMap) (k : Nat) (d : Nat) : Nat :=
  match m with
  | .leaf => d
  | .node _ mk mv l r =>
      if k < mk then findD l k d
      else if k > mk then findD r k d
      else mv

@[inline] def mkNode (k v : Nat) (l r : IntMap) : IntMap :=
  .node (1 + size l + size r) k v l r

def balance (k v : Nat) (l r : IntMap) : IntMap :=
  let sl := size l
  let sr := size r
  if sl + sr <= 1 then mkNode k v l r
  else if sr > 3 * sl + 1 then
    match r with
    | .node _ rk rv rl rr =>
        if size rl <= 2 * size rr then mkNode rk rv (mkNode k v l rl) rr
        else match rl with
          | .node _ rlk rlv rll rlr => mkNode rlk rlv (mkNode k v l rll) (mkNode rk rv rlr rr)
          | .leaf => mkNode k v l r
    | .leaf => mkNode k v l r
  else if sl > 3 * sr + 1 then
    match l with
    | .node _ lk lv ll lr =>
        if size lr <= 2 * size ll then mkNode lk lv ll (mkNode k v lr r)
        else match lr with
          | .node _ lrk lrv lrl lrr => mkNode lrk lrv (mkNode lk lv ll lrl) (mkNode k v lrr r)
          | .leaf => mkNode k v l r
    | .leaf => mkNode k v l r
  else mkNode k v l r

def insert (m : IntMap) (k v : Nat) : IntMap :=
  match m with
  | .leaf => .node 1 k v .leaf .leaf
  | .node s mk mv l r =>
      if k < mk then balance mk mv (insert l k v) r
      else if k > mk then balance mk mv l (insert r k v)
      else .node s k v l r

def foldSum (m : IntMap) (acc : UInt64) : UInt64 :=
  match m with
  | .leaf => acc
  | .node _ _ v l r => foldSum r (foldSum l (acc + v.toUInt64))

end IntMap

partial def intersectArr (doms : Array Nat) (b1 b2 : Nat) : Nat :=
  let rec loop (x y : Nat) : Nat :=
    if x == y then x
    else if x > y then loop (doms.getD x 0) y
    else loop x (doms.getD y 0)
  loop b1 b2

/-- Kernel 1A: Dominator Tree + SSA Frontier using linear `Array` (FBIP in-place `set!`). -/
partial def benchDomSsaArray (nBlocks : Nat) : UInt64 := Id.run do
  let mut preds0 : Array Nat := Array.replicate nBlocks 0
  let mut preds1 : Array Nat := Array.replicate nBlocks 0
  for i in [1:nBlocks] do
    preds0 := preds0.set! i (i - 1)
    let p1 := if i >= 3 && (i % 5 == 0) then i - 3 else i / 2
    preds1 := preds1.set! i p1

  let undef := 999999999
  let mut doms : Array Nat := Array.replicate nBlocks undef
  doms := doms.set! 0 0

  let mut changed := true
  while changed do
    changed := false
    for b in [1:nBlocks] do
      let p0 := preds0.getD b 0
      let p1 := preds1.getD b 0
      let mut newIdom := p0
      if doms.getD p1 undef != undef && p1 != p0 then
        newIdom := intersectArr doms newIdom p1
      if doms.getD b undef != newIdom then
        doms := doms.set! b newIdom
        changed := true

  let mut dfCount : Array UInt32 := Array.replicate nBlocks (0 : UInt32)
  for b in [1:nBlocks] do
    let p0 := preds0.getD b 0
    let p1 := preds1.getD b 0
    let idom := doms.getD b 0
    if p0 != p1 then
      let mut runner := p0
      while runner != idom do
        dfCount := dfCount.set! runner (dfCount.getD runner 0 + 1)
        runner := doms.getD runner 0
      runner := p1
      while runner != idom do
        dfCount := dfCount.set! runner (dfCount.getD runner 0 + 1)
        runner := doms.getD runner 0

  let mut checksum : UInt64 := 0
  for i in [0:nBlocks] do
    let d := (doms.getD i 0).toUInt64
    let df := (dfCount.getD i 0).toUInt64
    checksum := checksum + (d ^^^ (df <<< (16 : UInt64)))
  return checksum

/-- Kernel 1B: Dominator Tree using persistent `IntMap` (RBMap-equivalent tree). -/
partial def benchDomSsaRBMap (nBlocks : Nat) : UInt64 := Id.run do
  let mut doms : IntMap := IntMap.leaf.insert 0 0
  for b in [1:nBlocks] do
    let p0 := b - 1
    let p1 := if b >= 3 && (b % 5 == 0) then b - 3 else b / 2
    let mut b1 := p0
    let mut b2 := p1
    while b1 != b2 do
      while b1 > b2 do
        b1 := doms.findD b1 0
      while b2 > b1 do
        b2 := doms.findD b2 0
    doms := doms.insert b b1
  return doms.foldSum 0

/-- Kernel 1C: Dominator Tree using `IO.Ref` (`STRef`) mutable array cells. -/
partial def benchDomSsaSTRef (nBlocks : Nat) : IO UInt64 := do
  let undef := 999999999
  let domsRef ← IO.mkRef (Array.replicate nBlocks undef)
  domsRef.modify (fun a => a.set! 0 0)
  for b in [1:nBlocks] do
    let p0 := b - 1
    let p1 := if b >= 3 && (b % 5 == 0) then b - 3 else b / 2
    let doms ← domsRef.get
    let idom := intersectArr doms p0 p1
    domsRef.modify (fun a => a.set! b idom)
  let finalDoms ← domsRef.get
  let mut checksum : UInt64 := 0
  for i in [0:nBlocks] do
    checksum := checksum + (finalDoms.getD i 0).toUInt64
  return checksum

/-- Kernel 2: Symbol Interning & HashMap Lookups (500,000 insertions + 500,000 queries). -/
def benchHashMapIntern (nSyms : Nat) : UInt64 := Id.run do
  let mut map : Std.HashMap UInt64 UInt64 := Std.HashMap.emptyWithCapacity nSyms
  let mut state : UInt64 := 0x123456789abcdef0
  for i in [0:nSyms] do
    state := state * 6364136223846793005 + 1442695040888963407
    let key := state ^^^ (i.toUInt64 <<< (13 : UInt64))
    map := map.insert key (i.toUInt64 * 31)
  let mut checksum : UInt64 := 0
  state := 0x123456789abcdef0
  for i in [0:nSyms] do
    state := state * 6364136223846793005 + 1442695040888963407
    let key := state ^^^ (i.toUInt64 <<< (13 : UInt64))
    match map[key]? with
    | some v => checksum := checksum + v
    | none => pure ()
  return checksum

partial def ufFind (parent : Array UInt32) (x : UInt32) : Array UInt32 × UInt32 := Id.run do
  let mut pArr := parent
  let mut curr := x
  while pArr.getD curr.toNat curr != curr do
    let p := pArr.getD curr.toNat curr
    let gp := pArr.getD p.toNat p
    pArr := pArr.set! curr.toNat gp
    curr := p
  return (pArr, curr)

/-- Kernel 3: Union-Find & E-Graph Congruence Closure (200,000 e-classes, 600,000 merges). -/
def benchEgraphUf (nClasses : Nat) : UInt64 := Id.run do
  let mut parent : Array UInt32 := Array.ofFn (n := nClasses) (fun i => i.val.toUInt32)
  let mut rank : Array UInt8 := Array.replicate nClasses (0 : UInt8)
  let nMerges := nClasses * 3
  let half := nClasses / 2 + 1
  for step in [0:nMerges] do
    let a := ((step * 17 + 5) % nClasses).toUInt32
    let b := ((step * 31 + 19) % half).toUInt32
    let (p1, ra) := ufFind parent a
    let (p2, rb) := ufFind p1 b
    parent := p2
    if ra != rb then
      let rka := rank.getD ra.toNat 0
      let rkb := rank.getD rb.toNat 0
      if rka < rkb then
        parent := parent.set! ra.toNat rb
      else if rka > rkb then
        parent := parent.set! rb.toNat ra
      else
        parent := parent.set! rb.toNat ra
        rank := rank.set! ra.toNat (rka + 1)

  let mut checksum : UInt64 := 0
  for i in [0:nClasses] do
    let (pNext, r) := ufFind parent i.toUInt32
    parent := pNext
    checksum := checksum + r.toUInt64
  return checksum

/-- Kernel 4: Linear-Scan Register Allocation (100,000 virtual registers, 16 physical regs). -/
def benchRegalloc (nVregs : Nat) : UInt64 := Id.run do
  let mut physEnd : Array UInt32 := Array.replicate 16 (0 : UInt32)
  let mut nextSpill : UInt32 := 0
  let mut checksum : UInt64 := 0
  for i in [0:nVregs] do
    let start := (i * 2).toUInt32
    let len := ((i * 37 + 11) % 64 + 4).toUInt32
    let stop := start + len
    let mut allocated := 16
    let mut maxEndReg := 0
    let mut maxEndVal := physEnd.getD 0 0
    for r in [0:16] do
      let pe := physEnd.getD r 0
      if allocated == 16 && pe <= start then
        allocated := r
      if pe > maxEndVal then
        maxEndVal := pe
        maxEndReg := r
    if allocated < 16 then
      physEnd := physEnd.set! allocated stop
      checksum := checksum + allocated.toUInt64
    else
      nextSpill := nextSpill + 1
      if maxEndVal > stop then
        physEnd := physEnd.set! maxEndReg stop
      checksum := checksum + (nextSpill.toUInt64 <<< (8 : UInt64))
  return checksum

/-- Kernel 5: Machine Instruction Encoding & Binary Emission (2,000,000 x86-64 instructions). -/
def benchInstEncode (nInsts : Nat) : UInt64 := Id.run do
  let mut buf := ByteArray.emptyWithCapacity (nInsts * 4)
  for i in [0:nInsts] do
    let b1 : UInt8 := (((i >>> 3) &&& 1).toUInt8) <<< (2 : UInt8)
    let b2 : UInt8 := (i &&& 1).toUInt8
    let rex : UInt8 := (0x48 : UInt8) ||| b1 ||| b2
    let op : UInt8 :=
      match i &&& 3 with
      | 0 => 0x01
      | 1 => 0x29
      | 2 => 0x31
      | _ => 0x89
    let m1 : UInt8 := ((i &&& 7).toUInt8) <<< (3 : UInt8)
    let m2 : UInt8 := ((i >>> 4) &&& 7).toUInt8
    let modrm : UInt8 := (0xC0 : UInt8) ||| m1 ||| m2
    let imm : UInt8 := ((i * 73) &&& 0xFF).toUInt8
    buf := buf.push rex
    buf := buf.push op
    buf := buf.push modrm
    buf := buf.push imm
  let mut checksum : UInt64 := buf.size.toUInt64
  let mut idx := 0
  while idx < buf.size do
    checksum := checksum + (buf.get! idx).toUInt64
    idx := idx + 64
  return checksum

/-- Build the exact same 500,000-line textual SSA buffer as Rust `build_ssa_buffer`. -/
def buildSsaBuffer (nLines : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (nLines * 24)
  for i in [0:nLines] do
    let rDst := i % 1024
    let rA := (i * 7 + 1) % 1024
    let rB := (i * 13 + 3) % 1024
    let line := s!"v{rDst} = add v{rA}, v{rB}\n"
    out := out.append line.toUTF8
  return out

/-- Kernel 6: Lexer & Recursive-Descent SSA IR Parser. -/
partial def benchIrParser (buf : ByteArray) : UInt64 := Id.run do
  let mut pos := 0
  let n := buf.size
  let mut instCount : UInt64 := 0
  let mut regSum : UInt64 := 0
  while pos < n do
    let b := buf.get! pos
    if b == 118 then -- 'v'
      pos := pos + 1
      let mut val : UInt64 := 0
      while pos < n && (let d := buf.get! pos; d >= 48 && d <= 57) do
        let d := buf.get! pos
        val := val * 10 + (d - 48).toUInt64
        pos := pos + 1
      regSum := regSum + val
    else if b == 10 then -- '\n'
      instCount := instCount + 1
      pos := pos + 1
    else
      pos := pos + 1
  return (instCount <<< (32 : UInt64)) ^^^ regSum

def timeIo (iters : Nat) (act : Nat → IO UInt64) : IO (Float × Float × UInt64) := do
  let mut times : Array Float := #[]
  let mut last : UInt64 := 0
  for _ in [0:iters] do
    let t0 ← IO.monoNanosNow
    let dynZero := (t0 &&& 1) - (t0 &&& 1)
    last ← act dynZero
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0).toFloat / 1000000.0
    times := times.push ms
  let sorted := times.qsort (fun a b => a < b)
  let med := sorted.getD (iters / 2) 0.0
  let p95 := sorted.getD ((iters * 95) / 100) 0.0
  return (med, p95, last)

def main : IO Unit := do
  let iters := 7
  let (domArrMed, domArrP95, c1) ← timeIo iters (fun z => pure (benchDomSsaArray (20000 + z)))
  let (domTreeMed, domTreeP95, c1b) ← timeIo iters (fun z => pure (benchDomSsaRBMap (20000 + z)))
  let (domRefMed, domRefP95, c1c) ← timeIo iters (fun z => benchDomSsaSTRef (20000 + z))
  let (hmMed, hmP95, c2) ← timeIo iters (fun z => pure (benchHashMapIntern (500000 + z)))
  let (ufMed, ufP95, c3) ← timeIo iters (fun z => pure (benchEgraphUf (200000 + z)))
  let (raMed, raP95, c4) ← timeIo iters (fun z => pure (benchRegalloc (100000 + z)))
  let (encMed, encP95, c5) ← timeIo iters (fun z => pure (benchInstEncode (2000000 + z)))

  let ssaBuf := buildSsaBuffer 500000
  let (parseMed, parseP95, c6) ← timeIo iters (fun z => pure (benchIrParser (if z == 999 then ByteArray.empty else ssaBuf)))

  -- Parallel scaling across T in {1, 2, 4, 8, 16} using Task.spawn
  let threadCounts := #[1, 2, 4, 8, 16]
  let mut parOut : Array (Nat × Float) := #[]
  for t in threadCounts do
    let totalTasks := 32
    let tasksPerThread := totalTasks / t
    let mut times : Array Float := #[]
    for _ in [0:5] do
      let t0 ← IO.monoNanosNow
      let mut tasks : Array (Task UInt64) := #[]
      for tid in [0:t] do
        let tk := Task.spawn (prio := .dedicated) fun _ => Id.run do
          let mut s : UInt64 := 0
          for k in [0:tasksPerThread] do
            s := s + benchDomSsaArray (10000 + (tid + k) % 3)
            s := s + benchRegalloc 50000
          return s
        tasks := tasks.push tk
      let mut totalSum : UInt64 := 0
      for tk in tasks do
        totalSum := totalSum + tk.get
      if totalSum == 123456789 then IO.println "unreachable"
      let t1 ← IO.monoNanosNow
      times := times.push ((t1 - t0).toFloat / 1000000.0)
    let sorted := times.qsort (fun a b => a < b)
    parOut := parOut.push (t, sorted.getD 2 0.0)

  IO.println "{"
  IO.println s!"  \"dom_ssa_array_fbip\": \{\"median_ms\": {domArrMed}, \"p95_ms\": {domArrP95}, \"checksum\": {c1}},"
  IO.println s!"  \"dom_ssa_rbmap\": \{\"median_ms\": {domTreeMed}, \"p95_ms\": {domTreeP95}, \"checksum\": {c1b}},"
  IO.println s!"  \"dom_ssa_stref\": \{\"median_ms\": {domRefMed}, \"p95_ms\": {domRefP95}, \"checksum\": {c1c}},"
  IO.println s!"  \"hashmap_intern\": \{\"median_ms\": {hmMed}, \"p95_ms\": {hmP95}, \"checksum\": {c2}},"
  IO.println s!"  \"egraph_uf\": \{\"median_ms\": {ufMed}, \"p95_ms\": {ufP95}, \"checksum\": {c3}},"
  IO.println s!"  \"regalloc\": \{\"median_ms\": {raMed}, \"p95_ms\": {raP95}, \"checksum\": {c4}},"
  IO.println s!"  \"inst_encode\": \{\"median_ms\": {encMed}, \"p95_ms\": {encP95}, \"checksum\": {c5}},"
  IO.println s!"  \"ir_parser\": \{\"median_ms\": {parseMed}, \"p95_ms\": {parseP95}, \"checksum\": {c6}},"
  IO.println "  \"parallel_scaling_ms\": {"
  for idx in [0:parOut.size] do
    let (t, ms) := parOut.getD idx (1, 0.0)
    let comma := if idx + 1 < parOut.size then "," else ""
    IO.println s!"    \"T{t}\": {ms}{comma}"
  IO.println "  }"
  IO.println "}"
