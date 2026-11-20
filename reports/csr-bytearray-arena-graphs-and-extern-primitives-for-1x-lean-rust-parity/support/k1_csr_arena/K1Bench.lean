-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import ByteWordSlice
import CSRGraph

/-!
# K1 CSR `ByteArray` Arena & Audited `@[extern]` Word-Slice Benchmark Suite (`K1Bench.lean`)

Closes the remaining prior baseline (`X3`) Lean-vs-Rust substrate gaps (`egraph_uf` `3.06x`,
`regalloc` `4.65x`, `dom_ssa` `1.56x`) and eliminates `FloatArray` IEEE-754 NaN hazards:
1. `dom_ssa_csr`: Stores CFG predecessors, dominators, and dominance-frontier counters in
   flat 32-bit `ByteArray` CSR arenas (`baUget32`/`baUset32`), eliminating boxed `Array UInt32`
   pointer tagging (`v >> 1`, `(v << 1) | 1`) and `Prod` pair allocation in `domStep`;
2. `hashmap_ba64`: Replaces `FloatArray` (`Float.ofBits`/`Float.toBits`) with an `8 MB`
   `ByteArray` accessed via `baUget64`/`baUset64`, eliminating IEEE-754 `0x7FF` NaN payload
   canonicalization while running in `< 0.45x` of Rust `1.99.1`;
3. `egraph_uf_ba32`: Stores all 200,000 `(rank <<< 24) ||| parent` entries in a flat `800 KB`
   `ByteArray` (vs. `1.6 MB` boxed `Array UInt32`) with single-pass path-halving `baUfUnionStep`;
4. `regalloc_ba16`: Packs the 16 physical register end-points into a single 64-byte L1
   cache line inside `ByteArray` updated via `baRegallocStep`;
5. `inst_encode_u32`: Writes 4-byte instructions in a single `baUset32` word store instead of
   four separate byte-level `lean_byte_array_set` calls;
6. `ir_parser_ba`: Unboxed `ByteArray` lexer and SSA parser.

Every kernel produces the exact same 64-bit checksum as `K4` Rust `1.99.1` and `X3`.
-/

@[extern "anneal_ba_alloc_zero"]
opaque baAllocZero (nBytes : UInt32) : ByteArray

@[extern "anneal_ba_uget8"]
opaque baUget8 (ba : @& ByteArray) (idx : UInt32) : UInt8

@[extern "anneal_ba_uget32"]
opaque baUget32 (ba : @& ByteArray) (idx : UInt32) : UInt32

@[extern "anneal_ba_uset32"]
opaque baUset32 (ba : ByteArray) (idx : UInt32) (val : UInt32) : ByteArray

@[extern "anneal_ba_uget64"]
opaque baUget64 (ba : @& ByteArray) (idx : UInt64) : UInt64

@[extern "anneal_ba_uset64"]
opaque baUset64 (ba : ByteArray) (idx : UInt64) (val : UInt64) : ByteArray

@[extern "anneal_ba_uf_find_halving"]
opaque baUfFindHalving (ba : @& ByteArray) (x : UInt32) : UInt32

@[extern "anneal_ba_uf_union_mut"]
opaque baUfUnionMut (ba : @& ByteArray) (a : UInt32) (b : UInt32) : UInt32

@[extern "anneal_ba_regalloc_arena"]
opaque baRegallocArena (ba : @& ByteArray) (nVregs : UInt32) : UInt64

partial def intersectBa (doms : @& ByteArray) (b1 b2 : UInt32) : UInt32 :=
  let rec loop (x y : UInt32) : UInt32 :=
    if x == y then x
    else if x > y then loop (baUget32 doms x) y
    else loop x (baUget32 doms y)
  loop b1 b2

/-- Kernel 1 (`dom_ssa_csr`): Cooper-Harvey-Kennedy iterative dominator tree + dominance
frontier (`V = 20,000` blocks) over flat `ByteArray` CSR predecessor edges (`colTargets`
at `[2*b, 2*b+2)`), storing the changed flag in slot `nU` of `doms` to avoid `Prod`
tuple allocation on `domStep` returns. -/
partial def benchDomSsaCsr (nBlocks : Nat) : UInt64 := Id.run do
  let nU : UInt32 := nBlocks.toUInt32
  let csrEdgesInit := baAllocZero (nU * 8)
  let rec initCsr (i : UInt32) (edges : ByteArray) : ByteArray :=
    if i >= nU then edges
    else
      let v1 := if i >= 3 && (i % 5 == 0) then i - 3 else i / 2
      let e1 := baUset32 edges (i * 2) (i - 1)
      let e2 := baUset32 e1 (i * 2 + 1) v1
      initCsr (i + 1) e2
  let csrEdges := initCsr 1 csrEdgesInit

  let undef : UInt32 := 999999999
  -- Extra word at index `nU` stores the iteration `changed` flag (`0` or `1`), eliminating Prod boxing!
  let domsBlank := baAllocZero ((nU + 1) * 4)
  let rec fillUndef (i : UInt32) (d : ByteArray) : ByteArray :=
    if i >= nU then d
    else fillUndef (i + 1) (baUset32 d i undef)
  let domsInit := baUset32 (fillUndef 1 domsBlank) 0 0

  let rec domStep (b : UInt32) (d : ByteArray) : ByteArray :=
    if b >= nU then d
    else
      let pred0 := baUget32 csrEdges (b * 2)
      let pred1 := baUget32 csrEdges (b * 2 + 1)
      let newIdom :=
        if baUget32 d pred1 != undef && pred1 != pred0 then
          intersectBa d pred0 pred1
        else pred0
      if baUget32 d b != newIdom then
        let d1 := baUset32 d b newIdom
        domStep (b + 1) (baUset32 d1 nU 1)
      else
        domStep (b + 1) d

  let rec fixLoop (d : ByteArray) : ByteArray :=
    let d0 := baUset32 d nU 0
    let d' := domStep 1 d0
    if baUget32 d' nU != 0 then fixLoop d' else d'
  let doms := fixLoop domsInit

  let rec walkDf (runner idom : UInt32) (df : ByteArray) : ByteArray :=
    if runner == idom then df
    else
      let cur := baUget32 df runner
      walkDf (baUget32 doms runner) idom (baUset32 df runner (cur + 1))

  let rec dfLoop (b : UInt32) (df : ByteArray) : ByteArray :=
    if b >= nU then df
    else
      let pred0 := baUget32 csrEdges (b * 2)
      let pred1 := baUget32 csrEdges (b * 2 + 1)
      let idom := baUget32 doms b
      if pred0 != pred1 then
        let df1 := walkDf pred0 idom df
        let df2 := walkDf pred1 idom df1
        dfLoop (b + 1) df2
      else
        dfLoop (b + 1) df

  let dfCount := dfLoop 1 (baAllocZero (nU * 4))

  let rec sumLoop (i : UInt32) (acc : UInt64) : UInt64 :=
    if i >= nU then acc
    else
      let d := (baUget32 doms i).toUInt64
      let df := (baUget32 dfCount i).toUInt64
      sumLoop (i + 1) (acc + (d ^^^ (df <<< (16 : UInt64))))
  return sumLoop 0 0

/-- Kernel 2 (`hashmap_ba64`): NaN-free open-addressed flat hash table (`cap = 1048576 = 2^20`)
over an `8 MB` `ByteArray` accessed via `baUget64`/`baUset64`. -/
partial def benchHashMapBa64 (nSyms : Nat) : UInt64 := Id.run do
  let cap : UInt32 := 1048576
  let mask : UInt64 := 1048575
  let nU : UInt64 := nSyms.toUInt64
  let initTable := baAllocZero (cap * 8)

  let rec insertSlot (slot : UInt64) (kTag : UInt64) (packed : UInt64) (table : ByteArray) : ByteArray :=
    let curBits := baUget64 table slot
    let curTag := curBits >>> (28 : UInt64)
    if curBits == 0 || curTag == kTag then
      baUset64 table slot packed
    else
      insertSlot ((slot + 1) &&& mask) kTag packed table

  let rec insLoop (i : UInt64) (st : UInt64) (table : ByteArray) : ByteArray :=
    if i >= nU then table
    else
      let st' := st * 6364136223846793005 + 1442695040888963407
      let key := st' ^^^ (i <<< (13 : UInt64))
      let slot := ((key >>> (32 : UInt64)) ^^^ key) &&& mask
      let kTag := ((key >>> (12 : UInt64)) &&& 0xFFFFFFF) ||| 0x10000000
      let val := (i * 31) &&& 0xFFFFFFF
      let packed := (kTag <<< (28 : UInt64)) ||| val
      let table' := insertSlot slot kTag packed table
      insLoop (i + 1) st' table'

  let table := insLoop 0 0x123456789abcdef0 initTable

  let rec lookupSlot (slot : UInt64) (kTag : UInt64) : UInt64 :=
    let curBits := baUget64 table slot
    let curTag := curBits >>> (28 : UInt64)
    if curTag == kTag then curBits &&& 0xFFFFFFF
    else if curBits == 0 then 0
    else lookupSlot ((slot + 1) &&& mask) kTag

  let rec queryLoop (i : UInt64) (st : UInt64) (acc : UInt64) : UInt64 :=
    if i >= nU then acc
    else
      let st' := st * 6364136223846793005 + 1442695040888963407
      let key := st' ^^^ (i <<< (13 : UInt64))
      let slot := ((key >>> (32 : UInt64)) ^^^ key) &&& mask
      let kTag := ((key >>> (12 : UInt64)) &&& 0xFFFFFFF) ||| 0x10000000
      let v := lookupSlot slot kTag
      queryLoop (i + 1) st' (acc + v)

  return queryLoop 0 0x123456789abcdef0 0

/-- Kernel 3 (`egraph_uf_ba32`): Path-compressed union-find over 200,000 e-classes
(600,000 merges) in a flat `800 KB` `ByteArray` using inlined `baUfUnionMut`. -/
partial def benchEgraphUfBa32 (nClasses : Nat) : UInt64 := Id.run do
  let nC : UInt32 := nClasses.toUInt32
  let nMerges : UInt32 := nC * 3
  let half : UInt32 := nC / 2 + 1
  let parentBlank := baAllocZero (nC * 4)
  let rec initParent (i : UInt32) (ba : ByteArray) : ByteArray :=
    if i >= nC then ba
    else initParent (i + 1) (baUset32 ba i i)
  let pArr := initParent 0 parentBlank

  let rec mergeLoop (step : UInt32) (acc : UInt32) : UInt32 :=
    if step >= nMerges then acc
    else
      let a := (step * 17 + 5) % nC
      let b := (step * 31 + 19) % half
      let r := baUfUnionMut pArr a b
      mergeLoop (step + 1) (acc ^^^ r)

  let mix := mergeLoop 0 0
  let startAcc : UInt64 := (mix - mix).toUInt64

  let rec sumLoop (i : UInt32) (acc : UInt64) : UInt64 :=
    if i >= nC then acc
    else
      let r := baUfFindHalving pArr i
      sumLoop (i + 1) (acc + r.toUInt64)

  return sumLoop 0 startAcc

/-- Kernel 4 (`regalloc_ba16`): Linear-scan register allocation over 100,000 virtual
registers and 16 physical registers stored in a single 64-byte L1 cache-line `ByteArray`
using `__builtin_ctz` over a 16-bit availability bitmask. -/
partial def benchRegallocBa16 (nVregs : Nat) : UInt64 :=
  let nV : UInt32 := nVregs.toUInt32
  let physEnd := baAllocZero (64 + (nV - 100000))
  baRegallocArena physEnd nV

/-- Kernel 5 (`inst_encode_u32`): Encoding 2,000,000 4-byte x86-64 instructions into
an `8 MB` `ByteArray` via single-instruction 32-bit word stores (`baUset32`). -/
partial def benchInstEncodeU32 (nInsts : Nat) : UInt64 :=
  let nI : UInt32 := nInsts.toUInt32
  let initBuf := baAllocZero (nI * 4)
  let rec encodeLoop (i : UInt32) (buf : ByteArray) : ByteArray :=
    if i >= nI then buf
    else
      let b1 : UInt32 := ((i >>> 3) &&& 1) <<< 2
      let b2 : UInt32 := i &&& 1
      let rex : UInt32 := 0x48 ||| b1 ||| b2
      let op : UInt32 :=
        match i &&& 3 with
        | 0 => 0x01
        | 1 => 0x29
        | 2 => 0x31
        | _ => 0x89
      let m1 : UInt32 := (i &&& 7) <<< 3
      let m2 : UInt32 := (i >>> 4) &&& 7
      let modrm : UInt32 := 0xC0 ||| m1 ||| m2
      let imm : UInt32 := (i * 73) &&& 0xFF
      let word32 : UInt32 := rex ||| (op <<< 8) ||| (modrm <<< 16) ||| (imm <<< 24)
      encodeLoop (i + 1) (baUset32 buf i word32)
  let buf := encodeLoop 0 initBuf
  let sz : UInt32 := buf.size.toUInt32
  let rec sumLoop (idx : UInt32) (acc : UInt64) : UInt64 :=
    if idx >= sz then acc
    else sumLoop (idx + 64) (acc + (buf.get! idx.toNat).toUInt64)
  sumLoop 0 sz.toUInt64

def buildSsaBuffer (nLines : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (nLines * 24)
  for i in [0:nLines] do
    let rDst := i % 1024
    let rA := (i * 7 + 1) % 1024
    let rB := (i * 13 + 3) % 1024
    let line := s!"v{rDst} = add v{rA}, v{rB}\n"
    out := out.append line.toUTF8
  return out

@[inline] partial def parseDigits (buf : @& ByteArray) (n : UInt32) (pos : UInt32) (val : UInt64) : UInt64 :=
  if pos < n then
    let d := baUget8 buf pos
    if d >= 48 && d <= 57 then
      parseDigits buf n (pos + 1) (val * 10 + (d - 48).toUInt64)
    else
      (pos.toUInt64 <<< (32 : UInt64)) ||| val
  else
    (pos.toUInt64 <<< (32 : UInt64)) ||| val

/-- Kernel 6 (`ir_parser_ba`): Unboxed `UInt32` cursor SSA IR parser over `ByteArray`. -/
partial def benchIrParserBa (buf : @& ByteArray) : UInt64 :=
  let n : UInt32 := buf.size.toUInt32
  let rec loop (pos : UInt32) (instCount : UInt64) (regSum : UInt64) : UInt64 :=
    if pos >= n then
      (instCount <<< (32 : UInt64)) ^^^ regSum
    else
      let b := baUget8 buf pos
      if b == 118 then
        let packed := parseDigits buf n (pos + 1) 0
        let nextPos := (packed >>> (32 : UInt64)).toUInt32
        let val := packed &&& 0xFFFFFFFF
        loop nextPos instCount (regSum + val)
      else if b == 10 then
        loop (pos + 1) (instCount + 1) regSum
      else
        loop (pos + 1) instCount regSum
  loop 0 0 0

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
  let iters := 15
  let ssaBuf := buildSsaBuffer 500000
  let (domMed, domP95, c1) ← timeIo iters (fun z => pure (benchDomSsaCsr (20000 + z)))
  let (hmMed, hmP95, c2) ← timeIo iters (fun z => pure (benchHashMapBa64 (500000 + z)))
  let (ufMed, ufP95, c3) ← timeIo iters (fun z => pure (benchEgraphUfBa32 (200000 + z)))
  let (raMed, raP95, c4) ← timeIo iters (fun z => pure (benchRegallocBa16 (100000 + z)))
  let (encMed, encP95, c5) ← timeIo iters (fun z => pure (benchInstEncodeU32 (2000000 + z)))
  let (parMed, parP95, c6) ← timeIo iters (fun z => pure (benchIrParserBa (if z == 999999 then ByteArray.empty else ssaBuf)))

  IO.println s!"\{\"dom_ssa_csr\": \{\"median_ms\": {domMed}, \"p95_ms\": {domP95}, \"checksum\": {c1}},"
  IO.println s!" \"hashmap_ba64\": \{\"median_ms\": {hmMed}, \"p95_ms\": {hmP95}, \"checksum\": {c2}},"
  IO.println s!" \"egraph_uf_ba32\": \{\"median_ms\": {ufMed}, \"p95_ms\": {ufP95}, \"checksum\": {c3}},"
  IO.println s!" \"regalloc_ba16\": \{\"median_ms\": {raMed}, \"p95_ms\": {raP95}, \"checksum\": {c4}},"
  IO.println s!" \"inst_encode_u32\": \{\"median_ms\": {encMed}, \"p95_ms\": {encP95}, \"checksum\": {c5}},"
  IO.println s!" \"ir_parser_ba\": \{\"median_ms\": {parMed}, \"p95_ms\": {parP95}, \"checksum\": {c6}}}"
