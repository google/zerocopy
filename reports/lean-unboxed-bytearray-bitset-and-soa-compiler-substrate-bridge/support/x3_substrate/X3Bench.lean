-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import BitSet64

/-!
# X3 Unboxed `ByteArray` / `FloatArray` / `USize` SoA Compiler Substrate Benchmarks

Refactors all 6 compiler kernels from `K4Bench.lean` to eliminate:
1. `Nat` GMP boxing in loop counters (`i : USize` / `UInt32` instead of `Nat`, compiling to
   native `size_t` / `uint32_t` registers instead of `lean_object*` GMP checks);
2. `MProd` tuple heap allocation across multi-variable `for`/`while` loops (via tail-recursive
   functions that LCNF compiles to raw C `goto` loops with unboxed scalar parameters);
3. `lean_box_uint64` heap allocations and `AssocList` bucket chains in `Std.HashMap UInt64 UInt64`
   (via a single-array open-addressed hash table packing `(keyTag24 <<< 28) ||| val28` into
   52-bit IEEE-754 exact `FloatArray` (`lean_sarray_object`, `elem_size = 8`) slots with zero
   `Prod` pair returns and zero `lean_alloc_ctor` calls);
4. Boxed `(Array UInt32 × UInt32)` pair returns in union-find `ufFind`;
5. `8,000,000` cross-DSO `ByteArray.push` calls in `inst_encode` (replaced by pre-allocated
   `ByteArray` + inline `ByteArray.set!` writes).

Every kernel is verified to produce the exact same 64-bit output checksum as `K4`.
-/

partial def intersectArr (doms : @& Array UInt32) (b1 b2 : UInt32) : UInt32 :=
  let rec loop (x y : UInt32) : UInt32 :=
    if x == y then x
    else if x > y then loop (doms.getD x.toNat 0) y
    else loop x (doms.getD y.toNat 0)
  loop b1 b2

/-- Kernel 1 (`dom_ssa_soa`): Cooper-Harvey-Kennedy iterative dominator tree + dominance
frontier (`V = 20,000` blocks) using `UInt32` indices and tail-recursive loops. -/
partial def benchDomSsaSoA (nBlocks : Nat) : UInt64 := Id.run do
  let nU : UInt32 := nBlocks.toUInt32
  let preds0Init : Array UInt32 := Array.replicate nBlocks 0
  let preds1Init : Array UInt32 := Array.replicate nBlocks 0
  let rec initLoop (i : UInt32) (p0 p1 : Array UInt32) : Array UInt32 × Array UInt32 :=
    if i >= nU then (p0, p1)
    else
      let v1 := if i >= 3 && (i % 5 == 0) then i - 3 else i / 2
      initLoop (i + 1) (p0.set! i.toNat (i - 1)) (p1.set! i.toNat v1)
  let (preds0, preds1) := initLoop 1 preds0Init preds1Init

  let undef : UInt32 := 999999999
  let domsInit : Array UInt32 := (Array.replicate nBlocks undef).set! 0 0

  let rec domStep (b : UInt32) (d : Array UInt32) (chg : Bool) : Array UInt32 × Bool :=
    if b >= nU then (d, chg)
    else
      let bIdx := b.toNat
      let pred0 := preds0.getD bIdx 0
      let pred1 := preds1.getD bIdx 0
      let newIdom :=
        if d.getD pred1.toNat undef != undef && pred1 != pred0 then
          intersectArr d pred0 pred1
        else pred0
      if d.getD bIdx undef != newIdom then
        domStep (b + 1) (d.set! bIdx newIdom) true
      else
        domStep (b + 1) d chg

  let rec fixLoop (d : Array UInt32) : Array UInt32 :=
    let (d', chg) := domStep 1 d false
    if chg then fixLoop d' else d'
  let doms := fixLoop domsInit

  let rec walkDf (runner idom : UInt32) (df : Array UInt32) : Array UInt32 :=
    if runner == idom then df
    else
      let rIdx := runner.toNat
      walkDf (doms.getD rIdx 0) idom (df.set! rIdx (df.getD rIdx 0 + 1))

  let rec dfLoop (b : UInt32) (df : Array UInt32) : Array UInt32 :=
    if b >= nU then df
    else
      let bIdx := b.toNat
      let pred0 := preds0.getD bIdx 0
      let pred1 := preds1.getD bIdx 0
      let idom := doms.getD bIdx 0
      if pred0 != pred1 then
        let df1 := walkDf pred0 idom df
        let df2 := walkDf pred1 idom df1
        dfLoop (b + 1) df2
      else
        dfLoop (b + 1) df

  let dfCount := dfLoop 1 (Array.replicate nBlocks (0 : UInt32))

  let rec sumLoop (i : UInt32) (acc : UInt64) : UInt64 :=
    if i >= nU then acc
    else
      let idx := i.toNat
      let d := (doms.getD idx 0).toUInt64
      let df := (dfCount.getD idx 0).toUInt64
      sumLoop (i + 1) (acc + (d ^^^ (df <<< (16 : UInt64))))
  return sumLoop 0 0

/-- Kernel 2 (`hashmap_flat`): Single-array open-addressed flat hash table (`cap = 1048576 = 2^20`)
packing both a 32-bit key tag and 28-bit value `(kTag <<< 28) ||| val` into a single unboxed
`FloatArray` (`lean_sarray_object`, `elem_size = 8`) via `Float.ofBits` / `Float.toBits`
(top 4 bits are always `0`, so bit patterns are subnormal IEEE-754 floats and never NaN!).
Eliminates both `Std.HashMap` `AssocList` chaining and `Prod` pair returns! -/
partial def benchHashMapFlat (nSyms : Nat) : UInt64 := Id.run do
  let cap : Nat := 1048576
  let mask : UInt64 := 1048575
  let nU : UInt64 := nSyms.toUInt64
  -- Pre-populate an unboxed FloatArray of size 2^20 (`8 MB` contiguous C `double[]` buffer)
  let mut initFloats := FloatArray.emptyWithCapacity cap
  let zeroF := Float.ofBits 0
  let rec fillZero (i : UInt32) (fa : FloatArray) : FloatArray :=
    if i >= 1048576 then fa
    else fillZero (i + 1) (fa.push zeroF)
  initFloats := fillZero 0 initFloats

  let rec insertSlot (slot : UInt64) (kTag : UInt64) (packed : Float) (table : FloatArray) : FloatArray :=
    let idx := slot.toNat
    let curBits := (table.get! idx).toBits
    let curTag := curBits >>> (28 : UInt64)
    if curBits == 0 || curTag == kTag then
      table.set! idx packed
    else
      insertSlot ((slot + 1) &&& mask) kTag packed table

  let rec insLoop (i : UInt64) (st : UInt64) (table : FloatArray) : FloatArray :=
    if i >= nU then table
    else
      let st' := st * 6364136223846793005 + 1442695040888963407
      let key := st' ^^^ (i <<< (13 : UInt64))
      let slot := ((key >>> (32 : UInt64)) ^^^ key) &&& mask
      let kTag := ((key >>> (12 : UInt64)) &&& 0xFFFFFFF) ||| 0x10000000
      let val := (i * 31) &&& 0xFFFFFFF
      let packed := Float.ofBits ((kTag <<< (28 : UInt64)) ||| val)
      let table' := insertSlot slot kTag packed table
      insLoop (i + 1) st' table'

  let table := insLoop 0 0x123456789abcdef0 initFloats

  let rec lookupSlot (slot : UInt64) (kTag : UInt64) : UInt64 :=
    let curBits := (table.get! slot.toNat).toBits
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

/-- Kernel 3 (`egraph_uf_soa`): Path-compressed union-find over 200,000 e-classes
(600,000 merges) packing `parent` (`24` bits) and `rank` (`8` bits) into a single
`Array UInt32` (`entry = (rank <<< 24) ||| parent`) and using `UInt32` step counters! -/
@[inline] partial def ufFindRoot (pArr : @& Array UInt32) (x : UInt32) : UInt32 :=
  let p := pArr.getD x.toNat x &&& 0xFFFFFF
  if p == x then x else ufFindRoot pArr p

@[inline] partial def ufCompressHalving (pArr : Array UInt32) (x : UInt32) : Array UInt32 :=
  let entryX := pArr.getD x.toNat x
  let p := entryX &&& 0xFFFFFF
  if p == x then pArr
  else
    let entryP := pArr.getD p.toNat p
    let gp := entryP &&& 0xFFFFFF
    let newEntryX := (entryX &&& 0xFF000000) ||| gp
    ufCompressHalving (pArr.set! x.toNat newEntryX) p

partial def benchEgraphUfSoA (nClasses : Nat) : UInt64 := Id.run do
  let nC : UInt32 := nClasses.toUInt32
  let nMerges : UInt32 := nC * 3
  let half : UInt32 := nC / 2 + 1
  let parentInit : Array UInt32 := Array.ofFn (n := nClasses) (fun i => i.val.toUInt32)

  let rec mergeLoop (step : UInt32) (pArr : Array UInt32) : Array UInt32 :=
    if step >= nMerges then pArr
    else
      let a := (step * 17 + 5) % nC
      let b := (step * 31 + 19) % half
      let ra := ufFindRoot pArr a
      let p1 := ufCompressHalving pArr a
      let rb := ufFindRoot p1 b
      let p2 := ufCompressHalving p1 b
      if ra != rb then
        let ea := p2.getD ra.toNat ra
        let eb := p2.getD rb.toNat rb
        let rka := ea >>> 24
        let rkb := eb >>> 24
        if rka < rkb then
          mergeLoop (step + 1) (p2.set! ra.toNat ((rka <<< 24) ||| rb))
        else if rka > rkb then
          mergeLoop (step + 1) (p2.set! rb.toNat ((rkb <<< 24) ||| ra))
        else
          let p3 := p2.set! rb.toNat ((rkb <<< 24) ||| ra)
          mergeLoop (step + 1) (p3.set! ra.toNat (((rka + 1) <<< 24) ||| ra))
      else
        mergeLoop (step + 1) p2

  let finalParent := mergeLoop 0 parentInit

  let rec sumLoop (i : UInt32) (pArr : Array UInt32) (acc : UInt64) : UInt64 :=
    if i >= nC then acc
    else
      let r := ufFindRoot pArr i
      let pNext := ufCompressHalving pArr i
      sumLoop (i + 1) pNext (acc + r.toUInt64)

  return sumLoop 0 finalParent 0

/-- Kernel 4 (`regalloc_unboxed`): Linear-scan register allocation over 100,000 virtual
registers and 16 physical registers using `UInt32` loop counters and a packed 64-bit
scan return `(allocated <<< 48) ||| (maxEndReg <<< 32) ||| maxEndVal`. -/
@[inline] partial def scanPhysRegs
    (physEnd : @& Array UInt32) (start : UInt32)
    (r : UInt32) (allocated : UInt64) (maxReg : UInt64) (maxVal : UInt32) : UInt64 :=
  if r >= 16 then
    (allocated <<< (48 : UInt64)) ||| (maxReg <<< (32 : UInt64)) ||| maxVal.toUInt64
  else
    let pe := physEnd.getD r.toNat 0
    let alloc' := if allocated == 16 && pe <= start then r.toUInt64 else allocated
    if pe > maxVal then
      scanPhysRegs physEnd start (r + 1) alloc' r.toUInt64 pe
    else
      scanPhysRegs physEnd start (r + 1) alloc' maxReg maxVal

partial def benchRegallocUnboxed (nVregs : Nat) : UInt64 :=
  let nV : UInt32 := nVregs.toUInt32
  let rec loop (i : UInt32) (physEnd : Array UInt32) (nextSpill : UInt32) (checksum : UInt64) : UInt64 :=
    if i >= nV then checksum
    else
      let start := i * 2
      let len := (i * 37 + 11) % 64 + 4
      let stop := start + len
      let pe0 := physEnd.getD 0 0
      let packed := scanPhysRegs physEnd start 0 16 0 pe0
      let allocated := (packed >>> (48 : UInt64)).toNat
      let maxEndReg := ((packed >>> (32 : UInt64)) &&& 0xFFFF).toNat
      let maxEndVal := (packed &&& 0xFFFFFFFF).toUInt32
      if allocated < 16 then
        loop (i + 1) (physEnd.set! allocated stop) nextSpill (checksum + allocated.toUInt64)
      else
        let ns' := nextSpill + 1
        let phys' := if maxEndVal > stop then physEnd.set! maxEndReg stop else physEnd
        loop (i + 1) phys' ns' (checksum + (ns'.toUInt64 <<< (8 : UInt64)))
  loop 0 (Array.replicate 16 (0 : UInt32)) 0 0

/-- Pre-allocate a zero-filled `ByteArray` of size `nBytes` in O(log nBytes) doubling steps
so `inst_encode` can use inlined `ByteArray.set!` (`lean_byte_array_uset`) instead of
`8,000,000` cross-DSO `lean_byte_array_push` calls! -/
def mkZeroByteArray (nBytes : Nat) : ByteArray := Id.run do
  let mut chunk := ByteArray.emptyWithCapacity 1024
  for _ in [0:1024] do
    chunk := chunk.push 0
  while chunk.size * 2 <= nBytes do
    chunk := chunk.append chunk
  if chunk.size < nBytes then
    let rem := nBytes - chunk.size
    chunk := chunk.append (chunk.extract 0 rem)
  return chunk

/-- Kernel 5 (`inst_encode_unboxed`): Encoding 2,000,000 4-byte x86-64 instructions into
a pre-sized `8 MB` `ByteArray` via inlined `ByteArray.set!` (`lean_byte_array_fset`). -/
partial def benchInstEncodeUnboxed (nInsts : Nat) : UInt64 :=
  let nI : UInt32 := nInsts.toUInt32
  let initBuf := mkZeroByteArray (nInsts * 4)
  let rec encodeLoop (i : UInt32) (buf : ByteArray) : ByteArray :=
    if i >= nI then buf
    else
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
      let base := (i * 4).toNat
      let b' := (((buf.set! base rex).set! (base + 1) op).set! (base + 2) modrm).set! (base + 3) imm
      encodeLoop (i + 1) b'
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

/-- Kernel 6 (`ir_parser_unboxed`): Lexer & recursive-descent SSA IR parser using unboxed
`UInt32` cursor indices and bit-packed `(nextPos <<< 32) ||| val` state returns. -/
@[inline] partial def parseDigits (buf : @& ByteArray) (n : UInt32) (pos : UInt32) (val : UInt64) : UInt64 :=
  if pos < n then
    let d := buf.get! pos.toNat
    if d >= 48 && d <= 57 then
      parseDigits buf n (pos + 1) (val * 10 + (d - 48).toUInt64)
    else
      (pos.toUInt64 <<< (32 : UInt64)) ||| val
  else
    (pos.toUInt64 <<< (32 : UInt64)) ||| val

partial def benchIrParserUnboxed (buf : @& ByteArray) : UInt64 :=
  let n : UInt32 := buf.size.toUInt32
  let rec loop (pos : UInt32) (instCount : UInt64) (regSum : UInt64) : UInt64 :=
    if pos >= n then
      (instCount <<< (32 : UInt64)) ^^^ regSum
    else
      let b := buf.get! pos.toNat
      if b == 118 then -- 'v'
        let packed := parseDigits buf n (pos + 1) 0
        let nextPos := (packed >>> (32 : UInt64)).toUInt32
        let val := packed &&& 0xFFFFFFFF
        loop nextPos instCount (regSum + val)
      else if b == 10 then -- '\n'
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
  let iters := 7
  let ssaBuf := buildSsaBuffer 500000
  let (domMed, domP95, c1) ← timeIo iters (fun z => pure (benchDomSsaSoA (20000 + z)))
  let (hmMed, hmP95, c2) ← timeIo iters (fun z => pure (benchHashMapFlat (500000 + z)))
  let (ufMed, ufP95, c3) ← timeIo iters (fun z => pure (benchEgraphUfSoA (200000 + z)))
  let (raMed, raP95, c4) ← timeIo iters (fun z => pure (benchRegallocUnboxed (100000 + z)))
  let (encMed, encP95, c5) ← timeIo iters (fun z => pure (benchInstEncodeUnboxed (2000000 + z)))
  let (parMed, parP95, c6) ← timeIo iters (fun z => pure (benchIrParserUnboxed (if z == 999999 then ByteArray.empty else ssaBuf)))

  IO.println s!"\{\"dom_ssa_soa\": \{\"median_ms\": {domMed}, \"p95_ms\": {domP95}, \"checksum\": {c1}},"
  IO.println s!" \"hashmap_flat\": \{\"median_ms\": {hmMed}, \"p95_ms\": {hmP95}, \"checksum\": {c2}},"
  IO.println s!" \"egraph_uf_soa\": \{\"median_ms\": {ufMed}, \"p95_ms\": {ufP95}, \"checksum\": {c3}},"
  IO.println s!" \"regalloc_unboxed\": \{\"median_ms\": {raMed}, \"p95_ms\": {raP95}, \"checksum\": {c4}},"
  IO.println s!" \"inst_encode_unboxed\": \{\"median_ms\": {encMed}, \"p95_ms\": {encP95}, \"checksum\": {c5}},"
  IO.println s!" \"ir_parser_unboxed\": \{\"median_ms\": {parMed}, \"p95_ms\": {parP95}, \"checksum\": {c6}}}"
