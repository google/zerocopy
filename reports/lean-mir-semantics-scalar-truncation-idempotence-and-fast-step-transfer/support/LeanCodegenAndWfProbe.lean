-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-
  Lean 4 Native C Codegen and WF WHNF Verification Probe (`LeanCodegenAndWfProbe.lean`)
  Zero-sorry, zero-warning standalone Lean 4 probe covering:
  1. Pure CSE / `elimDeadVars` / `LCNF.floatLetIn` Benchmark Loop Hoisting (`lean --c` + `leanc -O3`)
  2. Perceus `@&` Borrow-Alias Self-Copy Quadratic Trap (`lean_inc_ref` -> `!lean_is_exclusive`) vs Single-Owned Argument (`m_rc == 1`)
  3. Well-Founded Recursion Translation WHNF Timeout (`DeflateFreqs.lean:77-160`, `DeflateDynamic.lean:62-116`) vs Outlined Helpers + `Subtype` Witness
  4. `Adler32` `data.data.foldl` Boxed `Array UInt8` Allocation (`16 MiB` per `2 MiB`) & `do`-Loop `MProd` Boxing vs Unboxed Tail-Recursive `USize`/`UInt32`
-/

-- ============================================================================
-- SECTION 1: Pure CSE, `elimDeadVars`, and `LCNF.floatLetIn` Clock-Sinking Traps
-- ============================================================================

@[noinline]
def pureChecksumLoop (data : @& ByteArray) (i n : USize) (acc : UInt64)
    (hsz : n.toNat ≤ data.size) : UInt64 :=
  if hlt : i < n then
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have _him : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp hlt
    have hb : i.toNat < data.size := Nat.lt_of_lt_of_le _him hsz
    let b := data.uget i hb
    let acc' := (acc ^^^ b.toUInt64) * 1099511628211 + i.toUInt64
    pureChecksumLoop data (i + 1) n acc' hsz
  else
    acc
termination_by n.toNat - i.toNat
decreasing_by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have _him : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp hlt
  have hmax : n.toNat < USize.size := USize.toNat_lt_size n
  have e : (i + 1).toNat = i.toNat + 1 := by
    rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt; omega
  omega

@[noinline]
def pureChecksum (data : ByteArray) (salt : UInt64) : UInt64 :=
  pureChecksumLoop data 0 data.size.toUSize salt (by
    simp only [Nat.toUSize]
    exact Nat.mod_le _ _)

-- Trap 1A: Dead pure `let` binding inside timed loop -> deleted by `LCNF.elimDeadVars`
@[noinline]
def benchDeadLet (data : ByteArray) (salt : UInt64) (reps : Nat) : IO Nat := do
  let mut totalNs : Nat := 0
  for _ in [:reps] do
    let t0 ← IO.monoNanosNow
    let _dead := pureChecksum data salt
    let t1 ← IO.monoNanosNow
    totalNs := totalNs + (t1 - t0)
  return totalNs

-- Trap 1B: Duplicate pure calls -> collapsed into 1 call (`shlq $2`) by `LCNF.cse`
@[noinline]
def pureChecksum4x (data : ByteArray) (salt : UInt64) : UInt64 :=
  let r1 := pureChecksum data salt
  let r2 := pureChecksum data salt
  let r3 := pureChecksum data salt
  let r4 := pureChecksum data salt
  r1 + r2 + r3 + r4

-- Trap 1C: Pure `let r := pureChecksum data salt` between `t0` and `t1`, used after `t1`
-- -> `LCNF.floatLetIn` sinks `l_pureChecksum` into the `if r == 0` branch *after* `t1`!
@[noinline]
def benchPureLetSunk (data : ByteArray) (salt : UInt64) (reps : Nat) : IO Nat := do
  let mut totalNs : Nat := 0
  for _ in [:reps] do
    let t0 ← IO.monoNanosNow
    let r := pureChecksum data salt
    let t1 ← IO.monoNanosNow
    if r == 0 then
      IO.eprintln "unreachable"
    totalNs := totalNs + (t1 - t0)
  return totalNs

-- Trap 1D: `IO` wrapper without `@[noinline]` -> `LCNF.simp` inlines `pure` and `floatLetIn` sinks past `t1`
@[inline]
def doChecksumInlineIO (data : ByteArray) (salt : UInt64) : IO UInt64 := do
  let r := pureChecksum data salt
  return r

@[noinline]
def benchInlineIOSunk (data : ByteArray) (salt : UInt64) (reps : Nat) : IO Nat := do
  let mut totalNs : Nat := 0
  for _ in [:reps] do
    let t0 ← IO.monoNanosNow
    let r ← doChecksumInlineIO data salt
    let t1 ← IO.monoNanosNow
    if r == 0 then
      IO.eprintln "unreachable"
    totalNs := totalNs + (t1 - t0)
  return totalNs

-- Correct Barrier (`lean_zip_BenchSilesia.lean` pattern): `@[noinline]` IO wrapper + post-timer consumer
@[noinline]
def doChecksumBarrier (data : ByteArray) (salt : UInt64) : IO UInt64 := do
  let r := pureChecksum data salt
  return r

@[noinline]
def benchNoinlineIOBarrier (data : ByteArray) (salt : UInt64) (reps : Nat) : IO Nat := do
  let mut totalNs : Nat := 0
  for _ in [:reps] do
    let t0 ← IO.monoNanosNow
    let r ← doChecksumBarrier data salt
    let t1 ← IO.monoNanosNow
    if r == 0 then
      IO.eprintln "unreachable"
    totalNs := totalNs + (t1 - t0)
  return totalNs

-- ============================================================================
-- SECTION 2: Perceus `@&` Borrow-Alias Self-Copy Quadratic Trap vs Owned FFI
-- ============================================================================

@[noinline]
def copySelfBorrowOwned (src : @& ByteArray) (dst : ByteArray) (srcOff len : Nat) : ByteArray :=
  ByteArray.copySlice src srcOff dst dst.size len false

@[noinline]
def callBorrowOwnedSameArg (a : ByteArray) (srcOff len : Nat) : ByteArray :=
  copySelfBorrowOwned a a srcOff len

@[noinline]
def stepAliased (a : ByteArray) (srcOff len : Nat) : ByteArray :=
  ByteArray.copySlice a srcOff a a.size len false

@[extern "probe_byte_array_copy_within"]
def copyWithinOwned (a : ByteArray) (srcOff len : @& Nat) : ByteArray :=
  ByteArray.copySlice a srcOff a a.size len false

@[noinline]
def stepOwned (a : ByteArray) (srcOff len : Nat) : ByteArray :=
  copyWithinOwned a srcOff len

@[noinline]
def benchAliasedSteps (seed : ByteArray) (steps chunkLen : Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut buf := seed
  for _ in [:steps] do
    buf := stepAliased buf 0 chunkLen
  let t1 ← IO.monoNanosNow
  return (buf.size, t1 - t0)

@[noinline]
def benchOwnedSteps (seed : ByteArray) (steps chunkLen : Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut buf := seed
  for _ in [:steps] do
    buf := stepOwned buf 0 chunkLen
  let t1 ← IO.monoNanosNow
  return (buf.size, t1 - t0)

-- ============================================================================
-- SECTION 3: Well-Founded Recursion Translation WHNF Timeout vs Outlined Helpers
-- ============================================================================

def lengthBase : Array UInt16 :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
    35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

def lengthExtra : Array UInt8 :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
    3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

def distBase : Array UInt16 :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
    257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

def distExtra : Array UInt8 :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
    7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

def findTableCode.go (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) (i : Nat) (hsize : baseTable.size ≤ extraTable.size) :
    Option (Nat × Nat × UInt32) :=
  if h1 : i + 1 < baseTable.size then
    if baseTable[i + 1].toNat > value then
      let extra := (extraTable[i]'(by omega)).toNat
      let extraVal := (value - (baseTable[i]'(by omega)).toNat).toUInt32
      some (i, extra, extraVal)
    else
      findTableCode.go baseTable extraTable value (i + 1) hsize
  else if h2 : i < baseTable.size then
    let extra := (extraTable[i]'(by omega)).toNat
    let extraVal := (value - baseTable[i].toNat).toUInt32
    some (i, extra, extraVal)
  else
    none
termination_by baseTable.size - i

def findTableCode (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) (hsize : baseTable.size ≤ extraTable.size := by decide) :
    Option (Nat × Nat × UInt32) :=
  findTableCode.go baseTable extraTable value 0 hsize

def findLengthCode (length : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode lengthBase lengthExtra length

def findDistCode (dist : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode distBase distExtra dist

theorem findTableCode_go_idx_lt {baseTable : Array UInt16} {extraTable : Array UInt8}
    {value i : Nat} {hsize : baseTable.size ≤ extraTable.size}
    {idx extraN : Nat} {extraV : UInt32}
    (h : findTableCode.go baseTable extraTable value i hsize = some (idx, extraN, extraV)) :
    idx < baseTable.size := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact findTableCode_go_idx_lt h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact nomatch h
termination_by baseTable.size - i

theorem findLengthCode_idx_lt {len idx extraN : Nat} {extraV : UInt32}
    (h : findLengthCode len = some (idx, extraN, extraV)) : idx < 29 :=
  findTableCode_go_idx_lt h

theorem findDistCode_idx_lt {dist dIdx dExtraN : Nat} {dExtraV : UInt32}
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) : dIdx < 30 :=
  findTableCode_go_idx_lt h

@[inline] def bumpLitFreqP (litLenFreqs : {a : Array Nat // a.size = 286}) (w : UInt32) :
    {a : Array Nat // a.size = 286} :=
  let idx := w.toUInt8.toNat
  have hidx : idx < litLenFreqs.val.size := by
    have := UInt8.toNat_lt w.toUInt8; have := litLenFreqs.property; omega
  ⟨litLenFreqs.val.set! idx (litLenFreqs.val[idx] + 1),
    by rw [Array.size_set!]; exact litLenFreqs.property⟩

@[inline] def bumpRefLitFreqP (litLenFreqs : {a : Array Nat // a.size = 286}) (w : UInt32) :
    {a : Array Nat // a.size = 286} :=
  match hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) with
  | none => litLenFreqs
  | some (lIdx, _, _) =>
    have hsym : lIdx + 257 < litLenFreqs.val.size := by
      have := findLengthCode_idx_lt hflc
      have := litLenFreqs.property; omega
    ⟨litLenFreqs.val.set! (lIdx + 257) (litLenFreqs.val[lIdx + 257] + 1),
      by rw [Array.size_set!]; exact litLenFreqs.property⟩

@[inline] def bumpRefDistFreqP (distFreqs : {a : Array Nat // a.size = 30}) (w : UInt32) :
    {a : Array Nat // a.size = 30} :=
  match hfdc : findDistCode ((w &&& 0xFFFF).toNat) with
  | none => distFreqs
  | some (dIdx, _, _) =>
    have hd : dIdx < distFreqs.val.size := by
      have := findDistCode_idx_lt hfdc
      have := distFreqs.property; omega
    ⟨distFreqs.val.set! dIdx (distFreqs.val[dIdx] + 1),
      by rw [Array.size_set!]; exact distFreqs.property⟩

def tokenFreqsP_Fast (tokens : Array UInt32) : Array Nat × Array Nat :=
  go tokens ⟨(Array.replicate 286 0).set! 256 1,
      by rw [Array.size_set!, Array.size_replicate]⟩
    ⟨Array.replicate 30 0, by rw [Array.size_replicate]⟩ 0
where
  go (tokens : Array UInt32) (litLenFreqs : {a : Array Nat // a.size = 286})
      (distFreqs : {a : Array Nat // a.size = 30}) (i : Nat) : Array Nat × Array Nat :=
    if h : i < tokens.size then
      let w := tokens[i]
      if w &&& ((1 : UInt32) <<< 31) = 0 then
        go tokens (bumpLitFreqP litLenFreqs w) distFreqs (i + 1)
      else
        go tokens (bumpRefLitFreqP litLenFreqs w) (bumpRefDistFreqP distFreqs w) (i + 1)
    else (litLenFreqs.val, distFreqs.val)
  termination_by tokens.size - i

-- ============================================================================
-- SECTION 4: `Adler32` `data.data.foldl` vs `do`-Loop `MProd` vs Unboxed `USize`
-- ============================================================================

def MOD_ADLER : Nat := 65521

def updateByte (s : Nat × Nat) (b : UInt8) : Nat × Nat :=
  let a := (s.1 + b.toNat) % MOD_ADLER
  let b' := (s.2 + a) % MOD_ADLER
  (a, b')

def updateBytes (s : Nat × Nat) (data : ByteArray) : Nat × Nat :=
  data.data.foldl updateByte s

def finish (s : Nat × Nat) : UInt32 :=
  (s.2 <<< 16 ||| s.1).toUInt32

def adler32BoxedFold (data : ByteArray) : UInt32 :=
  finish (updateBytes (1, 0) data)

@[noinline]
def adler32DoForLoop (data : ByteArray) : UInt32 := Id.run do
  let mut a : UInt32 := 1
  let mut b : UInt32 := 0
  let n := data.size
  for h : i in [0:n] do
    let byte := (data[i]'h.upper).toUInt32
    a := (a + byte) % 65521
    b := (b + a) % 65521
  return (b <<< 16) ||| a

@[noinline]
def adler32TailUSizeGo (data : @& ByteArray) (i n : USize) (a b : UInt32)
    (hsz : n.toNat ≤ data.size) : UInt32 :=
  if hlt : i < n then
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have _him : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp hlt
    have hb : i.toNat < data.size := Nat.lt_of_lt_of_le _him hsz
    let byte := (data.uget i hb).toUInt32
    let a' := (a + byte) % 65521
    let b' := (b + a') % 65521
    adler32TailUSizeGo data (i + 1) n a' b' hsz
  else
    (b <<< 16) ||| a
termination_by n.toNat - i.toNat
decreasing_by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have _him : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp hlt
  have hmax : n.toNat < USize.size := USize.toNat_lt_size n
  have e : (i + 1).toNat = i.toNat + 1 := by
    rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt; omega
  omega

@[noinline]
def adler32TailUSize (data : ByteArray) : UInt32 :=
  adler32TailUSizeGo data 0 data.size.toUSize 1 0 (by
    simp only [Nat.toUSize]
    exact Nat.mod_le _ _)

@[noinline]
def runAdlerBoxedFold (data : ByteArray) : IO UInt32 := return adler32BoxedFold data
@[noinline]
def runAdlerDoLoop (data : ByteArray) : IO UInt32 := return adler32DoForLoop data
@[noinline]
def runAdlerTailUSize (data : ByteArray) : IO UInt32 := return adler32TailUSize data

def main : IO Unit := do
  -- 1. Benchmark Loop Hoisting / Sinking Verification (64 KiB, 100 reps)
  let n1 := 65536
  let mut buf1 := ByteArray.emptyWithCapacity n1
  for i in [:n1] do
    buf1 := buf1.push (i % 251).toUInt8
  let reps := 100
  let nsDead ← benchDeadLet buf1 42 reps
  let nsPureSunk ← benchPureLetSunk buf1 42 reps
  let nsInlineSunk ← benchInlineIOSunk buf1 42 reps
  let nsBarrier ← benchNoinlineIOBarrier buf1 42 reps
  let c4x := pureChecksum4x buf1 42
  IO.println s!"[Probe 1] reps={reps} size={n1} c4x={c4x}: dead_ns={nsDead} ({nsDead/reps} ns/rep) pure_sunk_ns={nsPureSunk} ({nsPureSunk/reps} ns/rep) inline_io_sunk_ns={nsInlineSunk} ({nsInlineSunk/reps} ns/rep) barrier_ns={nsBarrier} ({nsBarrier/reps} ns/rep)"

  -- 2. Perceus Borrow-Alias Self-Copy Quadratic Trap vs Single-Owned Argument
  let mut seed := ByteArray.emptyWithCapacity 64
  for i in [:64] do
    seed := seed.push i.toUInt8
  let (szA1, nsA1) ← benchAliasedSteps seed 1000 64
  let (szO1, nsO1) ← benchOwnedSteps seed 1000 64
  let (szA4, nsA4) ← benchAliasedSteps seed 4000 64
  let (szO4, nsO4) ← benchOwnedSteps seed 4000 64
  IO.println s!"[Probe 2] steps=1000: sz={szA1}/{szO1} aliased_ns={nsA1} owned_ns={nsO1} | steps=4000: sz={szA4}/{szO4} aliased_ns={nsA4} owned_ns={nsO4} speedup={nsA4.toFloat / nsO4.toFloat}x"

  -- 3. WF Outlined Fast Sanity Check
  let sampleToks : Array UInt32 := #[0x00000041, 0x80050004]
  let (lf, df) := tokenFreqsP_Fast sampleToks
  IO.println s!"[Probe 3] tokenFreqsP_Fast sizes=({lf.size}, {df.size})"

  -- 4. Adler-32 2 MiB Comparison
  let n4 := 2 * 1024 * 1024
  let mut buf4 := ByteArray.emptyWithCapacity n4
  for i in [:n4] do
    buf4 := buf4.push (i % 251).toUInt8
  let t0 ← IO.monoNanosNow
  let c1 ← runAdlerBoxedFold buf4
  let t1 ← IO.monoNanosNow
  let c2 ← runAdlerDoLoop buf4
  let t2 ← IO.monoNanosNow
  let c3 ← runAdlerTailUSize buf4
  let t3 ← IO.monoNanosNow
  let mbps (ns : Nat) : Float := (n4.toFloat / 1000000.0) / (ns.toFloat / 1000000000.0)
  IO.println s!"[Probe 4] Adler32 2MiB: eq={c1 == c2 && c2 == c3} ({c1}) | lean_zip_ns={t1 - t0} ({mbps (t1 - t0)} MB/s) | do_loop_ns={t2 - t1} ({mbps (t2 - t1)} MB/s) | tail_usize_ns={t3 - t2} ({mbps (t3 - t2)} MB/s)"
