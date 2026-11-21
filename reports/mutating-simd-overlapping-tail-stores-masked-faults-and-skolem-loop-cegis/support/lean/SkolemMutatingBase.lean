-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic

/-!
# Tactic-Free Operational ISA Models & Reference Specifications for Mutating SIMD Loops (`SkolemMutatingBase`)

Contains zero tactics and zero `._unsafe_rec` constants (`@Nat.rec` throughout).
Defines:
1. Six mutating SIMD / `asm!` operational state machines and byte-exact scalar
   reference specifications (`VpshufbNibbleLut`, `Avx2AsciiTolowerInplace`,
   `DisjointXorOverlapTail`, `PreloadedInplaceXorTail`,
   `VpmaskmovdFaultSuppressingTail`, and `ScalarEpilogueShortDispatch`).
2. Six realistic mutating-SIMD bug models refuted by synthesized counterexamples
   in `RefuteMutatingSimd6.lean`.
-/

namespace SkolemMutatingBase

def W64 : Nat := 18446744073709551616

abbrev Mem := Nat → Nat

def writeByte (mem : Mem) (addr val : Nat) : Mem :=
  fun q => match Nat.beq q addr with
    | true  => val % 256
    | false => mem q

def writeSpan (mem0 : Mem) (base : Nat) (valFn : Nat → Nat) (width : Nat) : Mem :=
  @Nat.rec (fun _ => Mem)
    mem0
    (fun lane prev => writeByte prev (base + lane) (valFn lane))
    width

def checkPermSpan (perm : Nat → Bool) (base width : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun lane ok => ok && perm (base + lane))
    width

def DisjointSlices (dst src len : Nat) : Prop :=
  dst + len ≤ src ∨ src + len ≤ dst

-- ============================================================================
-- 1. `vpshufb` 16-Entry Nibble-LUT Transform (`VpshufbNibbleLut`)
-- ============================================================================

/-- Hardware x86-64 `VPSHUFB` lane semantics:
    if bit 7 of `ctrl` is set (`ctrl % 256 ≥ 128`), output is `0`;
    otherwise output is `lut (ctrl % 16) % 256`. -/
def vpshufbLane (lut : Nat → Nat) (ctrl : Nat) : Nat :=
  let c := ctrl % 256
  match Nat.ble 128 c with
  | true  => 0
  | false => (lut (c % 16)) % 256

def hexAsciiLut (nib : Nat) : Nat :=
  let n := nib % 16
  match Nat.blt n 10 with
  | true  => 48 + n
  | false => 87 + n

def specNibbleLut (lut : Nat → Nat) (dst src len : Nat) (mem0 : Mem) (q : Nat) : Nat :=
  if dst ≤ q ∧ q < dst + len then
    (lut ((mem0 (src + (q - dst))) % 16)) % 256
  else
    mem0 q

structure VpshufbState where
  pc     : Nat
  halted : Bool
  dst    : Nat
  src    : Nat
  len    : Nat
  cursor : Nat
  lut    : Nat → Nat
  mem    : Mem

def stepVpshufb (s : VpshufbState) : VpshufbState :=
  if s.halted then s
  else if s.pc = 0 then
    { s with pc := 1, cursor := 0 }
  else if s.pc = 1 then
    if s.cursor + 32 < s.len then
      let m' := writeSpan s.mem (s.dst + s.cursor)
        (fun j => vpshufbLane s.lut (Nat.land (s.mem (s.src + s.cursor + j)) 15)) 32
      { s with mem := m', cursor := s.cursor + 32 }
    else
      { s with pc := 2 }
  else
    let tail := s.len - 32
    let m' := writeSpan s.mem (s.dst + tail)
      (fun j => vpshufbLane s.lut (Nat.land (s.mem (s.src + tail + j)) 15)) 32
    { s with halted := true, mem := m' }

def runVpshufb (fuel : Nat) (s0 : VpshufbState) : VpshufbState :=
  @Nat.rec (fun _ => VpshufbState → VpshufbState)
    (fun s => s)
    (fun _ ih s => ih (stepVpshufb s))
    fuel s0

-- ============================================================================
-- 2. In-Place AVX2 `ascii_tolower` With Unbuffered Overlapping Tail
-- ============================================================================

/-- Exact AVX2 signed-bias range comparison (`'A'..'Z'` = `65..90`):
    `biased = (b + 63) % 256` maps `65..90` to signed `-128..-103` (`128..153` unsigned).
    `vpcmpgtb(-102, biased)` sets mask `0xFF` iff `128 ≤ biased < 154`, adding `0x20` (`32`). -/
def avx2TolowerLane (b : Nat) : Nat :=
  let u := b % 256
  let biased := (u + 63) % 256
  match Nat.ble 128 biased && Nat.blt biased 154 with
  | true  => (u + 32) % 256
  | false => u

def specAsciiTolowerByte (b : Nat) : Nat :=
  let u := b % 256
  if 65 ≤ u ∧ u ≤ 90 then u + 32 else u

def specAsciiTolowerInplace (buf len : Nat) (mem0 : Mem) (q : Nat) : Nat :=
  if buf ≤ q ∧ q < buf + len then
    specAsciiTolowerByte (mem0 q)
  else
    mem0 q

structure TolowerState where
  pc     : Nat
  halted : Bool
  buf    : Nat
  len    : Nat
  cursor : Nat
  mem    : Mem

def stepTolower (s : TolowerState) : TolowerState :=
  if s.halted then s
  else if s.pc = 0 then
    { s with pc := 1, cursor := 0 }
  else if s.pc = 1 then
    if s.cursor + 32 < s.len then
      let m' := writeSpan s.mem (s.buf + s.cursor)
        (fun j => avx2TolowerLane (s.mem (s.buf + s.cursor + j))) 32
      { s with mem := m', cursor := s.cursor + 32 }
    else
      { s with pc := 2 }
  else
    let tail := s.len - 32
    let m' := writeSpan s.mem (s.buf + tail)
      (fun j => avx2TolowerLane (s.mem (s.buf + tail + j))) 32
    { s with halted := true, mem := m' }

def runTolower (fuel : Nat) (s0 : TolowerState) : TolowerState :=
  @Nat.rec (fun _ => TolowerState → TolowerState)
    (fun s => s)
    (fun _ ih s => ih (stepTolower s))
    fuel s0

-- ============================================================================
-- 3. Disjoint `xor_stream` With Unbuffered Overlapping Tail
-- ============================================================================

def xorLane (key b : Nat) : Nat :=
  (Nat.xor (b % 256) (key % 256)) % 256

def specDisjointXor (dst src len key : Nat) (mem0 : Mem) (q : Nat) : Nat :=
  if dst ≤ q ∧ q < dst + len then
    xorLane key (mem0 (src + (q - dst)))
  else
    mem0 q

structure DisjointXorState where
  pc     : Nat
  halted : Bool
  dst    : Nat
  src    : Nat
  len    : Nat
  key    : Nat
  cursor : Nat
  mem    : Mem

def stepDisjointXor (s : DisjointXorState) : DisjointXorState :=
  if s.halted then s
  else if s.pc = 0 then
    { s with pc := 1, cursor := 0 }
  else if s.pc = 1 then
    if s.cursor + 32 < s.len then
      let m' := writeSpan s.mem (s.dst + s.cursor)
        (fun j => xorLane s.key (s.mem (s.src + s.cursor + j))) 32
      { s with mem := m', cursor := s.cursor + 32 }
    else
      { s with pc := 2 }
  else
    let tail := s.len - 32
    let m' := writeSpan s.mem (s.dst + tail)
      (fun j => xorLane s.key (s.mem (s.src + tail + j))) 32
    { s with halted := true, mem := m' }

def runDisjointXor (fuel : Nat) (s0 : DisjointXorState) : DisjointXorState :=
  @Nat.rec (fun _ => DisjointXorState → DisjointXorState)
    (fun s => s)
    (fun _ ih s => ih (stepDisjointXor s))
    fuel s0

-- ============================================================================
-- 4. Preloaded-Tail In-Place `xor_stream` (`PreloadedInplaceXorTail`)
-- ============================================================================

def specInplaceXor (buf len key : Nat) (mem0 : Mem) (q : Nat) : Nat :=
  if buf ≤ q ∧ q < buf + len then
    xorLane key (mem0 q)
  else
    mem0 q

structure PreloadXorState where
  pc      : Nat
  halted  : Bool
  buf     : Nat
  len     : Nat
  key     : Nat
  cursor  : Nat
  tailReg : Nat → Nat
  mem     : Mem

def stepPreloadXor (s : PreloadXorState) : PreloadXorState :=
  if s.halted then s
  else if s.pc = 0 then
    let tail := s.len - 32
    let snap := fun j => s.mem (s.buf + tail + j)
    { s with pc := 1, cursor := 0, tailReg := snap }
  else if s.pc = 1 then
    if s.cursor + 32 < s.len then
      let m' := writeSpan s.mem (s.buf + s.cursor)
        (fun j => xorLane s.key (s.mem (s.buf + s.cursor + j))) 32
      { s with mem := m', cursor := s.cursor + 32 }
    else
      { s with pc := 2 }
  else
    let tail := s.len - 32
    let m' := writeSpan s.mem (s.buf + tail)
      (fun j => xorLane s.key (s.tailReg j)) 32
    { s with halted := true, mem := m' }

def runPreloadXor (fuel : Nat) (s0 : PreloadXorState) : PreloadXorState :=
  @Nat.rec (fun _ => PreloadXorState → PreloadXorState)
    (fun s => s)
    (fun _ ih s => ih (stepPreloadXor s))
    fuel s0

-- ============================================================================
-- 5. Fault-Suppressing `VPMASKMOVD` Tail (`VpmaskmovdFaultSuppressingTail`)
-- ============================================================================

def execVpmaskmovd8
    (perm : Nat → Bool) (base remWords key : Nat) (mem0 : Mem) : Bool × Mem :=
  @Nat.rec (fun _ => Bool × Mem)
    (false, mem0)
    (fun lane prev =>
      let (flt, mCur) := prev
      if flt then (true, mCur)
      else
        match Nat.blt lane remWords with
        | false => (false, mCur)
        | true  =>
          let lAddr := base + 4 * lane
          match checkPermSpan perm lAddr 4 with
          | false => (true, mCur)
          | true  =>
            let mNext := writeSpan mCur lAddr
              (fun b => xorLane key (mCur (lAddr + b))) 4
            (false, mNext))
    8

def specVpmaskmovXor (buf totalWords key : Nat) (mem0 : Mem) (q : Nat) : Nat :=
  if buf ≤ q ∧ q < buf + 4 * totalWords then
    xorLane key (mem0 q)
  else
    mem0 q

structure VpmaskmovState where
  pc         : Nat
  halted     : Bool
  faulted    : Bool
  buf        : Nat
  totalWords : Nat
  key        : Nat
  wordCur    : Nat
  perm       : Nat → Bool
  mem        : Mem

def stepVpmaskmov (s : VpmaskmovState) : VpmaskmovState :=
  if s.halted || s.faulted then s
  else if s.pc = 0 then
    { s with pc := 1, wordCur := 0 }
  else if s.pc = 1 then
    if s.wordCur + 8 ≤ s.totalWords then
      let addr := s.buf + 4 * s.wordCur
      match checkPermSpan s.perm addr 32 with
      | false => { s with faulted := true, halted := true }
      | true  =>
        let m' := writeSpan s.mem addr (fun j => xorLane s.key (s.mem (addr + j))) 32
        { s with mem := m', wordCur := s.wordCur + 8 }
    else
      { s with pc := 2 }
  else
    let addr := s.buf + 4 * s.wordCur
    let remWords := s.totalWords - s.wordCur
    let (flt, m') := execVpmaskmovd8 s.perm addr remWords s.key s.mem
    { s with halted := true, faulted := flt, mem := m' }

def runVpmaskmov (fuel : Nat) (s0 : VpmaskmovState) : VpmaskmovState :=
  @Nat.rec (fun _ => VpmaskmovState → VpmaskmovState)
    (fun s => s)
    (fun _ ih s => ih (stepVpmaskmov s))
    fuel s0

-- ============================================================================
-- 6. Short-Slice `len < 32` Scalar Epilogue Dispatch (`ScalarEpilogueShortDispatch`)
-- ============================================================================

def addConstLane (c b : Nat) : Nat :=
  (b % 256 + c % 256) % 256

def specShortDispatchAdd (buf len c : Nat) (mem0 : Mem) (q : Nat) : Nat :=
  if buf ≤ q ∧ q < buf + len then
    addConstLane c (mem0 q)
  else
    mem0 q

structure ShortDispatchState where
  pc      : Nat
  halted  : Bool
  faulted : Bool
  buf     : Nat
  len     : Nat
  addVal  : Nat
  cursor  : Nat
  tailReg : Nat → Nat
  perm    : Nat → Bool
  mem     : Mem

def stepShortDispatch (s : ShortDispatchState) : ShortDispatchState :=
  if s.halted || s.faulted then s
  else if s.pc = 0 then
    if s.len < 32 then
      { s with pc := 3, cursor := 0 }
    else
      let tail := s.len - 32
      match checkPermSpan s.perm (s.buf + tail) 32 with
      | false => { s with faulted := true, halted := true }
      | true  =>
        let snap := fun j => s.mem (s.buf + tail + j)
        { s with pc := 1, cursor := 0, tailReg := snap }
  else if s.pc = 1 then
    if s.cursor + 32 < s.len then
      let addr := s.buf + s.cursor
      match checkPermSpan s.perm addr 32 with
      | false => { s with faulted := true, halted := true }
      | true  =>
        let m' := writeSpan s.mem addr (fun j => addConstLane s.addVal (s.mem (addr + j))) 32
        { s with mem := m', cursor := s.cursor + 32 }
    else
      { s with pc := 2 }
  else if s.pc = 2 then
    let tail := s.len - 32
    let addr := s.buf + tail
    match checkPermSpan s.perm addr 32 with
    | false => { s with faulted := true, halted := true }
    | true  =>
      let m' := writeSpan s.mem addr (fun j => addConstLane s.addVal (s.tailReg j)) 32
      { s with halted := true, mem := m' }
  else
    if s.cursor < s.len then
      let addr := s.buf + s.cursor
      match s.perm addr with
      | false => { s with faulted := true, halted := true }
      | true  =>
        let m' := writeByte s.mem addr (addConstLane s.addVal (s.mem addr))
        { s with mem := m', cursor := s.cursor + 1 }
    else
      { s with halted := true }

def runShortDispatch (fuel : Nat) (s0 : ShortDispatchState) : ShortDispatchState :=
  @Nat.rec (fun _ => ShortDispatchState → ShortDispatchState)
    (fun s => s)
    (fun _ ih s => ih (stepShortDispatch s))
    fuel s0

-- ============================================================================
-- 7. Six Mutating-SIMD Bug Models Refuted by Dual Counterexample Synthesis
-- ============================================================================

/-- Bug 1: In-place non-idempotent `xor_stream` using unbuffered overlapping tail `[len - 32 .. len)`. -/
def bug01InplaceXorUnbuffered (buf len key : Nat) (mem0 : Mem) : Mem :=
  let steps := (len - 1) / 32
  let memLoop := @Nat.rec (fun _ => Mem) mem0
    (fun k m => writeSpan m (buf + 32 * k) (fun j => xorLane key (m (buf + 32 * k + j))) 32)
    steps
  let tail := len - 32
  writeSpan memLoop (buf + tail) (fun j => xorLane key (memLoop (buf + tail + j))) 32

/-- Bug 2: Missing `len < 32` guard before 64-bit wrapping subtraction `(len - 32) mod 2^64`.
    Returns `true` if the 32-byte tail store stays inside `[buf .. buf + len)`, `false` on OOB/fault! -/
def bug02UnguardedTailInBounds64 (len : Nat) : Bool :=
  let tailOff64 := (len + (W64 - 32)) % W64
  Nat.ble (tailOff64 + 32) len

/-- Bug 3: Using `MASKMOVDQU` / `VMASKMOVDQU` at a page/permission boundary where trailing
    bytes have `mask = 0` yet map to `PROT_READ` / `PROT_NONE` (`perm = false`). -/
def bug03MaskmovdquSafe (perm : Nat → Bool) (rdi activeBytes : Nat) : Bool :=
  let _ := activeBytes
  checkPermSpan perm rdi 16

/-- Bug 4: Indexing a 16-entry `vpshufb` LUT without masking `ctrl & 0x0F`, allowing bit 7 (`0x80`)
    to zero the destination byte instead of reading `lut[ctrl & 0x0F]`. -/
def bug04VpshufbUnmasked (lut : Nat → Nat) (inputByte : Nat) : Nat :=
  vpshufbLane lut inputByte

/-- Bug 5: Aligned 32-byte RMW slack-writeback (`vmovdqa` load -> blend -> `vmovdqa` store)
    clobbering a concurrent/interleaved update `siblingDelta` at `algn + sliceLen`. -/
def bug05AlignedRmwSlackWriteback
    (algn sliceLen siblingDelta : Nat) (mem0 : Mem) : Mem :=
  let snap := fun j => mem0 (algn + j)
  let memInterleaved := writeByte mem0 (algn + sliceLen) ((mem0 (algn + sliceLen) + siblingDelta) % 256)
  writeSpan memInterleaved algn
    (fun j => if j < sliceLen then xorLane 0x42 (snap j) else snap j) 32

/-- Bug 6: Inline `asm!` `rep movsb` executed without `cld` when `RFLAGS.DF == true`,
    decrementing `rdi`/`rsi` instead of incrementing (`addr = dst + len - ...` vs `dst - i`)! -/
def bug06RepMovsbNoCld (df : Bool) (dst src len : Nat) (mem0 : Mem) : Mem :=
  @Nat.rec (fun _ => Mem)
    mem0
    (fun i m =>
      let dAddr := match df with
        | false => dst + i
        | true  => dst - i
      let sAddr := match df with
        | false => src + i
        | true  => src - i
      writeByte m dAddr (mem0 sAddr))
    len

end SkolemMutatingBase
