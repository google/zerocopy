-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Basic
import Init.Omega
import ByteX86Gcc

/-!
# `RustFfiSpecs`

Trusted safe-Rust FFI reference specifications and System V AMD64 `.o` equivalence
contracts (`prelude` + `Init.*` + `ByteX86Gcc` only, `0` `sorry`, `0` `isPartial`
via `Nat.rec`, `0` untrusted imports):

1. **Safe-Rust Functional & Memory-Framing Specifications:**
   - `rustFnv1a64`: 64-bit FNV-1a slice hash (`&[u8] -> u64`).
   - `rustAdler32Chunk`: Adler-32 chunk update (`(&[u8], u32) -> u32`, modulo `65521`).
   - `rustChecksumRolU8`: 32-bit `rotate_left(5)` + XOR checksum (`&[u8] -> u32`).
   - `rustAsciiTolowerByte` / `RustAsciiTolowerPost`: in-place `&mut [u8]` ASCII
     lowercasing with byte-exact non-slice memory framing.
   - `rustDotU8U16`: mixed-width `(&[u8], &[u16]) -> u32` wrapping dot product.
   - `RustXorStreamPost`: non-`restrict` `(&mut [u8], &[u8], u8)` streaming XOR
     cipher under safe-Rust `DisjointSlices` (`Tree Borrows` `&mut`/`&` exclusivity).
   - `rustEndpointsU64` and `rustSumU8ToU64`: safe-Rust specs for FFI bug refutation.
2. **Unified `CObjectMatchesRustContract` Predicate:**
   Universally quantifies over all initial `ByteX86Gcc.X64State`s satisfying `Pre`
   and all demonic `UndefChoice` flag/register streams `nd : Nat → UndefChoice`,
   requiring `ByteX86Gcc.runX64` on the literal ELF64 `.o` bytes to halt with
   `fault = false`, preserve `rsp` and `rbx, rbp, r12..r15`, preserve clean upper
   `YMM0..YMM15[255:128]` lanes, and satisfy `Post`.
-/

namespace RustFfiSpecs

open ByteX86Gcc

/-! ## Section 1: System V AMD64 ABI & Rust Slice Preconditions -/

def SysVCalleeSavedPreserved (s0 s1 : X64State) : Prop :=
  s1.regs .rsp = s0.regs .rsp ∧
  s1.regs .rbx = s0.regs .rbx ∧
  s1.regs .rbp = s0.regs .rbp ∧
  s1.regs .r12 = s0.regs .r12 ∧
  s1.regs .r13 = s0.regs .r13 ∧
  s1.regs .r14 = s0.regs .r14 ∧
  s1.regs .r15 = s0.regs .r15

def AllUpperYmmClean (s : X64State) : Prop :=
  ∀ idx : YmmIdx, BitVec.extractLsb' 128 128 (s.ymms idx) = 0#128

def UpperYmmCleanOrPreserved (s0 s1 : X64State) : Prop :=
  AllUpperYmmClean s0 → AllUpperYmmClean s1

def NoWrapSlice (ptr : BitVec 64) (byteLen : Nat) : Prop :=
  ptr.toNat + byteLen < 2 ^ 64

def DisjointSlices (p1 : BitVec 64) (len1 : Nat) (p2 : BitVec 64) (len2 : Nat) : Prop :=
  p1.toNat + len1 ≤ p2.toNat ∨ p2.toNat + len2 ≤ p1.toNat

def DisjointFromStack (ptr : BitVec 64) (byteLen : Nat)
    (rsp0 : BitVec 64) (stackReserve : Nat) : Prop :=
  stackReserve ≤ rsp0.toNat ∧
  (ptr.toNat + byteLen ≤ rsp0.toNat - stackReserve ∨ rsp0.toNat ≤ ptr.toNat)

def InSliceRange (addr ptr : BitVec 64) (byteLen : Nat) : Prop :=
  ptr.toNat ≤ addr.toNat ∧ addr.toNat < ptr.toNat + byteLen

def InPrivateStackWindow (addr rsp0 : BitVec 64) (stackReserve : Nat) : Prop :=
  rsp0.toNat - stackReserve ≤ addr.toNat ∧ addr.toNat < rsp0.toNat

/-- Read-only FFI call memory framing: every byte outside the callee's private
    stack window `[rsp0 - stackReserve, rsp0)` (including the return slot at
    `rsp0` and above, and all caller heap/slice buffers) is untouched. -/
def ReadOnlyMemFrame (m0 m1 : ByteMem) (rsp0 : BitVec 64) (stackReserve : Nat) : Prop :=
  ∀ addr : BitVec 64, ¬ InPrivateStackWindow addr rsp0 stackReserve → m1 addr = m0 addr

/-- Top-level `.o` $\equiv$ safe-Rust contract over `ByteX86Gcc.runX64`. -/
def CObjectMatchesRustContract (img : X64ObjImage) (entryOff : BitVec 64)
    (Pre : X64State → Prop) (Post : X64State → X64State → Prop) : Prop :=
  ∀ (s0 : X64State) (nd : Nat → UndefChoice),
    s0.halted = false →
    s0.fault = false →
    s0.rip = img.codeBase + entryOff →
    Pre s0 →
    ∃ steps : Nat,
      let s1 := runX64 img steps nd s0
      s1.halted = true ∧
      s1.fault = false ∧
      SysVCalleeSavedPreserved s0 s1 ∧
      UpperYmmCleanOrPreserved s0 s1 ∧
      Post s0 s1

/-! ## Section 2: Safe-Rust Reference Functions (`0` `isPartial` via `Nat.rec`) -/

/-- Safe-Rust reference for Kernel 1 (`c_fnv1a64`):
    ```rust
    pub fn rust_fnv1a64(buf: &[u8]) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in buf { h ^= b as u64; h = h.wrapping_mul(0x100000001b3); }
        h
    }
    ``` -/
def fnv1aStep (h : BitVec 64) (b : BitVec 8) : BitVec 64 :=
  (h ^^^ b.zeroExtend 64) * 0x100000001B3#64

def rustFnv1a64From (mem : ByteMem) (buf : BitVec 64) (len : Nat) (acc0 : BitVec 64) : BitVec 64 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
    (fun _ acc => acc)
    (fun _ ih p acc => ih (p + 1#64) (fnv1aStep acc (mem p)))
    len buf acc0

def rustFnv1a64 (mem : ByteMem) (buf : BitVec 64) (len : Nat) : BitVec 64 :=
  rustFnv1a64From mem buf len 0xCBF29CE484222325#64

/-- Safe-Rust reference for Kernel 2 (`c_adler32_chunk`):
    ```rust
    pub fn rust_adler32_chunk(buf: &[u8], init: u32) -> u32 {
        let (mut a, mut b) = (init & 0xffff, init >> 16);
        for &x in buf { a = (a + x as u32) % 65521; b = (b + a) % 65521; }
        (b << 16) | a
    }
    ``` -/
def adlerStep (ab : BitVec 32 × BitVec 32) (x : BitVec 8) : BitVec 32 × BitVec 32 :=
  let a' := BitVec.ofNat 32 ((ab.1.toNat + x.toNat) % 65521)
  let b' := BitVec.ofNat 32 ((ab.2.toNat + a'.toNat) % 65521)
  (a', b')

def rustAdler32Loop (mem : ByteMem) (buf : BitVec 64) (len : Nat)
    (a0 b0 : BitVec 32) : BitVec 32 × BitVec 32 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 32 × BitVec 32 → BitVec 32 × BitVec 32)
    (fun _ ab => ab)
    (fun _ ih p ab => ih (p + 1#64) (adlerStep ab (mem p)))
    len buf (a0, b0)

def rustAdler32Chunk (mem : ByteMem) (buf : BitVec 64) (len : Nat) (init : BitVec 32) : BitVec 32 :=
  let (a, b) := rustAdler32Loop mem buf len (init &&& 0xFFFF#32) (init >>> 16)
  (b <<< 16) ||| a

/-- Safe-Rust reference for Kernel 3 (`c_checksum_rol_u8`):
    ```rust
    pub fn rust_checksum_rol_u8(buf: &[u8]) -> u32 {
        buf.iter().fold(0u32, |acc, &b| acc.rotate_left(5) ^ (b as u32))
    }
    ``` -/
def rolXorStep (acc : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  BitVec.rotateLeft acc 5 ^^^ b.zeroExtend 32

def rustChecksumRolFrom (mem : ByteMem) (buf : BitVec 64) (len : Nat) (acc0 : BitVec 32) : BitVec 32 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 32 → BitVec 32)
    (fun _ acc => acc)
    (fun _ ih p acc => ih (p + 1#64) (rolXorStep acc (mem p)))
    len buf acc0

def rustChecksumRolU8 (mem : ByteMem) (buf : BitVec 64) (len : Nat) : BitVec 32 :=
  rustChecksumRolFrom mem buf len 0#32

/-- Safe-Rust reference for Kernel 4 (`c_ascii_tolower`):
    ```rust
    pub fn rust_ascii_tolower(buf: &mut [u8]) {
        for b in buf { if b.wrapping_sub(b'A') < 26 { *b = b.wrapping_add(32); } }
    }
    ``` -/
def rustAsciiTolowerByte (c : BitVec 8) : BitVec 8 :=
  if (c - 65#8).toNat < 26 then c + 32#8 else c

def RustAsciiTolowerPost (m0 m1 : ByteMem) (buf : BitVec 64) (len : Nat)
    (rsp0 : BitVec 64) (stackReserve : Nat) : Prop :=
  (∀ i : Nat, i < len →
    m1 (buf + BitVec.ofNat 64 i) = rustAsciiTolowerByte (m0 (buf + BitVec.ofNat 64 i))) ∧
  (∀ addr : BitVec 64,
    ¬ InSliceRange addr buf len →
    ¬ InPrivateStackWindow addr rsp0 stackReserve →
    m1 addr = m0 addr)

/-- Safe-Rust reference for Kernel 5 (`c_dot_u8_u16`):
    ```rust
    pub fn rust_dot_u8_u16(a: &[u8], b: &[u16]) -> u32 {
        a.iter().zip(b).fold(0u32, |s, (&x, &y)| s.wrapping_add((x as u32) * (y as u32)))
    }
    ``` -/
def dotStepU8U16 (sum : BitVec 32) (x : BitVec 8) (y : BitVec 16) : BitVec 32 :=
  sum + x.zeroExtend 32 * y.zeroExtend 32

def rustDotU8U16From (mem : ByteMem) (aPtr bPtr : BitVec 64) (len : Nat)
    (sum0 : BitVec 32) : BitVec 32 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 32 → BitVec 32)
    (fun _ _ s => s)
    (fun _ ih pa pb s =>
      ih (pa + 1#64) (pb + 2#64) (dotStepU8U16 s (mem pa) (readMem16 mem pb)))
    len aPtr bPtr sum0

def rustDotU8U16 (mem : ByteMem) (aPtr bPtr : BitVec 64) (len : Nat) : BitVec 32 :=
  rustDotU8U16From mem aPtr bPtr len 0#32

/-- Safe-Rust reference postcondition for Kernel 6 (`c_xor_stream`):
    ```rust
    pub fn rust_xor_stream(dst: &mut [u8], src: &[u8], key: u8) {
        for (d, &s) in dst.iter_mut().zip(src) { *d = s ^ key; }
    }
    ``` -/
def RustXorStreamPost (m0 m1 : ByteMem) (dst src : BitVec 64) (len : Nat)
    (key : BitVec 8) (rsp0 : BitVec 64) (stackReserve : Nat) : Prop :=
  (∀ i : Nat, i < len →
    m1 (dst + BitVec.ofNat 64 i) = m0 (src + BitVec.ofNat 64 i) ^^^ key) ∧
  (∀ addr : BitVec 64,
    ¬ InSliceRange addr dst len →
    ¬ InPrivateStackWindow addr rsp0 stackReserve →
    m1 addr = m0 addr)

/-- Safe-Rust reference for Bug 1 (`rust_endpoints_u64(buf: &[u8]) -> u64`). -/
def rustEndpointsU64 (mem : ByteMem) (buf : BitVec 64) (len : Nat) : BitVec 64 :=
  match len with
  | 0     => 0#64
  | k + 1 => (mem buf).zeroExtend 64 + (mem (buf + BitVec.ofNat 64 k)).zeroExtend 64

/-- Safe-Rust reference for Bug 4 (`rust_sum_u8_to_u64(buf: &[u8]) -> u64`). -/
def rustSumU8From (mem : ByteMem) (buf : BitVec 64) (len : Nat) (acc0 : BitVec 64) : BitVec 64 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 64 → BitVec 64)
    (fun _ acc => acc)
    (fun _ ih p acc => ih (p + 1#64) (acc + (mem p).zeroExtend 64))
    len buf acc0

def rustSumU8ToU64 (mem : ByteMem) (buf : BitVec 64) (len : Nat) : BitVec 64 :=
  rustSumU8From mem buf len 0#64

/-! ## Section 3: Concrete Per-Kernel Pre/Post Contracts -/

def Fnv1a64Pre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let buf := s0.regs .rdi
  let len := (s0.regs .rsi).toNat
  NoWrapSlice buf len ∧ DisjointFromStack buf len (s0.regs .rsp) stackReserve

def Fnv1a64Post (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  s1.regs .rax = rustFnv1a64 s0.mem (s0.regs .rdi) (s0.regs .rsi).toNat ∧
  ReadOnlyMemFrame s0.mem s1.mem (s0.regs .rsp) stackReserve

def Adler32Pre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let buf := s0.regs .rdi
  let len := (s0.regs .rsi).toNat
  NoWrapSlice buf len ∧ DisjointFromStack buf len (s0.regs .rsp) stackReserve

def Adler32Post (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  BitVec.extractLsb' 0 32 (s1.regs .rax) =
    rustAdler32Chunk s0.mem (s0.regs .rdi) (s0.regs .rsi).toNat
      (BitVec.extractLsb' 0 32 (s0.regs .rdx)) ∧
  ReadOnlyMemFrame s0.mem s1.mem (s0.regs .rsp) stackReserve

def ChecksumRolPre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let buf := s0.regs .rdi
  let len := (s0.regs .rsi).toNat
  NoWrapSlice buf len ∧ DisjointFromStack buf len (s0.regs .rsp) stackReserve

def ChecksumRolPost (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  BitVec.extractLsb' 0 32 (s1.regs .rax) =
    rustChecksumRolU8 s0.mem (s0.regs .rdi) (s0.regs .rsi).toNat ∧
  ReadOnlyMemFrame s0.mem s1.mem (s0.regs .rsp) stackReserve

def AsciiTolowerPre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let buf := s0.regs .rdi
  let len := (s0.regs .rsi).toNat
  NoWrapSlice buf len ∧ DisjointFromStack buf len (s0.regs .rsp) stackReserve

def AsciiTolowerContractPost (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  RustAsciiTolowerPost s0.mem s1.mem (s0.regs .rdi) (s0.regs .rsi).toNat
    (s0.regs .rsp) stackReserve

def DotU8U16Pre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let aPtr := s0.regs .rdi
  let bPtr := s0.regs .rsi
  let len  := (s0.regs .rdx).toNat
  2 * len < 2 ^ 64 ∧
  NoWrapSlice aPtr len ∧
  NoWrapSlice bPtr (2 * len) ∧
  DisjointFromStack aPtr len (s0.regs .rsp) stackReserve ∧
  DisjointFromStack bPtr (2 * len) (s0.regs .rsp) stackReserve

def DotU8U16Post (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  BitVec.extractLsb' 0 32 (s1.regs .rax) =
    rustDotU8U16 s0.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rdx).toNat ∧
  ReadOnlyMemFrame s0.mem s1.mem (s0.regs .rsp) stackReserve

def XorStreamPre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let dst := s0.regs .rdi
  let src := s0.regs .rsi
  let len := (s0.regs .rdx).toNat
  NoWrapSlice dst len ∧
  NoWrapSlice src len ∧
  DisjointSlices dst len src len ∧
  DisjointFromStack dst len (s0.regs .rsp) stackReserve ∧
  DisjointFromStack src len (s0.regs .rsp) stackReserve

def XorStreamContractPost (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  RustXorStreamPost s0.mem s1.mem (s0.regs .rdi) (s0.regs .rsi) (s0.regs .rdx).toNat
    (BitVec.extractLsb' 0 8 (s0.regs .rcx)) (s0.regs .rsp) stackReserve

def Bug1EndpointsPre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let buf := s0.regs .rdi
  let len := (s0.regs .rsi).toNat
  NoWrapSlice buf len ∧ DisjointFromStack buf len (s0.regs .rsp) stackReserve

def Bug1EndpointsPost (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  s1.regs .rax = rustEndpointsU64 s0.mem (s0.regs .rdi) (s0.regs .rsi).toNat ∧
  ReadOnlyMemFrame s0.mem s1.mem (s0.regs .rsp) stackReserve

def Bug4SumPre (stackReserve : Nat) (s0 : X64State) : Prop :=
  let buf := s0.regs .rdi
  let len := (s0.regs .rsi).toNat
  AllUpperYmmClean s0 ∧
  NoWrapSlice buf len ∧
  DisjointFromStack buf len (s0.regs .rsp) stackReserve

def Bug4SumPost (stackReserve : Nat) (s0 s1 : X64State) : Prop :=
  s1.regs .rax = rustSumU8ToU64 s0.mem (s0.regs .rdi) (s0.regs .rsi).toNat ∧
  ReadOnlyMemFrame s0.mem s1.mem (s0.regs .rsp) stackReserve

end RustFfiSpecs
