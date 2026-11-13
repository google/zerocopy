-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import S16Chain.Link3AbiLowering

namespace S16Chain

/-!
# Link 4: Concrete x86-64 Machine Byte Encoding, Variable-Length Decoder & ISA Execution

Models the concrete x86-64 machine state (`X86State`), the exact 29-byte machine
code sequence from `llvm-objdump -d s16_fixture.o`:
```text
   0: 48 8d 04 3e                   leaq    (%rsi,%rdi), %rax
   4: 31 c9                         xorl    %ecx, %ecx
   6: 48 81 fe e9 03 00 00          cmpq    $0x3e9, %rsi
   d: 48 0f 43 c1                   cmovaeq %rcx, %rax
  11: 48 81 ff e9 03 00 00          cmpq    $0x3e9, %rdi
  18: 48 0f 43 c1                   cmovaeq %rcx, %rax
  1c: c3                            retq
```
and small-step instruction fetch/decode/execute (`runX86`).
-/

/-- Concrete x86-64 machine state with 64-bit instruction pointer `rip`,
16 general-purpose registers, carry flag `cf`, byte-addressed code memory, and
64-bit stack return-address slot read. -/
structure X86State where
  rip : BitVec 64
  regs : Reg64 → BitVec 64
  cf : Bool
  codeMem : BitVec 64 → UInt8
  readStack64 : BitVec 64 → BitVec 64

/-- The exact 29 machine bytes emitted by `rustc 1.99.1 -C opt-level=3` for
`add_bounded`. -/
def fixtureMachineBytes : List UInt8 := [
  -- 0x00: 48 8d 04 3e (leaq (%rsi,%rdi), %rax)
  0x48, 0x8d, 0x04, 0x3e,
  -- 0x04: 31 c9 (xorl %ecx, %ecx)
  0x31, 0xc9,
  -- 0x06: 48 81 fe e9 03 00 00 (cmpq $0x3e9, %rsi)
  0x48, 0x81, 0xfe, 0xe9, 0x03, 0x00, 0x00,
  -- 0x0d: 48 0f 43 c1 (cmovaeq %rcx, %rax)
  0x48, 0x0f, 0x43, 0xc1,
  -- 0x11: 48 81 ff e9 03 00 00 (cmpq $0x3e9, %rdi)
  0x48, 0x81, 0xff, 0xe9, 0x03, 0x00, 0x00,
  -- 0x18: 48 0f 43 c1 (cmovaeq %rcx, %rax)
  0x48, 0x0f, 0x43, 0xc1,
  -- 0x1c: c3 (retq)
  0xc3
]

theorem fixtureMachineBytes_length : fixtureMachineBytes.length = 29 := rfl

/-- Predicate stating that `bytes` are loaded contiguously in `codeMem` starting
at `base`. -/
def loadedAt (m : X86State) (base : BitVec 64) (bytes : List UInt8) : Prop :=
  ∀ (off : Nat) (b : UInt8),
    bytes[off]? = some b →
    m.codeMem (base + BitVec.ofNat 64 off) = b

/-- Variable-length x86-64 instruction decoder returning `(inst, byteLen)`. -/
def decodeX86At (codeMem : BitVec 64 → UInt8) (rip : BitVec 64) : Option (X86Inst × BitVec 64) :=
  let b0 := codeMem rip
  if b0 == 0xc3 then
    some (.retq, 1#64)
  else if b0 == 0x31 && codeMem (rip + 1#64) == 0xc9 then
    some (.xorZero .rcx, 2#64)
  else if b0 == 0x48 then
    let b1 := codeMem (rip + 1#64)
    let b2 := codeMem (rip + 2#64)
    let b3 := codeMem (rip + 3#64)
    if b1 == 0x8d && b2 == 0x04 && b3 == 0x3e then
      some (.leaAdd .rax .rsi .rdi, 4#64)
    else if b1 == 0x0f && b2 == 0x43 && b3 == 0xc1 then
      some (.cmovae .rax .rcx, 4#64)
    else if b1 == 0x81 && b2 == 0xfe && b3 == 0xe9 &&
            codeMem (rip + 4#64) == 0x03 &&
            codeMem (rip + 5#64) == 0x00 &&
            codeMem (rip + 6#64) == 0x00 then
      some (.cmpImm .rsi 1001#64, 7#64)
    else if b1 == 0x81 && b2 == 0xff && b3 == 0xe9 &&
            codeMem (rip + 4#64) == 0x03 &&
            codeMem (rip + 5#64) == 0x00 &&
            codeMem (rip + 6#64) == 0x00 then
      some (.cmpImm .rdi 1001#64, 7#64)
    else
      none
  else
    none

/-- Project `AsmRegState` from `X86State`. -/
def X86State.toAsm (m : X86State) : AsmRegState :=
  { regs := m.regs, cf := m.cf }

/-- Update `X86State` from `AsmRegState` and advance `rip` by `len`. -/
def X86State.withAsmAndRip (m : X86State) (a : AsmRegState) (nextRip : BitVec 64) : X86State :=
  { m with rip := nextRip, regs := a.regs, cf := a.cf }

/-- Single-step concrete x86-64 machine execution (`stepX86`). -/
def stepX86 (m : X86State) : Option X86State :=
  match decodeX86At m.codeMem m.rip with
  | none => none
  | some (.retq, _) =>
    let retTarget := m.readStack64 (m.regs .rsp)
    let a' := m.toAsm.setReg .rsp (m.regs .rsp + 8#64)
    some (m.withAsmAndRip a' retTarget)
  | some (inst, len) =>
    let a' := stepAsmInst m.toAsm inst
    some (m.withAsmAndRip a' (m.rip + len))

/-- Multi-step concrete x86-64 execution for `k` instructions (`runX86`). -/
def runX86 : Nat → X86State → Option X86State
  | 0, m => some m
  | k + 1, m =>
    match stepX86 m with
    | none => none
    | some m' => runX86 k m'

/-- Link 4 Concrete Fetch/Decode/Execute Theorem:
When `fixtureMachineBytes` is loaded at `codeBase` and `m_init.rip = codeBase`,
7 small-step x86-64 machine steps (`runX86 7 m_init`) decode all 7 variable-length
instructions (`+4, +2, +7, +4, +7, +4, retq`), compute `runAddBoundedBodyAsm`,
pop the return address from `m_init.regs .rsp`, and increment `rsp` by 8. -/
theorem link4_x86_decode_and_run_7_steps
    (m_init : X86State) (codeBase : BitVec 64)
    (h_rip : m_init.rip = codeBase)
    (h_code : loadedAt m_init codeBase fixtureMachineBytes) :
    let a_body := runAddBoundedBodyAsm m_init.toAsm
    let a_final := a_body.setReg .rsp (m_init.regs .rsp + 8#64)
    let retTarget := m_init.readStack64 (m_init.regs .rsp)
    runX86 7 m_init = some (m_init.withAsmAndRip a_final retTarget) := by
  have b0  : m_init.codeMem (codeBase + 0#64)  = 0x48 := h_code 0  0x48 rfl
  have b1  : m_init.codeMem (codeBase + 1#64)  = 0x8d := h_code 1  0x8d rfl
  have b2  : m_init.codeMem (codeBase + 2#64)  = 0x04 := h_code 2  0x04 rfl
  have b3  : m_init.codeMem (codeBase + 3#64)  = 0x3e := h_code 3  0x3e rfl
  have b4  : m_init.codeMem (codeBase + 4#64)  = 0x31 := h_code 4  0x31 rfl
  have b5  : m_init.codeMem (codeBase + 5#64)  = 0xc9 := h_code 5  0xc9 rfl
  have b6  : m_init.codeMem (codeBase + 6#64)  = 0x48 := h_code 6  0x48 rfl
  have b7  : m_init.codeMem (codeBase + 7#64)  = 0x81 := h_code 7  0x81 rfl
  have b8  : m_init.codeMem (codeBase + 8#64)  = 0xfe := h_code 8  0xfe rfl
  have b9  : m_init.codeMem (codeBase + 9#64)  = 0xe9 := h_code 9  0xe9 rfl
  have b10 : m_init.codeMem (codeBase + 10#64) = 0x03 := h_code 10 0x03 rfl
  have b11 : m_init.codeMem (codeBase + 11#64) = 0x00 := h_code 11 0x00 rfl
  have b12 : m_init.codeMem (codeBase + 12#64) = 0x00 := h_code 12 0x00 rfl
  have b13 : m_init.codeMem (codeBase + 13#64) = 0x48 := h_code 13 0x48 rfl
  have b14 : m_init.codeMem (codeBase + 14#64) = 0x0f := h_code 14 0x0f rfl
  have b15 : m_init.codeMem (codeBase + 15#64) = 0x43 := h_code 15 0x43 rfl
  have b16 : m_init.codeMem (codeBase + 16#64) = 0xc1 := h_code 16 0xc1 rfl
  have b17 : m_init.codeMem (codeBase + 17#64) = 0x48 := h_code 17 0x48 rfl
  have b18 : m_init.codeMem (codeBase + 18#64) = 0x81 := h_code 18 0x81 rfl
  have b19 : m_init.codeMem (codeBase + 19#64) = 0xff := h_code 19 0xff rfl
  have b20 : m_init.codeMem (codeBase + 20#64) = 0xe9 := h_code 20 0xe9 rfl
  have b21 : m_init.codeMem (codeBase + 21#64) = 0x03 := h_code 21 0x03 rfl
  have b22 : m_init.codeMem (codeBase + 22#64) = 0x00 := h_code 22 0x00 rfl
  have b23 : m_init.codeMem (codeBase + 23#64) = 0x00 := h_code 23 0x00 rfl
  have b24 : m_init.codeMem (codeBase + 24#64) = 0x48 := h_code 24 0x48 rfl
  have b25 : m_init.codeMem (codeBase + 25#64) = 0x0f := h_code 25 0x0f rfl
  have b26 : m_init.codeMem (codeBase + 26#64) = 0x43 := h_code 26 0x43 rfl
  have b27 : m_init.codeMem (codeBase + 27#64) = 0xc1 := h_code 27 0xc1 rfl
  have b28 : m_init.codeMem (codeBase + 28#64) = 0xc3 := h_code 28 0xc3 rfl
  have b0' : m_init.codeMem codeBase = 0x48 := by simpa using b0
  have dec0 : decodeX86At m_init.codeMem codeBase = some (.leaAdd .rax .rsi .rdi, 4#64) := by
    simp [decodeX86At, b0', b1, b2, b3]
  let a1 := stepAsmInst m_init.toAsm (.leaAdd .rax .rsi .rdi)
  let m1 := m_init.withAsmAndRip a1 (codeBase + 4#64)
  have step1 : stepX86 m_init = some m1 := by
    simp [stepX86, h_rip, dec0, m1, a1]
  have dec1 : decodeX86At m_init.codeMem (codeBase + 4#64) = some (.xorZero .rcx, 2#64) := by
    simp [decodeX86At, BitVec.add_assoc, b4, b5]
  let a2 := stepAsmInst a1 (.xorZero .rcx)
  let m2 := m_init.withAsmAndRip a2 (codeBase + 6#64)
  have step2 : stepX86 m1 = some m2 := by
    simp [stepX86, dec1, m1, m2, a2, X86State.withAsmAndRip, X86State.toAsm, BitVec.add_assoc]
  have dec2 : decodeX86At m_init.codeMem (codeBase + 6#64) = some (.cmpImm .rsi 1001#64, 7#64) := by
    simp [decodeX86At, BitVec.add_assoc, b6, b7, b8, b9, b10, b11, b12]
  let a3 := stepAsmInst a2 (.cmpImm .rsi 1001#64)
  let m3 := m_init.withAsmAndRip a3 (codeBase + 13#64)
  have step3 : stepX86 m2 = some m3 := by
    simp [stepX86, dec2, m2, m3, a3, X86State.withAsmAndRip, X86State.toAsm, BitVec.add_assoc]
  have dec3 : decodeX86At m_init.codeMem (codeBase + 13#64) = some (.cmovae .rax .rcx, 4#64) := by
    simp [decodeX86At, BitVec.add_assoc, b13, b14, b15, b16]
  let a4 := stepAsmInst a3 (.cmovae .rax .rcx)
  let m4 := m_init.withAsmAndRip a4 (codeBase + 17#64)
  have step4 : stepX86 m3 = some m4 := by
    simp [stepX86, dec3, m3, m4, a4, X86State.withAsmAndRip, X86State.toAsm, BitVec.add_assoc]
  have dec4 : decodeX86At m_init.codeMem (codeBase + 17#64) = some (.cmpImm .rdi 1001#64, 7#64) := by
    simp [decodeX86At, BitVec.add_assoc, b17, b18, b19, b20, b21, b22, b23]
  let a5 := stepAsmInst a4 (.cmpImm .rdi 1001#64)
  let m5 := m_init.withAsmAndRip a5 (codeBase + 24#64)
  have step5 : stepX86 m4 = some m5 := by
    simp [stepX86, dec4, m4, m5, a5, X86State.withAsmAndRip, X86State.toAsm, BitVec.add_assoc]
  have dec5 : decodeX86At m_init.codeMem (codeBase + 24#64) = some (.cmovae .rax .rcx, 4#64) := by
    simp [decodeX86At, BitVec.add_assoc, b24, b25, b26, b27]
  let a6 := stepAsmInst a5 (.cmovae .rax .rcx)
  let m6 := m_init.withAsmAndRip a6 (codeBase + 28#64)
  have step6 : stepX86 m5 = some m6 := by
    simp [stepX86, dec5, m5, m6, a6, X86State.withAsmAndRip, X86State.toAsm, BitVec.add_assoc]
  have dec6 : decodeX86At m_init.codeMem (codeBase + 28#64) = some (.retq, 1#64) := by
    simp [decodeX86At, b28]
  have hrsp : a6.regs .rsp = m_init.regs .rsp := by
    have h_l3 := (link3_abi_lowering_sound m_init.toAsm).2.1
    exact h_l3
  have step7 : stepX86 m6 = some (m_init.withAsmAndRip (a6.setReg .rsp (m_init.regs .rsp + 8#64)) (m_init.readStack64 (m_init.regs .rsp))) := by
    simp [stepX86, dec6, m6, X86State.withAsmAndRip, X86State.toAsm, hrsp]
  simp [runX86, step1, step2, step3, step4, step5, step6, step7, runAddBoundedBodyAsm, a1, a2, a3, a4, a5, a6]

end S16Chain
