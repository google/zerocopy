-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import S16Chain.Link2W6Opt

namespace S16Chain

/-!
# Link 3: System V AMD64 ABI & Symbolic x86-64 Instruction Lowering

Lowers `evalSsaPostO3` to the exact 7-instruction symbolic x86-64 sequence
emitted by `rustc 1.99.1 -C opt-level=3` (`fixture_objdump.txt`):
  0. `leaq (%rsi,%rdi), %rax`
  1. `xorl %ecx, %ecx`
  2. `cmpq $0x3e9, %rsi`
  3. `cmovaeq %rcx, %rax`
  4. `cmpq $0x3e9, %rdi`
  5. `cmovaeq %rcx, %rax`
  6. `retq`
-/

/-- Architectural 64-bit general-purpose registers used in the System V AMD64
calling convention and callee-saved preservation contract. -/
inductive Reg64 where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

/-- Symbolic x86-64 instructions emitted for `add_bounded` and `alloc_passthrough`. -/
inductive X86Inst where
  | leaAdd (dst src1 src2 : Reg64)      -- `leaq (%src1, %src2), %dst` (does not touch flags)
  | xorZero (dst : Reg64)               -- `xorl %dst32, %dst32` (`dst := 0, CF := false`)
  | cmpImm (src : Reg64) (imm : BitVec 64) -- `cmpq $imm, %src` (`CF := src <u imm`)
  | cmovae (dst src : Reg64)            -- `cmovaeq %src, %dst` (`if !CF then dst := src`)
  | movReg (dst src : Reg64)            -- `movq %src, %dst`
  | retq                                -- `retq` (`rip := mem64[rsp]; rsp := rsp + 8`)
  deriving DecidableEq, Repr

/-- Exact 7-instruction x86-64 assembly program for `add_bounded`. -/
def addBoundedAsm : List X86Inst := [
  .leaAdd .rax .rsi .rdi,
  .xorZero .rcx,
  .cmpImm .rsi 1001#64,
  .cmovae .rax .rcx,
  .cmpImm .rdi 1001#64,
  .cmovae .rax .rcx,
  .retq
]

/-- Register + Carry-Flag file for symbolic assembly evaluation. -/
structure AsmRegState where
  regs : Reg64 → BitVec 64
  cf : Bool

def AsmRegState.setReg (st : AsmRegState) (r : Reg64) (v : BitVec 64) : AsmRegState :=
  { st with regs := fun r' => if r' = r then v else st.regs r' }

/-- Execute one non-control-flow instruction over `AsmRegState`. -/
def stepAsmInst (st : AsmRegState) : X86Inst → AsmRegState
  | .leaAdd dst s1 s2 => st.setReg dst (st.regs s1 + st.regs s2)
  | .xorZero dst => { (st.setReg dst 0#64) with cf := false }
  | .cmpImm src imm => { st with cf := st.regs src |>.ult imm }
  | .cmovae dst src => if !st.cf then st.setReg dst (st.regs src) else st
  | .movReg dst src => st.setReg dst (st.regs src)
  | .retq => st

/-- Execute the 6 body instructions of `addBoundedAsm` prior to `retq`. -/
def runAddBoundedBodyAsm (st : AsmRegState) : AsmRegState :=
  let st1 := stepAsmInst st (.leaAdd .rax .rsi .rdi)
  let st2 := stepAsmInst st1 (.xorZero .rcx)
  let st3 := stepAsmInst st2 (.cmpImm .rsi 1001#64)
  let st4 := stepAsmInst st3 (.cmovae .rax .rcx)
  let st5 := stepAsmInst st4 (.cmpImm .rdi 1001#64)
  stepAsmInst st5 (.cmovae .rax .rcx)

/-- Link 3 Lowering Theorem: executing `runAddBoundedBodyAsm` with System V
inputs `rdi = x` and `rsi = y` places the exact `evalSsaPostO3 x y` result into
`rax` while leaving `rsp` and all 6 System V callee-saved registers (`rbx`,
`rbp`, `r12`..`r15`) unchanged. -/
theorem link3_abi_lowering_sound (st : AsmRegState) :
    let st' := runAddBoundedBodyAsm st
    evalSsaPostO3 (st.regs .rdi) (st.regs .rsi) = .returned (st'.regs .rax) ∧
    st'.regs .rsp = st.regs .rsp ∧
    st'.regs .rbx = st.regs .rbx ∧
    st'.regs .rbp = st.regs .rbp ∧
    st'.regs .r12 = st.regs .r12 ∧
    st'.regs .r13 = st.regs .r13 ∧
    st'.regs .r14 = st.regs .r14 ∧
    st'.regs .r15 = st.regs .r15 := by
  dsimp only [runAddBoundedBodyAsm, stepAsmInst, AsmRegState.setReg, evalSsaPostO3]
  cases h_rsi : BitVec.ult (st.regs .rsi) 1001#64 <;>
  cases h_rdi : BitVec.ult (st.regs .rdi) 1001#64 <;>
  simp [h_rsi, h_rdi]

end S16Chain
