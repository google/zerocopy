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
import ByteX86Gcc
import CompiledCObjImages
import UntrustedCObjHints

/-!
# `UntrustedCObjBlockDecodes`

Reflected basic-block and branch instruction decode witnesses (pure-`Bool`
`FlatInstr` reflection via `decodeSeqAt_of_check` and `decodeAt_of_check`, `0` `sorry`).
-/

namespace UntrustedCObjBlockDecodes

open ByteX86Gcc
open CompiledCObjImages
open UntrustedCObjHints

theorem fnv_o2_test : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400000#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem fnv_o2_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400003#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000033#64) 2 :=
  decodeAt_of_check rfl

def fnv_o2_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) 0xcbf29ce484222325#64, 0x40000f#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400012#64),
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rcx) 0x00000100000001b3#64, 0x40001c#64),
  (ByteX86Gcc.X64Instr.nop, 0x400020#64)
]

theorem fnv_o2_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 4 0x400005#64 = some fnv_o2_preSeq :=
  decodeSeqAt_of_check rfl rfl

def fnv_o2_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x400023#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x400027#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x40002a#64),
  (ByteX86Gcc.X64Instr.imul2 (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)), 0x40002e#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400031#64)
]

theorem fnv_o2_loop_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 5 0x400020#64 = some fnv_o2_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem fnv_o2_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400031#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffed#64) 2 :=
  decodeAt_of_check rfl

theorem fnv_o2_ret1 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400033#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem fnv_o2_mov0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400038#64) = .ok (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) 0xcbf29ce484222325#64) 10 :=
  decodeAt_of_check rfl

theorem fnv_o2_ret0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400042#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem fnv_o3_test : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400000#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem fnv_o3_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400003#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000033#64) 2 :=
  decodeAt_of_check rfl

def fnv_o3_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) 0xcbf29ce484222325#64, 0x40000f#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400012#64),
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rcx) 0x00000100000001b3#64, 0x40001c#64),
  (ByteX86Gcc.X64Instr.nop, 0x400020#64)
]

theorem fnv_o3_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 4 0x400005#64 = some fnv_o3_preSeq :=
  decodeSeqAt_of_check rfl rfl

def fnv_o3_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x400023#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x400027#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x40002a#64),
  (ByteX86Gcc.X64Instr.imul2 (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)), 0x40002e#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400031#64)
]

theorem fnv_o3_loop_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 5 0x400020#64 = some fnv_o3_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem fnv_o3_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400031#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffed#64) 2 :=
  decodeAt_of_check rfl

theorem fnv_o3_ret1 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400033#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem fnv_o3_mov0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400038#64) = .ok (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) 0xcbf29ce484222325#64) 10 :=
  decodeAt_of_check rfl

theorem fnv_o3_ret0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400042#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

def adler_o2_entrySeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx16 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rcx) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)), 0x400053#64),
  (ByteX86Gcc.X64Instr.shiftImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.ShiftOp.shr) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) 0x10#8, 0x400056#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi), 0x400059#64)
]

theorem adler_o2_entry_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 3 0x400050#64 = some adler_o2_entrySeq :=
  decodeSeqAt_of_check rfl rfl

theorem adler_o2_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400059#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000065#64) 2 :=
  decodeAt_of_check rfl

def adler_o2_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x40005e#64),
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.r8) 0x0000000080078071#64, 0x400064#64),
  (ByteX86Gcc.X64Instr.nop, 0x40006a#64),
  (ByteX86Gcc.X64Instr.nop, 0x400075#64),
  (ByteX86Gcc.X64Instr.nop, 0x400080#64)
]

theorem adler_o2_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 5 0x40005b#64 = some adler_o2_preSeq :=
  decodeSeqAt_of_check rfl rfl

def adler_o2_loopASeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rax) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x400083#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x400087#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)) (ByteX86Gcc.Reg.rax), 0x400089#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rcx), 0x40008c#64),
  (ByteX86Gcc.X64Instr.imul2 (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rcx) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.r8)), 0x400090#64),
  (ByteX86Gcc.X64Instr.shiftImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.ShiftOp.shr) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)) 0x2f#8, 0x400094#64),
  (ByteX86Gcc.X64Instr.imul3 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.r9) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)) 0x000000000000fff1#64, 0x40009b#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.sub) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.r9), 0x40009e#64)
]

theorem adler_o2_loopA_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 8 0x400080#64 = some adler_o2_loopASeq :=
  decodeSeqAt_of_check rfl rfl

def adler_o2_loopBSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) (ByteX86Gcc.Reg.rax), 0x4000a0#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)) (ByteX86Gcc.Reg.rax), 0x4000a2#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) (ByteX86Gcc.Reg.rdx), 0x4000a4#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x4000a7#64),
  (ByteX86Gcc.X64Instr.imul2 (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.r8)), 0x4000ab#64),
  (ByteX86Gcc.X64Instr.shiftImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.ShiftOp.shr) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) 0x2f#8, 0x4000af#64),
  (ByteX86Gcc.X64Instr.imul3 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.r9) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) 0x000000000000fff1#64, 0x4000b6#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.sub) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.r9), 0x4000b9#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) (ByteX86Gcc.Reg.rax), 0x4000bb#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x4000be#64)
]

theorem adler_o2_loopB_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 10 0x40009e#64 = some adler_o2_loopBSeq :=
  decodeSeqAt_of_check rfl rfl

theorem adler_o2_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000be#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffc0#64) 2 :=
  decodeAt_of_check rfl

def adler_o2_exitSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.shiftImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.ShiftOp.shl) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) 0x10#8, 0x4000c3#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x4000c5#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.or) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rcx), 0x4000c7#64)
]

theorem adler_o2_exit_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 3 0x4000c0#64 = some adler_o2_exitSeq :=
  decodeSeqAt_of_check rfl rfl

theorem adler_o2_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000c7#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem rol_o2_test : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000d0#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem rol_o2_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000d3#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000023#64) 2 :=
  decodeAt_of_check rfl

def rol_o2_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x4000d8#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax), 0x4000da#64),
  (ByteX86Gcc.X64Instr.nop, 0x4000e0#64)
]

theorem rol_o2_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 3 0x4000d5#64 = some rol_o2_preSeq :=
  decodeSeqAt_of_check rfl rfl

def rol_o2_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x4000e3#64),
  (ByteX86Gcc.X64Instr.shiftImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.ShiftOp.rol) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) 0x05#8, 0x4000e6#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x4000ea#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x4000ec#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) (ByteX86Gcc.Reg.rsi), 0x4000ef#64)
]

theorem rol_o2_loop_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 5 0x4000e0#64 = some rol_o2_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem rol_o2_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000ef#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffef#64) 2 :=
  decodeAt_of_check rfl

theorem rol_o2_ret1 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000f1#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem rol_o2_xor0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000f8#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax)) 2 :=
  decodeAt_of_check rfl

theorem rol_o2_ret0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x4000fa#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem ascii_o2_test : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400100#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem ascii_o2_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400103#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000034#64) 2 :=
  decodeAt_of_check rfl

def ascii_o2_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400108#64),
  (ByteX86Gcc.X64Instr.nop, 0x40010a#64),
  (ByteX86Gcc.X64Instr.nop, 0x400115#64),
  (ByteX86Gcc.X64Instr.nop, 0x400120#64)
]

theorem ascii_o2_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 4 0x400105#64 = some ascii_o2_preSeq :=
  decodeSeqAt_of_check rfl rfl

def ascii_o2_headSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rax) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x400123#64),
  (ByteX86Gcc.X64Instr.lea (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) { base := some (ByteX86Gcc.Reg.rax), index := none, disp := 0xffffffffffffffbf#64, ripRel := false }, 0x400126#64),
  (ByteX86Gcc.X64Instr.alu8Imm (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm8.reg8 (ByteX86Gcc.SubReg8.lo8 (ByteX86Gcc.Reg.rdx))) 0x19#8, 0x400129#64)
]

theorem ascii_o2_head_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 3 0x400120#64 = some ascii_o2_headSeq :=
  decodeSeqAt_of_check rfl rfl

theorem ascii_o2_ja : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400129#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.a) 0x0000000000000005#64) 2 :=
  decodeAt_of_check rfl

def ascii_o2_storeSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) 0x0000000000000020#64, 0x40012e#64),
  (ByteX86Gcc.X64Instr.mov8Store (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }) (ByteX86Gcc.SubReg8.lo8 (ByteX86Gcc.Reg.rax)), 0x400130#64)
]

theorem ascii_o2_store_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 2 0x40012b#64 = some ascii_o2_storeSeq :=
  decodeSeqAt_of_check rfl rfl

def ascii_o2_latchSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x400134#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) (ByteX86Gcc.Reg.rsi), 0x400137#64)
]

theorem ascii_o2_latch_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 2 0x400130#64 = some ascii_o2_latchSeq :=
  decodeSeqAt_of_check rfl rfl

theorem ascii_o2_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400137#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffe7#64) 2 :=
  decodeAt_of_check rfl

theorem ascii_o2_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400139#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem rol_o3_test : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x4000d0#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem rol_o3_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x4000d3#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000023#64) 2 :=
  decodeAt_of_check rfl

def rol_o3_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x4000d8#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax), 0x4000da#64),
  (ByteX86Gcc.X64Instr.nop, 0x4000e0#64)
]

theorem rol_o3_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 3 0x4000d5#64 = some rol_o3_preSeq :=
  decodeSeqAt_of_check rfl rfl

def rol_o3_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x4000e3#64),
  (ByteX86Gcc.X64Instr.shiftImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.ShiftOp.rol) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) 0x05#8, 0x4000e6#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x4000ea#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x4000ec#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) (ByteX86Gcc.Reg.rsi), 0x4000ef#64)
]

theorem rol_o3_loop_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 5 0x4000e0#64 = some rol_o3_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem rol_o3_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x4000ef#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffef#64) 2 :=
  decodeAt_of_check rfl

theorem rol_o3_ret1 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x4000f1#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem rol_o3_xor0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x4000f8#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax)) 2 :=
  decodeAt_of_check rfl

theorem rol_o3_ret0 : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x4000fa#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem ascii_o3_test : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400100#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem ascii_o3_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400103#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000034#64) 2 :=
  decodeAt_of_check rfl

def ascii_o3_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400108#64),
  (ByteX86Gcc.X64Instr.nop, 0x40010a#64),
  (ByteX86Gcc.X64Instr.nop, 0x400115#64),
  (ByteX86Gcc.X64Instr.nop, 0x400120#64)
]

theorem ascii_o3_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 4 0x400105#64 = some ascii_o3_preSeq :=
  decodeSeqAt_of_check rfl rfl

def ascii_o3_headSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rax) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x400123#64),
  (ByteX86Gcc.X64Instr.lea (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) { base := some (ByteX86Gcc.Reg.rax), index := none, disp := 0xffffffffffffffbf#64, ripRel := false }, 0x400126#64),
  (ByteX86Gcc.X64Instr.alu8Imm (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm8.reg8 (ByteX86Gcc.SubReg8.lo8 (ByteX86Gcc.Reg.rdx))) 0x19#8, 0x400129#64)
]

theorem ascii_o3_head_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 3 0x400120#64 = some ascii_o3_headSeq :=
  decodeSeqAt_of_check rfl rfl

theorem ascii_o3_ja : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400129#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.a) 0x0000000000000005#64) 2 :=
  decodeAt_of_check rfl

def ascii_o3_storeSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) 0x0000000000000020#64, 0x40012e#64),
  (ByteX86Gcc.X64Instr.mov8Store (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }) (ByteX86Gcc.SubReg8.lo8 (ByteX86Gcc.Reg.rax)), 0x400130#64)
]

theorem ascii_o3_store_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 2 0x40012b#64 = some ascii_o3_storeSeq :=
  decodeSeqAt_of_check rfl rfl

def ascii_o3_latchSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x400134#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) (ByteX86Gcc.Reg.rsi), 0x400137#64)
]

theorem ascii_o3_latch_dec : decodeSeqAt (objCodeMap cFfiKernelsO3Avx2Obj) 2 0x400130#64 = some ascii_o3_latchSeq :=
  decodeSeqAt_of_check rfl rfl

theorem ascii_o3_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400137#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffe7#64) 2 :=
  decodeAt_of_check rfl

theorem ascii_o3_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO3Avx2Obj) 0x400139#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

def xor_o2_entrySeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.r8)) (ByteX86Gcc.Reg.rsi), 0x400233#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdx), 0x400236#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) (ByteX86Gcc.Reg.rdx), 0x400239#64)
]

theorem xor_o2_entry_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 3 0x400230#64 = some xor_o2_entrySeq :=
  decodeSeqAt_of_check rfl rfl

theorem xor_o2_je : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400239#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000018#64) 2 :=
  decodeAt_of_check rfl

def xor_o2_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax), 0x40023d#64),
  (ByteX86Gcc.X64Instr.nop, 0x400240#64)
]

theorem xor_o2_pre_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 2 0x40023b#64 = some xor_o2_preSeq :=
  decodeSeqAt_of_check rfl rfl

def xor_o2_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.r8), index := some (ByteX86Gcc.Reg.rax, 0), disp := 0x0000000000000000#64, ripRel := false }), 0x400245#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) (ByteX86Gcc.Reg.rcx), 0x400247#64),
  (ByteX86Gcc.X64Instr.mov8Store (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := some (ByteX86Gcc.Reg.rax, 0), disp := 0x0000000000000000#64, ripRel := false }) (ByteX86Gcc.SubReg8.lo8 (ByteX86Gcc.Reg.rdx)), 0x40024a#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) 0x0000000000000001#64, 0x40024e#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rax), 0x400251#64)
]

theorem xor_o2_loop_dec : decodeSeqAt (objCodeMap cFfiKernelsO2Obj) 5 0x400240#64 = some xor_o2_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem xor_o2_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400251#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffed#64) 2 :=
  decodeAt_of_check rfl

theorem xor_o2_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiKernelsO2Obj) 0x400253#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

def bug1_entrySeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax), 0x400002#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi), 0x400004#64)
]

theorem bug1_entry_dec : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 2 0x400000#64 = some bug1_entrySeq :=
  decodeSeqAt_of_check rfl rfl

theorem bug1_jle : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400004#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.le) 0x0000000000000010#64) 2 :=
  decodeAt_of_check rfl

theorem bug1_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400016#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

theorem bug2_test : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400020#64) = .ok (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi)) 3 :=
  decodeAt_of_check rfl

theorem bug2_je : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400023#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x0000000000000033#64) 2 :=
  decodeAt_of_check rfl

def bug2_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) 0xcbf29ce484222325#64, 0x40002f#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400032#64),
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rcx) 0x00000100000001b3#64, 0x40003c#64),
  (ByteX86Gcc.X64Instr.nop, 0x400040#64)
]

theorem bug2_pre_dec : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 4 0x400025#64 = some bug2_preSeq :=
  decodeSeqAt_of_check rfl rfl

def bug2_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movsx8 (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := none, disp := 0x0000000000000000#64, ripRel := false }), 0x400044#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) 0x0000000000000001#64, 0x400048#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rdx), 0x40004b#64),
  (ByteX86Gcc.X64Instr.imul2 (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rax) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rcx)), 0x40004f#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdi), 0x400052#64)
]

theorem bug2_loop_dec : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 5 0x400040#64 = some bug2_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem bug2_jne : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400052#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ne) 0xffffffffffffffec#64) 2 :=
  decodeAt_of_check rfl

theorem bug2_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400054#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

def bug3_preSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.r8)) (ByteX86Gcc.Reg.rdi), 0x400073#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.rax), 0x400075#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdi)) (ByteX86Gcc.Reg.rsi), 0x400078#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rdx), 0x40007b#64),
  (ByteX86Gcc.X64Instr.nop, 0x400080#64)
]

theorem bug3_pre_dec : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 5 0x400070#64 = some bug3_preSeq :=
  decodeSeqAt_of_check rfl rfl

def bug3_loopSeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.movzx8 (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.Reg.rdx) (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.rdi), index := some (ByteX86Gcc.Reg.rax, 0), disp := 0x0000000000000000#64, ripRel := false }), 0x400084#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rdx)) (ByteX86Gcc.Reg.rcx), 0x400086#64),
  (ByteX86Gcc.X64Instr.mov8Store (ByteX86Gcc.X64Rm8.mem8 { base := some (ByteX86Gcc.Reg.r8), index := some (ByteX86Gcc.Reg.rax, 0), disp := 0x0000000000000000#64, ripRel := false }) (ByteX86Gcc.SubReg8.lo8 (ByteX86Gcc.Reg.rdx)), 0x40008a#64),
  (ByteX86Gcc.X64Instr.aluImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.add) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) 0x0000000000000001#64, 0x40008e#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.cmp) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rax), 0x400091#64)
]

theorem bug3_loop_dec : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 5 0x400080#64 = some bug3_loopSeq :=
  decodeSeqAt_of_check rfl rfl

theorem bug3_jae : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400091#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.ae) 0xffffffffffffffed#64) 2 :=
  decodeAt_of_check rfl

theorem bug3_ret : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x400093#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

def bug4_entrySeq : List (X64Instr × BitVec 64) := [
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s32) (ByteX86Gcc.AluOp.xor) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.r8)) (ByteX86Gcc.Reg.r8), 0x4000a3#64),
  (ByteX86Gcc.X64Instr.movImm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.Reg.rbx) 0xdeadbeefcafebabe#64, 0x4000ad#64),
  (ByteX86Gcc.X64Instr.unaryRm (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.UnaryOp.inc) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.r12)), 0x4000b0#64),
  (ByteX86Gcc.X64Instr.simdCmpeq (ByteX86Gcc.SimdMode.vex256) (ByteX86Gcc.VecElem.e32) 0 0 (ByteX86Gcc.X64XmmRm.reg 0), 0x4000b4#64),
  (ByteX86Gcc.X64Instr.movStore (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rax)) (ByteX86Gcc.Reg.r8), 0x4000b7#64),
  (ByteX86Gcc.X64Instr.aluRmReg (ByteX86Gcc.OpSize.s64) (ByteX86Gcc.AluOp.test) (ByteX86Gcc.X64Rm.reg (ByteX86Gcc.Reg.rsi)) (ByteX86Gcc.Reg.rsi), 0x4000ba#64)
]

theorem bug4_entry_dec : decodeSeqAt (objCodeMap cFfiBugsO2Obj) 6 0x4000a0#64 = some bug4_entrySeq :=
  decodeSeqAt_of_check rfl rfl

theorem bug4_je0 : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x4000ba#64) = .ok (ByteX86Gcc.X64Instr.jccRel (ByteX86Gcc.Cond.e) 0x00000000000000f0#64) 6 :=
  decodeAt_of_check rfl

theorem bug4_ret0 : decodeX64 (fetchWindow16 (objCodeMap cFfiBugsO2Obj) 0x4001b0#64) = .ok (ByteX86Gcc.X64Instr.ret64) 1 :=
  decodeAt_of_check rfl

end UntrustedCObjBlockDecodes
