(* Upstream lines 1-83; other lines omitted. *)
(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail_riscv.sail_opsem.
Require Import isla.sail_riscv.tactics.
Require Import isla.automation.
Require Import isla.riscv64.riscv64.
From isla.instructions.riscv64_test Require Import instrs.
Require Import isla.examples.riscv64_test.

Lemma sim_instr_a0:
  sim_instr (Uncompressed (BV 32 0x00000513)) a0.
Proof.
  move => regs. unfold step_cpu, a0.
  red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve. all: sim_simpl_goal.
  - rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a4:
  sim_instr (Uncompressed (BV 32 0x00150513)) a4.
Proof.
  move => regs. unfold step_cpu, a4. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve. all: sim_simpl_goal.
  all: rewrite mword_to_bv_add_vec //.
Qed.

(* Upstream lines 190-225; other lines omitted. *)
  <[ (BV 64 0x0000000010300000) := Uncompressed (BV 32 0x00000513)]> $
  <[ (BV 64 0x0000000010300004) := Uncompressed (BV 32 0x00150513)]> $
  <[ (BV 64 0x0000000010300008) := Uncompressed (BV 32 0x00b13423)]> $
  <[ (BV 64 0x000000001030000c) := Uncompressed (BV 32 0x00813583)]> $
  <[ (BV 64 0x0000000010300010) := Uncompressed (BV 32 0x00b50463)]> $
  ∅.

Definition riscv_test_initial_sail_state (x2v : bv 64) (regs : regstate) : sail_state :=
  SAIL (Done tt) regs (riscv_test_state_global x2v).(seq_mem) riscv_test_sail_instrs false.

Lemma riscv_test_safe regs (satpv x10v x2v mstatus_bits x11v : bv 64):
  plat_enable_pmp () = false →
  plat_enable_misaligned_access () = false →
  mword_to_bv (plat_ram_base ()) = (BV 64 0x0000000080000000) →
  mword_to_bv (plat_ram_size ()) = (BV 64 0x0000000004000000) →
  mword_to_bv (plat_rom_base ()) = (BV 64 0x0000000000001000) →
  mword_to_bv (plat_rom_size ()) = (BV 64 0x0000000000000100) →
  mword_to_bv (plat_clint_base ()) = (BV 64 0x0000000002000000) →
  mword_to_bv (plat_clint_size ()) = (BV 64 0x00000000000c0000) →
  mword_to_bv (plat_htif_tohost ()) = (BV 64 0x0000000040001000) →
  Z.land (bv_unsigned mstatus_bits) 0x20000 = 0 →
  bv_unsigned x2v `mod` 8 = 0 →
  bv_unsigned x2v + 16 < 2 ^ 64 →
  0x0000000080000000 ≤ bv_unsigned x2v + 8 < 0x0000000080000000 + 0x0000000004000000 →
  PC regs = bv_to_mword (BV 64 0x0000000010300000) →
  x2 regs = bv_to_mword x2v →
  x10 regs = bv_to_mword x10v →
  x11 regs = bv_to_mword x11v →
  satp regs = bv_to_mword satpv →
  cur_privilege regs = Machine →
  misa regs = {| Misa_bits := bv_to_mword misa_bits |} →
  mstatus regs = {| Mstatus_bits := bv_to_mword mstatus_bits |} →
  safe sail_module (riscv_test_initial_sail_state x2v regs) ∧
    (∀ κs σ', steps sail_module (riscv_test_initial_sail_state x2v regs) κs σ' → riscv_test_spec x11v κs).
Proof.
  move => ?????????? ??? HPC Hx2 Hx10 Hx11 Hsatp Hcur_priv Hmisa Hmstatus.

