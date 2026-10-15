// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// accessors for default architectural addresses, for use from within instructions


/*!
  Retrieves the architectural PC value. This is not necessarily the value
  found in the PC register as extensions may choose to override this function.
  The value in the PC register is the absolute virtual address of the instruction
  to fetch.
 */
function get_arch_pc() -> xlenbits = PC

function get_next_pc() -> xlenbits = nextPC

function set_next_pc(pc : xlenbits) -> unit = {
  sail_branch_announce(xlen, pc);
  nextPC = pc;
  redirect_callback(pc);
}

function tick_pc() -> unit = {
  PC = nextPC;
  pc_write_callback(PC);
}
