// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// Callbacks for state-changing events

/// Called upon successful instruction fetch with the opcode.
/// If there is a fetch error then this is not called (but trap_callback() will be).
val fetch_callback = pure {cpp: "fetch_callback"} : forall 'n, 'n in {16, 32}. (bits('n)) -> unit
function fetch_callback(_) = ()

val mem_write_callback = pure {cpp: "mem_write_callback"} : forall 'n, 0 < 'n <= max_mem_access . (/* access type */ string, /* addr */ physaddrbits, /* width */ int('n), /* value */ bits(8 * 'n)) -> unit
function mem_write_callback(_) = ()

val mem_read_callback = pure {cpp: "mem_read_callback"} : forall 'n, 0 < 'n <= max_mem_access . (/* access type */ string, /* addr */ physaddrbits, /* width */ int('n), /* value */ bits(8 * 'n)) -> unit
function mem_read_callback(_) = ()

val mem_exception_callback = pure {cpp: "mem_exception_callback"} : (/* addr */ physaddrbits, /* exception code */ exc_code) -> unit
function mem_exception_callback(_) = ()

/// Called at the end of every step when PC is advanced to the next
/// instruction. This includes taken branches. It is not called when
/// the hart is waiting in WFI/WRS. The parameter is the new PC.
val pc_write_callback = pure {cpp: "pc_write_callback"} : (/* new_pc */ xlenbits) -> unit
function pc_write_callback(_) = ()

val xreg_full_write_callback = pure {cpp: "xreg_full_write_callback"} : (string, regidx, xlenbits) -> unit
function xreg_full_write_callback(_) = ()

val csr_full_write_callback = pure {cpp: "csr_full_write_callback"} : (string, csreg, xlenbits) -> unit
function csr_full_write_callback(_) = ()

val csr_full_read_callback = pure {cpp: "csr_full_read_callback"} : (string, csreg, xlenbits) -> unit
function csr_full_read_callback(_) = ()

/// Called when control flow is redirected from just executing the next instruction.
/// This includes:
///
///  * Unconditional jumps (jal, jalr)
///  * Traps
///  * Returning from trap handlers (mret, sret)
///  * Conditional branches that are taken (even if the target is the same instruction that
///    would have been executed if they were not taken).
///
/// The parameter is the new PC. pc_write_callback() will also be called after
/// this with the same parameter.
val redirect_callback = pure {cpp: "redirect_callback"} : (/* new_pc */ xlenbits) -> unit
function redirect_callback(_) = ()

/// Called on interrupts and exceptions. The exc_code does not include the 'interrupt' bit which is
/// in a separate bool.
val trap_callback = pure {cpp: "trap_callback"} : (/* is_interrupt */ bool, /* interrupt/exception cause */ exc_code) -> unit
function trap_callback(_) = ()

/// Called on xrets (mret <=> true, sret <=> false).
val xret_callback = pure {cpp: "xret_callback"} : (/* is_mret */ bool) -> unit
function xret_callback(_) = ()

/// Called when triggers match and fire, respectively, with the index of the relevant trigger.
val trigger_match_callback = pure {cpp: "trigger_match_callback"} : (nat) -> unit
function trigger_match_callback(_) = ()
val trigger_fire_callback = pure {cpp: "trigger_fire_callback"} : (nat) -> unit
function trigger_fire_callback(_) = ()

// Overloads for easier use of callbacks
function csr_name_write_callback(name : string, value : xlenbits) -> unit = {
  let csr = csr_name_map(name);
  csr_full_write_callback(name, csr, value);
}
function csr_id_write_callback(csr : csreg, value : xlenbits) -> unit = {
  let name = csr_name_map(csr);
  csr_full_write_callback(name, csr, value);
}
function csr_name_read_callback(name : string, value : xlenbits) -> unit = {
  let csr = csr_name_map(name);
  csr_full_read_callback(name, csr, value);
}
function csr_id_read_callback(csr : csreg, value : xlenbits) -> unit = {
  let name = csr_name_map(csr);
  csr_full_read_callback(name, csr, value);
}

overload csr_write_callback = {csr_name_write_callback, csr_id_write_callback, csr_full_write_callback}
overload csr_read_callback = {csr_name_read_callback, csr_id_read_callback, csr_full_read_callback}

function long_csr_write_callback(name : string, name_high : string, value : bits(64)) -> unit = {
  csr_write_callback(name, value[xlen - 1 .. 0]);
  if xlen == 32
  then csr_write_callback(name_high, value[63 .. 32]);
}
