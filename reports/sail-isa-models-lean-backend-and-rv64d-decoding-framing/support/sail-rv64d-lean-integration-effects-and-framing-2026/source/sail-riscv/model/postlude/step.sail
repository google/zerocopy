// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// The emulator fetch-execute-interrupt dispatch loop.

register hart_state : HartState = HART_ACTIVE()

private union Step = {
  Step_Pending_Interrupt  : (InterruptType, Privilege),
  Step_Pending_Trigger    : (Trig_Action, trigger_index, xlenbits),
  Step_Ext_Fetch_Failure  : ext_fetch_addr_error,
  Step_Fetch_Failure      : ExceptionContext,
  Step_Execute            : (ExecutionResult, instr_info),
  Step_Waiting            : WaitReason,
}

private function run_hart_waiting(_step_no : nat, wr: WaitReason, instr_info : instr_info, exit_wait : bool) -> Step = {
  // successfully interrupted waits
  if shouldWakeForInterrupt() then {
    if get_config_print_instr()
    then print_log("interrupt exit from " ^ wait_name(wr) ^ " state at PC " ^ bits_str(PC));

    // The waiting instruction retires successfully.  The
    // pending interrupts will be handled in the next step.
    hart_state = HART_ACTIVE();
    return Step_Execute(Retire_Success(), instr_info)
  };

  match (wr, valid_reservation(), exit_wait) {
    (WAIT_WRS_STO, false, _) => {
      if get_config_print_instr()
      then print_log("reservation invalid exit from " ^ wait_name(WAIT_WRS_STO) ^ " state at PC " ^ bits_str(PC));

      hart_state = HART_ACTIVE();
      Step_Execute(Retire_Success(), instr_info)
    },
    (WAIT_WRS_NTO, false, _) => {
      if get_config_print_instr()
      then print_log("reservation invalid exit from " ^ wait_name(WAIT_WRS_NTO) ^ " state at PC " ^ bits_str(PC));

      hart_state = HART_ACTIVE();
      Step_Execute(Retire_Success(), instr_info)
    },
    // Transition out of waiting states as instructed.
    (WAIT_WFI, _, true) => {
      if get_config_print_instr()
      then print_log("forced exit from " ^ wait_name(WAIT_WFI) ^ " state at PC " ^ bits_str(PC));

      hart_state = HART_ACTIVE();
      // "When TW=1, then if WFI is executed in any
      // less-privileged mode, and it does not complete within an
      // implementation-specific, bounded time limit, the WFI
      // instruction causes an illegal-instruction exception."
      // "When S-mode is implemented, then executing WFI in U-mode
      // causes an illegal-instruction exception, regardless of the
      // value of the TW bit, unless the instruction completes within
      // an implementation-specific, bounded time limit."

      // For VS-mode, VTW is checked instead since a set TW was already
      // caught in execute as an immediate illegal instruction.
      match cur_privilege {
        Machine           => Step_Execute(Retire_Success(), instr_info),
        User              => if   mstatus[TW] == 0b1 | currentlyEnabled(Ext_S)
                             then Step_Execute(Illegal_Instruction(), instr_info)
                             else Step_Execute(Retire_Success(), instr_info),
        VirtualSupervisor => if   hstatus[VTW] == 0b1
                             then Step_Execute(Virtual_Instruction(), instr_info)
                             else Step_Execute(Retire_Success(), instr_info),
        _                 => if   mstatus[TW] == 0b1
                             then Step_Execute(Illegal_Instruction(), instr_info)
                             else Step_Execute(Retire_Success(), instr_info),
      }
    },
    (WAIT_WRS_STO, _, true) => {
      if get_config_print_instr()
      then print_log("timed-out exit from " ^ wait_name(WAIT_WRS_STO) ^ " state at PC " ^ bits_str(PC));

      hart_state = HART_ACTIVE();
      Step_Execute(Retire_Success(), instr_info)
    },
    (WAIT_WRS_NTO, _, true) => {
      if get_config_print_instr()
      then print_log("timed-out exit from " ^ wait_name(WAIT_WRS_NTO) ^ " state at PC " ^ bits_str(PC));

      hart_state = HART_ACTIVE();
      // "When the TW bit in mstatus is set and WRS.NTO is executed in any
      // privilege mode other than M mode, and it does not complete within an
      // implementation-specific bounded time limit, the WRS.NTO instruction
      // will cause an illegal-instruction exception."
      // "When executing in VS or VU mode, if the VTW bit is set in hstatus,
      // the TW bit in mstatus is clear, and the WRS.NTO does not complete
      // within an implementation-specific bounded time limit, the WRS.NTO
      // instruction will cause a virtual-instruction exception."
      if      cur_privilege == Machine then Step_Execute(Retire_Success(), instr_info)
      else if mstatus[TW] == 0b1       then Step_Execute(Illegal_Instruction(), instr_info)
      else if inVirtualPrivilege() & hstatus[VTW] == 0b1
                                       then Step_Execute(Virtual_Instruction(), instr_info)
      else Step_Execute(Retire_Success(), instr_info)
    },
    // remain waiting
    (_, _, false) => {
      if get_config_print_instr()
      then print_log("remaining in " ^ wait_name(wr) ^ " state at PC " ^ bits_str(PC));
      Step_Waiting(wr)
    }
  }
}

private function run_hart_active(step_no: nat) -> Step = {
  // The Sdtrig extension does not define the priority of triggers
  // with respect to pending interrupts. See however:
  //   https://github.com/riscv/riscv-debug-spec/pull/802
  // and the related issue:
  //   https://github.com/riscv/riscv-debug-spec/issues/796
  //
  // For now, the implementation follows #802 by prioritizing the
  // itrigger, etrigger and icount triggers above asynchronous
  // interrupts.  When mcontrol6 triggers are implemented, their
  // `after` versions should also be handled here.
  match find_highest_priority_pending_trigger(cur_privilege) {
    Some(action, idx, breakpoint_tval) => return Step_Pending_Trigger(action, idx, breakpoint_tval),
    None() => (),
  };

  match dispatchInterrupt(cur_privilege) {
    Some(intr, priv) => return Step_Pending_Interrupt(intr, priv),
    None() => (),
  };

  // `icount` triggers match based on the privilege used for fetching,
  // but the match is performed after the instruction retires, by which time
  // the privilege might have changed (e.g. the xRET instructions).
  let fetch_privilege = cur_privilege;
  // Similarly, compute `icount` trigger reentrancy at fetch time,
  // before xRET restores MIE, SIE or tcontrol.mte.
  let fetch_trigger_reentrance = prevent_reentrance(TA_Breakpoint, fetch_privilege);

  match ext_fetch_hook(fetch()) {
    // extension error
    F_Ext_Error(e)   => Step_Ext_Fetch_Failure(e),
    // standard error
    F_Error(e) => Step_Fetch_Failure(e),
    // non-error cases:
    F_RVC(h) => {
      sail_instr_announce(h);
      fetch_callback(h);
      let instbits : instbits = zero_extend(h);
      let fetched_instruction = ext_decode_compressed(h);
      if   get_config_print_instr()
      then {
        print_log_instr("[" ^ dec_str(step_no) ^ "] [" ^ to_str(cur_privilege) ^ "]: " ^ bits_str(PC) ^ " (" ^ bits_str(h) ^ ") " ^ to_str(fetched_instruction), zero_extend(PC));
      };
      // When ELP is set to LP_EXPECTED, the next instruction needs to be
      // the non-RVC `LPAD` instruction.
      if is_landing_pad_expected() then {
        let r = trap(make_landing_pad_exception());
        let executed_instruction : option(instruction) = None();
        let instr_info = struct instr_info { fetch_privilege, fetch_trigger_reentrance, instbits, fetched_instruction, executed_instruction, compressed = true };
        Step_Execute(r, instr_info)
      }
      // check for RVC once here instead of every RVC execute clause.
      else if currentlyEnabled(Ext_Zca) then {
        nextPC = PC + 2;
        let (executed_instruction, result) : (option(instruction), ExecutionResult) = match execute(fetched_instruction) {
          ExecuteAs(other_inst) => (Some(other_inst), execute(other_inst)),
          result => (Some(fetched_instruction), result),
        };
        let instr_info = struct instr_info { fetch_privilege, fetch_trigger_reentrance, fetched_instruction, executed_instruction, instbits, compressed = true };
        Step_Execute(result, instr_info)
      } else {
        let executed_instruction : option(instruction) = None();
        let instr_info = struct instr_info { fetch_privilege, fetch_trigger_reentrance, fetched_instruction, executed_instruction, instbits, compressed = true };
        Step_Execute(Illegal_Instruction(), instr_info)
      }
    },
    F_Base(w) => {
      sail_instr_announce(w);
      fetch_callback(w);
      let instbits : instbits = zero_extend(w);
      let fetched_instruction = ext_decode(w);
      if   get_config_print_instr()
      then {
        print_log_instr("[" ^ dec_str(step_no) ^ "] [" ^ to_str(cur_privilege) ^ "]: " ^ bits_str(PC) ^ " (" ^ bits_str(w) ^ ") " ^ to_str(fetched_instruction), zero_extend(PC));
      };
      // When ELP is set to LP_EXPECTED, if the next instruction in
      // the instruction stream is not LPAD, then a software check
      // exception with a landing pad fault code is thrown.
      if is_landing_pad_expected() & not(is_lpad_instruction(fetched_instruction)) then {
        let r = trap(make_landing_pad_exception());
        let executed_instruction : option(instruction) = None();
        let instr_info = struct instr_info { fetch_privilege, fetch_trigger_reentrance, fetched_instruction, executed_instruction, instbits, compressed = false };
        Step_Execute(r, instr_info)
      } else {
        nextPC = PC + 4;
        let (executed_instruction, result) : (option(instruction), ExecutionResult) = match execute(fetched_instruction) {
          ExecuteAs(other_inst) => (Some(other_inst), execute(other_inst)),
          result => (Some(fetched_instruction), result),
        };
        let instr_info = struct instr_info { fetch_privilege, fetch_trigger_reentrance, fetched_instruction, executed_instruction, instbits, compressed = false };
        Step_Execute(result, instr_info)
      }
    }
  }
}

private function wait_is_nop(wr : WaitReason) -> bool =
  match wr {
    WAIT_WFI     => config platform.wfi_is_nop,
    WAIT_WRS_STO => config extensions.Zawrs.sto.is_nop,
    WAIT_WRS_NTO => config extensions.Zawrs.nto.is_nop,
  }

// The `try_step` function is the main internal driver of the Sail
// model. It performs the fetch-decode-execute for an instruction. It
// is also the primary interface to the non-Sail execution harness.
//
// A "step" is a full execution of an instruction, resulting either
// in its retirement or a trap. WFI and WRS instructions can cause
// the model to wait (hart_state is HART_WAITING), in which case
// a step has not happened and `try_step()` returns true. Otherwise
// it returns false. Equivalently, it returns whether the model is now
// in a waiting state (HART_WAITING).
//
// * step_no: the current step number; this is maintained by by the
//            non-Sail harness and is incremented when `try_step()`
//            returns true.
// * exit_wait: if true, and the model is waiting (HART_WAITING)
//              then it will wake up (switch to HART_ACTIVE) and
//              complete the WFI/WRS instruction, either successfully
//              retiring it or causing an illegal instruction
//              exception depending on mstatus[TW]. `exit_wait`
//              only affects the behaviour if the model is already
//              waiting from a previous WFI/WRS. It doesn't affect
//              WFI/WRS instructions executed in the same call of
//              `try_step()` (but see `wait_is_nop()`).
//
function try_step(step_no : nat, exit_wait : bool) -> bool = {
  // for step extensions
  ext_pre_step_hook();

  // Update the `mip` for any pending interrupts.
  update_mip();

  // This records whether or not minstret should be incremented when
  // the instruction is retired. Since retirement occurs before CSR
  // writes we initialise it based on mcountinhibit here, before it is
  // potentially changed. This is also set to false if minstret is
  // written.  See the note near the minstret declaration for more
  // information.
  minstret_increment = should_inc_minstret(cur_privilege);

  let step_val : Step = match hart_state {
      HART_WAITING(wr, instr_info) => run_hart_waiting(step_no, wr, instr_info, exit_wait),
      HART_ACTIVE()                => run_hart_active(step_no),
    };

  match step_val {
    Step_Pending_Trigger(action, _, trigger_tval) => {
      match action {
        TA_Breakpoint =>
          handle_exception(exception_context(E_Breakpoint(Brk_Hardware), trigger_tval)),
        _ =>
          internal_error(__FILE__, __LINE__, "Trigger action " ^ trigger_action_name(action) ^ " not supported."),
      }
    },
    Step_Pending_Interrupt(intr, priv) => {
      if   get_config_print_instr()
      then print_bits("Handling interrupt: ", interruptType_bits(intr));
      handle_interrupt(intr, priv)
    },
    Step_Ext_Fetch_Failure(e) => ext_handle_fetch_check_error(e),
    Step_Fetch_Failure(e) => handle_exception(e),
    Step_Waiting(_) => assert(hart_is_waiting(hart_state), "cannot be Waiting in a non-Wait state"),
    Step_Execute(Retire_Success(), instr_info) => {
      assert(hart_is_active(hart_state));
      match_icount_triggers(instr_info.fetch_privilege, instr_info.fetch_trigger_reentrance)
    },
    // We only support one level of ExecuteAs redirection, primarily intended
    // for compressed instructions (though it can be used elsewhere). If there
    // is more than one ExecuteAs indirection we'll get to here. This isn't supported.
    Step_Execute(ExecuteAs(_), _) => internal_error(__FILE__, __LINE__, "Multiple chained ExecuteAs (only one redirection is supported)."),
    // standard errors
    Step_Execute(Trap(priv, ctx, pc), instr_info) => {
      let ctx = transform_exception_context(ctx, instr_info);
      set_next_pc(exception_handler(priv, ctx, pc))
    },
    Step_Execute(Illegal_Instruction(), instr_info) =>
      handle_exception(make_instr_exception_context(E_Illegal_Instr(), zero_extend(instr_info.instbits))),
    Step_Execute(Virtual_Instruction(), instr_info) =>
      handle_exception(make_instr_exception_context(E_Virtual_Instr(), zero_extend(instr_info.instbits))),
    Step_Execute(Enter_Wait(wr), instr_info) => {
      if wait_is_nop(wr) then {
        // This is the same as the RETIRE_OK case.
        assert(hart_is_active(hart_state));
        match_icount_triggers(instr_info.fetch_privilege, instr_info.fetch_trigger_reentrance);
      } else {
        // Transition into the wait state.
        if   get_config_print_instr()
        then print_log("entering " ^ wait_name(wr) ^ " state at PC " ^ bits_str(PC));

        hart_state = HART_WAITING(wr, instr_info);
      }
    },
    // errors from extensions
    Step_Execute(Ext_CSR_Check_Failure(), _) => ext_check_CSR_fail(),
    Step_Execute(Ext_ControlAddr_Check_Failure(e), _) => ext_handle_control_check_error(e),
    Step_Execute(Ext_DataAddr_Check_Failure(e), _) => ext_handle_data_check_error(e),
    Step_Execute(Ext_XRET_Priv_Failure(), _) => ext_fail_xret_priv(),
  };

  match hart_state {
    HART_WAITING(_) => true,
    HART_ACTIVE() => {
      tick_pc();

      let retired : bool = match step_val {
        Step_Execute(Retire_Success(), _) => true,
        // WFI, WRS.{STO, NTO} retire immediately if the model is configured
        // to treat them as a nop.  Otherwise they always wait for at least
        // one call of `try_step()`.
        Step_Execute(Enter_Wait(wr), _) if wait_is_nop(wr) => true,
        _ => false,
      };

      // Increment minstret if we retired an instruction and the
      // update wasn't suppressed by writing to it explicitly or
      // mcountinhibit[IR] or minstretcfg.
      if retired & minstret_increment then minstret = minstret + 1;

      // Dispatch any events.
      dispatch_events();
      clear_written_event_index();

      // Update any triggers that were written.
      update_triggers();

      // Record the next PC for RVFI.
      // TODO: Remove this and implement it in C.
      if get_config_rvfi() then {
        rvfi_pc_data[rvfi_pc_wdata] = zero_extend(get_arch_pc())
      };

      // For step extensions
      ext_post_step_hook();

      if retired then instret_callback();

      // Return that we have stepped and are not waiting.
      false
    }
  }
}

function loop () : unit -> nat = {
  var i : nat = 0;
  var step_no : nat = 0;
  while not(htif_done) do {
    // This standalone loop always exits immediately out of waiting
    // states.
    let stepped = try_step(step_no, true);
    if stepped then {
      step_no = step_no + 1;
      if get_config_print_instr() then {
        print_step()
      };
      sail_end_cycle()
    };

    if not(htif_done) then {
      // update time
      i = i + 1;
      if i == plat_insns_per_tick then {
        tick_clock();
        i = 0;
      }
    }
  };

  let exit_val = unsigned(htif_exit_code);
  if exit_val == 0
    then print_endline("SUCCESS")
    else print_int("FAILURE: ", exit_val);
  exit_val
}

// Termination measures for loops are not supported by the Lean backend, so they
// should be guarded by this condition:
$iftarget rocq

// The top-level loop isn't terminating, but we put a limit so that it can still
// be included in the Coq output
termination_measure loop while 100

$endif
