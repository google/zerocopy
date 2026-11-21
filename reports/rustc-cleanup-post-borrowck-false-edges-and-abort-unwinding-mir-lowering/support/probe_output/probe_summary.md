# Probe Summary: CleanupPostBorrowck, PlaceMention, and AbortUnwindingCalls

- Toolchain: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)
- Miri: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`

## CleanupPostBorrowck & RemovePlaceMention Counts (Unwind vs `-Zmir-preserve-ub=yes`)

| Function | Before `FakeRead` | Before `FakeBorrow` | Before `Ascribe` | Before `FalseEdge`/`Unwind` | After `CleanupPostBorrowck` Analysis Items | `PlaceMention` Default RT | `PlaceMention` `-Zmir-preserve-ub` |
| :-- | --: | --: | --: | --: | --: | --: | --: |
| `specimen_match_guard` | 5 | 2 | 0 | 3 | 0 | 0 | 3 |
| `specimen_ascribe_and_ptr_coercions` | 8 | 0 | 8 | 0 | 0 | 0 | 1 |
| `specimen_place_mention_only` | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| `specimen_wildcard_match_place_mention` | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| `specimen_loop_false_unwind` | 0 | 0 | 0 | 1 | 0 | 0 | 0 |
| `specimen_nested_index_fake_borrow` | 2 | 2 | 0 | 0 | 0 | 0 | 0 |

## AbortUnwindingCalls Matrix (`-C panic=unwind` vs `-C panic=abort`)

| Caller | Strategy | Cleanup BBs Before -> After | `Continue` Before -> After | `Unreachable` Edges After | `Terminate(Abi)` Edges / Terminators After |
| :-- | :-- | --: | --: | --: | :-- |
| `caller_rust_calls_rust_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 0 |
| `caller_rust_calls_rust_no_drop` | `unwind` | 0 -> 0 | 1 -> 1 | 0 | 0 / 0 |
| `caller_extern_c_calls_rust_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 1 |
| `caller_extern_c_calls_rust_no_drop` | `unwind` | 0 -> 0 | 1 -> 0 | 0 | 1 / 0 |
| `caller_extern_c_calls_foreign_c_unwind_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 1 |
| `caller_extern_c_calls_foreign_c_unwind_no_drop` | `unwind` | 0 -> 0 | 1 -> 0 | 0 | 1 / 0 |
| `caller_extern_c_unwind_calls_foreign_c_unwind_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 0 |
| `caller_extern_c_calls_foreign_c_nounwind_with_drop` | `unwind` | 2 -> 1 | 0 -> 0 | 1 | 0 / 1 |
| `caller_rust_calls_fnptr_c_unwind_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 0 |
| `caller_rust_calls_fnptr_c_unwind_no_drop` | `unwind` | 0 -> 0 | 1 -> 1 | 0 | 0 / 0 |
| `caller_rust_calls_rust_defined_c_unwind_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 0 |
| `caller_rust_inline_asm_may_unwind_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 0 |
| `caller_rust_assert_overflow_with_drop` | `unwind` | 2 -> 2 | 0 -> 0 | 0 | 0 / 0 |
| `caller_rust_calls_rust_with_drop` | `abort` | 2 -> 0 | 0 -> 0 | 2 | 0 / 0 |
| `caller_rust_calls_rust_no_drop` | `abort` | 1 -> 0 | 0 -> 0 | 1 | 0 / 0 |
| `caller_extern_c_calls_rust_with_drop` | `abort` | 2 -> 0 | 0 -> 0 | 2 | 0 / 0 |
| `caller_extern_c_calls_rust_no_drop` | `abort` | 1 -> 0 | 0 -> 0 | 1 | 0 / 0 |
| `caller_extern_c_calls_foreign_c_unwind_with_drop` | `abort` | 2 -> 2 | 0 -> 0 | 1 | 0 / 1 |
| `caller_extern_c_calls_foreign_c_unwind_no_drop` | `abort` | 1 -> 1 | 0 -> 0 | 0 | 0 / 1 |
| `caller_extern_c_unwind_calls_foreign_c_unwind_with_drop` | `abort` | 2 -> 2 | 0 -> 0 | 1 | 0 / 1 |
| `caller_extern_c_calls_foreign_c_nounwind_with_drop` | `abort` | 2 -> 0 | 0 -> 0 | 2 | 0 / 0 |
| `caller_rust_calls_fnptr_c_unwind_with_drop` | `abort` | 2 -> 2 | 0 -> 0 | 1 | 0 / 1 |
| `caller_rust_calls_fnptr_c_unwind_no_drop` | `abort` | 1 -> 1 | 0 -> 0 | 0 | 0 / 1 |
| `caller_rust_calls_rust_defined_c_unwind_with_drop` | `abort` | 2 -> 0 | 0 -> 0 | 2 | 0 / 0 |
| `caller_rust_inline_asm_may_unwind_with_drop` | `abort` | 2 -> 2 | 0 -> 0 | 1 | 0 / 1 |
| `caller_rust_assert_overflow_with_drop` | `abort` | 2 -> 0 | 0 -> 0 | 2 | 0 / 0 |

## Miri, Borrowck, and Native Abort Checks

Total checks: 21; Passed: 21; Failed: 0.
- `PASS` `cleanup::match_guard_erases_all_fakeread_fakeborrow_falseedge` (before=(fr=5,fb=2,fe=3), after=(fr=0,fb=0,fe=0,nop=7))
- `PASS` `cleanup::match_guard_preserves_place_mention_across_postcleanup` (place_mention=3 -> 3 -> 3)
- `PASS` `cleanup::ascribe_and_ptr_coercions_lowered_to_nop_and_ptr_to_ptr` (ascribe=8->0, arr2ptr=1->0, mut2const=1->0)
- `PASS` `cleanup::loop_false_unwind_removed` (false_unwind=1->0)
- `PASS` `cleanup::nested_index_fake_borrow_for_index_erased` (before={'ForIndex': 2}, after_fb=0)
- `PASS` `cleanup::coverage_virtual_counter_preserved` (virtual_counters=10->10)
- `PASS` `runtime_cleanup::remove_place_mention_vs_mir_preserve_ub` (default=1->0, mir_preserve_ub=1)
- `PASS` `abort_unwinding::unwind_extern_c_with_drop_preserves_cleanup_and_terminates` (cleanup_bbs=2->2, term_abi=1)
- `PASS` `abort_unwinding::unwind_extern_c_no_drop_continue_to_terminate_abi` (before_cont=1, after_term_abi_edge=1)
- `PASS` `abort_unwinding::unwind_extern_c_calling_nounwind_c_marks_call_unreachable_and_drops_dead_cleanup` (cleanup_bbs=2->1, unreach_edge=1)
- `PASS` `abort_unwinding::panic_abort_rust_call_with_drop_removes_all_cleanup_blocks` (cleanup_bbs=2->0, unreach_edges=2)
- `PASS` `abort_unwinding::panic_abort_rust_defined_c_unwind_fndef_cannot_unwind` (cleanup_bbs=2->0)
- `PASS` `abort_unwinding::panic_abort_fnptr_c_unwind_retains_cleanup_and_terminates` (cleanup_bbs=2, term_abi=1)
- `PASS` `abort_unwinding::panic_abort_noop_pad_not_stripped_before_auc` (cleanup_bbs_after_auc=1, runtime_post_cleanup=1)
- `PASS` `abort_unwinding::panic_abort_inline_asm_may_unwind_retains_cleanup_while_assert_unreachable` (asm_bbs=2, assert_bbs=0)
- `PASS` `custom_mir::extern_c_unwind_continue_lowered_to_terminate_abi` (verified on both panic=unwind and panic=abort)
- `PASS` `miri::place_mention_and_wildcard_match_ignore_invalid_bool_value` (let_named_err=error: Undefined Behavior: constructing invalid value of type bool: encountered 0x02, but expected a boolean)
- `PASS` `miri::place_mention_still_evaluates_pointer_local_chain` (dangling_ptr_rc=0, double_ptr_err=error: Undefined Behavior: reading memory at alloc19[0x0..0x8], but memory is uninitialized at [0x0..0x8], and this operation requires initialized memory)
- `PASS` `miri::guard_raw_ptr_mutation_bypasses_erased_fake_borrow_and_triggers_ub` (guard_err=error: Undefined Behavior: interpreting an invalid 8-bit value as a bool: 0x02, void_err=error: Undefined Behavior: entering unreachable code)
- `PASS` `borrowck::fake_borrow_and_fake_read_reject_safe_equivalents` (guard=error[E0510]: cannot assign `x` in match guard, empty=error[E0381]: used binding `x` isn't initialized)
- `PASS` `native::extern_c_runs_local_destructor_before_abi_abort` (run_rc=-6, drop=True, msg=True)
