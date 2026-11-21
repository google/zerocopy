# Drop-elaboration probe summary

- compiler: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`)
- generated on: 2026-11-21
- checks: 39 passed, 0 failed

## panic_unwind (`support/specimens/drop_specimens.rs`)

Totals over 32 functions: flag locals 16; blocks 376 -> 540; cleanup blocks 108 -> 207; drop terminators 153 -> 127; flag tests 39; flag writes 64; styles {"conditional": 14, "dead": 67, "open": 18, "static": 54}.

| function | flags | blocks pre→post | cleanup pre→post | drops pre→post | flag tests | flag writes T/F | styles | blocks at runtime-post-cleanup |
| :-- | --: | :-- | :-- | :-- | --: | :-- | :-- | --: |
| `array_cond_move` | 1 | 17→30 | 5→13 | 8→7 | 3 | 1/3 | {"dead": 5, "open": 2, "static": 1} | 18 |
| `array_static_drop` | 0 | 10→10 | 3→3 | 5→3 | 0 | 0/0 | {"dead": 2, "static": 3} | 8 |
| `assign_overwrite` | 0 | 10→10 | 3→3 | 5→3 | 0 | 0/0 | {"dead": 2, "static": 3} | 9 |
| `assign_overwrite_old_dtor_panics` | 0 | 10→10 | 3→3 | 5→3 | 0 | 0/0 | {"dead": 2, "static": 3} | 9 |
| `box_cond_move` | 1 | 13→25 | 4→10 | 4→2 | 2 | 1/3 | {"dead": 2, "open": 2} | 16 |
| `cond_assign_overwrite` | 1 | 15→19 | 4→6 | 6→3 | 2 | 3/3 | {"conditional": 2, "dead": 3, "static": 1} | 15 |
| `cond_init` | 1 | 12→16 | 3→5 | 5→2 | 2 | 2/2 | {"conditional": 2, "dead": 3} | 11 |
| `cond_move` | 1 | 11→15 | 3→5 | 3→2 | 2 | 1/3 | {"conditional": 2, "dead": 1} | 12 |
| `cond_partial_move_nested` | 1 | 20→44 | 6→22 | 10→13 | 4 | 1/3 | {"dead": 6, "open": 2, "static": 2} | 23 |
| `cond_partial_move_struct` | 1 | 18→34 | 5→15 | 8→11 | 3 | 1/3 | {"dead": 4, "open": 2, "static": 2} | 23 |
| `cond_partial_move_tuple` | 1 | 15→28 | 4→12 | 6→7 | 3 | 1/3 | {"dead": 3, "open": 2, "static": 1} | 17 |
| `copy_type` | 0 | 2→2 | 0→0 | 0→0 | 0 | 0/0 | {} | 2 |
| `dead_drop` | 0 | 8→8 | 3→3 | 3→0 | 0 | 0/0 | {"dead": 3} | 5 |
| `double_panic` | 0 | 9→9 | 3→3 | 4→4 | 0 | 0/0 | {"static": 4} | 9 |
| `dtor_panics_normal_path` | 0 | 9→9 | 3→3 | 4→4 | 0 | 0/0 | {"static": 4} | 9 |
| `early_return` | 0 | 13→13 | 3→3 | 5→5 | 0 | 0/0 | {"static": 5} | 13 |
| `generic_cond_move` | 1 | 10→14 | 3→5 | 3→2 | 2 | 1/2 | {"conditional": 2, "dead": 1} | 11 |
| `generic_cond_move_copy` | 0 | 2→2 | 0→0 | 0→0 | 0 | 0/0 | {} | 2 |
| `generic_cond_move_loud` | 0 | 5→5 | 2→2 | 1→0 | 0 | 0/0 | {"dead": 1} | 4 |
| `loop_break_move` | 1 | 17→21 | 3→5 | 3→2 | 2 | 1/3 | {"conditional": 2, "dead": 1} | 18 |
| `manually_drop` | 0 | 6→6 | 2→2 | 1→0 | 0 | 0/0 | {"dead": 1} | 5 |
| `maybe_uninit` | 0 | 6→6 | 2→2 | 1→0 | 0 | 0/0 | {"dead": 1} | 5 |
| `nounwind_abi` | 0 | 7→7 | 2→2 | 2→2 | 0 | 0/0 | {"static": 2} | 7 |
| `open_ladder_in_cleanup` | 1 | 21→37 | 6→16 | 10→13 | 3 | 1/3 | {"dead": 4, "open": 2, "static": 4} | 26 |
| `open_ladder_normal_two_panics` | 1 | 18→34 | 5→15 | 8→11 | 3 | 1/3 | {"dead": 4, "open": 2, "static": 2} | 23 |
| `option_cond_move` | 2 | 16→35 | 4→17 | 6→4 | 4 | 2/5 | {"dead": 4, "open": 2} | 16 |
| `partial_move_tuple` | 0 | 12→19 | 4→8 | 6→4 | 0 | 0/0 | {"dead": 3, "open": 2, "static": 1} | 9 |
| `static_drop` | 0 | 6→6 | 2→2 | 2→2 | 0 | 0/0 | {"static": 2} | 6 |
| `static_glue_in_cleanup` | 0 | 16→16 | 5→5 | 9→6 | 0 | 0/0 | {"dead": 3, "static": 6} | 13 |
| `tuple_first_dtor_panics` | 0 | 13→13 | 4→4 | 7→4 | 0 | 0/0 | {"dead": 3, "static": 4} | 10 |
| `tuple_two_dtors_panic` | 0 | 13→13 | 4→4 | 7→4 | 0 | 0/0 | {"dead": 3, "static": 4} | 10 |
| `two_cond_moves` | 2 | 16→24 | 5→9 | 6→4 | 4 | 2/6 | {"conditional": 4, "dead": 2} | 18 |

| function | arg | stdout | exit | signal | panics | runtime markers |
| :-- | --: | :-- | --: | :-- | --: | :-- |
| `array_cond_move` | 0 | `effect join; drop arr1; drop arr0; main-returned` | 0 | None | 0 |  |
| `array_cond_move` | 1 | `consume arr0; drop arr0; effect join; drop arr1; main-returned` | 0 | None | 0 |  |
| `array_static_drop` | 0 | `effect body; drop arr0; drop arr1; main-returned` | 0 | None | 0 |  |
| `array_static_drop` | 1 | `effect body; drop arr0; drop arr1; main-returned` | 0 | None | 0 |  |
| `assign_overwrite` | 0 | `drop old; effect after-assign; drop new; main-returned` | 0 | None | 0 |  |
| `assign_overwrite` | 1 | `drop old` | 101 | None | 1 |  |
| `assign_overwrite_old_dtor_panics` | 0 | `drop old; drop new` | 101 | None | 1 |  |
| `assign_overwrite_old_dtor_panics` | 1 | `drop old; drop new` | 101 | None | 1 |  |
| `box_cond_move` | 0 | `effect join; drop boxed; main-returned` | 0 | None | 0 |  |
| `box_cond_move` | 1 | `consume boxed; drop boxed; effect join; main-returned` | 0 | None | 0 |  |
| `cond_assign_overwrite` | 0 | `drop old; effect after-assign; drop new; main-returned` | 0 | None | 0 |  |
| `cond_assign_overwrite` | 1 | `consume old; drop old; effect after-assign; drop new; main-returned` | 0 | None | 0 |  |
| `cond_init` | 0 | `effect join; main-returned` | 0 | None | 0 |  |
| `cond_init` | 1 | `effect join; drop x; main-returned` | 0 | None | 0 |  |
| `cond_move` | 0 | `effect join; drop x; main-returned` | 0 | None | 0 |  |
| `cond_move` | 1 | `consume x; drop x; effect join; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_nested` | 0 | `effect join; drop n00; drop n01; drop n1; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_nested` | 1 | `consume n01; drop n01; effect join; drop n00; drop n1; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_struct` | 0 | `effect join; drop s.a; drop s.b; drop s.c; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_struct` | 1 | `consume s.b; drop s.b; effect join; drop s.a; drop s.c; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_tuple` | 0 | `effect join; drop p0; drop p1; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_tuple` | 1 | `consume p0; drop p0; effect join; drop p1; main-returned` | 0 | None | 0 |  |
| `copy_type` | 0 | `effect body; main-returned` | 0 | None | 0 |  |
| `copy_type` | 1 | `effect body; main-returned` | 0 | None | 0 |  |
| `dead_drop` | 0 | `consume x; drop x; effect after; main-returned` | 0 | None | 0 |  |
| `dead_drop` | 1 | `consume x; drop x; effect after; main-returned` | 0 | None | 0 |  |
| `double_panic` | 0 | `drop a` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `double_panic` | 1 | `drop a` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `dtor_panics_normal_path` | 0 | `effect body; drop a; drop b` | 101 | None | 1 |  |
| `dtor_panics_normal_path` | 1 | `effect body; drop a; drop b` | 101 | None | 1 |  |
| `early_return` | 0 | `effect tail; drop b; drop a; main-returned` | 0 | None | 0 |  |
| `early_return` | 1 | `drop a; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_copy` | 0 | `effect join; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_copy` | 1 | `effect join; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_loud` | 0 | `effect join; drop g; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_loud` | 1 | `drop g; effect join; main-returned` | 0 | None | 0 |  |
| `loop_break_move` | 0 | `effect after-loop; drop x; main-returned` | 0 | None | 0 |  |
| `loop_break_move` | 1 | `consume x; drop x; effect after-loop; main-returned` | 0 | None | 0 |  |
| `manually_drop` | 0 | `effect body; main-returned` | 0 | None | 0 |  |
| `manually_drop` | 1 | `effect body; main-returned` | 0 | None | 0 |  |
| `maybe_uninit` | 0 | `effect body; main-returned` | 0 | None | 0 |  |
| `maybe_uninit` | 1 | `effect body; main-returned` | 0 | None | 0 |  |
| `nounwind_abi` | 0 | `effect body; drop g; main-returned` | 0 | None | 0 |  |
| `nounwind_abi` | 1 | `drop g` | None | SIGABRT | 2 | panic in a function that cannot unwind; thread caused non-unwinding panic. aborting. |
| `open_ladder_in_cleanup` | 0 | `drop t0` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `open_ladder_in_cleanup` | 1 | `consume t2; drop t2; drop t0` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `open_ladder_normal_two_panics` | 0 | `effect body; drop t0; drop t1` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `open_ladder_normal_two_panics` | 1 | `consume t2; drop t2; effect body; drop t0; drop t1` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `option_cond_move` | 0 | `effect join; drop o; main-returned` | 0 | None | 0 |  |
| `option_cond_move` | 1 | `consume o; drop o; effect join; main-returned` | 0 | None | 0 |  |
| `partial_move_tuple` | 0 | `consume p0; drop p0; effect after; drop p1; main-returned` | 0 | None | 0 |  |
| `partial_move_tuple` | 1 | `consume p0; drop p0; effect after; drop p1; main-returned` | 0 | None | 0 |  |
| `static_drop` | 0 | `effect body; drop x; main-returned` | 0 | None | 0 |  |
| `static_drop` | 1 | `effect body; drop x; main-returned` | 0 | None | 0 |  |
| `static_glue_in_cleanup` | 0 | `drop t0; drop t1; drop t2` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `static_glue_in_cleanup` | 1 | `drop t0; drop t1; drop t2` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `tuple_first_dtor_panics` | 0 | `effect body; drop t0; drop t1; drop t2` | 101 | None | 1 |  |
| `tuple_first_dtor_panics` | 1 | `effect body; drop t0; drop t1; drop t2` | 101 | None | 1 |  |
| `tuple_two_dtors_panic` | 0 | `effect body; drop t0; drop t1` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `tuple_two_dtors_panic` | 1 | `effect body; drop t0; drop t1` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `two_cond_moves` | 0 | `consume y; drop y; effect join; drop x; main-returned` | 0 | None | 0 |  |
| `two_cond_moves` | 1 | `consume x; drop x; effect join; drop y; main-returned` | 0 | None | 0 |  |

## panic_abort (`support/specimens/drop_specimens.rs`)

Totals over 32 functions: flag locals 16; blocks 378 -> 542; cleanup blocks 110 -> 209; drop terminators 153 -> 127; flag tests 39; flag writes 64; styles {"conditional": 14, "dead": 67, "open": 18, "static": 54}.

| function | flags | blocks pre→post | cleanup pre→post | drops pre→post | flag tests | flag writes T/F | styles | blocks at runtime-post-cleanup |
| :-- | --: | :-- | :-- | :-- | --: | :-- | :-- | --: |
| `array_cond_move` | 1 | 17→30 | 5→13 | 8→7 | 3 | 1/3 | {"dead": 5, "open": 2, "static": 1} | 11 |
| `array_static_drop` | 0 | 10→10 | 3→3 | 5→3 | 0 | 0/0 | {"dead": 2, "static": 3} | 5 |
| `assign_overwrite` | 0 | 10→10 | 3→3 | 5→3 | 0 | 0/0 | {"dead": 2, "static": 3} | 6 |
| `assign_overwrite_old_dtor_panics` | 0 | 10→10 | 3→3 | 5→3 | 0 | 0/0 | {"dead": 2, "static": 3} | 6 |
| `box_cond_move` | 1 | 13→25 | 4→10 | 4→2 | 2 | 1/3 | {"dead": 2, "open": 2} | 11 |
| `cond_assign_overwrite` | 1 | 15→19 | 4→6 | 6→3 | 2 | 3/3 | {"conditional": 2, "dead": 3, "static": 1} | 11 |
| `cond_init` | 1 | 12→16 | 3→5 | 5→2 | 2 | 2/2 | {"conditional": 2, "dead": 3} | 8 |
| `cond_move` | 1 | 11→15 | 3→5 | 3→2 | 2 | 1/3 | {"conditional": 2, "dead": 1} | 9 |
| `cond_partial_move_nested` | 1 | 20→44 | 6→22 | 10→13 | 4 | 1/3 | {"dead": 6, "open": 2, "static": 2} | 13 |
| `cond_partial_move_struct` | 1 | 18→34 | 5→15 | 8→11 | 3 | 1/3 | {"dead": 4, "open": 2, "static": 2} | 13 |
| `cond_partial_move_tuple` | 1 | 15→28 | 4→12 | 6→7 | 3 | 1/3 | {"dead": 3, "open": 2, "static": 1} | 11 |
| `copy_type` | 0 | 3→3 | 1→1 | 0→0 | 0 | 0/0 | {} | 2 |
| `dead_drop` | 0 | 8→8 | 3→3 | 3→0 | 0 | 0/0 | {"dead": 3} | 4 |
| `double_panic` | 0 | 9→9 | 3→3 | 4→4 | 0 | 0/0 | {"static": 4} | 6 |
| `dtor_panics_normal_path` | 0 | 9→9 | 3→3 | 4→4 | 0 | 0/0 | {"static": 4} | 6 |
| `early_return` | 0 | 13→13 | 3→3 | 5→5 | 0 | 0/0 | {"static": 5} | 10 |
| `generic_cond_move` | 1 | 10→14 | 3→5 | 3→2 | 2 | 1/2 | {"conditional": 2, "dead": 1} | 8 |
| `generic_cond_move_copy` | 0 | 3→3 | 1→1 | 0→0 | 0 | 0/0 | {} | 2 |
| `generic_cond_move_loud` | 0 | 5→5 | 2→2 | 1→0 | 0 | 0/0 | {"dead": 1} | 3 |
| `loop_break_move` | 1 | 17→21 | 3→5 | 3→2 | 2 | 1/3 | {"conditional": 2, "dead": 1} | 15 |
| `manually_drop` | 0 | 6→6 | 2→2 | 1→0 | 0 | 0/0 | {"dead": 1} | 4 |
| `maybe_uninit` | 0 | 6→6 | 2→2 | 1→0 | 0 | 0/0 | {"dead": 1} | 4 |
| `nounwind_abi` | 0 | 7→7 | 2→2 | 2→2 | 0 | 0/0 | {"static": 2} | 5 |
| `open_ladder_in_cleanup` | 1 | 21→37 | 6→16 | 10→13 | 3 | 1/3 | {"dead": 4, "open": 2, "static": 4} | 15 |
| `open_ladder_normal_two_panics` | 1 | 18→34 | 5→15 | 8→11 | 3 | 1/3 | {"dead": 4, "open": 2, "static": 2} | 13 |
| `option_cond_move` | 2 | 16→35 | 4→17 | 6→4 | 4 | 2/5 | {"dead": 4, "open": 2} | 12 |
| `partial_move_tuple` | 0 | 12→19 | 4→8 | 6→4 | 0 | 0/0 | {"dead": 3, "open": 2, "static": 1} | 6 |
| `static_drop` | 0 | 6→6 | 2→2 | 2→2 | 0 | 0/0 | {"static": 2} | 4 |
| `static_glue_in_cleanup` | 0 | 16→16 | 5→5 | 9→6 | 0 | 0/0 | {"dead": 3, "static": 6} | 8 |
| `tuple_first_dtor_panics` | 0 | 13→13 | 4→4 | 7→4 | 0 | 0/0 | {"dead": 3, "static": 4} | 6 |
| `tuple_two_dtors_panic` | 0 | 13→13 | 4→4 | 7→4 | 0 | 0/0 | {"dead": 3, "static": 4} | 6 |
| `two_cond_moves` | 2 | 16→24 | 5→9 | 6→4 | 4 | 2/6 | {"conditional": 4, "dead": 2} | 13 |

| function | arg | stdout | exit | signal | panics | runtime markers |
| :-- | --: | :-- | --: | :-- | --: | :-- |
| `array_cond_move` | 0 | `effect join; drop arr1; drop arr0; main-returned` | 0 | None | 0 |  |
| `array_cond_move` | 1 | `consume arr0; drop arr0; effect join; drop arr1; main-returned` | 0 | None | 0 |  |
| `array_static_drop` | 0 | `effect body; drop arr0; drop arr1; main-returned` | 0 | None | 0 |  |
| `array_static_drop` | 1 | `effect body; drop arr0; drop arr1; main-returned` | 0 | None | 0 |  |
| `assign_overwrite` | 0 | `drop old; effect after-assign; drop new; main-returned` | 0 | None | 0 |  |
| `assign_overwrite` | 1 | `` | None | SIGABRT | 1 |  |
| `assign_overwrite_old_dtor_panics` | 0 | `drop old` | None | SIGABRT | 1 |  |
| `assign_overwrite_old_dtor_panics` | 1 | `drop old` | None | SIGABRT | 1 |  |
| `box_cond_move` | 0 | `effect join; drop boxed; main-returned` | 0 | None | 0 |  |
| `box_cond_move` | 1 | `consume boxed; drop boxed; effect join; main-returned` | 0 | None | 0 |  |
| `cond_assign_overwrite` | 0 | `drop old; effect after-assign; drop new; main-returned` | 0 | None | 0 |  |
| `cond_assign_overwrite` | 1 | `consume old; drop old; effect after-assign; drop new; main-returned` | 0 | None | 0 |  |
| `cond_init` | 0 | `effect join; main-returned` | 0 | None | 0 |  |
| `cond_init` | 1 | `effect join; drop x; main-returned` | 0 | None | 0 |  |
| `cond_move` | 0 | `effect join; drop x; main-returned` | 0 | None | 0 |  |
| `cond_move` | 1 | `consume x; drop x; effect join; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_nested` | 0 | `effect join; drop n00; drop n01; drop n1; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_nested` | 1 | `consume n01; drop n01; effect join; drop n00; drop n1; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_struct` | 0 | `effect join; drop s.a; drop s.b; drop s.c; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_struct` | 1 | `consume s.b; drop s.b; effect join; drop s.a; drop s.c; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_tuple` | 0 | `effect join; drop p0; drop p1; main-returned` | 0 | None | 0 |  |
| `cond_partial_move_tuple` | 1 | `consume p0; drop p0; effect join; drop p1; main-returned` | 0 | None | 0 |  |
| `copy_type` | 0 | `effect body; main-returned` | 0 | None | 0 |  |
| `copy_type` | 1 | `effect body; main-returned` | 0 | None | 0 |  |
| `dead_drop` | 0 | `consume x; drop x; effect after; main-returned` | 0 | None | 0 |  |
| `dead_drop` | 1 | `consume x; drop x; effect after; main-returned` | 0 | None | 0 |  |
| `double_panic` | 0 | `` | None | SIGABRT | 1 |  |
| `double_panic` | 1 | `` | None | SIGABRT | 1 |  |
| `dtor_panics_normal_path` | 0 | `effect body; drop a` | None | SIGABRT | 1 |  |
| `dtor_panics_normal_path` | 1 | `effect body; drop a` | None | SIGABRT | 1 |  |
| `early_return` | 0 | `effect tail; drop b; drop a; main-returned` | 0 | None | 0 |  |
| `early_return` | 1 | `drop a; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_copy` | 0 | `effect join; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_copy` | 1 | `effect join; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_loud` | 0 | `effect join; drop g; main-returned` | 0 | None | 0 |  |
| `generic_cond_move_loud` | 1 | `drop g; effect join; main-returned` | 0 | None | 0 |  |
| `loop_break_move` | 0 | `effect after-loop; drop x; main-returned` | 0 | None | 0 |  |
| `loop_break_move` | 1 | `consume x; drop x; effect after-loop; main-returned` | 0 | None | 0 |  |
| `manually_drop` | 0 | `effect body; main-returned` | 0 | None | 0 |  |
| `manually_drop` | 1 | `effect body; main-returned` | 0 | None | 0 |  |
| `maybe_uninit` | 0 | `effect body; main-returned` | 0 | None | 0 |  |
| `maybe_uninit` | 1 | `effect body; main-returned` | 0 | None | 0 |  |
| `nounwind_abi` | 0 | `effect body; drop g; main-returned` | 0 | None | 0 |  |
| `nounwind_abi` | 1 | `` | None | SIGABRT | 1 |  |
| `open_ladder_in_cleanup` | 0 | `` | None | SIGABRT | 1 |  |
| `open_ladder_in_cleanup` | 1 | `consume t2; drop t2` | None | SIGABRT | 1 |  |
| `open_ladder_normal_two_panics` | 0 | `effect body; drop t0` | None | SIGABRT | 1 |  |
| `open_ladder_normal_two_panics` | 1 | `consume t2; drop t2; effect body; drop t0` | None | SIGABRT | 1 |  |
| `option_cond_move` | 0 | `effect join; drop o; main-returned` | 0 | None | 0 |  |
| `option_cond_move` | 1 | `consume o; drop o; effect join; main-returned` | 0 | None | 0 |  |
| `partial_move_tuple` | 0 | `consume p0; drop p0; effect after; drop p1; main-returned` | 0 | None | 0 |  |
| `partial_move_tuple` | 1 | `consume p0; drop p0; effect after; drop p1; main-returned` | 0 | None | 0 |  |
| `static_drop` | 0 | `effect body; drop x; main-returned` | 0 | None | 0 |  |
| `static_drop` | 1 | `effect body; drop x; main-returned` | 0 | None | 0 |  |
| `static_glue_in_cleanup` | 0 | `` | None | SIGABRT | 1 |  |
| `static_glue_in_cleanup` | 1 | `` | None | SIGABRT | 1 |  |
| `tuple_first_dtor_panics` | 0 | `effect body; drop t0` | None | SIGABRT | 1 |  |
| `tuple_first_dtor_panics` | 1 | `effect body; drop t0` | None | SIGABRT | 1 |  |
| `tuple_two_dtors_panic` | 0 | `effect body; drop t0` | None | SIGABRT | 1 |  |
| `tuple_two_dtors_panic` | 1 | `effect body; drop t0` | None | SIGABRT | 1 |  |
| `two_cond_moves` | 0 | `consume y; drop y; effect join; drop x; main-returned` | 0 | None | 0 |  |
| `two_cond_moves` | 1 | `consume x; drop x; effect join; drop y; main-returned` | 0 | None | 0 |  |

## custom_mir_unwind (`support/specimens/custom_mir_specimens.rs`)

Totals over 3 functions: flag locals 3; blocks 16 -> 25; cleanup blocks 0 -> 3; drop terminators 5 -> 5; flag tests 3; flag writes 8; styles {"conditional": 3, "static": 2}.

| function | flags | blocks pre→post | cleanup pre→post | drops pre→post | flag tests | flag writes T/F | styles | blocks at runtime-post-cleanup |
| :-- | --: | :-- | :-- | :-- | --: | :-- | :-- | --: |
| `cleanup_terminate` | (runtime-dialect body: `ElaborateDrops` does not run) | | | | | | | |
| `join_no_flag_always_drop` | (runtime-dialect body: `ElaborateDrops` does not run) | | | | | | | |
| `join_no_flag_never_drop` | (runtime-dialect body: `ElaborateDrops` does not run) | | | | | | | |
| `join_reference` | 1 | 5→8 | 0→1 | 1→1 | 1 | 1/2 | {"conditional": 1} | 7 |
| `stale_flag_join` | 1 | 5→8 | 0→1 | 2→2 | 1 | 1/1 | {"conditional": 1, "static": 1} | 7 |
| `stale_flag_join_storage_dead` | 1 | 6→9 | 0→1 | 2→2 | 1 | 1/2 | {"conditional": 1, "static": 1} | 8 |

| function | arg | stdout | exit | signal | panics | runtime markers |
| :-- | --: | :-- | --: | :-- | --: | :-- |
| `cleanup_terminate` | 0 | `drop bomb` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `cleanup_terminate` | 1 | `drop bomb` | None | SIGABRT | 3 | panic in a destructor during cleanup; thread caused non-unwinding panic. aborting. |
| `join_no_flag_always_drop` | 0 | `drop x; main-returned` | 0 | None | 0 |  |
| `join_no_flag_always_drop` | 1 | `consume x; drop x; drop x; main-returned` | 0 | None | 0 |  |
| `join_no_flag_never_drop` | 0 | `main-returned` | 0 | None | 0 |  |
| `join_no_flag_never_drop` | 1 | `consume x; drop x; main-returned` | 0 | None | 0 |  |
| `join_reference` | 0 | `drop x; main-returned` | 0 | None | 0 |  |
| `join_reference` | 1 | `consume x; drop x; main-returned` | 0 | None | 0 |  |
| `stale_flag_join` | 0 | `drop x; main-returned` | 0 | None | 0 |  |
| `stale_flag_join` | 1 | `drop x; drop x; main-returned` | 0 | None | 0 |  |
| `stale_flag_join_storage_dead` | 0 | `drop x; main-returned` | 0 | None | 0 |  |
| `stale_flag_join_storage_dead` | 1 | `drop x; main-returned` | 0 | None | 0 |  |

## Ill-formed hand-written body

- source: `support/specimens/custom_mir_cleanup_continue.rs`
- compiler exit code: 101
- compiler message: `error: internal compiler error: <rustc-src>/compiler/rustc_mir_transform/src/validate.rs:258:26: broken MIR in Item(DefId(0:12 ~ custom_mir_cleanup_continue[9c82]::cleanup_continue)) (after phase change to runtime-optimized) at bb5[0]:`

## Checks

| check | result | measured |
| :-- | :-- | :-- |
| `mir_built_specimens_never_drop_twice` | pass | max destructor runs per value = 1 |
| `no_flag::static_drop` | pass | flag locals = 0 |
| `no_flag::dead_drop` | pass | flag locals = 0 |
| `no_flag::early_return` | pass | flag locals = 0 |
| `no_flag::partial_move_tuple` | pass | flag locals = 0 |
| `no_flag::manually_drop` | pass | flag locals = 0 |
| `no_flag::maybe_uninit` | pass | flag locals = 0 |
| `no_flag::copy_type` | pass | flag locals = 0 |
| `has_flag::cond_move` | pass | flag locals = 1 |
| `has_flag::cond_init` | pass | flag locals = 1 |
| `has_flag::loop_break_move` | pass | flag locals = 1 |
| `has_flag::cond_partial_move_tuple` | pass | flag locals = 1 |
| `has_flag::cond_partial_move_struct` | pass | flag locals = 1 |
| `no_drop_glue::manually_drop` | pass | pre drops = 1, post drops = 0, destructor runs = 0 |
| `no_drop_glue::maybe_uninit` | pass | pre drops = 1, post drops = 0, destructor runs = 0 |
| `no_drop_glue::copy_type` | pass | pre drops = 0, post drops = 0, destructor runs = 0 |
| `exactly_once::cond_move` | pass | {0: {'x': 1}, 1: {'x': 1}} |
| `exactly_once::loop_break_move` | pass | {0: {'x': 1}, 1: {'x': 1}} |
| `exactly_once::cond_partial_move_tuple` | pass | {0: {'p0': 1, 'p1': 1}, 1: {'p0': 1, 'p1': 1}} |
| `open_drop_siblings::cond_partial_move_struct` | pass | ['consume s.b', 'drop s.b', 'effect join', 'drop s.a', 'drop s.c', 'main-returned'] |
| `open_drop_ladder_shape::cond_partial_move_tuple` | pass | [{"flag": "_10", "test_block": "bb23", "first_field_drop": {"block": "bb22", "place": "(_2.0: Loud)"}, "second_field_drop": {"block": "bb20", "place": "(_2.1: Loud)"}, "unwind_second_field_drop": {"block": "bb16", "place": "(_2.1: Loud)", "unwind": "terminate(cleanup)"}, "resume_block": "bb14"}] |
| `assign_overwrite::old_dropped_before_new_lives` | pass | ['drop old', 'effect after-assign', 'drop new', 'main-returned'] |
| `assign_overwrite::constructor_panic_drops_old_once` | pass | stdout = ['drop old'], exit = 101 |
| `assign_overwrite::assignment_completes_on_unwind_path` | pass | stdout = ['drop old', 'drop new'], exit = 101, panics = 1 |
| `double_panic::aborts_with_sigabrt` | pass | signal = SIGABRT, markers = ['panic in a destructor during cleanup', 'thread caused non-unwinding panic. aborting.'], stdout = ['drop a'] |
| `glue::one_panic_still_drops_siblings` | pass | stdout = ['effect body', 'drop t0', 'drop t1', 'drop t2'], exit = 101 |
| `glue::second_panic_aborts_before_third_field` | pass | stdout = ['effect body', 'drop t0', 'drop t1'], signal = SIGABRT |
| `pre_abort_trace_differs_between_static_and_open` | pass | static glue stdout = ['drop t0', 'drop t1', 'drop t2']; open ladder stdout = ['drop t0'] |
| `panic_abort::no_cleanup_after_abort_unwinding_calls` | pass | offending functions = [] |
| `panic_abort::same_elaboration_as_unwind` | pass | functions whose flags, styles, drops or flag tests differ = [] |
| `panic_abort::first_panic_aborts_without_destructors` | pass | signal = SIGABRT, stdout = [], panics = 1 |
| `array::open_ladder_reverses_range_order` | pass | whole-array drop stdout = ['effect body', 'drop arr0', 'drop arr1', 'main-returned']; open-ladder stdout = ['effect join', 'drop arr1', 'drop arr0', 'main-returned'] |
| `nounwind_abi::resume_rewritten_and_cleanup_still_runs` | pass | resume before/after = 1/0, terminate after = 1, stdout = ['drop g'], signal = SIGABRT |
| `custom_mir::no_flag_always_drop_runs_destructor_twice` | pass | ['consume x', 'drop x', 'drop x', 'main-returned'] |
| `custom_mir::no_flag_never_drop_leaks` | pass | ['main-returned'] |
| `custom_mir::real_pass_inserts_flag_exactly_once` | pass | destructor runs for x with argument 0/1 = [1, 1] |
| `custom_mir::stale_flag_join_runs_destructor_twice` | pass | stdout = ['drop x', 'drop x', 'main-returned'], flags = ['_3'] |
| `custom_mir::storage_dead_clears_flag` | pass | stdout = ['drop x', 'main-returned'] |
| `custom_mir::continue_in_cleanup_rejected` | pass | rustc exit = 101, message found = True |
