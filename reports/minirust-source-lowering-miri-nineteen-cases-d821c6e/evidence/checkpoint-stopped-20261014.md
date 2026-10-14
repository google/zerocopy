# Stopped execution checkpoint, 2026-10-14

Stopped on the parent's instruction following its reported automated cybersecurity-content flag. No further experiments, compiler invocations, repair generation, or builds were started after that instruction. The flag's exact interrupted operation is not visible in this agent's tool outputs. The last actual experiment completed was `upstream_ub_enum_ub_discriminant`; subsequent pre-stop tools only read source files. E05 optimized-MIR erasure work had not begun.

All paths below are relative to this checkpoint's directory, `@CAPTURE@`. Existing source, first-run outputs, compiler MIR, actual emitted MiniRust JSON, statuses and logs remain preserved. No native subject program was executed. No Git, canonical, issue or external publication changes were made.

## Completed investigation

Nineteen sources have Miri Tree Borrows results. Seventeen have actual emitted MiniRust executed under both Tree Borrows and Basic memory: sixteen agree with Miri, and one disagrees. Two additional sources stop in lowering and have no MiniRust semantic result. A successful exit is bounded evidence for the recorded program and interpreter configuration, not a source adequacy proof.

For each successful lowering, its run directory contains `rustc-input.mir`, `minimize-lower.stdout`, `minirust.json`, `result.json`, and per-command `.status.json`, `.stdout`, and `.stderr` files. The two lowering failures instead retain compiler MIR and failure/Miri status files. Exact command flags and return codes are in those status files. `inventory/cases.json` records every source path, full SHA-256, provenance and expected Miri outcome; the table below repeats those identities for the handoff.

| Case | Run directory | Mini Tree / Basic | Miri Tree | Source SHA-256 |
|---|---|---|---|---|
| smoke | `runs/smoke` | success | success | `a7f87990019385c2c8d861563a9f556cb97024d39b98dfedb0f535c1aa315279` |
| union_wide_one_field | `runs/union_wide_one_field` | UB | success | `04b5b028957da292ed7f3a662e3c7b4cd02b4f6951566fb30cd8c74292d76fc0` |
| union_wide_two_word_control | `runs/union_wide_two_word_control` | success | success | `5215d4828f6ec1d9da159cf9fc9f3c704da93d07e819a1be373631b71e8a2b21` |
| wide_pointer_control | `runs/wide_pointer_control` | success | success | `f8a065f483758d43f7540a6eab7db926b619fb00f9555b39e5a236f97b55e1d0` |
| enum_single_zero | `runs/enum_single_zero` | success | success | `765c0d37665748d0486123b50d5f82f8c420af016a10115c063e1354abc2b6eb` |
| enum_single_invalid_one | `runs/enum_single_invalid_one` | UB | UB | `082e1fb5fc34f024ae4c345e0689400175612898cb00eafa45502f393cc4cdd1` |
| enum_pair_one | `runs/enum_pair_one` | success | success | `3a02630a271a7cfa6149438a0bf6f64626626c996d89def3e718f2e45a69e65a` |
| enum_pair_invalid_two | `runs/enum_pair_invalid_two` | UB | UB | `55a3db8ea41f3f058860d8c52e1d7218431c9df5c1fd02839ebebc3630350060` |
| library_split_cell | `runs/library_split_cell` | success | success | `64f415ef81d605e3ea5657cd97c4a56be09b724e5f50946938efcef0202ec865` |
| library_box | `runs/library_box` | lowering ICE; no model result | success | `84783ec91b3c51c60b796e21d86508ac85f2a3eacf4ca50d91773a6da93e299a` |
| library_drop_count | `runs/library_drop_count` | success | success | `84038a1ff17e82b88f519202409fdbb519d3e8e1fe3f153432fa743473faaf6b` |
| library_drop_unwind | `runs/library_drop_unwind` | lowering ICE; no model result | success, expected caught panic | `619f1394d545cebe7309bc5d066f567853fe68905ec8a5bfdeee5150e171815c` |
| upstream_pass_enum_direct_tag | `runs/upstream_pass_enum_direct_tag` | success | success | `f6e7dea4f6a869e81cfed6e7ae80f8d9e5fc2910f1591d92dc8bff2e2c9404f7` |
| upstream_pass_enum_niche_tag | `runs/upstream_pass_enum_niche_tag` | success | success | `96372276b1ae27bd59dbf799ed42df0d10120eb7fb5032f63ccba39e5dcb36dd` |
| upstream_pass_slice | `runs/upstream_pass_slice` | success | success | `f4a72bab925364400d5607cd8f73864a4a0be9b464c0d880cf1ef01d0a534e61` |
| upstream_pass_drop | `runs-after-harness-fix/upstream_pass_drop` | success | success | `16c74a3131bf0334e9233812c017e1da7c64baec2f9bab449acca5a822b34137` |
| upstream_pass_tree_borrows_cell_inside_struct | `runs-after-harness-fix/upstream_pass_tree_borrows_cell_inside_struct` | success | success | `258ee141b26733d8a469fc201899baabf18ebfca6e799364843be87ab31babb9` |
| upstream_ub_inv_bool | `runs-after-harness-fix/upstream_ub_inv_bool` | UB | UB | `cf7c1f198ede8653db4f24a18a2807896dadb85ca04fbe08fbdc065df522f489` |
| upstream_ub_enum_ub_discriminant | `runs-after-harness-fix/upstream_ub_enum_ub_discriminant` | UB | UB | `825daf8dc3b049d170960a865199b3291295544bc2838ded5d944f3d2002dee9` |

## Preserved original disagreement and diagnosis

The valid one-field union source succeeds in Miri and fails with MiniRust UB in both memory models. Its actual source-generated union has size 16, alignment 8, a raw `ElementCount` pointer field at offset zero, and chunks `[[0,8]]`. The two-word array-field control produces `[[0,16]]` and succeeds in all three interpreters. Direct wide-pointer copying also succeeds. The actual source MIR copies the union through a non-inlined identity function.

Pinned `workspace/tooling/minimize/src/chunks.rs:47` marks every pointer using only `DefaultTarget::PTR_SIZE`. `ty.rs:217–220` uses this function for union chunks. Pinned specification `spec/lang/representation.md:155–178` represents wide pointers as two words; its union encoder at 332–340 initializes all bytes to Uninit then restores only chunks. Thus the emitted union omits its metadata word. This is a valid-source rejection / false positive in the tested translation-model pipeline. It is not evidence that invalid source is accepted, nor a proof about all unions or source/model refinement directions.

Original disagreement evidence:

- Source SHA-256: `04b5b028957da292ed7f3a662e3c7b4cd02b4f6951566fb30cd8c74292d76fc0`.
- MIR SHA-256: `42a8bafb7c383558deb03c16fad17bc192e15cc67ac407e75d21412ae46b0b22`.
- Actual emitted MiniRust JSON SHA-256: `777d5f58831da2911bf7c9c3265f5edbd18a8af649f9a96d4e680458ceae3327`.
- Both MiniRust stderr SHA-256: `a859ffe2bfb0e80addc18ab82e593a1ef8a4801d70f5445f5e1ffb03f78df6fc`.
- Miri exit zero with empty stdout and stderr; exact command in `runs/union_wide_one_field/miri-tree.status.json`.

The actual source-generated single-variant enum has a Branch discriminator with Invalid fallback and a tagger. Valid zero passes and invalid one is rejected by both engines. This corrects any attempt to transfer the earlier synthetic Known-discriminator speculation to this source enum; no broad enum adequacy claim follows.

## Diagnosed failures, without retries of failing lowering

Both Box and caught-unwind fixtures reach minimize's explicit foreign-item `span_bug!` at `minimize/src/bb.rs:790`, naming `alloc::alloc::__rust_dealloc` from exact installed `alloc/src/alloc.rs:128`. Compiler MIR emission succeeds. Both sources independently pass Miri; the unwind source records the expected caught subject panic and successful outer Drop-count assertion. These are lowering tool failures, not model UB, Rust unsupported-language results, or completed MiniRust unwind execution. See `diagnoses/library_box.json`, `diagnoses/library_drop_unwind.json`, and original `minimize-lower.stderr` files. No failing lowering was retried.

The initial upstream Drop run failed before MIR emission because the owned harness named dependency metadata `intrinsics.rmeta` instead of the compiler-required `libintrinsics.rmeta`. This owned harness defect and its original outputs remain at `runs/upstream_pass_drop`. Corrected fresh results are under `runs-after-harness-fix`. The test source is unchanged. `diagnoses/harness-extern-filename.json` records the correction; `inventory/run_cases-v1.py` preserves the original driver. No test-source or semantic repair was made.

## Repair and pending work

No isolated repair workspace, source patch, patched build, patched test, expanded DST/vtable/nested-union fixture, JSON comparison or optimized-MIR erasure experiment exists. The intended one-line pointer-layout repair was only discussed. The current original upstream Rust source remains unchanged; only exact local path-source Cargo.lock overrides were applied during initial workspace preparation, as inventoried.

Unestablished obligations include a general recursive union-chunk invariant; repair validation across metadata forms, nested unions and padding; preservation of relevant first-bad-prefix operations across actual MIR passes; complete library allocation and caught-unwind lowering; matching source/model validity and aliasing relations; and general source adequacy. The nineteen-case corpus does not discharge these.

## Tool and resource handoff

Pinned MiniRust: `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`; pinned Specr: `15200eb5e676e2ee91f43bd79e674f8fc32e5348`. Exact parent-restored Rust compiler commit: `f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, requested nightly 2026-05-01. The actual target for both engines was `aarch64-apple-darwin`. The interpreter data-layout check succeeds; this is not an x86 ISA validation claim. Driver flag differences are retained in `run_cases.py`, `inventory/miri-driver-primary-source.json`, and command statuses.

`status/build-minimize.json` records the successful offline, locked, -j2 minimize/minirun build, 19.748 s, log SHA-256 `8781cdaa571d0bd935f2f36d1b5d068b62f11599edad5991bb562ea436cf02df`. `status/minimize-sysroot.json` records 11.933 s success; `status/miri-sysroot.json` records 10.868 s success and log SHA-256 `d106ac2a322dd27493b6b604b8dd5b9be5976aa340d069753740895b94ac923e`. Exact temporary builder inputs are retained in `captured-inputs`. `inventory/dependency-archives.json` preserves 102 crate archives and checksum identities. Original lock/source inventories are under `inventory`.

All agent-owned compiler/interpreter subprocess calls returned; no yielded exec cell, PTY session, background job or outstanding asynchronous build is owned by this agent. A read-only process inventory attempt was denied by the sandbox (`ps: Operation not permitted`), so this does not assert a system-wide absence of processes. No escalation was attempted. Parent owns the shared restored toolchain. This task owns its Cargo cache, target directory and both sysroots under this root; no cleanup was performed. Last recorded task size is 639,967,320 bytes, below the 2 GiB allocation. No more execution will occur without the parent's further instruction.

Authored by an AI agent acting on joshlf's behalf.
