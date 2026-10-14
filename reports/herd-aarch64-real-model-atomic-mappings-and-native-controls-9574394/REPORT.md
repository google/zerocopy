# Actual AArch64 herd outcomes, Rust atomic mappings and concurrent assembly controls

## Summary

Ten actual runs of pinned herd distinguish missing release, acquire and fence edges. Both LDAR and LDAPR complete the selected message-passing pattern when paired with STLR. For the selected store-buffering pattern, STLR/LDAPR permits both reads to return zero; STLR/LDAR and two DMB ISH barriers forbid that outcome. These are results of the selected executable model, not hardware observations.

The actual May 1 Rust nightly emits LDAPR for the selected Acquire loads and LDAR for the SeqCst load, under its default `apple-m1` target setting. Six concurrent assembly-wrapper cases each completed 10,000 native rounds on the recorded Apple M4 Pro host. All observed outcomes are model-allowed. **No weak target outcome was observed**, including in the cases where herd permits it. Two incorrect `nomem`/`readonly` annotation controls were compiled only: the compiler retains the assembly store but replaces the following Rust load with the constant 7. The complete effect contract retains an actual load.

This supplies the bounded experiment evidence requested by E38. It does not prove the Rust/compiler/hardware weak-memory compatibility requested by E39.

*Authored by an AI agent acting on joshlf's behalf.*

## Applicability

The subjects form an evidence chain, not a proved refinement chain:

- herdtools7 commit `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`, actual executable reporting `7.58+1, Rev: exported`, SHA-256 `b50b95ab172b076b01d44b49e35cc86566ee6332550edce282a896db55e5095e`. Every model command selects `herd/libdir/aarch64.cat` with that directory on the include path; none supplies `-variant` or `-conf`. The inspected `herd/opts.ml:44` initializes variant selection to false; the complete actual argv is preserved for each run. The inputs use two symbolic locations, two threads and 32-bit W-register loads/stores. These are ordinary AArch64 data-memory cases; they do not exercise translation, instruction fetch, mixed sizes, RMWs or exceptional behavior.
- Rust `nightly-2026-05-01-aarch64-apple-darwin`, actual `rustc 1.97.0-nightly (f53b654a8 2026-04-30)`, full commit `f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, LLVM 22.1.4. Commands use edition 2021, optimization level 3 and no explicit `target-cpu` override. Generated IR records `target-cpu=apple-m1`; the captured default cfg includes `rcpc`. This compiler configuration is distinct from the physical CPU.
- Native execution records macOS 27.0.1, process architecture `arm64`, and a successful post-run CPU query returning `Apple M4 Pro`. The wrapper checks runtime RCpc support before starting; successful completion establishes that this check passed. An earlier CPU-brand query was denied by the sandbox; the later successful query resolves the host label. The denied query was retained in the task transcript, not as a subprocess receipt in this package.
- Rust Reference commit `2dafab96d919d6ab2884488e970bf95610ff83eb`, inline-assembly option and memory-contract sections. This interprets the incorrect-annotation controls; it does not supply a theorem connecting foreign assembly events to Rust atomic events.

The native program uses externally defined `global_asm!` leaves through raw-pointer C-ABI declarations. Its concurrent test is not the direct execution of the eight safe Rust `AtomicU32` functions. The inspected generated instructions match those functions after symbol and argument-register correspondence. Valid pointer construction, lifetime and round separation are reviewed below; the external atomic-memory interpretation remains an explicit trust boundary.

## Findings

### The actual model distinguishes all selected ordering controls

Basis: source + execution + derived explanation of the selected CAT relations.

Message passing writes data `x=1`, then publishes flag `y=1`. The reader loads flag, then data. The target is `(flag,data)=(1,0)`. Store buffering has each thread write its own location, then read its peer's location; the target is `(read0,read1)=(0,0)`. `Sometimes` means at least one enumerated model state satisfies the target; `Never` means none does. The printed `Test … Allowed` header alone is not the target verdict.

| Input | Publish / observation, or store / load | Target result | Enumerated states |
| --- | --- | --- | --- |
| MP-r0-a0 | STR flag; LDR flag | Sometimes | 4 |
| MP-r0-a1 | STR flag; LDAR flag | Sometimes | 4 |
| MP-r0-p1 | STR flag; LDAPR flag | Sometimes | 4 |
| MP-r1-a0 | STLR flag; LDR flag | Sometimes | 4 |
| MP-r1-a1 | STLR flag; LDAR flag | Never | 3 |
| MP-r1-p1 | STLR flag; LDAPR flag | Never | 3 |
| SB | STR; LDR | Sometimes | 4 |
| SB-STLR-LDAPR | STLR; LDAPR | Sometimes | 4 |
| SB-STLR-LDAR | STLR; LDAR | Never | 3 |
| SB-dmb | STR; DMB ISH; LDR in both threads | Never | 3 |

The six permitted-target cases each print one positive and three negative states. The four forbidden-target cases print zero positive and three negative states. Full final-register states and conditions are preserved in [the run outputs](evidence/runs/MP-r1-p1.stdout); [static-validation.json](static-validation.json) collects the ten cases without replacing those outputs. No graph-image or DOT trace was captured.

The source explains why the two acquire forms agree on this message-passing test but differ on store buffering. `lib/AArch64Base.ml:1254–1260` maps AA to LDAR and AQ to LDAPR; `herd/AArch64Sem.ml:2056–2072` assigns their events A and Q, respectively. STLR uses L in `stlr` at lines 2173–2174. `herd/AArch64Annot.ml:39–59` exposes these as distinct CAT sets. In `aarch64hwreqs.cat:128–138`, `bob` orders prior memory before release stores, and orders either A or Q reads before subsequent memory. It additionally orders an L write before an A read; that clause excludes Q. DMB full orders memory on both sides. `aarch64.cat:155–161` closes the selected ordered-before relation and requires irreflexivity. Thus the missing release/acquire controls remove an edge needed to reject stale message passing; the extra L-to-A clause distinguishes the selected SB pair. This explanation is derived from the inspected source and agrees with the actual enumeration; it is not a separate mechanized proof of the model.

Every herd command exited zero. Each stderr contains the OCaml environment's root-user warning. SB-dmb also prints the model's `Shareability-argument-for-DMB-is-deprecated` flag, defined by `aarch64fences.cat:37–42`; the run still prints its full state set and `Never` target result. The flag is retained, not suppressed.

### Actual Rust atomic code generation selects the relevant instructions

Basis: source + compiler execution. Source: [atomic_wrappers.rs](evidence/atomic_wrappers.rs); output: [atomic_wrappers.s](evidence/atomic_wrappers.s).

| Exported Rust function | Relevant emitted instructions |
| --- | --- |
| `publish_relaxed` | STR data; STR flag |
| `publish_release` | STR data; STLR flag |
| `observe_relaxed` | LDR flag; LDR data |
| `observe_acquire` | LDAPR flag; LDR data |
| `store_then_load_relaxed` | STR own; LDR peer |
| `store_then_load_fenced` | STR own; DMB ISH; LDR peer |
| `store_then_load_release_acquire` | STLR own; LDAPR peer |
| `store_then_load_seqcst` | STLR own; LDAR peer |

The observer combines flag in the upper 32 bits and data in the lower 32 bits. These are 32-bit atomic operations, with no RMW. The final eight-function compile has an explicit source hash and compiler binary hash in [its receipt](evidence/runs/final-rustc-atomic-asm.json). The preserved earlier source/output has six functions; its first compile receipt does not by itself establish the later eight-function output. No claim is made for another target CPU, compiler version, optimization level or whole-program context. The safe Rust functions were compiled, not invoked by the native test.

### The native wrapper uses valid locations and observes only allowed states

Basis: source review + compilation + native execution + comparison of recorded state sets.

[concurrent_assembly.rs](evidence/concurrent_assembly.rs) puts each live `AtomicU32` in a `repr(align(128))` wrapper inside an `Arc`. Each worker obtains pointers with `AtomicU32::as_ptr`; no deliberately invalid pointer, unaligned access, transient stack address or manufactured `&mut` is passed. The inspected leaves access one u32 at each supplied address, use only caller-saved registers, and return. The main thread resets the cells before a three-party start barrier; a three-party done barrier separates worker accesses from observation and the next reset. Result slots are Rust `AtomicU64`s. Both threads are joined before `run` returns. These facts control the specimen's pointer and round setup; they do not prove the foreign memory events have Rust's required atomic semantics for every execution.

The eight native leaf instruction sequences match the eight compiler mappings above. [The exact extracted assembly](evidence/concurrent-leaves-exact.s) retains their original text and extraction hash. The entire native assembly also contains Rust thread/allocation/barrier machinery. Those additional events and scheduling are not included in the two-thread litmus. Comparison concerns the selected leaf outcomes with the boundary protocol, not equality of complete event graphs.

| Native case | Corresponding model input | Counts `[00,01,10,11]` in 10,000 rounds |
| --- | --- | --- |
| MP-relaxed | MP-r0-a0 | `[4957,0,0,5043]` |
| MP-release-acquire | MP-r1-p1 | `[4947,0,0,5053]` |
| SB-relaxed | SB | `[0,4960,5040,0]` |
| SB-release-acquire | SB-STLR-LDAPR | `[0,5032,4968,0]` |
| SB-seqcst | SB-STLR-LDAR | `[0,5007,4993,0]` |
| SB-fence | SB-dmb | `[0,4936,5064,0]` |

All 60,000 rounds are accounted for; the captured process exited zero with empty stderr. MP indexes mean `(flag,data)`; SB indexes mean `(thread0 read,thread1 read)`. All nonzero histogram entries belong to the corresponding herd state set. MP's weak `10` and SB's weak `00` entries are all zero. Absence in a bounded run does not show impossibility. Barrier coordination, thread scheduling and this host can prevent or make weak behavior rare. There is no hardware observation of the distinction between the permitted-target SB variants and the forbidden-target variants in these data.

### Incorrect effect annotations change the optimizer's permitted observations

Basis: normative contract + source + compiler execution; **no execution of the incorrect controls**.

[annotation_controls.rs](evidence/annotation_controls.rs) first stores 7 through `&mut u32`, uses inline assembly to store 9 to the same pointer, then returns a Rust load. The complete contract omits `nomem`/`readonly`; it retains the subsequent LLVM load and actual `ldr w0,[x0]`. The two incorrect contracts still emit the assembly `str`, but both return `mov w0,#7`, with `ret i32 7` in [LLVM IR](evidence/annotation_controls.ll). In the IR, `nomem` omits the memory clobber and has an inaccessible-memory call effect; `readonly` keeps the clobber but marks the call read-only for accessible memory. The complete call has the unconstrained memory clobber. The selected reload difference therefore appears in both IR and final assembly.

The pinned [Rust Reference option rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#supported-options) prohibit externally accessible memory accesses for `nomem`, writes for `readonly`, and synchronization for either option. The corresponding exact rule identifiers in the preserved source are `asm.options.supported-options-nomem` and `asm.options.supported-options-readonly`, lines 1104–1105 and 1150–1151. The [assembly memory rule](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#rules-for-inline-assembly), `asm.rules.mem-same-as-ffi` at lines 1338–1342, connects accessible locations to the FFI boundary. These controls violate their declared contract if executed; they were emitted only as `.ll` and `.s`, never linked or called. The result is evidence that effects matter to optimization, not a runtime counterexample to a sound Rust program or a general optimizer theorem.

## Boundaries

- **Unestablished stronger claim (E39):** no proof relates these Rust operations or raw external assembly accesses to LLVM/compiler events and then to this hardware model. No universal complete-wrapper, mixed-width/overlap, byte-range race, RMW/failure-ordering or fence refinement theorem is supplied. The source-to-source instruction correspondence and finite state comparisons do not discharge those premises.
- **Not examined here:** mixed atomic/non-atomic sizes, other architectures, other memory types/shareability configurations, faulting accesses, unaligned locations, speculative or side-channel behavior, and RCpc transitive-publication patterns beyond these two-thread inputs. These are outside this selected experiment, not claimed to be unsupported by herd.
- **Known limit of the observation:** a model-permitted weak outcome was never actually seen. No probability, stress coverage, graph-isomorphism or completeness claim follows from the histograms. The model's enumeration of final-register states is not measurement of hardware executions.
- **Trusted boundary:** valid live pointer setup is inspected, but hardware single-copy/ordering behavior and the raw FFI interface are not a machine-checked Rust atomic-memory adequacy proof. Compiler diagnostics did not verify the effect annotations. The incorrect controls were never executed.
- **Provenance limit:** herd's version string says `exported`, rather than embedding the commit. The pinned archive inventory, checked container copy, recorded command, successful-build integration note and executable hash bind the selected experiment. The build integration note is a later parent transcription of the actual tool session, not an original subprocess-capture JSON. Tool identities and host label were refreshed after the run; their receipts are identified as such.

## Evidence

All preserved experiment evidence was acquired on 2026-10-14. This reporting task only inspected, hashed and projected existing files; it did not rerun herd, compile, invoke Docker or execute native subjects.

- [projection-receipts.json](projection-receipts.json) records each acquired file's original and public hash/length and exact replacement counts. Tool/container display prefixes are replaced with portable labels. Original captured hash fields remain hashes of the original streams; they are not silently rewritten to public-stream hashes. Sources, litmus inputs, model files, compiler instructions and native output histograms are unchanged. The complete `concurrent_assembly.s` has **two `.asciz` path strings changed**, so its public whole-file hash differs; native instructions and the separately extracted leaf text are unchanged. The executable is omitted; its original hash `0e0192997852c3a7816ac52bc4ac9b3e61e5fdbf2887ab9ece4a950396c2ac83` was checked by reading the file, without executing it.
- [source-inventory-audit.json](source-inventory-audit.json) records all 6,580 local source hashes matching [the original full inventory](evidence/herd-source.sha256), SHA-256 `fe98c51b56b0ec4db9b794516b0eb2982cdc72ed56f38c683650794e19af84b6`. The actual container-side verification printed 6,580 `OK` lines. Fifteen CAT files preserve the transitive textual includes of `aarch64.cat`, plus interpreter `stdlib.cat` support. Selected instruction/event source, upstream license, version and build requirements are retained under [upstream/herdtools7](upstream/herdtools7/VERSION.txt); the whole checkout and build cache are omitted.
- Primary model source: [aarch64.cat](https://github.com/herd/herdtools7/blob/9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34/herd/libdir/aarch64.cat), [aarch64hwreqs.cat](https://github.com/herd/herdtools7/blob/9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34/herd/libdir/aarch64hwreqs.cat), [AArch64Sem.ml](https://github.com/herd/herdtools7/blob/9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34/herd/AArch64Sem.ml). These are the precise selected model and interpreter source, not a claim that every Arm specification configuration has been proved equivalent to them.
- [herd version](evidence/runs/herd-version.stdout), [binary hash](evidence/runs/herd-binary-hash.stdout), [successful-build parent note](evidence/build/herd-verified-build-parent-note.json), and [container resource identity](evidence/environment/container-resource.json) retain executable/build/environment provenance. The source archive hash in the note is `b109f81e61e26f8bf74d6343b568ccc747cc0c40c41b8084103d557b3ab8a9fb`. Separate earlier [mounted-source permission diagnostics](evidence/build/prior-diagnostics/herd-build.stderr) and [missing-Version.ml diagnostics](evidence/build/prior-diagnostics/herd-container-build.stderr) are retained; they are not accepted build evidence. The parent note records completing the source copy and generating Version.ml before the successful fresh `_build_verified` build. Dependency-install output is retained as provenance only; the reporting task performed no installation.
- [Rust version](evidence/runs/rustc-version.stdout), [default cfg](evidence/runs/rustc-cfg.stdout), and [May 1 executable/driver identities](evidence/may1-tool-identities.json) identify the compiler actually used. The `rustc` launcher hash is `c456b0855e2d148f5d517952f2cb684bf0379d125d2c89b5ca16d46e56c80988`; the driver hash is `dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d`.
- [Native invocation](evidence/runs/concurrent-native.json), [native stdout](evidence/runs/concurrent-native.stdout), [host OS](evidence/runs/host-os.stdout), [process architecture](evidence/runs/host-process-arch.stdout) and [CPU receipt](evidence/runs/host-cpu-query.stdout) bind the observations. [coverage.json](coverage.json) keeps E38's experiment assessment separate from E39's unestablished theorem.
- [support/validate.py](support/validate.py) performs a static evidence audit only: hashes, actual instruction sequences, model state membership, native count totals, original-output receipts, and the compiled-only effect differences. Its recorded successful result is [static-validation.json](static-validation.json). It does not establish correctness of herd, rustc, the hardware or Rust/FFI atomic compatibility.

## Revalidation

First run `python3 support/validate.py` in this package. This reads only preserved files and can detect a changed input, projection, instruction sequence or claimed outcome. Verify the package manifest separately.

For an actual replay, use a fresh owned scratch copy, the exact recorded herd executable/source/model revision and the exact May 1 compiler. [support/replay-commands.json](support/replay-commands.json) gives portable argv and working-directory labels corresponding to the preserved commands. Rebuild herd only under separately authorized tooling; retain the full copied-source inventory and binary identity. Compare all ten model state sets and positive/negative target counts, not just exit status. Preserve the DMB deprecation flag. Compare all eight emitted atomic function bodies and the three annotation-control bodies/IR. **The incorrect annotation controls must remain compilation-only.**

Native replay requires the selected AArch64 platform, runtime RCpc support, valid live aligned cells and the barrier protocol. Preserve each histogram and host/configuration identity; expect counts and scheduling to vary. A replay need not observe a weak outcome to agree with this report, and absence must never be relabeled as a model prohibition. Any compiler, model, platform, access width or wrapper change requires re-examining the relevant mapping and boundary premises; the E39 proof remains separate even if all finite probes pass.
