# Seven-Release `rustc` `Runtime(PostCleanup)` MIR Schema Drift, Causal Compiler Commits, and Capture Compatibility (`1.93.1`–`1.102.0-nightly`)

## Summary

Longitudinal compilation of four Rust libraries—a `30`-function feature probe (`37` MIR bodies) plus three pinned zero-dependency crates (`ryu 1.0.23`, `itoa 1.0.19`, `memchr 2.8.3`; **`782` bodies per release**, `28 / 28` clean `rc=0` runs)—across **seven live `rustc` toolchains** spanning nine months (`1.93.1`, `1.94.0`, `1.96.0`, `1.99.0`, `1.99.1`, `1.100.0`, `1.102.0-nightly`; `2026-02-11` to `2026-11-11`), combined with `compiler/rustc_middle/src/mir/syntax.rs` AST diffing across nine `rust-lang/rust` commits and direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, establishes five primary-source findings that refute naive cross-release MIR compatibility claims:

1. **Cumulative Nine-Month `Runtime(PostCleanup)` MIR Drift Reaches `36.36%` Normalized (`33.39%` True AST/Type/Codegen) in `memchr 2.8.3`, While Patch Releases Preserve `0.00%` Drift:**
   - Across `1.93.1 -> 1.102.0-nightly`, **`232 / 638` (`36.36%`)** of common `memchr` bodies change after span, disambiguator, and `allocN` normalization (plus `1` renamed `Eq` method and `2` eliminated promoted `Debug` bodies). Stripping purely pretty-printer/debug-scope diffs (`19` bodies) leaves **`213 / 638` (`33.39%`)** with true operational AST, stdlib-type, or macro-codegen mutations. Over the same span, `feature_probe` changes **`7 / 37` (`18.92%`)**, `itoa 1.0.19` changes **`1 / 59` (`1.69%`)**, and pure arithmetic/table code in `ryu 1.0.23` exhibits **`0 / 45` (`0.00%`)** normalized drift.
   - Across stable patch release `1.99.0 -> 1.99.1`, normalized drift is **`0 / 782` (`0.00%`)** across all four corpora (`100%` of `ryu`'s `4 / 45` textual diffs are metadata-hash noise). Every single diff across `4,689` pairwise body comparisons maps to verified `rust-lang/rust` commits (`0` unclassified).
2. **Metadata Hashes, Monotonic `AllocId`s, Pretty-Printers, and Debug Scopes Account for `43%–100%` of Textual Drift on Individual Transitions:**
   - `CrateDisambiguator` 4-hex hashes rotate on **every release including patch releases** (`ryu[0a04] -> ryu[0867] -> ryu[d41f] -> ryu[2f3d] -> ryu[0d70] -> ryu[c6b2] -> ryu[58e3]`), driving `4 / 45` (`8.89%`) false drift in `ryu` that collapses to **`0.00%`** once normalized.
   - Session-global monotonic `AllocId` counters (`alloc92 -> alloc107 -> alloc117` in `itoa.DECIMAL_PAIRS`) drive **`13 / 59` (`22.03%`)** false drift in `itoa` (`1.93.1 -> 1.96.0`), **`70 / 640` (`10.94%`)** in `memchr` (`1.94.0 -> 1.96.0`), and **`29 / 639` (`4.54%`)** in `memchr` (`1.100.0 -> nightly`).
   - Pretty-printer and debug-scope changes—`#[doc(hidden)]` trimmed paths (`2df2c72d7ae36d11313ed730960030cc5af9fb21`), RFC 2229 closure debug names (`8c4486bc034869f27c4218c3d0037dbf2ed484e9`), and empty `?` `source_scopes` pruning (`e1663b69bf6e0f5b69c3490b7f66cb8a2113bb99`)—account for `80.17%` (`93 / 116`) of `memchr` `1.94.0 -> 1.96.0` textual diffs, `66.67%` (`28 / 42`) of `1.99.1 -> 1.100.0`, and `42.57%` (`43 / 101`) of `1.100.0 -> nightly`, demonstrating why direct `TyCtxt` capture beats textual `.mir` parsing.
3. **`rustc_middle::mir::syntax` Undergoes Nine Structural Mutations Across Seven Releases, With Two Directly Reshaping Live Production MIR:**
   - Six of ten core AST enums mutate across `1.93.1 -> 1.102.0-nightly`: `-Rvalue::NullaryOp` and `+Operand::RuntimeChecks` (`1.93.1 -> 1.94.0`); `-Rvalue::ShallowInitBox` (`1.94.0 -> 1.96.0`); `-StatementKind::Retag`, `Rvalue::Use(Operand)` -> `Rvalue::Use(Operand, WithRetag)`, `+Rvalue::Reborrow`, `+AssertKind::NullReferenceConstructed`, and `+CastKind::BoxDerefTransmute` (`1.96.0 -> 1.99.0`); `+ProjectionElem::PhantomDeref` (`1.99.1 -> 1.100.0`); and `TerminatorKind::Goto { loop_hint_attrs }` (`1.100.0 -> 1.102.0-nightly`).
   - In live `Runtime(PostCleanup)` MIR, `Rvalue::Use(_, WithRetag)` (`e402c1edf047a23b0cfef40c6097d1caa294050b`, PR `#154341`) introduces `no_retag copy` on **`124 / 641` (`19.34%`)** of `memchr` bodies and `2 / 37` (`5.41%`) of `feature_probe`, while `CastKind::BoxDerefTransmute` (`fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f`) rewrites all `5` `Box<T>` deref bodies in `memchr`.
4. **Stdlib Type Refactors, Never-Type Stabilization, and Built-In Derive Codegen Drive Large MIR Drift Independent of `syntax.rs`:**
   - `AtomicU* -> Atomic<T>` (`fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`, `1.94.0 -> 1.96.0`) hits `21 / 640` `memchr` and `5 / 37` `feature_probe` bodies. Never-type stabilization (`e7769602aca3770e8d8ea55716becb22e839a579`, PR `#155499`, plus `dd132214ed3e2415da4292fec21f564f4496baa5`, `1.99.1 -> 1.100.0`) flips Edition 2021 diverging statements to `!` (collapsing `let _17: (); let mut _18: !;` to `let _17: !;` in `itoa.{impl#3}-format`) and aliases `Infallible = !` (rewriting `ControlFlow<Option<Infallible>, T>` to `ControlFlow<Option<!>, T>` across `14 / 641` `memchr` bodies). `Box<T>.0` changes from `Unique<T>` to `BoxRaw<T>` (`5d260fd3da7b0165d6365adab12746bfc389d913`, `5 / 639` `memchr`), and `#[derive(Debug)]` concatenated field strings (`4719edece749ef683e8971e6e08fd643744a82d0` / `0ccb82fd1f0d9eb109c35cec2a760d48b8e6fa22`, PR `#164726`) reshape **`53 / 639` (`8.29%`)** of `memchr` bodies and eliminate `2` promoted constants.
5. **Direct Audit of `joshlf/anneal@c131b320e` Reveals an Internal Five-Month Compiler-Pin Skew (`f8a08b688` vs. `8144389c`):**
   - `trusted/rustc-capture/src/driver.rs:25` is an analysis-callback shell pinned to `1.98.0-nightly (f8a08b688 2026-05-30)` (no MIR emission yet), whereas `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` pins `8144389c` (`2026-10-20`). **Four `syntax.rs` mutations** separate those two pins (`+AssertKind::NullReferenceConstructed`, `+CastKind::BoxDerefTransmute`, `+ProjectionElem::PhantomDeref`, `Goto { loop_hint_attrs }`); synchronizing both surfaces to one pinned compiler commit is mandatory before wiring capture emission.

## Applicability

Findings apply to concrete pinned upstream revisions observed on `2026-11-20` on `x86_64-unknown-linux-gnu`:

- **Measured `rustc` toolchains (`7` live official `rustup` installations, `[real measurement]`):**
  `1.93.1` (`01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`, `2026-02-11`, `LLVM 21.1.8`), `1.94.0` (`4a4ef493e3a1488c6e321570238084b38948f6db`, `2026-03-02`, `LLVM 21.1.8`), `1.96.0` (`ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96`, `2026-05-25`, `LLVM 22.1.2`), `1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `2026-09-28`, `LLVM 23.1.1`), `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `2026-10-13`, `LLVM 23.1.1`), `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`, `2026-11-09`, `LLVM 23.1.5`), and `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, `LLVM 23.1.5`).
- **Additional `rust-lang/rust` AST source pins (`2` commits cited by `joshlf/anneal`, `[published source]`):**
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`, `2026-05-30`, pinned in `trusted/rustc-capture/src/driver.rs:25`) and `8144389c895da997dbdecaa635e41d6a50be6ffd` (`2026-10-20` nightly, cited across `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`).
- **Verification TCB (`[published source]`):** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/{main.rs,driver.rs}`, `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`).
- **Empirical corpora (`4` zero-dependency libraries, `782` post-cleanup bodies per release on `1.93.1–1.100.0` and `780` on `1.102.0-nightly`, `[real measurement]`):**
  1. `feature_probe` (`37` bodies, `--edition=2021`, preserved verbatim in `support/mir_seven_release_drift_probe.py`): `30` targeted Rust language/library functions covering checked/wrapping/div/shift ops, slice indexing/subslice patterns, `get_unchecked`/`NonNull`/`ptr::read`/`copy_nonoverlapping`, `unreachable_unchecked`, `f64::to_bits`, `#[repr(u8)]` enums, `Drop`, `&raw const`/`&raw mut`, `offset_of!`/`size_of`/`align_of`, `const {}`, array repeat, `MaybeUninit`, `dyn Trait`, closures, `AtomicU8`/`AtomicU32`/`AtomicU64`/`fence`/`compiler_fence`, and `Option<NonNull<u8>>`.
  2. `ryu 1.0.23` (`dtolnay/ryu@f0b52bb194befe6fd242154f2182fafd43a819b8`, `45` bodies, `--edition=2018`).
  3. `itoa 1.0.19` (`dtolnay/itoa@9339ca99a43c550b5ee36e2afe524d1c90413461`, `59` bodies, `--edition=2021`).
  4. `memchr 2.8.3` (`BurntSushi/memchr@5fdb40c054e1fff359a2f7bdf7f87a13b34b465d`, `641`/`639` bodies, `--edition=2021 --cfg feature="alloc" --cfg feature="std"`).
- **Invocation and relationship:** Every run invokes `RUSTC_BOOTSTRAP=1 rustup run <tc> rustc --crate-type=lib --crate-name=<name> <flags> -C opt-level=2 -Z dump-mir=all -Z dump-mir-dir=<tmp> -o <tmp>/lib<name>.rlib <lib.rs>` and extracts `*.3-2-000.runtime-post-cleanup.after.mir` (`MirPhase::Runtime(RuntimePhase::PostCleanup)`, post-drop-elaboration and pre-MIR-optimization/inlining). Cross-release behavior is measured directly on the seven toolchains and mapped onto `joshlf/anneal@c131b320e`; intermediate unmeasured releases (`1.95.x`, `1.97.x`, `1.98.x`) are not interpolated.

## Findings

### 1. Seven-Release `Runtime(PostCleanup)` MIR Drift Census Across Four Corpora

`Basis: execution (support/mir_seven_release_drift_probe.py, support/mir_seven_release_drift_summary.json, 28 live rustc -Z dump-mir=all runs)`

Across all `28` compilations, the post-cleanup dump identifier remained invariant: **`3-2-000.runtime-post-cleanup.after`** (`100%` of bodies on every toolchain). Total intermediate `.mir` dump volume under `-Z dump-mir=all` grew across `1.93.1 -> 1.99.0` (`memchr`: `67,138 -> 68,318 -> 69,498 -> 69,536` files; `feature_probe`: `3,914 -> 3,982 -> 4,050 -> 4,056`) before holding constant through `1.100.0` and dropping to `69,462` on `1.102.0-nightly` after `2` promoted `Debug` bodies disappeared.

#### Multi-Layer Drift Matrix (`6` Adjacent Transitions + Cumulative `1.93.1 -> 1.102.0-nightly`)

Normalization layers: **Span** strips `// ...` comments (equal to Raw on all `28` runs because source paths/spans are fixed); **+Disamb** replaces `crate[xxxx]` with `crate[DISAMB]`; **+Alloc** replaces `\balloc\d+\b` with `allocN`; **Sem** combines Span + Disamb + Alloc.

| Corpus (`Bodies`) | Transition | Common (`-`/`+`) | Span Chg (`%`) | +Disamb | +Alloc | Sem Chg (`%`) | Verified Causal Categories (`100%` Accounted) |
| :--- | :--- | :---: | ---: | ---: | ---: | ---: | :--- |
| **`feature_probe`** (`37`) | `1.93.1 -> 1.94.0` | `37` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | `1.94.0 -> 1.96.0` | `37` (`0`/`0`) | `5` (`13.51%`) | `5` | `5` | **`5` (`13.51%`)** | `5` `generic_atomic` (`AtomicU* -> Atomic<T>`) |
| | `1.96.0 -> 1.99.0` | `37` (`0`/`0`) | `2` (`5.41%`) | `2` | `2` | **`2` (`5.41%`)** | `2` `no_retag_copy` (closure + `Drop`) |
| | `1.99.0 -> 1.99.1` | `37` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | `1.99.1 -> 1.100.0` | `37` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | `1.100.0 -> nightly` | `37` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | **Cumul `1.93.1 -> nightly`** | `37` (`0`/`0`) | `7` (`18.92%`) | `7` | `7` | **`7` (`18.92%`)** | `5` `generic_atomic`, `2` `no_retag_copy` |
| **`ryu 1.0.23`** (`45`) | Each of `6` transitions | `45` (`0`/`0`) | `4` (`8.89%`) | **`0`** | `4` | **`0` (`0.00%`)** | `100%` `ryu[xxxx]` hash churn (`0a04->0867->d41f->2f3d->0d70->c6b2->58e3`) |
| | **Cumul `1.93.1 -> nightly`** | `45` (`0`/`0`) | `4` (`8.89%`) | **`0`** | `4` | **`0` (`0.00%`)** | `0` semantic changes across `9` months |
| **`itoa 1.0.19`** (`59`) | `1.93.1 -> 1.94.0` | `59` (`0`/`0`) | `13` (`22.03%`) | `13` | **`0`** | **`0` (`0.00%`)** | `100%` `alloc92 -> alloc107` ID churn |
| | `1.94.0 -> 1.96.0` | `59` (`0`/`0`) | `13` (`22.03%`) | `13` | **`0`** | **`0` (`0.00%`)** | `100%` `alloc107 -> alloc117` ID churn |
| | `1.96.0 -> 1.99.0` / `1.99.1` | `59` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | `1.99.1 -> 1.100.0` | `59` (`0`/`0`) | `1` (`1.69%`) | `1` | `1` | **`1` (`1.69%`)** | `1` `never_type_local_elision` (`itoa.{impl#3}-format`) |
| | `1.100.0 -> nightly` | `59` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | **Cumul `1.93.1 -> nightly`** | `59` (`0`/`0`) | `14` (`23.73%`) | `14` | `1` | **`1` (`1.69%`)** | `1` `never_type_local_elision` (`13` pure `allocN`) |
| **`memchr 2.8.3`** (`641`->`639`) | `1.93.1 -> 1.94.0` | `641` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | `1.94.0 -> 1.96.0` | `640` (`-1`/`+1`) | `116` (`18.12%`) | `116` | `46` | **`46` (`7.19%`)** | `21` `generic_atomic`, `16` `assert_failed` + `13` `doc_hidden` paths (`6` overlap atomics), `2` `PtrToPtr` temp, `+` `Eq` rename; `70` pure `allocN` |
| | `1.96.0 -> 1.99.0` | `641` (`0`/`0`) | `125` (`19.50%`) | `125` | `125` | **`125` (`19.50%`)** | `124` `no_retag_copy` (`5` also gain `BoxDerefTransmute`), `1` dead `discriminant()` elision |
| | `1.99.0 -> 1.99.1` | `641` (`0`/`0`) | `0` (`0.00%`) | `0` | `0` | **`0` (`0.00%`)** | — |
| | `1.99.1 -> 1.100.0` | `641` (`0`/`0`) | `42` (`6.55%`) | `42` | `42` | **`42` (`6.55%`)** | `28` closure upvar debug name (`self -> self__searcher`), `14` `Option<!>` `?` residual |
| | `1.100.0 -> nightly` | `639` (`-2`/`0`) | `101` (`15.81%`) | `101` | `72` | **`72` (`11.27%`)** | `53` `derive(Debug)` concat names (`-2` promoted bodies), `14` empty `?` scope elision, `5` `BoxRaw<T>`; `29` pure `allocN` |
| | **Cumul `1.93.1 -> nightly`** | `638` (`-3`/`+1`) | `245` (`38.40%`) | `245` | `232` | **`232` (`36.36%`)** | **`213` (`33.39%`) true AST/type/codegen + `19` (`2.98%`) pretty-print-only + `13` (`2.04%`) pure `allocN`** |

#### Root-Cause Resolution of `memchr 2.8.3` `rc=1` on `1.100.0` and `1.102.0-nightly`

`Basis: execution (isolated rustc 1.100.0 and 1.102.0-nightly runs of memchr 2.8.3 with/without RUSTC_BOOTSTRAP=1 and -Z dump-mir=all, plus df -i /tmp)`

An uncleaned multi-release harness retaining all seven toolchains' `-Z dump-mir=all` directories in one `/tmp` workspace fails with `rc=1` partway through `memchr` on `1.100.0` (`218 / 641` bodies dumped) and immediately on `1.102.0-nightly` (`0` bodies), printing only two deprecation warnings (`core::u8::MAX` at `src/arch/all/packedpair/mod.rs:179`, `core::u32::MAX` at `src/memmem/searcher.rs:916`). Direct isolation refutes any compiler or edition regression:
- Standalone `rustc` compilation of `memchr 2.8.3` (`--edition=2021 --cfg feature="alloc" --cfg feature="std" -C opt-level=2`) exits **`rc=0`** on both `1.100.0` and `1.102.0-nightly` with and without `RUSTC_BOOTSTRAP=1` and with `-Z dump-mir=all` (`69,536` and `69,462` `.mir` files).
- **Actual cause (tmpfs inode exhaustion):** Retaining five `memchr` dumps (`344,026` files) plus `ryu` (`32,800`), `itoa` (`32,294`), and `feature_probe` (`28,170`) accumulates **`437,290` files** in `/tmp` before `1.100.0` runs, exhausting `/tmp`'s `1,048,576`-inode tmpfs budget when concurrent processes already occupy `~400k+` inodes. Removing each toolchain's `mir_dir` immediately after reading `runtime-post-cleanup.after.mir` caps peak occupancy at `69,536` files (`~7×` lower) and yields `28 / 28` clean `rc=0` runs, exposing the full `memchr` `1.99.1 -> 1.100.0` (`42 / 641`) and `1.100.0 -> 1.102.0-nightly` (`72 / 639`, `-2` promoted) transitions.

### 2. Quantitative Separation of False Textual Noise From True Representation Drift

`Basis: execution + source (support/mir_seven_release_drift_summary.json, rust-lang/rust commits 2df2c72d7ae36d11313ed730960030cc5af9fb21, 8c4486bc034869f27c4218c3d0037dbf2ed484e9, e1663b69bf6e0f5b69c3490b7f66cb8a2113bb99)`

Four strictly non-operational noise mechanisms dominate raw textual `.mir` diffs:

1. **`CrateDisambiguator` 4-Hex Hash Rotation (Every Release, Including Patches):** `rustc` hashes compiler metadata into `DefId` static references, rotating `ryu`'s `DIGIT_TABLE` tag on all six transitions (`ryu[0a04] -> ryu[0867] -> ryu[d41f] -> ryu[2f3d] -> ryu[0d70] -> ryu[c6b2] -> ryu[58e3]`):
   ```diff
   --- 1.93.1:ryu.pretty-exponent-write_exponent2
   +++ 1.94.0:ryu.pretty-exponent-write_exponent2
   -        _22 = const <static(DefId(0:101 ~ ryu[0a04]::digit_table::DIGIT_TABLE))>;
   +        _22 = const <static(DefId(0:101 ~ ryu[0867]::digit_table::DIGIT_TABLE))>;
   ```
   Normalizing disambiguators drops `ryu` drift from `8.89%` (`4 / 45`) to **`0.00%` (`0 / 45`)** across all six transitions.
2. **Monotonic Global `AllocId` Counter Drift:** `rustc_const_eval` numbers `AllocId(NonZero<u64>)` monotonically across the entire session (including earlier sysroot/prelude evaluations). In `itoa`, `DECIMAL_PAIRS` shifts `alloc92 -> alloc107 -> alloc117` (`1.93.1 -> 1.94.0 -> 1.96.0`) and `itoa._` shifts `alloc71 -> alloc86 -> alloc96` with identical payload bytes:
   ```diff
   --- 1.93.1:itoa.DECIMAL_PAIRS
   +++ 1.94.0:itoa.DECIMAL_PAIRS
   -alloc92 (size: 200, align: 1) {
   +alloc107 (size: 200, align: 1) {
        0x00 │ 30 30 30 31 30 32 30 33 30 34 30 35 30 36 30 37 │ 0001020304050607
   ```
   Content-addressing `AllocId`s eliminates `13 / 59` (`22.03%`) false diffs in `itoa`, `70 / 640` (`10.94%`) in `memchr` (`1.94.0 -> 1.96.0`), and `29 / 639` (`4.54%`) in `memchr` (`1.100.0 -> nightly`, triggered when `2` promoted `Debug` statics were removed, shifting `alloc41 -> alloc39` and `alloc40 -> alloc38`).
3. **Pretty-Printer-Only `DefPath` and Closure Capture Name Changes (`0` AST Change):**
   - **`2df2c72d7ae36d11313ed730960030cc5af9fb21`** (`2026-01-19`, rollup `#151381`, `compiler/rustc_middle/src/ty/print/pretty.rs`: `"Ignore #[doc(hidden)] items when computing trimmed paths"`): Absent in `1.94.0`, present in `1.96.0`. Because `core::panicking::assert_failed` is `#[doc(hidden)]`, `1.96.0+` stops trimming it (`assert_failed` -> `core::panicking::assert_failed`, `16` `memchr` bodies) while trimming `memchr::memchr`/`memchr::memrchr` to bare `memchr`/`memrchr` (`13` bodies, `6` overlapping `generic_atomic`). Underlying callee `DefId`s are completely unchanged.
   - **`8c4486bc034869f27c4218c3d0037dbf2ed484e9`** (`2026-09-01`, PR `#162154`, merge `56b18c11458769ae086ce2ae6c7da36a60801843`, `compiler/rustc_middle/src/mir/pretty.rs:1256-1285`: `"fix[154166]: closure debug capture print"`): Switched `Debug for Rvalue::Aggregate(Closure | Coroutine)` from `tcx.upvars_mentioned` to `tcx.closure_captures` (`capture.to_symbol()`):
     ```diff
     --- 1.99.1:memchr.arch-all-memchr-{impl#1}-count
     +++ 1.100.0:memchr.arch-all-memchr-{impl#1}-count
     -        _3 = {closure@<SRC_ROOT>/src/arch/all/memchr.rs:323:23: 323:29} { self: move _4 };
     +        _3 = {closure@<SRC_ROOT>/src/arch/all/memchr.rs:323:23: 323:29} { self__searcher: move _4 };
     ```
     Affects **`28 / 641` (`4.37%`)** of `memchr` bodies (`66.67%` of all `1.99.1 -> 1.100.0` `memchr` diffs) with zero AST or closure-layout change.
4. **Debug `SourceScope` Pruning (`Body.source_scopes` Only):**
   - **`e1663b69bf6e0f5b69c3490b7f66cb8a2113bb99`** (`2026-10-19`, PR `#164122`, merge `0a4720d4b4809660670b050d97df98934f970c07`, `compiler/rustc_ast_lowering/src/expr.rs`: `"Don't emit allow attributes in try/contract desugaring"`): Eliminates empty `scope N {}` entries across **`14 / 639` (`2.19%`)** of `?`-using `memchr` bodies in `1.100.0 -> 1.102.0-nightly` with zero operational effect.

**Exact disjoint accounting (`memchr 2.8.3`):** On individual releases, pure cosmetic/debug noise accounts for **`80.17%` (`93 / 116`)** of `1.94.0 -> 1.96.0` span-stripped diffs (`70` `allocN` + `23` trimmed-path-only), **`66.67%` (`28 / 42`)** of `1.99.1 -> 1.100.0`, and **`42.57%` (`43 / 101`)** of `1.100.0 -> nightly` (`29` `allocN` + `14` empty-scope-only). Cumulatively across `1.93.1 -> nightly`, because `no_retag_copy` and `option_try_residual_never` overlap many of those same bodies, **`32 / 245`** (`13` pure `allocN` + `19` pure pretty-print) are strictly cosmetic while **`213 / 638` (`33.39%`)** carry genuine operational AST, stdlib-type, or derive-codegen changes.

### 3. Exhaustive `rustc_middle::mir::syntax` AST Evolution Across Nine Pinned Revisions (`1.93.1`–`1.102.0-nightly`)

`Basis: source (programmatic extraction of 10 core MIR AST enums from compiler/rustc_middle/src/mir/syntax.rs across all 9 pinned rust-lang/rust commits)`

While `BinOp` (`26`), `UnOp` (`3`), and `NonDivergingIntrinsic` (`2`) remained invariant across all nine revisions, the remaining seven enums underwent **nine structural schema changes**:

| Enum (`syntax.rs`) | Transition Window | Variant / Field Mutation | Verified Causal `rust-lang/rust` Commit & PR | Observed in Live 4-Corpus MIR? |
| :--- | :--- | :--- | :--- | :--- |
| **`Rvalue`** (`14->13`) | `1.93.1 -> 1.94.0` | `- NullaryOp(NullOp)` | `1a227bd47ff200975f4afb287ec725861ab8b87a` (PR `#148766`, `2025-12-14`) | No (uninlined `libcore` calls) |
| **`Operand`** (`3->4`) | `1.93.1 -> 1.94.0` | `+ RuntimeChecks(RuntimeChecks)` | `6319bee585561a078de4a0f8d07d567ce69cf12c` (PR `#148766`, `2025-12-14`) | No (lives in `libcore` pre-inlining) |
| **`Rvalue`** (`13->12`) | `1.94.0 -> 1.96.0` | `- ShallowInitBox(Operand, Ty)` | `6d4b1b38e76c0858c8e98f89afa37535261749ca` (PR `#152758`, `2026-02-17`) | No |
| **`StatementKind`** (`13->12`) | `1.96.0 -> 1.98-capture` (`1.99.0`) | `- Retag(RetagKind, Box<Place>)` | `e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`, merge `20de910db49d3476ccf49ea79a4b22e2b5dface0`, `2026-05-02`) | Paired with `WithRetag` below |
| **`Rvalue`** (`12->13`) | `1.96.0 -> 1.98-capture` (`1.99.0`) | `Use(Operand)` -> `Use(Operand, WithRetag)` | `e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`, `2026-05-02`) | **YES: `124 / 641` `memchr`, `2 / 37` `feature_probe`** |
| **`Rvalue`** (`12->13`) | `1.96.0 -> 1.98-capture` (`1.99.0`) | `+ Reborrow(Ty, Mutability, Place)` | `2d88ee87ddaa584a19e438528f60f825f735076a` (rollup `#156290`, `2026-05-07`) | No (unstable feature) |
| **`AssertKind`** (`11->12`) | `1.98-capture -> 1.99.0` | `+ NullReferenceConstructed` | `1a982425b6699f2b26552c6b44cc979a3d84543b` (PR `#158796`, `2026-07-05`) | No (emitted in `libcore`/UB checks) |
| **`CastKind`** (`11->12`) | `1.98-capture -> 1.99.0` | `+ BoxDerefTransmute` | `fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f` (rollup `#160339`, `2026-08-01`) | **YES: `5 / 641` `memchr` (`Box<T>` derefs)** |
| **`ProjectionElem`** (`8->9`) | `1.99.1 -> 1.100.0` (and `8144389c`) | `+ PhantomDeref` | `5686e563774cd9e8bfba79d3ab1167fe198e9e78` (PR `#159103`, `2026-08-27`) | No (unstable `reborrow`) |
| **`TerminatorKind`** (`15->15`) | `1.100.0 -> nightly` (and `8144389c`) | `Goto { target }` -> `Goto { target, loop_hint_attrs }` | `ec45ecffeee8ba13e42a7f45b6cdad3155ebd146` (PR `#163931`, `2026-10-07`) | Struct-field delta (`0` textual diff when empty) |

*Why `f07_ub_checks_unchecked` showed `0` diffs across `1.93.1 -> 1.94.0`:* Because `Runtime(PostCleanup)` precedes MIR inlining, `f07` retains direct calls to `core::slice::<impl [u32]>::get_unchecked`, `NonNull::new_unchecked`, and `std::ptr::read`; `Operand::RuntimeChecks(UbChecks)` resides inside `libcore`'s bodies rather than caller bodies.

### 4. Real-World Causal Taxonomy: Six Non-Noise Drift Classes in Production MIR

`Basis: execution + source (support/mir_seven_release_drift_summary.json, THIR/built-MIR diffs, and verified rust-lang/rust commits)`

#### 4.1 Implicit Retagging and `no_retag copy` (`1.96.0 -> 1.99.0`, `19.34%` of `memchr`, `5.41%` of `feature_probe`)

Commit **`e402c1edf047a23b0cfef40c6097d1caa294050b`** (PR `#154341`, merge `20de910db49d3476ccf49ea79a4b22e2b5dface0`) deleted `StatementKind::Retag`, made `StatementKind::Assign` implicitly retag references/boxes inside `Rvalue::Use(op, WithRetag::Yes)`, and marked non-retagging projected loads (closure captures, `Drop::drop` fields, struct reference projections) as **`Rvalue::Use(op, WithRetag::No)`**, printed by `pretty.rs` as `no_retag copy`:
```diff
--- 1.96.0:feature_probe.{impl#0}-drop
+++ 1.99.0:feature_probe.{impl#0}-drop
-        _5 = copy ((*_1).0: &mut u32);
+        _5 = no_retag copy ((*_1).0: &mut u32);
         _3 = copy (*_5);
```
```diff
--- 1.96.0:memchr.arch-all-memchr-{impl#0}-find-{closure#0}
+++ 1.99.0:memchr.arch-all-memchr-{impl#0}-find-{closure#0}
-        _7 = copy ((*_1).0: &arch::all::memchr::One);
+        _7 = no_retag copy ((*_1).0: &arch::all::memchr::One);
         _4 = &(*_7);
```
Because `WithRetag` directly governs Stacked/Tree Borrows provenance retagging, any capture driver spanning `1.96` and `1.97+` must model `WithRetag` explicitly (never erasing it silently once references are modeled).

#### 4.2 Double Mutation of `Box<T>` Dereference Lowering (`1.96.0 -> 1.99.0` and `1.100.0 -> 1.102.0-nightly`)

Across all five `Box<T>` dereference bodies in `memchr` (`arch-all-shiftor-{impl#0}-{find,new}`, `cow-{impl#2}-as_slice`, `memmem-{impl#6}-{build_forward_with_ranker_owned,build_reverse_owned}`), the exact same Rust dereference mutated **twice** in nine months:
- **`1.93.1`–`1.96.0`:** `_7 = copy (*_4); _8 = copy ((_7.0: core::ptr::Unique<[u8]>).0: core::ptr::NonNull<[u8]>) as *const [u8] (Transmute);`
- **`1.99.0`–`1.100.0`** (`e402c1ed` `WithRetag` + **`fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f`**, rollup `#160339`, `CastKind::BoxDerefTransmute`): `_7 = no_retag copy (*_4); _8 = copy (_7.0: core::ptr::Unique<[u8]>) as *const [u8] (BoxDerefTransmute);`
- **`1.102.0-nightly`** (**`5d260fd3da7b0165d6365adab12746bfc389d913`**, PR `#162849`, merge `2d418e9411cf9b91cd43c75b827f6df920ff5799`, `"Replace Unique in Box with a (NonNull, PhantomData) wrapper"`): `_7 = no_retag copy (*_4); _8 = copy (_7.0: std::boxed::BoxRaw<[u8]>) as *const [u8] (BoxDerefTransmute);`

Verifiers pattern-matching `Box<T>`'s private field `0` (`Unique` vs. `BoxRaw`) or `CastKind::Transmute` vs. `BoxDerefTransmute` break twice across nine months.

#### 4.3 Generic Atomic Refactor (`1.94.0 -> 1.96.0`, `21 / 640` `memchr`, `5 / 37` `feature_probe`)

Commit **`fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`** (`2026-03-01`, rollup `#153304`, `library/core/src/sync/atomic.rs`: `"core: make atomic primitives type aliases of Atomic<T>"`) erased nominal `AtomicU8`/`AtomicU32`/`AtomicU64`/`AtomicUsize` structs into type aliases of generic `core::sync::atomic::Atomic<T>`:
```diff
--- 1.94.0:feature_probe.f25_atomic_load_acquire
+++ 1.96.0:feature_probe.f25_atomic_load_acquire
-fn f25_atomic_load_acquire(_1: &AtomicU64) -> u64 {
+fn f25_atomic_load_acquire(_1: &Atomic<u64>) -> u64 {
-        _0 = AtomicU64::load(move _2, move _3) -> [return: bb1, unwind continue];
+        _0 = Atomic::<u64>::load(move _2, move _3) -> [return: bb1, unwind continue];
```
Every atomic local `TyKind::Adt` and method callee `DefId` changed across all `5` atomic functions in `feature_probe` (`13.51%`) and `21` `AtomicUsize` dispatch-cache functions in `memchr` (`3.28%`).

#### 4.4 Never-Type Stabilization: Edition 2021 `!` Fallback and `Infallible = !` (`1.99.1 -> 1.100.0`)

Commit **`e7769602aca3770e8d8ea55716becb22e839a579`** (PR `#155499`, `2026-08-24`: `"stabilize never type"`) plus **`dd132214ed3e2415da4292fec21f564f4496baa5`** (`2026-09-01`, rollup `#162148`, `"Dogfood never type in std"`) drove two distinct real MIR changes in `1.100.0`:

1. **Edition 2021 diverging-statement local elision (`itoa 1.0.19`, `1 / 59` = `1.69%`):** For `if string.len() > I::MAX_STR_LEN { unsafe { hint::unreachable_unchecked() }; }` (`itoa/src/lib.rs:109–111`), differential `-Z unpretty=thir-tree` and `built.after.mir` inspection confirms that `1.99.1` fell back to `()` via a THIR `NeverToAny` coercion (`let _17: (); let mut _18: !;`), whereas `1.100.0` switched never-type fallback to `!` on all editions, removing `NeverToAny` and collapsing both `built.after.mir` and `runtime-post-cleanup.after.mir`:
   ```diff
   --- 1.99.1:itoa.{impl#3}-format
   +++ 1.100.0:itoa.{impl#3}-format
   -    let _17: ();
   -    let mut _18: !;
   +    let _17: !;
        StorageLive(_17);
   -    StorageLive(_18);
   -    _18 = unreachable_unchecked() -> unwind continue;
   +    _17 = unreachable_unchecked() -> unwind continue;
   ```
2. **`ControlFlow<Option<Infallible>, T>` -> `ControlFlow<Option<!>, T>` (`memchr 2.8.3`, `14 / 641` = `2.18%`):** Aliasing `core::convert::Infallible = !` and updating `Option`'s `Try::Residual` (`library/core/src/option.rs`) replaced the uninhabited `0`-variant ADT `Infallible` with primitive `TyKind::Never` across every `?`-using `Option` body:
   ```diff
   --- 1.99.1:memchr.arch-all-packedpair-{impl#0}-find_prefilter
   +++ 1.100.0:memchr.arch-all-packedpair-{impl#0}-find_prefilter
   -    let mut _13: core::ops::ControlFlow<core::option::Option<core::convert::Infallible>, usize>;
   +    let mut _13: core::ops::ControlFlow<core::option::Option<!>, usize>;
   ```

#### 4.5 Built-In Derive Macro Codegen Drift (`#[derive(Eq)]` and `#[derive(Debug)]`)

- **`1.94.0 -> 1.96.0` (`#[derive(Eq)]`, `1` body renamed in `memchr`):** Commit **`f1ec10ecbd8628f315bee531ddee87f57cdb8096`** (PR `#149978`, `2026-02-25`) renamed `memchr.arch-all-rabinkarp-{impl#12}-assert_receiver_is_total_eq` to `assert_fields_are_eq`.
- **`1.100.0 -> 1.102.0-nightly` (`#[derive(Debug)]`, `53 / 639` = `8.29%` of `memchr` + `2` promoted bodies removed):** Commit **`4719edece749ef683e8971e6e08fd643744a82d0`** (PR `#164726`, merge **`0ccb82fd1f0d9eb109c35cec2a760d48b8e6fa22`**, `2026-10-26`: `"perf: emit field names as a concatenated string in derive(Debug) for structs"`) folded struct/field names into one `&str` constant (`const "One"` -> `const "One s1 v1"`; `const "OneIter"` -> `const "OneIter searcher it"`), shrinking locals across `53` `fmt` bodies and deleting `memchr.arch-all-memchr-{impl#24}-fmt-promoted[0]` and `memchr.arch-generic-memchr-{impl#14}-fmt-promoted[0]`.

#### 4.6 Secondary Lowering & Drop-Elaboration Changes (`3` Bodies in `memchr`)

- **`1.94.0 -> 1.96.0` (`2` bodies: `memchr.ext-{impl#1}-{as_usize,distance}`):** `(self as *const T)` gained one extra intermediate `*const T` `PtrToPtr` cast temporary.
- **`1.96.0 -> 1.99.0` (`1` body: `memchr.cow-{impl#1}-into_owned`):** Drop elaboration eliminated `4` unused `isize` locals (`_9`–`_12`) and `2` dead `discriminant((_1.0: cow::Imp<'_>))` statements (consistent with cleanups such as `3fb482fdde2d0df0853eca1cc0e55387c7722798`, `2026-07-21`; exact commit bisection `not examined`).

### 5. Direct Compatibility Mapping onto `joshlf/anneal` (`c131b320e`) Capture Driver and Trusted MIR Semantics

`Basis: source + derived (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613: trusted/rustc-capture/src/{main.rs,driver.rs}, trusted/lean/Trusted/{MirAst,MirSemantics}.lean)`

#### 5.1 Current Driver Scaffold and Five-Month Internal Pin Skew (`f8a08b688` vs. `8144389c`)

At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
1. **`trusted/rustc-capture/` is an analysis-callback shell, not yet a MIR emitter:** `driver.rs:25` locks `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, rejects compiler-version mismatch (`driver.rs:45-47`), binds the bundled `rust/` sysroot (`driver.rs:54-72`), and checks `tcx.dcx().has_errors().is_none()` in `after_analysis` (`driver.rs:75-84`, explicitly stating `"No compiler data or verification obligation is extracted here."`).
2. **`trusted/lean/Trusted/{MirAst,MirSemantics}.lean` pins a `5`-month-newer `rustc` (`8144389c`, `2026-10-20`):** `MirAst.lean:43-57` defines the full fail-closed `Runtime(PostCleanup)` AST and `MirSemantics.lean:801-802` enforces `pointerWidthBits = 64` and `mirProfileVersion = 1`.
3. **Four concrete `syntax.rs` schema divergences separate `f8a08b688` and `8144389c`:** `AssertKind::NullReferenceConstructed` (`1a982425`, `MirAst.lean:714`), `CastKind::BoxDerefTransmute` (`fcf68f21`), `ProjectionElem::PhantomDeref` (`5686e563`, `MirAst.lean:463`), and `TerminatorKind::Goto { target, loop_hint_attrs }` (`ec45ecff`, `MirAst.lean:747`, `MirSemantics.lean:1528`) all exist in `8144389c` and are **absent** in `f8a08b688`. Wiring live `rustc_private` MIR extraction therefore requires aligning `driver.rs` and `Trusted.MirAst` to one shared `rust-lang/rust` commit.

#### 5.2 Construct-by-Construct Lowering & Fail-Closed Admission Matrix

| 7-Release MIR Drift Item | `Trusted.MirAst` / `MirSemantics` Target (`c131b320e`) | Current Admission & Lowering Rule | Capture Compatibility Verdict |
| :--- | :--- | :--- | :--- |
| **`Rvalue::Use(_, WithRetag)` (`e402c1ed`)** | `Rvalue.use` (`MirAst.lean:583-597, 621`); `evalRvalue` (`MirSemantics.lean:1242-1251`) | Sound for `WithRetag::No` and ref/box-free scalar/bool/unit/never/fieldless-enum types; `Use(_, WithRetag::Yes)` on ref/box-bearing types MUST lower to `Rvalue.unsupported`. | **Compatible if capture checks `WithRetag` + ref-freeness:** Before enabling `MirTy.ref` execution, add `withRetag : Bool` to `Rvalue.use` (bumping `mirProfileVersion`) or keep ref-bearing `WithRetag::Yes` fail-closed. |
| **`Operand::RuntimeChecks` (`6319bee5`) & `-NullaryOp` (`1a227bd4`)** | `Operand` (`MirAst.lean:528-560`: `.copy`, `.move`, `.constant`) | `MirAst.lean:548-556` intentionally omits `RuntimeChecks` and forbids folding it to a `.constant` bool. | **Compatible (fail-closed):** Both `f8a08b688` and `8144389c` already match this shape; capture must fail closed on `RuntimeChecks`. |
| **`!`-Type Fallback (`e7769602`) & `Infallible = !` (`dd132214`)** | `MirTy.never` (`MirAst.lean:296, 316`), `enumAdmitted` (`MirSemantics.lean:507-520`), `isSupportedScalarOrUnitTy` (`MirSemantics.lean:721-724`) | `MirTy.never` IS admitted (`liveUninitSlot .never = .live none`); `0`-variant enums (`Variants::Empty`, pre-`1.100` `Infallible`) are REJECTED by `enumAdmitted`. | **Positive admission-boundary shift at `1.100.0`:** `itoa`'s `let _17: !;` stays admitted with fewer slots, and `Infallible` lowers to admitted `MirTy.never` rather than rejected `Variants::Empty` (though `Option<!>` remains `.unsupported` until payload ADTs land). |
| **`AtomicU* -> Atomic<T>` (`fa66fef1`)** | `MirTy.unsupported` (`MirAst.lean:308-311`), `TerminatorKind.call` (`MirSemantics.lean:1568`) | Non-fieldless ADTs and calls currently fault `.unsupported`. | **Fail-closed today; future hazard:** Future atomic lowering must match `core::sync::atomic::Atomic<T>` + `GenericArgs` or intrinsic items, never pre-`1.96` nominal `AtomicU32`/`AtomicU64` paths. |
| **`BoxDerefTransmute` (`fcf68f21`) & `BoxRaw<T>` (`5d260fd3`)** | `Rvalue.unsupported` (`MirAst.lean:612-618`), `MirTy.unsupported` (`MirAst.lean:308-311`) | All `Rvalue::Cast` and `Box`/`Unique`/`BoxRaw` ADTs lower fail-closed to `.unsupported`. | **Fail-closed today; future hazard:** Never pattern-match `Box.0 = Unique` vs. `BoxRaw` or `Transmute` vs. `BoxDerefTransmute`; lower via `TyAndLayout` + `Box` lang-item semantics. |
| **`NullReferenceConstructed` (`1a982425`) & `PhantomDeref` (`5686e563`) & `Reborrow` (`2d88ee87`)** | `AssertKind.unsupported` (`MirAst.lean:729`), `ProjectionElem.unsupported` (`MirAst.lean:469`), `Rvalue.unsupported` (`MirAst.lean:617`) | All three explicitly map to `.unsupported`. | **Pin-skew compile hazard only:** `NullReferenceConstructed` and `PhantomDeref` are absent in `f8a08b688`; align pin or use fail-closed wildcard `_ => .unsupported`. |
| **`Goto { loop_hint_attrs }` (`ec45ecff`)** | `TerminatorKind.goto` (`MirAst.lean:747, 770-772, 786`) | `loop_hint_attrs` erased cleanly (zero operational semantics). | **Pin-skew syntax hazard only:** Destructure `TerminatorKind::Goto { target, .. }` to stay compatible across `1.100.0` and `1.102.0-nightly`. |
| **`ConstLit`, `AllocId`, & `Body.identity`** | `ConstLit` (`MirAst.lean:504-506`), `AllocId` (`MirAst.lean:129`), `Body.identity` (`MirAst.lean:851-860`) | Indirect/pointer constants fail closed today; `ProgramVerified` requires pairwise-distinct `Body.identity`. | **Mandatory capture invariants:** Canonicalize `AllocId` by per-unit DFS/content hash (eliminating `22%` `itoa` / `11%` `memchr` noise) and emit untrimmed, disambiguator-stripped canonical `DefPath`s (eliminating `8.89%` `ryu` and `2df2c72d` trimmed-path drift). |

#### 5.3 Five Engineering Rules for Version-Resilient `Runtime(PostCleanup)` MIR Capture

1. **Capture via `rustc_middle::mir` (`TyCtxt`), never textual `.mir` dumps:** Eliminates `CrateDisambiguator` (`8.89%` `ryu`), trimmed-path (`2df2c72d`), closure debug-label (`8c4486bc`), and empty `source_scopes` (`e1663b69`) drift automatically.
2. **Lock capture driver and formal MIR AST to one shared `rust-lang/rust` SHA, gating semantic changes on `Program.mirProfileVersion`:** Eliminates internal pin skew (`f8a08b688` vs. `8144389c`) while keeping operational changes (`WithRetag`, `RuntimeChecks`) explicit.
3. **Canonicalize `AllocId` and `Body.identity` deterministically per captured unit:** Guarantees `0.00%` cache invalidation across patch releases (`1.99.0 -> 1.99.1`) and arithmetic crates (`ryu`).
4. **Insulate the TCB from `libcore`/`liballoc` private struct layouts and derive expansions:** Lower `Atomic<T>`, `Box<T>`, and `Infallible`/`!` via `TyAndLayout` and compiler lang/intrinsic items rather than hardcoded field paths; treat derived `Debug`/`Eq` bodies as compiler-version-bound proof obligations.
5. **Gate every `rustc` bump on a multi-corpus differential probe + `syntax.rs` AST diff:** Minor releases mutate `6.55%–19.50%` of real-world crate bodies (`memchr`), making automated upgrade differential checking essential.

### 6. Analytical Evaluation Across Performance (`L1`–`L6`), Comprehensibility (`C1`–`C2`), and Validation (`V1`–`V4`)

`Basis: execution (L3, L6 from support/mir_seven_release_drift_summary.json) + source/derived (C1, C2, V1, V2, V4); unmeasured metrics labeled not measured`

| Dimension | Empirical Measurement / Architectural Assessment | Evidence Basis |
| :--- | :--- | :--- |
| **`L1` Authoring & Proof Velocity** | **`not measured`** (no interactive Lean proof authoring was timed; qualitatively, `33.39%` cumulative true MIR drift in `memchr` shows proofs tied to raw MIR local indices or derived bodies incur substantial cross-release maintenance, whereas pure arithmetic crates like `ryu` incur `0.00%`). | `not measured` (`derived` note from `execution`) |
| **`L2` Toolchain Build Time** | **`not measured`** (official pre-built `rustup` toolchains were executed directly; building `rustc` or `anneal-rustc-capture` from source was not timed). | `not measured` |
| **`L3` Compile / Capture Extraction Latency** | **Measured live across `28` `rustc -C opt-level=2 -Z dump-mir=all` runs:** `feature_probe` (`37` bodies): **`0.234s–0.487s`**; `itoa` (`59`): **`0.641s–0.818s`**; `ryu` (`45`): **`0.866s–1.531s`**; `memchr` (`639–641`): **`5.101s–7.771s`**; complete 7-release × 4-corpus run: **`75.43s`**. In-memory `anneal-rustc-capture` latency is `not measured` (no emitter at `c131b320e`). | `execution` (`support/mir_seven_release_drift_summary.json`) |
| **`L4` Generated Code Performance** | **`not measured`** (scope is `Runtime(PostCleanup)` MIR schema stability, not compiled binary runtime). | `not measured` |
| **`L5` Certificate Checking Throughput** | **`not measured`** (no Lean 4 kernel replay or certificate checking was run). | `not measured` |
| **`L6` RAM / Disk / Inode Footprint** | **Measured live `-Z dump-mir=all` file/inode footprint:** `feature_probe`: `3,914–4,056` files/toolchain; `ryu`: `4,558–4,724`; `itoa`: `4,494–4,664`; `memchr`: **`67,138–69,536` files/toolchain**. Retaining `7` toolchains simultaneously exceeds `500k` files and hit `/tmp` tmpfs inode exhaustion (`1,048,576` total inodes); per-toolchain cleanup caps peak footprint at `69,536` files (`~7×` reduction). Peak RAM RSS and binary size: `not measured`. | `execution` (`support/mir_seven_release_drift_summary.json` + `df -i /tmp`) |
| **`C1` Auditability of Specs & Assumptions** | **Strong 1:1 upstream citation discipline in `Trusted/MirAst.lean`, weakened by pin skew:** `MirAst.lean` quotes `syntax.rs` verbatim with explicit `.unsupported` boundaries (`MirAst.lean:33-48`), but the `5`-month skew between `driver.rs` (`f8a08b688`) and `MirAst.lean` (`8144389c`) leaves `4` AST variants/fields unaligned until synchronized. | `source` (`joshlf/anneal@c131b320e` + 9-rev `syntax.rs` diff) |
| **`C2` Conceptual Orthogonality / Expressibility** | **Clean separation between cosmetic noise and semantic core:** Only `2 / 9` `syntax.rs` mutations (`WithRetag`, `BoxDerefTransmute`) fired in live production MIR, while `5` stdlib/typeck/derive changes (`Atomic<T>`, `Infallible = !`, `!` fallback, `BoxRaw`, `derive(Debug)`/`Eq`) reshaped `95` bodies without touching `syntax.rs`—validating layout/intrinsic-based lowering over stdlib path matching. | `source` + `derived` from `execution` |
| **`V1` Spec Adequacy & Non-Vacuity** | **Fail-closed non-vacuity verified statically on `WithRetag` and `Infallible -> !`:** `MirAst.lean:583-597` and `MirSemantics.lean:507-520, 721-724` reject ref-bearing `WithRetag::Yes` and `0`-variant enums fail-closed (`.unsupported`). Live capture-emitter mutation testing is `not measured` (`c131b320e` has no emitter). | `source` (`Trusted/{MirAst,MirSemantics}.lean`); emitter mutation `not measured` |
| **`V2` Differential Fuzzing & Probing** | **Cross-release differential probing across `4,689` pairwise body comparisons (`0` unclassified) + THIR/built-MIR bisection:** Caught `12` distinct compiler changes including `3` invisible to `syntax.rs` diffing (`Option<!>`, `BoxRaw`, `derive(Debug)` concat strings). Randomized MIR fuzzing (`rustlantis`) was `not examined`. | `execution` (`support/mir_seven_release_drift_probe.py`) |
| **`V3` Weak-Memory / Crash / Silicon** | **`not examined`** (atomic MIR type drift `AtomicU* -> Atomic<T>` is measured; hardware weak-memory lowering and silicon execution are out of scope). | `not examined` |
| **`V4` Held-Out Ecosystem Replay** | **Measured on `3` unmodified crates.io libraries (`745` bodies) + `37`-body probe across `7` real `rustc` releases (`28 / 28` `rc=0`):** Exposes real ecosystem drift (`memchr` `36.36%` vs. `ryu` `0.00%`) missed by synthetic probes (`feature_probe` did not trigger `BoxDerefTransmute`, `BoxRaw`, `Option<!>`, `!` fallback, `derive(Debug)`, or `derive(Eq)`). Multi-crate workspaces (`zerocopy`, proc-macros, `async`) were `not examined`. | `execution` (`support/mir_seven_release_drift_summary.json`) |

## Boundaries

1. **Unmeasured Intermediate Releases (`not examined`):** Only the seven installed toolchains (`1.93.1`, `1.94.0`, `1.96.0`, `1.99.0`, `1.99.1`, `1.100.0`, `1.102.0-nightly`) were executed; `1.95.x`, `1.97.x`, `1.98.x`, and `1.101.x` were `not examined` dynamically (though `f8a08b688` and `8144389c` were statically AST-diffed and causal commits verified via `gh api`).
2. **Cargo Workspaces, Proc-Macros, Async/Coroutines, and Nightly Features (`not examined`):** All crates were compiled standalone via bare `rustc --crate-type=lib` for uniform cross-toolchain flags. Multi-crate Cargo workspaces (`google/zerocopy`, which lacks a standalone root `src/lib.rs`), proc-macro crates, `async fn` coroutines, and unstable features (`reborrow`, `generic_const_exprs`) were `not examined` and likely exhibit higher churn.
3. **`Runtime(Optimized)` MIR and `-C debug-assertions=on` (`known not to apply`):** Measurements apply strictly to `3-2-000.runtime-post-cleanup.after.mir` at `-C opt-level=2` (pre-inlining, `debug-assertions=off`). Drift percentages are **`known not to apply`** to `Runtime(Optimized)` MIR (where optimization/inlining passes churn much more frequently), and `-C debug-assertions=on` or direct `libcore` capture will additionally surface `Operand::RuntimeChecks` (`1.94.0+`) and `AssertKind::NullReferenceConstructed` (`1.99.0+`).
4. **Live `anneal-rustc-capture` MIR Emitter (`unsupported` at `c131b320e`):** `trusted/rustc-capture/src/driver.rs:79` performs no MIR extraction at `c131b320e`; Section 5 maps empirical drift onto the committed `driver.rs` pin and `Trusted.{MirAst,MirSemantics}` definitions rather than executing a live MIR-to-Lean serializer.
5. **Secondary Commit Bisection (`unknown`):** Exact single-commit `git bisect` for `memchr`'s `2` `ext.rs` `PtrToPtr` bodies (`1.94.0 -> 1.96.0`) and `1` `cow::into_owned` dead-`discriminant()` body (`1.96.0 -> 1.99.0`) is `unknown` (the `Runtime(PostCleanup)` diffs themselves are directly observed).
6. **Non-`x86_64-unknown-linux-gnu` Targets and `L1`/`L2`/`L4`/`L5`/`V3` (`not examined`):** Alternative architectures (`aarch64`, `wasm32`, `32`-bit targets rejected by `pointerWidthBits = 64`) and unmeasured `L1`/`L2`/`L4`/`L5`/`V3` dimensions were `not examined`.

## Evidence

| Artifact / Upstream Source | Immutable Pin / Coordinates | Evidence Role & What It Establishes |
| :--- | :--- | :--- |
| `support/mir_seven_release_drift_probe.py` | Preserved in package (`support/`) | **Execution script:** Portable `7`-release × `4`-corpus `Runtime(PostCleanup)` MIR probe with per-toolchain `mir_dir` cleanup, 5-layer normalization, and causal classifier. |
| `support/mir_seven_release_drift_summary.json` | Preserved in package (`support/`), `89,023` bytes, `2026-11-20` | **Execution data (`28 / 28` `rc=0`):** Toolchain metadata, per-toolchain file/body/latency stats, `ryu[xxxx]` hashes, all `6` adjacent + cumulative `1.93.1 -> nightly` tables, and scrubbed diff samples. |
| `rust-lang/rust` (`1.93.1`, `LLVM 21.1.8`) | `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf` | **Execution & source:** Baseline `2026-02-11` toolchain and `syntax.rs` AST snapshot (`13` `StatementKind`, `14` `Rvalue`, `3` `Operand`, `8` `ProjectionElem`, `11` `AssertKind`, `11` `CastKind`). |
| `rust-lang/rust` (`1.94.0`, `LLVM 21.1.8`) | `4a4ef493e3a1488c6e321570238084b38948f6db` | **Execution & source:** `2026-03-02`; `-Rvalue::NullaryOp` (`1a227bd47ff200975f4afb287ec725861ab8b87a`) and `+Operand::RuntimeChecks` (`6319bee585561a078de4a0f8d07d567ce69cf12c`, PR `#148766`). |
| `rust-lang/rust` (`1.96.0`, `LLVM 22.1.2`) | `ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96` | **Execution & source:** `2026-05-25`; `-ShallowInitBox` (`6d4b1b38e76c0858c8e98f89afa37535261749ca`, PR `#152758`), `Atomic<T>` (`fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`), `#[doc(hidden)]` trimmed paths (`2df2c72d7ae36d11313ed730960030cc5af9fb21`), `Eq::assert_fields_are_eq` (`f1ec10ecbd8628f315bee531ddee87f57cdb8096`, PR `#149978`). |
| `rust-lang/rust` (`1.98.0-nightly`) | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | **Source:** `2026-05-30` pin in `joshlf/anneal` `trusted/rustc-capture/src/driver.rs:25`; contains `WithRetag` + `Reborrow`, lacks `4` later AST changes in `8144389c`. |
| `rust-lang/rust` (`1.99.0`, `LLVM 23.1.1`) | `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` | **Execution & source:** `2026-09-28`; `WithRetag` / `no_retag copy` (`e402c1edf047a23b0cfef40c6097d1caa294050b`, PR `#154341`, merge `20de910db49d3476ccf49ea79a4b22e2b5dface0`), `Reborrow` (`2d88ee87ddaa584a19e438528f60f825f735076a`), `NullReferenceConstructed` (`1a982425b6699f2b26552c6b44cc979a3d84543b`, PR `#158796`), `BoxDerefTransmute` (`fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f`). |
| `rust-lang/rust` (`1.99.1`, `LLVM 23.1.1`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | **Execution & source:** `2026-10-13`; confirms `0 / 782` (`0.00%`) normalized drift across stable patch release `1.99.0 -> 1.99.1`. |
| `rust-lang/rust` (`MirAst` ref) | `8144389c895da997dbdecaa635e41d6a50be6ffd` | **Source:** `2026-10-20` nightly cited in `joshlf/anneal` `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`. |
| `rust-lang/rust` (`1.100.0`, `LLVM 23.1.5`) | `0ef1bc386059596dada8fb65b50425aab2ea637a` | **Execution & source:** `2026-11-09`; never-type stabilization (`e7769602aca3770e8d8ea55716becb22e839a579`, PR `#155499`), `Option<!>` (`dd132214ed3e2415da4292fec21f564f4496baa5`), `PhantomDeref` (`5686e563774cd9e8bfba79d3ab1167fe198e9e78`, PR `#159103`), closure debug capture names (`8c4486bc034869f27c4218c3d0037dbf2ed484e9`, PR `#162154`, merge `56b18c11458769ae086ce2ae6c7da36a60801843`). |
| `rust-lang/rust` (`1.102.0-nightly`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | **Execution & source:** `2026-11-11`; `Goto { loop_hint_attrs }` (`ec45ecffeee8ba13e42a7f45b6cdad3155ebd146`, PR `#163931`), `BoxRaw<T>` (`5d260fd3da7b0165d6365adab12746bfc389d913`, PR `#162849`, merge `2d418e9411cf9b91cd43c75b827f6df920ff5799`), `?` scope pruning (`e1663b69bf6e0f5b69c3490b7f66cb8a2113bb99`, PR `#164122`, merge `0a4720d4b4809660670b050d97df98934f970c07`), `derive(Debug)` concat strings (`4719edece749ef683e8971e6e08fd643744a82d0`, PR `#164726`, merge `0ccb82fd1f0d9eb109c35cec2a760d48b8e6fa22`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | **Source:** `trusted/rustc-capture/src/{main.rs,driver.rs}` and `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`. |
| `dtolnay/ryu` (`1.0.23`) | `f0b52bb194befe6fd242154f2182fafd43a819b8` | **Execution corpus (`45` bodies):** `8.89%` pure `CrateDisambiguator` noise collapsing to `0.00%` semantic drift across all `7` releases. |
| `dtolnay/itoa` (`1.0.19`) | `9339ca99a43c550b5ee36e2afe524d1c90413461` | **Execution corpus (`59` bodies):** `22.03%` pure `AllocId` noise (`1.93.1 -> 1.96.0`) and `1.69%` Edition 2021 `!` local elision (`src/lib.rs:106–113`, `1.99.1 -> 1.100.0`). |
| `BurntSushi/memchr` (`2.8.3`) | `5fdb40c054e1fff359a2f7bdf7f87a13b34b465d` | **Execution corpus (`641`/`639` bodies):** `36.36%` (`232 / 638`) cumulative normalized drift (`213` true AST/type/codegen, `19` pretty-print-only, `13` pure `allocN`), `rc=0` on all `7` toolchains with per-toolchain dump cleanup. |

## Revalidation

1. **Re-run the full 7-release × 4-corpus probe** (requires `rustup` toolchains `1.93.1`, `1.94.0`, `1.96.0`, `1.99.0`, `1.99.1`, `1.100.0`, `nightly` and `ryu-1.0.23`/`itoa-1.0.19`/`memchr-2.8.3` in `$CARGO_HOME/registry/src/`):
   ```bash
   python3 support/mir_seven_release_drift_probe.py --out /tmp/mir_7rel_revalidate.json
   ```
   Confirm `28 / 28` `rc=0`, `ryu` `0 / 45` semantic drift across all transitions, `itoa` `1 / 59` at `1.99.1 -> 1.100.0`, and `memchr` `0 / 46 / 125 / 0 / 42 / 72` (`232 / 638` cumulative).
2. **Minimal `< 2s` reproducer for Edition 2021 `!` local elision (`1.99.1 -> 1.100.0`):**
   ```bash
   cat <<'RS' > /tmp/repro_never.rs
   pub fn f(x: bool) -> u32 {
       if x { unsafe { core::hint::unreachable_unchecked() }; }
       42
   }
   RS
   diff -u \
     <(RUSTC_BOOTSTRAP=1 rustup run 1.99.1 rustc --crate-type=lib --edition=2021 -Z unpretty=thir-tree /tmp/repro_never.rs) \
     <(RUSTC_BOOTSTRAP=1 rustup run 1.100.0 rustc --crate-type=lib --edition=2021 -Z unpretty=thir-tree /tmp/repro_never.rs) | grep -E '^[+-]\s*(ty:|NeverToAny)'
   ```
3. **Diff `compiler/rustc_middle/src/mir/syntax.rs` across any candidate `rustc` upgrade or `joshlf/anneal` pin pair:**
   ```bash
   diff -u \
     <(gh api "repos/rust-lang/rust/contents/compiler/rustc_middle/src/mir/syntax.rs?ref=f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1" -H "Accept: application/vnd.github.raw") \
     <(gh api "repos/rust-lang/rust/contents/compiler/rustc_middle/src/mir/syntax.rs?ref=8144389c895da997dbdecaa635e41d6a50be6ffd" -H "Accept: application/vnd.github.raw") \
     | grep -E '^[+-]\s*(pub enum|Goto|NullReferenceConstructed|BoxDerefTransmute|PhantomDeref|Use\(|Retag)'
   ```
4. **Extend once `anneal-rustc-capture` emits live Lean MIR:** Rerun this probe through the live capture binary on Cargo workspaces (`zerocopy`, async/proc-macro crates) and `-C debug-assertions=on` builds to measure in-memory `L3` latency, `V1` emitter mutations, and `Operand::RuntimeChecks` encounter rates.
