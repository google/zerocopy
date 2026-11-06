# Configured Rust Capture, FnAbi and Machine Placement Witnesses, and Formality/Specr/Generated-Rust Boundaries

## Summary

Sound verification of configured Rust crates requires binding six distinct semantic and compilation boundaries rather than treating surface source paths, post-expansion names, or compiler debug dumps as self-authenticating models:

1. **Configured Subject Capture, Implicit Operations/CTFE/TLS, and Independent Obligation Completeness**: Before Mid-Level Intermediate Representation (MIR) construction, a configured Rust subject is determined by `cfg` vs. `cfg!` evaluation, receiver/coercion adjustments (`Adjustment`, `PointerCoercion`, overloaded `Deref`), HIR/THIR desugarings (`rustc_ast_lowering`, `rustc_mir_build`), compile-time constant evaluation (`Allocation`, `eval_in_interpreter`, `intern_and_validate`), and `LocalKey` thread-local lifecycle rules. In `ObligationPilot.lean` (checked in Lean `4.31.0` at `68218e876d2a38b1985b8590fff244a83c321783`), an exact safety-obligation generator (`generated_exact : generate operations state ↔ Safe (run operations state)`) proves why an independently selected program and domain (`proposed = independentlySelectedOriginal`) are required to prevent omitted instructions, dropped `StorageDead` invalidations, or reordered assertion/load boundaries from hiding undefined behavior. Three bounded controls (`support/inline-control/Inline.lean`, `support/modular-control/Modular.lean`, and `support/attachment-control/probe.rs`, checked with Lean `4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52` and `rustc 1.99.0` / `1.101.0-nightly`) demonstrate that inlining preserves callee panic guards even when return values are unused, modular call composition rejects mismatched callee dictionaries/contracts, and post-expansion `DefId` owner binding distinguishes identically named macro-expanded functions (`intended::validate` vs. `decoy::validate`).
2. **Caller-Bound `rustc_driver` Capture with Actual Instances and Generated Owners**: Using `rustc 1.97.0-nightly` (`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, `aarch64-apple-darwin`), an `after_analysis` observer (`support/capture_observer.rs`) and consumer (`support/capture.py`) fix the caller request (source hashes, root signature, edition, target/CPU, `cfg` features, `/owned-source` path remap, and tool/driver SHA-256 digests) before comparing an untrusted candidate JSON against a fresh compiler observation of expanded local owners (`iter_local_def_id`), typed `instance_mir` bodies, concrete generic/trait instances (`try_resolve`), evaluated scalar constants, closure bodies, and generated `Drop` shims (`resolve_drop_in_place`). Across a 34-control matrix (`5` captures, `6` accepted candidate/request pairs, `23` rejections) and `1,280` native byte executions across five subjects, mutating a MIR operator (`BitXor` to `BitOr`) or coherently erasing a `Drop` terminator and its glue is rejected.
3. **Configured `FnAbi` Witnesses and Target-Specific Machine Placement (`aarch64-apple-darwin` vs. `x86_64-pc-windows-msvc`)**: Compiler `FnAbi` observations (`evidence/abi-witness/observer_v3.rs` on `rustc 1.97.0-nightly@f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`) are target- and optimization-configured witnesses rather than portable calling conventions or complete register maps. Across four Darwin (`aarch64-apple-darwin`/`apple-m1`, `opt0` and `opt2` on `subjects.rs` and `vectors.rs`) and one Windows (`x86_64-pc-windows-msvc`/`x86-64`, `opt2`) profile, whole-field consumer checks accept fresh references and reject `15` schema-admissible Darwin mutants, `7` fresh Windows mutants, and `63` pure-data/CLI controls. Matched LLVM IR, assembly, and object inspection (`904` Mach-O text bytes / `226` instructions on Darwin; `232` COFF text bytes / `72` instructions on Windows, verified with Apple LLVM `objdump` version `21.0.0`) show concrete placement differences: Darwin passes indirect aggregate results via `x8`, hidden `#[track_caller]` locations in `x1`, and stack arguments at `SP + [0, 8, 16, 24]`, whereas Windows uses `rcx` (returned in `rax`) for indirect aggregates, `rdx` for `#[track_caller]`, reserves a 32-byte shadow space (`RSP + [8, 40)`), and duplicates floating-point variadic arguments across `xmm2` and `r8` with `r9` carrying the fourth parameter.
4. **Executable Judgment, Codegen, and Nondeterminism Boundaries in `a-mir-formality` and `specr` / `MiniRust`**: Executing `rust-lang/a-mir-formality@71dc31c1b186df1f0a64d8464b8103195902a5a5` (`rustc 1.96.0-nightly@48cc71ee88cd0f11217eced958b9930970da998b`) across `20` owned judgment/codegen cases and `4` direct upstream normalization tests shows that a reachable `trusted fn` helper passes type checking but fails MiniRust code generation (`function helper must have expression body`), while an uncalled `trusted fn` is omitted from the generated reachable program. Examining `minirust/specr@15200eb5e676e2ee91f43bd79e674f8fc32e5348` (`0.1.41`) and `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` alongside Lean `4.34.1` proofs in `support/Choices.lean` shows that `specr-transpile` is an unverified syntax transformer without a formal prover backend, `libspecr`'s 50-sample `pick` and unimplemented `predict` cannot decide demonic (`∀`) vs. angelic (`∃`) semantic quantifiers, and `minimize`'s MIR-to-MiniRust lowering makes explicit UB/unwind choices (such as `unwind_block: None` on `Drop`).
5. **Build-Script (`build.rs`) and Procedural-Macro Visibility vs. Span Provenance in Charon (`nightly`)**: At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `charon cargo` compiles host crates (`build.rs` and `proc-macro` crates) normally without translating them (`is_selected_crate` requires `CARGO_PRIMARY_PACKAGE` and `--target`), then runs `translate_crate::translate` in `Callbacks::after_expansion`. Consequently, target Rust included from `OUT_DIR` via `include!` or expanded from a procedural macro is semantically visible to Charon's HIR/MIR translation, whereas linked native C/assembly objects have no Rust MIR body, and `translate_span_data` records only the final `Span` filename/line/column (`generated_from_span` tracks MIR inlining rather than macro expansion chains, and `FileName::NotReal` hits `unimplemented!()`).

## Applicability

This report synthesizes six primary-source and empirical investigations across Rust capture, ABI/machine placement, executable specifications, and macro/build-script visibility:

1. **Configured Capture, Implicit Operations/CTFE/TLS, and Independent Obligation Completeness (`2026-10-14`)**:
   - Normative/source pins: `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`, `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec`, `AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`, and `AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e`.
   - Executed artifacts: `ObligationPilot.lean` (SHA-256 `17149fd58168fce0120c9814b6aedb14b74d107ce2390627889ceb9bb140c545`) and `subject.rs` (SHA-256 `28f24a9ad2101629774e8bb53510a2467bef0fe85846e520e46e4d5fdb6c1200`) checked on `Lean 4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`, qualified by the Lean `4.32.2` nested-inductive soundness note, issue `14576` / PR `14577`); plus `support/inline-control/Inline.lean` (`fcd32005109d87f4b00f7748101c85a976f72d855de2f80d0f631043d31ff94a`), `support/modular-control/Modular.lean` (`b4768930f94676ce96fdb2808e3e755552b7e85e6f80f723f1c762e2b570396f`), and `support/attachment-control/probe.rs` (`3a48e47e5e080dc997532b4794d0ffe3f760cc03109146c9a815a5e6c8d8c4b0`) checked on `Lean 4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), and `rustc 1.101.0-nightly` (`1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`).
2. **Caller-Bound `rustc_driver` Capture with Actual Instances and Generated Owners (`2026-10-14`)**:
   - Executed on `aarch64-apple-darwin` (Darwin kernel `27.0.0`) with `rustc 1.97.0-nightly (2026-04-30)` (`rust-lang/rust@f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, LLVM `22.1.4`, `rustc` SHA-256 `c456b0855e2d148f5d517952f2cb684bf0379d125d2c89b5ca16d46e56c80988`, `librustc_driver` SHA-256 `dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d`) and owned observer (`support/capture_observer.rs` SHA-256 `59a998fb395374b810e3e0a04884e0a5c6382ea06b951fda6f8aec5cf3b87f35`, binary SHA-256 `656fb5eaac61cecbed4b59b90ff5842cf2594551310084d599d66c9af817f636`, consumer SHA-256 `0b1fc20394b64cbc84e2f4323301dad10f9334d2205952c6882dd81875b73382`, schema SHA-256 `6cb6da673ed91009ca3b64ee2df6628897a692dcd7ceffcc52aa09d7995bbb62`).
3. **Configured Rust `FnAbi` Witnesses and Machine Placement (`2026-10-14`)**:
   - Executed on `aarch64-apple-darwin` using `rustc 1.97.0-nightly` (`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, driver SHA-256 `dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d`), `observer_v3.rs` (SHA-256 `e6c50e7c4ce7bc9ff5eb5515cc4f5973fd2fc182d53bce38dbfeb09afc398ba1`, binary SHA-256 `f1d0404e6c9cfca353376653c1ea9464c328d358851447e12af65953d368172b`), `subjects.rs` (SHA-256 `aed38d71c0fcd664388c8711135f975e9980ded8d50ed7b9af837da423631e02`), `vectors.rs` (SHA-256 `0d12cc6a373d3d72dde1dcc52e0f01c0ff72ea65078a4bfb81e14bb5d99e45a8`), and Apple LLVM object reader release `21.0.0` (SHA-256 `83b32f39e5475ee168927eb1509c82978e08e0100ec8c6fafeca588d9960773c`) across target profiles `aarch64-apple-darwin`/`apple-m1` (`opt0`, `opt2`) and `x86_64-pc-windows-msvc`/`x86-64` (`opt2`).
4. **`a-mir-formality` Judgments/Codegen (`71dc31c`) and `specr`/`MiniRust` Boundaries (`15200eb`, `2026-10-14`)**:
   - `rust-lang/a-mir-formality@71dc31c1b186df1f0a64d8464b8103195902a5a5` (archive SHA-256 `dacb47547f117edd5ec63ad75dfcf6e78e219c46a7be1cd3f290836a5cb1db8c`, vendored `crates/minirust-rs` with `libspecr = 0.1.40` and `BasicMemory<x86_64>`) built and executed under `nightly` (`rust-lang/rust@48cc71ee88cd0f11217eced958b9930970da998b`, `1.96.0-nightly`, LLVM `22.1.2`, Cargo `888f67534`).
   - `minirust/specr@15200eb5e676e2ee91f43bd79e674f8fc32e5348` (`0.1.41`), `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`, `support/Choices.lean` (`d084b2a332bc4cd849b026be005e8ac0c282b575a55639ffcdd6b7e8546d7dfd`, verified in Lean `4.34.1`), and `support/probe.py` (`6306465ab2b89108bcfb32c3aeead927606d27e16e13278579ee5314a9f5e9f0`).
5. **Build-Script and Proc-Macro Visibility Before Charon (`2026-09-25`)**:
   - Examined at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`: Rust `2026-05-31`, Aeneas `nightly-2026.06.03`), `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and `rust-lang/reference@01b0ee707f4571e803c8b2c471d8335a448f5d60`.

## Findings

### 1. Configured Capture, Implicit Operations/CTFE/TLS, and Independent Obligation Completeness

#### 1.1 Pre-MIR Semantic Owners, Implicit Operations, CTFE Allocations, and Thread-Local Storage

`Basis: normative + source + derived`

- **Conditional Compilation (`cfg` vs. `cfg!`) and Charon Driver Hooks**: The Rust Reference ([`src/conditional-compilation.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/conditional-compilation.md#L354), lines 354–367, 439–451) distinguishes `cfg` attributes (which remove source items/forms; a false crate-level `#![cfg(...)]` retains preceding crate attributes while stripping subsequent crate contents) from the `cfg!` macro (which evaluates to a Boolean literal). In [`charon/src/bin/charon-driver/driver.rs`](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/driver.rs#L33) (lines 33–87, 367–394), Charon sets MIR optimization level `0` and preserves UB-relevant MIR, but also exposes an option replacing the borrow-check query.
- **Coercions, Method Lookup, CTFE, and `LocalKey` TLS**: The Rust Reference specifies coercion sites and conversions ([`src/type-coercions.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/type-coercions.md)), receiver candidate construction by repeated dereferencing/unsizing/borrowing ([`src/expressions/method-call-expr.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/expressions/method-call-expr.md#L21), lines 21–38), target-environment const evaluation ([`src/const_eval.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/const_eval.md#L23), lines 23–26, 277), and persistent static allocations ([`src/items/static-items.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/items/static-items.md#L13), lines 13–25). In [`library/std/src/thread/local.rs`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/std/src/thread/local.rs#L27) (lines 27–33, 83–107, 408–415), `LocalKey` documents lazy initialization, recursive-initializer hazards, panic on access during destruction, and process abort if a destructor panics.

| Frontier | Correspondence payload |
| --- | --- |
| Receiver/coercion elaboration | Selected target, dereference/borrow operations, representation conversion and evaluation order |
| Temporaries, storage, assertions, drops/cleanup | Lifetime/initialization and failure/outcome effects, including implicit calls |
| CTFE/promotions | Value and allocation contents/identity, target arithmetic, initialization and failure classification |
| Static/TLS access | Persistent or per-thread cell identity, initialization protocol, re-entry, mutation and destruction state |
| Closure/helper extraction | Captured values/resources, actual callable identities and call/cleanup behavior |

| Pinned source coordinates (`rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec`) | Operations and retained information |
| --- | --- |
| [`ty/adjustment.rs:11–40,83–114`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_middle/src/ty/adjustment.rs#L11) | Ordered `Adjustment(kind, target)`: `NeverToAny`, `Deref`, `Borrow`, `Pointer`, and `GenericReborrow`. `PointerCoercion` enumerates function reification, safe→unsafe fn pointer, closure→fn pointer, mut→const pointer, array→pointer, and `Unsize`. |
| `adjustment.rs:117–143,165–207` | Builtin/overloaded/`Pin` deref; shared/mutable borrow with two-phase permission, raw borrow, and `Pin` borrow. Overloaded deref resolves a trait method; its source lifetime relationship is not a runtime operation to invent after erasure. |
| [`rustc_ast_lowering/src/expr.rs:706–724,994–1046,1769–1884,1945–2017`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_ast_lowering/src/expr.rs#L1769) | HIR builders for `while`/`await`, `for`-loop iterator calls, and `?` branch/residual/early return expose inserted callable/control-flow owners; coroutine internals remain excluded. |
| [`thir/cx/expr.rs:84–143,179–299`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_mir_build/src/thir/cx/expr.rs#L117) | Applies typeck adjustments in order, constructs typed THIR operations/scopes, and materializes overloaded deref's borrow and callable. `Unsize` retains target type rather than an already instantiated deep-layout recipe. |
| [`builder/expr/as_rvalue.rs:444–586,662–730`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs#L444); [`as_place.rs:727–755`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_mir_build/src/builder/expr/as_place.rs#L727); [`builder/scope.rs:37–75`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_mir_build/src/builder/scope.rs#L37) | Conditional overflow assertions, division/remainder-by-zero assertions, index bounds assertions, capture temporary `StorageLive`/drop scheduling, and normal/unwind edge cleanup insertion. |

- **CTFE Allocation and Validation Internals**: In [`allocation.rs:95–116`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_middle/src/mir/interpret/allocation.rs#L95), [`eval_queries.rs:148–194,409–500`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_const_eval/src/const_eval/eval_queries.rs#L148), [`intern.rs:181–220`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_const_eval/src/interpret/intern.rs#L181), and [`validity.rs:1654–1668`](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/compiler/rustc_const_eval/src/interpret/validity.rs#L1654), `Allocation` retains bytes, pointer provenance, initialization mask, alignment, and mutability, while `intern_and_validate` validates `Const`/`Promoted`/`Static` modes and distinguishes dangling, mutable, non-global, and partial-pointer errors.
- **Charon `get_mir.rs` and `OfJson.ml` Reader Boundaries**: In [`get_mir.rs:68–109`](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/get_mir.rs#L68), [`export.rs:15–24`](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/export.rs#L15), [`OfJson.ml:21–53`](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon-ml/src/OfJson.ml#L21), and Aeneas [`LlbcOfJson.ml`](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/llbc/LlbcOfJson.ml), Charon falls back when a requested local MIR body was stolen, and the OCaml reader discards the third envelope entry (`has_errors`).

#### 1.2 Exact Obligation Completeness (`ObligationPilot.lean`) and Inlining, Modular-Call, and Attachment Controls

`Basis: source + execution + derived`

- **Exact Obligation Generator (`ObligationPilot.lean`)**: Over a one-cell state with liveness, initialization, read/write authority, alignment, and `u32`-bounded payload, `ObligationPilot.lean` proves:
  ```text
  generated_exact: generate operations state ↔ Safe(run operations state)
  aggregate:
    proposed = independentlySelectedOriginal
    ∧ (∀ state, independentlySelectedDomain(state) → generate proposed state)
    ⇒ ∀ state, Domain(state) → Safe(run original state).
  ```
  where `Safe` permits normal return and panic while excluding UB. `init_then_read` proves safety of `store(7); load` from initially uninitialized live cells, while three controls prove that an empty obligation list hides an omitted invalid load, inserting `StorageDead` invalidates a subsequent load, and placing an assertion before a load permits panic whereas reversing the order exposes UB (using only `propext`).
- **Outcome-Preserving Inlining (`support/inline-control/Inline.lean`)**: Compiling a `#[inline(always)]` callee (which panics on `0` and returns `x.wrapping_add(1)` otherwise) whose caller discards the return value and returns `7` under `rustc 1.99.0` (`b940084d7`, LLVM `23.1.1`, `opt-level=0` and `opt-level=3`) preserves the `x == 0` panic branch inside the caller's LLVM IR across all 256 `u8` inputs (`1` caught panic, `255` returns of `7`). `Inline.lean` (checked in Lean `4.34.1`) proves that outcome-preserving inlining agrees with call-then-return on all bytes whereas a value-only replacement disagrees at `0`.
- **Semantic Modular Call Composition (`support/modular-control/Modular.lean`)**: `Modular.lean` pairs an executable dictionary (`modulus = 256, bias = 1`) with `CalleeCertificate dictionary contract` and proves that `compose` rejects six mismatched negative Lean invocations: mutated body (`bias = 2`), 16-bit target at `x = 255`, nibble representation at `x = 15`, foreign dynamic implementation at `x = 0`, narrowed domain omitting `x = 255`, and weakened `True` postcondition.
- **Macro Expansion and Alias Attachment (`support/attachment-control/probe.rs`)**: Expanding one declarative macro into two modules (`intended::validate` at local `DefId 0:11` with `anneal:bool-valid-v1` accepting `{0, 1}` vs. `decoy::validate` at `DefId 0:14` accepting `{0, 1, 2}`) under `rustc 1.101.0-nightly` (`1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, edition 2024) shows that binding specifications to resolved `DefId` owners and semantic predicates rejects module-rename drift, `< 3` body mutation with a copied doc marker, decoy substitution, and alias duplication.

---

### 2. Caller-Bound `rustc_driver` Capture with Actual Instances and Generated Owners

`Basis: source + execution`

In [`support/capture_observer.rs`](support/capture_observer.rs) and [`support/capture.py`](support/capture.py) (with schema [`support/packet_schema.py`](support/packet_schema.py) and tool locks in [`support/tool-identities.json`](support/tool-identities.json)):

1. **Caller Request Authority Before Candidate Inspection**: `capture.py` takes separate `--request` and `--candidate` arguments, fixes source-file SHA-256 digests, root signature, crate name, edition (`2021`), target/CPU (`aarch64-apple-darwin` / `apple-m1`), `cfg` features (`none` or `feature="flip"`), `/owned-source` path remapping, and trusted `rustc`/driver/observer digests, runs its own fresh compiler observation in `Callbacks::after_analysis` ([`rustc_driver_impl/src/lib.rs:321`](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_driver_impl/src/lib.rs#L321), [`rustc_interface/src/passes.rs:1139`](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_interface/src/passes.rs#L1139)), and compares the complete captured projection against the candidate JSON.
2. **Captured Instance Graph and Local Owner Census**: Using [`instance_mir`](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/mod.rs#L1712), [`Instance::try_resolve`](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/instance.rs#L499), [MIR substitution/normalization](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/instance.rs#L892), [`resolve_drop_in_place`](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/instance.rs#L720), and [`iter_local_def_id`](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/context.rs#L1384), the baseline capture records `24` expanded local definitions, `10` local body templates, `10` concrete/constant/glue bodies, and `10` dependency edges (`root → generated, selected, generic<u8>, closure body, DropGlue<Guard>`; `generic<u8> → <u8 as Step>::step → <u8 as Step>::SHIFT → BIAS`; `DropGlue<Guard> → <Guard as Drop>::drop`).

| Caller-selected case | Definitions / templates / instances / edges | Native results on all byte inputs |
|---|---:|---|
| Baseline root | 24 / 10 / 10 / 10 | 4 |
| Cfg flip | 24 / 10 / 10 / 10 | 7 |
| Changed selected body | 24 / 10 / 10 / 10 | 1 |
| Generic call selecting the u16 implementation | 27 / 12 / 9 / 9 | 3 |
| Decoy as the requested root | 24 / 10 / 1 / 0 | `x ^ 9` |
| Two-file module | 7 / 3 / 3 / 2 | Native execution not requested for this case |

3. **34-Control Matrix and Loader-Placement Verification**: Across `34` controller calls (`5` captures, `6` accepted checks, `23` rejections including `16` candidate/reader mutations—such as `BitXor`→`BitOr`, coherent `Drop` terminator + glue deletion, or uncalled decoy owner deletion—`5` unsupported domain exits with code `65` for external `u8::wrapping_add`, floats, `dyn Trait`, coroutine/async, and generic root, plus `2` preflight rejections for edition `2024` and wrong driver path), all `34` outcomes match expectations (`support/independent-review.md`, `support/independent-review.json`, `support/REPLAY.md`). Because the observer binary uses an `@loader_path` parent-relative `toolchains/rustup/toolchains/nightly-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib` `LC_RPATH` to resolve `librustc_driver-16d1e96e5b674978.dylib` (`dcaea7cc...`), relocating the binary without preserving that relative library tree fails with `dyld` exit `-6` before analysis.

---

### 3. Configured Rust `FnAbi` Witnesses and Target-Specific Machine Placement

`Basis: source + execution + derived`

#### 3.1 Whole-Field `FnAbi` Consumer Checks and Negative Controls (`aarch64-apple-darwin` and `x86_64-pc-windows-msvc`)

Using `evidence/abi-witness/observer_v3.rs`, `evidence/abi-witness/e33_data_v3.py`, `evidence/abi-witness/e33_consumer_v3.py`, and `evidence/abi-witness/stage5/e33_consumer_windows.py` across `evidence/abi-witness/subjects.rs` (`26` selections) and `evidence/abi-witness/vectors.rs` (`3` `#[repr(simd)]` selections):

| Host profile | Entries | Raw reference SHA256 | Correct fresh check |
|---|---:|---|---|
|ordinary opt0|26|`b1a174967a6ec532e6911eaaeff4db89e4181c858bdf7cc903ccd3147056e0e8`|accepted|
|ordinary opt2|26|`befdf851863832f050eb65f4b86552372ad2606d2ed9482a23bf530be096a1d9`|accepted|
|vectors opt0|3|`514edb727f5d65d76b7eae40d137fe6e6efb7d04a82fe8c8dcec93b861ca7166`|accepted, warning-qualified|
|vectors opt2|3|`0f6013e6b62a40075faad25f949e842137af5f187d974bf4387064f1b21ee675`|accepted, warning-qualified|

- **Darwin Controls (`24` actual host controls in `evidence/abi-witness/stage4/actual-controls/results.json`)**: `9` pre-launch rejections and `15` schema-admissible mutants rejected after fresh reference generation (covering hidden `#[track_caller]`/vararg operands, `on_stack` mode, integer extension/`NoAlias`/`NoUndef`, pointee size/align, cast coverage/HFA consecutiveness, `bool` scalar range, generic result size, opaque layout, and unwind permission).
- **Windows Controls (`evidence/abi-witness/stage5/windows-pure-data-controls/results.json` and `evidence/abi-witness/stage6/control-handoff/handoff.json`)**: `63` pure-data/CLI controls plus `9` compiler observer runs (all producing reference SHA-256 `7d99dd6f1f72ca735b69e05f3fb257bc44326980b09edb4ddc38976eeea4e354`: `1` capture, `1` accepted check, and `7` rejected whole-field mutants, plus `3` pre-launch rejections).
- **Cross-Target and Optimization-Level `FnAbi` Differences (`rustc_ty_utils/src/abi.rs`, `rustc_target/src/callconv/{mod,aarch64,x86_win64}.rs`, `rustc_codegen_llvm/src/abi.rs`)**:
  - `C`/`system` narrow `u8`/`i16`/`bool` use `Zext`/`Sext`/`Zext`, whereas `Rust` omits `Zext`/`Sext` on `u8`/`i16`.
  - On Darwin, `C` `Pair` uses an integer-unit cast and `Hfa` uses a consecutive four-`f32` cast, whereas on Windows `C` `Pair` (`16` bytes, align `8`) and `Hfa` (`16` bytes, align `4`) both use `Indirect` input and result passing.
  - Shared `&u64` references acquire `NoAlias`, `ReadOnly`, and pointee-size attributes at `opt2` that are absent at `opt0` (while `&UnsafeCell<u64>` remains distinct).

#### 3.2 Darwin (`aarch64-apple-darwin`) vs. Windows (`x86_64-pc-windows-msvc`) Machine Placement

- **Darwin Mach-O Placement (`904` text bytes / `226` 4-byte instructions across `evidence/abi-witness/stage5/host-summary.json`, `evidence/abi-witness/stage5/artifact-comparison.json`, and `ERRATA.md`)**:
  - Indirect 24-byte `Big` return: `opt0` (`[0x1c, 0x34)`) saves `x8` in `x9`, loads from `x0`, and stores 24 bytes through `x8`; `opt2` (`[0, 0x14)`) stores directly through `x8`.
  - `#[track_caller]`: `opt2` (`[0xa8, 0xb4)`) reads the caller line at `[x1 + 16]` and XORs `x0`.
  - 12-scalar stack forwarding (`_abi_opaque_twelve`): entry `SP = S`, frame allocation `48` bytes, saved `FP`/`LR` at `newSP + 32` (`FP = S - 16`); incoming stack arguments `9..12` at `S + [0, 8, 16, 24]` copy to outgoing `newSP + [0, 8, 16, 24]` while `x0..x7` stay in registers; `bl` at `0x15c`/`0x94` carries `ARM64_RELOC_BRANCH26` (LLVM IR `tail call` does not emit a machine tail branch because the frame is restored before `ret`).
  - Variadic call (`_abi_opaque_vararg`, `opt0` `[0x230, 0x268)` / `opt2` `[0xcc, 0xfc)`): stores the three promoted variadic extras at outgoing `SP + [0, 8, 16]` and passes fixed argument `w0 = 1`.
- **Windows COFF Placement (`232` text bytes / `72` instructions across `16` COMDAT sections in `evidence/abi-witness/stage6/analysis/artifact-comparison.json`)**:
  - Indirect aggregates (`Big` in section `4` `[0, 0x12)`, `Hfa` in section `6` `[0, 0xa)`): copy indirect return pointer `rcx` to `rax` and read source aggregate from `rdx` (`Hfa` copies 16 bytes via `xmm0`). `Pair` (section `8` `[0, 0x10)`) copies bytes `0..12`, leaving padding bytes `12..16` unwritten (`initializes((0, 12))`).
  - `#[track_caller]` (section `16` `[0, 7)`): reads the 32-bit line number from `[rdx + 16]` and XORs `rcx`.
  - 12-scalar stack forwarding (`abi_opaque_twelve`, section `15` `[0, 0x45)`): entry `RSP = S` with return address at `S + [0, 8)`, incoming 32-byte shadow space at `S + [8, 40)`, and incoming arguments `5..12` at `S + [40, 48, 56, 64, 72, 80, 88, 96]`; allocates `104` bytes (`F = S - 104`), reserves outgoing shadow space at `F + [0, 32)`, copies arguments `5..12` to `F + [32..88]` as four 16-byte chunks, and passes `rcx`, `rdx`, `r8`, and `r9` through registers.
  - Mixed variadic call (`abi_opaque_vararg`, section `19` `[0, 0x24)`): receives `x` in `ecx` and `y` in `xmm1`, allocates `40` bytes (`32` shadow + `8` alignment), moves `x` to `edx`, sets `ecx = 1`, **duplicates `y` into both `xmm2` and `r8`**, and zeroes `r9` for the fourth (null-pointer) argument. Both `C` and `Rust` narrow bodies explicitly extend `cl`/`dx`/`r8b` in machine code despite differing IR parameter attributes.

---

### 4. `a-mir-formality` Judgments/Codegen and `specr` / `MiniRust` Boundaries

#### 4.1 `a-mir-formality` (`71dc31c`) Judgment, `trusted fn` Codegen, and Normalization Execution

`Basis: source + execution`

Executing `rust-lang/a-mir-formality@71dc31c1b186df1f0a64d8464b8103195902a5a5` via `owned_e07.rs` across `20` owned cases (`5` parser rejections, `5` checking rejections, `2` failed queries, `1` post-check codegen rejection, and `7` exit-zero runs including `4` vendored `minirust-rs` executions reaching `MachineStop`) plus `4` direct upstream test binary invocations (`normalize_basic`, `normalize_into_iterator`, `projection_equality`, `test_mirror_normalizes_u32_to_u32`):

| Input | Actual result |
|---|---|
| `identity::<i32>(42)` | Checks; generated program has 3 functions; prints 42; `MachineStop` after 21 steps |
| Same generic body at `i32` and `bool` | Checks; 4 functions; prints 42 then true; `MachineStop` after 36 steps |
| `i32` instantiation assigned to `bool` | Parses, then checking rejects |
| Generic call missing its argument | Parses, then checking rejects |
| Reachable `trusted fn` helper | Caller checks, then `codegen_program` fails with `function helper must have expression body` |
| Uncalled `trusted fn` helper | Checks and executes `main` (`MachineStop` after 11 steps); uncalled helper omitted from generated program |
| Uncalled ill-typed expression body | Checking rejects crate even though helper is uncalled |

Additionally, `polonius_alpha` parses, checks, and executes on the loan-free `i32` fixture, whereas unknown feature names, `cfg` attributes, `macro_rules!`, `async fn`, and closures fail parsing in the formality DSL (`feature-and-owner-census.json`), and safe calls to `unsafe fn` or unmarked `impl`s of `unsafe trait` are rejected by checking without proving semantic library invariants.

#### 4.2 `specr` (`15200eb`) Literate Extraction, Demonic vs. Angelic Nondeterminism (`Choices.lean`), and `minimize` Lowering

`Basis: normative + source + documentation + execution + derived`

1. **Literate Markdown Extraction and Name-Unresolved AST Passes (`specr-transpile`)**:
   - `specr-transpile/src/source.rs` enumerates Markdown files without sorting, extracting only blocks fenced by `\n\`\`\`rust\n` and a newline-terminated closing fence (verified by `support/probe.py` boundary discriminators).
   - `main.rs:compile` runs `argmatch`, recursive indirection (`typerec/fix.rs`, which matches enum variants using only their final path segment and wraps recursive payloads in `GcCow::new` without prior rustc name resolution), `impl` merging, automatic derives, index rewriting, and object-bound insertion. `config.rs:Config::load` parses TOML tables despite README documentation describing newline-separated lines.
   - The complete 77-file `specr` and 401-file `minirust` trees contain no `.lean`, `.v`, or `.agda` prover backends (Thiel's 2025-02-08 bachelor thesis references `minirust/specr2@49808b490b2ebd4e93be7322760077d949765527`, which returns HTTP `404` as recorded in `specr2-access.json`, and Kaššák's 2025-03-24 project description is a proposal without a completed prover artifact).
2. **Demonic (`pick`) vs. Angelic (`predict`) Choice Quantifiers (`libspecr/src/nondet.rs` and `support/Choices.lean`)**:
   - MiniRust defines `pick` demonically (universal quantification over allowed choices; an empty set yields no behavior) and `predict` angelically (existential quantification; an empty set is semantic UB). However, `libspecr/src/nondet.rs` samples at most `50` candidates for `pick` before panicking and leaves `predict` `unimplemented!()`. On a 4,096-element domain with 1 valid candidate, 50 independent uniform samples miss with probability $(4095/4096)^{50} \approx 0.9878657$.

| Outcome | Meaning that a validator must retain |
| --- | --- |
| Ordinary choice succeeds on one path | One witnessed execution; no universal safety conclusion |
| Ordinary allowed set empty | No semantic behavior at that choice |
| Predictive allowed set empty | Semantic UB |
| Predictive witness exists | Must also justify its continuation and use at later accesses |
| Divergent path | Not a terminal UB/error result; safety/termination claims differ |
| Sampling budget exhausted or unimplemented primitive | Tool limitation; semantic classification still unresolved |

   - `support/Choices.lean` (checked in Lean `4.34.1`) proves empty-set behavior, demonic coverage certificate soundness, angelic witness certificate soundness, and the quantifier-order inequality between $\forall a.\,\exists p.\,R(a,p)$ and $\exists p.\,\forall a.\,R(a,p)$ across all 16 Boolean relations.
3. **`minimize` MIR-to-MiniRust Lowering and Reference Clause Comparison (`clause-corpus.json`)**:
   - In `tooling/minimize/src/{main,function,bb,rvalue}.rs`, `DEFAULT_ARGS` appends user flags after `-Zmir-preserve-ub`, `Copy` and `Move` both lower to `ValueExpr::Load`, and `bb.rs:220-263` lowers `Drop` terminators to `Call` with `unwind_block: None` (omitting the unwind cleanup edge).

| Case | Current pinned Reference (`2dafab96...`) | MiniRust pin (`d821c6e3...`) / classification |
| --- | --- | --- |
| Raw place/address formation without a load | Raw-borrow rules permit places unsuitable for references; load/store and projection obligations are separate | Historical README raw-dereference note is not a verified current Reference disagreement |
| Reference to initialized, invalid Boolean referent | Reference validity includes valid pointee, explicitly debated | MiniRust checks nonnull/alignment/dereferenceability/inhabitedness but explicitly does not inspect pointee data; a policy difference remains |
| Zero-size access or reference | Zero size removes danglingness; reference nonnull/alignment rules remain | `BasicMemory` zero-size pointer check skips provenance, while load/store alignment occurs first and safe-pointer checks remain |
| Wide-pointer metadata | Valid `usize`/trait vtable and total-size conditions, with raw-vtable uncertainty | MiniRust has explicit metadata/vtable and dynamic-size checks; no general equivalence claimed |
| Union storage versus Boolean field read | Overall union validity unresolved; field read must be valid at field type | Union chunks can retain `Uninit`/provenance; decoding a Boolean field still rejects `2`/`Uninit` |

---

### 5. Build-Script (`build.rs`) and Procedural-Macro Visibility vs. Span Provenance Before Charon (`nightly`)

`Basis: normative + source + documentation + derived`

1. **Host Generator Compilation vs. Selected Target Translation (`charon/src/bin/charon/main.rs`, `charon-driver/driver.rs`)**:
   - Cargo compiles and runs `build.rs` and `proc-macro` crates as **host** executables (`src/doc/src/reference/build-scripts.md`, `environment-variables.md` at `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`). When `charon cargo` runs (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`), it sets `RUSTC_WRAPPER=charon-driver` and passes an explicit `--target`; `is_selected_crate` requires both `CARGO_PRIMARY_PACKAGE` and `--target`, so host `build.rs` and `proc-macro` crates are compiled normally and skipped for LLBC translation.
   - For the selected target crate, `rustc` runs name resolution and macro expansion (`tcx.resolver_for_lowering()`) before invoking `Callbacks::after_expansion` (`compiler/rustc_driver_impl/src/lib.rs` at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), where Charon executes `translate_crate::translate` starting by default from transparent `crate` (`charon/src/options.rs`, `translate_crate.rs`).
2. **Semantic Visibility vs. Native Link Outputs and `cargo::rustc-cfg`**:
   - Target Rust written by `build.rs` into `OUT_DIR` and consumed via `include!(concat!(env!("OUT_DIR"), "/generated.rs"))` (`library/core/src/macros/mod.rs`), or token streams returned by function-like, derive, or attribute procedural macros (`src/procedural-macros.md` at `rust-lang/reference@01b0ee707f4571e803c8b2c471d8335a448f5d60`), are lowered into target HIR/MIR before `after_expansion` and are therefore semantically visible to Charon on the same footing as handwritten target code.
   - Conversely, native C/assembly libraries compiled and linked by `build.rs` (`cargo::rustc-link-lib`) have no Rust MIR body (only Rust-side `extern` declarations/calls are visible), and items excluded by `cargo::rustc-cfg` are stripped before Charon's post-expansion callback.
3. **Proc-Macro `Span` Manufacture vs. Charon `translate_meta.rs` Span Serialization**:
   - In `library/proc_macro/src/lib.rs`, procedural macros are unhygienic for ordinary identifiers and can assign `Span::call_site()`, `Span::mixed_site()`, `resolved_at(other)`, or `located_at(other)` to emitted tokens.
   - In `charon/src/bin/charon-driver/translate/translate_meta.rs`, `translate_span` sets `generated_from_span: None` (using `generated_from_span` only for MIR `inlined_parent_scope` in `translate_span_from_source_info`), does not walk rustc's macro-expansion parent chain, and calls `unimplemented!()` if `translate_filename` returns `FileName::NotReal`. Real files included from `OUT_DIR` retain file spans and `source_file.src` contents in Charon's file table, though `OUT_DIR` filesystem paths are build-local rather than cross-machine identifiers.

## Boundaries

- **Known not to apply**:
  - `FnAbi` equality or compiler `eq_abi` does not determine physical register/stack placement across targets (`x8` on Darwin vs. `rcx`/`rax` and 32-byte shadow space on Windows) or optimization levels (`NoAlias`/`ReadOnly` added at `opt2`).
  - Passing `cargo check` on `specr-transpile` output or sampling 50 paths in `libspecr`'s `pick` does not verify MiniRust operational semantics or demonic (`∀`) / angelic (`∃`) choice quantifiers.
  - A reachable `trusted fn` in `a-mir-formality` passes type checking (`check_all_crates`) but cannot be executed by `codegen_program`, while an uncalled `trusted fn` is silently omitted from the generated executable MiniRust program.
  - Charon's post-expansion source spans cannot in general identify which procedural macro generated an unsafe operation, and `charon cargo` never translates unsafe code inside `build.rs` or `proc-macro` host crates themselves, nor native C/assembly objects linked by `build.rs`.
- **Unsupported or unexamined**:
  - Loops, general heaps/aliasing/provenance, allocation epochs, and unwind cleanup in the one-cell `ObligationPilot.lean` model; external bodies, floats, `dyn Trait`, and coroutines/async in `capture_observer.rs` (rejected with exit code `65`); Windows SIMD `FnAbi` profiles and foreign linking/execution of `subjects.rs`; the inaccessible `minirust/specr2@49808b490b2ebd4e93be7322760077d949765527` commit (`404`); and fresh execution of a combined `build.rs` + `proc-macro` workspace under `charon cargo`.

## Evidence

- **Configured Capture, Obligation Completeness, and Inlining/Modular/Attachment Controls**:
  - `ObligationPilot.lean`, `ObligationPilot.initial.lean`, `subject.rs`, `lean-check.json`, `source-identities.json`, `support/inline-control/Inline.lean`, `support/modular-control/Modular.lean`, and `support/attachment-control/probe.rs`.
- **Caller-Bound `rustc_driver` Instance and Owner Capture**:
  - `support/capture_observer.rs`, `support/capture.py`, `support/packet_schema.py`, `support/tool-identities.json`, `support/requests/base/request.json`, `support/requests/base/probe.rs`, `support/baseline-candidate.json`, `support/observer-build.json`, `support/observations.tar.gz`, `support/independent-review.md`, `support/independent-review.json`, `support/run_controls.py`, `support/run_controls_explicit_observer.py`, `support/replay-helper.diff`, `support/REPLAY.md`, `source-index.json`, `evidence-summary.json`, `projection-receipts.json`, and `projection-audit.json`.
- **Configured `FnAbi` and Machine Placement (`aarch64-apple-darwin` and `x86_64-pc-windows-msvc`)**:
  - `MANIFEST.json`, `PROJECTION.json`, `PRIMARY-SOURCES.json`, `UPSTREAM-LICENSES.json`, `ERRATA.md`, and `evidence/abi-witness/` (`subjects.rs`, `vectors.rs`, `observer_v3.rs`, `e33_data_v3.py`, `e33_consumer_v3.py`, `stage4/actual-controls/results.json`, `stage5/host-summary.json`, `stage5/artifact-comparison.json`, `stage5/HOST-ORACLES.md`, `stage5/windows-pure-data-controls/results.json`, `stage6/control-handoff/handoff.json`, `stage6/analysis/artifact-comparison.json`, `stage6/analysis/WINDOWS-ORACLES-CANDIDATE.md`).
- **`a-mir-formality` (`71dc31c`) and `specr`/`MiniRust` (`15200eb`)**:
  - `support/source.tar.gz`, `support/replay_owned.py`, `support/Choices.lean`, `support/probe.py`, `clause-corpus.json`, `artifact-inventory.json`, and `coverage.json`.

## Revalidation

1. **Re-verify the Lean obligation pilot, inlining/modular controls, and `specr` choice quantifier theorems**:
   ```sh
   lean support/inline-control/Inline.lean
   lean support/modular-control/Modular.lean
   lean support/Choices.lean
   python3 -B support/probe.py
   ```
   Require exit code `0` and zero `sorryAx` dependencies on all three Lean files and matching discriminator output from `support/probe.py`.
2. **Re-verify caller-bound `rustc_driver` instance capture and `a-mir-formality` judgment/codegen cases**:
   ```sh
   python3 -B support/check_evidence.py
   python3 -B support/capture.py check \
     --request support/requests/base/request.json \
     --candidate "$RESTORED_OR_FRESH_ACTUAL_CANDIDATE" \
     --toolchain "$PINNED_TOOLCHAIN" --observer "$EXACT_OBSERVER" \
     --output "$FRESH_OUTPUT"
   python3 -B support/replay_owned.py --toolchain "$APRIL1_TOOLCHAIN" --cargo-home-source "$LOCKED_CARGO_HOME" --workdir "$FRESH_WORKDIR"
   ```
3. **Re-verify `FnAbi` witnesses, Darwin/Windows machine placement, and `build.rs`/proc-macro visibility coordinates**:
   - Verify `MANIFEST.json` and `PROJECTION.json`, run `evidence/abi-witness/e33_consumer_v3.py` and `evidence/abi-witness/stage5/e33_consumer_windows.py` against the pinned `rustc 1.97.0-nightly` toolchain, and re-verify `--emit=llvm-ir,asm,obj` text sections and relocations against `evidence/abi-witness/stage5/artifact-comparison.json` and `evidence/abi-witness/stage6/analysis/artifact-comparison.json`.
   - Diff Cargo's `build-scripts.md`, `rustc_driver_impl/src/lib.rs` (`after_expansion`), and Charon's `driver.rs` (`is_selected_crate`) and `translate_meta.rs` (`translate_span_data`) when updating the toolchain or Charon pin.
