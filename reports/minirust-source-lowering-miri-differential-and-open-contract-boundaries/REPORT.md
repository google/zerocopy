# MiniRust Generated-Core Execution, 19-Case `minimize` vs. Miri Differential Comparison, Unwind Elaboration, and Open-Client Linking Boundaries

## Summary

MiniRust (`minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) connects to executable Rust through two toolchains: (1) `specr` (`minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`), which transpiles the Markdown specification into a Rust interpreter crate (`minirust_rs`) backed by `libspecr`, and (2) `minimize` (`tooling/minimize/`), which links `rustc` internals (`nightly`, `rustc 1.97.0-nightly f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`) to lower Rust MIR into serialized MiniRust programs. Meanwhile, `a-mir-formality` (`rust-lang/a-mir-formality@71dc31c1b186df1f0a64d8464b8103195902a5a5`) implements static crate, trait, associated-type normalization, and NLL borrow-checking judgments together with an experimental MiniRust code generator.

This report consolidates five investigations—actual `specr` code generation and `minirust_rs` execution, a 19-case end-to-end `minimize` vs. Miri (`-Zmiri-tree-borrows`) differential corpus, a mechanized Lean 4 (`4.34.1`) spatial-linking bridge (`Bridge.lean`), and source/execution audits of `a-mir-formality`, drop/unwind elaboration, and open-library callback contracts:

1. **Real Specr-Transpiled MiniRust Core Execution and Toolchain Version Sensitivity (`minirust-actual-core-disagreement-evidence-d821c6e`):**
   - Compiling the `specr`-generated MiniRust interpreter succeeds under the specification's requested `rustc 1.97.0-nightly (f53b654a8 2026-05-01)`, whereas `rustc 1.99.0 (b940084d7)` rejects `libspecr` with `E0046` because `libspecr`'s unstable `core::iter::Step` implementation omits the newer `forward_overflowing` and `backward_overflowing` methods.
   - Across 23 upstream `minitest` tests and 8 custom AST probes on the generated `run_program::<BasicMem>` API (`x86_64` target), the real core confirms: (a) `u8` byte `2` transmuted to `bool` and unchecked `255u8 + 1` raise semantic UB; (b) a 1-byte, 2-variant enum with `Discriminator::Known(0)` passes core well-formedness (`Type::check_wf`) yet decodes encoded variant `1` as variant `0`; and (c) a 16-byte wide-pointer union (`*const [u8]`) with `chunks = [(0, 8)]` passes well-formedness but resets the 8-byte length metadata word to `Uninit`, raising `Ub("transmuted value is not valid at new type")` on reload, whereas `chunks = [(0, 16)]` preserves length `3` and terminates with `MachineStop`.
2. **End-to-End `minimize` Lowering vs. Miri Tree Borrows Across 19 Rust Fixtures (`minirust-source-lowering-miri-nineteen-cases-d821c6e`):**
   - Out of 19 Rust source fixtures executed under Miri (`-Zmiri-tree-borrows` on `nightly`), 17 lower through `minimize` into MiniRust JSON and run under both MiniRust `TreeBorrowsMemory` (`--minirust-tree-borrows`, `implicit_writes=false`) and `BasicMemory`: **12 passing programs and 4 UB controls agree across all three engines**, while **1 valid program (`union_wide_one_field.rs`) succeeds in Miri but fails with UB in both MiniRust models** because `minimize`'s `calc_chunks` (`tooling/minimize/src/chunks.rs:47`) emits `chunks = [[0, 8]]` for the 16-byte `*const [u8]` union. Adding an unused `[usize; 2]` sibling field (`union_wide_two_word_control.rs`) expands emitted chunks to `[[0, 16]]` and restores agreement with Miri.
   - Contrary to the synthetic `Known(0)` core AST counterexample, lowering an actual single-variant Rust enum (`#[repr(u8)] enum E { Only = 0 }` in `enum_single_zero.rs` and `enum_single_invalid_one.rs`) via `minimize` (`tooling/minimize/src/enums.rs`) emits a `Branch` discriminator covering `[0, 1) -> Known(0)` with `fallback = Invalid`, rejecting invalid tag `1` in both MiniRust and Miri.
   - The remaining 2 fixtures (`library_box.rs` and `library_drop_unwind.rs`) succeed in Miri but abort in `minimize` with an internal compiler error (`exit 101`) at `tooling/minimize/src/bb.rs:790` on foreign allocator deallocation `alloc::alloc::__rust_dealloc`.
3. **Unwind Payloads, the `minimize` Destructor-Unwind Seam, and Drop-Elaboration Scope (`minirust-unwind-elaboration-and-open-client-obligations-d821c6e`):**
   - MiniRust's core language implements thread unwind-payload stacks and `StartUnwind`, `StopUnwind`, and `ResumeUnwind` terminators (`spec/lang/step/terminators.md:405`, `spec/lang/machine.md:109`), where `ResumeUnwind` deallocates frame locals and invokes `mem.end_call(frame.extra)` to release Tree Borrows protectors before jumping to the caller's unwind block.
   - However, `minimize`'s MIR `TerminatorKind::Drop { place, target, .. }` lowering (`tooling/minimize/src/bb.rs:220`) emits a MiniRust `Call` to drop glue with `unwind_block: None`, discarding the MIR `unwind` edge (such as `drop(_5) -> [return: bb8, unwind: bb12]` observed in [`support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe-bin.mir`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe-bin.mir)). Viktor Fukala's 2024 ETH thesis formalizes drop elaboration only for terminating executions without enums or unwinding.
4. **Static Judgments in `a-mir-formality` and Instance-Binding / Unsafe-Trait Controls (`minirust-static-judgments-and-open-contract-controls-2026`):**
   - In `rust-lang/a-mir-formality@71dc31c1b186df1f0a64d8464b8103195902a5a5`, `check_all_crates` and `prove_normalize` check crate coherence, associated-type normalization, and NLL borrow rules (`crates/formality-rust/src/check/borrow_check/nll.rs`), while `codegen_program` lowers monomorphic `FnDef` graphs into its vendored `minirust-rs` representation (`libspecr = 0.1.40`). However, `TrustedFnBody` declarations are assumed valid without body proofs (`check/fns.rs:36`) and rejected by `resolve_fn_body` during codegen (`codegen/helpers.rs:104`), and no machine-checked soundness theorem exists in the 254-blob repository.
   - Executed Rust (`open_contract.rs` with and without `--cfg feature_flip`) and Python (`contract_model.py`) controls demonstrate why proof transport must bind resolved method/trait instances (`Wrapper::len` returning `2` via `Deref` vs. `99` via inherent method; `instance::<A, 1>() == 11` vs. `instance::<B, 1>() == 21`) and caller-side unsafe-trait domains (preventing a mutated implementation predicate from admitting 254 invalid `bool` bytes).
5. **RustBelt / RefinedRust Spatial Linking and Bad-Prefix Reflection (`minirust-rustbelt-spatial-linking-obligations-2026`):**
   - Direct inspection of the POPL 2018 $\lambda_{\text{Rust}}$ archive (`theories/typing/{type.v,soundness.v}`) and the 2026 RefinedRust Radium archive (`rust_typing/typing/adequacy.v:93-111`) shows that transferring adequacy to MiniRust requires **contrapositive bad-prefix reflection** ($B_{\text{MiniRust}}(C[L]) \implies B_{\text{Model}}(E(C[L]))$), mechanized without axioms in [`support/minirust-rustbelt-spatial-linking-obligations-2026/Bridge.lean`](support/minirust-rustbelt-spatial-linking-obligations-2026/Bridge.lean) (`Bridge.safety_transfer`, `Bridge.contextual_link`), along with counterexamples (`invalid_bool_erasure`, `invalid_tag_erasure`) proving that erasing byte validity or alias tags invalidates safety transfer. Safe Rust callback controls (`safe_clients.rs` — 65,536 `Cell<u8>` callback pairs and 153 slice-split cases) confirm that functional contracts across open callbacks must expose interior-mutable state transitions and exit-restoration invariants.

## Applicability

- **MiniRust and Specr (`minirust/minirust`, `minirust/specr`):**
  - `minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`, 368 tracked files verified).
  - `minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (`0.1.41`, archive SHA-256 `7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220`, 61 tracked files verified).
- **Rust compilers and Miri across covered versions:**
  - `rust-lang/rust` `nightly` (`rustc 1.97.0-nightly f53b654a8882fd5fc036c4ca7a4ff41ce32497a6` on `aarch64-apple-darwin`): required by `minirust/minirust`'s `rust-toolchain` file; succeeds in compiling `libspecr`, the generated `minirust_rs` core, `minimize`, `minirun`, and Miri (`-Zmiri-tree-borrows`).
  - `rust-lang/rust` `1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` on `aarch64-apple-darwin`, with `cargo 1.99.0 5f94df4789f005f9a352888e8355ffc645b7ed0e`): compiles the `specr` transpiler binary and the standalone safe Rust probes (`safe_clients.rs`, `open_contract.rs`, `probe.rs`), but fails to compile `libspecr` (`E0046` on unstable `Step` methods `forward_overflowing` and `backward_overflowing`).
  - `rust-lang/reference` at commits `2dafab96d919d6ab2884488e970bf95610ff83eb` and `ad35aca481751a06afeb23820a672b0f3b11a476`.
- **Comparative static and program-logic artifacts:**
  - `rust-lang/a-mir-formality` at commit `71dc31c1b186df1f0a64d8464b8103195902a5a5` (noting that its internal `crates/minirust-rs` depends on `libspecr = 0.1.40` and is distinct from `minirust/minirust@d821c6e`).
  - Original $\lambda_{\text{Rust}}$ / RustBelt POPL 2018 source archive (`lambda-rust-popl18.tar.gz`, SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`).
  - RefinedRust 2026 source artifact (Zenodo `21636474`, `artifact.tar.gz`, SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`).
  - `AeneasVerif/aeneas` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), `AeneasVerif/charon` (`0.1.210`, `a535e914f74db4fd9e6be7048f4233270d8945c0`), and `GillianPlatform/gillian-rust` (`83d739e83034d71162fb66b569041cf301123df7`).
  - Viktor Fukala's ETH Zürich Bachelor's thesis (*Formalization of Rust Drop Elaboration*, `2024-08-05`, reporting commit `120d9b3d1e868ddd00ce9163b2bb53d099154247`).
- **Lean 4 proof checker:** `leanprover/lean4` version `4.34.1` at commit `5045d0056413266e57c625dcd7c365b10e377c52`.

## Findings

### 1. Real Specr-Transpiled MiniRust Core Execution and Disagreement Probes (`minirust-actual-core-disagreement-evidence-d821c6e`)

**Basis:** `source`, `execution`, and `derived`

#### 1.1 Transpilation Pipeline and Compiler Version Boundary (`1.97.0-nightly` vs. `1.99.0`)

Running `specr-transpile` (`minirust/specr@15200eb5e676e2ee91f43bd79e674f8fc32e5348`) on `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` emits 5 Rust source files totaling 288,411 bytes (archived in [`support/minirust-actual-core-disagreement-evidence-d821c6e/generated/`](support/minirust-actual-core-disagreement-evidence-d821c6e/generated/)). Attempting to compile the generated crate and `libspecr` with `rustc 1.99.0` (`RUSTC_BOOTSTRAP=1`) fails in `libspecr` with `E0046` (missing `Step::forward_overflowing` and `Step::backward_overflowing`, logged in [`support/minirust-actual-core-disagreement-evidence-d821c6e/logs/build-core.log`](support/minirust-actual-core-disagreement-evidence-d821c6e/logs/build-core.log)). Compiling with the specification's pinned `rustc 1.97.0-nightly (f53b654a8 2026-05-01)` succeeds offline and locked in 10.43 seconds ([`support/minirust-actual-core-disagreement-evidence-d821c6e/logs/build-core-requested.log`](support/minirust-actual-core-disagreement-evidence-d821c6e/logs/build-core-requested.log)).

#### 1.2 Upstream `minitest` Suite (23 Tests) and Owned Core-API Probes (8 Cases)

Executing 23 upstream tests (`tests::no_preserve_padding::no_preserve_padding`, `tests::no_preserve_prov::no_preserve_prov`, 6 `tests::bool::*` tests, and 15 `tests::enum_representation::*` tests) and the 8 custom AST cases in [`support/minirust-actual-core-disagreement-evidence-d821c6e/actual_core_probe.rs`](support/minirust-actual-core-disagreement-evidence-d821c6e/actual_core_probe.rs) (`run_program::<BasicMem>` on `DefaultTarget = x86_64`, results in [`support/minirust-actual-core-disagreement-evidence-d821c6e/actual-results.json`](support/minirust-actual-core-disagreement-evidence-d821c6e/actual-results.json)) establishes:

| Probe Group / Case in `actual_core_probe.rs` | Observed Generated-Core Outcome (`BasicMem`, `x86_64`) | Technical Significance |
| :--- | :--- | :--- |
| `u8` byte `1` transmuted to `bool` | `MachineStop` | Valid Boolean representation (`0` or `1`) succeeds |
| `u8` byte `2` transmuted to `bool` | `Ub("transmuted value is not valid at new type")` | Core decode/validity check rejects non-Boolean byte `2` |
| Unchecked `u8` addition `255 + 1` | `Ub("overflow in unchecked add")` | Separates mathematical `Int` from bounded unchecked operator UB |
| 1-byte Enum (`Known(0)`), store variant `1`, load & assert discriminant `== 0` | `MachineStop` | Checker-admitted incoherent enum silently decodes encoded variant `1` as variant `0` |
| 1-byte Enum (`Known(0)`), store variant `1`, load & assert discriminant `== 1` | `Ub("reached unreachable code")` | Confirms variant `1` was lost during typed store/load round-trip |
| Coherent 1-byte Enum (`Branch`), store variant `1`, load & assert discriminant `== 1` | `MachineStop` | Coherent tag-reading discriminator preserves variant `1` |
| 16B Union (`*const [u8]`, length `3`) with `chunks = [(0, 16)]` | `MachineStop` | Full two-word chunk list preserves wide-pointer slice metadata (`len == 3`) |
| 16B Union (`*const [u8]`, length `3`) with `chunks = [(0, 8)]` | `Ub("transmuted value is not valid at new type")` | One-word chunk list resets bytes `8..16` to `Uninit`, destroying slice metadata |

---

### 2. End-to-End `minimize` Lowering vs. Miri Tree Borrows Across 19 Rust Sources (`minirust-source-lowering-miri-nineteen-cases-d821c6e`)

**Basis:** `source`, `execution`, and `derived`

Under `rustc 1.97.0-nightly (f53b654a8 2026-05-01)` (`aarch64-apple-darwin`, edition 2021, `-Zmir-emit-retag -Zmir-opt-level=0 -Zmir-enable-passes=-CheckAlignment -Zmir-preserve-ub -Zub-checks=false`), 19 Rust source fixtures ([`support/minirust-source-lowering-miri-nineteen-cases-d821c6e/case-index.json`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/case-index.json)) were evaluated in Miri (`-Zmiri-tree-borrows`) and lowered via `minimize` for execution under MiniRust `TreeBorrowsMemory` (`--minirust-tree-borrows`, `implicit_writes=false`) and `BasicMemory`:

| Fixture (`support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/`) | MiniRust Tree / Basic | Miri (`-Zmiri-tree-borrows`) | Root Cause / Mechanism |
| :--- | :--- | :--- | :--- |
| `smoke.rs`, `wide_pointer_control.rs`, `library_split_cell.rs`, `library_drop_count.rs` | `success` / `success` | `success` | Baseline scalar, wide-pointer, slice-split/`Cell`, and normal-return drop execution agree |
| `union_wide_one_field.rs` (`union U { p: *const [u8] }`, 16B) | **`UB` / `UB`** | **`success`** | `minimize` `calc_chunks` (`chunks.rs:47`) marks `Type::Ptr` as 8B (`chunks = [[0, 8]]`), resetting metadata bytes `8..16` to `Uninit`; MiniRust aborts with `UB: load at type Ptr(Raw { meta_kind: ElementCount })` |
| `union_wide_two_word_control.rs` (`union U { p: *const [u8], words: [usize; 2] }`) | `success` / `success` | `success` | Second field `[usize; 2]` forces `calc_chunks` to emit `chunks = [[0, 16]]`, preserving the metadata word |
| `enum_single_zero.rs`, `enum_pair_one.rs`, `upstream_pass_enum_direct_tag.rs`, `upstream_pass_enum_niche_tag.rs` | `success` / `success` | `success` | Valid single-variant, two-variant, direct-tag, and niche-tag enums succeed |
| `enum_single_invalid_one.rs`, `enum_pair_invalid_two.rs`, `upstream_ub_inv_bool.rs`, `upstream_ub_enum_ub_discriminant.rs` | `UB` / `UB` | `UB` | `minimize` lowers `#[repr(u8)] enum E { Only = 0 }` to `Discriminator::Branch` (`[0, 1) -> Known(0)`, `fallback = Invalid`), rejecting invalid tag `1` |
| `upstream_pass_slice.rs`, `upstream_pass_drop.rs`, `upstream_pass_tree_borrows_cell_inside_struct.rs` | `success` / `success` | `success` | Upstream slice, intrinsic-helper drop, and interior-mutable `Cell` reborrow tests agree |
| `library_box.rs`, `library_drop_unwind.rs` | **Lowering ICE (`exit 101`)** | `success` | `minimize` panics with `span_bug!` at `tooling/minimize/src/bb.rs:790` on foreign call `alloc::alloc::__rust_dealloc` (`library/alloc/src/alloc.rs:128`) |

---

### 3. Unwind Control, the `minimize` Destructor-Unwind Seam, and Drop Elaboration (`minirust-unwind-elaboration-and-open-client-obligations-d821c6e`)

**Basis:** `source`, `documentation`, `execution`, and `derived`

1. **Core unwind semantics vs. `minimize` `TerminatorKind::Drop` lowering (`spec/lang/step/terminators.md:405`, `tooling/minimize/src/bb.rs:220`):**
   - In MiniRust core, `StartUnwind` pushes a thin payload pointer onto the thread's unwind stack and enters a `Cleanup` basic block; `ResumeUnwind` pops the stack frame, deallocates locals, runs `mem.end_call(frame.extra)` (releasing active Tree Borrows protectors), and jumps to the caller's `unwind_block` (raising UB if `unwind_block` is `None`).
   - In `tooling/minimize/src/bb.rs:220`, however, `TerminatorKind::Drop { place, target, .. }` lowers to a MiniRust `Call` with `unwind_block: None`, discarding the MIR unwind edge! Executing the safe Rust specimen [`support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe.rs`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe.rs) (`rustc 1.99.0`, MIR retained in [`support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe-bin.mir`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe-bin.mir)) demonstrates both partial-move cleanup (`drops = ["left", "right", "outer"]`) and catching a panicking destructor (`drops = ["body", "bomb", "outer"]`), where MIR `main::{closure#2}` `bb7` emits `drop(_5) -> [return: bb8, unwind: bb12]` and `bb12` drops `outer` before resuming—an exceptional edge that `minimize`'s `Drop` branch erases.
2. **Scope of Viktor Fukala's 2024 drop-elaboration thesis:**
   Fukala's thesis (§§3, 5.3–5.4, 6.1) proves pre-/post-elaboration equivalence only for terminating executions over a value heap without enums or unwinding (with a complete proof for scalars and a proof skeleton with unproved lemmas for tuples). Because equivalence restricted to terminating runs cannot rule out a bad finite prefix that faults before termination, a safety-reflecting drop-elaboration theorem must preserve finite prefixes, partial initialization flags, alias protector exits, and unwind edges.

---

### 4. Static Judgments in `a-mir-formality` and Instance / Unsafe-Trait Controls (`minirust-static-judgments-and-open-contract-controls-2026`)

**Basis:** `source`, `execution`, and `derived`

1. **Implemented rules vs. trusted leaves in `a-mir-formality` (`71dc31c1b186df1f0a64d8464b8103195902a5a5`):**
   - `check_all_crates` (`crates/formality-rust/src/check/mod.rs:32`), `check_fn` (`check/fns.rs:36`), `prove_normalize` (`prove/prove_normalize.rs:22`), and `nll.rs` (`check/borrow_check/nll.rs:419,977`) implement crate coherence, existential associated-type normalization, and NLL loan/drop checking for a safe expression subset, while `codegen_program` (`codegen/mod.rs:32,307`) lowers monomorphic `FnDef` call graphs.
   - However, `TrustedFnBody` succeeds by assumption during type checking (`check/fns.rs:36`) and is rejected by `resolve_fn_body` during codegen (`codegen/helpers.rs:104`); `nll.rs:419` leaves `unsafe` blocks/calls as a `FIXME` and `nll.rs:977` omits owned-deref moves (`Box`); and `check/impls.rs:76` checks syntactic `Safety` markers without proving semantic unsafe-trait invariants.
2. **Observable subject-resolution and open-contract controls ([`open_contract.rs`](support/minirust-static-judgments-and-open-contract-controls-2026/open_contract.rs), [`contract_model.py`](support/minirust-static-judgments-and-open-contract-controls-2026/contract_model.py)):**
   - Compiling the exact same source file [`support/minirust-static-judgments-and-open-contract-controls-2026/open_contract.rs`](support/minirust-static-judgments-and-open-contract-controls-2026/open_contract.rs) without and with `--cfg feature_flip` ([`support/minirust-static-judgments-and-open-contract-controls-2026/runs/results.json`](support/minirust-static-judgments-and-open-contract-controls-2026/runs/results.json)) changes `Wrapper.len()` from `2` (via `Deref`) to `99` (via inherent method), while `instance::<A, 1>() == 11` vs. `instance::<B, 1>() == 21` and temporary drop-order pairs (`[10, 1]` vs. `[2, 20]`; `[30, 3, 40]` vs. `[4, 50, 60]`) confirm that proof certificates must bind resolved `FnDef` / impl / const / cfg / drop-scope identities rather than surface names.
   - In `contract_model.py`, mutating an implementation-supplied unsafe-trait validity predicate to `True` admits all 256 byte values (including 254 invalid `bool` bytes) unless the verification interface independently enforces the caller domain `{0, 1}`, and a dishonest `Vec` length premise (`len = 5` with 3 initialized elements) exposes `Uninit` at index `4` to a safe client.

---

### 5. RustBelt / RefinedRust Spatial Linking and Bad-Prefix Reflection (`minirust-rustbelt-spatial-linking-obligations-2026`)

**Basis:** `source`, `execution`, and `derived`

1. **Contrapositive bad-prefix reflection (`Bridge.lean`):**
   In [`support/minirust-rustbelt-spatial-linking-obligations-2026/Bridge.lean`](support/minirust-rustbelt-spatial-linking-obligations-2026/Bridge.lean), `Bridge.safety_transfer` and `Bridge.contextual_link` prove (with zero axioms) that to conclude concrete MiniRust safety ($\neg B_M(C[L])$) from a proved model's adequacy theorem ($\neg B_P(E(C[L]))$, such as $\lambda_{\text{Rust}}$ `type_soundness` in `theories/typing/soundness.v:28-32` or RefinedRust `refinedrust_adequacy` in `rust_typing/typing/adequacy.v:93-111`), the embedding $E$ must reflect every concrete bad prefix into an abstract bad prefix ($B_M(C[L]) \implies B_P(E(C[L]))$). Counterexamples `invalid_bool_erasure` and `invalid_tag_erasure` in `Bridge.lean` prove that forgetting byte-validity rules (`u8` value `2` as `bool`) or erasing alias-tag liveness breaks reflection.
2. **Open callback and interior-mutability contracts (`safe_clients.rs`):**
   Executing [`support/minirust-rustbelt-spatial-linking-obligations-2026/safe_clients.rs`](support/minirust-rustbelt-spatial-linking-obligations-2026/safe_clients.rs) (`rustc 1.99.0`, results in [`support/minirust-rustbelt-spatial-linking-obligations-2026/safe-client-results.json`](support/minirust-rustbelt-spatial-linking-obligations-2026/safe-client-results.json)) tests `callback_read`, which reads a `&Cell<u8>`, invokes an unknown safe callback retaining a shared `&Cell<u8>` alias that mutates the cell, and reads the cell again: across all 65,536 `(initial, final)` byte pairs, 65,280 pairs observe distinct pre- and post-callback reads. Consequently, any functional translation (such as Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727` or Gillian-Rust `83d739e83034d71162fb66b569041cf301123df7`) that models a shared reference across an open callback as an immutable value snapshot is unsound unless `UnsafeCell` sharing is excluded or threaded as an explicit state transition.

## Boundaries

- **Known not to apply:**
  - `rustc 1.99.0` cannot compile `minirust/specr@15200eb5e676e2ee91f43bd79e674f8fc32e5348` (`libspecr`) due to `E0046` on unstable `core::iter::Step` methods; the pinned `nightly` (`f53b654a8`) is required.
  - `minimize` (`d821c6e`) does not preserve the second word of a 1-field wide-pointer union (`union_wide_one_field.rs` fails with false-positive UB in MiniRust while passing Miri) and does not preserve MIR unwind edges on `TerminatorKind::Drop` (`tooling/minimize/src/bb.rs:220`).
  - Erasing byte validity or alias tags in a $\lambda_{\text{Rust}}$ / iris bridge fails bad-prefix reflection (`Bridge.invalid_bool_erasure`, `Bridge.invalid_tag_erasure`), and treating `&Cell<T>` as immutable across an unknown safe callback is refuted by `safe_clients.rs`.
- **Not examined:**
  - First-bad-prefix preservation across optimizing `rustc` MIR passes (`-Zmir-opt-level > 0`), and patched repairs to `minimize`'s `calc_chunks` across nested unions or custom DSTs.
  - Differential MiniRust vs. Miri execution for exposed-provenance `int2ptr` (`predict`), concurrent data races, or reentrant FFI callbacks.
  - Executing `a-mir-formality`'s CLI or codegen directly (all `a-mir-formality` findings are from static source inspection of commit `71dc31c1b186df1f0a64d8464b8103195902a5a5`).
- **Unsupported in inspected `minimize` (`d821c6e`):**
  - Foreign allocator calls (`alloc::alloc::__rust_dealloc` ICE at `tooling/minimize/src/bb.rs:790` in `library_box.rs` and `library_drop_unwind.rs`) and `UnwindTerminate`, `Yield`, and `CoroutineDrop` terminators.
- **Unknown:**
  - Whether an upstream theorem or external proof artifact exists outside `rust-lang/a-mir-formality@71dc31c1b186df1f0a64d8464b8103195902a5a5` connecting `formality-rust` derivations to MiniRust operational safety.

## Evidence

1. **Actual Specr-generated MiniRust core build, 23 upstream tests, and 8 custom AST probes (`support/minirust-actual-core-disagreement-evidence-d821c6e/`, observed `2026-10-14`):**
   - Generated Rust core and manifest: [`support/minirust-actual-core-disagreement-evidence-d821c6e/generated/lib.rs`](support/minirust-actual-core-disagreement-evidence-d821c6e/generated/lib.rs), [`lang.rs`](support/minirust-actual-core-disagreement-evidence-d821c6e/generated/lang.rs), [`mem.rs`](support/minirust-actual-core-disagreement-evidence-d821c6e/generated/mem.rs), [`prelude.rs`](support/minirust-actual-core-disagreement-evidence-d821c6e/generated/prelude.rs), and [`observed-Cargo.toml`](support/minirust-actual-core-disagreement-evidence-d821c6e/generated/observed-Cargo.toml).
   - Retained upstream source archives and lockfiles: [`support/minirust-actual-core-disagreement-evidence-d821c6e/archives/minirust.tar.gz`](support/minirust-actual-core-disagreement-evidence-d821c6e/archives/minirust.tar.gz), [`archives/specr.tar.gz`](support/minirust-actual-core-disagreement-evidence-d821c6e/archives/specr.tar.gz), and [`locks/harness.Cargo.lock`](support/minirust-actual-core-disagreement-evidence-d821c6e/locks/harness.Cargo.lock).
   - Custom probe, replay helper, and results: [`support/minirust-actual-core-disagreement-evidence-d821c6e/actual_core_probe.rs`](support/minirust-actual-core-disagreement-evidence-d821c6e/actual_core_probe.rs), [`prepare_replay.py`](support/minirust-actual-core-disagreement-evidence-d821c6e/prepare_replay.py), [`actual-results.json`](support/minirust-actual-core-disagreement-evidence-d821c6e/actual-results.json), and [`status/selected-test-results.json`](support/minirust-actual-core-disagreement-evidence-d821c6e/status/selected-test-results.json).
2. **19-case `minimize` lowering and Miri Tree Borrows differential corpus (`support/minirust-source-lowering-miri-nineteen-cases-d821c6e/`, observed `2026-10-14`):**
   - Master index and representation diagnosis: [`support/minirust-source-lowering-miri-nineteen-cases-d821c6e/case-index.json`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/case-index.json), [`representation-findings.json`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/representation-findings.json), [`source-copy-revalidation.json`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/source-copy-revalidation.json), and [`normalization-receipts.json`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/normalization-receipts.json).
   - Key fixture sources: [`cases/union_wide_one_field.rs`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/union_wide_one_field.rs), [`cases/union_wide_two_word_control.rs`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/union_wide_two_word_control.rs), [`cases/enum_single_zero.rs`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/enum_single_zero.rs), [`cases/enum_single_invalid_one.rs`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/enum_single_invalid_one.rs), [`cases/library_box.rs`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/library_box.rs), and [`cases/library_drop_unwind.rs`](support/minirust-source-lowering-miri-nineteen-cases-d821c6e/cases/library_drop_unwind.rs).
3. **Unwind elaboration and destructor-unwind MIR evidence (`support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/`, observed `2026-10-14`):**
   - [`support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe.rs`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe.rs), [`probe-bin.mir`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/probe-bin.mir), [`results.txt`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/results.txt), [`execution.json`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/execution.json), and [`source-evidence.json`](support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e/source-evidence.json).
4. **Static judgments (`a-mir-formality`) and open-contract controls (`support/minirust-static-judgments-and-open-contract-controls-2026/`, observed `2026-10-14`):**
   - [`support/minirust-static-judgments-and-open-contract-controls-2026/open_contract.rs`](support/minirust-static-judgments-and-open-contract-controls-2026/open_contract.rs), [`contract_model.py`](support/minirust-static-judgments-and-open-contract-controls-2026/contract_model.py), [`revalidate.py`](support/minirust-static-judgments-and-open-contract-controls-2026/revalidate.py), [`runs/results.json`](support/minirust-static-judgments-and-open-contract-controls-2026/runs/results.json), [`runs/default.mir`](support/minirust-static-judgments-and-open-contract-controls-2026/runs/default.mir), [`runs/flipped.mir`](support/minirust-static-judgments-and-open-contract-controls-2026/runs/flipped.mir), and [`source-evidence.json`](support/minirust-static-judgments-and-open-contract-controls-2026/source-evidence.json).
5. **RustBelt / RefinedRust spatial linking and bad-prefix reflection (`support/minirust-rustbelt-spatial-linking-obligations-2026/`, observed `2026-10-14`):**
   - [`support/minirust-rustbelt-spatial-linking-obligations-2026/Bridge.lean`](support/minirust-rustbelt-spatial-linking-obligations-2026/Bridge.lean), [`lean.log`](support/minirust-rustbelt-spatial-linking-obligations-2026/lean.log), [`safe_clients.rs`](support/minirust-rustbelt-spatial-linking-obligations-2026/safe_clients.rs), [`safe_clients.mir`](support/minirust-rustbelt-spatial-linking-obligations-2026/safe_clients.mir), [`safe-client-results.json`](support/minirust-rustbelt-spatial-linking-obligations-2026/safe-client-results.json), and [`source-evidence.json`](support/minirust-rustbelt-spatial-linking-obligations-2026/source-evidence.json).

## Revalidation

To re-verify the Lean 4 spatial-linking bridge (`Bridge.lean`), the three standalone safe Rust probes (`safe_clients.rs`, `open_contract.rs`, `probe.rs`), the Python open-contract model (`contract_model.py`), and the static SHA-256 integrity of the 19-case `minimize`/Miri corpus from the repository root:

```bash
python3 - <<'EOF'
import hashlib, json, pathlib, subprocess, tempfile

pkg = pathlib.Path("reports/minirust-source-lowering-miri-differential-and-open-contract-boundaries")

# 1. Re-verify Bridge.lean and safe_clients.rs
sup_rb = pkg / "support/minirust-rustbelt-spatial-linking-obligations-2026"
subprocess.run(["lean", "-j1", "-M1024", str(sup_rb / "Bridge.lean")], check=True)
with tempfile.TemporaryDirectory() as tmp:
    bin_path = pathlib.Path(tmp) / "safe_clients"
    subprocess.run(["rustc", "--edition=2021", str(sup_rb / "safe_clients.rs"), "-o", str(bin_path)], check=True)
    subprocess.run([str(bin_path)], stdout=subprocess.DEVNULL, check=True)

# 2. Re-verify open_contract.rs (default and --cfg feature_flip) and contract_model.py
sup_oc = pkg / "support/minirust-static-judgments-and-open-contract-controls-2026"
subprocess.run(["python3", str(sup_oc / "contract_model.py")], stdout=subprocess.DEVNULL, check=True)
with tempfile.TemporaryDirectory() as tmp:
    b1 = pathlib.Path(tmp) / "oc_default"
    b2 = pathlib.Path(tmp) / "oc_flipped"
    subprocess.run(["rustc", "--edition=2024", "-O", str(sup_oc / "open_contract.rs"), "-o", str(b1)], check=True)
    subprocess.run([str(b1)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
    subprocess.run(["rustc", "--edition=2024", "-O", "--cfg", "feature_flip", str(sup_oc / "open_contract.rs"), "-o", str(b2)], check=True)
    subprocess.run([str(b2)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)

# 3. Re-verify unwind/drop probe.rs
sup_uw = pkg / "support/minirust-unwind-elaboration-and-open-client-obligations-d821c6e"
with tempfile.TemporaryDirectory() as tmp:
    bp = pathlib.Path(tmp) / "unwind_probe"
    subprocess.run(["rustc", "--edition=2021", str(sup_uw / "probe.rs"), "-o", str(bp)], check=True)
    subprocess.run([str(bp)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)

# 4. Verify 19-case minimize/Miri corpus manifest hashes
sup_19 = pkg / "support/minirust-source-lowering-miri-nineteen-cases-d821c6e"
manifest = json.loads((sup_19 / "package-manifest.json").read_text())
for entry in manifest.get("files", []):
    rel = entry["path"]
    if rel == "REPORT.md" or rel == "REPORT.json":
        continue
    fpath = sup_19 / rel
    assert fpath.is_file(), f"Missing {fpath}"
    digest = hashlib.sha256(fpath.read_bytes()).hexdigest()
    assert digest == entry["sha256"], f"Hash mismatch on {rel}"
print("OK: Bridge.lean, 3 safe Rust probes, contract_model.py, and 19-case corpus hashes verified.")
EOF
```

To stage and replay the 8-case generated-core harness offline under `rustc 1.97.0-nightly (f53b654a8 2026-05-01)`, run `python3 reports/minirust-source-lowering-miri-differential-and-open-contract-boundaries/support/minirust-actual-core-disagreement-evidence-d821c6e/prepare_replay.py --work <temp-dir>`. Revalidate this package when `minirust/minirust` advances beyond `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `minirust/specr` advances beyond `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, or `rust-lang/a-mir-formality` advances beyond `71dc31c1b186df1f0a64d8464b8103195902a5a5`.
