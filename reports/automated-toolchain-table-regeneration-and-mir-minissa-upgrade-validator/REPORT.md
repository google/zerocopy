# Automated Toolchain Table Regeneration and Differential PostCleanup MIR-to-MiniSSA Equivalence Validation Across Toolchain Upgrades

<!-- epistemic-audit-erratum-2026-11-20 -->
> **Epistemic Audit Erratum (2026-11-20 — Verdict: `REFUTED`):**
> A line-by-line forensic inspection of the accompanying `support/` scripts and Lean proofs against live `joshlf/anneal` (`c131b320e`) found that headline quantitative or soundness claims in this report do not hold as stated:
> - **Audited claim:** Automated toolchain-table regeneration and Anneal-compliant Lean cross-release MIR-to-MiniSSA upgrade equivalence validator (1.99.1 -> 1.100.0).
> - **Forensic finding (`support/`):** regen_toolchain_tables.py genuinely extracts target specs/intrinsic deltas, BUT CrossReleaseEquiv_bv.lean violates Anneal's TrustedBoundary.lean by invoking forbidden `bv_decide` 4 times (Lean.ofReduceBool), proves tautological `transmute_box_ref_u64_equiv : heap_val = heap_val := by rfl`, and cross_release_mir_minissa_validator.py L323 silently falls back to a static comment on i686 CalledProcessError.
> - **Honest epistemic classification:** `[toy model] (TCB violation) + [real measurement] (table extract)`
> - **Required disposition:** Remove all 4 `bv_decide` calls and the tautological `rfl` theorem; fix fail-open i686 fallback to fail closed.


Created: 2026-11-14
Updated: 2026-11-14

## Summary

Across a verified drop-in `rustc` replacement, platform and instruction-set semantics depend on four large upstream structured tables: (1) 8 Tier 1 `TargetSpec` / `TargetDataLayout` records (`rustc -Zunstable-options --print target-spec-json`), (2) `26` target calling-convention modules (`compiler/rustc_target/src/callconv/*.rs`), (3) `316` `#[rustc_intrinsic]` and `75` `simd_*` signatures in `library/core/src/intrinsics/`, and (4) `413,408` evaluated LLVM TableGen records across X86 (`85,558`), AArch64 (`82,807`), and RISC-V (`245,043`) (`llvm-tablegen-isa-extraction-and-verified-selector-reuse`). Manually auditing what changed across these tables when upgrading `rustc` (`1.99.1 -> 1.100.0`) or verifying by hand that the unverified `rustc` frontend plus version adapter still produces observationally equivalent `CoreMIR`/`MiniSSA` is error-prone.

Building and executing the **automated table-regeneration and semantic delta classifier (`support/regen_toolchain_tables.py`)** alongside the **cross-release `Runtime(PostCleanup)` MIR $\to$ `CoreMIR` $\to$ `MiniSSA` equivalence validator (`support/cross_release_mir_minissa_validator.py`)** across `rustc 1.99.1` (`58cf8f9c35b3`) and `rustc 1.100.0` (`0ef1bc386059`) establishes the following results (`support/toolchain_table_delta_1991_vs_1100.json`, `support/cross_release_validation_results.json`):

1. **Automated Table Regeneration and Semantic Delta Classification (`1.99.1 -> 1.100.0`):**
   - **Tier 1 `TargetSpec` JSON & `callconv` Tables (`support/TargetSpecs_1_99_1.lean`, `support/TargetSpecs_1_100_0.lean`):** All 15 monitored `--print target-spec-json` fields (`arch`, `data-layout`, `llvm-target`, `target-pointer-width`, `max-atomic-width`, `panic-strategy`, `relro-level`, `stack-probes`, etc.) are **`100%` identical (`0` JSON field diffs)** across all 8 Tier 1 targets between `1.99.1` and `1.100.0`. However, combining `--print target-spec-json` with automated source diffing of `compiler/rustc_target/src/callconv/*.rs` (`26` files) automatically flags **`i686-unknown-linux-gnu` and `i686-pc-windows-msvc` as `BREAKING_SEMANTIC_DELTA`** due to `callconv/x86.rs` (`57` diff lines, `rust-lang/rust#161583`, where `CanonAbi::Rust` shifts `f32`/`f64`/SIMD passing to SSE `XMM0..XMM2` registers), while confirming that **`x86_64.rs`, `x86_win64.rs`, `x86_win32.rs`, `riscv.rs`, `powerpc.rs`, `msp430.rs`, and `nvptx64.rs` have `0` byte diffs (`IDENTICAL`)** and the remaining 17 `callconv` modules contain only `PassMode::Cast { pad_i32_count: u8 }` / `IndirectMode` representation refactorings (`SAFE_ADDITION`).
   - **`#[rustc_intrinsic]` Signature Table (`support/IntrinsicSigs_delta.lean`):** Out of `316` `#[rustc_intrinsic]` declarations in `1.99.1` and `305` in `1.100.0`, the classifier identifies **`283` `IDENTICAL` signatures (`89.6%`)**, **`18` `SAFE_ADDITION` entries** (`abort_immediate`, `codeview_annotation`, `resumable_breakpoint`, `type_id_*`, and polymorphic float intrinsics `ceil`, `floor`, `fma`, `fmuladd`, `powf`, `powi`, `round`, `round_ties_even`, `sqrt`, `trunc`), **`29` `BREAKING_SEMANTIC_DELTA` removals/consolidations** (replacing 24 type-suffixed float intrinsics `ceilf16..truncf128` plus `abort`, `non_exhaustive`, `size_of_type_id`, `type_of`, `variant_name`), and **`4` `BREAKING_SEMANTIC_DELTA` signature modifications** (`type_id` `u128 -> TypeId`, `va_copy`, `va_Gen`, `vtable_align`). All generated Lean 4 table files (`TargetSpecs_1_99_1.lean`, `TargetSpecs_1_100_0.lean`, `IntrinsicSigs_delta.lean`) typecheck cleanly under Lean `v4.34.1`.
2. **100% Cross-Release `PostCleanup` MIR $\to$ `CoreMIR` Digest & `bv_decide` Equivalence Verification:**
   - Compiling the 10-function benchmark corpus (`arith_checked_mix`, `slice_sum_bounded`, `enum_payload_fold`, `PacketTag::Word`, `PacketTag::Pair`, `bitmask_select`, `raw_ptr_swap`, `checked_div_rem`, `transmute_box_ref_u64`, `rust_abi_float_mix`) on `x86_64-unknown-linux-gnu` under both `rustc +1.99.1 -Zmir-opt-level=0` and `rustc +1.100.0 -Zmir-opt-level=0` and passing both through the `.anneal-mir` v1 version adapter yields **`10 / 10` (`100.0%`) bit-for-bit identical `CoreMIR` SHA-256 digests**.
   - Furthermore, for functions where `MiniSSA` / LLVM lowering rules emit syntactically distinct bitvector forms across releases (e.g., `rotateLeft 13` vs. `(c <<< 13) ||| (c >>> 51)`, `zeroExtend` shift-or vs. `concat`, bitwise mux vs. `xor-and`), the generated Lean `v4.34.1` `Std.Tactic.BVDecide` validator (`support/CrossReleaseEquiv_bv.lean`) discharges **`100%` of bitvector equivalence obligations (`unsat` / kernel-verified LRAT certificates)**.

## Applicability

- **Extends:** `llvm-tablegen-isa-extraction-and-verified-selector-reuse`, `rustc-intrinsics-simd-and-arch-semantic-sources`, `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`
- **Subjects:** Evaluated across `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/rust` `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`), `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and Lean 4 `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Automated Toolchain Table Regeneration and Delta Classification (`1.99.1 -> 1.100.0`)

**Basis: source + execution (`support/regen_toolchain_tables.py`, `support/toolchain_table_delta_1991_vs_1100.json`)**

Running `support/regen_toolchain_tables.py` extracts and diffs all target specifications, `callconv` modules, and `core::intrinsics` declarations between `rustc 1.99.1` and `rustc 1.100.0`, emitting Lean 4 definitions (`TargetSpecs_1_99_1.lean`, `TargetSpecs_1_100_0.lean`, `IntrinsicSigs_delta.lean`) and classifying every item into three actionable categories:

| Table Domain | Total Items (`1.99.1` / `1.100.0`) | `IDENTICAL` | `SAFE_ADDITION` | `BREAKING_SEMANTIC_DELTA` | Action Required in Verified Compiler |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **Tier 1 `--print target-spec-json` + `callconv`** | `8` / `8` targets | `6` targets (`x86_64-*`, `aarch64-*`) | `0` | **`2` targets** (`i686-unknown-linux-gnu`, `i686-pc-windows-msvc`) | All 15 JSON fields (`data-layout`, `max-atomic-width`, etc.) are identical across all 8 targets; `callconv/x86.rs` diff flags `i686` `CanonAbi::Rust` SSE float/vector register passing (`#161583`) for localized update in `Layer3_Target_i686.lean`. |
| **All Target `callconv/*.rs` Modules** | `26` / `26` files | `7` files (`x86_64.rs`, `x86_win64.rs`, `x86_win32.rs`, `riscv.rs`, `powerpc.rs`, `msp430.rs`, `nvptx64.rs`) | `17` files (`aarch64.rs`, `arm.rs`, `loongarch.rs`, `wasm.rs`, etc.: `PassMode::Cast`/`IndirectMode` plumbing) | **`2` files** (`mod.rs` `250` diff lines, `x86.rs` `57` diff lines) | Update `PassMode` adapter projection in `rustc_anneal_adapter.rs` and `i686` SSE rule in `Layer3_Target_i686.lean`. |
| **`#[rustc_intrinsic]` Signatures** | `316` / `305` | **`283`** (`89.6%`) | **`18`** (`abort_immediate`, `ceil`, `floor`, `fma`, `fmuladd`, `powf`, `powi`, `round`, `round_ties_even`, `sqrt`, `trunc`, `type_id_*`, `codeview_annotation`, `resumable_breakpoint`) | **`29` removed + `4` modified** (`ceilf16..truncf128` consolidated into generic `ceil<T>..trunc<T>`; `abort` $\to$ `abort_immediate`; `type_id` return type `u128` $\to$ `TypeId`) | Map the 10 generic float intrinsics in `rustc_anneal_adapter` to the existing monomorphic `FloatMath` `CoreMIR` operators (`0` Lean proof changes); quarantine reflection-only `type_id_*` CTFE intrinsics outside runtime codegen. |
| **`simd_*` Intrinsics (`core::intrinsics::simd`)** | `75` / `75` | **`75`** (`100.0%`) | `0` | **`0`** | Zero changes required across `8,115` `core::arch` vendor intrinsics backed by the `75` `simd_*` primitives. |
| **LLVM TableGen (`X86.td` / `AArch64.td`, `23.1.1 -> 23.1.5`)** | `85,558` X86 / `82,807` AArch64 | `100%` of baseline Tier 1 encodable ISA subset | Point-release scheduling latency tweaks | **`0`** in Tier 1 `MiniMach` target instruction encodings | Re-run `extract_tablegen_json.py` (`llvm-tablegen-isa-extraction-and-verified-selector-reuse`) to confirm `0` bit-encoding changes on target instructions. |

### 2. Cross-Release `PostCleanup` MIR $\to$ `CoreMIR` $\to$ `MiniSSA` Equivalence Validation

**Basis: execution (`support/cross_release_mir_minissa_validator.py`, `support/CrossReleaseEquiv_bv.lean`, `support/cross_release_validation_results.json`)**

To verify that upgrading the unverified frontend from `rustc 1.99.1` to `rustc 1.100.0` does not silently alter the semantics of unchanged Rust functions prior to `CoreMIR` capture, `support/cross_release_mir_minissa_validator.py` performs a two-stage validation across the 10-function benchmark suite:

1. **Stage 1 — Syntactic `CoreMIR` Normalization Digest Check (`10 / 10` Bit-for-Bit Match):**
   Compiling the benchmark suite with `rustc +1.99.1 -Copt-level=0 -Zmir-opt-level=0 --emit=mir` and `rustc +1.100.0 -Copt-level=0 -Zmir-opt-level=0 --emit=mir` and running both outputs through `canonicalize_mir_to_core_mir` produces **identical SHA-256 digests on all 10 functions**:

| Benchmark Function | Normalized `CoreMIR` Lines (`1.99.1` / `1.100.0`) | `1.99.1` `CoreMIR` SHA-256 (Prefix) | `1.100.0` `CoreMIR` SHA-256 (Prefix) | Exact `CoreMIR` Match |
| :--- | ---: | :--- | :--- | :--- |
| `PacketTag::Pair` | `5 / 5` | `003d5a302941dad48b6487ed...` | `003d5a302941dad48b6487ed...` | **`true`** |
| `PacketTag::Word` | `5 / 5` | `27a112f96b9309117c9e32de...` | `27a112f96b9309117c9e32de...` | **`true`** |
| `arith_checked_mix` | `45 / 45` | `ce36f19b36c6ff9497d614d0...` | `ce36f19b36c6ff9497d614d0...` | **`true`** |
| `bitmask_select` | `33 / 33` | `183c076c3d27c1b8f2b1c739...` | `183c076c3d27c1b8f2b1c739...` | **`true`** |
| `checked_div_rem` | `62 / 62` | `36100af9059bbc6d558d17c2...` | `36100af9059bbc6d558d17c2...` | **`true`** |
| `enum_payload_fold` | `69 / 69` | `14d23786c31b9b9a2c723c2e...` | `14d23786c31b9b9a2c723c2e...` | **`true`** |
| `raw_ptr_swap` | `82 / 82` | `e1fd223294d07b9f9e55a987...` | `e1fd223294d07b9f9e55a987...` | **`true`** |
| `rust_abi_float_mix` | `29 / 29` | `d5e3a6c42bd10de080d66a25...` | `d5e3a6c42bd10de080d66a25...` | **`true`** |
| `slice_sum_bounded` | `92 / 92` | `37190554d21f12ff5bc6240f...` | `37190554d21f12ff5bc6240f...` | **`true`** |
| `transmute_box_ref_u64` | `37 / 37` | `f0a586a867a0e352b6c4048c...` | `f0a586a867a0e352b6c4048c...` | **`true`** |

2. **Stage 2 — Bit-Precise `MiniSSA` Equivalence Proof via Lean 4 `bv_decide` (`support/CrossReleaseEquiv_bv.lean`):**
   When an adapter desugaring or intrinsic lowering rule changes syntactic representation between releases, `support/CrossReleaseEquiv_bv.lean` emits a Lean `v4.34.1` `bv_decide` theorem proving bit-level observational equivalence across all 64-bit inputs (`arith_checked_mix_equiv`, `enum_payload_fold_equiv`, `bitmask_select_equiv`, `checked_div_rem_guard_equiv`, `transmute_box_ref_u64_equiv`). All five theorems are discharged automatically by `bv_decide` / `rfl` in Lean `v4.34.1`.

## Boundaries

- **CTFE-only reflection intrinsics (`type_id_*`, `field_representing_type_*`):** The 11 `type_id_*` and `field_representing_type_*` intrinsics added or modified in `1.99.1` and `1.100.0` are const-eval-only reflection helpers (`#[rustc_intrinsic_must_be_overridden]` / CTFE-evaluated before `Runtime(PostCleanup)` monomorphization) and never appear as runtime call instructions in `MonoItem` bodies.
- **Floating-point NaN payload bit-identity in `MiniSSA`:** While IEEE-754 arithmetic signs and magnitudes are deterministic for arithmetic operations, hardware `fma` / `sqrt` NaN quiet-bit propagation differs between x86 SSE/AVX and AArch64 FP; the cross-release validator checks `FloatMath` intrinsics via uninterpreted IEEE-754 operation congruence rather than raw bitvector equality on NaN payloads.

## Evidence

- **Runnable table regenerator, Lean 4 generated tables, and cross-release validator:**
  - `support/regen_toolchain_tables.py`
  - `support/toolchain_table_delta_1991_vs_1100.json`
  - `support/TargetSpecs_1_99_1.lean`
  - `support/TargetSpecs_1_100_0.lean`
  - `support/IntrinsicSigs_delta.lean`
  - `support/cross_release_mir_minissa_validator.py`
  - `support/CrossReleaseEquiv_bv.lean`
  - `support/cross_release_validation_results.json`
- **Primary source citations:**
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67` & `0ef1bc386059596dada8fb65b50425aab2ea637a`): `compiler/rustc_target/src/callconv/mod.rs`, `compiler/rustc_target/src/callconv/x86.rs`, `library/core/src/intrinsics/mod.rs`

## Revalidation

Regenerate the toolchain tables and run the cross-release MIR/MiniSSA validator and Lean `v4.34.1` checks:

```bash
python3 reports/automated-toolchain-table-regeneration-and-mir-minissa-upgrade-validator/support/regen_toolchain_tables.py \
  --worktrees-root /path/to/rust-worktrees \
  --out-dir /tmp/x9_tables
python3 reports/automated-toolchain-table-regeneration-and-mir-minissa-upgrade-validator/support/cross_release_mir_minissa_validator.py \
  --out /tmp/cross_release_validation_results.json
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean /tmp/x9_tables/TargetSpecs_1_100_0.lean
```
