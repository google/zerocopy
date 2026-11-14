# Hardware LBR AutoFDO Sample Profile Ingestion (`.anneal_site_map` / `anneal-profgen`), Machine-Branch Polarity Un-Flipping, and Minimum-Cost Circulation Flow Smoothing

## Summary

While deterministic instrumentation-based Profile-Guided Optimization (`-C profile-generate` / `.anneal-prof` in `mutation-resilient-polarity-safe-ir-portable-pgo`) eliminates stale-profile cliffs for staged benchmark builds, production fleet deployments rely on zero-overhead hardware PMU Last Branch Record (LBR) and Arm Statistical Profiling Extension (SPE) sample profiles (`perf record -b` $\rightarrow$ `llvm-profgen` $\rightarrow$ `rustc -Z profile-sample-use=<path>`, implemented in `compiler/rustc_session/src/options.rs:2773-2774` and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:686-695`). In `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), standard sample-based AutoFDO suffers three structural failure modes (`support/anneal_profgen_sim.py`, `support/lbr_skid_and_mutation_results.json`):

1. **DWARF Line-Offset and Crate-Metadata Fragility Under Source Edits (`M1`–`M4`)**:
   - Standard `-Z profile-sample-use` (paired with `-C debuginfo=1 -Z debuginfo-for-profiling=yes`) keys functions by the v0 crate-hash-mangled symbol (`_RNvCs<crate_hash>_...`) and keys internal basic blocks and call targets by relative source line offsets and DWARF discriminators (`LineLocation(LineOffset, Discriminator)` in `SampleProfile.cpp`).
   - Across our 5-scenario mutation benchmark (`support/lbr_autofdo_benchmark.csv`), inserting a 3-line early-return guard at the top of `<OpFastAdd as StageOp>::execute` (`M1_InsertEarlyReturnShiftLineOffsets`) shifts all downstream DWARF line offsets by `+4` lines (`line 4` $\rightarrow$ `line 8`, `line 8` $\rightarrow$ `line 12`), misassociating the cold branch weight with the hot body and collapsing `-Z profile-sample-use` retained PGO speedup from **`99.6%` (`+78.34%` speedup)** to **`-8.6%` (`-6.75%` regression, `48.60` $\mu\text{s}$ $\rightarrow$ `239.53` $\mu\text{s}`)**.
   - Negating branch conditions and swapping arms (`M2_NegateBranchConditionAndSwapArms`), extracting an inlined slice helper (`M3`), or changing `-C metadata` (`M4_CrateMetadataDrift`) similarly collapses `-Z profile-sample-use` retained PGO gain to **`9.7%`**, **`9.5%`**, and **`17.3%`**, respectively.
2. **Machine-Level Conditional Jump Polarity Inversion (`machine_branch_inverted_bit`)**:
   - When the backend lowers a MIR `SwitchInt(cond)` equality test (`if (x & 0x7f) == 0 { cold() } else { hot() }`) into an inverted hardware conditional jump (`testb $0x7f, %dil; jne .L_hot`), hardware LBR `taken` branch records (`from_ip -> to_ip`) count the MIR `false` arm (`(x & 0x7f) != 0`), while `not-taken` fallthrough ranges count the MIR `true` arm (`== 0`). Across the 14 branch sites in the 8-function benchmark suite, **`10 / 14` (`71.4%`) of machine conditional branches invert the source MIR predicate polarity**.
3. **PMU Instruction-Pointer Skid and Non-Conserving Edge Flows (`Regime S2`)**:
   - Under `15%` PMU IP skid ($\pm 1\text{--}2$ instructions spilling hot branch IP samples into adjacent fallthrough blocks) and `20%` fallthrough range dropout (`Regime S2`), raw un-smoothed LBR counts violate Kirchhoff flow conservation ($\sum_{e \in \text{in}(u)} \hat{w}(e) \neq \sum_{e \in \text{out}(u)} \hat{w}(e)$, with raw residuals of `94` to `5,016` across $100\text{--}5,000$ samples/function) and suffer mean branch-probability $L_1$ errors of `0.0440`–`0.0557` (`0.0595`–`0.0658` under `llvm-profgen`).

This report specifies, prototypes, and mechanizes in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) **`anneal-profgen`**, a hardware LBR sample profile ingester and **Minimum-Cost Circulation Flow Smoother (`CirculationSmoother`)** that maps hardware LBR stacks directly into `AnnealProfV1` (`mutation-resilient-polarity-safe-ir-portable-pgo`):
- **Zero-Overhead `.anneal_site_map` ELF Section and Dual Inline-Stack Attribution**: Emits a compact `32`-byte per-block non-`SHF_ALLOC` `.anneal_site_map` table recording `(pc_range_start, pc_range_end, inline_stack_id, canonical_item_key, site_anchor_key, machine_branch_inverted_bit)`. `anneal-profgen` un-flips hardware `taken`/`not-taken` counts via `machine_branch_inverted_bit`, attributes inlined ranges to both the caller's `InlineContextChain` and the un-inlined callee's `CanonicalItemKey`, and resolves LBR indirect-call `(call_site_ip, target_entry_ip)` pairs via `.symtab` to `CanonicalItemKey` at **`99.64%` accuracy** (`4,982 / 5,000` samples), feeding `VP-2` and `VP-3` value-profile specialization certificates without instrumentation counters.
- **Minimum-Cost Circulation Flow Smoothing (`CirculationSmoother`)**: Solves the confidence-weighted $L_1$ circulation problem on each function's CFG in **`0.020`–`0.033 ms`**, eliminating **`100%` of Kirchhoff flow-conservation residuals (`post_kirchhoff_residual = 0`)**, reducing PMU skid branch-probability $L_1$ error by **`75.53%`–`80.54%` vs. raw LBR** (**`81.91%`–`84.89%` vs. `llvm-profgen`**), and retaining **`99.5%`–`100.0%` of full PGO runtime speedup (`+78.32%` to `+78.71%` speedup, `47.77`–`48.66` $\mu\text{s}$)** across all source mutations `M0`–`M4`.
- **Mechanized Lean `v4.34.1` Proofs (`support/lean/AutoFdoCirculationAndPolarity.lean`, `9` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`)**: Proves Kirchhoff conservation under linear combinations and residual cycle augmentations (`applyResidualCycle_preserves_circulation`), machine-to-MIR polarity un-flipping involutivity and exactness (`unflipMachineBranch_involutive`, `lbr_polarity_transfer_sound`), `.symtab` indirect-target resolution soundness (`lbr_indirect_target_resolution_sound`), and end-to-end `AnnealProfV1WellFormed` validity (`circulationSmoother_produces_valid_anneal_prof`).

## Applicability

- **Subjects**:
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
  - `joshlf/anneal` (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`)
- **Targets and flags examined**: `x86_64-unknown-linux-gnu` with `-C opt-level=3`, `-C debuginfo=1`, `-Z debuginfo-for-profiling=yes`, and `-Z profile-sample-use=<path>` (note that on stable `rustc` 1.99.1, both `-Z debuginfo-for-profiling=yes` and `-Z profile-sample-use` are gated behind `RUSTC_BOOTSTRAP=1`).
- **Relationship to other corpus packages**: Extends `mutation-resilient-polarity-safe-ir-portable-pgo`, `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, and `value-profile-specialization-and-hybridtrace-guard-certificates`.

## Findings

### 1. Mechanics and Fragility of `rustc 1.99.1` `-Z profile-sample-use` (`PassWrapper.cpp:686-695`)

`Basis: source + execution (compiler/rustc_session/src/options.rs:2773-2774, compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:686-695, support/anneal_profgen_sim.py)`

In `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`), passing `-Z profile-sample-use=<path>` constructs `PGOOptions(PGOSampleUsePath, "", "", "", PGOOptions::SampleUse, PGOOptions::NoCSAction, PGOOptions::ColdFuncOpt::Default, DebugInfoForProfiling)` (`PassWrapper.cpp:687-695`), which schedules `SampleProfileLoaderPass` in the pre-link/ThinLTO optimization pipeline. Unlike instrumentation PGO (`-C profile-generate`), which matches basic blocks by a 60-bit `CFGMST` `JamCRC`, `SampleProfileLoaderPass` matches basic blocks and inline call stacks using DWARF `!dbg` `DILocation` metadata (`(LineOffset, Discriminator)` relative to the function's `DISubprogram` start line, augmented with `DILexicalBlockFile` discriminators when `-Z debuginfo-for-profiling=yes` is enabled).

Executing `support/anneal_profgen_sim.py` across `M0`–`M4` reveals why DWARF `(LineOffset, Discriminator)` keys fail under routine code evolution:
1. **Intra-Function Line-Offset Shift (`M1`)**: Inserting a 3-line early return at the top of `<OpFastAdd as StageOp>::execute` shifts the function body's relative `LineOffset`s by `+4` lines without changing the function start line (`DISubprogram::getScopeLine()`), causing `SampleProfileLoaderPass` to bind the old `LineOffset = 8` hot weight (`49,400`) to `LineOffset = 8` of the mutated function (which in the mutated function corresponds to the cold `else if (x & 0xff) == 1` branch!) and dropping the indirect-call target match.
2. **Branch Condition Negation (`M2`)**: Rewriting `if (x & 0x7f) == 0 { cold() } else { hot() }` into `if (x & 0x7f) != 0 { hot() } else { cold() }` places the hot body at the old cold `LineOffset = 4`, so line-based sample weights invert hot/cold branch probabilities.
3. **Mangled Symbol Hash Drift (`M4`)**: Because `llvm-profgen` keys top-level function headers in `.prof` by the ELF `.symtab` symbol name (`_RNvXCs<crate_hash>_...`), changing `-C metadata` invalidates `100%` of internal Rust symbols in `-Z profile-sample-use`.

---

### 2. The `.anneal_site_map` ELF Section and Minimum-Cost Circulation Smoother (`CirculationSmoother`)

`Basis: source + execution + derived (support/anneal_profgen_sim.py, support/lbr_skid_and_mutation_results.json)`

To decouple hardware LBR sample ingestion from DWARF line numbers and machine-branch polarity, `MiniMach` emits a non-allocatable (`!SHF_ALLOC`, stripped from production memory images) ELF section `.anneal_site_map` containing one 32-byte record per machine basic block:

| Byte Offset | Field Name | Width | Description |
| ---: | :--- | :--- | :--- |
| `0..8` | `pc_range_start` | `u64` | Start virtual address (or section-relative offset) of the `MiniMach` basic block |
| `8..16` | `pc_range_end` | `u64` | End virtual address of the `MiniMach` basic block (branch instruction at `pc_range_end - inst_len`) |
| `16..24` | `canonical_item_key` | `u64` | Truncated SHA-256 of un-disambiguated `(CrateName, DefPath, MonomorphizedFnSig)` |
| `24..31` | `site_anchor_key` | `u56` | Truncated SHA-256 of `(InlineContextSpine, TerminatorKind, ConditionPolarityFingerprint)` |
| `31` | `flags` | `u8` | Bit 0: `machine_branch_inverted_bit` (`1` if hardware `taken` corresponds to MIR `false`); Bits 1..3: `terminator_kind` (`CondBr`, `SwitchInt`, `IndirectCall`, `VTableCall`, `Return`) |

When `anneal-profgen` ingests a Linux `perf.data` LBR trace (`PERF_SAMPLE_BRANCH_STACK` of 16 or 32 `(from_ip, to_ip)` hardware branch records per PMU event):
1. **Direct Branch-Transition vs. Range Attribution**: Each consecutive LBR pair `(from_ip_k, to_ip_k)` directly increments the control-flow edge `(bb(from_ip_k) -> bb(to_ip_k))` with high confidence weight $\alpha_{\text{branch}} = 16$, while the unfolded instruction range `[to_ip_{k-1}, from_ip_k]` between taken branches increments the traversed fallthrough basic blocks with lower confidence weight $\alpha_{\text{range}} = 4$ (reflecting its susceptibility to PMU IP skid and range dropout).
2. **Polarity Un-Flipping (`unflipMachineBranch`)**: For every conditional branch block $b$, if `b.machine_branch_inverted_bit == 1`, `anneal-profgen` swaps `(hw_taken_count, hw_fallthrough_count)` before emitting `(when_cond_true_weight, when_cond_false_weight)` to `AnnealProfV1`.
3. **Weighted Minimum-Cost Circulation Smoothing (`CirculationSmoother`)**: On each function's CFG $G = (V, E \cup \{(\text{exit}, \text{entry})\})$, `CirculationSmoother` solves:
   $$\min_{f : E \to \mathbb{Z}_{\ge 0}} \sum_{e \in E} \alpha_e \cdot |f(e) - \hat{w}(e)| \quad \text{subject to} \quad \forall u \in V,\; \sum_{e \in \text{in}(u)} f(e) = \sum_{e \in \text{out}(u)} f(e)$$
   When PMU IP skid shifts `15%` of hot branch IP samples forward into the adjacent cold fallthrough block (`Regime S2`), the fallthrough block's range count $\hat{w}_{\text{range}}$ is inflated, but its outgoing LBR branch edge (`alpha_branch = 16`) records only true cold executions. Enforcing Kirchhoff conservation at the fallthrough vertex cancels the skidded flow and restores it to the hot taken edge.

Table 1 reports the branch-probability $L_1$ error, Kirchhoff flow residuals, and solver latency across Regimes `S1` (Clean LBR) and `S2` (`15%` PMU IP skid + `20%` fallthrough range dropout) across the 14 branch sites (`support/lbr_skid_and_mutation_results.json`):

| Regime & Sample Budget ($N$/fn) | `llvm-profgen` Mean $L_1$ Error | Raw Un-Smoothed `anneal-profgen` Mean $L_1$ Error | `anneal-profgen` + `CirculationSmoother` Mean $L_1$ Error | $L_1$ Error Reduction vs. Raw / vs. `llvm-profgen` (%) | Raw Kirchhoff Residual $\to$ Post-Smoother Residual | Circulation Solve Time (ms) |
| :--- | ---: | ---: | ---: | ---: | :---: | ---: |
| `S1_Clean_LBR` ($N = 100$) | `0.02410` | `0.02155` | **`0.02155`** | — | `0 -> 0` | `0.0325` |
| `S1_Clean_LBR` ($N = 500$) | `0.01320` | `0.01103` | **`0.01103`** | — | `0 -> 0` | `0.0301` |
| `S1_Clean_LBR` ($N = 5,000$) | `0.00280` | `0.00195` | **`0.00195`** | — | `0 -> 0` | `0.0264` |
| **`S2_Skid15_Dropout20` ($N = 100$)** | `0.06579` | `0.05572` | **`0.01172`** | **`-78.96%` / `-82.18%`** | `94 -> 0` | `0.0200` |
| **`S2_Skid15_Dropout20` ($N = 500$)** | `0.06526` | `0.05067` | **`0.00986`** | **`-80.54%` / `-84.89%`** | `501 -> 0` | `0.0254` |
| **`S2_Skid15_Dropout20` ($N = 5,000$)** | `0.05951` | `0.04399` | **`0.01076`** | **`-75.53%` / `-81.91%`** | `5,016 -> 0` | `0.0279` |

Table 2 compares end-to-end runtime performance (`x86_64-unknown-linux-gnu`, No-PGO baseline: `224.39` $\mu\text{s}$) when applying an LBR sample profile collected on `M0` across source mutations `M0`–`M4` (`support/lbr_autofdo_benchmark.csv`):

| Mutation Scenario | `-Z profile-sample-use` ($\mu\text{s}$) | `-Z profile-sample-use` Speedup (%) | LLVM Retained PGO Gain (%) | `anneal-profgen` + `CirculationSmoother` ($\mu\text{s}$) | `anneal-profgen` Speedup (%) | `anneal-profgen` Retained Gain (%) | Polarity Flips Un-Flipped |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `M0_Baseline_Unmodified` | 48.60 | +78.34% | 99.6% | **47.77** | **+78.71%** | **100.0%** | 7 |
| **`M1_InsertEarlyReturnShiftLineOffsets`** | **239.53** | **-6.75%** | **-8.6%** | **48.65** | **+78.32%** | **99.5%** | 7 |
| **`M2_NegateBranchConditionAndSwapArms`** | **207.23** | **+7.65%** | **9.7%** | **48.66** | **+78.32%** | **99.5%** | **9** |
| **`M3_ExtractInlinedHelperChangeInlineStack`** | **207.67** | **+7.45%** | **9.5%** | **48.64** | **+78.32%** | **99.5%** | 7 |
| **`M4_CrateMetadataDrift`** | **193.93** | **+13.58%** | **17.3%** | **47.79** | **+78.70%** | **100.0%** | 7 |

---

### 3. Lean `v4.34.1` Mechanization of Circulation Conservation and Polarity Transfer

`Basis: source + execution (support/lean/AutoFdoCirculationAndPolarity.lean)`

All 9 theorems in `support/lean/AutoFdoCirculationAndPolarity.lean` check in the Lean `v4.34.1` kernel with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Mechanized Property | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `addCirculation_preserves_circulation` | Pointwise sum of two Kirchhoff circulations `f + g` satisfies `IsValidCirculation`. | `[propext, Quot.sound]` |
| `scaleCirculation_preserves_circulation` | Non-negative scalar multiple `k * f` of a circulation satisfies `IsValidCirculation`. | `[propext]` |
| `applyResidualCycle_preserves_circulation` | Augmenting flow by `delta` along any balanced cycle `IsBalancedCycle` preserves `IsValidCirculation`. | `[propext, Quot.sound]` |
| `unflipMachineBranch_involutive` | `unflipMachineBranch inverted (unflipMachineBranch inverted hw) = hw`. | *(none)* |
| `lbr_polarity_transfer_sound` | Un-flipping hardware `(taken, notTaken)` LBR counts by `inverted` recovers exact semantic MIR `(wTrue, wFalse)`. | *(none)* |
| `lbr_indirect_target_resolution_sound` | Resolving `targetIp` in `.symtab` yields a verified `SymtabEntry` with `entryIp = targetIp` and `itemKey = k`. | `[propext, Quot.sound]` |
| `circulationSmoother_produces_valid_anneal_prof` | Cycle-smoothed + polarity-unflipped LBR counts satisfy `AnnealProfV1WellFormed`. | `[propext, Quot.sound]` |
| `canary_raw_lbr_skid_violates_kirchhoff` | Negative canary: skidded edge flow `(100, 82, 100)` on a 3-vertex cycle violates Kirchhoff conservation (`100 ≠ 82`). | *(none)* |
| `canary_ignoring_inverted_machine_branch_swaps_hot_cold` | Negative canary: omitting `unflipMachineBranch` when `inverted = true` swaps `(990, 10)` and `(10, 990)`. | *(none)* |

## Boundaries

- **Dynamic Indirect Targets in Unmapped JIT or Stripped Foreign Libraries**: `lbr_indirect_target_resolution_sound` resolves `target_entry_ip` to a `CanonicalItemKey` when the target resides in an ELF binary or shared library with `.anneal_site_map` or `.symtab` symbols (`99.64%` of samples in our benchmark; `18 / 5,000` samples landing in PLT stubs or stripped external C libraries are safely ignored).
- **Non-Taken Loop Bodies Below Minimum Sample Density**: When a function receives fewer than `5` total LBR samples across an entire profiling run, `anneal-profgen` marks its `SiteAnchorKey` entries as low-confidence and falls back to static branch-probability heuristics rather than amplifying single-sample Poisson noise.

## Evidence

- **Mechanized Lean `v4.34.1` proof module and `anneal-profgen` benchmark artifacts**:
  - `support/lean/AutoFdoCirculationAndPolarity.lean` (`9` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`)
  - `support/lean/lakefile.lean`
  - `support/anneal_profgen_sim.py`
  - `support/lbr_skid_and_mutation_results.json`
  - `support/lbr_autofdo_benchmark.csv`
- **Primary upstream source citations**:
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_session/src/options.rs:2773-2774` (`-Z profile-sample-use` option definition)
    - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:686-695` (`PGOOptions::SampleUse` and `DebugInfoForProfiling` wiring)
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Transforms/IPO/SampleProfile.cpp` (`SampleProfileLoaderPass` and `LineLocation(LineOffset, Discriminator)` matching)
    - `llvm/tools/llvm-profgen/ProfileGenerator.cpp` (LBR `(from_ip, to_ip)` branch stack and range aggregation)

## Revalidation

Run both the Lean `v4.34.1` kernel proof check and the `anneal-profgen` LBR skid and mutation benchmark:

```bash
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean \
  reports/hardware-lbr-autofdo-sample-profile-ingestion-and-circulation-smoothing/support/lean/AutoFdoCirculationAndPolarity.lean
python3 reports/hardware-lbr-autofdo-sample-profile-ingestion-and-circulation-smoothing/support/anneal_profgen_sim.py
```

Verify that `lean` exits with status `0` and zero `sorryAx`, that `CirculationSmoother` reduces Regime `S2` $L_1$ error by $>75\%$ with `post_kirchhoff_residual = 0`, and that `anneal-profgen` retains $>99\%$ of PGO runtime speedup across `M0`–`M4`.
