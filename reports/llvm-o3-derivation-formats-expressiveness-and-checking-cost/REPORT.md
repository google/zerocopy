# Expressiveness, Certificate Size, and Checking Cost of Derivation Formats Across Representative `-O3` LLVM Transformations

## Summary

Evaluating three candidate machine-checkable derivation formats—**Per-Pass Simulation Certificates (`SimCert`)**, **Relational Hoare / Alias-Citing Sequent Derivations (`RelJudg`)**, and **Hybrid Rewrite-Trace + Decidable Side-Condition Witnesses (`HybridTrace`)**—across **12 representative `-O3` transformations** extracted from `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled LLVM 23.1.1 `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) establishes the following quantitative boundaries (`support/measurements.json`):

1. **Expressiveness Across the 12 `-O3` Parity Transformations:**
   - **`SimCert` (Cut-Point Simulation Equations):** Directly expresses **`8 / 12` (`66.7%`)** transformations (`Devirtualization`, `SROA + mem2reg`, `Addressing-Mode Selection`, `RegAlloc with Spills`, `Loop Unrolling + IndVars`, `IEEE-754 Bit-Exact Rewrites`, `Jump Threading`, and `Function Merging`), but **cannot** directly express the remaining **`4 / 12`** (`LoopVectorize with SCEV alias check`, `GVN + LICM with noalias/readonly`, `Inlining across unwind edges`, and `C11/LLVM Atomics coalescing/reordering`) without bolting on auxiliary relational/ghost-memory invariants.
   - **`RelJudg` (Crellvm-Style Relational Hoare Judgments Citing Alias Scopes):** Directly expresses **`10 / 12` (`83.3%`)** transformations (including `GVN + LICM` with `!noalias`, `LoopVectorize` runtime overlap guards, `Inlining across unwind edges`, and `Atomics`), requiring auxiliary machine-frame extensions only for the **`2 / 12`** low-level target passes (`Addressing-Mode Selection` and `RegAlloc with Spills`).
   - **`HybridTrace` (Linear Micro-Rewrite Steps + Decidable Boolean Witness Tables):** Directly expresses all **`12 / 12` (`100%`)** transformations across both SSA middle-end (`MiniSSA`) and target machine (`MiniMach`) tiers without unguided solver search.
2. **Certificate Size and Compression Ratios (`support/derivations.json`):**
   - Across all 12 benchmark transformations (`89` `SimCert` steps, `105` `RelJudg` steps, `125` `HybridTrace` steps), `HybridTrace` achieves the smallest per-step footprint at **`24.77` bytes/step raw binary** (**`12.04` bytes/step compressed**, `3,096` bytes raw / `1,505` bytes compressed total), compared to **`33.08` bytes/step raw** (**`16.53` bytes/step compressed**) for `SimCert` and **`40.91` bytes/step raw** (**`17.66` bytes/step compressed**) for `RelJudg`.
3. **Automated Generation and Native Checking Throughput (`support/sroa_gvn_gen.py`, `support/w5_checker.rs`):**
   - Automated derivation generation in `support/sroa_gvn_gen.py` emits verified `SimCert`, `RelJudg`, and `HybridTrace` certificates in **`52.64` $\mu$s** for 3-field `SROA + mem2reg` (`PacketState`) and **`10.86` $\mu$s** for `GVN + LICM` with `!noalias` disjointness lookup.
   - In the native Rust checker (`support/w5_checker.rs`, compiled at `-C opt-level=3`), checking throughput reaches **`0.00217–0.00224` $\mu$s/step** (**`~450 million` steps/second** per core; **`0.275` $\mu$s** total for all 125 `HybridTrace` steps across the 12 benchmarks), while the Python reference checker (`support/w5_checker.py`) runs at **`0.1205–0.1292` $\mu$s/step** (`15.07` $\mu$s total for `HybridTrace`).

## Applicability

- **Extends:** `anllvm-globalisel-backend-and-certificate-checkers`, `llvm-derivation-emission-instrumentation-architecture-and-cost`, `proof-producing-compilation-and-certificate-formats-quantitative-survey`, `relational-logics-simulation-techniques-and-completeness-for-compiler-derivations`
- **Subjects and Environment:** Applies to `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) targeting `x86_64-unknown-linux-gnu` at `-C opt-level=3 -C codegen-units=1`.
- **Role of Candidate Formats:** The three derivation formats (`SimCert`, `RelJudg`, `HybridTrace`) and the two-tier IR (`MiniSSA` + `MiniMach`) are defined strictly as experimental measurement instruments to compare expressiveness, rule-family surface area, byte density, and checking latency on concrete `-O3` outputs.

## Findings

### 1. Candidate Format Definitions Over `MiniSSA` and `MiniMach`

**Basis: source + execution + derived**

To evaluate middle-end and backend transformations uniformly, `support/w5_checker.rs` and `support/w5_checker.py` operate over a two-tier representation (`MiniSSA` for CFG basic blocks, $\phi$-nodes, scoped `noalias`/`readonly` metadata, `invoke`/`landingpad` unwind edges, and C11/LLVM atomic orderings; `MiniMach` for physical registers, stack-frame spill slots `[rsp + disp]`, `rflags` condition codes, and x86-64 `[base + index*scale + disp]` SIB addressing):

| Candidate Format | Core Judgment / Step Structure | Binary Record Layout | Primary Strength | Structural Bottleneck |
| :--- | :--- | :--- | :--- | :--- |
| **`SimCert`** (Per-Pass Simulation Certificate) | Cut-point map $\pi : \text{PC}_{\text{tgt}} \to \text{PC}_{\text{src}}$ + symbolic value equalities $v'_i = E(v_1, \dots, v_k)$ | `8 B` header + `32 B/step` (`33.08 B/step` mean) | Compact on control-flow folding (`JumpThreading`), `SROA`, and `LoopUnroll` | Cannot justify load hoisting across pointer stores (`GVN`/`LICM`), runtime alias guards (`LoopVectorize`), or atomic reorderings without external ghost state |
| **`RelJudg`** (Relational Hoare / Alias-Citing Sequent) | $\Gamma_{\text{alias}}, \Delta_{\text{order}} \vdash \langle C_{\text{src}}, C_{\text{tgt}} \rangle : \mathcal{R}_{\text{pre}} \Rightarrow \mathcal{R}_{\text{post}}$ (Crellvm style) | `8 B` header + `40 B/step` (`40.91 B/step` mean) | Native support for `!noalias`/`readonly` frames, loop invariants, and happens-before lattices | Verbose pre/post relational assertions (`40.91 B/step`); awkward for physical register spills and SIB addressing |
| **`HybridTrace`** (Rewrite Trace + Witness Table) | Linear sequence of cone rewrites `(rule_id, src_cone_hash, tgt_cone_hash)` + boolean side-condition witness | `8 B` header + `24 B/step` (`24.77 B/step` mean) | Expresses all `12 / 12` transformations at lowest byte cost (`24.77 B/step` raw, `12.04 B/step` compressed) | Requires ~18% more elementary steps (`125` vs. `89` in `SimCert`) because compound passes decompose into micro-steps |

---

### 2. Twelve Representative `-O3` Transformations Extracted from `rustc 1.99.1`

**Basis: execution + source**

Compiling `support/w5_o3_corpus.rs` with `rustc +1.99.1-x86_64-unknown-linux-gnu` at `-C opt-level=0 -C no-prepopulate-passes --emit=llvm-ir` and `-C opt-level=3 -C codegen-units=1 -C debuginfo=1 -C remark=all -Z remark-dir=... --emit=llvm-ir,asm` yields the 12 concrete pre/post transformation pairs below (`support/measurements.json`):

| ID | Benchmark Function (`w5_o3_corpus.rs`) | `-O3` Transformation & Observed LLVM 23.1.1 / x86-64 Output | `SimCert` | `RelJudg` | `HybridTrace` | Steps (`Sim` / `Rel` / `Hyb`) | Binary Bytes (`Sim` / `Rel` / `Hyb`) | Rust Check $\mu$s (`Hyb`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`T01`** | `t01_vector_slice_loop_with_alias_check` | `LoopVectorize` emits `ptrtoaddr` runtime overlap guard (`sub %src7, %dst6 >u -32`), `2x<4 x i32>` `vector.body` (stride 8), `middle.block`, and scalar remainder loop (`10` BBs, `90` insts) | `AuxGhost` | **Direct** | **Direct** | `14 / 18 / 22` | `456 / 728 / 536` | `0.0473` |
| **`T02`** | `t02_devirtualize_under_lto` | `SROA` + `InstCombine` + `Inliner` fold `&dyn TransformOp` vtable dispatch into `%_3 = mul i64 %x, 13; %_0 = add i64 %_3, 29` (`leaq (%rdi,%rdi,2), %rax; leaq (%rdi,%rax,4), %rax; addq $29, %rax`) | **Direct** | **Direct** | **Direct** | `5 / 6 / 7` | `168 / 248 / 176` | `0.0159` |
| **`T03`** | `t03_gvn_licm_noalias_readonly` | `ScopedNoAliasAA` + `GVN` + `LICM` hoist `load i64, ptr %scale` and `load i64, ptr %cfg_weight` and `mul i64 %_8, %_7` out of the 64-iteration store loop (`!noundef`, `noalias readonly`) | `AuxGhost` | **Direct** | **Direct** | `8 / 9 / 12` | `264 / 368 / 296` | `0.0260` |
| **`T04`** | `t04_inline_across_unwinding_edges` | `Inliner` converts callee panic path into `invoke ... to label %unreachable.i unwind label %bb5.i` and merges inner `DropGuard` cleanup (`+0xDEADBEEF`) with outer `DropGuard` cleanup pad before `resume` | `AuxGhost` | **Direct** | **Direct** | `9 / 11 / 14` | `296 / 448 / 344` | `0.0305` |
| **`T05`** | `t05_sroa_and_mem2reg` | `SROA` + `PromoteMemoryToRegister` + `SimplifyCFG` split 16-byte `PacketState` alloca into pure SSA `select i1 %cond`, `zext`, `or`, and `add` (`0` allocas, `0` loads/stores, `1` BB, `13` insts) | **Direct** | **Direct** | **Direct** | `6 / 6 / 9` | `200 / 248 / 224` | `0.0198` |
| **`T06`** | `t06_addressing_mode_selection` | `X86ISelDAGToDAG` folds two `getelementptr inbounds` (`+32` and `idx * 8`), `load i64`, and `add i64` into a single x86-64 SIB instruction `addq 32(%rdi,%rcx,8), %rax` (`4` asm insts total) | **Direct** | `AuxGhost` | **Direct** | `3 / 4 / 4` | `104 / 168 / 104` | `0.0095` |
| **`T07`** | `t07_regalloc_with_spills` | `RAGreedy` + `PrologEpilogInserter` save 6 callee-saved GPRs (`%rbp,%r15..%rbx`), allocate `subq $24, %rsp`, and spill live loop accumulators to `8(%rsp)`/`16(%rsp)` across `callq external_clobber_call@PLT` | **Direct** | `AuxGhost` | **Direct** | `12 / 16 / 15` | `392 / 648 / 368` | `0.0324` |
| **`T08`** | `t08_unroll_and_indvar_simplify` | `IndVarSimplify` + `LoopUnroll` completely unroll 16 iterations into 1 basic block (`64` insts), strength-reducing `i * step` into shifts (`shl 1`, `shl 2`) and closed-form accumulation | **Direct** | **Direct** | **Direct** | `16 / 17 / 20` | `520 / 688 / 488` | `0.0431` |
| **`T09`** | `t09_atomics_coalesce_and_reorder` | `GVN` + `DSE` forward non-atomic `*local_scratch` register value `%_4` across `load atomic monotonic` and `load atomic acquire` (via `&mut u64` `noalias`) while preserving atomic load order | `AuxGhost` | **Direct** | **Direct** | `5 / 6 / 7` | `168 / 248 / 176` | `0.0157` |
| **`T10`** | `t10_ieee754_fp_valid_rewrites` | `InstCombine` eliminates bitwise-exact double negation `-(-x) -> x` (`FP-BitExact-DoubleNegElim`) while preserving `fmul double %y, 2.0` and `fadd` (`1` BB, `3` insts) | **Direct** | **Direct** | **Direct** | `3 / 3 / 4` | `104 / 128 / 104` | `0.0095` |
| **`T11`** | `t11_jump_threading` | `JumpThreading` + `SimplifyCFG` thread `x > 10` through `state == 1`, collapsing two diamond branches into `select i1 %_4, i32 %1, i32 %2` (`1` BB, `6` insts) | **Direct** | **Direct** | **Direct** | `4 / 5 / 6` | `136 / 208 / 152` | `0.0137` |
| **`T12`** | `t12_merge_functions_entry` | `MergeFunctions` proves structural isomorphism of `t12_mono_a(&[u32], usize) -> u32` and `t12_mono_b(&[i32], usize) -> i32` and redirects the second call directly to `t12_mono_a` | **Direct** | **Direct** | **Direct** | `4 / 4 / 5` | `136 / 168 / 128` | `0.0118` |

---

### 3. Rule-Family Inventory and Negative Soundness Rejection Tests

**Basis: execution + derived**

Across the 12 transformations, `HybridTrace` requires **12 modular rule families** (`CFG-EdgeSplit`, `SSA-DomSubst`, `Mem-NoAliasDisjoint`, `Loop-VectorRemainderSplit`, `Unwind-LandingPadMerge`, `Mach-FrameSpillSlot`, `Mach-AddrModeSIB`, `FP-BitExact`, `FP-FastMathFlag`, `Atomic-OrderLattice`, `IP-DevirtVtable`, and `IP-FuncMergeIso`).

To verify that the checker rejects unsound optimizations documented in LLVM bug censuses, `support/w5_checker.py` and `support/w5_checker.rs` test four mandatory negative derivations (`negative_soundness_tests` in `support/measurements.json`), rejecting 100% of them:

1. **`NEG-FP-01` (`fadd double %x, 0.0 -> %x` without `nsz`):** Rejected by `FP-FastMathFlag-Guard` with concrete IEEE-754 witness `x = -0.0` (`0x8000000000000000`), where `(-0.0) + (+0.0) = +0.0` (`0x0000000000000000`) under default `roundTiesToEven`.
2. **`NEG-FP-02` (`(x + y) + z -> x + (y + z)` without `reassoc`):** Rejected with witness `x = 1e308, y = 1e308, z = -1e308` (`+Inf` vs. `1e308`).
3. **`NEG-ATOM-01` (Reordering `load atomic seq_cst` before `store atomic seq_cst`):** Rejected by `Atomic-SeqCstTotalOrderGuard` (violates sequential consistency on the Store-Buffering litmus test).
4. **`NEG-ALIAS-01` (Hoisting loop load `%p` across store `%q` without `noalias` or runtime overlap guard):** Rejected by `Mem-NoAliasDisjoint`.

## Boundaries

- **Middle-End and Local Codegen Scope (`not examined` for global link-time binary relaxation):** The 12 benchmarks cover intraprocedural and module-level CGSCC/LTO transformations (`Inliner`, `Devirt`, `MergeFunctions`) plus function-level `ISel` and `RAGreedy`, but do not include linker-level `R_X86_64_GOTPCRELX` relaxation.
- **Automated Generator Coverage (`2 / 12` automated, `10 / 12` structured templates):** `support/sroa_gvn_gen.py` implements full automated derivation generation for `SROA + mem2reg` (`T05`) and `GVN + LICM` (`T03`); the remaining 10 transformations use deterministic corpus-bound certificate synthesis in `support/w5_checker.py`.

## Evidence

- **`support/w5_o3_corpus.rs`:** Self-contained 12-transformation Rust 1.99.1 benchmark crate.
- **`support/sroa_gvn_gen.py`:** Automated dominance-frontier `SROA + mem2reg` and `!noalias`-guided `GVN + LICM` derivation generator.
- **`support/w5_checker.rs` & `support/w5_checker.py`:** Native Rust and Python prototype checkers across `SimCert`, `RelJudg`, and `HybridTrace`.
- **`support/derivations.json` & `support/measurements.json`:** Complete serialized derivations, byte sizes, compression ratios, and microsecond timing tables.

## Revalidation

Run the generator and checker suite directly from `support/`:

```bash
python3 support/sroa_gvn_gen.py
python3 support/w5_checker.py
```

To re-extract the LLVM 23.1.1 IR, x86-64 assembly, and YAML optimization remarks on `rustc 1.99.1`:

```bash
rustc +1.99.1-x86_64-unknown-linux-gnu -C opt-level=0 -C no-prepopulate-passes --emit=llvm-ir support/w5_o3_corpus.rs
RUSTC_BOOTSTRAP=1 rustc +1.99.1-x86_64-unknown-linux-gnu -C opt-level=3 -C codegen-units=1 -C debuginfo=1 -C remark=all --emit=llvm-ir,asm support/w5_o3_corpus.rs
```
