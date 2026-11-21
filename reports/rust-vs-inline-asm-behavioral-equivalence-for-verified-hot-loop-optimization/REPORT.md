# Rust Reference vs. Inline/Naked Assembly Behavioral Equivalence for Verified Hot-Loop Optimization

## Summary

A workflow in which a developer or AI coding agent replaces a hot Rust function with hand-tuned inline (`core::arch::asm!`) or naked (`core::arch::naked_asm!`) assembly—claimed to be behaviorally equivalent to a clean Rust reference function, formally proved, and enforced in CI—requires closing four coupled engineering boundaries across semantics, compiler lowering, proof automation, and adversarial CI governance:

1. **Cross-Level Relational Contract Across MIR $\leftrightarrow$ ISA (`Basis: normative + source + execution + derived`):** Extending MIR-vs-MIR `TotalSafeTwinEquiv` across the MIR $\leftrightarrow$ ISA seam splits cleanly into a two-tier contract, mechanized with zero `sorryAx` in Lean `v4.34.1` ([`support/RustAsmRefinementAndLoopEquiv.lean`](support/RustAsmRefinementAndLoopEquiv.lean)):
   - Naive "return-only" panic refinement (`ref q = .returned v m -> asm q = .halted v m`) **unsoundly permits panic-to-UB laundering**, turning a safe Rust bounds-check panic (`len = 0`) into an unchecked hardware trap or memory corruption (`naive_panic_refinement_admits_panic_to_ub`).
   - Instead, exported safe Rust entry points must satisfy **`TotalMirAsmEquiv`** (fault/trap-freedom plus bidirectional parity on normal returns, panic caller-memory states, and divergence), while inner `asm!` hot loops prove **`PrecondMirAsmEquiv Pre`** and lift back to `TotalMirAsmEquiv` via a fast pre-loop Rust check (`checked_wrapper_recovers_total_equiv`).
   - Sound substitution for all downstream Rust callers (including `Tree Borrows` and `MaybeUninit` consumers) requires asymmetric output-byte refinement (`OutputByteRefines`: exact value and provenance on initialized bytes; arbitrary concrete bytes permitted on reference `.uninit` padding only when `asm!` tail over-reads satisfy `PadIndependent`), provenance-preserving subslice offsets (`SubslicePtrSound`), explicit IEEE-754 tolerance policies (bit-exact vs. `fadd_algebraic` / ULP bounds), and an opt-in 2-safety `LeakTrace` clause defeating McLean's Refinement Paradox (`functional_equiv_vs_ct_2safety`).
2. **Zero-Overhead Pairing, Dispatch Lowering, and a Critical `rustc` `asm!` Feature-Check Blind Spot (`Basis: source + execution`):** Empirical `rustc` probes across `1.98.0-nightly` (`14210df0e`), `1.99.1` (`58cf8f9c3`), and `1.102.0-nightly` (`3ef0c22cd`) ([`support/probe_dispatch_and_stripping.py`](support/probe_dispatch_and_stripping.py)) establish three concrete compiler invariants:
   - **Uncalled private reference twins give zero binary overhead with zero `#[cfg]` drift:** Across all three toolchains, a completely unreferenced `#[allow(dead_code)] fn ref_twin(...)` (and even an uninstantiated generic `fn<const K: u64>`) **always** passes typeck, borrowck, and `Runtime(PostCleanup)` MIR generation (`3-2-000.runtime-post-cleanup.after.mir`) while emitting **0 symbols** in `rlib`, `.o`, `cdylib`, and `bin` artifacts and **0 extra `.text` bytes** (`298,122` B vs. `298,122` B in `cdylib`).
   - **Critical `rustc` target-feature blind spot on `asm!` clobbers (`compiler/rustc_hir_typeck/src/inline_asm.rs:435-463`):** `InlineAsmCtxt::check_asm` intentionally skips target-feature checks whenever `op.is_clobber()` is true (`if !op.is_clobber()`). Consequently, across all three toolchains, `out(ymm_reg) _` and `out("ymm0") y` (`y: __m256i`) fail to compile without `#[target_feature(enable = "avx")]`, whereas **`out("ymm0") _` and raw AVX2 mnemonics with GPR/`xmm0` operands compile with exit code `0` and zero warnings inside baseline SSE2 functions** (downgrading `out("ymm0") _` to `~{xmm0}`, bypassing the `#[target_feature]` `unsafe` call fence, and omitting `vzeroupper`).
   - **Dispatch codegen & `1.102.0-nightly` version transition:** On default `x86_64`, `is_x86_feature_detected!("avx2")` lowers to a relaxed `CACHE` atomic load + tail jump (`jmp sum_u8_avx2_asm`) blocked from inlining by `#[target_feature]` (with an `extern "C"` `panic_cannot_unwind` pad), `AtomicPtr` lazy ifunc (`BurntSushi/memchr`) lowers to an indirect call, and zero-sized `Avx2Token` compiles to a single `jmp` (`0` branches); under `-C target-feature=+avx2`, `is_x86_feature_detected!` constant-folds away and inlines the `asm!` loop. Notably, combining `#[inline(always)]` with `#[target_feature]` is a hard compile error in `1.98.0-nightly` and `1.99.1`, but **compiles cleanly in `1.102.0-nightly`** while still blocking inlining into callers lacking the feature.
3. **Proof Automation and Fast Counterexample Loops for Real Hot-Loop Tricks (`Basis: normative + source + execution + derived`):**
   - For loop restructuring, **Tristan & Leroy's (POPL 2010) algebraic commutation law** (`E (P s) = iterN B mu s` and `E (K t) = iterN B delta (E t)` $\implies$ `E (iterN K k (P s)) = iterN B (mu + k * delta) s`) discharges **software pipelining** (overlapped prolog/kernel/epilog stages) cleanly in Lean `v4.34.1` (`software_pipelining_equiv`, `mac_software_pipelined_exact`) where step-by-step lockstep simulation fails, while `prolog_unroll_epilog_equiv` linearly composes misaligned prologs, arbitrary $U$-unrolled kernels, and scalar/masked epilogs.
   - Exhaustive arithmetic probes ([`support/probe_hot_loop_tricks_and_fuzz.py`](support/probe_hot_loop_tricks_and_fuzz.py)) show why random small-input unit tests miss data-level assembly bugs: classic Mycroft SWAR fails on `1/65,536` 2-byte pairs (`(0x00, 0x01)` — reproducing `BurntSushi/memchr` `regression_count_new_lines`'s `7` vs. `4` bug on `\x0b\n` while borrow-free SWAR achieves `0/65,536`), Granlund-Montgomery `u16` division by `7` (`0x924A`) and `100` (`0xA3D8` without pre-shift) pass every input below `43,693` / `43,699` before failing (`3,121` and `219` errors), BMI2 `bzhi` wraps `SRC2[7:0]` at `256` (`0` vs. `!0`), and unmasked `pshufb` LUTs zero `128/256` bytes.
   - A native Linux `x86_64` compiled Rust + `asm!` differential harness using real `mmap`/`mprotect(PROT_NONE)` leading and trailing guard pages catches a 16-byte SIMD over-read (`len = 1`) via **`SIGSEGV` (`rc = -11`)** that passed `22/22` normal heap `Vec` unit tests, while verifying `748` edge-length $\times$ alignment $\times$ guard-page checks on the fixed 4x-unrolled SSE2 kernel in **`1.32 ms`**—acting as a fast pre-filter before Lean proof discharge.
4. **Anti-Reward-Hacking CI Enforcement Under a Two-Surface Human-Review Model (`Basis: normative + source + execution`):** Treating the Rust reference function as the stated specification under Anneal's two-surface threat model (`joshlf/anneal@c131b320`, `THREAT_MODEL.md`) requires six deterministic CI gates: transitive `Runtime(PostCleanup)` MIR spec-cone hashing (`SpecConeHash` over all called helpers, constants, types, and trait impls, demonstrated in [`support/probe_ci_spec_surface_gate.py`](support/probe_ci_spec_surface_gate.py)), total public-API equivalence banning precondition weakening, single-`cfg` capture plus full multi-target ISA matrix checking, machine-byte opcode-to-feature auditing, verified dispatch across all fallback arms, and base-branch-isolated content-addressed per-function caching.

## Applicability

This report governs end-to-end semantic specification, Rust compiler lowering, proof automation, rapid differential pre-filtering, and CI enforcement for verifying inline (`asm!`) and naked (`naked_asm!`) assembly hot loops against Rust reference implementations.

### Examined Subjects and Their Relationships

| Subject | Pinned Identity | Role in Investigation |
| :--- | :--- | :--- |
| **`rustc` `1.98.0-nightly`** | `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Executed on Linux `x86_64` for MIR (`runtime-post-cleanup`), LLVM IR, ASM, `nm`, and `#[inline(always)]` + `#[target_feature]` checks |
| **`rustc` `1.99.1`** | `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` | Executed on `x86_64-unknown-linux-gnu` and cross-compiled to `aarch64-unknown-linux-gnu`; primary source inspection of `compiler/rustc_hir_typeck/src/inline_asm.rs` and `compiler/rustc_codegen_llvm/src/asm.rs` |
| **`rustc` `1.102.0-nightly`** | `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Executed on Linux `x86_64` and inspected (`compiler/rustc_codegen_ssa/src/target_features.rs`), capturing the `#[inline(always)]` + `#[target_feature]` legality transition |
| **The Rust Reference** | `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative rules for `asm!`/`naked_asm!` options, clobbers, memory rules, and `#[target_feature]` safety |
| **Anneal verifier** | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `THREAT_MODEL.md`, `docs/trust-model.md`, and `trusted/rustc-capture/src/driver.rs` governing two-surface human review, Pass-1 syntax limits, and capture isolation |
| **Lean 4** | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Executed kernel checker (`-DElab.async=false -Ddebug.skipKernelTC=false`) for all ten theorems in [`support/RustAsmRefinementAndLoopEquiv.lean`](support/RustAsmRefinementAndLoopEquiv.lean) |
| **`BurntSushi/memchr`** | `BurntSushi/memchr@bd6068c30e9074a90c285e47912fa0b047d07597` | Production Rust runtime-dispatch (`unsafe_ifunc!` `AtomicPtr` in `src/arch/x86_64/memchr.rs`), 4x-unrolled aligned SIMD (`src/arch/generic/memchr.rs`), and SWAR borrow-bug regression (`src/arch/all/memchr.rs:260-269, 875-885, 985-995`) |
| **Semantic Program Alignment** | `bchurchill/pldi19-equivalence-checker@2e7707be99c10828970f1d96c2bcbb058936cbdc`, DOI `10.1145/3314221.3314596` | Primary source (`src/validator/paa.h`, `README.md`) for data-driven Product Alignment Automata (`ProgramAlignmentAutomata`) |
| **`llreve` / `Rêve`** | `mattulbrich/llreve@68cb958c1c02177fa0db1965a8afd879a97c2fc4`, DOI `10.1145/2642937.2642987` | Primary source (`reve/reve/lib/InferMarks.cpp`) for loop-header CHC relational verification |
| **`SymDiff`** | `boogie-org/symdiff@54835f0f85c0562b653a219b7a43c794504b3e29`, DOI `10.1007/978-3-642-31424-7_54` | Primary source (`Sources/SymDiff/source/MutualSummary.cs`) for mutual summaries and 2-to-1 differential checking |
| **Tristan & Leroy (POPL 2010)** | DOI `10.1145/1706299.1706311` | Normative algebraic validation criteria ($P; E \sim B^\mu$, $S; E \sim E; B^\delta$) for software pipelining |
| **Granlund & Montgomery (PLDI 1994)** | DOI `10.1145/178243.178249` | Normative division-by-invariant-integer multiply-shift bounds and add-shift widening |

### Scope Boundary Relative to Sibling Corpus Reports

This report builds directly on—without duplicating—established sibling packages in `zerocopy/reference`:
- MIR-vs-MIR `TotalSafeTwinEquiv`, unwind loopholes `L1`–`L4`, HACL* `SecScalar`, and stride-4 `BiAlign`: `safe-twin-observational-equivalence-unwind-and-constant-time-alignment`.
- ABI register-preservation matrices, `vzeroupper` clobber bugs, CSR flags (`FPSR.QC`, `MXCSR`, `vstart`), `Tree Borrows` seam mechanics, `out` vs. `lateout` register quantifiers, and ELF/Mach-O relocation binding: `rust-inline-asm-and-external-asm-abi-seams-in-formal-verifiers` and `rust-inline-assembly-contracts-relocations-and-simd-correspondence`.
- Target-feature catalogs (`80` x86 / `94` AArch64), Rust-vs-LLVM implication divergences, and `std_detect` OS probe sources (`cpuid + _xgetbv(0)`, `getauxval(AT_HWCAP)`): `target-features-implications-detection-and-abi-effects`.
- Media-codec fixed-point traps (`PMADDUBSW`, `PAVGB`, `VPMULHRSW` vs. `SQRDMULH`) and `checkasm` architecture: `verified-simd-vs-scalar-equivalence-for-media-dsp-kernels-and-asm`.
- Compilation refinement transfer hierarchy (`ProductiveCompiles`, `CTCompiles`) and Kripke `AllocId` partial bijections: `observable-behavior-property-transfer-and-anneal-statement-forms` and `partial-bijection-kripke-allocid-isomorphisms-and-provenance-stripping-laws`.
- Pass-1 Lean 4 certificate checkers for Carcara/Alethe, LRAT, Spacer CHC, and egglog: `carcara-alethe-lrat-spacer-chc-elaboration-into-pass1-lean-certificates`.
- `Cryptol`/`SAW`, `EasyCrypt`/`Jasmin`, `CryptoLine`, `STOKE`/`Minotaur`, `oss-verify-proofs` `oft check`, `VerusEval`, and `SpanVC` blame repair: `cryptol-saw-symbolic-equivalence-easycrypt-game-hopping-and-cryptoline`, `superoptimization-smt-solver-fuzzing-and-rtl-contract-testing`, `frontier-ai-lab-binary-verification-oss-fuzz-proofs-and-agent-reward-hacking`, and `counterexample-trace-shrinking-span-blame-assignment-and-agent-proof-repair`.

## Findings

### 1. Cross-Level Relational Equivalence Contract (Rust MIR $\leftrightarrow$ Inline/Naked Assembly)

`Basis: normative + source + execution + derived` (`support/RustAsmRefinementAndLoopEquiv.lean`, checked under Lean `v4.34.1` in `0.69 s`, `160.9 MB` max RSS, zero `sorryAx`).

#### 1.1 Total Panic-Exact Equivalence vs. Precondition-Gated Panic Refinement

In MIR-vs-MIR verification (`safe-twin-observational-equivalence-unwind-and-constant-time-alignment`), both twins execute inside the same Rust Abstract Machine where panics unwind via `TerminalOut.unwound callerMem`. Crossing into `core::arch::asm!` or `naked_asm!` changes the operational asymmetry: ordinary `asm!` is **forbidden from unwinding** (`r[asm.rules.unwind]` in `rust-lang/reference@c9cc3282`, `src/inline-assembly.md`), and hand-written assembly loops omit per-element Rust bounds checks and overflow asserts precisely to eliminate loop-carried branches.

Three candidate cross-level relations arise between a safe Rust reference `ref : Q -> MirOut V M` (outcomes `.returned v m | .panicked m | .ub | .diverges`) and an optimized assembly candidate `asm : Q -> IsaOut V M` (outcomes `.halted v m | .panicked m | .trap | .diverges`, where any hardware fault such as `#GP`, `#PF`, `#DE`, or `#UD` maps to `.trap`, which lifts to Rust `.ub`):

| Contract Form | Formal Judgment (`RustAsmRefinementAndLoopEquiv.lean`) | Safe Exported Rust API? | Inner `asm!` Hot Loop? | Soundness Failure Mode if Misapplied |
| :--- | :--- | :---: | :---: | :--- |
| **(a) Total Panic-Exact (`TotalMirAsmEquiv`)** | $\forall q,\; \text{ref}(q) \ne \text{ub} \land \text{asm}(q) \ne \text{trap}$ and exact bidirectional parity on `.returned`/`.halted`, `.panicked` (including caller memory `m`), and `.diverges` | **Mandatory** | Often too strong directly (no bounds check inside inner loop) | None; preserves exact caller-visible memory before unwind and prevents silent divergence or panic-to-UB laundering |
| **(b) Precondition-Gated (`PrecondMirAsmEquiv Pre`)** | Same total equivalence restricted to $\{q \mid \text{Pre}(q)\}$ | **Only** for `unsafe fn` exposing `Pre` on the Human Review Surface | **Canonical choice** (e.g., `Pre := len >= 32 ∧ dst.len >= src.len`) | Unsound if `Pre` is unproved at call sites or silently narrowed without human review |
| **(c) Naive Weak Panic Refinement (`NaiveWeakPanicRefines`)** | $\forall q\, v\, m,\; \text{ref}(q) = \text{returned}(v, m) \implies \text{asm}(q) = \text{halted}(v, m)$ | **UNSOUND** | **UNSOUND** | **Panic-to-UB laundering**: when `ref` panics safely (e.g. `slice[0]` on `len = 0`), `asm` may execute an unchecked load (`IsaOut.trap` / OOB memory corruption) or return arbitrary garbage while satisfying the contract vacuously (`naive_panic_refinement_admits_panic_to_ub`) |

The safe, zero-loop-overhead composition is **Theorem 1 (`checked_wrapper_recovers_total_equiv`)**: prove `PrecondMirAsmEquiv Pre ref asm` for the inner `asm!` kernel (where `Pre` typically asserts slice-length equality, non-overflow of accumulation bounds, or minimum vector length), and wrap it in a checked safe Rust entry point `if guard(q) { unsafe { asm(q) } } else { ref(q) }` (or an explicit upfront panic matching `ref`'s exact pre-unwind caller memory!) with `guard(q) = true -> Pre(q)`. This discharges `TotalMirAsmEquiv` for the exported safe Rust function with a single upfront branch outside the hot loop.

Note one sharp sub-case on **mutating loops with mid-loop panics**: if `ref` mutates `dst[0..i]` *before* panicking at index `i` (e.g., `dst.len() < src.len()`), an assembly implementation that panics upfront before writing `dst[0..i]` differs on `.panicked callerMem` (`L4`). Either (i) `ref` itself checks `assert_eq!(dst.len(), src.len())` before the mutation loop (making upfront panic exact), or (ii) the contract must explicitly declare panic-state nondeterminism on the Human Review Surface (which breaks callers using `catch_unwind` to inspect partial mutations in `dst`).

#### 1.2 Pointer Provenance, `MaybeUninit` Padding, and Aliasing Parity for Downstream Callers

`Basis: normative + source + execution + derived` (`support/RustAsmRefinementAndLoopEquiv.lean`, `partial-bijection-kripke-allocid-isomorphisms-and-provenance-stripping-laws`, `rust-inline-asm-and-external-asm-abi-seams-in-formal-verifiers`).

For substituting `asm!` in place of `ref` to preserve soundness for *all* downstream Rust callers under `Tree Borrows` and `MaybeUninit`, the relational output invariant over every modified or returned byte and pointer must satisfy four asymmetric laws:

1. **Asymmetric Byte Refinement (`OutputByteRefines`):** Representing abstract memory bytes as `AByte ::= uninit | init (byte : Nat) (prov : Option Nat)`:
   - Whenever `ref` produces `AByte.init b p` (an initialized scalar or pointer-carrying byte), `asm` **must** produce the identical `AByte.init b p`—both value `b` and provenance `p` (`outputByteRefines_rejects_uninit_for_init`, `outputByteRefines_rejects_provenance_strip`). Dropping provenance (e.g., copying pointer-containing structs via integer `asm!` loads/stores without a provenance-transferring membrane) causes UB when a downstream caller dereferences a copied pointer.
   - Whenever `ref` leaves a byte `AByte.uninit` (e.g., struct trailing padding or untouched `MaybeUninit<u8>` buffer slack), `asm` **may** write any concrete initialized byte `AByte.init b none` (`outputByteRefines_allows_concrete_padding_write`)—for instance, zeroing padding via a full-struct 16-byte SIMD store—because initializing previously uninitialized bytes monotonically refines MiniRust's `le_defined` order (`uninit <=_def init b none`). The reverse direction (leaving initialized bytes uninitialized) is unsound.
2. **Input `MaybeUninit` Tail Over-Read Independence (`PadIndependent`):** When a SIMD `asm!` loop loads aligned 16/32-byte chunks spanning initialized data plus caller-allocated `MaybeUninit<u8>` padding (`PaddedSlice<'a, const PAD: usize>`), the ISA proof universally quantifies over every concrete byte pattern `p1, p2` in the padding slots and proves `kernel x p1 = kernel x p2` (zero leakage of arbitrary hardware padding bytes into initialized Rust outputs or branches). Without a caller-owned `MaybeUninit` allocation covering the over-read span, over-reading past a plain `&[u8]` slice is spatial UB and faults on page boundaries (Section 3.3).
3. **Derived Pointer / Subslice Provenance Pinning (`SubslicePtrSound`):** When `ref` returns a subslice `&mut buf[k..]` or pointer derived from a caller allocation `(callerAlloc, callerLen)`, `asm!` computes an integer offset `k` (or pointer `base + k`) in a GPR. Reconstructing the returned Rust reference soundly requires proving `k <= callerLen` and reconstructing via provenance-carrying pointer arithmetic (`buf.as_mut_ptr().add(k)` / `slice::from_raw_parts_mut`, preserving `callerAlloc` and its `Tree Borrows` child tag) rather than integer-to-pointer forging across allocations.
4. **Aliasing Parity (`&mut [T]` vs. `&[T]` and `Tree Borrows` Protectors):** Because Rust `&mut [T]` and `&[T]` parameters carry function-lifetime `Tree Borrows` protectors (`state_machine_protected.md`), a verified `asm!` body receiving `dst: &mut [T]` and `src: &[T]` may assume strict spatial disjointness (`dst ∩ src = ∅`), matching `ref`. Conversely, for in-place/overlapping kernels (`memmove`, intra-frame copy), the safe reference cannot take both `&mut [T]` and `&[T]` aliasing the same slice—both twins must take a single `&mut [T]` plus index ranges so neither carries conflicting protectors. Furthermore, the assembly must satisfy **trace-level footprint containment** (`memaccess_inbounds` on every memory instruction, not merely final-state equality), ruling out transient writes into `&[T]` (`Frozen` UB even if the same byte is written back!) or stack red-zone violations under `options(nostack)`.

#### 1.3 Nondeterminism, Floating-Point Tolerances, and Opt-In 2-Safety Constant-Time Parity

`Basis: normative + execution + derived` (`support/RustAsmRefinementAndLoopEquiv.lean`, `superoptimization-smt-solver-fuzzing-and-rtl-contract-testing`, `observable-behavior-property-transfer-and-anneal-statement-forms`).

- **Integer/SIMD Bit-Exactness vs. IEEE-754 Nondeterminism:**
  - Integer, bitwise, and byte-slice kernels require **bit-exact** equality on all initialized output bytes.
  - Floating-point (`f32`/`f64`) kernels must explicitly declare one of three equivalence modes on the Human Review Surface:
    1. *Strict IEEE-754 bit-exact* (modulo Rust's nondeterministic NaN-payload rule when NaN is produced: matching `Minotaur`'s conditional `refines_relaxed_nan` where `(is_nan(ref) && is_nan(asm)) || bits(ref) == bits(asm)` holds *only* on arithmetic NaN-producing operations, while bit-copy/shuffle kernels preserve exact NaN payloads);
    2. *Algebraic reassociation / FMA contraction refinement* (valid only when `ref` explicitly uses `fadd_algebraic`/`fmul_algebraic` or `mul_add`, or declares a tolerance contract);
    3. *Quantitative ULP / absolute-epsilon bound* (`|ref(x) - asm(x)| <= k * ulp(ref(x))` plus exact finite/`±Inf`/`NaN` classification), which breaks transitivity of strict equality and must therefore live explicitly in the human-reviewed spec.
- **Opt-In 2-Safety Constant-Time Parity (`CtEquiv`):** Functional `TotalMirAsmEquiv` is a 1-safety/1-trace property and **does not** prevent a hyper-optimizing agent from replacing a constant-time Rust reference with a faster secret-branching or table-lookup `asm!` kernel (`functional_equiv_vs_ct_2safety` in `support/RustAsmRefinementAndLoopEquiv.lean`, an instance of McLean's Refinement Paradox). Cryptographic or secret-processing functions must opt into a **2-safety `LeakTrace` non-interference contract** (`∀ pub sec1 sec2, leak(asm, pub, sec1) = leak(asm, pub, sec2)`) recording every conditional branch PC, memory-access effective address, and variable-latency instruction (`div`, `idiv`, non-DOIT opcodes), ensuring that only branchless `cmov`/`csel`/SIMD-masking optimizations pass.

---

### 2. Zero-Overhead Rust Source-Level Pairing & Runtime CPU Feature Dispatch

`Basis: source + execution` (`support/probe_dispatch_and_stripping.py`, `support/probe_dispatch_and_stripping_results.json`, executed across `rustc 1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`).

#### 2.1 Pattern 1: Runtime CPU Feature Dispatch (`is_x86_feature_detected!`, `AtomicPtr` IFUNC, and `CpuToken`)

Comparing three runtime-dispatch idioms compiled with `-O --emit=llvm-ir,asm` across `rustc` `1.98.0-nightly` (`14210df0e`), `1.99.1` (`58cf8f9c3`), and `1.102.0-nightly` (`3ef0c22cd`) (plus `aarch64-unknown-linux-gnu` on `1.99.1`):

| Dispatch Pattern | Default `x86_64` (`SSE2` baseline) Codegen (`rustc 1.99.1 -O`) | Static `-C target-feature=+avx2` Codegen | Verification & Runtime Trade-offs |
| :--- | :--- | :--- | :--- |
| **1A. Per-call `if is_x86_feature_detected!("avx2")`** | Loads `std_detect::detect::cache::CACHE` (64-bit `AtomicUsize`, relaxed), tests `0` $\to$ cold `detect_and_initialize` (`CPUID` + `_xgetbv(0)` `XCR0`), tests bit, **tail-jumps** (`jmp sum_u8_avx2_asm` vs. `jmp sum_u8_reference`). `#[target_feature]` blocks inlining; `extern "C"` wrapper emits `.cfi_lsda` + `panic_cannot_unwind` because `detect_and_initialize` is not `nounwind`. | `is_x86_feature_detected!` constant-folds to `true`; **eliminates `CACHE` load, branch, and `sum_u8_reference` completely**, and **inlines `sum_u8_avx2_asm`** directly into caller! | Easiest to verify directly (`TotalMirAsmEquiv` over `if`/`else`); pays 1 atomic load + 1 branch + 1 tail-jump per call when AVX2 is not statically enabled. |
| **1B. `AtomicPtr` lazy IFUNC (`BurntSushi/memchr` `unsafe_ifunc!`, `src/arch/x86_64/memchr.rs:58-159`)** | Single relaxed load + indirect call (`movq DISPATCH_FN(%rip), %rax; callq *%rax; retq`, plus `panic_cannot_unwind` if `fn` pointer can unwind). First call runs `detect` and stores `find_avx2`/`find_sse2`/`find_fallback`. | Still performs indirect call through `AtomicPtr` unless separately `#[cfg(target_feature = "avx2")]`-bypassed. | Eliminates per-call feature bit-test overhead for tiny calls; verification must prove the global `AtomicPtr` invariant (`∀ stored ptr f, TotalMirAsmEquiv(ref, f) ∧ HostSupports(req(f))`). |
| **1C. Zero-sized `CpuToken<Avx2>` witness (`Avx2Token::try_new()`)** | **1 instruction (`jmp sum_u8_avx2_asm`)**: `0` branches, `0` atomic loads, `0` bytes passed, `0` `.cfi_lsda` / `panic_cannot_unwind` pads! | **Directly inlines `sum_u8_avx2_asm`** with zero dispatch overhead (`0` branches, `0` calls). | Optimal for inner loops where callers acquire `Avx2Token` once outside a batch/frame loop; discharges `#[target_feature]` statically via ghost ownership of `HostSupports("avx2")`. |

On `aarch64-unknown-linux-gnu` (`rustc 1.99.1 -O`), `std::arch::is_aarch64_feature_detected!("dotprod")` and `is_aarch64_feature_detected!("sve2")` lower to two 64-bit relaxed loads from `std_detect::detect::cache::CACHE` (`ldr x19, [x20]; cbz ...; ldr x0, [x20, #8]; cbz ...`) backed by `getauxval(AT_HWCAP)` / `AT_HWCAP2` (with `/proc/self/auxv` fallback, documented in `target-features-implications-detection-and-abi-effects`), followed by branchless `bfxil`/`ubfx`/`csel` bit extraction.

#### 2.2 Critical `rustc` Blind Spot: `asm!` Inside Non-`#[target_feature]` Functions and `#[inline(always)]` Version Shift

`Basis: source + execution` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`: `compiler/rustc_hir_typeck/src/inline_asm.rs:435-518`; `support/probe_dispatch_and_stripping.py`).

Testing five variants of AVX2 `asm!` inside a plain baseline `x86_64` (SSE2-only) function reveals a sharp compiler enforcement gap across **all three** tested toolchains (`1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`):

| Test Case (Default `x86-64`, No `#[target_feature]`) | `1.98.0-nightly` (`14210df0e`) | `1.99.1` (`58cf8f9c3`) | `1.102.0-nightly` (`3ef0c22cd`) | Compiler Behavior & Soundness Consequence |
| :--- | :---: | :---: | :---: | :--- |
| **`out(ymm_reg) _`** (register class) | Error (`rc=1`) | Error (`rc=1`) | Error (`rc=1`) | Rejected: `register class 'ymm_reg' requires the 'avx' target feature` (`inline_asm.rs:495`) |
| **`let _y: __m256i; out("ymm0") _y`** (typed reg) | Error (`rc=1`) | Error (`rc=1`) | Error (`rc=1`) | Rejected: `!op.is_clobber()` triggers `inline_asm.rs:463-501` |
| **`out("ymm0") _`** (discarded explicit clobber) | **Compiles (`rc=0`)** | **Compiles (`rc=0`)** | **Compiles (`rc=0`)** | **SILENT BYPASS**: `inline_asm.rs:435-463` exempts `op.is_clobber()` from target-feature checks, emitting raw `vpxor %ymm0, %ymm0, %ymm0` inside `"target-cpu"="x86-64"` with LLVM clobber downgraded to `~{xmm0}` (also omitting `vzeroupper`)! |
| **Raw AVX2 string + GPR / `out("xmm0") _`** | **Compiles (`rc=0`)** | **Compiles (`rc=0`)** | **Compiles (`rc=0`)** | **SILENT BYPASS**: `rustc` does not parse ISA feature requirements from template strings; emits bare `vpaddq %ymm0, %ymm0, %ymm0` with zero `#[target_feature]` fence! |
| **`#[inline(always)]` + `#[target_feature(enable = "avx2")]`** | Error (`rc=1`) | Error (`rc=1`) | **Compiles (`rc=0`)** | **Version transition**: hard error in `1.98.0`/`1.99.1`; accepted in `1.102.0-nightly`, where `caller_sse2` still **refuses to inline** (`jmp avx2_leaf`) while `caller_avx2` **inlines** `vpaddq` directly! |

Two subtle LLVM optimizer observations follow from `d_raw_avx2_string_with_gpr_only_and_hoist`:
- LLVM's `isSafeToSpeculativelyExecute` conservatively refuses to hoist even `options(pure, nomem, nostack)` inline `asm!` across a runtime `br i1 %cond` (in both `diamond_speculate_test` and `loop_licm_hoist_test`, LLVM unswitched the loop on `has_avx2` and hoisted the `asm!` *only inside* the `has_avx2 == true` preheader).
- **However, placing AVX2 `asm!` directly inside a non-`#[target_feature]` function remains unsound** for two reasons: (1) it bypasses Rust's `#[target_feature]` call-site `unsafe` guard and `TTI::areInlineCompatible` boundary, so callers without `avx2` can inline or call it silently and fault with `#UD`; and (2) `out("ymm0") _` silently downgrades to `~{xmm0}`, bypassing `X86InsertVZeroUpper` (`rust-inline-asm-and-external-asm-abi-seams-in-formal-verifiers`). Therefore, every post-baseline `asm!` kernel **must** live in its own `#[target_feature(enable = "...")]` function and be audited by a machine-instruction feature decoder.

#### 2.3 Pattern 2: Zero-Overhead Un-Gated Reference Twins (`Runtime(PostCleanup)` MIR vs. Binary Stripping)

`Basis: execution` (`support/probe_dispatch_and_stripping.py`, `support/probe_dispatch_and_stripping_results.json`).

Gating a reference function behind `#[cfg(anneal)]` or `#[cfg(not(target_arch = "x86_64"))]` causes **`#[cfg]` drift** because ordinary `cargo check`/`build`/`test` runs on `x86_64` stop compiling the reference function. Empirical compilation across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly` establishes that an **un-gated private reference twin** eliminates both `#[cfg]` drift and binary bloat simultaneously:

| Reference Twin Declaration (`-O -C target-feature=+avx2`) | Reaches `Runtime(PostCleanup)` MIR (`3-2-000`)? | Reaches `runtime-optimized` MIR (`3-3-000`)? | Present in `rlib` `.rcgu.o` (`nm -C`)? | Present in `cdylib` / `bin` (`nm -C`)? | Extra `.text` Bytes in `cdylib` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `#[allow(dead_code)] fn truly_unreferenced_private_twin(...)` (0 callers) | **Yes** (`rlib` & `bin`) | No (not demanded by mono) | **No** (`0` syms) | **No** (`0` syms) | **`0` B** (`298,122` vs. `298,122` B) |
| `#[allow(dead_code)] fn dead_branch_private_twin(...)` (inside dead `if cfg!(...)` else) | **Yes** (`rlib` & `bin`) | **Yes** | **No** (`0` syms) | **No** (`0` syms) | **`0` B** |
| `#[allow(dead_code)] fn generic_private_reference_twin<const K: u64>(...)` (uninstantiated) | **Yes** (`rlib` & `bin`) | No | **No** (`0` syms) | **No** (`0` syms) | **`0` B** |
| `#[inline(never)] pub fn pub_ref_large(...)` (uncalled `pub` with loop) | **Yes** | **Yes** | **Yes** (exported in `rlib`) | **No** (GC'd by linker) | `0` B in final `cdylib`/`bin`, non-zero in `.rlib` |

Because `rustc` builds `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked`) for every local body owner *before* monomorphization reachability pruning (`collect_and_partition_mono_items`), an un-gated `#[allow(dead_code)]` private reference twin (or private `mod reference`) is **always** typechecked, borrowchecked, and captured into `Mir.lean` by `anneal-rustc-capture` with **exact zero runtime and binary-size overhead** (`cdylib` `.text = 298,122` B, total `dec = 309,184` B byte-for-byte identical with and without a loop-bearing `#[inline(never)]` private twin), while remaining directly callable from `#[cfg(test)]` differential tests.

#### 2.4 Pattern 3: Multi-ISA Matrix (`1` Rust Reference $\leftrightarrow K$ Target Backends)

`Basis: execution` (`support/probe_dispatch_and_stripping.py`: `pattern3_multi_isa_and_aarch64_detect`).

A single un-gated `xor_checksum_reference(buf: &[u8]) -> u8` paired with `#[cfg(target_arch = "x86_64")]` AVX2 (`vpxor ymm0` + `vzeroupper`) and `#[cfg(target_arch = "aarch64")]` NEON (`eor v0.16b` + `ldr q1`) compiles cleanly on `rustc 1.99.1 -O` for both `--target x86_64-unknown-linux-gnu -C target-feature=+avx2` and `--target aarch64-unknown-linux-gnu`, sharing one human-reviewed reference specification across $K$ ISA backends (`x86_64` AVX2/AVX-512, `aarch64` NEON/SVE2, `riscv64` RVV, plus scalar fallback). Crucially, compiling only on `x86_64` discards the `#[cfg(target_arch = "aarch64")]` AST before MIR generation—meaning multi-ISA verification **must** run the capture and proof pipeline across every configured `(target_triple, feature_tier)` cell in CI (Section 4).

---

### 3. Proof Automation & Rapid Counterexample Loops for Agent-Written Hot Loops

#### 3.1 Equivalence Paradigms Compared Across Real Hot-Loop Optimizations

`Basis: normative + source + derived` (`bchurchill/pldi19-equivalence-checker@2e7707be`, `mattulbrich/llreve@68cb958c`, `boogie-org/symdiff@54835f0f`, `Tristan & Leroy POPL 2010`, `carcara-alethe-lrat-spacer-chc-elaboration-into-pass1-lean-certificates`, `cryptol-saw-symbolic-equivalence-easycrypt-game-hopping-and-cryptoline`).

Comparing the three dominant verification architectures against the specific hot-loop transformations AI coding agents and performance engineers actually write:

| Optimization Family | Two-Stage Functional Lifting (`MIR -> f` + `ASM -> f` in Lean) | Direct Relational / Product Program (`BiAlign`/`BiGKAT`, CompCert, `DDEC`/`PAA`, `SymDiff`, `Rêve`) | Untrusted SMT / E-Graph / CAS $\to$ Pass-1 Lean 4 Certificate (`Carcara`, `LRAT`, `egglog`, Groebner) |
| :--- | :--- | :--- | :--- |
| **Alignment prolog + $4\times$/$8\times$ unrolled main loop + masked/scalar epilog** (`BurntSushi/memchr` `src/arch/generic/memchr.rs:54-107`) | Cleanly factors if `f` is an associative monoid/scan (`sum`, `xor`, `memchr` first-match), eliminating cross-program state coupling | **`prolog_unroll_epilog_equiv` / `BiAlign`** discharges in linear $O(|P|)$ proof size (`1`-to-$U$ tile induction); `llreve` (`InferMarks.cpp`) & `SymDiff` (`MutualSummary.cs`) struggle without manual loop unroll marks; `DDEC`/`PAA` (`paa.h`) auto-discovers multi-block `CfgPath` edges from traces but needed up to `1000 CPU-hours` on hard TSVC loops (`README.md:24`) | `Z3`/`Spacer` CHC or `Crab` `SplitDBM` synthesizes index-bound invariants (`i % U == 0 ∧ i <= len`), lowered to `<5 ms` Pass-1 `OmegaCutCert` / `SplitDbmHornCert` |
| **Software pipelining (overlapped prolog / kernel / epilog iterations)** | Hard to lift an in-flight kernel `K` directly to `f` without explicitly writing the drain state | **Tristan & Leroy (POPL 2010) algebraic commutation** (`E (P s) = iterN B mu s`, `E (K t) = iterN B delta (E t)` $\implies$ `software_pipelining_equiv`) discharges cleanly with **zero loop invariant guessing**—only two straight-line symbolic evaluations! | Straight-line obligations `E(P(s)) = B^mu(s)` and `E(K(t)) = B^delta(E(t))` are loop-free and discharge via `egglog` (`CongruenceDag`) or `cvc5`/`Carcara` $\to$ `RupLratTrieCert` |
| **Loop fusion / tiling** | Natural when fused stages match pure functional composition `g ∘ f` | Requires cross-loop permutation / commutativity side conditions (dependence analysis) | `egglog` / CAS proves algebraic commutativity; `SplitDBM` proves non-aliasing index bounds |
| **SWAR (`u64` 8-byte bit-twiddling), BMI2 (`pext`/`pdep`/`bzhi`), branchless `cmov`/`csel`** | Trivial pure bitvector spec `f : BitVec 64 -> ...`; avoids memory reasoning entirely | Per-iteration tile equality reduces directly to a loop-free bitvector identity | **Bit-blasted `QF_BV` (`CaDiCaL` $\to$ `RupLratTrieCert` in `<5 ms` Pass-1 Lean)** solves `64`-bit SWAR/BMI2/branchless straight-line identities automatically |
| **Division-by-constant magic multiply-shift** (Granlund & Montgomery PLDI 1994) | Pure arithmetic theorem over `Nat`/`BitVec` (`mulhi + shift` == `n / d`) | Straight-line relational identity | `QF_BV` bit-blasting stalls on `64×64 -> 128`-bit multipliers; **CryptoLine-style CAS (`Singular`) + linear range (`OmegaCutCert`)** proves $\lfloor n / d \rfloor$ in milliseconds over $\mathbb{Z}$ |
| **SIMD `.rodata` shuffle/gather LUTs** (`VPSHUFB`, `VPGATHERDD`) + **unaligned over-reads** | Explicit finite lane index map + `.rodata` constant array + `PadIndependent` predicate | `Rake`-style per-lane cone-of-influence slicing avoids 256/512-bit bit-blasting explosion | Per-lane `QF_BV` $\to$ `RupLratTrieCert` plus `SplitDBM` bounds proof (`idx < table.len` and `ptr + width <= alloc_end`) |

**Architectural Synthesis (`Basis: derived`):** Neither pure functional lifting nor pure monolithic product-program SMT dominates across all hot loops. The optimal hybrid pipeline for agent-written Rust-vs-`asm!` optimization is:
1. **Structural decomposition in Pass-1 Lean (`theory/`):** Use `prolog_unroll_epilog_equiv` for misaligned prolog + $U$-unrolled kernel + epilog loops, and **`software_pipelining_equiv`** (Tristan & Leroy POPL 2010) whenever an agent overlaps load/compute/store stages across iterations (proved in `mac_software_pipelined_exact` with zero loop-invariant synthesis—both `h_pe` and `h_ke` close by `rfl`!).
2. **Loop-free leaf discharge via untrusted solver certificates replayed in Pass-1 Lean:** Discharge the resulting finite straight-line tile/commutation obligations outside the TCB with `QF_BV` SAT/SMT (for SWAR, BMI2, `cmov`, per-lane `VPSHUFB` LUTs) or CAS+range splitting (for magic-multiplier division and wide multiply-accumulate), elaborating into `<5 ms` Pass-1 Lean 4 certificates (`RupLratTrieCert`, `OmegaCutCert`, `CongruenceDag`, `SplitDbmHornCert` per `carcara-alethe-lrat-spacer-chc-elaboration-into-pass1-lean-certificates`) so no external solver enters the TCB.

#### 3.2 Concrete Arithmetic & Bit-Twiddling Traps Verified by Exhaustive Probes

`Basis: source + execution` (`BurntSushi/memchr@bd6068c3`: `src/arch/all/memchr.rs:260-269, 875-885, 985-995`; `support/probe_hot_loop_tricks_and_fuzz.py`, `support/probe_hot_loop_tricks_and_fuzz_results.json`, `support/RustAsmRefinementAndLoopEquiv.lean`).

Exhaustive execution over exact finite domains exposes four recurring bugs where agent-written hot-loop optimizations pass standard small-input test suites yet fail formally:

| Hot-Loop Trick | Exact Domain Tested | Observed Bug & Minimal Counterexample | Sound Replacement |
| :--- | :--- | :--- | :--- |
| **SWAR zero-byte test** (`(w - LO) & !w & HI`, `memchr` `src/arch/all/memchr.rs:884`) | All `65,536` 2-byte pairs `[0..255]^2` (`171.61 ms`) + `memchr` `regression_count_new_lines` | **`0/65,536` errors for `find`**, but **`1/65,536` error for `count` & `rfind`** at `(0x00, 0x01)` (borrow from byte 0 into byte 1 sets false `0x80` bit in byte 1). On `BurntSushi/memchr`'s exact 8-byte chunk `b"\x0b\n\x0b\n\x0b\n\x0b\n"`, true count = **`4`**, classic Mycroft returns **`7`** (`swar_memchr_borrow_corruption_witness`). | Borrow-isolated SWAR `~(((w & 0x7F...) + 0x7F...) \| w \| 0x7F...) & 0x80...`: **`0/65,536` errors** across `find`, `rfind`, and `count`, exact count **`4`** on `memchr` witness. |
| **Division-by-constant magic multiply-shift** (`u16`, Granlund & Montgomery PLDI 1994) | All `65,536` `u16` values (`38.47 ms`) | `d = 7` naive floor `(n * 0x9249) >> 18`: **`9,362` errors** (first at `n = 7`: `0` vs. `1`). Naive ceil `(n * 0x924A) >> 18`: **`3,121` errors** (first at **`n = 43,693`**: `6,242` vs. `6,241`—invisible to tests with `n < 43,693`!). `d = 100` naive `(n * 0xA3D8) >> 22`: **`219` errors** (first at **`n = 43,699`**: `437` vs. `436`). | `d = 3` (`0xAAAB >> 17`), `d = 10` (`0xCCCD >> 19`), `d = 100` pre-shifted `((n >> 2) * 0xA3D8) >> 20`, and `d = 7` GM 17-bit add-shift `q = (n * 0x2493) >> 16; (((n - q) >> 1) + q) >> 2`: **`0/65,536` errors** on all four divisors. |
| **x86 BMI2 `bzhi`** (`SRC2[7:0]` width mask) | Boundary indices `64` vs. `256` | `bzhi(src, 64)` preserves all 64 bits, matching `if idx >= 64 { src }`, **but `bzhi(src, 256)` masks `256 & 0xFF = 0` and zeroes all 64 bits (`0` vs. `0xFFFF_FFFF_FFFF_FFFF`)**! | Precondition `idx < 256` (or saturating `idx.min(64)`) proved before `bzhi`. |
| **SSSE3/AVX2 `pshufb` `.rodata` 16-byte LUT** | All `256` index byte values | Unmasked `pshufb` zeroes every lane whose index has bit 7 set (`128/256` mismatches; first at `b = 128`: `0` vs. `lut[0] = 1`). | Explicit `vpand` with `0x0F` (or verified ASCII `< 0x80` precondition) prior to `pshufb`. |

#### 3.3 Fast Agent Counterexample Loop: Native Guard-Page Differential Fuzzing + Bounded Symexec Before Lean Proof

`Basis: execution + derived` (`support/probe_hot_loop_tricks_and_fuzz.py`: `native_guard_page_harness`, `counterexample-trace-shrinking-span-blame-assignment-and-agent-proof-repair`).

Asking an AI agent to jump directly from handwritten `asm!` to a full Lean 4 proof wastes minutes per iteration debugging trivial off-by-one, alignment, or page-boundary over-read bugs through opaque proof goals. Staging a **three-tier pre-proof counterexample funnel** accelerates agent convergence by orders of magnitude:

1. **Tier 1 (`~1–5 ms` runtime, `~186 ms` compile): `checkasm`-style Native Differential + OS Guard-Page Harness:**
   - Generates structured adversarial boundaries: edge lengths `len ∈ {0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257}`, all misaligned start offsets `0..31` (or `0..63` for AVX-512), extremal byte patterns (`0x00`, `0x01`, `0x7F`, `0x80`, `0xFF`, `0x0A`/`0x0B`), aliasing/self-overlap buffers, callee-saved register canaries, and **`mmap` + `mprotect(PROT_NONE)` leading and trailing guard pages**.
   - **Empirical discriminator (`support/probe_hot_loop_tricks_and_fuzz_results.json`):** Compiling a real Rust + x86_64 inline `asm!` harness with `rustc 1.99.1 -O` (`186.02 ms`), a buggy agent kernel that performs an unguarded 16-byte SSE2 `movdqu` load for `0 < len < 16` **passes `22/22` normal heap `Vec` unit tests (`rc = 0`)** because allocator buckets leave trailing bytes mapped—yet **crashes immediately with `SIGSEGV` (`rc = -11`)** when `len = 1` is placed flush against the trailing `PROT_NONE` guard page (`rw + PAGE - 1`)! After replacing it with a 4x-unrolled 64-byte SSE2 `psadbw` + 16-byte loop + exact scalar tail, all **`748` checks** (`22` lengths $\times$ `(trailing guard + leading guard + 32 misaligned offsets)`) pass in **`1.32 ms`**.
2. **Tier 2 (`~0.1–10 s` per kernel, untrusted): Bounded Symbolic Execution / `QF_BV` SMT (`Z3` / `Bitwuzla` / `CBMC` / `KLEE`):**
   - Catches measure-zero arithmetic corner cases invisible to Tier 1 fuzzing (such as the `1/65,536` SWAR `(0x00, 0x01)` borrow bug, `n = 43,693` magic-multiplier overflow, or `(-32768, -32768)` `vpmulhrsw` wrap-around) by symbolically executing the unrolled tile (`1..4` iterations) and extracting a concrete shrunken counterexample (`Class Ib`) before invoking Lean.
3. **Tier 3 (Unbounded, TCB-final): Kernel-Checked Pass-1 Lean 4 Proof + Certificate Replay:**
   - Once Tiers 1 and 2 find zero counterexamples, the agent discharges the unbounded inductive theorem (`TotalMirAsmEquiv` via `checked_wrapper_recovers_total_equiv`, `prolog_unroll_epilog_equiv`, or `software_pipelining_equiv`) plus untrusted-solver proof certificates in Lean `v4.34.1` (`0.69 s` in our mechanization).

---

### 4. CI Enforcement & Anti-Reward-Hacking Guarantees Under a Two-Surface Threat Model

`Basis: normative + source + execution` (`joshlf/anneal@c131b320`: `THREAT_MODEL.md:58-281`, `docs/trust-model.md:55-315`; `support/probe_ci_spec_surface_gate.py`, `support/probe_ci_spec_surface_gate_results.json`; `frontier-ai-lab-binary-verification-oss-fuzz-proofs-and-agent-reward-hacking`).

Under Anneal's two-surface threat model (`THREAT_MODEL.md:66-114`), a human reviewer audits **only** (1) the **stated specifications** (plus everything their meaning transitively depends on) and (2) the **TCB audit log**, and can safely ignore all implementation bodies and Lean proofs. When a hot-loop optimization PR treats the **Rust reference function `foo_reference` as the stated specification**, CI must close six adversarial agent reward-hacking vectors totally:

| # | Agent Reward-Hacking Vector | Concrete Exploitation Mechanism | Mandatory Deterministic CI Gate |
| :-: | :--- | :--- | :--- |
| **1** | **Transitive reference tampering** (`THREAT_MODEL.md:238-247`) | PR leaves `foo_reference` syntactically untouched while modifying a helper function (`mix_byte`), `const`, type definition, or trait impl it calls so both twins trivially return `0`. | **Transitive MIR `SpecConeHash` gate:** Extract `Runtime(PostCleanup)` MIR from `rustc` (never regex over `.rs` text), compute the transitive closure of every `DefId` (callees, `AdtDef`s, `const`s, trait impls) reachable from `foo_reference`, strip line-number comments only, and hash canonical MIR. Any change to `SpecConeHash` **blocks auto-merge and flags the PR on the `Human review surface`** (`CODEOWNERS` / required spec-owner sign-off). |
| **2** | **Precondition weakening / domain truncation** (`Footnote 06`, `VerusEval`) | PR adds `requires(len == 0)` or changes public signature / `unsafe` contract so `asm!` only covers trivial inputs. | **Public-API `TotalMirAsmEquiv` lock:** Exported safe functions MUST prove `TotalMirAsmEquiv` with zero extra preconditions; any edit to a public function signature or `unsafe fn` `Pre` mutates the locked `SpecConeHash` / `Human review surface`. |
| **3** | **`#[cfg]` split-brain & single-arch blind spot** | PR gates verified code under `#[cfg(anneal)]` while shipping buggy `asm!` under `#[cfg(not(anneal))]`, or breaks `#[cfg(target_arch = "aarch64")]` when CI runs only `x86_64`. | **Release-`cfg` parity + full target matrix:** Capture using the exact release `cfg` flags (relying on Pattern 2's un-gated private `foo_reference`), forbid verification-only `cfg` flags on verified items, and run CI across every `(target_triple, feature_tier)` cell present in `#[cfg(target_arch/target_feature)]`, failing closed on any unverified `InlineAsm` / `#[unsafe(naked)]` item. |
| **4** | **Missing runtime CPU feature guard / `out("ymm0") _` bypass** | PR exploits `inline_asm.rs:435-463` to put AVX2 mnemonics into a baseline function via `out("ymm0") _` or GPR operands without `#[target_feature]` or `is_x86_feature_detected!`. | **Machine-byte ISA feature decoder gate:** Decode the assembled bytes of every `asm!` / `naked_asm!` block and assert `RequiredFeatures(decoded_insns) ⊆ EffectiveTargetFeatures(fn)`, plus prove `HostSupports(F)` (`CPUID + XGETBV(0)` / `getauxval` / `CpuToken<F>`) at every call site reaching `#[target_feature(enable = F)]`. |
| **5** | **Unverified fallback arm, false `options(...)`, or hidden `#[anneal::trusted]`** | PR proves only the AVX2 arm while shipping an unverified SSE2/scalar fallback, lies in `options(nomem, preserves_flags)`, or slips in `#[anneal::trusted]`. | **Whole-dispatcher equivalence + TCB audit log:** Prove `TotalMirAsmEquiv(reference, dispatch)` over the top-level dispatcher (covering all branches / `AtomicPtr` targets), prove every `asm!` `options(...)` promise from ISA trace semantics (including `vzeroupper`, `FPSR.QC`, `vstart == 0`), and surface every `#[anneal::trusted]` waiver in the human-reviewed TCB audit log. |
| **6** | **Runner tampering or stale incremental cache** (`THREAT_MODEL.md:126-180`, `oss-verify-proofs` `oft check`) | PR edits CI scripts, `build.rs`, proc-macros, or relies on stale cached proofs after toolchain/flag/helper changes. | **Base-branch isolated runner + deterministic per-function cache key:** Execute `anneal-rustc-capture`, Lean kernel replay (`-DElab.async=false -Ddebug.skipKernelTC=false`, zero `sorryAx`, locked 3-axiom foundation), and `SpecConeHash` diff strictly from the protected base-branch workflow inside an OS sandbox (`--network none`), keying per-function verification caches on `SHA-256(toolchain_digest || rustc_version || target_and_flags || SpecConeHash(ref) || ImplMirAndBytesHash(asm) || ProofConeHash)`. |

#### Executable Verification of the Transitive `SpecConeHash` & Incremental Cache Gate

`Basis: execution` (`support/probe_ci_spec_surface_gate.py`, `support/probe_ci_spec_surface_gate_results.json` on `rustc 1.99.1`).

Running `probe_ci_spec_surface_gate.py` against real `Runtime(PostCleanup)` MIR dumps for a crate containing `checksum_ref` (calling `mix_byte` and reading `const SEED`), `checksum_asm`, and `unrelated_fn` resolves `base.spec_cone = ["checksum_ref", "mix_byte"]` and verifies all four PR mutation classes:

| PR Mutation Scenario | `SpecConeHash` Changed? | `CacheKey` Changed? | Requires Human Spec Review? | Triggers Re-Verification? |
| :--- | :---: | :---: | :---: | :---: |
| **1. Edit `unrelated_fn` (shifting source line numbers)** | `false` | `false` | **No** | **No (cache HIT)** |
| **2. Hyper-optimize `checksum_asm` only** (`imul 31` $\to$ `shl 5; sub`) | `false` | `true` | **No** (auto-verifiable!) | **Yes (`checksum_asm` only)** |
| **3. Leave `checksum_ref` untouched; tamper with helper `mix_byte`** | **`true`** | **`true`** | **Yes (blocks on Human Review Surface!)** | **Yes** |
| **4. Change compiler target flags (`-C target-feature=+avx2`)** | `false` | **`true`** | No | **Yes (invalidates stale target cache)** |

## Boundaries

- **Not examined — Local execution of external SMT/symbolic tools (`Z3`, `Bitwuzla`, `cvc5`, `CBMC`, `KLEE`, `Singular`):** None of those external binaries were installed on the test host (`x86_64-unknown-linux-gnu`); findings on `DDEC`/`PAA`, `llreve`, `SymDiff`, `CryptoLine`, and `Carcara` derive from primary upstream source inspection and peer-reviewed specifications rather than live execution of those tools.
- **Not examined — Physical execution on `aarch64` or `riscv64` silicon:** `aarch64-unknown-linux-gnu` findings come from live `rustc 1.99.1` cross-compilation (`--emit=llvm-ir,asm`) and `std_detect`/ABI specifications; native `mmap`/`mprotect` guard-page execution ran on Linux `x86_64` only.
- **Not examined — Full `anneal-audit` integration of [`support/RustAsmRefinementAndLoopEquiv.lean`](support/RustAsmRefinementAndLoopEquiv.lean):** The module uses `prelude` + 5 locked `Init.*` modules and was kernel-checked directly under Anneal's pinned `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false` (0 errors, 0 `sorryAx`, 9/10 theorems axiom-free and 1/10 `[propext]`); however, because it was not run through `anneal-audit`'s `TrustedBoundary.lean` syntax preflight, minor infix notations (`-`, `%` in `swarMycroft16`) would need replacing with `Nat.sub`/`Nat.mod` before checking into Anneal's strict Pass-1 `theory/` tree.
- **Not examined — Trait-impl / `AdtDef` traversal inside the standalone `probe_ci_spec_surface_gate.py` script:** The support script parses `-Z dump-mir=runtime-post-cleanup` textual call edges to demonstrate transitive callee hashing (`checksum_ref -> mix_byte`), whereas a production CI gate inside `anneal-rustc-capture` must walk `rustc`'s structured `TyCtxt` MIR/type/trait-resolution graph directly so generic monomorphizations, `const` items, `AdtDef` layouts, and trait method resolutions cannot evade text matching.
- **Unknown — End-to-end LLM convergence speedup from combining guard-page fuzzing + bounded SMT + Lean 4 proofs on a large unseen hot-loop corpus:** Quantitative token/turn reductions across diverse production Rust crates remain unmeasured empirically.
- **Known not to apply — Relying on `rustc` to reject post-baseline ISA instructions inside `asm!`:** As proved empirically across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`, `rustc` accepts both `out("ymm0") _` and raw AVX2 instruction strings inside non-`#[target_feature]` functions (`inline_asm.rs:435-463`).
- **Known not to apply — Relying on normal heap `Vec` differential tests to catch SIMD tail over-reads:** As proved by `native_guard_page_harness` (`HEAP_BUGGY_PASSED=22` vs. `SIGSEGV` at `PROT_NONE`), standard heap tests silently mask out-of-bounds vector over-reads that fault at OS page boundaries.
- **Unsupported — Direct operational verification of `TerminatorKind::InlineAsm` in baseline `joshlf/anneal@c131b320`:** Baseline `Trusted/MirAst.lean:782-796` maps `InlineAsm` to `TerminatorKind.unsupported` (failing closed to `FaultKind.unsupported`), so discharging real `asm!` blocks requires coupling `Trusted.MirSemantics` to a mechanized ISA model (`Sail`/x86/AArch64/RVV) across the state-bridge contract established in Section 1.

## Evidence

### Primary Upstream Sources and Peer-Reviewed Specifications (Observed `2026-11-20`)

- **`rust-lang/rust` (`1.98.0-nightly` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.99.1` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.102.0-nightly` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):**
  - `compiler/rustc_hir_typeck/src/inline_asm.rs:424-518` (`InlineAsmCtxt::check_asm`: `if !op.is_clobber()` explicit target-feature exemption for explicit-register clobbers such as `out("ymm0") _`).
  - `compiler/rustc_codegen_llvm/src/asm.rs:53-115, 688-805` (`reg_to_llvm` lowering of discarded `ymm` outputs to `xmm`).
  - `compiler/rustc_codegen_ssa/src/target_features.rs:143-186` (`asm_target_features` and `#[inline(always)]` + `#[target_feature]` legality transition in `3ef0c22cd`).
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** `src/inline-assembly.md` (`r[asm.rules.unwind]`, `r[asm.rules.mem-same-as-ffi]`, `options(...)`), `src/attributes/codegen.md` (`#[target_feature]`).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `THREAT_MODEL.md:58-281` (two-surface bounded human review, hidden specification dependencies, dev vs. CI boundary), `docs/trust-model.md:55-315` (Statement-Origin Separation and `anneal-audit`), `trusted/rustc-capture/src/driver.rs:25-152` (compiler version pin and clean-analysis gating).
- **`BurntSushi/memchr` (`bd6068c30e9074a90c285e47912fa0b047d07597`):** `src/arch/x86_64/memchr.rs:58-159` (`unsafe_ifunc!` `AtomicPtr` dispatch), `src/arch/generic/memchr.rs:50-125` (aligned prolog, `LOOP_SIZE = 4 * V::BYTES`, overlapping tail), `src/arch/all/memchr.rs:256-269, 875-885, 985-995` (`has_zero_byte` Mycroft SWAR and `regression_count_new_lines` `\x0b\n` failure).
- **Relational & Loop Equivalence Systems and Papers:**
  - `bchurchill/pldi19-equivalence-checker@2e7707be99c10828970f1d96c2bcbb058936cbdc` (`README.md:10-25`, `src/validator/paa.h:32-95`; Churchill, Padon, Sharma, Aiken, PLDI 2019, DOI `10.1145/3314221.3314596`).
  - `mattulbrich/llreve@68cb958c1c02177fa0db1965a8afd879a97c2fc4` (`reve/reve/lib/InferMarks.cpp:26-51`; Felsing et al., ASE 2014, DOI `10.1145/2642937.2642987`).
  - `boogie-org/symdiff@54835f0f85c0562b653a219b7a43c794504b3e29` (`Sources/SymDiff/source/MutualSummary.cs:15-80`; Lahiri et al., CAV 2012, DOI `10.1007/978-3-642-31424-7_54`).
  - Tristan & Leroy, *A Simple, Verified Validator for Software Pipelining*, POPL 2010 (DOI `10.1145/1706299.1706311`).
  - Granlund & Montgomery, *Division by Invariant Integers using Multiplication*, PLDI 1994 (DOI `10.1145/178243.178249`).

### Preserved Executable Support Artifacts (`support/`, Executed `2026-11-20` on Linux `x86_64`)

| Artifact Path | SHA-256 | Basis & Recorded Observation |
| :--- | :--- | :--- |
| [`support/RustAsmRefinementAndLoopEquiv.lean`](support/RustAsmRefinementAndLoopEquiv.lean) | `53fe19630c1bd838aa4d0646de737c118df07314151a7fb928f1dcf7820e0f6a` | **execution + derived**: Kernel-checked by `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) in `0.69 s` (`160,912 KB` RSS); 9/10 theorems axiom-free, 1/10 `[propext]`, 0 `sorryAx`. |
| [`support/probe_dispatch_and_stripping.py`](support/probe_dispatch_and_stripping.py) | `e466500a7b8f4bbb20ea47bc377cebdcf45f8616373db36f15cf145ac3322c7f` | **execution**: Multi-toolchain (`1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`) `rustc` probe testing Patterns 1–3, `out("ymm0") _` feature bypass, `#[inline(always)]` + `#[target_feature]` transition, `Runtime(PostCleanup)` MIR vs. `nm`/`size` (`298,122` B parity), and `aarch64` cross-compilation. |
| [`support/probe_dispatch_and_stripping_results.json`](support/probe_dispatch_and_stripping_results.json) | `c3d2e513798baeb3551e4f647c1eb3698f2f58f09ec57b99658c5bd3f49172d8` | **execution**: Recorded JSON output from `probe_dispatch_and_stripping.py`. |
| [`support/probe_hot_loop_tricks_and_fuzz.py`](support/probe_hot_loop_tricks_and_fuzz.py) | `e992afd90a71f9fbbc6ba61b0b7ba72f2780ad02dcb79e34027776f581f96e75` | **execution**: Exhaustive `65,536`-state SWAR (`171.61 ms`) and Granlund-Montgomery `u16` division (`38.47 ms`) checkers, BMI2 `bzhi` / `pshufb` witnesses, and native Linux `x86_64` `rustc 1.99.1` `mmap`/`mprotect(PROT_NONE)` guard-page differential harness (`HEAP_BUGGY_PASSED=22` vs. `SIGSEGV`, `FIXED_GUARD_CHECKS_PASSED=748` in `1.32 ms`). |
| [`support/probe_hot_loop_tricks_and_fuzz_results.json`](support/probe_hot_loop_tricks_and_fuzz_results.json) | `1cd198dd5be4294ff0591422d497dab5b4ea7e8064736cf56cb7e21e77a2787f` | **execution**: Recorded JSON output from `probe_hot_loop_tricks_and_fuzz.py`. |
| [`support/probe_ci_spec_surface_gate.py`](support/probe_ci_spec_surface_gate.py) | `60fccc9cf7a88e4f6c2b773edc0a97df035ccdf7765f6aee08000f64b2985113` | **execution**: Real `rustc 1.99.1` `-Z dump-mir` transitive `SpecConeHash` + per-function `CacheKey` gate validating all 4 PR mutation scenarios (`checksum_ref -> mix_byte`). |
| [`support/probe_ci_spec_surface_gate_results.json`](support/probe_ci_spec_surface_gate_results.json) | `8f225def1388db7862b0c6f1696c9653193d733313d9ef19e5a1b193483cb6bb` | **execution**: Recorded JSON output from `probe_ci_spec_surface_gate.py`. |

## Revalidation

Run the following deterministic checks from the report package directory to revalidate every mechanized theorem and empirical compiler/runtime probe (`< 10 s` total on Linux `x86_64` with `rustc` and `lean` `v4.34.1`):

1. **Kernel-check all 10 Lean `v4.34.1` theorems (`~0.7 s`):**
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/RustAsmRefinementAndLoopEquiv.lean
   ```
   Verify exit code `0` and that all `#print axioms` lines show either no axioms or `[propext]` only (zero `sorryAx`, zero `Lean.ofReduceBool`).
2. **Re-run `rustc` dispatch, `out("ymm0") _` clobber bypass, `Runtime(PostCleanup)` MIR, and binary-stripping probes (`~4 s`):**
   ```bash
   python3 support/probe_dispatch_and_stripping.py
   ```
   Check whether newer `rustc` revisions fix the `inline_asm.rs:463` `!op.is_clobber()` exemption (if `a_discarded_explicit_ymm0.rc` flips from `0` to `1`), whether `#[inline(always)]` + `#[target_feature]` stabilizes, and whether `exact_zero_byte_overhead` and `truly_unreferenced_private_twin` `runtime-post-cleanup` MIR presence remain `true`.
3. **Re-run exhaustive SWAR/division/BMI2 probes and native OS guard-page differential harness (`~0.5 s`):**
   ```bash
   python3 support/probe_hot_loop_tricks_and_fuzz.py
   ```
   Confirm `mycroft_count_mismatches == 1`, `borrow_free_count_mismatches == 0`, `d7_gm_addshift_mismatches == 0`, `d100_preshift_fixed_mismatches == 0`, `guard_buggy_killed_by_sigsegv == true`, and `FIXED_GUARD_CHECKS_PASSED=748`.
4. **Re-run the CI transitive MIR `SpecConeHash` and incremental cache-key gate (`~1.5 s`):**
   ```bash
   python3 support/probe_ci_spec_surface_gate.py
   ```
   Confirm exit code `0` (all four scenario assertions pass).
