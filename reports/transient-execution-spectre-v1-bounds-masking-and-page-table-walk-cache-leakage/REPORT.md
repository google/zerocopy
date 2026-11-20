# Speculative Execution Leakage Contracts, Bounds-Masking vs. SLH Soundness, and Page-Table-Walk Cache Side Channels

## Summary

Architectural constant-time (`CT`) guarantees collapse along two distinct hardware-software seams: transient control-flow/store misprediction (`Spectre-v1`, `v1.1`, `v4`) and implicit microarchitectural state emitted by hardware page-table walks (`PTW`s) and Translation Lookaside Buffers (`TLB`s). Synthesizing primary specifications, academic semantics, and production compiler passes yields four verifiable invariants:

1. **Hierarchy of Hardware-Software Leakage Contracts (`⟦·⟧^τ_σ`):** Speculative non-interference (`SNI`, Guarnieri et al., IEEE S&P 2020) enforces that mispredicted paths leak no more than sequential execution, permitting benign architectural declassifications (`#declassify`), whereas speculative constant-time (`SCT`, Cauligi et al., PLDI 2020; Barthe et al., IEEE S&P 2021) requires full observational equivalence across all low-equivalent inputs. Under `#declassify`, `SCT` strictly exceeds `CT ∧ SNI` unless `#declassify` retains speculative taint `(Sec, Sec) ↦ (Pub, Sec)` (*Spectre Declassified*, IEEE S&P 2023). Across compiler passes, source-level mitigations require robust speculative preservation (`RSNI`/`RSCT`, Patrignani & Guarnieri, CCS 2021) so register spilling and bounds-check elimination do not reintroduce transient leaks. **Basis: normative, source, documentation.**
2. **Mitigation Asymmetries Between Local Index Masking, `SLH` Variants, and Serialization Fences:** Stateless bounds clamping (`array_index_nospec` in Linux `nospec.h`) isolates only single-branch array offsets, breaks across nested predicates lacking cumulative misspeculation state (`MSF`), requires `size <= 2^63` in the generic shift formula, and lacks hardware barriers on RISC-V (`barrier_nospec()` is a no-op). Post-Load Value Speculative Load Hardening (`vSLH`, `hardenPostLoad` in LLVM `X86SpeculativeLoadHardening.cpp`) masks loaded data *after* dispatch, leaving the first load address observable via L1D cache fills and `PTW` cache lines, while Address SLH (`aSLH`, `hardenLoadAddr`) still leaks pre-existing secret registers through non-memory variable-time transmitters (`udiv`/`imul`) unless strengthened to Ultimate SLH (`USLH`, USENIX Security 2023) or serializing fences (`lfence` / `dsb nsh; isb` / `csdb`). Moreover, upstream LLVM (`1cfbf0a8`) contains SLH backends for X86 and AArch64 but **zero SLH backend for RISC-V**. **Basis: source, documentation, execution.**
3. **Radix `PTW` and `TLB` Cache Leakage Breaks Multi-Page Constant-Time Lookup Tables:** Even under architectural `CT` or `vSLH`, 3-level `Sv39` and 4-level x86-64 `IA-32e` walks index `8`-byte PTEs at `ppn * 4096 + vpn[lvl] * 8`, grouping `8` PTEs per 64-byte cache line. Accessing any table spanning `> 4 KiB` leaks `VPN[0][8:3]` (every `32 KiB` stride) into shared LLC lines (`AnC`, NDSS 2017) and leaks `VPN[0]` page index (`4 KiB` stride) via shared TLB sets (`TLBleed`, USENIX Security 2018), while walker-port contention (`Binoculars`, USENIX Security 2022) leaks `VA[11:6]` within a single 4 KiB page. Speculative RISC-V walks (`supervisor.adoc:1797–1809`) further dirty `A`-bit PTE cache lines under `Svadu`. **Basis: normative, source, execution, documentation.**
4. **Combined `SCT + PTW` Verification Obligations:** Closing both seams requires tracking 2-bit `(normal, speculative)` taint with a cumulative 3-state `MSF` automaton (`toinit | Exact | Trans`), hard-masking **both** load/store addresses and variable-time operands (`USLH` or fence), and enforcing single-page confinement (`<= 4 KiB`) or pinned `2 MiB` superpage mappings for secret-indexed lookup tables. **Basis: derived, source.**

## Applicability

This report governs cryptographic kernels, verified parsers, eBPF/sandboxed interpreters, and OS syscall/hypervisor boundaries targeting x86-64, AArch64, and 64-bit RISC-V (`Sv39`/`Sv48`). **Basis: normative, source.**

Within the corpus, it complements neighboring verification reports without overlap:
- [`murray-intransitive-unwinding-speculative-constant-time-and-fuel-time-credits`](../murray-intransitive-unwinding-speculative-constant-time-and-fuel-time-credits/REPORT.md) covers `seL4` intransitive unwinding and Jasmin's `sct_checker_forward.ml` `(n, s)` + `MSF` typing internals; here we contrast the semantic contract hierarchy (`CT` vs. `SNI` vs. `SCT` vs. `USLH`), LLVM X86/AArch64/Linux cross-ISA mitigations, and microarchitectural `PTW`/`TLB` side channels.
- [`compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences`](../compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences/REPORT.md) and [`verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening`](../verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening/REPORT.md) cover backend stack erasure and CFI/Retpoline; [`side-channel-freedom-foundations-and-leakage-contracts-1996-2026`](../side-channel-freedom-foundations-and-leakage-contracts-1996-2026/REPORT.md) surveys general leakage models; and [`mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`](../mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement/REPORT.md) analyzes functional TLB/PWC shootdown coherence. **Basis: documentation.**

## Findings

### 1. Hardware-Software Leakage Contracts `⟦p⟧^τ_σ`: `CT`, `SNI`, `SCT`, and Declassification

**Basis: normative, source, documentation, execution.**

Guarnieri et al. (*Hardware-Software Contracts for Secure Speculation*, IEEE S&P 2021, `doi:10.1109/SP40001.2021.00036`) parameterize microarchitectural leakage by a contract `⟦p⟧^τ_σ = ⟨f_arch(σ), L(σ)⟩` mapping initial state `σ` under architectural semantics `τ` and speculative hardware model to final state and trace `L(σ)`. Comparing `Spectector` (`839bec7d`, `doi:10.1109/SP40000.2020.00011`), `Pitchfork` (`8a3d3253`, `doi:10.1145/3385412.3385970`), `Jasmin` (`8c327997`, `doi:10.1109/SP40001.2021.00046`), `Spectre Declassified` (`10.1109/SP46215.2023.00011`), and *Exorcising Spectres with Secure Compilers* (`10.1145/3460120.3484534`) separates five distinct properties:

| Property | Relational Formal Definition (`σ₁ =_L σ₂` low-equivalent) | Observation Alphabet | Key Separation Witness |
| :--- | :--- | :--- | :--- |
| **Architectural `CT`** | `⟦p⟧^seq(σ₁).trace = ⟦p⟧^seq(σ₂).trace` | Sequential `pc`, load/store addrs, var-time ops | Fails `SNI`: `if (idx < pub_len) leak(pub[idx])` passes `CT` (`idx < pub_len`), leaks secret under `PHT` misprediction (`reval_spectre_ptw.py`: `oob_pub`) |
| **Speculative Non-Interference (`SNI`)** | `⟦p⟧^seq(σ₁).obs = ⟦p⟧^seq(σ₂).obs ⇒ ⟦p⟧^spec(σ₁).obs = ⟦p⟧^spec(σ₂).obs` | `spectector_noninter.pl:320–369` (`unif_obs(NTraceA, NTraceB)`) | Permits intentional non-CT output (`#declassify`) when sequential trace already distinguishes secrets; **fails** if transient path reaches `#declassify` on secret |
| **Speculative Constant-Time (`SCT`)** | `⟦p⟧^spec(σ₁).obs = ⟦p⟧^spec(σ₂).obs` | `pc`, memory addrs, branch targets across `PHT`/`STL` | Strictly stronger than `CT ∧ SNI` under `#declassify`: requires `declassify_lvl (_, s) = (Pub, s)` (`sct_checker_forward.ml:917`) so speculative secret taint blocks subsequent leaks |
| **Ultimate `SCT` (`USCT`)** | `∀ σ₁ =_L σ₂`, `⟦p⟧^arch-var(σ₁).obs = ⟦p⟧^arch-var(σ₂).obs` | `CT` + variable-time ALU (`div`, subnormal FP, `cmov` addr/val) | Separates `aSLH`/`vSLH` from `USLH`: register-resident secret entering `udiv` after a mispredicted branch leaks in `aSLH` unless `USLH` masks all variable-time operands |
| **Robust Secure Compilation (`RSNI`/`RSCT`)** | `∀ C, ⟦C[P]⟧_src ∈ Spec ⇒ ⟦C[↓P]⟧_tgt ∈ Spec` | Adversarial calling context `C` + compiler lowering `↓P` | Patrignani & Guarnieri (`10.1145/3460120.3484534`): local `SLH` fails `RSCT` across arbitrary contexts if caller enters with poisoned `SP`/flags or spills unmasked secrets to stack (`POPL 2025`) |

Primary-source inspection of `spectector` (`src/muasm_semantics.pl:170–359`, `src/spectector_noninter.pl:254–369`) and `pitchfork-angr` (`new-testcases/spectrev1.c:1–140`, `kocher_analysis.txt:1–33`) clarifies two frequent modeling errors:
- **Sequential Out-of-Bounds False Positives in Kocher Benchmarks:** `pitchfork`'s `kocher_analysis.txt` (`L4–13, 26–33`) documents that Kocher cases `04`, `09`, `14`, and `15` perform attacker-controlled out-of-bounds reads or pointer dereferences **even without speculation**, failing `CT` outright; valid `SNI`/`SCT` separation benchmarks require sequential bounds safety (`spectrev1.c:65–73, 115–127`).
- **Contract Sensitivity Across Microarchitectural Channels (`ct-seq` vs. `ct-pht` vs. `ct-stl` vs. `arch-pht`):** In `muasm_semantics.pl`, standard `SNI` records `load(N)`, `store(Ev)`, and `pc` (`L172, 184, 361`), whereas `weak_sni` (`L174, 185, 350`) additionally exposes loaded values (`value(V)`), corresponding to Guarnieri et al.'s `arch` vs. `ct` contracts. Furthermore, `Spectector` only forks on `beqz` (`PHT`, `L271–278`), omitting `STL` store-to-load bypass (`Spectre-v4`) which `Pitchfork` models via `specvex` bounded load-bypass windows and `Jasmin` abstracts via `Indirect` pointer taint and `corruption_speculative` (`sct_checker_forward.ml:592, 874, 893`).

### 2. Bounds Masking vs. `SLH` Variants vs. Fences Across x86-64, AArch64, and RISC-V

**Basis: source, documentation, execution.**

Examining `torvalds/linux` (`5f22fb20`: `include/linux/nospec.h:14–65`, `arch/x86/include/asm/barrier.h:36–49`, `arch/arm64/include/asm/barrier.h:43–45, 90–105`, `arch/riscv/include/asm/barrier.h:1–87`), `llvm/llvm-project` (`1cfbf0a8`: `X86SpeculativeLoadHardening.cpp`, `AArch64SpeculationHardening.cpp`), `jasmin-lang/jasmin` (`slh_ops.v:18–35`), `PLSysSec/blade` (`61ac7906`), and *Ultimate SLH* (`978-1-939133-37-3`) reveals sharply divergent guarantees and compiler gaps across mitigations and ISAs:

| Mechanism & Source Location | x86-64 Lowering | AArch64 Lowering | RV64GC Status | What It Protects vs. What Fails |
| :--- | :--- | :--- | :--- | :--- |
| **`array_index_nospec` (`nospec.h:27–65`)** | `cmp sz, idx; sbb mask, mask` (`x86/barrier.h:40`) | `cmp idx, sz; sbc mask, xzr, xzr; csdb` (`arm64/barrier.h:96–103`) | Generic shift mask `~(long)(i \| (sz - 1 - i)) >> 63` (`nospec.h:37`), **no `csdb`/fence** | Protects single-branch `idx < sz`; fails if `sz > 2^63` on generic shift (`reval_spectre_ptw.py`); **fails** under nested misprediction (`mask_nested`) or compiler constant-propagation without `OPTIMIZER_HIDE_VAR` (`L36`); leaves `PTW` safe only for the clamped index |
| **Serialization Fence (`barrier_nospec`)** | `lfence` (`x86/barrier.h:48`, `X86SLH:532`) | `dsb nsh; isb` or `sb` (`arm64/barrier.h:43–45`) | **`do { } while (0)` NO-OP (`nospec.h:15`)** | Halts transient window cleanly (`spbarr` in `muasm_semantics.pl:321`), closing Spectre-v1, `vSLH` PTW, and `USCT` transmitters; **absent** as a lightweight speculation barrier in base RV64GC (`fence.tso`/`fence iorw,iorw` orders memory, not speculation!) |
| **Address SLH (`aSLH`, `X86SLH:1530–1660`)** | Hardens dynamic `Base`/`Index` regs with `OR StateReg` (`Poison = -1`) | Masks address regs (`AND X16`, `X16 = 0` on mispred, `AArch64SLH:42–45, 73–78`) | **Unsupported in LLVM (`1cfbf0a8`)** | Prevents transient load from reading secret or touching secret L1D/`PTW` lines; **misses** non-memory `udiv`/branch transmitters fed by register secrets, plus `FI`/`RIP`/`RSP` loads skipped by `hardenLoadAddr` (`X86SLH:1542–1570`) |
| **Post-Load Value SLH (`vSLH`, `X86SLH:1919–1945`)** | Executes load first, then inserts `OR StateReg` on `DefReg` (`L1936–1937`) | Executes GPR load, then `AND` with `X16` + `CSDB` (`L73–82`) | **Unsupported in LLVM (`1cfbf0a8`)** | Stops *second* secret-dependent lookup `lut[*p]`; **LEAKS first-load address `*p` via L1D cache fills AND `PTW` cache lines (`AnC`)** before masking (`reval_spectre_ptw.py`), plus leaks into unhardened `LoadDepRegs` or `udiv` |
| **Ultimate SLH (`USLH`, `978-1-939133-37-3`)** | Masks **all** load/store addresses, branches, call/ret `SP`, and variable-time ALU operands (`udiv`, shifts, FP) | `CSEL` + `CSDB` (`X16`) over all sinks & operands | Must be synthesized manually in MIR/asm (`slt`/`neg`/`and` + cumulative `MSF`) | Closes `vSLH` first-load leakage, `aSLH` variable-time arithmetic leaks, and Spectre-v1.1 spill corruption; `Blade` (`10.1145/3434330`) synthesizes minimal `protect` cuts (`--blade-type=lfence\|slh`, `--blade-v1-1`) |

Four implementation pitfalls require explicit verification checks (`Basis: source, execution`):
1. **LLVM Post-Load `hardenPostLoad` Exposes First-Load Addresses (`X86SpeculativeLoadHardening.cpp:1919–1945`):** Because `hardenPostLoad` splits `OldDefReg` *after* the load instruction (`std::next(MI.getIterator())`, `L1937`), any secret-dependent pointer (e.g. a transiently forged or masked-omitted address) still dispatches to L1D and triggers a hardware radix page walk (`AnC`), leaking cache-line and PTE-line addresses even though `OldDefReg` is coerced to `-1` afterward. Cryptographic code assuming LLVM `--x86-slh` protects secret-indexed memory accesses must enforce **`aSLH` (hardened base+index)** rather than `vSLH`.
2. **AArch64 `CB(N)Z`/`TB(N)Z` Prohibition and `X16` Fallback (`AArch64SpeculationHardening.cpp:36–61`):** Tracking flags via `CSEL` + `CSDB` fails if instruction selection emits flagless `CBZ`/`CBNZ`/`TBZ`/`TBNZ`; AArch64 SLH therefore constrains codegen against flagless branches and falls back to `DSB SYS; ISB` whenever inline assembly touches `X16`.
3. **Why Generic `array_index_mask_nospec` Fails on `size > 2^63` and Nested Branches:** Linux's shift formula `~(long)(idx | (size - 1UL - idx)) >> 63` (`nospec.h:37`) treats bit 63 as a sign predicate: for `size = 2^63 + 1` and `idx = 0`, `size - 1 - idx = 2^63` sets bit 63 to `1`, making `~(...) >> 63` return `0` (falsely clamping a valid `0 < size` index, `reval_spectre_ptw.py`). More critically, local `array_index_nospec` cannot substitute for cumulative `MSF`: a valid outer bounds check `idx < len` followed by a mispredicted inner authorization check `if (is_admin)` lets the inner branch access an unmasked secret array (`mask_nested` in `reval_spectre_ptw.py`). Only cumulative `MSF` (`Exact` vs. `Trans`, `jasmin` `sct_checker_forward.ml:727–842`) tracks nested branch predicates across basic blocks.
4. **Absence of RISC-V Hardware Speculation Barriers and LLVM Pass:** Base RV64GC specifies neither an architectural `lfence` speculation barrier nor Arm's `CSDB` data-value speculation barrier (`linux/arch/riscv/include/asm/barrier.h` omits `barrier_nospec()`), and LLVM `1cfbf0a8` has no RISC-V SLH pass. Verified RISC-V cryptography and kernels must emit explicit branchless predicate masks (`slt`/`sltu`/`neg`/`and` or `Zicond` `czero`) propagated along CFG edges using `Blade`-style min-cuts verified by `(n, s) + MSF` typing.

### 3. Radix Page-Table-Walk (`PTW`) and `TLB` Cache Side Channels

**Basis: normative, source, execution, documentation.**

Standard `ct` leakage contracts model memory observations at 64-byte L1D cache-line granularity (`va >> 6`) or word addresses, ignoring the **implicit radix page-table-walk (`PTW`) and `TLB` structures** invoked on every memory load, store, or instruction fetch (`supervisor.adoc:1717–1770`; `sail-riscv` `model/sys/vmem.sail:172–256`). Three peer-reviewed attack classes prove that `PTW`/`TLB` microarchitecture leaks secret virtual addresses even when L1D lines are constant or caches are hardware-partitioned:

1. **MMU Page-Table Cache-Line Leakage (`AnC`, Gras et al., NDSS 2017, `doi:10.14722/ndss.2017.23271`):** For 64-bit `Sv39`/`Sv48` (`8`-byte PTEs, `4 KiB` page-table pages, `64`-byte cache lines holding `8` PTEs), Step 2 of VATP (`supervisor.adoc:1724`) reads physical address `a[lvl] + va.vpn[lvl] * 8`. Thus each non-superpage walk reads cache-line offset **`vpn[lvl][8:3] = (va >> (12 + 9 * lvl + 3)) & 0x3F`**:
   - **Level 0 (`4 KiB` PTEs):** Cache-line index `VPN[0][8:3]` changes every **`8 × 4 KiB = 32 KiB`**;
   - **Level 1 (`2 MiB` entries):** Cache-line index `VPN[1][8:3]` changes every **`8 × 2 MiB = 16 MiB`**;
   - **Level 2 (`1 GiB` entries):** Cache-line index `VPN[2][8:3]` changes every **`8 × 1 GiB = 8 GiB`**.
   An unprivileged attacker running `Evict+Time` on the shared Last-Level Cache (`LLC`) recovers the victim's secret-indexed Level-0 PTE cache line (`32 KiB` resolution) without sharing any data page with the victim. Worse, on RISC-V (`supervisor.adoc:1797–1809`), speculative PTWs run arbitrarily while `satp` is active and under `Svadu` (`L1625–1627`) can even write `A = 1` back to PTE memory during squashed speculative accesses, dirtying the PTE's L1D/LLC line!
2. **`TLB` Set-Residency Leakage (`TLBleed`, Gras et al., USENIX Security 2018, `ISBN 978-1-939133-04-5`):** Even when cache-partitioning defenses (e.g., Intel `CAT`) isolate LLC lines against `AnC`, shared Level-2/STLB sets remain indexed by virtual page number (`VPN[0]` bits on `4 KiB` pages). Thus two secret-indexed lookups separated by a single **`4 KiB` page** (`fp_p0` vs. `fp_p1` in `reval_spectre_ptw.py`) share Level-0 PTE cache line `0` (invisible to `AnC`), **yet collide on distinct `TLB` sets (`tlb_set 0` vs. `1`), leaking ECDSA/EdDSA bits across SMT threads**.
3. **Stateless Page-Walker Port Contention (`Binoculars`, Zhao et al., USENIX Security 2022, `ISBN 978-1-939133-31-1`):** Cross-hyperthread contention between hardware page-walker reads/stores and concurrent cache-line traffic produces up to ~20,000-cycle timing perturbations keyed to **`VA[11:6]` (64-byte cache-line offset within a `4 KiB` page)**—breaking constant-time isolation even inside a single 4 KiB page on shared SMT cores when cache-line sweep masking is omitted!

**Consequence for Cryptographic Scatter-Gather and Speculative `vSLH`:**
- **Scatter-Gather Over `> 4 KiB` Tables Breaks Under `AnC` and `TLBleed`:** Sweeping every 64-byte cache line inside a single `4 KiB` page (`size <= 4096`, `VPN[0]` fixed, sweeping all `64` lines `[0..63]` per lookup) keeps **both** L1D set sequence **and** Level-0 PTW cache line + `TLB` set invariant. However, a `64 KiB` (`16`-page) S-box or multiplier table where secret `s` chooses one `4 KiB` page and sweeps all `64` cache lines *within that page* keeps L1D `l1d_set` behavior misleadingly constant per offset, **yet leaks `s` via `TLBleed` at `4 KiB` granularity and `AnC` at `32 KiB` granularity** (`reval_spectre_ptw.py`: `fp_p0`, `fp_p1`, `fp_p8`)! Backing the `64 KiB` table with a **`2 MiB` superpage** (`level = 1` leaf PTE) eliminates Level-0 PTW reads and 4 KiB TLB-set variance (`sp_set` collapses to 1 element), leaving only `Binoculars` SMT cache-line offset `VA[11:6]` (mitigated by full `64`-line cache-line sweep or disabling SMT).
- **`vSLH` Does Not Mitigate `AnC`/`TLBleed` on First Loads:** Because `vSLH` masks *after* address translation and L1D access, transient out-of-bounds or secret-indexed first loads still trigger speculative PTWs (`supervisor.adoc:1797–1809`), polluting both LLC PTE lines (`AnC`) and STLB sets (`TLBleed`).

### 4. Mechanized `SCT + PTW` Obligations (`(n, s)` + `MSF` + Page-Footprint Confinement)

**Basis: derived, source.**

Composing Jasmin's 2-bit `(normal, speculative)` lattice (`sct_checker_forward.ml`) with `USLH` operand hardening and `PTW`/`TLB` residency invariance yields a compact 4-rule verification contract:

1. **Cumulative `MSF` + `(n, s)` Typing:** Maintain `MSF ∈ {ToInit, Exact, Trans(cond)}` across branches; forbid `(Pub, Sec)` or `(Sec, *)` in branch conditions, load/store addresses (`ensure_public_address`), and variable-time ALU sinks (`div`, variable shifts). `#declassify` maps `(n, s) ↦ (Pub, s)` so transient values must pass `#protect` (`Exact` MSF) before reaching any architectural or PTW sink.
2. **Address Hardening Over Post-Load Hardening (`aSLH` / `USLH`):** Any memory access reachable under misprediction must mask its effective address (`ptr_masked = mask_addr(ptr, msf)`) **prior** to memory dispatch so speculative PTWs cannot resolve secret-dependent `VPN`s.
3. **Single-Page or `2 MiB`-Superpage Table Confinement (`ptwFootprintConst`):** Any secret-indexed lookup or scatter-gather table `T` of byte range `[base, base + size)` must satisfy either `base >> 12 == (base + size - 1) >> 12` (`<= 4 KiB`, zero `VPN[0]` variance) or superpage alignment (`base >> 21 == (base + size - 1) >> 21` on a `level = 1` PTE with TLB entry pre-warmed and intra-page 64-byte line accesses swept uniformly).
4. **No Unmitigated `Svadu` Speculative Page-Table Dirtying on Secret-Dependent VAs:** Because `Svadu` permits speculative walks to set leaf `A = 1` (`supervisor.adoc:1625–1627`), secret-dependent speculative virtual addresses must be blocked at address-generation time (`aSLH` clamping to a pre-accessed `A = 1` dummy page), preventing secret-keyed PTE `A`-bit cache-line writes.

## Boundaries

- **`known not to apply` — Single-branch `array_index_nospec` under nested conditional misprediction, `vSLH` for secret-dependent first-load pointers, or `64 KiB` page-per-secret scatter-gather on `4 KiB` pages:** As verified in `reval_spectre_ptw.py`, local index clamping misses nested second-branch speculation (`mask_nested`), `vSLH` leaks first-load virtual addresses into L1D and Level-0 PTE cache lines before post-load register masking, and multi-page scatter-gather leaks `4 KiB` (`TLBleed`) and `32 KiB` (`AnC`) secret page indices. Generic `array_index_mask_nospec` also `known not to apply` to bounds `size > 2^63`. **Basis: source, execution.**
- **`unsupported` — Upstream LLVM `--x86-speculative-load-hardening`-equivalent passes on RISC-V (`llvm/llvm-project@1cfbf0a8`), and `barrier_nospec()` on RV64GC Linux (`5f22fb20`):** Upstream LLVM provides SLH backends for X86 and AArch64 only, and Linux RV64GC inherits an empty `barrier_nospec()` macro (`include/linux/nospec.h:15`). **Basis: source.**
- **`not examined` — Return-Stack-Buffer (`RSB` / `Spectre-v2` / `Retbleed`), Branch Target Injection (`IBPB`/`eIBRS`), and MDS/L1TF/Downfall transient microarchitectural buffers:** This synthesis isolates bounds-check bypass (`Spectre-v1`), speculative store corruption (`v1.1`), store-to-load bypass (`v4`), and radix `PTW`/`TLB` cache residency; indirect-branch BTB/RSB predictors and microcode staging buffers were `not examined`. **Basis: documentation.**
- **`unknown` — Exact proprietary STLB hash functions and hardware prefetcher trigger thresholds on unreleased x86-64, Arm, and RISC-V silicon:** While `TLBleed` and `Binoculars` reverse-engineered specific Intel generations and RISC-V `supervisor.adoc:1797–1809` authorizes arbitrary speculative PTWs, undisclosed vendor STLB indexing hashes remain `unknown` without per-core microarchitectural probing. **Basis: normative, documentation.**

## Evidence

| Subject / Paper | Pinned Identifier | Inspected Artifacts & Scope | Basis |
| :--- | :--- | :--- | :--- |
| `spectector/spectector` | `839bec7d96cd5b3387377cb42d26eb8ad55ecd4c`, `doi:10.1109/SP40000.2020.00011` | `README.md` `L1–115`; `src/muasm_semantics.pl` `L158–374` (`load`/`store` traces, `xc`, `bp_`, `spbarr`, `Se-Rollback-1`); `src/spectector_noninter.pl` `L254–369` (`noninter_cex_`, `filter_nonspec`, `unif_obs`); `tests/spectre_slh.muasm` `L1–7` | `source`, `documentation` |
| Guarnieri et al. (IEEE S&P 2021) | `doi:10.1109/SP40001.2021.00036`, `arXiv:2006.03841` | Hardware-software leakage contracts `⟦p⟧^τ_σ` (`ct-seq`, `ct-pht`, `ct-stl`, `arch-pht`) | `documentation` |
| `PLSysSec/pitchfork-angr` | `8a3d3253d465aa327f93075d6684d5ad03793283`, `doi:10.1145/3385412.3385970` | `README.md` `L1–87`; `pitchfork.py` `L1–115`; `new-testcases/spectrev1.c` `L1–140`; `kocher_analysis.txt` `L1–33` | `source`, `documentation` |
| `jasmin-lang/jasmin` | `8c3279973a89afd969e50301f71563bb40d55724`, `doi:10.1109/SP40001.2021.00046`, `10.1109/SP46215.2023.10179418` | `compiler/src/sct_checker_forward.ml` `L41–58, 592, 634–697, 727–842, 871–897, 917–1045` (`VlPairs`, `MSF`, `declassify_lvl`, `corruption_speculative`, `Protect`); `proofs/lang/slh_ops.v` `L18–35` | `source`, `documentation` |
| `PLSysSec/blade` | `61ac7906ddae019215ff4f33df7e774d88d6fdb1`, `doi:10.1145/3434330` | `README.md` `L1–81` (`T/S` def-use min-cuts, `--blade-type`, `--blade-v1-1`) | `source`, `documentation` |
| Patrignani & Guarnieri / Shivakumar et al. / Zhang et al. | `doi:10.1145/3460120.3484534`, `doi:10.1109/SP46215.2023.00011`, `isbn:978-1-939133-37-3`, `doi:10.5281/zenodo.7704637` | Robust speculative compilation (`RSNI`/`RSCT`), `#declassify` transient soundness (`SCT`), and `Ultimate SLH` over non-memory variable-time transmitters | `documentation` |
| `llvm/llvm-project` | `1cfbf0a826d28c27ae7fb802d8db6a37174a128b` | `llvm/lib/Target/X86/X86SpeculativeLoadHardening.cpp` `L380–445, 532–560, 1220–1310, 1525–1660, 1865–1980`; `AArch64SpeculationHardening.cpp` `L1–110`; verified no RISCV SLH pass in `llvm/lib/Target/RISCV/` | `source` |
| `torvalds/linux` | `5f22fb20497f4983094131f00a734362300d22d2` | `include/linux/nospec.h` `L14–65`; `arch/x86/include/asm/barrier.h` `L36–49`; `arch/arm64/include/asm/barrier.h` `L43–45, 90–105`; `arch/riscv/include/asm/barrier.h` `L1–87` | `source` |
| `riscv/riscv-isa-manual` & `riscv/sail-riscv` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `76f1ce3c184797178864b9869963e8b44465889e` | `supervisor.adoc` `L1625–1627, 1717–1770, 1797–1809`; `model/sys/vmem.sail` `L172–256` | `normative`, `source` |
| `AnC` / `TLBleed` / `Binoculars` | `doi:10.14722/ndss.2017.23271`, `isbn:978-1-939133-04-5`, `isbn:978-1-939133-31-1` | LLC PTW line attacks (`VPN[i][8:3]`), STLB set attacks (`VPN[0]`), and cross-SMT walker contention (`VA[11:6]`) | `documentation` |
| Python 3 Probe (`reval_spectre_ptw.py`) | Executed `2026-11-20`, Python 3.13 | Verified `array_index_mask_nospec` edge cases (`sz > 2^63`), `CT`/`SNI`/`SCT`/`USCT` separations, `vSLH` vs. `aSLH` vs. `USLH` leaks, and `Sv39` `AnC`/`TLBleed`/`Binoculars` bit-slices (`0.16 ms`, exit `0`) | `execution` |

## Revalidation

Run the standalone Python 3 probe below (`< 1 ms`, standard library only) to revalidate `array_index_mask_nospec` boundary behavior, `CT`/`SNI`/`SCT`/`USLH` separations, and `Sv39` `PTW`/`TLB`/`Binoculars` leakage footprints:

```python
#!/usr/bin/env python3
import time
t0 = time.perf_counter()

def linux_generic_mask_64(idx: int, sz: int) -> int:
    u_idx, u_sz = idx & ((1 << 64) - 1), sz & ((1 << 64) - 1)
    val = (u_idx | ((u_sz - 1 - u_idx) & ((1 << 64) - 1))) & ((1 << 64) - 1)
    return ((1 << 64) - 1) if (((~val) >> 63) & 1) else 0

for sz in (0, 1, 16, 256):
    for idx in (0, 1, max(0, sz - 1), sz, sz + 1, (1 << 63) - 1, (1 << 64) - 1):
        assert linux_generic_mask_64(idx, sz) == (((1 << 64) - 1) if idx < sz else 0)
assert linux_generic_mask_64(0, (1 << 63) + 1) == 0  # false clamp when sz > 2^63

def run_prog(variant: str, idx: int, cond2: bool, secret: int, reg_secret: int = 7,
             pub_arr=(1, 2, 3, 4), spec_mispredict: bool = False,
             pub_base: int = 0x1000, sec_base: int = 0x10000, lut_base: int = 0x20000) -> list:
    obs, msf = [], 0
    def branch_lt(a: int, b: int) -> bool:
        nonlocal msf
        real = a < b
        taken = (not real) if spec_mispredict else real
        obs.append(("br", taken))
        if taken != real:
            msf = (1 << 64) - 1
        return taken

    if variant == "oob_pub":
        if branch_lt(idx, len(pub_arr)):
            val = pub_arr[idx] if idx < len(pub_arr) else secret
            obs += [("load_line", (pub_base + idx * 8) >> 6), ("load_line", (lut_base + val * 64) >> 6)]
    elif variant == "mask_nested":
        if idx < len(pub_arr):
            safe_i = idx & linux_generic_mask_64(idx, len(pub_arr))
            taken2 = (not cond2) if spec_mispredict else cond2
            obs.append(("br2", taken2))
            if taken2:
                val = secret if (taken2 != cond2) else pub_arr[safe_i]
                obs.append(("load_line", (lut_base + val * 64) >> 6))
    elif variant in ("vslh", "aslh", "uslh", "lfence"):
        if branch_lt(idx, len(pub_arr)):
            if variant == "lfence" and msf != 0:
                return obs
            raw_ptr = (pub_base + idx * 8) if idx < len(pub_arr) else (sec_base + reg_secret * 4096 * 8)
            eff_ptr = (pub_base if msf else raw_ptr) if variant in ("aslh", "uslh") else raw_ptr
            obs += [("load_line", eff_ptr >> 6), ("ptw_l0_line", (eff_ptr >> 15) & 0x3F)]
            loaded = pub_arr[idx] if (eff_ptr < sec_base and idx < len(pub_arr)) else secret
            if variant in ("vslh", "aslh", "uslh") and msf:
                loaded = 0xFF
            obs.append(("load_line", (lut_base + (loaded & 0xFF) * 64) >> 6))
            div_op = (1 if msf else (pub_arr[idx] if idx < len(pub_arr) else 1)) if variant == "uslh" else (reg_secret if idx >= len(pub_arr) else pub_arr[idx])
            obs.append(("udiv_op", div_op))
    return obs

for s1, s2 in ((0x11, 0x22), (0x05, 0x7A)):
    assert run_prog("oob_pub", 0, True, s1, spec_mispredict=False) == run_prog("oob_pub", 0, True, s2, spec_mispredict=False)
    assert run_prog("oob_pub", 9, True, s1, spec_mispredict=True) != run_prog("oob_pub", 9, True, s2, spec_mispredict=True)

def declassify_sni_vs_sct(cond: bool, secret: int, mispredict: bool) -> list:
    taken = (not cond) if mispredict else cond
    return [("br", taken)] + ([("declassify", secret)] if taken else [])

assert declassify_sni_vs_sct(False, 1, False) == declassify_sni_vs_sct(False, 2, False)
assert declassify_sni_vs_sct(False, 1, True) != declassify_sni_vs_sct(False, 2, True)
assert run_prog("mask_nested", 0, False, 0x10, spec_mispredict=True) != run_prog("mask_nested", 0, False, 0x20, spec_mispredict=True)
assert run_prog("vslh", 9, True, 0x11, reg_secret=0, spec_mispredict=True) != run_prog("vslh", 9, True, 0x11, reg_secret=1, spec_mispredict=True)

t_a0 = run_prog("aslh", 9, True, 0x11, reg_secret=0, spec_mispredict=True)
t_a1 = run_prog("aslh", 9, True, 0x22, reg_secret=1, spec_mispredict=True)
assert [x for x in t_a0 if x[0] != "udiv_op"] == [x for x in t_a1 if x[0] != "udiv_op"] and t_a0 != t_a1
assert run_prog("uslh", 9, True, 0x11, reg_secret=0, spec_mispredict=True) == run_prog("uslh", 9, True, 0x22, reg_secret=1, spec_mispredict=True)
assert run_prog("lfence", 9, True, 0x11, reg_secret=0, spec_mispredict=True) == run_prog("lfence", 9, True, 0x22, reg_secret=1, spec_mispredict=True)

def sv39_ptw_footprint(va: int, is_2mb: bool = False, tlb_sets: int = 16) -> dict:
    return {
        "l0_pt_line": None if is_2mb else (((va >> 12) & 0x1FF) >> 3),
        "l1_pt_line": ((va >> 21) & 0x1FF) >> 3,
        "tlb_set": ((va >> 21) if is_2mb else (va >> 12)) & (tlb_sets - 1),
        "walker_64b_offset": (va >> 6) & 0x3F,
        "l1d_set": (va >> 6) & 0x3F,
    }

base_va = 0x0040_0000_0000
p0, p1, p8 = sv39_ptw_footprint(base_va), sv39_ptw_footprint(base_va + 4096), sv39_ptw_footprint(base_va + 8 * 4096)
assert p0["l1d_set"] == p1["l1d_set"] == p8["l1d_set"] == 0
assert p0["l0_pt_line"] == 0 and p8["l0_pt_line"] == 1
assert p0["tlb_set"] == 0 and p1["tlb_set"] == 1
assert sv39_ptw_footprint(base_va)["walker_64b_offset"] == 0 and sv39_ptw_footprint(base_va + 3 * 64)["walker_64b_offset"] == 3
assert len({(sv39_ptw_footprint(base_va + off, True)["l1_pt_line"], sv39_ptw_footprint(base_va + off, True)["tlb_set"]) for off in range(0, 65536, 4096)}) == 1

print(f"reval_spectre_ptw PASSED in {(time.perf_counter() - t0) * 1000.0:.2f} ms")
```

To check newer LLVM, Linux, or Jasmin commits for drift, inspect `llvm/lib/Target/RISCV/` for newly added speculation-hardening passes, `arch/riscv/include/asm/barrier.h` for `barrier_nospec()` / `array_index_mask_nospec`, and `jasmin/compiler/src/sct_checker_forward.ml` for `declassify_lvl` or `MSF` updates.
