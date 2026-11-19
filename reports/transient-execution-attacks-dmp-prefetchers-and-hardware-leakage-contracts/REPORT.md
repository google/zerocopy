# Transient Execution Channels, Data-Memory-Dependent Prefetchers, and Hardware-Software Leakage Contracts

## Summary

Classical ISA semantics model only committed architectural state, leaving microarchitectural state transitions invisible to sequential correctness proofs. Modern out-of-order processors expose secret-dependent microarchitectural side effects across three primary mechanism classes: (1) speculative control- and data-flow misprediction channels, (2) deferred fault and internal buffer forwarding channels, and (3) non-speculative Data Memory-Dependent Prefetchers (DMPs) that inspect and dereference pointer-shaped values stored at rest in cache lines.

Hardware-software leakage contracts decouple software constant-time verification from hardware microarchitecture verification by specifying an ISA-level observation function `O` that hardware must refine (`HW |= C`) and software must keep secret-independent (`SW |= C`). Sequential constant-time (`ct_seq`) and speculative constant-time (`ct_spec` / `arch`) contracts are strictly separated: a program that satisfies `ct_seq` can violate `ct_spec` under misprediction, and a straight-line program satisfying both `ct_seq` and `ct_spec` can still leak under a DMP contract (`ct_dmp`) unless pointer-shaped secret values are prevented or architectural data-independent timing modes suppress value-dependent prefetching.

## Applicability

This report synthesizes relationships across the subjects in `REPORT.json`:

- **Formal leakage contracts and CPU contract testing:** Guarnieri et al. (IEEE S&P 2021) define the contract framework; `microsoft/side-channel-fuzzer` (Revizor, `cc9fa2e53d92c496586689f44d6ea1740d95bd1d`) tests black-box CPUs against those contracts; `zilongwang123/LeaVe` (`9494f0d23453cc89e974e241c32d878cdea67070`) formally verifies Verilog RTL processors against ISA-level contracts.
- **Software-side speculative verification and mitigation:** `spectector/spectector` (`839bec7d96cd5b3387377cb42d26eb8ad55ecd4c`) checks speculative non-interference on x86-64 micro-assembly; `PLSysSec/lucet-blade` (`7a69d214807edb1e1a7c07ff3444ea7ac8f2aaf5`) with `PLSysSec/wasmtime-blade` (`8082aeaa5f593d8f343c9e6f1cca111802732724`) inserts minimal compiler fences/protections; `jasmin-lang/jasmin` (`5741d17e3134f5b3b110e5e53494704d6d54f7c7`) enforces Speculative Constant-Time (SCT) via type checking and misspeculation status flags (`msf`).
- **Hardware threat landscape:** Foundational transient-execution disclosures and DMP characterizations (Augury, GoFetch) establish which microarchitectural channels fall outside classical `ct_seq` or `ct_spec` contracts.

Findings apply to out-of-order superscalar processors (x86-64 and ARMv8/Apple Silicon) and verified constant-time cryptographic or sandboxed software compiled for them. Hardware contract verification findings in LeaVe apply specifically to synchronous RTL designs expressible in Yosys/SMT-BMC (e.g., RISC-V cores such as Ibex and DarkRISCV), not directly to proprietary out-of-order silicon without an RTL model.

## Findings

### 1. Architectural Taxonomy of Transient and Prefetcher Leakage Channels

Basis: normative + documentation + derived

Microarchitectural channels that violate sequential ISA isolation fall into three high-level parent classes:

| Parent Class | Core Hardware Mechanism | Representative Disclosures | Contract Impact |
| :--- | :--- | :--- | :--- |
| Speculative Control & Data-Flow Misprediction | Predictor structures (PHT, BTB, RSB, BHB, memory disambiguator) steer transient execution before architectural resolution commits or squashes the reorder buffer. | Spectre (v1, v2, v4, RSB), BHI, Retbleed, Inception, Pacman | Breaks `ct_seq`; requires speculative contract semantics (`ct_cond`, `ct_spec`, or `arch`) plus software/hardware barriers or SLH. |
| Deferred Fault & Internal Buffer Forwarding | Transient loads observe stale or cross-domain data from line fill buffers, store buffers, load ports, register files, or vector gather pipelines prior to exception/permission retirement. | Meltdown, MDS (RIDL, ZombieLoad, Fallout), LVI, Downfall (GDS), Zenbleed | Breaks ISA privilege and memory-isolation assumptions; requires hardware/microcode fixes, buffer clearing on domain switch, or load serialization (for LVI). |
| Data-Memory-Dependent Prefetchers (DMP) | Non-speculative hardware prefetchers inspect values inside fetched cache lines (e.g., array-of-pointers patterns) and dereference words matching valid virtual-address criteria. | Augury (Apple Silicon), GoFetch (Apple M-series / Intel DMP) | Breaks both `ct_seq` and `ct_spec` because secret values at rest trigger address-dependent cache fills without any secret-dependent instruction control flow or address computation. |

Key architectural boundary: unlike Spectre-class channels (where software can bound transient execution using branchless code, `LFENCE`, or Speculative Load Hardening), DMP leakage activates during architectural loads of public cache lines whose payload bytes happen to resemble valid pointers. Mitigating DMP channels therefore requires either hardware suppression modes (such as ARMv8.4+ Data Independent Timing `DIT` / Intel Data Operand Independent Timing Mode `DOITM` when configured to gate DMPs), cryptographic blinding of memory representations, or physical isolation of pointer-shaped secret words.

### 2. Formal Hardware-Software Leakage Contracts (`ct_seq`, `ct_spec`, `arch`)

Basis: normative + source

Guarnieri et al. (IEEE S&P 2021, `arXiv:2006.03841`) formalize a leakage contract as an ISA-level semantics `[[P]]_C(sigma)` emitting an observation trace. Two initial architectural states `sigma, sigma'` are low-equivalent (`sigma ~_L sigma'`) if they agree on public inputs.

- **Contract Satisfaction (Hardware obligation):** A hardware implementation `H` satisfies contract `C` (`H |= C`) iff for all programs `P` and architectural states `sigma, sigma'`, identical contract traces imply identical hardware microarchitectural observations:
  `[[P]]_C(sigma) = [[P]]_C(sigma')  ==>  [[P]]_H(sigma) = [[P]]_H(sigma')`.
- **Program Security (Software obligation):** A program `P` is secure under contract `C` iff `sigma ~_L sigma' ==> [[P]]_C(sigma) = [[P]]_C(sigma')`.
- **Composition Theorem:** If `H |= C` and `P` is secure under `C`, then `P` leaks no secrets on `H`.

Standard contract axes combine an **observation clause** (`ct`: program counter and memory addresses; `arch`: program counter, addresses, and all loaded architectural values; `ct-pc` / `ct-mem` subsets) with an **execution clause** (`seq`: sequential; `cond`: conditional branch misprediction; `bpas`: store-to-load bypass). Under `arch`, any value read sequentially is treated as observable, making `arch` weaker for software (harder to satisfy) and easier for hardware to satisfy than `ct`.

In `microsoft/side-channel-fuzzer` (`rvzr/model.py`), Revizor operationalizes `H |= C` via black-box model-based relational testing: the abstract `Model` class (`load_test_case`, `trace_test_case`) computes contract traces `CTrace` across input pairs `(i_1, i_2)` and flags a contract violation whenever `CTrace(i_1) == CTrace(i_2)` while measured CPU hardware traces diverge.

### 3. Software Verification and Compiler Enforcement (`Spectector`, `Blade`, `Jasmin SCT`)

Basis: source + documentation

Three verified software-side paradigms enforce speculative contract compliance at distinct abstraction layers:

| Tool / System | Verified Property | Mechanism & Verified Source Anchors | Key Boundary |
| :--- | :--- | :--- | :--- |
| `Spectector` (`spectector/spectector`) | Speculative Non-Interference (SNI): speculative traces reveal no more than non-speculative traces. | Symbolic execution over micro-assembly (`src/muasm_semantics.pl`: `mrun/2` dispatching `c/2` sequential vs `xc/3` speculative configurations; `src/spectector_noninter.pl`: `noninter_check/2`) discharging SMT queries in Z3. | Models bounded speculative windows for conditional branches; does not model DMP or microarchitectural buffer sampling. |
| `Blade` (`PLSysSec/lucet-blade` + `wasmtime-blade`) | Automatic elimination of transient dataflows from speculative sources to cache/control sinks. | Type-driven dataflow graph construction and minimum-cut placement of `protect` (SLH or fence) operations; integrated into Cranelift/Lucet (`lucetc/src/compiler.rs`: `blade_type`, `blade_v1_1` compiler options). | Minimizes barrier overhead relative to naive fence-after-every-load, assuming the hardware respects the modeled speculation primitives. |
| `Jasmin SCT` (`jasmin-lang/jasmin`) | Speculative Constant-Time (SCT) for high-speed cryptographic assembly. | Forward security type checker (`compiler/src/sct_checker_forward.ml`) tracking four sensitivity levels (`type ulevel = Secret | Transient | Public | Msf`) and explicit misspeculation status flag primitives (`type special_op = Init_msf | Update_msf | Mov_msf | Protect | Other`). | Preserves constant-time and selective SLH guarantees down to emitted x86-64/ARM assembly without blindly fencing all loads, provided hardware satisfies the modeled branch-speculation contract. |

### 4. RTL Hardware Contract Verification (`LeaVe`)

Basis: source + documentation

`zilongwang123/LeaVe` (`9494f0d23453cc89e974e241c32d878cdea67070`) checks `H |= C` directly on Verilog RTL designs by compiling the circuit through three custom Yosys passes (`addmodule.so`, `show_regs_mems.so`, `stuttering.so` configured in `config/RE.yaml`) into a self-composed two-copy product circuit (`prod.v`) and discharging relational invariants via Yosys-SMT-BMC (`yosys-smtbmc` with `inductiveyosysBMCBound` and `checkyosysBMCBound`).

In `config/RE.yaml`, the contract interface is separated cleanly into:
- `srcObservations`: ISA-level contract disclosures (e.g., operand disclosure on `MUL` when `op_ctr == 8'h02`),
- `predicateRetire` & `stateInvariant`: architectural retirement alignment and pipeline invariants,
- `trgObservations`: hardware attacker visibility (e.g., `ready` timing signal).

Stuttering alignment (`stuttering_left`, `stuttering_right`) enables bounded/inductive equivalence proofs even when variable-latency instructions take different cycle counts across executions.

### 5. Execution Verification: Strict Contract Separation (`ct_seq` vs `ct_spec` vs `ct_dmp`)

Basis: execution + derived

A self-contained Python semantics probe verified the strict separation between sequential, speculative, and DMP contracts:

- **Speculative separation (`Exp1`):** On a bounds-checked load with out-of-bounds `public_idx = 10 >= bound = 4` and secret-differing memory values (`0x41` vs `0x42`), `ct_seq` observations are identical (`True`), unprotected `ct_spec` observations diverge (`False`), and applying an SLH data-dependency mask restores `ct_spec` equivalence (`True`).
- **DMP separation (`Exp2`):** On a strictly straight-line load from a public address `0x0100` with no branches and no secret-dependent address arithmetic, differing stored words (`0x1040` inside valid pointer range `[0x1000, 0x2000)` vs `0x0040` outside) produce identical `ct_seq` (`True`) and `ct_spec` (`True`) traces, but diverge under `ct_dmp` (`False`: `(('pc', 0), ('load', 256), ('dmp_prefetch', 4160))` vs `(('pc', 0), ('load', 256))`).

This confirms structurally why software verified solely against `ct_seq` or `ct_spec` (including SLH-hardened or Jasmin-SCT code) remains exposed if the underlying hardware violates the contract by enabling an unmodeled DMP over secret-bearing memory.

## Boundaries

- **not examined:** Physical power, electromagnetic, and DVFS/frequency side channels (e.g., RAPL/Hertzbleed), which violate cycle-level timing abstractions orthogonal to ISA/cache contracts.
- **not examined:** Full-scale out-of-order commercial CPU RTL verification (LeaVe benchmarks evaluate open-source in-order RISC-V cores such as DarkRISCV, Sodor, and Ibex).
- **unknown:** Exact undocumented microarchitectural trigger predicates and cache-level filtering rules of future proprietary DMP implementations across undisclosed silicon revisions.
- **known not to apply:** Software SLH and SCT type systems (`Blade`, `Jasmin SCT`, `Spectector`) do not by themselves neutralize deferred-fault buffer forwarding (`Meltdown`/`MDS`) or unmodeled value-dependent hardware prefetchers (`DMP`), which violate the hardware side of `H |= C`.
- **unsupported:** Unmodified `ct_seq` / `ct_spec` contracts cannot express data-at-rest value-dependent prefetching without extending the contract observation clause (e.g., modeling `ct_dmp`) or enforcing hardware `DIT`/`DOITM` invariants.

## Evidence

- **Guarnieri et al. (IEEE S&P 2021):** `doi:10.48550/arXiv.2006.03841` — formalization of leakage contracts (`H |= C`, `ct_seq`, `arch`, speculative contracts).
- **Spectector (`spectector/spectector` @ `839bec7d96cd5b3387377cb42d26eb8ad55ecd4c`):**
  - `README.md` (lines 1–28): Ciao Prolog + Z3 symbolic execution for speculative non-interference.
  - `src/muasm_semantics.pl` (lines 28–38): `mrun/2`, `mrun_/2` dispatching sequential `c/2` and speculative `xc/3`.
  - `src/spectector_noninter.pl` (lines 41–45): `noninter_check/2` entry point.
- **Blade (`PLSysSec/lucet-blade` @ `7a69d214807edb1e1a7c07ff3444ea7ac8f2aaf5`, `PLSysSec/wasmtime-blade` @ `8082aeaa5f593d8f343c9e6f1cca111802732724`, `doi:10.1145/3434330`):**
  - `.gitmodules` (lines 1–4): links `wasmtime` submodule to `PLSysSec/wasmtime-blade`.
  - `lucetc/src/compiler.rs` (lines 65–84, 161–174): `blade_type` and `blade_v1_1` compiler configuration hooks.
- **Jasmin (`jasmin-lang/jasmin` @ `5741d17e3134f5b3b110e5e53494704d6d54f7c7`, `doi:10.1109/SP46215.2023.10179418`):**
  - `compiler/src/sct_checker_forward.ml` (lines 24–46): `type ulevel = Secret | Transient | Public | Msf` and `type special_op = Init_msf | Update_msf | Mov_msf | Protect | Other`.
- **LeaVe (`zilongwang123/LeaVe` @ `9494f0d23453cc89e974e241c32d878cdea67070`, `doi:10.48550/arXiv.2305.06979`):**
  - `README.md` (lines 1–50): Verilog RTL verification workflow and evaluated targets (`DarkRISCV-2`, `DarkRISCV-3`, `Sodor-2`, `ibex-small`, `ibex-mult-div`, `ibex-cache`).
  - `config/RE.yaml` (lines 1–85): `yosysAdditionalModules`, `srcObservations`, `predicateRetire`, `stateInvariant`, `trgObservations`, and `stuttering_signal`.
- **Revizor (`microsoft/side-channel-fuzzer` @ `cc9fa2e53d92c496586689f44d6ea1740d95bd1d`):**
  - `README.md` (lines 1–45) and `rvzr/model.py` (lines 20–55): abstract `Model` interface (`is_speculative`, `load_test_case`, `trace_test_case` returning `List[CTrace]`).
- **DMP and transient-execution literature:** Augury (`doi:10.1109/SP46214.2022.9833570`), GoFetch (USENIX Security 2024), Spectre (`doi:10.1109/SP.2019.00002`), Meltdown (`doi:10.48550/arXiv.1801.01207`), RIDL (`doi:10.1109/SP.2019.00087`), LVI (`doi:10.1109/SP40000.2020.00089`), Pacman (`doi:10.1145/3470496.3527429`), Retbleed & BHI (USENIX Security 2022), Downfall & Inception (USENIX Security 2023), Zenbleed (2023).
- **Execution probe (observed `2026-11-19`, Python 3):** Self-contained contract separation evaluator reproducing `Exp1_ct_seq_unprotected_eq: True`, `Exp1_ct_spec_unprotected_eq: False`, `Exp1_ct_spec_slh_eq: True`, `Exp2_ct_seq_eq: True`, `Exp2_ct_spec_eq: True`, `Exp2_ct_dmp_eq: False`.

## Revalidation

1. **Contract-tool drift check:** Fetch current `HEAD` commits of `jasmin-lang/jasmin` (`compiler/src/sct_checker_forward.ml`), `zilongwang123/LeaVe` (`config/RE.yaml`), and `microsoft/side-channel-fuzzer` (`rvzr/model.py`) and diff against the pinned SHAs in `REPORT.json` to check whether new leakage clauses (such as DMP or value-dependent prefetching) have been added to the contract lattice or type system.
2. **Silicon mitigation check:** On any target ARMv8.4+ or x86-64 microarchitecture, verify vendor architectural documentation for whether `DIT` / `DOITM` disables data-memory-dependent prefetching across all cache levels; if not guaranteed normatively, assume `ct_dmp` applies and re-audit cryptographic memory layouts.
3. **Contract separation probe:** Re-run a 25-line Python observational-equivalence check comparing `ct_seq`, `ct_spec` (with/without SLH masking), and `ct_dmp` over pointer-shaped vs non-pointer-shaped data words to confirm contract-extension invariants whenever revising a verifier's observation model.
