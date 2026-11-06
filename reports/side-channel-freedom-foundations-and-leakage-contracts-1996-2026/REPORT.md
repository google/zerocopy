# Foundations of Side-Channel Freedom, Hardware-Software Leakage Contracts, and Relational Compiler Preservation (1996–2026)

## Summary

Side-channel freedom (constant-time execution) is a **2-safety hyperproperty** (`CTNoninterference` in Clarkson & Schneider JCS 2010, `10.3233/JCS-2009-0393`): for any two initial machine states $s_1, s_2$ agreeing on public inputs ($s_1 \approx_{\text{pub}} s_2$), their execution observation traces must be identical ($\text{Obs}(s_1) = \text{Obs}(s_2)$). Because this specification relates two distinct execution runs rather than inspecting a single run in isolation, **no single-trace execution predicate or 1-run runtime monitor can decide side-channel freedom** (formally proved in `support/SideChannelFoundationsAndContracts.lean`, theorem `side_channel_freedom_not_1trace_property`).

Across the thirty-year research corpus (1996–2026), static verification and certified compilation of side-channel freedom have converged on four foundational verification paradigms, a five-level hardware-software leakage contract lattice, and explicit relational simulation conditions for compiler preservation, cost accounting, and transient stack depth:

1. **Four Static Verification Paradigms and Strict Expressiveness Separation**:
   - **Sequential Self-Composition ($P; P'$)** (Barthe, D'Argenio & Rezk CSFW 2004 / MSCS 2011 `10.1017/S0960129511000193`; Terauchi & Aiken SAS 2005 `10.1007/11547662_24`): Exact reduction of the 2-safety hyperproperty to a 1-safety property on sequentially duplicated state (`self_composition_iff_2safety_ct`), but with $4^k$ path-space explosion across $k$ branches and doubled loop invariant obligations.
   - **1-to-1 Lockstep Synchronized Product ($P \times_{\text{sync}} P$)** (Barthe, Crespo & Kunz CAV 2011 `10.1007/978-3-642-22110-1_17`; Almeida et al. `ct-verif` USENIX Security 2016 `imdea-software/verifying-constant-time@36e166781b0aa7398c12b335c7a4cd118b73568e`): Exact iff-characterization of constant-time noninterference (`lockstep_product_iff_ct_noninterference`) because constant-time control-flow equality forces both runs through identical basic blocks, collapsing $4^k$ self-composed branch paths to $2^k$ synchronized paths (`lockstep_product_quadratic_path_reduction`).
   - **1-Run Syntactic Security Type Systems ($\Gamma \vdash c : pc$)** (Volpano, Smith & Irvine JCS 1996 `10.3233/JCS-1996-42-304`; Cauligi et al. `FaCT` PLDI 2019 `10.1145/3314221.3314605`; Watt et al. `CT-Wasm` POPL 2019 `10.1145/3290390`; Barthe et al. `Jasmin` CCS 2017 `10.1145/3133956.3134078`): Fast $O(|P|)$ linear typechecking (`taint_type_system_sound_for_ct`), universally included inside relational product verification (`taint_typing_universal_inclusion_in_relational_product`), but **strictly weaker** ($\text{SyntacticTaintCT} \subsetneq \text{RelationalProductCT}$, theorem `relational_product_strictly_subsumes_taint_typing`) because non-relational taint lattices reject data-invariant algebraic cancellation (`rSec ^ rSec`) and branchless masked selection (`(rPub & rSec) | (rPub & ~rSec)`).
   - **1-Pass Cutpoint Relational Product Certificates** (Benton POPL 2004 `10.1145/964001.964003`): Checking 2-state relational invariants at CFG cutpoints achieves exact semantic completeness on lockstep programs while retaining $O(|P|)$ linear certificate verification (`relational_product_sound_for_ct`, `anneal_relational_ct_cert_checker_sound`).

2. **The 5-Level Hardware-Software Leakage Contract Lattice**:
   - Software-level constant-time proofs are sound only relative to an explicit hardware-software leakage contract (Guarnieri, Köpf, Morales, Reineke & Sánchez IEEE S&P 2021 `10.1109/SP40001.2021.00036`). Five strictly ordered leakage observation levels (`five_level_leakage_hierarchy_strict` in `support/SideChannelFoundationsAndContracts.lean`) separate functional value noninterference from real silicon guarantees:
     $$\text{Level 0 (Val-NI)} \;\prec\; \text{Level 1 (Arch-CT)} \;\prec\; \text{Level 2 (VarTime-CT)} \;\prec\; \text{Level 3 (Spec-CT)} \;\prec\; \text{Level 4 (DMP-CT)}$$
   - Each strict inequality is witnessed by a concrete microarchitectural vulnerability and proved in Lean 4 alongside its architectural mitigation: `KyberSlash` (`UDIV`/`REM` variable-latency instructions in ML-KEM, Bernstein et al. `ePrint 2024/1049`; mitigated by constant-time Barrett multiplication), `Spectre v1` (transient speculative loads across secret-independent architectural branches, Kocher et al. IEEE S&P 2019; mitigated by Speculative Load Hardening / `LFENCE` / `CSDB`), and `Augury` / `GoFetch` (data memory-dependent prefetchers dereferencing secret pointer-like words inside L1 cache lines on Apple M1/M2/M3 and Intel Raptor Lake, Vicarte et al. IEEE S&P 2022 `10.1109/SP46214.2022.9833570` and Chen et al. USENIX Security 2024; mitigated by pointer masking/blinding or hardware `DIT` on M3+).
   - Hardware constant-time mode registers (`ARMv8.4-DIT` `PSTATE.DIT`, `Intel DOITM` `IA32_UARCH_MISC_CTL[0]`, `RISC-V Zkt`) **do not** enforce constant-time execution on their own: they exempt integer division (`UDIV`/`SDIV`/`DIV`/`REM`), do not suppress speculative execution (`Spectre v1`), and on Apple M1/M2 do not disable the Data Memory-Dependent Prefetcher (`dit_mode_fails_on_exempt_div_or_m1m2_dmp`), whereas on Apple M3 setting `PSTATE.DIT = 1` disables DMP when combined with `VarTime-CT` and `Spec-CT` software proofs (`dit_mode_upgrades_m3_dmp_when_div_free`).

3. **Relational Compiler Preservation, Cost Accounting, and Transient Stack High-Water Marks**:
   - Standard value-refining compiler correctness preserves functional I/O semantics (`values_agree`) while freely introducing secret-dependent branches or memory accesses (`source_not_constant_time` in `support/security-observations-and-relational-compiler-preservation/SecurityWitness.lean`). Preserving constant-time across compilation requires **paired simulations with controlled stuttering** (Barthe, Grégoire, Laporte & Swamy CSF 2018) or **weak indexed relational ITree equivalence (`wkequiv_io` / `xrutt`)** with explicit public leakage events and source-safety side conditions (Barthe et al. `arXiv:2511.11292v1` and `jasmin-lang/jasmin@34f15840f10625bbc2cbf59b3d877e94c75bfbd9`).
   - Across eight mechanized Lean 4.34.1 operational-semantics modules (`support/PrefixAccounting.lean` through `support/CallSecurityComposition.lean`), we prove that:
     - **Cost and stack bounds require reverse target-prefix coverage (`Accounting.upper_bounds`)**: forward source-to-target simulation and output agreement cannot bound extra unmapped target internal steps (`ExtraTarget.safety_and_output_do_not_bound_target`) or mid-step transient stack push spikes (`deeper_stack_counterexample`, where peak stack reaches $n+2 > n+1$ before popping back to $n+1$).
     - **Macro-instruction expansion requires `PublicUniform` relational observation adapters**: lowering one source observation into multiple target micro-observations breaks literal trace equality (`expansion_is_not_literal_trace_equivalence`), but preserves `FiniteNoninterference` whenever the expansion function is uniform across public classes (`target_noninterference_of_adapter_image`, `target_prefix_noninterference_via_adapter`).
     - **Sequential call composition requires intermediate stage relational contracts (`StageMatch`)**: per-call marginal noninterference and return-cost summaries do not imply whole-pipeline noninterference when residual state (`scratch` registers or heap/cache state) survives across calls (`retained_not_noninterference`, `marginal_summary_does_not_supply_stage_contract`).

---

## Applicability

These findings apply directly to:
1. **Verified Low-Level Systems and Cryptographic Primitives**: Specifying and verifying constant-time machine-code and Rust/MIR primitives where memory addresses, branch targets, variable-time opcodes, and execution cost/stack bounds must be proved independent of secret inputs.
2. **Certificate-Checking Kernels and Admission Verifiers**: Embedding $O(|P|)$ 1-pass cutpoint relational product certificates (`RelationalCTCert` / `ProductMachineCert`) and explicit leakage-contract trust-policy gates (`LeakageTrustPolicy`, `DITHardwareTrustPolicy`) into proof-carrying code (PCC) admission pipelines without requiring an exponential multi-trace symbolic model checker inside the TCB.
3. **Verified Compiler Lowering Passes**: Designing simulation relations (`Accounting`, `PublicUniform` `ObsAdapter`, `StageMatch`) for compilers and macro-assemblers so that instruction selection, register spilling, and call lowering preserve both constant-time noninterference and worst-case stack/step ceilings.

---

## Findings

### 1. Why Side-Channel Freedom Is a 2-Safety Hyperproperty and the Four Static Verification Paradigms

In the Clarkson–Schneider hyperproperty hierarchy (`10.3233/JCS-2009-0393`), a standard **1-safety property** is a prefix-closed predicate $P \subseteq \mathcal{T}$ over individual execution traces $t \in \mathcal{T}$: a program satisfies $P$ iff $\forall s,\; \text{Obs}(s) \in P$. By contrast, side-channel freedom (`CTNoninterference`) is a **2-safety hyperproperty** over pairs of execution traces:
$$\text{CTNoninterference}(\text{Obs}, \approx_{\text{pub}}) \;\triangleq\; \forall s_1, s_2 \in \Sigma,\quad s_1 \approx_{\text{pub}} s_2 \implies \text{Obs}(s_1) = \text{Obs}(s_2)$$

In `support/SideChannelFoundationsAndContracts.lean` (Section 1, lines 50–103), theorem `side_channel_freedom_not_1trace_property` proves formally that **no single-trace predicate `P : Trace → Prop` can characterize `CTNoninterference`**: for any candidate `P`, either `P` rejects a constant-time function returning a constant outside `P`, or `P` accepts at least two distinct traces $t_a \neq t_b$ and therefore erroneously accepts a leaky secret-dependent program mapping secret `false` to $t_a$ and secret `true` to $t_b$. Consequently, dynamic 1-run runtime monitors and 1-trace Hoare logics cannot verify constant-time execution without a relational reduction.

#### Comparative Taxonomy of the Four Static Verification Paradigms

| Verification Paradigm | Canonical Primary Literature | Core Mathematical Reduction | Path / Verification Complexity ($k$ branches, program size $|P|$) | Completeness for Semantic CT | TCB / Certificate Checker Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. Sequential Self-Composition ($P; P'$)** | Barthe, D'Argenio & Rezk (CSFW 2004 / MSCS 2011 `10.1017/S0960129511000193`); Terauchi & Aiken (SAS 2005 `10.1007/11547662_24`) | Duplicate state space $\Sigma \times \Sigma$; run $P(\sigma_1)$ to completion producing $\tau_1$, then run $P'(\sigma_2)$ producing $\tau_2$; assert $\sigma_1 \approx_{\text{pub}} \sigma_2 \implies \tau_1 = \tau_2$. | **$O(4^k)$ paths** (cross-product of all paths in $P$ with all paths in $P'$); requires full functional loop invariants summarizing $\sigma_1 \mapsto \tau_1$. | **Complete** (`self_composition_iff_2safety_ct`), but intractable on cryptographic loops without alignment. | Standard 1-trace VCgen / Hoare verifier, but huge proof certificates. |
| **2. 1-to-1 Lockstep Synchronized Product ($P \times_{\text{sync}} P$)** | Barthe, Crespo & Kunz (CAV 2011 `10.1007/978-3-642-22110-1_17`); Zaks & Pnueli (FM 2008); Almeida et al. (`ct-verif`, USENIX Security 2016) | Step $(s_1, s_2) \to (s_1', s_2')$ in lockstep; assert step-local leakage equality $\ell(s_1) = \ell(s_2)$ at every instruction. | **$O(2^k)$ paths** (`lockstep_product_quadratic_path_reduction`: off-diagonal branch pairs immediately violate CT and are pruned). | **Complete** for all CT programs (`lockstep_product_iff_ct_noninterference`) because CT forces identical PC trajectories. | Product program builder + Boogie/SMT solver (`ct-verif` uses Smack + Boogie + Z3). |
| **3. 1-Run Syntactic Security Type Systems ($\Gamma \vdash c : pc$)** | Volpano, Smith & Irvine (JCS 1996 `10.3233/JCS-1996-42-304`); Cauligi et al. (`FaCT`, PLDI 2019 `10.1145/3314221.3314605`); Watt et al. (`CT-Wasm`, POPL 2019 `10.1145/3290390`) | Assign security lattice labels $\{\mathsf{Pub} \sqsubseteq \mathsf{Sec}\}$ to registers/locations; require branch conditions, memory indices, and variable-time operands to have label $\mathsf{Pub}$. | **$O(|P|)$ linear time** (single pass over syntax tree or SSA/Wasm bytecode). | **Sound but strictly incomplete** ($\text{SyntacticTaintCT} \subsetneq \text{RelationalProductCT}$): rejects `x ^ x` and masked selects. | Minimal syntax-directed typechecker (~200–500 LoC in `CT-Wasm` / `Jasmin`). |
| **4. 1-Pass Cutpoint Relational Product Certificates** | Benton (Relational Hoare Logic, POPL 2004 `10.1145/964001.964003`); Barthe et al. (`Jasmin` relational logic, CCS 2017 / POPL 2020) | Verify 2-state relational predicates $R_i(s_1, s_2)$ at CFG cutpoints checking $\ell(s_1) = \ell(s_2)$ and $R_{\text{next}}(\text{step}(s_1), \text{step}(s_2))$. | **$O(|P|)$ linear certificate checking**; relational solver generates cutpoint invariants offline. | **Complete** on lockstep CT programs; handles `x ^ x = 0`, masked arithmetic, and public declassification. | Small 1-pass relational proof checker (`anneal_relational_ct_cert_checker_sound`). |

#### Strict Separation Between Syntactic Taint Typing and Relational Product Verification

In `support/SideChannelFoundationsAndContracts.lean` (Sections 2–3, lines 105–361), we formalize a register machine with secret and public registers (`rPub`, `rSec`, `rTmp1`, `rTmp2`, `rOut`), bitwise ALU expressions (`var`, `const`, `xor`, `bitAnd`, `bitOr`, `bitNot`), and observable leakage events (`branchCond`, `memAddr`, `divOperands`). We prove:
1. **Soundness of Syntactic Taint Typing (`taint_type_system_sound_for_ct`)**: Every program accepted by the syntactic security type system `checkProgTaint` satisfies `ProgArchCT`.
2. **Universal Inclusion (`taint_typing_universal_inclusion_in_relational_product`)**: Every syntactically well-typed program (`checkProgTaint env p = some env'`) automatically satisfies the relational product specification (`ProgInRelationalProduct env p`).
3. **Strict Expressiveness Separation (`relational_product_strictly_subsumes_taint_typing`)**: There exist concrete constant-time programs that belong to `RelationalProductCT` (`ProgArchCT`) but are rejected by `checkProgTaint` (`checkProgTaint initTaintEnv p = none`). Two canonical witnesses are mechanized:
   - **Witness A (`progXorSelfCancel`)**: Zeroing a register via `rTmp1 := rSec ^ rSec` followed by a load at address `rPub + rTmp1` (`taint_rejects_xor_self_cancel` vs. `xor_self_cancel_is_arch_ct`). Because `Nat.xor v v = 0` for all $v$, the load address is identically `rPub`, independent of `rSec`, yet syntactic taint propagation joins `joinLabel .sec .sec = .sec` and rejects the memory indexing operation.
   - **Witness B (`progMaskedBranchlessEq`)**: Constant-time masked selection `rTmp1 := rPub & rSec; rTmp2 := rPub & ~rSec; rOut := rTmp1 | rTmp2` followed by branching on `rOut` (`taint_rejects_masked_branchless_eq` vs. `masked_branchless_eq_is_arch_ct`). By Boolean distributivity (`bitOr_bitAnd_compl`), `(a & b) | (a & ~b) = a` for all secret masks $b$, so `rOut` equals the public value `rPub`, yet both `rTmp1` and `rTmp2` carry `.sec` taint labels.

#### Sound vs. Unsound Public-Output Declassification

Cryptographic primitives frequently declassify a boolean verification tag (e.g., whether an AEAD authentication tag or ML-KEM re-encryption check succeeded) or branch on a public loop bound. In `support/SideChannelFoundationsAndContracts.lean` (Section 3.3, lines 363–409):
- **Conditioned Declassification Soundness (`conditioned_declassification_ct_soundness`)**: Declassifying an expression `declassExpr` to control a branch or memory index preserves `ProgArchCT` if and only if the relational precondition $\forall s_1, s_2,\; s_1 \approx_{\text{pub}} s_2 \implies \llbracket \text{declassExpr} \rrbracket(s_1) = \llbracket \text{declassExpr} \rrbracket(s_2)$ is discharged.
- **Unsoundness of Unguarded Declassification (`unguarded_declassification_launders_secret`)**: An unguarded `declassify(rSec)` cast without the relational agreement proof obligation immediately leaks `rSec` into the architectural branch trace `[ObsEvent.branchCond s.rSec]`.

---

### 2. The 5-Level Hardware-Software Leakage Contract Lattice (`Val-NI ≺ Arch-CT ≺ VarTime-CT ≺ Spec-CT ≺ DMP-CT`)

Following the formal framework of Hardware-Software Contracts for Security (Guarnieri et al., IEEE S&P 2021 `10.1109/SP40001.2021.00036`) extended to modern variable-latency instructions and data memory-dependent prefetchers (`Augury` 2022, `GoFetch` 2024, `KyberSlash` 2024), `support/SideChannelFoundationsAndContracts.lean` (Section 4, lines 411–691) formalizes five cumulative observation functions `obsAtLevel` over an extended microarchitectural instruction set `UArchStmt` (`assign`, `load`, `branchIfZero`, `divRem`, `speculativeWindow`, `lfence`, `cacheWordStore`):

| Contract Level | Formal Predicate (`SideChannelFoundationsAndContracts.lean`) | Leakage Observations Included in $\text{Obs}_{\text{level}}(s)$ | Vulnerable Microarchitectural Mechanism Excluded by Lower Levels | Concrete Counterexample / Exploit Separating Level $k-1$ from Level $k$ | Verified Software / Hardware Mitigation Restoring Level 4 (`DMP-CT`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Level 0: `Level0_ValNI`** | `SatisfiesContract p .Level0_ValNI` | Final public output register `[uValOut s'.rOut]` only. | All timing, control-flow, cache-line, and microarchitectural side channels. | `progSecretBranchSameOut` (`val_ni_not_arch_ct`): branches on `rSec` (`if rSec == 0 then rOut := rPub else rOut := rPub`), producing identical final `rOut` but distinct branch traces. | Replace secret control flow with branchless arithmetic (`Spec-CT` / `DMP-CT`). |
| **Level 1: `Level1_ArchCT`** | `SatisfiesContract p .Level1_ArchCT` | Level 0 + retired architectural PC/branch outcomes (`uBranch`) and architectural load/store addresses (`uMemAddr`). | Variable-latency arithmetic instructions (`UDIV`/`SDIV`/`REM`, variable-time FP/SIMD). | **`KyberSlash` (`arch_ct_not_vartime_ct_kyberslash`)**: `progKyberSlashDiv` executes `rOut := rSec / 3329` with zero branches and zero secret addresses, but hardware divider latency leaks `rSec` (`uDivOps`). | **`progKyberSlashBarrettFixed` (`kyberslash_barrett_replacement_restores_dmp_ct`)**: replace `UDIV` by constant-time Barrett multiplication `(rSec * 5039) >> 24`. |
| **Level 2: `Level2_VarTimeCT`** | `SatisfiesContract p .Level2_VarTimeCT` | Level 1 + operands of variable-latency instructions (`uDivOps`). | Transient speculative execution past mispredicted branches (`Spectre-PHT` / `Spectre v1`, `Spectre-BTB`, `Spectre-RSB`, `STL`). | **`Spectre v1` (`vartime_ct_not_spec_ct_spectre`)**: `progSpectreV1Gadget` guards an array access with a public bounds check `rPub != 0`, but under branch misprediction transiently executes `load(rSec)` (`uSpecAddr`). | **`progSpectreSLHFixed` (`spectre_slh_fence_restores_dmp_ct`)**: insert `lfence` / `CSDB` or architectural Speculative Load Hardening (SLH) mask before the load. |
| **Level 3: `Level3_SpecCT`** | `SatisfiesContract p .Level3_SpecCT` | Level 2 + transient speculative load/store addresses (`uSpecAddr`) inside unbounded/windowed speculation unless blocked by `lfence`. | Data Memory-Dependent Prefetchers (`DMP` on Apple M1/M2/M3 `Augury`/`GoFetch` and Intel Raptor Lake) and dynamic frequency/power scaling (`Hertzbleed` `CVE-2022-23823`). | **`GoFetch` / `Augury` (`spec_ct_not_dmp_ct_gofetch`)**: `progGoFetchDmpGadget` stores `0x10000000 + rSec` into a constant cache slot `0` with no branches, no divisions, and no speculative loads; DMP scans the stored cache word and prefetches `0x10000000 + rSec` (`uDmpWord`). | **`progGoFetchBlindedFixed` (`dmp_pointer_masking_blinding_soundness`)**: split or mask secret words (`rSec & 0xFFFF`) below the pointer-prefix threshold `0x10000000` (or enable `PSTATE.DIT` on Apple M3). |
| **Level 4: `Level4_DmpCT`** | `SatisfiesContract p .Level4_DmpCT` | Level 3 + pointer-like values ($\ge \texttt{0x10000000}$) stored in L1 data cache lines (`uDmpWord`). | Residual physical power/EM/DVFS channels (`Hertzbleed`) outside digital cache/prefetch state. | Master strict hierarchy theorem: **`five_level_leakage_hierarchy_strict`** proves all four strict separations simultaneously in a single conjunction. | Full `Level4_DmpCT` software verification + hardware `DIT` / `DOITM` / `Zkt` generation gate. |

---

### 3. Hardware Constant-Time Execution Mode Registers (`ARMv8.4-DIT`, `Intel DOITM`, `RISC-V Zkt`)

Modern ISAs expose architectural constant-time execution mode bits or extensions intended to bind microarchitectural timing to operand-independent latency:
- **ARMv8.4-A `DIT` (Data Independent Timing, `PSTATE.DIT` bit)**: Architectural specification guarantees that for a designated subset of data-processing and cryptographic instructions, instruction timing does not depend on data values. Crucially, the ARM Architecture Reference Manual **explicitly exempts integer division (`UDIV`/`SDIV`)** from `PSTATE.DIT` guarantees, and on Apple M1 (`Icestorm`/`Firestorm`) and M2 (`Blizzard`/`Avalanche`) microarchitectures, `PSTATE.DIT` **does not disable the Data Memory-Dependent Prefetcher (DMP)** (Chen et al., `GoFetch`, USENIX Security 2024). On Apple M3 and later cores, setting `PSTATE.DIT = 1` suppresses DMP dereferencing.
- **Intel `DOITM` (Data Operand Independent Timing Mode, `IA32_UARCH_MISC_CTL` MSR bit 0)**: Guarantees operand-independent latency for enumerated general-purpose and AVX/AES-NI instructions on Ice Lake and newer cores, but **exempts `DIV`/`IDIV`** and does **not** disable speculative execution (`Spectre v1`) or Intel Raptor Lake DMP unless specific microcode/prefetcher MSR controls are also applied.
- **RISC-V `Zkt` (Data-Independent Execution Latency Profile)**: Certifies operand-independent latency for scalar cryptographic and basic ALU/multiply instructions (`add`, `sub`, `xor`, `sll`, `mul`, `aes*`, `sha*`), while **explicitly excluding `div`/`divu`/`rem`/`remu`** and making no guarantee about speculative execution or DMP.

In `support/SideChannelFoundationsAndContracts.lean` (Section 5, lines 693–795), we formalize `MicroarchGen` (`appleM1M2`, `appleM3Plus`, `intelIceLakeRaptorLake`, `riscvZktCore`) and `SatisfiesDITModeContract` and prove three foundational boundary theorems:
1. **`dit_mode_fails_on_exempt_div_or_m1m2_dmp`**: Setting `ditEnabled = true` (`PSTATE.DIT = 1` / `DOITM = 1` / `Zkt`) **fails** to provide constant-time execution for `progKyberSlashDiv` on *every* hardware generation (`∀ gen, ¬ SatisfiesDITModeContract progKyberSlashDiv gen true`) because `UDIV`/`DIV` is architecturally exempt, and **fails** on Apple M1/M2 for `progGoFetchDmpGadget` (`¬ SatisfiesDITModeContract progGoFetchDmpGadget .appleM1M2 true`) because M1/M2 DMP ignores `PSTATE.DIT`.
2. **`dit_mode_upgrades_m3_dmp_when_div_free`**: On `MicroarchGen.appleM3Plus` (and `riscvZktCore` without DMP), enabling `ditEnabled = true` soundly upgrades any software program verified at `Level3_SpecCT` (free of secret branches, secret addresses, variable-time `divRem`, and speculative leaks) to full `SatisfiesDITModeContract p .appleM3Plus true`, without requiring software pointer-blinding for DMP.
3. **`anneal_dit_hardware_generation_trust_policy_soundness`**: Any admission gate (`DITHardwareTrustPolicy`) that checks `ditBitSetAtEntry = true`, `verifiedSpecCT p`, and either `targetGen = .appleM3Plus` or software `Level4_DmpCT` pointer-blinding is provably sound across all hardware generations.

---

### 4. Quantitative Cache Leakage (`CacheAudit`) and Product-Machine Embedding

For legacy table-lookup implementations (e.g., AES T-tables or precomputed RSA window tables) where strict observational determinism (`CTNoninterference`) fails, Doychev, Feld, Köpf, Mauborgne & Reineke (`CacheAudit`, USENIX Security 2013 / ACM TISSEC 2015 `10.1145/2756550`) bound the Shannon and min-entropy leakage of cache configurations via abstract interpretation over cache states:
$$I_{\infty}(S; \text{Obs}_{\text{cache}}) = \log_2 |\text{ReachableCacheObs}| \le \log_2 B \text{ bits}$$
When an entire lookup table fits within a single preloaded cache line ($|\text{ReachableCacheObs}| = 1$, i.e., $\forall s_1, s_2,\; s_1 \approx_{\text{pub}} s_2 \implies \lfloor \text{addr}(s_1) / L \rfloor = \lfloor \text{addr}(s_2) / L \rfloor$), quantitative leakage collapses to $\log_2(1) = 0$ bits (`cache_line_preload_zero_leakage_within_line` in `support/SideChannelFoundationsAndContracts.lean`, lines 803–825).

#### Embedding 2-Safety into Single-Trace Proof Engines (`ProductMachineCert`)

A verification kernel whose core proof engine verifies 1-trace state invariants (`Inv : State → Prop`) can verify 2-safety constant-time execution **without modifying its 1-trace proof kernel** by instantiating `State` with the synchronized product machine `ProductState = UArchState × UArchState` (lines 827–935 of `support/SideChannelFoundationsAndContracts.lean`):
- **Theorem `anneal_product_machine_wellformed_iff_all_prefix_ct`**: A `ProductMachineCert` over `UArchState × UArchState` is well-formed (`ProductCertWellFormed`) if and only if every execution prefix $n \in \mathbb{N}$ of the program satisfies `SatisfiesContractPrefix p cert.level n`.
- **Theorem `anneal_leakage_contract_trust_policy_gate_soundness`**: A trust-policy gate `LeakageTrustPolicy` that requires a valid `ProductMachineCert` at contract level `cert.level ≥ policy.requiredLevel` rejects every program with a violation at or below `policy.requiredLevel` (`KyberSlash` at `Level2_VarTimeCT`, `Spectre v1` at `Level3_SpecCT`, `GoFetch` at `Level4_DmpCT`) and guarantees `SatisfiesContract p policy.requiredLevel`.

#### Empirical Verification Benchmark Across 7 Cryptographic and Exploit Workloads

The companion executable benchmark (`support/side_channel_cert_probe.py`, output archived in `support/side_channel_cert_probe_results.json`) evaluates 1-run syntactic taint typing, 1-pass relational product certificates, self-composition path counts ($4^k$), lockstep product path counts ($2^k$), and leakage contract admission across `Level0_ValNI`..`Level4_DmpCT`:

| Workload ID | Description | Instr Count | Branches ($k$) | Self-Comp Paths ($4^k$) | Lockstep Paths ($2^k$) | Syntactic Taint (`FaCT`/`CT-Wasm`) | Relational Product Cert (`ct-verif`/RHL) | Highest Contract Level Satisfied (Unmitigated) | Highest Contract Level After Mitigation (`SLH` / Barrett / Blinding) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `montgomery_ladder_step` | Curve25519 constant-time CSWAP + field step | 6 | 1 (public loop exit) | 4 | 2 | **PASS** (6 steps) | **PASS** (6 steps) | `Level4_DmpCT` | `Level4_DmpCT` |
| `chacha20_quarter_round` | ARX quarter-round with public counter branch | 6 | 1 (public loop exit) | 4 | 2 | **PASS** (6 steps) | **PASS** (6 steps) | `Level4_DmpCT` | `Level4_DmpCT` |
| `mlkem_barrett_reduce` | ML-KEM constant-time Barrett reduction (`* 5039 >> 24`) | 5 | 0 | 1 | 1 | **PASS** (5 steps) | **PASS** (5 steps) | `Level4_DmpCT` | `Level4_DmpCT` |
| `masked_table_select` | Branchless masked table lookup `(rPub & rSec) \| (rPub & ~rSec)` | 6 | 1 (on masked pub) | 4 | 2 | **FALSE REJECT** (`rOut` tainted `.sec`) | **PASS** (6 steps; algebraic mask identity) | `Level4_DmpCT` | `Level4_DmpCT` |
| `xor_scratchpad_zeroize` | Secret register scrub `rTmp1 := rSec ^ rSec` then load | 4 | 0 | 1 | 1 | **FALSE REJECT** (`rTmp1` tainted `.sec`) | **PASS** (4 steps; `v ^ v = 0` identity) | `Level4_DmpCT` | `Level4_DmpCT` |
| `kyberslash_leaky_div` | ML-KEM message decoding using hardware `UDIV 3329` | 3 | 0 | 1 | 1 | **UNSOUND** if `UDIV` untyped; **REJECT** at `Level2` | **REJECT** at `Level2_VarTimeCT` (`uDivOps` leak) | `Level1_ArchCT` (fails `Level2_VarTimeCT`) | `Level4_DmpCT` (`mlkem_barrett_reduce`) |
| `spectre_v1_leaky_load` | Public bounds check `if rPub != 0` followed by `load(rSec)` | 4 | 1 (public guard) | 4 | 2 | **UNSOUND** at `Level1` (`rSec` load inside dead branch or speculative window) | **REJECT** at `Level3_SpecCT` (`uSpecAddr` leak) | `Level2_VarTimeCT` (fails `Level3_SpecCT`) | `Level4_DmpCT` (with `lfence` / SLH mask) |

---

### 5. Relational Compiler Preservation of Constant-Time and Cryptographic Security (`Jasmin` & Simulation Frameworks)

Standard verified compilers (such as CompCert's forward/backward value-refining simulations) guarantee that target assembly refines source I/O behavior, **not** that constant-time leakage traces are preserved. In `support/security-observations-and-relational-compiler-preservation/SecurityWitness.lean` (checked with zero axioms on Lean `4.31.0` commit `68218e876d2a38b1985b8590fff244a83c321783`), we construct a minimal counterexample demonstrating why value agreement (`values_agree`) fails to transfer constant-time security:
- `sourceRun (s : Secret) : Run`: branches on `s`, emitting trace `[Obs.branch true]` (cost `1`) for `s = true` and `[Obs.branch false]` (cost `2`) for `s = false`, while returning `value := 7` in both cases.
- `modelRun (_s : Secret) : Run`: emits `[Obs.step]` (cost `1`) and returns `value := 7` for all `s`.
- **Theorems (`SecurityWitness.lean`)**: `values_agree` holds (`∀ s, (sourceRun s).value = (modelRun s).value`), and `model_constant_time` holds (`∀ s₁ s₂, (modelRun s₁).trace = (modelRun s₂).trace ∧ (modelRun s₁).cost = (modelRun s₂).cost`), yet **`source_not_constant_time`** proves `(sourceRun true).trace ≠ (sourceRun false).trace ∧ (sourceRun true).cost ≠ (sourceRun false).cost`.

#### Conditions for Compiler Preservation of Constant-Time (Barthe et al. CSF 2018)

Barthe, Grégoire, Laporte & Swamy (*Secure Compilation of Side-Channel Countermeasures: The Case of Cryptographic "Constant-Time"*, CSF 2018, Theorems 1, 4, 6 and Definitions 7–10) establish the exact simulation conditions required for a compiler pass to preserve constant-time noninterference:
1. **CT Preservation via Paired Simulation (CSF 2018 Theorem 1)**: When source and target semantics step in lockstep on leakage events, CT is preserved if a simulation relation couples source pairs $(s_1, s_2)$ with target pairs $(t_1, t_2)$ such that public-equivalent source states map to coupled target states and every step preserves leakage equality.
2. **Controlled Stuttering / Internal Steps (CSF 2018 Theorem 4 & Definitions 7–8)**: When a pass inserts or eliminates internal (silent) steps (e.g., register moves, instruction selection, or dead-code elimination), an ordinary simulation allows secret-dependent stuttering counts that leak timing or trace length. Preservation requires **paired stuttering bounds** where the number and leakage of target steps taken between synchronization points depend only on public state, not on secret values.
3. **Memory Injection / Stack Spilling Preservation (CSF 2018 Theorem 6 & Definitions 9–10)**: When lowering source variables into stack frames or injected memory blocks, target memory addresses depend on stack frame layout and pointer offsets. Preservation requires the memory injection / frame layout relation to be **public-invariant** across the two relational executions so that spilled loads and stores emit identical target address traces.

#### Cryptographic Security Preservation in Jasmin (`arXiv:2511.11292v1` and `jasmin-lang/jasmin@34f15840`)

Barthe, Grégoire, Kunz, Laporte & Oliveira (*Cryptographic Security Preservation in Jasmin*, 2025, `arXiv:2511.11292v1`, §§5.2, 6.3, Theorem 2) and the upstream Coq mechanization in `jasmin-lang/jasmin` at commit `34f15840f10625bbc2cbf59b3d877e94c75bfbd9` lift compiler preservation from standalone deterministic programs to interactive cryptographic games (such as IND-CCA KEM encapsulation/decapsulation) with random sampling (`randombytes`) and explicit leakage accumulators:

| Jasmin Artifact / Theorem (`34f15840f10625bbc2cbf59b3d877e94c75bfbd9`) | File & Line Range | Exact Mathematical Role & Side Conditions |
| :--- | :--- | :--- |
| **`it_compile_prog_to_asmP`** | `proofs/compiler/it_compiler_proof.v:1688–1730` | Whole-compiler interaction-tree (ITree) relational theorem connecting source Jasmin (`p`) to target assembly (`xp`) across `compile_prog_to_asm` (`compiler.v:691–742`). |
| **`wkequiv_io`** | `proofs/lang/relational_logic.v:222–226` | Weak indexed relational equivalence over ITree executions parameterized by input/output relations (`R_I`, `R_O`) and auxiliary relational assertions. |
| **`xrutt` (with ` ErrCutoff := is_error ` on left, `NoErrCutoff` on right)** | `proofs/itrees/xrutt.v:138–147` & `proofs/lang/it_sems_core_defs.v:71–74` | Asymmetric error-cutoff relational bisimulation: if the **source** execution hits `is_error` (`ErrSem`, `ErrType`, `ErrAddrInvalid`, `ErrStack`), the relation holds vacuously (`it_sems_core_defs.v:140–145`). To transfer noninterference or cryptographic game equivalence to target assembly, **source safety (absence of `is_error` on valid inputs) must be discharged separately**. |
| **Game Preservation Theorem (`arXiv:2511.11292v1` Theorem 2)** | `arXiv:2511.11292v1` §§5.2, 6.3 | Preserves adversarial advantage in cryptographic games across 25 of Jasmin's 30 compiler passes (`§6.1`), explicitly conditioned on four caller/source obligations: **(1) source safety on valid inputs**, **(2) initialized result variables**, **(3) fresh stack memory above the frame**, and **(4) disjoint writable memory pointers**. |

---

### 6. Operational Cost Accounting, Transient Stack High-Water Marks, and Relational Observation Adapters

Even when a compiler preserves final values and architectural leakage events, two operational hazards can invalidate resource bounds and noninterference during lowering:
1. **Unaccounted target steps and mid-step transient stack spikes**: Forward simulation (`Simulation`) allows the target to take extra internal transitions (`extra : Nat → Config`) or push temporary values onto the stack and pop them before reaching the next matched source state.
2. **Macro-instruction trace expansion and cross-call residual state**: Lowering one source instruction into a multi-instruction target sequence alters trace structure, and composing two constant-time calls sequentially can leak secrets if residual state (`scratch` registers or cache lines) is retained across the call boundary.

To establish exact necessary and sufficient conditions for these properties, eight self-contained Lean 4 (`v4.34.1`) modules in `support/` (`PrefixAccounting.lean`, `CostStack.lean`, `Observations.lean`, `ObservationAdapters.lean`, `OperationalObservations.lean`, `OperationalAdapter.lean`, `CallSecuritySpecimens.lean`, `CallSecurityComposition.lean`; verification output in `support/lean-check-results.json`, aligned with MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) mechanize 113 theorem/witness declarations (`48` completely axiom-free `#print axioms` checks, with `Classical.choice`/`propext`/`Quot.sound` used only where classical existential witnesses are extracted).

#### Summary of the 8 Lean 4 Operational Semantics Modules (`support/*.lean`)

| Support Module | Core Definitions & Structures | Key Positive Soundness Theorems | Key Negative Counterexamples / Boundary Refutations |
| :--- | :--- | :--- | :--- |
| **`support/PrefixAccounting.lean`** | `ExecModel`, `ForwardMatch`, `Simulation`, `Accounting` (reverse target-prefix mapping `sourceIndex` with affine step/stack bounds `stepSlope * s + stepOffset`). | **`Accounting.upper_bounds`**: reverse target-prefix coverage transfers any source step/stack ceiling `sourceSteps ≤ B_s`, `sourceStack ≤ B_k` to a sound upper bound on **all reachable target prefixes** (`targetSteps ≤ a * B_s + b`, `targetStack ≤ c * B_k + d`). | **`ExtraTarget.safety_and_output_do_not_bound_target`** (`no_target_cost_bound`): a target with an unmapped stutter branch (`extra m`) satisfies `ForwardMatch`, `Simulation`, and `SameOutput`, yet reaches arbitrarily large target step count and stack depth $m+1$ for source cost $1$. |
| **`support/CostStack.lean`** | Concrete recursive call/return machine `Config` (`call`, `ret`, `extraPush`, `extraPop`) with cumulative `work` and high-water mark `peak := max s.peak (depth c')`. | **`source_completion`** (`work = 2n + 2`, `peak = n + 1`), **`source_peak_witness`** (stack depth reaches $n+1$ after $n$ calls), **`source_prefix_bounds`** (`work ≤ 2n + 2 ∧ peak ≤ n + 1`), and 2-phase (`armed : Bool`) **`target_prefix_bounds`** (`total ≤ 4n + 4 ∧ peak ≤ n + 1`). | **`charged_extra_step_counterexample`** (`work = 2n + 3 > 2n + 2` via one extra charged step) and **`deeper_stack_counterexample`** (`extraPush` followed by `extraPop` restores final stack depth and return value $n$, but raises the high-water mark to `peak = n + 2 > n + 1`). |
| **`support/Observations.lean`** | `ObsSystem`, `TraceEquiv`, `FiniteNoninterference` (possibilistic observation-set equality across public-equivalent states), `ObsRefines` ($\subseteq$), `BidirectionalObsMatch`, `DistSystem`. | **`finite_noninterference_of_bidirectional_coverage`**: if target observations both refine (`ObsRefines`) and are covered by (`SourceCoversTarget`) a noninterfering source, target satisfies `FiniteNoninterference`. | Four negative controls: **`branch_address_mutant_not_noninterference`** (same output `7` and common cost bound `≤ 1`, but leaks secret address `4` vs `8`), **`forward_matching_does_not_preserve_noninterference`**, **`trace_refinement_does_not_preserve_noninterference`** (refinement drops one branch trace on secret `false`), and **`same_coin_but_distinguishing_distribution`** (possibilistic support `{false, true}` matches on both secrets while biased coin distributions `(1,3)` vs `(3,1)` leak). |
| **`support/ObservationAdapters.lean`** | `ObsAdapter` (`mapObs : SrcObs → List TgtObs`), `PublicUniform` ($\forall x_1, x_2,\; \text{pub}(x_1) = \text{pub}(x_2) \implies \text{mapObs}(x_1, \tau) = \text{mapObs}(x_2, \tau)$), `AdapterImage`. | **`adapter_image_noninterference`** and **`target_noninterference_of_adapter_image`**: any `PublicUniform` macro-expansion adapter preserves `FiniteNoninterference` across exact adapter images. | **`expansion_is_not_literal_trace_equivalence`** (expanding 1 source `load a` into `[addrLow a, addrHigh a]` changes trace length from 1 to 2, refuting literal trace identity) and **`secret_adapter_not_noninterference`** (an adapter whose expansion depends on the secret bit `x.2` destroys noninterference even when the source trace `[load 4]` is constant). |
| **`support/OperationalObservations.lean`** | Step-indexed logged executions (`LoggedStep`, `LoggedRun`, `LoggedExec`) emitting per-step observation lists and accumulating traces over finite prefixes. | **`logged_run_CostStack_source_complete`** (connects operational logged runs to `CostStack.sourceTrace`) and **`prefix_noninterference_at_zero`**. | **`prefix_noninterference_fails_at_first_step`**: a single secret-dependent address step immediately violates prefix noninterference at $k = 1$. |
| **`support/OperationalAdapter.lean`** | Operational 2-phase lowering `OperationalAdapter` (`armed : Bool`) where each source `call`/`ret` step lowers to an `armed = true` step (emitting `stepTag` + work charge) followed by an `armed = false` step (emitting `stackDepth`). | **`target_logged_prefix_covered`** (every $m$-step target prefix is covered by a source prefix of length $\lceil m/2 \rceil$ via `expandPrefix`), **`operational_adapter_exact_image`**, and **`target_prefix_noninterference_via_adapter`** (full prefix noninterference transfer across 2-for-1 step expansion). | Demonstrates why naive 1-to-1 step lockstep fails on multi-step instruction lowering unless odd-length mid-expansion target prefixes (`m % 2 = 1`, covered by `expandHold`) are explicitly accounted for in the prefix adapter. |
| **`support/CallSecuritySpecimens.lean`** | Two-call sequential pipeline `firstCall` (`scratch := sec`, emits `[address .first false, charge .first, returned .first]`) followed by `secondCall` (`address .second state.scratch`), parameterized by `Mode.retained` vs. `Mode.fresh` (`resetBetweenCalls`). | **`retained_marginals_noninterference`** (each call in isolation is noninterfering from clean initial state `scratch = false`), **`completed_return_cost`** (both modes have identical total return cost `2` and `scratch = false` at completion), and **`fresh_composed_noninterference`** (when `resetBetweenCalls` clears `scratch := false` at the call boundary, all prefixes satisfy noninterference). | **`retained_not_noninterference`**: under `Mode.retained`, the 4-event prefix $k = 4$ exposes `[address .first false, charge .first, returned .first, address .second sec]`, leaking `sec` through the uncleaned `scratch` register despite both calls satisfying marginal noninterference and return-cost summaries! |
| **`support/CallSecurityComposition.lean`** | Abstract 2-stage composition contract `StageMatch R_0 R_1 R_2` where stage 1 maps $R_0$-related entry states to $R_1$-related intermediate states with equal stage-1 observations, and stage 2 maps $R_1$-related states to $R_2$-related exit states with equal stage-2 observations. | **`StageMatch.composed_obs_eq`**, **`StageMatch.composed_post`**, and **`fresh_call_cut_noninterference`** (instantiates `StageMatch` with $R_1(s_1, s_2) \triangleq s_1.\text{pub} = s_2.\text{pub} \wedge s_1.\text{scratch} = \text{false} \wedge s_2.\text{scratch} = \text{false}$ to prove composed noninterference of `Mode.fresh`). | **`retained_boundary_mismatch`** (proves `Mode.retained` violates the cut relation $R_1$ when $x_1.\text{sec} \neq x_2.\text{sec}$) and **`marginal_summary_does_not_supply_stage_contract`** (proves formally that marginal stage noninterference + completed return-cost summaries do not imply composed noninterference without $R_1$). |

---

## Boundaries

1. **Syntactic Security Type Systems Are Strictly Incomplete (`SyntacticTaintCT ⊊ RelationalProductCT`)**:
   - Never assume that rejection by a 1-run syntactic taint typechecker (`FaCT`, `CT-Wasm`, or unannotated taint propagation) implies a true timing leak, nor force cryptographic engineers to rewrite zeroization (`x ^ x`) or constant-time bitmask selects (`(a & m) | (a & ~m)`) if the verifier supports 1-pass cutpoint relational product certificates (`RelationalCTCert` / `ProductMachineCert`). Conversely, syntactic taint typing remains valuable as a fast $O(|P|)$ front-end filter because `taint_typing_universal_inclusion_in_relational_product` guarantees every taint-accepted program is already relationally valid.

2. **Software `Arch-CT` Proofs Do Not Prevent `KyberSlash`, `Spectre v1`, or `GoFetch`**:
   - Proving that retired architectural branch outcomes and retired memory addresses are secret-independent (`Level1_ArchCT`) is **insufficient** on physical CPUs if the binary executes variable-latency division instructions (`KyberSlash`, violating `Level2_VarTimeCT`), lacks speculative execution barriers or SLH masks behind bounds checks (`Spectre v1`, violating `Level3_SpecCT`), or stores secret-derived pointer-like words into L1 data cache lines on cores with active Data Memory-Dependent Prefetchers (`Augury`/`GoFetch`, violating `Level4_DmpCT`).

3. **Hardware `DIT` / `DOITM` / `Zkt` Bits Are Necessary Hardware Contracts, Not Standalone Proofs**:
   - Setting `PSTATE.DIT = 1`, `IA32_UARCH_MISC_CTL.DOITM = 1`, or targeting `RISC-V Zkt` **never** makes secret-dependent branches, secret-indexed memory loads, speculative execution gadgets, or `UDIV`/`DIV`/`REM` instructions constant-time (`dit_mode_fails_on_exempt_div_or_m1m2_dmp`). Furthermore, on Apple M1/M2 silicon, `PSTATE.DIT = 1` does not disable DMP; software pointer blinding/masking is required on M1/M2 (`dmp_pointer_masking_blinding_soundness`), whereas on Apple M3+ `PSTATE.DIT = 1` combined with a software `Level3_SpecCT` proof suffices (`dit_mode_upgrades_m3_dmp_when_div_free`).

4. **Forward Value Simulation and Trace Inclusion (`⊆`) Do Not Preserve Noninterference or Cost Bounds**:
   - Neither forward value-refining compiler simulation (`SecurityWitness.lean:source_not_constant_time`, `Observations.lean:forward_matching_does_not_preserve_noninterference`) nor subset trace refinement (`Observations.lean:trace_refinement_does_not_preserve_noninterference`) preserves constant-time noninterference: a compiler pass that prunes one nondeterministic branch on secret `false` while keeping two branches on secret `true` satisfies subset refinement $\text{Obs}_T(x) \subseteq \text{Obs}_S(x)$ yet creates a distinguishing observation on the target.
   - Similarly, forward simulation and I/O agreement do not bound target step count or transient stack high-water mark (`PrefixAccounting.lean:ExtraTarget.safety_and_output_do_not_bound_target`, `CostStack.lean:deeper_stack_counterexample`); reverse target-prefix coverage (`Accounting.upper_bounds`) is required.

5. **Possibilistic vs. Probabilistic Noninterference and Residual Call State**:
   - Possibilistic observation-set equality (`FiniteNoninterference`) does not detect biased probability distributions over identical support sets (`Observations.lean:same_coin_but_distinguishing_distribution`); randomized algorithms require distribution-preserving couplings (`Jasmin` `xrutt` / `wkequiv_io`).
   - Composing individually constant-time procedures sequentially is unsound unless intermediate residual state (`scratch` registers, spilled stack slots, or caller-visible flags) satisfies an explicit relational cut invariant $R_1$ at the call boundary (`CallSecuritySpecimens.lean:retained_not_noninterference`, `CallSecurityComposition.lean:StageMatch`).

---

## Evidence

### 1. Mechanized Lean 4 Proofs in `support/SideChannelFoundationsAndContracts.lean` (26 Theorems, Zero `sorry`, Zero Axioms)

All 26 foundational theorems in `support/SideChannelFoundationsAndContracts.lean` compile cleanly under Lean 4 (`v4.29.0-rc8` / `v4.34.1`) with zero `sorry` and zero axioms (`[anonymous]` in `#print axioms`):

| Section | Theorem Name (`support/SideChannelFoundationsAndContracts.lean`) | Lines | Mechanized Result |
| :--- | :--- | :---: | :--- |
| **§1. 2-Safety & Self-Composition** | `side_channel_freedom_not_1trace_property` | 64–92 | No 1-trace predicate `P : Trace → Prop` characterizes `CTNoninterference`. |
| **§1. 2-Safety & Self-Composition** | `self_composition_iff_2safety_ct` | 99–103 | Sequential self-composition ($P; P'$) is logically equivalent (`↔`) to `CTNoninterference`. |
| **§2. Lockstep Product** | `lockstep_product_iff_ct_noninterference` | 133–153 | 1-to-1 lockstep product execution (`LockstepProductHolds`) is equivalent (`↔`) to step-wise `CTNoninterference`. |
| **§2. Lockstep Product** | `lockstep_product_quadratic_path_reduction` | 164–171 | Lockstep product reduces branch path space from $4^k = (2^k)^2$ to $2^k$, with strict inequality $2^k < 4^k$ for all $k \ge 1$. |
| **§3. Taint vs. Relational Product** | `taint_type_system_sound_for_ct` | 269–282 | Syntactic taint typechecking (`checkProgTaint`) is sound for `ProgArchCT`. |
| **§3. Taint vs. Relational Product** | `relational_product_sound_for_ct` | 290–293 | Relational product verification (`ProgInRelationalProduct`) is sound for `ProgArchCT`. |
| **§3. Taint vs. Relational Product** | `taint_typing_universal_inclusion_in_relational_product` | 297–300 | Every taint-typable program is in `ProgInRelationalProduct`. |
| **§3. Taint vs. Relational Product** | `taint_rejects_xor_self_cancel` & `xor_self_cancel_is_arch_ct` | 310–323 | `progXorSelfCancel` (`rSec ^ rSec`) is rejected by taint typing (`none`) but satisfies `ProgArchCT`. |
| **§3. Taint vs. Relational Product** | `taint_rejects_masked_branchless_eq` & `masked_branchless_eq_is_arch_ct` | 341–351 | `progMaskedBranchlessEq` (`(rPub & rSec) \| (rPub & ~rSec)`) is rejected by taint typing but satisfies `ProgArchCT`. |
| **§3. Taint vs. Relational Product** | `relational_product_strictly_subsumes_taint_typing` | 354–361 | Strict inclusion $\text{SyntacticTaintCT} \subsetneq \text{RelationalProductCT}$ proven on both witnesses. |
| **§3. Declassification** | `conditioned_declassification_ct_soundness` | 380–394 | Public-conditioned declassification preserves `ProgArchCT` when the declassified expression agrees across `PubEquiv`. |
| **§3. Declassification** | `unguarded_declassification_launders_secret` | 398–409 | Unguarded declassification of `rSec` violates `ProgArchCT`. |
| **§4. 5-Level Contract Lattice** | `val_ni_not_arch_ct` | 536–556 | `progSecretBranchSameOut` satisfies `Level0_ValNI` but violates `Level1_ArchCT`. |
| **§4. 5-Level Contract Lattice** | `arch_ct_not_vartime_ct_kyberslash` | 563–585 | `progKyberSlashDiv` (`rSec / 3329`) satisfies `Level1_ArchCT` but violates `Level2_VarTimeCT`. |
| **§4. 5-Level Contract Lattice** | `kyberslash_barrett_replacement_restores_dmp_ct` | 592–600 | Replacing `UDIV 3329` with Barrett multiplication `(rSec * 5039) >> 24` restores `Level4_DmpCT`. |
| **§4. 5-Level Contract Lattice** | `vartime_ct_not_spec_ct_spectre` | 609–629 | `progSpectreV1Gadget` satisfies `Level2_VarTimeCT` but violates `Level3_SpecCT`. |
| **§4. 5-Level Contract Lattice** | `spectre_slh_fence_restores_dmp_ct` | 636–644 | Inserting `lfence`/SLH before the load restores `Level4_DmpCT`. |
| **§4. 5-Level Contract Lattice** | `spec_ct_not_dmp_ct_gofetch` | 652–672 | `progGoFetchDmpGadget` satisfies `Level3_SpecCT` but violates `Level4_DmpCT`. |
| **§4. 5-Level Contract Lattice** | `dmp_pointer_masking_blinding_soundness` | 679–687 | Pointer masking/blinding (`rSec & 0xFFFF`) below `0x10000000` restores `Level4_DmpCT`. |
| **§4. 5-Level Contract Lattice** | `five_level_leakage_hierarchy_strict` | 690–695 | Master strict separation `Level0_ValNI ≺ Level1_ArchCT ≺ Level2_VarTimeCT ≺ Level3_SpecCT ≺ Level4_DmpCT`. |
| **§5. Hardware DIT / DOITM / Zkt** | `dit_mode_fails_on_exempt_div_or_m1m2_dmp` | 739–759 | Hardware `DIT` fails on `UDIV` across all generations and fails on `GoFetch` DMP on Apple M1/M2. |
| **§5. Hardware DIT / DOITM / Zkt** | `dit_mode_upgrades_m3_dmp_when_div_free` | 763–774 | On Apple M3+, `PSTATE.DIT = 1` + software `Level3_SpecCT` guarantees full `DMP-CT` security. |
| **§5. Hardware DIT / DOITM / Zkt** | `anneal_dit_hardware_generation_trust_policy_soundness` | 787–795 | Soundness of the hardware-generation-aware `DITHardwareTrustPolicy` admission gate. |
| **§6. CacheAudit & Product Cert** | `cache_line_preload_zero_leakage_within_line` | 812–825 | Single-cache-line preload yields `0` bits of quantitative cache leakage (`CacheAudit`). |
| **§6. CacheAudit & Product Cert** | `anneal_relational_ct_cert_checker_sound` | 853–862 | Linear 1-pass `checkRelationalCTCert` checker is sound for `SatisfiesContract`. |
| **§6. CacheAudit & Product Cert** | `anneal_product_machine_wellformed_iff_all_prefix_ct` & `anneal_leakage_contract_trust_policy_gate_soundness` | 886–935 | Exact 2-safety embedding into 1-trace product machine (`UArchState × UArchState`) and `LeakageTrustPolicy` soundness. |

### 2. Primary Literature and Upstream Repository Citations

- **Hyperproperties, Self-Composition, Product Programs, and Relational Hoare Logic**:
  - Clarkson & Schneider, *Hyperproperties*, JCS 18(6), 2010 (`10.3233/JCS-2009-0393`).
  - Volpano, Smith & Irvine, *A Sound Type System for Secure Flow Analysis*, JCS 4(2–3), 1996 (`10.3233/JCS-1996-42-304`).
  - Benton, *Simple Relational Correctness Proofs for Static Analyses and Program Transformations*, POPL 2004 (`10.1145/964001.964003`).
  - Barthe, D'Argenio & Rezk, *Secure Information Flow by Self-Composition*, CSFW 2004 / MSCS 21(6), 2011 (`10.1017/S0960129511000193`).
  - Terauchi & Aiken, *Secure Information Flow as a Safety Problem*, SAS 2005 (`10.1007/11547662_24`).
  - Barthe, Crespo & Kunz, *Relational Verification Using Product Programs*, CAV 2011 (`10.1007/978-3-642-22110-1_17`).
  - Almeida, Barbosa, Barthe, Dupressoir & Emmi, *Verifying Constant-Time Implementations (`ct-verif`)*, USENIX Security 2016 (`imdea-software/verifying-constant-time@36e166781b0aa7398c12b335c7a4cd118b73568e`).
  - Cauligi et al., *FaCT: A DSL for Timing-Sensitive Computation*, PLDI 2019 (`10.1145/3314221.3314605`).
  - Watt, Renner, Popescu, Cauligi & Stefan, *CT-Wasm: Type-Driven Secure Cryptography for the Web Ecosystem*, POPL 2019 (`10.1145/3290390`).
  - Doychev, Feld, Köpf, Mauborgne & Reineke, *CacheAudit: A Tool for the Static Analysis of Cache Side Channels*, USENIX Security 2013 / ACM TISSEC 18(1), 2015 (`10.1145/2756550`).
- **Compiler Preservation and Jasmin**:
  - Barthe, Grégoire, Laporte & Swamy, *Secure Compilation of Side-Channel Countermeasures: The Case of Cryptographic "Constant-Time"*, CSF 2018 (`10.1109/CSF.2018.00031`).
  - Barthe et al., *Jasmin: High-Assurance and High-Speed Cryptography*, CCS 2017 (`10.1145/3133956.3134078`) and POPL 2020 (`10.1145/3371075`).
  - Barthe, Grégoire, Kunz, Laporte & Oliveira, *Cryptographic Security Preservation in Jasmin*, 2025 (`arXiv:2511.11292v1`) and upstream `jasmin-lang/jasmin@34f15840f10625bbc2cbf59b3d877e94c75bfbd9` (`proofs/compiler/it_compiler_proof.v`, `proofs/lang/relational_logic.v`, `proofs/itrees/xrutt.v`, `proofs/lang/it_sems_core_defs.v`).
- **Hardware-Software Leakage Contracts and Microarchitectural Side Channels**:
  - Guarnieri, Köpf, Morales, Reineke & Sánchez, *Hardware-Software Contracts for Secure Speculation*, IEEE S&P 2021 (`10.1109/SP40001.2021.00036`).
  - Kocher et al., *Spectre Attacks: Exploiting Speculative Execution*, IEEE S&P 2019 (`10.1109/SP.2019.00002`).
  - Vicarte et al., *Augury: Using Data Memory-Dependent Prefetchers to Leak Data at Rest*, IEEE S&P 2022 (`10.1109/SP46214.2022.9833570`).
  - Wang et al., *Hertzbleed: Turning Power Side-Channel Attacks Into Remote Timing Attacks on x86*, USENIX Security 2022 (`CVE-2022-23823`).
  - Chen et al., *GoFetch: Breaking Constant-Time Cryptographic Implementations Using Data Memory-Dependent Prefetchers*, USENIX Security 2024.
  - Bernstein, Karthikeyan, LZf, Panny & Prasanna, *KyberSlash: Exploiting Secret-Dependent Division Timings in Kyber Implementations*, 2024 (`ePrint 2024/1049`).

---

## Revalidation

1. **Re-verify the 26-Theorem Leakage Contract and Product-Machine Formalization (`support/SideChannelFoundationsAndContracts.lean`)**:
   ```bash
   lean support/SideChannelFoundationsAndContracts.lean
   ```
   Confirm zero errors, zero warnings, zero `sorry`, and that all `#print axioms` commands at the bottom of `support/SideChannelFoundationsAndContracts.lean` print `[anonymous]`.

2. **Re-run the Empirical Constant-Time Certificate Probe (`support/side_channel_cert_probe.py`)**:
   ```bash
   python3 support/side_channel_cert_probe.py
   ```
   Confirm that the script regenerates `support/side_channel_cert_probe_results.json` matching the 7-workload expressiveness and contract-level separation matrix.

3. **Re-verify the Value-Refinement vs. Constant-Time Separation Witness (`support/security-observations-and-relational-compiler-preservation/SecurityWitness.lean`)**:
   ```bash
   lean support/security-observations-and-relational-compiler-preservation/SecurityWitness.lean
   ```
   Confirm that `values_agree`, `model_constant_time`, and `source_not_constant_time` elaborate cleanly with no axioms (verified on Lean `4.31.0` commit `68218e876d2a38b1985b8590fff244a83c321783` and newer toolchains; note that if auditing historical Lean toolchains prior to `4.32.2`, check `leanprover/lean4` issue 14576 / PR 14577 for nested-inductive kernel soundness fixes).

4. **Re-verify the 8 Operational Cost, Stack-Depth, and Relational Adapter Modules (`support/PrefixAccounting.lean` .. `support/CallSecurityComposition.lean`)**:
   ```bash
   mkdir -p build/AnnealResearch
   for mod in PrefixAccounting CostStack Observations ObservationAdapters OperationalObservations OperationalAdapter CallSecuritySpecimens CallSecurityComposition; do
     LEAN_PATH=build lean -o "build/AnnealResearch/${mod}.olean" "support/${mod}.lean"
   done
   ```
   Confirm that all 8 modules compile in topological order and reproduce the 113 `#print axioms` audit declarations recorded in `support/lean-check-results.json`.

5. **Revalidate Jasmin Upstream ITree Relational Proof Anchors**:
   In a checkout of `jasmin-lang/jasmin` at commit `34f15840f10625bbc2cbf59b3d877e94c75bfbd9`, inspect `proofs/compiler/it_compiler_proof.v:1688–1730` (`it_compile_prog_to_asmP`), `proofs/lang/relational_logic.v:222–226` (`wkequiv_io`), and `proofs/itrees/xrutt.v:138–147` (`ErrCutoff := is_error` vs. `NoErrCutoff`), confirming whether remaining non-ported passes (`§6.1` of `arXiv:2511.11292v1`) have been integrated into `it_compile_prog_to_asmP` or whether source-safety discharge has been internalized into the top-level theorem.
