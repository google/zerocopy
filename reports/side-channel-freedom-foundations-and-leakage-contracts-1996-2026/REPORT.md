# Formalizing Side-Channel-Freedom: 2-Safety Hyperproperties, Self-Composition, Synchronized Product Programs, Security Type Systems, and the Hardware-Software Leakage Contract Lattice (1996–2026)

## Summary

Verifying that systems and cryptographic code is free of timing and microarchitectural side channels requires bridging two foundational divides:

1. **The Proof-Methodology Divide (2-Safety Hyperproperties vs. 1-Trace Safety Checkers)**:
   In Clarkson & Schneider's topological hierarchy of security policies (*Hyperproperties*, JCS 2010), side-channel freedom (Constant-Time Noninterference) is a **2-safety hyperproperty**—a relational predicate over pairs of execution traces $\forall s_1, s_2,\; \text{LowEq}(s_1, s_2) \implies \text{obsTrace}(p, s_1) = \text{obsTrace}(p, s_2)$—that provably **cannot** be expressed as any 1-trace property $P(\text{pubIn}, \tau)$ on individual executions (`side_channel_freedom_not_1trace_property`). Between 1996 and 2026, four static verification paradigms emerged to check this 2-safety hyperproperty:
   - **Sequential Self-Composition ($P ; P'$, Barthe, D'Argenio & Rezk 2004/2011; Terauchi & Aiken 2005)**: Reduces 2-safety noninterference to 1-trace safety over a duplicated state space (`self_composition_iff_2safety_ct`), at the cost of $O(2^{2k}) = 4^k$ cross-branch path explosion (`lockstep_product_quadratic_path_reduction`) and whole-program functional loop invariants.
   - **1-to-1 Lockstep Synchronized Product Programs ($P \times_{\text{sync}} P$, Barthe, Crespo & Kunz CAV 2011; Almeida et al. `ct-verif` USENIX Security 2016)**: Exploits the fact that Constant-Time Noninterference mandates per-step control-flow synchronization (`pcBranch` equality), making lockstep product execution **both sound and complete (`↔`)** (`lockstep_product_iff_ct_noninterference`) while reducing branch-path exploration from $4^k$ to $2^k$ and keeping loop invariants purely relational ($x_1 = x_2$).
   - **1-Run Syntactic Security Type Systems (`Volpano, Smith & Irvine` JCS 1996; `FaCT` PLDI 2019; `CT-Wasm` POPL 2019)**: Assigns a unary secrecy taint label ($\mathsf{pubLbl}$ vs. $\mathsf{secLbl}$) in a single linear pass (`taint_type_system_sound_for_ct`), which embeds universally into 2-run relational product checking (`taint_typing_universal_inclusion_in_relational_product`) but is **strictly incomplete ($\subsetneq$)** (`relational_product_strictly_subsumes_taint_typing`) on algebraic/bitwise constant-time idioms such as XOR self-cancellation (`rSec ^ rSec`) and branchless masked selection between equal public values (`(rPub & rSec) | (rPub & ~rSec)`).
   - **1-Pass Cutpoint Relational Product Certificates (`Benton` POPL 2004; `Anneal.CertChecker`)**: Combines linear-time $O(|P|)$ single-pass certificate checking with relational equality tracking (`.relEqual` vs. `.relVarying`) and algebraic cancellation witnesses (`relational_product_sound_for_ct`, `anneal_relational_ct_cert_checker_sound`).
2. **The Hardware-Software Leakage Contract Divide (`Val-NI ≺ Arch-CT ≺ VarTime-CT ≺ Spec-CT ≺ DMP-CT`)**:
   Classical Constant-Time (`Arch-CT`, requiring secret-independent control flow and memory addresses) was long assumed sufficient to prevent timing attacks. Between 2018 and 2024, four classes of microarchitectural attacks broke `Arch-CT` code:
   - **Variable-Latency ALU Dividers (`KyberSlash`, 2023/2024)**: Secret-dependent integer division (`udiv`/`sdiv`/`rem`) in ML-KEM leaked secret keys despite zero secret branches or memory accesses (`arch_ct_not_vartime_ct_kyberslash`), even when hardware timing modes (`Intel DOITM` / `RISC-V Zkt`) were enabled (`dit_mode_fails_on_exempt_div_or_m1m2_dmp`).
   - **Speculative PHT Bounds-Check Bypass (`Spectre v1`, 2018; Guarnieri et al. IEEE S&P 2021)**: Transient execution along mispredicted conditional branches indexed the data cache with secrets (`vartime_ct_not_spec_ct_spectre`).
   - **Data Memory-Dependent Prefetchers (`Augury` IEEE S&P 2022; `GoFetch` USENIX Security 2024)**: Hardware DMPs on Apple M1/M2/M3 inspect **data values** loaded from fixed public addresses and issue cache prefetches whenever a secret word matches a canonical pointer bit-pattern (`spec_ct_not_dmp_ct_gofetch`). Crucially, enabling `PSTATE.DIT = 1` (`ARMv8.4-DIT`) disables the DMP on Apple M3 (`dit_mode_upgrades_m3_dmp_when_div_free`) but is **ignored by the DMP on Apple M1 and M2** (`dit_mode_fails_on_exempt_div_or_m1m2_dmp`), requiring software constant-time pointer-tag masking / blinding (`dmp_pointer_masking_blinding_soundness`).

This report synthesizes these methodologies and hardware-software contracts from 17 primary sources and mechanizes **26 constructive, axiom-clean theorems** in [`support/SideChannelFoundationsAndContracts.lean`](support/SideChannelFoundationsAndContracts.lean) (verified under Lean `v4.34.1` with `0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`), alongside an empirical benchmark of four side-channel verification regimes across 7 workloads in [`support/side_channel_cert_probe.py`](support/side_channel_cert_probe.py).

---

## Applicability

This report applies directly to:

- **Anneal's Trusted Operational and Refinement Core (`AeneasVerif/anneal`, commit `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`)**:
  Specifically `trusted/lean/Trusted/StepResult.lean` (`StepResult`, `PrefixOutcome`, `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`, `SmallStepMachine.toLanguage`), `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Language`, `Language.WellFormedOn`, `TrustedAssumption`, `TrustPolicy`, `VerificationResultOn`), and `theory/Anneal/Refinement.lean` (`Anneal.CertChecker`).
- **Relational Compiler Preservation and Operational Noninterference Transport**:
  Complements the corpus reports [`reports/security-observations-and-relational-compiler-preservation/REPORT.md`](../security-observations-and-relational-compiler-preservation/REPORT.md) and [`reports/opsem-cost-stack-depth-and-relational-noninterference/REPORT.md`](../opsem-cost-stack-depth-and-relational-noninterference/REPORT.md) by providing the source/IR/bytecode proof methodologies (`syncProductMachine`, `checkRelationalProductProg`, conditioned declassification) and the 5-level hardware-software leakage contract lattice (`Level0_ValNI` through `Level4_DmpCT`) that feed into compiler preservation and `TrustPolicy` auditing.

---

## Findings

### 1. The Mathematical Hierarchy of Side-Channel-Freedom Proof Methodologies (1996–2026)

#### 1.1 Primary Sources

| Work | Authors & Venue | Identifier / DOI | Core Contribution |
|---|---|---|---|
| **Sound Security Type System** | Dennis Volpano, Geoffrey Smith, Cynthia Irvine, *JCS* Vol. 4(2–3), pp. 167–187, 1996 | `10.3233/JCS-1996-42-304` | Foundational 1-run security type system ($\Gamma, pc \vdash c$) proving noninterference via typed low-equivalence preservation |
| **Self-Composition** | Gilles Barthe, Pedro R. D'Argenio, Tamara Rezk, *CSFW 2004* / *MSCS* Vol. 21(6), pp. 1207–1252, 2011 | `10.1017/S0960129511000193` | Reduces 2-safety noninterference of $P$ to 1-trace Hoare/safety verification of sequential self-composition $P ; P'$ on disjoint variable copies |
| **Type-Directed Self-Composition** | Tachio Terauchi, Alex Aiken, *SAS 2005*, LNCS Vol. 3672, pp. 352–367 | `10.1007/11547662_24` | Uses 1-run security types to guide variable renaming and self-composition alignment for safety model checkers |
| **Relational Hoare Logic (RHL)** | Nick Benton, *POPL 2004*, pp. 14–25 | `10.1145/964001.964003` | Foundational 2-run relational judgment $\vdash c_1 \sim c_2 : \Phi \Rightarrow \Psi$ over partial equivalence relations (PERs) |
| **Hyperproperties** | Michael R. Clarkson, Fred B. Schneider, *JCS* Vol. 18(6), pp. 1157–1210, 2010 | `10.3233/JCS-2009-0393` | Classifies security policies into trace properties ($\Pi \subseteq \text{Traces}$) vs. hyperproperties ($\mathcal{H} \subseteq \mathcal{P}(\text{Traces})$) and $k$-safety hyperproperties |
| **Synchronized Product Programs** | Gilles Barthe, Juan Manuel Crespo, César Kunz, *CAV 2011*, LNCS Vol. 6806, pp. 200–215 | `10.1007/978-3-642-22110-1_17` | Interleaves lockstep loops and branches ($P_1 \times_{\text{sync}} P_2$) so relational loop invariants remain simple variable equalities ($x_1 = x_2$) |
| **`ct-verif`** | José Bacelar Almeida, Manuel Barbosa, Gilles Barthe, François Dupressoir, Michael Emmi, *USENIX Security 2016*, pp. 53–70 | `imdea-software/verifying-constant-time` (`36e166781b0aa7398c12b335c7a4cd118b73568e`) | Selective synchronized product reduction at the LLVM IR / Boogie level; formalizes output-insensitive and `public_out`-conditioned Constant-Time |
| **`FaCT` & `CT-Wasm`** | Sunjay Cauligi et al., *PLDI 2019* (`10.1145/3314221.3314605`); Conrad Watt et al., *POPL 2019* (`10.1145/3290390`) | `10.1145/3314221.3314605` & `10.1145/3290390` | 1-run secrecy type systems (`secret`/`public`, `s32`/`i32`) enforcing Constant-Time in a single linear pass |

#### 1.2 Why Side-Channel-Freedom Cannot Be Checked by Any 1-Trace Monitor (`side_channel_freedom_not_1trace_property`)

In [`support/SideChannelFoundationsAndContracts.lean`](support/SideChannelFoundationsAndContracts.lean) (`lines 274–345`), we formalize Constant-Time Noninterference (`CTNoninterference`) over a deterministic operational machine (`SCState`, `SCInstr`, `ObsEvent`):
$$\text{CTNoninterference}(p) \;\iff\; \forall s_1, s_2 \in \text{SCState},\; \text{LowEq}(s_1, s_2) \implies \text{obsTrace}(p, s_1) = \text{obsTrace}(p, s_2)$$
**Theorem 1 (`side_channel_freedom_not_1trace_property`, `lines 315–345`)** proves that **no 1-trace predicate** $P : \mathbb{N} \to \text{List ObsEvent} \to \text{Bool}$ inspecting public inputs and a single execution's observation trace can characterize `CTNoninterference`:
- `progConstTrue := [.branchEqZero (.const 0) (.const 1) (.const 0)]` unconditionally emits `[.branchCond true]` on every state and satisfies `CTNoninterference`;
- `progConstFalse := [.branchEqZero (.const 1) (.const 1) (.const 0)]` unconditionally emits `[.branchCond false]` on every state and satisfies `CTNoninterference`;
- `progSecretBranch := [.branchEqZero .varSecIn (.const 1) (.const 0)]` emits `[.branchCond true]` when `s.secIn = 0` and `[.branchCond false]` when `s.secIn = 1`, violating `CTNoninterference`.
Because every individual trace of `progSecretBranch` is bit-for-bit identical to the unique trace of either `progConstTrue` or `progConstFalse` on the same public input, any 1-trace predicate $P$ that accepts all constant-time programs must accept every individual execution of `progSecretBranch`, contradiction.

#### 1.3 Sequential Self-Composition vs. 1-to-1 Lockstep Synchronized Product Completeness (`self_composition_iff_2safety_ct`, `lockstep_product_iff_ct_noninterference`, `lockstep_product_quadratic_path_reduction`)

1. **Sequential Self-Composition (`runSelfComposed`, `lines 352–387`)**:
   Runs $P$ on `leftState := s₁` to completion and then runs a renamed copy $P'$ on `rightState := s₂`, asserting `obsTraceEq leftObs rightObs = true` at termination. **Theorem 2 (`self_composition_iff_2safety_ct`, `lines 375–387`)** proves that 1-trace safety of `runSelfComposed` is logically equivalent (`↔`) to `CTNoninterference`. However, across $k$ sequential branches, unaligned self-composition explores $2^k \times 2^k = 4^k$ twin branch-path pairs (`selfCompBranchPaths k = 2^k * 2^k`).
2. **1-to-1 Lockstep Synchronized Product (`runLockstepProduct`, `lines 399–577`)**:
   While general termination-insensitive noninterference (`Level0_ValNI`) allows two low-equivalent runs to take different control-flow branches before reconverging, **Constant-Time Noninterference specifically mandates `obsEvent(c, s₁) = obsEvent(c, s₂)` at every step**—including branch outcomes `.branchCond taken`. Therefore, two low-equivalent executions of a Constant-Time program **never diverge in control flow**.
   - **Theorem 3 (`lockstep_product_iff_ct_noninterference`, `lines 517–527`)** proves that the 1-to-1 Lockstep Synchronized Product Machine `runLockstepProduct` (which steps `(s₁, s₂)` together and faults immediately if `ev₁ ≠ ev₂`) is **both sound and complete (`↔`)** for `CTNoninterference`.
   - **Theorem 4 (`lockstep_product_quadratic_path_reduction`, `lines 562–577`, `0` axioms)** proves that lockstep synchronization reduces $k$-branch path exploration from $4^k$ (`selfCompBranchPaths`) to $2^k$ (`lockstepBranchPaths`).

#### 1.4 1-Run Syntactic Taint Typing $\subsetneq$ 1-Pass Relational Product Certificates (`taint_type_system_sound_for_ct`, `taint_typing_universal_inclusion_in_relational_product`, `relational_product_strictly_subsumes_taint_typing`)

In Section 3 of [`support/SideChannelFoundationsAndContracts.lean`](support/SideChannelFoundationsAndContracts.lean) (`lines 579–1198`), we formalize both a 1-run syntactic security type checker (`checkTaintProg : TaintEnv → List SCInstr → Option TaintEnv`, modeling Volpano-Smith-Irvine / `CT-Wasm` / `FaCT`) and a 1-pass relational equality-tracking product checker (`checkRelationalProductProg : RelEnv → List SCInstr → Option RelEnv`):
- **Soundness of Both Checkers**: **Theorem 5 (`taint_type_system_sound_for_ct`, `lines 791–798`)** and **Theorem 6 (`relational_product_sound_for_ct`, `lines 997–1008`)** prove that both checkers soundly imply `CTNoninterference`.
- **Universal Inclusion**: **Theorem 7 (`taint_typing_universal_inclusion_in_relational_product`, `lines 1147–1156`)** proves that every instruction sequence accepted by 1-run syntactic taint typing is accepted by the 1-pass relational product checker (`∀ env prog, (checkTaintProg env prog).isSome = true → (checkRelationalProductProg (relEnvOfTaintEnv env) prog).isSome = true`).
- **Strict Separation ($\subsetneq$)**: **Theorem 8 (`relational_product_strictly_subsumes_taint_typing`, `lines 1180–1198`)** proves two concrete separating programs:
  1. `progXorSelfCancel` (`lines 1160–1163`), which zeroizes a scratch register via `rTemp := rSec ^ rSec` and uses `rTemp` as a memory load address: rejected by 1-run syntactic taint typing (`false`) because `.varSec` is tainted `.secLbl`, yet accepted by `checkRelationalProductProg` (`true`) and proved `CTNoninterference`;
  2. `progMaskedBranchlessEq` (`lines 1167–1170`), which computes a branchless select `(rPub & rSec) | (rPub & ~rSec)` and uses the result as a load address: rejected by 1-run taint typing (`false`), yet accepted by `checkRelationalProductProg` (`true`) and proved `CTNoninterference`.

#### 1.5 Conditioned Public-Output Declassification vs. Unguarded Declassification (`conditioned_declassification_ct_soundness`, `unguarded_declassification_launders_secret`)

In Section 4 (`lines 1200–1250`), we formalize `ct-verif`'s output-sensitive Constant-Time (`CondCTNoninterference declassPred prog`, requiring trace equality across low-equivalent states that also agree on the declared public output `declassPred s₁ = declassPred s₂`, such as an AEAD MAC verification bit):
- **Theorem 9 (`conditioned_declassification_ct_soundness`, `lines 1228–1234`)** proves that `progDeclassifyAndBranch` satisfies `CondCTNoninterference (fun s => s.secIn)`.
- **Theorem 10 (`unguarded_declassification_launders_secret`, `lines 1241–1248`)** proves that treating `declassifyToPub` as an unconditioned taint reset violates `CTNoninterference`.

---

### 2. The 5-Level Hardware-Software Leakage Observation Hierarchy (`Val-NI ≺ Arch-CT ≺ VarTime-CT ≺ Spec-CT ≺ DMP-CT`)

#### 2.1 Primary Sources

| Level / Attack | Authors & Venue | Identifier / DOI | Microarchitectural Channel |
|---|---|---|---|
| **Hardware-Software Speculation Contracts ($\llbracket \cdot \rrbracket_{\text{arch}}^{\text{seq}}, \llbracket \cdot \rrbracket_{\text{ct}}^{\text{seq}}, \llbracket \cdot \rrbracket_{\text{ct}}^{\text{spec}}$)** | Marco Guarnieri, Boris Köpf, José F. Morales, Jan Reineke, Andrés Sánchez, *IEEE S&P 2021*, pp. 1317–1334 | `10.1109/SP40001.2021.00036` | Formalizes sequential and speculative constant-time leakage contracts |
| **`KyberSlash` (Variable-Latency Division)** | Daniel J. Bernstein et al., *IACR ePrint 2024/1049* (disclosed Dec 2023) | `https://kyberslash.cr.yp.to/` / `ePrint 2024/1049` | Secret-dependent `udiv`/`sdiv`/`rem` latency in ML-KEM (`CRYSTALS-Kyber`) |
| **`Hertzbleed` (DVFS Power/Frequency Throttling)** | Yingchen Wang et al., *USENIX Security 2022*, pp. 679–697 | `CVE-2022-23823` | Data Hamming-weight power draw triggers DVFS clock throttling |
| **`Augury` & `GoFetch` (Data Memory-Dependent Prefetchers)** | Jose Rodrigo Sanchez Vicarte et al., *IEEE S&P 2022* (`10.1109/SP46214.2022.9833570`); Boru Chen et al., *USENIX Security 2024* | `10.1109/SP46214.2022.9833570` & USENIX Security 2024 | Hardware DMP dereferences loaded secret memory values that match canonical pointer bit-patterns |

#### 2.2 The 5-Level Lattice, Four Strict Separations, and Verified Software Mitigations

In Section 5 of [`support/SideChannelFoundationsAndContracts.lean`](support/SideChannelFoundationsAndContracts.lean) (`lines 1252–1694`), we formalize the 5-level Hardware-Software Leakage Contract Lattice over `HwSwState` and `HwSwExecRecord`:
$$\mathsf{Level4\_DmpCT} \implies \mathsf{Level3\_SpecCT} \implies \mathsf{Level2\_VarTimeCT} \implies \mathsf{Level1\_ArchCT} \implies \mathsf{Level0\_ValNI}$$

| Level | Lean 4 Predicate | Observable Trace | Strict Separation Theorem (`Level k ∧ ¬Level (k+1)`) | Verified Software Mitigation Theorem (`→ Level4_DmpCT`) |
|---|---|---|---|---|
| **Level 0 (`Val-NI`)** | `Level0_ValNI` | `finalPubOut` | **Theorem 12 (`val_ni_not_arch_ct`, `lines 1554–1562`)** via `progValNiOnly` | Eliminating secret branch |
| **Level 1 (`Arch-CT`)** | `Level1_ArchCT` | Level 0 + `archTrace` (`.pcBranch`, `.memAddr`) | **Theorem 13 (`arch_ct_not_vartime_ct_kyberslash`, `lines 1576–1584`)** via `progKyberSlashDiv` (`div 3329`) | **Theorem 14 (`kyberslash_barrett_replacement_restores_dmp_ct`, `lines 1591–1595`)** via Barrett mul+shift `(x * 20159) >> 26` |
| **Level 2 (`VarTime-CT`)** | `Level2_VarTimeCT` | Level 1 + `aluVarTimeTrace` (`.divRemOperands`) | **Theorem 15 (`vartime_ct_not_spec_ct_spectre`, `lines 1609–1621`)** via `progSpectreV1Unfenced` | **Theorem 16 (`spectre_slh_fence_restores_dmp_ct`, `lines 1627–1634`)** via Speculative Load Hardening / `lfence` |
| **Level 3 (`Spec-CT`)** | `Level3_SpecCT` | Level 2 + `specPhtTrace` (`.specCacheLoad`) | **Theorem 17 (`spec_ct_not_dmp_ct_gofetch`, `lines 1649–1657`)** via `progGoFetchUnmasked` | **Theorem 18 (`dmp_pointer_masking_blinding_soundness`, `lines 1669–1677`)** via pointer-tag masking / blinding (`progGoFetchBlinded`) |
| **Level 4 (`DMP-CT`)** | `Level4_DmpCT` | Level 3 + `dmpTrace` (`.dmpPrefetchTarget`) | Conjoined in **Theorem 19 (`five_level_leakage_hierarchy_strict`, `lines 1683–1693`)** | Full 5-level side-channel freedom |

---

### 3. Hardware Constant-Time Mode Registers (`ARMv8.4-DIT` `PSTATE.DIT`, `Intel DOITM`, `RISC-V Zkt`) vs. Exempt Opcodes & Apple M1/M2 vs. M3 `DMP`

In Section 7 of [`support/SideChannelFoundationsAndContracts.lean`](support/SideChannelFoundationsAndContracts.lean) (`lines 2132–2478`), we formalize the interaction between runtime hardware timing-mode registers (`ditEnabled : Bool`, representing `PSTATE.DIT = 1` on ARMv8.4-A, `IA32_UARCH_MISC_CTL[DOITM] = 1` on Intel x86-64, or the `Zkt` profile on RISC-V) and microarchitectural generation (`MicroarchGen`: `.m1m2_ditIgnoresDmp` vs. `.m3_ditDisablesDmp`):

1. **Why Enabling `DIT` / `DOITM` / `Zkt` Does Not Rescue Exempt Division or Apple M1/M2 `DMP` (`dit_mode_fails_on_exempt_div_or_m1m2_dmp`, `lines 2299–2320`)**:
   - Both Intel's `DOITM` specification and the RISC-V `Zkt` specification **explicitly exclude integer division (`DIV`/`IDIV`/`UDIV`/`SDIV`/`REM`/`REMU`)** from their data-independent execution latency guarantees. Consequently, even on `.m3_ditDisablesDmp` with `ditEnabled = true` (`cfgM3WithDIT`), `progKyberSlashDiv` satisfies `Level1_ArchCT_Mode cfgM3WithDIT` but violates `Level2_VarTimeCT_Mode cfgM3WithDIT`.
   - As demonstrated in `GoFetch` (Chen et al., USENIX Security 2024, §6), setting `PSTATE.DIT = 1` on **Apple M1 and M2** (`.m1m2_ditIgnoresDmp`) does **not** disable the Data Memory-Dependent Prefetcher. Thus `progGoFetchUnmasked` satisfies `noExemptVarTimeOps = true` and `Level3_SpecCT_Mode cfgM1M2WithDIT`, yet violates `Level4_DmpCT_Mode cfgM1M2WithDIT`.
2. **When `PSTATE.DIT = 1` Automatically Upgrades `Spec-CT` to `DMP-CT` Without Software Blinding (`dit_mode_upgrades_m3_dmp_when_div_free`, `lines 2394–2428`)**:
   - On **Apple M3** (`.m3_ditDisablesDmp`) with `PSTATE.DIT = 1` (`cfgM3WithDIT`), the hardware DMP is disabled (`dmpSuppressedByHwMode cfgM3WithDIT = true`). We prove that for **every** program `prog` satisfying `noExemptVarTimeOps prog = true` (zero `UDIV`/`REM` instructions), `Level1_ArchCT_Mode cfgM3WithDIT prog` + speculative PHT safety automatically upgrades all the way to **`Level4_DmpCT_Mode cfgM3WithDIT prog`** (`Level4_DmpCT_Mode cfgM3WithDIT progGoFetchUnmasked` holds without software pointer-blinding overhead).
3. **Hardware-Generation-Aware `TrustPolicy` Gate (`anneal_dit_hardware_generation_trust_policy_soundness`, `lines 2447–2476`)**:
   - Proves that `hwModeDmpUpgradeTrustPolicy` soundly permits unblinded `Spec-CT → DMP-CT` promotion on `(cfgM3WithDIT, progGoFetchUnmasked)` while rejecting `(cfgM1M2WithDIT, progGoFetchUnmasked)`, `({ ditEnabled := false, hwGen := .m3_ditDisablesDmp }, progGoFetchUnmasked)`, and `(cfgM3WithDIT, progKyberSlashDiv)`.

---

### 4. Quantitative Cache Bounds (`CacheAudit`) & Direct Embedding into Anneal (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`)

1. **Quantitative Cache Side-Channel Bounds (`CacheAudit`, Doychev et al. USENIX Security 2013 / ACM TISSEC 2015, DOI `10.1145/2756550`)**:
   - **Theorem 20 (`cache_line_preload_zero_leakage_within_line`, `lines 1738–1744`)** proves that an 8-entry table aligned within a single 64-byte cache line (`offsets = [0, 8, 16, 24, 32, 40, 48, 56]`, `baseLine = 4`) yields `reachableCacheLines 4 [0, 8, 16, 24, 32, 40, 48, 56] = [4]` of cardinality **`1`** ($\log_2(1) = 0$ leaked bits at cache-line granularity), whereas a 64-byte-strided table (`[0, 64, 128, 192]`) yields cardinality **`4`** ($\log_2(4) = 2$ leaked bits).
2. **Direct Embedding into Anneal's `SmallStepMachine`, `Language.WellFormedOn`, `TrustPolicy`, and `CertChecker` (`lines 1746–2130`)**:
   - **Synchronized Product `SmallStepMachine` (`anneal_product_machine_wellformed_iff_all_prefix_ct`, `lines 1975–1993`)**: Mirroring `Trusted/StepResult.lean` and `Trusted/Refinement.lean` at commit `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, we define `syncProductMachine M obsEq` over twin states `State × State`, which transitions to `StepResult.failed` whenever `obsEq obs₁ obs₂ = false`. **Theorem 21** proves that standard 1-trace `Language.WellFormedOn (syncProductMachine M obsEq).toLanguage (fun q => lowEq q.init.1 q.init.2) p` is **logically equivalent (`↔`)** to `AllPrefixSafeAndCT M lowEq p`.
   - **Leakage Contract `TrustPolicy` (`anneal_leakage_contract_trust_policy_gate_soundness`, `lines 2049–2072`)**: Proves that `hwLeakageTrustPolicy` (`LeakageLevelLE item.targetHwRequiredLevel item.provenLevel`) soundly guarantees target hardware side-channel freedom while rejecting under-leveled proofs.
   - **Single-Pass Relational `CertChecker` (`anneal_relational_ct_cert_checker_sound`, `lines 2122–2130`)**: Instantiates `Anneal.CertChecker` (`theory/Anneal/Refinement.lean:1941-1947`) with `checkRelationalProductProg`.

---

### 5. Empirical Side-Channel Certificate Verification Benchmark ([`support/side_channel_cert_probe.py`](support/side_channel_cert_probe.py))

Executing [`support/side_channel_cert_probe.py`](support/side_channel_cert_probe.py) benchmarks four verification regimes across 5 safe Constant-Time primitives and 2 leaky negative controls ([`support/side_channel_cert_probe_results.json`](support/side_channel_cert_probe_results.json)):

| Workload | Safe (`Level4`)? | Instrs ($|P|$) | Branches ($k$) | (a) Self-Comp ($4^k$) Steps | (b) Lockstep ($2^k$) Steps | (c) 1-Run Taint (`CT-Wasm`) Steps / Verdict | (d) 1-Pass Relational `CertChecker` Steps / Verdict | Cert Size (Bytes) | Speedup: `CertChecker` vs. Self-Comp / Lockstep |
|---|---|---|---|---|---|---|---|---|---|
| `montgomery_ladder_step` | Yes | 16 | 8 | `2,097,152` (`65,536` pairs) | `4,096` (`256` paths) | `16` (`ACCEPT`) | `16` (`ACCEPT`, `0` alg witnesses) | `40 B` | **`131,072x` / `256x`** |
| `chacha20_quarter_round` | Yes | 16 | 4 | `8,192` (`256` pairs) | `256` (`16` paths) | `16` (`ACCEPT`) | `16` (`ACCEPT`, `0` alg witnesses) | `24 B` | **`512x` / `16x`** |
| `mlkem_barrett_reduce` | Yes | 16 | 6 | `131,072` (`4,096` pairs) | `1,024` (`64` paths) | `16` (`ACCEPT`) | `16` (`ACCEPT`, `0` alg witnesses) | `32 B` | **`8,192x` / `64x`** |
| `masked_table_select` | Yes | 8 | 5 | `16,384` (`1,024` pairs) | `256` (`32` paths) | `2` (**`FALSE POSITIVE REJECT`**: `tainted_load_address:eff_addr`) | `8` (`ACCEPT`, `1` alg witness: `RULE_MASKED_SELECT_SAME_PUB`) | `24 B` | **`2,048x` / `32x`** |
| `xor_scratchpad_zeroize` | Yes | 7 | 4 | `3,584` (`256` pairs) | `112` (`16` paths) | `3` (**`FALSE POSITIVE REJECT`**: `tainted_load_address:clean_addr`) | `7` (`ACCEPT`, `1` alg witness: `RULE_XOR_SELF_CANCEL`) | `16 B` | **`512x` / `16x`** |
| `kyberslash_leaky_div` | **No** (Neg Ctrl) | 3 | 2 | `96` (`REJECT`) | `12` (`REJECT`) | `1` (`TRUE REJECT`: `tainted_vartime_div`) | `1` (`TRUE REJECT`: `relational_varying_exempt_udiv`) | `7 B` | **`96x` / `12x`** |
| `spectre_v1_leaky_load` | **No** (Neg Ctrl) | 3 | 2 | `96` (`REJECT`) | `12` (`REJECT`) | `1` (`TRUE REJECT`: `unfenced_speculative_secret_load`) | `1` (`TRUE REJECT`: `unfenced_speculative_secret_load`) | `7 B` | **`96x` / `12x`** |
| **Total / Aggregate** | **5 Safe, 2 Unsafe** | **69** | **31** | **`2,256,576` steps** | **`5,768` steps** | **`55` steps (`2/5 = 40%` False Positives)** | **`65` steps (`0%` False Positives, `0%` False Negatives)** | **`150 B` total** | **`34,716.6x` / `88.7x`** |

---

## Boundaries

1. **Physical Power, EM, and DVFS Frequency-Throttling Channels (`Hertzbleed`, CVE-2022-23823)**:
   Even when a program satisfies `Level4_DmpCT` (zero secret branches, zero secret memory addresses, zero variable-time ALU dividers, zero speculative PHT leaks, and zero DMP pointer-value dereferences), data-dependent Hamming-weight power consumption can induce Dynamic Voltage and Frequency Scaling (DVFS) clock-frequency variations (`Hertzbleed`, Wang et al. USENIX Security 2022) or physical electromagnetic/power traces unless mitigated by constant-power masking shares or frequency-locked execution.
2. **Backend Compiler Preservation Below the Verified IR Boundary**:
   Verifying a `CertChecker` or `syncProductMachine` certificate at the MIR or LLVM IR level guarantees hardware side-channel freedom only if subsequent lowering and register-allocation passes preserve the target leakage contract (`Arch-CT`, `VarTime-CT`, `Spec-CT`, or `DMP-CT`). Unverified backend optimizations that introduce branch-on-zero shortcuts, spill secret pointer-like values to unmasked stack slots, or emit `UDIV` must be prevented by binary-level certificate checking (`Kraken` / `Rv64Semantics` / `X86Semantics`) or a leakage-preserving compiler (`Jasmin`).

---

## Evidence

### 1. Mechanized Theorem Inventory ([`support/SideChannelFoundationsAndContracts.lean`](support/SideChannelFoundationsAndContracts.lean))

| # | Theorem Name | Section | Lines | Axiom Footprint (`#print axioms`) |
|---|---|---|---|---|
| 1 | `side_channel_freedom_not_1trace_property` | Section 1 | `315–345` | `[propext]` |
| 2 | `self_composition_iff_2safety_ct` | Section 1 | `375–387` | `[propext]` |
| 3 | `lockstep_product_iff_ct_noninterference` | Section 2 | `517–527` | `[propext]` |
| 4 | `lockstep_product_quadratic_path_reduction` | Section 2 | `562–577` | `none` (0 axioms) |
| 5 | `taint_type_system_sound_for_ct` | Section 3 | `791–798` | `[propext]` |
| 6 | `relational_product_sound_for_ct` | Section 3 | `997–1008` | `[propext]` |
| 7 | `taint_typing_universal_inclusion_in_relational_product` | Section 3 | `1147–1156` | `[propext]` |
| 8 | `relational_product_strictly_subsumes_taint_typing` | Section 3 | `1180–1198` | `[propext]` |
| 9 | `conditioned_declassification_ct_soundness` | Section 4 | `1228–1234` | `[propext]` |
| 10 | `unguarded_declassification_launders_secret` | Section 4 | `1241–1248` | `[propext]` |
| 11 | `leakage_hierarchy_monotonic_inclusion` | Section 5 | `1478–1516` | `[propext]` |
| 12 | `val_ni_not_arch_ct` | Section 5 | `1554–1562` | `[propext]` |
| 13 | `arch_ct_not_vartime_ct_kyberslash` | Section 5 | `1576–1584` | `[propext]` |
| 14 | `kyberslash_barrett_replacement_restores_dmp_ct` | Section 5 | `1591–1595` | `[propext]` |
| 15 | `vartime_ct_not_spec_ct_spectre` | Section 5 | `1609–1621` | `[propext]` |
| 16 | `spectre_slh_fence_restores_dmp_ct` | Section 5 | `1627–1634` | `[propext]` |
| 17 | `spec_ct_not_dmp_ct_gofetch` | Section 5 | `1649–1657` | `[propext]` |
| 18 | `dmp_pointer_masking_blinding_soundness` | Section 5 | `1669–1677` | `[propext]` |
| 19 | `five_level_leakage_hierarchy_strict` | Section 5 | `1683–1693` | `[propext]` |
| 20 | `cache_line_preload_zero_leakage_within_line` | Section 6 | `1738–1744` | `[propext]` |
| 21 | `anneal_product_machine_wellformed_iff_all_prefix_ct` | Section 6 | `1975–1993` | `[propext]` |
| 22 | `anneal_leakage_contract_trust_policy_gate_soundness` | Section 6 | `2049–2072` | `[propext]` |
| 23 | `anneal_relational_ct_cert_checker_sound` | Section 6 | `2122–2130` | `[propext]` |
| 24 | `dit_mode_fails_on_exempt_div_or_m1m2_dmp` | Section 7 | `2299–2320` | `[propext]` |
| 25 | `dit_mode_upgrades_m3_dmp_when_div_free` | Section 7 | `2394–2428` | `[propext]` |
| 26 | `anneal_dit_hardware_generation_trust_policy_soundness` | Section 7 | `2447–2476` | `[propext]` |

### 2. Primary Source & Codebase Citations

- **Hyperproperties, Self-Composition, Product Programs & Security Type Systems**: Volpano, Smith & Irvine, JCS 1996 (`10.3233/JCS-1996-42-304`); Barthe, D'Argenio & Rezk, CSFW 2004 / MSCS 2011 (`10.1017/S0960129511000193`); Terauchi & Aiken, SAS 2005 (`10.1007/11547662_24`); Benton, POPL 2004 (`10.1145/964001.964003`); Clarkson & Schneider, JCS 2010 (`10.3233/JCS-2009-0393`); Barthe, Crespo & Kunz, CAV 2011 (`10.1007/978-3-642-22110-1_17`); Almeida et al. (`ct-verif`), USENIX Security 2016 (`imdea-software/verifying-constant-time`, commit `36e166781b0aa7398c12b335c7a4cd118b73568e`); Cauligi et al. (`FaCT`), PLDI 2019 (`10.1145/3314221.3314605`); Watt et al. (`CT-Wasm`), POPL 2019 (`10.1145/3290390`).
- **Hardware-Software Leakage Contracts & Microarchitectural Side Channels**: Guarnieri et al., IEEE S&P 2021 (`10.1109/SP40001.2021.00036`); Bernstein et al. (`KyberSlash`), IACR ePrint 2024/1049 (`https://kyberslash.cr.yp.to/`); Wang et al. (`Hertzbleed`), USENIX Security 2022 (`CVE-2022-23823`); Vicarte et al. (`Augury`), IEEE S&P 2022 (`10.1109/SP46214.2022.9833570`); Chen et al. (`GoFetch`), USENIX Security 2024 (`https://gofetch.fail/`); Doychev et al. (`CacheAudit`), USENIX Security 2013 / ACM TISSEC 2015 (`10.1145/2756550`).
- **Anneal Trusted Boundary**: `AeneasVerif/anneal` (commit `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, `trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`, `theory/Anneal/Refinement.lean`).

---

## Revalidation

Run the following commands from the package directory (`reports/side-channel-freedom-foundations-and-leakage-contracts-1996-2026/`) to revalidate all 26 mechanized theorems, axiom footprints, and empirical benchmark results:

```bash
# 1. Verify all 26 mechanized theorems and #print axioms outputs under Lean 4.34.1
lean support/SideChannelFoundationsAndContracts.lean

# 2. Re-run the empirical side-channel certificate verification benchmark probe
python3 support/side_channel_cert_probe.py
```
