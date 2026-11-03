# Compiler Constant-Time Preservation (`CompCert-CT`, `Jasmin`, Secret-Erasure), Kernel Context-Switch `Time Protection` (`seL4`), and Anneal's 7-Obligation Consumer-Bound Side-Channel-Free Ring-0 Admission Gate (2018–2026)

## Summary

Verifying that a kernel extension is constant-time and memory-safe at the source or bytecode level does not prevent secret leakage when compiled or JIT-lowered into Ring-0 native code, nor does verifying each extension's constant-time execution in isolation prevent cross-domain covert channels across kernel context switches. Standard functional-correctness compilers (`LLVM`/`Clang`, `rustc`, unmodified `CompCert`, and in-kernel bytecode JITs) preserve only architectural input-output semantics; they routinely rewrite branchless `cmov` or bitwise mask operations into secret-dependent branches (affecting up to `62.5%` of cryptographic primitives on `riscv64` and `43.8%` on `x86_64` under `Clang -O3`), eliminate post-computation secret-scrubbing stores as dead stores before `ret`, and spill secret-bearing virtual registers onto unscrubbed stack slots during register allocation. Furthermore, even if an extension satisfies constant-time instruction traces and scrubs its registers on normal `ret`, sequentially or preemptively scheduling a second extension on the same CPU core without microarchitectural state reset leaks secrets through shared `L1-D`/`L1-I`/`BPU`/`TLB` state, dirty cache-line writeback latency, or mid-execution timer preemption.

To close both compiler-induced and context-switch side-channel gaps, this report synthesizes `CompCert-CT` (POPL 2020), `Jasmin` (CCS 2017, POPL 2020, CCS 2023), Besson et al.'s Information-Flow-Preserving (`IFP`) secret-erasure passes (CSF 2019), and `seL4` `Time Protection` (EuroSys 2019) into a **7-obligation consumer-bound Ring-0 admission gate (`admitCtKernelExtension`)**, mechanized in Lean `v4.34.1` (`support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean`, 2,629 lines, **31 constructive theorems**, zero axioms `[]`). Rather than trusting an upstream compiler pass, the kernel loader checks a target-level constant-time and secret-erasure certificate (`ob7_sideChannelFreedom := ob7a_archConstantTime && ob7b_speculativeConstantTime && ob7c_secretExitAndSpillScrubbing && ob7d_secretIndependentFuelTiming`) directly against the decoded native machine bytes `req.candidate.bytes`. By pairing `ob6_boundedFuelTermination` (non-preemptible bounded-fuel execution within a timer tick) with `ob7c_secretExitAndSpillScrubbing` (8–12 cycle in-extension register and stack-spill zeroization before `ret`), synchronous Ring-0 extension calls achieve full 2-safety noninterference without paying the `14,800`–`15,300`-cycle penalty of a hardware `Time Protection` flush on every invocation (`265.24x` speedup for 100-cycle extensions on ARM Cortex-A9; `284.13x` on x86-64 Haswell), reserving full hardware partition flushes (`sel4TimeProtectedSwitch` / `timeProtectedPreemptIsr`) for cross-domain preemption boundaries.

| Architectural Layer | Vulnerability Mode in Standard Kernels / Compilers | Formal Mitigation Mechanism | Mechanized Lean 4 Witness (`CompilerPreservationTimeProtectionAndAnnealCtGate.lean`) |
| :--- | :--- | :--- | :--- |
| **Instruction Selection (`RTL` / `SelectionDAG`)** | Branchless `cmovSelectSec` or bitwise mask lowered to conditional branch (`branchSelectSec`) | `CompCert-CT` branchless `Selection` + target-byte `ob7a_archConstantTime` rejection | `cmov_to_branch_lowering_breaks_ct`, `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`, `drop_ob7a_unsound` |
| **Dead-Store Elimination (`DSE` / `DeadCode`)** | Secret-zeroizing store `scrubStackSlot 0` before `ret` deleted as architecturally dead | Besson et al. IFP `insert_erase` observable + target-byte `ob7c_secretExitAndSpillScrubbing` | `dead_store_elimination_breaks_secret_scrubbing`, `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`, `drop_ob7c_unsound` |
| **Register Allocation (`Allocation` / `Stacking`)** | Secret register spilled to `stack[0]` (`spillSecretRegToStack 0`) without zeroing the spill slot | Besson et al. tainted spill erasure (`bessonPatchedSpillPass`) + `ob7c` post-dominator check | `secret_register_spill_breaks_memory_erasure`, `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`, `drop_ob7c_unsound` |
| **Speculative Execution (`PHT` / `BTB` / `SLS`)** | Unmasked transient load (`specLoadUnmasked`) executed under branch misprediction (`oracle = true`) | `Jasmin` SCT `#msf` misspeculation masking + target-byte `ob7b_speculativeConstantTime` | `drop_ob7b_unsound`, `anneal_ob7_four_subobligations_necessary` |
| **Secret-Dependent Loop / Delay Count** | Secret-dependent step/cycle count (`secretFuelDelay`) with constant address trace | Target-byte `ob7d_secretIndependentFuelTiming` rejection | `drop_ob7d_unsound`, `anneal_ob7_four_subobligations_necessary` |
| **Sequential Extension Composition ($A ; B$)** | Extension $A$ leaves secret in scratch register, stack slot, or `L1-D`/`BPU`/dirty-line clock read by $B$ | `ob7c` pre-`ret` scrub + `seL4` `Time Protection` (`sel4TimeProtectedSwitch` + WCET padding) | `isolated_ct_insufficient_across_context_switch`, `unpadded_cache_flush_leaks_via_clock`, `sel4_time_protection_compositional_noninterference` |
| **Mid-Execution Timer Preemption** | Timer interrupt preempts extension at `preemptStep = 2` (after spill, before pre-`ret` scrub at `PC = 2..3`) | Non-preemptible tick-bounded fuel (`runBoundedTickNonPreemptible`) or PCB-saving `timeProtectedPreemptIsr` | `mid_execution_preemption_bypasses_exit_scrub`, `time_protected_isr_or_nonpreemptible_fuel_soundness` |

---

## Applicability

The findings and mechanized proofs in this report apply to:

1. **Consumer-Bound Native Machine-Code Certificate Checkers (`Anneal` and `Kraken`)**:
   - `AeneasVerif/anneal` (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, `rv64` backend `7677632ab267e6d7075fc9ddca7280ddf0296f87`, `x86_64` backend `3a89578`) and `AeneasVerif/kraken` (`8af78062037bc237b341d20252aafd1797c1bcb7` on `aarch64`), where an untrusted userspace toolchain emits a compiled binary image `req.candidate.bytes` together with a proof certificate checked by an in-kernel `CertChecker` prior to Ring-0 admission.
2. **Constant-Time & Secret-Erasing Compilers (`CompCert-CT`, `Jasmin`, and Besson et al. IFP)**:
   - `CompCert-CT` (Barthe et al., POPL 2020, DOI `10.1145/3371075`), which proves constant-time preservation across 18 passes of `CompCert` (`v3.0.1`) via lockstep leakage-preserving simulation (`CTSimulates`);
   - `Jasmin` (Almeida et al., CCS 2017 DOI `10.1145/3133956.3134078`, POPL 2020 DOI `10.1145/3371076`, CCS 2023 DOI `10.1145/3576915.3623157`), which provides Coq-verified compilation of high-speed cryptography with explicit programmer-controlled register spilling and Speculative Constant-Time (`SCT`) `#msf` protection;
   - Besson, Dang, Jensen & Pichardie (CSF 2019, DOI `10.1109/CSF.2019.00026`), which extends `CompCert` with Information-Flow-Preserving (`IFP`) secret-erasure passes that zeroize secret stack frames and register-allocator spill slots prior to function return.
3. **Kernel Context-Switch `Time Protection` (`seL4` EuroSys 2019)**:
   - Ge, Yarom, Cock & Heiser (EuroSys 2019, DOI `10.1145/3302424.3303976`), evaluated on `seL4` across ARM Cortex-A9 (Exynos 4412, 1.0 GHz) and x86-64 Haswell (Intel Core i7-4770, 3.4 GHz), establishing the OS abstraction of spatial cache coloring (`Kernel_Clone`) plus temporal partition reset (`L1-D`, `L1-I`, `BPU`, `TLB`, and worst-case dirty-line writeback padding) on domain switches.
4. **Mechanized Verification Environment**:
   - All 31 theorems in `support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean` are checked under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with zero axioms (`does not depend on any axioms`).

---

## Findings

### 1. Why Source/Bytecode Constant-Time Certificates Fail Under Functional Backend/JIT Lowering

Basis: normative specification + source + execution + derived (`support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean`, Section 1, lines 71–818; `support/ct_compiler_and_time_protection_probe_results.json`)

A standard functional-correctness compiler or in-kernel bytecode JIT guarantees only observational equivalence over architectural return values and final architecturally live memory:
$$\forall s,\; \text{retVal}(\text{runTgt}(T(P_{\text{src}}), s)) = \text{retVal}(\text{runSrc}(P_{\text{src}}, s))$$
Because neither the instruction-pointer (`PC`) trace, the memory-address trace, nor architecturally dead stack/register state after `ret` is observable in the standard C, Rust, or eBPF abstract machine, an unverified backend pass $T$ can satisfy 100% functional equivalence while destroying constant-time execution and secret erasure.

#### 1.1 Three Mechanized Compiler/JIT Optimization Counterexamples

In `support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean` (lines 71–530), we formalize a source/bytecode semantics (`runSrc`) and a target machine semantics (`runTgt`) tracking architectural return values (`retVal`), cumulative step leakage traces (`trace : List ObsEvent`, recording branch-condition and PC observations), and post-exit residual secrets in registers (`secReg`) and stack slots (`stackSlot0`). We define the composite security predicate `TargetCTAndScrubbed (P_tgt : TgtProg) : Prop`, requiring both 2-safety trace noninterference across all secret pairs `(s₁, s₂)` sharing public inputs and complete post-exit register/stack secret zeroization (`stackSlot0 = 0 ∧ secReg = 0`).

1. **`cmov_to_branch_lowering_breaks_ct` (lines 285–323)**:
   - **Mechanism**: The source program `P_cmov_src := [.cmovSelectSec, .ret]` selects between two values based on `s.secReg != 0` in constant time (`trace = [ObsEvent.pcStep 0, ObsEvent.pcStep 1]`). The backend pass `lowerCmovToBranch` lowers `.cmovSelectSec` to `.branchSelectSec` (modeling LLVM `X86CmovConversion` / `RISCVISD::SELECT_CC` diamond-branch lowering documented by Simon et al., EuroS&P 2018, and Schneider et al., ASIA CCS 2025).
   - **Mechanized Theorem**:
     ```lean
     theorem cmov_to_branch_lowering_breaks_ct :
         SourceCTAndScrubbed P_cmov_src ∧
         (∀ s : ExtInputState,
           (runTgt (lowerCmovToBranch P_cmov_src) s).retVal = (runSrc P_cmov_src s).retVal) ∧
         ¬ TargetCTAndScrubbed (lowerCmovToBranch P_cmov_src)
     ```
   - **Empirical Incidence**: Schneider et al. (ASIA CCS 2025, DOI `10.1145/3678890.3678916`) show that across constant-time cryptographic reference implementations, `Clang -O3` introduces secret-dependent branches or memory accesses in `43.8%` of primitives on `x86_64`, `37.5%` on `aarch64`, and `62.5%` on `riscv64` (where lack of a baseline integer `cmov` in unextended RV64GC forces `SelectInst` lowering into conditional `beq`/`bne` diamonds unless bitwise masks are preserved at the target ISA level).

2. **`dead_store_elimination_breaks_secret_scrubbing` (lines 352–390)**:
   - **Mechanism**: The source program `P_scrub_src := [.storeSecretToStack 0, .scrubStackSlot 0, .ret]` writes a temporary secret to `stack[0]` and explicitly scrubs `stack[0] := 0` before `.ret`. The backend Dead-Store Elimination pass (`dsePass`) strips `.scrubStackSlot 0` immediately preceding `.ret` because `stack[0]` is never read after `.ret` in the architectural return-value semantics.
   - **Mechanized Theorem**:
     ```lean
     theorem dead_store_elimination_breaks_secret_scrubbing :
         SourceCTAndScrubbed P_scrub_src ∧
         (∀ s : ExtInputState,
           (runTgt (dsePass P_scrub_src) s).retVal = (runSrc P_scrub_src s).retVal) ∧
         (runTgt (dsePass P_scrub_src) { pubIn := 10, secIn := 42 }).stackSlot0 = 42 ∧
         ¬ TargetCTAndScrubbed (dsePass P_scrub_src)
     ```

3. **`secret_register_spill_breaks_memory_erasure` (lines 422–460)**:
   - **Mechanism**: The source program `P_reg_only_src := [.computeInSecretReg, .scrubSecretReg, .ret]` performs secret computation purely in architectural registers and zeroes the secret register before returning—never touching memory at the source level. Under register pressure, the backend register allocator (`regAllocSpillPass`, modeling `CompCert`'s `Allocation` + `Stacking` passes) spills the secret register via `.spillSecretRegToStack 0` and reloads it before `.scrubSecretReg`, leaving a persistent copy of the secret in `stack[0]` (`stackSlot0 = 99`).
   - **Mechanized Theorem**:
     ```lean
     theorem secret_register_spill_breaks_memory_erasure :
         SourceCTAndScrubbed P_reg_only_src ∧
         (∀ s : ExtInputState,
           (runTgt (regAllocSpillPass P_reg_only_src) s).retVal = (runSrc P_reg_only_src s).retVal) ∧
         (runTgt (regAllocSpillPass P_reg_only_src) { pubIn := 5, secIn := 99 }).stackSlot0 = 99 ∧
         ¬ TargetCTAndScrubbed (regAllocSpillPass P_reg_only_src)
     ```

#### 1.2 Two Architectural Solutions: Verified Lockstep CT Simulation vs. Target-Byte Certificates

We mechanize and compare the two sound solutions to compiler-induced leakage:

1. **Compiler-Level Lockstep Leakage & Erasure Simulation (`CompCert-CT` + Besson et al. IFP)**:
   - In `CompCert-CT` (Barthe et al., POPL 2020), each compiler pass $P_{\text{src}} \mapsto P_{\text{tgt}}$ is equipped with a simulation relation augmented with step leakage equality $\mathcal{L}_{\text{tgt}}(s) = \mathcal{L}_{\text{src}}(s)$. Crucially, however, `CompCert-CT` (POPL 2020, §4.3) proves only that register-allocator spill slots reside at secret-independent stack offsets (preserving address-trace constant-time), **not** that secret values spilled to the stack are erased upon return.
   - Besson, Dang, Jensen & Pichardie (CSF 2019, DOI `10.1109/CSF.2019.00026`) close this gap via an Information-Flow-Preserving (`IFP`) taint analysis across `Linear`/`Mach` stack slots that injects explicit zeroizing stores (`Msetstack 0`) for every secret-tainted spill slot prior to `Lreturn` (`bessonPatchedSpillPass`).
   - We prove the general transfer theorem `ct_lockstep_simulation_preserves_ct_and_scrubbing` (lines 487–509) showing that `CTSimulates P_src P_tgt` transfers `SourceCTAndScrubbed P_src` to `TargetCTAndScrubbed P_tgt`.

2. **Consumer-Bound Target-Byte Certificate Verification (`Anneal` / `Kraken` / `Jasmin` Target Gate)**:
   - When an extensible OS kernel cannot place a 100,000-line optimizing C/Rust compiler inside its Ring-0 Trusted Computing Base (TCB), the kernel verifies the constant-time and secret-erasure certificate (`checkTargetByteCtAndScrubCert`) **directly on the decoded native machine instructions** at load time.
   - Theorem `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler` (lines 781–818, supported by inductive step invariants `stepTargetByteChecker_invariant` and `runTargetByteCheckerLoop_invariant`) proves that `checkTargetByteCtAndScrubCert` guarantees `TargetCTAndScrubbed` for every accepted binary, deterministically rejects all three broken compiler outputs (`lowerCmovToBranch P_cmov_src`, `dsePass P_scrub_src`, and `regAllocSpillPass P_reg_only_src`), and accepts the Besson-patched binary (`bessonPatchedSpillPass P_reg_only_src`).

---

### 2. Kernel Context-Switch & Domain-Exit Boundary: `seL4` `Time Protection` & Preemption Windows

Basis: normative specification + execution + derived (Ge et al., EuroSys 2019, DOI `10.1145/3302424.3303976`; `support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean`, Sections 2 and 4; `support/ct_compiler_and_time_protection_probe_results.json`)

#### 2.1 Why Isolated Constant-Time Extensions Leak Under Sequential Composition ($A ; B$)

Even if extension $A$ (`extA_residual`) and extension $B$ (`extB_observer`) each satisfy `IsolatedCT` when invoked from a clean microarchitectural baseline (`cleanMicroArchState baseClock`), executing $A$ followed by $B$ on the same CPU core in Ring 0 creates two compositional covert/side channels:

1. **Residual Scratch & Microarchitectural State (`isolated_ct_insufficient_across_context_switch`, lines 957–973)**:
   - Theorem `isolated_ct_insufficient_across_context_switch` proves that both `IsolatedCT extA_residual` and `IsolatedCT extB_observer` hold individually, yet under a naive context switch (`naiveContextSwitch`) that fails to scrub shared scratch/stack state and microarchitectural state between $A$ and $B$, `extB_observer`'s public output directly leaks `extA_residual`'s secret (`secA₁ = 0` vs. `secA₂ = 77`).
2. **Unpadded Dirty-Cache-Line Flush Latency (`unpadded_cache_flush_leaks_via_clock`, lines 980–993)**:
   - Even if the kernel zeroes `scratchRegs`, `sharedStack`, `cacheState`, and `bpuState` on context switch (`unpaddedFlushSwitch`), flushing `L1-D` writes dirty cache lines back to `L2`/DRAM. On ARM Cortex-A9 (1.0 GHz), an `L1-D` flush takes `3.9 µs` (`3,900` cycles) when all lines are clean vs. `10.9 µs` (`10,900` cycles) when all lines are dirty—a **`7,000`-cycle timing channel** (`1,020` cycles on Haswell) that reveals how many cache lines the outgoing domain modified!
   - Theorem `unpadded_cache_flush_leaks_via_clock` proves that even when `muB.cacheState = 0 ∧ muB.bpuState = 0 ∧ muB.scratchRegs = 0 ∧ muB.sharedStack = 0`, `unpaddedFlushSwitch` leaks Domain $A$'s secret to Domain $B$ through `mu.cycleClock`.

#### 2.2 `seL4` `Time Protection` Mechanics & Multi-Extension Schedule Noninterference

Ge et al. (EuroSys 2019) demonstrate that temporal isolation requires four coordinated OS mechanisms at every cross-domain switch (`sel4TimeProtectedSwitch`, lines 906–912):
1. **Spatial LLC/DRAM Partitioning + Cloned Kernel Text (`Kernel_Clone`)**: Off-core Last-Level Cache (`LLC`) ways/sets are partitioned by page coloring, and each security domain executes its own colored copy of the kernel text/read-only data and stack (`Kernel_Clone`) so one domain cannot evict another domain's kernel instructions from the LLC to infer kernel control flow.
2. **On-Core Microarchitectural State Reset**: On a domain switch, the kernel flushes the uncore-uncolorable on-core state: `L1-D`, `L1-I`, `BPU` (`IBPB` on x86-64 / `BPIALL` on ARMv7), and `TLB`/`ASID` (`invpcid` / `TLBIALL`).
3. **Worst-Case Dirty-Line Writeback Padding**: The kernel reads the hardware cycle counter after the flush and busy-waits until `baseClock + worstCaseBudget` (`14,800` cycles on Cortex-A9; `15,300` cycles on Haswell) expires.
4. **Compositional and Schedule-Wide Noninterference Theorems**:
   - `sel4_time_protection_compositional_noninterference` (lines 1003–1012) proves that interposing `sel4TimeProtectedSwitch` between any extension `extA` and any observer `extB` renders `muB` and `extB.runDom` 100% invariant across any secrets `(secA₁, secA₂)`.
   - `sel4_time_protection_schedule_noninterference` (lines 1034–1053) proves by induction over arbitrary $k$-extension schedules `s₁, s₂ : List (DomExtension × Nat)` (`s₁.length = s₂.length`) that replacing all $k$ domain secrets leaves the resulting post-switch `MicroArchState` 100% invariant.

#### 2.3 Mid-Execution Timer Preemption Window vs. Bounded Non-Preemptible Fuel / ISR `Time Protection`

A critical interaction arises between static pre-`ret` scrubbing (`ob7c_secretExitAndSpillScrubbing`) and preemptive kernel scheduling (Ge et al., EuroSys 2019, §4.5):
- Consider the valid extension `goodScrubbedProg := [.aluSecret, .storeStackSecretSpill 0, .scrubScratchRegs, .scrubStackSlot 0, .ret]` (`fuelBound = 5`), which passes all 7 obligations of `admitCtKernelExtension`.
- At full completion (`fuel = 5`), `ob7c` guarantees `residualRegSecret = 0 ∧ residualStackSecret = 0`. However, at `preemptStep = 2` (after `.aluSecret` and `.storeStackSecretSpill 0`, before `.scrubScratchRegs` and `.scrubStackSlot 0`), both the live register and stack spill slot transiently hold the raw secret (`42`).
- In Section 4 of `support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean` (lines 2399–2594), we prove two theorems governing this window:
  1. **`mid_execution_preemption_bypasses_exit_scrub` (lines 2445–2459)**:
     Proves that `(goodScrubbedReq, goodScrubbedCert)` satisfies `admitCtKernelExtension goodScrubbedReq goodScrubbedCert = true` and zeroes `residualRegSecret = 0 ∧ residualStackSecret = 0` at full completion (`fuel = 5`), yet if preempted by a timer interrupt at `preemptStep = 2` without ISR scrubbing, exposes live secrets `residualRegSecret = 42 ∧ residualStackSecret = 42`.
  2. **`time_protected_isr_or_nonpreemptible_fuel_soundness` (lines 2543–2593)**:
     Proves that 2-safety noninterference and zero residual secret exposure across the domain boundary are preserved under either of two disciplined kernel execution regimes:
     - **Discipline (i) — Non-Preemptible Bounded-Fuel Execution (`runBoundedTickNonPreemptible`)**: When the extension's certified fuel bound fits within the remaining timer tick (`natLe cert.fuelBound maxTickBudget = true`, matching `ob5_irqDiscipline` + `ob6_boundedFuelTermination`), the kernel masks preemption until `ret`, allowing the extension's own `ob7c` post-dominator instructions to zeroize all secret registers and stack slots in `8–12` cycles without a domain switch.
     - **Discipline (ii) — Time-Protected Preemptive ISR (`timeProtectedPreemptIsr`)**: When a timer interrupt preempts a domain at any step `preemptStep`, the kernel ISR saves the interrupted register and stack-spill frame into the outgoing domain's private colored PCB (`SavedDomainPcb`), zeroizes the CPU's live architectural registers and shared scratch stack (`nextDomainCpuState`), and executes `sel4TimeProtectedSwitch` (`nextDomainMu`) before dispatching the incoming domain.

---

### 3. Anneal's 7-Obligation Consumer-Bound Side-Channel-Free Ring-0 Admission Gate

Basis: source + execution + derived (`support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean`, Section 3, lines 1056–2397; `support/ct_compiler_and_time_protection_probe_results.json`)

Building on the 6-obligation functional/safety Ring-0 admission gate (`ob1_byteBinding` through `ob6_boundedFuelTermination`), Section 3 of `support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean` defines the **7-obligation consumer-bound side-channel-free admission checker (`admitCtKernelExtension`)**:

```lean
def ob7_sideChannelFreedom (prog : List CtRing0Instr) : Bool :=
  ob7a_archConstantTime prog &&
  ob7b_speculativeConstantTime prog &&
  ob7c_secretExitAndSpillScrubbing prog &&
  ob7d_secretIndependentFuelTiming prog

def admitCtKernelExtension (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  ob1_byteBinding req cert &&
  ob2_privilegeSafety cert.decodedProg &&
  ob3_helperContract req.allowedHelpers cert.decodedProg &&
  ob4_abiPreservation cert.decodedProg &&
  ob5_irqDiscipline cert.decodedProg &&
  ob6_boundedFuelTermination cert &&
  ob7_sideChannelFreedom cert.decodedProg
```

where `ob7_sideChannelFreedom` decomposes into four orthogonal, consumer-checked target-byte sub-obligations:
1. **`ob7a_archConstantTime`**: Verifies on the decoded target instruction stream that no secret-dependent branch (`branchSecret`) or variable-latency secret ALU instruction (`varTimeDivSecret`) occurs.
2. **`ob7b_speculativeConstantTime`**: Verifies that every memory load is either public (`loadPublic`) or speculatively masked in-bounds (`specLoadMasked`), rejecting unmasked transient loads (`specLoadUnmasked`) that leak secrets under branch misprediction (`oracle = true`).
3. **`ob7c_secretExitAndSpillScrubbing`**: Performs a forward taint/post-dominator check (`checkScrubLoop`) over the decoded target instructions ensuring that every instruction tainting a scratch register (`aluSecret`, `varTimeDivSecret`) or stack spill slot (`storeStackSecretSpill slot`) is overwritten by a corresponding zeroizing instruction (`scrubScratchRegs`, `scrubStackSlot slot`) before `.ret`.
4. **`ob7d_secretIndependentFuelTiming`**: Verifies that no instruction introduces secret-dependent step/cycle delays (`secretFuelDelay`) that alter `stepsTaken` without emitting an address or branch event.

#### 3.1 Master Sufficiency and 4-Way Sub-Obligation Necessity

- **Master Sufficiency (`anneal_ring0_ct_extension_admission_soundness`, lines 2184–2231)**: Proves via the inductive loop invariant `runCtProgWithFuel_soundness_loop` (lines 1711–2170) that any `(req, cert)` satisfying `admitCtKernelExtension req cert = true` executes on the raw bytes `req.candidate.bytes` with:
  1. Zero faults and guaranteed termination (`faulted = false ∧ halted = true`);
  2. Ring-0 privilege, ABI callee-saved preservation, and unmasked exit IRQs (`ringLevel = 0 ∧ calleeSaved = calleeSaved ∧ irqMasked = false`);
  3. Architectural 2-safety constant-time (`out₁.archObsTrace = out₂.archObsTrace`);
  4. Speculative 2-safety constant-time (`out₁.specObsTrace = out₂.specObsTrace`);
  5. Complete post-exit secret erasure (`residualRegSecret = 0 ∧ residualStackSecret = 0`); and
  6. Total execution step/fuel noninterference (`out₁.stepsTaken = out₂.stepsTaken`).
- **4-Way Sub-Obligation Necessity (`anneal_ob7_four_subobligations_necessary`, lines 2381–2396)**: Proves via `drop_ob7a_unsound`, `drop_ob7b_unsound`, `drop_ob7c_unsound`, and `drop_ob7d_unsound` that dropping any single sub-obligation while keeping `ob1`–`ob6` and the other three `ob7` sub-obligations intact admits a concrete binary (`badReq7a`–`badReq7d`) that violates the corresponding security property while satisfying the remaining three.

#### 3.2 Quantitative Overhead: Per-Call Hardware `Time Protection` Flush vs. Hybrid `ob6 + ob7c` Execution

Using the hardware cycle measurements from Ge et al. (EuroSys 2019, Table 1 & §5.2) and our empirical probe (`support/ct_compiler_and_time_protection_probe.py`), the table below compares **Strategy A** (executing a full hardware `seL4` `Time Protection` flush on every Ring-0 extension call and return: $2 \times 14{,}800 = 29{,}600$ cycles on ARM Cortex-A9; $2 \times 15{,}300 = 30{,}600$ cycles on x86-64 Haswell) against **Strategy B** (Anneal's hybrid architecture: running synchronous extensions non-preemptibly within a timer tick under `ob6_boundedFuelTermination`, executing an `8–12`-cycle in-extension `ob7c` register/stack-spill scrub before `ret`, and paying the `Time Protection` hardware flush only once per `10 ms` timer-tick domain switch):

| Extension Execution Cycles | Cortex-A9 (1.0 GHz) Per-Call Full Flush Overhead | Cortex-A9 Hybrid (`ob6 + ob7c` + 10 ms Tick) Overhead | Cortex-A9 Hybrid Speedup | Haswell (3.4 GHz) Per-Call Full Flush Overhead | Haswell Hybrid (`ob6 + ob7c` + 10 ms Tick) Overhead | Haswell Hybrid Speedup |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`100` cycles** (BPF packet filter) | `29,600.0%` (`29,600` cyc) | **`12.15%`** (`12.15` cyc) | **`265.24x`** | `30,600.0%` (`30,600` cyc) | **`8.04%`** (`8.04` cyc) | **`284.13x`** |
| **`1,000` cycles** (crypto block / hash) | `2,960.0%` (`29,600` cyc) | **`1.35%`** (`13.48` cyc) | **`30.19x`** | `3,060.0%` (`30,600` cyc) | **`0.84%`** (`8.45` cyc) | **`31.34x`** |
| **`10,000` cycles** (batch capability check) | `296.0%` (`29,600` cyc) | **`0.27%`** (`26.80` cyc) | **`3.95x`** | `306.0%` (`30,600` cyc) | **`0.12%`** (`12.50` cyc) | **`4.05x`** |
| **`100,000` cycles** (long syscall handler) | `29.6%` (`29,600` cyc) | **`0.16%`** (`160.00` cyc) | **`1.29x`** | `30.6%` (`30,600` cyc) | **`0.05%`** (`53.00` cyc) | **`1.31x`** |
| **`1,000,000` cycles** (1 ms compute slice) | `2.96%` (`29,600` cyc) | **`0.15%`** (`1,492.00` cyc) | **`1.03x`** | `3.06%` (`30,600` cyc) | **`0.05%`** (`458.00` cyc) | **`1.03x`** |

When an extension shares the same security domain as its caller (e.g., a tenant-specific packet filter or storage validator invoked synchronously on that tenant's packet/request), `ob6_boundedFuelTermination` + `ob7c_secretExitAndSpillScrubbing` eliminates residual secrets in shared CPU registers and kernel stack slots in `8–12` cycles, while `ob7a` + `ob7b` + `ob7d` ensures the extension's own cache/branch-predictor footprint and step count are secret-independent. A full hardware `Time Protection` flush (`14,800`–`15,300` cycles) is required **only** when switching between mutually distrusting security domains or when a timer interrupt preempts a domain mid-execution (`timeProtectedPreemptIsr`).

---

## Boundaries

1. **Hardware Data-Independent Timing Mode (`known not to apply` if hardware errata violate constant-latency ALU execution)**:
   - `ob7a_archConstantTime` rejects variable-latency division instructions (`varTimeDivSecret`) and secret branches (`branchSecret`), assuming that remaining integer ALU instructions execute in data-independent time. On processors where data-dependent timing optimizations exist for integer or vector instructions unless architectural control bits are set (such as ARMv8.4-A `DIT` or Intel `IA32_UARCH_MISC_CTL.DOIT`), the kernel must set `DIT`/`DOIT` prior to Ring-0 extension entry.
2. **Simultaneous Multithreading / Hyperthreading (`known not to apply` across sibling hardware threads)**:
   - As established by Ge et al. (EuroSys 2019, §3.2 & §6), temporal flushing of `L1-D`, `L1-I`, `BPU`, and `TLB` at context switches cannot prevent concurrent contention channels between two hardware threads (SMT / Hyperthreading) executing simultaneously on the same physical core. `Time Protection` requires either disabling SMT or co-scheduling only threads belonging to the same security domain on sibling hardware threads.
3. **Bus, Interconnect, and DRAM Row-Buffer Contention (`not examined` in Lean 4 model)**:
   - While `seL4` `Time Protection` partitions the Last-Level Cache (`LLC`) via page coloring, residual contention on the memory controller and DRAM row buffers is bounded empirically by Ge et al. (EuroSys 2019) rather than eliminated statically by `ob7a`–`ob7d`.

---

## Evidence

### 1. Primary Literature and Repositories

- **Barthe et al. (`CompCert-CT`, POPL 2020)**: Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David Pichardie, and Alix Trieu, *Formal Verification of a Constant-Time Preserving C Compiler*, Proc. ACM Program. Lang. 4 (POPL), Article 7, 2020, DOI `10.1145/3371075`. Establishes lockstep constant-time simulation (`CTSimulates`) across 18 `CompCert` passes and documents the `Allocation`/`Stacking` spill-slot challenge (§4.3).
- **Almeida et al. (`Jasmin`, CCS 2017 / POPL 2020 / CCS 2023)**:
  - José Bacelar Almeida et al., *Jasmin: High-Assurance and High-Speed Cryptography*, CCS 2017, DOI `10.1145/3133956.3134078`.
  - José Bacelar Almeida et al., *The Last Mile: High-Assurance and High-Speed Cryptographic Implementations*, POPL 2020, DOI `10.1145/3371076`.
  - José Bacelar Almeida et al., *Formally Verifying that Speculative Constant-Time is Preserved by Compilation*, CCS 2023, DOI `10.1145/3576915.3623157`.
- **Besson et al. (CSF 2019)**: Frédéric Besson, Alexandre Dang, Thomas Jensen, and David Pichardie, *Information-Flow Preservation in Compiler Optimisations and Register Spilling*, IEEE CSF 2019, DOI `10.1109/CSF.2019.00026`. Formalizes post-return secret memory erasure (`insert_erase`) and secret-tainted spill-slot zeroization in `CompCert`.
- **Simon, Chisnall & Anderson (EuroS&P 2018)**: Laurent Simon, David Chisnall, and Ross Anderson, *What You Get is What You C: Controlling Side Effects in Mainstream C Compilers*, IEEE EuroS&P 2018, DOI `10.1109/EuroSP.2018.00029`. Demonstrates how `Clang`/`GCC` dead-store elimination and branch lowering break constant-time C code and stack scrubbing.
- **Schneider, Lain, Ivan & Puddu (ASIA CCS 2025)**: Moritz Schneider, Daniele Lain, Luka Ivan, and Ivan Puddu, *Breaking Bad: How Compilers Break Constant-Time Implementations*, ACM ASIA CCS 2025, DOI `10.1145/3678890.3678916`. Quantifies constant-time violations across `LLVM`/`Clang`, `GCC`, and `rustc` across `x86_64`, `aarch64`, and `riscv64`.
- **Ge, Yarom, Cock & Heiser (`seL4` `Time Protection`, EuroSys 2019)**: Qian Ge, Yuval Yarom, David Cock, and Gernot Heiser, *Time Protection: The Missing OS Abstraction*, EuroSys 2019, DOI `10.1145/3302424.3303976`. Defines OS-level `Time Protection` (`Kernel_Clone`, cache coloring, on-core `L1-D`/`L1-I`/`BPU`/`TLB` flushing, dirty-line writeback padding, and timer-tick alignment).
- **Anneal & Kraken Repositories**: `AeneasVerif/anneal` (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and `AeneasVerif/kraken` (`8af78062037bc237b341d20252aafd1797c1bcb7`).

### 2. Preserved Support Artifacts in This Package

1. **[`support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean`](support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean)** (`SHA-256: 0c938c519b35f40c85a09cee169aa3c607804c17003044cd12e104aab1e6ea0e`):
   - Self-contained, 2,629-line Lean `v4.34.1` mechanization proving **31 constructive theorems** with **zero axioms** (`[]`), organized into four sections:
     - **Section 1 (lines 71–818)**: Source and target semantics with step-leakage traces and residual register/stack secret tracking; proofs of `cmov_to_branch_lowering_breaks_ct`, `dead_store_elimination_breaks_secret_scrubbing`, `secret_register_spill_breaks_memory_erasure`, `ct_lockstep_simulation_preserves_ct_and_scrubbing`, `stepTargetByteChecker_invariant`, `runTargetByteCheckerLoop_invariant`, and `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`.
     - **Section 2 (lines 820–1054)**: Compositional multi-extension execution model and `seL4` `Time Protection` semantics; proofs of `isolated_ct_insufficient_across_context_switch`, `unpadded_cache_flush_leaks_via_clock`, `sel4_time_protection_compositional_noninterference`, and `sel4_time_protection_schedule_noninterference`.
     - **Section 3 (lines 1056–2397)**: Anneal's 7-obligation consumer-bound Ring-0 admission gate (`admitCtKernelExtension`); proofs of `ctInstrEq_eq`, `ctProgEq_eq`, `optionCtProgEq_eq`, `halted_runCtProgWithFuel`, `runCtProgWithFuel_soundness_loop`, `anneal_ring0_ct_extension_admission_soundness`, `drop_ob7a_unsound`, `drop_ob7b_unsound`, `drop_ob7c_unsound`, `drop_ob7d_unsound`, and `anneal_ob7_four_subobligations_necessary`.
     - **Section 4 (lines 2399–2594)**: Step-indexed mid-execution timer preemption window model; proofs of `mid_execution_preemption_bypasses_exit_scrub` and `time_protected_isr_or_nonpreemptible_fuel_soundness`.
2. **[`support/ct_compiler_and_time_protection_probe.py`](support/ct_compiler_and_time_protection_probe.py)** (`SHA-256: 81e2f91f6e28522d6267a88ac21f0fca72504fd028b62669bb8bbeb0fc8e36a7`) and **[`support/ct_compiler_and_time_protection_probe_results.json`](support/ct_compiler_and_time_protection_probe_results.json)** (`SHA-256: e766a131fdc4868601f4b9af24b0233d8ac7edec059811ec5ca716ce7dc79c86`):
   - Deterministic Python probe cataloging compiler-induced side-channel hazards, verifying the 10-check single-fault rejection matrix of `admitCtKernelExtension`, and computing amortised cycle overheads of per-call hardware `Time Protection` flushing vs. hybrid `ob6 + ob7c` execution across ARM Cortex-A9 and x86-64 Haswell.

---

## Revalidation

To revalidate the mechanized Lean 4 proofs and regenerate the empirical probe results from the repository root:

```bash
# 1. Verify all 31 constructive theorems in Lean v4.34.1 (must exit 0 with zero axioms)
lean reports/compiler-preservation-time-protection-and-anneal-ct-certificates-2018-2026/support/CompilerPreservationTimeProtectionAndAnnealCtGate.lean

# 2. Regenerate the empirical compiler-leakage and Time Protection cycle-cost JSON
python3 reports/compiler-preservation-time-protection-and-anneal-ct-certificates-2018-2026/support/ct_compiler_and_time_protection_probe.py
```

Expected output of step 1: `31` lines of `'CompilerPreservationTimeProtectionAndAnnealCtGate.<theorem>' does not depend on any axioms`, zero warnings, and exit status `0`.
