# Observable Behavior, Property Transfer Across Refinement Notions, and Anneal's Statement Forms

## Summary

Proving a property about a Rust crate's `Runtime(PostCleanup)` Mid-level Intermediate Representation (MIR) in Anneal guarantees that the compiled machine-code binary inherits that property only if the compiler's refinement theorem preserves that property class. By analyzing five candidate compilation refinement notions—(1) **Forward Simulation (`FSim`)**, (2) **Demonic Safe-Source Backward Simulation (`Compiles` over `EventualBehaviorOf`)**, (3) **Miracle-Free Eventual Refinement (`ProductiveCompiles`)**, (4) **Resource-Bounded Refinement (`ResourceBSim` / CakeML `extend_with_resource_limit`)**, and (5) **Lockstep Leakage-Preserving Refinement (`CTCompiles` / `CompCert-CT` / `Jasmin`)**—and cataloging all ten statement forms in Anneal (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc` and `5fc1139f2208b3c9cfb513573c4a731cc32bb457`), we establish four governing results, mechanized in Lean `v4.34.1` ([`support/PropertyTransferAndAnnealClaimsProbe.lean`](support/PropertyTransferAndAnnealClaimsProbe.lean), 356 lines, zero `sorryAx`):

1. **Exact Property-Transfer Hierarchy Across Refinement Notions:**
   - **Forward simulation (`FSim`)** transfers existential reachability (`ProductiveOn`) on deterministic programs, but fails to transfer universal safety (`defined`), functional postconditions (`ContractPost`), or termination on nondeterministic targets unless inverted to a backward simulation via target determinacy and source receptiveness.
   - **Unproductive demonic refinement (`Compiles` alone)** transfers all-prefix safety (`defined`) and partial-correctness postconditions (`SafetyPost`, `ContractPost`), but fails to transfer `Language.ProductiveOn` (and therefore `Language.Verified`) if the target transition system can get vacuously stuck or miraculous on queries outside the codec's image (`productiveCompiles_rejects_query_slack_miracle`).
   - **Miracle-free eventual refinement (`ProductiveCompiles` over `EventualBehaviorOf`)** transfers the entire Anneal `Language.Verified` judgment—including static well-formedness (`wf`), miracle-freedom (`ProductiveOn`), all-prefix UB-freedom (`defined`), return-value validity (`SafetyPost`), conditional functional correctness (`ContractPost` / `EffectivePost`), and total termination (`TerminatesPost`, ruling out both silent `.diverges` and reactive `.reacts`)—as proved in `productiveCompiles_transfers_verified` and `productiveCompiles_transfers_termination`.
   - **Resource-bounded refinement (`ResourceBSim` / CakeML `extend_with_resource_limit`)** transfers partial-correctness safety (`SafetyPost` and `ContractPost` conditioned on normal return), but **fails** to transfer total termination (`resource_refinement_transfers_partial_safety_but_not_termination`) unless paired with a quantitative stack/heap bound (`stackUsage <= maxStack <= headroom`).
   - **2-Safety Hyperproperties (`ConstantTimeOn`, secret erasure, and possibilistic noninterference)** **fail to transfer** even under `ProductiveCompiles` (`productiveCompiles_fails_constant_time_transfer`, an instance of McLean's 1994 Refinement Paradox where standard compilation refines unconstrained microarchitectural step traces into secret-dependent branches or unzeroed stack spills). Transferring 2-safety claims requires **`CTCompiles`** (augmenting `ProductiveCompiles` with lockstep leakage-trace preservation, proved in `ctCompiles_transfers_verified_and_constant_time`) or a consumer-bound target-byte constant-time certificate checker.
2. **Observable Events and Fault/Resource Disposition Across Precedents:**
   - Verified compilers agree on treating OS system calls, volatile memory loads/stores, and process exit codes as observable events, while treating out-of-bounds memory accesses, division by zero (in C/Rust), unaligned accesses, and data races as source Undefined Behavior (`Goes_wrong` / `.failed`) that a compiler may exploit as a wildcard on unsafe inputs.
   - However, precedents diverge sharply on **stack overflow** and **out-of-memory (OOM)**: CompCert 3.18 leaves both unmodeled (`Mem.alloc` is infinite); CakeML models both via `Resource_limit_hit` in `extend_with_resource_limit`; and Stack-Aware CompCert (`ssrg-vt/compcert_stack_aware@0518d9ffb69ec11e79a214df1afc0b0159930478`), Bedrock2 (`FitsStack.v`), and Jasmin rule out stack overflow statically via a concrete stack-pointer headroom precondition (`stack_usage <= StackSize`).
3. **Complete Classification of Anneal's Ten Statement Forms (`SF-01`..`SF-10`):**
   Every claim proved by `Trusted.CrateTheorem` (`SF-01` through `SF-10` in [`support/anneal_claim_transfer_matrix.json`](support/anneal_claim_transfer_matrix.json)) is mapped to its exact binary inheritance status and required side conditions under each refinement notion.

## Applicability

This report applies to:
1. **Anneal (`joshlf/anneal` at commits `9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`, `24367bd1a8c784f2578535954f9915e24894a56f`, and `5fc1139f2208b3c9cfb513573c4a731cc32bb457`)**: `DOCS` (`docs/design.md`, `docs/architecture.md`, `docs/trust-model.md`, `THREAT_MODEL.md`), `trusted/audit/TrustedBoundary.lean`, and the core refinement and MIR semantic definitions (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `theory/Anneal/Refinement.lean`, reproduced self-contained in Section 3 and [`support/PropertyTransferAndAnnealClaimsProbe.lean`](support/PropertyTransferAndAnnealClaimsProbe.lean)).
2. **Rust (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`) and The Rust Reference (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`)**.
3. **Precedent Verified Compilers**: CompCert 3.18 (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`), Stack-Aware CompCert (`ssrg-vt/compcert_stack_aware@0518d9ffb69ec11e79a214df1afc0b0159930478`), CakeML (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`), `CompCert-CT` (POPL 2020), and Jasmin (`jasmin-lang/jasmin@34f15840f10625bbc2cbf59b3d877e94c75bfbd9`).
4. **Mechanized Verification Environment**: Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Property Transfer Under Candidate Refinement Notions

Basis: source + execution + derived ([`support/PropertyTransferAndAnnealClaimsProbe.lean`](support/PropertyTransferAndAnnealClaimsProbe.lean), [`support/anneal_claim_transfer_matrix.json`](support/anneal_claim_transfer_matrix.json)).

| Property Class | Forward Simulation (`FSim`) | Step-Truncated Prefix Refinement (`PrefixSim` with unconstrained $\pi$) | Demonic Safe-Source Refinement (`Compiles` over `EventualBehaviorOf`) | Miracle-Free Eventual Refinement (`ProductiveCompiles`) | Resource-Bounded Refinement (`CakeML` `extend_with_resource_limit`) | Lockstep Leakage Refinement (`CTCompiles` / `CompCert-CT` / `Jasmin`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **1. All-Prefix Safety / UB-Freedom (`defined`)** | No (unless target is deterministic) | No (vulnerable to $\pi_{\text{boundedFuel}}$ late-UB masking) | **Yes** | **Yes** (`productiveCompiles_transfers_verified`) | **Yes** (early OOM/StackOverflow is a defined halt, not UB) | **Yes** |
| **2. Miracle-Freedom (`ProductiveOn`)** | **Yes** | No | No (fails on query slack) | **Yes** (`productiveCompiles_transfers_verified`) | **Yes** | **Yes** |
| **3. Partial Functional Postconditions (`SafetyPost`, `ContractPost` on normal return)** | No (unless flipped to backward) | **Yes** (if $\pi$ preserves terminal values) | **Yes** | **Yes** (`productiveCompiles_transfers_verified`) | **Yes** (`resource_refinement_transfers_partial_safety...`) | **Yes** |
| **4. Total Termination & Liveness (`¬ .diverges`, `.reacts`)** | No | No (vulnerable to $\pi_{\text{stepZero}}$ `loop: jmp loop`) | **Yes** (when target is productive) | **Yes** (`productiveCompiles_transfers_termination`) | **No** (unless paired with quantitative stack/heap bound $\le \text{headroom}$) | **Yes** |
| **5. Spatial Memory Frame & Callee-Saved Preservation** | No | No | Needs `FramedCodec` + `PartitionedFrameLayout` | **Yes** (with `FramedCodec` + `PartitionedFrameLayout`) | **Yes** (with `FramedCodec`) | **Yes** |
| **6. 2-Safety Constant-Time & Secret Erasure (`ConstantTimeOn`)** | No | No | **No** (McLean's Paradox) | **No** (`productiveCompiles_fails_constant_time_transfer`) | **No** | **Yes** (`ctCompiles_transfers_verified_and_constant_time`) |
| **7. Quantitative Stack/Heap Usage Bounds** | No | No | No (source `localCount` $\ne$ target spill/padding bytes) | Requires quantitative `Stacking` certificate $\mathcal{S}(f) \le B$ | Requires quantitative bound $\le \text{headroom}$ | **Yes** (when paired with `Stacking` bound) |

---

### 2. What Precedents Count as Observable Events & How Stack Overflow and Out-of-Memory Are Treated

Basis: normative specification + source (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` `common/Events.v`, `common/Behaviors.v`; `ssrg-vt/compcert_stack_aware@0518d9ffb69ec11e79a214df1afc0b0159930478`; `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c` `semantics/ffi/ffiScript.sml`; `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

| Phenomenon | CompCert 3.18 | Stack-Aware CompCert (`POPL 2019`) | CakeML | Bedrock2 (`riscv-coq`) | Rust Reference & Anneal (`MirSemantics.lean`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **External / OS Calls** | Observable `Event_syscall name args res` (`Events.v:53`) | Observable `Event_syscall` + stack budget check | Observable `io_event` via `call_FFI` (`ffiScript.sml`) | Observable MMIO `trace` event via `ext_spec` | Modeled via callee `BodyId` / `OpenModule` contract or `Obs` event |
| **Volatile Memory Accesses** | Observable `Event_vload` / `Event_vstore` (`Events.v:54-55`) | Observable `Event_vload` / `Event_vstore` | Modeled via FFI/MMIO calls | Modeled via `nonmem_load` / `nonmem_store` MMIO events | `read_volatile` / `write_volatile` emit ordered trace observations |
| **Inline Assembly (`asm!`)** | Observable `Event_annot` (`EF_inline_asm`, `Events.v:56`); memory effects constrained by `extcall_properties` | Same + declared stack delta | N/A (compiler emits all target code) | Verified as RISC-V instruction sequence | Modeled via ISA bridge (`ensuresN_safety_refines_anneal_specOn`) or explicit `TCBItem` waiver |
| **Hardware Faults & Traps (Div-by-Zero, OOB/Unmapped Load)** | **Source UB (`Goes_wrong`)**: compiler assumes safe source programs never divide by zero or dereference invalid pointers | Same | Checked dynamically in ML (`Division` exception) or proved absent by type safety (`~Fail`) | Source `exec` requires proof that divisor $\ne 0$ and address is in separation-logic domain | **Explicit MIR checks (`Terminator.assert` -> `.unwind`) vs. unchecked UB (`.failed`)**: checked division panics cleanly (`.unwind`); unchecked OOB/invalid deref steps to `.failed` (`defined = False`) |
| **Exit Status / Unwind / Abort** | Observable `Terminates trace exit_code` | Observable `Terminates trace exit_code` | Observable `Terminate Success io_list` | `runsTo` postcondition on final `RiscvMachine` state | Distinguished by `TerminationKind`: `.normal ret`, `.unwind` (panic), `.abort`, `.compileTimeError` (`StepResult.lean:203-207`) |
| **Stack Overflow** | **Unmodeled** (`Mem.alloc` never fails; infinite blocks) | **Explicitly prevented** when `stack_usage(p) <= StackSize` (`0 <= StackSize <= Ptrofs.max_unsigned`) | **Allowed as early abort** (`Terminate Resource_limit_hit io_list`) | **Explicitly prevented** by `FitsStack.v` (`required_stack_space <= stack_pastend - stack_start`) | Guard-page trap via `__rust_probestack` at runtime; total binary transfer requires static frame bound $\mathcal{S}(f) \le \text{headroom}$ |
| **Out-of-Memory (Heap OOM)** | **Unmodeled** (`malloc` modeled as external call) | Unmodeled for heap (stack only) | **Allowed as early abort** (`Terminate Resource_limit_hit io_list` in GC) | No implicit heap allocation (explicit caller-supplied memory buffers) | Explicit allocator outcome (`Result::Err(AllocError)` or defined `.abort` via `handle_alloc_error`) |

---

### 3. Catalog of Anneal's Statement Forms and Binary Inheritance Classification

Basis: source + execution (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`, `docs/design.md`, `docs/architecture.md`, `docs/trust-model.md`, `THREAT_MODEL.md`, and the self-contained Lean 4 definitions in [`support/PropertyTransferAndAnnealClaimsProbe.lean`](support/PropertyTransferAndAnnealClaimsProbe.lean) and [`support/anneal_claim_transfer_matrix.json`](support/anneal_claim_transfer_matrix.json)).

In Anneal's architecture, the top-level crate obligation `Trusted.CrateTheorem (c : Crate) : Prop` is a conjunction of five crate-wide invariants:

```lean
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (FnContractWellFormed c.adts c.bodies)) ∧
  VerificationResult c.tcbWaivedIds
    (c.functions.map (fun fn => fn.obligation c.adts c.bodies c.adtInv c.tcb))
```

where each `fn.obligation` requires `FnVerified` across both `fn.bodyId` (`--release`) and optional `fn.debugBodyId` (`--debug`), and `FnBodyVerified` is defined as:

```lean
def FnBodyVerified (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (tcb : List TCBItem := []) : Prop :=
  (MirLang adts bodies).Verified
    (fun s => SafetyPre adts bodies adtInv fn body s tcb)
    (fun s out => EffectivePost adts bodies adtInv fn body s out tcb)
    body
```

By the multi-guarantee lattice-meet equivalence (`Anneal.verified_meet_iff`), `FnBodyVerified` is equivalent to proving unconditional baseline safety `(MirLang adts bodies).Verified SafetyPre SafetyPost body` together with conditional functional correctness `MirSem adts bodies body ≤ SpecOn (SafetyPre ∧ fn.safetyPre) ContractPost`.

Table 3 classifies all ten Anneal statement forms (`SF-01` through `SF-10`) and their exact binary transfer behavior:

| ID | Anneal Statement Form | Formal Definition in Anneal | Transfers Under `ProductiveCompiles`? | Transfers Under `ResourceBSim` (`CakeML`)? | Transfers Under `CTCompiles`? | Side Conditions Required for Binary Inheritance |
| :-: | :--- | :--- | :---: | :---: | :---: | :--- |
| **`SF-01`** | **Static & PME Contract Well-Formedness** | `FnContractWellFormed` (`StaticBodyWf ∧ ConstsTotal ∧ MonoConstsWf`) | **Yes** (`L_src.wf s ↔ L_tgt.wf t`) | **Yes** | **Yes** | Target layout sizes $\le \texttt{isize::MAX}$ and target instruction/register fit (`checkIsaFits`). |
| **`SF-02`** | **ADT Invariant Admissibility** | `AdmissibleAdtInv c.adts c.adtInv` (all-public-safe structs accept all structurally valid payloads) | **Yes** | **Yes** | **Yes** | Target ABI layout codec (`BehaviorCodec`) maps target byte representations back to `MirVal.valid`. |
| **`SF-03`** | **Miracle-Freedom (Law of Excluded Miracle)** | `Language.ProductiveOn SafetyPre body` ($\forall s,\; \text{SafetyPre}(s) \implies \exists h\; o,\; \text{val}\; h\; o$) | **Yes** (`productiveCompiles_transfers_verified`) | **Yes** | **Yes** | Target ISA transition relation must be total on all valid machine states (fails under `Compiles` alone on query slack). |
| **`SF-04`** | **All-Prefix Baseline UB-Freedom** | `(MirSem body s).defined` on `SafetyPre` ($\forall n\; tr\; out,\; \text{ReachesPrefix}\; n \implies out.\text{isSafe}$) | **Yes** (`productiveCompiles_transfers_verified`) | **Yes** (if stack overflow traps safely or is statically bounded) | **Yes** | Safe functions (`isUnsafe = false`) cannot assume `fn.safetyPre` to avoid UB; target must model hardware traps/OOB as `.failed`. |
| **`SF-05`** | **Return Validity & Compile-Time Guard Freedom** | `SafetyPost`: normal returns satisfy `r.value.valid adts adtInv` (and caller-owned referent bounds) and $out \ne \texttt{.compileTimeError}$ | **Yes** (`productiveCompiles_transfers_verified`) | **Yes** (`resource_refinement_transfers_partial_safety...`) | **Yes** | `PartialBehaviorCodec.decodeOut` must map invalid target bit patterns (e.g., `bool` byte $\notin \{0,1\}$) to `none`. |
| **`SF-06`** | **Conditional Functional Contracts** | `EffectivePost`: `SafetyPost s out ∧ (fn.safetyPre s → ContractPost s out)` (`EnsuresEqArg`, `EnsuresAtomicLoad`) | **Yes** (`productiveCompiles_transfers_verified`) | **Partial** (holds on normal return; early OOM allowed unless bounded) | **Yes** | Calling-convention lens (`FramedCodec`) must enforce ABI register/stack marshaling and callee-saved restoration. |
| **`SF-07`** | **Total Termination & Reactive Liveness** | `TerminatesPost` (excluding `.diverges` and `.reacts` in `EventualOut`) | **Yes** (`productiveCompiles_transfers_termination`) | **No** (unless paired with quantitative stack bound $\le \text{headroom}$) | **Yes** | Requires `EventualBehaviorOf` (well-founded stuttering measure) **plus** quantitative stack bound $\mathcal{S}(f) \le \text{headroom}$. |
| **`SF-08`** | **Spatial Memory Footprint & Frame Preservation** | `FootprintAt` / `argsMatchInv` / caller-local frame invariance | **Yes** (with `PartitionedFrameLayout`) | **Yes** (with `PartitionedFrameLayout`) | **Yes** | `Stacking` pass must isolate private spill/saved-register slots from public address-taken stack slots (`public_store_preserves_private_spills...`), with trace-level `memaccessInbounds`. |
| **`SF-09`** | **2-Safety Constant-Time & Secret Erasure** | `ConstantTimeOn` / `TargetCTAndScrubbed` | **No** (`productiveCompiles_fails_constant_time_transfer`) | **No** | **Yes** (`ctCompiles_transfers_verified_and_constant_time`) | Requires either lockstep `CTCompiles` + Besson IFP spill-scrubbing pass OR target-byte `admitCtKernelExtension` gate + hardware `DIT`/`DOITM`. |
| **`SF-10`** | **Crate Waiver & Obligation Envelope** | `VerificationResult c.tcbWaivedIds obligations` in `CrateTheorem` | **Yes** | **Yes** | **Yes** | Any unverified backend pass, FFI bridge, or `compileTimeGuard` waiver must be recorded in `c.tcb` (`NoDupIds`). |

## Boundaries

1. **Physical Stack Exhaustion Under Unbounded `ProductiveCompiles` (`known not to apply` without a static frame bound):**
   - Because Rust MIR locals (`_0`..`_k`) live in an abstract local store whereas x86-64/AArch64/RV64GC decrements a bounded physical stack pointer `sp`, `ProductiveCompiles` holds on real hardware only for initial machine states whose available stack headroom exceeds the compiled function's transitive stack high-water mark $\mathcal{S}(f)$ (verified via `Stack-Aware CompCert` / `Bedrock2` `FitsStack` / `checkIsaFits`).
2. **Microarchitectural Side Channels Beyond Architectural Constant-Time (`known not to apply` without hardware `DIT`/`DOITM` and context-switch `Time Protection`):**
   - `CTCompiles` preserves instruction-pointer (`PC`) and memory-address traces (`Arch-CT`), but preventing data-dependent ALU timing, speculative transient execution (`Spectre-v1`), and cross-domain cache/BPU residual leakage requires setting hardware `DIT`/`DOITM` bits, speculative `#msf` masking (`ob7b`), pre-return register/spill zeroization (`ob7c`), and OS context-switch `Time Protection` flushes.

## Evidence

1. **Anneal Repository Sources (`joshlf/anneal`):**
   - `joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`: `docs/design.md:190-286`, `docs/architecture.md:69-190, 288-370`, `docs/trust-model.md:42-251`, `THREAT_MODEL.md:58-120`, `trusted/audit/TrustedBoundary.lean:1-823`.
   - Core refinement and MIR statement definitions (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirSemantics.lean`, `theory/Anneal/Refinement.lean`) reproduced and verified in [`support/PropertyTransferAndAnnealClaimsProbe.lean`](support/PropertyTransferAndAnnealClaimsProbe.lean).
2. **Preserved Support Artifacts in This Package:**
   - [`support/PropertyTransferAndAnnealClaimsProbe.lean`](support/PropertyTransferAndAnnealClaimsProbe.lean) (356 lines, `sha256: 37d1a3dc964e62793de7a731810b4f119c542e69965cc591bfaf8c81e4d3ac99`): Checked under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false`, proving `productiveCompiles_transfers_verified`, `productiveCompiles_transfers_termination`, `resource_refinement_transfers_partial_safety_but_not_termination`, `productiveCompiles_fails_constant_time_transfer`, and `ctCompiles_transfers_verified_and_constant_time` with zero `sorryAx` and zero `Lean.ofReduceBool`.
   - [`support/anneal_claim_transfer_matrix.json`](support/anneal_claim_transfer_matrix.json) (124 lines, `sha256: 65538031b40900f2a05f2728d51f869c41e849088fb22007bdfb1671ef633a95`): Structured 10-form × 6-refinement transfer classification matrix.

## Revalidation

Run the following command to revalidate all five mechanized Lean 4.34.1 property-transfer theorems and verify the 10-form JSON matrix:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/observable-behavior-property-transfer-and-anneal-statement-forms/support/PropertyTransferAndAnnealClaimsProbe.lean

python3 -c 'import json; d = json.load(open("reports/observable-behavior-property-transfer-and-anneal-statement-forms/support/anneal_claim_transfer_matrix.json")); assert len(d["anneal_statement_forms"]) == 10; print("OK:", len(d["anneal_statement_forms"]), "statement forms")'
```

Expected output: four `#print axioms` checks report `does not depend on any axioms` and one reports `[propext, Quot.sound]` (zero `sorryAx`, zero `Lean.ofReduceBool`), and the Python check prints `OK: 10 statement forms` with exit code `0`.
