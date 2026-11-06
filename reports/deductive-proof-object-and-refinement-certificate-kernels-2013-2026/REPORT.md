# Certificate-Verifying Kernels: Deductive Proof-Object Checkers, seL4 Binary/Cogent Refinement Certificates, and Anneal's Ring-0 Kernel Extension Admission Architecture (2013–2026)

## Summary

Operating system kernels that admit native machine code into privileged execution (Ring 0 on x86-64, EL1 on AArch64, M/S-mode on RISC-V) without hardware page-table switching face a fundamental tension between **expressiveness** and **trusted computing base (TCB) complexity**. In-kernel abstract interpreters such as the Linux eBPF verifier (~35,000+ LoC of C) suffer recurring path-explosion, range-tracking, and state-pruning soundness bugs because the kernel performs complex static analysis online at module load time.

Between 2013 and 2026, four distinct certificate-verifying paradigms emerged to replace online abstract interpretation with small, mechanically verified proof or refinement checks:

1. **A Posteriori Binary Translation Validation via Cutpoint Graph Refinement (`seL4/graph-refine`, PLDI 2013)**:
   Decompiles compiled ARM, x86-64, or RISC-V ELF kernel binaries into an intermediate control-flow graph (`GraphLang`) using the Cambridge HOL4 decompiler (Myreen's decompilation-into-logic) and proves trace equivalence against `Simpl`/`AutoCorres` C semantics by slicing loops at designated **cutpoints** and discharging acyclic path equivalences via SMT verification conditions.
2. **Certifying Systems DSL Compilation via Linear Value-to-In-Place-Update Refinement (`Cogent`, `Dargent`, `Pancake`, 2016–2023)**:
   Restricts kernel filesystems (`BilbyFS`, `ext2`) and device drivers to a pure, linearly typed functional language (`Cogent`) paired with declarative bit/byte layout descriptors (`Dargent`). Because the **linear / uniqueness type system** guarantees that every mutable heap pointer has a unique live owner, the compiler emits both zero-GC destructive in-place C mutations and a modular 4-stage Isabelle/HOL refinement certificate proving that imperative in-place updates refine pure functional updates while preserving all disjoint kernel heap objects.
3. **Minimal Deductive Proof-Object Checkers (`Metamath Zero / .mmb` CPP 2020, `CakeML`/`Candle`, Lean 4 Kernel Replay)**:
   Separates proof synthesis from an ultra-compact linear stack-machine proof checker (`mm0-c/verifier.c`, ~500–1,000 LoC of allocation-free C over a pointer-indexed binary `.mmb` stream) or an out-of-kernel verified checker paired with cryptographic or capability-bound attestation.
4. **Anneal's Consumer-Bound Proof-Checking & Ring-0 Extension Admission Architecture (`Trusted.*`, `Anneal.PassCompiler`, `Anneal.CertChecker`, `Kraken`, 2026)**:
   Unifies per-pass certificate checking (`PassCompiler.ofCertChecker`) and deductive kernel replay (`StrictUnitTheorem` + `EmittedArtifact` + `trusted/audit`) under a **consumer-bound admission gate** whose theorem statement is parameterized directly over the exact byte sequence loaded by the kernel consumer.

This report synthesizes these four paradigms from primary sources and mechanizes **22 constructive, axiom-clean theorems** in [`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean) (verified under Lean `v4.34.1` with `0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`), alongside an empirical benchmark of three Ring-0 certificate-checking substrates across extension sizes $N \in \{16, 64, 256, 1024, 4096\}$ in [`support/certificate_substrate_probe.py`](support/certificate_substrate_probe.py).

---

## Applicability

This report applies directly to:

- **Anneal's Trusted Verification Boundary (`joshlf/anneal`, `trusted/lean/Trusted/` and `theory/Anneal/Refinement.lean`)**:
  Specifically `Trusted.Refinement` (`Language`, `VerifiedOn`, `Obligation`, `EmittedArtifact`, `StrictUnitTheorem`), `Trusted.StepResult` (`StepResult`, `SmallStepMachine`, `ReachesPrefix`, `EventualBehaviorOf`), `Trusted.MirSemantics` (`CrateTheorem`), `Trusted.Rv64Semantics` (`encodeRv64ElfBytes`, `Rv64ArchState`), `Trusted.X86Semantics` (`X86State`, `AdmissibleLibInv`, `CrateTheorem`), `Anneal.PassCompiler`, `Anneal.CertChecker`, and the outer audit gate `trusted/audit/src/lib.rs` (`verify_emitted_artifacts`).
- **Anneal's Kernel Verification Prototype (`google/zerocopy` branch `anneal-kernel`, commit `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`)**:
  Specifically `anneal/src/Anneal.lean` (`Anneal.SpecHolds (defined inline as `∀ x, ∃ y, f x = some y ∧ Rel x y`)`, `Anneal.wp_prove_orthogonal`, `SpecLayout`, `SpecSliceDstLayout`) and `anneal/src/generate.rs`.
- **Kraken's Consumer-Bound Byte-Certificate Checker (`AeneasVerif/kraken`, commit `8af78062037bc237b341d20252aafd1797c1bcb7`)**:
  Specifically how consumer-bound byte checking extends from single-leaf AArch64 functions to full Ring-0 kernel extensions with host-kernel helper calls and linear capability transfer.

---

## Findings

### 1. seL4 Binary Translation Validation (`seL4/graph-refine`, PLDI 2013) & Cutpoint Trace Refinement

#### 1.1 Primary Sources

| System / Paper | Authors & Venue | DOI / Repository | Core Mechanism |
|---|---|---|---|
| **seL4 Binary Translation Validation (`graph-refine`)** | Thomas Sewell, Magnus O. Myreen, Gerwin Klein, *Translation Validation for a Verified OS Kernel*, PLDI 2013 | `10.1145/2491956.2462183` / `seL4/graph-refine` | HOL4 decompilation of ELF binary + `Simpl` C semantics $\to$ `GraphLang` cutpoint splitting + SMT trace equivalence |
| **Decompilation into Logic** | Magnus O. Myreen, Michael J. C. Gordon, Konrad Slind, *Decompilation into Logic — Improved*, FMCAD 2012 | `10.1109/FMCAD.2012.6462558` | Certifying lifter producing HOL4 Hoare triples $\text{SPEC}\; M\; P\; c\; Q$ over ARM/x86/RISC-V machine code |

#### 1.2 Technical Anatomy of `seL4/graph-refine`

The seL4 C implementation proof establishes that the `Simpl` C model (parsed from C99 source into Isabelle/HOL) refines the abstract specification via an intermediate executable design model. To remove the GCC compiler and linker from the TCB without rewriting GCC as a verified compiler, `seL4/graph-refine` performs **per-binary translation validation**:

1. **Trusted Machine-Code Lifter (Cambridge HOL4 Decompiler)**:
   Given the compiled seL4 ELF binary, Myreen's HOL4 decompiler decodes each instruction at concrete virtual addresses and proves a machine-code Hoare triple $\text{SPEC}\; M\; P\; c\; Q$ in HOL4 (modeling instruction fetch, register file updates, status flags, memory reads/writes, and alignment faults).
2. **`GraphLang` Common Control-Flow Representation**:
   Both the Isabelle/HOL `Simpl` C semantics (and `AutoCorres`-simplified C functions) and the HOL4-decompiled binary Hoare triples are exported into a common, flat control-flow graph representation called **`GraphLang`**. A `GraphLang` function consists of five node kinds:
   - `Basic(next, [var := expr, ...])`: simultaneous state variable updates;
   - `Cond(left, right, pred)`: conditional branch on a boolean formula `pred`;
   - `Call(next, fn_name, args, rets)`: structured function call;
   - `Ret`: normal function return;
   - `Err`: undefined behavior / alignment fault / safety violation trap.
3. **Cutpoint Splitting (`CutpointStep`)**:
   Because GCC at `-O1`/`-O2` transforms local control flow (register allocation, common subexpression elimination, loop rotation, tail-call/inlining adjustments), step-for-step lockstep simulation fails. Whole-function symbolic execution also diverges in the presence of loops. `graph-refine` resolves both by selecting **cutpoints** (function entry, function exit/error, and loop headers in the source and binary CFGs) that slice the cyclic control-flow graphs into a finite set of **loop-free (acyclic) path segments**.
4. **SMT Proof Obligations & Inductive Composition (`sel4_graph_refine_cutpoint_composition_soundness`)**:
   Between each pair of cutpoints $(c_{\text{in}}, c_{\text{out}})$, `graph-refine` symbolically executes all acyclic paths in the C `GraphLang` and binary `GraphLang`, emitting quantifier-free bitvector + array (`QF_ABV`) verification conditions to Z3 / SONOLAR. The SMT obligation checks:
   - **Safety (Non-Failure)**: If the C `GraphLang` cannot reach `Err` from a state satisfying the cutpoint invariant at $c_{\text{in}}$, the binary `GraphLang` cannot reach `Err` either.
   - **Trace Equivalence**: For every non-erroneous execution reaching $c_{\text{out}}$ in the binary, there is a matching execution in the C graph reaching $c_{\text{out}}$ such that the cutpoint state relation (`CutpointStateRel`, equating global kernel memory, ghost heap-typing state `htd`, and ABI return registers) holds on exit.
   In [`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean) (`lines 149–164`), theorem `sel4_graph_refine_cutpoint_composition_soundness` proves (with `0` axioms) that local segment refinement (`SegmentRefines`) composes inductively across arbitrary multi-segment execution traces.

---

### 2. Certifying Kernel Compilers (`Cogent`, `Dargent`, `Pancake`) & Linear Value-to-In-Place-Update Certificates

#### 2.1 Primary Sources

| System / Paper | Authors & Venue | DOI / Repository | Core Mechanism |
|---|---|---|---|
| **Cogent (ASPLOS 2016)** | Sidney Amani et al., *Cogent: Verifying High-Assurance File System Implementations*, ASPLOS 2016 | `10.1145/2872362.2872404` / `seL4/cogent` | Certifying linear functional compiler for `BilbyFS` & `ext2` emitting C + Isabelle/HOL refinement proofs |
| **Cogent Value $\leftrightarrow$ Update Refinement (ICFP 2016)** | Liam O'Connor et al., *Refinement through Restraint: Bringing Down the Cost of Verification*, ICFP 2016 | `10.1145/2951913.2951940` / `seL4/cogent` | Formalization of `Value` semantics, `Update` semantics, linear frame relation `uval_typing`, and `AutoCorres` bridge |
| **Dargent Data Layout Refinement (POPL 2023)** | Zilin Chen, Ambroise Lafont, Liam O'Connor, Gabriele Keller, Craig McLaughlin, Vincent Jackson, Christine Rizkallah, *Dargent: A Silver Bullet for Verified Data Layout Refinement*, POPL 2023 | `10.1145/3571240` / `seL4/cogent` | Declarative bit/byte layout DSL generating custom C getters/setters and bit-disjointness refinement theorems |
| **Pancake Verified Driver Compiler (PLOS 2023)** | Johannes Aman Pohjola et al., *Pancake: Verified Systems Programming Made Sweeter*, PLOS 2023 | `10.1145/3623759.3624544` / `CakeML/pancake` | Imperative systems language for seL4 Microkit device drivers compiled directly through the verified CakeML backend |

#### 2.2 The Four-Layer `Cogent` Refinement Chain & Destructive In-Place Update Soundness

While `seL4/graph-refine` validates a single fixed microkernel binary *a posteriori*, OS kernel extensions such as filesystems (`BilbyFS`, `ext2`) and device drivers require high-level modularity without garbage collection. **`Cogent`** achieves this by co-designing a **linearly typed pure functional language** with an **automatic Isabelle/HOL refinement-certificate generator**:

1. **Four-Layer Isabelle/HOL Certificate Chain**:
   For every compiled `Cogent` module, the compiler emits C code plus four Isabelle/HOL theories and three connecting refinement proofs:
   $$\underbrace{\text{Shallow Functional Spec}}_{\text{Pure HOL functions/records}} \;\sqsubseteq_{\text{Desugar/Scorer}}\; \underbrace{\text{Deep Embedding (Value Semantics)}}_{v \vdash e \Downarrow_V v'} \;\sqsubseteq_{\text{Linear Frame (`uval\_typing`)}}\; \underbrace{\text{Deep Embedding (Update Semantics)}}_{(u, \mu) \vdash e \Downarrow_U (u', \mu')} \;\sqsubseteq_{\text{AutoCorres}}\; \underbrace{\text{Compiled C}}_{\text{SIMPL / C99}}$$
2. **How Linear Types Eliminate Garbage Collection and Enable Destructive In-Place Mutation**:
   In `Cogent`'s type system, every heap-allocated boxed record (`Boxed Record τ p`) has a linear/uniqueness kind unless temporarily borrowed as read-only via the **`!` (bang)** operator:
   - Every linear variable must be consumed **exactly once** (no implicit drop $\implies$ no garbage collector or reference counting needed; no implicit duplication $\implies$ no mutable aliasing).
   - When a pure functional `Cogent` program takes a boxed record `r` and constructs an updated record `r { field := newVal }`, the generated C code **destructively overwrites `r->field = newVal` in-place** at the exact pointer `p` in the kernel heap $\mu$.
3. **Mechanized Soundness (`cogent_linear_in_place_refinement_soundness`) and Aliasing Counterexample (`nonlinear_alias_breaks_in_place_refinement`)**:
   In [`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean) (`lines 176–366`):
   - `frame_disjoint_preservation` (`lines 285–293`) proves that destructive in-place mutation `evalImpInPlace` of `targetVar` leaves every disjoint heap buffer `q ≠ ptrs targetVar` byte-for-byte identical.
   - `cogent_linear_in_place_refinement_soundness` (`lines 300–338`) proves that when `LinearCert` certifies that no other live variable aliases `ptrs targetVar` and `LayoutDisjoint` certifies that `Dargent` field offsets are non-overlapping, `evalImpInPlace` refines the pure functional record update `evalPureUpdate` across all live variables (`FrameRel`) with zero copying and zero GC.
   - `nonlinear_alias_breaks_in_place_refinement` (`lines 345–366`) proves that if two distinct live variables (`0` and `1`) alias the same heap buffer pointer (`ptrs 0 = 0`, `ptrs 1 = 0`, so `LinearCert [0, 1] ptrs 0 = false`), in-place mutation of `0` silently corrupts the pure observation of `1`, falsifying `FrameRel`.

---

### 3. Compact Proof-Object Certificate Checkers (`Metamath Zero / .mmb`, Signed Attestation Daemons, and Anneal's Consumer-Bound Proof-Checking Gate)

#### 3.1 Technical Anatomy of Metamath Zero (`MM0` / `.mmb`, Carneiro CPP 2020)

Mario Carneiro's **Metamath Zero (`MM0`)** (*Metamath Zero: Designing a Theorem Prover Prover*, CPP 2020, DOI `10.1145/3372885.3373826`, `digama0/mm0`) defines a binary proof-object format (**`.mmb`**) engineered for a **~500-line allocation-free C verifier (`mm0-c/verifier.c`)**:

1. **40-Byte Fixed Header & Pointer-Indexed Tables**:
   An `.mmb` file begins with a 40-byte header (`MM0B` magic bytes, version `1`, `num_sorts`, `num_terms`, `num_thms`, `u32` offsets `p_terms`, `p_thms`, and `u64` offsets `p_proof`, `p_index`) so the C verifier can cast the byte buffer directly into C struct arrays with **zero dynamic memory allocation (`malloc`)** and **zero hash-table lookups**.
2. **Separation of Unification Stream and Proof Stream**:
   Each theorem entry in `p_thms` stores an explicit **unification bytecode stream** (`U_Ref`, `U_Term`, `U_Dummy`, `U_Hyp`, `U_Save`). When the main proof stream invokes `MP_THM` (apply theorem $T$), the verifier pops the substitution arguments and hypotheses from `g_stack` and runs $T$'s linear unification bytecode in deterministic $O(|T|)$ steps without unification search or backtracking.
3. **5-Bit Opcode + 3-Bit Data-Width Varint Stream & Fixed Stacks**:
   Every command in the proof stream encodes a 5-bit opcode (`CMD_END = 0`, `MP_SAVE`, `MP_TERM`, `MP_REF`, `MP_DUMMY`, `MP_THM`, `MP_HYP`, `MP_CONV`, `MP_REFL`, `MP_SYMM`, `MP_CONG`, `MP_UNFOLD`) and a 3-bit immediate width selector (`0, 1, 2, 4` bytes) operating on `g_stack` and the append-only DAG-sharing array `g_heap`.

#### 3.2 Exact Mapping to Anneal's Trusted Verification Boundary

Inspecting `joshlf/anneal` (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, `3a89578`) and `google/zerocopy` (`anneal-kernel` `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`) establishes how Anneal implements consumer-bound proof and certificate verification:

- **`anneal/src/Anneal.lean` (`8fb35253fbc703cb2cd0997f4efcda76cf9062b6`)**:
  - `Anneal.SpecHolds (defined inline as `∀ x, ∃ y, f x = some y ∧ Rel x y`)` (`lines 34–38`) and `Anneal.wp_prove_orthogonal` (`lines 60–65`) decouple total termination/progress (`∃ y, m = .ok y`) from functional postcondition correctness (`∀ y, m = .ok y → P y`).
  - `SpecLayout`, `Layout`, `HasStaticLayout` (`lines 260–376`), and `SpecSliceDstLayout`/`reprCSliceDstSize` (`lines 414–502`) formalize layout and alignment invariants for zero-copy pointer conversions.
- **`trusted/lean/Trusted/Refinement.lean` (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`)**:
  - `Partial (B : Type u)` (`lines 106–108`): Constructive partiality carrier (`defined : Prop`, `val : defined → B`) avoiding `Classical.choice`, with `Partial.ub` (`118–119`) and `Partial.bot` (`127–128`).
  - `Language (SemObs : Type w)` (`lines 201–210`) & `Language.VerifiedOn` (`lines 329–334`): Conjoins `SpineSpecOn`, `NonVacuousOn`, and `ProductiveOn`.
  - Constructor-gated `Obligation (P : Prop)` (`lines 545–548` with `private mk ::`).
  - `EmittedArtifact` (`lines 733–742`), `VerificationUnit` (`lines 777–781`), and `StrictUnitTheorem` (`lines 795–799`): Binds every verification result `r ∈ u.results` to a unique `EmittedArtifact` `a ∈ u.emitted` with `a.id = r.artifactId ∧ a.contents = r.expectedArtifactContents`.
- **`trusted/lean/Trusted/StepResult.lean`**:
  - `StepResult` (`lines 57–61`: `.step`, `.choice`, `.terminated`, `.failed`, plus `.silent` `71–73` and `.externalCall` `92–95`), `SmallStepMachine` (`157–160`), `ReachesPrefix` (`175–204`), and `EventualBehaviorOf` (`228–248`).
- **`theory/Anneal/Refinement.lean`**:
  - `PassCompiler` (`lines 1312–1314`) and `CertChecker` (`lines 1941–1947`: `check : L.Prog → Cert → Bool`, `check_sound : ∀ p c, check p c = true → adm p`), with `PassCompiler.ofCertChecker` (`lines 1957–1963`) and `strictUnitTheorem_binds_emitted_artifact_to_compiled_target` (`lines 2020–2037`).
- **`trusted/lean/Trusted/MirSemantics.lean`, `Rv64Semantics.lean`, `X86Semantics.lean`, and `trusted/audit/src/lib.rs`**:
  - `CrateTheorem` (`MirSemantics.lean:727-733` and `X86Semantics.lean:888-894`), `encodeRv64ElfBytes` (`Rv64Semantics.lean:936-1007`), `AdmissibleLibInv` (`X86Semantics.lean:625-633`), and `verify_emitted_artifacts` (`trusted/audit/src/lib.rs:645-784`, checking on-disk ELF/hex bytes against `EmittedArtifact.contents` and replaying `TrustedBoundary.lean` at `trustLevel := 0` with only `{Quot.sound, propext}`).

#### 3.3 Mechanized Proof-Object & TCB-Transfer Theorems (Sections 2 & 5)

In [`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean):
- `mmb_verifier_sound` (`lines 667–692`) proves that any `.mmb` command stream accepted by `verifyMmbProof hyps stream target = true` yields a valid Hilbert-style derivation `Deriv hyps target`.
- `consumer_bound_mmb_gate_sound` (`lines 716–721`) and `unbound_theorem_checker_admits_spoofed_subject` (`lines 729–741`) prove that binding the `.mmb` verifier's target formula to `.byteSafe candidateBytes reqPolicy` is both sufficient and necessary to prevent Theorem-Subject Spoofing (where an unbound proof checker accepts a valid proof of `benignBytes = [1]` when loading `maliciousBytes = [2, 3]`).
- `extracted_cert_checker_to_mmb_bridge` (`lines 1805–1814`) and `concrete_mmb_modus_ponens_bridge_sound` (`lines 1821–1842`) prove that any verified `ByteCertChecker` equipped with a `CertToMmbBridge` transfers both `Deriv hyps (.byteSafe candidateBytes reqPolicy)` and semantic admissibility `Adm candidateBytes reqPolicy` through `consumerBoundMmbGate` via a 3-step modus-ponens `.mmb` stream `[.loadHyp 1, .loadHyp 0, .applyModusPonens]`.

#### 3.4 Architectural & Empirical Comparison of the Three Ring-0 Certificate Substrates

Executing [`support/certificate_substrate_probe.py`](support/certificate_substrate_probe.py) across extension sizes $N \in \{16, 64, 256, 1024, 4096\}$ instructions (`64 B` to `16,384 B` machine-code images; raw outputs in [`support/certificate_substrate_probe_results.json`](support/certificate_substrate_probe_results.json)) yields the following quantitative comparison:

| Extension Size $N$ (Instructions / Image Bytes) | Substrate A: In-Kernel `.mmb` Proof-Stream Verifier (`cert_bytes` / `state_bytes` / `steps`) | Substrate B: In-Kernel Extracted `CertChecker` (`cert_bytes` / `state_bytes` / `steps`) | Substrate C: Out-of-Kernel Daemon + Signed Attestation (`cert_bytes` / `state_bytes` / `steps`) |
|---|---|---|---|
| **$N = 16$** (`64 B` image) | `239 B` / `248 B` (`3` stack, `28` heap) / `53` steps | **`32 B`** / **`64 B`** / `16` steps | `128 B` / `128 B` / `3` SHA blocks |
| **$N = 64$** (`256 B` image) | `533 B` / `680 B` (`3` stack, `82` heap) / `203` steps | **`56 B`** / **`64 B`** / `64` steps | `128 B` / `128 B` / `6` SHA blocks |
| **$N = 256$** (`1,024 B` image) | `1,709 B` / `2,408 B` (`3` stack, `298` heap) / `803` steps | `152 B` / **`64 B`** / `256` steps | **`128 B`** / `128 B` / `18` SHA blocks |
| **$N = 1,024$** (`4,096 B` image) | `6,413 B` / `9,320 B` (`3` stack, `1,162` heap) / `3,203` steps | `536 B` (`13.1%` of img) / **`64 B`** / `1,024` steps | **`128 B`** / `128 B` / `66` SHA blocks |
| **$N = 4,096$** (`16,384 B` image) | `25,229 B` (`1.54x` img) / `36,968 B` (`3` stack, `4,618` heap) / `12,803` steps | `2,072 B` (**`12.6%` of img**) / **`64 B`** / `4,096` steps | **`128 B`** / `128 B` / `258` SHA blocks |

- **Extracted `CertChecker` (Substrate B)** achieves a **constant 64-byte ($O(1)$) Ring-0 verifier memory footprint** with zero dynamic allocation and a certificate size of only **$12.6\%$ of the machine-code binary size** at $N = 4096$ ($12.2\times$ smaller than `.mmb` proof streams and $3.2\times$ fewer verification steps).
- **`.mmb` Proof-Stream Verification (Substrate A)** maintains a constant 3-slot (`24 B`) evaluation stack and a tiny fixed deductive checker (~500 LoC C), making it ideal as a cross-policy deductive exchange format (`extracted_cert_checker_to_mmb_bridge`), though its append-only `g_heap` grows linearly with saved intermediate subproofs.
- **Signed Daemon Attestation (Substrate C)** provides a constant 128-byte envelope for hot-path cached reloads after an initial `CertChecker` or `trusted/audit` admission check, at the cost of placing the user-space daemon and key management inside the trust boundary if used standalone.

---

### 4. Anneal's Complete Ring-0 Kernel Extension Admission Gate (`KernelExtensionAdmissionGate`) & Linear Helper Capability Discipline

#### 4.1 Six-Obligation Sufficiency and Six-Way Non-Redundancy (Section 3)

Admitting a native machine-code extension directly into Ring 0 requires **six jointly sufficient and individually necessary obligations**:

| Obligation ID | Formal Predicate in `DeductiveAndRefinementCertificateKernels.lean` | Ring-0 Hazard Prevented |
|---|---|---|
| **Obligation 1 (`ob1_byteBinding`)** | `natListEq cert.boundBytes img.bytes && natEq cert.relocHash img.relocHash && natEq img.relocHash req.expectedReloc && progEq cert.certifiedProg img.decodedProg` | Whole-artifact byte substitution, trailing-byte injection, relocation-table tampering, or instruction-decode mismatch |
| **Obligation 2 (`ob2_isaPrivilegeConfinement`)** | `ob2_isaPrivilegeConfinement cert.certifiedProg` (no `.privOp`) | Privileged Ring-0 ISA escapes: `wrmsr` (`IA32_LSTAR` hijacking), `mov cr3`, `cli`/`sti`, `lidt`/`lgdt`, `swapgs` |
| **Obligation 3 (`ob3_frameDisjointMemory`)** | `ob3_frameDisjointMemory req cert.certifiedProg` (`memRead` $\in [\text{readableLo}, \text{readableHi})$, `memWrite` $\in [\text{writableLo}, \text{writableHi})$) | Arbitrary Ring-0 memory corruption of host page tables, IDT, or scheduler runqueues (`KernelCoreFrame`) |
| **Obligation 4 (`ob4_abiCalleeSaveRestoration`)** | `ob4_abiCalleeSaveRestoration req cert.certifiedProg` (`calleeSaveRbp = req.entryRbp`) | Clobbering host kernel caller's callee-saved registers (`rbp`, `rbx`, `r12..r15` / `s0..s11` / `x19..x29`) |
| **Obligation 5 (`ob5_interruptSafePointInvariant`)** | `ob5_interruptSafePointInvariant cert.certifiedProg` (`irqSafeEveryStep = true`) | Asynchronous hardware interrupt / NMI arriving while Ring-0 `rsp` is misaligned or while holding a spinlock across an exit/fault boundary |
| **Obligation 6 (`ob6_boundedFuelTermination`)** | `ob6_boundedFuelTermination req cert` (`certifiedFuel ≤ maxKernelExtensionFuel` $\wedge$ `terminatedRet = some req.expectedOutput`) | Ring-0 kernel thread hang / non-preemptible infinite loop (`.infiniteLoop`) or functional specification violation |

In [`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean) (`lines 748–1392`):
- **Master Sufficiency (`anneal_ring0_extension_admission_soundness`, `lines 1122–1168`)**: Proves that when `admitKernelExtension req candidateImage cert = true` (all 6 obligations hold), executing `candidateImage` in Ring 0 satisfies `SafeAndRefinesRing0 req` (privilege integrity, `KernelCoreFrame` preservation, ABI callee-save restoration, every-step interrupt safety, and fuel-bounded functional refinement).
- **Master Six-Way Necessity (`drop_ob1_unsound` .. `drop_ob6_unsound` and `anneal_ring0_six_obligations_necessary`, `lines 1223–1392`)**: Proves six concrete separating counterexamples demonstrating that dropping *any single obligation* $i \in \{1..6\}$ while enforcing all remaining five admits a concrete `(badImg_i, cert_i)` that violates Ring-0 kernel safety or liveness.

#### 4.2 Linear Capability Transfer & Borrow Across Host-Kernel Helper Calls (Section 4)

In Section 4 of [`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean) (`lines 1394–1766`), we model host-kernel helper invocations (`ExternalHelperKind`: `.borrowReadOnly cap`, `.consumeAndTransfer cap`, `.allocAcquire cap`) corresponding to `StepResult.externalCall` (`Trusted/StepResult.lean:92-95`):
- **Read-Only Borrow (`helper_linear_borrow_preserves_frame`, `lines 1566–1578`)**: Borrowing an owned capability `cap` via `.borrowReadOnly cap` preserves `ownedCaps`, `kernelCoreFrameIntact = true`, and `useAfterTransferFault = false`.
- **Linear Transfer & Static Use-After-Transfer Rejection (`use_after_transfer_rejected` `lines 1585–1609` & `helper_linear_consume_prevents_use_after_free` `lines 1693–1721`)**: Consuming/transferring `p` via `.consumeAndTransfer p` removes `p` from `ownedCaps` (`hasCap_removeCap_self`), statically rejecting any subsequent read or write to `p` (`= none`) and guaranteeing zero use-after-transfer faults across arbitrary multi-step programs.
- **Zero-Net-Acquired-Capability Return Gate (`untracked_helper_leak_across_exit_unsound` `lines 1729–1742` & `linear_helper_discipline_leak_free` `lines 1749–1766`)**: Proves that per-step capability checking (`checkCapProg`) alone admits resource/spinlock leaks across exit (`[.callHelper (.allocAcquire 9), .retClean 7]`), whereas enforcing `checkLinearHelperGate st.ownedCaps st.ownedCaps prog = true` guarantees both zero use-after-transfer faults and strict capability/lock conservation on exit (`stFinal.ownedCaps = st.ownedCaps`).

---

## Boundaries

1. **Trusted Hardware & Loader Semantics**:
   All four certificate-verifying kernel architectures depend on the soundness of the lowest-level instruction decoder and operational machine model (`Rv64Semantics`, `X86Semantics`, `Kraken` AArch64 decoder, or HOL4's `SPEC` lifter) with respect to physical CPU execution, including instruction-cache coherence (`icache`/`dcache` flush upon module load) and absence of unmodeled self-modifying code.
2. **Asynchronous Shared-Memory Races Outside Linear Capabilities**:
   `cogent_linear_in_place_refinement_soundness` and `linear_helper_discipline_leak_free` guarantee frame preservation and absence of use-after-transfer under linear capability discipline (`LinearCert` and `checkLinearHelperGate`). If host-kernel code outside the verified boundary concurrently mutates a buffer while an extension holds a capability to it (violating disjoint ownership), linear refinement no longer holds unless mediated by explicit capability transfer (`consumeAndTransfer` / `allocAcquire`).

---

## Evidence

### 1. Mechanized Theorem Inventory ([`support/DeductiveAndRefinementCertificateKernels.lean`](support/DeductiveAndRefinementCertificateKernels.lean))

| # | Theorem Name | Section | Lines | Axiom Footprint (`#print axioms`) |
|---|---|---|---|---|
| 1 | `sel4_graph_refine_cutpoint_composition_soundness` | 1A | `149–164` | `none` (0 axioms) |
| 2 | `frame_disjoint_preservation` | 1B | `285–293` | `[propext]` |
| 3 | `cogent_linear_in_place_refinement_soundness` | 1B | `300–338` | `[propext]` |
| 4 | `nonlinear_alias_breaks_in_place_refinement` | 1B | `345–366` | `[propext]` |
| 5 | `mmb_verifier_sound` | 2 | `667–692` | `[propext]` |
| 6 | `consumer_bound_mmb_gate_sound` | 2 | `716–721` | `[propext]` |
| 7 | `unbound_theorem_checker_admits_spoofed_subject` | 2 | `729–741` | `[propext]` |
| 8 | `anneal_ring0_extension_admission_soundness` | 3 | `1122–1168` | `[propext]` |
| 9 | `drop_ob1_unsound` | 3 | `1223–1243` | `[propext]` |
| 10 | `drop_ob2_unsound` | 3 | `1248–1268` | `[propext]` |
| 11 | `drop_ob3_unsound` | 3 | `1273–1293` | `[propext]` |
| 12 | `drop_ob4_unsound` | 3 | `1298–1318` | `[propext]` |
| 13 | `drop_ob5_unsound` | 3 | `1323–1343` | `[propext]` |
| 14 | `drop_ob6_unsound` | 3 | `1349–1369` | `[propext]` |
| 15 | `anneal_ring0_six_obligations_necessary` | 3 | `1375–1391` | `[propext]` |
| 16 | `hasCap_removeCap_self` | 4 | `1431–1442` | `none` (0 axioms) |
| 17 | `helper_linear_borrow_preserves_frame` | 4 | `1566–1578` | `[propext]` |
| 18 | `use_after_transfer_rejected` | 4 | `1585–1609` | `[propext]` |
| 19 | `helper_linear_consume_prevents_use_after_free` | 4 | `1693–1721` | `[propext]` |
| 20 | `untracked_helper_leak_across_exit_unsound` | 4 | `1729–1742` | `[propext]` |
| 21 | `linear_helper_discipline_leak_free` | 4 | `1749–1766` | `[propext]` |
| 22 | `extracted_cert_checker_to_mmb_bridge` | 5 | `1805–1814` | `[propext]` |
| 23 | `concrete_mmb_modus_ponens_bridge_sound` | 5 | `1821–1842` | `[propext]` |

### 2. Primary Source & Codebase Citations

- **seL4 Binary Translation Validation**: Sewell, Myreen & Klein, PLDI 2013 (`10.1145/2491956.2462183`); Myreen, Gordon & Slind, FMCAD 2012 (`10.1109/FMCAD.2012.6462558`); `seL4/graph-refine`.
- **Cogent, Dargent & Pancake**: Amani et al., ASPLOS 2016 (`10.1145/2872362.2872404`); O'Connor et al., ICFP 2016 (`10.1145/2951913.2951940`); Chen et al., POPL 2023 (`10.1145/3571240`); Aman Pohjola et al., PLOS 2023 (`10.1145/3623759.3624544`).
- **Metamath Zero (`.mmb`)**: Carneiro, CPP 2020 (`10.1145/3372885.3373826`); `digama0/mm0` (`mm0-c/verifier.c`, `mm0-c/verifier.h`).
- **Anneal & Kraken**: `joshlf/anneal` (`trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/lean/Trusted/Rv64Semantics.lean`, `trusted/lean/Trusted/X86Semantics.lean`, `theory/Anneal/Refinement.lean`, `trusted/audit/src/lib.rs`); `google/zerocopy` (`anneal-kernel` branch `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, `anneal/src/Anneal.lean`); `AeneasVerif/kraken` (`8af78062037bc237b341d20252aafd1797c1bcb7`).

---

## Revalidation

Run the following commands from the package directory (`reports/deductive-proof-object-and-refinement-certificate-kernels-2013-2026/`) to revalidate all mechanized theorems, axiom footprints, and empirical substrate benchmarks:

```bash
# 1. Verify all 23 mechanized theorems and #print axioms outputs under Lean 4.34.1
lean support/DeductiveAndRefinementCertificateKernels.lean

# 2. Re-run the empirical Ring-0 certificate-checking substrate benchmark probe
python3 support/certificate_substrate_probe.py
```
