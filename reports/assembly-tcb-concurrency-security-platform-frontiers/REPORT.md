# Assembly proof TCB, concurrency, security and platform extension boundaries

## Summary

A small proof kernel does not remove the need to justify the program/model/ABI/resource interfaces supplied to it. Proof search, rewriting and symbolic execution can remain untrusted when their outputs are checked against exact obligations; an unvalidated instruction summary, erased access or wrong ABI witness can still make a valid proof describe the wrong claim.

Sequential functional correctness, concurrent soundness, architectural constant-time and physical security are distinct properties. The current bounded Kraken domain is useful, but extending it to atomics, interrupts, devices or control-flow protections requires explicit operational and environment changes. This report investigates those changes and executes small discriminating witnesses; it does not claim such extensions have been implemented.

## Applicability

The trust analysis combines current Kraken/Sail/Islaris/Jasmin/Vale/s2n findings with the completed Anneal TCB/compiler corpus. Concrete pins and selected theorem closure are retained in their companion reports. Rust atomic documentation is version1.99.0, compiler `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`; inline rules use Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. Intel DOIT guidance is live documentation observed2026-10-14, updated2025-09-10, not an immutable model pin.

`weak_memory_probe.py` exhausts an owned finite store-buffering example under immediate-write and delayed-store fragments. `ContextBridge.lean` checks owned observation-model witnesses using Lean4.34.1. Neither artifact is a full language/hardware weak-memory or side-channel model. Research coverage: AS24–AS27 and the internal-TCB portion of MR24.

## Findings

### Internal trust is a ledger of semantic arrows

Basis: surveyed primary artifacts + derived.

Separate at least five trust classes:

| Class | Examples | How the logical TCB can shrink |
|---|---|---|
| Proof admission | Kernel implementation, actual theorem axioms, native reduction/checking | Checked terms, explicit axiom policy, independently validated kernel/checker |
| Semantic definition | ISA operations, UB, byte/permission/provenance rules | Small reviewed definitions, reference-model relations, checked instruction summaries |
| Import and binding | Source parser, AST, decoder, layout, symbol/bytes | Verified import or independently checked certificates bound to exact subjects |
| Language boundary | Rust type/resource interpretation, FnAbi, callbacks/continuations | Machine-checked adapters and contextual linking theorems |
| Physical/environment | Hardware configuration, loader, OS, devices, deployed bytes | Narrow configuration assumptions, final-artifact checks and proved environment refinements |

An external user may reasonably include all Anneal code in their trust boundary, while the internal proof architecture separates these classes. Merely moving a transformation into an external process does not remove it from the semantic TCB. Conversely, a large untrusted producer need not become a logical axiom when the consumer can verify its exact output.

Selected theorem closure matters more than a repository-wide admission count. The actual Kraken pilot has no native reduction axiom, while one inspected upstream arithmetic theorem has an additional native bit-vector checker equation in its closure. That is different from `sorryAx`, and its acceptance policy must be explicit. The prior corpus's historical Lean kernel findings also prevent equating a clean axiom list with a proof of the kernel implementation itself.

### Proof-producing adapters need hostile-input controls

Basis: derived + performed companion experiments.

A minimal consumer should reconstruct the expected claim from independent challenge data, rather than accept a producer's statement about what it proved. Bind source/AST, instruction bytes/layout, ABI instance, initial resource domain, effects, observation relation and theorem dependencies. Cache reuse must preserve the same bindings.

The performed controls cover complementary parts: false inline contracts compile, an illegal late-output allocation has a checked counterexample, same-value/dead-resource states differ, a final-state frame can conceal an access, and exact byte/symbol checks reject selected object mutants. Each isolates a real seam; none alone is a general malicious-producer theorem. Reflection or solver certificates should check the intended formula and exact bit widths, not only a valid unrelated unsatisfiability result.

Useful next checker obligations include total parsing/admission, explicit unsupported results, complete CFG/operation coverage, no unadvertised premises, exact proof-root binding and preserved transitive assumptions. Reuse the prior TCB reports for protocol/kernel details; the assembly-specific delta is the ISA/ABI/resource/byte subject.

### Atomic compatibility spans compiler, language and hardware models

Basis: normative + derived + owned finite execution.

Rust1.99 atomic documentation describes an access-based interpretation of its atomic memory rules, including race and mixed-size restrictions. A raw assembly instruction that happens to perform an indivisible hardware operation still needs a language-level interpretation, compiler-visible effects and the ordering/resource contract. A compiler barrier and a hardware fence discharge different obligations. Memory options that promise no synchronization cannot be justified just by observing no final data change.

The owned litmus has two threads: write one's own variable, then read the other's. Under immediate writes with thread order retained, exhaustive exploration excludes result(0,0). Allowing writes to remain in one-entry buffers admits(0,0). This is a bounded, explicitly defined model distinction. It demonstrates why a sequential/interleaving argument cannot silently establish all weak-memory behaviors; it does not classify a Rust program or prove the full x86/AArch64 model.

For a future atomic wrapper, state access widths and alignments, supported target atomic features, the language/hardware event relation, synchronization edges, ownership transfer and mixed-size policy. A compare-exchange failure, larger physical implementation access or retry loop may need a different trace than a simple source load/store. A proof must preserve those relevant observations or prove their abstraction sound. The current sequential Kraken layer and MiniRust's SC-atomic wrapper cannot jointly supply an unstated full relaxed-memory theorem.

### Functional equality does not imply constant-time

Basis: primary security analysis + checked owned witnesses + derived.

`fixed_trace_noninterference` proves an owned fixed trace independent of a secret Boolean; `same_result_can_leak` proves equal scalar results can coexist with different observed addresses. Both have no axioms in their reported Lean closure. Their deliberately small observation model is the point: the security property must name its observations.

A real assembly constant-time theorem typically relates two executions with equal public inputs and compares relevant control/access observations. Return addresses, code placement, public lengths and environment configuration must be included or explicitly fixed. Nondeterministic/undefined instruction results and declassification require their own quantifiers. This is additional to single-execution safety and functional correctness.

The s2n analysis supplies a concrete separation among functional, access-safety and constant-time theorems. Intel's documented DOIT mode guarantees are instruction/configuration limited and do not eliminate all address-, power-, thermal- or frequency-related leakage. Thus a trace theorem and physical side-channel resistance remain different claims. The pilot makes no measured or proved constant-time assertion about its actual hardware executions.

### Platform extensions alter the state and environment relation

Basis: primary scope evidence + derived.

| Extension | New obligation before reusing a sequential hosted proof |
|---|---|
| Interrupts/signals/reentry | Interference relation, invariant opening/closing, stack and register save/restore |
| Context switching/TLS | Ownership of saved contexts, thread-local state and stack bounds; valid continuation identity |
| Virtual memory/faults | Translation/configuration, permissions, fault paths and environment changes |
| MMIO/volatile/DMA | Device/external events, ordering, access granularity and asynchronous resource changes |
| Stack probing/unwinding | Guard-page/probe premise, actual frame metadata and exceptional exits |
| PAC/BTI/CET/shadow stacks | Additional architectural/control-flow state and required instruction/metadata behavior |
| Self-modifying or dynamically replaced code | Code identity across execution, synchronization and permitted replacement relation |

These are conditional domains, not requirements for every scalar byte API. For a motivated extension, the simplest adequate route may be a richer authoritative ISA model rather than enlarging every hand-written Kraken definition. Islaris's system-level case studies demonstrate relevant methodology, while its exact source/validation limitations remain in the comparative report. A model that omits an effect cannot prove its interaction correct by treating the operation as an inert primitive.

One concrete extension is a device-ready read that transfers a byte buffer back to the CPU. Kraken's actual AArch64 `nonmem_load` continuation can receive both a value and a changed byte map; it deliberately permits a read to affect memory. `EnvironmentContracts.lean` constructs that actual effect, checks that default `All` rejects it, and checks an explicitly chosen response returning7 with byte42 at address256. A response returning7 but omitting the memory change fails the chosen postcondition. All three final theorem closures contain only the foundational trio. This is a small checked interface experiment, with no physical MMIO or device code executed. It identifies a possible environment contract; it does not prove a device obeys it, interpret Rust volatile accesses, or transfer logical borrow ownership. Those require an environment/resource relation in addition to the concrete byte update. Two ordinary failed proof drafts were rejected before the complete final proof; neither is accepted evidence.

### Conditional architecture choices

Basis: derived.

For ordinary scalar functions, a small Kraken adapter plus actual byte binding and a Rust resource relation may be practical. For broad system effects, a generated ISA model with checked summaries may reduce semantic duplication. For generated optimized kernels, Jasmin/Vale-style controlled languages can eliminate different compilation obligations. For imported existing binaries, object-bound HOL/ISA lifting offers a different starting point.

Compare these routes by which arrows they discharge and what remains trusted, not kernel size alone. The smallest source footprint can carry the largest unproved semantic assumption. The final agenda synthesis provides the many-to-many question/report map and the remaining stronger implementation frontiers.

## Boundaries

No complete weak-memory assembly/Rust wrapper, physical side-channel proof, interrupt/device model or new kernel was implemented. The finite litmus and observation witnesses are performed owned experiments, not full formalizations of Rust atomics, TSO, Arm memory or hardware timing. No deliberately invalid Rust or privileged operation was executed.

An unsupported extension is an honest domain restriction. It does not establish that the extension is impossible or that another surveyed foundation lacks it. Live vendor guidance must be rechecked for the exact processor/configuration, and empirical timing cannot prove absence of all leakage.

## Evidence

- Companion exact-source Kraken, Sail/Islaris, Jasmin/Vale and s2n reports and their selected theorem/byte-binding evidence.
- [Rust atomic rules](https://doc.rust-lang.org/std/sync/atomic/), version1.99.0; source at [the compiler pin](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/sync/atomic.rs).
- [Pinned inline interface](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md).
- [s2n soundness analysis](https://github.com/awslabs/s2n-bignum/blob/4d1356a7470663c752660a59375dc3a9ef548428/SOUNDNESS.md), particularly access safety and security boundaries.
- [Intel DOIT guidance](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/best-practices/data-operand-independent-timing-isa-guidance.html), observed2026-10-14.
- `support/weak_memory_probe.py` and exact outcome log; `ContextBridge.lean` and closure log in the resource-linking report.
- `support/EnvironmentContracts.lean` and final checker output: actual Kraken nonmemory effect plus a deliberately narrow chosen device response and omitted-effect control.

## Revalidation

Run the finite litmus probe and inspect its explicit transition rules, not only the result count. Recheck the current language/hardware ordering contract for any actual atomic case. Audit selected theorem dependencies after changing kernel or proof automation, and rerun the code/ABI/resource mutants against the intended consumer.

For an extension, define one concrete environment contract and a discriminating negative case before claiming support. A successful scalar pilot remains evidence only for that scalar domain.

*Authored by an AI agent acting on joshlf's behalf.*
