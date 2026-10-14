# Pinning, async progress and foreign or hardware resource contracts

## Summary

Pinning protects a valid value at a particular address until destruction permits storage reuse. Async suspension retains resources in future state, and cancellation needs a destruction/registration protocol. A fairness or responsiveness theorem addresses progress under explicit runtime/environment premises; it does not establish raw-pointer safety or cancellation cleanup.

FFI, volatile I/O, assembly and DMA add behavior outside an ordinary Rust heap model. Their specifications must carry ABI, ownership, synchronization and environmental effects visibly. In particular, volatile access is not inter-thread synchronization, and the MMIO exception cannot authorize arbitrary mutation of Rust-allocated memory.

## Applicability

Language contracts are inspected at Rust `d8ef4f3fe7031514cbd7d056b7b058814987ecec` and Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. Two research preprints are exact v1 subjects: arXiv `2610.09198v1` submitted 2026-10-06, and `2610.06003v1` submitted 2026-10-05. Both were publicly available before the 2026-10-14 observation; future venue labels in them do not make future publication an observed event. Their formal languages/subsets are not identified with actual Rust, MiniRust or normative language authority.

The native probe uses rustc 1.99.0 (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), aarch64-apple-darwin, LLVM 23.1.1, edition 2021, std and default debug compilation. It runs no async runtime, FFI, assembly or hardware I/O.

## Findings

### Pin protects validity until destruction, not just a numerical address

The `core::pin` contract requires an address-sensitive pinned value to remain valid in place until its drop handler is called, and its storage must not be invalidated/repurposed until drop returns or panics. For non-Unpin values, overwriting or manual deallocation therefore requires the prescribed destruction step first. Leaking a Box so its storage is never reused is compatible with this requirement. `Unpin` removes the pin restriction. Basis: **normative** stdlib contract, [drop guarantee](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/pin.rs#L510).

A suitable resource interpretation consequently retains allocation identity/liveness, the pinned place, the self-reference relation, permitted projections and the terminal destruction protocol. Address equality alone omits validity and storage lifetime. Recovering an ordinary mutable reference that permits moving the payload requires Unpin or the exact unsafe accessor premise. These are **derived** obligations from the contract, not a completed formal Pin model.

### Pending futures retain state; wakeup does not itself execute the task

`Future::poll` takes a pinned mutable receiver and Context, returning Pending or Ready. The latest Context waker is the one to schedule; pending futures generally need active polling to progress. Polling again after Ready may panic or block, but the safe method must still never cause UB. This is a stronger safe-call domain than a functional contract that simply excludes repolling. Basis: **normative** standard-library interface, [Future](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/future/future.rs#L37).

The Reference's await description converts to a future, polls a pinned receiver and yields when Pending; it explains suspension and resumption, rather than assigning a particular scheduler fairness guarantee. Resource proofs must connect each suspended state to its retained borrows/owned values, wake registrations and accessible aliases. Cancellation may destroy the future without taking the success continuation, so unregistering callbacks and releasing borrowed resources must be covered on that path. Basis: **normative** await rules + **derived** obligations, [await](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/expressions/await-expr.md).

### The native probe observes two destruction paths

`async_drop_probe.rs` captures an Rc-counted Drop value, drops one future without polling, then polls a second boxed/pinned future to Pending and drops it. Output is `unpolled=1; suspended_before_drop=1; suspended_after_drop=2`; every assertion succeeds and process exits zero. The preserved commands/output identify the exact executable observation. Basis: **execution**.

The probe distinguishes owned-state destruction from successful async completion on one compiler/target. It uses no self-reference, borrowed external buffer, persistent callback or runtime queue. It therefore does not prove cancellation safety, Pin projection, a lost-wakeup protocol, leak robustness or fair scheduling. These remain independent **derived** obligations.

### Responsiveness is conditional obligation discharge in LART

The `2610.09198v1` preprint defines LART obligations pairing wakers with monotonic predicates, transferred through repositories. Theorem 1 requires pollables to preserve obligations at yield and reactors to be responsive. Theorem 5 additionally requires faithful async compilation, fair scheduling and eventual external predicates, then concludes eventual task progress. Theorem 4's reactor argument uses repeated iterations; the terminating-reactor extension needs additional invocation ordering. The paper's base analysis does not handle try-wait-retry contention without its extension. Basis: **documentation**, §§3.2,4–5. [Exact preprint](https://arxiv.org/pdf/2610.09198v1).

This is progress evidence for the formalized pollable/reactor language and annotated extraction, not a proof of pointer validity, arbitrary Future cancellation or every production runtime. The claimed Jackdaw implementation is reported by the paper; its source artifact, analysis/extraction definitions and full correspondence were not obtained or examined in this wave. That is a research gap, not an unsupported-feature result.

### LAGC fairness has a restricted safe-Rust subject

The `2610.06003v1` preprint models safe source-like Rust using locally abstract/global concrete traces and an abstract current-thread scheduler. Theorem 5.7 assumes no locally infinite computations and a translation `trans`, relating scheduler executions to quiescent-fair traces. Theorem 5.9 establishes its Tokio-fair execution relation. The paper explicitly takes Rust's typing/borrowing guarantees for granted and excludes unsafe Rust. Basis: **documentation**, §§5.5,7. [Exact preprint](https://arxiv.org/pdf/2610.06003v1).

This result addresses a fairness notion and scheduling model, not a normative source semantics, Tree/Stacked Borrows, weak-memory UB or cancellation/destructor correspondence. Source/artifact definitions and the complete proof premises were not inspected here; its Rust-LAGC repository remains a separate lead. The title's completeness wording does not broaden the inspected theorem.

### Erased execution must preserve relevant failure and infinite behavior

A finite-result equality can hold even if abstraction maps an infinite source execution to a terminating model execution. A concrete mathematical witness is a source state with both `s → s` and `s → unit`, and a model with only `m → unit`: both finite-result sets are `{unit}`, but the source admits an infinite self-loop while the model strongly normalizes. Mapping the self-loop to no model step therefore does not reflect termination. This is a **derived** transition-system witness, not an executed Rust counterexample.

Likewise, deleting wake-registration, cancellation or environmental interference can remove the event on which a liveness premise depends. Termination/progress transfer therefore needs a relation controlling stuttering and infinite executions, plus the same fairness/environment hypotheses; ordinary partial-result agreement is insufficient. Basis: **derived** logical requirement, informed by the distinct WP/TWP and responsiveness targets.

For async resources, the relation must preserve the suspended state and terminal cleanup obligations even when no successful output exists. The proofs above supply useful examples of visible premises; neither supplies this complete bridge for Anneal's erased Rust execution. This is a future engineering obligation once a supported source/model domain is selected; the paper/artifact comparisons explicitly still unexamined are separate research gaps.

### Foreign callbacks require temporal ABI and ownership contracts

The pinned Reference lists wrong-ABI calls and unwinding across disallowed frames among UB. A foreign function contract must identify calling convention, value/layout validity, pointer ownership, retention duration, permitted mutation, concurrency and unwind behavior. A callback also needs reentrancy and terminal unregister/join behavior so the environment cannot use expired borrowed/pinned storage. Basis: **normative** UB clause + **derived** contract decomposition, [call/unwind boundary](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md#L55).

These are visible environmental obligations, not assumptions justified by a safe callback signature. A library cannot hide an unenforced caller restriction merely because it verifies its Rust half. No concrete foreign library/ABI implementation is audited here.

### Volatile and assembly contracts expose hardware-specific premises

`read_volatile` distinguishes Rust-allocated memory, where ordinary validity/provenance rules remain, from non-Rust-allocation I/O memory. In the latter case hardware must define the access; provenance is irrelevant, but side effects must not affect Rust-allocated memory. Traps must immediately abort the process. Volatile remains non-atomic, ZST operations may be ignored, and hardware load splitting has no stability guarantee. Basis: **normative** API contract, [volatile](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/ptr/mod.rs#L2056).

The Reference's inline-assembly rules restrict memory effects according to operands/options, require preserved registers, and make false `pure` promises UB. `nomem`/`readonly` and synchronization permissions are contractual inputs to optimization, not inferred from instruction text. CPU features, instruction effects, ABI clobbers, interrupts and external agents must match the chosen target/ISA. Basis: **normative** + **derived**, [assembly rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#L1320).

DMA that writes into Rust buffers does not fit the MMIO exception's prohibition on affecting Rust-allocated memory. A DMA-buffer proof needs a separate external-memory/ownership protocol governing CPU/device phases, completion, cache coherence, fences and buffer lifetime before Rust references resume access. This is a **derived** required contract, not a claim that Rust forbids all DMA or that one fence establishes the protocol. No ISA/device specification was inspected sufficiently to certify a concrete DMA case.

## Boundaries

- **Not examined:** mechanized Pin/generator/cancellation resource models, projected pinned fields, suspended borrowed self-references, callback/DMA implementations, ISA/linker/device contracts and cache coherence.
- **Not examined:** Jackdaw/Rust-LAGC source/theorem implementation artifacts and end-to-end extraction correspondence. Paper models were examined at named statements; no tool was run.
- **Known not to apply:** these async fairness results do not establish unsafe memory/provenance correctness; volatile does not provide ordinary inter-thread synchronization.
- **Unknown:** complete source/model progress reflection for erased/silent transitions. No blanket async/runtime safety or fairness claim is made.

## Evidence

The preprint PDFs acquired on 2026-10-14 have SHA-256 `d22755eaee7f4a07725adda27711ea1e1b1f275760b9f46de060e69df2d32c30` (responsiveness) and `1f8421bb193e351a0a10443478a2dde25c3c1b34493f7540a54a0c1977c3d16d` (LAGC). Submission/version history verifies availability by the cutoff. `source-evidence.json` records pinned Rust contracts; `probe-results.json` and `async_drop_probe.rs` preserve input, compiler identity, commands and output. Evidence roles are **normative**, **documentation**, **source**, **execution** and explicit **derived** implications.

## Revalidation

Revalidate pin storage lifetime and every drop/cancel exit before changing a state machine. For progress, preserve the theorem's formal language, scheduler/environment assumptions, obligation definitions and infinite-trace relation. Inspect Jackdaw/source artifacts before treating the paper's implementation claims as checked tool evidence. For FFI/hardware, select exact foreign ABI/ISA/device contracts and trace ownership transfer through callback removal or DMA completion; Rust contracts alone cannot supply those effects.

*Authored by an AI agent acting on joshlf's behalf.*
