# Aliasing models, modular logics, and source-safety transfer

## Summary

Stacked Borrows, Tree Borrows, and newer program logics retain different dynamic state and justify different theorems. Their results cannot be combined through shared terminology alone. In particular, an optimization proof that assumes source UB-freedom cannot establish source UB-freedom from a safe optimized model. Recent async results add useful progress obligations, but their abstractions do not resolve unsafe pointer or byte semantics.

## Applicability

This report compares the POPL 2020 Stacked Borrows paper, the PLDI 2025 Tree Borrows paper, pinned May 2026 Miri source, and MiniRust at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`. It also examines Peterson's author-hosted 2025 thesis, the March 2026 aliasing-logic preprint, and two October 2026 async preprints. They are separate formal subjects, not a tested common toolchain.

The October preprints were available before the observation cutoff: arXiv `2610.06003v1` was submitted 2026-10-05 and `2610.09198v1` on 2026-10-06. The latter is described as an ESOP 2027 preprint; it is not treated as an already published 2027 result. None of these research semantics is presented as normative Rust. No fresh model execution or proof artifact rebuild was performed.

## Findings

### Stacked Borrows supplies dynamic permissions and optimization proofs

The paper's `Access` finds the topmost matching stack item that grants the requested access. `Unique` and `SharedRW` grant writes; `SharedRO` also grants reads; failed lookup or permission update makes the transition stuck. Retagging creates tags and may attach call protectors. Its Coq development proves representative transformations using open simulations in the presence of unknown code. These are proofs about the paper's instrumented operational subject, not a source-to-Miri compiler theorem. Basis: **source**, paper §§6–7. [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/paper.pdf).

At the pinned Miri source, shared-reference retagging distinguishes frozen data from `UnsafeCell`, and boxes receive different permissions/protection according to pointee properties. Thus source-level type names do not determine access rights without the retagging configuration and reachable data. Basis: **source**. [Miri retagging](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L100).

### Tree Borrows preserves deferred activation and changes compatibility

In the inspected MiniRust unprotected state machine, `Reserved` survives a foreign read and becomes `Unique` on a local write; a foreign read of `Unique` makes it `Frozen`; foreign writes disable ordinary nodes. `Cell` and `ReservedIm` differ. Protected nodes additionally track local and foreign access history; a protected reserved node that has seen a foreign read rejects a later local write. Protector removal can emit a final implicit read/write. Basis: **source**, state machines. [Unprotected rules](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md), [protected rules](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_protected.md).

Retag settings also depend on `UnsafeCell` layout, `unpin`, function entry, the global `implicit_writes` parameter, and a per-function opt-out. Mutable references/boxes to a non-`Unpin` pointee are currently not retagged, with an `UnsafePinned` FIXME. A certificate must bind these parameters and type facts. Basis: **source** + **derived** binding obligation. [Retag settings](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/reborrow_settings.md#L89).

The PLDI paper reports fewer rejected tests under Tree Borrows but also cases accepted by Stacked Borrows and rejected by Tree Borrows. Therefore empirical permissiveness does not establish inclusion of their accepted program sets. Its optimization logic uses Simuliris for fair, termination-preserving contextual refinements, with restrictions on moving activation and on crossing unknown-code/protector boundaries. Crucially §5 assumes the source has no UB: source UB permits arbitrary target behavior. Basis: **source**, paper §§4–5. [Tree Borrows](https://research.ralfj.de/papers/2025-pldi-tree-borrows.pdf).

### A small source discriminator separates the models

`discriminator.rs` isolates creating a mutable reference from a raw pointer, reading through the raw pointer, then passing the reference to an empty function. The pinned upstream `sb_fails.rs` states that the raw read invalidates the reference in Stacked Borrows but leaves it reserved in Tree Borrows. This supplies a narrow compatibility discriminator. The preserved expected results are **source/documentation**, not **execution**; no result is claimed for the locally installed September toolchain. [Pinned upstream discriminator](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/tests/pass/tree_borrows/sb_fails.rs#L25).

### Modular aliasing logic now has concrete but different foundations

Peterson's thesis defines λTB with block-based value memory, explicit retagging, and sequential consistency; byte interpretation and relaxed memory remain future work. Its Iris ghost trees support permission weakening, subtree deletion, and lateral block separation. It reports mechanized adequacy and examples in Rocq. Zero-size retags still require a live block, and exclusive tag facts constrain tree recombination. The thesis names code revision `ccca9f325f909dceed4fd88008862f64296dbfd9`; the public API request returned 404, so that artifact was not inspected or rebuilt. Basis: **source** thesis, §§3.2, 4–6; code identity is **documentation**, not verified code evidence. [Thesis](https://rudynicolop.github.io/files/thesis.pdf).

Tas and Jacobs `2603.28326v1` define λPA pointers with provenance/address and fractional points-to plus reference-ending resources. The source explicitly provides no separate operational semantics: the proof rules serve as axiomatic semantics. Soundness against Tree Borrows and a VeriFast implementation remain planned. Structs and recursive freezing are gaps. Its statement that other tools are unsound is an author claim; this investigation did not audit those tools and does not adopt that verdict. Basis: **source**, `lang-syntax.tex`, `program-logic.tex`, conclusion. [Preprint](https://arxiv.org/abs/2603.28326v1).

### Source traces and async progress introduce additional obligations

Drodt's LAGC semantics separates local expression evaluation from globally composed state/event traces. It takes Rust typing/borrowing guarantees for granted and covers safe HIR, rather than proving unsafe alias compliance. Its current-thread Tokio model is quiescent-fair assuming no locally infinite computations; bounded task count and poll duration enter stronger Tokio fairness. The multi-thread runtime proof is omitted. These are model theorems, not source/runtime equivalence or provenance guarantees. Basis: **source**, `2610.06003v1` §§2, 5.5–5.6 and 7. [Source-trace preprint](https://arxiv.org/pdf/2610.06003v1).

Li, Beschastnikh and Summers' LART abstracts runtime responsiveness using monotonic completion predicates and waker obligations. `Pending` must preserve or transfer the obligation; reactors wake ready obligations and retain the rest. Theorems 1–3 connect component conditions and verification conditions to eventual progression, trusting compiler async lowering, external observations and fair scheduling. LART explicitly models runtime architecture rather than Rust itself. Basis: **source**, `2610.09198v1` §§3.2–5.4. [Responsiveness preprint](https://arxiv.org/pdf/2610.09198v1).

These progress results map to concurrency/progress and async extension questions. They do not discharge pinning, cancellation, destructor, byte, or provenance obligations for unsafe Rust. A relation that erases source steps must separately preserve fair infinite execution and needed progress; finite-result agreement is insufficient. Basis: **derived** consequence of their trace and fairness premises.

### Compatibility requires a safety-reflecting relation with explicit scope

For a verification model `M` and Rust operational subject `S`, the intended inference is `Safe(M) → Safe(S)` for all admitted source executions and callers. A usual compiler refinement `Behaviors(target) ⊆ Behaviors(source)` does not provide that inference when source UB denotes unrestricted behavior: the inclusion can hold even when the target hides a source failure.

Before composing proofs, bind both languages, revisions, configurations and program artifacts, then compare allocation/lifetime identity, alias tags and protectors, initialization/provenance fragments, effects and traces, and concurrency/fairness. Discharge each erased distinction or keep it as an assumption. Agreement on the discriminator above establishes only one local relationship. This is a **derived** proof obligation, not an implemented correspondence checker.

## Boundaries

- **Unknown:** equivalence or safety inclusion among the pinned Miri, MiniRust, PLDI Tree Borrows, λTB, and λPA subjects. No cross-model theorem was established.
- **Not examined:** complete Coq/Rocq artifacts, generic/trait lowering, exposed-provenance integration into alias logics, full relaxed-memory Rust, or a current source/runtime implementation correspondence for either async preprint.
- **Known not to apply:** LAGC's safe-HIR assumptions and LART's architectural abstractions do not justify arbitrary unsafe pointer operations.
- **Unsupported/omitted in the examined accounts:** λTB byte interpretation and relaxed memory; λPA structs and recursive freezing; LAGC's multi-thread Tokio fairness proof.
- **Not established:** pinning and cancellation correctness, destruction after suspension, all library callers, or source safety reflected through an optimized extraction pipeline.
- **Execution boundary:** installed Miri binaries were observed, but no cached interpreter sysroot was found in the checked standard cache locations. No setup, installation, or model run was attempted; this observation is not evidence about model acceptance.

## Evidence

Primary sources were inspected on 2026-10-14. Paper versions and acquired PDF SHA-256 values are in `REPORT.json`; executable artifacts were not rerun.

- Stacked Borrows DOI `10.1145/3371109`, §§6.2–6.3, Figs. 2–4, §7.2 (mechanized optimization account).
- Tree Borrows DOI `10.1145/3735592`, §§4–5, especially the source-UB premise and the protected-reference transformation restrictions. The paper references artifact DOI `10.5281/zenodo.15002703`; the record fetch failed, so neither archive identity nor proof code was independently verified.
- Rust `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: `src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs:100–160` and `tree_borrows/perms.rs:9–231` (`PermissionPriv`, transition rules); README's experimental-model qualifications.
- MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`: named state-machine/settings files and `tooling/minimize/tests/pass/tree_borrows/sb_fails.rs`, `pass_invalid_mut`.
- Peterson thesis: §§3.2, 4.2, 6.1–6.3. Code commit is reported by the thesis only.
- λPA preprint source archive SHA-256 `575b891dc5a83aaecc0e8c15bb90d7e7703bbebd5bcbf9586700b836abb6043b`; inspected named TeX files and planned-soundness conclusion.
- October arXiv submission records plus exact v1 PDFs, narrow sections named above. Placeholder TOPLAS metadata in the LAGC PDF is not a published article identity.

## Revalidation

First diff exact retag and permission definitions with their parameters. If a matching Miri sysroot already exists, run `discriminator.rs` under both explicitly selected alias models, recording toolchain hash, target, complete flags and exit status; changed or passing output supports only that example. Rebuild a pinned proof artifact before relying on its adequacy as independently revalidated evidence. To compose models, examine the relation's direction and UB treatment, then add discriminators for protector exit, integer exposure, missing provenance fragments, allocation reuse, and a fair infinite trace. Any unsupported case must remain outside the acceptance claim.

*Authored by an AI agent acting on joshlf's behalf.*
