# RefinedRust's operational, extraction and proof acceptance boundaries

## Summary

The inspected RefinedRust artifact contains a concrete byte/provenance resource model and an adequacy theorem for finite Radium thread-pool executions. Its theorem assumes a layout algorithm, initialized state, valid entry addresses and logically typed entry points with provable preconditions. It does not prove the rustc frontend's translation correct.

Proof generation and proof acceptance are separate stages. The source supports assumed specifications and explicitly admitted proofs, while default generation does not invoke the proof checker. A usable verification result must retain the exact generated model, dependency pins, configuration, complete checked proof closure and the assumptions connecting that model to the intended Rust program.

## Applicability

The principal subject is the source archive from [Zenodo record 21636474](https://zenodo.org/records/21636474), published 2026-07-28 and acquired on 2026-10-14. Its exact SHA-256 is `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`; no upstream RefinedRust Git revision was recovered from this artifact. The package name's `v2` is a navigation handle, not a claim that the metadata declares a semantic-version release.

Inspected members lie mainly under `artifact/ACE-RISCV/verification/refinedrust/`; one retained manual proof lies under `verification/rust_proofs/`. The 2026 paper is documentary context for this extended development. The 2024 paper supplies historical context only: its omissions and evaluation are not assigned to the 2026 source by continuity.

The artifact requests frontend `nightly-2026-06-29`, Rocq core 9.1.1 and standard library 9.0.0. `theories/refinedrust.opam` declares immutable dependency pins: Iris `aa39151cf17dbfd53649a4466a6420c3dbb02a96`, stdpp `2301f95c0bf0c336b64d9f0d6cb26668ce35fd8c`, iris-contrib `35ebb0772e832eb535b20c6195375ec593c9081b`, lifetime-logic `804c0168f773731b669110872bd72e6cce05e755`. These are source-declared requirements, not a measured installed or successfully built combination. No artifact code, translation, or proof was run.

## Findings

### Adequacy quantifies concrete executions under typed entry-point premises

`rust_typing/typing/adequacy.v:93–111` states `refinedrust_adequacy` under `typePreG` and `A : LayoutAlg`. It assumes global-block allocation for the static values, an initial state containing the supplied function table and thread count, and entry-point addresses in `USize`. Its logical premise holds for every `typeGS` with `ALG = A`: given the initialized static points-to resources and function-table entries, it produces each main's function-pointer typing and a provable precondition `P`. `main_type P` has no lifetime/type arguments, unit input/output, precondition `P` and trivial final postcondition.

For an `nsteps` execution of this initial Radium thread pool, with the specified observation list, the conclusion is that every reached thread is `not_stuck`. The proof invokes specialized strong WP adequacy and initializes the required authoritative resources. This is finite-execution safety for `c_lang`, not termination or a generic source-level functional-correctness theorem. Basis: **source**.

The artifact also retains `case_studies/adequacy/output/adequacy/proofs/proof_adequacy.v`. Its `main_adequate` assembles a one-function, one-thread program with empty static lists, explicit address-distinctness/range premises and the same non-stuck conclusion. Its source main is empty. The proof imports generated code, specifications and `proof_main`, which are absent from the source archive inspected here. It is an instructive assembly specimen, not freshly checked evidence of a complete build. Basis: **source** + **derived** dependency limitation.

### Byte resources retain initialization, allocation identity and access state

Radium's `loc.v` separates an integer physical address from `ProvNone`, an allocation identifier, or function-pointer provenance. Its `mbyte` is an ordinary byte, a pointer fragment carrying a location and fragment index, or poison; a value is a list of these memory bytes. `mbyte_to_byte` can expose a pointer fragment's numeric byte and allocation identity but returns no result for poison. `val_to_loc_n` accepts a pointer only when its fragments exactly match `val_of_loc_n`; `val_to_loc` additionally checks address range. Basis: **source**, `radium/loc.v:12–23`, `val.v:82–101,115–140`.

The heap camera is an authoritative finite map from addresses to cells. A cell combines a fractional share, a lock-state camera, and agreement on allocation identifier plus memory byte. The lock-state camera distinguishes exclusive writer ownership from reader counts. Separate ghost maps track allocation metadata, allocation liveness and the function table. Range points-to assertions combine bounds with ownership of the individual bytes at offsets; freeable resources include allocation metadata and fractional liveness evidence. Basis: **source**, `radium/ghost_state.v:14–32,56–95,146–177`.

This is a concrete candidate resource design for byte-oriented verification, with distinctions that a plain map of integers would lose. It is not a proven interchangeability result with MiniRust, Stacked Borrows or Tree Borrows. The inspected provenance datatype alone is insufficient to decide the full model's alias rules. Basis: **derived** from the representation, with model comparison **unknown**.

### Layout correctness remains an explicit interface and correspondence obligation

`LayoutAlg` maps named structs/unions/enums and already-computed field layouts to optional layouts. Its laws preserve named members or variants. Struct and union results must satisfy layout well-formedness; struct padding has alignment constraints; `repr(C)` computations equal the defined C layout algorithms. Enum alignment has a stated bound. The source retains a TODO for `repr(transparent)` requirements. Names can affect results, and the field-layout premise encodes coherence.

`LayoutAlg_C` supplies a proved inhabitant by using those C algorithms for every representation. That establishes satisfaction of this interface; it does not prove agreement with rustc's default Rust representation, every target ABI, niches, or all desired transparent-layout guarantees. `refinedrust_adequacy` retains the chosen `LayoutAlg` premise. Basis: **source** + **derived**, `radium/syntypes.v:1174–1257`. A downstream proof must identify both the formal algorithm and the actual layout facts it expects to use.

### The frontend selects and encodes rustc MIR without a translation theorem here

`Procedure::new` retrieves borrow-checked MIR and `mir_drops_elaborated_and_const_checked`, maps locations between them, and stores the drop-elaborated body. Thus the source confirms a concrete dependence on rustc's internal MIR stages rather than a standalone surface-Rust operational definition. Basis: **source**, `rr_frontend/translation/src/environment/procedure.rs:53–78`.

The 2026 paper explicitly places Radium and the Rust-to-Radium encoding in the trusted base, including preceding rustc processing. Its extended generic/trait reasoning belongs to this formalized model and encoding. The 2024 theorem and evaluated Vec variant concern the earlier development; they do not establish correctness of current std implementations or this newer frontend. Basis: **documentation**; [2026 paper](https://iris-project.org/pdfs/2026-oopsla-refinedrust2.pdf), §5; [2024 paper](https://robbertkrebbers.nl/research/articles/refinedrust.pdf), §5–6.

Consequently, importing a valid Rocq proof checks the extracted subject under its assumptions. Reflecting source safety requires an additional relationship between Rust behavior and this model, with the direction strong enough to preserve bad-source executions. Ordinary compiler refinement or output equivalence alone does not provide that relationship. This is a **derived** acceptance requirement, not a theorem proved by the inspected frontend.

### Generation modes materially change the evidence that must be accepted

`rr_frontend/rrconfig/src/lib.rs:91–118` defaults `admit_proofs=false`, `no_assumption=false`, `run_check=false`, `verify_deps=false`, `no_verify=false`, and `skip_unsupported_features=true`. These source defaults do not establish the effective configuration of the published examples. They do show that emitting output is not equivalent to checking all dependent implementations.

`Mode::is_assumed` classifies `OnlySpec` and `TrustMe` as assumed. `needs_proof` selects `Prove` and `CodeShim`; `needs_def` selects `Prove` and `TrustMe`. Registration emits a diagnostic for an assumed mode when `no_assumption` is enabled. The end-to-end failure behavior of that diagnostic was not executed. `generate_proof` emits the function lemma, automation and annotated tactics, then `Admitted` when `admit_proofs` is true and `Qed` otherwise. Selecting the latter emits a checking command; successful checking still has to occur. Basis: **source**, `translation/src/procedures.rs:19–79,294–312`, `radium/src/code.rs:1263–1307`, `translation/src/lib.rs:939`.

The README describes generated code/specification/template files separately from persistent, manually editable proof files, and identifies stdlib interfaces without proofs. This separation supports proof maintenance, but a verified caller can still depend on assumed library specifications. Acceptance must account for those assumptions and the actual linked callee bodies. Basis: **documentation** in the pinned source README, corroborated by generation source.

### Automation and retained manual proofs still need a complete checked closure

Lithium's `SimplifyHyp` class contains a proof of `P -∗ Q`; `Subsume` contains proof of `P1 -∗ P2 ∗ T`. Search instances therefore supply logical entailments within the existing calculus. This supports treating tactic search as evidence construction, provided the resulting theorem and its assumptions are checked. It does not expose a portable serialized entailment certificate or an independently implemented checker. Basis: **source** + **derived**, `lithium/definitions.v:69–93`.

The retained `rust_proofs/pointers_utility/proofs/proof_ptr_byte_add_mut.v` demonstrates automatic `liRStep` plus manual arithmetic cases for wrapping offsets and zero offsets, ending in `Qed`. It imports generated implementation/specification/template modules that are absent from this source archive. A stored proof script ending in `Qed` is therefore a concrete maintenance artifact, but not evidence this inspection checked its dependency closure. Basis: **source**.

For Anneal, direct Rocq delegation would need a reproducible checked closure and semantic correspondence. Certificate import would additionally need a defined certificate language and checker semantics. Independent rechecking would need its own trusted checker and translated assumptions. These are separate acceptance routes; none was implemented or verified here. Basis: **derived** integration implications.

## Boundaries

- **Known not to apply:** the displayed adequacy theorem does not prove rustc correct, all target layouts correct, termination, a source-level functional result, or arbitrary unsafe-caller coverage.
- **Not examined:** a fresh build, real extraction/proof execution, full assumption closure, effective example configuration, all unsupported-feature handling, trait/closure/iterator rule completeness, or a cross-prover certificate format.
- **Unknown:** agreement with actual Rust provenance/alias models and a source-safety reflection theorem; exact downstream trust of assumed stdlib specifications.
- **Incomplete artifact closure:** the selected pointer proof and empty-main adequacy specimen require absent generated modules; generation may restore them, but was not run.
- **Separate scope:** MoSeL/Iris and Lithium entailment interfaces were examined in this wave. Diaframe and Quiver, full Lean parity and resource-port feasibility remain unexamined.

## Evidence

`source-evidence.json` binds inspected archive members, symbols and member SHA-256 hashes to the full artifact digest. `inspection.json` records the source-presence checks for the two selected proof closures. Evidence roles are **source**, upstream **documentation** and explicit **derived** consequences; there is no fresh execution or kernel-checking evidence.

The authoritative Zenodo API reports publication date 2026-07-28; acquired archive MD5 `29905dcfac8e796707989daf1592d965` matches the file record. The 2026 paper's acquired bytes have SHA-256 `c0cd3468e733fb2298d94ce4b4ec8870d24ebd775f8a4404f2968ebd2bcf57bd`, DOI `10.1145/3839484`; the 2024 paper SHA-256 is `421aa4110d31261cbad1ab8b7805a4a9801f4705294411c4b0f1a6541ebc40d4`, DOI `10.1145/3656422`. The 2026 source artifact and paper were publicly accessible by the observation date. Their byte identities do not establish a new release's continuity.

## Revalidation

Reacquire the exact source archive, verify its digest and declared toolchain/dependency pins, then generate one concrete selected function and retain all code/spec/template/proof inputs. Record the effective configuration, assumed modes, linked library bodies and accepted theorem assumptions. Check the entire proof closure and assemble its exact adequacy instance. Compare the chosen formal layout and operational model against the source/target configuration. When using another prover or certificate route, preserve theorem premises, source correspondence and caller quantification rather than transporting only a theorem name or successful tool exit code.

*Authored by an AI agent acting on joshlf's behalf.*
