# Kani, Crux-MIR and Soteria: model coverage and completeness of symbolic results

## Summary

These tools can provide concrete model-based evidence over selected harnesses and paths, but they expose different memory models, assumptions and completeness statuses. Kani needs adequate unwinding and explicit stub/check configuration; Crux-MIR uses a structured reference model and overrides; Soteria exposes approximation mode, fuel, alias/provenance configuration and partial outcomes.

A successful process exit is insufficient evidence of an exhaustive safety result. In the inspected Soteria artifact, `OkPartial` returns exit code zero. A useful accepted result must bind the entry point, input assumptions, model, unsupported operations, all explored/unexplored paths and the exact obligations discharged.

## Applicability

Kani is pinned to `model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`, dated 2026-10-14, declaring `nightly-2026-10-12`. Crux-MIR/Crucible source is `GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`, dated 2026-10-12. Source/member identities are retained in `source-evidence.json`.

Soteria implementation evidence is the small source artifact from [Zenodo record 19080425](https://zenodo.org/records/19080425), publication date 2026-03-18, archive SHA-256 `dc956d43369582e4a7dcecd25b2086a5c426686380965e02fcbd77920ae7c2b2`, matching published MD5 `bef244344711889712e585616a589998`. A Git revision was not recovered; exact archive bytes bind the inspected source. Current public GitHub access returned 404 via both connector and direct API; this failure is not classified as absence of the tool. The artifact is not claimed as the latest October source.

Its separate formal paper is [arXiv 2511.08729v6](https://arxiv.org/pdf/2511.08729v6), released 2026-04-20, SHA-256 `aaa53c109e55944981b147ae63209ce6a85c38b94e5800b967fa01b8f0e57a54`. It proves a symbolic-library interface, not every Rust interpreter operation. Sources and papers were inspected on 2026-10-14, with no verifier execution, fresh proof checking or performance reproduction.

## Findings

### Kani completeness is conditional on harness bounds and enabled obligations

The unwinding guide explains that an insufficient loop bound fails an unwinding assertion and can leave other properties undetermined. A passing unwinding obligation can establish that no further iterations are needed for the chosen harness/input domain; the result is then exhaustive within that model/domain rather than merely a truncated trace sample. It does not remove explicit harness size or value assumptions. Basis: upstream **documentation**, `tutorial-loop-unwinding.md`.

`call_cbmc.rs` selects the unwind limit from CLI, harness annotation or default. It can disable unwinding assertions, memory-safety checks and other checks. It deliberately replaces some C-style shift/overflow checking with Rust-specific instrumentation and passes `--no-malloc-may-fail`. Thus the model/check configuration is part of the theorem-like claim a future agent might extract from the result. Basis: **source**, `call_cbmc.rs:328–330,376–408,824–830`.

A complete bounded result needs all relevant checks enabled, no failed/unreachable required cover obligations, adequate unwind checks, and a faithfully modeled entry/input/environment. A liveness claim or all-library-caller claim needs further evidence. This is a **derived** acceptance condition, not a completeness certificate emitted by this investigation.

### Kani UB checks and contracts have explicit model and assumption limits

The pinned UB guide lists alias/reference-lifetime rules, data races, several intrinsic/ABI/target issues and invalid values as incomplete or delegated areas. Those are documentary coverage claims; source-level initialization instrumentation was separately inspected. `check_uninit/mod.rs` injects checks/updates and unsupported-operation checks for selected memory operations. That confirms a concrete checking mechanism without establishing coverage of every Rust value invariant, provenance rule or UB class. Basis: **documentation** + **source**.

Contracts and stubs change the checked subject. Ordinary `#[kani::stub]` replaces a function on a per-harness basis and requires separate justification of that replacement. Contract checking and `stub_verified` permit a caller to use an abstract behavior after the corresponding implementation contract is established in its own harness/model. The transform source distinguishes checking/replacement modes, and the documentation notes return-value havoc. Neither syntax proves that all effective preconditions, modifies sets, stubs and bounds are appropriate for the original linked program. Basis: **source** + **documentation**, `transform/contracts.rs`, contract/stubbing guides.

The result guide distinguishes success, failure, unreachable and undetermined obligations, and explains why an unsatisfiable cover can expose incompleteness. Preserve those obligation-level results rather than collapsing them into one process status.

### Crux-MIR's structured references and overrides determine its subject

The README describes symbolic-input assertion checking and limits unsupported unsafe operations, symbolic capacities without a finite upper bound, and some references/function pointers in constants/statics. Unsupported calls can fail translation/simulation; the documentation suggests adding overrides. These are precise tool boundaries rather than proof that every accepted Rust operation follows one complete normative model. Basis: **documentation** in the pinned source.

`Mir/Intrinsics/Reference.hs` represents a reference by a root (Crucible reference cell, global or constant) and a typed path through structures, variants, optional values, vectors and related components. This is a structured symbolic reference model. The inspected definitions are not a byte/provenance operational semantics equivalent to Rust's full alias model. `Overrides.hs` supplies custom primitive behavior and turns assertions into Crucible obligations; the correctness of an override belongs in trust unless separately established. Basis: **source**.

`MethodSpec.hs` defines method-spec/override interfaces but explicitly puts concrete implementations in SAW's separate `crux-mir-comp` component. This is a real compositional integration hook, not evidence this package inspected its specification validity, equivalence checker or proof acceptance. Those parts remain research gaps. A future zerocopy experiment should identify the target function and every reached intrinsic/override before measuring compatibility.

### Soteria approximation mode controls what solver uncertainty means

The artifact's `solver_result.ml` takes `Unknown` branches in OX mode and drops them in UX mode; known satisfiable branches are taken and known unsatisfiable branches dropped. Its core `Symex` library separately tracks unexplored branches and give-up reasons. This implements a distinction between over-approximate coverage and under-approximate bug search; one mode's absence of errors must not be interpreted using the other's coverage claim. Basis: **source**.

The paper's Theorem 6.1/E.6 preserves mode-soundness through composition when both constituent computations already satisfy it. Theorem E.7 additionally assumes a mode-approximate solver for branching: OX must not lose feasible paths; UX must not invent feasible paths. Symbolic interpretations connect abstract and concrete values. This conditional library theorem does not prove the concrete Rust interpreter, frontend, solver or each custom symbolic primitive correct. Basis: **documentation**, §6/Appendix E of the versioned paper.

An OX error needs feasible-path/model evidence before it becomes a source-program counterexample. An error-free UX run is not exhaustive verification. These are **derived** consequences of the approximation interfaces.

### Soteria exposes alias rules and incomplete coverage as configuration

The inspected Tree Borrows implementation has Reserved, Unique, Frozen, interior-mutable, Disabled and UB states, plus strong/weak protectors and separate local/foreign read/write transitions. `tree_state.ml` installs tags and calls the borrow logic; `interp.ml` protects passed references and removes protection on return. This is actual model implementation evidence, beyond recognizing a Tree Borrows label. The standalone strong-protector rejection check in `tree_state.ml:675–689` is commented out with a FIXME in the deallocation path; other checks still run. This is an observed model-coverage concern, not an executed demonstration of a particular admitted bad program. Compatibility with another Tree Borrows revision or normative Rust remains a separate question. Basis: **source**, `tree_borrow.ml`, `tree_state.ml`, `interp.ml`.

The artifact config can disable alias checking; its default provenance mode is permissive, and recursive validity/approximate floating-point checking default to warning. Recursive validity is documented as only one level deep. The frontend defaults to Obol while also offering Charon; compile-skipping and target controls exist. Those settings make a blanket “all Rust UB checked” inference unsupported, even with Tree Borrows enabled. Basis: **source** + upstream **documentation**, `config.ml`.

### Partial exploration can still produce a zero exit code

On fuel exhaustion, the core records unexplored branches and stops that continuation. The Rust WPST driver executes OX mode, reads that count, warns that errors may have been missed when explicit fuel limits apply, and returns a partial flag for an otherwise error-free run. `outcome.ml` maps `OkPartial` to exit code zero alongside `Ok`; errors/fatal outcomes have different codes. Expected-error harness mode also remaps outcomes, so its flag must accompany result interpretation. Feasible unsupported operations instead produce give-up/error handling. Basis: **source**, `symex.ml:460–467,561–569,654–663,769–792`, `analyses/wpst.ml:90–153`, `outcome.ml:3–19`.

This is a source-derived acceptance discriminator, not an executed reproducer. An integration relying only on status code would merge complete and incomplete outcomes that the tool itself distinguishes. It must retain the partial flag, fuel, unexplored count, solver unknowns and unsupported/warning status.

### Model results, certificates and source guarantees are distinct artifacts

Kani's bounded obligations, Crux's symbolic/override obligations and Soteria's model paths can all be useful complementary evidence. A counterexample trace, complete unwind check and inductive invariant solve different obligations. None of the inspected interfaces supplies a general independently checked source-safety certificate or liveness argument.

For a certificate architecture, an untrusted engine may propose a trace, invariant or abstract summary; a smaller checker must validate the corresponding transition, inductiveness/entailment and coverage obligations under a compatible model. This is a **derived** role distinction. The current research establishes several result-meaning constraints; building an Anneal checker or reproducing a benchmark remains future engineering/measurement.

## Boundaries

- **Known constraints:** finite input/capacity assumptions and configurations remain part of the result; model-level alias/provenance differences prevent automatic interchangeability.
- **Not examined:** a real zerocopy harness, end-to-end run, full Kani UB implementation matrix, SAW compositional/equivalence implementation, all Soteria operation rules or independently checked certificates.
- **Unknown:** Rust source-safety reflection/correspondence sufficient to lift each model result to all intended source behaviors.
- **No current-source claim for Soteria:** access failed; the pinned artifact is an earlier public subject, not an invented October Git revision.
- **No liveness/completeness overclaim:** bounded error-free results need explicit coverage evidence; `OkPartial` and exit zero remain different observations.

## Evidence

`source-evidence.json` binds both Git source pins and eleven inspected Soteria archive members. The source-archive digest and published MD5 were verified. Versioned paper dates precede the observation date. Evidence is direct source/documentation plus derived acceptance constraints, with no actual verifier execution. Public-access failures and the exact fallback artifact are retained here rather than interpreted as missing implementation support.

## Revalidation

Choose one precise harness/API and bind input assumptions, target/compiler, flags, checks, unwind/fuel limits, contracts and stubs/overrides. Record obligation status and coverage independently from exit code. For each memory operation, inspect the model/rule actually executed and its unsupported paths. Verify completeness conditions before claiming exhaustive safety for that harness. For a source-level or independently checked result, add the translation/model correspondence and a defined certificate/checker; do not infer them from another tool's similar syntax or a generic symbolic-library theorem.


*Authored by an AI agent acting on joshlf's behalf.*
