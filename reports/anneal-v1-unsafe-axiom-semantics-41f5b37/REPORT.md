# Anneal V1 `unsafe(axiom)` semantics at `41f5b37`

## Summary

Historical Anneal V1's `unsafe(axiom)` annotation is an explicit trust boundary, not a relaxed proof mode. The parser converts the annotated function specification to `FunctionBlockInner::Axiom` and forbids a `proof context` or `proof` section. Anneal then tells Charon to treat that Rust function as opaque, accepts Aeneas's external declaration for the opaque function, and separately emits the user's specification as a Lean `axiom` asserting an `Aeneas.Std.WP.spec` proposition about that external function. The Rust implementation body is therefore not used to establish the asserted pre/postcondition relation.

The practical trust boundary has two linked pieces. Aeneas supplies an uninterpreted external function in Lean because Charon did not translate the body. Anneal supplies an axiomatic theorem saying that function satisfies the user-written specification. Verified callers may reason from that theorem, but the correspondence between the real Rust body and the asserted specification is trusted. A wrong `unsafe(axiom)` specification can therefore make downstream proofs succeed while describing behavior the implementation does not have.

At the exact Aeneas revision pinned by V1, that specification is **total**, not merely partial-correctness. `Aeneas.Std.WP.spec` evaluates to the postcondition for `Result.ok`, and to `False` for both `Result.fail` and `Result.div`; Aeneas also proves `spec m P ↔ ∃ y, m = ok y ∧ P y`. Therefore an Anneal `unsafe(axiom)` contract says, under its generated preconditions, that the modeled function reaches a successful `ok` result satisfying the postcondition. It rules out modeled failure and divergence. In that precise sense, V1 `unsafe(axiom)` **did imply progress in addition to correctness**. Because the actual Rust body is opaque, however, real termination/non-panicking behavior is itself part of the trusted assertion rather than something Anneal establishes.

`--allow-sorry` is separate. Ordinary `spec` blocks can use `--allow-sorry` to let missing proof automation fall back to `sorry`; an `unsafe(axiom)` block does not need that flag because it intentionally emits an axiom and has no proof body. Consequently, a V1 run with `--allow-sorry` disabled can still contain intentional `unsafe(axiom)` trust assumptions.

One source-level edge is easy to miss: although the syntax and documentation describe `unsafe(axiom)` as an axiomatization of an unsafe function, the parser at this revision does not reject the mode merely because the Rust function is safe. It uses Rust unsafety only to reject `requires` clauses on safe functions. The later Charon and generation paths key on `FunctionBlockInner::Axiom`, not on the Rust `unsafe` qualifier. Thus the inspected source permits a safe function to enter the axiom pipeline if its annotation otherwise parses, for example when it has no `requires` clause. No fresh execution was performed to exercise that case.

This report is about the preserved V1 implementation under `anneal/v1/`. Its documentation is explicitly historical and is not current Anneal design authority.

## Applicability

The findings apply to the historical V1 source preserved at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially:

- `anneal/v1/src/parse/attr.rs` for annotation syntax and conversion to `FunctionBlockInner::Axiom`;
- `anneal/v1/src/parse/mod.rs` for propagation of the Rust function's `unsafe` qualifier into parsing;
- `anneal/v1/src/validate.rs` for proof-validation behavior;
- `anneal/v1/src/charon.rs` for `--opaque` construction;
- `anneal/v1/src/aeneas.rs` for external templates, imports, `noncomputable` handling, and `--allow-sorry` behavior;
- `anneal/v1/src/generate.rs` for generation of the user specification as a Lean `axiom`;
- V1 README and agent documentation for the intended trust interpretation.

The report characterizes source-defined pipeline behavior. It does not claim that the V1 architecture is sound, that every possible opaque Aeneas declaration behaves identically, or that current Anneal should preserve this mechanism. V1's own README labels the prototype pre-alpha and says many things are broken or unsound; current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` supersede V1 documentation as current design authority.

## Findings

### `unsafe(axiom)` selects a distinct AST state, not a proof with relaxed checking

The function info-string parser recognizes exactly `unsafe(axiom)` as `FunctionAttribute::UnsafeAxiom`. Strings beginning with `unsafe` but not matching that token are rejected with a targeted error. Generic function annotations default to `spec` mode instead.

After parsing the body, `UnsafeAxiom` rejects both `proof context` and `proof` sections and produces `FunctionBlockInner::Axiom`. By contrast, `spec` produces `FunctionBlockInner::Proof` with proof context and cases.

This makes the semantic distinction structural before Charon or Lean is invoked: an axiom block does not mean "attempt the same proof but permit failure." It means "there is no implementation proof in this annotation mode."

Basis: **source** — `anneal/v1/src/parse/attr.rs`.

### The Rust body is deliberately hidden from Charon

For every parsed function whose Anneal block is `FunctionBlockInner::Axiom`, V1 constructs the module-qualified Rust item name and passes:

```text
--opaque <module-qualified-name>
```

to Charon. The source comment states the intended effect directly: Aeneas should treat the function as external and generate an external template containing its type signature as an axiom rather than attempting to translate the body.

This is the first half of the trust boundary. The Rust body is not translated into LLBC/Aeneas functional semantics for the purpose of proving this function's behavior. Verified code can call an external model of the function instead.

Basis: **source** — `anneal/v1/src/charon.rs`.

### Aeneas's external declaration and Anneal's specification axiom are different roles

When Aeneas produces `FunsExternal_Template.lean` for an opaque function, Anneal copies it to `FunsExternal.lean` if no such file exists and imports that module into the generated project. The V1 source describes the template as containing opaque function type signatures as axioms.

Separately, Anneal's own generator maps `FunctionBlockInner::Axiom` to the Lean keyword `axiom`. The generated declaration has the same specification shape used for proved functions: it states an `Aeneas.Std.WP.spec` proposition about the translated/external function, including the generated `Pre`/`Post` structure from the annotation. The unit test `test_gen_unsafe_axiom` checks that the output contains an `axiom spec ...` declaration and an `Aeneas.Std.WP.spec (ffi p)` proposition and contains no proof block.

The external function declaration therefore gives Lean an opaque function symbol/model. The Anneal-generated axiom gives clients a behavioral theorem about that symbol. The latter is what lets downstream proofs conclude the asserted pre/postcondition behavior without a proof of the Rust body.

Basis: **source** + checked-in **test** — `anneal/v1/src/aeneas.rs` and `anneal/v1/src/generate.rs`.

### The asserted specification becomes part of the trusted computing base

Because the implementation body is opaque and the specification theorem is an axiom, a successful downstream Lean proof establishes only consequences of the asserted model. It does not establish that the real Rust implementation refines that model.

V1 documentation presents this intentionally as the escape hatch for unsafe leaves, FFI, assembly, and other behavior outside the functional model. The README says such code remains in the trusted computing base and that the programmer must axiomatically assert its behavior. The agent guide describes the intended pattern as axiomatizing un-verifiable unsafe leaf operations while using Aeneas to verify the safe glue that composes them.

For a function with a false or incomplete asserted contract, every proof that relies on the contract inherits that trust failure. This is not a failure-open path in which Anneal silently ignores a proof error; it is an explicit assumption that changes what the checker is allowed to use as a premise.

Basis: historical V1 **documentation** + **source**; the TCB consequence is **derived** from Lean axiom semantics and the source pipeline.

### Preconditions constrain clients, but do not validate the opaque implementation

The parser still accepts `requires` and `ensures` clauses for an axiom block, subject to the ordinary annotation rules. The generated specification axiom packages those conditions into the same WP-oriented interface used by proved specifications.

A `requires` clause can therefore make client use conditional: callers must establish the precondition before applying the specification theorem. It does not cause Anneal to analyze the hidden Rust body under that precondition. Likewise, an `ensures` clause specifies the promised result/post-state, but the implementation-to-postcondition connection is axiomatic.

This distinction matters for unsafe APIs. `unsafe(axiom)` can encode the intended caller obligation and promised behavior of an unsafe leaf, but the soundness of that encoding and of the leaf implementation remains trusted.

Basis: **source** — parser/generator pipeline; **derived** trust consequence.

### The axiom asserts modeled progress as well as the postcondition

V1's `anneal/v1/Cargo.toml` pins Aeneas revision `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`. At that exact revision, `Aeneas.Std.Result` has three outcomes:

```text
ok value
fail error
div
```

`Aeneas.Std.WP.theta` maps `ok x` to the requested postcondition and maps both `fail _` and `div` to `False`. `WP.spec` is exactly `theta x p`. The file proves all three simplification lemmas—`spec_ok`, `spec_fail`, and `spec_div`—and, more directly:

```text
spec m P ↔ ∃ y, m = ok y ∧ P y
```

Anneal's generated axiom is therefore not the partial-correctness proposition “if this function returns successfully, its result satisfies `P`.” It asserts that the modeled result **is** an `ok y` satisfying `P`. Under the generated `h_req` precondition, modeled panic/error and modeled divergence are excluded.

That answers the inventory's progress question affirmatively, with an important trust qualifier. Since Charon deliberately hides the Rust body, Anneal does not prove that the implementation really terminates or avoids panic. Instead, the `unsafe(axiom)` assumption *includes* that progress claim. If the Rust body diverges or panics on an input satisfying the asserted precondition, the trusted axiom is false and any downstream proof relying on it no longer justifies the real program.

Basis: **source** — V1's Aeneas pin in `anneal/v1/Cargo.toml`; pinned Aeneas `backends/lean/Aeneas/Std/Primitives.lean` and `WP.lean`; Anneal V1 generator source.

### `--allow-sorry` is a separate development mechanism

V1's proof mode uses auto-parameter machinery for omitted proofs. With `--allow-sorry`, that machinery may fall back to `sorry`; without it, V1 injects Lean syntax that rejects the `sorry` tactic and term. The generated project also writes `axiom Anneal.allow_sorry : True` only in allow-sorry mode.

None of that converts `unsafe(axiom)` into a proof. The axiom path already contains no proof case, and `generate_function` emits the `axiom` keyword directly. Therefore disabling `--allow-sorry` removes one development-time source of unchecked proof holes but does not remove intentional `unsafe(axiom)` assumptions.

A trust audit must distinguish at least these two cases: explicit application-level axioms and temporary proof holes. Treating "no `sorry`" as "no unchecked assumptions" is incorrect for V1.

Basis: **source** + historical V1 **documentation** — `anneal/v1/src/aeneas.rs`, `validate.rs`, and `docs/agent/05_proof_architecture.md`.

### `noncomputable` wrapping is an execution accommodation, not semantic evidence

Aeneas-generated functions that call an opaque axiom cannot be compiled to Lean bytecode as ordinary computable definitions. V1 works around this by wrapping generated `Funs.lean` content in a `noncomputable section`; the source comments say verification does not execute those functions directly in Lean.

This changes Lean's computability obligations. It does not supply an implementation for the opaque function, prove the axiom, or reconnect the Lean model to the Rust body. The proof-relevant trust boundary remains exactly where the external and specification axioms place it.

Basis: **source** — `anneal/v1/src/aeneas.rs`.

### The source does not enforce that axiom mode itself appears only on Rust `unsafe fn`

`parse::Visitor` passes `i.sig.unsafety.is_some()` into `FunctionAnnealBlock::parse_from_attrs`. Inside that parser, the `is_unsafe` flag is used to reject `requires` clauses on safe functions. The later match on `FunctionAttribute::UnsafeAxiom` does not test `is_unsafe`; it only rejects proof sections and creates `FunctionBlockInner::Axiom`.

The validator's proof-coverage logic applies to `FunctionBlockInner::Proof`; no later V1 validation branch inspected in this investigation adds an axiom-mode/Rust-unsafety check. The Charon and generator paths likewise dispatch on `FunctionBlockInner::Axiom`.

Thus, despite the name and documentation, the source-defined gate at this revision is narrower: a safe function cannot carry a `requires` clause, but the axiom mode itself is not rejected merely because the function lacks the Rust `unsafe` qualifier. A safe `unsafe(axiom)` function with no `requires` appears source-permitted and would enter the opaque/axiom pipeline.

This is a source-level result. No fresh V1 execution was performed to confirm a concrete safe-function specimen end to end.

Basis: **source** — `anneal/v1/src/parse/mod.rs`, `parse/attr.rs`, `validate.rs`, `charon.rs`, and `generate.rs`; final pipeline consequence **derived**.

## Boundaries

- **Historical only.** `anneal/v1/README.md` and `anneal/v1/AGENTS.md` explicitly say they describe the historical V1 prototype and are not current Anneal design authority. This report must not be read as a recommendation for V2.
- **No fresh execution.** Charon, Aeneas, Lean, and V1 Anneal were not run for this report. The pipeline and the safe-function edge are established from exact source and checked-in tests/documentation.
- **Progress is a modeled assertion.** `WP.spec` excludes Aeneas `fail` and `div`, so the axiom entails modeled successful return. This does not independently prove that the hidden Rust implementation terminates, avoids panic, or otherwise refines the Aeneas result model.
- **No claim of V1 soundness.** The report explains where trust enters. It does not prove that all non-axiomatized V1 translation or proof machinery was sound.
- **No claim that every unsafe operation requires this path.** `unsafe(axiom)` is one explicit V1 abstraction boundary. Other Aeneas/Anneal models and unsupported operations have their own behavior.
- **External-template replacement is not analyzed as a user workflow.** Source notes that Aeneas users may replace `FunsExternal.lean` with manual implementations or proofs, while V1's comment says that is not relevant to its own path. This report characterizes the default copy/import behavior.
- **The exact real-world TCB log was not reconstructed.** V1 documentation uses TCB language, but this report identifies semantic trust dependencies rather than claiming a particular serialized audit-log format.
- **The safe-function axiom case is source-permitted, not execution-observed.** A later hidden constraint could only contradict this result if it sits outside the inspected parse/validate/Charon/generator pipeline; no such constraint was found.
- **`noncomputable` does not imply unsoundness by itself.** Its significance here is only that it permits Lean definitions depending on opaque axioms to remain usable for theorem reasoning without executable bytecode.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

**Historical V1 parser and scanner — source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/v1/src/parse/attr.rs`, blob `9f352d511ca964e8c58d24206a3088608cb8aaf6`: exact `unsafe(axiom)` token, `FunctionAttribute::UnsafeAxiom`, proof/proof-context rejection, `FunctionBlockInner::Axiom`, and the only local Rust-unsafety gate on function specifications (`requires` clauses).
- `anneal/v1/src/parse/mod.rs`, blob `5f630310199c6abaafa6eee5ea674730bffd773f`: passes `sig.unsafety.is_some()` to function annotation parsing for free, foreign, impl, and trait functions.
- `anneal/v1/src/validate.rs`, blob `2259c939e4bba4b2c329b9751a2a3e86601c416c`: proof-coverage validation is conditioned on `FunctionBlockInner::Proof`; `--allow-sorry` affects proof completeness rather than changing axiom mode.

**Pinned Aeneas progress semantics — source.**

- `anneal/v1/Cargo.toml`, blob `f545b31c8e15a3cc5b5bbaf277abb9e56afc2e33`: pins Aeneas revision `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`.
- `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`, `backends/lean/Aeneas/Std/Primitives.lean`, blob `5a73ea5bfae575baf2f26e1d86ea00768d1bccea`: defines `Result.ok`, `Result.fail`, and `Result.div`.
- Same Aeneas revision, `backends/lean/Aeneas/Std/WP.lean`, blob `a599b2b6632fbfdfadbe3dcfb68ee17a6048be5d`: `theta` maps `fail` and `div` to `False`; `spec` is `theta x p`; `spec_equiv_exists` proves `spec m P ↔ ∃ y, m = ok y ∧ P y`.

Evidence role: **source**. This is the exact basis for the conclusion that `unsafe(axiom)` asserted modeled progress as well as postcondition correctness.

**Opaque extraction — source.** Same repository/revision:

- `anneal/v1/src/charon.rs`, blob `7e33bda392770d04397f7172296d9a7f25c6e180`: maps every parsed Axiom function to a module-qualified `--opaque` Charon argument and documents the intended external-Aeneas result.

**Generated Lean — source and checked-in test.** Same repository/revision:

- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: maps Axiom to the Lean keyword `axiom`; `test_gen_unsafe_axiom` checks an `axiom spec ...` declaration over `Aeneas.Std.WP.spec` with no proof block.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: copies/imports Aeneas external templates, uses `noncomputable section` for generated functions depending on opaque axioms, and implements the distinct `--allow-sorry` controls.
- `anneal/v1/src/main.rs`, blob `3d363b977df790b266fe2a0635da1c294ec1b7c2`: pipeline order from validation through Charon, Aeneas, and Lean verification.

**Historical V1 documentation.** Same repository/revision:

- `anneal/v1/README.md`, blob `2bfda6336f87bf3cd785a19286363ab13423bd7d`: V1 trust/TCB framing and explicit historical-status notice.
- `anneal/v1/docs/agent/01_philosophy_and_pipeline.md`, blob `39f0e1569e6c9f7d74722c78bdcae550e31bdb9c`: intended unsafe-leaf/opaque-function architecture.
- `anneal/v1/docs/agent/04_specifications_and_syntax.md`, blob `1b5a7a8c9f7cc25b6549bc4f2697040c72e14f71`: proof-versus-axiom syntax and statement that implementation-body proof is skipped.
- `anneal/v1/docs/agent/05_proof_architecture.md`, blob `8f7f589c629876a4696ed86f215ba1c050a4ba36`: distinct `--allow-sorry` behavior.

`trust-boundary-flow.json` preserves the pipeline/trust decomposition in machine-readable form. `source-map.json` preserves the compact evidence index and source roles.

## Revalidation

For another V1 revision, the cheapest reliable source revalidation is:

1. Inspect `parse/attr.rs` for the info-string tokens, Axiom AST state, proof-section rules, and any Rust-`unsafe` gate.
2. Inspect the parser visitor in `parse/mod.rs` to confirm what syntactic unsafety information reaches annotation parsing.
3. Inspect `charon.rs` for how Axiom functions are converted to `--opaque` roots or other translator controls.
4. Inspect `aeneas.rs` for external-template generation/copy/import behavior and any replacement of external axioms with definitions or proofs.
5. Inspect `generate.rs` for the generated declaration keyword and theorem proposition. The discriminating invariant is whether the user's behavioral contract is proved from a translated body or asserted independently.
6. Resolve V1's exact Aeneas pin and inspect `Aeneas/Std/Primitives.lean` plus `Aeneas/Std/WP.lean`. Re-check how `spec` treats successful return, failure, and divergence before making any progress/termination claim.
7. Inspect `validate.rs` and the `--allow-sorry` setup separately so intentional axioms are not conflated with temporary proof holes.

On an execution-capable surface, a minimal matrix should contain four functions: safe/spec, unsafe/spec, unsafe/unsafe(axiom), and safe/unsafe(axiom). For the last two, preserve Charon arguments, LLBC presence/absence of the body, generated `FunsExternal*.lean`, generated Anneal specification text, and Lean acceptance with `--allow-sorry` both disabled and enabled. Add a safe/unsafe(axiom) specimen with a `requires` clause as a negative control; source predicts parser rejection because `requires` is reserved for Rust `unsafe fn`.

A successful matrix would confirm the source-defined behavior for those specimens. It would not establish that the asserted axiom matches the real Rust implementation; that correspondence is precisely the trusted assumption this mechanism introduces.