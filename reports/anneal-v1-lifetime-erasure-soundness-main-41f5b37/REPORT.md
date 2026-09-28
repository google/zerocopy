# Anneal V1 lifetime erasure and the `PtrInner` soundness failure

## Summary

Anneal V1's proof-facing Rust-to-Lean adapter cannot represent a source lifetime as a parameter of an `IsValid` invariant or as an argument of a translated Rust type. The retained V1 parser explicitly discards lifetime names and lifetime generic arguments, and the generator separately ignores lifetime parameters and maps `&T` to the translated `T`. Its own regression test expects `MyStruct<'a, T>` to become `MyStruct T`.

That erasure is not merely a loss of source syntax. Zerocopy issue #3053 preserved a concrete soundness failure in which `PtrInner<'a, T>` promises that its allocation lives for at least `'a`, while `from_ref` is sound only because its input reference has that same `'a`. If a verifier cannot distinguish the sound relation

```rust
fn from_ref<'a>(ptr: &'a T) -> PtrInner<'a, T>
```

from an implementation whose input uses an unrelated `'b`, it can miss the fact that the returned pointer may outlive the allocation backing the input reference. The issue follows that gap through `Ptr::from_ref` and `Ptr::as_ref` to a safe use-after-free.

The important boundary is narrower than "Aeneas throws away lifetimes." The current reference corpus establishes that Aeneas uses Charon signature regions while constructing its functional translation and erases lifetime parameters only from the final pure type language. This report is about Anneal V1's annotation/specification layer: once V1 constructs lifetime-free Lean types and lifetime-free `IsValid` instances, a lifetime-dependent Rust validity invariant has no parameter through which to state the dependency. Any Rust-level safety claim that needs such a dependency must therefore be rejected, modeled through an explicitly justified replacement abstraction, or carried by some other proof artifact; silently treating the erased signatures as equivalent is insufficient.

## Applicability

The implementation findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically the retained `anneal/v1` parser and generator. They describe how V1 itself mirrors Rust syntax and emits Lean-facing specification scaffolding; they are not a claim that every piece of lifetime information is absent from rustc, Charon, or Aeneas internally.

The concrete counterexample comes from zerocopy issue #3053 and the source revision it cites, `c6b794933a8d49481b9dded6ed99bc339202b41d`. At that revision, `PtrInner<'a, T>` carried an invariant tying the referent allocation's lifetime to `'a`; `PtrInner::from_ref` used an `&'a T` to establish that invariant; `Ptr::from_ref` propagated the resulting inner pointer into a safe pointer wrapper; and `Ptr::as_ref` could materialize an `&'a T` from that wrapper.

The current main revision still has the same material `PtrInner<'a, T>` allocation-lifetime invariant and `from_ref(ptr: &'a T)` relationship, but this report preserves the historical revision because #3053 formulated the failure against it. The issue text itself is mutable GitHub state, so `lifetime-erasure-counterexample.json` preserves the material counterexample and source identities observed for this report.

## Findings

### V1 drops lifetime identity while mirroring Rust syntax

`anneal/v1/src/parse/hkd.rs` turns Rust syntax into a thread-safe simplified AST before generation. Four choices jointly erase the information this counterexample needs:

- `SafeType::Reference` stores only `mutability` and the referent type. It has no lifetime field.
- When mirroring path arguments, V1 retains only `syn::GenericArgument::Type`; lifetime arguments such as `'a` are filtered out.
- A generic lifetime parameter is represented only as the marker `SafeGenericParam::Lifetime`; its name and relationships are not retained.
- A lifetime where-predicate is similarly collapsed to `SafeWherePredicate::Lifetime` with no payload.

Thus `PtrInner<'a, T>` and `PtrInner<'b, T>` already have the same `SafeType` path representation, and `&'a T` and `&'b T` already have the same `SafeType::Reference` representation.

Basis: **source**.

### Generation erases the remaining lifetime markers

`anneal/v1/src/generate.rs` completes the erasure:

- `extract_generic_params` has an explicit `SafeGenericParam::Lifetime => {}` arm, so no Lean binder or argument is generated for a Rust lifetime parameter.
- It processes only type where-predicates; lifetime predicates produce no generated condition.
- `map_type` maps a reference directly to `map_type(elem)`, with the source comment stating that references are erased in the functional model.
- The retained unit test `test_gen_impl_generic_lifetimes` constructs `MyStruct<'a, T>` and asserts that the generated receiver type is `(MyStruct T)`.

The V1 design document describes the same proof-facing model at a higher level: shared references become pure values, mutable references become state-transforming inputs/outputs, and complex lifetime-bearing returns are a known limitation.

Basis: **source** + **documentation**.

### V1 `IsValid` cannot be parameterized by the erased lifetime

For a Rust type annotation, `generate_type` first calls `extract_generic_params`, builds the Lean type application from the returned generic arguments, and then emits an `Anneal.IsValid` instance for that application. Because lifetime parameters and lifetime path arguments are absent from those returned values, an annotated Rust type `PtrInner<'a, T>` can produce an `IsValid` instance parameterized by `T`, but not by `'a`.

For function specifications, V1 also automatically adds `Anneal.IsValid.isValid` obligations for ordinary arguments, return values, and post-state values of mutable-reference arguments. These obligations are useful only for facts expressible by the generated `IsValid` instance. A property of the form "the allocation backing this pointer remains alive for `'a`" cannot distinguish one erased lifetime from another if the lifetime is not represented in the instance's parameters or proof-facing value.

Basis: **source** + **derived** consequence of the generator's construction.

### The `PtrInner` invariant needs the exact input/output lifetime relation

At the historical revision cited by #3053, `PtrInner<'a, T>` requires that, for a non-zero-sized referent, the backing Rust allocation live for at least `'a`. `PtrInner::from_ref(ptr: &'a T)` establishes that obligation from the input reference's own lifetime. The equality of those two lifetime occurrences is therefore part of the safety argument, not decorative generic syntax.

Issue #3053 makes the failure concrete by considering an implementation with independent lifetimes:

```rust
fn from_ref<'b>(ptr: &'b T) -> PtrInner<'a, T> { /* ... */ }
```

The body can use the unsafe `PtrInner::new` constructor to assert the stronger output lifetime without evidence that `'b: 'a`. If a verification interface erases the distinction between `'a` and `'b`, the lifetime mismatch is invisible at the invariant/specification boundary. The issue then composes the bad `PtrInner` into `Ptr`, lets the original referent die, and obtains a reference through `Ptr::as_ref`, yielding a safe use-after-free.

Basis: **source** + preserved **issue evidence** + **derived** connection to the retained V1 erasure rules.

### The sound and unsound signatures collide in V1's proof-facing type model

For the lifetime information relevant here, V1 maps both sides of the distinction to the same shapes:

| Rust distinction | V1 proof-facing representation |
| --- | --- |
| `'a` generic parameter vs `'b` generic parameter | no generated lifetime binder |
| `&'a T` vs `&'b T` | translated `T` |
| `PtrInner<'a, T>` vs `PtrInner<'b, T>` | translated `PtrInner T` |
| lifetime where-predicate/outlives relation | no V1-generated lifetime predicate |

This is a representational collision. It does not by itself show that a particular end-to-end V1 run accepts the altered `PtrInner` implementation: acceptance also depends on which functions are translated or axiomatized, Aeneas behavior, available models, and the annotation/proof supplied. It does show that V1's own generated type and `IsValid` scaffolding cannot carry the lifetime fact needed to distinguish the historical soundness case.

Basis: **source** + **derived** comparison.

### Aeneas's earlier use of regions does not repair a missing V1 invariant parameter

The existing `rust-lifetimes-charon-aeneas-nightly-2026-05-31` report establishes an important qualification. Charon preserves signature-level lifetime information, and Aeneas uses signature regions to organize borrow abstractions and forward/backward interfaces before its final pure AST erases lifetime parameters and reference constructors. Therefore, "lifetimes are erased" must not be read as "Aeneas ignores all lifetime information before translation."

That qualification does not make V1's `IsValid` layer lifetime-sensitive. V1 independently mirrors Rust types and independently generates the `IsValid` and function-specification surface described above. Once that surface has only `PtrInner T`, there is no `'a` argument on which a `PtrInner` validity predicate can depend. An indirect effect that Aeneas used while synthesizing a functional function is not automatically a proposition available to a user-authored V1 validity invariant.

Basis: existing pinned **source-derived reference evidence** + V1 **source** + **derived** interface distinction.

### The fail-closed boundary is explicit

The historical issue proposed three classes of remedy: reject annotations that need lifetimes, avoid axiomatizing unsafe operations whose soundness depends on erased lifetime facts, or add a sound way for annotations to refer to lifetimes. For the retained V1 architecture, the reusable principle is the same: do not treat a lifetime-erased proof surface as sufficient for a Rust-level safety obligation whose truth changes when source lifetimes are changed independently.

This aligns with current Anneal's fail-closed principle but is recorded here as a V1 technical boundary, not as a new V2 design decision.

Basis: preserved **issue evidence** + current Anneal **design authority** + **derived** applicability statement.

## Boundaries

- **No fresh execution.** This report did not compile a modified `PtrInner`, run Charon/Aeneas, or execute Anneal V1. It establishes the V1 representational collision from retained source and preserves the historical counterexample. It does not claim an observed successful verification of the unsound variant.
- **Not a blanket Aeneas-unsoundness claim.** The current corpus documents that Aeneas uses region structure before pure erasure. This report does not assert that Aeneas's advertised safe-Rust translation is unsound.
- **Not every lifetime-sensitive property needs an explicit lifetime term.** A translation may soundly erase information when a theorem or abstraction argument establishes that the retained semantics suffice. The `PtrInner` example matters because its stated validity invariant itself quantifies over the duration `'a`.
- **The V1 surface can still express arbitrary Lean text.** The problem is not lexical inability to type characters resembling a lifetime; it is the absence of a generated semantic lifetime object/binder corresponding to the Rust lifetime and connected to the translated type.
- **The issue was originally framed for Hermes.** The report reuses it because the retained Anneal V1 generator independently exhibits the same relevant proof-facing lifetime erasure. It does not claim Hermes and Anneal V1 are otherwise identical systems.
- **Current V2 policy is out of scope.** Current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` determine what V2 should do. This package preserves a failure mode V2 must not accidentally recreate; it does not prescribe the mechanism V2 must use.

## Evidence

**Retained Anneal V1 source — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.**

- `anneal/v1/src/parse/hkd.rs`, blob `619d1e956ebc230aece4c13c34797d1322b1bb94`: `SafeType::Reference` lacks a lifetime; path mirroring retains only type generic arguments; lifetime generic parameters and lifetime where-predicates become payload-free markers.
- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: `extract_generic_params` discards lifetime parameters; `map_type` erases references; `generate_type` builds lifetime-free `Anneal.IsValid` instances; function generation inserts `IsValid` obligations; `test_gen_impl_generic_lifetimes` expects `MyStruct<'a, T>` to generate `(MyStruct T)`.
- `anneal/v1/docs/design/design.md`, blob `f09bf3c9ecd828fb457006853632bc824b1218df`: V1's functional reference model and its explicit complex-lifetime limitation.

**Historical counterexample — issue #3053 and its pinned zerocopy source.**

- `google/zerocopy` issue #3053, "Allow safety invariants and proofs to depend on lifetimes", created 2026-02-13 and last updated 2026-03-24 as observed on 2026-09-27. The material counterexample is preserved in `lifetime-erasure-counterexample.json` because issue text is mutable.
- `google/zerocopy@c6b794933a8d49481b9dded6ed99bc339202b41d`, `src/pointer/inner.rs`, blob `2f35d5a99d6b62ab40de995ba417b2c33f7634fd`: `PtrInner<'a, T>` allocation-lifetime invariant and `from_ref(ptr: &'a T)` justification.
- Same revision, `src/pointer/ptr.rs`, blob `bb4bacb3fab78ba17584578d3cd214fd38c9c197`: safe `Ptr::from_ref` construction and `Ptr::as_ref` conversion that make a falsely extended lifetime observable as safe Rust.

**Related current corpus evidence.**

- `reports/rust-lifetimes-charon-aeneas-nightly-2026-05-31/REPORT.md`, blob `75fa9ea86ea9e623c7735484563dc18d6e340e9c`: Charon/Aeneas lifetime propagation, signature-region use, and final pure-language erasure. This report is used only to prevent the stronger and incorrect interpretation that Aeneas discards all lifetime information before translation.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Anneal implementation, the cheapest discriminating check is a two-signature probe plus inspection of the generated specification types:

1. Define one function whose input and output share `'a` and a second whose input has independent `'b` while the output carries `'a`.
2. Use a lifetime-dependent wrapper invariant analogous to `PtrInner<'a, T>`.
3. Inspect the generated verification interface before attempting a proof. If the two functions expose indistinguishable proof obligations for the lifetime-dependent property, the dangerous collision remains.
4. If the interfaces differ, identify the exact semantic object carrying the relation: an explicit lifetime/region term, an outlives proposition, a resource token, a translation certificate, or another justified abstraction.
5. Confirm fail-closed behavior by attempting the mismatched-lifetime variant. The verifier should reject it or require an unprovable lifetime/resource obligation rather than allowing the erased form to inherit the sound case's proof unchanged.

For the retained V1 code specifically, a source-only revalidation is cheaper: inspect `SafeType`, `SafeGenericParam`, `SafeWherePredicate`, `Mirror for syn::Type`, `Mirror for syn::Generics`, `extract_generic_params`, `map_type`, and `generate_type`. Any claim that the failure has been repaired requires an end-to-end relation between source lifetime identity and the proof-facing validity/specification object; merely renaming or rearranging the erased Lean types is not sufficient.
