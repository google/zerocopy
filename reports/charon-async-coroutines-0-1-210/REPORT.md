# Charon async, generator, and coroutine support at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`
(0.1.210), Charon does **not** support Rust coroutine bodies end to end. The
pinned translator rejects coroutine types, coroutine/coroutine-closure MIR
aggregates, `Yield` and `CoroutineDrop` terminators, and coroutine-only resumed
state assertions. It also refuses to register rustc's
`SyntheticCoroutineBody` as an ordinary translated item.

The upstream test suite records even an empty:

```rust
pub async fn f() {}
```

as a known failure. Its checked-in diagnostic reports both "Coroutine types are
not supported yet" and "Coroutines are not supported", then fails translation.
That fixture is preserved execution evidence for the exact pinned revision.

Charon's AST does contain names for compiler/built-in traits such as `Future`,
`AsyncFn`, `AsyncFnMut`, `AsyncFnOnce`, and `Coroutine`. Their presence should
not be mistaken for coroutine execution support. They are part of Charon's
trait-proof/builtin taxonomy; the Rust representations needed to translate an
ordinary async state machine still hit explicit unsupported branches.

For Anneal, the practical boundary is therefore simple at this pin: a
verification subject requiring translation of ordinary Rust `async fn`,
generator/coroutine state, suspension/resumption, or `yield` cannot be claimed
covered by the Charon 0.1.210 pipeline. Such a subject must be rejected,
excluded by a precisely justified boundary, or handled by a different semantics
before a Rust-level verification claim can include it.

No fresh compiler or Charon execution was performed. The report relies on exact
pinned source plus the checked-in known-failure fixture.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

"Coroutine" follows the compiler/Charon terminology at this revision and covers
the compiler representation underlying ordinary Rust async/generator-like
state machines. The report uses "async" for Rust async syntax such as
`async fn`, and "generator/coroutine" for the lowered state-machine forms and
MIR operations.

Ordinary non-async closures are a separate subject and are supported through
Charon's explicit closure-state/`Fn*` lowering. The existence of that closure
machinery does not imply support for coroutine closures.

## Findings

### Charon's type translator explicitly rejects coroutine types

Hax exposes rustc coroutine types to Charon as `hax::TyKind::Coroutine`. The
pinned `translate_types.rs` matches that variant and immediately registers an
error:

```text
Coroutine types are not supported yet
```

There is no alternative Charon type node constructed in this branch.

This is a direct semantic boundary: once a translated Rust item's type requires
the compiler coroutine type, normal type translation fails.

Basis: pinned Charon **source**.

### MIR construction of coroutine state is explicitly unsupported

The MIR body translator handles `mir::AggregateKind::Coroutine` and
`mir::AggregateKind::CoroutineClosure` together. Both enter an error branch:

```text
Coroutines are not supported
```

Thus support is not merely missing from pretty-printing or final
serialization. Charon rejects the MIR rvalue that materializes coroutine
state.

Basis: pinned Charon **source**.

### `yield` and coroutine-drop control flow are not translated

The terminator translator groups `TerminatorKind::CoroutineDrop` and
`TerminatorKind::Yield` with unsupported terminators and raises an error.

A coroutine semantics needs to account for suspension, later resumption, and
dropping a suspended state. These are precisely the control-flow operations
that this pinned translator does not map into Charon's body representation.

Basis: pinned Charon **source** + **derived** semantic consequence.

### Coroutine-only resumed-state assertions are also rejected

rustc MIR has assertions for invalid resumption states, including resuming
after drop, panic, or return. Charon's pinned assertion translator rejects:

- `ResumedAfterDrop`,
- `ResumedAfterPanic`,
- `ResumedAfterReturn`

with "Coroutines are not supported".

This is additional evidence that the unsupported boundary is systemic rather
than one missing type case: state-machine safety checks themselves lack a
Charon translation at this revision.

Basis: pinned Charon **source**.

### Synthetic coroutine bodies are not registerable Charon items

`translate_crate::base_kind_for_item` maps ordinary Rust definition kinds into
Charon item kinds. `SyntheticCoroutineBody` is instead in the group that emits:

```text
Cannot register item ... with kind ...
```

and returns no Charon item kind.

Therefore compiler-generated coroutine body identities are not treated like
ordinary functions that can simply be reached through Charon's item work
queue.

Basis: pinned Charon **source**.

### Hax can describe coroutine types even though Charon cannot translate them

The pinned Hax-facing type layer contains a `TyKind::Coroutine(ItemRef)` case
converted from rustc's coroutine type. Charon therefore does not fail because
the compiler front-end is incapable of naming the type at all; the unsupported
boundary appears later in Charon's own type translation.

This distinction is useful when revalidating a future version. A later Charon
could plausibly retain the same Hax input shape while adding a semantic Charon
representation.

Basis: pinned Charon **source**.

### Builtin trait names for async/coroutine concepts do not establish body semantics

Charon's type-level builtin taxonomy includes entries for:

- `AsyncFn`,
- `AsyncFnMut`,
- `AsyncFnOnce`,
- `Coroutine`,
- `Future`.

Those identifiers let Charon classify compiler-provided trait proofs or lang
items. They do not override the explicit rejection of coroutine types,
aggregates, terminators, and resumed-state assertions.

A corpus search or downstream consumer must therefore not use the presence of
`Future`/`AsyncFn` names as evidence that Charon can verify an async function's
state-machine behavior.

Basis: pinned Charon **source** + **derived** negative-space conclusion.

### The upstream suite marks a minimal `async fn` as a known failure

The pinned fixture `charon/tests/ui/simple/coroutine.rs` is:

```rust
//@ known-failure
pub async fn f() {}
```

The checked-in output contains two diagnostics:

```text
error: Coroutine types are not supported yet
...
error: Coroutines are not supported
...
ERROR Charon failed to translate this code (2 errors)
```

The example has no await point, user-written `yield`, captured state, or complex
control flow. Even this minimal async function crosses the unsupported
compiler-coroutine boundary.

This preserved failure is stronger than an inference from untested source
branches: the upstream repository records the unsupported behavior as an
expected fixture at the pinned revision.

Basis: fixture **source** + preserved upstream **execution** artifact.

### Ordinary async functions cannot be treated as opaque successful translations by default

The pinned fixture fails translation rather than successfully emitting a
complete Charon declaration whose body is merely `Opaque`.

That matters for verification orchestration. "Charon does not understand the
body, so downstream verification may model it" is not the observed default
behavior for the minimal async fixture. The Charon stage itself reports errors.

A deliberately introduced abstraction could still be possible in a different
architecture—for example, excluding async definitions from the verified domain
or providing an earlier model—but that would be an explicit Anneal design
choice, not behavior established by Charon 0.1.210.

Basis: preserved upstream **execution** artifact + **derived** consequence.

### `async fn` coverage cannot be inferred from successful translation of its callers

Charon's dependency/reachability machinery can encounter signatures or other
items without translating every implementation body. Separately, coroutine
types and bodies are unsupported.

Therefore a successful translation of surrounding synchronous code does not
establish that an async callee's semantics were represented. A Rust-level claim
covering the async behavior needs explicit evidence that the relevant coroutine
definition was translated with a justified semantics; this pinned version
cannot supply that evidence through its ordinary coroutine path.

Basis: pinned Charon **source** + **derived** Anneal boundary.

### This unsupported boundary is different from nontermination

A coroutine may suspend and later resume; that is not the same semantic
phenomenon as an ordinary function simply diverging forever. Charon's failure
here is a missing representation for compiler coroutine state/control-flow,
not a conclusion that async execution should be modeled as nontermination.

Conflating the two would erase state, wake/resume behavior, drop of suspended
state, and possible completion values.

Basis: **derived** from the rejected coroutine operations; no stronger async
runtime semantics are claimed.

## Boundaries

- No fresh Charon, rustc, or Cargo execution was performed.
- The checked-in `.out` file is upstream preserved execution evidence; it was
  not regenerated on this surface.
- The report establishes lack of ordinary coroutine translation at the pinned
  revision. It does not prove every syntactic form involving the `Future` trait
  fails. A hand-written synchronous type implementing `Future` may exercise
  trait machinery without itself being a compiler coroutine.
- It does not characterize async runtime/executor behavior, wakeups, pinning, or
  polling semantics because Charon does not reach a supported coroutine body
  representation from which those could be studied.
- It does not characterize post-0.1.210 work or plans for coroutine support.
- It does not treat non-async closures as unsupported; those use a distinct
  supported lowering covered by the closure report.
- It does not claim every future compiler `SyntheticCoroutineBody` shape will
  retain the same identity or MIR operations.
- It does not test an exhaustive matrix of `async` blocks, async closures,
  explicit coroutine syntax, `await`, or nested async constructs. The source
  rejection points are broader than the one minimal fixture, while the
  preserved execution evidence is specifically an empty `async fn`.

## Evidence

**Primary subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/bin/charon-driver/translate/translate_types.rs`, blob
  `35bef6ea79992c65ea934413765fa95f631274e6`: explicit rejection of
  `hax::TyKind::Coroutine`.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob
  `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: explicit rejection of
  coroutine/coroutine-closure aggregates, `CoroutineDrop`, `Yield`, and
  resumed-state assertions.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob
  `53536c6df6e241c9655840f6b1f8a4aca2113f90`: refusal to register
  `SyntheticCoroutineBody` as a translated item kind.
- `charon/src/bin/charon-driver/hax/types/ty.rs`, blob
  `470ed2ff4d992efe30f8c4a09a3676111f304003`: Hax-facing
  `TyKind::Coroutine(ItemRef)`.
- `charon/src/ast/types.rs`, blob
  `548be29762fdc4f4d1cd652537db6f54065ff6ee`: builtin trait taxonomy
  including `AsyncFn*`, `Coroutine`, and `Future`.

**Preserved known-failure fixture:**

- `charon/tests/ui/simple/coroutine.rs`, blob
  `6ac66497f6dce1e319dbb253bca0c2428c81384e`: minimal `async fn` marked
  `known-failure`.
- `charon/tests/ui/simple/coroutine.out`, blob
  `102ff14a6b823671ad2a59b398ddd9bf3d3feece`: preserved **execution**
  diagnostics showing coroutine type/body rejection and failed Charon
  translation.

Evidence roles:

- translator/Hax/AST implementation is **source** evidence;
- the checked-in diagnostic is preserved upstream **execution** evidence;
- verification consequences are explicitly **derived**.

No fresh **execution** was performed.

## Revalidation

For a future Charon revision, first diff:

1. `translate_types.rs` for `TyKind::Coroutine`;
2. `translate_bodies.rs` for coroutine aggregate, `Yield`, `CoroutineDrop`, and
   resumed-state handling;
3. `translate_crate.rs` for `SyntheticCoroutineBody`;
4. the Hax coroutine input representation;
5. `tests/ui/simple/coroutine.rs` and its expected output.

If any rejection disappears, perform a capable-surface probe containing:

- an empty `async fn`;
- `async fn` with one and multiple `.await` points;
- async blocks with captured shared/mutable/owned values;
- cancellation/drop while suspended;
- nested async blocks;
- async closures if supported by the tested Rust revision;
- an explicit coroutine/yield fixture if the language/toolchain exposes one;
- a hand-written non-coroutine `Future` implementation as a control.

Preserve ULLBC/LLBC and error status. Determine whether Charon represents:

- the state type and discriminant/state transitions;
- suspension and resumption;
- values live across suspension;
- poll/yield/resume inputs and outputs;
- drop/cancellation of suspended state;
- panic/unwind edges;
- trait relationships (`Future`, `Coroutine`, `AsyncFn*`);
- source correspondence.

Only after those semantics exist should the #3720 coroutine subject be
reclassified from "unsupported" to a richer representation report.