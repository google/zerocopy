# Charon closure representation and translation at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`
(0.1.210), Charon represents a Rust closure as an explicit state type plus the
appropriate `FnOnce`/`FnMut`/`Fn` trait implementations and call methods. The
state type is a struct whose anonymous fields are the compiler-reported capture
types. A closure that captures shared references therefore carries shared
reference fields; a closure that mutates through a capture carries a mutable
reference field; and a consuming closure can carry a captured value directly.

The inferred closure kind controls which call traits exist. `FnOnce` always
exists. An `FnMut` closure also has `FnMut`, and an `Fn` closure has all three
traits. Charon places the closure's translated body on the call method matching
the inferred kind and synthesizes the less-specific supertrait methods as
shims. `FnOnce` takes the state by value, `FnMut` takes `&mut state`, and `Fn`
takes `&state`; ordinary closure arguments are packed into the tuple required
by Rust's `Fn*` traits.

This representation preserves several distinctions that matter to verification:
capture state is explicit data, consuming versus mutating versus shared
invocation is explicit in the receiver, and closure generics/lifetimes are not
flattened into one undifferentiated binder. Charon separately tracks lifetimes
from captured upvars, higher-ranked closure signatures, and the receiver
borrow used by `call`/`call_mut`.

A non-capturing closure coerced to a function pointer gets an additional
synthetic top-level function. That wrapper constructs the empty closure state
and dispatches through the closure's `FnOnce` implementation, so the function
pointer still reaches the closure semantics rather than bypassing them.

No fresh Charon or rustc execution was performed. The report uses the pinned
translation source and checked-in golden LLBC fixtures. Those golden outputs are
preserved upstream execution evidence, not newly generated results.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

It covers ordinary Rust closures as represented in Charon's ULLBC/LLBC:
captured state, closure kind, generated `Fn*` implementations, call-method
receivers and argument tuples, closure-specific lifetime handling, nested
closures, and non-capturing closure-to-function-pointer coercions.

This report does not cover async closures, generators/coroutines, or future
state machines. Those have distinct compiler representations and are separate
#3720 subjects. Drop behavior is described only where a generated closure call
shim visibly consumes/drops the state; Charon's general destructor semantics are
a separate subject.

## Findings

### Charon deliberately desugars closures into explicit state plus `Fn*` machinery

`translate_closures.rs` states its model directly: Rust closures behave like
ADTs that automatically implement `FnOnce`, `FnMut`, and/or `Fn`. Charon
therefore converts a closure into:

1. a struct holding the closure state (the upvars);
2. trait implementations for the closure's supported `Fn*` traits;
3. call-method declarations implementing `call_once`, `call_mut`, and/or
   `call`.

This is not merely a pretty-printing convention. The generated state type,
trait references, methods, and bodies are ordinary Charon declarations that
other translated items refer to.

Basis: pinned Charon **source**.

### Closure identity is compiler structural identity, not a source-level name

Closures are anonymous Rust expressions, but Charon assigns them normal item/type identities derived from rustc/hax definition identity. Pretty output uses structural names such as `foo::closure` or nested `foo::closure::closure`.

The existing local/nested-items report establishes the broader rustc identity model. The important closure-specific fact is that the generated ADT, trait impls, and call methods all point back to one closure definition identity.

Basis: Charon **source** + preserved **execution** output.

### Captured variables become anonymous fields with compiler-derived capture types

`translate_closure_upvar_tys` reads the closure's `upvar_tys` from Hax/rustc and
translates each type. `translate_closure_adt` then creates one anonymous private
struct field per translated upvar type.

The translation does not reconstruct capture mode from closure syntax. The
compiler-facing closure description has already decided the capture types.
Consequently, verification should reason from the actual generated field types
rather than from a source-level heuristic such as "`move` means every field is
owned."

The checked-in `closure-fn.out` fixture preserves a closure state with two
shared-reference fields, while `closure-fnmut.out` preserves a mutable-reference
field. `closure-fnonce.out` preserves a state field containing a non-`Copy`
value by value.

Basis: Charon **source** + preserved upstream **execution** artifacts.

### A `move` closure can still store a reference value

The fixture `closure-capture-ref-by-move.rs` first creates a mutable reference
and then moves that reference into a closure. The golden output represents the
closure as:

```text
struct closure<'_0> {
  &'_0 mut i32,
}
```

and constructs it by moving the reference into field 0.

Thus the source keyword `move` describes how the closure captures the variable;
it does not imply that Charon replaces the variable's type with the referent's
type. If the moved variable itself is `&mut T`, the explicit closure state
contains `&mut T`.

Basis: fixture **source** + preserved upstream **execution** artifact.

### Charon records the inferred closure kind as `Fn`, `FnMut`, or `FnOnce`

The serialized AST has a `ClosureKind` enum with exactly:

- `Fn`,
- `FnMut`,
- `FnOnce`.

`ClosureInfo` records the kind, the always-present `FnOnce` implementation, an
optional `FnMut` implementation, an optional `Fn` implementation, and the
higher-ranked closure signature.

The translator maps Hax's compiler-derived closure kind directly to this enum.
It does not infer the kind from Charon's own inspection of the body.

Basis: pinned Charon **source**.

### `FnOnce` always exists; stronger reusable call traits are added according to closure kind

`translate_closure_info` constructs implementations according to the familiar
Rust hierarchy:

- an `FnOnce` closure gets `FnOnce`;
- an `FnMut` closure gets `FnOnce` and `FnMut`;
- an `Fn` closure gets `FnOnce`, `FnMut`, and `Fn`.

The golden fixtures preserve exactly these sets. `closure-fnonce.out` contains
only the `FnOnce` implementation for the closure. `closure-fnmut.out` contains
`FnOnce` and `FnMut`. `closure-fn.out` contains all three.

This matters when a downstream proof uses a closure through a generic bound:
the available Charon trait impls encode which calling modes Rust permits.

Basis: Charon **source** + preserved upstream **execution** artifacts.

### Invalid strengthening combinations are rejected internally

The closure-body builder treats combinations such as asking an `FnOnce` closure to implement `FnMut` or `Fn` as impossible and panics if such a translation path is requested. The impl set is constructed so those combinations should not occur.

This is an internal invariant of the translator, not a user-facing support claim beyond rustc's closure-kind classification.

Basis: Charon **source**.

### Call methods make ownership of the closure state explicit

Charon constructs the receiver of each generated call method according to the
target trait:

- `FnOnce::call_once` receives the closure state by value;
- `FnMut::call_mut` receives `&mut` closure state;
- `Fn::call` receives `&` closure state.

The remaining closure parameters are bundled into one tuple, matching the
`Fn*<Args>` trait shape. For example, a two-argument `Fn` closure is represented
with a method shaped like:

```text
fn call(&closure_state, (arg0, arg1)) -> Output
```

rather than as a free function that silently captures ambient variables.

Basis: pinned Charon **source** + preserved upstream **execution** artifacts.

### The actual closure body lives on the method matching the inferred closure kind

For the method whose target kind equals the compiler-inferred closure kind,
Charon translates the closure's MIR body normally. Rustc's closure body is
initially shaped as if the logical parameters were the state followed by each
individual closure argument. Charon rewrites that body to match the `Fn*`
method ABI:

1. it inserts the tupled `Args` local;
2. shifts subsequent local IDs;
3. unpacks tuple fields into the original argument locals at the start of the
   body.

The checked-in outputs show this directly. The `Fn` fixture's substantive
arithmetic body is on `Fn::call`; the `FnMut` fixture's substantive mutating
body is on `FnMut::call_mut`; and the consuming fixture's substantive body is on
`FnOnce::call_once`.

Basis: pinned Charon **source** + preserved upstream **execution** artifacts.

### Supertrait call methods are explicit shims, not duplicate source bodies

When a closure supports a stronger reusable call mode, Charon still needs the
less-specific supertrait methods.

For an `Fn` closure:

- `Fn::call` contains the translated closure body;
- Charon synthesizes `FnMut::call_mut` by shared-reborrowing the mutable state
  receiver and calling `Fn::call`;
- `FnOnce::call_once` uses rustc's closure-once shim, which borrows the owned
  state as required, dispatches onward, then accounts for consuming the state.

For an `FnMut` closure:

- `FnMut::call_mut` contains the translated body;
- `FnOnce::call_once` uses rustc's closure-once shim to call through the mutable
  receiver and consume the closure state.

A pure `FnOnce` closure needs no more-permissive shim.

The golden `Fn` and `FnMut` fixtures preserve these forwarding bodies. A proof
should therefore not count `call`, `call_mut`, and `call_once` as three
independent translations of the source closure body.

Basis: pinned Charon **source** + preserved upstream **execution** artifacts.

### `FnOnce` shims make state consumption and drop visible

The preserved `Fn`/`FnMut` fixture outputs show `call_once` taking the closure
state by value, borrowing it to call the reusable method, and then executing a
drop of the closure state before return.

This is important negative space: the reusable `call`/`call_mut` body and the
consuming `call_once` wrapper are not interchangeable for resource reasoning.
Even when both eventually invoke the same user closure logic, consuming the
closure state can add drop behavior.

This report does not attempt to justify Charon's general drop semantics; it only
records the closure shim structure that is visibly present.

Basis: preserved upstream **execution** artifacts + pinned translator **source**.

### Closure lifetimes come from three distinct binder sources

`translate_closures.rs` calls out three lifetime sources that must not be
conflated:

1. lifetimes in captured upvars/state;
2. late-bound lifetimes in a higher-ranked closure signature;
3. late-bound receiver lifetimes on `call`/`call_mut`.

The translator has separate helper paths for closure references that need the
closure signature's late-bound lifetimes and for call-method references that
need method-borrow lifetimes. `FnOnce` does not add a receiver-borrow lifetime
because its state is passed by value; `Fn` and `FnMut` do.

This explicit binder bookkeeping is a material part of the representation, not
an incidental naming detail. The nested/generic closure golden fixtures contain
several independent lifetime parameters around state, arguments, and generated
methods, demonstrating the shape preserved by the implementation.

Basis: pinned Charon **source** + preserved upstream **execution** artifacts.

### The closure's output type is the `FnOnce::Output` associated type

Generated closure `FnOnce` impls bind the trait's `Output` associated type to the translated closure return type. `FnMut` and `Fn` inherit access to that output through their parent-trait relationships.

Pinned output shows the `FnOnce` proof/impl carrying `type Output = ...` and higher `Fn*` traits referring through implied clauses to the same result type.

Basis: Charon **source** + preserved **execution** evidence.

### Closure calls become explicit trait/impl calls

Where rustc resolves a concrete closure call, Charon can emit a direct reference to the generated closure `Fn*` implementation method with the appropriate generic/proof arguments. Generic `Fn`/`FnMut`/`FnOnce` calls use the same trait-evidence machinery described in the traits/generics report.

A downstream consumer therefore sees closure invocation through the same explicit function/trait call representation used for other trait methods, rather than a special opaque closure-call opcode.

Basis: Charon **source** + preserved **execution** evidence.

### Parent generics and trait clauses can flow into closure declarations

Closures defined inside generic functions or impls are not isolated
monomorphic objects. The closure state and generated impls can carry the
surrounding type parameters, regions, and trait clauses needed by captures and
the body.

The nested-closure golden output preserves closure state types and `Fn*`
implementations parameterized by outer `T` and trait clauses. This is consistent
with Charon's dedicated closure generic/binder machinery.

A downstream verifier should therefore identify a closure by its declaration
plus generic arguments, not by a source location/name alone.

Basis: pinned Charon **source** + preserved upstream **execution** artifact.

### Nested closures become nested synthetic closure declarations

A closure body can itself contain another closure. The checked-in nested
fixture preserves successive synthetic closure items under the enclosing
closure name, each with its own state type and generated `Fn*` machinery.

This demonstrates that Charon's closure model composes structurally: inner
closures do not disappear into one outer function body. They remain semantic
items that can themselves capture values and carry generics/lifetimes.

The exact rendered synthetic names are implementation-facing identities, not a
Rust source API promise. Name stability across Charon/rustc revisions is not
established here.

Basis: preserved upstream **execution** artifact + pinned **source**.

### Non-capturing closures can be translated to ordinary function-pointer targets

Rust permits a non-capturing closure to coerce to a function pointer. Charon
handles this as a special closure item kind, `ClosureAsFnCast`.

`translate_stateless_closure_as_fn` requires the closure's upvar list to be
empty. It generates a top-level function with the closure's ordinary parameter
list. The synthetic function:

1. builds the tuple of call arguments;
2. constructs the empty closure state;
3. calls the closure's `FnOnce` method.

The `closure-as-fn` golden output preserves an empty `struct closure {}`, a
synthetic `closure::as_fn`, a cast of that function to `fn()`, and the original
closure's body reachable through the generated `Fn*` calls.

Thus the coercion does not erase the closure semantics merely because the final
value is a plain function pointer.

Basis: pinned Charon **source** + fixture **source** + preserved upstream
**execution** artifact.

### Capturing closures are not treated as function-pointer coercions by this path

The source asserts that only stateless closures can use the synthetic
closure-as-function translation. A closure with upvars has state that an
ordinary Rust `fn` pointer cannot carry, so this particular lowering is
inapplicable.

This is a source-defined precondition, not an empirical survey of every
possible coercion expression.

Basis: pinned Charon **source**.

### Closure destruction remains a separate semantic boundary

Closure structs participate in ordinary drop/destructor handling because captured state can need destruction. Golden output includes generated `Destruct` implementations/drop references for closure structs.

At this pinned revision some displayed closure drop bodies are marked `<missing>` under the tested MIR/configuration, consistent with the broader pinned drop/body-availability limitations. The existence of an explicit closure `Destruct` relation therefore does not by itself establish complete destructor semantics.

Basis: preserved **execution** evidence + existing drop/support reports.

### Closure opacity can remove generated method bodies

Generated closure methods still pass through Charon's item opacity machinery.
`translate_closure_method` and `translate_stateless_closure_as_fn` both emit
`Body::Opaque` when the item's effective opacity hides private contents.

Therefore the existence of a closure state type or `Fn*` trait implementation
does not, by itself, prove that the user closure body is present. Selection and
opacity remain part of the theorem domain.

Basis: pinned Charon **source**.

### The Charon closure struct is a semantic desugaring, not a Rust layout promise

Charon models closure state as a struct with fields corresponding to upvar
types. This representation is useful for reasoning about captured values and
borrows.

The report does **not** establish that Charon's synthetic field order or struct
layout is a normative description of rustc's physical closure layout suitable
for arbitrary byte-level or FFI reasoning. Rust closure types are compiler
generated, and this report inspected Charon's semantic translation rather than
a language-level closure-layout guarantee.

For Anneal, treating the state struct as an abstraction of captured state is
supported by the pinned translator. Treating it as a cross-version stable ABI
would require separate rustc/layout evidence.

Basis: Charon **source** + **derived** boundary.

## Boundaries

- No fresh Charon or rustc execution was performed.
- Checked-in `.out` files are preserved upstream execution evidence and were
  not regenerated on this surface.
- Async closures, generators, coroutines, and `Future` lowering are excluded.
- General drop/destructor correctness is excluded. This report records the
  generated closure `Destruct` relation and observed missing-body boundary, but
  does not treat that relation as complete destructor semantics.
- The report does not prove rustc's closure-capture inference correct or stable.
  Charon consumes compiler/Hax closure kind and upvar types.
- It does not establish a stable source-level or cross-version naming scheme for
  synthetic closure items.
- It does not establish physical memory layout/ABI of compiler-generated Rust
  closure types.
- It does not exhaustively characterize monomorphized closure translation.
  Pinned source contains dedicated monomorphization paths and tests, but the
  report focuses on the ordinary generic representation.
- It does not characterize trait objects containing `dyn Fn*`; ordinary closure
  `Fn*` implementations are the subject here.
- It does not claim every captured projection is represented as a whole
  source-variable field. The authoritative input is the compiler/Hax
  `upvar_tys`/closure representation for this revision.
- It does not prove that every higher-ranked lifetime pattern is supported.
  It records the explicit binder architecture and checked-in coverage.
- It does not benchmark nested-closure depth or closure-heavy workloads.

## Evidence

**Primary subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/bin/charon-driver/translate/translate_closures.rs`, blob
  `2081ec4748d1073dd5af306fcacf7829c5596d0c`: state-struct lowering,
  closure kind mapping, `Fn*` impl construction, call signatures, tuple
  argument rewriting, forwarding shims, binder handling, and stateless
  closure-to-function conversion.
- `charon/src/ast/types.rs`, blob
  `548be29762fdc4f4d1cd652537db6f54065ff6ee`: serialized
  `ClosureKind`/`ClosureInfo` representation.

**Preserved ordinary-closure fixtures:**

- `charon/tests/ui/simple/closure-fn.rs`, blob
  `36192da46944f1adffced595896bfce975a28fb0`, with golden output blob
  `226ced674eb6b1c024ea68681c372479dfb92d58`: shared-reference captures;
  explicit `Fn`, `FnMut`, and `FnOnce` impls; forwarding shims.
- `charon/tests/ui/simple/closure-fnmut.rs`, blob
  `bcef676f69c81c4fe1789fe330dea0e4d7cbc6e1`, with golden output blob
  `77daed76a5ed02317de011a1a9af4163ee56c6dd`: mutable-reference state;
  `FnMut` body plus `FnOnce` shim.
- `charon/tests/ui/simple/closure-fnonce.rs`, blob
  `083fc57b18c04084e1d93fd945d9af9b7face11a`, with golden output blob
  `152baeb93b819637c8012fbb33d28e35de090b9f`: by-value non-`Copy`
  capture and `FnOnce`-only call machinery.
- `charon/tests/ui/simple/closure-capture-ref-by-move.rs`, blob
  `43124675c82e261691eafbab1c5a9907fa0df6d5`, with golden output blob
  `2100f8ddfd12acd72ae9ed4e2ab4e65de2a0b762`: moving an `&mut` variable
  into the closure preserves an `&mut` closure-state field.

**Preserved nesting/coercion fixtures:**

- `charon/tests/ui/simple/nested-closure.rs`, blob
  `6766f92b74737e10dbef7ed4190698c4e33a290d`: nested generic closure
  input; its checked-in golden output preserves nested synthetic closure
  state/types/impls.
- `charon/tests/ui/closure-as-fn.rs`, blob
  `a117c96b160d2f0c395dc8a1e8c856d1d5d40e13`, with golden output blob
  `ab5667ddbf5b01f4df5ace7e326c2fc054ed0754`: non-capturing closure
  converted through synthetic `closure::as_fn`.

Evidence roles:

- the Rust implementation and AST declarations above are **source** evidence;
- checked-in `.out` files are preserved upstream **execution** evidence;
- statements about what Anneal may safely infer from the representation are
  explicitly **derived** boundaries rather than upstream guarantees.

No fresh **execution** evidence was produced for this report.

## Revalidation

For a later Charon revision, first diff:

1. `translate_closures.rs`, especially closure state construction,
   `translate_closure_info`, call-method signatures, shim generation, and
   `ClosureAsFnCast`;
2. `ClosureKind` and `ClosureInfo` in the serialized AST;
3. Hax closure arguments/upvar representation consumed by Charon;
4. the `closure-fn`, `closure-fnmut`, `closure-fnonce`,
   `closure-capture-ref-by-move`, nested-closure, and closure-as-fn golden
   fixtures.

On an execution-capable surface, use one compact fixture matrix containing:

- no-capture `Fn`, `FnMut`, and `FnOnce` closures;
- captures by shared reference, mutable reference, `Copy` value, and non-`Copy`
  value;
- `move` of an owned value and `move` of a reference value;
- multiple captures with disjoint modes;
- nested closures;
- generic captures and where-clauses;
- a higher-ranked closure argument;
- a non-capturing closure coerced to each applicable function-pointer shape;
- closure calls through generic `Fn`, `FnMut`, and `FnOnce` bounds.

For each case preserve the exact source, rustc/Charon revision, final LLBC, and
serialized metadata. Check:

- state field types and count;
- `ClosureKind`;
- which `Fn*` implementations exist;
- receiver types on each call method;
- tuple argument shape;
- which method contains the source body versus a forwarding shim;
- lifetime binders on state, signature, and receiver;
- generated `as_fn` presence/absence;
- errors or `has_errors`.

That experiment would revalidate this representation for the exact tested
revision. It would not establish cross-version physical layout or async
closure/coroutine semantics.