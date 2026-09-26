# Local and nested Rust item identity for Anneal

## Summary

Rust permits definition-like constructs inside bodies that do not have ordinary
module paths.

The most important categories are:

1. **item declarations inside blocks**, such as an inner `fn`, `struct`, `enum`,
   `type`, `const`, `static`, trait, impl or macro item where syntax permits;
2. **closures**, each of which has a unique anonymous type and can capture its
   surrounding environment;
3. **anonymous/inline constants**, including array-length/const-generic
   expressions and `const { ... }` blocks;
4. **compiler-synthesized definitions**, such as constructors, opaque types,
   nested statics and synthetic coroutine bodies;
5. **macro-generated definitions**, which can occur in module or block scope
   even when the original source contained no explicit item spelling.

A block-local **item declaration** is still an item, not a closure. Its name is
scoped to the containing block, but the Rust Reference says it receives **no
canonical source path**, and neither do sub-items it declares. It does not
implicitly capture the containing function's generic parameters, parameters, or
locals. In this respect it behaves more like a nested static declaration
environment than like lexical closure code.

A closure is the opposite on capture: each closure expression has a unique,
anonymous closure type and can capture outer variables by shared reference,
mutable reference, copy or move. rustc nevertheless gives the closure a
definition identity using anonymous `DefPathData::Closure` plus a sibling
disambiguator under its compiler parent.

Anonymous constants and inline consts similarly receive DefIds even though they
have no user name. The examined compiler maps both `DefKind::AnonConst` and
`DefKind::InlineConst` to `DefPathData::AnonConst`. Other hidden/synthetic
constructs receive their own DefPathData variants.

The resulting compiler paths are therefore **structural paths**, not Rust source
paths. A definition may be represented internally with components such as:

```text
outer_function::{closure#0}
outer_function::{constant#1}
outer_function::InnerType
```

while no legal canonical Rust path can name those components from elsewhere.
The precise debug spelling is implementation detail; the important fact is that
rustc can distinguish them using parent identity + definition kind/name +
disambiguator.

For Anneal, item discovery must not be restricted to module-level,
path-nameable items. If the verification promise covers code reachable through
a selected target, local item bodies, closures, inline constants and
macro-generated local definitions can contain unsafe or otherwise
verification-relevant behavior. Compiler-derived IDs and body ownership are the
reliable discovery/identity boundary.

## Applicability

Normative claims apply to:

```text
rust-lang/reference
ad35aca481751a06afeb23820a672b0f3b11a476
```

Compiler identity findings apply to:

```text
rust-lang/rust
f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1
1.98.0-nightly
```

Anneal implications apply to:

```text
google/zerocopy
0eca5581c6d27aaeaba4c421f7bf2a26bdd50228
```

This report is about **definitions and bodies** in local/nested positions, not
the later question of which of them Charon/Aeneas currently serializes.

## Findings

### 1. Items can be declaration statements inside blocks

The Reference defines item declarations as one of the two kinds of declaration
statement.

**Basis: normative.**

A body can therefore contain named items without creating a nested module.

### 2. A block-local item is scoped to the containing block

Its name is available over the block's item scope rather than being a member of
an enclosing module's public path namespace.

**Basis: normative.**

### 3. Block-local items have no canonical Rust path

The Reference explicitly states that an item declared within a statement block
"is not given a canonical path nor are any sub-items it may declare."

**Basis: normative.**

This is a direct reason a source-path-only identity scheme is incomplete.

### 4. Block item names can be visible before textual declaration

Item scopes extend from the start of the block to its end.

**Basis: normative.**

This differs from local `let` bindings, whose scope starts after the binding.

### 5. Local item declarations do not implicitly capture outer locals

A nested function cannot directly refer to a containing function's local
variables merely because it is lexically nested there.

**Basis: normative.**

### 6. Local item declarations do not implicitly capture outer function parameters

The Reference's "no implicit capture" rule includes parameters.

**Basis: normative.**

### 7. Local item declarations do not implicitly capture outer generic parameters

A nested item inside a function cannot use the containing function's generic
type/lifetime/const parameters merely by lexical nesting.

**Basis: normative.**

### 8. A local item may declare its own generics

It can introduce fresh generic parameters according to ordinary item syntax.

**Basis: normative.**

### 9. Inner items may shadow outer function generic parameter names

The Reference explicitly allows items declared within functions to introduce
generic parameters with the same spelling as the outer function's generics.

**Basis: normative.**

This reinforces that the inner item is a separate definition environment.

### 10. Local item identity still has a compiler parent

rustc's `DefPath` model assigns every definition a parent chain even when no
canonical Rust path exists.

**Basis: compiler identity model.**

### 11. Named local items can use ordinary namespace path data under an internal parent

A nested function/type still has `ValueNs(name)` or `TypeNs(name)` definition
data, but the parent may itself be a function/body-owning definition rather than
a module.

**Basis: DefPath design + language local-item behavior.**

The resulting internal path is not promised to be a nameable Rust path.

### 12. Local impls have anonymous impl identity

An impl block has `DefPathData::Impl`, and sibling impls are distinguished by
disambiguators.

**Basis: rustc source.**

### 13. Associated items inside a local type/impl gain identities under that local parent

They are compiler definitions even though the containing type itself has no
canonical external path.

**Basis: DefPath parent structure.**

### 14. Each closure expression has a unique anonymous type

The Reference states this directly.

**Basis: normative.**

Two textually identical closure expressions are different closure types.

### 15. Closures capture their environment; ordinary function items do not

This is one of the language-level distinctions between a closure and an inner
`fn`.

**Basis: normative.**

### 16. Closure capture mode is inferred unless `move` forces capture by value

The compiler can infer shared-reference, mutable-reference, copy or move
capture.

**Basis: normative.**

### 17. Capture behavior affects the closure's implemented call traits

Depending on captures and behavior, closure types implement `Fn`, `FnMut` and/or
`FnOnce`.

**Basis: normative.**

### 18. Captured variable types affect auto traits

Closure `Send`/`Sync` behavior depends on captured values.

**Basis: normative.**

Thus a closure is semantically more than its visible body expression.

### 19. rustc assigns closures DefIds

`DefKind::Closure` maps to `DefPathData::Closure`.

**Basis: rustc source.**

### 20. Closure DefPath components are anonymous

There is no source identifier to hash. Sibling closures under the same parent
are separated by integer disambiguators.

**Basis: definitions source.**

### 21. Closure identity can therefore be ordering-sensitive

Inserting another closure of the same anonymous path-data kind before an
existing sibling can change the sibling's disambiguator.

**Basis: DefPath disambiguation model.**

This is an implementation-stability caveat, not a language-semantic change.

### 22. A closure can contain unsafe Rust

A closure body is an ordinary Rust expression/body for language purposes.

**Basis: language semantics.**

Any whole-program UB-freedom analysis must cover reachable closure bodies.

### 23. A closure can itself contain local item declarations

Because closures have block/expression bodies capable of containing blocks and
items, local definition nesting can continue under a closure context.

**Basis: language composition.**

### 24. Async closures/coroutines introduce additional synthetic structure

The examined DefPathData includes `SyntheticCoroutineBody`, and closure/coroutine
lowering can generate implementation-specific bodies.

**Basis: rustc source.**

### 25. Anonymous const expressions receive definitions

rustc has `DefKind::AnonConst` and `DefPathData::AnonConst`.

**Basis: rustc source.**

### 26. Inline `const { ... }` blocks also use anonymous-const path data

The compiler printing source explicitly notes that its AnonConst path handling
covers both `DefKind::AnonConst` and `DefKind::InlineConst`.

**Basis: rustc source.**

### 27. Const blocks have no separate named const item

The Reference describes inline const blocks as constant values without defining
new constant items.

**Basis: normative.**

Yet the compiler still needs a definition/body identity for analysis and
evaluation.

### 28. Inline consts support local type inference

Unlike named const items, the compiler can infer the const block's type from
context.

**Basis: normative.**

### 29. Const contexts execute under target semantics

Const evaluation uses the compilation target's semantics, such as target
pointer width, rather than host semantics.

**Basis: normative.**

This can matter for verification of anonymous consts in cross compilation.

### 30. Anonymous consts occur in many syntactic roles

Examples include array lengths, const generic arguments/defaults, enum
discriminants, repeat counts and other const contexts.

**Basis: Rust language structure + compiler DefKind.**

### 31. Anonymous const identity is structural, not textual-value identity

Two separate `{1 + 1}` anonymous constants are separate definitions even if
they evaluate to the same value.

**Basis: DefPath/body model.**

### 32. Named constants can have nested anonymous definitions

A named item's type/body can contain anonymous consts or closures whose parent
chain is below the named definition.

**Basis: structural identity model.**

### 33. Constructors have their own compiler identity

Tuple/unit struct or enum-variant constructors use `DefPathData::Ctor`.

**Basis: rustc source.**

The constructor can share a human spelling with its type/variant but is a
separate value-namespace definition.

### 34. Opaque `impl Trait` types can have hidden compiler definitions

`DefPathData::OpaqueTy` represents such anonymous/implicit type definitions.

**Basis: rustc source.**

### 35. RPITIT can create anonymous associated types

The examined compiler has `AnonAssocTy(method-name)` path data.

**Basis: rustc source.**

A source method signature can therefore induce a compiler definition not
directly written as an associated `type` item.

### 36. Statics can induce nested static data definitions

`DefPathData::NestedStatic` exists for additional static data referred to by a
static.

**Basis: rustc source.**

### 37. Macro-generated definitions participate in the same identity system

After expansion, generated functions/types/impls/closures/consts are ordinary
compiler definitions under their expansion context/parent.

**Basis: proc-macro and rustc identity reports.**

### 38. Generated local definitions may have no original source declaration span containing their full syntax

Their spans can point into macro input/call sites or generated expansion
locations.

**Basis: proc-macro span model.**

### 39. Human-readable `def_path` strings are not guaranteed legal Rust paths

Anonymous components and disambiguators can appear in debug representation.

**Basis: rustc definitions source.**

### 40. Compiler body ownership is a better traversal key than canonical source path

Local functions, closures and anonymous consts can each own bodies/definitions
without having externally nameable paths.

**Basis: compiler architecture + language rules.**

### 41. A module-only item scan misses local function bodies

A verifier that only enumerates module children by named path will not discover
nested item declarations unless it recursively traverses compiler definitions.

**Basis: synthesis.**

### 42. A named-function-only scan misses closures

Closures can contain arbitrary Rust behavior and have their own compiler body
identity.

**Basis: synthesis.**

### 43. An executable-code-only scan can miss compile-time const behavior relevant to validity/layout

Anonymous constants can affect types, array lengths, discriminants and generic
instantiations even when they have no runtime function body.

**Basis: language semantics.**

### 44. Local source identity should retain parent context

The spelling `inner` is reusable in many functions/blocks. A useful diagnostic
name needs at least enough parent context to tell those definitions apart.

**Basis: scope + DefPath model.**

### 45. Persisted stable identity should not depend only on anonymous sibling ordinal

rustc's DefPathHash necessarily includes the disambiguator, but an external
system promising refactoring-stable proof attachment may need a higher-level
reassociation strategy after edits.

**Basis: compiler identity limitation + derived engineering consequence.**

This is not a criticism of rustc's identity; its stability target differs from
a proof database's UX target.

### 46. A local item can be unreachable yet still compile/type-check

Item definitions in a body are part of the compiled crate's semantic
environment even if no runtime call reaches them; whether MIR is instantiated/
codegenerated depends on later compiler stages.

**Basis: Rust item semantics.**

This distinction will matter in later MIR/reachability reports.

### 47. Reachability and existence are separate dimensions

A closure/local item can have a DefId/body but never be invoked.

**Basis: compiler model.**

Anneal may need to distinguish "definition discovered" from "behavior reachable
under the verified subject."

### 48. Charon coverage of local definitions must be measured, not assumed

The Rust/rustc evidence establishes that these definitions exist. It does not
establish that pinned Charon serializes every local item/closure/anon const in
the form Anneal needs.

**Basis: boundary discipline.**

That question belongs in the later Charon coverage reports.

## Boundaries

### Not examined

- Full HIR `BodyOwnerKind` taxonomy.
- MIR creation policy for every anonymous definition.
- Codegen/monomorphization of unreachable local functions.
- Async/closure lowering details in full.
- Generator/coroutine state-machine fields.
- Capture precision and borrow checker internals.
- CTFE semantics beyond identifying anonymous consts as separate bodies.
- Charon's local-definition serialization.

### Unknown

- Which local/synthetic definition classes Anneal V2 will expose as first-class
  proof subjects.
- Whether user annotations will ever target closures or anonymous constants
  directly.
- How proof attachment should survive edits that perturb anonymous
  disambiguators.

### Known not to apply

- A block-local item does not implicitly capture containing function locals.
- A closure does capture its environment.
- A block-local item has no canonical Rust path merely because rustc can print a
  DefPath.
- An inline const is not a named const item even though rustc gives it a DefId.

### Attractive stronger conclusions not established

This report does **not** establish that:

- every anonymous definition needs a separate user-visible Anneal proof;
- all anonymous definitions reach runtime;
- DefPath sibling ordering is unstable under every edit;
- local items should be rejected;
- closure generated types should be exposed to users by rustc debug names.

## Evidence

### Rust Reference

```text
rust-lang/reference
ad35aca481751a06afeb23820a672b0f3b11a476
```

Primary files:

- `src/statements.md`
  - item declaration statements;
  - block scope;
  - absence of canonical path;
  - no implicit capture.
- `src/names/scopes.md`
  - item statement scope;
  - generic-parameter capture/shadowing rules.
- `src/expressions/closure-expr.md`
  - unique anonymous closure type;
  - captures.
- `src/expressions/block-expr.md`
  - const blocks/inline consts.
- `src/const_eval.md`
  - const contexts and target evaluation.

### rustc

```text
rust-lang/rust
f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1
```

Primary identity files:

- `compiler/rustc_hir/src/definitions.rs`
  - anonymous DefPathData;
  - disambiguators.
- `compiler/rustc_hir/src/def.rs`
  - mapping DefKinds including Closure, AnonConst, InlineConst, impl, opaque and
    synthetic definitions to DefPathData.
- `compiler/rustc_span/src/def_id.rs`
  - definition identity.

### Preserved probe

`probes/local.rs` contains:

- duplicate-spelling inner functions in separate outer functions;
- an inner generic type and impl;
- closures;
- array-length anonymous consts;
- inline const blocks;
- macro-generated local items.

Suggested compiler inspection uses `-Zunpretty=hir-tree`; a rustc-driver probe
can enumerate all local DefIds and print parent/DefPath/DefKind.

The fixture was not executed during this investigation.

## Revalidation

### 1. Recheck language rules

Confirm current Reference statements for:

- block item scope;
- canonical path absence;
- outer capture restrictions;
- closure unique types/captures;
- inline consts.

### 2. Recheck DefPathData taxonomy

Inspect:

```text
compiler/rustc_hir/src/definitions.rs
compiler/rustc_hir/src/def.rs
```

Record new/removed anonymous/synthetic categories.

### 3. Run HIR inspection

```console
rustc +nightly-2026-05-31 -Zunpretty=hir-tree probes/local.rs \
  > hir-tree.txt
```

Use only as an inspection aid.

### 4. Run a rustc-driver definition enumerator

For each local definition, record:

```text
DefKind
DefPath
DefPathHash
parent
span
body owner status
```

Verify that inner items, closures and anonymous consts are distinct.

### 5. Perturb source ordering

Insert a closure/anonymous const before an existing one and compare DefPathHash
changes. This directly measures the refactoring sensitivity of anonymous
disambiguators at the target compiler revision.

### 6. Recheck Charon

Measure which definition classes appear in LLBC and how they are identified
before deciding Anneal's coverage/annotation model.
