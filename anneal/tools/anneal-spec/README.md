<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `anneal-spec`: Rust-syntax Anneal specifications

This workspace lets Rust authors state Anneal function contracts in Rust syntax
and lowers them to a declarative `Spec.lean` built on
`Trusted.MirSemantics.Contract` (`FnContract`, `ContractSignature`,
`ContractSpecs`), emitting explicit `isUnsafe`, parameter `MirTy`, and return
`MirTy` signatures for every `ContractEntry`.

- `lower/` (`anneal-spec-lower`): the parser, checker, and emitter, plus a CLI
  that writes or checks `Spec.lean` and `spec_span_map.json`, or span-free
  per-claim Lean modules.
- `macros/` (`anneal-spec`, imported as `anneal`): inert attributes that only
  check clause syntax, for crates that choose to depend on them.

Nothing here is part of Anneal's trusted computing base, but the lowering
decides what every Rust-syntax specification means. The generated `Spec.lean`
is therefore the authoritative review artifact: it is committed next to its
Rust source so reviewers read the exact Lean proposition, `cargo-anneal`'s
`spec-preflight` and target audit check it like any hand-written
specification, and `--check` rejects a stale file.

The workspace lives in Anneal's untrusted `tools/` zone
(`anneal/tools/anneal-spec/`), outside Anneal's `trusted/` TCB and `tests/`
suites. It does not depend on any `anneal/` crate, and no `trusted/` or
`tests/` crate may depend on `tools/`. CI runs its unit tests and formatting
checks, and checks that every generated specification in `zerocopy/proofs` is
fresh.

## Attaching specifications

Both forms share one grammar and lower to byte-identical `Spec.lean`.

Out-of-tree companion file (no change to the specified crate):

```rust
anneal::external_spec! {
    impl PointerMetadata for usize {
        #[anneal::spec(total, ensures(|ret| ret == elems))]
        fn from_elem_count(elems: usize) -> Self;
    }
    mod util::macros {
        #[anneal::spec(total)]
        unsafe fn __unsafe();
    }
}
```

Inline, without any dependency (`rustc` strips an inactive `cfg_attr` before
name resolution; add `--check-cfg=cfg(anneal)` to silence `unexpected_cfgs`):

```rust
#[cfg_attr(anneal, anneal::spec(total, ensures(|ret| ret == elems)))]
fn from_elem_count(elems: usize) -> usize { elems }
```

The `anneal` cfg may enable only these attributes, one per `cfg_attr`:
`#[cfg_attr(anneal, A)]` where `A` is `anneal::spec(..)`, `anneal::pure`, or
`anneal::vacuous_ok(..)`. Anything else conditional on
`anneal` (`#[cfg(anneal)]`, a compound predicate such as
`cfg_attr(any(anneal, test), ..)`, or `cfg!(anneal)`) would make the crate the
specifications describe differ from the crate users build, so it is rejected in
every input file. Because a macro can assemble a cfg predicate from tokens
that are never adjacent in the source, the identifier `anneal` is reserved: it
may appear only as such a `cfg_attr` predicate or at the start of an
`anneal::{spec,pure,vacuous_ok,external_spec}` path.

Lower a unit with:

```sh
cargo run -p anneal-spec-lower -- --src-root SRC --out-dir OUT FILE...
cargo run -p anneal-spec-lower -- --src-root SRC --check OUT FILE...
```

Every item is checked, but `--target PATH` (repeatable) and `--claim C` lower
only the selected items, together with the `#[anneal::pure]` helpers they
reach. `--list-targets` prints every specified item, its claim, file, and kind
(`inline` or `external`) as JSON, without type-checking clauses.
`--format v2-module --crate-slug S --claim C` writes the selection as the Lean
module `OUT/Specs/S/C.lean` in namespace `Specs.S.C` (spelled
`Specs.«S».«C»`), with no span map: it records no Rust source positions, so
edits elsewhere in the Rust file leave it unchanged. The default `--format v1`
writes `Spec.lean` (namespace `Spec`) and `spec_span_map.json`.

## Clauses (profile v1)

| Clause | Meaning |
| :--- | :--- |
| `requires(P)` | Behavioral precondition. On an `unsafe fn` it is also the caller's safety obligation. On a safe `fn` it can never excuse undefined behavior. |
| `safety_requires(P)` | Caller safety obligation of an `unsafe fn` that does not restrict the behavioral domain. Rejected on safe functions. |
| `ensures(\|ret\| Q)` | Postcondition on normal return. |
| `terminates`, `may_diverge`, `may_unwind`, `may_panic`, `no_unwind`, `no_panic`, `total` | Effect mask. Total normal return (`terminates := true`, `noUnwind := true`) is the default; `may_diverge` permits divergence (`terminates := false`) while keeping `noUnwind := true`, and `may_unwind` / `may_panic` permit unwinding (`noUnwind := false`). Positive synonyms (`total`, `terminates`, `no_unwind`, `no_panic`) are idempotent. Contradicting `may_diverge` with `terminates`/`total` or `may_unwind`/`may_panic` with `no_unwind`/`no_panic`/`total` is rejected. Bare specs on `-> !` without a precondition or effect opt-out are rejected. `no_abort` is rejected because every contract already rules out aborting. |
| `max_steps = E` | Upper bound (`Nat`) on deterministic MIR `Step` transitions over unsigned entry arguments (an algorithmic step budget, not physical wall-clock time or hardware cycles). Implies `terminates`, rejects `may_diverge`, and rejects signed values, unary `-`, and subtraction `-` so bounds never silently clamp below zero. |
| `target = "path"` | Overrides the derived item path, in both attachment forms. Required on inherent `impl` methods. Only characters of a Rust item path are accepted. |
| `claim = "C"` | Puts the item in verification claim `C`, which `--claim C` selects. `C` is 1 to 64 ASCII letters, digits, and `_`, starting with a letter, and not an Anneal module root, a reserved Lean name, or a name such as `panic` that specifications may not use. Without it, an item is alone in the claim derived from its path: `::` becomes `__`, `<T as Tr>` becomes `impl_Tr_for_T` (`impl_Tr_for_unit` for `()`), any other character becomes `_`, and a `c_` prefix is added if the result does not start with a letter. A derived claim may not coincide with another item's claim (`<usize as PointerMetadata>::from_elem_count` is in `impl_PointerMetadata_for_usize__from_elem_count`). |
| `instantiate = [["u8"], ...]` | Generic instantiations to verify. Parsed and validated, but rejected by profile v1, which has no generics. |
| `#[anneal::pure]` | A non-recursive, side-effect-free helper usable in clauses. Its name must be an ASCII identifier other than `math`, `old`, `wrapping_*`, or `no_overflow_*`, and its parameters may not be named `Int`, `True`, `False`, `Trusted`, `Spec`, `Specs`, or `_root_`. |
| `#[anneal::vacuous_ok(reason = "...")]` | Waives the check that the precondition admits some input. |

Expressions: `true`/`false`, integer literals (with optional suffix),
parameters, the `ensures` binder, `!`, unary `-`, `&&`, `||`, `==>`
(right-associative), `<==>`, comparisons, `+ - * / %`, helper calls,
`math(e)`/`math { e }`, `wrapping_{add,sub,mul}`, and
`no_overflow_{add,sub,mul}`. Types: `bool`, `()`, and fixed-width integers.

Every integer lowers to its mathematical `Int` value via `scalarAsInt`.
Arithmetic on machine integers must say what it means: `math(a) + math(b)` is
unbounded, `wrapping_add(a, b)` is modular, and `no_overflow_add(a, b)` states
that the mathematical sum is in range. Division and remainder lower to
`Trusted.MirSemantics.intTdiv`/`intTmod` (Rust's truncating semantics, as in
`Int.tdiv`/`Int.tmod`) and require the divisor to
be a nonzero literal or guarded by `d != 0` (or `d > 0`) earlier in a `&&` or
`==>` chain or in a `requires` clause. A `safety_requires` guard does not
count outside `safety_requires`, since it is not part of the behavioral
precondition of a body that is not `unsafe`. Integer literals above
`u128::MAX` are not supported.

The following parse but are rejected by the profile v1 lowering:
`old`, `cases`, `modifies`, `ensures_err`, `ensures_unwind`, `after_expiry`,
`decreases`, `witness`, `must_reject`, references, slices, and generics.

## Diagnostics

Errors are rendered `rustc`-style with exact spans: byte offsets index the
UTF-8 source and columns count Unicode scalar values.

| Code | Rejects |
| :--- | :--- |
| `E_ANNEAL_AMBIGUOUS_SPEC_ARITH` | `+ - * / %` or unary `-` on a machine integer outside `math` |
| `E_ANNEAL_UNGUARDED_SPEC_DIV` | `/` or `%` whose divisor may be zero |
| `E_ANNEAL_EAGER_CLAUSE_JOIN` | `&` or `\|` between `bool`s |
| `E_ANNEAL_AMBIGUOUS_NEGATION` | `!a == b` and `!a != b` |
| `E_ANNEAL_CHAINED_COMPARISON` | `a < b < c` |
| `E_ANNEAL_IMPURE_SPEC_EXPR` | assignments, blocks, `if`/`match`/`let`/loops, `unsafe` helpers |
| `E_ANNEAL_OLD_IN_PRECONDITION` / `E_ANNEAL_UNSUPPORTED_OLD` | `old(...)` |
| `E_ANNEAL_SAFETY_REQUIRES_ON_SAFE_FN` | `safety_requires` on a safe function |
| `E_ANNEAL_SPEC_UNKNOWN_IDENT` / `E_ANNEAL_SPEC_UNKNOWN_FN` | unbound names (with a did-you-mean hint) |
| `E_ANNEAL_SPEC_TYPE_MISMATCH` / `E_ANNEAL_SPEC_LITERAL_RANGE` / `E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED` | ill-typed expressions |
| `E_ANNEAL_SPEC_SHADOWING` | an `ensures` binder that shadows a parameter |
| `E_ANNEAL_PURE_RECURSION` | recursive helpers |
| `E_ANNEAL_UNSUPPORTED_CLAUSE` / `E_ANNEAL_UNKNOWN_CLAUSE` / `E_ANNEAL_UNKNOWN_ATTRIBUTE` | clauses outside profile v1 |
| `E_ANNEAL_UNSUPPORTED_TYPE` / `E_ANNEAL_SPEC_UNSUPPORTED_EXPR` / `E_ANNEAL_UNSUPPORTED_BITWISE` | types and expressions outside profile v1 |
| `E_ANNEAL_DUPLICATE_TARGET` / `E_ANNEAL_DUPLICATE_CLAUSE` / `E_ANNEAL_DUPLICATE_HELPER` / `E_ANNEAL_CONFLICTING_EFFECTS` / `E_ANNEAL_UNSATISFIABLE_NEVER_EFFECTS` | duplicates, conflicting effect qualifiers, and bare `-> !` total-normal specs |
| `E_ANNEAL_IGNORED_ATTRIBUTE` | an `anneal::` item in a position the lowering does not read |
| `E_ANNEAL_BARE_OR_COMPOUND_CFG` | any use of the `anneal` cfg other than `cfg_attr(anneal, ..)` enabling `anneal::` specification attributes, and the identifier `anneal` anywhere but there or in an `anneal::` path |
| `E_ANNEAL_CLAIM_COLLISION` | a claim derived from an item's path that equals another item's claim |
| `E_ANNEAL_UNSUPPORTED_IMPORT` | `use anneal::*`, `use anneal::{..}`, or renaming the crate |
| `E_ANNEAL_INVALID_TARGET` / `E_ANNEAL_INVALID_CLAIM` / `E_ANNEAL_RESERVED_HELPER_NAME` / `E_ANNEAL_RESERVED_PARAM_NAME` | unsafe-to-emit names |
| `E_ANNEAL_UNKNOWN_TARGET` / `E_ANNEAL_EMPTY_CLAIM` / `E_ANNEAL_INVALID_OPTIONS` | a `--target` that no item specifies or that is outside `--claim`, a `--claim` with no items, or inconsistent options |
| `E_ANNEAL_TARGET_REQUIRED` / `E_ANNEAL_VACUOUS_OK_REASON` / `E_ANNEAL_EMPTY_UNIT` / `E_ANNEAL_SPEC_ARITY` / `E_ANNEAL_SPEC_SYNTAX` | malformed input |

## Generated output

`Spec.lean` spells every conversion explicitly (no `↑` coercions) and
contains no Rust line numbers, so reformatting the Rust source leaves it
byte-identical. `cargo-anneal` compiles it with `autoImplicit` disabled.
It imports only `Trusted.MirSemantics` on top of `prelude`, and every global
name it references is qualified from `Int`, `True`, `False`, `Trusted`, or
its own namespace (`Spec.pure_h` or `Specs.S.C.pure_h`,
`Trusted.MirSemantics.intTdiv`). Helper parameters become Lean binders, so
those names (and `Specs`) are reserved for them.
`spec_span_map.json` maps each generated declaration's Lean line range to the
Rust span it came from.

The CI verifier also accepts `anneal-spec` units of its own under
`tests/zerocopy/`, whose specifications come from exactly one of a companion
`spec.rs` or a `spec_sources.json` such as `{"files": ["lib.rs"]}`. The
`zerocopy` specifications that used to live there are now written inline in
`zerocopy/src` and verified through `zerocopy/proofs`, so none remain.

A `zerocopy/proofs` unit can take its specification from inline attributes,
one claim at a time. Its `spec_sources.json` binds a claim, as in
`{"files": ["lib.rs"], "claim": "zc01_usize_pointer_metadata"}`, and the unit
checks in the span-free module `Specs/zerocopy/<claim>.lean` (from
`--format v2-module --crate-slug zerocopy --claim <claim>`) as its only
specification source, with `proof.specification` set to
`Specs.zerocopy.<claim>.specs`. `verify_zerocopy.py` verifies such a unit like
any other; the `anneal-spec` verifier checks that its module is fresh, and runs
its negative controls (a falsified inline specification and a mismatched
signature must both fail to verify) on `02_unit_pointer_metadata`.

The CI verifier also checks contract uniqueness: it lists the items specified
in every `zerocopy/src` file and in every companion `spec.rs`. An item
specified in `zerocopy/src` may not also be specified in a companion file, and
must be lowered by exactly one unit: an `anneal-spec` unit whose
`spec_sources.json` names its file, or a claim-bound `zerocopy/proofs` unit
that names its file and claim. Companion files are independent fixtures and
may specify the same item differently.
