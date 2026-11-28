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
| `#[anneal::pure]` | A non-recursive, side-effect-free helper usable in clauses. Its name must be an ASCII identifier other than `math`, `old`, `abs_diff`, `wrapping_*`, `no_overflow_*`, or `saturating_*`, and its parameters may not be named `Int`, `Nat`, `True`, `False`, `Trusted`, `Min`, `Max`, `Spec`, `Specs`, or `_root_`. |
| `#[anneal::vacuous_ok(reason = "...")]` | Waives the check that the precondition admits some input. |

Expressions: `true`/`false`, integer literals (with optional suffix), the
integer constants `T::MIN`, `T::MAX`, and `T::BITS` for a fixed-width integer
type `T`, parameters, the `ensures` binder, `!`, unary `-`, `&&`, `||`, `==>`
(right-associative), `<==>`, comparisons, `+ - * / %`, `& | ^ << >>` and `!`
on integers, `e as T` casts to fixed-width integer types, the integer methods
below, helper calls, `math(e)`/`math { e }`,
`wrapping_{add,sub,mul,neg,shl,shr}`,
`no_overflow_{add,sub,mul,neg}`, `saturating_{add,sub,mul,neg}`,
`abs_diff`, `if c { a } else { b }` (with `else if` chains),
`match s { pat => e, .. }`, and blocks `{ let x = e; .. value }`.
Types: `bool`, `()`, and fixed-width integers.

Every integer lowers to its mathematical `Int` value via `scalarAsInt`.
Arithmetic on machine integers must say what it means: `math(a) + math(b)` is
unbounded, `wrapping_add(a, b)` is modular, `saturating_add(a, b)` clamps the
sum to the type's range, and `no_overflow_add(a, b)` states that the
mathematical sum is in range. The `_neg` forms negate one operand, and
`saturating_neg` takes only a signed operand, as in Rust. `abs_diff(a, b)` is
the distance between `a` and `b`, of the unsigned type of their width, as
`i8::abs_diff` returns `u8`. These intrinsics take operands of one
fixed-width integer type, even inside `math`, where their result is
mathematical. A saturating result lowers to
`(let «saturating» : Int := e; if «saturating» < lo then lo else ..)`, which
binds the exact result `e` once, and `abs_diff` to
`(Int.ofNat (Int.natAbs (a - b)))`.

Bitwise operators have Rust's meaning and precedence. `&`, `|`, `^`, and `!`
act on the two's-complement bits of their operands, which must have one
fixed-width integer type; like the intrinsics, they take machine-typed
operands even inside `math`, except that `!` on an integer inside `math` is
rejected, since there it would apply to a mathematical integer. Unsigned
operands lower through `Int.toNat` to `Nat`'s `&&&`, `|||`, and `^^^`, signed
ones through their remainder modulo `2^bits`, and `!a` to `MAX - a` or
`-a - 1`. `a << k` and `a >> k` shift by a constant `k` of any integer type
below the bit width of `a`, through `Trusted.MirSemantics.intShiftLeft`
(reduced into the type's range) and `intShiftRight` (arithmetic on signed
types). Rust panics on, or masks, a larger or non-constant amount, so those
are rejected; `wrapping_shl(a, n)` and `wrapping_shr(a, n)` take a `u32` `n`
modulo the bit width, as in Rust. In `max_steps`, these operators may supply
unsigned step counts.

`e as T` casts an integer or a `bool` to the fixed-width integer type `T`, with
Rust's precedence: tighter than every binary operator, looser than prefix `!`
and `-`, and left-associative, so `x as u16 as i8` casts twice. As in Rust,
`<` or `<<` directly after the type is rejected, since Rust reads it as the
start of generic arguments; parenthesize the cast instead. The result is the
value of `e` when it fits in `T`, and otherwise that value reduced into `T`'s
range modulo `2^bits`, through `Trusted.MirSemantics.intEmod`. Like the
bitwise operators, `e` keeps its machine type inside `math`, where the result
is mathematical; a mathematical `e`, as in `math(a + b) as u8`, is reduced
like any other value. An unsuffixed literal has Rust's default type, `i32`, so
`-1 as u8` is `255` and `3000000000 as u32` is rejected. A `bool` casts to
`1` or `0` through Lean's `if`, so it must be decidable, as the condition of
an `if` that chooses an integer must be. Any other target, including `bool`
and `()`, is rejected. In `max_steps`, a cast to an unsigned type is a step
count.

A fixed-width integer has these methods, which bind tighter than every operator,
as in Rust, so `!a.min(b)` is `!(a.min(b))`. Each intrinsic above except `math`
is also a method whose receiver is its first operand: `a.wrapping_add(b)` is
`wrapping_add(a, b)`. `a.min(b)` and `a.max(b)` lower to Lean's `Min.min` and
`Max.max`, which evaluate each operand once. `a.clamp(lo, hi)` lowers to
`Min.min (Max.max a lo) hi`; Rust panics when `lo > hi`, so its bounds must be
constants in order, and `a.max(lo).min(hi)` states the same value for other
bounds when they are in order. `a.is_power_of_two()` takes an unsigned integer,
as in Rust, and lowers to the decidable `0 < p ∧ p &&& (p - 1) = 0`, where `p`
is `Int.toNat a`, bound once by `let «power_of_two»`. Like the intrinsics, these
methods take operands of one fixed-width integer type, even inside `math`, where
their integer results are mathematical, and in `max_steps` an unsigned result is
a step count. Field accesses and other methods are rejected, as is a method call
directly after a cast, which Rust also rejects.

Four more methods follow Rust's definitions. `a.div_ceil(b)` takes unsigned
operands, as in Rust, and a divisor guarded as for `/`, and lowers to
`intTdiv (a + b - 1) b`. `a.is_multiple_of(b)` takes unsigned operands and
lowers to the decidable `intTmod a b = 0`, which needs no guard: as in Rust,
`a.is_multiple_of(0)` holds exactly when `a` is `0`, and `intTmod a 0` is `a`.
`a.rotate_left(n)` and `a.rotate_right(n)` take a `u32` `n` modulo the bit
width, rotate the `Nat` bits of `a` (its remainder modulo `2^bits`) with
`<<<`, `>>>`, and `|||`, and sign-extend a signed result. An operation that
needs an operand twice lowers to a Lean `fun` applied to the operands, as in
`((fun («n» «d» : Int) => ..) a b)`, so each operand is evaluated once and no
specification name is in the scope of the binders.

Division and remainder lower to
`Trusted.MirSemantics.intTdiv`/`intTmod` (Rust's truncating semantics, as in
`Int.tdiv`/`Int.tmod`) and require the divisor to be a nonzero literal or
guarded by `d != 0` (or `d > 0`) earlier in a `&&` or `==>` chain, by the
condition of an enclosing `if`, or in a `requires` clause. A `safety_requires`
guard does not count outside `safety_requires`, since it is not part of the
behavioral precondition of a body that is not `unsafe`. Integer literals above
`u128::MAX` are not supported.

A specification `if` is an expression, so its `else` branch is required. As in
Rust, the condition ends at the first `{`, so write `math(..)` rather than
`math { .. }` there. No binary operator may follow an `if` directly:
parenthesize the `if`, or the expression that ends with it, as in
`(r == if c { a } else { b }) && ..`. Both branches must have one type, and
untyped integer literal branches take their type from context. An `if` between
`bool`s lowers to `((c → a) ∧ (¬ c → b))`. An `if` that chooses an integer or
`()` lowers to Lean's `if c then a else b`, so its condition must be decidable:
it may test integers and `bool` arguments and return values, but may not call a
`bool` helper or name a `bool` helper parameter, which lower to arbitrary
propositions. A branch may divide by what the condition proves nonzero on its
side, as in `if d == 0 { r == 0 } else { math(r) == math(n / d) }`.

A block binds immutable names with `let` statements and has the value of its
final expression. A block in expression position must bind at least one name;
`if` branches, `math { .. }`, and helper bodies are blocks that may also be a
bare expression. A `let` binds one identifier, optionally annotated as `bool`,
`()`, or a fixed-width integer type. The lowering rejects `let mut`, patterns,
`_`, `let ... else`, and a binding that the rest of its block never uses,
which Lean would warn about. It also rejects a binding that shadows a
parameter, the `ensures` binder, an enclosing binding, or a helper, and one
named like an intrinsic or a name the generated Lean uses (the names reserved
for helper parameters, plus `q`, `out`, and the `spec*` functions). As with an
`if`, no binary operator may follow a block directly.

A binding has the type of its value: `let s = math(a) + math(b);` is a
mathematical integer, and `let x = a;` keeps `a`'s machine type. An untyped
integer needs an annotation, as in `let k: u64 = 4;`, except inside `math`,
where `let k = 4;` is mathematical. An annotation gives the binding that
machine type even inside `math`, so its initializer is then a machine-typed
expression. In `max_steps`, an integer binding is a `Nat` step count; a signed
annotation is rejected, and an unsigned one must match a machine-typed value.
A binding lowers to `(let «x» : T := e; body)`, where `T` is `Prop`, `Int`,
`Nat`, or `Trusted.MirSemantics.Val`. A `bool` binding is decidable in the
condition of an `if` that chooses a value exactly when its initializer is.

Divisor guards pass through bindings. A name bound to a nonzero constant, or
to a value already known to be nonzero, guards a divisor in the rest of its
block, and a name bound to `0` counts as zero in a guard such as `d != z`. A
`bool` binding guards what its initializer guards, so
`let ok = d != 0; ok ==> math(n / d) == ..` passes. A guard that names a
block's own binding, such as `{ let e = d; e != 0 }`, does not leave the
block.

A `match` examines a `bool` or integer scrutinee and takes the first arm whose
pattern matches. A pattern is `_`, a name, `true` or `false`, an integer
literal (optionally negative or suffixed), or an integer constant such as
`u8::MAX`, and literals may be joined with `|`. A name binds the scrutinee and
follows the `let` rules. Guards, ranges, and tuple, struct, enum, slice,
`ref`, and `mut` patterns are rejected. A `match` must be exhaustive: a `bool`
match covers `true` and `false`, and an integer match ends with a `_` or name
arm. An arm whose patterns earlier arms already cover is rejected, as is an
empty `match`. As with an `if`, the scrutinee ends at the first `{`, the arms
must have one type, and no binary operator may follow a `match` directly. As
in Rust, an arm body in braces ends at its `}` and needs no comma after it;
other arm bodies, including `if` and `match` expressions, need one.

An integer pattern must be in range for the scrutinee's machine type, and a
suffixed pattern must have that type and be in range for its suffix. A
`math` scrutinee has no machine type, so its suffixed patterns need only be in
range. In `max_steps`, patterns are non-negative and unsigned, and a scrutinee
has the machine type it has in a `max_steps` `if` condition: `match n` on a
`u32` parameter rejects `3u8` and `4294967296`, while a sum, product, or
`let` binding of step counts has no machine type.

The lowering binds the scrutinee once, as `«match»` (a Rust keyword, so no
specification name can capture it), and treats the arms as nested `if`s over
`«match» = v`: arms between `bool`s join as implications, and arms that choose
a value use Lean's `if`, which needs a decidable scrutinee when it is a
`bool`. Each arm may divide by what its pattern and the earlier arms prove
nonzero, so `match d { 0 => r == 0, _ => math(r) == math(n / d) }` passes, as
does a name arm after a `0` arm.

An integer constant lowers to its value on the profile v1 target, where
`usize` and `isize` are 64 bits wide: `usize::MAX` lowers to
`(18446744073709551615 : Int)`. As in Rust, `T::MIN` and `T::MAX` have type
`T` and `T::BITS` has type `u32`, so arithmetic on them needs `math` like any
other machine integer, as in `math(a) + math(b) <= math(usize::MAX)`. A
nonzero constant guards a divisor as a nonzero literal does. No other path is
accepted: not other constants, not methods such as `usize::max_value()`, and
not longer paths such as `core::usize::MAX`.

The following parse but are rejected by the profile v1 lowering:
`old`, `cases`, `modifies`, `ensures_err`, `ensures_unwind`, `after_expiry`,
`decreases`, `witness`, `must_reject`, references, slices, and generics.

## Diagnostics

Errors are rendered `rustc`-style with exact spans: byte offsets index the
UTF-8 source and columns count Unicode scalar values.

| Code | Rejects |
| :--- | :--- |
| `E_ANNEAL_AMBIGUOUS_SPEC_ARITH` | `+ - * / %` or unary `-` on a machine integer outside `math`, a shift by an amount that is not a constant, or `clamp` with bounds that are not constants |
| `E_ANNEAL_UNGUARDED_SPEC_DIV` | `/` or `%` whose divisor may be zero |
| `E_ANNEAL_EAGER_CLAUSE_JOIN` | `&` or `\|` between `bool`s |
| `E_ANNEAL_AMBIGUOUS_NEGATION` | `!a == b` and `!a != b` |
| `E_ANNEAL_CHAINED_COMPARISON` | `a < b < c` |
| `E_ANNEAL_IMPURE_SPEC_EXPR` | assignments, blocks that bind no name, loops, `let mut`, `let` patterns and `let ... else`, `unsafe` helpers |
| `E_ANNEAL_UNUSED_LET` | a `let` binding that the rest of its block never uses, or a pattern binding that its arm never uses |
| `E_ANNEAL_NON_EXHAUSTIVE_MATCH` | an empty `match`, a `bool` `match` without both `true` and `false`, or an integer `match` without a final `_` or name arm |
| `E_ANNEAL_UNREACHABLE_MATCH_ARM` | a `match` pattern or arm that earlier patterns already cover |
| `E_ANNEAL_UNDECIDABLE_SPEC_IF` | an `if` choosing an integer or `()`, or a `bool` cast with `as`, whose condition or operand calls a `bool` helper, names a `bool` helper parameter, or compares `()` values |
| `E_ANNEAL_OLD_IN_PRECONDITION` / `E_ANNEAL_UNSUPPORTED_OLD` | `old(...)` |
| `E_ANNEAL_SAFETY_REQUIRES_ON_SAFE_FN` | `safety_requires` on a safe function |
| `E_ANNEAL_SPEC_UNKNOWN_IDENT` / `E_ANNEAL_SPEC_UNKNOWN_FN` | unbound names (with a did-you-mean hint) |
| `E_ANNEAL_SPEC_TYPE_MISMATCH` / `E_ANNEAL_SPEC_LITERAL_RANGE` / `E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED` | ill-typed expressions |
| `E_ANNEAL_SPEC_SHADOWING` | an `ensures` binder that shadows a parameter, and a `let` or pattern binding that shadows a parameter, the `ensures` binder, an enclosing binding, or a helper |
| `E_ANNEAL_PURE_RECURSION` | recursive helpers |
| `E_ANNEAL_UNSUPPORTED_CLAUSE` / `E_ANNEAL_UNKNOWN_CLAUSE` / `E_ANNEAL_UNKNOWN_ATTRIBUTE` | clauses outside profile v1 |
| `E_ANNEAL_UNSUPPORTED_TYPE` / `E_ANNEAL_SPEC_UNSUPPORTED_EXPR` | types, expressions, and `match` patterns outside profile v1 |
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
name it references is qualified from `Int`, `Nat`, `True`, `False`, `Trusted`,
`Min`, `Max`, or its own namespace (`Spec.pure_h` or `Specs.S.C.pure_h`,
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
