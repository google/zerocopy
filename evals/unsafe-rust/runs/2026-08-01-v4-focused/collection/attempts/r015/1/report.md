# Focused unsafe-code audit

## Claim, scope, and verdicts

This audit covers the supplied `Cargo.toml`, `src/lib.rs`, two policy files, and
`TCB.md`, at the 2026-08-01 cutoff. It covers the public safe function
`value_or_zero`, its two configuration-selected implementations, the one
`unsafe` call, and the compile-time rejection item. There are no dependencies,
generated artifacts, unsafe public APIs, fields, traits, impls, callbacks, FFI,
assembly, or representation invariants in the supplied source.

For the conservative audit domain `Required` defined below:

| Claim | Verdict | Qualification |
|---|---|---|
| Every well-typed call with any valid `Option<u8>` is free of Rust UB | **PROVED** | Source-level Rust semantics; relative to accepted `BUILD-MAP-POLICY` for policy-to-`cfg` reachability |
| The call returns its contained byte, or zero for `None` | **PROVED** | Same domain and qualification |
| Combined mandatory claim | **PROVED** | `Required ⊆ Covered_sound ∩ Covered_post` is proved below |
| A single exact project support predicate can be selected from Scarlet and Indigo | **UNPROVED** | No precedence or conflict-resolution rule is authorized; the audit union is not such a resolution |

These are source-level conclusions, not compiler-backend, binary, or platform
correctness claims.

## Exact policy predicates and relationship

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}`, where `X`, `A`, and `W` have the
triples defined in the policies, and let `f` and `h` be Boolean `turbo` and
`hardened` states. Scarlet supports exactly `v∈V ∧ t∈T` and:

```text
!f
or (f and t = X and (!h or v >= 1.85.0))
or (f and t = A and h)
```

Indigo supports exactly `v∈V ∧ t∈T` and:

```text
!f
or (f and t = X and (h or v >= 1.86.0))
or (f and t = A and !h and v >= 1.85.0)
```

They are unequal and incomparable. The configuration
`(1.84.0,X,true,false)` is Scarlet-only: Scarlet's `X ∧ !h` disjunct holds,
whereas every Indigo disjunct is false. Conversely,
`(1.84.0,X,true,true)` is Indigo-only: Indigo's `X ∧ h` disjunct holds,
whereas Scarlet requires `!h` or `v>=1.85.0`. Thus neither predicate contains
the other. Each separator extends to every policy-supported profile,
debug-assertion state, and valid input.

## Full-case domains

Let:

```text
B = {false,true}
P = the symbolic set of all Cargo profiles
O = {None} ∪ {Some(n) | n∈{0,…,255}}
c = (v,t,f,h,p,d,i)
Base(c) := v∈V ∧ t∈T ∧ f∈B ∧ h∈B ∧ p∈P ∧ d∈B ∧ i∈O
```

Writing the displayed policy bodies as `S(v,t,f,h)` and `I(v,t,f,h)`:

```text
D_S(c) := Base(c) ∧ S(v,t,f,h)
D_I(c) := Base(c) ∧ I(v,t,f,h)
Required(c) := D_S(c) ∨ D_I(c)
```

`D_S` and `D_I` are the exact Scarlet- and Indigo-induced full-case domains.
`Required` is the selected conservative audit domain. Separately,
`D_S⊆Required` and `D_I⊆Required` follow by disjunction introduction for
every complete tuple `c`; hence it contains both domains. No equality between
`Required` and an exact crate support promise is asserted: the latter remains
unresolved by the controlling documents.

## Authoritative semantic premises

The following wording was checked separately at every exact release, so no
cross-version compatibility assumption is used.

* On the exact Option pages for [1.84.0 `unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or), [1.85.0 `unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or), and [1.86.0 `unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or), the contract says: “Returns the contained `Some` value or a provided default.” The corresponding [1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), and [1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked) `unwrap_unchecked` pages say “Returns the contained `Some` value” and, under Safety, “Calling this method on `None` is undefined behavior.”
* Each exact conditional-compilation Reference—[1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), and [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation)—defines `all()` as “true if all of the given predicates are true” and `not()` as “true if its predicate is false.” Their `cfg`-attribute sections ([1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute)) say it “conditionally includes” its attached item and that when the “predicate is false, the thing is removed.”
* The exact [1.84.0](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85.0](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), and [1.86.0](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html) macro pages all state: “Causes compilation to fail with the given error message when encountered.”

## Exclusion and effective rejection

Define the full rejected region
`E(c):=Base(c) ∧ f ∧ t=W`. Both policies exclude every member: with
`f=true`, `!f` is false, and with `t=W`, every `t=X` or `t=A` turbo disjunct is
false. Therefore `E∩D_S=E∩D_I=∅`, independently of `h,p,d,i`.

Source-level rejection is a separate fact. Relative to the accepted
`BUILD-MAP-POLICY`, every `c∈E` sets both `feature="turbo"` and
`target_arch="wasm32"`. The `all(...)` predicate is therefore true, its `cfg`
item is included, and the encountered `compile_error!` makes compilation fail.
Thus no `E` case produces a callable library artifact. `h`, profile,
`debug_assertions`, and runtime input do not occur in this rejection condition.

## Branch and obligation proofs

Define `g(None)=0` and `g(Some(n))=n`.

**Non-turbo branch (`Base(c) ∧ !f`).** `BUILD-MAP-POLICY` plus the versioned
`cfg` rules selects the safe implementation. The exact-version `unwrap_or`
contract gives `value.unwrap_or(0)=g(i)` for both exhaustive input cases.
There is no unsafe operation on this branch, and it returns `g(i)`, proving
soundness and the documented postcondition. The argument is parametric in
`v,t,h,p,d` after applying the appropriate one of the three exact-version
premises.

**Turbo, non-W branch (`Base(c) ∧ f ∧ t≠W`).** The mapping and `cfg` rules
select the turbo implementation without encountering the rejection item.
First, safe `unwrap_or(0)` establishes the local `value=g(i)`. The receiver of
the unsafe call is then the expression `Some(value)`, hence is not `None`.
This discharges the complete documented safety obligation of
`unwrap_unchecked`; its return contract yields the contained `value=g(i)`.
The execution is UB-free and returns exactly the documented result for every
`i∈O`. Again `h,p,d` and the non-W target identity do not affect the dataflow,
and each `v` uses its own exact documentation.

The existing safety comment records the decisive checked fact, but omits the
callee's explicit not-`None` obligation. This is proof-documentation debt, not
an implementation defect. A complete adjacent replacement would be:

```rust
// SAFETY: `unwrap_unchecked` requires its receiver not be `None`.
// The receiver is constructed here as `Some(value)`, so it is not `None`.
```

## Covered predicates and closure certificates

Without projecting away any full-case dimension, let:

```text
Covered_sound(c) := Base(c) ∧ !(f ∧ t=W)
Covered_post(c)  := Base(c) ∧ !(f ∧ t=W)
Covered_reject(c):= Base(c) ∧ f ∧ t=W
```

For each of the first two obligations, `Covered` is the union of the exhaustive
`!f` proof case and the `f ∧ t≠W` proof case. For every `c∈Required`, the
full `Base(c)` conjunct holds. The policy-exclusion proof above also gives
`!(f ∧ t=W)`. Hence `Required⊆Covered_sound` and independently
`Required⊆Covered_post`; pointwise conjunction gives
`Required⊆Covered_sound∩Covered_post`. This is the certificate for both
whole-domain `PROVED` verdicts. `Covered_reject` records the disjoint,
effectively rejected source region; it is not treated as a callable-behavior
case.

## TCB, evidence, residual scope, and triggers

`BUILD-MAP-POLICY` is the sole additional accepted premise. Its identity is
the toolchain-bundled Cargo for exactly Rust 1.84.0, 1.85.0, and 1.86.0 on the
supplied manifest/source. Only its named feature-to-`cfg` and target-to-
`target_arch` mappings are consumed, solely for branch reachability and
effective rejection. No Rust semantics, backend behavior, or versions outside
`V` are inferred from it. The exact-version Rust pages above are authoritative
axioms, not a compatibility bridge. No test, execution, build, expansion, or
tool-derived result was used.

Residual scope comprises configurations outside `Base`, binary/backend
correctness, and the unresolved identity of the crate's single support promise.
Re-audit is required by any source, manifest, policy, TCB disposition/mapping,
feature or target set, supported Rust release, relevant Rust documentation, or
documented `value_or_zero` contract change.
