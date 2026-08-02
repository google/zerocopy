# Focused unsafe-Rust source audit

## Claim, snapshot, and verdicts

This review covers the supplied `Cargo.toml`, `src/lib.rs`, both published
policy documents, and `TCB.md`, source-only, as inspected on 2026-08-01. The
crate is `focused-predicate-target` 0.1.0, edition 2021, with no dependencies,
build script, generator, or generated artifact. Nothing was built, expanded,
run, or tested.

- **PROVED — source soundness:** every well-typed safe call to the selected
  `value_or_zero` implementation is free of Rust undefined behavior over the
  conservative audit domain `A` below, relative to accepted
  `BUILD-MAP-POLICY` and the exact-version Rust axioms cited below.
- **PROVED — documented behavior:** on that same domain, normal return is the
  contained byte for `Some(n)` and zero for `None`.
- **PROVED, TCB-qualified — effective rejection:** every considered
  `turbo`/`wasm32` compilation is rejected, relative specifically to
  `BUILD-MAP-POLICY` and the cited `cfg`/`compile_error!` contracts.
- **UNPROVED — identity of the project's exact support promise:** Scarlet and
  Indigo are current, incomparable commitments, and no merge or precedence
  rule is authorized. `A` is an audit domain, not a resolution of that
  governance question.

There is no `UNSOUND` or `CONTRACT-BROKEN` finding.

## Exact policy and full-case domains

Let

```text
V = {1.84.0, 1.85.0, 1.86.0}
T = {X, A, W}
X = x86_64-unknown-linux-gnu
A = aarch64-unknown-linux-gnu
W = wasm32-unknown-unknown
B = {false, true}
P = the set of all Cargo profiles
O = {None} union {Some(n) | n is any u8, 0 <= n <= 255}
```

A full case is `c=(v,t,f,h,p,d,i)`, where `f` is `turbo`, `h` is
`hardened`, `p` is profile, `d` is `debug_assertions`, and `i` is input. Define

```text
Base(c) := v in V and t in T and f,h,d in B and p in P and i in O.
```

The exact Scarlet configuration predicate is

```text
S0(v,t,f,h) :=
  !f
  or (f and t = X and (!h or v >= 1.85.0))
  or (f and t = A and h).
```

Its induced full-case domain is
`DS(c) := Base(c) and S0(v,t,f,h)`.

The exact Indigo configuration predicate is

```text
I0(v,t,f,h) :=
  !f
  or (f and t = X and (h or v >= 1.86.0))
  or (f and t = A and !h and v >= 1.85.0).
```

Its induced full-case domain is
`DI(c) := Base(c) and I0(v,t,f,h)`.

They are unequal and neither contains the other. The full case
`(1.84.0,X,true,false,dev,true,None)` is in `DS` because Scarlet's
`X and !h` clause holds, but not `DI` because both `h` and
`v >= 1.86.0` are false. Conversely,
`(1.86.0,A,true,false,dev,true,None)` is in `DI` because Indigo's
`A and !h and v >= 1.85.0` clause holds, but not `DS` because Scarlet's
`A` clause requires `h`.

Select the conservative full-case audit domain

```text
Required(c) := A(c) := DS(c) or DI(c).
```

The two required containments are immediate but separate: if `DS(c)`, then
the left disjunct establishes `A(c)`; if `DI(c)`, the right disjunct establishes
`A(c)`. Thus `DS subseteq A` and `DI subseteq A`. This exact union is chosen
only to audit every case promised by either document; it is not asserted to be
the project's support promise.

## Policy exclusion and effective rejection

For any `Base(c)` with `f=true` and `t=W`, neither policy holds: every `f=true`
disjunct in both `S0` and `I0` requires `t=X` or `t=A`. Hence no such case is in
`DS`, `DI`, or `Required`, for every `v,h,p,d,i`.

Source rejection is independently stronger within `Base`. Accepted
`BUILD-MAP-POLICY` maps `f=true` to `cfg(feature="turbo")` and `t=W` to
`target_arch="wasm32"` for each exact release and every profile. The enclosing
`cfg(all(...))` therefore includes `compile_error!` for every such case,
independently of `h,d,i`. For each exact release, the Reference says: “The
`cfg` attribute conditionally includes the thing it is attached to based on a
configuration predicate.” ([1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute)).
The corresponding macro pages say: “Causes compilation to fail with the given
error message when encountered.” ([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
[1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
[1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)). Thus no
library artifact containing a callable function is produced for these cases.

## Surface and obligation inventory

The complete crate-defined callable surface is one safe public free function,
`value_or_zero(Option<u8>) -> u8`, with mutually exclusive non-`turbo` and
`turbo` definitions. There are no public fields, constructors, user-defined
types or traits, callbacks, FFI items, reexports, hidden items, or exported
macros. `compile_error!` is the rejection site. The sole unsafe operation is
`Some(value).unwrap_unchecked()` in the `turbo` definition. There is no
persistent invariant-bearing state.

For each `r` in `V`, the exact `Option` pages provide the same three premises:
“Returns the contained `Some` value or a provided default” for `unwrap_or`,
“Returns the contained `Some` value” for `unwrap_unchecked`, and “Calling this
method on `None` is undefined behavior.” See
[1.84 `unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or) /
[`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.85 `unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or) /
[`unwrap_unchecked`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), and
[1.86 `unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or) /
[`unwrap_unchecked`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked).
Using each release's own pages is an exhaustive three-member partition; no
cross-version compatibility premise is used.

Let `Q(i,r)` mean `(i=None and r=0) or (there exists n: i=Some(n) and r=n)`.

1. **Non-`turbo` branch.** For every full case with `f=false`, the build-map
   premise and complementary `cfg` select this definition. If `i=None`,
   `i.unwrap_or(0)` returns the provided zero; if `i=Some(n)`, it returns `n`.
   The call is safe and establishes `Q` for every `i in O`; there is no unsafe
   operation.
2. **`turbo` executable branch.** For every full case with `f=true` and
   `t in {X,A}`, the `turbo` definition is selected and the rejection predicate
   is false. The first `unwrap_or(0)` produces `x=0` from `None` and `x=n` from
   `Some(n)`. The unsafe receiver is then syntactically constructed as
   `Some(x)`, not `None`; therefore the exact `unwrap_unchecked` safety
   obligation holds. It returns `x`, establishing `Q` in both input cases.

These derivations are parametric in `t,h,p,d,i` where stated. `h`, profile, and
debug assertions do not occur in either function body; target affects only the
proved `W` rejection. Version is discharged by the exhaustive exact-document
partition above.

## Covered predicates and closure certificates

Without dropping any full-case dimension, define

```text
Executable(c) := Base(c) and (!f or (f and t in {X,A})).
Covered_sound(c) := Executable(c).
Covered_post(c)  := Executable(c).
Required_sound(c) := Required(c).
Required_post(c)  := Required(c).
```

The branch lemmas prove soundness and `Q`, respectively, for every case in the
two `Executable` disjuncts, so these are the applicable aggregate coverage
predicates. If `Required(c)`, then `DS(c)` or `DI(c)`. Both imply `Base(c)`; if
`!f`, the first `Executable` disjunct holds, while if `f`, inspection of every
`f`-disjunct in both exact policy predicates gives `t in {X,A}`. Consequently
`Required_sound subseteq Covered_sound` and
`Required_post subseteq Covered_post`. These two pointwise containments certify
the whole-domain soundness and behavioral verdicts; coverage is not a union of
different obligations proved on different regions.

## TCB, findings, and residual scope

`BUILD-MAP-POLICY` is the only admitted non-Rust premise. Its human disposition
is accepted; its identity is the toolchain-bundled Cargo for exactly Rust
1.84.0, 1.85.0, and 1.86.0 acting on the supplied manifest/source. This report
uses it only for feature/target `cfg` reachability, branch selection, and
effective rejection, exactly its listed consumers. It is not used for Rust
semantics, branch correctness, compatibility, or binary/backend correctness.
The versioned Reference/std propositions above are authoritative Rust axioms,
not compatibility assumptions. There is no dependency, tool-result, external,
deployment, or probabilistic TCB entry.

**POLICY-1 (UNPROVED governance claim).** The smallest missing premise is an
authorized rule selecting or combining Scarlet and Indigo. Resolution requires
a published precedence/supersession/merge decision; it would change domain
identity, not the proofs over `A` unless it adds cases outside `A`.

**DOC-1 (proof-artifact deficiency; implementation proved).** The existing
SAFETY comment records the decisive local fact—construction as `Some`—but does
not state the consumed callee precondition. A proof-grade replacement is:

```rust
// SAFETY: `unwrap_unchecked` requires the receiver not to be `None`.
// It is constructed immediately here as `Some(value)`, so that holds.
```

No implementation change is required for this finding.

Excluded from the claims are configurations outside `Required`, emitted binary
correctness, compiler/backend/linker behavior, performance, and undocumented
robustness. Re-audit is required for any source, manifest, policy-resolution,
feature/target/profile support, TCB disposition or mapping, Rust-version scope,
or materially consumed authoritative-documentation change.
