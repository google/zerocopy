# Focused unsafe-code audit

## Claim, snapshot, and verdicts

This source-only review covers the supplied `Cargo.toml`, `POLICY-SCARLET.md`,
`POLICY-INDIGO.md`, `TCB.md`, and `src/lib.rs` snapshot, with audit cutoff
2026-08-01. There are no dependencies, generators, expansions, or prior results
in the supplied evidence. No build, execution, test, or backend claim is made.

For a full case

`c = (v,t,f,h,p,d,i) = (version,target,turbo,hardened,profile,debug_assertions,input)`,

the soundness theorem is: every well-typed safe call to the selected
`value_or_zero` in every required case is free of Rust undefined behavior. The
behavioral theorem is: if the call returns `r`, then

`Q(i,r) := (i = None => r = 0) and (for every n, i = Some(n) => r = n)`.

Results over the conservative domain `R` defined below:

* **Soundness: PROVED relative to `BUILD-MAP-POLICY`.**
* **Documented postcondition `Q`: PROVED relative to `BUILD-MAP-POLICY`.**
* **Combined mandatory result: PROVED relative to `BUILD-MAP-POLICY`.**
* **Identity of the crate's exact support promise: UNPROVED.** Scarlet and
  Indigo are both current, conflict, and have no authorized resolution. `R` is
  an audit domain, not a resolution or newly inferred project promise.

## Exact policy predicates and relationship

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}`, with `X`, `A`, and `W` denoting
the three exact triples in the policies. Let `B={false,true}`, `P` be all Cargo
profiles, and `O` be every valid `Option<u8>`.

The exact Scarlet configuration predicate is

`S(v,t,f,h) := v in V and t in T and [!f or (f and t=X and (!h or v>=1.85.0)) or (f and t=A and h)]`.

The exact Indigo configuration predicate is

`I(v,t,f,h) := v in V and t in T and [!f or (f and t=X and (h or v>=1.86.0)) or (f and t=A and !h and v>=1.85.0)]`.

They are **incomparable**, hence unequal:

* `(1.84.0,X,true,false)` is in Scarlet: its `X` clause has `!h`; it is not in
  Indigo because both `h` and `v>=1.86.0` are false. Thus `S` is not contained
  in `I`.
* `(1.84.0,X,true,true)` is in Indigo: its `X` clause has `h`; it is not in
  Scarlet because both `!h` and `v>=1.85.0` are false. Thus `I` is not
  contained in `S`.

The induced full-case domains, retaining every requested dimension, are

`D_S(c) := S(v,t,f,h) and p in P and d in B and i in O`, and

`D_I(c) := I(v,t,f,h) and p in P and d in B and i in O`.

Select the conservative audit domain

`R(c) = Required(c) := D_S(c) or D_I(c)`.

For every full case, `D_S(c) => D_S(c) or D_I(c)` and independently
`D_I(c) => D_S(c) or D_I(c)`. Therefore `D_S` is contained in `R` and `D_I`
is contained in `R`; these are full-case, not configuration-projection,
containments. Conversely, `R = D_S union D_I` by definition, but that equality
does not resolve which current policy controls the project's promise.

## Authorities and TCB

For each exact release, its `Option` page states that `unwrap_or` “Returns the
contained `Some` value or a provided default”; `unwrap_unchecked` “Returns the
contained `Some` value”; and “Calling this method on `None` is undefined
behavior”: [1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or),
[1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or),
[1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).
The corresponding unsafe-method anchors are
[1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), and
[1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked).
These separate exact-version axioms avoid any cross-release compatibility
assumption.

For each release, the Reference says an option predicate is “true if the
configuration option is set”; `all` requires “all of the given predicates” to
be true, `not` is true when “its predicate is false,” and `cfg` “conditionally
includes” its attached item: [1.84.0 predicates](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
[1.84.0 attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.85.0 predicates](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation),
[1.85.0 attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.86.0 predicates](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation), and
[1.86.0 attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute).
Each exact-version macro page says `compile_error!` “causes compilation to fail
with the given error message when encountered”: [1.84.0](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
[1.85.0](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
[1.86.0](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).

`BUILD-MAP-POLICY` is the sole additional TCB entry. It is accepted by the
authorized human and admits, only for the toolchain-bundled Cargo at the three
releases and supplied manifest/source, that feature enablement maps exactly to
the two feature cfgs and the three triples map respectively to `x86_64`,
`aarch64`, and `wasm32`. This audit consumes it only in source selection and
effective rejection below; it supplies no Option semantics or branch
correctness. Its limitations and re-audit triggers are exactly those in
`TCB.md`. No implementation, backend, dependency, tool-result, or environmental
premise is admitted.

## Selection, exclusion, and effective rejection

By the build mapping and cited cfg semantics, `!f` selects exactly the
`#[cfg(not(feature="turbo"))]` definition, while `f` selects exactly the
`#[cfg(feature="turbo")]` definition. Neither profile, `d`, `h`, nor `i`
occurs in these selectors, so this argument is parametric over their complete
fibers and is repeated under each release's exact Reference text.

At policy level, if `f` and `t=W`, every disjunct in both `S` and `I` is false:
`!f` is false and each remaining disjunct requires `t=X` or `t=A`. Thus neither
policy induces such a full case and `R` excludes all of them.

Independently, for every `v in V`, `h,d in B`, `p in P`, and `i in O`, the TCB
maps `f=true,t=W` to both `feature="turbo"` and `target_arch="wasm32"` being
set. `all(...)` is therefore true, its cfg includes `compile_error!`, and the
cited macro contract makes compilation fail. No library artifact or runtime
input is reached. This proves source-level effective rejection across the
entire stated `turbo`/`wasm32` case fiber, relative to the TCB; it is not used
to pretend those policy-excluded cases are members of `R`.

For every `R(c)` with `f=true`, either policy's only possible true turbo
disjunct requires `t=X` or `t=A`. Hence the rejection condition is false and
the turbo source branch is the relevant branch.

## Branch-local proofs and obligation ledger

The sole public safe surface is `value_or_zero(Option<u8>) -> u8`, with one of
two configuration-specific definitions. There are no fields, constructors,
traits, impls, exported macros, hidden items, callbacks, FFI surfaces, or
stateful invariants.

**OBL-NONTURBO (`R(c) and !f`).** The selected body is
`i.unwrap_or(0)`. For each `v` the exact-version safe-method contract yields
`0` when `i=None` and the contained `n` when `i=Some(n)`. Thus `Q` holds. The
body contains no unsafe operation, and the safe standard-library call is made
with its typed receiver and argument; soundness is proved for every `t,h,p,d,i`
in this fiber.

**OBL-TURBO (`R(c) and f`).** First, the same release-specific `unwrap_or`
contract establishes a local byte `x=0` for `None`, or `x=n` for `Some(n)`.
Next the receiver at the unsafe site is syntactically and immediately
constructed as `Some(x)`. Therefore it is not `None`, discharging the exact
`unwrap_unchecked` safety obligation. Its documented result is the contained
value `x`; substitution of the first step proves `Q`. This proves both UB
freedom and behavior for every `t in {X,A}`, `h,p,d,i` admitted by `R` and for
each separately cited release.

**DOC-1 (proof artifact deficient; implementation proved).** The existing
`SAFETY` comment records the decisive local fact but omits the callee's exact
`None`-UB obligation and the result used for `Q`. Suggested replacement:

> SAFETY: `unwrap_unchecked` is UB on `None`. The receiver is exactly
> `Some(value)`, hence not `None`; the call returns its contained `value`.

This is documentation debt, not a hidden caller obligation or implementation
defect.

## Full-case Covered predicates and closure

The two branch lemmas are universal over every omitted-dimension fiber, so no
dimension is projected away. State the proved predicates extensionally as

`Covered_sound(c) := R(c)`, and `Covered_post(c) := R(c)`.

Their derivation is the exhaustive partition `R(c) and !f` versus `R(c) and f`.
Boolean totality covers every `f`; the first is OBL-NONTURBO, and in the second
`R=>t in {X,A}` followed by OBL-TURBO applies. Each lemma retains `v,t,f,h,p,d,i`;
`p,d,h` are irrelevant because they neither select nor alter the body, while
`i` is handled parametrically as `None` or `Some(n)`. The release dimension is
exhausted by three release-specific authority/derivation instances.

For soundness, `Required(c)=R(c)=Covered_sound(c)`, hence
`Required` is contained in `Covered_sound`. Independently,
`Required(c)=R(c)=Covered_post(c)`, hence `Required` is contained in
`Covered_post`. Claim-level coverage is their pointwise conjunction, not a
union: `Covered_sound(c) and Covered_post(c) = R(c)`. Therefore
`Required` is contained in aggregate `Covered`, certifying both PROVED verdicts
relative to `BUILD-MAP-POLICY`.

## Residual scope and review triggers

The unresolved item is solely which conflicting policy defines the exact
project promise; an authorized precedence/merge decision is required. Cases
outside `R`, including all turbo/wasm32 cases, versions outside `V`, targets
outside `T`, non-Cargo/custom build mappings, compiler/backend correctness, and
binary behavior are not affirmative audit claims. Re-audit on any source,
manifest, policy/resolution, supported-axis, feature/target mapping, TCB
disposition, or consumed exact-version Rust documentation change.
