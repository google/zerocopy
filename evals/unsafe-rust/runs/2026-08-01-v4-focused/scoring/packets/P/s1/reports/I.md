# Focused unsafe-code audit

## Claim, snapshot, and verdicts

This is a source-level audit of the supplied `Cargo.toml` and `src/lib.rs` under
the two supplied policies, for Rust/standard-library releases 1.84.0, 1.85.0,
and 1.86.0. Scope comprises the public safe function `value_or_zero`, its two
conditionally selected definitions, the one `unwrap_unchecked` operation, its
documented return-value postcondition, and the `turbo`/`wasm32` rejection. There
are no dependencies, generated sources, build scripts, public fields, traits,
impls, exported macros, FFI surfaces, or representation invariants.

| Claim | Verdict | Qualification |
|---|---|---|
| Freedom from Rust undefined behavior for every case in the conservative audit domain `Required` below | **PROVED** | Source semantics; relative to accepted `BUILD-MAP-POLICY` solely for mapping policy configurations to Rust `cfg`s/source selection |
| “Returns the contained byte, or zero when `value` is `None`” over that same domain | **PROVED** | Same qualification |
| Identity of the crate's exact support promise | **UNPROVED** | Scarlet and Indigo are incomparable current commitments and no resolution rule is authorized |

Thus the mandatory soundness and behavioral claims are also **PROVED**
separately over each policy-induced domain, by their proved containment in
`Required`. This does not resolve which policy, union, intersection, or other
set is the actual project promise. No backend, binary, future-release, or
unsupported-configuration correctness is claimed. Audit cutoff: 2026-08-02;
the supplied policies contain no moving component.

## Exact policy and full-case domains

Let

- `V = {1.84.0, 1.85.0, 1.86.0}`;
- `T = {X, A, W}`, with the triples defined exactly as in the policies;
- `B = {false, true}`;
- `P` be all Cargo profiles (as quantified by both policies); and
- `O = Valid(Option<u8>)`, including `None` and every `Some(x)` with valid
  `x: u8`.

For configuration `q=(v,t,f,h)`, the policies' exact predicates are

```text
Scarlet(q) := v in V and t in T and
  (!f
   or (f and t = X and (!h or v >= 1.85.0))
   or (f and t = A and h))

Indigo(q) := v in V and t in T and
  (!f
   or (f and t = X and (h or v >= 1.86.0))
   or (f and t = A and !h and v >= 1.85.0))
```

They are unequal and incomparable. `(1.84.0,X,true,false)` is Scarlet: its
Scarlet `X` arm holds through `!h`; it is not Indigo because both `h` and
`v>=1.86.0` are false. Conversely `(1.84.0,X,true,true)` is Indigo through its
`h` term, but not Scarlet because both `!h` and `v>=1.85.0` are false. These
are explicit witnesses to `Scarlet ⊈ Indigo` and `Indigo ⊈ Scarlet`.

A full case is exactly
`c=(v,t,f,h,p,d,i)`, for `p in P`, `d in B` (the `debug_assertions` state),
and `i in O`. Define

```text
D_S(c) := Scarlet(v,t,f,h) and p in P and d in B and i in O
D_I(c) := Indigo(v,t,f,h) and p in P and d in B and i in O
Required(c) := D_S(c) or D_I(c)
```

`Required` is the selected conservative audit domain, not an asserted project
promise. For arbitrary full `c`, `D_S(c) => Required(c)` by left disjunction
introduction, and `D_I(c) => Required(c)` by right disjunction introduction;
these separately prove `D_S ⊆ Required` and `D_I ⊆ Required`. The same
two witnesses, extended with any `p,d,i`, show the full-case domains remain
incomparable.

## Configuration selection and rejection

For each exact release, the Reference says `all()` is “true if all … predicates
are true”, `not()` is “true if its predicate is false”, and a `cfg` attribute
“conditionally includes the thing … based on a configuration predicate”:
[1.84 predicates](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
[1.84 attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.85 predicates](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation),
[1.85 attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.86 predicates](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation),
[1.86 attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute).
The exact-version `compile_error!` pages identically state: “Causes compilation
to fail with the given error message when encountered.”
([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
[1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
[1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)).

Applying only the accepted `BUILD-MAP-POLICY`, `f` supplies
`cfg(feature="turbo")`, `h` supplies the analogous `hardened` option, and
`X/A/W` supply `target_arch="x86_64"/"aarch64"/"wasm32"`, for each listed
release and profile. Combining that admitted leaf mapping with the cited Rust
semantics proves:

- if `!f`, exactly the `cfg(not(feature="turbo"))` function is included;
- if `f` and `t` is `X` or `A`, exactly the turbo function is included and the
  `compile_error!` predicate is false; and
- if `f` and `t=W`, both operands of `all(...)` are true, so the error macro is
  included and compilation fails. This rejection is independent of `h,p,d,i`.

Policy-level exclusion is independent: substituting `f=true,t=W` makes `!f`
false and every `t=X`/`t=A` arm false in both predicates. Hence no such case is
in `D_S`, `D_I`, or `Required`. The source additionally rejects every such
build effectively, relative to `BUILD-MAP-POLICY`; it supplies no callable
library execution to which the runtime postcondition could apply.

## Branch proofs and obligation ledger

The exact 1.84/1.85/1.86 `Option` pages use identical controlling prose:
`unwrap_or` “Returns the contained `Some` value or a provided default”;
`unwrap_unchecked` “Returns the contained `Some` value”; and “Calling this
method on `None` is undefined behavior.”
([1.84 `unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or),
[1.84 `unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.85 `unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or),
[1.85 `unwrap_unchecked`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.86 `unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or),
[1.86 `unwrap_unchecked`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked)).

Let `Q(i,r)` mean `r=x` when `i=Some(x)`, and `r=0` when `i=None`.

| Obligation | Full applicability | Derivation | Status |
|---|---|---|---|
| Non-turbo soundness and `Q` (`lib.rs:7-9`) | `v in V,!f,t in T,h,d in B,p in P,i in O` | Safe `unwrap_or(0)` returns the contained value or `0`; no unsafe operation occurs | **PROVED** |
| Turbo unsafe precondition (`lib.rs:16`) | `v in V,f,t in {X,A},h,d in B,p in P,i in O` | First `unwrap_or(0)` produces some byte `y`; the receiver is then constructed immediately as `Some(y)`, therefore it is not `None` | **PROVED** |
| Turbo `Q` (`lib.rs:13-16`) | same | `unwrap_unchecked` returns the contained `y`; the preceding `unwrap_or(0)` establishes `y=x` for `Some(x)` and `y=0` for `None` | **PROVED** |
| `turbo`/`W` effective rejection (`lib.rs:3-4`) | `v in V,f,t=W,h,d in B,p in P,i in O` | cfg derivation above; failure precedes any runtime input | **PROVED relative to BUILD-MAP-POLICY** |

The branch proofs are parametric in target within their stated branch,
`h`, profile, debug assertions, and every valid input; none of those omitted
dimensions changes the source operations or the cited contracts.

## Exact coverage and closure

Define, without projecting any dimension,

```text
Base(c) := v in V and t in T and f in B and h in B
           and p in P and d in B and i in O
Compiles(c) := !f or (f and t in {X,A})
Covered_sound(c) := Base(c) and Compiles(c)
Covered_post(c)  := Base(c) and Compiles(c)
```

Here `Covered_sound` denotes exactly the full cases covered by the two
source-level absence-of-UB lemmas above, and `Covered_post` those covered by
their `Q` lemmas, within the audited versions/targets. For arbitrary `c` with
`Required(c)`, either policy predicate holds. If `!f`, `Compiles(c)` holds. If
`f`, every surviving arm in either exact predicate explicitly requires
`t=X` or `t=A`; hence `Compiles(c)` again holds. All other `Base` conjuncts are
retained verbatim by `D_S` and `D_I`. Therefore

```text
Required ⊆ Covered_sound
Required ⊆ Covered_post.
```

These containments, the exhaustive `f` branch split, and the per-branch proofs
are the certificates for both whole-domain **PROVED** verdicts.

## TCB disposition, finding, and residual scope

TCB identity is the supplied `TCB.md`, entry `BUILD-MAP-POLICY`; disposition:
accepted. It is consumed only in source-selection and effective-rejection
lemmas. It supplies no Option semantics, branch correctness, version
compatibility, or backend correctness. The version-matched Reference/std
quotations above are authoritative `AXIOM` entries, each restricted to its
named release. No compatibility interpolation is used and no other assumption
or tool-derived evidence is consumed.

**Documentation finding (implementation still PROVED).** The existing safety
comment records the decisive local fact—construction as `Some`—but omits the
callee's exact precondition and the result used for `Q`; the audit had to
reconstruct those material links. A proof-grade replacement is:

```rust
// SAFETY: `Option::unwrap_unchecked` requires this receiver not to be `None`.
// It is constructed immediately as `Some(value)`, so that requirement holds;
// the call returns the contained `value`.
unsafe { Some(value).unwrap_unchecked() }
```

Re-audit on any source/manifest/policy/TCB change; a change to the three Rust
versions or cited contracts; or a change to feature names, targets, supported
profiles, or debug-assertion policy. Residual scope comprises invalid
`Option<u8>` values, versions/targets outside the stated sets, rejected builds,
compiler/backend/binary behavior, and resolution of the conflicting support
commitments.
