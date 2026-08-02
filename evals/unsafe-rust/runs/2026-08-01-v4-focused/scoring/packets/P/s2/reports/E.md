# Focused unsafe-code audit

## Claim, snapshot, and verdicts

This is a source-only review of the supplied `Cargo.toml`, `src/lib.rs`, two
published policies, and `TCB.md`, at the 2026-08-01 audit cutoff. No generated
artifact, dependency, build, execution, test, backend, or binary claim is in
scope.

| Claim | Verdict |
|---|---|
| Which policy is the crate's exact support promise | **UNPROVED**: Scarlet and Indigo are both current, are incomparable, and no resolution rule is authorized. |
| Freedom from Rust UB for every `value_or_zero` call in `Required` below | **PROVED relative to accepted `BUILD-MAP-POLICY`** and the exact-version Rust axioms below. |
| Documented result: contained byte, or zero for `None`, throughout `Required` | **PROVED relative to accepted `BUILD-MAP-POLICY`** and those axioms. |
| Source rejection of every named `turbo`/`wasm32` configuration | **PROVED relative to accepted `BUILD-MAP-POLICY`** and the cfg/`compile_error!` axioms. |

Thus the combined source theorem over the explicitly conservative audit domain
is **PROVED relative to `BUILD-MAP-POLICY`**. This does **not** resolve or rename
that domain as the crate's published support promise.

## Exact policies and full-case domains

Let `V = {1.84.0, 1.85.0, 1.86.0}`, `X =
x86_64-unknown-linux-gnu`, `A = aarch64-unknown-linux-gnu`, and `W =
wasm32-unknown-unknown`. Let Boolean `f` and `h` mean `turbo` and `hardened`.
The exact Scarlet configuration predicate is

```text
v in V and t in {X,A,W} and
(!f
 or (f and t = X and (!h or v >= 1.85.0))
 or (f and t = A and h))
```

The exact Indigo configuration predicate is

```text
v in V and t in {X,A,W} and
(!f
 or (f and t = X and (h or v >= 1.86.0))
 or (f and t = A and !h and v >= 1.85.0))
```

Write these predicates as `S(v,t,f,h)` and `I(v,t,f,h)`. They are neither
equal nor contained in one another:

* `(1.84.0,A,true,true)` satisfies Scarlet but not Indigo.
* `(1.84.0,X,true,true)` satisfies Indigo but not Scarlet.

Either witness becomes a separating full case, for example, by adding
`profile=dev`, `debug_assertions=false`, and `input=None`.

Let `P` be the symbolic set of every Cargo profile, `B={false,true}`, and
`O={None} union {Some(x) | x is any valid u8}`. For
`c=(v,t,f,h,p,d,i)`, the two policy-induced full domains are exactly

```text
D_S(c) := S(v,t,f,h) and p in P and d in B and i in O
D_I(c) := I(v,t,f,h) and p in P and d in B and i in O.
```

No input, profile, or debug-assertion dimension has been projected away.

## Conservative domain and exclusions

Define

```text
F(c) := v in V and t in {X,A,W} and f,h in B
        and p in P and d in B and i in O
Required(c) := F(c) and not(f and t = W).
```

This is the selected conservative audit domain. Separately for Scarlet: if
`D_S(c)` and `f` is false, `not(f and t=W)` follows immediately; if `f` is
true, Scarlet's only true turbo disjunct has `t=X` or `t=A`. Hence
`D_S subset Required`. The identical split for Indigo uses its turbo
disjuncts, also restricted to `X` or `A`, so `D_I subset Required`. The other
three full-case dimensions are universally identical in each policy and in
`Required`. This proves both containments without claiming policy equality.

At policy level, setting `f=true,t=W` falsifies every disjunct in both policies,
for every `v,h,p,d,i`. At source level, `BUILD-MAP-POLICY` maps exactly that
feature/target selection to both cfg atoms; `all(...)` is true, the cfg keeps
the `compile_error!`, and compilation fails. Thus every such full case is both
policy-excluded and effectively rejected before an executable library is
produced. This rejection statement, unlike the Boolean policy calculation,
depends on the accepted build-map premise.

## Applicable Rust axioms

The following quoted prose is identical on each linked exact release; no
cross-release compatibility inference is used.

* CFG-84/85/86: the Reference describes `cfg` as “conditionally includes”;
  `all` is “true if all of the given predicates are true”; `not` is “true if
  the given predicate is false”; a false cfg is “removed from the source.”
  Sources: [1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
  [1.84 cfg attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
  [1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation),
  [1.85 cfg attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
  [1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation),
  [1.86 cfg attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute).
* CE-84/85/86: `compile_error!` “Causes compilation to fail with the given error
  message when encountered.” Sources: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
  [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
  [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).
* OPTION-84/85/86: `unwrap_or` “Returns the contained `Some` value or a provided
  default.” `unwrap_unchecked` “Returns the contained `Some` value”; “Calling
  this method on `None` is undefined behavior.” Sources:
  [1.84 `unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or),
  [1.84 unchecked](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [1.85 `unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or),
  [1.85 unchecked](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [1.86 `unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or),
  [1.86 unchecked](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked).

## Branch proofs and obligation ledger

The only language-reachable crate API is the safe free function
`value_or_zero(Option<u8>) -> u8`, with exactly one cfg-selected definition.
There are no public fields, user constructors, methods, traits/impls, callbacks,
macros exported by this crate, hidden items, FFI, or invariant-bearing state.

**Non-turbo lemma (`F(c) and !f`).** CFG plus `BUILD-MAP-POLICY` selects the
first definition and removes the second. There is no unsafe operation.
OPTION-84/85/86 entails that `Some(x).unwrap_or(0)` returns `x` and
`None.unwrap_or(0)` returns `0`. This proves UB freedom and the documented
postcondition for every `v,t,h,p,d,i` in this lemma.

**Turbo lemma (`F(c) and f and t in {X,A}`).** The accepted mapping and CFG
select the second definition; the wasm compile error is absent. First,
`i.unwrap_or(0)` produces `y=x` for `i=Some(x)` and `y=0` for `i=None`.
The receiver of the sole unsafe operation is then syntactically and immediately
constructed as `Some(y)`. It is therefore not `None`, discharging the complete
documented safety precondition of `unwrap_unchecked`; OPTION-84/85/86 says it
returns the contained `y`. Thus the operation is free of its documented UB and
the function returns `x` for `Some(x)`, otherwise `0`, for every retained
version, target, hardened state, profile, debug-assertion state, and input.

`h`, profile, and debug assertions occur in neither body nor source-selection
predicate, and the proof is parametric over them. Target affects only the
separately proved compile-error gate. Each exact version has its own cited
premises.

## Covered predicates and closure certificates

Keeping every case dimension explicit, define

```text
L0(c) := F(c) and !f
L1(c) := F(c) and f and t in {X,A}
Covered_sound(c) := L0(c) or L1(c)
Covered_behavior(c) := L0(c) or L1(c).
```

The two branch proofs establish their respective lemmas for both obligations.
If `Required(c)`, either `!f`, giving `L0`, or `f`; then `t` is one of
`{X,A,W}` and the exclusion forces `t in {X,A}`, giving `L1`. Conversely each
lemma satisfies `Required`. Hence
`Required = Covered_sound = Covered_behavior`, proving separately
`Required subset Covered_sound` and `Required subset Covered_behavior`.
Their pointwise intersection also equals `Required`, which is the combined
closure certificate.

## TCB, documentation finding, and residual scope

TCB log identity is the supplied `TCB.md`. `BUILD-MAP-POLICY` is accepted only
for the three exact Cargo/Rust releases, named feature-to-cfg mappings,
target-to-`target_arch` mappings, and the selection/rejection consumers above.
It supplies no Rust semantics or backend correctness. CFG, CE, and OPTION are
exact-version authoritative axioms, not implementation assumptions. No other
premise or tool evidence is consumed.

The unsafe implementation is proved, but its adjacent safety comment is
proof-documentation deficient: it states the local `Some` fact without naming
the callee's `None`/UB obligation, cited contract, or resulting value. A compact
replacement is:

```rust
// SAFETY: Option::unwrap_unchecked is UB only for None. This receiver is
// constructed immediately as Some(value), so it is not None; the call returns
// that contained value.
```

This documentation finding changes neither implementation verdict. There is no
proved UB witness and no UB-free postcondition counterexample. Residual scope is
the unresolved identity of the published support promise and all backend,
binary, custom-target, non-named-version, or changed-toolchain claims. Re-audit
is required by any source/manifest/policy/TCB change, support-domain expansion,
different Cargo or Rust release, or material change to a consumed Rust page.
