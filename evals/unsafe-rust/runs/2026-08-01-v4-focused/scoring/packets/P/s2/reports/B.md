# Focused unsafe-code audit

## Claim, snapshot, and verdicts

This is a source-only audit of the exact supplied `Cargo.toml`, `src/lib.rs`, two policy documents, and `TCB.md`, cut off 2026-08-01. No generated code, dependencies, tests, execution, macro expansion, backend, or binary claim is in scope. The public surface is the safe free function `value_or_zero(Option<u8>) -> u8`, with mutually conditional definitions. The only unsafe operation is `Option::unwrap_unchecked` in the `turbo` definition. There are no public fields, constructors, traits, callbacks, FFI items, invariant-bearing representations, or other exported items.

Verdicts:

- **PROVED, relative to accepted `BUILD-MAP-POLICY` and the version-specific Rust axioms below:** every well-typed call in the conservative full-case audit domain is free of Rust undefined behavior.
- **PROVED under the same qualification:** every such call returns the contained byte, or zero for `None`.
- **PROVED under the same qualification:** every `turbo`/`wasm32` compilation in the stated version/feature/profile/debug domain is rejected before a library artifact is produced.
- **UNPROVED (policy identity only):** which one set, if any, is the crate's exact support promise. Scarlet and Indigo are incomparable current commitments and no resolution rule is authorized. The conservative audit domain below is not a resolution or a new support promise.

## Exact domains and relationships

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` with the triples defined by the policies, `B={false,true}`, `P` be all Cargo profiles, and
`O={None} union {Some(n) | n is a valid u8}`. A full case is
`c=(v,t,f,h,p,d,i) in V x T x B x B x P x B x O`.

The exact configuration predicates are:

```text
S_cfg(v,t,f,h) := v in V and t in T and (
  !f
  or (f and t = X and (!h or v >= 1.85.0))
  or (f and t = A and h)
)

I_cfg(v,t,f,h) := v in V and t in T and (
  !f
  or (f and t = X and (h or v >= 1.86.0))
  or (f and t = A and !h and v >= 1.85.0)
)
```

Their induced full-case domains are
`S(c):=S_cfg(v,t,f,h) and p in P and d in B and i in O` and identically
`I(c):=I_cfg(v,t,f,h) and p in P and d in B and i in O`.

Neither contains the other. The configuration `(1.84.0,X,true,false)` is in Scarlet: its `X and !h` term is true; it is not in Indigo because both `h` and `v>=1.86.0` are false. Conversely `(1.84.0,X,true,true)` is in Indigo by `X and h`, but not Scarlet because both `!h` and `v>=1.85.0` are false. Each satisfies the common `V,T` bounds; choosing any `p,d,i` lifts each witness to the corresponding full-case difference.

Select the conservative audit domain `A(c):=S(c) or I(c)`. Equivalently its configuration part is

```text
A_cfg := v in V and t in T and (
  !f or (f and t = X) or
  (f and t = A and (h or v >= 1.85.0))
).
```

Proof of equality: `S_cfg or I_cfg` has no `f,W` disjunct; for `f,X`, `h` selects Indigo and `!h` selects Scarlet, so every `v,h` is included; for `f,A`, Scarlet contributes `h` and Indigo contributes `!h and v>=1.85.0`. Conversely, each displayed normalized case selects the named policy term: `!f` selects both; `f,X,h` selects Indigo; `f,X,!h` selects Scarlet; `f,A,h` selects Scarlet; and `f,A,!h,v>=1.85.0` selects Indigo. Thus both directions hold. Separately, `S subseteq A` and `I subseteq A` follow by disjunction introduction, with every `p,d,i` unchanged.

Accordingly `Required_S(c)=S(c)` and `Required_I(c)=I(c)`. There is no authorized unique crate-level `Required`. For the conservative audit theorem only, `Required_A(c)=A(c)`.

## Authorities and TCB

For each of Rust 1.84.0, 1.85.0, and 1.86.0, the exact-version Conditional Compilation pages state: “The predicate is true if the option is set and false if it is unset”; for `all`, “It is true if all of the given predicates are true, or if the list is empty”; and for `not`, “It is true if its predicate is false and false if its predicate is true.” The `cfg`-attribute section states: “The `cfg` attribute conditionally includes the thing it is attached to based on a configuration predicate” and “If the predicate is false, the thing is removed from the source code.” ([1.84 predicate](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.84 attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute); [1.85 predicate](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [1.85 attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute); [1.86 predicate](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation), [1.86 attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute).)

At each exact version, `compile_error!` “causes compilation to fail with the given error message when encountered.” ([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).)

At each exact version, `unwrap_or` “Returns the contained `Some` value or a provided default.” ([1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or), [1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or), [1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).) `unwrap_unchecked` “Returns the contained `Some` value ... without checking that the value is not `None`,” and its Safety clause says: “Calling this method on `None` is undefined behavior.” ([1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked).) Direct per-release citations avoid any compatibility premise.

`BUILD-MAP-POLICY` is the sole admitted non-axiom premise. The authorized reviewer accepts, only for the three bundled Cargo releases, supplied manifest/source, all supported profiles, named feature cfgs, and three target-to-`target_arch` mappings, exactly the mapping recorded in `TCB.md`. It is consumed only for source selection and rejection. It supplies no Rust semantics or branch correctness. Every whole-case verdict above depends on it; local reasoning about an already-selected definition does not. No tool-derived evidence or other premise is used.

## Selection, rejection, and local proofs

Under the TCB mapping and cited cfg rules, `f=false` selects exactly the `not(feature="turbo")` definition; `f=true` selects exactly the other definition. Neither `h`, `p`, `d`, `v`, nor a non-wasm target changes either value computation.

For every hypothetical full `turbo`/`wasm32` case
`E(c):=v in V and t=W and f and h in B and p in P and d in B and i in O`, both policies exclude it: `!f`, `t=X`, and `t=A` are all false in each predicate. Independently, the TCB makes both leaves of `all(feature="turbo",target_arch="wasm32")` true; the cited `all` and cfg rules therefore include `compile_error!`, whose cited contract fails compilation. This proof is uniform over `v,h,p,d`; rejection precedes and is independent of runtime `i`. Thus `E` contains no shippable library case and is not silently counted as covered API execution.

Define `q(None)=0` and `q(Some(n))=n`.

- Non-turbo: `value.unwrap_or(0)` returns the contained `n` for `Some(n)` and the supplied default `0` for `None`. It is the documented safe operation, so every `i in O` is UB-free and the result is `q(i)`.
- Turbo: the first `unwrap_or(0)` produces `x=q(i)`. The unsafe receiver is then constructed locally as `Some(x)`, hence is not `None`. This proves the entire cited safety obligation for `unwrap_unchecked`; its return contract yields the contained `x=q(i)`. Thus every `i in O` is UB-free and satisfies the postcondition.

The existing safety comment records the decisive local fact (`Some` construction), so the implementation obligation is proved, but the proof artifact is deficient: it does not state the callee's `None`/UB obligation or the consumed return guarantee. Proposed replacement:

```rust
// SAFETY: `unwrap_unchecked` is UB only when its receiver is `None`.
// This receiver is constructed immediately as `Some(value)`, so it is not
// `None`; the call returns that contained `value`.
```

## Full-case coverage certificate

Without projecting any dimension away, define

```text
Covered_sound(c) := A(c) and (
  (!f and the selected non-turbo execution on i is UB-free) or
  (f and t in {X,A} and the selected turbo execution on i is UB-free)
)

Covered_post(c) := A(c) and (
  (!f and the selected non-turbo result on i equals q(i)) or
  (f and t in {X,A} and the selected turbo result on i equals q(i))
).
```

Take arbitrary `c` with `Required_A(c)`. If `!f`, selection plus the non-turbo lemma puts the same complete `(v,t,f,h,p,d,i)` in both Covered predicates. If `f`, normalized `A_cfg` implies `t=X` or `t=A`; selection plus the turbo lemma does likewise. These cases exhaust `B`. The lemmas quantify every `v,t,h,p,d,i`; irrelevance of `v,h,p,d` follows from their absence from the selected computations, not from projection. Hence
`Required_A subseteq Covered_sound intersect Covered_post`. Conversely both Covered predicates include `A(c)` by definition, so each equals `A`; aggregate closure is exact. Since `S subseteq A` and `I subseteq A`, the same proofs close each published policy domain separately.

## Residual scope and review triggers

Only the identity of the single governing support promise is unresolved; authorized policy resolution is required. Re-audit on any change to the supplied source, manifest, either policy, feature/target/profile scope, any of the three Rust/Cargo identities or cited contracts, `BUILD-MAP-POLICY` disposition/mapping, or the documented postcondition. No code change was made.
