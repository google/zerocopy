# Focused unsafe-Rust source audit

## Claim and results

This audit covers the complete supplied `focused-predicate-target` source snapshot: `Cargo.toml`, `src/lib.rs`, both published policies, and `TCB.md`. It is a source-level claim under the documented Rust abstract semantics, not a compiler-backend or binary claim. Audit cutoff: 2026-08-01. TCB log identity is the supplied `TCB.md` snapshot; no revision identifier is stated. Skill identity is the supplied `unsafe-rust` package; no revision identifier is stated. No generated code, dependencies, FFI, macros, stateful invariants, tests, builds, or prior audit results are in scope or used.

| Claim | Required domain | Result | Qualification |
|---|---|---|---|
| Every well-typed safe call of `value_or_zero` is free of Rust UB | conservative domain `R` below | **PROVED** | Relative to accepted `BUILD-MAP-POLICY` and the exact-version Rust axioms quoted below |
| The return is the contained byte, or zero for `None` | `R` | **PROVED** | Same qualification |
| Either published policy is *the* exact crate support promise | identity of Scarlet versus Indigo | **UNPROVED** | The documents are incomparable and no resolution rule is authorized |

The combined mandatory soundness-and-behavior result is **PROVED over `R`**, relative to that TCB. This does not resolve or redefine the project's exact support promise.

## Exact domains and policy relationship

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` with the triples' meanings exactly as in the policies, `B={false,true}`, `P` be all Cargo profiles, `D=B` be both debug-assertion states, and

`O={None} union {Some(n) | n is a u8}`.

A full case is `c=(v,t,f,h,p,d,i)` in `K=V x T x B x B x P x D x O`. Comparisons of versions below are only over the finite set `V`.

The exact Scarlet configuration predicate is

`S(v,t,f,h) := v in V and t in T and [!f or (f and t=X and (!h or v>=1.85.0)) or (f and t=A and h)]`.

The exact Indigo configuration predicate is

`I(v,t,f,h) := v in V and t in T and [!f or (f and t=X and (h or v>=1.86.0)) or (f and t=A and !h and v>=1.85.0)]`.

Their induced full-case domains are

`D_S(c) := c in K and S(v,t,f,h)` and `D_I(c) := c in K and I(v,t,f,h)`.

They are unequal and incomparable:

* `(1.84.0,X,true,false)` is in Scarlet because its `X` clause has `!h`; it is not in Indigo because `h` and `v>=1.86.0` are both false.
* `(1.84.0,X,true,true)` is in Indigo because its `X` clause has `h`; it is not in Scarlet because `!h` and `v>=1.85.0` are both false.

Thus neither `D_S subseteq D_I` nor `D_I subseteq D_S`; adding any `p in P`, `d in D`, and `i in O` lifts each witness to a full-case witness.

Select the conservative audit domain

`R(c) := D_S(c) or D_I(c)`.

For every `c`, `D_S(c)` implies `R(c)` by the left disjunct, and `D_I(c)` implies `R(c)` by the right disjunct. Hence `D_S subseteq R` and `D_I subseteq R` separately. `R` is the union of the candidate commitments, used only as an audit requirement; it is not asserted to be the exact project promise.

## Exact-version semantic premises

For each of Rust 1.84.0, 1.85.0, and 1.86.0, the Reference states: “The `cfg` attribute conditionally includes the thing it is attached to based on a configuration predicate.” It further states: “If the predicate is true, the thing is rewritten to not have the `cfg` attribute on it. If the predicate is false, the thing is removed from the source.” It defines `all()` as true when all its predicates are true, and `not()` as true when its predicate is false. ([1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute); predicate definitions: [1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation)).

Each exact-version standard-library page says: “The `compile_error!` macro causes compilation to fail with the given error message when encountered.” ([1.84.0](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85.0](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86.0](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)).

For `Option::unwrap_or`, each exact-version page says: “Returns the contained `Some` value or a provided default.” ([1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or), [1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or), [1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or)). For `Option::unwrap_unchecked`, each says: “Returns the contained `Some` value, consuming the `self` value, without checking that the value is not `None`,” and its Safety section says: “Calling this method on `None` is undefined behavior.” ([1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked)). These are three release-specific premise sets; no cross-release compatibility premise is used.

## Selection and effective rejection

`BUILD-MAP-POLICY` is consumed only here. For every `v in V` and `p in P`, it maps enabled `turbo`/`hardened` to their like-named feature cfgs and maps `X,A,W` to `x86_64,aarch64,wasm32`. With the quoted cfg rules, complete source inspection gives this exhaustive partition:

* `!f`: the non-turbo function is included, the turbo function removed, and the compile error removed.
* `f and t in {X,A}`: the turbo function is included, the non-turbo function removed, and the compile error removed.
* `f and t=W`: both predicates in `all(feature="turbo",target_arch="wasm32")` are true, so `compile_error!` is included and compilation fails before a library API can execute.

The source predicates mention neither `h`, profile, debug assertions, nor input; the partition is therefore parametric over those dimensions. Input exists only for an emitted API call.

Policy-level exclusion is independent: for `f=true,t=W`, `!f` is false and every `X` or `A` conjunct is false in both `S` and `I`. Thus every such full case is absent from both policy domains. Source-level rejection additionally covers every such build in `K`, for either `h`, every profile and debug state, and any hypothetical input, relative to `BUILD-MAP-POLICY`.

## API inventory and obligation ledger

The sole language-reachable crate API is one configuration-selected safe free function `pub fn value_or_zero(Option<u8>)->u8`. There are no public fields, constructors, traits or impls, hidden items, callbacks, exported macros, unsafe APIs, or persistent invariant-bearing state. The only unsafe operation is `Some(value).unwrap_unchecked()` on the turbo branch.

Define `spec(None)=0` and `spec(Some(x))=x`.

| ID | Domain and obligation | Proof | Status |
|---|---|---|---|
| O-NT | Every `c in K` with `!f`: no UB and result `spec(i)` | `i.unwrap_or(0)` is a safe call and, by its quoted contract, returns `x` for `Some(x)` and the supplied `0` for `None` | **PROVED** |
| O-T-UNSAFE | Every `c in K` with `f,t in {X,A}`: receiver of `unwrap_unchecked` is not `None` | First `unwrap_or(0)` yields a `u8` named `value`; the receiver is then constructed at the call site as the `Some(value)` variant. It is therefore not `None`, satisfying the complete quoted safety obligation | **PROVED** |
| O-T-POST | Same cases: result `spec(i)` | The quoted contract returns the contained value, hence the unsafe call returns `value`; the first call made `value=spec(i)` | **PROVED** |
| O-REJECT | Every `c in K` with `f,t=W`: no shippable API case | Selection/rejection proof above | **PROVED**, relative to `BUILD-MAP-POLICY` |

The local `SAFETY` comment records the decisive source fact but omits the callee obligation and returned-value consequence. The implementation proof is complete; the proof artifact is deficient under proof-grade documentation. Proposed replacement:

```rust
// SAFETY: `unwrap_unchecked` requires the receiver not to be `None`.
// This receiver is constructed here as `Some(value)`, so that requirement
// holds; the operation returns the contained `value`.
```

This is a documentation finding, not an implementation defect or a caller-facing hidden precondition.

## Full-case coverage and closure

For this audit, `Required(c) := R(c)`. The soundness derivation covers

`Covered_sound(c) := c in K and [!f or (f and t in {X,A})]`,

and the behavioral derivation covers the identical full-case predicate

`Covered_post(c) := c in K and [!f or (f and t in {X,A})]`.

These predicates retain `v,t,f,h,p,d,i` through membership in `K`; O-NT and O-T quantify parametrically over every omitted fiber value, including every valid `Option<u8>`.

For any `c in Required`, either its Scarlet or Indigo predicate holds. If `!f`, it is in both covered predicates by O-NT. If `f`, inspection of every positive disjunct of either exact policy shows `t=X` or `t=A`, so it is in both covered predicates by O-T-UNSAFE and O-T-POST. Therefore

`Required subseteq Covered_sound intersection Covered_post`.

This is the required whole-domain certificate for both **PROVED** verdicts. No sampled enumeration substitutes for it; version applicability is an exhaustive three-member partition backed by the three exact-version documentation sets.

## TCB audit log, residual scope, and triggers

* **BUILD-MAP-POLICY (IMPLEMENTATION/build tool): accepted.** Exact identity, proposition, scope, consumers, exclusions, and re-audit trigger are those in supplied `TCB.md`. Consumers here are only branch reachability and effective rejection. It supplies no Rust semantics or branch correctness.
* **AXIOM-CFG-{1.84,1.85,1.86}, AXIOM-COMPILE-{1.84,1.85,1.86}, AXIOM-OPTION-{1.84,1.85,1.86}: authoritative Rust premises.** Exact propositions, identities, quotations, version scopes, links, and consumers appear above.
* No other build-tool, compiler-implementation, dependency, environment, tool-derived, probabilistic, or compatibility premise is consumed. No test or tool evidence is claimed.

Residual scope is compiler/backend/binary correctness and unsupported configurations. The exact project support-promise identity remains unresolved; an authorized precedence, supersession, intersection, union, or other rule is required to resolve it. Re-audit on any supplied source, manifest, policy, accepted TCB disposition/mapping, supported version/target/feature/profile/debug domain, or consumed authoritative contract change.

All in-scope surfaces, configuration paths, unsafe obligations, mandatory postconditions, policy relationships, and full-case dimensions have a disposition above.
