# Focused unsafe-Rust source audit

## Claim, scope, and verdicts

The audited artifact is the complete supplied `focused-predicate-target` 0.1.0 source snapshot (`Cargo.toml`, both policy files, `TCB.md`, and `src/lib.rs`), edition 2021. This is a source-level Rust-abstract-semantics review at cutoff 2026-08-01; no build, execution, expansion, backend, or binary claim is made. There are no dependencies, generators, FFI, traits, fields, statics, or macros authored by the crate. The sole public surface is the safe function `value_or_zero(Option<u8>) -> u8`; its two definitions are configuration alternatives. The sole unsafe operation is `Option::unwrap_unchecked` at `src/lib.rs:18`.

* **Soundness: PROVED** for every full case in `D_A` below, relative to accepted `BUILD-MAP-POLICY` and the exact-version Rust axioms quoted below.
* **Documented postcondition: PROVED** on `D_A`: the result is the contained byte for `Some(byte)` and zero for `None`, under the same qualification.
* **Effective turbo/wasm32 rejection: PROVED** on `R_W` below, relative to `BUILD-MAP-POLICY`.
* **Identity of the crate's exact support promise: UNPROVED.** Scarlet and Indigo are current, incomparable commitments and no resolution rule is authorized. `D_A` is an audit envelope, not a declaration that union is the project's resolved promise.

There is no invariant-bearing state. The existing adjacent `SAFETY` comment is proof-documentation-deficient but the implementation obligation is proved by the reconstructed derivation below.

## Exact policy predicates and relationships

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` with the policy-defined triples, and `B={false,true}`. Writing `f` for turbo and `h` for hardened, the exact Scarlet predicate is

```text
S(v,t,f,h) := v∈V ∧ t∈T ∧
  (!f
   or (f and t=X and (!h or v>=1.85.0))
   or (f and t=A and h))
```

and the exact Indigo predicate is

```text
I(v,t,f,h) := v∈V ∧ t∈T ∧
  (!f
   or (f and t=X and (h or v>=1.86.0))
   or (f and t=A and !h and v>=1.85.0)).
```

They are unequal and incomparable. Witness `s=(1.84.0,X,true,false)` is in Scarlet because its `X` clause has `!h`, but not Indigo because both `h` and `v>=1.86.0` are false; hence `S⊄I`. Witness `i=(1.84.0,X,true,true)` is in Indigo because `h`, but not Scarlet because both `!h` and `v>=1.85.0` are false; hence `I⊄S`.

Let `P` be all Cargo profiles, `O=Val(Option<u8>)={None}∪{Some(x)|x∈0..=255}`, and a full case be the requested

```text
c=(v,t,f,h,p,d,input), where p∈P, d∈B, input∈O.
D_S(c) := S(v,t,f,h) ∧ p∈P ∧ d∈B ∧ input∈O.
D_I(c) := I(v,t,f,h) ∧ p∈P ∧ d∈B ∧ input∈O.
```

Select the conservative configuration predicate

```text
U(v,t,f,h) := v∈V ∧ t∈T ∧
  (!f or (f and t=X) or (f and t=A and (h or v>=1.85.0)))
```

and full audit domain

```text
D_A(c) := U(v,t,f,h) ∧ p∈P ∧ d∈B ∧ input∈O.
Required(c) := D_A(c).
```

Separate containment certificates: every Scarlet disjunct implies the corresponding `U` disjunct (`!f`; `f∧t=X`; or `f∧t=A∧h`), so `D_S⊆D_A`. Every Indigo disjunct likewise implies `!f`, `f∧t=X`, or `f∧t=A∧v>=1.85.0`, so `D_I⊆D_A`. All four remaining case dimensions are preserved unchanged in both arguments.

In fact `U=S∨I`: conversely, `!f` belongs to both; for `f∧t=X`, `h` selects Indigo and `!h` selects Scarlet; for `f∧t=A∧(h∨v>=1.85.0)`, `h` selects Scarlet, while `!h` forces `v>=1.85.0` and selects Indigo. This equality describes the chosen envelope; it does not resolve which published policy controls.

## Applicable Rust premises and TCB

For each exact release, the Reference says `cfg` “conditionally includes the thing it is attached to”; `all` is “true if all predicates are true,” and `not` is “true if its predicate is false”: [1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute). Each exact `compile_error!` page says it “Causes compilation to fail with the given error message when encountered”: [1.84.0](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85.0](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86.0](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).

For each exact release, `unwrap_or` “Returns the contained `Some` value or a provided default”; `unwrap_unchecked` “Returns the contained `Some` value,” and its Safety section says, “Calling this method on `None` is undefined behavior”: [1.84.0 `unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or), [1.84.0 unchecked](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.85.0 `unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or), [1.85.0 unchecked](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.86.0 `unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or), [1.86.0 unchecked](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked). These are per-release premises; no cross-release compatibility inference is used.

`BUILD-MAP-POLICY` is accepted human trust, limited exactly to Cargo 1.84.0/1.85.0/1.86.0 mapping the two named feature selections and the three named targets to their source `cfg` options for every supported profile. It is consumed only below for branch reachability and rejection. It supplies no Rust semantics or implementation correctness. No other non-authoritative premise is consumed. Re-audit on any trigger listed in `TCB.md`.

## Selection, rejection, and branch proofs

Define

```text
R_W(c) := v∈V ∧ t=W ∧ f ∧ h∈B ∧ p∈P ∧ d∈B ∧ input∈O.
C_N(c) := v∈V ∧ t∈T ∧ !f ∧ h∈B ∧ p∈P ∧ d∈B ∧ input∈O.
C_T(c) := v∈V ∧ t∈{X,A} ∧ f ∧ h∈B ∧ p∈P ∧ d∈B ∧ input∈O.
```

**Turbo/wasm32.** Policy-level: with `f=true,t=W`, every non-`!f` disjunct in both `S` and `I` requires `t=X` or `t=A`; hence `R_W∩D_S=R_W∩D_I=∅`. Source-level: on every `R_W` case, `BUILD-MAP-POLICY` makes both leaves of `all(feature="turbo",target_arch="wasm32")` true. The exact-version `cfg` rules include the item and `compile_error!` rejects compilation. This is independent of `h,p,d,input`; the API is never executed. Thus every such policy-excluded configuration is also effectively rejected, rather than merely undocumented.

**Non-turbo branch (`C_N`).** The build mapping plus exact-version `cfg` semantics includes lines 8–10 and excludes lines 14–19. For arbitrary full-case `input`, `input.unwrap_or(0)` returns its contained `x` for `Some(x)` and the provided `0` for `None`. There is no unsafe operation on this branch, and the documented postcondition holds.

**Turbo non-wasm branch (`C_T`).** The rejection predicate is false because `t∈{X,A}`; the build mapping and `cfg` semantics include lines 14–19 and exclude lines 8–10. Let `r=input.unwrap_or(0)`. The cited contract gives `r=x` for `Some(x)` and `r=0` for `None`. The receiver of the unsafe call is constructed at that expression as `Some(r)`, so it is not `None`; the sole documented safety obligation is satisfied. The call returns the contained `r`, proving both absence of UB at the unsafe site and the public postcondition.

Profiles and `debug_assertions` do not occur in source predicates or operations, and `h` affects policy membership but not selected code. The proofs therefore quantify parametrically over every `p,d,h,input`; no dimension is projected away.

## Covered predicates and closure

Let `Q(input,result)` mean `(input=None ∧ result=0) ∨ ∃x∈0..=255.(input=Some(x) ∧ result=x)`. The preceding per-release derivations establish, retaining the complete tuple:

```text
Covered_sound(c) := C_N(c) ∨ C_T(c).
Covered_behavior(c) := C_N(c) ∨ C_T(c), with Q established.
```

For arbitrary `c` with `Required(c)=D_A(c)`: if `!f`, then `c∈C_N`; if `f`, predicate `U` forces `t=X` or `t=A`, hence `c∈C_T`. Every other coordinate is carried unchanged. Therefore

```text
Required ⊆ Covered_sound
Required ⊆ Covered_behavior.
```

This supplies both whole-domain `PROVED` certificates. It also covers each candidate promise separately by `D_S⊆D_A` and `D_I⊆D_A`. The source-selection partition is exhaustive on `Required`; the separately proved `R_W` rejection lies outside it.

## Finding: local proof text is incomplete

`src/lib.rs:17` records the decisive local fact but does not state the callee's exact safety obligation or the postcondition used to prove the wrapper's behavior. This is documentation debt, not an implementation defect. Suggested adjacent replacement:

```rust
// SAFETY: `unwrap_unchecked` requires that its receiver is not `None`.
// This receiver is constructed here as `Some(value)`, so that requirement
// holds; the operation returns the contained `value`.
```

No code change was authorized. Re-audit if source, either policy, the accepted build mapping, supported versions/targets/features/profiles, or any consumed Rust documentation changes.
