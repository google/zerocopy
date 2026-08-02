# Focused unsafe Rust source audit

## Claim, snapshot, and verdicts

This review covers the supplied `Cargo.toml`, `POLICY-SCARLET.md`,
`POLICY-INDIGO.md`, `TCB.md`, and `src/lib.rs` source snapshot, under Rust
1.84.0, 1.85.0, and 1.86.0. It is source-level only: no compiler/backend,
binary, tests, generated artifacts, dependencies, or prior audit are claimed.
Review date/audit cutoff: 2026-08-01. The support documents are static for this
snapshot, so the cutoff does not resolve their conflict.

| Claim | Verdict | Qualification |
|---|---|---|
| Every well-typed safe call of `value_or_zero` in `Required` is free of Rust UB | **PROVED** | Relative to `TCB-BUILD-MAP` only for mapping policy configurations to source branches; branch correctness uses the version-specific Rust axioms below. |
| The call returns the contained byte, or zero for `None`, throughout `Required` | **PROVED** | Same qualification. |
| Every `turbo`/`wasm32` configuration is rejected before a library artifact is produced | **PROVED** | Conspicuously conditional on `TCB-BUILD-MAP`; this is a compilation claim, not a runtime-input claim. |
| One uniquely determined exact project support predicate can be recovered | **UNPROVED** | Scarlet and Indigo are incomparable current exact commitments, and no resolution rule is authorized. |

The combined mandatory soundness-and-requested-behavior result is **PROVED over
the conservative audit domain `Required` defined below, relative to
`TCB-BUILD-MAP`**. `Required` is not asserted to be the crate's exact support
promise.

## Exact predicates and full-case domains

Let

* `V = {1.84.0, 1.85.0, 1.86.0}`;
* `X = x86_64-unknown-linux-gnu`, `A = aarch64-unknown-linux-gnu`, and
  `W = wasm32-unknown-unknown`;
* `B = {false,true}`; `f` means `turbo`, and `h` means `hardened`;
* `P` be the symbolic set of **all Cargo profiles** (no finite enumeration is
  substituted); and
* `O = {None} union {Some(n) | n is any u8}`, exactly every valid `Option<u8>`.

For the full case `c=(v,t,f,h,p,d,o)`, with `d` the state of debug assertions,
the separately reproduced configuration predicates are

```text
S(v,t,f,h) := v in V and t in {X,A,W} and
  (!f
   or (f and t = X and (!h or v >= 1.85.0))
   or (f and t = A and h))

I(v,t,f,h) := v in V and t in {X,A,W} and
  (!f
   or (f and t = X and (h or v >= 1.86.0))
   or (f and t = A and !h and v >= 1.85.0))
```

Their induced full-case domains, preserving every dimension, are

```text
D_S(c) := S(v,t,f,h) and p in P and d in B and o in O
D_I(c) := I(v,t,f,h) and p in P and d in B and o in O.
```

Neither contains the other. `(1.84.0,X,true,false)` satisfies Scarlet's
`t=X and !h` term but not Indigo's `h or v>=1.86.0`, so `S` is not a subset of
`I`. Conversely, `(1.84.0,X,true,true)` satisfies Indigo's `t=X and h` term but
not Scarlet's `!h or v>=1.85.0`, so `I` is not a subset of `S`. Extending either
witness with any `p in P`, `d in B`, and `o in O` separates the full-case
domains. Thus they are unequal and incomparable.

Select the least union as the conservative audit configuration predicate:

```text
U(v,t,f,h) := S(v,t,f,h) or I(v,t,f,h)
            = v in V and t in {X,A,W} and
              (!f or (f and
                (t = X or (t = A and (h or v >= 1.85.0)))))

Required(c) := U(v,t,f,h) and p in P and d in B and o in O.
```

The equality follows by cases. For `!f`, both policies admit every listed
`v,t,h`. For `f,t=X`, Scarlet admits every `h=false` case and Indigo every
`h=true` case, hence all `v,h`. For `f,t=A`, Scarlet admits all `h=true` cases,
while Indigo admits precisely `h=false,v>=1.85.0`, yielding
`h or v>=1.85.0`. Neither admits `f,t=W`. Separately, `D_S subseteq Required`
because `S implies S or I`, and `D_I subseteq Required` because
`I implies S or I`; the other full-case conjuncts are identical. This proves
both required containments without resolving which policy is authoritative.

## Authority and TCB audit log

For each of 1.84.0, 1.85.0, and 1.86.0, the applicable Reference pages are:
[conditional predicates 1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
[1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation),
[1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation),
and [`cfg` attribute 1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute).
They state, respectively, “It is true if all of the given predicates are true”
and “It is true if its predicate is false”; for item selection: “If the
predicate is true, the thing is rewritten to not have the cfg attribute ... If
the predicate is false, the thing is removed”. These are `AX-CFG-{84,85,86}`.

The exact-version `compile_error!` pages
([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
[1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
[1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)) say:
“Causes compilation to fail with the given error message when encountered.”
These are `AX-COMPILE-ERROR-{84,85,86}`.

The exact-version `Option` pages are
[`unwrap_or` 1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or),
[1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or),
[1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or),
and [`unwrap_unchecked` 1.84](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.85](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
[1.86](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked).
Each says `unwrap_or` “Returns the contained `Some` value or a provided
default”; `unwrap_unchecked` “Returns the contained `Some` value”, while
“Calling this method on `None` is undefined behavior.” These are
`AX-OPTION-{84,85,86}` and supply separate exhaustive version coverage—no
cross-version compatibility assumption is used.

`TCB-BUILD-MAP` is the sole non-axiom entry: the accepted `BUILD-MAP-POLICY` in
`TCB.md`, with the exact three toolchain-bundled Cargo releases, manifest, named
features, targets, and all supported profiles. It admits only that enabled and
disabled features set and do not set their matching feature predicates, and
that `X/A/W` set `target_arch` to `x86_64/aarch64/wasm32`. It is consumed only
to map policy cases to source reachability and to prove effective rejection.
It supplies no Rust semantics, branch correctness, compatibility, or binary
correctness. Its disposition is accepted by the authorized human reviewer.
No other TCB premise is consumed.

## API, rejection, and obligation proofs

The complete exposed surface is one safe free function, `value_or_zero`, with
two mutually exclusive `cfg` definitions. There are no public fields,
constructors, traits/impls, macros generating APIs, hidden items, callbacks,
FFI, allocation, concurrency, or invariant-bearing state. The only unsafe
operation is `Option::unwrap_unchecked` at `src/lib.rs:18`. No generated code or
tool-derived evidence exists.

Define `Q(None)=0` and `Q(Some(n))=n`, and define the actually proved source
case predicate without dropping any axes:

```text
K(c) := v in V and t in {X,A,W} and f in B and h in B
        and p in P and d in B and o in O
Covered_sound(c) := K(c) and (!f or t != W)
Covered_behavior(c) := K(c) and (!f or t != W).
```

* **Non-turbo branch (`!f`).** `TCB-BUILD-MAP` plus `AX-CFG-v` selects only
  lines 7-10. `o.unwrap_or(0)` returns the contained `n` for `Some(n)` and the
  provided `0` for `None`, so it returns `Q(o)`. There is no unsafe operation.
* **Turbo, non-wasm branch (`f and t!=W`).** The same reachability premises
  select lines 13-19 and do not encounter the compile error. The first
  `unwrap_or(0)` establishes local fact `r=Q(o)`. The unsafe receiver is then
  constructed syntactically as `Some(r)`. Its exact safety obligation is “the
  receiver is not `None`”; construction proves it. `AX-OPTION-v` then gives
  both absence of the documented UB and return value `r=Q(o)`. This proof is
  parametric in `h,p,d,o` and partitioned exhaustively by each exact `v` axiom.
* **Every turbo/wasm case.** Both policies exclude it: when `f` is true, their
  only target terms require `X` or `A`. Independently, for every `v in V`,
  `h,p,d`, and would-be `o`, `TCB-BUILD-MAP` makes both operands of the
  crate-level `all(feature="turbo",target_arch="wasm32")` true;
  `AX-CFG-v` retains the macro and `AX-COMPILE-ERROR-v` makes compilation fail.
  Thus no call/input execution exists. This enforcement conclusion must not be
  detached from its accepted TCB premise.

`U` implies `!f or t=X or t=A`, hence `U implies (!f or t!=W)`. All remaining
conjuncts of `Required`, `Covered_sound`, and `Covered_behavior` are identical.
Therefore, separately,
`Required subseteq Covered_sound` and
`Required subseteq Covered_behavior`. The aggregate coverage predicate is their
intersection, which is the same predicate, so `Required` is contained in it.
This is the whole-domain certificate for both **PROVED** verdicts.

## Findings, residual scope, and maintenance

`F-POLICY`: the support-promise identity remains **UNPROVED**. The smallest
missing premise is an authorized rule selecting, merging, or otherwise
reconciling Scarlet and Indigo. The conservative union prevents that policy
defect from leaving either candidate domain unaudited, but does not repair it.

The implementation obligation at line 18 is proved. Its adjacent safety
comment records the decisive local `Some` construction, but omits the callee's
exact “not `None`” obligation. A proof-grade replacement is:

```rust
// SAFETY: `unwrap_unchecked` requires this receiver not to be `None`.
// It is constructed immediately here as `Some(value)`, so that holds.
```

This is proof-documentation debt, not an implementation defect. No UB witness
or UB-free postcondition counterexample exists in the audited domain.

Residual scope excludes unsupported configurations and all binary/backend
correctness. Re-audit is required for any source/manifest/policy change,
resolution of the policy conflict, Rust or cited-documentation version change,
feature/target/profile scope change, or any change to `TCB-BUILD-MAP` identity,
mapping, disposition, or consumers.
