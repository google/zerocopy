# Focused unsafe-Rust source audit

## Claim, snapshot, and verdicts

The audited artifact is exactly the supplied `Cargo.toml`, `src/lib.rs`, two
published policies, and `TCB.md`: package `focused-predicate-target` 0.1.0,
edition 2021, with no dependencies or generated artifacts. The toolchain domain
is the three exact Rust/standard-library releases below. This is a source-level
claim under documented Rust abstract semantics, not a claim about compiler
backends or binaries.

For a full case `c = (v,t,f,h,p,d,i)`, the claims are: (SND) every well-typed
safe call of the selected `value_or_zero` implementation is free of Rust UB;
and (POST) if it returns `r`, then
`Q(i,r) := (i=None => r=0) and (i=Some(n) => r=n)`.

- **SND: PROVED** over `Required(c)` defined below, relative to accepted
  `BUILD-MAP-POLICY` and the exact-version Rust axioms recorded below.
- **POST: PROVED** over the same domain and TCB.
- **Combined mandatory result: PROVED**, with the same qualification.

Each published policy-induced domain is therefore covered separately. This
does **not** resolve which domain is the crate's exact support promise: both
policies are current and no rule chooses or combines them.

## Exact policy predicates and full-case domains

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}`, where `X`, `A`, and `W` have the
exact triples defined in the policies; let `f,h,d` be Booleans, `P` be all
Cargo profiles, and `O` be every valid `Option<u8>` (`None` and every
`Some(n)` for valid `u8` `n`). Scarlet's exact configuration predicate is

```text
C_S(v,t,f,h) := v in V and t in {X,A,W} and (
  !f
  or (f and t = X and (!h or v >= 1.85.0))
  or (f and t = A and h)
)
```

Indigo's exact configuration predicate is

```text
C_I(v,t,f,h) := v in V and t in {X,A,W} and (
  !f
  or (f and t = X and (h or v >= 1.86.0))
  or (f and t = A and !h and v >= 1.85.0)
)
```

They are unequal and incomparable. `(1.84.0,X,true,false)` is Scarlet but not
Indigo. `(1.84.0,X,true,true)` is Indigo but not Scarlet. Thus neither
`C_S subseteq C_I` nor `C_I subseteq C_S`.

The policy-induced full-case domains, without dropping any dimension, are

```text
D_S(c) := C_S(v,t,f,h) and p in P and d in {false,true} and i in O
D_I(c) := C_I(v,t,f,h) and p in P and d in {false,true} and i in O
```

I select the conservative audit domain

```text
Required(c) := D_S(c) or D_I(c).
```

Separately, `D_S(c) => Required(c)` by left disjunction introduction, and
`D_I(c) => Required(c)` by right disjunction introduction. Hence it contains
both candidate commitments. It is their audit union, not an authorized union
of support promises.

## Configuration and API closure

Define the dimension-preserving base

```text
B(c) := v in V and t in T and f,h,d in {false,true}
        and p in P and i in O
N(c) := B(c) and !f
U(c) := B(c) and f and t in {X,A}
Covered_SND(c)  := N(c) or U(c)
Covered_POST(c) := N(c) or U(c)
```

Relative to `BUILD-MAP-POLICY`, feature and target values set the correspondingly
named `cfg` options. The exact-version `cfg` axioms then give this exhaustive
source partition:

- On `N`, `#[cfg(not(feature="turbo"))]` includes lines 8--10 and removes lines
  14--19. The `compile_error!` item is removed.
- On `U`, the non-turbo definition is removed, the turbo definition at lines
  14--19 is included, and the `compile_error!` item is removed because the
  target is not `wasm32`.
- For every `f=true,t=W` combination (all `v,h,p,d`), both policies exclude the
  configuration: `!f` is false and both remaining disjuncts require `X` or
  `A`. Independently, and conspicuously **relative to BUILD-MAP-POLICY**, the
  source `all(feature="turbo",target_arch="wasm32")` predicate is true, so
  lines 3--4 are included and `compile_error!` fails compilation. Thus every
  turbo/wasm case is both policy-excluded and effectively source-rejected; no
  runtime input is reached.

For closure, take arbitrary `c` with `Required(c)`. Either policy conjunct
implies `B(c)`. If `!f`, then `N(c)`. If `f`, inspection of either exact policy
shows its satisfied turbo disjunct requires `t=X` or `t=A`, hence `U(c)`.
Therefore

```text
Required subseteq Covered_SND
Required subseteq Covered_POST.
```

This argument is parametric in `h,p,d,i` rather than silently projecting them
away. The code contains no profile, hardened, or debug-assertion selector, so
those axes do not change either branch proof.

The complete language-reachable API surface is one safe free function,
`pub fn value_or_zero(Option<u8>) -> u8`, with exactly one definition in each
buildable case above. There are no public fields, constructors, user traits,
macros, reexports, hidden items, FFI, allocation, concurrency, or invariant-
bearing state. The sole unsafe operation is the turbo definition's
`Option::unwrap_unchecked` call.

## Obligation ledger and proofs

| ID | Domain | Obligation | Derivation | Status |
|---|---|---|---|---|
| N-SND | `N(c)` | safe implementation has no UB | `unwrap_or(0)` is a safe standard-library call with the exact behavior below; there is no unsafe operation | PROVED |
| N-POST | `N(c)` | `Q(i,r)` | `unwrap_or` returns the contained value for `Some(n)` and the supplied `0` for `None` | PROVED |
| U-SND | `U(c)` | `unwrap_unchecked` receiver is not `None` | first `x=i.unwrap_or(0)`; the receiver is then syntactically constructed as `Some(x)`, so the sole stated safety prohibition is false | PROVED |
| U-POST | `U(c)` | `Q(i,r)` | `x=n` for `Some(n)` and `x=0` for `None`; unwrapping `Some(x)` returns its contained `x` | PROVED |

These proofs quantify over every `i in O`. The `N` and `U` lemmas union to each
`Covered` predicate; the two containment results above supply the required
whole-domain certificates.

The implementation proof at lines 17--18 is correct, but its `SAFETY` comment
is proof-documentation deficient: it gives the decisive local fact but omits
the callee's exact obligation and resulting postcondition. Proposed replacement
(review only; the source was not changed):

```rust
// SAFETY: `Option::unwrap_unchecked` is UB when called on `None`. This
// receiver is constructed immediately as `Some(value)`, so it is not `None`;
// the call returns that contained `value`.
```

## Rust axioms and TCB audit log

All quotations below were verified with identical relevant wording in the
three exact releases; no version interpolation or compatibility assumption is
used.

- **AX-OR** — [1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or),
  [1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or),
  [1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or):
  “Returns the contained `Some` value or a provided default.” This proves both
  case equations for the first operation on each branch.
- **AX-UNCHECKED** — [1.84.0](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
  [1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked):
  “Returns the contained `Some` value ... without checking that the value is
  not `None`.” “Calling this method on `None` is undefined behavior.” These
  supply the exact local prohibition, return fact, and UB consequence.
- **AX-CFG-PRED** — conditional-compilation pages for
  [1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation),
  [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), and
  [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation):
  a configuration-option predicate is “true if the option is set”; `all` is
  “true if all of the given predicates are true”; `not` is “true if its
  predicate is false.”
- **AX-CFG-ATTR** — `cfg`-attribute pages for
  [1.84.0](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
  [1.85.0](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), and
  [1.86.0](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute):
  it “conditionally includes the thing it is attached to”; when false, “the
  thing is removed from the source code.”
- **AX-COMPILE-ERROR** — [1.84.0](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
  [1.85.0](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), and
  [1.86.0](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html):
  “Causes compilation to fail with the given error message when encountered.”

**BUILD-MAP-POLICY (accepted OUT-OF-BAND/IMPLEMENTATION premise):** exactly the
toolchain-bundled Cargo releases for 1.84.0, 1.85.0, and 1.86.0 map the two
named features and three targets to the source `cfg` options as stated in
`TCB.md`, for every supported profile. It is consumed only by branch
reachability and effective rejection, never as a Rust semantic or branch-
correctness premise. Its identity, manifest/source/cfg changes, or human
disposition trigger re-audit. No other implementation premise is consumed.

No tests, compilation, execution, macro expansion, or tool-derived proof was
used. Residual scope is the unresolved identity of the exact published support
promise and all backend/binary behavior; neither weakens the proved source
claims over the explicitly conservative audit domain. Re-audit is required for
changes to source, policies or conflict resolution, manifest/features/targets,
the accepted TCB mapping, supported Rust versions, or any cited contract.
