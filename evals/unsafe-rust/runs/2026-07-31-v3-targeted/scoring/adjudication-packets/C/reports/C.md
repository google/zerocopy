# Unsafe Rust source audit

## Claim and verdicts

The audited artifact is exactly the supplied `Cargo.toml`, `src/lib.rs`, two
published policies, and `TCB.md`; no repository identity is asserted. For every
well-typed safe call to `value_or_zero` in every configuration in `Required`
below, under Rust's documented source semantics and relative only to the TCB
listed below:

| Claim | Verdict | Certificate |
|---|---|---|
| Freedom from Rust undefined behavior | **PROVED** | OBL-1--4 and `Required ⊆ Covered` |
| Documented result: contained byte for `Some`, zero for `None` | **PROVED** | OBL-2--4 |
| One resolved project support predicate | **UNPROVED** | Scarlet and Indigo conflict and no resolution is authorized |

The strongest non-policy-selecting conclusion is therefore source soundness
and the stated behavior over the conservative union of both commitments. This
does not resolve or redefine the project's support promise. No backend,
binary, compiler-implementation, performance, or other robustness claim is
made.

## Snapshot, boundary, and inventory

The crate is edition 2021, `no_std`, has no dependencies or generators, and
declares independent `turbo` and `hardened` features. Rust/stdlib versions are
exactly 1.84.0, 1.85.0, and 1.86.0. The complete language-reachable crate-owned
surface is one safe public free function, with mutually exclusive
`#[cfg(not(feature = "turbo"))]` and `#[cfg(feature = "turbo")]` definitions.
There are no fields, constructors, traits/impls, callbacks, FFI, statics,
reexports, hidden items, exported macros, generated APIs, or owned invariants.
The only unsafe operation is the turbo definition's
`Option<u8>::unwrap_unchecked`. The `compile_error!` invocation is an internal
configuration-rejection site.

## Required-domain recovery and effective rejection

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}`, and let `f,h` have the meanings in
the policies. Preserve the controlling predicates:

```text
I = !f or (f and t=X and (h or v>=1.86.0))
         or (f and t=A and !h and v>=1.85.0)
S = !f or (f and t=X and (!h or v>=1.85.0))
         or (f and t=A and h)
```

With the shared `v∈V`, `t∈T`, Boolean `f,h`, all profiles, and both debug-
assertion states, choose only the conservative audit predicate
`Required = I ∪ S`. Exact normalization gives:

```text
Required = !f or (f and t=X)
              or (f and t=A and (h or v>=1.85.0)).
```

Proof of equality: `!f` is common; neither policy admits `f∧t=W`; for `f∧t=X`,
Indigo admits `h` at 1.84 while Scarlet admits `!h`, Scarlet admits both states
from 1.85, and both admit both at 1.86; for `f∧t=A`, Scarlet admits `h` at every
version and Indigo adds `!h` exactly from 1.85. Thus both `I⊆Required` and
`S⊆Required`, without selecting either policy.

BUILD-MAP-C establishes, only for the three versions, named targets, features,
and profiles, that Cargo features and `target_arch` set the corresponding cfgs.
The version-matched Reference says a true cfg predicate includes its item and a
false one removes it ([1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute),
[1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute));
`compile_error!` causes compilation to fail when encountered
([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html),
[1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html),
[1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)). Therefore
every `f∧t=W` case is effectively rejected before a library artifact can ship,
in every profile/debug-assertion state. Both policies already exclude those
cases; the proof does not silently enlarge either promise. No other policy
exclusion is source-enforced, nor is enforcement needed for this union proof.

## Obligation ledger and derivations

| ID | Proposition and proof | Domain | Status |
|---|---|---|---|
| OBL-1 | cfg selection/rejection has the behavior above, from version-matched cfg and macro axioms plus BUILD-MAP-C | all policy axes | PROVED |
| OBL-2 | Non-turbo `unwrap_or(0)` returns the `Some` byte or `0` for `None` | `Required∧!f` | PROVED |
| OBL-3 | At `unwrap_unchecked`, `value` is not `None`; the dominating `is_none()` true branch returned, and `Option` has only `None` and `Some` | `Required∧f` | PROVED |
| OBL-4 | The unchecked call returns the contained byte; combining OBL-2/3 proves the public postcondition | all `Required` | PROVED |

For each exact release, `is_none` “returns true” for `None`,
`unwrap_unchecked` returns the contained `Some` value and calling it on `None`
is undefined behavior, and `unwrap_or` returns the contained value or supplied
default: [1.84 is_none](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none),
[unchecked](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked),
[unwrap_or](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or);
[1.85 is_none](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none),
[unchecked](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked),
[unwrap_or](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or);
[1.86 is_none](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none),
[unchecked](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked),
[unwrap_or](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).
These are an exhaustive release partition, not compatibility extrapolation.

For `f=false`, OBL-2 applies parametrically to every target, `h`, profile, and
assertion state. For `f=true`, OBL-3/4 do likewise wherever `Required` admits
X or A. The source has no arithmetic, assertions, target-dependent unsafe
semantics, or other branches affected by remaining axes. Hence aggregate
`Covered = Required`, proving `Required ⊆ Covered`.

## TCB audit log

- **BUILD-MAP-C — IMPLEMENTATION/build-tool mapping, accepted.** Exact
  proposition, identities, consumers, exclusions, and triggers are those in
  supplied `TCB.md`. It is consumed only by OBL-1 and domain reachability. It
  supplies no Rust semantic or branch-correctness fact.
- **AX-OPT-184/185/186 and AX-CFG-184/185/186 — AXIOM.** Exact propositions are
  the narrow versioned Rust documentation statements cited above; consumers
  are OBL-1--4. Applicability is one named release each.

No other trust, dependency, tool result, test, or execution evidence is used.

## Findings and residual scope

**DOC-1 — deficient adjacent proof, implementation still proved.** The current
comment states the crucial control-flow fact but does not name the unchecked
operation's exact precondition. Suggested replacement:

```rust
// SAFETY: `unwrap_unchecked` requires `value` not be `None`.
// `is_none()` is true exactly for `None`; that branch returned, so here
// `value` is `Some(_)`.
```

**POLICY-1 — unresolved support identity.** The smallest missing proposition is
an authorized rule selecting, superseding, or reconciling Scarlet and Indigo.
This blocks a claim about the one true project promise, but not the proved
conservative-union source theorem.

No target was built, run, tested, or macro-expanded. Custom targets, other Rust
versions, backend/binary correctness, and configurations outside both policies
are excluded. Re-audit on any source, manifest, policy/resolution, TCB
disposition/mapping, supported version/target/feature/profile, or cited Rust
contract change. Every in-scope surface, obligation, postcondition, premise,
and unresolved claim has a disposition above.
