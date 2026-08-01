# Focused unsafe-Rust source review

## Claim frame, snapshot, and domain

Reviewed on 2026-08-01: the supplied `Cargo.toml`, `lib.rs`,
`DEPENDENCY-API.md`, `EVIDENCE.md`, and `TCB.md` for `quantifier-target` 0.1.0.
The dependency implementation, generated output, binary, and prior audit are
absent. The complete exported surface in `lib.rs` is the safe free function
`force_unreachable` and unsafe free function `delegated_nonzero`; there are no
exported fields, types, traits, impls, macros, statics, reexports, or
configuration-specific items in the submitted source.

Let

`D = {(Rust 1.80.0, t, p) | this exact source and peer-unsafe-dep 3.4.5 resolve
for target t, and p is an ordinary debug or ordinary release profile}`.

This is the request's controlling expression, retained symbolically: the
packet does not justify enumerating its target projection. `Cargo.toml` pins
`peer-unsafe-dep = "=3.4.5"`, and `DEPENDENCY-API.md` confirms that exact
resolution. The reviewed crate has no `cfg`, features, generated code, build
script, profile branch, target branch, or input-dependent control-flow branch.
Thus the local source arguments below are parametric over `t` and `p`.
Dependency-side variation is not available for inspection and is addressed as
trust, not silently excluded.

## Evidence and TCB

`AXIOM-UU-1.80` is accepted exactly as authorized by `TCB.md`. The opened Rust
1.80.0 standard-library Safety section states: “Reaching this function is
Undefined Behavior.” ([versioned source](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)).
The page identifies rustdoc 1.80.0 and gives no target- or profile-specific
qualification. It therefore covers all of `D` under the submitted evidence
policy.

There is no accepted `UNSAFE-DEP` proposition for `peer-unsafe-dep` 3.4.5;
`TCB.md` expressly declines that trust. The selected-safe-dependency exception
does not apply to correctness of a third-party **unsafe** API. No tool,
implementation, compatibility, or deployment premise is admitted.

## Claim 1 — `force_unreachable`: **UNSOUND**

**Exact claim.** For every configuration in `D`, every well-typed safe call to
`force_unreachable()` is free of Rust undefined behavior. Because the API is
safe, valid use has no caller-side safety precondition.

**Existential UB certificate (parametric over `D`).**

1. **Valid use:** in any `d in D`, safe code may call the public safe function
   `force_unreachable()` with no arguments (`lib.rs:4`).
2. **Reachability:** after entry, its sole, unconditional expression directly
   calls `std::hint::unreachable_unchecked()` (`lib.rs:6`). There is no guard,
   earlier divergence, callback, or alternate path.
3. **False required proposition:** the call site is therefore reached; the
   required proposition that it be unreachable is false.
4. **UB consequence:** `AXIOM-UU-1.80` says reaching that function is undefined
   behavior.

This supplies a valid in-scope UB execution for every member of `D`, so the
strongest soundness verdict is `UNSOUND`, not merely `UNPROVED`. The local
comment “This site is assumed to be unreachable” (`lib.rs:5`) is circular and
false for the witness; it supplies no derivation. No UB-free whole execution is
claimed as a postcondition witness.

**Required resolution:** remove the unsafe operation (for example, use a
defined diverging/panicking path), or expose and document a sufficient unsafe
caller obligation and re-audit the resulting new API. Changing the comment
alone cannot repair this safe API.

## Claim 2 — `delegated_nonzero`: **UNPROVED**

**Exact valid-use claim.** For every `d in D` and every `value: u8` with
`value != 0`, every execution of the unsafe call
`delegated_nonzero(value)` is free of Rust undefined behavior. The inequality
is the complete documented caller safety obligation (`lib.rs:11-14`); no
ongoing or terminal obligation is stated. The supplied peer contract also says
that, on return, `duplicate_nonzero(value)` returns `value`.

**Proved local portion (all of `D`).** The wrapper passes the unchanged
`value` directly to `peer_unsafe_dep::duplicate_nonzero` (`lib.rs:17`). For
every valid wrapper call, `value != 0`; this is exactly the dependency's
documented caller-side precondition. The adjacent safety comment correctly
proves this call-site obligation. There are no intervening transitions or
other local unsafe operations.

**Smallest missing propositions.** For the exact implementation selected as
`peer-unsafe-dep` 3.4.5, over every target/profile in `D`:

- for every `u8 v != 0`, every permitted execution of
  `duplicate_nonzero(v)` is free of undefined behavior; and
- on normal return, its result equals `v` (the submitted dependency
  postcondition).

The declaration and caller contract do not prove that an unavailable unsafe
implementation fulfills its promise. `DEPENDENCY-API.md` expressly supplies
no body-execution assertion, implementation artifact, generated output, or
prior audit, and the only possible implementation premise is rejected by the
TCB. Consequently the local precondition coverage is `D`, but aggregate
soundness/postcondition coverage cannot be established for any part of `D`.
`Required subset Covered` is therefore not certified.

No existential refutation is available either: the packet contains no fact
showing what the dependency body executes for any valid value. Thus `UNSOUND`
would be unjustified, and the strongest verdict is `UNPROVED`. The peer's
return-equals-input guarantee is likewise `UNPROVED`; it cannot be promoted
from documentation to an implementation fact for this unsafe dependency.

**Required resolution:** recursively audit the exact resolved 3.4.5
implementation (including relevant generated/configuration-dependent code) and
prove both propositions throughout `D`. Alternatively, an authorized reviewer
could accept a precise `UNSAFE-DEP` entry, but the governing trust decision for
this review expressly refuses that route.

## Closure and residual scope

For Claim 1, the witness proof is target/profile-parametric and the Rust axiom
covers `D`; no configuration is omitted. For Claim 2, every wrapper-owned
obligation is proved parametrically, while the dependency-implementation
obligation remains missing over the entire symbolic target/profile domain.
No builds, executions, tests, downloads, macro expansions, or dependency-source
claims contribute evidence. Re-audit on source/API changes, Rust-version or
support-domain changes, dependency identity/contract changes, or provision or
acceptance of dependency implementation evidence.
