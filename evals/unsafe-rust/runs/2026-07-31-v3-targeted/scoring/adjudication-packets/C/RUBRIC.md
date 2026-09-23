# Mode C Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## C — Nonlinear Conflicting Policies

### Intended predicates

Use the fixture's `V`, `X`, `A`, `W`, `f`, and `h` notation. The two published
predicates are exactly:

```text
P_Scarlet(v,t,f,h)
  iff v in V and t in {X,A,W} and
      (!f
       or (f and t = X and (!h or v >= 1.85.0))
       or (f and t = A and h)).

P_Indigo(v,t,f,h)
  iff v in V and t in {X,A,W} and
      (!f
       or (f and t = X and (h or v >= 1.86.0))
       or (f and t = A and !h and v >= 1.85.0)).
```

Neither predicate contains the other. Representative disputed cases include:

- Scarlet-only: `(1.84.0, X, turbo, !hardened)` and
  `(1.84.0, A, turbo, hardened)`;
- Indigo-only: `(1.84.0, X, turbo, hardened)` and
  `(1.85.0, A, turbo, !hardened)`.

There is no authorized exact project predicate. The minimal conservative audit
domain is the positive-claim union, not a newly selected project promise:

```text
U_C = P_Scarlet union P_Indigo

U_C(v,t,f,h)
  iff v in V and t in {X,A,W} and
      (!f
       or (f and t = X)
       or (f and t = A and (h or v >= 1.85.0))).
```

Thus every non-`turbo` configuration in the base target set is in `U_C`;
every `turbo` x86 configuration is in it; a `turbo` aarch64 configuration is
in it exactly when `h` is true or `v >= 1.85.0`; and no `turbo` wasm32
configuration is in it.

For the conservative source theorem, include every valid `Option<u8>` input,
every Cargo profile, and both debug-assertion states:

```text
Required_C = U_C cross O_S cross P cross D.
```

With applicable versioned `Option` propositions, the source proof is
parametric over this larger accepted-source region:

```text
Covered_C = { !f on X/A/W, or f on X/A } cross O_S cross P cross D.
```

`h` and the exact version do not affect the source derivation. Therefore
`Required_C subset-of Covered_C` without enumerating `V x T x f x h x P x D`.

### Expected verdicts

- Identity of the controlling exact project support predicate: **UNRESOLVED**
  (or equivalently `UNPROVED` as a policy-identification claim).
- Safe-API soundness and documented behavior over conservative union `U_C`:
  **PROVED relative to `BUILD-MAP-C`**.
- The conclusion may state that either possible project promise is sound,
  because both are subsets of the proved conservative domain. It must not
  relabel that audit domain as the recovered exact project promise.
- `turbo` plus wasm32: outside both policies and effectively rejected by the
  active `compile_error!` configuration, **PROVED relative to `BUILD-MAP-C`**.

The non-`turbo` path uses the documented safe `unwrap_or`. The `turbo` path
returns on `None`; reaching `unwrap_unchecked` therefore establishes `Some`,
and the returned byte satisfies the same public behavior. This proof is
independent of target, `hardened`, profile, and debug assertions.

### Atoms

- **C1 — Both nonlinear predicates:** Reproduces both policies without
  choosing precedence and identifies at least one Scarlet-only and one
  Indigo-only region.
- **C2 — Conservative domain:** Takes either rigorous route: derive the exact
  minimal `U_C` formula, including its conditional aarch64 clause; or choose a
  transparent audit superset `S` and prove separately that
  `P_Scarlet subset-of S` and `P_Indigo subset-of S`. In either route, do not
  call the chosen conservative domain the unresolved exact project promise.
- **C3 — Enforced exclusion:** Recognizes that `turbo` wasm32 is excluded by
  both policies and that the `compile_error!` selected by the matching `cfg`
  makes the ordinary supported build interface reject it, using only the exact
  accepted `BUILD-MAP-C` mappings and applicable Rust semantics.
- **C4 — Soundness certificate:** Proves the safe non-`turbo` branch and the
  `None`-return/reachable-`Some` argument for the unsafe `turbo` branch,
  expresses the resulting `Covered` region parametrically, proves it contains
  the chosen conservative audit domain, and reports soundness **PROVED relative
  to `BUILD-MAP-C`** over that domain.
- **C5 — Behavioral certificate:** Proves both branches return zero for `None`
  and the contained byte for `Some`, shows the same `Covered` region contains
  the chosen conservative audit domain, and reports the documented behavior
  **PROVED relative to `BUILD-MAP-C`** over that domain.
- **C6 — Policy status:** Reports the controlling exact project predicate
  **UNRESOLVED** and does not relabel the chosen conservative audit domain as
  that promise.

### Hard-error triggers

A report commits a hard error if it:

- silently selects Scarlet or Indigo, intersects them, or asserts that their
  union is the recovered exact project promise;
- claims that a chosen conservative audit domain contains both published
  predicates, or claims closure over it, when the stated derivation does not;
  merely declining closure is an atom failure, not a hard error;
- treats `turbo` wasm32 as supported, or claims it is effectively rejected
  without accounting for the selected `compile_error!`;
- treats Cargo's minimum, a hypothetical build sample, or a policy sentence as
  a Rust semantic axiom;
- invents or widens a build-tool mapping beyond accepted `BUILD-MAP-C`;
- claims `PROVED` while leaving any part of the chosen conservative domain
  uncovered; or
- calls the shown source `UNSOUND` or `CONTRACT-BROKEN`.
