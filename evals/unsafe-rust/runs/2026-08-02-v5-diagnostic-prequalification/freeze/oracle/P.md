# V5 Diagnostic Oracle — P: Predicates and Full-Case Proof

> **DRAFT / evaluator-only.** Never expose formulas, witnesses, verdicts, atom
> IDs, defect rules, or the authority inventory to a report agent.

## Scoring contract

This is the V4 P target with its authority-closure atom split into P27, P28,
and P29. Score the direct criteria in `../atoms/P.json`; use only closed IDs in
`../rules/defect-rules.json`. Equivalent predicates and any valid separating
witnesses pass. Do not collapse a disclosed upstream failure into each
dependent atom, and do not turn omission alone into a hard error.

## Exact policy predicates

Let:

```text
V = {1.84.0, 1.85.0, 1.86.0}
T = {X = x86_64-unknown-linux-gnu,
     A = aarch64-unknown-linux-gnu,
     W = wasm32-unknown-unknown}
f = turbo enabled
h = hardened enabled
```

The two published predicates are:

```text
Scarlet(v,t,f,h)
  iff v in V and t in T and
      (!f
       or (f and t = X and (!h or v >= 1.85.0))
       or (f and t = A and h)).

Indigo(v,t,f,h)
  iff v in V and t in T and
      (!f
       or (f and t = X and (h or v >= 1.86.0))
       or (f and t = A and !h and v >= 1.85.0)).
```

Neither contains the other. For example:

```text
(1.84.0, A, true, true) is Scarlet-only.
(1.84.0, X, true, true) is Indigo-only.
```

The supplied evidence contains no rule identifying either predicate, their
intersection, their union, or any other combination as the controlling exact
project promise. That identification is **UNRESOLVED** (or explicitly scoped
**UNPROVED**). Selecting a conservative audit set is a separate analyst act.

## Full-case domains

Let `P` be every supported Cargo profile, `D = {false,true}` the two
debug-assertion states, and `I` every valid `Option<u8>`. A full case is:

```text
(version, target, turbo, hardened, profile, debug_assertions, input).
```

```text
ScarletCases = {c | Scarlet(c.v,c.t,c.f,c.h)
                     and c.p in P and c.d in D and c.i in I}
IndigoCases  = {c | Indigo(c.v,c.t,c.f,c.h)
                     and c.p in P and c.d in D and c.i in I}
```

The canonical conservative choice is `Audit = ScarletCases union
IndigoCases`. Its configuration projection is equivalently:

```text
UnionCfg(v,t,f,h)
  iff v in V and t in T and
      (!f
       or (f and t = X)
       or (f and t = A and (h or v >= 1.85.0))).

Required(c)
  iff UnionCfg(c.v,c.t,c.f,c.h)
      and c.p in P and c.d in D and c.i in I.
```

The two containments must be proved separately. A transparent larger
full-case superset also passes if both containments and the resulting theorem
are proved, and it is not called the project's promise.

## Source proof and exact conclusions

Both policies exclude every `f=true, t=W` configuration, universally over the
remaining coordinates. Relative only to exact `BUILD-MAP-POLICY`, such a
requested build sets the turbo/wasm32 cfg. Rust's `all`, cfg-attribute, and
`compile_error!` rules then prove library-compilation failure on Rust 1.84.0,
1.85.0, and 1.86.0. Effective rejection is **PROVED relative to
BUILD-MAP-POLICY**.

For every compiled required case:

- without turbo, `value.unwrap_or(0)` contextually types `0` as `u8` and
  returns the byte for `Some(byte)` or zero for `None`;
- with turbo, the same expression first produces `r`; source constructs
  `Some(r)`, so `unwrap_unchecked` is never called on `None` and returns `r`.

One exact coverage predicate usable for both separate obligations is:

```text
Covered(c)
  iff c.v in V and c.t in T and c.f in {false,true}
      and c.h in {false,true} and c.p in P and c.d in D and c.i in I
      and (!c.f or (c.f and c.t in {X,A})).
```

The unsafe-precondition proof and the documented-return proof remain distinct.
Every disjunct of `UnionCfg` implies the final source clause, while every
profile/debug/input fiber is preserved. Therefore:

```text
Required subset-of Covered_sound
Required subset-of Covered_behavior
```

Safe-API soundness and the documented `value_or_zero` postcondition on the
chosen conservative audit domain are each **PROVED relative to exact
BUILD-MAP-POLICY**.

## P27 / P28 / P29 split

- **P27 inventory completeness:** every consumed Rust semantic premise has an
  entry with every exact release URL, narrow quotation, proposition,
  applicability, and consumer. This includes contextual type/value of the
  unsuffixed zero, both Option methods, cfg/all/not/retention, and
  `compile_error!`.
- **P28 entailment correctness:** each quotation actually entails its stated
  proposition in the direction and domain used on all three releases. Page
  identity or a nearby sentence is insufficient.
- **P29 authority/TCB reconciliation:** `BUILD-MAP-POLICY` is limited to its
  exact tool identities, feature/target mappings, consumers, releases, and
  profiles; every dependent conclusion is conspicuously TCB-relative. It is
  not Rust authority and supplies no source correctness.

The closed mode hard errors are exactly `PH1`–`PH7`; common `GH*` and `GD*`
rules apply independently.
