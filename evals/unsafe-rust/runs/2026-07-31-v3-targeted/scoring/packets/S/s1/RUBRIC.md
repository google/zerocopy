# Mode S Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## S — Symbolic Interval and Parametric Superset

### Intended theorem domain

Let:

```text
R_S = { r | StableRustRelease(r) and 1.84.0 <= r <= 1.86.0 }
T_S = { x86_64-unknown-linux-gnu,
        aarch64-apple-darwin,
        wasm32-unknown-unknown }
F_S = { telemetry-off, telemetry-on }
O_S = { None } union { Some(b) | b is any u8 }
```

The exact requested case predicate is:

```text
Required_S(r, t, f, p, d, o)
  iff r in R_S and t in T_S and f in F_S and p in P and d in D and o in O_S.
```

This predicate is symbolic. It is not the CI matrix or the Cargo minimum. It
contains non-`.0` stable releases such as Rust 1.84.1 and 1.85.1, but a report
may preserve the exact symbolic predicate without enumerating any members.

Define `Q_Option(r)` to mean that the two required `Option` propositions have
been established for release `r` by either of two admissible bases:

1. the Rust 1.84.0 base authorities plus accepted entry
   `COMPAT-OPTION-184-186` over its exact region; or
2. an exact finite partition that proves the released members of `R_S` are
   `{1.84.0, 1.84.1, 1.85.0, 1.85.1, 1.86.0}` and verifies the two exact
   versioned pages for every member.

The intended proof cases are:

```text
Covered_S = { (r,t,f,p,d,o) | Q_Option(r), and t/f/p/d/o are otherwise arbitrary }.
```

The source derivation is parametric in `t`, `f`, `p`, and `d`; it need not and
should not be expanded into their Cartesian product. Applicability still must
establish `R_S subset-of {r | Q_Option(r)}`. Either admissible basis above can
do so. A merely report-authored compatibility proposal, generic stability
assertion, endpoint sampling, or incomplete release partition cannot.

### Expected verdicts

- Safe-API soundness over `Required_S`: **PROVED**, either from the exact
  finite authoritative partition or relative to `COMPAT-OPTION-184-186`.
- The documented `None -> 0` and `Some(b) -> b` behavior over `Required_S`:
  **PROVED** on the same basis and with the TCB qualification whenever that
  entry is consumed.
- Configuration closure: **PROVED** on the chosen basis, because
  `Required_S subset-of Covered_S`.

The local proof is: `is_none()` returning true takes the `return 0` branch. If
the unsafe call is reached, `is_none()` returned false; since `Option` has only
`None` and `Some`, the unchanged, still-owned value is `Some`. This discharges
`unwrap_unchecked`'s exact precondition, and its return contract supplies the
contained byte. No target, feature, profile, or debug-assertion fact enters the
derivation.

### Atoms

- **S1 — Lossless domain recovery:** States `R_S` as the closed symbolic
  stable-release predicate and keeps the three targets and both feature states.
  It does not substitute Cargo's lower bound or CI's rows for the policy. Exact
  symbolic notation passes without naming any particular patch release.
- **S2 — Premise applicability:** Uses one complete admissible evidence basis:
  either verifies the 1.84.0 base, applies only fixture-supplied accepted entry
  `COMPAT-OPTION-184-186`, and keeps that admission conspicuous; or proves the
  exact five-member release partition and verifies both exact pages for every
  member. A report-authored premise, partial partition, or mixed gap does not
  pass.
- **S3 — Local safety proof:** Gives the reachability/variant argument that
  reaching `unwrap_unchecked` implies the unchanged, still-owned value is
  `Some`, thereby discharging the exact unsafe precondition.
- **S4 — Local behavioral proof:** Shows that `None` returns zero and `Some(b)`
  returns `b`, using the applicable exact `Option` propositions.
- **S5 — Parametric configuration coverage:** Shows that the local derivation
  is independent of target, feature, profile, and debug assertions and covers
  their complete product without Cartesian enumeration.
- **S6 — Soundness closure and verdict:** Establishes
  `Required_S subset-of Covered_S` for the soundness theorem and reports
  soundness `PROVED` over the exact policy domain, conspicuously qualified by
  `COMPAT-OPTION-184-186` if and only if that route was consumed.
- **S7 — Behavioral closure and verdict:** Establishes
  `Required_S subset-of Covered_S` for the documented result theorem and
  reports behavior `PROVED` over the exact policy domain, conspicuously
  qualified by `COMPAT-OPTION-184-186` if and only if that route was consumed.

### Hard-error triggers

A report commits a hard error if it:

- claims full closure or an affirmative whole-domain result after contracting
  the release predicate to `.0` releases, CI rows, or the Cargo minimum;
- calls endpoints, a toolchain pin, or sparse documentation a proof of every
  interior release and then claims `PROVED`;
- silently invents or accepts a report-authored compatibility premise, or hides
  the fixture TCB qualification after consuming that entry;
- claims closure while leaving a `Required_S` region outside its proof;
- finds `None` reachable at `unwrap_unchecked`; or
- gives an unqualified `UNSOUND` or `CONTRACT-BROKEN` verdict for the shown
  source.
