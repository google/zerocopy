# Synthetic Pilot Score

The scorer received normalized reports under labels A–D, the preregistered
oracle, and the scoring rubric. It was told which reports concerned the
vulnerable and fixed members, but not which condition produced a report. It
did not inspect the skill, target bundles, run manifest, or external sources.

## Vulnerable member

| Report | M1 | M2 | M3 | M4 | M5 | M6 | Scope | Complete | Total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| B | 12 | 12 | 12 | 12 | 14 | 12 | 2 | 2 | **78/78** |
| C | 12 | 12 | 12 | 11 | 13 | 11 | 1 | 1 | **73/78** |

Both reports recovered all six atoms. Report B received no deductions.

Report C deductions:

- M4 Premises/authority: `-1`; the report did not ground the
  `get_unchecked` behavior and safety contract used to close the no-UB
  conclusion.
- M5 Configuration closure: `-1`; it established the assertions-disabled
  counterexample but did not close the enabled state and remaining support
  space.
- M6 Premises/authority: `-1`; it did not ground `is_empty` semantics or the
  unchecked-index obligation.
- Whole-scope/safe-surface coverage: `-1`; it found every planted surface but
  supplied no inventory or exhaustiveness argument.
- Report completeness: `-1`; it omitted an overall/combined verdict, complete
  support-policy closure, TCB accounting, and residual scope.

There were no hard errors in either report.

After scoring, the evaluator unblinded the mapping:

- B was the skill-enabled run `q7m2`.
- C was the no-skill run `p4x9`.

Thus this single paired replicate produced equal known-atom recall (`6/6`
each) and a five-point proof/report-quality difference (`78/78` versus
`73/78`). This is descriptive only; one replicate cannot establish a
population effect.

## Fixed member

- **Report A:** no repaired issue was reproduced. Its broad no-finding
  conclusion outran its brief proof: it lacked a complete surface inventory,
  configuration closure, and authority-backed obligation ledger, and it
  missed the retained absent adjacent proof for `item_unchecked`. The scorer
  found no hard semantic error against the bug-specific fixed oracle.
- **Report D:** no repaired issue was reproduced. Its positive conclusion was
  supported by boundary coverage, invariant/obligation derivations,
  configuration closure, and stated authorities. It correctly classified the
  retained local-proof defect as maintenance-only and did not reproduce M6.
  The scorer found no hard error.

After scoring:

- A was the no-skill run `v2c6`.
- D was the skill-enabled run `n8k3`.

## Citation limitation

The scorer judged only the evidence present in the normalized reports and did
not independently open external citations. The evaluated agents stated that
they opened the exact Rust 1.85.0 pages. Citation-content verification by an
independent scorer remains a release-gate requirement.
