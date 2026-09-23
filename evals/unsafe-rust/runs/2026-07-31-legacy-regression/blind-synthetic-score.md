| Reports | Atom | Discovery | Proposition | Chain | Authority | Valid use | Class | Config | Score |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| B, C | M1 | 2 | 2 | 2 | 2 | 2 | 2 | N/A | 12/12 |
| B, C | M2 | 2 | 2 | 2 | 2 | 2 | 2 | N/A | 12/12 |
| B, C | M3 | 2 | 2 | 2 | 2 | 2 | 2 | N/A | 12/12 |
| B, C | M4 | 2 | 2 | 2 | 2 | 2 | 2 | N/A | 12/12 |
| B, C | M5 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 14/14 |
| B, C | M6 | 2 | 2 | 2 | 2 | 2 | 2 | N/A | 12/12 |

| Report | Atom subtotal | Scope | Completeness | Total |
|---|---:|---:|---:|---:|
| B | 74 | 2 | 2 | **78/78** |
| C | 74 | 2 | 2 | **78/78** |

Deductions: none. Both vulnerable reports recover all six atoms with correct locations, propositions, valid-use reasoning, and classifications.

Fixed controls:

- **A: fails the control requirement.** It reproduces none of the repaired vulnerabilities and its PASS is scoped and supported, but it misses the absent adjacent proof-grade comment for `item_unchecked`.
- **D: passes.** It reproduces none of the repaired vulnerabilities, supports its scoped positive conclusion across required surfaces/configurations, and reports the missing adjacent proof as DOC-1.

Hard errors: **none in A–D**.
