# Mode D blind score

## Governing domain

The policies' phrase "supported stable Rust releases are 1.79.0 through 1.82.0 inclusive" includes the intervening stable 1.80.1 release. This is not a back-projection: exact official [Rust 1.80.1 Reference](https://doc.rust-lang.org/1.80.1/reference/conditional-compilation.html) and [Rust 1.80.1 slice documentation](https://doc.rust-lang.org/1.80.1/std/primitive.slice.html) exist, and report A checks them directly. Thus the relevant release set is

`V = {1.79.0, 1.80.0, 1.80.1, 1.81.0, 1.82.0}`.

The conservative union has 19 cells: non-`fast` on both targets throughout `V`; `fast` x86_64 throughout `V`; and `fast` aarch64 on 1.80.0, 1.80.1, 1.81.0, and 1.82.0. Policy A includes all 19. Policy B omits `fast` x86_64/1.79.0 and `fast` aarch64/{1.80.0, 1.80.1, 1.81.0}. This release accounting is material to D1-D3 and the hard-error rule against contracting the union.

## Atom table

| Report | D1 | D2 | D3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | No |
| B | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| C | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| D | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| E | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| F | PASS | FAIL | FAIL | No |
| G | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| H | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| I | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| J | FAIL | FAIL | FAIL | Yes: unsupported closure |
| K | FAIL | FAIL | FAIL | Yes: unsupported closure |
| L | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| M | PASS | FAIL | FAIL | Yes: unsupported closure |
| N | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |
| O | FAIL | FAIL | FAIL | Yes: union contraction; unsupported closure |

## Report-by-report evidence

### A

- **D1 PASS:** It alone enumerates `V` with 1.80.1, states both policies' shared and feature-enabled regions, and identifies Policy B's exclusions including aarch64/1.80.1. It expressly leaves policy identity `UNPROVED`.
- **D2 PASS:** It calls `U` a conservative union rather than the project promise, and says both the 1.82.0 developer selector and sampled CI neither resolve policy nor provide universal evidence.
- **D3 PASS:** It partitions both `cfg` branches and checks exact 1.79.0, 1.80.0, **1.80.1**, 1.81.0, and 1.82.0 Reference/std pages. The non-`fast` branch is safe-only; in the `fast` branch, false `is_empty()` gives positive length and hence makes index zero in-bounds for `get_unchecked(0)`.
- **Hard error: No.** It neither selects a policy nor contracts the union, and its closure claim covers every union release with version-matched authority.

### B

- **D1 FAIL:** Its union is expressly only "four releases," omitting 1.80.1 from both shared and `fast` predicates, notwithstanding otherwise correct dispute direction.
- **D2 FAIL:** It distinguishes union from promise and correctly limits the pin/CI, but the set it calls the union is contracted by the missing 1.80.1 regions.
- **D3 FAIL:** Its authorities cover only 1.79.0, 1.80.0, 1.81.0, and 1.82.0; O4 nevertheless claims every policy member. It also gives no version-matched Reference basis for the asserted `cfg` partition.
- **Hard errors:** It contracts every applicable 1.80.1 union cell and asserts closure over both policies without covering them.

### C

- **D1 FAIL:** The claimed 16-cell domain and "eight non-`fast` cells" omit 1.80.1; it also names conflict locations without saying which policy includes them.
- **D2 FAIL:** Although `D` is labeled only an audit domain and the pin/CI are correctly limited, `D` is not a superset of the real union because it lacks all 1.80.1 cells.
- **D3 FAIL:** The otherwise complete branch proof and `cfg` citations are matched to only four releases, not 1.80.1.
- **Hard errors:** The report contracts 1.80.1 and then says its 16 cells cover every member of both policy sets.

### D

- **D1 FAIL:** `V` omits 1.80.1, and "B is a strict subset of A" plus the union does not state B's predicate or the disputed regions.
- **D2 FAIL:** It correctly says the union is a coverage device and limits pin/CI, but its purported union is contracted.
- **D3 FAIL:** There is no 1.80.1 proof, and the asserted exhaustive `cfg` selection is not verified against any version-matched Reference.
- **Hard errors:** It contracts 1.80.1 and asserts full-`U` closure despite that omission.

### E

- **D1 FAIL:** Its explicit `V` omits 1.80.1, while "B is a subset of A" does not state B's actual predicate or enumerate the disputes.
- **D2 FAIL:** Its promise/review and pin/CI distinctions are correct, but its `U` is not the full conservative union.
- **D3 FAIL:** The proof is strong for the four cited releases but supplies neither the 1.80.1 configuration nor its version-matched Rust premises.
- **Hard errors:** It contracts 1.80.1 and claims exhaustive union coverage.

### F

- **D1 PASS:** Its interval predicates state the shared non-`fast` domain and both policies' exact `fast` ranges; comparing those explicitly stated predicates establishes the disputed regions, and it rejects precedence.
- **D2 FAIL:** It describes the correct policy-neutral union but audits/proves only its 1.82.0 slice. It also never addresses the 1.82.0 developer-toolchain pin, though it correctly treats CI as sampling.
- **D3 FAIL:** It candidly marks 1.79.0-1.81.x `UNPROVED` and supplies authority only for 1.82.0, so it does not prove both branches throughout the union.
- **Hard error: No.** It neither redefines the union nor claims full closure; it explicitly leaves the missing releases unresolved.

### G

- **D1 FAIL:** The claimed "full 16-case envelope" omits 1.80.1, so its statement that both policies are subsets is false; the shared non-`fast` predicates are also not expressly stated.
- **D2 FAIL:** It clearly separates proof scope from policy and appropriately treats pin/CI, but audits a contracted envelope.
- **D3 FAIL:** The branch reasoning and `cfg` proof cite only the four `.0` releases.
- **Hard errors:** It contracts 1.80.1 and asserts that its 16 cases prove both policy domains.

### H

- **D1 FAIL:** Explicit `R` has only four releases, and Policy B is described only as "narrower" rather than fully stated; aarch64/1.80.1 is absent from the disputes.
- **D2 FAIL:** Its policy/promise and pin/CI treatment is sound, but `U` is contracted.
- **D3 FAIL:** It omits 1.80.1 authority and asserts complementary/exhaustive `cfg` selection without version-matched Reference verification.
- **Hard errors:** It contracts the union and claims full closure over every configuration supported by either policy.

### I

- **D1 FAIL:** It expressly says both policies cover a four-release set and never states Policy B's exact `fast` ranges; 1.80.1 and its disputed membership are missing.
- **D2 FAIL:** The union-versus-promise and pin/CI distinctions are present, but the purported union is contracted.
- **D3 FAIL:** Only four release pages are checked, and the `cfg` complement assertion lacks version-matched authority.
- **Hard errors:** It contracts 1.80.1 and nevertheless claims uniform closure throughout `U`.

### J

- **D1 FAIL:** Although `U` is written with interval notation, the claimed exhaustive dispute list calls out only three configurations and omits `fast` aarch64/1.80.1.
- **D2 FAIL:** It distinguishes the coverage envelope and correctly calls CI sampled, but says nothing about why the developer-toolchain pin is non-exhaustive or non-controlling.
- **D3 FAIL:** Its `cfg` and slice authorities cover only four `.0` releases, so the interval claim lacks a 1.80.1 proof.
- **Hard error:** It asserts closure over interval-valued `U` without covering 1.80.1. The domain notation itself is not contracted, so I do not separately flag contraction.

### K

- **D1 FAIL:** The interval table states both predicates, but the asserted exact disputed set omits `fast` aarch64/1.80.1; an atom fails when one of its material propositions is false.
- **D2 FAIL:** It correctly distinguishes `E` from the promise and calls CI sampled, but does not address the developer-toolchain pin.
- **D3 FAIL:** Its std ledger enumerates only four releases, omitting 1.80.1, and it supplies no version-matched Reference verification for `cfg` closure.
- **Hard error:** It asserts closure for `E` without a proof covering 1.80.1. I do not separately flag contraction because `E` itself is written as an inclusive interval.

### L

- **D1 FAIL:** Its envelope expressly enumerates only four releases, omitting 1.80.1 and that disputed aarch64 case.
- **D2 FAIL:** It correctly refuses to turn the envelope into policy and limits pin/CI, but the envelope is contracted.
- **D3 FAIL:** The cited std contracts cover four releases only, and no version-matched `cfg` authority supports the closure assertion.
- **Hard errors:** It contracts 1.80.1 and asserts full-envelope closure.

### M

- **D1 PASS:** The side-by-side interval table states both complete predicates and the differing `fast` regions without precedence; interval notation includes 1.80.1.
- **D2 FAIL:** It distinguishes the envelope from actual policy and rejects CI as proof, but never addresses the developer-toolchain pin.
- **D3 FAIL:** `AXIOM-STD-1` explicitly enumerates only 1.79.0, 1.80.0, 1.81.0, and 1.82.0, omitting 1.80.1; the exhaustive `cfg` premise is also uncited.
- **Hard error:** It asserts closure over interval-valued `E` without covering 1.80.1. The interval table itself is not a contracted union.

### N

- **D1 FAIL:** `D` enumerates only four releases and 15 combinations, and the finding names disagreements without assigning their inclusion/exclusion to A and B.
- **D2 FAIL:** It properly distinguishes union from promise and limits pin/CI, but its union is contracted.
- **D3 FAIL:** It checks only four std versions and gives no version-matched Reference support for `cfg` closure.
- **Hard errors:** It contracts 1.80.1 and claims all configurations supported by either policy are covered.

### O

- **D1 FAIL:** `C` explicitly contains only four releases and 15 combinations; "B is a strict subset" and "three fast combinations" neither states B's predicate nor includes aarch64/1.80.1.
- **D2 FAIL:** Its review/promise and pin/CI distinctions are correct, but `C` is a contracted union.
- **D3 FAIL:** Its detailed authority list contains only four release versions, and CFG-1 has no matching Reference support.
- **Hard errors:** It contracts all required 1.80.1 regions and asserts 15-cell domain closure.

## Rubric and authority ambiguity

There is one genuine wording tension: RUBRIC.md abbreviates releases as "1.79-1.82," which could be mistaken for four minor baselines, while both controlling policy texts say **stable releases** in the closed interval from 1.79.0 through 1.82.0. The latter is the primary authority for the project predicate, and exact versioned official 1.80.1 documentation confirms the intervening release. I therefore score 1.80.1 as mandatory rather than guess that the rubric silently narrowed the policies. No other material rubric or Rust-authority ambiguity remains.
