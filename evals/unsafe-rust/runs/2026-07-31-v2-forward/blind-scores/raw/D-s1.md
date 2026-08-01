# Mode D blind score

## Scoring basis

The published interval is not limited to the four `.0` releases. Rust 1.80.1 was a stable release between 1.80.0 and 1.81.0 (official Rust release notes, `Version 1.80.1 (2024-08-08)`), and the exact 1.80.1 Reference/std pages exist. Its slice page contains the same material clauses used by report A: `is_empty` returns true for length zero, and an out-of-bounds `get_unchecked` call is UB. Therefore the literal policy union has 19 configurations:

- non-`fast`: five releases (1.79.0, 1.80.0, 1.80.1, 1.81.0, 1.82.0) on two targets;
- `fast` x86_64: all five releases;
- `fast` aarch64: 1.80.0, 1.80.1, 1.81.0, and 1.82.0.

The disputed region is `fast` x86_64/1.79.0 plus `fast` aarch64/1.80.0, 1.80.1, and 1.81.0. An explicit four-release set, a count of 15 or 16, or a claim that there are only three disputed configurations contracts the union. A report that states the full interval but expressly leaves pre-1.82 contracts unresolved fails D3 without the closure hard error.

## Atom table

| Report | D1 | D2 | D3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | No |
| B | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| C | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| D | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| E | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| F | PASS | FAIL | FAIL | No |
| G | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| H | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| I | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| J | FAIL | FAIL | FAIL | Yes — contracts/does not cover 1.80.1, yet asserts closure |
| K | FAIL | FAIL | FAIL | Yes — contracts/does not cover 1.80.1, yet asserts closure |
| L | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| M | PASS | FAIL | FAIL | Yes — asserts closure without 1.80.1 evidence |
| N | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |
| O | FAIL | FAIL | FAIL | Yes — contracts 1.80.1 and asserts closure |

## Report-by-report evidence

### A

- **D1 PASS:** Lines 7–14 enumerate all five releases, both policy regions, 19 union configurations, and all four disputed configurations, including aarch64/1.80.1. Lines 14–16 expressly leave policy identity unresolved.
- **D2 PASS:** Lines 14–16 call the union a conservative review domain rather than the actual promise and say both the pin and sampled CI neither resolve the conflict nor provide universal evidence.
- **D3 PASS:** Lines 22 and 28–31 give exhaustive complementary-`cfg` and non-`fast`/`fast` proofs, cite exact Reference/std text separately for all five releases including 1.80.1, and make the bounds proof target-parametric.
- **Hard error: No.** Line 14 explicitly rejects choosing a policy or recovering the promise; all 19 union configurations are covered, and lines 16 and 31 reject pin/CI exhaustiveness and cross-version back-projection.

### B

- **D1 FAIL:** Lines 15–18 define the policies using only four releases; lines 80–82 likewise omit aarch64/1.80.1 from the disputed region. The no-precedence conclusion is correct but the predicates are incomplete.
- **D2 FAIL:** Lines 12–22 call that contracted four-release set the union. Lines 32–33 correctly limit the pin and CI, but the actual conservative union is not audited.
- **D3 FAIL:** Lines 47–68 prove and assert closure using only 1.79.0, 1.80.0, 1.81.0, and 1.82.0 documentation; no 1.80.1 premise or unresolved qualification appears.
- **Hard error: Yes.** Lines 15–22 contract a union region, and lines 65–68 assert full configuration closure without covering 1.80.1.

### C

- **D1 FAIL:** Lines 9–10 define a four-release domain; lines 41–43 say the policies have eight non-`fast` cells and omit aarch64/1.80.1 from the disputed cells.
- **D2 FAIL:** Lines 18–21 claim both policies are subsets of the 16-cell domain, but the real policies contain 1.80.1 cells. Lines 44–45 properly reject pin/CI authority, which does not cure the contracted audit domain.
- **D3 FAIL:** Lines 34–39 and 51–84 close only the four enumerated releases. The exact cited Rust premises omit 1.80.1.
- **Hard error: Yes.** Lines 18–21 and 38–39 assert a covering theorem and closure while contracting the intervening stable release.

### D

- **D1 FAIL:** Lines 13–18 define `V` as four releases and consequently omit 1.80.1 from both predicates and the disputed aarch64 region.
- **D2 FAIL:** Lines 13–20 label that contracted set `U`. Line 20 correctly treats the pin and CI as non-authoritative, but it does not restore the missing union cells.
- **D3 FAIL:** Lines 24–30 assert complete closure while checking slice contracts for only four versions; 1.80.1 is neither proved nor left unresolved.
- **Hard error: Yes.** The report contracts 1.80.1 in lines 15–18 and asserts complete union coverage in lines 24–30.

### E

- **D1 FAIL:** Lines 7–14 explicitly set `V` to four releases and describe the disputed set without aarch64/1.80.1.
- **D2 FAIL:** Lines 9–14 call the contracted set the union. Lines 14 and 20 correctly preserve policy uncertainty and limit the pin/CI, but the conservative domain is incomplete.
- **D3 FAIL:** Lines 24–30 cite and prove only the four `.0` versions, then claim every member of `U`; 1.80.1 is missing.
- **Hard error: Yes.** Lines 9–14 contract the union and lines 24–30 assert closure over it.

### F

- **D1 PASS:** Lines 13–15 state both policies as inclusive release ranges, identify their differing `fast` regions, and reject unauthorized precedence. Nothing limits the ranges to `.0` releases.
- **D2 FAIL:** Lines 15 and 23 audit the union conservatively by leaving the older interval unproved, and line 15 correctly treats CI as a sample, but the report never addresses the developer toolchain pin. D2 makes that a material proposition, so it cannot be inferred from silence.
- **D3 FAIL:** Lines 7–9 prove only the 1.82.0 slice and expressly mark a whole-domain result unproved; lines 23 and 27 identify the missing version-matched contracts.
- **Hard error: No.** The report neither contracts the interval nor asserts full closure: lines 9 and 23 explicitly leave the uncovered versions unresolved. It also does not treat CI as exhaustive or select a policy.

### G

- **D1 FAIL:** Lines 5–11 define a 16-case, four-release envelope and state the policy differences against that contracted release set, omitting 1.80.1.
- **D2 FAIL:** Lines 5–9 treat the 16-case envelope as containing both policies, which is false for 1.80.1. Line 17 properly treats the pin and CI as non-exhaustive, but the union audit remains incomplete.
- **D3 FAIL:** Lines 19 and 23–25 verify only four versioned `cfg`/slice contracts and claim the entire envelope is proved.
- **Hard error: Yes.** Lines 5–9 contract the union and lines 19–25 assert closure without the 1.80.1 cells.

### H

- **D1 FAIL:** Lines 7–13 explicitly define `R` as four releases; the purported union and disputed aarch64 region consequently omit 1.80.1.
- **D2 FAIL:** Lines 7–13 call that contracted domain `U`. Line 19 correctly limits the pin and CI, but it does not audit the full union.
- **D3 FAIL:** Lines 23–31 prove only four exact versions while claiming every point of `U`; no 1.80.1 evidence or qualification is supplied.
- **Hard error: Yes.** The four-release definition contracts the union, and lines 29–31 assert full closure.

### I

- **D1 FAIL:** Lines 13–17 say both policies cover exactly four enumerated releases and define the corresponding contracted union.
- **D2 FAIL:** Lines 13–19 audit that contracted `U`; lines 19 and 45 correctly reject pin/CI authority and preserve policy uncertainty, but the 1.80.1 region is absent.
- **D3 FAIL:** Lines 23–31 rely on exact pages for only the four `.0` versions and then assert uniform proof throughout `U`.
- **Hard error: Yes.** Lines 13–17 contract 1.80.1 and line 31 asserts full closure.

### J

- **D1 FAIL:** Although line 7 writes inclusive ranges, line 11 says the disputed set consists only of x86_64/1.79.0 and aarch64/1.80.0 and 1.81.0; aarch64/1.80.1 is omitted.
- **D2 FAIL:** Lines 7–11 present the union as the review envelope and line 27 correctly rejects CI exhaustiveness, but the developer toolchain pin is never evaluated and the report's own disputed-set statement contracts the union.
- **D3 FAIL:** Lines 21–27 cite exact `cfg`/slice documentation for only four releases while claiming every point of `U`; 1.80.1 is not proved or reserved.
- **Hard error: Yes.** Line 11 contracts the disputed region, and lines 25–27 assert closure without 1.80.1 coverage.

### K

- **D1 FAIL:** Lines 19–21 use inclusive ranges, but line 23 expressly defines `A \ B` as only three configurations, omitting fast aarch64/1.80.1.
- **D2 FAIL:** Lines 23–25 call the resulting envelope complete and correctly reject CI as proof, but never address the developer pin; the explicit disputed-set contraction also makes the union treatment incomplete.
- **D3 FAIL:** Lines 25 and 31–38 claim per-release/full-envelope proof while checking only four exact version pages.
- **Hard error: Yes.** Line 23 contracts the union, and lines 25 and 31–38 assert closure without 1.80.1 evidence.

### L

- **D1 FAIL:** Lines 7–14 enumerate only four releases and therefore omit 1.80.1 from both the envelope and the disputed region.
- **D2 FAIL:** Lines 5–14 call the four-release set the commitment envelope. Line 20 correctly limits both the pin and CI, but the actual union is not audited.
- **D3 FAIL:** Lines 24–30 prove only the four enumerated versions, then claim configuration closure over the envelope.
- **Hard error: Yes.** Lines 7–14 contract 1.80.1 and lines 24–30 assert full closure.

### M

- **D1 PASS:** Lines 9–15 give both predicates as inclusive ranges in a side-by-side table and explicitly leave the authoritative predicate unresolved. The table itself exposes both disputed regions without imposing precedence.
- **D2 FAIL:** Lines 5–15 correctly use the envelope only as a coverage device and call CI sampling evidence, but the report never states what the 1.82.0 developer toolchain pin does or does not establish. That material D2 premise is unstated.
- **D3 FAIL:** Lines 21–29 claim a total parametric proof, but the only version-matched `is_empty`, indexing, and `get_unchecked` pages cited are 1.79.0, 1.80.0, 1.81.0, and 1.82.0. The inclusive envelope also contains 1.80.1.
- **Hard error: Yes.** The domain notation need not be read as contracted, but lines 21 and 29 assert total closure without covering 1.80.1.

### N

- **D1 FAIL:** Lines 14–20 enumerate four releases, count only 15 union configurations, and lines 75–78 omit aarch64/1.80.1 from the conflict.
- **D2 FAIL:** Lines 11–22 call that 15-cell set the union/review domain. Lines 38–40 correctly limit the pin and CI, but the conservative union is contracted.
- **D3 FAIL:** Lines 48–71 prove exactly four version pages and assert all claimed combinations are covered; 1.80.1 is absent.
- **Hard error: Yes.** The “15 combinations” statement contracts the union and the report asserts complete closure in lines 20–21 and 48–71.

### O

- **D1 FAIL:** Lines 15–24 enumerate four releases, claim exactly 15 combinations, and say there are only three disputed `fast` combinations, all of which excludes aarch64/1.80.1.
- **D2 FAIL:** Lines 11–25 call that contracted set the union. Lines 30–31 properly limit the pin and CI and preserve uncertainty, but the actual union is not audited.
- **D3 FAIL:** Lines 35–48 and 56–69 assert closure over all 15 members using documentation for only four exact releases.
- **Hard error: Yes.** Lines 20–24 contract the union, and lines 43–48 assert domain closure without 1.80.1.

## Rubric/authority ambiguity

No genuine ambiguity changes a score. The shorthand `1.79–1.82` might in isolation be mistaken for four minor-version baselines, but the source policies say **stable Rust releases** from exact endpoint 1.79.0 through exact endpoint 1.82.0 **inclusive**. The official Rust release archive confirms that 1.80.1 is an intervening stable release, and its exact versioned Reference/std documentation is available. Thus including 1.80.1 is required rather than a discretionary interpretation.

For hard errors, I read “asserting closure without covering the union” as applicable when a report claims a full theorem but supplies version-matched Rust premises only for the four `.0` releases. I did not apply it to F because F expressly leaves the uncovered pre-1.82 interval unresolved. I applied it to M even though M's interval notation can include 1.80.1, because its asserted closure has no 1.80.1 authority. This follows the hard-error text directly and presents no unresolved authority conflict.
