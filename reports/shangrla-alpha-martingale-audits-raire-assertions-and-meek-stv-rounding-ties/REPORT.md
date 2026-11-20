# Risk-limiting audit tests (SHANGRLA, ALPHA, Arlo), reproducible ballot sampling, RAIRE assertions for IRV, and STV rounding and tie rules (rcv, ConcreteSTV), with certificate-checked counting

## Summary

- **SHANGRLA's test layer is calibrated, except for `wald_sprt`.** SHANGRLA reduces every supported outcome to assertions "assorter mean > 1/2" and tests each with a `NonnegMean` supermartingale. The p-value is `min(1, 1/max_j M_j)`, and an assertion is proved once p ≤ the risk limit, after which it stays proved. At the pin, `alpha_mart` and `betting_mart` rejected a true null at no more than the nominal rate on synthetic data. `wald_sprt` applies `np.cumprod` twice (`NonnegMean.py:790-794`) and rejected about 52% of true nulls at α = 0.05. It is not the default test.
- **Stratified audits are not implemented in SHANGRLA core** (`Audit.py:1162-1164`). Arlo provides SUITE's two-stratum Fisher combination (`suite.py`).
- **Sample reproducibility rests on different mechanisms.** Arlo's ticket is a SHA-256 of `hex(SHA-256(seed)) + str(id)`, independent of manifest order. It can be recomputed with `hashlib` alone, but `id` is a Python tuple and its `repr` is what gets hashed. SHANGRLA gives the k-th CVR the k-th output of `SHA256(str(seed) + "," + "\0"*k)`, so its sample depends on CVR list order. SHANGRLA's `CVR.consistent_sampling` duplicates already-sampled cards when resumed (shown by execution).
- **Arlo's Python RAIRE port returns incomplete assertion sets.** On 3 of the 5 example inputs bundled with raire-rs, the sets it returns leave some alternative winners not ruled out. In the guide example, they leave alternative winners Diego and Alice possible. The cause: `raire.py:186-187` always defers a leaf to its best ancestor, even when that ancestor's difficulty is ∞. Adding SHANGRLA's leaf-versus-ancestor comparison (4 lines) makes the output equal to raire-rs on all 5 examples. No caller in `server/api` reaches this function at the pin.
- **STV precision and tie rules can change who is elected.** ConcreteSTV's integer-tally ACT rules (`ACTPre2020`) and 6-decimal rules (`ACT2021`) elected different candidates on a 91-ballot synthetic profile, because truncating 0.104 of a vote created a countback tie. rcv's "previous round counts, then random" fallback draws from a list built by iterating a `HashSet`. Its documentation describes an alphabetically sorted list.
- **Certificate checking covers the count, not the ballots.** HOL4/CakeML checkers (ACT, Victoria, union and CADE variants) and Coq-synthesised counters certify the count *given the certified ballots*. Showing that those ballots match the paper remains the RLA's job.

## Applicability

The subjects are the Git revisions and the wheel listed in `REPORT.json`, examined on 2026-11-20:

- SHANGRLA (`shangrla/core`, `shangrla/raire`).
- Arlo (`server/audit_math`, `server/api/shared.py`).
- consistent_sampler at the revision Arlo pins (`pyproject.toml:64`).
- The cryptorandom 0.4 wheel.
- rcv (RCTab).
- ConcreteSTV.
- raire-rs.
- Three verified-counting repositories.

The report compares independent implementations of the same concepts: RLA tests and samplers (SHANGRLA vs Arlo), RAIRE (raire-rs vs the SHANGRLA and Arlo Python ports), and tabulation (rcv vs ConcreteSTV). SHANGRLA consumes RAIRE JSON through `Assertion.make_assertions_from_json`.

Execution ran on one x86-64 Linux host with Python 3.13.15, numpy 2.5.4, scipy 1.18.1, release builds from rustc 1.102.0-nightly, and OpenJDK 27.0.1. SHANGRLA and consistent_sampler were installed from the pinned tarballs, and Arlo's `audit_math` was imported in place. All ballots and populations are synthetic, or are the example inputs bundled with raire-rs. The resulting rates are properties of those inputs, not of real elections, and no defect below was observed in a real audit. The behaviours are tied to the pins; the Revalidation section gives cheap checks for later revisions.

## Findings

### 1. Assorters, assertions and sequential tests in SHANGRLA

Basis: source + execution (P2). Every assertion's null is that the assorter mean is ≤ 1/2.

| Assertion | Assorter on card *c* | *u* | Source (`Audit.py`) |
|---|---|---|---|
| Plurality *w* vs *l* | `(vote(w) − vote(l) + 1)/2` | 1 | `1979-2051` (`2042`) |
| Supermajority share *f* | `vote(w)/(2f)` if the card has one valid vote, else `1/2` | `1/(2f)` | `2054-2141` (`2130-2134`) |
| RAIRE `WINNER_ONLY` (NEB) | `(1[first pref = w] − 1[l ranked, and w unranked or below l] + 1)/2` | 1 | `2183-2219`, `rcv_lfunc_wo` `340-367` |
| RAIRE `IRV_ELIMINATION` (NEN) | `(votefor(w; remaining) − votefor(l; remaining) + 1)/2` | 1 | `2220-2252`, `rcv_votefor_cand` `369-402` |
| Card-level comparison | `(1 − ω/u)/(2 − v/u)`, with ω = A(cvr) − A(mvr) and v = 2·mean − 1 | `2/(2 − v/u)` | `1551-1583`, `1620`, `1758` |

Phantom handling (`Assorter.overstatement`, `2692-2740`): a phantom CVR scores 1/2, `int(cvr.phantom) / 2 + (1 - int(cvr.phantom)) * self.assort(cvr)`. A phantom MVR scores 0, and so does an MVR that lacks the contest when `use_style` is set.

`sjm` (`NonnegMean.py:142-176`) gives the population mean still remaining under the null: `m_j = (N·t − S_{j−1})/(N − j + 1)` for finite N, or `t` when `N = np.inf`. N therefore selects sampling with or without replacement.

| Test | Term | N = ∞ | Status |
|---|---|---|---|
| `alpha_mart` (`90-140`) | `(x η/m + (u−x)(u−η)/(u−m))/u` (`129`); p = `min(1, 1/max M)` | yes | calibrated (P2) |
| `betting_mart` (`178-242`) | `1 + λ(x − m)` (`225`) | yes | calibrated with `agrapa` (P2) |
| `kaplan_kolmogorov` (`599-647`) | `(x + g)/m` | **no**: `assert N == int(N)` (`640`) raises `OverflowError`, although the class docstring promises "with and without replacement" | defect (execution) |
| `wald_sprt` (`734-797`) | generalized SPRT | yes | **invalid** (see below) |

Estimators: `fixed_alternative_mean` (`289-322`), `shrink_trunc` (`324-388`; shrinks towards η with d = 100 and truncates by `c/√(d+j−1)`), `optimal_comparison` (`390-420`) and `agrapa` (`497-561`). `best_fixed_bet` (`471-494`) is a stub that returns `lam`. The constructor's default η is `t + (u−t)/2` (`68-70`), whereas the docstrings say `u*(1-eps)`.

**`wald_sprt` defect.** The pinned code (`NonnegMean.py:790-794`):

```python
            terms = np.cumprod(
                (x * etas / m + (u - x) * (u - etas) / (u - m)) / u
            )  # generalization of Bernoulli SPRT
        terms[m < 0] = np.inf  # the null is surely false
        terms = np.cumprod(terms)
```

- P2 computed the independent martingale for x = [1,1,0,1,1], η = 0.6: `[1.2, 1.44, 1.152, 1.3824, 1.6589]`. `wald_sprt` returned `1/p_history = [1.2, 1.728, 1.9907, 2.7519, 4.565]`, exactly `cumprod(M_j)`.
- Null-rejection rates (mean exactly 1/2, at most 500 draws, 2000 replications, α = 0.05):

  | Test | Without replacement (N = 2000) | With replacement |
  |---|---|---|
  | `wald_sprt` | 0.5155 | 0.527 |
  | `alpha_mart`, fixed η | 0.036 | 0.029 |
  | `alpha_mart`, `shrink_trunc` | 0.0245 | 0.0265 |
  | `betting_mart`, `agrapa` | 0.033 | 0.022 |
  | independently coded BRAVO | 0.0155 | 0.029 |

- `tests/core/test_NonnegMean.py` tests neither `wald_sprt` nor `kaplan_kolmogorov`.

**Stopping times under an alternative.** Toy population: N = 10 000, winner share 0.55, 300 replications. Median (90th percentile) draws to stop:

| Test | Median (p90) |
|---|---|
| `alpha_mart`, fixed η | 442 (1062) |
| Independent BRAVO | 466 (1157) |
| `shrink_trunc` | 529 (1229) |
| `agrapa` (defaults) | 1335 (2717) |

Basis: execution (SHANGRLA functions on toy data). These numbers rank the tests on this one population only.

**Stopping rule.** `asn.proved = (asn.p_value <= con.risk_limit) or asn.proved` (`Audit.py:2429`). Sample-size simulation uses `np.random.RandomState(seed)` (`NonnegMean.py:843`); the real sample uses cryptorandom.

**Further defects confirmed by execution:**

- **`Assorter(require_validation=True).assort(cvr)` returns a function.** The inner lambda is the value of the conditional expression (`Audit.py:2542-2548`):

  ```python
          self.assort = (lambda cvr: assort_fn(cvr) #
                         if not self.require_validation
                         else
                         (lambda cvr: assort_fn(cvr)
                          if cvr.contest_validated(self.contest.id, raise_exception=True)
                          else np.nan
                         ))
  ```

- **`make_supermajority_assertion` ignores its `share_to_win` parameter** (`:2057`). It uses `u=1 / (2 * contest.share_to_win)` (`:2116`, `:2134`). Passing 2/3 with `contest.share_to_win = 0.5` gave an upper bound of 1.0.
- **An unknown JSON assertion type raises `TypeError`.** The code says `raise NotImplemented(` (`:2254`), and `NotImplemented` is not callable.

### 2. Arlo audit mathematics: stopping conventions

Basis: source.

| Method | Statistic | Stops when | Lines |
|---|---|---|---|
| BRAVO | `T = Π (s_wl/0.5)^{v_w}((1−s_wl)/0.5)^{v_l}` over cumulative round totals (`Decimal` built from floats, `:158`) | every pair has 1/T ≤ α (`if raw > alpha: finished = False`), or a full hand count | `bravo.py:115-167`, `:484-537` |
| MINERVA / Providence | delegated to the `athena` / `r2b2` libraries (git-pinned, `pyproject.toml:63,65`) | `all(risk <= alpha ...)` (`minerva.py:254`) | not examined further |
| SuperSimple | `p = Π ((1 − 1/U)/(1 − e_r·V/(2γ)))^{times_sampled}` with `U = 2γ/margin` and `γ = Decimal(1.03905)` (`:10`); understatements clipped to 0 (`:355`) | `0 < p < alpha`, **strict** (`:375`) | `supersimple.py:284-378` |
| SUITE (hybrid) | Fisher combination maximised over a grid; raises `ValueError` if either stratum has been fully counted | `max_p <= alpha` (`:751`) | `suite.py:274`, `:692-751` |

- Sampled ballots that cannot be found count as votes for every loser (`ballot_polling.py:36-40`, `:65-68`).
- Arlo evaluates risk at round boundaries from cumulative tallies; SHANGRLA keeps a sequential p-value history.
- The boundary differs between methods (`<` vs `≤`), so identical p-values can stop under one method and not another.

### 3. Reproducible sample selection

Basis: source + execution (P1).

| Property | SHANGRLA (`assign_sample_nums` + `consistent_sampling`) | Arlo ballots (`draw_sample` → consistent_sampler) | Arlo batches (PPEB) |
|---|---|---|---|
| Randomness | output k = `SHA256(str(seed) + "," + "\0"*k)` (cryptorandom; confirmed with `hashlib`) | `sha256_uniform(sha256_hex(seed) + str(id))`, decimal digits reversed (`consistent_sampler.py:244-297`) | `default_rng(int(sha256_hex(seed), 16)).random(n)` plus a CDF search (`sampler.py:96-125`) |
| Depends on order | **yes**: the k-th CVR gets output k (`Audit.py:828-829`). P1: reversing the list changed all of the first five picks | no (P1) | no: keys are sorted (`sampler.py:333`) |
| What is hashed | `str(seed)`, so `SHA256(5)` ≡ `SHA256("5")` | `str(((jurisdiction, tabulator, batch), position))` (`shared.py:1140`), e.g. `(('J1', None, 'B1'), 9)`; an apostrophe in a name switches the quoting to `"O'Brien"` | 256-bit integer → `SeedSequence` → PCG64 |
| Replacement | set by the test's N | `next_fraction` re-tickets a drawn ballot (`:300-331`); with replacement except for non-CVR ballots in hybrid audits (`shared.py:1244`) | with replacement |
| Later rounds | resuming restarts at position `len(sampled)` (`Audit.py:964-967`) and **re-appends** earlier picks (P1: duplicates `[10, 14]`) | `take = n + num_sampled`, then `[num_sampled:]` (`sampler.py:61-69`); round 2 equals `s10[5:]` (P1) | prefix property (docstring `:295-300`) |
| Precision | 256-bit integer | `trim(…, 18)` for output only (`:172-198`) | float64 |

- Keeping only the `drop + take` smallest first tickets (`consistent_sampler.py:595-596`) is safe for sampling with replacement, because a ballot's later tickets always exceed its first.
- `sampler.py:22`'s docstring says "with replacement" regardless of the flag.
- The PPEB path rebuilds `Generator.choice(p=…)` from `random()` (`sampler.py:102-104`). NEP 19 says these objects "MUST guarantee stream-compatibility" for `.bytes()`, `integers()` and `random()` only. Reading that as covering today's `Generator.random` is my interpretation (Basis: documentation + derived).
- Arlo's experimental extra-batch selection uses `random.Random(str(seed)).choice(sorted(...))` (`shared.py:916`, `:1032`). Python guarantees only that `random()` sequences are reproducible for a compatible seeding, not `choice`.

### 4. RAIRE: reducing IRV to NEB/NEN assertions

Basis: source + execution (P3).

**Semantics** (raire-rs `assertions.rs`):

- **NEB(w, l)** (`27-41`): w cannot be eliminated before l. The comparison is w's first preferences against l's votes over {w, l}.
- **NEN(w, l, S)** (`181-199`): with exactly S continuing, w out-polls l, so w is not eliminated next.

A set of assertions suffices when every elimination order that ends in a candidate other than the reported winner contradicts at least one assertion.

**Difficulty** (`audit_type.rs:35-131`), as a function of the winner tally w and loser tally l:

| Variant | Difficulty |
|---|---|
| `OneOnMargin` | `N/(w−l)` |
| `OneOnMarginSq` | `(N/(w−l))²` |
| `MACRO` | `−ln α·2γN/(w−l)` |
| `BRAVO` | average sample number with `s = w/(w+l)` |

Ties give ∞, and a set's difficulty is its maximum. raire-rs has `verify_result_does_prove_winner` (`raire_algorithm.rs:66-75`), but only `utilities/examples/us_examples.rs:46` calls it.

**Differential results.**

- On the guide example (13 500 ballots, winner Chuan), raire-rs returned 6 assertions with difficulty 27.0 (margin 500) in 0.00 s and 3.2 MB RSS.
- SHANGRLA's assorters, built from raire-rs's JSON, reproduced its margins `[4000, 4500, 500, 500, 2500, 3000]` exactly.
- SHANGRLA's own Python port returned 13 untrimmed assertions, with the same maximum and complete coverage.
- Arlo's port returned 3 assertions, with the winner set exactly as Arlo's own tests set it. Three elimination orders were left standing, for example `(Bob, Chuan, Diego, Alice)`.
- Across the 5 bundled examples, Arlo's port was incomplete on 3: guide, NEB_assertions and why_not_audit_every_step, with 3, 1 and 4 uncovered orders. It matched raire-rs on the other 2.

**Cause.** `server/audit_math/raire.py:178-187`:

```python
                if not newn.expandable:
                    # 'newn' is a leaf.
                    if (
                        newn.estimate == np.inf
                        and newn.best_ancestor.estimate == np.inf
                    ):
                        return False

                    lowerbound = max(lowerbound, newn.best_ancestor.estimate)  # ty: ignore[unsound-assignment]
                    frontier.replace_descendents(newn.best_ancestor)
```

If the leaf's estimate is finite but its ancestor's is ∞:

1. `lowerbound` becomes ∞.
2. The ancestor, which carries no assertion, replaces its descendants.
3. The loop exits through `if not to_expand.expandable: return True` (`:116-117`).
4. Nodes without an assertion are filtered out (`:275-281`).

SHANGRLA's `manage_node` (`shangrla/raire/raire_utils.py:795-803`) branches on `if newn.best_ancestor.estimate <= newn.estimate:` and otherwise does `frontier.insert_node(newn)`. Copying that branch into Arlo (patch P3b) produced exactly raire-rs's sets on all 5 examples, with nothing uncovered.

Arlo's `make_neb_matrix` also skips NEB assertions whose loser is a winner (`raire.py:49`). `compute_raire_assertions` is called only from `server/tests` (source search).

### 5. IRV/STV tabulation rules

Basis: source + documentation; execution P4 and T1.

| Rule set | Tally | Surplus TV | Rounding | Ties |
|---|---|---|---|---|
| rcv, multi-seat | `BigDecimal`, d ∈ [1, 20] (`ContestConfig.java:79-80`) | inclusive Gregory: a winner's ballot keeps `ftv − round_down(ftv·surplus/votes)` (`Tabulator.java:220-238`, `CastVoteRecord.java:210-218`) | `divide` and `multiply` use `RoundingMode.DOWN` at scale d (`ContestConfig.java:1021-1029`); residual surplus is logged (`Tabulator.java:422-436`) | random, ask, previous-round counts then random or ask, candidate order, permutation (`Tabulator.java:1351-1360`) |
| rcv threshold | — | Droop `floor(V/(S+1)) + 10^-d` (or `+1`); Hare `ceil(V/S)` | `DOWN` / `UP` (`Tabulator.java:474`, `:480`) | — |
| ConcreteSTV `FederalPost2021` | `usize` | one TV for all papers, surplus/papers | `mul_rounding_down` | `AnyDifferenceIsADiscriminator` (`federal/src/lib.rs:34-57`, `:268`) |
| `ACTPre2020` / `ACT2021` / `ACT2020` | `usize` / 6-decimal / 6-decimal | last parcel, continuing papers, capped at the prior TV | down / down / **nearest** (`act/src/lib.rs:239`) | `AnyDifferenceIsADiscriminator` (`act/src/lib.rs:21-70`, `:172-205`, `:221-269`) |
| `NSWLocalGov2021` | `usize` | surplus over continuing papers; equal TVs merged | down | historical counts all different (`nsw/src/lib.rs:38-66`) |
| `NZMeekLegislation` / `NZMeekApocryphal` | 9-decimal | Meek keep values; quota `(v − vnt)/(n+1) + 10⁻⁹` | clause 10: round every product up / round down except the last | legislated / "apocryphal" NZ PRNs (`nzmeek/src/lib.rs:62-73`, `:114-134`, `:158-162`) |

ConcreteSTV keeps exact transfer values as a `BigRational` (`stv/src/transfer_value.rs:24`). Rounding happens only in each rule set's conversion function.

**Tie-break ordering.** ConcreteSTV sorts tied candidates by index before a ChaCha20 shuffle "because Hash table ordering is not guaranteed to be repeatable" (`stv/src/random_util.rs:32-38`). rcv sorts in the `Tiebreak` constructor (`Tiebreak.java:88`). In previous-round mode, though, it narrows the tied set through `new HashSet<>(candidatesInContention)` (`:254`) and calls `doRandom(candidatesInContention)` without re-sorting (`:286`). The documentation for the fallback points to the "Random" mode (`config_file_documentation.txt:169`), where "the list of tied candidates is sorted alphabetically" (`:156`). rcv was not built or run.

T1 is a toy of JDK semantics, not rcv. With `new Random(42)`, index 2 picks `Kim` from the sorted list `[Amy, Bob, Kim, Zed]` but `Amy` from HashSet order `[Bob, Zed, Amy, Kim]`. A recount written from the documentation could therefore pick a different candidate.

**Seat flips in ConcreteSTV (P4).** 2000 synthetic profiles (5 candidates, 2 seats), 12 000 runs, 12.35 s:

| Rule-set pair | Profiles with different elected sets |
|---|---|
| `ACTPre2020` vs `ACT2021` | 30 |
| `ACT2020` vs `ACT2021` | 0 |
| NZ Legislation vs NZ Apocryphal | 12 |
| `FederalPost2021` vs `ACT2021` | 122 |
| `FederalPost2021` vs `NZMeekApocryphal` | 188 |

These frequencies belong to the toy distribution.

Worked example, profile 145 (91 papers, quota 31):

1. K4 has 48 votes, so its surplus is 17 and TV = 17/48.
2. Of K4's papers, 11 go to K0 (adding 3.896) and 37 to K3 (adding 13.104).
3. With integer tallies, K3 = 18 and ties K2. The countback (count 1: K3 5, K2 18) excludes K3, and K2 is elected: {K4, K2}.
4. With 6 decimals, K3 = 18.104166, so K2 is excluded and K0 is elected: {K4, K0}.

The NZ divergences I inspected (profiles 16, 85 and 149) all begin with a first-preference tie that the two PRN schemes break differently, not with clause-10 rounding.

**Documented divergences from official counts** (Basis: documentation, not reproduced). ConcreteSTV's `ElectionRules.md` records:

- the AEC applying rule 273(18) in 2019 and 2022 (lines 36-38), and bulk exclusion in 2016 (33-35, 48-50);
- ElectionsACT's 2020 rounding and last-parcel bugs, fixed in a 2021 recount (109-121);
- NSWEC errors in 2012 and 2016 (133-134);
- NZ clause-10 rounding that conflicts with published results (223-234).

The same document says NSW random selection "can significantly change the outcome" when the count is rerun (125-127); Conway et al. (DOI 10.1145/3014812.3014837) analyse this. The NZ Meek implementation is marked "NOT YET SUITABLE FOR USE FOR CHECKING ELECTION RESULTS!" (`nzmeek/src/lib.rs:28`).

### 6. Certificate-checked counting

Basis: source (line counts at the pins) + documentation.

**Modular_High_Assurance_Voting_Verifiers** (HOL4 → CakeML).

- `Valid_Certificate` requires an initial judgement (zero tallies, empty piles, all candidates continuing), and every consecutive pair of judgements must satisfy one of `HWIN`, `EWIN`, `COUNT`, `TRANSFER`, `ELECT`, `ELIM_CAND` or `TRANSFER_EXCLUDED` (`Checker/CheckerSpecScript.sml:14-61`).
- `Check_Parsed_Certificate_iff_Valid_Certificate` (`CheckerProofsScript.sml:113-118`) proves the implementation equals the specification.
- Instantiations: ACT, an ACT variant, Victoria, union elections, CADE.
- Size: 5550 lines of HOL4 (Checker 395, Auxiliary 2110), plus an untrusted 345-line Haskell certificate generator.
- A prebuilt ACT checker is committed (405 281 B, ELF x86-64, with `basis_ffi.c`).
- Trusted base (derived): the HOL4 kernel, CakeML's compiler theorem, the C FFI, the OS, and the rule specifications.
- Build cost per the README (line 24): about 6 h for CakeML dependencies plus 1.5 h per verifier.
- The VSTTE abstract claims "real-size elections efficiently"; no figures were retrieved.

**Modular-STVCalculi** (Coq): 6062 lines. `FrameBase.v` has 3674; the ACT, Victoria and ANU-Union instances have 635–746 each. It extracts Haskell counters that emit certificates; extraction and the runtime are trusted.

**Checker** (2017, HOL4): 2573 lines.

None of these checkers shows that the certified ballots equal the paper ballots.

### 7. Performance and resource levels (L1–L6)

| Level | Measurements and status |
|---|---|
| L1 | **Non-blank lines of code** (source): SHANGRLA core 3666 plus raire port 1133, against 1636 test lines. Arlo `audit_math` 3891 against 8007 test lines. consistent_sampler 498. rcv main 12 771 (tabulator core 2158) against 1383 test lines and 87 test-data directories. ConcreteSTV `stv` 7091, `federal` 1497, `nsw` 2081, `act` 732, `nzmeek` 265. raire-rs core 1564 against 552 test lines. HOL4 5550; Coq 6062. **Not examined:** person-months and token budgets. |
| L2 | **Measured:** raire-rs workspace, release, `-j 16`, cold target directory: 22.78 s. ConcreteSTV `-p main-app`, `-j 32`: 64 s. **Documentation:** CakeML about 6 h + 1.5 h. **Not examined:** rcv (Gradle 8.14 with JavaFX), Coq and HOL4 builds. |
| L3 | raire-rs on 4 candidates: 0.00 s wall (it reports about 2.4e-5 s to find assertions). Python ports: under 2 s per example including setup, not separated. |
| L4 | **SHANGRLA:** `alpha_mart` + `shrink_trunc` 6.4 / 70.6 / 725.8 ms for n = 10⁴ / 10⁵ / 10⁶; `assign_sample_nums` 10.1 / 88.7 ms for 10⁴ / 10⁵ CVRs. **Arlo:** `draw_sample` (take 1000) 72.6 / 462.5 ms for 10⁴ / 10⁵ ballots, linear because every id is hashed. **ConcreteSTV**, 549 919 synthetic papers (20 candidates, 5 seats): 2.61 s `FederalPost2021`, 2.71 s `ACT2021`, 3.00 s `NZMeekApocryphal`. All single runs. |
| L5 | SHANGRLA's 61 tests pass in 2.38 s. The RAIRE coverage check is O(n!). The CakeML checker was not executed (I chose not to run a committed binary); its speed is reported only qualitatively. |
| L6 | **Binaries:** `raire` 1 429 576 B; `concrete_stv` 4 785 952 B; CakeML checker 405 281 B. **Peak RSS:** `concrete_stv` 23–29 MB at 550k papers; `raire` 3.2 MB; P2 102 MB; P5 268 MB; pytest 151 MB. **Transcripts:** 11.8 / 12.4 / 38.8 KB. **Not examined:** energy. |

### 8. Comprehensibility and simplicity (C1–C2)

**C1. Comprehensibility.**

- **SHANGRLA's model is small** (one inequality per assertion, one supermartingale per test), but its parameter surface is wide: `u`, `N` with an `np.inf` sentinel, `t`, `eta`, `c`, `d`, `f`, `minsd`, `g`, `random_order`. The comparison bound is reset in three places (`Audit.py:1620`, `:1758`, `:2373`).
- **Two defects look like normal output.** `wald_sprt` produces plausible p-values, and `consistent_sampling`'s duplicates appear only in later rounds.
- **Arlo** mixes the `<` and `≤` boundary conventions.
- **Sample locality differs.** The consistent sampler allows local reasoning (one ballot, one hash). Reproducing SHANGRLA's sample needs the exact CVR order, including appended phantoms (`Audit.py:807`).
- **For STV, the burden is ambiguous legislation.** ConcreteSTV names each interpretation as a separate rule set.

**C2. Simplicity.**

- **"Untrusted producer plus small checker"** unifies RAIRE assertion sets, SHANGRLA assertions and STV certificates. The Python RAIRE ports omit the checker; a 20-line coverage check (P3) caught Arlo's defect.
- **Ticket-based sampling** subsumes replacement, contest filtering and resumption.
- **"Canonicalise, then permute with a seeded PRNG"** is the single universal tie rule. rcv's two orderings add a distinction with no purpose.
- **Exact rationals with one explicit rounding step per legislated operation** (ConcreteSTV) separate semantics from arithmetic.

### 9. Validation (V1–V4)

- **V1, specification adequacy and non-vacuity.** The null-calibration run (P2) is the non-vacuity check: it fails `wald_sprt` and passes the valid tests. SHANGRLA's 61 tests miss `wald_sprt`, `kaplan_kolmogorov`, the resume path, and `require_validation`. Arlo's RAIRE tests compare against stored outputs and have no coverage oracle. ConcreteSTV checks itself against official transcripts (documentation).
- **V2, differential testing.** Executed: raire-rs against two ports, SHANGRLA against raire-rs margins, ConcreteSTV rule sets against each other, BRAVO against `alpha_mart`. Documentation: Conway et al. Not examined: fuzzing certificate checkers, and rcv against ConcreteSTV.
- **V3, concurrency, crash and physical.** Mostly known not to apply. The analogue that does apply is cross-platform determinism; the dependencies are Python `repr`, numpy's Generator, `random.Random` and JDK `HashSet`.
- **V4, reality checks.** The paper record is the plant, and the RLA is the runtime check against it (software independence, DOI 10.1098/rsta.2008.0149). Manifest integrity and chain of custody lie outside every subject.

## Boundaries

- **Not examined:**
  - rcv execution;
  - MINERVA, Providence, MACRO, ONEAudit and SUITE numerics;
  - SHANGRLA's Dominion and Hart parsers;
  - NZ PRN details;
  - paper figures (paywalled);
  - building or running the HOL4, CakeML and Coq artifacts;
  - Arlo's database ordering (`num_previously_sampled`, batch keys);
  - `kaplan_markov` and `kaplan_wald`;
  - VVSG 2.0.
- **Unknown:**
  - whether any deployed audit used Arlo's RAIRE port, SHANGRLA's `wald_sprt`, or its resume path;
  - whether rcv's HashSet fallback has ever changed a real selection;
  - how often seats flip in real elections;
  - how stable numpy seeding is across major versions.
- **Unsupported:**
  - SHANGRLA stratified audits;
  - `kaplan_kolmogorov` with replacement;
  - supermajority assertions for "no winner" (`Audit.py:1664-1670`);
  - ConcreteSTV NZ Meek with one vacancy (`ElectionRules.md:268-270`);
  - SUITE after a stratum has been fully counted.
- **Known not to apply:**
  - The `wald_sprt` rates say nothing about ALPHA or betting.
  - Arlo's order independence does not carry over to SHANGRLA.
  - The Arlo RAIRE defect is not reachable from `server/api` at the pin.
- **Not established:**
  - that any real audit confirmed a wrong outcome;
  - that ConcreteSTV's rule sets equal the electoral commissions' rules beyond what its documentation claims;
  - that the CakeML checkers are fast at scale.

## Evidence

**Subjects.** Tarballs come from `https://codeload.github.com/<owner>/<repo>/tar.gz/<sha>`. Paths and lines are cited inline, relative to each repository root.

| Repository | Revision |
|---|---|
| pbstark/SHANGRLA | efd329380937f20e9c4bde8abed00abbd873007d |
| votingworks/arlo | a2f618623c13e7d6109ff6fedfdd85f9a388c5db |
| votingworks/consistent_sampler | 46f6f0a6761adc7172e2c3e844bee359e6bd11bf |
| BrightSpots/rcv | 0baae6680d6338f280ef4874421ac6d9b9d189d4 |
| AndrewConway/ConcreteSTV | 98aa16d63a25832e8e2df0e641c548dd0266b2c5 |
| DemocracyDevelopers/raire-rs | 2349c336ff8f2a9c78bcf781eeaf849f90403bbb |
| MiladKetabGhale/Modular_High_Assurance_Voting_Verifiers | 40de9bf098df41610bdeac349a68eda874900cdd |
| mukeshtiwari/Modular-STVCalculi | e19b6c8e1d23e25e9f9a06becba20f11c2ed386a |
| mukeshtiwari/Checker | 59403ac3bc654c1884d98b550866ac4ea5bab56e |

**Literature**, verified on 2026-11-20 against Crossref or arXiv:

- I. D. Hill, "Algorithm Supplement: Single Transferable Vote by Meek's Method," *Comput. J.* 30(3):277–281, 1987, DOI 10.1093/comjnl/30.3.277.
- R. L. Rivest, "On the notion of 'software independence' in voting systems," *Phil. Trans. R. Soc. A* 366(1881):3759–3767, 2008, DOI 10.1098/rsta.2008.0149.
- M. Lindeman, P. B. Stark, "A Gentle Introduction to Risk-Limiting Audits," *IEEE S&P* 10(5):42–49, 2012, DOI 10.1109/MSP.2012.56.
- A. Conway, M. Blom, L. Naish, V. Teague, "An analysis of New South Wales electronic vote counting," ACSW 2017, 1–5, DOI 10.1145/3014812.3014837.
- M. K. Ghale, R. Goré, D. Pattinson, M. Tiwari, "Modular Formalisation and Verification of STV Algorithms," E-Vote-ID 2018, 51–66, DOI 10.1007/978-3-030-00419-4_4.
- M. K. Ghale, D. Pattinson, R. Kumar, M. Norrish, "Verified Certificate Checking for Counting Votes," VSTTE 2018, 69–87, DOI 10.1007/978-3-030-03592-1_5.
- M. Blom, P. J. Stuckey, V. Teague, "RAIRE: Risk-Limiting Audits for IRV Elections," arXiv:1903.08804.
- P. B. Stark, "Sets of Half-Average Nulls Generate Risk-Limiting Audits: SHANGRLA," FC 2020 Workshops, 319–336, DOI 10.1007/978-3-030-54455-3_23.
- P. B. Stark, "ALPHA: Audit that learns from previously hand-audited ballots," *Ann. Appl. Stat.* 17(1):641–679, 2023, DOI 10.1214/22-AOAS1646.
- F. Zagórski, G. McClearn, S. Morin, N. McBurnett, P. L. Vora, "The ATHENA Class of Risk-Limiting Ballot Polling Audits," arXiv:2008.02315.
- K. Ottoboni, P. B. Stark, M. Lindeman, N. McBurnett, "Risk-Limiting Audits by Stratified Union-Intersection Tests of Elections (SUITE)," arXiv:1809.04235.
- I. Waudby-Smith, A. Ramdas, "Estimating means of bounded random variables by betting," arXiv:2010.09686.
- NumPy NEP 19, https://numpy.org/neps/nep-0019-rng-policy.html.
- Python `random`, "Notes on Reproducibility," https://docs.python.org/3/library/random.html.

**Setup.** x86-64 Linux, Python 3.13; all runs on 2026-11-20.

```sh
python3 -m venv /tmp/venv && /tmp/venv/bin/pip install typing_extensions \
  https://codeload.github.com/pbstark/SHANGRLA/tar.gz/efd329380937f20e9c4bde8abed00abbd873007d \
  https://codeload.github.com/votingworks/consistent_sampler/tar.gz/46f6f0a6761adc7172e2c3e844bee359e6bd11bf
mkdir -p /tmp/arlo && curl -sSL https://codeload.github.com/votingworks/arlo/tar.gz/a2f618623c13e7d6109ff6fedfdd85f9a388c5db | tar xz -C /tmp/arlo --strip-components=1
cargo build --release -j 16                 # raire-rs checkout
cargo build --release -j 32 -p main-app     # ConcreteSTV checkout
```

The cryptorandom wheel resolved by pip had sha256 `1dd5bb74f7942fcf4265036853c2c2903b9403ecf0b67d916dba251da758526e`.

**P1** (`ARLO=/tmp/arlo /tmp/venv/bin/python p1_sampling.py`):

```python
import hashlib, os, sys
sys.path.insert(0, os.environ.get("ARLO", "/tmp/arlo") + "/server")  # import Arlo's audit_math as a package
from cryptorandom.cryptorandom import SHA256
from shangrla.core.Audit import CVR, Contest
import consistent_sampler as cs
from audit_math import sampler as arlo
SEED = "12345678901234567890"
mk = lambda ids, skip=(): [CVR(id=i, votes={} if i in skip else {"C1": {"A": 1}}) for i in ids]
ids = [f"card-{k:03d}" for k in range(20)]
a, b = mk(ids), mk(ids); CVR.assign_sample_nums(a, SHA256(SEED)); CVR.assign_sample_nums(b, SHA256(SEED))
print("SHANGRLA rerun identical:", [c.sample_num for c in a] == [c.sample_num for c in b])
ind = [int.from_bytes(hashlib.sha256((SEED + ",").encode() + b"\0" * k).digest(), "big") for k in range(20)]
print("k-th sample_num == SHA256(seed+','+NUL*k):", ind == [c.sample_num for c in a])
first5 = lambda cv: [c.id for c in sorted(cv, key=lambda c: c.sample_num)][:5]
r = mk(ids[::-1]); CVR.assign_sample_nums(r, SHA256(SEED))
print("first 5, manifest order :", first5(a)); print("first 5, reversed order:", first5(r))
print("SHA256(5) stream == SHA256('5') stream:", SHA256(5).nextRandom() == SHA256("5").nextRandom())
cv = mk(ids, skip={ids[1], ids[3], ids[4]}); CVR.assign_sample_nums(cv, SHA256(SEED))
con = Contest(id="C1", cards=20, choice_function=Contest.SOCIAL_CHOICE_FUNCTION.PLURALITY,
              candidates=["A", "B"], winner=["A"]); con.sample_size = 8
r1 = CVR.consistent_sampling(cv, {"C1": con}); con.sample_size = 12
r2 = CVR.consistent_sampling(cv, {"C1": con}, sampled_cvr_indices=list(r1))
print("round 1:", r1); print("round 2 (resumed):", r2, "duplicates:", sorted({i for i in r2 if r2.count(i) > 1}))
man = {("J1", None, "B1"): list(range(1, 11)), ("J1", None, "B2"): list(range(1, 6)), ("J2", "T1", "B1"): list(range(1, 8))}
s10 = arlo.draw_sample(SEED, man, 10)
print("Arlo rerun identical:", s10 == arlo.draw_sample(SEED, man, 10),
      "| manifest-order independent:", s10 == arlo.draw_sample(SEED, dict(reversed(list(man.items()))), 10),
      "| round 2 == s10[5:]:", arlo.draw_sample(SEED, man, 5, num_sampled=5) == s10[5:])
print("first 3:", s10[:3])
h = hashlib.sha256(SEED.encode()).hexdigest()
tick = lambda i: "0." + "{:064d}".format(int(hashlib.sha256((h + str(i)).encode()).hexdigest(), 16))[::-1]
print("first ticket recomputed with hashlib:", cs.trim(tick(s10[0][1]), 18) == s10[0][0])
print("hashed id text:", str(s10[0][1]), "|", str((("O'Brien", None, "B1"), 3)))
for wr in (True, False):
    print("3-ballot manifest, take 8, with_replacement=%s:" % wr,
          [(t[1][1], t[2]) for t in arlo.draw_sample(SEED, {("J", None, "B"): [1, 2, 3]}, 8, with_replacement=wr)])
```

Output:

```text
SHANGRLA rerun identical: True
k-th sample_num == SHA256(seed+','+NUL*k): True
first 5, manifest order : ['card-019', 'card-005', 'card-011', 'card-006', 'card-003']
first 5, reversed order: ['card-000', 'card-014', 'card-008', 'card-013', 'card-016']
SHA256(5) stream == SHA256('5') stream: True
round 1: [19, 5, 11, 6, 17, 16, 14, 10]
round 2 (resumed): [19, 5, 11, 6, 17, 16, 14, 10, 14, 10, 8, 13] duplicates: [10, 14]
Arlo rerun identical: True | manifest-order independent: True | round 2 == s10[5:]: True
first 3: [('0.054020390556572429', (('J1', None, 'B1'), 9), 1), ('0.103740925193050211', (('J1', None, 'B2'), 2), 1), ('0.126618201390852414', (('J1', None, 'B1'), 7), 1)]
first ticket recomputed with hashlib: True
hashed id text: (('J1', None, 'B1'), 9) | (("O'Brien", None, 'B1'), 3)
3-ballot manifest, take 8, with_replacement=True: [(1, 1), (1, 2), (3, 1), (2, 1), (1, 3), (3, 2), (2, 2), (3, 3)]
3-ballot manifest, take 8, with_replacement=False: [(1, 1), (3, 1), (2, 1)]
```

**P2** (`/tmp/venv/bin/python p2_tests.py`: 8.99 s, 102 MB RSS; SHANGRLA's functions on synthetic populations):

```python
import warnings, numpy as np
warnings.filterwarnings("ignore")
from shangrla.core.NonnegMean import NonnegMean as NM
from shangrla.core.Audit import Assorter, Assertion, Contest, CVR
x, t, eta = np.array([1, 1, 0, 1, 1]), 0.5, 0.6
M = np.cumprod(x * eta / t + (1 - x) * (1 - eta) / (1 - t))            # generalized SPRT, u=1, N=inf
_, h = NM(test=NM.wald_sprt, N=np.inf, t=t, u=1, eta=eta).test(x)
print("independent M_j:", M.round(4), "| 1/p_history from wald_sprt:", (1 / h).round(4),
      "| cumprod(M_j):", np.cumprod(M).round(4))
cross = lambda p: (np.flatnonzero(np.asarray(p) <= 0.05)[:1] + 1).tolist() or [None]
bravo = lambda xs, pw=0.55: np.minimum(1, 1 / np.cumprod(np.where(xs == 1, pw / 0.5, (1 - pw) / 0.5)))
def tests(N, e=0.55):
    return {"alpha fixed eta": NM(test=NM.alpha_mart, estim=NM.fixed_alternative_mean, N=N, t=.5, u=1, eta=e),
            "alpha shrink_trunc": NM(test=NM.alpha_mart, estim=NM.shrink_trunc, N=N, t=.5, u=1, eta=e),
            "betting agrapa": NM(test=NM.betting_mart, bet=NM.agrapa, N=N, t=.5, u=1),
            "wald_sprt": NM(test=NM.wald_sprt, N=N, t=.5, u=1, eta=e)}
rng = np.random.default_rng(20261120)
for label, N in (("null, w/o replacement N=2000", 2000), ("null, with replacement", np.inf)):
    rej, R = {}, 2000
    for _ in range(R):
        xs = rng.permutation(np.r_[np.ones(1000), np.zeros(1000)])[:500] if np.isfinite(N) else rng.integers(0, 2, 500).astype(float)
        for k, T in tests(N).items(): rej[k] = rej.get(k, 0) + (cross(T.test(xs)[1])[0] is not None)
        rej["BRAVO (own code)"] = rej.get("BRAVO (own code)", 0) + (cross(bravo(xs))[0] is not None)
    print(label, {k: round(v / R, 4) for k, v in rej.items()})
pop, res = np.r_[np.ones(5500), np.zeros(4500)], {}
for _ in range(300):
    xs = rng.permutation(pop)[:4000]
    for k, T in tests(10000).items(): res.setdefault(k, []).append(cross(T.test(xs)[1])[0] or 4001)
    res.setdefault("BRAVO (own code)", []).append(cross(bravo(xs))[0] or 4001)
for k, v in res.items():
    print(f"alt 0.55 N=10000 {k:18s} median {int(np.median(v)):5d} p90 {int(np.quantile(v, .9)):5d} unstopped {np.mean(np.array(v) > 4000):.3f}")
try: NM(test=NM.kaplan_kolmogorov, N=np.inf, t=.5, u=1).test(np.array([1., 0, 1]))
except Exception as e: print("kaplan_kolmogorov N=inf ->", type(e).__name__, e)
c = Contest(id="C1", cards=3, choice_function=Contest.SOCIAL_CHOICE_FUNCTION.PLURALITY, candidates=["A", "B"], winner=["A"])
print("Assorter(require_validation=True).assort(cvr) ->",
      type(Assorter(contest=c, assort=lambda v: .75, require_validation=True).assort(CVR(id="x", votes={"C1": {"A": 1}}))).__name__)
s = Contest(id="S", cards=10, choice_function=Contest.SOCIAL_CHOICE_FUNCTION.SUPERMAJORITY, share_to_win=.5, candidates=["Y", "N"], winner=["Y"])
a = Assertion.make_supermajority_assertion(contest=s, share_to_win=2/3, winner="Y", loser=["N"], test=NM.alpha_mart, estim=NM.shrink_trunc)
print("supermajority share_to_win=2/3 arg, contest.share_to_win=0.5 -> upper_bound", next(iter(a.values())).assorter.upper_bound)
try: Assertion.make_assertions_from_json(contest=c, candidates=["A", "B"], json_assertions=[{"winner": "A", "loser": "B", "assertion_type": "X"}], test=NM.alpha_mart)
except Exception as e: print("unknown assertion_type ->", type(e).__name__, e)
```

Output:

```text
independent M_j: [1.2    1.44   1.152  1.3824 1.6589] | 1/p_history from wald_sprt: [1.2    1.728  1.9907 2.7519 4.565 ] | cumprod(M_j): [1.2    1.728  1.9907 2.7519 4.565 ]
null, w/o replacement N=2000 {'alpha fixed eta': 0.036, 'alpha shrink_trunc': 0.0245, 'betting agrapa': 0.033, 'wald_sprt': 0.5155, 'BRAVO (own code)': 0.0155}
null, with replacement {'alpha fixed eta': 0.029, 'alpha shrink_trunc': 0.0265, 'betting agrapa': 0.022, 'wald_sprt': 0.527, 'BRAVO (own code)': 0.029}
alt 0.55 N=10000 alpha fixed eta    median   442 p90  1062 unstopped 0.000
alt 0.55 N=10000 alpha shrink_trunc median   529 p90  1229 unstopped 0.000
alt 0.55 N=10000 betting agrapa     median  1335 p90  2717 unstopped 0.000
alt 0.55 N=10000 wald_sprt          median    32 p90   465 unstopped 0.023
alt 0.55 N=10000 BRAVO (own code)   median   466 p90  1157 unstopped 0.000
kaplan_kolmogorov N=inf -> OverflowError cannot convert float infinity to integer
Assorter(require_validation=True).assort(cvr) -> function
supermajority share_to_win=2/3 arg, contest.share_to_win=0.5 -> upper_bound 1.0
unknown assertion_type -> TypeError 'NotImplementedType' object is not callable
```

**P3.** For each file E in raire-rs `WebContent/example_input/`, run `raire E out.json`, then `ARLO=/tmp/arlo /tmp/venv/bin/python p3_raire.py E out.json`:

```python
import io, json, os, sys, warnings
from itertools import permutations
import numpy as np
warnings.filterwarnings("ignore")
ARLO = os.environ.get("ARLO", "/tmp/arlo"); sys.path.insert(0, ARLO + "/server")
inp = json.load(open(sys.argv[1])); out = json.load(open(sys.argv[2]))["solution"]["Ok"]   # raire-rs input / output
names, N = inp["metadata"]["candidates"], inp["audit"]["total_auditable_ballots"]; W = names[inp["winner"]]
ballots = [b for g in inp["votes"] for b in [{names[c]: r + 1 for r, c in enumerate(g["prefs"])}] * g["n"]]
def norm(kind, w, l, cont): return (kind, w, l, () if kind == "NEB" else tuple(sorted(cont)))
rs = [norm(a["assertion"]["type"], names[a["assertion"]["winner"]], names[a["assertion"]["loser"]],
           [names[c] for c in a["assertion"].get("continuing", [])]) for a in out["assertions"]]
def uncovered(asserts):                      # independent check: which non-W elimination orders survive?
    bad = []
    for order in permutations(names):
        if order[-1] == W: continue
        if not any(order.index(w) < order.index(l) if k == "NEB" else
                   (set(order[-len(c):]) == set(c) and order[-len(c)] == w) for k, w, l, c in asserts):
            bad.append(order)
    return bad
print("raire-rs:", len(rs), "assertions, max difficulty", out["difficulty"], "uncovered", uncovered(rs))
from shangrla.core.Audit import CVR, Contest, Assertion
from shangrla.core.NonnegMean import NonnegMean
cvrs = [CVR(id=str(i), votes={"G": b}) for i, b in enumerate(ballots)]
con = Contest(id="G", cards=N, choice_function=Contest.SOCIAL_CHOICE_FUNCTION.IRV, candidates=names, winner=[W])
js = [{"winner": w, "loser": l, "assertion_type": "WINNER_ONLY"} if k == "NEB" else
      {"winner": w, "loser": l, "assertion_type": "IRV_ELIMINATION", "already_eliminated": [n for n in names if n not in c]}
      for k, w, l, c in rs]
A = Assertion.make_assertions_from_json(contest=con, candidates=names, json_assertions=js, test=NonnegMean.alpha_mart)
sh_m = [round((2 * a.assorter.mean(cvrs) - 1) * N) for a in A.values()]
print("SHANGRLA assorter margins:", sh_m, "== raire-rs margins:", sh_m == [a["margin"] for a in out["assertions"]])
from shangrla.raire.raire_utils import Contest as RC
from shangrla.raire.raire import compute_raire_assertions as sh_raire
rc = {str(i): {"G": b} for i, b in enumerate(ballots)}
sh = sh_raire(RC("G", names, W, N), rc, W, lambda w, l, o, t: t / (w - l) if w > l else np.inf, False, stream=io.StringIO())
sh = [norm("NEB" if a.to_str().startswith("NEB") else "NEN", a.winner, a.loser,
           [n for n in names if n not in getattr(a, "eliminated", [])]) for a in sh]
print("SHANGRLA port:", len(sh), "assertions, uncovered", uncovered(sh))
from audit_math.sampler_contest import Contest as AC
from audit_math.raire import compute_raire_assertions as arlo_raire
fp = {n: sum(b.get(n) == 1 for b in ballots) for n in names}
ac = AC("G", {**fp, "ballots": N, "numWinners": 1, "votesAllowed": 1}); ac.winners = {W: fp[W]}   # as Arlo's own RAIRE tests do
ar = arlo_raire(ac, rc, lambda m: N / m if m > 0 else np.inf)
ar = [norm("NEB" if str(a).startswith("NEB") else "NEN", a.winner, a.loser,
           [n for n in names if n not in getattr(a, "eliminated", set())]) for a in ar]
print("Arlo port (%s):" % ARLO, len(ar), "assertions, same set as raire-rs:", sorted(ar) == sorted(rs), "uncovered", uncovered(ar))
```

Guide example (the `ARLO` path is shown as `/tmp/arlo`; the run used an equivalent extracted tree):

```text
raire-rs: 6 assertions, max difficulty 27.0 uncovered []
SHANGRLA assorter margins: [4000, 4500, 500, 500, 2500, 3000] == raire-rs margins: True
SHANGRLA port: 13 assertions, uncovered []
Arlo port (/tmp/arlo): 3 assertions, same set as raire-rs: False uncovered [('Alice', 'Bob', 'Chuan', 'Diego'), ('Bob', 'Alice', 'Chuan', 'Diego'), ('Bob', 'Chuan', 'Diego', 'Alice')]
```

Other examples:

- unpatched, `NEB_assertions`: 1 uncovered order, `('Diego','Chuan','Bob','Alice')`;
- unpatched, `why_not_audit_every_step`: 4 uncovered orders;
- unpatched, `one_candidate_dominates` and `two_leading_candidates`: same set as raire-rs;
- patched with P3b (`ARLO=/tmp/arlo_patched`), all five examples: `same set as raire-rs: True uncovered []`.

**P3b** (`python3 p3_patch.py /tmp/arlo /tmp/arlo_patched`):

```python
import os, shutil, sys
src, dst = sys.argv[1], sys.argv[2]           # e.g. /tmp/arlo  /tmp/arlo_patched
shutil.copytree(src + "/server/audit_math", dst + "/server/audit_math")
p = dst + "/server/audit_math/raire.py"; s = open(p).read()
old = ("                    lowerbound = max(lowerbound, newn.best_ancestor.estimate)  # ty: ignore[unsound-assignment]\n"
       "                    frontier.replace_descendents(newn.best_ancestor)\n")
new = ("                    if newn.best_ancestor.estimate <= newn.estimate:\n"
       "                        lowerbound = max(lowerbound, newn.best_ancestor.estimate)\n"
       "                        frontier.replace_descendents(newn.best_ancestor)\n"
       "                    else:\n"
       "                        lowerbound = max(lowerbound, newn.estimate)\n"
       "                        frontier.insert_node(newn)\n")
assert s.count(old) == 1; open(p, "w").write(s.replace(old, new)); print("patched", p)
```

**P4** (`python3 p4_cstv.py <ConcreteSTV>/target/release/concrete_stv /tmp/cstv 2000`, 12.35 s):

```python
import json, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
BIN, WORK, NP = sys.argv[1], sys.argv[2], int(sys.argv[3]); os.makedirs(WORK, exist_ok=True)
PAIRS = [("ACTPre2020", "ACT2021"), ("ACT2020", "ACT2021"), ("NZMeekLegislation", "NZMeekApocryphal"),
         ("FederalPost2021", "ACT2021"), ("FederalPost2021", "NZMeekApocryphal")]
RULES = sorted({r for p in PAIRS for r in p})
def run(seed):                       # synthetic profile: 5 candidates, 2 vacancies, 6-12 distinct rankings
    rnd = random.Random(seed)
    btl = [{"candidates": rnd.sample(range(5), rnd.randint(1, 5)), "n": rnd.randint(1, 15)} for _ in range(rnd.randint(6, 12))]
    path, out = f"{WORK}/p{seed}.stv", {}
    with open(path, "w") as f:
        json.dump({"metadata": {"name": {"year": "toy", "authority": "synthetic", "name": f"p{seed}", "electorate": "toy"},
                   "candidates": [{"name": f"K{i}"} for i in range(5)], "vacancies": 2}, "atl": [], "btl": btl, "informal": 0}, f)
    for r in RULES:
        subprocess.run([BIN, r, path, "-t", f"{path}.{r}"], check=True, capture_output=True)
        out[r] = sorted(json.load(open(f"{path}.{r}"))["transcript"]["elected"])
    return seed, out
with ThreadPoolExecutor(32) as ex: res = list(ex.map(run, range(NP)))
for a, b in PAIRS:
    d = [s for s, o in res if o[a] != o[b]]
    print(f"{a} vs {b}: elected sets differ in {len(d)}/{NP}; first {d[:5]}")
```

Output:

```text
ACTPre2020 vs ACT2021: elected sets differ in 30/2000; first [145, 148, 168, 185, 217]
ACT2020 vs ACT2021: elected sets differ in 0/2000; first []
NZMeekLegislation vs NZMeekApocryphal: elected sets differ in 12/2000; first [16, 85, 149, 289, 358]
FederalPost2021 vs ACT2021: elected sets differ in 122/2000; first [27, 31, 59, 61, 74]
FederalPost2021 vs NZMeekApocryphal: elected sets differ in 188/2000; first [6, 16, 27, 31, 33]
```

Profile 145, ranking × count (candidates K0–K4), is reproduced explicitly because Python does not guarantee that `random.Random` produces the same `sample` and `randint` streams across versions:

```text
[4,0,1,3]x11 [3,2,0]x5 [0,2]x12 [0,2,1,3]x7 [2,0]x9 [0,1,4,2]x1 [4,3,1,2]x11 [2,3,4,0]x3 [2,3,0,1]x4 [2,0,1,4,3]x2 [4,3]x15 [4,3,2,1]x11
```

`concrete_stv ACTPre2020|ACT2021 p145.stv` elects `[4, 2]` / `[4, 0]`. The count-2 tallies are `[23, 0, 18, 18, 31]` / `['23.895833', '0', '18', '18.104166', '31']`.

**T1** (`java TieOrder.java`; a toy of JDK semantics):

```java
import java.util.*;
public class TieOrder {
  public static void main(String[] args) {
    List<String> tied = new ArrayList<>(List.of("Zed", "Amy", "Kim", "Bob"));
    Collections.sort(tied);                                   // as in the Tiebreak constructor
    LinkedList<String> viaHashSet = new LinkedList<>();
    for (String c : new HashSet<>(tied)) viaHashSet.add(c);  // as in doPreviousRounds' narrowing
    long seed = 42;
    for (List<String> order : List.of(tied, viaHashSet)) {
      double d = new Random(seed).nextDouble();
      int idx = (int) Math.floor(d * (double) order.size());
      System.out.println(order + " -> nextDouble=" + d + " index=" + idx + " pick=" + order.get(idx));
    }
  }
}
```

Output:

```text
[Amy, Bob, Kim, Zed] -> nextDouble=0.7275636800328681 index=2 pick=Kim
[Bob, Zed, Amy, Kim] -> nextDouble=0.7275636800328681 index=2 pick=Amy
```

**P5** (`ARLO=/tmp/arlo /tmp/venv/bin/python -W ignore p5_perf.py`; output in §7 L4):

```python
import os, sys, time, resource, numpy as np
sys.path.insert(0, os.environ.get("ARLO", "/tmp/arlo") + "/server")
from shangrla.core.NonnegMean import NonnegMean as NM
from shangrla.core.Audit import CVR
from cryptorandom.cryptorandom import SHA256
from audit_math import sampler
def ms(f):
    s = time.perf_counter(); f(); return round((time.perf_counter() - s) * 1e3, 1)
rng = np.random.default_rng(1)
for n in (10**4, 10**5, 10**6):
    x = (rng.random(n) < 0.55).astype(float)
    print("alpha_mart+shrink_trunc n=%d: %s ms" % (n, ms(lambda: NM(test=NM.alpha_mart, estim=NM.shrink_trunc, N=2 * n, t=.5, u=1, eta=.55).test(x))))
for n in (10**4, 10**5):
    cv = [CVR(id=str(i), votes={"C": {"A": 1}}) for i in range(n)]
    print("assign_sample_nums %d CVRs: %s ms" % (n, ms(lambda: CVR.assign_sample_nums(cv, SHA256("1234")))))
    man = {("J", None, f"B{b}"): list(range(1, 101)) for b in range(n // 100)}
    print("Arlo draw_sample %d ballots, take 1000: %s ms" % (n, ms(lambda: sampler.draw_sample("1234", man, 1000))))
print("peak RSS MB:", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024)
```

The ConcreteSTV scale run used a synthetic `.stv` file with 100 000 BTL entries: 20 candidates, 5 vacancies, ranking lengths 1–12, n from 1–10, for 549 919 papers in total. Each rule set was timed with `/usr/bin/time -f "%e s %M KB" concrete_stv <rules> scale.stv`. SHANGRLA's tests were run with `python -m pytest -q tests` from the SHANGRLA checkout. Line counts were taken with `grep -c -v '^\s*$'`.

## Revalidation

- **`wald_sprt`:** check whether it still contains two `terms = np.cumprod(` assignments, then rerun the first lines of P2. A fix gives `1/p_history == M_j`.
- **Sampling:** rerun P1. A fixed SHANGRLA resume prints `duplicates: []`. The Arlo lines must stay `True`; a change to `digits` or to the id text breaks the hashlib recomputation.
- **Arlo RAIRE:** diff `server/audit_math/raire.py` at `if not newn.expandable:`, rerun P3 on the 5 raire-rs examples, and grep `server/api` for `compute_raire_assertions` to see whether it has become reachable.
- **rcv:** check whether `Tiebreak.doPreviousRounds` still passes HashSet-derived lists to `doRandom`, and whether `config_file_documentation.txt:156-169` still promises alphabetical order.
- **ConcreteSTV:** rerun profile 145 under `ACTPre2020` and `ACT2021` (milliseconds). Diff `act/src/lib.rs`, `nzmeek/src/lib.rs` and `ElectionRules.md`.
- **SHANGRLA stratification:** grep `Audit.py` for `Stratified audits are not currently implemented`.
- **Certificate checkers:** no cheap check exists. Rebuilding takes hours (documented); re-diff the cited specification and proof lines and the line counts instead.
