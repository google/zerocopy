# Test-oracle strength: pseudo-tested methods and Descartes, checked coverage, oracle assessment, coverage and mutation versus real faults, tolerance assertions (Hook–Kelly, FLASH, FLEX), assertion-helper defaults, and industrial mutation cost

## Summary

- **Coverage measures execution, not checking.** Four lines of evidence:
  - *Pseudo-tested methods.* These are covered methods whose whole body can be replaced by a trivial body (`return 0`, `return null`, an empty void body) without any test failing. They are found by extreme mutation in every project studied:
    - Niedermayr et al.: 14 Java projects; 6%–53% of covered methods in most projects, 6%–72% under system tests.
    - Vera-Pérez et al.: 21 projects, 28K+ methods; 1%–46% per project, below 7% in 14 projects.
  - *Developer response.* Developers judged only 30 of 101 inspected pseudo-tested methods worth extra testing. All pull requests fixing selected cases in 7 projects were merged.
  - *Checked coverage.* This is the dynamic slice from assertions back into the code. It averaged 43% against 67% statement coverage on seven projects. It fell faster than mutation score as assertions were removed.
  - *Oracle assessment.* Jahangirova et al. improve an oracle by counting false negatives (surviving mutants) and false positives (generated failing-but-correct tests). They raised fault detection by 48.6% on average across five subjects.
- **Mutation score tracks real faults better than coverage, but coverage loses most of its signal once suite size is controlled.**
  - Inozemtseva–Holmes: 31,000 suites over five systems. Coverage–effectiveness correlation is "low to moderate" when suite size is controlled.
  - Just et al.: 357 real Defects4J faults, 230,000 mutants. 73% of faults were coupled to mutants; mutant detection correlates with real-fault detection more strongly than statement coverage does. Defects4J now holds 854 active bugs in 17 projects.
- **Tolerance is the dominant oracle weakness in numerical code, and the evidence base for it is thin.**
  - Hook–Kelly's mutation sensitivity testing (abstracts and the thesis abstract only) reports that tightening tolerances is often more effective than adding tests. Oracles with uncertainty above about 80% of the expected output were "of questionable value".
  - Kanewala–Bieman (62 studies) list choosing tolerances as a core scientific-testing challenge.
  - In ML projects, FLASH found that adjusting thresholds is the most common fix for flaky tests (15 of 79 fixes).
  - FLEX recomputes bounds from Extreme Value Theory (peaks-over-threshold, generalized Pareto) at a chosen percentile. It proposed fixes for 28 of 35 tests; 9 of 19 pull requests were accepted.
- **Default tolerances of common helpers differ by orders of magnitude and in shape.** All rules below are from source and were executed.

  | Helper | Default rule |
  |---|---|
  | `numpy.testing.assert_allclose` | `|a−d| ≤ 0 + 1e-7·|d|`, asymmetric, NaN==NaN |
  | `numpy.isclose`/`allclose` | `|a−b| ≤ 1e-8 + 1e-5·|b|`, asymmetric |
  | `pytest.approx` | `|e−a| ≤ max(1e-6·|e|, 1e-12)` |
  | `math.isclose` | `|a−b| ≤ max(1e-9·max(|a|,|b|), 0)`, symmetric |
  | `unittest.assertAlmostEqual` | `round(a−b, 7) == 0`, scale-free absolute |
  | `numpy.testing.assert_almost_equal` | `|d−a| < 1.5e-7` |
  | `torch.testing.assert_close` | dtype-dependent, e.g. float32 `rtol 1.3e-6, atol 1e-5` |

  Absolute-only rules accept 100% relative error at small magnitudes; relative-only rules reject any nonzero value when the expected value is 0.
- **Industrial mutation testing is feasible only with aggressive suppression.**
  - Petrović–Ivanković 2018: more than 70,000 diffs, 1.1M mutants, 150,000 findings; reported usefulness rose from 20% to 80%.
  - Petrović et al. 2022: about 17M mutants, 760,000 changes, more than 24,000 developers; productive mutants rose from 15% to 89%; the median number of mutants per change fell from 820 (all) to 77 (one per line) to 7 (one per line with arid-node suppression). Resolving one mutant "takes several minutes".
- **A toy experiment** written for this report illustrates the mechanisms; it is not evidence about real projects.
  - The correct integrator's own truncation error, 8.5×10^-8 relative, forces any passing relative tolerance up to that floor. Below it the correct code fails.
  - The kill rate fell from 69.7% at τ=1e-7 to 46.5% at τ=0.1.
  - A tautological oracle killed only crashing mutants.
  - An unchecked helper was covered yet survived extreme mutation (pseudo-tested).

## Applicability

- **Literature.** The report applies to the cited studies' subjects only: Java projects for the pseudo-tested, checked-coverage, coverage and real-fault studies; ML and probabilistic-programming Python projects for FLASH and FLEX; Google's monorepo for Petrović et al.; small numerical routines for Hook–Kelly. Numbers are not transferable to other ecosystems without re-measurement.
- **Tool source** is pinned to development heads resolved on 2026-11-21:
  - PIT `hcoles/pitest@1c6bfcdfdc6078313f5377b31630331e3fb56a33`;
  - Descartes `STAMP-project/pitest-descartes@20cbecff6fab5a3bdfcdc048371981cbae973fd5`;
  - Defects4J `rjust/defects4j@8c16da8230843cdc918eaf4ddb449637f02b83c6` (README states version 3.0.1).

  These revisions postdate the studies. The Descartes operators used in the 2018 tool paper differ in one detail (§2).
- **Assertion helpers.**
  - Source is read at NumPy `numpy/numpy@e092b9144edcdf1c52f46b4b2a0ad0869109c500`, pytest `pytest-dev/pytest@9efd0121a4396da80c20d7c3b7844825966612f6`, CPython `python/cpython@ab5b8f87a70b62a22c1ed78b3e26ccd9ba84caaa` and PyTorch `pytorch/pytorch@f37e6ed227cb8010651c6ee2fda26ec900cc88c9`.
  - Execution used NumPy 2.3.5 (`c3d60fc8393f3ca3306b8ce8b6453d43737e3d90`), CPython 3.13.15 (`4061bc4c35f7c26f25264666d4ba083b93d2f6f9`), and pytest's `approx.py` and `warning_types.py` loaded directly from the pinned pytest revision.
  - The executed releases carry the same default constants and comparison expressions as the heads; the exact lines are listed under Evidence.
  - PyTorch was not executed.
- **The toy experiment** characterises only its own 20-line subject and hand-written test (§8).

## Findings

### 1. What an oracle is, and how its weakness is classified

Barr et al. (TSE 2015) organise solutions to the oracle problem into four groups: "test oracles can be specified ...; test oracles can be derived ...; test oracles can be built from implicit information ...; and no automatable oracle is available, yet it is still possible to reduce human effort". Basis: documentation.

The measures below assess different failure modes of an existing oracle:

| Failure mode | Example | Measure that targets it |
|---|---|---|
| no check reaches the computation | method result never asserted | pseudo-tested detection (extreme mutation); checked coverage |
| check too weak (accepts wrong values) | tolerance wider than plausible errors; tautological expectation | conventional mutation score; Jahangirova false-negative analysis; mutation sensitivity |
| check too strong (rejects right values) | tolerance tighter than algorithmic noise or truncation error | Jahangirova false-positive analysis; FLASH (detects); FLEX (repairs) |
| check of the wrong property | asserting non-null instead of value | checked coverage partly (slice size); mutation |

Basis: derived from the cited definitions.

### 2. Pseudo-tested methods and extreme mutation

**Definition.** Vera-Pérez et al. (EMSE 2019, arXiv:1807.05030v2) define them as methods that "are covered by the test suite, yet no test case fails when the method body is removed, i.e., when all the effects of this method are suppressed." Niedermayr et al. (CSED 2016, arXiv:1611.07163v1) apply this per method:
- void methods have all statements removed;
- methods returning a primitive or string get two mutants with different constant returns;
- object-returning methods return a factory-built instance;
- "it is sufficient for a method to be considered as tested if at least one of the two mutants can be killed".

Methods with no statements, and one-statement getters and setters, are excluded. Basis: documentation.

**Descartes operators** (source, `src/main/java/eu/stamp_project/descartes/DescartesEngineFactory.java` lines 32–55, used when no mutators are configured, lines 17–21):

```java
  public static final List<String> DEFAULT_MUTATION_OPERATORS =
      List.of("void", "null", "empty", "true", "false", "0", "1", "(short)0", "(short)1",
              "(byte)0", "(byte)1", "0L", "1L", "0.0", "1.0", "0.0f", "1.0f", "'\\40'", "'A'", "\"\"", "\"A\"");
```

This list is condensed onto fewer lines than in the file. `'\40'` is the octal escape for a space.

The 2018 tool paper's Table 1 lists `float,double  Returns 0.0 or 0.1`, whereas the pinned source uses `0.0` and `1.0`. A reader replicating the paper should note the difference. Basis: source + documentation.

**Method classification** (`reporting/models/MethodClassification.java` lines 33–68; Basis: source):
- all extreme mutants of a method detected → `TESTED`;
- none detected → `PSEUDO_TESTED`;
- a mix of detected and undetected → `PARTIALLY_TESTED`;
- not covered → `NOT_COVERED`;
- `NOT_COVERED` or `ERROR` mixed with any other outcome → `ERROR`.

`interceptors/stopmethods/StopMethodMatchers.java` (lines 14–107) skips the following "stop methods" by default:
- static initialisers, `hashCode`, `toString`, deprecated and synthetic methods;
- empty void methods;
- bodies that only return null, `this`, a parameter or a constant;
- simple getters and setters, delegates, and enum-generated methods.

**Contrast with conventional operators.** PIT's conventional engine (Gregor) registers operators by name through `ServiceLoader` (`pitest/.../gregor/config/Mutator.java` lines 52–62). `StandardMutatorGroups.java` lines 12–23 define the default groups:
- `DEFAULTS` = `INVERT_NEGS, MATH, VOID_METHOD_CALLS, REMOVE_CONDITIONALS_ORDER_ELSE, REMOVE_CONDITIONALS_EQUAL_ELSE, CONDITIONALS_BOUNDARY, INCREMENTS, RETURNS`;
- `STRONGER` adds `EXPERIMENTAL_SWITCH` and the `_IF` conditional removals.

Conventional operators perturb expressions inside a method. Extreme operators remove the method's effect entirely. Basis: source.

**Prevalence and coverage** (Basis: documentation):
- **Niedermayr et al., 14 open-source Java projects.** The ratio of pseudo-tested to covered methods "ranged between 6% and 53% for most study objects". Under system tests it "ranges between 6% and 72% ... (mean: 35.48%, standard deviation: 20.60%)". Commons Lang had 93% method-level coverage and "less than 2%" pseudo-tested. Predictor, Struts 2 and LittleProxy had more than half of executed methods pseudo-tested. Their conclusion: coverage "is only a valid effectiveness indicator for unit tests".
- **Vera-Pérez et al., 21 projects, 28K+ methods.** "The PS RATE varies from 1% to 46%. In 14 cases its value remains below 7%". Counts ranged from 2 methods (commons-cli) to 473 (jfreechart). The authors attribute their lower range than Niedermayr's to excluding deprecated methods and adding two operators.
  - Conventional PIT mutants planted *inside* pseudo-tested methods were killed far less often. The narrowest gap was pdfbox, at 32% versus 68%. For scifio, only 1% of mutants in pseudo-tested methods were killed, versus 84% in required methods. Required methods average 52 points higher.
- **Developer response (Vera-Pérez et al.).** Pull requests addressing pseudo-tested methods in 7 projects were all merged. Of 101 pseudo-tested methods inspected with developers of 3 projects, developers considered "only 30 of them worth spending time improving the test suite".
- **Cost (Descartes tool paper, ASE 2018).** Descartes "completed the task in much less time" than Gregor in every project: Spoon took "a little less than two hours and a half" versus "more than 56 hours"; JGit 1.5 h versus 16 h; Jaxen under 2 min versus nearly 25 min.

### 3. Checked coverage and oracle assessment

**Checked coverage** (Schuler–Zeller, ICST 2011, author copy; the STVR 2013 extension was read as abstract only; Basis: documentation):
- **Definition.** "the dynamic slice of covered statements that actually influence an oracle". It is computed from one traced run plus slicing from every check statement.
- **Results on seven projects** (AspectJ, Barbecue, Commons-Lang, Jaxen, Joda-Time, JTopas, XStream). Averages were checked coverage 43%, statement coverage 67% and mutation score 75%. "In all projects, checked coverage is lower than regular coverage, with an average difference of 24%."
- **Oracle decay.** With randomly removed assertions, "On average, when 75% of the tests are removed, checked coverage decreases by 23%, whereas the mutation testing score only decreases by 14%". Statement coverage was the least sensitive.
- **Implicit checks.** For the original suites, 32–65% of detected mutations were caught by *implicit* checks (exceptions) rather than assertions. "A test suite with no assertions still detects over 50% of the mutations detected by the original test suite".
- **Cost (Table IV).** Checked coverage (trace plus slice) took between 0:09:36 (JTopas) and 2:02:03 (Joda-Time). Mutation testing with Javalanche took between 0:06:07 (Barbecue) and 20:18:38 (AspectJ). The COMMONS row lists trace 0:32:07 and slice 3:40:37 but total 1:12:44, which is internally inconsistent in the paper.

**Oracle assessment** (Jahangirova et al., ISSTA 2016; abstract only via OpenAlex; Basis: documentation):
- The technique is "assessing and improving test oracles by reducing the incidence of both false positives and false negatives", combining "test case generation to reveal false positives and mutation testing to reveal false negatives".
- It is proved to increase "the mutual information between the actual and perfect oracles".
- On five real-world subjects, fault detection rose "on average, by 48.6% (86% over the implicit oracle)", and three exposed faults were fixed.

**What each measure can flag** (Basis: derived from the definitions above, supported by the toy in §8):

| Measure | Tautological oracle (expected value computed by the code under test) | Tolerance admitting every plausible output |
|---|---|---|
| Statement / branch coverage | no | no |
| Checked coverage | **no**: the slice from `assert f(x) == approx(f(x))` contains `f`, so `f` counts as checked | **no**: slices are value-insensitive |
| Conventional mutation score | yes: mutants change both sides identically and survive (toy: 0 non-crash kills) | partly: mutants whose effect lies inside the tolerance survive, so the score falls as tolerance widens (toy: 69.7% → 46.5%) |
| Extreme mutation (pseudo-tested) | yes: replacing `f` with a constant changes both sides | only if the constant lands inside the tolerance |
| Jahangirova FP/FN assessment | yes (FN analysis) | yes (FN analysis finds too-loose oracles; FP analysis finds too-tight ones) |
| Golden master (exact recorded value) | n/a (it is a different oracle) | it is the tightest regression oracle, but it encodes the old output, not correctness |

### 4. Coverage, mutation score, suite size and real faults

- **Inozemtseva–Holmes** (ICSE 2014, author copy).
  - Setup: "we generated 31,000 test suites for five systems consisting of up to 724,000 lines of source code". Effectiveness was measured by mutation score.
  - Coverage: "there is a low to moderate correlation between coverage and effectiveness when the number of test cases in the suite is controlled for". "stronger forms of coverage do not provide greater insight into the effectiveness of the suite".
  - Suite size: effectiveness correlated with size with r between 0.51 and 0.98 (normalised effectiveness).
  - Basis: documentation.
- **Just et al.** (FSE 2014, author copy).
  - Setup: "357 real faults in 5 open-source applications that comprise a total of 321,000 lines of code" and "230,000 mutants".
  - Coupling: "existence of a coupling effect for 73% of real faults". "10% of real faults require a new or stronger mutation operator". "17% of real faults are not coupled to mutants".
  - Correlation: mutant detection correlates with real-fault detection, and the correlation is "stronger than the correlation between statement coverage and real fault detection".
  - Basis: documentation.
- **Defects4J today** (source):
  - `README.md` (version 3.0.1) states "Defects4J contains 854 bugs (plus 10 deprecated bugs)". Counting `framework/projects/*/active-bugs.csv` rows at the pinned revision gives 854 across 17 projects (Closure 174, JacksonDatabind 110, Math 106, Jsoup 93, Lang 61, Compress 47, Cli 39, Mockito 38, Collections 28, Chart 26, JacksonCore 26, Time 26, JxPath 22, Codec 18, Gson 18, Csv 16, JacksonXml 6).
  - The `d4j-mutation` command applies "AOR, LOR, SOR, COR, ROR, ORU, LVR, STD" by default, mutating "only ... the classes modified by the bug fix" (`framework/bin/d4j/d4j-mutation` POD).
  - Basis: source + derived count.

### 5. Tolerance-based assertions in scientific and probabilistic code

- **Hook–Kelly (2009).** Both papers are closed-access. Only the OpenAlex abstracts and the thesis abstract on which the work is based were read. Basis: documentation, abstracts only.
  - "Mutation sensitivity testing addresses these challenges, showing that a few well-designed tests can detect many code faults and that reducing error tolerances is often more effective than running additional tests" (CiSE 11(6)).
  - "Due to the lack of oracles, scientists use judgment based on experience to assess trustworthiness, rather than correctness" (SECSE).
  - The thesis abstract (Queen's University, 2009) reports "eight small numerical routines, four classes of mutation operators, and 1155 tests". It finds that "oracles that exhibit uncertainties greater than (approximately) 80% of the expected output are of questionable value".
  - Injected-fault classes beyond "four classes" and per-tolerance detection counts were **not examined**.
- **Kanewala–Bieman** (IST 2014, arXiv:1804.01954v1; Basis: documentation).
  - "We identified 62 studies".
  - Testing challenges split into those from software characteristics ("such as oracle problems") and those from cultural differences.
  - Listed explicitly: "Choosing suitable tolerances for an oracle when testing numerical programs is difficult due to the involvement of complex floating point computations".
  - Metamorphic testing appears repeatedly among proposed remedies.
- **FLASH** (Dutta et al., ISSTA 2020; NSF public-access copy; Basis: documentation).
  - Study: 75 bug reports or commits about flaky tests in 20 probabilistic-programming and ML projects. "the majority of the causes for flaky tests (45 / 75) are due to Algorithmic Non-determinism".
  - Fixes (Table 4, 79 fixes): Adjust Thresholds 15, Fix Test 13, Fix Seed 12, Remove Test 10, Mark Flaky 10, Fix Code 9, Adjust Test Params 8, other 2.
  - Detection: FLASH re-runs tests under different random seeds, checking sample convergence with the Geweke diagnostic. It found "11 previously-unknown flaky tests"; developers accepted fixes for 5 and confirmed 5 more.
- **FLEX** (Dutta, Shi, Misailovic, ESEC/FSE 2021, author copy; Basis: documentation).
  - Method: "Peak Over Threshold method from statistical Extreme Value Theory, which estimates the tail distribution of the output values observed from several runs". The tail "converges in the limit to an instance of the Generalized Pareto Distribution". If convergence fails, a Box-Cox transformation is tried.
  - Worked example: a bound is set at the 99.9th percentile (0.2) from 100 samples of a Kolmogorov–Smirnov statistic that the test compared against 0.1.
  - Evaluation: 35 flaky tests in 21 projects using PyTorch, TensorFlow, TensorFlow-Probability, Pyro, PyMC3 and NumPyro. It proposed fixes for 28; "We sent 19 pull requests ... So far, 9 have been accepted".
  - Cost: "Updating the thresholds in the assertions does not change the execution time of the test", while the re-run strategy increases it. The cost of FLEX's own sampling runs was **not found** in the text read.

FLASH and FLEX target *too-tight* bounds that cause flakiness. Neither, in the text read, checks whether the widened bound still rejects plausible faults. Combining FLEX bounds with mutation sensitivity is therefore an open validation step (Basis: derived).

### 6. Default rules of assertion helpers

All rules below were read from source and executed, except PyTorch (source only).

| Helper (source location at pinned head) | Rule | Default tolerances | Symmetric? | Expected = 0 | NaN |
|---|---|---|---|---|---|
| `numpy.testing.assert_allclose` (`numpy/testing/_private/utils.py` 1684, 1783–1785) | delegates to `isclose(actual, desired, rtol, atol)` | `rtol=1e-7, atol=0` | no (scales by `|desired|`) | any nonzero fails | equal by default (`equal_nan=True`) |
| `numpy.isclose` / `allclose` (`numpy/_core/numeric.py` 2252, 2346, 2468–2472) | `less_equal(abs(x - y), atol + rtol * abs(y)) & isfinite(y) | (x == y)` | `rtol=1e-5, atol=1e-8` | no | `|x| ≤ 1e-8` passes | unequal by default |
| `numpy.testing.assert_almost_equal` (utils.py 533, 656) | `abs(desired - actual) >= 1.5 * 10.0**(-decimal)` fails | `decimal=7`, i.e. `< 1.5e-7` absolute | yes | `|a| < 1.5e-7` passes | equal |
| `pytest.approx` (`src/_pytest/approx.py` 488–489, 602, 629–652) | `abs(self.expected - actual) <= max(rel*|expected|, abs)`; if only `abs=` is given, `rel` is ignored | `rel=1e-6, abs=1e-12` | no (scales by expected) | `|a| ≤ 1e-12` passes | unequal unless `nan_ok=True` |
| `math.isclose` (`Modules/mathmodule.c` 2746–2749, 2779–2805) | `diff <= fabs(rel_tol*b) || diff <= fabs(rel_tol*a) || diff <= abs_tol` | `rel_tol=1e-9, abs_tol=0.0` | yes | any nonzero fails | unequal |
| `unittest.TestCase.assertAlmostEqual` (`Lib/unittest/case.py` 960–994) | `round(diff, places) == 0` | `places=7` | yes | `|a| ≲ 5e-8` passes | unequal |
| `torch.testing.assert_close` (`torch/testing/_comparison.py` 96–104, 121–140, 1415–1422) | `isclose` with dtype-derived `(rtol, atol)`; loosest across both inputs | float16 `(1e-3, 1e-5)`, bfloat16 `(0.016, 1e-5)`, float32 `(1.3e-6, 1e-5)`, float64 `(1e-7, 1e-7)`; other dtypes `(0, 0)` | no | depends on `atol` | unequal by default (`equal_nan: bool = False`, line 1422) |

The deprecated `torch.testing.assert_allclose` uses looser defaults (float32 `(1e-4, 1e-5)`, float64 `(1e-5, 1e-8)`; lines 1720–1726) and `equal_nan=True` (line 1703).

**Executed verdicts** (`support/helper_semantics.py`, output `support/helper_semantics.out`; NumPy 2.3.5, CPython 3.13.15, pytest `approx.py` from the pinned revision; Basis: execution):

| Case (actual vs expected) | assert_allclose | assert_almost_equal | np.isclose | math.isclose | assertAlmostEqual | approx |
|---|---|---|---|---|---|---|
| 1+5e-8 vs 1 | PASS | PASS | PASS | FAIL | PASS | PASS |
| 1+5e-7 vs 1 | FAIL | FAIL | PASS | FAIL | FAIL | PASS |
| 1+5e-6 vs 1 | FAIL | FAIL | PASS | FAIL | FAIL | FAIL |
| 1e10+1 vs 1e10 (rel 1e-10) | PASS | FAIL | PASS | PASS | FAIL | PASS |
| 2e-9 vs 1e-9 (100% rel) | FAIL | PASS | PASS | FAIL | PASS | FAIL |
| 2e-12 vs 1e-12 (100% rel) | FAIL | PASS | PASS | FAIL | PASS | PASS |
| 1e-9 vs 0 | FAIL | PASS | PASS | FAIL | PASS | FAIL |
| 1e-300 vs 0 | FAIL | PASS | PASS | FAIL | PASS | PASS |
| NaN vs NaN | PASS | PASS | FAIL | FAIL | FAIL | FAIL |

Asymmetry was executed with `a=1.0, b=1.00001001005`: `np.isclose(a, b)` is `True` and `np.isclose(b, a)` is `False`.

Consequences:
- An absolute default (`assertAlmostEqual`, `assert_almost_equal`, the `atol` terms) accepts every output whose magnitude is below about 1e-7. A quantity of scale 1e-9 is therefore effectively unchecked by default.
- A relative-only default (`assert_allclose`, `math.isclose`) cannot pass any nonzero result against an expected 0.
- The same numeric test thus changes meaning when ported between helpers.

### 7. Measurement designs for real suites

These are protocols, not results; neither was executed.

- **Pseudo-tested methods in scientific and safety-relevant code.**
  - Sample: a fixed list of Maven or Gradle projects with numerical cores, each pinned to a commit.
  - Run PIT with `mutationEngine=descartes` and the default operator list (§2), plus the Gregor `DEFAULTS` group.
  - For each method, record:
    - the Descartes class (§2);
    - statement coverage;
    - the kind of assertion that reaches it, read from a dynamic slice (checked-coverage style): exact equality, a tolerance comparison (helper name and tolerances), exception-only, or none.
  - Report pseudo-tested ratios separately for methods reached only by tolerance comparisons. The cost driver is the test-suite runtime multiplied by the number of extreme mutants (§9 L4/L5).
- **Tolerance sensitivity of numerical test suites.**
  - For each assertion, record the helper and its effective absolute threshold at the observed magnitude (§6).
  - Inject scalar perturbations `x → x·(1+δ)` at each floating-point operation of the code under test, for δ ∈ {10^-k}.
  - Record the smallest δ the assertion detects, and the ratio of that δ to the unmutated code's own observed error (the tolerance floor).
  - An assertion whose minimum detectable δ exceeds the method's claimed accuracy is ineffective by construction. The toy in §8 is a one-routine instance of this protocol.

### 8. Toy mutation-sensitivity experiment

TOY MODEL; the script is `support/tolerance_mutation.py` and its output is `support/tolerance_mutation.out`. Basis: execution (toy model of the protocol in §7, not any real project).

**Setup.**
- Subject: composite Simpson integration with n=16, plus an a-posteriori `error_estimate` whose result the test never asserts.
- Test: integrate `exp` on [0,1] against `e−1`.
- Mutants: 99, generated from the AST — 12 operator swaps, 80 constant replacements (including `c·(1+δ)` for δ = 10^-2…10^-10), 4 loop-bound shifts, and 3 whole-body `return 0.0` replacements.
- Statement coverage of the subject under the test: 13 of 14 statements, missing only the odd-`n` adjustment.

**Results.**
- **Tolerance floor.** The correct code's relative error is 8.473×10^-8. It fails at τ=1e-9 and 1e-12, and passes at τ=1e-7, the `assert_allclose` default, with only a 1.18× margin.
- **Kill rate versus τ (Oracle A, analytic reference).**

  | τ | 1e-7 | 1e-6 | 1e-5 | 1e-4 | 1e-3 | 1e-2 | 1e-1 |
  |---|---|---|---|---|---|---|---|
  | killed | 69.7% | 66.7% | 66.7% | 63.6% | 63.6% | 60.6% | 46.5% |

  25 mutants crash and are killed at every τ.
- **Survivors at τ=1e-6 (33 mutants).**
  - 23 produce a value bit-identical to the original on the test input. Some of these are equivalent only for this input: `b - a` → `b + a` is invisible because `a = 0`, and mutations of the odd-`n` branch are invisible because `n = 16`.
  - 10 change the value by less than the tolerance. Constant perturbations of δ ≤ 1e-6 on the Simpson weights survive.
- **Other oracles.**
  - *Tautological* (expected value recomputed by the subject): 25 of 99 killed, the crashes only.
  - *Golden master* (exact old value): 76 of 99.
  - *Observed order of accuracy* (n = 8, 16, 32 must give an order in [3.5, 4.5]): 71 of 99. It kills 5 of the 33 τ=1e-6 survivors without using any reference tolerance.
- **Extreme mutation.** Replacing `error_estimate`'s body with `return 0.0` survives every value oracle. The method is covered but pseudo-tested.

### 9. Industrial cost of mutation analysis (Petrović et al.)

Basis: documentation.

- **2018** (ICSE-SEIP, author PDF):
  - The approach is diff-based and probabilistic. It mutates only covered lines of changed code, at most one mutant per line, and suppresses "arid" lines by language-specific heuristics informed by developer feedback.
  - Scale: "used by 6,000 engineers ... affecting in total more than 13,000 code authors". It processes "about 30% of all diffs ... that have statement coverage calculated".
  - Results: "more than 70'000 diffs, testing 1.1 million mutants and surfacing 150'000 actionable findings during code review ... usefulness ... improved from 20% to 80%". "Over 87% of all test runs over mutants fail, killing the mutant".
  - The ABS mutator was dropped as predominantly not useful.
- **2022** (TSE 48(10), arXiv:2102.11378v2):
  - Scale: "more than 24,000 developers on more than 1,000 projects"; "almost 17 million mutants and 760,000 changes, which surfaced 2 million mutants during code review".
  - Unproductive mutants: developers "initially classified 85% of reported mutants as unproductive". Suppression heuristics "improved the ratio of productive mutants from 15% to 89%".
  - Mutants per changelist (median): 820 for traditional mutagenesis, 77 for one per line, 7 for one per line after arid-node exclusion.
  - Productivity by operator: ROR 84.1%, UOI 74.5%. By language: Java 87.2%, Python 70.6%.
  - Human cost: "evaluating and resolving a single mutant takes several minutes".

### 10. Performance and resource footprint across six levels

| Level | Evidence | Basis |
|---|---|---|
| L1 human / agent effort | about "several minutes" per mutant (Petrović et al. 2022); 30 of 101 pseudo-tested methods judged worth fixing (Vera-Pérez); FLEX: 19 PRs, 9 accepted. LoC per person-month and token budgets: not measured | documentation |
| L2 tool build time | PIT, Descartes, Defects4J build time: not measured | not measured |
| L3 analysis latency | Descartes vs Gregor: about 2.5 h vs >56 h (Spoon), 1.5 h vs 16 h (JGit), <2 min vs about 25 min (Jaxen). Checked coverage 0:09:36–2:02:03 vs Javalanche 0:06:07–20:18:38 (seven projects). Toy engine: 99 mutants in 0.15 s (toy) | documentation + execution (toy) |
| L4 effect on tested code | none: oracle measures do not change production code. FLEX bound updates leave test time unchanged; re-runs multiply it | documentation |
| L5 check throughput | median 7 surfaced-candidate mutants per change after suppression (vs 820); at most 1 mutant per line (Petrović) | documentation |
| L6 memory / artefacts | dynamic-slice trace sizes: not reported in the text read; not measured | not measured |

### 11. Human comprehensibility and model simplicity

- **C1, comprehension.**
  - A pseudo-tested report ("method X can return 0 and nothing fails") is a local, legible counterexample.
  - A mutation score or a checked-coverage percentage is a nonlocal aggregate that developers must decompose before acting. Petrović et al.'s shift to one surfaced mutant per line during code review is a response to that cost: usefulness rose from 20% to 80%.
  - Tolerance rules are not human-auditable from call sites. The same `approx`/`isclose` call means absolute, relative, symmetric or asymmetric depending on the library (§6).
  - At small magnitudes the absolute defaults silently turn an assertion into a no-op.
- **C2, simplicity.** One invariant underlies every measure here: an oracle is adequate only if some plausible wrong implementation makes it fail.
  - Extreme mutation, conventional mutation, mutation sensitivity and Jahangirova's FN analysis are the same experiment at different mutant granularities. Checked coverage is a cheap static-plus-dynamic over-approximation that cannot see values; FP analysis and FLEX are its dual, plausible *right* implementations that must pass.
  - A unified treatment would report, per assertion, the interval of perturbations it rejects and the interval of legitimate variation it accepts. This is a derived proposal, not a tested design. It makes the tautological case (empty rejected set) and the over-wide-tolerance case ordinary instances rather than special failure modes.

### 12. Validation of the validators (V1–V4)

- **V1, specification adequacy.** This report's subject is V1 itself. Validation evidence for the measures:
  - Just et al.: mutants couple to 73% of real faults.
  - Schuler–Zeller: oracle-decay sensitivity.
  - Jahangirova et al.: improved fault detection plus 3 confirmed faults.
  - Vera-Pérez et al.: developer adjudication, 30 of 101 methods.
- **V2, toolchain fuzzing.** Not applicable to these tools; no study fuzzed the mutation engines themselves. Not examined.
- **V3, concurrency and nondeterminism.** FLASH's seed-varying re-execution and FLEX's tail modelling are the only nondeterminism-aware oracle validations found.
- **V4, field and human validation.** Petrović et al. used in-review usefulness feedback; Vera-Pérez et al. used merged pull requests. Both are human-in-the-loop field validation.

## Boundaries

- **Not examined.**
  - Full text of both Hook–Kelly papers: closed access; abstracts and the thesis abstract only. Their tolerance values and per-class detection counts are therefore unknown here.
  - Full text of Schuler–Zeller STVR 2013 and of Jahangirova et al. 2016: abstracts only.
  - PIT and Descartes were not executed on any project; all Descartes numbers are from the papers.
  - PyTorch helpers were not executed.
  - Mutation tools for other languages (for example Rust, C++ or Python mutation engines) were not examined in this package.
- **Unknown.**
  - Whether the 2018 Descartes "0.1" float operator is a typo or a since-changed default.
  - FLEX's sampling cost per test.
  - How prevalent pseudo-tested methods are in scientific-computing projects specifically: no study above samples them, and the §7 design is unexecuted.
- **Known not to apply.**
  - Checked coverage does not detect tautological or over-wide-tolerance oracles (§3 table).
  - Golden-master equality does not establish correctness.
  - Inozemtseva–Holmes measured effectiveness by mutants, not real faults.
- **Not established.**
  - That mutation score predicts real-fault detection in every setting: Just et al. found 17% of real faults uncoupled.
  - That pseudo-tested methods are defects: developers rejected about 70% of the inspected methods as not worth testing.
  - That the toy's kill-rate curve applies to any real numerical suite.
  - That Petrović et al.'s productivity figures transfer outside their monorepo, review tooling and language mix.

## Evidence

Evidence was gathered on 2026-11-21 (UTC).

**Source**, at the revisions in Applicability:
- PIT: `pitest/src/main/java/org/pitest/mutationtest/engine/gregor/config/Mutator.java` lines 48–98; `StandardMutatorGroups.java` lines 8–25.
- Descartes: `README.md`; `src/main/java/eu/stamp_project/descartes/DescartesEngineFactory.java` lines 15–59; `reporting/models/MethodClassification.java` lines 10–68; `interceptors/stopmethods/StopMethodMatchers.java` lines 10–109.
- Defects4J: `README.md` lines 1–50 and 70–111; `framework/projects/*/active-bugs.csv` (row counts; header excluded); `framework/bin/d4j/d4j-mutation` lines 25–80.
- NumPy head: `numpy/testing/_private/utils.py` lines 533–545, 656, 1146, 1230–1240, 1684–1699 and 1775–1797; `numpy/_core/numeric.py` lines 2252, 2346 and 2440–2475.
- NumPy 2.3.5 (`c3d60fc8393f3ca3306b8ce8b6453d43737e3d90`): the same definitions at utils.py 506 and 1607, and numeric.py 2280, 2374 and 2496.
- pytest: `src/_pytest/approx.py` lines 484–652 and 774.
- CPython head: `Modules/mathmodule.c` lines 2746–2805; `Lib/unittest/case.py` lines 960–994.
- CPython 3.13.15 (`4061bc4c35f7c26f25264666d4ba083b93d2f6f9`): `mathmodule.c` lines 3165–3222; `case.py` lines 950–952.
- PyTorch: `torch/testing/_comparison.py` lines 90–140, 1415–1422 and 1700–1730.

**Literature.** Every DOI was verified against Crossref (title, author order, venue, year, pages) on 2026-11-21, with no mismatches against the citations used here. The Hook thesis was identified by its handle page.

| Work | DOI or identifier | Version read |
|---|---|---|
| Hook & Kelly (SECSE) | 10.1109/SECSE.2009.5069163 | OpenAlex abstract |
| Hook & Kelly (CiSE) | 10.1109/MCSE.2009.200 | OpenAlex abstract |
| Hook thesis | http://hdl.handle.net/1974/1765 | abstract on the handle page |
| Schuler & Zeller (ICST 2011) | 10.1109/ICST.2011.32 | author PDF, full text |
| Schuler & Zeller (STVR 2013) | 10.1002/stvr.1497 | OpenAlex abstract |
| Inozemtseva & Holmes | 10.1145/2568225.2568271 | author PDF |
| Just et al. | 10.1145/2635868.2635929 | author PDF |
| Kanewala & Bieman | 10.1016/j.infsof.2014.05.006 | arXiv:1804.01954v1 |
| Barr et al. | 10.1109/TSE.2014.2372785 | typeset copy |
| Niedermayr et al. | 10.1145/2896941.2896944 | arXiv:1611.07163v1 |
| Jahangirova et al. | 10.1145/2931037.2931062 | OpenAlex abstract |
| Petrović & Ivanković | 10.1145/3183519.3183521 | author PDF |
| Vera-Pérez et al. (tool) | 10.1145/3238147.3240474 | arXiv:1811.03045 |
| Vera-Pérez et al. (EMSE) | 10.1007/s10664-018-9653-2 | arXiv:1807.05030v2 |
| Dutta et al. (FLASH) | 10.1145/3395363.3397366 | NSF public-access copy |
| Dutta et al. (FLEX) | 10.1145/3468264.3468615 | author PDF |
| Petrović et al. (TSE 2022) | 10.1109/TSE.2021.3107634 | arXiv:2102.11378v2 |

**Execution.** x86-64 Linux, Python 3.13.15, NumPy 2.3.5. Run `support/fetch_pytest_approx.sh` to materialise pytest's `approx.py` and `warning_types.py` from the pinned revision into a scratch directory, then `PYTHONPATH=<that dir> python3 support/helper_semantics.py`. The toy runs as `python3 support/tolerance_mutation.py` with no dependencies. Outputs are preserved as `support/*.out`.

## Revalidation

- **Helper defaults.** Re-run `support/helper_semantics.py` against new library versions and diff the output against `support/helper_semantics.out`. Alternatively grep the definition lines listed in Evidence: `def assert_allclose(`, `def isclose(`, `DEFAULT_RELATIVE_TOLERANCE`, `rel_tol: double`, `places = 7` and `_DTYPE_PRECISIONS`.
- **Descartes operators and classification.** Diff `DEFAULT_MUTATION_OPERATORS` and `MethodClassification.classify` at a new revision.
- **PIT default group.** Diff `StandardMutatorGroups.register`.
- **Defects4J size.** Count rows of `framework/projects/*/active-bugs.csv`.
- **Toy.** `python3 support/tolerance_mutation.py` is deterministic; any change in counts indicates a Python `ast`/`unparse` behaviour change.
- **Study numbers.** These require the papers; no cheaper check exists. The §7 designs must be executed to replace the toy with real-suite evidence.
