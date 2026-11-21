# Fail-Open Validators for Structured Scientific, Clinical, and Monitoring Data: Cross-Implementation Conformance, Specification-Derived Checkers, Constraint-Based Generation, and Property-Based Testing

## Summary

- **A validator fails open when it accepts input its specification forbids, or reports nothing where it should report a failure.** Every mechanism in this report was confirmed against source at a pinned revision, and most were reproduced by running the real tool:

| # | Mechanism | Confirmed instance |
|---|---|---|
| M1 | Specification default | JSON Schema 2020-12 requires `format` assertion to be off by default |
| M2 | Missing optional dependency | python-jsonschema registers format checkers under `suppress(ImportError)`, and its `FormatChecker` returns true for formats it cannot check |
| M3 | Weak heuristic | python-jsonschema's `email` check is `"@" in instance` |
| M4 | Host-language object model | ajv's default `ownProperties: false` lets `{}` satisfy `required: ["toString", …]` |
| M5 | Prefix-only match | CF checker `cell_methods` uses `regex.match`; dicom-validator drops a trailing "or …" disjunct |
| M6 | Unevaluable condition demoted to optional | dicom-validator: 35–40% of DICOM conditions, per its own documentation |
| M7 | Exception swallowed from the report | compliance-checker drops a crashing check from the JSON score; only stderr and exit code 2 record it |
| M8 | Vacuous check over empty or whitespace input | compliance-checker accepts zero `flag_values` with a whitespace-only `flag_meanings` |
| M9 | Absent data yields no alert | Prometheus: an empty vector, a NaN ratio, or `count()` of nothing produces no alert |
| M10 | Assertion stripped by the optimizer | ISLa's `ThreeValuedTruth` coerces UNKNOWN to `True` under `python -O` |

- **Cross-implementation conformance.** Bowtie (pinned revision) ran 10 JSON Schema implementations on the pinned test suite under draft 2020-12: 409 cases, 1,319 tests. Bowtie skips cases tagged `format-assertion`, which is derived from the counts: 431 compatible cases minus 22 tagged ones.
  - Six implementations agreed on all 1,319 tests, and so did networknt when rerun alone.
  - ajv 8.20.0, run alone, had 11 false accepts, 16 false rejects and 236 errored tests. Most errors came from its default *strict mode* rejecting schemas.
  - python-jsonschema had 9 errored tests (Python `re` rejects `\p{Letter}`) and 1 false reject.
  - One harness failed to start.
  - The first, concurrent run marked 369 ajv cases and 364 networknt cases `mismatched seq`. Isolated reruns cleared this, so a single Bowtie run's error counts are not a property of the implementation.
- **Format assertion in python-jsonschema** (all 479 invalid instances in the suite's `format-assertion` cases for 2020-12): a default install with a `FormatChecker` still accepts 285 of them (59.5%); installing the `format` extra reduces this to 109 (22.8%). The remaining false accepts are mostly `email` (41) and `hostname` (26).
- **Generation-based testing.** Grammar- and constraint-based generators (ISLa; grammar-based whitebox fuzzing; k-path coverage) reach structured edge cases that random text rarely produces. In a toy demonstration, Hypothesis failed to find a prefix-match bug from 5,000 random strings but found it at once with a grammar-shaped strategy. Differential oracles (NEZHA, Bowtie) find acceptance disagreements without a specification oracle. A field study of property-based testing (30 interviews) reports generator effort and effectiveness evaluation as the main weaknesses.

## Applicability

The report covers validators at the pinned revisions in `REPORT.json`:
- JSON Schema: the test suite, the Bowtie harness, python-jsonschema, and ajv v8.20.0 as packaged in Bowtie's harness image;
- DICOM information object definition (IOD) validation: dicom-validator;
- CF/netCDF metadata: the IOOS compliance-checker, read against the CF conventions source;
- input generation: ISLa and Hypothesis;
- alert rules: Prometheus documentation at the pinned revision, plus `promtool` from release v3.16.0.

Executions ran on one host (Linux x86-64, 96 vCPU Intel Xeon @ 2.60 GHz, 236 GiB RAM) with Python 3.13.15 and Podman 5.8.6, on 2026-11-21.

Bowtie executed implementations from container images, which are identified by digest in **Evidence**. The ajv and python-jsonschema versions are the ones those images report: ajv 8.20.0, and python-jsonschema `4.26.1.dev207+g64b62de5d`, the same commit as the pinned source.

Subjects are compared, not combined. Results for one checker version do not transfer to other versions without the revalidation probes. The Hypothesis M1–M5 validators are **toy code written for this report**, not upstream code. The literature figures are the authors' measurements.

## Findings

### F1. Mechanism catalogue

Basis: normative + source + execution, as marked per row

| # | Mechanism | Instance (pinned) | Effect observed | Basis |
|---|---|---|---|---|
| M1 | Specification default | JSON Schema 2020-12 Validation, Format-Annotation vocabulary: assertion "MUST be disabled by default" | All 479 invalid `format` instances accepted when no checker is enabled | normative + execution |
| M2 | Optional dependency | `jsonschema/_format.py:29–30`: "`FormatChecker` objects always return ``True`` when asked about formats that they do not know how to validate"; checkers for hostname, idn-hostname, IRI, URI, time, color, json-pointer, uri-template and duration are registered under `with suppress(ImportError)` | 176 additional false accepts without the `format` extra (285 vs. 109) | source + execution |
| M3 | Weak heuristic | `_format.py:242–245`: `is_email` returns `"@" in instance` | 41 false accepts in `format-email.json` even with extras | source + execution |
| M4 | Host object model | ajv `lib/vocabularies/code.ts:55–63` `noPropertyInData`: ``data[prop] === undefined`` unless `ownProperties` | `{}` valid against `{"required":["__proto__","toString","constructor"]}` | source + execution |
| M5a | Prefix match | compliance-checker `cf/cf_1_6.py:3063` `regex.match(psep, method) is not None` | `cell_methods = "time: mean ;;; DROP"` produces no message | source + execution |
| M5b | Ignored disjunct | dicom-validator `spec_reader/condition_parser.py:84–87, 124, 142` | "…(0018,9361) is YES or the Patient is an animal" parses as "(0018,9361) = YES" | source + execution |
| M6 | Unevaluable condition demoted to optional | dicom-validator README "Limitations": "the related module or tag is considered optional, which may hide some non-conformity"; `doc/source/validation.rst:140`: "Currently, 35-40% of all conditions in the standard are of this kind." | Conditional requirements are silently skipped | documentation + source + execution |
| M7 | Swallowed exception | compliance-checker `suite.py:407–410` stores the exception in `errs` and scores only `vals`; `cchecker.py:323–324` exits 2 | A 3-element `valid_range`, or `units = "days since 1970-13-45"`, removes the check from the JSON report with no field recording it | source + execution |
| M8 | Vacuous or whitespace emptiness | `cf_1_6.py:1371` tests `len(flag_meanings) > 0` on the raw string; the loop at :1378 is over `split()` tokens | Zero `flag_values` plus `flag_meanings = "   "` produces no flags message | source + execution |
| M9 | Absent data | Prometheus `alerting_rules.md`: an alert is active only "Whenever the alert expression results in one or more vector elements" | Threshold, ratio, `count()<k` and `up==0` rules stay silent after the target disappears | documentation + execution |
| M10 | Assertion-only guard | ISLa `three_valued_truth.py:31–36`: `assert self.val != ThreeValuedTruth.UNKNOWN; return bool(self.val)` | `bool(UNKNOWN)` raises normally but is `True` under `python -O` | source + execution |
| M11 | NaN comparison | `cf_1_6.py:593–596`: NaN `_FillValue` passes by explicit branch; a NaN bound makes `fill < rmin or fill > rmax` false | NaN fill accepted. A NaN `valid_range` bound produces a *false failure* (fail-closed). | source + execution |

Several mechanisms in the original question did not appear as validator defects in the examined code:
- *Inverted or mis-associated operators.* The CF mask check `vals_arr & masks_arr == vals_arr` (`cf_1_6.py:1229`) is correct in Python, where `&` binds tighter than `==`. The same text would be wrong in C.
- *Short-circuit skips* appeared only as the toy M3, and as the scope skip in F5 (valid_min only).

### F2. JSON-Schema-Test-Suite structure at the pinned revision

Basis: documentation + execution

The suite now uses one unified tree, `validation/tests/`, which has 69 required files plus 13 files in `optional/` and 4 in `proposals/`, instead of per-draft directories. A case's dialect applicability is given by a `compatibility` string such as `"7"`, `"<=2019"`, `"6,<=2019"` or `"=2020"`. The README gives pseudocode whose early `BREAK` makes the comma-separated terms behave as a disjunction of ranges; it was transcribed verbatim into the probe runner.

`tags` (`format-assertion`, `format-annotation`) tell runners to skip cases whose behaviour the implementation does not provide. `externalSchemas` replaces the old `remotes/` directory and "must" be scoped per case.

The README states its own limits:
- "draft-04 and later releases are well covered"; draft-03 is "reasonably well covered";
- `optional/` "conflates many reasons why a test may be optional".

Census of the required files (execution):

| Dialect | Compatible cases | Tests | Invalid tests | `format-assertion` cases / tests |
|---|---|---|---|---|
| draft-04 | 194 | 911 | 446 | 7 / 239 |
| draft-06 | 263 | 1,218 | 581 | 10 / 340 |
| draft-07 | 304 | 1,655 | 815 | 19 / 683 |
| 2019-09 | 417 | 2,043 | 990 | 21 / 751 |
| 2020-12 | 431 | 2,082 | 1,019 | 22 / 763 (479 invalid) |

Over all dialects there are 613 cases and 2,643 tests, of which 1,282 are invalid; 51 cases use `externalSchemas`.

### F3. Bowtie: how the harness runs implementations and what it reported

Basis: source + execution

**Protocol.** Bowtie starts each implementation's harness in a container and exchanges JSON lines on stdio: `start`, `dialect`, `run` (with a `seq` number) and `stop`. The ajv harness (`/usr/app/bowtie_ajv.js` in the image) constructs `new Ajv2020()` with **default options**, compiles each case, and returns `{valid}` per test, or `{errored, context}`.

**Errors.** Bowtie's container connection waits `read_timeout_sec` (default **2.0 s**) per read, with 3 retries (`bowtie/_containers.py:77–121`). A response whose `seq` differs from the request becomes `CaseErrored.uncaught(message="mismatched seq")` (`bowtie/_core.py:593–600`).

**Report.** The report is JSONL: a header with implementation metadata, then one `{"seq", "case"}` line per case, then per-implementation result lines.

Run: `bowtie suite -i <10 implementations> --dialect 2020-12 <suite>/validation/tests` took 27.35 s wall and 95,212 KB max RSS for the Bowtie process (`/usr/bin/time -v`; container memory not included). Classified per test (support script `classify_bowtie.py`):

| Implementation (reported version) | Agree | False accept | False reject | Errored |
|---|---|---|---|---|
| cpp-blaze (5eeef87e), dotnet-jsonschema-net 9.7.0, go-jsonschema v6.0.2, ruby-json_schemer 2.5.0, rust-boon 0.6.1, rust-jsonschema 0.47.0 | 1,319 each | 0 | 0 | 0 |
| python-jsonschema 4.26.1.dev207+g64b62de5d | 1,309 | 0 | 1 | 9 |
| java-networknt 3.0.6: concurrent run / alone | 142 / 1,319 | 0 / 0 | 0 / 0 | 1,177 / 0 |
| js-ajv 8.20.0: concurrent run / alone (`-j 1`) | 49 / 1,056 | 0 / 11 | 0 / 16 | 1,270 / 236 |
| js-hyperjump | failed to start ("invalid response for Bowtie's protocol") | | | |

In the concurrent run, 369 of ajv's 393 errored cases and 364 of networknt's 365 were `mismatched seq`. Derived explanation (not directly observed): one response arrived after the 2 s × 3 read window. Each later request then read the previous case's late response, so every subsequent case cascaded into `mismatched seq`. Several JVM and Node containers starting concurrently make such delays plausible.

ajv run alone:
- **False accepts** (11), all instances of M4, `unevaluatedItems`/`unevaluatedProperties` interactions, or `$dynamicRef`:
  - 4 for `required` names that are JavaScript prototype properties (`{}`, `{"__proto__":"foo"}`, `{"toString":{…}}`, `{"constructor":{…}}`);
  - 2 for "multiple dynamic paths to the $dynamicRef keyword";
  - 1 for "$dynamicRef points to a boolean schema";
  - 4 for `unevaluated*` combined with `if`/`else`, nested `items`, or `contains`.
- **Errors** (72 cases): mostly strict-mode refusals and unsupported constructs:
  - `unknown format "…" ignored in schema`: 39 cases across 20 formats;
  - `strict mode: unknown keyword: "$anchor"`: 11;
  - `"if" without "then" and "else" is ignored`: 6;
  - "Maximum call stack size exceeded": 3.

Strict mode turns specification-valid schemas into errors, which fails *closed*. `ownProperties: false` fails *open*.

Direct check, in the same image (`node -e`, ajv 8.20.0, node v26.12.1): with default options, `{}` is valid against `{"required":["__proto__","toString","constructor"]}` (`true`); with `{ownProperties: true}` it is invalid (`false`).

### F4. python-jsonschema `format` behaviour, measured on the suite

Basis: source + execution

A runner (`run_jsts.py`) drives `Draft202012Validator` (and the other drafts) over the required files. It enables `FORMAT_CHECKER` for cases tagged `format-assertion` ("tags" mode), or never ("off" mode).

| Install / mode (2020-12, 2,082 tests) | Agree | False accept | False reject | Crash |
|---|---|---|---|---|
| default install, off | 1,593 | 479 | 1 | 9 |
| default install, tags | 1,782 | 285 | 6 | 9 |
| `jsonschema[format]` extras, tags | 1,954 | 109 | 10 | 9 |

- Every false accept in "tags" mode is in a `format-*` file.
- The 9 crashes are `re.PatternError` on `\p{Letter}` (Unicode property escapes, which Python's `re` does not support) in `pattern.json` and `patternProperties.json`.
- With extras, the remaining false accepts include:
  - `email` 41: the `"@" in instance` heuristic;
  - `hostname` 26 and `uri-template` 11: checks backed by optional libraries (`fqdn`, `uri_template`) that still accept these suite inputs;
  - `duration` 10;
  - trailing-newline cases for date-time, time, URI and IRI.
- New false rejects appear with extras: 2 valid leap-second date-times, and 2 valid uri-templates.
- For drafts 4, 6 and 7, every failure is in a `format-*` file. 2019-09 adds only the `vocabulary.json` false reject: a custom metaschema without the validation vocabulary still has validation keywords applied.

The specification permits annotation-only `format` by default (M1). It also says that when the Format-Assertion vocabulary is declared, "Implementations that cannot provide full validation support MUST refuse to process the schema". A checker that returns true for unknown formats does not refuse. Whether python-jsonschema detects that vocabulary declaration was **not established**: the runner fixed the validator class instead of resolving custom metaschemas.

### F5. CF/netCDF: specification-derived checks in compliance-checker

Basis: normative (cf-conventions) + source + execution

**Structure.** Checkers are version classes (`cf_1_6.py` … `cf_1_12.py`), and later versions inherit earlier checks. Results are weighted HIGH/MEDIUM/LOW, scored as points, and grouped by CF section title. Conformance text lives in `conformance.adoc` of the CF repository. For example, line 81 reads "The value of the **`_FillValue`** attribute should not be within a specified valid range", and lines 228–239 give the `flag_*` requirements.

**Probe.** 17 netCDF-4 files were generated by `make_cases.py` and checked with `compliance-checker --test cf:1.8 --format json_new`. Each run took 0.46–0.77 s wall. The baseline scores 52/53; the one failure is the missing `history` global, MEDIUM.

| File: edge case | Reported? |
|---|---|
| `_FillValue` 5 inside `valid_range` [0, 400] | Yes: "should be outside the range" |
| `_FillValue` 5 with only `valid_min` = 0 | **No.** The check runs only for `valid_range` or both bounds (`cf_1_6.py:571`); `else: continue`. |
| `valid_range` with 3 elements | **No message.** `rmin, rmax = variable.valid_range` (:568) raises "too many values to unpack"; the check vanishes from the JSON (56/57); stderr warning; exit 2. |
| NaN `_FillValue`, `valid_range` [0, 400] | Accepted (explicit NaN branch, :593) |
| `valid_range` [NaN, 400], fill −999 | Reported, though −999 lies outside the defined bound: a NaN comparison failing closed |
| zero `flag_values`, `flag_meanings` = 3 spaces | **No message** (M8) |
| one flag value, `flag_meanings` = 3 spaces | Count mismatch reported; "can't be empty" not reported |
| `units = "kelvinish"` | Yes (UDUNITS) |
| `units = "m s-1"` with `standard_name = air_temperature` | Yes (not convertible to K) |
| `coordinates = "lat lon"` (missing variables) | Yes (4 HIGH messages) |
| `cell_methods = "time: mean ;;; DROP"` | **No** (M5a) |
| `calendar = "martian"` | Yes, indirectly ("month_lengths must be supplied") |
| `units = "days since 1970-13-45"` | **No message.** `check_calendar` raises `invalid month`; exit 2. |
| no `Conventions` | Yes (MEDIUM) |
| unknown `standard_name` | Yes (table v95, with close matches) |
| NaN inside the time coordinate | "must be strictly monotonic" (fail-closed) |

**Data model.** Hassell et al. (GMD 2017) define a CF data model that "describe[s] all possible CF-compliant data". They state that cf-python "is, however, not strict about CF compliance", and define no conformance-checking procedure. Without a model, each application makes "its own interpretation" of the conventions, which is a source of checker disagreement.

### F6. DICOM IOD validation from the standard text (dicom-validator)

Basis: documentation + source + execution

**Rule derivation** (`doc/source/validation.rst`). The tool parses DocBook XML for PS3.3 (IOD and module tables), PS3.4 (SOP Class to IOD mapping) and PS3.6 (dictionary) for a chosen edition, so that it uses "exactly the information from a given revision of the standard".

**Usage classes:**
- modules are M, C or U ("Any module not listed for the IOD is not allowed");
- attributes are Type 1, 1C, 2, 2C or 3;
- "type 1/1C attributes are required to have a value".

**Error kinds:** Tag missing, Tag empty, Tag unexpected, Tag not allowed, Enum value not allowed, Invalid value (pydicom VR validation), and Invalid sequence (a wrong VR, after which the sequence "is ignored in the validation").

**Documented open paths:**
- unparsable conditions make the tag or module "optional, which may hide some non-conformity";
- "Defined terms are _not_ checked";
- retired tags "are not considered at all";
- a tag missing from the shared functional group but present per-frame is "not seen as an error".

**Documentation vs. source.** `validation.rst:142` says "If the unparsable condition is part of an AND condition, it is ignored, if it is part of an OR condition, the whole condition is deemed unparsable." The parser at the pinned revision does the opposite:
- a trailing unparsable `and …` returns `ConditionType.UserDefined`, i.e. the whole condition becomes optional (`condition_parser.py:126–141`);
- the project's own tests `test_unparsable_part_invalidates_and_condition1/2` expect this;
- a remainder starting with `or ` is accepted and dropped (lines 84–87 and 142, with the comment at 124: "new sentences and unparsable or-conditions can be ignored").

Executed with the real parser (`cond_probe.py`; the tag dictionary built from pydicom 3.0.2):

| Condition text | Parsed |
|---|---|
| "Required if VOI LUT Sequence (0028,3010) is not present." | `MU`, (0028,3010) absent |
| "Required if the image is reconstructed from a system with multiple X-Ray sources and Multi-energy CT Acquisition (0018,9361) is NO or is absent." | `U` (optional) |
| "Required if Multi-energy CT Acquisition (0018,9361) is YES or the Patient is an animal." (constructed) | `MU`, (0018,9361) = YES: the disjunct is dropped |
| "Required if the Patient is an animal." | `U` |

Dropping a disjunct narrows "required if A or B" to "required if A". A file where B holds and A does not is therefore not checked for the tag. Full IOD validation of DICOM files was **not executed**, because it needs a downloaded edition of the standard.

### F7. Generation-based and differential methods

Basis: source + documentation (papers) + execution

| Method | Input model | Oracle | Reported results (cited) |
|---|---|---|---|
| QuickCheck (ICFP 2000) | Typed random generators | Executable properties | 3 bugs from "implicit unjustified assumptions", incl. that "none of the input clauses was empty"; an example run "passed 100 tests (43% trivial)", where trivial meant the empty list |
| Grammar-based whitebox fuzzing (PLDI 2008; figures from the MSR-TR-2007-154 version) | Grammar plus symbolic constraints on tokens | Crashes and coverage | IE7 JavaScript code generator: coverage 53.5% → 81.5% with 2,378 vs. 6,883 inputs (2 h runs) |
| k-path coverage (ASE 2019) | Grammar paths of length k | Exceptions and branch coverage | More branches than Grammarinator on 22/24 (k=2) and 23/24 (k=3) subjects; 23 exceptions, incl. jsonschema2pojo `StringIndexOutOfBounds` |
| ISLa (ESEC/FSE 2022) | Grammar plus SMT-backed semantic constraints | Constraint check (generate *and* validate) | Abstract: "a few ISLa constraints suffice to produce 100% semantically valid inputs"; throughput tables not examined |
| NEZHA (S&P 2017) | Mutation guided by δ-diversity | Differential: accept/reject tuples | 778 discrepancies (764 X.509, 5 XZ, 2 ELF, 7 PDF); LibreSSL "ignores the ASN.1 time format tag" and may accept expired certificates; ClamAV skips malformed ELF and XZ |
| Hypothesis (JOSS 2019) | Universal choice-sequence representation, shrinking | User properties | No evaluation section; bugs found in numpy and astropy (no count) |
| PBT in practice (ICSE 2024) | Interview study, 30 interviews, 31 participants | n/a | Differential/model-based properties in 17/30; generators "tedious" (6) or "high-effort" (7); 11 had not thought hard enough about effectiveness; budgets of 50 ms–30 s |

**ISLa executed** (pinned revision, z3-solver 4.11.2.0):
- `ThreeValuedTruth` (F1, M10): `bool(UNKNOWN)` raises `AssertionError` normally, and returns `True` under `python -O`, where `not UNKNOWN` is `False`. Whether any ISLa code path coerces an UNKNOWN value with `bool()` during solving was **not examined**.
- Generation throughput: see **Boundaries**.

**Toy probe** (Hypothesis 6.170.17, pinned; `find`, `derandomize=True`, `max_examples=5000`). Each toy validator was paired with a reference predicate, and Hypothesis searched for inputs the toy accepted but the reference rejected:

| Toy mechanism | Minimal counterexample | Wall |
|---|---|---|
| NaN range test `not (x < lo or x > hi)` | `nan` | 0.025 s |
| `all()` over an empty list | `[]` | 0.006 s |
| `units is None or units in UNITS` | `{}` | 0.006 s |
| `not a or b` for "neither" | `(False, True)` | 0.009 s |
| `re.match` prefix, random text | none found | 1.73 s |
| `re.match` prefix, grammar-shaped strategy | `'a: mean;'` | 1.35 s |

### F8. Alert rules on absent data (Prometheus)

Basis: documentation + execution

- **Rule semantics.** `docs/configuration/alerting_rules.md`: an alert is active "Whenever the alert expression results in one or more vector elements". Comparison operators drop the elements for which the comparison is false (`docs/querying/operators.md`).
- **Staleness.** Series disappear after a stale marker or after the 5-minute lookback (`basics.md`, "Staleness").
- **Guards.** `absent(v)` returns "a 1-element vector with the value 1 if the vector passed to it has no elements". `absent_over_time(v[d])` does the same for a window.

`promtool test rules` (v3.16.0, revision e2e28ade…). All series are scraped each minute for 10 minutes, then receive a stale marker:

| Rule | t=5m (data present) | t=15m (data gone) |
|---|---|---|
| `queue_depth > 100` | firing | **silent** |
| `rate(errors)/rate(requests) > 0.05` | firing | **silent** |
| `count(up == 1) < 2` | silent | **silent** |
| `up == 0` | silent | **silent** |
| `absent(queue_depth)` | silent | firing `{job="ingest"}` |
| `(count(up == 1) or vector(0)) < 2` | silent | firing `{}` |
| `absent_over_time(queue_depth[10m])` | — | silent at 15m, firing at 21m |

A second scenario held the counters flat while their series stayed present. The ratio evaluates to NaN (checked with `x != bool x` = 1), and the `> 0.05` alert is silent.

A mutant expectation ("`TooFewInstances` fires at 15m") fails with `got:[]`, so the test file discriminates. The document's own `keep_firing_for` guards against "false resolutions due to lack of data". It does not turn absence into an alert.

### F9. What studies of scientific-software errors say

Basis: documentation (papers)

- **Hatton (IEEE CS&E 1997).**
  - T1, static analysis: interface inconsistencies "one in every 7 interfaces" in Fortran and "one in every 37" in C.
  - T2, nine independent seismic packages: agreement "gradually degenerated from 6 significant figures to 1".
  - Overall: about 8 (C) and 12 (Fortran) "serious faults per 1000 executable lines".
  - Every discrepancy fed back "led to the discovery of a fault".
- **Kanewala and Bieman (IST 2014).** 62 studies. "Oracle problems are prevalent". "Only two studies use test coverage information". Floating-point paths make boundary identification hard.
- **Ziemann et al. (Genome Biology 2016).** Default spreadsheet conversion corrupted gene names in 704 of 3,597 papers with Excel gene lists (19.6%). This is a silent input coercion in which no validator ran.

None of these studies classify validator defects by the mechanisms in F1. The link is derived: their oracle problems are why a differential oracle (F3, F7) or an executable reference predicate (F7) is needed.

### F10. Six-level performance and resource footprint

| Level | JSON Schema (suite, Bowtie, python-jsonschema) | compliance-checker | dicom-validator | ISLa / Hypothesis | Prometheus |
|---|---|---|---|---|---|
| L1 authoring | not measured | not measured | not measured | Goldstein: generators "tedious"/"high-effort" (cited) | not measured |
| L2 toolchain build | not measured (pip installs untimed) | not measured | not measured | not measured | not applicable (release binary) |
| L3 validation latency | 2,082 tests in 0.16 s (python-jsonschema runner, measured); Bowtie 10 implementations, 409 cases in 27.35 s wall (measured) | 0.46–0.77 s per file (measured) | not measured | Hypothesis searches 0.006–1.73 s (measured, toy) | not measured |
| L4 throughput | NEZHA: > 400 certificates/s vs. 271 and 0.08 for comparators (cited) | not measured | not measured | ISLa: see Boundaries | not measured |
| L5 certificate check | not applicable | not applicable | not applicable | not applicable | not applicable |
| L6 memory | Bowtie process max RSS 95,212 KB (measured; containers excluded); harness images 67.6 MB (python-jsonschema) | not measured | not measured | not measured | release tarball sha256 in **Evidence** (size not recorded) |

### F11. Comprehensibility (C1) and simplicity (C2)

Basis: derived

- **C1.** Every fail-open path here is *silent at the point of use*, so the user sees nothing:
  - a JSON report missing a check (M7);
  - an empty alert list (M9);
  - an optional module (M6);
  - a `True` from an unknown format (M2).

  The legible designs make the decision visible: Bowtie's per-case `errored` with traceback; ajv strict mode's explicit refusal; dicom-validator's documented limitations; CF's stderr warning and exit code 2. Their weak point is that the signal lives outside the primary result object.
- **C2.** A single invariant covers M2, M5–M7 and M10: *every requirement the validator cannot evaluate must surface as a third outcome ("not checked"), never as pass*. ISLa models this explicitly (TRUE/FALSE/UNKNOWN) but collapses it with an `assert`. Bowtie models it (`errored`, `skipped`). compliance-checker and dicom-validator model it only out of band: stderr, documentation, and the `U` type. Carrying "unknown" in the result type, rather than in adapters or logs, makes the exceptions ordinary cases without new mechanisms.

### F12. Validation of the validators (V1–V4)

Basis: derived + execution

- **V1, specification adequacy.**
  - The test suite is a shared, curated oracle.
  - The promtool file was mutation-checked: one mutant was killed.
  - The CF probe files are hand-derived from `conformance.adoc`.
  - No examined project reports mutation scores for its checker.
- **V2, differential.**
  - Bowtie is a differential harness, but its verdicts depend on harness configuration (default options), and in one run on timing (F3).
  - NEZHA demonstrates domain-independent differential testing.
  - No differential harness across CF checkers or across DICOM validators was examined.
- **V3, concurrency and robustness.** The Bowtie cascade is a concurrency/timeout robustness finding about the harness itself.
- **V4, human mental models.** Goldstein et al. is the only examined study of practitioner behaviour. No study tests whether users expect `format` or absent-data semantics.

## Boundaries

- **Not examined:**
  - full DICOM file validation, which needs the DICOM standard DocBook download;
  - dicom-validator's measured parse rate (the 35–40% figure is the project's own claim);
  - Bowtie under dialects other than 2020-12, and its optional and format-assertion cases;
  - other CF checkers (cf-checker, cfdm);
  - Grafana and other alerting systems;
  - the PLDI version of grammar-based whitebox fuzzing (figures are from the technical report);
  - the main text of the ISLa paper (abstract and appendix only);
  - Hatton–Roberts 1994 (DOI verified, text not read).
- **Unknown:**
  - **ISLa generation throughput.** A run generating 50 length-prefixed records (`str.to.int(<len>) = str.len(<data>)`) used more than 6 CPU-minutes without completing, and a smaller rerun had produced no output when this report was written. Inputs per second are therefore **not measured**, and no slowness claim is made about ISLa in general.
  - Whether any ISLa code path executes `bool()` on UNKNOWN.
  - The root cause of the `mismatched seq` cascade (F3 gives a source-consistent hypothesis).
  - Whether python-jsonschema honours a declared Format-Assertion vocabulary (F4).
- **Known not to apply:**
  - the ajv `required` false accepts when `ownProperties: true` is set (executed);
  - the python-jsonschema dependency gap (M2) when the `format` extra is installed, though M3 still applies.
- **Unsupported:** Python's `re` does not support `\p{…}`, so python-jsonschema errors on those schemas: it fails closed, with an error.
- **Attractive but unsupported conclusions:**
  - "Six implementations are fully conformant": they agree on the required 2020-12 tests that Bowtie runs, which exclude format-assertion cases.
  - "The CF checker's score measures compliance": checks that crash are removed from the score.
  - Wall-clock comparisons between implementations: Bowtie timing includes container startup.

## Evidence

Observation date: all evidence was gathered on 2026-11-21 (UTC).

**Pinned source:**
- `json-schema-org/JSON-Schema-Test-Suite@e2a68a15cd490750fd6b95e604e4054d7d978d1f`: `README.md`, `validation/README.md`, `validation/tests/**`.
- `bowtie-json-schema/bowtie@7efa389ea00a409ab5402135a828b97e84061b52`: `bowtie/_containers.py:77–121`, `bowtie/_core.py:581–610`; installed with pip from this commit (`bowtie, version 2026.11.5.dev10+g7efa389ea`).
- `python-jsonschema/jsonschema@64b62de5df4ec52d7679c770427329e86a22c395`: `jsonschema/_format.py:24–60, 236–300, 401–541`, `pyproject.toml` (`[project.optional-dependencies] format`).
- `ajv-validator/ajv@0fba0b8e649909613cfce0999b149cd08f4a4987` (tag v8.20.0): `lib/vocabularies/code.ts:16–63`, `lib/vocabularies/validation/required.ts:76–86`, `lib/core.ts:137`.
- `pydicom/dicom-validator@4c10bc6d1e10ae72c1e6dd1e163bc74739e3e8ae`: `README.md` ("Limitations"), `doc/source/validation.rst:20–160`, `dicom_validator/spec_reader/condition_parser.py:1–147`, `dicom_validator/spec_reader/condition.py:11–92`, `dicom_validator/tests/spec_reader/test_condition_parser.py:12–85`.
- `ioos/compliance-checker@b25b86dfe58fd18a1db3e35f3c495837790408dc`: `compliance_checker/cf/cf_1_6.py:536–604, 1159–1388, 3021–3118`, `compliance_checker/suite.py:398–420`, `compliance_checker/runner.py:120–140, 247–276`, `cchecker.py:282–327`; installed from this commit (`cc_version 6.1.1.dev158+gb25b86dfe`).
- `cf-convention/cf-conventions@2805580ad312cd940aa03537b25fa1809781f35b`: `conformance.adoc:71–82, 228–239`, `ch02.adoc:101–124`, `ch07.adoc:283–284`.
- `json-schema-org/json-schema-spec@add836e705c9a07434c467b6b90946ba45258a73` (tags `draft-bhutton-json-schema-01` and `draft-bhutton-json-schema-validation-01`, the 2020-12 documents): `jsonschema-validation.xml:550–635`, `jsonschema-core.xml:348–358`.
- `rindPHI/isla@1a04b7833d2960cffe037fb88826111769fefbeb`: `src/isla/three_valued_truth.py:23–60`, `README.md`.
- `HypothesisWorks/hypothesis@9a15ddde58248954d62f97e6265c8bf99c25bd54` (installed from subdirectory `hypothesis`, reporting 6.170.17).
- `prometheus/prometheus@06170caaea449ce139982c9ca9ddb5bf499ad488`: `docs/configuration/alerting_rules.md:1–48`, `docs/querying/functions.md` (`absent`, `absent_over_time`), `docs/querying/basics.md` ("Staleness"), `docs/querying/operators.md`.
- `prometheus/prometheus@e2e28adeee2c5883d000fc82aca6008cfbf7e96d` (tag v3.16.0): release asset `prometheus-3.16.0.linux-amd64.tar.gz`, sha256 `68727009472a2c02e1ff7f062fd5b3e637285bffc8fc2d340c76fb449d6e0f34`, matching the published `sha256sums.txt`.

**Container images** (ghcr.io/bowtie-json-schema/…, digest as pulled):
- js-ajv `sha256:ea0f71070f9ac77e5b08a57ed76ee6999cb3f8a5e8894b0ca37b8660df80357f`
- python-jsonschema `sha256:bff076a43a8c1535cb916f6e7766af7126a1b967b724373eb266e50cc2a4f6bf`
- java-networknt-json-schema-validator `sha256:4224f99a6f51aa6dbc37279099fa47dc907e4fe7080681b79804cf5287bd59f4`
- go-jsonschema `sha256:1ac7de7c1d3e5f30e4986fb2350316973a7c0460abd5f3ae461f6a25cfbc16fb`
- rust-jsonschema `sha256:617ff1105a376b86cadc5496a0abc12cb5d63cbf158c5b7505bdb6ea76136915`
- rust-boon `sha256:5cfdff38765369da8a9bdeef2ce2c9ab961dc3765999237061d462a2bc309355`
- ruby-json_schemer `sha256:fc52d0352f2bb0e535e6780dc277a944d73ada4c7c751296d8d5252923b322ac`
- dotnet-jsonschema-net `sha256:e11d7fe30d163dde81649f78f17975b0052d6885fd64dada42c2a684da7251f8`
- cpp-blaze `sha256:80df5bd0d020bd0af8eb975a09d6ecea9b7115ab4bb28d6c24616fa9f19ef923`

**Literature** (DOIs verified against Crossref):
- Hatton, IEEE CS&E 4(2):27–38, 1997, DOI 10.1109/99.609829
- Hatton & Roberts, IEEE TSE 20(10):785–797, 1994, DOI 10.1109/32.328993
- Claessen & Hughes, ICFP 2000, pp. 268–279, DOI 10.1145/351240.351266
- McKeeman, "Differential Testing for Software", Digital Technical Journal 10(1):100–107, 1998 (no DOI)
- Godefroid, Kiezun, Levin, PLDI 2008, pp. 206–215, DOI 10.1145/1375581.1375607
- Kanewala & Bieman, IST 56(10):1219–1232, 2014, DOI 10.1016/j.infsof.2014.05.006
- Petsios et al., IEEE S&P 2017, pp. 615–632, DOI 10.1109/SP.2017.27
- Hassell et al., GMD 10(12):4619–4646, 2017, DOI 10.5194/gmd-10-4619-2017
- Havrikov & Zeller, ASE 2019, pp. 189–199, DOI 10.1109/ASE.2019.00027
- MacIver, Hatfield-Dodds et al., JOSS 4(43):1891, 2019, DOI 10.21105/joss.01891
- Steinhöfel & Zeller, ESEC/FSE 2022, pp. 583–594, DOI 10.1145/3540250.3549139
- Goldstein et al., ICSE 2024, pp. 1–13, DOI 10.1145/3597503.3639581
- Ziemann, Eren, El-Osta, Genome Biology 17:177, 2016, DOI 10.1186/s13059-016-1044-7

**Execution commands** (scripts and outputs in `support/`):
1. `run_jsts.py <suite> 2020 --format-mode {off,tags}`, in two virtual environments: `jsonschema` alone, and `jsonschema[format]`.
2. `bowtie suite -i … --dialect 2020-12 <suite>/validation/tests > run.jsonl`, then `classify_bowtie.py run.jsonl`; ajv and networknt rerun with `-j 1`.
3. `make_cases.py nc/` then `run_cases.py compliance-checker nc/`.
4. `cond_probe.py` (dicom-validator).
5. `hyp_probe.py`.
6. `promtool test rules tests.yml` (rules in `rules.yml`).
7. The ISLa `-O` check, as in F7.

## Revalidation

1. **JSON Schema format gap:** rerun `run_jsts.py` against a new suite or library revision. The discriminators are:
   - false accepts in "tags" mode with and without `jsonschema[format]`;
   - `grep -n "always return" jsonschema/_format.py`;
   - `grep -n '"@" in instance'` (the email check).
2. **ajv:** run `new Ajv2020().compile({required:["toString"]})({})` in the harness image. `true` means M4 still holds. Check whether Bowtie's ajv harness passes `ownProperties`.
3. **Bowtie stability:** run each implementation once with `-j 1` and compare its error counts with the concurrent run before trusting either.
4. **CF checker:** run `run_cases.py` on the 17 files. Files 01, 03, 06, 11 and 13 are the discriminators: for each, a message appearing means fixed, and silence or exit 2 means unchanged. Diff `cf_1_6.py` around `check_fill_value_outside_valid_range`, `_check_flag_meanings`, and `check_cell_methods`.
5. **dicom-validator:** run `cond_probe.py`. An `MU` result for the constructed OR sentence means the disjunct is still dropped. Diff `validation.rst:142` against `condition_parser.py:124–145`.
6. **Prometheus:** `promtool test rules tests.yml` should still print SUCCESS. Any change in the absence semantics fails a specific `eval_time`.
7. **ISLa:** `python -O -c "from isla.three_valued_truth import ThreeValuedTruth as T; print(bool(T.unknown()))"`.
