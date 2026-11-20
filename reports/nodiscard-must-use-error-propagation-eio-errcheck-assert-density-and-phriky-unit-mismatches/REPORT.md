# Discarded checks: unused-result diagnostics (C, C++, Rust, Go), error-propagation defect studies, assertion density, the Ariane 501 unprotected conversion, and annotation-free unit-mismatch detection

## Summary

- **Three different "discarded check" classes need three different mechanisms.** (1) An *ignored result* (a returned error code or must-use value dropped at the call site) is caught by unused-result attributes and checkers. (2) A *missing or disabled limit check* (an unprotected narrowing conversion, a removed assertion) is invisible to unused-result checking, because nothing is returned and dropped. Only run-time checks, range analysis or proof catch it. (3) An *unstated unit or convention* crossing an interface is caught only by unit inference or unit types. No mechanism studied here covers more than one class.
- **Language defaults differ in ways that matter.** These were measured on real toolchains (rustc nightly 2026-11-11, GCC 15.2, Go 1.27.3, errcheck at a pinned commit):
  - The C23/C++ `[[nodiscard]]` attribute is silenced by a `(void)` cast. GCC's `__attribute__((warn_unused_result))` is *not*.
  - `-Wno-unused-result` silences both.
  - None of the C, C++ and Rust function-level markings follow a call made through a function pointer, a closure or a generic wrapper. Type-level markings do travel through wrappers: C++ `[[nodiscard]]` on a class and Rust `#[must_use]` on a type such as `Result`.
  - Rust's lint looks through `Box`, `Pin`, tuples and non-empty arrays. It does **not** look through `Option<Result<..>>`.
  - `errcheck` flags `fmt.Fprintf` to an arbitrary `io.Writer` by default. Its README claims that `fmt` is ignored entirely by default. Source and execution agree with each other and contradict the README.
- **Effectiveness evidence is real but narrow.** Error-handling studies report large defect populations:
  - EIO: 1153 of 9022 error-propagating calls (13%) in Linux 2.6.15.4 file systems and storage drivers drop the error.
  - Yuan et al.: 92% of 48 catastrophic failures came from mishandled non-fatal errors.
  - Engler et al.: 195 derived-null-checker bugs against 37 false positives.
  - EPEx: 102 new bugs, with 28 false positives among 130 reports.
  
  Confirmation rates vary and are often self-labelled. **Assertion evidence is weak and partly retracted.** Kudrjavets et al. found Spearman correlations of −0.21 to −0.38 between assertion density and fault density in two Microsoft components. The Casalnuovo et al. 2015 GitHub result ("methods with asserts have significantly fewer defects") was reversed by the same authors' replication after a function-extraction defect was fixed. They concluded "there is no evidence that non test asserts have an effect on defects in general."
- **Ariane 501 was a missing protection, not an ignored return value.** The inquiry board says seven conversion variables were analysed as at risk, four were protected, and three, including horizontal bias `BH`, were left unprotected. The stated reason was an 80% processor-workload target, and no justification appeared in the source.
- **phriky-units needs no annotations.** It infers units from ROS message fields and achieved 87% precision (40 TP / 6 FP) on high-confidence reports across 213 ROS systems. Low-confidence precision was 37% (64/171). Recall is unknown.

## Applicability

This report applies to the following pinned subjects and to the evidence classes stated for each claim:

- **Language mechanisms.** Rust's `#[must_use]` handling was read in `compiler/rustc_lint/src/unused/must_use.rs` at `rust-lang/rust` `560abf7946ae41fd210edac5dfe829d7eff86eec`. At that commit the logic lives in the `unused/must_use.rs` submodule declared by `pub mod must_use;` at `unused.rs:17`, not in `unused.rs` itself. Behaviour was **executed** on the toolchain `rustc 1.102.0-nightly` with commit-hash `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`. C and C++ behaviour was executed on GCC 15.2.0 (Debian 15.2.0-14) with `-std=c23` and `-std=c++20`. Clang was not available, so Clang's `[[nodiscard]]`/`warn_unused_result` behaviour is **not examined**.
- **Checkers.** `errcheck` at `kisielk/errcheck` `59d0c8437e9f9e666d6b5ab02e55a093eecf7736` was read and **executed**. It was built offline against `golang/tools` v0.51.0 (`ea2f152dc35325e4b9b639583972375972350a84`), `golang/mod` v0.41.0 (`d0a27b2d4a48460806692bf5c87fc157c3c65292`) and `golang/sync` v0.23.0 (`f75267d8412fc1dfd12b343644a7ea46e4d9c85d`), using a `replace` directive and `GOPROXY=off`. `go vet` (the `unusedresult` analyzer) was executed with the go1.27.3 distribution toolchain. The upstream tag `go1.27.3` is `2aae1000ea1d4b28923b96db28acf4e3b99d6aff`, but distribution patches were not audited. The analyzer source was read at `golang/tools` `7594d6faa7b96cfab035af98d21146b78e23738d`. Error Prone `CheckReturnValue` was **source-only**, at `google/error-prone` `103086b59892dbbac53c573a44ecad79f9decfae`. clang-tidy `bugprone-unused-return-value` was also **source-only**, at `llvm/llvm-project` `0c99e3f432142834a257cd4c3067d7a69373e6d1`.
- **Unit checking.** `unl-nimbus-lab/phriky-units` `16c8cdd91de0899411b139e5a94fcb4ea8104ad2` was **source-only**. The tool requires Cppcheck dumps, and Cppcheck was not installed. Effectiveness numbers come from the author's 2019 dissertation, which reproduces the ISSTA 2017 evaluation. The ISSTA paper PDF itself could not be retrieved.
- **Studies.** Defect numbers come from the papers' own text where full text was retrieved: Engler 2001, EIO 2008, Yuan 2014, Jana 2016 (published abstract only), Kudrjavets (the TR-2006-54 version), Casalnuovo 2015 and its replication, the Ore dissertation, Holzmann 2006 and the Ariane report mirror. For Rubio-González 2009 and Aftandilian 2012, only bibliographic metadata was verified, so their quantitative content is **not examined**.
- **Execution host.** Linux x86_64, 96 logical CPUs (Intel Xeon @ 2.60 GHz), 236 GiB RAM. Timings are single runs with a warm build cache unless stated, and are host-specific.

The subjects are compared side by side. No claim here concerns their combination.

## Findings

### 1. A taxonomy of discarded checks and which mechanism family can see each

| Class | What is lost | Visible to unused-result checking? | Mechanisms that can detect it | Basis |
| :--- | :--- | :--- | :--- | :--- |
| A. Ignored result | A returned status or must-use value dropped at the call site | Yes, when the callee or type is marked or listed | `[[nodiscard]]`, `warn_unused_result`, `#[must_use]`, `errcheck`, `CheckReturnValue`, `bugprone-unused-return-value`, `go vet unusedresult` | source + execution |
| A′. Result kept but then dropped | Stored in a variable, then overwritten or never tested | **No** for every call-site checker examined | Dataflow analyses such as EDP/EIO and Rubio-González's error-propagation analysis; the `errcheck` README points to staticcheck | documentation + execution (errcheck C9 below) |
| B. Missing or disabled limit check | No check exists, or it was compiled out | **No**: there is no result to drop | Run-time checking (Ada constraint checks, assertions), range or abstract interpretation, proof of value bounds | documentation (Ariane report; Holzmann rule 5) + derived |
| C. Unstated unit or frame convention | Two values in different units are combined | **No** | Unit inference (phriky-units), unit types | source + documentation |

Basis: derived from the per-mechanism findings below. The A′ row for `errcheck` was executed (case C9). The B row follows from the Ariane failure mode: the conversion `BH` → 16-bit integer returns nothing to discard.

### 2. Language-level unused-result mechanisms: measured behaviour

#### 2.1 C and C++ (GCC 15.2.0, executed)

The probe sources are `wur.c` and `nd.cpp`, reproduced in `support/`. Diagnostics were run with default flags:

| Case | Code | GCC result |
| :--- | :--- | :--- |
| G1 | `legacy();` where `legacy` has `__attribute__((warn_unused_result))` | warning `-Wunused-result` |
| G2 | `(void)legacy();` | **still warns** (`wur.c:11:11`) |
| G3 | `modern();` where `modern` is C23 `[[nodiscard]]` | warning |
| G4 | `(void)modern();` | silent |
| G5 | `[[nodiscard("check the status")]]` | warning that includes the reason string |
| G6 | `fp_t f = legacy; f();` (function pointer) | **silent** |
| G7 | `CALL_LEGACY()` macro wrapping `legacy()` | warning, located at the macro definition |
| G8, G9 | unannotated call; result used in an `if` | silent |
| P1/P2 | C++ `[[nodiscard]] int f(); f();` and `(void)f();` | warn / silent |
| P3 | `struct [[nodiscard]] Status` returned by value, discarded | warning ("ignoring returned value of type 'Status'") |
| P4 | `call(f)` with `template<class F> auto call(F fn){ return fn(); }`, returning `int` | **silent** |
| P5 | `call(op)` returning `Status` | warning: the type-level marking propagates through the wrapper |
| P6 | `Guard(1);` with a `[[nodiscard]]` constructor | warning |
| P7/P8 | `static_cast<void>(op())`; `[[maybe_unused]] auto x = f();` | silent |
| all | `-Wno-unused-result` | every warning above is silenced |

Basis: execution. Reading: the GNU attribute and the standard attribute share one warning flag but differ on the `(void)` escape. Holzmann's Power of Ten rule 7 explicitly sanctions `(void)` casts as the deliberate-discard idiom: "it can be acceptable to explicitly cast the function return value to (void)". A code base that mixes `warn_unused_result` with that idiom therefore gets warnings that only renaming or restructuring removes. Function-level marking binds to the declaration, not the function type, so any indirection loses it (G6, P4). Type-level marking binds to the value and survives indirection (P5).

#### 2.2 Rust (`rustc` nightly `3ef0c22cd`, executed; source at `560abf79`)

Source facts in `compiler/rustc_lint/src/unused/must_use.rs`:

- `UNUSED_MUST_USE` is declared `Warn` with `report_in_external_macro` (lines 45–48). `UNUSED_RESULTS` is declared `Allow` (lines 85–86). Its documentation says it "is \"allow\" by default because it can be noisy".
- Only statement-position expressions are checked: `let hir::StmtKind::Semi(mut expr) = s.kind else { return; };` (line 285). `let _ = f();` is a `Let` statement and is therefore the explicit-discard syntax.
- A call is checked for a function-level `#[must_use]` only when the callee resolves to `DefKind::Fn | DefKind::AssocFn`. Lines 437–438 read: "`Res::Local` if it was a closure, for which we do not currently support must-use linting".
- Type-level propagation goes through `Box`, `Pin`, `Result<T, Uninhabited>`, `ControlFlow<Uninhabited, T>`, opaque `impl Trait` and `dyn Trait` whose trait is `#[must_use]`, tuple elements, non-empty arrays ("If the array is empty we don't lint, to avoid false positives", line 256), closures and coroutines (`enum MustUsePath`, lines 117–133). Unit and uninhabited types are treated as trivial (lines 143–152 and 349).

Probe `mu.rs` (in `support/`), compiled with `rustc --edition 2024 --emit=metadata`:

| Case | Code | Default lints | With `-W unused_results` |
| :--- | :--- | :--- | :--- |
| R1 | `g();` where `g` is `#[must_use] fn -> i32` | warning | — |
| R2 | `let _ = g();` | silent | silent |
| R3 | `r();` returning `Result<(),()>` | warning (`Result` is a `#[must_use]` type) | — |
| R4 | `let h = g; h();` | **silent** | `unused result of type i32` |
| R5 | `call(g)` with a generic wrapper returning `i32` | **silent** | `unused result of type i32` |
| R6 | `call_r(r)` with a wrapper returning `Result` | warning | — |
| R7 | `(|| g())();` | **silent** | `unused result of type i32` |
| R8 | `m!()` expanding to `g()` | warning | — |
| R9 | `#[must_use]` trait method | warning | — |
| R10 | `#[must_use = "..."] struct Guard` | warning | — |
| R11 | `Some(r());` (`Option<Result<..>>`) | **silent** | `unused result of type Option<Result<(), ()>>` |
| R12–R14 | `(r(),1)`, `Box::new(r())`, `[r()]` | warning (tuple element, boxed, array) | — |
| R15 | `drop(r())` | `dropping_copy_types` warning, because `Result<(),()>` is `Copy` | — |
| R16, R17 | `1 + 1;`, `iter().map(..)` | warning (arithmetic op; `Map` is `#[must_use]`) | — |

Basis: source + execution. `Option` is not `#[must_use]` and `is_ty_must_use` does not descend into it. A `Result` wrapped in `Option` therefore escapes the default lint. This is the type-level analogue of G6/P4.

#### 2.3 Go: no language mechanism; `errcheck` and `go vet` (executed)

Go has no unused-result attribute. Discarding all results of a call in statement position is legal. Two checkers fill the gap. Probe `demo.go` is in `support/`:

| Case | Code | `errcheck` default | `errcheck -blank -asserts` | `go vet` |
| :--- | :--- | :--- | :--- | :--- |
| C1 | `mayFail()` | flagged | flagged | — |
| C2 | `_ = mayFail()` | silent | flagged | — |
| C3 | `defer f.Close()` | flagged | flagged | — |
| C4 | `go mayFail()` | flagged | flagged | — |
| C5 | `fmt.Fprintf(w, "x")` with `w io.Writer` | **flagged** | flagged | — |
| C6, C7 | `fmt.Println`, `bytes.Buffer.WriteString` | silent (built-in excludes) | silent | — |
| C8 | `n, _ := pair()` | silent | flagged | — |
| C9 | `err := mayFail(); err = mayFail(); if err != nil` | **silent** (first error lost) | silent | — |
| C10, C11 | call via func value; immediately invoked closure | flagged | flagged | — |
| C12 | `s := i.(string)` | silent | flagged | — |
| C13 | `callIt(mayFail)`, where the callee drops the error internally | call site silent; flagged *inside* `callIt` | same | — |
| C15 | `fmt.Sprintf("x")` | — | — | `result of fmt.Sprintf call not used` |
| C16 | `errors.New("x")` | flagged (it returns an error) | flagged | `result of errors.New call not used` |

Basis: execution + source. Unlike the C, C++ and Rust function attributes, `errcheck` keys on the *result type* (`isErrorType` uses `types.Implements` against the universe `error` interface, `errcheck.go:23–27`). Calls through function values and closures are therefore caught (C10, C11). Its exclusion list is name-based (`excludes.go:13–68`). `go vet`'s `unusedresult` instead keys on a fixed list of pure functions (`unusedresult.go:62–` lists `context.WithCancel`, `errors.New`, `fmt.Errorf`, `fmt.Sprintf`, and `maps.*`/`slices.*` functions). It never flags a dropped error from a user function (C1 is silent under `go vet`).

**Documentation/source disagreement (`errcheck`).** `README.md:140` states: "Note that by default the `fmt` package is ignored entirely, unless a regex is specified for it." At the pinned commit, `main.go` initialises the `-ignore` map empty (`ignore := ignoreFlag(map[string]*regexp.Regexp{})`, line 200). It adds only `DefaultExcludedSymbols` (line 223). That list excludes `fmt.Print`, `fmt.Printf` and `fmt.Println`, plus `fmt.Fprint*` *only* when the first argument is `*bytes.Buffer`, `*strings.Builder`, `os.Stdout` or `os.Stderr` (`excludes.go:26–41`). Execution case C5 confirms that `fmt.Fprintf(w, ...)` with an arbitrary `io.Writer` is reported by default. Basis: documentation + source + execution.

**Measured volume on a real module.** `errcheck ./...` on `golang/sync` v0.23.0 (2,421 lines across all `.go` files, counted by `wc -l`) produced 26 reports. All were in `_test.go` files (`-ignoretests` gives 0): 16 `sem.Acquire(...)`, 6 `g.Wait()`, 3 `g.Do(...)`, 2 `recover()` and 1 `resp.Body.Close()`. `-blank` added one. The run took 5.75 s wall and 275 MB max RSS with a cold analysis cache. `errcheck` on its own repository (3,427 lines excluding `testdata`) reported nothing, in 1.29 s and 147 MB. Basis: execution. This is a single small module, not a precision study.

### 3. Production checkers: configuration surface (source)

| Checker | Default severity | Marking granularity | Explicit-discard idiom | Wrappers / callbacks | Basis |
| :--- | :--- | :--- | :--- | :--- | :--- |
| rustc `unused_must_use` | Warn (`must_use.rs:45–46`); `unused_results` Allow | fn, assoc fn, trait method, ADT, trait (through `impl`/`dyn`) | `let _ = …`, `drop(…)` | fn markings lost through pointers and closures; type markings kept | source + execution |
| GCC `-Wunused-result` | on by default (warning) | function (`warn_unused_result`); function, type, constructor (`[[nodiscard]]`) | `(void)` for `[[nodiscard]]` only | fn markings lost through pointers and templates | execution |
| `errcheck` | exit status 1 on any finding | none: every call returning `error`, minus excludes | `_ =` (reported only with `-blank`) | callee type drives it; func values and closures caught | source + execution |
| Error Prone `CheckReturnValue` | `severity = ERROR` (`CheckReturnValue.java:98–102`); in `ENABLED_ERRORS` (`BuiltInCheckerSuppliers.java:729`, entry at 752) | method, class or package via `@CheckReturnValue`, with an opt-out `@CanIgnoreReturnValue`; Kotlin `MustUseReturnValues`/`IgnorableReturnValue` recognised (lines 110–113) | assign to a variable whose name starts with `unused` (documentation; `documentSuppression = false`) | method references whose result is ignored are reported (`describeReturnValueIgnored(MemberReferenceTree …)`, line 369) | source + documentation |
| clang-tidy `bugprone-unused-return-value` | warning, check opt-in | 89 default function regexes (`UnusedReturnValueCheck.cpp:51–141`) plus 5 return types (`std::error_code`, `std::error_condition`, `std::errc`, `std::expected`, `boost::system::error_code`, lines 142–147) | **`AllowCastToVoid` defaults to `false`** (line 148), so `(void)` casts are still reported by default | matches direct calls only (`callExpr(callee(functionDecl(...)))`, lines 174–185); disabled inside GNU statement expressions | source + documentation |
| `go vet unusedresult` | on in `go vet` | fixed list of pure functions plus `String()` methods | n/a | n/a | source + execution |

Error Prone also exposes `CheckReturnValue:CheckAllConstructors`, `CheckReturnValue:CheckAllMethods` and `CheckReturnValue:Packages` flags (lines 119–122). With these, the default can be inverted to "every method must have its result used unless marked ignorable". That is the same polarity as `errcheck`, but for all types. Its documented ignored contexts are Mockito `verify`/`when`, `assertThrows`, try/fail/catch, and `ExpectedException`. The clang-tidy documentation states that `cert-err33-c` is an alias of this check with a fixed, larger standard-library list.

### 4. Empirical error-handling defect studies

| Study | Corpus | Detection method | Reported defects | False positives / precision | Upstream confirmation | Basis |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Engler et al. 2001 (SOSP) | Linux 2.4.1, OpenBSD 2.8 | Belief inference: MUST beliefs for contradictions; MAY beliefs ranked by the z statistic. Template "function *f* must be checked for failure" | Derived null checker: Linux 52+102, OpenBSD 27+14, total 195 (Table 5). An earlier analysis found 79 unchecked results of 4 Linux allocators and 49 in one OpenBSD allocator | 16 (Linux), 21 (OpenBSD), 37 total: derived precision 195/232 = 84.1% (Linux 154/170 = 90.6%, OpenBSD 41/62 = 66.1%) | "Many of our bugs have resulted in kernel patches"; no count given | documentation + derived |
| Gunawi et al. 2008 (FAST, EIO) | All file systems and 3 storage drivers in Linux 2.6.15.4 | EDP: CIL-based dataflow over error-code "channels" | 1153 of 9022 error-propagating calls (13%; 12.8% derived) do not save the error code. Write errors are neglected more than read errors | 39 false positives found by manual review and excluded from the counts | Developer comments quoted, e.g. XFS "Just ignore errors at this point"; no fix count | documentation |
| Rubio-González et al. 2009 (PLDI) | Linux file systems (per title and metadata) | Interprocedural error-propagation analysis | **not examined** (full text not retrieved) | not examined | not examined | — |
| Aftandilian et al. 2012 (SCAM) | Java code base where Error Prone was developed | Compiler-integrated checks (`javac` plugin) | **not examined** (full text not retrieved) | not examined | not examined | — |
| Yuan et al. 2014 (OSDI) | 198 randomly sampled user-reported failures in Cassandra, HBase, HDFS, MapReduce and Redis; 48 (24%) catastrophic | Manual study, plus the Aspirator static checker (3 rules: empty or log-only handler, abort on over-general catch, TODO/FIXME in handler) | 92% of catastrophic failures came from incorrect handling of explicitly signalled non-fatal errors; 58% detectable by simple testing; 35% matched the 3 trivial patterns. Aspirator: 121 new bugs and 379 bad practices in 9 systems | 115 false positives: (121+379)/615 = 81.3% non-FP; bugs only 121/615 = 19.7% (derived) | 143 "fixed or confirmed by the systems' developers" | documentation + derived |
| Jana et al. 2016 (USENIX Security, EPEx) | 867,000 lines of C: OpenSSL, GnuTLS, mbedTLS, wolfSSL, httpd, cURL, Wget, Lynx, Mutt | Error specifications plus under-constrained symbolic exploration of error paths | 102 new error-handling bugs, of which at least 53 break SSL/TLS security guarantees | FP 28 of 130 reports (precision 78.5% derived); FN 20 of 960 correct cases | not stated in the abstract | documentation (abstract) + derived |

**Consequence classifications as reported.** EIO shows that unsaved error codes cause silent failures, via fault injection. Yuan et al. classify by user-visible symptom; catastrophic means most or all users see an outage or data loss. EPEx classifies security impact as broken SSL/TLS guarantees. Engler et al. treat a missing check on a routine that is almost always checked as a probable error. None of these studies measured a language attribute's effect. They measure the *population* that attributes and checkers target. Basis: derived.

### 5. Assertions: density, defects, and a published reversal

- **Kudrjavets, Nagappan and Ball** (MSR TR-2006-54, the accessible version of the ISSRE 2006 study). The subjects were two Visual Studio components, each in two releases:
  - A: 104–106 KLOC at 26.6–33.1 assertions/KLOC.
  - B: 365–372 KLOC at 37.1–39.5 assertions/KLOC.
  
  Per-file Spearman correlation between assertion density and fault density was −0.320, −0.209, −0.384 and −0.295 (p < 0.0005 to 0.002). On average 14.5% (A) and 6.5% (B) of faults were "related to assertions". The authors caution that the coefficients are "not high (around 0.3's)" and that mandating a density "may not lead to an effective use of assertions". Basis: documentation.
- **Casalnuovo et al. 2015.** Of the 100 most popular C and C++ GitHub projects, 69 used asserts (35 MLOC), and 4.6% of methods contained asserts. The paper reported that asserts have "a small (but significant) effect on reducing the density of bugs". Basis: documentation.
- **Replication (same authors).** The authors found a defect in the tool that extracted function names from `git diff` hunk headers. With exact rather than approximate extraction, 7.6% of functions contain asserts (130,928/1,717,381). In their words, "the effect of asserts has further diminished, reversed direction, and is positively correlated with defects", with logistic odds of 1.03 and much less than 1% of null deviance explained. They conclude "there is no evidence that non test asserts have an effect on defects in general." Scripts are at `caseycas/assert_replication` `50fa733c85b019733d13dbaaf37dda609d4e0776`; the raw logs are available on request only, per its README. Basis: documentation. **The original and the replication disagree. The replication supersedes the original's direction of effect.**
- **Holzmann's Power of Ten, rule 5** asks for "a minimum of two assertions per function". Its rationale is that "the odds of intercepting defects increase with assertion density". It also notes that assertions "can be selectively disabled after testing in performance-critical code". The rule is normative guidance, not measured evidence.

### 6. Ariane 501: what was discarded

Facts from the inquiry board report (Paris, 19 July 1996; Basis: documentation):

- The SRI software exception was raised "during execution of a data conversion from 64-bit floating point to 16-bit signed integer value". The value was larger than a 16-bit signed integer can represent, causing an Operand Error. The conversion "(in Ada code) [was] not protected … although other conversions of comparable variables in the same place in the code were protected."
- "Operations involving seven variables were at risk of leading to an Operand Error. This led to protection being added to four of the variables … three of the variables were left unprotected. No reference to justification of this decision was found directly in the source code."
- The reason given: "not all the conversions were protected because a maximum workload target of 80% had been set for the SRI computer". The unprotected variables were believed "physically limited or that there was a large margin of safety". For `BH` that belief was wrong, because Ariane 5's early trajectory gives "considerably higher horizontal velocity values". It was "jointly agreed not to include the Ariane 5 trajectory data in the SRI requirements and specification."
- The alignment function serves no purpose after lift-off but ran for about 40 s of flight, an Ariane 4 requirement. Both SRIs failed the same way, and the specified exception response was to shut the processor down. Break-up began at about H0 + 39 s.
- Recommendations include R5 ("Identify all implicit assumptions made by the code and its justification documents…") and R12 ("Give the justification documents the same attention as code. Improve the technique for keeping code and its justifications consistent.").

Classification (derived): this is class B in §1, not class A. No result was returned and dropped, so no unused-result mechanism in §2–§3 could have flagged it. Mechanisms that address class B include always-on range checks, which have a measured time cost; that cost was the stated reason for omission. Others are static range proofs using trajectory-derived input bounds, which require the excluded trajectory data, and keeping the "not protected because bounded" justification next to the code (R12). A unit checker (class C) would not have helped: `BH` had a consistent unit, and the failure was one of magnitude.

### 7. Annotation-free unit-inconsistency detection: phriky-units

- **Mechanism (source).** The tool reads Cppcheck dumps of ROS C++ code. It assigns units from a mapping of ROS message attributes and APIs (for example `geometry_msgs` fields) and from heuristics; the source is `cps_units_checker.py`, `symbol_helper.py` and `tree_walker.py`. Units propagate through `*` and `/` and are checked at `+`, `-`, comparisons and assignments. `phriky_units/unit_error_types.py:4–11` defines the reported classes: `VARIABLE_MULTIPLE_UNITS`, `COMPARISON_INCOMPATIBLE_UNITS`, `VARIABLE_BECOME_UNITLESS`, `FUNCTION_CALLED_WITH_DIFFERENT_UNIT_ARGUMENTS`, `VARIABLE_WITH_UNUSUAL_UNITS`, `ADDITION_OF_INCOMPATIBLE_UNITS`, `LOGICAL_OPERATOR_USED_ON_UNITS` and `UNIT_SMELL`. The README lists "Path insensitive", "No annotation burden", and "Low false positive rate (< 15% for 'high-confidence' inconsistencies)". It also states that the project has been superseded by "Phys". Requirement: Cppcheck > 1.75.
- **Corpus files.** Contrary to a single `SYSTEMS_ANALYZED` file, the pinned tree has a *directory*. `SYSTEMS_ANALYZED/ROS/SYSTEMS_ANALYZED.txt` has 213 lines, one `name, git URL` per system, and `SYSTEMS_ANALYZED/ROS/SYSTEMS_ANALYZED_IROS_4665_GIT_REPOS.txt` has 4,665 lines. At the repository root, `2017_ISSTA_GITHUB_SYSTEMS_STUDIED_DOWNLOAD.sh` contains 212 `git clone` lines, each followed by a pinned `git checkout`, and `2017_IROS_3484_GITHUB_SYSTEMS_ANALYZED.txt` has 3,484 lines. Basis: source (line counts by `wc -l`).
- **Effectiveness (dissertation §5, Table 5.3; Basis: documentation).** The corpus came from the ROS Indigo package list: 2,416 projects, 649 live Git repositories, 436 with C++, and 213 using ROS physical-unit libraries.

  | Inconsistency type | High-confidence TP / FP / precision | Low-confidence TP / FP / precision |
  | :--- | :--- | :--- |
  | Assignment of multiple units | 33 / 6 / 85% | 55 / 83 / 40% |
  | Addition of inconsistent units | 5 / 0 / 100% | 9 / 20 / 31% |
  | Comparison of inconsistent units | 2 / 0 / 100% | 0 / 4 / 0% |
  | Total | **40 / 6 / 87%** | **64 / 107 / 37%** |

  All high-confidence false positives were hand-written vector cross and outer products, where meters × meters is intended. Labels are self-assigned by the authors, and recall is unknown. One reported inconsistency was acknowledged by its developers within 90 minutes and patched within 36 hours. A larger study of 3,484 repositories (5.9 MLOC) found dimensional inconsistencies in 211 repositories (6%). The dissertation's introduction says "231 open-source" systems where §5 and Table 5.2 say 213. This report uses 213.
- **Cost (documentation + derived).** The run covered 934,124 non-blank, non-comment lines in 213 systems. It took 108 min on one core of a 2015 MacBook Pro (2.9 GHz i5, 16 GiB): 61 min for Cppcheck parsing and 47 min for analysis. That averages 31 s per system. The dissertation states "approximately 150 lines of code per second"; the derived figure is 934,124 / 6,480 s = 144 lines/s, which is consistent.

### 8. Which discarded check each mechanism can detect, at what annotation cost, with what reported precision

| Mechanism | Class A | A′ | B | C | Annotation cost | Reported precision |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `[[nodiscard]]` / `warn_unused_result` | marked callees and types | no | no | no | one attribute per function or type | not measured |
| Rust `#[must_use]` | marked fns and types; std marks `Result` and iterator adaptors | no | no | no | one attribute; `Result` free | not measured |
| `errcheck` | every call returning `error` | no (C9) | no | no | none; exclusion list | not measured (26 test-only reports on `golang/sync`; not labelled) |
| Error Prone `CheckReturnValue` | annotated, or all with flags | no | no | no | per method, class or package, or a global flag | not examined |
| clang-tidy check | 89 functions plus 5 types by default | no | no | no | regex configuration | not measured |
| EDP/EIO, error-propagation analyses | yes | yes | no | no | error-code list | EIO: 39 FPs excluded (not a rate) |
| Aspirator | handler-shape rules | partly | no | no | none | 81.3% non-FP, 19.7% confirmed-bug share (derived) |
| EPEx | error-path specifications | yes | no | no | per-function error specifications | 78.5% (derived) |
| Assertions (run-time) | no | no | yes, if present and enabled | partly (magnitude only) | per assertion | correlation −0.21 to −0.38 (Kudrjavets); no effect (Casalnuovo replication) |
| phriky-units | no | no | no | yes, for ROS-typed quantities | none | 87% high-confidence, 37% low-confidence |

Basis: derived from §2–§7.

### 9. Performance and resource footprint (L1–L6)

| Level | Item | Value | Basis |
| :--- | :--- | :--- | :--- |
| L1 authoring | Annotation burden per mechanism | §8 column; person-hours not measured | derived / not measured |
| L1 | Maintenance cost when a callee becomes must-use | not measured | — |
| L2 toolchain build | `errcheck` offline build | binary 8,316,949 bytes; build time not recorded | execution (size) / not measured |
| L3 analysis latency | GCC C23 / C++20 probe compile | 0.06 s / 0.05 s; 23 / 25 MB max RSS | execution |
| L3 | `rustc --emit=metadata` probe | 0.10 s; 112 MB | execution |
| L3 | `errcheck` probe / with `-blank -asserts` / `go vet` | 0.48 s, 62 MB / 0.62 s, 65 MB / 0.38 s, 34 MB | execution |
| L3 | `errcheck` on `golang/sync` v0.23.0 | 5.75 s, 275 MB (cold analysis cache) | execution |
| L3 | EDP on all Linux 2.6.15.4 file systems | 47 s on a 2.4 GHz Pentium 4, 512 MB | documentation (EIO Table 1) |
| L3 | Aspirator per system | < 15 s, < 1.2 GB on a 2.7 GHz Core i7 laptop | documentation (Yuan §6) |
| L3 | phriky-units | 31 s per system average; about 150 LOC/s (144 derived) | documentation + derived |
| L4 generated code | Unused-result attributes | diagnostics only; no code-generation effect intended (derived from attribute semantics); not measured | derived / not measured |
| L4 | Run-time conversion checks | an 80% SRI workload target was the stated reason for leaving conversions unprotected; overhead not quantified in the report | documentation |
| L5 certificate checking | — | not applicable: none of these mechanisms emits a checkable certificate | known not to apply |
| L6 memory | Max RSS figures | in the L3 rows | execution / documentation |

### 10. Human comprehensibility (C1) and model refinement (C2)

- **C1.** The *mental model a reader needs* is the source of most misreadings:
  - "`(void)` means deliberately discarded" is true for `[[nodiscard]]`. It is false for GCC's `warn_unused_result` and for clang-tidy's default.
  - "`_ =` silences errcheck" is true unless `-blank` is set.
  - "`#[must_use]` on a function protects every caller" is false through function pointers, closures and generic wrappers. It is also false for `Option<Result<..>>`.
  
  Each mechanism's diagnostic is local and legible: one line at the call site, plus a reason string where supported. The *absence* of a diagnostic is non-local and illegible. A reader cannot tell from a silent build whether a callee is unmarked, reached through an indirection, or excluded by name. Basis: derived from §2.
- **C2.** The orthogonal core invariant is "a value of an obligation-carrying type must be consumed or explicitly discarded". Function-level marking is a special case that does not compose with higher-order code (G6, P4, R4, R5, R7). Type-level marking composes (P5, R6, and `errcheck`'s type-keyed rule, C10/C11). The minimal uniform abstraction is therefore a must-use *type*, with one explicit discard form. Function-level marks then become sugar for returning such a type. Rust and C++ already allow both. The residual gap is that container types like `Option` do not inherit must-use-ness, which a structural rule ("must-use if any field is must-use") would close. That rule is **unsupported** by `rustc` at the pinned commit for `Option`. Classes A′, B and C are *not* expressible as must-use obligations. Folding them into one mechanism would hide their different laws: dataflow liveness of a stored error, numeric range, and dimension algebra. Basis: derived.

### 11. Validation (V1–V4)

- **V1 specification adequacy.** For unused-result checking, the "specification" is the set of marked callees. Its adequacy is checked empirically by the defect studies in §4: Engler's statistical inference of which functions *should* be checked is a specification-mining check. No mutation or kill-rate study of must-use annotations was found (**not examined**).
- **V2 checker soundness.** The execution matrices in §2 are differential tests of the documented behaviour of four implementations. They surfaced one documentation/source disagreement (`errcheck` README on `fmt`). No fuzzing of the lint implementations was done.
- **V3.** Not applicable to unused-result checking. For class B, the Ariane board's recommendation R2 (test with as much real equipment as feasible) and its note that trajectory data were excluded from the specification are hardware-in-the-loop and plant-data validation concerns.
- **V4.** Studies of human handling: Yuan et al.'s finding that 35% of catastrophic failures sit in trivially detectable handler shapes, EIO's quoted developer comments ("We can't do anything about an error here"), and the phriky developer-response survey (dissertation §5.5.3) bear on whether developers understand error obligations. No controlled study of how programmers read `(void)`, `_ =` or `let _ =` was found (**not examined**).

## Boundaries

- **Not examined:**
  - Clang's front-end `[[nodiscard]]`/`warn_unused_result` behaviour (no Clang binary).
  - MSVC `_Check_return_`/SAL.
  - MISRA C:2012 Rule 17.7 and SEI CERT ERR33-C texts. These are cited only by identifier; CERT ERR33-C is mapped to clang-tidy through the alias stated in the clang-tidy documentation.
  - Executing Error Prone or clang-tidy.
  - Running phriky-units.
  - Rubio-González 2009 and Aftandilian 2012 content.
  - Holzmann rules other than 5 and 7.
- **Unknown:**
  - Recall of every checker and analysis in §4 and §7. No study reports false negatives except EPEx's 20/960 on correct cases.
  - Whether `errcheck`'s README statement on `fmt` reflects an earlier version's behaviour. Git history was not bisected.
  - Whether GCC distributions differ in the `(void)` behaviour. Only one GCC build was run.
- **Known not to apply:** Unused-result mechanisms cannot detect a missing range check (Ariane class B) or a unit mismatch (class C). Unit inference cannot detect magnitude overflow within one unit.
- **Unsupported (by the tool at the pinned revision):**
  - `rustc` must-use linting of closures, `Res::Local`.
  - Propagation of must-use through `Option`.
  - clang-tidy matching of indirect calls.
  - The default `go vet` flagging dropped errors from arbitrary functions.
- **Stronger conclusions the evidence does not establish:**
  - That adding assertions reduces defects. The replication reversed the 2015 effect, and the Kudrjavets correlations are modest and observational.
  - That any of the precision figures transfer to other code bases. All are self-labelled by tool authors, except EPEx's FP/FN counts, whose labelling procedure was not examined.
  - That `errcheck`'s 26 reports on `golang/sync` are bugs. They were not triaged.

## Evidence

Observation date: all sources and executions were acquired 2026-11-20 (UTC).

- **rust-lang/rust** `560abf7946ae41fd210edac5dfe829d7eff86eec`:
  - `compiler/rustc_lint/src/unused.rs:17` (`pub mod must_use;`).
  - `compiler/rustc_lint/src/unused/must_use.rs`: lines 21–49 (`UNUSED_MUST_USE`, `Warn`, `report_in_external_macro`); 51–88 (`UNUSED_RESULTS`, `Allow`); 117–133 (`enum MustUsePath`); 139–281 (`is_ty_must_use`); 285 (`StmtKind::Semi`); 437–438 (closure comment); 465–469 (`is_def_must_use`).
- **kisielk/errcheck** `59d0c8437e9f9e666d6b5ab02e55a093eecf7736`:
  - `README.md:140` (the `fmt` claim).
  - `main.go:188–189` (`-blank`, `-asserts` flags), `:200` (empty ignore map), `:219–224` (exclusion wiring).
  - `errcheck/excludes.go:13–68` (`DefaultExcludedSymbols`).
  - `errcheck/errcheck.go:23–27` (`isErrorType`), `:532–588` (`Visit`: `ExprStmt`, `GoStmt`, `DeferStmt`, `ValueSpec`, `AssignStmt`, `TypeAssertExpr`, `RangeStmt`).
- **golang/tools** `7594d6faa7b96cfab035af98d21146b78e23738d`: `go/analysis/passes/unusedresult/doc.go`; `unusedresult.go:62–` (`funcs` defaults).
- **google/error-prone** `103086b59892dbbac53c573a44ecad79f9decfae`:
  - `core/.../bugpatterns/CheckReturnValue.java:98–103` (`@BugPattern`, `severity = ERROR`), `:106–122` (annotation names and flags), `:369` (member references).
  - `core/.../scanner/BuiltInCheckerSuppliers.java:729,752`.
  - `docs/bugpattern/CheckReturnValue.md`.
- **llvm/llvm-project** `0c99e3f432142834a257cd4c3067d7a69373e6d1`: `clang-tools-extra/clang-tidy/bugprone/UnusedReturnValueCheck.cpp:50–148` (options and defaults), `:172–208` (matchers); `clang-tools-extra/docs/clang-tidy/checks/bugprone/unused-return-value.md`.
- **unl-nimbus-lab/phriky-units** `16c8cdd91de0899411b139e5a94fcb4ea8104ad2`: `README.md:49–54`; `phriky_units/unit_error_types.py:1–29`; `SYSTEMS_ANALYZED/ROS/SYSTEMS_ANALYZED.txt`; `2017_ISSTA_GITHUB_SYSTEMS_STUDIED_DOWNLOAD.sh`.
- **caseycas/assert_replication** `50fa733c85b019733d13dbaaf37dda609d4e0776`: `README.md`.
- **Papers:**
  - Engler et al., DOI 10.1145/502034.502041 (§8, Table 5).
  - Gunawi et al., FAST 2008, USENIX URL above (abstract; §2.2 Table 1; §3.1.3).
  - Yuan et al., OSDI 2014 (abstract; §1; Table 2; §6, Table 9 discussion).
  - Jana et al., USENIX Security 2016 (published abstract).
  - Kudrjavets et al., DOI 10.1109/ISSRE.2006.14; numbers taken from MSR-TR-2006-54, Tables 1–2 and §6.
  - Casalnuovo et al., DOI 10.1109/ICSE.2015.88 (§I), and the replication PDF (§§III–V).
  - Ore et al., DOIs 10.1145/3092703.3092722 and 10.1145/3092703.3098219; numbers from the 2019 dissertation (§5.4–5.5, Table 5.3; §6.2).
  - Holzmann, DOI 10.1109/MC.2006.212; rule text from the author-hosted PDF (rules 5 and 7).
  - Ariane 501 report: mirror URL above; original ESA press URL recorded in `REPORT.json`.
  - DOIs were verified against Crossref metadata on 2026-11-20. Crossref lists the Holzmann author as "J. Gerald"; title and DOI match.
- **Execution** (support files are in `support/`):

  ```console
  gcc -std=c23 -c -o /dev/null wur.c        # G1..G9
  g++ -std=c++20 -c -o /dev/null nd.cpp     # P1..P8
  rustc --edition 2024 --crate-type bin --emit=metadata -o mu.rmeta mu.rs
  rustc --edition 2024 --crate-type bin --emit=metadata -W unused_results -o mu.rmeta mu.rs
  # errcheck built offline: clone kisielk/errcheck@59d0c84 and golang/{tools@v0.51.0,mod@v0.41.0,sync@v0.23.0}
  go mod edit -replace golang.org/x/tools=../tools -replace golang.org/x/mod=../mod -replace golang.org/x/sync=../sync
  GOFLAGS=-mod=mod GOPROXY=off GOSUMDB=off go build -o errcheck-bin .
  errcheck-bin ./... ; errcheck-bin -blank -asserts ./... ; go vet ./...     # in support/godemo
  errcheck-bin ./... ; errcheck-bin -ignoretests ./...                       # in golang/sync@v0.23.0
  ```

  Raw outputs are in `support/outputs.txt`.

## Revalidation

- **Rust.** Diff `compiler/rustc_lint/src/unused/must_use.rs` against `560abf79` around `is_ty_must_use` and `check_fn_must_use`. Then re-run `mu.rs`. R4, R5, R7 and R11 are the discriminating cases: if any becomes a default warning, update §2.2 and §10.
- **GCC/Clang.** Compile `wur.c` with the target compiler. G2 (`(void)` on `warn_unused_result`) and G6 (function pointer) are the discriminating lines.
- **errcheck.** Run the `demo.go` probe. C5 discriminates the README/source disagreement and C9 the A′ limitation. Also re-read `excludes.go`.
- **Error Prone and clang-tidy.** Check `BuiltInCheckerSuppliers.java` for `CheckReturnValue` in `ENABLED_ERRORS`. Check `UnusedReturnValueCheck.cpp` for the `AllowCastToVoid` default and the default list lengths (89 functions plus 5 types).
- **Studies.** These are fixed publications. Revalidation means checking for later corrections, as happened for Casalnuovo et al., before citing a direction of effect.
- **phriky-units.** The pinned repository is archived in favour of Phys. Re-running needs Cppcheck > 1.75 and the 212 pinned checkouts in `2017_ISSTA_GITHUB_SYSTEMS_STUDIED_DOWNLOAD.sh`, with fresh hand-labelling. No cheap probe reproduces the precision figures.
