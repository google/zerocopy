# Dimensions and numeric kinds as types: field evidence on unit-library adoption, unit-annotation accuracy, CamFort inference for Fortran, numeric promotion rules (Python, Julia, C, Rust), numerical-bug frequencies, and Fluctuat at Airbus

## Summary

- **UoM-library adoption is limited by awareness, learning effort, and integration, not by a shortage of libraries** (McKeever et al. 2021: ~3700 repository hits → 82 top-tier libraries; 91 surveyed practitioners; "interferes with existing code" cited by 46% of adopters and 38% of non-adopters). All analyzed libraries implement the Quantity pattern but share no core API.
- **Humans annotate units poorly:** 51% accuracy (71/138, ±8.5%) and 136.0 s mean per correct annotation; a correct suggestion raises accuracy to 73%, a wrong one drops it to 28% (Ore et al. 2018; 2021 replication with 97 developers: 51%, ~2 min). Robot code shows inconsistencies in 6% of 3,484 ROS repositories (Ore et al. 2017).
- **CamFort** solves `!= unit` comment annotations as a linear system over unit exponents (Hermite normal form) and reports "critical variables" (non-pivot columns); its authors report ~18% of declared variables need annotations. Its model has no scale factors, offsets, or numeric kinds (`int`/`real`/`nint` are `'a -> 'a`).
- **Promotion rules decide where an integer-vs-real mistake surfaces:** Python 3 and Julia make integer `/` produce a float; Julia promotes `Int64`+`Float16` to `Float16` and wraps on overflow; C silently converts (`-1 < 1u` is false; an integer quotient returned as `double` drew no GCC 15.2 warning under `-Wall -Wextra -Wconversion`); Rust rejects mixed arithmetic (E0277/E0308) but its `as` casts saturate/truncate silently, and the five numeric Clippy cast lints are allow-by-default `pedantic`, width-based, and blind to `f64::from(sum / n)`.
- **Numerical-bug frequencies** (Di Franco et al. 2017, 269 bugs in five libraries): correctness 37%, special values 28%, convergence 21%, accuracy 14%; integer-vs-real confusion is not a top-level category.
- **Fluctuat at Airbus** bounded ranges and rounding-error propagation for C basic operators of fly-by-wire software from input range/imprecision assertions, with bounds usually of the same magnitude as, and sometimes up to one order of magnitude less pessimistic than, the legacy manual analysis; DO-178B/C qualification was listed only as future work (slides; full paper not examined).
- **pint** catches dimension mismatches at run time but accepts Hz+Bq, Gy+Sv, N·m+J and rad/s+Hz, skips checks for plain 0/NaN operands, returns `False` for `1 m == 1 s`, and cost ~300–440× a float operation on the observation host.

## Applicability

The report compares mechanisms; it does not describe a combined system. Subjects fall into three groups: (a) published field studies (McKeever et al. 2019, 2021; Bennich-Björkman–McKeever 2018; Ore et al. 2017, 2018, 2021; Di Franco et al. 2017; Dietz et al. 2015; Delmas et al. 2009); (b) mechanisms pinned to revisions: CamFort 1.2.0 (`camfort/camfort`), pint (`hgrecco/pint`), Julia's promotion machinery (`JuliaLang/julia`), PEP 238 (`python/peps`) and Clippy's cast lints (`rust-lang/rust-clippy`); (c) probe toolchains: CPython 3.13.15, GCC 15.2.0 (Debian 15.2.0-14), rustc 1.102.0-nightly (rust-lang/rust commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) with clippy 0.1.101.

Version and coverage caveats: Clippy *logic* is quoted from the pinned source but Clippy *output* comes from the toolchain's bundled clippy 0.1.101, not a build of the pinned revision. pint was installed from the pinned revision (reports `0.26.3.dev31+g072281c5f`), so source and execution agree. Julia was **not installed**: all Julia statements are Basis: source. CamFort was **not built or run** (its README requires GHC 8.4–8.10, FLINT, LAPACK/BLAS, Z3 and "at least 3 GiBs of memory"): all CamFort statements are Basis: source or documentation.

Host: x86-64 Linux workstation, 96 vCPU Intel Xeon @ 2.60 GHz, LP64 (16-bit `short`, 32-bit `int`, 64-bit `long`), shared and not isolated for benchmarking; C conversion results differ on ILP32. pint used a default `UnitRegistry()` (`autoconvert_offset_to_baseunit=False`, `non_int_type=float`). Literature numbers apply to the studied populations (ROS C++ repositories, MTurk programmers on ROS snippets, five numerical libraries, Airbus control-software operators); extension beyond them is analogy and is labelled where used.

## Findings

### F1. UoM library adoption and suitability

Basis: documentation (full texts of McKeever et al. 2019 and 2021, read from the publisher PDF and the Uppsala DiVA copy; Bennich-Björkman–McKeever 2018 read as abstract only, with its numbers taken as restated by the 2019 and 2021 papers).

| Study | Method | Population / corpus | Adoption measure | Key quantitative results |
|---|---|---|---|---|
| Bennich-Björkman & McKeever, SLE 2018 | repository search and tiering (as restated in 2019/2021) | top 20 languages | presence in hosted repositories; tiering on documentation, unit coverage, ratings/popularity, recency | "close to 300 active libraries", reduced to 82 (2019, §3) |
| McKeever, Paçacı, Bennich-Björkman, MODELSWARD 2019 | design analysis of prominent libraries | Java (JSR 385, CaliperSharp), C++ (Boost.Units), Python (Astropy, pint), C# (UnitsNet, Gu.Units), others | none new | all implement the Quantity pattern, "lacking a core API, compromising both interoperability and thereby usage"; claim that further library development is not what adoption needs |
| McKeever, Bennich-Björkman, Salah, SPE 2021 | repository search; 4 interviews; survey of 91 practitioners; forum discussions | 7 hosting sites; ~65,000 non-unique hits → ~3700 checked → 586 relevant → 391 valid (296 libraries, 95 tools) → 82 top tier, 38 updated in prior 2 years | hosting-site presence, commits (~36,000 total; Astropy ~22,000), contributors (~8.3 mean, ~5.5 without Astropy); ~200 units per library on average; 30 languages, C# most common, then Python and Ruby | respondents: 67% practitioners, 25.3% technical team leads, 7.7% managers; 45 adopter respondents; reasons: lack of concern (≈33% of non-adopters; 44% of adopters cite it as a factor), effort of learning (42% adopters, 32% non-adopters), interference with existing code (46% / 38%) |

The 2021 study's suitability criteria were good documentation, many supported units and unit systems, high ratings and popularity, and recent updates. Its adoption evidence is self-report plus repository activity. Download counts and reverse-dependency counts were **not** used (no such figures appear in the text).

Its central argument is that adoption stays limited "so long as units are not part of the language, or not supported through an IDE extension". It concludes that libraries suit applications where checking at *run time* is desirable. Respondent quotes cite friction with Eigen, PETSc, deal.II, and Trilinos, and the loss of standard-layout/trivial/POD properties in `boost::units::quantity<T>`.

**Basis: derived.** These obstacles are about integration, not detection power. So the measured value of a unit checker in a codebase depends on how many interfaces carry raw `double`, a number none of the cited studies reports.

### F2. Measured prevalence of dimensional inconsistencies

Basis: documentation (abstract of Ore et al. 2017; secondary figures quoted in McKeever et al. 2021 §2).

| Source | Corpus | Detection method | Prevalence |
|---|---|---|---|
| Ore, Elbaum, Detweiler, IROS 2017 | 3,484 ROS repositories, 5.9M LOC | dimensional analysis over ROS code (per abstract; Ore et al. 2018 §3 reuses the same 3,484-repository corpus with the Phriky tool, but the 2017 tool and configuration were not confirmed from its full text) | inconsistencies in 6% (211/3,484) of repositories; "assigning multiple units to a variable" = 75% of inconsistencies; `geometry_msgs::Twist` involved in over half |
| Ore et al. (as cited in McKeever 2021) | 213 open-source C++ systems | "lightweight C++ unit inconsistency tool" (McKeever 2021 wording) | inconsistencies in 11% |
| Cooper & McKeever (as cited in McKeever 2021) | CellML model repository | validator | of invalid models, 60% had dimensionally inconsistent units |
| Antoniu et al. (as cited in McKeever 2021) | 22 published scientific spreadsheets | spreadsheet unit checker | 3 with errors |

The abstract does not describe how detections were validated or state precision/recall; the full text was not examined.

### F3. Accuracy, speed, and suggestion effects for human unit annotations

Basis: documentation (Ore et al. 2018 full text from the first author's site; Ore et al. 2021 abstract only).

- **Design (2018).**
  - Code: 20 artifacts randomly drawn from 31,928 files that Phriky flags as unit-bearing. These come from a corpus of 797,410 C++ files in 3,484 ROS repositories.
  - Ground truth: each artifact was reviewed by at least two authors and cross-checked twice.
  - Subjects: 71 MTurk subjects, each given 10 questions.
  - Treatments: T1 none, T2 correct suggestion, T3 incorrect suggestion.
  - Answer menu: a drop-down of the 19 most common robot-code units, plus NO UNITS and OTHER.
- **Results (2018).**
  - Accuracy (T1): 71/138 = 51% (±8.5%, 95% Agresti–Coull).
  - Time: mean 136.0 s, median 108.6 s per correct annotation.
  - Experience: no significant effect (5+ years: 56%, others 50%; p = 0.554).
  - Correct suggestion: risk ratio of a wrong answer 0.40 (95% CI 0.24–0.66).
  - Incorrect suggestion: risk ratio 2.66 (1.62–4.39); 31% of wrong T3 answers "took the bait".
  - Most common wrong answer: NO UNITS (T2: 14/39; T3: 28/98).
  - Tool comparison: Phriky 1.0.0 made a suggestion for 7/20 variables, 5 correct and 2 incorrect.
- **2021 (TOSEM, abstract).**
  - 97 developers, 20 artifacts.
  - About 51% accuracy and about 2 minutes per correct annotation.
  - A single suggestion has a strong effect, whether correct or incorrect. Three suggestions keep the benefit without the negative effect and add no time penalty.
  - Identifier names and reasoning about operations are the main clues subjects use.

**Basis: derived.** Annotation accuracy is about 51%, and a wrong suggestion is worse than none. So an annotation-heavy checker inherits a large error rate at its *inputs*. A checker that infers most units from a few annotations, as CamFort does (F4), reduces the number of human decisions but does not make each decision more accurate.

### F4. CamFort: inference-based units checking of legacy Fortran

Basis: source (`camfort/camfort@fda0f101c00bf21446433647612a112c1601a976`) + documentation (Contrastin et al. 2016 accepted manuscript; Orchard et al. 2015 abstract).

**Annotation language.** Annotations are Fortran comments, so compilers ignore them. The grammar is in `src/Camfort/Specification/Units/Parser.y`:

- Lines 41–43 define two statement forms. An assignment is `unit UEXP [:: ids]`. An alias is `unit :: id = UEXP`.
- Lines 53–58 accept `1`, `(1)`, or `()` for unitless, plus `record(...)` for derived types.
- Lines 67–81 allow products by juxtaposition or `*`, quotients with `/`, and powers `**n` or `**(p/q)` (rational powers, line 81).
- Unit names are opaque atoms. The lexer lower-cases the whole annotation (line 163: `tokens <- lexer $ map toLower src`), so `Mm` and `mm` are the same atom.
- Identifiers may contain `'`, `_`, and `-` after the first letter (line 151 accepts any character that is alphanumeric or one of `'`, `_`, `-`). By the lexer rule, `m-1` is therefore one atom, not m⁻¹ (Basis: source, not executed).
- Polymorphic units are written `'a` (`samples/units/poly1.f90` lines 11–20).

**Inference.**

- `InferenceBackend.hs` builds a coefficient matrix over unit exponents (`constraintsToMatrix`). It reduces groups of related columns to Hermite normal form through FLINT, in parallel (`splitNormHNF`, lines 136–145, `map (first Flint.normHNF) (splitMat unsolvedM)`).
- Inconsistency is detected when concrete units force unequal coefficients on an implicit abstract unit, or when a parametric unit is assigned to a monomorphic literal (`detectInconsistency`, lines 89–96; `mustBeUnitless`, lines 100–119).
- Critical variables are columns that are not a pivot after `rref` (lines 570–577: `criticalIndices = A.indices colA \\ uncriticalIndices`, where `uncriticalIndices = mapMaybe (findIndex (/= 0)) $ H.toLists solvedM`).
- `rref` operates on `H.Matrix Double` (line 415).
- `doc/units.txt` (lines 33–61) records that an earlier `linearSolveSVD` route produced real-valued solutions for under-constrained systems.

**Literals.** There are three modes, with Mixed the CLI default (`src/Main.hs` lines 360–366):

- Unitless: every literal is unitless.
- Poly: every literal is polymorphic.
- Mixed (`Analysis.hs` lines 318–343): `0` and `0.0` are fully polymorphic, and other literals are monomorphic. A constant multiplier in `*` or `/` is treated as unitless (lines 344–357).

Contrastin et al. justify the zero exception: zero is the additive identity, so `x + 0` is unit-correct for any unit. pint has the same exception (F5).

**Intrinsics.** `Analysis.hs` lines 1011–1091 (`intrinsicUnits`) give:

- `sqrt :: 'a**2 -> 'a` (line 1057).
- `exp`/`log`/`sin` take and return unitless values (lines 1060–1070).
- `atan2 :: ('a,'a) -> unitless` (line 1082).
- Every kind-conversion intrinsic maps `'a -> 'a`: `int` (1033), `nint`/`real`/`float` (1049–1051), `dble` (1026). Units and numeric kind are therefore orthogonal in CamFort; an `int(x)` truncation is invisible to it.
- `mod`, `modulo`, `amod`, and `dmod` give the second argument an independent unit variable `'b` (lines 1045–1048; line 1045: `("mod", (UnitParamEAPAbs ("'a", "'a"), [UnitParamEAPAbs ("'a", "'a"), UnitParamEAPAbs ("'b", "'b")]))`). By this table, `mod(x [m], y [s])` is accepted (Basis: source; this is a design permissiveness, not a reported bug).

**What the model cannot express (Basis: source + derived).**

- There are no conversion factors. `m` and `km` are unrelated atoms unless the user writes a scaling variable with unit `km/m`. Contrastin et al. state that implicit conversion "does not fall into the scope of the CamFort project".
- There are no offsets. `samples/units/fahrenheit.f90` writes `f = s * c + a` with `!= unit(fah / cel) :: s`. The checker can only require `a` to have unit `fah`; whether a value is an absolute temperature or a temperature difference is not represented.
- The checker is static and only as good as the annotations.

**Commands and reported results.**

| Item | Value | Basis |
|---|---|---|
| Commands at pinned revision | `units-suggest`, `units-check`, `units-infer`, `units-summarise` (aliases include `units-compile`), `units-synth` (`src/Main.hs` 514–528); exit code 1 on inconsistency (`Consistent.hs` 50–52) | source |
| Commands in 2016 article | `camfort units`, `camfort criticalUnits` (older spelling) | documentation |
| Written vs. inferred | "a typical program requires roughly only 18% of its declared variables to be annotated before CamFort can automatically infer the rest" (Contrastin et al. 2016, citing Orchard et al. 2015) | documentation (secondary; Orchard full text not examined) |
| Example bug found | kinetic energy computed as `half * mass * velocity` instead of velocity²: "cannot match units 'kg m**2/s**2' and 'kg m/s'" | documentation |
| Inconsistency classes in the test fixtures | distinct units added (`example-inconsist-1.f90`: `z = x + y` with `x` in s, `y` in m); non-zero literal given a parametric unit (`literal-nonzero-inconsist1..5.f90`); recursive multiplication (`inconsistRecMult.f90`); literal in polymorphic function (`inconsistLitInPolyFun.f90`) | source (fixtures not executed) |
| Bugs found in real scientific codes | not examined (Orchard 2015 full text unavailable to this investigation) | — |

### F5. pint: what run-time quantity checking catches

Basis: source (`hgrecco/pint@072281c5f1b3d5fe30d097cbb0791be03ee24d45`) + execution (`support/pint_probe.py`, CPython 3.13.15).

| Probe | Result | Governing source |
|---|---|---|
| `1 m + 1 s`, `1 m < 1 s`, `(1 m).to('kg')` | `DimensionalityError` | `quantity.py` 847–850; `compare` 1744–1747 |
| `1 m + 1 ft` | `1.3048 meter` (converted to the left operand's unit) | `quantity.py` 863–865 |
| `1 Hz + 1 Bq` | `2 hertz` | `default_en.txt` 230 `hertz = 1 / second`, 378 `becquerel = counts_per_second`, 118 `count = []` |
| `1 Gy + 1 Sv` | `2 gray` | `default_en.txt` 381–382 (both `joule / kilogram`) |
| `1 N*m + 1 J` | `2 newton * meter` | same dimension |
| `1 rad/s + 1 Hz` | `2.0 radian / second` (angular vs. cyclic frequency: a 2π error) | `default_en.txt` 116 `radian = [] = rad`, 132 `turn = 2 * π * radian ... = cycle` |
| `1 rad + 1` | `2 dimensionless` | radian is dimensionless |
| `math.sin(Q_(90,'deg'))` | `1.0` (degree→radian conversion applied by `__float__`) | `quantity.py` 648–651 |
| `1 m + 0`, `1 m + nan` | accepted, unit kept | `quantity.py` 798–802: "If the other value is 0 or NaN (but not a PlainQuantity) do the operation without checking units." |
| `1 m + 1` | `DimensionalityError` | `quantity.py` 807–808 |
| `1 m == 1 s`; `0 m == 0 s` | `False`; `False` (no exception) | `__eq__` 1685–1691, 1702–1703 (`except DimensionalityError: return bool_result(False)`) |
| `float(1 m)` | `DimensionalityError` | `quantity.py` 648–651 |
| `(1 m).magnitude + 1` | `2` (unit discarded) | escape hatch |
| `10 degC + 10 degC`; `2 * 10 degC` | `OffsetUnitCalculusError` | `quantity.py` 912; `nonmultiplicative/registry.py` 47 default `autoconvert_offset_to_baseunit=False` |
| `10 degC - 5 degC` | `5 delta_degree_Celsius` | `quantity.py` 867–877 |
| `(10 degC).to('degF')` | `49.999999999999936 degree_Fahrenheit` | affine conversion in binary floating point |
| `Q_(7,'m') / 2`; `Q_(7,'m') // Q_(2,'m')`; `Q_(7,'m') // 2` | `3.5 meter`; `3 dimensionless`; `DimensionalityError` | `_truedivide_cast_int` 1252–1257 (int/int → `non_int_type`); `__floordiv__` 1351–1358 |

**Classification (Basis: derived).**

- pint excludes *dimension* mismatch and ambiguous offset arithmetic, but only on executed paths and only at run time.
- It cannot exclude:
  - same-dimension, different-kind confusions: Hz/Bq, Gy/Sv, torque/energy, rad/s vs Hz;
  - any error once `.magnitude` or `m_as` is taken;
  - plain-zero/NaN additions;
  - equality tests across dimensions, which return `False` rather than raising.
- These are exactly the cases a dimension-only static checker such as CamFort also misses, except for the run-time-only issues.
- Numeric kind is preserved independently: integer magnitudes stay `int` until a true division.

### F6. Promotion and conversion rules as defect sources

Basis: normative (PEP 238) + source (Julia, Clippy) + execution (Python, C, Rust probes) + documentation (Dietz et al. 2015 §3.2 for C rules; ISO C text itself not examined).

**Python (PEP 238, `python/peps@4434e728a7db24540d581f52e96570ca1230356e`, `peps/pep-0238.rst`).**

- The motivation (lines 15–20, 52–73) is that classic `/` "returns the floor of the mathematical result of division if the arguments are ints or longs". This makes "expressions expecting float or complex results error-prone when integers are not expected but possible as inputs". The PEP calls the problem "unique to dynamically typed languages" because a C prototype would convert the argument (lines 61–66).
- `x//y` is floor division with result type equal to the coerced common type (lines 268–289). True division of ints converts to float, so `2/1` gives `2.0` (lines 298–300), and long true division "retains no more than 53 bits of precision" (lines 310–314).
- For representable quotients, there are no more than 3 rounding errors, and silent underflow to 0.0 (lines 390–395).
- Migration: `from __future__ import division`, the `-Q old|warn|warnall|new` option (lines 238–254), and the tools `Tools/scripts/finddiv.py` and `fixdiv.py`, which work "based on run-time analysis" (lines 453–457).
- The FAQ warns that floor division rounds toward −∞ while `int()` truncates toward zero (lines 427–437).

Probe (`support/py_division_probe.out`):

- `7/2 = 3.5`, `-7//2 = -4`, `int(-7/2) = -3`, `-7 % 2 = 1`.
- `(2**53+1)/1 = 9007199254740992.0`, whereas `(2**53+1)//1` is exact.
- `(10**400)/(10**399) = 10.0`, but `(10**400)/1` raises `OverflowError` and `1/(10**400) = 0.0`.

**Julia (`JuliaLang/julia@8dda794eec3571f4776fac724629459301e3ecfd`).**

- Mixed arithmetic dispatches through `promote` (`base/promotion.jl` 464–467: `+(x::Number, y::Number) = +(promote(x,y)...)`; comparisons 526–528).
- `promote_type` tries `promote_rule` in both orders (346–354). With no rule, it falls back to `typejoin` (373–376), and `promote` then raises "promotion of types ... failed to change any arguments" (453–461).
- The docstring states that "some loss is tolerated" and gives `promote_type(Int64, Float16) == Float16` and `promote_type(Int8, UInt16) == UInt16` (300–327). The rules behind these are in `base/float.jl` 243–263, where Float16/32/64 win over every integer type.
- Integer `/` returns float: `base/int.jl` 101–103, `(/)(x::BitInteger, y::BitInteger) = float(x) / float(y)`.
- Fixed-width `+ - *` wrap (`int.jl` 87–89: `add_int`, `sub_int`, `mul_int`), but `div` is checked (359–361).
- With mixed signedness at the same width, unsigned wins for arithmetic (`int.jl` 821–826: `promote_rule(::Type{UInt64}, ::Type{Int64}) = UInt64`). Comparisons, however, bypass promotion and are value-correct: `<(x::BitSigned, y::BitUnsigned) = !(y <= x)` and, for `(x::BitUnsigned, y::BitSigned)` of equal or greater width, `(y >= 0) & $op(x, unsigned(y) % typeof(x))` (`int.jl` 581–593).
- Float→integer *constructors* throw `InexactError` unless the value is integral and in range (`float.jl` 896–904); `unsafe_trunc` is the unchecked path (406–415).
- Execution: not performed (Julia not installed).

**C (rules as summarized by Dietz et al. 2015 §3.2, exercised with GCC 15.2.0).**

- Operands narrower than `int` are promoted to `int`. Mixed signedness converts to unsigned unless the signed type can represent all the unsigned type's values.
- Dietz et al. show that `long a = -1; unsigned b = 1; a > b` returns 0 on x86-64 but 1 on x86 (ILP32).

Probe (`support/c_conversions_probe.*`, `-O0` and `-O2` agree):

- `(-1 < 1u) = 0` drew the only compile-time diagnostic (`-Wsign-compare`). `(-1L < 1u) = 1` on LP64.
- `(unsigned short)65535 * 65535` drew a UBSan "signed integer overflow: 65535 * 65535 cannot be represented in type 'int'" at run time, with no compile-time warning.
- `double average_int(int s, int n) { return s / n; }` gives `3.000000` for (7,2) with **no warning** under `-Wall -Wextra -Wsign-compare -Wconversion`. The int→double conversion is value-preserving, so `-Wconversion` is silent about the integer quotient.
- `(float)16777217 = 16777216.0`, `0u - 1 = 4294967295`, `(uint8_t)(200+100) = 44`.

**Rust (rustc 1.102.0-nightly; clippy source at `rust-lang/rust-clippy@663e7ca4f8e69efa893b816140889b4a40c65f74`).**

- Mixed arithmetic does not compile:
  - `1u32 + 1.0f64` gives E0277 "cannot add `f64` to `u32`".
  - `let b: u64 = 1u32` gives E0308.
  - Returning `sum / n` (u32) from an `f64` function gives E0308, and rustc suggests `(sum / n).into()`. Note that the suggestion keeps the *integer* division.
- Explicit `as` is silent:
  - `300.7f64 as u8 = 255`, `-1.5f64 as u8 = 0`, `NAN as i32 = 0`, `1e20 as i64 = i64::MAX` (saturating).
  - `300i32 as u8 = 44`, `u32::MAX as i32 = -1`.
  - `16777217i32 as f32 = 16777216.0`.
  - `(i64::MAX as f64) as i64 == i64::MAX` is `true`, because saturation masks the rounding to 2⁶³.
- Checked alternatives: `u8::try_from(300i32) = Err(PosOverflow)`, `200u8.checked_add(100) = None`.

**Clippy lint logic.**

- `CAST_POSSIBLE_TRUNCATION`, `CAST_POSSIBLE_WRAP`, `CAST_PRECISION_LOSS`, `CAST_SIGN_LOSS`, and `CAST_LOSSLESS` are all declared `pedantic` (`clippy_lints/src/casts/mod.rs` lines 239, 300, 336, 362, 412). They are therefore off unless enabled.
- `CAST_NAN_TO_INT` is `suspicious` (261).
- Precision loss fires iff the source is `isize`/`usize` or `from_nbits >= to_nbits` (`cast_precision_loss.rs` line 20). So `i32→f32` and `i64→f64` lint, but `i32→f64` does not.
- Truncation is width-based, with a syntactic reduction for `&`, `%`, `>>`, `/`-by-constant, `min`, `clamp`, and `signum` (`cast_possible_truncation.rs` 29–84). For example, `(x & 0xff) as u8` is not linted.
- Float→int always lints (158–159), and `f64→f32` lints (162–163).
- `CAST_LOSSLESS` fires for int→wider-int with no signed→unsigned conversion and no `isize`/`usize`, and for int→float when `from_nbits < to_nbits` (`cast_lossless.rs` 89–105).

Probe (`support/clippy_casts_probe.out`): 9 warnings, one per intended case. `masked` drew no warning. `fn int_div_then_float(sum: i32, n: i32) -> f64 { f64::from(sum / n) }` returns `3` for (7, 2) and drew **no lint at all**.

**Comparison table (Basis: derived from the above).**

| Rule | Python 3 | Julia | C | Rust (rustc) | Rust + pedantic clippy |
|---|---|---|---|---|---|
| int `/` int | float (true division) | float | int (truncates toward 0) | int (truncates toward 0) | int; no lint |
| mixed int+float | float (implicit) | promote (may *narrow* to Float16) | implicit to float type | compile error | compile error |
| mixed signedness, same width | n/a (unbounded int) | arithmetic: unsigned wins; comparison: value-correct | unsigned wins (`-1 < 1u` false) | compile error | compile error |
| fixed-width overflow | n/a (int unbounded); float→`OverflowError` on int→float | wraps | signed: UB (UBSan flags at run time); unsigned: wraps | `200u8 + 100`: panics without `-O`, gives 44 with `-O` (`support/rust_overflow_probe.out`) | — |
| float→int conversion | `int()` truncates; NaN→`ValueError`, inf→`OverflowError` | constructor throws `InexactError` unless exact | out-of-range case not examined | `as` saturates, NaN→0 | `cast_possible_truncation` warns |
| int→float precision | above 2⁵³ rounds | silent (tolerated by design) | silent | `as` rounds silently; `From` only where exact | `cast_precision_loss` warns by width |

### F7. Which defect classes each rule set admits, rejects, or warns about

Basis: derived from F5, F6, Dietz et al. 2015 (Table II taxonomy; Table III SPEC CINT2000 wraparounds), and Di Franco et al. 2017 (categories, from the authors' ASE 2017 slides).

Dietz et al. classify integer overflow by intent (intentional/unintentional) × definedness (UB / defined).

- In SPEC CINT2000 they found 219 static overflow sources in 8 of 12 benchmarks: 148 unsigned and 71 signed (32%).
- The most common uses were hashing (128), overflow checks requiring `-fwrapv` (37), bit manipulation (25), and random-number generation (6).
- "the vast majority ... were not bugs". Several rows are labelled "Type promotion" or "Type promotion artifact" (for example `164.gzip trees.c(552:25)`).
- Dietz et al. also count *value-losing conversions* (e.g. a truncating `int`→`short` cast) as "overflow errors".

| Defect class | Python 3 | Julia | C | Rust | Clippy (pedantic) | pint | CamFort | Fluctuat-style analysis |
|---|---|---|---|---|---|---|---|---|
| integer division where real was meant | excluded for `/` (PEP 238) | excluded for `/` | admitted, no warning | admitted if written `a / b` on ints; mixing types rejected | not detected | not detected (kind orthogonal) | not detected (`int`/`real` are `'a→'a`) | value-range effects visible only if the analysis is set up to compare against the intended real formula (not examined) |
| mixed signed/unsigned comparison | n/a | excluded (dedicated value-correct methods, `int.jl` 581–593); mixed-sign *arithmetic* still yields unsigned | admitted; `-Wsign-compare` warns | rejected | n/a | n/a | n/a | not examined |
| unintentional signed overflow | n/a | admitted (wraps) | UB; UBSan detects at run time | panics without `-O`, wraps with `-O` (probed on `u8`) | n/a | n/a | n/a | range analysis can flag overflow (claimed in slides: "freedom from run-time errors") |
| truncating int→narrower-int conversion | n/a | not examined (int→int constructors not inspected) | admitted silently | `as` silent; `try_from` checked | `cast_possible_truncation` | n/a | n/a | not examined |
| float→int out of range | `OverflowError`/`ValueError` | `InexactError` | not examined | saturates silently | warns on every float→int `as` | n/a | n/a | range bounds |
| int→float precision loss | silent above 2⁵³ | silent | silent | silent with `as` | `cast_precision_loss` | n/a | n/a | rounding-error bounds |
| dimension mismatch | n/a | n/a | n/a | n/a | n/a | run-time error | static error | not in scope |
| same-dimension kind confusion (Hz/Bq, torque/energy) | n/a | n/a | n/a | n/a | n/a | admitted | admitted unless distinct user atoms are declared | not in scope |

**Di Franco et al. categories mapped (Basis: derived).**

- **Accuracy bugs (38).** Causes: insufficient precision types, buggy arithmetic expressions, ill-conditioned problems. These are the target of rounding-error analysis such as Fluctuat, and are invisible to unit checkers and promotion rules, except that "insufficient precision type" overlaps the Float16/float32 promotion choices above.
- **Special-value bugs (76).** Missing NaN checks, overflow/underflow. Range analysis can bound overflow; NaN propagation is not prevented by any promotion rule examined. pint even skips unit checks for NaN operands.
- **Convergence bugs (56).** These require algorithmic knowledge; none of the mechanisms examined addresses them.
- **Correctness bugs (99).** Typographical errors in formulas, approximations used outside their domain, and compiler optimizations violating mathematical semantics. Unit checkers can catch the subset of formula typos that change dimension: CamFort's kinetic-energy example is one. Domain errors and optimization-induced errors are out of their scope.

### F8. Di Franco et al.: numerical bug frequencies

Basis: documentation (abstract; authors' ASE 2017 slides; the paper's full text not examined).

- The corpus was 17,089 issues, filtered or sampled to 828 inspected, of which 269 (32%) were numerical.
- Selection keywords included nan, overflow, underflow, precision, roundoff, truncation, cancellation, and accuracy.

| Library | Accuracy | Special values | Convergence | Correctness | Total |
|---|---|---|---|---|---|
| NumPy | 5 | 16 | 0 | 3 | 24 |
| SciPy | 8 | 27 | 6 | 30 | 71 |
| Elemental | 0 | 0 | 0 | 9 | 9 |
| LAPACK | 11 | 11 | 11 | 9 | 42 |
| GSL | 14 | 22 | 39 | 48 | 123 |
| **Total** | **38 (14%)** | **76 (28%)** | **56 (21%)** | **99 (37%)** | **269** |

The column and row sums were checked arithmetically (e.g. 38+76+56+99 = 269). The slides report "no indication during manual inspection that users or developers use tools for bug finding or bug fixing". They name differential comparison against less efficient implementations as the most common way bugs are exposed.

### F9. Fluctuat on Airbus avionics software

Basis: documentation (Springer abstract; authors' FMICS 2009 slides; paper full text not examined).

- **Software analysed.** C basic operators in the library used by code generated from SCADE/Simulink models for fly-by-wire computers. Examples include polynomial approximations (an arctangent), interpolators, digital filters, signal integrators, and a Householder square-root scheme.
- **Properties established.** Fluctuat establishes, for each operator:
  1. input ranges that guarantee absence of run-time errors;
  2. bounds showing the operator "can introduce only negligible rounding errors";
  3. bounds showing it "cannot significantly amplify errors on inputs";
  4. "in some cases, a functional proof of the underlying algorithm ... (in real and floating-point numbers)".
- **Method.** Abstract interpretation with an affine-arithmetic (zonotope) domain. Each variable has a real value plus error terms, and errors are decomposed by source line. The specification is the real-number semantics and the implementation is IEEE 754.
- **Assumptions supplied.** Assertions on input ranges, input imprecision, and the range of a value's gradient. Settings are parameterizable for precision/time trade-offs, domains, and architecture-dependent features.
- **Challenges named.**
  - Very large input ranges.
  - Implicit unbounded loops in digital filters.
  - Bitwise tricks, such as an int-to-double conversion that assembles a double from 32-bit words (`0x43300000` and `0x80000000 ^ i`) and subtracts a constant, in order to avoid compiler-generated constant sections. The motivation is WCET, determinism, and traceability.
- **Comparison with the legacy method.** Faster and easier. Bounds were "usually of the same magnitude" and "sometimes much less pessimistic (up to one order of magnitude)".
- **Scale claimed for the tool.** Code "of size up to about 50000 LOCs (on laptop PCs 1Gb)".
- **Certification role.** The slides list Airbus's existing certification-credit uses of StackAnalyzer, aiT WCET, and CAVEAT. For Fluctuat they list "qualification as a verification tool wrt. DO-178B/C?" under future work. Certification credit for Fluctuat is therefore **not** claimed in the material examined.
- **Handling of false alarms.** Unknown (not described in the abstract or slides).

### F10. Performance and resource footprint (L1–L6)

| Level | Measured / quoted value | Basis |
|---|---|---|
| L1 authoring | correct unit annotation: mean 136.0 s, median 108.6 s, 51% accuracy (Ore 2018); ~2 min, 51% (Ore 2021); CamFort: ~18% of declared variables need annotations (Contrastin 2016); Airbus/Fluctuat: "faster & easier" than manual analysis, no time figure | documentation |
| L1 repair/migration | PEP 238 migration via `finddiv.py`/`fixdiv.py`, transition ≥2 years planned; effort figures **not measured** | normative |
| L2 toolchain build | CamFort: "at least 3 GiBs of memory" (README); Julia/pint/clippy build **not measured** | documentation |
| L3 analysis latency | rustc probe compile 0.09–0.13 s, peak RSS ≈124 MiB; GCC probe 0.05–0.06 s, ≈27 MiB; `cargo clippy` on the 1-file probe crate 0.07–0.12 s, 80–106 MiB (`/usr/bin/time`, two runs). CamFort and Fluctuat analysis times **not measured** | execution |
| L4 run-time overhead | pint: add 8.7–9.7 µs/op vs float 22–26 ns (≈379–395×); mul 9.0–9.5 µs vs 21–30 ns (≈313–435×); `to('m')` 11.2–13.2 µs (two runs, `timeit` best-of-5 × 200,000). IOC (C overflow checker) on SPEC CPU2006: geometric mean 20.0% (undefined checks only) to 28.8% (all checks) (Dietz 2015). Julia v0.6.2: 0.9×–6.1× of optimized C on 10 small benchmarks (Bezanson 2018 author copy). CamFort: zero run-time overhead by construction (comments only) | execution + documentation |
| L5 checker speed | Fluctuat: whole codes up to ~50 kLOC (no time given); others **not measured** | documentation |
| L6 memory | pint: peak RSS 26.8–28.2 MiB after `import pint` + `UnitRegistry()` vs 7.9 MiB bare interpreter; import 124–154 ms; registry construction 133–357 ms. Fluctuat: "laptop PCs 1Gb" | execution + documentation |

All execution numbers come from one shared x86-64 host. They are indicative, not benchmarks of record.

### F11. Comprehensibility (C1) and conceptual simplicity (C2)

**C1.**

- The Ore studies measure *human* comprehension directly, and it is poor: 51% accuracy, with no experience effect. The diagnostic content of a unit error therefore depends on annotations that are often wrong.
- CamFort's diagnostics name the conflicting units (`'kg m**2/s**2' and 'kg m/s'`), which keeps checking local. The critical-variables report pushes users toward the minimal set of decisions, but each decision is still one of the 51%-accurate kind.
- pint's failures are local exceptions on the executed path. Its silent cases need non-local knowledge of registry definitions: radian dimensionless, Bq ≡ Hz, the zero/NaN rule, and `==` returning `False`.
- C's conversions require remembering the rank/signedness table and the data model. GCC flagged one of the three conversion hazards probed.
- Rust removes the implicit layer entirely. The burden moves to choosing between `as`, `From`, and `TryFrom` at each site, and rustc's own fix-it for E0308 preserves an integer division.

**C2 (Basis: derived).** Two orthogonal invariants recur: the *dimension* (an element of a free abelian group of base units) and the *numeric kind* (exact integer vs. rounded real, plus width).

- Every mechanism examined enforces at most one of them. CamFort and pint enforce dimension; PEP 238, Julia, Rust, and clippy govern kind; Fluctuat bounds the real-vs-float gap.
- The two places where special cases appear are the same in the two unit systems: zero is unit-polymorphic in both CamFort (Mixed mode) and pint (`zero_or_nan`), and offsets need separate machinery (pint's delta units; absent in CamFort).
- A minimal model that makes these ordinary would type a quantity by (dimension, kind, affine-vs-linear), with conversions as explicit morphisms. This is a design hypothesis, not evaluated here.
- The obstacles in F1 (interoperability with untyped numeric libraries) suggest the cost would move to adapter boundaries rather than vanish.

### F12. Validation of the mechanisms (V1–V4)

| Mechanism | V1 spec adequacy / non-vacuity | V2 checker or lowering soundness | V3 platform / physical effects | V4 human or plant validation |
|---|---|---|---|---|
| CamFort | negative fixtures that must be rejected (`tests/fixtures/Specification/Units/*inconsist*`); Hspec suites `tests/Camfort/Specification/Units/**` (not executed) | linear-algebra backend has SBV and FLINT variants (`InferenceBackendSBV.hs`, `InferenceBackendFlint.hs`); cross-validation **not examined** | n/a (static, comment-only) | annotation accuracy is the Ore-measured weak point; no CamFort-specific user study found |
| pint | 46 test modules under `pint/testsuite/` (count only; not run); our probe acts as a litmus suite | n/a | float rounding in affine conversion (`49.999999999999936 °F`) | none found |
| PEP 238 | run-time warning modes `-Qwarn/-Qwarnall` and `fixdiv.py` patches drawn from run-time observation | n/a | silent underflow to 0.0 is documented | migration designed around educators and library authors; no measured study |
| Julia promotion | `jldoctest` examples in `promotion.jl` docstrings (not run) | not examined | Float16 promotion is a precision choice, not hardware | none |
| Clippy casts | UI tests `tests/ui/cast*.rs` (13 files at pinned revision; not run) | lints are syntactic on width; no semantic intent check | target pointer-width caveats in lint messages | none |
| IOC (Dietz) | manual triage of every SPEC CINT2000 overflow | found undefined overflows in SQLite, PostgreSQL, LLVM, OpenSSL, and others | compiler optimizations breaking UB-dependent code is the cited risk | n/a |
| Fluctuat | real-number semantics as specification | soundness relative to the IEEE 754 model; architecture parameters exist | not examined (x87/FMA specifics not described) | compared against Airbus's legacy manual analyses |
| Ore studies | 2-author ground truth, cross-checked twice | n/a | n/a | directly measures human mental models (V4) |

## Boundaries

- **Not examined (full text).**
  - Orchard et al. 2015: abstract only. The 18% figure comes via Contrastin et al. 2016. The paper's real-code results, polymorphism details, and timings are not reproduced here.
  - Ore et al. 2017 and 2021: abstracts only.
  - Bennich-Björkman & McKeever 2018: abstract only; numbers restated from the 2019 and 2021 papers.
  - Di Franco et al. 2017: abstract and authors' slides only, so per-category fix strategies and symptom tables are not reproduced.
  - Delmas et al. 2009: abstract and authors' slides only, so analysis times, specific error bounds, and the handling of false alarms are unknown.
- **Not examined (execution).**
  - CamFort was not built or run. Its behavior on `fahrenheit.f90`, `m-1` lexing, `mod` units, and the fixtures is derived from source.
  - Julia was not installed, so all Julia behavior is source-derived.
  - Rust overflow was probed only for `u8` addition with and without `-O`; profile settings such as `overflow-checks` in Cargo were not examined.
  - C float→int out-of-range conversion was not probed.
  - The clippy run used the toolchain's clippy 0.1.101, not a build of the pinned revision.
- **Not examined (normative text).** The ISO/IEC 9899 standard itself; C rules were taken from Dietz et al. §3.2 and observed behavior. Fortran's implicit-typing rules were not examined.
- **Unknown.**
  - Whether pint's skipping of the unit check for plain zero/NaN has caused field defects.
  - How often same-dimension kind confusions (Hz/Bq, rad/s vs Hz) occur in practice. No cited study measures them.
  - The precision/recall of Phriky-based prevalence figures.
- **Known not to apply.**
  - Python and Julia `/` cannot produce integer truncation for built-in integers.
  - Rust cannot implicitly mix integer and float operands.
  - Dimension checkers cannot detect numeric-kind defects, and promotion rules cannot detect dimension defects.
- **Unsupported.**
  - CamFort: unit conversion factors and offsets ("does not fall into the scope of the CamFort project").
  - pint (default registry): arithmetic on absolute offset temperatures, which raises `OffsetUnitCalculusError`.
  - Clippy: cast lints for `f16`/`f128` (`FIXME` in `cast_precision_loss.rs` line 14 and `cast_lossless.rs` line 98).
- **Attractive conclusions not established.**
  - That unit checkers would have prevented a given share of the 269 Di Franco bugs; no such mapping was measured.
  - That 51% annotation accuracy transfers to scientific Fortran programmers; the subjects were MTurk workers on ROS C++.
  - That Fluctuat analyses carry DO-178 certification credit.
  - That the pint overhead ratio holds on other hosts or for array magnitudes, which were not measured.
  - That integer-versus-real confusion is rare; it is simply not a top-level category in the one large study examined.

## Evidence

All evidence was acquired on 2026-11-20.

**Repositories (GitHub; SHAs re-resolved on the observation date via the GitHub commits API).**

- `camfort/camfort` @ `fda0f101c00bf21446433647612a112c1601a976` (HEAD on the observation date; `camfort.cabal` version 1.2.0):
  - `src/Camfort/Specification/Units/Parser.y` 41–89, 151, 163
  - `src/Camfort/Specification/Units/Analysis.hs` 318–357, 1011–1091
  - `src/Camfort/Specification/Units/InferenceBackend.hs` 89–119, 136–145, 414–416, 568–578
  - `src/Camfort/Specification/Units/Analysis/Criticals.hs` 10–12, 101–145
  - `src/Camfort/Specification/Units/Analysis/Consistent.hs` 37–52
  - `src/Main.hs` 360–366, 514–528
  - `doc/units.txt` 31–61
  - `README.md` 53–66
  - `samples/units/fahrenheit.f90`, `samples/units/poly1.f90`
  - `tests/fixtures/Specification/Units/example-inconsist-1.f90`, `literal-nonzero-inconsist1.f90`
- `hgrecco/pint` @ `072281c5f1b3d5fe30d097cbb0791be03ee24d45` (HEAD on the observation date):
  - `pint/facets/plain/quantity.py` 643–651, 776–914, 1252–1257, 1351–1358, 1640–1748
  - `pint/facets/plain/registry.py` 228–244
  - `pint/facets/nonmultiplicative/registry.py` 38–58
  - `pint/default_en.txt` 116–133, 207–209, 230, 378–382
- `JuliaLang/julia` @ `8dda794eec3571f4776fac724629459301e3ecfd` (resolves; not HEAD on the observation date):
  - `base/promotion.jl` 300–467, 526–528
  - `base/int.jl` 87–103, 359–361, 577–593, 812–826
  - `base/float.jl` 243–263, 406–415, 885–928
- `python/peps` @ `4434e728a7db24540d581f52e96570ca1230356e` (HEAD on the observation date): `peps/pep-0238.rst` 1–479 (Status: Final; Python-Version 2.2).
- `rust-lang/rust-clippy` @ `663e7ca4f8e69efa893b816140889b4a40c65f74` (HEAD on the observation date):
  - `clippy_lints/src/casts/mod.rs` 210–414
  - `cast_precision_loss.rs` 1–43
  - `cast_possible_truncation.rs` 29–177
  - `cast_lossless.rs` 79–109
  - `tests/ui/cast*.rs` (listing only)
- `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`: the commit of the rustc nightly used for probes (reported by `rustc --version --verbose`).

**Literature.** Every DOI was verified through the doi.org handle API (responseCode 1) plus OpenAlex metadata (title, authors, venue, year, volume, pages); Crossref was unreachable from the observation host.

| DOI | Work | Text read |
|---|---|---|
| 10.1007/978-3-642-04570-7_6 | Delmas, Goubault, Putot, Souyris, Tekkal, Védrine, FMICS 2009, LNCS pp. 53–69 | abstract (Springer page) + authors' slides (lix.polytechnique.fr) |
| 10.1145/2743019 | Dietz, Li, Regehr, Adve, TOSEM 25(1) 2015 | author manuscript (users.cs.utah.edu) |
| 10.1016/j.jocs.2015.04.018 | Orchard, Rice, Oshmyan, J. Comput. Sci. 9:156–162, 2015 | abstract only |
| 10.1109/MCSE.2016.17 | Contrastin, Rice, Danish, Orchard, CiSE 18(1):102–107 | accepted manuscript (Kent repository) |
| 10.1109/IROS.2017.8202229 | Ore, Elbaum, Detweiler, IROS 2017, pp. 712–718 | abstract only |
| 10.1109/ASE.2017.8115662 | Di Franco, Guo, Rubio-González, ASE 2017, pp. 509–519 | abstract + authors' slides |
| 10.1145/3238147.3238173 | Ore, Elbaum, Detweiler, Karkazis, ASE 2018, pp. 190–201 | full text (first author's site) |
| 10.1145/3276604.3276613 | Bennich-Björkman, McKeever, SLE 2018, pp. 121–132 | abstract only |
| 10.1145/3276490 | Bezanson, Chen, Chung, Karpinski, Shah, Vitek, Zoubritzky, PACMPL 2(OOPSLA) 2018 | author copy (janvitek.org); it contains no discussion of the promotion system ("promot" does not occur) |
| 10.5220/0007524704430449 | McKeever, Paçacı, Bennich-Björkman, MODELSWARD 2019, pp. 443–449 | full text (SciTePress) |
| 10.1002/spe.2926 | McKeever, Bennich-Björkman, Salah, SPE 51(4):711–734, 2021 | full text (DiVA copy) |
| 10.1145/3439775 | Ore, Detweiler, Elbaum, TOSEM 30(2) 2021 | abstract only |

OpenAlex lists publication year 2015 for the CiSE article (online first; issue 18(1) is 2016) and 2020 for the SPE article (online first; issue 51(4) is 2021).

**Execution (support material in `support/`).**

- Host: x86-64 Linux, 96 vCPU Intel Xeon @ 2.60 GHz, shared.
- Toolchains: CPython 3.13.15; GCC 15.2.0 (Debian 15.2.0-14); rustc 1.102.0-nightly (2026-11-11); clippy 0.1.101; pint installed with `pip install "git+https://github.com/hgrecco/pint@072281c5f1b3d5fe30d097cbb0791be03ee24d45"` into a fresh virtualenv.
- Files: `py_division_probe.*`, `c_conversions_probe.*`, `rust_casts_probe.*`, `rust_mixed_e0277.*`, `rust_overflow_probe.*`, `clippy_casts_probe/` + outputs, `pint_probe.*`, `pint_bench.*`. Exact commands are in `support/README.md`.
- Timing commands used `/usr/bin/time -f "%e s wall, %M KiB maxrss"`.

## Revalidation

- **PEP 238 / Python.** Run `python3 support/py_division_probe.py` and diff against `py_division_probe.out`. Any change in `/` or `//` results would be a language change.
- **Julia.** Check that `base/int.jl` still contains `(/)(x::BitInteger, y::BitInteger) = float(x) / float(y)`, and that `promote_type(Int64, Float16)` is still documented as `Float16` in `base/promotion.jl`. With Julia installed, evaluate `promote_type(Int64, Float16)`, `typeof(7/2)`, `typemax(Int)+1`, `Int(2.5)` (expect `InexactError`), `promote_type(Int64, UInt64)` (expect `UInt64`), and `-1 < UInt(1)` (expect `true`, by the comparison methods in `int.jl` 581–593).
- **C.** Recompile `support/c_conversions_probe.c` with the same flags on the target compiler. The discriminating facts are:
  - whether any warning appears for `return sum / n;` in `average_int`;
  - whether `-Wconversion` flags `a * b`;
  - whether `(-1L < 1u)` changes on ILP32.
- **Rust / Clippy.**
  - `rustc rust_mixed_e0277.rs` must still fail with E0277/E0308.
  - In a newer clippy checkout, diff `clippy_lints/src/casts/mod.rs` for lint group changes away from `pedantic`, and `cast_precision_loss.rs` line 20 for the width rule.
  - Rerun `cargo clippy` in `support/clippy_casts_probe/` and compare against the 9 recorded warnings.
- **pint.** Reinstall at the new revision and diff `pint_probe.out`. Then grep `quantity.py` for the `zero_or_nan` branch in `_add_sub` and for `except DimensionalityError` in `__eq__`.
- **CamFort.** Diff `Analysis.hs` `intrinsicUnits` (especially `mod` and the `int`/`real` rows), `Parser.y` lexer line 151, and `Main.hs` default `LitMixed`. To confirm source-derived claims by execution, build CamFort and run `camfort units-check samples/units/fahrenheit.f90` and `units-suggest` on the energy example from Contrastin et al.
- **Literature numbers** are fixed by publication. To check them, re-read the cited sections: Ore 2018 §4.1–4.3; McKeever 2021 §3.4, §4.1.2–4.2; Dietz 2015 §6.3 and §7.3. The full texts of Orchard 2015, Ore 2017/2021, Di Franco 2017, and Delmas 2009 still need to be obtained to replace the abstract- and slide-level claims.
