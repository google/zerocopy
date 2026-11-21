# Deployed operator-precedence and arithmetic-kind diagnostics (Error Prone, SpotBugs, GCC/Clang, Clippy, Swift precedence groups) and field evidence on warning false positives and bug-detector recall

## Summary

- **Checkers disagree on which operator pairs are "confusing".** Error Prone `OperatorPrecedence` flags two different-precedence operators from `& | ^ && ||`, and a shift mixed with `+ - * /` (not `%`). GCC 15.2 `-Wparentheses` flags `+`/`-` under a shift; `+`/`-`, lower-precedence-level bitwise operators or comparisons under `& ^ |`; `&&` under `||`; and relational chains, but never `a & b << c` or `a % b << 2`. Clang warns by default on bitwise-vs-comparison, `+`/`-` under a shift and arithmetic before `?:`, needs `-Wall` for `&`-in-`|` and `&&`-in-`||`, never flags `a & b + c`, and makes `a < b < c` a default **error**. Clippy's default `precedence` flags arithmetic (including `%`) under a shift or under `& | ^`; neither it nor the restriction lint `precedence_bits` flags `a & b | c` or `&&`-in-`||`. SpotBugs' only precedence pattern, `BSHIFT_WRONG_ADD_PRIORITY`, needs the **constant as left addend** of `x << (c + y)`, ignores `-` and right shifts, and is hidden by default unless `c == 8`, the value came from `&`, or the method is `hashCode`. Basis: source + execution.
- **Arithmetic-kind checks split along source vs bytecode.** SpotBugs `ICAST_IDIV_CAST_TO_DOUBLE` matches `IDIV|LDIV` then `I2D|I2F|L2D|L2F` (implicit and explicit conversions alike; folded constants invisible). Error Prone `NarrowCalculation` flags integral `/` with a floating target type and `int * int` with a `long` target; `IntLongMath` flags non-constant `int` arithmetic stored to `long`; `ConstantOverflow` (an error) covers constants. GCC/Clang core have no integer-division-in-float warning (clang-tidy does). Rust makes both mistakes type errors or explicit `as` casts that default Clippy ignores. Basis: source + execution.
- **Languages remove some classes.** Java rejects `a & b == c` and `a < b < c` on `int`; Rust binds `& ^ |` above comparisons and rejects chained comparisons. Swift SE-0077 replaced numeric precedence by a DAG of `precedencegroup`s, citing `a & b < c` and `a / b as Double`, yet the standard groups form **one chain**: only ungrouped operators (`DefaultPrecedence`) are unordered against arithmetic, comparison and logical operators, and Swift's order parses `x << 16 + y`, `a & b + c`, `a % b << 2`, `x >> y - 1` differently from C. Basis: normative + source + derived.
- **Field evaluations measure developer action, not ground truth** (Tricorder's *effective false positive*, probation at a ≥ 10% not-useful rate, zero effective false positives for compiler errors; FindBugs triage; Habib–Pradel's 27 of 594 Defects4J bugs found; Findings 4–5). No study examined reports per-pattern rates for precedence or integer-division checks: `not measured`.

## Applicability

| Subject (revisions in Evidence) | Role |
|---|---|
| Error Prone (`google/error-prone`) | source only (GitHub releases v2.51.0–v2.53.0 carry no jar assets; Maven Central downloads were out of scope) |
| SpotBugs source and tag `4.10.5` + `spotbugs-4.10.5.tgz` | source; executed release; both detectors, `findbugs.xml` and `bugrank.txt` are byte-identical between the two revisions (`cmp`) |
| Clang/clang-tidy (`llvm/llvm-project`) | source only (no Clang binary on the host) |
| GCC `releases/gcc-15.2.0` source; `gcc (Debian 15.2.0-14) 15.2.0` | source + execution (distribution patches not examined; all probe results match upstream source) |
| Clippy source; `rust-lang/rust` nightly (`rustc 1.102.0-nightly`, `clippy 0.1.101`) | source; executed toolchain, whose in-tree `precedence.rs` and `integer_division.rs` equal the Clippy pin |
| `javac 27.0.1` | executed (type rejections; `--release 17` class files for SpotBugs) |
| SE-0077 (`swiftlang/swift-evolution`); Swift stdlib (`swiftlang/swift`) | normative proposal; stdlib groups and diagnostics; not executed |
| `sola-da/StaticBugCheckers`; papers by DOI | recall artifact; field studies (Findings 4–5) |

Subjects are compared on one shared probe set, not combined. "Default": Error Prone `ENABLED_*` sets without flags; SpotBugs `-effort:max` without `-low`; GCC/Clang without `-W` flags; Clippy without `-W/-A`. Other versions are not claimed (see Revalidation).

## Findings

### 1. Checker definitions at the pinned revisions

#### 1.1 Error Prone `OperatorPrecedence`

```java
46     summary = "Use grouping parenthesis to make the operator precedence explicit",
47     severity = WARNING,
52  private static final ImmutableSet<Kind> CONDITIONAL =
53      Sets.immutableEnumSet(Kind.AND, Kind.OR, Kind.XOR, Kind.CONDITIONAL_AND, Kind.CONDITIONAL_OR);
58  private static final ImmutableSet<Kind> ARITHMETIC =
59      Sets.immutableEnumSet(Kind.PLUS, Kind.MULTIPLY, Kind.DIVIDE, Kind.MINUS);
97    if (CONDITIONAL.contains(thisKind) && CONDITIONAL.contains(parentKind)) {
100   return (SHIFT.contains(thisKind) && ARITHMETIC.contains(parentKind))
101       || (SHIFT.contains(parentKind) && ARITHMETIC.contains(thisKind));
```

A binary child of a binary parent with *different* javac precedence (lines 64–78) and a pair accepted by `isConfusing` (96–102); `SHIFT` = `<< >> >>>` (55–56). Also a `?:` whose condition is an unparenthesized `& | ^ && ||` and whose result type is `boolean` (80–94). Not flagged: equal precedence, anything with `%`, `a & b + c`, `a & b << c`, comparisons. Fix: wrap the child in parentheses (138–141), re-bracketing associative `&& || +` chains (104–113). Severity WARNING, tag `STYLE`, in `ENABLED_WARNINGS` (`BuiltInCheckerSuppliers.java` line 1135). The also-enabled `UnnecessaryParentheses` (line 1218) cannot undo these fixes: `ASTHelpers.requiresParentheses` returns `true` for every binary expression (`ASTHelpers.java` 376–425). Basis: source.

#### 1.2 Error Prone arithmetic-kind checks

| Check | Severity / default | Trigger | Exemptions | Fix |
|---|---|---|---|---|
| `IntLongMath` (44–127) | WARNING, `ENABLED_WARNINGS` l.1046 | initializer, assignment or `return` with `long` target and `int` expression; innermost left-spine op not in `DIVIDE, REMAINDER, AND, XOR, OR, RIGHT_SHIFT` (109–115, "binops that can't overflow") | compile-time constants (91–93) | `L` on a literal, else `(long) ` on left operand (121–127) |
| `NarrowCalculation` (41–107) | WARNING, l.1114 | integral `/` with floating target type; `int * int` with `long` target | exact constant division (60–66); constant product fitting `int` (90–96); `*` in test-only targets (83–87) | retype literal (`L`/`f`/`.0`) or cast right operand |
| `ConstantOverflow` (54) | ERROR, `ENABLED_ERRORS` l.763 | outermost constant expression that overflows | non-constants | `L` suffix |

`NarrowCalculation`'s target type comes from `TargetType`, which skips parentheses (lines 103–106) and returns the cast type under a cast (342–344), so `(double) (i / j)` is in scope. `IntLongMath`'s own documentation example (`long nanosPerDay = 24 * 60 * 60 * 1000 * 1000 * 1000;`) is a constant expression that `IntLongMath` skips; by source it is reported by `ConstantOverflow`. Basis: source (not executed).

#### 1.3 SpotBugs `ICAST_IDIV_CAST_TO_DOUBLE`

`IDivResultCastToDouble.java` records a pending location when `prevOpCode == Const.IDIV && (seen == Const.I2D || seen == Const.I2F) || prevOpCode == Const.LDIV && (seen == Const.L2D || seen == Const.L2F)` (lines 70–72) and, at the next instruction, emits `new BugInstance(this, "ICAST_IDIV_CAST_TO_DOUBLE", NORMAL_PRIORITY)` (63–68) — unless that instruction is a `Math.ceil` call, which yields `ICAST_INT_CAST_TO_DOUBLE_PASSED_TO_CEIL` at HIGH priority instead (51–56). Enabled detector (`findbugs.xml` 583–584), category `STYLE` (1208), no fix offered. Executed: reported for `double d = i / j`, `(double) (i / j)` and `long` division (priority 2, rank 17); not for `(double) (7 / 2)` (javac folds it); `Math.ceil(i / j)` gives the CEIL pattern (priority 1, rank 7). Basis: source + execution.

#### 1.4 SpotBugs `BSHIFT_WRONG_ADD_PRIORITY` and `ICAST_INTEGER_MULTIPLY_CAST_TO_LONG`

```java
344 if (seen == Const.IADD && (getNextOpcode() == Const.ISHL || getNextOpcode() == Const.LSHL) && stack.getStackDepth() >= 3) {
346     OpcodeStack.Item v = stack.getStackItem(1);
349     if (constantValue instanceof Integer && !Integer.valueOf(1).equals(l.getConstant())) {
351         int priority = LOW_PRIORITY;
363                 // commonly observed error is hashCode body like "return foo << 16 + bar;"
```

(`FindPuzzlers.java`.) Requires `IADD` then `ISHL`/`LSHL` with the *second* stack item (the left addend) an `Integer` constant `c < 32` (`< 64` for `LSHL`, line 354); exempts a shifted constant `1`. Priority starts LOW and is raised for `c == 8` (355–357), a preceding `IAND` (358–360), or a `hashCode()` that returns the result (HIGH, 361–365). Category `CORRECTNESS` (`findbugs.xml` 1239); `bugrank.txt` line 29 adds `+5`. Executed: `x << 16 + y` priority 3 / rank 15 (shown only with `-low`); `x << 8 + y` priority 2 / rank 12; the `hashCode` case priority 1 / rank 10; `x << y + 16`, `x >> y - 1`, `a % b << 2` and `& | ^` mixes never. `ICAST_INTEGER_MULTIPLY_CAST_TO_LONG` (263–273, `IMUL; I2L`) fired for `long l = i * j` (rank 17) and `days * 24 * 3600 * 1000` (rank 15), not for a folded constant. Basis: source + execution.

#### 1.5 Clang `-Wparentheses` family and clang-tidy (source only)

`-Wparentheses` = `logical-op-`, `logical-not-`, `bitwise-conditional-`, `bitwise-op-`, `shift-op-`, `overloaded-shift-op-parentheses`, `parentheses-equality`, `dangling-else` (`DiagnosticGroups.td` 1401–1409), and is in `-Wall` (1577).

| Diagnostic (`DiagnosticSemaKinds.td`) | Default | Trigger (`SemaExpr.cpp`) |
|---|---|---|
| `warn_precedence_bitwise_rel` (7657) "%0 has lower precedence than %1; %1 will be evaluated first" | on | `& ^ \|` with exactly one comparison side and no bitwise side ("Bitwise operations are sometimes used as eager logical ops") (16205–16242) |
| `warn_addition_in_bitshift` (7715) | on | `+`/`-` directly under `<<` (integral LHS) or `>>` (16311–16323, 16374–16379) |
| `warn_precedence_conditional`, `_bitwise_conditional` (7665, 7668) | on | unparenthesized `+ - * / % << >> & \|` as `?:` condition with boolean-looking RHS; `^` and logical ops excluded as having "a high false positive rate" (9379–9491) |
| `warn_consecutive_comparison` (7674) | **error** | `< <= > >=` with an unparenthesized comparison LHS (16040–16050) |
| `warn_bitwise_op_in_bitwise_op` (7699) | off | `&` under `^`/`\|`, `^` under `\|`, outside macros (16296–16309, 16361–16365) |
| `warn_logical_and_in_logical_or` (7702) | off | `&&` under `\|\|`, except `&& "literal"` (16259–16291) |
| `warn_overloaded_shift_in_comparison` (7705) | on | overloaded `<<`/`>>` as comparison LHS (16325–16349) |
| `warn_logical_not_on_lhs_of_check` (8260) | on | `!x == y`, `!x & y` (12793) |

All attach parenthesizing fix-its. Derived: Clang flags none of `a & b + c`, `a & b << c`, `a % b << 2`, `a * b + c`. clang-tidy adds `bugprone-integer-division` (integer `/` under a `CK_IntegralToFloating` cast, unless an intervening bitwise/logical/comparison operator, `?:`, integer call or integer cast; `IntegerDivisionCheck.cpp` 16–41), `bugprone-implicit-widening-of-multiplication-result` (implicit widening of a product, **not** explicit casts; 110–111, 277–284) and `readability-math-missing-parentheses` (any nesting of different levels among `* / %`, `+ -`, `&`, `^`, `|`, including `a * b + c`, never shifts; `MathMissingParenthesesCheck.cpp` 18–91). Basis: source.

#### 1.6 GCC 15.2 `-Wparentheses`

`warn_about_parentheses` (`gcc/c-family/c-warn.cc` 2015–2188) switches on the parent operator: `<<`/`>>` with `+`/`-` child (2044–2072); `||` with `&&` (2074–2081); `|` with `& ^ + -`, else a comparison, else `!x` (2083–2105); `^` with `& + -`, else comparison (2107–2123); `&` with `+ -`, else comparison, else `!x` (2125–2151); `==`/`!=` with comparison (2153–2168); relational with relational, non-equality, integral child: "comparisons like 'X<=Y<=Z' do not have their mathematical meaning" (2170–2186). Executed (matrix, Finding 3): with no flags only `-Woverflow` fires; `-Wall`/`-Wparentheses` match these predictions exactly; `!a == b` needs `-Wlogical-not-parentheses` (in `-Wall`); no arithmetic-kind case warns even with `-Wall -Wextra -Wconversion`. Basis: source + execution.

#### 1.7 Clippy `precedence`, `precedence_bits`, `integer_division`

```rust
73                    BitAnd | BitOr | BitXor,
74                    Some(left_op @ (Shl | Shr | Add | Div | Mul | Rem | Sub)),
78                    Shl | Shr,
79                    Some(left_op @ (Add | Div | Mul | Rem | Sub)),
```

(`precedence.rs`; `PRECEDENCE` is declared `complexity` at lines 23–24, `PRECEDENCE_BITS` `restriction` since 1.86.0 at 40–42.) Early (AST) lint on a `^ & | << >>` node with an unparenthesized binary child from those sets (67–111); if every operator is a bit operator the finding goes to `PRECEDENCE_BITS` (141–147). `PRECEDENCE` also flags a method call on a closure (112–125); macro expansions are skipped (50–52). `complexity` warns by default, `restriction` is allow-by-default; both give `MachineApplicable` parenthesization. `integer_division` (restriction since 1.37.0; `operators/mod.rs` 599–623, `integer_division.rs` 16–24) flags every `/` with integral operands. Executed results are in the matrix (Finding 3); notably `a & b | c`, `a ^ b | c`, `a & b ^ c` and `a && b || c` get nothing, and `(i * j) as i64` only the pedantic `cast_lossless`. Basis: source + execution.

### 2. Prevention by grammar and types

| Mistake | Java (javac, executed) | Rust (rustc, executed) | Swift (derived, not executed) |
|---|---|---|---|
| `a & b == c` (ints) | type error "bad operand types for binary operator '&'" | parses `(a & b) == c` | `&` (Multiplication) > Comparison: `(a & b) == c` |
| `a < b < c` | type error | parse error "comparison operators cannot be chained" | Comparison is non-associative: error |
| `long l = i * j`; `double d = i / j` | compile silently | E0308; suggested fix `(i * j).into()` / `(i / j).into()` keeps the narrow operation | not examined |

(`outputs/javac.txt`, `outputs/rustc_reject.txt`.) A type error turns an implicit widening into an explicit one without moving the operation to the wider type. Basis: execution + derived.

#### 2.1 Swift SE-0077 precedence groups

- **Model** (SE-0077 at the pin, "Implemented (Swift 3.0)"): named groups with optional `associativity`, `assignment`, `higherThan`/`lowerThan`; "to omit parentheses in expression with two neighbouring `infix` operators, precedence relationship *must* be defined between their precedence groups" (lines 86–110, e.g. `1 + 2 & 3  // error`). Relations form a DAG queried by reachability; cycles are errors (115–129, 183–210). `lowerThan` may only name another module's group (157–179; enforced by `precedence_group_lower_within_module`, `DiagnosticsSema.def` 1436–1439). Relating two imported groups by transitivity is specified as an error (212–230), but no diagnostic with that meaning was found in `DiagnosticsSema.def` (`unknown`). Ungrouped operators join `DefaultPrecedence { higherThan: TernaryPrecedence }` (133–148).
- **Motivation vs outcome:** `a & b < c` and `a / b as Double` are cited as "common error patterns" (51–56), but breaking the stdlib's single hierarchy is deferred to "another proposal" (407–412).
- **Source compatibility** (397–405): the migrator strips operator bodies and assigns `DefaultPrecedence`; code relying on implicit relations between user operators "may be broken" and is fixed by hand; no measurement is cited.

Standard groups at the Swift pin (`Policy.swift` 390–436, members 467–520), highest first:

```text
BitwiseShift(none: << &<< >> &>>) > Multiplication(left: * &* / % &) > Addition(left: + &+ - &- | ^)
> RangeFormation(none: ... ..<) > Casting(none: as is) > NilCoalescing(right: ??)
> Comparison(none: < <= > >= == != === !== ~=) > LogicalConjunction(left: &&) > LogicalDisjunction(left: ||)
> Ternary(right) > FunctionArrow(right) > Assignment(right, assignment)
Default(none) > Ternary   -- unordered with BitwiseShift ... LogicalDisjunction
```

Relative to SE-0077 only `FunctionArrowPrecedence` and the operators `&<<`, `&>>` and one-sided range operators were added. **Unrelated pairs:** every pair of standard operators is ordered, so between them the compiler can raise only `non_associative_adjacent_operators` (`DiagnosticsSema.def` 5197–5199; e.g. `a << b << c`, `a < b < c`, `a ... b ... c`), never `unordered_adjacent_operators` (5200–5202). Parentheses are forced by missing order only next to an ungrouped custom operator (`DefaultPrecedence` vs the nine groups from BitwiseShift to LogicalDisjunction). Swift therefore fixes `a & b == c` by *reordering*, and the reordering diverges from C exactly where C checkers warn: `x << 16 + y` = `(x << 16) + y`, `a & b + c` = `(a & b) + c`, `a % b << 2` = `a % (b << 2)`, `x >> y - 1` = `(x >> y) - 1`. Basis: normative + source + derived.

### 3. Cross-checker matrix

**E** executed and reported; **E–** executed, not reported; **S**/**S–** source-derived would / would not report; **T** rejected by the language; n/a not expressible. GCC column is `-Wall` (no flags: only c20). Clang and Error Prone not executed. clang-tidy column: `readability-math-missing-parentheses` for precedence rows, `bugprone-integer-division` / `-implicit-widening-of-multiplication-result` for c17–c20.

| # | Expression (C syntax) | GCC 15.2 `-Wall` | Clang default (`-Wall` adds) | clang-tidy | Error Prone | SpotBugs 4.10.5 default (`-low`) | javac | rustc | Clippy default (opt-in) | Swift parse |
|---|---|---|---|---|---|---|---|---|---|---|
| c01 | `a & b == c` | E | S | S– | n/a | n/a | T | `(a&b)==c` | E– | `(a&b)==c` |
| c02 | `x << 16 + y` | E | S | S– | S | E– (E, rank 15) | ok | ok | E | `(x<<16)+y` |
| c02b | `x << 8 + y` | E | S | S– | S | E (rank 12) | ok | ok | E | `(x<<8)+y` |
| c03 | `x << y + 16` | E | S | S– | S | E– (E–) | ok | ok | E | `(x<<y)+16` |
| c04 | `a && b \|\| c` | E | S– (S) | S– | S | E– | ok | ok | E– | same as C |
| c05 | `a & b \| c` | E | S– (S) | S | S | E– | ok | ok | E– (E–) | same as C |
| c06 | `a ^ b \| c` | E | S– (S) | S | S | E– | ok | ok | E– (E–) | same as C |
| c07 | `a & b ^ c` | E | S– (S) | S | S | E– | ok | ok | E– (E–) | same as C |
| c08 | `a & b << c` | E– | S– | S– | S– | E– | ok | ok | E– (E, `precedence_bits`) | same as C |
| c09 | `a & b + c` | E | S– | S | S– | E– | ok | ok | E | `(a&b)+c` |
| c10 | `a * b + c` (control) | E– | S– | **S** | S– | E– | ok | ok | E– | same as C |
| c11 | `a % b << 2` | E– | S– | S– | S– (`%` omitted) | E– | ok | ok | E | `a%(b<<2)` |
| c12 | `a < b < c` | E | **S (error)** | S– | n/a | n/a | T | T | n/a | error |
| c13 | `a + (b>0) ? 1 : 2` | E– | S | S– | n/a | n/a | T | T | n/a | not examined |
| c14 | `a & (b>0) ? 1 : 2` | E– | S | S– | n/a | n/a | T | T | n/a | not examined |
| c15 | `!a == b` | E (`-Wlogical-not-parentheses`, in `-Wall` but not in `-Wparentheses`) | S | S– | not probed | not probed | not probed | not probed | not probed | not examined |
| c17 | `double d = i / j` | E– | S– | S | S (`NarrowCalculation`) | E | ok | T | n/a | not examined |
| c18 | `(double)(i / j)` | E– | S– | S | S | E | ok | ok (`as f64`) | E– (E, `integer_division`) | not examined |
| c18b | `(double)(7 / 2)` | E– | S– | S | S | E– (folded) | ok | not probed | not probed | not examined |
| c19 | `long l = i * j` | E– | S– | S (implicit only) | S (`IntLongMath` + `NarrowCalculation`) | E | ok | T | E– (`as i64`; pedantic `cast_lossless` only) | not examined |
| c20 | `24*60*60*1000*1000` | E (`-Woverflow`, default) | not examined | not examined | S (`ConstantOverflow`, error) | E– | ok | not probed | not probed | not examined |
| c22 | `x >> y - 1` | E | S | S– | S | E– | ok | ok | E | `(x>>y)-1` |

Observations (derived from the matrix): (1) among the three executed checkers (GCC `-Wall`, SpotBugs default, Clippy default) only `x << 8 + y` is reported by all three, while `x << 16 + y` is hidden by SpotBugs' default threshold and `x << y + 16` is invisible to SpotBugs; (2) bitwise-vs-bitwise mixes (`c05`–`c07`) are flagged by GCC `-Wall`, Clang `-Wall` and Error Prone but by neither Clippy lint; (3) `a & b + c` (`c09`) is flagged by GCC and Clippy but by neither Clang nor Error Prone; (4) only SpotBugs and Error Prone (by source) see integer division in a floating context without opt-in; (5) the control `a * b + c` is flagged only by clang-tidy's readability check. Basis: execution + source + derived.

### 4. Field evaluations of static-analysis warnings

Every DOI below resolves in Crossref to the intended paper. "Read" = full text read; "abstract" = abstract and secondary sources only. Numbers are quoted from the text read.

| Study | Setting | Definitions / triage | Verified numbers and policy |
|---|---|---|---|
| Hovemeyer–Pugh 2004 (read: pre-publication draft) | FindBugs 0.8.44 high/medium warnings, six Java code bases (GNU Classpath 0.08 … jEdit 4.2pre15) | *false positive* / *mostly harmless* / *serious* | target "at least 50% of reported bugs should be genuine"; per-detector false-positive shares range 0–100% by code base (Figure 12 as reconstructed from text extraction; e.g. `Wa` 100% on Classpath and JBoss). None of the 18 patterns discussed is a precedence or integer-division pattern. |
| Ayewah et al. 2007 (abstract) / 2008 (read) | Sun JDK, Glassfish, Google | 2007: "false positives, trivial bugs and serious bugs" | 2008: of 379 JDK 1.6.0 medium/high correctness warnings, 5 bad analysis, 160 little/no impact, 176 functional, 38 substantial; Google "evaluated several thousand FindBugs warnings and filed more than 1,000 bug reports", "fixed more than 1,000 issues"; patterns ranked "using both the observed falsepositive rate and the observed fix rate"; "stale warnings have a greater negative impact ... than a false positive". |
| Google FindBugs fixit 2009 (as reported in Sadowski et al. 2018) | company-wide review week | reviewed / filed / fixed | 3,954 of 9,473 warnings reviewed (42%), 1,746 bug reports (44% of reviewed), 640 fixed (16%). |
| Kim–Ernst 2007 (read) | FindBugs, JLint, PMD on Columba, Lucene, Scarab | warning "correct" iff on a line modified by a later fix change (log keywords) | 6%, 9%, 9% of warnings removed by fixes; tools' priorities reach precision 3%, 12%, 8%; history-based category weights (α = 0.9; train on revisions 1…n/2−1, test n/2…n) reach 17%, 25%, 67%. |
| Heckman–Williams 2011 (abstract) | systematic review | actionable = "anomalies important enough for developers to fix" | 21 studies; 7 report precision; the two most precise use program history. |
| Aftandilian et al. 2012 (abstract) | Error Prone and two other `javac`-based tools | — | adds error checks to compilation with automated repair; no number verified. |
| Johnson et al. 2013 (read) | 20 interviews (16 professionals, 4 graduate students) | — | 14/20 report harm from poorly presented output; 19/20 stress workflow integration; missing quick fixes most-mentioned. |
| Sadowski et al. 2015, Tricorder (read) | code-review analysis platform | **effective false positive**: "any report from the tool where a user chooses not to take action to resolve the report"; not-useful rate = NOT USEFUL / (NOT USEFUL + PLEASE FIX + APPLY FIX) | admission requires "an actual issue at least 90% of the time" (manual sample); "A rate ≥ 10% puts the analyzer on probation"; "above 25%, we may decide to turn the analyzer off"; platform rate "around 5%", "under 4%" without probationary analyzers, best 0–3%; ~93K findings/day, 716 PLEASE FIX vs 48 NOT USEFUL/day; build-breaking analyses: effective false-positive rate "essentially zero", "< 5% overhead". |
| Sadowski et al. 2018, CACM (read) | Google-wide | adds: a real fault the developer "did not understand ... and therefore took no action" is an effective false positive | compiler checks: "no effective false positives", "correctness rather than style"; code review: "up to 10%"; ratio "above 10%" → analyzer disabled (stricter than the 2015 wording; disagreement preserved); 733 Error Prone checks by 162 authors; ~50,000 changes/day; >5,000 Please Fix, ~3,000 applied fixes, 250 Not useful per day; compile-time issues judged "real problems" 74% vs 21% in checked-in code; "we fixed 31 occurrences" of an `int` shifted by 32 when that check became an Error Prone error. |
| Beller et al. 2016 (read) | 122 projects + 168,214 configs; nine ASATs incl. Checkstyle, FindBugs, PMD | — | 59% of the 122 use ASATs; Table V: FindBugs 93.0% "Changed" vs 7.0% "No Deviations" (unit not verified); custom rules ≤ 5%; "a little over 80%" of configs never change. |

Derived: (1) `OperatorPrecedence` is tagged `STYLE`; under the 2018 compiler-check criteria a style check belongs in code review, consistent with its `WARNING` severity (no organization's configuration was examined). (2) The shift-by-32 anecdote matches Error Prone `BadShiftAmount` ("Shift by an amount that is out of range", ERROR, `ENABLED_ERRORS` line 746); the article does not name the check. (3) All rates are platform-level; per-pattern rates for precedence or integer-division checks are `not measured`.

### 5. Detector recall against real faults

**Habib–Pradel 2018** (paper full text not available; read: abstract, authors' slides, artifact `sola-da/StaticBugCheckers` @ `e3bd772b9151722f0683e8037bcd1af1f8fa4142`). Error Prone 2.1.1, Infer 0.13.0 (replication script: 0.15.0), SpotBugs 3.1.0 (`scripts/download_static_checkers.sh` 9–30) on 594 bugs from 15 projects in an unofficial Defects4J extension (README 95–100: "596 bugs instead of 395 bugs in the official release", metadata repaired by hand; the 594/596 gap is unexplained). Matching: diff-based (warning on a fix-changed line) plus fixed-warnings-based (warning disappears after the fix), then manual full/partial/mismatch classification; 5,247 warnings → 153 candidates. Result: "Detect 27 of 594 bugs (less than 5%)"; SpotBugs 18, Error Prone 8, Infer 5, 27 unique (`results/README.md` 36–45; 4.5% derived). Of 20 sampled misses, 14 domain-specific, 6 near misses. **Precedence / arithmetic kind:** the per-bug tables ("not in the paper") contain no precedence pattern; the only arithmetic-kind detection is Error Prone `NarrowingCompoundAssignment` (Math-57); `FE_FLOATING_POINT_EQUALITY` and `CO_COMPARETO_INCORRECT_FLOATING` are float-comparison patterns. How many missed bugs are precedence or integer-division faults: `unknown`.

**Rahman et al. 2014** (read). FindBugs and PMD (Jlint dropped) vs logistic defect prediction on Lucene, Wicket, OpenJPA, Qpid, Derby, scored by inspection-cost-sensitive AUCEC with full or partial credit. FindBugs beat prediction in 21 of 29 releases under full credit, while under partial credit prediction beat FindBugs in 11 of 29 and PMD in 27 of 29; overall "no significant discernible difference" between FindBugs and prediction; up to "99.5" [percent] of warnings "are perhaps false positives"; ordering warnings by prediction scores beat native priorities. No per-pattern breakdown for precedence or arithmetic patterns was found.

### 6. Performance and resource footprint (L1–L6)

Measured values are start-up-dominated micro-runs on the probe files (x86-64 Linux workstation, 96 logical CPUs; `support/outputs/timings.txt`), not costs on real code bases.

| Level | Measured or cited | Not measured |
|---|---|---|
| L1 implementation size (maintenance proxy) | Error Prone `OperatorPrecedence` 152 lines, `IntLongMath` 129, `NarrowCalculation` 156, `ConstantOverflow` 269; SpotBugs `IDivResultCastToDouble` 76, `BSHIFT` block 31; GCC `warn_about_parentheses` 174; Clang precedence helpers 185 + 113; clang-tidy checks 49/101/312; Clippy `precedence.rs` 147, `integer_division.rs` 26; Swift group declarations 47 [measured from pinned source] | developer effort per finding (only platform-level act/fix rates exist, Finding 4) |
| L2 toolchain build | — | all subjects |
| L3 analysis latency | SpotBugs: 2.64–4.18 s wall for one class (`-effort:max`, JVM start-up included), self-reported analysis clock 1.36–1.94 s; GCC `-fsyntax-only -Wall`: ≤ 0.01 s; `cargo clippy` re-check 0.07–0.16 s vs `cargo check` 0.04–0.07 s (difference within run spread); Tricorder requires compile-time analyses to add "< 5% overhead" (policy, cited) | Error Prone, Clang, Swift |
| L4 generated code | parenthesizing fixes that restate the parse leave the AST unchanged; retyping fixes (`L`, `(long)`, `.0`) change results by design (derived) | runtime effect of retyping fixes |
| L5 certificate checking | not applicable: no subject produces certificates | — |
| L6 memory / artifacts | `spotbugs-4.10.5.tgz` 15,948,373 bytes (GitHub API), extracted 17,477,519 bytes; SpotBugs peak RSS 531–632 MB vs self-reported 230–270 MB; GCC 12.9–13.9 MB; `cargo clippy` 106–126 MB (`cargo check` 90–113 MB) | Error Prone, Clang, Swift |

### 7. Comprehensibility and model refinement (C1–C2)

**C1.** GCC and Clang state the *rule* ("'&' has lower precedence than '=='; '==' will be evaluated first") with a fix-it, so a reader needs only the two operators on the line; Error Prone and Clippy print a parenthesized rewrite without the rule; SpotBugs names a method and line and leaves the reader to map bytecode evidence back to source. Thresholds hide coverage: whether `x << 16 + y`, `a & b | c` or `a & b << c` is reported depends on SpotBugs' priority threshold, Clang's `-Wall` and a Clippy restriction lint respectively, so "precedence checking is on" does not predict what is checked. Swift moves the burden to declarations: readers need the twelve-group chain and `DefaultPrecedence`'s unordered status, and a reader carrying C's table mis-parses four probe cases silently. Basis: derived.

**C2.** The invariants are "the intended parse is the grammar's parse" and "the operation is performed in the type its result is used at".
- Each checker hard-codes a different pair list. A partial order of operator groups with "unordered ⇒ parentheses required" (SE-0077's mechanism) applied to C-family operators — `& ^ |` unordered with comparisons and arithmetic, shifts unordered with arithmetic — makes every listed pair an ordinary case and replaces the lists by one table. Swift adopted the mechanism but kept standard operators totally ordered (SE-0077 lines 51–56 vs 407–412).
- Error Prone reports `long l = i * j` through two checks and its constant form through a third; one rule "operation narrower than its target type", parameterized by operator and constness, would subsume them.
- Bytecode is a realization accident: SpotBugs cannot tell `double d = i / j` from `(double)(i / j)`, loses folded constants, and reads operand order from stack depth (hence the left-constant restriction); clang-tidy instead treats an explicit cast as intent.
- Type systems remove cases without checkers, but Rust's suggested `(i * j).into()` keeps the narrow multiplication, so the arithmetic-kind invariant still needs a lint Clippy does not enable by default. Basis: source + execution + derived.

### 8. Validation of the checkers (V1–V4)

| Level | Evidence | Status |
|---|---|---|
| V1 spec adequacy | golden tests at the pins: `OperatorPrecedenceTest` 9 `@Test` (4 `BUG: Diagnostic` markers, rest refactoring pairs), `IntLongMathTest` 3, `NarrowCalculationTest` 8; Clippy UI `precedence.stderr` 10 diagnostics, `precedence_bits` 5, `integer_division` 5 [measured]; mutation testing not measured | partial |
| V2 differential | the matrix compares 3 executed and 2 source-derived checkers; it found coverage disagreements but no checker bug (all executed results match pinned source); fuzzing not examined | partial |
| V3 concurrency/crash/hardware | purely syntactic or bytecode-local checks | known not to apply |
| V4 human comprehension | field studies measure acted-on rates, not comprehension; see `infix-precedence-misunderstandings-rhombus-lattices-and-uax31-joiners` | not examined here |

## Boundaries

- **Source-derived only (not executed):** Error Prone, Clang/clang-tidy, Swift. Hence the double report of `long l = i * j` (`IntLongMath` + `NarrowCalculation`), `NarrowCalculation` on `(double)(i / j)`, every Clang cell and every Swift parse are inferences. GCC distribution patches: not examined.
- **Not exhaustive:** the absence of a Clang core integer-division-in-float diagnostic covers only the code read (the `-Wparentheses` family, `ImplicitIntFloatConversion`, conditional precedence). Enforcement of SE-0077's "joining unrelated imported groups" rule: `unknown`. Swift typing of `a / b as Double` with literals: not examined.
- **Per-pattern field data: not measured.** No verified study gives false-positive, effective-false-positive, fix or suppression rates for any checker examined here; assigning platform-wide rates to them is unsupported.
- **Literature read partially:** Ayewah et al. 2007, Heckman–Williams 2011, Aftandilian et al. 2012 and Habib–Pradel 2018 rest on abstracts, slides and the artifact; Hovemeyer–Pugh on the pre-publication draft. The artifact counts three Error Prone `MissingOverride` rows as detections while the slides show a `MissingOverride` candidate judged a mismatch; which count the paper used is `unknown`.
- **Census not executed:** a history census (run the executed checkers on each release of a fixed project sample, match warnings by file, method and normalized expression, and classify disappearances as fixed, suppressed or deleted) was designed but not run.
- **Unsupported stronger conclusions:** that SpotBugs ranks reflect measured precision (`bugrank.txt` offsets are hand-assigned); that Clang's `DefaultIgnore` choices rest on measurements (the only rationale in source, the `IsArithmeticOp` comment, cites no data); that Swift's groups eliminate precedence bugs (they reorder rather than forbid).
- **Related reports:** `infix-precedence-misunderstandings-rhombus-lattices-and-uax31-joiners` (human comprehension, partial-order precedence in new languages) and `mckeever-quantity-library-survey-ore-annotation-accuracy-camfort-fortran-units-pep238-true-division-and-fluctuat-airbus` (numeric promotion, true division) are not duplicated.

## Evidence

All evidence acquired 2026-11-21 (UTC); revisions resolved through the GitHub REST API. Line ranges are given where cited in Findings.

| Repository @ revision | Paths |
|---|---|
| `google/error-prone` @ `d37bcb8d89b21dd64b762274c7fb96967a3cba80` | `core/src/main/java/com/google/errorprone/bugpatterns/{OperatorPrecedence,IntLongMath,NarrowCalculation,ConstantOverflow,UnnecessaryParentheses,BadShiftAmount}.java`; `core/.../scanner/BuiltInCheckerSuppliers.java`; `check_api/src/main/java/com/google/errorprone/util/{ASTHelpers,TargetType}.java`; `docs/bugpattern/`; tests under `core/src/test/java/com/google/errorprone/bugpatterns/` |
| `spotbugs/spotbugs` @ `f4544188eb473d60221572fc0d5645325c8b18eb`; tag `4.10.5` @ `6816eb256805aa6eed1dced23e6a4aea08cc6660` | `spotbugs/src/main/java/edu/umd/cs/findbugs/detect/{IDivResultCastToDouble,FindPuzzlers}.java`; `spotbugs/etc/{findbugs.xml,bugrank.txt,messages.xml}` |
| `llvm/llvm-project` @ `25b1c803e1e1504f6dc11f7afd68e65ad3ee5964` | `clang/include/clang/Basic/{DiagnosticGroups,DiagnosticSemaKinds}.td`; `clang/lib/Sema/SemaExpr.cpp`; `clang/include/clang/AST/OperationKinds.def`; `clang-tools-extra/clang-tidy/{bugprone,readability}/` checks named in 1.5 |
| `gcc-mirror/gcc` @ `5115c7e447fc07457443df874bf57840e8316d5f` (tag `releases/gcc-15.2.0`) | `gcc/c-family/c-warn.cc`; `gcc/BASE-VER` |
| `rust-lang/rust-clippy` @ `663e7ca4f8e69efa893b816140889b4a40c65f74`; `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `clippy_lints/src/precedence.rs`, `clippy_lints/src/operators/{integer_division,mod}.rs`, `tests/ui/`; in-tree copies under `src/tools/clippy/` |
| `swiftlang/swift-evolution` @ `d8a2ff1f9c95e11772e99574fc4853da924f9a68`; `swiftlang/swift` @ `2d2f72d90982a9510260acefde67c8fcc1db04c5` | `proposals/0077-operator-precedence.md`; `stdlib/public/core/Policy.swift`; `include/swift/AST/DiagnosticsSema.def` |
| `sola-da/StaticBugCheckers` @ `e3bd772b9151722f0683e8037bcd1af1f8fa4142` | `README.md`, `results/README.md`, `scripts/download_static_checkers.sh` |

Papers: DOIs in `REPORT.json`, each checked with `api.crossref.org/works/<doi>`; full texts as marked in Finding 4. The 2009 fixit figures are quoted from Sadowski et al. 2018, which cites Ayewah–Pugh, "The Google FindBugs fixit", ISSTA 2010 (DOI 10.1145/1831708.1831738, Crossref-verified, not read).

**Execution:** x86-64 Linux workstation, 96 logical CPUs; `gcc (Debian 15.2.0-14) 15.2.0`; `javac 27.0.1` (class files `--release 17`); SpotBugs 4.10.5 from GitHub asset `spotbugs-4.10.5.tgz`, sha256 `cce3244900cc215ccd9f5a8db29ed9468fc47824faf662f4fad005343d96007e` (equal to the GitHub API digest); `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, `clippy 0.1.101`, edition 2024. Probes in `support/probes/` (function names carry case labels); outputs in `support/outputs/` (home-directory prefixes replaced by `$RUSTUP_HOME`); runner `support/run_probes.sh <spotbugs-4.10.5-dir> [workdir]`.

## Revalidation

1. **Diff the decision regions** at a newer revision: Error Prone `OperatorPrecedence.java` sets and `isConfusing` (52–102), `IntLongMath.java` skip list and constant exemption (91–115), `NarrowCalculation.java` (54–107), and the `ENABLED_*` membership in `BuiltInCheckerSuppliers.java`; SpotBugs `IDivResultCastToDouble.java` (51–73), the `BSHIFT` block of `FindPuzzlers.java` (344–374), `bugrank.txt`; Clang `SemaExpr.cpp` 16201–16385 and 9379–9491 plus the `DefaultIgnore`/`DefaultError` markers of the diagnostics in Finding 1.5; GCC `warn_about_parentheses`; Clippy `precedence.rs` match arms (71–111) and lint levels; Swift `Policy.swift` 390–436. Unchanged regions mean Findings 1–2 carry over.
2. **Rerun the probes:** `bash support/run_probes.sh /path/to/spotbugs-<ver>` with the toolchains to test on `PATH`, then diff `support/outputs/*.txt`; function-name labels map each changed line to a matrix cell. One full run took under 30 s on the probe host.
3. **Close source-only cells** by executing: Error Prone (`javac -Xplugin:ErrorProne`) on `Probe.java`; `clang -fsyntax-only` with and without `-Wall` on `probe.c` (source predicts c01, c02, c02b, c03, c13, c14, c15, c22 by default, c04–c07 added by `-Wall`, c12 an error); the three clang-tidy checks; `swiftc -typecheck` on Swift transliterations of c01, c02, c09, c11, c12, c22 and an ungrouped custom operator beside `+`.
4. Literature figures do not drift; re-check only if DOI metadata changes.

A passing rerun establishes only the probed cases, not field false-positive rates or recall for newer versions.
