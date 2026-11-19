# Parsing Expression Grammars, Left-Recursive Packrat Pathologies, and Unicode Source-Lexing Integrity

## Summary

Language front-ends built on Parsing Expression Grammars (PEGs) and Unicode-capable lexers trade classical Context-Free Grammar (CFG) declarativeness and ASCII visual bijection for deterministic top-down execution and internationalized source text—creating sharp metatheoretic and security pitfalls at both the grammar and lexical layers:

1. **PEG Ordered Choice, Silent Prefix Capture, and Metatheoretic Undecidability (Ford, POPL 2004):** Because PEG prioritized choice `e1 / e2` commits irrevocably to `e1` upon *local* success without backtracking across subsequent sequence failures, `e1 / e2` is non-commutative and silently shadows longer suffixes whenever `e1` matches a prefix of `e2`. For example, `A <- 'a' A 'a' / 'aa'`—which in a CFG generates all even-length strings $a^{2n}$ ($n \ge 1$)—in a PEG accepts **only** powers of two ($|w| = 2^k$, verified by execution for $2, 4, 8, 16$ while rejecting $6, 10, 12, 14, 18, 20$). Conversely, syntactic lookahead predicates (`&e`, `!e`) give PEGs Boolean closure and strictly surpass CFGs (recognizing $\{a^n b^n c^n \mid n \ge 1\}$), at the steep metatheoretic cost that **emptiness, equivalence, inclusion, and disjointness of PEG languages are all undecidable** (via reduction from CFG intersection / Post Correspondence Problem).
2. **Bytecode Parsing Machines vs. Memoized Left-Recursive Packrat Parsers (`LPeg`, `Ohm`, CPython `pegen`):**
   - `roberto-ieru/LPeg` (`089112f883540c4434e9e8e96de50a75f2b15f7e`) avoids Packrat memo-table memory overhead by compiling PEGs to a 26-opcode backtracking VM (`lpvm.h:16-43`) with FIRST/FOLLOW disjointness stack elision (`lpcode.c:678-713`), `IPartialCommit` $O(1)$-stack loops (`L822-851`), and static well-formedness rejection of *all* left-recursive cycles and nullable repetition loops (`verifyrule`, `checkloops`, `verifygrammar` in `lptree.c:1044-1155`).
   - Memoized left-recursive Packrat engines (Warth et al., PEPM 2008; `ohmjs/ohm`; CPython `pegen`) break left-recursion cycles by priming the memo slot at `(pos, rule)` with failure and iteratively "growing the seed" while consumed length strictly increases (`python/cpython` `Tools/peg_generator/pegen/parser.py:77-158`). However, Tratt (2010) and Medeiros et al. (SCP 2014) demonstrated that naive seed-growing **inverts operator associativity** on left-and-right-recursive rules: on `E <- E '-' E / N` and input `1 - 2 - 3`, seed-growing yields right-associative `(1 - (2 - 3))` (evaluating to `+2`) instead of left-associative `((1 - 2) - 3)` (`-4`), verified directly by execution. Furthermore, CPython `pegen` enforces a **single-leader feedback-vertex constraint** on multi-rule left-recursive SCCs (`Tools/peg_generator/pegen/grammar_analysis.py:109-136`) and omits memoization on non-leader SCC rules, sacrificing strict $O(n)$ worst-case Packrat bounds on pathological inputs in exchange for lower overhead.
3. **Unicode Source-Lexing Integrity (`UAX #9` Trojan Source, `UAX #31`, `UTS #39`, and `NFC` vs. `NFKC`):**
   - **BiDi reordering (`CVE-2021-42574`, Boucher & Anderson, USENIX Security 2023):** The 9 explicit Unicode Bidirectional formatting and isolate controls (`U+202A..U+202E`, `U+2066..U+2069`, category `Cf`) instruct UAX #9 display renderers to reorder visual glyphs without altering the compiler's logical token stream, decoupling human code review from compiled AST semantics across comments and string literals. `rustc` (`rust-lang/rust @ c884ecfbabb04b04fa5054dafc67ec258ecde745`) mitigates this by default via a SIMD `memchr(0xE2)` UTF-8 scan (`compiler/rustc_ast/src/util/unicode.rs:1-35`) feeding deny-by-default `TEXT_DIRECTION_CODEPOINT_IN_COMMENT` and `TEXT_DIRECTION_CODEPOINT_IN_LITERAL` lints, whereas executed **CPython `3.13.15` `ast.parse` silently accepts `U+202E` inside both comments and string literals** (rejecting it only in identifiers).
   - **Confusable identifiers & normalization divergence (`CVE-2021-42694`, `UAX #31`, `UTS #39`):** `rustc` applies **NFC** normalization to identifiers (`compiler/rustc_parse/src/lexer/mod.rs:1303-1310`) and runs crate-wide UTS #39 `GeneralSecurityProfile`, `skeleton(X)` (`CONFUSABLE_IDENTS`), and `AugmentedScriptSet` (`MIXED_SCRIPT_CONFUSABLES`) lints (`compiler/rustc_lint/src/non_ascii_idents.rs:154-392`), though `MIXED_SCRIPT_CONFUSABLES` is intentionally silenced once any non-confusable character of that script appears anywhere in the crate. In contrast, executed **CPython `3.13.15`** applies **NFKC** compatibility normalization to identifiers, silently aliasing mathematical bold `𝐚` (`U+1D41A`) and fullwidth `ａ` (`U+FF41`) to ASCII `a`, ligature `ﬁ` (`U+FB01`) to `fi`, and Kelvin `K` (`U+212A`) to `K`, while keeping Cyrillic `а` (`U+0430`) distinct—creating both silent identifier shadowing and cross-script homoglyph surfaces.

## Applicability

These findings apply to compiler front-ends, parser generators, DSL recognizers, static-analysis / formal-verification toolchains verifying syntax or source integrity, and CI/code-review security gates.

### Examined Subjects and Relationships

The subjects in `REPORT.json` span two coupled front-end strata (parsing metatheory/engines and lexical Unicode handling):

1. **PEG Theory & Parsing Machine / Packrat Cluster:**
   - **Formal foundations:** Ford (POPL 2004, DOI `10.1145/964001.964011`), Ierusalimschy (SPE 2009, DOI `10.1002/spe.892`), Warth, Douglass, & Millstein (PEPM 2008, DOI `10.1145/1328408.1328424`), Tratt (2010, Technical Report `EIS-10-01`), and Medeiros, Mascarenhas, & Ierusalimschy (SCP 2014, DOI `10.1016/j.scico.2014.01.013`, `arXiv:1207.0443v3`).
   - **Production implementations compared:** `roberto-ieru/LPeg` (`089112f883540c4434e9e8e96de50a75f2b15f7e`, static-checked VM without left recursion), `python/cpython` (`484bc16723ef534e693bcd13e139ccd710a64da4`, `pegen` single-leader SCC seed-growing parser), and `ohmjs/ohm` (`43c345b920c98b3eb13ce6b12df2b6ebd400b63b`, dynamic Warth-style `involvedSet` left-recursion memoizer).
2. **Unicode Lexical Integrity & Compiler Defense Cluster:**
   - **Normative specifications & security study:** Unicode UAX #9 (Bidirectional Algorithm), UAX #31 (Identifiers and Pattern Syntax), UTS #39 (Security Mechanisms), Boucher & Anderson (USENIX Security 2023, `arXiv:2111.00169v2`, `CVE-2021-42574`, `CVE-2021-42694`), and `nickboucher/trojan-source` (`e3dc153fcf465f4a84424ea874ff39be29adb1f7`).
   - **Compiler/runtime implementations compared:** `rust-lang/rust` (`c884ecfbabb04b04fa5054dafc67ec258ecde745`, lexer BiDi checks, NFC normalization, and UTS #39 `NonAsciiIdents` lints) contrasted directly against executed `CPython 3.13.15` (`Unicode 15.1.0`, `ast.parse` and `unicodedata`).

### Scope Conditions and Extension Arguments

- **Exact observations** apply to the pinned repository revisions, cited publications, and `CPython 3.13.15` runtime (`Unicode 15.1.0`).
- **Broader applicability:** PEG undecidability (emptiness, equivalence), prefix-capture non-commutativity, and seed-growing right-associativity on `E <- E op E / N` are mathematical theorems holding for *all* pure PEG and unguarded seed-growing Packrat implementations (`Basis: derived` from Ford 2004 and Medeiros et al. 2014). Likewise, UAX #9 BiDi decoupling holds for *any* language whose lexer treats comments/strings as opaque UTF-8 byte spans while code viewers render source lines through a compliant UAX #9 display engine.

## Findings

### 1. PEG Ordered-Choice Semantics, Prefix-Capture Shadowing, and Undecidability

`Basis: normative + execution + derived`

A Parsing Expression Grammar (Ford, POPL 2004, DOI `10.1145/964001.964011`) is a 4-tuple $G = (V_N, V_T, R, e_S)$ where $V_N$ is a finite set of nonterminals, $V_T$ is a finite alphabet, $R : V_N \to \mathcal{E}$ maps each nonterminal to a parsing expression, and $e_S$ is the start expression. Unlike CFGs (which define a generative relation $A \Rightarrow^* w$ and permit ambiguous parse trees), PEGs define a **deterministic partial recognition function** $(e, x) \Rightarrow o \in (V_T^* \times V_T^*) \cup \{\bot\}$ where $(x_{\text{consumed}}, x_{\text{rem}})$ splits $x = x_{\text{consumed}} \cdot x_{\text{rem}}$ on success and $\bot$ denotes failure:

$$\frac{(e_1, x) \Rightarrow (y, z)}{(e_1 / e_2, x) \Rightarrow (y, z)} \qquad \frac{(e_1, x) \Rightarrow \bot \quad (e_2, x) \Rightarrow o}{(e_1 / e_2, x) \Rightarrow o}$$

$$\frac{(e_1, x) \Rightarrow (y_1, x') \quad (e_2, x') \Rightarrow (y_2, z)}{(e_1\, e_2, x) \Rightarrow (y_1 y_2, z)} \qquad \frac{(e, x) \Rightarrow (y, z)}{(\&e, x) \Rightarrow (\varepsilon, x)} \qquad \frac{(e, x) \Rightarrow \bot}{(!e, x) \Rightarrow (\varepsilon, x)}$$

#### Consequence A: Non-Commutativity and Silent Prefix-Capture Shadowing

Because ordered choice `e1 / e2` never backtracks into `e2` once `e1` succeeds—even if a subsequent expression in an enclosing sequence fails—PEGs exhibit two silent specification hazards that CFG authors routinely miss:
1. **Direct prefix shadowing:** In `S <- ('a' / 'ab') 'c'`, the input `"abc"` is **rejected** because `'a'` succeeds at position 0, committing the choice; `'c'` then fails on `'b'`, and `'ab'` is never tried. Ordering alternatives longest-first (`'ab' / 'a'`) fixes finite literal choices, *but does not fix recursive prefix capture*.
2. **Recursive prefix capture (`A <- 'a' A 'a' / 'aa'`):** As a CFG, $A \to a A a \mid aa$ generates $\{a^{2n} \mid n \ge 1\}$. As a PEG, `A` greedily consumes leading `'a'` characters via recursive calls until hitting the end of the string, then unwinds matching `'aa'` at the innermost call that has two remaining `'a'`s, consuming a total length that satisfies the recurrence $L(k) = 2^k$. Executed verification (`Basis: execution`) confirms that across even lengths $2..20$:
   - **Full-string matches:** `[2, 4, 8, 16]` (exactly powers of two!).
   - **Rejected even lengths (length, silently consumed prefix):** `[(6, 4), (10, 4), (12, 8), (14, 12), (18, 4), (20, 8)]`.
   No syntactic warning is emitted by standard PEG tools for this divergence; the grammar remains well-formed and deterministic while silently shrinking its language from all even strings to $\{a^{2^k}\}$.

#### Consequence B: Beyond Context-Free Power and Metatheoretic Undecidability

Syntactic predicates `&e` and `!e` close PEG languages under complement (`!e`) and intersection (`&e1 e2`) without consuming input, enabling recognition of classic non-context-free languages such as $L = \{a^n b^n c^n \mid n \ge 1\}$:
```text
S <- &(A 'c') 'a'+ B !.
A <- 'a' A? 'b'
B <- 'b' B? 'c'
```
Executed verification (`Basis: execution`) confirms acceptance of `"abc"`, `"aabbcc"`, `"aaabbbccc"` and rejection of `"aabbc"`, `"aabbccc"`, `"abbc"`.

However, this exact intersection power implies **Ford's Undecidability Theorem (POPL 2004 §4.3):**
- **Emptiness ($L(G) = \emptyset$?) is undecidable.** Proof sketch (`Basis: normative + derived`): Every Deterministic Context-Free Grammar (and, more directly, every Post Correspondence Problem instance over pairs $(u_i, v_i)$) can be encoded as two unambiguous prefix-free PEGs $G_1$ and $G_2$ recognizing the upper and lower PCP encodings over the same index prefix; then the combined PEG $G_{\cap} \equiv \&(G_1\, !.)\, G_2\, !.$ recognizes $L(G_1) \cap L(G_2)$, which is non-empty if and only if the PCP instance has a solution. Since PCP is undecidable, PEG emptiness is undecidable.
- **Equivalence ($L(G_1) = L(G_2)$?), inclusion ($L(G_1) \subseteq L(G_2)$?), and disjointness ($L(G_1) \cap L(G_2) = \emptyset$?) are all undecidable** by immediate reduction from emptiness (`G` is empty iff $L(G) = L(\bot)$).
- **Engineering implication for grammar refactoring:** Unlike LL($k$)/LR($k$) CFGs (where emptiness is decidable in linear time and shift/reduce conflicts statically surface ambiguity), no compiler pass can automatically verify that reordering two PEG alternatives `e1 / e2` to `e2 / e1`, adding a rule to an ordered choice, or eliminating a dead branch preserves language semantics in general.

---

### 2. Bytecode Parsing Machines and Static Well-Formedness in `roberto-ieru/LPeg`

`Basis: documentation + source`

While Packrat parsers (Ford, ICFP 2002 / POPL 2004) guarantee $O(|w| \cdot |G|)$ worst-case time by memoizing every `(nonterminal, position)` pair, they pay $O(|w| \cdot |G|)$ heap space and cache-miss overhead. Roberto Ierusalimschy's `LPeg` (`Software: Practice and Experience` 2009, DOI `10.1002/spe.892`; inspected at `roberto-ieru/LPeg @ 089112f883540c4434e9e8e96de50a75f2b15f7e`) takes the alternative architecture: compiling PEGs into a compact **26-opcode Parsing Machine** (`lpvm.h:16-43`) that uses explicit backtracking stack frames without global Packrat memoization.

#### Compilation Patterns and Backtracking-Stack Optimizations (`lpcode.c`)

Direct inspection of `roberto-ieru/LPeg` `lpcode.c` establishes four load-bearing code-generation invariants:

1. **FIRST/FOLLOW Deterministic Choice Elision (`codechoice`, `lpcode.c:678-713`):** Before emitting a backtracking frame for `p1 / p2`, LPeg computes the 1-byte FIRST set `cs1` of `p1` (`getfirst(p1, fullset, &cs1)`). If `p1` can fail only on its very first byte (`headfail(p1)`) OR `p1` is non-nullable and its FIRST set is disjoint from `p2`'s FIRST/FOLLOW set (`cs_disjoint(&cs1, &cs2)` at `L683-L684`), LPeg **omits `IChoice`/`ICommit` entirely** and emits a zero-backtracking conditional jump (`ITestChar`/`ITestSet -> L1; <p1>; IJmp L2; L1: <p2>; L2:`). Only genuinely overlapping choices emit `IChoice L1; <p1>; ICommit L2; L1: <p2>; L2:` (`L701-L711`).
2. **Lookahead Predicates Without Heap Allocation (`codeand`, `codenot`, `lpcode.c:721-737, 861-875`):**
   - Positive lookahead `&p` compiles to `<p>; IBehind n` whenever `p` has fixed length $n \le \text{MAXBEHIND}$ and no captures (`L722-L727`), avoiding any stack push. Otherwise it emits `IChoice L1; <p>; IBackCommit L2; L1: IFail; L2:` (`L728-L736`), where `IBackCommit` restores the saved subject offset from the choice frame while jumping forward to `L2`.
   - Negative lookahead `!p` compiles to `test(fail(p)) -> L1; IFail; L1:` for `headfail(p)` (`L865-L866`), or `test(fail(p)) -> L1; IChoice L1; <p>; IFailTwice; L1:` (`L867-L873`), where `IFailTwice` pops the local choice frame and propagates failure to the enclosing choice frame if `<p>` succeeded.
3. **Constant-Stack Repetition (`coderep`, `lpcode.c:822-851`):** Compiling `p*` via naive recursive choice would push $O(|w|)$ stack frames. LPeg instead emits a single `IChoice L2` before the loop body and `IPartialCommit L1` at the back edge (`L842-L848`), which updates the *top* choice frame's saved subject position in place—keeping repetition stack depth at $O(1)$.
4. **Static Left-Recursion and Nullable-Loop Rejection (`lptree.c:1044-1155`):** Because a non-memoized recursive-descent VM diverges immediately on either left recursion ($A \leftarrow A \alpha$) or repetition of a nullable expression ($e^*$ where $\varepsilon \in L(e)$), `verifygrammar` (`lptree.c:1138-1155`) enforces two conservative static checks prior to bytecode emission:
   - `verifyrule` + `ruleentry` (`L1069-L1135`) performs a 3-color DFS (`RLNOTVISITED`, `RLBEINGVISITED`, `RLNULL`/`RLNONNULL`) over the grammar AST, recursing into the second operand of `TSeq` **only** if the first operand is nullable (`L1117-L1121`) and raising `"rule '%s' may be left recursive"` (`L1080`) on any cycle reaching a `RLBEINGVISITED` rule.
   - `checkloops` (`L1044-L1061`, called at `L1149`) walks every reachable rule and raises `"empty loop in rule '%s'"` (`L1151`) if any `TRep` node wraps a statically `nullable` child.
   - **Trade-off boundary:** Because `LPeg` does *not* memoize intermediate rule calls, grammars with overlapping non-disjoint recursive alternatives (exponential backtracking, e.g., pathological nested choices) can exhibit superlinear/exponential runtime in LPeg, whereas Packrat parsers cap runtime at $O(n)$ (for non-left-recursive grammars) at the cost of $O(n \cdot |V_N|)$ memo storage.

---

### 3. Left-Recursive Packrat Parsers, Seed-Growing Associativity Bugs, and CPython `pegen`

`Basis: documentation + source + execution`

Ford's original POPL 2004 well-formedness criterion forbids all direct and indirect left recursion. Because idiomatic expression grammars (`E <- E '-' N / N`) rely heavily on left recursion to express left-associative operators cleanly, three generations of algorithms extended Packrat parsing to handle left recursion—exposing subtle **associativity** and **complexity** pathologies.

#### Algorithm Comparison: Warth et al. (`Ohm`), CPython `pegen`, and Medeiros et al. (SCP 2014)

| Engine / Algorithm | Cycle Detection & Seed Mechanism | Indirect / Mutual Left Recursion | Associativity on `E <- E '-' E / N` (`1 - 2 - 3`) | Worst-Case Time Guarantee |
| :--- | :--- | :--- | :--- | :--- |
| **LPeg** (`roberto-ieru/LPeg @ 089112f8`) | Static DFS (`verifyrule`, `lptree.c:1099-1135`) rejects all left recursion at compile time. | **Unsupported** (compile error). | N/A (rejected). | Exponential on overlapping backtracking; $O(n)$ when FIRST/FOLLOW disjoint. |
| **Warth, Douglass, Millstein (PEPM 2008)** & **`ohmjs/ohm`** (`43c345b9`, `pexprs-eval.js:207-331`) | Dynamic call-stack detection (`posInfo.isActive(app)` -> `handleCycle` primes failure memo `value: false`), then `growSeedResult` loops while match grows, tracking `involvedSet` (`currentLR.isInvolved(memoKey)`) so involved rules are not prematurely memoized. | Supported dynamically (tracks all rules on active cycle via `updateInvolvedApplicationMemoKeys`, `L239`). | **Right-associative bug:** `(1 - (2 - 3))` (`+2`) (Tratt 2010 counterexample). | **Superlinear ($O(n^2)$+)** on nested/indirect left-recursive inputs because `involvedSet` entries must be re-evaluated across seed iterations. |
| **CPython `pegen`** (`python/cpython @ 484bc167`, `parser.py:77-158`, `grammar_analysis.py:109-136`, `Parser/pegen.c:95-135, 485-510`) | Static Tarjan SCC analysis (`compute_left_recursives`) marks each left-recursive SCC's `leader`; leader runs `memoize_left_rec` (`cache[key] = (None, mark)`, loop until `not result or endmark <= lastmark`). C runtime accelerates token memo lookup with a 64-bit `memo_mask` Bloom filter (`pegen.c:107, 496`). | **Restricted:** Multi-rule SCCs MUST possess a single `leader` vertex lying on *every* elementary cycle (`grammar_analysis.py:118-127`, else `ValueError`). Non-leader SCC rules are **not memoized** (`parser.py:20`). | **Right-associative bug** on `E <- E '-' E / N` (`(1 - (2 - 3))`); CPython's Python grammar avoids this by stratifying precedence levels (left-recursive at each level only on LHS, higher-precedence nonterminal on RHS). | Superlinear on left-recursive or non-leader SCC rules; $O(n)$ on strictly memoized non-LR rules. |
| **Medeiros, Mascarenhas, Ierusalimschy (SCP 2014, `arXiv:1207.0443v3`)** | Conservative bounded-depth operational semantics $A^k$ (depth bound $k$ incremented until fixed point) plus **precedence-level parameter** $E^p$ (`E^1 <- E^1 '-' E^2 / N` for left-assoc; `E^1 <- E^2 '^' E^1 / N` for right-assoc). | General direct and indirect left recursion with proved conservativeness over non-LR PEGs. | **Exact controllable associativity:** Left-associative `((1 - 2) - 3)` (`-4`) for `E^k op E^{k+1}`; right-associative for `E^{k+1} op E^k`. | Depends on memoization policy; bounded-depth semantics preserves exact PEG determinism without arbitrary right-bias. |

#### Executed Proof of Tratt's Associativity Counterexample (`Basis: execution`)

Why does naive seed-growing (`memoize_left_rec` in CPython `pegen` `parser.py:77-158` and Warth et al. PEPM 2008) invert associativity on the left-and-right-recursive rule `E <- E '-' E / N`?

Trace `1 - 2 - 3` starting at position `0`:
1. **Iteration 1 (seed phase at `pos = 0`):** `cache[(0, E)]` is primed to `(None, 0)`. The first alternative `E '-' E` calls `E` at `pos = 0`, receives the primed failure `None`, and backtracks to `N`, which matches `'1'` (`end = 1`). `cache[(0, E)]` is updated to `('1', 1)`.
2. **Iteration 2 (growth phase at `pos = 0`):** `E` restarts at `pos = 0`. The LHS `E` hits `cache[(0, E)]` and returns `('1', 1)`. `'-'` matches at `pos = 1`, advancing to `pos = 2`. Now the **RHS** calls `E` at **`pos = 2`**! Because no active left recursion is open at `pos = 2`, the nested call at `pos = 2` runs its *entire* own seed-growing loop from scratch on the remaining suffix `"2 - 3"`, consuming ALL of `"2 - 3"` and returning `('2', '-', '3')` at `end = 5`!
3. The outer call at `pos = 0` combines LHS `'1'` with RHS `('2', '-', '3')` to produce **`('1', '-', ('2', '-', '3'))`**, reaching EOF (`end = 5`). Iteration 3 cannot advance past `5`, so the loop terminates—locking in a **right-associative** tree even though the grammar was written with left recursion!

In contrast, when the RHS is strictly higher-precedence (`E <- E '-' N / N`, or Medeiros et al.'s precedence-climbing `E^1 <- E^1 '-' E^2 / N` where `E^2` cannot match `'-'`), the RHS at `pos = 2` stops after `'2'`, returning `('1', '-', '2')` at `end = 3`; Iteration 3 then consumes `'-' '3'` to produce `(('1', '-', '2'), '-', '3')`.

Observed execution output (`Python 3.13.15`):
```text
Input: 1 - 2 - 3
E <- E '-' N / N (seed-grow):              (('1', '-', '2'), '-', '3')  (eval = -4)
E <- E '-' E / N (seed-grow, Tratt bug!):  ('1', '-', ('2', '-', '3'))  (eval = +2, RIGHT-ASSOCIATIVE!)
E^1 <- E^1 '-' E^2 / N (Medeiros prec):    (('1', '-', '2'), '-', '3')  (eval = -4, LEFT-ASSOCIATIVE)
```

#### CPython `pegen` Single-Leader SCC Constraint (`grammar_analysis.py:109-136`)

Inspection of `python/cpython` (`484bc16723ef534e693bcd13e139ccd710a64da4`) reveals an architectural constraint rarely documented outside `pegen`'s source:
- `compute_left_recursives` (`Tools/peg_generator/pegen/grammar_analysis.py:109-136`) builds the initial-invocation graph `make_first_graph` (incorporating `compute_nullables` so edges traverse nullable prefixes) and computes Tarjan SCCs.
- For any multi-rule SCC (`len(scc) > 1`), it enumerates elementary cycles via `sccutils.find_cycles_in_scc` and intersects all cycle vertex sets (`leaders -= scc - set(cycle)`, `L123`). If the intersection is empty (e.g., an SCC with two cycles $A \to B \to A$ and $B \to C \to B$ plus $A \to C \to A$ with no single common node, or two disjoint sub-cycles joined by cross edges), `pegen` **refuses to generate the parser** with `ValueError("SCC ... has no leadership candidate")`.
- Even when a unique `leader` exists, `pegen` wraps *only* the leader with `memoize_left_rec` and strips memoization from the other SCC members (`parser.py:17-21`) to prevent intermediate seed values from polluting the memo cache—a deliberate simplification over Warth et al.'s `involvedSet` tracking that imposes worst-case exponential blowup if non-leader SCC rules backtrack repeatedly.

---

### 4. Unicode Bidirectional Visual Reordering (`UAX #9` / Trojan Source `CVE-2021-42574`)

`Basis: normative + source + execution + documentation`

Every mainstream compiler lexes source files as a **logical sequence of Unicode scalar values** (UTF-8 / UTF-16 code units in memory order), whereas code editors, terminals, and web diff viewers render each source line using the **Unicode Bidirectional Algorithm (UAX #9)** to support mixed left-to-right (LTR, e.g., Latin) and right-to-left (RTL, e.g., Arabic/Hebrew) scripts.

#### The 9 Explicit BiDi Control Codepoints (`CVE-2021-42574`)

Boucher and Anderson (*Trojan Source: Invisible Vulnerabilities*, USENIX Security 2023, `arXiv:2111.00169v2`, artifact `nickboucher/trojan-source @ e3dc153fcf465f4a84424ea874ff39be29adb1f7`) demonstrated that inserting **invisible formatting characters** (Unicode general category `Cf`) from UAX #9 inside comments or string literals—contexts where most language lexers accept arbitrary UTF-8 characters—causes UAX #9 renderers to permute visual token order across comment/string delimiter boundaries while leaving the lexer's logical parse tree unchanged.

The exact 9 explicit directional formatting and isolate codepoints (`Basis: normative + execution`, verified in Python `3.13.15` `Unicode 15.1.0` and `rust-lang/rust` `compiler/rustc_ast/src/util/unicode.rs:1-17`):

| Codepoint | UTF-8 Bytes | UAX #9 BiDi Class | Unicode Name | Structural Effect on Display Order |
| :--- | :--- | :--- | :--- | :--- |
| `U+202A` | `E2 80 AA` | `LRE` | LEFT-TO-RIGHT EMBEDDING | Pushes LTR directional embedding level on UAX #9 stack (max depth 125). |
| `U+202B` | `E2 80 AB` | `RLE` | RIGHT-TO-LEFT EMBEDDING | Pushes RTL directional embedding level. |
| `U+202C` | `E2 80 AC` | `PDF` | POP DIRECTIONAL FORMATTING | Pops matching `LRE`/`RLE`/`LRO`/`RLO` scope. |
| `U+202D` | `E2 80 AD` | `LRO` | LEFT-TO-RIGHT OVERRIDE | Forces strongly LTR character rendering, overriding inherent character directionality. |
| `U+202E` | `E2 80 AE` | `RLO` | RIGHT-TO-LEFT OVERRIDE | Forces strongly RTL reversal of all enclosed ASCII/Latin characters until `PDF` or newline. |
| `U+2066` | `E2 81 A6` | `LRI` | LEFT-TO-RIGHT ISOLATE | Opens isolated LTR directional run (prevents bleeding into surrounding text). |
| `U+2067` | `E2 81 A7` | `RLI` | RIGHT-TO-LEFT ISOLATE | Opens isolated RTL directional run (orders enclosed runs right-to-left). |
| `U+2068` | `E2 81 A8` | `FSI` | FIRST STRONG ISOLATE | Infers isolate direction from first strong directional character inside scope. |
| `U+2069` | `E2 81 A9` | `PDI` | POP DIRECTIONAL ISOLATE | Terminates matching `LRI`/`RLI`/`FSI` (and any unclosed inner embeddings/overrides). |

Because UAX #9 treats line terminators (`LF`/`CR`/`CRLF`) as paragraph separators that implicitly close unterminated directional scopes, an unclosed `RLI`/`RLO` placed inside a single-line comment or string literal affects visual ordering solely on that line without perturbing subsequent lines—enabling three conceptual visual-vs-logical divergence classes documented in `nickboucher/trojan-source` (`README.md:21-36`):
1. **Commenting-out inversion:** Executable statements appear visually inside a comment delimiter while logically sitting outside it.
2. **Stretched string literals:** Part of an executable comparison or branch appears visually inside a string literal while logically executing as code (or vice versa).
3. **Early-return reordering:** A `return` statement inside a line comment or preceding block visually swaps order with surrounding code tokens.

#### Compiler Defense Asymmetry: `rustc` vs. `CPython 3.13.15`

Direct source inspection of `rust-lang/rust` (`c884ecfbabb04b04fa5054dafc67ec258ecde745`) contrasted with execution on `CPython 3.13.15` exposes a stark ecosystem split:

- **`rustc` (`compiler/rustc_ast/src/util/unicode.rs:1-35`, `compiler/rustc_parse/src/lexer/mod.rs:557-694`, `compiler/rustc_lint_defs/src/builtin.rs:3908-3946`):**
  - Defines `TEXT_FLOW_CONTROL_CHARS` as the exact 9 codepoints above and scans every comment, doc comment, and string/char/cstr/raw literal via `contains_text_flow_control_chars`, using `memchr::memchr(0xE2, bytes)` to match `[0xE2, 0x80, 0xAA..=0xAE] | [0xE2, 0x81, 0xA6..=0xA9]` at SIMD speed with negligible overhead on ASCII source.
  - Emits **deny-by-default** (`Deny`) crate-level lints `TEXT_DIRECTION_CODEPOINT_IN_COMMENT` and `TEXT_DIRECTION_CODEPOINT_IN_LITERAL`, with machine-applicable suggestions to replace literal BiDi characters with explicit `\u{...}` escapes inside string literals.
  - **Residual boundary in `rustc`:** Implicit directional marks (`U+200E` `LRM`, `U+200F` `RLM`, `U+061C` `ALM`) and zero-width invisible formatters (`U+200B` ZWSP, `U+200C` ZWNJ, `U+200D` ZWJ) are *not* members of `TEXT_FLOW_CONTROL_CHARS`. While Rust's UAX #31 lexer rejects them inside identifiers, they remain silently allowed inside comments and string literals (where strong RTL characters from Arabic/Hebrew combined with `RLM` can still trigger implicit UAX #9 reordering).
- **`CPython 3.13.15` (Executed):**
  - `ast.parse("a\u202eb = 1")` and `ast.parse("a\u200bb = 1")` raise `SyntaxError(invalid non-printable character ...)`.
  - **However, `ast.parse("x = 1 # \u202e comment")`, `ast.parse('x = "\u202eabc"')`, and `ast.parse('x = "\u200eabc"')` all succeed silently without warning or error!** Consistent with PEP 672, CPython delegates BiDi-in-comments/strings detection to external linters, editors, and code-hosting platforms rather than enforcing it inside the interpreter.

---

### 5. `UAX #31` Identifiers, `UTS #39` Confusable Skeletons (`CVE-2021-42694`), and `NFC` vs. `NFKC` Hazards

`Basis: normative + source + execution`

Languages allowing internationalized identifiers typically adopt **UAX #31** (`XID_Start` / `XID_Continue`, designed to remain closed under Unicode normalization). Even when BiDi controls are completely blocked, two orthogonal lexical integrity hazards remain: **visual homoglyphs** (distinct Unicode sequences that render identically) and **normalization aliasing** (distinct source strings that the compiler silently merges into the same symbol).

#### `NFC` vs. `NFKC` Identifier Normalization Divergence

Unicode defines four normalization forms: canonical decomposition (`NFD`), canonical decomposition + composition (`NFC`), compatibility decomposition (`NFKD`), and compatibility decomposition + composition (`NFKC`). Compatibility forms (`NFKD`/`NFKC`) collapse formatting distinctions—superscripts, subscripts, ligatures, fullwidth forms, mathematical bold/italic letters, and circled letters—into plain ASCII sequences.

| Input Identifier | Codepoint(s) | `NFC` Form | `NFKC` Form | `rustc` (`c884ecfb`, NFC + `XID`) | `CPython 3.13.15` `ast.parse` (Executed, NFKC) | Security / Review Consequence |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `a` | `U+0061` | `'a'` | `'a'` | `Ident("a")` | `'a'` | Baseline ASCII identifier. |
| `𝐚` (Math Bold) | `U+1D41A` | `'𝐚'` | `'a'` | Allowed as `XID_Start`? No (`Not_NFKC` / rejected or flagged by `UNCOMMON_CODEPOINTS`) | **Silently collapsed to `'a'`** (`ast.parse("𝐚 = 1")` sets `id == 'a'`) | Visual decoy that aliases ASCII variable `a` in Python while failing naive ASCII grep/regex searches! |
| `ａ` (Fullwidth) | `U+FF41` | `'ａ'` | `'a'` | Distinct NFC symbol (flagged `UNCOMMON_CODEPOINTS`: `Not_NFKC`) | **Silently collapsed to `'a'`** | Keyword/variable aliasing invisible to byte-level static analyzers (`grep`, `sed`, regex SAST). |
| `ﬁ` (Ligature) | `U+FB01` | `'ﬁ'` | `'fi'` | Distinct NFC symbol (flagged `Not_NFKC`) | **Silently collapsed to `'fi'`** | Single-codepoint identifier expands into a 2-character ASCII identifier (`fi`). |
| `K` (Kelvin Sign) | `U+212A` | `'K'` (`U+004B`!) | `'K'` | Collapsed to `'K'` (canonical singleton decomposition in NFC) | **Collapsed to `'K'`** | Even strict NFC collapses singleton canonical equivalents (`U+212A` -> `U+004B`, `U+212B` Angstrom -> `U+00C5`). |
| `а` (Cyrillic Small A) | `U+0430` | `'а'` | `'а'` | Distinct symbol `'а'` (flagged `CONFUSABLE_IDENTS` / `MIXED_SCRIPT_CONFUSABLES`) | **Distinct symbol `'\u0430'`** (NO built-in warning!) | **Homoglyph shadowing (`CVE-2021-42694`):** Looks identical to ASCII `'a'` in most fonts, yet binds an entirely separate variable/function in both Rust and Python! |
| `é` (`e` + `U+0301`) vs. `é` (`U+00E9`) | `U+0065 U+0301` vs. `U+00E9` | Both `'é'` (`U+00E9`) | Both `'é'` (`U+00E9`) | Both normalized to `'é'` via `nfc_normalize` (`lexer/mod.rs:1303-1310`) | Both normalized to `'é'` | Canonical equivalence preserved without compatibility folding. |

*Key insight (`Basis: source + execution`):* Notice the dual trap:
- **NFKC (Python)** eliminates compatibility-character spoofing against identical identifiers (because `𝐚` and `a` become the same variable), **but** introduces **SAST/regex bypasses** where raw-source scanners looking for `eval`, `exec`, or sensitive symbol names miss `𝐞𝐯𝐚𝐥` (`U+1D41E U+1D42F U+1D41A U+1D425`), which CPython compiles directly to `eval`! Meanwhile, NFKC provides **zero protection** against cross-script homoglyphs (`U+0430` Cyrillic `а` vs. `U+0061` Latin `a`), because cross-script lookalikes are neither canonically nor compatibly equivalent.
- **NFC (Rust)** avoids unexpected compatibility aliasing (`compiler/rustc_parse/src/lexer/mod.rs:1303-1310`), and instead delegates security screening to dedicated **UTS #39** compiler lints.

#### Exact Audit of `rustc`'s UTS #39 `NonAsciiIdents` Lint Pass (`non_ascii_idents.rs`)

Direct inspection of `rust-lang/rust` (`c884ecfbabb04b04fa5054dafc67ec258ecde745`, `compiler/rustc_lint/src/non_ascii_idents.rs:14-392`) establishes the exact four-layer identifier defense architecture and its precise boundaries:

1. **`NON_ASCII_IDENTS` (`Allow` by default, `L37-L41`):** Optional strict ASCII-only policy gate (`#![forbid(non_ascii_idents)]`), which eliminates all non-ASCII homoglyph and normalization surfaces completely when enabled.
2. **`UNCOMMON_CODEPOINTS` (`Warn` by default, `L71-L75, L191-L235`):** Checks every non-ASCII identifier character against UTS #39 §3.1 `GeneralSecurityProfile::identifier_allowed`, explicitly classifying disallowed codepoints into `Exclusion`, `Technical`, `Limited_Use`, `Not_NFKC`, and `Restricted`.
3. **`CONFUSABLE_IDENTS` (`Warn` by default, `L110-L114, L238-L281`):** Computes the UTS #39 §4 `skeleton(X)` transform (`NFD -> prototype mapping from confusables.txt -> NFD`) over every distinct identifier in the crate's `symbol_gallery` and warns whenever two distinct symbols map to the same skeleton and at least one is non-ASCII (`!*existing_is_ascii || !is_ascii`, `L261`).
   - **Scope boundary (`Basis: source`):** `skeleton_map` only inspects identifiers appearing in the **same crate's** `symbol_gallery` (`L176`, `L239`). If a crate defines a spoofed function using Cyrillic `а` (`U+0430`) *without* also defining or referencing the Latin ASCII counterpart in the same crate (or if the target identifier lives only in an external dependency not interned in this crate's gallery), `CONFUSABLE_IDENTS` alone will not fire; `MIXED_SCRIPT_CONFUSABLES` is required as the backstop.
4. **`MIXED_SCRIPT_CONFUSABLES` (`Warn` by default, `L146-L150, L283-L390`):** Tracks each non-ASCII `AugmentedScriptSet` used across the crate (`Latin` is pre-seeded as `Verified`, `L295-L296`). Any script whose *only* characters appearing in the crate are `is_potential_mixed_script_confusable_char` triggers a warning (`L314-L329, L350-L388`).
   - **Subtle bypass boundary (`Basis: source + derived`):** Look at `L315-L319` and `L357-L366`: if the crate contains even a **single** legitimate, non-confusable character from a script $S$ (e.g., a single non-confusable Cyrillic or Greek identifier anywhere in the crate), `script_states[S]` transitions to `ScriptSetUsage::Verified`, permanently suppressing `MIXED_SCRIPT_CONFUSABLES` for *all* confusable characters of script $S$ across the entire crate! High-assurance codebases that do not require internationalized identifiers should therefore set `#![forbid(non_ascii_idents)]` (or enforce UTS #39 *Single-Script* / *ASCII-Only* restriction per identifier, not merely per crate).

---

### 6. Engineering & Verification Invariants for PEG and Unicode Front-Ends

`Basis: derived` (from Ford 2004, Medeiros et al. 2014, `LPeg`, `pegen`, `rustc`, and UAX #9/#31 / UTS #39)

1. **Disambiguate PEG Ordered Choices Explicitly:** Order prefix-overlapping literal alternatives longest-first (and ensure keyword rules terminate with an explicit negative identifier-character lookahead, e.g. `'if' !ident_cont`). Never transcribe a recursive CFG rule like `A -> a A a | aa` into a PEG without checking for greedy prefix capture against a differential test corpus.
2. **Stratify Operator Precedence Under Left-Recursive Packrat:** Never write unstratified left-and-right-recursive rules (`E <- E op E / N`) under Warth-style or `pegen`-style seed-growing parsers; always separate precedence levels (`E_k <- E_k op E_{k+1} / E_{k+1}` for left-associative operators, `E_k <- E_{k+1} op E_k / E_{k+1}` for right-associative operators) or adopt Medeiros et al.'s precedence-parameterized $E^k$ semantics. For `pegen`-based grammars, verify statically that every multi-rule left-recursive SCC has a dominating leader vertex—or refactor indirect left recursion into direct left recursion to preserve linear-time memoization.
3. **Treat Compiler-Level BiDi Rejection as Mandatory Defense-in-Depth:** Do not assume the language runtime blocks `CVE-2021-42574` inside comments or string literals (Python 3.13 does not). Enforce repository/CI-level rejection of all 9 explicit BiDi controls (`U+202A..U+202E`, `U+2066..U+2069`) **plus** implicit directional marks (`U+200E`, `U+200F`, `U+061C`) and zero-width invisible formatters (`U+200B..U+200D`, `U+FEFF` outside byte offset 0) in unescaped source text, requiring `\u{...}` / `\uXXXX` escapes inside string literals.
4. **Normalize Before Security Scanning & Lock Down Identifier Profiles:** Any SAST, secret scanner, or policy gate analyzing NFKC-normalizing languages (such as Python) MUST normalize identifiers using the target compiler's exact normalization form (`NFKC` for Python, `NFC` for Rust) *before* symbol matching, while concurrently running UTS #39 `skeleton(X)` and per-identifier (not merely per-crate) mixed-script checks—or enforcing ASCII-only identifiers (`#![forbid(non_ascii_idents)]` in Rust) for security-critical codebases.

## Boundaries

- **Other PEG implementations (`pest-parser/pest`, `kevinmehall/rust-peg`, `tree-sitter` GLR, `ANTLR4` ALL(\*)):** **not examined** in this report; `tree-sitter` uses GLR (not PEG) and `ANTLR4` uses adaptive LL(\*) with distinct left-recursion rewriting rules.
- **Native execution of `LPeg` C VM and `ohmjs/ohm` JavaScript runtime:** **not examined** by running Lua or Node.js binaries in this environment; findings for `roberto-ieru/LPeg` and `ohmjs/ohm` rest on direct source inspection (`Basis: source`) paired with peer-reviewed literature (`Basis: documentation`) and the standalone Python seed-growing reproduction (`Basis: execution`).
- **Automated decidability of restricted PEG subclasses (e.g., LL(1)-disjoint PEGs or non-recursive finite-state PEGs):** **not examined** in full; the undecidability theorems cited in Section 1 apply to general PEGs with lookahead predicates (`&e`, `!e`) and recursion, and are **known not to apply** to regular (non-recursive) or strictly LL(1)-disjoint subsets without arbitrary lookahead intersection.
- **Implicit BiDi reordering without explicit `Cf` controls (e.g., raw Arabic/Hebrew strong-RTL letters adjacent to ASCII operators in comments/strings):** **not examined** experimentally; note that `rustc`'s `TEXT_FLOW_CONTROL_CHARS` (`compiler/rustc_ast/src/util/unicode.rs:1-4`) deliberately covers only the 9 explicit embedding/override/isolate controls (`U+202A..U+202E`, `U+2066..U+2069`), so implicit RTL-script reordering inside comments is **unsupported** by that lint alone.
- **GCC, Clang, Go, javac, and V8/Node.js Trojan Source compiler mitigations post-2021:** **not examined** at current pinned commits; historical baseline vulnerability status in `nickboucher/trojan-source` (`README.md:21-63`) reflects the 2021–2023 evaluation versions documented in that repository and does not imply those toolchains remain unpatched today.
- **Unicode 16.0+ `confusables.txt` delta changes:** **unknown** — our executed Python probe used `CPython 3.13.15` bundled with `Unicode 15.1.0`, and `rustc` consumes its pinned `unicode-security` table revision; newly assigned Unicode 16.0+ confusable pairs were not audited.

## Evidence

### Primary Git Repository Sources (Observed 2026-11-19)

1. **`roberto-ieru/LPeg`** @ `089112f883540c4434e9e8e96de50a75f2b15f7e`
   - `lpvm.h:16-43`: Complete 26-opcode Parsing Machine ISA (`IAny` through `IEmpty`, including `IChoice`, `ICommit`, `IPartialCommit`, `IBackCommit`, `IFailTwice`, `IBehind`, `ICall`, `IRet`).
   - `lpcode.c:678-713`: `codechoice` FIRST/FOLLOW disjointness optimization (`headfail(p1) || (!e1 && cs_disjoint(&cs1, &cs2))`).
   - `lpcode.c:721-737`: `codeand` (`IBehind n` fast path vs. `IChoice`/`IBackCommit`/`IFail`).
   - `lpcode.c:822-851`: `coderep` (`IPartialCommit` constant-stack repetition loop).
   - `lpcode.c:861-875`: `codenot` (`IChoice`/`IFailTwice` negative lookahead).
   - `lptree.c:1044-1155`: `checkloops` (nullable `TRep` rejection), `ruleentry`, `verifyrule` (static DFS left-recursion check), and `verifygrammar`.
2. **`python/cpython`** @ `484bc16723ef534e693bcd13e139ccd710a64da4`
   - `Tools/peg_generator/pegen/parser.py:17-21, 77-158`: `logger` comment noting non-leader left-recursive rules are unmemoized; `memoize_left_rec` seed-growing loop (`self._cache[key] = None, mark`, iterating while `result` and `endmark > lastmark`).
   - `Tools/peg_generator/pegen/grammar_analysis.py:25-155`: `NullableVisitor`, `InitialNamesVisitor`, `make_first_graph`, and `compute_left_recursives` (Tarjan SCC decomposition + single-leader intersection check `leaders -= scc - set(cycle)` raising `ValueError` when no single vertex dominates all cycles).
   - `Parser/pegen.c:95-135, 485-510`: `_PyPegen_insert_memo`, `_PyPegen_insert_memo_direct`, `_PyPegen_update_memo`, and `_PyPegen_is_memoized` with 64-bit `memo_mask` Bloom filter (`1ULL << (type & 63)`).
3. **`ohmjs/ohm`** @ `43c345b920c98b3eb13ce6b12df2b6ebd400b63b`
   - `packages/ohm-js/src/pexprs-eval.js:207-331`: `Apply.prototype.eval`, `handleCycle` (`updateInvolvedApplicationMemoKeys`, `startLeftRecursion`), and `reallyEval` (`growSeedResult`, skipping memoization while `currentLR.isInvolved(memoKey)`).
4. **`rust-lang/rust`** @ `c884ecfbabb04b04fa5054dafc67ec258ecde745`
   - `compiler/rustc_ast/src/util/unicode.rs:1-35`: `TEXT_FLOW_CONTROL_CHARS` (exact 9 codepoints) and `contains_text_flow_control_chars` (`memchr::memchr(0xE2, bytes)` UTF-8 match).
   - `compiler/rustc_parse/src/lexer/mod.rs:557-694, 1303-1310`: `lint_unicode_text_flow`, `lint_doc_comment_unicode_text_flow`, `lint_literal_unicode_text_flow`, `report_text_direction_codepoint`, and `nfc_normalize`.
   - `compiler/rustc_lint_defs/src/builtin.rs:3908-3946`: `Deny`-by-default declarations of `TEXT_DIRECTION_CODEPOINT_IN_COMMENT` and `TEXT_DIRECTION_CODEPOINT_IN_LITERAL`.
   - `compiler/rustc_lint/src/non_ascii_idents.rs:14-392`: `NON_ASCII_IDENTS`, `UNCOMMON_CODEPOINTS` (UTS #39 `GeneralSecurityProfile`), `CONFUSABLE_IDENTS` (UTS #39 `skeleton`), and `MIXED_SCRIPT_CONFUSABLES` (`AugmentedScriptSet` crate-wide verification logic).
5. **`nickboucher/trojan-source`** @ `e3dc153fcf465f4a84424ea874ff39be29adb1f7`
   - `README.md:1-108`: Evaluated language vulnerability matrix (Early Return, Commenting-Out, Stretched Strings across 12 languages) and code-viewer matrix across 13 editors/platforms.

### Peer-Reviewed Literature and Normative Standards

- Ford, B. (2004). *Parsing Expression Grammars: A Recognition-Based Syntactic Foundation.* ACM POPL 2004. DOI: `10.1145/964001.964011`.
- Warth, A., Douglass, J. R., & Millstein, T. (2008). *Packrat Parsers Can Support Left Recursion.* ACM PEPM 2008. DOI: `10.1145/1328408.1328424`.
- Ierusalimschy, R. (2009). *A Text Pattern-Matching Tool based on Parsing Expression Grammars.* Software: Practice and Experience, 39(3):221–258. DOI: `10.1002/spe.892`.
- Tratt, L. (2010). *Direct Left-Recursive Parsing Expression Grammars.* Technical Report EIS-10-01, Middlesex University.
- Medeiros, S., Mascarenhas, F., & Ierusalimschy, R. (2014). *Left Recursion in Parsing Expression Grammars.* Science of Computer Programming, 96(2):177–190. DOI: `10.1016/j.scico.2014.01.013`; preprint `arXiv:1207.0443v3`.
- Boucher, N., & Anderson, R. (2023). *Trojan Source: Invisible Vulnerabilities.* 32nd USENIX Security Symposium. Preprint `arXiv:2111.00169v2` (DOI: `10.48550/arXiv.2111.00169`); tracked as `CVE-2021-42574` (BiDi) and `CVE-2021-42694` (homoglyphs).
- Unicode Consortium: UAX #9 (*Unicode Bidirectional Algorithm*), UAX #31 (*Unicode Identifiers and Pattern Syntax*), UTS #39 (*Unicode Security Mechanisms*).

### Reproducible Execution Probes (`CPython 3.13.15`, `Unicode 15.1.0`, Observed 2026-11-19)

```bash
python3 - <<'PY'
import ast, unicodedata

# 1. Ford prefix-capture shadowing: A <- 'a' A 'a' / 'aa'
def peg_even_a(s, pos):
    if pos < len(s) and s[pos] == 'a':
        p1 = peg_even_a(s, pos + 1)
        if p1 is not None and p1 < len(s) and s[p1] == 'a':
            return p1 + 1
    return pos + 2 if s[pos:pos+2] == 'aa' else None

print("powers_of_2:", [n for n in range(2, 22, 2) if peg_even_a('a'*n, 0) == n])

# 2. Seed-growing left-and-right recursion associativity counterexample
class P:
    def __init__(self, toks): self.t, self.p, self.c = toks, 0, {}
    def num(self):
        if self.p < len(self.t) and self.t[self.p].isdigit():
            v = self.t[self.p]; self.p += 1; return v
    def eat(self, x):
        if self.p < len(self.t) and self.t[self.p] == x:
            self.p += 1; return x
    def lr(self, name, body):
        m = self.p; k = (m, name)
        if k in self.c:
            r, e = self.c[k]; self.p = e; return r
        self.c[k] = (None, m); lr_res, lr_end = None, m
        while True:
            self.p = m; r = body(); e = self.p
            if r is None or e <= lr_end: break
            self.c[k] = lr_res, lr_end = r, e
        self.p = lr_end; self.c[k] = (lr_res, lr_end); return lr_res
    def E_both(self):
        def body():
            m = self.p; a = self.E_both()
            if a is not None and self.eat('-'):
                b = self.E_both()
                if b is not None: return (a, '-', b)
            self.p = m; return self.num()
        return self.lr("E", body)

print("E <- E '-' E / N on 1-2-3:", P(["1","-","2","-","3"]).E_both())

# 3. Python 3.13 NFKC & BiDi ast.parse checks
for src in ["\U0001D41A = 1", "\uFB01 = 1", "\u0430 = 1"]:
    print(repr(src), "-> AST id =", repr(ast.parse(src).body[0].targets[0].id))
for label, src in [("comment", "x = 1 # \u202e c"), ("string", 'x = "\u202ea"'), ("ident", "a\u202eb = 1")]:
    try: ast.parse(src); print(label, "-> ACCEPTED")
    except SyntaxError as e: print(label, "-> SyntaxError:", e.msg)
PY
```

Observed output:
```text
powers_of_2: [2, 4, 8, 16]
E <- E '-' E / N on 1-2-3: ('1', '-', ('2', '-', '3'))
'𝐚 = 1' -> AST id = 'a'
'ﬁ = 1' -> AST id = 'fi'
'а = 1' -> AST id = 'а'
comment -> ACCEPTED
string -> ACCEPTED
ident -> SyntaxError: invalid non-printable character U+202E
```

## Revalidation

To cheaply revalidate these findings on newer compiler/parser revisions:

1. **PEG & Packrat Left-Recursion Checks:**
   - Diff `roberto-ieru/LPeg` `lptree.c` (`verifyrule`, `checkloops`) to verify whether LPeg still statically forbids left recursion and nullable loops.
   - Diff `python/cpython` `Tools/peg_generator/pegen/grammar_analysis.py` (`compute_left_recursives`) and `Tools/peg_generator/pegen/parser.py` (`memoize_left_rec`) to check whether CPython relaxes the single-leader SCC requirement or adds precedence-parameterized left-recursion semantics.
   - Run Probe 2 (`E <- E '-' E / N` on `1 - 2 - 3`) against any target left-recursive PEG generator to verify whether it enforces left-associativity or exhibits Warth/Tratt right-associative grouping.
2. **Unicode Lexer & Compiler Lint Checks:**
   - Diff `rust-lang/rust` `compiler/rustc_ast/src/util/unicode.rs` (`TEXT_FLOW_CONTROL_CHARS`) and `compiler/rustc_lint/src/non_ascii_idents.rs` (`check_crate`) to confirm whether implicit BiDi marks (`U+200E`/`U+200F`/`U+061C`) or per-identifier mixed-script checks have been added.
   - Re-run the 6-line Python `ast.parse` snippet in the Evidence section on any newer CPython minor release to check whether BiDi controls in comments/strings remain accepted or emit warnings/errors, and whether identifier normalization remains `NFKC`.
3. **Scope of Revalidation:** Passing these targeted probes establishes only the tested grammar rules and codepoints; auditing an arbitrary language front-end still requires checking both its full lexer character tables (comment, raw-string, and preprocessor states) and its grammar compiler's handling of mutual left recursion and precedence.
