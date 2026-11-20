# Printer–parser inverses and rendering fidelity: Danielsson's correct-by-construction pretty-printing, invertible syntax descriptions, FliPpr, Lean 4 delaboration round trips, Rocq notation direction, and Naproche/ForTheL and Verbose Lean controlled natural language

## Summary

- **"The printer is the inverse of the parser" is never unconditional. Each system guarantees a weaker, precisely conditioned property:**
  - **Danielsson's Agda library** proves mechanically that every renderer's output lies in the grammar's language for the printed value: `parsable : (d : Doc g x) → x ∈ g · render d`. Parsing yields back exactly `x` only under an additional (local) unambiguity hypothesis (`correct-if-locally-unambiguous`). The shipped examples do not discharge that hypothesis.
  - **Invertible syntax descriptions** (Rendel–Ostermann style) give consistency only if every partial isomorphism's `apply`/`unapply` really are mutual inverses (the types do not enforce this) and the description is unambiguous. A naive top-down list-of-successes interpreter does not terminate on left recursion.
  - **FliPpr** derives a context-free grammar parser from a printer that uses biased choice. The parser returns *all* parses and accepts every alternative (for example redundant parentheses) while the printer emits only the preferred one, so `print ∘ parse ≠ id` on strings by design.
- **Lean 4's printer is not a parser inverse, and Lean says so.** `TopDownAnalyze.lean` (v4.35.0) states that the analyzer "is neither sound nor complete", and `pp.analyze` is off by default. I measured a print → re-parse → re-elaborate → compare check on all 50,421 theorem statements of `Init` and `Std` in the v4.35.0 toolchain:
  - With default options, 75.4% round-trip exactly (alpha-equivalent with identical binder annotations), 78.8% to a definitionally equal term, and 20.3% fail loudly (parse error, elaboration error, or `⋯` elision).
  - **0.93% (471) silently re-elaborate to a different, well-typed statement.**
  - `pp.analyze` lowers the silent rate to 0.65%, and adding `checkInstances` lowers it to 0.47%, at about 1.8–1.9× the cost.
  - `pp.all` gives 98.98% exact, 0 silent and 17 loud failures, but prints 3.5× more text.
  - The check costs 4.6–10.2 ms per statement on one core.
- **Three concrete Lean 4 v4.35.0 defects** were found and confirmed by direct re-elaboration:
  - **(a)** `BitVec.ofNatLT` has a *scoped* `#'` syntax but a *global* `app_unexpander`, so printed statements such as `0#'h = 0#w` do not parse outside `open BitVec` (`src/Init/Data/BitVec/Basic.lean:188–195`).
  - **(b)** Elided coercion targets turn an `Int` statement into a `Nat` statement (`BitVec.toNat_mod_cancel'`; 102 statements in that diff class).
  - **(c)** `∃ h, …` hides the binder type, so `Array.mapFinIdx_eq_iff` re-elaborates `h : ys.size = xs.size` as `h : (*...xs.toList.length).upper = ys.size`.
- **Rocq documents the same hazard on the notation side.** An `only printing` notation "may use notation and argument levels that differ … These differences can prevent printed terms from being parsed back correctly." Printing-only notations may carry multiple interpretations per scope, but parsing notations may carry only one.
- **Controlled natural language removes the second rendering of the statement, not the trusted translation.**
  - In **Naproche**, the ForTheL text is the checked input. Parsing is deliberately ambiguous. Translation to first-order logic happens inside the parser. An obligation counts as proved when the external prover prints a line starting `# SZS status Theorem`, with no proof object replayed.
  - In **Verbose Lean**, the controlled natural language is ordinary Lean syntax plus notation, checked by Lean's kernel. Its author documents a real misreading: `0 < 1` is silently elaborated over `ℕ` when students meant `ℝ`. The teaching evidence is explicitly "anecdotal".

## Applicability

- **Lean 4.** The source was read, and the probe executed, at `leanprover/lean4` `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. That is the commit reported by `lean --githash` for the released v4.35.0 toolchain used for every execution here. Behaviour at other Lean versions is **not examined**. The pretty-printer changes often between releases, so the numbers must not be extended to other versions without re-running the probe. The probe covers theorem *statements* (`ConstantInfo.type`) of public theorems whose defining module begins with `Init` or `Std`. Definitions' bodies, Mathlib, `Lean.*` modules, goals in the editor and hover output were not covered. Probe conditions: root namespace, no `open` declarations, `autoImplicit false`, the declaration's universe parameters in scope, `maxHeartbeats 200000` per stage, and the elaborator state restored after every theorem.
- **Rocq.** Documentation and source only, at `rocq-prover/rocq` `ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76` (`doc/sphinx/user-extensions/syntax-extensions.rst`, `interp/notation.ml`). No Rocq round-trip measurement was made.
- **Danielsson.** The Agda library `nad/pretty` was read at `975d543009aef6647319494df27081ec197caf88`. The library was not type-checked here; its statements are reported as written. The DTP 2013 paper (DOI verified) was not retrieved, so the README module that maps paper sections to modules stands in for it.
- **FliPpr.** `kztk-m/flippre` (package `flippre` 0.3.1) was read at `da2ed20723a88d82f072dbbefc9926de4e1814b5`; it was not built. The ESOP 2013, NGC 2018 and Haskell 2018 papers were verified by DOI. Only the Haskell 2018 abstract was read.
- **Rendel–Ostermann.** The paper was verified by DOI but its full text was not retrieved. The structure is reported from a third-party PureScript port that reproduces the paper's interfaces (`paulyoung/purescript-invertible-syntax` `81f4c91df215d4d17fc0b3abe13cf446649f4913` and `paulyoung/purescript-partial-isomorphisms` `7a53fd3248850ce92eba4b40094abf78247fd839`) and from a **toy model** written for this report. Neither is the original Haskell package.
- **Naproche.** Read at `naproche/naproche` `bdb727a2998c1a4cbaa51b9ea3678ba47a3fe56f`, together with the CADE 2021 system description (chapter page text). It was not run.
- **Verbose Lean.** Read at `PatrickMassot/verbose-lean4` `ea52f4bf6c60d986cb3fa2a5b7d7a8429b886eed`, whose `lean-toolchain` is v4.31.0, plus the ITP 2024 paper. The paper's PDF ships in that repository as `itp2024_paper.pdf` (SHA-256 `25f1f7de…c8c5`). The library was not built.
- **Execution host.** Linux x86_64, 96 logical CPUs (Intel Xeon @ 2.60 GHz), 236 GiB RAM. Each probe variant ran single-threaded in its own process with Lean's `-M 12288` memory option. Six variants ran concurrently, so the per-statement timings may include contention between them; that effect was not measured.

The subjects are compared as alternative mechanisms for one problem: making the rendering a human audits denote the statement a checker accepts. No combination is claimed.

## Findings

### 1. Properties to keep apart

Write *print* for the map from abstract values or terms to strings, *parse* for the map from strings to sets of values, and, for proof assistants, *elab* for the map from syntax to kernel terms.

| Property | Statement | Who provides it |
| :--- | :--- | :--- |
| P1 soundness of printing | `print x = s ⇒ x ∈ parse s` | Danielsson (any renderer, mechanized); FliPpr, Rendel–Ostermann (conditional) |
| P2 unique recovery | `print x = s ⇒ parse s = {x}` | Danielsson only with `Unambiguous g`, or locally unambiguous at `s` |
| P3 string normalization | `s ∈ dom parse ⇒ print (parse s) = s` | Nobody here; biased choice and layout freedom violate it by design |
| P4 Pollack-consistency (Wiedijk) | "a system being able to correctly parse formulas that it printed itself" (ENTCS 2012 abstract) | Lean partially, measured in §6 |
| P5 elaborated round trip | `elab (parse (print e)) ≡ e`, where ≡ is syntactic, alpha, or definitional | Lean's own tests use `isDefEq`; §6 measures all three |

For elaborated languages, P5's equality relation is the whole question. Definitional equality accepts re-generated auxiliary `match_` definitions and differently found proofs. Alpha-equivalence rejects them. Neither catches metadata the printer cannot show (§6.4). Basis: derived.

### 2. Danielsson: correct by construction (Agda, mechanized)

Source at `nad/pretty` `975d543009aef6647319494df27081ec197caf88`:

- **Documents are indexed by grammar and value.** `data Doc : ∀ {A} → Grammar A → A → Set₁` (`Pretty.agda:39`) has constructors `_◇_`, `text : Doc (string s) s` (line 50), `line : Doc (tt G.<$ whitespace +) tt` (line 54, meaning one *or more* whitespace characters), `group`, `nest`, `emb` and `fill`. A pretty-printer is `Pretty-printer g = ∀ x → Doc g x` (lines 89–90). A printer that produces the wrong value or the wrong syntax therefore fails to type-check.
- **The renderer contract** (`Renderer.agda:38–47`):

  ```agda
  record Renderer : Set₁ where
    field
      render   : ∀ {A} {g : Grammar A} {x : A} → Doc g x → List Char
      parsable : ∀ {A} {g : Grammar A} {x : A} (d : Doc g x) → x ∈ g · render d
  ```

  Therefore P1 holds for every renderer (`correct`, lines 55–58). `group` and `nest` are layout *hints* that "Renderers are free to ignore". The library includes an `ugly-renderer` (line 131) and a Wadler-style renderer (line 460), and P1 holds for both.
- **Unique recovery is conditional** (`Renderer.agda:60–79`; `Grammar/Infinite.agda:277–288`):

  ```agda
  Locally-unambiguous g s = ∀ {x y} → x ∈ g · s → y ∈ g · s → x ≡ y
  Unambiguous g = ∀ {s} → Locally-unambiguous g s
  Parser g = ∀ s → Dec (∃ λ x → x ∈ g · s)
  correct-if-locally-unambiguous : (parse : Parser g) (pretty : Pretty-printer g) → ∀ x →
    Locally-unambiguous g (render (pretty x)) → ∃ λ p → parse (render (pretty x)) ≡ yes (x , p)
  ```

- **Grammar class.** The README module says that the extended grammar type "is proved to be no more expressive" than the basic one, and that "every language that can be recursively enumerated can be represented by a (unit-valued) grammar". Expressiveness is therefore not the limit. Ambiguity is: unambiguity of such grammars is not decidable in general (derived), and no example module (`Examples/{Bool,Expression,Identifier,Identifier-list,Precedence,Tree,XML}.agda`) contains the string "unambiguous". **P2 is never discharged for the shipped examples.** Basis: source.
- **Layout freedom.** Any whitespace sequence satisfying `whitespace +` is allowed wherever `line` appears. The printed string is one of many members of the grammar's language for `x`. Basis: source.

### 3. Invertible syntax descriptions (Rendel–Ostermann style)

From the PureScript port, which reproduces the paper's interfaces (Basis: source of the port):

- `Iso a b` pairs `apply :: a -> Maybe b` (parser direction) with `unapply :: b -> Maybe a` (printer direction). Combinators include `***`, `associate`, `commute`, `unit`, `distribute` and `element` (`Control/Isomorphism/Partial/Prim.purs:12–70`). `class Syntax d` combines `IsoFunctor`, `ProductFunctor` (`<*>`) and `Alternative` (`<|>`, `empty`) with `pure` and `token` (`Text/Syntax/Classes.purs:9–24`).
- **Interpreters.** The printer is `newtype Printer a = Printer (a -> Maybe String)` with left-biased `alt` (`Printer/Naive.purs:13,21–22`). The parser is a list of successes, `newtype Parser a = Parser (String -> List (Tuple a String))`, and its `alt` concatenates results (`Parser/Naive.purs:12,24–25`). **Port-specific observation:** this port's `IsoFunctor` and `ProductFunctor` instances bind only the *head* of the inner parser's result list (`f s | Cons (Tuple x s') _ <- p s, …`, lines 16 and 21). `parse` returns a result only if that first branch consumed all input (lines 35–37). The port therefore does not explore all alternatives. The round trip depends on interpreter choices as well as on the description. This observation is about the port only, not the original Haskell library.
- **Conditions for consistency** (derived from the interfaces, and demonstrated by a **toy model**, `support/toy_invertible_syntax.py`, *not* the original library):

  | Test | Toy-model result |
  | :--- | :--- |
  | T0 left-recursive description `lr ::= lr 'x' | 'x'` | naive top-down parser raises `RecursionError` |
  | T1 list of numbers printed with no separator | `print([1,2]) = "12" = print([12])`; `parse "12" = [[1,2],[12]]`, so P1 holds and P2 fails |
  | T2 number of parses of `"1"*n` | 1, 2, 4, …, 512 for n = 1…10 (2^(n−1)) |
  | T3 the same with a `' '` separator | `parse "1 2" = [[1,2]]`, so P2 holds |
  | T4/T5 lawful vs non-lawful iso (unapply swaps operands) | lawful: round trip holds; non-lawful: `print (1,2) = "2,1"`, `parse` gives `(2,1)`, round trip fails silently and type-checks |
  | T6 biased choice `atom ::= number | '(' atom ')'` | `parse "((7))" = [7]` but `print 7 = "7"`, so P3 fails |
  | T7 partiality | `print (-3) = None`: values outside the printer's image have no rendering |

  Basis: execution of a toy model. These show the *logical* preconditions (lawful isos, unambiguity, no left recursion for top-down interpreters). They do not measure any real library.

### 4. FliPpr: deriving a CFG parser from a printer

Basis: source and documentation for `kztk-m/flippre` `da2ed207`.

- **Purpose.** The README says that FliPpr lets you "define pretty-printers in a functional programming style while ensuring they remain invertible to produce context-free grammar (CFG) parsers", and that "the current implementation relies on the `Earley` library for parsing".
- **Combinators.** The exported combinators include biased choice `(<?)` and `abort`, `case_` with `PartialBij`-based branches, and sharing and recursion primitives (`share`, `local`, `mfixF`, `letrs`). Layout comes from Wadler-style `Doc` combinators (`Text/FliPpr.hs` export list).
- **Example.** In `flippre-examples/Arith.hs`, `manyParens d = … d <? parens m` (lines 49–51) means:
  - the printer uses `d` without parentheses whenever it can;
  - the derived parser accepts any number of redundant parentheses.

  The derived parser has type `parseExp :: [Char] -> Err ann [Exp]` (line 97). It returns a *list*, so ambiguity surfaces as multiple results rather than being excluded statically. Numbers are printed and parsed through the `PartialBij` pair `dm10` (`divMod x 10` forward, `10 * d + r` backward). If such a pair is not truly inverse, the round trip breaks, exactly as in toy-model T5.
- **Haskell 2018 paper.** Its abstract (Semantic Scholar record) describes re-embedding FliPpr with Atkey et al.'s unembedding technique "to achieve a high level of interoperability with the host language". It makes no mechanized-proof claim. Whether the ESOP/NGC papers prove the derived parser correct on paper is **not examined**.
- **Shared examples.** Danielsson's `Examples/Expression.agda` reimplements "several examples based on Matsuda and Wang's 'FliPpr'". The two approaches can therefore be compared on the same grammars.

### 5. Comparison of the three printer–parser approaches

| | Danielsson | Rendel–Ostermann style | FliPpr |
| :--- | :--- | :--- | :--- |
| Guaranteed property | P1 for any renderer; P2 under (local) unambiguity | P1/P2 if isos are lawful and the description is unambiguous (port + toy) | parser derived from printer; returns all parses |
| Mechanically checked | yes (Agda types and proofs) | no proof accompanies the examined port | not examined (paper-level claims not read) |
| Grammar class | infinite grammars; any r.e. language (unit-valued) | whatever the interpreter supports; naive top-down rejects left recursion | context-free (Earley backend) |
| Ambiguity handling | hypothesis supplied by the user | interpreter-dependent (list or head) | multiple parses returned |
| Layout freedom | renderer chooses; `line` = one or more spaces | printer fixed; parser per description | biased choice: printer picks first, parser accepts all |
| Iso/inverse obligation | discharged by `Doc` indexing | on the user, unchecked | on the user (`PartialBij`), unchecked |

### 6. Lean 4 v4.35.0: delaboration, analyzer, parenthesizer, and a measured round-trip check

#### 6.1 What upstream documents

- **Analyzer.** `src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean:20–27` reads: "The top-down analyzer is an optional preprocessor to the delaborator that aims to determine the minimal annotations necessary to ensure that the delaborated expression can be re-elaborated correctly. Currently, the top-down analyzer is neither sound nor complete…"
  - `pp.analyze` defaults to `false` (lines 32–35).
  - `pp.analyze.checkInstances` defaults to `false`, with a TODO explaining that `MessageData` lacks the local instances (lines 37–44).
  - The trust knobs default to `true`: `trustOfNat` ("always 'pretend' `OfNat.ofNat` applications can elab bottom-up"), `trustOfScientific`, `trustSubtypeMk`, `trustId`, `trustKnownFOType2TypeHOFuns`, `omitMax` and `knowsType`.
  - `canBottomUp` is described as "incomplete (and possibly unsound) heuristics" (line 289).
  - `nameNotRoundtrippable` covers macro scopes, private names and numeric name components (lines 213–219).
  - **If the analysis throws, `topDownAnalyze` catches the exception, traces it under `pp.analyze.error`, and returns no annotations (lines 613–625).** The delaborator then proceeds as if analysis had not been requested.
- **Parenthesizer.** `Parenthesizer.lean:27` reads: "The Lean 4 grammar is unstructured and extensible with arbitrary new parsers, so in general it is undecidable whether parentheses are necessary or even allowed…". It handles Pratt-parser categories.
- **Coercions.** `Delaborator/Builtins.lean:1224–1228`: "instead of printing `ofNat n` we just print `↑n`, and when re-parsing this we can (usually) recover the specific coercion being used."
- **Lossy defaults** (`Delaborator/Options.lean`):
  - `pp.proofs` false: proofs print as `⋯`, line 179.
  - `pp.deepTerms` false: deep terms print as `⋯`, line 199.
  - `pp.maxSteps` 5000, line 15.
  - `pp.funBinderTypes` false, line 68.
  - `pp.coercions` true, which hides coercion functions, line 48.
  - `pp.numericTypes` false, line 97.
  - `pp.explicit`, `pp.universes` and `pp.fullNames` false.
- **Upstream's own round-trip tests are hand-picked.** The harness `checkM` in `tests/elab/PPRoundtrip.lean:13–27` prints, re-parses, re-elaborates and checks `isDefEq`. Line 32 records ``-- #eval checkM `(?m)  -- fails round-trip``, and line 38 has a TODO on universe metavariables. `tests/elab/PPTopDownAnalyze.lean` uses `isDefEq` under a message that says "roundtrip not structurally equal". Its disabled cases are `arrayMkInjEqSnippet` (line 323), a `Subtype` case (line 332), `Nat.mod_lt` "hangs" (line 362), `HEq.subst` (`blockImplicit` decided from the term's type, lines 365–367), `ExceptT.seqRight_eq` (universe constraints, line 369) and `Char.eqOfVeq` (explicit binders on a function whose type has implicit binders, line 373).

#### 6.2 The mechanical check (algorithm)

`support/RoundTrip.lean` implements:

```text
for each public theorem c in modules Init.*, Std.* (sorted by name):
  save elaborator state
  s  ← format (delab c.type) with variant options          -- delabErr if this throws
  if "⋯" ∈ s                       → omission
  stx ← Parser.runParserCategory env `term s                -- parseErr
  e' ← withoutErrToSorry (withLevelNames c.levelParams (elabType stx));
       synthesizeSyntheticMVarsNoPostponing; instantiateMVars
       (thrown or logged error, residual mvars, sorry)      → elabErr
  if e'.eqv c.type: exact if binder infos equal, else eqvOnly
  elif stripMData e' eqv stripMData c.type                  → mdataOnly
  elif isDefEq c.type e' (default transparency)             → defEqOnly
  else                                                      → notDefEq   (silent reinterpretation)
  restore elaborator state
```

The `notDefEq` class is the dangerous one: the printed text parses and elaborates **without any error** to a different statement. Restoring the state between theorems is essential. An earlier version without it leaked postponed universe constraints from one theorem into the next. That inflated `elabErr` from 3,580 to 32,969 in the generated-excluded variant, and the version was discarded.

#### 6.3 Measured results (v4.35.0, 2026-11-20)

| Variant (options) | Theorems | exact | mdataOnly | defEqOnly | **notDefEq** | elabErr | parseErr | omission | ms/thm | Printed chars | Max RSS |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| A default | 50,421 | 38,002 (75.37%) | 137 | 1,598 | **471 (0.93%)** | 4,887 | 679 | 4,647 | 5.39 | 8,735,698 | 5.20 GiB |
| B `pp.analyze` | 50,421 | 39,390 (78.12%) | 223 | 2,435 | **327 (0.65%)** | 2,361 | 611 | 5,074 | 9.82 | 9,964,411 | 5.26 GiB |
| E `pp.analyze` + `checkInstances` | 50,421 | 39,729 (78.79%) | 223 | 2,479 | **239 (0.47%)** | 2,037 | 604 | 5,110 | 10.23 | 10,038,483 | 5.32 GiB |
| F `pp.proofs` + `pp.deepTerms` | 50,421 | 41,413 (82.13%) | 154 | 2,261 | **480 (0.95%)** | 5,349 | 764 | 0 | 6.38 | 9,037,036 | 5.82 GiB |
| C `pp.all` | 50,421 | 49,909 (98.98%) | 408 | 87 | **0** | 9 | 6 | 2 | 4.59 | 30,815,523 | 12.09 GiB |
| D default, generated theorems excluded | 46,449 | 36,125 (77.77%) | 134 | 1,293 | **453 (0.98%)** | 3,580 | 671 | 4,193 | 5.46 | 7,658,189 | 4.90 GiB |

`delabErr` and `eqvOnly` were 0 in every variant. Basis: execution. Derived ratios:

- `pp.all` prints 3.53× more characters than the default.
- `pp.analyze` costs 1.82× default time, and 1.90× with `checkInstances`.
- Default throughput is 185.6 statements/s, which covers `Init` + `Std` in 272 s on one core.
- Max RSS includes the baseline cost of loading the `Lean` environment: a 31-theorem smoke run peaked at 1,584,568 KB. The 12 GiB for `pp.all` was not attributed further.

#### 6.4 Failure taxonomy (default variant A)

Categories come from a separate full catalog run (`RTProbe.catalog`) with identical options. Counts are of statements whose first error message or first differing subterm matches the category.

- **Silent reinterpretation (`notDefEq`, 471 total)** — every example below was re-elaborated by hand:
  - Elided coercion target, 102 statements. Example: `BitVec.toNat_mod_cancel'` prints `↑x.toNat % ↑(2 ^ n) = ↑x.toNat`. The original is `(↑x.toNat : Int) % (↑(2 ^ n) : Int) = (↑x.toNat : Int)`. The printed text re-elaborates to the `Nat` statement `x.toNat % 2 ^ n = x.toNat`, with every coercion silently dropped.
  - Numeric literals with no type anchor, 39 statements. Example: `Lean.Grind.AddCommGroup.neg_zero` prints `-0 = 0` for an arbitrary `M` and re-elaborates as `(-0 : Int) = (0 : Int)`. Lean's unused-variable linter then warns that the binder `inst` is unused, which is a free partial detector for this class. Under `pp.analyze` the same mechanism turns `Array.prod #[] = 1` into `#[].prod = (1 : Nat)`. That is consistent with `pp.analyze.trustOfNat := true`.

    The texts were re-elaborated in support `Cases3.lean` with `pp.numericTypes true`.
  - `Fin` vs `Nat` through `↑`, 24 statements (`Fin.and_val`).
  - Hidden `∃` binder types. Example: `Array.mapFinIdx_eq_iff`. Its default output reads `… ↔ ∃ h, ∀ (i : Nat) (h_1 : i < xs.size), ys[i] = f i xs[i] h_1`. With `pp.funBinderTypes true` the original reads `∃ (h : ys.size = xs.size), …`. Re-elaborating the default text gives `∃ (h : (*...xs.toList.length).upper = ys.size), …` (support `Cases2.lean`). `h` is used only inside an invisible array-bounds proof, so its statement is unrecoverable from the text.
- **Loud failures:**
  - 1,156 × structure-instance notation without a known type, mostly generated `inj`/`injEq` lemmas, for example `{ toList := toList } = { toList := toList_1 }`.
  - 585 × residual metavariables, for example `@Acc.ndrecOn = @Acc.ndrecOnC`, whose universe arguments are unconstrained.
  - 491 × stuck `Std.Iterator` instances.
  - 314 × field notation on `∅` (`∅.insert k v`).
  - 312 × elided bounds proofs that `get_elem_tactic` cannot rediscover (`xs[xs.size - 2]` under `h : 0 < xs.pop.size`).
  - Unapplied polymorphic operators with no type anchor: 24–33 statements each for `HAdd`, `HMul`, `HOr` and `HAnd` (for example `Std.Associative fun x1 x2 => x1 * x2`), and 39 for `Pure`.
- **Parse failures (679):**
  - 106 statements print the scoped `#'` syntax.
  - The remainder include `Std.Do` notations such as `⦃P⦄ x ⦃Q⦄` and `⊢ₛ`, which were not individually diagnosed.
- **Upstream defect (a), exact source.** `src/Init/Data/BitVec/Basic.lean`:

  ```lean
  188  /-- Notation for bitvector literals without truncation. `i#'lt` is a shorthand for `BitVec.ofNatLT i lt`. -/
  189  scoped syntax:max term:max noWs "#'" noWs term:max : term
  190  macro_rules | `($i#'$p) => `(BitVec.ofNatLT $i $p)
  ...
  193  @[app_unexpander BitVec.ofNatLT] meta def unexpandBitVecOfNatLt : Lean.PrettyPrinter.Unexpander
  194    | `($(_) $i $p) => `($i#'$p)
  ```

  The syntax is `scoped`, but the unexpander attribute is not, so `#check @BitVec.ofNatLT_zero` prints `0#'h = 0#w` in the root namespace. Feeding that text back gives `error: missing end of character literal`. It parses under `open BitVec in`. Basis: source + execution.
- **Definitional-only matches (1,598):**
  - re-generated auxiliary `match_` definitions (a fresh matcher in the probe's module versus, for example, `Array.foldl_filterMap'.match_1`);
  - proofs found by a different route (`Nat.lt_of_le_of_lt …` versus `Decidable.byContradiction`);
  - universe-level normal-form order (`max u_2 u_1` versus `max u_1 u_2`).
- **Metadata-only matches (137).** These are `Expr.mdata` nodes `borrowed := true`, the FFI borrow marker on a binder type. No printer option renders it, so any round trip strips it.
- **`pp.all` residue:**
  - 9 elaboration errors: binder types containing `autoParam`, in the `Nat.dfoldRev_*` family.
  - 6 parse errors: "unexpected identifier after decimal point; consider parenthesizing the number".
  - 87 definitional-only matches: `Expr.proj` printed as `.2` re-elaborates to a `PProd.snd` application, and implicit lambdas are eta-expanded.

#### 6.5 Cost and coverage of the check

On one core, the check covers 100% of public `Init`/`Std` theorem statements of the toolchain in 4–9 minutes, depending on options. It is embarrassingly parallel per declaration; parallel speed-up was not measured. The check is itself unverified meta-code that runs inside the elaborator. A `notDefEq` verdict is a *detector* hit. An `exact` verdict only shows that this printer–elaborator pair agrees under these options and scope; it is not a proof that a human reads the same statement. Basis: execution + derived.

### 7. Rocq: notation direction modifiers

Basis: documentation + source at `rocq-prover/rocq` `ddb69e5c`.

- **Default direction.** "The default for a notation is to be used both for parsing and printing", and `only parsing` / `only printing` restrict this (`syntax-extensions.rst:436–444`).
- **Interpretations per scope.** "Notations used for parsing … can have only a single interpretation per scope. On the other side, notations marked with `only printing` can have multiple associated interpretations, even in the same scope" (lines 450–455).
- **Levels.** Lines 457–459: "An `only printing` notation may use notation and argument levels that differ from other declarations for the same string. These differences can prevent printed terms from being parsed back correctly." The incompatible-level warning is emitted "because different printing levels can make printed terms ambiguous or cause them to be parsed as different terms" (around line 466).
- **Non-reversible notations** (line 401: "This notation is not reversible, it will not be used for printing") cover tactics-in-terms and `:>` casts.
- **Notation selection.** The notation that captures the largest subterm is preferred, then the most recent one. "If the notation is in a scope … either the scope has to be opened or a delimiter has to exist in the scope for the notation to be usable" (lines 470–486). This is the scope-awareness that Lean defect (a) lacks.
- **Data structure.** In `interp/notation.ml:84–95`, each scope maps a notation string to `parsing_notation_data` (`NoParsingData | OnlyParsingData | ParsingAndPrintingData`, holding one interpretation) and to `extra_printing_notation_data`, a *list*. `update_notation_data` (line 478) pushes `OnlyPrinting` entries onto that list. **Printing and parsing are therefore structurally asymmetric by design.**

### 8. Controlled natural language front ends

#### 8.1 Naproche (ForTheL)

Basis: source + documentation.

- **What the human reads is what is parsed.** ForTheL `.ftl` or `.ftl.tex` text is checked directly, so there is no separate printed rendering of the statement to compare.
- **Trusted steps.** The CADE 2021 description says: "We allow ambiguous parsing, since it better fits natural language. Currently the translation into tagged first-order logic is already part of the parsing process." ForTheL notions are "internally represented as predicates" ("types as predicates"). Obligations are exported to TPTP and sent to E by default; SPASS and Vampire are also available.
  - `src/Naproche/Prover.hs:122–145` (`prover_status`) classifies the prover's stdout by line prefix. `eprover_messages` (lines 175–181) sets `_success = ["# SZS status Theorem"]`.
  - With `by_contradiction`, `ContradictoryAxioms` also counts as success (line 139).
  - **No proof object is returned or checked.**
  - Default time limits are 1 s per ontological check and 3 s per proof attempt (CADE 2021 §5.5).
  - "From the perspective of logic, there is no connection of Naproche with Isabelle/Sledgehammer or any other Isabelle/HOL tools." Isabelle supplies the editor (PIDE) and process management only.
- **Known language-level ambiguity** (`TODO.md:37–38`): "writing something along the line of `there exist x,y,z such that ...` results in an ambiguity error."
- **Misreading evidence.** No user study of misreadings was found in the examined sources (**unknown**).

#### 8.2 Verbose Lean

Basis: source + documentation.

- **What is checked.** Statements and proofs are Lean syntax extended by notation and tactics, so Lean's kernel checks them. The controlled natural language affects the *proof script* reading. The statement still passes through Lean elaboration.
- **Notation and printing overrides.** `Verbose/Tactics/Notations.lean` adds `notation:25 (priority := high) a:26 " ⇒ " b:25 => a → b` and an `infix " ⇔ "` (lines 12–14). It also adds custom delaborators. `delabPi` rewrites `∀ (x : _), x > z ⇒ body` to `∀ x > z, body` (lines 27–53), which *drops the printed binder type* and relies on inference from `z` to recover it.
- **Documented misreading** (ITP 2024 paper, §4.1): "We have seen students feeling the need to state as an intermediate fact something like 0 < 1 … Lean will interpret the above statement as an inequality of natural numbers and our tactics will happily prove it. But then using this intermediate fact will fail if the intended meaning was an inequality of real numbers." The paper mentions an option named `pp.numeralTypes`. In the v4.35.0 source the option is `pp.numericTypes` (`Options.lean:97`), so the name differs. The paper also describes overriding the division symbol in teaching files so that it always means real division. That is a deliberate change of meaning hidden behind a standard symbol.
- **Evidence strength.** The library has been "used for five years in University Paris-Saclay at Orsay". The conclusion states "One limitation of those experiments, besides their anecdotal nature, is that we did not try to use this tool with really weak students". A rigorous assessment with education specialists is announced as future work. The author also argues that controlled natural language is "not sufficiently efficient as a general input format" and that readable access to formal mathematics is better served "by translating formalized mathematics to natural language a posteriori".

### 9. What the human reads, what is checked, what stays trusted

| Front end | Human reads | Checked object | Trusted translation steps | Misreading evidence |
| :--- | :--- | :--- | :--- | :--- |
| Lean, default printing | delaborated text (hidden implicits, coercions, binder types, proofs) | kernel term | delaborator, parenthesizer and formatter for the reader; elaborator for the author | measured: 0.93% of `Init`/`Std` statements silently differ on re-elaboration (§6.3) |
| Lean, `pp.all` | fully explicit text, 3.5× longer | kernel term | as above | measured: 0 silent; 17 loud failures in 50,421 |
| Naproche/ForTheL | the source text itself | first-order translation discharged by an external ATP | ambiguous parser plus first-order translation; ATP verdict line | none found |
| Verbose Lean | controlled-natural-language script plus Lean statement notation | kernel term | Lean elaborator plus Verbose notations and delaborators | one documented student case (`0 < 1`); anecdotal |
| Danielsson-style printer | rendered string | the value `x` (by construction) | the unambiguity proof (user-supplied) | not applicable |

Basis: derived from §2–§8.

### 10. Performance and resource footprint (L1–L6)

| Level | Item | Value | Basis |
| :--- | :--- | :--- | :--- |
| L1 authoring | Writing a Danielsson printer or a FliPpr description | not measured (no LoC or person-time data examined) | — |
| L1 | Annotation burden of `pp.all` review | 611 vs 173 printed characters per statement (3.53×) | execution + derived |
| L2 toolchain build | Building Lean, Rocq, Agda library, flippre | not measured (released Lean toolchain used) | — |
| L3 elaboration | Round-trip check per statement | 4.59–10.23 ms single core (§6.3) | execution |
| L3 | Naproche default ATP limits | 1 s ontological, 3 s proof per attempt | documentation |
| L3 | Toy-model ambiguity growth | 2^(n−1) parses for n digits without separators | execution (toy) |
| L4 generated code | — | not applicable (printing does not affect generated code) | known not to apply |
| L5 checking | Kernel re-check of re-elaborated statements | not measured separately (included in L3 time) | — |
| L5 | Naproche ATP certificate checking | none: verdict accepted from stdout | source |
| L6 memory | Probe max RSS | 4.90–5.82 GiB; 12.09 GiB for `pp.all` | execution |

### 11. Human comprehensibility (C1) and model refinement (C2)

- **C1.** Hidden information is the main hazard for a reader: binder types of `∃`, coercion targets, numeric-literal types, implicit universe arguments and elided proofs. Every silent-reinterpretation class in §6.4 corresponds to information the default printer omits. The checker's verdict is legible: a first-differing-subterm pair such as `orig: Int | reelab: Nat`. A reader looking at the printed statement alone cannot see the problem. `pp.all` removes the silent class but makes statements 3.5× longer, which raises working-memory load. A per-statement *differential* display is a cheaper middle ground: default text, plus explicit annotations only where the round trip fails. That middle ground is **not examined**. Basis: derived.
- **C2.** The orthogonal invariant is "the audited text must elaborate, in the audit context, to the checked term". Lean currently spreads this over several partial mechanisms: unexpanders, scoped syntax, `pp.*` options, the analyzer and the parenthesizer. None of them is checked against the invariant, and the analyzer fails open (§6.1). The minimal universal mechanism is the round-trip check itself, used as the *acceptance criterion* for a rendering. Analyzer annotations then become an optimization whose failures are caught, not trusted. The scoped-notation defect is one instance of a missing invariant, namely "an unexpander may only emit syntax that is parseable in the printing scope". Rocq states that invariant for printing in scopes; Lean does not enforce it. Danielsson's design makes P1 a typing obligation, while P2 stays a separate proof obligation that cannot be folded away. Basis: derived.

### 12. Validation (V1–V4)

- **V1 specification adequacy.** The round-trip check is a non-vacuity test of the *rendering*. A statement that does not survive print → elaborate is not the statement the reader reviewed. The toy-model T5 case, a well-typed but non-lawful iso, shows why the lawfulness of partial isomorphisms needs property-based testing. No `QuickCheck`/`QuickChick` suites for flippre or the PureScript port were examined (**not examined**).
- **V2 checker soundness.** The probe is differential: printer versus parser plus elaborator. It found defect (a), confirmed by an independent manual `#check`. The probe's own soundness rests on `Expr.eqv`, `isDefEq` and the state-restore discipline. One earlier probe defect, leaked postponed constraints, was found and fixed before the reported runs.
- **V3.** Not applicable.
- **V4 human comprehension.** The only behavioural evidence found is the Verbose teaching report (anecdotal) and Wiedijk's observation that Pollack-inconsistency "happens regularly". No controlled study of how mathematicians read pretty-printed Lean statements was found (**unknown**).

## Boundaries

- **Not examined:**
  - The full text of the Danielsson DTP 2013, Rendel–Ostermann 2010, FliPpr ESOP 2013 and NGC 2018 papers, so their exact paper-level theorem statements are not quoted here.
  - Type-checking `nad/pretty`, and building flippre.
  - Running Naproche or Verbose.
  - Rocq round-trip measurement.
  - Lean `Lean.*` modules, Mathlib, definitions' bodies, goal display and hover.
  - Lean versions other than v4.35.0.
  - Parallel speed-up of the check.
  - The `Std.Do` parse-failure group beyond its examples.
  - A differential-annotation printer.
- **Unknown:**
  - Whether any FliPpr paper proves the derived parser correct mechanically.
  - Misreading rates among human reviewers of default Lean output. The 0.93% figure is a machine re-elaboration rate, not a human error rate.
  - Whether `pp.analyze` fails open on any statements in the probe, because the `pp.analyze.error` trace was not collected.
- **Known not to apply:** The Lean results do not transfer to Rocq, and vice versa. Rocq's only-printing semantics differ structurally (§7).
- **Unsupported (by the subject):**
  - Lean's printer does not guarantee P4/P5, as stated upstream.
  - The default printer cannot render `mdata` such as `borrowed`.
  - Naproche does not replay ATP proofs.
- **Stronger conclusions the evidence does not establish:**
  - That `pp.all` output is what humans *should* review. Its exactness is measured, its readability is not.
  - That `exact` round trips mean the reader understood the statement.
  - That the toy-model results describe the original invertible-syntax library.
  - That controlled natural language reduces misreadings. No controlled study was found.

## Evidence

All sources and executions were acquired 2026-11-20 (UTC).

- **leanprover/lean4** `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (v4.35.0):
  - `src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean:20–27, 32–95, 213–219, 287–308, 578–593, 613–625`.
  - `src/Lean/PrettyPrinter/Delaborator/Options.lean:15–17, 19–22, 48–50, 68–70, 97–99, 179–181, 199–201`.
  - `src/Lean/PrettyPrinter/Delaborator/Builtins.lean:1224–1259` (`coeDelaborator`).
  - `src/Lean/PrettyPrinter/Parenthesizer.lean:20–34`.
  - `src/Init/Data/BitVec/Basic.lean:188–195`.
  - `tests/elab/PPRoundtrip.lean:13–38`; `tests/elab/PPTopDownAnalyze.lean:11–36, 323–375`.
- **rocq-prover/rocq** `ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76`: `doc/sphinx/user-extensions/syntax-extensions.rst:401–405, 436–486`; `interp/notation.ml:81–95, 478–491`.
- **nad/pretty** `975d543009aef6647319494df27081ec197caf88`:
  - `Pretty.agda:39–90`.
  - `Renderer.agda:38–111, 131–186, 460`.
  - `Grammar/Infinite.agda:275–288`.
  - `README.agda`; `README/Correct-by-Construction-Pretty-Printing.agda`.
  - `Examples/*.agda`, searched for "unambiguous": 0 hits.
- **kztk-m/flippre** `da2ed20723a88d82f072dbbefc9926de4e1814b5`: `README.md`; `flippre/src/Text/FliPpr.hs` (export list); `flippre-examples/Arith.hs:42–99`; `flippre/flippre.cabal` (version 0.3.1).
- **paulyoung/purescript-partial-isomorphisms** `7a53fd3248850ce92eba4b40094abf78247fd839`: `src/Control/Isomorphism/Partial/Prim.purs`.
- **paulyoung/purescript-invertible-syntax** `81f4c91df215d4d17fc0b3abe13cf446649f4913`: `src/Text/Syntax/{Classes,Parser/Naive,Printer/Naive}.purs`.
- **naproche/naproche** `bdb727a2998c1a4cbaa51b9ea3678ba47a3fe56f`: `README.md`; `src/Naproche/Prover.hs:52–58, 110–181`; `TODO.md:37–38`.
- **PatrickMassot/verbose-lean4** `ea52f4bf6c60d986cb3fa2a5b7d7a8429b886eed`: `Verbose/Tactics/Notations.lean:12–53`; `lean-toolchain`; `README.md`; `itp2024_paper.pdf` (§4.1, §7).
- **Papers.** DOIs were verified on 2026-11-20 against Crossref (Danielsson, Rendel–Ostermann, the three FliPpr papers, Wiedijk, De Lon et al., Ullrich–de Moura 10.1007/978-3-030-51054-1_10, de Moura–Ullrich 10.1007/978-3-030-79876-5_37) and against DataCite (Massot). The Ullrich–de Moura and de Moura–Ullrich papers are cited as context only; their content was not examined. Wiedijk is quoted from the abstract. The De Lon et al. quotations come from the publisher chapter page text.
- **Execution.** Support files are in `support/`:

  ```console
  # Lean v4.35.0 (lean --githash = eb6cafb7290e8bd5f2937522d8d804f58f02bafc)
  # one file per variant = support/RoundTrip.lean + one driver line from support/drivers.txt
  lean V_A.lean      # '#eval RTProbe.run "A-default" [] [`Init, `Std]'
  lean V_cat.lean    # '#eval RTProbe.catalog [`Init, `Std]'  (failure categories)
  lean Cases.lean; lean Cases2.lean                 # manual confirmation of defects (a) and (c)
  python3 toy_invertible_syntax.py                  # toy model T0..T7 (Python 3.13)
  ```

  Summaries are in `support/results.txt`, and the per-category catalog is in `support/catalog.txt`. Max RSS and wall time were measured with `/usr/bin/time -v`.

## Revalidation

- **Lean.** For a new toolchain, re-run `support/RoundTrip.lean` with the six driver lines. The discriminating outputs are:
  - the `notDefEq` counts;
  - `#check @BitVec.ofNatLT_zero` followed by re-parsing its output at root (defect (a));
  - re-elaborating the default text of `Array.mapFinIdx_eq_iff` (defect (c));
  - `BitVec.toNat_mod_cancel'` (defect (b)).

  Diff `TopDownAnalyze.lean` lines 20–95 and 613–625 for changed defaults or fail-open behaviour, and `BitVec/Basic.lean:188–195` for a `scoped` unexpander.
- **Rocq.** Re-read `syntax-extensions.rst` around the `only printing` note and `interp/notation.ml` `update_notation_data`.
- **Danielsson.** Check that `Renderer.parsable` and `correct-if-locally-unambiguous` keep their types, and grep `Examples/` for unambiguity proofs.
- **FliPpr.** Check the `parseExp` result type (still a list) and `<?` semantics in `Text/FliPpr.hs`.
- **Naproche.** Re-read `prover_status` and `eprover_messages` in `src/Naproche/Prover.hs` to see whether a proof object or proof checking step has been added.
- **Verbose.** Re-read `Verbose/Tactics/Notations.lean` and the paper's §4.1. No cheap probe re-measures human misreading.
