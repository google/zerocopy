# Statutory Default Logic, Deontic Contract Languages, and Linear Financial Contract Calculi

## Summary

Normative legal systems, commercial agreements, and financial settlement engines expose four structural properties that mainstream imperative and affine programming languages conflate or erase:

1. **Non-monotonic statutory exception hierarchies (`Catala`, ICFP 2021):** Statutory rules are structured as base definitions overridden by scattered, nested exceptions. Catala's Default Calculus replaces order-sensitive `if`/`else` chains with a three-outcome lattice (`Empty | Value(v, pos) | Conflict(positions)`), compiled to pure `Option` values (`TOption (TTuple [t; TLit TPos])`) and checked statically for absence of `NoValue` and `Conflict` via pairwise quadratic ($O(n^2)$) Z3 verification conditions (`compiler/verification/conditions.ml`). Its Coq mechanization (`CatalaLang/catala-formalization`) proves small-step continuation simulation for this default-to-option lowering while explicitly assuming termination (`measure`) and `FunctionalExtensionality`.
2. **Cross-backend exact numeric and date rounding semantics (`Catala` vs. `Mlang`):** Statutory calculations mandate exact rational/cent arithmetic and explicit midpoint tie-breaking. Across OCaml (`Zarith`), C (`GMP`), Python (`fractions.Fraction`), and Java (vendored Apache Commons `BigFraction`), Catala implements uniform round-half-away-from-zero (`sgn(q) * floor((2|n| + d) / (2d))`), deliberately shadowing Python's built-in banker's rounding (`round`) and contrasting sharply with France's legacy DGFiP `M` compiler (`Mlang`), which must emulate binary64 `0.5 + 50*epsilon` rounding fudges and mainframe `max_long` floor guards to match historical tax computations.
3. **Defeasible deontic obligations and breach reparations (`L4`):** Where Catala models *constitutive* calculations, `L4` (`smucclaw/dsl`, `smucclaw/baby-l4`) models *regulative* multi-party temporal obligations (`DMust`, `DMay`, `DShant`) chained through `hence` (fulfillment) and `lest` (contrary-to-duty breach reparation) clauses, avoiding Standard Deontic Logic's Chisholm explosion and transpiling regulative rules into UPPAAL timed automata (`LS.XPile.Uppaal`) and SMT-encoded TCTL reachability problems (`TimedMC`).
4. **Declarative contract algebras vs. bytecode-verified linear conservation (`Composing Contracts`, `Marlowe`, `Move`, `TigerBeetle`):** Composable contract combinators (`ICFP 2000`; `Marlowe` Isabelle/HOL `playTrace_preserves_assets` and `closeIsSafe`) guarantee termination and value conservation over a finite continuation AST, whereas `Move` enforces strictly linear asset conservation directly on untrusted stack bytecode via four orthogonal abilities (`Copy`, `Drop`, `Store`, `Key`) checked by abstract interpretation (`locals_safety` rejects unconsumed non-`Drop` locals at `Ret` and `StLoc` while treating `Abort` as a no-op because blockchain execution provides atomic transaction rollback). Crossing FFI into non-transactional hosts (`C`, `Rust` affine `Drop`/`mem::forget`, or network ledgers such as `TigerBeetle`'s 128-bit double-entry two-phase transfers) breaks both Catala's arena/error guarantees and Move's linearity unless explicit transactional/outbox or capability-sealing protocols bridge the seam.

## Applicability

This report synthesizes and compares eleven durable primary subjects spanning four closely related formalisms for law, compliance, and financial engineering:

- **Statutory default-logic compilation and exact legal arithmetic:** `CatalaLang/catala` (revision `7a0c93beda25b903ebcdfe64d672caf53dd41370`), its companion Coq formalization `CatalaLang/catala-formalization` (revision `985eb86afb7c6bd3d020fb99ea9e391b93576d44`), the ICFP 2021 paper (`doi:10.1145/3473582`), and the legacy French tax compiler `MLanguage/mlang` (revision `66f6b37308c0dfeb3bb24c8af7952a522452a1af`) used as a direct historical baseline for binary floating-point rounding quirks.
- **Deontic contract languages and timed compliance automata:** `smucclaw/dsl` (Natural L4, revision `3a679a7a2dfd935f562dd335f708e6c5a3b5bb64`) and `smucclaw/baby-l4` (core L4 and SMT timed model checker, revision `f351e4e8d435e3f5800653b558de2571ed19740c`), interpreted against defeasible deontic logic and Chisholm's contrary-to-duty paradox.
- **Declarative financial contract calculi and formal settlement preservation:** Peyton Jones, Eber, and Seward's `Composing Contracts` (`doi:10.1145/351240.351267`) and `input-output-hk/marlowe` (revision `7b5b1e900ec53a8eb18747992bec73470704dfcb`, specifically its Isabelle/HOL `isabelle/Core/*.thy` theories).
- **Bytecode-verified linear resources and double-entry ledgers:** `move-language/move` (revision `c453c90994cba0af30314fe4134acee57fb20d0c`, `move-binary-format` and `move-bytecode-verifier`), the Move Prover (`doi:10.1007/978-3-030-53288-8_7`), and `tigerbeetle/tigerbeetle` (revision `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`, `src/tigerbeetle.zig`) as a concrete systems-level double-entry settlement target.

Findings apply to compiler design, formal verification of policy/statutory engines, cross-language FFI runtime integration (`C`, `OCaml`, `Python`, `Java`, `Rust`, `Zig`), and multi-party financial/asset state machines. Findings about Catala's default lowering, Z3 VC generation, and C/OCaml/Python/Java runtimes reflect exact source inspection at `7a0c93beda25b903ebcdfe64d672caf53dd41370` (where defaults compile to `TOption (TTuple [t; TLit TPos])` via `lcalc/from_dcalc.ml`, superseding the earlier exception-based lowering described in ICFP 2021). Findings about `Move` apply to the core Move bytecode verifier (`move-language/move` `c453c909...`) and do not automatically assume later Sui Move or Aptos Move v2 extensions unless explicitly noted.

## Findings

### 1. Prioritized Default Logic and Exception Trees in Catala

#### 1.1 Operational Semantics of the Default Calculus (`Dcalc`)
Basis: normative (`doi:10.1145/3473582`) + source (`CatalaLang/catala`, `CatalaLang/catala-formalization`) + execution

Statutory law frequently introduces a general rule in one section, an exception dozens of pages later, and an exception-to-the-exception in a subsequent amendment. Encoding these rules as flat imperative `if`/`else if`/`else` chains conflates *evaluation order* with *normative priority*: if two unranked exceptions apply simultaneously, the earlier branch silently wins, masking a genuine legislative ambiguity.

Catala formalizes legislative exception trees via a **Default Calculus** (`Dcalc`), derived from Raymond Reiter's prioritized default logic and Sarah Lawsky's legal formalization. A default term has the form:

$$\langle e_1, \dots, e_n \mid e_{\text{just}} \mathrel{:-} e_{\text{cons}} \rangle$$

In `CatalaLang/catala-formalization` (`theories/catala/syntax.v:18-39`), the core default calculus augments simply-typed $\lambda$-calculus with five dedicated constructors:

```coq
| ErrorOnEmpty (arg: term)
| DefaultPure (arg: term)
| Default (ts: list term) (tj tc: term)
| Empty
| Conflict
```

Evaluation of `Default [e_1; ...; e_n] e_just e_cons` follows a deterministic three-outcome error lattice (`Empty | Value(v, pos) | Conflict(positions)`):

1. Evaluate every sibling exception $e_1, \dots, e_n$.
2. Partition the results: discard `Empty` outcomes; propagate `Conflict` immediately.
3. Let $S$ be the multiset of active non-`Empty` exception values:
   - If $|S| = 0$: evaluate justification $e_{\text{just}}$; if `true`, evaluate and return $e_{\text{cons}}$; if `false`, return `Empty`.
   - If $|S| = 1$ with $S = \{v\}$: return $v$ (the unique exception overrides the base rule).
   - If $|S| \ge 2$: raise fatal **`Conflict`** carrying the source positions of every simultaneously active exception.
4. Wrapping a scope definition in `ErrorOnEmpty` converts a top-level `Empty` result (no applicable rule and no active exception) into fatal **`NoValue`** (`EmptyError` in ICFP 2021).

In the Python execution probe reproducing this evaluator, two unranked exceptions (`Art.42` and `Art.89`) active simultaneously over base rule `Art.1` deterministically trigger `Conflict(['Art.42', 'Art.89'])` rather than silently selecting whichever clause was coded first.

#### 1.2 Lowering Defaults to `Option` Types (`Dcalc -> Lcalc`) and Mechanized Soundness
Basis: source (`CatalaLang/catala`, `CatalaLang/catala-formalization`)

While the ICFP 2021 paper (`doi:10.1145/3473582`) presented an F\*-verified compilation of defaults via exceptions, the production Catala compiler (`CatalaLang/catala`, `compiler/lcalc/from_dcalc.ml:32-165`) lowers `Dcalc` into `Lcalc` *without* runtime exceptions for `Empty`, exploiting the invariant that defaultable values only occur at `TDefault`-typed positions:

- **Type translation (`compiler/lcalc/from_dcalc.ml:32-37`):** `TDefault t` translates to `TOption (TTuple [t; TLit TPos])`, pairing every active value with its statutory source-span provenance (`code_location`).
- **Term translation (`compiler/lcalc/from_dcalc.ml:122-165`):**
  - `EEmpty` lowers to `Option.None ()`.
  - `EPureDefault e` lowers to `Option.Some (translate_expr e, pos)`.
  - `EErrorOnEmpty arg` lowers to a pattern match: `None _ -> fatal NoValue pos | Some (v, _) -> v`.
  - `EDefault { excepts; just; cons }` compiles to `Op.HandleExceptions` over an array of `Option (t * pos)` values (when `|excepts| >= 2`), followed by matching `Some x -> Some x | None -> if just then cons else None`. Single-exception and constant-boolean `just` cases are specialized directly without allocating an array (`from_dcalc.ml:71-113`).
- **Runtime `handle_exceptions` (`runtimes/ocaml/catala_runtime.ml:1026-1043`):** Filters `Optional.Present` entries from the exception array; returns `Optional.Absent` on `[]`, the unique element on `[res]`, and raises `Error (Conflict, positions, None)` whenever two or more exceptions are present, attaching every conflicting statutory `code_location`.

The companion Coq mechanization (`CatalaLang/catala-formalization`, `theories/catala/trans.v:129-195` and `CLAIMS.md`) proves `correction_continuations`: every continuation-machine step `cred s1 s2` in the source default calculus is simulated by reflexive-transitive steps `star cred` on the translated `Option`-based MiniML states `trans_state s1` and `trans_state s2` joining at a common target state. Crucially, `CLAIMS.md` explicitly records the proof's two axioms/assumptions: (1) `Autosubst` relies on Coq's `FunctionalExtensionality`, and (2) `theories/catala/typing.v` submodule `correctness` assumes a decreasing `measure` hypothesis for simply-typed $\lambda$-calculus termination rather than mechanizing strong normalization from scratch.

#### 1.3 Static SMT Verification of Conflict-Freedom and Non-Emptiness
Basis: source (`CatalaLang/catala`) + derived

Detecting statutory `Conflict` or `NoValue` statically across all possible taxpayer/citizen inputs is implemented in `compiler/verification/conditions.ml` and `compiler/verification/z3backend.ml`:

- **Non-emptiness VC (`conditions.ml:140-228`):** `generate_vc_must_not_return_empty` maps `EDefault { excepts; just; cons }` to the disjunction that either at least one exception $e_i$ is non-empty, or `just` is non-empty and `if just then non_empty(cons) else false`.
- **Conflict-freedom VC (`conditions.ml:234-268`):** `generate_vc_must_not_return_conflict` checks two conjuncts:
  1. Recursively, neither `just`, `cons`, nor any $e_i \in \text{excepts}$ can itself conflict.
  2. **Pairwise disjointness (`quadratic`):** Over `half_product excepts excepts` — i.e., all $\binom{n}{2} = \frac{n(n-1)}{2}$ unordered pairs $(e_i, e_j)$ with $i < j$ — the VC asserts $\neg \bigvee_{i < j} (\text{non\_empty}(e_i) \land \text{non\_empty}(e_j))$.
- **TCB and expressiveness limitations observed in source:**
  1. The quadratic pairwise expansion at every `EDefault` node compounds multiplicatively across nested exception trees and scope calls, causing SMT formula blowup on large tax brackets with nonlinear multiplication/division and array traversals (`z3backend.ml:32-65`).
  2. Source comment at `conditions.ml:164-168` notes an explicit soundness caveat when justifications themselves contain nested default terms (`the justification is not checked for holding an default term`), requiring encoding default logic inside VC generation for full completeness.
  3. The Z3 backend (`z3backend.ml`) maps `ctx_z3vars` back to Catala variable names and types to pretty-print counterexample models, but Z3 itself sits inside the trusted computing base (no proof certificates are re-checked in Coq/Lean).

---

### 2. Cross-Backend Exact Numeric, Rounding, and Calendar Semantics (`Catala` vs. `Mlang`)

#### 2.1 Uniform Exact Types and Round-Half-Away-From-Zero Across Four Backends
Basis: source (`CatalaLang/catala`, `MLanguage/mlang`) + execution

Binary IEEE-754 floating point cannot represent `$0.10` or `$100.05` cleanly in base 10 and creates severe platform-dependent tax discrepancies. Catala eliminates binary floats from its semantic core, providing exact arbitrary-precision `integer` ($\mathbb{Z}$), exact rational `decimal` ($\mathbb{Q}$), and exact integer-cent `money` ($\mathbb{Z}$ cents), with explicit rounding coercions. Every target runtime implements the identical mathematical rounding formula:

$$\operatorname{round}(q) = \operatorname{sgn}(q) \cdot \left\lfloor |q| + \frac{1}{2} \right\rfloor = \operatorname{sgn}(q) \cdot \left\lfloor \frac{2|n| + d}{2d} \right\rfloor \quad \text{for } q = \frac{n}{d} \in \mathbb{Q},\ d > 0$$

This is **round-half-away-from-zero** (mapping $+0.5 \mapsto +1$, $-0.5 \mapsto -1$, $+2.5 \mapsto +3$, $-2.5 \mapsto -3$). Direct source inspection at `CatalaLang/catala` `7a0c93beda25b903ebcdfe64d672caf53dd41370` confirms how each backend avoids host-language rounding traps:

| Target Backend | `integer` / `money` Rep. | `decimal` ($\mathbb{Q}$) Rep. | Exact `round` Implementation | Host Pitfall Explicitly Avoided |
|---|---|---|---|---|
| **OCaml** (`runtimes/ocaml/catala_runtime.ml:22-24, 107-119`) | `Z.t` (Zarith / GMP); `money` in cents | `Q.t` (Zarith / GMP) | `Z.(of_int sgn * fdiv ((z2 * n) + d) (z2 * d))` | `Q.to_bigint` truncates toward `0` (`-0.1 -> 0`) rather than flooring (`catala_runtime.ml:109-111`) |
| **C** (`runtimes/c/catala_runtime.c:167-173, 1138-1169`) | `mpz_ptr` (GMP) arena-allocated | `mpq_ptr` (GMP) canonicalized | `round_div`: `mpz_fdiv_q(2*|num|+|den|, 2*|den|)` * `sign` | `mpz_tdiv_q` truncates toward `0` (intentionally used only in `o_toint_rat`, line 1160, vs. `round_div` in `o_toint_mon`, line 1167) |
| **Python** (`runtimes/python/src/catala/catala_runtime.py:480-615, 832-838`) | `class Integer(Value, int)`, `class Money(Value, int)` | `class Decimal(Value, Fraction)` | Custom `def round(q)` (`(2*n + d) // (2*d)`) shadowing built-in `round` | Python 3 built-in `round(Fraction)` uses **round-half-to-even** (`round(Fraction(1,2)) == 0`, `round(Fraction(5,2)) == 2`) |
| **Java** (`runtimes/java/catala/runtime/CatalaDecimal.java:144-146`, `CatalaMoney.java:126`) | `BigInteger` (`CatalaInteger`, `CatalaMoney`) | Vendored Apache Commons `BigFraction` | `bigDecimalValue(0, RoundingMode.HALF_UP).toBigInteger()` | `BigDecimal.divide` without scale/mode throws `ArithmeticException` on non-terminating `1/3`; `HALF_EVEN` diverges on ties |

#### 2.2 Historical Contrast: Legacy DGFiP `M` Floating-Point Rounding Quirks (`Mlang`)
Basis: source (`MLanguage/mlang`) + execution

Direct inspection of `MLanguage/mlang` (`66f6b37308c0dfeb3bb24c8af7952a522452a1af`, `src/mlang/m_ir/mir_roundops.ml:28-79`) reveals the real-world cost of encoding tax law on binary64 hardware without exact rationals. To reproduce France's legacy DGFiP tax calculator bit-for-bit across PC and mainframe targets, `Mlang` defines three functorized rounding implementations (`DefaultRoundOps`, `MultiRoundOps`, `MainframeRoundOps`):

```ocaml
(* MLanguage/mlang src/mlang/m_ir/mir_roundops.ml:39-41, 65-78 *)
let roundf (x : N.t) =
  let e = N.of_float (0.5 +. (epsilon *. 50.)) in
  if N.(x < zero ()) then N.ceil N.(x -. e) else N.floor N.(x +. e)
```

Two pathological artifacts appear in `mir_roundops.ml`:
1. **Epsilon bias shifts near-midpoints:** Because `e = 0.5 + 50 * epsilon` (compensating for binary64 representation error when `epsilon = 1e-6`), our execution probe confirms that `q = 49999/100000 = 0.49999` rounds to **`0`** under Catala exact arithmetic and Python banker's rounding, but rounds to **`1`** under `mlang_round(0.49999, eps=1e-6)` (`0.49999 + 0.50005 = 1.00004`).
2. **Signed-zero and mainframe overflow traps:** `mir_roundops.ml:36-38` explicitly warns that `copysign` cannot replace `x < zero ()` due to `-0.0`, while `MainframeRoundOps` (`lines 65-70`) must guard `floor_g`/`ceil_g` with `if N.abs x <= N.of_int !L.max_long then N.floor x else x` to emulate legacy mainframe `long`-cast saturation!

#### 2.3 Calendar Date Ambiguity and Bi-Temporal Versioning
Basis: source (`CatalaLang/catala`) + documentation

Statutory calendars are non-uniform (variable month lengths, leap days such as `2024-02-29 + 1 year`). Catala's `dates_calc` runtime (`runtimes/ocaml/catala_runtime.ml:27-30, 236-247`) refuses silent calendar heuristics:
- Date-addition rounding mode is an explicit tri-state parameter: `RoundUp | RoundDown | AbortOnRound`.
- Comparing mixed-unit durations (`compare_periods`, lines 236-247) succeeds only when both periods are pure year/month (`days = 0`) or pure day (`years = months = 0`); comparing months against days raises `DateError "ambiguous comparison between durations in different units (e.g. months vs. days)"`.

In production statutory engines, rules also vary across two orthogonal timelines (**bi-temporal semantics**): **valid time** ($T_{\text{valid}}$, when the factual event occurred) and **enactment / transaction time** ($T_{\text{enact}}$, when a statute or retroactive amendment took effect). Because neither Catala's core type system nor standard SQL CRUD tables statically index computations by `(T_valid, T_enact)`, calling an unversioned foreign lookup table or system wall-clock inside a historical recalculation creates a silent **temporal-leak soundness violation** where post-$T_{\text{enact}}$ rates contaminate an as-of-$T_{\text{enact}}$ audit.

#### 2.4 C FFI Arena and `longjmp` Boundary Hazards in Catala
Basis: source (`CatalaLang/catala`)

Inspecting `runtimes/c/catala_runtime.c:30-150` exposes strict C-FFI invariants that host applications must obey to avoid memory corruption or process termination:
- **Thread-local bump arena (`lines 66-141`):** `catala_malloc` allocates out of a `__thread struct catala_heap` chain of `BLOCKSIZE = 16384`-byte blocks; individual `catala_free` is a no-op (`lines 137-141`) until `catala_free_all()` bulk-frees the entire thread-local heap. Returning pointers into host data structures without enabling `catala_set_persistent_malloc()` (`lines 144-150`) causes dangling-pointer use-after-free once `catala_free_all()` runs.
- **`setjmp`/`longjmp` error unwind (`lines 43-62`):** Every runtime error (`NoValue`, `Conflict`, `DivisionByZero`, `AssertionFailed`, `DateError`, `catala_malloc_error`) invokes `longjmp(catala_error_jump_buffer, 1)` when inside a `catala_do` frame, or calls **`abort()`** (`line 60`) if triggered outside `catala_do`. Calling Catala C functions across C++ or Rust FFI frames that hold RAII/Drop guards without isolating `catala_do` causes **Undefined Behavior** (unwinding past non-POD C++/Rust frames via `longjmp` skips destructors and violates Rust ABI unwind rules).

---

### 3. Defeasible Deontic Logic and Temporal Reparation Automata (`L4`)

#### 3.1 Chisholm's Paradox and Defeasible Deontic Modalities
Basis: normative (Chisholm 1963; `arXiv:2205.07335`) + source (`smucclaw/dsl`, `smucclaw/baby-l4`)

While Catala targets *constitutive* rules (calculating amounts or eligibility booleans at a point in time), commercial contracts, SLAs, and regulatory obligations are *regulative* and *temporal*: obligations activate upon events, carry deadlines, and trigger secondary **contrary-to-duty (CTD)** penalties when breached.

Standard Deontic Logic (modal logic **KD**, with obligation operator $O$, permission $P(p) \equiv \neg O(\neg p)$, and axiom $O(p) \to \neg O(\neg p)$) suffers **Chisholm's Paradox** (1963). Given four consistent contractual premises:
1. $O(a)$ (Party A must deliver goods),
2. $O(a \to b)$ (if A delivers, A must send a delivery notice),
3. $\neg a \to O(\neg b)$ (if A does not deliver, A must not send a notice),
4. $\neg a$ (A breaches and fails to deliver),

modus ponens on (3)-(4) derives $O(\neg b)$, while KD necessitation/distribution on (1)-(2) derives $O(b)$—violating consistency ($O(b) \land O(\neg b)$) and causing deontic explosion.

Defeasible Deontic Logic (DDL) and L4 resolve CTD reasoning by representing explicit reparation chains ($O(a) \otimes O(b)$: "$a$ is obligatory; if breached, compensating obligation $b$ activates") combined with defeasible superiority relations overriding primary norms when breach occurs.

#### 3.2 `L4` Regulative AST, `HENCE`/`LEST` Chains, and Timed Automaton Compilation
Basis: source (`smucclaw/dsl`, `smucclaw/baby-l4`)

In Natural L4 (`smucclaw/dsl`, `3a679a7a2dfd935f562dd335f708e6c5a3b5bb64`):
- **Deontic operators (`lib/haskell/natural4/src/LS/Types.hs:619`):** `data Deontic = DMust | DMay | DShant` directly encodes obligation (`MUST`), permission (`MAY`), and prohibition (`SHANT`).
- **Regulative rule structure (`lib/haskell/natural4/src/LS/Rule.hs:152-171`):**
  ```haskell
  data Rule = Regulative
    { subj     :: BoolStructP                        -- obligated party
    , rkeyword :: RegKeywords                        -- Every | Party | TokAll
    , who      :: Maybe BoolStructR                  -- party qualification
    , cond     :: Maybe BoolStructR                  -- activation guard (IF/WHEN)
    , deontic  :: Deontic                            -- DMust | DMay | DShant
    , action   :: BoolStructP                        -- required/permitted/forbidden action
    , temporal :: Maybe (TemporalConstraint Text)    -- TBefore | TAfter | TBy | TOn
    , hence    :: Maybe Rule                         -- continuation upon fulfillment
    , lest     :: Maybe Rule                         -- CTD reparation upon breach
    , upon     :: Maybe ParamText                    -- triggering event
    ... }
  ```
  Terminal states are explicitly represented as `RegFulfilled` (`"FULFILLED"`) and `RegBreach` (`"BREACH"`, `LS/Rule.hs:321-322`), with cross-rule transitions via `RuleAlias RuleName` (`HENCE NextStep`, `line 232`).
- **Multi-target transpilation (`LS/XPile/`):** Natural L4 separates constitutive (`Constitutive`, `Hornlike`) from regulative rules and compiles them to multiple targets including `Uppaal.hs`, `Petri.hs`, `Maude.hs`, `Prolog.hs`, `Typescript.hs`, `Purescript.hs`, `NaturalLanguage.hs`, and `CoreL4.hs`.
- **UPPAAL & SMT Timed Model Checking (`LS/XPile/Uppaal.hs:40-75`, `smucclaw/baby-l4` `src/TimedMC.hs:1-75`):**
  - `LS.XPile.Uppaal.toL4TA` converts each `Regulative` rule into a timed automaton synchronized on `henceChannels` (`Set.fromList $ foldMap getHence rules`).
  - `baby-l4`'s `src/TimedMC.hs` encodes a timed automaton and TCTL specification into SMT using explicit action/delay transition relations (`ATrans`, `DTrans`) parameterized over discrete `StateT` and continuous `TimeT` clock variables (`transitionFunTp n`, `lines 55-60`).
- **Concrete implementation boundaries observed in source (`LS/XPile/Uppaal.hs:59, 73-74`):** The UPPAAL transpiler contains explicit unfinished markers: `-- TODO: Handle recursive Hence`, `-- TODO Nested`, and `-- TODO Handle party`. Thus while single-level `RuleAlias` `HENCE` chaining compiles to UPPAAL channels, nested inline `HENCE`/`LEST` trees and multi-party identity scoping are not yet completely lowered in the inspected snapshot.

#### 3.3 Structural Contrast: Deontic Reparation Automata vs. Multiparty Session Types
Basis: derived (from `smucclaw/dsl` + standard MPST literature)

A recurring design question is whether L4 `HENCE`/`LEST` reparation automata are isomorphic to Multiparty Session Types (MPST) with timeouts. They share state-machine structure, but diverge on three fundamental axes:
1. **Protocol rejection vs. breach continuation:** Classical MPST statically forbids invalid transitions (progress/fidelity rules out non-conforming peers); deontic contract automata *must* accept non-conforming events (`SHANT` violated, or `MUST` deadline missed) and transition cleanly into `lest` reparation states rather than treating breach as impossible/UB.
2. **Concurrent overlapping obligations:** Multiple simultaneous obligations over independent deadlines compose asynchronously in timed automata, incurring exponential state-space growth ($O(\prod |Q_i|)$ product states and EXPTIME-complete timed-game strategy synthesis in the number of clocks) when checking whether a party has a compliance-preserving winning strategy against adversarial counterparties.
3. **Event-abstraction and clock-skew FFI seam:** Idealized UPPAAL/SMT clocks assume exact instantaneous event observation; bridging to distributed webhooks/payment rails introduces network delay, clock skew, and non-atomic delivery where a payment sent before `TBy` arrives after `TBy`.

---

### 4. Composable Financial Contract Algebras (`Composing Contracts` and `Marlowe`)

#### 4.1 Algebraic Contract Combinators (`ICFP 2000`)
Basis: normative (`doi:10.1145/351240.351267`)

Peyton Jones, Eber, and Seward (`ICFP 2000`) factored financial derivative definitions away from imperative valuation loops by defining a compact algebraic combinator language parameterized by stochastic time-indexed `Observable a` streams:

- **Primitives & combinators:** `zero` (no rights/obligations), `one k` (immediately receive 1 unit of currency `k`), `give c` (invert holder/counterparty obligations), `and c1 c2`, `or c1 c2` (holder chooses between `c1` and `c2`), `cond o c1 c2`, `scale o c`, `when o c` (acquire `c` when boolean observable `o` first holds), `anytime o c` (American-style optional exercise window), and `until o c` (abandon upon observable `o`).
- **Multiple interpretations over one AST:** Because contracts are pure inductive terms, a single specification feeds cashflow schedule extraction, lattice/Monte Carlo pricing, automatic differentiation for risk Greeks, and term-sheet generation without front-office/back-office drift.
- **Irreducible compositional limits:**
  1. **Optimal stopping in `or`/`anytime`:** Cashflow obligations are purely algebraic, but fair pricing of holder-optionality requires backward dynamic programming / optimal-stopping over stochastic filtrations (inherently model-dependent).
  2. **Portfolio-level non-compositionality:** Close-out netting under counterparty bankruptcy and margin collateralization depend on *sets* of contracts sharing a counterparty (`and c1 c2` nets differently when `c1, c2` share a defaulting counterparty than when they span two distinct counterparties).

#### 4.2 `Marlowe` Continuation AST and Isabelle/HOL Preservation Theorems
Basis: normative (`doi:10.1007/978-3-030-03427-6_27`) + source (`input-output-hk/marlowe`)

`Marlowe` adapts Peyton Jones–Eber combinators to a finite, non-Turing-complete blockchain execution model with mechanized Isabelle/HOL semantics (`input-output-hk/marlowe`, `7b5b1e900ec53a8eb18747992bec73470704dfcb`, `isabelle/Core/SemanticsTypes.thy:257-263`):

```isabelle
datatype Case = Case Action Contract
and Contract = Close
             | Pay AccountId Payee Token Value Contract
             | If Observation Contract Contract
             | When "Case list" Timeout Contract
             | Let ValueId Value Contract
             | Assert Observation Contract
```

Every `When` construct carries an explicit finite `Timeout` and fallback continuation, guaranteeing that every contract eventually reaches `Close` (which refunds all remaining internal account balances to their designated owners). The Isabelle/HOL development proves four load-bearing safety theorems directly over the executable semantics (which is code-exported to Haskell in `isabelle/generated/`):

1. **Exact Asset Conservation (`isabelle/Core/AssetsPreservation.thy`, `theorem playTrace_preserves_assets`):** For any valid trace `playTrace slot contract txs = TransactionOutput out`:
   $$\text{assetsInTransactions}(\text{txs}) = \text{assetsInState}(\text{txOutState}(\text{out})) + \text{assetsInExternalPayments}(\text{txOutPayments}(\text{out}))$$
   No value can be created or destroyed across arbitrary sequences of deposits, internal payments, external payouts, and timeouts.
2. **No Stuck Funds / Close Safety (`isabelle/Core/CloseSafe.thy`, `theorem closeIsSafe`):** Once reduced to `Close`, executing `computeTransaction` produces zero warnings (`txOutWarnings trec = []`), and `Close` is idempotent under `reduceContractUntilQuiescent`.
3. **Bounded Termination (`isabelle/Core/TransactionBound.thy`):** `reductionLoop_reduces_maxTransactions` and `countWhens` establish a static upper bound on the maximum number of transactions a contract can ever accept, ruling out infinite loops and unbounded on-chain liveness stalls.
4. **Positive Internal Accounts (`isabelle/Core/PositiveAccounts.thy` & `ValidState.thy`):** `computeTransaction_preserves_validAndPositive_state` guarantees internal account maps never hold negative or zero-entry garbage balances.

---

### 5. Bytecode-Verified Linear Resource Conservation (`Move`) and Double-Entry Ledgers (`TigerBeetle`)

#### 5.1 Four Orthogonal Abilities and Bytecode Verifier Pipeline (`Move`)
Basis: source (`move-language/move`) + normative (`doi:10.1007/978-3-030-53288-8_7`)

Unlike `Marlowe` (which restricts contracts to a fixed finite AST), `Move` provides Turing-complete programmable smart-contract modules while guaranteeing asset conservation **at the untrusted bytecode level**—so a malicious external module calling compiled bytecode directly cannot duplicate or discard a token.

In `move-language/move` (`c453c90994cba0af30314fe4134acee57fb20d0c`, `language/move-binary-format/src/file_format.rs:578-624`), every type carries a 4-bit `AbilitySet` over four abilities:

| Ability | Bit | Operational Permission | Field Requirement (`Ability::requires()`) |
|---|---|---|---|
| `Copy` | `0x1` | Value may be duplicated via `CopyLoc` or `ReadRef` | Every field must have `Copy` |
| `Drop` | `0x2` | Value may be discarded via `Pop`, `WriteRef`, `StLoc`, `Eq`/`Neq`, or left in a local at `Ret` | Every field must have `Drop` |
| `Store` | `0x4` | Value may reside inside a struct stored in global storage | Every field must have `Store` |
| `Key` | `0x8` | Struct may serve as a top-level global storage resource (`MoveTo`/`MoveFrom`) | Every field must have **`Store`** (`file_format.rs:613`) |

A currency struct `Coin<T>` declared with `has store` (or `has key, store`)—omitting both `Copy` and `Drop`—is a **strictly linear resource**. A struct declared with `AbilitySet::EMPTY` (no `Copy`, `Drop`, `Store`, or `Key`) implements the **"hot potato" pattern** (e.g., a flash-loan receipt that can neither be dropped, copied, nor stashed in global storage, statically forcing the caller to pass it back to the defining module's `repay` function before returning).

The bytecode verifier (`language/move-bytecode-verifier/src/verifier.rs:94-119`) runs an ordered, fail-closed pipeline wrapped in `std::panic::catch_unwind` (converting any internal verifier panic into `StatusCode::VERIFIER_INVARIANT_VIOLATION`):
1. `BoundsChecker` (validates table indices before any indexing)
2. `LimitsVerifier` (bounds module complexity/DoS limits)
3. `DuplicationChecker`, `SignatureChecker`, `InstructionConsistency`, `constants`, `friends`
4. `ability_field_requirements::verify_module` (`ability_field_requirements.rs:20-52`: checks `required_abilities.is_subset(field_abilities)` for every declared struct field, emitting `StatusCode::FIELD_MISSING_TYPE_ABILITY` on violation)
5. `RecursiveStructDefChecker` & `InstantiationLoopChecker` (forbids infinite-size types and polymorphic recursion cycles)
6. `CodeUnitVerifier` (stack usage, control flow, type safety, `locals_safety`, `reference_safety`, `acquires_list_verifier`)
7. `script_signature`

#### 5.2 Linear Conservation vs. `Abort` Unwinding (`locals_safety`)
Basis: source (`move-language/move`) + derived

Direct inspection of `language/move-bytecode-verifier/src/locals_safety/mod.rs:40-100` reveals the exact control-flow-sensitive abstract interpretation enforcing linearity—and its critical dependence on transactional rollback:

- **`Bytecode::StLoc(idx)` (`lines 41-48`):** Overwriting a local whose abstract state is `Available` or `MaybeAvailable` when `!state.local_abilities(*idx).has_drop()` fails verification with **`StatusCode::STLOC_UNSAFE_TO_DESTROY_ERROR`**.
- **`Bytecode::Ret` (`lines 73-88`):** Iterates every local slot; any slot in `Available | MaybeAvailable` without `Drop` fails verification with **`StatusCode::UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`**.
- **`Bytecode::Abort` (`line 94`):** Explicitly falls into the no-op arm alongside `Nop` and arithmetic ops! Move does **not** require live non-`Drop` resources (including hot potatoes!) to be consumed before `Abort`, because the Move VM executes every transaction inside an **atomic transactional rollback** boundary: upon `Abort`, all global-storage mutations revert cleanly.

This exposes a deep mathematical boundary for general-purpose systems languages (such as Rust, whose ownership model is **affine**—values may be silently dropped or leaked via safe `std::mem::forget`): true linearity is sound under runtime failure *only* if the execution substrate guarantees either (a) **atomic transactional rollback** (`Move`, SQL, STM), (b) **totality / proven panic-freedom** (`Marlowe`, total `Catala` scopes proved free of `NoValue`/`Conflict`/`DivByZero`), or (c) **explicit linear compensation handlers** along every unwind path.

#### 5.3 Global Invariants (`Move Prover`) and Systems-Level Double-Entry Settlement (`TigerBeetle`)
Basis: normative (`doi:10.1007/978-3-030-53288-8_7`) + source (`tigerbeetle/tigerbeetle`) + execution

Linearity alone enforces conservation of *individual* tokens (no duplication or silent burn of a `Coin<T>`), not relational multi-asset invariants (e.g., total supply equality across accounts, or AMM pool invariants $x \cdot y \ge k$). The **Move Prover** (`CAV 2020`, `doi:10.1007/978-3-030-53288-8_7`) translates Move bytecode and specification blocks into Boogie/Z3, leveraging Move's reference-safety verifier (`reference_safety/mod.rs`, which enforces tree-structured, alias-free mutable borrows without arbitrary heap aliasing) to compile mutable references into pure functional read/write value updates without complex separation-logic heap framing.

At the high-throughput financial ledger layer (`tigerbeetle/tigerbeetle`, `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`, `src/tigerbeetle.zig:45-148`), double-entry settlement enforces conservation and multi-leg atomicity through fixed-layout 128-bit structures (`@sizeOf(AccountBalance) == 128`, verified via `comptime` assertions):
- **`AccountBalance` (`lines 70-80`):** Tracks four distinct unsigned `u128` accumulators (`debits_pending`, `debits_posted`, `credits_pending`, `credits_posted`), preventing negative wraparound while preserving full audit history.
- **`AccountFlags` (`lines 45-68`):** Enforces per-account invariants (`debits_must_not_exceed_credits`, `credits_must_not_exceed_debits`) and atomic batch chaining (`.linked`, where every event in a linked chain commits or rolls back as an atomic unit, returning `.linked_event_failed` on failure).
- **`TransferFlags` (`lines 132-148`):** Provides native two-phase commit (`pending`, `post_pending_transfer`, `void_pending_transfer`) plus `balancing_debit`/`balancing_credit` for exact net-settlement caps.
- **Integer-cent rounding dust (`execution`):** Dividing an exact integer-cent balance across $N$ recipients cannot preserve exact sum-to-zero conservation without an explicit remainder law: as confirmed by our probe, splitting `10000` cents (`$100.00`) across `3` recipients yields `3333 * 3 = 9999` cents, losing `1` cent of **rounding dust** unless routed deterministically (e.g., Hamilton/largest-remainder or a designated dust account).

---

### 6. Cross-System Trade-Off Matrix and FFI Verification Boundaries

Basis: derived (synthesized from primary sources in §§1–5)

| Dimension | `Catala` (`7a0c93be`) | `Natural L4` (`3a679a7a`) | `Marlowe` (`7b5b1e90`) | `Move` (`c453c909`) | `TigerBeetle` (`a2a3c706`) |
|---|---|---|---|---|---|
| **Primary Domain** | Constitutive statutory law (tax, benefits) | Regulative multi-party contracts (obligations) | Finite financial derivatives on-chain | Programmable linear digital assets | High-throughput double-entry settlement |
| **Core Formalism** | Prioritized Default Calculus (`Empty\|Val\|Conflict`) | Defeasible Deontic Logic (`MUST\|MAY\|SHANT`, `HENCE`/`LEST`) | Continuation contract algebra (`Close\|Pay\|If\|When\|Let\|Assert`) | Linear/affine bytecode abilities (`Copy\|Drop\|Store\|Key`) | Strict double-entry `u128` 2PC state machine |
| **Termination** | Enforced (no general recursion in core) | Finite automata (bounded clocks / states) | Mechanically proven (`TransactionBound.thy`) | Metered (gas) / arbitrary loops | Bounded single-pass batch execution |
| **Arithmetic Model** | Exact $\mathbb{Z}$, $\mathbb{Q}$, cents; half-away-from-zero | Symbolic / SMT `Int` & `Time` (`Float`) | Arbitrary-precision integers (`Int`) | Unsigned fixed-width (`u8`..`u256`), abort on overflow | Checked `u128` balances; explicit overflow status |
| **Verification Oracle** | Coq (`catala-formalization`) + Z3 VC (`conditions.ml`) | UPPAAL timed automata + SMT (`TimedMC`) | Isabelle/HOL (`AssetsPreservation`, `CloseSafe`) + SMT | Bytecode verifier (absint) + Move Prover (Boogie/Z3) | Deterministic Simulation Testing (DST) + `comptime` layout checks |
| **Critical FFI / Boundary Seam** | C `__thread` arena lifetime & `longjmp` across C++/Rust; JSON float truncation | Webhook/ERP clock skew & unverified runtime monitors | External oracle inputs & portfolio close-out netting | Linearity destroyed on serialization to Rust/C/JSON/EVM | Network retry idempotency & external ledger DvP split-brain |

**Core Cross-Boundary Verification Invariant:** Across all five systems, formal guarantees hold *only inside the closed execution boundary* of the respective semantics. Crossing an FFI seam degrades guarantees along four concrete vectors: (1) **Error-lattice collapse** (`Catala` `NoValue`/`Conflict` -> C `longjmp`/`abort()`), (2) **Numeric representation drift** (exact $\mathbb{Q}$/cents -> IEEE-754 JSON `Number` or Python banker's `round`), (3) **Linearity erasure** (`Move` non-`Copy`/non-`Drop` resource -> copyable/droppable Rust/C struct or duplicate network message), and (4) **Temporal/transactional leakage** (unversioned wall-clock/SQL reads leaking into bi-temporal legal audits, or non-transactional side effects escaping rollback).

## Boundaries

- **Known not to apply:**
  - *Closed-world algorithmic formalization of open-textured legal predicates:* Legal standards such as "reasonable effort", "good faith", or "undue hardship" cannot be formally decided by Catala, L4, or SMT solvers; encoding ad-hoc numeric thresholds silently usurps legislative/judicial discretion. Such predicates must remain explicit external inputs/oracle parameters whose values are captured in decision audit traces.
  - *Move linear bytecode conservation in non-transactional hosts:* Because `Move`'s `locals_safety` treats `Bytecode::Abort` as a no-op (`locals_safety/mod.rs:94`), transplanting Move's linear ability rules directly into a non-transactional OS or Rust runtime without either totality proofs or explicit linear unwind compensation is unsound under runtime aborts/panics.
  - *Pairwise compositional valuation of `Composing Contracts` under counterparty default:* Close-out netting and collateralization are portfolio-level invariants that do not distribute cleanly over independent `and c1 c2` subcontracts.
- **Unsupported (explicitly observed in source):**
  - `smucclaw/dsl` `LS/XPile/Uppaal.hs` (`3a679a7a`, lines 59, 73–74) explicitly marks recursive `HENCE` chains, nested regulative rules, and multi-party scoping as unimplemented `TODO`s in its UPPAAL transpiler.
  - `CatalaLang/catala` `compiler/verification/conditions.ml` (`7a0c93be`, lines 164–168) explicitly notes that justifications (`just`) containing nested default terms are not fully encoded in the current Z3 VC generator.
  - `CatalaLang/catala` C runtime (`runtimes/c/catala_runtime.c:58-61`) does not support recovering from Catala errors raised outside a `catala_do` `setjmp` guard (terminates via `abort()`).
- **Unknown:**
  - *Compositional cross-jurisdiction default-tree linking:* Whether separately compiled Catala statutory modules (e.g., a state tax code overriding sub-definitions of a precompiled federal module) can link exception trees and discharge conflict-freedom compositionally without whole-program recompilation remains an open research problem.
  - *Static numerator/denominator bit-width bounding for zero-allocation rational codegen:* Whether acyclic statutory DAGs in Catala admit tight static upper bounds on rational bit-widths sufficient to replace GMP/heap allocation with fixed-width stack arithmetic in C/Rust/Wasm was not established.
  - *Cross-FFI preservation of linear resources into non-linear hosts:* Designing zero-overhead capability-sealing protocols (e.g., single-use handle tables or CHERI capabilities) that preserve Move-grade conservation across Rust/C/Wasm FFI without reverting to dynamic reference counting remains open.
- **Not examined:**
  - `digital-asset/daml` Canton sub-transaction privacy protocol implementation internals and `openfisca/openfisca-core` Python vectorization/bi-temporal parameter engine were not directly source-inspected in this investigation (only top-level repository identities were resolved).
  - Catala's ReScript (`runtimes/rescript/`) and js_of_ocaml (`runtimes/jsoo/`) runtimes and the Move Prover Boogie translator implementation (`language/move-prover/`) were not directly audited line-by-line.
  - Later Sui Move object-centric ownership extensions (`MystenLabs/sui`) and Aptos Move v2 compiler passes were not compared line-by-line against `move-language/move` (`c453c909`).

## Evidence

### Primary Git Sources Inspected (Observed 2026-11-19)
- `CatalaLang/catala` @ `7a0c93beda25b903ebcdfe64d672caf53dd41370`:
  - `compiler/lcalc/from_dcalc.ml:32-207` (`translate_typ`, `translate_default`, `translate_expr` lowering `TDefault` to `TOption (TTuple [t; TLit TPos])` and `Op.HandleExceptions`).
  - `compiler/verification/conditions.ml:88-289` (`half_product`, `generate_vc_must_not_return_empty`, `generate_vc_must_not_return_conflict`, `verification_condition_kind`).
  - `compiler/verification/z3backend.ml:1-80` (Z3 context, sort mappings, counterexample variable tracking).
  - `runtimes/ocaml/catala_runtime.ml:21-194, 236-250, 1026-1044` (`round`, `money_round`, `integer_of_decimal`, `integer_of_money`, `date_rounding`, `compare_periods`, `handle_exceptions`).
  - `runtimes/c/catala_runtime.c:30-250, 1138-1217` (`catala_error` `setjmp`/`longjmp`/`abort()`, `__thread struct catala_heap`, `catala_malloc`/`catala_free_all`, `round_div`, `o_toint_rat` vs. `o_toint_mon`, `o_round_rat`, `o_round_mon`).
  - `runtimes/python/src/catala/catala_runtime.py:480-616, 832-848` (`Integer`, `Decimal(Value, Fraction)`, `Money(Value, int)`, custom `def round(q)` half-away-from-zero, `handle_exceptions`).
  - `runtimes/java/catala/runtime/CatalaDecimal.java:1-160` & `CatalaMoney.java:125-137` (vendored `BigFraction`, `RoundingMode.HALF_UP`).
- `CatalaLang/catala-formalization` @ `985eb86afb7c6bd3d020fb99ea9e391b93576d44`:
  - `CLAIMS.md` (explicit axiom inventory: `FunctionalExtensionality` + `measure` termination assumption in `theories/catala/typing.v`).
  - `theories/catala/syntax.v:18-46` (`term` and `value` inductives including `ErrorOnEmpty`, `DefaultPure`, `Default`, `Empty`, `Conflict`).
  - `theories/catala/trans.v:129-195` (`trans_conts`, `trans_return`, `trans_state`, `Theorem correction_continuations`).
- `MLanguage/mlang` @ `66f6b37308c0dfeb3bb24c8af7952a522452a1af`:
  - `src/mlang/m_ir/mir_roundops.ml:17-79` (`DefaultRoundOps`, `MultiRoundOps`, `MainframeRoundOps` with `0.5 +. (epsilon *. 50.)`, `-0` comment, `max_long` guard).
- `smucclaw/dsl` @ `3a679a7a2dfd935f562dd335f708e6c5a3b5bb64`:
  - `lib/haskell/natural4/src/LS/Types.hs:619` (`data Deontic = DMust | DMay | DShant`).
  - `lib/haskell/natural4/src/LS/Rule.hs:152-235, 305-330` (`Regulative`, `Constitutive`, `Hornlike`, `RuleAlias`, `RegFulfilled`, `RegBreach`).
  - `lib/haskell/natural4/src/LS/XPile/Uppaal.hs:1-75` (`toL4TA`, `henceChannels`, explicit `TODO` markers on recursive `Hence`, nested rules, and party handling).
- `smucclaw/baby-l4` @ `f351e4e8d435e3f5800653b558de2571ed19740c`:
  - `src/TimedMC.hs:1-75` (`ATrans`, `DTrans`, `transitionFunTp`, SMT-encoded TCTL timed model checker).
- `input-output-hk/marlowe` @ `7b5b1e900ec53a8eb18747992bec73470704dfcb`:
  - `isabelle/Core/SemanticsTypes.thy:257-269` (`datatype Case` and `Contract`).
  - `isabelle/Core/AssetsPreservation.thy` (`theorem playTrace_preserves_assets`).
  - `isabelle/Core/CloseSafe.thy` (`theorem closeIsSafe`, `closeIdemp_reduceContractUntilQuiescent`).
  - `isabelle/Core/TransactionBound.thy` (`reductionLoop_reduces_maxTransactions`, `countWhens`).
- `move-language/move` @ `c453c90994cba0af30314fe4134acee57fb20d0c`:
  - `language/move-binary-format/src/file_format.rs:578-638` (`enum Ability`, `Ability::requires`, `Ability::required_by`, `AbilitySet`).
  - `language/move-bytecode-verifier/src/ability_field_requirements.rs:1-52` (`verify_module_impl`, `FIELD_MISSING_TYPE_ABILITY`).
  - `language/move-bytecode-verifier/src/locals_safety/mod.rs:35-100` (`StLoc` `STLOC_UNSAFE_TO_DESTROY_ERROR`, `Ret` `UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`, `Abort` no-op).
  - `language/move-bytecode-verifier/src/verifier.rs:56-125` (`verify_module_with_config` pass ordering and `catch_unwind`).
- `tigerbeetle/tigerbeetle` @ `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`:
  - `src/tigerbeetle.zig:45-167` (`AccountFlags`, `AccountBalance` 128-byte `u128` layout, `TransferFlags` two-phase pending/post/void & balancing flags).

### Peer-Reviewed Papers Verified
- Denis Mérigoux, Nicolas Chataing, Jonathan Protzenko, *Catala: A Programming Language for the Law*, PACMPL 5 (ICFP 2021), `doi:10.1145/3473582`, `arXiv:2103.03198`.
- How Khang Lim, Avishkar Mahajan, Martin Strecker, Meng Weng Wong, *Automating Defeasible Reasoning in Law*, `arXiv:2205.07335` (`doi:10.48550/arXiv.2205.07335`).
- Simon L. Peyton Jones, Jean-Marc Eber, Julian Seward, *Composing Contracts: An Adventure in Financial Engineering*, ICFP 2000, `doi:10.1145/351240.351267`.
- Pablo Lamela Seijas, Simon Thompson, *Marlowe: Financial Contracts on Blockchain*, ISoLA 2018, `doi:10.1007/978-3-030-03427-6_27`.
- Jingyi Emma Zhong et al., *The Move Prover*, CAV 2020, `doi:10.1007/978-3-030-53288-8_7`.

### Execution Probe (Python 3.13.15, Observed 2026-11-19)
Reproducible standalone probe executing the default-calculus evaluator, Catala vs. Python banker's vs. `Mlang` rounding, and integer-cent rounding dust:

```python
import math
from fractions import Fraction

def catala_round(q: Fraction) -> int:
    sgn = -1 if q < 0 else (1 if q > 0 else 0)
    aq = abs(q)
    return sgn * ((2 * aq.numerator + aq.denominator) // (2 * aq.denominator))

def mlang_round(x: float, eps: float = 1e-6) -> int:
    e = 0.5 + 50.0 * eps
    return int(math.ceil(x - e)) if x < 0.0 else int(math.floor(x + e))

for q in [Fraction(1,2), Fraction(-1,2), Fraction(5,2), Fraction(-5,2), Fraction(49999,100000)]:
    print(q, catala_round(q), round(q), mlang_round(float(q)))
```

Recorded outputs on Python 3.13.15:
- Overlapping default exceptions `['Art.42', 'Art.89']` raise `Conflict(['Art.42', 'Art.89'])`.
- `1/2`: `catala_round=1`, `py_bankers=0`, `mlang_eps=1`.
- `-1/2`: `catala_round=-1`, `py_bankers=0`, `mlang_eps=-1`.
- `5/2`: `catala_round=3`, `py_bankers=2`, `mlang_eps=3`.
- `-5/2`: `catala_round=-3`, `py_bankers=-2`, `mlang_eps=-3`.
- `49999/100000`: `catala_round=0`, `py_bankers=0`, `mlang_eps=1`.
- Integer-cent rounding dust: `10000 // 3 = 3333`, `3333 * 3 = 9999`, `dust = 1`.

## Revalidation

1. **Catala default lowering and cross-backend rounding parity:** Diff `compiler/lcalc/from_dcalc.ml`, `compiler/verification/conditions.ml`, and the four runtime rounding functions (`runtimes/ocaml/catala_runtime.ml:round`, `runtimes/c/catala_runtime.c:round_div`, `runtimes/python/src/catala/catala_runtime.py:round`, `runtimes/java/catala/runtime/CatalaDecimal.java:round`) against newer `CatalaLang/catala` revisions. Check whether `conditions.ml` still expands `half_product` quadratically and whether justification default terms are now handled.
2. **Catala Coq proof axioms:** Inspect `CLAIMS.md` and `theories/catala/typing.v` in `CatalaLang/catala-formalization` to verify whether the termination `measure` hypothesis has been discharged or whether `compiler/lcalc/from_dcalc.ml`'s exact optimization cases (e.g., single-exception `match_some`) have been integrated into `trans.v`.
3. **Natural L4 UPPAAL completeness:** Grep `LS/XPile/Uppaal.hs` in newer `smucclaw/dsl` (or successor L4 repositories) for removal of the `-- TODO: Handle recursive Hence` / `-- TODO Nested` / `-- TODO Handle party` markers and verify whether multi-party timed-game synthesis is supported.
4. **Move verifier linearity under `Abort`:** Diff `language/move-bytecode-verifier/src/locals_safety/mod.rs` and `verifier.rs` in `move-language/move` (or Sui/Aptos forks) to check whether `Bytecode::Ret`, `Bytecode::StLoc`, `Bytecode::Abort`, and `Ability::requires()` preserve the same linearity and rollback assumptions.
5. **Marlowe Isabelle proofs:** Check `isabelle/Core/AssetsPreservation.thy`, `CloseSafe.thy`, and `TransactionBound.thy` in `input-output-hk/marlowe` for any additions to `datatype Contract` that alter conservation or transaction-bound proofs.
