# String Word-Equation SMT Solvers and Verified Batch vs. Incremental Parsing

## Summary

Automated reasoning over strings and formally verified parsing sit at opposite ends of formal language theory—decision procedures for string constraints and executable recognizers for context-free/context-sensitive syntax—yet share identical architectural fault lines: decidability cliffs, hidden lexer/tokenizer state, alphabet/encoding mismatches, and soundness vs. termination trade-offs.

1. **String SMT decidability cliff:** Pure word equations with regular membership are decidable in PSPACE (Plandowski 2004; Jeż 2016 recompression), while adding unrestricted length constraints remains a major open problem and adding arbitrary finite-state transductions or unrestricted `replaceAll` with shared variables is undecidable (Lin & Barceló 2016; Chen et al. 2018). Decidable completeness for complex operations (`concat`, `reverse`, `replaceAll`, transducers, length/Parikh) is recovered only under structural acyclicity: **OSTRICH** (`uuverifiers/ostrich` @ `806aa9fad141bb41b1fb111b6369b45b4a9390ed`) achieves completeness on the **straight-line** (and chain-free) fragment via backward regular pre-image propagation (`PreOp`) and cost-enriched Parikh automata (`ParikhExploration`), while **cvc5** (`7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`), **Z3 `theory_seq`** (`c73b745cef365e1390408fbd7c599236941d34d1`), and **Z3str4** (`FM 2021`) target general SMT-LIB 2.7 Unicode strings (`196,608` code points, `U+0000..U+2FFFF`) using incomplete-in-general word-equation splitting, length-aware regex derivatives/automata, and multi-armed portfolio selection. Notably, `OstrichStringTheory.scala` pins `alphabetSize = 0x10000` (16-bit BMP), diverging semantically from SMT-LIB 2.7 on supplementary planes `U+10000..U+2FFFF`.
2. **Verified batch parsing splits along generator-validation vs. general-CFG execution:** **CompCert's MenhirLib** (`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`) leaves LR(1) table generation untrusted and checks five safety invariants (`Validator_safe.is_safe`) and eight completeness invariants (`Validator_complete.is_complete`) inside Coq to obtain `parse_correct`, `parse_complete`, and `unambiguity`, parameterized by a step-fuel exponent (`log_fuel = 50`, i.e., $2^{50}$ steps, in `cparser/Parse.ml`) and relying on an unverified OCaml `pre_parser` + lexer feedback loop for C's typedef-name context sensitivity. **CoStar** (`slasser/CoStar` @ `a213d4d7ef738cc56e5e73e84ca465f0e80f4583`) proves soundness, completeness, ambiguity detection (`Accept` vs. `Ambig`), and fuel-free well-founded termination (`Acc lex_nat_triple`) for ALL(*) parsing over *arbitrary* non-left-recursive CFGs by verifying that SLL lookahead simulation soundly overapproximates full-context LL prediction (`SLL_optimization_sound.approx`).
3. **Incremental GLR subtree reuse soundness hinges on five non-obvious guards:** In **Tree-sitter** (`tree-sitter/tree-sitter` @ `f0090e112482d66653b43ca73e85668db1cde794`), generalizing Wagner–Graham incremental LR parsing to GLR with stateful C/Wasm external scanners requires checking (a) `total_size.bytes + lookahead_bytes` edit-horizon invalidation, (b) `depends_on_column` column-shift propagation, (c) byte-for-byte `external_scanner_state_eq` (up to `TREE_SITTER_SERIALIZATION_BUFFER_SIZE = 1024` bytes), (d) `fragile_left || fragile_right` rejection of ambiguously constructed subtrees, and (e) first-leaf lex-mode/keyword-capture/reserved-word compatibility (`ts_parser__can_reuse_first_leaf`). To maintain interactive latency, Tree-sitter enforces a hard GLR concurrency ceiling (`MAX_VERSION_COUNT = 6`), trading theoretical GLR completeness for bounded parse latency.

## Applicability

This report synthesizes and compares two coupled verification domains across eight pinned durable subjects:

- **String SMT solvers (comparison against the normative SMT-LIB 2.7 UnicodeStrings standard):**
  - `uuverifiers/ostrich` @ `806aa9fad141bb41b1fb111b6369b45b4a9390ed` (Scala/Princess-based solver implementing straight-line backward propagation, Nielsen splitting, and cost-enriched automata / Parikh exploration).
  - `Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1` (`src/smt/theory_seq.*`, `seq_eq_solver.cpp`, `seq_regex.cpp`; note that legacy `theory_str` / Z3str3 is no longer present under `src/smt/` at this revision).
  - `Z3str4` (Mora et al., FM 2021, DOI `10.1007/978-3-030-90870-6_21`) and its regular-expression + linear-arithmetic arm `Z3str3RE` (Berzish et al., CAV 2021, DOI `10.1007/978-3-030-81688-9_14`), characterized from their peer-reviewed publications rather than a separate repository snapshot.
  - `cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc` (`src/theory/strings/strategy.cpp` and companion sub-solvers).
- **Verified batch and incremental parsers (architectural comparison across grammar classes and trust boundaries):**
  - `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc` (`MenhirLib/*.v` Coq LR(1) validator and interpreter, plus `cparser/Parse.ml` driver).
  - `slasser/CoStar` @ `a213d4d7ef738cc56e5e73e84ca465f0e80f4583` (`parser/*.v` Coq verified ALL(*) parser).
  - `tree-sitter/tree-sitter` @ `f0090e112482d66653b43ca73e85668db1cde794` (`lib/src/{parser.c,parser.h,subtree.h,subtree.c,reusable_node.h}` C incremental GLR runtime), interpreted against the Wagner & Graham (TOPLAS 1998, DOI `10.1145/293677.293678`) incremental parsing framework.

Findings about specific source-level invariants (alphabet bounds, `MAX_VERSION_COUNT`, `log_fuel`, `PreOp` contract, `Validator_safe`/`Validator_complete` conjuncts, `Icp`-free CoStar theorems) apply strictly to the pinned revisions above. Complexity and decidability theorems apply mathematically to the defined logic fragments independent of solver version. Executable micro-probes run under standard Python 3 (stdlib only) characterize the mathematical transducer pre-image semantics and Tree-sitter's reuse predicate logic; they do not substitute for running compiled OSTRICH, Z3, cvc5, Coq, or Tree-sitter binaries.

## Findings

### 1. Decidability and Complexity Boundaries for String Constraints

Basis: normative (SMT-LIB 2.7 UnicodeStrings) + derived (peer-reviewed theorems: Plandowski 2004, Jeż 2016, Lin & Barceló 2016, Chen et al. 2018, Chen et al. 2019)

The SMT-LIB 2.7 Theory of Unicode Strings defines `String` over a finite alphabet $\Sigma$ of cardinality **$196{,}608$** (`U+0000` through `U+2FFFF`, covering Planes 0–2 rather than full Unicode `U+10FFFF`) and `RegLan` over regular expressions (`re.++`, `re.union`, `re.*`, `re.inter`, `re.comp`, `re.diff`, `re.range`, `re.loop`), alongside concatenation (`str.++`), length (`str.len`), code-point conversion (`str.to_code`, `str.from_code`), substring/indexing (`str.substr`, `str.indexof`), and leftmost replacement (`str.replace`, `str.replace_all`, `str.replace_re`, `str.replace_re_all`).

Combining these primitives crosses sharp decidability boundaries:

| String Logic Fragment | Decidability / Complexity | Key Result & Mechanism | Practical Implication for Solvers |
| :--- | :--- | :--- | :--- |
| Pure word equations ($\bigwedge_i u_i = v_i$, constants + variables) | **Decidable (PSPACE, linear space NSPACE$(n \log n)$)** | Makanin (1977) decidability; Plandowski (JACM 2004, `10.1145/990308.990312`) PSPACE; Jeż (JACM 2016, `10.1145/2743014`) local recompression | Complete algorithms exist, but worst-case minimal solution lengths can be doubly exponential in equation size; SMT solvers use heuristic Nielsen/Levi splitting instead of full recompression. |
| Word equations + regular membership (`str.in_re`) | **Decidable (PSPACE)** | Schulz (1990) / Plandowski / Jeż recompression preserves regular membership | Regular constraints alone do not break decidability, though complementation (`re.comp`) and intersection (`re.inter`) can incur exponential DFA blowup. |
| Word equations + linear integer arithmetic over lengths (`str.len`) | **Open problem** (decidable for quadratic / acyclic / straight-line fragments) | Longstanding open question connecting word equations and Diophantine equations (Matiyasevich) | General SMT solvers (`cvc5`, `Z3`, `Z3str4`) are **sound** (modulo bugs) on SAT/UNSAT answers they return, but **incomplete** (may diverge or return `unknown`). |
| Word equations + finite-state transducers (or `replaceAll` with non-straight-line sharing) | **Undecidable** | Lin & Barceló (POPL 2016, `10.1145/2837614.2837641`); Chen et al. (POPL 2018, `10.1145/3158091`) | Even a single equation $x = T(x)$ or cyclic dependency across `replaceAll` encodes Post Correspondence Problem / Turing machine computation histories. |
| **Straight-line** (acyclic SSA) `concat` + `replaceAll` + transducers + `reverse` + regular constraints | **Decidable (EXPSPACE / N2EXPTIME depending on length/Parikh)** | Chen et al. (POPL 2018 `10.1145/3158091`; POPL 2019 `10.1145/3290362`) | Acyclic dataflow $x_i = f_i(x_1,\dots,x_{i-1})$ allows exact backward pre-image propagation of regular constraints to input leaves without cycles. |
| Straight-line + linear length / character-count (Parikh) constraints + `substr`/`indexof` | **Decidable (via Cost-Enriched Automata / Parikh images)** | Chen et al. (POPL 2019 `10.1145/3290362`; OSTRICH2 CEA/Parikh) | Regular pre-images are enriched with integer register updates; leaf feasibility reduces to Presburger arithmetic (LIA) over Parikh images. |
| Regular membership + linear length arithmetic (no word equations, no transducers) | **Decidable (NP / PSPACE depending on regex ops)** | Parikh's theorem (semilinear length sets of NFA/DFA) | Target of `Z3str3RE` (CAV 2021, `10.1007/978-3-030-81688-9_14`): length-aware automata intersection and pruning. |

**Why straight-line acyclicity is load-bearing:** In a straight-line conjunction $\bigwedge_{i=1}^m x_i = f_i(\vec{y}_i) \land \bigwedge_j x_j \in L(A_j)$ where every variable $x_i$ is defined at most once and the dependency graph is a DAG, every string operation $f_i$ whose inverse image preserves regularity ($f_i^{-1}(L(A)) = \bigcup_{k=1}^K L(B_{k,1}) \times \dots \times L(B_{k,r})$—a finite union of recognizable relations) can be eliminated backwards in reverse topological order. Once all intermediate definitions are projected onto leaf variables, each leaf holds an intersection of regular languages (or cost-enriched automata), whose emptiness is decidable. Breaking acyclicity (e.g., $x = \text{concat}(y, z) \land y = \text{replaceAll}(x, a, b)$) or defining a variable twice ($x = f(y) \land x = g(z)$ without finite decomposition) breaks termination of backward saturation.

---

### 2. OSTRICH Architecture: Backward Pre-Image Calculus, Leftmost-Longest `ReplaceAll`, and Cost-Enriched Parikh Solving

Basis: source (`uuverifiers/ostrich` @ `806aa9fad141bb41b1fb111b6369b45b4a9390ed`) + execution (Probe 1A)

OSTRICH is implemented as a theory plugin inside the Princess SMT solver. Inspection of its Scala implementation reveals four critical architectural invariants and one major SMT-LIB conformance divergence:

#### 2.1 The `PreOp` Contract (`PreOp.scala:44-105`)
Every backward-propagatable string operator implements `trait PreOp`:

```scala
def apply(argumentConstraints : Seq[Seq[Automaton]],
          resultConstraint : Automaton)
        : (Iterator[Seq[Automaton]], Seq[Seq[Automaton]])
```

The contract documented and enforced in `src/main/scala/ostrich/preop/PreOp.scala:46-68` has three obligations:
1. **Soundness (containment in pre-image):** Every tuple of words accepted by any returned automaton tuple $(A_1, \dots, A_n)$ must map under $f$ into `resultConstraint`.
2. **Relative completeness (subsumption):** Every tuple accepted by `argumentConstraints` whose image under $f$ lies in `resultConstraint` must be accepted by at least one tuple in the returned `Iterator[Seq[Automaton]]`.
3. **Dependency tracking:** The second tuple component returns the subset of `argumentConstraints` actually consulted to prune the pre-image, enabling sound conflict-clause extraction in `BackwardsSaturation`.

Each `PreOp` may additionally supply sound linear-arithmetic abstractions via `lengthApproximation` (`L82-84`), per-character Parikh count abstractions via `charCountApproximation` (`L94-97`), and forward over-approximations via `forwardApprox` (`L103-104`).

#### 2.2 Priority-Guided Backward Saturation and Length-Guided Nielsen Splitting
- **`BackwardsSaturation` (`src/main/scala/ostrich/proofops/BackwardsSaturation.scala:57-228`):** Implements Princess's `SaturationProcedure("BackwardsPropagation")`. For every application point `(funApp, argCon)` where `funApp` encodes $x = f(y_1, \dots, y_n)$ and `argCon` is `str_in_re_id(x, autid)` (or `None` for $\Sigma^*$), `handleApplicationPoint` (`L160-223`) computes `op(argAuts, resAut)`, filters out tuples containing an empty automaton (`L195`), increments constraint age (`age + 1`, `L201`), and emits a Princess `AxiomSplit(assumptions, argCases, theory)` (`L221`). Priority scheduling (`applicationPriority`, `L135-158`) ranks splits by automaton state size plus a `+100` penalty on `str_++` (`computePenalty`, `L119-123`) and a `-5` bonus per concrete constant (`computeConstantBonus`, `L125-133`), deferring high-branching concatenation splits (which produce $O(|Q|^{k-1})$ disjuncts for $k$-ary concat over a $|Q|$-state DFA; see Probe 1A.4).
- **`OstrichNielsenSplitter` (`src/main/scala/ostrich/proofops/OstrichNielsenSplitter.scala:77-250`):** Outside the pure straight-line fragment, OSTRICH falls back to length-model-guided Nielsen splitting. Given two concatenation trees for the same term, `chooseSplit` (`L137-182`) queries Princess's integer model (`lengthModel: ReduceWithConjunction`) for the concrete length `splitLenConc` of the left operand (`L141`), walks the opposing concatenation tree until locating the exact symbolic term `symToSplit` straddling that offset (`L176-182`), and splits the proof into either `splittingFormula` (introducing fresh `leftSplitSym`, `rightSplitSym` with `leftSplitSym ++ rightSplitSym = symToSplit`, `L184-199`) or `diffLengthFormula` (`splitLen < leftTermsLen || splitLen > leftTermsLen + len(symToSplit)`, `L201-211`).

#### 2.3 Leftmost-Longest `ReplaceAll` Transducer Construction (`ReplaceAllPreOp.scala:326-420`)
In `ReplaceAllLongestPreOpRegEx.buildTransducer` (`src/main/scala/ostrich/preop/ReplaceAllPreOp.scala:358-420`), leftmost-longest regex matching for $x = \text{replaceAll}(y, e, z)$ is compiled into a finite-state transducer over states `(Mode, noreach : Set[aut.State])`:
- `Mode` is one of `NotMatching`, `Matching(frontier: Set[aut.State])` (inside an active candidate match), or `EndMatch(frontier: Set[aut.State])` (just completed a match).
- `noreach` tracks NFA states of previously bypassed/shortened matches that **must never reach an accepting state**; any transducer state where `noreach.exists(aut.isAccept(_))` is non-accepting and pruned from the worklist (`goodNoreach = !noreach.exists(aut.isAccept(_))`, `L394-401`).
- Matched spans are rewritten to a distinguished sentinel `OutputOp("", Internal, "")` (`internalChar`, `L371`), separating regex match localization from symbolic replacement insertion in `ReplaceAllPreOpTran` (`L607`).
- **Explicit source boundary (`L356`):** `// TODO: currently does not handle empty matches` — regexes accepting $\varepsilon$ are not handled by `ReplaceAllLongestPreOpRegEx.buildTransducer`.

#### 2.4 Cost-Enriched Automata (`ParikhExploration.scala:88-250`) and Alphabet Divergence (`OstrichStringTheory.scala:70-74`)
- **Cost-Enriched Parikh Solving (OSTRICH2):** `src/main/scala/ostrich/cesolver/core/ParikhExploration.scala:111-234` topologically sorts all `PreOp` applications (including `LengthCEPreOp`, `SubStringCEPreOp`, and `IndexOfCEPreOp`, lifting integer terms to the topological front, `L164-165`). When inputs leave the straight-line fragment, the code explicitly logs and degrades:
  - Cyclic definitions (`remFunApps.nonEmpty`, `L184-187`): `"WARNING: cyclic definitions found, ignoring ..."` (drops cyclic applications into `ignoredApps`).
  - Multiply-defined non-concrete string variables (`nonTreeLikeApps`, `L221-233`): `"Warning: input is not straightline, some variables have multiple definitions"`.
- **Semantic Divergence — 16-bit BMP Alphabet vs. SMT-LIB 2.7 (`OstrichStringTheory.scala:70-74`):**
  ```scala
  // TODO: at some point this has to be fixed, Unicode is
  // bigger. Seems to be a problem with the BRICS automata library;
  // use Unicode-16 encoding?
  val alphabetSize = 0x10000
  ```
  OSTRICH restricts `CharSort` to `[0, 0xFFFF]` (`65,536` characters), whereas SMT-LIB 2.7 defines `UnicodeStrings` over `[0, 0x2FFFF]` (`196,608` characters). Consequently, any satisfiable SMT-LIB formula requiring a supplementary-plane code point (e.g., `(and (= (str.len x) 1) (= (str.to_code x) 128512))`, `U+1F600`) is **unsatisfiable under OSTRICH's BMP domain** (Probe 1A.3).

---

### 3. General SMT-LIB String Solvers: Z3 `theory_seq`, Z3str4 / Z3str3RE, and cvc5

Basis: source (`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`, `cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`) + documentation (`FM 2021`, `CAV 2021`)

General SMT-LIB string solvers target unconstrained word equations + LIA lengths + extended functions (`substr`, `indexof`, `replace`, `to_int`) + regexes without requiring straight-line form:

#### 3.1 Z3 `theory_seq` (`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`)
At HEAD `c73b745cef365e1390408fbd7c599236941d34d1`, upstream Z3 implements string solving solely through `theory_seq` (`src/smt/theory_seq.h`, `seq_eq_solver.cpp`, `seq_ne_solver.cpp`, `seq_regex.cpp`, `seq_offset_eq.cpp`); legacy `theory_str` (Z3str3) is absent from `src/smt/`. Key source-verified mechanisms:
- **Dependency-tracked equation reduction (`seq_eq_solver.cpp:46-108`):** `theory_seq::solve_eqs` iteratively canonizes equations `e.ls = e.rs` (`L69-70`), applies `simplify_eq`, `lift_ite`, delegates to `m_eq.reduce(er, r)` (`L88`), and resolves elementwise `solve_nth_eq`. Under suspended cancellation limits, eager reductions are bounded to `1024` steps (`m_num_eager_eq_steps >= 1024`, `L37`). Every derived lemma carries exact `dependency*` provenance linearized into SAT conflict clauses (`add_consequence`, `L110-127`).
- **Monadic derivative regex solver (`seq_regex.cpp:30-145`):** Regex membership uses symbolic Brzozowski (`brz`) or light Antimirov (`light-ant`) derivatives (`monadic_transition_mode`, `L30-36`) in `forward`, `reversed`, or `retry` orientation (`L38-46`). Crucially, `seq_regex::compute_expansion` (`L102-124`) and `add_monadic_membership` (`L126-145`) expand `s` through defining word equations (e.g., `x = x8 ++ "/" ++ s9`) before passing `s_expanded` to `m_monadic`—with a depth-40 guard (`L73`) and fallback skipping `seq.unit(nth ..)` length-representation pollution (`L86-99`)—specifically to prevent witness/equality livelock (`L131-134`), folding equality dependencies into unsat cores for soundness.

#### 3.2 Z3str4 & Z3str3RE (`FM 2021` / `CAV 2021`)
- **Z3str3RE** (Berzish et al., CAV 2021, DOI `10.1007/978-3-030-81688-9_14`) specializes in regex + linear length constraints via length-aware automata: propagating length bounds directly into automaton state reachability and using length abstractions to prune expensive product-automaton intersections.
- **Z3str4** (Mora, Berzish, Kulczynski, Nowotka, Ganesh, FM 2021, DOI `10.1007/978-3-030-90870-6_21`) wraps multiple complementary string backends (including arrangement-based `Z3str3RE` and sequence-based `Z3seq`) inside a **multi-armed contextual bandit algorithm selector** trained over syntactic formula features (word-equation density, regex depth, length arithmetic coupling), mitigating individual solver pathology across heterogeneous SMT-LIB benchmarks.

#### 3.3 cvc5 Theory of Strings (`cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`)
In `src/theory/strings/strategy.cpp:113-181`, cvc5 executes an explicit, deterministically ordered staged inference pipeline at `EFFORT_FULL` (short-circuiting on each `BREAK` whenever lemmas or conflicts are emitted):
1. `CHECK_INIT` $\to$ `CHECK_CONST_EQC` (constant equivalence classes) $\to$ `CHECK_EXTF_EVAL(0)` (context-independent extended-function evaluation) $\to$ `CHECK_CYCLES` (**must precede flat forms**, `L131`) $\to$ `CHECK_FLAT_FORMS`.
2. `CHECK_EXTF_REDUCTION_EAGER` $\to$ `CHECK_MEMBERSHIP_EAGER` (cheap regex rewrites/entailment before word-equation splits).
3. `CHECK_NORMAL_FORMS_EQ_PROP` $\to$ `CHECK_NORMAL_FORMS_EQ` (Levi's lemma / normal-form splitting on $x_1 \cdots x_m = y_1 \cdots y_n$) $\to$ `CHECK_EXTF_EVAL(1)` $\to$ `CHECK_NORMAL_FORMS_DEQ` (disequality arrangement) $\to$ `CHECK_CODES` (`str.to_code` injectivity/bounds over `[0, 196607]`).
4. `CHECK_LENGTH_EQC` $\to$ optional `CHECK_SEQUENCES_ARRAY_*` $\to$ `CHECK_EXTF_REDUCTION` (lazy axiomatic reduction of `substr`/`indexof`/`replace` into word equations + LIA) $\to$ `CHECK_MEMBERSHIP` (derivative/automaton unfolding) $\to$ `CHECK_CARDINALITY` (ensuring distinct equivalence classes fit within finite $|\Sigma|^k$ strings of length $k$).
5. At `EFFORT_LAST_CALL` (when `stringModelBasedReduction` is enabled, `L160-170`), cvc5 runs `CHECK_EXTF_EVAL(3)` $\to$ `CHECK_EXTF_REDUCTION` $\to$ `CHECK_MEMBERSHIP` lazily against the candidate model.

| Dimension | OSTRICH (`806aa9fa`) | Z3 `theory_seq` (`c73b745c`) | Z3str4 (`FM 2021`) | cvc5 (`7507ed17`) |
| :--- | :--- | :--- | :--- | :--- |
| **Core Calculus** | Backward regular/CEA pre-image (`PreOp`) + Nielsen fallback | Canonizing equation solver + Brzozowski/Antimirov monadic regex derivatives | Multi-armed bandit portfolio (`Z3str3RE` length-aware automata + `Z3seq`) | Staged normal-form splitting + lazy extended-fn reduction + regex derivatives |
| **Complete Fragment** | Straight-line `concat` + `replaceAll` + transducers + length/Parikh (provably complete) | Regular + acyclic cases; incomplete on general `WordEq + Len` | Incomplete in general; strong on `RegLan + LIA` via `Z3str3RE` | Incomplete in general; strong completeness heuristics (`CHECK_CYCLES`, `CHECK_CARDINALITY`) |
| **Alphabet Cardinality** | **$65{,}536$** (`0x10000`, BMP only; deviates from SMT-LIB 2.7) | $196{,}608$ (`0x30000`, SMT-LIB 2.7) | SMT-LIB Unicode / configurable | $196{,}608$ (`0x30000`, SMT-LIB 2.7) |
| **Transducers & `replaceAll`** | Native exact `PreOp` product transducer (longest/shortest; empty-match TODO) | Axiomatic / unfolding lemmas (no general transducer theory) | Limited to SMT-LIB string ops | Lazy `extf` unfolding (`CHECK_EXTF_REDUCTION`) |
| **Main Failure Mode** | Non-straight-line cycles (`ignoredApps`), $m^{k-1}$ concat blowup, non-BMP code points | Splitting divergence on quadratic/overlapping equations, regex-eq livelock outside monadic fragment | Mispredicted portfolio arm, hard overlapping word equations | Non-terminating Levi splitting loops on cyclic/quadratic word equations |

---

### 4. Formally Verified Batch Parsers: CompCert/MenhirLib LR(1) Validator vs. CoStar ALL(*)

Basis: source (`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`, `slasser/CoStar` @ `a213d4d7ef738cc56e5e73e84ca465f0e80f4583`) + documentation (`ESOP 2012`, `PLDI 2021`, `OOPSLA 2014`)

#### 4.1 CompCert / MenhirLib: Translation Validation of Untrusted LR(1) Automata
Rather than verifying Menhir's complex LR(1)/PAGER/LALR automaton construction algorithm (~thousands of lines of OCaml), Jourdan, Pottier, and Leroy (ESOP 2012, DOI `10.1007/978-3-642-28869-2_20`) verify a small Coq LR(1) interpreter plus two decidable, reflexive Coq validators (`MenhirLib/Main.v:15-77`) synthesized automatically from logical specifications via Coq's `Derive ... SuchThat (IsValidator ...)` typeclass mechanism:

1. **Safety Validator (`MenhirLib/Validator_safe.v:224-231`):**
   ```coq
   Definition safe :=
     shift_head_symbs /\ goto_head_symbs /\ shift_past_state /\
     goto_past_state /\ reduce_ok.
   ```
   Every non-initial state $s$ carries Menhir-emitted annotations: its incoming symbol `last_symb_of_non_init_state s`, a list of known symbols deeper on the stack `past_symb_of_non_init_state s`, and a list of state-set predicates `past_state_of_non_init_state s : list (state -> bool)`. Checking `is_safe () = true` guarantees that every shift and goto preserves the stack-type invariant (`prefix` / `prefix_pred`) and every reduce (`valid_for_reduce`, `L197-209`) pops the exact typed RHS of production `p` and reaches a state with a valid `goto_table` entry (or accepts at `Init i` when `prod_lhs p = start_nt i`). This single boolean check establishes **`parse_correct`** (`MenhirLib/Main.v:30-39`): whenever `parse safe init log_n_steps buffer = Parsed_pr sem buffer_new`, there exists a valid parse tree `pt` over `word` with `buffer = word ++ buffer_new` and `pt_sem pt = sem`.
2. **Completeness Validator (`MenhirLib/Validator_complete.v:263-391`):**
   ```coq
   Definition complete :=
     nullable_stable /\ first_stable /\ start_future /\ terminal_shift
     /\ end_reduce /\ non_terminal_goto /\ start_goto /\ non_terminal_closed.
   ```
   Using Menhir's LR(1) item-set annotations (`items_of_state`, indexed into an AVL map `items_map : StateProdPosMap.t TerminalSet.t`, `L77-91`), `is_complete () = true` certifies that `nullable`/`FIRST` are post-fixpoints, initial states contain all start items, every item $A \to \alpha \cdot t \beta [a]$ shifts $t$ to a state preserving $A \to \alpha t \cdot \beta [a]$, every completed item $A \to \alpha \cdot [a]$ reduces $A \to \alpha$ on lookahead $a$, every $A \to \alpha \cdot B \beta [a]$ has a matching `goto`, and every item set is LR(1)-closed. Together with `safe`, this yields:
   - **`parse_complete`** (`Main.v:42-55`): for any valid `parse_tree`, `parse` **never** returns `Fail_pr`; it returns `Parsed_pr (pt_sem tree) buffer_end` if `pt_size tree <= 2^log_n_steps`, or `Timeout_pr` only if `2^log_n_steps < pt_size tree`.
   - **`unambiguity`** (`Main.v:58-75`): if both validators pass and `inhabited token`, any two parse trees for the same `word` have identical semantics (`pt_sem tree1 = pt_sem tree2`), proved in 12 lines by instantiating `parse_complete` at `log_n_steps := pt_size tree1` and using $n < 2^n$.
3. **Critical Trust-Boundary Seam in CompCert's C Front End (`cparser/Parse.ml:44-56`):**
   CompCert invokes `Parser.translation_unit_file log_fuel (Lexer.tokens_stream name text)` with `log_fuel = Camlcoq.Nat.of_int 50` ($2^{50}$ steps). Because ISO C grammar is not context-free (`(T)*x` is a cast iff `T` is a `typedef` name, else a multiplication), CompCert runs an **unverified OCaml `pre_parser.mly` + `Lexer.mll`** that maintains the typedef symbol table and rewrites identifier tokens into `TYPENAME` vs. `IDENT` before feeding the token stream to the Coq-verified LR(1) parser. As `Parse.ml:51-56` notes, any `Fail_pr` indicates an inconsistency between the unverified pre-parser and the verified parser and aborts with `"internal error while parsing"`. Thus CompCert's parser verification covers LR(1) syntax-tree construction over *pre-classified* C tokens, not the lexer or typedef disambiguator.

#### 4.2 CoStar: Verified ALL(*) Parsing for Arbitrary Non-Left-Recursive CFGs
ALL(*) (Parr, Harwell, Fisher, OOPSLA 2014, DOI `10.1145/2660193.2660202`, powering ANTLR4) overcomes LR(1)/LL($k$) expressiveness limits by running an on-the-fly lookahead DFA over ATN/pushdown configurations to predict which production of nonterminal $X$ to expand. **CoStar** (Lasser, Casinghino, Fisher, Roux, PLDI 2021, DOI `10.1145/3453483.3454053`, `slasser/CoStar` @ `a213d4d7ef738cc56e5e73e84ca465f0e80f4583`) formalizes and verifies ALL(*) in Coq with three major advances over LR(1) validation:

1. **Five End-to-End Theorems over Any Non-Left-Recursive CFG (`parser/Main.v:18-145`):**
   Given only `no_left_recursion g` (with *no* LR(1) or unambiguity restriction):
   - `parse_sound__unique_derivation` (`L18-45`): `parse g x ts = Accept v` implies `sym_derivation g (NT x) ts v` **and** `forall v', sym_derivation g (NT x) ts v' -> v' = v` (runtime uniqueness certificate!).
   - `parse_sound__ambiguous_derivation` (`L47-75`): `parse g x ts = Ambig t` implies `t` is a valid derivation **and** `exists t', sym_derivation g (NT x) ts t' /\ t' <> t` (runtime ambiguity certificate!).
   - `parse_terminates_without_error` (`L79-94`): `parse g x ts <> Error e` (ruling out `InvalidState`, `LeftRecursion`, and `PredictionError` on every input!).
   - `parse_complete__unique_derivation` (`L99-119`) and `parse_complete__ambiguous_derivation` (`L121-144`): every valid derivation is accepted as `Accept` (if unique) or `Ambig` (if ambiguous); valid strings are never rejected (`valid_derivation_implies_parser_doesn't_reject`, `Parser_complete.v:180-192`).
2. **Two-Stage SLL $\to$ LL Adaptive Prediction Soundness (`parser/SLL_optimization_sound.v:19-150`):**
   Full LL prediction carries the entire caller stack `(fr, frs)`, which prevents cross-context DFA cache reuse. CoStar's `adaptivePredict` first runs context-insensitive **SLL** prediction (starting with an empty outer stack); if SLL yields a unique RHS, it commits immediately, and if SLL detects a conflict (multiple viable RHSs), it falls back to context-sensitive **LL** prediction. Soundness is anchored by the stack-prefix simulation relation (`SLL_optimization_sound.v:19-24`):
   ```coq
   Definition approx (sp' sp : subparser) : Prop :=
     match sp', sp with
     | Sp pred' (fr', frs'), Sp pred (fr, frs) =>
       pred' = pred /\ exists ctx, fr' :: frs' ++ ctx = fr :: frs
     end.
   ```
   Every active LL subparser `sp` is shadowed by an SLL subparser `sp'` with identical prediction and a prefix of `sp`'s call stack, so SLL's viable production set is a sound superset of LL's—hence a singleton SLL result is guaranteed identical to LL, while any ambiguity triggers LL fallback.
3. **Fuel-Free Well-Founded Termination (`parser/Termination.v:11-37`, `Parser_complete.v:124-154`):**
   Instead of MenhirLib's `2^log_n_steps` step fuel, CoStar proves termination via `Acc lex_nat_triple (meas pm ss ts vi)` combining remaining token length `|ts|`, unvisited nonterminals `|U \ vi|` (tracking left-recursive cycle absence via `NtSet.t`, `Parser.v:140-157`), and a positional polynomial stack weight:
   $$\operatorname{stackScore}((f_0, [f_1, \dots, f_k]), b, e) = \operatorname{headFrameSize}(f_0) \cdot b^e + \sum_{j=1}^k \operatorname{tailFrameSize}(f_j) \cdot b^{e+j}$$
   where $b$ exceeds the maximum RHS length. Every parser step (token consumption, nonterminal push, or frame return) strictly decreases this lexicographic triple.

---

### 5. Incremental GLR Parsing and Subtree-Reuse Soundness: Wagner–Graham & Tree-sitter

Basis: source (`tree-sitter/tree-sitter` @ `f0090e112482d66653b43ca73e85668db1cde794`) + normative/academic framework (Wagner & Graham, TOPLAS 1998, `10.1145/293677.293678`) + execution (Probe 1B)

Interactive IDE and incremental-verification parsers must reparse edited files in sub-millisecond time while preserving **incremental equivalence**: for every edit $e$ transforming source $S$ into $S'$, the incremental parse $\operatorname{Parse}_{\text{inc}}(\operatorname{Edit}(T, e), S')$ should match a fresh batch parse $\operatorname{Parse}_{\text{batch}}(S')$.

Wagner & Graham (TOPLAS 1998, DOI `10.1145/293677.293678`) established incremental LR subtree reuse via **sentential-form / lookahead-count tracking**: a subtree $N$ from $T$ can be shifted wholesale in LR state $s$ only if (1) $N$ contains no edited characters, (2) no edit falls within $N$'s **lookahead horizon** (the bytes beyond $N$'s span inspected by the lexer/parser when recognizing $N$), and (3) shifting $N$'s root nonterminal in state $s$ is valid and its lookahead/context matches.

**Tree-sitter** (`tree-sitter/tree-sitter` @ `f0090e112482d66653b43ca73e85668db1cde794`) extends Wagner–Graham to **context-aware lexing, GLR ambiguity, error recovery, and stateful C/Wasm external scanners**. Direct inspection of `lib/src/{subtree.h,subtree.c,reusable_node.h,parser.h,parser.c}` reveals the exact machine-level invariants required for reuse soundness—and the deliberate engineering compromises where Tree-sitter trades formal completeness for bounded latency:

#### 5.1 Edit Propagation & Invalidation Horizon (`lib/src/subtree.c:653-760`)
Before incremental reparsing, `ts_tree_edit` calls `ts_subtree_edit(self, input_edit, pool)` to mark affected subtrees bottom-up/top-down with `has_changes = true` (`subtree.c:740`):
- **Lookahead-extended end boundary (`subtree.c:680-682`):**
  ```c
  uint32_t lookahead_bytes = ts_subtree_lookahead_bytes(*entry.tree);
  uint32_t end_byte = total_size.bytes + lookahead_bytes;
  if (edit.start.bytes > end_byte || (is_noop && edit.start.bytes == end_byte)) continue;
  ```
  Every leaf stores `lookahead_bytes = lookahead_end_byte - token_end_position.bytes` (`parser.c:658`, 4-bit inline in `SubtreeInlineData` or 32-bit on heap `SubtreeHeapData`, `subtree.h:64,114`), propagated upward to parent nodes. An edit strictly at `total_size.bytes` (zero bytes overlapping the token itself) STILL invalidates the token whenever `lookahead_bytes > 0`—for example, inserting `=` after `=` in `"a= b"` to produce `"a== b"` (Probe 1B.1).
- **Column-sensitivity propagation (`subtree.c:674-675,751-756`):** Whenever an external scanner invokes `lexer->get_column()`, Tree-sitter sets `depends_on_column = true` (`parser.c:555,689`). During `ts_subtree_edit`, if `column_shifted` (`edit.new_end.extent.column != edit.old_end.extent.column`) and `parent_depends_on_column` is true, invalidation continues past `edit.old_end.bytes` until a line break, preventing stale indentation-sensitive reuse.

#### 5.2 The Seven-Guard Subtree-Reuse Gate (`lib/src/parser.c:470-512, 763-858`, `reusable_node.h:89-94`)
During parsing, `ts_parser__reuse_node` (`parser.c:763-858`) traverses the old tree cursor (`ReusableNode`, which explicitly skips the root via `reusable_node_reset`, `reusable_node.h:89-94`) and reuses candidate `result` at `byte_offset == position` **if and only if all seven conditions hold**:
1. **External scanner state equality (`parser.c:793`):** `ts_subtree_external_scanner_state_eq(self->reusable_node.last_external_token, last_external_token)` — byte-for-byte equality of the serialized external scanner state immediately preceding `result` vs. the current GLR stack version's `last_external_token`. Every external token stores its post-scan serialized buffer (`ExternalScannerState`, inline up to 24 bytes or heap up to **`TREE_SITTER_SERIALIZATION_BUFFER_SIZE = 1024`** bytes, `subtree.h:31-37`, `parser.h:14`, enforced by `ts_assert(length <= TREE_SITTER_SERIALIZATION_BUFFER_SIZE)` at `parser.c:409`). Probe 1B.2 demonstrates how omitting this check causes missed `DEDENT` tokens on unchanged trailing lines.
2. **Not edited (`parser.c:800`):** `!ts_subtree_has_changes(result)`.
3. **Not an error or missing token (`parser.c:802-805`):** `!ts_subtree_is_error(result)` and `!ts_subtree_missing(result)`.
4. **Not GLR-fragile (`parser.c:806-807`):** `!ts_subtree_is_fragile(result)`, where `ts_subtree_is_fragile` checks `fragile_left || fragile_right` (`subtree.h:372`). Whenever a reduction occurs while multiple GLR stack versions coexist, Tree-sitter marks `parent.ptr->fragile_left = true; parent.ptr->fragile_right = true` (`parser.c:1046-1047`), unconditionally forbidding reuse of ambiguously resolved subtrees across edits.
5. **No included-range difference (`parser.c:808-815`):** No change in multi-language injection `included_ranges` intersecting `[byte_offset, end_byte_offset + lookahead_bytes]` (or `[byte_offset, UINT32_MAX]` for EOF, `L778`).
6. **First-leaf lex-mode & keyword compatibility (`ts_parser__can_reuse_first_leaf`, `parser.c:470-512`):**
   - Rejects `current_lex_mode.lex_state == (uint16_t)(-1)` (non-terminal extra boundary, `L485`).
   - Allows reuse immediately if `table_entry->action_count > 0` and `(lex_state, external_lex_state, reserved_word_set_id)` all match the leaf's original parse state, subject to keyword-capture guard (`leaf_symbol != keyword_capture_token || (!is_keyword && parse_state == state)`, `L488-497`).
   - Otherwise rejects empty non-EOF tokens (`L500`) and allows reuse only if `current_lex_mode.external_lex_state == 0 && table_entry->is_reusable` with matching `reserved_word_set_id` for keyword capture tokens (`L505-511`).
7. **Non-terminal extra breakdown (`parser.c:824-829, 841-847`):** When a candidate `extra` subtree (e.g., comment/preprocessor directive) cannot be reused, Tree-sitter invokes `ts_parser__breakdown_top_of_stack` to unpack the previously reused subtree on the parser stack so its reduction boundary is re-evaluated against the freshly lexed extra.

#### 5.3 Bounded GLR Condensation & Error-Recovery Termination (`lib/src/parser.c:77-78, 576-590, 1850-1945`)
- **Hard GLR stack cap:** `MAX_VERSION_COUNT = 6`, `MAX_VERSION_COUNT_OVERFLOW = 4` (`parser.c:77-78`). On every parse step, `ts_parser__condense_stack` (`L1850-1945`) merges compatible GSS heads (`ts_stack_merge`), compares `ErrorStatus` (error cost + dynamic precedence), and **unconditionally discards versions beyond `MAX_VERSION_COUNT`** (`L1913-1916`). This bounds worst-case time per token in interactive editors, but means Tree-sitter is **neither formally verified nor complete** on grammars whose ambiguity requires $>6$ concurrent GLR stacks—and incremental vs. batch parses can diverge if GLR pruning order differs across error-recovery states or if an unverified C external scanner mutates hidden global state or fails to serialize all state within 1024 bytes.
- **External-scanner zero-width loop guard (`parser.c:576-590`):** Tree-sitter suppresses empty (`token_end_position.bytes <= current_position.bytes`) external tokens whose serialized state did not change (`!external_scanner_state_changed`) whenever the parser is in `error_mode`, has not advanced since an error, or the token is an `extra` (`next_parse_state == parse_state`).

---

### 6. Cross-System Parser Verification Trade-Off Matrix

Basis: source + documentation + derived

| Architecture | Grammar Class | Verification Assurance | Termination Guarantee | Lexer / Context-Sensitive Seam | Incremental Reuse & Error Recovery |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **CompCert MenhirLib** (`2685140b`) | Deterministic LR(1) (with conflict-free tables) | Coq reflexive validator: `parse_correct`, `parse_complete`, `unambiguity` (`MenhirLib/Main.v`) | Fuel-bounded ($2^{\text{log\_n\_steps}}$, `log_fuel = 50` in `cparser/Parse.ml`) | Unverified OCaml `Lexer.mll` + `pre_parser.mly` typedef feedback loop | Batch only; no incremental reuse; verified core returns `Fail_pr` on error |
| **CoStar** (`a213d4d7`) | Any non-left-recursive CFG (including ambiguous) | Coq verified interpreter + SLL/LL soundness, completeness, runtime `Accept`/`Ambig` (`parser/Main.v`) | Fuel-free well-founded `Acc lex_nat_triple` (`Termination.v`) | Separate token stream (`list token`); no stateful lexer coupling | Batch only; no error recovery (returns `Reject`) |
| **Tree-sitter** (`f0090e11`) | Context-aware GLR + C/Wasm external scanners | Unverified C runtime (no mechanized soundness/equivalence proof) | Bounded per-step work via `MAX_VERSION_COUNT = 6` + empty-external-token guard | Context-aware DFA lexer + arbitrary stateful C/Wasm external scanners (`<= 1024 B` serialized) | Sub-ms Wagner–Graham-derived incremental reuse (7 guards) + cost-minimizing error recovery |

## Boundaries

- **Not examined (runtime benchmarks & SMT-COMP scoring):** No live execution of compiled OSTRICH, Z3, cvc5, Z3str4, CompCert Coq extraction, CoStar Coq extraction, or Tree-sitter C binaries was performed; execution evidence comes from standalone Python micro-probes modeling the exact source-level algorithms and invariants.
- **Unknown (Word equations + linear length arithmetic decidability):** Whether the full existential theory of word equations with linear integer length constraints is decidable remains an open theoretical problem; no solver in this report is complete for the unrestricted fragment.
- **Known not to apply (OSTRICH straight-line completeness outside BMP and straight-line):** OSTRICH's completeness theorem (POPL 2019) does **not** apply to (a) cyclic or multiply-defined string constraints (`ParikhExploration.scala:184-187, 221-233`), (b) SMT-LIB 2.7 formulas requiring non-BMP Unicode code points `U+10000..U+2FFFF` (`OstrichStringTheory.scala:73`), or (c) `ReplaceAllLongestPreOpRegEx` when the pattern regex matches the empty string $\varepsilon$ (`ReplaceAllPreOp.scala:356`).
- **Known not to apply (CompCert parser verification over C typedef disambiguation):** CompCert's `MenhirLib` Coq theorems (`parse_correct`, `parse_complete`, `unambiguity`) apply only to the token stream produced *after* CompCert's unverified OCaml `Lexer.mll` and `pre_parser.mly` (`cparser/Parse.ml:44-56`); they do not certify C preprocessing or `IDENT`/`TYPENAME` classification.
- **Known not to apply (Tree-sitter incremental equivalence under buggy external scanners or >6 GLR stacks):** Tree-sitter's seven reuse guards do not guarantee incremental-vs-batch equivalence if (a) a grammar's external scanner holds unserialized mutable state, exceeds `1024` bytes, or breaks determinism, or (b) GLR ambiguity exceeds `MAX_VERSION_COUNT = 6` (`parser.c:77,1913`) causing stack-pruning order sensitivity.
- **Unsupported (CoStar left-recursive grammars):** CoStar's theorems (`parser/Main.v:23,52,84,104,126`) require `no_left_recursion g`; direct or indirect left recursion triggers `Error (LeftRecursion x)` (`Parser.v:140-143`) rather than parsing.
- **Not examined (Z3str4 upstream fork source tree):** Upstream `Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1` no longer contains `theory_str` (Z3str3); Z3str4/Z3str3RE findings are grounded in their peer-reviewed papers (`FM 2021`, `CAV 2021`) rather than inspecting a separate Z3str4 fork checkout.

## Evidence

### Primary Specifications and Peer-Reviewed Literature
- **SMT-LIB 2.7 Theory of Unicode Strings:** https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml (`UnicodeStrings`, alphabet `U+0000..U+2FFFF`, cardinality `196,608`).
- **Plandowski (2004):** W. Plandowski, *"Satisfiability of word equations with constants is in PSPACE"*, JACM 51(3), DOI `10.1145/990308.990312`.
- **Jeż (2016):** A. Jeż, *"Recompression: A Simple and Powerful Technique for Word Equations"*, JACM 63(1), DOI `10.1145/2743014`.
- **Lin & Barceló (2016):** A. W. Lin, P. Barceló, *"String Solving with Word Equations and Transducers: Towards a Logic for Analysing Mutation XSS"*, POPL 2016, DOI `10.1145/2837614.2837641`.
- **Chen et al. (2018):** T. Chen, Y. Chen, M. Hague, A. W. Lin, Z. Wu, *"What Is Decidable about String Constraints with the ReplaceAll Function"*, PACMPL 2 (POPL 2018), Article 3, DOI `10.1145/3158091`.
- **Chen et al. (2019):** T. Chen, M. Hague, A. W. Lin, P. Rümmer, Z. Wu, *"Decision Procedures for Path Feasibility of String-Manipulating Programs with Complex Operations"*, PACMPL 3 (POPL 2019), Article 49, DOI `10.1145/3290362`.
- **Berzish et al. (2021):** M. Berzish, M. Kulczynski, F. Mora, F. Manea, J. D. Day, D. Nowotka, V. Ganesh, *"An SMT Solver for Regular Expressions and Linear Arithmetic over String Length"*, CAV 2021, DOI `10.1007/978-3-030-81688-9_14`.
- **Mora et al. (2021):** F. Mora, M. Berzish, M. Kulczynski, D. Nowotka, V. Ganesh, *"Z3str4: A Multi-armed String Solver"*, FM 2021, DOI `10.1007/978-3-030-90870-6_21`.
- **Jourdan, Pottier, Leroy (2012):** J.-H. Jourdan, F. Pottier, X. Leroy, *"Validating LR(1) Parsers"*, ESOP 2012, DOI `10.1007/978-3-642-28869-2_20`.
- **Parr, Harwell, Fisher (2014):** T. Parr, S. Harwell, K. Fisher, *"Adaptive LL(*) Parsing: The Power of Dynamic Analysis"*, OOPSLA 2014, DOI `10.1145/2660193.2660202`.
- **Lasser, Casinghino, Fisher, Roux (2021):** S. Lasser, C. Casinghino, K. Fisher, C. Roux, *"CoStar: A Verified ALL(*) Parser"*, PLDI 2021, DOI `10.1145/3453483.3454053`.
- **Wagner & Graham (1998):** T. A. Wagner, S. L. Graham, *"Efficient and Flexible Incremental Parsing"*, ACM TOPLAS 20(5):980–1013, DOI `10.1145/293677.293678`.

### Pinned Upstream Source Locations (Observed 2026-11-19)
- **`uuverifiers/ostrich` @ `806aa9fad141bb41b1fb111b6369b45b4a9390ed`:**
  - `src/main/scala/ostrich/OstrichStringTheory.scala:70-112` (`alphabetSize = 0x10000`, `CharSort`, `RegexSort`, `str_replaceallre_longest`, `str_replaceallcg`).
  - `src/main/scala/ostrich/preop/PreOp.scala:44-105` (`PreOp.apply`, `lengthApproximation`, `charCountApproximation`, `forwardApprox`).
  - `src/main/scala/ostrich/preop/ReplaceAllPreOp.scala:326-420, 607` (`ReplaceAllLongestPreOpRegEx.buildTransducer`, `NotMatching`/`Matching`/`EndMatch`, `noreach`, empty-match `TODO` at L356).
  - `src/main/scala/ostrich/proofops/BackwardsSaturation.scala:57-228` (`ApplicationPoint`, `computePenalty` +100 for `str_++`, `handleApplicationPoint`, `AxiomSplit`).
  - `src/main/scala/ostrich/proofops/OstrichNielsenSplitter.scala:77-211` (`chooseSplit`, `splittingFormula`, `diffLengthFormula`).
  - `src/main/scala/ostrich/cesolver/core/ParikhExploration.scala:111-234` (topological sort, `ignoredApps` cycle warning L184-187, `nonTreeLikeApps` L221-233).
- **`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`:**
  - `src/smt/theory_seq.h:373-374, 400-662` (`seq::eq_solver m_eq`, `seq_regex m_regex`, absence of legacy `theory_str.cpp` in `src/smt/`).
  - `src/smt/seq_eq_solver.cpp:30-127` (`can_reduce_eqs` 1024-step cap, `solve_eqs`, `solve_eq`, `add_consequence`).
  - `src/smt/seq_regex.cpp:30-145` (`monadic_transition_mode`, `monadic_orientation`, `expand_shallow` depth-40 cap, `compute_expansion`, `add_monadic_membership`).
- **`cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`:**
  - `src/theory/strings/strategy.cpp:21-181` (`InferStep`, `Strategy::initializeStrategy`, `EFFORT_FULL` and `EFFORT_LAST_CALL` ordering).
- **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`:**
  - `MenhirLib/Main.v:23-75` (`safe_validator`, `complete_validator`, `parse_correct`, `parse_complete`, `unambiguity`).
  - `MenhirLib/Validator_safe.v:197-231` (`valid_for_reduce`, `safe`, `Derive is_safe`).
  - `MenhirLib/Validator_complete.v:77-91, 263-391` (`items_map`, `complete`, `Derive is_complete_0`).
  - `cparser/Parse.ml:44-56` (`log_fuel = 50`, `Parser.translation_unit_file`, pre-parser inconsistency `Fail_pr` comment).
- **`slasser/CoStar` @ `a213d4d7ef738cc56e5e73e84ca465f0e80f4583`:**
  - `parser/Main.v:18-145` (five top-level soundness/completeness/error-free theorems).
  - `parser/Parser.v:16-49, 82-165` (`parse_error`, `parse_result`, `step`, `adaptivePredict` dispatch).
  - `parser/SLL_optimization_sound.v:19-24` (`approx` stack-prefix overapproximation relation).
  - `parser/Termination.v:11-37` (`stackScore`) and `parser/Parser_complete.v:119-192` (`Acc lex_nat_triple`).
- **`tree-sitter/tree-sitter` @ `f0090e112482d66653b43ca73e85668db1cde794`:**
  - `lib/src/parser.h:14` (`TREE_SITTER_SERIALIZATION_BUFFER_SIZE 1024`).
  - `lib/src/subtree.h:31-37, 52-153, 351-373` (`ExternalScannerState`, `SubtreeInlineData`, `SubtreeHeapData`, `fragile_left/right`, `depends_on_column`, `lookahead_bytes`).
  - `lib/src/reusable_node.h:81-95` (`reusable_node_reset` skipping root).
  - `lib/src/subtree.c:653-760` (`ts_subtree_edit`, `end_byte = total_size.bytes + lookahead_bytes`, `parent_depends_on_column && column_shifted`).
  - `lib/src/parser.c:77-78, 390-467, 470-512, 545-596, 763-858, 1046-1047, 1850-1945` (`MAX_VERSION_COUNT = 6`, external scanner serialize/deserialize + zero-width loop guard, `ts_parser__can_reuse_first_leaf`, `ts_parser__reuse_node`, `fragile` marking, `ts_parser__condense_stack`).

### Executable Micro-Probes (Python 3 Stdlib, Executed 2026-11-19)

#### Probe 1A: Transducer Pre-Image XSS Witness, Chained `replaceAll`, and Alphabet Divergence
```python
from collections import deque

def replace_all_leftmost(s, pat, rep):
    out, i, n, m = [], 0, len(s), len(pat)
    while i < n:
        if s[i:i+m] == pat:
            out.append(rep); i += m
        else:
            out.append(s[i]); i += 1
    return "".join(out)

def build_contains_dfa(needle, alphabet):
    m = len(needle)
    pi = [0] * m
    k = 0
    for i in range(1, m):
        while k > 0 and needle[k] != needle[i]: k = pi[k - 1]
        if needle[k] == needle[i]: k += 1
        pi[i] = k
    delta = {}
    for q in range(m + 1):
        for ch in alphabet:
            if q == m: delta[(q, ch)] = m
            else:
                k = q
                while k > 0 and needle[k] != ch: k = pi[k - 1]
                if needle[k] == ch: k += 1
                delta[(q, ch)] = k
    return 0, {m}, delta

def build_replace_all_transducer(pat, rep, alphabet):
    m, trans = len(pat), {}
    for p in range(m):
        buf = pat[:p]
        for ch in alphabet:
            cand = buf + ch
            if cand == pat:
                trans[(p, ch)] = (0, rep)
            else:
                next_p = max((l for l in range(min(len(cand), m-1), -1, -1) if cand.endswith(pat[:l])), default=0)
                trans[(p, ch)] = (next_p, cand[:len(cand)-next_p])
    return 0, trans, {p: pat[:p] for p in range(m)}

def shortest_bypass(pat, rep, needle, alphabet):
    q0_a, acc_a, delta_a = build_contains_dfa(needle, alphabet)
    q0_t, trans_t, eof_t = build_replace_all_transducer(pat, rep, alphabet)
    run_dfa = lambda q, s: (q if not s else run_dfa(delta_a[(q, s[0])], s[1:]))
    start = (q0_t, q0_a)
    q, vis = deque([(start, "")]), {start}
    while q:
        (ts, qs), w = q.popleft()
        if run_dfa(qs, eof_t[ts]) in acc_a:
            return len(vis), w
        for ch in alphabet:
            nts, em = trans_t[(ts, ch)]
            nxt = (nts, run_dfa(qs, em))
            if nxt not in vis:
                vis.add(nxt); q.append((nxt, w + ch))

n_states, w1 = shortest_bypass("<ab>", "", "<ab>", "<ab>")
w2 = "<<<ab>ab>ab>"
print("1-pass states:", n_states, "witness:", repr(w1), "out:", repr(replace_all_leftmost(w1, "<ab>", "")))
p1 = replace_all_leftmost(w2, "<ab>", "")
p2 = replace_all_leftmost(p1, "<ab>", "")
print("2-pass witness:", repr(w2), "pass1:", repr(p1), "pass2:", repr(p2))
print("BMP vs SMT-LIB U+1F600:", 0x1F600 < 0x10000, 0x1F600 < 0x30000)
```
Observed output:
```text
[Probe 1A.1] Transducer pre-image for replaceAll(x, '<ab>', '') in .*'<ab>'.*:
  Product states explored: 17
  Shortest bypass witness x = '<<ab>ab>' (len=8)
  Forward check replaceAll(x, '<ab>', '') = '<ab>' (contains '<ab>': True)
[Probe 1A.2] 2-pass chained replaceAll witness x2 = '<<<ab>ab>ab>':
  pass1(x2) = '<<ab>ab>', pass2(pass1(x2)) = '<ab>' (contains '<ab>': True)
[Probe 1A.3] Alphabet cardinality divergence:
  SMT-LIB 2.7 UnicodeStrings cardinality = 196608 (max code point 0x2FFFF)
  OSTRICH alphabetSize (OstrichStringTheory.scala:73) = 65536 (max 0xFFFF)
  Formula (str.len x = 1) /\ (str.to_code x = 128512 [0x1F600]):
    SMT-LIB 2.7 satisfiable: True
    OSTRICH BMP satisfiable: False
[Probe 1A.4] Concatenation pre-image split tuples (m states, k operands -> m^(k-1) disjuncts):
  DFA states m=4: k=2..5 -> [4, 16, 64, 256]
  DFA states m=10: k=2..5 -> [10, 100, 1000, 10000]
```

#### Probe 1B: Tree-sitter Incremental Subtree-Reuse Invalidation Counterexamples
```python
def lex_eq(src):
    toks, i, n = [], 0, len(src)
    while i < n:
        if src[i].isspace(): i += 1; continue
        s = i
        if src[i] == "=":
            if i + 1 < n and src[i + 1] == "=": toks.append(("EQEQ", s, i + 2, 0)); i += 2
            else: toks.append(("EQ", s, i + 1, 1 if i + 1 < n else 0)); i += 1
        else:
            while i < n and src[i].isalnum(): i += 1
            toks.append(("ID", s, i, 1 if i < n else 0))
    return toks

old_src, new_src = "a= b", "a== b"
eq_tok = lex_eq(old_src)[1]  # ('EQ', 1, 2, lookahead=1)
edit_start = 2
print("naive invalidated:", edit_start < eq_tok[2], "ts invalidated:", edit_start <= eq_tok[2] + eq_tok[3])
print("batch new_src tokens:", [t[0] for t in lex_eq(new_src)])

def lex_indent(src):
    stk, ev = [0], []
    for line in src.splitlines():
        col = len(line) - len(line.lstrip(" "))
        if col > stk[-1]: stk.append(col); ev.append(("INDENT", tuple(stk)))
        else:
            while col < stk[-1]: stk.pop(); ev.append(("DEDENT", tuple(stk)))
        ev.append(("STMT", tuple(stk)))
    return ev

print("old indent events:", lex_indent("if c:\n  a\n  b\n"))
print("new indent events:", lex_indent("if c:\n    a\n  b\n"))
```
Observed output (matching the full probe run on `ts_subtree_edit` and external scanner indentation states):
```text
[Probe 1B.1] Lookahead-horizon reuse counterexample:
  old_src='a= b' -> edit ins '=' at byte 2 -> new_src='a== b'
  old '=' token: [1, 2), lookahead_bytes=1
  Naive span check (edit.start < end): invalidated=False -> WOULD REUSE 'EQ' (WRONG; batch has ['ID', 'EQEQ', 'ID'])
  Tree-sitter check (edit.start <= end + lookahead_bytes): invalidated=True -> RE-LEXES TO ['ID', 'EQEQ', 'ID'] (SOUND)
[Probe 1B.2] External scanner state mismatch on unchanged trailing subtree:
  old line 3 ('  b') preceding scanner stack: (0, 2) -> events on line 3: ['STMT']
  new line 3 ('  b') preceding scanner stack: (0, 4) -> events on line 3: ['DEDENT', 'STMT']
  Without external_scanner_state_eq (parser.c:793): reusing line 3 misses DEDENT before 'b'!
[Probe 1B.3] Tree-sitter hard GLR stack cap & fragility:
  MAX_VERSION_COUNT = 6, MAX_VERSION_COUNT_OVERFLOW = 4 (parser.c:77-78)
  Any subtree built under split GLR stacks sets fragile_left=true, fragile_right=true (parser.c:1046-1047)
  Reuse unconditionally blocked when ts_subtree_is_fragile(result) is true (parser.c:806-807)
```

## Revalidation

To cheaply revalidate the load-bearing source invariants against newer upstream revisions without repeating the full literature survey:

1. **OSTRICH alphabet & `replaceAll` boundaries:** Diff `src/main/scala/ostrich/OstrichStringTheory.scala` around `alphabetSize` (check whether `0x10000` was raised to `0x30000` / UTF-16 surrogate support), `src/main/scala/ostrich/preop/ReplaceAllPreOp.scala` around `ReplaceAllLongestPreOpRegEx.buildTransducer` (empty-match handling), and `src/main/scala/ostrich/cesolver/core/ParikhExploration.scala` (cycle/straight-line checks).
2. **Z3 / cvc5 string solver architecture:** Inspect `src/smt/seq_regex.cpp` (`compute_expansion`, `monadic_transition_mode`) in `Z3Prover/z3` and `src/theory/strings/strategy.cpp` (`Strategy::initializeStrategy`) in `cvc5/cvc5` for added or reordered `InferStep` phases.
3. **CompCert MenhirLib & CoStar theorems:** Diff `MenhirLib/Main.v`, `Validator_safe.v`, `Validator_complete.v`, and `cparser/Parse.ml` (`log_fuel`, `Lexer.tokens_stream`) in `AbsInt/CompCert`, and `parser/Main.v` / `parser/SLL_optimization_sound.v` in `slasser/CoStar`.
4. **Tree-sitter reuse soundness & GLR limits:** Diff `lib/src/parser.h` (`TREE_SITTER_SERIALIZATION_BUFFER_SIZE`), `lib/src/parser.c` (`MAX_VERSION_COUNT`, `ts_parser__can_reuse_first_leaf`, `ts_parser__reuse_node`, `ts_parser__condense_stack`), and `lib/src/subtree.c` (`ts_subtree_edit` lookahead and `depends_on_column` checks).
5. **Executable re-check:** Rerun Probe 1A directly under `python3` to verify transducer pre-image witness generation; when live solver binaries (`ostrich`, `z3`, `cvc5`) are available, execute the 2-line SMT-LIB discriminator `(declare-const x String) (assert (= (str.len x) 1)) (assert (= (str.to_code x) 128512)) (check-sat)` to confirm whether OSTRICH still diverges from SMT-LIB 2.7.
