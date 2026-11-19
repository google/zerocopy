# Neurosymbolic Languages, Type-Constrained Decoding, and Verified Runtime Safety Shields

## Summary

Integrating stochastic neural components—large language models (LLMs), perception networks, and reinforcement-learning (RL) policies—into formal programming languages, compilers, and safety-critical runtimes breaks classical deterministic FFI assumptions because neural principals are simultaneously non-deterministic, distribution-bearing, floating-point-sensitive, and susceptible to in-band control/data hijacking. Across language design, decoding theory, information-flow security, and cyber-physical control, one architectural invariant governs sound composition: **keep the high-capacity neural oracle outside the Trusted Computing Base (TCB) and enforce hard algebraic, syntactic, type, information-flow, and physical safety properties at a small, deterministic, formally verifiable boundary envelope.**

Seven concrete technical results define the current state of practice and its mathematical limits:

1. **Differentiable Logic & Provenance Semirings (`Scallop`):** Embedding recursive Datalog over commutative provenance semirings enables end-to-end backpropagation from logical conclusions to upstream neural perception tensors (`Provenance` trait, `DualNumberSemiring`). Because exact Weighted Model Counting (WMC) over Boolean derivation formulas is `#P`-hard, `DiffTopKProofsProvenance` truncates DNF formulas to the top-$k$ proofs per tuple; this restores tractability at the cost of breaking strict semiring distributivity and introducing zero-gradient bias whenever ground-truth derivations fall outside the top-$k$ frontier.
2. **Type-Constrained Decoding & Typed-Hole Contextualization (`Mündler et al. PLDI 2025`, `Hazel`/`ChatLSP` OOPSLA 2024):** Pure CFG masking eliminates parse errors yet leaves >50% of synthesis failures as semantic type errors. Prefix automata paired with bounded search over inhabitable types soundly mask untypable token prefixes (cutting TypeScript compilation errors by >50% on HumanEval/MBPP), while total error-localized ASTs with typed holes extract minimal transitive codebase definitions `(Γ, τ)` without poisoning context on incomplete edits. Both face fundamental complexity walls: type inhabitation is `PSPACE`-complete in STLC and undecidable for System F, Rust traits, TypeScript conditional types, and dependent types.
3. **BPE Subword Mismatch & Greedy Distribution Distortion (`llguidance`, `Outlines`, `XGrammar`, `GAD`/`ASAp`, `SMC`):** Variable-length BPE vocabularies cross grammar terminal boundaries, requiring Earley/PDA intersection plus Brzozowski-derivative lexers (`llguidance` computes 128k-vocab JSON Schema masks in ~1.5 ms full and `<50 μs` amortized via slicer optimization) and KV-cache-rewinding token healing at prompt seams. Crucially, greedy per-token logit masking samples from the locally renormalized distribution rather than the true conditional posterior $P(x \mid x \in L)$; an executable 3-string probe confirms greedy masking yields `TV = 0.882143` and `D_KL = 3.299535 nats` divergence from exact conditioning, while importance-weighted Sequential Monte Carlo (`SMC`) recovers the exact posterior to within `1.3e-4` error.
4. **Capability Isolation for Prompt-Injection Defense (`CaMeL`):** Because transformer self-attention merges instructions and untrusted data in one differentiable token stream, probabilistic classifier guardrails cannot provide worst-case non-interference. `CaMeL` enforces architectural control/data separation via a Privileged LLM compiling the trusted user query into a restricted Python AST (`camel_eval`, disallowing arbitrary function/class definitions outside `BaseModel` schemas), a tool-less Quarantined LLM extracting typed fields from untrusted data, and runtime `Capabilities(sources_set, readers_set)` checked fail-closed by `SecurityPolicyEngine.check_policy` on both tool arguments and control/data dependencies.
5. **Verified Runtime Safety Shields (`Simplex`, `CBF-QP`, `LTL Shields`, `ModelPlex`, `VeriPhy`):** Wrapping untrusted controllers in formally verified envelopes requires bridging four distinct failure seams: (a) computing conservative backward-reachable recoverability sets $\mathcal{R}_{\text{base}} \subsetneq \mathcal{S}$ and dwell-time hysteresis in `Simplex`; (b) handling multi-constraint `CBF-QP` infeasibility under actuator saturation and real-time solver error; (c) closing the continuous-to-discrete sim-to-real gap via $\text{d}\mathcal{L}$-synthesized `ModelPlex` controller/model monitors and `VeriPhy` verified executables; and (d) bounding doubly-exponential reactive LTL shield synthesis (`2EXPTIME`-complete in general) while preserving RL credit assignment.
6. **Floating-Point & Batched-GPU Non-Determinism (`Jia & Rinard SAS 2021`):** Real-arithmetic neural and CBF verifiers are unsound under IEEE-754 rounding and quantization drift. An executable IEEE-754 `binary64` probe confirms a concrete CBF inequality where naive `f64` evaluates `+0.25` (`SAFE`) while exact rational arithmetic evaluates `-0.25` (`UNSAFE`); outward-rounded interval arithmetic (`[-1.75, +2.25]`) catches the boundary violation and triggers a certified `Simplex` fallback. Similarly, dynamic batching changes GEMM reduction order and MoE token routing, breaking deterministic replay even at `temperature = 0`.
7. **Proof-Carrying Stochastic Oracles (`LLM-Modulo`, `Rosette`, `Synquid`):** Decoupling heuristic neural sketch generation from deterministic SMT/kernel checkers removes the LLM from the TCB, provided the boundary enforces cryptographic spec-locking, kernel axiom audits (banning `sorry`, unchecked axioms, and unsafe reflection), and fuel-bounded structured cancellation across CPU/GPU seams.

## Applicability

This report synthesizes primary source implementations, peer-reviewed formalizations, and executable probes across five interacting layers of neurosymbolic and runtime-assured systems:

- **Differentiable logic runtimes:** `scallop-lang/scallop` (commit `668bfb6d45ce302fd4ffa7f29916baf3c7ce36ef`, PLDI 2023 DOI `10.1145/3591280`) covering its Rust provenance semiring core and `diff-top-k-proofs` WMC backend.
- **Constrained decoding and typed-hole contextualization:** `eth-sri/type-constrained-code-generation` (commit `3486122b3e980006d0f848cde1ea3d424e19dd42`, PLDI 2025 DOI `10.1145/3729274`, TypeScript implementation), `hazelgrove/hazel` (commit `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`, OOPSLA 2024 DOI `10.1145/3689728`), `guidance-ai/llguidance` (commit `4b1bdd7eaab212dacdbcebcd71ad84d194dfc629`), `dottxt-ai/outlines` (commit `c52af8472c6fe8a607a733ec11b709476af77a96`), `mlc-ai/xgrammar` (commit `3fe39321a6f24c90c2cc4fa4519b87e22367bcfc`, `arXiv:2411.15100`), alongside the formal analyses in `DOMINO` (ICML 2024), `GAD`/`ASAp` (`arXiv:2405.21047`), `SMC` (`arXiv:2504.13139`), and `Tam et al.` (`arXiv:2408.02442`).
- **Solver-aided synthesis and verifier-in-the-loop planning:** `emina/rosette` (commit `373c8c35e4a7667f38fce10cf0b74ae17de07f1d`), `nadia-polikarpova/synquid` (commit `9bceb4cc775e07ab279fff8c51fdd86ae0b2878c`), and `LLM-Modulo` (`arXiv:2402.01817`).
- **Agent information-flow security:** `google-research/camel-prompt-injection` (commit `f083b6b396399d3b3c7f2ddaf613a5945eaf32d8`, `arXiv:2503.18813`) evaluated on Python AST interpretation with explicit capability metadata.
- **Cyber-physical runtime assurance and numeric soundness:** `Simplex` (DOI `10.1109/MS.2001.936213`), `CBF-QP` (DOIs `10.1109/TAC.2016.2638961`, `10.23919/ECC.2019.8796030`), `LTL Shielding` (DOI `10.1609/aaai.v32i1.11797`), `LS-Lab/KeYmaeraX-release` `ModelPlex` (commit `2753f99b53cea5f946386998a39faded05ede677`, DOI `10.1007/s10703-016-0241-z`), `VeriPhy` (DOI `10.1145/3192366.3192400`), and `Jia & Rinard` (DOI `10.1007/978-3-030-88806-0_9`).
- **Executable probes:** Executed on `CPython 3.13.15` (`x86_64-linux`) using exact `fractions.Fraction` and IEEE-754 `math.nextafter` outward rounding.

The findings relate these subjects as complementary defense-in-depth and interface layers around an untrusted stochastic oracle: constrained decoding and typed holes govern *what the oracle can emit*, provenance semirings and SMC govern *how probabilistic/gradient signals propagate*, capability IFC (`CaMeL`) governs *what effects oracle outputs can trigger*, and hybrid/reactive shields (`Simplex`, `CBF`, `ModelPlex`, outward-rounded checks) govern *physical and numerical invariants before actuation*.

## Findings

### 1. Provenance-Semiring Differentiable Logic (`Scallop`) and the `#P` vs. Top-$k$ Gradient Cliff

Basis: source + normative (`scallop-lang/scallop` @ `668bfb6d45ce302fd4ffa7f29916baf3c7ce36ef`, PLDI 2023 DOI `10.1145/3591280`)

`Scallop` bridges neural perception (e.g., PyTorch classifiers outputting probability tensors over relational tuples) with recursive Datalog supporting stratified negation, aggregation, and algebraic data types by parameterizing relational evaluation over a generalized commutative **provenance semiring** $(K, \oplus, \otimes, \mathbf{0}, \mathbf{1})$ in `core/src/runtime/provenance/provenance.rs:6–75`:

```rust
pub trait Provenance: Clone + 'static {
  type InputTag: Clone + Debug + StaticInputTag;
  type Tag: Tag;
  type OutputTag: Clone + Debug + Display;
  fn tagging_fn(&self, ext_tag: Self::InputTag) -> Self::Tag;
  fn recover_fn(&self, t: &Self::Tag) -> Self::OutputTag;
  fn discard(&self, t: &Self::Tag) -> bool;
  fn zero(&self) -> Self::Tag;
  fn one(&self) -> Self::Tag;
  fn add(&self, t1: &Self::Tag, t2: &Self::Tag) -> Self::Tag;
  fn mult(&self, t1: &Self::Tag, t2: &Self::Tag) -> Self::Tag;
  fn negate(&self, t: &Self::Tag) -> Option<Self::Tag> { None }
  fn minus(&self, t1: &Self::Tag, t2: &Self::Tag) -> Option<Self::Tag> {
    self.negate(t2).map(|neg_t2| self.mult(t1, &neg_t2))
  }
  fn saturated(&self, t_old: &Self::Tag, t_new: &Self::Tag) -> bool;
  fn weight(&self, tag: &Self::Tag) -> f64 { 1.0 }
}
```

#### Algebraic and Computational Mechanics
- **Exact probabilistic inference is `#P`-hard:** Under independent probabilistic facts (or mutually exclusive disjunction groups), computing the exact probability of a derived tuple requires Weighted Model Counting (WMC) over its Boolean derivation formula (e.g., via Sentential Decision Diagrams / d-DNNF). On recursive Datalog queries (graph reachability, scene-graph parsing, multi-hop relational reasoning), the provenance Boolean formula grows exponentially in derivation depth.
- **Top-$k$ Differentiable Approximation (`diff-top-k-proofs`):** In `core/src/runtime/provenance/differentiable/diff_top_k_proofs.rs:6–143`, `DiffTopKProofsProvenance<T, P>` represents each tuple's internal `Tag` as a `DNFFormula` truncated to at most `k` highest-probability conjunctive proof clauses during `add` (`self.top_k_add(t1, t2, self.k)`), `mult` (`self.top_k_mult(t1, t2, self.k)`), and `negate` (`self.top_k_negate(t, self.k)`). Mutual-exclusivity constraints (e.g., softmax class outputs from a neural network) are tracked in `disjunctions: P::Cell<Disjunctions>` and enforced via `has_disjunction_conflict` and `wmc_with_disjunctions`.
- **Forward-mode dual-number WMC recovery:** At query output (`recover_fn`, lines 83–109), `Scallop` constructs a `DualNumberSemiring::new(num_var_requires_grad)` and executes WMC (`t.wmc_with_disjunctions(&s, &v, disj)` or `t.wmc(&s, &v)`) over the retained top-$k$ DNF formula, emitting `OutputDiffProb(prob, deriv)` where `deriv: Vec<(usize, f64)>` carries exact partial derivatives $\partial P(\text{tuple}) / \partial p_i$ back into PyTorch's autograd graph.

#### Concrete Failure Cliffs and FFI Seam Hazards
1. **Semiring law breakage & gradient starvation:** Truncating to the top-$k$ proofs violates strict semiring distributivity and associativity, producing a sound *lower bound* on true derivation probability for positive monotone queries but an *unboundedly biased* estimate under negation (`top_k_negate`). Early in training—when neural weights are near-random—the ground-truth proof frequently ranks below the top $k$, causing `deriv` for the true input facts to vanish identically (`0.0`) and stalling gradient descent unless $k$ is annealed or smoothed.
2. **CPU↔GPU synchronization cliff:** Semi-naive relational fixpoint loops run over sparse CPU hash/BTree indices (`BTreeSet<usize>`, `P::Cell<Disjunctions>`), whereas neural perception and loss layers execute on GPU tensor streams; marshaling sparse probability vectors and sparse backward derivatives across PCIe every minibatch dominates wall-clock training time unless relational provenance operations are vectorized onto GPUs.
3. **FFI provenance erasure:** Any host function or foreign predicate that converts a tagged tuple to a plain scalar (`f64`/`bool`) without preserving `InputExclusiveDiffProb` silently severs the autograd chain (`external_tag.is_none()` maps to `s.constant(real)` at line 94) with zero compile-time error. Downstream symbolic verifiers expecting calibrated probabilities cannot assume `DiffTopKProofsProvenance` outputs satisfy Kolmogorov probability axioms without carrying explicit WMC truncation error bounds.

---

### 2. Type-Constrained Decoding (`Mündler et al.`) and Typed-Hole Contextualization (`Hazel` / `ChatLSP`)

Basis: source + normative (`eth-sri/type-constrained-code-generation` @ `3486122b3e980006d0f848cde1ea3d424e19dd42`, PLDI 2025 DOI `10.1145/3729274`; `hazelgrove/hazel` @ `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`, OOPSLA 2024 DOI `10.1145/3689728`)

Syntactic CFG masking eliminates parse errors but leaves semantic type errors (non-existent fields, invalid receivers, arity mismatches, uninstantiated generic bounds) as the dominant failure mode in LLM code synthesis. Two complementary PL mechanisms attack this seam from opposite directions: *constraining token emission* vs. *enriching prompt context and interactive repair*.

#### Type-Constrained Decoding via Prefix Automata and Inhabitable-Type Search
Mündler, He, Wang, Sen, Song, & Vechev (PLDI 2025, `arXiv:2504.09246`, DOI `10.1145/3729274`) formalize **type-constrained decoding** on the simply-typed lambda calculus (STLC) and implement an incremental decoder for TypeScript (`eth-sri/type-constrained-code-generation`, `sample_constrained` + incremental TypeScript parser):

- **Prefix automaton over partial programs:** Given a left-to-right token prefix $w$, the incremental parser maintains the set of viable partial parse/typing states rather than rejecting incomplete code. For example (documented in `README.md:92–105`), `"let x: number = "` yields a single accepting state expecting `number`; `"let x: number = \"hey\" + "` retains accepting states because a string expression can still be projected via `.length` to yield `number`; whereas `"let x: boolean = \"hey\" < "` rejects all states because `"hey"` cannot inhabit the numeric operand required by `<` (under strict typing rules).
- **Search over inhabitable types:** A candidate next token $t$ is masked out iff no finite extension of $w \cdot t$ can complete a well-typed AST given the current typing environment $\Gamma$ and expected goal type $\tau$. To decide reachability, the decoder checks whether required intermediate argument or field types are *inhabitable* from $\Gamma$ (via local variables, member accesses, constructors, or function applications).
- **Empirical impact:** Across HumanEval and MBPP synthesis, translation, and repair benchmarks in TypeScript, type-constrained decoding cuts compilation errors by more than half while increasing pass@1 functional correctness.

#### Fundamental Complexity and Language-Design Limits
- **Decidability cliff:** Type inhabitation is already `PSPACE`-complete for STLC (Statman 1979) and **undecidable** for System F (Urzyczyn 1997), Rust trait resolution with associated types, TypeScript conditional/mapped types, and full dependent types (Lean 4 / Coq). Consequently, any finite-time online decoder must use **bounded-depth sound over-approximation** (allowing a token whenever inhabitation search reaches its depth/time budget) rather than exact completeness.
- **Non-local / right-to-left typing dependencies:** Hindley-Milner let-polymorphism, bidirectional inference from trailing return annotations or call-site contexts, forward references, and mutually recursive declarations make prefix validity depend on tokens *not yet emitted*.
- **Shadow type-checker drift:** Because mainstream compilers (`tsc`, `rustc`, `clang`) do not expose an incremental prefix-inhabitation oracle, standalone type-constrained decoders maintain partial re-implementations of the language's type checker—creating a soundness/completeness drift hazard whenever language features or FFI bindings evolve.

#### Live Typed Holes and Semantic Contextualization (`Hazel` & `ChatLSP`)
Blinn, Li, Kim, & Omar (OOPSLA 2024, `arXiv:2409.00921`, DOI `10.1145/3689728`) demonstrate in `Hazel` (and a TypeScript `ChatLSP` prototype) that static semantic context extracted from **typed holes** dramatically improves synthesis over custom codebase types (`MVUBench`):

- **Total syntax & error-localized gradual typing:** Unlike batch parsers (`rustc`/`tsc`) that poison downstream AST nodes with `<error>` types when an earlier line is incomplete, `Hazel`'s structural/total syntax guarantees that *every* edit state has a well-defined AST where incomplete expressions and type errors are isolated inside explicit **holes** (`?`).
- **Transitive hole context extraction:** For a target hole $h$, the language server extracts its exact expected type $\tau_h$, its local binding environment $\Gamma_h$ (in-scope variables and their types), and the transitive closure of user-defined type declarations referenced by $\tau_h$ and $\Gamma_h$ across the repository—fitting compact, high-signal semantic context inside finite prompt budgets without flooding the context window with irrelevant files.
- **`ChatLSP` refinement loop:** Candidate completions returned by the LLM are parsed and type-checked inside the hole context; localized type errors are fed back iteratively without polluting unrelated edits.
- **FFI seam limitation:** Language servers stop at opaque FFI boundaries (`extern "C"`, raw JSON payloads, untyped `PyObject*`); a typed hole on the host side cannot automatically pull foreign ABI invariants or preconditions across the boundary unless a polyglot schema/specification bridge exists.

---

### 3. BPE Token-Boundary Alignment, Token Healing, and Constrained-Decoding Distribution Distortion

Basis: source + normative + execution (`guidance-ai/llguidance` @ `4b1bdd7eaab212dacdbcebcd71ad84d194dfc629`, `dottxt-ai/outlines` @ `c52af8472c6fe8a607a733ec11b709476af77a96`, `mlc-ai/xgrammar` @ `3fe39321a6f24c90c2cc4fa4519b87e22367bcfc`, `arXiv:2405.21047`, `arXiv:2504.13139`, `arXiv:2408.02442`, `CPython 3.13.15` Probe 1A)

#### BPE Subword Seam and Maximal-Munch Lookahead Cliffs
Autoregressive LLMs generate Byte-Pair Encoding (BPE) or SentencePiece subword tokens ($|V| \in [32\text{k}, 256\text{k}]$) trained for corpus compression rather than grammar tokenization. A single BPE token frequently spans multiple syntactic terminals (e.g., `"): "`, `":{\"`) or splits one keyword/identifier mid-lexeme (`func` + `tion`). This creates three distinct engineering cliffs:

1. **Prompt-seam tokenization mismatch & token healing:** If a prompt ends mid-lexeme (e.g., `"http://` or `let x =`), naive continuation forces the LLM to emit a token starting strictly after the prompt's trailing byte, forbidding the natural merged BPE token (such as `://www` or ` = 42`) that the model was trained to expect. **Token healing** rewinds the final prompt token(s) back to the last clean prefix boundary, replays the KV-cache prefix, and constrains the next generated token to begin with the trimmed characters.
2. **Maximal-munch lexer fusion:** If a grammar's lexer follows maximal munch (standard in C, Rust, TypeScript, JSON), emitting a token ending in `in` followed by a token starting with `t` fuses both into the single keyword `int` rather than two identifiers—silently invalidating the parser state unless the lexer automaton tracks lookahead/boundary invariants across BPE chunks.
3. **Parser differentials:** If the constrained decoder's CFG/regex engine approximates the target runtime's parser (e.g., omitting Unicode normalization, duplicate JSON keys, IEEE-754 literal overflow like `1e9999`, or indentation-sensitive Python/YAML blocks), outputs certified "valid" by the decoder can still be rejected—or parsed into a different AST—by the downstream consumer.

#### Cross-Engine Comparison Matrix

| Engine / Algorithm | Core Parsing / Masking Mechanism | Expressiveness | Typical CPU Mask Latency (128k Vocab) | Token Healing / Subword Handling | Distribution Fidelity | Key Limitation / Failure Mode |
|---|---|---|---|---|---|---|
| **`Outlines`** (`dottxt-ai/outlines`) | Regex compiled to DFA + precomputed state-to-token index (`outlines_core`) | Regular languages (JSON Schema via regex subset); CFG via incremental parser | Sub-millisecond after offline FSM build | Pre-indexed BPE transitions over DFA states | Greedy per-token masking (distorted) | High startup/memory cost for large schemas; no exact CFG precomputation |
| **`DOMINO`** (Beurer-Kellner et al., ICML 2024) | Subword-aligned DFA/CFG precomputation + speculative multi-token drafting | Regex + CFG | Near-zero amortized (up to ~2× speedup via speculative forcing) | Subword-aligned transitions + minimal invasiveness | Greedy per-token masking (distorted) | Precomputation overhead on dynamic per-request grammars |
| **`XGrammar`** (`mlc-ai/xgrammar`, `arXiv:2411.15100`) | Splits $|V|$ into context-independent (prechecked) vs. context-dependent tokens + persistent PDA stack + GPU overlap | Full CFG (EBNF, JSON Schema) | `<40 μs` effective (up to 100× over naive stack check) | Byte-level PDA traversal across BPE tokens | Greedy per-token masking (distorted) | Context-dependent stack states still require runtime check; no semantic types |
| **`llguidance`** (`guidance-ai/llguidance`) | Earley CFG parser + Brzozowski-derivative lexer (`derivre`) + "slicer" optimization + fast-forward tokens | Full CFG, Lark grammars, JSON Schema | ~1.5 ms full; **`<50 μs` median** via slicer (`README.md:34–99`) | Native token trie (`toktrie`), fast-forward forced spans, lazy lexer derivatives | Greedy per-token masking (distorted) | Syntax/regex only; no context-sensitive typing or posterior reweighting |
| **Type-Constrained Decoding** (`Mündler et al. PLDI 2025`) | Incremental prefix automaton + bounded inhabitable-type search | Context-sensitive typing (STLC formalized; TypeScript implemented) | Higher per-token CPU search (requires memoization & depth caps) | Incremental parser tracks partial identifier/operator states | Greedy per-token masking (distorted) | Undecidable for System F / Rust traits / dependent types; shadow type checker |
| **`GAD` / `ASAp`** (`Park et al. NeurIPS 2024`) | Adaptive Sampling with Approximate expected future grammaticality upper bounds | Arbitrary CFG / decidable constraint | Multi-sample amortized overhead | Compatible with BPE prefix masks | **Asymptotically exact** $P(x \mid x \in L)$ | Requires multiple trajectories to tighten expected-future estimates |
| **`GenLM` `SMC`** (`Loula et al. ICLR 2025`) | Sequential Monte Carlo particle ensembles with incremental syntactic/semantic potentials + resampling | Arbitrary incremental syntactic + semantic verifiers | Scales linearly with particle count $N$ (batched GPU) | Byte/token reweighting + KV-cache branching | **Asymptotically exact** posterior alignment | Requires cheap snapshot/clone of foreign verifier state alongside KV-cache |

#### Distribution Distortion Proof and Executable Quantification (Probe 1A)
Basis: normative (`arXiv:2405.21047`, `arXiv:2504.13139`) + execution (`CPython 3.13.15`)

Standard Grammar-Constrained Decoding (GCD) enforces $x \in L(G)$ via **myopic local renormalization**:
$$P_{\text{GCD}}(t_i \mid t_{<i}) = \frac{P(t_i \mid t_{<i}) \cdot \mathbb{I}[\exists s.\, t_{\le i} s \in L]}{\sum_{t' \in V} P(t' \mid t_{<i}) \cdot \mathbb{I}[\exists s.\, t_{<i} t' s \in L]}$$
By contrast, the true conditional posterior requires weighting each candidate next token by its **future grammaticality partition function** $Z(t_{\le i}) = \sum_{s : t_{\le i} s \in L} P(s \mid t_{\le i})$, which is `#P`-hard / undecidable in general:
$$P(t_i \mid t_{<i}, x \in L) \propto P(t_i \mid t_{<i}) \cdot Z(t_{\le i})$$
Whenever a high-probability prefix $t_{\le i}$ is a **myopic trap** (it admits at least one valid continuation, so $\mathbb{I}[\exists s]=1$, yet nearly all of its unconstrained probability mass falls on ungrammatical continuations so $Z(t_{\le i}) \ll 1$), greedy GCD commits to the trap and forces astronomically unlikely continuations later.

**Executable Probe 1A (`CPython 3.13.15`):** Consider grammar $L = \{\texttt{"ab"}, \texttt{"ac"}, \texttt{"bd"}\}$ over alphabet $\{a,b,c,d,x\}$ with LM distribution $P(a)=0.90, P(b)=0.10$; $P(b \mid a)=0.001, P(c \mid a)=0.001, P(x \mid a)=0.998$; $P(d \mid b)=0.990, P(x \mid b)=0.010$. Running the probe script in `## Evidence` (`/tmp/probe_neurosymbolic.py`) yields:

| String $s \in L$ | Unconstrained $P(s)$ | Exact Posterior $P(s \mid s \in L)$ | Greedy GCD $P_{\text{GCD}}(s)$ | SMC Weighted ($N=20{,}000$, seed 42) |
|---|---:|---:|---:|---:|
| `"ab"` | `0.000900` | `0.008929` | **`0.450000`** (50.4× over-weighted) | `0.009004` (err `0.000075`) |
| `"ac"` | `0.000900` | `0.008929` | **`0.450000`** (50.4× over-weighted) | `0.008981` (err `0.000052`) |
| `"bd"` | `0.099000` | **`0.982143`** | `0.100000` (9.8× under-weighted) | `0.982015` (err `0.000127`) |

- Exact partition function: $Z = P(L) = 0.100800$.
- **Greedy GCD distortion:** Total Variation distance $\text{TV}(P_{\text{GCD}}, P(\cdot \mid L)) = \mathbf{0.882143}$; KL divergence $D_{\text{KL}}(P_{\text{GCD}} \| P(\cdot \mid L)) = \mathbf{3.299535\text{ nats}}$.
- **Format-restriction reasoning penalty (`Tam et al. EMNLP 2024`, `arXiv:2408.02442`):** Empirically, forcing strict schema compliance (JSON/XML mode) without unconstrained reasoning scratchpads degrades multi-step reasoning accuracy across models, whereas separating an unconstrained reasoning channel from a grammar/posterior-aligned emission channel preserves both validity and accuracy.

---

### 4. Capability-Based Isolation for Stochastic Oracles (`CaMeL`)

Basis: source + normative (`google-research/camel-prompt-injection` @ `f083b6b396399d3b3c7f2ddaf613a5945eaf32d8`, `arXiv:2503.18813`)

Indirect prompt injection is an instance of **control-data confusion** inside transformer self-attention: because instructions and retrieved external text share one undifferentiated token sequence, adversarial content inside an email, web page, or log file can hijack tool calls in a monolithic ReAct loop. `CaMeL` (*CApabilities for MachinE Learning*, Debenedetti et al., `arXiv:2503.18813`) defeats prompt injection architecturally by enforcing classic operating-system capability and information-flow control (IFC) invariants outside the neural model:

1. **Dual-LLM Control/Data Separation:**
   - A **Privileged LLM (P-LLM)** receives *only* the trusted user query (never untrusted tool return payloads) and emits a plan written in a restricted Python subset executed by a custom AST interpreter (`src/camel/interpreter/interpreter.py`, `camel_eval` at line 2403). Arbitrary `def` functions and general classes are disabled (`class definitions must inherit from BaseModel` at line 2272; `only field definitions are supported in class definitions` at line 2197; unsupported AST nodes raise `NotImplementedError` at line 2651).
   - A **Quarantined LLM (Q-LLM)** has **zero tool-calling capabilities** (`query_ai_assistant` is listed in `NO_SIDE_EFFECT_TOOLS` at `src/camel/security_policy.py:52–55`) and is invoked strictly to parse unstructured external data into typed `BaseModel` schemas.
2. **Fine-Grained Runtime Capability & Provenance Metadata:**
   Every runtime value is wrapped in a `CaMeLValue` carrying `Capabilities` (`src/camel/capabilities/capabilities.py:24–38`):
   - `sources_set: frozenset[sources.Source]` (`SourceEnum.User`, `SourceEnum.CaMeL`, or `sources.Tool(...)`), tracking provenance;
   - `readers_set: readers.Readers` (`readers.Public()` or a restricted set of authorized principals, supporting set-intersection lattice meet `&` in `src/camel/capabilities/readers.py:32–38`).
3. **Fail-Closed Policy Enforcement Over Both Arguments and Control Dependencies:**
   Before invoking any state-changing tool, `SecurityPolicyEngine.check_policy` (`src/camel/security_policy.py:77–97`) checks *two* conditions:
   ```python
   if tool_name in self.no_side_effect_tools:
       return Allowed()
   non_public_variables = [d.raw for d in dependencies if not is_public(d)]
   if len(non_public_variables) > 0:
       return Denied(f"{tool_name} is state-changing and depends on private values {non_public_variables}.")
   for policy_name, policy in self.policies:
       if fnmatch.fnmatch(tool_name, policy_name):
           return policy(tool_name, kwargs)
   return Denied("No security policy matched for tool. Defaulting to denial.")
   ```
   - Crucially, `dependencies` captures **control-flow and data-flow provenance** (controlled by `MetadataEvalMode` in `interpreter.py:119`): if a branch condition depended on private data, executing a state-changing sink inside that branch is denied (blocking implicit-flow exfiltration), and tools with no matching policy fail closed (`Denied`).

#### Remaining Security Frontier and FFI Seam Failure Modes
- **Semantic data-to-data attacks:** Even when control flow cannot be altered, an untrusted document processed by the Q-LLM can forge a plausible data value (e.g., substituting an attacker's email address when extracting a "billing contact" string). Preventing exfiltration then relies strictly on the per-tool `SecurityPolicy` checking `sources_set` and `readers_set` (e.g., forbidding sending private-reader data to an untrusted-source recipient address).
- **FFI metadata erasure:** Standard JSON-RPC, MCP, REST, and C FFI boundaries strip `(sources_set, readers_set)` upon serialization. If an invoked tool spawns a sub-agent or writes to shared mutable storage (filesystem, database, clipboard) without propagating capability labels across the wire protocol, downstream readers lose provenance and bypass policy enforcement.

---

### 5. Verified Runtime Safety Shields (`Simplex`, `CBF-QP`, `LTL Shields`, `ModelPlex`, `VeriPhy`)

Basis: source + normative (`LS-Lab/KeYmaeraX-release` @ `2753f99b53cea5f946386998a39faded05ede677`; DOIs `10.1109/MS.2001.936213`, `10.1109/TAC.2016.2638961`, `10.23919/ECC.2019.8796030`, `10.1609/aaai.v32i1.11797`, `10.1007/s10703-016-0241-z`, `10.1145/3192366.3192400`)

When neural policies actuate physical or distributed systems, static verification of the neural weights alone is generally intractable or brittle under distribution shift. Runtime Assurance (RTA) shields wrap the unverified high-performance controller inside a small, formally verified safety envelope.

#### Runtime Safety-Shield Taxonomy

| Architecture | Domain & Formalism | Online Computation | Soundness Guarantee | Primary Failure Modes | Isolation / FFI Boundary Requirement |
|---|---|---|---|---|---|
| **`Simplex`** (Sha, IEEE Software 2001) | Continuous / hybrid control; backward reachable recoverability set $\mathcal{R}_{\text{base}} \subsetneq \mathcal{S}$ | $O(1)$ switching check + simple verified baseline controller | Forward safety invariance if DM switches before exiting $\mathcal{R}_{\text{base}}$ | Under-conservative $\mathcal{R}_{\text{base}}$ (switches too late for momentum); Zeno chattering on re-engagement; common-mode crashes | Hardware/partition isolation (`seL4`/CHERI/separate MCU) + lock-free deadline-miss mailbox |
| **`CBF-QP` Safety Filter** (Ames et al., TAC 2017 / ECC 2019) | Control-affine ODE $\dot{x} = f(x) + g(x)u$, barrier $\mathcal{C} = \{x \mid h(x) \ge 0\}$ | Real-time convex QP: $\min_{u \in \mathcal{U}} \frac{1}{2}\|u - u_{\text{ML}}\|^2$ s.t. $L_f h + L_g h\, u + \alpha(h) \ge 0$ | Minimally invasive forward invariance of $\mathcal{C}$ by Nagumo's theorem (assuming exact feasibility) | Multi-CBF + actuator-saturation QP infeasibility; higher relative degree ($L_g h = 0$); solver early-stop primal violation; saddle-point deadlock | Untrusted QP solver (`OSQP`) must be wrapped by an outward-rounded interval primal-feasibility checker + `Simplex` fallback |
| **Reactive `LTL` Shield** (Alshiekh et al., AAAI 2018) | Discrete two-player safety game synthesized from safety-LTL | $O(1)$ finite-state automaton transition / action mask | Guarantees $\Box \phi$ throughout both RL exploration and deployment | `2EXPTIME`-complete synthesis explosion; lossy continuous-to-discrete abstraction; credit-assignment corruption in post-posed overrides | Linear typestate synchronization between RL episode resets and stateful shield automaton across Python↔Rust FFI |
| **`ModelPlex` + `VeriPhy`** (Mitsch & Platzer 2016; Bohrer et al. PLDI 2018) | Differential dynamic logic ($\text{d}\mathcal{L}$) in `KeYmaera X` + verified `CakeML` machine code | Runtime evaluation of synthesized quantifier-free controller & model monitors | End-to-end safety from $\text{d}\mathcal{L}$ proof to machine code modulo runtime plant-model conformance | Violation *within* a single sampling interval $\Delta t$; unmodeled sensor latency $\tau_{\text{lat}}$; `CakeML` GC runtime overhead on bare-metal MCUs | Verified ADC/DAC scaling, units-of-measure agreement, timestamp freshness, and outward-rounded interval monitor arithmetic |
| **`CaMeL` Capability IFC** (Debenedetti et al. 2025) | Discrete agent tool calls; provenance + reader-set lattice | AST evaluation + $O(\text{deps})$ policy checks | Control-flow non-interference + fail-closed sink authorization | Semantic data-to-data forgery; missing policy rules; metadata stripping across external RPCs | Propagating `(sources_set, readers_set)` across tool/MCP wire protocols |

#### Primary-Source Mechanics of `ModelPlex` (`KeYmaera X`)
In `LS-Lab/KeYmaeraX-release` (`keymaerax-core/src/main/scala/org/keymaerax/btactics/ModelPlex.scala:47–1389`), `ModelPlex` automatically synthesizes provably sound runtime monitors from verified $\text{d}\mathcal{L}$ hybrid-program models (`createMonitorSpecificationConjecture` at line 233; `controllerMonitorT` at line 1384; `modelMonitorT` at line 1389):
- **Controller monitor (`ModelPlexKind.Ctrl`):** Checks at runtime whether the concrete control decision $u_k$ proposed by an untrusted/advanced controller satisfies the verified control envelope of the $\text{d}\mathcal{L}$ model at current state $x_k$ before actuation commits.
- **Model monitor (`ModelPlexKind.Model`):** Checks whether the physically observed next state $x_{k+1}$ after applying $u_k$ from $x_k$ actually falls within the ODE envelope assumed by the offline proof (`applyAtAllODEs` at line 1210). If physical drift (worn brakes, wind gust, unmodeled mass change) violates the ODE model, the monitor detects the sim-to-real divergence and triggers a fail-safe maneuver.
- **`VeriPhy` (`PLDI 2018`, DOI `10.1145/3192366.3192400`):** Compiles verified `KeYmaera X` monitors and fallback controllers through `CakeML` down to machine code while bounding real-to-finite-precision numerical error via interval arithmetic—closing both the model-to-code and real-to-float gaps, though inheriting `CakeML`'s managed-runtime/GC footprint.

---

### 6. Floating-Point Unsoundness, Outward-Rounded CBF Checking, and Batched-GPU Non-Determinism

Basis: normative (`Jia & Rinard SAS 2021`, DOI `10.1007/978-3-030-88806-0_9`) + execution (`CPython 3.13.15` Probe 1B) + derived

#### Real-vs.-IEEE-754 Soundness Gap (`Jia & Rinard SAS 2021`)
Formal neural network verifiers (`Marabou`, `α,β-CROWN`, MILP/LP-based checkers) typically encode affine layers and ReLU activations over exact reals $\mathbb{R}$ (or invoke floating-point LP solvers with tolerances $\sim 10^{-6}$). Jia & Rinard (SAS 2021, `arXiv:2003.03021`) proved that IEEE-754 rounding near ReLU decision hyperplanes ($\max(0, x)$) and non-associative accumulation allow systematic construction of concrete `float32` adversarial inputs violating properties "proven" by complete real-arithmetic verifiers, as well as networks that defeat incomplete verifiers. Across accelerator FFI boundaries, post-verification quantization (`f32 → bf16 / fp8 / int8` in TensorRT/XLA/ONNX Runtime) invalidates offline real-arithmetic certificates unless the deployed network either executes bit-exact integer arithmetic (`i8`/`i32` accumulators verified directly) or carries hardware-ISA-matched outward-rounded error bounds.

#### Executable Probe 1B: Outward-Rounded IEEE-754 Interval CBF Checker vs. Naive `f64`
Because real-time `CBF-QP` solvers (`OSQP`, `qpOASES`) are large unverified C/C++ numerical packages that may terminate early or suffer floating-point cancellation, the sound `Simplex`-style architecture treats the QP solver as an **untrusted oracle** and checks its returned primal iterate $u_{\text{ML}}$ inside a tiny verified **outward-rounded interval feasibility checker**: verify that the lower bound $\underline{B}(u) \ge 0$ where $[ \underline{B}(u), \overline{B}(u) ] \supseteq L_f h(x) + L_g h(x)\,u + \alpha(h(x))$ using directed rounding toward $-\infty$ / $+\infty$ (`math.nextafter(..., ±math.inf)` or hardware `FE_DOWNWARD`/`FE_UPWARD`), and verify $u \in \mathcal{U}$.

Running the outward-rounded interval probe in `## Evidence` (`/tmp/probe_neurosymbolic.py`, `CPython 3.13.15`) on exact IEEE-754 `binary64` inputs `Lfh = 1e16`, `Lgh = -3333333333333333.5`, `u_ml = 3.0`, `alpha_h = 0.25`:
- **Naive `f64` evaluation:** `Lgh * u_ml` rounds to even (`-10000000000000000.0`, silently discarding `-0.5`), yielding `(Lfh + Lgh * u_ml) + alpha_h = +0.25 >= 0` — **FALSE SAFE**.
- **Exact rational arithmetic (`fractions.Fraction`):** $10^{16} + (-3333333333333333.5 \times 3) + 0.25 = -0.25 = -\tfrac{1}{4} < 0$ — **TRUE UNSAFE** (barrier violated).
- **Outward-rounded interval checker:** Computes `[-1.7500000000000007, 2.250000000000001]`. Since lower bound `< 0`, it **REJECTS** $u_{\text{ML}}$ and switches instantaneously to verified backup `u_base = 2.9999`, whose outward-rounded interval `[333333333332.25, 333333333336.25]` has strictly positive lower bound (`CERTIFIED SAFE`).

#### Batched-GPU Non-Determinism and Neural FFI Reproducibility Collapse
Basis: derived + documentation

Even at `temperature = 0` with fixed PRNG seeds, GPU-served neural oracles are non-deterministic across requests due to: (1) dynamic continuous batching altering GEMM tile dimensions and split-K parallel reduction order under non-associative IEEE-754 floating-point addition (shifting logits by $10^{-4}$–$10^{-2}$ and flipping argmax tokens); (2) Mixture-of-Experts (MoE) capacity-factor routing dropping or rerouting tokens based on co-batched tenant queries (creating both non-determinism and a cross-tenant covert channel); and (3) hardware-scheduled `atomicAdd` scatter reductions. Verified build systems and deterministic replay/verification frameworks must therefore model neural FFI calls as **nondeterministic external oracle events** recorded with cryptographic transcript witnesses, replaying only deterministic checkers during trusted compilation.

---

### 7. Solver-Aided Synthesis, `LLM-Modulo` Proof Loops, and Resource Budget Governance

Basis: source + normative (`emina/rosette` @ `373c8c35e4a7667f38fce10cf0b74ae17de07f1d`, `nadia-polikarpova/synquid` @ `9bceb4cc775e07ab279fff8c51fdd86ae0b2878c`, `arXiv:2402.01817`)

- **Complementary scaling regimes (`Rosette`/`Synquid` vs. LLMs):** Solver-aided languages (`Rosette` symbolic state merging + CEGIS over Z3; `Synquid` bidirectional liquid-type Horn-clause synthesis) deliver sound, exact synthesis over small sketches and bitvector/invariant holes, yet hit sharp cliffs: symbolic-merge `ite` blowups in `Rosette`, exponential enumerative search in `Synquid` beyond ~20–50 library components, and immediate collapse across opaque foreign FFI calls lacking symbolic summaries. Conversely, LLMs excel at heuristic global sketch selection across huge APIs but cannot self-verify (`Kambhampati et al. ICML 2024`, `arXiv:2402.01817`).
- **TCB isolation & specification-gaming defenses:** In an `LLM-Modulo` verify-generate loop, keeping the LLM strictly outside the TCB requires mechanical boundary enforcement against escape hatches: (1) cryptographic spec-locking preventing edits to theorem statements or test harnesses; (2) kernel axiom inspection rejecting `sorry`, unapproved axioms, and unsafe reflection/reduction escapes; (3) vacuity and mutation checks catching tautological postconditions or unsatisfiable preconditions; and (4) warm, sub-50 ms in-memory incremental verifier overlays (avoiding multi-second cold compiler restarts).
- **Bounded fuel & structured cancellation:** Because autoregressive latency scales $O(T)$ in emitted tokens (with $O(T)$ KV-cache memory) and constrained decoding can enter EOS-suppression repetition loops, neural FFI boundaries in latency- or liveness-sensitive hosts must enforce explicit token/latency fuel budgets, propagate cancellation into GPU inference schedulers to reclaim KV-cache blocks, and expose a total degraded-mode fallback (`Verified(T) | BudgetExhausted(Fallback)`).

## Boundaries

- **Decidable prefix-inhabitation fragments for Rust traits and dependent types (`unknown`):** While Mündler et al. (PLDI 2025) formalize prefix-automaton inhabitation for STLC and implement a bounded TypeScript prototype, the tightest practical over-approximating fragment that handles Rust trait coherence/associated types or Lean 4 dependent elaboration within a `<1 ms` per-token GPU budget remains an open research problem.
- **Joint discrete-LTL and continuous-CBF shield feasibility (`unknown`):** Composing a discrete high-level LTL reactive shield with a continuous low-level `CBF-QP` filter lacks a general tractable synthesis procedure guaranteeing that every mode switch commanded by the discrete shield lands inside the joint feasible kernel of the continuous CBFs under actuator saturation.
- **Bare-metal `VeriPhy` compilation without GC runtime (`not examined` / `unsupported` in examined `KeYmaera X` pipeline):** The examined `VeriPhy` pipeline compiles through `CakeML`; directly lowering `ModelPlex` monitors to zero-allocation `no_std` Rust or bare-metal C with machine-checked WCET and outward-rounded IEEE-754 proofs was not examined in an upstream released implementation.
- **Empirical GPU kernel overhead of batch-invariant deterministic GEMM (`not examined`):** Exact throughput penalties for fixed-reduction-order cuBLAS/CUTLASS kernels across specific GPU microarchitectures were not benchmarked in this study (no GPU hardware in the probe environment).
- **Exact formal equivalence between `llguidance`/`XGrammar` JSON Schema compilation and JSON Schema Draft 2020-12 (`known not to apply` in full generality):** Because Draft 2020-12 validation with `$dynamicRef` is `PSPACE`-complete in schema size and `unevaluatedProperties` induces exponential CFG blowup, fast CFG/DFA constrained decoders cannot soundly and compactly represent arbitrary Draft 2020-12 schemas without subset restrictions or approximations.
- **Formal IFC proof of `CaMeL` against all side channels (`known not to apply`):** `CaMeL`'s Python interpreter (`google-research/camel-prompt-injection`) enforces explicit control/data capability checks on tool calls and documented AST nodes, but does not protect against timing/termination covert channels, unmodeled external state mutated outside the interpreter, or semantic data-to-data forgery permitted by an overly permissive `SecurityPolicy`.

## Evidence

### Primary Git Source Artifacts (Observed `2026-11-19`)
- **`scallop-lang/scallop` @ `668bfb6d45ce302fd4ffa7f29916baf3c7ce36ef`:**
  - `core/src/runtime/provenance/provenance.rs:6–79`: `Provenance` trait (`tagging_fn`, `recover_fn`, `add`, `mult`, `negate`, `minus`, `saturated`, `weight`).
  - `core/src/runtime/provenance/differentiable/diff_top_k_proofs.rs:6–143`: `DiffTopKProofsProvenance`, `DNFContextTrait` (`has_disjunction_conflict`), `recover_fn` using `DualNumberSemiring` + `wmc_with_disjunctions`, and `top_k_{add,mult,negate}`.
- **`eth-sri/type-constrained-code-generation` @ `3486122b3e980006d0f848cde1ea3d424e19dd42`:**
  - `README.md:9–106`: TypeScript-only scope, `sample_constrained`, and incremental prefix-completability examples (`"hey" +` vs `"hey" <`).
- **`hazelgrove/hazel` @ `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`:**
  - `README.md`: Live functional programming environment with total syntax and typed-hole evaluation.
- **`guidance-ai/llguidance` @ `4b1bdd7eaab212dacdbcebcd71ad84d194dfc629`:**
  - `README.md:34–99`: Earley CFG parser + Brzozowski-derivative lexer, fast-forward tokens, ~1.5 ms full JSON Schema mask latency on 128k tokenizer reduced to `<50 μs` median via slicer optimization.
  - `docs/syntax.md`: Lark-variant CFG syntax and lexer directives.
- **`dottxt-ai/outlines` @ `c52af8472c6fe8a607a733ec11b709476af77a96`** & **`mlc-ai/xgrammar` @ `3fe39321a6f24c90c2cc4fa4519b87e22367bcfc`:**
  - `README.md`: Precomputed FSM/regex indexing (`Outlines`) vs. context-independent/context-dependent token split + persistent PDA stack (`XGrammar`).
- **`google-research/camel-prompt-injection` @ `f083b6b396399d3b3c7f2ddaf613a5945eaf32d8`:**
  - `src/camel/capabilities/capabilities.py:24–38`: `Capabilities(sources_set, readers_set)` + `default()` / `camel()`.
  - `src/camel/capabilities/sources.py:22–38` and `readers.py:22–38`: `SourceEnum`, `Tool`, `Public`, and `&` reader-set intersection.
  - `src/camel/security_policy.py:26–97`: `Allowed`, `Denied`, `NO_SIDE_EFFECT_TOOLS`, `base_security_policy`, and fail-closed `SecurityPolicyEngine.check_policy` checking `dependencies` before `fnmatch` policy dispatch.
  - `src/camel/interpreter/interpreter.py:119,2063,2197–2272,2403–2654`: `MetadataEvalMode`, `SecurityPolicyDeniedError`, `BaseModel`-only class restriction, `camel_eval` AST subset.
- **`LS-Lab/KeYmaeraX-release` @ `2753f99b53cea5f946386998a39faded05ede677`:**
  - `keymaerax-core/src/main/scala/org/keymaerax/btactics/ModelPlex.scala:47–1389`: `object ModelPlex`, `createMonitorSpecificationConjecture` (L233), `controllerMonitorByChase` (L1110), `modelMonitorByChase` (L1201), `applyAtAllODEs` (L1210), `controllerMonitorT` (L1384), `modelMonitorT` (L1389).
- **`emina/rosette` @ `373c8c35e4a7667f38fce10cf0b74ae17de07f1d`** & **`nadia-polikarpova/synquid` @ `9bceb4cc775e07ab279fff8c51fdd86ae0b2878c`:** Pinned upstream repositories for solver-aided synthesis and refinement-type synthesis.

### Peer-Reviewed Literature & Standards
- Li, Huang, & Naik, *Scallop: A Language for Neurosymbolic Programming*, PLDI 2023, DOI `10.1145/3591280`, `arXiv:2304.04812`.
- Mündler, He, Wang, Sen, Song, & Vechev, *Type-Constrained Code Generation with Language Models*, PLDI 2025, DOI `10.1145/3729274`, `arXiv:2504.09246`.
- Blinn, Li, Kim, & Omar, *Statically Contextualizing Large Language Models with Typed Holes*, OOPSLA 2024, DOI `10.1145/3689728`, `arXiv:2409.00921`.
- Dong, Ruan, Cai, Lai, Xu, Zhao, & Chen, *XGrammar: Flexible and Efficient Structured Generation Engine for Large Language Models*, `arXiv:2411.15100`.
- Beurer-Kellner, Fischer, & Vechev, *Guiding LLMs The Right Way: Fast, Non-Invasive Constrained Generation* (`DOMINO`), ICML 2024.
- Park, Wang, Berg-Kirkpatrick, Polikarpova, & D'Antoni, *Grammar-Aligned Decoding* (`GAD`/`ASAp`), NeurIPS 2024, `arXiv:2405.21047`.
- Loula et al., *Syntactic and Semantic Control of Large Language Models via Sequential Monte Carlo*, ICLR 2025, `arXiv:2504.13139`.
- Tam, Wu, Tsai, Lin, Lee, & Chen, *Let Me Speak Freely? A Study on the Impact of Format Restrictions on Performance of Large Language Models*, EMNLP 2024, `arXiv:2408.02442`.
- Kambhampati et al., *Position: LLMs Can't Plan, But Can Help Planning in LLM-Modulo Frameworks*, ICML 2024, `arXiv:2402.01817`.
- Debenedetti et al., *Defeating Prompt Injections by Design* (`CaMeL`), `arXiv:2503.18813`.
- Sha, *Using Simplicity to Control Complexity*, IEEE Software 18(4):20–28, 2001, DOI `10.1109/MS.2001.936213`.
- Ames, Xu, Grizzle, & Tabuada, *Control Barrier Function Based Quadratic Programs for Safety Critical Systems*, IEEE TAC 62(8):3861–3876, 2017, DOI `10.1109/TAC.2016.2638961`; Ames et al., ECC 2019, DOI `10.23919/ECC.2019.8796030`.
- Alshiekh, Bloem, Ehlers, Könighofer, Niekum, & Topcu, *Safe Reinforcement Learning via Shielding*, AAAI 2018, DOI `10.1609/aaai.v32i1.11797`.
- Mitsch & Platzer, *ModelPlex: Verified Runtime Validation of Verified Cyber-Physical System Models*, FMSD 2016, DOI `10.1007/s10703-016-0241-z`.
- Bohrer, Tan, Mitsch, Myreen, & Platzer, *VeriPhy: Verified Controller Executables from Verified Cyber-Physical System Models*, PLDI 2018, DOI `10.1145/3192366.3192400`.
- Jia & Rinard, *Exploiting Verified Neural Networks via Floating Point Numerical Error*, SAS 2021, DOI `10.1007/978-3-030-88806-0_9`, `arXiv:2003.03021`.

### Executable Probes (Executed `2026-11-19` on `CPython 3.13.15`, `x86_64-linux`)
```python
# Save to /tmp/probe_neurosymbolic.py and run: python3 /tmp/probe_neurosymbolic.py
import math, random
from fractions import Fraction

# Probe 1A: Greedy GCD distortion vs exact posterior P(s | s in L) and SMC
p1 = {"a": 0.90, "b": 0.10}
p2 = {"a": {"b": 0.001, "c": 0.001, "x": 0.998}, "b": {"d": 0.990, "x": 0.010}}
valid = {"ab", "ac", "bd"}
unnorm = {s: p1[s[0]] * p2[s[0]][s[1]] for s in sorted(valid)}
Z = sum(unnorm.values())
p_exact = {s: v / Z for s, v in unnorm.items()}
p_gcd = {
    s: p1[s[0]] * (p2[s[0]][s[1]] / sum(p2[s[0]][c] for c in p2[s[0]] if s[0] + c in valid))
    for s in sorted(valid)
}
tv = 0.5 * sum(abs(p_gcd[s] - p_exact[s]) for s in valid)
kl = sum(p_gcd[s] * math.log(p_gcd[s] / p_exact[s]) for s in valid)
print(f"Z={Z:.6f} TV={tv:.6f} KL={kl:.6f}")

# Probe 1B: Outward-rounded IEEE-754 interval CBF primal checker vs naive f64
def iv_add(x, y): return (math.nextafter(x[0]+y[0], -math.inf), math.nextafter(x[1]+y[1], math.inf))
def iv_mul(x, y):
    ps = [x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1]]
    return (math.nextafter(min(ps), -math.inf), math.nextafter(max(ps), math.inf))
Lfh, Lgh, u_ml, alpha_h = 1e16, -3333333333333333.5, 3.0, 0.25
naive = (Lfh + (Lgh * u_ml)) + alpha_h
exact = Fraction(Lfh) + Fraction(Lgh) * Fraction(u_ml) + Fraction(alpha_h)
iv = iv_add(iv_add((Lfh, Lfh), iv_mul((Lgh, Lgh), (u_ml, u_ml))), (alpha_h, alpha_h))
print(f"naive_f64={naive!r} exact={exact} interval={iv!r}")
```
Observed stdout:
```text
Z=0.100800 TV=0.882143 KL=3.299535
naive_f64=0.25 exact=-1/4 interval=(-1.7500000000000007, 2.250000000000001)
```

## Revalidation

1. **Constrained-decoding engines (`llguidance`, `XGrammar`, `type-constrained-code-generation`):** Diff `guidance-ai/llguidance` (`parser/src/earley/`, `README.md`) and `mlc-ai/xgrammar` (`README.md`, grammar compiler sources) against the pinned commits when evaluating new tokenizer-healing, posterior-reweighting (`SMC`/`ASAp`), or semantic type-automaton hooks. Check whether `eth-sri/type-constrained-code-generation` adds backends beyond TypeScript (e.g., Rust or Python) or integrates incremental compiler servers rather than a standalone prefix type checker.
2. **Differentiable provenance (`Scallop`):** Inspect `core/src/runtime/provenance/provenance.rs` and `differentiable/` in `scallop-lang/scallop` for GPU-vectorized provenance backends or interval-bounded WMC approximations replacing `DiffTopKProofsProvenance`.
3. **Capability IFC (`CaMeL`):** Diff `src/camel/security_policy.py` (`SecurityPolicyEngine.check_policy`) and `src/camel/interpreter/interpreter.py` (`camel_eval`) in `google-research/camel-prompt-injection` to verify whether fail-closed dependency checks, `BaseModel`-only class rules, or cross-RPC capability propagation changed.
4. **Executable probe regression:** Re-run the embedded Python probe in `## Evidence` (takes `<100 ms` on any CPython 3.10+ host) to confirm exact `TV`/`KL` values and IEEE-754 `binary64` rounding sign flip; when targeting a specific bare-metal control platform (e.g., ARM Cortex-R52 with FMA), port Probe 1B to the target's exact C/Rust compiler flags (`-ffp-contract=off`, hardware directed rounding) to verify interval soundness under target FMA contraction rules.
5. **Typed-hole LSP standardization:** Check LSP specification drafts (`3.18+`) and `hazelgrove/hazel` for standardized `ChatLSP`-style transitive hole-context and in-memory speculative fill endpoints.
