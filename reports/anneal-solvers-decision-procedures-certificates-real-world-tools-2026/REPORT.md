<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# External Decision Procedures, Proof-Producing Solvers, and Certificate Checkers for Anneal

## Summary

Anneal's soundness architecture (`PRINCIPLES.md`,
`trusted/audit/TrustedBoundary.lean`, and `trusted/lean/foundation-lock.json`)
enforces a strict separation between **finding** a proof and **checking** a
proof. External decision procedures—including CDCL SAT and QBF solvers
(`CaDiCaL`, `Kissat`, `DepQBF`, `CAQE`, `Pedant`), bit-blasters (`Bitwuzla`,
`Boolector`), SMT solvers (`cvc5`, `Z3`, `OpenSMT`), equality-saturation and
Datalog engines (`egg`, `slotted-egraphs`, `egglog`, `Soufflé`, `Ascent`),
computer algebra and SDP systems (`Singular`, `CryptoLine`, `CSDP`,
`Clarabel.rs`, `RealCertify`), floating-point error analyzers (`Gappa`,
`FPTaylor`, `Sollya`, `MetiTarski`), hardware/software model checkers and CHC
solvers (`ABC`, `btormc`, `AVR`, `Pono`, `Spacer`, `Eldarica`, `Golem`, `Mata`,
`SPOT`, `Ultimate Automizer`, `T2`), and SyGuS/LLM synthesizers (`cvc5 SyGuS`,
`Souper`, `LEMUR`, `Loopy`)—execute outside the Lean 4 kernel as untrusted
oracles. None of their C, C++, Rust, Scala, or Python binaries enter Anneal's
Trusted Computing Base (TCB).

Across 20 concrete certificate-checking use cases spanning 7 solver families,
this report establishes five architectural results governing how real-world
proof-producing solvers integrate with Anneal's four `trusted/lean/` primitives
(`Language SemObs` + `BehaviorCodec`, `ProductiveOn` + `InhabitedPre`,
positive per-obligation `VerificationResult`, and `SmallStepMachine` with
`EventualBehaviorOf` + `StepResult.externalCall`):

1. **Kernel-reducible certificate checking without `native_decide`:**
   `TrustedBoundary.lean` (lines 314–329) forbids `axiom`, `unsafe`, `partial`,
   `by_elab`, `run_tac`, `native_decide` (`Lean.ofReduceBool`), and
   `decide +native`, and Phase 2 (`"audit"`, line 972) replays every
   non-foundation declaration in a clean `foundation`-only (`Init.*`) kernel
   environment via `base.toKernelEnv.replay locals`. Consequently, unlike
   Lean 4's upstream `bv_decide` (which relies on `Lean.ofReduceBool` native
   code execution in standard setups), every Anneal certificate checker in
   `theory/` must reduce inside Lean's interpreted kernel Whnf reducer (`rfl`)
   using total, structurally terminating functions over `Init.*` types.
2. **Witness-first certificate formats eliminate kernel search and quadratic
   array copying:** In Lean 4's kernel reducer (unlike the Lean VM),
   `Array.set` copies the underlying spine in $O(N)$ steps, turning naive array
   mutation into an $O(N^2)$ bottleneck during `rfl` and `replay`. High-speed
   kernel certificate checkers in `theory/` therefore combine (a) persistent
   radix-2/radix-4 trees (`PArray`, $O(\log N)$ updates) for mutable state in
   `LRAT`/`LIDRUP`/`VeriPB`, (b) integer-ID hash-consed DAG arenas (`TermArena`)
   for $O(1)$ term equality in `Alethe`/`LFSC`/`egg`, (c) oracle-supplied
   permutation witnesses (`perm : Array UInt16`) instead of in-kernel sorting
   for AC normalization and NTT index partitions, (d) denominator-cleared
   `Nat`-pair dot products and binary-fuel structural recursion (`powMod`) to
   hit Lean's GMP C++ kernel fast path in `Farkas`/`VIPR`, `PAC`/`Pastèque`,
   `SOS`, and `Pocklington`, and (e) proof-irrelevant `private theorem`
   (`thmInfo`) chunking so `base.toKernelEnv.replay` never unfolds completed
   sub-certificates.
3. **Two canonical integration modes cover all 20 solver families without
   expanding `trusted/`:**
   - **Mode A (Direct Obligation Discharge in `VerificationResult`):** Symbolic
     execution of `Runtime(PostCleanup)` MIR emits pure verification conditions
     into a function's `obligations : List Obligation` inside
     `VerificationResult policy waived obligations`. Shared multi-target
     certificates (`MultiLRAT`, `Alethe`, `LIACert`, `EgglogProvenanceCert`)
     batch-verify all obligations of a function in a single `private theorem`
     kernel reduction while preserving per-obligation waiver granularity
     (`ob.id ∈ waived ∨ ob.prop`).
   - **Mode B (Semantic Abstraction and Compilation via `Language SemObs` +
     `BehaviorCodec`):** Domain-specific verification languages $L_v$ (bitvector
     circuits, e-graph term DAGs, polynomial rings $\mathbb{Z}[\vec{x}]/\langle
     p \rangle$, IEEE-754 real-enclosure $\varepsilon$-balls, CHC predicate
     models, and finite-state transducers) connect to `MirLang` via `Abstracts`
     and `Compiles`. Monotonicity of `codec.toMorphism` transports both safety
     (`SpecOn`) and liveness/termination (`ProductiveOn` + `InhabitedPre`) back
     to concrete MIR.
4. **`Language.obs : Out → SemObs` and nondeterministic `Behavior` resolve
   redundant algebraic representations and quantitative error bounds:** In
   `BehaviorCodec L₁ L₂`, `decodeOut` must be injective on its `some` domain
   (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`). For redundant multi-limb
   cryptographic arithmetic (`CryptoLine`, `formosa-mlkem`, `s2n-bignum`),
   retaining the unreduced integer limb tuple in `L_v.Out` (so `decodeOut` is a
   bijection) while quotienting modulo $p$ in `L_v.obs : Out → SemObs`
   satisfies `obs_decodeOut` with zero trusted changes. For floating-point
   error bounds (`Gappa`, `FPTaylor`, `Sollya`), modeling the abstract
   specification's behavior as the nondeterministic $\varepsilon$-ball
   $\{o \mid |\text{toReal}(o) - f_{\mathbb{R}}(q)| \le \varepsilon\}$ turns
   standard behavioral refinement (`≤`) directly into a machine-checked
   $\varepsilon$-accuracy theorem.
5. **Demonic-to-angelic Skolem bridging and self-verified native checker
   bootstrapping:** Skolem-AIG certificates (`DepQBF`, `CAQE`, `Pedant`,
   `Manthan`) construct computable witness functions that bridge demonic
   `StepResult.externalCall` nondeterminism to angelic `ProductiveOn` witnesses
   without `Classical.choice`. For multi-gigabyte industrial proofs exceeding
   in-kernel memory budgets, Anneal supports both dominator-cut `thmInfo`
   splitting (`ParaDRAT`-style) and bootstrapping self-verified Rust certificate
   checkers (`CreuSAT` / `cake_lpr` pattern) proved sound via
   `Trusted.CrateTheorem`.

## Applicability

The findings in this report apply to the subjects recorded in `REPORT.json`:

1. **Anneal trust boundary and locked foundation** at
   `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:
   - `trusted/audit/TrustedBoundary.lean` (two-phase `"preflight"` and `"audit"`
     inspector, closed `commandKinds` and `allowedAttributeNames`, rejection of
     `native_decide` and `decide +native` at lines 318–329, expression-graph
     traversal `exprEdges` at lines 480–516, and clean kernel replay
     `base.toKernelEnv.replay locals` at lines 971–972).
   - `trusted/lean/Trusted/Attributes.lean` (`Trusted.expandTrustDeclaration`
     and `Trusted.candidate`).
   - `trusted/lean/foundation-lock.json` (locked Lean `v4.34.1` `Init.*`
     modules and the three permitted axioms `Classical.choice`, `Quot.sound`,
     and `propext`).
2. **Anneal trusted behavioral refinement and small-step core** at
   `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (and its 4-primitive
   consolidation tracked in `gh_part1_body.md`):
   - `Language (SemObs : Type)`, `BehaviorCodec L₁ L₂`, `Compiles`, `Abstracts`,
     `ProductiveOn`, `InhabitedPre`, and `VerificationResult` in
     `trusted/lean/Trusted/Refinement.lean`, and
   - `SmallStepMachine`, `EventualOut`, `EventualBehaviorOf`, and
     `StepResult.externalCall` in `trusted/lean/Trusted/StepResult.lean`.
3. **Lean 4 theorem prover** at
   `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`),
   specifically contrasting upstream `Std.Tactic.BVDecide` (which outside
   Anneal uses `Lean.ofReduceBool`) and `omega`/`grind` (which elaborate
   explicit kernel proof terms) against Anneal's `Init.*`-only closed kernel
   environment.
4. **External solver and certificate-checker ecosystems across Categories 1–7**
   as identified in `REPORT.json`: claims regarding solver algorithms,
   certificate grammars (`DRAT`, `LRAT`, `FRAT`, `GRAT`, `LIDRUP`, `VeriPB`,
   `QRAT`, `FERP`, `Alethe`, `LFSC`, `CPC`/`Eunoia`, `VIPR`, `CPF`, `PAC`/`LPAC`,
   `AIGER`), and verified checkers (`cake_lpr`, `cake_pb`, `gratchk`, `Pastèque`,
   `Carcara`, `Ethos`, `SMTCoq`, `CeTA`, `Flocq`, `CoqInterval`, `Certifaiger`,
   `CreuSAT`) reflect their published specifications and upstream architectures.
   Mappings onto `theory/Anneal/Solv/*` define target certificate-checker
   architectures engineered to satisfy `TrustedBoundary.lean` invariants.

## Findings

### 1. Architectural Overview: Proof-Producing Oracles Under Anneal's 4-Primitive Trusted Core

`Basis: normative + source + derived`

Anneal's TCB audit invariant (`PRINCIPLES.md` and `README.md`) requires that
auditing `trusted/` alone suffices to verify that any accepted crate satisfies
its specification, even if all code in `theory/` and all external solver
binaries are adversarial. In `trusted/audit/TrustedBoundary.lean`, this
invariant is enforced by five mechanical gates that directly constrain how
external decision procedures can interact with Lean 4:

1. **No External I/O or FFI During Elaboration (`"preflight"`):**
   `inspectSyntax` (`TrustedBoundary.lean:312-352`) rejects `#eval`, `run_tac`,
   `by_elab`, `unsafe`, `partial`, `axiom`, `coinductive`, `deriving`, and
   `set_option`. `inspectAttrInstance` (`L240-275`) rejects `@[extern]`,
   `@[implemented_by]`, and `@[csimp]`. External solvers therefore cannot be
   invoked via FFI or `IO` inside `.lean` files during verification; instead,
   `cargo-anneal` invokes external solvers during proof-script generation and
   serializes their output certificates as pure Lean data declarations or term
   literals inside `.anneal/Proof.lean`.
2. **Prohibition of `native_decide` (`Lean.ofReduceBool`):**
   `inspectSyntax` (`TrustedBoundary.lean:318-329`) explicitly rejects
   `Lean.Parser.Tactic.nativeDecide` (`native_decide`) and `decide +native`.
   Furthermore, in Phase 2 (`"audit"`), `closure` (`L562-578`) rejects any
   reachable axiom outside `{Classical.choice, Quot.sound, propext}`—which
   blocks `Lean.ofReduceBool` and `Lean.trustCompiler` at the `.olean` kernel
   level even if surface syntax checks were bypassed. Consequently, every
   reflective boolean certificate checker `checkCert goal cert = true` must be
   discharged by `rfl` (`Eq.refl true`) inside Lean's interpreted kernel Whnf
   reducer.
3. **Foundation Lock (`trusted/lean/foundation-lock.json`):**
   Only the locked `Init.*` modules of Lean `v4.34.1` are present in the
   foundation environment. Non-locked standard library namespaces—including
   `Std.Sat`, `Std.Tactic.BVDecide`, and `Rat` (`Std.Internal.Rat`)—are outside
   `foundation-lock.json`. All data structures (`PArray`, `TermArena`, dyadic
   rationals, polynomial rings) and certificate checkers must be defined purely
   in `theory/` on top of `Init.*` (`Nat`, `Int`, `BitVec`, `UInt*`, `Array`,
   `ByteArray`, `List`, `WellFounded`).
4. **Expression-Graph Traversal Cost (`exprEdges`):**
   In `TrustedBoundary.lean:480-516`, `exprEdges` walks the DAG of every kernel
   `Expr` in `locals` using a `Std.HashSet Expr` worklist. Notice lines
   505–506: a `.lit (.natVal _)` or `.lit (.strVal _)` node is a single atomic
   leaf in `Expr` regardless of its bit-length! Encoding large certificates as
   packed `Nat` or `String`/`ByteArray` literals rather than deep AST trees of
   constructor applications keeps `exprEdges` traversal $O(1)$ in AST nodes.
5. **Double Kernel Evaluation (`base.toKernelEnv.replay locals`):**
   Every declaration in `locals` (`Trusted`, `Anneal`, `Mir`, `Proof`) is
   typechecked once when `lean` compiles the module and a second time when
   `base.toKernelEnv.replay locals` (`TrustedBoundary.lean:972`) replays all
   constants into a fresh `foundation`-only kernel environment. Because Lean's
   kernel treats `thmInfo` (`theorem` in `Prop`) as opaque once its proof term
   is checked—never unfolding a theorem's proof body when checking later
   declarations—wrapping each certificate reduction `checkCert goal cert = true`
   inside a `private theorem` prevents re-evaluation of the certificate when
   checking `Proof.verify_crate`.

---

### 2. Category 1: SAT, MaxSAT, QBF, and Bit-Blasting Proof Checkers (Use Cases 1–3)

`Basis: documentation + source + derived`

#### 2.1 Comparative Ecosystem Analysis of Category 1 Tools

1. **Bit-Blasters and SMT Bitvector Solvers (`Bitwuzla`, `Boolector`, Lean 4
   `bv_decide`):**
   - **Goals & Target Users:** Discharge quantifier-free fixed-width bitvector
     (`QF_BV`), array (`QF_ABV`), and floating-point (`QF_FP`) formulas in
     hardware verification, compiler backend validation (`Alive2`), and systems
     software verification.
   - **History & Lineage:** `Boolector` (Brummayer and Biere, TACAS 2009;
     Niemetz, Preiner, and Biere, JSAT 2015) pioneered word-level rewriting
     combined with lazy AIG (And-Inverter Graph) bit-blasting. `Bitwuzla`
     (Niemetz and Preiner, CAV 2023; `bitwuzla/bitwuzla`) succeeded `Boolector`
     with a redesigned local-search engine, ternary propagation, and granular
     Alethe/LRAT proof production. Lean 4's `bv_decide` (Böving et al., 2024;
     `Std.Tactic.BVDecide` in `leanprover/lean4`) brought verified bitvector
     rewriting, AIG construction (`Std.Sat.AIG`), Tseitin CNF lowering, and
     `LRAT` checking directly into Lean 4.
   - **Design Philosophy & Tradeoffs:** `Bitwuzla` maximizes solving speed via
     aggressive C++ word-level passes before bit-blasting to `CaDiCaL`/`Kissat`.
     `bv_decide` proves every word-level rewrite, AIG gate sharing step, and
     Tseitin encoding step inside Lean 4 so that no part of the bit-blaster is
     trusted; however, standard `bv_decide` invokes `Lean.ofReduceBool`
     (`native_decide`) to run the compiled `LRAT` checker at native C speed—a
     mechanism forbidden by Anneal's `TrustedBoundary.lean`.
2. **CDCL SAT Solvers and Clausal Proof Formats (`CaDiCaL`, `Kissat`,
   `drat-trim`, `lrat-trim`, `FRAT-rs`/`frat-elan`, `LIDRUP`):**
   - **Goals & Lineage:** `CaDiCaL` (Biere et al., `arminbiere/cadical`) and
     `Kissat` (Biere et al., `arminbiere/kissat`) are state-of-the-art CDCL SAT
     solvers dominating SAT Competitions. Historically, solvers emitted `DRUP`
     (Delete Reverse Unit Propagation) or `DRAT` (Delete Resolution Asymmetric
     Tautology; Wetzler, Heule, and Hunt, SAT 2014). Checking `DRAT` requires
     full unit-propagation search over the clause database, making verified
     checking slow.
   - **Evolution of Proof Formats (`DRAT` $\to$ `LRAT` $\to$ `FRAT` /
     `LIDRUP`):**
     - `drat-trim` and `lrat-trim` (Heule et al.) post-process `DRAT` proofs
       backward from the empty clause $\bot$ to prune unused clauses and emit
       **`LRAT` (Linear RAT)**, which annotates every added clause with explicit
       clause-ID unit-propagation hints.
     - `FRAT` (Final RAT; Baek, Carneiro, and Heule, TACAS 2021; `FRAT-rs` /
       `frat-elan`) decouples solver proof logging from hint generation by
       allowing solvers to emit lightweight `FRAT` traces with final-clause
       markers that `frat-elan` elaborates into full `LRAT` proofs.
     - `LIDRUP` (Linear Incremental DRUP; Biere, Faller, Fazekas, Fleury,
       Froleyks, and Pollitt, 2024; natively supported in `CaDiCaL`) emits
       linear unit-propagation hints *online* during incremental SAT solving
       (`assume`/`solve`/`failed` queries), eliminating the offline `drat-trim`
       bottleneck and supporting incremental UNSAT cores natively.
3. **Formally Verified Clausal and Pseudo-Boolean Checkers (`cake_lpr`,
   `GRAT`/`gratchk`, `ACL2 lrat-checker`/`FGL`, `IsaSAT`, `VeriPB`/`cake_pb`):**
   - **`cake_lpr`** (Tan, Heule, and Myreen, TACAS 2021; `CakeML/cake_lpr`):
     Verified in HOL4 and compiled to native x86-64/ARM machine code via the
     verified CakeML compiler; checks `LRAT` and `LPR` (Linear Propagation
     Redundancy, the strongest known polynomial-time checkable clausal system
     without extension variables).
   - **`GRAT` (`gratgen` / `gratchk`)** (Lammich, CADE-26, 2017): Uses a
     multi-threaded C++ elaborator (`gratgen`) to produce split certificate
     files checked by a formally verified Isabelle/HOL checker (`gratchk`
     extracted via Imperative HOL).
   - **`ACL2 lrat-checker` & `FGL`** (Hunt, Kaufmann, Swords et al.): Industrial
     hardware verification framework at Centaur/Intel/AMD combining AIG symbolic
     simulation (`FGL`) with an ACL2-verified `LRAT` checker.
   - **`IsaSAT`** (Blanchette, Fleury, Lammich, and Weidenbach, JAR 2018 /
     Isabelle Formalization of Logic): A full CDCL SAT solver with two-watched
     literals verified in Isabelle/HOL via stepwise refinement (`Sepref`) to
     LLVM/SML.
   - **`VeriPB` & `cake_pb`** (Bogaerts, Gocht, McCreesh, Myreen, Nordström, and
     Tan, AAAI/SAT/CP 2022–2023; `MIAOresearch/VeriPB`): Generalizes clausal
     proofs to $0\text{--}1$ Integer Linear Programming (Pseudo-Boolean
     constraints $\sum_i a_i \ell_i \ge b$) with cutting planes (addition,
     division, saturation) and dominance-based strengthening. This allows native
     1-step certification of cardinality constraints, MaxSAT optimization bounds,
     parity/XOR Gaussian elimination, and symmetry breaking that would require
     exponentially many or huge Tseitin-encoded clauses in `LRAT`.
4. **QBF, DQBF, and Boolean Functional Synthesis Certifiers (`DepQBF`,
   `QRAT-trim`, `CAQE`/`CertCheck`, `Pedant`, `FerpCheck`, `Manthan`):**
   - **`DepQBF` & `QRAT-trim`** (Lonsing and Egly; Heule, Seidl, and Biere,
     IJCAR 2014): QDPLL solver and proof trimmer for the **`QRAT` (Quantified
     RAT)** proof system, which certifies both satisfiability (Skolem functions)
     and unsatisfiability (Herbrand functions) of arbitrary-prefix QBFs via
     clause addition, universal reduction, and quantifier elimination.
   - **`CAQE` & `CertCheck`** (Rabe and Tentrup, FMCAD 2015): Clause-abstraction
     QBF solver emitting AIGER circuit witnesses (`CertCheck`) encoding Skolem
     or Herbrand functions.
   - **`FerpCheck`** (CADE/SAT QBF trace checking): Certifies false QBF formulas
     via **FERP (uatan-style Expansion and Resolution Proofs)**, recording the
     exact universal variable instantiations and propositional resolution steps.
   - **`Pedant`** (Reichl, Slivovsky, and Szeider, TACAS/CAV 2021–2023): Solver
     and certifier for **DQBF (Dependency Quantified Boolean Formulas)** with
     Henkin quantifiers ($\forall x_1 \forall x_2 \exists y_1(x_1) \exists
     y_2(x_2)$), emitting explicit definability/consistency certificates for
     partial information dependencies.
   - **`Manthan`** (Golia, Roy, and Meel, CAV 2020; `meelgroup/manthan`):
     Data-driven Boolean functional synthesizer that learns candidate Skolem
     functions via decision trees, repairs them with MaxSAT/CEGAR counterexamples,
     and emits an AIGER Skolem circuit certified by a single UNSAT check of the
     negated specification $\Phi(\vec{x}, \vec{S}(\vec{x}))$.

---

#### 2.2 Use Case 1: Verified Bit-Blasting (`AIG` / Tseitin `CNF`) + `LRAT` Unsatisfiability Certificate Checker

- **Engineering Problem:** Fixed-width bit-level reasoning in `unsafe` and
  low-level Rust: bitwise intrinsics (`u64::leading_zeros`, `rotate_left`,
  `reverse_bits`, BMI2 `pext`/`pdep`), SWAR (SIMD Within A Register) UTF-8/ASCII
  scanners, niche-encoded enum discriminant decoding in `rustc`
  `Runtime(PostCleanup)` MIR (where `discriminant_value` computes tag ranges via
  wrapping addition and range comparisons), and packed bitfield extraction in
  OS kernel page-table entries (`PageTableEntry`) and network headers.
- **Untrusted Oracles:** `Bitwuzla` / `Boolector` (word-level preprocessing +
  AIG bit-blasting) paired with `CaDiCaL` or `Kissat`, post-processed by
  `lrat-trim`, `frat-elan`, or `cake_lpr` (or emitted directly by `CaDiCaL` via
  `LIDRUP`/`LRAT`).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/BitBlastLRAT.lean`):**
  1. **Tseitin AIG Witness (`AIGCert`):** A topologically sorted array of
     And-Inverter Graph (`AIG`) nodes mapping each `BitVec w` wire to $w$
     signed integer literals ($\pm v$), with each internal gate $g = \ell_1
     \land \ell_2$ generating the three Tseitin clauses $(\neg g \lor \ell_1)$,
     $(\neg g \lor \ell_2)$, and $(g \lor \neg \ell_1 \lor \neg \ell_2)$.
     Because each extension variable $g$ is a deterministic function of earlier
     variables ($g_i$ depends only on $v < g_i$), extending any input valuation
     `env : BVValuation` to the AIG variables is total and unique.
  2. **Binary `LRAT` / `VeriPB` Proof (`Array LRATStep`):** A sequence of clause
     addition steps `(clauseId : Nat, lits : Array Int32, rupHints : Array Nat,
     ratHints : Array (Nat × Array Nat))` and deletion steps `(delIds : Array
     Nat)`. Checking an RUP step sets all literals of `lits` to `false` and
     propagates each hint clause $C_h$ in `rupHints` in order, verifying that at
     most one literal of $C_h$ is unassigned (becoming `true`) until a hint
     clause has all literals `false` ($\bot$).
  3. **Soundness Theorem in `theory/`:**
     ```lean
     theorem bitblast_lrat_sound (e : BVExpr 1) (aig : AIG) (cnf : CNF)
         (steps : Array LRATStep) :
         checkTseitin e aig cnf = true →
         checkLRAT cnf steps = true →
         ∀ env, evalBVExpr env e = 1#1
     ```
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **`Language SemObs` + `BehaviorCodec` (`Abstracts`):** Define
     $L_{\text{BV}} : \text{Language } (\text{EventualOut Empty } (\text{BitVec }
     w))$ where `Prog := BVCircuit w`, `Query := BVValuation`, `Out :=
     EventualOut Empty (BitVec w)`, `obs o := .terminated [] (.returned ())`,
     and `sem c q` is a total, deterministic singleton returning `.terminated []
     (.returned (evalCircuit q c))`. For a loop-free, memory-pure MIR basic-block
     DAG $p_{\text{mir}}$, `BehaviorCodec L_{\text{BV}} L_{\text{MIR}}` maps
     `BVValuation` to initial MIR `LocalFrame` states (`encodeQuery` /
     `decodeQuery`) and maps `.terminated [] (.returned bv)` to the MIR terminal
     state (`encodeOut` / `decodeOut`), while setting `decodeOut (.terminated _
     (.failed .ub)) = none` and `decodeOut .diverges = none`. Proving
     `Abstracts L_{\text{BV}} L_{\text{MIR}} codec c_{\text{bv}} p_{\text{mir}}`
     reduces to checking that every intermediate MIR checked arithmetic/shift
     guard holds via `bitblast_lrat_sound`.
  2. **`ProductiveOn` + `InhabitedPre`:** Because $L_{\text{BV}}$ is total and
     deterministic, `L_{\text{BV}}.ProductiveOn pre c_{\text{bv}}` holds
     automatically for any `InhabitedPre pre`, which transports via `Abstracts`
     to prove that $p_{\text{mir}}$ never panics, never triggers `.failed .ub`,
     and always terminates on `pre`.
  3. **Kernel Engineering Without `native_decide`:** In Lean 4's kernel Whnf
     reducer, `Array.set` copies the entire array in $O(N)$ steps because the
     kernel does not use reference-counted destructive updates. `checkLRAT`
     therefore represents the clause database and literal assignment table as a
     **persistent radix-2 binary trie (`PArray α` of depth 16)** defined in
     `theory/`, achieving $O(\log N)$ purely functional updates inside `rfl`
     and `base.toKernelEnv.replay`.

---

#### 2.3 Use Case 2: `FRAT` / `LIDRUP` Elaborated `DRAT→LRAT` & Incremental Assumption-Core (`UNSAT Core`) Certificate Checker

- **Engineering Problem:** When verifying a complex Rust function with dozens of
  `match` arms, `?` early returns, and nested `unsafe` blocks (such as a
  zero-copy packet parser in `zerocopy` or a `serde` deserializer), symbolic
  execution generates hundreds of branch feasibility and assertion queries that
  share 95% of their SSA path context. Running a standalone SAT check per branch
  duplicates work, and when an obligation fails or succeeds, Anneal needs a
  **minimal UNSAT core** of path assumptions to prune unreachable MIR basic
  blocks or emit rustc-style blame spans (`PRINCIPLES.md`).
- **Untrusted Oracles:** `CaDiCaL` in incremental IPASIR/LIDRUP mode
  (`assume(lit)` + `failed(lit)` core extraction with online `LIDRUP` linear
  hints) and `FRAT-rs` / `frat-elan` (elaborating solver logs into trimmed
  multi-target `LRAT`).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/IncrementalLRAT.lean`):**
  - **`MultiLRATCert`:** A shared base clause set $C_{\text{base}}$ encoding the
    function's SSA dataflow graph once, paired with a tree of monotonic `LRAT` /
    `LIDRUP` derivation segments and an array of assumption queries $Q_k =
    (\text{assumptions } A_k, \text{derivedClauseId } c_k, \text{coreSubset }
    A_k^{\text{core}} \subseteq A_k)$.
  - `checkMultiLRAT : CNF → Array AssumptionQuery → MultiLRATCert → Array Bool`
    traverses the shared derivation tree once using persistent `PArray`
    snapshots at branch split points and verifies for each query $k$ that the
    derived clause $C_{c_k}$ consists solely of negated literals from
    $A_k^{\text{core}} \subseteq A_k$ ($\bigvee_{\ell \in A_k^{\text{core}}}
    \neg \ell$).
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **Batching in `VerificationResult policy waived obligations`:** Instead of
     generating $m$ separate large proof constants in `.anneal/Proof.lean`
     (which would duplicate $C_{\text{base}}$ $m$ times in `.olean` and multiply
     `base.toKernelEnv.replay` time by $m$), `.anneal/Proof.lean` emits a single
     shared theorem:
     ```lean
     private theorem fn_batch_valid :
         checkMultiLRAT fn_cnf fn_queries fn_cert = #[true, ..., true] := rfl
     ```
     Each obligation $k$ in `VerificationResult` projects the $k$-th entry via
     `multi_lrat_proj k fn_batch_valid`. Because `checkMultiLRAT` returns
     `Array Bool`, if obligation $k_0$ evaluates to `false` because the user
     waived it (`ob_{k_0}.id ∈ waived`) under an `alpha` policy, the remaining
     $m-1$ obligations still verify from the same shared certificate!
  2. **Pruning Dead Demonically Chosen Branches in `SmallStepMachine`:** When
     `SmallStepMachine` steps through conditional branches or
     `StepResult.externalCall`, infeasible paths have path condition
     `pre_branch q` that `MultiLRATCert` proves contradictory (`pre_branch q →
     False`), discharging `L.sem p q ≤ ...` vacuously on dead paths while
     isolating live paths for `InhabitedPre`.

---

#### 2.4 Use Case 3: `QRAT` / `FERP` Quantified Boolean Formula (QBF/DQBF) & Skolem-Function Certificate Checker

- **Engineering Problem:** Verifying $\forall \exists$ and $\exists \forall$
  properties over fixed-width state:
  1. **Hardware/MMIO Register Masks (`StepResult.externalCall`):** Proving that
     *for every* volatile read value $r_{\text{ext}}$ returned by hardware (`∀
     r_ext : BitVec 32`) satisfying a device datasheet invariant, *there exists*
     a valid next driver state transition or mask configuration (`∃ cmd :
     BitVec 32`).
  2. **Constant-Time Masking / Side-Channel Blinding:** Proving that for every
     secret key byte $k$ and every target masked intermediate byte $m$, there
     exists a blinding mask $r$ (depending only on permitted Henkin variables in
     DQBF) producing $m$ ($\forall k\; \forall m\; \exists r,\; f(k, r) = m$).
- **Untrusted Oracles:** `DepQBF` + `QRAT-trim`, `CAQE` + `CertCheck`,
  `FerpCheck`, `Pedant` (for DQBF Henkin dependencies), and `Manthan`
  (data-driven CEGAR Skolem synthesis).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/QBFCheck.lean`):**
  - **For true $\forall \vec{x}\; \exists \vec{y},\; \Phi(\vec{x}, \vec{y})$
    (and DQBF $\exists y_i(\vec{x}_{D_i})$):** A **Skolem AIG Certificate
    (`SkolemAIG`)** providing explicit boolean circuit definitions $y_i :=
    S_i(\vec{x}_{D_i})$ (where `checkDeps` syntactically verifies that circuit
    $S_i$ only reads input wires in its allowed Henkin dependency set $D_i$),
    paired with an `LRAT` unsatisfiability certificate for the quantifier-free
    substitution $\neg \Phi(\vec{x}, \vec{S}(\vec{x}))$.
  - **For false $\forall \vec{x}\; \exists \vec{y},\; \Phi(\vec{x}, \vec{y})$ or
    general $\Pi_k^P$ QBF:** A **`FERP` / `QRAT` Refutation Certificate**
    providing explicit universal expansion instances $\vec{x}^{(1)}, \dots,
    \vec{x}^{(r)}$ (or Herbrand circuits $x_j := H_j(\vec{y})$) plus an `LRAT`
    refutation of $\bigwedge_{t=1}^r \Phi(\vec{x}^{(t)}, \vec{y}^{(t)})$.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Bridging Demonic `StepResult.externalCall` to Angelic `ProductiveOn` &
    `Abstracts`:** In Anneal's `trusted/lean/` core, `StepResult.externalCall
    boundaryInv branches` introduces **demonic choice** ($\forall s' \in
    \text{branches}$), whereas `L.ProductiveOn pre prog` (`∀ q, pre q → ∃ h,
    ∃ o, (L.sem prog q).val h o`) and existential simulation witnesses in
    `Abstracts` require **angelic witness existence** ($\exists o$). A certified
    `SkolemAIG` constructively turns an existential quantifier into a computable
    total function `evalSkolem S : BVValuation → BVValuation` in `theory/`,
    supplying the exact witness `o := evalSkolem S q` without invoking
    `Classical.choice`! Dual to UNSAT `LRAT`, evaluating a concrete SAT witness
    bitvector $\vec{x}_0$ via `evalBVExpr x₀ pre == 1#1` discharges
    `InhabitedPre pre` (`∃ q, pre q`) in $O(1)$ kernel reduction steps.

---

### 3. Category 2: SMT Proof Checkers and Reconstruction Engines (Use Cases 4–7)

`Basis: documentation + source + derived`

#### 3.1 Comparative Ecosystem Analysis of Category 2 Tools

1. **SMT Proof Formats and Standalone Checkers (`Alethe`, `Carcara`,
   `Ethos`/`CPC`/`Eo`, `LFSC`/`lfscc`, `Z3` proof logs, `OpenSMT`):**
   - **`Alethe` & `Carcara`** (Schurr, Fleury, Barbosa, and Fontaine, FroCoS
     2021; Andreotti, Lachnitt, and Barbosa, CAV 2023): `Alethe` is an
     SMT-LIB-compatible proof format produced by `veriT` and `cvc5`
     (`--proof-format-mode=alethe`), combining natural-deduction `anchor`/`bind`
     subproof scopes with fine-grained resolution, congruence (`cong`), linear
     arithmetic (`la_generic`), and bitvector (`bv_bitblast`) steps. `Carcara`
     is a high-performance Rust checker and elaborator for `Alethe` that
     expands coarse solver steps into fine-grained checkable rules.
   - **`Ethos`, `Eunoia` (`Eo`), and the Cooperating Proof Calculus (`CPC`)**
     (Barbosa, Reynolds, Tinelli et al., FMCAD/TACAS 2023–2025; `cvc5/ethos`):
     `cvc5`'s native proof architecture defines its 600+ theory inference rules
     declaratively in the `Eunoia` (`Eo`) logical framework with side conditions
     executed by `Ethos`, covering strings (`QF_SLIA`), datatypes (`QF_DT`),
     bags, sets, finite fields, and bitvectors.
   - **`LFSC` (`lfscc`)** (Stump, Oe, Reynolds, Hadarean, and Tinelli, FMSD
     2013): Logical Framework with Side Conditions—a dependently typed metamodel
     with procedural side-condition code used by CVC4 and `cvc5`
     (`--proof-format=lfsc`).
   - **`Z3` Proof Logs & `OpenSMT`** (de Moura and Bjørner, TACAS 2008; Hyvärinen,
     Marescotti, Alt, Sharygina, `OpenSMT2`): `Z3` emits DAG proof objects with
     `mp`, `th-lemma`, `quant-inst`, and `hyper-res` nodes (whose `th-lemma`
     leaves often require secondary arithmetic/bitvector elaboration), whereas
     `OpenSMT` focuses on Craig interpolation and proof compression for
     propositional, `QF_UF`, `QF_LRA`, and `QF_IDL` theories.
2. **ITP Proof Reconstruction Bridges (`lean-smt`, `SMTCoq`, `Isabelle smt`,
   `lean-auto`/`Duper`):**
   - **`lean-smt`** (Mohamed, Mascarenhas, Barbosa et al., CAV/CADE;
     `ufmg-smite/lean-smt`), **`SMTCoq`** (Ekici, Mebsout, Tinelli, Keller,
     Katz, Reynolds, and Barrett, CAV 2017), and **`Isabelle smt`** (Böhme and
     Weber, ITP 2010; Blanchette, Fleury, Lachnitt, and Schurr):
     Notice the fundamental architectural divergence between **tactic-level
     term reconstruction** (`lean-smt`, `Isabelle smt`) and **computational
     reflection** (`SMTCoq`):
     - `lean-smt` and `Isabelle smt` replay each `Alethe` step by constructing
       explicit host-prover kernel `Expr` proof terms (`congrArg`, `Eq.trans`,
       `omega`, `bv_decide`). On a 30,000-step SMT proof, tactic reconstruction
       generates a multi-megabyte `Expr` term that stresses `TrustedBoundary.lean`
       (`exprEdges` and `base.toKernelEnv.replay`).
     - `SMTCoq` instead uses a **verified reflective checker** in Gallina over
       reified hash-consed term arrays, so the proof term is a single application
       of `smt_checker_sound` to `vm_compute`/`rfl`. Anneal adopts `SMTCoq`'s
       reflective architecture while engineering the data structures in `theory/`
       specifically for Lean 4's interpreted kernel Whnf reducer rather than
       Coq's VM.
   - **`lean-auto` & `Duper`** (Qian, Clune, Alexander, Bentkamp, Avigad, and
     Tinelli, ITP/CADE 2024; `leanprover-community/duper`, `lean-auto`):
     `lean-auto` monomorphizes and reifies polymorphic higher-order Lean 4 goals
     into ground first-order clauses, solved either by an external solver or by
     `Duper`, a superposition prover written in Lean 4 that reconstructs sleek
     clause-by-clause kernel resolution and paramodulation proofs.
3. **Linear, Integer, and Mixed-Integer Certifiers (`Lean 4 omega`/`linarith`,
   `Coq Micromega`, `VIPR`/`viprchk`/`SCIP-Exact`):**
   - **`Lean 4 omega` & `linarith`** (`Init.Omega` in `foundation-lock.json`)
     and **`Coq Micromega` (`lia`, `lra`, `nia`, `psatz`)** (Besson, TYPES 2006):
     Use Farkas' Lemma (non-negative linear combinations $\sum w_i c_i$), Fourier-Motzkin
     elimination, and Omega dark-shadow / cutting-plane case splits. In Coq,
     `Micromega` is a reflective certificate checker over a `Psatz` witness tree.
   - **`VIPR` (`viprchk`) & `SCIP-Exact`** (Cheung, Gleixner, and Steffy, IPCO
     2017; Cook, Koch, Steffy, and Wolter, Math. Prog. Comp. 2013; Eifler and
     Gleixner, `scipopt/scip`): The first format and checker for branch-and-cut
     Mixed-Integer Linear Programming (`MIP` / `QF_LIA`) using **exact rational
     arithmetic**, certifying optimality and infeasibility via Chvátal-Gomory
     rounding cuts, split disjunctions, and Farkas dual multipliers without
     floating-point solver unsoundness.
4. **Nonlinear Real/Integer and CAD Engines (`cvc5`/`libpoly`, `SMT-RAT`/`CArL`,
   `QEPCAD B`, `Sturm`/`Bernstein`):**
   - **`cvc5` + `libpoly`** (Jovanović and de Moura, IJCAR 2012 `nlsat`; Kremer,
     Ábrahám, Reynolds, Barbosa et al., TACAS 2022 CAD proofs),
     **`SMT-RAT` / `CArL`** (Corzilius, Kremer, Junges, Schupp, and Ábrahám,
     SAT 2015), and **`QEPCAD B`** (Brown, J. Symb. Comput. 2003): Implement
     Cylindrical Algebraic Decomposition (CAD), Virtual Substitution, and
     incremental tangent-plane linearization for `QF_NRA` and `QF_NIA`.
   - **`Sturm` & `Bernstein` Root Isolation:** Certify the sign of univariate
     and multivariate polynomials on rational intervals via Sturm remainder
     sequences (counting sign variations) and Bernstein basis expansions without
     needing the full CAD projection phase inside the trusted checker.

---

#### 3.2 Use Case 4: `Alethe` (`cvc5` / `Carcara` / `Ethos`) Proof Checker for `QF_UF + QF_AX + QF_BV`

- **Engineering Problem:** Verification conditions generated from
  `Runtime(PostCleanup)` MIR combine multiple theories simultaneously:
  1. **Uninterpreted Functions (`QF_UF`):** Abstracting pure helper calls, hash
     combinators, or opaque type projections.
  2. **Extensional Arrays (`QF_AX` / `QF_ABV`):** Modeling byte-level memory
     allocations, Rust slices `&[T]` / `&mut [T]`, and stack frames via
     McCarthy's `select(store(a, i, v), j)` read-over-write axioms.
  3. **Bitvectors (`QF_BV`):** Fixed-width pointer offsets (`usize`), niche
     discriminants, and wrapping/checked arithmetic.
- **Untrusted Oracles:** `cvc5` (`--proof-format-mode=alethe
  --proof-granularity=theory-rewrite`) elaborated by `Carcara` (or `Ethos` CPC
  logs lowered to `Alethe`).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/AletheCheck.lean`):**
  - **Hash-Consed `TermArena`:** Deeply embeds SMT terms into a flat array of
    nodes indexed by `TermId := UInt32`, so checking syntactic equality of two
    terms during `resolution`, `symm`, `trans`, or `cong` is an $O(1)$ integer
    comparison (`t1 == t2`) rather than recursive tree traversal.
  - **`AletheStep` Array:** Supports `assume`, `step` (`resolution`, `refl`,
    `symm`, `trans`, `cong`, `row1` $\text{select}(\text{store}(a,i,v),i) = v$,
    `row2` $i \neq j \implies \text{select}(\text{store}(a,i,v),j) =
    \text{select}(a,j)$, and `bv_bitblast` delegating a `QF_BV` clause to an
    embedded `LRAT` certificate from Use Case 1), and `subproof` (`anchor`/`bind`)
    frames.
  - **Soundness Theorem in `theory/`:**
    ```lean
    theorem alethe_unsat_sound (arena : TermArena) (hyps : Array TermId)
        (steps : Array AletheStep) (interp : ModelInterp arena) :
        checkAlethe arena hyps steps = true →
        (∀ h ∈ hyps, evalTerm interp h = true) → False
    ```
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Discharging `SmallStepMachine` Frame Conditions (`VerificationResult` +
    `SpecOn`):** During `EventualBehaviorOf` symbolic execution in `theory/`,
    heap and stack writes update an abstract memory map `mem : Addr → ByteVal`.
    Proving that writing to `*ptr_a` does not alias a borrowed reference
    `&*ptr_b` (`ptr_a + len_a ≤ ptr_b ∨ ptr_b + len_b ≤ ptr_a`) and therefore
    preserves all fields read through `ptr_b` is a `QF_ABV + QF_UF` obligation.
    A verified `reifyEnv : ConcreteMirState → ModelInterp arena` bridge ensures
    that `evalTerm (reifyEnv st) h` reduces definitionally (`rfl`) to the
    shallow MIR hypothesis, while storing the `Alethe` certificate as a flat
    data literal keeps `TrustedBoundary.lean`'s `exprEdges` traversal $O(1)$!

---

#### 3.3 Use Case 5: Farkas Lemma, Gomory Cut & `VIPR`/`Micromega` Branch-and-Bound Checker for `QF_LIA` / `QF_LRA`

- **Engineering Problem:** Almost every safe and `unsafe` slice, vector,
  ring-buffer, and memory-layout operation in Rust generates linear integer
  arithmetic (`QF_LIA`) obligations:
  - Slice indexing and sub-slicing: `0 ≤ start ≤ end ≤ slice.len()`, `mid =
    start + (end - start) / 2`.
  - Allocator `Layout::from_size_align_unchecked(size, align)` and
    `Layout::array::<T>(n)` bounds: `size + pad ≤ isize::MAX`.
  - DMA scatter-gather descriptor rings and packet header cursor arithmetic:
    `offset + hdr_len + payload_len ≤ packet.len()`.
- **Untrusted Oracles:** `Z3`, `cvc5`, `OpenSMT`, `SCIP-Exact` emitting `VIPR`
  branch-and-cut certificates, or Lean's `omega` pre-solver emitting `Micromega`
  / `VIPR`-style witnesses.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/LIACheck.lean`):**
  An inductive `LIACert` tree with three constructors (matching `VIPR` and
  `Micromega` `PsatzZ`):
  1. **`farkas (weights : Array Nat) (constantSlack : Nat)`:** Witnesses that the
     non-negative linear combination $\sum_i w_i \cdot (a_i \cdot \vec{x} + b_i
     \le 0)$ cancels all variable coefficients to `0` and leaves a strictly
     positive constant $c > 0$ ($c \le 0 \implies \bot$).
  2. **`cut (weights : Array Nat) (divisor : Nat) (next : LIACert)`:** A
     **Chvátal-Gomory Cutting Plane** step: verifies that $d > 0$ divides every
     combined variable coefficient $\sum_i w_i a_{i,j}$ and appends the rounded
     integer inequality $\sum_j (\frac{1}{d}\sum_i w_i a_{i,j}) x_j + \lceil
     (\sum_i w_i b_i)/d \rceil \le 0$ to the context for `next`.
  3. **`split (poly : LinearForm) (lb : Int) (left : LIACert) (right :
     LIACert)`:** Branch-and-bound / Omega dark-shadow case split on $L(\vec{x})
     \le \text{lb} \lor -L(\vec{x}) + (\text{lb} + 1) \le 0$.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **BitVec-to-Int Abstraction (`Abstracts` + `BehaviorCodec`):** Fixed-width
     `usize`/`u64` multiplication by a constant stride (`idx * sizeof::<T>()`)
     is slow in bit-blasting but instantaneous in `QF_LIA` once no-overflow side
     conditions ($0 \le x < 2^{64}$) are added as linear bounds. A verified
     `BehaviorCodec L_{\text{Int}} L_{\text{BV}}` translates `BitVec.toNat` /
     `BitVec.toInt` operations into linear integer inequalities with explicit
     wrap-around case splits.
  2. **Loop Termination Ranking Functions (`ProductiveOn`):** Proving
     `L.ProductiveOn pre prog` for a `SmallStepMachine` with `while` loops
     requires showing that a linear ranking measure $M(s) = c_0 + \sum_j c_j s_j
     \in \mathbb{Z}$ satisfies $M(s) \ge 0$ on loop entry and $M(s') \le M(s) -
     1$ across every back-edge—both discharged directly by `LIACert`.
  3. **GMP Kernel Fast Path:** Lean 4's kernel natively intercepts closed `Nat`
     operations (`Nat.add`, `Nat.mul`, `Nat.div`, `Nat.ble`) and evaluates them
     in C++/GMP in $O(1)$ steps. Normalizing `LIACert` dot products into pairs of
     `Nat` `(posSum : Nat, negSum : Nat)` instead of `Int` constructors ensures
     the entire Farkas/Gomory check runs on the GMP fast path.

---

#### 3.4 Use Case 6: `LFSC` / `Z3` Proof-Log & `lean-auto`/`Duper` Checker for Algebraic Datatypes (`QF_DT`), Byte Sequences (`QF_SLIA`), and Quantifier Instantiation (`E-matching` / `MBQI`)

- **Engineering Problem:**
  1. **Rust Algebraic Datatypes (`enum` / `struct` / `Option` / `Result`):**
     `Runtime(PostCleanup)` MIR lowers pattern matching to `SwitchInt` on
     discriminants followed by variant downcasting (`PlaceElem::Downcast`) and
     field projections (`PlaceElem::Field`). Verifying recursive or nested Rust
     types (`LinkedList`, B-Tree nodes, protocol frames) requires the theory of
     Algebraic Datatypes (`QF_DT`: constructor injectivity, variant
     disjointness, acyclicity `t ≠ C(... t ...)`).
  2. **Slices, Strings, and Sub-Sequence Slicing (`QF_SLIA`):** Verifying UTF-8
     parsers, zero-copy slice splitters (`split_at`), and ring-buffer
     concatenation (`s == s1 ++ s2`, `len(s1) == k`, `nth(s, i)`).
  3. **Quantified Specifications (`∀ i ∈ 0..n, slice[i] == 0`):** Discharging
     universal quantifiers over slice indices or collection elements.
- **Untrusted Oracles:** `cvc5` (`--proof-format=lfsc` or `alethe`), `Z3`
  (proof logs with `quant-inst` E-matching/MBQI witness nodes), and
  `lean-auto` + `Duper` (monomorphization and superposition proof search).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/QuantDTSeqCheck.lean`):**
  - **Explicit Quantifier Instantiation Witness (`InstCert`):** Records the
    exact ground terms $\vec{t}_1, \dots, \vec{t}_k$ discovered by the solver's
    E-matching, MBQI, or superposition engine for each universally quantified
    hypothesis $\forall \vec{x},\; \psi(\vec{x})$, reducing the quantified
    formula in a single linear de Bruijn substitution pass to the ground
    conjunction $\bigwedge_{j=1}^k \psi(\vec{t}_j)$.
  - **`DT` & `Seq` Axiom Schema Instances:** Explicit ground instances of
    selector-constructor inversion ($\text{sel}_i(C(x_1,\dots,x_n)) = x_i$),
    discriminant disjointness ($\text{discrim}(C_a(\dots)) \neq
    \text{discrim}(C_b(\dots))$), and sequence concatenation/length lemmas
    ($\text{len}(s_1 \mathbin{++} s_2) = \text{len}(s_1) + \text{len}(s_2)$),
    discharged at the leaves by `checkAlethe` + `checkLIACert`.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Bridging `BehaviorCodec` Representation Invariants (`obs_decodeOut`):**
    When an `unsafe` Rust data structure (e.g., an intrusive doubly-linked list
    or slice-backed `VecDeque<T>`) refines a mathematical `List α` in $L_v$,
    `BehaviorCodec.decodeOut : L_{\text{MIR}}.Out → Option L_v.Out` reconstructs
    the abstract `List α` from concrete heap memory (returning `none` if layout
    invariants fail). Proving `Abstracts L_v L_{\text{MIR}} codec v_prog
    mir_prog` requires showing that writing at `write_idx` preserves
    `nth(decode(mem'), i) = nth(decode(mem), i)` for all $i \neq
    \text{write\_idx}$. `InstCert` discharges these quantified frame conditions
    by instantiating the universal quantifier only at the concrete indices
    touched in the MIR basic blocks, completely eliminating heuristic
    E-matching from the Lean kernel.

---

#### 3.5 Use Case 7: Cylindrical Algebraic Decomposition (`CAD`), `Sturm`/`Bernstein` Root Isolation & Nonlinear Tangent Certificate Checker (`QF_NRA` / `QF_NIA`)

- **Engineering Problem:** Nonlinear arithmetic in systems Rust:
  - 2D/3D tensor and image buffer indexing (`(z * height + y) * width + x <
    total_bytes`) where `width`, `height`, and `z` are all runtime variables
    (`usize`).
  - Fixed-point Q16.16 / Q32.32 DSP scaling, hash-table load-factor capacity
    resizing (`used * denom ≤ cap * numer`), and Euclidean division/remainder
    identities (`a == (a / b) * b + (a % b)` with dynamic divisor `b`).
- **Untrusted Oracles:** `cvc5` (nonlinear incremental linearization +
  `libpoly` CAD proofs), `Z3` (`nlsat`), `SMT-RAT` / `CArL`, and `QEPCAD B`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/NLACheck.lean`):**
  1. **Incremental Linearization / Tangent-Plane & Secant Witness
     (`NIATangentCert`):** Reduces bounded `QF_NIA` obligations to `QF_LIA` by
     citing explicit instances of verified nonlinear lemma schemas:
     monotonicity ($0 \le a \le b \land 0 \le c \implies a \cdot c \le b \cdot
     c$), tangent planes ($x \cdot y \ge x_0 \cdot y + x \cdot y_0 - x_0 \cdot
     y_0$ when $(x - x_0)(y - y_0) \ge 0$), and Euclidean division bounds ($0
     \le a \bmod b < |b|$), then delegates the linearized system to
     `checkLIACert`.
  2. **Cylindrical Sample-Cell & Sturm/Bernstein Isolation Witness
     (`CADCert`):** For general polynomial inequalities $p_1(\vec{x}) \bowtie 0,
     \dots, p_m(\vec{x}) \bowtie 0$, provides a tree of cylindrical cell splits
     along rational isolating intervals $[l_k, u_k]$ verified via **Sturm
     remainder chains** or **Bernstein polynomial coefficients**, with an
     explicit rational sample point $\vec{q}_{\text{sample}}$ per cell.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Multi-Dimensional Slice & Tensor Bounds (`SpecOn` & `VerificationResult`):**
    Discharges `get_unchecked(row * stride + col)` bounds checks in matrix/ML
    kernels via a 3-line `NIATangentCert` + `Farkas` certificate.
  - **Clearing Denominators Under `foundation-lock.json`:** Because `Rat`
    (`Std.Internal.Rat`) is outside `trusted/lean/foundation-lock.json`,
    `NLACheck.lean` clears rational denominators up front into scaled
    homogeneous `Int` polynomials (or unreduced `DyadicRat := Int × Nat` with
    $q = m \cdot 2^{-e}$), avoiding Euclidean GCD reductions inside the kernel!

---

### 4. Category 3: Equality Saturation and Rewrite Certificate Checkers (Use Cases 8–10)

`Basis: documentation + source + derived`

#### 4.1 Comparative Ecosystem Analysis of Category 3 Tools

1. **Equality Saturation Engines and Proof Extraction (`egg`, `lean-egg`,
   `Tensat`, `Herbie`, `CeTA`/`IsaFoR`):**
   - **`egg` (`Explanation` / `FlatExplanation`)** (Willsey, Nandi, Wang, Flatt,
     Tatlock, and Panchekha, POPL 2021; `egraphs-good/egg`): Re-engineered
     e-graphs with amortized invariant rebuilding and e-class analyses, and
     introduced proof production (`Explanation`) that extracts a tree or flat
     sequence (`FlatExplanation`) of single-step term rewrites and congruence
     steps connecting two equivalent e-nodes after saturation.
   - **`lean-egg`** (Rossel et al., 2024; `marcusrossel/lean-egg`): Bridges Lean
     4 and `egg` by serializing Lean goals to an external `egg` process and
     reconstructing the returned `FlatExplanation` into Lean equality proofs
     (`Eq.trans`, `congrArg`).
   - **`Tensat` & `Herbie`** (Yang et al., MLSys 2021; Panchekha et al., PLDI
     2015): Apply equality saturation to tensor computation graph optimization
     (`Tensat`, extracting optimal schedules via ILP) and floating-point accuracy
     rewriting (`Herbie`), demonstrating the need for DAG-level rewrite
     certificates when shared subgraphs are transformed.
   - **`CeTA` & `IsaFoR` (`CPF`)** (Thiemann and Sternagel, CADE-22, 2009):
     The Certification Problem Format (`CPF`) and Isabelle/HOL-verified
     certifier `CeTA` validate untrusted equational, conditional, and
     orientable term-rewriting and confluence/termination proofs.
2. **Binders and Associative-Commutative (`AC`) Normalization (`slotted-egraphs`,
   `Lean 4 ac_rfl`, `AAC_tactics`):**
   - **`slotted-egraphs`** (Schneider, Kœhler, Michel, Steuwer et al., EGRAPHS /
     PLDI 2024; `memoryleak47/slotted-egraphs`): Replaces de Bruijn indices
     (which break under e-graph subgraph sharing when shifting across binders)
     with explicit named **slots** and slot bijections attached to e-class edges,
     making alpha-equivalence a zero-cost symmetry of the e-class.
   - **`Lean 4 ac_rfl`** (`Init.Data.AC` in `foundation-lock.json`) and **`Coq
     AAC_tactics`** (Braibant and Pous, CPP 2011; `coq-community/aac-tactics`):
     Normalize expressions modulo Associativity, Commutativity, and Idempotency
     (`Std.Associative`, `Std.Commutative`, `Std.IdempotentOp`). Standard
     e-graphs suffer $n! \cdot C_{n-1}$ e-node blowup on AC operators;
     reflective AC normalizers flatten AC trees into canonical lists.
3. **Relational E-Graphs and Provenance-Producing Datalog (`egglog`, `Soufflé
   --provenance`, `Ascent`):**
   - **`egglog`** (Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock, and
     Willsey, PLDI 2023; `egraphs-good/egglog`): Unifies Datalog relational
     fixpoints with equality saturation via functional dependencies over a
     relational database, allowing mutual propagation of program analysis
     relations (`Range`, `NonNull`, `Aligned`) and equational rewrites (`a = b`).
   - **`Soufflé --provenance`** (Jordan, Scholz, and Subotić, CAV 2016; Zhao,
     Subotić, and Scholz, 2020) and **`Ascent`** (Sahebolamri, Holding, and
     Rossberg, CC 2022): High-performance compiled Datalog engines (C++ and Rust
     proc-macros, respectively). `Soufflé`'s provenance tracking records minimum
     height proof trees explaining which Horn rules derived any target tuple.

---

#### 4.2 Use Case 8: `egg` / `lean-egg` / `CeTA` Linear & DAG Equational Term-Rewrite Certificate Checker

- **Engineering Problem:**
  1. Proving equivalence (`Compiles` / `Abstracts`) between a hand-optimized
     `unsafe` SIMD or bitwise Rust routine (`memchr`, `crc32`, `base64`, slice
     chunking via `as_chunks_unchecked`) and a clean, idiomatic reference
     specification.
  2. Canonicalizing tangled pointer-offset and sub-slice expressions generated
     by `rustc` `Runtime(PostCleanup)` MIR lowering (e.g.,
     `((ptr.offset(i)).offset(j)).offset(-i) == ptr.offset(j)`).
- **Untrusted Oracles:** `egg` (`Explanation` / `FlatExplanation`), `Tensat`,
  and `CeTA`/`CPF`-style rewrite trace generators.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/EqSatCheck.lean`):**
  - Instead of placing the e-graph union-find or e-matching engine inside the
    TCB, `egg` runs externally to saturation and emits a **Hash-Consed DAG
    Rewrite Trace (`Array DAGRewriteStep`)**.
  - Each `DAGRewriteStep` specifies `(ruleId : UInt16, dir : Bool, targetNode :
    NodeId, subst : Array NodeId)` or a `cong` step updating a parent DAG node's
    children to rewritten node IDs. Operating on hash-consed `NodeId`s rather
    than trees prevents exponential blowup when rewriting shared subexpressions
    (such as a 20-round ChaCha or Feistel network where tree expansion would
    have $2^{20}$ nodes!).
  - **Soundness Theorem in `theory/`:**
    ```lean
    theorem eqsat_dag_sound (rules : TheoryRules α) (arena : TermArena)
        (steps : Array DAGRewriteStep) (srcId dstId : NodeId) :
        checkDAGRewriteTrace rules arena steps srcId dstId = true →
        ∀ env, evalNode arena env srcId = evalNode arena env dstId
    ```
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Direct Realization of `Abstracts` and `Compiles` (`Language SemObs` +
    `BehaviorCodec`):** When both a specification function `spec_fn` and a
    production implementation `fast_fn` are symbolically evaluated into DAG
    terms $t_{\text{spec}}, t_{\text{fast}}$ in an expression language
    $L_{\text{Expr}}$, `eqsat_dag_sound` proves `L_{\text{Expr}}.sem t_{\text{fast}}
    = L_{\text{Expr}}.sem t_{\text{spec}}`. Composing with `Abstracts
    L_{\text{Expr}} L_{\text{MIR}} codec t_{\text{fast}} fast_fn_mir` via the
    identity codec `idCodec` on $L_{\text{Expr}}$ immediately establishes
    `Abstracts L_{\text{Expr}} L_{\text{MIR}} codec t_{\text{spec}} fast_fn_mir`
    with zero codec overhead!

---

#### 4.3 Use Case 9: `slotted-egraphs` Binder-Aware Alpha-Equivalence & `ac_rfl`/`AAC_tactics` Permutation Certificate Checker

- **Engineering Problem:**
  1. **Binder-Aware Equivalence (`Slotted E-Graphs`):** Reasoning about Rust
     closures, `Iterator::map` / `fold` / `filter` combinator pipelines, and
     loop fusion where bound variables ($\lambda i.\; \dots$) undergo
     alpha-renaming and beta-reduction.
  2. **Associative-Commutative (`AC`) Normalization:** Bitwise XOR/AND/OR masks,
     wrapping integer additions, and multiset/bag specifications of collection
     algorithms require native AC equivalence checking without $O(n^2)$ binary
     swap steps.
- **Untrusted Oracles:** `slotted-egraphs` and external AC normalizers.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/SlottedACCheck.lean`):**
  - **Slot-Bijection Steps:** Witness alpha-equivalence between binder nodes via
    an explicit finite bijection on named slot IDs.
  - **Oracle-Supplied AC Permutation Witness (`perm : Array UInt16`):** While
    `Init.Data.AC` (`foundation-lock.json` line 232) provides Lean's built-in
    `ac_rfl` normalizer (which sorts flattened AC lists inside the kernel in
    $O(N \log N)$ term comparisons), `SlottedACCheck` supports an even faster
    **Linear Permutation Witness Pattern**: the untrusted oracle flattens both
    AC trees into arrays `lhs, rhs : Array TermId` of length $N$ and emits a
    permutation index array `perm : Array UInt16` (`#[1, 3, 0, 2]`). The Lean
    kernel checker verifies in a single $O(N)$ linear pass that `perm` is a
    bijection on `0..N` and `lhs[perm[i]] == rhs[i]`!
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Iterator-to-SIMD Loop Fusion (`Compiles` / `Abstracts`):** In
    `Runtime(PostCleanup)` MIR, an iterator pipeline `slice.iter().zip(other)
    .map(|(a,b)| a ^ b).fold(0, |acc, x| acc ^ x)` lowers to a sequential
    state-machine loop, whereas a 4-lane SIMD loop accumulates four lane
    registers in parallel and XOR-reduces them at exit. Abstracting both into
    $L_{\text{Fold}}$ and checking a `SlottedACCert` proves that reordering the
    associative-commutative XOR reductions produces the exact same `SemObs`
    (`EventualOut Empty UInt64`).

---

#### 4.4 Use Case 10: Relational E-Graph (`egglog` / `Soufflé` / `Ascent`) Datalog Horn-Provenance Certificate Checker

- **Engineering Problem:** Most real-world Rust program equivalences and safety
  rewrites are **conditional** on relational dataflow facts (range bounds,
  non-nullness, alignment, disjointness, initialization):
  - Rewriting `slice.get(i).unwrap()` to `slice.get_unchecked(i)` is valid *only
    if* `InBounds(i, slice.len())` is derivable.
  - Simplifying modular arithmetic or eliminating `CheckedAdd` overflow checks
    requires mutually propagating relational Datalog facts (`Range(x, lo, hi)`,
    `Aligned(ptr, 8)`, `NonOverlapping(p1, n1, p2, n2)`) and equational rewrites
    (`a == b`), where discovering `a == b` transfers relational facts to `b`,
    unlocking further conditional rewrites.
- **Untrusted Oracles:** `egglog`, `Soufflé --provenance`, and `Ascent`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/EgglogCheck.lean`):**
  - **Topologically Sorted Horn-Provenance DAG (`Array EgglogStep`):** Every
    derived fact—either an equality `Eq(t1, t2)` or a semantic relation
    `Rel(R, args)`—is assigned a sequentially increasing `FactId := Nat` and
    cites a verified Horn rule `r : HornRuleId`, ground substitution terms
    `subst : Array TermId`, and premise fact IDs `premiseIds : Array FactId`.
  - **Strict Topological Invariant (`∀ p ∈ step.premiseIds, p < step.id`):**
    Because `TrustedBoundary.lean` (lines 314, 855) forbids `partial` functions,
    requiring `p < step.id` guarantees that the derivation graph is a DAG
    without running cycle detection, allowing `checkEgglog` to fold linearly
    over `steps` (`Array.foldl`) with trivial structural termination!
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Discharging `StepResult.externalCall` `boundaryInv = true`:** In
    `SmallStepMachine`, a MIR statement with a safety side condition or an
    external call `StepResult.externalCall (boundaryInv : Bool) branches` steps
    to `.failed .ub` if `boundaryInv` is `false`. `EgglogProvenanceCert` derives
    `Rel(BoundaryInvHolds, [state_id])` from entry preconditions and basic-block
    branch guards via mutual equality saturation and Horn deduction, reducing
    `boundaryInv` to `true` so `StepResult.externalCall` simplifies
    definitionally to `.choice .demonic branches`.

---

### 5. Category 4: Computer Algebra, Polynomial, and Cryptographic Arithmetic Certifiers (Use Cases 11–13)

`Basis: documentation + source + derived`

#### 5.1 Comparative Ecosystem Analysis of Category 4 Tools

1. **Cryptographic Algebra and Ideal-Membership Certifiers (`CryptoLine`,
   `Singular`, `PAC`/`LPAC`, `Pacheck`, `Pastèque`, `Lean 4 grind`/`polyrith`,
   `Coq ring`/`nsatz`):**
   - **`CryptoLine` + `Singular` + `Boolector`** (Fu, Tsai, Wang, Yang, and
     Bow-Yaw Wang, CCS 2019 / CAV; `fmlab-iis/cryptoline`): Verifies low-level
     cryptographic assembly and C/Rust multi-limb implementations (Curve25519,
     P-256, Bitcoin `secp256k1`, Kyber, Dilithium) by splitting verification
     into two tracks: (a) a **range/overflow track** solved by `Boolector` /
     `Bitwuzla` proving that carries and limb additions never overflow hardware
     words, and (b) an **algebraic track** solved by the `Singular` Computer
     Algebra System via Gröbner basis reduction in $\mathbb{Z}[x_1,\dots,x_n]$
     modulo the prime modulus $p$.
   - **`PAC` / `LPAC`, `Pacheck`, and `Pastèque`** (Kaufmann, Fleury, Biere, and
     Kauers, FMCAD 2020 / TACAS): The **Practical Algebraic Calculus (`PAC`)**
     and its linear-hint variant **`LPAC`** certify step-by-step polynomial
     addition, multiplication, and extension rules in $\mathbb{Z}[\vec{x}]$ (or
     $\mathbb{F}_2[\vec{x}]$ for hardware multipliers). `Pacheck` is a fast C
     checker; `Pastèque` is a formally verified checker extracted from
     Isabelle/HOL to MLton.
   - **`Lean 4 grind` (`CommRing`), `linear_combination`, `polyrith`, and `Coq
     ring`/`nsatz`** (Grégoire and Mahboubi, TPHOLs 2005): `Coq ring` and Lean
     4's `grind` normalize multivariate ring expressions into canonical Horner
     or sparse-monomial form; `nsatz` and `polyrith` query a Gröbner basis
     oracle (`Singular` / `SageMath`) for Hilbert Nullstellensatz co-factors
     $(q_1, \dots, q_m)$ such that $f - g = \sum_k q_k h_k$, reducing ideal
     membership to a single ring normalization check.
2. **Verified Bignum and Post-Quantum Cryptography Suites (`formosa-mlkem`,
   `formosa-mldsa`, `s2n-bignum`):**
   - **`formosa-mlkem` & `formosa-mldsa`** (Almeida, Barbosa, Barthe, Dupressoir,
     Grégoire, Laporte, Oliveira et al., Formosa Crypto Project): Machine-checked
     implementations of FIPS 203 (`ML-KEM` / Kyber) and FIPS 204 (`ML-DSA` /
     Dilithium) in Jasmin and EasyCrypt, verifying Cooley-Tukey /
     Gentleman-Sande Number-Theoretic Transforms (`NTT`), Montgomery reductions,
     and lazy Barrett bounds.
   - **`s2n-bignum`** (Harrison et al., AWS `awslabs/s2n-bignum`): Formally
     verified x86-64 and AArch64 multi-precision arithmetic routines proved in
     HOL Light over machine-code semantics, combining word-level symbolic
     simulation with multi-limb polynomial identities.
3. **Semidefinite Programming (`SDP`), Sum-of-Squares (`SOS`), and Primality
   Certifiers (`CSDP`, `Clarabel.rs`, `Real2RatSOS`, `RealCertify`,
   `CoqPrime` / Mathlib Pratt & Pocklington-Lehmer):**
   - **`CSDP`, `Clarabel.rs`, `Real2RatSOS`, and `RealCertify`** (Harrison, TPHOLs
     2007; Goulart and Chen, `oxfordcontrol/Clarabel.rs`; Magron and Safey El
     Din, ISSAC 2018 `RealCertify`): Numerical interior-point SDP solvers
     (`CSDP` in C, `Clarabel.rs` in pure Rust) find an approximate positive
     semidefinite Gram matrix $Q \succeq 0$ such that $P(\vec{x}) \approx
     v(\vec{x})^T Q v(\vec{x})$. `RealCertify` / Gauss-Newton rational
     projection rounds $Q$ into an exact rational matrix and computes its exact
     $L D L^T$ Cholesky decomposition, yielding an exact rational Sum-of-Squares
     identity $\sum_j c_j q_j(\vec{x})^2$ checkable by polynomial expansion.
   - **Pratt & Pocklington-Lehmer Primality Certifiers (`CoqPrime`, Isabelle
     Pratt, Mathlib `LucasLehmer`/`Pratt`):** (Théry and Grégoire, `CoqPrime`;
     Wimmer et al., Isabelle AFP): Certify primality of cryptographic moduli
     ($2^{255}-19$, $p_{\text{P256}}$, BLS12-381) via recursive prime
     factorizations of $N - 1$ (`Pratt` / `Pocklington`) in $O(\log^3 N)$ bit
     operations instead of exponential trial division.

---

#### 5.2 Use Case 11: Gröbner Basis / Hilbert Nullstellensatz & `LPAC` Ideal-Membership Certificate Checker (`Singular` / `CryptoLine` / `Pastèque`)

- **Engineering Problem:** Verifying multi-limb finite-field and big-integer
  arithmetic in production Rust cryptography crates (`curve25519-dalek`, `p256`,
  `k256`, `blstrs`, `ring`, `aws-lc-rs`):
  - A 255-bit Curve25519 field element is represented in radix-$2^{51}$ across
    five `u64` limbs $(x_0, x_1, x_2, x_3, x_4)$ using `u128` widening
    multiplies (`(a_i as u128) * (b_j as u128)`) and pseudo-Mersenne reduction
    $2^{255} \equiv 19 \pmod{2^{255}-19}$.
  - Neither bit-blasting (which times out on 25 widening 64×64-bit multipliers)
    nor linear arithmetic (`QF_LIA`) can prove that the 5-limb output $(z_0,
    \dots, z_4)$ of `fe_mul` satisfies $\sum_{i=0}^4 z_i 2^{51i} \equiv
    (\sum_{i=0}^4 a_i 2^{51i})(\sum_{j=0}^4 b_j 2^{51j}) \pmod{2^{255}-19}$.
- **Untrusted Oracles:** `CryptoLine` paired with `Singular` (computing Gröbner
  bases over $\mathbb{Z}[\vec{x}]$) and `Pacheck`/`Pastèque` (`LPAC` proof
  traces).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/PolyIdealCheck.lean`):**
  - **Explicit Co-Factor Witness (`IdealMembershipCert`):** To prove $f(\vec{x})
    \equiv g(\vec{x}) \pmod{\langle h_1(\vec{x}), \dots, h_m(\vec{x}), p
    \rangle}$ where $h_k(\vec{x}) = 0$ are the intermediate SSA carry-split
    equations ($2^{51} c_i + r_i - s_i = 0$) and $p = 2^{255} - 19$, the CAS
    emits polynomial co-factors $(q_0, q_1, \dots, q_m) \in
    (\mathbb{Z}[\vec{x}])^{m+1}$ such that:
    $$f(\vec{x}) - g(\vec{x}) = q_0(\vec{x}) \cdot p + \sum_{k=1}^m q_k(\vec{x}) \cdot h_k(\vec{x})$$
    holds as an **exact polynomial identity in $\mathbb{Z}[x_1,\dots,x_n]$**.
  - `checkIdealCert` never computes Buchberger's S-polynomials; it normalizes
    both sides into canonical sparse multivariate polynomials (`normHorner :
    PolyExpr → SparsePoly`) and checks syntactic equality `normHorner lhs ==
    normHorner rhs`!
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **Two-Stage `Abstracts` Chain (`MirLang → L_SplitInt → L_{F_p}`):**
     - Stage 1 (`Abstracts L_SplitInt L_MIR` via `BitBlastLRAT` / `LIACert`):
       Certifies that no `u64`/`u128` addition overflows and that each bit-shift
       `c_i = s_i >> 51` and mask `r_i = s_i & 0x7ffffffffffff` satisfies the
       exact integer equation $2^{51} c_i + r_i - s_i = 0$.
     - Stage 2 (`Abstracts L_{F_p} L_SplitInt` via `IdealMembershipCert`):
       Certifies the modular polynomial identity over $\mathbb{Z}[\vec{x}]$.
  2. **Crucial `BehaviorCodec` & `Language.obs` Insight for Redundant Limbs:**
     In Curve25519's radix-$2^{51}$ representation before final `freeze`,
     multiple 5-limb tuples represent the same field element in $\mathbb{F}_p$.
     Because `BehaviorCodec.decodeOut` must be injective on its `some` domain
     (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`), `L_{F_p}.Out` retains the
     full 5-limb integer tuple $(z_0,\dots,z_4)$ (making `encodeOut`/`decodeOut`
     a 1-to-1 bijection with `L_SplitInt.Out`), while `L_{F_p}.obs : Out →
     SemObs` projects $(z_0,\dots,z_4) \mapsto (\sum_{i=0}^4 z_i 2^{51i}) \bmod
     p \in \mathbb{F}_p$! This directly validates why `Language SemObs`
     separating `Out` from `SemObs` via `obs : Out → SemObs` is indispensable.

---

#### 5.3 Use Case 12: Number-Theoretic Transform (`NTT`) & Ring-Polynomial Equivalence Certifier for Post-Quantum Cryptography (`ML-KEM` & `ML-DSA`)

- **Engineering Problem:** Post-Quantum Cryptography (FIPS 203 `ML-KEM` / Kyber
  with $q = 3329, n = 256$ and FIPS 204 `ML-DSA` / Dilithium with $q = 8380417,
  n = 256$) relies on in-place Cooley-Tukey and Gentleman-Sande `NTT` /
  `InvNTT` butterfly loops with Montgomery reductions (`fqmul`) over $R_q =
  \mathbb{Z}_q[X]/(X^{256}+1)$ and lazy Barrett reductions across layers.
- **Untrusted Oracles:** `CryptoLine` + `Singular` + `formosa-mlkem` /
  `formosa-mldsa` layer invariants.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/NTTCertCheck.lean`):**
  - **`NTTLayerCert`:** Decomposes the 7-layer (Kyber) or 8-layer (Dilithium)
    in-place transform into per-layer certificates, each containing:
    1. **Index Partition Bijection (`perm : Array UInt16`):** Certifies that for
       stride $len \in \{128, 64, \dots, 2\}$, the index pairs $(j, j + len)$
       partition $\{0, \dots, 255\}$ into 128 disjoint butterfly pairs (proving
       in-place slice mutation safety).
    2. **Montgomery CRT Butterfly Identity:** An `IdealMembershipCert` +
       `LIACert` proving that $(a + \text{fqmul}(b, \zeta),\, a - \text{fqmul}(b,
       \zeta))$ implements the Chinese Remainder Theorem isomorphism
       $\mathbb{Z}_q[X]/(X^{2m} - \psi^2) \xrightarrow{\sim}
       \mathbb{Z}_q[X]/(X^m - \psi) \times \mathbb{Z}_q[X]/(X^m + \psi)$ and
       keeps `i16` coefficient magnitudes within $[-9q, 9q]$ prior to Barrett
       reduction.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Compositional 7/8-Stage `Compiles` Chain (`Language SemObs`):** Unrolling
    all 256×7 = 1,792 Montgomery butterflies into a single monolithic polynomial
    certificate would cause superlinear certificate blowup. Modeling each NTT
    stage $s \in \{0,\dots,6\}$ in $L_{\text{PolyArray}}$ and proving
    `Compiles L_{\text{PolyArray}} L_{\text{PolyArray}} idCodec spec_stage_s
    impl_stage_s` composes the 7 stages by transitivity of behavioral refinement
    (`≤`) in $O(7)$ kernel steps!

---

#### 5.4 Use Case 13: Positivstellensatz (Sum-of-Squares `SOS` / SDP) & Pocklington / Pratt Primality Certificate Checkers

- **Engineering Problem:**
  1. **Universal Nonlinear Polynomial Inequalities (`Positivstellensatz` /
     `SOS`):** Proving $P(\vec{x}) \ge 0$ on a semialgebraic set $\{g_1(\vec{x})
     \ge 0, \dots, g_m(\vec{x}) \ge 0\}$ (e.g., quadratic/cubic Lyapunov barrier
     functions $V(s) - V(s') \ge \epsilon \|s\|^2$ in robotics/control Rust code
     or elliptic-curve non-degeneracy).
  2. **Primality Certificates for Cryptographic Moduli (`Pratt` /
     `Pocklington`):** In Use Cases 11–12, field inversion via Fermat's Little
     Theorem ($a^{p-2} \bmod p = a^{-1}$) requires a kernel-checked theorem
     `Prime p` for 255-bit to 381-bit primes ($p = 2^{255}-19$, $p_{\text{P256}}$,
     BLS12-381), where trial division up to $\sqrt{p} \approx 2^{127.5}$ is
     infeasible.
- **Untrusted Oracles:** `CSDP`, `Clarabel.rs`, and `RealCertify` (for rational
  $L D L^T$ SOS certificates); `PARI/GP`, `Primo`, and `CoqPrime`-style
  generators (for Pocklington-Lehmer / Pratt primality trees).
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/SOSAndPrimeCheck.lean`):**
  1. **`SOSCert`:** Represents $d^2 \cdot P(\vec{x}) - \sum_i \sigma_i(\vec{x})
     g_i(\vec{x}) = \sum_{j=1}^r c_j \cdot q_j(\vec{x})^2$ with cleared integer
     denominator $d > 0$, non-negative integer weights $c_j \ge 0$, and integer
     polynomials $q_j(\vec{x}) \in \mathbb{Z}[\vec{x}]$, checked via
     `normHorner`.
  2. **`PrimalityCert` (Pocklington-Lehmer Tree):** Certifies $N > 1$ is prime
     via a primitive root witness $a \in \mathbb{N}$ and a partial prime
     factorization $F = \prod_{i=1}^k p_i^{e_i}$ of $N - 1$ with $F^2 > N$
     (each $p_i$ recursively certified by a child `PrimalityCert`) such that
     $a^{N-1} \equiv 1 \pmod N$ and $\forall i,\; \gcd(a^{(N-1)/p_i} - 1, N) =
     1$.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **Discharging Type-Level `Prime p` in $L_{\mathbb{F}_p}$ and Nonlinear
     Lyapunov Ranking in `ProductiveOn`:** `checkPocklington_sound` proves
     `Prime (2^255 - 19)` via `rfl` with zero cryptographic axioms in
     `foundation-lock.json`, while `checkSOSCert_sound` discharges polynomial
     ranking decreases $V(s) - V(s') - 1 \ge 0$ for `L.ProductiveOn pre prog`.
  2. **Structural Binary-Fuel `powMod` for GMP Kernel Speed:** In
     `Init.Data.Nat.Div.Basic` (`foundation-lock.json` line 447), `n / 2` uses
     well-founded recursion (`WellFounded.fix`), which can unfold accessibility
     proofs during kernel reduction. Defining `powMod (base exp mod fuel : Nat)`
     by primitive structural recursion (`Nat.rec`) on `fuel := 256` evaluates
     256-bit modular exponentiation in $< 200$ GMP `Nat.mul` / `Nat.mod` calls
     ($\sim 1\text{ ms}$ in the Lean kernel)!

---

### 6. Category 5: Floating-Point and Real-Arithmetic Error-Bound Certifiers (Use Cases 14–15)

`Basis: documentation + source + derived`

#### 6.1 Comparative Ecosystem Analysis of Category 5 Tools

1. **IEEE-754 Rounding-Error Analyzers and Formalizations (`Gappa`, `FPTaylor`,
   `Flocq`, `VCFloat2`):**
   - **`Flocq`** (Boldo and Melquiond, IEEE Trans. Computers 2011 / Book 2017):
     The foundational Coq formalization of multi-radix, multi-precision IEEE-754
     floating-point arithmetic (formats `FLT`, `FIX`, `FLX`, generic rounding
     modes, ulp/error theorems), which also inspired SMT-LIB `QF_FP` and C/Rust
     floating-point verification models.
   - **`Gappa`** (Daumas and Melquiond, ACM TOMS 2010): Standalone C++ interval
     and forward/backward error-propagation engine over dyadic rationals ($m
     \cdot 2^e$) that bounds rounding errors of straight-line numerical code and
     emits machine-checkable proof scripts for Coq/`Flocq`.
   - **`FPTaylor`** (Solovyev, Baranowski, Briggs, Jacobsen, Rakamarić, and
     Gopalakrishnan, ACM TOPLAS 2018; `soarlab/FPTaylor`): Uses **Symbolic
     Taylor Forms** (first-order Taylor expansion with respect to per-operation
     rounding variables $e_i \in [-\varepsilon, +\varepsilon]$) plus branch-and-bound
     global optimization to achieve tighter bounds than naive interval arithmetic
     (avoiding the interval dependency problem on correlated expressions like
     $x / (x + 1)$).
   - **`VCFloat2`** (Appel and Kellison, CPP 2024; `VeriNum/vcfloat`): Automates
     round-off error verification inside Coq over `Flocq` using reflective
     abstract syntax trees and interval/derivative bounds.
2. **Transcendental Function, Taylor-Model, and Minimax Polynomial Certifiers
   (`Sollya`, `CoqInterval`, `PVS Bernstein`, `MetiTarski`):**
   - **`Sollya`** (Chevillard, Joldeş, and Lauter, ICMS 2010; `sollya.org`):
     Interactive environment and C library for developing `libm` mathematical
     functions, computing Remez minimax polynomials (`fpminimax`), lattice-reduction
     (`LLL`) floating-point coefficient rounding, and validated supremum norms
     (`infnorm` / `checkinfnorm` $|f(x) - p(x)| \le \varepsilon$).
   - **`CoqInterval`** (Melquiond, IJCAR 2008 / `coq-interval`): Reflective Coq
     tactic using **Rigorous Taylor Models** (polynomial approximation +
     interval remainder) and multi-precision dyadic floating-point intervals to
     certify bounds on expressions containing $\sin, \cos, \exp, \ln, \arctan,
     \sqrt{\cdot}$.
   - **`PVS Bernstein` & `MetiTarski`** (Muñoz and Narkawicz, J. Autom. Reason.
     2013; Akbarpour and Paulson, J. Autom. Reason. 2010): `PVS Bernstein`
     certifies multivariate polynomial optimization via Bernstein basis
     subdivision, while `MetiTarski` proves universal inequalities over real
     transcendental functions by bounding them between rational/polynomial upper
     and lower envelopes and invoking `QEPCAD B` / `Z3`.

---

#### 6.2 Use Case 14: `Gappa` / `FPTaylor` / `Flocq` / `VCFloat2` IEEE-754 Rounding-Error & Forward/Backward Range Certificate Checker

- **Engineering Problem:** Verifying Rust numerical, audio/DSP, robotics,
  graphics, and ML inference code operating on `f32` and `f64`:
  1. **Absence of `NaN` and `±Infinity` (`x.is_finite()`):** Required before
     calling `unsafe { f32::to_int_unchecked::<i32>(x) }` (which is immediate
     Undefined Behavior in Rust if `x` is `NaN`, `±Inf`, or outside
     `[i32::MIN..i32::MAX]` after truncation!).
  2. **Quantitative Rounding-Error Bounds:** Proving that a quantized ML kernel
     (`fp16`/`bf16`/`f32` dot product or Softmax) or biquad IIR filter stays
     within a certified absolute/relative error $|\text{fl}(E(\vec{x})) -
     E_{\mathbb{R}}(\vec{x})| \le \varepsilon$ of the ideal real-valued formula
     $E_{\mathbb{R}}(\vec{x})$ for all inputs $\vec{x} \in \prod_i [a_i, b_i]$.
- **Untrusted Oracles:** `Gappa` and `FPTaylor`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/GappaCheck.lean`):**
  - Built on top of a pure, bit-exact IEEE-754 binary32/binary64 formalization
    in `theory/` using exact dyadic rationals `Dyadic := Int × Int` ($m \cdot
    2^e$, requiring zero axioms outside `Init.*`).
  - **`GappaCert`:** A DAG of dyadic interval and Taylor-error deduction steps:
    - `BND(e, [l, u])` (certified enclosure $l \le e \le u$), `ABS(e, [l, u])`,
      `FIX(e, k)` (least significant bit weight $2^k$), `FLT(e, p)` ($p=24$ for
      `f32`, $p=53$ for `f64$), and `REL(e, r, [l, u])`.
    - Inference rules: IEEE-754 single-operation rounding theorems
      (`add_round_nearest_even`, `mul_subnormal_bound`, Sterbenz's exact
      subtraction lemma when $\frac{1}{2} \le \frac{y}{x} \le 2$), first-order
      Taylor error summation (`FPTaylor` forms), and **recursive interval
      bisection trees** subdividing $[a, b]$ into $2^d$ sub-intervals.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **Discharging `float_to_int_unchecked` UB Obligations (`VerificationResult`
     + `SpecOn`):** `checkGappaCert` proves `BND(x_f32, [-2147483520.0,
     2147483520.0])` and `¬isNaN(x_f32)`, discharging the UB guard of
     `core::intrinsics::float_to_int_unchecked` and proving that nondeterministic
     IEEE-754 `NaN`-payload branches (Rust RFC 3514) are unreachable.
  2. **Quantitative $\varepsilon$-Refinement via `Language SemObs` &
     `Abstracts`:** How does Anneal express "the concrete `f32` Rust function
     approximates the ideal real specification $f_{\mathbb{R}} : \mathbb{R}^n
     \to \mathbb{R}$ within $\varepsilon$" without adding metric spaces to
     `trusted/lean/`? In $L_{\text{RealBall}}$ (the Real Enclosure Language), a
     specification program `v` maps query $q$ to the **nondeterministic set of
     all floating-point outcomes within $\varepsilon$ of $f_{\mathbb{R}}(q)$**:
     $$L_{\text{RealBall}}.\text{sem}\; v\; q := \text{defined},\quad o \in (L_{\text{RealBall}}.\text{sem}\; v\; q).\text{val} \iff |\text{toDyadic}(o) - f_{\mathbb{R}}(q)| \le \varepsilon$$
     Because `Abstracts L_{\text{RealBall}} L_{\text{MIR}} codec v s` is
     `L_{\text{MIR}}.sem s ≤ codec.toMorphism (L_{\text{RealBall}}.sem v)`
     (refinement = subset of allowed outcomes!), the deterministic `f32` result
     $o_{\text{mir}}$ refines `v` if and only if $|\text{toDyadic}(o_{\text{mir}})
     - f_{\mathbb{R}}(q)| \le \varepsilon$!

---

#### 6.3 Use Case 15: Taylor-Model & Chebyshev / Remez Polynomial Enclosure Certifier (`Sollya` / `CoqInterval` / `PVS Bernstein`)

- **Engineering Problem:** Verifying pure-Rust mathematical libraries (`libm`,
  `core_math`, `sleef-rs`, fixed-point DSP lookup tables) that implement
  transcendental functions (`expf`, `logf`, `sinf`, `cosf`, `atan2f`, `cbrtf`,
  `erff`) using Cody-Waite range reduction and minimax Remez polynomial
  approximations. Proving that `libm::sinf(x)` is faithful ($< 0.501\text{ ULP}$)
  or correctly rounded ($< 0.5\text{ ULP}$) on $[-\pi/4, \pi/4]$ requires
  bounding both:
  1. **Method / Truncation Error:** $|\sin(x) - P_{\text{Remez}}(x)| \le
     \varepsilon_{\text{method}}$ for all $x \in [-\pi/4, \pi/4]$, and
  2. **Evaluation Rounding Error:** $|\text{fl}_{\text{FMA}}(P_{\text{Remez}}(x))
     - P_{\text{Remez}}(x)| \le \varepsilon_{\text{round}}$ (Use Case 14).
- **Untrusted Oracles:** `Sollya` (`fpminimax`, `infnorm`, `checkinfnorm`),
  `CoqInterval` Taylor model generators, and `PVS Bernstein` / `MetiTarski`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/TaylorModelCheck.lean`):**
  - **Taylor Model of Order $d$ (`TM d`):** Represents a $C^{d+1}$ elementary
    function $f(x)$ on dyadic interval $I = [a, b]$ by a degree-$d$ dyadic
    polynomial $T_d(x) = \sum_{k=0}^d c_k (x - x_0)^k$ plus a certified Lagrange
    remainder interval $\Delta = [\underline{\delta}, \overline{\delta}]$ where
    $\forall x \in I,\; f(x) - T_d(x) \in \Delta$.
  - **Bernstein Basis Supremum Witness:** Transforms the difference polynomial
    $D(x) = T_d(x) - P_{\text{Remez}}(x)$ on $[a, b]$ into the **Bernstein
    basis** $\sum_{i=0}^d b_i B_{i,d}(\frac{x-a}{b-a})$ (verified via
    `normHorner` polynomial identity). By the Bernstein convex-hull property,
    $\min_i b_i \le D(x) \le \max_i b_i$ for all $x \in [a, b]$, so checking
    $\max_{x \in [a,b]} |D(x)| \le \varepsilon_{\text{poly}}$ reduces to checking
    $d+1$ dyadic inequalities $-\varepsilon_{\text{poly}} \le b_i \le
    +\varepsilon_{\text{poly}}$!
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Constructive Transcendental Specifications Without `Mathlib`'s Classical
    `Real`:** Because `trusted/lean/foundation-lock.json` locks only `Init.*`
    (no Cauchy/Dedekind reals), `theory/` defines elementary functions
    ($\sin_{\mathbb{Q}}(x, k), \exp_{\mathbb{Q}}(x, k), \ln_{\mathbb{Q}}(x, k)$)
    constructively as **convergent alternating/geometric Taylor interval
    enclosures** over `DyadicInterval`. `TaylorModelCert` proves that for every
    `f32` input $x$ and every precision order $k$, `libm::sinf(x)` refines the
    $(\varepsilon_{\text{method}} + \varepsilon_{\text{round}})$-ball around
    $\sin_{\mathbb{Q}}(x, k)$ via `Abstracts` and `ProductiveOn`.

---

### 7. Category 6: Model Checking, CHC, and Automata Certificate Checkers (Use Cases 16–18)

`Basis: documentation + source + derived`

#### 7.1 Comparative Ecosystem Analysis of Category 6 Tools

1. **Bit-Level and Word-Level IC3/PDR Model Checkers and Witness Checkers
   (`Certifaiger`, `ABC`, `btormc`, `AVR`, `Pono`):**
   - **`ABC` (`pdr`) & `btormc`** (Brayton and Mishchenko, CAV 2010; Bradley,
     VMCAI 2011 IC3; Niemetz, Preiner, Wolf, and Biere, CAV 2018 `btormc`):
     Bit-level (`AIGER`) and word-level (`BTOR2`) hardware model checkers using
     Property-Directed Reachability (`IC3`/`PDR`) and bounded/unbounded
     $k$-induction.
   - **`AVR` & `Pono`** (Goel and Sakallah, TACAS 2020 `AVR`; Mann, Irfan,
     Lonsing, Yang, Zhang, Brown, Gupta, and Barrett, CAV 2021 `Pono`):
     Word-level SMT model checkers combining syntax-guided abstraction
     refinement (`AVR`), IC3ia (implicit predicate abstraction), and
     interpolation over `QF_BV`, `QF_ABV`, and `QF_LIA`.
   - **`Certifaiger`** (Froleyks, Yu, Biere, and Heljanko, FMCAD/CAV 2021–2024;
     `Froleyks/certifaiger`): The standard witness checker for the Hardware
     Model Checking Competition (`HWMCC`). Given a sequential circuit $M$ and an
     inductive witness circuit $W$ discovered by IC3/PDR, `Certifaiger` generates
     combinational miter circuits for initiation, inductiveness, and safety, and
     certifies each miter via `CaDiCaL` + `LRAT`/`cake_lpr`.
2. **Constrained Horn Clause (`CHC`) Solvers (`Z3 Spacer`, `Eldarica`,
   `Golem`):**
   - **`Z3 Spacer`** (Komuravelli, Gurfinkel, and Chaki, CAV 2014 / FMSD 2016):
     The default CHC engine in `Z3` (powering `SeaHorn`, `JayHorn`, and
     `RustHorn`), extending IC3/PDR to nonlinear Horn clauses with
     under-approximating summaries, Model-Based Projection (`MBP`), and global
     guidance.
   - **`Eldarica`** (Hojjat and Rümmer, FMCAD 2018; `uuverifiers/eldarica`):
     Scala-based CHC solver using predicate abstraction, Craig interpolation over
     Presburger arithmetic and algebraic datatypes, and acceleration of
     counter-machine loops.
   - **`Golem`** (Blicha, Britikov, Hyvärinen, and Sharygina, CAV 2023;
     `usi-verification-and-security/golem`): Modular C++ CHC solver built on
     `OpenSMT` implementing `Spacer`, Transition Power Abstraction (`TPA` for
     deep multi-step loop invariants), and explicit witness validation (`--validate`).
3. **Automata, LTL Model Checking, and Termination Certifiers (`Mata`/`Vata`,
   `SPOT`, `CAVA`, `Ultimate Automizer`, `T2`):**
   - **`Mata` & `Vata`** (Chocholatý, Fiedor,Holík, Lengál, and Síč, TACAS
     2024 `Mata`; Lengál, Šimáček, and Vojnar, TACAS 2012 `Vata`): High-speed
     explicit/symbolic NFA, DFA, and tree-automata libraries used for regular
     model checking, string constraints (`QF_SLIA`), and Hopcroft-Karp
     antichain/bisimulation language inclusion.
   - **`SPOT` & `CAVA`** (Duret-Lutz et al., ATVA 2016 / CAV 2022 `SPOT`;
     Esparza, Lammich, Neumann, Nipkow, Schimpf, and Smaus, CAV 2013 `CAVA`):
     `SPOT` translates LTL/$\omega$-automata with acceptance parity/Büchi
     conditions; `CAVA` is a full LTL model checker formally verified in
     Isabelle/HOL.
   - **`Ultimate Automizer` & `T2`** (Heizmann, Hoenicke, and Podelski, POPL
     2013 / TACAS `Ultimate Automizer`; Cook, Podelski, and Rybalchenko, PLDI
     2006 `Terminator` / `T2`): Verify software safety and termination/liveness
     by decomposing traces into Buchi automata of Floyd-Hoare interpolants and
     certifying termination via lexicographic or disjunctive ranking functions.

---

#### 7.2 Use Case 16: `Certifaiger` / `IC3` (`PDR`) Inductive Clause & $k$-Induction Certificate Checker (`AVR` / `Pono` / `ABC` / `btormc`)

- **Engineering Problem:** Verifying unbounded loops and stateful event loops in
  Rust where the developer writes only the function postcondition—or writes
  *zero* annotations and relies on Anneal's always-on UB-freedom check
  (`PRINCIPLES.md`):
  - Stateful ring-buffer consumers/producers, DMA state machines, streaming
    parsers, and network protocol connection handlers where a safety property
    $P(s)$ (e.g., `head ≤ tail ∧ tail - head ≤ cap`) is not 1-inductive on its
    own and requires auxiliary strengthened clauses $F_m$ discovered by
    `IC3`/`PDR` or $k$-step unrolling ($k$-induction).
- **Untrusted Oracles:** `btormc`, `AVR`, `Pono`, and `ABC` (`pdr`) paired with
  `Certifaiger`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/IC3Check.lean`):**
  Once `IC3`/`PDR` converges at frame $F_m = F_{m+1}$, the entire multi-frame
  clause-pushing search trace is discarded. The certificate `IC3Cert` contains
  only:
  1. **Strengthened Inductive Invariant Formula $I(s) = \bigwedge_{i=1}^r
     C_i(s)$** (or $k$-step invariant + witness circuit latches $W$).
  2. **Three Ground UNSAT Certificates (`LRAT` or `Alethe` + `LIACert`):**
     - `cert_init`: Witnesses $\text{Init}(s_0) \land \neg I(s_0) \vdash \bot$.
     - `cert_ind`: Witnesses $I(s) \land \text{Step}(s, s') \land \neg I(s')
       \vdash \bot$ (or $k$-step inductiveness $\bigwedge_{j=0}^{k-1} (I(s_j)
       \land \text{Step}(s_j, s_{j+1})) \land \neg I(s_k) \vdash \bot$).
     - `cert_safe`: Witnesses $I(s) \land \text{IsUB}(\text{step}(s)) \vdash
       \bot$.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Direct Coupling to `SmallStepMachine` and `EventualBehaviorOf`:** In
    `trusted/lean/Trusted/StepResult.lean`, `EventualBehaviorOf` defines the
    behavior of a `SmallStepMachine` over unbounded traces (`.terminated trace
    term | .diverges`). A single generic metatheorem
    `SmallStepMachine.k_induction_safety` in `theory/` proves that if $I :
    \text{State} \to \text{Prop}$ satisfies `cert_init`, `cert_ind`, and
    `cert_safe`, then `EventualBehaviorOf M s₀` is `defined` (UB-free across all
    finite prefixes) for both terminating (`.terminated`) and intentionally
    diverging (`.diverges`, e.g., embedded `loop {}` firmware) executions!

---

#### 7.3 Use Case 17: Constrained Horn Clause (`CHC`) Relational Invariant & Resolution-DAG Certifier (`Z3 Spacer` / `Eldarica` / `Golem`)

- **Engineering Problem:** Verifying **inter-procedural** and **mutually
  recursive** Rust functions, nested loops, and Ghost-state mutable-borrow
  prophecy invariants (`RustHorn` / `SeaHorn` style):
  - When a Rust function borrows `&mut T`, passes a sub-borrow `&mut U` to a
    helper function or loop, and restores the outer type's representation
    invariant (`AdtInv`) when the borrow expires, the verification problem across
    procedures forms a system of **Constrained Horn Clauses (CHCs)**:
    $$\forall \vec{x},\quad P_1(\vec{x}_1) \land \dots \land P_k(\vec{x}_k) \land \phi_{\text{body}}(\vec{x}) \implies H(\vec{x}_0)$$
    where $P_i, H$ are unknown relational predicates representing loop invariants
    and function pre/post summaries.
- **Untrusted Oracles:** `Z3 Spacer`, `Eldarica`, and `Golem`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/CHCCheck.lean`):**
  - **Symbolic Relational Model (`CHCModel`):** Explicit closed-form logical
    formulas $\mathcal{M}(P_i)(\vec{v})$ for every unknown predicate symbol
    $P_i$ in the CHC system.
  - **Per-Clause Entailment Certificates (`Array ClauseCert`):** For each Horn
    clause $c_j$, a ground SMT certificate (`Alethe` + `LIACert` +
    `BitBlastLRAT`) proving that substituting $\mathcal{M}(P_i)$ into $c_j$
    yields a valid formula ($\neg c_j[\mathcal{M}] \vdash \bot$).
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Modular Inter-Procedural Summaries via `StepResult.externalCall` &
    `SpecOn`:** Each interpreted predicate $\mathcal{M}(P_f)(\text{args},
    \text{ret})$ defines the modular contract `SpecOn pre_f post_f` of helper
    function $f$. At each call site `StepResult.externalCall boundaryInv
    branches`, the caller's CHC clause certifies `boundaryInv = true` (`pre_f`
    holds) and assumes `post_f` on the demonic return `branches`, while callee
    $f$'s CHC clause certifies that $f$'s body satisfies `SpecOn pre_f post_f`.

---

#### 7.4 Use Case 18: Hopcroft-Karp Bisimulation, Transducer Equivalence & Büchi Lexicographic Ranking Certificate Checker (`Mata` / `SPOT` / `T2`)

- **Engineering Problem:**
  1. **Regex, Lexer & Protocol State-Machine Equivalence (`Hopcroft-Karp`):**
     Crates like `regex-automata`, `aho-corasick`, `logos`, `nom`, and
     HTTP/TLS/QUIC frame parsers compile declarative NFAs/DFAs into dense
     lookup-table or SIMD state machines. We must prove that the table-driven
     Rust state machine accepts the exact same byte streams and emits the exact
     same token spans (`trace : List Obs`) as the reference specification.
  2. **Liveness and Termination of Multi-Phase State Machines (`Büchi` /
     Lexicographic Ranking):** Proving `ProductiveOn` (termination without
     infinite stuttering) when no single linear measure decreases on every step.
- **Untrusted Oracles:** `Mata` / `Vata`, `SPOT` / `CAVA`, `Ultimate Automizer`,
  and `T2`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/AutomataRankCheck.lean`):**
  1. **Bisimulation Relation Witness (`BisimCert`):** A finite array of state
     pairs $R \subseteq Q_1 \times Q_2$ containing $(q_{1,\text{init}},
     q_{2,\text{init}})$ plus a pre-indexed transition lookup table `nextPairIdx :
     Array (Array UInt16)` of size $|R| \times 256$. `checkBisimCert` verifies in
     $O(|R| \times |\Sigma|)$ array lookups (without running union-find in the
     kernel) that every pair $(q_1, q_2) \in R$ has matching outputs and steps to
     `(q_1', q_2') = R[nextPairIdx[p][a]]` on every byte $a \in [0, 255]$.
  2. **Lexicographic Ranking Certificate (`LexRankCert`):** A tuple of integer
     ranking expressions $(r_1(s), \dots, r_d(s))$ plus per-back-edge `LIACert`
     proofs witnessing which component $k \in \{1,\dots,d\}$ strictly decreases
     ($r_k(s') \le r_k(s) - 1, r_k(s) \ge 0$) while $r_j(s') \le r_j(s)$ for all
     $j < k$, lifted via `Prod.Lex` in `Init.WF` (`foundation-lock.json` line
     786).
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  - **Trace Equality over `EventualOut` (`trace : List Obs`):** Exercises the
    observation trace spine `SemObs := EventualOut Obs Unit` in
    `EventualOut.terminated (trace : List Obs) (term : Terminal Val)`:
    `checkBisimCert_sound` proves bilateral `Compiles L₁ L₂ codec M₁ M₂` and
    `Compiles L₂ L₁ codec⁻¹ M₂ M₁`, while `checkLexRankCert_sound` rules out
    `EventualOut.diverges` to establish `L.ProductiveOn pre prog`.

---

### 8. Category 7: SyGuS/LLM Candidate Synthesis and Bootstrapped Native Checkers (Use Cases 19–20)

`Basis: documentation + source + derived`

#### 8.1 Comparative Ecosystem Analysis of Category 7 Tools

1. **Syntax-Guided Synthesis (`SyGuS`), Superoptimizers, and LLM-Guided
   Invariant Synthesizers (`cvc5 SyGuS`, `Souper`, `Alive2`, `LEMUR`, `Loopy`):**
   - **`cvc5 SyGuS`** (Reynolds, Barbosa, Nötzli, Barrett, and Tinelli, CAV
     2019): Enumerative and CEGIS (Counterexample-Guided Inductive Synthesis)
     solver for `--lang=sygus2`, synthesizing loop invariants, Skolem functions,
     and bitvector expressions that satisfy an SMT specification.
   - **`Souper` & `Alive2`** (Sasnauskas, Chen, Collingbourne, Ketema, Lup,
     Taneja, and Regehr, `google/souper`; Lopes, Lee, Hur, Liu,Alive2 PLDI
     2021): Synthesize (`Souper`) and translation-validate (`Alive2`) LLVM IR
     peephole optimizations over bitvectors, `poison`, and `undef` using
     `Z3`/`Bitwuzla`.
   - **`LEMUR` & `Loopy`** (Wu, Barrett, and Narodytska, ICLR 2024 `LEMUR`;
     Kamath et al., 2024 `Loopy`): Combine Large Language Models with SMT/CHC
     model checkers in a guess-and-check / backtracking loop where the LLM
     proposes candidate loop invariants, helper contracts, or ranking functions
     and the verifier either certifies them or returns concrete counterexample
     states.
2. **Formally Verified Native SAT Checkers and Parallel DAG Proof Splitters
   (`CreuSAT`, `cake_lpr` bootstrap, `ParaDRAT`):**
   - **`CreuSAT`** (Skotåm, Master's Thesis, Univ. of Oslo 2022;
     `sarsko/CreuSAT`): A CDCL SAT solver with two-watched literals and conflict
     analysis written in safe Rust and formally verified using **Creusot**
     (Why3), demonstrating that high-performance SAT/LRAT engines can be written
     and verified directly in Rust.
   - **`ParaDRAT` / DAG Cut Splitting** (Heule, Biere, Lammich et al.): Splits
     multi-gigabyte SAT proofs into independent sub-proofs along clause
     dominators/cuts so chunks can be checked in bounded memory or in parallel.

---

#### 8.2 Use Case 19: `cvc5 SyGuS`, `Souper`/`Alive2` & `LEMUR`/`Loopy` LLM Candidate Invariant / Ranking / Bit-Hack Certifier

- **Engineering Problem:**
  1. **Zero-Annotation Loop Invariant & Contract Synthesis:** Upholding
     `PRINCIPLES.md` (*"without obliging Rust developers to learn Lean 4"*) when
     verifying loops with complex data-structure or nonlinear invariants where
     unassisted `IC3`/`CHC` times out.
  2. **Bit-Hack & Peephole Synthesis (`Souper` / LLM):** Proposing a branchless
     bit-manipulation routine and certifying its equivalence to a reference spec.
- **Untrusted Oracles:** Frontier LLMs (Gemini / `LEMUR` / `Loopy` CEGIS loops),
  `cvc5 --lang=sygus2`, and `Souper`.
- **Formal Certificate Format & TCB (`theory/Anneal/Solv/SyGuSCheck.lean`):**
  - **`SyGuSCert`:** Packages the synthesizer's untrusted candidate ASTs
    (`candInv : Formula`, `candRank : Array LinearForm`, `candExpr : BVExpr w`)
    together with standard `LRAT`, `Alethe`, `LIACert`, or `IdealMembershipCert`
    proofs that the candidates satisfy initiation, inductiveness, safety, and
    termination.
- **Exact Mapping onto Anneal's 4 `trusted/` Primitives:**
  1. **Adversarial-Oracle Sandbox (`TrustedBoundary.lean`):** Even if an LLM
     synthesizes `.anneal/Proof.lean` directly, `TrustedBoundary.lean` enforces
     closed `commandKinds` and `allowedAttributeNames` in Phase 1 (`"preflight"`)
     and checks exact `Proof.verify_crate : Trusted.CrateTheorem Mir.crate` type
     equality, axiom closure (`{Classical.choice, Quot.sound, propext}`), and
     clean kernel replay (`base.toKernelEnv.replay locals`) in Phase 2
     (`"audit"`). A hallucinated candidate invariant simply fails `rfl`
     typechecking with zero soundness risk.
  2. **Counterexample Execution for Rust-Style Diagnostics (`PRINCIPLES.md`):**
     When a candidate or program assertion is *false*, the SAT/SMT oracle emits a
     concrete counterexample valuation `SATValuation`. Stepping `SmallStepMachine`
     concretely on `SATValuation` traces the exact path to `.failed .ub`,
     surfacing a rustc-style diagnostic with concrete variable values.

---

#### 8.3 Use Case 20: `ParaDRAT` Dominator-Cut Proof Splitting & `CreuSAT`-Style Bootstrapped Self-Verified Native Rust Certificate Checkers

- **Engineering Problem (The Meta-Challenge of Multi-Megabyte Certificates
  Without `native_decide`):**
  Because `TrustedBoundary.lean` forbids `native_decide` (`Lean.ofReduceBool`),
  every reflective certificate check in `theory/` is evaluated by Lean's
  interpreted kernel Whnf reducer (twice: during compilation and during
  `base.toKernelEnv.replay`). While 99% of per-function obligations have
  $10^2\text{--}5\times 10^4$ steps ($1\text{--}100\text{ ms}$ in the kernel), a
  bit-blasted 256-bit division circuit or massive hardware state machine can
  produce a **50 MB, $10^7$-step `LRAT` proof** that would exceed single-term
  kernel reduction memory limits.
- **Two Complementary Sound Mechanisms in Anneal:**
  1. **Mechanism 20A — Dominator-Cut Proof Splitting into `private theorem`
     Chunks (`ParaDRAT` Pattern in `.anneal/Proof.lean`):**
     An external proof splitter partitions the $10^7$-step `LRAT` / `Alethe` DAG
     along cut clauses into $K$ chunks $C_1, \dots, C_K$ of $10,000$ steps each.
     Each chunk is wrapped in its own `private theorem chunk_k : ... := rfl`
     (`thmInfo`) with the chunk's `ByteArray`/`Nat` literal **inlined directly
     inside the theorem proof body** (never as a separate `def` / `defnInfo`!).
     Because Lean's kernel treats `thmInfo` bodies in `Prop` as proof-irrelevant
     and opaque once checked, `base.toKernelEnv.replay` checks each chunk in
     $O(\text{ChunkSize})$ memory and never unfolds `chunk_k` when checking
     `Proof.verify_crate`!
  2. **Mechanism 20B — Self-Verified Native Rust Certificate Checkers
     (`CreuSAT` / `cake_lpr` Bootstrap Pattern via `Abstracts`):**
     Implement a zero-dependency `no_std` Rust `LRAT`/`Alethe` checker
     `anneal-lrat-check` (`fn verify_lrat(cnf: &[i32], proof: &[i32]) -> bool`)
     and **verify that Rust crate using Anneal itself** (`Trusted.CrateTheorem
     Mir.crate` proves `Abstracts L_{\text{LRAT}} L_{\text{MIR}} codec
     spec_check_lrat mir_verify_lrat` and `ProductiveOn`). Projects whose
     explicit trust policy opts into the Anneal-verified `anneal-lrat-check`
     binary (recorded transparently in the TCB audit log per `PRINCIPLES.md`)
     can check multi-gigabyte proofs at native CPU speed while every line of the
     checker carries a Lean 4 `Trusted.CrateTheorem` proof.

---

### 9. Cross-Cutting Synthesis: 20-Use-Case Matrix and Kernel Engineering Rules

`Basis: source + derived`

| # | Use Case / Certificate Checker | Representative Real-World Tools | Certificate Format | Primary `trusted/` Primitive(s) Exercised | Kernel Reduction Strategy (No `native_decide`) |
| :- | :--- | :--- | :--- | :--- | :--- |
| **1** | **Bit-Blasting (`AIG`) + `LRAT`** | `Lean 4 bv_decide`, `Bitwuzla`, `Boolector`, `CaDiCaL`, `Kissat`, `cake_lpr`, `VeriPB`/`cake_pb`, `ACL2 FGL` | Tseitin AIG + `LRAT`/`VeriPB` hints | `Abstracts` ($L_{\text{BV}} \leftarrow L_{\text{MIR}}$), `ProductiveOn` | Persistent radix-2 tree `PArray` ($O(\log N)$ updates) |
| **2** | **Incremental `FRAT`/`LIDRUP` & UNSAT Core** | `CaDiCaL` (`LIDRUP`), `FRAT-rs`/`frat-elan`, `GRAT` (`gratchk`), `IsaSAT` | Shared-DAG `MultiLRAT` + core subset | `VerificationResult` batching & waiver projection | Single shared `private theorem` batch reduction |
| **3** | **`QRAT`/`FERP` QBF/DQBF & Skolem-AIG** | `DepQBF`, `QRAT-trim`, `CAQE`/`CertCheck`, `Pedant`, `FerpCheck`, `Manthan` | Skolem boolean circuits + `LRAT` | Demonic `externalCall` $\leftrightarrow$ Angelic `ProductiveOn` | Constructive circuit substitution (`Classical.choice`-free) |
| **4** | **`Alethe` (`QF_UF + QF_AX + QF_BV`)** | `cvc5`, `Carcara`, `Alethe`, `Ethos`/`CPC`/`Eo`, `lean-smt`, `SMTCoq`, `Isabelle smt` | Hash-consed `Alethe` step DAG | Disjoint heap/slice frame conditions in `SmallStepMachine` | Integer-ID hash-consed `TermArena` ($O(1)$ term eq) |
| **5** | **Farkas, Gomory Cut & B&B (`QF_LIA`)** | `VIPR`/`viprchk`, `SCIP-Exact`, `Coq Micromega`, `Lean 4 omega`, `Z3`, `OpenSMT` | Non-negative weights + Chvátal-Gomory cuts | Slice bounds (`SpecOn`) & linear ranking (`ProductiveOn`) | GMP-backed `Nat`-pair dot-product reduction |
| **6** | **`LFSC`/Z3 `QF_DT + QF_SLIA + Inst`** | `LFSC`/`lfscc`, `Z3` proof logs, `lean-auto`, `Duper` | Ground instantiation terms $\vec{t}_j$ + `DT`/`Seq` | `BehaviorCodec` `decodeOut` representation invariants | Linear de Bruijn ground substitution + `Alethe` |
| **7** | **`CAD` & Sturm/Bernstein (`QF_NRA`/`NIA`)** | `cvc5`/`libpoly`, `SMT-RAT`/`CArL`, `QEPCAD B`, `Sturm`/`Bernstein` | Tangent planes + Sturm/Bernstein cells | Multi-dimensional tensor stride `SpecOn` | Denominator-cleared homogeneous `Int` polynomials |
| **8** | **`egg` Linear & DAG Rewrite Checker** | `egg` (`Explanation`), `lean-egg`, `Tensat`, `Herbie`, `CeTA`/`IsaFoR` (`CPF`) | Hash-consed DAG rewrite trace | `Compiles` & `Abstracts` between spec & fast MIR | DAG `NodeId` rewriting ($O(1)$ per step, no tree blowup) |
| **9** | **Slotted E-Graph & `AC` Normalizer** | `slotted-egraphs`, `Lean 4 ac_rfl`, `AAC_tactics` | Slot bijection + `perm : Array UInt16` | Iterator-to-SIMD loop fusion (`Compiles`) | $O(N)$ oracle permutation bijection verification |
| **10** | **Relational E-Graph (`egglog` Datalog)** | `egglog`, `Soufflé --provenance`, `Ascent` | Topologically sorted Horn-equality DAG | `StepResult.externalCall` `boundaryInv = true` | Strictly increasing fact IDs (`p < step.id`, no `partial`) |
| **11** | **Gröbner Basis & `LPAC` Ideal Cert** | `CryptoLine`, `Singular`, `PAC`/`LPAC`, `Pacheck`, `Pastèque`, `Lean 4 grind`/`Coq nsatz` | Polynomial co-factors $q_0 p + \sum q_k h_k$ | `Language.obs` (`SemObs`) quotienting redundant limbs | Sparse/Horner multivariate polynomial normalization |
| **12** | **NTT Butterfly & Ring Certifier (PQC)** | `formosa-mlkem`, `formosa-mldsa`, `s2n-bignum`, `CryptoLine` | Per-layer CRT split + index bijection | Compositional 7/8-stage `Compiles` chain | Layer-by-layer modular CRT decomposition |
| **13** | **Positivstellensatz (`SOS`) & Primality** | `CSDP`, `Clarabel.rs`, `Real2RatSOS`, `RealCertify`, `CoqPrime`, Mathlib `Pratt` | Rational $L D L^T$ squares + Pocklington tree | Type-level `Prime p` & nonlinear Lyapunov `ProductiveOn` | Structural binary-fuel `powMod` on GMP `Nat` ($\sim 1\text{ ms}$) |
| **14** | **`Gappa`/`FPTaylor` IEEE-754 Error Cert** | `Gappa`, `FPTaylor`, `Flocq`, `VCFloat2` | Dyadic interval + Taylor bisection DAG | `Abstracts` into $\varepsilon$-ball nondeterministic `Behavior` | Exact dyadic `(mantissa : Int, exp2 : Int)` math |
| **15** | **Taylor-Model & Remez Chebyshev Cert** | `Sollya`, `CoqInterval`, `PVS Bernstein`, `MetiTarski` | Degree-$d$ Taylor model + Bernstein basis | Constructive `libm` specs without `Mathlib` reals | Bernstein convex-hull coefficient bounds |
| **16** | **`Certifaiger` / `IC3` (`PDR`) & $k$-Ind** | `Certifaiger`, `AVR`, `Pono`, `ABC`, `btormc` | Converged clause set $F_m$ + 3 UNSAT certs | `EventualBehaviorOf` safety over `.diverges`/`.terminated` | 3 ground `LRAT`/`Alethe` checks (search trace discarded) |
| **17** | **`CHC` Relational Invariant (`Spacer`)** | `Z3 Spacer`, `Eldarica`, `Golem` | Closed-form $\mathcal{M}(P_i)$ + per-clause certs | Inter-procedural `externalCall` + borrow prophecies | Ground predicate substitution + SMT check |
| **18** | **Hopcroft-Karp Bisim & Büchi Ranking** | `Mata`/`Vata`, `SPOT`, `CAVA`, `T2`, `Ultimate Automizer` | State-pair table $R$ + `Prod.Lex` ranking | Trace equality (`List Obs` in `EventualOut`) & `Init.WF` | $O(|R| \times |\Sigma|)$ flat lookup scan + `Prod.Lex` |
| **19** | **`SyGuS` & LLM Candidate Certifier** | `cvc5 SyGuS`, `Souper`, `Alive2`, `LEMUR`, `Loopy` | Candidate AST + `LRAT`/`Alethe`/`LIA` proof | Zero-trust sandbox (`TrustedBoundary.lean`) | Fails closed on invalid candidates; CEX trace execution |
| **20** | **Dominator-Cut Split & Rust Bootstrap** | `ParaDRAT`, `CreuSAT`, `cake_lpr` bootstrap | Cut-split `thmInfo` chunks / verified Rust | `Trusted.CrateTheorem` self-verification | Proof-irrelevant `thmInfo` cut composition ($O(\text{Chunk})$) |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **PBLean (`Lean-zh/PBLean`, 2025) and CPOG (`cpog-gen`/`cpog-check`, TACAS
  2023-2024):** Reflective Lean 4 checker for `VeriPB` pseudo-Boolean
  certificates and Certified Partitioned-Operation Graphs for `#SAT` model
  counting via `LRAT`.
- **`dpr-trim` / `sr-trim` (CADE 2017) and `QBFCert` (`TraceCheck` +
  `CertCheck`, SAT 2012):** Propagation/substitution redundancy checkers and
  AIGER Skolem-function certificate validators.
- **Dolmen (`Gbury/dolmen`), Princess (`uuverifiers/princess`), Dedukti/Lambdapi
  (`Deducteam/lambdapi`), and Zipperposition:** Multi-format SMT/Alethe/TPTP
  static typecheckers, Presburger Craig-interpolant solvers, and rewrite-modulo
  proof checkers.
- **Twee (`nick8325/twee`, CADE 2021), CoLoR/Rainbow (`fblanqui/color`), Veri-
  ISLE/Crocus, Guided Equality Saturation (`rise-lang/shine`, POPL 2024), and
  Nemo (`knowsys/nemo`):** Equational completion certifiers, Coq CPF checkers,
  Cranelift ISLE verifiers, and Datalog provenance engines.
- **AMulet2 / TeluMA (`danielakaufmann/amulet2`, TACAS 2021 / FMCAD 2023) and
  RevSCA-2.0:** Symbolic computer-algebra multiplier verifiers emitting `.pac`
  and Hilbert Nullstellensatz certificates checked by `Pacheck`/`Pasteque`.
- **PRECiSA (`nasa/PRECiSA`, FM 2017), Daisy (`malyzajko/daisy`), Satire
  (`utahplt/Satire`), Fluctuat, and CORE-MATH (`core-math/core-math`):**
  Floating-point round-off error certifiers handling unstable conditional
  branches (`Compiles` + `Abstracts`).
- **Cerbtora / Btor2-Cert (CAV 2024), MoXI (`ModelChecker/moxi-mc-flow`, CAV
  2024), HoIce/PCSat, SV-COMP Witness v2.0 Validators, and Marabou + Imandra
  Farkas Checker (TACAS 2024):** Word-level model-checking, non-linear CHC, and
  exact rational Farkas branch-and-bound certificate checkers.

## Boundaries

1. **In-Repository Implementation Status (`not examined` / future `theory/`
   build-out):** At `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`,
   `trusted/lean/` contains `Trusted.lean`, `Trusted/Attributes.lean`, and
   `foundation-lock.json`, while the `theory/Anneal/Solv/*` certificate checkers
   designed in this report (`BitBlastLRAT.lean`, `AletheCheck.lean`,
   `LIACheck.lean`, `EqSatCheck.lean`, `PolyIdealCheck.lean`, `GappaCheck.lean`,
   `IC3Check.lean`, etc.) are target architectural designs for `theory/`, not
   yet committed modules on `main`.
2. **`native_decide` and External FFI Are Known Not to Apply (`unsupported`):**
   Unlike upstream Lean 4 tactics that invoke `Lean.ofReduceBool`
   (`Std.Tactic.BVDecide`) or `@[extern]` C bindings, `TrustedBoundary.lean`
   unconditionally rejects `native_decide`, `decide +native`, `@[extern]`,
   `@[implemented_by]`, and `@[csimp]`. Any solver integration that relies on
   unverified native evaluation or FFI inside `.lean` files is **unsupported**
   by Anneal's trust boundary.
3. **Solver Completeness vs. Checker Soundness (`known not to apply`):**
   Certificate checkers in `theory/` guarantee **soundness** (`checkCert goal
   cert = true → interpGoal goal`), not completeness of the external oracle on
   undecidable theories (`QF_NIA`, `CHC`, synthesis). When an untrusted solver
   times out or returns `unknown`, Anneal must fail closed (`PRINCIPLES.md`).

## Evidence

1. **Anneal Trust Boundary and Foundation Lock (`source`):**
   - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:
     - `trusted/audit/TrustedBoundary.lean`: lines 180–185 (`commandKinds`),
       lines 201–208 (`allowedAttributeNames`, `validCandidateFeatures`), lines
       312–330 (`inspectSyntax` rejecting `unsafe`, `partial`, `axiom`,
       `byElab`, `runTac`, `nativeDecide`, and `decide +native`), lines 480–516
       (`exprEdges` kernel `Expr` DAG walk and `.lit (.natVal _)` /
       `.lit (.strVal _)` leaf handling), lines 562–578 (`closure` axiom
       verification), lines 832–873 (`verifyAndCollectLocals`), and lines
       900–974 (`audit` and `base.toKernelEnv.replay locals`).
     - `trusted/lean/Trusted/Attributes.lean`: lines 63–139
       (`Trusted.expandTrustDeclaration` and `Trusted.candidate`).
     - `trusted/lean/foundation-lock.json`: lines 1–15 (locked axioms
       `Classical.choice`, `Quot.sound`, `propext`), lines 16–21 (Lean `v4.34.1`
       commit `5045d0056413266e57c625dcd7c365b10e377c52`), and locked `Init.*`
       module graph (`Init.Data.AC`, `Init.Data.BitVec.*`, `Init.Data.Int.*`,
       `Init.Data.Nat.*`, `Init.Omega`, `Init.WF`).
2. **Anneal 4-Primitive Trusted Semantic Core (`source`):**
   - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and corpus
     synthesis in `anneal-behavior-codec-and-progress-refinement-2026` and
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`:
     - `Language (SemObs : Type)`, `BehaviorCodec L₁ L₂` (with partial
       `decodeOut : L₂.Out → Option L₁.Out` and `obs_decodeOut`), `Compiles`,
       `Abstracts`, `ProductiveOn`, `InhabitedPre`, and positive per-obligation
       `VerificationResult`.
     - `SmallStepMachine`, `EventualOut`, `EventualBehaviorOf`, and
       `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`.
3. **Primary Literature and Upstream Solver/Checker Specifications (`normative` +
   `documentation`):**
   - **Category 1:** Tan, Heule, and Myreen, *"cake_lpr: Verified Propagation
     Redundancy Checking in CakeML"*, TACAS 2021 (`10.1007/978-3-030-72013-1_14`);
     Bogaerts, Gocht, McCreesh, Myreen, Nordström, and Tan, *"Certified
     Symmetry and Dominance Breaking for Combinatorial Optimisation"* / `VeriPB`
     & `cake_pb` (AAAI 2022 / CP 2023); Lammich, *"Efficient Verified (UN)SAT
     Certificate Checking"* (`GRAT`), CADE-26 (2017,
     `10.1007/978-3-319-63046-5_24`); Baek, Carneiro, and Heule, *"A Flexible
     Proof Format for SAT Solver-Elaborator Communication"* (`FRAT`), TACAS
     2021; Biere, Faller, Fazekas, Fleury, Froleyks, and Pollitt, *"LIDRUP"*,
     2024; Niemetz and Preiner, *"Bitwuzla"*, CAV 2023; Heule, Seidl, and Biere,
     *"QRAT"*, IJCAR 2014; Rabe and Tentrup, *"CAQE"*, FMCAD 2015; Reichl,
     Slivovsky, and Szeider, *"Pedant"*, TACAS 2023; Golia, Roy, and Meel,
     *"Manthan: A Data-Driven Approach for Boolean Functional Synthesis"*, CAV
     2020 (`10.1007/978-3-030-53288-8_27`).
   - **Category 2:** Andreotti, Lachnitt, and Barbosa, *"Carcara: An Efficient
     Proof Checker and Elaborator for SMT Proofs in the Alethe Format"*, CAV
     2023 (`10.1007/978-3-031-37703-7_18`); Barbosa et al., *"cvc5"* / `Ethos` /
     `CPC`, TACAS 2022 / FMCAD 2023; Ekici et al., *"SMTCoq"*, CAV 2017; Cheung,
     Gleixner, and Steffy, *"Verifying Integer Programming Results"* (`VIPR`),
     IPCO 2017 (`10.1007/978-3-319-59250-3_12`); Besson, *"Fast Reflexive
     Arithmetic Tactics: The Linear Case and Beyond"* (`Micromega`), TYPES 2006;
     Stump et al., *"LFSC"*, FMSD 2013; Clune et al., *"Duper"*, ITP 2024;
     Corzilius et al., *"SMT-RAT"*, SAT 2015 (`10.1007/978-3-319-24318-4_4`).
   - **Category 3:** Willsey et al., *"egg: Fast and Extensible Equality
     Saturation"*, POPL 2021 (`10.1145/3434304`); Zhang et al., *"Better
     Together: Unifying Datalog and Equality Saturation"* (`egglog`), PLDI 2023;
     Schneider et al., *"Slotted E-Graphs"*, EGRAPHS 2024; Thiemann and
     Sternagel, *"Certification of Termination Proofs using CeTA"*, TPHOLs/CADE
     2009 (`10.1007/978-3-642-02959-2_10`); Braibant and Pous, *"AAC_tactics"*,
     CPP 2011; Sahebolamri, Holding, and Rossberg, *"Seamless Deductive
     Inference via Macros"* (`Ascent`), CC 2022; Zhao, Subotić, and Scholz,
     *"Debugging Large-scale Datalog: A Scalable Provenance Evaluation
     Strategy"* (`Soufflé`), TOPLAS 2020.
   - **Category 4:** Polytechnique / Academia Sinica (`Fu, Tsai, Wang, Yang,
     Wang`), *"Signed Cryptographic Program Verification with Typed CryptoLine"*,
     CCS 2019 (`10.1145/3319535.3354199`); Kaufmann, Fleury, Biere, and Kauers,
     *"Practical Algebraic Calculus and Nullstellensatz with the Checkers
     Pacheck and Pastèque"*, FMCAD 2020; Formosa Crypto Project
     (`formosa-mlkem`, `formosa-mldsa`); AWS `s2n-bignum`; Magron and Safey El
     Din, *"RealCertify"*, ISSAC 2018 (`10.1145/3208976.3208980`); Théry and
     Grégoire, *"CoqPrime"*.
   - **Category 5:** Daumas and Melquiond, *"Certification of Bounds on
     Expressions Involving Rounded Operators"* (`Gappa`), ACM TOMS 2010
     (`10.1145/1941487.1941490`); Boldo and Melquiond, *"Flocq"*, IEEE TC 2011;
     Solovyev et al., *"Rigorous Estimation of Floating-Point Round-Off Errors
     with Symbolic Taylor Expansions"* (`FPTaylor`), ACM TOPLAS 2018; Appel and
     Kellison, *"VCFloat2"*, CPP 2024; Chevillard, Joldeş, and Lauter,
     *"Sollya"*, ICMS 2010; Melquiond, *"CoqInterval"*, IJCAR 2008; Muñoz and
     Narkawicz, *"Formalization of Bernstein Polynomials and Applications to
     Global Optimization"* (`PVS`), JAR 2013; Akbarpour and Paulson,
     *"MetiTarski"*, JAR 2010.
   - **Category 6:** Froleyks, Yu, Biere, and Heljanko, *"Certifaiger"*, FMCAD
     2021; Mann et al., *"Pono"*, CAV 2021; Goel and Sakallah, *"AVR"*, TACAS
     2020; Komuravelli, Gurfinkel, and Chaki, *"SMT-Based Model Checking for
     Recursive Programs"* (`Spacer`), CAV 2014 / FMSD 2016
     (`10.1007/978-3-319-41528-4_22`); Hojjat and Rümmer, *"Eldarica"*, FMCAD
     2018; Blicha et al., *"Golem"*, CAV 2023; Chocholatý et al., *"Mata"*,
     TACAS 2024; Duret-Lutz et al., *"SPOT"*, CAV 2022; Esparza et al.,
     *"CAVA"*, CAV 2013; Heizmann et al., *"Ultimate Automizer"*, POPL 2013.
   - **Category 7:** Lopes et al., *"Alive2: Bounded Translation Validation for
     LLVM"*, PLDI 2021 (`10.1145/3453483.3454037`); Wu, Barrett, and
     Narodytska, *"LEMUR: Integrating Large Language Models in Automated Program
     Verification"*, ICLR 2024; Skotåm, *"CreuSAT: Using Rust and Creusot to
     Create the World's Fastest Verified SAT Solver"*, Master's Thesis, Univ. of
     Oslo 2022.

## Revalidation

To revalidate the findings in this report after changes to `trusted/lean/`,
`trusted/audit/TrustedBoundary.lean`, or the pinned Lean 4 toolchain:

1. **Verify `TrustedBoundary.lean` syntax and axiom gates:**
   Inspect `inspectSyntax` (`trusted/audit/TrustedBoundary.lean:312-330`) and
   `closure` (`L562-578`) to confirm whether `Lean.Parser.Tactic.nativeDecide`
   (`native_decide`) and `decide +native` remain rejected and whether
   `trusted/lean/foundation-lock.json` still restricts axioms to
   `{Classical.choice, Quot.sound, propext}`:
   ```console
   cargo test --manifest-path trusted/audit/Cargo.toml
   ```
2. **Verify `foundation-lock.json` module coverage for `theory/` checkers:**
   Check whether `Std.Sat`, `Std.Tactic.BVDecide`, or `Rat` have been added to
   `trusted/lean/foundation-lock.json` or remain excluded (requiring `theory/`
   checkers to use `Init.*` primitives and denominator-cleared `Nat`/`Int` or
   `Dyadic` representations).
3. **Verify `BehaviorCodec` and `StepResult.externalCall` contracts:**
   When `Trusted/Refinement.lean` and `Trusted/StepResult.lean` are updated,
   check that `Language SemObs` retains `obs : Out → SemObs` (required by Use
   Cases 11–12 for redundant limb quotienting) and that `Behavior` retains set
   inclusion `≤` over `Out → Prop` (required by Use Cases 14–15 for
   $\varepsilon$-ball floating-point refinement).
