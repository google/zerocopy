# Translation Validation, Certifying Compilation, and Pass-Refinement Certificates

## Summary

Translation validation, proof-producing (certifying) compilation, hinted replay, and pass-refinement certificates shift compiler and extractor implementations out of the trusted computing base by requiring every accepted translation run to pass an independent semantic or proof check. Across foundational and modern translation-validation and certification systems—from Pnueli, Siegel, and Singerman (TACAS 1998), Necula (POPL 1997, PLDI 2000), Barthe et al. (SAS 2006), Blech and Poetzsch-Heffter (ENTCS 2007), Tristan and Leroy (POPL 2008), and AutoCorres (PLDI 2014) to Crellvm (PLDI 2018), Jitterbug (OSDI 2020), Alive2 (PLDI 2021, CAV 2021), Cogent (JFP 2021), Katamaran (ICFP 2022), Computing Correctly with Inductive Relations (PLDI 2022), Dargent (POPL 2023), CryptOpt (2023), Plutus Translation Certification (FLOPS 2022, SCP 2024), PotPie (ITP 2024), Owlang (2025), RustCompCert (2026), EquiVM (2026), and Trivet (2026)—nine core architectural principles determine what a certificate or validator actually establishes:

1. **Per-Run Validation vs. Universal Compiler Verification (TACAS 1998 – PLDI 2021):** Translation validation establishes a correctness relation $c_1 \le c_2$ for a single concrete source/target pair $(c_1, c_2)$ rather than quantifying over all compiler executions. Its assurance rests on two independent pillars: the **semantic relation** (which must include undefined behavior, definedness obligations, memory effects, nondeterminism, and divergence rather than comparing only terminating return values) and the **validator trust model** (unverified heuristic/SMT checker vs. formally verified boolean validator $V(c_1, c_2) = \text{true} \implies c_1 \le c_2$ in Coq vs. proof-producing certificate checker). Bounded SMT validators such as Alive2 trade unbounded loop and resource coverage for automated bug-finding and refinement checking over LLVM's poison/`undef` and memory models (`support/translation-validation-techniques-1998-2021/technique-matrix.json`).
2. **Proof-Producing vs. Validating Translations (POPL 1997 – FLOPS 2022):** A verified validator internalizes evidence search into a proved decision procedure returning a boolean, whereas a proof-producing (certifying) translator externalizes a per-run derivation or proof object checked by a small kernel (`support/proof-producing-versus-validating-translations-1997-2022/architecture-matrix.json`). Crucially, target-policy proofs (Proof-Carrying Code), syntactic pass-relation derivations $\text{Rel}_i(t_i, t_{i+1})$, semantic-preservation theorems $\text{Rel}_i(t_i, t_{i+1}) \implies \llbracket t_i \rrbracket_i \sim_i \llbracket t_{i+1} \rrbracket_{i+1}$, and target-model property proofs in Lean solve distinct obligations: a Lean kernel proof about generated Lean code does not by itself certify that the generated Lean model faithfully translates the input Rust program.
3. **Cross-System Certificate Seam Comparison (Katamaran, VeriFast, CakeML, Lean4Lean, hax, Electrolysis):** Existing verification systems instantiate six distinct assurance architectures (`evidence.json`, `coverage.json`): verified transformations, verified validators, proof-producing translations, guided replay (Foundational VeriFast `0a83dba42db7ce0b445034ece5298afe980e57dc`), verified symbolic-to-shallow execution (Katamaran, DOI `10.1145/3547628`), and external kernel rechecking (Lean4Lean `arXiv:2403.14064v3`). Current `cryspen/hax@cc6da074ca754ca9d406ec922daad3221aacbce5` Lean documentation routes directly through Charon and Aeneas, providing workflow ergonomics rather than an independent translation oracle.
4. **Instrumented Optimization Certificates and Rule-Admission Boundaries (Crellvm PLDI 2018):** In Crellvm (`snu-sf/crellvm@668249b88756233f96b3ef21f12993501a348afc`, DOI `10.1145/3192366.3192377`), compiler instrumentation emits relational Hoare logic (ERHL) witnesses checked to establish target behavior inclusion $\text{Beh}(\text{target}) \subseteq \text{Beh}(\text{source})$. Direct source inspection reveals two critical boundaries: (a) `Behavior.v`'s `beh_error` admits every observation after a source error, so $\text{Beh}(\text{target}) \subseteq \text{Beh}(\text{source})$ holds trivially when the source triggers UB even if the target is safe (forward optimization refinement does not reflect target safety back to source safety), and (b) `SoundInfrules.v` (`apply_not_interesting_infrule_sound`) invokes `TODOProof.ADMIT` (`Admitted`) for arithmetic and InstCombine-only rules, while `ocaml/main.ml` bypasses validation on `ADMITTED` hints and exits with zero on `Some false` layout/type mismatches.
5. **Inductive Pass Relations vs. Admitted Side-Condition Helpers (Plutus SCP 2024):** Krijnen et al. (SCP 2024, DOI `10.1016/j.scico.2023.103051`, artifact `basetunnel/2022-scp-translation-relations@72e619f3243498a612d8c6c5090b88117c404489`) separate inductive pass relations `dead_code(s, t) = elim(s, t) /\ unique(s) /\ closed(t)` from reflected decision procedures. Source analysis of the pinned artifact exposes that `DeadCode/DecideSound.v` proves only `dec_elim_Term s t = true -> elim s t` and relies on `Analysis/Purity.v`'s `sound_dec_pure_binding`, which ends with `Admitted`—and for a strict error binding `b = TermBind Strict vd (Error T)`, `dec_pure_binding [] b` evaluates to `true` (`Value.dec_value' 0 (Error T) = true`) while `pure_binding [] b` is false because `is_pure` forbids `IsError` (`support/plutus-inductive-pass-certificates-scp-2024/purity_witness.py`).
6. **Guarded Model Abstraction and Nonfailure Reflection (AutoCorres PLDI 2014):** Greenaway et al. (PLDI 2014, DOI `10.1145/2594291.2594296`) generate per-program LCF correspondence theorems in Isabelle/HOL for word and heap abstractions whose conclusion explicitly conjoins concrete nonfailure ($\text{NF}(A(\text{st}(s))) \implies \text{NF}(C(s)) \land \forall(r,t) \in \text{Out}(C(s)).\, (r,\text{st}(t)) \in \text{Out}(A(\text{st}(s)))$). Unlike forward compiler refinement, this nonfailure reflection implication $\text{NF}(\text{abstract}) \implies \text{NF}(\text{concrete})$ is the exact logical direction required by Anneal (`verification/aeneas/ADMISSION_DESIGN.md`) so that proving safety of an abstracted model implies absence of concrete source failure/UB.
7. **Memory-to-Value Refinement vs. Physical Layout Meaning (Cogent JFP 2021 & Dargent POPL 2023):** Cogent (DOI `10.1017/S095679682100023X`) factors functional value semantics, imperative update semantics, and C heap refinement with explicit writable-footprint framing and concrete nonfailure (`NF(P(\sigma))`). Dargent (DOI `10.1145/3571240`) adds custom bit/byte layout refinement via generated getters and setters, proving getter/setter algebraic laws alongside a separate getter format-correspondence theorem against `uval_from_array(type, layout, arr)` (while noting the generic setter format theorem was not yet completed in POPL 2023 §4.4). A finite witness (`support/cogent-dargent-memory-value-layout-certificates-2021-2023/layout_witness.py`) confirms that swapped physical field offsets satisfy all getter/setter round-trip and frame laws while violating physical layout meaning.
8. **Property-Proof Translation and Independent Specification Meaning (Barthe SAS 2006 & PotPie ITP 2024):** Barthe et al. (SAS 2006, DOI `10.1007/11823230_20`) and PotPie (ITP 2024, DOI `10.4230/LIPIcs.ITP.2024.33`, `uwplse/potpie@a57f960958901dee3b8075be0a312d6a194be456`) translate Hoare proofs across compiler passes ($\text{Certifies}(c, p, \phi) \implies \text{Certifies}(T_{\text{cert}}(c), T_{\text{code}}(p), T_{\text{spec}}(\phi))$). PotPie's `StkHoareTree.v` checks target derivation trees (`stk_valid_tree`), while `ProofCompilerCodeCompAgnostic.v` requires separate specification-soundness bi-implications ($\text{source\_state} \models P \iff \text{target\_state} \models T_{\text{spec}}(P)$). As confirmed by `support/property-proof-translation-specification-meaning-2006-2024/specification_witness.py`, a generator that mutates both code and specification can produce a kernel-valid target theorem for a trivially weakened postcondition (`True`) or strengthened precondition (`False`) unless specification meaning is pinned independently.
9. **Refinement Direction vs. Safety Reflection Across Compiler Families (Alive2, Trivet, CryptOpt, Jitterbug, EquiVM, Owlang, RustCompCert):** Comparing refinement endpoints (`support/refinement-policy-and-safety-direction-comparison/relation_endpoint_witness.py`) shows that forward optimization refinement (`src \sqsupseteq tgt` in Alive2 and Trivet `arXiv:2609.19583v1`) legally refines source UB into defined target behavior, and conditional JIT correctness (Jitterbug OSDI 2020) assumes source safety as a premise; neither reflects target safety back to source safety without an explicit source-failure reflection obligation or a separate ownership-safety theorem (as in Owlang `arXiv:2510.10015v1` §5 Theorems 5.1–5.2).

## Applicability

This report synthesizes nine primary investigations in the Anneal reference corpus covering translation validation, certifying compilation, and pass-refinement certificates:

- **Foundational and Modern Translation Validation (1998–2021):** Pnueli, Siegel, & Singerman (TACAS 1998, DOI `10.1007/BFb0054170`), Necula (PLDI 2000, DOI `10.1145/349299.349314`), Tristan & Leroy (POPL 2008, DOI `10.1145/1328438.1328444`), Lopes et al. (Alive2, PLDI 2021, DOI `10.1145/3453483.3454030`), and Lee et al. (CAV 2021, DOI `10.1007/978-3-030-81688-9_35`).
- **Proof-Producing vs. Validating Architectures (1997–2022):** Necula (Proof-Carrying Code, POPL 1997, DOI `10.1145/263699.263712`), Blech & Poetzsch-Heffter (ENTCS 190(4), 2007, DOI `10.1016/j.entcs.2007.09.008`), Tristan & Leroy (POPL 2008), and Krijnen et al. (FLOPS 2022, DOI `10.1007/978-3-030-99461-7_6`).
- **Related Certifying-Translation Techniques:** Katamaran (ICFP 2022, DOI `10.1145/3547628`), CakeML backend (`https://cakeml.org/jfp19.pdf`, 2018-11-19), Lean4Lean (`arXiv:2403.14064v3`), `cryspen/hax@cc6da074ca754ca9d406ec922daad3221aacbce5`, and `Kha/electrolysis` (`README.md` blob `670746012e99efc7b239bc5cd41f9ee2d967997b`), alongside corpus comparisons with Foundational VeriFast (`0a83dba42db7ce0b445034ece5298afe980e57dc`), Creusot (`c4e9770ac1371ac4274bfe02145266d315c2fb86`), RustHornBelt, and RefinedRust (`google/zerocopy@fa65b241fd0cb2c791c841eace86d43d724359bc`).
- **Instrumented Refinement & Inductive Pass Certificates:** Crellvm (PLDI 2018, DOI `10.1145/3192366.3192377`, `snu-sf/crellvm@668249b88756233f96b3ef21f12993501a348afc`) and Plutus Translation Certification (SCP 233 (2024) 103051, DOI `10.1016/j.scico.2023.103051`, `basetunnel/2022-scp-translation-relations@72e619f3243498a612d8c6c5090b88117c404489`).
- **Model Abstraction, Memory/Layout Refinement, and Proof Compilation:** AutoCorres (PLDI 2014, DOI `10.1145/2594291.2594296`), Cogent (JFP 2021 e25, DOI `10.1017/S095679682100023X`), Dargent (POPL 2023 article 47, DOI `10.1145/3571240`), Barthe et al. (SAS 2006, DOI `10.1007/11823230_20`), and PotPie (ITP 2024 article 33, DOI `10.4230/LIPIcs.ITP.2024.33`, `uwplse/potpie@a57f960958901dee3b8075be0a312d6a194be456`), evaluated against Anneal's models and admission design (`google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`).
- **Refinement Direction and Policy Taxonomy:** Alive2 (`AliveToolkit/alive2@5d0eb277235b73f71000501c3a4f5ab9b2586915`), CryptOpt (`arXiv:2211.10665v3`, `0xADE1A1DE/CryptOpt@c089d8ce3cace748a0a22e25d7adfbf2cfc6a883`, `mit-plv/fiat-crypto@b4ad623c6a5bde0c71169493963a308c612fce3f`), Jitterbug (OSDI 2020, `uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d`), Trivet (`arXiv:2609.19583v1`), EquiVM (`arXiv:2607.26306v1`), Owlang (`arXiv:2510.10015v1`), RustCompCert (`arXiv:2602.07455v1`), Paraskevopoulou et al. (PLDI 2022), and Vellvm (`vellvm/vellvm@4c6db50077cbc0df3fb3156c0570129201cc35f3`).

## Findings

### Part I: Translation-Validation Techniques and Validator Trust Models (1998–2021)

#### 1. Per-Run Refinement Checking vs. Universal Compiler Verification

Pnueli, Siegel, and Singerman (TACAS 1998, DOI `10.1007/BFb0054170`) formulate translation validation as a post-translation verification pass receiving a concrete source program and its compiled target and establishing a formal refinement/simulation relation between them within a shared semantic framework. Necula (PLDI 2000, DOI `10.1145/349299.349314`) applies this pass-locally across GCC optimization passes using symbolic execution and heuristic inference of transformation correspondence without requiring the optimizer to emit proof witnesses.

Across the 1998–2021 spine (`support/translation-validation-techniques-1998-2021/technique-matrix.json`), validators differ along five orthogonal axes:

| System / Paper | Target Granularity | Semantic Relation | Correspondence / Proof Method | Trust & Completeness Boundary |
| --- | --- | --- | --- | --- |
| **Pnueli, Siegel, Singerman (TACAS 1998)** | Whole-program synchronous/source-to-C translation | Refinement / simulation mapping over shared semantic framework | Automated proof script / invariant generation | Soundness depends on validator and proof checker; incomplete for general programs |
| **Necula (PLDI 2000)** | Pass-local GCC IR optimization passes | Simulation / equivalence of pass-level IR semantics | Symbolic execution + heuristic branch/value correspondence inference | Unverified C/symbolic validator; no compiler instrumentation required |
| **Tristan & Leroy (POPL 2008)** | CompCert Mach instruction-scheduling pass | $V(c_1, c_2) = \text{true} \implies c_1 \le c_2$ (definedness + final symbolic state) | Symbolic evaluation + definedness constraint tracking | Mechanized Coq soundness theorem (`Theorem 1`); fail-closed wrapper (`Error` on rejection) |
| **Alive2 (PLDI 2021) & CAV 2021 Memory Model** | LLVM IR intraprocedural transformations | LLVM refinement ($\text{src} \sqsupseteq \text{tgt}$): target may refine UB/poison/`undef` | Symbolic execution lowered to SMT (Z3) with precise byte/pointer memory encoding | Bounded loop unrolling, time, and memory; unverified C++/Z3 TCB; aims for zero false alarms within supported fragment |

#### 2. Definedness Tracking, Bounded SMT Validation, and the Three-Way Outcome Taxonomy

- **Definedness tracking in symbolic validation (POPL 2008 §2.2):** Equality of final symbolic register/memory expressions on terminating paths is unsound by itself because a rescheduled block could introduce a new failing operation (e.g., division by zero or invalid load) prior to computing the same final expression. Tristan and Leroy's validator therefore tracks the set of operations whose definedness is required and checks that the target's definedness obligations are no stronger than the source's.
- **Language-specific UB/poison refinement and boundedness (PLDI 2021 §§5, 7 & CAV 2021):** Because LLVM optimizations legally exploit undefined behavior and resolve `undef`/poison nondeterminism, Alive2 checks a directional refinement relation rather than extensional equality, paired with an SMT encoding of LLVM's memory model (Lee et al., CAV 2021, DOI `10.1007/978-3-030-81688-9_35`). Because Alive2 unrolls loops up to a finite bound, an accepted run establishes refinement only up to that bound and within the modeled intraprocedural fragment.
- **Three-way outcome taxonomy:** Every validation architecture must distinguish (1) **accepted** (the validator established its declared relation), (2) **rejected with counterexample/discrepancy** (semantic violation exhibited), and (3) **unknown / unsupported / resource-exhausted** (the validator failed to establish the relation without proving a bug). Only (1) may produce an ordinary verified result.

---

### Part II: Proof-Producing vs. Validating Translations (1997–2022)

#### 1. Producer/Checker Asymmetry and Target Safety vs. Translation Correspondence

Comparing four foundational certification designs (`support/proof-producing-versus-validating-translations-1997-2022/architecture-matrix.json`) separates where evidence resides from what proposition it proves:

- **Proof-Carrying Code (Necula, POPL 1997, DOI `10.1145/263699.263712`):** An untrusted producer emits target code paired with a proof that the target satisfies a consumer-defined safety policy. This removes the producer from the TCB for *target safety*, but says nothing about whether the target faithfully translates a source program.
- **Certifying Code Generation (Blech & Poetzsch-Heffter, ENTCS 190(4), 2007, DOI `10.1016/j.entcs.2007.09.008`):** Each compilation run generates an explicit per-run correctness proof checked by a separate theorem prover (using proof schemas to mitigate proof-checking bottlenecks).
- **Verified Translation Validators (Tristan & Leroy, POPL 2008, DOI `10.1145/1328438.1328444`):** No per-run proof object leaves the validator; instead, the validator $V : L_1 \times L_2 \to \text{bool}$ is proved sound once ($V(c_1, c_2) = \text{true} \implies c_1 \le c_2$).
- **Translation Certification for Smart Contracts (Krijnen et al., FLOPS 2022, DOI `10.1007/978-3-030-99461-7_6`):** Models each pass by a proof-relevant inductive relation $\text{Rel}_i(t_i, t_{i+1})$ over intermediate ASTs $t_1, \dots, t_n$, demonstrating that a certifier can construct evidence via (1) tactic search, (2) a proof-producing decision procedure returning `option (Rel_i t1 t2)`, or (3) a boolean decision procedure paired with a soundness theorem (proof by reflection).

#### 2. Three Layers of a Translation Certificate and Artifact Identity Binding

Krijnen et al. (FLOPS 2022 §§2.3–2.4) expose a critical three-layer separation:
1. **Artifact Identity Binding:** The certificate binds the exact concrete AST sequence $t_1, \dots, t_n$ so a proof for program $A$ cannot be replayed for program $B$.
2. **Syntactic Translation Conformance:** A conjunction of per-pass derivations $\text{Rel}_1(t_1, t_2) \land \dots \land \text{Rel}_{n-1}(t_{n-1}, t_n)$ proves each pass stayed within its inductive specification.
3. **Semantic Consequence:** A separate theorem $\text{Rel}_i(t_i, t_{i+1}) \implies \llbracket t_i \rrbracket_i \sim_i \llbracket t_{i+1} \rrbracket_{i+1}$ is required to lift syntactic relation conformance to semantic preservation.

For Anneal, a Lean kernel proof of a user theorem about generated Lean code is proof-producing *inside the target logic*, but it does not supply either a `Rust -> LLBC` or an `LLBC -> Lean` translation certificate.

---

### Part III: Certifying Translations and Related Verification Techniques Across Systems

#### 1. Six Assurance Architectures and Cross-System Proof Boundaries

Synthesizing assurance architectures across nine related verification systems (`evidence.json`, `coverage.json`, `primary-evidence.json`) clarifies what each mechanism removes from the trusted path and what bridge remains missing for Rust/Anneal:

| System | Theorem Domain & Semantic/Trust Boundary | Evidence Seam & Partiality/Resource Model | Transferable Mechanism & Missing Bridge for Anneal |
| --- | --- | --- | --- |
| **Foundational VeriFast** (`0a83dba42db7ce0b445034ece5298afe980e57dc`) | Replay soundness into an Iris axiomatic semantics at the inspected pin; primitive/storage admissions remain | Recorded symbolic choices (chunk selection, pointer/type equalities) checked against bodies/contracts; bounded fuel | Hinted replay avoids re-running heuristic search, but requires concrete Rust operational adequacy and complete primitive closure |
| **Katamaran** (ICFP 2022, DOI `10.1145/3547628`, Lemmas 2.1, 5.1, 6.1) | Symbolic VC implies shallow specification-monad VC via Kripke logical relation, then Iris operational partial correctness (Lemma 6.1) | Deep symbolic formulas, world/substitution scope discipline, spatial heap chunks; default partial correctness | Proved symbolic-to-shallow decomposition (`appendloop`: 34 shallow vs. 3 symbolic branches, 0.034s in Coq 8.15.2 on Ryzen 9 5950X); requires Rust semantics |
| **RustHornBelt** | $\lambda_{\text{Rust}}$ semantic type/borrow transformers and prophecy/lifetime resources | Current/final borrow values and proved consistency | Justifies prophecy/backward-function borrow contracts; frontend extraction remains separate |
| **RefinedRust** | Radium adequacy under typed-entry/layout premises; explicit frontend/model assumptions | Generated Rocq obligations plus maintained proofs | Byte-resource and proof-maintenance structure; does not prove MiniRust equivalence automatically |
| **Creusot / Coma** (`c4e9770ac1371ac4274bfe02145266d315c2fb86`) | Coma VC/semantic theorem is separate from Rust extraction, trusted primitive models, and SMT solver acceptance | Permission-carrying APIs and Why3/SMT prover chain | Explicit permission/specification boundary; source extraction and solver checking remain trusted unless bridged |
| **Cogent / Dargent** (JFP 2021 / POPL 2023) | Functional/update/C state refinement and generated layout accessors for total core language | Isabelle program-specific tactic proofs and frame/layout obligations | Value-memory refinement factoring and layout accessor algebra; Rust aliasing, provenance, and recursion are additional |
| **CompCert 3.18** (`74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`) | Conditional C-to-Asm trace backward simulation under source receptiveness and target determinacy | Composed per-pass forward simulations + verified-validator wrapper option | Lexicographic stuttering measures and fail-closed pass composition |
| **CakeML Backend** (`https://cakeml.org/jfp19.pdf`, 2018-11-19, §§2.3–2.4, 10–12) | HOL4 source-to-machine behavioral refinement up to resource-limit termination and FFI premises | Verified compiler, runtime, and in-logic bootstrap (~9h translation, 24–30h in-logic evaluation) | Proof-producing synthesis and verified machine lowering; Rust frontend and cross-logic bridge remain separate |
| **Lean4Lean v3** (`arXiv:2403.14064v3`) | External Lean typechecker written in Lean with correctness proved for kernel components | Rechecks exported kernel proof objects (20–50% slower than C++ reference kernel) | Independent kernel checking diversity; does not establish Rust source-to-model adequacy |

#### 2. Extraction vs. Justification in `hax` and `electrolysis`, and Candidate Aeneas Witness Interfaces

- **`cryspen/hax@cc6da074ca754ca9d406ec922daad3221aacbce5` and `Kha/electrolysis`:** At `docs/dev/architecture.md` (blob `4491c64185044fc3dce318b4b02031be9a88b0a3`), `hax`'s Lean backend delegates directly to Charon and Aeneas; `docs/manual/lean/quick_start.md` (blob `715bd5bc5cfa4c96d60bdb0ff5b8552ec812b1e2`) and `docs/manual/lean/tutorial/panic-freedom.md` (blob `c5622ab470f2e7164ca16b09fad41864c04e1acb`) document partial extraction and template `sorry` proofs before user proof discharge. `Kha/electrolysis` (`README.md` blob `670746012e99efc7b239bc5cd41f9ee2d967997b`) provides historical documentation of `rustc`-API transpilation to Lean for a binary-search example without a verified-translator theorem.
- **Candidate Finite Witness Interfaces for Aeneas Symbolic-to-Pure Seams:**

| Translation Boundary | Candidate Finite Evidence | Checker Obligation |
| --- | --- | --- |
| **Borrow creation / end / reborrow** | Resource IDs, lifetime inclusions, affected places, continuation/update relation | Authority transfer, aliasing exclusion, and value restoration without duplicating ownership |
| **Abstraction change** | Before/after state relation and substitution map | Both abstract states represent related concrete states under the same environment |
| **Control-flow join** | Branch-state injections and common merged abstract state | Every feasible incoming branch state is covered without dropping resources |
| **Loop translation** | Invariant, entry proof, body preservation, and exit proof | All iterations and exits preserve the invariant; total correctness requires a separate well-founded measure |
| **Pure transformation** | Typed binder/substitution witness or local rewrite derivation | Result/failure equivalence under the target denotation and capture-avoiding variable binding |
| **CFG reconstruction** | Positional copy/edge map with administrative-step ranks | Normal/unwind edges and divergence match, including synthetic loops |
| **Primitive / model call** | Exact symbol/instantiation identity and proved contract | Concrete operation refines the model with complete frame and failure conditions |

---

### Part IV: Instrumented Optimization Certificates and Refinement Direction in Crellvm (PLDI 2018)

#### 1. ERHL Relational Evidence vs. Pinned `snu-sf/crellvm` Source Boundaries

Crellvm (Kang et al., PLDI 2018, DOI `10.1145/3192366.3192377`, targeting LLVM 3.7.1; repository `snu-sf/crellvm@668249b88756233f96b3ef21f12993501a348afc`, tree `0b62b6ab302501596f06f4b94181cc1c82df6aa7`) instruments LLVM passes to emit alignment points, invariants, and rule hints checked in Coq via Expectational Relational Hoare Logic (ERHL) to establish target behavior inclusion:
$$\text{Beh}(\text{target}) \subseteq \text{Beh}(\text{source})$$
Direct inspection of the pinned Coq and OCaml files establishes three concrete boundaries:
1. **Unrestricted source error behaviors (`Adequacy.v` & `Behavior.v`):** `coq/proof/Adequacy.v` (blob `ecfae4591dd0975edc9edac1004385145a62ee3e`, lines 25–28, 72–97) exports `sim(source_state, target_state) -> behave(target_state) \subseteq behave(source_state)`. In `coq/proof/Behavior.v` (blob `ff32147504d3ae7f8fe479d038d6c54c5664c907`, lines 21–27, 61–64), `beh_error` admits *every* observation once the source reaches an error state. Consequently, if a source program triggers UB, $\text{behave}(\text{source\_state})$ is the universal set of behaviors, and any safe target trivially satisfies $\text{behave}(\text{target\_state}) \subseteq \text{behave}(\text{source\_state})$. Forward behavior inclusion therefore cannot reflect target safety back to source UB-freedom.
2. **Admitted inference-rule subset (`SoundInfrules.v` & `TODOProof.v`):** `coq/proof/SoundInfrules.v` (blob `5c3d417c392d71c6fa8cfe7ec2b4e4071f5f3596`, lines 32–52) splits rules into interesting and non-interesting subsets; `apply_not_interesting_infrule_sound` discharges arithmetic and InstCombine-only rules by invoking `ADMIT`, defined in `coq/proof/TODOProof.v` (blob `c6f0050509b787b90504039c36a6aa52699657c2`, lines 467–468) using Coq's `Admitted`.
3. **Three-valued validator return and CLI exit behavior (`Validator.v` & `main.ml`):** `coq/def/Validator.v` (blob `e56bd51e4c621ee70c51a824bf118c0a8938ad1a`, lines 335–346, `valid_module`) returns `Some true` on validated modules, `Some false` on layout/named-type mismatch, and `None` on validation failure. In `ocaml/main.ml` (blob `d5f842d591b010276e7b9f6fcbfcef277a3dfb43`, lines 84–115), the CLI wrapper bypasses validation on an `ADMITTED` hint, prints an admission message without failing the process on `Some false`, and exits with an error code only on `None`. Process exit code `0` is therefore not equivalent to `valid_module = Some true`. (Note also that `Makefile` blob `5830bda3dc2ea453c75fe5028731dbff8f01c7f6` clones unpinned external Vellvm/LLVM repositories, and `coq/proof/Refinement.v` named in the README is absent from the tree.)

---

### Part V: Inductive Pass Relations and Admitted Purity Helpers in Plutus (SCP 2024)

#### 1. Syntactic Pass Relations vs. Partial Checker Theorems in `basetunnel/2022-scp-translation-relations`

In *Translation Certification for Smart Contracts* (Krijnen et al., *Science of Computer Programming* 233 (2024) 103051, DOI `10.1016/j.scico.2023.103051`, §§2.1–2.4, 4, 5.4; artifact `basetunnel/2022-scp-translation-relations@72e619f3243498a612d8c6c5090b88117c404489`), dead-code elimination between Plutus Intermediate Representation (PIR) terms is specified in `src/Language/PlutusIR/Transform/DeadCode.v` (blob `65da05418c6a310e2b4c32d831cecd037a8154a1`, lines 39–84) as the conjunction:
$$\text{dead\_code}(s, t) \triangleq \text{elim}(s, t) \land \text{unique}(s) \land \text{closed}(t)$$
where rule `elim_delete_let` requires every eliminated let-binding to satisfy `pure_binding []`.

Inspecting the decision procedure in `src/Language/PlutusIR/Transform/DeadCode/Decide.v` (blob `ebded9229af3833934b759f6996f31a383f26a1c`, lines 31–34, 59–71) and its soundness proof in `src/Language/PlutusIR/Transform/DeadCode/DecideSound.v` (blob `95a0873b9ebdf3ee4d2bd3281fc5c1ead581d49a`, lines 23–24, 33–48, 177–185, 201–276) establishes two gaps:
1. `DecideSound.v` proves `dec_elim_Term s t = true -> elim s t` (only the first conjunct of `dead_code(s, t)`), and semantic preservation from `elim` to operational equivalence is left outside the paper's mechanized scope.
2. `sound_dec_elim_Term` depends on `sound_dec_pure_binding` in `src/Language/PlutusIR/Analysis/Purity.v` (blob `19d151e814725bae0d6d49d918f075ce925a7d17`, lines 24–26, 44–57, 77–103), which is terminated with `Admitted` (alongside admitted value-check lemmas in `src/Language/PlutusIR/Analysis/Value.v`, blob `1666903f2244d5a658db523fc6528081b207c4ee`).

#### 2. Concrete Strict-`Error` Counterexample to the Admitted Purity Lemma

Direct constructor inversion yields a counterexample to the admitted `sound_dec_pure_binding` lemma (`support/plutus-inductive-pass-certificates-scp-2024/purity_witness.py` and `support/plutus-inductive-pass-certificates-scp-2024/purity-results.json`):
- Let `b = TermBind Strict vd (Error T)` for any variable declaration `vd` and type `T`.
- Evaluating `Purity.dec_pure_binding [] b` reduces to `Value.dec_value (Error T)`, which calls `dec_value' 0 (Error T)` and returns `true`.
- However, any derivation of `pure_binding [] b` for a `Strict` binding requires `is_pure [] (Error T)`. The value constructor of `is_pure` explicitly requires `~ is_error t`, which `IsError : is_error (Error T)` refutes, and the remaining `is_pure` constructors apply only to variables/applications.
- Thus `dec_pure_binding [] (TermBind Strict vd (Error T)) = true` while `pure_binding [] (TermBind Strict vd (Error T))` is unprovable, allowing `dec_elim_Term` to accept deletion of a strict error binding.

#### 3. Five-Component Anneal Pass-Certificate Interface

To prevent admitted helpers or unverified side conditions from silently entering a pass certificate, an Anneal pass-certificate boundary for pass $i$ must check five distinct components: (1) **Endpoints** (exact before/after ASTs and configuration identity), (2) **Transformation Derivation** ($\text{Rel}_i(\text{before}, \text{after})$), (3) **Admissibility Witnesses** (checked scope, binder uniqueness, effect/purity, guard, and frame obligations), (4) **Semantic Theorem** (connecting $\text{Rel}_i$ + admissibility to the required behavioral relation, including first-bad-step reflection for safety claims), and (5) **Assumption Closure** (auditing the transitive kernel environment so no `Admitted`/`sorry` or unverified axiom is reachable).

---

### Part VI: Guarded Model Certificates and Nonfailure Reflection in AutoCorres (PLDI 2014)

#### 1. AutoCorres Word and Heap Abstraction Propositions

Greenaway, Lim, Andronick, and Klein (PLDI 2014, DOI `10.1145/2594291.2594296`, §§2, 3.3, 4.2–4.4) translate C (imported into Simpl) through progressive abstraction layers in Isabelle/HOL, generating LCF correspondence theorems for each C function:
- **Word abstraction (§3.3, PDF p. 4):**
  $$P(s) \land \text{NF}(A(s)) \implies \text{NF}(C(s)) \land \forall(r, t) \in \text{Out}(C(s)).\, (\text{mapNormalException}(rx, ex, r), t) \in \text{Out}(A(s))$$
- **Heap abstraction (§4.4, PDF p. 7):**
  $$\text{NF}(A(\text{st}(s))) \implies \text{NF}(C(s)) \land \forall(r, t) \in \text{Out}(C(s)).\, (r, \text{st}(t)) \in \text{Out}(A(\text{st}(s)))$$

Here $\text{NF}(\cdot)$ negates the nondeterministic state monad's failure flag, and $\text{st}(s)$ projects the raw byte-level C heap into typed abstract heaps only when type tags, alignment, non-nullness, and non-wrapping footprints hold (unsigned-to-natural word abstraction similarly inserts overflow guards). Because $\text{NF}(A(\text{st}(s))) \implies \text{NF}(C(s))$ is part of the theorem conclusion, proving that the abstract model $A$ never fails immediately proves that the concrete program $C$ never triggers any modeled C undefined behavior or guard failure.

#### 2. Four-Obligation Source-to-Model Correspondence Rule for Anneal

Matching AutoCorres's nonfailure reflection against Anneal's admission design (`google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, `verification/aeneas/ADMISSION_DESIGN.md` blob `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf`, lines 134–276, 520–604; `anneal/lean/README.md` blob `9799e4c04818c085ac9b3e95bb79dc7ddbe78cc5`, lines 3–34), a sound program-to-model certificate between an imported operational program $S$ and an executable functional model $M$ under state relation $\text{Rel}$ requires four properties:
1. **Entry Coverage:** Every concrete entry state permitted by the public Rust signature has at least one $\text{Rel}$-related model entry state.
2. **Normal-Step Preservation:** Every safe concrete execution step has a $\text{Rel}$-related model transition preserving required observations and the caller's frame.
3. **First-Bad-Step Exposure (Failure Reflection):** From any $\text{Rel}$-related state reached prior to the first forbidden/UB concrete step, that forbidden concrete step forces model failure before execution continues (without assuming whole-invocation safety as a premise).
4. **Progress / Termination Bridge:** Any erased concrete steps carry a well-founded measure sufficient for total-correctness contracts (as required in AutoCorres's list-reversal case study, §5.2, PDF p. 9).

---

### Part VII: Memory-to-Value Refinement and Physical Layout Meaning in Cogent and Dargent (2021–2023)

#### 1. Cogent Value/Update/C Refinement vs. Dargent Layout Accessor Certificates

- **Cogent (O'Connor et al., JFP 2021 e25, DOI `10.1017/S095679682100023X`, Theorem 4.3, Definition 5.1, Generated Theorem 5.7, PDF pp. 34–35, 43–50):** Connects a pure functional embedding, value semantics, imperative update semantics, and monadic C via a store-typing relation $\text{Rel}(\mu, \sigma)$ with writable-footprint framing and concrete nonfailure:
  $$\text{TypedFootprint}(U, \mu) \land \text{Rel}(\mu, \sigma) \implies \text{NF}(P(\sigma)) \land \forall(c, \sigma') \in \text{Out}(P(\sigma)).\, \exists u, \mu'.\, \text{UpdateEval}(U, \mu, e, u, \mu') \land \text{Rel}(\mu', \sigma') \land \text{ValueRel}(u, c)$$
- **Dargent (Chen et al., POPL 2023 article 47, DOI `10.1145/3571240`, §§3.4, 4.1–4.5, PDF pp. 12–14, 17–19):** Refines high-level records into custom packed bit/word layouts via generated C getters and setters, discharging algebraic read-after-write and cross-field frame laws:
  $$\text{ValueRel}(x, v) \implies \text{ValueRel}(x, \text{get}_a(\text{set}_a(\text{arr}, v))), \qquad a \neq b \implies \text{get}_a(\text{set}_b(\text{arr}, v)) = \text{get}_a(\text{arr})$$
  Crucially, Dargent also requires a separate physical-format correspondence theorem relating $\text{get}_b(\text{arr})$ to the declarative layout specification `uval_from_array(type, layout, arr)` (while explicitly noting in §4.4, PDF p. 18: *"We have not yet done the same for setters"*, proving outside-field bit preservation instead).

#### 2. Finite Layout and Padding-Initializedness Witnesses (`layout_witness.py`)

Executing the deterministic finite witness (`support/cogent-dargent-memory-value-layout-certificates-2021-2023/layout_witness.py` and `support/cogent-dargent-memory-value-layout-certificates-2021-2023/layout-results.json`, paired with `verification/aeneas/SEMANTICS.md` blob `d89909750724dbafb76715e673626023b6cd49fd`) demonstrates two separation facts over all 16 values of a 4-bit word holding two 2-bit fields:
1. **Algebraic laws do not fix physical layout:** A swapped accessor family that exchanges the physical bit offsets of the two 2-bit fields satisfies 100% of same-field round-trip and distinct-field frame laws across all 4-bit words and 2-bit field values, yet fails the independent physical-offset specification at word `1`.
2. **Payload decoders vs. padding initializedness:** Modeling a 2-byte struct (1 initialized payload byte + 1 initialized padding byte) across a transfer that preserves the payload value while forgetting padding initializedness satisfies payload-only decoding before and after the transfer, but fails a subsequent full-byte-slice read guard—showing why runtime byte-transfer certificates must track byte initializedness, provenance, and access authority beyond pure mathematical decoders.

---

### Part VIII: Property-Proof Translation and Independent Specification Meaning (2006–2024)

#### 1. Barthe's Certificate Translation (SAS 2006) and PotPie's Specification Soundness (ITP 2024)

- **Certificate Translation (Barthe, Grégoire, Kunz, & Rezk, SAS 2006, LNCS 4134, pp. 301–317, DOI `10.1007/11823230_20`, §§1–4, 6):** Formalizes translating a source proof certificate $c$ for program $p$ and property $\phi$ across RTL compiler optimizations into a target certificate:
  $$\text{Certifies}(c, p, \phi) \implies \text{Certifies}(T_{\text{cert}}(c), T_{\text{code}}(p), T_{\text{spec}}(\phi))$$
  using certified static-analysis facts in the policy logic and ghost variables for eliminated registers.
- **PotPie Proof Compiler (Seo et al., ITP 2024 article 33, DOI `10.4230/LIPIcs.ITP.2024.33`, Definitions 3–5, Table 1, §§3.1–3.2, 5–7; repository `uwplse/potpie@a57f960958901dee3b8075be0a312d6a194be456`, version `v0.5`):**
  - In `Imp_LangTrick/Stack/StkHoareTree.v` (blob `4cd9167805e89beff2690ae606d42e4109fec660`, lines 61–135, 218–227), `valid_tree_can_construct_hl_stk` converts a validated tree certificate (`stk_valid_tree`) into a target Hoare logic derivation indexed by the target precondition, command, and postcondition.
  - In `Imp_LangTrick/ProofCompiler/ProofCompilerCodeCompAgnostic.v` (blob `4a0b9a379be26a92baf77738d6d01317d9c32a36`, lines 1270–1308, `induction_P`, `hl_compile`, `proof_compiler`) and `Imp_LangTrick/ProofCompiler/ProofCompilableCodeCompiler.v` (blob `0a4727e0218f726cbaec72dba199769d807da8e7`, lines 509–593, 634–665), transporting the proof requires an explicit **specification soundness** bi-implication on related source stores and target stacks:
    $$\text{source\_state} \models P \iff \text{target\_state} \models T_{\text{spec}}(P)$$
    plus substitution commutation and target expression purity. (`README.md` blob `3e5c3d571a0f26c2b0dfd114e99c8a82c78f854a`, lines 30–65, also warns users to distinguish kernel-checked `stk_valid_tree` certificates from the fallback boolean checker and to verify that the certified triple matches the intended specification.)

#### 2. Finite Specification-Meaning Witness (`specification_witness.py`)

Executing `support/property-proof-translation-specification-meaning-2006-2024/specification_witness.py` (`support/property-proof-translation-specification-meaning-2006-2024/specification-results.json`) exhibits three finite separation cases:
1. **Legitimate selected-property preservation:** Source and target both satisfy `x = 0` while differing on an unobserved variable `y`.
2. **Correlated code + postcondition mutation:** Source `x = 1` is mistranslated to target `x = 2` while postcondition `x = 1` is mistranslated to `True`; the target proof is valid for the generated triple, but an independent specification-meaning check rejects `T_spec(P)`.
3. **Precondition strengthening to `False`:** Translating the entry precondition to `False` makes the target Hoare triple vacuously valid while silently excluding all valid callers.

---

### Part IX: Refinement Policy and Safety Direction Comparison Across Compiler Families

#### 1. Comparative Taxonomy of Refinement Direction, Exception Allowances, and Ownership Safety

Comparing primary theorem statements across eight compiler/validation families (`support/refinement-policy-and-safety-direction-comparison/relation_endpoint_witness.py` and `support/refinement-policy-and-safety-direction-comparison/relation-endpoint-results.json`) isolates when target verification does—and does not—imply source safety:

| System / Source | Formal Relation & Direction | Exceptional / UB / Resource Treatment | Reflects Target Safety to Source UB-Freedom? |
| --- | --- | --- | --- |
| **Alive2** (PLDI 2021, DOI `10.1145/3453483.3454030`; `AliveToolkit/alive2@5d0eb277235b73f71000501c3a4f5ab9b2586915`, `README.md` blob `372a07fc19b0967be02217c01302a59820a7b7d6`) | Forward LLVM refinement ($\text{src} \sqsupseteq \text{tgt}$) within loop/resource bounds; intraprocedural only | Source UB allows any target state; source poison allows poison or any value; target nondeterminism may narrow | **No:** a safe target refines an unsafe (UB) source |
| **Trivet** (`arXiv:2609.19583v1`, §2.1 Def. 2.1, §§3.3–3.4) | Kernel-checked Lean proof of $\text{src} \sqsupseteq \text{tgt}$ for restricted straight-line / single-backedge-loop LLVM IR | Excludes `undef`, memory operations, and floats; immediate source UB permits arbitrary target behavior | **No:** forward optimization refinement allows erasing source UB |
| **CryptOpt + Fiat Crypto** (`arXiv:2211.10665v3`, §§6.1–6.4; `0xADE1A1DE/CryptOpt@c089d8ce3cace748a0a22e25d7adfbf2cfc6a883` blob `dabb2871b3dda26ebef571e7d71d12691ecda290`; `mit-plv/fiat-crypto@b4ad623c6a5bde0c71169493963a308c612fce3f`) | E-graph symbolic equivalence over straight-line Fiat IR and x86-64 assembly | Proved symbolic interpreter connects expressions to modeled straight-line instruction execution | Equivalence holds for modeled straight-line assembly instructions; random optimizer is outside TCB |
| **Jitterbug** (OSDI 2020, §4.1 Def. 1, §4.2 Thm. 1, §§6–7; `uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d` blob `c4f57da601d1ee124913f16efd14f651ef88bd95`) | Conditional trace/return-value preservation assuming safe source eBPF program and well-formed JIT context | Source safety (termination without UB) is an explicit *premise*; Rosette/SMT verifies DSL JITs | **No:** assumes source safety rather than proving it |
| **EquiVM** (`arXiv:2607.26306v1`, §5 Fig. 9 `runtimeEquiv`) | Universal quantification over related EVM/spec states and bounded calldata with bytecode refinement | Explicitly permits out-of-gas exceptions and shared dispatch/decode rejections; termination is separate | Refinement is relative to explicit out-of-gas/revert allowances |
| **Owlang** (`arXiv:2510.10015v1`, §5 Theorems 5.1–5.2) | Open backward simulation (Thm. 5.1) + open ownership safety theorem (Thm. 5.2) under interface `Iown` and calling convention `RRA` | Combines source partial safety (ignoring memory errors) with ownership checking (`Iown`) to conclude total source + target safety | **Yes, for memory safety within Owlang's modeled fragment**, because Theorem 5.2 supplies a separate ownership-checking safety proof |
| **RustCompCert** (`arXiv:2602.07455v1`, §2 & footnote 2) | Ongoing-work 3-page preprint writing $\llbracket \text{target} \rrbracket \leqslant \llbracket \text{source} \rrbracket$ ("backward simulation") while prose states source behaviors are included in target behaviors | Unresolved equation-vs.-prose inclusion direction conflict; footnote 2 treats integer division by zero as an example in its partial-safety account (whereas normative Rust panics per `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` `src/expressions/operator-expr.md#L403`) | Cannot be used as an uninspected load-bearing safety-direction premise until resolved against a mechanized artifact |
| **Computing Correctly with Inductive Relations** (PLDI 2022, §3 Fig. 1, §6.3) & **Vellvm** (`vellvm/vellvm@4c6db50077cbc0df3fb3156c0570129201cc35f3` blob `08d549602a4f146e6f2016013c2fdb82741be1ff`) | Fuel-bounded partial decision procedures (`Some true` / `Some false` / `None`) derived with soundness/completeness proofs for inductive relations | Proves the checker matches the inductive relation, not that the inductive relation preserves program semantics | Checker derivation is orthogonal to semantic safety reflection |

#### 2. Exhaustive Four-Outcome Finite Witness (`relation_endpoint_witness.py`)

Running `support/refinement-policy-and-safety-direction-comparison/relation_endpoint_witness.py` over the four-outcome lattice (`UB`, `Poison`, `Val(0)`, `Val(1)`) confirms three discriminating facts:
1. A target returning `Val(0)` validly refines a source returning `UB` under $\text{src} \sqsupseteq \text{tgt}$, demonstrating that a proved-safe target under forward refinement can originate from an unsafe source.
2. A target returning `Val(1)` for a `Val(0)` source passes a coarse target-only "no-UB/no-Poison" safety policy while violating source-to-target value refinement.
3. A transformation matching on inputs `0..3` and diverging on input `4` passes bounded checking of depth 4 while failing unbounded equivalence.

## Boundaries

- **No fresh upstream theorem-prover or compiler builds:** None of the external Coq/Rocq, Isabelle/HOL, HOL4, Lean, Rosette/Z3, LLVM, Alive2, Crellvm, Plutus, AutoCorres, Cogent/Dargent, PotPie, CryptOpt, Jitterbug, EquiVM, Owlang, or Trivet toolchains was built or executed. Execution evidence in this package is strictly limited to the four deterministic, self-contained Python finite witnesses (`purity_witness.py`, `layout_witness.py`, `specification_witness.py`, and `relation_endpoint_witness.py`).
- **Pinned artifact findings vs. current upstream projects:** The admitted rules in `snu-sf/crellvm@668249b88756233f96b3ef21f12993501a348afc` and the admitted purity lemma (`sound_dec_pure_binding`) with its strict-`Error` counterexample in `basetunnel/2022-scp-translation-relations@72e619f3243498a612d8c6c5090b88117c404489` are exact findings about those inspected research artifacts, not claims about current production LLVM or Plutus compilers.
- **Optimization refinement vs. source-safety reflection:** Forward compiler refinement ($\text{Beh}(\text{target}) \subseteq \text{Beh}(\text{source})$ or $\text{src} \sqsupseteq \text{tgt}$) is sound for optimizing already-safe programs, but cannot be used in reverse to infer Rust source UB-freedom from a verified target model unless paired with an explicit nonfailure-reflection implication ($\text{NF}(\text{model}) \implies \text{NF}(\text{source})$, as in AutoCorres) or an independent source ownership/safety theorem.

## Evidence

### 1. Translation Validation & Proof-Producing Compilation Primary Literature
- **TACAS 1998:** A. Pnueli, M. Siegel, and E. Singerman, “Translation Validation,” *TACAS 1998*, LNCS 1384, pp. 151–166, DOI `10.1007/BFb0054170`.
- **POPL 1997 & PLDI 2000:** G. C. Necula, “Proof-Carrying Code,” *POPL 1997*, pp. 106–119, DOI `10.1145/263699.263712`; “Translation Validation for an Optimizing Compiler,” *PLDI 2000*, pp. 83–94, DOI `10.1145/349299.349314`.
- **ENTCS 2007:** J. O. Blech and A. Poetzsch-Heffter, “A Certifying Code Generation Phase,” *ENTCS* 190(4), 2007, pp. 65–82, DOI `10.1016/j.entcs.2007.09.008`.
- **POPL 2008:** J.-B. Tristan and X. Leroy, “Formal Verification of Translation Validators: A Case Study on Instruction Scheduling Optimizations,” *POPL 2008*, pp. 17–27, DOI `10.1145/1328438.1328444`.
- **PLDI 2021 & CAV 2021 (Alive2):** N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, and J. Regehr, “Alive2: Bounded Translation Validation for LLVM,” *PLDI 2021*, pp. 65–79, DOI `10.1145/3453483.3454030`; J. Lee, D. Kim, C.-K. Hur, and N. P. Lopes, “An SMT Encoding of LLVM's Memory Model for Bounded Translation Validation,” *CAV 2021*, DOI `10.1007/978-3-030-81688-9_35`; `AliveToolkit/alive2@5d0eb277235b73f71000501c3a4f5ab9b2586915` (`README.md` blob `372a07fc19b0967be02217c01302a59820a7b7d6`).
- **FLOPS 2022 & SCP 2024 (Plutus):** J. O. G. Krijnen, M. M. T. Chakravarty, G. Keller, and W. Swierstra, “Translation Certification for Smart Contracts,” *FLOPS 2022*, LNCS 13215, pp. 94–111, DOI `10.1007/978-3-030-99461-7_6`, and *Science of Computer Programming* 233 (2024) 103051, DOI `10.1016/j.scico.2023.103051`.

### 2. Certifying Translations, Symbolic Execution, and Pinned Repository Sources
- **Katamaran, CakeML, Lean4Lean, hax, and Electrolysis:**
  - Katamaran: *ICFP 2022*, DOI `10.1145/3547628` (Lemmas 2.1, 5.1, 6.1; §6.2/Table 1).
  - CakeML backend manuscript: `https://cakeml.org/jfp19.pdf` (2018-11-19, 59 pages, §§2.3–2.4, 10–12).
  - Lean4Lean: `arXiv:2403.14064v3`.
  - `cryspen/hax@cc6da074ca754ca9d406ec922daad3221aacbce5`: `docs/dev/architecture.md` (blob `4491c64185044fc3dce318b4b02031be9a88b0a3`), `docs/manual/lean/quick_start.md` (blob `715bd5bc5cfa4c96d60bdb0ff5b8552ec812b1e2`), `docs/manual/lean/tutorial/panic-freedom.md` (blob `c5622ab470f2e7164ca16b09fad41864c04e1acb`).
  - `Kha/electrolysis`: `README.md` (blob `670746012e99efc7b239bc5cd41f9ee2d967997b`).
- **Crellvm (`snu-sf/crellvm@668249b88756233f96b3ef21f12993501a348afc`, tree `0b62b6ab302501596f06f4b94181cc1c82df6aa7`, DOI `10.1145/3192366.3192377`):**
  - `coq/proof/Adequacy.v` (blob `ecfae4591dd0975edc9edac1004385145a62ee3e`), `coq/proof/Behavior.v` (blob `ff32147504d3ae7f8fe479d038d6c54c5664c907`), `coq/proof/SoundInfrules.v` (blob `5c3d417c392d71c6fa8cfe7ec2b4e4071f5f3596`), `coq/proof/TODOProof.v` (blob `c6f0050509b787b90504039c36a6aa52699657c2`), `coq/def/Validator.v` (blob `e56bd51e4c621ee70c51a824bf118c0a8938ad1a`), `ocaml/main.ml` (blob `d5f842d591b010276e7b9f6fcbfcef277a3dfb43`), `Makefile` (blob `5830bda3dc2ea453c75fe5028731dbff8f01c7f6`).
- **Plutus Translation Relations (`basetunnel/2022-scp-translation-relations@72e619f3243498a612d8c6c5090b88117c404489`):**
  - `src/Language/PlutusIR/Transform/DeadCode.v` (blob `65da05418c6a310e2b4c32d831cecd037a8154a1`), `src/Language/PlutusIR/Transform/DeadCode/Decide.v` (blob `ebded9229af3833934b759f6996f31a383f26a1c`), `src/Language/PlutusIR/Transform/DeadCode/DecideSound.v` (blob `95a0873b9ebdf3ee4d2bd3281fc5c1ead581d49a`), `src/Language/PlutusIR/Analysis/Purity.v` (blob `19d151e814725bae0d6d49d918f075ce925a7d17`), `src/Language/PlutusIR/Analysis/Value.v` (blob `1666903f2244d5a658db523fc6528081b207c4ee`).
- **AutoCorres, Cogent, Dargent, SAS 2006, and PotPie (`uwplse/potpie@a57f960958901dee3b8075be0a312d6a194be456`):**
  - AutoCorres: Greenaway et al., *PLDI 2014*, DOI `10.1145/2594291.2594296`.
  - Cogent: O'Connor et al., *JFP 2021* e25, DOI `10.1017/S095679682100023X`.
  - Dargent: Chen et al., *POPL 2023* article 47, DOI `10.1145/3571240`.
  - Certificate Translation: Barthe et al., *SAS 2006*, LNCS 4134, DOI `10.1007/11823230_20`.
  - PotPie: Seo et al., *ITP 2024* article 33, DOI `10.4230/LIPIcs.ITP.2024.33`; `Imp_LangTrick/Stack/StkHoareTree.v` (blob `4cd9167805e89beff2690ae606d42e4109fec660`), `Imp_LangTrick/ProofCompiler/ProofCompilableCodeCompiler.v` (blob `0a4727e0218f726cbaec72dba199769d807da8e7`), `Imp_LangTrick/ProofCompiler/ProofCompilerCodeCompAgnostic.v` (blob `4a0b9a379be26a92baf77738d6d01317d9c32a36`), `README.md` (blob `3e5c3d571a0f26c2b0dfd114e99c8a82c78f854a`).
  - Anneal comparison baseline (`google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`): `anneal/lean/README.md` (blob `9799e4c04818c085ac9b3e95bb79dc7ddbe78cc5`), `verification/aeneas/SEMANTICS.md` (blob `d89909750724dbafb76715e673626023b6cd49fd`), `verification/aeneas/ADMISSION_DESIGN.md` (blob `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf`).
- **CryptOpt, Jitterbug, Trivet, EquiVM, Owlang, RustCompCert, and Vellvm:**
  - CryptOpt (`arXiv:2211.10665v3`, DOI `10.5281/zenodo.7710435`, `0xADE1A1DE/CryptOpt@c089d8ce3cace748a0a22e25d7adfbf2cfc6a883` `Readme.md` blob `dabb2871b3dda26ebef571e7d71d12691ecda290`, `mit-plv/fiat-crypto@b4ad623c6a5bde0c71169493963a308c612fce3f`).
  - Jitterbug (*OSDI 2020*, `uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d` `README.md` blob `c4f57da601d1ee124913f16efd14f651ef88bd95`).
  - Trivet (`arXiv:2609.19583v1`), EquiVM (`arXiv:2607.26306v1`), Owlang (`arXiv:2510.10015v1`), RustCompCert (`arXiv:2602.07455v1`), Paraskevopoulou et al. (*PLDI 2022*), and Vellvm (`vellvm/vellvm@4c6db50077cbc0df3fb3156c0570129201cc35f3` `README.md` blob `08d549602a4f146e6f2016013c2fdb82741be1ff`).
- **Bundled Support Artifacts & Executable Finite Witnesses:**
  - `support/translation-validation-techniques-1998-2021/source-map.json`, `support/translation-validation-techniques-1998-2021/technique-matrix.json`
  - `support/proof-producing-versus-validating-translations-1997-2022/architecture-matrix.json`, `support/proof-producing-versus-validating-translations-1997-2022/source-map.json`
  - `evidence.json`, `coverage.json`, `primary-evidence.json`
  - `support/plutus-inductive-pass-certificates-scp-2024/purity_witness.py`, `support/plutus-inductive-pass-certificates-scp-2024/purity-results.json`
  - `support/cogent-dargent-memory-value-layout-certificates-2021-2023/layout_witness.py`, `support/cogent-dargent-memory-value-layout-certificates-2021-2023/layout-results.json`
  - `support/property-proof-translation-specification-meaning-2006-2024/specification_witness.py`, `support/property-proof-translation-specification-meaning-2006-2024/specification-results.json`
  - `support/refinement-policy-and-safety-direction-comparison/relation_endpoint_witness.py`, `support/refinement-policy-and-safety-direction-comparison/relation-endpoint-results.json`

## Revalidation

1. **Replay Finite Witnesses:** From the package directory, execute:
   - `python3 -B support/plutus-inductive-pass-certificates-scp-2024/purity_witness.py`
   - `python3 -B support/cogent-dargent-memory-value-layout-certificates-2021-2023/layout_witness.py`
   - `python3 -B support/property-proof-translation-specification-meaning-2006-2024/specification_witness.py`
   - `python3 -B support/refinement-policy-and-safety-direction-comparison/relation_endpoint_witness.py`
   and verify that each script reproduces the exact JSON results in `purity-results.json`, `layout-results.json`, `specification-results.json`, and `relation-endpoint-results.json`.
2. **Audit Candidate Validators and Pass Certificates:** For any proposed Anneal validator or pass-refinement certificate, verify six mandatory gates:
   - **Direction & Failure Reflection:** Does the theorem reflect model safety back to concrete source nonfailure ($\text{NF}(\text{model}) \implies \text{NF}(\text{source})$), or only prove forward optimization refinement ($\text{Beh}(\text{target}) \subseteq \text{Beh}(\text{source})$)?
   - **Independent Specification Meaning:** Is $T_{\text{spec}}(P)$ checked against an independently pinned source contract ($\text{source\_state} \models P \iff \text{target\_state} \models T_{\text{spec}}(P)$)?
   - **Independent Layout Meaning:** Are byte/bit layout accessors verified against an independent declarative layout specification rather than only getter/setter round-trip algebra?
   - **Semantic Consequence:** Is the syntactic pass relation $\text{Rel}_i(s, t)$ connected to a proved semantic-preservation theorem?
   - **Assumption Closure:** Does `Print Assumptions` / Lean kernel axiom auditing confirm zero `Admitted`/`sorry` helpers in the transitive dependency cone?
   - **Fail-Closed Wrapper:** Do `Some false`, `None`, solver `unknown`, fuel exhaustion, and unsupported constructs all fail closed rather than exiting with ordinary success?
