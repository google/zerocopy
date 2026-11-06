# CompCert, seL4, and Project Everest: Compiler-Pass Composition, Proof-Maintenance Architectures, Nontermination, Operational vs. Functional Semantics, and Environmental Effects

## Summary

Verified compiler correctness and long-lived system verification are compositional only when every translation stage and abstraction layer exports a semantic relation that downstream proofs can compose and maintain. Across CompCert 3.18 (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`), seL4 (`seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5` and `seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b`), Project Everest (`hacl-star/hacl-star@504c2987452f87fe44bce9b9f12e19d6e051761f`, `FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`, and `project-everest/everest@2a3f67dab56be02d1793b2801ef08f368423a3ac`), Aeneas (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `nightly-2026.06.03`, together with the ICFP 2022 and ICFP 2024 semantic foundations), and coinductive interaction/choice-tree formalisms (Interaction Trees, POPL 2020; Choice Trees, POPL 2023), six structural rules govern end-to-end soundness and proof maintenance:

1. **Vertical Pass Composition and Verified Validators (CompCert 3.18 & Tristan–Leroy POPL 2008):** CompCert 3.18 proves forward simulations for individual compiler passes (`common/Smallstep.v`), composes them via `compose_forward_simulations` using lexicographic well-founded stuttering orders, and derives its whole-compiler backward simulation (`driver/Compiler.v`, `transf_c_program_correct`) through explicit side conditions: source receptiveness (`receptive L1`), target determinacy (`determinate L2`), event factoring (`factor_forward_simulation`), `single_events L3` for `compose_backward_simulation`, and a separate strategy-to-language backward simulation (`c_semantic_preservation`). Pass failure composes by failing closed (`transf_c_program p = OK tp`), and disabled optional passes supply an explicit `forward_simulation_identity` via `match_if_simulation`. Complementarily, Tristan and Leroy (POPL 2008, DOI `10.1145/1328438.1328444`) show that an unverified optimization pass $C : L_1 \to L_2 + \text{Error}$ wrapped with a sound boolean validator $V : L_1 \times L_2 \to \text{bool}$ ($V(c_1, c_2) = \text{true} \implies c_1 \le c_2$) exports the exact pass-level semantic-preservation interface required by `compose_forward_simulations`, provided $V$ checks both final symbolic values and definedness conditions.
2. **Proof-Maintenance Architectures (seL4, CompCert, and Project Everest, 2009–2026):** Mature verification systems reduce proof-maintenance cost by stabilizing the semantic interfaces that proofs depend on, while explicitly managing five distinct propagation axes: (a) semantic-contract changes, (b) proof-facing representation/normal-form changes, (c) automation/toolchain changes, (d) generated-artifact provenance, and (e) trusted-boundary changes. In seL4, strengthening `numDomains` to 256 (`bce918b83bd9deaf91c3b9e7c3678929c4ad5799`) broke zero downstream proofs because existing obligations already implied the bound, whereas reserving VMID 0 on AArch64 (`589b63f232d3c042cc7fc41f5fd304f2e7114e7a`, 9 files) and reserved ASIDs on ARM/ARM_HYP (`411e76099fff81c09cd4eb6619cef13d8d9bb6cf`, 36 files) required cross-layer invariant updates, and extensionally equivalent `init`/`butlast` definitions (`9ae6b8106f5ef4dd14cb0e9543d9fe14101bbc4f`) were deliberately kept separate to preserve simplifier stability. In CompCert, strengthening memory injections for negative-offset metadata (`2f5e3204c48510f94c91699c64dee8bd18cd2b75`) and refactoring `Senv.inject`/`Genv.inject`/`Val.inject_ptr_flat` (`59b473374b23660f587230969b48ff407241dc19`, 16 files) crossed pass proofs, while commit `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` restored `Events.meminj_preserve_globals` as a compatibility shim for VST. In Project Everest / HACL*, modular Low* abstractions and code specialization scaled HACL* past 100,000 lines of verified source (ICFP 2023, DOI `10.1145/3607844`), while repository maintenance pins Z3 4.8.5 (`43ffda45c9eb03ef2661f6b89c47f1d5a735a502`), F*/KaRaMeL revisions, proof hints (`ecbf1aaa83016c0b3e67c49c0f962afcdd3986fa`), and version-controlled `dist/` C/ASM outputs (`ee6ac4d2b58fb3da421086e778132800fb3f0e37`).
3. **Current-Source Continuity Across the Six Upstream Repositories:** Official-source inspection (`support/matrix.json` and `support/official-source-observation.json`) confirms that five of the six upstream default branches (`seL4/l4v` `master`, `seL4/verification-manifest` `master`, `hacl-star/hacl-star` `main`, `FStarLang/karamel` `master`, and `project-everest/everest` `master`) remain at the exact pinned commits above, while `AbsInt/CompCert` `master` (`66a9fd06ef88619cc94765ca995a1018f7259b5c`) is four commits ahead of `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (touching only `cfrontend/CPragmas.ml`, `common/Switch.v`, `common/Switchaux.ml`, `cparser/Lexer.mll`, and `test`) with `VERSION`, `common/Smallstep.v`, and `driver/Compiler.v` retaining identical Git blob IDs (`v3.18` remains the latest official CompCert release).
4. **Reasoning About Nontermination (CompCert 3.18 vs. Aeneas):** Nontermination is an infinite semantic execution property—distinct from recursive/cyclic syntax and narrower than Rust's diverging expression (`!`, which includes finite panics in `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`). CompCert 3.18 (`common/Behaviors.v`, `driver/Complements.v`) separates silent divergence after a finite trace (`Diverges t` via coinductive `Forever_silent`) from reactive divergence with an infinite trace (`Reacts T` via `Forever_reactive`) and erroneous stuckness (`Goes_wrong`), transporting both infinite execution modes across forward and backward simulations. Aeneas (`nightly-2026.06.03`) assigns supported recursive functions a partial denotation via Lean `partial_fixpoint` with bottom `Result.div`, separating translation from termination proof (`WP.spec` sets `spec div P = False` to rule out `Result.div`), whereas conservative static flags (`can_diverge`) are not termination or divergence proofs and unconditional `NoBreak` loops are rejected at translation time.
5. **Operational Semantics vs. Functional Translation (Aeneas ICFP 2022/2024 vs. CompCert):** Operational semantics keeps state, memory, failure, divergence, nondeterminism, and observable traces explicit in execution relations, whereas functional translation (Aeneas ICFP 2022, DOI `10.1145/3547647`) functionalizes safe-Rust ownership and mutable borrows via backward functions so proofs use native theorem-prover functions. Functionalization simplifies the user proof surface without discharging the source-to-target semantic bridge: Aeneas 2024 (ICFP 2024, DOI `10.1145/3674640`) justifies the ownership-centric LLBC model operationally via simulation against a lower-level heap/address pointer semantics and symbolic execution soundness, while the production LLBC-to-Lean code generator remains a trusted translation stage unless paired with a proof or validator.
6. **Nondeterminism and Environmental Effects (CompCert Worlds, Interaction Trees, and Choice Trees):** Nondeterminism and environmental interactions are semantic structure that proofs must quantify over rather than silently collapsing to a single deterministic value. CompCert (`common/Events.v`, `common/Determinism.v`) models external calls relationally via `extcall_sem` (with `ec_receptive` and `ec_determ` up to matching traces) and separately instantiates deterministic environment responses via a coinductive `world`. Interaction Trees (POPL 2020, DOI `10.1145/3371119`) represent recursive impure programs via uninterpreted visible events interpreted by handlers up to weak bisimulation, while Choice Trees (POPL 2023, DOI `10.1145/3571254`) add explicit internal nondeterministic branching nodes alongside external events so internal choice and environment responses remain distinct under simulation and refinement.

## Applicability

This report synthesizes six primary verification-architecture analyses for the Anneal reference corpus:

- **Compiler-Pass Composition and Verified Validators:** CompCert 3.18 (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `common/Smallstep.v` and `driver/Compiler.v`) and Tristan & Leroy (POPL 2008, DOI `10.1145/1328438.1328444`), covering vertical pass simulation composition, stuttering well-foundedness, forward-to-backward simulation conversion, fail-closed compilation premises, and verified post-pass validation wrappers.
- **Proof-Maintenance Architectures (2009–2026):** `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, `seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b`, `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (and 2026 memory-injection history), `hacl-star/hacl-star@504c2987452f87fe44bce9b9f12e19d6e051761f`, `FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`, `project-everest/everest@2a3f67dab56be02d1793b2801ef08f368423a3ac`, and Ho, Fromherz, & Protzenko (ICFP 2023, DOI `10.1145/3607844`), analyzing how module contracts, abstraction layers, solver/prover pins, generated code, and compatibility shims govern proof repair.
- **Current-Source Review Across Upstream Repositories:** Exact comparison of the six upstream repositories and their GitHub release tags as observed on `2026-09-30` (`AbsInt/CompCert` `master` at `66a9fd06ef88619cc94765ca995a1018f7259b5c`), reconciling pinned source blobs and release ancestry.
- **Nontermination Semantics and Obligations:** CompCert 3.18 (`common/Behaviors.v`, `driver/Complements.v`, `common/Events.v`), Aeneas `nightly-2026.06.03` (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`), and the Rust Reference (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` for `nightly`).
- **Operational Semantics vs. Functional Translation:** Ho & Protzenko (ICFP 2022, DOI `10.1145/3547647`), Ho, Fromherz, & Protzenko (ICFP 2024, DOI `10.1145/3674640`), and CompCert 3.18 dynamic-semantics simulation chains, evaluated against Anneal's Charon-to-Aeneas-to-Lean pipeline (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`).
- **Nondeterminism and Environmental Effects:** CompCert 3.18 (`common/Events.v`, `common/Determinism.v`, `common/Behaviors.v`), Xia et al. (POPL 2020, DOI `10.1145/3371119`), and Chappe et al. (POPL 2023, DOI `10.1145/3571254`).

This package applies directly to Anneal's pipeline architecture (`Rust semantics -> Charon LLBC -> Aeneas Lean model -> Anneal proof obligations -> Lean kernel theorem`), obligation schema stability, fail-closed translation boundaries, and adequacy checklists for nontermination and effectful constructs.

## Findings

### Part I: Verified Compiler-Pass Composition in CompCert 3.18 and Verified Validators (POPL 2008)

#### 1. Pass Proofs Compose Through a Shared Semantic Interface and Lexicographic Stuttering Order

CompCert 3.18 represents pass correctness using simulations between formal small-step semantics (`common/Smallstep.v`). The generic composition theorem `compose_forward_simulations` has the shape:

```text
forward_simulation L1 L2
→ forward_simulation L2 L3
→ forward_simulation L1 L3
```

The theorem does not inspect either compiler pass's implementation algorithm; it composes only the semantic witnesses exported by their proofs. Because a forward simulation can match one source step with zero target steps when an internal transition stutters, simple relation transitivity on final values is unsound. CompCert pairs the two simulation indices, existentially retains an intermediate `L2` state, and constructs a lexicographic well-founded order whose first component transitively closes the first simulation's order and whose second component carries the second simulation's order. This well-founded measure rules out unsound preservation via infinite zero-step stuttering.

Basis: **source** — `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `common/Smallstep.v`, `compose_forward_simulations` (lines 1003–1043).

#### 2. Explicit Whole-Compiler Simulation Chaining and Optional-Pass Identity

In `driver/Compiler.v`, `cstrategy_semantic_preservation` (lines 344–416) repeatedly applies `compose_forward_simulations` across every transformation in the compilation pipeline: expression simplification, local simplification, `Csharpminor` and `Cminor` generation, instruction selection, RTL generation, inlining, register-related transformations, dead-code-related transformations, register allocation, linearization, label cleanup, stacking, and assembly generation.

Optional passes are gated by `match_if_simulation`: if an optional pass is enabled, the caller must supply its `forward_simulation` proof; if disabled, source and target languages coincide and the proof supplies `forward_simulation_identity`. Neither skipping a pass nor running a pass omits a proof obligation.

Basis: **source** — `driver/Compiler.v`, `cstrategy_semantic_preservation`, `match_if_simulation`; **documentation** — CompCert 3.18 manual, Chapter 1.

#### 3. Simulation Direction Conversion and Semantic Side Conditions at the Pipeline Boundary

CompCert's top-level theorem states a backward simulation from C semantics to assembly semantics, whereas `cstrategy_semantic_preservation` first assembles a forward simulation. The conversion in `common/Smallstep.v` (`forward_to_backward_simulation`, lines 1863 onward) requires explicit side conditions:

```text
forward_simulation L1 L2
receptive L1
determinate L2
→ backward_simulation L1 L2
```

In `driver/Compiler.v`, `cstrategy_semantic_preservation` first applies `factor_forward_simulation` (`common/Smallstep.v`, lines 2004 onward) so the event granularity matches, then supplies strong receptiveness for the atomic C strategy semantics and determinacy for assembly. Next, `c_semantic_preservation` (lines 419–434) composes the backward simulation from ordinary C semantics to the strategy semantics with the strategy-to-assembly backward simulation using `compose_backward_simulation` (`common/Smallstep.v`, lines 1566 onward), which additionally requires `single_events L3`.

Thus end-to-end pass composition requires four distinct proof steps:
1. Establish a compatible simulation relation for each pass;
2. Compose those relations in the direction supported by their generic theorem;
3. Discharge trace and progress side conditions (`receptive`, `determinate`, `single_events`, event factoring) needed to invert simulation direction; and
4. Connect the user-facing source language semantics to the internal semantics of the pass chain.

Basis: **source** — `common/Smallstep.v` (`forward_to_backward_simulation`, `compose_backward_simulation`, `factor_forward_simulation`) and `driver/Compiler.v` (`cstrategy_semantic_preservation`, `c_semantic_preservation`).

#### 4. Fail-Closed Compilation Premise and Verified Validator Wrappers

CompCert's whole-compiler theorem (`driver/Compiler.v`, `transf_c_program_correct`, lines 446–453) is conditional on successful compilation:

```text
transf_c_program p = OK tp
→ backward_simulation (Csem.semantics p) (Asm.semantics tp)
```

If any pass returns `Error`, no target program is produced and no semantic-preservation claim is emitted.

Tristan and Leroy (POPL 2008, DOI `10.1145/1328438.1328444`, §2.1 equations (1)–(2) and Theorem 1) use this exact fail-closed premise to integrate unverified optimization passes. Modeling an untrusted pass as $C : L_1 \to L_2 + \text{Error}$ and a validator as $V : L_1 \times L_2 \to \text{boolean}$, the validated wrapper returns $c_2$ when $C(c_1) = \text{OK}(c_2) \land V(c_1, c_2) = \text{true}$, and returns $\text{Error}$ otherwise. Theorem 1 proves that if validator acceptance implies the required semantic relation ($V(c_1, c_2) = \text{true} \implies c_1 \le c_2$), the wrapped pass is formally verified regardless of $C$'s internal heuristics. Validator incompleteness affects only compilation success, never soundness.

Critically, a validator replaces a pass proof only when it exports the *same required relation* ($\le$) expected by surrounding passes. In Tristan and Leroy's Mach instruction-scheduling validator (§2.2), symbolic evaluation tracks not only final symbolic state equations but also the set of operations whose definedness matters; otherwise a rescheduled block could compute identical final values on terminating runs while introducing a new division-by-zero or invalid memory access.

Basis: **source** — `driver/Compiler.v`, `transf_c_program_correct`; **published result** — Tristan and Leroy, POPL 2008, DOI `10.1145/1328438.1328444`, §2.1–2.2.

#### 5. End-to-End Composition Preserves Only the Weakest Boundary Contract and Separates Vertical from Horizontal Composition

When three translation stages establish binary relations `Rel_12`, `Rel_23`, and `Rel_34`, their conjunction does not establish an end-to-end theorem unless a generic theorem composes them or explicit bridge lemmas convert them to a common relation with all side conditions discharged. If `Rel_12` excludes unsupported source operations, `Rel_23` assumes termination, and `Rel_34` reasons only about normal-return pure values, the composed chain does not prove preservation of arbitrary source executions. For Anneal, each boundary leg in the chain (`composition-patterns.json`):

```text
Rust semantics
  --Rel_1--> Charon/LLBC
  --Rel_2--> Aeneas model / generated Lean
  --Rel_3--> Anneal proof obligations
  --Rel_4--> kernel-checked theorem
```

must explicitly record the established relation, its evidence, its assumptions, and its fail-closed rejection behavior.

Furthermore, CompCert 3.18's `separate_transf_c_program_correct` (`driver/Compiler.v`, lines 466 onward) demonstrates that vertical pass composition is distinct from horizontal module composition and linking: it establishes per-unit `match_prog` witnesses, transports them across linking via `link_list_compose_passes`, and only then applies whole-program semantic preservation.

Basis: **source** — `driver/Compiler.v`, `separate_transf_c_program_correct`; **derived** synthesis (`composition-patterns.json`).

---

### Part II: Proof-Maintenance Architectures Across seL4, CompCert, and Project Everest (2009–2026)

#### 1. Five Distinct Axes of Proof-Maintenance Propagation

Across seL4, CompCert, and Project Everest (`support/proof-maintenance-architectures-sel4-compcert-everest-2009-2026/maintenance-cases.json`), proof repair propagates along five distinct interfaces:

| Propagation Axis | Mechanism | Representative Empirical / Historical Case |
| --- | --- | --- |
| **1. Semantic-contract change** | A modified invariant, memory relation, or externally visible behavior invalidates downstream theorems that genuinely depend on it. | `seL4/l4v` reserved VMID 0 (`589b63f232d3c042cc7fc41f5fd304f2e7114e7a`, 9 files, +171/-93) and reserved ASID (`411e76099fff81c09cd4eb6619cef13d8d9bb6cf`, 36 files, +891/-589); CompCert negative-offset `free` memory injection (`2f5e3204c48510f94c91699c64dee8bd18cd2b75`, 374 lines). |
| **2. Proof-facing representation change** | Denotational semantics remain equivalent while normal forms, rewrite rules, lemma shapes, or simplifier behavior change. | `seL4/l4v` commit `9ae6b8106f5ef4dd14cb0e9543d9fe14101bbc4f` proved `HaskellLib` `init` equivalent to Isabelle `butlast` but deliberately retained `init` to avoid breaking simplifier-dependent proof scripts. |
| **3. Automation / toolchain change** | Theorem prover, SMT solver, compiler, or proof-hint format changes alter how identical obligations discharge. | `seL4/l4v` 10-commit Isabelle2025-2 migration series; `hacl-star` commit `43ffda45c9eb03ef2661f6b89c47f1d5a735a502` reverting to Z3 4.8.5 due to solver performance regressions; Vale proof stabilization (`bfb6db8ecc67f36754d257500c2a0f1e2f6be609`). |
| **4. Generated-artifact provenance** | High-level source and proof remain aligned while generated C, assembly, manifests, or proof hints require synchronized regeneration and identity control. | `hacl-star` commits `ecbf1aaa83016c0b3e67c49c0f962afcdd3986fa`, `ee6ac4d2b58fb3da421086e778132800fb3f0e37`, and `504c2987452f87fe44bce9b9f12e19d6e051761f` regenerating hints and `dist/` C/ASM outputs; `seL4/l4v` Makefile/`run_tests` regeneration of C/design specs. |
| **5. Trusted-boundary change** | Moving a component into or out of the proved path alters the final assurance assumptions even when runtime behavior is unchanged. | seL4 FAQ explicit assumptions for boot code and machine-interface functions vs. PLDI 2013 binary validation; KaRaMeL `DESIGN.md` unverified internal Low*-subset invariant. |

Basis: **source/history** and **derived** taxonomy (`support/proof-maintenance-architectures-sel4-compcert-everest-2009-2026/maintenance-cases.json`).

#### 2. seL4 Layered Refinement, Invariant Scope, and Configuration-Controlled Replay Manifests

In `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5` (`README.md` blob `03421c4b7db4e9756efde5f46f19e60970fc7288`, `docs/setup.md` blob `c20d7ba4fb16845977b4d205d725cb6c52a64eb9`), the proof stack interposes an abstract functional specification, a Haskell executable design model, a machine interface, automatically imported C semantics, and capDL specifications, connected by separate abstract-invariant, abstract-to-design, design-to-C, access-control, information-flow, and binary-refinement layers.

- **Zero-propagation boundary strengthening:** Commit `bce918b83bd9deaf91c3b9e7c3678929c4ad5799` updated `numDomains` to permit 256 domains in `spec/machine/Kernel_Config_Lemmas.thy` (2 insertions, 1 deletion, 1 file) with zero downstream proof breakage because existing downstream obligations already consumed a proposition implied by the updated bound.
- **Cross-layer invariant propagation and reuse:** Reserving VMID 0 on AArch64 (`589b63f232d3c042cc7fc41f5fd304f2e7114e7a`, 9 files, +171/-93) introduced a global invariant that the next VMID is never the reserved value across invariant, refinement, C-refinement, and information-flow layers; the subsequent ARM/ARM_HYP reserved-ASID update (`411e76099fff81c09cd4eb6619cef13d8d9bb6cf`, 36 files, +891/-589) repaired analogous obligations while reusing the AArch64 proof setup.
- **Configuration-controlled replay (`seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b`):** `README.md` (blob `2b3f4a193bbb3012f9b7711f06bbb3dc2c98e352`) separates `default.xml` and `mcs.xml` (latest CI-tested working combinations of proof, kernel, and tool hashes), development manifests, and official release manifests (which also pin the exact Isabelle/HOL release). Ten separate commits (`910c9762d46f097632851c5c92626e2b1915f7c0`, `d115a952c9bcf8e7912e29956cdb208a529187ec`, `d4a975e3a0ac41619f363ca9a073011f15117383`, `21de89eeb255427106d4426d2a8e89579f0fb041`, `d78df302c558e58a6f27933b0516bcd5955053db`, `02a52e2e775e3b71f2168a05bdb0392bd76e8abe`, `55070e5fb87604ff5855bc736b2bdd2bb83709fb`, `44badcfc889e852dcb8f395acd0d5d0ea83ef745`, `bfe148f0687398efa270d289b4c7a904ec103dbd`, `9b7b14847dbf2e9c4a0a99615951f2810e330d6d`) migrated `l4v` sessions to Isabelle2025-2, demonstrating that replay environment identity is distinct from theorem semantics.

Basis: **source/history/documentation** — `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5` and `seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b`.

#### 3. CompCert Shared Memory-Injection Refactoring and Downstream Compatibility Shims

While CompCert's per-pass simulation architecture isolates internal pass algorithm changes, shared semantic relations across passes remain high-blast-radius hinges:

- Commit `2f5e3204c48510f94c91699c64dee8bd18cd2b75` strengthened memory injections so metadata stored at negative block offsets could not become normally accessible after injection, repairing the semantic foundation for `free` (374 changed lines across common memory and proof clients).
- Commit `59b473374b23660f587230969b48ff407241dc19` introduced `Senv.inject`, `Genv.inject`, and `Val.inject_ptr_flat`, replacing older event and global-preservation machinery across 16 files (625 changed lines, touching inlining, stacking, unused-global removal, `Cminor` generation, local simplification, global environments, values, and target operations).
- Commit `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` explicitly restored `Events.meminj_preserve_globals` as a temporary backward-compatibility shim for external downstream developments such as the Verified Software Toolchain (VST), providing a bounded migration window without reverting the internal refactoring.

Basis: **source/history** — `AbsInt/CompCert` commits `2f5e3204c48510f94c91699c64dee8bd18cd2b75`, `59b473374b23660f587230969b48ff407241dc19`, and `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`.

#### 4. Project Everest, HACL*, and KaRaMeL: High-Level Specialization vs. Extraction and Solver Pinning

In `hacl-star/hacl-star@504c2987452f87fe44bce9b9f12e19d6e051761f` (`README.md` blob `8815628e9cea88ca1cbb777e5f30cab98b66e012`), cryptographic implementations are verified in Low* (for memory safety, functional correctness, and secret independence) or Vale (assembly) and extracted to C via KaRaMeL (`FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`, `README.md` blob `3c0396bb78ad3b8c252da3a0518eba029b2e7cc9`, `DESIGN.md` blob `1c61b9572744fa0fbb8f602129ea15aadaac6a36`). Ho, Fromherz, and Protzenko (ICFP 2023, DOI `10.1145/3607844`) report that indexed effects, dependent types, meta-programming, and zero-cost specialization were essential to scaling HACL* past 100,000 lines of verified source and reusing a single generic streaming verification across more than a dozen cryptographic constructions (several integrated into CPython).

At the same time, KaRaMeL's `DESIGN.md` documents a multi-pass lowering pipeline (typed AST conversion, monomorphization, tuple/datatype elimination, simplification, inlining, statement conversion, C* translation, C AST translation, and pretty-printing) and notes an unverified internal invariant that intermediate passes stay within the Low* subset. Consequently, extraction remains part of the trust/correspondence story, and Project Everest (`project-everest/everest@2a3f67dab56be02d1793b2801ef08f368423a3ac`, `README.md` blob `ce627659804164d6250a5ec1397c403c14af4418`) manages proof maintenance by pinning known-good F*, KaRaMeL, Vale, and Z3 4.8.5 revisions (`43ffda45c9eb03ef2661f6b89c47f1d5a735a502`), stabilizing CI-sensitive proofs (`bfb6db8ecc67f36754d257500c2a0f1e2f6be609`, `ecbf1aaa83016c0b3e67c49c0f962afcdd3986fa`), and keeping regenerated proof hints and `dist/` C/ASM artifacts synchronized under version control (`ee6ac4d2b58fb3da421086e778132800fb3f0e37`, `504c2987452f87fe44bce9b9f12e19d6e051761f`).

#### 5. Architectural Implications for Anneal Maintenance Boundaries

To avoid conflating distinct invalidation causes, Anneal should track four separate identities: (1) the semantic version of the obligation/claim, (2) the proof-facing representation version (canonicalizing surface syntax where possible so automation does not couple to incidental generator output shapes), (3) the toolchain/replay environment identity, and (4) the concrete generated artifact identity.

---

### Part III: Current-Source Continuity and Release Observations Across seL4, CompCert, and Everest

#### 1. Six-Repository Default-Branch and Claim-Mapped File Comparison

An official-source review (`support/matrix.json`, `support/official-source-observation.json`, verified offline by `support/check_matrix.py`) compared the pinned revisions of the proof-maintenance and pass-composition analyses (frozen at `google/zerocopy` `reference` commit `47d8250bff3ea17f1fbb4340370032e03692617b`, reconciling the 581-report inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837` with the 613-report parent) against current upstream default branches:

| Source Line | Exact Claim-Mapped Files | Observed Upstream Default-Branch Result |
| --- | --- | --- |
| [`seL4/l4v`](https://github.com/seL4/l4v/commit/6b4076aeb35f7803b7c232963e5f996545e3acb5) | `README.md`, `docs/setup.md` | `master` equals pinned commit `6b4076aeb35f7803b7c232963e5f996545e3acb5`; both Git blobs match (`support/sel4-compcert-everest-current-source-review/snapshots/seL4--l4v/README.md`, `support/sel4-compcert-everest-current-source-review/snapshots/seL4--l4v/docs/setup.md`). |
| [`seL4/verification-manifest`](https://github.com/seL4/verification-manifest/commit/f1f7a4289585e9610733ea041c1849e46af9701b) | `README.md` | `master` equals pinned commit `f1f7a4289585e9610733ea041c1849e46af9701b`; blob matches (`support/sel4-compcert-everest-current-source-review/snapshots/seL4--verification-manifest/README.md`). |
| [`AbsInt/CompCert`](https://github.com/AbsInt/CompCert/commit/66a9fd06ef88619cc94765ca995a1018f7259b5c) | `VERSION`, `common/Smallstep.v`, `driver/Compiler.v` | `master` (`66a9fd06ef88619cc94765ca995a1018f7259b5c`) is 4 commits ahead of `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`; all 3 claim-mapped blobs (`support/snapshots/AbsInt--CompCert/VERSION`, `support/snapshots/AbsInt--CompCert/common/Smallstep.v`, `support/snapshots/AbsInt--CompCert/driver/Compiler.v`) are identical to 3.18. |
| [`hacl-star/hacl-star`](https://github.com/hacl-star/hacl-star/commit/504c2987452f87fe44bce9b9f12e19d6e051761f) | `README.md` | `main` equals pinned commit `504c2987452f87fe44bce9b9f12e19d6e051761f`; blob matches (`support/snapshots/hacl-star--hacl-star/README.md`). |
| [`FStarLang/karamel`](https://github.com/FStarLang/karamel/commit/9abbb865b10a0cd5c557da81c024c3965cb6ff53) | `README.md`, `DESIGN.md` | `master` equals pinned commit `9abbb865b10a0cd5c557da81c024c3965cb6ff53`; both blobs match (`support/snapshots/FStarLang--karamel/README.md`, `support/snapshots/FStarLang--karamel/DESIGN.md`). |
| [`project-everest/everest`](https://github.com/project-everest/everest/commit/2a3f67dab56be02d1793b2801ef08f368423a3ac) | `README.md` | `master` equals pinned commit `2a3f67dab56be02d1793b2801ef08f368423a3ac`; blob matches (`support/snapshots/project-everest--everest/README.md`). |

The 4 later commits on `AbsInt/CompCert` `master` modify exactly 5 paths: `cfrontend/CPragmas.ml`, `common/Switch.v`, `common/Switchaux.ml`, `cparser/Lexer.mll`, and `test`. None of the three cited files (`VERSION`, `common/Smallstep.v`, `driver/Compiler.v`) changed.

#### 2. Release Tag Observations and Ancestry

Querying GitHub `releases/latest` across the six repositories (`support/seL4--l4v-release-tag-refs.txt`, `support/AbsInt--CompCert-release-tag-refs.txt`, `support/hacl-star--hacl-star-release-tag-refs.txt`, `support/FStarLang--karamel-release-tag-refs.txt`) returned:
- `seL4/l4v`: tag `seL4-16.0.0` (precedes pinned `master` by 92 commits);
- `AbsInt/CompCert`: tag `v3.18` (precedes pinned `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` by 14 commits, confirming `v3.18` remains the latest official CompCert release);
- `hacl-star/hacl-star`: tag `ocaml-v0.4.5` (an OCaml package tag preceding pinned `main` by 2,898 commits, not a newer HACL* library release);
- `FStarLang/karamel`: tag `v0.9.6.0` (precedes pinned `master` by 3,002 commits); and
- `seL4/verification-manifest` and `project-everest/everest`: HTTP 404 on `releases/latest` (no GitHub Release objects published).

---

### Part IV: Reasoning About Nontermination in CompCert 3.18 and Aeneas (`nightly-2026.06.03`)

#### 1. Semantic Nontermination vs. Recursive Syntax and Rust Divergence

Semantic nontermination is an infinite execution property, distinct from both:
- **Syntactic recursion or cyclic control flow:** A recursive function or loop may terminate on every reachable input, while a nonrecursive function may diverge by invoking a partial operation or waiting forever on an environment.
- **Rust diverging expressions (`!`):** In `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/divergence.md` blob `5e25d6d0d944ae8a62236ce7e46f347ded3fbfcc`, `src/types/never.md` blob `fe30bce74d6ab02eb06b9d6a852f9dc3e523eec2`, `src/expressions/loop-expr.md` blob `8e67295482c3826c841585172560d93b2823510f`), a diverging expression is any expression that does not complete normally, which includes finite abrupt termination such as `panic!`. Neither a `!` return type, nor a bottom constructor, nor a conservative static flag establishes semantic nontermination or termination by itself (`support/reasoning-about-nontermination-compcert-aeneas/nontermination-reasoning-map.json`).

#### 2. CompCert 3.18 Silent vs. Reactive Divergence and Coinductive Simulation Preservation

CompCert 3.18 (`common/Behaviors.v`, blob `822b08832f491e82fefc5b60251c13a63ef71301`) classifies whole-program execution into four outcomes under `program_behavior`:
1. `Terminates t i`: finite execution with trace `t` and exit code `i`;
2. `Diverges t`: after finite observable trace `t`, execution continues forever silently (`Forever_silent`) without further observable I/O;
3. `Reacts T`: execution continues forever while producing an infinite trace `T` of observable events (`Forever_reactive`); and
4. `Goes_wrong t`: execution gets stuck in an erroneous/undefined state after finite trace `t`.

Both `Forever_silent` and `Forever_reactive` are coinductive-style execution relations, and CompCert's forward and backward simulation libraries prove dedicated preservation lemmas for both infinite modes (`driver/Complements.v`, blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`). Moreover, `behavior_improves` permits target behavior to refine `Goes_wrong t`, whereas `Diverges t` and `Reacts T` are valid safe behaviors that simulations must preserve rather than conflate with stuckness or collapse into each other (turning a reactive server into a silent spin loop violates `Reacts T` preservation).

#### 3. Aeneas Partial Denotations (`partial_fixpoint`, `Result.div`), `WP.spec`, and `can_diverge` Boundaries

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`), Aeneas separates semantic partiality from termination proofs:
- **Partial denotation:** Supported recursive functions are emitted using Lean's `partial_fixpoint` over the `Result α` monad (`ok`, `fail`, `div`), where `Result.div` is the CCPO bottom element propagated by monadic bind. Translation therefore succeeds without requiring an upfront termination proof.
- **Specification-time termination exclusion:** In Aeneas's weakest-precondition layer (`WP.lean`), `spec div P` evaluates to `False`, and standard `WP.spec` proofs establish the existence of an `ok` value satisfying the postcondition—thereby ruling out `Result.div` for that verified invocation.
- **Conservative `can_diverge` flag vs. `NoBreak` loop rejection:** Aeneas's static `can_diverge` flag (`FunsAnalysis.ml`) conservatively marks direct/mutual recursion, loops, and transitive calls (with a known trait-method propagation limitation) to select translation machinery; neither `can_diverge = true` nor `can_diverge = false` is a semantic proof of divergence or termination. Furthermore, while recursive divergence can denote `Result.div`, symbolic execution of unconditional loops whose break context is `NoBreak` is rejected with an unsupported-loop error rather than translated to `Result.div`.

---

### Part V: Operational Semantics vs. Functional Translation

#### 1. Structural Tradeoffs Between Operational Execution Relations and Functional Target Models

Comparing CompCert 3.18 and the Aeneas 2022/2024 semantic stack (`support/operational-semantics-versus-functional-translation/comparison-matrix.json` and `model-comparison.json`) isolates where each paradigm places proof complexity:

| Dimension | Operational Semantics (e.g., CompCert 3.18, LLBC/Pointer Semantics) | Functional Translation (e.g., Aeneas Pure Lambda Calculus / Lean Target) |
| --- | --- | --- |
| **State & memory representation** | Explicit program configurations, heaps, addresses, environments, and step/evaluation relations. | Ownership-centric values; mutable borrows encoded as pure forward outputs plus **backward functions** returning updated values when borrows end (ICFP 2022, DOI `10.1145/3547647`). |
| **Non-returning & effectful behaviors** | Directly represented in transitions, stuck states, coinductive traces, and relational external calls. | Requires explicit target encodings (`Result` types for failure/bottom, state/trace threading, monads/ITrees, or partiality domains). |
| **User proof burden** | Higher per-program invariant burden (heap framing, address aliasing, step indexing) unless wrapped by a program logic. | Lower per-program proof burden: proofs use native functional induction, equational rewriting, and algebraic datatypes in the theorem prover. |
| **Source-to-target soundness bridge** | Simulation/refinement between dynamic semantics (CompCert `Smallstep.v` / `Compiler.v`). | Requires a separate correspondence proof, validator, or explicit trust assumption connecting source execution to the generated target function. |

#### 2. How Aeneas 2024 Operationally Justifies the Ownership-Centric LLBC Model

In *Sound Borrow-Checking for Rust via Symbolic Semantics* (ICFP 2024, DOI `10.1145/3674640`, `arXiv:2404.02680`), Ho, Fromherz, and Protzenko bridge the gap between low-level operational execution and high-level ownership reasoning by proving three linked results:
1. **High-level view correctness:** Value-based, ownership-centric LLBC semantics correctly refines a lower-level operational model with an explicit heap and memory addresses.
2. **Symbolic abstraction soundness:** Symbolic LLBC execution (including the control-flow merge `join` operation) soundly abstracts concrete LLBC execution.
3. **Borrow-checking non-stuckness:** Programs accepted by the symbolic borrow checker do not get stuck in the lower-level heap-and-address execution model.

Crucially, operational and functional models compose in a single assurance chain:
$$\text{source operational behavior} \longrightarrow \text{abstract operational/symbolic behavior (LLBC)} \longrightarrow \text{functional target evaluation (Lean)} \longrightarrow \text{proved target theorem}$$
While ICFP 2024 mechanizes the operational-to-LLBC and symbolic-abstraction links for its modeled fragment, the production OCaml LLBC-to-Lean translator (`AeneasVerif/aeneas`) does not emit per-run refinement proofs and therefore remains a trusted translation stage unless discharging certificates or validated.

---

### Part VI: Nondeterminism and Environmental Effects in Program Verification

#### 1. Relational External Calls vs. Deterministic Environment Worlds in CompCert 3.18

In CompCert 3.18 (`common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`), external interactions (system calls, volatile loads/stores, annotations) are modeled by a relational judgment `extcall_sem` relating the global symbol environment, argument values, pre-call memory, emitted trace (`trace` / `traceinf` over `event` and `eventval`), return value, and post-call memory, constrained by `extcall_properties` (`ec_trace_length`, receptiveness `ec_receptive`, and trace-conditional determinism `ec_determ`).

In `common/Determinism.v` (blob `7c2f99cb801bacd9432c94494edb0c538a61a2f7`), CompCert explicitly notes that unspecified system-call results introduce nondeterminism, and defines a coinductive `world` supplying deterministic response functions for `io`, volatile loads, and volatile stores (`possible_event`, `possible_trace`, `possible_traceinf`, `possible_behavior`). Proving a property under one fixed `world` establishes behavior only for that deterministic environment stream; proving a property across all admissible environments requires quantifying over all worlds or preserving the relational `program_behaves` judgment (`common/Behaviors.v`, `forward_simulation_behavior_improves`, `forward_simulation_same_safe_behavior`).

#### 2. Interaction Trees (POPL 2020) vs. Choice Trees (POPL 2023): Separating Environment Responses from Internal Branching

- **Interaction Trees (Xia et al., POPL 2020, DOI `10.1145/3371119`, `arXiv:1906.00046`):** Represent recursive impure programs coinductively as uninterpreted visible events paired with response-indexed continuations, interpreted into semantic domains by modular event handlers and compared up to termination-sensitive weak bisimulation.
- **Choice Trees (Chappe et al., POPL 2023, DOI `10.1145/3571254`, `arXiv:2211.06863`):** Extend the coinductive interaction-tree architecture with explicit internal nondeterministic branching nodes (stepping and visible br nodes) distinct from external environment events, providing simulation, bisimulation, and trace-equivalence machinery plus a monad morphism connecting CTrees to ITree handlers.

Preserving the distinction between **environment interaction** (the environment chooses among responses to a visible event) and **internal nondeterminism** (the program or semantics chooses among internal branches) prevents silent strengthening when handlers or refinement relations are instantiated.

#### 3. Five-Question Adequacy Checklist for Effectful or Nondeterministic Constructs in Anneal

For every Rust, Charon LLBC, or Aeneas construct that is not a pure deterministic function of modeled state, Anneal's adequacy review must answer five questions:
1. **Choice owner:** Is variability internal to the program semantics, supplied by an external environment, or both?
2. **Observable surface:** Which events, memory/state mutations, errors, silent vs. reactive divergence modes, or return values are observable to the claimed property?
3. **Allowed outcomes:** What relation, event handler, world protocol, or assumption constrains the admissible responses and branches?
4. **Preservation direction:** Must translation preserve all source behaviors, forbid new target behaviors (refinement / trace inclusion), establish bisimulation, or hold only conditionally on normal return?
5. **Unsupported-operation disposition:** When the construct is outside the modeled subset, does the pipeline fail closed by rejecting it, surface an explicit named assumption/effect, or unsoundly collapse it to a single deterministic value?

## Boundaries

- **No fresh theorem-prover or compiler execution:** No Rocq/Coq, Isabelle/HOL, F*, KaRaMeL, Vale, Z3, Charon, Aeneas, Lean, or Rust build was executed for this synthesis (`runtime_result` in `support/official-source-observation.json` is `unexecuted_in_this_review`). All claims derive from exact source inspection, repository commit histories, official release metadata, and published peer-reviewed papers.
- **System-specific semantics are not prescribed verbatim for Anneal:** CompCert's `forward_simulation`, `backward_simulation`, `behavior_improves`, and event vocabulary, seL4's capDL/C-refinement layers, HACL*'s Low* memory model, and ITree/CTree coinductive encodings are reference architectures, not mandatory verbatim encodings for Rust or Anneal.
- **CompCert compiler core vs. full deployment chain:** CompCert's formal `transf_c_program_correct` theorem covers the C-to-Asm compiler core; assembling, linking, and hardware execution assumptions remain separate boundaries, and unchanged `Smallstep.v`/`Compiler.v` blobs on `AbsInt/CompCert` `master` (`66a9fd06ef88619cc94765ca995a1018f7259b5c`) do not establish unexecuted proof replay across the 4 newer `master` commits.
- **KaRaMeL and Aeneas production translators are not mechanically verified compilers:** KaRaMeL's `DESIGN.md` explicitly records an unverified internal Low*-subset invariant, and Aeneas's production OCaml LLBC-to-Lean translator (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`) is not mechanically proved end-to-end by the ICFP 2022 or ICFP 2024 formalizations.
- **Nontermination and concurrency scope:** CompCert's `Diverges`/`Reacts` taxonomy is sequential trace semantics and does not model weak-memory concurrency, scheduler fairness, deadlocks, or probabilistic choice. Aeneas's `Result.div` does not cover unconditional `NoBreak` loops (which are rejected at `nightly-2026.06.03`), and `can_diverge` is a conservative static analysis flag rather than a semantic oracle.

## Evidence

### 1. CompCert 3.18 and Current `master` Source & Documentation (`AbsInt/CompCert`)
- **Pinned 3.18 Revision:** `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (tag `v3.18`):
  - `VERSION`, blob `5fd2882f6f042e89ce617586ce5041f5762c1766` (`support/snapshots/AbsInt--CompCert/VERSION`).
  - `common/Smallstep.v`, blob `cefab134fdce4f3ea2f970db49a99d987c05d3a1` (`support/snapshots/AbsInt--CompCert/common/Smallstep.v`): `compose_forward_simulations` (lines 1003–1043), `compose_backward_simulation` (lines 1566 onward), `forward_to_backward_simulation` (lines 1863 onward), `factor_forward_simulation` (lines 2004 onward).
  - `driver/Compiler.v`, blob `60fc74fec1411216425004f6d63567354e146e9c` (`support/snapshots/AbsInt--CompCert/driver/Compiler.v`): `match_if_simulation`, `cstrategy_semantic_preservation` (lines 344–416), `c_semantic_preservation` (lines 419–434), `transf_c_program_correct` (lines 446–453), `separate_transf_c_program_correct` (lines 466 onward).
  - `common/Behaviors.v`, blob `822b08832f491e82fefc5b60251c13a63ef71301`: `program_behavior` (`Terminates`, `Diverges`, `Reacts`, `Goes_wrong`), `state_behaves`, `Forever_silent`, `Forever_reactive`, `behavior_improves`, `forward_simulation_behavior_improves`, `forward_simulation_same_safe_behavior`.
  - `driver/Complements.v`, blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`: `transf_c_program_preservation`, `transf_c_program_is_refinement`.
  - `common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`: `eventval`, `event`, `trace`, `traceinf`, `extcall_sem`, `extcall_properties` (`ec_trace_length`, `ec_receptive`, `ec_determ`).
  - `common/Determinism.v`, blob `7c2f99cb801bacd9432c94494edb0c538a61a2f7`: coinductive `world`, `possible_event`, `possible_trace`, `possible_traceinf`, `possible_behavior`.
- **CompCert 2026 Maintenance Commits & Observed `master`:**
  - `2f5e3204c48510f94c91699c64dee8bd18cd2b75` (negative-offset metadata protection in memory injections, 374 lines).
  - `59b473374b23660f587230969b48ff407241dc19` (`Senv.inject`, `Genv.inject`, `Val.inject_ptr_flat` refactor across 16 files, 625 lines).
  - `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (restores `Events.meminj_preserve_globals` for VST compatibility).
  - Observed `master` on `2026-09-30`: `66a9fd06ef88619cc94765ca995a1018f7259b5c` (4 commits ahead of `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`; recorded in `support/AbsInt--CompCert-refs.txt` and `support/AbsInt--CompCert-release-tag-refs.txt`).
- **CompCert 3.18 Documentation:** `https://compcert.org/doc/`, `https://compcert.org/man/manual001.html`, and `https://compcert.org/doc/html/compcert.driver.Compiler.html`.

### 2. seL4 Proof Corpus (`seL4/l4v`) and Verification Manifest (`seL4/verification-manifest`)
- **Pinned & Observed `master` Revisions:** `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5` (`README.md` blob `03421c4b7db4e9756efde5f46f19e60970fc7288`, `docs/setup.md` blob `c20d7ba4fb16845977b4d205d725cb6c52a64eb9`) and `seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b` (`README.md` blob `2b3f4a193bbb3012f9b7711f06bbb3dc2c98e352`).
- **Sampled `seL4/l4v` Maintenance Commits:** `bce918b83bd9deaf91c3b9e7c3678929c4ad5799` (`numDomains = 256`), `589b63f232d3c042cc7fc41f5fd304f2e7114e7a` (AArch64 reserved VMID 0), `411e76099fff81c09cd4eb6619cef13d8d9bb6cf` (ARM/ARM_HYP reserved ASID), `9ae6b8106f5ef4dd14cb0e9543d9fe14101bbc4f` (`init`/`butlast` simplifier stability), and Isabelle2025-2 migration commits (`910c9762d46f097632851c5c92626e2b1915f7c0`, `d115a952c9bcf8e7912e29956cdb208a529187ec`, `d4a975e3a0ac41619f363ca9a073011f15117383`, `21de89eeb255427106d4426d2a8e89579f0fb041`, `d78df302c558e58a6f27933b0516bcd5955053db`, `02a52e2e775e3b71f2168a05bdb0392bd76e8abe`, `55070e5fb87604ff5855bc736b2bdd2bb83709fb`, `44badcfc889e852dcb8f395acd0d5d0ea83ef745`, `bfe148f0687398efa270d289b4c7a904ec103dbd`, `9b7b14847dbf2e9c4a0a99615951f2810e330d6d`).
- **Publications & Documentation:** Klein et al., SOSP 2009; Sewell, Myreen, & Klein, PLDI 2013; `https://docs.sel4.systems/projects/sel4/kernel-contribution.html`, `https://docs.sel4.systems/releases.html`, `https://sel4.systems/Verification/proofs.html`, `https://sel4.systems/About/FAQ.html`.

### 3. Project Everest, HACL*, and KaRaMeL
- **`hacl-star/hacl-star@504c2987452f87fe44bce9b9f12e19d6e051761f`:** `README.md` blob `8815628e9cea88ca1cbb777e5f30cab98b66e012` (`support/snapshots/hacl-star--hacl-star/README.md`), plus maintenance commits `bfb6db8ecc67f36754d257500c2a0f1e2f6be609`, `ecbf1aaa83016c0b3e67c49c0f962afcdd3986fa`, `43ffda45c9eb03ef2661f6b89c47f1d5a735a502` (Z3 4.8.5), and `ee6ac4d2b58fb3da421086e778132800fb3f0e37`.
- **`FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`:** `README.md` blob `3c0396bb78ad3b8c252da3a0518eba029b2e7cc9` (`support/snapshots/FStarLang--karamel/README.md`) and `DESIGN.md` blob `1c61b9572744fa0fbb8f602129ea15aadaac6a36` (`support/snapshots/FStarLang--karamel/DESIGN.md`).
- **`project-everest/everest@2a3f67dab56be02d1793b2801ef08f368423a3ac`:** `README.md` blob `ce627659804164d6250a5ec1397c403c14af4418` (`support/snapshots/project-everest--everest/README.md`) and `https://project-everest.github.io/`.
- **Publication:** Son Ho, Aymeric Fromherz, and Jonathan Protzenko, “Modularity, Code Specialization, and Zero-Cost Abstractions for Program Verification,” *PACMPL* 7 (ICFP 2023), DOI `10.1145/3607844`.

### 4. Published Validator, Aeneas, Rust Reference, and ITree/CTree Primary Sources
- **Verified Validator Pattern:** Jean-Baptiste Tristan and Xavier Leroy, “Formal Verification of Translation Validators: A Case Study on Instruction Scheduling Optimizations,” *POPL 2008*, pp. 17–27, DOI `10.1145/1328438.1328444`.
- **Aeneas Functional Translation & Symbolic Semantics:**
  - Son Ho and Jonathan Protzenko, “Aeneas: Rust Verification by Functional Translation,” *PACMPL* 6 (ICFP 2022), Article 116, DOI `10.1145/3547647` (`arXiv:2206.07185`).
  - Son Ho, Aymeric Fromherz, and Jonathan Protzenko, “Sound Borrow-Checking for Rust via Symbolic Semantics,” *PACMPL* 8 (ICFP 2024), DOI `10.1145/3674640` (`arXiv:2404.02680`).
  - Pinned Aeneas implementation: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).
- **Rust Reference Termination Terminology:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/divergence.md` blob `5e25d6d0d944ae8a62236ce7e46f347ded3fbfcc`, `src/types/never.md` blob `fe30bce74d6ab02eb06b9d6a852f9dc3e523eec2`, `src/expressions/loop-expr.md` blob `8e67295482c3826c841585172560d93b2823510f`).
- **Interaction Trees & Choice Trees:**
  - Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic, “Interaction Trees: Representing Recursive and Impure Programs in Coq,” *PACMPL* 4 (POPL 2020), Article 51, DOI `10.1145/3371119` (`arXiv:1906.00046`).
  - Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, and Steve Zdancewic, “Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq,” *PACMPL* 7 (POPL 2023), pp. 1770–1800, DOI `10.1145/3571254` (`arXiv:2211.06863`).
- **Bundled Support Artifacts:** `support/matrix.json`, `support/official-source-observation.json`, `support/check_matrix.py`, `support/proof-maintenance-architectures-sel4-compcert-everest-2009-2026/maintenance-cases.json`, `support/proof-maintenance-architectures-sel4-compcert-everest-2009-2026/source-map.json`, `support/reasoning-about-nontermination-compcert-aeneas/nontermination-reasoning-map.json`, `support/reasoning-about-nontermination-compcert-aeneas/source-map.json`, `support/operational-semantics-versus-functional-translation/comparison-matrix.json`, and `support/operational-semantics-versus-functional-translation/source-map.json`.

## Revalidation

1. **CompCert Pass Composition & Behavior/World Semantics:** On any newer CompCert release or `master` commit, diff `common/Smallstep.v` (`compose_forward_simulations`, `compose_backward_simulation`, `forward_to_backward_simulation`, `factor_forward_simulation`), `driver/Compiler.v` (`cstrategy_semantic_preservation`, `c_semantic_preservation`, `transf_c_program_correct`, `separate_transf_c_program_correct`), `common/Events.v` (`extcall_sem`, `extcall_properties`, `meminj_preserve_globals`), `common/Determinism.v` (`world`, `possible_trace`, `possible_behavior`), and `common/Behaviors.v` (`program_behavior`, `Forever_silent`, `Forever_reactive`, `behavior_improves`).
2. **seL4 and Project Everest Proof-Maintenance & Source Continuity:** Run `python3 reports/compcert-sel4-everest-pass-composition-and-proof-maintenance/support/check_matrix.py` to verify frozen source blobs and release ancestry; when refreshing upstream pins, check `seL4/l4v` (`README.md`, `docs/setup.md`), `seL4/verification-manifest` (`README.md`), `hacl-star/hacl-star` (`README.md`, solver/hint commits, `dist/` synchronization), `FStarLang/karamel` (`README.md`, `DESIGN.md`), and `project-everest/everest` (`README.md`).
3. **Aeneas Nontermination & Functional-Translation Bridge:** On any Aeneas upgrade beyond `nightly-2026.06.03` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), inspect `FunsAnalysis.ml`, loop break-context handling (`NoBreak`), `ExtractBase.ml`, `Primitives.lean` (`partial_fixpoint`, `Result.div`), and `WP.lean` (`WP.spec` exclusion of `div`), and check whether any mechanized refinement or validator bridges the OCaml LLBC-to-Lean generator.
4. **Anneal Boundary & Effect Adequacy Audit:** Maintain a stage-by-stage boundary table (`Rel_1` through `Rel_4`) and evaluate every admitted effectful or potentially nonterminating construct against the five adequacy questions in Findings Part VI.3 (choice owner, observable surface, allowed outcomes, preservation direction, and fail-closed unsupported-operation handling).
