# Aeneas formal results: proved semantics versus trusted engineering

## Summary

The Aeneas literature establishes important formal results, but it does not provide a mechanically verified end-to-end compiler from the Rust accepted by `rustc` to the Lean emitted by Anneal's pinned Aeneas release.

The 2022 Aeneas paper defines a functional LLBC semantics and a translation from LLBC to a pure lambda calculus. It demonstrates the approach by translating Rust programs and proving functional correctness of a resizing hash table. The paper does **not** claim a mechanically established refinement theorem for the implementation of that translation. On the contrary, it describes Aeneas as generating a **trusted** pure translation, contrasts this with systems that emit per-run refinement proofs, and lists a mechanical soundness proof of its ownership-centric semantics as future work.

The 2024 paper closes a different and foundational gap. It proves three semantic relationships for the modeled languages: LLBC is a correct high-level view of a lower-level heap-and-address execution model; LLBC's symbolic semantics correctly abstract concrete LLBC execution; and successful symbolic checking acts as a borrow checker, in the sense that symbolically checked LLBC programs do not get stuck in the low-level execution model. It also proves that the join operation used to handle control-flow joins preserves the relevant abstraction and borrow-checking properties. A current Rocq development in `AeneasVerif/mechanized-llbc` formalizes this LLBC line of work and contains the corresponding simulation infrastructure. This run inspected its sources but did not freshly check them with Rocq.

Those results justify the semantic design of Aeneas much more strongly than an engineering-only translation would. They still leave implementation bridges that Anneal must treat separately: `rustc`/MIR to Charon LLBC, conformance of production Charon/Aeneas code to the paper models, LLBC-to-backend extraction, hand-written models for external definitions, and the trust/admission boundary of the generated Lean development. A proof accepted by Lean can therefore be an extremely strong result about the generated model without the papers, by themselves, making that theorem an end-to-end mechanically certified theorem about arbitrary Rust source.

No fresh proof-assistant build, Aeneas execution, or paper-artifact execution was performed.

## Applicability

The literature subjects are:

- Son Ho and Jonathan Protzenko, *Aeneas: Rust Verification by Functional Translation*, PACMPL/ICFP 2022, DOI `10.1145/3547647`, long version `arXiv:2206.07185v2`.
- Son Ho, Aymeric Fromherz, and Jonathan Protzenko, *Sound Borrow-Checking for Rust via Symbolic Semantics*, PACMPL/ICFP 2024, DOI `10.1145/3674640`, long version `arXiv:2404.02680`.

The implementation point used for Anneal comparison is `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`. Its README identifies the same two papers as the project's formalization results and states that this release targets a subset of safe Rust; unsafe code and concurrency remain outside that functional model.

The current mechanization point inspected here is `AeneasVerif/mechanized-llbc@1268d802a59ddb0672528f24d873ed4b3b28ca0c`. Its README identifies the 2024 paper as the reference for a Rocq formalization of LLBC. This current repository revision is useful evidence that a machine-checked development exists, but it is not treated as the exact frozen artifact evaluated with the 2024 publication unless an immutable publication artifact establishes that identity.

The 2023 paper *Modularity, Code Specialization, and Zero-Cost Abstractions for Program Verification* has overlapping authors but concerns F*, Low*, and HACL*, not Aeneas. It is not counted as an Aeneas formal result in this report.

## Findings

### The 2022 result is a formal semantic design and translation, not a verified compiler implementation

The 2022 paper's first contribution is a value-based, ownership-centric semantics for LLBC. It deliberately removes addresses and pointer arithmetic from the verification-facing language and represents Rust borrowing through loans, borrows, and semantic reorganization of those values.

Its second contribution is a translation from LLBC to a pure lambda calculus. Backward functions reconstruct values returned through mutable borrows and allow the translated program to remain functional.

That is a substantive formalization. It explains what the translation is intended to mean and gives a mathematical object against which an implementation can be judged.

The paper nevertheless draws a clear trust boundary around the implemented translator. In its comparison with foundational systems, it calls the generated Aeneas program a trusted pure translation. It contrasts Aeneas with Cogent, whose compiler emits a refinement proof for each run, and explicitly says that Aeneas's compiler must be trusted instead. In its related-work discussion it also says that mechanically proving the soundness of Aeneas's ownership-centric semantics is future work.

Accordingly, "the translation has been formalized" must not be expanded into "the production Rust/OCaml translator has a machine-checked semantics-preservation proof." The former is supported by the paper and the pinned Aeneas README. The latter is not established by the 2022 evidence.

Basis: 2022 paper **formal model**, **source-level paper claims**, and **derived trust-boundary reading**.

### The verified hash table is a program proof over the trusted translation

The 2022 paper's main case study is a low-level resizing hash table. After Aeneas translates the Rust program, the authors prove functional properties of the generated pure program in F*. The specifications cover invariants and the behavior of operations such as insertion, including success and arithmetic-overflow cases.

This is a real functional-correctness proof, not merely a test of the translator.

Its scope is important. Because the paper treats the generated pure translation as trusted, the F* theorem establishes correctness of the translated model under that trust assumption. It is not, by itself, a machine-checked refinement proof that the original `rustc` program and the generated F* term have identical semantics.

Basis: 2022 paper **case-study proof** + **derived composition boundary**.

### The 2024 paper proves LLBC against a lower-level execution model

The 2024 paper states three central semantic results.

First, LLBC is a correct view over a conventional low-level execution model with heap locations and addresses. This connects the borrow-centric value model to a representation that looks much more like ordinary low-level execution.

Second, the symbolic semantics used for borrow reasoning are a correct abstraction of concrete LLBC programs.

Third, those symbolic semantics act as a borrow checker: a program accepted by the symbolic semantics does not get stuck when executed in the lower-level heap-and-address model, within the modeled language and assumptions.

These are the strongest foundational results in the Aeneas papers examined here. They move the central borrow discipline from an intended semantic explanation to a proved abstraction/simulation story.

They are still theorems about the formal languages of the paper. They do not, without additional bridge proofs, establish that every current `rustc` MIR program translated by Charon is an instance of the modeled LLBC semantics or that the OCaml/Lean implementation exactly realizes every formal rule.

Basis: 2024 paper **proved semantic results** + **derived implementation boundary**.

### The 2024 join result supports loops without changing the trust boundary above it

The 2024 work adds a join operation to the symbolic semantics so control-flow paths can be merged. The paper states that this join preserves the abstraction and borrow-checking properties. This provides the semantic basis for adding loops to Aeneas's symbolic framework.

The result is stronger than an empirical observation that loop examples happen to work: the join participates in the formal preservation argument.

The current `mechanized-llbc` development also contains an explicit `simulation_LLBC_sharp_LLBC_plus` lemma and simulation code for join-bearing evaluation, which is consistent with the paper's simulation structure at the current mechanization revision.

The result does not mean that every current Aeneas loop-lowering implementation is mechanically certified. It establishes the soundness of the modeled join/symbolic semantics. Separate implementation conformance is still required.

Basis: 2024 paper **proved result** + current Rocq **source** + **derived implementation boundary**.

### A Rocq LLBC mechanization exists today

At current `AeneasVerif/mechanized-llbc@1268d802a59ddb0672528f24d873ed4b3b28ca0c`, the README describes the repository as a Rocq formalization of the LLBC model and names the 2024 paper as its reference.

The repository contains dedicated formal-language and simulation modules, including:

- `src/LLBC.v`, `src/LLBC_plus.v`, and `src/LLBC_sharp.v`;
- `src/Symbolic_states.v`;
- `src/simulations/Simulation_LLBC_plus.v`;
- `src/simulations/Simulation_HLPL_plus.v`;
- `src/simulations/Simulation_LLBC_sharp_LLBC_plus.v`.

The latter contains the lemma `simulation_LLBC_sharp_LLBC_plus`, stated as a forward simulation from `LLBC_sharp.eval_stmt` to `LLBC_plus.eval_stmt`.

This establishes that the LLBC semantic line is represented by proof-assistant source at the current development head, rather than existing only as prose. This run did not execute Rocq, so it does not independently establish that the current tree checks successfully. It also does **not** establish that this exact repository revision is the immutable artifact corresponding to the published 2024 paper, nor that every paper theorem was already machine-checked in the publication artifact. The public ICFP 2024 artifact-evaluation description instead describes an Aeneas tree modified for loop support plus the Section 6 tests; it does not identify the current `mechanized-llbc` revision.

Basis: current mechanization **source** and README.

### The papers do not certify Charon's `rustc`-to-LLBC extraction

Anneal begins above the formal LLBC models. `rustc` lowers Rust to MIR, Charon consumes compiler internals, and Charon emits the LLBC-family representation that Aeneas consumes.

Neither the 2022 translation paper nor the 2024 LLBC soundness result is a proof that the exact Charon revision paired with Aeneas `nightly-2026.06.03` preserves all semantics of `rust-lang/rust` at Anneal's compiler pin.

That bridge includes practical questions already documented elsewhere in the reference corpus: unsupported constructs, opacity, source coverage, item identity, MIR phase choice, inline assembly, FFI, and other representation losses. Those facts must be composed with the paper results rather than subsumed by them.

Basis: **derived** composition boundary, with companion corpus evidence.

### The papers do not certify the production Aeneas translator as an implementation of the formal translation

The papers describe the language-level semantics and translation; the current release contains a substantial OCaml implementation plus backend-specific extraction and support libraries.

A mathematical definition and an implementation of that definition are different artifacts. A compiler-correctness result needs a connection between them. The 2022 paper explicitly places the implementation on the trusted side rather than providing a per-run translation proof, and the 2024 paper's primary theorem chain concerns LLBC concrete/symbolic semantics and borrow checking.

Therefore the formal results are not evidence that every code path in `AeneasVerif/aeneas@ac9f1bc5...` is a verified implementation of the formal rules. Tests, generated fixtures, implementation checks, and code review are valuable engineering evidence, but they are a different evidence class from a mechanized compiler-correctness theorem.

Basis: 2022/2024 **paper scope** + pinned Aeneas **implementation identity** + **derived** distinction.

### External models remain assumptions unless proved against their Rust definitions

The pinned Aeneas release maps external Rust definitions to backend models. The formal LLBC theorems do not automatically prove each hand-written or standard-library model faithful to the actual Rust implementation and contract.

If a proof crosses such a model, its end-to-end meaning depends on that model's correctness or on an explicit trust assumption. The existing `aeneas-external-models-nightly-2026-06-03` report inventories this boundary at the pinned release.

Basis: companion corpus **source evidence** + **derived** composition boundary.

### Lean kernel checking proves the generated theorem, not the omitted translation bridges

Once generated Lean and its proof are accepted without disallowed admissions, Lean provides a strong check of the theorem expressed in the generated Lean environment. That theorem can include functional properties, termination claims, or other specifications.

Kernel checking does not retroactively prove that Charon preserved Rust semantics, that Aeneas implemented the paper translation correctly, or that an external model matches its Rust implementation. Those are premises connecting the Lean theorem back to the source program.

The practical soundness story is therefore a chain, not a single theorem:

1. Rust/compiler semantics and the selected MIR program;
2. Charon extraction into LLBC;
3. the formal LLBC semantic relationship proved in the literature;
4. the production Aeneas translation into Lean;
5. backend/external models and libraries;
6. Lean elaboration/kernel acceptance of the final theorem.

The 2024 paper substantially strengthens step 3. It does not collapse steps 1, 2, 4, and 5 into proved consequences.

Basis: **derived** end-to-end trust decomposition.

### The formal subset is narrower than arbitrary Rust

The 2022 paper explicitly targets programs that avoid unsafe code and interior mutability. The pinned Aeneas README says the current functional model targets a subset of safe Rust and lists unsafe code and concurrency as work for the separation-logic extension.

The 2024 theorem therefore should not be described as a proof of memory safety or functional correctness for arbitrary Rust, unsafe Rust, concurrent Rust, or every library feature. Its non-stuck guarantee is for symbolically checked programs in the formal language and model covered by the theorem.

Basis: 2022 **paper scope**, pinned Aeneas **source documentation**, and **derived** limitation.

## Boundaries

- No fresh Rocq, Coq, Lean, Aeneas, Charon, or paper-artifact execution was performed.
- The report distinguishes paper theorems from implementation claims; it does not reproduce the full formal definitions or proof scripts.
- The current `mechanized-llbc` revision is evidence of a machine-checked development today. It is not asserted to be the exact archived ICFP 2024 artifact.
- The report does not claim the 2022 functional translation is unsound. It records that its implementation is trusted rather than mechanically connected to the source by a compiler-correctness proof in the cited paper.
- The 2024 results are summarized at the level stated by the authors: lower-level/LLBC correctness, symbolic abstraction, borrow-checking non-stuckness, and join preservation. This report does not strengthen those statements into equivalence, total correctness, or arbitrary-Rust memory safety.
- The resizing-hash-table theorem is a proof about the translated program under the translation's trust assumptions; it is not dismissed as mere testing.
- Current implementation proof obligations are a neighboring corpus subject. This report deliberately does not duplicate a code-level audit of Aeneas `nightly-2026.06.03`.
- Charon's own 2025 publication and unrelated papers by overlapping authors are outside the "Aeneas papers" theorem inventory unless they establish a bridge required by this report.
- No claim is made about unpublished or later formal results not represented by the cited papers/current public mechanization.

## Evidence

**Primary publication:** Son Ho and Jonathan Protzenko, *Aeneas: Rust Verification by Functional Translation*, PACMPL 6 (ICFP 2022), DOI `10.1145/3547647`, long version `https://arxiv.org/html/2206.07185v2`.

Relevant paper evidence:

- abstract/contributions: pure ownership-centric LLBC semantics, functional translation, implementation, and hash-table verification;
- evaluation section: functional-correctness proof for the translated resizing hash table;
- related work: Aeneas generates a trusted pure translation;
- comparison with Cogent: Cogent emits a refinement proof per compilation, whereas Aeneas's compiler is trusted;
- future-work statement: mechanically establishing soundness of Aeneas's ownership-centric semantics remained future work in that paper.

**Primary publication:** Son Ho, Aymeric Fromherz, and Jonathan Protzenko, *Sound Borrow-Checking for Rust via Symbolic Semantics*, PACMPL 8 (ICFP 2024), DOI `10.1145/3674640`, long version `https://arxiv.org/abs/2404.02680`.

The abstract states the three central results used here: LLBC correctness relative to a low-level pointer model, correctness of the symbolic abstraction, and borrow-checking/non-stuckness of symbolically checked programs. It also states that the join operation preserves the abstraction and borrow-checking properties and enables loop support.

**Mechanization source:** `AeneasVerif/mechanized-llbc@1268d802a59ddb0672528f24d873ed4b3b28ca0c`.

- `README.md`, blob `997fe7d2f11f12a903c986780db488ddb90fa459`: identifies the repository as a Rocq formalization of LLBC and the 2024 paper as its reference.
- `src/simulations/Simulation_LLBC_plus.v`, blob `2239c02de5f64f051f377fb3a87c1e6e3f855f8c`: simulation machinery for LLBC+ evaluation and joins.
- `src/simulations/Simulation_HLPL_plus.v`, blob `d5e987271903ebd7030089bcb7ed373e071f4087`: forward-simulation infrastructure to the lower-level semantics.
- `src/simulations/Simulation_LLBC_sharp_LLBC_plus.v`, blob `5da80dd4db01dfd7dc17b344aaad47744b69d3ee`: `simulation_LLBC_sharp_LLBC_plus`.

**Pinned implementation documentation:** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: identifies the 2022 translation formalization and 2024 borrow-checking proof; states the current supported subset and the unsafe/concurrency boundary.

**Publication/artifact cross-check:** Microsoft Research publication pages for DOI `10.1145/3547647` and DOI `10.1145/3674640` reproduce the authors' abstracts and bibliographic identity. The ICFP 2024 artifact-evaluation page, `https://icfp24.sigplan.org/details/icfp-2024-artifact-evaluation/7/Sound-Borrow-Checking-for-Rust-via-Symbolic-Semantics`, describes the evaluated artifact as the loop-support Aeneas implementation and its tests; this report does not infer from that description that the current Rocq repository was the evaluated proof artifact.

No evidence above is fresh **execution**.

## Revalidation

For a future Aeneas/Anneal pin:

1. Re-read the pinned Aeneas documentation and identify any new formal-correctness publication or mechanized artifact.
2. Resolve an immutable revision or archived artifact for the 2024 Rocq development, then compare its theorem inventory with the current `mechanized-llbc` head.
3. Check whether a new result mechanically connects `rustc`/Charon extraction to the LLBC formal language.
4. Check whether the production Aeneas translator has acquired a machine-checked implementation-refinement theorem or proof-producing translation mode.
5. Check whether standard-library/external models have independent refinement proofs against their Rust definitions.
6. Re-evaluate the supported semantic subset, especially unsafe code, interior mutability, concurrency, panics, FFI, and other effects.

On an execution-capable surface, build the exact archived mechanization artifact with its declared proof-assistant version and preserve the commit, dependency lock state, commands, and successful proof-check transcript. Separately, run the pinned Charon/Aeneas pipeline on a small discriminating corpus and preserve the generated LLBC/Lean artifacts.

Those execution checks establish artifact health and implementation behavior. They do not, by themselves, fill an absent refinement theorem between the implementation and the formal models.