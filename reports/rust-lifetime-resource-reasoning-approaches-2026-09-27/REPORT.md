# Lifetime and resource reasoning approaches for Rust verification

## Summary

Rust verifiers agree on one difficult fact even when they encode it in very different ways: a mutable borrow temporarily transfers the right to update state, and the verifier must relate the borrower's final state back to the suspended owner when that borrow ends. The principal approaches differ in what they preserve from Rust and where they place the proof burden.

**Semantic-resource approaches** such as RustBelt and RefinedRust represent ownership, borrowing, and lifetime obligations directly as logical resources. They can state what is owned during a borrow and what becomes available after the lifetime ends. This is the most direct family for reasoning about unsafe implementations, but it requires an explicit semantic model and a logic strong enough to describe the resources.

**Functionalization and prophecy approaches** such as RustHorn represent a mutable reference by its current value together with a future value that will become known when the borrow ends. This can erase explicit heaps from verification of well-borrowed safe Rust and reduce verification to first-order constraints. RustHornBelt shows how that style can be given a semantic foundation at an unsafe-library boundary by modeling prophecies inside separation logic. Thrust later integrates the same future-value idea into a refinement type system.

**Functional borrow-calculus approaches** such as Aeneas also exploit Rust's ownership discipline to remove explicit memory reasoning, but use loans and backward functions rather than prophecy variables as their main translation device. The backward function computes the state returned to the lender when a borrow terminates.

**Permission-synthesis approaches** such as Prusti use Rust's type information to synthesize the ownership and framing facts needed by an underlying permission logic. For returned mutable references, Prusti's later “pledge” mechanism describes facts that hold after the returned reference expires. This keeps user specifications close to Rust while delegating mutable-state reasoning to Viper-style permissions.

These techniques are not interchangeable. Some intentionally rely on the Rust type system or a well-borrowedness assumption and therefore simplify away precisely the memory behavior that unsafe Rust can violate. Others retain an explicit semantic resource model and can make unsafe code itself a verification subject. A later architecture should therefore ask two separate questions: **how does the verifier represent a live borrow and its eventual return of state, and what establishes that the source program obeys the assumptions required by that representation?**

Basis: **source/publication** + **derived** cross-system synthesis. No fresh verifier execution was performed.

## Applicability

This report is a comparative reference for published Rust verification techniques, not a prescription for Anneal architecture. It concentrates on the treatment of mutable borrowing, lifetime termination, resource transfer, and the restoration or resolution of state when a borrow ends.

The directly examined subjects are the published works identified in `REPORT.json`:

- RustBelt, POPL 2018, DOI `10.1145/3158154`;
- Prusti's foundational OOPSLA 2019 technique, DOI `10.1145/3360573`;
- RustHorn, ESOP 2020, DOI `10.1007/978-3-030-44914-8_18`;
- Aeneas, ICFP 2022, DOI `10.1145/3547647`;
- RustHornBelt, PLDI 2022, DOI `10.1145/3519939.3523704`;
- RefinedRust, PLDI 2024, DOI `10.1145/3656422`; and
- Thrust, PLDI 2025, DOI `10.1145/3729333`.

Later implementation documentation is used only where the report explicitly identifies it as such. In particular, Prusti's pledge mechanism postdates the core 2019 paper and is treated as an implementation-level extension rather than silently attributed to the 2019 formalization.

“Lifetime/resource reasoning” here means the mechanism by which a verifier represents exclusive or shared access while a Rust borrow is live, relates a reborrow to its parent, and recovers information for the lender after the borrow ends. This report does not attempt a complete survey of Rust verification, alias models, borrow checkers, or separation logics.

The word “safe” below distinguishes Rust code whose use of references is justified by Rust's ordinary typing/borrowing discipline from unsafe implementations that may perform operations outside that discipline. The exact supported Rust subset differs by tool and paper; the comparison does not claim that all techniques accept the same source language.

## Findings

### A common obligation: suspend the lender, reason about the borrower, then recover state

A mutable borrow creates a temporal split in reasoning. While `&mut` access is delegated, the original owner cannot simultaneously use the borrowed place as if it still held an independently mutable value. When the borrow ends, the owner becomes usable again, but its logical value may have changed because the borrower mutated the referent.

Each family below needs a representation of both phases:

1. what capability or value is available while the borrow is live; and
2. what value, resource, or postcondition is returned when the borrow ends.

The systems differ primarily in whether they represent this relationship as a logical resource, a future value, an explicit return translation, or a synthesized permission/postcondition.

Basis: **derived**, from the mechanisms described below.

### RustBelt makes lifetimes and ownership semantic resources

RustBelt gives Rust types semantic interpretations in Iris-style higher-order concurrent separation logic. Its lifetime logic supports temporary borrowing of resources: a borrow transfers access for the duration of a lifetime while preserving a way to recover the underlying resource when that lifetime ends. This lets the semantic interpretation of a Rust reference express more than a raw address or value.

That resource-oriented view matters for unsafe abstractions. The proof of an unsafe library is allowed to choose a semantic interpretation for its abstract types and then prove that each public operation satisfies the interpretation of its Rust type. Safe clients use the interface through the fundamental theorem; they do not repeat the unsafe implementation proof at each call site.

The important lifetime lesson is not a particular syntax but the **resource split across time**. Ownership is not merely a static compiler fact that disappears after type checking. It is represented in the logic strongly enough to justify what can be used during the borrow and what can be recovered later.

Basis: **publication/source** — RustBelt, DOI `10.1145/3158154`, especially its lifetime logic, semantic typing, and unsafe-library verification case studies.

### RustHorn replaces a mutable reference with current and future values

RustHorn takes a different route for well-borrowed Rust. Rather than retain explicit heap and pointer structure in its CHC encoding, it uses Rust's borrowing discipline to functionalize state.

A mutable reference is represented as a pair:

- the **current value**, which can change while the reference is used; and
- the **future value** at the deadline/end of the borrow.

The future component acts like a prophecy variable. At borrow creation its final value is not yet known. When the mutable reference is eventually released, the prophecy is constrained to the final current value. The lender can therefore be represented using that future component even while the borrower temporarily owns update authority.

This encoding is particularly attractive for automated verification because the heap update problem becomes a relation among ordinary logical values. Its simplification is conditional, however: the soundness argument relies on the source program respecting the borrowing discipline for the modeled safe subset. The approach does not by itself provide a semantics for arbitrary pointer-manipulating unsafe code.

Basis: **publication/source** — RustHorn, DOI `10.1007/978-3-030-44914-8_18`; the paper's central mutable-reference encoding explicitly uses the current value and the value at the borrow deadline.

### RustHornBelt puts prophecy-based functional specifications back on a semantic foundation

RustHornBelt addresses the boundary that plain RustHorn leaves open. It combines RustHorn-style first-order functional specifications with RustBelt-style semantic typing so that a safe API implemented using unsafe code can receive a first-order functional specification without simply assuming the unsafe implementation.

The key mechanism is **parametric prophecies** in separation logic. Instead of committing to one guessed future too early, the logic reasons parametrically over possible prophecy assignments until the borrow is resolved. This provides a semantic model for the future-value technique used by RustHorn.

The composition is useful as a design distinction: a verifier can expose a lightweight functional interface to safe client reasoning while discharging the unsafe implementation against a richer semantic logic. Functionalization and semantic resource reasoning can therefore be complementary layers rather than mutually exclusive whole-system choices.

Basis: **publication/source** — RustHornBelt, DOI `10.1145/3519939.3523704`.

### Aeneas returns borrowed state with backward functions instead of prophecy variables

Aeneas exploits Rust's ownership guarantees to eliminate explicit memory reasoning for a substantial safe-Rust subset, but its core account of borrow termination is different from RustHorn's.

Aeneas defines a value-based, ownership-centric semantics for its Low-Level Borrow Calculus (LLBC). It tracks loans and borrows semantically rather than modeling memory addresses. Its functional translation generates **forward** code for ordinary computation and **backward functions** that reconstruct the state returned to lenders when mutable borrows terminate.

Intuitively, if a function receives a mutable borrow and changes its referent, the forward translation computes its ordinary result while a corresponding backward translation describes how the borrowed state is returned. The translation approximates the borrow graph around function calls so it can know which state must flow back.

This preserves the same temporal obligation as prophecy methods—state goes out through the mutable borrow and later comes back—but packages the “future” information as an explicit functional return transformation rather than a prophecy variable carried alongside the current value.

The original Aeneas paper deliberately scopes this simplification away from interior mutability and unsafe code. That boundary is material: the absence of explicit memory is an advantage only where the source semantics and borrow discipline justify eliminating it.

Basis: **publication/source** — Aeneas, DOI `10.1145/3547647`.

### Prusti synthesizes permission reasoning from Rust's type information

Prusti takes another route: it translates the ownership and framing guarantees obtained from Rust type checking into a proof in the Viper permission infrastructure.

The OOPSLA 2019 Prusti technique analyzes compiler information and synthesizes a “core proof” in an automated separation-logic-like permission system. User contracts can then focus on functional properties at the Rust level rather than manually spelling out the ownership and frame conditions already implied by the language's type system.

This creates an important dependency boundary. The permission proof is simpler because Rust typing establishes facts about aliasing and mutation that the verifier lifts into its logic. If those facts do not hold for a source feature—most notably interior mutability, or arbitrary unsafe manipulation—the framing abstraction needs additional treatment rather than being assumed unchanged.

Later Prusti documentation adds **pledges** for functions that return references. An `after_expiry` pledge can state a property that becomes available once the returned reference's lifetime ends; `before_expiry` can refer to the state immediately before expiry. This is another explicit answer to the “returned mutable borrow” problem: the caller receives a reference now and a deferred fact about the lender once the reference is no longer live.

RefinedRust's comparison notes an expressiveness difference: its borrow-name mechanism can describe cases that Prusti's then-current pledge implementation could not, such as certain mutable references nested inside `Option`. That is a tool/version boundary, not a general impossibility result for permission logics.

Basis: **publication** — Prusti, DOI `10.1145/3360573`; **documentation/comparison** — later Prusti pledge documentation and RefinedRust's PLDI 2024 comparison.

### RefinedRust combines RustBelt lifetime logic with value-level refinement information

RefinedRust keeps the semantic-resource foundation needed for unsafe code but adds automation and functional refinements.

Its types are interpreted as separation-logic predicates in Coq, building on RustBelt's lifetime logic. To describe mutable references precisely, RefinedRust uses **borrow names** and related type-state machinery to connect the value visible through a borrow with the value that must eventually flow back to the borrowed place. This lets specifications express reborrowing and APIs that return mutable references while still reasoning about the owner after the lifetime ends.

The approach can also temporarily weaken what is known about a borrowed location and restore a stronger fact when the relevant lifetime ends. This is the same temporal pattern as RustBelt—resources are split into what is usable during the lifetime and what becomes available afterward—but enriched with functional information about values.

RefinedRust's paper emphasizes that it targets both safe and unsafe Rust against an explicit model and produces Coq-checked proofs. It therefore pays the cost of a richer semantic account in exchange for being able to make unsafe pointer-manipulating implementations themselves part of the proof rather than treating them as an assumed functional primitive.

Basis: **publication/source** — RefinedRust, DOI `10.1145/3656422`.

### Thrust places prophecy values inside a refinement type system

Thrust demonstrates that the future-value idea can live directly inside a refinement type system rather than only in a CHC translation.

Like RustHorn, it represents a mutable borrow using a current value and a prophecy for the final value. When a borrow or reborrow is created, the owner's logical state is related to the new prophecy. When that mutable reference is released, the prophecy is fixed to the final current value, propagating the update back to the original owner.

Thrust's formal soundness theorem is conditional on **well-borrowedness**, expressed using an adapted Stacked Borrows-style model. The paper deliberately delegates the aliasing/borrowing guarantee to Rust rather than making the refinement type system itself establish arbitrary unsafe alias behavior. This keeps the verification layer focused on functional correctness and makes automated CHC-based inference possible.

That conditional soundness statement is an important reusable pattern: a resource-light representation can be precise and useful if another layer establishes the borrowing invariant it relies on. It is not evidence that the same representation automatically covers operations that invalidate or bypass that invariant.

Basis: **publication/source** — Thrust, DOI `10.1145/3729333`.

### Flux shows another type-directed strong-update point in the design space

Flux is not one of the subjects in `REPORT.json`, but it provides a useful neighboring comparison. Flux refines Rust types with logical information and exploits ownership to support strong updates without exposing users to a full separation-logic proof. Its published soundness also makes the dependence on well-borrowed executions explicit.

The important distinction for this report is that strong update permission alone does not solve every “future owner state” problem. Thrust's evaluation and discussion identify cases where prophecy information improves precision when the verifier must propagate a dynamically selected mutable borrow's final value back to the owner.

Thus “uses Rust ownership for strong updates” and “can express the value restored after an arbitrary mutable-borrow lifetime” are separate capabilities.

Basis: **publication/comparison** — Flux, DOI `10.1145/3591283`; Thrust, DOI `10.1145/3729333`.

### The approaches can be compared along four independent axes

A useful comparison separates four questions that are often conflated.

**1. What represents the live borrow?**

- RustBelt / RefinedRust: logical lifetime/ownership resources.
- RustHorn / Thrust: current value plus future/prophecy value.
- Aeneas: loans/borrows in LLBC and the functional value being lent.
- Prusti: permissions inferred from Rust typing and represented in Viper.

**2. How does information return to the lender?**

- RustBelt / RefinedRust: lifetime resources allow recovery/restoration after the borrow ends.
- RustHorn / Thrust: resolve the prophecy to the final borrower value.
- Aeneas: run the generated backward function.
- Prusti: regain permissions; for returned references, a pledge can expose an after-expiry fact.

**3. What justifies removing or abstracting memory?**

- RustHorn, Aeneas, Thrust, and Prusti deliberately exploit guarantees supplied by Rust's ownership/borrowing discipline.
- RustBelt and RefinedRust retain richer semantic state because their target includes proving unsafe abstractions or unsafe implementations themselves.
- RustHornBelt bridges the two: lightweight prophecy-based client specifications can be justified by a semantic proof of the unsafe boundary.

**4. Where is source-language borrowing trusted or re-proved?**

This varies by system and version. A paper may prove a core calculus while the real frontend remains trusted, or assume a well-borrowed execution while relying on Rust's checker to establish that assumption. RefinedRust's frontend, for example, supplies lifetime annotations/hints to proof generation, while the proof layer is designed to check rather than blindly trust those annotations. Aeneas uses its own ownership-centric LLBC semantics. Thrust states soundness under well-borrowedness rather than tying the theorem to one borrow-checker implementation.

Basis: **derived**, with the component claims grounded in the cited publications.

### A later verifier should record both the resource model and its source-side premise

The main reusable lesson is a documentation requirement rather than an architectural choice.

A statement such as “mutable references are modeled functionally” is incomplete unless the verifier also records why that is sound for the source operations admitted into the model. Likewise, “ownership is a separation-logic resource” is incomplete without saying which Rust memory behaviors the operational semantics and resource interpretation cover.

For any Rust verification pipeline, two artifacts therefore deserve separate identities:

1. the **borrow/resource representation** used by the proof layer; and
2. the **source-to-model argument** establishing that admitted Rust operations satisfy the assumptions of that representation.

This separation is especially important when safe and unsafe Rust use different reasoning layers.

Basis: **derived** from the contrasts above.

## Boundaries

- This is a representative comparison, not a complete survey of Rust verification systems.
- No verifier, Rust compiler, proof assistant, CHC solver, or artifact was executed for this report.
- The report does not establish that current implementations exactly match their published papers. Implementation details can and do evolve independently.
- RustBelt, RustHornBelt, and RefinedRust use substantially richer logics than the short descriptions here; this report extracts only the lifetime/resource mechanisms needed for the comparison.
- RustHorn and Thrust simplify verification by depending on well-borrowed behavior. Their results must not be generalized to arbitrary unsafe pointer manipulation without an additional semantic argument.
- Aeneas's 2022 paper explicitly scopes its memory-eliminating translation away from interior mutability and unsafe code. Later Aeneas development, including separation-logic work, is a different subject and is covered elsewhere in the corpus.
- Prusti's 2019 core paper and its later pledge mechanism are temporally distinct. This report does not attribute every current Prusti feature to the 2019 formalization.
- The current limitations of Prusti pledges reported by RefinedRust/Thrust are observations about the compared tool versions, not a theorem that pledges or permission logics cannot express those patterns.
- Flux and Gillian-Rust are adjacent systems rather than directly identified report subjects. Flux is used only to sharpen the strong-update-versus-future-state distinction; Gillian-Rust is omitted from the main taxonomy despite combining RustBelt lifetime logic and RustHornBelt prophecies because the existing subjects already expose that composition.
- The report does not survey Polonius, NLL, two-phase borrowing, Stacked Borrows, Tree Borrows, or current borrow-checker implementation details except where a paper states them as a soundness premise.
- The report does not compare proof automation, performance, annotation burden, supported Rust syntax, or theorem-prover TCB comprehensively.
- “Lifetime ends” is used at the proof-model level. It does not imply a runtime event in compiled Rust.
- The report does not claim that these techniques prove Rust's normative memory model; several operate over research calculi or explicit soundness assumptions.

## Evidence

### RustBelt

- Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, and Derek Dreyer, *RustBelt: Securing the Foundations of the Rust Programming Language*, PACMPL 2 (POPL), Article 66, DOI [`10.1145/3158154`](https://doi.org/10.1145/3158154).
- The paper's semantic typing, lifetime logic, fundamental theorem, adequacy theorem, and unsafe-library case studies establish the semantic-resource model summarized here.

### Prusti

- Vytautas Astrauskas, Peter Müller, Federico Poli, and Alexander J. Summers, *Leveraging Rust Types for Modular Specification and Verification*, PACMPL 3 (OOPSLA), Article 147, DOI [`10.1145/3360573`](https://doi.org/10.1145/3360573).
- The paper describes compiler analysis that synthesizes a core proof in an automated permission/separation-logic setting and interweaves Rust-level functional specifications.
- ETH Zurich's Prusti project documentation describes the same high-level split: ownership/framing information is lifted from Rust type checking into the verification proof.
- Later Prusti documentation for pledges defines `after_expiry`/`before_expiry` specifications for references returned by functions. This is implementation documentation rather than evidence about the original 2019 calculus.

### RustHorn

- Yusuke Matsushita, Takeshi Tsukada, and Naoki Kobayashi, *RustHorn: CHC-Based Verification for Rust Programs*, ESOP 2020, DOI [`10.1007/978-3-030-44914-8_18`](https://doi.org/10.1007/978-3-030-44914-8_18).
- The paper's central encoding represents a mutable reference by its current value and the value at the borrow deadline, explicitly relating the second component to prophecy variables.

### Aeneas

- Son Ho and Jonathan Protzenko, *Aeneas: Rust Verification by Functional Translation*, PACMPL 6 (ICFP), Article 116, DOI [`10.1145/3547647`](https://doi.org/10.1145/3547647).
- The abstract and body characterize LLBC as value-based and ownership-centric and describe the borrow-graph approximation and backward functions used to translate borrow termination.
- The paper explicitly states that the memory-eliminating approach targets programs not relying on interior mutability or unsafe code.

### RustHornBelt

- Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, and Derek Dreyer, *RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code*, PLDI 2022, DOI [`10.1145/3519939.3523704`](https://doi.org/10.1145/3519939.3523704).
- The paper gives a machine-checked foundation for RustHorn-style first-order specifications of safe APIs implemented with unsafe code and introduces parametric prophecies as the separation-logic mechanism for RustHorn-style future values.
- Artifact: Zenodo DOI [`10.5281/zenodo.6417462`](https://doi.org/10.5281/zenodo.6417462). The artifact was identified but not downloaded or executed.

### RefinedRust

- Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, and Derek Dreyer, *RefinedRust: A Type System for High-Assurance Verification of Rust Programs*, PACMPL 8 (PLDI), Article 192, DOI [`10.1145/3656422`](https://doi.org/10.1145/3656422).
- The paper describes refined ownership types interpreted as Iris separation-logic predicates, builds on RustBelt's lifetime logic, and uses borrow-name machinery to retain functional information across mutable borrowing and reborrowing.
- Its related-work section directly compares RustHorn's current/future-value encoding, Prusti's type-derived permissions and pledges, and Aeneas's functional borrow calculus.

### Thrust

- Hiromi Ogawa, Taro Sekiyama, and Hiroshi Unno, *Thrust: A Prophecy-Based Refinement Type System for Rust*, PACMPL 9 (PLDI), Article 230, DOI [`10.1145/3729333`](https://doi.org/10.1145/3729333).
- The paper represents a mutable reference with a current value and a prophecy for its final value, propagates the final value back to the owner on release, handles nested/partial reborrowing, and states soundness under a well-borrowedness assumption formulated using an adapted Stacked Borrows-style model.

### Adjacent comparison: Flux

- Nico Lehmann, Adam T. Geller, Niki Vazou, and Ranjit Jhala, *Flux: Liquid Types for Rust*, PACMPL 7 (PLDI), Article 169, DOI [`10.1145/3591283`](https://doi.org/10.1145/3591283).
- Flux uses Rust ownership to support strong updates in a refinement type system. It is used only as an adjacent comparison, not as a primary subject of this report.

No fresh **execution** evidence was produced.

## Revalidation

The cheapest revalidation depends on which claim changes.

**For the conceptual taxonomy**, first check whether newer publications materially change one of the mechanisms rather than assuming a newer tool version preserves the same encoding. The high-signal discriminators are:

- Does a mutable borrow still carry an explicit logical resource, a current/future pair, a backward translation, or a permission plus deferred postcondition?
- What exact event or proof rule restores information to the lender?
- Does the soundness theorem prove the borrowing discipline itself, or assume a well-borrowed/type-checked source program?
- Can the model verify the unsafe implementation that establishes a safe abstraction, or only consume an assumed functional interface?

**For RustBelt-family semantic-resource reasoning**, compare the lifetime/borrow rules and semantic interpretation of mutable references. If a successor logic changes how a borrow is opened, shortened, reborrowed, or returned, treat that as a material change even if the surface notation is similar.

**For RustHorn/Thrust-style prophecies**, inspect the mutable-reference representation and release rule. A minimal discriminating example is:

1. own a value `x`;
2. create `&mut x`;
3. pass/reborrow it through a function that mutates it;
4. end the borrow; and
5. prove a property of `x` that depends on the final borrower value.

Record where the future value is introduced and where it is resolved.

**For Aeneas-style functional translation**, inspect the current borrow-termination translation and generated backward functions around a mutable-reference call. Preserve the generated functional term for a small nested-reborrow example. If a newer Aeneas backend introduces an explicit spatial/heap semantics for unsafe code, record that as a distinct mechanism rather than silently extending the 2022 memory-elimination result.

**For Prusti-style permission reasoning**, inspect both the compiler-to-permission encoding and the current pledge/expiry mechanism. A returned-`&mut` example is the cheapest probe: determine which permissions are unavailable while the reference is live and exactly which assertion becomes available on expiry.

For any system intended to justify unsafe Rust, add a second probe that cannot be discharged merely by assuming ordinary borrow checking—for example, an implementation that uses a raw pointer internally while exposing a safe mutable-reference API. The revalidation should make clear which layer proves the unsafe operation and which layer only consumes the safe interface.
