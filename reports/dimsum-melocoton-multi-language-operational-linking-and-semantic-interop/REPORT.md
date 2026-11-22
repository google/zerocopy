# Multi-Language Operational Linking and Semantic Interoperability: DimSum, Melocoton, the Compositional CompCert Lineage, and Cerise

## Summary

Four major lines of mechanized verification formalize multi-language linking and cross-boundary interoperability through distinct operational architectures, making incompatible assumptions about memory, control flow, and the trustworthiness of linked code:

1. **Decentralized event-based linking — DimSum (POPL 2023):** Models every module as a labelled transition system with dual (demonic + angelic) nondeterminism over a language-specific event alphabet (`Rec`, `Asm`, `Spec`). Horizontal compositionality (`asm-link-horizontal`, `rec-link-horizontal`, `rec-to-asm-link`) is proved once for a generic turn-based linking combinator; vertical compositionality additionally eliminates stacked wrappers (`rec-to-asm-vertical`, needed for `Mem2Reg`). Because linking is just another combinator, non-well-bracketed control such as coroutines (`⊕_coro`) is supported by swapping the linker rather than altering the core metatheory.
2. **FFI memory membranes and view reconciliation — Melocoton (OOPSLA 2023):** Keeps language-local Iris logics (`Iris_ML`, `Iris_C`) with independent heaps and connects them via a dual-nondeterministic operational wrapper (`[e]_FFI ⊕ p`) tracking logical-to-ML locations (`chi`), a stable block store (`zeta`), and a demonically re-chosen address map (`theta`) reified as a separation-logic token `GC(theta)`. Exclusive-ownership view reconciliation (`ml_to_mut` / `mut_to_ml`) preserves language-local frame rules, reentrant callbacks are mediated by an interface-parameterized runtime protocol (`Ψ_FFI^Π`), and adequacy (`Theorem 4.2`) requires **Transfinite Iris** to break the circularity between step-indexing and angelic witness extraction. Its `umrel` multirelations use the **exact opposite polarity** to DimSum's transition systems.
3. **Shared-IR interaction semantics and simulation algebras — Compositional CompCert (POPL 2015), CompCertM (POPL 2020), and CompCertO (PLDI 2021):** All three retain CompCert's shared block-and-offset memory model and a well-bracketed LIFO call/return interface, differing in how they overcome the open-simulation composition barrier:
   - *Compositional CompCert* forces a single heavyweight `StructuredInjection` across every pass (+145.77% pass-proof overhead over CompCert 2.1, per CompCertM §1).
   - *CompCertM* introduces **RUSC** (Refinement Under Self-related Contexts) over four memory relations and repairs physical-assembly inadequacy by turning violations of three calling-convention assumptions (callee-save preservation, non-info-passing register pointers, and caller outgoing stack-arguments ownership) into assembly-boundary UB (+18.73% pass-proof overhead on CompCert 3.5).
   - *CompCertO* introduces an algebra of Kripke simulation conventions `R : A_1 ⇔ A_2` (`C := R* · wt · CA · vainj_A`, +3% SLOC) and shows explicitly that asymmetric pass conventions (`injp ↠ inj`) break horizontal compositionality unless rectified via Clight self-simulations.
4. **Hardware capability-machine logical relations — Cerise (POPL 2021, JACM 2024):** Drops all behavioral trust in unknown assembly. Known and untrusted code share one flat address space and transfer control by ordinary `jmp`. A unary Iris logical relation (`V(w)` / `E(pc)`) with the Fundamental Theorem of the Logical Relation (FTLR) serves as a universal contract for arbitrary machine code: sentry (`E`) capabilities enforce local-state encapsulation, while local + uninitialized (`URW`/`URWL`/`URWLX`) capabilities and public/private future worlds enforce well-bracketed control flow (mechanically verifying the awkward example) without clearing unused stack memory.
5. **Toy-model mechanization (`[kernel-checked proof]` `[toy model]`):** A standalone Mathlib-free Lean `v4.34.1` mechanization under [`lean/`](lean/) proves 13 theorems across `Toy/EventLinking.lean` and `Toy/ReentrantMembrane.lean`: preorder and horizontal turn-routing compositionality of dual-nondeterministic event linking (weak payload-dropping analogue), DimSum-vs.-Melocoton polarity inversion and one-step WP stuckness/vacuity breakdown, breakdown of naive shared-state linking under reentrant callbacks, well-bracketed vs. non-bracketed return-pointer replay on the awkward example, and soundness of a framed rely-guarantee/membrane contract under arbitrary reentrant callback depth. **Model–system relation: none proved.**

## Applicability

This report synthesizes seven directly read primary-source peer-reviewed papers (plus five Crossref-verified lineage citations) alongside a standalone Lean `v4.34.1` toy-model mechanization (`observed_at: 2026-11-22`). The subjects in `REPORT.json` relate as a **four-way architectural comparison** of operational linking and semantic interoperability frameworks:

- **DimSum** (POPL 2023) and **Melocoton** (OOPSLA 2023) share dual-nondeterministic stateful wrappers in Coq/Iris, with Melocoton adapting DimSum's wrapper idea to a garbage-collected FFI with program-logic verification rather than refinement.
- **Compositional CompCert** (POPL 2015), **CompCertM** (POPL 2020), and **CompCertO** (PLDI 2021) form a direct technical lineage addressing open-module separate compilation and C/assembly linking over the CompCert memory model.
- **Cerise** (POPL 2021 on uninitialized capabilities and JACM 2024 on the core sentry-capability framework) provides the contrasting hardware-enforced, zero-trust model against arbitrary untrusted assembly in Iris/Coq.
- **Lean 4 `v4.34.1`** (`5045d0056413266e57c625dcd7c365b10e377c52`) is the proof assistant used to check the standalone toy model in [`lean/`](lean/). **Model–system relation: none proved.**

### Cross-references to adjacent corpus packages (material not duplicated here)

To avoid duplication, this report omits topics already covered in three adjacent `reference-corpus/1` packages and focuses exclusively on the deep comparative operational-linking mechanics and composition-failure modes of the four systems above:

- **`semantic-multi-language-interop-dimsum-melocoton-and-linking-types`**: Covers Matthews–Findler syntactic multi-language lump/natural embeddings (TOPLAS 2009), Patterson–Ahmed linking types (SNAPL 2017), Patterson–Mushtak–Wagner–Ahmed realizability after compilation (PLDI 2022), VeriFFI (POPL 2025), Abate et al.'s 26 robust property preservation criteria (CSF 2019), and a baseline introduction to DimSum and Melocoton (noting in its `## Boundaries` that it did not inspect the texts of Compositional CompCert, CompCertM, CompCertO, or Cerise).
- **`compositional-correctness-linking-and-whole-program-optimization`**: Covers multi-CGU Rust compilation, ThinLTO summary importing, `-Zshare-generics`, and closed-world WPO passes (`Unusedglob`, `Internalize`, `IPSCCP`, `DAE`, `GlobalDCE`, devirtualization), with a high-level summary table of CompCert variants.
- **`mswasm-colored-memory-safety-van-strydonck-linear-capabilities-georges-uninitialized-capabilities-skorstengaard-local-capabilities-richwasm-and-cherivoke-sweeping-revocation`**: Covers temporal dangling-handle revocation across MSWasm, StkTokens, local/uninitialized/directed capabilities, RichWasm, and CHERIvoke/Cornucopia.

All examined formal systems are **sequential** (single-threaded); none of the four primary frameworks models shared-memory concurrency, hardware weak memory, or C++/Rust unwinding across FFI boundaries in the cited papers.

## Findings

### 1. Primary-Source Coordinates and Attribution Clarifications

Basis: documentation (Crossref REST records verified 2026-11-22 and front matter of the seven downloaded author-hosted PDFs).

| System / Lineage Entry | Verified Primary Coordinates | Text Read? |
| :--- | :--- | :--- |
| **DimSum** | Michael Sammler, Simon Spies, Youngju Song, Emanuele D'Osualdo, Robbert Krebbers, Deepak Garg, Derek Dreyer. *DimSum: A Decentralized Approach to Multi-language Semantics and Verification*. PACMPL 7(POPL), Article 27, pp. 775–805, Jan. 2023. DOI `10.1145/3571220`. | Yes (author PDF) |
| **Melocoton** | Armaël Guéneau, Johannes Hostert, Simon Spies, Michael Sammler, Lars Birkedal, Derek Dreyer. *Melocoton: A Program Logic for Verified Interoperability Between OCaml and C*. PACMPL 7(OOPSLA2), Article 247, pp. 716–744, Oct. 2023. DOI `10.1145/3622823`. | Yes (author PDF) |
| **Compositional CompCert** | Gordon Stewart, Lennart Beringer, Santiago Cuellar, Andrew W. Appel. *Compositional CompCert*. POPL '15, pp. 275–287, Jan. 2015. DOI `10.1145/2676726.2676985`. | Yes (author PDF) |
| **CompCertM** | Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, Chung-Kil Hur. *CompCertM: CompCert with C-Assembly Linking and Lightweight Modular Verification*. PACMPL 4(POPL), Article 23, pp. 1–31, Jan. 2020 (online Dec. 2019). DOI `10.1145/3371091`. | Yes (author PDF) |
| **CompCertO** | Jérémie Koenig, Zhong Shao. *CompCertO: Compiling Certified Open C Components*. PLDI '21, pp. 1095–1109, June 2021. DOI `10.1145/3453483.3454097` (Yale TR `YALEU/DCS/TR-1556`). | Yes (author PDF) |
| **Cerise (JACM)** | Aïna Linn Georges, Armaël Guéneau, Thomas Van Strydonck, Amin Timany, Alix Trieu, Dominique Devriese, Lars Birkedal. *Cerise: Program Verification on a Capability Machine in the Presence of Untrusted Code*. J. ACM 71(1), Article 3, pp. 1–59, Feb. 2024. DOI `10.1145/3623510`. | Yes (author PDF) |
| **Cerise (POPL '21 — Uninitialized Capabilities)** | Aïna Linn Georges, Armaël Guéneau, Thomas Van Strydonck, Amin Timany, Alix Trieu, Sander Huyghebaert, Dominique Devriese, Lars Birkedal. *Efficient and Provable Local Capability Revocation using Uninitialized Capabilities*. PACMPL 5(POPL), Article 6, pp. 1–30, Jan. 2021. DOI `10.1145/3434287`. | Yes (author PDF) |
| *Lineage (metadata only)* | Koenig & Shao, *Refinement-Based Game Semantics for Certified Abstraction Layers*, LICS '20, pp. 633–647, DOI `10.1145/3373718.3394799`; Skorstengaard, Devriese, Birkedal, *Reasoning About a Machine with Local Capabilities*, ESOP '18 (`10.1007/978-3-319-89884-1_17`) & TOPLAS 42(1) 2019 (`10.1145/3363519`); Skorstengaard, Devriese, Birkedal, *StkTokens*, POPL '19 (`10.1145/3290332`); Georges, Trieu, Birkedal, *Le temps des cerises*, OOPSLA1 '22 (`10.1145/3527318`). | Metadata only |

**Venue/attribution clarifications (preserving accuracy against circulating misattributions):**
- **CompCertO** was published at **PLDI 2021** (`10.1145/3453483.3454097`), not OOPSLA 2020 or POPL 2021; Koenig and Shao's 2020 precursor paper on refinement-based game semantics appeared at **LICS 2020** (`10.1145/3373718.3394799`).
- **Cerise's** primary papers by Georges et al. appeared at **POPL 2021** (`10.1145/3434287`, uninitialized capabilities), **OOPSLA1 2022** (`10.1145/3527318`, directed capabilities), and **JACM 2024** (`10.1145/3623510`, core Cerise with sentry capabilities); the earlier **ESOP 2018** local-capabilities paper (`10.1007/978-3-319-89884-1_17`) was authored by Skorstengaard, Devriese, and Birkedal, and there is no ESOP 2021 archival paper by Georges et al.

---

### 2. Four-Way Architectural Comparison Matrix

Basis: documentation (all seven primary PDFs) + derived (comparative synthesis).

| Architectural Dimension | **DimSum** (POPL '23) | **Melocoton** (OOPSLA '23) | **CompCert Lineage** (CompComp '15 / CompCertM '20 / CompCertO '21) | **Cerise** (POPL '21 / JACM '24) |
| :--- | :--- | :--- | :--- | :--- |
| **Linking mechanism** | Decentralized turn-based event combinators (`⊕_a`, `⊕_r`, `⊕_coro`) + stateful wrappers (`⌈·⌉_{r⇌a}`) | Operational FFI wrapper + symmetric linker (`[e]_FFI ⊕ p`) with protocol cancellation (`Link`) | Shared interaction semantics (`AtExternal`/`AfterExternal`) or open LTS horizontal product (`L_1 ⊕ L_2`) | Single flat address space; control transfers via ordinary `jmp` to capabilities |
| **Memory model requirement** | **Heterogeneous per language** (`Rec` block+offset vs. `Asm` flat byte map); translated by wrapper state `w` | **Heterogeneous per language** (`λ_ML` heap vs. `λ_C` heap); bridged by membrane `(chi, zeta, theta)` + `GC(theta)` | **Fixed global CompCert memory model** (`block × offset` + permissions) across all languages | **Single flat word-addressed memory** with hardware capability tags & bounds |
| **Control-flow assumption** | **Pluggable per linker** (`Rec` LIFO stack, `Asm` jumps, `⊕_coro` coroutines) | **LIFO call/return + reentrant `callback`**; no exceptions or continuations | **Fixed LIFO well-bracketed call/return** in all three variants | **Unrestricted jumps**; WBCF enforced only where calling convention (`scallU` + local/U-caps) establishes it |
| **Primary proof obligation** | Branching-sensitive coinductive refinement `M_1 ⪯ M_2` | Language-local Iris Hoare triples (`Iris_ML`, `Iris_C`) + umbrella adequacy (`Iris_{ML+C}`) | Open forward / mixed simulations (`StructuredInjection`, RUSC `≽_R`, or Kripke `≤_{R↠S}`) | Iris program logic (known code) + unary logical relation FTLR (`V(w) → E(w)`, unknown code) |
| **Trust in unknown / foreign code** | Must satisfy the event-level refinement / wrapper protocol | Must satisfy its declared Iris interface `Π` (or `Ψ_FFI^Π`) | CompComp: reach-closed structured injection; CompCertM: self-related under `R` + 3 ABI UB rules; CompCertO: simulation convention `C` | **Zero behavioral trust**; adversary may run arbitrary instructions using only initially granted capabilities |
| **Horizontal composition** | Generic `link_mod_trefines` + `rec-to-asm-link` | Symmetric `Link` rule cancelling dual assumptions `Π` / `Ψ` | CompComp Thm. 2; CompCertM Thm. 2.1 / Cor. 5.4; CompCertO Thm. 3.4 (requires symmetric convention `R ↠ R`) | Independent verification of mutually untrusting components via FTLR + Iris invariants |
| **Vertical composition** | Preorder transitivity (Lem. 3.1) + wrapper elimination (`rec-to-asm-vertical`) | Not a multi-pass compiler; embeds `Iris_ML`/`Iris_C` into `Iris_{ML+C}` | CompComp Thm. 1 (heavy `compose_sm`); CompCertM RUSC transitivity; CompCertO Thm. 3.7 (`R · S` algebra) | Adequacy (Thm. 1) lifts Iris invariants directly to concrete capability-machine traces |
| **Coq / Iris mechanization** | Coq + Iris (for wrapper Kripke world); safety only | Coq + **Transfinite Iris** (ordinal step-indices for angelic adequacy) | Coq (CompCert 2.1 / 3.5 / 3.x extensions; no Iris) | Coq + Iris (with `W^std`/`W^cus` STSs for POPL '21) |

---

### 3. DimSum: Decentralized Event-Based Linking and Wrapper Compositionality

Basis: documentation (`dimsum.pdf` §§2–6, Figs. 5, 14, 15, Lemma 3.1, Theorems 3.2 and 5.1; Coq identifier names `link_mod`, `link_mod_trefines`, `r2a_bij_vertical`, and `VisNoAng` correspond to DimSum's public Coq artifact `iris/dimsum` at `4fad7a63` and the companion report `semantic-multi-language-interop-dimsum-melocoton-and-linking-types`, rather than direct full-script inspection of `.v` proofs here).

Beyond the dual-nondeterministic transition-system basics documented in `semantic-multi-language-interop-dimsum-melocoton-and-linking-types`, DimSum's distinct contribution to operational linking rests on three mechanisms:

1. **Generic horizontal compositionality via turn-based routing (`link_mod`):** Every language-specific linking operator (`⊕_a`, `⊕_r`, `⊕_coro`) is instantiated from a single generic linking combinator over turn state `d ∈ {E, L, R}` and linking state (e.g., `None` for `Asm`, a caller-turn stack `ds` for `Rec`, or a coroutine slot `(d, None)` for `⊕_coro`; Fig. 14). Because monotonicity of `link_mod` is proved once for all modules satisfying the side condition that visible events make no nontrivial angelic choice (Coq typeclass `VisNoAng`), every instantiated linker automatically satisfies horizontal compositionality (`asm-link-horizontal`, `rec-link-horizontal`; Fig. 5).
2. **Wrapper distribution and vertical wrapper elimination:** Linking two compiled `Rec` modules in `Asm` relies on two distinct laws (Fig. 5 & §5):
   - *Wrapper-link distribution (`rec-to-asm-link`):* `⌈M_1⌉_{r⇌a} ⊕_a ⌈M_2⌉_{r⇌a} ⪯ ⌈M_1 ⊕_r M_2⌉_{r⇌a}`. When `M_1` emits a demonic `Rec` call translated by its wrapper into an `Asm` jump, the linked peer wrapper's angelic decoding of that `Asm` jump into a `Rec` call is discharged by forwarding `M_1`'s exact high-level value and Kripke block-map `w`.
   - *Vertical compositionality beyond transitivity (`rec-to-asm-vertical`, §5):* Transitivity of `⪯` (Lemma 3.1) alone leaves stacked wrappers when an optimization pass changes the memory layout (specifically `Mem2Reg`, which removes stack-allocated local variables and therefore refines `⟦R⟧_r` only up to a `Rec`-to-`Rec` memory-bijection wrapper `⌈·⌉_{r⇌r}`). Vertical compositionality proves `⌈⌈M⌉_{r⇌r}⌉_{r⇌a} ⪯ ⌈M⌉_{r⇌a}` (Coq lemma `r2a_bij_vertical`, per artifact documentation), collapsing the pass wrapper into the `Rec`-to-`Asm` wrapper so Theorem 5.1 (`⟦↓R⟧_a ⪯ ⌈⟦R⟧_r⌉_{r⇌a}`) exposes a pass-independent top-level interface.
3. **Decentralized non-well-bracketed linking (`⊕_coro`, Fig. 14):** To give a `Rec`-level specification to a coroutine library written in `Asm`, DimSum defines a custom linking relation `⇝_coro` whose rule `coro-link-yield` routes `Call(yield, [v], m)` from module `d ∈ {L, R}` directly into `Return(v, m)` for the peer `d' ≠ d`. Because DimSum does not hardwire a global LIFO call stack into its notion of module, `⊕_coro` is horizontally compositional out of the box—an explicit contrast with CompCertO/CompCertM (§6).

**Structural cost of DimSum's design:** Every `Rec` `Call`/`Return` event and every `Asm` `Jump` event carries the **entire** memory state `m` (and register file `r`). Consequently, memory separation and framing are not native to the event alphabet; they must be encoded inside stateful wrappers using Iris ghost state (`w`, ownership of private blocks) or proved relationally across the whole heap.

---

### 4. Melocoton: FFI Memory Membranes, Reentrant Callbacks, and Transfinite Adequacy

Basis: documentation (`melocoton.pdf` §§2–4, Figs. 8–10, Theorems 4.1 and 4.2; Coq identifier names `LlocPrivate`, `ml_to_mut`, `mut_to_ml`, and `prim_step_no_NB` are cited from the companion report `semantic-multi-language-interop-dimsum-melocoton-and-linking-types`, which inspected `logsem/melocoton` Coq sources).

Where DimSum proves whole-program trace refinement (`M_1 ⪯ M_2`), Melocoton verifies functional correctness across a garbage-collected boundary (`λ_ML` + `λ_C`) via a **memory membrane** embedded in a three-logic Iris architecture:

1. **Membrane encapsulation and exclusive-ownership view reconciliation:** Rather than forcing `λ_ML` and `λ_C` into a common memory model, the wrapper `[e]_FFI` maintains three ghost/operational maps—`chi` (logical location → ML location or `LlocPrivate`), `zeta` (stable block store), and `theta` (logical location → current C address)—and exposes `GC(theta)` as a single exclusive Iris resource in `Iris_C`. View-reconciliation updates (`ml_to_mut`, `mut_to_ml`) exchange `l ↦_ML vs` for `g ↦_blk[0|mut] lvs` (and back) only while holding `GC(theta)`. Because ownership of a mutable block is **exclusive** to one view at any instant, neither `Iris_ML` nor `Iris_C` loses its standard separation-logic frame rule.
2. **Protocol cancellation and reentrant callbacks (`Theorem 4.1`, Fig. 9):** Verification splits into (1) `{True} e @ ∅, Π {V. ∃n. V = n ∗ ϕ(n)}_ML` in `Iris_ML` and (2) `Ψ_FFI^Π |=_C p : [Π]_FFI` in `Iris_C`, where `[Π]_FFI` wraps ML-level interface `Π` into a C-level protocol (quantifying over `theta`, translating `V ~_ML v ~_{theta,C} w` on entry and returning a fresh `theta'` on exit). Crucially, the runtime interface `Ψ_FFI^Π` is **parameterized by `Π`**: its `ExecCallback` rule allows C code to invoke an ML closure, which may execute arbitrary ML code and **re-enter** C functions specified in `Π` before returning to C with a **fresh** `GC(theta')` token (invalidating every unrooted C pointer held across the callback). Embedding both proofs (`EmbedML`, `EmbedC`) into `Iris_{ML+C}` and applying symmetric `Link` cancels `[Π]_FFI` against `Ψ_FFI^Π`, yielding `∅ |=_{ML+C} [e]_FFI ⊕ p : main(ϕ)` (`Theorem 4.1`).
3. **Why Transfinite Iris is mandatory for adequacy (`Theorem 4.2`, §4.3):** In Melocoton's `Iris_{ML+C}` weakest precondition (`wp e @ p, Ψ {Φ}`, Fig. 10), case `(WP2)` skips external calls under a later modality `▷`, and case `(WP3)` existentially quantifies an angelic successor set `∃S` under `umrel` multirelations `p; s -↠ S`. To prove coinductive adequacy (`p; (call main [], ∅) -↠* {(n̂, h) | ϕ(n)}`), those angelic witnesses `S` must be extracted *outside* the logic. In ordinary `ω`-step-indexed Iris, an internal existential witness `S` may depend on the step-index `k`, while the program's execution length itself depends on `S`, creating an unbreakable circularity. Melocoton breaks this cycle by moving to **Transfinite Iris** (ordinal step-indices), proving that the angelic witnesses are step-index-independent.
4. **Opposite dual-nondeterminism polarity vs. DimSum:** Both frameworks use the signature `S → (S → Prop) → Prop`, but invert the meaning of outer vs. inner quantification (illustrated in the toy model [`Toy/EventLinking.lean`](lean/Toy/EventLinking.lean), `polarity_mismatch_breaks_refinement`; note that conjuncts 3–4 on `MeloRefines` hold by construction from flipping the relation, while conjuncts 5–6 on `MeloOneStepSafe` carry independent one-step WP content):
   - **DimSum:** outer transition = demonic (all must be simulated), inner set = angelic (pick one); no transition = `NB` (bottom, refines everything); transition to `∅` = `UB` (top, refined by everything).
   - **Melocoton `umrel`:** outer transition = angelic (WP picks one rule/set), inner set = demonic (WP covers all members); no transition = stuck/`UB` (fails WP); transition to `∅` = `NB` (vacuously satisfies any WP, including `False`, so Melocoton's language interface explicitly forbids it via `prim_step_no_NB` on non-values).

---

### 5. The Compositional CompCert Lineage: Shared-IR Interaction Semantics and Simulation Algebras

Basis: documentation (`compcomp.pdf` §§1, 3–5; `compcertm.pdf` §§1–3, 5; `compcerto.pdf` §§1–6).

All three extensions of CompCert compile open C (Clight) modules to assembly over CompCert's shared block-and-offset memory model, revealing a clear progression in solving the **open-simulation composition problem**:

#### 5.1 Compositional CompCert (Stewart et al., POPL 2015)

- **Core mechanism:** Introduces **interaction semantics** (split into internal steps plus `at_external`/`after_external` call/return boundaries) and **language-independent linking** `L` over a stack of active module cores sharing one CompCert memory.
- **Structured injections (`§4`):** To make vertical transitivity (`Theorem 1`) and horizontal composition (`Theorem 2`) go through simultaneously, Compositional CompCert replaces CompCert's three pass-specific memory relations (`id`, `ext`, `inj`) with a single **structured injection** `μ = (ownS, ownT, f_us, f_them)` partitioning every source and target block into five ownership classes `Priv | Pub | Frgn | Invis | None` (where `owned_i = {Priv, Pub}` and `shared_i = {Pub, Frgn}`), together with a **reach-closed restriction condition** (`μ|_X`, requiring `∼_μ` to be independent of `Invis`/`None` blocks for every pointer-reachability-closed superset `X ⊇ vis_μ`).
- **Observed bottlenecks (reported by CompCertM §1 and §3):**
  1. *Proof-engineering blowup:* Forcing every pass to maintain structured injections inflated compiler pass correctness proofs by **+145.77%** and metatheory by **+81.77%** over CompCert 2.1.
  2. *Assembly inadequacy:* Compositional CompCert's interaction semantics restricts assembly modules to C-like well-behaved calls and did not establish adequacy against unrestricted physical assembly linking (where assembly can clobber callee-save registers or dereference stale register pointers).

#### 5.2 CompCertM (Song et al., POPL 2020)

- **Diagnosing the open-simulation dilemma (§1):** In closed-program verification, a stronger memory relation (`id` or `ext`) implies a weaker one (`inj`). In open-module verification, that implication **fails**: a proof using `id` guarantees more about its own module's transitions *only by assuming more* (namely `id`-preservation) about unknown external contexts. Consequently, pass proofs verified under different memory relations cannot be vertically composed directly.
- **RUSC (`§2`, Theorem 2.1, Theorem 5.3, Corollary 5.4):** CompCertM solves this by defining **Refinement Under Self-related Contexts**: `p ≽_R q` holds iff for every context `C` that is self-related under *every* relation `r ∈ R`, `Beh(C[p]) ⊇ Beh(C[q])`. Taking `R` to be four open mixed forward-backward simulations (CompCert's `id`, `ext`, `inj`, plus a new memory injection with module-local private-memory invariants `(ι, m_src^prv, m_tgt^prv)` supporting register spilling alongside address-taken stack variables, §2.4), every pass keeps its natural CompCert relation, reducing proof overhead to **+18.73%** on pass proofs and **+32.59%** on metatheory (CompCert 3.5).
- **Exact three calling-convention violations that break physical adequacy (§3.3, Figs. 4–5):** CompCertM proves concrete counterexamples showing that standard C-to-assembly translations (CompCert, GCC, LLVM) are invalidated by linked handwritten assembly violating any of three assumptions:
  1. *Callee-save register preservation:* an invoked assembly function mutates `%rbx` across a call.
  2. *Non-info-passing register isolation:* an invoked assembly function dereferences a leftover pointer to a caller's non-escaped array still sitting in a register (e.g., `%rbx`) that was not part of the call's formal arguments.
  3. *Outgoing stack-arguments ownership:* the caller leaks `&arg` (via `%rsp`) into a global `leak` before calling `f(..., x)`, and a reentrant/nested callee `g()` invoked by `f` overwrites `*leak`, mutating `f`'s formal parameter `x` mid-execution (Fig. 5).
  CompCertM repairs interaction semantics by turning violations of these three assumptions into assembly-boundary **undefined behavior (UB)** (using nondeterministic initial-state injection + mixed simulations so every valid assembly module becomes self-related, proving two-way adequacy against physical Asm and C semantics, §5). Notably, CompCertM also discovers that **CompCert C** modules (unlike Clight) are **not always self-related under memory injections** because of a strict alignment rule on zero-sized blocks (§5, p. 23:21), restricting modular correctness (`Theorem 5.3`) to Clight.

#### 5.3 CompCertO (Koenig & Shao, PLDI 2021)

- **Simulation-convention algebra (`Defs. 2.1, 2.5, 2.6, 3.1–3.3, 3.6`):** CompCertO models an open transition system `L : A ↠ B` between incoming language interface `B = ⟨B^∘, B^•⟩` and outgoing interface `A = ⟨A^∘, A^•⟩`. A **simulation convention** `R : A_1 ⇔ A_2` is a triple `⟨W_R, R^∘, R^•⟩` of a Kripke world set `W_R` and world-indexed query/reply relations. Open simulations `L_1 ≤_{R_A ↠ R_B} L_2` compose:
  - *Vertically (`Theorem 3.7`):* via Kripke relation composition `R · S := ⟨W_R × W_S, R^∘ · S^∘, R^• · S^•⟩`.
  - *Horizontally (`Theorem 3.4` & `Theorem 3.5`):* `L_1 ⊕ L_2 ≤_{R ↠ R} L_1' ⊕ L_2'`, linking assembly via `Asm(p_1) ⊕ Asm(p_2) ≤_{id ↠ id} Asm(p_1 + p_2)`.
- **Why asymmetry breaks horizontal compositionality (§2.3, Table 3):** Several CompCert passes naturally have *asymmetric* simulation conventions—e.g., `SimplLocals` and `Cminorgen` satisfy `injp ↠ inj` (requiring stronger `injp` guarantees on outgoing calls than the `inj` guarantees they provide on incoming calls). Because horizontal composition (`Theorem 3.4`) feeds one module's outgoing call into the other module's incoming call, **asymmetry directly breaks horizontal linking**. CompCertO resolves this *outside* the pass proofs by inserting Clight self-simulations and algebraically rewriting the composite compiler convention into a single symmetric convention (`Theorem 3.8`, §5):
  `Clight(p) ≤_{C ↠ C} Asm(p')` where `C := R* · wt · CA · vainj_A`, `R := injp + inj + ext + vainj + vaext`, and `CA ≡ CL · LM · MA`.
  This keeps proof additions remarkably small (**+1,136 SLOC, +3%** over CompCert).
- **Structural boundaries of CompCertO:** As noted in CompCertO §3.5 and DimSum §6, `C` remains coupled to CompCert's shared memory model, horizontal linking hardwires well-bracketed LIFO calls, and CompCertO's open transition systems do not directly support persistent private state carried across top-level calls (motivating later direct-refinement extensions).

---

### 6. Cerise: Hardware Capability-Machine Logical Relations Against Arbitrary Unknown Assembly

Basis: documentation (`cerise_jacm.pdf` §§1–5, Theorems 1–2; `cerise_popl21.pdf` §§1, 4, 6, Figs. 11, 13, Theorems 6.1 and 6.3).

Cerise flips the trust boundary completely: instead of asking the foreign/unverified peer to obey a calling convention, memory injection, or interface specification, **unknown code is arbitrary untrusted machine instructions** executing in the same address space and invoked via an ordinary `jmp`.

1. **Unary Iris logical relation and FTLR (`cerise_jacm.pdf` §5, Theorems 1–2):**
   - Known code is verified with standard Iris separation-logic Hoare triples over concrete register/memory points-to predicates (`r ↦ w`, `a ↦ w`) and Iris invariants `I(mem)`.
   - A unary step-indexed logical relation defines `V(w)` ("word `w` is safe to share with unknown code"—e.g., an integer, or a capability whose accessible range holds invariants preserving `V`) and `E(pc)` ("executing from capability `pc` with safe registers preserves all invariants").
   - **Theorem 2 (FTLR):** `∀ p, b, e, a. V(p, b, e, a) → E(p, b, e, a)`. Proved by exhaustive case analysis over every machine instruction to verify that no instruction can amplify capability authority. Combined with **Theorem 1 (Adequacy)**—which requires, among its hypotheses (memory disjointness `prog ⊎ adv ⊆ mem`, initial invariant `I(mem)`, initial register setup, and the Iris safety proof), that the initial adversary region `[b_adv, e_adv)` contains no capabilities pointing outside `[b_adv, e_adv)`—known code can hand safe capabilities to arbitrary unknown assembly, jump to it, and know that every private Iris invariant `I(mem)` holds at every step.
2. **Sentry (`E`) capabilities for Local State Encapsulation (LSE):** A sentry ("enter") capability cannot be loaded from or stored through; jumping to it unseals it into an executable `RX` capability pointing to a fixed entrypoint (e.g., closure code + private environment pointer). Thus two mutually untrusting components can verify their private invariants independently, each treating the other as the adversary (`cerise_jacm.pdf` §5, p. 26).
3. **Uninitialized capabilities (`URW`/`URWL`/`URWLX`) and public/private worlds for Well-Bracketed Control Flow (WBCF) (`cerise_popl21.pdf` §§4, 6):**
   - Earlier local-capability calling conventions (Skorstengaard et al., ESOP '18) enforced WBCF and stack encapsulation by making stack/return pointers *local* (storable only through write-local capabilities) and clearing the entire unused stack (`mclear`) at every boundary crossing—a prohibitive `O(stack_size)` cost.
   - Georges et al. (POPL 2021) introduce **uninitialized capabilities** (`URW`, `URWL`, `URWLX`) whose cursor `a` splits `[b, e)` into a readable/writable initialized prefix `[b, a)` and a write-only uninitialized suffix `[a, e)` (`LoadU` requires `a' < a`; `StoreU` at offset 0 advances `a` by 1). Passing an uninitialized stack capability to a callee prevents it from reading stale prior frames without zero-clearing them.
   - To prove WBCF for reentrant callbacks (specifically the **awkward example** `let x = ref 0 in λf. (x := 0; f(); x := 1; f(); assert(!x = 1))` compiled to capability assembly with macro `scallU`, Fig. 13), Cerise's POPL 2021 model equips Iris worlds `W = (W^std, W^cus)` with **public future worlds** (`⊒_pub`, monotonically extending or promoting `Frozen → Temporary`) and **private future worlds** (`⊒_priv`, revoking temporary invariants on return). Permanent invariants (`permR`) must be monotone under `⊒_priv`, whereas temporary invariants (`tempR`) for write-local stack slots require monotonicity only under `⊒_pub` (Fig. 11). Custom STSs in `W^cus` encode the awkward closure's `0 → 1` protocol across callbacks, mechanically proving `assert(!x = 1)` against arbitrary adversarial machine code (`Theorem 6.1` FTLR, §6.8).

---

### 7. Exact Mechanisms Where Composition Breaks (Reentrancy, Well-Bracketedness, Shared Mutable State)

Basis (failure-mechanism and framework columns): documentation (all seven primary papers) + derived (comparative taxonomy).
Basis (toy-model column): source + execution (`[kernel-checked proof]` `[toy model]` in [`lean/`](lean/)).

| Stress Axis | Exact Failure Mechanism | How Each Framework Handles (or Breaks on) It | Toy-Model Theorem (`lean/`) |
| :--- | :--- | :--- | :--- |
| **1. Reentrancy** | **Half-updated private invariant exposed across outgoing call:** A module updates part of a coupled invariant (`x := x + 1`), invokes an external callback before finishing (`y := y + 1`), and the callback re-enters an exported entrypoint that observes `x ≠ y`. | **DimSum:** Wrapper/spec must re-establish relational invariant at every `Call!`. **Melocoton:** `Iris_ML`/`Iris_C` invariants must be closed before external calls; `ExecCallback` yields a fresh `GC(theta')`, invalidating all unrooted C addresses across reentrant calls. **CompCertM/O:** Requires invariants to hold at every external call; asymmetric pass conventions (`injp ↠ inj`) break mutual-recursion horizontal linking in CompCertO unless rectified by Clight self-simulations. **Cerise:** Iris invariants must be closed before `jmp` to unknown code; reentrant state transitions require `W^cus` STSs (`0 → 1` monotonic protocol). | `naive_sequential_preserves_inv` (passes without reentrancy) vs. `naive_reentrant_linking_breaks_invariant` (fails under reentrancy) vs. `framed_membrane_reentrant_sound` & `fixed_coupled_reentrant_safe` (sound for arbitrary callback depth) |
| **2. Call-stack well-bracketedness (WBCF)** | **Return-pointer replay / non-LIFO jump (Dreyer–Neis–Birkedal awkward attack):** Context calls `f` (`x := 0`), returns from first callback (`x := 1`, capturing continuation `k_2`), re-enters `f` (`x := 0`), and jumps directly to outer `k_2`, violating `assert(x == 1)`. | **CompCert lineage:** Hardwires LIFO call stack into interaction semantics / open LTS—so WBCF holds by assumption, but **coroutines, `setjmp`/`longjmp`, and foreign unwinding cannot be linked**. **Melocoton:** Hardwires LIFO call/callback stack; **exceptions/unwinding are unsupported**. **DimSum:** Decouples linking from LIFO—supports *intentional* non-WBCF via custom linker `⊕_coro`, while enforcing LIFO when using `⊕_r`. **Cerise:** Untrusted assembly can freely attempt return-pointer replay; WBCF is **enforced by hardware capabilities + calling convention** (`scallU` with local + uninitialized/directed capabilities). | `wbcf_awkward_safe` (LIFO stack preserves `failed = false` for all reachable states) vs. `non_wbcf_awkward_fails` (4-step non-bracketed replay reaches `failed = true`) |
| **3. Shared mutable state** | **(a) Aliasing / pointer escape into private frames:** Spilled register or outgoing stack-argument slot is mutated by foreign assembly via an escaped or leftover pointer.<br>**(b) Representation/GC divergence:** Two languages interpret the same memory differently or a moving GC relocates blocks.<br>**(c) Dual-nondeterminism polarity mismatch:** Connecting a DimSum transition system directly to a Melocoton `umrel` logic swaps `UB` and `NB`. | **(a)** Compositional CompCert uses 5-class ownership (`Priv`/`Pub`/`Frgn`/`Invis`/`None`) + reachability closure; CompCertM adds `(ι, m_src^prv, m_tgt^prv)` + turns the 3 assembly register/stack violations into UB; CompCertO encodes framing in `CA` + `injp`; Cerise isolates private frames via hardware capability bounds + `rclear`.<br>**(b)** Melocoton enforces exclusive single-view ownership via `ml_to_mut`/`mut_to_ml` + `GC(theta)`; DimSum uses a monotonically growing Kripke block-to-address map `w`.<br>**(c)** Polarity must be explicitly dualized at any boundary between refinement LTSs and WP `umrel`s. | `peer_only_preserves_private_frame` (framed rely protects `priv`), `link_horizontal_comp` (event linking horizontal soundness), `polarity_mismatch_breaks_refinement` (exact polarity inversion + vacuous `False` WP / stuck `NB` failure) |

---

### 8. Lean `v4.34.1` Toy-Model Mechanization (`[kernel-checked proof]` `[toy model]`)

Basis: source + execution (`lean/Toy/EventLinking.lean`, `lean/Toy/ReentrantMembrane.lean`, `lean/Toy.lean`, checked with Lean `v4.34.1`).

**Model–system relation: none proved.** The Lean files under [`lean/`](lean/) are minimal, Mathlib-free formal models constructed solely to machine-check the structural theorems and counterexamples above; they are not extracted from or proved equivalent to the Coq artifacts of DimSum, Melocoton, CompCertO, or Cerise.

| Module | Theorem (`[kernel-checked proof]` `[toy model]`) | Formal Statement Summary |
| :--- | :--- | :--- |
| `Toy.EventLinking` | `refines_refl`, `refines_trans` | Greatest-fixpoint dual-nondeterminism refinement `Refines` is a preorder (DimSum Lemma 3.1 analogue). |
| `Toy.EventLinking` | `link_horizontal_comp` | Turn-based event linking `linkMod route M1 M2` preserves `Refines` horizontally (`M1 ⪯ M1' ∧ M2 ⪯ M2' → link M1 M2 ⪯ link M1' M2'`). *Scope note:* `leftToRight` and `rightToLeft` transfer only the turn without delivering the event payload to the peer (dropping inter-module messages), so this is a weak turn-routing analogue of DimSum's `link_mod`. |
| `Toy.EventLinking` | `polarity_mismatch_breaks_refinement` | Under DimSum polarity `modNoStep ⪯ modEmptySet` and `¬(modEmptySet ⪯ modNoStep)`; under Melocoton `umrel` polarity `MeloRefines modEmptySet modNoStep` and `¬MeloRefines modNoStep modEmptySet`, `MeloOneStepSafe modEmptySet (fun _ => False)` holds vacuously, and `¬MeloOneStepSafe modNoStep (fun _ => True)`. *Scope note:* `MeloRefines M1 M2` is defined as `Refines M2 M1` with the relation flipped, so conjuncts 3–4 hold by construction as a restatement of conjuncts 1–2; only conjuncts 5–6 (`MeloOneStepSafe`) carry independent semantic content. |
| `Toy.ReentrantMembrane` | `naive_sequential_preserves_inv` | `naiveModule` (`x := x + 1; cb(); y := y + 1`) preserves `CoupledInv` (`x = y`) for any non-reentrant callback touching only `ext`. |
| `Toy.ReentrantMembrane` | `naive_reentrant_linking_breaks_invariant` | Linking `naiveModule` with reentrant callback `checkInv` breaks `CoupledInv` on the first reentrant call (`ok = false`). |
| `Toy.ReentrantMembrane` | `wbcf_step_preserves_inv`, `wbcf_reach_preserves_inv`, `wbcf_awkward_safe` | Single-step and multi-step preservation of `WbcfInv` under strict LIFO `WbcfStep`, yielding that every reachable state of the awkward example satisfies `failed = false`. |
| `Toy.ReentrantMembrane` | `non_wbcf_awkward_fails` | Under non-bracketed `NonWbcfStep` (permitting jump to any saved `afterSecondCall`), a 4-step trace reaches `failed = true`. |
| `Toy.ReentrantMembrane` | `framed_membrane_reentrant_sound`, `peer_only_preserves_private_frame`, `fixed_coupled_reentrant_safe` | Any module satisfying a `FramedMembrane` contract (restoring `Inv` before outgoing calls with disjoint `priv` framed off from `peerStep`) preserves `Inv` across arbitrary reentrant callback trees `PeerAction`, leaves `priv` untouched during peer-only execution, and fixes `CoupledInv`. |

## Boundaries

- **Model–system relation: none proved.** The Lean `v4.34.1` theorems in [`lean/`](lean/) are `[kernel-checked proof]` `[toy model]` mechanizations of simplified finite/inductive abstractions; they do **not** verify any compiler, FFI runtime, Coq artifact, or hardware ISA.
- **Not examined:**
  - The Coq proof scripts of DimSum, Compositional CompCert, CompCertM, CompCertO, and Cerise JACM 2024 (all claims about these five come from reading their published papers; only Melocoton's Coq statistics were previously checked in `semantic-multi-language-interop-dimsum-melocoton-and-linking-types` and POPL '21/OOPSLA '22 Cerise Coq hole counts in `mswasm-...`).
  - Full texts of CompCertOC (Zhang et al., POPL 2024, `10.1145/3632914`), Koenig & Shao LICS 2020 (`10.1145/3373718.3394799`), StkTokens (POPL 2019), and *Le temps des cerises* (OOPSLA1 2022) — cited strictly for verified lineage coordinates.
  - Concurrent or weak-memory extensions (e.g., multicore OCaml 5 FFI, concurrent CompCert variants, or CHERI multicore memory models).
- **Unknown:**
  - Whether DimSum's stateful-wrapper refinement approach scales without ergonomic friction to a full C/Rust/OCaml FFI with a moving generational GC and exceptions.
  - Whether CompCertO's simulation-convention algebra can be lifted cleanly to heterogeneous memory models (CompCertO §3.5 sketches embedding into richer game models as future work; DimSum §6 notes it has not been demonstrated).
  - Whether Cerise's capability-machine logical relations can be composed directly with an optimizing multi-pass C/Rust compiler (as opposed to hand-verified assembly components and toy compilers).
- **Known not to apply:**
  - **Concurrency and liveness:** All four primary frameworks are sequential and safety-only (DimSum §7, Melocoton §6, CompCertO §3.5, Cerise JACM §1). None proves termination, progress under fairness, or data-race freedom across threads.
  - **Exceptions and unwinding across FFI:** Neither Melocoton nor the Compositional CompCert / CompCertM / CompCertO lineage models C++/`extern "C-unwind"` stack unwinding or OCaml exceptions crossing the FFI boundary.
  - **Zero-trust against adversarial assembly in CompCertM/CompCertO:** Unlike Cerise, CompCertM and CompCertO do **not** protect compiled C modules against arbitrary malicious assembly; they assume linked assembly obeys the calling-convention contract (or treat violations as assembly-side UB).
  - **CompCert C under CompCertM modular correctness:** CompCertM §5 explicitly establishes that CompCert C modules are not always self-related under memory injections due to zero-size block alignment; `Theorem 5.3` applies to Clight, not CompCert C.
- **Unsupported (explicitly out of scope in the primary sources):**
  - DimSum (`Rec`/`Asm`): closures, garbage collection, static types, concurrency, and liveness.
  - Melocoton (`λ_ML`/`λ_C`): OCaml exceptions, threads/multicore domains, direct pointer access into OCaml block fields, custom-block comparison/finalization hooks, and verification of the GC implementation itself.
  - Cerise (JACM '24): local/uninitialized/directed capabilities are omitted from the core JACM '24 presentation (which focuses on sentry capabilities and LSE) and live in the POPL '21 / OOPSLA '22 extensions.
- **Attractive stronger conclusions NOT established:**
  - Horizontal compositionality of an event-based linker (`link_horizontal_comp`) does **not** automatically grant local-state framing or memory safety; framing still requires an explicit wrapper/membrane invariant or hardware isolation.
  - Proving a module safe under well-bracketed call/return semantics (CompCertO/M or Melocoton) does **not** establish safety when linked with low-level code capable of `longjmp`, continuations, coroutines, or raw return-pointer manipulation unless WBCF is separately enforced (e.g., via Cerise-style capabilities).

## Evidence

All primary-source evidence and Lean kernel checks were acquired on **2026-11-22**.

### Primary Papers and Metadata Verification

1. **Crossref REST metadata (`https://api.crossref.org/works/<DOI>`), queried 2026-11-22:** Confirmed exact titles, full author lists, containers, volumes/issues, page ranges, and publication dates for `10.1145/3571220` (DimSum), `10.1145/3622823` (Melocoton), `10.1145/2676726.2676985` (Compositional CompCert), `10.1145/3371091` (CompCertM), `10.1145/3453483.3454097` (CompCertO), `10.1145/3373718.3394799` (Koenig & Shao LICS '20), `10.1145/3434287` (Georges et al. POPL '21), `10.1145/3623510` (Cerise JACM '24), `10.1145/3290332` (StkTokens), `10.1145/3527318` (*Le temps des cerises*), `10.1007/978-3-319-89884-1_17` (Skorstengaard et al. ESOP '18), and `10.1145/3363519` (TOPLAS '19).
2. **Primary-source PDFs downloaded and inspected on 2026-11-22:**
   - DimSum: `https://iris-project.org/pdfs/2023-popl-dimsum.pdf` (2,690 extracted text lines; §§2–6, Figs. 5, 14–15, Lemma 3.1, Thms. 3.2 & 5.1).
   - Melocoton: `https://iris-project.org/pdfs/2023-oopsla-melocoton.pdf` (1,797 extracted text lines; §§2–4, Figs. 8–10, Thms. 4.1 & 4.2).
   - Compositional CompCert: `https://www.cs.princeton.edu/~appel/papers/compcomp.pdf` (1,824 extracted text lines; §§1, 3–5, structured injections & Thms. 1–2).
   - CompCertM: `https://sf.snu.ac.kr/publications/compcertm.pdf` (2,046 extracted text lines; §§1–3, 5, Figs. 4–5, RUSC Thms. 2.1 & 5.3, Cor. 5.4, SLOC overhead numbers).
   - CompCertO: `http://flint.cs.yale.edu/flint/publications/compcerto.pdf` (2,186 extracted text lines; §§1–6, Defs. 2.1, 2.5–2.6, 3.1–3.3, 3.6, Thms. 3.4–3.5, 3.7–3.8, Cor. 3.9, Table 3 SLOC).
   - Cerise (JACM '24): `https://iris-project.org/pdfs/2023-jacm-cerise.pdf` (4,926 extracted text lines; §§1–5, Thms. 1–2).
   - Cerise (POPL '21): `https://iris-project.org/pdfs/2021-popl-ucaps-final.pdf` (1,959 extracted text lines; §§1, 4, 6, Figs. 11 & 13, Thms. 6.1 & 6.3).

### Lean `v4.34.1` Kernel Audit (`[kernel-checked proof]` `[toy model]`)

Package files preserved under [`lean/`](lean/):
- [`lean/lean-toolchain`](lean/lean-toolchain) (`leanprover/lean4:v4.34.1`)
- [`lean/lakefile.toml`](lean/lakefile.toml) (Mathlib-free, `defaultTargets = ["Toy"]`)
- [`lean/Toy/EventLinking.lean`](lean/Toy/EventLinking.lean)
- [`lean/Toy/ReentrantMembrane.lean`](lean/Toy/ReentrantMembrane.lean)
- [`lean/Toy.lean`](lean/Toy.lean)

Exact `#print axioms` output for all 13 hand-written theorems captured after `lake build && lake env lean Toy.lean` (exit code `0`, 0 errors, 0 warnings, 0 `sorryAx`, standard Lean axiom subset `⊆ {propext}` only):

```text
'EventLinking.refines_refl' does not depend on any axioms
'EventLinking.refines_trans' does not depend on any axioms
'EventLinking.link_horizontal_comp' does not depend on any axioms
'EventLinking.polarity_mismatch_breaks_refinement' does not depend on any axioms
'ReentrantMembrane.naive_sequential_preserves_inv' depends on axioms: [propext]
'ReentrantMembrane.naive_reentrant_linking_breaks_invariant' does not depend on any axioms
'ReentrantMembrane.wbcf_step_preserves_inv' depends on axioms: [propext]
'ReentrantMembrane.wbcf_reach_preserves_inv' depends on axioms: [propext]
'ReentrantMembrane.wbcf_awkward_safe' depends on axioms: [propext]
'ReentrantMembrane.non_wbcf_awkward_fails' depends on axioms: [propext]
'ReentrantMembrane.framed_membrane_reentrant_sound' does not depend on any axioms
'ReentrantMembrane.peer_only_preserves_private_frame' does not depend on any axioms
'ReentrantMembrane.fixed_coupled_reentrant_safe' does not depend on any axioms
```

## Revalidation

1. **Rebuild and axiom-check the Lean `v4.34.1` toy model** (copy `lean/` to a clean temporary directory so `.lake/` build artifacts are not left in the corpus tree):
   ```bash
   TMPDIR=$(mktemp -d)
   cp -R lean/. "$TMPDIR/"
   (cd "$TMPDIR" && lake build && lake env lean Toy.lean)
   rm -rf "$TMPDIR"
   ```
   Expected result: exit code `0`, zero warnings/errors, zero `sorryAx`, and every theorem in `Toy.lean` reports either zero axioms or only a subset of `{propext, Classical.choice, Quot.sound}`.
2. **Verify DOI metadata stability:** Query `https://api.crossref.org/works/<DOI>` for each of the seven primary DOIs in `REPORT.json` and confirm titles, authors, and venues remain unchanged.
3. **Revalidate scope boundaries against newer papers:** If a future revision of DimSum, Melocoton, CompCertO (e.g., CompCertOC or concurrent variants), or Cerise adds shared-memory concurrency, exceptions/unwinding across FFI, or verified compiler integration on capability machines, inspect the new paper's top-level adequacy/compositionality theorem and compare its assumptions against the failure taxonomy in Finding 7 and `## Boundaries`.
