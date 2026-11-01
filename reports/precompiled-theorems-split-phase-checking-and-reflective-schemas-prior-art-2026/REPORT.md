# Pre-Compiled Theorem Interfaces, Split-Phase Proof Checking, and Reflective Schema Acceleration Across Interactive Theorem Provers

## Summary

Minimally trusted program verification pipelines such as Anneal restrict their
Trusted Computing Base (`trusted/`) to primitive operational semantics,
behavioral refinement relations, and top-level theorem gates
(`Trusted.CrateTheorem` and `VerificationResult` in `trusted/lean/`), while
placing derived program-logic lemmas, symbolic evaluators, and decision
procedures in an untrusted proof library (`theory/Anneal/`). Without explicit
architectural separation between build-time theory checking and per-crate
runtime checking, two distinct kernel bottlenecks arise at verification runtime:

1. **Stage-1 Theory Re-Verification Bottleneck in Kernel Boundary Auditing:**
   In `joshlf/anneal@76fad1a1befa2e4c038d88c3a1bbbe873acb1322`,
   `trusted/audit/src/lib.rs` (`build_prefix_cache` at lines 1676–1733 and
   `load_or_build_verify_prefix` at lines 1735–1930) caches compiled `.olean`
   and `.ir` artifacts for `Trusted.*` and `Anneal.*` so Phase 1 elaboration
   compiles only the target crate's `Mir.lean` and `Proof.lean`. However, Phase
   2 boundary auditing (`trusted/audit/TrustedBoundary.lean`,
   `verifyAndCollectLocals` at lines 832–873 and `audit` at lines 900–973)
   imports only `foundation` (`Init.*`) into `base`, collects every declaration
   across `trusted ++ theory ++ #[Mir, Proof]` into `locals`, and executes
   `base.toKernelEnv.replay locals` (line 972). Consequently, every proof term
   in `theory/Anneal/` is re-checked in the Lean 4 kernel from scratch on every
   `cargo anneal verify` invocation.
2. **Stage-2 Per-Program Certificate Spine and Kernel Conversion Bottleneck:**
   Even when `theory/Anneal/` is not replayed at crate verification time,
   `Proof.lean` must construct a kernel-checked proof of
   `Trusted.CrateTheorem Mir.crate`. When `Proof.lean` steps through concrete
   instructions via nested tactical applications of single-step lemmas (such as
   `reachesPrefix_safeAndEnsures_of_step` in `theory/Anneal/MirLemmas.lean`,
   lines 3510–3565) or updates multi-field program state structures via nested
   `{ s with ... }` projections, both the proof-term spine size and the kernel
   definitional-equality (`is_def_eq` / `whnf`) cost grow superlinearly with
   instruction count and local context size.

Across six major interactive theorem prover (ITP) prior-art families—Coq/Rocq
(`.vos`/`.vok` separate interface compilation, `OpaqueDef`, `Strategy opaque`,
and VST-Floyd), Iris/Diaframe/RefinedC/RefinedRust (`Lithium` goal-directed
typeclass search over pre-proved `Subsume`/`SimplifyHyp`/`SimplifyGoal`
schemas), HOL4/HOL Light/Candle (`TheoryReader`/`disk_thm`, Myreen's
`cv_compute`/`cv_trans`, and `awslabs/s2n-bignum`), Isabelle/HOL (stacked
session heap images, `AutoCorres`/`AutoCorres2` 5-phase schematic refinement,
and `Isabelle_LLVM` `Sepref`), Metamath Zero (`.mmb` `STMT_THM`/`CMD_PROOF_THM`
header authority) and Dedukti/Lambdapi/Alethe/LRAT, and Gonthier–Mahboubi
SSReflect small-scale reflection with Malecha et al.'s `MirrorCore` `RTac`—all
scalable systems resolve these two bottlenecks through **two orthogonal,
complementary mechanisms** that preserve a zero-growth TCB:

- **Mechanism I (Split-Phase Environment Sealing and Theorem Header Authority):**
  Verify `trusted/lean/` and `theory/Anneal/` once against `foundation` during
  Stage-1 pre-auditing, hash-lock the audited `.olean` closure, and load
  `foundation ++ trusted ++ theory` directly as the imported `base` environment
  during Stage-2 per-crate verification so `base.toKernelEnv.replay` checks only
  `#[Mir, Proof]`. Because Lean 4's C++ kernel (`leanprover/lean4` `v4.34.1`,
  `src/kernel/environment.cpp:192-209` and `src/kernel/type_checker.cpp`) stores
  `Declaration.thmDecl` as `ConstantInfo.thmInfo` and never unfolds a theorem's
  `.value` proof term during `is_def_eq` or `whnf`, importing pre-audited
  `theory/Anneal/` theorems into `base` (or compacting their `.olean`
  entries to `.axiomInfo` stubs of identical `.name`, `.levelParams`, and
  `.type`) is mechanically isomorphic to Metamath Zero's `.mmb` theorem header
  table (`CMD_PROOF_THM`), Rocq's `.vos`/`OpaqueDef` delayed proof handles,
  HOL4's `TheoryReader` (`disk_thm`), and Isabelle's stacked session heaps
  (`isabelle build -b`)—with zero new axioms in `trusted/lean/`. In our
  companion report
  [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md),
  this single-import two-stage boundary auditor reduces Phase-2 `"audit"`
  latency on Anneal's prefix from `2,013.5 ms` to `79.3 ms` (`25.4x` speedup)
  while cutting `FunctionalTranslation.olean` disk size by `64.0%` (`13.94 MB`
  to `5.02 MB`).
- **Mechanism II (Reflective and Schematic Acceleration of Per-Crate Proofs):**
  Replace per-instruction proof-term spines in `Proof.lean` by combining (a)
  **computational reflection** (`evalCvProg_sound`, `evalIdiomPlan_sound`,
  `wpX86_sound_steps`, and `checkSideConds_sound` discharged via `Eq.refl true`
  using Lean 4's C++ GMP `Nat` fast path `reduce_nat` in
  `src/kernel/type_checker.cpp:101-372`, analogous to HOL4's `cv_compute` and
  SSReflect's `elimT`) with (b) **canonical-form schematic theorems and
  partial reflective VC generation** in `theory/Anneal/` (analogous to VST's
  `semax_load_37` under `Opaque semax`, Lithium's `Subsume` schemas,
  `AutoCorres`'s `ac_corres_chain`, and `MirrorCore` `RTac`'s `Result.More_ s'
  g'` residual obligation emission into `VerificationResult`). In our companion
  report
  [`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md),
  combining Mechanism I and Mechanism II across a 10-function `zerocopy`-style
  crate reduces end-to-end elaboration time by `23.04x` (`18,750.3 ms` to
  `813.8 ms`), reduces Stage-2 kernel replay time by `32.11x` (`5,042.587 ms`
  to `157.056 ms`, or `3,001.54x` to `1.680 ms` with per-function `ShardCert`
  incremental sharding), and shrinks unfolded proof-tree size by `995.31x`
  (`51,614,627` to `51,858` nodes).

## Applicability

This report synthesizes comparative architectural evidence across six interactive
theorem prover families and connects those mechanisms to Lean `v4.34.1` and
Anneal. The findings apply to the following exact pinned repositories,
revisions, and publications identified in `REPORT.json`:

1. **Anneal (`joshlf/anneal`):**
   - `main` at `76fad1a1befa2e4c038d88c3a1bbbe873acb1322`:
     `trusted/audit/src/lib.rs` (lines 1–1961),
     `trusted/audit/TrustedBoundary.lean` (lines 1–1014),
     `trusted/lean/foundation-lock.json`, and `PRINCIPLES.md`.
   - `trusted-core` branch at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
     `trusted/lean/Trusted/Refinement.lean` (lines 1–490) and
     `trusted/lean/Trusted/StepResult.lean` (lines 1–331).
   - `mir-to-x86` branch at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`:
     `theory/Anneal/MirSemantics.lean` (lines 1–1458),
     `theory/Anneal/MirLemmas.lean` (lines 1–3590),
     `theory/Anneal/AsmX86.lean` (lines 1–1713), and
     `theory/Anneal/MirToX86.lean` (lines 1–1482).
2. **Lean 4 (`leanprover/lean4`):**
   - Commit `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):
     `src/kernel/environment.cpp` (lines 192–209),
     `src/kernel/type_checker.cpp` (lines 101–372), and
     `src/Lean/Elab/Tactic/BVDecide/`.
3. **Coq / Rocq and VST:**
   - `rocq-prover/rocq@0b9568e12875891c1b9463fa3548f36384ea6f99`:
     `kernel/declarations.mli` (lines 53–85),
     `kernel/opaqueproof.mli` (lines 14–50),
     `kernel/constant_typing.ml` (lines 212–291),
     `kernel/conv_oracle.mli` (lines 14–60), and
     `theories/Corelib/ssr/ssrbool.v` (lines 18–30, 657–724).
   - `PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`:
     `floyd/sc_set_load_store.v` (lines 222–350) and
     `floyd/call_lemmas.v` (lines 37–1658).
   - Cao et al., *VST-Floyd: A Separation Logic Tool to Verify Correctness of C
     Programs*, JAR 61(1–4), 2018, DOI `10.1007/s10817-018-9457-5`.
4. **Iris, Diaframe, RefinedC, and RefinedRust:**
   - `iris/refinedc@2e89846baeaa7f65cbe17e3ae7297a8ed5b4feca` and
     `d057583986651a28047164581f05fbee3a83ed9d`:
     `theories/lithium/definitions.v` (lines 19–332),
     `theories/lithium/interpreter.v` (lines 19–196),
     `theories/typing/type.v` (lines 14–108), and
     `theories/typing/adequacy.v` (lines 15–51); Sammler et al., PLDI 2021, DOI
     `10.1145/3453483.3454036`.
   - `lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52` and
     RefinedRust PLDI 2024 artifact (Zenodo `21636474`, `theories/typing/programs.v`,
     `theories/typing/function.v`, `theories/radium/interp.v`); Gäher et al.,
     PLDI 2024, DOI `10.1145/3656422`.
   - Mulder et al., *Diaframe*, PLDI 2022, DOI `10.1145/3519939.3523432`.
   - `rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088` and
     `leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`.
5. **HOL4, HOL Light, Candle, and `awslabs/s2n-bignum`:**
   - `HOL-Theorem-Prover/HOL@68c9d77e53532cb258e09421952efe3957f40276`:
     `src/postkernel/TheoryReader.sml` (lines 18–138),
     `src/thm/std-thm.ML` (lines 1115–1135, 1476–1558),
     `src/thm/Compute.sml` (lines 1–90), and
     `src/num/theories/cv_compute/cv_computeLib.sml` (lines 1–90).
   - Myreen, ITP 2021, DOI `10.4230/LIPIcs.ITP.2021.27`; Abrahamsson et al.,
     ITP 2022, DOI `10.4230/LIPIcs.ITP.2022.3`; Gómez-Londoño and Myreen, ITP
     2023, DOI `10.4230/LIPIcs.ITP.2023.17`.
   - `jrh13/hol-light@233b83c3202370e03c54de2bd090e4d34f677e91` (`fusion.ml`
     lines 320–569) and `b19af6934759eed622d7aca25092367f81656eee`.
   - `awslabs/s2n-bignum@9f2cd960e11892a582e7facb0c191b4a2959ea91` and
     `4d1356a7470663c752660a59375dc3a9ef548428`:
     `common/execution.ml` (lines 1254–1805),
     `arm/proofs/instruction.ml` (lines 727–745), and
     `x86/proofs/bignum_add.ml` (lines 51–164).
6. **Isabelle/HOL, `AutoCorres`, and `Isabelle_LLVM`:**
   - `seL4/l4v@12c300e75bb0ca0c82f76496fafacd7e614c0aba`:
     `tools/autocorres/AutoCorres.thy` (lines 11–90) and
     `tools/autocorres/autocorres.ML`; Greenaway et al., PLDI 2014, DOI
     `10.1145/2594291.2594296`.
   - `lammich/isabelle_llvm@6be37a9c3cae74a1134dbef2979e312abb5f7f42`; Lammich,
     ITP 2015, DOI `10.1007/978-3-319-22102-1_17`, and ITP 2019, DOI
     `10.4230/LIPIcs.ITP.2019.21`.
7. **Metamath Zero (`MM0`) and Dedukti / Lambdapi / Alethe / LRAT:**
   - `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`:
     `mm0-c/mmb.md` (lines 34–462),
     `mm0-c/verifier.c` (lines 213–809), and
     `examples/separation_logic.mm1`; Carneiro, CPP 2020, DOI
     `10.1145/3372885.3373824`.
   - `Deducteam/Dedukti@f3c0eba869ddd46f2e75c123a59f2b612076dba0`
     (`kernel/typing.ml:105-410`, `kernel/confluence.ml:23-213`) and
     `Deducteam/lambdapi@72cc2f10d391932fe078ba5a401765e29a1d4cb7`
     (`src/handle/command.ml:228-284`).
8. **SSReflect and `MirrorCore` / `RTac`:**
   - Gonthier and Mahboubi, JFR 3(2), 2010, DOI `10.6092/issn.1972-5787/1979`
     (and JAR 2010, DOI `10.1007/s10817-010-9183-1`).
   - `gmalecha/mirror-core@b962fbca15b0b5a4653f66d29d7115bb04ebd4f3`:
     `theories/RTac/Core.v` (lines 62–110, 196–200, 402–535); Malecha,
     Chlipala, and Braibant, ITP 2014, DOI `10.1007/978-3-319-08970-6_24` (and
     ESOP 2016, DOI `10.1007/978-3-662-49498-1_19`).

These subjects are related through a comparative design synthesis: the six
upstream ITP families establish the soundness invariants and engineering
tradeoffs of split-phase theorem persistence and reflective/schematic proof
compression, while the Lean `v4.34.1` and Anneal subjects establish how those
mechanisms map onto Lean's `.olean` format, `Kernel.Environment.replay`, and
Anneal's `trusted/` vs. `theory/` boundary. Concrete Lean `v4.34.1` execution
benchmarks and adversarial security tests for the resulting Anneal designs are
preserved in the companion packages
[`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md)
and
[`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md).

## Findings

### Finding 1: Diagnosis of Dual Runtime Bottlenecks in Minimally Trusted Proof-Carrying Verification Pipelines (Stage-1 Theory Re-Verification vs. Stage-2 Per-Program Certificate Spine & Conversion Cost)

`Basis: normative + source + derived`

In `joshlf/anneal@76fad1a1befa2e4c038d88c3a1bbbe873acb1322`, `cargo anneal
verify` executes two sequential phases across four module roots: `Trusted`
(`trusted/lean/`), `Anneal` (`theory/`), `Mir` (`.anneal/Mir.lean`), and
`Proof` (`.anneal/Proof.lean`).

1. **Phase 1 Elaboration (`trusted/audit/src/lib.rs:1460-1950`):**
   - `verify_crate_roots` (lines 1460–1590) manages `.olean` compilation for all
     four roots.
   - When `VERIFY_PREFIX_CACHE` (or `prefix_cache_dir`) is enabled,
     `load_or_build_verify_prefix` (lines 1735–1930) computes a SHA-256 cache
     key (`compute_verify_prefix_cache_key`, lines 1630–1674) over the Lean
     toolchain binary, `foundation-lock.json`, and all `.lean` source files in
     `trusted/lean/` and `theory/`. On a cache hit, it copies the pre-compiled
     `.olean` and `.ir` files for `Trusted.*` and `Anneal.*` into the verification
     working directory and runs `compile_lean_module` (`lean -o ... -i ...`)
     **only** on `Mir.lean` and `Proof.lean` (lines 1510–1538), reusing the
     cached prefix's syntax preflight record (`prefix-preflight.json`, lines
     1711–1718).
2. **Phase 2 Kernel Boundary Audit (`trusted/audit/TrustedBoundary.lean:832-975`):**
   - After `Proof.olean` is produced, `verify_crate_roots` invokes
     `anneal-boundary-audit audit` (lines 1549–1586).
   - Inside `TrustedBoundary.lean`, `audit` (lines 900–973) partitions module
     names into `foundation` (`Init.*` locked by `foundation-lock.json`),
     `trusted` (`Trusted.*`), `theory` (`Anneal.*`), `Mir`, and `Proof`.
   - Lines 947–948 import the `foundation`-only environment (`let base ←
     importEnv j foundation`) and the full environment (`let full ← importEnv j
     fullNames`).
   - Line 949 calls `verifyAndCollectLocals base full (trusted ++ theory ++
     #[Mir, Proof])`, which iterates over **every constant in `trusted`,
     `theory`, `Mir`, and `Proof`** (lines 843–871), verifying expression DAG
     edges (`exprEdges`, lines 480–516) and inserting each constant into
     `locals : Std.HashMap Name ConstantInfo`.
   - Line 972 then executes:
     ```lean
     let _ ← base.toKernelEnv.replay locals
     ```
     Because `base` contains only `foundation` (`Init.*`), `replay` re-checks
     every definition and theorem in `trusted/lean/` and `theory/Anneal/` inside
     the Lean 4 kernel on every crate verification run.
3. **Proof-Term Spine vs. Verified Symbolic/WP Evaluation in `theory/Anneal/`
   (`mir-to-x86@4f45f0a391a921ced9c9dc773b9a040dbc215d14`):**
   - `theory/Anneal/` contains two contrasting proof architectures:
     - **Step-by-step tactical chaining (`MirLemmas.lean:3510-3565`):**
       `reachesPrefix_safeAndEnsures_of_step` chains single-step operational
       lemmas across basic blocks, constructing explicit proof subterms and
       continuation lambdas at every step.
     - **Verified symbolic/WP evaluation (`MirToX86.lean:369-1482` and
       `AsmX86.lean:1553-1713`):** `evalSymInst`, `evalSymBlock`, and `wpX86`
       compute symbolic post-states and weakest preconditions in `theory/Anneal/`,
       paired with once-and-for-all soundness theorems (`evalSymBlock_sound`,
       `wpX86_sound_steps`, `compiles_mir_x86_of_symEq`).

This baseline establishes why neither mechanism suffices alone:
- Caching `.olean` files for `theory/Anneal/` eliminates Phase 1 elaboration of
  `theory/`, but leaves Phase 2 kernel replay (`base.toKernelEnv.replay locals`)
  to re-verify every proof in `theory/Anneal/` unless pre-audited `trusted` and
  `theory` modules are moved from `locals` into `base` (**Mechanism I**).
- Moving `theory/Anneal/` into `base` eliminates Stage-1 theory replay at crate
  verification time, but leaves `Proof.lean` slow if `Proof.lean` still builds
  deep per-instruction proof-term spines or unfolds underlying operational
  definitions (`EventualBehaviorOf`, `ReachesPrefix`, or nested record
  projections) during kernel conversion (**Mechanism II**).

---

### Finding 2: Coq / Rocq Separate Interface Compilation (`-vos`/`-vok` vs. `-vo`), `Qed` Opacity (`OpaqueDef` in `kernel/declarations.mli` and `kernel/opaqueproof.mli`), `Strategy opaque`, and VST (`PrincetonUniversity/VST`) `Opaque semax` + Canonical `PTree` Forward Symbolic Execution Rules

`Basis: documentation + source + derived`

#### Primary-Source Coordinates and Citations

- **Repository (`rocq-prover/rocq`):** Commit
  `0b9568e12875891c1b9463fa3548f36384ea6f99`:
  - `kernel/declarations.mli` (lines 53–59): Defines
    `type ('a, 'opaque, 'rules) constant_def = Undef of inline | Def of 'a |
    OpaqueDef of 'opaque | Primitive of CPrimitives.t | Symbol of 'rules`.
  - `kernel/opaqueproof.mli` (lines 14–50): Defines `opaquetab`, `opaque`, and
    `opaque_handle`, storing `Qed` proof terms in an indirect table serialized
    in an optionally loaded segment of `.vo` files.
  - `kernel/constant_typing.ml` (lines 212–291): Defines `infer_definition`
    (lines 212–233), `infer_opaque` (lines 262–284, returning `OpaqueDef` paired
    with a `cooking_info` delayed check token), and `check_delayed` (lines
    286–291, which forces the proof term and checks `Subtyping.check_voiced`
    against the statement's type).
  - `kernel/conv_oracle.mli` (lines 14–60): Defines the conversion unfolding
    oracle `type level = Expand | Level of int | Opaque` controlled by the
    vernacular commands `Strategy opaque [c]` and `Opaque c`.
- **Repository (`PrincetonUniversity/VST`):** Commit
  `3c37c2e2b574e23aee8fdd1684aa0ffed227491e`:
  - `floyd/sc_set_load_store.v` (lines 222–350): Pre-proved canonical-form
    symbolic execution lemmas `semax_load_37`, `semax_cast_load_37`, and
    `semax_store_nth`.
  - `floyd/call_lemmas.v` (lines 37–97, 941–1658): Pre-proved function-call
    schemas `semax_call'`, `semax_call_aux55`, and
    `semax_call_id00_wow`..`semax_call_id01_wow_nil`.
- **Publications:**
  - Appel et al., *Program Logics for Certified Compilers*, Cambridge University
    Press, 2014.
  - Cao, Beringer, Gruetter, Dodds, and Appel, *VST-Floyd: A Separation Logic
    Tool to Verify Correctness of C Programs*, Journal of Automated Reasoning
    61(1–4), pp. 367–422, 2018, DOI `10.1007/s10817-018-9457-5`.

#### Technical Mechanism and Architectural Analysis

1. **Kernel Opacity (`OpaqueDef` vs. `Def`) and Separate `.vos` / `.vok`
   Checking:**
   In Rocq's kernel (`kernel/declarations.mli:53-59`), a transparent definition
   (`Defined` / `Def`) stores its body inline so the conversion test
   (`Reduction.conv`) can delta-unfold it when checking downstream modules. By
   contrast, a theorem closed with `Qed` is typed by
   `Constant_typing.infer_opaque` (`kernel/constant_typing.ml:262-284`) as an
   `OpaqueDef (opaque : Opaqueproof.opaque)`. Because `OpaqueDef` is never
   unfolded during definitional equality (under `Prop` non-computational
   elimination restrictions), downstream modules depend **only** on the
   theorem's statement `const_type` (and universe constraints when polymorphic),
   never on its proof term.
   - Under `-vos` (omitting opaque proofs), `rocq compile -vos` elaborates
     theorem statements and transparent definitions, writing `.vos` interface
     files with empty `opaquetab` entries.
   - Downstream modules compile against `.vos` files without loading upstream
     opaque proof bodies. In parallel or in CI, `rocq compile -vok` runs
     `Constant_typing.check_delayed` (`kernel/constant_typing.ml:286-291`) to
     verify each `OpaqueDef` proof term against its declared `const_type`,
     emitting an empty `.vok` certificate file.
2. **Controlling Conversion Blowup via `Strategy opaque` and Canonical-Form
   Lemmas in VST (`VST-Floyd`):**
   In VST (`PrincetonUniversity/VST`), the Hoare triple judgment
   `semax Espec Delta P c Q` is defined in `veric/semax.v` as a step-indexed,
   higher-order separation-logic predicate over CompCert `Clight` operational
   semantics. Unfolding `semax` during a per-function C verification script
   would force Rocq's kernel to reduce step-indexed `rmap` approximations on
   every C statement. VST eliminates this bottleneck through three mechanisms:
   - **Global Opacity of the Semantic Judgment:** Once the structural rules of
     `semax` (`semax_seq`, `semax_ifthenelse`, `semax_loop`, `semax_load`,
     `semax_store`, `semax_call`) are proved in `veric/` and `floyd/` and sealed
     with `Qed`, `semax` is marked `Global Opaque semax` (mapping to
     `Conv_oracle.Opaque` in `kernel/conv_oracle.mli:44`). Neither tactics nor
     kernel conversion unfold `semax` during user C proofs.
   - **Canonical Representation (`PROPx P (LOCALx Q (SEPx R))`) and Finite-Map
     Lookup (`PTree`):** Instead of running general associative-commutative
     separation-logic search on every load and store, VST-Floyd maintains
     assertions in canonical form `PROPx P (LOCALx Q (SEPx R))` and converts the
     local variable list `Q` into a binary Patricia tree `PTree.t val`
     (`local2ptree Q = (Qtemp, Qvar, nil, GV)` in `floyd/call_lemmas.v:951`).
   - **Pre-Proved Computational Premise Lemmas (`semax_load_37`,
     `semax_store_nth`, `semax_call_id01_wow`):** In
     `floyd/sc_set_load_store.v:222-350` and `floyd/call_lemmas.v:941-1658`,
     VST pre-proves single-step symbolic execution lemmas whose premises are
     computational equations (`nth_error R n = Some ...`, `local2ptree Q = ...`,
     `force_list (map (msubst_eval_expr Delta Qtemp Qvar GV) ...) = Some vl`).
     At C verification time, the `forward` tactic computes node indices $n$ and
     discharges those premises by `reflexivity` (`rfl`), producing a flat
     single-lemma application per C statement.

#### Correspondence to Lean `v4.34.1` and Anneal

- **Lean 4 Kernel Equivalence of `OpaqueDef` (`ConstantInfo.thmInfo`):**
  In Lean 4's C++ kernel (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  `src/kernel/environment.cpp:192-209` and `src/kernel/type_checker.cpp`), every
  `theorem` declaration (`Declaration.thmDecl`) is stored as
  `ConstantInfo.thmInfo` in `Prop`. During definitional equality (`is_def_eq`)
  and weak-head normal form reduction (`whnf_core`), the Lean 4 kernel unfolds
  `ConstantInfo.defnInfo` (`def`), **never** `ConstantInfo.thmInfo` (`theorem`)
  or `ConstantInfo.opaqueInfo` (`opaque`). Furthermore, any two proof terms of
  the same `Prop` type are definitionally equal by proof irrelevance
  (`is_def_eq_proof_irrel`).
- **Realization in Anneal:**
  1. **Split-Phase `theory/` Audit (`-vos`/`-vok` analogue):** When checking
     `Mir.lean` and `Proof.lean`, the Lean 4 kernel never reads the `.value`
     field of any `theorem` in `theory/Anneal/`; it reads only `.type` (and
     `.levelParams`). Moving pre-audited `trusted` and `theory` modules from
     `locals` into `base`—and optionally replacing `.thmInfo` entries in the
     runtime `.olean` cache with `.axiomInfo` stubs of identical `.name`,
     `.levelParams`, and `.type`, as proved conservative in
     [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md)—eliminates
     all `theory/` proof replay at runtime.
  2. **Semantic Opacity and Canonical Schemas (`VST` analogue):** Sealing
     derived program-logic lemmas in `theory/Anneal/` as `theorem` (`thmInfo`)
     and replacing nested record projections with canonical tuple/validator
     steps prevents Lean's elaborator and kernel from unfolding
     `EventualBehaviorOf` and `ReachesPrefix` inside per-crate `Proof.lean`.

---

### Finding 3: Iris / Diaframe / RefinedC / RefinedRust (`Lithium` Goal-Directed Typeclass Search Over Pre-Proved `Subsume`, `SimplifyHyp`, and `SimplifyGoal` Schemas)

`Basis: documentation + source + derived`

#### Primary-Source Coordinates and Citations

- **Repository (`iris/refinedc`):** Commit
  `2e89846baeaa7f65cbe17e3ae7297a8ed5b4feca` (and
  `d057583986651a28047164581f05fbee3a83ed9d`):
  - `theories/lithium/definitions.v` (lines 19–332): Defines the goal-directed
    subsumption and simplification typeclasses `Subsume` (line 19), `SimplifyHyp`
    (line 33), `SimplifyGoal` (line 45), `FindInContext` (line 88), and the
    syntax-directed logic-programming (`liStmt`) AST connectives (lines
    203–332).
  - `theories/lithium/interpreter.v` (lines 19–196): Defines the single-pass
    goal-directed separation-logic interpreter `li_step` and `liRStep` (line 53).
  - `theories/typing/type.v` (lines 14–108): Defines refinement ownership types
    `r @ ty` (`ty_own_val`, `ty_own`, `ty_shr`).
  - `theories/typing/adequacy.v` (lines 15–51): Proves the Adequacy Theorem
    erasing Iris `iProp Σ` and Lithium typing judgments to closed operational
    `Caesium` execution statements.
- **Repository (`lgaeher/refinedrust-dev` & Zenodo `21636474`):** Commit
  `8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`:
  - `theories/typing/programs.v` (lines 51–123): Defines `typed_stmt`,
    `typed_body`, and per-instruction typing schemas over Radium MIR.
  - `theories/typing/function.v` (lines 62–150): Defines `typed_function` and
    modular function-call subsumption.
- **Publications:**
  - Sammler, Lepigre, Krebbers, Memarian, Dreyer, and Garg, *RefinedC:
    Automating the Foundational Verification of C Code with Refined Ownership
    Types*, PLDI 2021, pp. 158–174, DOI `10.1145/3453483.3454036`.
  - Gäher, Sammler, Spies, Jung, Marquardt, Lepigre, Krebbers, and Dreyer,
    *RefinedRust: A Type System for High-Assurance Verification of Rust
    Programs*, PLDI 2024, PACMPL 8(PLDI), Article 192, DOI `10.1145/3656422`.
  - Mulder, Krebbers, and Geuvers, *Diaframe: Automated Verification of
    Fine-Grained Concurrent Programs in Iris*, PLDI 2022, pp. 809–824, DOI
    `10.1145/3519939.3523432`.

#### Technical Mechanism and Architectural Analysis

1. **Overhead of General Separation-Logic Proof Mode (`IPM` / `MoSeL`) in
   Automated Program Verification:**
   In standard Iris (`MoSeL`, Krebbers et al., ICFP 2018), every spatial tactic
   (`iDestruct`, `iFrame`, `iApply`) manipulates a reified environment
   `envs (iPropI Σ)` and checks spatial entailments by reflecting the spatial
   context and running associative-commutative list manipulation inside Rocq.
   For a 100-line C or Rust MIR function with 40 local variables, running
   `iFrame` at every MIR statement incurs $O(N^2)$ to $O(N^3)$ overhead in
   context size $N$ and can backtrack exponentially when multiple heap
   predicates (`r1 ↦ ty1`, `r2 ↦ ty2`) match a subgoal.
2. **Lithium's Deterministic Goal-Directed Architecture (`iris/refinedc`):**
   Lithium replaces unstructured separation-logic entailment search with a
   **syntax-directed logic-programming calculus (`liStmt`)** governed by four
   pre-proved typeclass rule families (`theories/lithium/definitions.v:19-105`):
   - `TypedInstruction` / `typed_stmt`: Maps each concrete C (`Caesium`) or Rust
     MIR (`Radium`) instruction directly to a fixed sequence of Lithium goals
     without unfolding the operational semantics or Iris `wp` definition.
   - `SimplifyHyp` and `SimplifyGoal`: Deterministically decompose compound
     ownership types (`r @ struct_ty`, `r @ &own(ty)`, `r @ int(u64)`) in the
     spatial context or goal into atomic points-to facts (`l ↦ v`) and pure
     side conditions (`⌜0 ≤ x < 2^64⌝`).
   - `FindInContext` and `Subsume A B G`: When an instruction requires ownership
     of location `l` (`FindInContext (FindDirect l)`), Lithium looks up `l`
     directly as a syntactic key and invokes `Subsume (l ↦ ty1) (l ↦ ty2) G`,
     consuming `l ↦ ty1` in one step and emitting the pure residue `G` (a
     standard `Prop` goal discharged at the end of the basic block by `lia` or
     SMT).
   - **Zero-Backtracking Invariant:** Every `Subsume`, `SimplifyHyp`, and
     `SimplifyGoal` instance is required to be invertible (committing to a
     unique choice without backtracking), keeping proof search linear $O(|I|)$
     in the number of MIR instructions $|I|$.
3. **Diaframe's Bi-Abductive Hint Database (`Mulder et al., PLDI 2022`):**
   Diaframe extends goal-directed Iris search to fine-grained concurrency (ghost
   state updates and atomic invariants) by factoring frame inference into a
   bi-abductive typeclass `BiAbd P Q R` ($P * \text{?anti-frame} \vdash Q * R$)
   driven by pre-proved library hints, avoiding step-indexed unfolding during
   per-program verification.

#### Correspondence to Lean `v4.34.1` and Anneal

- **Separating Spatial/Instruction Framing from Pure `VerificationResult`
  Obligations:**
  Lithium's separation between deterministic instruction stepping and residual
  pure side conditions `G` maps directly onto Anneal's
  `VerificationResult policy waived obligations`
  (`trusted/lean/Trusted/Refinement.lean:458-489`):
  - In `theory/Anneal/`, pre-proved block/idiom validators (`evalIdiomPlan`,
    `checkSideConds` in
    [`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md))
    step through MIR basic blocks in a single deterministic pass and discharge
    batch arithmetic/alignment/disjointness side conditions by `Eq.refl true`
    or emit remaining symbolic obligations into `obligations : List Obligation`.
  - A single pre-proved soundness theorem in `theory/Anneal/` (analogous to
    `theories/typing/adequacy.v:15-51`) bridges the validator result and
    `VerificationResult` obligations to `Trusted.CrateTheorem`.

---

### Finding 4: HOL4 / HOL Light / Candle LCF Abstract `thm` Persistence (`TheoryReader.sml` / `disk_thm`), Myreen's `cv_trans` / `cv_compute` Fast In-Kernel `:cv` Evaluation, and `awslabs/s2n-bignum` Checkpointed Session Images + Modular Subroutine Specifications

`Basis: documentation + source + derived`

#### Primary-Source Coordinates and Citations

- **Repository (`HOL-Theorem-Prover/HOL`):** Commit
  `68c9d77e53532cb258e09421952efe3957f40276`:
  - `src/postkernel/TheoryReader.sml` (lines 27–79): `load_thydata_from_dat`
    reads serialized parent theory `.dat` S-expressions (`HOLsexp`), verifies
    parent theory hashes (`Theory.link_parents (thyname, hash)` at line 37),
    reconstructs shared types and terms (`SharingTables.dec_sdata` at lines
    45–50), and mints abstract `Thm.thm` values via `export_from_sharing_data`
    (line 51) without re-running ML proof scripts.
  - `src/thm/std-thm.ML` (lines 1476–1503): `disk_thm` constructs a kernel
    `THM(Tag.read_disk_tag (d,ocl), list_hyp asl, c)` tagged with `Count.Disk`.
  - `src/thm/std-thm.ML` (lines 1509–1558) and `src/thm/Compute.sml` (lines
    1–90): Implements the kernel primitive `Thm.compute`, which validates a set
    of characteristic equations (`char_eqns`) and recursive code equations
    (`code_eqs` over the `:cv` Lisp S-expression type), executes
    `Compute.term_compute` at native ML speed using arbitrary-precision
    integers, and mints `|- tm = tm'` tagged with `Count.Compute`.
  - `src/num/theories/cv_compute/cv_computeLib.sml` (lines 21–90): Instantiates
    `Thm.compute` with `:cv` (`Pair cv cv | Num num`) and `:num` characteristic
    equations.
- **Repository (`jrh13/hol-light`):** Commit
  `233b83c3202370e03c54de2bd090e4d34f677e91` (`fusion.ml` lines 320–569,
  defining the 10 primitive inference rules of the stateless LCF `thm` kernel).
- **Repository (`awslabs/s2n-bignum`):** Commit
  `9f2cd960e11892a582e7facb0c191b4a2959ea91` (and
  `4d1356a7470663c752660a59375dc3a9ef548428`):
  - `common/execution.ml` (lines 1254–1805): Defines the single-instruction
    symbolic steppers `STEP_TAC`, `ARM_SINGLE_STEP_TAC`, and
    `X86_SINGLE_STEP_TAC` using pre-proved instruction decode theorems and
    canonical state projections.
  - `arm/proofs/instruction.ml` (lines 727–745) and `x86/proofs/bignum_add.ml`
    (lines 51–164): Pre-proved per-instruction decoder/semantics theorems and
    symbolic execution proofs over machine-code byte sequences.
- **Publications:**
  - Myreen, *Fast, Verified Computation for HOL*, ITP 2021, LIPIcs vol. 193,
    Article 27, DOI `10.4230/LIPIcs.ITP.2021.27`.
  - Abrahamsson, Myreen, Kumar, and Tan, *Candle: A Verified Implementation of
    HOL Light*, ITP 2022, LIPIcs vol. 237, Article 3, DOI
    `10.4230/LIPIcs.ITP.2022.3`.
  - Gómez-Londoño and Myreen, *HOL4's New Compute Primitive: Verified
    Compilation of HOL Functions to `cv_compute` (`cv_trans`)*, ITP 2023,
    LIPIcs vol. 268, Article 17, DOI `10.4230/LIPIcs.ITP.2023.17`.

#### Technical Mechanism and Architectural Analysis

1. **LCF Abstract `thm` Persistence (`HOL4 TheoryReader` vs. `HOL Light`
   Process Checkpointing):**
   In a pure LCF system (`jrh13/hol-light` `fusion.ml:320-569`), a theorem `thm`
   is an abstract ML value with no persistent proof object once constructed.
   - Because HOL Light has no built-in `disk_thm` deserializer in `fusion.ml`,
     reloading the base libraries and ISA semantics (`arm/proofs/instruction.ml`,
     `x86/proofs/instruction.ml`) from source takes 15–40 minutes; consequently,
     `awslabs/s2n-bignum` relies on OS-level process checkpointing (`dmtcp` /
     `criu`) or persistent background ML sessions to snapshot the live OCaml
     heap containing pre-proved `thm` values.
   - By contrast, HOL4 (`src/postkernel/TheoryReader.sml:27-79` and
     `src/thm/std-thm.ML:1476-1503`) serializes each compiled theory's exported
     theorem statements (`(asl, c)`) and DAG-shared term tables (`SharingTables`)
     along with parent theory hashes (`#parents rawthy`, checked by
     `Theory.link_parents (thyname, hash)` at line 37) into `.dat` files. When a
     downstream theory loads a parent `.dat` file, `disk_thm` reconstructs
     abstract `Thm.thm` values directly from the statement table in milliseconds
     without re-running primitive inference rules.
2. **In-Logic Fast Computation via `cv_compute` and `cv_trans` (Myreen ITP 2021,
   ITP 2023):**
   In traditional HOL4 and HOL Light, evaluating a ground function in logic
   (`EVAL` / `cbv_conv`) chains primitive LCF equality steps (`Thm.Beta`,
   `Thm.Subst`, numeral bit manipulations), which is $10^3\times$ to
   $10^4\times$ slower than native execution.
   - Myreen (ITP 2021) added `Thm.compute` (`src/thm/std-thm.ML:1532-1558` and
     `src/thm/Compute.sml`) to the HOL4 kernel (and proved it conservative in
     Candle, ITP 2022): it introduces a single first-order Lisp-like datatype
     `:cv = Num num | Pair cv cv` with primitive operations (`cv_add`, `cv_sub`,
     `cv_mul`, `cv_div`, `cv_mod`, `cv_lt`, `cv_if`, `cv_eq`, `cv_fst`,
     `cv_snd`, `cv_ispair` in `cv_computeLib.sml:21-52`). Given first-order
     recursive equations over `:cv` proved as theorems (`code_eqs`),
     `Compute.term_compute` executes them in an ML loop backed by GMP/PolyML big
     integers and returns `|- f (Num n) = Num m` in a single kernel step.
   - Gómez-Londoño and Myreen (ITP 2023, `cv_trans`) built a certifying
     translation compiler on top of `cv_compute`: for any higher-level HOL
     function $f : \alpha \to \beta$ over algebraic datatypes, lists, words, or
     finite maps, `cv_trans f` defines a `:cv` shadow function
     $f_{\text{cv}} : \text{cv} \to \text{cv}$ and **proves a translation
     theorem**
     $\vdash \forall x,\; \text{from\_cv} (f(x)) = f_{\text{cv}}(\text{to\_cv}(x))$
     at definition time. At runtime, evaluating $f(c)$ invokes `Thm.compute` on
     $f_{\text{cv}}(\text{to\_cv}(c))$ and uses the pre-proved translation
     theorem to lift the result back to $\beta$ in $O(1)$ inference steps.
3. **`awslabs/s2n-bignum` Instruction Pre-Decoding and Modular Subroutine
   Specifications:**
   In `awslabs/s2n-bignum`, `X86_MK_EXEC_RULE` (`common/execution.ml:1254-1805`)
   pre-decodes concrete machine-code byte sequences once per function using
   generic decode schemas (`arm/proofs/instruction.ml:727-745`), and modular
   subroutine specifications allow callers to step over helper calls using the
   callee's pre-proved contract rather than re-stepping the callee's instructions.

#### Correspondence to Lean `v4.34.1` and Anneal

- **Lean 4 Already Includes a Native C++ GMP Fast Path (`reduce_nat`):**
  In `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  `src/kernel/type_checker.cpp:101-372` (`reduce_nat` and `reduce_bin_nat_op`)
  intercepts `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`,
  `Nat.gcd`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`,
  `Nat.shiftLeft`, and `Nat.shiftRight` on closed `.lit (.natVal n)` literals
  and evaluates them in C++ using GMP `mpz_t` (`lean::mpz`) without unfolding
  Peano `Nat.succ` constructors.
- **Applying the `cv_trans` Pattern in `theory/Anneal/` (`evalCvProg_sound`):**
  While Lean 4's kernel natively accelerates closed `Nat` arithmetic and bitwise
  shifts in C++, user-defined inductive ASTs (`MirState`, `BitVec` wrappers,
  `Array`) reduce via interpreted Whnf constructor matching. By adopting HOL4's
  `cv_trans` pattern in `theory/Anneal/`—evaluating pure `BitVec64`/register
  chains via a `Nat`-mirror evaluator (`evalCvExpr`, `evalCvProg`) paired with a
  pre-proved correspondence theorem (`evalCvProg_sound` in
  [`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md))—Anneal
  achieves native C++ GMP reduction speed inside `rfl` (`Eq.refl`) without
  `native_decide` (`Lean.ofReduceBool`) and with zero additions to `trusted/`.
  Crucially, as established in
  [`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md),
  because `type_checker::reduce_nat` immediately returns `none` when
  `has_fvar(e)` holds (which causes `Nat.shiftRight` / `Nat.div` to get stuck on
  `WellFounded.fix` when applied to an unpacked local `let` state variable `s`),
  any fallback symbolic stepper must unpack `State.casesOn` at step entry so
  concrete register fields are exposed as closed `.lit (.natVal n)` literals.

---

### Finding 5: Isabelle/HOL Stacked Session Heap Images (`isabelle build -b`), `AutoCorres` (`PLDI 2014`) 5-Phase Schematic Refinement (`ac_corres_chain`), and `Isabelle_LLVM` (`Sepref`)

`Basis: documentation + source + derived`

#### Primary-Source Coordinates and Citations

- **Repository (`seL4/l4v`):** Commit `12c300e75bb0ca0c82f76496fafacd7e614c0aba`:
  - `tools/autocorres/AutoCorres.thy` (lines 11–90): Defines `ac_corres_chain`
    (lines 78–90), which composes the five phase correspondence theorems:
    ```isabelle
    lemma ac_corres_chain:
    "⟦ L1corres check_termination Gamma c_L1 c;
       L2corres st_L2 rx_L2 (λ_. ()) P_L2 c_L2 c_L1;
       L2Tcorres st_HL c_HL c_L2;
       corresTA P_WA rx_WA ex_WA c_WA c_HL;
       L2_call c_WA = A ⟧ ⟹
      ac_corres (st_HL o st_L2) check_termination Gamma
        (rx_WA o rx_L2) (P_L2 and (P_WA o st_HL o st_L2)) A c"
    ```
  - `tools/autocorres/L1Defs.thy`, `L2Defs.thy`, `HeapLift.thy`,
    `WordAbstract.thy`, `TypeStrengthen.thy`: Pre-proved composition and
    structural refinement rules for each of the five phases (`L1`, `L2`, `HL`,
    `WA`, `TS`).
- **Repository (`lammich/isabelle_llvm`):** Commit
  `6be37a9c3cae74a1134dbef2979e312abb5f7f42`:
  - Implements the `Sepref` synthesis framework lowering nondeterministic
    monadic Isabelle/HOL specifications (`nres`) to imperative LLVM IR (`M`) via
    pre-proved relational refinement rules (`hnr`).
- **Publications:**
  - Greenaway, Lim, Andronick, and Klein, *Don't Sweat the Small Stuff: Formal
    Verification of C Code Without the Pain (`AutoCorres`)*, PLDI 2014, pp.
    429–439, DOI `10.1145/2594291.2594296`.
  - Lammich, *Refinement to Imperative HOL (`Sepref`)*, ITP 2015, LNCS vol.
    9236, pp. 253–269, DOI `10.1007/978-3-319-22102-1_17`.
  - Lammich, *Generating Verified LLVM from Isabelle/HOL*, ITP 2019, LIPIcs vol.
    141, Article 21, DOI `10.4230/LIPIcs.ITP.2019.21`.

#### Technical Mechanism and Architectural Analysis

1. **Stacked Session Heap Images (`isabelle build -b` / `PolyML.SaveState`):**
   Isabelle/HOL organizes developments into a DAG of sessions (`ROOT` files:
   `Pure` $\to$ `HOL` $\to$ `HOL-Word` $\to$ `AutoCorres` $\to$ `CRefine`).
   When `isabelle build -b <Session>` runs, Poly/ML incremental heap saving
   (`PolyML.SaveState.saveChild`) writes a read-only delta heap image of the
   verified `Context.theory` state containing all abstract `thm` values, syntax
   tables, and `simpset`/`wp` rule nets. When verifying a leaf C file in seL4,
   Isabelle maps the parent session heaps into memory and checks only the leaf
   theory without re-checking `HOL` or `AutoCorres`.
2. **`AutoCorres`'s Staged Syntactic-Rule Refinement Pipeline (`L1` $\to$ `L2`
   $\to$ `HL` $\to$ `WA` $\to$ `TS`):**
   Instead of proving a monolithic refinement from deeply embedded C (`SIMPL`)
   to a shallow pure/monadic function in one pass, `AutoCorres` factors C
   abstraction into five orthogonal syntactic phases, each backed by a finite
   set of pre-proved syntax-directed composition rules:
   - **Phase 1 (`L1`, `ExceptionRewrite.thy`):** Flattens C `break`, `continue`,
     `return`, and `goto` control flow into uniform structured exception blocks
     (`L1_seq`, `L1_catch`, `L1_while`, `L1_condition`), proved via pre-proved
     `L1corres` congruence rules.
   - **Phase 2 (`L2`, `LocalVarExtract.thy`):** Lifts C stack frame record
     fields (`myvars.x_'`) into SSA-like functional monadic bound variables,
     discharging frame preservation via pre-proved `L2corres` rules.
   - **Phase 3 (`HL`, `HeapLift.thy`):** Splits the monolithic byte-level C heap
     `hrs_mem` into disjoint typed pointer heaps (`heap_w32`, `heap_struct_foo`)
     guarded by pointer validity (`c_guard p`), proved via `L2Tcorres` rules.
   - **Phase 4 (`WA`, `WordAbstract.thy`):** Abstracts 32-bit/64-bit machine
     words (`word32`, `sword32`) into unbounded mathematical `nat` or `int`,
     inserting explicit overflow guards (`0 ≤ x + y ≤ INT_MAX`) via pre-proved
     `corresTA` rules.
   - **Phase 5 (`TS`, `TypeStrengthen.thy`):** Strengthens the nondeterministic
     state-exception monad into a deterministic `option` monad or pure total
     function (`L2_call c_WA = A`).
   - **Top-Level Composition (`ac_corres_chain`, `AutoCorres.thy:78-90`):** A
     single 12-line pre-proved theorem chains all five phases into the final
     `ac_corres` theorem. Because each phase's structural rules (`seq`, `cond`,
     `while`, `call`) are pre-proved once in `tools/autocorres/*.thy`,
     translating a C function of $K$ AST nodes applies $O(K)$ pre-proved syntax
     rules by resolution (`RTAC` in Isabelle ML) without unfolding monad or
     operational semantics definitions.
3. **`Isabelle_LLVM` `Sepref` (Lammich ITP 2015, ITP 2019):**
   `Sepref` operates top-down: given an abstract algorithm in the `nres`
   nondeterministic refinement monad, `Sepref` applies pre-proved higher-order
   separation-logic refinement rules (`hnr Γ c Γ' R m`) syntax-directedly over
   $m$, synthesizing both the concrete LLVM program $c$ and its kernel proof in
   a single pass.

#### Correspondence to Lean `v4.34.1` and Anneal

- **`AutoCorres` `ac_corres_chain` Maps to Transitive `Abstracts` and
  `Compiles` Chains in `Trusted/Refinement.lean`:**
  In `trusted/lean/Trusted/Refinement.lean` (`trusted-core` branch at
  `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`), `Abstracts L₁ L₂ codec v s` and
  `Compiles L₁ L₂ codec s c` are defined by behavioral refinement (`≤` on
  `Behavior Query Out`) through `BehaviorCodec`. Just as `AutoCorres` factors C
  abstraction into `SIMPL → L1 → L2 → HL → WA → TS` composed by
  `ac_corres_chain`, `theory/Anneal/` can compose pre-proved CFG/diamond
  convergence lemmas (`diamond_converge_step`), loop summary theorems
  (`loop_summary_sound`), and interprocedural `CalleeSummary` theorems without
  unfolding the primitive step relation during per-crate proof checking.

---

### Finding 6: Metamath Zero (`MM0` / `.mmb`, Carneiro `CPP 2020`) `STMT_THM` / `CMD_PROOF_THM` $O(1)$ Header Lookup and Dedukti / Alethe / LRAT Certificate Checkers

`Basis: normative + source + derived`

#### Primary-Source Coordinates and Citations

- **Repository (`digama0/mm0`):** Commit
  `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`:
  - `mm0-c/mmb.md` (lines 34–462): Normative binary specification of the `.mmb`
    proof file format, including the header table of sorts, terms/defs, and
    axioms/theorems (`p_terms`, `p_thms`, `StmtEntry` unify stream offsets at
    lines 96–185), the proof stream opcodes (`CMD_PROOF_THM = 0x16` and
    `CMD_PROOF_THM_SAVE = 0x17` at lines 242–298), and the unify stream opcodes
    (`CMD_UNIFY_REF`..`CMD_UNIFY_DUMMY` at lines 350–405).
  - `mm0-c/verifier.c` (lines 213–809): C implementation of the bare `.mmb`
    kernel verifier:
    - `run_unify` (lines 213–315): Executes the theorem header's unify bytecode
      against a substitution array `g_uheap` to match hypotheses and construct
      the instantiated conclusion.
    - `CMD_PROOF_THM` / `CMD_PROOF_THM_SAVE` (lines 436–468): Looks up a
      previously proved theorem `thm_entry* e = &g_thms[data]` in the header
      table by $O(1)$ array indexing, checks disjoint-variable (`DV`) constraints
      in $O(1)$ bitmask operations, and runs `run_unify` on the theorem's header
      statement—**never reading or re-executing the theorem's proof stream**.
    - `parse_until` (lines 625–745): Verifies the top-level declaration stream
      (`STMT_AXIOM`, `STMT_THM`, `STMT_DEF`), checking each `STMT_THM`'s proof
      stream once and discarding its proof stack before advancing to the next
      declaration.
  - `examples/separation_logic.mm1`: Demonstrates pre-proving derived separation
    logic and x86-64 Hoare rules as `theorem` entries in MM1/MMB so downstream
    machine-code proofs invoke them via single `CMD_PROOF_THM` opcodes.
- **Repository (`Deducteam/Dedukti` & `Deducteam/lambdapi`):**
  - `Deducteam/Dedukti@f3c0eba869ddd46f2e75c123a59f2b612076dba0`:
    `kernel/typing.ml` (lines 105–410) and `kernel/confluence.ml` (lines 23–213),
    implementing user-declared rewrite rules (`[x, y] f x y --> g x y`) in the
    $\lambda\Pi$-calculus modulo rewriting ($\lambda\Pi/\equiv_{\beta\mathcal{R}}$).
  - `Deducteam/lambdapi@72cc2f10d391932fe078ba5a401765e29a1d4cb7`:
    `src/handle/command.ml` (lines 228–284), registering user rewrite rules into
    the kernel symbol table (`Sign.add_rule`).
- **Publications:**
  - Carneiro, *Metamath Zero: Designing a Theorem Prover Prover*, CPP 2020, pp.
    71–84, DOI `10.1145/3372885.3373824`.

#### Technical Mechanism and Architectural Analysis

1. **Why Metamath Zero (`MM0` / `.mmb`) Achieves Sub-Millisecond Derived-Rule
   Application Without Growing the TCB (`mm0-c/verifier.c:436-468`):**
   In `MM0` (`Carneiro, CPP 2020`), there is **zero distinction at point of use**
   between a primitive `axiom` (`STMT_AXIOM`) and a pre-proved `theorem`
   (`STMT_THM`):
   - In the `.mmb` binary header (`mm0-c/mmb.md:96-185`), both `axiom`s and
     `theorem`s occupy identical 8-byte `StmtEntry` records in the global
     `g_thms` array, each storing `(num_args, unify_stream_offset)` describing
     its bound/regular arguments, hypotheses, and conclusion as a flat
     reverse-Polish unification bytecode stream.
   - When a `theorem` $T_k$ is declared in the `.mmb` file (`STMT_THM`), the
     verifier (`parse_until` in `mm0-c/verifier.c:625-745`) executes $T_k$'s
     proof stream **once** to check that it derives the conclusion specified by
     $T_k$'s unify stream from $T_k$'s hypotheses, and then immediately discards
     the proof stack (`g_hstack`).
   - From that point forward, whenever any subsequent theorem proof invokes
     `CMD_PROOF_THM(k)` (`verifier.c:436-468`), $T_k$ is applied in **the exact
     same way and at the exact same $O(|\text{stmt}(T_k)|)$ cost as a primitive
     axiom**: the verifier pops the hypotheses from the proof stack, runs
     `run_unify` on $T_k$'s header unify stream, checks the 64-bit
     disjoint-variable (`DV`) bitmasks, and pushes the instantiated conclusion.
     The internal proof of $T_k$ is never read again.
2. **Contrast with Dedukti / Lambdapi ($\lambda\Pi$-Calculus Modulo User Rewrite
   Rules) vs. Verified `LRAT` / `Alethe` Certificate Checkers:**
   Dedukti (`Deducteam/Dedukti`) accelerates derived equational rules by letting
   users inject custom rewrite rules $l \hookrightarrow r$ directly into the
   kernel's conversion test (`kernel/typing.ml` and `kernel/confluence.ml`).
   However, adding unverified user rewrite rules to the kernel conversion engine
   **directly expands the TCB**: a non-terminating or non-confluent rewrite rule,
   or one that equates `true` and `false`, makes the logic inconsistent
   (`False`), and Lean 4's kernel intentionally forbids user rewrite extensions
   (`Lean.Environment.addQuot` is closed; `@[csimp]` only affects compiled code
   and is rejected by `TrustedBoundary.lean:240-275`). By contrast, external
   certificate formats (`LRAT` for SAT and `Alethe` for SMT) verified by a
   total recursive boolean checker `checkCert : Formula → Cert → Bool` proved
   sound once in `theory/Anneal/` (`checkCert_sound`) and invoked via
   `Eq.refl true` add zero rules to the kernel TCB.

#### Correspondence to Lean `v4.34.1` and Anneal

- **Lean 4's `ConstantInfo.thmInfo` in Pre-Audited `.olean` Files Is
  Mechanically Isomorphic to MM0's `StmtEntry` Header Table:**
  - In `MM0`, once `STMT_THM` $T_k$ is verified, `CMD_PROOF_THM(k)` reads only
    $T_k$'s header statement (`g_thms[k]`), never $T_k$'s proof stream.
  - In Lean 4 (`src/kernel/environment.cpp:192-209` and
    `src/kernel/type_checker.cpp`), once a `theorem` $T_k$ in `theory/Anneal/`
    is verified and stored in `base : Kernel.Environment` as
    `ConstantInfo.thmInfo`, applying `@T_k` in `Proof.lean` checks only the
    argument types against `T_k.type` (and universe arguments against
    `T_k.levelParams`)—it **never** reads or unfolds `T_k.value`.
  - Consequently, as proved in our companion report
    [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md),
    even replacing `.thmInfo` declarations in pre-audited `theory/Anneal/`
    `.olean` files with `.axiomInfo` stubs of identical `.name`, `.levelParams`,
    and `.type` (stripping the serialized proof DAGs from disk) is 100%
    kernel-indistinguishable during Stage-2 verification of `#[Mir, Proof]`.

---

### Finding 7: Gonthier–Mahboubi SSReflect Small-Scale `reflect` Views and Malecha et al. `MirrorCore` `RTac` (`Result.More_ s' g'` Residual Obligation Emission)

`Basis: documentation + source + derived`

#### Primary-Source Coordinates and Citations

- **Repository (`rocq-prover/rocq`):** Commit
  `0b9568e12875891c1b9463fa3548f36384ea6f99`:
  - `theories/Corelib/ssr/ssrbool.v` (lines 18–30, 657–724): Defines
    `is_true (b : bool) : Prop := b = true`,
    `Inductive reflect (P : Prop) : bool -> Set := ReflectT of P : reflect P
    true | ReflectF of ~ P : reflect P false`, and the reflection bridge lemmas
    `elimT : reflect P b -> b -> P` (line 709) and
    `introT : reflect P b -> P -> b` (line 702).
- **Repository (`gmalecha/mirror-core`):** Commit
  `b962fbca15b0b5a4653f66d29d7115bb04ebd4f3`:
  - `theories/RTac/Core.v`:
    - Lines 62–69: Defines the reified goal tree
      `Inductive Goal := GAll : typ -> Goal -> Goal | GExs : list typ -> amap
      expr -> Goal -> Goal | GHyp : expr -> Goal -> Goal | GConj_ : Goal ->
      Goal -> Goal | GGoal : expr -> Goal | GSolved : Goal`.
    - Lines 197–199: Defines a reflective tactic
      `Definition rtac : Type := forall c : Ctx typ expr, ctx_subst c -> expr ->
      Result c` returning `Fail | Solved s' | More_ s' g'`.
    - Lines 402–439 and 488–524: Defines `rtac_spec`, `GoalImplies`, and
      `rtac_sound (tac : rtac) : Prop`: when `tac` returns `Solved s'`, the
      denotation of the original goal `goalD ... g` holds outright; when `tac`
      returns `More_ s' g'` (for a partially solved symbolic goal with open
      obligations), the denotation of the residual subgoal `goalD ... g'`
      implies the original goal `goalD ... g` (`GoalImplies (s, g) (s', g')`,
      line 488).
- **Publications:**
  - Gonthier and Mahboubi, *An Introduction to Small Scale Reflection in Coq*,
    Journal of Formalized Reasoning 3(2), pp. 95–152, 2010, DOI
    `10.6092/issn.1972-5787/1979` (and JAR 2010, DOI
    `10.1007/s10817-010-9183-1`).
  - Malecha, Chlipala, and Braibant, *Compositional Computational Reflection
    (`MirrorCore` / `RTac`)*, ITP 2014, LNCS vol. 8558, pp. 374–389, DOI
    `10.1007/978-3-319-08970-6_24` (and Malecha et al., ESOP 2016, LNCS vol.
    9632, pp. 532–559, DOI `10.1007/978-3-662-49498-1_19`).

#### Technical Mechanism and Architectural Analysis

1. **Small-Scale Reflection (`ssrbool.v` `reflect P b`) vs. Large-Scale Partial
   Reflection (`MirrorCore` / `RTac`):**
   - **Small-Scale Reflection (Gonthier & Mahboubi, 2010):** Instead of reifying
     an arbitrary syntactic meta-language of `Prop` formulas, small-scale
     reflection states local invariants and side conditions directly as
     computable boolean predicates `b : Bool` coerced to `Prop` via `b = true`
     and bridged to logical specifications $P : \text{Prop}$ via `reflect P b`
     (`elimT : reflect P b → b = true → P`). Whenever subterms are closed or
     canonical, `b = true` reduces natively in the kernel via `Eq.refl true`;
     whenever subterms contain symbolic variables, equational rewriting on
     `Bool` (`&&`, `||`) simplifies the boolean expression without building
     nested `And.intro` / `Or.inl` proof trees.
   - **Partial Reflective Simplification for Open/Symbolic Goals (`RTac`
     `More_ s' g'` in `gmalecha/mirror-core`, `theories/RTac/Core.v:62-69,
     402-524`):** A purely boolean decision procedure `decide : Expr → Bool`
     only succeeds when a goal is 100% closed (`Solved`). When symbolic
     execution of a function discharges 95% of the steps (register/local moves,
     concrete layout offsets, alignment masks) by computation but leaves 5% as
     open symbolic proof obligations (user postconditions, nonlinear arithmetic,
     or external call contracts), `MirrorCore` / `RTac` returns
     **`Result.More_ s' g'`** (`GoalImplies (s, g) (s', g')` at line 488): the
     reflective procedure executes inside the kernel reducer, discharges all
     decidable steps by computation, and emits a simplified residual goal tree
     `g' : Goal` (a conjunction of unsolved symbolic obligations `GConj_`,
     `GAll`, `GHyp`, `GGoal`). The once-and-for-all theorem `rtac_sound` proves
     that **if the residual denotation `goalD ... g'` holds, then the original
     goal `goalD ... g` holds.**
2. **Interaction with Lean 4's `bv_decide`, `grind`, and `omega` Under
   `TrustedBoundary.lean`:**
   - **Upstream `bv_decide`:** Relies on `Lean.ofReduceBool` (`native_decide`)
     to run compiled C code for its LRAT checker, which is rejected by
     `TrustedBoundary.lean:318-329,562-578` because `Lean.trustCompiler` places
     the Lean-to-C compiler inside the TCB. In Anneal, reflective checkers in
     `theory/Anneal/` run inside the Lean 4 kernel Whnf reducer via `rfl`
     (`Eq.refl true`).
   - **`omega` and `grind`:** Construct explicit kernel proof terms (`Expr.app`
     chains of linear-combination and ring-normalization lemmas). They are
     accepted by `TrustedBoundary.lean`, and are suited to discharging the
     small residual symbolic obligations (`Result.More_ s' g'`) that remain
     after reflective symbolic stepping and batch `checkSideConds` `rfl`
     reduction.

#### Correspondence to Lean `v4.34.1` and Anneal

- **`RTac`'s `More_ s' g'` (`GoalImplies`) Directly Models Anneal's Reflective
  VCGen Targeting `VerificationResult`:**
  In Anneal, a reflective symbolic evaluator / VCGen in `theory/Anneal/` steps
  through the MIR CFG inside Lean's kernel reducer:
  - Concrete memory layout offsets, local register reads/writes, idiom plans
    (`evalIdiomPlan`), pure bitvector blocks (`evalCvProg`), and batch
    arithmetic/disjointness checks (`checkSideConds`) reduce to `true` via
    `rfl`.
  - Any remaining open or symbolic obligations (such as a loop or external-call
    postcondition containing symbolic parameters) are emitted into the residual
    obligation list `obs : List Obligation` of `VerificationResult policy waived
    obs` (`Trusted/Refinement.lean:458-489`).
  - A pre-proved soundness theorem in `theory/Anneal/` (analogous to `RTac`'s
    `rtac_sound` for `More_ s' g'`) proves that if the reflective validator
    returns `true` and `VerificationResult policy waived obs` holds, then
    `Compiler.Verified` holds for the function.

---

### Finding 8: Cross-System Comparative Synthesis Matrix and Architectural Realization in Lean `v4.34.1` and Anneal (`trusted/` vs. `theory/Anneal/`)

`Basis: source + derived`

#### 8.1 Comparative Synthesis Matrix Across All Six Prior-Art Families

| Prior-Art Family & Mechanism | (a) TCB Impact | (b) Build-Time (Stage-1 Pre-Audit) vs. Runtime (Stage-2 Per-Crate) Cost | (c) Handling of Open / Symbolic Obligations | (d) Realization in Lean `v4.34.1` and Anneal (`trusted/` vs. `theory/Anneal/`) |
| :--- | :--- | :--- | :--- | :--- |
| **1a. Rocq `-vos`/`-vok` & `OpaqueDef` (`kernel/declarations.mli:56`, `constant_typing.ml:262-291`)** | **Zero TCB growth** when `.vok` delayed proof checks are completed and locked; kernel never unfolds `OpaqueDef` during conversion. | **Stage 1:** Full kernel checking of `theory/` proofs (`-vok`).<br>**Stage 2:** $O(|\text{stmt}|)$ header import; zero replay of `theory/` proof bodies. | Agnostic (applies to arbitrary universally quantified theorem statements in `Prop`). | **Mechanism I:** Pre-audit `trusted/lean/` and `theory/Anneal/` in Stage 1, lock `.olean` SHA-256 digests (`prefix-lock.json`), and load `foundation ++ trusted ++ theory` as `base` in `TrustedBoundary.lean` so Stage 2 replays only `#[Mir, Proof]`. |
| **1b. Rocq `Strategy opaque` & VST Canonical Schemas (`floyd/sc_set_load_store.v:222-350`, `call_lemmas.v:941-1658`)** | **Zero TCB growth:** `semax` and all Floyd lemmas are proved in `Prop` (`Qed`) over CompCert operational semantics. | **Stage 1:** Prove canonical load/store/call lemmas once in `theory/`.<br>**Stage 2:** $O(1)$ lemma application per block/statement + `rfl` on finite-map lookups; avoids unfolding `semax`. | Symbolic values, ghost variables, and pure `PROPx` propositions are carried syntactically in the canonical state tuple. | Seal derived Hoare/WP wrappers in `theory/Anneal/` as `theorem` (`thmInfo`), unpack state tuples via `State.casesOn`, and use structural list membership witnesses (`.head`/`.tail`) rather than `by decide` on TCB lookup tables. |
| **2. Iris / RefinedC / RefinedRust `Lithium` & `Diaframe` (`theories/lithium/definitions.v:19-332`, `interpreter.v:19-196`)** | **Zero TCB growth:** All `iProp Σ`, cameras, and `Subsume`/`SimplifyGoal` classes live outside the TCB, erased by `adequacy.v`. | **Stage 1:** Prove `TypedInstruction`, `Subsume`, `SimplifyHyp`, and `iris_adequacy` once in `theory/`.<br>**Stage 2:** Deterministic $O(|I|)$ single-pass stepping without backtracking. | Emits unsolved symbolic side conditions as a pure `Prop` continuation `G` at the end of each basic block. | Pre-prove deterministic block/idiom schemas (`evalIdiomPlan_sound`, `checkSideConds_sound`) in `theory/Anneal/` and collect residual pure side conditions into `VerificationResult`'s `obligations : List Obligation`. |
| **3a. HOL4 `TheoryReader` / `disk_thm` (`TheoryReader.sml:27-79`, `std-thm.ML:1476-1503`) & HOL Light Snapshots (`s2n-bignum`)** | **Zero TCB growth** when parent `.dat` files are cryptographically/structurally hash-linked (`Theory.link_parents`). | **Stage 1:** Elaborate and export `.dat`/`.olean` theory tables once.<br>**Stage 2:** Millisecond DAG deserialization of exported `thm` statements; zero inference replay. | Supports arbitrary schematic polymorphism and free variables in exported theorems. | Directly parallels Lean 4 `.olean` importing when `TrustedBoundary.lean` validates `prefix-lock.json` hashes and places `trusted ++ theory` in `base` rather than `locals`. |
| **3b. HOL4 `cv_compute` / `cv_trans` (`std-thm.ML:1532-1558`, `Compute.sml`, Myreen ITP 2021/2023)** | In HOL4/Candle, adds `:cv` evaluator to kernel. **In Lean 4, zero TCB growth** because GMP `reduce_nat` is already in `src/kernel/type_checker.cpp:101-372`. | **Stage 1:** Prove `from_cv (f x) = f_cv (to_cv x)` once in `theory/`.<br>**Stage 2:** Native C++ GMP speed inside `rfl` (`Eq.refl`) without `native_decide`. | Purely ground on `:cv`, or combined with symbolic postconditions via `cv_trans` wrapper theorems. | **Mechanism II:** Encode straight-line bitvector/register computation and batch side-condition lists in `theory/Anneal/` via `Nat`-mirror evaluators (`evalCvProg_sound`, `checkSideConds_sound`) backed by `reduce_nat`. |
| **4. Isabelle/HOL Session Heaps (`isabelle build -b`), `AutoCorres` (`AutoCorres.thy:78-90`), & `Sepref`** | **Zero TCB growth:** All 5 phases (`L1`..`TS`) and `ac_corres_chain` are kernel-checked theorems over `SIMPL`. | **Stage 1:** Build stacked session heap and prove phase rules once.<br>**Stage 2:** Composes passes via `ac_corres_chain` in $O(1)$ top-level steps. | Preserves symbolic inputs, nondeterminism (`StepResult.choice`), and open overflow/pointer guards (`P_L2`, `P_WA`). | Factor `theory/Anneal/` into composable CFG/block/loop/call validators (`diamond_converge_step`, `loop_summary_sound`, `CalleeSummary`) composed via `Abstracts` and `Compiles` in `Trusted/Refinement.lean`. |
| **5a. Metamath Zero `.mmb` Theorem Table (`CMD_PROOF_THM`, `mm0-c/verifier.c:436-468`)** | **Zero TCB growth:** `.mmb` verifier is $< 850$ lines of C; `STMT_THM` is checked once and then indexed identically to `STMT_AXIOM`. | **Stage 1:** Verify `STMT_THM` proof stream once.<br>**Stage 2:** $O(1)$ table lookup + header unification (`run_unify`); proof stream is never re-read. | Supports arbitrary schematic variables and disjoint-variable (`DV`) conditions in theorem headers. | Mechanical model for why Lean 4 `ConstantInfo.thmInfo` declarations (or compacted `.axiomInfo` stubs) in pre-audited `theory/Anneal/` `.olean` files act as zero-cost derived inference rules in `Proof.lean`. |
| **5b. Dedukti / Lambdapi User Rewrite Rules vs. `LRAT` / `Alethe` Certificate Checkers** | **Dedukti:** Expands TCB (unverified rewrite rules can break consistency).<br>**`LRAT`/`Alethe` in `theory/`:** **Zero TCB growth.** | **Stage 1:** Prove `checkLRAT_sound` / `checkAlethe_sound` once in `theory/`.<br>**Stage 2:** Linear $O(|\text{cert}| \log N)$ kernel Whnf reduction via `PArray`. | `LRAT` handles ground bitvectors; `Alethe` and `Egglog` handle quantified/uninterpreted symbolic formulas. | Reject user kernel rewrite extensions (enforced by `TrustedBoundary.lean`); implement certificate checkers as total structural-recursion functions in `theory/Anneal/` invoked via `rfl`. |
| **6. SSReflect (`ssrbool.v:702-724`) & `MirrorCore` / `RTac` (`theories/RTac/Core.v:62-69, 402-524`)** | **Zero TCB growth:** `reflect P b` and `rtac_sound` are proved inside the logic without trusting external code or `native_decide`. | **Stage 1:** Prove `rtac_sound` / validator soundness once in `theory/`.<br>**Stage 2:** Discharges decidable MIR/ISA steps by kernel reduction (`rfl`), leaving a minimal residual goal tree. | **First-class support via `Result.More_ s' g'` (`GoalImplies`):** simplifies symbolic goals and emits unsolved obligations as residual `Prop` subgoals. | Hybrid validator architecture in `theory/Anneal/`: discharge decidable straight-line and side-condition obligations by `rfl`, while emitting open symbolic obligations into `VerificationResult`. |

#### 8.2 End-to-End Realization and Cross-Verification in Companion Packages

The two mechanisms synthesized from these six ITP families have been concretely
implemented, security-audited, and benchmarked in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
across our two companion packages:

1. **Realization of Mechanism I — Two-Stage Pre-Audit, Single-Import Boundary
   Checking, and `.olean` Axiom-Stubbing
   ([`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md)):**
   - **Compositional Conservativity of Moving `trusted ++ theory` to `base`:**
     Because Lean environments are append-only DAGs and `Kernel.Environment.replay`
     is compositional ($\text{replay}(\text{base}, A \cup B) \simeq
     \text{replay}(\text{replay}(\text{base}, A), B)$ when $A = \text{trusted}
     \cup \text{theory}$ is closed over `foundation` and $B = \{\text{Mir},
     \text{Proof}\}$), running Stage-1 `audit-prefix` once to replay $A$ over
     `foundation` and lock `prefix-lock.json`, then running Stage-2
     `audit-crate` to import `base := foundation ++ trusted ++ theory` in a
     single `importModules(..., loadExts := false)` call and replay only
     `Mir.olean` and `Proof.olean` read via `readModuleData`, reduces Phase-2
     `"audit"` wall-clock time from **`2,013.5 ms` to `79.3 ms` (`25.4x`
     speedup)** and halves process `VmRSS` growth (`+49.2 MiB` vs. `+100.5 MiB`).
   - **MM0 `.mmb` / Rocq `.vos` Realization via `.thmInfo -> .axiomInfo`
     Compaction:** Replacing every verified `.thmInfo` constant in the cached
     runtime `Anneal.*` `.olean` files with an `.axiomInfo` stub of identical
     `.name`, `.levelParams`, and `.type` (and pruning unreachable private proof
     helpers plus code-generator LCNF/IR environment extensions) shrinks
     `FunctionalTranslation.olean` from `13.94 MB` to `5.02 MB` (`-64.0%`) and
     total Stage-1 `.olean` size from `17.11 MB` to `6.11 MB` (`-64.3%`) while
     preserving byte-identical behavior in both `lean` elaboration and
     `base.toKernelEnv.replay`.
   - **Boundary Invariants Across the `base` vs. `locals` Seam:** As documented
     in detail in
     [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md),
     splitting `base` and `locals` requires closing five subtle boundary seams:
     (Gap A) recording a 6-feature monotonic fixed-point summary over `base` in
     `prefix-lock.json` (`hasUnsafe`, `hasPartial`, `reachAxioms`,
     `refsTrustCandidate`, `refsVettedInductCtor`, `hasSimp`) paired with
     cross-stage `realizeConst` tracking; (Gap B) recursively scanning
     `e.hasLooseBVars` at every AST node inside `expressionEdges`; (Gap C)
     enforcing `mirCrateCi.levelParams.isEmpty && proofCi.levelParams.isEmpty`
     (which is otherwise exploitable from pure `.lean` source when `lean` runs
     with `-DElab.async=false`); (Gap D) fixed-point propagation over mutual
     blocks; and (Gap E) guarding `@[vetted]` inductive owner checks with
     `if dep != depOwner` so benign type references do not trigger false
     rejections.
2. **Realization of Mechanism II — Hybrid Reflective/Schematic `Theory`
   Validators and Per-Function Incremental Sharding
   ([`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md)):**
   - **Why Mechanism I Alone Is Necessary but Not Sufficient:** On the
     10-function `zerocopy`-style crate benchmark in
     [`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md),
     moving `Theory` from `locals` to `base` (`Stage 0 -> Stage 1`) shrinks the
     audited `.olean` payload by `2.98x` (`5.15 MB` to `1.73 MB`), but reduces
     Stage-2 kernel replay time by only `1.05x` (`5,042.6 ms` to `4,787.1 ms`)
     because `94.9%` of the baseline replay time is spent inside `Proof.lean`
     re-evaluating continuation-lambda proof spines, `{ s with ... }` record
     projections, `omega` proof terms, and `by decide` `String.beq` lookups.
   - **Applying VST + HOL4 `cv_trans` + Lithium + `AutoCorres` + `RTac`
     Patterns (`Stage 1 -> Stage 3 -> Stage 4`):**
     1. Replacing `{ s with ... }` record updates with `State.casesOn` flat-tuple
        unpacking + contiguous `let` sharing + structural `.head`/`.tail`
        membership proofs (`ListMem`) + batch `checkSideConds_sound` `rfl`
        evaluation (`Stage 2`) cuts Stage-2 kernel replay by **`9.84x`** (to
        `512.7 ms`) and unfolded proof-tree size `TREE_NODES` by **`90.92x`**
        (`51,614,627` to `567,704`).
     2. Introducing the 3-layer pre-proved `Theory` validator stack (`Stage 3`:
        Layer A `evalCvProg_sound` HOL4 `cv_trans` `Nat`-mirror evaluator,
        Layer B `evalIdiomPlan_sound` parameterized MIR memory/layout idiom
        validator, and Layer C `diamond_converge_step` + `CalleeSummary` +
        `loop_summary_sound` compositional CFG/call/loop schemas) cuts
        elaboration time by **`23.04x`** (`18,750.3 ms` to `813.8 ms`), cuts
        Stage-2 kernel replay by **`32.11x`** (`5,042.6 ms` to `157.1 ms`, or
        `43.7 ms` / **`115.35x`** excluding four one-time `String.beq` callee
        table lookups), and shrinks `TREE_NODES` by **`995.31x`** (to `51,858`).
     3. Adding per-function `ShardCert` `.olean` sharding (`Stage 4`, analogous
        to fine-grained Rocq `.vos`/`.vok` and HOL4 `.dat` theory granularity)
        so unchanged function shards reside in `base` and only a single modified
        function shard plus the root `CrateTheorem` aggregator are replayed
        reduces incremental Stage-2 kernel replay to **`1.680 ms` (`3,001.54x`
        speedup over `Stage 0`)**.

## Boundaries

- **Known not to apply (Unverified Kernel Rewrite Rules and `native_decide`):**
  Dedukti/Lambdapi-style user-declared kernel rewrite rules
  ($\lambda\Pi/\equiv_{\beta\mathcal{R}}$) and Lean 4's `Lean.ofReduceBool`
  (`native_decide`) do **not** satisfy Anneal's zero-TCB-growth boundary. User
  rewrite rules in the kernel conversion check can violate confluence or
  termination and derive `False`, while `Lean.ofReduceBool` trusts the
  unverified Lean-to-C compiler and native execution environment. All reflective
  evaluators (`evalCvProg`, `evalIdiomPlan`, `wpX86`, `checkSideConds`) and
  certificate checkers (`LRAT`, `Alethe`) in `theory/Anneal/` must execute inside
  the Lean 4 kernel's standard `whnf` / `reduce_nat` engine via `Eq.refl`.
- **Known not to apply (`WellFounded.fix` and Dependent Indexing Inside
  Reflective Evaluators):** While Lean 4's kernel never unfolds `theorem`
  (`ConstantInfo.thmInfo`) bodies from `theory/Anneal/`, it **does** unfold
  `def` (`ConstantInfo.defnInfo`) bodies when checking `rfl` proofs in
  `Proof.lean`. If a reflective evaluator `def` in `theory/Anneal/` uses
  well-founded recursion (`WellFounded.fix`, including `Nat.div` /
  `Nat.shiftRight` on open `has_fvar` terms where `reduce_nat` does not fire) or
  carries embedded proof terms (`Array.get` with `h : i < a.size`), kernel Whnf
  reduction can stall or spend exponential time reducing proof terms inside
  computational branches. All reflective evaluators in `theory/Anneal/` must use
  primitive structural recursion (`Nat.rec` / `List.rec` on explicit fuel or
  inductive syntax), total indexing (`getD` / `?`), and `State.casesOn` entry
  unpacking.
- **Not examined (Fresh Execution of Non-Lean External Provers):** Rocq, VST,
  RefinedC/RefinedRust, HOL4, HOL Light (`s2n-bignum`), Isabelle/HOL
  (`AutoCorres`, `Isabelle_LLVM`), Metamath Zero (`mm0-c`), Dedukti, and
  `MirrorCore` were examined via their immutable Git source trees and published
  artifacts/papers rather than compiled and executed locally on this host. Only
  Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and Anneal were
  executed directly (as recorded in the companion packages).

## Evidence

All primary-source claims in this report are bound to immutable Git revisions
examined on `2026-10-31`:

1. **Anneal (`joshlf/anneal`):**
   - `76fad1a1befa2e4c038d88c3a1bbbe873acb1322` (`main`):
     - `trusted/audit/src/lib.rs`: `compute_verify_prefix_cache_key` (lines
       1630–1674), `build_prefix_cache` (lines 1676–1733),
       `load_or_build_verify_prefix` (lines 1735–1930), `verify_crate_roots`
       (lines 1460–1590).
     - `trusted/audit/TrustedBoundary.lean`: `exprEdges` (lines 480–516),
       `closure` (lines 530–615), `checkCandidate` (lines 770–830),
       `verifyAndCollectLocals` (lines 832–873), `audit` and
       `base.toKernelEnv.replay locals` (lines 900–973).
   - `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core`):
     - `trusted/lean/Trusted/Refinement.lean` (lines 1–490, including
       `Abstracts`, `Compiles`, and `VerificationResult` at lines 458–489).
     - `trusted/lean/Trusted/StepResult.lean` (lines 1–331, including
       `StepResult.externalCall`).
   - `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`):
     - `theory/Anneal/MirSemantics.lean` (lines 1–1458).
     - `theory/Anneal/MirLemmas.lean` (`reachesPrefix_safeAndEnsures_of_step`
       at lines 3510–3565).
     - `theory/Anneal/AsmX86.lean` (`wpX86` and `wpX86_sound_steps` at lines
       1553–1713).
     - `theory/Anneal/MirToX86.lean` (`evalSymInst`, `evalSymBlock`,
       `evalSymBlock_sound`, and `compiles_mir_x86_of_symEq` at lines 369–1482).
2. **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
   `v4.34.1`):**
   - `src/kernel/environment.cpp` (`add_thm` at lines 192–209).
   - `src/kernel/type_checker.cpp` (`reduce_nat` and `reduce_bin_nat_op` at
     lines 101–372; `whnf_core` and `is_def_eq` theorem opacity).
3. **Coq / Rocq (`rocq-prover/rocq@0b9568e12875891c1b9463fa3548f36384ea6f99`)
   and VST (`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`):**
   - `rocq-prover/rocq`: `kernel/declarations.mli` (lines 53–85),
     `kernel/opaqueproof.mli` (lines 14–50), `kernel/constant_typing.ml` (lines
     212–291), `kernel/conv_oracle.mli` (lines 14–60), and
     `theories/Corelib/ssr/ssrbool.v` (lines 18–30, 657–724).
   - `PrincetonUniversity/VST`: `floyd/sc_set_load_store.v` (lines 222–350) and
     `floyd/call_lemmas.v` (lines 37–97, 941–1658).
4. **Iris / RefinedC / RefinedRust:**
   - `iris/refinedc@2e89846baeaa7f65cbe17e3ae7297a8ed5b4feca` (and
     `d057583986651a28047164581f05fbee3a83ed9d`):
     `theories/lithium/definitions.v` (lines 19–332),
     `theories/lithium/interpreter.v` (lines 19–196),
     `theories/typing/type.v` (lines 14–108), and
     `theories/typing/adequacy.v` (lines 15–51).
   - `lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52` (and
     Zenodo `21636474`): `theories/typing/programs.v` (lines 51–123) and
     `theories/typing/function.v` (lines 62–150).
5. **HOL4 (`HOL-Theorem-Prover/HOL@68c9d77e53532cb258e09421952efe3957f40276`),
   HOL Light (`jrh13/hol-light@233b83c3202370e03c54de2bd090e4d34f677e91`), and
   `s2n-bignum` (`awslabs/s2n-bignum@9f2cd960e11892a582e7facb0c191b4a2959ea91`):**
   - `HOL-Theorem-Prover/HOL`: `src/postkernel/TheoryReader.sml` (lines 18–138),
     `src/thm/std-thm.ML` (lines 1115–1135, 1476–1558), `src/thm/Compute.sml`
     (lines 1–90), and `src/num/theories/cv_compute/cv_computeLib.sml` (lines
     1–90).
   - `jrh13/hol-light`: `fusion.ml` (lines 320–569).
   - `awslabs/s2n-bignum`: `common/execution.ml` (lines 1254–1805),
     `arm/proofs/instruction.ml` (lines 727–745), and
     `x86/proofs/bignum_add.ml` (lines 51–164).
6. **Isabelle/HOL `AutoCorres` (`seL4/l4v@12c300e75bb0ca0c82f76496fafacd7e614c0aba`)
   and `Isabelle_LLVM` (`lammich/isabelle_llvm@6be37a9c3cae74a1134dbef2979e312abb5f7f42`):**
   - `seL4/l4v`: `tools/autocorres/AutoCorres.thy` (`ac_corres_chain` at lines
     78–90) and `tools/autocorres/{L1Defs,L2Defs,HeapLift,WordAbstract,TypeStrengthen}.thy`.
7. **Metamath Zero (`digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`) and
   Dedukti (`Deducteam/Dedukti@f3c0eba869ddd46f2e75c123a59f2b612076dba0`):**
   - `digama0/mm0`: `mm0-c/mmb.md` (lines 34–462), `mm0-c/verifier.c`
     (`run_unify` at lines 213–315, `CMD_PROOF_THM` at lines 436–468,
     `parse_until` at lines 625–745), and `examples/separation_logic.mm1`.
   - `Deducteam/Dedukti`: `kernel/typing.ml` (lines 105–410) and
     `kernel/confluence.ml` (lines 23–213).
8. **`MirrorCore` / `RTac`
   (`gmalecha/mirror-core@b962fbca15b0b5a4653f66d29d7115bb04ebd4f3`):**
   - `theories/RTac/Core.v` (`Goal` at lines 62–69, `rtac` at lines 197–199,
     `rtac_spec`, `GoalImplies`, and `rtac_sound` at lines 402–524).

## Revalidation

To revalidate the findings in this report after an upstream change in Anneal,
Lean 4, or one of the compared ITP systems:

1. **Revalidate Anneal's Phase 1 / Phase 2 boundary and `base` vs. `locals`
   split:**
   - Diff `trusted/audit/src/lib.rs` (`verify_crate_roots`,
     `build_prefix_cache`, `load_or_build_verify_prefix`) and
     `trusted/audit/TrustedBoundary.lean` (`verifyAndCollectLocals`, `audit`,
     `base.toKernelEnv.replay locals`) against
     `joshlf/anneal@76fad1a1befa2e4c038d88c3a1bbbe873acb1322`.
   - Run the preserved two-stage boundary auditor and security suite in
     [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md)
     (`bash support/run_two_stage_verification.sh`) to verify that single-import
     Stage-2 auditing and `.thmInfo -> .axiomInfo` compaction remain
     conservative and pass all positive and negative security probes.
2. **Revalidate Lean 4 kernel theorem opacity and `reduce_nat` fast-path
   semantics:**
   - Diff `src/kernel/environment.cpp` (`add_thm`) and
     `src/kernel/type_checker.cpp` (`reduce_nat`, `reduce_bin_nat_op`,
     `whnf_core`, `is_def_eq`) against
     `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
   - Run the preserved 5-stage validator benchmark and 5 negative soundness
     canaries in
     [`lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026`](../lean-4-34-1-kernel-proof-scaling-and-preproved-validator-architectures-2026/REPORT.md)
     (`python3 support/run_unified_benchmark.py`) to confirm that
     `evalCvProg_sound`, `evalIdiomPlan_sound`, `diamond_converge_step`,
     `CalleeSummary`, `loop_summary_sound`, and per-function `ShardCert`
     sharding maintain zero-axiom kernel replay and reject all invalid
     mutations.
3. **Revalidate upstream ITP source coordinates:**
   - Fetch the pinned file revisions listed under [Evidence](#evidence) via
     `gh api repos/<owner>/<repo>/contents/<path>?ref=<commit>` and verify the
     cited symbol definitions and line ranges.
