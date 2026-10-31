<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Behavior Codecs, Progress Refinement, and Optimizer Anti-Degeneracy in Anneal

## Summary

Anneal's trusted refinement core (`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean`) mediates cross-language compilation
(`Compiles`), verification abstraction (`Abstracts`), compiler soundness
(`Compiler.SoundOn`), and target verification (`Compiler.Verified`) over
step-indexed prefix semantics `BehaviorOf M p` (`Query := ExecQuery State`,
`Out := ExecOut Obs Val`). Across
`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and the MIR-to-x86-64
compiler branch `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`, three
structural tensions govern how behavior mappings
`π : L_src.Behavior → L_tgt.Behavior` and `BehaviorCodec L₁ L₂` interact with
multi-step compilation, target hardware encodings, and optimizing passes:

1. **Morphism degeneracy under unconstrained `Monotone π`:** Requiring only
   `Monotone π` in `Compiler.SoundOn` admits four orthogonal classes of
   degenerate morphisms—**(a) top collapse (`π_top`)**, **(b) chaotic defined
   outcome erasure (`π_chaosPure`, `π_chaosVal`)**, **(c) step-zero and
   bounded-fuel query truncation (`π_stepZero`, `π_boundedFuel K`)**, and
   **(d) observation and return-value erasure**—under which UB-free source
   programs compile to faulting, diverging, trace-deleting, or wrong-value
   target programs while satisfying `Compiler.SoundOn` and `Compiler.Verified`.
   Although anchoring a pass pipeline to a target specification
   (`C.π (π_v spec_v) ≤ spec_tgt`) rules out Classes (a), (b), and (d), every
   step-independent partial-correctness specification (`WellFormed`,
   `WellFormedOn`, `EnsuresRetLibInv`) satisfies `π_stepZero spec = spec` and
   `π_boundedFuel K spec = spec` definitionally (`rfl`), leaving target-anchored
   pipelines blind to Class (c) divergence introduction (`loop: jmp loop`) and
   late-UB masking unless step-budget coverage is enforced by the coupling.
2. **Variable-step stuttering and partial outcome decoding in `BehaviorCodec`:**
   `BehaviorCodec L₁ L₂` in `Trusted/Refinement.lean` assumes 1-to-1 query step
   mapping and a total section-retraction pair
   (`∀ o₂, encodeOut (decodeOut o₂) = o₂`) on outcomes. Variable-step
   instruction selection—such as lowering a 1-step MIR `Downcast` to `0` x86-64
   instructions and a 1-step `NicheDecode` to `3` x86-64 instructions—breaks
   1-to-1 step-indexed `Compiles` at intermediate step budgets, and no
   state-independent step projection `stepMap : Nat → Nat` can simultaneously
   validate passes that both compress ($2 \to 1$) and expand ($2 \to 3$) step
   counts. Moving `steps : Nat` inside the semantics constructor
   `EventualBehaviorOf` (`Query := State`, `Out := EventualOut Obs Val`)
   preserves exact all-prefix UB-freedom
   (`eventual_wellFormed_iff_prefix_wellFormed`) with zero `Classical.choice`
   and zero coinduction, strictly rejects infinite-loop codegen, and eliminates
   step-dilation bounds from `BehaviorCodec`. Independently, when a target
   representation type has strictly larger cardinality than the source type
   (such as an 8-bit or 64-bit register holding a 2-valued Rust `bool`), no
   total `(encodeOut, decodeOut)` can satisfy `encode_decode_out`. Generalizing
   `decodeOut` to `L₂.Out → Option L₁.Out` (`PartialBehaviorCodec`) with
   `decode_encode_out` and `encode_of_decode_some` preserves strict functorial
   composition via `Option.bind` and automatically rejects target programs that
   produce invalid bit patterns (`decodeOut o₂ = none`).
3. **Certifying pass anti-degeneracy and instruction deletion under `π_opt`:**
   In `theory/Anneal/Compiler/Peephole.lean`, `optimizePeephole` is unwired in
   `trusted/rustc-capture/src/lib.rs`, omits recursion into `X86Term.call1`
   callees and `requiredConsts`, and acts as the strict identity (`rfl`) on all
   four functions in the `MirLemmas.lean` corpus. Moreover, because
   `PeepholeCompiler` uses `π = id` over step-indexed `BehaviorOf`, no pass
   that deletes or coalesces even a single `.nop` instruction can satisfy
   `Compiles X86Lang X86Lang id s (opt s)`. Replacing `id` with the monotone
   step-rescaling morphism `π_opt` and gating certifying passes with
   `CertifiedOptimizationPass` (combining universal soundness under `π_opt`,
   kernel-`rfl` certificate acceptance on a corpus benchmark, and strict static
   and dynamic step reduction) rejects always-`false` validators (Trap 1),
   identity optimizers (Trap 2), and no-op `optimizePeephole`, while accepting a
   verified instruction-coalescing and constant-folding pass
   (`coalesceAndFoldBody`).

## Applicability

The findings in this report apply to the three subjects recorded in
`REPORT.json`:

1. **Anneal core verification framework** at
   `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
   - `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Monotone`, `Behavior`,
     `Language`, `BehaviorCodec`, `Compiles`, `Abstracts`, `Compiler`,
     `Compiler.SoundOn`, `Compiler.Verified`, `VerificationResultOn`),
   - `trusted/lean/Trusted/StepResult.lean` (`TerminationKind`, `StepResult`,
     `PrefixOutcome`, `ExecQuery`, `ExecOut`, `SmallStepMachine`,
     `ReachesPrefix`, `BehaviorOf`),
   - `trusted/lean/Trusted/MirSemantics.lean` (`MirMachine`, `MirLang`,
     `EnsuresRetLibInv`, `RustcCompiler`), and
   - `theory/Anneal/Refinement.lean` (`pass_trans`, `Compiles.comp`,
     `Abstracts.comp`, `Compiler.SoundOn.verify`, `verify_through_passes`).
2. **Anneal MIR-to-x86-64 compiler branch** at
   `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`:
   - `trusted/lean/Trusted/X86Semantics.lean` (`X86Machine`, `X86Lang`,
     `EnsuresRetLibInv`, `AssemblerCompiler`),
   - `theory/Anneal/Compiler/NaiveCodegen.lean` (`compileStmt`, `compileStage0`,
     `naiveCodec`, `Stage0Compiler`),
   - `theory/Anneal/Compiler/Peephole.lean` (`optimizeInstr`, `optimizeTerm`,
     `optimizeBlock`, `optimizePeephole`, `PeepholeCompiler`), and
   - `theory/Anneal/MirLemmas.lean` (corpus verification over `idCopyBody`,
     `newUncheckedBody`, `makeNonZeroBody`, and `getUncheckedNonZeroBody`).
3. **Lean 4 theorem prover** at
   `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`),
   invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` over standalone
   modules using only `prelude` and `import Init.NotationExtra`.

All counterexamples, impossibility theorems, and replacement structures in this
report are kernel-verified in the preserved package files
[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean),
[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean),
and
[AntiDegeneracyAndCallbackFraming.lean](support/AntiDegeneracyAndCallbackFraming.lean).

## Findings

### 1. Taxonomy of Morphism Degeneracy Under Unconstrained `Monotone π`

`Basis: source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 369–413 at
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`), cross-language refinement judgments
are parameterized by an arbitrary mapping `π : L_src.Behavior → L_tgt.Behavior`:

- `Compiles L_src L_tgt π_c s t` is `L_tgt.sem t ≤ π_c (L_src.sem s)`.
- `Abstracts L_v L_src π_v v s` is `L_src.sem s ≤ π_v (L_v.sem v)`.
- `Compiler.SoundOn C s` is
  `Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)`.
- `Compiler.Verified C s spec` is
  `L_src.sem s ≤ spec ∧ Compiles L_src L_tgt C.π s (C.compile s)` conjoined with
  `L_tgt.sem (C.compile s) ≤ C.π spec`.

Because `Partial B` places `Partial.ub` (`defined := False`) at the top element
$\top$ of the refinement order and `Out → Prop` is ordered by subset inclusion
$\subseteq$ with `fun _ => True` at the top of defined outcome sets,
`Monotone π` leaves three unconstrained degrees of freedom:

1. **Definedness inflation:** `π` can map a defined source behavior (`defined :=
   True`) to `Partial.ub` (`defined := False`), vacating both target safety and
   target outcome refinement.
2. **Outcome-predicate coarsening:** `π` can preserve `defined` while mapping
   `val` to `fun _ => True` (or an existential image under a non-injective
   projection), erasing postconditions, trace observations, return values, or
   `.stuck` distinctions.
3. **Contravariant query distortion:** Even when `π` is restricted to the
   contravariant pullback form (`pullbackMorphism` in
   [MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), lines
   788–800), `monotone_pullbackMorphism` holds unconditionally for *any*
   functions `mapQ : L₂.Query → L₁.Query` and `mapOut : L₂.Out → L₁.Out`. In
   `trusted/lean/Trusted/StepResult.lean` (lines 172–188),
   `BehaviorOf M p ⟨init, 0⟩` admits only the `ReachesPrefix.zero` derivation
   (`outcome = .running`, `trace = []`), so `(BehaviorOf M p ⟨init, 0⟩).defined`
   is unconditionally `True` for every program `p`
   (`behaviorOf_steps_zero_defined`, lines 805–812). Projecting `q.steps` to `0`
   or `min q.steps K` therefore allows `mapQ` to hide source UB or manufacture
   target divergence while preserving `Monotone`.

| Class | Degenerate Morphism | `Monotone`? | Preserves `.defined` on `mapQ q`? | Uses Identity `mapOut = id`? | Pathologies Admitted Under `Compiler.SoundOn` / `Compiler.Verified` | Mechanized Theorems ([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean)) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **(a) Top collapse** | `π_top := fun _ _ => Partial.ub` | Yes (`monotone_π_top`, L666) | No (`defined := False`) | N/A | Compiles UB-free `.good` to `.immediateUb` (`.failed`) and `.stuck`; abstracts `.immediateUb` by `.good`; satisfies `C_top.Verified .good specGood` while target faults at step 1 | `compiles_π_top_trivial` (L672), `abstracts_π_top_trivial` (L677), `counterexample_class_a_masks_target_ub` (L685) |
| **(b) Chaotic defined outcome** | `π_chaosPure := fun _ _ => Partial.pure (fun _ => True)` and `π_chaosVal mapQ` | Yes (`monotone_π_chaosPure`, L712; `monotone_π_chaosVal`, L722) | Yes (`(π_chaosVal id b q).defined ↔ (b q).defined`) | No (`val := fun _ => True`) | Rejects target `.failed`/`.stuck` on `BehaviorOf` (since `out.isSafe` is in `.defined`), but compiles `.good` to `.wrongVal` (`999 ≠ 42`), `.infiniteLoop`, and `.silentReturn` (and to `.stuck` in `RawToyLang`) while satisfying `C_chaos.Verified .good specGood` | `counterexample_class_b_erases_postconditions` (L735), `counterexample_class_b_allows_stuck_when_defined` (L777) |
| **(c) Step-zero / bounded-fuel query distortion** | `π_stepZero := pullbackMorphism (fun q => ⟨q.init, 0⟩) id` and `π_boundedFuel K` | Yes (`monotone_π_stepZero`, L823; `monotone_π_boundedFuel`, L890) | Yes (`(π b q).defined = (b (mapQ q)).defined`) | Yes (`mapOut = id`) | `π_stepZero` maps `.immediateUb` to a `WellFormed` behavior and compiles both `.good` and `.immediateUb` to `.infiniteLoop` (`loop: jmp loop`) while satisfying `C_zero.Verified .good specGood`; `π_boundedFuel 1` masks step-2 UB in `.lateUb` and compiles `.good` to `.loopAfter1` | `behaviorOf_steps_zero_defined` (L805), `counterexample_class_c_stepZero_diverges_and_masks_ub` (L830), `counterexample_class_c_boundedFuel_masks_late_ub_and_divergence` (L902) |
| **(d) Observation & return-value erasure** | `covariantMorphism eraseTraceProj`, `covariantMorphism collapseValProj`, `pullbackMorphism id spoofOutContra` | Yes (`monotone_covariantMorphism`, L1055; `monotone_pullbackMorphism`, L794) | Yes (`mapQ = id`) | No (non-injective `proj` / `mapOut`) | Compiles `.good` (trace `[10]`, return `42`) to `.silentReturn` (trace `[]`, deleting volatile I/O) or `.wrongVal` (return `999`) while satisfying `C.Verified .good specGood` | `counterexample_class_d_erases_observations_and_values` (L1097) |

### 2. Target Specification Anchoring vs. Step-Independent Blindness

`Basis: source + execution + derived`

In `theory/Anneal/Refinement.lean` (lines 269–286 at
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`), `verify_through_passes` combines an
upward abstraction pass `Abstracts L_v L_src π_v v s` with a downward
compilation pass `C.SoundOn s` to conclude `C.Verified s (π_v spec)`. Because
`L_tgt.sem (C.compile s) ≤ C.π (π_v spec)` evaluates the specification through
the composed morphism `C.π ∘ π_v`, an unanchored pass pipeline is vulnerable to
degeneracy in either `π_v` or `C.π`
([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), Section 4,
lines 1675–1788):

- **Unanchored pipeline vulnerability
  (`verify_through_passes_unanchored_vulnerable`, L1680):** Even when the
  compiler is the exact identity `C_id := { compile := id, π := id }`, choosing
  `π_v := π_top ToyLang ToyLang` allows `verify_through_passes` to prove
  `C_id.Verified .immediateUb (π_top ToyLang ToyLang specGood)` from
  `progGood_satisfies_specGood`, even though `.immediateUb` faults at step 1
  (`¬ (ToyLang.sem .immediateUb ≤ ToyLang.WellFormed)`).
- **Target-anchored pipeline (`verify_through_passes_anchored`, L1699, and
  `target_anchor_rejects_degenerate_classes`, L1722):** Adding an explicit
  target-anchor obligation `h_anchor : C.π (π_v spec_v) ≤ spec_tgt` yields
  `L_tgt.sem (C.compile s) ≤ spec_tgt` directly in `L_tgt.Behavior`. When
  `spec_tgt` is defined (`specGood`) and constrains traces and return values,
  `C.π specGood ≤ specGood` is provably false (`¬ (π specGood ≤ specGood)`) for
  Class (a) (`π_top`), Class (b) (`π_chaosVal id`), and Class (d)
  (`covariantMorphism collapseValProj`). When `spec_tgt` is step-sensitive
  (`specTerminatesAt2`, requiring
  `q.steps = 2 → out.outcome = .terminated (.normal 42)`), it also rejects
  `π_stepZero`.
- **Why step-independent target anchors are blind to Class (c)
  (`stepIndependent_target_anchor_blind_to_class_c`, L1769):** Every canonical
  specification in Anneal (`Language.WellFormed`, `Language.WellFormedOn pre`,
  `EnsuresRetLibInv`, and `specGood`) is **step-independent**: its precondition
  `pre q` and postcondition `post q out` inspect `q.init` and `out`, but not
  `q.steps`. Pulling back any step-independent specification `spec` along
  `q ↦ ⟨q.init, 0⟩` or `q ↦ ⟨q.init, capSteps q.steps K⟩` leaves `spec`
  **definitionally unchanged**:
  $$\pi_{\text{stepZero}}(\text{specGood}) = \text{specGood} \quad (\text{by }\texttt{rfl}), \qquad \pi_{\text{boundedFuel } K}(\text{specGood}) = \text{specGood} \quad (\text{by }\texttt{rfl}).$$
  Consequently, the degenerate compiler
  `C_zero := { compile := fun _ => .infiniteLoop, π := π_stepZero }` that
  compiles every source program to `loop: jmp loop` simultaneously satisfies:
  1. `C_zero.SoundOn .good`,
  2. `C_zero.Verified .good specGood`, and
  3. the target-anchoring inequality `C_zero.π specGood ≤ specGood` (by
     `Preorder.le_refl specGood`).

  In partial correctness (`SpecOn`), `.infiniteLoop` never reaches `.failed`,
  `.stuck`, or `.terminated`, so it vacuously satisfies `specGood` at every step
  budget. The only obligation that prevents `.good` from compiling to
  `.infiniteLoop` is the operational simulation
  `Compiles ToyLang ToyLang C.π .good .infiniteLoop`, which `π_stepZero`
  defeats by querying `.good` exclusively at `steps = 0` where `.good` is still
  `.running`. Target specification anchoring therefore cannot substitute for
  step-budget coverage in the compiler morphism.

### 3. Admissible Simulation Couplings and Total Lockstep `BehaviorCodec`

`Basis: source + execution + derived`

In [MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) (Sections
4–6, lines 1303–2945), two composable structures eliminate all four degeneracy
classes **(a)–(d)**:

#### 3.1 Total `BehaviorCodec L₁ L₂` (1-to-1 Lockstep Retraction-Section Codec)

`BehaviorCodec L₁ L₂`
([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), lines
2719–2726; matching `trusted/lean/Trusted/Refinement.lean`, lines 155–169 at
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`) pairs:

1. **Query retraction (`encodeQuery : L₁.Query → L₂.Query`,
   `decodeQuery : L₂.Query → L₁.Query`):**
   `decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁`. This forces
   `decodeQuery` to be **surjective** onto `L₁.Query`
   (`BehaviorCodec.decodeQuery_surjective`, L2729), ruling out Class (c) step
   truncation while allowing `L₂.Query` to carry additional target-only state.
2. **Outcome section (`decodeOut : L₂.Out → L₁.Out`,
   `encodeOut : L₁.Out → L₂.Out`):**
   `encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂` (together with
   `decode_encode_out` in `Trusted/Refinement.lean`). This forces `decodeOut` to
   be **injective** on `L₂.Out` (`BehaviorCodec.decodeOut_injective`, L2736),
   ruling out Class (d) trace, value, and outcome conflation.
3. **Pullback morphism (`BehaviorCodec.toMorphism`, L2746):**
   `c.toMorphism := pullbackMorphism c.decodeQuery c.decodeOut`.

Kernel-verified properties in
[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) establish that
`BehaviorCodec`:

- is unconditionally `Monotone` (`BehaviorCodec.monotone_toMorphism`, L2751),
- preserves `.defined` bi-directionally at every `q₂`
  (`BehaviorCodec.toMorphism_defined_iff`, L2757, ruling out Class (a)) and
  recovers `(b q₁)` exactly at `c.encodeQuery q₁`
  (`BehaviorCodec.toMorphism_encodeQuery`, L2772, and
  `BehaviorCodec.toMorphism_encodeQuery_val_iff`, L2781, ruling out Class (b)),
- is closed under `BehaviorCodec.id` (L2794) and `BehaviorCodec.comp` (L2807)
  with **strict definitional functoriality (`rfl`)**:
  `(BehaviorCodec.id L).toMorphism b = b` (`id_toMorphism`, L2802) and
  `(c₁₂.comp c₂₃).toMorphism b = c₂₃.toMorphism (c₁₂.toMorphism b)`
  (`comp_toMorphism`, L2821), and
- **bi-directionally preserves both termination and non-termination** on
  deterministic source / total target machines
  (`BehaviorCodec.compiles_bidirectional_outcome`, L2832): when `s` has unique
  outcome `o₁` at `q₁` and `t` is total at `c.encodeQuery q₁`,
  `Compiles L₁ L₂ c.toMorphism s t` forces every target outcome `o₂` at
  `c.encodeQuery q₁` to satisfy `c.decodeOut o₂ = o₁` and `o₂ = c.encodeOut o₁`.

#### 3.2 `ExecSimCoupling` and `AdmissibleExecCoupling` ($1 \to k$ Multi-Step)

For multi-step passes where 1 source step lowers to $k \ge 2$ target steps
over step-indexed `ExecQuery State`, a single-valued query pullback
`decodeQuery : L₂.Query → L₁.Query` is insufficient: at an intermediate target
micro-step $n_2 = k \cdot m + r$ ($0 < r < k$), the target's `.running` outcome
corresponds to completed source step $\lfloor n_2 / k \rfloor = m$, whereas a
mid-instruction target fault (`.failed`) must be gated by source safety at
started source step $\lceil n_2 / k \rceil = m + 1$.

`ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂`
([MorphismAdmissibility.lean](support/MorphismAdmissibility.lean), lines
1341–1380) couples step budgets via a relation
`stepCoupling : Nat → Nat → Prop` and induces `C.toMorphism` via dual
universal/existential quantification:

```lean
def ExecSimCoupling.toMorphism
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (b : Behavior (ExecQuery State₁) (ExecOut Obs₁ Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Obs₂ Val₂) :=
  fun q₂ => {
    defined :=
      ∀ n₁, C.stepCoupling q₂.steps n₁ →
        (b ⟨C.decompileInit q₂.init, n₁⟩).defined
    val := fun h out₂ =>
      ∃ n₁, ∃ (hn₁ : C.stepCoupling q₂.steps n₁),
        (b ⟨C.decompileInit q₂.init, n₁⟩).val (h n₁ hn₁) (C.decompileOut out₂)
  }
```

where `C.decompileOut` maps `⟨tr₂, outc₂⟩` to
`⟨C.decompileTrace tr₂, outc₂.map C.decompileVal⟩`, preserving `.running`,
`.terminated (.normal _)`, `.terminated .unwind`, `.failed`, and `.stuck`
constructors 1-to-1 (`PrefixOutcome.map`, L1316). `AdmissibleExecCoupling C`
(lines 1402–1423) requires four conditions:

1. `step_nonempty : ∀ n₂, ∃ n₁, C.stepCoupling n₂ n₁`,
2. `step_coverage : ∀ n₁, ∃ n₂, C.stepCoupling n₂ n₁` conjoined with uniqueness
   `∀ n₁', C.stepCoupling n₂ n₁' → n₁' = n₁`,
3. `trace_injective` on `C.decompileTrace`, and
4. `val_injective` on `C.decompileVal`.

Sections 4–6 of
[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) prove that
`AdmissibleExecCoupling`:

- is constructively `Monotone` (`ExecSimCoupling.monotone_toMorphism`, L1375),
  maps `SpecOn` to `SpecOn` (`toMorphism_specOn_le`, L1438), and satisfies
  `C.toMorphism L₁.WellFormed ≤ L₂.WellFormed` (`toMorphism_wellFormed_le`,
  L1471);
- rules out Class (a) (`admissible_rules_out_class_a_target_ub_and_stuck`,
  L1482; `π_top_not_admissible`, L1498), Class (b) (`π_chaosVal_not_admissible`,
  L1509), Class (c) (`stepZero_not_step_coverage`, L1528;
  `boundedFuel_not_step_coverage`, L1543;
  `admissible_rules_out_class_c_late_ub_and_divergence`, L1560), and Class (d)
  (`admissible_rules_out_class_d_trace_and_val_erasure`, L1619);
- is closed under identity (`AdmissibleExecCoupling.id`, L1802) and composition
  (`AdmissibleExecCoupling.comp`, L1867; `Compiles.comp_coupling`, L1972;
  `Abstracts.comp_coupling`, L1988); and
- verifies a concrete $1 \to 2$ multi-step lowering
  `MirMultiLang → X86MultiLang` (`compileMirToX86_compiles`, L2350) using
  `stepCoupling n₂ n₁ := n₁ = div2 n₂ ∨ n₁ = ceil2 n₂`
  (`admissible_mirToX86Coupling`, L2153), where single-valued floor pullback
  alone fails on `.failNow` at `n₂ = 1` (`not_compiles_floor_only_failNow`,
  L2409) and single-valued ceiling pullback alone fails on `.incAndRet` at
  `n₂ = 1` (`not_compiles_ceil_only_incAndRet`, L2430), and composes end-to-end
  with an upward functional abstraction `FuncLang → MirMultiLang`
  (`endToEnd_func_mir_x86_verified`, L2667).

### 4. Variable-Step Stuttering and Eventual Semantics (`EventualBehaviorOf`)

`Basis: source + execution + derived`

In `theory/Anneal/Compiler/NaiveCodegen.lean` (lines 148–153 and 264–288 at
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`), `compileStmt` maps each MIR
statement to a single x86-64 instruction (`k = 1`), allowing `naiveCodec` to
copy the step budget unchanged (`steps := q.steps`). Realistic instruction
selection violates 1-to-1 step lockstep whenever some MIR statements lower to
`k = 0` instructions (e.g., `PlaceElem::Downcast`, `StorageLive`, `Nop`) and
others lower to `k ≥ 2` instructions (e.g., niche discriminant decoding or
compound `Rvalue` trees).

In
[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean)
(Section 2, lines 278–757), `s_var = [.downcast, .nicheDecodeRet]` models a
2-statement MIR program where statement 0 (`downcast`) takes 1 source step and
emits `0` target instructions (`[]`), and statement 1 (`nicheDecodeRet`) takes 1
source step and emits `3` target instructions
(`[.incAcc, .incAcc, .incAccRet]`):

| Step budget `steps` | Source `s_var` outcome (`VarMirMachine`) | Target `t_var` outcome (`VarX86Machine`) | Match under 1-to-1 `lockstepCodec`? |
| :--- | :--- | :--- | :--- |
| `0` | `.incomplete` | `.incomplete` | Yes |
| `1` | `.incomplete` | `.incomplete` | Yes |
| `2` | `.terminated (.normal (acc + 3))` | `.incomplete` | **No** (`t_var` is `.incomplete`, `s_var` has terminated) |
| `n + 3` | `.terminated (.normal (acc + 3))` | `.terminated (.normal (acc + 3))` | Yes |

This yields two mechanized impossibility results:

1. **Failure of 1-to-1 `lockstepCodec` (`lockstep_codec_fails_on_s_var`,
   L638):** At `q₂ = ⟨⟨0, 0⟩, 2⟩`, `t_var` produces `PrefixOutcome.incomplete`
   while `s_var` at `steps = 2` produces only `.terminated (.normal 3)`,
   refuting `Compiles` under `lockstepCodec.toMorphism`.
2. **Impossibility of any state-independent query step projection
   (`no_state_independent_step_map_for_variable_lowering`, L676):** Consider
   `s_fast = [.downcast, .retNow]`, which terminates in `2` source steps while
   `t_fast = compileVarProg s_fast = [.retNow]` terminates in `1` target step.
   Validating `s_fast → t_fast` at target budget `steps = 1` requires `s_fast`
   to have terminated at `stepMap 1`, forcing `stepMap 1 ≥ 2`; validating
   `s_var → t_var` at target budget `steps = 1` requires `s_var` to still be
   `.incomplete` at `stepMap 1`, forcing `stepMap 1 < 2`. Thus no
   state-independent function `stepMap : Nat → Nat` can serve as a pass-level
   `BehaviorCodec` for variable-step lowering.

Sections 3 and 4 of
[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean)
(lines 758–1297) mechanize and compare two 100% constructive
(`0 Classical.choice`, `0 coinduction`) replacements:

- **Architecture A — Bounded-Dilation `ExecQuery` Codec (`DilationCodec`,
  lines 767–1031):** Retains `Query := ExecQuery State` and equips the codec
  with a monotone, unbounded step-dilation window `[srcFloor n, srcCeil n]`
  (`floor_unbounded : ∀ M, ∃ N, ∀ n, N ≤ n → M ≤ srcFloor n`). While
  `DilationCodec` is monotone (`DilationCodec.monotone_toMorphism`, L803),
  rejects `loopX86Prog` (`dilationCodec_rejects_loopCodegen`, L932), and
  verifies `s_var → t_var` with `srcFloor n := n / 3` and `srcCeil n := n + 1`
  (`dilationCodec_verifies_s_var`, L970), it adds 6 step-dilation fields to
  `BehaviorCodec`, cannot express runtime data-dependent step ratios, and
  composes only laxly (`DilationCodec.comp_toMorphism_le`, L860:
  `c₂.toMorphism (c₁.toMorphism b) ≤ (c₂.comp c₁).toMorphism b`).
- **Architecture B — Step-Decoupled Eventual-Outcome Semantics
  (`EventualBehaviorOf`, lines 1050–1297):** Keeps `ReachesPrefix` inductive
  while moving the operational fuel coordinate `steps : Nat` inside the
  semantics constructor `EventualBehaviorOf` (`Query := State`,
  `Out := EventualOut Obs Val`):
  ```lean
  inductive EventualOut (Obs Val : Type) where
    | terminated (trace : List Obs) (term : TerminationKind Val)
    | diverges

  def EventualBehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
      State → Partial (EventualOut Obs Val → Prop) :=
    fun init => {
      defined :=
        M.initState p init →
          ∀ (n : Nat) (tr : List Obs) (out : PrefixOutcome Val),
            ReachesPrefix M p n init tr out →
            out.isSafe
      val := fun _ ev =>
        M.initState p init ∧
        match ev with
        | .terminated tr term =>
          ∃ (n : Nat), ReachesPrefix M p n init tr (.terminated term)
        | .diverges =>
          ∀ (n : Nat), ∃ (tr : List Obs),
            ReachesPrefix M p n init tr .incomplete
    }
  ```
  `EventualBehaviorOf` requires zero `Classical.choice`
  (`exists_nat_no_choice_canary`, L1050), is propositionally equivalent (with
  **zero axioms**) to all-prefix safety under `BehaviorOf`
  (`eventual_wellFormed_iff_prefix_wellFormed`, L1098), strictly rejects
  `loopX86Prog` (`eventual_rejects_loopCodegen`, L1164), and verifies both
  `s_var → t_var` (`eventual_verifies_s_var`, L1196) and `s_fast → t_fast`
  (`eventual_verifies_s_fast`, L1247) under the **exact same** step-free
  identity codec `eventualVarCodec` (L1150).

| Criterion | Step-Indexed `BehaviorOf` + `TotalBehaviorCodec` | Architecture A (`DilationCodec`) | Architecture B (`EventualBehaviorOf` + `PartialBehaviorCodec`) |
| :--- | :--- | :--- | :--- |
| Constructive (`0 Classical.choice`, `0 coinduction`)? | Yes | Yes | **Yes** |
| All-prefix UB-freedom preserved? | Yes | Yes (within window) | **Yes** (`eventual_wellFormed_iff_prefix_wellFormed`, 0 axioms) |
| Rejects `loopCodegen` (`bb0: jmp bb0`)? | Yes | Yes (`dilationCodec_rejects_loopCodegen`) | **Yes** (`eventual_rejects_loopCodegen`) |
| Handles fixed variable-step passes ($k = 0, 3$)? | **No** (`lockstep_codec_fails_on_s_var`) | Yes (`dilationCodec_verifies_s_var`) | **Yes** (`eventual_verifies_s_var`) |
| Handles unbounded / data-dependent step ratios? | No | **No** (bounds depend only on `n`) | **Yes** (`∃ n` in `.terminated`) |
| Extra fields required in `BehaviorCodec` | 0 (7 fields total) | +6 fields (`srcFloor`, `srcCeil`, 4 laws) | **0** (7 fields total) |
| Functorial composition of `.toMorphism` | Strict (`=`) | Lax (`≤` only) | **Strict (`=`)** |

### 5. Non-Surjectivity Obstruction and `PartialBehaviorCodec`

`Basis: source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 155–169), `BehaviorCodec`
requires `encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂`, which forces
`encodeOut : L₁.Out → L₂.Out` to be **surjective** onto `L₂.Out`. Whenever the
target outcome carrier has strictly greater cardinality than the source outcome
carrier—such as an 8-bit or 64-bit x86-64 register (`UInt8`, `UInt64`, or `Nat`)
holding a 2-valued Rust `bool` where `0` encodes `false`, `1` encodes `true`,
and `2..255` are invalid bit patterns—no total section-retraction pair can
exist
([BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean),
Section 5, lines 1298–1802):

- **Impossibility of total section-retraction
  (`no_total_section_for_bool_in_uint8`, L1311, and
  `no_total_section_for_bool_in_nat`, L1349):** No total functions
  `encodeOut : Bool → UInt8` (or `Nat`) and `decodeOut : UInt8 → Bool` (or
  `Nat → Bool`) can satisfy `∀ o₂, encodeOut (decodeOut o₂) = o₂`. Furthermore,
  dropping `encode_decode_out` while keeping `decodeOut` total (e.g., mapping
  `2 ↦ true`) unsoundly accepts a buggy target program that outputs `al = 2` for
  a `bool`.
- **Partial outcome decoding (`PartialBehaviorCodec`, lines 1384–1404):**
  Replacing `decodeOut : L₂.Out → L₁.Out` with
  `decodeOut : L₂.Out → Option L₁.Out` governed by
  `decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁` and
  `encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
  strictly generalizes `TotalBehaviorCodec`
  (`TotalBehaviorCodec.toPartialCodec`, L1407) with the same 7-field footprint:
  ```lean
  structure PartialBehaviorCodec (L₁ L₂ : Language) where
    encodeQuery : L₁.Query → L₂.Query
    decodeQuery : L₂.Query → L₁.Query
    decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
    encodeOut : L₁.Out → L₂.Out
    decodeOut : L₂.Out → Option L₁.Out
    decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
    encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂

  def PartialBehaviorCodec.toMorphism {L₁ L₂ : Language}
      (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
    fun q₂ =>
      let p := b (c.decodeQuery q₂)
      { defined := p.defined
        val := fun h o₂ => ∃ o₁, c.decodeOut o₂ = some o₁ ∧ p.val h o₁ }
  ```
- **Kernel-verified properties of `PartialBehaviorCodec` (lines 1421–1802):**
  1. *Bi-directional injectivity:* `c.encodeOut` is injective
     (`encodeOut_injective`, L1421) and `c.decodeOut` is injective on `some`
     (`decodeOut_injective_on_some`, L1433), preventing distinct target bit
     patterns `o₂ ≠ o₂'` from decoding to the same `some o₁`.
  2. *Automatic rejection of invalid target bit patterns:* Whenever
     `c.decodeOut o₂ = none`, `¬ (c.toMorphism b q₂).val h o₂`
     (`invalid_target_out_rejected`, L1447), and any target program `t` that can
     emit `o₂` at a defined query is automatically rejected by `Compiles`
     (`compiles_rejects_invalid_target_out`, L1460).
  3. *Monotonicity, definedness preservation, and exact recovery:*
     `monotone_toMorphism` (L1474), `toMorphism_defined` (L1485),
     `toMorphism_encodeQuery_defined` (L1493), and `toMorphism_val_encodeOut`
     (L1502).
  4. *Identity and strict functorial composition via `Option.bind`:*
     `PartialBehaviorCodec.id` (L1517), `PartialBehaviorCodec.comp` (L1530),
     `comp_toMorphism_iff` (L1556, 0 axioms), `id_toMorphism` (L1583), and
     `comp_toMorphism` (L1596).
  5. *Concrete `MirAbiVal ↔ X86RawVal` instantiation:* `mirToX86AbiCodec`
     (L1760) verifies valid boolean negation (`0 ↔ 1`,
     `valid_bool_negation_compiles`, L1773) and automatically rejects a corrupt
     target implementation returning `.boolWord 2`
     (`corrupt_bool_bitpattern_2_rejected`, L1793).

### 6. Certifying Pass Anti-Degeneracy and `CertifiedOptimizationPass`

`Basis: source + execution + derived`

Auditing `theory/Anneal/Compiler/Peephole.lean` (lines 45–205 at
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`) alongside
`theory/Anneal/MirLemmas.lean` (lines 380–755) and
`trusted/rustc-capture/src/lib.rs` (lines 1166–1340), and mechanizing the pass
in
[AntiDegeneracyAndCallbackFraming.lean](support/AntiDegeneracyAndCallbackFraming.lean)
(Section 3, lines 708–1565), reveals four findings:

1. **`Peephole.lean` is unwired, shallow on call trees, and a complete no-op on
   the `MirLemmas.lean` corpus (`peephole_noop_on_corpus`, L867):**
   - `optimizePeephole`, `PeepholeCompiler`, and `compileOptimized` are never
     referenced outside `Peephole.lean`; `rustc-capture` and `MirLemmas.lean`
     verify unoptimized Stage 0 `X86Body` values directly.
   - `optimizePeephole` maps `optimizeBlock` over `body.blocks`
     (`Peephole.lean`, line 66) but leaves `body.requiredConsts` and the
     `callee : X86Body` inside `X86Term.call1` (line 59) unoptimized; the
     step-commutation proof `evalX86Step_optimizePeephole` (line 115) relies on
     this omission so that `evalX86Step` inside `s.curBody = some callee`
     commutes by `rfl`.
   - Because unoptimized `rustc -Z mir-opt-level=0` MIR materializes operands
     into stack slots before binary operations or conditional branches,
     `optimizeInstr` (which matches only `.alu op dst (.imm v1) (.imm v2)`) and
     `optimizeTerm` (which matches only `.jccBool (.imm (.boolVal b)) ...`)
     never fire on Stage 0 output. On all four corpus functions in
     `MirLemmas.lean` (`idCopyBody`, `newUncheckedBody`, `makeNonZeroBody`, and
     `getUncheckedNonZeroBody`), `optimizePeephole body = body` holds by `rfl`
     (`peephole_noop_on_corpus`, L867).
2. **Vacuous translation validators (Trap 1) and identity optimizers (Trap 2):**
   In `runValidatedPass` (`if checkCert s t cert then t else s`, L739), the
   trivial validator `alwaysFalseCertifier := fun _ _ _ => false` satisfies
   `Compiles X86Lang X86Lang id s` on
   `runValidatedPass alwaysFalseCertifier s t cert` for every `s`, `t`, and
   `cert` via a 1-line `Preorder.le_refl` proof (`trap1_alwaysFalse_compiles`,
   L753) while rejecting 100% of optimizations
   (`trap1_alwaysFalse_never_accepts`, L760). Likewise, `idOptimizer s := s`
   satisfies `Compiles X86Lang X86Lang id s (idOptimizer s)` by
   `Preorder.le_refl` (`trap2_id_compiles`, L777).
3. **Why `Compiles X86Lang X86Lang id` forbids instruction deletion
   (`compiles_id_forbids_instruction_deletion`, L916):**
   In `BehaviorOf M p (q : ExecQuery State)`, every `ReachesPrefix.step`
   transition increments `q.steps` by `1` and prepends `()` to
   `out.trace : List Unit`. Under `PeepholeCompiler`'s identity behavior
   morphism `π = id` (`Peephole.lean`, line 179),
   `Compiles X86Lang X86Lang id s t` requires `t` to match `s` at the exact same
   step count `q.steps` and trace length `out.trace.length`. Consequently,
   deleting a single `.nop` instruction from the 2-instruction function
   `nopConstBody` (`.nop; .mov _0 42; .ret`, terminating at step 3) to produce
   `elimNopConstBody` (`.mov _0 42; .ret`, terminating at step 2) is **provably
   rejected** by `Compiles X86Lang X86Lang id`
   (`¬ Compiles X86Lang X86Lang (fun b => b) nopConstBody elimNopConstBody`,
   L916).
4. **Step-rescaling morphism `π_opt` and the `CertifiedOptimizationPass`
   contract (lines 991–1565):**
   Defining the step-rescaling morphism
   `π_opt : X86Lang.Behavior → X86Lang.Behavior` (L991):
   ```lean
   def π_opt (b : X86Lang.Behavior) : X86Lang.Behavior :=
     fun q => {
       defined := ∀ steps_src, (b { init := q.init, steps := steps_src }).defined
       val := fun hDef out =>
         ∃ steps_src tr_src,
           (b { init := q.init, steps := steps_src }).val (hDef steps_src)
             { trace := tr_src, outcome := out.outcome }
     }
   ```
   preserves monotonicity (`monotone_π_opt`, L1000), `WellFormedOn`
   (`π_opt_preserves_wellFormedOn`, L1015), and `EnsuresRetLibInv`
   (`π_opt_preserves_ensuresRetLibInv`, L1025). Pairing `π_opt` with
   `CertifiedOptimizationPass` (L1101)—which conjoins universal soundness of
   `runValidatedPass` under `π_opt`, constructive non-vacuity
   (`checkCert s_bench (pass s_bench) (genCert s_bench) = true`), strict static
   cost reduction (`staticCost (pass s_bench) < staticCost s_bench`), and strict
   dynamic step reduction (`steps_opt < steps_src` with
   `TerminatesInMinSteps`)—provably rejects `alwaysFalseCertifier`
   (`trap1_rejected_by_contract`, L1131), `idOptimizer`
   (`trap2_id_rejected_by_contract`, L1142), and `optimizePeephole` on
   `newUncheckedBody` (`peephole_on_newUnchecked_rejected`, L1154), while
   accepting the move/wrap-coalescing and constant-folding pass
   `coalesceAndFoldBody` (`genuineCoalescePass_certified`, L1540), which reduces
   `newUncheckedBody` from `staticCost = 7` (5 dynamic steps) to
   `staticCost = 3` (2 dynamic steps).

## Boundaries

- **Non-deterministic target machines with empty outcome sets (`known not to
  apply` without totality):** Under demonic-choice refinement
  (`L_tgt.sem t ≤ π (L_src.sem s)`), an empty target outcome predicate
  (`val := fun _ => False`) refines any defined source behavior. In
  `BehaviorOf M p`, empty outcome sets arise only at invalid initial states
  (`¬ M.initState p q.init`); from any valid initial state, a total machine has
  at least one reachable prefix outcome at every step budget `n` (an explicit
  hypothesis in `BehaviorCodec.compiles_bidirectional_outcome`,
  [MorphismAdmissibility.lean](support/MorphismAdmissibility.lean) L2832).
- **Silent vs. observable transitions in `StepResult` (`known not to apply` to
  non-Unit I/O traces without trace projection):** Because
  `StepResult.step obs next` always appends `obs` to `trace : List Obs` and both
  `MirMachine` and `X86Machine` instantiate `Obs := Unit`, `out.trace` is a
  unary step counter (`List.replicate k ()`). Any variable-step lowering or
  instruction-deleting optimization must either treat `Unit` ticks as silent (as
  in `SilentEventualBehaviorOf` and `π_opt`) or emit `.choice` for internal
  micro-steps while reserving `Obs` for external I/O observations.
- **Infinite reactive I/O streams under `EventualOut.diverges`
  (`not examined`):** `EventualOut Obs Val` records the finite observation trace
  `trace : List Obs` upon termination (`.terminated trace term`) and classifies
  non-terminating executions via `.diverges`
  (`∀ n, ∃ tr, ReachesPrefix M p n init tr .incomplete`). Distinguishing two
  intentionally non-terminating reactive loops by their infinite I/O trace
  prefixes was not examined because Anneal specifies Rust functions at
  call/return boundaries.
- **Unanchored `π_opt` and termination preservation (`known not to apply`
  without `EventualBehaviorOf` or `TerminatesInMinSteps`):** Because `π_opt`
  existentially quantifies `∃ steps_src` over step-indexed `BehaviorOf` where
  every program has an `.incomplete`/`.running` prefix at `steps_src = 0`,
  `π_opt` preserves safety (`WellFormedOn`) and partial-correctness
  postconditions (`EnsuresRetLibInv`) but relies on `TerminatesInMinSteps` in
  `CertifiedOptimizationPass` (or `EventualBehaviorOf` in Architecture B, where
  `.diverges` is disjoint from `.terminated`) to prevent an optimizer from
  replacing a terminating block with an infinite loop.

## Evidence

### Preserved Mechanized Lean 4 Support Artifacts

All three standalone Lean 4 modules in `support/` were verified with Lean 4
`v4.34.1` (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) on `2026-10-31`
with exit code `0`, zero warnings, zero `sorryAx`, zero `Lean.ofReduceBool`, and
zero `Classical.choice`:

1. **[MorphismAdmissibility.lean](support/MorphismAdmissibility.lean)**
   - **Lines:** `2982`
   - **SHA-256:**
     `6d9a6f0a68163d8751a4623f3b38cf084eaa13ee233bdc14096257625372c846`
   - **Key mechanized declarations and theorems (all 30 `#print axioms` checks
     report `does not depend on any axioms`):**
     - Class (a)–(d) counterexamples: `counterexample_class_a_masks_target_ub`
       (L685), `counterexample_class_b_erases_postconditions` (L735),
       `counterexample_class_b_allows_stuck_when_defined` (L777),
       `behaviorOf_steps_zero_defined` (L805),
       `counterexample_class_c_stepZero_diverges_and_masks_ub` (L830),
       `counterexample_class_c_boundedFuel_masks_late_ub_and_divergence` (L902),
       `counterexample_class_d_erases_observations_and_values` (L1097).
     - Pipeline anchoring and Class (c) step-independence blindness:
       `verify_through_passes_unanchored_vulnerable` (L1680),
       `verify_through_passes_anchored` (L1699),
       `target_anchor_rejects_degenerate_classes` (L1722),
       `stepIndependent_target_anchor_blind_to_class_c` (L1769).
     - `ExecSimCoupling` and `AdmissibleExecCoupling`: `ExecSimCoupling`
       (L1341), `AdmissibleExecCoupling` (L1402),
       `admissible_rules_out_class_a_target_ub_and_stuck` (L1482),
       `admissible_rules_out_class_c_late_ub_and_divergence` (L1560),
       `admissible_rules_out_class_d_trace_and_val_erasure` (L1619),
       `AdmissibleExecCoupling.id` (L1802), `AdmissibleExecCoupling.comp`
       (L1867), `compileMirToX86_compiles` (L2350),
       `not_compiles_floor_only_failNow` (L2409),
       `not_compiles_ceil_only_incAndRet` (L2430),
       `endToEnd_func_mir_x86_verified` (L2667).
     - Lockstep `BehaviorCodec`: `BehaviorCodec` (L2719),
       `BehaviorCodec.decodeQuery_surjective` (L2729),
       `BehaviorCodec.decodeOut_injective` (L2736),
       `BehaviorCodec.id_toMorphism` (L2802), `BehaviorCodec.comp_toMorphism`
       (L2821), `BehaviorCodec.compiles_bidirectional_outcome` (L2832),
       `SmallStepCodec.admissible_toExecSimCoupling` (L2927).

2. **[BehaviorCodecExpressiveness.lean](support/BehaviorCodecExpressiveness.lean)**
   - **Lines:** `1837`
   - **SHA-256:**
     `bcdb2643cd16b6e22f202f95b757aa7b4dfd7236f7978b22b451297dfd23bc83`
   - **Key mechanized declarations and theorems (zero `Classical.choice`, zero
     `sorryAx`):**
     - Variable-step impossibility on step-indexed `BehaviorCodec`:
       `s_var_vs_t_var_step_mismatch` (L584), `lockstep_codec_fails_on_s_var`
       (L638), `no_state_independent_step_map_for_variable_lowering` (L676).
     - Architecture A (`DilationCodec`): `DilationCodec` (L767),
       `DilationCodec.monotone_toMorphism` (L803),
       `DilationCodec.comp_toMorphism_le` (L860),
       `dilationCodec_rejects_loopCodegen` (L932),
       `dilationCodec_verifies_s_var` (L970).
     - Architecture B (`EventualBehaviorOf`): `exists_nat_no_choice_canary`
       (L1050), `EventualOut` (L1059), `EventualBehaviorOf` (L1066),
       `eventual_wellFormed_iff_prefix_wellFormed` (L1098),
       `eventual_rejects_loopCodegen` (L1164), `eventual_verifies_s_var`
       (L1196), `eventual_verifies_s_fast` (L1247).
     - Non-surjectivity obstruction and `PartialBehaviorCodec`:
       `no_total_section_for_bool_in_uint8` (L1311),
       `no_total_section_for_bool_in_nat` (L1349), `PartialBehaviorCodec`
       (L1384), `PartialBehaviorCodec.encodeOut_injective` (L1421),
       `PartialBehaviorCodec.decodeOut_injective_on_some` (L1433),
       `PartialBehaviorCodec.invalid_target_out_rejected` (L1447),
       `PartialBehaviorCodec.compiles_rejects_invalid_target_out` (L1460),
       `PartialBehaviorCodec.monotone_toMorphism` (L1474),
       `PartialBehaviorCodec.comp_toMorphism_iff` (L1556),
       `PartialBehaviorCodec.id_toMorphism` (L1583),
       `PartialBehaviorCodec.comp_toMorphism` (L1596),
       `valid_bool_negation_compiles` (L1773),
       `corrupt_bool_bitpattern_2_rejected` (L1793).

3. **[AntiDegeneracyAndCallbackFraming.lean](support/AntiDegeneracyAndCallbackFraming.lean)**
   - **Lines:** `3956`
   - **SHA-256:**
     `3b8050a5d531ad98097cfe440a3a40bd02a25afc32ea25680244264d42e7c41f`
   - **Key mechanized declarations and theorems for certifying pass
     anti-degeneracy (Section 3, lines 708–1565):**
     - `trap1_alwaysFalse_compiles` (L753), `trap1_alwaysFalse_never_accepts`
       (L760), `trap2_id_compiles` (L777), `peephole_noop_on_corpus` (L867),
       `compiles_id_forbids_instruction_deletion` (L916).
     - `π_opt` (L991), `monotone_π_opt` (L1000),
       `π_opt_preserves_wellFormedOn` (L1015),
       `π_opt_preserves_ensuresRetLibInv` (L1025),
       `CertifiedOptimizationPass` (L1101), `trap1_rejected_by_contract`
       (L1131), `trap2_id_rejected_by_contract` (L1142),
       `peephole_on_newUnchecked_rejected` (L1154), `coalesceAndFoldBody`
       (L1186), `genuineCoalescePass_certified` (L1540).
     (Section 4 of this file, lines 1569–3955, additionally contains the shared
     callback re-entrancy and `StepResultExt.externalCall` mechanization.)

### Upstream Repository Source Coordinates

- `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
  - `trusted/lean/Trusted/Refinement.lean` (lines 48–461)
  - `trusted/lean/Trusted/StepResult.lean` (lines 32–198)
  - `trusted/lean/Trusted/MirSemantics.lean` (lines 590–867)
  - `theory/Anneal/Refinement.lean` (lines 1–288)
- `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`:
  - `trusted/lean/Trusted/Refinement.lean` (lines 155–245)
  - `trusted/lean/Trusted/StepResult.lean` (lines 49–215)
  - `trusted/lean/Trusted/X86Semantics.lean` (lines 650–896)
  - `theory/Anneal/Compiler/NaiveCodegen.lean` (lines 38–153, 264–299, 810–870)
  - `theory/Anneal/Compiler/Peephole.lean` (lines 45–205)
  - `theory/Anneal/MirLemmas.lean` (lines 380–755)
  - `trusted/rustc-capture/src/lib.rs` (lines 1166–1340)

## Revalidation

Re-run the preserved Lean 4 checks and review this report's conclusions
whenever:

1. `trusted/lean/Trusted/Refinement.lean` modifies `Partial`, `BehaviorCodec`,
   `Compiles`, `Abstracts`, `Compiler`, `Compiler.SoundOn`, or
   `Compiler.Verified`.
2. `trusted/lean/Trusted/StepResult.lean` modifies `StepResult`,
   `PrefixOutcome`, `ExecQuery`, `ReachesPrefix`, or `BehaviorOf` (or adopts
   `EventualBehaviorOf`).
3. `theory/Anneal/Compiler/NaiveCodegen.lean` or
   `theory/Anneal/Compiler/Peephole.lean` expands `compileStmt` beyond 1-to-1
   instruction selection, lowers typed `X86Val` values into raw machine words,
   or wires an optimization pass into `rustc-capture`.

Deterministic kernel revalidation command from the package root:

```bash
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/MorphismAdmissibility.lean && \
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/BehaviorCodecExpressiveness.lean && \
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/AntiDegeneracyAndCallbackFraming.lean
```
