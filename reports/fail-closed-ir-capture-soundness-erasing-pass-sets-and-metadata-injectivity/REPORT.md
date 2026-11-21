# Fail-closed IR capture, erasing-pass sets before the capture point, and metadata injectivity

## Summary

This package proves, in Lean 4 without Mathlib, statements about a toy model of a *capture*: a translation of programs from a source IR into a verifier IR, taken at a capture point after some compiler passes have run, that may reject programs it does not model. The results relate a verifier's verdict about the captured program to the source program (through the passes before the capture point), characterize what a capture must guarantee for every sound verifier, compare failing closed with failing open on unmodeled constructs, state when merging metadata rules out a faithful verifier semantics, and treat a toy build-flag contract. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend. Upstream compiler documentation enters through a separately labelled `derived (modeling bridge)` discussion at pinned public revisions and in no Lean statement; no tool was run and nothing was measured.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result follows, each the plain claim of its card in `## Findings` with all of its hypotheses; the non-claims of every card are listed first under `## Boundaries`.

- `transfer-to-capture-input` (theorem, T0): For all types `S`, `V`, `E`, `B`, source semantics `semS`, verifier semantics `semV`, capture `cap : S → Except E V`, verdict relation `verified`, programs `p`, `q` and specification `spec : B → Prop`: if `verified` is sound for `semV` (`VerifierSound`) and `cap` over-approximates on its ok-image (`OverApproxOnOk`: every run of a successfully captured program is a run of its capture), then `cap p = .ok q` and `verified q spec` imply `Sat (semS p) spec`. When the capture is taken after a pipeline, `p` is the pipeline output, not the original source.
- `transfer-through-pipeline-losing-no-runs` (theorem, T0): For every pipeline `pipe`, source `src`, program `q` and specification `spec`: if `verified` is sound for `semV`, `cap` over-approximates on its ok-image, and every pass of `pipe`, whatever its tag, loses no run at its actual input (`LosesNoBehaviourAtInputs`: the input of pass `i` is the program the passes before it produce from `src`), then `cap (runPipe pipe src) = .ok q` and `verified q spec` imply `Sat (semS src) spec`.
- `transfer-relative-to-erasing-set` (theorem, T1): For every pipeline `pipe`, source `src`, program `q` and specification `spec`: if `verified` is sound for `semV`, `cap` over-approximates on its ok-image, every `equiv`-tagged pass of `pipe` preserves the denotation of every program (`EquivTagSound`, for all programs, not only those it is applied to), and every pass in the erasing set `E_k` (`InErasingSet`: the `erasing`-tagged passes of `pipe`) loses no run at its actual input (`ErasingSetPrecondition`, equivalently `erasingSetPrecondition_iff_forall_inErasingSet`), then `cap (runPipe pipe src) = .ok q` and `verified q spec` imply `Sat (semS src) spec`. Its one-pass instance is `transfer_single_pass`.
- `capture-after-ub-erasing-pass` (counterexample, T1): In the concrete toy, with the fail-closed capture `capFC`, the exact verifier for `semV .noop` and a pipeline of exactly one erasing pass, the captured program is verified `ubFree` while the source is not, for place-mention erasure on `pPM`, zero-size-read erasure on `pZst`, and equal-target switch erasure on `pSw`; in each instance every hypothesis of `transfer_relative_to_erasingSet` except the erasing-set precondition holds, and the precondition fails.
- `fail-open-capture-variants-unsound` (counterexample, T1): In the concrete toy, with the empty pipeline and the exact verifier for `semV .noop`, for each of the three fail-open captures there is a named program with an unmodeled construct that the capture accepts, and a specification that the verifier proves of the captured program and that is false of the source: `capDefault` on `pTrap` (specification `returnsNormally`), `capStringify` on `pAsm` with `opaque` read as a no-op (specification `silent`, no output), `capSwallow` on `pErr` (specification `returnsNormally`); in each instance every hypothesis of `transfer_relative_to_erasingSet` except over-approximation holds, and over-approximation fails.
- `dropped-metadata-unsound` (counterexample, T1): In the concrete toy, `capNoCleanup` maps `pCl` (aborts with reason `inCleanup`) and `pNo` (unwinds) to the same `qUnw`, and `capNoReason` maps `pTerm .abi` and `pTerm .inCleanup` to the same `qTermAbi`, although in each pair the two programs do not admit the same runs; with the empty pipeline and the exact verifier for `semV .noop`, the verifier proves `noAbort` of `qUnw` (false of `pCl`) and `noAbortInCleanup` of `qTermAbi` (false of `pTerm .inCleanup`), and every hypothesis of `transfer_relative_to_erasingSet` except over-approximation holds.
- `no-faithful-semantics-for-merged-pair` (impossibility, T0): For every capture `cap`, source semantics `semS` and programs `p₁`, `p₂`, `q`: if `cap p₁ = .ok q`, `cap p₂ = .ok q`, and `p₁`, `p₂` do not admit the same runs, then no verifier semantics makes `cap` faithful at both `p₁` and `p₂` (`no_semV_faithful_at_merged_pair`), and hence none makes `cap` faithful on its ok-image (`not_faithfulOnOk_of_merged_pair`).
- `faithful-semantics-exists-iff-merges-only-equivalent` (characterization, T0): For every capture `cap` and source semantics `semS`, some verifier semantics makes `cap` faithful on its ok-image iff any two programs that `cap` maps to the same `q` admit the same runs.
- `toy-clearing-replace-flag-is-equivalence` (theorem, T1): In the concrete toy, clearing every drop replace flag (`clearReplace`) preserves the source denotation of every program.
- `transfer-soundness-iff-over-approximation` (characterization, T0): For every capture `cap : S → Except E V`, source semantics `semS` and verifier semantics `semV`: verification transfers through `cap` (`TransferSound`, which quantifies over every specification `spec : B → Prop`) for every verdict relation sound for `semV` iff `cap` over-approximates on its ok-image; and it transfers for the exact verifier of `semV` iff `cap` over-approximates on its ok-image. Programs on which `cap` errors impose no obligation.
- `fail-closed-and-fail-open-obligations` (characterization, T0): For every decidable fragment `M` and translation `tr`: the fail-closed capture `failClosed M tr e` (for every error value `e`) over-approximates on its ok-image iff `tr` over-approximates on every program in `M`; the fail-open capture `failOpen M tr fb` (for every fallback `fb`) over-approximates iff `tr` over-approximates on every program in `M` and `fb` over-approximates on every program outside `M`; and more generally the partial extension `partialExtend M tr rest` over-approximates iff `tr` over-approximates on `M` and every successful result of `rest` outside `M` over-approximates.
- `over-approximation-is-faithfulness-for-total-deterministic` (theorem, T0): For runs of the form `I × O`: if every successfully captured source denotation is total (`Total`: every input has at least one outcome) and every captured denotation is deterministic (`Det`: every input has at most one outcome), then the capture over-approximates on its ok-image iff it is faithful on its ok-image.
- `toy-fail-closed-capture-faithful` (theorem, T1): In the concrete toy, the fail-closed capture `capFC` is faithful on its ok-image for either meaning of `opaque` (`capFC_faithfulOnOk`); more precisely, whenever `capFC p = .ok q`, the verifier run of `q` equals the source run of `p` at every fuel, block and state (`capFC_runV_eq_runS`).
- `toy-stringify-with-havoc-over-approximates` (theorem, T1): In the concrete toy, `capStringify` over-approximates on its ok-image when `opaque` is read as `havoc`; it is not faithful under that reading, and it does not over-approximate when `opaque` is read as a no-op.
- `flag-contract-sound-iff-no-silent-omission` (characterization, T1): For every toy backend `be` and per-flag property `Holds`: if admitted flags are honoured (`HonoursAdmitted`: for every list `fs` of admitted flags, the artifact `be.build fs` has the property of every flag in `fs`, all at once) and every omission is observable in some admitted context (`OmissionObservableOnAdmitted`: for every omitted flag `f` there is a list `fs` of admitted flags, possibly empty, such that `be.build fs` lacks `f`'s property), then the contract 'flag set ⇒ property holds of the artifact', for every configuration (`FlagContractSound`), holds iff the backend never silently omits a flag (`NeverOmits`). Sufficiency uses `HonoursAdmitted` alone (`flagContractSound_of_neverOmits`), necessity uses `OmissionObservableOnAdmitted` alone (`neverOmits_of_flagContractSound`), and under `HonoursAdmitted` alone the contract holds iff the property of every omitted flag holds of the artifact built from every list of admitted flags (`flagContractSound_iff_omitted_hold_in_admitted_contexts`).
- `checked-artifact-restores-flag-contract` (theorem, T0): For every toy backend `be`, property `Holds` and per-flag check `check`: if the check is sound for the property (`check f a = true → Holds f a`), then every artifact that the checked run `checkedRun be check cfg` returns has the property of every requested flag, for every configuration `cfg`, including for a backend that silently omits flags (`checkedRun_contractSound`); and if the check is also complete (`Holds f a → check f a = true`), the checked run returns `a` whenever `be.run cfg = .ok a` and `a` has the property of every flag in `cfg` (`checkedRun_eq_run_of_holds`).
- `exempting-source-audit-weaker-than-ir-audit` (theorem, T0): In the toy audit model, every program that the post-expansion IR audit `irAudit` accepts is accepted by the source-level audit `srcAuditExemptExternal`, which exempts external macro expansions (`srcAudit_of_irAudit`); and the converse fails: there is a program, `[.macro true [true]]` (exactly one external macro whose expansion contains an unsafe item), that the exempting source audit accepts and the IR audit rejects (`srcAudit_misses_external_unsafe`). `exemptingSrcAudit_strictlyWeaker_than_irAudit` states both.

## Applicability

**Model fidelity.** Every result is a Lean theorem about definitions in namespace `Toy.Capture` (Lake project `lean/`, library `Toy`). The abstract layer (`Basic.lean`) is parametric: source programs `S`, verifier programs `V`, capture errors `E`, runs `B`, denotations `Den B := B → Prop`, a capture `S → Except E V`, passes `S → S` tagged `equiv` or `erasing`, and verdict relations `V → (B → Prop) → Prop`. The concrete toy (`Lang.lean`, `Sim.lean`, `Examples.lean`, `Counterexamples.lean`) instantiates it with a small control-flow-graph language and a fuel-bounded interpreter; the flag model (`Flags.lean`) is a separate toy of backends that admit, reject or omit requested flags. The definitions are meant to capture a capture bridge from a compiler's source IR to a verifier's IR, the passes that run before the capture point, and the build flags that request properties of an artifact.

**Known gaps.** The concrete toy runs for at most `blocks.length + 1` block entries and reports `fuelOut` beyond that (`fixedFuel_boundary`); erroneous constants fail at run time with outcome `constErr`; inline assembly is a fall-through statement; the panic response is decided by the block's cleanup mark; the terminate reason is part of the observable outcome; the drop terminator deinitializes a local and runs no drop glue; dialect changes between pipeline phases are not modeled; flag responses are per flag and configuration-independent. Each card's non-claims under `## Boundaries` list the gaps that bear on it.

**Relation to real systems.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend. The subsection *Modeling bridge* under `## Findings` quotes rust-lang/rust source and documentation at the pinned revisions f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1 and 26bfbf28f5f79dff333ce5a232f131b496ec9cfe and states, as `derived (modeling bridge)` reasoning, how the toy's erasing passes, cleanup marks, terminate reasons and drop replace flag correspond to the documented design; that reasoning is not a theorem. Those revisions are cited as documentation for the bridge, not as subjects of the Lean results.

**Subjects.** The Lean 4 toolchain `leanprover/lean4:v4.34.1` (tag commit 5045d0056413266e57c625dcd7c365b10e377c52) is the kernel that checked every theorem. The papers (Leroy, JAR 2009; Pnueli, Siegel and Singerman, TACAS 1998; Blazy, Dargaye and Leroy, FM 2006) and CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc are the prior art that several cards restate in this vocabulary (tier `T0`); they are cited, not formalized or imported. Four packages of the same reference corpus are cited by name as related results; nothing is imported from them.

**Toolchain.** Lean `leanprover/lean4:v4.34.1`, core Lean: no Mathlib, no `Std` import, no Lake dependencies (one `[[lean_lib]]`, no `[[require]]`).

## Findings

Basis of every Lean statement below: execution (Lean kernel check). Every Lean block is a verbatim quote of the package source, labelled `-- path:lines` relative to the package root (the Lake project is `lean/`); theorem quotes end at the line that ends the statement, and a proof that starts on that line is elided as `:= …`. Definitions are quoted in full.

### Key definitions unfolded (prose)

Unfolded (prose):
- A denotation `Den B` is a predicate on runs `B`. `Sat d spec` is `∀ b, d b → spec b`. `DenIncl d₁ d₂` is `∀ b, d₁ b → d₂ b`; `DenEquiv d₁ d₂` is `∀ b, d₁ b ↔ d₂ b`.
- `FaithfulOnOk semS semV cap`: `∀ p q, cap p = .ok q → ∀ b, semV q b ↔ semS p b`. `FaithfulAt semS semV cap p` is the same at one `p`. `OverApproxOnOk semS semV cap`: `∀ p q, cap p = .ok q → ∀ b, semS p b → semV q b`. Programs on which `cap` returns `.error` impose no condition.
- `VerifierSound semV verified`: `∀ q spec, verified q spec → Sat (semV q) spec`. `exactVerifier semV q spec` is `Sat (semV q) spec`. `TransferSound semS cap verified`: `∀ p q spec, cap p = .ok q → verified q spec → Sat (semS p) spec`, for every specification `spec : B → Prop`.
- A pass is a tag (`equiv` or `erasing`) and a function `S → S`; `runPipe [P₁, …, Pₖ] src` applies `P₁` first. `EquivTagSound semS P`: if `P` is tagged `equiv`, then `semS (P.run p)` and `semS p` admit the same runs for every program `p` (not only for the programs it is applied to). The `erasing` tag carries no hypothesis. `LosesNoBehaviourAt semS f p` is `DenIncl (semS p) (semS (f p))`. `ErasingSetPrecondition semS pipe src`: for every index `i < pipe.length` whose pass is tagged `erasing` (the erasing set `E_k`, `InErasingSet`; `erasingSetPrecondition_iff_forall_inErasingSet`), that pass loses no run at `runPipe (pipe.take i) src`. `LosesNoBehaviourAtInputs` requires this for every index, whatever the tag.
- `failClosed M tr e` and `failOpen M tr fb` translate the programs in the fragment `M` with `tr`; outside `M` the first returns the error `e` and the second returns `fb p`. Both are instances of `partialExtend M tr rest`, which returns `rest p` outside `M`.
- Concrete toy (`Lang.lean`). A run is `(x, b)`: input `x : Nat` (stored in local `0`; other locals start uninitialized) and behaviour `b = ⟨trace, outcome⟩` with outcomes `ret`, `unwind`, `abort r` (`r ∈ {abi, inCleanup}`), `trap`, `ub`, `constErr`, `fuelOut`. `semS p` is deterministic and total (`semS_det`, `semS_total`): `runS` with fuel `SProg.fuel p` = number of blocks + 1, one unit per block entered, counting every block whether reachable or not; a run that needs more ends in `fuelOut` (`fixedFuel_boundary`). Source statements: `assign`, `placeMention l` and `zstRead l` (both UB iff local `l` is uninitialized or holds `0`), `emit`, and `asm c` (outputs `c`). Source terminators: `goto`, `switchInt o targets otherwise` (reads `o`; UB if `o` reads an uninitialized local; value `v` selects `targets[v]` if `v < targets.length`, else `otherwise`), `ret`, `resume` (outcome `unwind`), `call panics next unwind` (a panic in a cleanup block gives `abort inCleanup`; in a normal block it follows `unwind`: `continueUnwind` gives outcome `unwind`, `cleanup c` jumps to block `c`), `drop replace l next` (UB if `l` is uninitialized, otherwise deinitializes `l`; `replace` is ignored), `terminate r` (outcome `abort r`), `trap next` (outcome `trap`; `next` is never taken), `unreachable` (UB). Constants are `val n` or `err` (evaluation gives outcome `constErr`). Jumping to a missing block is UB.
- Verifier IR: the same constructs without `asm`, `trap`, erroneous constants and the replace flag, plus `opaque tag`. `semV os q`: `noop` reads `opaque` as no effect; under `havoc` a run that reaches `opaque` ends with `VRes.top`, which admits every behaviour for that input, including behaviours whose trace does not extend the output emitted before `opaque` (`semV_havoc_admits_any_trace`). Captures `capWith c` translate block by block; `cfgFC` rejects `asm`, `trap` and erroneous constants and keeps cleanup marks and terminate reasons. `capDefault`, `capStringify`, `capSwallow`, `capNoCleanup` and `capNoReason` each change exactly one field of `cfgFC`: `trap next ↦ goto next`; `asm c ↦ opaque c`; `err ↦ val 0`; every block marked normal; every terminate reason ↦ `abi`. Each of the first three agrees with `capFC` wherever `capFC` succeeds (`failOpenVariants_eq_partialExtend_capFC`).
- Passes: `erasePlaceMentions` and `eraseZstReads` delete every such statement; `simplifyTrivialSwitches` replaces each `switchInt o ts ow` whose targets all equal `ow`, and whose operand is not an erroneous constant, by `goto ow` (the operand read disappears); `clearReplace` sets every replace flag to `false`.
- Flags (`Flags.lean`). A toy `Backend` responds to each flag with `admitted`, `rejected` or `omitted`; `Backend.run` fails on the first rejected flag and otherwise builds from the admitted flags, dropping omitted flags silently. `FlagContractSound Holds be`: every successful build has the property of every requested flag. `HonoursAdmitted`: the artifact built from any list of admitted flags has all their properties at once. `OmissionObservableOnAdmitted`: every omitted flag's property fails for the artifact built from some list of admitted flags (possibly empty). `NeverOmits`: no flag is omitted.

### Design questions and how the cards answer them

- Capture point: a verdict about captured IR is about the program the capture saw (`transfer-to-capture-input`); it transfers to the source through the passes before the capture point when every pass loses no source run at its actual input (`transfer-through-pipeline-losing-no-runs`), and in tag form when every `equiv` tag is sound for every program and every pass in the erasing set `E_k` meets its precondition at its actual input (`transfer-relative-to-erasing-set`); without the erasing-set precondition it can fail (`capture-after-ub-erasing-pass`).
- Fail-closed: over-approximation on the ok-image is the exact capture-side condition for transfer with every sound verifier (`transfer-soundness-iff-over-approximation`); failing closed adds no obligation outside the modeled fragment, while failing open adds one per accepted unmodeled program (`fail-closed-and-fail-open-obligations`); concrete fail-open variants violate it (`fail-open-capture-variants-unsound`), except a stringifying capture whose placeholder the verifier reads as `havoc` (`toy-stringify-with-havoc-over-approximates`). Faithfulness coincides with over-approximation for total sources and deterministic captured programs (`over-approximation-is-faithfulness-for-total-deterministic`); the toy fail-closed capture is faithful (`toy-fail-closed-capture-faithful`).
- Metadata: a faithful verifier semantics exists iff the capture merges only programs with equal run sets (`faithful-semantics-exists-iff-merges-only-equivalent`, `no-faithful-semantics-for-merged-pair`); forgetting the cleanup mark or the terminate reason merges programs with different runs (`dropped-metadata-unsound`), forgetting the replace flag does not (`toy-clearing-replace-flag-is-equivalence`).
- Configuration: with admitted flags honoured and omissions observable in some admitted context, the flag contract holds iff nothing is silently omitted (`flag-contract-sound-iff-no-silent-omission`); a sound check of every requested flag on the artifact restores the contract shape (`checked-artifact-restores-flag-contract`); a source audit that exempts external macro expansions is strictly weaker than an audit of the expanded IR in the toy (`exempting-source-audit-weaker-than-ir-audit`).

### Definitions (verbatim) with examples

#### Abstract layer (`Basic.lean`)

```lean
-- lean/Toy/Capture/Basic.lean:29
abbrev Den (B : Type) : Type := B → Prop
```

```lean
-- lean/Toy/Capture/Basic.lean:33-34
def Sat {B : Type} (d : Den B) (spec : B → Prop) : Prop :=
  ∀ b, d b → spec b
```

```lean
-- lean/Toy/Capture/Basic.lean:37-38
def DenIncl {B : Type} (d₁ d₂ : Den B) : Prop :=
  ∀ b, d₁ b → d₂ b
```

```lean
-- lean/Toy/Capture/Basic.lean:41-42
def DenEquiv {B : Type} (d₁ d₂ : Den B) : Prop :=
  ∀ b, d₁ b ↔ d₂ b
```

Examples: `sat_example_pos`, `sat_example_neg`, `denIncl_example_pos`, `denIncl_example_neg`, `denEquiv_example_pos`, `denEquiv_example_neg`.

```lean
-- lean/Toy/Capture/Basic.lean:46-48
def FaithfulOnOk {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) : Prop :=
  ∀ p q, cap p = .ok q → DenEquiv (semV q) (semS p)
```

```lean
-- lean/Toy/Capture/Basic.lean:53-55
def OverApproxOnOk {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) : Prop :=
  ∀ p q, cap p = .ok q → DenIncl (semS p) (semV q)
```

Examples: `faithfulOnOk_example_pos`, `faithfulOnOk_example_neg`, `faithfulAt_example_pos`, `faithfulAt_example_neg`, `overApproxOnOk_example_pos`, `overApproxOnOk_example_neg`.

```lean
-- lean/Toy/Capture/Basic.lean:60-62
def VerifierSound {V B : Type} (semV : V → Den B) (verified : V → (B → Prop) → Prop) :
    Prop :=
  ∀ q spec, verified q spec → Sat (semV q) spec
```

```lean
-- lean/Toy/Capture/Basic.lean:67-68
def exactVerifier {V B : Type} (semV : V → Den B) : V → (B → Prop) → Prop :=
  fun q spec => Sat (semV q) spec
```

```lean
-- lean/Toy/Capture/Basic.lean:72-74
def TransferSound {S V E B : Type} (semS : S → Den B) (cap : S → Except E V)
    (verified : V → (B → Prop) → Prop) : Prop :=
  ∀ p q spec, cap p = .ok q → verified q spec → Sat (semS p) spec
```

Examples: `verifierSound_example_pos`, `verifierSound_example_neg`, `transferSound_example_pos`, `transferSound_example_neg`.

```lean
-- lean/Toy/Capture/Basic.lean:82-85
inductive Tag where
  | equiv
  | erasing
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Basic.lean:88-90
structure Pass (S : Type) where
  tag : Tag
  run : S → S
```

```lean
-- lean/Toy/Capture/Basic.lean:93-95
def runPipe {S : Type} : List (Pass S) → S → S
  | [], p => p
  | P :: rest, p => runPipe rest (P.run p)
```

```lean
-- lean/Toy/Capture/Basic.lean:99-100
def EquivTagSound {S B : Type} (semS : S → Den B) (P : Pass S) : Prop :=
  P.tag = .equiv → ∀ p, DenEquiv (semS (P.run p)) (semS p)
```

```lean
-- lean/Toy/Capture/Basic.lean:105-106
def LosesNoBehaviourAt {S B : Type} (semS : S → Den B) (f : S → S) (p : S) : Prop :=
  DenIncl (semS p) (semS (f p))
```

```lean
-- lean/Toy/Capture/Basic.lean:111-112
def InErasingSet {S : Type} (pipe : List (Pass S)) (i : Nat) : Prop :=
  ∃ h : i < pipe.length, (pipe[i]'h).tag = .erasing
```

```lean
-- lean/Toy/Capture/Basic.lean:116-119
def ErasingSetPrecondition {S B : Type} (semS : S → Den B) (pipe : List (Pass S))
    (src : S) : Prop :=
  ∀ i (h : i < pipe.length), (pipe[i]'h).tag = .erasing →
    LosesNoBehaviourAt semS (pipe[i]'h).run (runPipe (pipe.take i) src)
```

```lean
-- lean/Toy/Capture/Basic.lean:122-125
def LosesNoBehaviourAtInputs {S B : Type} (semS : S → Den B) (pipe : List (Pass S))
    (src : S) : Prop :=
  ∀ i (h : i < pipe.length),
    LosesNoBehaviourAt semS (pipe[i]'h).run (runPipe (pipe.take i) src)
```

Examples: `runPipe_example`, `equivTagSound_example_pos`, `equivTagSound_example_neg`, `equivTagSound_erasing`, `losesNoBehaviourAt_example_pos`, `losesNoBehaviourAt_example_neg`, `inErasingSet_example_pos`, `inErasingSet_example_neg`, `erasingSetPrecondition_example_pos`, `erasingSetPrecondition_example_neg`, `losesNoBehaviourAtInputs_example_pos`, `losesNoBehaviourAtInputs_example_neg`.

```lean
-- lean/Toy/Capture/Basic.lean:251-253
def FaithfulAt {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) (p : S) : Prop :=
  ∀ q, cap p = .ok q → DenEquiv (semV q) (semS p)
```

```lean
-- lean/Toy/Capture/Basic.lean:352-353
def Total {I O : Type} (d : Den (I × O)) : Prop :=
  ∀ i, ∃ o, d (i, o)
```

```lean
-- lean/Toy/Capture/Basic.lean:357-358
def Det {I O : Type} (d : Den (I × O)) : Prop :=
  ∀ i o o', d (i, o) → d (i, o') → o = o'
```

Examples: `semS_total`, `semS_det`, `total_example_neg`, `det_example_neg`.

```lean
-- lean/Toy/Capture/Basic.lean:386-388
def failClosed {S V E : Type} (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E)
    (p : S) : Except E V :=
  if M p then .ok (tr p) else .error e
```

```lean
-- lean/Toy/Capture/Basic.lean:393-395
def failOpen {S V E : Type} (M : S → Prop) [DecidablePred M] (tr fb : S → V)
    (p : S) : Except E V :=
  if M p then .ok (tr p) else .ok (fb p)
```

Examples: `failClosed_example_pos`, `failClosed_example_neg`, `failOpen_example`, `failOpen_overApproxOnOk_example_pos`, `failClosed_empty_fragment`.

```lean
-- lean/Toy/Capture/Basic.lean:401-403
def partialExtend {S V E : Type} (M : S → Prop) [DecidablePred M] (tr : S → V)
    (rest : S → Except E V) (p : S) : Except E V :=
  if M p then .ok (tr p) else rest p
```

#### Concrete toy (`Lang.lean`)

```lean
-- lean/Toy/Capture/Lang.lean:30-33
inductive Reason where
  | abi
  | inCleanup
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:38-46
inductive Outcome where
  | ret
  | unwind
  | abort (r : Reason)
  | trap
  | ub
  | constErr
  | fuelOut
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:49-52
structure Beh where
  trace : List Nat
  out : Outcome
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:55
abbrev Run : Type := Nat × Beh
```

```lean
-- lean/Toy/Capture/Lang.lean:58-60
structure St where
  loc : Nat → Option Nat
  tr : List Nat
```

```lean
-- lean/Toy/Capture/Lang.lean:64
def St.init (x : Nat) : St := ⟨fun l => if l = 0 then some x else none, []⟩
```

```lean
-- lean/Toy/Capture/Lang.lean:66-67
def St.set (st : St) (l : Nat) (v : Option Nat) : St :=
  { st with loc := fun j => if j = l then v else st.loc j }
```

```lean
-- lean/Toy/Capture/Lang.lean:69
def St.emit (st : St) (v : Nat) : St := { st with tr := st.tr ++ [v] }
```

```lean
-- lean/Toy/Capture/Lang.lean:72
def St.fin (st : St) (o : Outcome) : Beh := ⟨st.tr, o⟩
```

```lean
-- lean/Toy/Capture/Lang.lean:76-79
def derefOk (st : St) (l : Nat) : Bool :=
  match st.loc l with
  | some (_ + 1) => true
  | _ => false
```

```lean
-- lean/Toy/Capture/Lang.lean:84-87
inductive Const where
  | val (n : Nat)
  | err
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:89-92
inductive SOperand where
  | copy (l : Nat)
  | const (c : Const)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:94-106
inductive SStmt where
  /-- `d := o` -/
  | assign (d : Nat) (o : SOperand)
  /-- Evaluate the place `*l` and discard it (no load). UB iff `*l` is invalid. -/
  | placeMention (l : Nat)
  /-- Read zero bytes through the pointer in local `l`. UB iff `*l` is invalid. -/
  | zstRead (l : Nat)
  /-- Append the operand's value to the output trace. -/
  | emit (o : SOperand)
  /-- A construct the captures here do not model: it appends `c` to the output
  trace. -/
  | asm (c : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:110-113
inductive UnwindAct where
  | continueUnwind
  | cleanup (l : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:115-136
inductive STerm where
  | goto (t : Nat)
  /-- Read `o`; jump to `targets[v]` if the value `v` is below `targets.length`,
  otherwise to `otherwise`. Reading an uninitialized local is UB. -/
  | switchInt (o : SOperand) (targets : List Nat) (otherwise : Nat)
  | ret
  /-- Continue unwinding out of the function (outcome `unwind`). -/
  | resume
  /-- Call an opaque function that panics iff `panics`. A panic in a cleanup block
  aborts with reason `inCleanup`; in a normal block it follows `unwind`. -/
  | call (panics : Bool) (next : Nat) (unwind : UnwindAct)
  /-- Drop local `l` (deinitialize it) and go to `next`; UB if `l` is
  uninitialized. The `replace` flag has no operational effect. -/
  | drop (replace : Bool) (l : Nat) (next : Nat)
  /-- Abort with the given reason. -/
  | terminate (r : Reason)
  /-- A construct the captures here do not model: it aborts the run (outcome
  `trap`). `next` is a syntactic fall-through label that is never taken. -/
  | trap (next : Nat)
  /-- UB. -/
  | unreachable
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:138-142
structure SBlock where
  stmts : List SStmt
  term : STerm
  cleanup : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:145-147
structure SProg where
  blocks : List SBlock
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:149-155
def SOperand.eval (st : St) : SOperand → Except Outcome Nat
  | .copy l =>
    match st.loc l with
    | some v => .ok v
    | none => .error .ub
  | .const (.val n) => .ok n
  | .const .err => .error .constErr
```

```lean
-- lean/Toy/Capture/Lang.lean:159-170
def execSStmt (st : St) : SStmt → Except Beh St
  | .assign d o =>
    match o.eval st with
    | .ok v => .ok (st.set d (some v))
    | .error e => .error (st.fin e)
  | .placeMention l => if derefOk st l then .ok st else .error (st.fin .ub)
  | .zstRead l => if derefOk st l then .ok st else .error (st.fin .ub)
  | .emit o =>
    match o.eval st with
    | .ok v => .ok (st.emit v)
    | .error e => .error (st.fin e)
  | .asm c => .ok (st.emit c)
```

```lean
-- lean/Toy/Capture/Lang.lean:172-177
def execSStmts : List SStmt → St → Except Beh St
  | [], st => .ok st
  | s :: ss, st =>
    match execSStmt st s with
    | .ok st' => execSStmts ss st'
    | .error b => .error b
```

```lean
-- lean/Toy/Capture/Lang.lean:181-212
def runS (p : SProg) : Nat → Nat → St → Beh
  | 0, _, st => st.fin .fuelOut
  | n + 1, pc, st =>
    match p.blocks[pc]? with
    | none => st.fin .ub
    | some blk =>
      match execSStmts blk.stmts st with
      | .error b => b
      | .ok st' =>
        match blk.term with
        | .goto t => runS p n t st'
        | .switchInt o ts ow =>
          match o.eval st' with
          | .ok v => runS p n (ts.getD v ow) st'
          | .error e => st'.fin e
        | .ret => st'.fin .ret
        | .resume => st'.fin .unwind
        | .call panics next uw =>
          if panics then
            if blk.cleanup then st'.fin (.abort .inCleanup)
            else
              match uw with
              | .continueUnwind => st'.fin .unwind
              | .cleanup c => runS p n c st'
          else runS p n next st'
        | .drop _ l next =>
          match st'.loc l with
          | some _ => runS p n next (st'.set l none)
          | none => st'.fin .ub
        | .terminate r => st'.fin (.abort r)
        | .trap _ => st'.fin .trap
        | .unreachable => st'.fin .ub
```

```lean
-- lean/Toy/Capture/Lang.lean:217
def SProg.fuel (p : SProg) : Nat := p.blocks.length + 1
```

```lean
-- lean/Toy/Capture/Lang.lean:221-222
def semS (p : SProg) : Den Run :=
  fun r => runS p p.fuel 0 (St.init r.1) = r.2
```

```lean
-- lean/Toy/Capture/Lang.lean:229-232
inductive VOperand where
  | copy (l : Nat)
  | const (n : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:234-242
inductive VStmt where
  | assign (d : Nat) (o : VOperand)
  | placeMention (l : Nat)
  | zstRead (l : Nat)
  | emit (o : VOperand)
  /-- A statement the verifier knows only by an opaque tag; its meaning is the
  parameter `OpaqueSem`. -/
  | opaque (tag : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:244-253
inductive VTerm where
  | goto (t : Nat)
  | switchInt (o : VOperand) (targets : List Nat) (otherwise : Nat)
  | ret
  | resume
  | call (panics : Bool) (next : Nat) (unwind : UnwindAct)
  | drop (l : Nat) (next : Nat)
  | terminate (r : Reason)
  | unreachable
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:255-259
structure VBlock where
  stmts : List VStmt
  term : VTerm
  cleanup : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:261-263
structure VProg where
  blocks : List VBlock
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:269-272
inductive OpaqueSem where
  | noop
  | havoc
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:276-279
inductive VRes where
  | det (b : Beh)
  | top
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:282-284
def VRes.admits : VRes → Beh → Prop
  | .det b', b => b' = b
  | .top, _ => True
```

```lean
-- lean/Toy/Capture/Lang.lean:286-291
def VOperand.eval (st : St) : VOperand → Except Outcome Nat
  | .copy l =>
    match st.loc l with
    | some v => .ok v
    | none => .error .ub
  | .const n => .ok n
```

```lean
-- lean/Toy/Capture/Lang.lean:293-307
def execVStmt (os : OpaqueSem) (st : St) : VStmt → Except VRes St
  | .assign d o =>
    match o.eval st with
    | .ok v => .ok (st.set d (some v))
    | .error e => .error (.det (st.fin e))
  | .placeMention l => if derefOk st l then .ok st else .error (.det (st.fin .ub))
  | .zstRead l => if derefOk st l then .ok st else .error (.det (st.fin .ub))
  | .emit o =>
    match o.eval st with
    | .ok v => .ok (st.emit v)
    | .error e => .error (.det (st.fin e))
  | .opaque _ =>
    match os with
    | .noop => .ok st
    | .havoc => .error .top
```

```lean
-- lean/Toy/Capture/Lang.lean:309-314
def execVStmts (os : OpaqueSem) : List VStmt → St → Except VRes St
  | [], st => .ok st
  | s :: ss, st =>
    match execVStmt os st s with
    | .ok st' => execVStmts os ss st'
    | .error r => .error r
```

```lean
-- lean/Toy/Capture/Lang.lean:316-346
def runV (os : OpaqueSem) (q : VProg) : Nat → Nat → St → VRes
  | 0, _, st => .det (st.fin .fuelOut)
  | n + 1, pc, st =>
    match q.blocks[pc]? with
    | none => .det (st.fin .ub)
    | some blk =>
      match execVStmts os blk.stmts st with
      | .error r => r
      | .ok st' =>
        match blk.term with
        | .goto t => runV os q n t st'
        | .switchInt o ts ow =>
          match o.eval st' with
          | .ok v => runV os q n (ts.getD v ow) st'
          | .error e => .det (st'.fin e)
        | .ret => .det (st'.fin .ret)
        | .resume => .det (st'.fin .unwind)
        | .call panics next uw =>
          if panics then
            if blk.cleanup then .det (st'.fin (.abort .inCleanup))
            else
              match uw with
              | .continueUnwind => .det (st'.fin .unwind)
              | .cleanup c => runV os q n c st'
          else runV os q n next st'
        | .drop l next =>
          match st'.loc l with
          | some _ => runV os q n next (st'.set l none)
          | none => .det (st'.fin .ub)
        | .terminate r => .det (st'.fin (.abort r))
        | .unreachable => .det (st'.fin .ub)
```

```lean
-- lean/Toy/Capture/Lang.lean:348
def VProg.fuel (q : VProg) : Nat := q.blocks.length + 1
```

```lean
-- lean/Toy/Capture/Lang.lean:351-352
def semV (os : OpaqueSem) (q : VProg) : Den Run :=
  fun r => (runV os q q.fuel 0 (St.init r.1)).admits r.2
```

Examples: `semS_example_pos`, `semS_example_neg`, `semV_example_pos`, `semV_example_neg`, `semV_havoc_admits_any_trace`.

```lean
-- lean/Toy/Capture/Lang.lean:365-369
inductive CapErr where
  | unmodeledStmt
  | unmodeledTerm
  | erroneousConst
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:373-385
structure CapCfg where
  /-- default: map `trap next` to `goto next` (a no-op) instead of failing. -/
  defaultTrap : Bool
  /-- stringify: map `asm c` to `opaque c` instead of failing. -/
  stringifyAsm : Bool
  /-- swallow: map an erroneous constant to the value `0` instead of failing. -/
  swallowErrConst : Bool
  /-- keep the cleanup mark of each block (otherwise every block is marked
  normal). -/
  keepCleanup : Bool
  /-- keep the terminate reason (otherwise every reason becomes `abi`). -/
  keepReason : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Lang.lean:387-390
def capOperand (c : CapCfg) : SOperand → Except CapErr VOperand
  | .copy l => .ok (.copy l)
  | .const (.val n) => .ok (.const n)
  | .const .err => if c.swallowErrConst then .ok (.const 0) else .error .erroneousConst
```

```lean
-- lean/Toy/Capture/Lang.lean:392-403
def capStmt (c : CapCfg) : SStmt → Except CapErr VStmt
  | .assign d o =>
    match capOperand c o with
    | .ok vo => .ok (.assign d vo)
    | .error e => .error e
  | .placeMention l => .ok (.placeMention l)
  | .zstRead l => .ok (.zstRead l)
  | .emit o =>
    match capOperand c o with
    | .ok vo => .ok (.emit vo)
    | .error e => .error e
  | .asm t => if c.stringifyAsm then .ok (.opaque t) else .error .unmodeledStmt
```

```lean
-- lean/Toy/Capture/Lang.lean:405-411
def capStmts (c : CapCfg) : List SStmt → Except CapErr (List VStmt)
  | [] => .ok []
  | s :: ss =>
    match capStmt c s, capStmts c ss with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e
```

```lean
-- lean/Toy/Capture/Lang.lean:415-427
def capTerm (c : CapCfg) : STerm → Except CapErr VTerm
  | .goto t => .ok (.goto t)
  | .switchInt o ts ow =>
    match capOperand c o with
    | .ok vo => .ok (.switchInt vo ts ow)
    | .error e => .error e
  | .ret => .ok .ret
  | .resume => .ok .resume
  | .call pa nx uw => .ok (.call pa nx uw)
  | .drop _ l nx => .ok (.drop l nx)
  | .terminate r => .ok (.terminate (if c.keepReason then r else .abi))
  | .trap nx => if c.defaultTrap then .ok (.goto nx) else .error .unmodeledTerm
  | .unreachable => .ok .unreachable
```

```lean
-- lean/Toy/Capture/Lang.lean:429-433
def capBlock (c : CapCfg) (b : SBlock) : Except CapErr VBlock :=
  match capStmts c b.stmts, capTerm c b.term with
  | .ok ss, .ok t => .ok ⟨ss, t, if c.keepCleanup then b.cleanup else false⟩
  | .error e, _ => .error e
  | .ok _, .error e => .error e
```

```lean
-- lean/Toy/Capture/Lang.lean:435-441
def capBlocks (c : CapCfg) : List SBlock → Except CapErr (List VBlock)
  | [] => .ok []
  | b :: bs =>
    match capBlock c b, capBlocks c bs with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e
```

```lean
-- lean/Toy/Capture/Lang.lean:443-446
def capWith (c : CapCfg) (p : SProg) : Except CapErr VProg :=
  match capBlocks c p.blocks with
  | .ok bs => .ok ⟨bs⟩
  | .error e => .error e
```

```lean
-- lean/Toy/Capture/Lang.lean:450-452
def cfgFC : CapCfg :=
  { defaultTrap := false, stringifyAsm := false, swallowErrConst := false,
    keepCleanup := true, keepReason := true }
```

```lean
-- lean/Toy/Capture/Lang.lean:455
def capFC : SProg → Except CapErr VProg := capWith cfgFC
```

```lean
-- lean/Toy/Capture/Lang.lean:457
def capDefault : SProg → Except CapErr VProg := capWith { cfgFC with defaultTrap := true }
```

```lean
-- lean/Toy/Capture/Lang.lean:459
def capStringify : SProg → Except CapErr VProg := capWith { cfgFC with stringifyAsm := true }
```

```lean
-- lean/Toy/Capture/Lang.lean:461
def capSwallow : SProg → Except CapErr VProg := capWith { cfgFC with swallowErrConst := true }
```

```lean
-- lean/Toy/Capture/Lang.lean:463
def capNoCleanup : SProg → Except CapErr VProg := capWith { cfgFC with keepCleanup := false }
```

```lean
-- lean/Toy/Capture/Lang.lean:465
def capNoReason : SProg → Except CapErr VProg := capWith { cfgFC with keepReason := false }
```

```lean
-- lean/Toy/Capture/Lang.lean:469-471
def SStmt.isPlaceMention : SStmt → Bool
  | .placeMention _ => true
  | _ => false
```

```lean
-- lean/Toy/Capture/Lang.lean:473-475
def SStmt.isZstRead : SStmt → Bool
  | .zstRead _ => true
  | _ => false
```

```lean
-- lean/Toy/Capture/Lang.lean:478-479
def erasePlaceMentions (p : SProg) : SProg :=
  ⟨p.blocks.map fun b => { b with stmts := b.stmts.filter fun s => !s.isPlaceMention }⟩
```

```lean
-- lean/Toy/Capture/Lang.lean:482-483
def eraseZstReads (p : SProg) : SProg :=
  ⟨p.blocks.map fun b => { b with stmts := b.stmts.filter fun s => !s.isZstRead }⟩
```

```lean
-- lean/Toy/Capture/Lang.lean:489-495
def simplifyTrivialSwitches (p : SProg) : SProg :=
  ⟨p.blocks.map fun b =>
    { b with term :=
        match b.term with
        | .switchInt o ts ow =>
          if o != .const .err && ts.all (· == ow) then .goto ow else .switchInt o ts ow
        | t => t }⟩
```

```lean
-- lean/Toy/Capture/Lang.lean:498-502
def clearReplaceBlock (b : SBlock) : SBlock :=
  { b with term :=
      match b.term with
      | .drop _ l nx => .drop false l nx
      | t => t }
```

```lean
-- lean/Toy/Capture/Lang.lean:506-507
def clearReplace (p : SProg) : SProg :=
  ⟨p.blocks.map clearReplaceBlock⟩
```

Examples: `passes_example`.

```lean
-- lean/Toy/Capture/Lang.lean:512-514
def Outcome.isAbort : Outcome → Bool
  | .abort _ => true
  | _ => false
```

```lean
-- lean/Toy/Capture/Lang.lean:517
def ubFree : Run → Prop := fun r => r.2.out ≠ .ub
```

```lean
-- lean/Toy/Capture/Lang.lean:519
def returnsNormally : Run → Prop := fun r => r.2.out = .ret
```

```lean
-- lean/Toy/Capture/Lang.lean:521
def silent : Run → Prop := fun r => r.2.trace = []
```

```lean
-- lean/Toy/Capture/Lang.lean:523
def noAbort : Run → Prop := fun r => r.2.out.isAbort = false
```

```lean
-- lean/Toy/Capture/Lang.lean:525
def noAbortInCleanup : Run → Prop := fun r => r.2.out ≠ .abort .inCleanup
```

Examples: `specs_example`.

#### Simulation helpers (`Sim.lean`)

```lean
-- lean/Toy/Capture/Sim.lean:19-21
def liftS : Except Beh St → Except VRes St
  | .ok st => .ok st
  | .error b => .error (.det b)
```

```lean
-- lean/Toy/Capture/Sim.lean:25-29
structure CfgFCExceptAsm (c : CapCfg) : Prop where
  noDefault : c.defaultTrap = false
  noSwallow : c.swallowErrConst = false
  keepCl : c.keepCleanup = true
  keepR : c.keepReason = true
```

```lean
-- lean/Toy/Capture/Sim.lean:390
def capFCAccepts (p : SProg) : Prop := ∃ q, capFC p = .ok q
```

```lean
-- lean/Toy/Capture/Sim.lean:398-401
def capFCOut (p : SProg) : VProg :=
  match capFC p with
  | .ok q => q
  | .error _ => ⟨[]⟩
```

#### Programs used below (`Examples.lean`)

```lean
-- lean/Toy/Capture/Examples.lean:15
def pPM : SProg := ⟨[⟨[.placeMention 0], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:17
def pZst : SProg := ⟨[⟨[.zstRead 0], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:20
def pSw : SProg := ⟨[⟨[], .switchInt (.copy 1) [1] 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:22
def pRet : SProg := ⟨[⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:24
def pTrap : SProg := ⟨[⟨[], .trap 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:26
def pAsm : SProg := ⟨[⟨[.asm 7], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:28
def pErr : SProg := ⟨[⟨[.emit (.const .err)], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:31-33
def pCl : SProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, true⟩, ⟨[], .resume, true⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:35-37
def pNo : SProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, false⟩, ⟨[], .resume, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:40-41
def pTerm (r : Reason) : SProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩, ⟨[], .terminate r, true⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:43
def pDrop (rep : Bool) : SProg := ⟨[⟨[], .drop rep 0 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:46-48
def pOk : SProg :=
  ⟨[⟨[.assign 1 (.const (.val 5)), .placeMention 1], .drop true 1 1, false⟩,
    ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:51
def pSwConstErr : SProg := ⟨[⟨[], .switchInt (.const .err) [1] 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:54
def qRet : VProg := ⟨[⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:55
def qGoto : VProg := ⟨[⟨[], .goto 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:56
def qPM : VProg := ⟨[⟨[.placeMention 0], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:57
def qAsm : VProg := ⟨[⟨[.opaque 7], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:58
def qZero : VProg := ⟨[⟨[.emit (.const 0)], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:59-61
def qUnw : VProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, false⟩, ⟨[], .resume, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:62-63
def qTermAbi : VProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩, ⟨[], .terminate .abi, true⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:64
def qDrop : VProg := ⟨[⟨[], .drop 0 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:65-66
def qOk : VProg :=
  ⟨[⟨[.assign 1 (.const 5)], .drop 1 1, false⟩, ⟨[], .ret, false⟩]⟩
```

```lean
-- lean/Toy/Capture/Examples.lean:69
def trustAll : VProg → (Run → Prop) → Prop := fun _ _ => True
```

```lean
-- lean/Toy/Capture/Examples.lean:269
def pipePM : List (Pass SProg) := [⟨.erasing, erasePlaceMentions⟩]
```

```lean
-- lean/Toy/Capture/Examples.lean:271
def pipeOk : List (Pass SProg) := [⟨.erasing, erasePlaceMentions⟩, ⟨.equiv, clearReplace⟩]
```

```lean
-- lean/Toy/Capture/Examples.lean:337
def qEmitOpaque : VProg := ⟨[⟨[.emit (.const 42), .opaque 7], .ret, false⟩]⟩
```

#### Pipelines and programs used in counterexamples (`Counterexamples.lean`)

```lean
-- lean/Toy/Capture/Counterexamples.lean:47
def pipeZst : List (Pass SProg) := [⟨.erasing, eraseZstReads⟩]
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:49
def pipeSw : List (Pass SProg) := [⟨.erasing, simplifyTrivialSwitches⟩]
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:51
def pipeMis : List (Pass SProg) := [⟨.equiv, erasePlaceMentions⟩]
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:305
def passPM : Pass SProg := ⟨.erasing, erasePlaceMentions⟩
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:439-441
def qCl : VProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, true⟩, ⟨[], .resume, true⟩]⟩
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:678-686
def pLoopDead : SProg :=
  ⟨[ ⟨[.assign 1 (.const (.val 0)), .assign 2 (.const (.val 0))], .goto 1, false⟩,
     ⟨[], .switchInt (.copy 2) [2] 4, false⟩,
     ⟨[], .goto 3, false⟩,
     ⟨[.assign 2 (.copy 1), .assign 1 (.const (.val 1))], .goto 1, false⟩,
     ⟨[], .ret, false⟩,
     ⟨[], .ret, false⟩,
     ⟨[], .ret, false⟩,
     ⟨[], .ret, false⟩ ]⟩
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:689
def pLoopTrim : SProg := ⟨pLoopDead.blocks.take 5⟩
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:692-693
def pLoopUB : SProg :=
  ⟨(pLoopDead.blocks.take 4) ++ [⟨[], .unreachable, false⟩]⟩
```

#### Flags (`Flags.lean`)

```lean
-- lean/Toy/Capture/Flags.lean:17-21
inductive Response where
  | admitted
  | rejected
  | omitted
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Flags.lean:25-27
structure Backend (F A : Type) where
  respond : F → Response
  build : List F → A
```

```lean
-- lean/Toy/Capture/Flags.lean:32-35
def Backend.run {F A : Type} (be : Backend F A) (cfg : List F) : Except F A :=
  match cfg.find? (fun f => be.respond f == .rejected) with
  | some f => .error f
  | none => .ok (be.build (cfg.filter (fun f => be.respond f == .admitted)))
```

```lean
-- lean/Toy/Capture/Flags.lean:39-40
def HonoursAdmitted {F A : Type} (Holds : F → A → Prop) (be : Backend F A) : Prop :=
  ∀ fs f, (∀ g ∈ fs, be.respond g = .admitted) → f ∈ fs → Holds f (be.build fs)
```

```lean
-- lean/Toy/Capture/Flags.lean:45-48
def OmissionObservableOnAdmitted {F A : Type} (Holds : F → A → Prop) (be : Backend F A) :
    Prop :=
  ∀ f, be.respond f = .omitted →
    ∃ fs, (∀ g ∈ fs, be.respond g = .admitted) ∧ ¬ Holds f (be.build fs)
```

```lean
-- lean/Toy/Capture/Flags.lean:53-54
def FlagContractSound {F A : Type} (Holds : F → A → Prop) (be : Backend F A) : Prop :=
  ∀ cfg a, be.run cfg = .ok a → ∀ f ∈ cfg, Holds f a
```

```lean
-- lean/Toy/Capture/Flags.lean:57-58
def NeverOmits {F A : Type} (be : Backend F A) : Prop :=
  ∀ f, be.respond f ≠ .omitted
```

Examples: `run_example`, `beOmit_honours`, `beFC_honours`, `beOmit_observable`, `beFC_observable`, `beSan_instance`, `flag_nonvacuous`.

```lean
-- lean/Toy/Capture/Flags.lean:155-156
def beOmit : Backend Nat (List Nat) :=
  ⟨fun f => if f = 0 then .admitted else if f = 1 then .rejected else .omitted, id⟩
```

```lean
-- lean/Toy/Capture/Flags.lean:159-160
def beFC : Backend Nat (List Nat) :=
  ⟨fun f => if f = 1 then .rejected else .admitted, id⟩
```

```lean
-- lean/Toy/Capture/Flags.lean:163
def instruments (f : Nat) (a : List Nat) : Prop := f ∈ a
```

```lean
-- lean/Toy/Capture/Flags.lean:206-207
def beSan : Backend Bool (Bool × Bool) :=
  ⟨fun b => if b then .omitted else .admitted, fun fs => (fs.contains false, fs.contains true)⟩
```

```lean
-- lean/Toy/Capture/Flags.lean:211-212
def sanHolds (f : Bool) (a : Bool × Bool) : Prop :=
  if f then (a.1 = true → a.2 = true) else a.1 = true
```

```lean
-- lean/Toy/Capture/Flags.lean:299-306
def checkedRun {F A : Type} (be : Backend F A) (check : F → A → Bool) (cfg : List F) :
    Except F A :=
  match be.run cfg with
  | .error f => .error f
  | .ok a =>
    match cfg.find? (fun f => !check f a) with
    | some f => .error f
    | none => .ok a
```

```lean
-- lean/Toy/Capture/Flags.lean:424-427
inductive Item where
  | plain (isUnsafe : Bool)
  | macro (external : Bool) (expansion : List Bool)
  deriving DecidableEq, Repr
```

```lean
-- lean/Toy/Capture/Flags.lean:430-433
def expand : List Item → List Bool
  | [] => []
  | .plain u :: rest => u :: expand rest
  | .macro _ e :: rest => e ++ expand rest
```

```lean
-- lean/Toy/Capture/Flags.lean:438-441
def srcAuditExemptExternal : List Item → Bool
  | [] => true
  | .plain u :: rest => !u && srcAuditExemptExternal rest
  | .macro ext e :: rest => (ext || !e.any id) && srcAuditExemptExternal rest
```

Negative examples (the audit rejects a program with exactly one unsafe plain item, and a program with exactly one non-external macro whose expansion is unsafe):

```lean
-- lean/Toy/Capture/Supplement.lean:16-18
theorem srcAuditExemptExternal_example_neg :
    srcAuditExemptExternal [.plain true] = false ∧
    srcAuditExemptExternal [.macro false [true]] = false := by
```

```lean
-- lean/Toy/Capture/Flags.lean:445
def irAudit (prog : List Item) : Bool := !(expand prog).any id
```

```lean
-- lean/Toy/Capture/Flags.lean:475
def progAuditOk : List Item := [.plain false, .macro false [false], .macro true [false]]
```

### Cards

Each card gives the plain claim, kind, tier and depth, the verbatim Lean statement(s), the hypothesis ledger, the non-vacuity witness (and the positive control where one is given), prior art and the design question; its non-claims are listed under `## Boundaries`. "Tight" means: a named Lean counterexample satisfies all the other hypotheses and the conclusion fails; the class of the witness is stated.

#### `transfer-to-capture-input` (theorem)

**Plain claim.** For all types `S`, `V`, `E`, `B`, source semantics `semS`, verifier semantics `semV`, capture `cap : S → Except E V`, verdict relation `verified`, programs `p`, `q` and specification `spec : B → Prop`: if `verified` is sound for `semV` (`VerifierSound`) and `cap` over-approximates on its ok-image (`OverApproxOnOk`: every run of a successfully captured program is a run of its capture), then `cap p = .ok q` and `verified q spec` imply `Sat (semS p) spec`. When the capture is taken after a pipeline, `p` is the pipeline output, not the original source.

**Kind / tier / depth.** theorem / T0 (The standard soundness argument of translation validation and semantics-preserving compilation (backward simulation implies preservation of every specification), restated for a partial capture.) / definitional.

**Lean statement.**

```lean
-- lean/Toy/Capture/Basic.lean:190-194
theorem transfer_to_capture_input {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    {p : S} {q : V} {spec : B → Prop}
    (hok : cap p = .ok q) (hver : verified q spec) : Sat (semS p) spec :=
```

**Hypothesis ledger.**
- `hV : VerifierSound semV verified` — verdicts must be true of the verifier semantics. tight: `cex_capInput_hV` (concrete toy: `capFC`, `p = pPM`, `q = qPM`, the verdict relation `trustAll` accepts `ubFree` for `qPM`).
- `hcap : OverApproxOnOk semS semV cap` — every run of a successfully captured program must be a run of its capture. tight: `cex_capInput_hcap` (concrete toy: `capDefault` maps `pTrap` to `qGoto`; spec `returnsNormally`).
- `hok : cap p = .ok q` — ties `q` to `p`. tight: `cex_capInput_hok` (concrete toy: `qRet` is verified UB-free but is not the capture of `pPM`).
- `hver : verified q spec` — the verdict. tight: `cex_capInput_hver` (concrete toy: the capture `qPM` of `pPM` is not verified UB-free).

**Non-vacuity witness.** `transfer_to_capture_input_nonvacuous`: the exact verifier for `semV os`, `capFC`, `p = pRet`, `q = qRet`, spec `ubFree`.

**Non-claims.** Listed under `## Boundaries`, subsection `transfer-to-capture-input`.

**Prior art.**
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), §2.1 "Notions of semantic preservation": Definition 2 (backward simulation, ∀B, C ⇓ B ⟹ S ⇓ B), Definition 3 (backward simulation for safe programs), Definition 4 (forward simulation), Definition 6 (preservation of a specification, S ⊨ Spec ⟹ C ⊨ Spec, where C ⊨ Spec means that every behaviour of C satisfies Spec), and the remarks that backward simulation for safe programs implies preservation of every specification, and that forward simulation implies backward simulation if C is deterministic. In a capture, the verified program (the captured `q`) plays the role of S and the program concluded about (`p`) the role of C.
- A. Pnueli, M. Siegel, E. Singerman, "Translation Validation", TACAS 1998, LNCS 1384, pp. 151–166, doi:10.1007/BFb0054170 (publisher's abstract: each run of the translator is followed by a validation that the target code correctly implements the source, with correct implementation formalized as a refinement relation).
- S. Blazy, Z. Dargaye, X. Leroy, "Formal Verification of a C Compiler Front-End", FM 2006, LNCS 4085, pp. 460–475, doi:10.1007/11813040_31 (publisher's abstract: machine-checked proof of observational semantic equivalence between source and generated code for a front-end from a subset of C to Cminor). The direction differs from a capture: a compiler correctness theorem of this kind constrains the behaviours of the generated code by those of the source, and in CompCert it is conditional on the source not going wrong (X. Leroy, JAR 2009, §2.1, Definition 3), whereas transfer through a capture with every sound verifier needs every source run, UB runs included, to be a run of the captured program (`transferSound_all_sound_verifiers_iff_overApproxOnOk`).
- reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`, cards `ub-check-of-output-complete-under-reverse-refinement` (`Toy.ZstAssume.ubFree_src_of_ubFree_tgt_of_refinesWT_rev`, `Toy.ZstAssume.ubFree_src_of_ubFree_output_of_revChainWT`: UB-freedom of an output transfers to a source that whole-trace-refines it, also along a pipeline whose every pass's input refines its output), `ub-check-of-output-incomplete` (`Toy.ZstAssume.ubCheck_of_output_misses_source_ub`) and `delete-zero-size-access-equivalence-exact-condition` (`Toy.ZstAssume.deleteZeroSizeAccess_equivPP_iff`); cited, not imported.

**Design question.** What must a capture guarantee for a verifier's verdict about the captured program to say anything about the captured program's input?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `transfer-through-pipeline-losing-no-runs` (theorem)

**Plain claim.** For every pipeline `pipe`, source `src`, program `q` and specification `spec`: if `verified` is sound for `semV`, `cap` over-approximates on its ok-image, and every pass of `pipe`, whatever its tag, loses no run at its actual input (`LosesNoBehaviourAtInputs`: the input of pass `i` is the program the passes before it produce from `src`), then `cap (runPipe pipe src) = .ok q` and `verified q spec` imply `Sat (semS src) spec`.

**Kind / tier / depth.** theorem / T0 (Finite composition of reverse inclusions with `transfer-to-capture-input`; the same composition is mechanized for UB-freedom along a pipeline in the cited zero-size-access package.) / shallow.

**Lean statement.**

```lean
-- lean/Toy/Capture/Basic.lean:220-226
theorem transfer_of_losesNoBehaviourAtInputs {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (pipe : List (Pass S)) (src : S) (q : V) (spec : B → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    (hpipe : LosesNoBehaviourAtInputs semS pipe src)
    (hok : cap (runPipe pipe src) = .ok q) (hver : verified q spec) :
    Sat (semS src) spec :=
```

**Hypothesis ledger.**
- `hV : VerifierSound semV verified` — verdicts must be true of the verifier semantics. tight: `cex_pipeline_hV` (concrete toy, empty pipeline, `capFC`, source `pPM`, `trustAll`).
- `hcap : OverApproxOnOk semS semV cap` — every run of a successfully captured program must be a run of its capture. tight: `cex_pipeline_hcap` (concrete toy, empty pipeline, `capDefault` on `pTrap`).
- `hpipe : LosesNoBehaviourAtInputs semS pipe src` — no pass may lose a source run at its actual input. tight: `cex_pipeline_hpipe` (concrete toy: `pipePM` (exactly one pass, erasing place mentions) at `pPM`).
- `hok : cap (runPipe pipe src) = .ok q` — ties `q` to `src`. tight: `cex_pipeline_hok` (concrete toy, empty pipeline: `qRet` is not the capture of `pPM`).
- `hver : verified q spec` — the verdict. tight: `cex_pipeline_hver` (concrete toy, empty pipeline: `qPM` is not verified UB-free).

**Non-vacuity witness.** `transfer_of_losesNoBehaviourAtInputs_nonvacuous`: `pipeOk` (an erasing pass, then an equiv pass) at `pOk`, `capFC`, `q = qOk`, exact verifier, spec `ubFree`.

**Non-claims.** Listed under `## Boundaries`, subsection `transfer-through-pipeline-losing-no-runs`.

**Prior art.**
- reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`, cards `ub-check-of-output-complete-under-reverse-refinement` (`Toy.ZstAssume.ubFree_src_of_ubFree_tgt_of_refinesWT_rev`, `Toy.ZstAssume.ubFree_src_of_ubFree_output_of_revChainWT`: UB-freedom of an output transfers to a source that whole-trace-refines it, also along a pipeline whose every pass's input refines its output), `ub-check-of-output-incomplete` (`Toy.ZstAssume.ubCheck_of_output_misses_source_ub`) and `delete-zero-size-access-equivalence-exact-condition` (`Toy.ZstAssume.deleteZeroSizeAccess_equivPP_iff`); cited, not imported.
- A. Pnueli, M. Siegel, E. Singerman, "Translation Validation", TACAS 1998, LNCS 1384, pp. 151–166, doi:10.1007/BFb0054170 (publisher's abstract: each run of the translator is followed by a validation that the target code correctly implements the source, with correct implementation formalized as a refinement relation).
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), §2.1 "Notions of semantic preservation": Definition 2 (backward simulation, ∀B, C ⇓ B ⟹ S ⇓ B), Definition 3 (backward simulation for safe programs), Definition 4 (forward simulation), Definition 6 (preservation of a specification, S ⊨ Spec ⟹ C ⊨ Spec, where C ⊨ Spec means that every behaviour of C satisfies Spec), and the remarks that backward simulation for safe programs implies preservation of every specification, and that forward simulation implies backward simulation if C is deterministic. In a capture, the verified program (the captured `q`) plays the role of S and the program concluded about (`p`) the role of C.

**Design question.** What is the weakest per-pass condition, in this model, under which a verdict about captured IR transfers through every pass before the capture point?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `transfer-relative-to-erasing-set` (theorem)

**Plain claim.** For every pipeline `pipe`, source `src`, program `q` and specification `spec`: if `verified` is sound for `semV`, `cap` over-approximates on its ok-image, every `equiv`-tagged pass of `pipe` preserves the denotation of every program (`EquivTagSound`, for all programs, not only those it is applied to), and every pass in the erasing set `E_k` (`InErasingSet`: the `erasing`-tagged passes of `pipe`) loses no run at its actual input (`ErasingSetPrecondition`, equivalently `erasingSetPrecondition_iff_forall_inErasingSet`), then `cap (runPipe pipe src) = .ok q` and `verified q spec` imply `Sat (semS src) spec`. Its one-pass instance is `transfer_single_pass`.

**Kind / tier / depth.** theorem / T1 (Translation-validation folklore, made precise relative to a stated set of UB-erasing passes before the capture point.) / shallow.

**Lean statement.**

```lean
-- lean/Toy/Capture/Basic.lean:235-242
theorem transfer_relative_to_erasingSet {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (pipe : List (Pass S)) (src : S) (q : V) (spec : B → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    (hEq : ∀ P ∈ pipe, EquivTagSound semS P)
    (hE : ErasingSetPrecondition semS pipe src)
    (hok : cap (runPipe pipe src) = .ok q) (hver : verified q spec) :
    Sat (semS src) spec :=
```

**Hypothesis ledger.**
- `hV : VerifierSound semV verified` — verdicts must be true of the verifier semantics. tight: `cex_hV` (concrete toy, empty pipeline, `trustAll`).
- `hcap : OverApproxOnOk semS semV cap` — every run of a successfully captured program must be a run of its capture. tight: `cex_hcap_default` (concrete toy, empty pipeline; also `cex_hcap_stringify_noop`, `cex_hcap_swallow`, `cex_hcap_noCleanup`, `cex_hcap_noReason`).
- `hEq : ∀ P ∈ pipe, EquivTagSound semS P` — an `equiv` tag is trusted without a per-input check, so the tag's promise is stated for every program; the proof uses no more than that each `equiv` pass loses no run at its actual input (see the non-claims). tight: `cex_hEq` (concrete toy: the place-mention eraser mis-tagged `equiv` (erasing set empty, so `hE` holds vacuously)).
- `hE : ErasingSetPrecondition semS pipe src` — erasing passes must lose no run at their actual inputs. tight: `cex_erasingSet_placeMention` (concrete toy: exactly one erasing pass removing place mentions, source `pPM` (UB on input 0); also the zero-size-read and equal-target switch variants).
- `hok : cap (runPipe pipe src) = .ok q` — ties `q` to `src`. tight: `cex_hok` (concrete toy, empty pipeline).
- `hver : verified q spec` — the verdict. tight: `cex_hver` (concrete toy, empty pipeline).

**Non-vacuity witness.** `transfer_relative_to_erasingSet_nonvacuous`: `pipeOk` at `pOk` (erasing set {0}, `InErasingSet pipeOk 0`; equiv pass `clearReplace`), `capFC`, `q = qOk`, exact verifier, spec `ubFree`. For the one-pass instance: `transfer_single_pass_nonvacuous`.

**Positive control.** `erasure_disabled_control`.

**Non-claims.** Listed under `## Boundaries`, subsection `transfer-relative-to-erasing-set`.

**Prior art.**
- A. Pnueli, M. Siegel, E. Singerman, "Translation Validation", TACAS 1998, LNCS 1384, pp. 151–166, doi:10.1007/BFb0054170 (publisher's abstract: each run of the translator is followed by a validation that the target code correctly implements the source, with correct implementation formalized as a refinement relation).
- S. Blazy, Z. Dargaye, X. Leroy, "Formal Verification of a C Compiler Front-End", FM 2006, LNCS 4085, pp. 460–475, doi:10.1007/11813040_31 (publisher's abstract: machine-checked proof of observational semantic equivalence between source and generated code for a front-end from a subset of C to Cminor). The direction differs from a capture: a compiler correctness theorem of this kind constrains the behaviours of the generated code by those of the source, and in CompCert it is conditional on the source not going wrong (X. Leroy, JAR 2009, §2.1, Definition 3), whereas transfer through a capture with every sound verifier needs every source run, UB runs included, to be a run of the captured program (`transferSound_all_sound_verifiers_iff_overApproxOnOk`).
- reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`, cards `ub-check-of-output-complete-under-reverse-refinement` (`Toy.ZstAssume.ubFree_src_of_ubFree_tgt_of_refinesWT_rev`, `Toy.ZstAssume.ubFree_src_of_ubFree_output_of_revChainWT`: UB-freedom of an output transfers to a source that whole-trace-refines it, also along a pipeline whose every pass's input refines its output), `ub-check-of-output-incomplete` (`Toy.ZstAssume.ubCheck_of_output_misses_source_ub`) and `delete-zero-size-access-equivalence-exact-condition` (`Toy.ZstAssume.deleteZeroSizeAccess_equivPP_iff`); cited, not imported.
- reference corpus package `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches`, cards `place-mention-erasure-equivalence-exact-condition-static-slots` (`Toy.PlaceEval.erasePlaceMention_equivPP_iff_slots`: exact condition for deleting a place mention to be a prefix-preserving equivalence), `equal-target-switch-erasure-equivalence-exact-condition-static-slots` (`Toy.PlaceEval.switchToGoto_equivPP_iff_slots`: the same for replacing an equal-target switch by a goto) and `ub-check-after-erasure-incomplete` (`Toy.PlaceEval.ubCheck_after_erasePlaceMention_misses_place_ub`: an exact UB checker accepts the edited program although the original is not UB-free); cited, not imported.
- reference corpus package `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations`, cards `R2` (`Toy.Inline.inline_behEquiv_retTemp_of_capsEq`: under stated side conditions, inlining a call site is a behavioural equivalence, an instance of a pass whose `equiv` tag would be sound) and `R4` (`Toy.Inline.terminalHolds_iff_of_behEquivAt`: a property of every halted run transfers both ways across behavioural equivalence); cited, not imported.
- reference corpus package `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets`, card `R6-spec-transfer` (`Toy.MonoShim.closed_target_meets_specs_in_source_semantics`: verdicts on a closed monomorphic target transfer to the source semantics under its stated hypotheses, in the partial-correctness sense); it concerns which items are captured, while this package concerns what a capture of one program must preserve; cited, not imported.
- [documentation and source; connection to the toy: derived (modeling bridge)] rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_mir_transform/src/lib.rs L649–663 (`run_runtime_cleanup_passes`: passes `LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`, run with `Some(MirPhase::Runtime(RuntimePhase::PostCleanup))`), L596–598 (call and assertion of `Runtime(PostCleanup)`); compiler/rustc_mir_transform/src/remove_place_mention.rs L10–12 (`is_enabled` returns `!sess.opts.unstable_opts.mir_preserve_ub`); compiler/rustc_session/src/options.rs L2469–2471 (help text of `mir_preserve_ub`: "keep place mention statements and reads in trivial SwitchInt terminators, which are interpreted e.g., by miri; implies -Zmir-opt-level=0 (default: no)"); compiler/rustc_mir_transform/src/simplify.rs L128–130 and L307–309 ("Removing a `SwitchInt` terminator may remove reads that result in UB, so we must not apply this optimization before borrowck or when `-Zmir-preserve-ub` is set."; the same comment is at rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, simplify.rs L309–311).

**Design question.** Which passes before the capture point must preserve UB (or have their erasure precondition discharged at the actual input) for a UB-freedom proof of the captured IR to transfer to the source?

Basis: execution (Lean kernel check) for the Lean statements of this card.

Basis: derived (modeling bridge) for the bracketed rust-lang/rust items under Prior art: documentation and source at the pinned revision, connected to the toy by the reasoning in the subsection *Modeling bridge* below; not a theorem.

#### `capture-after-ub-erasing-pass` (counterexample)

**Plain claim.** In the concrete toy, with the fail-closed capture `capFC`, the exact verifier for `semV .noop` and a pipeline of exactly one erasing pass, the captured program is verified `ubFree` while the source is not, for place-mention erasure on `pPM`, zero-size-read erasure on `pZst`, and equal-target switch erasure on `pSw`; in each instance every hypothesis of `transfer_relative_to_erasingSet` except the erasing-set precondition holds, and the precondition fails.

**Kind / tier / depth.** counterexample / T1 (Instances, in this toy, of the known incompleteness of checking the output of UB-erasing passes.) / definitional.

**Lean statements.**

```lean
-- lean/Toy/Capture/Counterexamples.lean:85-92
theorem cex_erasingSet_placeMention :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ pipePM, EquivTagSound semS P) ∧
    capFC (runPipe pipePM pPM) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ ErasingSetPrecondition semS pipePM pPM ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:98-105
theorem cex_erasingSet_zstRead :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ pipeZst, EquivTagSound semS P) ∧
    capFC (runPipe pipeZst pZst) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ ErasingSetPrecondition semS pipeZst pZst ∧
    ¬ Sat (semS pZst) ubFree := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:115-122
theorem cex_erasingSet_trivialSwitch :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ pipeSw, EquivTagSound semS P) ∧
    capFC (runPipe pipeSw pSw) = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto ubFree ∧
    ¬ ErasingSetPrecondition semS pipeSw pSw ∧
    ¬ Sat (semS pSw) ubFree := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** Concrete statements; control `erasure_disabled_control` (without the erasing pass, the capture of `pPM` keeps the place mention and is not verified `ubFree`).

**Positive control.** `erasure_disabled_control`.

**Non-claims.** Listed under `## Boundaries`, subsection `capture-after-ub-erasing-pass`.

**Prior art.**
- reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`, cards `ub-check-of-output-complete-under-reverse-refinement` (`Toy.ZstAssume.ubFree_src_of_ubFree_tgt_of_refinesWT_rev`, `Toy.ZstAssume.ubFree_src_of_ubFree_output_of_revChainWT`: UB-freedom of an output transfers to a source that whole-trace-refines it, also along a pipeline whose every pass's input refines its output), `ub-check-of-output-incomplete` (`Toy.ZstAssume.ubCheck_of_output_misses_source_ub`) and `delete-zero-size-access-equivalence-exact-condition` (`Toy.ZstAssume.deleteZeroSizeAccess_equivPP_iff`); cited, not imported.
- reference corpus package `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches`, cards `place-mention-erasure-equivalence-exact-condition-static-slots` (`Toy.PlaceEval.erasePlaceMention_equivPP_iff_slots`: exact condition for deleting a place mention to be a prefix-preserving equivalence), `equal-target-switch-erasure-equivalence-exact-condition-static-slots` (`Toy.PlaceEval.switchToGoto_equivPP_iff_slots`: the same for replacing an equal-target switch by a goto) and `ub-check-after-erasure-incomplete` (`Toy.PlaceEval.ubCheck_after_erasePlaceMention_misses_place_ub`: an exact UB checker accepts the edited program although the original is not UB-free); cited, not imported.

**Design question.** Does a verdict about IR captured after a UB-erasing pass say anything about UB in the source?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `fail-open-capture-variants-unsound` (counterexample)

**Plain claim.** In the concrete toy, with the empty pipeline and the exact verifier for `semV .noop`, for each of the three fail-open captures there is a named program with an unmodeled construct that the capture accepts, and a specification that the verifier proves of the captured program and that is false of the source: `capDefault` on `pTrap` (specification `returnsNormally`), `capStringify` on `pAsm` with `opaque` read as a no-op (specification `silent`, no output), `capSwallow` on `pErr` (specification `returnsNormally`); in each instance every hypothesis of `transfer_relative_to_erasingSet` except over-approximation holds, and over-approximation fails.

**Kind / tier / depth.** counterexample / T1 (Folklore made precise.) / definitional.

**Lean statements.**

```lean
-- lean/Toy/Capture/Counterexamples.lean:143-150
theorem cex_hcap_default :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pTrap ∧
    capDefault (runPipe [] pTrap) = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧
    ¬ Sat (semS pTrap) returnsNormally := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:160-167
theorem cex_hcap_stringify_noop :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pAsm ∧
    capStringify (runPipe [] pAsm) = .ok qAsm ∧
    exactVerifier (semV .noop) qAsm silent ∧
    ¬ OverApproxOnOk semS (semV .noop) capStringify ∧
    ¬ Sat (semS pAsm) silent :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:175-182
theorem cex_hcap_swallow :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pErr ∧
    capSwallow (runPipe [] pErr) = .ok qZero ∧
    exactVerifier (semV .noop) qZero returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capSwallow ∧
    ¬ Sat (semS pErr) returnsNormally := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** Concrete statements; the fail-closed capture rejects the three programs (`capFC_pTrap`, `capFC_pAsm`, `capFC_pErr`), and each variant agrees with `capFC` wherever `capFC` succeeds (`failOpenVariants_eq_partialExtend_capFC`).

**Positive control.** `capFC_pTrap`, `capFC_pAsm`, `capFC_pErr`.

**Non-claims.** Listed under `## Boundaries`, subsection `fail-open-capture-variants-unsound`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** Why must a capture reject, rather than default, stringify or swallow, constructs it does not model, unless the verifier reads the placeholder as an arbitrary effect?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `dropped-metadata-unsound` (counterexample)

**Plain claim.** In the concrete toy, `capNoCleanup` maps `pCl` (aborts with reason `inCleanup`) and `pNo` (unwinds) to the same `qUnw`, and `capNoReason` maps `pTerm .abi` and `pTerm .inCleanup` to the same `qTermAbi`, although in each pair the two programs do not admit the same runs; with the empty pipeline and the exact verifier for `semV .noop`, the verifier proves `noAbort` of `qUnw` (false of `pCl`) and `noAbortInCleanup` of `qTermAbi` (false of `pTerm .inCleanup`), and every hypothesis of `transfer_relative_to_erasingSet` except over-approximation holds.

**Kind / tier / depth.** counterexample / T1 (Folklore made precise.) / definitional.

**Lean statements.**

```lean
-- lean/Toy/Capture/Counterexamples.lean:194-196
theorem cleanupMark_merged_pair :
    capNoCleanup pCl = .ok qUnw ∧ capNoCleanup pNo = .ok qUnw ∧
    ¬ DenEquiv (semS pCl) (semS pNo) :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:220-222
theorem terminateReason_merged_pair :
    capNoReason (pTerm .abi) = .ok qTermAbi ∧ capNoReason (pTerm .inCleanup) = .ok qTermAbi ∧
    ¬ DenEquiv (semS (pTerm .abi)) (semS (pTerm .inCleanup)) :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:203-210
theorem cex_hcap_noCleanup :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pCl ∧
    capNoCleanup (runPipe [] pCl) = .ok qUnw ∧
    exactVerifier (semV .noop) qUnw noAbort ∧
    ¬ OverApproxOnOk semS (semV .noop) capNoCleanup ∧
    ¬ Sat (semS pCl) noAbort := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:227-234
theorem cex_hcap_noReason :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] (pTerm .inCleanup) ∧
    capNoReason (runPipe [] (pTerm .inCleanup)) = .ok qTermAbi ∧
    exactVerifier (semV .noop) qTermAbi noAbortInCleanup ∧
    ¬ OverApproxOnOk semS (semV .noop) capNoReason ∧
    ¬ Sat (semS (pTerm .inCleanup)) noAbortInCleanup := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `cleanupMark_merged_pair` and `terminateReason_merged_pair` exhibit the two merged pairs; positive control: the fail-closed capture separates both pairs (`capFC_pCl_ne_pNo`, `capFC_pTerm_abi_ne_inCleanup`).

**Positive control.** `capFC_pCl_ne_pNo`, `capFC_pTerm_abi_ne_inCleanup`.

**Non-claims.** Listed under `## Boundaries`, subsection `dropped-metadata-unsound`.

**Prior art.**
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_middle/src/mir/syntax.rs L1046–1055 (`UnwindTerminateReason`: "The reason we are terminating the process during unwinding.", variants `Abi` ("Unwinding is just not possible given the ABI of this function.") and `InCleanup` ("We were already cleaning up for an ongoing unwind, and a *second*, *nested* unwind was triggered by the drop glue.")); L675 (within the list of cleanup-block restrictions at L673–676): "1. All `unwind` fields in them must be `UnwindAction::Terminate` or `UnwindAction::Unreachable`."; compiler/rustc_middle/src/mir/mod.rs L1337–1341 (field `is_cleanup`: "If true, this block lies on an unwind path. This is used during codegen where distinct kinds of basic blocks may be generated (particularly for MSVC cleanup). Unwind blocks must only branch to other unwind blocks.").

**Design question.** Which metadata must a capture carry across, and what goes wrong when it collapses two values of it?

Basis: execution (Lean kernel check) for the Lean statements of this card.

Basis: derived (modeling bridge) for the bracketed rust-lang/rust items under Prior art: documentation and source at the pinned revision, connected to the toy by the reasoning in the subsection *Modeling bridge* below; not a theorem.

#### `no-faithful-semantics-for-merged-pair` (impossibility)

**Plain claim.** For every capture `cap`, source semantics `semS` and programs `p₁`, `p₂`, `q`: if `cap p₁ = .ok q`, `cap p₂ = .ok q`, and `p₁`, `p₂` do not admit the same runs, then no verifier semantics makes `cap` faithful at both `p₁` and `p₂` (`no_semV_faithful_at_merged_pair`), and hence none makes `cap` faithful on its ok-image (`not_faithfulOnOk_of_merged_pair`).

**Kind / tier / depth.** impossibility / T0 (Elementary: no function of the captured program can separate two programs that the capture identifies.) / definitional.

**Lean statements.**

```lean
-- lean/Toy/Capture/Basic.lean:263-268
theorem no_semV_faithful_at_merged_pair {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) {p₁ p₂ : S} {q : V}
    (h₁ : cap p₁ = .ok q) (h₂ : cap p₂ = .ok q)
    (hdiff : ¬ DenEquiv (semS p₁) (semS p₂)) :
    ∀ semV : V → Den B,
      ¬ (FaithfulAt semS semV cap p₁ ∧ FaithfulAt semS semV cap p₂) := by
```

```lean
-- lean/Toy/Capture/Basic.lean:274-278
theorem not_faithfulOnOk_of_merged_pair {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) {p₁ p₂ : S} {q : V}
    (h₁ : cap p₁ = .ok q) (h₂ : cap p₂ = .ok q)
    (hdiff : ¬ DenEquiv (semS p₁) (semS p₂)) :
    ∀ semV : V → Den B, ¬ FaithfulOnOk semS semV cap :=
```

**Hypothesis ledger.**
- `h₁ : cap p₁ = .ok q` — the merge (first program). tight: `merge_hypotheses_tight` (concrete toy: `capFC` maps `pCl` to `qCl` and `pNo` to `qUnw ≠ qCl`; take `q = qUnw`).
- `h₂ : cap p₂ = .ok q` — the merge (second program). tight: `merge_hypotheses_tight` (concrete toy: as for `h₁`, take `q = qCl`).
- `hdiff : ¬ DenEquiv (semS p₁) (semS p₂)` — the merged programs must differ in runs. tight: `dropReplace_merged_yet_faithful` (concrete toy: `pDrop true`, `pDrop false` (they differ in nothing but the replace flag)).

**Non-vacuity witness.** `cleanupMark_no_faithful_semV` (the `capNoCleanup` pair `pCl`, `pNo`); also `terminateReason_no_faithful_semV`.

**Positive control.** `dropReplace_merged_yet_faithful`.

**Non-claims.** Listed under `## Boundaries`, subsection `no-faithful-semantics-for-merged-pair`.

**Prior art.**
- Elementary; no specific source is claimed. (Lean core's quotient primitive `Quot.lift` asks the lifted function to agree on related elements, the same condition read positively.)
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_middle/src/mir/syntax.rs L758–760: "The `replace` flag indicates whether this terminator was created as part of an assignment. This should only be used for diagnostic purposes, and does not have any operational meaning."

**Design question.** Why must a capture preserve injectively every piece of metadata that distinguishes behaviour?

Basis: execution (Lean kernel check) for the Lean statements of this card.

Basis: derived (modeling bridge) for the bracketed rust-lang/rust items under Prior art: documentation and source at the pinned revision, connected to the toy by the reasoning in the subsection *Modeling bridge* below; not a theorem.

#### `faithful-semantics-exists-iff-merges-only-equivalent` (characterization)

**Plain claim.** For every capture `cap` and source semantics `semS`, some verifier semantics makes `cap` faithful on its ok-image iff any two programs that `cap` maps to the same `q` admit the same runs.

**Kind / tier / depth.** characterization / T0 (Elementary factorization through the identifications a map makes, restated for partial captures.) / shallow.

**Lean statement.**

```lean
-- lean/Toy/Capture/Basic.lean:286-289
theorem exists_faithful_semV_iff_merges_only_equivalent {S V E B : Type}
    (semS : S → Den B) (cap : S → Except E V) :
    (∃ semV : V → Den B, FaithfulOnOk semS semV cap) ↔
      ∀ p₁ p₂ q, cap p₁ = .ok q → cap p₂ = .ok q → DenEquiv (semS p₁) (semS p₂) := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `exists_faithful_semV_witnesses`: both sides hold for `capFC` and both fail for `capNoCleanup`.

**Non-claims.** Listed under `## Boundaries`, subsection `faithful-semantics-exists-iff-merges-only-equivalent`.

**Prior art.**
- Elementary; no specific source is claimed.

**Design question.** Exactly which identifications may a capture make if a faithful verifier semantics is to exist?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `toy-clearing-replace-flag-is-equivalence` (theorem)

**Plain claim.** In the concrete toy, clearing every drop replace flag (`clearReplace`) preserves the source denotation of every program.

**Kind / tier / depth.** theorem / T1 (Direct consequence of the toy semantics, which follows documented upstream design.) / shallow.

**Lean statement.**

```lean
-- lean/Toy/Capture/Sim.lean:300
theorem clearReplace_denEquiv (p : SProg) : DenEquiv (semS (clearReplace p)) (semS p) := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `denEquiv_example_pos` (`pDrop true`).

**Non-claims.** Listed under `## Boundaries`, subsection `toy-clearing-replace-flag-is-equivalence`.

**Prior art.**
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_middle/src/mir/syntax.rs L758–760: "The `replace` flag indicates whether this terminator was created as part of an assignment. This should only be used for diagnostic purposes, and does not have any operational meaning."

**Design question.** May a capture drop metadata that the source semantics documents as non-operational?

Basis: execution (Lean kernel check) for the Lean statements of this card.

Basis: derived (modeling bridge) for the bracketed rust-lang/rust items under Prior art: documentation and source at the pinned revision, connected to the toy by the reasoning in the subsection *Modeling bridge* below; not a theorem.

#### `transfer-soundness-iff-over-approximation` (characterization)

**Plain claim.** For every capture `cap : S → Except E V`, source semantics `semS` and verifier semantics `semV`: verification transfers through `cap` (`TransferSound`, which quantifies over every specification `spec : B → Prop`) for every verdict relation sound for `semV` iff `cap` over-approximates on its ok-image; and it transfers for the exact verifier of `semV` iff `cap` over-approximates on its ok-image. Programs on which `cap` errors impose no obligation.

**Kind / tier / depth.** characterization / T0 (Backward simulation (behaviour inclusion) implies preservation of every specification (Leroy, JAR 2009, §2.1); the converse is the instantiation `spec := semV q`. Restated for partial captures and sound verdict relations.) / shallow.

**Lean statements.**

```lean
-- lean/Toy/Capture/Basic.lean:321-325
theorem transferSound_all_sound_verifiers_iff_overApproxOnOk {S V E B : Type}
    (semS : S → Den B) (semV : V → Den B) (cap : S → Except E V) :
    (∀ verified : V → (B → Prop) → Prop, VerifierSound semV verified →
        TransferSound semS cap verified) ↔
      OverApproxOnOk semS semV cap := by
```

```lean
-- lean/Toy/Capture/Basic.lean:334-336
theorem transferSound_exactVerifier_iff_overApproxOnOk {S V E B : Type}
    (semS : S → Den B) (semV : V → Den B) (cap : S → Except E V) :
    TransferSound semS cap (exactVerifier semV) ↔ OverApproxOnOk semS semV cap := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `transferSound_iff_witnesses`: both sides hold for `capFC`; both fail for `capDefault`; both hold for `capStringify` read with `havoc`, which is not faithful.

**Non-claims.** Listed under `## Boundaries`, subsection `transfer-soundness-iff-over-approximation`.

**Prior art.**
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), §2.1 "Notions of semantic preservation": Definition 2 (backward simulation, ∀B, C ⇓ B ⟹ S ⇓ B), Definition 3 (backward simulation for safe programs), Definition 4 (forward simulation), Definition 6 (preservation of a specification, S ⊨ Spec ⟹ C ⊨ Spec, where C ⊨ Spec means that every behaviour of C satisfies Spec), and the remarks that backward simulation for safe programs implies preservation of every specification, and that forward simulation implies backward simulation if C is deterministic. In a capture, the verified program (the captured `q`) plays the role of S and the program concluded about (`p`) the role of C.
- A. Pnueli, M. Siegel, E. Singerman, "Translation Validation", TACAS 1998, LNCS 1384, pp. 151–166, doi:10.1007/BFb0054170 (publisher's abstract: each run of the translator is followed by a validation that the target code correctly implements the source, with correct implementation formalized as a refinement relation).

**Design question.** What exactly must a capture guarantee, independently of which sound verifier consumes its output?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `fail-closed-and-fail-open-obligations` (characterization)

**Plain claim.** For every decidable fragment `M` and translation `tr`: the fail-closed capture `failClosed M tr e` (for every error value `e`) over-approximates on its ok-image iff `tr` over-approximates on every program in `M`; the fail-open capture `failOpen M tr fb` (for every fallback `fb`) over-approximates iff `tr` over-approximates on every program in `M` and `fb` over-approximates on every program outside `M`; and more generally the partial extension `partialExtend M tr rest` over-approximates iff `tr` over-approximates on `M` and every successful result of `rest` outside `M` over-approximates.

**Kind / tier / depth.** characterization / T0 (Case analysis on an if-then-else; restated for captures.) / definitional.

**Lean statements.**

```lean
-- lean/Toy/Capture/Basic.lean:435-438
theorem failClosed_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E) :
    OverApproxOnOk semS semV (failClosed M tr e) ↔
      ∀ p, M p → DenIncl (semS p) (semV (tr p)) := by
```

```lean
-- lean/Toy/Capture/Basic.lean:453-457
theorem failOpen_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr fb : S → V) :
    OverApproxOnOk semS semV (failOpen (E := E) M tr fb) ↔
      (∀ p, M p → DenIncl (semS p) (semV (tr p))) ∧
        (∀ p, ¬ M p → DenIncl (semS p) (semV (fb p))) := by
```

```lean
-- lean/Toy/Capture/Basic.lean:416-421
theorem partialExtend_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr : S → V)
    (rest : S → Except E V) :
    OverApproxOnOk semS semV (partialExtend M tr rest) ↔
      (∀ p, M p → DenIncl (semS p) (semV (tr p))) ∧
        (∀ p q, ¬ M p → rest p = .ok q → DenIncl (semS p) (semV q)) := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `failClosed_failOpen_witnesses`: on Nat with identity semantics, fragment {0}, `tr = id`, fallback `fun _ => 0`, the fail-closed capture over-approximates and the fail-open capture does not; `failOpen_overApproxOnOk_example_pos`: a fail-open capture whose fallback admits every run over-approximates.

**Non-claims.** Listed under `## Boundaries`, subsection `fail-closed-and-fail-open-obligations`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** What extra obligation does a capture take on when it returns a result for a construct it does not model?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `over-approximation-is-faithfulness-for-total-deterministic` (theorem)

**Plain claim.** For runs of the form `I × O`: if every successfully captured source denotation is total (`Total`: every input has at least one outcome) and every captured denotation is deterministic (`Det`: every input has at most one outcome), then the capture over-approximates on its ok-image iff it is faithful on its ok-image.

**Kind / tier / depth.** theorem / T0 (Forward simulation implies backward simulation for deterministic targets (Leroy, JAR 2009, §2.1; mechanized at step level in CompCert), restated for run sets over `I × O`.) / shallow.

**Lean statement.**

```lean
-- lean/Toy/Capture/Basic.lean:364-368
theorem faithfulOnOk_iff_overApproxOnOk_of_total_of_det {S V E I O : Type}
    (semS : S → Den (I × O)) (semV : V → Den (I × O)) (cap : S → Except E V)
    (htot : ∀ p q, cap p = .ok q → Total (semS p))
    (hdet : ∀ p q, cap p = .ok q → Det (semV q)) :
    FaithfulOnOk semS semV cap ↔ OverApproxOnOk semS semV cap := by
```

**Hypothesis ledger.**
- `htot : ∀ p q, cap p = .ok q → Total (semS p)` — every input of a captured source has at least one outcome. tight: `cex_faithful_iff_htot` (instance with exactly one program, over `Unit × Bool`, whose source denotation is empty).
- `hdet : ∀ p q, cap p = .ok q → Det (semV q)` — every captured program has at most one outcome per input. tight: `cex_faithful_iff_hdet` (concrete toy: `capStringify` read with `havoc`).

**Non-vacuity witness.** `faithful_iff_overApprox_nonvacuous` (`capFC`).

**Non-claims.** Listed under `## Boundaries`, subsection `over-approximation-is-faithfulness-for-total-deterministic`.

**Prior art.**
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), §2.1 "Notions of semantic preservation": Definition 2 (backward simulation, ∀B, C ⇓ B ⟹ S ⇓ B), Definition 3 (backward simulation for safe programs), Definition 4 (forward simulation), Definition 6 (preservation of a specification, S ⊨ Spec ⟹ C ⊨ Spec, where C ⊨ Spec means that every behaviour of C satisfies Spec), and the remarks that backward simulation for safe programs implies preservation of every specification, and that forward simulation implies backward simulation if C is deterministic. In a capture, the verified program (the captured `q`) plays the role of S and the program concluded about (`p`) the role of C.
- CompCert (github.com/AbsInt/CompCert at 2685140bf72c959446981fb99b5e44a8975021bc): common/Smallstep.v L1863–1866, `Lemma forward_to_backward_simulation: forall L1 L2, forward_simulation L1 L2 -> receptive L1 -> determinate L2 -> backward_simulation L1 L2.`; common/Behaviors.v L493–496 (`backward_simulation_behavior_improves`). These are the step-level, mechanized counterparts of the set-level statements here.

**Design question.** When is 'the captured program means exactly the source' the right requirement, rather than 'the captured program allows at least the source's behaviours'?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `toy-fail-closed-capture-faithful` (theorem)

**Plain claim.** In the concrete toy, the fail-closed capture `capFC` is faithful on its ok-image for either meaning of `opaque` (`capFC_faithfulOnOk`); more precisely, whenever `capFC p = .ok q`, the verifier run of `q` equals the source run of `p` at every fuel, block and state (`capFC_runV_eq_runS`).

**Kind / tier / depth.** theorem / T1 (A simulation between two toy interpreters written to correspond construct by construct.) / shallow.

**Lean statements.**

```lean
-- lean/Toy/Capture/Sim.lean:257
theorem capFC_faithfulOnOk (os : OpaqueSem) : FaithfulOnOk semS (semV os) capFC := by
```

```lean
-- lean/Toy/Capture/Sim.lean:248-249
theorem capFC_runV_eq_runS (os : OpaqueSem) {p : SProg} {q : VProg} (h : capFC p = .ok q) :
    ∀ n pc st, runV os q n pc st = .det (runS p n pc st) := by
```

**Hypothesis ledger.**
- `h : capFC p = .ok q` (`capFC_runV_eq_runS`) — ties `q` to `p`. tight: `cex_capFC_runV_h` (concrete toy: `qRet` is not the capture of `pPM`, and their runs differ on input 0).

**Non-vacuity witness.** `capFC_pPM` (a successful capture).

**Non-claims.** Listed under `## Boundaries`, subsection `toy-fail-closed-capture-faithful`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** Is there a non-trivial capture that meets the transfer requirement on a modeled fragment?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `toy-stringify-with-havoc-over-approximates` (theorem)

**Plain claim.** In the concrete toy, `capStringify` over-approximates on its ok-image when `opaque` is read as `havoc`; it is not faithful under that reading, and it does not over-approximate when `opaque` is read as a no-op.

**Kind / tier / depth.** theorem / T1 (Reading unknown constructs as arbitrary effects is standard; made precise in the toy.) / shallow.

**Lean statements.**

```lean
-- lean/Toy/Capture/Sim.lean:267-268
theorem capStringify_overApproxOnOk_havoc :
    OverApproxOnOk semS (semV .havoc) capStringify := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:509
theorem capStringify_havoc_not_faithful : ¬ FaithfulOnOk semS (semV .havoc) capStringify := by
```

```lean
-- lean/Toy/Capture/Examples.lean:217
theorem overApproxOnOk_example_neg : ¬ OverApproxOnOk semS (semV .noop) capStringify := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `capStringify_pAsm` (a successful capture containing `opaque`).

**Non-claims.** Listed under `## Boundaries`, subsection `toy-stringify-with-havoc-over-approximates`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** Is fail-closed necessary when the verifier is conservative about unmodeled constructs?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `flag-contract-sound-iff-no-silent-omission` (characterization)

**Plain claim.** For every toy backend `be` and per-flag property `Holds`: if admitted flags are honoured (`HonoursAdmitted`: for every list `fs` of admitted flags, the artifact `be.build fs` has the property of every flag in `fs`, all at once) and every omission is observable in some admitted context (`OmissionObservableOnAdmitted`: for every omitted flag `f` there is a list `fs` of admitted flags, possibly empty, such that `be.build fs` lacks `f`'s property), then the contract 'flag set ⇒ property holds of the artifact', for every configuration (`FlagContractSound`), holds iff the backend never silently omits a flag (`NeverOmits`). Sufficiency uses `HonoursAdmitted` alone (`flagContractSound_of_neverOmits`), necessity uses `OmissionObservableOnAdmitted` alone (`neverOmits_of_flagContractSound`), and under `HonoursAdmitted` alone the contract holds iff the property of every omitted flag holds of the artifact built from every list of admitted flags (`flagContractSound_iff_omitted_hold_in_admitted_contexts`).

**Kind / tier / depth.** characterization / T1 (Fail-closed configuration handling (folklore), made precise with its two side conditions.) / shallow.

**Lean statements.**

```lean
-- lean/Toy/Capture/Flags.lean:117-120
theorem flagContractSound_iff_neverOmits {F A : Type} (Holds : F → A → Prop)
    (be : Backend F A) (hAdm : HonoursAdmitted Holds be)
    (hObs : OmissionObservableOnAdmitted Holds be) :
    FlagContractSound Holds be ↔ NeverOmits be :=
```

```lean
-- lean/Toy/Capture/Flags.lean:78-80
theorem flagContractSound_of_neverOmits {F A : Type} (Holds : F → A → Prop)
    (be : Backend F A) (hAdm : HonoursAdmitted Holds be) (hno : NeverOmits be) :
    FlagContractSound Holds be := by
```

```lean
-- lean/Toy/Capture/Flags.lean:106-108
theorem neverOmits_of_flagContractSound {F A : Type} (Holds : F → A → Prop)
    (be : Backend F A) (hObs : OmissionObservableOnAdmitted Holds be)
    (hS : FlagContractSound Holds be) : NeverOmits be := by
```

```lean
-- lean/Toy/Capture/Flags.lean:126-130
theorem flagContractSound_iff_omitted_hold_in_admitted_contexts {F A : Type}
    (Holds : F → A → Prop) (be : Backend F A) (hAdm : HonoursAdmitted Holds be) :
    FlagContractSound Holds be ↔
      ∀ f, be.respond f = .omitted →
        ∀ fs, (∀ g ∈ fs, be.respond g = .admitted) → Holds f (be.build fs) := by
```

**Hypothesis ledger.**
- `hAdm : HonoursAdmitted Holds be` (`flagContractSound_iff_neverOmits`, `flagContractSound_of_neverOmits`, `flagContractSound_iff_omitted_hold_in_admitted_contexts`) — admitted flags must be established. tight: `cex_flag_hAdm` (backend over `Unit` with exactly one flag, which it admits without establishing its property).
- `hObs : OmissionObservableOnAdmitted Holds be` (`flagContractSound_iff_neverOmits`, `neverOmits_of_flagContractSound`) — an omitted property must fail in some admitted context. tight: `cex_flag_hObs` (backend over `Unit` with exactly one flag, which it omits although its property always holds).
- `hno : NeverOmits be` (`flagContractSound_of_neverOmits`) — the backend never omits. tight: `cex_flag_hno` (the toy backend `beOmit` with property `instruments`: it honours admitted flags, omits flag 2, and the contract fails).
- `hS : FlagContractSound Holds be` (`neverOmits_of_flagContractSound`) — the contract holds. tight: `cex_flag_hS` (the toy backend `beOmit` with property `instruments`: its omissions are observable, the contract fails, and it omits flag 2).

**Non-vacuity witness.** `flag_nonvacuous`: both hypotheses hold for `beFC` and `beOmit`; both sides hold for `beFC` and fail for `beOmit`. `beSan_instance`: a backend with exactly two flags for which both hypotheses hold, the omitted flag's property holds of the artifact built from no flags and fails in the admitted context `[false]`.

**Non-claims.** Listed under `## Boundaries`, subsection `flag-contract-sound-iff-no-silent-omission`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** When a configuration requests a property, what must the backend do with requests it cannot honour?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `checked-artifact-restores-flag-contract` (theorem)

**Plain claim.** For every toy backend `be`, property `Holds` and per-flag check `check`: if the check is sound for the property (`check f a = true → Holds f a`), then every artifact that the checked run `checkedRun be check cfg` returns has the property of every requested flag, for every configuration `cfg`, including for a backend that silently omits flags (`checkedRun_contractSound`); and if the check is also complete (`Holds f a → check f a = true`), the checked run returns `a` whenever `be.run cfg = .ok a` and `a` has the property of every flag in `cfg` (`checkedRun_eq_run_of_holds`).

**Kind / tier / depth.** theorem / T0 (Elementary: a guard that checks every requested flag on the returned artifact (`List.find?` returns `none` iff no element fails the check).) / definitional.

**Lean statements.**

```lean
-- lean/Toy/Capture/Flags.lean:314-316
theorem checkedRun_contractSound {F A : Type} (Holds : F → A → Prop) (be : Backend F A)
    (check : F → A → Bool) (hcheck : ∀ f a, check f a = true → Holds f a) :
    ∀ cfg a, checkedRun be check cfg = .ok a → ∀ f ∈ cfg, Holds f a := by
```

```lean
-- lean/Toy/Capture/Flags.lean:335-338
theorem checkedRun_eq_run_of_holds {F A : Type} (Holds : F → A → Prop) (be : Backend F A)
    (check : F → A → Bool) (hcomp : ∀ f a, Holds f a → check f a = true) (cfg : List F)
    (a : A) (hrun : be.run cfg = .ok a) (hall : ∀ f ∈ cfg, Holds f a) :
    checkedRun be check cfg = .ok a := by
```

**Hypothesis ledger.**
- `hcheck : ∀ f a, check f a = true → Holds f a` (`checkedRun_contractSound`) — the check must be sound for the property. tight: `cex_checkedRun_hcheck` (toy backend `beOmit` with the check that accepts everything).
- `hcomp : ∀ f a, Holds f a → check f a = true` (`checkedRun_eq_run_of_holds`) — the check must accept artifacts that have the property. tight: `cex_checkedRun_hcomp` (toy backend `beFC` with the check that rejects everything).
- `hrun : be.run cfg = .ok a` (`checkedRun_eq_run_of_holds`) — the build must succeed with `a`. tight: `cex_checkedRun_hrun` (toy backend `beOmit`, which rejects flag 1).
- `hall : ∀ f ∈ cfg, Holds f a` (`checkedRun_eq_run_of_holds`) — the artifact must have every requested property. tight: `cex_checkedRun_hall` (toy backend `beOmit`, which omits flag 2).

**Non-vacuity witness.** `checkedRun_nonvacuous`: the membership check is sound and complete for `instruments`; the checked runs of `beOmit` on `[0]` and of `beFC` on `[0, 2]` succeed with artifacts that have every requested property. Contrast: `checkedRun_detects_omission` (the checked run of `beOmit` on `[2]` fails).

**Non-claims.** Listed under `## Boundaries`, subsection `checked-artifact-restores-flag-contract`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** Can a post-hoc check of the produced artifact detect silent omission?

Basis: execution (Lean kernel check) for the Lean statements of this card.

#### `exempting-source-audit-weaker-than-ir-audit` (theorem)

**Plain claim.** In the toy audit model, every program that the post-expansion IR audit `irAudit` accepts is accepted by the source-level audit `srcAuditExemptExternal`, which exempts external macro expansions (`srcAudit_of_irAudit`); and the converse fails: there is a program, `[.macro true [true]]` (exactly one external macro whose expansion contains an unsafe item), that the exempting source audit accepts and the IR audit rejects (`srcAudit_misses_external_unsafe`). `exemptingSrcAudit_strictlyWeaker_than_irAudit` states both.

**Kind / tier / depth.** theorem / T0 (Elementary list induction (`List.any` over an append) in a toy audit model.) / shallow.

**Lean statements.**

```lean
-- lean/Toy/Capture/Flags.lean:487-489
theorem exemptingSrcAudit_strictlyWeaker_than_irAudit :
    (∀ prog, irAudit prog = true → srcAuditExemptExternal prog = true) ∧
    ∃ prog, srcAuditExemptExternal prog = true ∧ irAudit prog = false :=
```

```lean
-- lean/Toy/Capture/Flags.lean:449
theorem srcAudit_of_irAudit : ∀ prog, irAudit prog = true → srcAuditExemptExternal prog = true
```

```lean
-- lean/Toy/Capture/Flags.lean:469-470
theorem srcAudit_misses_external_unsafe :
    srcAuditExemptExternal [.macro true [true]] = true ∧ irAudit [.macro true [true]] = false := by
```

**Hypothesis ledger.** No hypotheses beyond the typed parameters.

**Non-vacuity witness.** `srcAudit_of_irAudit_nonvacuous`: both audits accept `progAuditOk` (plain safe code, a safe non-external expansion and a safe external expansion).

**Non-claims.** Listed under `## Boundaries`, subsection `exempting-source-audit-weaker-than-ir-audit`.

**Prior art.**
- Folklore; no specific source is claimed.

**Design question.** Is a source-level audit that exempts external macro expansions a substitute for an audit of the post-expansion IR?

Basis: execution (Lean kernel check) for the Lean statements of this card.

### Modeling bridge: rustc's documented pipeline before `Runtime(PostCleanup)` (`derived (modeling bridge)`)

Basis: derived (modeling bridge), from documentation and source at pinned public revisions; no tool was run.

These are quotations of upstream source and documentation at pinned public revisions, followed by the reasoning that connects them to the toy. The connection is a modeling bridge, not a theorem: Model–system relation: none proved. Comment markers (`///`, `//`, `//!`) are removed in quotations.

**Quotations (documentation and source).**
- rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, `compiler/rustc_mir_transform/src/lib.rs` L649–663: doc comment "Returns the sequence of passes that do the initial cleanup of runtime MIR." on `fn run_runtime_cleanup_passes`, whose pass list (L651–655) is `&lower_intrinsics::LowerIntrinsics`, `&remove_place_mention::RemovePlaceMention`, `&simplify::SimplifyCfg::PreOptimizations`, passed to `pm::run_passes(tcx, body, passes, Some(MirPhase::Runtime(RuntimePhase::PostCleanup)), pm::Optimizations::Allowed)` (L657–663).
- Same revision, same file, L596–598: `debug!("runtime_mir_cleanup({:?})", did);` / `run_runtime_cleanup_passes(tcx, body);` / `assert!(body.phase == MirPhase::Runtime(RuntimePhase::PostCleanup));` (end of `run_analysis_to_runtime_passes`, L569–599), which `mir_drops_elaborated_and_const_checked` (L513) calls at L562.
- Same revision, `compiler/rustc_mir_transform/src/remove_place_mention.rs` L1: "This pass removes `PlaceMention` statement, which has no effect at codegen."; L10–12: `fn is_enabled(&self, sess: &rustc_session::Session) -> bool {` / `!sess.opts.unstable_opts.mir_preserve_ub` / `}`.
- Same revision, `compiler/rustc_session/src/options.rs` L2469–2471 (option `mir_preserve_ub`, help text): "keep place mention statements and reads in trivial SwitchInt terminators, which are interpreted e.g., by miri; implies -Zmir-opt-level=0 (default: no)". The same text is at rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, `compiler/rustc_session/src/options.rs` L2654–2656.
- Same revision (f8a08b68…), `compiler/rustc_mir_transform/src/simplify.rs` L128–130: "Preserve `SwitchInt` reads on built and analysis MIR, or if `-Zmir-preserve-ub`." followed by `let preserve_switch_reads = matches!(body.phase, MirPhase::Built | MirPhase::Analysis(_))` / `|| tcx.sess.opts.unstable_opts.mir_preserve_ub;`; L305: "turn a branch with all successors identical to a goto" (the comment above `fn simplify_branch`, L306) and L307–309: "Removing a `SwitchInt` terminator may remove reads that result in UB, so we must not apply this optimization before borrowck or when `-Zmir-preserve-ub` is set." The same two comments are at rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, `compiler/rustc_mir_transform/src/simplify.rs` L307 and L309–311 (the revision whose documentation the reference corpus package `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches` quotes).
- Same revision (f8a08b68…), `compiler/rustc_middle/src/mir/syntax.rs` L65: "The \"runtime MIR\" dialect, used for CTFE, optimizations, and codegen."; L138–140 (`RuntimePhase::PostCleanup`): "Beginning with this phase, the following variant is disallowed: * [`ProjectionElem::Deref`] of `Box`".
- Same revision, `compiler/rustc_middle/src/mir/syntax.rs` L758–760 (doc of `TerminatorKind::Drop`): "The `replace` flag indicates whether this terminator was created as part of an assignment. This should only be used for diagnostic purposes, and does not have any operational meaning."
- Same revision, `compiler/rustc_middle/src/mir/syntax.rs` L1046–1055: "The reason we are terminating the process during unwinding." on `pub enum UnwindTerminateReason`, with variants `Abi` ("Unwinding is just not possible given the ABI of this function.") and `InCleanup` ("We were already cleaning up for an ongoing unwind, and a *second*, *nested* unwind was triggered by the drop glue.").
- Same revision, `compiler/rustc_middle/src/mir/syntax.rs` L673–676: "The basic block pointed to by a `Cleanup` unwind action must have its `cleanup` flag set. `cleanup` basic blocks have a couple restrictions: 1. All `unwind` fields in them must be `UnwindAction::Terminate` or `UnwindAction::Unreachable`. 2. `Return` terminators are not allowed in them. `Terminate` and `Resume` terminators are."
- Same revision, `compiler/rustc_middle/src/mir/syntax.rs` L666–671 (documentation of `TerminatorKind`): "A note on unwinding: Panics may occur during the execution of some terminators. Depending on the `-C panic` flag, this may either cause the program to abort or the call stack to unwind. Such terminators have a `unwind: UnwindAction` field on them. If stack unwinding occurs, then once the current function is reached, an action will be taken based on the `unwind` field. If the action is `Cleanup`, then the execution continues at the given basic block. If the action is `Continue` then no cleanup is performed, and the stack continues unwinding."
- Same revision, `compiler/rustc_middle/src/mir/mod.rs` L1337–1341 (field `is_cleanup` of `BasicBlockData`): "If true, this block lies on an unwind path. This is used during codegen where distinct kinds of basic blocks may be generated (particularly for MSVC cleanup). Unwind blocks must only branch to other unwind blocks."

**Derived (modeling bridge).**
- By the pass list and the phase argument above, a body in `Runtime(PostCleanup)` produced by this pipeline has been through `RemovePlaceMention` (enabled unless `-Zmir-preserve-ub`) and `SimplifyCfg::PreOptimizations`. Since the body is in the runtime dialect while these passes run (the assertion at L594 of `lib.rs` precedes the cleanup call), the condition at `simplify.rs` L128–130 does not preserve `SwitchInt` reads there unless `-Zmir-preserve-ub` is set. So capture at `Runtime(PostCleanup)` is not "before every UB-erasing pass": in the toy's terms, the erasing set `E_k` before such a capture point contains the analogues of place-mention erasure and equal-target switch erasure, and `transfer_relative_to_erasingSet` then asks for their preconditions at the actual inputs. With `-Zmir-preserve-ub`, the quoted code disables these two erasures (the toy analogue of a pipeline without them is `erasure_disabled_control`); it does not follow that no erasing pass runs before `Runtime(PostCleanup)` (next item).
- Whether the other passes on the way to `Runtime(PostCleanup)` (`LowerIntrinsics` in the quoted list, analysis cleanup and runtime lowering) erase UB, and how the change from the analysis to the runtime dialect interacts with the erasing set, are not examined here. Nor is it examined whether borrow checking, which the quoted comment orders before the switch optimization, discharges any erasure precondition.
- The toy's terminate reasons mirror `UnwindTerminateReason` by name; the toy makes the reason part of the observable outcome. The quoted documentation does not say whether the reason is observable at run time; this package does not claim it is.
- The toy decides the response to a panic from the block's cleanup mark. The quoted documentation instead attaches the response to the terminator's `unwind: UnwindAction` field (`syntax.rs` L666–671) and restricts the unwind actions allowed in cleanup blocks; `is_cleanup` is documented as used during codegen. The toy witness pair for the cleanup mark therefore shows that whatever field carries this distinction must be preserved; it does not show that `is_cleanup` alone carries it. The toy witness `pCl` also has a `continueUnwind` call inside a cleanup block, which the restriction quoted from `syntax.rs` L675 excludes.
- The toy ignores the drop replace flag, as the quoted documentation describes; this makes the replace flag the positive control of `no-faithful-semantics-for-merged-pair`.
- Public compiler interfaces for reading MIR are not examined; nothing is claimed about what they expose or preserve.

### Auxiliary declarations cited by name (verbatim)

```lean
-- lean/Toy/Capture/Basic.lean:131-135
theorem erasingSetPrecondition_iff_forall_inErasingSet {S B : Type} (semS : S → Den B)
    (pipe : List (Pass S)) (src : S) :
    ErasingSetPrecondition semS pipe src ↔
      ∀ i (hi : InErasingSet pipe i),
        LosesNoBehaviourAt semS (pipe[i]'hi.1).run (runPipe (pipe.take i) src) :=
```

```lean
-- lean/Toy/Capture/Basic.lean:159-161
theorem denIncl_runPipe_of_losesNoBehaviourAtInputs {S B : Type} (semS : S → Den B) :
    ∀ (pipe : List (Pass S)) (src : S), LosesNoBehaviourAtInputs semS pipe src →
      DenIncl (semS src) (semS (runPipe pipe src))
```

```lean
-- lean/Toy/Capture/Basic.lean:173-176
theorem losesNoBehaviourAtInputs_of_erasingSet {S B : Type} (semS : S → Den B)
    (pipe : List (Pass S)) (src : S) (hEq : ∀ P ∈ pipe, EquivTagSound semS P)
    (hE : ErasingSetPrecondition semS pipe src) :
    LosesNoBehaviourAtInputs semS pipe src := by
```

```lean
-- lean/Toy/Capture/Basic.lean:202-209
theorem transfer_single_pass {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (P : Pass S) (src : S) (q : V) (spec : B → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    (hEq : EquivTagSound semS P)
    (hE : P.tag = .erasing → LosesNoBehaviourAt semS P.run src)
    (hok : cap (P.run src) = .ok q) (hver : verified q spec) :
    Sat (semS src) spec := by
```

```lean
-- lean/Toy/Capture/Basic.lean:307-311
theorem verdict_on_merged_capture_holds_for_both {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (hT : TransferSound semS cap verified) {p₁ p₂ : S} {q : V} {spec : B → Prop}
    (h₁ : cap p₁ = .ok q) (h₂ : cap p₂ = .ok q) (hv : verified q spec) :
    Sat (semS p₁) spec ∧ Sat (semS p₂) spec :=
```

```lean
-- lean/Toy/Capture/Basic.lean:346-347
theorem transferSound_of_verifier_accepts_nothing {S V E B : Type} (semS : S → Den B)
    (cap : S → Except E V) : TransferSound semS cap (fun _ _ => False) :=
```

```lean
-- lean/Toy/Capture/Basic.lean:405-406
theorem failClosed_eq_partialExtend {S V E : Type} (M : S → Prop) [DecidablePred M]
    (tr : S → V) (e : E) : failClosed M tr e = partialExtend M tr (fun _ => .error e) :=
```

```lean
-- lean/Toy/Capture/Basic.lean:409-410
theorem failOpen_eq_partialExtend {S V E : Type} (M : S → Prop) [DecidablePred M]
    (tr fb : S → V) : failOpen (E := E) M tr fb = partialExtend M tr (fun p => .ok (fb p)) :=
```

```lean
-- lean/Toy/Capture/Sim.lean:146-150
theorem capWith_runV {c : CapCfg} (hc : CfgFCExceptAsm c) (os : OpaqueSem)
    (hstr : c.stringifyAsm = false ∨ os = .havoc) {p : SProg} {q : VProg}
    (h : capWith c p = .ok q) :
    ∀ n pc st, runV os q n pc st = .det (runS p n pc st) ∨
      (c.stringifyAsm = true ∧ os = .havoc ∧ runV os q n pc st = .top) := by
```

```lean
-- lean/Toy/Capture/Sim.lean:237-238
theorem capWith_fuel {c : CapCfg} {p : SProg} {q : VProg} (h : capWith c p = .ok q) :
    q.fuel = p.fuel := by
```

```lean
-- lean/Toy/Capture/Sim.lean:277-278
theorem runS_clearReplace (p : SProg) :
    ∀ n pc st, runS (clearReplace p) n pc st = runS p n pc st
```

```lean
-- lean/Toy/Capture/Sim.lean:407-410
theorem failOpenVariants_eq_partialExtend_capFC :
    capDefault = partialExtend capFCAccepts capFCOut capDefault ∧
    capStringify = partialExtend capFCAccepts capFCOut capStringify ∧
    capSwallow = partialExtend capFCAccepts capFCOut capSwallow := by
```

```lean
-- lean/Toy/Capture/Examples.lean:104-105
theorem runS_pPM (x : Nat) :
    runS pPM pPM.fuel 0 (St.init x) = if x = 0 then ⟨[], .ub⟩ else ⟨[], .ret⟩ := by
```

```lean
-- lean/Toy/Capture/Examples.lean:147
theorem capFC_pPM : capFC pPM = .ok qPM := …
```

```lean
-- lean/Toy/Capture/Examples.lean:153
theorem capFC_pTrap : capFC pTrap = .error .unmodeledTerm := …
```

```lean
-- lean/Toy/Capture/Examples.lean:154
theorem capFC_pAsm : capFC pAsm = .error .unmodeledStmt := …
```

```lean
-- lean/Toy/Capture/Examples.lean:155
theorem capFC_pErr : capFC pErr = .error .erroneousConst := …
```

```lean
-- lean/Toy/Capture/Examples.lean:157
theorem capStringify_pAsm : capStringify pAsm = .ok qAsm := …
```

```lean
-- lean/Toy/Capture/Examples.lean:165
theorem capFC_pCl_ne_pNo : capFC pCl ≠ capFC pNo := …
```

```lean
-- lean/Toy/Capture/Examples.lean:166
theorem capFC_pTerm_abi_ne_inCleanup : capFC (pTerm .abi) ≠ capFC (pTerm .inCleanup) := by
```

```lean
-- lean/Toy/Capture/Examples.lean:172
theorem sat_example_pos : Sat (semS pRet) ubFree :=
```

```lean
-- lean/Toy/Capture/Examples.lean:175
theorem sat_example_neg : ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Examples.lean:179
theorem denIncl_example_pos : DenIncl (semS pAsm) (semV .havoc qAsm) := by
```

```lean
-- lean/Toy/Capture/Examples.lean:183
theorem denIncl_example_neg : ¬ DenIncl (semV .havoc qAsm) (semS pAsm) := by
```

```lean
-- lean/Toy/Capture/Examples.lean:189
theorem denEquiv_example_pos : DenEquiv (semS (clearReplace (pDrop true))) (semS (pDrop true)) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:192
theorem denEquiv_example_neg : ¬ DenEquiv (semS pCl) (semS pNo) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:196
theorem faithfulAt_example_pos (os : OpaqueSem) : FaithfulAt semS (semV os) capFC pCl :=
```

```lean
-- lean/Toy/Capture/Examples.lean:199
theorem faithfulAt_example_neg (os : OpaqueSem) : ¬ FaithfulAt semS (semV os) capNoCleanup pCl := by
```

```lean
-- lean/Toy/Capture/Examples.lean:205
theorem faithfulOnOk_example_pos (os : OpaqueSem) : FaithfulOnOk semS (semV os) capFC :=
```

```lean
-- lean/Toy/Capture/Examples.lean:208
theorem faithfulOnOk_example_neg (os : OpaqueSem) : ¬ FaithfulOnOk semS (semV os) capDefault := by
```

```lean
-- lean/Toy/Capture/Examples.lean:214
theorem overApproxOnOk_example_pos : OverApproxOnOk semS (semV .havoc) capStringify :=
```

```lean
-- lean/Toy/Capture/Examples.lean:223-224
theorem verifierSound_example_pos (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:227
theorem verifierSound_example_neg (os : OpaqueSem) : ¬ VerifierSound (semV os) trustAll := by
```

```lean
-- lean/Toy/Capture/Examples.lean:232-233
theorem transferSound_example_pos (os : OpaqueSem) :
    TransferSound semS capFC (exactVerifier (semV os)) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:236-237
theorem transferSound_example_neg (os : OpaqueSem) :
    ¬ TransferSound semS capDefault (exactVerifier (semV os)) := by
```

```lean
-- lean/Toy/Capture/Examples.lean:244
theorem equivTagSound_example_pos : EquivTagSound semS ⟨.equiv, clearReplace⟩ :=
```

```lean
-- lean/Toy/Capture/Examples.lean:247
theorem equivTagSound_example_neg : ¬ EquivTagSound semS ⟨.equiv, erasePlaceMentions⟩ := by
```

```lean
-- lean/Toy/Capture/Examples.lean:252
theorem equivTagSound_erasing (f : SProg → SProg) : EquivTagSound semS ⟨.erasing, f⟩ :=
```

```lean
-- lean/Toy/Capture/Examples.lean:256
theorem losesNoBehaviourAt_example_pos : LosesNoBehaviourAt semS erasePlaceMentions pOk := by
```

```lean
-- lean/Toy/Capture/Examples.lean:263
theorem losesNoBehaviourAt_example_neg : ¬ LosesNoBehaviourAt semS erasePlaceMentions pPM := by
```

```lean
-- lean/Toy/Capture/Examples.lean:274
theorem inErasingSet_example_pos : InErasingSet pipePM 0 := …
```

```lean
-- lean/Toy/Capture/Examples.lean:277
theorem inErasingSet_example_neg : ¬ InErasingSet pipeOk 1 ∧ ¬ InErasingSet pipePM 1 := by
```

```lean
-- lean/Toy/Capture/Examples.lean:285
theorem erasingSetPrecondition_example_pos : ErasingSetPrecondition semS pipeOk pOk := by
```

```lean
-- lean/Toy/Capture/Examples.lean:291
theorem erasingSetPrecondition_example_neg : ¬ ErasingSetPrecondition semS pipePM pPM :=
```

```lean
-- lean/Toy/Capture/Examples.lean:295
theorem losesNoBehaviourAtInputs_example_pos : LosesNoBehaviourAtInputs semS pipeOk pOk :=
```

```lean
-- lean/Toy/Capture/Examples.lean:305
theorem losesNoBehaviourAtInputs_example_neg : ¬ LosesNoBehaviourAtInputs semS pipePM pPM :=
```

```lean
-- lean/Toy/Capture/Examples.lean:309
theorem runPipe_example : runPipe pipeOk pOk = clearReplace (erasePlaceMentions pOk) := …
```

```lean
-- lean/Toy/Capture/Examples.lean:312
theorem semS_total (p : SProg) : Total (semS p) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:314
theorem semS_det (p : SProg) : Det (semS p) := …
```

```lean
-- lean/Toy/Capture/Examples.lean:316
theorem total_example_neg : ¬ Total (fun _ : Unit × Bool => False) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:319
theorem det_example_neg : ¬ Det (semV .havoc qAsm) := by
```

```lean
-- lean/Toy/Capture/Examples.lean:326
theorem failClosed_example_pos : failClosed (· = 0) id () 0 = .ok 0 := …
```

```lean
-- lean/Toy/Capture/Examples.lean:327
theorem failClosed_example_neg : failClosed (· = 0) id () 1 = .error () := …
```

```lean
-- lean/Toy/Capture/Examples.lean:328
theorem failOpen_example : failOpen (E := Unit) (· = 0) id (fun _ => 0) 1 = .ok 0 := …
```

```lean
-- lean/Toy/Capture/Examples.lean:331
theorem semS_example_pos : semS pPM (0, ⟨[], .ub⟩) := …
```

```lean
-- lean/Toy/Capture/Examples.lean:332
theorem semS_example_neg : ¬ semS pPM (0, ⟨[], .ret⟩) := …
```

```lean
-- lean/Toy/Capture/Examples.lean:333
theorem semV_example_pos : semV .havoc qAsm (0, ⟨[], .ub⟩) := …
```

```lean
-- lean/Toy/Capture/Examples.lean:334
theorem semV_example_neg : ¬ semV .noop qAsm (0, ⟨[7], .ret⟩) := …
```

```lean
-- lean/Toy/Capture/Examples.lean:342-343
theorem semV_havoc_admits_any_trace :
    semV .havoc qEmitOpaque (0, ⟨[], .ret⟩) ∧ ¬ semV .noop qEmitOpaque (0, ⟨[], .ret⟩) :=
```

```lean
-- lean/Toy/Capture/Examples.lean:347-352
theorem specs_example :
    ubFree (0, ⟨[], .ret⟩) ∧ ¬ ubFree (0, ⟨[], .ub⟩) ∧
    returnsNormally (0, ⟨[], .ret⟩) ∧ ¬ returnsNormally (0, ⟨[], .trap⟩) ∧
    silent (0, ⟨[], .ret⟩) ∧ ¬ silent (0, ⟨[7], .ret⟩) ∧
    noAbort (0, ⟨[], .unwind⟩) ∧ ¬ noAbort (0, ⟨[], .abort .inCleanup⟩) ∧
    noAbortInCleanup (0, ⟨[], .abort .abi⟩) ∧ ¬ noAbortInCleanup (0, ⟨[], .abort .inCleanup⟩) := by
```

```lean
-- lean/Toy/Capture/Examples.lean:357-362
theorem passes_example :
    erasePlaceMentions pPM = pRet ∧ eraseZstReads pZst = pRet ∧
    simplifyTrivialSwitches pSw = ⟨[⟨[], .goto 1, false⟩, ⟨[], .ret, false⟩]⟩ ∧
    simplifyTrivialSwitches pSwConstErr = pSwConstErr ∧
    clearReplace (pDrop true) = pDrop false ∧
    simplifyTrivialSwitches pCl = pCl := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:132-133
theorem erasure_disabled_control (os : OpaqueSem) :
    capFC (runPipe [] pPM) = .ok qPM ∧ ¬ exactVerifier (semV os) qPM ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:247-254
theorem cex_hV :
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    trustAll qPM ubFree ∧
    ¬ VerifierSound (semV .noop) trustAll ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:261-268
theorem cex_hEq :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    ErasingSetPrecondition semS pipeMis pPM ∧
    capFC (runPipe pipeMis pPM) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ (∀ P ∈ pipeMis, EquivTagSound semS P) ∧
    ¬ Sat (semS pPM) ubFree := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:278-285
theorem cex_hok :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pPM ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    capFC (runPipe [] pPM) ≠ .ok qRet ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:291-298
theorem cex_hver :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    ¬ exactVerifier (semV .noop) qPM ubFree ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:308-314
theorem cex_pipeline_hpipe :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    capFC (runPipe pipePM pPM) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ LosesNoBehaviourAtInputs semS pipePM pPM ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:320-326
theorem cex_pipeline_hV :
    OverApproxOnOk semS (semV .noop) capFC ∧
    LosesNoBehaviourAtInputs semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    trustAll qPM ubFree ∧
    ¬ VerifierSound (semV .noop) trustAll ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:332-338
theorem cex_pipeline_hcap :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    LosesNoBehaviourAtInputs semS [] pTrap ∧
    capDefault (runPipe [] pTrap) = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧
    ¬ Sat (semS pTrap) returnsNormally :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:344-350
theorem cex_pipeline_hok :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    LosesNoBehaviourAtInputs semS [] pPM ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    capFC (runPipe [] pPM) ≠ .ok qRet ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:356-362
theorem cex_pipeline_hver :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    LosesNoBehaviourAtInputs semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    ¬ exactVerifier (semV .noop) qPM ubFree ∧
    ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:370-372
theorem cex_capInput_hV :
    OverApproxOnOk semS (semV .noop) capFC ∧ capFC pPM = .ok qPM ∧ trustAll qPM ubFree ∧
    ¬ VerifierSound (semV .noop) trustAll ∧ ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:377-380
theorem cex_capInput_hcap :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧ capDefault pTrap = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧ ¬ Sat (semS pTrap) returnsNormally :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:386-389
theorem cex_capInput_hok :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧ exactVerifier (semV .noop) qRet ubFree ∧
    capFC pPM ≠ .ok qRet ∧ ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:394-397
theorem cex_capInput_hver :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧ capFC pPM = .ok qPM ∧
    ¬ exactVerifier (semV .noop) qPM ubFree ∧ ¬ Sat (semS pPM) ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:404-406
theorem transfer_to_capture_input_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    capFC pRet = .ok qRet ∧ exactVerifier (semV os) qRet ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:411-415
theorem transfer_single_pass_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    EquivTagSound semS passPM ∧
    (passPM.tag = .erasing → LosesNoBehaviourAt semS passPM.run pOk) ∧
    capFC (passPM.run pOk) = .ok qOk ∧ exactVerifier (semV os) qOk ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:421-425
theorem transfer_relative_to_erasingSet_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    (∀ P ∈ pipeOk, EquivTagSound semS P) ∧ ErasingSetPrecondition semS pipeOk pOk ∧
    InErasingSet pipeOk 0 ∧
    capFC (runPipe pipeOk pOk) = .ok qOk ∧ exactVerifier (semV os) qOk ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:430-433
theorem transfer_of_losesNoBehaviourAtInputs_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    LosesNoBehaviourAtInputs semS pipeOk pOk ∧
    capFC (runPipe pipeOk pOk) = .ok qOk ∧ exactVerifier (semV os) qOk ubFree :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:445-449
theorem cleanupMark_no_faithful_semV :
    (capNoCleanup pCl = .ok qUnw ∧ capNoCleanup pNo = .ok qUnw ∧
      ¬ DenEquiv (semS pCl) (semS pNo)) ∧
    ∀ semV' : VProg → Den Run,
      ¬ (FaithfulAt semS semV' capNoCleanup pCl ∧ FaithfulAt semS semV' capNoCleanup pNo) :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:454-457
theorem terminateReason_no_faithful_semV :
    ∀ semV' : VProg → Den Run,
      ¬ (FaithfulAt semS semV' capNoReason (pTerm .abi) ∧
        FaithfulAt semS semV' capNoReason (pTerm .inCleanup)) :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:465-469
theorem dropReplace_merged_yet_faithful (os : OpaqueSem) :
    capFC (pDrop true) = .ok qDrop ∧ capFC (pDrop false) = .ok qDrop ∧
    DenEquiv (semS (pDrop true)) (semS (pDrop false)) ∧
    FaithfulAt semS (semV os) capFC (pDrop true) ∧
    FaithfulAt semS (semV os) capFC (pDrop false) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:482-485
theorem merge_hypotheses_tight (os : OpaqueSem) :
    capFC pCl = .ok qCl ∧ capFC pNo = .ok qUnw ∧ qCl ≠ qUnw ∧
    ¬ DenEquiv (semS pCl) (semS pNo) ∧
    FaithfulAt semS (semV os) capFC pCl ∧ FaithfulAt semS (semV os) capFC pNo :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:492-497
theorem exists_faithful_semV_witnesses :
    (∃ semV' : VProg → Den Run, FaithfulOnOk semS semV' capFC) ∧
    (∀ p₁ p₂ q, capFC p₁ = .ok q → capFC p₂ = .ok q → DenEquiv (semS p₁) (semS p₂)) ∧
    ¬ (∃ semV' : VProg → Den Run, FaithfulOnOk semS semV' capNoCleanup) ∧
    ¬ (∀ p₁ p₂ q, capNoCleanup p₁ = .ok q → capNoCleanup p₂ = .ok q →
        DenEquiv (semS p₁) (semS p₂)) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:517-523
theorem transferSound_iff_witnesses :
    (∀ verified, VerifierSound (semV .noop) verified → TransferSound semS capFC verified) ∧
    ¬ (∀ verified, VerifierSound (semV .noop) verified → TransferSound semS capDefault verified) ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧
    (∀ verified, VerifierSound (semV .havoc) verified →
      TransferSound semS capStringify verified) ∧
    ¬ FaithfulOnOk semS (semV .havoc) capStringify :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:534-535
theorem capFC_image_det (os : OpaqueSem) :
    ∀ p q, capFC p = .ok q → Det (semV os q) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:542-543
theorem faithful_iff_overApprox_nonvacuous (os : OpaqueSem) :
    (∀ p q, capFC p = .ok q → Total (semS p)) ∧ (∀ p q, capFC p = .ok q → Det (semV os q)) :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:548-552
theorem cex_faithful_iff_hdet :
    (∀ p q, capStringify p = .ok q → Total (semS p)) ∧
    ¬ (∀ p q, capStringify p = .ok q → Det (semV .havoc q)) ∧
    OverApproxOnOk semS (semV .havoc) capStringify ∧
    ¬ FaithfulOnOk semS (semV .havoc) capStringify :=
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:558-564
theorem cex_faithful_iff_htot :
    let semS' : Unit → Den (Unit × Bool) := fun _ _ => False
    let semV' : Unit → Den (Unit × Bool) := fun _ r => r.2 = true
    let cap' : Unit → Except Unit Unit := fun _ => .ok ()
    ¬ (∀ p q, cap' p = .ok q → Total (semS' p)) ∧
    (∀ p q, cap' p = .ok q → Det (semV' q)) ∧
    OverApproxOnOk semS' semV' cap' ∧ ¬ FaithfulOnOk semS' semV' cap' := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:575-578
theorem failClosed_failOpen_witnesses :
    let semN : Nat → Den Nat := fun p r => r = p
    OverApproxOnOk semN semN (failClosed (· = 0) id ()) ∧
    ¬ OverApproxOnOk semN semN (failOpen (E := Unit) (· = 0) id (fun _ => 0)) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:590-593
theorem failOpen_overApproxOnOk_example_pos :
    let semS' : Nat → Den Nat := fun p r => r = p
    let semV' : Option Nat → Den Nat := fun q r => match q with | some n => r = n | none => True
    OverApproxOnOk semS' semV' (failOpen (E := Unit) (· = 0) some (fun _ => none)) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:602-605
theorem failClosed_empty_fragment {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (tr : S → V) (e : E) :
    (∀ p, failClosed (fun _ : S => False) tr e p = .error e) ∧
    OverApproxOnOk semS semV (failClosed (fun _ : S => False) tr e) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:613-614
theorem cex_capFC_runV_h :
    capFC pPM ≠ .ok qRet ∧ runV .noop qRet 2 0 (St.init 0) ≠ .det (runS pPM 2 0 (St.init 0)) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:622-624
theorem refuted_capFC_has_failClosed_shape :
    ¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr : SProg → VProg) (e : CapErr),
      @failClosed SProg VProg CapErr M inst tr e = capFC := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:640-646
theorem refuted_failOpenVariants_have_failOpen_shape :
    (¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg),
      @failOpen SProg VProg CapErr M inst tr fb = capDefault) ∧
    (¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg),
      @failOpen SProg VProg CapErr M inst tr fb = capStringify) ∧
    (¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg),
      @failOpen SProg VProg CapErr M inst tr fb = capSwallow) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:701-707
theorem fixedFuel_boundary :
    (∀ i < 5, pLoopTrim.blocks[i]? = pLoopDead.blocks[i]?) ∧
    (∀ x, runS pLoopDead pLoopDead.fuel 0 (St.init x) = ⟨[], .ret⟩) ∧
    (∀ x, runS pLoopTrim pLoopTrim.fuel 0 (St.init x) = ⟨[], .fuelOut⟩) ∧
    ¬ DenEquiv (semS pLoopTrim) (semS pLoopDead) ∧
    Sat (semS pLoopUB) ubFree ∧
    (∀ x, runS pLoopUB 9 0 (St.init x) = ⟨[], .ub⟩) := by
```

```lean
-- lean/Toy/Capture/Counterexamples.lean:722-725
theorem acceptNothing_control (os : OpaqueSem) :
    VerifierSound (semV os) (fun _ _ => False) ∧
    TransferSound semS capDefault (fun _ _ => False) ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault :=
```

```lean
-- lean/Toy/Capture/Flags.lean:165
theorem beOmit_honours : HonoursAdmitted instruments beOmit := …
```

```lean
-- lean/Toy/Capture/Flags.lean:166
theorem beFC_honours : HonoursAdmitted instruments beFC := …
```

```lean
-- lean/Toy/Capture/Flags.lean:167
theorem beOmit_observable : OmissionObservableOnAdmitted instruments beOmit :=
```

```lean
-- lean/Toy/Capture/Flags.lean:169
theorem beFC_observable : OmissionObservableOnAdmitted instruments beFC := by
```

```lean
-- lean/Toy/Capture/Flags.lean:175-176
theorem run_example :
    beOmit.run [0, 1] = .error 1 ∧ beOmit.run [0, 2] = .ok [0] ∧ beFC.run [0, 2] = .ok [0, 2] := by
```

```lean
-- lean/Toy/Capture/Flags.lean:181-182
theorem silent_omission_breaks_contract :
    beOmit.run [2] = .ok [] ∧ ¬ instruments 2 [] ∧ ¬ FlagContractSound instruments beOmit := by
```

```lean
-- lean/Toy/Capture/Flags.lean:189-193
theorem flag_nonvacuous :
    HonoursAdmitted instruments beFC ∧ OmissionObservableOnAdmitted instruments beFC ∧
    NeverOmits beFC ∧ FlagContractSound instruments beFC ∧
    HonoursAdmitted instruments beOmit ∧ OmissionObservableOnAdmitted instruments beOmit ∧
    ¬ NeverOmits beOmit ∧ ¬ FlagContractSound instruments beOmit := by
```

```lean
-- lean/Toy/Capture/Flags.lean:218-221
theorem beSan_instance :
    sanHolds true (beSan.build []) ∧ ¬ sanHolds true (beSan.build [false]) ∧
    HonoursAdmitted sanHolds beSan ∧ OmissionObservableOnAdmitted sanHolds beSan ∧
    ¬ NeverOmits beSan ∧ ¬ FlagContractSound sanHolds beSan := by
```

```lean
-- lean/Toy/Capture/Flags.lean:251-257
theorem cex_flag_hAdm :
    let be : Backend Unit Unit := ⟨fun _ => .admitted, fun _ => ()⟩
    let H : Unit → Unit → Prop := fun _ _ => False
    OmissionObservableOnAdmitted H be ∧ NeverOmits be ∧
      (∀ f, be.respond f = .omitted →
        ∀ fs, (∀ g ∈ fs, be.respond g = .admitted) → H f (be.build fs)) ∧
      ¬ HonoursAdmitted H be ∧ ¬ FlagContractSound H be := by
```

```lean
-- lean/Toy/Capture/Flags.lean:273-277
theorem cex_flag_hObs :
    let be : Backend Unit Unit := ⟨fun _ => .omitted, fun _ => ()⟩
    let H : Unit → Unit → Prop := fun _ _ => True
    HonoursAdmitted H be ∧ ¬ OmissionObservableOnAdmitted H be ∧ ¬ NeverOmits be ∧
      FlagContractSound H be :=
```

```lean
-- lean/Toy/Capture/Flags.lean:283-285
theorem cex_flag_hno :
    HonoursAdmitted instruments beOmit ∧ ¬ NeverOmits beOmit ∧
      ¬ FlagContractSound instruments beOmit :=
```

```lean
-- lean/Toy/Capture/Flags.lean:290-292
theorem cex_flag_hS :
    OmissionObservableOnAdmitted instruments beOmit ∧ ¬ FlagContractSound instruments beOmit ∧
      ¬ NeverOmits beOmit :=
```

```lean
-- lean/Toy/Capture/Flags.lean:348-349
theorem checkedRun_detects_omission :
    checkedRun beOmit (fun f a => decide (f ∈ a)) [2] = .error 2 := …
```

```lean
-- lean/Toy/Capture/Flags.lean:354-356
theorem cex_checkedRun_hcheck :
    ¬ (∀ f a, (fun (_ : Nat) (_ : List Nat) => true) f a = true → instruments f a) ∧
    checkedRun beOmit (fun _ _ => true) [2] = .ok [] ∧ ¬ instruments 2 [] := by
```

```lean
-- lean/Toy/Capture/Flags.lean:363-366
theorem cex_checkedRun_hcomp :
    ¬ (∀ f a, instruments f a → (fun (_ : Nat) (_ : List Nat) => false) f a = true) ∧
    beFC.run [0] = .ok [0] ∧ (∀ f ∈ [0], instruments f [0]) ∧
    checkedRun beFC (fun _ _ => false) [0] = .error 0 := by
```

```lean
-- lean/Toy/Capture/Flags.lean:377-383
theorem checkedRun_nonvacuous :
    (∀ (f : Nat) (a : List Nat), (fun f a => decide (f ∈ a)) f a = true → instruments f a) ∧
    (∀ (f : Nat) (a : List Nat), instruments f a → (fun f a => decide (f ∈ a)) f a = true) ∧
    beOmit.run [0] = .ok [0] ∧ (∀ f ∈ ([0] : List Nat), instruments f [0]) ∧
    checkedRun beOmit (fun f a => decide (f ∈ a)) [0] = .ok [0] ∧
    beFC.run [0, 2] = .ok [0, 2] ∧ (∀ f ∈ ([0, 2] : List Nat), instruments f [0, 2]) ∧
    checkedRun beFC (fun f a => decide (f ∈ a)) [0, 2] = .ok [0, 2] := by
```

```lean
-- lean/Toy/Capture/Flags.lean:398-401
theorem cex_checkedRun_hrun :
    (∀ (f : Nat) (a : List Nat), instruments f a → (fun f a => decide (f ∈ a)) f a = true) ∧
    beOmit.run [1] ≠ .ok [1] ∧ (∀ f ∈ ([1] : List Nat), instruments f [1]) ∧
    checkedRun beOmit (fun f a => decide (f ∈ a)) [1] ≠ .ok [1] := by
```

```lean
-- lean/Toy/Capture/Flags.lean:411-414
theorem cex_checkedRun_hall :
    (∀ (f : Nat) (a : List Nat), instruments f a → (fun f a => decide (f ∈ a)) f a = true) ∧
    beOmit.run [2] = .ok [] ∧ ¬ (∀ f ∈ ([2] : List Nat), instruments f []) ∧
    checkedRun beOmit (fun f a => decide (f ∈ a)) [2] ≠ .ok [] := by
```

```lean
-- lean/Toy/Capture/Flags.lean:479-480
theorem srcAudit_of_irAudit_nonvacuous :
    irAudit progAuditOk = true ∧ srcAuditExemptExternal progAuditOk = true := by
```

Under the `havoc` reading of `opaque`, `qAsm` admits a run ending in UB, so no verdict relation sound for `semV .havoc` accepts `ubFree` for `qAsm`:

```lean
-- lean/Toy/Capture/Supplement.lean:24-27
theorem qAsm_havoc_no_sound_verifier_accepts_ubFree :
    semV .havoc qAsm (0, ⟨[], .ub⟩) ∧
    ∀ verified : VProg → (Run → Prop) → Prop,
      VerifierSound (semV .havoc) verified → ¬ verified qAsm ubFree := by
```

## Boundaries

### Non-claims

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend. The package proves no embedding, abstraction or simulation between the toy and any real system; a transfer of a result to a real system is not licensed by anything proved here.

#### `transfer-to-capture-input`

- It says nothing about the program before any pass ran; see `transfer-relative-to-erasing-set` and `capture-after-ub-erasing-pass`.
- Over-approximation is weaker than faithfulness; an over-approximating capture may make many specifications unverifiable (`qAsm` read with `havoc` admits a run ending in UB, so no sound verifier accepts `ubFree` for it: `qAsm_havoc_no_sound_verifier_accepts_ubFree`).
- Failure and divergence must be runs of `B` for `Sat` to say anything about them: `Sat (semS p) spec` quantifies over the runs that `semS p` admits. If `semS` admits no run for a stuck or diverging execution, `Sat (semS p) spec` and `OverApproxOnOk` hold vacuously for it (`cex_faithful_iff_htot` exhibits an empty source denotation that over-approximation accepts). The concrete toy reifies UB, erroneous constants and running out of fuel as outcomes, and every `semS p` admits a run on every input (`semS_total`).
- `Sat` expresses universal properties of single runs (`∀ b, d b → spec b`). Over-approximation on the ok-image is not shown to transfer existential properties (`∃ b, d b ∧ spec b`, such as reachability of a bug) or properties of sets of runs; such transfers would need the reverse inclusion (not proved here).
- No coverage is claimed: programs on which `cap` returns `.error` impose no obligation, and a capture that rejects every program over-approximates vacuously (`failClosed_empty_fragment`). A capture error neither proves nor refutes `Sat (semS p) spec`.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `transfer-through-pipeline-losing-no-runs`

- The hypothesis is per input: it asks for every pass at the inputs produced from this `src`, and the theorem gives no way to establish it.
- The scope remarks of `transfer-to-capture-input` apply: failure and divergence must be runs of `B`, `Sat` is a universal single-run property, and rejected programs carry no obligation.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `transfer-relative-to-erasing-set`

- `hEq` asks more than the proof uses: `transfer-through-pipeline-losing-no-runs` asks each `equiv` pass to lose no run at its actual input, instead of preserving every program's denotation.
- Without `hE`, the package proves the conclusion for the pipeline output (`transfer_to_capture_input`), and `cex_erasingSet_placeMention` shows that it can fail for `src`.
- When `spec` is UB-freedom (`ubFree`), discharging `hE` amounts to showing, outside the post-capture verifier, that no erasing pass loses a UB run at its actual input; the post-capture verdict adds no check of the UB that the erasing passes remove.
- [derived (modeling bridge); rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_mir_transform/src/simplify.rs L307–309] Not claimed: that running erasing passes after borrow checking discharges `ErasingSetPrecondition`. The quoted upstream comment orders the switch optimization after borrowck and says nothing about `unsafe` code; this package does not examine borrowck.
- [derived (modeling bridge); rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_mir_transform/src/lib.rs L649–663, compiler/rustc_mir_transform/src/remove_place_mention.rs L10–12, compiler/rustc_mir_transform/src/simplify.rs L128–130] Not claimed: that `-Zmir-preserve-ub` makes the erasing set empty up to `Runtime(PostCleanup)`. The quoted code disables `RemovePlaceMention` and the removal of `SwitchInt` reads; the other passes on the way (for example `LowerIntrinsics`, in the same quoted pass list, and the analysis-cleanup and runtime-lowering passes) and the change of MIR dialect are not examined here.
- Which real compiler passes are UB-erasing, and their preconditions, are not established here; the bridge section quotes documentation and proves nothing about it.
- The scope remarks of `transfer-to-capture-input` apply: failure and divergence must be runs of `B`, `Sat` is a universal single-run property, and rejected programs carry no obligation.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `capture-after-ub-erasing-pass`

- The toy passes are not shown to be refinements here; what is shown is that they lose the UB run.
- It does not say that any real pass behaves like these toy passes on any real program.
- Toy simplifications: an erroneous constant fails at run time with outcome `constErr` (a real source language may reject such a constant at compile time instead); `asm` is a fall-through statement (a real IR may represent inline assembly as a block terminator instead); `placeMention` and `zstRead` have the same validity check (null or uninitialized pointer), ignoring alignment and provenance; the drop terminator deinitializes a local and runs no drop glue. `simplifyTrivialSwitches` keeps switches on an erroneous constant (`passes_example`), so it never removes a `constErr` outcome.
- Fixed fuel: `semS` and `semV` run for at most `blocks.length + 1` block entries and report `fuelOut` beyond that; `fuelOut` satisfies `ubFree`, `noAbort` and `noAbortInCleanup`. So a loop that reaches UB after more block entries than that counts as UB-free (`fixedFuel_boundary`: `pLoopUB`), and deleting unreachable blocks can change a denotation (`fixedFuel_boundary`: `pLoopDead`, `pLoopTrim`). The other concrete statements in the cards (witnesses, counterexamples and controls) are checked by computation at this fixed bound, so the bound is part of what they assert.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `fail-open-capture-variants-unsound`

- It does not show that every non-error result on an unmodeled construct is unsound: `capStringify` read with `havoc` is transfer-sound for every sound verifier (`transferSound_iff_witnesses`).
- Toy simplifications: an erroneous constant fails at run time with outcome `constErr` (a real source language may reject such a constant at compile time instead); `asm` is a fall-through statement that outputs a value (a real IR may represent inline assembly as a block terminator that may diverge or unwind); `trap` aborts.
- No real capture tool is described.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `dropped-metadata-unsound`

- [derived (modeling bridge); rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_middle/src/mir/syntax.rs L666–671, compiler/rustc_middle/src/mir/mod.rs L1337–1341] In the toy the cleanup mark decides the response to a panic; in rustc's documented design the response is carried by the terminator's unwind action, so the toy pair does not establish that `is_cleanup` alone is operationally distinguishing.
- [derived (modeling bridge); rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_middle/src/mir/syntax.rs L675] The toy witness `pCl` has a call whose unwind action is `continueUnwind` inside a block marked cleanup; rustc's documented invariant (syntax.rs L675) restricts the `unwind` fields in cleanup blocks to `UnwindAction::Terminate` or `UnwindAction::Unreachable`, so `pCl` has no direct rustc counterpart.
- [derived (modeling bridge); rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1, compiler/rustc_middle/src/mir/syntax.rs L1046–1055] Not claimed: that the abort reason is observable at run time in rustc. The toy makes the reason part of the observable outcome; the quoted `UnwindTerminateReason` documentation does not say whether it is observable.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `no-faithful-semantics-for-merged-pair`

- It concerns faithfulness (equality of run sets). A merging capture can still over-approximate, and so be transfer-sound, if `semV q` admits the runs of both programs; then every verified specification holds of both (`verdict_on_merged_capture_holds_for_both`).
- Escape hatches: mapping the two programs to different results, or rejecting one of them, removes `h₁` or `h₂` (the fail-closed capture maps the cleanup pair to different programs and is faithful at both, `merge_hypotheses_tight`); and coarsening the runs `B` until the merged programs admit the same runs removes `hdiff` (the replace-flag pair, `dropReplace_merged_yet_faithful`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `faithful-semantics-exists-iff-merges-only-equivalent`

- The `semV` constructed in the proof admits, at `q`, exactly the runs of the programs captured to `q` (and no run outside `cap`'s ok-image); it is defined from `semS` and `cap` as a whole, so the theorem says nothing about a computable, total or compositional verifier semantics, nor about a given, independently defined one.
- In the toy, the cleanup mark and the terminate reason separate programs with different runs (`cleanupMark_merged_pair`, `terminateReason_merged_pair`); the replace flag does not (`dropReplace_merged_yet_faithful`, `clearReplace_denEquiv`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `toy-clearing-replace-flag-is-equivalence`

- It holds because the toy semantics ignores the flag, following the quoted upstream documentation; it says nothing about how any real tool or pass uses the flag.
- The underlying run equality `runS_clearReplace` holds at every fuel, so the result does not depend on the fuel bound; `clearReplace` also keeps the number of blocks.
- The toy drop terminator deinitializes a local (UB if it is uninitialized); drop glue, conditional drops, and any other fields that a real drop terminator carries are not modeled.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `transfer-soundness-iff-over-approximation`

- Faithfulness on the ok-image is sufficient, not necessary (`transferSound_iff_witnesses`, `capStringify_havoc_not_faithful`).
- Transfer soundness for one fixed verdict relation is not characterized: a relation that accepts nothing makes every capture transfer-sound (`acceptNothing_control`).
- Necessity uses the quantification over every specification: the proof instantiates `spec := semV q`. For a verifier that checks a restricted family of specifications (for example `ubFree` alone), over-approximation remains sufficient; it is not shown to be necessary there (not proved here).
- The scope remarks of `transfer-to-capture-input` apply: failure and divergence must be runs of `B`, `Sat` is a universal single-run property, and rejected programs carry no obligation.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `fail-closed-and-fail-open-obligations`

- Fail-open is not always unsound: a fallback that over-approximates is sound (`failOpen_overApproxOnOk_example_pos`; in the concrete toy, `capStringify` read with `havoc`).
- Refuted earlier candidate statement: "the concrete captures have the shape of `failClosed` or `failOpen` on whole programs". They do not: `capFC` returns construct-specific errors (`refuted_capFC_has_failClosed_shape`), and `failOpen` never returns an error while each fail-open variant does (`refuted_failOpenVariants_have_failOpen_shape`). What holds instead: each fail-open variant is the partial extension of `capFC`'s result on the programs `capFC` accepts (`failOpenVariants_eq_partialExtend_capFC`), so `partialExtend_overApproxOnOk_iff` splits its obligation into `capFC`'s and the variant's own on the rest.
- Coverage is not measured: the fail-closed capture on the empty fragment rejects every program and over-approximates vacuously (`failClosed_empty_fragment`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `over-approximation-is-faithfulness-for-total-deterministic`

- The hypotheses ask for totality of `semS p` and determinism of `semV q` whenever `cap p = .ok q`; nothing is claimed about rejected programs.
- Any nondeterminism in `semV q` (for example a choice of addresses or of a thread schedule that the run records) breaks `Det (semV q)`; then over-approximation is not shown to imply faithfulness, and `cex_faithful_iff_hdet` shows that it can fail to.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `toy-fail-closed-capture-faithful`

- Faithfulness is a property of the toy interpreters; it is the positive control for `transfer-soundness-iff-over-approximation`, not evidence about any real capture.
- Fixed fuel: `semS` and `semV` run for at most `blocks.length + 1` block entries and report `fuelOut` beyond that; `fuelOut` satisfies `ubFree`, `noAbort` and `noAbortInCleanup`. So a loop that reaches UB after more block entries than that counts as UB-free (`fixedFuel_boundary`: `pLoopUB`), and deleting unreachable blocks can change a denotation (`fixedFuel_boundary`: `pLoopDead`, `pLoopTrim`). The other concrete statements in the cards (witnesses, counterexamples and controls) are checked by computation at this fixed bound, so the bound is part of what they assert. The step-for-step simulation `capFC_runV_eq_runS` holds at every fuel, so faithfulness does not depend on the bound; `capFC` also keeps the number of blocks (`capWith_fuel`). A capture or pass that splits or merges blocks is not covered.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `toy-stringify-with-havoc-over-approximates`

- Under `havoc`, for an input on which a run reaches `opaque`, the specifications that hold of the captured program are those that every behaviour satisfies.
- The toy `havoc` is whole-run: reaching `opaque` admits every behaviour for the input, including behaviours whose trace does not extend the output emitted before `opaque` (`semV_havoc_admits_any_trace`). A havoc that keeps the emitted prefix or the unmodified state is a different semantics and is not studied here.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `flag-contract-sound-iff-no-silent-omission`

- Backend behaviour and properties are toy parameters; nothing is claimed about any real backend.
- `hObs` is a real restriction: omission can be harmless when the property holds anyway (`cex_flag_hObs`).
- The response `respond : F → Response` is per flag and does not depend on the rest of the configuration; `HonoursAdmitted` excludes interactions in which one admitted flag overrides another; `build` takes the list of admitted flags and no source program. Configuration-dependent responses and flag overrides are not modeled.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `checked-artifact-restores-flag-contract`

- `checkedRun` is a function `List F → Except F A` around `Backend.run`, not a `Backend`; the conclusion has the shape of `FlagContractSound` with `checkedRun` in place of `Backend.run`, and the proof does not use `respond`.
- The check sees nothing but the artifact. In the toy, erasing the place mention of `pPM` gives `pRet` (`passes_example`), so no check of the output alone can tell whether a place mention was erased or was never present; detecting the omission of an erasure-disabling request would have to use information beyond the output artifact, for example the input program or trustworthy build metadata (not proved here beyond the toy pair).
- The check is a toy parameter; nothing is claimed about any real checker.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

#### `exempting-source-audit-weaker-than-ir-audit`

- The audits are toy functions; nothing is claimed about any real lint, audit tool, macro hygiene or attribute semantics.
- The implication holds in the toy because `expand` keeps the unsafe flag of every plain item and every item is code that the IR contains. Whether an audit of a real lowered IR (for example a function-body IR) subsumes a source-level audit is neither established nor refuted here; source constructs that a function-body IR may not represent (such as declarations outside function bodies, foreign-function blocks, global assembly, conditionally excluded code, or the syntactic extent of unsafe regions) are not modeled.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real compiler's IR pipeline, about any verifier that consumes compiler IR, or about any compiler backend.

### Attractive stronger conclusions that are not established

- That a verdict about captured IR is a verdict about the program before the passes ran: the package derives this from the pipeline hypotheses of `transfer-through-pipeline-losing-no-runs` or `transfer-relative-to-erasing-set`, and `capture-after-ub-erasing-pass` shows that it can fail when the erasing-set precondition fails.
- That faithfulness is necessary for transfer: over-approximation on the ok-image is the exact condition for every sound verifier (`transfer-soundness-iff-over-approximation`), and `transferSound_iff_witnesses` shows that `capStringify` with `opaque` read as `havoc` is transfer-sound for every verdict relation sound for `semV .havoc` and is not faithful (`capStringify_havoc_not_faithful`).
- That failing open is always unsound: `capStringify`, a fail-open capture, over-approximates on its ok-image when the verifier reads `opaque` as `havoc` (`capStringify_overApproxOnOk_havoc`).
- That a capture covers any program: rejected programs carry no obligation, and the fail-closed capture on the empty fragment rejects every program and over-approximates (`failClosed_empty_fragment`).
- That existential properties (reachability of a bug) or properties of sets of runs transfer through an over-approximating capture (not proved here).

### Escape hatches

- `no-faithful-semantics-for-merged-pair`: mapping the two programs to different captured programs, or rejecting one of them, removes `h₁` or `h₂` (`merge_hypotheses_tight`); coarsening the runs until the merged programs admit the same runs removes `hdiff` (`dropReplace_merged_yet_faithful`). The conclusion concerns faithfulness: a merging capture can still over-approximate if `semV q` admits the runs of both programs, and then every verified specification holds of both (`verdict_on_merged_capture_holds_for_both`).

### Tightness status

Every hypothesis in every ledger is `tight`, with a named Lean counterexample whose witness class the ledger states; no hypothesis is marked `harmless` or `unknown`.

### Earlier candidate statements refuted in Lean

- Refuted earlier candidate statement: "a capture is transfer-sound for every sound verifier iff it is faithful on its ok-image". `transferSound_iff_witnesses` shows that `capStringify` with `opaque` read as `havoc` is transfer-sound for every verdict relation sound for `semV .havoc` and is not faithful; the exact condition is over-approximation (`transferSound_all_sound_verifiers_iff_overApproxOnOk`).
- Refuted earlier candidate statement: "every capture that returns a non-error result on an unmodeled construct is unsound for some program". The same witness (`capStringify_overApproxOnOk_havoc`, `transferSound_iff_witnesses`) refutes it.
- Refuted earlier candidate statement: "transfer soundness relative to one fixed verdict relation is a property of the capture". A verdict relation that accepts nothing makes every capture transfer-sound (`transferSound_of_verifier_accepts_nothing`, `acceptNothing_control`).
- Refuted earlier candidate statement: "the concrete captures have the shape of `failClosed` or `failOpen` on whole programs" (`refuted_capFC_has_failClosed_shape`, `refuted_failOpenVariants_have_failOpen_shape`); what holds instead is `failOpenVariants_eq_partialExtend_capFC`.

### Dropped or disproved statements

None. Every result of this package is proved, and no statement of a result was found false.

### Not examined

- Real compiler passes, real verifiers, real capture tools, real backends and real checkers.
- Whether any real pass is UB-erasing, and its preconditions; whether borrow checking or any other analysis discharges an erasure precondition; the effect of IR dialect changes along the pipeline.
- Captures or passes that split or merge blocks (the toy's fuel bound counts blocks).

## Evidence

Observed 2026-11-21. Toolchain: Lean `leanprover/lean4:v4.34.1`, tag commit 5045d0056413266e57c625dcd7c365b10e377c52 (GitHub `leanprover/lean4`, `refs/tags/v4.34.1`).

**Kernel check.** `lake build` of `lean/` succeeds with no warnings; no Lean source contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]` or `unsafe`. Every declaration of the library depends on at most the axioms `propext`, `Classical.choice` and `Quot.sound` (computed with Lean's `collectAxioms`; recorded per declaration in `audit/axioms.json`).

**What is hashed.** For every Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of the Lean `repr` of its type (statement hash) and the SHA-256 of its definition closure: the sorted list of `name : repr(type)` entries, followed by ` := repr(value)` for non-theorems, of every package constant reachable from the statement (theorem bodies excluded).

**Per-name record** (`audit/statements.json`, `audit/axioms.json`): Lean name, axioms, statement SHA-256, closure SHA-256 and closure size.

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- |
| `Toy.Capture.Backend` | none | `7e100a5ea88c20a932cc3563ffe20596912e5db0a2c25554e863cd4633db46cc` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Backend.run` | none | `4e51d1659845e66f61f59b1cab4a12eaddb44e70bd27d92288c3bdb2cfa4feb7` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.Beh` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.CapCfg` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.CapErr` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.CfgFCExceptAsm` | none | `938e692b12ce5421bea35565b31c1da0904eb84e49124ae5b8d3100416993865` | `571a344ab7ff37be9c593a3bb1f0463aace78fdc0815cf6bef476baadb18e55c` (2) |
| `Toy.Capture.Const` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Den` | none | `ac04b7a8462b88437b2fcc81d013f2d2454df5a6ca33ffae5d54ebdd38ba7c3d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.DenEquiv` | none | `61a3590f6aaabf16dbba1177bb9bda8f559eb2e381efee42d27ff016f69ab128` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.DenIncl` | none | `61a3590f6aaabf16dbba1177bb9bda8f559eb2e381efee42d27ff016f69ab128` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.Det` | none | `f9976449c3779b411384b87f4c2aab2929c7da14f3a435fd9d52f6f9d251ba4a` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.EquivTagSound` | none | `226e23d51ac3fa3b7d7bbdf0ea417dd70548ebe1ad63ef3a18c88725190598ec` | `d236fd57f115d71808fbec124e785359e4711daf2934bc770c64db2d224d99cc` (6) |
| `Toy.Capture.ErasingSetPrecondition` | none | `59927bcc0d1b224b691ab20b0f49361f9b8cd7b0d6b940f068996a5ef166f112` | `d236fd57f115d71808fbec124e785359e4711daf2934bc770c64db2d224d99cc` (6) |
| `Toy.Capture.FaithfulAt` | none | `d8e68941e574acf2968b6b6f6ec2c0c5cccb0ae5883b0ebac6799ead0a75936d` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.FaithfulOnOk` | none | `56591d718a83dbbfb956d94e3b76e7469745371f1c3a2caee65a3d84d0788935` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.FlagContractSound` | none | `b2d86ada3fd323e352716c41953ff60bddb2af3b3f6a6d122e79537f7e4d2efd` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.HonoursAdmitted` | none | `b2d86ada3fd323e352716c41953ff60bddb2af3b3f6a6d122e79537f7e4d2efd` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.InErasingSet` | none | `2a073d7b8b40b9095476f79c3ecac2a31a912c77587129ac1cc1b0570f2cd827` | `0517fdb6c5ceaba00db035b5305e8f55a4de6f6792f95e0e7f83da005d24fc77` (5) |
| `Toy.Capture.Item` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.LosesNoBehaviourAt` | none | `e0308079ca453b6808ace9c5d8120283d31c6a86a54ae2c2788c80a6306a0bc8` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.LosesNoBehaviourAtInputs` | none | `59927bcc0d1b224b691ab20b0f49361f9b8cd7b0d6b940f068996a5ef166f112` | `d236fd57f115d71808fbec124e785359e4711daf2934bc770c64db2d224d99cc` (6) |
| `Toy.Capture.NeverOmits` | none | `9300c14b5d4ed50cec9a27c8708ec48ab55f3d4fb0c3ac4f21d5b3b50b0c6a2b` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.OmissionObservableOnAdmitted` | none | `b2d86ada3fd323e352716c41953ff60bddb2af3b3f6a6d122e79537f7e4d2efd` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.OpaqueSem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Outcome` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Outcome.isAbort` | propext | `d26d0f741e484ea4a7f0d2087229756d2b8fccea0e5bbfc54859c96999b5145a` | `f60c348bad5d5ff220f75e32abb084855007467cc58f47092889ed30e7fd66f9` (11) |
| `Toy.Capture.OverApproxOnOk` | none | `56591d718a83dbbfb956d94e3b76e7469745371f1c3a2caee65a3d84d0788935` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.Pass` | none | `a8dc5c150dffbeb8ef8091cecafe85672f8110e0fe10cca4d6a5836328177c85` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Reason` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Response` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Run` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.SBlock` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.SOperand` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.SOperand.eval` | none | `c24ab538578be35d3cab461647a7d8bd47e6e2093fc5c1d03fede62e8a4c7948` | `f59bdd5cba25be2c17d1024d713c11c9a3fdfcdc7884af8e721e2a85916eb83c` (19) |
| `Toy.Capture.SProg` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.SProg.fuel` | none | `cea097b85d2358bdfe3dee8f0d50930bad782d5f288288c9cef7bc3c6a2b6b04` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.SStmt` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.SStmt.isPlaceMention` | propext | `c6c200e3dc3e608c61250853bb8f027656073e7a86a8ca17fbae3619a956c256` | `69a40aaf302feafcaf7e5ed8de5b3295e02800e8be43160a0505568621a47458` (12) |
| `Toy.Capture.SStmt.isZstRead` | propext | `c6c200e3dc3e608c61250853bb8f027656073e7a86a8ca17fbae3619a956c256` | `69a40aaf302feafcaf7e5ed8de5b3295e02800e8be43160a0505568621a47458` (12) |
| `Toy.Capture.STerm` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Sat` | none | `f8d910b81ca7601cd276ac5d474c59a2eef72285ea3a79a48a6bf277b911f3a4` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.St` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.St.emit` | none | `2e810e301ac8876093fb5da463686ae9d400eee65078156540c7d23678a7f0bc` | `3237a3892f4bc162bfa5dbe735f5f58a4dbb750ad3779373e540fdb481562c66` (2) |
| `Toy.Capture.St.fin` | none | `087970f5d43dafe1352df774fd12747379dba460c7de6bd81f0dd7d2e5f6f06c` | `38fd7a2d55c408e64bcb73756c4a7057ab4c7cdb1a998ca4b11971b1efdffbca` (15) |
| `Toy.Capture.St.init` | none | `ba43303969f4dd44ddd9172f1e58862fcd75ef757a8479434311a87bebf133ad` | `3237a3892f4bc162bfa5dbe735f5f58a4dbb750ad3779373e540fdb481562c66` (2) |
| `Toy.Capture.St.set` | none | `e167c2f2d036f293b368ccd0c9d8a64aa2c4634a51f103611cd99e324624460f` | `3237a3892f4bc162bfa5dbe735f5f58a4dbb750ad3779373e540fdb481562c66` (2) |
| `Toy.Capture.Tag` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.Total` | none | `f9976449c3779b411384b87f4c2aab2929c7da14f3a435fd9d52f6f9d251ba4a` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.TransferSound` | none | `319323d5ca4bdbf5dd6613c44486cbb48695fae48a4dfcd2c9c421d5167ecee1` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.UnwindAct` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VBlock` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VOperand` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VOperand.eval` | none | `49dc112bb09e0f35dd3265318fd31ab93779754ebf24344a1f979c8db2d545bb` | `a6e6654c64d146d4157306092f768dcf72e8a85b0acd16e2dd5377ac2a76c2b1` (16) |
| `Toy.Capture.VProg` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VProg.fuel` | none | `8cd595f0e7b496a045dbc3b5a774f9c16ae92fe61c5411f37e48ccf850f90d0f` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.VRes` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VRes.admits` | none | `0ad408311996480860b66036d96e0aafeaef647a425cd2f9f19a21f4284ab0ee` | `81013364ae43b360fb835a7c587d5936539710a8e16d4e0764bb6a78b04bda4c` (16) |
| `Toy.Capture.VStmt` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VTerm` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.VerifierSound` | none | `84dadae1f5bf72cb851f10e1eb80c6b0f1de6af3ac322a60c0520a4ed2ca385e` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.acceptNothing_control` | propext | `227de59353d28366dc2984b50a6c6b6b7cfe2e14a54cbf9f73898dc12f9f1a22` | `e4780a3a1cde63bc1dd0775d441d766151ab891f4c839c75069ff9b822ec1a40` (183) |
| `Toy.Capture.beFC` | none | `3d3927dc61b7a4ba37ff317f2a7a68a942193371725a7a3fa6de921ba685a7e3` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.beFC_honours` | none | `fd496e47add0f5f4f9fa55f1720179a693603366fed5793e1aac7471588a697c` | `a4c4933832fbc7fca91789fbf17ce229254f1133fcd74b1ec257d78e7346fa47` (11) |
| `Toy.Capture.beFC_observable` | none | `83d1f0d0e9f1b81ff74478c7f8515608ce192d4b7d1c4bc94a26bb27c8da3aed` | `47b37084be616678869aa487190dcc77df8a5cd42ad9250baf4a58a9770c4d41` (11) |
| `Toy.Capture.beOmit` | none | `3d3927dc61b7a4ba37ff317f2a7a68a942193371725a7a3fa6de921ba685a7e3` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.beOmit_honours` | none | `09fe7b0d9c6c6d5423a6435288abfc832fd653b69392c306dcc4407199bbfa49` | `485b4fe7c56464c7e28c7f3790a98903c4bfe733645c87fb5845bf50b3ca1767` (11) |
| `Toy.Capture.beOmit_observable` | propext | `c1155cb329aa1c74eac97ed0ea6e5130847822d9b6c0e458e3f6ca5937de374c` | `e06649a71df41a077ed5e9a7e3e620302a626bc27bd77628e78cbee940551173` (11) |
| `Toy.Capture.beSan` | none | `16fb0d107901dc96c25b80d4026382b66392a81eedfa952e1e58abf8d7577ac7` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.beSan_instance` | Quot.sound, propext | `2a87386a80f71683c3e83a49b79eb4fc53fedfd80892bd0cfd8030b88d8aae19` | `8da53e2326c69960ad871c0dafb3218219d1a55f486e4938f8a79ecd54910ebd` (22) |
| `Toy.Capture.capBlock` | none | `f79b95d1cf13f8346dc73d7bd761d01570f0b2b7184cd5754317db134e19deaf` | `3bc764cb9e8a33638e06d5bf0f48dbc58ffb23e0150ddb954a4a8f65d493aafc` (56) |
| `Toy.Capture.capBlocks` | none | `7dff3fdfd4e8db42f2daa80e4f8aff5a33091b5e34378190d2e6de032bc72160` | `3bc764cb9e8a33638e06d5bf0f48dbc58ffb23e0150ddb954a4a8f65d493aafc` (56) |
| `Toy.Capture.capDefault` | none | `974948c55dfe0b15acf124f09676334f6202ff03d408cece3ee131379bdbd95b` | `1621b11b7a1247b2b481daaa693baaf2cba82b83bf95d273397ca85c9dc21a2e` (58) |
| `Toy.Capture.capFC` | none | `974948c55dfe0b15acf124f09676334f6202ff03d408cece3ee131379bdbd95b` | `1621b11b7a1247b2b481daaa693baaf2cba82b83bf95d273397ca85c9dc21a2e` (58) |
| `Toy.Capture.capFCAccepts` | none | `66c9f2b44662ece2bec2db5a9d647834457ce3636519e59b955a7291f0f84043` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.capFCOut` | none | `a0afd5b5b8989e235f7bab52e93e2dc53bac7af2eecc44946885499744bf159e` | `b4471914898c8fdcc334a25c13ef84be54e2de660720fa1fdbd67f0a82e2ef9a` (54) |
| `Toy.Capture.capFC_faithfulOnOk` | Quot.sound, propext | `25e0822762c84a1a16378b79ca10dd2bd0dab518c418693e6c6251225fff4671` | `28afea70b4a7d4438c6936abaf2ee9e4078f1537bad34a96bf3717b9b324a880` (180) |
| `Toy.Capture.capFC_image_det` | Quot.sound, propext | `58cf164d86ca3d5dfb8eb24bf1dbcb6f722ca8cabfe27805eaa8d787d4d26432` | `a787f07468638689fbf8d3dbf49a7fb11de46ac39dc09c826f9faec10b310595` (167) |
| `Toy.Capture.capFC_pAsm` | none | `a93764669987824d8b037ca7c56c91babba8c5a0b887be384f7998fa6a2f5456` | `ca1892f67c463435743a1720acbe5a1fd62c58510015d03127b21a89dece5f5d` (99) |
| `Toy.Capture.capFC_pCl_ne_pNo` | none | `5afb3de28e7c7ad9ef2eacd1cb5c0c16cba774336f61807ae5c7916b0e5a1e44` | `f246058d162b50981c7239225f311189b4e2c353ab7f35828170eb447479af80` (100) |
| `Toy.Capture.capFC_pErr` | none | `d45d32a39604df120961c044f6480c0a9f865c55daef411ca90e981c8dfc0ca6` | `9195ff278b3936a1fe6f8753dea8137bd15423f7d46e6bbf4b3c9bc5519c6bb5` (99) |
| `Toy.Capture.capFC_pPM` | none | `eea6356e629b64a3799ad1d01fa426694b7460bd1163f169534ade5d081ecdd0` | `dc4b15b44e383b25de64d41d44dd3e1ed12113b0ad5ac470112d25a29e12614f` (100) |
| `Toy.Capture.capFC_pTerm_abi_ne_inCleanup` | none | `0e75d523590cc4fff5a03f3f83c42020e405e390f74c8092cc93b2b9a24411fc` | `2e9900544aad0382753a8016282880c8c7d5ad56c9b213ec0815e450e6000477` (99) |
| `Toy.Capture.capFC_pTrap` | none | `9e83424958417b8e488baeb469bc3de0b421f82ca9c0948d04d9000ad5432bd7` | `8f4273d8d38f53e069319d2e652b1a4955db73ce36c20c55dd0c29eafaa3a732` (99) |
| `Toy.Capture.capFC_runV_eq_runS` | Quot.sound, propext | `c2c152b023990c9a45ff103d4f04348063b8625df739ba7d5330b315a1e832ca` | `0fc0a5965be79fe1aa592e2706ffc8f346decee4bb460e76b96c07109d4b0b44` (167) |
| `Toy.Capture.capNoCleanup` | none | `974948c55dfe0b15acf124f09676334f6202ff03d408cece3ee131379bdbd95b` | `1621b11b7a1247b2b481daaa693baaf2cba82b83bf95d273397ca85c9dc21a2e` (58) |
| `Toy.Capture.capNoReason` | none | `974948c55dfe0b15acf124f09676334f6202ff03d408cece3ee131379bdbd95b` | `1621b11b7a1247b2b481daaa693baaf2cba82b83bf95d273397ca85c9dc21a2e` (58) |
| `Toy.Capture.capOperand` | none | `cc4bb0ddecc51a954dcf492c671e41652f59bc8ab725b98d5b67e894de4f38d5` | `803965193ed852b79b492b6990da121b9fd111ec47b265267d0fd905e33bb6cd` (15) |
| `Toy.Capture.capStmt` | none | `c931d5a52e0f4d6eb3c356e534c372e151815a69741869b6680ef61d7a98d107` | `8d570bdc0a4f938a72e2150e674878d2d82760dbaf876e53d3421eb5e8cef299` (27) |
| `Toy.Capture.capStmts` | none | `8ff31d5669feeb3bf16389f9bffcb0fe498f9c065a688ac24d0145f2a82689dc` | `8d570bdc0a4f938a72e2150e674878d2d82760dbaf876e53d3421eb5e8cef299` (27) |
| `Toy.Capture.capStringify` | none | `974948c55dfe0b15acf124f09676334f6202ff03d408cece3ee131379bdbd95b` | `1621b11b7a1247b2b481daaa693baaf2cba82b83bf95d273397ca85c9dc21a2e` (58) |
| `Toy.Capture.capStringify_havoc_not_faithful` | propext | `68e4e01c8df6302557a2814ae5808b4e0aa88ec51e4afbab869af617817c1936` | `3aa201fff28e549541fb412e877a939d928b79cbaac54bcd0d935499cded88ef` (180) |
| `Toy.Capture.capStringify_overApproxOnOk_havoc` | Quot.sound, propext | `d2f0f2c39608d679f1503ff7e4c75a99b0eb4016380960665615d0d9caa23341` | `983ac95d1ab75ff65d4e53c96660ef7f1f79749001a150b5d8f47ef38826e007` (180) |
| `Toy.Capture.capStringify_pAsm` | none | `025242a9cfcd872b900243dc27797761e32e1aa697b2571f0d0188a26f448785` | `53ce7644788d7243e8d9a3d2c38cc1140517424ec8dc55f85ec04102b52919e9` (100) |
| `Toy.Capture.capSwallow` | none | `974948c55dfe0b15acf124f09676334f6202ff03d408cece3ee131379bdbd95b` | `1621b11b7a1247b2b481daaa693baaf2cba82b83bf95d273397ca85c9dc21a2e` (58) |
| `Toy.Capture.capTerm` | none | `e82655d44e0a2dcf27fa66d35b8a2985b439964d3fc84b201741ee32c9faee26` | `489e55f2e409f6e471d354c093e80c772a5c7b76137772ad8350fdeb9f8cdc74` (40) |
| `Toy.Capture.capWith` | none | `f5f4eb848429acea9c520ad6523cdbb4d87c5de9c64e59a6dfc26382d3357390` | `dae0f2fcb7252744e40ba38908031b5969710356cf725f6b1db514fb6c312f43` (60) |
| `Toy.Capture.capWith_fuel` | propext | `4261fbf925c17c58a5ffb271362a2483788585994d40242ded4bf1ae0bde2f3b` | `7e684c7f4b759807ebc76fb8b5f905cfc9e317e78d0a4a707cfa4fc3a0c55cfd` (99) |
| `Toy.Capture.capWith_runV` | Quot.sound, propext | `1f8f5c80d43203ebd9d7e1c852f6348ecffde4393f970f71b3145fe114d59d31` | `2c4dd965a1bedbeb5e3df17d97a220517a1c07dd5cee92f694525072d0892f7a` (167) |
| `Toy.Capture.cex_capFC_runV_h` | propext | `daed76af6959626cd456fa783cfcf4afdb9958ef997537c5c1d140a5210409d7` | `2bc36a3eede5854eac69fbfb934a3d48896c2cacdcb8c846330293bdb6d060e6` (170) |
| `Toy.Capture.cex_capInput_hV` | Quot.sound, propext | `2e9631b001b7a1eb132f381979bf6a2f095cc0880e83604bf86876355b1deeb5` | `18fbcb47ce80cfe020b75713a5e93515f5e2e29b25ba5fcba882d4301e66e223` (187) |
| `Toy.Capture.cex_capInput_hcap` | propext | `974a7f177cf72572b52328276db8186dac888645409432bcd308afe1381a7581` | `31a9332b27d5c058aa0286a59ab8c0d64dc3b63875e76ced0fd0494cc1ae46a7` (187) |
| `Toy.Capture.cex_capInput_hok` | Quot.sound, propext | `32130be61ea470d78cc4a324e9e29d57e4bcc82033c72fa064af681490879f58` | `d26c7f1b4f08e1eff360cccb49276df5effea0caaa8c91d863c7c0546206458e` (187) |
| `Toy.Capture.cex_capInput_hver` | Quot.sound, propext | `25a4cd93d8ffbc0aaf58c1014c1316d13be124ccb8c6a62888ced29e4b6fd0ff` | `254a54edae4280581560426c9b21bb4ff750e598d0d147185176c4b656adc75e` (187) |
| `Toy.Capture.cex_checkedRun_hall` | Quot.sound, propext | `d0f689d9c226bf9c47d4368571717b2125bcf23768ea4055158afeb4d87871a2` | `3d38b129b35eea8168d405154049607560001b20ba6f5b475139fe87b1b3fd30` (20) |
| `Toy.Capture.cex_checkedRun_hcheck` | propext | `da349ca2a899e9c3235e0bffce04671245ac9f022fcb0f1c4925a04ae6b9b778` | `3d38b129b35eea8168d405154049607560001b20ba6f5b475139fe87b1b3fd30` (20) |
| `Toy.Capture.cex_checkedRun_hcomp` | propext | `3f71fcbb6b5d851eeeaef1ae5932d3300b8040e1e25f8904d5302810dc0f5e95` | `12cde4daf77321c6dabc0b5e0e09196aebd0756a13a69d1bdf43a4919409426e` (20) |
| `Toy.Capture.cex_checkedRun_hrun` | Quot.sound, propext | `995c54ecf925ba453b487a547e89f0d5277e3232392122e08839865840b2c1b9` | `3d38b129b35eea8168d405154049607560001b20ba6f5b475139fe87b1b3fd30` (20) |
| `Toy.Capture.cex_erasingSet_placeMention` | Quot.sound, propext | `1ccb735a3c45bd00d03483a7e0cf51cb03f7b32369f022be2e34c520d9ae9926` | `d35512ca29545b08ba1a57458beb1fe6640ee529b0e78f06f5c11a2e58cbac46` (207) |
| `Toy.Capture.cex_erasingSet_trivialSwitch` | Quot.sound, propext | `a703c567d77c5e53244153fd0ee146b713304bea23f7d93b14d303c730308408` | `4e9c83ca881be71196ada767528bb65313fbbbad68ee38a1ad0b4c3903b30c8a` (222) |
| `Toy.Capture.cex_erasingSet_zstRead` | Quot.sound, propext | `02279d3688458e2724a7adf3cf88d165b5cbc27be8d1c01fd9aa7abe4357ff6e` | `145cb45bffb15ae21f9a1e4e595554d052462c782cf7238ad488deba28e0326d` (207) |
| `Toy.Capture.cex_faithful_iff_hdet` | Quot.sound, propext | `974dc916739c2ad02a960a9e84fbbbc83e9b5006c1b053f3bc47b498a4c71fda` | `df78c57ebeaeb55688c5e94ff0e69eacc3bb7eb292868a17025ca6f7c9e9bba4` (184) |
| `Toy.Capture.cex_faithful_iff_htot` | none | `b42383c892b11eaeefb1a5cd15874b230c1061c09f51129288fdd642e13a88e9` | `23ea3914a671ee630e2069e28c1cd4beff8620153fdb29653a58c2f136d6359b` (7) |
| `Toy.Capture.cex_flag_hAdm` | Quot.sound, propext | `c4199e2a4271459aa330dfd65fc7b166e817039887555bef719432dae52ca1cf` | `a0334d344fa2fadc1d3e2b5b56e4ac0daf3ad6b9fefe493856d8f6c523ba5a19` (20) |
| `Toy.Capture.cex_flag_hObs` | none | `fa3b5cfaa8455756d23d5670f24667efddabbc3d4c0b98da84edb71c2fe1deb0` | `a0334d344fa2fadc1d3e2b5b56e4ac0daf3ad6b9fefe493856d8f6c523ba5a19` (20) |
| `Toy.Capture.cex_flag_hS` | propext | `b9b362f07f8929351e9813e927fb939b84ab5b2112307df651ee64f6e3c21ddd` | `99fff5f36e17d5da21d84d6960ebbaa6bdf7ecd98813fa24f776b56e8608ff60` (21) |
| `Toy.Capture.cex_flag_hno` | propext | `9ecc1dcc052f5f983871417b3c616d5d72541475df3440c5a8d61ddf1069aff4` | `ea97de9793e87f781f72faa6a81fb9be9ea118dd3299c6e994d1c35814eb1805` (21) |
| `Toy.Capture.cex_hEq` | Quot.sound, propext | `c66e4e23e6c76fc603fa1acc609ab13fb8269378050491d14b0a1a631bcddf6c` | `922936b5ee88ec639acef0dbcfe495da6281fd4f8cad7d020836477915b10e53` (207) |
| `Toy.Capture.cex_hV` | Quot.sound, propext | `4319c92e3a7aa11a2ba1bb4d25adee856ed10446bf7fea55081ca4f828ea1611` | `791dd0601d95742322f5eeb2d175daa4c304ebebd20e48a49f682b778534b6d1` (201) |
| `Toy.Capture.cex_hcap_default` | propext | `a73a12fa21694607fc7a53c4080838778bef57d4cde8efbb1d12ff943499fc9a` | `d3004b9d22128e2b7599436e0effdb3d0c6abf9db015289359d18fc9e33aad46` (201) |
| `Toy.Capture.cex_hcap_noCleanup` | propext | `92df453a5b1bf9d8b8153b086e65c2f6d8827d6274301d3187526dc7ca28f9f5` | `9bccc7dd2841a73564bdcbfc240c3bffaf2d8bd88ea6f0338c0d947e556f348a` (207) |
| `Toy.Capture.cex_hcap_noReason` | propext | `67fed2f31150fab4a812cb521eaaae16e9ecee00a2841ad59c5fedadd0bade12` | `f8a396affc438b4d95eeaf4ba8535fed9626bf2f5191c04183a266892974d4c1` (201) |
| `Toy.Capture.cex_hcap_stringify_noop` | propext | `91925511f09035a388ecb43af57805dc9caf37bad45f84a5e1975d424502718a` | `1649779d0affa9fd1ad3d00d28fec831de25159cf7600ccd13884ab8aead8b18` (201) |
| `Toy.Capture.cex_hcap_swallow` | propext | `265ef8df1c96a37c16ba5da184b5c423f268dd99105c9e260cce23b4346167d1` | `d306854c25d246b723b7eb330b05755c7c556370ce535c1ad93c19fca523bae4` (201) |
| `Toy.Capture.cex_hok` | Quot.sound, propext | `000a400d8ba7c04dcb6dcc70db76c9b5be74657aca76ae32d0d73f6a870f3f07` | `5c9280c3a4f7674ffbcfc2cae3c4eecdb32c306d567b2d4aa044a1b514128b8c` (201) |
| `Toy.Capture.cex_hver` | Quot.sound, propext | `e0d98450f92cb9d62e5a35b152756554b001e13db7a4c1132f4dd0f64718e135` | `4492e2a4745f2619b8886802d61ab0fb39a3628becc89e6b61fa7d8584d83998` (201) |
| `Toy.Capture.cex_pipeline_hV` | Quot.sound, propext | `280cb51125e3f3ed83ab4bea5519d848f030522e0060a7bb1eb767d2970e8437` | `f6e85af329d7699afc77f52de7e662d6594ba0c6a80d490353398be8070e331d` (198) |
| `Toy.Capture.cex_pipeline_hcap` | propext | `64d9a9e73f0cb9c7e36662ade13739ca5f8e508c85dcbb99330e6eabb27aaa03` | `158f3e006d82d44005f0c91246523f6a9cb4400b6a28dc8ca965bf08a987105d` (198) |
| `Toy.Capture.cex_pipeline_hok` | Quot.sound, propext | `ffacc8c17c281d5b0ff21fb6de6ec9ec95e493fdf56bedf4011053c9220ab709` | `0fa4301c28f450339f8b157e9d6e1e51dd1717f9075009d146d93a15e125b32a` (198) |
| `Toy.Capture.cex_pipeline_hpipe` | Quot.sound, propext | `9c9f40218cb8cb2f942022f9f2b8fae5998d504491dc805e2921aec8ec043402` | `de5498796d9a6bada48c697b65ac214f9cdfa34b9330fdf629ba00fbfbdc9a68` (204) |
| `Toy.Capture.cex_pipeline_hver` | Quot.sound, propext | `f1dc7caf4898735ffa4a480cce98c916e61297dc684a181d9bfe1bd763ec8995` | `0ee756a2d14a69d311ebab67e6de3b6ab285a770f46720cb3111399327a4cbaf` (198) |
| `Toy.Capture.cfgFC` | none | `c31cd30acd188045dd92061b0bd2dd6b413d9d750ec05abda5769197db2c2505` | `571a344ab7ff37be9c593a3bb1f0463aace78fdc0815cf6bef476baadb18e55c` (2) |
| `Toy.Capture.checkedRun` | none | `72d97c8eeedceb227d0b613fe4fbd60e882be7e8bb2bc003cde5922c85b0a31a` | `bd8d5ab1acbc5711f7492b974ad2500deee627dfc40053602785fdcfd8d68af3` (6) |
| `Toy.Capture.checkedRun_contractSound` | Quot.sound, propext | `345c0c2d28a9afd2247adac68b0b7484f2e57ee4ebf93d05e53d7175828c408b` | `6994449769dcb4b1c72567912343cd673f473ebc0351216493f7f5aaea2e407e` (18) |
| `Toy.Capture.checkedRun_detects_omission` | Quot.sound, propext | `f6bc0b0cf5a3991c1f590209f4a59fc8b5f068da113c7505a5ea5d030c69da47` | `9e31ce7b86179648285813df0f2a09b9a6072665a9555173bb774d758d00ddc0` (19) |
| `Toy.Capture.checkedRun_eq_run_of_holds` | Quot.sound, propext | `6a673ae1dcadd8eeff2a562523b681748902ecc3ff1033ffc1baa5416dfa9b36` | `6994449769dcb4b1c72567912343cd673f473ebc0351216493f7f5aaea2e407e` (18) |
| `Toy.Capture.checkedRun_nonvacuous` | Quot.sound, propext | `fb3aaf536a39b00d026acc8b409994b37a778934d92ffbd19749a781ed70554b` | `5ff9507373338e3c109336d8ee8ffac44be24f20cc53a0537693945202a02c3f` (21) |
| `Toy.Capture.cleanupMark_merged_pair` | propext | `1b08e07f30b6866403bfc38d075cef53499947cdcabaf393b0998691e37377df` | `fe800a31809c3ad041f267457f387fb02c04a348487255514c54f206ec6df7a6` (144) |
| `Toy.Capture.cleanupMark_no_faithful_semV` | propext | `29fb8d1a0fc4984bd7bc6c0daa9979dbebc78c3f0a813b1c230815ca6f3bcc36` | `006eaeed103c37490157dfb5d52d901ea48c43776cae1d7df03b57254e877c79` (145) |
| `Toy.Capture.clearReplace` | propext | `5da8de1f4046798907190b777c352a54351381fe41cfe70a2dc21b885905a1dd` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.clearReplaceBlock` | propext | `f4eda1a6123ac7113bf88a3988f25993250470d5b2e2c81efd99df25d07a2970` | `3fb9e3b709cf06375b2fefd541f3cd260a22205512558b2db6143236d47045bb` (30) |
| `Toy.Capture.clearReplace_denEquiv` | Quot.sound, propext | `70a8fffedade25d8e89be356fc07f0bd24243a12b2209870d1a38b75e5fbe382` | `3006c968ca2344879644cef67d71301fa712ca1c12aa604aff42ca9496cbb15a` (95) |
| `Toy.Capture.denEquiv_example_neg` | propext | `4775cad4c06034fef21e85ba07db5747efcf32fca9187ac464252fa6cdc0cb40` | `da09b87f18a4c961d98d986492cec83dd184c9aa5fbf0f1d9b73e8aeec10771b` (92) |
| `Toy.Capture.denEquiv_example_pos` | Quot.sound, propext | `bbebca84bda2cbfa1f8567af4ad6ccf44d4bd0ab990249f3549119782812f906` | `8947752dd7dce064192585b9b7e1680001d7dccac4fe2a92e3be288bafc337b4` (96) |
| `Toy.Capture.denIncl_example_neg` | propext | `15ec0073b3faf80bbbda6565e932ae86aaa66a3770404ca51e2120b0be10a53b` | `69ac7cb70252a8260f38b9fa9946292e64ba91e53f870054dceb04d0b0929435` (152) |
| `Toy.Capture.denIncl_example_pos` | propext | `5a818a7a4f7c756cc0e7671ea4943d30528b0bee76ba28fd546f8db7af66a3d5` | `69ac7cb70252a8260f38b9fa9946292e64ba91e53f870054dceb04d0b0929435` (152) |
| `Toy.Capture.denIncl_runPipe_of_losesNoBehaviourAtInputs` | propext | `655aae6fde9cbfe306db146a0c49e76ff41535012a4bcc65274896b9ed6e83f4` | `57167a08ef1995caa30d62947e00087fb30fd904c49cf94eb3772990a80b7266` (13) |
| `Toy.Capture.derefOk` | propext | `a110d158c946075bce51d8af1a85865afd3680b8c0f9d96d0f07482d8a2dbe88` | `3237a3892f4bc162bfa5dbe735f5f58a4dbb750ad3779373e540fdb481562c66` (2) |
| `Toy.Capture.det_example_neg` | propext | `f6d2eb876beece65c65e9b265a42e181f507885fddfe5a28eca19e193112c125` | `19434adf77d438eee4f13fe31be52da9c4180a4b529b15ba64716286f00e9951` (98) |
| `Toy.Capture.dropReplace_merged_yet_faithful` | Quot.sound, propext | `dcf2b94d28a373d21a0c27437b40d56779b4ee64a8f425bfc22e1ef1aa0eb071` | `89f382bfd8e9155bf06a4d363785c5c4f49048a1353ee6a6e52895f049620910` (182) |
| `Toy.Capture.equivTagSound_erasing` | propext | `6dc066f41c1b1654a8b078f4cd529f3da7d2f7389855bef52f504912176bfb5a` | `47ddba3424dff70782b2d3d484cc5a2afc578a0930e7ef2e3c035ed39f00eb76` (98) |
| `Toy.Capture.equivTagSound_example_neg` | propext | `7f787712418814a8d7fc06179a5063764bf70071a89ca62bbb5c87508512df29` | `b5a5b9350bd3f873827e8d25520b5511bf35395edb49b8d3f459044b1daa444f` (103) |
| `Toy.Capture.equivTagSound_example_pos` | Quot.sound, propext | `8fec03b7a2b08f42c557587c3c12bd46c7961e5a165d72379569ce6e14988457` | `725b07990440a98327f6b40e9f8793fd8916f5d53db9e46162bac6cc358239a3` (103) |
| `Toy.Capture.erasePlaceMentions` | propext | `5da8de1f4046798907190b777c352a54351381fe41cfe70a2dc21b885905a1dd` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.eraseZstReads` | propext | `5da8de1f4046798907190b777c352a54351381fe41cfe70a2dc21b885905a1dd` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.erasingSetPrecondition_example_neg` | propext | `91996edee777712b4c33a14cc99fe31c80446e570549903580c0592c38c4981e` | `6beb961d76c614b620724343e6be241a6d75a06d9b8f0abcf6c416d5879f0445` (109) |
| `Toy.Capture.erasingSetPrecondition_example_pos` | propext | `48a909e8e377b7c376674d18e60a723fecdcba5d0706c1e2c47edba1a644511d` | `a112ed47041b90842d2ede02c500efd8742f40dff722c494396c2970a997da5c` (114) |
| `Toy.Capture.erasingSetPrecondition_iff_forall_inErasingSet` | none | `089e5dc04cb7d74cfb5b0626cdb924b1dd1d1c4af46099c86bc7a52e8af6cb31` | `7da9e2c3451a28b0e4b01cd9762d6dc6bf2cb7d658d57c8ab2b7a36d53d04e1e` (15) |
| `Toy.Capture.erasure_disabled_control` | propext | `04f6b3af806707639566ac09be9e83a6bfa9398ebaed7e19a64be476881b2e4f` | `d9622d64a573bf0b740cf5d3608c8793d5c7f9a1f35a834bbe0e8efd12093ae1` (181) |
| `Toy.Capture.exactVerifier` | none | `226b14c350fadcd875afd3f55b5d40f947a2639980c469fd27fcea947d3b30d0` | `177d67651c5298e73ae75b9760060e981af4c1a01871a445d49f2939b4fb9e58` (1) |
| `Toy.Capture.execSStmt` | propext | `74015a0e92ab9a75f23690ead6ccd51011fd57904386fadc99053f55db207c9b` | `10cf1490058c1c5ea52e96183b68bbc05017e6d5631dce89af465d401b939c00` (27) |
| `Toy.Capture.execSStmts` | propext | `591d52f978192584d5d031ff53139c0256b251c324ef1a023fc3409bba92bf95` | `10cf1490058c1c5ea52e96183b68bbc05017e6d5631dce89af465d401b939c00` (27) |
| `Toy.Capture.execVStmt` | propext | `050cfd4daae08eacd43c91accd406e735e4f538416e683d19d5a74af4532a272` | `218234c985eb202994ef6249bbfd40cfe326031cff5fcde5993b890573860cca` (30) |
| `Toy.Capture.execVStmts` | propext | `6919da418bee00e07918ca8035ca5c11992cb45ccbd2af7ce07b1377deb0f538` | `218234c985eb202994ef6249bbfd40cfe326031cff5fcde5993b890573860cca` (30) |
| `Toy.Capture.exemptingSrcAudit_strictlyWeaker_than_irAudit` | Quot.sound, propext | `19432d72bac752c3093e8d4ef2a317ddfd55ba2a2b63e0736abfd70dbab13578` | `82e2adabfcf6ab577ae263c0ccf09fe44c359a50cbd767a621feb93912725b3f` (11) |
| `Toy.Capture.exists_faithful_semV_iff_merges_only_equivalent` | none | `0199dfca0f5bcb5293aa586f777ae52622340012d710d92760e9eb3da69f69f5` | `63b48af8df102b337437d8f87d3d242596311804a8a08c6b1cd7c96892454199` (3) |
| `Toy.Capture.exists_faithful_semV_witnesses` | Quot.sound, propext | `ac61318cf94578b646bf74307cd143d5c097bcc057733a96152b9c1879601d9a` | `a3125176c509abd05a58575b2d97933b82bfd8b6d8ab07cbb3039dd9156b666c` (143) |
| `Toy.Capture.expand` | none | `7009a2b024f32e84e70f00ef561bcd6d2388f35775fe8e93ae154d1e5b669865` | `933a62e82f4aa1c8559ff91b9c4f478bf1dabc63c2cd06da29d823e1028df278` (3) |
| `Toy.Capture.failClosed` | none | `bb8d7ff29a8bb91af7b758dd371d0aa499b0389a96b7d002d0453f7121f6d241` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.failClosed_empty_fragment` | propext | `399d5d0034a35dde71495581d618c732cbd72cdd55543767ea272c1bb2f85185` | `f2cfc0cce0307771b3bad8706b35221dab5e7758451386a2c516e3f612767996` (4) |
| `Toy.Capture.failClosed_eq_partialExtend` | none | `589b32713af64970fa97328f9f4d776b337f2ad2b6b28a6cf5207a4fb469f1c4` | `5e2e929611acea2b5bdb85dc7675bd6e90695743ad2f4d28248fa4db3200feff` (2) |
| `Toy.Capture.failClosed_example_neg` | none | `d69f9f40bb87a405f7b2ad7232a4763bd68d18100f66f8e56898ca437bc2adad` | `1483788790599658922c74896fb090a96a36c04889da303ba701ad26cbc93237` (1) |
| `Toy.Capture.failClosed_example_pos` | none | `564fc8aa9dedfb2ce795d2d0b90ad14602198f4b507bd33cf3b36e17de700342` | `1483788790599658922c74896fb090a96a36c04889da303ba701ad26cbc93237` (1) |
| `Toy.Capture.failClosed_failOpen_witnesses` | propext | `a5510b8d805d1df36774f2ee5e05c02fd17433bd226258474620031f1acb5fca` | `84a759f34b906161e183ffd2493f6fd026013e6145ba5e27382f9dd209035074` (5) |
| `Toy.Capture.failClosed_overApproxOnOk_iff` | propext | `00ed27d4f9d41060c07389d579a95158a081ef44435b5fbe89dd3da63aed39fd` | `f2cfc0cce0307771b3bad8706b35221dab5e7758451386a2c516e3f612767996` (4) |
| `Toy.Capture.failOpen` | none | `046f5c38a3417323365e9351ab2eb5ee565dafee5057457b39c847a63f0c8f6d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.failOpenVariants_eq_partialExtend_capFC` | Quot.sound, propext | `d5a5cf50c07bca5a51bfbc2134ad8534e75d705d033321b16033e003c10a1967` | `e019831296f230e4cd6b152197c8f5408769d5b59c0abfe4f157e520b5198e5b` (109) |
| `Toy.Capture.failOpen_eq_partialExtend` | none | `4eb25cbc02b23126c8c5f95aa86d2a8975707734f5978fdedb6c6bb6238672ba` | `0e1f41b1b4e81ba404067a05c53d78374702c0e34eee10604339a27b972d5579` (2) |
| `Toy.Capture.failOpen_example` | none | `59318b3970298b28cf4798fe1b183be35f2ff9f47775817096dfc39b5379d86a` | `55fff9e067d22d6f5c142954cd9bd214482e0f173f90226d7cf72f9df3a9c959` (1) |
| `Toy.Capture.failOpen_overApproxOnOk_example_pos` | propext | `b286044461297843d3060f8ae1e76708779e1c4f1fd4caf2c8c1fba747fc3078` | `0e9c362096775b04605bd5edb2411ad38293456d59a8f138669d11aeb1d3cff9` (5) |
| `Toy.Capture.failOpen_overApproxOnOk_iff` | propext | `18e7d32cc285bb0ea149eacaa16207453fddc75319bfc312fe1b51536ab1fd9d` | `f6db4b1a959819dd4ba67a27c462f904065223929819c92ecc92ce79495848cc` (4) |
| `Toy.Capture.faithfulAt_example_neg` | propext | `7bf3057fa71ef130d041d82d2ef92b06431481760891fd7f7e8e683fa1c81cea` | `9981e52709515c46a198295013527e183e70ecae8c0e0680de788ce871ca06d9` (181) |
| `Toy.Capture.faithfulAt_example_pos` | Quot.sound, propext | `49075df265111ed7a6f170147b4c305081aae94e4dc6fb4cb84cb25bd9d668b5` | `341895030b68156f63ae4c4f2ca3afa7643ed703ae584a86adca9484da7d989b` (181) |
| `Toy.Capture.faithfulOnOk_example_neg` | propext | `6450f9cff67eebe33c9cb2edd35078b1e9ff552e27348df4a836717bd518f140` | `29997aa4901e78a6d459dcd3722ed7a77e823554dde5b58ddf3c069aee51bfcd` (180) |
| `Toy.Capture.faithfulOnOk_example_pos` | Quot.sound, propext | `25e0822762c84a1a16378b79ca10dd2bd0dab518c418693e6c6251225fff4671` | `28afea70b4a7d4438c6936abaf2ee9e4078f1537bad34a96bf3717b9b324a880` (180) |
| `Toy.Capture.faithfulOnOk_iff_overApproxOnOk_of_total_of_det` | none | `ea91df7a5962d73757af10ec1501ecdab250dbda46e06e87e4da517a33f1e3ab` | `23ea3914a671ee630e2069e28c1cd4beff8620153fdb29653a58c2f136d6359b` (7) |
| `Toy.Capture.faithful_iff_overApprox_nonvacuous` | Quot.sound, propext | `9697d2d0e63021317672909251988083a381828f660ebfb2cd8700bc77974132` | `a63dca94d0051330c2b8f5f14256ba485cc4c225c7e901444b6bb7fcac8f8e8f` (180) |
| `Toy.Capture.fixedFuel_boundary` | propext | `6089ff370b68f53140741e0d24146f01846cb7cbf200c0b79dee8af9b589edfd` | `986d393248b391005f04fa2e2c7bea055f1a9ea332c2046089b734cca83f06b5` (96) |
| `Toy.Capture.flagContractSound_iff_neverOmits` | Quot.sound, propext | `ecc1a9589bf0ee9c78dcfdd32bc76673fe1d2fcc64e61c7a55dd0420386fd9cb` | `a0334d344fa2fadc1d3e2b5b56e4ac0daf3ad6b9fefe493856d8f6c523ba5a19` (20) |
| `Toy.Capture.flagContractSound_iff_omitted_hold_in_admitted_contexts` | Quot.sound, propext | `54bc3aeac6d2e858332076ed6379309fd9b84a55aa23081015fd9a20216f4f85` | `da5b38019986aece47b83eb07b5f163498cefcfad778f23bd004a035c28bef5e` (18) |
| `Toy.Capture.flagContractSound_of_neverOmits` | Quot.sound, propext | `afa4787583d3789b7faf8528e79d02991a1a99593888215049e1edd6b84ab6af` | `fba62696a6989fbbe2daa653cd7fd3a093f2e36d45ac2255d8fbbffcc2b4ea3e` (19) |
| `Toy.Capture.flag_nonvacuous` | Quot.sound, propext | `95342f9bed797f7fc18101a3ceb61b4a2df9ec9b07f28b5b0a7d56483dcabb82` | `cb1e8aabeb74a1ca355c8e1fa71ff384b8b611ce7835e73ce5352f6fdcfa5b73` (23) |
| `Toy.Capture.inErasingSet_example_neg` | propext | `dc14843e5a2d113c2f1585d73ed99cdd861957c0b2bef7a7fd9b3fd8d6562851` | `7c57762f9dd22eb1a3efb5caa42adc6acddcb9eaef57aa3c9efb9fc9b6e69072` (59) |
| `Toy.Capture.inErasingSet_example_pos` | propext | `4e8b7bdfd0b9d1e052e1e3be91100a859c6efc9542ff7a7cfa35812224ccb6dc` | `c1ae8301a6eec171692b87b8824f98d4398c42a7bbdeb9f158b843fee00c7447` (51) |
| `Toy.Capture.instruments` | none | `74a6beb817457fdf386d69f652b57006d9d1975825e63ed2c35536d262bed679` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.irAudit` | none | `4993959825b25722381cbb43a0523803d5c9539c94465b5462f8287e52432186` | `933a62e82f4aa1c8559ff91b9c4f478bf1dabc63c2cd06da29d823e1028df278` (3) |
| `Toy.Capture.liftS` | none | `c43617c1e7c1ecd3ead56c1cd174dcdfeec1562a461be5de4c31b08bb09468c5` | `eb3ea6ef7da016c2345bc050bec467fa287d96885bed92758f5b5269074d92a7` (18) |
| `Toy.Capture.losesNoBehaviourAtInputs_example_neg` | propext | `7ca7a4ac39a519b14910e23dcfe75da1bd8a6350c35d932989775140436d2b89` | `1bebafa50e54b785f7788f5ebcf8e75c1533ad998791c83e01506fe47b03f70d` (108) |
| `Toy.Capture.losesNoBehaviourAtInputs_example_pos` | Quot.sound, propext | `33b759139da3aec5380d8ad15ec57af79a9080e683d87fd0d0852f1504ed1fd5` | `6b582c88d08715667a245778c75516540230f1680d536084d68bd50bed17d879` (113) |
| `Toy.Capture.losesNoBehaviourAtInputs_of_erasingSet` | none | `02a7cb0b83d6b9cb5f357294a1bb56f48e4348e910044ade339bf11b35dd2cb3` | `b4079e9dd884e537bee7c44e216e115e2af2299a4616c5ac160bc385ced71d53` (17) |
| `Toy.Capture.losesNoBehaviourAt_example_neg` | propext | `1c5ce30a6548d6f2701a9aaa5a1233bf1dbbf3df7cb54c03d837d8699a43ad25` | `601a2ef5ebb78a57552354e08ae3fbd816e372548a288f32946b0afceeeaba82` (97) |
| `Toy.Capture.losesNoBehaviourAt_example_pos` | propext | `380739dce39515db12c95da05f4e665c726341763cff80f22e68284c200d9ca0` | `c7cff347886b6a495bb86c90a9ad3f62b995e9f7067c84365909ddf38eb7910a` (97) |
| `Toy.Capture.merge_hypotheses_tight` | Quot.sound, propext | `67e2dee18627c7543c5dd811273f79d3dac39ab01246b1375bea1004f98f8809` | `ebcf43de556bf5f0c4e2055839cae1ec2c396003d66aa612b54291a9d83afe60` (184) |
| `Toy.Capture.neverOmits_of_flagContractSound` | Quot.sound, propext | `67ef47281cbfa33aef4c539974d82458c8fd7fd0ff53f176950c7b5da257d926` | `c7fda4e75c014196fd1bc144a347f37a3e5f9da4f30f2cdd7cfa5eb91929c30d` (19) |
| `Toy.Capture.noAbort` | propext | `f1dc3b010f6cd0167752b6254d612b67f13f00439b0a8c7000e696fc5b484509` | `5599e05acd2754e7ad3c54f4c8de178f4d5c901cc6d7bdc704f55c24e8f8fef4` (14) |
| `Toy.Capture.noAbortInCleanup` | none | `f1dc3b010f6cd0167752b6254d612b67f13f00439b0a8c7000e696fc5b484509` | `5599e05acd2754e7ad3c54f4c8de178f4d5c901cc6d7bdc704f55c24e8f8fef4` (14) |
| `Toy.Capture.no_semV_faithful_at_merged_pair` | none | `66b4391afc392a22dc367e55414f10ad0fe29f6868cf1c5800b13f03cc192efd` | `f44ed785792d73b4dee0603f6a226ee41b78615f63b8cf7cd6687a050c28708a` (3) |
| `Toy.Capture.not_faithfulOnOk_of_merged_pair` | none | `5f68f6d9fcb0d60cce2d8c4d6d70558c00e3367c8816a0e91399c7d437329d3a` | `63b48af8df102b337437d8f87d3d242596311804a8a08c6b1cd7c96892454199` (3) |
| `Toy.Capture.overApproxOnOk_example_neg` | propext | `ae3af5bca12554521f8f06622f02fb19317ff1f340c1291989854858559e4a01` | `983ac95d1ab75ff65d4e53c96660ef7f1f79749001a150b5d8f47ef38826e007` (180) |
| `Toy.Capture.overApproxOnOk_example_pos` | Quot.sound, propext | `d2f0f2c39608d679f1503ff7e4c75a99b0eb4016380960665615d0d9caa23341` | `983ac95d1ab75ff65d4e53c96660ef7f1f79749001a150b5d8f47ef38826e007` (180) |
| `Toy.Capture.pAsm` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pCl` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pDrop` | none | `887e4d2f8cbc7cb880d535d9478a9016d4d72f6f57039a956f542e4817c0a2d5` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pErr` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pLoopDead` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pLoopTrim` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pLoopUB` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pNo` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pOk` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pPM` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pRet` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pSw` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pSwConstErr` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pTerm` | none | `d982722b2e19d65324646304750bf479d1a86a80aa419ffed51d9b255981781f` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pTrap` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.pZst` | none | `52673a9876f30b0745f0956ea7852c732ae52bd5c87530736334852806616549` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.partialExtend` | none | `76c90a829d4de4a5e517ed9e04f93064ccd7a1de9e8fbd29000504ebb575a62d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.partialExtend_overApproxOnOk_iff` | propext | `27b58a5b6759015d6965733603169daeccca71d55edce8048b85e683bdc5c72e` | `b5806da695ee4ba5f6e828a183754519f99ace82dd5966ffb264541659c7444e` (4) |
| `Toy.Capture.passPM` | propext | `b523f60c26bd4c4757b5a70778ac1a9b729a2d24e33dd0772ff18562d3d2ef80` | `257dd7a3282f3ae38fac6d27d3ebad1626d8401c4db92b1afe5c48ae1ea956a6` (37) |
| `Toy.Capture.passes_example` | propext | `fbc14ce4274ae813f43d485e5b1a568cbd5ca12d11503709023203f8d4d1d8ae` | `98b51f53e86afb10a573dd968502b2b7a94eb3aea9397f7d3f7664609ba2ed9c` (84) |
| `Toy.Capture.pipeMis` | propext | `24cf67f1bbd847cf66d388198cbaa79762eb4e50f341878c72d2b97c3a3a3440` | `257dd7a3282f3ae38fac6d27d3ebad1626d8401c4db92b1afe5c48ae1ea956a6` (37) |
| `Toy.Capture.pipeOk` | propext | `24cf67f1bbd847cf66d388198cbaa79762eb4e50f341878c72d2b97c3a3a3440` | `257dd7a3282f3ae38fac6d27d3ebad1626d8401c4db92b1afe5c48ae1ea956a6` (37) |
| `Toy.Capture.pipePM` | propext | `24cf67f1bbd847cf66d388198cbaa79762eb4e50f341878c72d2b97c3a3a3440` | `257dd7a3282f3ae38fac6d27d3ebad1626d8401c4db92b1afe5c48ae1ea956a6` (37) |
| `Toy.Capture.pipeSw` | propext | `24cf67f1bbd847cf66d388198cbaa79762eb4e50f341878c72d2b97c3a3a3440` | `257dd7a3282f3ae38fac6d27d3ebad1626d8401c4db92b1afe5c48ae1ea956a6` (37) |
| `Toy.Capture.pipeZst` | propext | `24cf67f1bbd847cf66d388198cbaa79762eb4e50f341878c72d2b97c3a3a3440` | `257dd7a3282f3ae38fac6d27d3ebad1626d8401c4db92b1afe5c48ae1ea956a6` (37) |
| `Toy.Capture.progAuditOk` | none | `022da2139760ae2da6abae5f2fcd7aa1c3ae092197f0a082201a052072916a81` | `933a62e82f4aa1c8559ff91b9c4f478bf1dabc63c2cd06da29d823e1028df278` (3) |
| `Toy.Capture.qAsm` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qAsm_havoc_no_sound_verifier_accepts_ubFree` | propext | `2b78b94082a47dbbdbc9544739b53cf5376e11b40858d90f785b7f4302270203` | `7842c641cf7feea39aa29bce744d72355dcd5ef30ed8d29fc538edf58984dac5` (101) |
| `Toy.Capture.qCl` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qDrop` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qEmitOpaque` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qGoto` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qOk` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qPM` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qRet` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qTermAbi` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qUnw` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.qZero` | none | `364dd772896ef2752a1563b88cad47acb9230d8565dd04031515249b513b4dbb` | `39b79197069285ad1797ee5f9b1099b71d77529d0dd051d06ec0990f39cd9339` (28) |
| `Toy.Capture.refuted_capFC_has_failClosed_shape` | propext | `d85ec3a27270e1b8d01514c800ca665635acfadc77122098401ece1d9b6078fc` | `355e92122c141a81cf90b610e8a912c254f4b249675695f15db67a87f4a4e6aa` (99) |
| `Toy.Capture.refuted_failOpenVariants_have_failOpen_shape` | Quot.sound | `30cba32b21b1e65164d1fe2587a529c622902948839f765067563b7721c620a1` | `86f488f9f68b4f11be66d7bd939bcfdd13da64499f68c670fc34d9bde352fc35` (101) |
| `Toy.Capture.returnsNormally` | none | `f1dc3b010f6cd0167752b6254d612b67f13f00439b0a8c7000e696fc5b484509` | `5599e05acd2754e7ad3c54f4c8de178f4d5c901cc6d7bdc704f55c24e8f8fef4` (14) |
| `Toy.Capture.runPipe` | none | `95a9ee6c2c6ff5625f74e958017eed22938f2353e3afd4abb623d2e7d987ef96` | `0517fdb6c5ceaba00db035b5305e8f55a4de6f6792f95e0e7f83da005d24fc77` (5) |
| `Toy.Capture.runPipe_example` | propext | `ebe9b3aaa047ab57b3176f2ff19f65fced080be78dda13479a521d15fc0ea3be` | `8b8a543a8f90045f39100219bb4052ffe97d8441edfa9d8281c6735354d1e7c2` (61) |
| `Toy.Capture.runS` | propext | `f299f290b663cdec7d41ce74267ae26f8dbf975227a3781d39b8eb2b382d5b67` | `b5b7405a7b42311cb70f66e315d7caef4eb2821179d630bbd556374d2f5fd504` (44) |
| `Toy.Capture.runS_clearReplace` | Quot.sound, propext | `a21026139f9b59796fa2bc0bfa269e10691d32a5ca0037b52acc54426ffa2ff8` | `ee948f4210ff01c4f957ea26331582e30c594469cf001a9b2d03bb78fd7d901e` (89) |
| `Toy.Capture.runS_pPM` | propext | `4d98525c36567c15f5ae78ca44ade45e12b9e938716cf88ab5af22925032b324` | `19465c0af9f472a73d26be71ae590d4147f3db4e94f141aed8b5d3d1977d155f` (87) |
| `Toy.Capture.runV` | propext | `0be835aeac453f3e1149ef7de09f4e37fc412de20bf683a480df6dced1c668b1` | `1b09ac4aa1d4a9c955e2e96315e468cde0f3eb7c43db9e21b9ff8e372537a28f` (46) |
| `Toy.Capture.run_example` | none | `fe8aeaf084ee8fd3fd0d5f4f3e50f417b22c7f6193b63c61c9c7220c7ea1d7ec` | `b60917756dc712b8b5c3a33afe7d2fead36fb085be3db3567b8fe137551d19ed` (18) |
| `Toy.Capture.sanHolds` | none | `e123622a969ddaf443dcf89b853da91ce5e467385dc02fc00228b0a07feacd7c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Capture.sat_example_neg` | propext | `b1c10a7211c0ca8a510975363efdcf259f0e4dcadd1331bdc0fefdd9ded93159` | `ddd210d53a21ce17048c5e52b34f448350ced7ccf427521e04c9b4ba0a5b357b` (93) |
| `Toy.Capture.sat_example_pos` | propext | `8e49221af071ca70ce7ab784316f139500fd587e46317fc2f0efff2a1d6e65d0` | `15df781a481ec1a58fbbbf7bb3c0499f5e5073a33b751fe451abee240aca8b80` (93) |
| `Toy.Capture.semS` | propext | `ba55feabf5046d29fc40fc19b224018d7eaa8a69ae1298dfc98bcf8e5049023a` | `c0e086acfb7cf8143bc42f0145592d43154056e8398cea6e70b960508c1804cd` (44) |
| `Toy.Capture.semS_det` | propext | `56b05efffb18e862c24ec58330cecedd8a07d974fe9c369c66230ae8244af8ee` | `35a8957bc2b3dc8f8ff7ac6dd8ae5f9bb4101b48e0b5dc7039fd5bd38ec29be0` (90) |
| `Toy.Capture.semS_example_neg` | propext | `6d039441d44e118c6872e17c71f85d7aec0d9cb13c50fcb893c886715d8d7f0c` | `f61478dcebdab633f7cc3c756f92d54b0bdb41d7c3afa046640b6d11eb44ff49` (90) |
| `Toy.Capture.semS_example_pos` | propext | `96487ae05fe1989a9ad9e44370e942ce5aae4389cb2ba19b983e24b057da0975` | `f61478dcebdab633f7cc3c756f92d54b0bdb41d7c3afa046640b6d11eb44ff49` (90) |
| `Toy.Capture.semS_total` | propext | `b88b9fc02147b3d1db3230915edc699c448c85bdf9f9f76131dfe7168ca42fdc` | `55241b1b8fb1fd2be2e9992e951d870ac8167c22964681f10a17c604df15c30d` (90) |
| `Toy.Capture.semV` | propext | `0dfddf2bcad1ae5a0e710abab012632a045c0adbeceae5cee12f6f444498922c` | `9d5fb6e16826af1aa6859528b44a0588f8a614e31c38db306b15f14f41ad2a31` (43) |
| `Toy.Capture.semV_example_neg` | propext | `eba81ebb7b4855f82bc31683cd6f1e73a8b9f61d7b74b9f0cff828f70c1f8810` | `63ce596c3f2f756776b4406630037df133fc695b36441f8972bff4d29fd95e4f` (97) |
| `Toy.Capture.semV_example_pos` | propext | `8ed034fdb1199abb8c57ba2cca6dabf01e6dbcee1c77aec9c89bee6e3c470827` | `63ce596c3f2f756776b4406630037df133fc695b36441f8972bff4d29fd95e4f` (97) |
| `Toy.Capture.semV_havoc_admits_any_trace` | propext | `54cc0c25a0bd8878c044827506f3837661280bc30e1b390c38c73d3f84a2bc4d` | `a17d6c7c096b46c0c5de726bba54b085a2641cc2cc68fcfea7877aba2207ae31` (97) |
| `Toy.Capture.silent` | none | `f1dc3b010f6cd0167752b6254d612b67f13f00439b0a8c7000e696fc5b484509` | `5599e05acd2754e7ad3c54f4c8de178f4d5c901cc6d7bdc704f55c24e8f8fef4` (14) |
| `Toy.Capture.silent_omission_breaks_contract` | propext | `f4208fd9ced00080d4d3bbcc7d70afaf27e8673837944faa4c78f9640438428b` | `c533494ec92967fe112d34816c787f518f36dcdbb78e15936f76cb799a5b31c5` (19) |
| `Toy.Capture.simplifyTrivialSwitches` | propext | `5da8de1f4046798907190b777c352a54351381fe41cfe70a2dc21b885905a1dd` | `6fb071fbb83125d2304daf50d10d8f55861e047ae54378819be19d1a714032d8` (32) |
| `Toy.Capture.specs_example` | propext | `57981f2872cfad55f06f59b9959681b9daf72ccb7605a5c2b5bb5ec790cad7c3` | `d5bab7c4d2daaba394421432d0e45f8c36e7196128678b8edfd18f6dc405e56a` (27) |
| `Toy.Capture.srcAuditExemptExternal` | none | `78ecabc330621687dac65a1e0db4caa2aa49d516543c1b442bb3d5b8684b96a6` | `933a62e82f4aa1c8559ff91b9c4f478bf1dabc63c2cd06da29d823e1028df278` (3) |
| `Toy.Capture.srcAuditExemptExternal_example_neg` | none | `77ecdf1f2c452bbed507e6136700f162cd01e03efb7e05e28c530249d67eaba7` | `2c9b3e81a946169d86487ce2699dfe794ba746291dfba5c90d38944229452c05` (8) |
| `Toy.Capture.srcAudit_misses_external_unsafe` | none | `112c5a93e2d804f84dc19dc4d083834bbc41679eb861fc23695d44ddc65c3e0f` | `82e2adabfcf6ab577ae263c0ccf09fe44c359a50cbd767a621feb93912725b3f` (11) |
| `Toy.Capture.srcAudit_of_irAudit` | Quot.sound, propext | `7669640f909aaba49e84665a14ab7e9b7a3e97e1f0e953071998ada202eb6726` | `82e2adabfcf6ab577ae263c0ccf09fe44c359a50cbd767a621feb93912725b3f` (11) |
| `Toy.Capture.srcAudit_of_irAudit_nonvacuous` | none | `ee5de8dcb8f2347e6ed7183136e348b6d7b7db3535c0e0796eaf2db646ed60a8` | `1afd1d0072ca3d3129ad015876be15444cf0ce9b7391579748cf0f3a5407070d` (12) |
| `Toy.Capture.terminateReason_merged_pair` | propext | `e9ba705561812c2dffe23f442364c9f5e8c16652995ff87b87e6a7c0c7ab178e` | `33b8292cc33058116637387c876130eec2c794c1595b2d4e1c00ceb0b16d6707` (143) |
| `Toy.Capture.terminateReason_no_faithful_semV` | propext | `a953003521f994158a3b0c7b7c29f74f2d7260269269f8a2368c70b0976dedb5` | `e11f86400a93b4b21443c33b3e4ebb7359491b86fafd728b5eec15a4f434de21` (143) |
| `Toy.Capture.total_example_neg` | none | `626dc1fd7e3a5d3ca626d9f67b69044cbc5bd68fb868be65326359745b8d2d93` | `9ec4a0a1c432c1ac7d636edbd8d7b387a686de1f621ece2e5485b16609cb63e0` (2) |
| `Toy.Capture.transferSound_all_sound_verifiers_iff_overApproxOnOk` | none | `261221e1457b9ba3decd9ffd9879b19fa917c737aa9ba456fd09c8c1cb7d41bc` | `215634105e0d1f328c26867b6a5a804fe2eef8dbfc746e95296ff34e578776a6` (6) |
| `Toy.Capture.transferSound_exactVerifier_iff_overApproxOnOk` | none | `d1b9ea191708e8fc47572c6b0f8b98185b5a378eb07298bba6994d374ba1445c` | `52e96099768818b9d40cec85c7a5af4abe6b7b693e9edc802502666ad230b81e` (6) |
| `Toy.Capture.transferSound_example_neg` | propext | `ff744f2d87a02ccf9be703852b05409751d5e51393d42f7e39a7d8dea7d73b0c` | `c87ffaaeedefc15638ec2c894a7b154b77d25bde166875b003ea65d637854caf` (181) |
| `Toy.Capture.transferSound_example_pos` | Quot.sound, propext | `99dff4a66886d943d87ed5cf5ea8ffd8a7706835060731c0f9b00cae2b4e8dc2` | `e48dadec2bf4c0b396166162b25250a2f597396157bbd9b344315c92d95340cb` (181) |
| `Toy.Capture.transferSound_iff_witnesses` | Quot.sound, propext | `d5b7d143e233f88a5b6926c02dff430cfe38c68af0474d183dbf551d95c2e9a8` | `894cfddbd6891fdeeaf7c6397c8f8a19555a1896f1ad8b9dcdae217d3394f2bc` (187) |
| `Toy.Capture.transferSound_of_verifier_accepts_nothing` | none | `dacc4447c02852c149665a37ff4a68e6203de8c090ab1580d6496198a1b05250` | `b41272a75e122a4ccc22daa9b2510ec8b381a504178402bd17d6c5b3ee15ab12` (3) |
| `Toy.Capture.transfer_of_losesNoBehaviourAtInputs` | propext | `461eff618516c0b5ed1a6cb4b08fa2c370e6866de09f6e1402a8e38ac4d68725` | `58d067287d31cd4b2b287bc10253958755b094ff89b2b969cf772d7f245c5b50` (16) |
| `Toy.Capture.transfer_of_losesNoBehaviourAtInputs_nonvacuous` | Quot.sound, propext | `a0d65965c20c782d496a6b5f0e100c4093d4ca88c0bbdf36413fc8b95be53534` | `828a3a4674b72fd0380ad2eaf01734760843efd7700f98558ba8ccb5cc760c88` (209) |
| `Toy.Capture.transfer_relative_to_erasingSet` | propext | `bd989d479e5840fbf13555d34dbcd43af2d825d282577b428436228fdc8e884b` | `11ed4fc113b42314c02383494a5813f61c8df6485305e470ee79113e0a74b510` (19) |
| `Toy.Capture.transfer_relative_to_erasingSet_nonvacuous` | Quot.sound, propext | `32dcfc0d371c51a76861106e39332ee552f057883b1cb44694d281e6ede0030c` | `cc8955b158eb12d77aac3f9184348ddf660f8c8af408dc3224b4e390de511e6e` (213) |
| `Toy.Capture.transfer_single_pass` | none | `c557605ad619420ef9e07fca665b758c6fe608d46ba86a6ff7f7c5307afc15b3` | `49c10e5f62df03a2811d52ef6e6371a2aa8df8c3756437844ad9068424eeeebc` (15) |
| `Toy.Capture.transfer_single_pass_nonvacuous` | Quot.sound, propext | `ae8663efe048a85935e250a99a82f9ca22f30ed8eca4473e6171c1906f964b7c` | `c191f4d30f4cdb4a03f7a5056291cabf953ed392c58f1ffc9275feb360a456b3` (203) |
| `Toy.Capture.transfer_to_capture_input` | none | `d5b40f4d24089b5e37696b8ba337f22b3e562260707cc6f8544cd280ff8a4047` | `6d943f913f96cdcd085ee757799555c575ac5dc81928921f3162a4b5c06ac58f` (5) |
| `Toy.Capture.transfer_to_capture_input_nonvacuous` | Quot.sound, propext | `ee058ee1b673d96caf5a487199cf71bfc3a0a4d2a75375ed968f029dd8cbb443` | `9999ea6cdd4c54faaea89690ffdf486edd12e4c856ba4b5171e061637ba62704` (187) |
| `Toy.Capture.trustAll` | none | `626bc3b81d547ce3e10fa63c1ed9732193c866b35984f096b46df1bd824dd756` | `0ae25ef86d63528db6a473f9fe54111b02fd69a6bfca745652774545d629631d` (39) |
| `Toy.Capture.ubFree` | none | `f1dc3b010f6cd0167752b6254d612b67f13f00439b0a8c7000e696fc5b484509` | `5599e05acd2754e7ad3c54f4c8de178f4d5c901cc6d7bdc704f55c24e8f8fef4` (14) |
| `Toy.Capture.verdict_on_merged_capture_holds_for_both` | none | `516bf1c68b93bbc35899bd5a293825a266a8cbff8fb9e688113f0651b822c200` | `b41272a75e122a4ccc22daa9b2510ec8b381a504178402bd17d6c5b3ee15ab12` (3) |
| `Toy.Capture.verifierSound_example_neg` | propext | `42fa24ffeebb57896e8b54a3c6648373ac7ea558fa83548048f0e276351c4527` | `e6cc53a94faf652ef45b40147bba67d67f9000b347a6254e793e6262a6a6dce0` (99) |
| `Toy.Capture.verifierSound_example_pos` | propext | `dc0607233fb998cf02f9733ad8a43b129b7984c99417265f9a2fd48523a52f49` | `4fbc9f590e6076e7667299a7966f47915cf9180f60c13ecfed2c8584837c3a62` (99) |

**Primary sources.**

- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4; §2.1 read in arXiv:0902.2137 (Definitions 1–7 and the remarks cited in the cards; §2.1 has no numbered propositions).
- A. Pnueli, M. Siegel, E. Singerman, "Translation Validation", TACAS 1998, LNCS 1384, pp. 151–166, doi:10.1007/BFb0054170 (publisher's abstract).
- S. Blazy, Z. Dargaye, X. Leroy, "Formal Verification of a C Compiler Front-End", FM 2006, LNCS 4085, pp. 460–475, doi:10.1007/11813040_31 (publisher's abstract).
- CompCert, github.com/AbsInt/CompCert at 2685140bf72c959446981fb99b5e44a8975021bc: `common/Smallstep.v` L1863–1866 (`forward_to_backward_simulation`), `common/Behaviors.v` L493–496 (`backward_simulation_behavior_improves`).
- rust-lang/rust f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1 (documentation and source quoted for the `derived (modeling bridge)` discussion): `compiler/rustc_mir_transform/src/lib.rs` L513, L562, L569–599 (L594, L596–598), L649–663; `compiler/rustc_mir_transform/src/remove_place_mention.rs` L1, L10–12; `compiler/rustc_session/src/options.rs` L2469–2471; `compiler/rustc_mir_transform/src/simplify.rs` L128–130, L305, L307–309; `compiler/rustc_middle/src/mir/syntax.rs` L65, L138–140, L666–671, L673–676, L758–760, L1046–1055; `compiler/rustc_middle/src/mir/mod.rs` L1337–1341. Each quoted range was re-read at this revision on 2026-11-21.
- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe (documentation quoted for the `derived (modeling bridge)` discussion): `compiler/rustc_session/src/options.rs` L2654–2656 and `compiler/rustc_mir_transform/src/simplify.rs` L307 and L309–311 (the same text as at the revision above).
- Related corpus packages, cited by name, card identifiers and Lean names checked in each package's `results.json` on branch `reference` of the GitHub repository `google/zerocopy` at 4b379cbb55a9c944533423ec4d6f82cfd758728b: `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`, `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets`, `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations`, `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches`.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`.

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It runs `lake build`; scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; runs an inline Lean audit program that computes the axioms of every library declaration with `collectAxioms` and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`; and recomputes, for every name referenced by `results.json` or recorded in `audit/statements.json`, the statement hash and the closure hash described under `## Evidence`, comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff every check passes.

Manual axiom audit of the main results (from the package directory):

```sh
cd lean
lake build
cat > /tmp/capture_axioms.lean <<'EOF'
import Toy
#print axioms Toy.Capture.transfer_to_capture_input
#print axioms Toy.Capture.transfer_of_losesNoBehaviourAtInputs
#print axioms Toy.Capture.transfer_relative_to_erasingSet
#print axioms Toy.Capture.cex_erasingSet_placeMention
#print axioms Toy.Capture.cex_erasingSet_zstRead
#print axioms Toy.Capture.cex_erasingSet_trivialSwitch
#print axioms Toy.Capture.cex_hcap_default
#print axioms Toy.Capture.cex_hcap_stringify_noop
#print axioms Toy.Capture.cex_hcap_swallow
#print axioms Toy.Capture.cleanupMark_merged_pair
#print axioms Toy.Capture.terminateReason_merged_pair
#print axioms Toy.Capture.cex_hcap_noCleanup
#print axioms Toy.Capture.cex_hcap_noReason
#print axioms Toy.Capture.no_semV_faithful_at_merged_pair
#print axioms Toy.Capture.not_faithfulOnOk_of_merged_pair
#print axioms Toy.Capture.exists_faithful_semV_iff_merges_only_equivalent
#print axioms Toy.Capture.clearReplace_denEquiv
#print axioms Toy.Capture.transferSound_all_sound_verifiers_iff_overApproxOnOk
#print axioms Toy.Capture.transferSound_exactVerifier_iff_overApproxOnOk
#print axioms Toy.Capture.failClosed_overApproxOnOk_iff
#print axioms Toy.Capture.failOpen_overApproxOnOk_iff
#print axioms Toy.Capture.partialExtend_overApproxOnOk_iff
#print axioms Toy.Capture.faithfulOnOk_iff_overApproxOnOk_of_total_of_det
#print axioms Toy.Capture.capFC_faithfulOnOk
#print axioms Toy.Capture.capFC_runV_eq_runS
#print axioms Toy.Capture.capStringify_overApproxOnOk_havoc
#print axioms Toy.Capture.capStringify_havoc_not_faithful
#print axioms Toy.Capture.overApproxOnOk_example_neg
#print axioms Toy.Capture.flagContractSound_iff_neverOmits
#print axioms Toy.Capture.flagContractSound_of_neverOmits
#print axioms Toy.Capture.neverOmits_of_flagContractSound
#print axioms Toy.Capture.flagContractSound_iff_omitted_hold_in_admitted_contexts
#print axioms Toy.Capture.checkedRun_contractSound
#print axioms Toy.Capture.checkedRun_eq_run_of_holds
#print axioms Toy.Capture.exemptingSrcAudit_strictlyWeaker_than_irAudit
#print axioms Toy.Capture.srcAudit_of_irAudit
#print axioms Toy.Capture.srcAudit_misses_external_unsafe
EOF
lake env lean /tmp/capture_axioms.lean
```

Each `#print axioms` output must name no axiom other than `propext`, `Classical.choice` and `Quot.sound` (or report that the declaration depends on no axioms).

Narrower checks after a change: a change to the type or value of a package definition changes the closure hash of every recorded name whose closure reaches that definition, and `support/revalidate.py` reports those names. The `derived (modeling bridge)` discussion is revalidated by re-reading the rust-lang/rust line ranges listed under `## Evidence` at the new revision; a passing Lean check says nothing about the bridge.
