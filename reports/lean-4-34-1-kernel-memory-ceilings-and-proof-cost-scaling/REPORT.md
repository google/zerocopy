# Lean 4.34.1 Kernel Memory Ceilings, Eliminator Overhead, LCNF String Hoisting, and Proof-Cost Scaling

## Summary

Empirical measurement of `leanprover/lean4:v4.34.1` across 68 verification and
parser modules under deterministic single-threaded flags (`lean -j1 -M768` and
`lean -j1 -M2048`) identifies four distinct mechanisms that govern Lean 4
kernel memory consumption, LCNF compilation stability, and proof-checking cost:

1. **Base `.olean` Import Footprint and Per-`inductive` Eliminator Synthesis Overhead:**
   On Linux `x86_64` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`),
   importing `Std` (or a base module that transitively imports `Std`) consumes
   `~785–800 MB` of resident set size (RSS), compared to `~680–695 MB` on
   `aarch64-apple-darwin` (`commit d8ef7fd2d72efbe2ee2cefd1b62bf8ab2ff3f205`)
   and `~510–545 MB` for prelude-only (`Init`) modules. Against a `-M768`
   (`768 MiB`) kernel allocator ceiling, each `inductive` or `structure`
   declaration synthesizes 6–15 auxiliary constants (`.casesOn`, `.recOn`,
   `.noConfusion`, `.noConfusionType`, `.below`, `.brecOn`, `.ctorIdx`,
   `.ctorElim`), adding `~12–25 MB` of kernel heap pressure; when the `-M768`
   ceiling trips mid-declaration, the LCNF compiler panics at
   `Lean.Compiler.LCNF.ExplicitBoxing:301:45` (`unreachable code has been reached`).
   Replacing enumeration `inductive` types and `structure` records with
   `abbrev ... := Nat` and nested `×` tuples + `noncomputable def` +
   `set_option Elab.async false` eliminates eliminator synthesis and LCNF code
   generation, allowing modules to pass within `-M768`.
2. **LCNF String Literal Hoisting vs. Compact Wire-Format Byte/Word Parsers:**
   Embedding a `10,366`-byte source string literal and running `String.Slice` /
   `List Char` operations in kernel WHNF ([`support/EndCallSourceShape.lean.txt`](support/EndCallSourceShape.lean.txt))
   triggers `(kernel) excessive memory consumption detected` after `2.186s` at
   `894.6 MB` RSS, followed by an IR join-point failure (`unknown join point 'block_0'`)
   in `._closed_2`. By contrast, compact integer-word wire parsers
   ([`support/MirWireParser.lean`](support/MirWireParser.lean), `0.625s`) and
   prelude-only `.amir` v3 binary byte-list parsers using `UInt8`, `bif`, and
   `LawfulBEq` ([`support/SubstantiveMirByteParser.lean`](support/SubstantiveMirByteParser.lean),
   `7.937s`, `799.8 MB` RSS, 639 lines) check cleanly under `-j1 -M768`.
3. **Compositional Continuation Reuse vs. Step-Horizon Invariant Proof Scaling:**
   - **Call-site repetition (`ProofCost*`, 12 modules):** When a base 3-step
     safety theorem is already cached (`ProofCostContinuationBase`), repeating
     the call 1, 4, or 16 times (`ProofCost*Client{One,Four,Sixteen}`) is flat
     (`~0.336–0.360s`) for both continuation and global-invariant styles;
     however, extending a global 9-phase `Inv` inductive to a second live
     buffer (`ProofCostInvariantExtension`, `12,916` B) requires re-proving all
     9 phase cases from scratch, whereas `ProofCostContinuation` (`7,452` B)
     composes the existing base continuation theorem with a per-ID frame rule.
   - **Program-horizon scaling (`ProgramCost*`, 8 modules + failed 128-call invariant):**
     Across straight-line programs of $N \in \{8, 32, 128\}$ memory operations,
     the continuation route (`ProgramCostContinuation{8,32,128}`) grows from
     `11,497` B (`0.600s`, `806.3 MB` RSS) at $N=8$ to `19,799` B (`0.703s`,
     `814.4 MB` RSS) at $N=128$. By contrast, the monolithic phase-invariant
     route (`ProgramCostInvariant{8,32,128}`) grows from `11,663` B (`0.624s`)
     at $N=8$ to `32,152` B (`1.131s`, `844.5 MB` RSS) at $N=32$, and its
     128-phase inductive (`ProgramCostInvariant128-initial.lean.txt`, `97,876` B,
     130 constructors) fails `-M768` at `1.311s` (`839.4 MB` RSS, 74 kernel
     excessive-memory errors).
   - **Tuple-projection and `Eq.ndrec` rewrite-motive blowup:** Deep
     right-associated tuple projections (`.2.2.2.2.2.2.2.2.2` over a 10-tuple
     in [`support/ServiceIntervals-initial.lean.txt`](support/ServiceIntervals-initial.lean.txt))
     and chained `rw` steps over a 9-field unfolded tuple (~66 `Eq.ndrec`
     motive copies in [`support/ClaimChangeReport-initial.lean.txt`](support/ClaimChangeReport-initial.lean.txt))
     both breach `-M768` (`820.9 MB` and `807.3 MB` RSS), whereas factoring
     single-step helper lemmas ([`support/ClaimChangeResolution.lean`](support/ClaimChangeResolution.lean))
     checks in `0.636s` under `-M768`.
4. **Ground `decide` vs. Factored Equality Reflection vs. Symbolic `∀ base : Nat` WHNF Reduction:**
   - Proving a 618-byte `List UInt8` / hex-string equality by kernel `decide`
     ([`support/CargoLeanCostCold2BindingGround.lean`](support/CargoLeanCostCold2BindingGround.lean))
     takes `10.148s` and `1,952.0 MB` RSS on Linux `x86_64` (`5.544s` and
     `1,811.4 MiB` on `aarch64-apple-darwin`), whereas proving the identical
     theorem via `(beq_iff_eq _ _).mpr rfl`
     ([`support/CargoLeanCostCold2Binding.lean`](support/CargoLeanCostCold2Binding.lean))
     takes `0.421s` and `548.4 MB` RSS (**24.1x faster** and **1,403.6 MB lower
     RSS**). A monolithic `decide` over the full `cold2` acceptance predicate
     ([`support/CargoLeanCostCold2Monolithic.lean`](support/CargoLeanCostCold2Monolithic.lean))
     exceeds even `-M2048` on Linux `x86_64` (`11.585s`, `2,099.7 MB` RSS),
     whereas the 11-module factored composition (`CargoLeanCostCold2Composed`)
     checks in `4.896s` at `1,000.4 MB` RSS.
   - For concrete ground execution of `.amir` v3 multi-function call trees
     ([`support/StatefulGenericLibraryH3H7Core.lean`](support/StatefulGenericLibraryH3H7Core.lean)),
     `by decide` checks in `< 0.5s`; however, symbolic universal proofs
     (`∀ base : Nat`) over a 12-frame `evalSteps 60` loop force the kernel to
     unfold the full state machine over symbolic terms `base + 1`, hitting the
     `200,000`-heartbeat / `1,024-MiB` limit unless each symbolic step is
     discharged via a modular single-step transition lemma
     (`evalStepGenericSlot_true_universal`).

## Applicability

These findings apply to:

- **`leanprover/lean4`:** Version `4.34.1`:
  - Linux `x86_64` release (`x86_64-unknown-linux-gnu`, commit
    `5045d0056413266e57c625dcd7c365b10e377c52`)
  - macOS `arm64` release (`aarch64-apple-darwin`, commit
    `d8ef7fd2d72efbe2ee2cefd1b62bf8ab2ff3f205`)
- **Invocation Regimes:** Single-threaded command-line invocations
  `lean -j1 -M768` (768 MiB internal kernel memory cap) and `lean -j1 -M2048`
  (2,048 MiB internal kernel memory cap).

## Findings

### 1. Base `.olean` Import RSS and Per-`inductive` Eliminator Synthesis Overhead

- **Basis:** `execution` and `derived`
  ([`support/r12_m768_replay.json`](support/r12_m768_replay.json),
  [`support/r12_m2048_replay.json`](support/r12_m2048_replay.json),
  [`support/SpecValidationControls-initial.lean.txt`](support/SpecValidationControls-initial.lean.txt),
  [`support/SpecValidation.lean`](support/SpecValidation.lean), and
  [`support/SpecChallengeResolution.lean`](support/SpecChallengeResolution.lean)).

1. **Platform Baseline RSS (`import Std` vs. `Init`-only):**
   - Modules that omit `import Std` and rely only on `Init` (such as
     `Post96LifecycleInterface.lean` or `CargoLeanCostCold2Data.lean`) run at
     `521–566 MB` RSS on Linux `x86_64` (`395–438 MiB` on `aarch64-apple-darwin`).
   - Modules that import `Std` (directly or via `Execution.lean`) start at
     `~785–800 MB` process RSS on Linux `x86_64` (`~680–708 MB` on
     `aarch64-apple-darwin`), leaving minimal kernel allocator headroom under
     `-M768`.
2. **Per-`inductive` Eliminator Cascade and LCNF Explicit-Boxing Panic:**
   Each `inductive` or `structure` declaration triggers synthesis of `.casesOn`,
   `.recOn`, `.noConfusion`, `.noConfusionType`, `.below`, `.brecOn`, `.ctorIdx`,
   and `.ctorElim` (plus `DecidableEq` / `Repr` instances when derived),
   consuming `~12–25 MB` of kernel heap per declaration. When the `-M768`
   internal memory limit is exceeded during `inductive` elaboration:
   - The kernel rejects the declaration with `error: (kernel) excessive memory consumption detected`.
   - Downstream `noConfusion` and `sizeOf_spec` theorems fail with cascading
     type mismatches because `.ctorElim` was never registered in the kernel.
   - The LCNF compiler then panics in
     `Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType`
     (`Lean.Compiler.LCNF.ExplicitBoxing:301:45: unreachable code has been reached`).
3. **Controlled Before/After Comparison (`SpecValidationControls-initial.lean.txt` vs. `SpecChallengeResolution.lean`):**

| Specimen | Type & Proof Representation | `-j1 -M768` Outcome (Linux `x86_64`) | Wall Time | Peak RSS |
|---|---|---|---|---|
| [`support/SpecValidationControls-initial.lean.txt`](support/SpecValidationControls-initial.lean.txt) | `inductive ChallengeStatus \| validated \| rejectedWeak ... deriving DecidableEq` + computable defs | **Fails** (`(kernel) excessive memory consumption detected` at line 58 + 5 cascading errors) | `0.819s` | `808.7 MB` |
| [`support/SpecChallengeResolution.lean`](support/SpecChallengeResolution.lean) | `abbrev ChallengeStatus : Type := Nat` + `noncomputable def` + `set_option Elab.async false` | **Passes** (all 8 theorems verified, `#print axioms` clean) | `0.557s` | `799.8 MB` |
| [`support/SpecValidation.lean`](support/SpecValidation.lean) | Zero-`inductive` `abbrev` + `noncomputable def` + `set_option Elab.async false` | **Passes** (all 8 theorems verified) | `0.558s` | `799.8 MB` |

### 2. LCNF String Literal Hoisting vs. Binary Wire-Format Byte/Word Parsers

- **Basis:** `execution` and `source`
  ([`support/EndCallSourceShape.lean.txt`](support/EndCallSourceShape.lean.txt),
  [`support/MirWireParser.lean`](support/MirWireParser.lean),
  [`support/SubstantiveMirByteParser.lean`](support/SubstantiveMirByteParser.lean),
  and [`support/r12_m768_replay.json`](support/r12_m768_replay.json)).

1. **Failure of Embedded Source String Parsing (`EndCallSourceShape.lean.txt`):**
   In [`support/EndCallSourceShape.lean.txt`](support/EndCallSourceShape.lean.txt)
   (`15,280` bytes), embedding a `10,366`-byte Markdown file (`memoryMd`) and two
   extracted slices (`165` B and `279` B) as Lean `String` literals and proving
   `extractEndCall memoryMd = some (actualBasic, actualTree)` by `rfl` / `decide`
   fails under `lean -j1 -M768` after `2.186s` (`894,582,784` B RSS):
   - LCNF closed-term hoisting (`extractEndCall._closed_2`) fails with
     `compiler IR check failed at extractEndCall._closed_2. Error: unknown join point 'block_0'`
     followed by the `ExplicitBoxing:301:45` panic.
   - Kernel WHNF reduction of `String.Slice` / `List Char` over the 10-KB literal
     allocates thousands of transient `Char` cons cells, exhausting `-M768`.
2. **Compact Wire-Format `Nat` and `UInt8` Parsers Under `-j1 -M768`:**
   - [`support/MirWireParser.lean`](support/MirWireParser.lean) (`13,448` B):
     Replaces raw string scanning with a 6-word `List Nat` packet format
     (`encodePacket` / `parsePacket`), proving round-trip completeness, parser
     soundness, injectivity, and `NoUB` transfer in `0.625s` under `-j1 -M768`.
   - [`support/SubstantiveMirByteParser.lean`](support/SubstantiveMirByteParser.lean)
     (`27,631` B, 639 lines, prelude-only without `import Std`): Mechanizes a
     complete fail-closed `.amir` v3 (`AMIR\x03`) binary byte-stream parser
     (`parseWirePackage : List UInt8 → Option WirePackage`) and specification
     encoder (`specEncodePackage`) using `bif` (Boolean conditional) and
     `LawfulBEq` lemmas (`universal_accepted_byte_soundness` and
     `universal_accepted_package_canonical_unique`), checking 7 real compiled
     Rust MIR byte packages by kernel `rfl` in `7.937s` under `-j1 -M768`.

### 3. Compositional Continuation Reuse vs. Step-Horizon Invariant Proof Scaling

- **Basis:** `execution` and `derived`
  ([`support/r12_m2048_replay.json`](support/r12_m2048_replay.json),
  [`support/ProofCostCommon.lean`](support/ProofCostCommon.lean)–[`support/ProofCostInvariantClientSixteen.lean`](support/ProofCostInvariantClientSixteen.lean),
  [`support/ProgramCostCommon.lean`](support/ProgramCostCommon.lean)–[`support/ProgramCostContinuation128.lean`](support/ProgramCostContinuation128.lean),
  [`support/ProgramCostInvariant128-initial.lean.txt`](support/ProgramCostInvariant128-initial.lean.txt),
  [`support/ServiceIntervals-initial.lean.txt`](support/ServiceIntervals-initial.lean.txt),
  [`support/ClaimChangeReport-initial.lean.txt`](support/ClaimChangeReport-initial.lean.txt),
  and [`support/ClaimChangeResolution.lean`](support/ClaimChangeResolution.lean)).

#### 3.1 Call-Site Repetition vs. Feature Extension (`ProofCost*`, 12 Modules)

In the 12-module `ProofCost*` suite, a base 3-operation memory cycle (`allocate`,
`store`, `deallocate`) and an extended two-live-buffer cycle (`allocate` buffer 1,
`allocate` buffer 2, `store` buffer 1, `store` buffer 2, `deallocate` both) are
proved via (A) compositional continuation lemmas (`ProofCostContinuation*`) and
(B) a monolithic 9-phase operational invariant (`ProofCostInvariant*`):

| Module | Source Bytes | `.olean` Bytes | Fresh Linux `-M2048` Wall (s) | Fresh Linux Max RSS (KB) | Historical Darwin `-M768` Wall (s) |
|---|---:|---:|---:|---:|---:|
| [`support/ProofCostCommon.lean`](support/ProofCostCommon.lean) | 17,135 | 175,880 | `1.106` | `814,632` | `0.629` |
| [`support/ProofCostFrames.lean`](support/ProofCostFrames.lean) | 8,275 | 94,008 | `0.917` | `804,256` | `0.483` |
| [`support/ProofCostContinuationBase.lean`](support/ProofCostContinuationBase.lean) | 920 | 32,768 | `0.345` | `785,292` | `0.214` |
| [`support/ProofCostContinuation.lean`](support/ProofCostContinuation.lean) | 7,452 | 66,464 | `0.553` | `798,352` | `0.341` |
| [`support/ProofCostContinuationClientOne.lean`](support/ProofCostContinuationClientOne.lean) | 791 | 29,648 | `0.336` | `786,660` | `0.223` |
| [`support/ProofCostContinuationClientFour.lean`](support/ProofCostContinuationClientFour.lean) | 797 | 29,672 | `0.360` | `785,800` | `0.213` |
| [`support/ProofCostContinuationClientSixteen.lean`](support/ProofCostContinuationClientSixteen.lean) | 815 | 29,720 | `0.350` | `786,656` | `0.215` |
| [`support/ProofCostInvariant.lean`](support/ProofCostInvariant.lean) | 6,600 | 91,008 | `0.531` | `800,664` | `0.331` |
| [`support/ProofCostInvariantExtension.lean`](support/ProofCostInvariantExtension.lean) | 12,916 | 140,864 | `0.654` | `809,524` | `0.399` |
| [`support/ProofCostInvariantClientOne.lean`](support/ProofCostInvariantClientOne.lean) | 783 | 29,480 | `0.356` | `786,756` | `0.215` |
| [`support/ProofCostInvariantClientFour.lean`](support/ProofCostInvariantClientFour.lean) | 789 | 29,504 | `0.350` | `786,752` | `0.217` |
| [`support/ProofCostInvariantClientSixteen.lean`](support/ProofCostInvariantClientSixteen.lean) | 807 | 29,552 | `0.336` | `786,752` | `0.217` |

Key observation: once a loop/repetition combinator is proved, instantiating it
at $k \in \{1, 4, 16\}$ iterations (`ClientOne`, `ClientFour`, `ClientSixteen`)
is $O(1)$ (`~0.336–0.360s`). However, extending the program body from 1 buffer
to 2 buffers (`ProofCostInvariantExtension` vs. `ProofCostContinuation`) forces
the invariant route to define a new 9-constructor `Inv` inductive (`12,916` B,
`140,864` B `.olean`) with zero theorem reuse from `ProofCostInvariant`, whereas
`ProofCostContinuation` (`7,452` B, `66,464` B `.olean`) reuses the per-operation
continuation rules.

#### 3.2 Straight-Line Program Horizon Scaling ($N \in \{8, 32, 128\}$, `ProgramCost*`)

When $N$ distinct sequential memory operations are verified without loop
compression (`ProgramCost*`), the continuation route scales linearly with minimal
constant factor while the monolithic `Phase` inductive invariant route hits the
`-M768` ceiling at $N = 128$:

| Module | Horizon $N$ | Source Bytes | `.olean` Bytes | Fresh Linux `-M2048` Wall (s) | Fresh Linux Max RSS (KB) | Historical Darwin `-M768` Wall (s) / RSS |
|---|---:|---:|---:|---:|---:|---|
| [`support/ProgramCostCommon.lean`](support/ProgramCostCommon.lean) | shared | 39,602 | 645,448 | `1.250` | `825,548` | `0.733s` / `719.2 MB` |
| [`support/ProgramCostPrimitives.lean`](support/ProgramCostPrimitives.lean) | shared | 15,320 | 147,552 | `0.940` | `812,020` | `0.583s` / `712.7 MB` |
| [`support/ProgramCostSmallControls.lean`](support/ProgramCostSmallControls.lean) | $N=8$ controls | 13,223 | 173,272 | `0.908` | `808,228` | `0.580s` / `707.0 MB` |
| [`support/ProgramCostContinuation8.lean`](support/ProgramCostContinuation8.lean) | $N=8$ | 11,497 | 80,680 | `0.600` | `806,340` | `0.382s` / `703.7 MB` |
| [`support/ProgramCostInvariant8.lean`](support/ProgramCostInvariant8.lean) | $N=8$ | 11,663 | 136,416 | `0.624` | `812,932` | `0.422s` / `710.1 MB` |
| [`support/ProgramCostContinuation32.lean`](support/ProgramCostContinuation32.lean) | $N=32$ | 15,769 | 127,480 | `0.646` | `806,880` | `0.431s` / `706.5 MB` |
| [`support/ProgramCostInvariant32.lean`](support/ProgramCostInvariant32.lean) | $N=32$ | 32,152 | 418,752 | `1.131` | `844,512` | `0.708s` / `739.1 MB` |
| [`support/ProgramCostContinuation128.lean`](support/ProgramCostContinuation128.lean) | $N=128$ | 19,799 | 206,536 | `0.703` | `814,444` | `0.488s` / `707.2 MB` |
| [`support/ProgramCostInvariant128-initial.lean.txt`](support/ProgramCostInvariant128-initial.lean.txt) | $N=128$ | 97,876 | *failed* | *quarantined* | *quarantined* | **Fails `-M768`** at `1.311s` / `839.4 MB` (74 kernel excessive-memory errors) |

At $N = 32$, `ProgramCostInvariant32` already produces a `3.28x` larger `.olean`
(`418,752` B vs. `127,480` B) and consumes `+37.6 MB` more RSS than
`ProgramCostContinuation32`. At $N = 128$, `ProgramCostInvariant128-initial`
declares a 130-constructor `Phase` inductive whose eliminator + 130-way case
split exceeds `-M768`, while `ProgramCostContinuation128` adds only `+0.057s`
and `+7.6 MB` RSS over $N = 32$.

#### 3.3 Deep Tuple Projections and `Eq.ndrec` Rewrite-Motive Duplication

Even when `inductive` declarations are avoided, two proof-term shapes cause
superlinear kernel memory growth under `-M768`:

- **Right-associated product projection chains (`ServiceIntervals-initial.lean.txt`):**
  Representing a 10-field machine state as a right-associated product
  `Nat × Nat × ... × Nat` and unfolding 9-deep projections `.2.2.2.2.2.2.2.2.2`
  across 18 theorems ([`support/ServiceIntervals-initial.lean.txt`](support/ServiceIntervals-initial.lean.txt))
  fails `-M768` at `1.876s` (`820.9 MB` RSS), because each nested `Prod.snd`
  carries both components' types as implicit arguments (`O(k^2)` term size for
  tuple depth $k$).
- **Chained `rw` (`Eq.ndrec`) over large unfolded tuples (`ClaimChangeReport-initial.lean.txt` vs. `ClaimChangeResolution.lean`):**
  In [`support/ClaimChangeReport-initial.lean.txt`](support/ClaimChangeReport-initial.lean.txt),
  a `repeat first | rw [...]` loop executing ~66 rewrites over a 9-field
  unfolded report expression constructs 66 nested `Eq.ndrec` applications, each
  embedding a full copy of the 9-field motive (`1.304s`, `807.3 MB` RSS, kernel
  excessive memory failure). Factoring the proof into per-field congruence
  lemmas ([`support/ClaimChangeResolution.lean`](support/ClaimChangeResolution.lean))
  reduces checking time to `0.636s` under `-j1 -M768`.

### 4. Ground `decide` vs. Factored Equality Reflection vs. Symbolic `∀ base : Nat` Reduction

- **Basis:** `execution` and `source`
  ([`support/CargoLeanCostCold2Data.lean`](support/CargoLeanCostCold2Data.lean),
  [`support/CargoLeanCostCold2Binding.lean`](support/CargoLeanCostCold2Binding.lean),
  [`support/CargoLeanCostCold2BindingGround.lean`](support/CargoLeanCostCold2BindingGround.lean),
  [`support/CargoLeanCostCold2Monolithic.lean`](support/CargoLeanCostCold2Monolithic.lean),
  [`support/Post96LifecycleGenerated.lean.failed.txt`](support/Post96LifecycleGenerated.lean.failed.txt),
  [`support/StatefulGenericLibraryH3H7Core.lean`](support/StatefulGenericLibraryH3H7Core.lean),
  and [`support/r12_m2048_replay.json`](support/r12_m2048_replay.json)).

1. **`by decide` vs. `(beq_iff_eq _ _).mpr rfl` on 618-Byte `.amir` Package Payloads (`CargoLeanCostCold2*`):**
   In `Post96LifecycleGenerated.lean.failed.txt` (`54,284` B), placing three
   `~618`-byte `.amir` v3 `List UInt8` literals and 16 `by decide` theorems in a
   single module failed `-M768` after `13.480s` (`805.7 MB` RSS). Isolating the
   exact `cold2` specimen in the `CargoLeanCostCold2*` benchmark suite reveals
   the root cause:

| Module | Proof Strategy | Fresh Linux `-M2048` Wall (s) | Fresh Linux Max RSS (KB) | Historical Darwin `-M2048` Wall (s) / RSS |
|---|---|---:|---:|---|
| [`support/CargoLeanCostCold2Data.lean`](support/CargoLeanCostCold2Data.lean) | Data definitions only (`14,888` B) | `0.567` | `543,504` | `0.369s` / `430.5 MiB` |
| [`support/CargoLeanCostCold2Binding.lean`](support/CargoLeanCostCold2Binding.lean) | Factored `(beq_iff_eq _ _).mpr rfl` on `cold2BindingCheck` | **`0.421`** | **`548,436`** | **`0.327s` / `435.0 MiB`** |
| [`support/CargoLeanCostCold2BindingGround.lean`](support/CargoLeanCostCold2BindingGround.lean) | Ground `by decide` on the **exact same** `cold2BindingCheck` proposition | **`10.148`** | **`1,951,988`** | **`5.544s` / `1,811.4 MiB`** |
| `CargoLeanCostCold2Composed` | 11-module factored composition of full `cold2` acceptance | `4.896` | `1,000,360` | `2.659s` / `872.0 MiB` |
| [`support/CargoLeanCostCold2Monolithic.lean`](support/CargoLeanCostCold2Monolithic.lean) | Monolithic `by decide` on full `cold2` acceptance | **Fails `-M2048`** (`11.585s`) | **`2,099,692`** | `5.657s` / `1,816.8 MiB` |

   Why does `by decide` allocate `+1.4 GB` more kernel heap than
   `(beq_iff_eq _ _).mpr rfl` on the same check? `by decide` synthesizes a
   nested `instDecidableAnd` / `instDecidableEqString` / `instDecidableEqList`
   typeclass decision tree over the 64-character SHA-256 strings and 618-element
   `List UInt8` literals, and the kernel must reduce both the `Decidable`
   instance term and its proof witness. By contrast, defining the check as a
   Boolean function `cold2BindingCheck : Bool` and applying
   `(beq_iff_eq _ _).mpr rfl` reduces the Boolean expression directly via fast
   kernel `BEq` WHNF evaluation (`rfl`) without constructing a `Decidable`
   proof tree.

2. **Concrete Ground `decide` vs. Symbolic `∀ base : Nat` WHNF Unfolding (`StatefulGenericLibraryH3H7Core.lean`):**
   In [`support/StatefulGenericLibraryH3H7Core.lean`](support/StatefulGenericLibraryH3H7Core.lean)
   (checked in `22.992s` and `749,344 KB` RSS in
   [`support/r12_m2048_replay.json`](support/r12_m2048_replay.json)):
   - Ground execution theorems over a 3-crate `.amir` v3 call tree (5 functions,
     12 call frames, `evalSteps 60`) with concrete inputs check in `< 0.5s` by
     `decide` (`h3_ground_execution_exact`).
   - However, when the input parameter is universally quantified
     (`∀ base : Nat`), attempting to unfold `evalSteps 60` in a single proof
     forces the kernel's WHNF reducer to symbolically evaluate `Nat.beq`,
     `List.get?`, and `Option.bind` across 60 steps where register values contain
     stuck symbolic terms (`base + 1`, `base + 3`), exceeding `200,000`
     heartbeats and `1,024 MiB` RSS.
   - Factoring the symbolic proof into per-step transition lemmas
     (`evalStepGenericSlot_true_universal`, lines 629–735 of
     [`support/StatefulGenericLibraryH3H7Core.lean`](support/StatefulGenericLibraryH3H7Core.lean))
     bounds each kernel reduction to a single instruction step (`maxHeartbeats 400000`),
     allowing the full 5-function symbolic composition to check within `749.3 MB`
     RSS.

## Boundaries

- **Not examined:**
  - Multi-threaded elaboration (`-j > 1`), where concurrent tactic tasks share
    the `-M` process memory limit and introduce non-deterministic peak RSS.
  - Mathlib4-scale `.olean` import graphs (several gigabytes of `.olean` mmap/heap
    data), which require `-M4096` or higher regardless of local proof style.
- **Unknown:**
  - Whether future Lean 4 releases will replace the `ExplicitBoxing:301:45`
    panic after a kernel memory-limit error with a graceful compiler bailout.
- **Known not to apply:**
  - `by decide` over multi-hundred-element `List UInt8` / `String` equality
    conjunctions does **not** fit within `-M768` (`~1.8–1.95 GB` RSS); Boolean
    reflection via `(beq_iff_eq _ _).mpr rfl` or `LawfulBEq` must be used instead.
  - Monolithic phase-invariant `inductive` declarations with $\ge 128$
    constructors (`ProgramCostInvariant128`) do **not** fit within `-M768`.
- **Unsupported:**
  - Unfactored `evalSteps k` unfolding over symbolic `∀ base : Nat` arguments
    for large horizons ($k \ge 60$) is unsupported within standard heartbeat and
    `-M768` limits without per-step transition lemmas.

## Evidence

| File | SHA-256 | Role |
|---|---|---|
| [`support/r12_m768_replay.json`](support/r12_m768_replay.json) | `091d039abbbf9365f6889b87bee67ff19c4167fa34b95480a4ad69357756774d` | Fresh Linux `x86_64` Lean 4.34.1 (`-j1 -M768`) replay ledger for 10 `-M768`-compliant modules (`Execution`, `MirWireParser`, `SubstantiveMirByteParser`, `SpecValidation`, `SpecChallengeResolution`, `ClaimChangeResolution`, `ClaimChangeResolutionControls`) |
| [`support/r12_m2048_replay.json`](support/r12_m2048_replay.json) | `e967cb95eda8121c5d9e4f1c6a2afef6387bc4d531a67112fd2bd54993364401` | Fresh Linux `x86_64` Lean 4.34.1 (`-j1 -M2048`) replay ledger across 60 modules (`ProofCost*`, `ProgramCost*`, `StatefulGenericLibraryH3H7*`, `CargoLeanCostCold2*`) |
| [`support/EndCallSourceShape.lean.txt`](support/EndCallSourceShape.lean.txt) | `618886f7b3c9ba98bfa47ed4d36b09bc8a85b52b7f05ffc255ef4c5f60d202ba` | Quarantined 10-KB embedded string literal specimen failing `-M768` (`2.186s`, `894.6 MB` RSS, LCNF `._closed_2` IR error + `ExplicitBoxing` panic) |
| [`support/MirWireParser.lean`](support/MirWireParser.lean) | `9fa2f09b01ac3cc23297431402fc5b24f8fb3930436755354d4947a93f81c34b` | Compact 6-word `List Nat` wire parser and soundness/injectivity proof (`0.625s` under `-j1 -M768`) |
| [`support/SubstantiveMirByteParser.lean`](support/SubstantiveMirByteParser.lean) | `9e24337cdf324d6f1d41914a6302b8e72560fd0de1f542da43507dc3b71def7a` | Standalone 639-line `.amir` v3 `List UInt8` binary wire parser using `bif` and `LawfulBEq` (`7.937s` under `-j1 -M768`) |
| [`support/SpecValidationControls-initial.lean.txt`](support/SpecValidationControls-initial.lean.txt) | `80327853d135c6d26c84a62a8de1e1ab4e6387b0f5af04f2a757e6adea26be0b` | Quarantined specimen where `inductive ChallengeStatus ... deriving DecidableEq` exceeds `-M768` at `808.7 MB` RSS |
| [`support/SpecChallengeResolution.lean`](support/SpecChallengeResolution.lean) | `bb6c49b749f15b489680f49a70bbca29ae46830b9ad97e3dd3eeb73196d5139a` | Re-engineered zero-`inductive` `abbrev ChallengeStatus : Type := Nat` module passing `-j1 -M768` in `0.557s` |
| [`support/ServiceIntervals-initial.lean.txt`](support/ServiceIntervals-initial.lean.txt) | `08328762e08bfdc8352fcc4b6a7790663949ed9e370d75c7f174866d16bcb9c0` | Quarantined 9-deep right-associated product `.2.2.2...` specimen failing `-M768` at `1.876s` (`820.9 MB` RSS) |
| [`support/ClaimChangeReport-initial.lean.txt`](support/ClaimChangeReport-initial.lean.txt) | `3419c524945178bfa559a71e31218e2295fbed9400f47d33a56efef3211f2f2e` | Quarantined ~66-step `Eq.ndrec` rewrite-motive duplication specimen failing `-M768` at `1.304s` (`807.3 MB` RSS) |
| [`support/ClaimChangeResolution.lean`](support/ClaimChangeResolution.lean) | `b0d63e18438f0f2aa6017d8b19e00e98664536f622af7bf32d9063b2ac80204f` | Factored helper-lemma replacement passing `-j1 -M768` in `0.636s` |
| [`support/ProofCostCommon.lean`](support/ProofCostCommon.lean)–[`support/ProofCostInvariantClientSixteen.lean`](support/ProofCostInvariantClientSixteen.lean) | *(12 files; see table in §3.1 and `r12_m2048_replay.json`)* | 12-module `ProofCost*` call-site repetition and feature-extension suite |
| [`support/ProgramCostCommon.lean`](support/ProgramCostCommon.lean)–[`support/ProgramCostContinuation128.lean`](support/ProgramCostContinuation128.lean) & [`support/ProgramCostInvariant128-initial.lean.txt`](support/ProgramCostInvariant128-initial.lean.txt) | *(9 files; see table in §3.2 and `r12_m2048_replay.json`)* | 8 passing `ProgramCost*` modules ($N \in \{8, 32, 128\}$) plus the quarantined $N=128$ phase-invariant failure specimen |
| [`support/Post96LifecycleGenerated.lean.failed.txt`](support/Post96LifecycleGenerated.lean.failed.txt) | `c88d61017f795633934ec2c733d014899c21cd50887e66ace53d2b0149ad7979` | Quarantined 16-theorem monolithic `decide` `.amir` lifecycle module failing `-M768` at `13.480s` (`805.7 MB` RSS) |
| [`support/CargoLeanCostCold2Data.lean`](support/CargoLeanCostCold2Data.lean), [`support/CargoLeanCostCold2Binding.lean`](support/CargoLeanCostCold2Binding.lean), [`support/CargoLeanCostCold2BindingGround.lean`](support/CargoLeanCostCold2BindingGround.lean), [`support/CargoLeanCostCold2Monolithic.lean`](support/CargoLeanCostCold2Monolithic.lean) | `c106d2a6...`, `1787f155...`, `6e6dbc4c...`, `b2625eda...` | Controlled comparison of `(beq_iff_eq _ _).mpr rfl` (`0.421s`, `548.4 MB`) vs. ground `decide` (`10.148s`, `1,952.0 MB`) vs. monolithic `decide` (`> 2,048 MiB`) |
| [`support/StatefulGenericLibraryH3H7Core.lean`](support/StatefulGenericLibraryH3H7Core.lean) | `ddcd212ee3175dcad9a1a2a927454806039d10429de44ecf4ebe0f402bd341b0` | 3-crate `.amir` v3 ground `decide` (`< 0.5s`) and factored symbolic `∀ base : Nat` step-lemma verification (`22.992s`, `749.3 MB` RSS) |

## Revalidation

To re-validate the standalone prelude-only `.amir` v3 byte-stream parser under
`lean -j1 -M768`:

```bash
lean +leanprover/lean4:v4.34.1 -j1 -M768 \
  reports/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/support/SubstantiveMirByteParser.lean
```

To inspect and verify the preserved `-M768` and `-M2048` empirical timing/RSS
ledgers across all re-validated modules:

```bash
python3 - <<'PY'
import json
from pathlib import Path

pkg = Path("reports/lean-4-34-1-kernel-memory-ceilings-and-proof-cost-scaling/support")
m768 = json.loads((pkg / "r12_m768_replay.json").read_text())
m2048 = json.loads((pkg / "r12_m2048_replay.json").read_text())

assert all(r["exit_code"] == 0 for r in m768["runs"])
by_mod = {m["module"]: m for m in m2048["modules"]}
assert by_mod["AnnealResearch.ProgramCostContinuation128"]["returncode"] == 0
assert by_mod["AnnealResearch.CargoLeanCostCold2Binding"]["wall_seconds"] < 1.0
assert by_mod["AnnealResearch.CargoLeanCostCold2BindingGround"]["wall_seconds"] > 5.0
assert by_mod["AnnealResearch.CargoLeanCostCold2Monolithic"]["returncode"] != 0
print("Verified R12 -M768 (10 modules) and -M2048 (60 modules) replay ledgers.")
PY
```
