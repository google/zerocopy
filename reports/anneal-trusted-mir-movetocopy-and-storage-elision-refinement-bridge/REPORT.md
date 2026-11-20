# Direct Refinement Bridge Over Anneal Trusted MIR Semantics for `MoveToCopy` and `RemoveStorageMarkers`

## Summary

Bridging MIR pre-normalization passes directly onto Anneal's unmodified trusted operational semantics (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` and `Trusted.MirSemantics`)—rather than onto standalone toy IRs or shadow `namespace Trusted` surrogates—exposes a sharp **forward/reverse soundness asymmetry** governed by `deinitMovedPlace = true`, entry-time `hasStorageAnnotation` liveness initialization, and `StorageLive` slot wiping. Prior corpus reports either declared a fake `namespace Trusted` omitting `deinitMovedPlace = true` (refuted in `bidirectional-mir-minissa-refinement-and-anneal-vc-transport`) or mechanized a standalone zero-import model unbridged to Anneal's TCB (`field-granular-deinit-move-mir-to-minissa-bisimulation-and-vc-transport`).

This report documents the **first direct mechanized refinement and verification-condition (VC) transport bridge over unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` `Trusted.MirAst` and `Trusted.MirSemantics`** (`support/AnnealTrustedMirMoveToCopyStorage.lean`, namespace `VrustcFormal.F1_1b`, `6,489` lines, `275,460` bytes, `0` fake `namespace Trusted` declarations, `0` `Anneal.*` references, `0` `sorry`, axioms strictly **`[propext]`**—zero `Classical.choice`, zero `Quot.sound`):

1. **Unconditional Forward Codegen Refinement (`[kernel-checked proof]`):** Rewriting any subset of `Operand.move p ↦ Operand.copy p` (`isMoveToCopyProgram`, `codegen_moveToCopy_refines_unconditional`) or replacing all in-bounds `StorageLive(id)` (`0 ≤ id < locals.length`) and non-return `StorageDead(id)` (`1 ≤ id < locals.length`) statements 1-to-1 with `.nop` while retaining `.storageDead 0` and out-of-bounds markers (`isRemoveStorageMarkersProgram`, `codegen_removeStorageMarkers_refines_unconditional`) unconditionally preserves `WellFormed`, exact finite `Behavior` (`↔`), infinite `Diverges` (`↔`), `SatisfiesPost`, and `BodyVerified` whenever `pSrc` is `WellFormed`.
2. **All-or-Nothing `RemoveStorageMarkers` Forward Boundary (`[kernel-checked proof]`):** Eliding only `StorageLive(id)` while retaining `StorageDead(id)` is **unsound even forward** because `hasStorageAnnotation` stays `true`, initializing `id` to `.dead` so the first write faults `.fault .undefined` (`ce_partial_storageLive_only_elision_unsound`).
3. **Certified Bidirectional VC Transport (`[kernel-checked proof]`):** Uncertified reverse transport (`WellFormed pTgt q → WellFormed pSrc q`) is strictly false for both passes on `Trusted.MirSemantics` (`ce_vc_transport_moveToCopy_unsound_without_cert`, `ce_m4_reversed_move_then_copy_rejected`, `ce_vc_transport_storageDead_unsound_without_cert`, `ce_storageLive_wipes_value_in_TrustedMir`). Pairing either relation with a passing three-state CFG abstract-interpretation certificate (`checkNoUseAfterMoveProgram` / `checkStorageSafeProgram`) upgrades refinement to full **bidirectional operational equivalence (`↔`)** across **all** queries `q : Query`—preserving `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and `BodyVerified` (`vc_transport_moveToCopy_certified_iff`, `vc_transport_removeStorageMarkers_certified_iff`).
4. **Lean `v4.34.1` `._unsafe_rec` / `isPartial` Trap Under `TrustedBoundary.lean` (`[real measurement]`):** Computable recursive `def`s—including **recursive `Prop`-valued `def`s** like `execOutcome`—emit `isPartial = true` `._unsafe_rec` helpers rejected by `TrustedBoundary.validateRepoConstant`. Marking recursive `def`s (and non-`Prop` callers) `noncomputable def` while leaving non-recursive `: Prop` definitions unmarked resolves the rejection cleanly without breaking `rfl` reduction.
5. **Three-Kernel + TCB Audit Verification (`[real measurement]`):** All `19` public user theorems (`232` source decls, `602` kernel constants) pass fresh synchronous Lean `v4.34.1` (`16.101 s` cached / `16.270 s` fresh), unmodified `TrustedBoundary.lean` `"preflight"` (`3.914 s`, negative `sorry` probe rejected `rc = 1`) + Pass 1 `"audit"` (`6.607 s`, `2,183` replayed decls, `axioms = ["propext"]`; standalone `1,926 / 1,926` replay without `Anneal.MirWp` over `51 / 51` locked `foundation-lock.json` modules), fresh Lean `v4.35.0` (`14.713 s`), and `lean4export 3.1.0` + **`nanoda_bin 0.4.19`** (**`1,795` declarations checked with `0` errors in `0.889 s` / `34.29 MB` RSS**; negative probe `permitted_axioms = []` rejected `rc = 1`).

> **Scope Caution:** All theorems target `Trusted.MirSemantics@c131b320e` (deterministic `ValidChoice _ _ c := c = 0`, single-frame, empty `callerMem`, unprojected scalar/unit/never/fieldless-enum fragment where `.call`/`.assert` immediately fault `.unsupported`). They do **not** cover memory, pointers/references, Tree Borrows, projections, calls, `SimplifyCfg` `.nop` deletion, arbitrary `Specs.property`, direct `Anneal.MirWp.wpProg` rewriting, or native binary codegen. See `## Boundaries`.

---

## Applicability

### Subject Relationships and Exact Configuration Scope

This report characterizes `support/AnnealTrustedMirMoveToCopyStorage.lean` (namespace `VrustcFormal.F1_1b`, `6,489` lines, `275,460` bytes, SHA-256 `79d0c63cfe045233d1dcc491529b585981c7afe715bb876f52d314d0a7c91a5c`) directly against unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Supplies unmodified imported TCB semantics (`Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`), the syntactic preflight and `.olean` kernel-replay auditor (`trusted/audit/TrustedBoundary.lean`), the `51`-module `foundation-lock.json` (`schema: 1`), and `Trusted/Correspondence.lean`.
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Toolchain pinned by `foundation-lock.json`, executing synchronous compilation (`-DElab.async=false -Ddebug.skipKernelTC=false`), `TrustedBoundary.lean` preflight/audit, standalone `Kernel.Environment.replay`, and the `._unsafe_rec` analysis.
- **`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`nanoda_bin 0.4.19`):** Independent cross-version Lean kernel and Rust external typechecker verifying unmodified `Trusted.{MirAst,MirSemantics}` and all `19` exported public user theorems (`1,795` declarations).
- **`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`:** Upstream baselines pinned by `joshlf/anneal@c131b320e`, establishing exact semantic differences between upstream `rustc`/Miri and Anneal's patched `deinitMovedPlace = true` profile.

**Frozen Contract Integrity:** Stripping only the strictly `private` helper block (`L510–L5551`: `9 private def`, `136 private theorem`) and replacing the `4` Part III theorem proofs (`L5552–L5756`) with `  sorry` reproduces the pre-proof frozen statement (`1,343` lines, `53,472` bytes, SHA-256 `2ef604bdd8754337c00d9c16869e9518b8a984c0b95c3948d4232358ce5d4a2c`, `support/AnnealTrustedMirMoveToCopyStorage.frozen.sha256`) byte-for-byte.

**Admission Envelope & Generalization:** Soundness theorems apply strictly to `Trusted.MirAst.Program` values under `Trusted.MirSemantics@c131b320e` (`pointerWidthBits = 64`, `mirProfileVersion = 1`, `callerMem.allocations = []`, unprojected `Place`, `isSupportedScalarOrUnitTy`, single-frame `frames = [frame]`, `ValidChoice _ _ c := c = 0`). The constructive `iterState` simulation-lifting technique and the `TrustedBoundary.lean` `noncomputable` rule for recursive `def`s generalize across Lean `v4.34.1` Anneal theory modules; the MIR bridge theorems themselves must be re-proved if `MirSemantics` adds executable `.call`, `.assert`, memory, projections, or nondeterminism.

---

## Findings

### 1. Target Semantics ($M_{\text{anneal}}$) and the Forward/Reverse Asymmetry on `Trusted.MirSemantics`

`Basis: source (joshlf/anneal@c131b320e Trusted/{MirAst,MirSemantics,Correspondence}.lean; rust-lang/rust@8144389c) + derived`

Six concrete rules in `Trusted.MirSemantics@c131b320e` govern the exact soundness boundary of `MoveToCopy` and `RemoveStorageMarkers`:

| Semantic Rule (`Trusted.MirSemantics@c131b320e`) | Exact Source Location & Definition | Consequence for `MoveToCopy` & `RemoveStorageMarkers` |
| :--- | :--- | :--- |
| **1. Opt-in `deinitMovedPlace = true`** | `Trusted/MirSemantics.lean:949–976` (`evalOperandToSlot`), `MirAst.lean:537–546`, `Correspondence.lean:69–76`. `.move place` writes `liveUninitSlot ty` (`.live none` for non-ZSTs); `.copy` leaves `locals` untouched. Upstream `rustc@8144389c` (`operand.rs`) leaves non-`Call` move invalidation as an unimplemented `FIXME`; Anneal patches `10` `vendor/lean-miri` files over `lean-miri@c92d1d97`. | `.move p ↦ .copy p` monotonically increases slot definedness (unconditional forward refinement on `WellFormed pSrc q`), but masks move-after-move UB in reverse (Witnesses 3 & 8). |
| **2. Left-to-right `binaryOp` threading** | `Trusted/MirSemantics.lean:145–148` (`evalRvalue` `.binaryOp`). Threads `locals` through `lhs` into `locals₁` before evaluating `rhs`. | `copy _1 + move _1` is `WellFormed` (Witness 1), whereas `move _1 + copy _1` faults `.undefined` (Witness 8); checkers must thread `env → env₁` left-to-right. |
| **3. Inhabited 0-byte ZST preservation** | `Trusted/MirSemantics.lean:721–752` (`liveUninitSlot`), `1279–1300` (`.discriminant`). `liveUninitSlot .unit = .live (some .unit)`; for 1-variant `.zeroSized` enums (`isZstEnumTy ety`), `liveUninitSlot (.enum ety) = .live (some (.enumVal ety 0))`, and `.discriminant` succeeds even on `.live none`. | Moving `.unit` or a 1-variant `.zeroSized` enum leaves it inhabited (Witnesses 7 & 9); checkers must not deinitialize inhabited ZSTs. |
| **4. Entry `hasStorageAnnotation` rule** | `Trusted/MirSemantics.lean:775–790` (`initLocalsLoop`), `813` (`storageAnnotationsInBounds`). `_0` starts at `liveUninitSlot`; params `1..argumentCount` start at `.live (some arg)`; locals `> argumentCount` start **`.dead`** iff `hasStorageAnnotation body idx = true`, else `liveUninitSlot`. | Eliding only `StorageLive` while keeping `StorageDead` keeps `hasStorageAnnotation = true`, starting the local `.dead` and turning a `WellFormed` body into `.fault .undefined` (Witness 6). Forward soundness requires **all-or-nothing** elision. |
| **5. `StorageLive` wiping & `StorageDead 0`** | `Trusted/MirSemantics.lean:1376–1405` (`evalStatement`). `.storageLive id` resets `locals[id] := liveUninitSlot localTy` even when already initialized (including `_0` or params) without faulting; `.storageDead 0` and OOB markers (`id ≥ locals.length`) fault `.unsupported`. | Repeated `StorageLive` wipes prior values in `pSrc` while `.nop` preserves them in `pTgt` (Witness 5). Preserving `.storageDead 0` and OOB markers keeps `storageAnnotationsInBounds` and `.unsupported` identical. |
| **6. Deterministic single-frame stepping** | `Trusted/MirSemantics.lean:646–647` (`ValidChoice _ _ c := c = 0`), `801–829` (`initState`), `1568–1620` (`evalTerminator`, `evalStep`). Only `frames = [frame]` and empty `callerMem` execute; `.call`, `.assert`, `.unwindResume`, `.unsupported` immediately fault `.unsupported`. | Determinism lets `iterState` build `Diverges` witnesses constructively without `Classical.choice`, giving `Behavior ↔` and `Diverges ↔` forward and full `FaultKind ↔` under certified bisimulation. |

Consequently, **forward compilation (`pSrc → pTgt`)** requires only safe-source refinement (`WellFormed pSrc q → ...`) and needs no static certificate, whereas **reverse VC transport (`pTgt → pSrc`)** requires a static certificate proving `pSrc` never triggers a move-deinitialization or storage-liveness fault that `pTgt` masked.

---

### 2. Decidable Rewrite Relations (`Part I`) and Unified Three-State CFG Abstract Interpretation (`Part II`)

`Basis: source + execution (support/AnnealTrustedMirMoveToCopyStorage.lean, L66–L509)`

#### Part I: Total Structural Rewrite Relations (`L66–L260`)

Both relations are pure boolean predicates directly on `Trusted.MirAst.Program` with zero surrogate ASTs:

- **`isMoveToCopyProgram (pSrc pTgt : Program) : Bool` (`L213–L218`):** Enforces exact structural equality on `pointerWidthBits`, `mirProfileVersion`, `entryDefId`, `scope`, and every body header (`argumentCount`, `MirTy.beqList locals`, `isUnsafe`, `stringBeq identity`, block `cleanup`). Every operand is checked by `isMoveToCopyOperand` (`L145–L150`), allowing `.move p ↦ .copy p` (for identical `placeEq p₁ p₂`) and requiring exact equality elsewhere. Storage markers are untouched, so `hasStorageAnnotation`, `storageAnnotationsInBounds`, `BodyStaticAdmitted`, `ValidEntryArgs`, and `initState` are identical.
- **`isRemoveStorageMarkersProgram (pSrc pTgt : Program) : Bool` (`L254–L259`):** Enforces exact equality on metadata and operands (`operandEq`), and checks every statement with `isRemoveStorageMarkersStmt numLocals` (`L225–L236`):
  - `.storageLive id ↦ .nop` iff `id < numLocals`; out-of-bounds `.storageLive id` (`id ≥ numLocals`) is preserved verbatim.
  - `.storageDead id ↦ .nop` iff `id ≠ 0 ∧ id < numLocals`; `.storageDead 0` and out-of-bounds `.storageDead id` are preserved verbatim.
  - This exact rule guarantees (1) `storageAnnotationsInBounds bSrc = storageAnnotationsInBounds bTgt` unconditionally (even with empty `locals` or unreachable OOB markers), preserving `BodyStaticAdmitted` and `initState`, and (2) whenever `initState` succeeds, every local `idx > argumentCount` has `hasStorageAnnotation bTgt idx = false`, so every slot in `pTgt` stays `.live _` throughout execution.

#### Part II: Unified Three-State Abstract Domain & Certificate Checkers (`L261–L509`)

One parameterized checker `checkAbsBody (requireLiveDst : Bool) (body : Body) (cert : BodyAbsCert) : Bool` (`L480–L489`) validates both passes:

- **Lattice (`AbsSlot`, `L278–L295`):** Three-point order `.liveInit ⊑ .liveUninit ⊑ .dead` (`absSlotImplies`), lifted pointwise (`absEnvImplies := listRel absSlotImplies`). `.liveInit` certifies identical well-typed initialized values in `pSrc` and `pTgt`; `.liveUninit` certifies both live; `.dead` permits `.dead` in `pSrc` (forbidding reads, and forbidding writes when `requireLiveDst = true`).
- **Inhabited ZSTs & Entry State (`L265–L322`):** `isAlwaysInhabitedZst` returns `true` strictly for `.unit` and `.enum ety` with `isZstEnumTy ety = true`; `initAbsSlot` mirrors `initLocalsLoop` case-for-case.
- **Operand & Rvalue Stepping (`L330–L380`):** `.copy p` requires `p.projection.isEmpty` and `.liveInit`; `.move p` requires `.liveInit` and transitions `p.localId` to `.liveInit` if `isAlwaysInhabitedZst ty`, else `.liveUninit`. `.binaryOp` threads `env → env₁ → env₂` left-to-right (accepting `copy _k + move _k`, rejecting `move _k + copy _k`). `.discriminant p` accepts `.liveInit | .liveUninit` on `isZstEnumTy` enums (rejecting `.dead`) and requires `.liveInit` on scalar-tagged enums. Unsupported rvalues (`.ref`, `.addressOf`, `.aggregateTuple`, `.unsupported`) return `none`.
- **Statement Stepping & `requireLiveDst` (`L386–L413`):**
  - `checkNoUseAfterMoveProgram := listRel (checkAbsBody false)` (`L492–L498`): admits `.assign dst _` even when `env₁[dst.localId] = some .dead`. This remains sound for `MoveToCopy` because `.dead` vs. `.live` never differs between `pSrc` and `pTgt`, so `writePlace` faults identically (`.unsupported` on `!checkVal` or `.undefined` on `.dead`) and halts immediately.
  - `checkStorageSafeProgram := listRel (checkAbsBody true)` (`L502–L508`): enforces `storageAnnotationsInBounds body = true` (`L488`) and rejects writes into `.dead` slots (`L410`). Both modes reject `.storageDead 0` and OOB storage markers.
- **CFG Blocks & Terminators (`L428–L490`):** `BodyAbsCert := List (Option (List AbsSlot))` marks unreachable blocks `none` (`checkAbsBlock` returns `true`). Block `0` must be entailed by `initAbsEnvLoop`. In-bounds `.goto` and all `.switchInt` targets must be `some tgtEnv` entailed by `exitEnv` (OOB targets fault `.unsupported` identically). Non-cleanup `.return_` requires `exitEnv[0] = some .liveInit`. Immediate-fault terminators (`.unreachable`, `.unwindResume`, `.assert`, `.call`, `.unsupported`) return `true` at `L468–L469` (tightly coupled to `MirSemantics@c131b320e`; see Boundary 1).

---

### 3. The Four Core Kernel-Checked Theorems (`Part III`) and Four-Layer Proof Architecture

`Basis: source + execution (support/AnnealTrustedMirMoveToCopyStorage.lean, L510–L5756; [kernel-checked proof])`

#### Verbatim Public Signatures of the Four Core Theorems (`L5560–L5755`)

All four theorem types reference strictly `Init.{Core,Prelude}`, `Trusted.{MirAst,MirSemantics}`, and pure definitions in `VrustcFormal.F1_1b` (`0` `Anneal.*` references):

```lean
theorem codegen_moveToCopy_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isMoveToCopyProgram pSrc pTgt = true) :
    (∀ q : Query,
      WellFormed pSrc q →
      WellFormed pTgt q ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (Diverges pTgt q ↔ Diverges pSrc q)) ∧
    (∀ (q : Query) (post : TerminalOut → Prop),
      SatisfiesPost pSrc q post → SatisfiesPost pTgt q post) ∧
    (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      BodyVerified pSrc defId bSrc safetyPre →
      BodyVerified pTgt defId bTgt safetyPre)

theorem vc_transport_moveToCopy_certified_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isMoveToCopyProgram pSrc pTgt = true)
    (hCert : checkNoUseAfterMoveProgram pSrc cert = true) :
    (∀ q : Query,
      (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (∀ k : FaultKind,
        ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
      (Diverges pTgt q ↔ Diverges pSrc q)) ∧
    (∀ (q : Query) (post : TerminalOut → Prop),
      SatisfiesPost pTgt q post ↔ SatisfiesPost pSrc q post) ∧
    (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      (BodyVerified pTgt defId bTgt safetyPre ↔
        BodyVerified pSrc defId bSrc safetyPre))

theorem codegen_removeStorageMarkers_refines_unconditional
    (pSrc pTgt : Program)
    (hRel : isRemoveStorageMarkersProgram pSrc pTgt = true) :
    (∀ q : Query,
      WellFormed pSrc q →
      WellFormed pTgt q ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (Diverges pTgt q ↔ Diverges pSrc q)) ∧
    (∀ (q : Query) (post : TerminalOut → Prop),
      SatisfiesPost pSrc q post → SatisfiesPost pTgt q post) ∧
    (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      BodyVerified pSrc defId bSrc safetyPre →
      BodyVerified pTgt defId bTgt safetyPre)

theorem vc_transport_removeStorageMarkers_certified_iff
    (pSrc pTgt : Program) (cert : ProgramAbsCert)
    (hRel : isRemoveStorageMarkersProgram pSrc pTgt = true)
    (hCert : checkStorageSafeProgram pSrc cert = true) :
    (∀ q : Query,
      (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
      (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
      (∀ k : FaultKind,
        ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
      (Diverges pTgt q ↔ Diverges pSrc q)) ∧
    (∀ (q : Query) (post : TerminalOut → Prop),
      SatisfiesPost pTgt q post ↔ SatisfiesPost pSrc q post) ∧
    (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
      Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
      Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
      (BodyVerified pTgt defId bTgt safetyPre ↔
        BodyVerified pSrc defId bSrc safetyPre))
```

#### Four-Layer Private Proof Architecture (`L510–L5551`: `9 private def`, `136 private theorem`)

| Layer | Lines | Core Private Definitions & Lemmas | Mathematical Role |
| :--- | :---: | :--- | :--- |
| **Layer A: Reflection & Lists** | `L510–L1283` | `nat_beq_eq`, mutual `mirTy_beq_eq`/`mirTy_beqList_eq` (`L1024–L1077`), `enumTy_beq_eq`, `listRel_getElem?_{left,right}`, `bodyStaticAdmitted_eq_of_fields`, `initState_equiv` | Reflects boolean AST equality into `=` and proves identical `BodyStaticAdmitted` and `initState` admission across both passes. |
| **Layer B: Constructive Simulation Lifting** | `L1284–L1585` | `iterState` (`L1286`), `step_iff_evalStep`, `reaches_fwd_sim`, `diverges_fwd_sim`, `fwd_sim_lift` (`L1354`), `bisim_lift` (`L1492`) | Lifts 1-step relations `R : State → State → Prop` to `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, and `Diverges`. Building infinite traces constructively via deterministic `iterState` avoids `Classical.choice` entirely (`[propext]` only!). |
| **Layer C1: Forward Refinement** | `L1586–L3772` | `SlotWellTyped` (`L1588`), `checkVal_{unit,zstEnum}_eq`, `slot_eq_liveUninit_of_zst`, `SlotFwdRefines allowDead` (`L1738`), `LocalsFwdRefines`, `StateFwdRel` (`L3211`), `{moveToCopy,removeStorage}_fwd_query` | Parameterizes forward slot refinement by `allowDead` (`false` for `MoveToCopy`, `true` for `RemoveStorageMarkers`). `SlotWellTyped` forces every live inhabited ZST to equal `liveUninitSlot ty`. |
| **Layer C3: Certified Bisimulation** | `L3773–L5551` | `SlotCertBisim reqLiveDst` (`L3775`), `slotCertBisim_mono`, `LocalsCertBisim`, `BlockTermOk` (`L4494`), `StateCertBisim` (`L4679`), `evalStep_cert_bisim_generic`, `{moveToCopy,removeStorage}_cert_bisim_query` | Couples `pSrc`/`pTgt` frames with the active residual abstract environment `curEnv` over `bb.statements.drop stmtIdx`, proving exact 1-step lockstep including identical `FaultKind` on every fault path. |

**Composing With `Anneal.MirWp`:** Discharging a specification on normalized `pTgt` via `Anneal.MirWp.wellFormed_and_spec_of_wp` (`Trusted/MirSemantics.lean:1831–1837`) produces `SatisfiesPost pTgt q post ∧ ¬ Diverges pTgt q ∧ ∃ out, Behavior pTgt q out ∧ post out`. Applying `vc_transport_*_certified_iff` transports all three conjuncts and `BodyVerified` back to `pSrc` with zero TCB additions and zero `Anneal.*` imports in `VrustcFormal.F1_1b`.

---

### 4. Complete Inventory of Public Adequacy Theorems and Positive/Negative Witnesses (`19` Public User Theorems)

`Basis: source + execution (support/AnnealTrustedMirMoveToCopyStorage.lean, L5757–L6489; [kernel-checked proof])`

Alongside the `4` core theorems (Part III), the file proves `5` deterministic execution adequacy theorems (Part IV, `L5757–L5927`) and `10` theorems in Part V (`L5928–L6489`: `9` concrete non-vacuity canaries and sharpness counterexamples plus `bool_and_false`):

| # | Public Theorem (`VrustcFormal.F1_1b`) | Role | Exact Property Established | Axioms | Reachable Decls |
| :-: | :--- | :--- | :--- | :--- | ---: |
| 1 | `codegen_moveToCopy_refines_unconditional` | Core 1 | Unconditional forward refinement for `MoveToCopy` (`WellFormed`, `Behavior ↔`, `Diverges ↔`, `SatisfiesPost`, `BodyVerified`). | `[propext]` | `1,447` |
| 2 | `vc_transport_moveToCopy_certified_iff` | Core 2 | Certified all-query bidirectional equivalence (`↔`, incl. `ReachesResult (.fault k)`) for `MoveToCopy`. | `[propext]` | `1,522` |
| 3 | `codegen_removeStorageMarkers_refines_unconditional` | Core 3 | Unconditional forward refinement for all-in-bounds `RemoveStorageMarkers`. | `[propext]` | `1,488` |
| 4 | `vc_transport_removeStorageMarkers_certified_iff` | Core 4 | Certified all-query bidirectional equivalence for `RemoveStorageMarkers`. | `[propext]` | `1,564` |
| 5 | `reaches_head_det` | Adequacy | Prepends a deterministic `Step` to `Reaches`. | `[propext]` | `1,013` |
| 6 | `execOutcome_reaches_inv` | Adequacy | Preserves fuel-bounded `execOutcome` along `Reaches`. | `[propext]` | `1,023` |
| 7 | `execOutcome_terminal` | Adequacy | Extracts a reachable terminal `.done`/`.fault` step from `execOutcome`. | `[propext]` | `1,022` |
| 8 | `positiveCanary_of_execReturns` | Adequacy | `execReturns p fuel q expected → PositiveCanaryClaim p q expected`. | `[propext]` | `1,069` |
| 9 | `negativeCanary_of_execFaults` | Adequacy | `other ≠ expected → execFaults p fuel q expected → NegativeCanaryClaim p q expected other`. | `[propext]` | `1,084` |
| 10 | `canary_moveToCopy_loop_and_m4_accepted` | Witness 1 | 4-block counted loop (`args := [3u32]`: `3 → 7 → 11`, latch `_1 = add(move _1, 4)`, `SwitchInt(move _2)`, exit `copy _1 + move _1 = 22u32`) certified by `checkNoUseAfterMoveProgram`, returning `22u32` on both sides. | `[propext]` | `1,261` |
| 11 | `canary_removeStorageMarkers_scoped_cf_accepted` | Witness 2 | Directly rewrites Anneal's TCB canary `Trusted.MirSemantics.progStmtsAndCf` (`StorageLive(2); StorageDead(2); StorageLive(2); SwitchInt(move _2)`), certified by `checkStorageSafeProgram`, returning `100u32` on `10` and `200u32` on `99`. | `[propext]` | `1,260` |
| 12 | `bool_and_false` | Helper | `(b && false) = false`, enabling finite case exhaustion for universal `∀ cert` proofs. | `[]` | `13` |
| 13 | `ce_vc_transport_moveToCopy_unsound_without_cert` | Witness 3 | `_0 = move _1; _0 = copy _1`: `pTgt` returns `7u32`, `pSrc` faults `.undefined`, and **universally** `∀ cert, checkNoUseAfterMoveProgram pSrc cert = false`. | `[propext]` | `1,285` |
| 14 | `ce_vc_transport_storageDead_unsound_without_cert` | Witness 4 | `StorageLive(1); _1 = 42; StorageDead(1); _0 = copy _1`: `pTgt` returns `42u32`, `pSrc` faults `.undefined`, and `∀ cert, checkStorageSafeProgram pSrc cert = false`. | `[propext]` | `1,287` |
| 15 | `ce_storageLive_wipes_value_in_TrustedMir` | Witness 5 | `StorageLive(1); _1 = 42; StorageLive(1); _0 = copy _1`: repeated `StorageLive(1)` wipes `_1` to `liveUninitSlot`, faulting `.undefined` in `pSrc` while `pTgt` returns `42u32`; `∀ cert, checkStorageSafeProgram = false`. | `[propext]` | `1,287` |
| 16 | `ce_partial_storageLive_only_elision_unsound` | Witness 6 | Rewriting only `StorageLive(1) ↦ .nop` while keeping `StorageDead(1)` leaves `hasStorageAnnotation = true`, turning a `WellFormed` `pSrc` (`99u32`) into `.fault .undefined`; rejected by `isRemoveStorageMarkersProgram = false`. | `[propext]` | `1,235` |
| 17 | `canary_zst_unit_move_then_copy_valid_in_TrustedMir` | Witness 7 | `_0 = move _1; _0 = copy _1` on `MirTy.unit` passes `checkNoUseAfterMoveProgram = true` and returns `.unit`. | `[propext]` | `1,130` |
| 18 | `ce_m4_reversed_move_then_copy_rejected` | Witness 8 | `_0 = add(move _1, copy _1)`: `pTgt` returns `18u32` on `9u32`, `pSrc` faults `.undefined` under left-to-right operand evaluation, and `∀ cert, checkNoUseAfterMoveProgram = false`. | `[propext]` | `1,285` |
| 19 | `canary_zst_enum_discriminant_storage_elision` | Witness 9 | 1-variant `.zeroSized` `MirTy.enum` (`discriminants := [7]`) executing `StorageLive(1); _0 = discriminant(_1); StorageDead(1)` passes `isRemoveStorageMarkersProgram` + `checkStorageSafeProgram` and returns `7u32` on both sides. | `[propext]` | `1,262` |

*(Lean also elaborates `3` auto-generated `AbsSlot.*.sizeOf_spec` lemmas with `[]` axioms. Every theorem type originates strictly from `VrustcFormal.F1_1b`, `Init.{Core,Prelude}`, and `Trusted.{MirAst,MirSemantics}`.)*

---

### 5. Lean `v4.34.1` `._unsafe_rec` / `isPartial = true` Discovery on Recursive `Prop` and Value `def`s Under `TrustedBoundary.lean`

`Basis: source (joshlf/anneal@c131b320e TrustedBoundary.lean:1117–1152, MirAst.lean:75–92; lean4@5045d005 src/Lean/Replay.lean:176–185) + execution ([real measurement])`

Pre-freeze testing directly against `TrustedBoundary.validateRepoConstant` exposed a critical Lean `v4.34.1` trap for all Anneal `theory/` authors:

1. **Observed Failure (`[real measurement]`):** Omitting `noncomputable` on **both** a value-level recursive definition (`def listRel`, `L69`) and a **`Prop`-valued recursive definition** (`def execOutcome : ... → Nat → State → Prop`, `L5761`) caused Lean `v4.34.1` to emit `isPartial = true` `._unsafe_rec` compiler auxiliaries into the `.olean` inventory:
   ```text
   [REJECTED ConstantInfo] VrustcFormal.F1_1b.listRel._unsafe_rec: isUnsafe=false, isPartial=true
   [validateRepoConstant FAIL] VrustcFormal.F1_1b.listRel._unsafe_rec: policy:unsafe/partial declaration ...
   [REJECTED ConstantInfo] VrustcFormal.F1_1b.execOutcome._unsafe_rec: isUnsafe=false, isPartial=true
   [validateRepoConstant FAIL] VrustcFormal.F1_1b.execOutcome._unsafe_rec: policy:unsafe/partial declaration ...
   ```
2. **Root Cause (`[published source]`):** Lean's kernel replayer (`src/Lean/Replay.lean:176–185`) skips `unsafe` and `partial` constants without kernel-checking them, so `TrustedBoundary.ensureReplayableConstant` / `validateRepoConstant` (`TrustedBoundary.lean:1117–1152`) unconditionally rejects `ci.isPartial` across both `trusted/` and `theory/` modules.
3. **Prescriptive Rule for Anneal `theory/` Authors (`[real measurement]`):**
   - Mark **every** recursive `def`—including recursive `: Prop` definitions—as `noncomputable def` individually (never `noncomputable section`, which `TrustedBoundary.inspectNodeKind` forbids). This suppresses `._unsafe_rec` without altering kernel reduction (`rfl` still succeeds).
   - Mark non-`Prop` transitive callers (`switchTargetsEq`, `absEnvImplies`, etc.) `noncomputable def` to satisfy `dependsOnNoncomputable`.
   - Leave **non-recursive `: Prop` definitions** (`execReturns`, `execFaults`, `SlotFwdRefines`, `LocalsFwdRefines`, `StateFwdRel`) unmarked—they compile cleanly with `0` `isPartial` constants while avoiding Anneal's Pass 1 advisory against redundant `noncomputable` on `: Prop`.
4. **Before/After Receipt (`[real measurement]`):** Adding `noncomputable` to `listRel`, `switchTargetsEq`, `absEnvImplies`, and `execOutcome` reduced pre-proof statement constants from `240` to `238`, cut `validateRepoConstant` errors from `2` to `0`, kept all witness `rfl` proofs passing, and enabled full `Kernel.Environment.replay`.

---

### 6. Three-Kernel Verification, Unmodified `TrustedBoundary.lean` Audit & Replay, and `nanoda_bin 0.4.19` Receipts

`Basis: execution (recorded 2026-11-20 across unmodified joshlf/anneal@c131b320e, Lean v4.34.1, Lean v4.35.0, lean4export 3.1.0, and nanoda_bin 0.4.19; [real measurement])`

| Verification Step / Checker | Pinned Revision | Mode & Configuration | Exit | Wall (s) | User (s) | Peak RSS (MB) | Measured Outcome |
| :--- | :--- | :--- | :---: | ---: | ---: | ---: | :--- |
| **1. `foundation-lock.json` check** | `anneal@c131b320e` | Verify `51/51` `v4.34.1` sysroot modules (`.olean*`, `.ir*`) | `0` | — | — | — | `51 / 51` matched (`0` SHA-256 mismatches) |
| **2a. Lean `v4.34.1` Run A (cached)** | `lean4@5045d005` | `-DElab.async=false -Ddebug.skipKernelTC=false` | `0` | `16.101` | `15.77` | `571.20` | `0` errs/warns/`sorry`; `.olean` = `11,353,432 B` |
| **2b. Lean `v4.34.1` Run B (fresh)** | `lean4@5045d005` | Fresh `Trusted.{MirAst,MirSemantics}` (`0` diffs across `1,324` constants) + proof | `0` | `16.270` | `16.06` | `569.32` | `0` errs/warns/`sorry`; `.olean` = `11,352,200 B` |
| **3a. `TrustedBoundary` `"preflight"`** | `anneal@c131b320e` | `SourceRole.theory`, `8` admitted imports, explicit `prelude` | `0` | `3.914` | — | — | `ok = true`, `trustTier = null` |
| **3b. `"preflight"` negative probe** | `anneal@c131b320e` | Frozen pre-proof file with `4` `sorry` stubs | `1` | `3.360` | — | — | Fail-closed: `policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry` |
| **4. `TrustedBoundary` Pass 1 `"audit"`** | `anneal@c131b320e` | `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, `requireMirWp = true` | `0` | `6.607` | — | — | `ok = true`, `kernelDeclarations = 1,324`, `replayedDeclarations = 2,183`, `compilerOnlyNames = 281`, `reachableDeclarations = 2,953`, `axioms = ["propext"]`, `replay = true` |
| **5. Standalone replay (no `MirWp`)** | `lean4@5045d005` | `{Trusted.MirAst, Trusted.MirSemantics, F1_1b}` onto locked foundation | `0` | — | — | — | `1,926 / 1,926` decls (`716 + 608 + 602`); `0` forbidden constructs across `602` module + `1,766` transitive decls |
| **6a. Lean `v4.35.0` (`MirAst`)** | `lean4@eb6cafb7` | Fresh `-DElab.async=false -Ddebug.skipKernelTC=false` | `0` | `0.985` | `0.82` | `178.23` | `0` errs/warns; `.olean` = `1,362,944 B` |
| **6b. Lean `v4.35.0` (`MirSemantics`)** | `lean4@eb6cafb7` | Fresh `-DElab.async=false -Ddebug.skipKernelTC=false` | `0` | `1.269` | `1.08` | `195.56` | `0` errs/warns; `.olean` = `1,221,264 B` |
| **6c. Lean `v4.35.0` (`F1_1b`)** | `lean4@eb6cafb7` | Fresh `-DElab.async=false -Ddebug.skipKernelTC=false` | `0` | `14.713` | `14.50` | `545.20` | `0` errs/warns; `.olean` = `11,343,888 B` |
| **7. `lean4export 3.1.0`** | `lean4export@5a9a355d` | Export all `19` public user theorems to NDJSON | `0` | `1.408` | `1.01` | `441.40` | `17,545,747 B` (`338,284` lines; `95` inductives, `1,103` defs, `306` thms, `1` axiom = `propext`) |
| **8a. `nanoda_bin 0.4.19` (positive)** | `nanoda_lib@0da9f98f` | `permitted_axioms = ["propext"]`, `unpermitted_axiom_hard_error = true`, `nat_extension = true`, `string_extension = true` | **`0`** | **`0.889`** | **`0.85`** | **`34.29`** | **`Checked 1795 declarations with no typechecker errors`** *(cosmetic note `"Unable to print axioms"`)* |
| **8b. `nanoda_bin` (negative probe)** | `nanoda_lib@0da9f98f` | `permitted_axioms = []`, `unpermitted_axiom_hard_error = true` | **`1`** | `0.012` | `0.01` | — | Fail-closed: `Error: export file declares unpermitted axiom "propext"` |
| *(Note) `lean4lean`* | Host binary | Attempted on compiled `.olean` & sysroot | `1` | `0.661` | `0.19` | `81.01` | **Not exercised:** older `.olean` format (`incompatible header` on `v4.35.0` and `v4.28.0-rc1` `Lean.olean`). |

**Zero-Hit Hygiene Scan (`[real measurement]`):** Across all `602` kernel constants (`248` public, `354` private) and `1,766` transitively visited declarations: `0` `isUnsafe`, `0` `isPartial`, `0` `._unsafe_rec`, `0` `opaqueInfo`/`axiomInfo`/`quotInfo`, `0` `sorryAx`/`Expr.hasSorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`, `0` `Trusted` namespace declarations, `0` `Anneal.*` references, `0` CRLF or bidi/control Unicode characters.

**External-Checker Efficiency:** `nanoda_bin 0.4.19` re-verifies the entire `1,795`-declaration exported proof closure in **`0.889 s` and `34.29 MB` RSS**—**`16.5×` faster / `15.9×` leaner** than Lean `v4.35.0` (`14.713 s` / `545.20 MB`) and **`18.3×` faster / `16.6×` leaner** than Lean `v4.34.1` (`16.270 s` / `569.32 MB`).

---

### 7. Analytical Dimensions Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

`Basis: execution + source + derived ([real measurement] and [kernel-checked proof])`

| Dim | Category | Measured Status / Assessment |
| :-: | :--- | :--- |
| **`L1`** | Authoring & proof velocity | `[real measurement]` `1,343`-line frozen contract + `5,042`-line strictly `private` proof (`6,489` lines, `232` source decls, `155` theorems) audited pre-freeze (catching `._unsafe_rec`), frozen, proved (`0` `sorry`), and 3-kernel verified on `2026-11-20`. |
| **`L2`** | Toolchain / TCB build time | `[real measurement]` Fresh Lean `v4.35.0` build of `Trusted.MirAst.lean` (`0.985 s`, `178.23 MB`) + `Trusted.MirSemantics.lean` (`1.269 s`, `195.56 MB`) = `2.254 s`; zero external packages beyond `Init` and `Trusted`. |
| **`L3`** | Pass / cert synthesis latency | **`not measured`** — Verifies *a posteriori* checkers only; no MIR pass or certificate synthesizer is implemented. |
| **`L4`** | Generated code performance | **`not measured`** — Pure `Trusted.MirAst → Trusted.MirAst` theorem; no native codegen. |
| **`L5`** | Checking latency & throughput | `[real measurement]` Lean kernel: `16.101–16.270 s` (`v4.34.1`) / `14.713 s` (`v4.35.0`); `TrustedBoundary.lean`: `3.914 s` preflight + `6.607 s` audit (`2,183` decls); `lean4export`: `1.408 s`; **`nanoda_bin 0.4.19`: `0.889 s` (`1,795` decls, `~2,019` decls/s).** Large-body `check*Program` reduction scaling is **`not measured`**. |
| **`L6`** | RAM & artifact footprint | `[real measurement]` Source `275,460 B`; `.olean` `11.35 MB` (`v4.34.1`) / `11.34 MB` (`v4.35.0`); NDJSON `17.55 MB`; peak RSS `569.32–571.20 MB` (`v4.34.1`), `545.20 MB` (`v4.35.0`), `441.40 MB` (`lean4export`), **`34.29 MB` (`nanoda_bin`)**. |
| **`C1`** | Spec & assumption auditability | `[real measurement]` `509`-line specification/checker prefix + `4` theorem types referencing only `Init.*` and `Trusted.{MirAst,MirSemantics}` (`0` `Anneal.*`, `[propext]` only); exact `53,472`-byte frozen SHA-256 reconstruction. |
| **`C2`** | Orthogonality & simplicity | `[derived]` Single boolean `requireLiveDst` parameter unifies both checkers (`checkAbsBody`), mirrored by `SlotFwdRefines allowDead`, `SlotCertBisim reqLiveDst`, `evalStep_cert_bisim_generic`, and Layer B `fwd_sim_lift`/`bisim_lift`. |
| **`V1`** | Adequacy, mutation & non-vacuity | `[kernel-checked proof]` + `[real measurement]` `9` witnesses (loops, M4 `copy + move`, `progStmtsAndCf`, `.unit`/1-variant `.zeroSized` enum ZSTs, `StorageLive` wiping, partial elision, `∀ cert` universal rejections) + paired fail-closed probes on `TrustedBoundary.lean` and `nanoda_bin`. |
| **`V2`** | Differential fuzzing | **`not measured`** — No automated fuzzer against `rustc`'s `RemoveStorageMarkers` pass or `anneal-rustc-capture`. |
| **`V3`** | Weak-memory / crash / silicon | **`known not to apply`** — Strictly sequential, single-frame, deterministic, value-only MIR fragment. |
| **`V4`** | Held-out ecosystem replay | **`not examined`** — Exercised on `1–4` block / `2–3` local fixtures (including `progStmtsAndCf`); real captured crate bodies not replayed. |

---

## Boundaries

### Honest Scope & Non-Claims (`VrustcFormal.F1_1b`)

**What `VrustcFormal.F1_1b` proves (`[kernel-checked proof]`):** Directly over unmodified `joshlf/anneal@c131b320e` `Trusted.MirAst` and `Trusted.MirSemantics`—with zero surrogate MIR AST, zero `Anneal.*` dependencies, and only `propext` (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorry`, independently re-checked by `TrustedBoundary.lean` replay on Lean `v4.34.1` and by `nanoda_bin 0.4.19` via Lean `v4.35.0` + `leanexport 3.1.0`)—`VrustcFormal.F1_1b` mechanizes the exact forward/reverse asymmetry for two MIR pre-normalization relations:
1. **Unconditional forward refinement** (`codegen_moveToCopy_refines_unconditional`, `codegen_removeStorageMarkers_refines_unconditional`): on any `WellFormed pSrc q`, rewriting any subset of `Operand.move p ↦ Operand.copy p`, or replacing all in-bounds `StorageLive(id)` (`0 ≤ id < |locals|`) and non-return `StorageDead(id)` (`1 ≤ id < |locals|`) statements 1-to-1 with `.nop` (preserving `.storageDead 0` and out-of-bounds markers), unconditionally preserves `WellFormed`, exact finite `Behavior` (`↔`), infinite `Diverges` (`↔`), `SatisfiesPost`, and `BodyVerified`.
2. **Certified bidirectional VC transport** (`vc_transport_moveToCopy_certified_iff`, `vc_transport_removeStorageMarkers_certified_iff`): pairing those relations with a passing CFG abstract-interpretation certificate (`checkNoUseAfterMoveProgram` / `checkStorageSafeProgram`) upgrades refinement to full operational equivalence (`↔`) for `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and `BodyVerified` across all queries `q : Query`, allowing Anneal proofs discharged via `Anneal.MirWp.wellFormed_and_spec_of_wp` on `pTgt` to transport back to `pSrc`.
3. **Non-vacuity and sharpness:** Nine kernel-checked witnesses confirm that loops, left-to-right `copy _1 + move _1`, Anneal's own `progStmtsAndCf`, and inhabited 0-byte ZSTs (`()`, 1-variant `.zeroSized` enums) pass, while uncertified reverse VC transport, reversed `move _1 + copy _1`, repeated `StorageLive` wiping, and partial `StorageLive`-only elision are all strictly unsound on `Trusted.MirSemantics`.

**Explicit Non-Claims & Trust Boundaries:**
- **Single-frame scalar/fieldless-enum fragment only:** `Trusted.MirSemantics@c131b320e` is strictly deterministic (`ValidChoice _ _ c := c = 0`), single-frame, and value-only (`callerMem.allocations = []`; locals restricted to `.bool`, `.int`, `.unit`, `.never`, and admitted fieldless `.enum`). It models **no** heap/stack memory, raw pointers, `&`/`&mut` references, aliasing, place projections, structs/tuples/arrays, unwinding, or Stacked/Tree Borrows. `TerminatorKind.call` and `.assert` fail closed immediately (`.fault .unsupported`) without evaluating operands, so `checkAbsBlock` does **not** validate `.call` arguments or interprocedural `deinitInPlaceArg` semantics—extending `Trusted.MirSemantics` to execute calls, assertions, or memory will require extending both the checkers and proofs.
- **Semantic profile vs. upstream `rustc`/Miri:** `Trusted.MirSemantics` models Anneal's opt-in `deinitMovedPlace = true` over-approximation (stricter than current upstream `rustc@8144389c`/Miri outside `Call` arguments), resets slots on repeated `StorageLive` without UB, and treats `RemoveStorageMarkers` as 1-to-1 `.nop` replacement rather than `.nop`-deleting `SimplifyCfg` compaction. Composite ZSTs (`[(); N]`, `((), ())`, structs, `[!; 0]`) and 0-variant uninhabited enums are outside `isSupportedScalarOrUnitTy` / `enumAdmitted`.
- **Per-body / semantic judgments, not arbitrary crate syntax or direct `wpProg` terms:** `VrustcFormal.F1_1b` preserves `BodyVerified` and `SatisfiesPost`, not `ProgramVerified`/`CrateTheorem`/`UnitTheorem` under arbitrary syntactic `Specs.property : Program → Prop`, and does not directly rewrite `Anneal.MirWp.wpProg` derivations (composition goes through `wellFormed_and_spec_of_wp`). Whole-program certificate checkers (`listRel` over `pSrc.bodies`) reject a multi-body `Program` if any body falls outside the supported fragment or uses path-sensitive initialization / dynamically dead branches with move/storage violations.
- **Translation validation, `noncomputable` checkers, and external pipeline gap:** `VrustcFormal.F1_1b` verifies *a posteriori* `noncomputable` Lean kernel checkers (not an executable native validator binary, verified MIR pass, or certificate synthesizer; kernel-reduction scaling beyond small fixtures is unmeasured) and makes no end-to-end claim about `anneal-rustc-capture`, `rustc`'s Rust pass implementations, LLVM/Cranelift codegen, or hardware execution.

---

### Eight Highest-Risk Over-Readings and Concrete Counterexamples

`Basis: source + derived (adversarial line-by-line audit of support/AnnealTrustedMirMoveToCopyStorage.lean and joshlf/anneal@c131b320e)`

1. **Single-frame, non-calling, non-panicking, deterministic fragment (`known not to apply` to calls or panics):**
   - *Citations:* `MirSemantics.lean:646–647`, `1568–1569`, `1599–1614`; `support/AnnealTrustedMirMoveToCopyStorage.lean:180–184`, `468–469`, `5765`.
   - *Counterexample:* The `0` in `evalStep p 0 s` is deterministic `Choice := 0`, not a call depth. Because `evalTerminator` immediately faults `.unsupported` on `.call`/`.assert` without evaluating operands, `checkAbsBlock` (`L468–L469`) returns `true` on `call f(move _1, copy _1)` or `assert(move _1)` without checking operands, destinations, or continuation edges. Sound solely because both programs fault in `1` step on `MirSemantics@c131b320e`; executing `.call` (where Miri runs `deinitInPlaceArg`, `MirAst.lean:541`) or `.assert` breaks `checkAbsBlock` and Theorems 1–4 immediately.

2. **Zero memory, aliasing, references, raw pointers, aggregates, projections, or Tree Borrows (`unsupported`, `known not to apply`):**
   - *Citations:* `MirSemantics.lean:721–724`, `803–804`, `815–816`, `953–954`, `1270–1271`, `1313`, `1407–1408`; `support/AnnealTrustedMirMoveToCopyStorage.lean:334, 341, 366, 380, 399`.
   - *Counterexample:* Any function with `&x`, `&mut x`, `*mut T`, projections (`p.0`), or non-empty `callerMem` fails `initState` with `.error .unsupported` (making Theorems 1 & 3 vacuous via `WellFormed pSrc q = False`) and yields `check*Program = false` (making Theorems 2 & 4 inapplicable). Address-taken `StorageDead`, `AllocId` reuse, pointer identity, and Tree Borrows protectors are completely unmodeled.

3. **Semantic divergence from upstream `rustc`/Miri and `SimplifyCfg` (`known not to apply` without adjustment):**
   - *Citations:* `MirSemantics.lean:67–69, 126–148, 923–948, 1376–1405`; `Correspondence.lean:70–76`; `support/AnnealTrustedMirMoveToCopyStorage.lean:220–236`, Witnesses 3, 5, 6 (`L6097–L6345`).
   - *Counterexamples:* (a) Upstream `rustc@8144389c` / Miri uses `deinitMovedPlace = false` outside `Call`, whereas Anneal patches `10` `vendor/lean-miri` files for `deinitMovedPlace = true` (UCG#188). (b) Repeated `StorageLive` wipes live slots without UB (Witness 5), and repeated `StorageDead` is a no-op. (c) `isRemoveStorageMarkersStmt` replaces markers 1-to-1 with `.nop` (preserving `stmtIdx`/step count) and proves no stuttering simulation for `.nop`-deleting `SimplifyCfg`.

4. **Narrow inhabited-ZST coverage (`known not to apply` to composite ZSTs or 0-variant enums):**
   - *Citations:* `MirAst.lean:211–225, 295–311`; `MirSemantics.lean:507–526, 721–724, 748–752`; `support/AnnealTrustedMirMoveToCopyStorage.lean:265–269`, Witnesses 7 & 9 (`L6346–L6488`).
   - *Counterexample:* `struct Empty;`, `((), ())`, `[(); 4]`, `[!; 0]`, `PhantomData<T>`, and `enum Void {}` (`discriminants = []`) all fail `isSupportedScalarOrUnitTy` / `enumAdmitted` with `.unsupported`. `MirTy.never` has `isAlwaysInhabitedZst = false` and empty `ValidEntryArgs`, reducing `BodyVerified` on `!`-param bodies solely to `BodyStaticAdmitted`.

5. **No arbitrary `Specs.property` transport, no direct `wpProg` term transport, and all-bodies `listRel` sensitivity (`known not to apply`):**
   - *Citations:* `MirSemantics.lean:1766–1808`, `1831–1853`; `support/AnnealTrustedMirMoveToCopyStorage.lean:496–508, 5560–5755`.
   - *Counterexamples:* (a) `specs.property := fun p => p = pSrc` (or inspecting `hasStorageAnnotation`) holds on `pSrc` but fails on `pTgt` despite `BodyVerified`. (b) `VrustcFormal.F1_1b` has `0` `Anneal.MirWp` imports; composition routes through `wellFormed_and_spec_of_wp`, not `wpProg pTgt ↔ wpProg pSrc`. (c) `check*Program` maps `listRel` over all `pSrc.bodies`, so one unsupported body rejects the entire `Program`.

6. **Translation validation only, `noncomputable` checkers, and unbenchmarked linked-list cost (`unsupported` for native binary codegen; `not measured` at scale):**
   - *Citations:* `support/AnnealTrustedMirMoveToCopyStorage.lean:69–508`; `MirAst.lean:77–91`; `MirSemantics.lean:174–181`.
   - *Impact:* Verifies `(pSrc, pTgt, cert)` checking only (no verified pass or synthesizer). Because all checkers transitively call `Trusted` `noncomputable def`s (suppressing `isPartial` `._unsafe_rec`), Lean cannot codegen them into a native executable—they discharge via kernel reduction (`rfl`) or require bridging to a separate executable checker. `getElem?`/`setElem?` are $O(|L|)$ and `hasStorageAnnotation` is $O(|L| \cdot |B| \cdot |S|)$, tested only on `1–4` block / `2–3` local fixtures.

7. **Path-insensitive `AbsSlot` lattice and all-edges checking (`known not to apply` to path-sensitive or dead-branch MIR):**
   - *Citations:* `support/AnnealTrustedMirMoveToCopyStorage.lean:278–295, 357–380, 428–470`.
   - *Counterexample:* `let x: u32; if c { x = 1; } if c { return x; }` is UB-free, yet `AbsSlot` joins `x` to `.liveUninit` before the second branch, causing `check*Program` to return `false` for **every** `cert`. Constant-false `switchInt` branches and reachable `.ref`/`.addressOf`/`.aggregateTuple` blocks are likewise rejected unconditionally.

8. **Forward-refinement silence on faulting queries (`¬ WellFormed pSrc q`) and external pipeline gap (`known not to apply` / `not examined`):**
   - *Citations:* `support/AnnealTrustedMirMoveToCopyStorage.lean:5563–5567, 5666–5670`; `MirAst.lean:875–878, 927–936`; `MirSemantics.lean:1700–1706`.
   - *Counterexample:* On `ceMoveAfterMoveSrc` (`args := [7u32]`), `WellFormed pSrc q = False`, so Theorems 1 & 3 permit `pTgt` to refine UB into `7u32` (fault preservation requires certified Theorems 2 & 4). No claim is made about `anneal-rustc-capture`, `rustc`'s Rust passes, LLVM/Cranelift codegen, or hardware execution.

### Tooling Boundary: `lean4lean`

- **`lean4lean` (`unsupported` on current host):** Running the host `lean4lean` binary against compiled `v4.35.0` `.olean`s (and `v4.28.0-rc1` sysroot `Lean.olean`) failed with `rc = 1` (`incompatible header`). Independent external checking is established by `lean4export 3.1.0` + `nanoda_bin 0.4.19`, not `lean4lean`.

---

## Evidence

### Preserved Artifacts & Primary Sources (`2026-11-20`)

| Artifact / Upstream Subject | Pin / Path | Size / Scope | SHA-256 / Exact Coordinates |
| :--- | :--- | ---: | :--- |
| `support/AnnealTrustedMirMoveToCopyStorage.lean` | Package artifact | `6,489` lines / `275,460 B` | `79d0c63cfe045233d1dcc491529b585981c7afe715bb876f52d314d0a7c91a5c` |
| `support/AnnealTrustedMirMoveToCopyStorage.frozen.sha256` | Package artifact | `1` line / `125 B` | Frozen target (`1,343` lines, `53,472 B`): `2ef604bdd8754337c00d9c16869e9518b8a984c0b95c3948d4232358ce5d4a2c` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` | `40,381 B` (`716` consts) | `71b57539fa1d462e1e856db4d7b0c7a260f7c39255c05cf489cfe87edc1a77c8` (`L75–92, 211–225, 295–311, 525–560, 875–936`) |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean` | `111,865 B` (`608` consts) | `b8378127ea7b81b473a5f86cd164df430feb56296cbbbe57457cc2b125316c0a` (`L67–69, 126–148, 507–526, 646–647, 721–830, 920–976, 1270–1415, 1560–1620, 1695–1855`) |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean` | `117,602 B` | `6f19cc602cf931522d61efb320eae3ca60d7759db20ba6304c912bf372f2fc6a` (`L1110–1153`) |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/foundation-lock.json` | `48,369 B` (`51` mods) | `37f780b6257d0bc99fd5d7d3d0a1f16d168ef066a2a01466f4076f080d3425d2` (`schema: 1`) |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/correspondence/Trusted/Correspondence.lean` | `135,615 B` | `L60–90` (`deinitMovedPlace = true` 10-file patch provenance) |
| `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` (`src/Lean/Replay.lean:176–185`) | Release x86_64-linux | Primary kernel (`16.101 s` / `16.270 s`) & `TrustedBoundary.lean` replay |
| `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | `v4.35.0` | Release x86_64-linux | Cross-version kernel (`14.713 s`, `545.20 MB` RSS) |
| `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` | `leanexport` (`3.1.0`) | Export format `3.1.0` | `19` public theorems (`17,545,747 B`, `338,284` lines, `1.408 s`) |
| `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` | `nanoda_bin` (`0.4.19`) | Rust external kernel | `Checked 1795 declarations with no typechecker errors` (`0.889 s`, `34.29 MB`) |
| `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` | `rustc_const_eval/src/interpret/*`, `rustc_middle/src/mir/syntax.rs` | Upstream baseline | Normative reference for `Operand::Move`, `always_storage_live_locals`, `RETURN_PLACE`, `Variants::Single` |
| `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/Interpreter/*.lean` | Upstream baseline | Base semantics extended by Anneal's opt-in `deinitMovedPlace = true` patch |

### Source vs. Compiled Declaration Inventory (`[real measurement]`)

| Scope | `inductive` | `abbrev` | `def` | `theorem` | Source Total | Kernel `ConstantInfo` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| Public (`VrustcFormal.F1_1b`) | `1` | `2` | `65` | `19` | `87` | `248` |
| Private (`L510–L5551`) | `0` | `0` | `9` | `136` | `145` | `354` |
| **Module Total** | **`1`** | **`2`** | **`74`** | **`155`** | **`232`** | **`602`** |
| Standalone Replay (`MirAst` + `MirSemantics` + `F1_1b`) | — | — | — | — | — | **`1,926`** (`716 + 608 + 602`) |
| Full `TrustedBoundary.lean` Pass 1 Replay (incl. `MirWp`) | — | — | — | — | — | **`2,183`** (`2,953` reachable) |
| Exported `nanoda_bin 0.4.19` Closure (`19` theorems) | `95` | — | `1,103` | `306` (`+1` axiom) | — | **`1,795`** checked decls |

*(Cache provenance note: precompiled `Trusted.{MirAst,MirSemantics}.olean` matched a fresh `v4.34.1` compile with `-R <anneal-root>` at identical byte sizes—`1,392,896 B` and `1,243,560 B`—and `0` diffs across all `1,324` kernel constants; raw bytes differ solely in ASLR mmap header bytes `52–68`.)*

---

## Revalidation

All checks run self-contained in `/tmp` using only preserved package artifacts and pinned GitHub commits:

1. **Frozen Contract Digest Check (~0.1 s):** Verify `sha256sum support/AnnealTrustedMirMoveToCopyStorage.lean` equals `79d0c63cfe045233d1dcc491529b585981c7afe715bb876f52d314d0a7c91a5c`, and confirm stripping `L510–L5551` plus replacing the `4` Part III proofs with `  sorry` matches `support/AnnealTrustedMirMoveToCopyStorage.frozen.sha256` (`2ef604bdd8754337c00d9c16869e9518b8a984c0b95c3948d4232358ce5d4a2c`, `53,472` bytes).
2. **Fresh Synchronous Lean `v4.34.1` Build Against Unmodified `joshlf/anneal@c131b320e` (~18 s):**
   ```bash
   mkdir -p /tmp/reval_anneal_bridge/build/Trusted
   LEAN434="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   "$LEAN434" -DElab.async=false -Ddebug.skipKernelTC=false \
     -R /tmp/reval_anneal/trusted/lean \
     -o /tmp/reval_anneal_bridge/build/Trusted/MirAst.olean \
     /tmp/reval_anneal/trusted/lean/Trusted/MirAst.lean
   LEAN_PATH=/tmp/reval_anneal_bridge/build "$LEAN434" -DElab.async=false -Ddebug.skipKernelTC=false \
     -R /tmp/reval_anneal/trusted/lean \
     -o /tmp/reval_anneal_bridge/build/Trusted/MirSemantics.olean \
     /tmp/reval_anneal/trusted/lean/Trusted/MirSemantics.lean
   LEAN_PATH=/tmp/reval_anneal_bridge/build "$LEAN434" -DElab.async=false -Ddebug.skipKernelTC=false \
     -R support \
     -o /tmp/reval_anneal_bridge/build/AnnealTrustedMirMoveToCopyStorage.olean \
     support/AnnealTrustedMirMoveToCopyStorage.lean
   ```
   Confirm `rc = 0`, `0` errors/warnings, and `#print axioms` returning `[propext]` on all `18` main/adequacy/witness theorems (`[]` on `bool_and_false`).
3. **Unmodified `TrustedBoundary.lean` Preflight & Pass 1 Audit (~11 s):** Run `/tmp/reval_anneal/trusted/audit/TrustedBoundary.lean` in `"preflight"` (`SourceRole.theory`, verifying positive `ok = true` and negative `sorry` rejection `rc = 1`) and Pass 1 `"audit"` (`trustLevel := 0`, `plugins := #[]`, `loadExts := false`, verifying `ok = true`, `axioms = ["propext"]`, `replay = true`, `0` `isPartial` rejections).
4. **Independent Cross-Version & Rust Kernel Check (~19 s):** Repeat Step 2 under `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), export all `19` public theorems via `leanexport` (`5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`), and run `nanoda_bin` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`) with `permitted_axioms: ["propext"]`, `unpermitted_axiom_hard_error: true`, `nat_extension: true`, `string_extension: true`. Confirm `Checked 1795 declarations with no typechecker errors` (`rc = 0`) and `permitted_axioms: []` failure (`rc = 1`).
5. **Drift Triggers Requiring Re-Audit:** Re-verify `checkAbsBlock`, `stepAbsStmt`, and Theorems 1–4 whenever `joshlf/anneal` extends `Trusted/MirSemantics.lean` with executable `.call` (`deinitInPlaceArg`), `.assert`, non-empty `callerMem`, `ProjectionElem`, references/aggregates, or nondeterminism, or updates `deinitMovedPlace`, `liveUninitSlot`, `hasStorageAnnotation`, `TrustedBoundary.lean`, or `foundation-lock.json`.
