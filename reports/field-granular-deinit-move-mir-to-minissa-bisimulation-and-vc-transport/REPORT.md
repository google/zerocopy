# Field-Granular Move-Deinitialization MIR-to-MiniSSA Bisimulation and VC Transport in Lean 4

## Summary

A central semantic tension separates production `rustc` MIR optimization from conservative mechanized MIR semantics such as `joshlf/anneal`'s `Trusted.MirSemantics`: upstream `rustc` (`compiler/rustc_const_eval/src/interpret/operand.rs`, `compiler/rustc_middle/src/mir/syntax.rs`) currently treats `Operand::Move` as non-mutating outside in-place `Call` arguments (leaving move invalidation an open `FIXME`), whereas `Trusted.MirSemantics.evalOperandToSlot` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirSemantics.lean:949-976`) conservatively enforces `deinitMovedPlace = true`, overwriting moved non-ZST local slots with `liveUninitSlot ty` (`.live none`) while keeping inhabited zero-sized types (`.unit` and 1-variant `.zeroSized` enums) inhabited.

Direct empirical inspection of `rustc 1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`) MIR across `4,657` `Runtime(PostCleanup)` bodies of `zerocopy` (`0.9.0-alpha.1`) and `11,339` `libcore` bodies proves two load-bearing constraints for any verified MIR-to-SSA lowering targeting `deinitMovedPlace = true`:

1. **Field-Granular Deinitialization Is Required on Real `Runtime(PostCleanup)` MIR:** Flagship `zerocopy` entry points—including `TryFromBytes::try_read_from_prefix` right in `Runtime(PostCleanup)` (`move (_4.0: MaybeUninit<Self>)` followed by `_3 = copy (_4.1: &[u8])`), `padding_needed_for` (`move (_2.0: usize)` followed by `_12 = move (_2.1: usize)`), and `libcore`'s `slice_get_unchecked_mut_range` (`move (_2.0)` followed by `move (_2.1)`)—move one tuple/struct field and immediately read or move a sibling field. Naive local-granular move deinitialization falsely faults `.undefined` on these valid programs.
2. **Strict Left-to-Right Operand Threading Is Required:** Real `libcore` functions (`parse_decimal_seq`, `dec2flt`, `round_up`, `digits_to_dec_str`; `0.07%` of `libcore` bodies) emit calls such as `slice_index_fail(const 8_usize, copy _104, move _104)`, which succeed strictly because `copy _104` evaluates before `move _104` deinitializes `_104`.

> **Formal Scope (`[kernel-checked proof]`, `VrustcFormal.F1_1`):** In Lean 4 (`4.28.0-rc1`, axioms `{propext, Quot.sound}`, zero `sorry`, zero external imports), `mir_to_minissa_forward_bisim` and `mir_to_minissa_vc_transport` prove soundness of a decidable, single-pass, 1:1 block-lockstep translation-validation certificate checker (`checkMirToMiniSsaCert`) from a standalone core-MIR operational model (`MirBody` under `.fieldGranular` `deinitMovedPlace = true`) to a read-non-destructive register/block-parameter IR (`SsaBody`): for any certified `(mir, ssa, cert)` and any entry state satisfying `stateMatches`, MIR and MiniSSA agree identically at every fuel bound on both return values and `.outOfFuel` divergence, MIR never faults (`.undefined`/`.unsupported`), and partial-correctness postconditions transport soundly from MiniSSA to MIR (accompanied by a 4-block loop non-vacuity canary and four tightness counterexamples, including unconditional checker rejection of a loop back-edge use-after-move). This proof does **not** bridge to `joshlf/anneal`'s `Trusted.MirSemantics.lean` or `rustc-capture` ASTs, does **not** verify a lowering/synthesis algorithm (and its checker is intentionally incomplete for valid whole-pair local copies/moves, field-target binary operations, constant used-phi arguments, and CFG restructuring), does **not** prove termination, and models only pure wrapping `UInt64` operations (`add`/`sub`/`xor`/`bitAnd`), inhabited `.unit` ZSTs, and flat 2-field `(u64, u64)` pairs—excluding UB-bearing arithmetic, pointers/references, heap memory, aliasing/Tree Borrows, calls, unwinding, and non-`u64` return types.

---

## Applicability

- **Mechanized Proof Artifact:** `support/F1_1_MirToMiniSsa_DeinitMove_Proof.lean` (`2,449` lines, `58` public declarations, `35` theorems = `7` public + `28` private helpers), verified synchronously under Lean `4.28.0-rc1` (`leanprover/lean4@3b0f2862196c6a8af9eb0025ee650252694013dd`) with `-DElab.async=false -Ddebug.skipKernelTC=false` (`0` errors, `0` warnings, `14.112s`, zero `sorry`, zero `Classical.choice`, zero `Lean.ofReduceBool`).
- **Frozen Statement Integrity:** All `58` public declarations and all `7` public theorem signatures match the pre-proof frozen statement (SHA-256 `7c8fdf72a7817e69b86ee624222c23c18707a26ad531acf85354c1b2f27a38fa`, recorded in `support/F1_1_FROZEN.sha256`) byte-for-byte.
- **Empirical Grounding:** MIR phase comparison (`support/e1_2d_zerocopy_postcleanup_vs_opt.json`) measured on `rustc 1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`) compiling `zerocopy` (`0.9.0-alpha.1`) with `-Z dump-mir=runtime-post-cleanup|runtime-optimized`, and semantic conventions cross-checked against `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirSemantics.lean`).
- **Complementary Corpus Reports:** General multi-pass simulation diagrams live in `simulation-diagrams-and-multi-pass-compiler-correctness`; general unprojected scalar `MoveToCopy`/`StorageSafe` analysis lives in `mir-move-deinit-gvn-cse-and-guarded-preheader-licm-soundness`; full crate-wide `rustc 1.99.1` / `LLVM 23.1.1` IR statistics live in `rustc-postcleanup-mir-and-llvm-poison-freeze-ground-truth-census`.

---

## Findings

### 1. Empirical Grounding: `Runtime(PostCleanup)` vs. `Runtime(Optimized)` MIR on `zerocopy`

`Basis: execution (rustc 1.99.1 -Z dump-mir=runtime-post-cleanup|runtime-optimized on zerocopy 0.9.0-alpha.1 in support/e1_2d_zerocopy_postcleanup_vs_opt.json)`

Comparing the exact MIR phase captured by `joshlf/anneal`'s `rustc-capture` (`Runtime(PostCleanup)`) against `Runtime(Optimized)` on `zerocopy` confirms both why `PostCleanup` is a dramatically cleaner verification entry point and why field-granular move deinitialization cannot be deferred:

| Metric (`rustc 1.99.1`, `zerocopy`) | `Runtime(PostCleanup)` (`4,657` bodies) | `Runtime(Optimized)` (`4,449` bodies) | Architectural Significance |
| :--- | ---: | ---: | :--- |
| **Total basic blocks (`p50 / p95 / max`)** | `13,815` (`1 / 6 / 184`) | `13,186` (`1 / 11 / 131`) | `PostCleanup` keeps `p95` CFG size `1.83x` smaller (`6` vs. `11` BBs). |
| **Simple unprojected/no-unwind/no-rawptr bodies** | `74.02%` | `62.22%` | `+11.80 pp` higher simple-fragment admission at `PostCleanup`. |
| **Bodies containing `transmute`** | **`2.15%`** | **`31.02%`** | `14.4x` `transmute` jump in `Optimized` from inlining internal helpers. |
| **Bodies containing raw pointers (`&raw`)** | `7.77%` | `10.29%` | Lower raw-pointer exposure before MIR inlining. |
| **Bodies with partial-field moves (`M3`)** | **`0.26%` (`12` bodies)** | **`0.29%` (`13` bodies)** | Already present at `PostCleanup` (e.g. `TryFromBytes::try_read_from_prefix`). |
| **Unprojected move-then-read (`M1`/`M2`)** | `0` | `0` | Zero unprojected use-after-move observed in `zerocopy`. |

Concrete `Runtime(PostCleanup)` witness from `zerocopy.TryFromBytes-try_read_from_prefix.runtime-post-cleanup.after.mir` (`bb4`):
- Local `_4 : (core::mem::MaybeUninit<Self>, &[u8])` has field `(_4.0)` moved out, followed directly by `_3 = copy (_4.1: &[u8]);`.
- Under local-granular `deinitMovedPlace = true` (`locals[4] := liveUninitSlot ty`), reading `(_4.1)` spuriously faults `.undefined`. Under field-granular `deinitMovedPlace = true`, moving `(_4.0)` deinitializes only slot `0`, preserving `(_4.1)` as live and initialized.

### 2. Statement-First Formal Model (`VrustcFormal.F1_1`) and Checker Design

`Basis: formal proof (Lean 4.28.0-rc1 kernel check of support/F1_1_MirToMiniSsa_DeinitMove_Proof.lean)`

Rather than re-declaring a fake `namespace Trusted`, the formalization lives in `VrustcFormal.F1_1` with explicit fidelity notes against `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- **Operational MIR Semantics (`execMirLoop`):** Genuine fuel-indexed block-step CFG interpreter (no closed-form loop shortcuts) parameterized by `DeinitMode` (`.fieldGranular` vs. `.localGranular`) over `MirTy` (`.u64`, `.unit`, `.pairU64`), `LocalSlot` (`.dead` vs. `.live LivePayload`), `StorageLive`, `StorageDead` (enforcing `StorageDead 0 -> .error .unsupported` matching `Trusted/MirSemantics.lean:1391-1393`, `StackError.cannotMakeReturnPlaceDead`), `Assign` (`.use`, `.binaryOp`, `.mkPair` into `.local` or `.field`), `Goto`, `SwitchZero`, and `Ret`. `evalRvalue` threads updated `locals1` strictly left-to-right from `lhs` to `rhs` (matching `Trusted/MirSemantics.lean:145-148`), and `liveUninitSlot .unit = .live .zst` preserves inhabited ZSTs across moves (matching `Trusted/MirSemantics.lean:942-947`).
- **Target `MiniSSA` IR (`execSsaLoop`):** Register + block-parameter phi CFG IR where reads (`evalSsaArg`) never mutate registers (`SsaEnv := Nat → Option UInt64`), eliminating move-deinitialization state transitions from verification-condition generation. Edge phi bindings (`bindSsaParams env1 env1 tblk.params args`) evaluate all edge arguments against the fixed pre-edge environment `env1` so parallel swap cycles (e.g., `params = [6, 5], args = [.reg 5, .reg 6]`) are genuinely parallel once `tgtParams` are distinct.
- **Single-Pass Decidable Translation-Validation Checker (`checkMirToMiniSsaCert`):** Given a certificate `cert.blockEntryAbs : List (List AbsSlot)` assigning each basic block an abstract map (`.dead`, `.liveScalar (Option Nat)`, `.liveZst`, `.livePair (Option Nat) (Option Nat)`), `checkMirToMiniSsaCert` verifies every block `pc ∈ 0 ..< blocks.length`:
  1. Lockstep statement simulation (`checkBlockStmts`): checks left-to-right `checkAbsOperand` (clearing only the moved scalar local or moved struct field, leaving sibling fields and `.liveZst` intact), enforces `StorageDead 0` rejection, enforces inline register freshness (`regNotInAbs dstReg aCleared`), and enforces sequential `.mkPair` non-clobber (`r0 != r1 && a1' != .reg r0`).
  2. Edge phi validation (`checkEdge`): checks parameter distinctness (`tgtParams.eraseDups.length == tgtParams.length`), checks that **every** register in `edgeArgs` is live in `absEnd` (`!regNotInAbs rs absEnd`), and checks that every live target slot register is either validly rebound by `pairs` or preserved un-clobbered across the edge.

### 3. Three Kernel-Verified Defects Caught by Pre-Freeze Blind Statement Review

`Basis: formal proof (blind pre-freeze adversarial review before SHA-256 freeze)`

Applying a strict statement-first protocol (Draft → Blind Review → SHA-256 Freeze → Zero-`sorry` Proof → Final Over-Reading Audit) caught **three critical soundness and faithfulness defects** via concrete Lean-4-checked counterexamples before proving began:

| Defect ID | Failure Mechanism Caught Pre-Freeze | Concrete Counterexample Impact | Patch Frozen in `7c8fdf72a781` |
| :--- | :--- | :--- | :--- |
| **`B1` (Critical Soundness)** | `.mkPair op0 op1` lowers to two sequential SSA statements `.copy r0 a0' :: .copy r1 a1'`. Checking `regNotInAbs r0 aCleared` *after* clearing moved regs and slot `id` permitted `a1' == .reg r0` (both via `move` in `op1` and via self-read `_1 = mkPair(99, copy (_1.1))`). | Certified `(mir, ssa, cert)` returned `20` in MIR and `10` (or `99`) in MiniSSA, refuting both core theorems. | Added `a1' != .reg r0` and merged register freshness inline into single-pass `checkBlockStmts`. |
| **`B2` (Critical Soundness — Derived `False`!)** | `checkEdge` checked only phi parameters referenced in `tgtAbs`. An unused target phi parameter `p = 777` paired with an undefined edge argument `.reg 999` (`env 999 = none`) passed `checkMirToMiniSsaCert = true`. | `execMirLoop` returned `.ok (.ret 42)` while `execSsaLoop` returned `none` for all `fuel ≥ 1`; vacuous `hssa` for `P := fun _ => False` made `mir_to_minissa_vc_transport` imply **`False`**. | Added `edgeArgs.all (fun | .constU64 _ => true | .reg rs => !regNotInAbs rs absEnd)` to `checkEdge`. |
| **`B3` (Anneal Faithfulness)** | Draft permitted `StorageDead 0`, whereas real `Trusted/MirSemantics.lean:1391-1393` faults `.fault .unsupported` on return-place `StorageDead 0`. | Certified programs that fault `.unsupported` under Anneal's actual semantics. | Added `if id == 0` rejection in both `stepMirStmt` and `checkBlockStmts`. |

### 4. Kernel-Checked Theorems, Positive Non-Vacuity Canary, and Tightness Counterexamples

`Basis: formal proof (Lean 4.28.0-rc1 synchronous kernel check of support/F1_1_MirToMiniSsa_DeinitMove_Proof.lean)`

All `7` public theorems (backed by `28` private helper lemmas covering `getAt?`/`setAt?`, `eraseDups` `Nodup` preservation, `bindSsa` framing, `evalOperand` preservation, `checkBlockStmts_sound`, `bindSsaParams` parallel soundness, and `checkEdge_sound`) pass synchronous kernel checking (`-DElab.async=false -Ddebug.skipKernelTC=false`) with `0` `sorry`, `0` `Classical.choice`, and `0` `Lean.ofReduceBool`:

| Public Theorem | Exact Property Established | Kernel Axioms |
| :--- | :--- | :--- |
| **`mir_to_minissa_forward_bisim`** | Certified `(mir, ssa, cert)` + `stateMatches` at `pc` ⇒ `∃ out, execMirLoop .fieldGranular mir fuel pc locals = .ok out ∧ execSsaLoop ssa fuel pc env = some out` for all `fuel : Nat`. | `[propext, Quot.sound]` |
| **`mir_to_minissa_vc_transport`** | Under certification at `pc = 0`: (1) `MiniSSA` postcondition `P` transports to MIR, (2) bidirectional return equivalence `execMirLoop ... = .ok (.ret v) ↔ execSsaLoop ... = some (.ret v)`, and (3) total MIR fault-freedom `∀ fuel k, ... ≠ .error k`. | `[propext, Quot.sound]` |
| **`canary_counted_loop_cert_accepted`** | 4-block counted summation loop `sumLoopMir` with phi back-edges passes `checkMirToMiniSsaCert = true` and evaluates identically (`sum(5) = 15`) at `fuel = 20` in both IRs. | `[propext, Quot.sound]` |
| **`ce_operand_order_matters`** | `copy _0 + move _0` yields `.ok (.u64 84, [.live (.scalar none)])`, while `move _0 + copy _0` faults `.error .undefined` (matching real `libcore` M4 operand-ordering constraint). | `[propext, Quot.sound]` |
| **`ce_local_granular_breaks_sibling_field_move`** | `move (_0.0) + move (_0.1)` on `.pairU64` yields `.ok (.u64 30, ...)` under `.fieldGranular`, and faults `.error .undefined` under `.localGranular` (matching real `zerocopy` M3 witness). | `[propext, Quot.sound]` |
| **`ce_zst_move_remains_inhabited`** | Moving then copying `.unit` succeeds (`.ok (.unit, [.live .zst])`), while moving then copying `.u64` faults `.error .undefined`. | `[propext]` |
| **`ce_loop_backedge_use_after_move`** | 1-block self-loop moving `_1` without re-init succeeds at `fuel = 1` (`.ok .outOfFuel`), faults `.error .undefined` at `fuel = 2`, and is **unconditionally rejected** (`∀ ssa cert, checkMirToMiniSsaCert loopUseAfterMoveMir ssa cert = false`). | `[propext, Quot.sound]` |

### 5. Performance, Footprint, Comprehensibility, and Validation (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

- **`L1` (Authoring & Proof Effort):** `Basis: execution` — Full 5-stage statement-first pipeline (draft, blind pre-freeze review catching 3 bugs, SHA-256 freeze, `2,449`-line zero-`sorry` proof with `35` theorems, final over-reading audit) completed in a single engineering session.
- **`L2` / `L5` / `L6` (Elaboration & Checking Cost):** `Basis: execution` — Synchronous kernel replay (`lean -DElab.async=false -Ddebug.skipKernelTC=false`) of the entire `2,449`-line proof completes in **`14.112s` wall-clock** (`14.484s` user, `0.387s` sys) on `Lean 4.28.0-rc1` with zero external library imports (`Init` only).
- **`L3` / `L4` (Compile Latency & Generated Code Perf):** `not measured` — No lowering synthesizer or machine codegen is included in this formalization; this artifact verifies only the translation-validation certificate checker.
- **`C1` / `C2` (Auditability & Orthogonality):** Merging `freshRegsInStmts` into single-pass `checkBlockStmts` and dropping dead helpers reduced the trusted specification/checker surface to `~639` lines with zero external imports, zero metaprogramming, and zero `noncomputable` definitions.
- **`V1`–`V4` (Validation):**
  - `V1` (Non-vacuity & Tightness): Verified by `canary_counted_loop_cert_accepted` (4-block phi loop), 4 in-file tightness counterexamples, plus independent Stage-5 sensitivity checks confirming `.pairU64`, `.field`, `.unit`, `storageLive`, and `storageDead` branches in `checkMirToMiniSsaCert` are all reachable and non-vacuous.
  - `V2` (Adversarial Pre-Freeze & Post-Proof Audit): Blind pre-freeze review refuted two subtle soundness holes (`B1`, `B2`) before freeze; post-proof byte-equality audit verified `58/58` public declarations unchanged.
  - `V3` / `V4` (Weak Memory / Ecosystem Replay): `known not to apply` / `not examined` — sequential register/local model only; bridging to `joshlf/anneal`'s full `Trusted.MirSemantics.lean` and real `rustc-capture` outputs is the explicit next milestone.

---

## Boundaries

To prevent any over-claiming, the following five boundaries are **known not to apply** to `VrustcFormal.F1_1`:

1. **No Bridge to `joshlf/anneal` `Trusted.MirSemantics.lean` Yet (`not examined`):** `F1_1_MirToMiniSsa_DeinitMove_Proof.lean` has zero imports beyond Lean `Init` and does not prove a refinement bridge to `joshlf/anneal/trusted/lean/Trusted/MirAst.lean` or `MirSemantics.lean`. Several secondary fault-ordering details differ (e.g., `assign` destination-bounds check before RHS evaluation, `isPrimitiveReadableTy` check before uninit read, `StorageLive` re-initialization, and return local `_0` hardcoded to `.u64`).
2. **Excluded Rust Semantics (`known not to apply`):** Models only total wrapping `UInt64` ops (`add`, `sub`, `xor`, `bitAnd`), `.unit`, and flat 2-field `(u64, u64)` pairs. Excludes UB-bearing arithmetic (`div`/`rem`, shift overflow, checked/unchecked overflow), `bool`/multi-width integers/enums/`!`, casts, references/raw pointers (`&T`, `&mut T`, `*mut T`), heap memory, Tree Borrows / Stacked Borrows aliasing, function calls, `Drop`, `Assert`, multi-arm `SwitchInt`, and `panic=unwind` cleanup pads.
3. **Translation Validation Only — No Verified Lowering Synthesizer & Intentional Checker Incompleteness (`known not to apply`):** No `compile : MirBody → Option (SsaBody × SsaCert)` pass is verified. Furthermore, `checkMirToMiniSsaCert` is intentionally incomplete even within `VrustcFormal.F1_1`: it unconditionally rejects valid whole-pair `.copy`/`.move` local assignments, valid field-target `.binaryOp` assignments, constant phi arguments bound to used target slots, non-1:1 CFG restructuring, and bodies with uncertifiable unreachable blocks.
4. **Partial Correctness / Fuel-Indexed Lockstep Only (`known not to apply`):** Both theorems equate `.outOfFuel` with `.outOfFuel` at shared `fuel : Nat` and do not prove termination (though the bidirectional `↔` conjunct in `mir_to_minissa_vc_transport` transports any separately proved MiniSSA termination witness back to MIR at the same fuel). Safety holds only from initial states matching `stateMatches`.
5. **Read-Non-Destructive Registers, Not Global Syntactic SSA (`known not to apply`):** `MiniSSA` eliminates read/move-induced deinitialization, while permitting in-place register updates across loop-header phi bindings and intra-block reuse of dead registers (`regNotInAbs dstReg aCleared = true`).

---

## Evidence

| Artifact / Source | Pin / Checksum | Role |
| :--- | :--- | :--- |
| `support/F1_1_MirToMiniSsa_DeinitMove_Proof.lean` | SHA-256 `00402a51cf6e25c2d822ac791609d943100540bb46f9604674c8c405e34c687a` | Complete `2,449`-line, `35`-theorem zero-`sorry` Lean `4.28.0-rc1` proof (`[propext, Quot.sound]`, `14.112s`). |
| `support/F1_1_FROZEN.sha256` | SHA-256 `7c8fdf72a7817e69b86ee624222c23c18707a26ad531acf85354c1b2f27a38fa` | Frozen pre-proof statement digest verified byte-identical across all `58` public declarations. |
| `support/e1_2d_zerocopy_postcleanup_vs_opt.json` | Generated live (`2026-11-20`) | `rustc 1.99.1` `Runtime(PostCleanup)` (`4,657` bodies) vs. `Runtime(Optimized)` (`4,449` bodies) MIR census on `zerocopy`. |
| `joshlf/anneal` (`trusted/lean/Trusted/MirSemantics.lean`) | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Reference semantics for `deinitMovedPlace = true` (`L949-976`), `liveUninitSlot` (`L942-947`), left-to-right operand threading (`L145-148`), and `StorageDead 0` (`L1391-1393`). |
| `rust-lang/rust` (`rustc 1.99.1`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Upstream compiler used to dump real `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR. |
| `google/zerocopy` | `1962a9c0e3eda8a3a58387f61c70ddd2c396b118` | Real Rust crate exhibiting `TryFromBytes::try_read_from_prefix` partial-field move at `Runtime(PostCleanup)`. |
| `leanprover/lean4` (`v4.28.0-rc1`) | `3b0f2862196c6a8af9eb0025ee650252694013dd` | Kernel verifier executing synchronous replay (`-DElab.async=false -Ddebug.skipKernelTC=false`). |

---

## Revalidation

1. **Replay Lean 4 kernel check (zero external dependencies beyond `Init`):**
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/F1_1_MirToMiniSsa_DeinitMove_Proof.lean
   ```
   Confirm exit code `0`, zero errors/warnings, and exact `#print axioms` output strictly within `[propext, Quot.sound]`.
2. **Re-verify `Runtime(PostCleanup)` partial-field move witnesses on `rustc 1.99.1`:**
   ```bash
   RUSTC_BOOTSTRAP=1 cargo +1.99.1 rustc --lib --release -- \
     -Z "dump-mir=runtime-post-cleanup|runtime-optimized" \
     -Z dump-mir-exclude-alloc-bytes -Z dump-mir-exclude-pass-number
   ```
   Inspect `zerocopy.TryFromBytes-try_read_from_prefix.runtime-post-cleanup.after.mir` for `move (_4.0)` followed by `copy (_4.1)`.
3. **Re-audit upon upstream `joshlf/anneal` changes:** Revisit whenever `trusted/lean/Trusted/MirSemantics.lean` extends `Place.projection` to struct/tuple fields (verify field/byte-granular move deinitialization matches) or when `VrustcFormal.F1_1` is bridged directly onto `Trusted.MirAst` and `Trusted.MirSemantics`.
