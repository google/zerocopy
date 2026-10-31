# Syntax-Directed Symbolic Execution (`wpX86`), In-Place Canonical Cut-Points (`wpX86Cut`), and Inductive Loop Verification in Anneal

## Summary

In `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`),
`trusted/rustc-capture/src/proof_gen.rs` matches 10 hardcoded MIR AST shapes
and dispatches to 1,100+ lines of manual, instruction-by-instruction lemmas in
`theory/Anneal/MirLemmas.lean` (up to 132 lines for a 2-branch `max_usize`). Our
mechanizations in `support/SymbolicVCGenProbe.lean` (1,594 lines, 100
declarations, 54 theorems, 0 `sorry`) and `support/LoopAndJoinVCGenProbe.lean`
(149 declarations, 75 theorems, 0 `sorry`) show that syntax-directed weakest
precondition generation (`wpX86`), cut-point join merging (`wpX86Cut` +
`canonMemUpTo`), and unbounded loop verification (`wpX86_loop_sound`) can live
**100% in `theory/` with zero changes to `trusted/lean/`**:

1. **Exact Root-Cause Diagnosis of Symbolic Reduction Blockers in `evalX86Step`:**
   In `Trusted/X86Semantics.lean`, `evalX86Step` is already deterministic and
   reduces by kernel `whnf`/`rfl` on all 9 `X86Instr` constructors and 7 of 9
   `X86Term` constructors once `s.mem` is concrete. Symbolic execution gets
   stuck at only three points:
   - **Abstract `s.mem` in `initX86State`:** `initX86State` constrains `s.mem :
     Nat → Option X86Val` existentially via `argsMatchStack`. Because `s.mem` is
     a free function variable rather than a concrete `updateSlot` chain, `s.mem
     1` cannot reduce by `whnf`, forcing manual `if`-chain rewrites at every
     read.
   - **Symbolic branch condition in `X86Term.jccBool`:** `evalX86Term` matches
     on `some (.boolVal false, mem')` vs `some (.boolVal true, mem')` before
     returning `.step ()`, blocking on `Bool.rec` when the condition is symbolic
     (`decide (a < b)`).
   - **Symbolic type-size equality in `X86Term.repMovsbJmp`:** `evalRepMovsb`
     guards `.step ()` with `if decide (srcSz = dstSz)` and `if decide (vSz =
     srcSz)`, which cannot reduce by `rfl` when `tySizes : Nat → Nat` is
     universally quantified.
2. **Universal Entry-State Canonicalization (`forallTypedArgs`) and Syntax-Directed `wpX86`:**
   `forallTypedArgsAux` and `initX86State_canonical` unpack each `X86Ty` in
   `body.argTys` into its unique `X86Val` constructor under `v.hasTy` and
   substitute the concrete `updateSlot (... (updateSlot (fun _ => none) 1 (some
   v₁)) ...)` chain for `s.mem` via `funext`. `wpX86` (45 lines) delegates all 9
   `X86Instr` cases directly to `evalX86Instr` and 7 of 9 `X86Term` cases
   (including `.call1` frame pushing and `.ret` frame popping) to `evalX86Term`,
   intercepting only `.jccBool` (splitting into `(b = false → wpX86 ...) ∧ (b =
   true → wpX86 ...)` so concrete `bb` and `ip := 0` reduce immediately in both
   arms) and `.repMovsbJmp` (emitting `srcSz = dstSz ∧ vSz = srcSz ∧ wpX86 ...`).
   Moreover, because `SafeAndEnsures P (.terminated .unwind)` is `True` for all
   `P`, `wpX86` already maps `.abortPanic` branches to `True`, allowing
   `constSucceeds_of_wpX86` to extract post-monomorphization error (PME)
   `ConstSucceeds` obligations in 1 line without a separate necessity proof
   (`⟨fun _ => True.intro, of_decide_eq_true⟩`).
3. **In-Place Finite-Support Canonical Memory Spine (`canonMemUpTo` and `canonState`) on `Trusted.X86State`:**
   Instead of duplicating `X86Semantics.lean` over a separate state type,
   `canonMemUpTo B m` normalizes `s.mem : Nat → Option X86Val` directly in place
   on `Trusted.X86State` up to `B = body.slotCount`:
   ```lean
   noncomputable def canonMemUpTo :
       Nat → (Nat → Option X86Val) → (Nat → Option X86Val)
     | 0, _ => fun _ => none
     | k + 1, m => updateSlot (canonMemUpTo k m) k (m k)

   noncomputable def canonState (B : Nat) (s : X86State) : X86State :=
     { s with mem := canonMemUpTo B s.mem }
   ```
   For any concrete `B`, `canonState B s` samples `s.mem 0 ..< B` by kernel
   `whnf` and builds a fixed-shape `updateSlot` spine, erasing all overwritten
   or deallocated scratch-slot closures so converging CFG paths become
   definitionally equal (`rfl`). Defining `MemSubsumed cm m : Prop := ∀ i v, cm
   i = some v → m i = some v` yields an **unconditional** simulation
   `canonState_subsumed : ∀ B s, StateSubsumed (canonState B s) s` and
   `evalX86Step_subsumed` across all instructions and terminators.
4. **Cut-Point `wpX86Cut` ($O(D)$ Diamond Joins) and Strong-Induction Loop Verification (`wpX86_loop_sound`):**
   `wpX86Cut fuel rootBody cutBb s Cut P` executes at least one small-step
   transition from `s` before stopping when a terminator lands at `(cutBb, ip =
   0, curBody = none)`, where it emits `Cut (canonState rootBody.slotCount s')`.
   Because at least one transition occurs before reaching `cutBb`, the remaining
   prefix fuel strictly decreases (`n' < n` via `reachesPrefix_of_step_lt`). By
   strong induction on the `ReachesPrefix` fuel budget `n : Nat`
   (`nat_strong_ind`), `reachesPrefix_of_loop_invariant` and `wpX86_loop_sound`
   prove that a single-iteration `wpX86Cut` obligation at `headerBb` implies
   `SafeAndEnsures P out` for **every** prefix budget `n : Nat`, verifying
   runtime-trip-count `while` loops (`countUpLoopBody`, `sumLoopBody`,
   `nonZeroLoopBody`, `loopWithInternalDiamondBody`) and $O(D)$ chained diamonds
   (`asymmetricDiamondJoinBody`, `doubleDiamondChainBody`) in 4–20 lines each.

## Applicability

These findings apply to:

- **Anneal (`joshlf/anneal`):** Commit
  `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`), specifically
  `trusted/lean/Trusted/StepResult.lean`,
  `trusted/lean/Trusted/X86Ast.lean`, `trusted/lean/Trusted/X86Semantics.lean`,
  `trusted/audit/TrustedBoundary.lean`, `trusted/rustc-capture/src/proof_gen.rs`,
  and `theory/Anneal/MirLemmas.lean`.
- **Lean 4 (`leanprover/lean4`):** Version `v4.34.1` at commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`prelude`-only mode with `import
  Init.NotationExtra` and `import Init.Classical`).

## Findings

### 1. Entry-State Canonicalization (`forallTypedArgs`) and Syntax-Directed `wpX86`

In `Trusted/X86Semantics.lean:160-175`, `initX86State` defines entry states
relationally (`s.mem 0 = none ∧ argsMatchStack s.tySizes body.argTys s.mem`). In
`support/SymbolicVCGenProbe.lean:88-265`, `buildArgMem` constructs the concrete
entry memory for any argument list, and `forallTypedArgsAux` unpacks each
`X86Ty` into its unique `X86Val` constructor while substituting `buildArgMem`
into the goal via `funext`:

```lean
noncomputable def forallTypedArgsAux (tySizes : Nat → Nat) :
    List X86Ty → (List X86Val → Prop) → Prop
  | [], k => k []
  | .usize :: tys, k =>
      ∀ a : Nat, forallTypedArgsAux tySizes tys (fun vs => k (.word64 a :: vs))
  | .bool :: tys, k =>
      ∀ b : Bool, forallTypedArgsAux tySizes tys (fun vs => k (.boolVal b :: vs))
  | .unit :: tys, k =>
      forallTypedArgsAux tySizes tys (fun vs => k (.unit :: vs))
  | .adt id :: tys, k =>
      ∀ a : Nat, forallTypedArgsAux tySizes tys (fun vs => k (.adt id (.word64 a) :: vs))
  | .param idx :: tys, k =>
      ∀ bits : Nat, forallTypedArgsAux tySizes tys
        (fun vs => k (.bytes (tySizes idx) bits :: vs))
  | .refParam _ :: tys, k =>
      ∀ slot : Nat, forallTypedArgsAux tySizes tys
        (fun vs => k (.stackPtr slot :: vs))
```

Once `s.mem` is replaced by `buildArgMem`, every slot lookup `s.mem idx`
(including out-of-bounds slots `idx > argTys.length`) reduces to `some v_idx` or
`none` by pure kernel `whnf`/`rfl`.

`wpX86` (`SymbolicVCGenProbe.lean:295-345`) then computes a sufficient
verification condition for `SafeAndEnsures P out` across all `n : Nat` by
recursing on `fuel : Nat`:

```lean
noncomputable def wpX86 :
    Nat → X86Body → X86State → (X86Val → Prop) → Prop
  | 0, _, _, _ => False
  | fuel' + 1, rootBody, s, P =>
      let activeBody := match s.curBody with | none => rootBody | some b => b
      match activeBody.blocks[s.bb]? with
      | none => False
      | some blk =>
          match blk.instrs[s.ip]? with
          | some instr =>
              match evalX86Instr s instr with
              | .step s' => wpX86 fuel' rootBody s' P
              | .terminated (.normal ret) => P ret
              | .terminated .unwind => True
              | .failed _ => False
          | none =>
              match blk.term with
              | .jccBool cond falseTarget trueTarget =>
                  match evalX86Operand s.mem cond with
                  | some (.boolVal b, mem') =>
                      (b = false →
                        wpX86 fuel' rootBody
                          { s with mem := mem', bb := falseTarget.index, ip := 0 } P) ∧
                      (b = true →
                        wpX86 fuel' rootBody
                          { s with mem := mem', bb := trueTarget.index, ip := 0 } P)
                  | _ => False
              | .repMovsbJmp dst srcTy dstTy ptrOp target => ...
              | term =>
                  match evalX86Term rootBody s term with
                  | .step s' => wpX86 fuel' rootBody s' P
                  | .terminated (.normal ret) => P ret
                  | .terminated .unwind => True
                  | .failed _ => False
```

| Benchmark Suite | `MirLemmas.lean` Lines | `SymbolicVCGenProbe.lean` Lines | AST-Shape Invariance Verified |
| :--- | :---: | :---: | :--- |
| **`id` (`Copy`, `Move`, `const`, `idMultiTempBody k`)** | ~140 lines (20–34 each) | **18 lines total** (1–3 each) | `idMultiTempBody k` has parametric `slotCount := k`, 3 temp copies, interleaved `nop`s, and reordered `deallocSlot`; proved by `(fun _ _ => rfl)`. |
| **Binary ALU (8 ops) & Cmp (6 ops) + `binOpExtraTempsBody`** | ~295 lines (65–82 each) | **32 lines total** (4–8 each) | `binOpExtraTempsBody` has `slotCount = 9` and 2 basic blocks (`jmp`); proved by `(fun _ _ _ => ensuresBinOp_of_eq rfl rfl rfl)`. |
| **`max_usize` (4-block diamond) & `clamp_usize` (6-block 3-way branch)** | 132 lines (`max_usize` `RetLibInv` only) | **3 lines** (`max_usize` `RetLibInv`), **9 lines** (full `if`/`else` spec); **5 / 16 lines** (`clamp_usize`) | Proves full functional specifications `ret = .word64 (if a < b then b else a)` and `ret = .word64 (if x < lo then lo else if hi < x then hi else x)`. |
| **PME `sizeEqConst` (`slotCount = 5` & `6`), `transmute_checked`, `outer_transmute` (`call1`)** | 262 lines (64 + 95 + 103) | **15 lines total** (1 + 1 + 6 + 7) | Identical 1-line proof `constSucceeds_extract 20 h ⟨fun _ => True.intro, of_decide_eq_true⟩` verifies both `slotCount = 5` and `slotCount = 6`. |
| **`NonZeroUsize` Library (`make_nonzero`, `new_unchecked`, `get_unchecked_nonzero`, 2-call `sanitize_nonzero`)** | 206 lines (3 fns) | **16 lines total** (4 fns: 2 + 3 + 3 + 8) | Proves end-to-end 4-function `CrateTheorem` (`prove_nonzero_four_fn_crate`) with `sanitizeNonZeroBody` chaining two `call1` calls across 3 basic blocks. |

Basis: **source** (`Trusted/X86Semantics.lean`, `theory/Anneal/MirLemmas.lean`)
+ **execution** (`support/SymbolicVCGenProbe.lean`, `support/ReplayAudit.lean`).

### 2. In-Place Canonical Memory Normalization (`canonMemUpTo`) and Cut-Point `wpX86Cut`

When a function contains $D$ sequential diamond branches or a runtime loop back-edge,
unfolding `.jccBool` to termination duplicates the post-join continuation $2^D$
times, and raw `updateSlot` chains from asymmetric branches cannot unify by
`rfl`. In `support/LoopAndJoinVCGenProbe.lean` (Sections 1–3), we solve both
problems directly on `Trusted.X86State` without introducing a second operational
semantics:

1. **In-Place Spine Rebuild (`canonMemUpTo` and `canonState`):**
   `canonMemUpTo B m` evaluates `m 0`, `m 1`, ..., `m (B - 1)` by kernel `whnf`
   and rebuilds a canonical `updateSlot` spine of length `B` rooted at `fun _ =>
   none`. Any temporary slots $< B$ allocated, mutated, and deallocated inside a
   branch or loop body evaluate to `none` and collapse into identical
   `updateSlot ... k none` nodes by `rfl`.
2. **Unconditional Forward Simulation (`StateSubsumed`):**
   Because `evalX86Operand`, `evalX86Instr`, and `evalX86Term` only require that
   every `some v` read from the canonical memory is also `some v` in the runtime
   memory (`MemSubsumed cm m : ∀ i v, cm i = some v → m i = some v`),
   `canonState_subsumed : ∀ B s, StateSubsumed (canonState B s) s` holds
   **unconditionally** for every `B : Nat` and `s : X86State` (even without
   requiring slots $\ge B$ to be `none`), and `evalX86Step_subsumed` lifts every
   non-failing step of `cs` to `s`.
3. **Cut-Point Weakest Precondition (`wpX86Cut` and `wpX86Cut_sound`):**
   `wpX86Cut fuel rootBody cutBb s Cut P` steps at least once from `s` and checks
   at each subsequent block transition (`ip = 0`, `curBody = none`) whether
   `s'.bb = cutBb`. If so, it stops unfolding and emits `Cut (canonState
   rootBody.slotCount s')`; otherwise it continues unfolding up to `fuel`.
   `wpX86Cut_reachesCutOrTerm` proves that for every `ReachesPrefix` derivation
   of length `n`, either the prefix already satisfies `SafeAndEnsures P out`, or
   execution safely reaches an intermediate state `s'` at `cutBb` with
   strictly smaller remaining fuel `n' < n` such that `StateSubsumed (canonState
   rootBody.slotCount s') s'` and `Cut (canonState rootBody.slotCount s')`.

Basis: **execution** + **derived** (`support/LoopAndJoinVCGenProbe.lean`
Sections 1–3).

### 3. Strong-Induction Loop Verification under `ReachesPrefix` (`wpX86_loop_sound`)

Why can runtime-trip-count `while` loops (whose step count depends on a runtime
parameter `n : Nat` or `UInt64`, or even potentially non-terminating loops) be
verified under `ReachesPrefix` without a termination ranking function when
proving `WellFormed` or partial-correctness `Ensures*` specs?

In `Trusted/StepResult.lean` and `Trusted/X86Semantics.lean`:

- Every query `q : ExecQuery X86State` supplies a **finite** step budget `q.steps
  : Nat`.
- Whenever `q.steps` runs out while the loop is still executing, `ReachesPrefix`
  produces `out.outcome = .running`.
- For `.running`, `PrefixOutcome.isSafe .running` is `True` and `.running =
  .terminated (.normal ret)` is `False`, so `SafeAndEnsures P .running` is
  `True`!

Therefore, in `support/LoopAndJoinVCGenProbe.lean` (Section 4),
`reachesPrefix_of_loop_invariant` and `wpX86_loop_sound` apply strong induction
(`nat_strong_ind`) on the prefix step budget `steps : Nat`:

- Given a parameterized family of canonical loop-header states `stateAt : α →
  X86State` at `headerBb` and a loop invariant `Inv : α → Prop`, if for every
  `x : α` satisfying `Inv x`, a single finite-fuel `wpX86Cut iterFuel body
  headerBb (stateAt x) (IndexedCut stateAt Inv) P` holds (meaning one iteration
  from `stateAt x` either exits safely to `.ret` satisfying `P`, or steps in $k
  \ge 1$ safe transitions back to `headerBb` where `canonState body.slotCount
  s'` equals `stateAt x'` for some `x'` satisfying `Inv x'`), then because $k
  \ge 1$ consumes at least 1 unit of prefix fuel (`n' < steps`), the strong
  induction hypothesis immediately discharges the remaining prefix `n'`!

| Verified Benchmark in `LoopAndJoinVCGenProbe.lean` | CFG Structure | Verified Theorems | Proof Size |
| :--- | :--- | :--- | :---: |
| **`countUpLoopBody`** | `while i < n { i = i + 1 } return i` (4 blocks, back-edge `bb3 -> bb1`) | `countUpLoopBody_retLibInv`, `countUpLoopBody_wellFormed`, `countUpLoopBody_ensures_eq_arg` (`ret = .word64 n`), `prove_count_up_loop_crate` | 4–9 lines |
| **`sumLoopBody`** | 2-arg loop accumulating `x` into `acc` `n` times while mutating/deallocating scratch slots `5, 6, 7` every iteration | `sumLoopBody_retLibInv`, `sumLoopBody_ensures_product` (`ret = .word64 (x * n)`), `prove_sum_loop_crate` | 5–20 lines |
| **`nonZeroLoopBody`** | `NonZeroUsize` loop extracting `x.0`, incrementing in a loop, and wrapping `.adt 0` under custom `nonZeroLibInv` | `nonZeroLoopFn_retLibInv`, `prove_non_zero_loop_crate` | 7 lines |
| **`loopWithInternalDiamondBody`** | Loop containing an internal `if i < k / else` diamond mutating asymmetric scratch slots `6` vs `7, 8` before jumping to `bb1` | `loopWithInternalDiamondBody_retLibInv`, `loopWithInternalDiamondBody_ensures_ge` (`ret ≥ n`), `prove_loop_with_internal_diamond_crate` | 8–12 lines |
| **`asymmetricDiamondJoinBody`** | `bb0 -> (bb1 \| bb2) -> bb3` (`bb1` uses scratch slot `4`; `bb2` uses scratch slots `5, 6`; both merge by `rfl` at `bb3`) | `asymmetricDiamondJoinBody_ensures`, `asymmetricDiamondJoinBody_retLibInv` | 4 lines |
| **`doubleDiamondChainBody`** | 2-stage chained diamond `bb0 -> (bb1 \| bb2) -> bb3 -> (bb4 \| bb5) -> bb6` verified via two `byIndexedCut` stages ($O(D)$) | `doubleDiamondChainBody_retLibInv`, `doubleDiamondChainBody_ensures_gt20` (`ret > 20`), `prove_double_diamond_chain_crate` | 9–12 lines |

Running `support/ReplayAudit.lean` confirms that all `1,959` non-foundation
declarations (`1,810` from `Trusted` + `Anneal` plus `149` from
`LoopAndJoinVCGenProbe`) replay in the Lean 4.34.1 kernel in `1,161 ms` (`521 ms`
incremental for `LoopAndJoinVCGenProbe`), with zero `isUnsafe`, `isPartial`, or
`isAxiom` constants and transitive axiom closure `[Quot.sound, propext]`.

Basis: **execution** (`support/LoopAndJoinVCGenProbe.lean` Sections 4–7,
`support/ReplayAudit.lean`).

## Boundaries

- **Known not to apply:** `wpX86_loop_sound` proves `SafeAndEnsures P out` over
  all `ReachesPrefix` queries (guaranteeing no `.failed` UB at any step depth
  and guaranteeing `P ret` whenever `.terminated (.normal ret)` is reached),
  which matches every specification constructor in `Trusted/X86Semantics.lean`.
  Proving total liveness (that there *exists* a finite step budget $N$ at which
  `.terminated` is reached) additionally requires a well-founded ranking measure
  on the loop header family `α`.
- **Known not to apply:** Recursive `Prop`-valued definitions in `theory/`
  (`wpX86`, `wpX86Cut`, `necX86Normal`, `forallTypedArgsAux`, `canonMemUpTo`)
  must still carry `noncomputable def` in Lean `v4.34.1` so `addPreDefinitions`
  does not emit `<fn>._unsafe_rec` (`isPartial = true`).
- **Not examined:** Mutual recursion across `call1` cycles (recursive function
  calls rather than intraprocedural CFG back-edges), which can be handled by the
  same strong induction on `ReachesPrefix` fuel at `.call1` boundaries.

## Evidence

- **Anneal `mir-to-x86` prototype (`joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`):**
  - `trusted/lean/Trusted/X86Semantics.lean:1-290` (`evalX86Operand`, `evalX86Instr`, `evalX86Term`, `evalX86Step`, `initX86State`, `ConstSucceeds`).
  - `theory/Anneal/MirLemmas.lean:1-1122` (baseline manual instruction-by-instruction proofs).
  - `trusted/rustc-capture/src/proof_gen.rs:1-420` (baseline AST-shape matchers).
- **Preserved package artifacts (`reports/anneal-mir-to-x86-symbolic-vcgen-cutpoints-and-loops/support/`):**
  - `support/SymbolicVCGenProbe.lean` (`sha256: 62b694386ee6f3a3da3de1bf88d74c2ce3cc368a2d6534fd71bf1f20e7eea155`, 1,594 lines, 100 declarations, 54 theorems, 0 `sorry`).
  - `support/LoopAndJoinVCGenProbe.lean` (`sha256: 3c9b2aee3b7028c6824b494bd187e412298840727963f18728accd6041a21d4c`, 149 declarations, 75 theorems, 0 `sorry`).
  - `support/ReplayAudit.lean` (`sha256: d640d0dc042102f123d0ac5c775bfb13bdccbab7a10949c7a04fb4455a19ed62`, full kernel replay and `TrustedBoundary` check).

## Revalidation

With the `mir-to-x86` `.olean` build directory on `LEAN_PATH`, compile both
probes and run `ReplayAudit.lean` under Lean 4.34.1:

```bash
LEAN_PATH=/path/to/anneal/build/lean \
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
  -o /tmp/SymbolicVCGenProbe.olean support/SymbolicVCGenProbe.lean
LEAN_PATH=/path/to/anneal/build/lean \
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
  -o /tmp/LoopAndJoinVCGenProbe.olean support/LoopAndJoinVCGenProbe.lean
LEAN_PATH=/tmp:/path/to/anneal/build/lean \
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ReplayAudit.lean
```
