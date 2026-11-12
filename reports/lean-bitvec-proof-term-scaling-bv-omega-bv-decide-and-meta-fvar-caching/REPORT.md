# Lean 4 `BitVec` Proof-Term Scaling, `CheckRange`/`bv_omega`/`bv_decide` Kernel Replay Cost, Closed `Bool` Reflection with Direct GMP Builtins, and `Lean.Meta` `hasFVar` Caching

## Summary

Across Lean `v4.29.0` (`leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740`) and Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), primary-source analysis and empirical measurement of kernel `ConstantInfo.thmInfo.value` DAGs, unshared expression trees, `.olean` byte footprints, elaboration wall time, and `Environment.toKernelEnv.replay` cost establish the scaling laws and `TrustedBoundary` admissibility rules for 64-bit bitvector and mixed bitwise-arithmetic verification in Anneal (`joshlf/anneal@af3c1e99c0a7410aa63522fc3888d34c32c13175` and `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`):

1. **Four Compounding Causes of the `5.91 MB` (`255.14M` Unshared Tree-Node) Blowup in `Endianness.lean`**:
   - Although the 70-line `Endianness.lean` fixture in Starnix `apply_endianness` (`joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`) does not invoke `bv_omega` directly, it discharges 11 `BitVec 64` byte-swap and negative-test theorems via `BitVec.eq_of_getLsbD_eq`, a 64-way proposition conjunction `CheckRange 64`, and `simp` over `BitVec.getLsbD_*` lemmas, producing a **`5,909,768`-byte (`5.91 MB`) `.olean`** (`5,708,160` B in `v4.29.0`) with **`220,511` DAG nodes**, **`255,140,486` unshared tree nodes** (depth `425`), `2.10 s` (`v4.34.1`) / `2.81 s` (`v4.29.0`) single-file compile time, and **`489.13 ms` (`v4.34.1`) / `556.50 ms` (`v4.29.0`)** in `toKernelEnv.replay`:
     1. *Free-variable simproc bailout (`BuiltinSimprocs/BitVec.lean:72-78`)*: `BitVec.reduceGetLsb` calls `Nat.fromExpr? e.appArg!`, which returns `none` whenever the bit index (`i - s` or `s + i`) contains a free variable `i`, preventing symbolic reduction of `(swap64 x).getLsbD i` before index enumeration.
     2. *CPS-shifted `CheckRange` lambda-addition tower*: Defining `CheckRange (n + 1) p = p 0 ∧ CheckRange n (fun i => p (i + 1))` wraps `p` in $k$ nested lambdas and substitutes `0 + 1 + ... + 1` ($k$ times) at step $k \in [0, 63]$. Across 8 byte lanes, `simp` constructs $\sum_{k=0}^{63} 19k \approx 38{,}304$ unary addition congruence steps; without `simp`, the 63-deep lambda tower exceeds Lean's default `maxRecDepth` (`512`).
     3. *`And.intro` proposition-type embedding and `Bool.or` left-strictness*: Even with top-down `CheckRange 64` (`p n ∧ CheckRange n p`), `Eq.symm rfl` per index, and a factored `Bool.or` helper `getLsbD_or_laneL`/`R` (`EndiannessCheckRangeOpt.lean`), 64 nested `@And.intro P Q` constructors embed the unreduced 8-lane proposition `P` and tail conjunction `Q` in their type arguments (`8,782` DAG nodes and `9,504,075` unshared tree nodes for `swap64_exact` alone).
     4. *Unfactored `swap*_involutive` ($64 \times 8 \times 8$ expansion) vs. `omega` Euclidean div/mod linearization*: Re-running `CheckRange 64` + `simp` on `swap64 (swap64 x)` expands each of the 8 outer lanes into 8 inner lanes across 64 bit indices (`22,865` DAG nodes, `64,813,809` tree nodes, `98.81 ms` replay). Factoring `swap*_involutive` through `swap*_bits` and `reverseByteIndex_involutive` avoids the $64 \times 64$ expansion, but proving `reverseByteIndex_involutive` via `omega` still emits a `3,423`-DAG-node (`2,022,805`-tree-node, `44.85 ms` replay) auxiliary proof due to Euclidean `/ 8` and `% 8` linearization.
2. **Parameter-Free Closed `Bool` Reflection + Direct C++ GMP Builtins (`EndiannessDropIn.lean`: `20.86x` Smaller `.olean`, `915.2x` Fewer Tree Nodes, `9.06x` Faster Kernel Replay, `0` Extra Axioms)**:
   - Factoring the symbolic bit reader `f := x.getLsbD : Nat → Bool` out of the 8-lane shift-mask cascade via `evalLanes f lanes` and `checkLanes lanes target` reduces `swap8_exact`..`swap64_exact` to 1–7 symbolic `rw` steps followed by closed `Bool` `rfl` (`845` DAG nodes and `115,869` tree nodes for `swap64_exact`, vs. `120,035` DAG nodes and `165,305,787` tree nodes in `EndiannessBaseline`).
   - *Critical `Decidable` / `instBEqOfDecidableEq` Bottleneck in Kernel `rfl`*: In `src/Init/Prelude.lean:1872-1878, 2089-2105` and `src/Init/Data/Nat/Bitwise/Basic.lean:133-134`, neither `decide (a < b)` (`Nat.decLt`) nor `a != 0` inside `Nat.testBit` (`instBEqOfDecidableEq`) is a direct C++ kernel builtin. During kernel `rfl`, both unfold `Decidable.decide`, `Nat.decLe`, `Nat.decEq`, and `dite`, constructing and discarding `isTrue (Nat.le_of_ble_eq_true ...)` and `isTrue (Nat.eq_of_beq_eq_true ...)` proof terms on every bit evaluation. Replacing `decide (a < b)` with `Nat.ble a.succ b` (`decide_lt_eq_ble`) and `m.getLsbD idx` with `testBitFast m.toNat idx := !Nat.beq (Nat.land 1 (Nat.shiftRight m.toNat idx)) 0` (`getLsbD_eq_testBitFast`) routes kernel WHNF directly into C++ GMP builtins (`Nat.ble`, `Nat.beq`, `Nat.land`, `Nat.shiftRight`), cutting `EndiannessDropIn.lean`'s kernel replay time from `124.28 ms` down to **`54.01 ms` (`9.06x` faster than `EndiannessBaseline`'s `489.13 ms`)** and `.olean` size from `5,909,768` B to **`283,240` B (`20.86x` smaller)** with **zero extra axioms**.
   - Defining proof-only reflection combinators (`evalLanes`, `allInactive`, `checkLanes`, `checkNatPred`) via `List.rec` / `Nat.rec` as `noncomputable def` and unfolding them via `change` rather than `simp` suppresses lazy synthesis of `.eq_def`, `.eq_1`, `.match_1`, `._f`, `._sunfold`, and `._unsafe_rec` constants (`34` constants vs. `84` in `EndiannessBaseline`).
3. **`bv_decide` vs. `bv_normalize` and `TrustedBoundary.lean` Axiom Auditing (`_native.bv_decide.ax`)**:
   - In both `v4.29.0` (`98dc76e3c0a9`) and `v4.34.1` (`5045d0056413`), `bv_decide` (`Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean:119-165`) runs `bv_normalize` first. If `bv_normalize` (`Sym.Simp` AC-normalizer + `extractLsb'` rules) closes the goal by rewriting, `0` native axioms are emitted. However, `bv_normalize` rewrites bitwise OR `a ||| b` into De Morgan form `~~~(~~~a &&& ~~~b)`, which blocks pure rewrite closure on multi-lane shift-and-OR expressions (`swap16`..`swap64`, `getDstReg (setDstReg raw val)`).
   - Whenever `bv_normalize` leaves a residual goal, `bv_decide` bit-blasts to AIG, runs CaDiCaL, and calls `LratCert.toReflectionProof` (`Frontend/BVDecide/ReifiedBVLogical.lean:133-155`) $\to$ `Lean.Meta.mkAuxTheorem` + `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean:37-87`). Unlike `native_decide` (which references the global `Lean.ofReduceBool` axiom), `nativeEqTrue` registers a **fresh per-invocation `Declaration.axiomDecl`** named `<Decl>._native.bv_decide.ax_1_5`. Anneal's `trusted/audit/TrustedBoundary.lean` rejects these proofs at two independent gates: `targetAudit` (`lines 553-570`) enforces an exact 3-axiom allowlist (`Classical.choice`, `Quot.sound`, `propext`), and `classifyConstant` (`lines 820-859`) rejects any local `.axiomInfo` declaration outside `Trusted.*`.
4. **Mixed 64-Bit Bitwise + Integer Abstract-Domain Proof Strategies (`MixedBitVecArithProbe.lean`)**:
   - Across four representative Starnix eBPF verification families (`U64ScalarValueData::bitand_scalar` known-bits, `EbpfInstruction` 64-bit bitfield lens and `< 16` register bound, `U64Range::add_range` wrapping addition vs. no-overflow bounds, and `reverseByteIndex` Euclidean div/mod), `TrustedBoundary`-compliant proof strategies outperform both `bv_omega` and `bv_decide`:
     - *Pure bitwise Boolean algebra (`bitand_wf_cases`)*: `BitVec.eq_of_getLsbD_eq` + `cases` on the 4 bit atoms replays in **`3.11 ms`** (`1,861` DAG nodes, `0` extra axioms, width-parametric) vs. `5.58 ms` for `bv_decide` (which emits `_native.bv_decide.ax_1_5`).
     - *Bitfield `< 2^k` bound (`dstReg_lt_16_algebraic`)*: `BitVec.toNat_and` + `Nat.and_le_right` produces **`135` DAG nodes (`1,483` tree nodes)** and replays in **`0.41 ms`** (`5.5x` faster than `bv_decide`).
     - *Packed 64-bit bitfield round-trip (`getDstReg_setDstReg_reflect`)*: Combining `checkNatPred_sound 64` with 4-way Boolean truth-table reflection `checkAllBool2_sound` proves `getDstReg (setDstReg raw val) = val &&& 0x0f#64` in **`740` DAG nodes (`29,988` tree nodes)** with **`0` extra axioms**.
     - *Wrapping `BitVec 64` addition under no-overflow bounds (`u64_add_range_mod_elim` vs. `bv_omega`)*: Calling `bv_omega` directly on `lo1 + lo2 ≤ x1 + x2 ∧ x1 + x2 ≤ hi1 + hi2` expands three `% 2^64` modulo operations into Euclidean division case splits inside `omega`, generating **`5,223` DAG nodes (`841,932` tree nodes)** and **`54.67 ms`** kernel replay; rewriting `BitVec.toNat_add` + `Nat.mod_eq_of_lt` before linear arithmetic shrinks the proof to **`667` DAG nodes (`23,292` tree nodes, `36.1x` smaller)** and **`0.89 ms` kernel replay (`61.7x` faster)**.
5. **`Lean.Meta` Caching Under Free Variables (`hasFVar`) Across Elaboration Subsystems (`MetaHasFVarCachingProbe.lean`)**:
   - Source audit of `src/Lean/Meta/` in `v4.29.0` and `v4.34.1` reveals a sharp asymmetry in how `hasFVar` affects memoization:
     - **`Meta.whnf` (`src/Lean/Meta/WHNF.lean:273-277`)**: `useWHNFCache e` returns `false` whenever `e.hasFVar || e.hasMVar` is `true` at `.default` or `.all` transparency (whereas the C++ kernel `type_checker::whnf_core` caches local constants `fvar` unconditionally). Consequently, on a depth-$d$ shared state-transition DAG where a concrete `Bool` tag is paired with a symbolic `FVar` payload, `(Prod.fst cur).hasFVar` is `true`, disabling `whnfDefault` caching and causing $O(2^d)$ re-evaluation: at $d = 20$, `whnf` takes **`4,533.96 ms` (`v4.34.1`) / `12,453.04 ms` (`v4.29.0`)** vs. **`0.15 ms` / `0.36 ms`** when closed (**`31,241x` / `34,126x` slowdown**).
     - **`Meta.simp`, `Meta.dsimp`, `Meta.transform`, `InferType`, `Sym.Simp`, and `Sym.DSimp`**: All cache by `Expr` (or `PtrMap Expr` in `Sym.Simp` / `Sym.DSimp`) even when `e.hasFVar == true` (gating only on `!e.hasMVar` in `InferType.lean`). Running `Meta.dsimp` on the exact same depth-20 `FVar`-coupled DAG completes in **`1.42 ms` (`v4.34.1`, `3,185x` faster than `whnf`)** and **`3.03 ms` (`v4.29.0`, `4,110x` faster)**; decoupling the reducible control DAG from the `FVar` payload restores `useWHNFCache` and runs in **`0.18 ms` (`25,440x` faster)**.
     - **`BuiltinSimprocs/BitVec.lean` and `Offset.lean` (`evalNat`)**: Every builtin `BitVec` simproc calls `BitVec.fromExpr?` or `Nat.fromExpr?`, which immediately returns `none` when an operand contains an `FVar`, leaving symbolic `BitVec` expressions unreduced unless handled by `@[simp]` rewrite lemmas or closed `Bool` reflection.

## Applicability

This report applies to:

- **Lean 4 `v4.29.0`**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740` (`x86_64-unknown-linux-gnu`).
- **Lean 4 `v4.34.1`**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`x86_64-unknown-linux-gnu`).
- **Anneal repository revisions**:
  - `joshlf/anneal` at `af3c1e99c0a7410aa63522fc3888d34c32c13175` (`trusted/audit/TrustedBoundary.lean` kernel environment replay and axiom allowlist auditor).
  - `joshlf/anneal` at `f2bc17e9be87b777d63c785b31f3370ff058d69b` (`trusted/cargo-anneal/tests/fixtures/starnix/proof/Endianness.lean` and the 17-module Starnix `apply_endianness` verification fixture).
- **Fuchsia Starnix eBPF verifier target**: `fuchsia/fuchsia` at `823a15538f191b9dbd9ebafaa6ba23220b87d2e1` (`src/starnix/lib/ebpf/src/{conformance.rs, verifier.rs}`).

To keep all semantic references self-contained, the byte-swap specification (`ByteReversal`) and 64-bit bitwise/arithmetic operations examined in this report are defined inline over standard Lean 4 `Init.Data.BitVec` types:

```lean
def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

def ByteReversal (bits : Nat) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ (x : BitVec 64) (i : Nat), i < 64 →
    (f x).getLsbD i = if i < bits then x.getLsbD (reverseByteIndex bits i) else false
```

## Findings

### 1. Root-Cause Anatomy of the `5.91 MB` (`255.14M` Unshared Tree-Node) Proof-Term Blowup in `Endianness.lean`

Basis: **source** + **execution** (`src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean`, `src/Init/Data/BitVec/Lemmas.lean`, `src/Lean/Replay.lean`; [`support/EndiannessBaseline.lean`](support/EndiannessBaseline.lean), [`support/EndiannessCheckRangeOpt.lean`](support/EndiannessCheckRangeOpt.lean), [`support/probe_results.json`](support/probe_results.json)).

#### 1.1 Why `Endianness.lean` Reached `5.91 MB` and `489.13 ms` Kernel Replay
After CPS spine-forcing (`runForced`) reduced `ProductionSteps.lean` in the Starnix `apply_endianness` fixture (`joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`) from `3.33 MB` to `383.6 KB`, the 70-line [`Endianness.lean`](support/EndiannessBaseline.lean) module became the single largest `.olean` in the build (`5,909,768` bytes in `v4.34.1`; `5,708,160` bytes in `v4.29.0`) and the #2 kernel replay bottleneck (`489.13 ms` in `v4.34.1`; `556.50 ms` in `v4.29.0`).

Inspection of `Endianness.lean` and the per-constant `.olean` DAG/tree metrics in [`support/probe_results.json`](support/probe_results.json) shows that `Endianness.lean` does not call `bv_omega`. Instead, it proves 11 theorems over `BitVec 64` byte-swap masks (`swap8`, `swap16`, `swap32`, `swap64`) using `BitVec.eq_of_getLsbD_eq`, a 64-way recursive proposition conjunction `CheckRange 64`, and `simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]`:

| Constant in `EndiannessBaseline.lean` (`v4.34.1`) | Value DAG Nodes | Unshared Tree Nodes | Max Depth | `toKernelEnv.replay` (ms) |
| :--- | ---: | ---: | ---: | ---: |
| `Endianness.swap64_exact` | `120,035` | `165,305,787` | `351` | `258.50` |
| `Endianness.swap64_involutive` | `22,865` | `64,813,809` | `425` | `98.81` |
| `Endianness.swap32_exact` | `36,281` | `17,677,739` | `223` | `63.61` |
| `Endianness.swap32_involutive` | `12,113` | `3,581,225` | `261` | `21.92` |
| `Endianness.swap16_exact` | `13,173` | `2,713,511` | `159` | `19.63` |
| `Endianness.swap8_exact` | `5,846` | `681,829` | `130` | `8.59` |
| `Endianness.swap16_involutive` | `6,737` | `297,513` | `197` | `8.25` |
| `Endianness.swap8_involutive` | `1,364` | `35,286` | `133` | `1.59` |
| All other 76 constants (`._f`, `.eq_def`, `swap*_bits`, etc.) | `2,097` | `33,787` | `46` | `8.23` |
| **Total (`84` constants)** | **`220,511`** | **`255,140,486`** | **`425`** | **`489.13`** |

Four distinct mechanisms compound to create this `255.14M`-node tree:
1. **Free-variable bailout in `BitVec.reduceGetLsb` (`src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean:72-78`)**:
   ```lean
   builtin_dsimproc [simp, seval] reduceGetLsb (BitVec.getLsbD _ _) := fun e => do
     let_expr BitVec.getLsbD _ x i := e | return .continue
     let some x ← fromExpr? x | return .continue
     let some i ← Nat.fromExpr? i | return .continue
     return .done <| toExpr (x.getLsbD i)
   ```
   After `simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]` pushes `.getLsbD i` through the 8 shift-and-mask lanes of `swap64 x`, each constant mask bit extraction has the form `(0x000000000000ff00#64).getLsbD (i - 40)` or `(0x0000000000ff0000#64).getLsbD (40 + i)`. Because the index argument contains the free variable `i`, `Nat.fromExpr?` returns `none`, leaving all 8 lanes unreduced in the goal passed to `CheckRange 64`.
2. **CPS-shifted `CheckRange` lambda-addition tower**:
   In `EndiannessBaseline.lean`, `CheckRange` is defined bottom-up by shifting the predicate at every recursion step:
   ```lean
   def CheckRange : Nat → (Nat → Prop) → Prop
     | 0, _ => True
     | n + 1, p => p 0 ∧ CheckRange n (fun i => p (i + 1))
   ```
   At index $k \in [0, 63]$, `p` is wrapped in $k$ nested lambdas `(fun i => ... (fun i => p (i + 1)) ... (0 + 1))` and beta-reduced to `p (0 + 1 + ... + 1)` ($k$ unary additions). In `swap64_exact`, `p` references its index argument `19` times across the 8 byte lanes and RHS specification. Over $k = 0..63$, `simp` constructs congruence proof chains for $\sum_{k=0}^{63} 19k = 38{,}304$ nested `Nat.add` applications. Attempting to discharge `CheckRange 64` without `simp` fails immediately with `maximum recursion depth has been reached` at `maxRecDepth = 512` because WHNF must traverse the 63-deep nested lambda tower.
3. **`@And.intro` proposition-type embedding and `Bool.or` left-strictness**:
   Replacing `CheckRange` with top-down recursion `CheckRange (n + 1) p = p n ∧ CheckRange n p` and discharging each index by `Eq.symm rfl` ([`support/EndiannessCheckRangeOpt.lean`](support/EndiannessCheckRangeOpt.lean)) requires one subtle algebraic step: in Lean 4 (`src/Init/Prelude.lean:802-805`), `Bool.or` (`||`) pattern-matches strictly on its *left* argument:
   ```lean
   def Bool.or : Bool → Bool → Bool
     | true,  _ => true
     | false, b => b
   ```
   Consequently, `false || x.getLsbD idx` reduces definitionally to `x.getLsbD idx`, whereas `x.getLsbD idx || false` is stuck on the symbolic free variable `x`! Folding each byte lane via `bif cond then rest || x.getLsbD idx else rest` (`getLsbD_or_laneL` / `getLsbD_or_laneR`) makes inactive lanes disappear definitionally, allowing `Eq.symm rfl` to close each of the 64 bit indices. However, because `@And.intro P Q hP hQ` embeds both propositions `P` (the 8-lane bit equality at index $k$) and `Q` (`CheckRange k p`) in its type arguments at all 64 steps, `swap64_exact` still has `8,782` DAG nodes and `9,504,075` unshared tree nodes (`862,784` B `.olean`, `221.16 ms` replay).
4. **Unfactored `swap*_involutive` vs. `omega` Euclidean div/mod linearization**:
   In `EndiannessBaseline.lean`, `swap64_involutive` applies `CheckRange 64` directly to `(swap64 (swap64 x)).getLsbD i = x.getLsbD i`, substituting the 8-lane definition of `swap64 x` into each of the 8 lanes of the outer `swap64` ($8 \times 8 = 64$ lanes per bit $\times 64$ bits), producing `22,865` DAG nodes (`64,813,809` tree nodes). Factoring `swap*_involutive` through `swap*_bits` (`ByteReversal`) reduces all four involutivity proofs to a single index identity:
   $$\forall \text{bits} \in \{8, 16, 32, 64\},\; \forall i < \text{bits},\quad \text{reverseByteIndex}(\text{bits}, \text{reverseByteIndex}(\text{bits}, i)) = i \;\wedge\; \text{reverseByteIndex}(\text{bits}, i) < \text{bits}$$
   However, discharging this identity via `omega` (`EndiannessCheckRangeOpt.lean`) still emits a `3,423`-DAG-node (`2,022,805`-tree-node, depth `85`) auxiliary proof `reverseByteIndex_involutive._proof_1_1` taking `44.85 ms` in kernel replay because `omega` linearizes Euclidean division (`/ 8`) and remainder (`% 8`) into auxiliary quotient/remainder variables and Fourier–Motzkin case splits.

---

### 2. Parameter-Free Closed `Bool` Reflection and Direct C++ GMP Kernel Builtins (`EndiannessDropIn.lean`)

Basis: **source** + **execution** (`src/Init/Prelude.lean:1872-1878, 2089-2105`, `src/Init/Data/Nat/Bitwise/Basic.lean:133-134`, `src/kernel/type_checker.cpp:703-775`; [`support/EndiannessDropIn.lean`](support/EndiannessDropIn.lean), [`support/probe_results.json`](support/probe_results.json)).

#### 2.1 Factoring Symbolic Bit Readers out of Multi-Lane Shift-Mask Cascades (`evalLanes` & `checkLanes`)
Every byte-swap function `swapN x` is a left-associated `|||`-cascade of byte lanes of the form:
- Left-shifted lane (`shiftLeft = true`): `((x &&& mask) <<< shift)`
- Right-shifted lane (`shiftLeft = false`): `((x >>> shift) &&& mask)`

Instead of pushing `.getLsbD i` inside `x` and repeating `x.getLsbD` inside 64 proposition types, [`support/EndiannessDropIn.lean`](support/EndiannessDropIn.lean) abstracts the symbolic bit reader as an arbitrary function `f : Nat → Bool` (instantiated to `x.getLsbD`) and represents each lane by its parameter tuple `Lane := Bool × Nat × Nat` (`(shiftLeft, shift, mask.toNat)`):

```lean
abbrev Lane := Bool × Nat × Nat

def testBitFast (m idx : Nat) : Bool :=
  !Nat.beq (Nat.land 1 (Nat.shiftRight m idx)) 0

def evalLane (f : Nat → Bool) (i : Nat) (l : Lane) : Bool :=
  bif l.1 then
    Nat.ble i.succ 64 && !Nat.ble i.succ l.2.1 &&
      (f (i - l.2.1) && testBitFast l.2.2 (i - l.2.1))
  else
    f (l.2.1 + i) && testBitFast l.2.2 i

noncomputable def evalLanes (f : Nat → Bool) (i : Nat) (lanes : List Lane) : Bool :=
  List.rec false (fun l _ ih => ih || evalLane f i l) lanes
```

Crucially, for any bit index `i < 64`, at most one lane in `lanes` has a `true` mask bit `testBitFast mask idx`, and for `i < bits` that single active lane reads `f (reverseByteIndex bits i)`. This fact is a **parameter-free property of the constant lane table `lanes`**—it does not depend on `f : Nat → Bool` at all! Checking `checkLanes lanes bits = true` by closed kernel `rfl` once per width (`8`, `16`, `32`, `64`) discharges `evalLanes f i lanes = Nat.ble i.succ bits && f (reverseByteIndex bits i)` universally for all `f : Nat → Bool` and `i < 64`. Each `swapN_exact` proof then consists solely of 1–7 symbolic `rw [evalLanes_cons_shl / evalLanes_cons_ushr]` steps followed by `exact checkLanes_sound (x.getLsbD) lanesN N rfl i hi`.

#### 2.2 The Hidden `Decidable` / `instBEqOfDecidableEq` Overhead in Kernel `rfl`
When `checkLanes` and `checkNatPred` are evaluated by kernel `rfl`, what expressions actually execute inside `type_checker::whnf_core`?
In `src/Init/Prelude.lean:1872-1878, 2089-2105` and `src/Init/Data/Nat/Bitwise/Basic.lean:133-134`:
1. **`decide (a < b)` is NOT a C++ kernel builtin**:
   `decide (a < b)` expands to `@Decidable.decide (a < b) (Nat.decLt a b)`, where:
   ```lean
   instance Nat.decLe (n m : Nat) : Decidable (n ≤ m) :=
     dite (Nat.ble n m = true)
       (fun h => isTrue (Nat.le_of_ble_eq_true h))
       (fun h => isFalse (Nat.not_le_of_not_ble_eq_true h))
   ```
   Every time kernel WHNF reduces `decide (a < b)`, it reduces `Nat.ble a.succ b` via GMP, reduces `Eq.Decidable` on `Bool`, unfolds `dite`, constructs the proof object `isTrue (Nat.le_of_ble_eq_true (Eq.refl true))` (or `isFalse ...`), and then pattern-matches on `Decidable.decide` to extract `true` or `false` and **discard the proof object**!
2. **`(m : BitVec 64).getLsbD idx` (`Nat.testBit`) uses `instBEqOfDecidableEq` (`Nat.decEq`) instead of `Nat.beq`**:
   In `src/Init/Data/Nat/Bitwise/Basic.lean:133-134`:
   ```lean
   def testBit (m n : Nat) : Bool :=
     1 &&& (m >>> n) != 0
   ```
   Because `!=` uses `instBEqOfDecidableEq`, which calls `Nat.decEq` (`dite (Nat.beq a b = true) ...`), every `getLsbD` call during kernel WHNF also constructs and discards a `Decidable` equality proof term!

Bridging `decide (a < b)` to `Nat.ble a.succ b` (`decide_lt_eq_ble`) and `m.getLsbD idx` to `testBitFast m.toNat idx := !Nat.beq (Nat.land 1 (Nat.shiftRight m.toNat idx)) 0` (`getLsbD_eq_testBitFast`) routes all bit-index comparisons and mask-bit extractions directly to the four C++ GMP kernel builtins (`Nat.ble`, `Nat.beq`, `Nat.land`, `Nat.shiftRight` in `src/kernel/type_checker.cpp:703-775`). In `EndiannessDropIn.lean`, this single optimization cuts total module `toKernelEnv.replay` time in `v4.34.1` from `124.28 ms` down to **`54.01 ms`** (`2.30x` faster, and **`9.06x` faster** than `EndiannessBaseline.lean`).

#### 2.3 Complete 4-Variant Comparison on `Endianness.lean` (`v4.34.1` & `v4.29.0`)
All four variants of `Endianness.lean` were compiled and benchmarked across both Lean `v4.34.1` (`5045d0056413`) and Lean `v4.29.0` (`98dc76e3c0a9`):

| Metric (`v4.34.1` / `v4.29.0`) | [`EndiannessBaseline.lean`](support/EndiannessBaseline.lean) (`CheckRange 64` + `simp`) | [`EndiannessCheckRangeOpt.lean`](support/EndiannessCheckRangeOpt.lean) (Top-Down `CheckRange` + `bif` + `omega`) | [`EndiannessBvDecide.lean`](support/EndiannessBvDecide.lean) (`bv_decide` on `swap*_involutive` only; 7/15 thms) | [`EndiannessDropIn.lean`](support/EndiannessDropIn.lean) (Closed `Bool` Reflection + `testBitFast`/`Nat.ble`; 15/15 thms) | Improvement (`DropIn` vs. `Baseline`) |
| :--- | ---: | ---: | ---: | ---: | ---: |
| **`.olean` Size (Bytes)** | `5,909,768` / `5,708,160` (`5.91 MB`) | `862,784` / `858,136` (`842.6 KB`) | `301,720` / `426,000` (`294.6 KB`) | **`283,240` / `281,208` (`276.6 KB`)** | **`20.86x` / `20.30x` smaller** |
| **Total Module Constants** | `84` / `68` | `66` / `55` | `43` / `50` | **`34` / `34`** | **`2.47x` fewer constants** |
| **Total Kernel DAG Nodes** | `220,511` / `213,490` | `32,525` / `32,395` | `7,358` / `10,857` | **`9,786` / `9,786`** | **`22.53x` / `21.82x` smaller** |
| **Unshared Tree Nodes** | `255,140,486` / `253,184,426` | `12,743,177` / `12,741,005` | `4,451,868` / `4,882,816` | **`278,779` / `278,779`** | **`915.2x` / `908.2x` smaller** |
| **Max Proof Term Depth** | `425` / `423` | `135` / `135` | `144` / `147` | **`55` / `55`** | **`7.73x` shallower** |
| **Compile Wall Time (s)** | `2.10 s` / `2.81 s` | `1.11 s` / `1.21 s` | `0.60 s` / `0.70 s` | **`0.46 s` / `0.45 s`** | **`4.57x` / `6.24x` faster** |
| **Compile Peak RSS (MB)** | `431.7` / `444.7` | `385.8` / `372.5` | `698.2` / `704.4` | **`332.3` / `297.2`** | **`-99.4 MB` / `-147.5 MB` RSS** |
| **`toKernelEnv.replay` Min (ms)** | `489.13` / `556.50` | `221.16` / `248.64` | `42.45` / `70.93` | **`54.01` / `69.73`** | **`9.06x` / `7.98x` faster** |
| **Extra Axioms Beyond Std 3** | `0` | `0` | **`4` (`_native.bv_decide.ax_1_5`)** | **`0` (`TrustedBoundary`-clean)** | **100% TCB-compliant** |

---

### 3. `bv_decide` vs. `bv_normalize` Internals and `TrustedBoundary.lean` Axiom Auditing (`v4.29.0` & `v4.34.1`)

Basis: **source** + **execution** (`src/Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean`, `src/Lean/Elab/Tactic/BVDecide/Frontend/BVDecide/ReifiedBVLogical.lean`, `src/Lean/Meta/Native.lean:37-87`, `trusted/audit/TrustedBoundary.lean:553-570, 820-859`; [`support/EndiannessBvDecide.lean`](support/EndiannessBvDecide.lean), [`support/MixedBitVecArithProbe.lean`](support/MixedBitVecArithProbe.lean)).

#### 3.1 Two-Stage `bv_decide` Pipeline (`bv_normalize` vs. LRAT Native Reflection)
In both Lean `v4.29.0` (`98dc76e3c0a9`) and `v4.34.1` (`5045d0056413`), `bv_decide` (`Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean:119-165`) executes two stages:
1. **Stage 1 (`bv_normalize`, pure kernel proof terms)**: Runs the `Sym.Simp` rewrite/simproc pass (`normalizationRules` + `bv_normalize_proc` AC-normalizer). If Stage 1 simplifies the goal to `True`, it closes the goal using ordinary kernel congruence and rewrite proof terms with **zero extra axioms**.
   - *Why `bv_normalize` fails on multi-lane shift-and-OR expressions (`swap8` vs. `swap16`..`swap64`)*: `bv_normalize` normalizes bitwise OR `a ||| b` into negated bitwise AND `~~~(~~~a &&& ~~~b)` (`BitVec.or_eq_not_and_not`) and pushes constants/masks through single shifts (`extractLsb'`). On `swap8 (swap8 x) = x &&& 0xff#64` (1 lane, no `|||`), `bv_normalize` folds `(x &&& 0xff#64) &&& 0xff#64` to `x &&& 0xff#64` in Stage 1 without invoking CaDiCaL. On `swap16`, `swap32`, `swap64`, and `getDstReg (setDstReg raw val)` (which combine multiple shifted lanes via `|||`), De Morgan rewriting turns `|||` into nested `~~~(... &&& ...)`, preventing pure rewrite closure and forcing Stage 2.
2. **Stage 2 (Bit-blasting + CaDiCaL + `LratCert.toReflectionProof` $\to$ `Lean.Meta.nativeEqTrue`)**:
   When Stage 1 leaves a non-empty goal, `bv_decide` bit-blasts the `BitVec` goal into an AIG, invokes CaDiCaL to produce an LRAT certificate, and calls `LratCert.toReflectionProof` (`Frontend/BVDecide/ReifiedBVLogical.lean:133-155`), which calls `Lean.Meta.mkAuxTheorem` on `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean:37-87`):
   ```lean
   -- src/Lean/Meta/Native.lean:62-84
   let axiomName ← mkAuxDeclName (kind := `_native ++ tacticName ++ `ax)
   let axDecl := Declaration.axiomDecl {
     name := axiomName
     levelParams := []
     type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
     isUnsafe := false
   }
   addDecl axDecl
   ```

#### 3.2 How `_native.bv_decide.ax` Differs from `Lean.ofReduceBool` and Why `TrustedBoundary.lean` Rejects Both
- **Does `bv_decide` depend on `Lean.ofReduceBool`?** **No.** Unlike `native_decide` (`elabNativeDecideCore` in `Lean/Elab/Tactic/ElabTerm.lean`), which emits a single global axiom `Lean.ofReduceBool` into the proof term, `bv_decide`'s `nativeEqTrue` helper dynamically registers a **fresh per-invocation `Declaration.axiomDecl`** named `<TheoremName>._native.bv_decide.ax_1_5` (asserting `verifyBVExpr bvExpr lratCert = true` after native compiled evaluation during elaboration) alongside auxiliary definitions `<TheoremName>._expr_def_1_1` and `<TheoremName>._cert_def_1_1`.
- **Why `TrustedBoundary.lean` rejects `bv_decide` Stage 2 proofs**:
  In `joshlf/anneal@af3c1e99c0a7410aa63522fc3888d34c32c13175` (`trusted/audit/TrustedBoundary.lean`), `bv_decide` Stage 2 proofs fail two independent TCB checks:
  1. **Transitive axiom allowlist (`targetAudit`, lines `553-570`)**: `collectAxioms` traverses `cinfo.getUsedConstantsAsSet` and requires every `.axiomInfo` reachable from `Trusted.CrateTheorem` to belong to `allowedAxioms = [Classical.choice, Quot.sound, propext]`. Any `<Decl>._native.bv_decide.ax_1_5` triggers `disallowedAxioms`.
  2. **Module constant classification (`classifyConstant`, lines `820-859`)**: Any `.axiomInfo` declared in a non-`Trusted.*` proof module is rejected as a local axiom declaration.

---

### 4. Mixed 64-Bit Bitwise + Integer Abstract-Domain Proof Strategies (`MixedBitVecArithProbe.lean`)

Basis: **execution** + **source** ([`support/MixedBitVecArithProbe.lean`](support/MixedBitVecArithProbe.lean), [`support/probe_results.json`](support/probe_results.json)).

To evaluate proof strategies on Starnix eBPF verification obligations (`fuchsia/fuchsia@823a15538f191b9dbd9ebafaa6ba23220b87d2e1`, `src/starnix/lib/ebpf/src/verifier.rs`), [`support/MixedBitVecArithProbe.lean`](support/MixedBitVecArithProbe.lean) benchmarks four representative obligation families across Lean `v4.34.1` and `v4.29.0`:

| Obligation Family & Theorem (`MixedBitVecArithProbe.lean`) | Proof Strategy | DAG Nodes (`4.34.1` / `4.29.0`) | Unshared Tree Nodes (`4.34.1` / `4.29.0`) | Max Depth | Kernel Replay (`4.34.1` ms) | Extra Axioms |
| :--- | :--- | ---: | ---: | ---: | ---: | :--- |
| **1A. `bitand_wf_cases`** (`U64ScalarValueData::bitand_scalar` known-bits invariant) | `BitVec.eq_of_getLsbD_eq` + `cases` on 4 `Bool` bit atoms at index `i` | `1,861` / `1,861` | `41,080` / `41,080` | `67` | **`3.11 ms`** | **`0`** |
| **1B. `bitand_wf_bv_decide`** | `bv_decide` (CaDiCaL + LRAT native axiom) | `580` / `583` (incl. `_expr_def`) | `41,347` / `42,027` | `52` | `5.58 ms` | `1` (`_native.bv_decide.ax`) |
| **2A. `dstReg_lt_16_algebraic`** (`(getDstReg raw).toNat < 16` bound) | `BitVec.toNat_and` + `Nat.lt_of_le_of_lt Nat.and_le_right (by decide)` | **`135` / `135`** | **`1,483` / `1,483`** | **`24`** | **`0.41 ms`** | **`0`** |
| **2B. `dstReg_lt_16_bv_decide`** | `bv_decide` on `getDstReg raw < 16#64` + `BitVec.lt_def.mp` | `411` / `441` | `8,654` / `10,446` | `37` | `2.26 ms` | `1` (`_native.bv_decide.ax`) |
| **2C. `getDstReg_setDstReg_reflect`** (`EbpfInstruction` bitfield lens round-trip) | `BitVec.eq_of_getLsbD_eq` + `checkNatPred_sound 64` + `checkAllBool2_sound` + `rfl` | `740` / `725` | **`29,988` / `29,992`** | **`47`** | `18.07 ms` | **`0`** |
| **2D. `getDstReg_setDstReg_bv_decide`** | `bv_decide` (De Morgan blocks `bv_normalize`; triggers Stage 2) | `633` / `714` | `32,377` / `41,745` | `53` | `4.97 ms` | `1` (`_native.bv_decide.ax`) |
| **3A. `u64_add_range_bv_omega`** (`U64Range::add_range` wrapping `+` under no-overflow) | `bv_omega` directly on `BitVec 64` inequalities (3 modulo `% 2^64` splits) | `5,223` / `5,223` (incl. `_proof_1_1`) | `841,932` / `841,932` | `73` | `54.67 ms` (`54.03 ms` in `_proof_1_1`) | `0` |
| **3B. `u64_add_range_mod_elim`** | `BitVec.le_def` + `BitVec.toNat_add` + `Nat.mod_eq_of_lt` before linear addition | **`667` / `667` (`7.8x` smaller)** | **`23,292` / `23,292` (`36.1x` smaller)** | **`40`** | **`0.89 ms` (`61.7x` faster)** | **`0`** |
| **4A. `revIdx64_omega`** (`reverseByteIndex 64` involutivity) | `unfold reverseByteIndex; omega` (Euclidean `/ 8`, `% 8` linearization) | `3,269` / `3,269` (incl. `_proof_1_1`) | `1,956,798` / `1,956,798` | `83` | `45.23 ms` (`44.85 ms` in `_proof_1_1`) | `0` |
| **4B. `revIdx64_reflect`** | `checkNatPred_sound 64` + closed `Bool` `rfl` | **`151` / `140` (`21.6x` smaller)** | **`1,243` / `1,247` (`1,574x` smaller)** | **`21`** | **`5.28 ms` (`8.6x` faster)** | **`0`** |

Key synthesis rules for mixed 64-bit bitwise + integer proofs:
1. **Pure bitwise word obligations without shifts (`&&&`, `|||`, `~~~`, `^^^`)**: Use `BitVec.eq_of_getLsbD_eq` + `simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_zero]` followed by `cases` on the $k \le 4$ bit atoms (`v.getLsbD i`). The proof is width-independent, requires `0` SAT axioms, and replays in `~3 ms`.
2. **Packed bitfield lens round-trips combining shifts, masks, and `|||`**: Use `BitVec.eq_of_getLsbD_eq` + `checkNatPred_sound 64` composed with finite truth-table quantification (`checkAllBool2_sound`) over the input bit atoms `(raw.getLsbD (s + i), val.getLsbD i)`. This avoids both `CheckRange` proposition-type bloat and `bv_decide` Stage 2 axioms.
3. **Wrapping `BitVec 64` arithmetic under `toNat` no-overflow hypotheses**: Never invoke `bv_omega` directly on `BitVec 64` addition/subtraction inequalities, because `bv_omega` unfolds `BitVec.toNat_add` (`(a.toNat + b.toNat) % 18446744073709551616`) and forces `omega` to case-split on Euclidean division by $2^{64}$ (`841,932` tree nodes, `54.67 ms` replay). Always rewrite `% 2^64` away first via `Nat.mod_eq_of_lt` (`61.7x` faster replay).
4. **Bounded-domain nonlinear/div/mod `Nat` index identities (`i < 64`)**: Replace `omega` with `checkNatPred_sound 64 ... rfl` (`1,574x` fewer tree nodes; `8.6x–17.6x` faster kernel replay).

---

### 5. `Lean.Meta` Caching (`useWHNFCache`, `dsimp`, `simp`, `Sym.Simp`) Under Free Variables (`hasFVar`)

Basis: **source** + **execution** (`src/Lean/Meta/WHNF.lean:273-277`, `src/Lean/Meta/Basic.lean:166-205`, `src/Lean/Meta/InferType.lean:28-35`, `src/Lean/Meta/Transform.lean:45-95`, `src/Lean/Meta/Tactic/Simp/Main.lean:77, 352`, `src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean`, `src/Lean/Meta/Sym/Simp/SimpM.lean:105`, `src/Lean/Meta/Sym/DSimp/DSimpM.lean:58`; [`support/MetaHasFVarCachingProbe.lean`](support/MetaHasFVarCachingProbe.lean), [`support/probe_results.json`](support/probe_results.json)).

#### 5.1 Complete Map of `hasFVar` / `hasMVar` Memoization Gates Across `Lean.Meta` (`v4.29.0` & `v4.34.1`)

| `Lean.Meta` Subsystem & Source Location (`v4.34.1`) | Cache Data Structure | `hasFVar` / `hasMVar` Guard | Operational Consequence on Symbolic `BitVec 64` / `State` DAGs |
| :--- | :--- | :--- | :--- |
| **`Meta.whnf` (`src/Lean/Meta/WHNF.lean:273-277`)** | `Cache.whnfDefault` / `Cache.whnfAll` (`ExprMap Expr`) | `useWHNFCache e` returns **`false` if `e.hasFVar \|\| e.hasMVar`** (at `.default` or `.all` transparency; other transparencies never cache). | **Critical $O(2^d)$ blowup**: Any shared subterm `cur` containing a free variable anywhere inside it (even in an unused tuple field `(ctrl, symVar).1`) has `hasFVar == true` and bypasses `whnfDefault`, re-evaluating shared DAG nodes exponentially. |
| **`Meta.inferType` (`src/Lean/Meta/InferType.lean:28-35`)** | `Cache.inferType` (`ExprMap Expr` keyed by `ExprWithCtx`) | Checks **`!e.hasMVar`** (`hasFVar` is **allowed** in cache!). | `inferType` caches expressions containing free variables, *except* when computing dependent application/projection types invokes `whnf` on a type or term with `hasFVar == true`. |
| **`Meta.transform` / `Core.transform` (`src/Lean/Meta/Transform.lean:45-95`)** | Local `ExprMap Expr` per `transform` call | **No `hasFVar` guard** (caches all shared `Expr` nodes by structural hash/equality). | Traverses shared symbolic DAGs in $O(\text{DAG nodes})$ time regardless of `hasFVar`. |
| **`Meta.dsimp` (`src/Lean/Meta/Tactic/Simp/Main.lean:352`)** | `dsimpCache : ExprMap Expr` | **No `hasFVar` guard** (caches all expressions when `config.memoize == true`). | Reduces shared `FVar`-containing DAGs in $O(\text{DAG nodes})$ time (`3,185x–4,110x` faster than `Meta.whnf` at depth 20). |
| **`Meta.simp` (`src/Lean/Meta/Tactic/Simp/Main.lean:77`)** | `cache : ExprMap Result` | Caches when `config.memoize == true` (skips cache only when result depends on contextual `hasMVar`). | Memoizes shared `FVar` subterms across the DAG, *unless* a side condition or `dite`/`ite` `Decidable` synthesis calls `whnf`/`isDefEq` on a large `hasFVar` term. |
| **`Sym.Simp` / `Sym.DSimp` (`src/Lean/Meta/Sym/Simp/SimpM.lean:105`, `DSimpM.lean:58`)** | `PtrMap Expr Result` / `PtrMap Expr Expr` (after `shareCommon`) | **No `hasFVar` guard** ($O(1)$ pointer-identity lookup). | $O(\text{DAG nodes})$ bottom-up simplification used by `bv_normalize`. |
| **`BuiltinSimprocs.BitVec` (`src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean`)** | None (stateless `dsimproc`s) | Calls `BitVec.fromExpr?` / `Nat.fromExpr?`, which **returns `none` on any non-literal (`hasFVar == true`)**. | All 35+ builtin `BitVec` simprocs (`reduceAdd`, `reduceAnd`, `reduceGetLsb`, `reduceGetElem`, etc.) immediately return `.continue` when either operand contains an `FVar`. |
| **C++ Kernel `whnf_core` (`src/kernel/type_checker.cpp:703, m_whnf_core_cache`)** | `m_whnf_core_cache` (`expr_map<expr>`) | Caches WHNF even when `has_fvar(e) == true`; **only `reduce_nat` (`line 703`) aborts on `has_fvar(e)`**. | Kernel `rfl` scales linearly $O(d)$ on shared `FVar` DAGs, *provided* `Nat` GMP operations (`reduce_nat`) do not wrap unreduced projections of an `FVar`-carrying state tuple. |

#### 5.2 Empirical Benchmark: $O(2^d)$ `Meta.whnf` Blowup vs. $O(d)$ `Meta.dsimp` and Decoupled State DAGs (`MetaHasFVarCachingProbe.lean`)
In [`support/MetaHasFVarCachingProbe.lean`](support/MetaHasFVarCachingProbe.lean), we construct a depth-$d$ state-transition DAG ($d \in \{10, 12, 14, 16, 18, 20\}$) where each step updates a `Bool` control tag via `Bool.or cur.1 cur.1` while forwarding a second component `cur.2 := payload`, and then projects `(step^d (false, payload)).1`:
- Because `Bool.or false b` reduces its first argument to `false` and then reduces its second argument `b`, reducing `(step^d (false, payload)).1` requires reducing both occurrences of the shared subterm `cur_{d-1}.1` at every depth.
- When `payload` is a closed literal `0 : Nat` (`hasFVar = false`), `useWHNFCache` caches the first branch of `Bool.or cur.1 cur.1` in `whnfDefault` and hits the cache in $O(1)$ on the second branch.
- When `payload` is a free variable `symVar : Nat` (`hasFVar = true`), `(Prod.fst cur).hasFVar` is `true`—even though `.1` projects only the concrete `Bool` tag! Consequently, `useWHNFCache` returns `false` and `Meta.whnf` re-evaluates both branches from scratch ($O(2^d)$):

| Depth $d$ | `whnf` Closed (`hasFVar = false`) (`4.34.1` / `4.29.0` ms) | `whnf` Coupled `FVar` (`hasFVar = true`) (`4.34.1` / `4.29.0` ms) | `dsimp` Coupled `FVar` (`ExprMap` cached) (`4.34.1` / `4.29.0` ms) | `whnf` Decoupled `FVar` (`ctrl` separated) (`4.34.1` / `4.29.0` ms) | `dsimp` Speedup Over `whnf` (`4.34.1` / `4.29.0`) | Decoupled Speedup Over Coupled `whnf` (`4.34.1` / `4.29.0`) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`10`** | `0.28` / `0.53` | `4.53` / `12.11` | `0.88` / `1.07` | **`0.09` / `0.23`** | `5.1x` / `11.3x` | `52.2x` / `52.6x` |
| **`12`** | `0.09` / `0.23` | `17.74` / `48.15` | `0.77` / `1.06` | **`0.08` / `0.22`** | `22.9x` / `45.4x` | `234.0x` / `223.7x` |
| **`14`** | `0.10` / `0.25` | `70.68` / `191.60` | `0.94` / `1.19` | **`0.09` / `0.25`** | `75.0x` / `160.4x` | `762.5x` / `781.4x` |
| **`16`** | `0.12` / `0.30` | `281.77` / `772.18` | `1.08` / `1.40` | **`0.11` / `0.30`** | `260.6x` / `549.6x` | `2,486.7x` / `2,543.3x` |
| **`18`** | `0.13` / `0.32` | `1,132.82` / `3,107.26` | `1.22` / `1.58` | **`0.12` / `0.34`** | `927.8x` / `1,965.3x` | `9,173.3x` / `9,275.1x` |
| **`20`** | `0.15` / `0.36` | **`4,533.96` / `12,453.04`** | **`1.42` / `3.03`** | **`0.18` / `0.40`** | **`3,184.9x` / `4,109.6x`** | **`25,439.8x` / `30,947.6x`** |

This reveals why structural separation of concrete control-flow state from symbolic `BitVec` payloads—or CPS constructor forcing (`runForced`) before embedding symbolic payloads—is essential in Lean 4: because `Expr.hasFVar` is a coarse syntactic bit cached on every `Expr` node (`(mkProj ``Prod 0 pair).hasFVar == pair.hasFVar`), bundling a symbolic `FVar` inside the same unforced tuple or structure as concrete control tags poisons `useWHNFCache` for every projection of that tuple.

## Boundaries

- **Bitwidths beyond 64 bits (`w > 64`) for closed `Bool` reflection (`known not to apply` without factoring)**: Parameter-free closed `Bool` reflection over bit indices (`checkLanes` / `checkNatPred w`) scales linearly $O(w)$ in bitwidth `w` and is ideal for `w <= 64` (`54 ms` replay for 15 theorems). For wide bitvectors (`w >= 1024`) or symbolic bitwidths, use width-parametric `BitVec.eq_of_getLsbD_eq` + `Bool.casesOn` (`bitand_wf_cases`) when shift offsets are zero, or byte-chunked / word-algebraic lemmas.
- **`bv_decide` Stage 2 LRAT reflection under `TrustedBoundary.lean` (`unsupported` without TCB change)**: Any `bv_decide` invocation that cannot be closed by Stage 1 (`bv_normalize`) emits `<Decl>._native.bv_decide.ax_1_5` via `Lean.Meta.nativeEqTrue` and is rejected by `TrustedBoundary.lean`.
- **Multi-threaded elaboration (`-j > 1`) (`not examined`)**: All compilation and kernel replay measurements were conducted with single-file invocations wrapped in `anneal-lean-run`.

## Evidence

- **Four-Variant `Endianness.lean` Proof-Term & Kernel Replay Benchmark (`support/`)**:
  - [`support/EndiannessBaseline.lean`](support/EndiannessBaseline.lean) (`3fae68c78c64900d09880bd71fa7b2b2146aa936f944c192e706cc1d48252500`): Original 70-line `CheckRange 64` + `simp` fixture (`5,909,768` B `.olean`, `220,511` DAG nodes, `255,140,486` tree nodes, `489.13 ms` replay in `v4.34.1`).
  - [`support/EndiannessCheckRangeOpt.lean`](support/EndiannessCheckRangeOpt.lean) (`79aa547fe716d1ce269339abf03a2d5356111a9bcffa51d10f255e294b8b51a2`): Top-down `CheckRange 64` + `bif` lane folding + `omega` involutivity (`862,784` B `.olean`, `32,525` DAG nodes, `12,743,177` tree nodes, `221.16 ms` replay).
  - [`support/EndiannessBvDecide.lean`](support/EndiannessBvDecide.lean) (`758da3065d30e99e4053d495f6945680937a10fa295abd1ee692893afe7b929f`): `bv_decide` on `swap*_involutive` (`301,720` B `.olean`, `4` `_native.bv_decide.ax_1_5` axioms).
  - [`support/EndiannessDropIn.lean`](support/EndiannessDropIn.lean) (`0c4198f22df0caa8a662e613fa69dd933ceaf4aff0431c590d54c856b565c53e`): Drop-in `TrustedBoundary`-compliant replacement using `evalLanes`, `checkLanes`, `checkNatPred`, `testBitFast`, and `Nat.ble` (`283,240` B `.olean`, `9,786` DAG nodes, `278,779` tree nodes, `54.01 ms` replay, `0` extra axioms).
- **Mixed 64-Bit Bitwise + Integer Abstract-Domain Probe (`support/`)**:
  - [`support/MixedBitVecArithProbe.lean`](support/MixedBitVecArithProbe.lean) (`df393754d55199a51d696fd3fafdd471753c101010c657a17367266e5285ebda`): Side-by-side comparison across `U64ScalarValueData::bitand_scalar`, `EbpfInstruction` bitfield lenses and bounds, `U64Range::add_range` modulo elimination vs. `bv_omega`, and `reverseByteIndex` reflection vs. `omega`.
- **`Lean.Meta` `hasFVar` Caching Probe & `.olean` Replay Profilers (`support/`)**:
  - [`support/MetaHasFVarCachingProbe.lean`](support/MetaHasFVarCachingProbe.lean) (`02efe3ffe409b871cdc14a7f6035ce7c111bb13d184a970c8dfa87a670718c85`): `Meta.whnf` vs. `Meta.dsimp` vs. decoupled-DAG scaling across depths $d \in \{10, 12, 14, 16, 18, 20\}$ and `BuiltinSimprocs.BitVec` `hasFVar` behavior.
  - [`support/BenchOlean.lean`](support/BenchOlean.lean) (`5a58bca6355a93fae735c3076a68b0a3bc5885bd0d01b54f515f07e0b18a4bbb`), [`support/BenchOlean429.lean`](support/BenchOlean429.lean) (`edd267ec9b16caff2da90c091d038fdc34cca60c9218c473599f9c6089318559`), [`support/TimeConsts.lean`](support/TimeConsts.lean) (`5a8262f8ff0c02e1825c07f549737a1ccab542a2b332dca18f97cd26305a70df`), and [`support/probe_results.json`](support/probe_results.json) (`2bee5e296f25c4c3eb0b9d7594b95d6f5a1168f1b4f7d218c141853abd768d8d`).

## Revalidation

1. **Re-compile and benchmark the four `Endianness` variants and `MixedBitVecArithProbe` on Lean `v4.34.1` (or `v4.29.0`)**:
   ```bash
   cd reports/lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching/support
   SYSROOT="$(lean --print-prefix)"
   for mod in EndiannessBaseline EndiannessCheckRangeOpt EndiannessBvDecide EndiannessDropIn MixedBitVecArithProbe; do
     lean -o "${mod}.olean" "${mod}.lean"
     LEAN_PATH=. lean --run BenchOlean.lean "$mod" "$SYSROOT"
     LEAN_PATH=. lean --run TimeConsts.lean "$mod" "$SYSROOT"
   done
   ```
2. **Re-run the `Lean.Meta` `hasFVar` caching benchmark**:
   ```bash
   cd reports/lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching/support
   lean --run MetaHasFVarCachingProbe.lean "$(lean --print-prefix)"
   ```
3. **Inspect upstream control points on Lean toolchain upgrades**:
   Check `src/Lean/Meta/WHNF.lean` (`useWHNFCache` `hasFVar` guard), `src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean` (`fromExpr?` / `Nat.fromExpr?`), `src/Lean/Meta/Native.lean` (`nativeEqTrue` `_native.bv_decide.ax` emission), and `src/Init/Prelude.lean` (`Nat.decLe` / `instBEqOfDecidableEq`).
