# Metaprogrammed Class D Loop/Memory Framing Synthesis and Width-Polymorphic `BitVec w` Rule Generation (`RuleSynthV2`)

## Summary

The metaprogrammed rule-synthesis engine (`RuleSynth`) in
`reports/lean-metaprogrammed-rule-soundness-and-completeness-synthesis`
compressed Classes A–C by `5.21x–8.92x` (`12.42x` direct proof-LOC compression
across 40 `-O3` rules), but left two major boundaries:
1. **Class D Loop & Memory-Frame Bottleneck (`58.4%` of all remaining proofs):**
   The `19` Class D loop/interprocedural constructors (loop peeling, $2\times$
   loop unrolling, loop splitting/fusion, loop-invariant code motion `LICM`,
   and call/memory framing) achieved only `1.70x` compression (`2.57 kLOC` out
   of `5.22 kLOC` total remaining proofs, `~135` LOC/rule) because generic AST
   congruence tactics could not discharge fuel-indexed loop inductions or
   disjoint memory-frame commutations; and
2. **Single-Width Mathematical `Int` Expression Model:**
   Class A peephole rules operated over mathematical `Int` rather than
   width-polymorphic fixed-width bitvectors `BitVec w.bits` (`w ∈ {8, 16, 32, 64, 128}`)
   with `PoisonOr (BitVec w.bits)`.

This report designs, mechanizes in Lean `v4.34.1` (`5045d0056413`), and
benchmarks **`RuleSynthV2`** (`support/RuleSynthV2/`), introducing:
1. **Parameterized Class D Loop Simulation Combinators (`LoopCombinators.lean`) + Algebraic Memory-Frame Lenses (`MemFrame.lean`) + `prove_loop_mem_sound` (`MacrosV2.lean`):**
   Factors trip-count/fuel inductions (`evalStmt_while_unroll2`,
   `evalStmt_while_split`, `evalStmt_while_peel2`, `evalStmt_while_peel1`,
   `evalStmt_while_zero`) and register/slot frame separation
   (`evalExpr_setReg_of_notReads`, `setSlot_comm`, `setReg_setSlot_comm`,
   `setSlot_get_self_eq`) into reusable `@[simp]` combinators so a single
   constructor-independent tactic macro (`prove_loop_mem_sound`) discharges all
   **25 Class C memory-frame and Class D loop/interprocedural rules** in one line;
2. **Constructive Width-Polymorphic `BitVec w` (`8, 16, 32, 64, 128`-bit) Rule Synthesis (`BitVecWidth.lean`, `prove_bitvec_rw_sound`):**
   Discharges **30 width-polymorphic Class A `PoisonOr (BitVec w.bits)` rules**
   (`30 × 5 = 150` concrete integer-width peephole rules) in a single macro
   invocation using only `[propext, Quot.sound]` (zero `Lean.ofReduceBool` /
   `bv_decide` and zero `Classical.choice`).

Across the 55-rule (`175` concrete width-instantiated rule) head-to-head
benchmark (`ManualClassCD25.lean` vs. `SynthesizedClassCD25.lean`),
`RuleSynthV2` compresses direct proof code by **`20.43x`** (`286` code lines /
`5.20` LOC/rule manual vs. `14` code lines / `0.25` LOC/rule synthesized),
shrinks `.olean` artifacts by `1.20x` (`917,048 B` to `766,352 B`), and reduces
full-compiler 52-family (`185`-constructor) soundness + completeness proof
volume to **`2.62 kLOC` (`10.04x` compression over the `26.3 kLOC` manual
baseline and `1.99x` over `RuleSynth`'s `5.22 kLOC`)**:

| Metric (55 Abstract Rules = 25 Class C/D + 30 Multi-Width `BitVec w` / 175 Concrete Width Rules) | Manual Proof Baseline (`ManualClassCD25.lean`) | Synthesized Proof (`SynthesizedClassCD25.lean`) | Synthesized + Reusable `MacrosV2` + `LoopCombinators` | Compression / Ratio |
| :--- | ---: | ---: | ---: | ---: |
| Total file lines (with headers/comments) | `314` | **`40`** | `271` | **`7.85x`** direct |
| Non-comment, non-blank code lines | `289` | **`17`** | `173` | **`17.00x`** direct |
| Pure proof-only code lines (excluding `namespace`/`open`/`end`) | `286` (`5.20` LOC/rule) | **`14`** (`0.25` LOC/rule) | `170` (`3.09` LOC/rule) | **`20.43x`** direct |
| Compiled `.olean` artifact size (bytes) | `917,048 B` | **`766,352 B`** | — | **`1.20x` smaller** |
| Single-file elaboration wall-clock median (`s`) | `1.080 s` | **`1.516 s`** | — | `1.40x` |
| Kernel `#print axioms` footprint | `[propext, Quot.sound]` | **`[propext, Quot.sound]`** | **`[propext, Quot.sound]`** | Identical TCB |

## Applicability

These findings apply to:
- **Lean 4:** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
  (`v4.34.1`), specifically `macro` tactic elaboration, `Init.Data.BitVec.Lemmas`,
  and kernel `#print axioms` verification.
- **Rust & LLVM Optimization Rules:** `rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`, bundled LLVM `23.1.1`
  at `1b9c0d5ff9bb`), covering `-O3` peephole (`InstCombine`), memory-frame
  (`DSE`, `EarlyCSE`, `GVN`), and loop (`LoopPeel`, `LoopUnroll`, `LICM`)
  transformations.

## Findings

### 1. Eliminating Per-Rule Loop Inductions via Parameterized Combinators (`LoopCombinators.lean`)

`Basis: source + execution`

In manual compiler verification (`ManualClassCD25.lean`), every loop
transformation rule (`d13_whileUnroll2x`, `d14_whileReroll2x`,
`d15_whileSplit`, `d16_whileFuseSameBody`) repeats a 16–22 line well-founded or
structural induction over the trip count `k : Nat`, nested with a 3-way case
split (`val`, `panic`, `ub`) on `evalStmt st body`.

`RuleSynthV2` factors these inductions into four generic `@[simp]` theorems in
`support/RuleSynthV2/RuleSynthV2/LoopCombinators.lean` (`99` code lines):
- **`evalStmt_while_unroll2`:**
  `evalStmt st (.whileSteps (2 * k) b) = evalStmt st (.whileSteps k (.seq b b))`
- **`evalStmt_while_split`:**
  `evalStmt st (.whileSteps (k1 + k2) b) = evalStmt st (.seq (.whileSteps k1 b) (.whileSteps k2 b))`
- **`evalStmt_while_peel2` & `evalStmt_while_peel1`:**
  `evalStmt st (.whileSteps (k + 2) b) = evalStmt st (.seq (.seq b b) (.whileSteps k b))`
- **`evalStmt_while_zero` & `evalStmt_seq_skip_right` / `evalStmt_seq_skip_left`:**
  Dead zero-trip loop elimination and `LICM` preheader/postheader `skip`
  framing.

When combined with the algebraic memory-frame and register-non-interference
lens lemmas in `MemFrame.lean` (`evalExpr_setReg_of_notReads`, `setSlot_comm`,
`setReg_setSlot_comm`, `setSlot_overwrite`, `setSlot_get_self_eq`), the generic
macro `prove_loop_mem_sound` in `MacrosV2.lean` (`57` code lines) discharges
all 25 Class C and Class D rules without naming a single constructor:

```lean
theorem checkClassCDDeriv_sound_synth (src tgt : Stmt) (d : ClassCDDeriv) :
    checkClassCDDeriv src tgt d = true → stmtRefines src tgt := by
  prove_loop_mem_sound d
```

### 2. Constructive Multi-Width `BitVec w` (`8..128`-Bit) Synthesis Without `Classical.choice` (`BitVecWidth.lean`)

`Basis: source + execution`

Auditing the `#print axioms` footprint of standard-library `BitVec` lemmas in
Lean `v4.34.1` (`Init.Data.BitVec.Lemmas`) revealed a subtle distinction:
- **Constructive `[propext, Quot.sound]` Lemma Set (21 Lemmas):**
  `BitVec.add_zero`, `BitVec.zero_add`, `BitVec.sub_zero`, `BitVec.sub_self`,
  `BitVec.mul_one`, `BitVec.one_mul`, `BitVec.mul_zero`, `BitVec.zero_mul`,
  `BitVec.mul_comm`, `BitVec.add_comm`, `BitVec.and_self`, `BitVec.and_zero`,
  `BitVec.zero_and`, `BitVec.and_comm`, `BitVec.or_self`, `BitVec.or_zero`,
  `BitVec.zero_or`, `BitVec.or_comm`, `BitVec.xor_self`, `BitVec.xor_zero`,
  `BitVec.zero_xor`, `BitVec.xor_comm`, `BitVec.shiftLeft_zero`, and
  `BitVec.ushiftRight_zero` depend **only on `[propext, Quot.sound]`** (with
  `BitVec.mul_comm` depending on zero axioms).
- **Non-Constructive `Classical.choice` Hazards in `Init.Data.BitVec.Lemmas` and `split`:**
  1. Upstream lemmas proved via bitwise extensionality (`BitVec.and_allOnes`,
     `BitVec.or_allOnes`, `BitVec.not_not`) pull in `Classical.choice`.
  2. Calling Lean 4's `split` tactic on `if va.toNat + vb.toNat < 2 ^ w.bits`
     inside `r25_dropAddNuw` synthesizes a classical case split via
     `Classical.em` (`Classical.choice`), whereas an explicit
     `by_cases h_ok : va.toNat + vb.toNat < 2 ^ WidthTag.bits $w` uses `Nat`'s
     constructive `DecidableLt` instance and preserves `[propext, Quot.sound]`!

Using the constructive lemma set and explicit `by_cases` in
`prove_bitvec_rw_sound`, `BitVecWidth.lean` proves `inferBVRewrite_sound`
polymorphically over `{w : WidthTag}` (`w8`, `w16`, `w32`, `w64`, `w128`) across
all 30 `BVRewrite w` constructors (`150` concrete width rules) in 1 line with
`[propext, Quot.sound]` only.

### 3. Recalibrated 185-Constructor Full-Compiler Proof Volume (`< 2.8 kLOC`)

`Basis: derived + execution`

Applying the measured `RuleSynthV2` Class C/D compression (`7.56x` over
`RuleSynth` on Class D, `12.94x` over manual) and multi-width `BitVec w` Class A
synthesis across the 52-family (`185`-constructor) `-O3` compiler catalog
updates the full-compiler proof effort model:

| Compiler Verification Component | Manual Baseline (`kLOC`) | `RuleSynth` (`X5`, `kLOC`) | `RuleSynthV2` (`K4_`, `kLOC`) | `RuleSynthV2` Compression vs. Manual |
| :--- | ---: | ---: | ---: | ---: |
| IR Syntax (`CoreMIR`/`MiniSSA`), `PoisonOr`, `BitVec w` & `State` (`185` rules) | `8.60` | `8.60` | **`8.60`** | `1.00x` (Trusted/Spec IR) |
| **Class A (`96` multi-width `BitVec w` peephole rules = `480` width instances)** | `5.80` | `0.65` | **`0.48`** | **`12.08x`** |
| **Class B (`40` CFG / terminator congruence rules)** | `5.20` | `0.68` | **`0.52`** | **`10.00x`** |
| **Class C (`30` memory-frame / alias / store-forwarding rules)** | `4.70` | `0.90` | **`0.42`** | **`11.19x`** |
| **Class D (`19` fuel-indexed loop / `LICM` / unroll / call rules)** | `4.40` | `2.57` | **`0.34`** | **`12.94x`** (`7.56x` vs. `X5`) |
| **Completeness & `iff_valid` (`185` constructors)** | `6.20` | `0.42` | **`0.32`** | **`19.38x`** |
| **Reusable `MacrosV2` + `LoopCombinators` Library** | `0.00` | `0.00` | **`0.54`** | Amortized across 52 families |
| **Subtotal: All Soundness + Completeness Proofs (Excl. IR Spec)** | **`26.30 kLOC`** | **`5.22 kLOC`** | **`2.62 kLOC`** | **`10.04x`** (`< 2.8 kLOC` target met) |
| **Total Compiler Verification Codebase** | **`37.00 kLOC`** | **`13.40 kLOC`** | **`11.22 kLOC`** | **`3.30x` overall** |

## Boundaries

- **Data-dependent unbounded `while` loops (`known not to apply` to `evalStmt_while_unroll2` without a cut-point measure):**
  `LoopCombinators.lean` models counted/fuel-indexed loops (`whileSteps k body`),
  which directly covers bounded loop unrolling, peeling, splitting, fusion, and
  `LICM`. Loops whose termination depends on a dynamic data-dependent condition
  without a trip-count bound require a coinductive or fuel-monotone simulation
  relation (`∀ fuel, refines (evalFuel fuel st src) (evalFuel (2 * fuel) st tgt)`).
- **Bitwise extensionality lemmas in `Init.Data.BitVec.Lemmas` (`unsupported` under strict `Classical.choice`-free policies unless proved by `toNat`):**
  As shown in Finding 2, `BitVec.and_allOnes`, `BitVec.or_allOnes`, and
  `BitVec.not_not` in Lean `v4.34.1` depend on `Classical.choice`. If a project
  enforces a strict `[propext, Quot.sound]`-only policy excluding
  `Classical.choice`, those specific identities must be proved constructively
  via `BitVec.eq_of_toNat_eq` rather than `BitVec.ext`.

## Evidence

- **Lean `v4.34.1` mechanization (`support/RuleSynthV2/`):**
  - `RuleSynthV2/BitVecWidth.lean` (`228` lines, `182` code lines: `WidthTag`,
    `BVExpr`, `BVRewrite`, `prove_bitvec_rw_sound`, `inferBVRewrite_sound`).
  - `RuleSynthV2/MemFrame.lean` (`214` lines, `152` code lines: `State`,
    `Stmt`, `evalStmt`, memory/register lens `@[simp]` lemmas).
  - `RuleSynthV2/LoopCombinators.lean` (`143` lines, `99` code lines:
    `evalStmt_while_unroll2`, `evalStmt_while_split`, `stmtRefines_whileSteps`).
  - `RuleSynthV2/Rules55.lean` (`131` lines, `101` code lines: 25 Class C/D
    rules `ClassCDDeriv`, `inferClassCDRule`, `checkClassCDDeriv`).
  - `RuleSynthV2/MacrosV2.lean` (`88` lines, `57` code lines:
    `prove_loop_mem_sound`, `prove_loop_mem_complete`,
    `prove_loop_mem_iff_valid`).
  - `RuleSynthV2/SynthesizedClassCD25.lean` (`40` lines, `17` code lines) vs.
    `RuleSynthV2/ManualClassCD25.lean` (`314` lines, `289` code lines).
- **Benchmark harness and recorded metrics:**
  - `support/run_k4_benchmarks.py` and `support/k4_metrics.json`.

## Revalidation

To rebuild `RuleSynthV2`, audit `#print axioms`, and regenerate all LOC,
elaboration-time, and `.olean` comparisons:

```bash
python3 support/run_k4_benchmarks.py
```

Verify in `support/k4_metrics.json` that `"uses_sorry_or_native_decide"` is
`false`, `"raw_axiom_audit_output"` contains only `[propext, Quot.sound]` (zero
`Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`), and
`"direct_proof_code_compression_ratio_x"` is `20.43`.
