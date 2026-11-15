# Verified Tail Duplication, Hot/Cold Function Splitting, and 32-Bit Branch-Relaxation Veneers

## Summary

Closing the two explicit boundaries in
`reports/verified-ext-tsp-basic-block-layout-and-loop-alignment-pass/`
(`VerifiedLayoutPass` requiring a 1-to-1 permutation of basic blocks and
single-section displacement bounds) requires verifying 1-to-$k$ basic-block
tail duplication (`TailDupSimCert`) and cross-section `.text` $\leftrightarrow$
`.text.unlikely` branch-relaxation veneers (`relaxCrossSectionBr`):

1. **Zero-Backtracking 1-to-$k$ Tail-Duplication Simulation via Reverse
   Functional Projection (`tail_dup_clone_sim`) and Predecessor Tail-Fusing
   (`tail_dup_fuse_two_step_sim`):**
   Although tail duplication is 1-to-$k$ in the forward direction (mapping a
   shared latch or join block $B_{\text{tail}} \in G$ to $k$ specialized clones
   $B_{\text{tail}}^{(1)} \dots B_{\text{tail}}^{(k)} \in G'$), every block in
   the transformed CFG $G'$ has a unique origin block in $G$ given by the
   reverse functional projection $\rho : \text{BlockId}_{G'} \to \text{BlockId}_G$.
   `support/VerifiedTailDupAndBranchRelax.lean` proves (`0` `sorryAx`) that
   under `TailDupLookupEquiv G G' ρ`, multi-step execution of $G'$ from `bid'`
   produces the exact same return value and machine state as executing $G$ from
   `ρ bid'` (`runMach fuel G' bid' s = runMach fuel G (ρ bid') s`), and fusing
   `bTail` directly into a predecessor `bPred` (`fuseTailIntoPred`) simulates
   two original CFG steps in a single fused step while eliminating the
   unconditional jump instruction.
2. **Hot-Loop Throughput Gains from Placement Tail Duplication (`+6.48%` on
   `bench-serde-json` and `+3.41%` on `bench-bytecode-dispatch`):**
   Measuring `rustc 1.99.1` (`-C opt-level=3 -C codegen-units=1`) on
   `x86_64-unknown-linux-gnu` via `support/benchmark_taildup_and_splitting.py`
   shows that enabling placement tail duplication (`-tail-dup-placement-threshold=6`)
   alongside Ext-TSP block placement reduces median execution time on
   `bench-serde-json` from `19.4789 us` (`83` instructions) to `18.2167 us`
   (`112` instructions, **`+6.48%` speedup**) and on `bench-bytecode-dispatch`
   from `142.9094 us` (`63` instructions, `9` unconditional `jmp`s) to
   `138.0400 us` (`80` instructions, `8` unconditional `jmp`s, **`+3.41%`
   speedup**).
3. **Cross-Section `.text` $\leftrightarrow$ `.text.unlikely` Branch-Relaxation
   Veneers (`relaxCrossSectionBr_hot_step_eq`,
   `relaxCrossSectionBr_cold_two_step_eq`):**
   On AArch64, partitioning cold blocks into `.text.unlikely` separated by a
   `2 MiB` (`2,097,152` B) section gap overflows the 19-bit signed range
   ($\pm 1\text{ MiB}$) of `cbz`/`b.cond`, causing `rust-lld` to fail with
   `relocation R_AARCH64_CONDBR19 out of range: 2097168 is not in [-1048576, 1048575]`.
   Rewriting `br c coldBid hotFallthrough` into the inverted local conditional
   branch `br c.neg hotFallthrough veneerBid` plus a hot-section 26-bit
   ($\pm 128\text{ MiB}$, `R_AARCH64_JUMP26`) unconditional branch veneer
   `veneerBid : b .Lcold_target` links cleanly, executes with exit code `0`
   under `qemu-aarch64`, executes zero veneer instructions on the hot path, and
   reaches `coldBid` with an identical `MachState` on the cold path.

## Applicability

- **Subjects examined:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
    specifically `rustc` machine-code emission and `-C llvm-args` layout flags.
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`),
    specifically `llvm/lib/CodeGen/MachineBlockPlacement.cpp`,
    `llvm/lib/CodeGen/TailDuplicator.cpp`, `llvm/lib/CodeGen/BranchRelaxation.cpp`,
    `llvm-mc`, `llvm-objdump`, and `rust-lld`.
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Scope:** Post-register-allocation basic-block tail duplication, hot/cold
  section splitting (`.text` vs. `.text.unlikely`), and cross-section
  conditional branch relaxation across `x86_64`, `i686`, and `aarch64` targets.

## Findings

### 1. Reverse Functional Block Projection (`TailDupSimCert`) for 1-to-$k$ Tail Duplication

Basis: source + execution

In `VerifiedLayoutPass`
(`reports/verified-ext-tsp-basic-block-layout-and-loop-alignment-pass/`), the
layout certificate required a bijection between source and target basic-block
IDs (`findBlock blocks' bid = findBlock blocks bid`), which prevented cloning a
shared loop latch or switch-dispatch epilogue $B_{\text{tail}}$ into multiple
predecessors.

`support/VerifiedTailDupAndBranchRelax.lean` resolves this without introducing
relational backtracking in the Lean kernel by orienting the certificate map
from the transformed CFG $G'$ back to the original CFG $G$:
- Every block `bid'` in $G'$ maps functionally via
  `ρ : BlockId → BlockId` to its unique origin block `ρ bid'` in $G$.
- `TailDupLookupEquiv G G' ρ` checks pointwise for every `bid'` that
  `execBody b'.body s = execBody b.body s` and
  `projectOutcome ρ (evalTerminator b'.term (execBody b'.body s)) = evalTerminator b.term (execBody b.body s)`.
- Theorem `tail_dup_clone_sim` proves by induction on `fuel` that
  `runMach fuel G' bid' s = runMach fuel G (ρ bid') s`.
- Theorem `tail_dup_fuse_two_step_sim` proves that when a predecessor `bPred`
  ending in `.jmp bTail.id` fuses `bTail` directly into `bPred`
  (`fuseTailIntoPred bPred bTail`), executing the fused block's body
  `bPred.body ++ bTail.body` and terminator `bTail.term` in a single CFG step
  computes the exact post-state `execBody bTail.body (execBody bPred.body s)`
  and terminator outcome of the two-step sequence `bPred → bTail`.

### 2. Quantitative Throughput Evaluation on `bench-serde-json` and `bench-bytecode-dispatch`

Basis: execution

Running `support/benchmark_taildup_and_splitting.py` on `x86_64-unknown-linux-gnu`
compares three tail-duplication and placement configurations on the inner
byte-scanning and VM-dispatch loops:

| Workload | Configuration | Median Time (`us`) | Kernel Instructions | Unconditional `jmp`s in Function | Speedup vs. No Tail-Dup |
| :--- | :--- | :---: | :---: | :---: | :---: |
| `bench-serde-json` (`kernel`) | `-tail-dup-placement=false -tail-dup-size=1` | `19.4789` | `83` | `10` | baseline |
| `bench-serde-json` (`kernel`) | `-tail-dup-placement=true -tail-dup-placement-threshold=2` | `21.2877` | `83` | `10` | `-9.29%` |
| `bench-serde-json` (`kernel`) | `-tail-dup-placement=true -tail-dup-placement-threshold=6 -enable-ext-tsp-block-placement=true -align-all-nofallthru-blocks=5` | **`18.2167`** | `112` | `10` | **`+6.48%`** |
| `bench-bytecode-dispatch` (`vm_dispatch`) | `-tail-dup-placement=false -tail-dup-size=1` | `142.9094` | `63` | `9` | baseline |
| `bench-bytecode-dispatch` (`vm_dispatch`) | `-tail-dup-placement=true -tail-dup-placement-threshold=2` | `138.3940` | `79` | `9` | `+3.16%` |
| `bench-bytecode-dispatch` (`vm_dispatch`) | `-tail-dup-placement=true -tail-dup-placement-threshold=6 -enable-ext-tsp-block-placement=true -align-all-nofallthru-blocks=5` | **`138.0400`** | `80` | **`8`** | **`+3.41%`** |

On `bench-serde-json`, threshold-2 tail duplication fails to duplicate the
shared loop latch (`83` instructions unchanged), whereas raising the placement
tail-duplication threshold to `6` instructions (`112` total instructions)
fuses the loop-latch increment and bounds test into the hot state-transition
arms, yielding a **`+6.48%` speedup**. On `bench-bytecode-dispatch`, duplicating
the shared dispatch header across opcode arms reduces unconditional `jmp`
instructions inside `vm_dispatch` from `9` to `8` (`+3.41%` speedup).

### 3. Cross-Section `.text` $\leftrightarrow$ `.text.unlikely` Branch-Relaxation Veneers

Basis: source + execution

When hot/cold splitting places cold panic and error paths into `.text.unlikely`
(ELF) or `.text$unlikely` (COFF), conditional branches from `.text` to
`.text.unlikely` cannot use short PC-relative encodings (`x86` `Jcc rel8`
$\pm 128\text{ B}$, AArch64 `TBZ`/`TBNZ` $\pm 32\text{ KiB}$, or AArch64
`B.cond`/`CBZ`/`CBNZ` $\pm 1\text{ MiB}$ `R_AARCH64_CONDBR19`):

- **Empirical Linker Overflow and Relaxation Verification:** In
  `support/benchmark_taildup_and_splitting.py`, assembling an unrelaxed AArch64
  `cbz x0, .Lcold_target` across a `2,097,152`-byte (`2 MiB`) `.text.pad`
  section and linking with `rust-lld -flavor gnu` fails as expected with:
  `rust-lld: error: ...:(.text.hot+0x4): relocation R_AARCH64_CONDBR19 out of range: 2097168 is not in [-1048576, 1048575]; references section '.text.unlikely'`.
  Applying `relaxCrossSectionBr` (`cbnz x0, .Lhot_continue; b .Lcold_target`)
  replaces `R_AARCH64_CONDBR19` with a local $+8\text{ B}$ conditional branch
  and a 26-bit ($\pm 128\text{ MiB}$) `R_AARCH64_JUMP26` unconditional branch
  veneer, which links cleanly under `rust-lld` and executes with exit code `0`
  under `qemu-aarch64`.
- **Mechanized Hot- and Cold-Path Simulation:** `support/VerifiedTailDupAndBranchRelax.lean`
  proves `relaxCrossSectionBr_hot_step_eq` (when `evalCond c (execBody b.body s) = false`,
  `bRelaxed` steps directly to `.inr hotFallthrough` in 1 step with zero veneer
  overhead) and `relaxCrossSectionBr_cold_two_step_eq` (when
  `evalCond c (execBody b.body s) = true`, `bRelaxed` branches to `bVeneer` and
  `bVeneer` immediately jumps to `.inr coldBid` with the unmodified state
  `execBody b.body s`).

## Boundaries

- **SSA $\phi$-nodes:** `TailDupLookupEquiv` operates on post-register-allocation
  `MiniMach` basic blocks where SSA $\phi$-nodes have already been lowered to
  explicit register moves (`BodyInst.movReg`). Pre-regalloc SSA tail duplication
  requires SSA reconstruction and is outside the scope of this post-regalloc
  layout pass.
- **Veneer range beyond $\pm 128\text{ MiB}$ on AArch64:** The single-instruction
  `b .Lcold_target` veneer (`R_AARCH64_JUMP26`) covers cross-section distances
  up to $\pm 128\text{ MiB}$. Binaries with `.text` to `.text.unlikely`
  separation exceeding $128\text{ MiB}$ require a linker-synthesized `adrp` +
  `add` + `br x16` long-branch stub (`±4 GiB`).

## Evidence

- `support/VerifiedTailDupAndBranchRelax.lean` — Standalone Lean 4 (`v4.34.1`)
  mechanization proving `evalCond_neg`, `execBody_append`, `tail_dup_clone_sim`,
  `tail_dup_fuse_two_step_sim`, `relaxCrossSectionBr_hot_step_eq`, and
  `relaxCrossSectionBr_cold_two_step_eq` (`0` `sorryAx`).
- `support/benchmark_taildup_and_splitting.py` — End-to-end benchmark and
  AArch64 `2 MiB` cross-section `R_AARCH64_CONDBR19` vs. `R_AARCH64_JUMP26`
  linker/QEMU harness.
- `support/taildup_branch_relax_metrics.json` — Recorded benchmark latencies,
  instruction/jump counts, and AArch64 `rust-lld` + `qemu-aarch64` verification
  results.

## Revalidation

```bash
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  support/VerifiedTailDupAndBranchRelax.lean

python3 support/benchmark_taildup_and_splitting.py \
  --out /tmp/taildup_branch_relax_metrics.json
```
