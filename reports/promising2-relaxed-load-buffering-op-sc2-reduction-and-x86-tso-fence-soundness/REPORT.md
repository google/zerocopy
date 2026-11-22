# Operational Promising 2.0 `Relaxed` Load-Buffering, Modular Invariant & Release-Write Promise-Free Reductions, and `x86-TSO` `compiler_fence(SeqCst)` Soundness

## Summary

Sound verification of arbitrary weak-memory Rust programs—including `Ordering::Relaxed` shared stores and architecture-specific `#[cfg(target_arch = "x86_64")]` synchronization in `crossbeam-epoch 0.9.21`—cannot rely solely on promise-free `acyclic(sb ∪ rf)` operational interleaving (`ORC11` / promise-free `Op-SC2'`) or an unparameterized C++20 memory model:

1. **Unsoundness of Promise-Free `acyclic(sb ∪ rf)` Operational Semantics for `Ordering::Relaxed` on `ARMv8` and `RVWMO`:**
   - Under `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `-Copt-level=3 --emit=asm`), `lb_rlx` (`atomic_load::<u32, Relaxed>(x); atomic_store::<u32, Relaxed>(y, 1)`), `lb_false_dep` (`z = wrapping_sub(r, r); atomic_store(y, wrapping_add(1, z))`), and `lb_branch_hoist` (`match r { 1 => store(y, 1), _ => store(y, 1) }`) fold to identical machine instruction sequences on `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin` (`ldr w0, [x0]; mov w8, #1; str w8, [x1]; ret`) and `riscv64gc-unknown-linux-gnu` (`lw a0, 0(a0); li a2, 1; sw a2, 0(a1); ret`), while `lb_rlx_fetch_add` emits `ldr w0, [x0]; mov w8, #1; ldadd w8, w8, [x1]; ret` on `aarch64-apple-darwin` and `lw a0, 0(a0); li a2, 1; amoadd.w zero, a2, (a1); ret` on `riscv64gc-unknown-linux-gnu`.
   - Both `ARMv8` and `RVWMO` hardware permit `(r0 = 1, r1 = 1)` on two-thread `LB+rlx` (`[R]; po-loc-different; [W]` without address/data/control+ISB dependency). However, Lean 4 theorem `promiseFree_forbids_lb_rlx_1_1` proves that every promise-free operational execution of `LB+rlx` forbids `(1, 1)`—meaning a promise-free `ORC11` / `Op-SC2'` operational model would allow proving `¬ (r0 = 1 ∧ r1 = 1)` as a guard for `unsafe` operations that execute Undefined Behavior on `ARMv8` and `RVWMO` hardware.
2. **Operational Promising 2.0 (`PS2`) Capped-Memory Certification + Modular Promise-Erasure Reductions (`support/Anneal/PromisingReductionProof.lean`):**
   - Extending timestamped view semantics with Promising 2.0 (`PS 2.0`, Lee et al. PLDI 2020) capped-memory (`capMem`) `Relaxed` write promises admits halted promise-fulfilled `(1, 1)` on `LB+rlx` (`ps2_allows_lb_rlx_1_1`), `LB+false_dep`, `LB+branch_hoist`, and `LB+rlx_fetch_add`, as well as `(1, 2)` on `LB+cond_overwrite` via sub-interval insertion `(1, 3]` strictly below promised `(4, 6]` (`ps2_allows_lb_cond_overwrite_1_2`).
   - `capMem` places adjacent synthetic cap blocks `(M_max, M_max + 1]` at maximum per-location timestamps during thread-local certification, blocking stealable RMW certification (`ps2_cap_blocks_stealable_rmw_promise`; uncapped ablation produces dead unfulfillable promise states in `PS2_capMem_rmw_steal_control`), while `fence(Release | AcqRel | SeqCst)` promise draining forbids `(1, 1)` on `LB+frel+acq` (`ps2_forbids_lb_frel_acq_1_1`).
   - Crucially, **modular verification over `PS2` does not force user proofs to construct thread-local certification traces**:
     - `ps2_pure_relaxed_invariant_preserved` proves by induction over certification traces that any unary per-location value invariant `Φ : Loc → Nat → Prop` respected by thread commands (`CmdRespectsValInv`) and initial memory (`AllMessagesRespect`) holds across all reachable `PS2` configurations (both promised and fulfilled messages), immediately yielding Out-Of-Thin-Air (`OOTA`) freedom `c.t0.obs = 0 ∧ c.t1.obs = 0` across all reachable states of `LB+data_dep` (`ps2_forbids_oota_lb_data_dep`).
     - `releaseOnly_exact_bisimulation` proves that whenever a thread's shared writes all carry release semantics (`CmdAllWritesRelease`: `Release`, `AcqRel`, or `SeqCst` on stores/RMWs, while permitting arbitrary `Relaxed`/`Acquire`/`SeqCst` loads and fences), no unfulfilled promise can ever pass `Certified`, reducing `PS2ThreadStep` by exact step equivalence (`↔`) to `PromiseFreeThreadStep`.
3. **`TargetMemModel` Separation of Portable C++20 vs. `x86-TSO` `compiler_fence(SeqCst)` (`crossbeam-epoch 0.9.21`):**
   - On `crossbeam-epoch`'s `#[cfg(target_arch = "x86_64")]` epoch-pinning idiom (`atomic_xchg::<usize, SeqCst>(x, 1); compiler_fence(SeqCst); atomic_load::<usize, Acquire>(y)`, `internal.rs:212-225`), `x86_64-unknown-linux-gnu` emits `xchgq %rax, (%rdi); movq (%rsi), %rax` (omitting `portable_fence_sc_pattern`'s extra `lock orl $0, -64(%rsp)` because `xchgq` already drains the `x86-TSO` store buffer), whereas `aarch64-apple-darwin` (`ARMv8.3 +rcpc`) emits `swpal x8, x8, [x0]; ldapr x0, [x1]` without `dmb ish` (where `[W & L]; po; [R & Q]` permits `(0, 0)`).
   - Parameterizing operational transitions by `TargetMemModel` (`portableCpp20` vs. `x86Tso`) proves both halves (`tso_xchg_forbids_0_0_and_portable_allows_0_0`): `portableCpp20` admits halted `(0, 0)` (`portableCpp20_allows_xchg_cfence_acq_0_0`), while `x86Tso` forbids halted `(0, 0)` across all reachable states (`x86Tso_forbids_xchg_cfence_acq_0_0`).

## Applicability

- **Repository & Auditor Target:** `google/zerocopy` @ `ae3c943b7b1004d839ddb8d0dad65eacba158d58` (`anneal/trusted/audit/TrustedBoundary.lean` and `anneal/trusted/lean/foundation-lock.json` pinning `leanprover/lean4:v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`).
- **Compiler & Crate Subjects:** `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) emitting `-Copt-level=3` assembly for `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `riscv64gc-unknown-linux-gnu`, and `x86_64-unknown-linux-gnu`, and `crossbeam-epoch 0.9.21` (`sha256: dc74980687109a3b14c72fd458107bf0baa1da1a1a805e178d15501ba9b86d9d`).

## Findings

### 1. Multi-Architecture `#![no_core]` Atomic Codegen Under Pinned `rustc 1.98.0-nightly` (`f8a08b688c`)

`Basis: execution (compiler assembly output) + normative hardware/language specifications`

| Function Pattern (`u32` / `usize`) | `aarch64-apple-darwin` (`+lse +rcpc`) | `riscv64gc-unknown-linux-gnu` (`RVWMO`) | `x86_64-unknown-linux-gnu` (`x86-TSO`) |
| :--- | :--- | :--- | :--- |
| `lb_rlx` / `lb_false_dep` / `lb_branch_hoist` (identical emitted instructions) | `ldr w0, [x0]; mov w8, #1; str w8, [x1]; ret` | `lw a0, 0(a0); li a2, 1; sw a2, 0(a1); ret` | `movl (%rdi), %eax; movl $1, (%rsi); retq` |
| `lb_rlx_fetch_add` (`load(Rlx); xadd(1, Rlx)`) | `ldr w0, [x0]; mov w8, #1; ldadd w8, w8, [x1]; ret` | `lw a0, 0(a0); li a2, 1; amoadd.w zero, a2, (a1); ret` | `movl (%rdi), %eax; lock incl (%rsi); retq` |
| `lb_data_dep` (`store(y, r, Rlx)`) | `ldr w0, [x0]; str w0, [x1]; ret` | `lw a0, 0(a0); sw a0, 0(a1); ret` | `movl (%rdi), %eax; movl %eax, (%rsi); retq` |
| `lb_ctrl_dep` (`if r == 1 { store(y, 1, Rlx) }`) | `ldr w0, [x0]; cmp w0, #1; b.ne ...; mov w8, #1; str w8, [x1]; ret` | `lw a0, 0(a0); li a2, 1; bne a0, a2, ...; sw a2, 0(a1); ret` | `movl (%rdi), %eax; cmpl $1, %eax; jne ...; movl $1, (%rsi); retq` |
| `lb_frel_acq` (`load(Acq); fence(Rel); store(1, Rlx)`) | `ldapr w0, [x0]; dmb ish; mov w8, #1; str w8, [x1]; ret` | `lw a0, 0(a0); fence r, rw; fence rw, w; li a2, 1; sw a2, 0(a1); ret` | `movl (%rdi), %eax; movl $1, (%rsi); retq` |
| `crossbeam_x86_pattern` (`xchg(SeqCst); singlethreadfence(SeqCst); load(Acq)`) | `mov w8, #1; swpal x8, x8, [x0]; ldapr x0, [x1]; ret` | `li a2, 1; amoswap.d.aqrl zero, a2, (a0); ld a0, 0(a1); fence r, rw; ret` | `movl $1, %eax; xchgq %rax, (%rdi); movq (%rsi), %rax; retq` |
| `portable_fence_sc_pattern` (`xchg(SeqCst); fence(SeqCst); load(Acq)`) | `mov w8, #1; swpal x8, x8, [x0]; dmb ish; ldapr x0, [x1]; ret` | `li a2, 1; amoswap.d.aqrl zero, a2, (a0); fence rw, rw; ld a0, 0(a1); fence r, rw; ret` | `movl $1, %eax; xchgq %rax, (%rdi); lock orl $0, -64(%rsp); movq (%rsi), %rax; retq` |

- On `aarch64-unknown-linux-gnu` (baseline `ARMv8.0` without `+rcpc`), `crossbeam_x86_pattern` emits `bl __aarch64_swp8_acq_rel; ldar x0, [x19]` (`RCsc` `ldar`), whereas `aarch64-apple-darwin` (`+rcpc`) lowers `Acquire` load to `ldapr`, allowing hardware reordering before `swpal` unless `fence(SeqCst)` (`dmb ish`) intervenes.
- On `lb_cond_overwrite` (`match r { 0 => { store(y, 1); store(y, 2) }, _ => store(y, 2) }`), LLVM 20 preserves all 3 atomic store instructions across the two arms on all four targets; `(1, 2)` remains hardware-observable in the `r != 0` arm via `ldr`/`lw` -> `str`/`sw` reordering, and `PS2` admits `(1, 2)` both with and without dead-atomic-store elimination.

### 2. Executable `PS2-OpSC2'` State-Space & Non-Vacuity Verification

`Basis: execution + derived`

- **Litmus Outcomes Verified (`support/verify_promising2_op_sc2_and_tso.py`):**
  - *Admitted (`PS2-OpSC2'`):* `LB+rlx (1, 1)` (forbidden under `allow_promises=False`), `LB+false_dep (1, 1)`, `LB+branch_hoist (1, 1)`, `LB+cond_overwrite (1, 2)` (splitting rational interval `(0, 2)` below promised `(2, 3]`), and `LB+rlx_fetch_add (1, 1)` (adjacent `Relaxed` RMW promise).
  - *Forbidden (`PS2-OpSC2'`):* `LB+data_dep_OOTA (1, 1)` (sole outcome `(0, 0)`), `LB+ctrl_dep (1, 1)` (sole outcome `(0, 0)`), `LB+rel+acq (1, 1)`, and `LB+frel+acq (1, 1)`.
  - *Paired Ablation Controls:*
    1. **`PS2_capMem_rmw_steal_control`:** With `use_cap=True` (`cap_memory` placing `(max_to, max_to + 1]` caps during `can_certify`), `stuck_promise = False`; disabling `use_cap=False` allows Thread 0 to certify a promise of `y = 1` via an RMW on `z` that Thread 1 subsequently steals, producing a dead unfulfillable promise state (`stuck_promise = True`).
    2. **`LB+frel+acq` release-fence tracking:** Disabling both `drain_on_release_fence=False` and `check_rel_on_fulfill=False` causes `LB+frel+acq` to falsely admit `(1, 1)` (`ablation_no_fence_drain_and_no_rel_view_falsely_allows_1_1 = True`). Note that when `drain_on_release_fence=True` holds, `st.rel` is invariant across the lifetime of every unfulfilled promise, so deterministically setting a promise's exported view to `view_bump(st.rel, loc, to_ts)` at promise allocation loses no generality relative to existential view selection.

### 3. Kernel-Checked Lean 4.34.1 Mechanization (`Anneal.PromisingReductionProof`)

`Basis: execution (Lean 4 kernel replay at trustLevel := 0)`

`support/Anneal/PromisingReductionProof.lean` (`2,449` lines, SHA-256 `3ccbb2bd49d82d10a28818680ee0f4f652c877bb30519f977e143dcd99d931a0`) passes `TrustedBoundary.lean` `"preflight"`, `-t0 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` compilation, `"audit"` fresh kernel replay (`2,781` replayed declarations), `CheckEnvConstants` (`587` constants, `isUnsafe=0, isPartial=0, unsafeRec=0, isAxiom=0, isOpaque=0, hasSorry=0`), and `#print axioms` (`[propext]` only across all `12` theorems):

1. `promiseFree_forbids_lb_rlx_1_1`: Proves `¬ (c.t0.obs = 1 ∧ c.t1.obs = 1)` across all `PFReachable2 lbRlxInitPF c` states.
2. `ps2_allows_lb_rlx_1_1` & `ps2_allows_lb_cond_overwrite_1_2`: Construct explicit `PS2Reachable2` traces to `Cmd.halt` with `hasPromiseBy 0 c.mem = false ∧ hasPromiseBy 1 c.mem = false` achieving `(1, 1)` and `(1, 2)`.
3. `ps2_cap_blocks_stealable_rmw_promise`: Proves `¬ Certified 0 (initThread stealableRmwCmd) (mProm :: initMem2)` for all `(fromTs, toTs)`.
4. `ps2_threadStep_preserves_valInv`, `ps2_pure_relaxed_invariant_preserved`, & `ps2_forbids_oota_lb_data_dep`: Proves universal unary per-location invariant preservation across `PS2` promises and physical steps, deriving `c.t0.obs = 0 ∧ c.t1.obs = 0` on `LB+data_dep`.
5. `ps2_forbids_lb_frel_acq_1_1`: Proves `¬ (c.t0.obs = 1 ∧ c.t1.obs = 1)` across all `PS2Reachable2 lbFrelAcqInitPS2 c` states.
6. `releaseOnly_exact_bisimulation`: Proves `(PS2ThreadStep tid s mem s' mem' ∧ (∀ m, m ∈ mem' → m.promisedBy = none)) ↔ PromiseFreeThreadStep tid s mem s' mem'` under `CmdAllWritesRelease s.cmd` and unpromised `mem` (refuting `PS2ThreadStep.promise` directly via `no_promise_when_allWritesRelease` without relying on the post-state conjunct).
7. `portableCpp20_allows_xchg_cfence_acq_0_0`, `x86Tso_forbids_xchg_cfence_acq_0_0`, & `tso_xchg_forbids_0_0_and_portable_allows_0_0`: Proves the exact `(0, 0)` separation between `TargetMemModel.portableCpp20` and `TargetMemModel.x86Tso` on `crossbeamInitTarget`.

## Boundaries

1. **Standalone Operational Model vs. `Trusted.MirSemantics` Wiring:** Although `PromisingReductionProof.lean` imports `Trusted.MirSemantics` and `Anneal.Core.SepPCM` and passes `TrustedBoundary.lean` with `"requireMirWp": true`, its theorems are proved over the standalone `Cmd` / `Msg` / `View2` transition relations in that module rather than wired into `Trusted.MirSemantics.Step`.
2. **Two-Location / Two-Thread Specialization & Discrete `Nat` Endpoints in Lean:** `PromisingReductionProof.lean` specializes views (`View2`), `capMem`, and configurations (`PFConfig2`, `PS2Config2`, `TargetConfig2`) to two locations (`{0, 1}`) and two threads (`{0, 1}`), and uses discrete `Nat` interval endpoints (`fromTs, toTs : Nat`) without promise `split`/`lower` transitions or `fulfillRmw`. While all six impossibility, invariant, and bisimulation theorems are timestamp-scale-invariant (embedding into $\mathbb{Q}_{\ge 0}$), general `PS 2.0` completeness for arbitrary numbers of conditional pre-promise writes requires dense $\mathbb{Q}_{>0}$ timestamps (as implemented in `support/verify_promising2_op_sc2_and_tso.py` via `fractions.Fraction`) plus promise `split`/`lower` and RMW fulfillment.
3. **`SeqCst` View Scope Across Sections:** Sections 1–4 of `PromisingReductionProof.lean` omit the global `SeqCst` view `S_sc` (studied separately in `c20-p0668r5-operational-seqcst-tree-borrows-fnexit-and-lean4-scope-soundness`), while Section 5's `TargetThreadStep` models the three operations in `crossbeamInitTarget` (`rmwXchg .seqCst`, `compilerFenceSeqCst`, `load .acquire`) rather than full `x86-TSO` FIFO write-buffer semantics for ordinary `Mov` stores.
4. **Unary Per-Location Scope of `CmdRespectsValInv`:** `ps2_pure_relaxed_invariant_preserved` applies to unary per-location value predicates `Φ : Loc → Nat → Prop` (sufficient for OOTA freedom, initialized-tag invariants, and valid-range bounds), not multi-location relational invariants (which `Relaxed` operations without `Release`/`Acquire` synchronization do not preserve).
5. **Bounded Explorer Horizon:** `support/verify_promising2_op_sc2_and_tso.py` bounds `can_certify` depth to `< 8` and active promises to `<= 1` per thread, which is exact for the `<= 5`-instruction loop-free litmus suite tested (`not examined` for unbounded loops).

## Evidence

- `support/Anneal/PromisingReductionProof.lean` — `2,449` lines, SHA-256 `3ccbb2bd49d82d10a28818680ee0f4f652c877bb30519f977e143dcd99d931a0`, zero-`sorry` Lean 4.34.1 mechanization of Theorems 1–5 (`12` exported theorems, `[propext]` only).
- `support/verify_promising2_op_sc2_and_tso.py` — reproducible multi-target `#![no_core]` `rustc` assembly probe, `Fraction`-timestamp `PS2-OpSC2'` + `TargetMemModel` state-space explorer with paired non-vacuity ablations, and 5-gate `TrustedBoundary.lean` replay driver against `google/zerocopy` @ `ae3c943b7b1004d839ddb8d0dad65eacba158d58`.

## Revalidation

```bash
ZEROCOPY_REPO=/path/to/zerocopy \
  ZEROCOPY_REV=ae3c943b7b1004d839ddb8d0dad65eacba158d58 \
  python3 -B reports/promising2-relaxed-load-buffering-op-sc2-reduction-and-x86-tso-fence-soundness/support/verify_promising2_op_sc2_and_tso.py
```
