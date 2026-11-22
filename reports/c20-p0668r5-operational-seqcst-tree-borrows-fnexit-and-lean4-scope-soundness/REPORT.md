# Operational C++20 `P0668R5` `SeqCst` (`Op-SC2'`), `TreeBorrows` `FnExit` `VClock` Soundness, and Pass-1 Lean 4 Universe-Polymorphic `std::thread::scope` Proofs

## Summary

Designing a sound weak-memory operational semantics and Pass-1 Lean 4 verification layer for Rust concurrency exposes four concrete architectural constraints verified across axiomatic/operational model checking, Tree Borrows + vector-clock trace analysis, and live `TrustedBoundary.lean` kernel replay (`leanprover/lean4:v4.34.1`):

1. **Global-View Operational `SeqCst` (`SC-1a`) Is Unsound for `rustc`'s `ARMv8.3+` (`+rcpc`) Codegen; `Op-SC2'` Achieves Exact C++20 `P0668R5` + `P0982R1` Equivalence Without Event-Graph History:**
   - Standard operational `ORC11` (`SC-1a`, maintaining a global `sc : Loc -> Ts` map joined cross-location into `tv.cur` on both `SeqCst` accesses and `SeqCst` fences) forbids `(r1 = 0, r2 = 0)` on `SB+sc_acq` (`T1: x.store(1, SeqCst); r1 = y.load(Acquire)` || `T2: y.store(1, SeqCst); r2 = x.load(SeqCst)`). Yet `rustc` compiles `aarch64-apple-darwin` (`target-cpu = "apple-m1"`, `ARMv8.3+ +rcpc`) `Ordering::Acquire` loads to `LDAPR` (`Q`), where `[W & L]; po; [R & Q]` is absent from `bob`, so both real Apple Silicon / Neoverse hardware and C++20 `P0668R5` **allow `(0, 0)`**.
   - Per-location `SeqCst` accesses (`SC-1b`) restore `SB+sc_acq (0, 0)` while still forbidding C++20-allowed `RWC+sc+acq (1, 0, 0)` and `Z6.U (1, 3, 0)` (which are allowed on non-MCA targets).
   - **`Op-SC2'`** (promise-free `ORC11 + P0982R1` + dense rational `STime` interval placement on `[SC ∪ F_sc]` events with bounded per-thread/per-message scalar `S`-bounds and live `obs_{cur,acq,rel}` maps, crucially updating `tv.s_left_hb_rel := max(left_sb_entering, tv.s_left_hb_cur)` on non-`SC` `fence(Release | AcqRel)` to preserve 4-thread `[SC]; sb; hb; sb; [SC]` chains) matches **100% of reachable `(regs, final_mo)` outcome sets** of Axiomatic C++20 (`P0668R5 + P0982R1 + acyclic(sb ∪ rf)`) across all `15` canonical 2–3 thread litmus tests, `4` targeted 4-thread mixed `SC`/`AcqRel`/RMW litmus tests (including `P_4_acqrel_fence`), `150` random 2–4 thread differential fuzz programs (`2T=40, 3T=50, 4T=60`), and an arbitrary-$N$-thread algebraic soundness/completeness invariant check.
   - **Mandatory `P0982R1` `Release`-Only RMW Rule:** On a `Release`-only RMW such as `std::thread::scope`'s `num_running_threads.fetch_sub(1, Ordering::Release)` (`library/std/src/thread/scoped.rs:67`), the new message's view must be `vmax(base_m.msg_view, tv.cur)` (preserving the prior release sequence) and `tv.acq` must join `base_m.msg_view` (enabling `Arc::drop`'s trailing `fence(Acquire)`), while leaving `tv.cur` un-joined with `base_m.msg_view`.
2. **Per-Thread `VClock : Tid -> Nat` Is Mandatory for Non-Atomic Race Detection:**
   - Tracking non-atomic reads and writes with scalar per-location timestamps (`naWriteTs`, `naReadTs : Loc -> Nat`) silently misses unsynchronized read-write data races whenever two threads hold equal `curView[loc] = k` (both initially at `k = 0` and after acquiring a shared store at `k > 0`). Per-thread vector clocks (`VClock : Tid -> Nat`) catch both while permitting `Release -> Acquire` handoffs and concurrent read-read sharing.
3. **`TreeBorrows` `FnExit` `ProtectorEnd` Must Emit `VClock` Accesses to Match LLVM `noalias`:**
   - In `rust-lang/rust` (`49d7345362`, `src/tools/miri/src/borrow_tracker/tree_borrows/{mod.rs:92-105, 186-189, 398-417; tree.rs:701-727}`), `FnEntry` retagging updates both `BorrowTree` and `VClock` (`NaReadType::Retag` / `NaWriteType::Retag`), whereas `FnExit` `release_protector` (`perform_protector_end_access`) updates only `BorrowTree` (likewise in single-threaded `vendor/lean-miri/Miri/TreeBorrows/TreeState.lean:1036-1065`). Under default `-Zmiri-tree-borrows` (`implicit_writes == false`), `fn foo(x: &mut AtomicUsize) { x.store(1, Relaxed); }` followed by `flag.store(1, Relaxed)` || `if flag.load(Relaxed) == 1 { (*raw_p).load(Relaxed) }` is accepted by unpatched Miri on sequential schedules yet triggers `DataRace` UB after LLVM's `noalias`-justified end-of-call non-atomic writeback. Emitting `NaWrite::ProtectorEnd` (when `perm == Unique && accessed`) and `NaRead::ProtectorEnd` (when `perm ∈ {ReservedFrz, Frozen} && accessed`) at `FnExit` closes this soundness gap without over-rejecting `Mutex` release/acquire handoffs or unwritten `&mut AtomicUsize`.
4. **Unmodified `TrustedBoundary.lean` Already Admits `universe u` Helpers on `theory/`, While `prelude` Without `Init.WF` Requires `@Nat.rec` to Avoid `._unsafe_rec`:**
   - Live `"preflight"`, `-DwarningAsError=true` compilation, `"audit"` (`base.toKernelEnv.replay`, `162` replayed declarations), and `requireClaimProof` against `google/zerocopy` (`f2efbfd1eb0c`) `anneal/trusted/audit/TrustedBoundary.lean` confirm that `universe u` (`ViewPCM (α : Type u)`, bare level identifiers with elaborator-inferred instantiation, excluding explicit `foo.{u}` syntax and compound `u + 1` / `max u v`) is already permitted on `SourceRole.theory` helpers, with `levelParams.isEmpty` enforced strictly on root claim and theorem endpoints.
   - Under `prelude` without `Init.WF` (`foundation-lock.json` keeps `Init.WFTactics` private), equation-compiler recursion on `Nat` compiles cleanly yet emits a hidden `*._unsafe_rec` auxiliary rejected by `"audit"` (`ci.isUnsafe || ci.isPartial`); writing fuel-indexed higher-order `Send`/`Sync` invariants (`SendSyncInv`) via kernel `@Nat.rec` eliminates `._unsafe_rec` completely (`Anneal.scope_sound`: `0` axioms).

## Applicability

These results apply to the pinned revisions and standards listed in `REPORT.json`:

- **Operational vs. Axiomatic vs. Hardware `SeqCst` (`Op-SC2'`):** Applies to single-word atomic `{load, store, successful fetch_add RMW, fence}` programs under `acyclic(sb ∪ rf)` targeting ISO C++20 (`P0668R5` + `P0982R1`) and `rustc` codegen on `x86_64`, `ARMv8.0` (`STLR`/`LDAR`), and `ARMv8.3+ (+rcpc)` (`aarch64-apple-darwin` `apple-m1` / Neoverse `STLR`/`LDAPR`).
- **Vector-Clock Race Detection and `TreeBorrows` `FnExit` Coupling:** Applies to `rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da` (`src/tools/miri/src/borrow_tracker/tree_borrows/` under default `implicit_writes == false`, and `src/tools/miri/src/concurrency/data_race.rs`) and `google/zerocopy` @ `f2efbfd1eb0c923aa2865e38229f72782a5aefb7` (`anneal/vendor/lean-miri/Miri/TreeBorrows/TreeState.lean`).
- **Pass-1 Lean 4 Boundary & `Send`/`Sync` Proof Mechanics:** Applies to `google/zerocopy` @ `f2efbfd1eb0c923aa2865e38229f72782a5aefb7` (`anneal/trusted/audit/TrustedBoundary.lean` and `anneal/trusted/lean/foundation-lock.json`) compiled with `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Operational `SeqCst` Separation (`SC-1a` vs. `SC-1b` vs. `Op-SC2'`) and `P0982R1` `Release` RMWs

`Basis: normative + source + execution + derived`

#### 1.1 Why `SC-1a` Fails on Real Apple Silicon (`ARMv8.3+ +rcpc`) and `SC-1b` Fails on `P0668R5`

In `rustc`, `aarch64-apple-darwin` (`compiler/rustc_target/src/spec/targets/aarch64_apple_darwin.rs:20`) defaults to `target-cpu = "apple-m1"`, enabling `ARMv8.3+ +rcpc` so `Ordering::Acquire` loads lower to `LDAPR` (`Q`) rather than `LDAR` (`A`), while `Ordering::SeqCst` stores lower to `STLR` (`L`). Consider `SB+sc_acq`:

```text
T1: x.store(1, SeqCst); r1 = y.load(Acquire)   // ARMv8.3 +rcpc: STLR x; LDAPR y
T2: y.store(1, SeqCst); r2 = x.load(SeqCst)    // ARMv8.3 +rcpc: STLR y; LDAR  x
```

In `aarch64hwreqs.cat`, barrier-ordered-before (`bob`) includes `[W & L]; po; [R & A]` (`STLR -> LDAR`) but **excludes** `[W & L]; po; [R & Q]` (`STLR -> LDAPR`) on distinct locations `x != y`. Likewise, in C++20 `P0668R5` (`[atomics.order]/3-4`), `r1 = y.load(Acquire)` is not `SeqCst`, so the unique valid `S`-order `[W_sc(y, 1), R_sc(x, 0), W_sc(x, 1)]` permits **`(r1 = 0, r2 = 0)`**.

- **`SC-1a` (`GlobalSCView-All`):** Joining a global `sc : Loc -> Ts` map cross-location into `tv.cur` on `SeqCst` accesses forces whichever of `T1: W_sc(x, 1)` or `T2: W_sc(y, 1)` executes second to absorb the first write's timestamp into `tv.cur`, **forbidding `(0, 0)`** and making `SC-1a` unsound for real `ARMv8.3+` hardware!
- **`SC-1b` (`PerLocAccess + GlobalFenceSC`):** Updating/checking `sc[loc]` only at `loc` on `SeqCst` accesses (while `fence(SeqCst)` still performs two-way global `sc` join) restores `SB+sc_acq (0, 0)`. However, because step order satisfies $u \prec_{\text{hb}} v \implies \text{step}(u) < \text{step}(v)$, `SC-1b` still forces `([SC]; hb; [SC]) ⊆ S`, forbidding C++20-allowed `RWC+sc+acq (1, 0, 0)` (`S = [c, d, e, a]`) and `Z6.U (1, 3, 0)` (which matter for non-MCA targets; note that under Arm's 2018 multi-copy-atomic `aarch64.cat`, `RWC+sc+acq` and `Z6.U` are forbidden on MCA `ARMv8.0`/`ARMv8.3` via `rfe ∪ fre ∪ bob`).

#### 1.2 `Op-SC2'`: Exact Operational C++20 (`P0668R5` + `P0982R1` + `acyclic(sb ∪ rf)`) Without Event-Graph History

Just as operational `ORC11` inserts atomic writes into dense modification-order timestamps `mo_ts ∈ Q_{>=0}`, **`Op-SC2'`** lets each `[SC ∪ F_sc]` event nondeterministically select a dense `S`-order timestamp $s \in (\text{lb}, \text{ub}) \subset (0, \infty) \subset \mathbb{Q}$ using only bounded per-thread scalars and per-message metadata (full implementation in `support/verify_op_sc2_vs_cpp20.py`):

- **Per-thread state (`ThreadView`):**
  - Standard `ORC11` `mo` views: `cur, acq, rel : Loc -> Q`.
  - Observed `hb` frontier for retroactive `F_sc` `eco` edges: `obs_{cur,acq,rel} : Loc -> Q ∪ {-1}` paired with `obs_is_read_{cur,acq,rel} : Loc -> Bool` (tie-breaking equal timestamps via `r1 || r2` so co-reading pure loads are not falsely ordered while `fr` lower bounds remain exact).
  - Scalar `STime` bounds: `s_last_sc` (max `s(u)` of prior `[SC ∪ F_sc]` on the thread), `s_left_hb_{cur,acq,rel}` (tracking $\max\{s(u) : u \in \text{SC}_{\text{all}},\; \exists x,\; u \to_{\text{sb}} x \to_{\text{hb}^?} e\}$ for `shb = (sb ∪ ([SC]; sw; [SC]) ∪ (sb; hb; sb))+`), and `s_f_{cur,acq,rel}` (max `s(F_sc)` preceding `hb`).
- **Critical 4-Thread `fence(AcqRel)` Invariant (`P_4_acqrel_fence`):**
  On entering any instruction, `left_sb_entering := max(tv0.s_last_sc, tv0.s_left_hb_cur)`. On a non-`SC` `fence(AcqRel)`:
  1. The `Acquire` half first sets `tv.s_left_hb_cur := max(tv.s_left_hb_cur, tv.s_left_hb_acq)`.
  2. The `Release` half **must** set **`tv.s_left_hb_rel := max(left_sb_entering, tv.s_left_hb_cur)`** (matching `fence(SeqCst)`).
  Omitting `tv.s_left_hb_cur` (`tv.s_left_hb_rel := left_sb_entering`) passes all 2- and 3-thread tests (`tv.rel := tv.cur` prevents closing the `S`-cycle without `eco` collision on `<= 3` threads) yet fails on 4-thread `P_4_acqrel_fence`:
  - `T0: a: store(x, 1, SC); b: store(y, 1, REL)`
  - `T1: c: r1 = load(y, RLX); d: fence(ACQ_REL); e: store(z, 1, RLX)`
  - `T2: f: r2 = load(z, ACQ); g: r3 = load(w, SC)`
  - `T3: h: store(w, 1, SC); i: r4 = load(x, SC)`
  C++20 forbids `(r1=1, r2=1, r3=0, r4=0)` via `(a, g) ∈ sb; hb; sb ⊆ shb ⊆ S` (`a ->_S g ->_fr h ->_sb i ->_fr a`), whereas unpatched `tv.s_left_hb_rel := left_sb_entering` allows `(1, 1, 0, 0)` (`16` vs. `15` `(regs, final_mo)` outcomes).
- **Mandatory `P0982R1` `Release`-Only RMW View Join (`std::thread::scope`):**
  In `library/std/src/thread/scoped.rs:67`, `ScopeData::decrement_num_running_threads` executes `num_running_threads.fetch_sub(1, Ordering::Release)` (read half `Relaxed`, write half `Release`). On any `fad(REL)` extending `base_m`:
  - `tv.acq` joins `base_m.msg_view` (and `obs_acq`, `s_left_hb_acq`, `s_f_acq`) so a trailing `fence(Acquire)` (`Arc::drop`) synchronizes;
  - `tv.cur` does **not** join `base_m.msg_view` (since `!has_acq(REL)`);
  - The newly inserted message sets `m_view := vmax(base_m.msg_view, tv.cur)` (and joins `base_m`'s `obs_view`, `s_left_msg`, `s_f_msg` with `tv`'s `cur` counterparts), preserving the prior thread's release view across the RMW release sequence (`MP+rel+rmw_rel+acq`).

#### 1.3 Verified Model-Checking Results (`support/verify_op_sc2_vs_cpp20.py`)

| Litmus Test | C++20 (`P0668R5`) | `ARMv8.0` | `ARMv8.3 +rcpc` | `SC-1a` | `SC-1b` | `Op-SC2'` | Exact `(regs, mo)` Match? |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `MP+rel+rmw_rlx+acq` | FORB | FORB | FORB | FORB | FORB | FORB | EXACT (`8`) |
| `MP+rel+rmw_rel+acq` (`ScopeDrop`) | FORB | FORB | FORB | FORB | FORB | FORB | EXACT (`8`) |
| `MP+rel+write_rlx+acq` (`P0982R1`) | ALLOW | FORB | FORB | ALLOW | ALLOW | ALLOW | EXACT (`5`) |
| `SB+sc_accesses` / `SB+sc_fences` / `SB+mixed` | FORB | FORB | FORB | FORB | FORB | FORB | EXACT (`3` each) |
| **`SB+sc_acq` (`ARMv8.3 +rcpc`)** | **ALLOW** | FORB | **ALLOW** | **FORB (BUG)** | ALLOW | **ALLOW** | **EXACT (`4`)** |
| **`RWC+sc+acq` (`P0668R5`)** | **ALLOW** | FORB | FORB | FORB | FORB | **ALLOW** | **EXACT (`8`)** |
| **`Z6.U` (`P0668R5`)** | **ALLOW** | FORB | FORB | FORB | FORB | **ALLOW** | **EXACT (`12`)** |
| `IRIW+sc` / `2+2W+sc` | FORB | FORB | FORB | FORB | FORB | FORB | EXACT (`15`, `3`) |
| `IRIW+acq` / `SB+rlx` / `2+2W+rlx` | ALLOW | FORB/ALLOW | FORB/ALLOW | ALLOW | ALLOW | ALLOW | EXACT (`16`, `4`, `4`) |
| `LB+rlx` (under `acyclic(sb ∪ rf)`) | FORB | ALLOW | ALLOW | FORB | FORB | FORB | EXACT (`3`) |
| **`P_4_acqrel_fence` (4-thread)** | **FORB** | — | — | — | — | **FORB** | **EXACT (`15`; unpatched `16`)** |
| `4T_IRIW+sc_fences` / `4T_AcqRelChain+RMW+SC` / `4T_WRC+Fsc+AcqRel` | — | — | — | — | — | — | **EXACT (`15` each)** |

Differential random fuzzing across `150` programs (`2T=40, 3T=50, 4T=60`, mixing `load`/`store`/`fad`/`fence` across all five orderings) matched **100%** of exact `(regs, final_mo)` outcome sets between `Op-SC2'` and Axiomatic C++20 (`P0668R5 + P0982R1 + acyclic(sb ∪ rf)`), and algebraic invariant checks verify all 8 multi-thread `shb`, `eco`, retroactive `obs_join`, and `F_sc` paths for arbitrary thread count $N$.

---

### 2. Scalar-Timestamp Race Blindness vs. `VClock` and `TreeBorrows` `FnExit` `ProtectorEnd` Soundness

`Basis: source + execution + derived`

#### 2.1 Scalar `naWriteTs`/`naReadTs` Blindness

If a weak-memory operational model replaces thread-indexed vector clocks with scalar per-location timestamps (`naWriteTs, naReadTs : Loc -> Nat`), where `readNA` checks `naWriteTs[loc] <= curView[loc]` and updates `naReadTs[loc] := max(naReadTs[loc], curView[loc])`, while `writeNA` checks `naWriteTs[loc] <= curView[loc] && naReadTs[loc] <= curView[loc]`:

- Whenever two unsynchronized threads `T1 != T2` hold equal `curView[loc] = k`—either initially (`k = 0`) or after both acquire the same prior store (`k = 5`)—`T1`'s `readNA(loc)` writes `naReadTs[loc] := k`, and `T2`'s unsynchronized `writeNA(loc, v)` checks `k <= k` (`true`), silently **missing a textbook non-atomic read-write data race**.
- Per-thread vector clocks (`VClock : Tid -> Nat`, tracking `na_write : Option (Tid × Nat)`, `na_reads : Tid -> Nat`, `at_write : VClock`, `at_read : VClock`) catch both `k = 0` and `k = 5` races while cleanly admitting `Release -> Acquire` handoffs and concurrent read-read sharing (`support/probe_vclock_and_tree_borrows_fnexit.py`, Part 2A).

#### 2.2 `TreeBorrows` `FnExit` `ProtectorEnd` `VClock` Soundness Gap

Direct inspection of `rust-lang/rust` (`49d7345362`) establishes an asymmetry between `FnEntry` and `FnExit`:

1. At **`FnEntry`** (`src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:398-417`), `tb_reborrow` informs both `BorrowTree` and `alloc_extra.data_race` (`NaReadType::Retag` / `NaWriteType::Retag`). Under default `-Zmiri-tree-borrows` (`implicit_writes == false`, `mod.rs:146`), `x: &mut AtomicUsize` (`AtomicUsize: Unpin`, emitting LLVM `noalias` + `dereferenceable` per `compiler/rustc_ty_utils/src/abi.rs:365-376`) starts as protected `ReservedFrz` (`NaReadType::Retag`).
2. Inside `fn foo(x: &mut AtomicUsize) { x.store(1, Ordering::Relaxed); }`, the atomic store reborrows `&*x` as `Cell`, whose child write activates `x` to **`Active` (`Unique`) with `accessed = true`** (`perms.rs:194-196, 208-216`) while recording only an *atomic* write in `VClock`.
3. At **`FnExit`** (`mod.rs:92-105, 186-189`, `tree.rs:701-727`, `borrow_tracker/mod.rs:359-397`), `release_protector` (`perform_protector_end_access`) computes `protector_end_access` (`Some(AccessKind::Write)` for `Active`/`Unique`, `Some(AccessKind::Read)` for `ReservedFrz`/`Frozen`) and updates `BorrowTree`, **without informing `data_race` (`VClock`)**. (Single-threaded `vendor/lean-miri/Miri/TreeBorrows/TreeState.lean:1036-1065` likewise updates only `BorrowTree`, as `vendor/lean-miri` currently has no `VClock` hook at `FnEntry` either.)
4. **LLVM `noalias` Soundness Witness (`support/probe_vclock_and_tree_borrows_fnexit.py`, Part 2B):**
   ```text
   T0: foo(&mut a); flag.store(1, Relaxed);              // raw_p = &a as *const AtomicUsize (Cell) or &raw mut a (Unique)
   T1: if flag.load(Relaxed) == 1 { (*raw_p).load(Relaxed); }
   ```
   On schedules where `foo` returns before `T1` runs, unpatched Miri **accepts** the source program for both `raw_p = Cell` sibling and `raw_p = Unique` parent, yet **rejects (`UB DataRace`)** the LLVM-optimized program that inserts a `noalias`-justified end-of-call non-atomic writeback right before `foo` returns!
5. **Required Semantic Rule:** When releasing a protector at `FnExit` on any location where `node.accessed == true`, emit `NaWrite::ProtectorEnd` into `VClock` if `protector_end_access == Some(Write)` (`Unique`), and `NaRead::ProtectorEnd` into `VClock` if `protector_end_access == Some(Read)` (`ReservedFrz`/`Frozen`, protecting `dereferenceable` speculative loads against unsynchronized `AtomicStore(Relaxed)`). Positive controls verify this rule still accepts `Mutex::unlock(Release) -> Mutex::lock(Acquire)` and unwritten `&mut AtomicUsize` (`ReservedFrz`, `accessed == false`).

---

### 3. Live `TrustedBoundary.lean` Universe Polymorphism and `@Nat.rec` Higher-Order `Send`/`Sync`

`Basis: source + execution`

Executing unmodified `TrustedBoundary.lean` (`google/zerocopy` @ `f2efbfd1eb0c`, identical to `joshlf/anneal` @ `c131b320eeeb`) on `support/Trusted/ScopeModel.lean` (`-- anneal-trust-tier: candidate:memory`, tactic-free) and `support/Anneal/ScopeConcurrencyProof.lean` (`SourceRole.theory`) under `leanprover/lean4:v4.34.1` establishes:

1. **Exact `universe u` Boundary:**
   - `"preflight"` (`allowedCommandKinds` `Lean.Parser.Command.universe`, `allowedTermSyntaxKinds` `Lean.Parser.Term.{sort,type,explicit}`) and `"audit"` (`replayOntoBase`) **admit** universe-polymorphic `theory/` declarations (`structure ViewPCM (α : Type u)`, `levelParams = [u]`), instantiated at both `Type 0` (`memViewPCM : ViewPCM Trusted.MemView`) and `Type 1` (`higherTypePredPCM : ViewPCM (Type 0 -> Prop)`).
   - Explicit universe instantiation syntax (`foo.{u}`, `Lean.Parser.Term.explicitUniv`) and compound level expressions (`u + 1`, `max u v`, `imax u v`) are **not** in `allowedTermSyntaxKinds`; helpers must use bare level identifiers/numerals (`Type u`, `Type 0`, `Sort u`) with elaborator-inferred instantiation.
   - `requireClaimProof` enforces `levelParams.isEmpty` strictly on the root claim and root theorem (`Trusted.ScopeSoundClaim` + `Anneal.scope_sound` pass with `levelParams = []`; negative controls `Trusted.BadPolyScopeClaim.{u}` and `Anneal.bad_poly_thm_for_mono_claim.{v}` are rejected with `policy:claim ... must have no universe parameters` and `policy:theorem ... must have no universe parameters`).
2. **`prelude`-Without-`Init.WF` `._unsafe_rec` Trap and `@Nat.rec` Resolution:**
   - In `trusted/lean/foundation-lock.json`, `Init.WFTactics` is private (`isExported: false`) behind `Init.Meta.Defs`. Consequently, writing a fuel-indexed recursive predicate (`SendSyncInv (fuel : Nat) ... : Prop`) via equation-compiler pattern matching compiles with exit code `0` yet synthesizes a hidden `Anneal.SendSyncInv._unsafe_rec` auxiliary (`isPartial = true`), which `"audit"` rejects (`ensureReplayableConstant`: `policy:unsafe/partial declaration Anneal.SendSyncInv._unsafe_rec`).
   - Defining `SendSyncInv` directly via primitive kernel recursion (`@Nat.rec (fun _ => Prop) True (fun k ih => tbl fid k v ∧ ih) fuel`) eliminates `._unsafe_rec` completely: `"preflight"` (`ok: true`), `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`), `"audit"` (`ok: true`, `replay: true`, `162` replayed declarations, `440` reachable declarations, axioms `['propext', 'Quot.sound']`), and `#print axioms Anneal.scope_sound` (`0` axioms; `scope_relaxed_refutes_soundness` proves weakening `Packet::drop` from `Release` to `Relaxed` fails with `exit 1` on `BogusRelaxedSound.lean`).

## Boundaries

- **Load-Buffering (`LB`) Cycles (`not examined` beyond `acyclic(sb ∪ rf)`):** `Op-SC2'` is promise-free and matches Axiomatic C++20 under `acyclic(sb ∪ rf)` (both forbid `LB+rlx (1, 1)`). Admitting out-of-order independent `LB+rlx (1, 1)` (as permitted by `ARMv8` / `RVWMO` hardware without dependencies) requires a promise-certification mechanism (`Promising 2.0` / `Weakestmo`), which is outside `Op-SC2'`.
- **Failed `compare_exchange` Split Orderings (`not examined` in `Op-SC2'`):** `support/verify_op_sc2_vs_cpp20.py` models `{load, store, successful fad RMW, fence}`; failed `compare_exchange` with distinct failure orderings behaves as a pure `load` at `failure_ord` and must be added when lifting `Op-SC2'` to full MIR atomics.
- **Random Fuzzer Per-Thread Length Bound (`execution` scope):** In `support/verify_op_sc2_vs_cpp20.py`, random fuzzing caps thread length at `k_len = 2` for 4-thread programs (`max_ins = 3` for 2T, `2` for 3T). Multi-instruction (`>= 3`) 4-thread chains are covered by the four targeted 4-thread litmus tests (`P_4_acqrel_fence`, `4T_IRIW+sc_fences`, `4T_AcqRelChain+RMW+SC`, `4T_WRC+Fsc+AcqRel`) and the closed-form inductive invariant analysis.
- **Miri `-Zmiri-tree-borrows-implicit-writes` Mode (`known not to apply` to `FnEntry` part of the witness):** Under `-Zmiri-tree-borrows-implicit-writes` (`tree_borrows/mod.rs:378`), `FnEntry` already emits `NaWriteType::Retag` on `&mut` reborrow; however, `FnExit` `NaWrite::ProtectorEnd` remains necessary whenever synchronization occurs *inside* `foo` before `FnExit`.
- **Unmodified `ScopeConcurrencyProof` Proof-Term Structure (`execution` detail):** In `support/Anneal/ScopeConcurrencyProof.lean`, `Anneal.scope_sound` discharges `Trusted.ScopeSoundClaim` via `decide` (`0` axioms) rather than invoking `scope_join_preserves_sendSyncInv`; `"audit"` independently kernel-replays all `162` declarations in the module (including `ViewPCM`, `higherTypePredPCM`, `SendSyncInv`, and `scope_join_preserves_sendSyncInv`).

## Evidence

- **Observed `2026-11-22` against `google/zerocopy` @ `f2efbfd1eb0c923aa2865e38229f72782a5aefb7` (verified `0` diff vs. `0b2ebead393851ebd9b6af76e343eea2f6fc0cba` on `TrustedBoundary.lean`, `foundation-lock.json`, and `vendor/lean-miri`):**
  - `anneal/trusted/audit/TrustedBoundary.lean` (allowed command/term syntax kinds, `ensureReplayableConstant`, `requireClaimProof`, `replayOntoBase`).
  - `anneal/trusted/lean/foundation-lock.json` (`51` foundation modules, Lean `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`; `Init.WFTactics` private).
  - `anneal/vendor/lean-miri/Miri/TreeBorrows/TreeState.lean:1036-1065` (`releaseProtector`) and `Miri/Interpreter/MachineHooks.lean:414-450`.
- **Observed `2026-11-22` against `rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da`:**
  - `compiler/rustc_target/src/spec/targets/aarch64_apple_darwin.rs:20` (`target-cpu = "apple-m1"`).
  - `compiler/rustc_ty_utils/src/abi.rs:365-376` (`noalias` + `dereferenceable` on `&mut AtomicUsize`).
  - `library/std/src/thread/scoped.rs:63-70, 160-165` (`fetch_sub(1, Ordering::Release)`).
  - `src/tools/miri/src/borrow_tracker/tree_borrows/{mod.rs:92-105, 146, 186-189, 378, 398-417; perms.rs:194-196, 208-216, 311-319; tree.rs:701-727}`, `src/tools/miri/src/borrow_tracker/mod.rs:359-397`, and `src/tools/miri/src/concurrency/data_race.rs:623-635, 716-744`.
- **Preserved Runnable Support Artifacts:**
  - `support/verify_op_sc2_vs_cpp20.py` — complete self-contained Python model checker (`15` canonical 2–3T litmus tests, `4` 4-thread litmus tests including `P_4_acqrel_fence`, `op_sc2_unpatched_bug` + 3 additional non-vacuity controls, and `150` random 2–4T differential fuzz trials).
  - `support/probe_vclock_and_tree_borrows_fnexit.py` — executable scalar-vs-`VClock` race witness and `TreeBorrows` `FnExit` `ProtectorEnd` + LLVM `noalias` writeback probe.
  - `support/Trusted/ScopeModel.lean` and `support/Anneal/ScopeConcurrencyProof.lean` — live-audited Lean 4.34.1 modules (`162` replayed declarations, `0` `._unsafe_rec`, `0` axioms on `scope_sound`).

## Revalidation

1. **Re-run Operational vs. Axiomatic `SeqCst` Model Checker (< 15 seconds):**
   ```console
   python3 -B support/verify_op_sc2_vs_cpp20.py
   ```
   Verifies `15/15` 2–3T litmus tests, `4/4` 4T litmus tests (including `P_4_acqrel_fence` and the `op_sc2_unpatched_bug` control), and `150/150` random 2–4T differential fuzz programs.
2. **Re-run Scalar-vs-`VClock` & `TreeBorrows` `FnExit` Probe (< 1 second):**
   ```console
   python3 -B support/probe_vclock_and_tree_borrows_fnexit.py
   ```
   Also diff `release_protector` / `perform_protector_end_access` in `rust-lang/miri` (`src/borrow_tracker/tree_borrows/{mod.rs, tree.rs}`) to check whether upstream Miri has added `data_race` `VClock` hooks at `FnExit`.
3. **Re-run `TrustedBoundary.lean` Audit on Lean / Policy Upgrades:**
   Compile `support/Trusted/ScopeModel.lean` and `support/Anneal/ScopeConcurrencyProof.lean` under the target `lean-toolchain` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and run `TrustedBoundary.lean` `"preflight"` + `"audit"` (`requireMirWp: false`) to check whether `universe u` admission, `explicitUniv` restrictions, or `Init.WF` visibility in `foundation-lock.json` have changed.
