# Rust Atomics, C++20 Weak-Memory Message Passing, Aliasing Models, and Operational Semantics Boundaries

## Summary

Verifying concurrent and pointer-manipulating unsafe Rust requires separating normative language rules from experimental operational models and tracking four orthogonal semantic dimensions across atomic and aliasing state machines:

1. **Authority hierarchy among the Rust Reference, Miri, MiniRust, and Unsafe Code Guidelines (UCG):** The Rust Reference is the primary normative specification for Rust, but explicitly states that its undefined-behavior (UB) inventory is non-exhaustive and that Rust's formal memory, provenance, and pointer-aliasing models remain incomplete. Miri (`src/tools/miri`) is an executable UB detector whose non-experimental checks diagnose concrete Reference violations, whereas its Stacked Borrows (default) and Tree Borrows (`-Zmiri-tree-borrows`) aliasing trackers are explicitly experimental approximations. The UCG repository (`rust-lang/unsafe-code-guidelines`) serves as an open-question forum that defers normative consensus to operational-semantics team (`t-opsem`) decisions and the Reference.
2. **Incompatibility and directionality across Stacked Borrows, Tree Borrows, and modular program logics:** Stacked Borrows (POPL 2020) and Tree Borrows (PLDI 2025, MiniRust) maintain incompatible dynamic state (`discriminator.rs` / `sb_fails.rs`: creating `&mut` from a raw pointer, reading via the raw pointer, and passing `&mut` to an empty function is UB in Stacked Borrows because the raw read pops `Unique`, whereas in Tree Borrows the unactivated child remains `Reserved` and survives the foreign read). Tree Borrows retagging further depends on `UnsafeCell` layout, `Unpin` status, function-entry protectors, and `implicit_writes`. Crucially, compiler optimization soundness proofs (`Behaviors(target) ⊆ Behaviors(source)` assuming the source has no UB) cannot be inverted to infer source UB-freedom from an optimized IR; transferring safety from a verification model $M$ to a Rust operational subject $S$ requires a safety-reflecting simulation ($\text{Safe}(M) \implies \text{Safe}(S)$).
3. **`core::sync::atomic` and C++20 (`N4868`) access-based weak-memory contracts:** Rust's atomic module adopts the C++20 memory model (`intro.races` and `atomics.order` in `cplusplus/draft@n4868`), omitting `memory_order_consume` and translating C++ object rules into byte-span accesses (so concurrent atomic and non-atomic reads of the same bytes are defined when no write conflicts). A **data race** requires conflicting unsynchronized accesses where at least one is non-atomic; conflicting unsynchronized atomic accesses avoid data races only when they target the exact same byte span and size (partially overlapping mixed-size atomic writes are UB). Read-modify-write (RMW) orderings split into load and store components (`Acquire` has a `Relaxed` store component; `Release` has a `Relaxed` load component), failed `compare_exchange` acts purely as a load, and `fence(Ordering::Relaxed)` panics.
4. **MiniRust concurrency boundary (`minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):** MiniRust's `ConcurrentMemory` defines `Atomicity::{Atomic, None}` and actively exempts pairs of `Atomic` accesses in `Access.races` and `check_data_races` (despite a stale file-header comment stating atomicity is ignored). However, `Memory::load`/`store` and `AtomicLoad`/`AtomicStore` pass `Atomicity::Atomic` to sequential memory without `Release`/`Acquire`/`Relaxed` ordering parameters or read-from supplier selection.
5. **Machine-checked Lean 4.34.1 weak-memory message-passing and operational prefix models:** Five Lean 4.34.1 modules (113 `#print axioms` audits, zero `sorryAx`) formalize a six-event two-thread message-passing litmus coupled with `MiniRustReference` raw storage checks. They prove that Release/Acquire forces observed outcome `(1, 1)` (`ra_flag_one_data_one`), Relaxed admits stale outcome `(1, 0)` (`relaxed_stale_rules`), any latest-preceding-write interleaving model (`LatestOnly`) cannot realize `(1, 0)` (`stale_not_latest`), read-from (`RF`) edges must track modifying-event identities rather than numeric values (`actual_wrong_supplier`), atomic orderings never mask raw pointer/provenance/alignment UB (`invalid_ordering_independent`), and an operational step-by-step prefix machine (`AtomicPrefixExecution`, `AtomicPrefixRules`, `AtomicPrefixCoverage`) immediately traps on earlier producer raw UB (`badD_first`) while matching the axiomatic candidate classifier on all completed `flag == 1` executions (`completed_flag_one_bridge`, `projected_sound`, `old_observed_covered`).

## Applicability

This report covers the specifications, compiler/interpreter snapshots, research papers, and Lean 4 formalizations identified in `REPORT.json`:

- **Rust compiler, standard library, and Miri (multi-version coverage):**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`): primary source for `library/core/src/sync/atomic.rs` (blob `4f2faa7e5fbd6bd7aa7377118b2e2dc1849243c5`), bundled Miri (`src/tools/miri/README.md`, `src/tools/miri/src/borrow_tracker/{stacked_borrows/mod.rs,tree_borrows/perms.rs}`).
  - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (release `1.99.1`): `library/core/src/sync/atomic.rs` (blob `71502f8d918e739c558710955e3fba31db2ad29e`, SHA-256 `cec944d1305f81be719caf639e8dce2f8aaba9a3d7751cb48f2bbf22096e4d2e`).
- **Rust Reference, C++20 Draft, and Unsafe Code Guidelines:**
  - `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` and `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` (`src/{introduction.md,behavior-considered-undefined.md,memory-model.md}`).
  - `cplusplus/draft@1f468a67c67143625d7946cdc4cfc7f7730d9160` (tag `n4868`, `source/basic.tex` blob `f078e90b7505cad0a51f896b16d12c059aca6330` and `source/atomics.tex` blob `5891afba507bda95dad2fe6b2fbe3d3a7f759891`).
  - `rust-lang/unsafe-code-guidelines@d809f91e62968913d808e53397fbcf7cea762cce` (`README.md`, `reference/src/glossary.md`).
- **MiniRust and Academic Aliasing / Concurrency Models:**
  - `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (`spec/mem/{concurrent.md,interface.md}`, `spec/lang/step/intrinsics.md`, `spec/mem/tree_borrows/{state_machine_unprotected.md,state_machine_protected.md,reborrow_settings.md}`, `tooling/minimize/tests/pass/tree_borrows/sb_fails.rs`).
  - Stacked Borrows (POPL 2020, DOI `10.1145/3371109`), Tree Borrows (PLDI 2025, DOI `10.1145/3735592`), Peterson's 2025 $\lambda_{\text{TB}}$ thesis (`sha256: e49b0d5bbd1c...`), Tas & Jacobs $\lambda_{\text{PA}}$ (`arXiv:2603.28326v1`), Drodt LAGC (`arXiv:2610.06003v1`), and Li, Beschastnikh & Summers LART (`arXiv:2610.09198v1`).
- **Lean 4 kernel verification:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`4.34.1`, `x86_64-unknown-linux-gnu`).

**Cross-version invariance vs. model differences:**
- *Invariant across `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`) and `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`), and across Reference `ad35aca48175` and `82da570bafd9`:* The adoption of C++20 `N4868` `intro.races` without `Consume`, the access-based byte-span translation, the mixed-size atomic access prohibition, the `Ordering` panic matrix on `load`/`store`/`compare_exchange`/`fence`, and the Reference's explicit statement that Rust's aliasing and weak-memory specifications remain incomplete.
- *Model-to-model variations:* Stacked Borrows, Tree Borrows (PLDI 2025 vs. Miri vs. MiniRust), $\lambda_{\text{TB}}$, and $\lambda_{\text{PA}}$ define non-equivalent state machines and accept incomparable sets of unsafe Rust programs.

## Findings

### 1. Authority Boundaries: Rust Reference vs. Miri, UCG, and Experimental Operational Models

`Basis: normative | documentation | source | derived`

At `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`src/tools/miri`), and `rust-lang/unsafe-code-guidelines@d809f91e62968913d808e53397fbcf7cea762cce`:

1. **Normative Reference scope and explicit incompleteness (`src/{introduction.md,behavior-considered-undefined.md,memory-model.md}`):**
   - The Reference defines authoritative language-level UB categories (data races, dangling/misaligned loads and stores, out-of-bounds projections, invalid typed values, ABI/unwind violations, intrinsic precondition violations, and pointer-aliasing violations) and establishes that abstract-machine bytes track initialization and optional pointer provenance.
   - However, it explicitly warns that its UB list is **non-exhaustive** and that Rust has no complete formal model deciding all pointer-aliasing, provenance, union-validity, or weak-memory edge cases.
2. **Asymmetric evidentiary value of Miri (`src/tools/miri/README.md`):**
   - Miri is an interpreter for detecting UB on single concrete executions, not the definition of Rust semantics. Passing Miri never proves a library sound across all inputs, schedules, or future compiler optimizations.
   - Miri explicitly separates definite Reference checks from **Experimental** borrow-tracking checks (`Stacked Borrows` by default, `Tree Borrows` under `-Zmiri-tree-borrows`), warning that Tree Borrows is likely more permissive than the eventual normative Rust aliasing model.
3. **Role of the Unsafe Code Guidelines repository (`README.md`, `reference/src/glossary.md`):**
   - UCG documents open operational-semantics questions and archives historical explorations; normative decisions reside in accepted `t-opsem` Final Comment Period (FCP) resolutions and the Rust Language Reference.

### 2. Aliasing Operational Models, Modular Program Logics, and Source-Safety Transfer

`Basis: source | documentation | derived`

Comparing the six aliasing and concurrency semantics subjects (`support/rust-alias-model-compatibility/coverage.json`, `support/rust-alias-model-compatibility/acquisition-notes.json`) shows why verification claims must pin their exact operational model and simulation direction:

| Model / Logic | Dynamic State & Retag Mechanism | Key Restrictions & Omissions | Proof Direction / Guarantee |
| --- | --- | --- | --- |
| **Stacked Borrows** (POPL 2020, DOI `10.1145/3371109`; Miri `stacked_borrows/mod.rs` lines 100–160) | Per-location permission stack (`Unique`, `SharedRW`, `SharedRO`, `Disabled`) + call protectors. Eagerly activates `&mut T` as `Unique`. | Rejects reading a parent raw pointer after creating an unused `&mut` child before child use (`sb_fails.rs`). | Contextual refinement for optimizations in Coq assuming source UB-freedom. |
| **Tree Borrows** (PLDI 2025, DOI `10.1145/3735592`; MiniRust `tree_borrows/state_machine_*.md`, `reborrow_settings.md` line 89) | Per-allocation borrow tree (`Reserved`, `ReservedIm`, `Unique`, `Frozen`, `Disabled`, `Cell`) + protected access history. Defers `&mut` activation until first local write. | Protected `Reserved` node that saw a foreign read rejects a later local write; skips retagging `!Unpin` mutable refs/boxes (`UnsafePinned` FIXME). | Simuliris contextual refinement assuming source has no UB (§5); accepted program set is **incomparable** with Stacked Borrows. |
| **$\lambda_{\text{TB}}$** (Peterson 2025 thesis) | Block-based value memory, explicit retagging, Iris ghost borrow trees (weakening, subtree deletion, lateral block separation). | Sequential consistency only; omits byte-level splitting and relaxed memory. Zero-size retags still require a live block. | Mechanized Rocq adequacy for value-level sequential Tree Borrows. |
| **$\lambda_{\text{PA}}$** (Tas & Jacobs `arXiv:2603.28326v1`) | Provenance + address pointers with fractional points-to and reference-ending resources. | Axiomatic proof rules only (no separate operational semantics); omits structs and recursive freezing; Tree Borrows soundness planned. | Unverified axiomatic separation logic. |
| **LAGC** (`arXiv:2610.06003v1`) & **LART** (`arXiv:2610.09198v1`) | Safe-HIR trace composition (LAGC) and monotonic waker-obligation responsiveness (LART). | Assume safe Rust borrowing/typing and compiler async lowering; omit multi-thread Tokio fairness proof (LAGC) and unsafe pointer/byte semantics. | Eventual progression / quiescent fairness under scheduler assumptions. |

- **Minimal source discriminator (`support/rust-alias-model-compatibility/discriminator.rs`, `support/rust-alias-model-compatibility/expected-model-results.json`, MiniRust `tooling/minimize/tests/pass/tree_borrows/sb_fails.rs` line 25):**
  ```rust
  let mut data = 0u8;
  let raw: *mut u8 = &mut data;
  let reference: &mut u8 = unsafe { &mut *raw }; // Retag without writing
  let _observed = unsafe { *raw };               // Foreign read through parent raw pointer
  accept_mut(reference);                         // Function-entry retag on `reference`
  ```
  Under Stacked Borrows, `*raw` pops `reference`'s `Unique` tag, so `accept_mut(reference)` triggers UB. Under Tree Borrows, `reference` starts as `Reserved`, survives the foreign read `*raw`, and enters `accept_mut` validly.
- **Why optimization refinement does not transfer source safety (`derived`):** A compiler refinement theorem proves $\text{NoUB}(S) \implies \text{Behaviors}(T) \subseteq \text{Behaviors}(S)$. When a verifier analyzes an optimized or translated target $M$ (such as MIR after optimizations or functional LLBC), proving $\text{NoUB}(M)$ does **not** imply $\text{NoUB}(S)$ because an optimization pass is allowed to erase a source UB branch. Sound verification requires a **safety-reflecting** relation ($\text{Safe}(M) \implies \text{Safe}(S)$) that preserves allocation liveness, alias tags/protectors, initialization/provenance, and fair infinite traces.

### 3. Rust `core::sync::atomic` and C++20 (`N4868`) Memory-Ordering Rules

`Basis: normative | documentation | source | derived`

Cross-referencing `library/core/src/sync/atomic.rs` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `58cf8f9c35b355199727627d07ae34a4e2846d67`, mapped in `support/rust-atomics-memory-orderings/atomic-ordering-matrix.json` and `support/rust-atomics-memory-orderings/source-map.json`) with `cplusplus/draft@1f468a67c67143625d7946cdc4cfc7f7730d9160` (`source/basic.tex` lines 5715–6229, `source/atomics.tex` lines 388–562 and 1654–1665, `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/atomic-message-passing-sources.json`) establishes the exact operational rules for Rust atomics:

1. **Access-based C++20 translation and mixed-size atomic UB (`atomic.rs` lines 25–58):**
   - Rust adopts C++20 `intro.races` without `memory_order_consume`, translating C++'s object-based rules into byte-span accesses. Concurrent atomic and non-atomic **reads** of overlapping bytes are permitted when no write conflicts.
   - Two overlapping accesses conflict if at least one is a write (a failed `compare_exchange` or `compare_exchange_weak` is a pure load, not a write). If two conflicting accesses are unordered by happens-before (`hb`), they cause a **data race (UB)** if at least one is non-atomic (`intro.races` §21), and cause **mixed-size atomic UB** even when both are atomic unless they cover the exact same byte range and size.
   - Furthermore, `Atomic*::new(v)` is **not** an atomic write (`atomics.types.operations` §3); initialization must happen-before concurrent worker accesses.
2. **Operation-specific `Ordering` decomposition and runtime panics:**

   | Operation | Accepted Orderings | Load Component | Store Component | Runtime Panic / Special Rules |
   | --- | --- | --- | --- | --- |
   | `load(order)` | `Relaxed`, `Acquire`, `SeqCst` | `order` | — | Panics on `Release` or `AcqRel`. Read-only target memory is UB except small `Relaxed` loads on supported targets. |
   | `store(val, order)` | `Relaxed`, `Release`, `SeqCst` | — | `order` | Panics on `Acquire` or `AcqRel`. Always UB on target-level read-only memory. |
   | RMW (`swap`, `fetch_*`) | `Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst` | `Relaxed` (for `Release`), `Acquire` (for `Acquire`/`AcqRel`), `SeqCst` | `Relaxed` (for `Acquire`), `Release` (for `Release`/`AcqRel`), `SeqCst` | `Acquire` does **not** release its store; `Release` does **not** acquire its load. |
   | `compare_exchange(_weak)(..., success, failure)` | `success`: all 5; `failure`: `Relaxed`, `Acquire`, `SeqCst` | `success` load half on match; `failure` on mismatch | `success` store half on match; none on mismatch | Panics if `failure` is `Release` or `AcqRel`. `_weak` may fail spuriously even when comparison bits match. |
   | `fence(order)` / `compiler_fence(order)` | `Acquire`, `Release`, `AcqRel`, `SeqCst` | Synchronizes with atomic ops | Synchronizes with atomic ops | Panics on `Relaxed`. `fence` requires atomic loads/stores to synchronize across threads; `compiler_fence` emits no CPU instruction and synchronizes only within a single hardware thread/signal handler. |

3. **Coherence and happens-before (`basic.tex` lines 5908–6197, `atomics.order` §§1–2):**
   - Each atomic byte span has a total modification order (`mo`, §4). An `Acquire` load $A$ synchronizes-with ($F \xrightarrow{\text{sw}} A$) a `Release` store $F$ when $A$ takes its value from the release sequence headed by $F$ (matching numeric bits alone do not establish $\text{sw}$; the supplying modification event identity is required).
   - Without `Consume`, happens-before (`hb`, §§9–11) is the transitive closure of sequenced-before (`sb`) and `sw`, and must be acyclic (§10). Every atomic read $R$ must take its value from a same-location modification $W$ with $\neg(R \xrightarrow{\text{hb}} W)$ (§14) and satisfy write-write (§15), read-read (§16), read-write (§17), and write-read (§18: if $W \xrightarrow{\text{hb}} R$, $R$ cannot read an `mo`-earlier write than $W$) coherence.

### 4. MiniRust Concurrency Boundary and Lean 4.34.1 Weak-Memory Verification

`Basis: source | execution | derived`

1. **MiniRust `@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` atomic boundary (`support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/atomic-message-passing-sources.json`):**
   - `spec/mem/concurrent.md` (lines 14–21, 63–86, 134–174) defines `pub enum Atomicity { Atomic, None }`. Although the file header (lines 3–4) states *"Atomicity is currently ignored"*, `Access.races` (lines 164–174) actively checks `if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic { return false; }` and `check_data_races` (lines 134–149) filters by `cur_thread` and `sync_threads`.
   - However, `ConcurrentMemory::store`/`load` delegate directly to sequential `self.memory.store`/`load`, `spec/mem/interface.md` (lines 162–167) lists `Option<Ordering>` as a future extension, and `AtomicStore`/`AtomicLoad` (`spec/lang/step/intrinsics.md` lines 430–490) ignore memory-ordering operands.
2. **Five machine-checked Lean 4.34.1 message-passing and prefix-execution modules (`support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/lean-check-results.json`, 113 `#print axioms` audits, zero `sorryAx`):**
   - The formalization models a two-thread message-passing litmus over two 2-byte atomic locations (`data` at allocation `0`, base `16`; `flag` at allocation `1`, base `32`), with initial modifications $I_{\text{data}} = 0, I_{\text{flag}} = 0$, producer thread $D: \text{data.store}(1, \text{Relaxed}); F: \text{flag.store}(1, \text{mode})$, and consumer thread $A: \text{flag.load}(\text{mode}); \text{if } A == 1 \{ B: \text{data.load}(\text{Relaxed}) \}$:

   | Lean 4.34.1 Module (`support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/`) | Audits (Axiom-Free) | Principal Verified Theorems and Controls |
   | --- | ---: | --- |
   | `AtomicMessagePassing.lean` | 28 (3) | Proves per-location `MO` totality and `HB` acyclicity (`hb_acyclic`, `no_read_hb_write`), Release/Acquire stale-read exclusion (`ra_flag_one_data_one`: $F \xrightarrow{\text{sw}} A \implies D \xrightarrow{\text{hb}} B \implies B = 1$), Relaxed `(1, 0)` admissibility (`relaxed_stale_rules` via monotone cut `relaxed_cut`), and impossibility of `(1, 0)` under any `LatestOnly` interleaving schedule (`latest_flag_one_data_one`, `stale_not_latest`). |
   | `AtomicMessagePassingControls.lean` | 37 (2) | Couples `SelectedRules` with `MiniRustReference` raw storage gates (`runCandidate`, `observed_sound`, `ra_observed_values`, `ra_no_observed_stale`, `actual_relaxed_stale`). Proves that `wrongSupplier := ⟨.dataStore, .dataStore⟩` yields numeric `(1, 1)` but fails `RFValid` (`actual_wrong_supplier = .inconsistent locations`), that zero-offset `wrappingOffset` aliasing preserves all outcomes (`alias_substitution`), and that `.noProvenance`, `.dead`, and `.misalignedLoad` fail identically across `releaseAcquire` and `relaxed` (`invalid_ordering_independent`). Also proves `zero_flag_bad_producer_outside`: static prefiltering on `flagValue == 0` returns `.outsideBranch 0` even when producer store $D$ has `.noProvenance` UB. |
   | `AtomicPrefixExecution.lean` | 13 (1) | Defines an operational step machine (`Step`) that threads actual `MiniRustReference.store` memory updates (`store_step_threads_raw`, `healthyD_actual`), transitions immediately to terminal `.ub` on any reached raw fault without future-completion prefiltering (`ub_step_iff`, `badD_first`, `badD_not_noUB`), and enforces an already-issued-write `ReadGuard` (`PrefixRules`). |
   | `AtomicPrefixRules.lean` | 20 (0) | Proves that successful stores preserve `RawLayout` (`store_preserves_info`) and `PrefixRules` unconditionally (`store_coherent`, `scheduled_store_coherent` using `zeroRF` extension), establishes `root_prefix_invariant` and `root_prefix_coherent` across all reachable states, and proves the bidirectional bridge `completed_flag_one_bridge` between completed $A = 1$ operational runs and axiomatic `SelectedRules`. |
   | `AtomicPrefixCoverage.lean` | 15 (0) | Proves partial-projection soundness (`projected_sound`, `completed_sound`), constructive 5-step producer-first coverage (`old_observed_covered`, where raw memory holds `oneBytes` `[1, 0]` at both locations even when Relaxed `RF` selects `.initialData` and binds atomic value `0`), `ra_completed_values`, and `root_flag_zero_no_B` (if $A = 0$, consumer skips $B$ and no `.read .data` attempt ever occurs in `trace`). |

## Boundaries

- **Not examined:**
  - Hardware instruction lowering (x86-TSO, ARMv8, RISC-V RVWMO), LLVM IR atomic/fence lowering, or multi-step RMW release sequences and `SeqCst` total orders in the Lean 4.34.1 model.
  - Speculative future-write / promising-semantics execution prefixes or out-of-thin-air (`atomics.order` §8) value cycles.
  - Concurrent composition of weak-memory read-from graphs with Tree Borrows alias-tree state transitions.
- **Unknown:**
  - Any formal equivalence or safety-inclusion theorem among Miri's Stacked Borrows, Miri's Tree Borrows, MiniRust's Tree Borrows, $\lambda_{\text{TB}}$, and $\lambda_{\text{PA}}$.
  - The final normative Rust memory and aliasing specification where `rust-lang/reference` (`src/memory-model.md` and `src/behavior-considered-undefined.md`) marks the rules as open.
- **Known not to apply:**
  - Compiler optimization refinements ($\text{Behaviors}(\text{target}) \subseteq \text{Behaviors}(\text{source})$ under a no-source-UB premise) do **not** transfer UB-freedom backward from an optimized model to source Rust.
  - A sequential-consistency or latest-preceding-write interleaving model (`LatestOnly`) cannot generate the C++20/Rust `Relaxed` `(1, 0)` message-passing outcome (`stale_not_latest`).
  - A non-atomic `data` payload cannot be used in the `Relaxed` `(1, 0)` message-passing litmus without causing a non-atomic data race (UB).
  - Static candidate prefiltering on `flag == 0` (`runCandidate` returning `.outsideBranch 0`) does **not** establish execution prefix safety (`NoUB`) when an earlier producer store faults (`zero_flag_bad_producer_outside`, `badD_first`).
- **Unsupported:**
  - MiniRust at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` does not support `Release`, `Acquire`, or `Relaxed` orderings in `Atomicity`, `Memory::load`/`store`, or `AtomicLoad`/`AtomicStore`.
  - `core::sync::atomic` intentionally omits C++ `memory_order_consume` and panics at runtime on `fence(Ordering::Relaxed)`, `load(Release | AcqRel)`, `store(Acquire | AcqRel)`, and `compare_exchange(..., Release | AcqRel)`.
  - In the Lean atomic-prefix study, a fourth candidate module (`AtomicPrefixControls`) failed type-checking on two `rfl` mismatches and is excluded from accepted evidence and from `support/`.

## Evidence

### Primary Upstream Sources

- **Rust Reference, Standard Library, Miri, and UCG:**
  - `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` and `82da570bafd9efed421bdbae0f8603ede8dd308b`: `src/introduction.md`, `src/behavior-considered-undefined.md` (blob `373052061c50fc2f6d1c07a91960d40bac505284`), `src/memory-model.md`.
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: `library/core/src/sync/atomic.rs` (blob `4f2faa7e5fbd6bd7aa7377118b2e2dc1849243c5`), `src/tools/miri/README.md`, `src/tools/miri/src/borrow_tracker/{stacked_borrows/mod.rs,tree_borrows/perms.rs}`.
  - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`): `library/core/src/sync/atomic.rs` (blob `71502f8d918e739c558710955e3fba31db2ad29e`, lines 25–58 and 4489–4498).
  - `rust-lang/unsafe-code-guidelines@d809f91e62968913d808e53397fbcf7cea762cce`: `README.md`, `reference/src/glossary.md`.
- **C++20 Working Draft (`cplusplus/draft@1f468a67c67143625d7946cdc4cfc7f7730d9160`, tag `n4868`):**
  - `source/basic.tex` (blob `f078e90b7505cad0a51f896b16d12c059aca6330`, lines 5715–6229: `intro.execution` and `intro.races` §§1–21).
  - `source/atomics.tex` (blob `5891afba507bda95dad2fe6b2fbe3d3a7f759891`, lines 388–562 and 1654–1665: `atomics.order` and `atomics.types.operations`).
- **MiniRust and Academic Aliasing / Concurrency Papers:**
  - `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`: `spec/mem/concurrent.md` (blob `2b3f928517be...`), `spec/mem/interface.md` (blob `dfe4e0f504fc...`), `spec/lang/step/intrinsics.md` (blob `261fe197e655...`), `spec/mem/tree_borrows/{state_machine_unprotected.md,state_machine_protected.md,reborrow_settings.md}`, `tooling/minimize/tests/pass/tree_borrows/sb_fails.rs` (line 25).
  - Stacked Borrows (POPL 2020, DOI `10.1145/3371109`), Tree Borrows (PLDI 2025, DOI `10.1145/3735592`), Peterson thesis (`sha256: e49b0d5bbd1c...`), Tas & Jacobs (`arXiv:2603.28326v1`), Drodt (`arXiv:2610.06003v1`), Li et al. (`arXiv:2610.09198v1`).

### Preserved Package Support Artifacts

- **Aliasing model compatibility and discriminator artifacts (observed 2026-10-14):**
  - `support/rust-alias-model-compatibility/discriminator.rs`
  - `support/rust-alias-model-compatibility/expected-model-results.json`
  - `support/rust-alias-model-compatibility/acquisition-notes.json`
  - `support/rust-alias-model-compatibility/coverage.json`
- **Atomic ordering matrix and source map (observed 2026-09-27):**
  - `support/rust-atomics-memory-orderings/atomic-ordering-matrix.json`
  - `support/rust-atomics-memory-orderings/source-map.json`
- **C++20 / MiniRust source inventory and Lean 4.34.1 weak-memory modules (observed 2026-10-24):**
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/atomic-message-passing-sources.json`
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/AtomicMessagePassing.lean`
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/AtomicMessagePassingControls.lean`
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/AtomicPrefixExecution.lean`
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/AtomicPrefixRules.lean`
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/AtomicPrefixCoverage.lean`
  - `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/lean-check-results.json`

## Revalidation

1. **Specification and source diffing:**
   - Diff `library/core/src/sync/atomic.rs` against `support/rust-atomics-memory-orderings/source-map.json` and `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/atomic-message-passing-sources.json` for changes to the adopted C++20 `intro.races` model, mixed-size atomic access rules, or `Ordering` panic conditions.
   - Diff `src/{behavior-considered-undefined.md,memory-model.md}` in `rust-lang/reference`, `src/tools/miri/README.md`, and `src/tools/miri/src/borrow_tracker/` in `rust-lang/rust`, plus MiniRust's `spec/mem/{concurrent.md,interface.md,tree_borrows/}` and `spec/lang/step/intrinsics.md`.
2. **Re-running the Stacked Borrows vs. Tree Borrows discriminator under Miri:**
   ```bash
   miri support/rust-alias-model-compatibility/discriminator.rs
   miri -Zmiri-tree-borrows support/rust-alias-model-compatibility/discriminator.rs
   ```
   Confirm that default Stacked Borrows rejects `discriminator.rs` on `accept_mut(reference)` after the raw read `*raw`, while `-Zmiri-tree-borrows` accepts it (`support/rust-alias-model-compatibility/expected-model-results.json`).
3. **Re-running the five Lean 4.34.1 weak-memory and prefix-execution modules:**
   ```bash
   # With base modules MiniRustReference and Execution compiled on LEAN_PATH:
   for mod in AtomicMessagePassing AtomicMessagePassingControls AtomicPrefixExecution AtomicPrefixRules AtomicPrefixCoverage; do
     lean -j1 -M2048 -o "./build/AnnealResearch/${mod}.olean" \
       "support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/${mod}.lean"
   done
   ```
   Verify exit code `0`, zero warnings, and `.olean` digests and `#print axioms` outputs matching `support/rust-cpp20-weak-memory-views-and-minirust-atomic-concurrency/lean-check-results.json`.
