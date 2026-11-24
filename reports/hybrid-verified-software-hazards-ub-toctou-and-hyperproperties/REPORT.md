# Hybrid Verified Software Hazards: In-Process `unsafe` UB, Safe-Rust TOCTOU, Checker-Spec Drift, and Hyperproperty Leakage Limits

## Summary

Pairing an unverified producer with a formally verified runtime certificate checker eliminates producer logic bugs *only* for first-order functional safety properties and *only* when the runtime memory and timing seam between producer, checker, and consumer is properly sealed. Mechanizing four hazard classes in Lean `v4.34.1` ([`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean), `361` lines, `8` theorems, `0` `sorryAx`) and executing concrete Rust/Miri probes ([`support/hazard_probes/src/lib.rs`](support/hazard_probes/src/lib.rs), `rustc 1.102.0-nightly` / `miri 0.1.0`) establishes four sharp boundaries:

1. **In-Process `unsafe` UB Invalidates Verified Safe Checkers:** In Rust, an untrusted in-process producer containing `unsafe` code cannot be contained by a post-execution safe checker. Under Miri (both Stacked Borrows and `-Zmiri-tree-borrows`), `unsafe_aliasing_post_check_bypass` (holding an aliased `*mut u64` while lending `&u64` to the checker and writing `999` afterward) triggers fatal Undefined Behavior (`read access ... is forbidden`, state `Disabled`), and `unsafe_invalid_bool_probe` triggers `constructing invalid value of type bool: encountered 0x02`—while `cargo test --release` compiles and passes both silently. In-process unverified Rust producers therefore **require** `#![forbid(unsafe_code)]` (plus zero unvetted `unsafe` dependencies / proc-macros / `build.rs`), or else OS-process / Wasm / hardware-enforced memory isolation.
2. **Safe-Rust TOCTOU, Trait-Contract Spoofing, and Unwind Pollution (`#![forbid(unsafe_code)]` Alone Is Insufficient):** Even inside `#![forbid(unsafe_code)]` safe Rust, three non-`unsafe` mechanisms bypass naive checkers:
   - *Interior-mutability TOCTOU:* `naive_check_cell_lt_100(&Cell<u64>)` checks `< 100` (`true`), after which safe code sets the `Cell` to `999`. Linear ownership snapshot sealing (`CertifiedU64Lt100::check_cell`) copies `let snap = x.get()` into a private owned newtype prior to checking, closing TOCTOU (`toctou_post_check_mutation_unsound_vs_sealed`).
   - *Adversarial generic trait implementations:* `generic_is_sorted<T: Ord>(&[T])` accepts an unsorted `[100, 1]` `TrojanOrd` array whose `Ord::cmp` flips behavior via `Cell<bool>` after checking, demonstrating that verified checkers must bind concrete primitive/sealed types (`concrete_u64_is_sorted`) or require verified trait laws.
   - *Mutable-borrow panic pollution:* Passing `&mut LedgerState` into `catch_unwind` leaves `st.balance = 0` corrupted after a panic before fallback (`naive_mut_catch_unwind_with_fallback`), whereas read-only `&LedgerState` or cloned-snapshot execution preserves `100` on panic.
3. **Three Hyperproperty Leakage Channels Survive a `100%` Verified Functional Checker (`HybridHyperproperties.lean`):**
   - *Channel 1 (`Some`/`None` decision leakage, `option_decision_channel_leaks_despite_sound_checker`):* Returning `some` iff `secret = false` passes a `100%` sound checker while leaking `1 bit/call` via `Option` discriminants. **Closed by** deterministic total fallback (`fallback_deterministic_closes_option_channel`).
   - *Channel 2 (Relational witness steganography, `nondet_rel_allows_witness_steganography_despite_total_checker`):* Even with `100%` availability (`0` fallbacks, `0` `None`), any relational spec admitting `≥ 2` valid outputs (`y = p ∨ y = p + 1`) lets an untrusted producer encode secret bits into which valid output it submits. **Closed by** making the outer specification deterministic on public inputs (`unique_spec_blocks_witness_steganography`).
   - *Channel 3 (Timing and resource-consumption leakage, `timing_channel_survives_deterministic_total_spec`):* Even under a strictly deterministic functional spec and total fallback, an untrusted producer taking `1` step vs `100` steps leaks secrets via runtime duration. **Closed only by** fixed-budget padded execution (`padded_deterministic_hybrid_noninterferent`) or secret-blind/isolated producer execution.
4. **Derived-Field Trust (`I2`) vs. Zero-TCB Spec Equivalence (`derived_field_trust_vs_recomputing`):** A checker that reads a producer-supplied summary field (`claimedSum`) rather than recomputing from primary witness data accepts forged invalid bundles (`[50, 50]` claiming `sum = 0 <= 10`). Proving `checker x y w = true -> Spec x y` in Lean 4 directly eliminates checker-to-spec drift and derived-field shortcuts from the TCB.

*Model–system relation note:* The theorems in [`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean) model abstract functions, deterministic/padded step counts, and snapshot sealing in pure Lean 4; physical microarchitectural cache/speculative side channels and multi-threaded OS scheduling are outside the Lean model (`Basis: derived (modeling bridge)`).

## Applicability

- **Lean 4.34.1 mechanization (`support/HybridHyperproperties.lean`, `support/lakefile.toml`, `support/lean-toolchain`):** Checked directly with `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), core `Init` only (`0` external deps, `0` warnings, `0` `sorryAx`, `0` `Lean.ofReduceBool`).
- **Rust and Miri execution probes (`support/hazard_probes/`):** Compiled and executed with `rust-lang/rust` `rustc 1.102.0-nightly` / `miri 0.1.0` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) on `x86_64-unknown-linux-gnu` under debug, `--release`, default Miri (Stacked Borrows), and `-Zmiri-tree-borrows`.
- **Relationship to sibling corpus reports:** Complements `refinement-and-hyperproperties-noninterference-and-randomness` (general `GNI` / `ObsDet` trace-inclusion paradoxes), `compiler-preservation-time-protection-and-anneal-ct-certificates-2018-2026` (Ring-0 CT preservation and `Time Protection`), `non-quorum-kernel-confidence-trace-downtranslation-and-guard-mutation` (derived-field invariant `I2` in proof checkers), `safe-trait-adversarial-implementations-coherence-and-soundness-boundaries`, and `hybrid-verified-software-contracts-fallback-and-ratcheting`. This report synthesizes the specific **in-process Rust memory/TOCTOU/trait boundary** and the **3-channel hyperproperty taxonomy for certificate-checked `Option<T>` / fallback components**.

## Findings

### 1. In-Process `unsafe` Producers Break Safe Checkers (`cargo test --release` vs. `miri`)

`Basis: source + execution` ([`support/hazard_probes/src/lib.rs`](support/hazard_probes/src/lib.rs))

If an untrusted producer runs in the same address space as a verified Rust checker and contains even a single `unsafe` block, checking its return value in safe Rust **does not** restore memory safety or functional soundness:

| Probe (`support/hazard_probes/src/lib.rs`) | Mechanism | `cargo test --release` | Miri (`Stacked` & `-Zmiri-tree-borrows`) |
| :--- | :--- | :--- | :--- |
| **`unsafe_aliasing_post_check_bypass`** (`L119-133`) | Producer allocates `Box`, creates `&u64` for checker (`*shared_ref < 100` -> `true`), then mutates via aliased `*mut u64` (`*raw = 999`) before downstream read | **Compiles cleanly (`0` warnings) & passes test** (`observed == 999` after `checked == true`) | **Rejected as fatal UB:** Stacked Borrows `<141476>` invalidated by write; Tree Borrows `<138648>` state `Disabled` forbids read at `src/lib.rs:128:20` |
| **`unsafe_invalid_bool_probe`** (`L137-142`) | Producer constructs `transmute::<u8, bool>(2u8)` (`forged as u8 == 2`) | **Compiles cleanly & passes** (`branch_taken == true`) | **Rejected as fatal UB:** `constructing invalid value of type bool: encountered 0x02, but expected a boolean` at `src/lib.rs:139:33` |

**Implication (`Basis: derived`):** For an untrusted producer to execute *in-process* alongside a verified checker in Rust, **the producer crate/module must enforce `#![forbid(unsafe_code)]`** (verified by `TrustedBoundary` / build policy with zero unverified `unsafe` dependencies, proc-macros, or `build.rs` scripts). Otherwise, the producer must execute across an OS process, hardware capability, or Wasm isolation boundary (`google/zerocopy@7527dd2b` `anneal/THREAT_MODEL.md`).

---

### 2. Safe-Rust TOCTOU, Trait Spoofing, and Unwind Pollution (`#![forbid(unsafe_code)]`)

`Basis: source + execution` ([`support/hazard_probes/src/lib.rs`](support/hazard_probes/src/lib.rs), `L14-114, 150-204`; [`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean), `L321-355`)

All three safe probes below live inside `pub mod safe_boundary { #![forbid(unsafe_code)] ... }` and pass `cargo miri test` cleanly with `0` UB—proving that safe Rust's type system alone still permits checker bypasses unless three defensive patterns are applied:

1. **Interior-Mutability TOCTOU (`naive_check_cell_lt_100` vs. `CertifiedU64Lt100::check_cell`):**
   - Checking `&Cell<u64>` (or `&AtomicU64` / `&RefCell<T>`) validates only the point-in-time read; safe code or concurrent threads can mutate the cell immediately after checking (`10` -> `999`).
   - **Fix (`CertifiedU64Lt100`, `L22-37`):** Copy out a frozen value snapshot (`let snap = x.get();`) into an owned immutable private-field newtype *before* checking (`toctou_post_check_mutation_unsound_vs_sealed`, `HybridHyperproperties.lean:329-355`, axioms `[propext]`).
2. **Adversarial Generic Trait Implementations (`generic_is_sorted` vs. `concrete_u64_is_sorted`):**
   - In `test_safe_trojan_ord_bypasses_generic_checker` (`L166-176`), `TrojanOrd` uses `Cell<bool>` inside `Ord::cmp` so `generic_is_sorted::<TrojanOrd>(&[100, 1])` returns `true` while the underlying payloads `[100, 1]` are unsorted.
   - **Fix:** Checkers must accept concrete sealed/primitive representations (`&[u64]`, `&[u8]`) rather than generic unverified `T: Ord` / `T: PartialEq` / `T: Deref` bounds unless the trait implementation itself carries a verified `Ord` law contract.
3. **Mutable-Borrow Panic Pollution (`naive_mut_catch_unwind_with_fallback` vs. `snapshot_isolated_with_fallback`):**
   - Even when `std::panic::catch_unwind` catches an untrusted producer panic and invokes a verified fallback (`L83-97`), passing `&mut LedgerState` allows the producer to corrupt `st.balance` from `100` to `0` prior to panicking. Passing read-only `&LedgerState` (with state updates performed solely in the verified commit/fallback branch) preserves `100` across arbitrary producer panics.

---

### 3. Three Hyperproperty Leakage Channels Surviving Verified Checkers

`Basis: execution (Lean 4 v4.34.1 kernel check)` ([`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean), `L17-278`)

Let inputs decompose into public `p : L` and secret `s : H`. Even when a formally verified checker `V` guarantees `100%` functional soundness (`CheckerSound R V : ∀ p y w, V p y w = true → R p y`), three orthogonal information-flow channels remain open unless closed systematically:

| Leakage Channel | Active When | Lean 4 Counterexample Theorem (`Axioms`) | Necessary & Sufficient Closure | Lean 4 Closure Theorem (`Axioms`) |
| :--- | :--- | :--- | :--- | :--- |
| **1. `Some`/`None` Decision Channel** | `Option<Y>` return exposes checker rejection / `None` to callers | `option_decision_channel_leaks_despite_sound_checker` (`[propext]`) | Mask rejections via **total verified fallback** + deterministic spec `R` | `fallback_deterministic_closes_option_channel` (`[]`) |
| **2. Relational Witness Steganography** | Spec `RelSpec p y` admits $\ge 2$ valid outputs `y₀ ≠ y₁` (`100%` accepted, `0` fallbacks) | `nondet_rel_allows_witness_steganography_despite_total_checker` (`[propext, Classical.choice, Quot.sound]`) | Require **public-input uniqueness** (`∀ p y₁ y₂, RelSpec p y₁ → RelSpec p y₂ → y₁ = y₂`) or canonicalization | `unique_spec_blocks_witness_steganography` (`[]`) |
| **3. Execution Timing / Resource Channel** | Producer step count / latency / cache footprint depends on `s` before checker runs | `timing_channel_survives_deterministic_total_spec` (`[propext]`) | **Secret-blind isolation** (don't pass `s` to untrusted producer) OR **fixed-budget padded / constant-time envelope** | `padded_deterministic_hybrid_noninterferent` (`[]`) |

**Key Architectural Insight (`Basis: derived`):** Notice the sharp hierarchy:
- **Functional soundness** requires only a sound checker `V`.
- **1-bit output-presence privacy** requires `verify_or_fallback` (eliminating `None`).
- **Full output noninterference** additionally requires **functional determinism of the specification** (`ContractDeterministic` in `Anneal.Core.SpecRealizability`); otherwise, any slack in a relational postcondition (e.g., tie-breaking in compression match selection, shortest-path equal-cost parent choices, or instruction scheduling order) gives an untrusted producer an uncheckable covert channel!
- **Full timing/microarchitectural noninterference** cannot be enforced by *any* post-hoc output checker at all; it requires **secret-independent producer inputs** or **constant-time / padded-budget / spatial-temporal isolation** (consistent with `Time Protection`).

---

### 4. Checker-to-Specification Drift and Derived-Field Trust (`I2`)

`Basis: execution (Lean 4 v4.34.1 kernel check)` ([`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean), `L282-319`)

In `derived_field_trust_vs_recomputing` (`L305-319`, axioms `[propext]`):
- When a witness bundle includes a producer-computed summary field (`CertWithDerived.claimedSum`) alongside primary witness elements (`elems`), a checker that validates `claimedSum ≤ bound` (`buggyTrustingChecker`) accepts the forged certificate `{ elems := [50, 50], claimedSum := 0 }` under `bound = 10`, whereas `recomputingChecker` (`listSum c.elems ≤ bound`) proves `trueSpec bound c` directly.
- Generalizing to Lean 4 / Anneal: stating and kernel-checking `checker x y w = true -> Spec x y` directly against the human-audited declarative `Spec` (rather than auditing `checker` informally) prevents omitted side conditions, unvalidated derived fields, and silent semantic drift between the outer spec and the runtime checker.

## Boundaries

- **Single-step functional/step model in Lean:** [`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean) models single-invocation public/secret pairs `(p : L, s : H)` and discrete step budgets `TimedOut`. Microarchitectural cache eviction, speculative execution (`Spectre`), hardware power/EM side channels, and concurrent multi-threaded preemption between producer and fallback are **not** formalized in the Lean file (`not examined`).
- **Local Miri coverage vs. compiler optimization exploits:** `cargo miri test` verifies deterministic abstract-machine UB detection on the specific `unsafe_aliasing_post_check_bypass` and `unsafe_invalid_bool_probe` triggers; exact miscompilation behavior under other `rustc` flags, target triples, or LTO configurations varies across LLVM passes (`unknown` across arbitrary targets).
- **Safe Rust memory exhaustion / stack overflow:** Even `#![forbid(unsafe_code)]` with snapshot-sealed `CertifiedU64Lt100` cannot prevent `abort` on OOM (`alloc::handle_alloc_error`) or stack overflow on unbounded recursion inside the same OS process (`unsupported` in-process without fallible allocation or OS/Wasm containment).

## Evidence

- **Standalone Lean 4.34.1 mechanization (preserved in package `support/`):**
  - [`support/HybridHyperproperties.lean`](support/HybridHyperproperties.lean) (`361` lines, SHA-256 `6a85901e1c5c653711af04a5eb9af80e8db3b8b04bcd758186960528a2e87cfa`), [`support/lakefile.toml`](support/lakefile.toml), [`support/lean-toolchain`](support/lean-toolchain).
  - Checked via `elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridHyperproperties.lean` on `2026-11-24` (exit `0`, zero warnings): `3` theorems use zero axioms `[]` (`fallback_deterministic_closes_option_channel`, `unique_spec_blocks_witness_steganography`, `padded_deterministic_hybrid_noninterferent`), `4` use `[propext]` (`option_decision_channel_leaks_despite_sound_checker`, `timing_channel_survives_deterministic_total_spec`, `derived_field_trust_vs_recomputing`, `toctou_post_check_mutation_unsound_vs_sealed`), and `1` uses `[propext, Classical.choice, Quot.sound]` (`nondet_rel_allows_witness_steganography_despite_total_checker`). Zero `sorryAx` or `Lean.ofReduceBool`.
- **Standalone Rust + Miri probes (preserved in package `support/hazard_probes/`):**
  - [`support/hazard_probes/Cargo.toml`](support/hazard_probes/Cargo.toml) and [`support/hazard_probes/src/lib.rs`](support/hazard_probes/src/lib.rs) (SHA-256 `a5c6fce0d4cc919ccb9e12ce247284d649f51b1e796829374bf4fd7e0943cf93`).
  - Executed `2026-11-24` under `rustc 1.102.0-nightly` / `miri 0.1.0 (3ef0c22cdb 2026-11-11)`:
    - `cargo test --offline`: `3 passed; 0 failed; 2 ignored`.
    - `cargo test --release --offline -- --include-ignored`: `5 passed; 0 failed` (demonstrating silent release compilation & execution of the `unsafe` probes).
    - `cargo miri test --offline`: `3 passed; 0 failed; 2 ignored` (`0.53s`).
    - `cargo miri test --offline ub_aliasing_bypass_detected_by_miri -- --ignored` (default Stacked Borrows & `MIRIFLAGS="-Zmiri-tree-borrows"`): rejected with exact aliasing UB at `src/lib.rs:128:20`.
    - `cargo miri test --offline ub_invalid_bool_detected_by_miri -- --ignored`: rejected with `constructing invalid value of type bool: encountered 0x02` at `src/lib.rs:139:33`.

## Revalidation

From `reports/hybrid-verified-software-hazards-ub-toctou-and-hyperproperties/support/`:

1. Verify all 8 Lean `v4.34.1` theorems and axiom footprints:
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridHyperproperties.lean
   ```
2. Verify safe probes pass Miri while deliberate `unsafe` producer bypasses fail closed under Miri:
   ```bash
   cd hazard_probes
   cargo miri test --offline
   ! MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test --offline ub_aliasing_bypass_detected_by_miri -- --ignored
   ! cargo miri test --offline ub_invalid_bool_detected_by_miri -- --ignored
   ```
