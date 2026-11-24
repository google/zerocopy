# Epistemology and Defense-in-Depth Soundness Architecture for AI-Accelerated Operational Semantics

## Summary

Evaluating the soundness of a formal program verifier by *who authored its operational semantics* (human specialists versus AI agents) fails on both empirical and logical grounds. Historically, every major C and Rust verification stack—including CompCert's unverified front-end parser and elaborator, Verus, Kani, Creusot, Prusti, Aeneas/Charon, RefinedRust, Miri, and single-kernel binary `.olean` loaders—has suffered real soundness defects in handwritten front-ends, extraction passes, or semantic encodings. Logically, positive deductive verification ($\text{Program} \wedge \text{Pre} \vdash \neg\text{UB} \wedge \text{Post}$) is monotone under weakening undefined-behavior ($\text{UB}$) checks or narrowing $\text{Pre}$: omitting a UB guard leaves every existing positive proof green while unsoundly accepting broken code. Conversely, AI-authored operational semantics *without* independent external oracles fails due to correlated blind spots—illustrated when a standalone concrete Rust MIR stepper derived from Anneal's specification reproduced the exact zero-sized memory alignment bypass (`size == 0` returning prior to `isAligned`) present in `anneal/trusted/lean/Trusted/MirSemantics/Memory.lean`.

Soundness is instead a property of a **two-sided, non-AI-anchored evidence graph** combined with radical fail-closedness (returning `unsupported` on unmodeled constructs never produces a false certificate, whereas silent under-approximation does). Measured against `google/zerocopy@706acd8761d7d8da4be9fc72f280931f75f7d837` (`anneal-v0.2.0-alpha.11`), Anneal anchors AI-accelerated operational semantics across six orthogonal defense layers:

1. **Mechanized reference correspondence (`proofs-rs/lean-miri@c92d1d9754c9`):** `37` kernel-checked correspondence claims over `160` vendored execution-machine modules (`24,415` lines in `anneal/correspondence/`), establishing both forward simulation and bidirectional fault equivalence (`.undefined ↔ .ub`) and pinpointing the exact `rustc_const_eval` zero-sized place alignment rule (`alignment-only` at `size == 0`, even on deallocated metadata, without liveness/bounds/mutability checks).
2. **Independent concrete execution oracles (`rust-lang/rust@49d734536222` Miri suite):** Differential execution pairing a zero-TCB `#![no_std]` schema-v4 MIR evaluator against live `miri 0.1.0` across upstream Miri's `644` negative UB test files (`549` `fail/` + `95` `fail-dep/`) and `447` `pass*` files; a `19`-test live canary recorded **`0 / 19` unsound accepts** (`2` caught as UB, `16` rejected fail-closed as unsupported across capture/eval, `1` rejected by `rustc` const-eval).
3. **Two-sided semantic mutation testing and historical bug refutations:** `48` active CI guards in `anneal/ci/check_guard_mutation.py` (`100%` required kill rate), `100` `#[test]` boundary tests, and `<2s` `[propext]`-only kernel refutations (`¬ Expected.claim`) on verbatim historical open-source bugs (`RustCrypto/block-ciphers@2d7f6eb8` and `tokio-rs/bytes@79fb8532`).
4. **Pre-optimization capture-seam grounding:** Exhaustive `Runtime(PostCleanup)` MIR extraction via `mir_drops_elaborated_and_const_checked` with `-Zmir-preserve-ub` (preventing the `32.8%` `PlaceMention` UB-check erasure observed after `optimized_mir`), pinned `rust-lang/rust` commit citations, and optional post-MIR translation validation (`Trusted.MirSemantics -> -O3 LLVM IR -> ELF64`).
5. **Minimal human-auditable TCB, multi-kernel NDJSON replay, and a profile-parametric verification envelope:** `86.8%` of Anneal's Lean codebase (`103,592` code lines in `theory/` and `correspondence/` vs `15,703` code lines in `trusted/`, a **`6.60 : 1` `0`-TCB ratio**) cannot introduce unsoundness, leaving a **`5,621`-line** core Profile v1 AST/model/semantics readable by human auditors, paired with `ExecSeal` (`linux_bwrap`), dual-kernel NDJSON proof replay (`nanoda_bin` + `con-ron`), and a **`~230`-line kernel-checked `VerificationEnvelope` spine** ([`support/FrameworkEnvelopeSketch.lean`](support/FrameworkEnvelopeSketch.lean)) that enforces constructive domain non-vacuity, external-stub realizability, upper-triangular oracle claim licensing, and mandatory gap disclosure in `Expected.claim`.
6. **Separation of defect filters from trust anchors:** Cross-family automated code review is strictly treated as a pre-merge bug filter—never a soundness axiom—complemented by human TCB ownership, external verifier auditing, and deterministic Miri-gated soundness bug bounties.

## Applicability

These findings apply to `anneal/` in `google/zerocopy@706acd8761d7d8da4be9fc72f280931f75f7d837` (`anneal-v0.2.0-alpha.11`), evaluated against:

- **`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`**, vendored under `anneal/vendor/lean-miri/` (`608` `.lean` files, `160` modules in `execution_machine_closure`, `13` SHA-256-locked compatibility patches in `anneal/trusted/audit/src/miri_pin.rs:46-60`);
- **`rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da`** (`src/tools/miri/tests/`), executed under `miri 0.1.0 (6905905bb7 2026-11-19)` (`nightly-2026-11-20`, `-Zmiri-tree-borrows`) for concrete UB oracle classification and canary testing;
- **`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`** (`1.98.0-nightly`, `2026-05-30` / toolchain `nightly-2026-05-31`, LLVM `22.1.6`) for `anneal-rustc-capture`, and **`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`** (`compiler/rustc_const_eval/src/interpret/`) for normative interpreter memory/alignment semantics; and
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`** (`v4.34.1`), used to elaborate and kernel-check both `anneal/` and the standalone [`support/FrameworkEnvelopeSketch.lean`](support/FrameworkEnvelopeSketch.lean) specification.

The epistemological analysis, monotone vacuity laws, zero-sized place alignment rules, and `VerificationEnvelope` type discipline apply broadly to deductive program verifiers whose operational semantics or proof automation are co-developed with automated synthesis agents. Exact line counts, file inventories, and open boundary items apply specifically to `google/zerocopy@706acd8761d7d8da4be9fc72f280931f75f7d837`.

## Findings

### 1. Epistemological Grounding: Why Evidence Graphs Dominate Author Provenance

1. **Documented soundness bugs across human-authored verifiers and reference interpreters.** Inspection of published compiler-testing studies and public upstream issue trackers (`2026-11-23`) demonstrates that human authorship is neither necessary nor sufficient for semantic soundness across >100 MIR constructs, aliasing rules, and target ABIs:
   - *Unverified front-end and extraction seams:* In CompCert (`AbsInt/CompCert@2685140bf7`), CSmith random differential testing (Yang et al., PLDI 2011) found `0` wrong-code bugs in the Rocq-verified middle-end and back-end passes while discovering multiple wrong-code bugs in the unverified `3,377`-line OCaml C front-end/elaborator (`Lexer.mll`, `pre_parser.mly`, `Elab.ml`) and ABI model. Analogously, RefinedRust (Zenodo `21636474`) pairs foundational Rocq Iris proofs (`caesium`/`lithium`) with an unverified `refinedrust-rustc` MIR-to-Rocq translator and `#[rr::trust_me]` body elision, while Aeneas and Charon (`AeneasVerif/aeneas`, `AeneasVerif/charon`) exhibit open/historical soundness gaps where custom `Drop` destructors are omitted (`AeneasVerif/aeneas#1410`), interior-mutable `Cell::set` / `Atomic*::fetch_add` calls through `&self` are modeled as pure (`AeneasVerif/aeneas#1525`), array axioms are unsound (`AeneasVerif/aeneas#1116`), or `unsafe` indexing is mis-translated (`AeneasVerif/charon#583`).
   - *Ghost-dialect, contract-encoding, and SMT-lowering seams:* Public trackers record `16` open and `127` closed soundness issues in Verus (`verus-lang/verus`, including five `proves false` defects closed in Nov 2026: `verus-lang/verus#3567` ghost closure read bypassing live `&mut`, `#3565` dropped state-machine `let` binding, `#3564` tokenized state-machine instance construction, `#3502` `dyn` supertrait positivity miss, and `#3498` recursive termination ignoring type arguments), `57` open and `50` closed `[F] Soundness` issues in Kani (`model-checking/kani`, including `#5094` `#[kani::stub]` silently skipped on MIR-inlined `-O2/-O3` calls, `#5212` `should_panic` masking failed assertions under `--prove-safety-only`, and `#4757` vacuous constructors), `4` open and `28` closed soundness issues in Creusot (`creusot-rs/creusot`, e.g., `#2367` proving `ensures(false)` after `0u8.leading_ones()` and `#2368` `saturating_div`/`Ord::min` specification drift), and `4` open and `5` closed soundness issues in Prusti (`viperproject/prusti-dev`, e.g., `#1505` signed division and `#1501` signed discriminant encoding). Across six peer Rust verification tools (Verus, Kani, Aeneas, Creusot, Prusti, Flux), `0 / 6` advertise an independent third-party security audit of the verifier itself.
   - *Reference-oracle and kernel deserialization bugs:* Upstream Miri (`rust-lang/miri`) has tracked subtle UB corner-case omissions (`rust-lang/miri#5543` Tree Borrows wildcard assertion failure, `#5320` `2.0f64.powi(63)` rounding missing `float_to_int_unchecked` UB, `#4189` missed by-move argument UB, `#4995` `f32::trunc(NaN)` x86 divergence), and Lean 4 (`leanprover/lean4`) fixed both wrong-structure projection soundness (`leanprover/lean4#14576`) and binary `.olean` cached metadata trust (`leanprover/lean4#16690`, reducing `leanchecker` to text-level `--from-export` replay).
   `Basis: source + documentation`

2. **One-sidedness of positive verification and correlated synthesis blind spots.**
   - *Monotone lattice collapse:* Positive safety theorems ($\forall q,\, \text{Dom}(q) \wedge \text{Pre}(q) \implies \text{WellFormed}(P, q) \wedge \text{Post}(P, q)$) hold trivially whenever $\text{Dom}(q) \wedge \text{Pre}(q)$ is unsatisfiable ($\text{LHS} = \bot$) or whenever $\text{WellFormed}$ omits a UB transition ($\text{RHS}$ weakened). Positive verification suites alone never detect a missing UB rule.
   - *Correlated tool blind spots:* An untrusted `#![no_std]` concrete Rust MIR evaluator authored to mirror `Trusted.MirSemantics` independently implemented `if size == 0 { return Ok(Vec::new()); }` and `if bytes.is_empty() { return Ok(()); }` *before* checking pointer alignment—propagating the exact `size == 0` alignment bypass present in `anneal/trusted/lean/Trusted/MirSemantics/Memory.lean:207, 231`. Only cross-checking against **independent, non-AI-authored oracles** (`proofs-rs/lean-miri`, upstream `cargo miri`, and `rustc_const_eval`) exposes shared specification blind spots.
   - *Fail-closed asymmetry as a speed multiplier:* Because rejecting an unmodeled MIR construct (`status: "unsupported"`) causes safe abstention rather than a false proof, pairing fail-closed extraction with mechanized `lean-miri` correspondence, Miri differential suites, and AST mutation killing allows rapid automated development of `0`-TCB proof automation without expanding semantic risk.
   `Basis: source + derived`

### 2. Measured TCB Separation on `google/zerocopy@706acd8761d7`

Direct enumeration of `anneal/` at `google/zerocopy@706acd8761d7d8da4be9fc72f280931f75f7d837` establishes a **`6.60 : 1` code-line ratio** (`86.8%` vs `13.2%`) between `0`-TCB kernel-checked Lean modules and Trusted Lean modules:

| Trust Zone | Subtree | `.lean` Files | Total Lines | Non-Blank/Non-Comment Code Lines | Soundness Role |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **Pass-1 TCB Semantics** | `anneal/trusted/lean/` | `19` | `6,428` | `5,591` | `MirAst*` (`1,164`L), `MirModel.lean` (`267`L), `MirSemantics*` (`4,977`L incl. `787`L `CanaryFixtures.lean`) + `Trusted.lean` (`20`L) $\implies$ **`5,621` total lines** of core Profile v1 AST, model, and semantics |
| **Pass-2 TCB Bridge** | `anneal/trusted/correspondence/` | `7` | `4,251` | `3,900` | `Correspondence.lean` (`692`L locking `37` claims) + `Codec`, `Config`, `Eval`, `Simulation`, `State`, `CanaryFixtures` |
| **Audit Boundary TCB** | `anneal/trusted/audit/` | `1` | `6,620` | `6,212` | `TrustedBoundary.lean` JSON IPC inspector |
| **Subtotal: Trusted Lean** | `anneal/trusted/{lean,correspondence,audit}` | **`27`** | **`17,299`** | **`15,703`** | **All Trusted Lean (`13.2%` of Anneal Lean code lines)** |
| **Untrusted Automation** | `anneal/theory/` | `77` | `86,811` | `80,208` | `0`-TCB (`MirWp`, `LinearArith`, `BitTrieLrat`, `SpineForce`, `ClassicalEm`, `InitLemmas`, `Firewall`) |
| **Untrusted Refinement** | `anneal/correspondence/` | `16` | `24,415` | `23,384` | `0`-TCB simulation and fault-equivalence proofs against `vendor/lean-miri` |
| **Subtotal: `0`-TCB Lean** | `anneal/{theory,correspondence}` | **`93`** | **`111,226`** | **`103,592`** | **Zero-TCB Lean (`86.8%` of Anneal Lean code lines; `6.60 : 1` over Trusted Lean)** |

On the Rust host side (`32` `.rs` files, `44,585` total lines across `trusted/audit` `5,335`L, `trusted/rustc-capture` `11,075`L, and `trusted/cargo-anneal` `28,175`L), `anneal/Cargo.toml:11-25` and `check_cargo_boundary` enforce a strict two-zone DAG (`Zone::Trusted = 0 < Zone::Tests = 1`) backed by `100` `#[test]` functions (`13,941` lines in `anneal/tests/audit/tests/`). Replacing in-process `.olean` binary loading (`leanprover/lean4#16690`) with text-level NDJSON export replayed by two independent pure-Rust typecheckers (`nanoda_bin` and `con-ron`) reduces runtime Lean audit TCB from `4,369` to `1,169` LOC (`-73.2%`) while completing dual-kernel replay in `2.411s`.
`Basis: source + execution`

### 3. Layer 1 (`lean-miri` Correspondence) and the Zero-Sized Place Alignment Law

1. **Profile v1 correspondence baseline.** `anneal/trusted/correspondence/Trusted/Correspondence.lean` locks `37` `*Claim` theorems connecting `Trusted.MirSemantics.evalStep` to SHA-locked `proofs-rs/lean-miri@c92d1d9754c9` (`160` modules in `execution_machine_closure`), checked via `anneal-audit --require-correspondence` and recorded in Receipt v3 `correspondence_provenance` (`anneal/trusted/cargo-anneal/src/verify.rs:1921-1938, 3320-3322`). Replacing the intermediate 10-inductive `RefProg` shadow AST (`Program -> RefProg -> Miri.MIR.Body`) with direct 2-hop `encodeToMiri : Program -> MiriProg` eliminates `Codec`/`State` shadow-AST drift (`google/zerocopy#4204`).
   `Basis: source`

2. **Root cause and exact bidirectional rule for zero-sized (`size == 0`) memory accesses.**
   - At `google/zerocopy@706acd8761d7`, `anneal/trusted/lean/Trusted/MirSemantics/Memory.lean` implements `readBytes` (`L194-217`) and `writeBytes` (`L219-248`) by returning `.ok []` when `Nat.beq size 0` (`L207`) and `.ok m` when `Nat.beq bytes.length 0` (`L231`) *before* looking up the allocation or testing `isAligned`.
   - Direct comparison against `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`compiler/rustc_const_eval/src/interpret/`) shows that `Memory.lean` quoted and copied the control flow of the inner bounds helper while serving the role of the outer place helper:
     - Inner `check_and_deref_ptr` (`memory.rs:519-566`, `L531-534`: `if size == 0 { return interp_ok(None); }`) and `get_ptr_alloc` / `get_ptr_alloc_mut` (`memory.rs:750-797, 851-890`, explicitly documented *"Bounds-checked **but not align-checked** allocation access"*) return `None` at `size == 0` prior to `ptr_try_get_alloc_id`, liveness (`PointerUseAfterFree`), bounds (`PointerOutOfBounds`), read-only checks (`WriteToReadOnly`), and `before_memory_read`/`before_memory_write` (Tree Borrows).
     - Outer `get_place_alloc` and `get_place_alloc_mut` (`place.rs:542-573`) invoke `get_ptr_alloc(_mut)` and then **unconditionally call `check_misalign(mplace.misaligned, ...)`** even when `None` was returned, computing alignment via `get_alloc_info` (`memory.rs:579-626`), which succeeds on dead (`live = false`) allocations as well. `proofs-rs/lean-miri@c92d1d9754c9` (`Miri/Memory/Access.lean:134-155` and `Miri/Interpreter/MemoryOperand.lean:103-163`) implements this exact two-layer order.
   - **Why Profile v1 correspondence did not trigger:** `Trusted/Correspondence/Simulation.lean:40-54` defines `SlotMatchesTy ... | .indirect _ => False` (excluding indirect memory locals from Profile v1), and all Profile v1 zero-sized types (`.unit`, `.never`, zero-sized fieldless enums) have `alignLog2 = 0` (`Layout.lean:166-172`), making `isAligned ... 0` tautologically `true`. As soon as aligned zero-sized types (`[T; 0]` with `align_of::<T>() > 1` or `#[repr(align(N))]` unit structs) and indirect pointer dereferences are admitted, skipping `isAligned` at `size == 0` becomes an unsound under-approximation of Rust UB.
   - **Bidirectional fault-equivalence constraint:** At `size == 0`, `readBytes` and `writeBytes` must check `findAllocation` and `isAligned a place.offset alignLog2` (including when `a.live = false`) *before* returning `.ok`, and must **not** enforce `a.live`, `isInBounds`, or `a.mutability == .mut` at `size == 0`. Enforcing liveness, bounds, or mutability at `size == 0` would be sound for universal safety (`forallSafety`), but would break bidirectional fault equivalence (`.undefined ↔ .ub`), invalidating existential UB refutation proofs (`refutationUB`).
   `Basis: normative + source + derived`

### 4. Layers 2–4: Concrete Miri Oracles, Mutation Killing, and Capture-Seam Grounding

1. **Upstream Miri `tests/fail*` census and `19`-test concrete oracle canary (`0 / 19` unsound accepts).**
   - Enumerating `src/tools/miri/tests/` in `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` yields **`644` negative UB `.rs` files** (`549` in `fail/` and `95` in `fail-dep/`), partitioned across intrinsics (`90`), aliasing (`127`: `tree_borrows` `53`, `stacked_borrows` `37`, `both_borrows` `37`), validity/uninitialized memory (`83`: `validity` `62`, `uninit` `11`, `match` `10`), pointers/allocation/provenance (`~100+`: `dangling` `21`, `unaligned` `17`, `alloc` `15`, `provenance` `14`, plus root tests), calls/ABI/unwinding/shims (`~100`), and concurrency/data-race/OS (`135`), alongside **`447` positive files** (`378` `pass/` + `69` `pass-dep/`).
   - Executing `19` representative upstream `tests/fail/*.rs` tests (`14/14` verified `rc = 1` UB under `miri 0.1.0 (6905905bb7) -Zmiri-tree-borrows`) through `anneal-rustc-capture` (`nightly-2026-05-31`) piped into the schema-v4 `#![no_std]` concrete MIR evaluator yielded:
     - **`0 / 19` unsound accepts** (`capture_rc = 0 ∧ eval_rc = 0`);
     - **`2 / 19` captured and caught as UB (`eval_rc = 2`, `FAULT undefined`):** `intrinsics/div-by-zero.rs` and `intrinsics/unchecked_div1.rs` (`MIN / -1` overflow);
     - **`1 / 19` captured and rejected fail-closed (`eval_rc = 3`):** `unreachable.rs` (`Terminator::Unsupported`);
     - **`15 / 19` rejected fail-closed at capture (`capture_rc = 1`, `status: "unsupported"`):** including `unaligned_pointers/unaligned_ptr_zst.rs` (`Range<i32>`), `dangling_pointers/{null,dangling}_pointer_deref.rs`, `validity/invalid_{bool,char,enum_cast}.rs`, `tree_borrows/alternate-read-write.rs`, `storage-live-{dead,resets}-var.rs`, `intrinsics/assume.rs`, and intrinsic `Call` wrappers; and
     - **`1 / 19` rejected by `rustc` prior to runtime MIR (`status: "compiler_failed"`):** `erroneous_const.rs`.
   - Continuous CI integration tracks three orthogonal counters over unmodified `tests/fail*` and `tests/pass*`: (a) **`unsound_accept == 0` (hard merge gate)**, (b) **`fail*_ub_caught / total` (monotonic completeness ratchet)**, and (c) **`pass*_false_positive_ub == 0` (absence of spurious UB faults on valid Rust)**.
   `Basis: execution + source`

2. **Semantic guard mutation and two-sided real-bug refutations.**
   - `anneal/ci/check_guard_mutation.py` (`.github/workflows/anneal-current.yml:445`) mutates `48` annotated TCB guards (`44` `MirSemanticsGuard` across `Ops:4`, `Enum:2`, `Bytes:5`, `Memory:15`, `Step:15`, `Boundary:3`, plus `4` `AuditHeaderGuard` in `TrustedBoundary.lean`) and requires a `100%` kill rate in CI (`google/zerocopy#4144` tracks expansion to unannotated AST-level predicate mutation across all lines of `MirSemantics/*.lean` and `extract.rs`).
   - Against byte-identical `Spec.lean` functional contracts, `cargo anneal verify` certifies fixed upstream commits (`Receipt v3`, `axioms: ["propext"]`, `taint_reasons: []`, `linux_bwrap`) while standalone Lean counterexample theorems (`Counterexample.bug_refutes_spec : ¬ Expected.claim`, `[propext]` only) refute verbatim buggy upstream commits in `<2s`:
     - `RustCrypto/block-ciphers`: buggy `2d7f6eb8ee7084e8b67d68970a3db1b62254584` (`(x as u8 >> i) & 0x01`) refuted at `x = 256, i = 8` in `1.707s` vs fixed `b6728c22fc98c2aa02bef6454595419693f4df42` (`(x >> i) as u8 & 0x01`).
     - `tokio-rs/bytes`: buggy `79fb85323cf4cf14d9b85f487b65fc147030cf4b` (`sign_extend` computing `(val << 64) as i64 >> 64` at `nbytes = 0`, shipped in `bytes` `v1.7.2`–`v1.11.0`) refuted at `val = 1, nbytes = 0` in `1.650s` vs fixed `acd1e0ffb8f076225759b8005d04f65ef77cccca`.
   `Basis: execution + source`

3. **Pre-optimization `PostCleanup` MIR capture and post-MIR translation validation.**
   - `anneal/trusted/rustc-capture/` (`capture.rs:83-85`) hooks `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) with `-Zmir-preserve-ub` (`google/zerocopy#4042`). Measuring `PostCleanup` versus `optimized_mir` across `963` `PlaceMention` sites shows that post-optimization MIR erases **`316 / 963` (`32.8%`)** `PlaceMention` UB checks prior to verification.
   - Until post-MIR translation validation (`google/zerocopy#3867`) is enabled for a target, `rustc` MIR optimizations, LLVM codegen, and linking remain explicitly disclosed as `unmodeled_downstream` assumptions in Receipt v3. For leaf functions requiring compiler-TCB removal without paying a `>25:1` whole-program binary proof tax, a Lean `v4.34.1` two-seam translation-validation canary (`30.81s` wall clock on `rustc 1.98.0-nightly` / LLVM `22.1.6` `-C opt-level=3`) proved universal equivalence from `Trusted.MirSemantics.ReturnsTotal` through parsed `-O3` LLVM IR (`InstCombine` two's-complement strength reduction `!(if len == 0 { usize::MAX } else { len - 1 }) & (align - 1) ↦ (align + -1) & (0 - len)` and `@llvm.smin.i32`) to kernel-decoded x86-64 ELF64 `.text` bytes on `<usize as PointerMetadata>::from_elem_count` (`48 89 f8 c3`), scalarized `padding_needed_for`, and ITU-T H.264 `Clip3`, while rejecting `3/3` injected LLVM/ELF miscompilations (including a 1-byte `0x4c cmovl -> 0x42 cmovb` signedness flip).
   `Basis: execution + source`

### 5. Layer 5: Profile-Parametric Verification Envelope (`support/FrameworkEnvelopeSketch.lean`)

Inspecting how `anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean` scales across multiple MIR profiles exposes a structural tension between two extremes:

- **Over-abstracted small-step frameworks (`>3,000`–`10,000` LOC in `trusted/`):** Wrapping every inner operational step in relational trace existentials, custom `@[default_instance]` ABI typeclass priorities, dozens of smart constructors, or a hard `Classical.choice` ban bloats the human-auditable TCB, degrades Lean kernel WHNF reduction on large straight-line/CPS blocks, and breaks compatibility with `vendor/lean-miri` (`39,088` declarations using `Classical.choice`).
- **Ununified per-profile boundary duplication:** Duplicating `StepV2`, `WellFormedV2`, `SpecsV2` (`String → Query → Prop`), `CrateV2`, and `UnitTheoremV2` alongside Profile v1 `Specs` (`String → List Val → Prop`) causes immediate type collisions for shared contract libraries, allows unbridged profiles (`correspondence.applicable = false`) to emit untainted status strings unless manually patched in Rust, and leaves Rust receipt metadata (`licensed_claim_shapes`, `unmodeled_downstream`, external callee stubs) disconnected from the Lean kernel obligation `Expected.claim`.

The minimal design mechanized in [`support/FrameworkEnvelopeSketch.lean`](support/FrameworkEnvelopeSketch.lean) (`230` lines, `0` axioms, `0` warnings on Lean `v4.34.1`) wraps **only the outer claim boundary**, leaving inner `MirSemantics` step functions (`WellFormed`, `Behavior`, `Diverges`) completely concrete (`0%` WHNF step overhead):

1. **Unified `ExecutionModel` and `FnContract Query Ret Mem`:** Parameterizing `FnContract` over `Query` (which carries `args : List Val` and `callerMem : CallerMemory`) unifies value-only (`MirProfileV1`, constraining `q.callerMem = ⟨[]⟩` in `entryDom`) and pointer/slice (`MirProfileV2`) specifications under a single contract type, while `FnContract.effectiveSafetyPre` (`safe_fn_ignores_false_safetyPre`) structurally ignores `safetyPre` whenever `isUnsafe = false`.
2. **Constructive `NonVacuousEntry` and `StubRealizable`:** `NonVacuousEntry M body pre := (∃ q, M.entryDom body q ∧ pre q) ∨ (∀ q, ¬ M.entryDom body q)` rejects contradictory preconditions on inhabited types while constructively admitting uninhabited parameter types (`!`, `core::convert::Infallible`) via `uninhabited_domain_nonVacuous` with zero waivers and zero `Classical.choice`. `StubRealizable` prevents inconsistent external callee summaries (`postReturn := False` with `terminates = true`) from discharging callers by `False.elim`.
3. **Upper-triangular `OracleGrade.licenses` transfer gate:** Encodes `forwardSim_rejects_refutationUB` and `biFaultEquiv_licenses_refutationUB` directly in `EnvelopeTheorem`, preventing an over-approximating model (`forwardSim`) from certifying bogus existential UB witnesses (`refutationUB`).
4. **Constructor-gated `DisclosedGap` binding (`unbridged_envelope_requires_gap`):** Marking `VerificationEnvelope.mk` `private` and requiring `EnvelopeGradeDisclosed M.oracleGrade env.gaps` makes it a Lean type error to state an `EnvelopeTheorem` over `OracleGrade.unbridged pid` (or with external callee stubs or raw-pointer aliasing assumptions) unless the exact `DisclosedGap` constructor appears inside `Expected.claim`, where the Rust NDJSON comparator can verify byte-for-byte parity with Receipt v3.
`Basis: source + execution (Lean kernel) + derived`

## Boundaries

- **Known not to apply on `google/zerocopy@706acd8761d7` (`Stage 0`, `"experimental": true`):**
  - `anneal/Cargo.lock:320-323` at `706acd8761d7` still resolves crates.io `exocrate 0.3.0` (`39f392e0...`), prior to publishing `exocrate 0.3.1` with pre-unpack SHA-256 verification and bumping `anneal/Cargo.lock`.
  - `anneal/trusted/root-manifest.sha256` at `706acd8761d7` hashes `4` root manifest/lock files (`Cargo.toml`, `Cargo.lock`, `flake.nix`, `flake.lock`) rather than all source files under `anneal/trusted/**`.
  - `anneal/trusted/lean/Trusted/MirSemantics/Memory.lean:207, 231` at `706acd8761d7` still short-circuits `size == 0` prior to `findAllocation` and `isAligned` (latent for Profile v1 types where `alignLog2 = 0`, requiring repair before admitting aligned ZST pointer dereferences).
  - Golden specification-closure diffing and canonical path-only contract binding (retiring positional `entryProgForBody program 0`) are not yet complete at Stage 0 (`google/zerocopy#4012`); human review of `Proof.lean` is not waived on `experimental: true` receipts.
- **Unsupported on `706acd8761d7`:**
  - Multi-crate `--extern` capture, user `Drop` execution, interior mutability, concurrent/atomic memory models (`135` upstream Miri concurrency/OS `fail*` files), inline assembly/SIMD intrinsics, and Pass-2 `lean-miri` correspondence for indirect pointer/slice memory profiles (`SlotMatchesTy .indirect _ => False` in `Simulation.lean:40-54`).
  - Downstream `rustc` MIR optimizations, LLVM code generation, and linking remain outside Pass-1 MIR verification (`unmodeled_downstream`) unless separately discharged by post-MIR translation validation (`google/zerocopy#3867`).
- **Not examined:**
  - Full CI runtime across all `644` upstream Miri `fail*` and `447` `pass*` files after stripping `Range<i32>` loop harnesses.
  - Mutation survival rates under unannotated AST-level mutation across non-guard lines of `Trusted/MirSemantics/*.lean` and `trusted/rustc-capture/src/extract.rs` (`google/zerocopy#4144`).

## Evidence

- **Anneal baseline (`google/zerocopy@706acd8761d7d8da4be9fc72f280931f75f7d837`, tag `anneal-v0.2.0-alpha.11`):**
  - Trust zones & manifests: `anneal/Cargo.toml:11-25`, `anneal/Cargo.lock:320-323`, `anneal/trusted/root-manifest.sha256:9-12`.
  - Pass-1 TCB semantics: `anneal/trusted/lean/Trusted/MirSemantics/{MirSemantics,Boundary,Bytes,CanaryFixtures,Enum,Layout,Memory,Ops,State,Step}.lean` (`Memory.lean:194-248`, `Layout.lean:166-172`, `Ops.lean:36-41`).
  - Pass-2 `lean-miri` correspondence & pin: `anneal/trusted/correspondence/Trusted/Correspondence.lean`, `anneal/trusted/correspondence/Trusted/Correspondence/Simulation.lean:40-54`, `anneal/correspondence/`, `anneal/trusted/audit/src/miri_pin.rs:46-60`, `anneal/vendor/lean-miri/UPSTREAM_PIN.json`.
  - Capture, audit, & CI mutation: `anneal/trusted/rustc-capture/src/{capture,extract}.rs`, `anneal/trusted/cargo-anneal/src/verify.rs:1921-1959, 3320-3322`, `anneal/trusted/audit/TrustedBoundary.lean`, `anneal/ci/check_guard_mutation.py`, `.github/workflows/anneal-current.yml:445`, `anneal/tests/audit/tests/{boundary_audit,target_audit,cli_environment}.rs`.
- **External reference pins (`2026-11-24`):**
  - `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/Memory/Access.lean:134-155`, `Miri/Interpreter/MemoryOperand.lean:103-163`).
  - `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`compiler/rustc_const_eval/src/interpret/memory.rs:519-634, 750-890`, `place.rs:542-573, 786-789`, `operand.rs:586-589`).
  - `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`src/tools/miri/tests/{fail,fail-dep,pass,pass-dep}/`), tested with `miri 0.1.0 (6905905bb7 2026-11-19)` (`nightly-2026-11-20`) and `anneal-rustc-capture` (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `nightly-2026-05-31`).
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `leanprover/lean4#14576`, `leanprover/lean4#16690`).
  - Historical open-source bug-refutation commits: `RustCrypto/block-ciphers@2d7f6eb8ee7084e8b67d68970a3db1b62254584` vs `b6728c22fc98c2aa02bef6454595419693f4df42`; `tokio-rs/bytes@79fb85323cf4cf14d9b85f487b65fc147030cf4b` vs `acd1e0ffb8f076225759b8005d04f65ef77cccca`.
  - Literature: Xuejun Yang, Yang Chen, Eric Eide, and John Regehr, *"Finding and Understanding Bugs in C Compilers,"* PLDI 2011 (`doi:10.1145/1993498.1993532`).
- **Preserved kernel-checked support artifact:**
  - [`support/FrameworkEnvelopeSketch.lean`](support/FrameworkEnvelopeSketch.lean) — Self-contained Lean `v4.34.1` mechanization of `ExecutionModel`, `ClaimShape`, `OracleGrade.licenses`, `DisclosedGap`, `NonVacuousEntry`, `StubRealizable`, `VerificationEnvelope`, `EnvelopeTheorem`, and five structural soundness theorems (`forwardSim_rejects_refutationUB`, `biFaultEquiv_licenses_refutationUB`, `safe_fn_ignores_false_safetyPre`, `uninhabited_domain_nonVacuous`, `unbridged_envelope_requires_gap`).

## Revalidation

1. **Kernel-check the preserved `VerificationEnvelope` mechanization on Lean `v4.34.1` (`<3s`):**
   ```bash
   lean -DwarningAsError=true reports/epistemology-and-defense-in-depth-soundness-for-ai-accelerated-semantics/support/FrameworkEnvelopeSketch.lean
   ```
   Confirms that all definitions and structural licensing/non-vacuity/gap-disclosure theorems elaborate with zero warnings and zero custom axioms.

2. **Recompute Anneal's TCB vs. `0`-TCB Lean ratio and core semantics line budget on a newer `google/zerocopy` checkout (`<2s`):**
   ```bash
   python3 - << 'EOF'
   import pathlib
   root = pathlib.Path("anneal")
   zones = {"trusted_lean": "trusted/lean", "trusted_corr": "trusted/correspondence",
            "trusted_audit": "trusted/audit", "theory": "theory", "correspondence": "correspondence"}
   for name, rel in zones.items():
       files = sorted((root / rel).rglob("*.lean"))
       tot = sum(len(f.read_text().splitlines()) for f in files)
       code = sum(1 for f in files for l in f.read_text().splitlines()
                  if l.strip() and not l.strip().startswith("--"))
       print(f"{name:16s} files={len(files):3d} total={tot:6d} code={code:6d}")
   EOF
   ```
   Verifies whether `0`-TCB `theory/` + `correspondence/` continues to hold its `~6.6:1` ratio over `trusted/` and whether `trusted/lean/` remains within a human-auditable ~`5.6K`-line core.

3. **Verify zero-sized memory alignment ordering and `100%` CI guard-mutation kill rate:**
   ```bash
   grep -n -C5 "Nat.beq size 0\|Nat.beq bytes.length 0" anneal/trusted/lean/Trusted/MirSemantics/Memory.lean
   python3 anneal/ci/check_guard_mutation.py
   ```
   Checks whether `findAllocation` and `isAligned` execute prior to the `size == 0` return in `readBytes`/`writeBytes` and confirms that every annotated semantic guard in `Trusted/MirSemantics/*.lean` and `TrustedBoundary.lean` kills at least one negative test when mutated.
