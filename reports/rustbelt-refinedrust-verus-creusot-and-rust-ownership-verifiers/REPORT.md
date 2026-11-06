# RustBelt, RefinedRust, Verus, Creusot, Gillian-Rust, Foundational VeriFast, and Rust Ownership Verifiers

## Summary

This report synthesizes eight primary-source and artifact-level investigations across foundational and SMT-backed Rust ownership verifiers, contract bridges, hinted proof-mirroring checkers, and Rust-to-C/Rocq/F*/Lean extraction pipelines:

1. **RustBelt Unsafe-Abstraction Soundness Model (POPL 2018, `lambda-rust-popl18.tar.gz`)**: Mechanized in Coq over $\lambda_{\text{Rust}}$ (`theories/lang/lang.v`) and Iris 3.1, RustBelt separates syntactic typing (`typing.v`) from semantic type interpretations (`ty.v`: size, own-predicate `ty_own`, share-predicate `ty_shr`, and shrinking/lifetime laws). Its adequacy theorem (`theories/typing/adequacy.v:21–42`, `type_soundness`) proves that a closed program linking syntactically well-typed safe code with manually proved semantic (`unsafe`) libraries (`Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `RwLock`, `Vec`, `mem::swap`, `take_mut`) never gets stuck (`adequate NotStuck`).
2. **RustBelt to RustHornBelt First-Order Contract Bridge (PLDI 2022, `the_artifact.tgz`, Zenodo `6417462`)**: Extends RustBelt's semantic type system with prophecy variables (`proph_map.v`, `resolving`) so mutable borrows (`&uniq{κ, ξ} T`) carry the future value resolved when lifetime `κ` ends. This bridges Iris separation logic (`[[...]]` semantic judgments) to pure first-order logic / CHC postconditions (`<...>`) without exposing Iris resources to safe callers (`theories/typing/programs.v:63–114`). Includes the author erratum (`errata.txt`) correcting the paper's presentation of nested-borrow prophecy resolution while leaving the Coq mechanization (`theories/typing/uniq_bor.v`) intact.
3. **RefinedRust and Radium Proof Boundaries (PLDI 2024 & POPL 2026, Zenodo `21636474`)**: RefinedRust lowers Rust `rustc` MIR into the Caesium operational model (`caesium/theories/`) and discharges Lithium separation-logic verification conditions in Rocq (`refinedrust/theories/`). The POPL 2026 artifact (`artifact.tar.gz`) adds **Radium** (`case_studies/radium/`), verifying `Cell`, `Atomic*`, and `Radium` trait implementations against relaxed-memory/atomic specs. Audit of the archive confirms that while the Rocq theories (`caesium`, `lithium`, `refinedrust`, `radium`) are foundational, the Rust-to-Rocq frontend generator (`refinedrust-rustc`) is an unverified translator and `#[rr::trust_me]` attributes skip body generation.
4. **Verus Tracked-Memory and Trust Boundary (`verus-lang/verus` `0141ebc6f14410dfc87fef1da57408578002eb7c`)**: Verus embeds linear `tracked` and duplicable `ghost` permissions directly in Rust syntax (validated by `rust_verify/src/lifetime.rs` using `rustc`'s borrow checker) and lowers `exec`/`proof`/`spec` code through VIR (`source/vir/`) to AIR and Z3/CVC5 queries without producing kernel proof terms. In `source/vstd/raw_ptr.rs` (`PointsTo<T>`, `PointsToRaw`, `Dealloc`), raw pointer operations (`ptr_mut_write`, `ptr_ref`, `expose_provenance`, `with_exposed_provenance`) are axiomatized via `#[verifier::external_body]` contracts parameterized by ghost `PointsToData<T>`.
5. **Creusot Permission & Coma Intermediate Verification Language (`creusot-rs/creusot` `c4e9770ac1371ac4274bfe02145266d315c2fb86`, ESOP 2025)**: Creusot translates Rust MIR via prophetic mutable borrows (`^x` final value, `*x` current value) into **Coma** (`why3/src/coma.rs`), an intermediate continuation-passing handler language inside Why3 (`creusot/src/backend/`), and discharges VCs via external SMT solvers (`Alt-Ergo`, `Z3`, `CVC5`). Raw pointer and container permissions (`creusot-contracts/src/std/ptr.rs`: `PtrOwn<T>`, `slice_ptr_len`) are trusted specification contracts (`#[trusted]`) backed by a Ghost/Resource algebra library (`creusot-contracts/src/ghost/resource.rs`, `pmap.rs`, `fmap.rs`) rather than an operational byte-memory model.
6. **Gillian-Rust Hybrid Symbolic-Heap and Prophecy Boundary (`GillianPlatform/gillian-rust` `83d739e83034d71162fb66b569041cf301123df7`, PLDI 2025, & Lean 4.34.1 Replay)**: Gillian-Rust combines a spatial layout-aware tree memory model (`libgillian_rust/mem_model.ml`) for raw pointers and `unsafe` code with a pure prophetic representation (`pcy_env.ml`, `obs_ctx.ml`) for safe borrows. Inspection of `GillianCore/engine/Abstraction/Matcher.ml` (`25c97535`) and `gillian-rust` shows symbolic execution and Z3 discharge without foundational proof certificates; an executable Lean 4.34.1 model (`support/focused-replay-and-encoding/ProphecyReplay.lean`) proves `prophecy_controller_observation_roundtrip` and demonstrates why omitting structural observation constraints (`neg_unconstrained_prophecy_unsound`) allows invalid prophecy assignments.
7. **Foundational VeriFast via Hinted Mirroring (`verifast/verifast` `0a83dba42db7ce0b445034ece5298afe980e57dc`, arXiv `2601.13727v1`)**: VeriFast's `-emit_rocq_proof` flag exports a symbolic execution trace and hint stream (`src/rocq_proof.ml`) that is replayed in Rocq against an axiomatic C semantics (`bin/rocq/verifast.v`, `bin/rocq/sema.v`, `busy_wait.v`). Auditing `0a83dba4` (`support/selected-source-audit.json`) confirms that the Rocq mirror applies exclusively to VeriFast's **C** verifier (`src/c_frontend/`), **not** to VeriFast's Rust frontend (`src/rust_frontend/`), and relies on explicit axiomatic semantics parameters (`axiomatic_semantics`) in `bin/rocq/verifast.v`.
8. **`hax`, `Eurydice`, `Charon`, and `RustCompCert` Extraction Frontiers (`cryspen/hax` `cc6da074`, `AeneasVerif/eurydice` `7332393a`, `AeneasVerif/charon` `cf02e3f2`, `SJTU-PLV/CompCert` `e3d03ed8`)**: Maps the exact input IR, supported Rust subsets, and trust gaps across `hax` (THIR-based extraction to F*, Coq, ProVerif, and Lean `engine/backends/lean/lean_backend.ml`), `Eurydice` (Charon LLBC-to-KaRaMeL C extraction `lib/Ceil.ml`, `Cleanup1..3.ml`), and `RustCompCert` (`SJTU-PLV/CompCert` `e3d03ed8` + arXiv `2602.07455v1`, an early MIR-to-Clight/CompCert prototype with explicit `Admitted` proofs in `rust/MirSem.v` and `rust/Mir2Clightproof.v`).

---

## Applicability

| System / Subject | Pinned Identity / Commit / Archive | Verification / Replay Scope |
|---|---|---|
| RustBelt (POPL 2018) | `lambda-rust-popl18.tar.gz` (`sha256: b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`), DOI `10.1145/3158154` | Coq source inspection of $\lambda_{\text{Rust}}$, lifetime logic (`theories/lifetime/`), semantic types (`theories/typing/`), and unsafe stdlib (`theories/typing/lib/`) |
| RustHornBelt (PLDI 2022) | Zenodo `6417462` (`the_artifact.tgz`, `sha256: 7e67c2d49b3b655113675c0d517d76589d615c9622eac2d91417d99263959121`), DOI `10.1145/3519939.3523704`, errata `5112f5ce` | Coq source inspection of prophetic borrows (`uniq_bor.v`), first-order horn contracts (`programs.v`), and errata comparison |
| RefinedRust & Radium (2024 / 2026) | Zenodo `21636474` (`artifact.tar.gz`, `sha256: 34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`), DOIs `10.1145/3656422`, `10.1145/3839484` | Archive audit of `caesium/`, `lithium/`, `refinedrust/`, `case_studies/radium/`, and `refinedrust-rustc` frontend (`support/refinedrust-radium-proof-boundary-2026-v2/inspection.json`) |
| Verus | `verus-lang/verus` at `0141ebc6f14410dfc87fef1da57408578002eb7c`, arXiv `2303.05491v2` | Source inspection of `rust_verify/src/lifetime.rs`, `source/vir/`, `source/air/`, `source/vstd/raw_ptr.rs`, `cell.rs`, `atomic_ghost.rs` |
| Creusot & Coma | `creusot-rs/creusot` at `c4e9770ac1371ac4274bfe02145266d315c2fb86`, Coma ESOP 2025 (`sha256: a52ad7b7...`) | Source inspection of `creusot/src/backend/`, `why3/src/coma.rs`, `creusot-contracts/src/std/ptr.rs`, `ghost/resource.rs` |
| Gillian-Rust | `GillianPlatform/gillian-rust` at `83d739e83034d71162fb66b569041cf301123df7`, `GillianPlatform/gillian` at `25c97535e513be63b4de3a0fc98e4ac096e75c0f`, PLDI 2025 (`10.1145/3729289`), + Lean `4.34.1` replay | Source inspection of hybrid memory/prophecy engine + Lean 4.34.1 mechanization (`support/focused-replay-and-encoding/ProphecyReplay.lean`) |
| Foundational VeriFast | `verifast/verifast` at `0a83dba42db7ce0b445034ece5298afe980e57dc`, arXiv `2601.13727v1` | Source audit (`support/selected-source-audit.json`) of `src/rocq_proof.ml`, `bin/rocq/verifast.v`, and `src/rust_frontend/` |
| `hax`, `Eurydice`, `Charon`, `RustCompCert` | `cryspen/hax` `cc6da074`, `AeneasVerif/eurydice` `7332393a`, `AeneasVerif/charon` `cf02e3f2`, `SJTU-PLV/CompCert` `e3d03ed8` (arXiv `2602.07455v1`) | Source inspection of Lean/F*/C extraction passes and `RustCompCert` Coq development |

---

## Findings

### 1. RustBelt POPL 2018 Unsafe-Abstraction Soundness Model (`lambda-rust-popl18.tar.gz`)

**Basis: source (`support/rustbelt-unsafe-abstraction-model-popl-2018/source-map.json`).**

#### 1.1 Semantic Type System Architecture (`theories/typing/ty.v`, `programs.v`, `adequacy.v`)
RustBelt formalizes a core continuation-passing/expression calculus $\lambda_{\text{Rust}}$ (`theories/lang/lang.v`) over a block-offset heap (`loc := (block * Z)`) with explicit allocation, free, atomic CAS, and non-atomic reads/writes (`NotStuck` failure on data races, use-after-free, or out-of-bounds access).
- **Semantic Type Interface (`theories/typing/ty.v:15–70`)**: A semantic type `ty Σ` is a record bundling:
  1. `ty_size : nat` (word count in memory),
  2. `ty_own : tid → list val → iProp Σ` (exclusive ownership of a value representation in thread `tid`),
  3. `ty_shr : lft → tid → loc → iProp Σ` (persistent shared borrow at lifetime `κ` and heap location `l`),
  4. `ty_shr_mono` (contravariance in `κ': κ' ⊑ κ ⊢ ty_shr κ t l -∗ ty_shr κ' t l`), and
  5. `ty_share` (`&{κ} (l ↦∗: ty_own t) =[lft_ctx]=∗ ty_shr κ t l`, converting a full borrow of owned memory into the persistent shared predicate under a mask update).
- **`Send` and `Sync` as Semantic Predicates (`theories/typing/ty.v:72–90`)**:
  - `Send` (`Send ty`): `ty_own t1 vl ⊢ ty_own t2 vl` (thread-id independence of owned representation).
  - `Sync` (`Sync ty`): `ty_shr κ t1 l ⊢ ty_shr κ t2 l` (thread-id independence of shared reference predicate).
- **Whole-Program Soundness (`theories/typing/adequacy.v:21–42`)**: `type_soundness` invokes Iris's `wp_adequacy` (`adequacy.v`) after initializing the lifetime context (`lft_init`) and thread-local non-atomic invariant pool (`na_init`). Any closed expression `e` semantically typed in the empty context (`typed_body`) executes without getting stuck (`adequate NotStuck e σ (λ _ _, True)`).

#### 1.2 Verified Unsafe Standard-Library Abstractions (`theories/typing/lib/`)
Each interior-mutable or synchronization primitive in `theories/typing/lib/` is verified by defining a custom `ty_own` / `ty_shr` using Iris ghost state and proving the syntactic API signature as a semantic typing lemma:
- **Single-threaded (`Cell`, `RefCell`, `Rc`)**: Uses thread-local non-atomic invariants (`na_inv tid N P`) indexed by the owning thread `tid`, explaining why `ty_shr` depends on `tid` and why `Sync` fails for `Cell`/`RefCell` and `Send`/`Sync` fail for `Rc`.
- **Concurrent (`Arc`, `Mutex`, `RwLock`, `spawn`, `join`)**: Uses standard thread-independent Iris invariants (`inv N P`) and fractional/counting ghost state (`authR`), satisfying `Send`/`Sync` conditioned on `Send T` / `Sync T`.

---

### 2. RustBelt to RustHornBelt Contract Bridge (PLDI 2022, Zenodo `6417462`)

**Basis: source and errata inspection (`support/rustbelt-rusthornbelt-contract-bridge-2022/source-evidence.json`, `support/rustbelt-rusthornbelt-contract-bridge-2022/coverage.json`).**

#### 2.1 Prophetic Mutable Borrows (`theories/typing/uniq_bor.v`)
Standard RustBelt verifies type safety ("no undefined behavior"), not functional correctness specifications of client code, and requires separation-logic proofs even for safe Rust functions. RustHorn (ESOP 2020, `10.1007/978-3-030-44914-8_18`) reduces safe Rust mutable borrows to pure first-order Constrained Horn Clauses (CHCs) using prophecy values, but assumes `unsafe` libraries away.

RustHornBelt (`the_artifact.tgz`) unifies both by enriching the semantic type of mutable references (`&uniq{κ, ξ} T` in `theories/typing/uniq_bor.v:32–118`):
- Each semantic type `ty` is extended with a **mathematical value domain** `ty_proph : Type` and an abstraction relation `ty_own_proph` linking physical values `list val` to pure mathematical values `v : ty_proph`.
- A unique borrow `&uniq{κ, ξ} T` pairs the spatial borrow `&{κ}(l ↦∗: ...)` with exclusive ownership of a prophecy variable `ξ` (`proph ξ v_future`), where `v_future` predicts the mathematical value that will reside at `l` when lifetime `κ` expires.
- Reborrowing (`reborrow_uniq` in `uniq_bor.v:180–265`) allocates a fresh intermediate prophecy `ξ'` for the sub-borrow `&uniq{κ', ξ'} T` and records a prophecy resolution observer showing that when `κ'` ends, `ξ` inherits the updates made through `ξ'`.

#### 2.2 The Two-Sided Contract Bridge and Author Erratum
- **Safe Callers (`theories/typing/programs.v:63–114`)**: Safe functions are verified purely in first-order logic over mathematical values `(v_cur, v_final)` without mentioning heaps, step indices, or Iris cameras.
- **Unsafe Callees (`theories/typing/lib/vec.v`, `mutex.v`, `cell.v`, `rc.v`, `take_mut.v`)**: Unsafe primitives (`Vec::push`, `Vec::index_mut`, `mem::swap`, `take_mut`) are proved once in Coq/Iris to satisfy their prophetic semantic contract.
- **Author Erratum (`errata.txt`, `sha256: 5112f5ce...`)**: Documents that the PLDI 2022 paper text simplified the presentation of `ty_own_proph` for types containing nested mutable references (`&mut &mut T`), whereas the actual Coq artifact (`theories/typing/uniq_bor.v` and `theories/typing/ty.v`) explicitly tracks prophecy dependencies (`dep_proph`) and is unaffected by the prose simplification.

---

### 3. RefinedRust and Radium Proof Boundaries (2024 / 2026, Zenodo `21636474`)

**Basis: source archive inspection (`support/refinedrust-radium-proof-boundary-2026-v2/source-evidence.json`, `support/refinedrust-radium-proof-boundary-2026-v2/inspection.json`, `support/refinedrust-radium-proof-boundary-2026-v2/coverage.json`).**

| Layer in `artifact.tar.gz` (Zenodo `21636474`) | Directory & Key Files | Mechanized Role | Trust & Soundness Boundary |
|---|---|---|---|
| **Caesium Operational Model** | `caesium/theories/` (`lang.v`, `memory.v`, `int_type.v`, `layout.v`, `atomic.v`) | Foundational Rocq operational semantics for low-level MIR-like CFG blocks, byte-level provenance memory, integer overflow modes, and atomic accesses | Trusted operational baseline; does not include a verifiedequivalence proof against `rustc` MIR or LLVM IR |
| **Lithium Automation Engine** | `lithium/theories/` (`base/shim.v`, `interpreter.v`, ` normalize.v`) | Goal-directed separation-logic proof search (`liRStep`) generating kernel-checked Rocq/Iris proof terms | **Untrusted** for soundness: every Lithium step elaborates to a foundational Iris theorem checked by the Rocq kernel |
| **RefinedRust Type System** | `refinedrust/theories/` (`ty.v`, `references.v`, `shims.v`, `own.v`, `frac.v`) | Refinement and ownership type definitions (`own_ptr`, `shr_ref`, `mut_ref`, `uninit`, `place`) over Caesium + Iris | Mechanized in Rocq; soundness holds relative to Caesium's semantics |
| **Radium Case Study (POPL 2026)** | `case_studies/radium/` (`src/lib.rs`, `proofs/`) | Verifies `Radium` unified abstraction over `Cell<T>` and `Atomic*` types (`fetch_add`, `compare_exchange`, `swap`) | Demonstrates unified specs for atomic and non-atomic interior mutability in RefinedRust |
| **Frontend (`refinedrust-rustc`)** | `frontend/` (Rust compiler driver plugin) | Translates `rustc` MIR + `#[rr::...]` annotations into Rocq `.v` files containing Caesium ASTs and typing obligations | **In the TCB**: translation from `rustc` MIR to Caesium Rocq syntax is unverified, and functions annotated `#[rr::trust_me]` emit Rocq `Axiom`/`Admitted` obligations |

---

### 4. Verus Tracked-Memory and Trust Boundary (`verus-lang/verus` `0141ebc`)

**Basis: source (`support/verus-tracked-memory-trust-0141ebc/source-evidence.json`, `support/verus-tracked-memory-trust-0141ebc/additional-source-evidence.json`, `support/verus-tracked-memory-trust-0141ebc/coverage.json`).**

#### 4.1 Linear Ghost Modes Checked by `rustc` (`rust_verify/src/lifetime.rs`)
Instead of embedding separation logic in an external theorem prover, Verus partitions code and variables into three modes (`exec`, `proof`, `spec`):
- `spec` values are duplicable and erased before compilation.
- `tracked` ghost values are **linear/affine** resources: `rust_verify/src/lifetime.rs` emits a synthetic Rust program stripped of SMT expressions and invokes `rustc`'s standard borrow checker (`lifetime_generate.rs`) to enforce exclusivity and lifetime bounds on `tracked` tokens (`#[verifier::proof]` / `tracked`).
- Operational and specification VC generation flows `rustc HIR/THIR → VIR (source/vir/) → AIR (source/air/) → SMT-LIB2 (Z3/CVC5)` without generating proof terms for a proof assistant kernel.

#### 4.2 Raw Pointer and Interior Mutability Axiomatization (`source/vstd/raw_ptr.rs`, `cell.rs`, `atomic_ghost.rs`)
In `source/vstd/raw_ptr.rs` (at `0141ebc6f14410dfc87fef1da57408578002eb7c`):
- Raw pointers `*mut T` / `*const T` are pure `exec` addresses accompanied by a `tracked` permission token `PointsTo<T>` (or byte-level `PointsToRaw` + `Dealloc`).
- `PointsTo<T>` wraps an uninterpreted `spec` ghost state `PointsToData<T>` (`ptr: *mut T`, `opt_value: MemContents<T>`), accounting for provenance (`Provenance`), alignment, and initialization (`MemContents::Init(v)` vs. `Uninit`).
- All primitive operations (`ptr_mut_write`, `ptr_mut_read`, `ptr_ref`, `allocate`, `deallocate`, `PointsToRaw::into_typed`, `expose_provenance`) are declared `#[verifier::external_body]`: their Rust bodies execute raw pointer dereferences while their `requires`/`ensures` clauses over `tracked PointsTo<T>` are **trusted axioms** in the Verus TCB.
- Similarly, `source/vstd/cell.rs` (`PCell<T>`) and `source/vstd/atomic_ghost.rs` (`AtomicU64<_, G, _>`) pair an `external_body` interior-mutable wrapper with a `tracked` permission token (`PointsTo<T>` or ghost state `G` updated inside an `atomic_with_ghost!` block).

---

### 5. Creusot Permission and Coma Architecture (`creusot-rs/creusot` `c4e9770`, ESOP 2025)

**Basis: source (`support/creusot-permission-coma-trust-c4e9770/source-evidence.json`, `support/creusot-permission-coma-trust-c4e9770/additional-source-evidence.json`, `support/creusot-permission-coma-trust-c4e9770/coverage.json`).**

#### 5.1 Prophetic Translation to Coma (`why3/src/coma.rs`, `creusot/src/backend/`)
- **Prophetic Mutable Borrows**: Following RustHorn, Creusot translates a mutable borrow `b : &mut T` into a pair `(cur : T, fin : T)` (`*b` and `^b`), resolving `^b = *b` at the exact MIR point where the borrow dies (`creusot/src/translation/fmir.rs`).
- **Coma Intermediate Language (`why3/src/coma.rs`, ESOP 2025 `esop2025.pdf`)**: Rather than emitting legacy WhyML expressions directly, Creusot `c4e9770` lowers fMIR into **Coma**, a small continuation-passing verification language with explicit parameterized handlers (`Defn`, `App`, `Any`, `Assert`, `Assume`, `BlackBox`). Coma generates compact, structure-preserving VCs in Why3 (`creusot/src/backend/program.rs`) without exponential WP duplication across CFG joins.

#### 5.2 Ghost Permissions (`PtrOwn<T>`) and Resource Algebras (`creusot-contracts`)
To verify `unsafe` code that cannot be expressed as safe prophetic borrows, `creusot-contracts` provides:
- **`PtrOwn<T>` (`creusot-contracts/src/std/ptr.rs`)**: A non-duplicable `GhostBox<PtrOwn<T>>` permission token pairing a raw pointer `ptr : *const T` with its logical value `val : T`. Operations `PtrOwn::new`, `as_ref`, `as_mut`, `to_raw`, and `drop` are annotated `#[trusted]`: their specifications bridge raw pointer operations back to prophetic borrows (`&T` / `&mut T`) by axiomatically asserting `*ret == *own.val()` and `^ret == ^own.val()`.
- **Iris-Style Ghost Resources (`creusot-contracts/src/ghost/resource.rs`, `fmap.rs`, `pmap.rs`)**: Mechanizes `Resource<R>` over a `Unit`/`Idem`/`Commutative` camera trait (`CMRA`) inside pure Creusot logic, enabling ghost authority/fragment protocols discharged by SMT solvers (`Z3`, `CVC5`, `Alt-Ergo`) via Why3.

---

### 6. Gillian-Rust Hybrid Symbolic-Heap and Prophecy Boundary (`83d739e`, PLDI 2025)

**Basis: source and Lean 4.34.1 replay (`support/gillian-rust-hybrid-resource-boundary-83d739e/source-evidence.json`, `support/gillian-rust-hybrid-resource-boundary-83d739e/coverage.json`, `support/focused-replay-and-encoding/ProphecyReplay.lean`, `support/focused-replay-and-encoding/replay-results.json`).**

#### 6.1 Dual-Mode Hybrid Representation (`gillian-rust` `83d739e`, `gillian` `25c97535`)
Gillian-Rust (`GillianPlatform/gillian-rust` at `83d739e83034d71162fb66b569041cf301123df7`, locking `GillianPlatform/gillian` at `25c97535e513be63b4de3a0fc98e4ac096e75c0f`) operates in two modes controlled by `#[gillian::prophetic]` / `#[gillian::spatial]`:
1. **Spatial Tree-Block Memory (`libgillian_rust/mem_model.ml`, `tree_block.ml`)**: Models allocations as structural layout trees supporting sub-object slicing, raw-pointer offset arithmetic, uninitialized memory (`Uninit`), and fractional borrow lifetimes (`lft`).
2. **Prophetic Borrow Layer (`libgillian_rust/pcy_env.ml`, `obs_ctx.ml`)**: Inspired by RustHornBelt, safe mutable borrows are represented by pairing a controller/value representation with a prophecy variable `pcy_var` and an **observation context** (`obs_ctx.ml`) that constrains how inner prophecy variables relate to outer ones when a borrow splits or reborrows.
3. **Engine Boundary (`GillianCore/engine/Abstraction/Matcher.ml`, `Verifier.ml`)**: Gillian's symbolic execution engine consumes and produces spatial/prophetic predicates using unification and Z3 (`PState.ml`), outputting pass/fail verification logs rather than foundational Rocq or Lean kernel certificates.

#### 6.2 Mechanized Lean 4.34.1 Replay of Prophecy-Controller Observation Soundness (`support/focused-replay-and-encoding/ProphecyReplay.lean`)
To isolate the exact soundness condition required when combining spatial ownership with prophetic borrows in Lean 4, `support/focused-replay-and-encoding/ProphecyReplay.lean` (replayed on Lean `4.34.1`, exit `0`, zero `sorry`, `support/focused-replay-and-encoding/replay-results.json`) models:
- `PropheticBorrow`: a current value `cur`, prophecy variable ID `pcy`, and controller obligation `ctrl`.
- `ObsConstraint`: the structural observation equation equating a parent borrow's prophecy at freeze time with the child borrow's final resolved value plus unborrowed sibling fields.
- **Verified Theorems**:
  - `prophecy_controller_observation_roundtrip`: When the observation context `ObsConstraint` is enforced across field projection and reborrow resolution, the prophetic postcondition is sound with respect to concrete state mutation.
  - `hybrid_spatial_prophetic_isolation`: Spatial mutations on disjoint heap addresses preserve active prophecy observation contexts.
  - `neg_unconstrained_prophecy_unsound`: Explicitly constructs a counterexample trace showing that if a verifier omits the controller observation constraint upon borrow splitting, a caller can derive a false postcondition (`0 = 1`) from an arbitrary prophecy assignment.

---

### 7. Foundational VeriFast via Hinted Mirroring (`verifast` `0a83dba4`, arXiv `2601.13727v1`)

**Basis: source audit (`support/audit_upstream.py`, `support/selected-source-audit.json`, arXiv `2601.13727v1`).**

#### 7.1 Hinted Mirroring Architecture (`src/rocq_proof.ml`, `bin/rocq/verifast.v`)
Foundational VeriFast (`2601.13727v1`) addresses the trust gap of fast symbolic-execution verifiers by having VeriFast emit a compact stream of **hints** (`-emit_rocq_proof`, implemented in `src/rocq_proof.ml`) during symbolic execution of a C program:
- Rather than translating SMT/symbolic-execution steps one-for-one into giant proof terms, `src/rocq_proof.ml` emits only the non-deterministic choices (which heap chunk was consumed, how fractional permissions were split, and which lemma/predicate unfolding occurred).
- In Rocq (`bin/rocq/verifast.v`, `bin/rocq/sema.v`, `bin/rocq/busy_wait.v`), a deterministic symbolic mirror re-executes the function over a shallowly embedded C AST and checks each step against an axiomatic C operational semantics using `lia` / `congruence` for pure side conditions.

#### 7.2 Critical Scope and Trust Boundaries (`support/selected-source-audit.json`)
Auditing `verifast/verifast` at `0a83dba42db7ce0b445034ece5298afe980e57dc` via `support/audit_upstream.py` establishes two hard boundaries relevant to Rust verification:
1. **C-Only Coverage (`src/rust_frontend/` Excluded)**: The `-emit_rocq_proof` pipeline in `src/rocq_proof.ml` and `bin/rocq/verifast.v` handles **only** C AST constructs (`src/c_frontend/`). VeriFast's Rust frontend (`src/rust_frontend/`) is completely unconnected to `rocq_proof.ml`.
2. **Axiomatic Semantics Parameterization (`bin/rocq/verifast.v`)**: The Rocq development in `bin/rocq/verifast.v` parameterizes its soundness theorem over an `axiomatic_semantics` record (modeling expression evaluation, heap chunk allocation, and call steps) rather than connecting end-to-end to CompCert Clight (`Csem`).

---

### 8. `hax`, `Eurydice`, `Charon`, and `RustCompCert` Extraction Frontiers

**Basis: source inspection (`cryspen/hax` `cc6da074`, `AeneasVerif/eurydice` `7332393a`, `AeneasVerif/charon` `cf02e3f2`, `SJTU-PLV/CompCert` `e3d03ed8`, arXiv `2602.07455v1`).**

| Extraction / Compiler Pipeline | Pinned Repository & Commit | Input Rust IR | Target Output | Current Capabilities & Explicit Trust Boundaries |
|---|---|---|---|---|
| **`hax` (`cryspen/hax`)** | `cc6da074ca754ca9d406ec922daad3221aacbce5` | `rustc` THIR + MIR drops (`frontend/exporter/`) | F*, Rocq, ProVerif, and Lean 4 (`engine/backends/lean/lean_backend.ml`) | Functional AST-to-AST translation eliminating local mutation where possible; Lean 4 backend (`lean_backend.ml`) emits pure Lean definitions and `hax-lib` contract wrappers, but lacks a mechanized semantics-preservation proof from Rust THIR and rejects raw pointer mutation / arbitrary `&mut` aliasing |
| **`Charon` (`AeneasVerif/charon`)** | `cf02e3f228f97ee7be3a415be56989053063326d` | `rustc` MIR (`charon/src/bin/charon-driver/`) | ULLBC (unstructured CFG) and LLBC (structured control-flow AST JSON) | Shared frontend for Aeneas and Eurydice; reconstructs structured loops/conditionals from MIR CFGs (`ullbc_to_llbc.rs`); unverified translator in the TCB |
| **`Eurydice` (`AeneasVerif/eurydice`)** | `7332393a18a20baae808d8783266acd15121ddd2` | Charon LLBC | KaRaMeL AST $\to$ C (`lib/AstOfLlbc.ml`, `Cleanup1.ml`–`Cleanup3.ml`) | Compiles low-level Rust (slices, arrays, structs, enums, pointers) to readable C for cryptographic code (e.g., `libcrux`); translation passes (`AstOfLlbc.ml`, monomorphization, slice fat-pointer lowering) are unverified OCaml code |
| **`RustCompCert` (`SJTU-PLV/CompCert`)** | `e3d03ed822a7aaf452b7022c347187ed1efc1c12` (arXiv `2602.07455v1`) | Restricted MIR subset (`rust/Mir.v`) | CompCert `Clight` (`rust/Mir2Clight.v`) $\to$ Assembly | Early-stage Rocq formalization defining `rust/MirSem.v` and `rust/Mir2Clightproof.v`; direct inspection at `e3d03ed8` shows multiple `Admitted` simulation lemmas in `rust/Mir2Clightproof.v` and restricted type/borrow coverage |

---

## Boundaries

1. **Unverified Frontend Translators**: Across RefinedRust (`refinedrust-rustc`), Verus (`rust_verify`), Creusot (`creusot-rustc`), Gillian-Rust (`gillian-rust` MIR lowering), `hax` (`hax-exporter`), and `Charon`/`Eurydice`, the extraction pass from `rustc` HIR/THIR/MIR into the verifier's internal representation is implemented in unverified Rust or OCaml code.
2. **SMT-Backed vs. Kernel-Checked Foundations**: Verus (`0141ebc`), Creusot (`c4e9770`), and Gillian-Rust (`83d739e`) rely on SMT solvers (`Z3`, `CVC5`, `Alt-Ergo`) and axiomatized raw-pointer primitives (`vstd::raw_ptr::PointsTo`, `creusot_contracts::std::ptr::PtrOwn`) rather than producing foundational Rocq or Lean kernel proof terms.
3. **Foundational VeriFast Rust Gap**: VeriFast's `-emit_rocq_proof` hinted-mirroring pipeline (`0a83dba4`) targets C only and does not support VeriFast's Rust frontend.
4. **`RustCompCert` Incompleteness**: At `e3d03ed8`, `SJTU-PLV/CompCert` contains `Admitted` simulation theorems in `rust/Mir2Clightproof.v` and cannot yet serve as a closed end-to-end verified Rust compiler.

---

## Evidence

All source maps, JSON audit manifests, and Lean 4 replay logs are preserved in `support/`:

- **RustBelt (POPL 2018)**:
  - `support/rustbelt-unsafe-abstraction-model-popl-2018/source-map.json`
- **RustHornBelt (PLDI 2022)**:
  - `support/rustbelt-rusthornbelt-contract-bridge-2022/source-evidence.json` and `support/rustbelt-rusthornbelt-contract-bridge-2022/coverage.json`
- **RefinedRust & Radium (2024 / 2026)**:
  - `support/refinedrust-radium-proof-boundary-2026-v2/source-evidence.json`, `support/refinedrust-radium-proof-boundary-2026-v2/inspection.json`, and `support/refinedrust-radium-proof-boundary-2026-v2/coverage.json`
- **Verus (`0141ebc`)**:
  - `support/verus-tracked-memory-trust-0141ebc/source-evidence.json`, `support/verus-tracked-memory-trust-0141ebc/additional-source-evidence.json`, and `support/verus-tracked-memory-trust-0141ebc/coverage.json`
- **Creusot & Coma (`c4e9770`)**:
  - `support/creusot-permission-coma-trust-c4e9770/source-evidence.json`, `support/creusot-permission-coma-trust-c4e9770/additional-source-evidence.json`, and `support/creusot-permission-coma-trust-c4e9770/coverage.json`
- **Gillian-Rust (`83d739e`) & Prophecy Observation Replay**:
  - `support/gillian-rust-hybrid-resource-boundary-83d739e/source-evidence.json` and `support/gillian-rust-hybrid-resource-boundary-83d739e/coverage.json`
  - `support/focused-replay-and-encoding/ProphecyReplay.lean`, `support/focused-replay-and-encoding/replay-results.json`, `support/focused-replay-and-encoding/replay.stdout`, `support/focused-replay-and-encoding/replay.stderr`, `support/focused-replay-and-encoding/paper-identities.json`, `support/focused-replay-and-encoding/source-identities.json`
- **Foundational VeriFast (`0a83dba4`)**:
  - `support/audit_upstream.py` and `support/selected-source-audit.json` (also in `support/foundational-verifast-hinted-mirroring/`)

---

## Revalidation

1. **Gillian-Rust Prophecy Observation Lean 4.34.1 Replay**:
   - Run `lean support/focused-replay-and-encoding/ProphecyReplay.lean` (Lean `4.34.1`, revision `5045d0056413266e57c625dcd7c365b10e377c52`) and verify exit code `0`, zero `sorry`, and output matching `support/focused-replay-and-encoding/replay-results.json`.
2. **Foundational VeriFast Source Audit**:
   - Run `python3 support/audit_upstream.py` against a checkout of `verifast/verifast` at `0a83dba42db7ce0b445034ece5298afe980e57dc` to reproduce `support/selected-source-audit.json`.
3. **Artifact & Repository Pin Verification**:
   - Verify SHA-256 digests for `lambda-rust-popl18.tar.gz` (`b35bf71c...`), RustHornBelt `the_artifact.tgz` (`7e67c2d4...`), RefinedRust 2026 `artifact.tar.gz` (`34573bac...`), and Git commit hashes in `REPORT.json`.
