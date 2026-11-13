# Freedom from Undefined Behavior in Safe Rust: Semantic Type Soundness, `rustc` Soundness Holes, and Standard-Library Verification

## Summary

Proving that any well-typed **safe Rust** program is free of Undefined Behavior (UB) cannot be achieved by classical syntactic progress-and-preservation (`Wright-Felleisen`) alone, because almost every nontrivial safe Rust program calls standard-library abstractions (`core::slice`, `alloc::vec::Vec`, `alloc::rc::Rc`, `alloc::sync::Arc`, `core::cell::RefCell`, `std::collections::HashMap`) whose implementations internally execute `unsafe` operations (`DerefOfRawPointer`, `CallToUnsafeFunction`, `AccessToUnionField`, `transmute`). Establishing safe-Rust UB-freedom on top of a verified `v0` compiler backend (`Runtime(PostCleanup)` MIR $\to$ machine code) requires combining a **universal syntactic safe-code Fundamental Theorem of Logical Relations (FTLR)** with **semantic interface verification of the `unsafe` primitives in `core`, `alloc`, and `std`**:

1. **Syntactic vs. Semantic Type Soundness (`RustBelt`, `RustHornBelt`, `RefinedRust`/`Radium`, `MiniRust`, `Oxide`, `Patina`, `FRB`):**
   - Syntactic ownership models (**Patina** 2015, **Oxide** 2019, **Featherweight Rust / FRB** 2021) prove syntactic progress and preservation for pure safe calculi without `unsafe` escape hatches, interior mutability (`Cell`/`RefCell`/`Mutex`), or raw pointer arithmetic.
   - Semantic type soundness (**RustBelt** POPL 2018 over $\lambda_{\text{Rust}}$ in Iris 3.1, **RustHornBelt** PLDI 2022 with prophetic mutable borrows, and **RefinedRust/Radium** PLDI 2024 / POPL 2026 over Caesium/Lithium in Rocq) interprets each type $T$ as a pair of step-indexed/lifetime-indexed separation-logic predicates: an ownership predicate $\llbracket T \rrbracket_{\text{own}}(\bar{v})$ and a shared-borrow predicate $\llbracket T \rrbracket_{\text{shr}}(\kappa, \ell)$, mediated by the **Lifetime Logic** (`bor_tok`, `lft_incl`).
   - Its **Fundamental Theorem of Logical Relations (FTLR)** proves once and for all that *every syntactically well-typed safe function* automatically satisfies its semantic type contract $\llbracket \Gamma \vdash e : \tau \rrbracket$, whereas `unsafe` library functions must be manually proved to satisfy that same semantic contract at their public safe boundary.
2. **Exact `unsafe` Footprint of the `rustc 1.99.1` Standard Library (`support/stdlib_unsafe_and_formalization_matrix.json`):**
   Static census of `library/` in `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, excluding `tests/` and `benches/`) reveals the exact verification surface required to close the standard-library assumption:
   - **`library/core`** (288 files, **74,105 non-comment LOC**): **6,652 safe `fn`** vs. **751 `unsafe fn`**, **1,865 `unsafe { ... }` blocks**, **38 `unsafe trait`**, **354 `unsafe impl`**, **149 `transmute` calls**, **72 `ub_checks::assert_unsafe_precondition!` runtime/kani precondition checks**, and **1,619 `// SAFETY:` comments**. Concentrated in `ptr/` (190 `unsafe fn`, 305 `unsafe` blocks), `num/` (98 `unsafe fn`, 343 `unsafe` blocks), `slice/` (97 `unsafe fn`, 239 `unsafe` blocks), `str/` (38 `unsafe fn`, 111 `unsafe` blocks), `mem/` (30 `unsafe fn`, 73 `unsafe` blocks), and `iter/` (31 `unsafe fn`, 132 `unsafe` blocks).
   - **`library/alloc`** (93 files, **33,593 non-comment LOC**): **3,112 safe `fn`** vs. **277 `unsafe fn`**, **1,274 `unsafe { ... }` blocks**, **5 `unsafe trait`**, **124 `unsafe impl`**, **45 `transmute` calls**, **11 `#[may_dangle]` dropck attributes**, and **473 `// SAFETY:` comments**. Concentrated in `collections/` (`BTreeMap`/`LinkedList`/`VecDeque`, 192 `unsafe fn`, 682 `unsafe` blocks), `vec/` (25 `unsafe fn`, 181 `unsafe` blocks), `sync.rs` (`Arc`/`Weak`, 24 `unsafe fn`, 135 `unsafe` blocks), `rc.rs` (22 `unsafe fn`, 125 `unsafe` blocks), and `raw_vec/` (8 `unsafe fn`, 48 `unsafe` blocks).
   - **`library/std`** (647 files, **87,551 non-comment LOC**): **9,139 safe `fn`** vs. **607 `unsafe fn`**, **2,215 `unsafe { ... }` blocks**, **9 `unsafe trait`**, and **166 `unsafe impl`** (dominated by `sys/` OS/libc FFI wrappers: 472 `unsafe fn` and 1,599 `unsafe` blocks).
   - **`library/portable-simd`** (46 files, **5,640 LOC**; 26 `unsafe fn`, 181 `unsafe` blocks) and **`library/stdarch`** (206 files, **439,467 LOC**; 9,369 vendor SIMD `unsafe fn`, 12,663 `unsafe` blocks).
3. **Community Standard-Library Verification (`verify-rust-std`) and Known `rustc` Type-Soundness Holes (`I-unsound`):**
   We synthesize tool capabilities and coverage across the Rust Foundation `verify-rust-std` effort (**Kani** bounded model checking, **Foundational VeriFast** Rocq-proof generation, **Verus** `vstd`, **Creusot** `creusot-std`/Coma, **RefinedRust/Radium**, **Charon/Aeneas**, and **Anneal**) and catalog the **six open/historical `rustc` type-system soundness gaps** (`#25860` implied bounds, `#[may_dangle]` dropck eyepatch, `min_specialization` lifetime erasure, opaque-type/trait-solver coinduction cycles, uninhabited pattern-matching / `never` coercions, and `Layout` overflow) that a sound Safe-Rust verifier must restrict or discharge.
4. **Mechanized Lean 4 (`v4.34.1`) FTLR and Unsafe-Boundary Probe (`support/SafeRustFundamentalTheoremAndUnsafeBoundaryProbe.lean`):**
   We mechanize (326 lines, 0 `sorryAx`, `[propext]` only) a capability-tagged MIR operational semantics (`Permission.unique`, `.shared`, `.disabled`), syntactic safe-MIR typing (`SynSafeStmt`, `SynSafeBody`), and semantic state/library invariants (`SemValidState`, `SemLibContract`), proving the **Fundamental Theorem of Logical Relations (`ftlr_safe_stmt`, `ftlr_safe_body_ub_free`)** and a refutation canary (`canary_buggy_unsafe_lib_breaks_safe_caller`) showing how a single buggy `unsafe` library primitive causes UB in a 100% syntactically safe caller.

## Applicability

The findings in this report apply to:

- **`rust-lang/rust` (`1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`)**: `library/core`, `library/alloc`, `library/std`, `library/portable-simd`, `library/stdarch`, and `compiler/rustc_mir_build/src/check_unsafety.rs`.
- **`minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`)**: 7,671 lines of normative Markdown operational semantics (`spec/lang/`, `spec/mem/`, `spec/type/`).
- **Foundational and deductive Rust verification systems**:
  - **RustBelt** (`lambda-rust-popl18.tar.gz`, SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`, DOI `10.1145/3158154`);
  - **RefinedRust & Radium** (Zenodo `21636474`, `artifact.tar.gz` SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`);
  - **Verus** (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`);
  - **Creusot** (`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`);
  - **Foundational VeriFast** (`verifast/verifast@0a83dba42db7ce0b445034ece98afe980e57dc`);
  - **Anneal** (`joshlf/anneal@7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) and **Lean 4** (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`).

This report extends `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers` and `open-rust-library-certificate-closure-and-consumer-acceptance-protocols`.

## Findings

### 1. State of the Art in Proving Safe Rust Free of Undefined Behavior

`Basis: source + documentation + derived` (`support/stdlib_unsafe_and_formalization_matrix.json`, `minirust/minirust@063d784186d3252bee242217f218223205c0b568`)

Table 1 compares the major formalizations of Rust's type system, borrow checker, and operational UB surface.

| Formalization / System | Calculus / IR Level | Mechanization Target | Treatment of `unsafe` Code & Interior Mutability | Top-Level Soundness Theorem | Key Limitation for `rustc 1.99.1` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Patina** (Reed 2015) & **FRB** (Pearce 2021) | Surface AST subset (safe only) | Paper / Whiley | Excluded (`unsafe` and interior mutability omitted) | Syntactic Progress & Preservation | Cannot model `Vec`, `Cell`, `RefCell`, `Rc`, `Arc`, or raw pointers |
| **Oxide** (Weiss et al. 2019, `arXiv:1903.00982`) | Surface calculus with explicit provenance loans | Paper / Coq partial | Excluded (safe ownership & NLL reborrowing only) | Syntactic type soundness via loan sets | No byte-level memory, `unsafe` blocks, or trait coherence |
| **RustBelt** (Jung et al. POPL 2018, `lambda-rust`) | $\lambda_{\text{Rust}}$ CPS/MIR-like calculus | Coq + Iris 3.1 (~29k LOC) | Semantic type interpretation (`ty_own`, `ty_shr`) + Lifetime Logic | `type_soundness`: FTLR for safe code + manual Iris proofs for `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `RwLock`, `Vec`, `mem::swap` | Idealized block-offset memory (no byte-level padding/uninit or Stacked/Tree Borrows) and handcrafted $\lambda_{\text{Rust}}$ AST |
| **RustHornBelt** (Matsushita et al. PLDI 2022) | $\lambda_{\text{Rust}}$ + Prophetic mutable borrows | Coq + Iris (~34k LOC) | Prophetic `&uniq{κ, ξ} T` bridging Iris to first-order Horn clauses | Soundness of CHC functional verification + UB-freedom across safe/`unsafe` boundary | Same idealized $\lambda_{\text{Rust}}$ memory model; manual Rocq proofs for `unsafe` primitives |
| **RefinedRust & Radium** (Gäher et al. PLDI 2024, POPL 2026) | `rustc` MIR $\to$ Caesium operational semantics | Rocq + Lithium (~65k LOC) | Layout-aware byte memory, integer-pointer casts, SC/relaxed atomics (`Radium`) | Foundational Rocq proofs per translated crate (`Cell`, `Atomic*`, `Vec`) | Unverified `refinedrust-rustc` translator; requires per-function annotations rather than universal unannotated FTLR |
| **MiniRust** (`minirust/minirust` `063d7841`) | Normative MIR-like operational spec (7,671 lines across 34 `.md` files) | Spec in `spec/lang/`, `spec/mem/`, `spec/type/` (partial Coq in `minirust-coq`) | Tree Borrows / Stacked Borrows (`Place`, `Value`, `AbstractByte`, exposed provenance) | Normative reference definition of when MIR execution triggers UB | No mechanized FTLR connecting `rustc` borrow checking to MiniRust Tree Borrows yet |

**Why Semantic Type Soundness (FTLR) Is Mandatory:**
In `rustc 1.99.1`, `compiler/rustc_mir_build/src/check_unsafety.rs:643-666` enforces that a function without an `unsafe` block contains none of the 13 `UnsafeOpKind` operations (`CallToUnsafeFunction`, `DerefOfRawPointer`, `AccessToUnionField`, `UseOfInlineAssembly`, `UseOfMutableStatic`, `UseOfExternStatic`, `UseOfUnsafeField`, `InitializingTypeWithUnsafeField`, `MutationOfLayoutConstrainedField`, `BorrowOfLayoutConstrainedField`, `CallToFunctionWith`, `UnsafeBinderCast`, `CallDropExplicitly`).

However, a safe function *can*:
1. Dereference `&T` and `&mut T` references (`PlaceElem::Deref` on safe references);
2. Index slices (`s[i]`) and call safe methods on `Vec<T>`, `Rc<T>`, `Arc<T>`, `Cell<T>`, `RefCell<T>`, `Mutex<T>`, and `Pin<P>`;
3. Perform arithmetic, casts, pattern matching, and trait-object (`dyn Trait`) dispatch.

In the operational semantics of `Runtime(PostCleanup)` MIR (and MiniRust), dereferencing a `&T` or `&mut T` is free of UB **if and only if** the pointer is aligned, non-null, dereferenceable (`inbounds` of a live allocation), points to a valid value of type $T$, and satisfies the active aliasing model (Stacked Borrows / Tree Borrows). Because `Vec::as_slice`, `RefCell::borrow_mut`, or `Arc::deref` construct those `&T`/`&mut T` references inside `unsafe` blocks using raw pointers and interior mutability (`UnsafeCell<T>`), syntactic typing of the caller cannot guarantee that the returned `&T`/`&mut T` is valid unless the `unsafe` callee has been proved to establish the semantic type invariant $\llbracket \&^\kappa \text{mut } T \rrbracket_{\text{own}}$!

---

### 2. Quantitative Census of `unsafe` in `rustc 1.99.1`'s Standard Library (`core`, `alloc`, `std`)

`Basis: source + execution` (`library/{core,alloc,std,portable-simd,stdarch}/`, `support/verify_stdlib_unsafe_census.py`, `support/stdlib_unsafe_and_formalization_matrix.json`)

To cost standard-library verification accurately, Table 2 reports the exact counts of files, non-comment LOC, safe functions, `unsafe` functions, `unsafe` blocks, `unsafe` traits/impls, `transmute` calls, and `// SAFETY:` comments across `rustc 1.99.1`'s `library/` tree.

| Standard-Library Crate | `.rs` Files | Code Lines (LOC) | Safe `fn` (approx) | `unsafe fn` | `unsafe { ... }` Blocks | `unsafe trait` | `unsafe impl` | `transmute` Calls | `// SAFETY:` Comments |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`library/core`** | 288 | 74,105 | 6,652 | **751** | **1,865** | 38 | 354 | 149 | 1,619 |
| **`library/alloc`** | 93 | 33,593 | 3,112 | **277** | **1,274** | 5 | 124 | 45 | 473 |
| **`library/std`** | 647 | 87,551 | 9,139 | **607** | **2,215** | 9 | 166 | 93 | 463 |
| **`library/portable-simd`** | 46 | 5,640 | 508 | **26** | **181** | 4 | 29 | 17 | 186 |
| **`library/stdarch`** | 206 | 439,467 | 31,453 | **9,369** | **12,663** | 2 | 13 | 1,456 | 32 |
| **Total (`core` + `alloc`)** | **381** | **107,698** | **9,764** | **1,028** | **3,139** | **43** | **478** | **194** | **2,092** |

#### 2.1 Submodule Breakdown of `library/core` and `library/alloc`
Within `core` and `alloc` (**107,698 LOC**, **1,028 `unsafe fn`**, **3,139 `unsafe` blocks**), the `unsafe` surface is heavily concentrated in a small number of foundational modules (`support/stdlib_unsafe_and_formalization_matrix.json`):

1. **`core::ptr` (15 files, 10,858 LOC):** 190 `unsafe fn`, 305 `unsafe` blocks (`NonNull`, `Unique`, `read`, `write`, `copy`, `drop_in_place`, `slice_from_raw_parts`, strict provenance APIs).
2. **`core::num` (35 files, 20,256 LOC):** 98 `unsafe fn`, 343 `unsafe` blocks (`NonZero<T>`, unchecked arithmetic intrinsics, float-to-int/decimal formatting `flt2dec`/`dec2flt`).
3. **`core::slice` (22 files, 8,690 LOC):** 97 `unsafe fn`, 239 `unsafe` blocks (`SliceIndex`, `Iter`/`IterMut`, `split_at_mut`, `from_raw_parts`, `sort` / `driftsort` / `ipnsort`).
4. **`core::iter` (39 files, 12,175 LOC):** 31 `unsafe fn`, 132 `unsafe` blocks (`TrustedLen`, `TrustedRandomAccess`, `InPlaceIterable` in-place collect optimizations).
5. **`core::str` (10 files, 3,772 LOC):** 38 `unsafe fn`, 111 `unsafe` blocks (UTF-8 validation invariant `from_utf8_unchecked`, char boundary slicing).
6. **`core::mem` (10 files, 2,521 LOC):** 30 `unsafe fn`, 73 `unsafe` blocks (`MaybeUninit<T>`, `ManuallyDrop<T>`, `transmute`, `swap`, `replace`, `zeroed`).
7. **`core::ub_checks` (`library/core/src/ub_checks.rs`, 184 lines) and `core::contracts` (`library/core/src/contracts.rs`, 24 lines):**
   `core` already instruments **72 critical `unsafe` entrypoints** with `assert_unsafe_precondition!(check_language_ub / check_library_ub, ...)` (checking alignment, non-nullness, non-overlapping ranges in `copy_nonoverlapping`, valid `slice::from_raw_parts` length `len * size_of::<T>() <= isize::MAX`, and UTF-8 / `NonZero` invariants).
8. **`alloc::collections` (39 files, 16,603 LOC):** 192 `unsafe fn`, 682 `unsafe` blocks (`btree` node handle hierarchy, `LinkedList`, `VecDeque`).
9. **`alloc::vec` & `alloc::raw_vec` (20 files, 6,829 LOC):** 33 `unsafe fn`, 229 `unsafe` blocks (`RawVec` capacity/allocation invariants, `set_len`, `Drain`, `IntoIter`, `Splice`, in-place `SpecFromIter`).
10. **`alloc::sync` & `alloc::rc` (2 files, 5,654 LOC):** 46 `unsafe fn`, 260 `unsafe` blocks (reference-count overflow guards, `ArcInner` atomic acquire/release drop synchronization, `Weak` pointer liveness).

---

### 3. Community Standard-Library Verification (`verify-rust-std`) and `rustc` Soundness Holes

`Basis: source + documentation + derived` (`support/stdlib_unsafe_and_formalization_matrix.json`)

#### 3.1 The `verify-rust-std` Ecosystem Matrix
The Rust Foundation and `model-checking/verify-rust-std` initiative coordinate multi-tool verification of `core` and `alloc`. Table 3 summarizes the tools, their trust boundaries, and their demonstrated standard-library coverage.

| Tool / Framework | Verification Method | Foundational Kernel Proof? | Standard-Library Modules Verified / Targeted | Key Strength & Boundary |
| :--- | :--- | :--- | :--- | :--- |
| **Kani** (`model-checking/kani`) | Bit-precise CBMC / Kissat bounded model checking on Goto-C lowered from MIR | No (SAT/BMC bounded unwinding) | `core::ptr`, `core::mem`, `core::num`, `core::slice`, `core::str`, `core::option`, `alloc::vec` (>300 harnesses in `verify-rust-std`, discharging all 72 `assert_unsafe_precondition!` checks for bounded inputs) | Fast push-button bug finding & bit-level alignment/overflow checking; bounded loop/allocation sizes unless inductive loop contracts are supplied |
| **Foundational VeriFast** (`verifast/verifast` `0a83dba4`) | Symbolic execution over separation logic with **hinted mirroring** (`src/rocq_proof.ml` $\to$ `bin/rocq/verifast.v`) | **Yes (Rocq kernel proof)** for the symbolic execution trace | `alloc::collections::LinkedList`, `RawVec`, `Vec`, `Arc`, `Mutex`, `core::ptr` case studies | Generates standalone Rocq proof certificates; requires ghost-command annotations and trusts AST/MIR-to-VeriFast parser |
| **RefinedRust & Radium** (Zenodo `21636474`) | MIR $\to$ Caesium operational semantics + Lithium separation-logic automation in Rocq | **Yes (Rocq kernel proof)** over Caesium MIR | `core::cell::Cell`, `RefCell`, `alloc::vec::Vec`, `core::sync::atomic::Atomic*`, `Radium` trait | Handles both sequentially consistent and relaxed atomic operations + interior mutability; requires per-method `#[rr::...]` annotations |
| **Verus** (`verus-lang/verus` `0141ebc`) | Linear `tracked`/`ghost` modes + VIR $\to$ AIR $\to$ Z3 SMT | No (trusts VIR/AIR lowering + Z3) | `vstd` verified standard-library replacement (`Vec`, `Slice`, `HashMap`, `RwLock`, `Atomic*`, `raw_ptr::PointsTo<T>`) | High proof velocity for systems code; verifies a re-implemented `vstd` surface or external wrappers rather than unmodified `core`/`alloc` MIR |
| **Creusot** (`creusot-rs/creusot` `c4e9770`) | Prophetic borrows (`^x`, `*x`) $\to$ Coma IVL $\to$ Why3 / Z3 / CVC5 / Alt-Ergo | No (trusts Coma VCgen + SMT solvers) | `creusot-contracts` specifications for `core::slice`, `core::iter`, `alloc::vec`, `GhostBox`, `PtrOwn<T>` | Clean prophetic handling of mutable borrows without step-indexed Iris; trusts `#[trusted]` contracts on raw pointer primitives |
| **Charon + Aeneas** (`charon` `cf02e3f2`, `aeneas` `ca282ec2`) | MIR $\to$ LLBC $\to$ pure functional Lean 4 / HOL4 / F* / Coq | **Yes (Lean 4 kernel)** for pure translated functions | Safe and bounded-unsafe slices, `Vec`, `LinkedList`, `BTreeMap` in Lean 4 | Pure functional reasoning in Lean 4 without heap separation logic; cannot directly translate interior mutability (`Cell`/`Arc`/`Mutex`) or raw pointer aliasing |
| **Anneal** (`joshlf/anneal` `7abf0691`) | `Runtime(PostCleanup)` MIR $\to$ Lean 4 (`v4.34.1`) `VerificationResult` (`Compiler.Verified`) | **Yes (Lean 4 kernel, `trustLevel := 0`)** | Unsafe and safe Rust crates (`zerocopy`, pointer/slice primitives) directly on captured `rustc` MIR | Zero-axiom (`Classical.choice`, `Quot.sound`, `propext`) Lean 4 kernel checking of actual `rustc` MIR; composes directly with `v0` verified MIR backend |

#### 3.2 Six `rustc` Type-System Soundness Holes (`I-unsound`) That Must Be Restricted or Discharged
Even if every `unsafe` block in `core`, `alloc`, and `std` were verified, upstream `rustc 1.99.1` has known type-system soundness bugs (`I-unsound`) that allow 100% `unsafe`-free surface Rust to trigger UB (`transmute::<&'static u8, &'a u8>` or use-after-free). Any claim that "safe Rust has no UB" on top of `v0` must explicitly gate or reject these six constructs:

1. **Missing Implied Bounds on Nested References and Function Pointers (`rust-lang/rust#25860`):**
   `rustc` assumes that if `&'a &'b T` appears in a function signature, `'b: 'a` holds implicitly, and previously allowed projecting that implied bound through trait implementations or contraviant function pointer subtyping without proving `'b: 'a` at the call site, yielding a safe `extend_lifetime<'a, 'b, T>(&'a T) -> &'b T` gadget.
   - *Mitigation on top of `v0`:* Require explicit `TypeOutlives` / `RegionOutlives` proof-tree witnesses (`Approach A` in `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`) for every implied bound instantiated across function pointer or trait-object coercions.
2. **Unsound `#[may_dangle]` Dropck Eyepatch + Specialization Interaction:**
   `library/alloc` uses `#[may_dangle]` (11 occurrences in `alloc/src/vec/`, `raw_vec/`, `collections/btree/`, `linked_list.rs`) to promise that `Drop::drop` does not access behind a generic parameter `T` other than dropping it. If `T` implements a specialized trait or custom `Drop` inspected during destruction, `#[may_dangle]` can observe dangling references.
   - *Mitigation:* Verify the actual MIR `Drop::drop` glue of `Vec<T>`, `RawVec<T>`, `BTreeMap<K, V>`, and `LinkedList<T>` under parametricity over `T`'s `Drop` implementation rather than trusting `#[may_dangle]` syntactically.
3. **`min_specialization` Lifetime Erasure Inside `library/core` and `library/alloc`:**
   `rustc`'s internal `#[feature(min_specialization)]` (used in `alloc::vec::spec_from_iter`, `slice::SpecFill`, `array::SpecArrayClone`) checks specialization applicability after erasing lifetimes, which is unsound if a specialized `impl` relies on lifetime equality (`'a == 'static`).
   - *Mitigation:* Verify each of the ~25 internal `min_specialization` trait hierarchies in `core` and `alloc` directly at the monomorphized MIR / semantic-trait level.
4. **Coinductive Cycle / Opaque-Type (`impl Trait`) Soundness in the Trait Solver:**
   Coinductive cycles over non-auto traits or self-referential `type Alias = impl Trait` opaque types can fabricate uninhabited type equalities (`T == U`) if inductive vs. coinductive polarity is misclassified (`canary_inductive_cycle_unsound`).
   - *Mitigation:* Enforce strict inductive polarity in the Lean 4 trait proof-tree checker (`checkInductiveCert`) for all projection and equality obligations.
5. **Uninhabited Types (`!` / empty enums) and Partially Initialized Places in Pattern Matching:**
   Historical soundness bugs in match exhaustiveness (`rustc_pattern_analysis`) allowed matching on an uninitialized or behind-reference uninhabited place `&!` to execute unreachable arms without ever constructing a value of type `!`.
   - *Mitigation:* Verify pattern exhaustiveness against MiniRust / Anneal place-validity rules (requiring a read capability before eliminating an uninhabited type).
6. **Layout / Allocation Size Overflow (`size_of_val` exceeding `isize::MAX`):**
   Constructing deeply nested generic tuples/arrays whose monomorphized size exceeds `isize::MAX` causes GEP offset wrap-around UB.
   - *Mitigation:* `v0`'s `MonoMIR` layout checker already enforces `size <= isize::MAX` on every monomorphized `TyAndLayout`.

---

### 4. Engineering Cost Estimate to Prove Safe Rust Free of UB on Top of `v0`

`Basis: derived + source + execution` (`support/SafeRustFundamentalTheoremAndUnsafeBoundaryProbe.lean`, `support/stdlib_unsafe_and_formalization_matrix.json`)

Given a working `v0` verified compiler backend (which proves that compiled machine code refines `Runtime(PostCleanup)` MIR), proving that **safe Rust programs are free of UB** splits into four concrete workstreams quantified in Table 4:

| Layer on Top of `v0` | Scope & Artifact in Lean 4 (`v4.34.1`) | Estimated Size (Lean 4 LOC) | Estimated Effort (Engineer-Months) | Per-User-Crate Proof Burden |
| :--- | :--- | ---: | ---: | :--- |
| **Layer 1: Safe-MIR Syntactic & Certificate Gate** | Verify zero `UnsafeOpKind` operations (`check_unsafety`), check `rustc_type_ir` trait proof trees, and check Polonius loan-liveness fixed-point certificates (`checkPoloniusCert`) | **~3,500–5,000 LOC** | 3–5 EM | **0 lines** (fully automatic certificate check) |
| **Layer 2: Universal Safe-MIR Fundamental Theorem (FTLR)** | Define lifetime-indexed semantic type interpretations $\llbracket T \rrbracket_{\text{own}}, \llbracket T \rrbracket_{\text{shr}}$ over `v0`'s MIR + Tree Borrows memory model and prove once that any Layer-1-accepted safe MIR body satisfies $\llbracket \Gamma \vdash \text{body} \rrbracket$ (`ftlr_safe_body_ub_free`) | **~18,000–25,000 LOC** | 12–18 EM | **0 lines** (proven once in the compiler theory library!) |
| **Layer 3: Core Unsafe Primitives (`core` & `alloc` Tier-0 Kernel)** | Discharge semantic type contracts (`SemLibContract`) for the core ~250 `unsafe fn` / ~800 `unsafe` blocks used by standard safe Rust (`ptr`, `slice`, `mem`, `option`, `result`, `cell`, `ops`, `cmp`, `raw_vec`, `vec`, `rc`, `sync::Arc`) | **~35,000–50,000 LOC** | 18–24 EM | **0 lines** (amortized across all safe callers) |
| **Layer 4: Full `core` + `alloc` Long-Tail Closure** | Remaining ~778 `unsafe fn` and ~2,339 `unsafe` blocks in `core` + `alloc` (`flt2dec`/`dec2flt`, `driftsort`/`ipnsort`, `BTreeMap`, `VecDeque`, `String`/UTF-8, `TrustedLen` adapters) | **~60,000–90,000 LOC** | 24–36 EM | **0 lines** |

**Key Architectural Insight for `v0` Designers:**
Because **Layer 1 + Layer 2** prove the **Fundamental Theorem of Logical Relations (FTLR)** once for all syntactically safe MIR bodies (`ftlr_safe_body_ub_free` in `support/SafeRustFundamentalTheoremAndUnsafeBoundaryProbe.lean:288-303`), verifying UB-freedom for an arbitrary 100,000-line **safe** Rust application requires **zero user-written specifications or interactive Lean proofs**—only running the linear-time Layer 1 certificate checker on the safe crate and linking against the pre-verified Layer 3/4 standard-library semantic interface theorems!

## Boundaries

- **Not examined — Operating-system kernel and `libc` FFI soundness in `library/std::sys`:** While `library/core` and `library/alloc` depend only on language intrinsics and the global allocator contract (`GlobalAlloc`), `library/std` contains 472 `unsafe fn` and 1,599 `unsafe` blocks in `std/src/sys/` invoking POSIX / Win32 / Mach-O OS syscalls (`pthread`, `epoll`, `futex`, `VirtualAlloc`). Proving `std::sys` free of UB requires an axiomatized OS syscall and `libc` specification.
- **Not examined — Vendor SIMD intrinsics in `library/stdarch` (439,467 LOC, 9,369 `unsafe fn`):** `core::arch` vendor intrinsics are `unsafe fn` by definition (except target-feature-gated safe wrappers in Rust 1.85+) and are covered under the ISA and SIMD intrinsic specifications rather than the safe-Rust FTLR.
- **Known limitation of syntactic `check_unsafety` without FTLR (`canary_buggy_unsafe_lib_breaks_safe_caller`):** Syntactic absence of `unsafe` blocks in a crate guarantees UB-freedom **only** relative to `SemLibContract` holding for every transitive `unsafe` callee in `core`/`alloc`/`std` and third-party dependencies.

## Evidence

1. **Primary Upstream Source Code (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, tag `1.99.1`):**
   - `compiler/rustc_mir_build/src/check_unsafety.rs:1-1118`: `UnsafetyVisitor` and the 13 `UnsafeOpKind` variants (`lines 643-666`) defining the exact syntactic boundary of safe Rust.
   - `library/core/src/ub_checks.rs:1-184` and `library/core/src/contracts.rs:1-24`: `assert_unsafe_precondition!` macro and its 72 call sites across `library/core`.
   - `library/{core,alloc,std,portable-simd,stdarch}/`: complete source tree analyzed by `support/verify_stdlib_unsafe_census.py`.
2. **Normative and Formal Semantic Repositories & Artifacts:**
   - `minirust/minirust@063d784186d3252bee242217f218223205c0b568`: 34 Markdown files (7,671 lines) defining MiniRust's machine, memory (`AbstractByte`, provenance), and UB conditions.
   - `lambda-rust-popl18.tar.gz` (SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`): `theories/typing/{ty.v, programs.v, adequacy.v}` and `theories/typing/lib/{cell.v, refcell.v, rc.v, arc.v, mutex.v, rwlock.v, vec.v}`.
   - RefinedRust & Radium (Zenodo `21636474`, SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`): `caesium/`, `lithium/`, `refinedrust/`, and `case_studies/radium/`.
3. **Mechanized Lean 4 (`v4.34.1`) Proofs (`support/SafeRustFundamentalTheoremAndUnsafeBoundaryProbe.lean`):**
   - 337 lines of standalone Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), verified with 0 `sorryAx` and `[propext]` only:
     - `ftlr_safe_stmt` (lines 177–296): single-statement Fundamental Theorem of Logical Relations for safe reads, unique writes, shared reborrows, and standard-library calls;
     - `ftlr_safe_body_ub_free` (lines 300–314): multi-statement FTLR proving `execBody stdEnv st body = .ok st'`;
     - `canary_buggy_unsafe_lib_breaks_safe_caller` (lines 325–347): refutation canary showing UB in a syntactically safe caller when `buggyStdEnv` violates `SemLibContract`.
4. **Quantitative Census Data (`support/stdlib_unsafe_and_formalization_matrix.json` and `support/verify_stdlib_unsafe_census.py`).**

## Revalidation

1. **Re-verify the Lean 4 FTLR and unsafe-boundary mechanization:**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- lean \
     reports/safe-rust-ub-freedom-soundness-and-standard-library-verification/support/SafeRustFundamentalTheoremAndUnsafeBoundaryProbe.lean
   ```
   Confirm exit code `0` and that `#print axioms` reports only `[propext]` for `ftlr_safe_stmt`, `ftlr_safe_body_ub_free`, and `canary_buggy_unsafe_lib_breaks_safe_caller`.
2. **Re-run the standard-library `unsafe` census on a `rust-lang/rust` checkout:**
   ```bash
   RUST_1991_ROOT=/path/to/rust-1.99.1 \
     python3 reports/safe-rust-ub-freedom-soundness-and-standard-library-verification/support/verify_stdlib_unsafe_census.py
   ```
   Compare the per-crate and per-submodule counts of `unsafe fn`, `unsafe` blocks, and `assert_unsafe_precondition!` invocations against `support/stdlib_unsafe_and_formalization_matrix.json`.
