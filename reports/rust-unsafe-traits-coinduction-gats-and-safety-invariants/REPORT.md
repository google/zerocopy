# Rust Unsafe Trait Invariants, Auto-Trait Coinduction, Generic Associated Types, Unsafe Fields, and Safety-Boundary Completeness

## Summary

Verifying Rust abstractions that rely on `unsafe trait` implementations, marker traits, generic associated types (GATs), or module-encapsulated state requires distinguishing what the Rust compiler enforces syntactically from the semantic invariants that unsafe code relies on:

1. **`unsafe trait` and `unsafe impl` as implementation-side proof obligations:** Under the Rust Reference, declaring an `unsafe trait` attaches a semantic safety contract to implementations rather than callers, and writing `unsafe impl` is an unchecked programmer assertion that the contract holds (`rustc` checks only the syntactic match via `E0200` and `E0199`). Trait safety (`unsafe trait` vs. `trait`) and method safety (`unsafe fn` vs. `fn`) are orthogonal: safe code may freely invoke safe methods on a bound `T: UnsafeTrait` or trait object `dyn UnsafeTrait`, and safe subtraits (`trait Sub: UnsafeSuper`) transitively carry their unsafe supertraits' semantic contracts.
2. **Coinductive auto-trait solving vs. cyclic `unsafe impl` soundness:** `Send` and `Sync` are `pub unsafe auto trait`s whose structural derivations are coinductive so recursive types (`struct Link { next: Option<Box<Link>> }`) can satisfy `Send`. However, in both the classic trait solver (`coinductive_match`) and the next-generation trait solver (`CurrentGoalKind::CoinductiveTrait` mapping `GoalSource::ImplWhereBound` to `PathKind::Coinductive` with provisional `Certainty::Yes`), a user-written self-referential implementation such as `unsafe impl Send for NotSend where NotSend: Send {}` participates in the same coinductive cycle acceptance, whereas an analogous cycle on a non-auto trait is rejected with `E0275`. Consequently, compiler derivability of an `unsafe impl`'s own where-bounds does not establish that its semantic safety obligation has been discharged through productive structural reduction.
3. **Generic associated types (GATs), specialization, and selected-implementation evidence:** A GAT (`type Assoc<'a>: ... where Self: 'a`) denotes an indexed family of types and laws quantified over all permitted arguments; proving an equality at a single normalized lifetime does not prove the family law, and GATs render a trait non-dyn-compatible (`E0038`). Furthermore, default trait method bodies, blanket implementations, and `min_specialization` resolve to different executable bodies depending on monomorphization and `leaf_def.is_final()`, so a sound verification certificate must bind the exact resolved implementation identity and substitutions rather than assuming the trait default specification applies.
4. **Safety-boundary completeness beyond syntactic `unsafe` blocks:** Rust's `unsafe` keyword gates a fixed inventory of language-level operations, not every state transition that affects an abstraction's safety invariant. Safe code can overwrite places via assignment, mutate shared state through `Cell::set`, obtain raw mutable pointers via `UnsafeCell::get`, transition initialization state via `MaybeUninit::{uninit, write}`, and suppress destructors via `core::mem::forget`. Soundness proofs must therefore cover all invariant producers, safe and unsafe state transitions across visibility boundaries, and unsafe consumers.
5. **Unstable `#![feature(unsafe_fields)]` (RFC 3458):** Marking a named record field `unsafe` makes variant construction (`ExprKind::Adt`) and field projection (`ExprKind::Field`, including reads, writes, borrows, `&raw const`, and pattern bindings) require an `unsafe` block (`E0133`), requires `unsafe impl Copy` (`coherence/unsafety.rs`), and suppresses automatic structural implementations of unsafe auto traits (`Send`, `Sync`) in both trait solvers. However, `unsafe` fields do not relax language-level type validity (`T`), do not make `..` pattern ignoring or `offset_of!` unsafe, and do not make automatic `Drop` unsafe.

## Applicability

This report synthesizes findings across the compiler revisions, specifications, RFCs, and formal verification artifacts declared in `REPORT.json`:

- **Rust compiler and standard library (multi-version coverage):**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`): primary source for `unsafe trait` coherence checking (`compiler/rustc_hir_analysis/src/coherence/unsafety.rs`), `Send`/`Sync`/`TrustedLen` (`library/core/src/{marker.rs,iter/traits/marker.rs}`, `library/alloc/src/rc.rs`), classic and next-solver auto-trait coinduction (`compiler/rustc_trait_selection` and `compiler/rustc_next_trait_solver`), safe interior-mutability/uninitialized-storage/forget primitives (`library/core/src/{cell.rs,mem/maybe_uninit.rs,mem/mod.rs,ptr/mod.rs}`), and `#![feature(unsafe_fields)]`.
  - `rust-lang/rust@1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6` (`1.101.0-nightly`, `rustc` binary SHA-256 `eb3147b0fd9629eba4886d6c4072d0ba21ae493b43b776871c1645f0e977916e`, examined on `aarch64-apple-darwin`, edition `2024`, `-C opt-level=1`): used to execute the GAT lending control, `min_specialization` dispatch control, structural `Send` vs. ordinary-cycle `E0275` control, and GAT `dyn` rejection `E0038` control.
  - `rust-lang/rust@f6c1107f8be13e48465e12c0fd26e6a39fe18e4f`: later compiler snapshot cross-checked for next-solver `consider_auto_trait_candidate` (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs`).
- **Rust Reference, RFC, and Developer Guide:**
  - `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` and `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/{unsafe-keyword.md,unsafety.md,items/traits.md,items/associated-items.md,items/implementations.md,special-types-and-traits.md,expressions/operator-expr.md}`).
  - `rust-lang/rfcs@f5749baed7b7ecfe03d95dc9197d0c1344712f43` (`text/3458-unsafe-fields.md`, RFC 3458).
  - `rust-lang/rustc-dev-guide@bfbca953b5d4a3596081360a1c79ad88f31e7d60` (`src/solve/coinduction.md` and `src/traits/specialization.md`).
- **External verification framework artifact:**
  - RefinedRust 2026 artifact (`zenodo: 21636474`, `artifact.tar.gz`, SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`), specifically `traits/{registry.rs,resolution.rs}` and Radium `specs/traits.rs`.

**Cross-version invariance vs. version-specific differences:**
- *Invariant across examined `rustc` revisions (`14210df0e27c`, `1d81eb4ad9cd`, and `f6c1107f8be1`):* `unsafe trait`/`unsafe impl` coherence rules (`E0199`/`E0200`), GAT family parameterization and `dyn` incompatibility (`E0038`), structural auto-trait coinduction vs. ordinary-trait cycle rejection (`E0275`), next-solver `consider_auto_trait_candidate` ordering (checking explicit implementations before structural field constituents), and safe-API state transitions (`Cell::set`, `UnsafeCell::get`, `MaybeUninit`, `mem::forget`).
- *Feature-gated or evolving behavior:* `#![feature(unsafe_fields)]` is an incomplete nightly feature at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` where the compiler parser and `tests/ui/unsafe-fields/unsafe-fields.rs` accept `unsafe` fields inside a `union` declaration despite RFC 3458 stating that unsafe union fields remain forbidden pending further design. Similarly, `#![feature(min_specialization)]` is an unstable nightly feature.

## Findings

### 1. `unsafe trait` Invariants, `unsafe impl` Coherence, and Contract Provenance

`Basis: normative | documentation | source | derived`

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (indexed in `support/rust-unsafe-trait-invariants/unsafe-trait-contract-matrix.json` and `support/rust-unsafe-trait-invariants/source-map.json`), `unsafe trait` establishes a trust boundary at implementation sites rather than call sites:

1. **Syntactic enforcement vs. semantic uncheckability (`compiler/rustc_hir_analysis/src/coherence/unsafety.rs`, blob `8114106a2a4117a1e8e1d706afff753ff834f263`):**
   - Implementing an `unsafe trait` without the `unsafe` keyword is rejected with `E0200` (*"the trait `...` requires an `unsafe impl` declaration; the trait `...` enforces invariants that the compiler can't check"*).
   - Conversely, writing `unsafe impl` for an ordinary safe trait is rejected with `E0199`.
   - Adding `unsafe` to the `impl` header satisfies `rustc`'s coherence gate without verifying the prose safety contract.
2. **Orthogonality of trait safety and method safety (`src/unsafe-keyword.md`, `src/items/traits.md`):**
   - Using a correctly implemented `unsafe trait` is safe. A safe method inside an `unsafe trait` can be called from safe code without an `unsafe` block, whereas an `unsafe fn` inside either a safe or unsafe trait imposes a per-call precondition on the caller.
   - Dynamic dispatch (`dyn UnsafeTrait`) and safe subtraits (`trait Child: UnsafeSuper`) preserve the implementation-side obligation: constructing or satisfying the bound requires an implementation of the unsafe trait, and consumers may rely on that implementation's invariant without new call-site `unsafe` blocks.
3. **Distinct standard-library unsafe-trait patterns (`library/core/src/marker.rs` blob `53141aabacc453e3781bbe9593618e26c06ca732`, `library/core/src/iter/traits/marker.rs` blob `542d283fe95abab901534fd21e38bddaa6a28823`):**
   - *Pure semantic markers (`Send`, `Sync`):* Have zero associated items; their entire meaning is thread-transfer or shared-reference safety, with provenance split between **compiler-derived** structural auto-trait implementations and **user-written** `unsafe impl`s (alongside explicit negative impls such as `!Send` and `!Sync` on raw pointers and `alloc::rc::Rc`).
   - *Method-refining unsafe contracts (`TrustedLen`, `TrustedStep`):* Refine the behavior of safe methods on a supertrait (`Iterator::size_hint` must return an exact bound or diverge before exhaustion) so downstream `unsafe` code (such as `Vec::from_iter` buffer preallocation) can omit bounds checks.
   - Because downstream extractors such as Charon do not structurally preserve the `unsafe` modifier on trait declarations or implementations, a verification environment must attach an explicit semantic predicate and provenance tag (compiler-derived, standard-library axiom, or user proof obligation) to every `unsafe trait` bound.

### 2. Auto-Trait Coinduction and Self-Referential `unsafe impl` Cycles

`Basis: normative | documentation | source | execution | derived`

Auto traits (`Send`, `Sync`) require coinductive cycle handling so that recursive data structures (`struct Link { next: Option<Box<Link>> }`) do not fail trait selection when their field obligations recurse back to `Link: Send`. However, inspecting both `rustc` trait solvers at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `f6c1107f8be13e48465e12c0fd26e6a39fe18e4f` shows that explicit user `unsafe impl` where-bounds are admitted into the same coinductive cycle rule:

```rust
use std::rc::Rc;
struct NotSend(Rc<()>); // Rc<()> is explicitly !Send and !Sync
unsafe impl Send for NotSend where NotSend: Send {}
```

1. **Classic trait solver (`compiler/rustc_trait_selection/src/traits/select/mod.rs` blob `eadc937639f209ceaebef0eaf59cf4b279d507e7`, `compiler/rustc_middle/src/ty/mod.rs` blob `6df1ed82d260a5c95dbe9671f2c7ddf8585c36ab`):**
   - When trait selection encounters a cycle of trait predicates, `coinductive_match` accepts the cycle whenever every predicate in the cycle satisfies `trait_is_coinductive` (which holds for auto traits and `Sized`). It does not distinguish whether the cycle edge came from an automatically synthesized structural impl or a user-written `unsafe impl` where-clause.
2. **Next-generation trait solver (`compiler/rustc_next_trait_solver/src/solve/{eval_ctxt/mod.rs,search_graph.rs,trait_goals.rs}`, blobs `54d306466cf5b1b5b8f32625606b469dcfa7d5a8`, `a46261fcf72716f5571a996da35fa0ffc6e4504f`, `e09864295020f89899863236d38853505ed1f0ef`):**
   - In `consider_auto_trait_candidate`, the solver checks explicit implementations before structural constituent fields.
   - Under `CurrentGoalKind::CoinductiveTrait`, stepping into `GoalSource::ImplWhereBound` classifies the edge as `PathKind::Coinductive` (introduced in `rust-lang/rust` PR #136824 and tested in `tests/ui/traits/next-solver/cycles/coinduction/only-one-coinductive-step-needed.rs`), and `search_graph.rs` assigns a coinductive cycle the initial provisional result `Certainty::Yes`.
3. **Contrast with ordinary traits and verification consequence:**
   - For non-auto traits (`trait OrdinaryMarker {} impl<T: OrdinaryMarker> OrdinaryMarker for Wrapper<T> {}` where `Wrapper<T>` aliases a self-referential cycle in `support/rust-gat-laws-and-selected-implementation-evidence-2026/ordinary_cycle_rejected.rs`), the cycle is inductive and `rustc 1.101.0-nightly` rejects it with `E0275` (`overflow evaluating the requirement`).
   - Upstream issue `rust-lang/rust#149743` and `google/zerocopy#3380` document the unresolved language question of whether `rustc` should reject non-productive explicit auto-trait self-cycles or whether recursive `unsafe impl`s carry a stronger guardedness obligation. Regardless of how `rustc` resolves that issue, a sound verifier **must not** model `unsafe impl Trait for T where P` as a simple logical implication $P \implies \text{SafeTrait}(T)$ when $P$ can be discharged coinductively through the same impl; recursive unsafe-trait proofs require an explicit well-founded or guarded fixed-point argument.

### 3. Generic Associated Type (GAT) Family Laws, Specialization Dispatch, and RefinedRust Inspection

`Basis: normative | documentation | source | execution | derived`

Combining the Rust Reference (`2dafab96d919d6ab2884488e970bf95610ff83eb`), `rustc-dev-guide` (`bfbca953b5d4a3596081360a1c79ad88f31e7d60`), compiler controls on `rustc 1.101.0-nightly` (`1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6` in `support/rust-gat-laws-and-selected-implementation-evidence-2026/execution.json`), and the RefinedRust 2026 frontend (`support/rust-gat-laws-and-selected-implementation-evidence-2026/trait-source-identities.json`) establishes how associated families and method selection must be represented:

1. **GATs as universally quantified type/contract families (`support/rust-gat-laws-and-selected-implementation-evidence-2026/generics.rs`, `support/rust-gat-laws-and-selected-implementation-evidence-2026/gat_dyn_rejected.rs`):**
   - A GAT declaration such as `trait Family { type Borrow<'a>: Deref<Target = [u8]> where Self: 'a; fn lend<'a>(&'a self) -> Self::Borrow<'a>; }` defines a family indexed by `'a`. A sound semantic dictionary for `T: Family` must supply the type interpretation $\text{Borrow}(T, 'a)$, its validity/lifetime-bound laws under $\text{Self}: 'a$, and the method specification quantified over all permitted `'a`—not merely a single normalized instance.
   - Under `src/items/traits.md`, traits with generic associated types are not `dyn`-compatible; attempting to form `&dyn NonObjectSafe` fails with `E0038` (`the trait 'NonObjectSafe' is not dyn compatible` because `type View<'a>` has generic parameters, verified in `gat_dyn_rejected.rs`).
2. **Default bodies, blanket impls, and `min_specialization` (`generics.rs`):**
   - In `generics.rs`, `trait SelectValue { fn selected(&self) -> u8 { 1 } }` has a blanket implementation `impl<T: Copy> SelectValue for T { default fn selected(&self) -> u8 { 2 } }` and a specialized implementation `impl SelectValue for u8 { fn selected(&self) -> u8 { 3 } }`. Calling `call_selected::<u8>(0)` and `call_selected::<u16>(0)` outputs `selected_u8=3 selected_u16=2`.
   - Consequently, a verifier cannot attach the trait default method's specification (`returns 1`) or the blanket default's specification (`returns 2`) to a generic call unless specialization resolution is final (`leaf_def.is_final()`).
3. **RefinedRust 2026 trait-frontend comparison (`support/rust-gat-laws-and-selected-implementation-evidence-2026/trait-source-identities.json`):**
   - `traits/resolution.rs:resolve_assoc_item` (lines 281–336, SHA-256 `9f28617a106079fd2432deae961448bf9c4acbe1fb3d1b29909c00e55d5b13a4`) inspects `rustc` specialization ancestors' `leaf_def`; when the leaf definition is not final and the trait reference remains specializable, it retains the unspecialized item and substitutions rather than prematurely normalizing to an overridable default body.
   - Radium `specs/traits.rs:make_semantic_decl` (lines 1029–1055, SHA-256 `12cf89c8eb78dfefcf785f3003737a0c1b4d8295c4ba1fb7ff2a460b0cf40014`) emits an optional user-defined semantic predicate quantified over refinement/type parameters and trait-level lifetimes. However, `traits/registry.rs:get_associated_type_use` (lines 146–167, SHA-256 `4fb5a6494ca4800b6944bfaa65b9eb46f99f62f2950e6451e952c1dc9168bf43`) and `specs/traits.rs:make_assoc_type_use` (lines 453–461) look up associated types by associated-item index without threading GAT-local lifetime/type arguments.

### 4. Safety-Boundary Completeness and `#![feature(unsafe_fields)]` (RFC 3458)

`Basis: normative | documentation | source | derived`

1. **Why syntactic `unsafe` blocks are not a complete invariant slice (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
   - The Rust Reference (`src/unsafety.md`) restricts `unsafe` syntax to raw-pointer dereferences, mutable/external statics, union field reads, `unsafe fn` calls, target-feature calls, `unsafe impl`, `unsafe extern`, and `unsafe` attributes.
   - Safe operations within a module can still mutate or invalidate state relied upon by internal `unsafe` code:
     - Ordinary place assignment (`src/expressions/operator-expr.md`) drops the old value and writes a new value without an `unsafe` block.
     - `core::cell::Cell::set` (`library/core/src/cell.rs`, blob `1c79cf6bfcb36c2a814155bce8f8ea32afb2c191`) mutates through `&self`, and `UnsafeCell::get(&self) -> *mut T` safely constructs a mutable raw pointer.
     - `core::mem::MaybeUninit::uninit()` and `MaybeUninit::write` (`library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d`) safely create and overwrite uninitialized/initialized storage before an unsafe `assume_init`.
     - `core::mem::forget` (`library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2`) safely suppresses a value's destructor, so unsafe abstractions can never assume callers will run `Drop` to restore safety invariants.
   - A complete abstraction proof must therefore audit the full module visibility boundary: invariant constructors, all safe and unsafe state-transition methods, and unsafe consumers.
2. **How `#![feature(unsafe_fields)]` narrows explicit field transitions (`rust-lang/rfcs@f5749baed7b7ecfe03d95dc9197d0c1344712f43`, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
   - **What becomes `unsafe`:** Constructing a struct/enum variant with any `unsafe` field (`ExprKind::Adt` in `compiler/rustc_mir_build/src/check_unsafety.rs`, blob `f99d8934aa7fa8944e2906c2719e1eb4356c3c09`), projecting an `unsafe` field (`ExprKind::Field` for reads, writes, moves, shared/mutable references, `&raw const`/`&raw mut`, and pattern bindings, verified in `tests/ui/unsafe-fields/unsafe-fields.{rs,stderr}`), and implementing `Copy` (`unsafe impl Copy` required by `coherence/unsafety.rs`, verified in `tests/ui/unsafe-fields/copy-trait.rs`).
   - **Auto-trait suppression:** Both the classic solver (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs`, blob `3b599db8ff1c20005aa95ed9928e78aeecfd7f53`) and next solver (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs`, blob `e09864295020f89899863236d38853505ed1f0ef`) disable automatic structural implementations of unsafe auto traits (`Send`, `Sync`) for types containing `unsafe` fields (`tests/ui/unsafe-fields/auto-traits.rs`).
   - **What remains safe or outside `unsafe_fields`:** Ignoring an unsafe field with `..` in destructuring patterns, computing `core::mem::offset_of!(Type, unsafe_field)`, projecting sibling safe fields, and **automatic `Drop` destruction** (if a temporarily relaxed field invariant would make `Drop` unsound, the field must be wrapped in `ManuallyDrop`). Furthermore, `unsafe` fields only express library invariants; they never permit violating the language-level bit-validity of the field's declared type `T`.

## Boundaries

- **Not examined:**
  - End-to-end GAT family translation and generated proof obligations inside RefinedRust or Aeneas (the inspection of RefinedRust `traits/registry.rs` and `specs/traits.rs` covered only the named associated-type lookup functions, not every frontend path).
  - Const-generic associated type families, higher-ranked `for<'a>` callback extraction, or dynamic-dispatch vtable verification in Lean.
  - Preservation of `#![feature(unsafe_fields)]` HIR/MIR metadata by Charon or Aeneas.
- **Unknown:**
  - The final upstream resolution of `rust-lang/rust#149743` (whether `rustc` will restrict coinductive `ImplWhereBound` steps to compiler-synthesized structural auto-trait impls or keep explicit `unsafe impl` self-cycles accepted) and `rust-lang/rust#132922` (whether `unsafe_fields` will forbid union fields as stated in RFC 3458).
- **Known not to apply:**
  - Compiler acceptance of an `unsafe impl` (including via auto-trait coinduction) does **not** prove the trait's semantic safety invariant.
  - Proving a GAT equality or method contract at one concrete lifetime does **not** establish the universally quantified GAT family contract.
  - Auditing only syntactic `unsafe { ... }` blocks does **not** suffice to verify an unsafe abstraction whose invariant-bearing state can be modified by safe methods, `Cell`/`UnsafeCell`, `MaybeUninit`, or `mem::forget`.
- **Unsupported:**
  - Under the Rust Reference dyn-compatibility rules (and verified with `E0038` in `support/rust-gat-laws-and-selected-implementation-evidence-2026/gat_dyn_rejected.rs`), traits with generic associated types cannot be used as `dyn Trait` trait objects.
  - Positional tuple-struct fields cannot be marked `unsafe` at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`compiler/rustc_parse/src/parser/item.rs`, blob `3f6429c6a60f0372cb44262a12218bd6a821c390`) due to syntactic ambiguity with `unsafe fn()`.

## Evidence

### Primary Upstream Sources

- **Rust Reference (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` and `2dafab96d919d6ab2884488e970bf95610ff83eb`):**
  - `src/unsafe-keyword.md` (blob `7658c1f5c5425d03e2183e89b55260e5e9fd889b`), `src/unsafety.md` (blob `7353bcc6004d74b9e8698c71c093b35eebe05a70`), `src/items/traits.md` (blob `fe1a985f5390b0b7edf15db28cd717ce44c3945b`), `src/items/associated-items.md` (lines 200–300), `src/items/implementations.md`, `src/special-types-and-traits.md`, `src/expressions/operator-expr.md` (blob `6c5e4ffbf1532597c3ffe9a800ca80e0fb3cec8a`).
- **Rust compiler and standard library (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, `f6c1107f8be13e48465e12c0fd26e6a39fe18e4f`):**
  - `library/core/src/marker.rs` (blob `53141aabacc453e3781bbe9593618e26c06ca732`), `library/alloc/src/rc.rs` (blob `523c9b8b1585846d448791b40d0b800f7286af0e`), `library/core/src/iter/traits/marker.rs` (blob `542d283fe95abab901534fd21e38bddaa6a28823`).
  - `library/core/src/mem/mod.rs` (blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2`), `library/core/src/cell.rs` (blob `1c79cf6bfcb36c2a814155bce8f8ea32afb2c191`), `library/core/src/mem/maybe_uninit.rs` (blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d`), `library/core/src/ptr/mod.rs` (blob `ff2c18d685b65832c296731f23f1664779b874f2`).
  - `compiler/rustc_hir_analysis/src/coherence/unsafety.rs` (blob `8114106a2a4117a1e8e1d706afff753ff834f263`).
  - `compiler/rustc_middle/src/ty/mod.rs` (blob `6df1ed82d260a5c95dbe9671f2c7ddf8585c36ab`) and `compiler/rustc_middle/src/ty/util.rs` (blob `99da2da391151fe1f67cbb0d48fdde32f0c982e9`).
  - `compiler/rustc_trait_selection/src/traits/select/{mod.rs,candidate_assembly.rs}` (blobs `eadc937639f209ceaebef0eaf59cf4b279d507e7` and `3b599db8ff1c20005aa95ed9928e78aeecfd7f53`).
  - `compiler/rustc_next_trait_solver/src/solve/{eval_ctxt/mod.rs,search_graph.rs,trait_goals.rs}` (blobs `54d306466cf5b1b5b8f32625606b469dcfa7d5a8`, `a46261fcf72716f5571a996da35fa0ffc6e4504f`, `e09864295020f89899863236d38853505ed1f0ef`).
  - `compiler/rustc_feature/src/unstable.rs` (blob `388482209cf9eb17a562735bae03b644db686368`), `compiler/rustc_parse/src/parser/item.rs` (blob `3f6429c6a60f0372cb44262a12218bd6a821c390`), `compiler/rustc_ast_lowering/src/item.rs` (blob `70f55d67c7a16e582eabdfd160db93d6b03f8c4d`), `compiler/rustc_mir_build/src/check_unsafety.rs` (blob `f99d8934aa7fa8944e2906c2719e1eb4356c3c09`).
  - Checked-in UI test fixtures at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: `tests/ui/traits/next-solver/cycles/coinduction/only-one-coinductive-step-needed.rs` (blob `e41f7d7f3ceb341d1f48aa4b591435aaccde4273`) and `tests/ui/unsafe-fields/{unsafe-fields.rs,unsafe-fields.stderr,unsafe-fields-crate.rs,copy-trait.rs,auto-traits.rs}` (blobs `cb86479bb20d36dd6db2ea4bdde6ab46f839d578`, `d0e2dc16a13d546baada6f6252181e1fced0fecf`, `cfb9ad6b544fde44efb7e6a555dd9f35eef2d937`, `fb09ed02e3ffee1231400e5ab191e284972d5407`, `e15d0000079ef16c85506900219c99f66f9ad815`).
- **RFC 3458 and `rustc-dev-guide`:**
  - `rust-lang/rfcs@f5749baed7b7ecfe03d95dc9197d0c1344712f43`: `text/3458-unsafe-fields.md` (blob `4d9bc5b975d54327ae41df16bbab8bdf729893c7`).
  - `rust-lang/rustc-dev-guide@bfbca953b5d4a3596081360a1c79ad88f31e7d60`: `src/solve/coinduction.md` and `src/traits/specialization.md`.

### Preserved Package Support Artifacts

- **GAT, coinduction, specialization, and RefinedRust artifacts (observed 2026-10-14):**
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/generics.rs`
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/gat_dyn_rejected.rs`
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/ordinary_cycle_rejected.rs`
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/execution.json`
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/source-identities.json`
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/trait-source-identities.json`
  - `support/rust-gat-laws-and-selected-implementation-evidence-2026/coverage.json`
- **Unsafe-trait contract matrix and source map (observed 2026-09-27):**
  - `support/rust-unsafe-trait-invariants/unsafe-trait-contract-matrix.json`
  - `support/rust-unsafe-trait-invariants/source-map.json`

## Revalidation

1. **Compiler and specification source checks:**
   - Diff `compiler/rustc_hir_analysis/src/coherence/unsafety.rs` for `E0199`/`E0200` and conditional `Copy` unsafety on ADTs with `unsafe` fields.
   - Diff `coinductive_match` in `compiler/rustc_trait_selection` and `CurrentGoalKind::CoinductiveTrait` / `consider_auto_trait_candidate` in `compiler/rustc_next_trait_solver` to check whether `GoalSource::ImplWhereBound` still produces `PathKind::Coinductive` for explicit user auto-trait impls (`rust-lang/rust#149743`).
   - Diff `compiler/rustc_mir_build/src/check_unsafety.rs` and `tests/ui/unsafe-fields/` to check whether `unsafe_fields` has stabilized or forbidden union fields.
2. **Executable compiler controls (`support/rust-gat-laws-and-selected-implementation-evidence-2026/`):**
   ```bash
   mkdir -p ./build/gat-controls
   rustc --edition=2024 -O support/rust-gat-laws-and-selected-implementation-evidence-2026/generics.rs \
     -o ./build/gat-controls/generics
   ./build/gat-controls/generics
   rustc --edition=2024 --crate-type=lib \
     support/rust-gat-laws-and-selected-implementation-evidence-2026/gat_dyn_rejected.rs
   rustc --edition=2024 --crate-type=lib \
     support/rust-gat-laws-and-selected-implementation-evidence-2026/ordinary_cycle_rejected.rs
   ```
   Confirm that `./build/gat-controls/generics` exits with status `0` and prints `lend=4 link=1 selected_u8=3 selected_u16=2`, that `gat_dyn_rejected.rs` fails with `E0038`, and that `ordinary_cycle_rejected.rs` fails with `E0275` (`support/rust-gat-laws-and-selected-implementation-evidence-2026/execution.json`).
