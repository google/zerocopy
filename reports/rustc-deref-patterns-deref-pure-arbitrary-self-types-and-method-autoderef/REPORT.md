# Rust `deref_patterns`, Arbitrary Self Types v2 (`Receiver` vs. `DispatchFromDyn`), and Method-Call Autoderef/Autoref Resolution

## Summary

This report establishes primary-source, empirical (`rustc` + `Miri`), and kernel-checked (`Lean v4.34.1`) ground truth for three tightly coupled Rust type-checking, pattern-lowering, and method-dispatch mechanisms in 2026 `rustc`:

1. **`deref_patterns` (`deref!(...)`) requires both `unsafe trait DerefPure` and `FakeBorrowKind::Deep` for decision-tree soundness.**
   In `rustc`'s backtracking match builder, every `deref!(...)` arm on a non-`Box` smart pointer allocates a fresh temporary and emits a separate `TerminatorKind::Call` to `<P as Deref>::deref` (or `DerefMut::deref_mut` when any subpattern contains a `ref mut` binding), while `rustc_pattern_analysis` treats `Constructor::DerefPattern` as exhaustive under the assumption that repeated dereferences yield the same target value. Because `CleanupPostBorrowck` strips `BorrowKind::Fake(Deep)` and `FakeRead` before `Runtime(PostCleanup)` MIR, post-cleanup MIR retains multiple `Deref::deref` calls followed by `TerminatorKind::Unreachable`. Direct execution under `rustc 1.98.0-nightly` confirms that a two-arm match over a custom `PureBool` emits exactly two `<PureBool as Deref>::deref` calls plus `unreachable;`, that a match guard mutating `*b` is blocked by `E0510` via `FakeBorrowKind::Deep`, and that an unsound `unsafe impl DerefPure` whose `deref` toggles a `Cell<bool>` triggers `Undefined Behavior: entering unreachable code` under `Miri`. The mechanized theorem `derefPure_decision_tree_sound` proves that relational `DerefPure` idempotence together with guard stability (`DeepFakeBorrowGuards`) prevents `unreachableUB` for all exhaustive arm lists, while two constructive counterexamples (`ce_impure_deref_breaks_exhaustiveness` and `ce_shallow_fake_borrow_guard_breaks_exhaustiveness`) prove that dropping either hypothesis independently breaks exhaustiveness.

2. **Arbitrary Self Types v2 decouples method receivers (`core::ops::Receiver`) from dereferencing (`Deref`), separates raw pointers (`arbitrary_self_types_pointers`), gates `dyn Trait` dispatch on pointer-ABI transparency (`DispatchFromDyn`), and enforces an asymmetric anti-shadowing check.**
   Under `#![feature(arbitrary_self_types)]`, method well-formedness walks `Autoderef::use_receiver_trait()` (`Receiver::Target`) instead of requiring `Deref` or `LegacyReceiver`, permitting custom non-`Deref` handles (such as FFI handles carrying extra metadata fields) as `self: Handle<Self>`. Raw-pointer receivers (`self: *const Self`, `self: *mut Self`) remain separately gated behind `#![feature(arbitrary_self_types_pointers)]` (`E0658`). However, `Receiver` alone never grants dyn compatibility: `receiver_is_dispatchable` checks `Receiver: DispatchFromDyn<Receiver[Self => U]>`, rejecting non-`DispatchFromDyn` handles with `E0038`, while coherence (`visit_implementation_of_dispatch_from_dyn`) rejects `DispatchFromDyn` with `E0378` on `#[repr(C)]`/`#[repr(packed)]` structs, structs with any non-1-ZST extra field, or 1-ZST fields mentioning type parameters. The mechanized proof pair (`dispatchFromDyn_vtable_call_sound` and `ce_non_layout_isomorphic_receiver_breaks_vtable_call`) proves that `DispatchFromDyn`'s structural rules are exact ABI-isomorphism conditions for wide-to-thin vtable metadata stripping (`2` words wide -> `1` word thin), and that adding even one extra non-ZST word (`NonDynHandle { ptr, tag }`) breaks the vtable shim ABI (`3` words wide, `2` words thin). During method lookup, `check_for_shadowed_autorefd_method` enforces an **asymmetric** `E0034` anti-shadowing rule (`candidate.receiver_steps > shadower.receiver_steps`): a smart pointer's inherent `self` (or `&self`) method cannot silently shadow a pointee's inherent `self: &Ptr<Self>` (or `self: &mut Ptr<Self>`) method (`E0034`), whereas a pointee's inherent `self: Ptr<Self>` method *does* silently shadow a smart pointer's inherent `&self` method (`0 > 1` is false).

3. **Method-call resolution follows a strict deterministic lexicographic order `(stepIndex, RefKind, CandKind)` over `Deref`-reachable, non-unsafe steps, trying all autoref adjustments at depth $d$ before dereferencing to depth $d+1$ or unsizing `[T; N]` to `[T]`.**
   `method_autoderef_steps` builds candidates along the `Receiver` chain (so inherent methods on pointees are assembled) while tagging each step with `reachable_via_deref` and `from_unsafe_deref`, and appends an `unsize: true` slice step only when `autoderef_via_deref.final_ty()` is an array `[T; N]`. `pick_all_method` filters out non-`Deref`-reachable and raw-pointer-dereferenced steps (`!from_unsafe_deref`, preventing implicit raw-pointer dereference with `E0599`) and searches each surviving step in the fixed sequence `ByVal` (skipped when `unsize`) -> `SharedRef` -> `MutRef` -> `ConstPtr` (`*mut T -> *const T`, skipped when `unsize`) -> `ReborrowPin`, always preferring `InherentImplPick` over extension traits at each `(step, RefKind)`. The mechanized theorem `methodProbe_first_step_wins` proves lexicographic optimality and safety-filter soundness across arbitrary step lists and candidate sets, and empirical probes confirm all 9 precedence relations identically under native `rustc`, Miri Stacked Borrows, and Miri Tree Borrows.

4. **Anneal's trusted MIR boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) currently fails closed on all constructs introduced by these three features.**
   `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` fail closed on non-empty place projections (including `ProjectionElem.deref`), `Rvalue::Cast` (including `PointerCoercion::Unsize` and `MutToConstPointer`), `Rvalue::CopyForDeref`, `StatementKind::FakeRead`, indirect/virtual `TerminatorKind::Call`, and retagging `Use(_, WithRetag::Yes)` on references/boxes. Extending a verified MIR semantics or middle-end optimizer to cover `deref_patterns` or arbitrary `dyn` receivers requires explicit treatment of `DerefPure` call-idempotence axioms (or post-lowering deref deduplication) and `DispatchFromDyn` ABI transparency.

---

## Applicability

This report covers four pinned, independently resolvable upstream subjects recorded in `REPORT.json`:

| Subject | Repository | Immutable Revision | Role in This Report |
| :--- | :--- | :--- | :--- |
| Upstream `rustc` & `core` source | `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main`) | Primary-source inspection of current compiler and `core::ops` implementation (`2026-11-22`). |
| Executed nightly `rustc` & `Miri` toolchain | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, LLVM `22.1.6`, `miri 0.1.0`) | Live native compilation, `--emit=mir` inspection, diagnostic capture, Miri Stacked Borrows & `-Zmiri-tree-borrows` execution, and line-by-line diff against `342d74463`. |
| Anneal trusted MIR semantics & capture driver | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main`) | Primary-source audit of `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` (which itself pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`). |
| Lean 4 proof kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel verification of `support/DerefPatternsAndArbitrarySelfSoundness.lean` (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`). |

### Relationship Among Subjects and Version Scope

- **Shared behavior across `rust-lang/rust` `14210df0e` (`1.98.0-nightly`) and `342d74463` (`main` HEAD):** Direct source diffing across all 18 examined files in `library/core/src/ops/`, `compiler/rustc_hir_analysis/`, `compiler/rustc_hir_typeck/`, `compiler/rustc_trait_selection/`, `compiler/rustc_mir_build/`, `compiler/rustc_pattern_analysis/`, and `compiler/rustc_mir_transform/` confirms that the core semantics of `check_pat_deref`, `deref_pat_target`, `PatKind::DerefPattern` exhaustiveness lowering, `FakeBorrowKind::Deep` collection, `TestKind::Deref` call emission, `check_method_receiver` / `receiver_is_valid`, `visit_implementation_of_dispatch_from_dyn`, `method_autoderef_steps`, `pick_all_method`, `check_for_shadowed_autorefd_method`, and `create_ty_adjustments_from_pick` are identical across both commits.
- **Concrete refinements between `14210df0e` and `342d74463`:** Three changes landed between the executed `1.98.0-nightly` commit and live `main` HEAD (detailed in Finding 6): (i) `#[rustc_dyn_incompatible_trait]` was added explicitly to `pub trait Receiver`, (ii) `CoerceUnsized<&'a mut U> for &'b mut T` gained `'b: 'a` lifetime covariance while `DispatchFromDyn<&'a mut U> for &'a mut T` stayed invariant, and (iii) `receiver_is_dispatchable` expanded its synthetic `param_env` to instantiate trait non-supertrait clauses and `Self`-bearing projection clauses for the synthetic unsized type parameter `U`.
- **Feature-gate and edition scope:** Empirical probes compile with `--edition=2024` on `x86_64-unknown-linux-gnu` using unstable nightly crate attributes `#![feature(deref_patterns)]`, `#![feature(deref_pure_trait)]`, `#![feature(arbitrary_self_types)]`, `#![feature(arbitrary_self_types_pointers)]`, `#![feature(coerce_unsized)]`, `#![feature(dispatch_from_dyn)]`, and `#![feature(unsize)]` as required per test case. Method autoderef/autoref ordering (Part C, excluding raw-pointer `self: *const Self` receivers) applies on stable Rust as well, because `pick_all_method`'s non-arbitrary-self path uses the exact same `Deref` step list and `ByVal -> SharedRef -> MutRef -> ConstPtr` sequence.
- **Formalization scope:** `support/DerefPatternsAndArbitrarySelfSoundness.lean` is a standalone pure-core Lean 4 formalization of the extracted decision-tree, method-probe, and vtable-ABI semantics. It does not import `joshlf/anneal`'s `Trusted.MirSemantics` because `Trusted.MirSemantics` at `c131b320e` intentionally rejects place dereference projections and indirect/vtable calls fail-closed (Finding 5).

---

## Findings

### 1. Deref Patterns (`deref!(...)`), `DerefPure`, and Deep Fake-Borrow Enforcement

#### 1.1 `DerefPure` Trait Contract and Type-Checking Gate
Basis: source + execution + documentation

In `library/core/src/ops/deref.rs` (lines 285–303 at both `342d74463` and `14210df0e`), `DerefPure` is defined as an `unsafe` marker trait (explicitly dyn-incompatible):

```rust
/// Perma-unstable marker trait. Indicates that the type has a well-behaved [`Deref`]
/// (and, if applicable, [`DerefMut`]) implementation. This is relied on for soundness
/// of deref patterns.
///
/// FIXME(deref_patterns): The precise semantics are undecided; the rough idea is that
/// successive calls to `deref`/`deref_mut` without intermediate mutation should be
/// idempotent, in the sense that they return the same value as far as pattern-matching
/// is concerned. Calls to `deref`/`deref_mut` must leave the pointer itself likewise
/// unchanged.
#[unstable(feature = "deref_pure_trait", issue = "87121")]
#[lang = "deref_pure"]
#[rustc_dyn_incompatible_trait]
pub unsafe trait DerefPure: PointeeSized {}

unsafe impl<T: ?Sized> DerefPure for &T {}
unsafe impl<T: ?Sized> DerefPure for &mut T {}
```

Standard-library `DerefPure` implementations verified in `rust-src` at `14210df0e` include `&T`, `&mut T` (`core/src/ops/deref.rs:300-303`), `Box<T, A>` (`alloc/src/boxed.rs`), `Rc<T, A>` and `UniqueRc<T, A>` (`alloc/src/rc.rs:2449,2453`), `Arc<T, A>` and `UniqueArc<T, A>` (`alloc/src/sync.rs:2452,4907`), `Vec<T, A>` (`alloc/src/vec/mod.rs:3808`), `String` (`alloc/src/string.rs:2841`), `ByteString` (`alloc/src/bstr.rs:85`), and a deliberately restricted set of `Cow` impls (`alloc/src/borrow.rs:357-368`): `Cow<'_, T>` for `T: Clone` (`Sized`), `Cow<'_, str>`, and `Cow<'_, [T]>` for `T: Clone`. Arbitrary unsized `Cow<'_, B>` is intentionally omitted because `<B::Owned as Borrow<B>>::borrow` is safe user code and therefore untrusted for idempotence.

During HIR type checking (`compiler/rustc_hir_typeck/src/pat.rs:2740-2791` at `342d74463`; lines 2702–2753 at `14210df0e`), an explicit `deref!(inner)` pattern executes `check_pat_deref`:

1. `deref_pat_target(span, expected)` unconditionally registers a `LangItem::DerefPure` trait bound on `expected`, then projects and normalizes `<expected as Deref>::Target` as the expected type of `inner`.
2. `check_pat(inner, target_ty, pat_info)` type-checks the inner pattern without mutating default binding mode through smart-pointer peeling (`check_deref_pattern`, lines 712–748, also enforces `tcx.recursion_limit()` against self-referential `T: Deref<Target = T>`).
3. `register_deref_mut_bounds_if_needed` inspects whether `inner` contains any `ref mut` binding (including binding modes inherited from outer `&mut` reference patterns); only if so does it register `LangItem::DerefMut` on `expected`.

Empirical verification (`support/probe_deref_patterns_and_arbitrary_self.py`, Part A):
- Matching `ImpureWrapper(u32)` (implements `Deref`, omits `DerefPure`) with `deref!(0) => 1` fails compilation with `E0277: the trait bound ImpureWrapper: DerefPure is not satisfied`.
- Matching across `Box<u32>`, `Rc<u32>`, `Arc<u32>`, `String`, `Vec<u32>`, `Cow<'_, str>`, and custom `PureWrap<u32>` (implementing `Deref`, `DerefMut`, and `unsafe impl DerefPure`, including `deref!(ref mut x)` mutation) compiles and runs identically across native `rustc`, Miri Stacked Borrows, and Miri Tree Borrows (`DEREF_PAT_OK=210 MUT_CUSTOM=45`).

#### 1.2 Pattern Exhaustiveness and Constructor Isolation
Basis: source + execution

In `compiler/rustc_pattern_analysis/src/rustc.rs` (lines 495–505 at `342d74463`, byte-for-byte identical at `14210df0e`), `PatKind::DerefPattern` lowers to a unary constructor `Constructor::DerefPattern(cx.reveal_opaque_ty(subpattern.ty))` of arity `1`:

```rust
PatKind::DerefPattern { subpattern, .. } => {
    // NB(deref_patterns): This assumes the deref pattern is matching on a trusted
    // `DerefPure` type. If the `Deref` impl isn't trusted, exhaustiveness must take
    // into account that multiple calls to deref may return different results. Hence
    // multiple deref! patterns cannot be exhaustive together unless each is exhaustive
    // by itself.
    fields = vec![self.lower_pat(subpattern).at_index(0)];
    arity = 1;
    ctor = DerefPattern(cx.reveal_opaque_ty(subpattern.ty));
    self.internal_state.has_lowered_deref_pat.set(true);
}
```

Two architectural invariants follow immediately from `rustc_pattern_analysis`:
- **Exhaustiveness trusts `DerefPure` as a pure function:** Two patterns `deref!(true)` and `deref!(false)` are treated as partitioning the unique sub-value of `Constructor::DerefPattern(bool)`, marking the match exhaustive without a wildcard arm.
- **No mixing of `DerefPattern` and ADT constructors:** `RustcPatCtxt::report_mixed_deref_pat_ctors` (`rustc.rs:1034-1047`) rejects any match column that mixes `deref!(...)` with a normal struct/enum constructor on the same smart pointer type. Empirical probe `mixed_deref_and_adt_ctors_rejected` confirms `rustc` rejects `match w { deref!(0) => 1, PureWrap(1) => 2, _ => 3 }` with `error: mix of deref patterns and normal constructors`.

#### 1.3 Backtracking MIR Decision-Tree Lowering and Repeated `Deref::deref` Calls
Basis: source + execution

In `compiler/rustc_mir_build/src/builder/matches/match_pair.rs` (lines 432–455 at `342d74463`; lines 311–342 at `14210df0e`), THIR `PatKind::DerefPattern` lowers along two distinct paths depending on `DerefPatBorrowMode`:

- **`DerefPatBorrowMode::Box` (built-in `Box<T>`):** Lowered as an **irrefutable** node using `place_builder.deref()` (`ProjectionElem::Deref`), emitting no trait call. Later, `compiler/rustc_mir_transform/src/deref_separator.rs` (`Derefer`, lines 23–81, `PassPolicy::Required`) hoists any non-leading `ProjectionElem::Deref` into a `LocalInfo::DerefTemp` assigned via `Rvalue::CopyForDeref` so subsequent MIR passes only ever observe `ProjectionElem::Deref` as the first projection element.
- **`DerefPatBorrowMode::Borrow(mutability)` (all other `DerefPure` types, e.g. `Rc`, `Arc`, `String`, `Vec`, `Cow`, custom `DerefPure`):** Lowered as a **refutable** `MatchPairKind::Testable` carrying `TestableCase::Deref { temp, mutability }`, allocating a **brand-new temporary `temp`** for each `deref!(...)` occurrence:

```rust
PatKind::DerefPattern {
    ref subpattern,
    borrow: DerefPatBorrowMode::Borrow(mutability),
} => {
    // Create a new temporary for each deref pattern.
    // FIXME(deref_patterns): dedup temporaries to avoid multiple `deref()` calls?
    let temp = cx.temp(
        Ty::new_ref(cx.tcx, cx.tcx.lifetimes.re_erased, subpattern.ty, mutability),
        pattern.span,
    );
    let subpat =
        InterPat::lower_thir_pat(cx, PlaceBuilder::from(temp).deref(), subpattern);
    InterPatKind::Refutable {
        place: unwrap_place(),
        testable_case: TestableCase::Deref { temp, mutability },
        subpats: vec![subpat],
    }
}
```

Two downstream sites amplify this design choice:
1. In `compiler/rustc_mir_build/src/builder/matches/buckets.rs` (lines 343–348 at `342d74463`; lines 336–341 at `14210df0e`), two `TestableCase::Deref` match pairs are merged into the same test bucket **only when `test_temp == temp`**. Because separate match arms receive distinct `Local` temporaries (`_2`, `_3`, ...), arms never share a `TestKind::Deref` node.
2. In `compiler/rustc_mir_build/src/builder/matches/test.rs` (lines 311–382), each `TestKind::Deref` emits `_ref = &place` (or `&mut place`) followed by `TerminatorKind::Call` to `<Ty as Deref>::deref` (or `DerefMut::deref_mut`) writing into `temp`. Because `match_candidates` (`matches/mod.rs:1665-1718`) compiles matches into a **backtracking automaton**, failing arm 1 jumps to the `otherwise` block and invokes `Deref::deref` a second time for arm 2, terminating the final exhausted `otherwise` block with `TerminatorKind::Unreachable`.

**Direct empirical MIR observation (`rustc 1.98.0-nightly --emit=mir`):** Compiling `classify_pure(w: PureBool) -> u32 { match w { deref!(true) => 10, deref!(false) => 20 } }` yields the exact post-cleanup MIR below (captured verbatim in `support/probe_results.json`):

```rust
fn classify_pure(_1: PureBool) -> u32 {
    debug w => _1;
    let mut _0: u32;
    let mut _2: &bool;
    let mut _3: &bool;
    let mut _4: &PureBool;
    let mut _5: &PureBool;

    bb0: {
        _4 = &_1;
        _2 = <PureBool as Deref>::deref(move _4) -> [return: bb2, unwind continue];
    }
    bb1: {
        _5 = &_1;
        _3 = <PureBool as Deref>::deref(move _5) -> [return: bb4, unwind continue];
    }
    bb2: { switchInt(copy (*_2)) -> [0: bb1, otherwise: bb6]; }
    bb3: { unreachable; }
    bb4: { switchInt(copy (*_3)) -> [0: bb5, otherwise: bb3]; }
    bb5: { _0 = const 20_u32; goto -> bb7; }
    bb6: { _0 = const 10_u32; goto -> bb7; }
    bb7: { return; }
}
```

This MIR dump directly proves three facts simultaneously: (1) two separate `<PureBool as Deref>::deref` calls occur on the false path (`bb0` -> `bb2` -> `bb1`), (2) `bb3` is an unconditional `unreachable;` whose reachability depends exclusively on `*(_2)` and `*(_3)` agreeing, and (3) zero `FakeBorrow` or `FakeRead` statements survive into post-cleanup MIR.

#### 1.4 Match-Guard Stability (`FakeBorrowKind::Deep`) and Post-Borrowck Erasure
Basis: source + execution

Even when `Deref` is genuinely pure (e.g. `Box<bool>`), a match guard between two `deref!(...)` arms could mutate the pointee unless borrowck forbids it. Ordinary pattern tests emit `FakeBorrowKind::Shallow` (`compiler/rustc_mir_build/src/builder/matches/util.rs:188`), which permits mutating behind pointers/boxes in guards when only outer structure was tested. For `TestableCase::Deref`, however, `FakeBorrowCollector::visit_match_pair` (`util.rs:171-185` at `342d74463`; lines 167–182 at `14210df0e`) upgrades the scrutinee borrow to **`FakeBorrowKind::Deep`**:

```rust
if matches!(testable_case, TestableCase::Deref { .. }) {
    // ... if we only shallowly fake-borrowed `match_pair.place`, this would allow:
    //   let mut b = Box::new(false);
    //   match b {
    //       deref!(true) => {} // not reached because `*b == false`
    //       _ if { *b = true; false } => {} // not reached because guard is `false`
    //       deref!(false) => {} // not reached because guard changed it -> UB!
    //   }
    // Hence we fake borrow using a deep borrow.
    self.fake_borrow(place, FakeBorrowKind::Deep);
}
```

`bind_and_guard_matched_candidate` (`matches/mod.rs:2432-2469`) emits `Rvalue::Ref(re_erased, BorrowKind::Fake(kind), place)` before evaluating the guard and `FakeRead(ForMatchGuard, temp)` after it. Then `CleanupPostBorrowck` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:34-38, 86-89`, `PassPolicy::Required`) replaces every `Assign(_, Rvalue::Ref(_, BorrowKind::Fake(_), _))` and `FakeRead` with `Nop` (and lowers `FalseEdge`/`FalseUnwind` to `Goto`), because fake borrows of inactive enum variants would be UB if executed at runtime.

Empirical verification confirms both halves of the soundness barrier:
- **Guard mutation blocked (`deep_fake_borrow_blocks_guard_mutation`):** Compiling the exact `Box<bool>` guard pattern above fails borrow checking with `E0510: cannot assign *b in match guard`.
- **Unsound `DerefPure` triggers immediate UB (`lying_deref_pure_triggers_miri_ub`):** Defining `struct LyingToggle(Cell<bool>)` whose `Deref::deref` flips the `Cell` on each call (returning `&false` then `&true`) with a deliberately unsound `unsafe impl DerefPure for LyingToggle {}` compiles cleanly under `rustc` and aborts under `Miri` with `error: Undefined Behavior: entering unreachable code` at the `match w` expression.

---

### 2. Arbitrary Self Types v2: `core::ops::Receiver`, Raw-Pointer Gate, Dyn-Compatibility Split, and Shadowing

#### 2.1 Decoupling `core::ops::Receiver` from `Deref` and `LegacyReceiver`
Basis: source + execution

In `library/core/src/ops/deref.rs` (lines 368–406 at `342d74463`; lines 367–405 at `14210df0e`), Arbitrary Self Types v2 separates method-receiver eligibility (`Receiver`) from value dereferencing (`Deref`):

```rust
#[lang = "receiver"]
#[unstable(feature = "arbitrary_self_types", issue = "44874")]
#[rustc_dyn_incompatible_trait] // added between 14210df0e and 342d74463
pub trait Receiver: PointeeSized {
    #[rustc_diagnostic_item = "receiver_target"]
    #[lang = "receiver_target"]
    #[unstable(feature = "arbitrary_self_types", issue = "44874")]
    type Target: ?Sized;
}

impl<P: ?Sized, T: ?Sized> Receiver for P
where
    P: Deref<Target = T>,
{
    type Target = T;
}

#[lang = "legacy_receiver"]
#[unstable(feature = "legacy_receiver_trait", issue = "none")]
#[doc(hidden)]
pub trait LegacyReceiver: PointeeSized {}
```

Crucial architectural properties:
- **Blanket compatibility:** Every `Deref<Target = T>` automatically implements `Receiver<Target = T>` via the blanket impl (`deref.rs:380-385`).
- **Non-`Deref` smart pointers:** Types that cannot soundlessly yield `&T` (e.g., C++/FFI handles, GC/arena handles, or raw-pointer wrappers that cannot uphold Rust's aliasing invariants for `&T`) can implement `Receiver<Target = T>` directly without implementing `Deref`.
- **Stable baseline (`LegacyReceiver`):** Without `#![feature(arbitrary_self_types)]`, only `&T`, `&mut T`, `Box<T, A>`, `Rc<T>`, `Arc<T>`, and `Pin<Ptr>` (where `Ptr: LegacyReceiver`) implement `LegacyReceiver` (`core/src/ops/deref.rs:403-406`, `core/src/pin.rs:1782`, `alloc/src/{boxed,rc,sync}.rs`).

#### 2.2 Well-Formedness Checking and the Two-Tier Feature Gate
Basis: source + execution

In `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`check_method_receiver` lines 1752–1889 and `receiver_is_valid` lines 1925–2021 at `342d74463`; lines 1800–2056 at `14210df0e`), `rustc` classifies method-receiver capability into three levels:

```rust
enum ArbitrarySelfTypesLevel {
    Basic,        // #![feature(arbitrary_self_types)]
    WithPointers, // #![feature(arbitrary_self_types_pointers)]
}
```

`receiver_is_valid` checks method receivers in exact order:
1. **Identity fast path (`wfcheck.rs:1939-1949`):** If `receiver_ty == self_ty`, succeeds immediately without requiring `Receiver`.
2. **Method generic parameter prohibition (`wfcheck.rs:1904-1914, 1951, 1974`):** Neither `receiver_ty` nor any intermediate step in the chain may be one of the method's own generic type parameters (`param.index >= method_generics.parent_count`).
3. **Chain selection (`wfcheck.rs:1953-1965`):** Constructs `Autoderef::new(...)` (`compiler/rustc_hir_analysis/src/autoderef.rs:33-250`):
   - If `arbitrary_self_types_enabled.is_some()`, calls `.use_receiver_trait()`, which switches `overloaded_deref_ty` (`autoderef.rs:146-150`) from `(Deref, Deref::Target)` to `(Receiver, Receiver::Target)` while still handling built-in `&T`/`&mut T` derefs first for MIR/const benefits (`autoderef.rs:83-96`).
   - Only if `arbitrary_self_types_enabled == Some(ArbitrarySelfTypesLevel::WithPointers)` does it also call `.include_raw_pointers()`, enabling `ty.builtin_deref(true)` to step through `*const T` / `*mut T`.
4. **Loop until unification with `self_ty` (`wfcheck.rs:1968-2017`):** Walks `autoderef.next()`, strips view types via `ignore_view`, and returns `Ok(())` upon unification with `self_ty`. When `arbitrary_self_types_enabled.is_none()`, every intermediate type must also satisfy `LegacyReceiver`.
5. **Diagnostic probing (`wfcheck.rs:1794-1845`):** If validation fails at the crate's active level, `check_method_receiver` speculatively re-runs `receiver_is_valid` at `Basic` and `WithPointers` to emit targeted `E0658` feature-gate diagnostics naming `arbitrary_self_types` or `arbitrary_self_types_pointers`.

Empirical verification (Part B):
- `struct Handle<T: ?Sized> { ptr: *const T, tag: u32 }` implementing `Receiver<Target = T>` without `Deref`, together with `self: *const Self` and `self: *mut Self` methods under `#![feature(arbitrary_self_types, arbitrary_self_types_pointers)]`, runs identically under native `rustc`, Miri Stacked Borrows, and Miri Tree Borrows (`HANDLE=31 RAW_PTR=40 RAW_MUT=27`).
- Removing `arbitrary_self_types_pointers` while keeping `#![feature(arbitrary_self_types)]` rejects `fn raw_self(self: *const Self)` with `E0658: *const S cannot be used as the type of self without the arbitrary_self_types_pointers feature`.

#### 2.3 The `Receiver` vs. `DispatchFromDyn` Dyn-Compatibility Split
Basis: source + execution + derived

Implementing `Receiver` (or even `Deref`) allows inherent and statically dispatched trait methods, **not** `dyn Trait` dynamic dispatch. Dyn compatibility (`compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs:695-838` at `342d74463`; lines 665–760 at `14210df0e`) invokes `receiver_is_dispatchable(tcx, method, receiver_ty)`:

1. Synthesizes a universally quantified unsized type parameter `U` (`Ty::new_param(tcx, u32::MAX, sym::RustaceansAreAwesome)`).
2. Substitutes `Self => U` in `receiver_ty` to obtain `unsized_receiver_ty = Receiver[Self => U]`.
3. Builds a `param_env` assuming `Self: Unsize<U>`, `U: Trait<...>`, `U: MetaSized`, plus (at `342d74463`) `Trait`'s instantiated non-supertrait trait clauses and `Self`-bearing projection clauses.
4. Requires `infcx.predicate_must_hold_modulo_regions` on:
   ```text
   Receiver : DispatchFromDyn<Receiver[Self => U]>
   ```
   Failure renders the trait non-dyn-compatible with **`E0038`**.

Why does `rustc` require `DispatchFromDyn` instead of merely `Receiver` or `CoerceUnsized`? The primary-source answer lives in `library/core/src/ops/unsize.rs:89-106` and `compiler/rustc_hir_analysis/src/coherence/builtin.rs:287-463` (`visit_implementation_of_dispatch_from_dyn`):

- Unlike `CoerceUnsized` (which converts `P<Concrete>` -> `P<dyn Trait>` at a known coercion site), `DispatchFromDyn` governs the **reverse, compiler-hardwired narrowing conversion** inside a vtable shim: receiving `P<dyn Trait>` (containing a wide pointer `(data_ptr, vtable_ptr)`) and passing `P<Concrete>` (containing a thin pointer `data_ptr`) to the concrete monomorphized method.
- `coherence/builtin.rs:322-329` explicitly documents the ABI invariant: *"Later parts of the compiler rely on all `DispatchFromDyn` types to be ABI-compatible with raw pointers... we ensure that for the cases where the type implements this trait, they **do** satisfy the `repr(transparent)` rules, and then we assume that everything else in the compiler (in particular, all the call ABI logic) will treat them as `repr(transparent)` even if they do not carry that attribute."*
- Accordingly, `visit_implementation_of_dispatch_from_dyn` enforces five strict structural constraints (`E0378` on violation):
  1. `source` and `target` are either same-region/same-mutability `&T -> &U`, same-mutability `*const/*mut`, same `Pat`, or the **same `struct` ADT** (`def_a == def_b`, lines 330–362).
  2. The struct must **not** carry `#[repr(C)]` or `#[repr(packed)]` (`DispatchFromDynRepr`, lines 364–366).
  3. Every non-coerced field must be either `PhantomData` or a 1-aligned ZST (`layout.is_1zst()`) that **does not mention any non-region type parameter** (`!ty_a.has_non_region_param()`, lines 374–411 — forbidding type-param ZST transmutation across unsizing).
  4. **Exactly one** field may vary between `source` and `target` (`coerced_fields.len() == 1`, rejecting 0 with `CoerceNoField` and $\ge 2$ with `CoerceMulti`, lines 419–459).
  5. That unique coerced field must recursively satisfy `ty_a: DispatchFromDyn<ty_b>` (lines 426–446).

Empirical verification (Part B):
- `trait DynAttempt { fn ping(self: NonDynHandle<Self>) -> u32; }` (where `NonDynHandle { ptr: *const T, tag: u32 }` implements `Receiver` without `DispatchFromDyn`) is rejected on `&dyn DynAttempt` with **`E0038`** (`because method ping's self parameter cannot be dispatched on`).
- Attempting `impl DispatchFromDyn` on `TwoField { ptr: *const T, extra: u32 }` fails coherence with **`E0378`** (`extra field extra of type u32 is not allowed`).
- Attempting `impl DispatchFromDyn` on `#[repr(C)] struct ReprCHandle<T: ?Sized>(*const T)` fails coherence with **`E0378`** (`structs implementing DispatchFromDyn may not have #[repr(packed)] or #[repr(C)]`).
- Positive control: `struct DynHandle<T: ?Sized> { ptr: *const T, _zst: PhantomData<u8> }` implementing `Receiver`, `CoerceUnsized`, and `DispatchFromDyn` dispatches `DynHandle<dyn DynOk>::ping()` cleanly under both native `rustc` and `Miri` (`DYN_HANDLE_OK=142`).

#### 2.4 Smart-Pointer vs. Target Method Shadowing Matrix and Anti-Shadowing Asymmetry
Basis: source + execution

A subtle and frequently misunderstood part of Arbitrary Self Types v2 is method shadowing between a smart pointer `SmartPtr<T>` (`receiver_steps = 0`) and its pointee `Inner` (`receiver_steps = 1`). Every inherent candidate recorded by `ProbeContext::assemble_inherent_impl_probe` (`compiler/rustc_hir_typeck/src/method/probe.rs:1004-1025`) tags `CandidateKind::InherentImplCandidate { impl_def_id, receiver_steps }`.

When `pick_all_method` (`probe.rs:1375-1430`) finds an `InherentImplPick` at `ByVal` (resp. `SharedRef`), it calls `check_for_shadowed_autorefd_method` (`probe.rs:1496-1581`) to search for a potentially shadowed inherent candidate at `SharedRef` and `MutRef` (resp. `MutRef`) matching `PickConstraintsForShadowed` (`probe.rs:190-215`):

```rust
fn may_shadow_based_on_autoderefs(&self, autoderefs: usize) -> bool {
    autoderefs == self.autoderefs
}
fn candidate_may_shadow(&self, candidate: &Candidate<'_>) -> bool {
    candidate.item.def_id != self.def_id
        && match candidate.kind {
            CandidateKind::InherentImplCandidate { receiver_steps, .. } => match self.receiver_steps {
                Some(shadowed_receiver_steps) => receiver_steps > shadowed_receiver_steps,
                _ => false
            },
            _ => false
        }
}
```

Crucially, note two consequences of this exact code:
1. **Only `ByVal -> {SharedRef, MutRef}` and `SharedRef -> MutRef` are checked.** `ConstPtr` (`*mut -> *const`) and `ReborrowPin` are explicitly excluded (`probe.rs:1431-1454`) because `<*mut T>::cast` legitimately shadows `<*const T>::cast`.
2. **The check is strictly asymmetric (`receiver_steps > shadowed_receiver_steps`) and applies only to `InherentImplPick` at equal `autoderefs`:** it protects pointee inherent methods from being broken when a smart pointer later adds a by-value or `&self` method, but it does **not** prevent a pointee's by-value `self: SmartPtr<Self>` method (`receiver_steps = 1`) from shadowing a smart pointer's `&self` method (`receiver_steps = 0`), because `0 > 1` is false!

All six cells of this shadowing matrix were empirically verified under both native `rustc 1.98.0-nightly` and `Miri`:

| Case | `SmartPtr<T>` impl (`receiver_steps = 0`) | `Inner` impl (`receiver_steps = 1`) | Trait Impl on `SmartPtr` | `p.method()` Outcome (`rustc` & `Miri`) | Governing Mechanism (`probe.rs`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 1. Deref depth-0 vs depth-1 | `impl SmartPtr<T> { fn tag(&self) -> 222 }` | `impl Inner { fn tag(&self) -> 111 }` | `Deref` | **OK -> `222`** (`SmartPtr` wins) | `autoderefs = 0` beats `autoderefs = 1`; `may_shadow_based_on_autoderefs` requires equal `autoderefs`. |
| 2. Inherent vs trait extension at same `&SmartPtr<Inner>` | `impl SmartPtr<T> { fn tag(&self) -> 222 }` | `impl ExtTag for Inner { fn tag(self: &SmartPtr<Self>) -> 111 }` | `Receiver` | **OK -> `222`** (`SmartPtr` inherent wins) | `pick_method` searches `inherent_candidates` strictly before `extension_candidates` (`probe.rs:1750-1764`). |
| 3. Same-ref-level inherent collision | `impl SmartPtr<T> { fn same_ref(&self) -> 222 }` | `impl Inner { fn same_ref(self: &SmartPtr<Self>) -> 111 }` | `Receiver` | **`E0034` ambiguity** | Two inherent candidates match the identical `(depth=0, SharedRef)` query `&SmartPtr<Inner>`. |
| 4. Anti-shadowing `ByVal` vs `SharedRef` | `impl SmartPtr<T> { fn collide(self) -> 222 }` | `impl Inner { fn collide(self: &SmartPtr<Self>) -> 111 }` | `Receiver` | **`E0034` ambiguity** | `check_for_shadowed_autorefd_method`: `1 > 0` triggers `MethodError::Ambiguity`. |
| 5. Anti-shadowing `SharedRef` vs `MutRef` | `impl SmartPtr<T> { fn collide_ref(&self) -> 222 }` | `impl Inner { fn collide_ref(self: &mut SmartPtr<Self>) -> 111 }` | `Receiver` | **`E0034` ambiguity** | `check_for_shadowed_autorefd_method`: `1 > 0` triggers `MethodError::Ambiguity`. |
| 6. **Asymmetry: Inner `ByVal` vs SmartPtr `SharedRef`** | `impl SmartPtr<T> { fn asym(&self) -> 222 }` | `impl Inner { fn asym(self: SmartPtr<Self>) -> 111 }` | `Receiver` | **OK -> `111`** (`Inner` silently shadows `SmartPtr`) | `Inner::asym` wins `ByVal` (`receiver_steps = 1`); anti-shadowing requires `candidate.receiver_steps > 1`, which `SmartPtr` (`0`) fails! |

---

### 3. Method-Call Autoderef, Autoref, Array-Unsizing, and Raw-Pointer Resolution Order

#### 3.1 Dual-Chain Step Assembly and Filtering (`method_autoderef_steps`)
Basis: source + execution

In `compiler/rustc_hir_typeck/src/method/probe.rs` (lines 706–821 at `342d74463`; lines 639–754 at `14210df0e`), `method_autoderef_steps` constructs the `steps: &[CandidateStep]` table for a receiver expression of type `self_ty`:

1. Always creates `autoderef_via_deref = Autoderef::new(..., self_ty).include_raw_pointers().silence_errors()`.
2. When `arbitrary_self_types` or `arbitrary_self_types_pointers` is enabled, also creates `autoderef_via_receiver = Autoderef::new(...).include_raw_pointers().use_receiver_trait().silence_errors()`, zips it against `autoderef_via_deref.map(|_| true).chain(repeat(false))`, and emits one `CandidateStep` per `Receiver` step tagged with:
   - `autoderefs: d` (step depth `0, 1, 2, ...`),
   - `reachable_via_deref: bool` (`true` for the prefix reachable through `Deref`, `false` for tail steps reachable *only* via `Receiver`),
   - `from_unsafe_deref: bool` (`false` up to and including the first raw pointer type `*const T`/`*mut T`, and `true` for every step *after* dereferencing through a raw pointer, lines 735–742),
   - `unsize: false`.
3. Inspects `final_ty = autoderef_via_deref.final_ty()` (`probe.rs:772-811`): **if and only if** `final_ty` is `ty::Array(elem_ty, _)`, appends **one trailing `CandidateStep`** with `self_ty = [elem_ty]`, `autoderefs = deref_steps_count - 1`, `from_unsafe_deref = reached_raw_pointer`, `unsize = true`, and `reachable_via_deref = true`.

Why are `reachable_via_deref = false` and `from_unsafe_deref = true` steps present in `self.steps` at all? Because `assemble_inherent_candidates` walks **all** steps in `self.steps` to collect inherent impl blocks on pointee types (e.g., finding `impl Target { fn foo(self: Handle<Self>) }` or `impl Target { fn bar(self: *const Self) }`), whereas `pick_all_method` (`probe.rs:1351-1362`) filters them **out** as callable receiver conversion targets:

```rust
self.steps
    .iter()
    .filter(|step| step.reachable_via_deref)
    .filter(|step| !step.self_ty.value.references_error() && !step.from_unsafe_deref)
    .find_map(|step| { ... })
```

#### 3.2 Exact Lexicographic Pick Order and Adjustment Lowering
Basis: source + execution

For each surviving eligible `step` in `self.steps` order (`Iterator::find_map`), `pick_all_method` (`probe.rs:1363-1479`) executes the following exact sequence and returns on the **first** non-`None` result:

1. **`ByVal`** (`pick_by_value_method`, lines 1589–1631): immediately returns `None` if `step.unsize` is `true` (arrays never unsize to slices by value). Otherwise calls `pick_method(self_ty)`. If `step.self_ty` is already a reference `&T`/`&mut T`, inserts an implicit reborrow (`autoderefs += 1`, `Autoref { mutbl }`) to avoid moving `&mut T`. Runs `check_for_shadowed_autorefd_method` against `Not` and `Mut` when the pick is an `InherentImplPick`.
2. **`SharedRef`** (`pick_autorefd_method(..., Mutability::Not)`, lines 1633–1668): calls `pick_method(&self_ty)`. Runs `check_for_shadowed_autorefd_method` against `Mut` when the pick is an `InherentImplPick`.
3. **`MutRef`** (`pick_autorefd_method(..., Mutability::Mut)`, lines 1454–1461): calls `pick_method(&mut self_ty)`.
4. **`ConstPtr`** (`pick_const_ptr_method`, lines 1713–1739): immediately returns `None` if `step.unsize` is `true` or `self_ty` is not `*mut T`. Otherwise calls `pick_method(*const T)` and records `AutorefOrPtrAdjustment::ToConstPtr` (coercing `*mut T` to `*const T` without dereferencing the pointer).
5. **`ReborrowPin`** (`pick_reborrow_pin_method`, lines 1672–1708): active only under `#![feature(pin_ergonomics)]` when `self_ty` is `Pin<&mut T>`; probes `Pin<&T>`.

Inside every call to `pick_method` (`probe.rs:1741-1765`), `self.inherent_candidates` is searched **strictly before** `self.extension_candidates`. Thus the total resolution priority is strictly lexicographic over:
$$\bigl(\text{stepIndex},\; \text{RefKind} \in [\text{ByVal} < \text{SharedRef} < \text{MutRef} < \text{ConstPtr} < \text{ReborrowPin}],\; \text{CandKind} \in [\text{Inherent} < \text{Extension}]\bigr)$$
subject only to the `E0034` anti-shadowing check above.

During confirmation (`compiler/rustc_hir_typeck/src/method/confirm.rs:201-292` at `342d74463`; lines 191–282 at `14210df0e`), `create_ty_adjustments_from_pick` replays `autoderef.nth(pick.autoderefs)` into `Adjust::Deref(Builtin | Overloaded)`, then appends:
- `Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::new(mutbl, AllowTwoPhase::Yes)))` (enabling two-phase borrows on mutable method receivers), followed by `Adjust::Pointer(PointerCoercion::Unsize)` when `unsize == true`; or
- `Adjust::Pointer(PointerCoercion::MutToConstPointer)` for `ToConstPtr`; or
- `Adjust::Deref(DerefAdjustKind::Pin)` + `Adjust::Borrow(AutoBorrow::Pin(mutbl))` for `ReborrowPin`.

#### 3.3 Empirical Verification of All 9 Precedence Edges and Raw-Pointer Isolation
Basis: execution

`support/probe_deref_patterns_and_arbitrary_self.py` (Part C) empirically executes all 9 discriminating precedence assertions under native `rustc`, Miri Stacked Borrows, and Miri Tree Borrows (all three yielding byte-identical stdout `PICK_VAL=10 D0R_VS_D1V=20 D0M_VS_D1R=30 INH_VS_EXT=40 ARR=50 SLICE=60 BOTH=70 CONST_PTR=85 REF_BEFORE_CONST=90`):

| Assertion | Competing Candidates | Observed Winner | Confirms |
| :--- | :--- | :--- | :--- |
| `PICK_VAL` | `ExtByVal::m_val(self)` on `Outer` | `10` | Depth-0 `ByVal` selected first. |
| `D0R_VS_D1V` | Trait `&Outer` (`depth=0, SharedRef, Ext`) vs. inherent `Inner` (`depth=1, ByVal, Inh`) | `20` (`&Outer`) | Depth-0 `SharedRef` trait beats Depth-1 `ByVal` inherent. |
| `D0M_VS_D1R` | Trait `&mut Outer` (`depth=0, MutRef, Ext`) vs. inherent `&Inner` (`depth=1, SharedRef, Inh`) | `30` (`&mut Outer`) | Depth-0 `MutRef` trait beats Depth-1 `SharedRef` inherent. |
| `INH_VS_EXT` | Inherent `&Outer` vs. trait `&Outer` at `(depth=0, SharedRef)` | `40` (inherent) | Inherent beats extension at equal `(stepIndex, RefKind)`. |
| `ARR` / `SLICE` / `BOTH` | `ArrWrap: Deref<Target = [u32; 4]>`: `&[u32; 4]` vs. unsized `&[u32]` | `50`, `60`, `70` (`[u32; 4]` wins `BOTH`) | Exact array step precedes trailing `unsize = true` slice step. |
| `CONST_PTR` | `pm: *mut RawItem` calling `RawItem::only_const(self: *const Self)` | `85` | `pick_const_ptr_method` coerces `*mut -> *const` without deref. |
| `REF_BEFORE_CONST` | Trait `&(*mut RawItem)` (`SharedRef`) vs. inherent `self: *const RawItem` (`ConstPtr`) | `90` (`&(*mut RawItem)`) | `SharedRef` (`rank 1`) strictly precedes `ConstPtr` (`rank 3`). |
| `raw_ptr_never_autoderefs` | `p: *const Target` calling `Target::by_ref(&self)` with both arbitrary-self features enabled | **`E0599`** | `from_unsafe_deref = true` step is never selected as a callable receiver. |

---

### 4. Mechanized `Lean v4.34.1` Soundness, Determinism, and Sharpness Theorems

Basis: derived (kernel-checked proofs in `support/DerefPatternsAndArbitrarySelfSoundness.lean`)

The accompanying 1,240-line pure-core Lean `v4.34.1` module (`support/DerefPatternsAndArbitrarySelfSoundness.lean`) mechanizes all three subsystems using total structural recursion only. Kernel verification under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` succeeds with exit code `0`, zero warnings, zero `sorry`/`sorryAx`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`/`Lean.ofReduceBool`, zero `partial def`, and zero `._unsafe_rec`.

| Theorem (`RustcDerefAndArbitrarySelf.*`) | Lines | Proven Property | Kernel Axioms (`#print axioms`) |
| :--- | :---: | :--- | :--- |
| `derefPure_decision_tree_sound` | L227–235 | `DerefPureRel Eqv derefOp ∧ DeepFakeBorrowGuards Eqv arms ∧ ExhaustiveArms arms → ∀ σ v, ∃ r σ', evalDecisionTree derefOp σ v arms = .matched r σ'`. | `[propext]` |
| `derefPure_decision_tree_no_ub` | L239–249 | Corollary: under the same hypotheses, `evalDecisionTree derefOp σ v arms ≠ .unreachableUB σ'`. | `[propext]` |
| `derefPure_unguarded_matches_single_deref` | L300–308 | For unguarded arms under `DerefPureRel`, multi-call backtracking produces the identical matched arm result as a single cached `Deref::deref` call (`evalSingleDeref`). | `[propext, Quot.sound]` |
| `ce_impure_deref_breaks_exhaustiveness` | L326–334 | **Sharpness CE:** `boolDerefArms` is exhaustive and unguarded, yet stateful `toggleDeref` drives `evalDecisionTree` to `.unreachableUB false`. | *(none)* `[]` |
| `ce_shallow_fake_borrow_guard_breaks_exhaustiveness` | L359–367 | **Sharpness CE:** `pureBoxDeref` satisfies `DerefPureRel Eq` and `mutatingGuardArms` is exhaustive, yet a guard mutating the pointee drives `evalDecisionTree` to `.unreachableUB true`. | *(none)* `[]` |
| `methodProbe_first_step_wins` | L917–943 | Whenever `probePick steps cands ast = .picked p`, `p.step` is eligible (`reachableViaDeref = true`, `fromUnsafeDeref = false`) and `ProbePriorityLe p.stepIdx p.refKind p.cand.kind j rk c.kind` holds against every matching candidate `c` on every eligible step `j`. | `[propext, Quot.sound]` |
| `methodProbe_never_picks_non_deref_step` | L947–952 | No pick ever originates from a `Receiver`-only (`reachableViaDeref = false`) step. | `[propext, Quot.sound]` |
| `methodProbe_never_picks_unsafe_raw_deref` | L956–961 | No pick ever dereferences through a raw pointer (`fromUnsafeDeref = true`). | `[propext, Quot.sound]` |
| `methodProbe_unsized_step_never_by_value` | L965–977 | An `unsize = true` array-to-slice step never matches `byVal` or `constPtr`. | `[propext, Quot.sound]` |
| `ce_depth0_autoref_beats_depth1_by_val` | L983–989 | **Sharpness CE:** `(stepIdx=0, sharedRef, extension)` beats `(stepIdx=1, byVal, inherent)`. | `[propext]` |
| `ce_array_exact_beats_unsized_slice` | L992–998 | **Sharpness CE:** exact `[T; N]` beats trailing `unsize = true` `[T]` step. | `[propext]` |
| `ce_shadowing_asymmetry_and_anti_shadowing` | L1010–1021 | **Sharpness CE:** witnesses both `E0034` anti-shadowing rejections (`Ptr byVal` vs `Inner sharedRef`, `Ptr sharedRef` vs `Inner mutRef`) AND the asymmetry (`Inner byVal` silently beats `Ptr sharedRef`). | `[propext]` |
| `dispatchFromDyn_vtable_call_sound` | L1178–1193 | `SatisfiesDispatchFromDyn L → abiWordCount true L = 2 ∧ abiWordCount false L = 1 ∧ ∀ d v t, vtableShimNarrow (encodeReceiver L [d, v] t) = some (encodeReceiver L [d] t)`. | `[propext]` |
| `ce_non_layout_isomorphic_receiver_breaks_vtable_call` | L1207–1217 | **Sharpness CE:** `nonDynHandleLayout` (`{ ptr, tag }`) fails `SatisfiesDispatchFromDyn`, has word widths `3` (wide) and `2` (thin), fails `vtableShimNarrow` (`= none`), and `[4096] ≠ [4096, 42]`. | `[propext]` |
| `ce_repr_c_receiver_rejected_by_dispatch_from_dyn` | L1224–1228 | **Sharpness CE:** `#[repr(C)]` single-pointer wrapper fails `SatisfiesDispatchFromDyn`. | `[propext]` |
| `ce_zst_type_param_rejected_by_dispatch_from_dyn` | L1235–1238 | **Sharpness CE:** 1-ZST field mentioning a type parameter fails `SatisfiesDispatchFromDyn`. | `[propext]` |

Key modeling design choice: `DerefPureRel Eqv derefOp` is parameterized by an arbitrary reflexive-transitive store preorder `Eqv : S → S → Prop` rather than strict store equality `Eq`. This captures real-world benign interior state transitions (such as memoized metadata or reference-count telemetry that leave the dereferenced target invariant) while specializing directly to `Eq` for pure value containers like `Box<T>`.

---

### 5. Verified-Compiler and Anneal Trusted-Boundary Implications (`joshlf/anneal@c131b320e`)

Basis: source + derived

Direct inspection of `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs`) establishes the exact boundary between 2026 `rustc`'s lowering of these features and Anneal's current trusted semantics:

1. **Pinned capture toolchain:** `trusted/rustc-capture/src/driver.rs:25,45` enforces exact `rustc` version equality (`1.98.0-nightly (f8a08b688 2026-05-30)` — one day before our executed `14210df0e` toolchain) and currently runs only a clean analysis callback without lowering MIR obligations (`driver.rs:79,149`).
2. **Place dereference projections fail closed:** `Trusted/MirAst.lean:472-475` declares `ProjectionElem.deref`, `ProjectionElem.field`, and `ProjectionElem.unsupported` (mapping `Index`, `ConstantIndex`, `Subslice`, `Downcast`, `OpaqueCast`, `UnwrapUnsafeBinder`, and `PhantomDeref` to `.unsupported`), while `Trusted/MirSemantics.lean:953,962` (`evalOperandToSlot`) rejects **any** non-empty `place.projection` with `.error .unsupported`. Consequently, both `Box` deref patterns (`*_1`) and post-call `Borrow` deref patterns (`*_2` after `Deref::deref`) fail closed today.
3. **Coercions, `CopyForDeref`, and retags fail closed:** `Trusted/MirAst.lean:583-628` maps `Rvalue::Cast` (which carries `PointerCoercion::Unsize` for array-to-slice method adjustments and `DynHandle<Concrete> -> DynHandle<dyn Tr>`, as well as `MutToConstPointer` from `pick_const_ptr_method`), `Rvalue::CopyForDeref` (emitted by `Derefer` on nested deref projections), and retagging `Rvalue::Use(_, WithRetag::Yes)` on values containing references or boxes to `.unsupported`.
4. **Fake borrows and virtual calls fail closed:** `Trusted/MirAst.lean:654-662, 780-795` maps `StatementKind::FakeRead`, `TerminatorKind::FalseEdge`, `TerminatorKind::FalseUnwind`, and all indirect/virtual `TerminatorKind::Call`s (`InstanceDef::Virtual` for `dyn Trait` dispatch) to `.unsupported`.

**Five formal obligations for any future Anneal or verified-`rustc` extension admitting these features:**
1. **Capture post-`CleanupPostBorrowck` MIR, never pre-borrowck MIR:** Pre-borrowck MIR contains `BorrowKind::Fake(Deep)` over potentially inactive enum variants (which would be UB to execute operationally, `util.rs:59-70`).
2. **Account for `DerefPure` across repeated post-cleanup `Deref::deref` calls:** Because `CleanupPostBorrowck` erases `FakeBorrowKind::Deep` while `match_pair.rs:444` leaves multiple `<P as Deref>::deref` calls feeding a terminal `TerminatorKind::Unreachable`, a post-cleanup MIR verifier cannot discharge `TerminatorKind::Unreachable` unless it either (a) assumes a relational `DerefPureRel` axiom for trusted `DerefPure` callees (plus frame preservation across any intervening guards) or (b) proves a verified MIR pass that deduplicates `TestKind::Deref` calls to a single temporary prior to verification.
3. **Preserve `deinitMovedPlace` on `ByVal` arbitrary-self receivers:** Because `Trusted/MirSemantics.lean:949-976` conservatively sets `deinitMovedPlace = true` (deinitializing moved non-ZST locals on `Operand.move`), calling a by-value `self: Handle<Self>` method moves and invalidates the caller's `Handle` local immediately at the `Call` operand evaluation boundary, whereas `self: &Handle<Self>` or `self: *const Self` (a `Copy` scalar) leaves the caller slot initialized.
4. **Verify `DispatchFromDyn` ABI transparency at the MIR-to-ABI/vtable boundary:** Any verified backend lowering `InstanceDef::Virtual` calls for arbitrary `Receiver` types must carry the `SatisfiesDispatchFromDyn` structural invariant (`reprRust`, unique coerced pointer field, only `PhantomData` / type-param-free 1-ZST siblings) to justify passing the stripped data pointer directly into the concrete callee's receiver register.
5. **Respect two-phase borrow semantics on method autoref adjustments:** `confirm.rs:230` lowers every `&mut self` method adjustment with `AllowTwoPhase::Yes`, so verifying mutable method calls in a memory model with aliasing (Tree Borrows / Stacked Borrows) must model reservation vs. activation rather than eager exclusive retagging.

---

### 6. Revision Comparison Across Examined `rust-lang/rust` Commits (`14210df0e` vs. `342d74463`)

Basis: source

Direct programmatic diffing between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`) and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main`, `2026-11-22`) identified exact continuity and three specific upstream deltas:

| Subsystem & File | `14210df0e` (`1.98.0-nightly`) | `342d74463` (`main` HEAD) | Behavioral Delta? |
| :--- | :--- | :--- | :--- |
| `library/core/src/ops/deref.rs` (`Deref`, `DerefPure`, `Receiver`, `LegacyReceiver`) | `Receiver` lacks explicit `#[rustc_dyn_incompatible_trait]` attribute (still dyn-incompatible via assoc type / compiler rules). | Adds explicit `#[rustc_dyn_incompatible_trait]` on `pub trait Receiver` (L370). | Diagnostic/attribute tightening only; `DerefPure` and blanket `Receiver` impl unchanged. |
| `library/core/src/ops/unsize.rs` (`CoerceUnsized`, `DispatchFromDyn`) | `CoerceUnsized<&'a mut U> for &'a mut T` (single lifetime `'a`). | `CoerceUnsized<&'a mut U> for &'b mut T` with `'b: 'a` (L42–45). `DispatchFromDyn` unchanged. | Allows lifetime shortening during `&mut` unsizing coercion; `DispatchFromDyn` stays invariant `'a`. |
| `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs` (`receiver_is_dispatchable`) | Synthetic `param_env` adds `method` predicates + `Self: Unsize<U>` + `U: Trait` + `U: MetaSized`. | Also instantiates `Trait`'s non-supertrait trait clauses (`#161621`) and `Self`-bearing projection clauses (`#163550`) for `U` (L758–812). | Fixes false-negative `E0038` on traits with auxiliary `where` clauses or `Self` in projection args; `DispatchFromDyn` gate itself unchanged. |
| `compiler/rustc_hir_typeck/src/pat.rs` (`check_pat_deref`, `deref_pat_target`) | Registers `DerefPure`, normalizes `<Self as Deref>::Target`, conditionally registers `DerefMut`. | Same logic; API refactor (`Ty::new_projection` takes `ty::IsRigid::No`, `deeply_resolve_ignoring_regions_with_obligations`). | None. |
| `compiler/rustc_pattern_analysis/src/rustc.rs` (`PatKind::DerefPattern`) | Lowers to unary `Constructor::DerefPattern` trusting `DerefPure`. | Byte-for-byte identical (0 diff lines in L478–518). | None. |
| `compiler/rustc_mir_build/src/builder/matches/{match_pair,test,util,buckets}.rs` | `Box` irrefutable deref; non-`Box` allocates fresh `temp` per arm -> `TestKind::Deref` `Call`; `FakeBorrowKind::Deep`. | Same semantics; `MatchPairTree` refactored into `MatchPairKind::{Or, Testable}`. | None. |
| `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`check_method_receiver`, `receiver_is_valid`) | `ArbitrarySelfTypesLevel::{Basic, WithPointers}`, `use_receiver_trait`, `include_raw_pointers`, `LegacyReceiver`. | Same semantics; `LangItem::NonNull` check replaces diagnostic-name lookup; `.emit()` -> `.emit_err()`. | None. |
| `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`visit_implementation_of_dispatch_from_dyn`) | Enforces same struct, non-`repr(C)`/non-`repr(packed)`, unique coerced field, `PhantomData` / type-param-free 1-ZSTs, recursive `DispatchFromDyn`. | Same rules (L287–463). | None. |
| `compiler/rustc_hir_typeck/src/method/probe.rs` (`method_autoderef_steps`, `pick_all_method`, `check_for_shadowed_autorefd_method`) | Dual `Deref`/`Receiver` step chains, `from_unsafe_deref`, trailing array `unsize`, `ByVal -> SharedRef -> MutRef -> ConstPtr -> ReborrowPin`, asymmetric anti-shadowing. | Semantically identical across L706–821 and L1346–1765. | None. |

---

## Boundaries

### Explicitly Out-of-Scope and Negative-Space Classification

- **`not examined` — Unchecked nightly execution on `342d74463` (`2026-11-22`):** While `342d74463` was inspected at the source level and diffed function-by-function against `14210df0e`, live `rustc` and `Miri` execution in `support/probe_results.json` ran on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)`. Execution on a binary built from `342d74463` was not performed; continuity is supported by the zero-behavioral-diff source audit of the exercised code paths (Finding 6).
- **`not examined` — `pin_ergonomics` (`Pin<&mut T>` -> `Pin<&T>`) and implicit deref patterns (`deref_patterns` sugar without `deref!(...)`):** `pick_reborrow_pin_method` (`probe.rs:1672-1708`) and `PatKind::Deref { pin: Pinnedness::Pinned, .. }` (`match_pair.rs:417-430`) are included in the source audit and Lean `RefKind.reborrowPin` rank ordering, but no runtime `rustc`/`Miri` probe was executed for `#![feature(pin_ergonomics)]` or implicit string/slice deref patterns without explicit `deref!(...)`.
- **`not examined` — Next-generation trait solver (`-Znext-solver=globally`) and negative-impl interactions:** All empirical probes used `rustc 1.98.0-nightly`'s default trait solver. Subtle differences in `Autoderef::overloaded_deref_ty` normalization (`predicate_may_hold_opaque_types_jank`) or `receiver_is_dispatchable` under `-Znext-solver=globally` were not empirically tested.
- **`not examined` — Non-x86_64 calling-convention ABI lowering for `DispatchFromDyn`:** The Lean formalization models receiver ABI layout at the abstract machine-word level (`1` word thin, `2` words wide) matching `coherence/builtin.rs:322-329`'s `repr(transparent)` contract; target-specific register assignment (e.g., SysV64 `ScalarPair` vs. Win64 indirect-by-pointer passing for 16-byte wide pointers) was not examined.
- **`unknown` — Final normative specification of `DerefPure`:** As documented verbatim in `library/core/src/ops/deref.rs:289-293` (`FIXME(deref_patterns): The precise semantics are undecided`), upstream Rust has not yet finalized whether `DerefPure` prohibits all interior side effects, allows idempotent memoization/reference-counting, or specifies exact pointer-provenance stability under Tree Borrows. Our Lean `DerefPureRel Eqv` formalizes the relational idempotence condition sufficient for decision-tree exhaustiveness, without claiming it equals whatever final normative specification Rust eventually stabilizes.
- **`known not to apply` — Anti-shadowing `E0034` on `*mut T` vs `*const T`, `ReborrowPin`, extension traits, or cross-`autoderefs` calls:** By direct source inspection (`probe.rs:1385, 1415, 1431-1454, 1523-1533`) and empirical verification (Finding 2.4), `check_for_shadowed_autorefd_method` does **not** apply to extension-trait picks, does **not** apply to `ConstPtr` or `ReborrowPin`, does **not** apply when `SmartPtr` and `Inner` are at different `autoderefs` depths (`Deref` depth 0 vs. depth 1), and does **not** prevent a pointee inherent `ByVal` method (`receiver_steps = 1`) from shadowing a smart pointer inherent `SharedRef` method (`receiver_steps = 0`).
- **`known not to apply` — `DerefPure` deduplication across separate match arms:** On both `14210df0e` and `342d74463`, `rustc` does **not** deduplicate `<P as Deref>::deref` calls across distinct `deref!(...)` arms (`match_pair.rs:442-444` `FIXME`). Any assumption that `match x { deref!(a) => ..., deref!(b) => ... }` invokes `Deref::deref` at most once is false.
- **`unsupported` — Arbitrary non-`DispatchFromDyn` receivers in `dyn Trait` and `NonNull`/`Weak` as receivers without `Receiver`:** `rustc` explicitly rejects `dyn Trait` methods whose receiver lacks `DispatchFromDyn` (`E0038`) and rejects custom structs with `#[repr(C)]`, `#[repr(packed)]`, extra non-ZST fields, or type-parameter ZST fields from implementing `DispatchFromDyn` (`E0378`). Likewise, `joshlf/anneal@c131b320e` explicitly rejects place dereferences, pointer coercions, `FakeRead`, and virtual calls fail-closed.

### Attractive Stronger Conclusions Not Established

1. **Passing `DerefPure` type checking does NOT guarantee runtime soundness for custom `unsafe impl DerefPure` types:** `DerefPure` is an unchecked `unsafe` marker trait; as `lying_deref_pure_triggers_miri_ub` proves, an unsound `unsafe impl DerefPure` compiles cleanly and triggers `unreachable` UB at runtime.
2. **Implementing `CoerceUnsized` does NOT imply `DispatchFromDyn`:** `CoerceUnsized` allows multi-field structs (as long as only one field varies) and `#[repr(C)]` wrappers (such as `struct WithTag<T: ?Sized> { tag: u32, ptr: *const T }`), which can be unsized to `WithTag<dyn Tr>` yet are rejected by `visit_implementation_of_dispatch_from_dyn` (`E0378`) because vtable dispatch requires single-pointer ABI transparency.
3. **Our Lean 4 formalization proves invariants of a faithful extracted model, NOT machine-checked compiler extraction from `rustc`'s Rust source:** The Lean proofs establish mathematical soundness and sharpness of `rustc`'s documented algorithms (`evalDecisionTree`, `probePick`, `SatisfiesDispatchFromDyn`) rather than proving that `rustc`'s compiled binary refines those Lean functions.

---

## Evidence

### 1. Primary-Source Git Coordinates (Pinned 40-Hex Commits)

All repository commit SHAs were resolved live via GitHub API on `2026-11-22`:

- **`rust-lang/rust` (`main` HEAD): `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`**
  - `library/core/src/ops/deref.rs` — `Deref` (L139–151), `DerefMut` (L270–275), `DerefPure` (L285–303), `Receiver` + blanket `Deref` impl (L368–385), `LegacyReceiver` (L395–406).
  - `library/core/src/ops/unsize.rs` — `CoerceUnsized` (L36–72), `DispatchFromDyn` contract & primitive impls (L74–137).
  - `compiler/rustc_hir_typeck/src/pat.rs` — `check_deref_pattern` (L712–748), `calc_adjust_mode` (L753–813), `check_pat_deref` / `deref_pat_target` / `register_deref_mut_bounds_if_needed` (L2740–2791).
  - `compiler/rustc_pattern_analysis/src/rustc.rs` — `PatKind::DerefPattern` (L495–505), `report_mixed_deref_pat_ctors` (L1034–1047).
  - `compiler/rustc_mir_build/src/builder/matches/match_pair.rs` — `DerefPatBorrowMode::Box` (L432–436), `DerefPatBorrowMode::Borrow` with per-arm `cx.temp` (L438–455).
  - `compiler/rustc_mir_build/src/builder/matches/test.rs` — `TestKind::Deref` (L311–315), `call_deref` (L335–382).
  - `compiler/rustc_mir_build/src/builder/matches/buckets.rs` — `TestKind::Deref` temp-equality bucketing (L343–348).
  - `compiler/rustc_mir_build/src/builder/matches/util.rs` — `collect_fake_borrows` (L71–101), `FakeBorrowCollector::visit_match_pair` upgrading `TestableCase::Deref` to `FakeBorrowKind::Deep` (L170–195).
  - `compiler/rustc_mir_build/src/builder/matches/mod.rs` — backtracking automaton `match_candidates` (L1665–1758), `bind_and_guard_matched_candidate` emitting `BorrowKind::Fake` and `FakeRead` (L2387–2471).
  - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs` — `CleanupPostBorrowck` erasing `BorrowKind::Fake`, `FakeRead`, `FalseEdge`, `FalseUnwind` (L24–90).
  - `compiler/rustc_mir_transform/src/deref_separator.rs` — `Derefer` hoisting non-leading `ProjectionElem::Deref` to `LocalInfo::DerefTemp` / `Rvalue::CopyForDeref` (L23–109).
  - `compiler/rustc_hir_analysis/src/autoderef.rs` — `Autoderef`, `overloaded_deref_ty`, `include_raw_pointers`, `use_receiver_trait` (L33–245).
  - `compiler/rustc_hir_analysis/src/check/wfcheck.rs` — `ArbitrarySelfTypesLevel`, `check_method_receiver` (L1745–1889), `confirm_type_is_not_a_method_generic_param` (L1904–1914), `receiver_is_valid` (L1925–2021).
  - `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs` — `receiver_is_dispatchable` (`Receiver: DispatchFromDyn<Receiver[Self => U]>`, L695–838).
  - `compiler/rustc_hir_analysis/src/coherence/builtin.rs` — `visit_implementation_of_dispatch_from_dyn` (L287–463).
  - `compiler/rustc_hir_typeck/src/method/probe.rs` — `PickConstraintsForShadowed` (L190–215), `method_autoderef_steps` (L706–821), `pick_all_method` (L1346–1479), `check_for_shadowed_autorefd_method` (L1496–1581), `pick_by_value_method` / `pick_autorefd_method` / `pick_reborrow_pin_method` / `pick_const_ptr_method` / `pick_method` (L1589–1765).
  - `compiler/rustc_hir_typeck/src/method/confirm.rs` — `create_ty_adjustments_from_pick` (L201–292).
- **`rust-lang/rust` (executed toolchain): `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `LLVM 22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`)
  - All 18 files above downloaded and programmatically diffed against `342d74463`; stdlib `DerefPure` / `LegacyReceiver` / `DispatchFromDyn` impls verified in bundled `rust-src` (`library/alloc/src/{boxed,rc,sync,vec/mod,string,bstr,borrow}.rs`, `library/core/src/{pin,ops/deref,ops/unsize}.rs`).
- **`joshlf/anneal` (`main` HEAD): `c131b320eeeb26ef692e5afd5ec8db49ee518613`**
  - `trusted/rustc-capture/src/driver.rs` (L25, L45, L75–85, L148–150) — pinned `1.98.0-nightly (f8a08b688 2026-05-30)` analysis-only callback.
  - `trusted/lean/Trusted/MirAst.lean` (L472–475 `ProjectionElem`, L577–628 `Rvalue`, L654–662 `StatementKind`, L780–795 `TerminatorKind`).
  - `trusted/lean/Trusted/MirSemantics.lean` (L949–976 `evalOperandToSlot` failing closed on non-empty projections and applying `deinitMovedPlace = true`).
- **`leanprover/lean4` (`v4.34.1`): `5045d0056413266e57c625dcd7c365b10e377c52`**
  - Verified live via `lean --version`: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

### 2. Preserved Package Support Artifacts and Integrity Hashes

All scripts, machine-captured probe outputs, and kernel-checked proofs are preserved inside `support/`:

| File | Lines | Bytes | SHA-256 | Purpose |
| :--- | ---: | ---: | :--- | :--- |
| `support/probe_deref_patterns_and_arbitrary_self.py` | 959 | 32,927 | `8d31dd8d9d1e9a67ef182e93f1fa44a8191eb95033cbf94b9dac72081214dfdd` | Self-contained `rustc` + `Miri` (Stacked Borrows & Tree Borrows) + `--emit=mir` probe runner executing all 19 checks across Parts A, B, and C. |
| `support/probe_results.json` | 193 | 15,718 | `dfc5db6ad37465dfef62cc92da4951accfd25e7850885ce916fd4b537f113298` | Exact JSON transcript captured on `2026-11-22T09:39:41Z` (`all_checks_passed: true`, `19/19` checks passing, exit code `0`). |
| `support/DerefPatternsAndArbitrarySelfSoundness.lean` | 1,240 | 56,543 | `679fbd8ad7a26354fb3397da01d838576e676cd65b3bfe0364c45aa90c852e6a` | Pure-core `Lean v4.34.1` formalization containing all 16 public theorems and constructive counterexamples. |

### 3. Execution Receipts (Captured `2026-11-22`)

#### 3.1 `rustc` + `Miri` Empirical Probe Suite (`19 / 19` checks passed, exit code `0`)

Command executed:
```bash
python3 support/probe_deref_patterns_and_arbitrary_self.py --out support/probe_results.json
```

Observed results (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`):
- `part_a_impure_rejected_E0277`: `true` (`rc = 1`, `error[E0277]: the trait bound ImpureWrapper: DerefPure is not satisfied`).
- `part_a_std_custom_native_miri_agree`: `true` (native, Miri Stacked Borrows, and Miri `-Zmiri-tree-borrows` all exit `0` with `DEREF_PAT_OK=210 MUT_CUSTOM=45`).
- `part_a_deep_fake_borrow_blocks_guard_E0510`: `true` (`rc = 1`, `error[E0510]: cannot assign *b in match guard`).
- `part_a_mixed_ctors_rejected`: `true` (`rc = 1`, `error: mix of deref patterns and normal constructors`).
- `part_a_mir_emits_two_derefs_and_unreachable_no_fake_borrow`: `true` (`deref_call_count_in_post_cleanup_mir = 2`, `has_unreachable_terminator = true`, `has_residual_fake_borrow_or_fake_read = false`).
- `part_a_lying_deref_pure_miri_catches_unreachable_ub`: `true` (`rc = 1`, `error: Undefined Behavior: entering unreachable code`).
- `part_b_non_deref_receiver_native_miri_agree`: `true` (native, Miri SB, Miri TB all exit `0` with `HANDLE=31 RAW_PTR=40 RAW_MUT=27`).
- `part_b_raw_ptr_gate_E0658`: `true` (`rc = 1`, `error[E0658]: *const S cannot be used as the type of self without the arbitrary_self_types_pointers feature`).
- `part_b_dyn_compat_split_E0038`: `true` (`rc = 1`, `error[E0038]: the trait DynAttempt is not dyn compatible`).
- `part_b_dispatch_from_dyn_rejects_two_field_and_repr_c`: `true` (both fail with `E0378`).
- `part_b_dispatch_from_dyn_valid_custom_handle_native_miri_agree`: `true` (native & Miri both print `DYN_HANDLE_OK=142`).
- `part_b_shadowing_deref_depth0_wins_native_miri_agree`: `true` (`SHADOW_TAG=222 EXPLICIT_INNER=111`).
- `part_b_shadowing_inh_over_ext_native_miri_agree`: `true` (`INH_OVER_EXT_TAG=222 EXPLICIT_EXT=111`).
- `part_b_shadowing_asymmetry_inner_by_val_wins_native_miri_agree`: `true` (`ASYM_INNER_WINS=111`).
- `part_b_both_inh_same_ref_E0034`: `true` (`rc = 1`, `E0034`).
- `part_b_anti_shadowing_by_val_vs_by_ref_E0034`: `true` (`rc = 1`, `E0034`).
- `part_b_anti_shadowing_ref_vs_mut_ref_E0034`: `true` (`rc = 1`, `E0034`).
- `part_c_precedence_native_miri_agree`: `true` (native, Miri SB, Miri TB all exit `0` with `PICK_VAL=10 D0R_VS_D1V=20 D0M_VS_D1R=30 INH_VS_EXT=40 ARR=50 SLICE=60 BOTH=70 CONST_PTR=85 REF_BEFORE_CONST=90`).
- `part_c_raw_ptr_never_autoderefs_E0599`: `true` (`rc = 1`, `error[E0599]: no method named by_ref found for raw pointer *const Target`).

#### 3.2 `Lean v4.34.1` Kernel Verification and Axiom Audit (`exit code 0`)

Command executed:
```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/DerefPatternsAndArbitrarySelfSoundness.lean
```

Observed results:
- Exit code `0`, empty stdout/stderr (zero warnings, zero errors).
- `#print axioms` verified across all 16 public theorems: every theorem depends only on `[]`, `[propext]`, or `[propext, Quot.sound]`. Zero occurrences of `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or `_unsafe_rec`.

---

## Revalidation

To revalidate these findings against a newer `rustc` nightly, `Miri`, `joshlf/anneal`, or `Lean` release without repeating the full investigation, run these three narrow checks:

1. **Re-run the 19-check `rustc` + `Miri` probe suite** (takes ~10 seconds once a Miri sysroot is cached):
   ```bash
   python3 support/probe_deref_patterns_and_arbitrary_self.py --out /tmp/revalidate_probe.json
   ```
   - A failure in `part_a_mir_emits_two_derefs_and_unreachable_no_fake_borrow` or `part_a_lying_deref_pure_miri_catches_unreachable_ub` indicates that upstream resolved `FIXME(deref_patterns)` temporary deduplication in `match_pair.rs:443` (making `classify_pure` call `Deref::deref` once instead of twice) — inspect `match_pair.rs` and `buckets.rs` before concluding `DerefPure` is no longer required (multi-level nested/guarded patterns can still re-enter `deref`).
   - A failure in `part_b_shadowing_asymmetry_inner_by_val_wins_native_miri_agree` indicates upstream tightened `PickConstraintsForShadowed::candidate_may_shadow` (`probe.rs:208-210`) to become symmetric.
   - A failure in `part_a_impure_rejected_E0277`, `part_b_raw_ptr_gate_E0658`, or `part_b_dyn_compat_split_E0038` indicates a stabilization or feature-gate change in `pat.rs`, `wfcheck.rs`, or `dyn_compatibility.rs`.

2. **Re-check the upstream compiler seam files against a new `rust-lang/rust` commit:**
   Diff the following narrow regions against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
   - `library/core/src/ops/deref.rs` (`DerefPure`, `Receiver`, `LegacyReceiver`) and `library/core/src/ops/unsize.rs` (`DispatchFromDyn`);
   - `compiler/rustc_mir_build/src/builder/matches/{match_pair,test,util,buckets}.rs` (`DerefPatBorrowMode`, `TestKind::Deref`, `FakeBorrowKind::Deep`);
   - `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`check_method_receiver`, `receiver_is_valid`);
   - `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`visit_implementation_of_dispatch_from_dyn`);
   - `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs` (`receiver_is_dispatchable`);
   - `compiler/rustc_hir_typeck/src/method/probe.rs` (`method_autoderef_steps`, `pick_all_method`, `check_for_shadowed_autorefd_method`).

3. **Re-verify the `Lean` formalization and axiom boundary** (takes ~5 seconds):
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/DerefPatternsAndArbitrarySelfSoundness.lean
   ```
   Confirm exit code `0` and inspect `#print axioms` on `derefPure_decision_tree_sound`, `methodProbe_first_step_wins`, `dispatchFromDyn_vtable_call_sound`, and `ce_non_layout_isomorphic_receiver_breaks_vtable_call` to ensure no `Classical.choice`, `sorryAx`, or `Lean.ofReduceBool` enters the proof footprint under newer Lean toolchains.

4. **Re-check Anneal's fail-closed boundary** whenever `joshlf/anneal` updates `Trusted/MirAst.lean` or `Trusted/MirSemantics.lean`: inspect `evalOperandToSlot`, `Rvalue`, `StatementKind`, and `TerminatorKind` for newly admitted `.deref` projections, `PointerCoercion::Unsize`, or virtual calls, and verify that any admitted lowering discharges the five obligations in Finding 5.
