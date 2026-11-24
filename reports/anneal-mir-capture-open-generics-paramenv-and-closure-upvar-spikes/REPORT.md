# Anneal MIR Capture Feasibility: Open Generics (`ParamEnv`, `required_consts`) and Concrete Closure Upvars

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Two `rustc_private` empirical extraction spikes over `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked` under `-Zmir-preserve-ub`, never `optimized_mir`) on unmodified `google/zerocopy@2b88472905` and `library/core` establish bounded, low-TCB capture paths for both open generics and concrete closures:

1. **Open Generics & `ParamEnv` (`GO` for bounded `ParamEnv` + `ConstMirMachine`; `NO-GO` for full Charon-style trait-dictionary elaboration) `[real measurement]`:** Across all `9,349` unstolen bodies (`4,166` generic functions) in `zerocopy`, **zero (`0`)** hit specialization, GATs, nested projections, opaque types, `generic_const_exprs`, or virtual calls on type parameters (`T3 = 0`). Every unresolved trait call is discharged by a direct `ParamEnv` clause (`492` calls across `135` bodies) or a one-level alias item bound (`13` calls), and `tcx.param_env` is already fully elaborated (`0` supertrait clauses added).
2. **Generic `required_consts` (`ConstMirMachine`) `[real measurement]`:** `zerocopy` has `0` inline `const { ... }` blocks; its `static_assert!`/`const_assert!` macros expand to `40` `StaticAssert::ASSERT` blanket-impl const bodies (with `89` generic const bodies seeding a `106`-body transitive closure including `19` local `const fn`s). Monomorphic `const`/`AnonConst` bodies (`117` in `zerocopy`, `1,883` in `core`) are already stolen by analysis-time CTFE before `after_analysis`, requiring capture from the provider hook or `mir_for_ctfe`.
3. **Concrete Closure Upvars & Shims (`542 / 542` bodies have `spread_arg = None`) `[real measurement]`:** At `Runtime(PostCleanup)`, closures are already defunctionalized into nominal aggregates (`Aggregate(Closure, [...])`) whose bodies receive `_1 = env` and already-untupled parameters (`Field`/`Deref` projections off `_1`). However, `1 / 71` measured closure layouts differs from a tuple-of-upvars layout (ZST field offset `[8, 0]` vs. `[0, 0]`), requiring capture to record `layout_of` offsets directly. All `ClosureOnceShim`, `FnPtrShim`, and `ReifyShim` bodies reside at `Runtime(Optimized)` with `spread_arg = Some(_2)`; in a real `zerocopy` monomorphization graph (`35` closure instances), `0` need `ClosureOnceShim`, while `4` instances need `FnPtrShim(call_once, FnDef)`. Estimated incremental TCB for Type-0 concrete closures is **`~300` Rust + `~125–145` Lean LOC**.

## Applicability

- **Open generics & `ParamEnv` measurements:** Apply to `google/zerocopy@2b88472905` (`--lib --features alloc,std,simd,derive`) under `nightly-2026-06-01` (`14210df0e`, selected because local pinned `f8a08b688` lacked `rust-src`; 1 day compiler delta vs. `f8a08b688` not diffed for MIR drift) and to `library/core` from that toolchain's `rust-src`, built with dev overflow checks enabled (`assert:Overflow` counts drop under `-Coverflow-checks=no`).
- **Closure upvar & shim measurements:** Apply directly to `google/zerocopy@2b88472905` under pinned `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`-Zmir-preserve-ub`, `Runtime(PostCleanup)`), `library/core` from pinned `rust-src` (`-Cpanic=abort`), synthetic fixtures (`19` edition-2024 cases, `7` cases across editions 2018/2021), and a downstream binary monomorphization graph (`collect_and_partition_mono_items`) calling `zerocopy` APIs (`Ref::from_prefix/suffix`, `try_transmute_{ref,mut}!`, `<[bool]>::try_ref_from_bytes`, `SplitAt::split_at{,_mut}`, `SplitByteSlice` on `cell::Ref{,Mut}`, `Unalign::update`).
- **Relationship among subjects:** Characterizes MIR shapes emitted by `rustc` `Runtime(PostCleanup)` on `google/zerocopy` and `rust-lang/rust` `library/core` to determine the exact AST and TCB requirements for `anneal-rustc-capture` and `Trusted.MirSemantics`.

## Findings

### Spike 1: Open Generics & `ParamEnv` Coverage Tiers

Basis: `execution` (`600`-LOC `rustc_private` driver forcing `tcx.mir_drops_elaborated_and_const_checked(def)` in `after_analysis` under `-Zmir-preserve-ub` and `TypingEnv::post_analysis`, `[real measurement]`).

Tier definitions over fn-like bodies (`Fn`, `AssocFn`, `Closure`):
- **T0:** No type or const parameters.
- **T1 (clean open generic):** `TyKind::Param`/`ConstKind::Param` only; every call is monomorphic, inherent, or resolves generically to a concrete impl item.
- **T2 (bounded `ParamEnv`):** Needs `ParamEnv`-sourced dictionaries, rigid projections, generic `required_consts`, polymorphic `Drop`, or `Pointee`/`Unsize` reasoning over parameters.
- **T3 (Charon-like):** Unexplained dictionary source (specialization), GAT, nested projection, opaque type, virtual call, or resolution error.

| Corpus | Bodies (unstolen) | Generic `fn` | T0 | T1 | T2 | **T3** |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `zerocopy` | 9,349 | 4,166 | 560 | 3,865 (92.8%) | 301 (7.2%) | **0** |
| `core::{ptr,slice}` | 1,147 | 930 | 165 | 470 (50.5%) | 441 (47.4%) | **19 (2.0%)** |
| all of `core` | 28,016 | 7,225 | 16,551 | 2,854 | 4,203 | **168 (2.3%)** |

Named `zerocopy` target breakdown:

| Target | Bodies | Tiers | Requirements |
| :--- | ---: | :--- | :--- |
| `IntoBytes::as_bytes` | 1 | T1 | `ParamEnv` `Self: Immutable + IntoBytes + MetaSized`; generic `size_of_val::<Self>` resolves as inherent |
| `HasField` / `ProjectField` | 1,888 | 1,883 T1, 5 T2 | 2 `ParamEnv` dictionary calls (`HasField::project`, `ProjectField::is_projectable`), 4 rigid projections |
| `PtrInner` | 17 | 10 T1, 7 T2 | `KnownLayout::{pointer_to_metadata, raw_from_ptr_len, size_for_metadata_unchecked}` and `Project::project` via `ParamEnv`; `KnownLayout::PointerMetadata` projection |
| `Ref` | 34 | 10 T1, 24 T2 (1 `dyn Debug`, 2 alias-bound) | `Deref`/`DerefMut` on `B` (21), `SplitByteSlice::split_at` (6), 10 `StaticAssert` required consts, 13 polymorphic `Drop`, 2 alias-bound `PointerMetadata::{to,from}_elem_count` calls |
| `Wrap::transmute_*` | 16 | 8 T1, 8 T2 | `0` dictionary calls; 8 generic `StaticAssert::ASSERT` required consts, 1 polymorphic `Transmute` |

Trait-solver corners measured across the three corpora:

| Corner | `zerocopy` | `core::{ptr,slice}` | all `core` |
| :--- | --- | --- | --- |
| Unresolved trait call, `ParamEnv`-direct | 492 calls (135 bodies) | 157 | 4,000 |
| Unresolved trait call, alias item bound (`<T::PointerMetadata as PointerMetadata>::...`, `<I::Alignment as Alignment>::read`, `<T::MaybeUninit as KnownLayout>::...`) | **13** | 0 | 49 |
| Unresolved, `min_specialization` (`Spec*`/`*Impl`, `default fn`) | **0** | 19 (sort, `slice::cmp`, `SpecFill`, `CloneFromSpec`) | 113 |
| `ParamEnv` supertrait elaboration needed | **0** (`tcx.param_env` already elaborated) | 0 | 0 |
| Generic call resolved generically to impl item | 367 | 267 | 1,700 |
| GAT projections | 0 | 0 | 44 bodies (`AsyncFn*`, `str::pattern`) |
| Nested projection (projection on alias) | 0 | 0 | 14 |
| Opaque / `impl Trait` | 0 | 0 | 0 |
| HRTB clauses (all lifetime-only, erasable) | 1 (`Unalign::update`: `for<'a> FnOnce(&'a mut T)`) | 172 bodies (`FnMut(&T)`) | 361 |
| `HostEffect` (`[const] Trait`) clauses | 0 | 110 | 2,827 |
| Auto-trait clauses (`Send`/`Sync`/`Unpin`/...) | **0** | 0 | 24 |
| `Unsize`/`CoerceUnsized`/`DispatchFromDyn` clauses | **0** | 0 | 0 |
| Polymorphic unsize coercions (builtin, from concrete shape) | 4 (`→ dyn Debug` in `fmt`) | 64 (32 slice, 32 dyn) | — |
| `Pointee` | 0 `ptr::Pointee` clauses; `KnownLayout::PointerMetadata` rigid projection in 57 bodies; 26 unknown-metadata ptr casts | 7 `Pointee` clauses; rigid `Pointee::Metadata` in 9 bodies; 61 `PtrMetadata` on params; 183 unknown-metadata casts | — |
| Polymorphic `Drop` | 38 bodies (54 direct `T` drops) | 73 bodies; 2 `ptr::drop_glue` unresolved | — |
| `Sized`/`MetaSized` clauses | 42,193 / 6,131 (mean 16.4/generic fn, max 130) | 1,054 / 283 | — |

All rigid projections in `zerocopy` are single-level `<P as Tr>::A` rooted at a parameter (none are GATs): `KnownLayout::PointerMetadata` (57 bodies), `Invariants::{Aliasing,Validity,Alignment}` (22, 15, 13), `SplitAt::Elem` (18), `HasTag::Tag`, `HasField::Type`, `ProjectField::Error`, `TryWithError::{Mapped,Inner}`, `KnownLayout::MaybeUninit`, `BoxAllocator::Boxed`, and `Deref::Target`.

**Stolen monomorphic consts finding:** Forcing `mir_drops_elaborated_and_const_checked` in `after_analysis` found `0` stolen function bodies, but **`117` (`zerocopy`) and `1,883` (`core`) stolen monomorphic `const`/`AnonConst` bodies** (already stolen by analysis-time CTFE). `capture.rs:1054` ("force then check `is_stolen`") would reject any selected monomorphic const item; generic consts were never stolen. Const capture must extract inside the provider hook (guarding against E0391 cycles) or read `mir_for_ctfe`.

### Spike 2: Generic `required_consts` and `ConstMirMachine` Subset

Basis: `execution` (`[real measurement]`).

- `zerocopy` has `0` inline `const { ... }` blocks; `static_assert!` / `const_assert!` expand to `const ASSERT: bool` on a blanket trait (`impl<T...> StaticAssert for T`), yielding **`40` `StaticAssert::ASSERT` impl const bodies** and **`89` generic const bodies** seeding a **`106`-body transitive const-eval closure** (including `19` local `const fn`s such as `DstLayout::for_type`, `validate_cast_and_convert_metadata`, `TrailingSliceLayout::*`, `padding_needed_for`, `round_down_to_next_multiple_of_alignment`).
- In generic fn `required_consts` (`91` generic `AssocConst` entries): `KnownLayout::LAYOUT` (`88`, `try_resolve` returns `UNRESOLVED` `ParamEnv` const), `ByteOrder::ORDER` (`24`, `UNRESOLVED`), `CastFrom::project::Params::CAST_PARAMS` (`UNRESOLVED`), and every `StaticAssert::ASSERT` entry (resolving generically to the blanket-impl const). Plus `182` runtime operands reading `Const::Unevaluated(AssocConst)`.
- In `core`: `mem::size_of::<T>()` is a runtime read of `<T as SizedTypeProperties>::SIZE` calling `intrinsics::size_of::<T>()`; `IS_ZST` appears in `69` `ptr`/`slice` bodies; `8` generic `InlineConst`s appear in `ptr`/`slice`; `ConstKind::Param` appears as `Const::Ty(Param)` in `69` `required_consts`, `138` operands, and `47` `[T; N]` bodies; `generic_const_exprs` (`ConstKind::Expr` / type-level `Unevaluated`) occurs **`0` times** in either crate.
- **Minimal `ConstMirMachine` operator union (`106` `zerocopy` const bodies):**
  - Statements: `Assign`, `PlaceMention`, `StorageLive`/`StorageDead`.
  - Rvalues: `Use`, `Ref` (19), `Repeat` (17), `Aggregate` (Struct 41, Enum 43, Tuple 9), `Discriminant` (87), `UnaryOp::Not`, `Cast::IntToInt` (1).
  - `BinaryOp`: `Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`, `BitAnd`, `BitOr`, `BitXor`, `Shl`, `Div`, `Rem`, `Add`/`SubWithOverflow`.
  - Terminators: `SwitchInt`, `Goto`, `Return`, `Unreachable`, `Call`, `Assert` (Overflow/DivByZero/RemByZero).
  - Constants: `Unevaluated(AssocConst)` (163), `Unevaluated(Const)` (4), promoted (3), `Ty(Param)` (2).
  - External calls: `mem::{size_of, align_of}`, `NonZero::{get, new}`, `usize::{checked_*, wrapping_*, is_power_of_two, leading_zeros}`, `Option::is_some`, `panic`, `panic_fmt` + `Arguments::from_str` (plus `needs_drop`, `variant_count`, `type_id`/`type_info` in `core`).
  - Zero pointers, raw pointers, non-`IntToInt` casts, `Drop`, or unsizing occur in this subset. Because monomorphization aborts if any `required_consts` fails, `ConstMirMachine` translates each const body symbolically into a predicate over abstract `size_of T`/`align_of T`/`T::LAYOUT` assumed by the generic body.

### Spike 3: Concrete Closure Upvars, `RustCall`, and Shims

Basis: `execution` (`[real measurement]`) + `source` inspection of `rustc_mir_transform/src/shim.rs:67-249`, `rustc_const_eval/src/interpret/{step.rs, call.rs:458, 661-683}`, `rustc_middle/src/mir/statement.rs:868-874`, and `anneal/trusted/` at `google/zerocopy@2b88472905`.

Baseline `anneal-rustc-capture` refuses every closure: `capture.rs:235-237` admits only `Fn | AssocFn`, `extract.rs:200` rejects `Closure(...)`, and `Trusted/MirAst/Types.lean:265-280` maps `Closure` to `.unsupported`.

Census across all measured corpora (`[real measurement]`):

| Corpus | Driver mode | Bodies at `PostCleanup` | Closures | Closure `unsafe` blocks |
| :--- | :--- | ---: | ---: | ---: |
| Synthetic `closures.rs` (19 cases, ed. 2024; `unwind` & `abort`) | per-body census + resolution matrix | 42/42 | 19 | 1 |
| `editions.rs` (7 cases × editions 2018/2021) | per-body census | 15/15 per ed. | 7 | 1 |
| Verbatim `zerocopy/src` (`alloc,std,simd`; `unwind` & `abort`) | per-body census | **4,588/4,588** | **43** | **14** (12 bodies) |
| Verbatim `library/core` (`-Cpanic=abort`; 15.8 s wall, 870 MB RSS) | per-body census | **23,775/23,775** | **466** | 20 |
| Downstream bin calling real `zerocopy` APIs | `collect_and_partition_mono_items` | — | 35 `zerocopy` + 3 `core` instances | — |

Empirical closure properties (`[real measurement]` unless noted):
1. **`spread_arg = None` (`542 / 542` bodies):** Every closure signature uses `ExternAbi::RustCall`, receiving `_1 = env` (`{closure}`, `&{closure}`, or `&mut {closure}`) followed by already-untupled parameters; `extract.rs:1038-1045`'s `spread_arg.is_some()` refusal can stay unchanged. `zerocopy` has `40 / 43` `FnOnce` (by-value env), `3` `FnMut` (`&mut` env), and `0` `Fn` (`&` env); `core` has `118 / 317 / 31`.
2. **Upvar construction & access:** Construction uses `Aggregate(Closure, [...])` (which performs no retag in `write_aggregate` `step.rs`), using `move &T` (`11×`), `move &mut T` (`1×`), `copy *mut T` (`1×`), and by-value operands in `zerocopy`. Access uses ordinary projections (`Field(0)` 15, `Field(0).Deref` 11, `Deref.Field(0)` 2 in `zerocopy`; `Deref.Field(k)` 354, `Field(k)` 196, `...Field(k).Deref` 164 in `core`), e.g.:
   ```text
   // <cell::Ref<[u8]> as SplitByteSlice>::split_at_unchecked::{closure#0}
   _5 = no_retag copy (_1.0: &usize);
   _4 = copy (*_5);
   _0 = <&[u8] as SplitByteSlice>::split_at_unchecked(move _3, move _4)
   ```
   By-ref upvars read via `no_retag copy (_1.0: &usize)` (`11` in `zerocopy`, `17` in fixture) require modeling `WithRetag::No` (current `ir::Body::try_new` admits only retag-noop `Use`s).
3. **Layout divergence (`1 / 71` mismatch):** `map_try_fold::<..., {zerocopy Ptr::iter closure}, {Iterator::all::check closure}>::{closure#0}` (upvars `(ZST closure, &mut closure)`) has `rustc` closure layout `{ size: 8, align: 8, offsets: [8, 0] }` vs. tuple-of-upvars `{ size: 8, align: 8, offsets: [0, 0] }` (`ZST` offset differs). Capture **must** record `layout_of` offsets rather than recomputing tuple layouts in Lean.
4. **Call resolution & `RustCall` untupling:** Calling `<F as FnOnce<(T,)>>::call_once(move _6, move _7)` resolves under `Instance::try_resolve` directly to `Item(closure_def)` for all `35` `zerocopy` closure instances in the downstream mono graph (`Option::map`, `Result::map_err`, `<Map as Iterator>::fold`, `cell::Ref::map_split`/`RefMut::map_split`). `call.rs:661-683` untuples the final tuple argument whenever `caller_abi == RustCall`; adding an explicit `untupleLast : Bool` flag on `TerminatorKind.call` avoids rewriting operands in the Rust TCB.
5. **Shims are never `PostCleanup` (`shim.rs:67-249`):** Every `ClosureOnceShim`, `FnPtrShim`, and `ReifyShim` has `phase = Runtime(Optimized)` and `spread_arg = Some(_2)`. In the downstream mono graph, `0 / 35` `zerocopy` closures require `ClosureOnceShim`, while **`4` instances require `FnPtrShim(call_once, FnDef)`** (`.map(Ptr::as_ref)`, `as_mut`, `[u8]` `as_ref`, `impls.rs:934` `.all(<T as TryFromBytes>::is_safe)`), which capture can resolve directly to `FnDef` with `untuple_last = true`.
6. **Other corners:** `UniqueImmutable` / `Ref(Mut { kind: ClosureCapture })` (`0` in `zerocopy`, `10/280` in `core`, `statement.rs:868-874` treats every `BorrowKind::Mut` alike except `TwoPhaseBorrow`) lowers to `.ref .mut`. RFC 2229 precise/truncated captures (`0` in `zerocopy`, `108` in `core`) affect only the parent's borrow place. `Drop` of a `!needs_drop` monomorphic closure lowers to `goto` (`0` `DropGlue` closure instances in the mono sample). Unwind edges appear in `6 / 43` `zerocopy` closures under `panic=unwind` and `0` under `abort`. `FnEntry` retag of a by-value env holding `&mut` (`split_at_mut` closure) follows the general struct-field retag rule (`call.rs:458`, `source` inspection only).

### Recommended Implementation Sequence

Basis: `derived` from Spike 1–3 measurements (`[projection from code inspection]` for closure TCB LOC).

1. **Open Generics / `ParamEnv` / `ConstMirMachine`:** (1) Capture `tcx.param_env(def).caller_bounds()` verbatim + 3-variant `ImplSource` (`Resolved | Param | AliasBound`), failing closed on specialization/GAT/nested/opaque/virtual; (2) model rigid single-level projections as opaque type vars with `item_bounds`; (3) implement the `ConstMirMachine` subset for generic `required_consts`; (4) fix monomorphic const capture via provider hook or `mir_for_ctfe`.
2. **Concrete `Type-0` Closures (`PR W5-a`, `~300` Rust + `~125–145` Lean TCB LOC on top of W1–W4 prerequisites):** `extract::ty` (`~35`), `extract::rvalue` (`~15`), `extract::terminator` + `mono.rs` (`~130`), `capture.rs` (`~25`), `ir.rs` validation (`~70`), `lean.rs` (`~30`), `Trusted.MirAst` (`~35`), `Trusted.MirSemantics` (`~90–110`). First-customer targets: `<cell::Ref<'_, [u8]> as SplitByteSlice>::split_at_unchecked::{closure#0}` (+ `RefMut` twin, `byte_slice.rs:335,355`), `PtrInner::<[T]>::iter::{closure#0}` (`inner.rs:450`, `3` `unsafe` blocks), and `Wrap::try_transmute_{ref,mut}::{closure#0,1}` (`macro_util.rs:808-886`).

## Boundaries

- **No proof or semantics execution (`not examined`):** Neither spike modified Anneal's Rust or Lean codebase or executed Lean `MirSemantics` proofs; closure TCB LOC figures are projections from file structure, not implementations.
- **Compiler gap (`not examined`):** Spike 1 used `nightly-2026-06-01` (`14210df0e`) so `rust-src` matched its compiler; the 1-day compiler difference vs. pinned `f8a08b688` (`2026-05-30`) was not diffed for MIR differences.
- **Unexercised closure surfaces (`not examined` / `unsupported`):** `FnEntry` retag of by-value closure environments holding `&mut` upvars was checked by source inspection (`call.rs:458`), not dynamically under Miri; `cfg`-gated closure sites (`inner.rs:710/720/770`) outside `alloc,std,simd`, other downstream generic instantiations that may produce `ClosureOnceShim`/`FnPtrShim`, and `-Cpanic=unwind` cleanup semantics were not exercised.
- **Deferred / fail-closed items (`unsupported`):** `ClosureOnceShim`, `ClosureFnPointer` coercions, `FnPtrShim(_, FnPtr)` (non-`FnDef`), `Virtual` / indirect calls inside closures, `min_specialization` (`19` calls in `core::{ptr,slice}`), polymorphic `drop_glue::<T>`, and `core::ptr::Pointee` builtin metadata remain deferred or fail-closed.

## Evidence

- **Open generics & `ParamEnv` spike (`[real measurement]`):** Custom `rustc_private` wrapper (`600` LOC) executed under `nightly-2026-06-01` (`14210df0e`) on `google/zerocopy@2b88472905` (`alloc,std,simd,derive`, `9,349` unstolen bodies, `89` generic consts / `106`-body closure) and `library/core` (`28,016` unstolen bodies; `20 s` run under memory-capped cgroup).
- **Closure upvar & shim spike (`[real measurement]` + `[source inspection]`):** Custom `rustc_private` driver executed under pinned `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`-Zmir-preserve-ub`) across synthetic `closures.rs` (`42` bodies), `editions.rs` (`15` bodies/edition), `google/zerocopy@2b88472905` (`4,588/4,588` bodies, `43` closures), `library/core` (`23,775/23,775` bodies, `466` closures, `15.8 s` wall, `870 MB` RSS), and downstream `collect_and_partition_mono_items` (`35` `zerocopy` + `3` `core` closure instances), cross-checked against `rustc_mir_transform/src/shim.rs:67-249`, `rustc_const_eval/src/interpret/{step.rs,call.rs}`, `rustc_middle/src/mir/statement.rs:868-874`, and `anneal/trusted/{rustc-capture/src/{capture,extract}.rs,lean/Trusted/MirAst/Types.lean}` at `2b88472905`.

## Revalidation

1. Re-run a `rustc_private` `after_analysis` visitor forcing `tcx.mir_drops_elaborated_and_const_checked(def)` under `-Zmir-preserve-ub` on a newer `google/zerocopy` commit or `rustc` pin and check that `T3` count (`specialization | GAT | nested projection | opaque | virtual`) remains `0` across `zerocopy` and that `spread_arg.is_none()` still holds across all closure bodies.
2. Diff `anneal/trusted/rustc-capture/src/{capture,extract}.rs` and `rustc_mir_transform/src/shim.rs` when advancing the pinned `rustc` revision to verify `ClosureOnceShim`/`FnPtrShim` template stability and whether `capture.rs:1054` const-stealing or `ir::Body::try_new` `no_retag` admissions have landed.
