# `rustc_transmute` (`core::mem::TransmuteFrom<Src, ASSUME>`): 257-Symbol Byte-Level DFA Checking, Safety-Invariant Pruning, Reference Obligations, and the Live `&Cell<T> -> &T` Soundness Defect

## Summary

`rustc_transmute` implements the compiler-synthesized nightly trait `core::mem::TransmuteFrom<Src, const ASSUME: Assume>` (`#[lang = "transmute_trait"]`, `#[rustc_coinductive]`, tracking issue `rust-lang/rust#99571`) by lowering monomorphized Rust layouts to trees of 257-symbol byte ranges, zero-width definition markers, and reference transitions; pruning destination definitions that may carry safety invariants; compiling the trees into acyclic deterministic finite automata (`Dfa`); and comparing the automata to emit either `Answer::Yes`, `Answer::No(Reason)`, or `Answer::If(Condition)` for the trait solver. Primary-source inspection across `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), live `rustc` / LLVM IR / Miri execution (52 compile-time cases across legacy and `-Z next-solver=globally`, plus native `-O0`/`-O2` and Stacked/Tree Borrows runs), audit of Anneal's trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), and a constructive `Lean v4.34.1` formalization establish six load-bearing facts:

1. **257-Symbol Byte Alphabet and Conservative `Def::has_safety_invariants` Pruning:** `layout::Byte` models half-open intervals `[start, end)` over `0..=256`, where `0..=255` are initialized byte values and `UNINIT = 256` represents an uninitialized byte (`Byte::uninit()` is `[0, 257)`, accepting any initialized byte *or* uninitialized). During `Tree` pruning, source `Def` markers are unconditionally stripped (`src.prune(&|_def| false)`), while destination `Def` markers are pruned whenever `!assume.safety && def.has_safety_invariants()`. Because `Def::has_safety_invariants()` is implemented conservatively as `self != &Self::Primitive`, **every user-defined struct, enum, and union—as well as `core::mem::MaybeUninit<T>`—is pruned away as a destination unless `Assume::SAFETY` is passed** (returning `Reason::DstMayHaveSafetyInvariants`). Separately, `Tree::from_variant` requires `FieldsShape::Arbitrary`, so `NonZero<u8>` and `Option<NonZero<u8>>`—whose `NonZero` inner struct has `FieldsShape::Primitive`—fail closed with `SrcIsNotYetSupported` / `DstIsNotYetSupported` (tracked by open PR `rust-lang/rust#148449`), whereas `Option<bool>` (`TagEncoding::Niche` over primitive `bool`) is already supported.
2. **Union-Transmute Semantics (Prefix Truncation and Trailing-Uninit Extension) and the `Assume::VALIDITY` Quantifier Flip:** `TransmuteFrom::transmute` is defined operationally via a `#[repr(C)]` union (`ManuallyDrop<Src>` / `ManuallyDrop<Dst>`), not equal-size `core::mem::transmute`. In `MaybeTransmutableQuery::answer_impl`, reaching `dst_state == dst.accept` returns `Answer::Yes` immediately (permitting prefix truncation such as `u32 -> u8`), while reaching `src_state == src.accept` before `dst.accept` advances `dst` solely along `UNINIT`-covering edges via `Dfa::get_uninit_edge_dst` (permitting trailing-padding extension such as `u8 -> PaddedAlign2`, while rejecting `u8 -> u16` with `DstIsTooBig`). Setting `Assume::VALIDITY` does **not** bypass DFA comparison: it switches `Quantifier::ForAll` (language inclusion $L(\text{Src}) \subseteq L(\text{Dst})$ for equal-size types) to `Quantifier::ThereExists` (non-empty intersection $L(\text{Src}) \cap L(\text{Dst}) \neq \emptyset$), so disjoint bit-validity sets (`TwoOnly -> bool`) are still rejected even with `Assume::VALIDITY`. Uninhabited sources (`Void -> u128`) vacuously yield `Answer::Yes`, whereas inhabited-to-uninhabited (`u8 -> Void`) yields `DstUninhabited` even with all four `Assume` flags enabled.
3. **Non-Boolean `Answer::or` Retention and `IfAny`-as-`IfAll` Solver Collapse:** `Answer::or` (`compiler/rustc_type_ir/src/transmute.rs:106-131`) matches `(Answer::Yes, other) | (other, Answer::Yes) => other`, retaining `If(c)` instead of absorbing to `Yes`. Combined with `Quantifier::ThereExists` breaking only on `Answer::Yes`, this makes `TransmuteFrom` under `Assume::VALIDITY` **dependent on enum discriminant ordering**: empirically, `SrcMixRefFirst { RefArm(&'a u8) = 0, ByteArm(u8) = 1 } -> DstMixRefFirst { RefArm(&'a Cell<u8>) = 0, ByteArm(u8) = 1 }` is rejected (`UnsafeCell<u8>: Freeze` unsatisfied), while swapping discriminants `0` and `1` (`SrcMixByteFirst -> DstMixByteFirst`) causes the exact same transmutation to compile under both solvers. Independently, `flatten_answer_tree` (`compiler/rustc_next_trait_solver/src/solve/mod.rs:452-457`, shared by both legacy and next solvers) flattens `Condition::IfAny(conds)` identically to `Condition::IfAll(conds)`, causing `&'a u8 -> union DstRefUnion<'a> { good: &'a u8, bad: &'a Cell<u8> }` to fail on `Cell<u8>: Freeze` despite the matching `&'a u8` field.
4. **Live Soundness Defect `rust-lang/rust#164247` (`&Cell<T> -> &T` under `Assume::NOTHING`) Across Legacy and Next Solvers:** At `compiler/rustc_transmute/src/maybe_transmutable/mod.rs:278-282` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; `:297-301` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), when `!dst_ref.is_mut`, `rustc_transmute` emits `Condition::Immutable { ty: dst_ref.referent }` (`Dst: Freeze`) but **omits `Condition::Immutable { ty: src_ref.referent }` (`Src: Freeze`)** when `!src_ref.is_mut`. Because the nested query `u8: TransmuteFrom<Cell<u8>, { Assume::NOTHING }>` strips `Def::Adt(Cell)` and `Def::Adt(UnsafeCell)` from `src`, `<&u8 as TransmuteFrom<&Cell<u8>, { Assume::NOTHING }>>::transmute` is accepted. On `rustc 1.98.0-nightly` (`14210df0e`), LLVM `-O2` emits `ptr noalias noundef nonnull readonly captures(none) dereferenceable(1) %ro` on the transmuted `&u8`, miscompiling an alias test (`-O0`: `BEFORE=7 AFTER=99 CELL=99`; `-O2`: `BEFORE=7 AFTER=7 CELL=99`), and Miri faults immediate UB (`rc = 1`) in both Stacked Borrows and Tree Borrows under both protected (`FnEntry` strong protector failing at `cell.set(99)`) and unprotected (inline `main` failing at the subsequent `*ro` read) contexts. Prior to `cee2a0ddf022ee393e384ff576c6a190915f19a1` (`2026-10-12`, PR `#163946`), `-Z next-solver=globally` rejected all `Answer::If` obligations (11/38 divergences on `1.98.0-nightly`); after `cee2a0ddf022ee393e384ff576c6a190915f19a1` (verified on `1.102.0-nightly` `3ef0c22cd` and `HEAD` `342d74463a`), legacy and `-Z next-solver=globally` agree on 38/38 cases and **both** exhibit `#164247`.
5. **Exact Interior-Mutability Aliasing Boundaries Observed in Miri:** Miri execution separates three distinct cases: (a) `&mut Cell<u8> -> &u8` (`Assume::NOTHING`) succeeds with `rc = 0` under both Stacked Borrows and Tree Borrows because the unique `&mut` handle is consumed by value; (b) `&#[repr(C)] struct CellFirst(Cell<u8>, u8) -> &u8` triggers immediate UB (`rc = 1`) in both Stacked Borrows and Tree Borrows; and (c) `&#[repr(C)] struct CellSecond(u8, Cell<u8>) -> &u8` passes (`rc = 0`, `CELL_SECOND B=7 A=7 CELL=99`) when mutating `.1` while reading `.0`. Consequently, adding `Condition::Immutable { ty: src_ref.referent }` when `!src_ref.is_mut && !dst_ref.is_mut` is sound (sufficient to close `#164247` and all overlapping prefix-truncation hazards) and strictly coarser than byte-offset `visit_freeze_sensitive` only when an `UnsafeCell` lies entirely outside `[0, size_of::<Dst>())`.
6. **Anneal Trusted-Boundary Implications and Kernel-Checked `Lean v4.34.1` Formalization:** At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` and `Trusted.MirSemantics` already model the 257-element byte space via `AllocByte` (with optional `AllocId` provenance), enforce `deinitMovedPlace = true`, and fail closed to `.unsupported` on `Rvalue::Cast` (including `CastKind::Transmute`), structs/unions, and retagging `Use(_, WithRetag::Yes)` on reference-containing types. Any future trusted boundary or verified compiler pass MUST NOT treat `rustc`'s `TransmuteFrom` solver answers as a trusted oracle while `#164247` remains open. The accompanying 1,097-line `Lean v4.34.1` module `support/RustcTransmuteDfaAndRefSoundness.lean` (kernel-checked with `-DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, max axioms `[propext, Quot.sound]`) mechanizes the 257-symbol byte DFA, union-transmute prefix truncation and trailing-uninit extension, `Def::has_safety_invariants` pruning, `Answer::or` order asymmetry, and the upstream vs. repaired reference `Freeze` rules, proving soundness of the DFA checker and repaired reference rule alongside three constructive counterexamples (`ce1`, `ce2`, `ce3`).

## Applicability

This report characterizes the exact relationship among five pinned subjects listed in `REPORT.json`:

- **Upstream `rustc` primary source (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, observed `2026-11-22`):** Direct source audit of `compiler/rustc_transmute/src/{lib.rs, layout/mod.rs, layout/tree.rs, layout/dfa.rs, maybe_transmutable/mod.rs, maybe_transmutable/query_context.rs}`, `compiler/rustc_type_ir/src/transmute.rs`, `compiler/rustc_trait_selection/src/{traits/select/candidate_assembly.rs, traits/select/confirmation.rs, solve/delegate.rs}`, `compiler/rustc_next_trait_solver/src/solve/{mod.rs, trait_goals.rs}`, and `library/core/src/mem/transmutability.rs`.
- **Executed nightly toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly 2026-05-31`, `miri 0.1.0`, `LLVM 22.1.6`, `x86_64-unknown-linux-gnu`):** Direct live execution via `support/probe_rustc_transmute.py` (`support/probe_rustc_transmute_results.json`) of all 38 core `TransmuteFrom` cases and 14 extended diagnostic cases under both the legacy trait solver and `-Z next-solver=globally`, native `-Copt-level=0` and `-Copt-level=2` binaries, `-Copt-level=2 --emit=llvm-ir`, and Miri under both default Stacked Borrows and `-Zmiri-tree-borrows`.
- **Post-`#163946` nightly toolchain (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly 2026-11-11`, `LLVM 23.1.5`, `x86_64-unknown-linux-gnu`):** Direct source diff confirming byte-for-byte identity with `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` across `compiler/rustc_transmute/src/`, plus recorded 38-case legacy-vs-`-Z next-solver=globally` and Miri comparison.
- **Anneal trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Direct source audit of `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` to determine current transmutation/union/retagging fail-closed boundaries and requirements for integrating verified transmutability.
- **Lean 4 kernel (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Direct kernel checking of `support/RustcTransmuteDfaAndRefSoundness.lean` using Core Lean only (zero Mathlib or Lake dependencies).

### Version-Specific Differences vs. Shared Invariants

| Behavior / Mechanism | `1.98.0-nightly` (`14210df0e`, `2026-05-31`) | `1.102.0-nightly` (`3ef0c22cd`, `2026-11-11`) & `HEAD` (`342d74463`, `2026-11-22`) | Primary-Source Cause |
| :--- | :--- | :--- | :--- |
| 257-symbol `Byte`, `Tree::from_ty`, `Def::has_safety_invariants`, `Dfa` union/concat, `MaybeTransmutableQuery::answer_impl` | Identical semantics (`Answer`/`Condition`/`Reason` in `rustc_transmute::lib`) | Identical semantics (`Answer`/`Condition`/`Reason` moved to `rustc_type_ir::transmute` in `5b216e01a117532b30f061f3dff8a61408113c77`) | Source diff of `compiler/rustc_transmute/src/*` shows comments/moves only; algorithm unchanged. |
| Legacy trait solver handling of `Answer::If(cond)` (all reference `TransmuteFrom` cases) | Lowers `Answer::If` via `flatten_answer_tree`; accepts valid refs **and** unsound `&Cell<u8> -> &u8` (`Assume::NOTHING`) | Identical (`confirm_transmutability_candidate` calls `flatten_answer_tree`) | `compiler/rustc_trait_selection/src/traits/select/confirmation.rs:275-318`. |
| `-Z next-solver=globally` handling of `Answer::If(cond)` | **Stubbed to `Err(NoSolution)`** in `delegate.rs:378-381`; diverges from legacy on 11/38 core ref cases (+ 1/14 extended) | **Implemented** via `flatten_answer_tree` in `trait_goals.rs:723-734` (merged `2026-10-12` in `cee2a0ddf022ee393e384ff576c6a190915f19a1`, PR `#163946`); **0/38 divergences**, so `#164247` now reproduces under **both** solvers | `delegate.rs:378-381` (`14210df0e`) vs `trait_goals.rs:720-736` (`342d74463`). |
| `Answer::or(Yes, If(c)) = If(c)` & `flatten_answer_tree` collapsing `IfAny` into `IfAll` | Present in both (`maybe_transmutable/mod.rs:350-374`) | Present in both (`rustc_type_ir/src/transmute.rs:106-131`, explicit comment added on lines 104-105; `next_trait_solver/src/solve/mod.rs:454`) | Unchanged semantics; `answer_or_byte_first_safety_validity` even succeeds on `1.98` next-solver because `ByteArm` breaks with `Answer::Yes`. |
| `NonZero<u8>` / `Option<NonZero<u8>>` (`FieldsShape::Primitive`) | Rejected (`SrcIsNotYetSupported` / `DstIsNotYetSupported`) | Still rejected (`rust-lang/rust#148449` remains open as of `2026-11-22`) | `tree.rs:485-487` requires `FieldsShape::Arbitrary`. |

### Scope Qualifications

- All Rust probes require nightly `#![feature(transmutability)]` (`edition = "2024"`) and were executed on `x86_64-unknown-linux-gnu` (little-endian, 64-bit pointers). Endianness affects multi-byte `char` and enum tag byte ordering (`Tree::from_big_endian` / `Tree::from_tag`) as well as the specific byte extracted by prefix truncation (`u32 -> u8` yields `0x44` from `0x11223344u32` on little-endian; on big-endian it would yield `0x11`).
- The Lean 4 formalization (`support/RustcTransmuteDfaAndRefSoundness.lean`) models the byte-level DFA algorithm, tree safety-invariant pruning, `Answer::or` order asymmetry, and reference `Freeze` obligations over a small-step single-location aliasing model. No machine-checked refinement proof links this Lean model to `rustc`'s Rust source code, LLVM IR, or Miri's full Stacked/Tree Borrows interpreter; all claims connecting the Lean theorems to `rustc`/Miri are `derived` modeling arguments, explicitly separated under **Boundaries**.

## Findings

### 1. 257-Symbol Byte Alphabet, Layout Trees, `NonZero` Rejection, and `Def::has_safety_invariants` Pruning

Basis: source + execution (`compiler/rustc_transmute/src/layout/{mod.rs, tree.rs, dfa.rs}`, `support/probe_rustc_transmute_results.json`)

#### 1.1 The 257-Symbol Alphabet (`Byte { start, end }`)

In `compiler/rustc_transmute/src/layout/mod.rs:19-57` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), a single byte's validity set is represented as a half-open `u16` interval `[start, end)` over the 257-element alphabet `{0, 1, ..., 255, 256}`:

```rust
pub(crate) struct Byte {
    pub(crate) start: u16,
    pub(crate) end: u16,
}

impl Byte {
    const UNINIT: u16 = 256;

    fn new(range: RangeInclusive<u8>) -> Self {
        let start: u16 = (*range.start()).into();
        let end: u16 = (*range.end()).into();
        Byte { start, end: end + 1 }
    }

    fn uninit() -> Byte {
        Byte { start: 0, end: Self::UNINIT + 1 } // [0, 257): 0..=255 | UNINIT
    }

    fn contains_uninit(&self) -> bool {
        self.start <= Self::UNINIT && Self::UNINIT < self.end
    }
}
```

Key representation invariants:
- **`Byte::uninit()` is `[0, 257)`, NOT `[256, 257)`:** Because a padding byte or `MaybeUninit<u8>` byte may hold *either* any initialized byte `0..=255` *or* the uninitialized value `UNINIT = 256`, `Tree::uninit()` / `Tree::padding(n)` emits `[0, 257)`. Consequently:
  - Transmuting initialized `u8` (`[0, 256)`) into `MaybeUninit<u8>` (`[0, 257)`) satisfies `[0, 256) ⊆ [0, 257)` (once `Assume::SAFETY` bypasses ADT pruning).
  - Transmuting `MaybeUninit<u8>` (`[0, 257)`) or `HasPad` (whose padding byte carries `[0, 257)`) into `u8` / `[u8; 4]` (`[0, 256)`) fails under `Assume::NOTHING` because `256 ∈ [0, 257) \ [0, 256)` (`Reason::DstIsBitIncompatible`).
  - Transmuting `MaybeUninit<u8>` into `u8` under `Assume::VALIDITY` succeeds because `[0, 257) ∩ [0, 256) = [0, 256) ≠ ∅`.
- **Sorted, non-overlapping `EdgeSet` runs (`layout/dfa.rs:342-425`):** Outbound byte transitions from a `Dfa` state are stored in `SmallVec<[(Byte, State); 1]>` in ascending order of `start`, merging adjacent runs with equal destination states. Because `UNINIT = 256` is the maximum symbol in the alphabet, `EdgeSet::get_uninit_edge_dst` (`dfa.rs:379-386`) checks **only the last run** (`self.runs.last()?` and `range.contains_uninit()`), running in $O(1)$ time.
- **No pointer provenance on byte edges:** Byte transitions encode only initialization status and numeric value `0..=255`; reference transitions are segregated into `Transitions::ref_transitions: Map<Reference<R, T>, State>` (`dfa.rs:24-31`). Raw pointers (`*const T`, `*mut T`), `Box<T>`, function pointers, slices, `str`, `dyn Trait`, closures, and coroutines all hit the fallback `_ => Err(Err::NotYetSupported)` in `Tree::from_ty` (`tree.rs:368`).

#### 1.2 `Tree::from_ty`, `FieldsShape::Primitive`, and Why `Option<NonZero<u8>>` Fails While `Option<bool>` Succeeds

`Tree::from_ty` (`compiler/rustc_transmute/src/layout/tree.rs:304-370`) lowers monomorphized types (`TypingEnv::fully_monomorphized()`, `maybe_transmutable/mod.rs:50`) as follows:
- `ty::Bool` -> `Byte(0..=1)`; `ty::Int` / `ty::Uint` / `ty::Float` -> `Seq` of `width` `u8` (`0..=255`) bytes; `ty::Char` -> 3-way `Alt` over UTF-32 scalar ranges `[0x0000..=0xD7FF]` and `[0xE000..=0x10FFFF]` adjusted for target endianness (`tree.rs:97-114`).
- `ty::Tuple` -> `from_tuple` (`tree.rs:373-390`): handles **both** `FieldsShape::Primitive` (1-element tuple delegates directly to `from_ty(members[0])`) and `FieldsShape::Arbitrary` (delegates to `from_variant` with `Def::Primitive`).
- `ty::Array(inner, _)` -> requires `FieldsShape::Array { stride, count }` (`assert_eq!(*stride, inner_layout.size)`), folding `count` copies of `Tree::from_ty(*inner)` via `Tree::then` (`tree.rs:335-344`).
- `ty::Ref(region, ty, mutability)` -> `Tree::Ref(Reference { region, is_mut, referent, referent_align, referent_size })` (`tree.rs:352-364`), preserving regions un-erased via `ty_field` (`tree.rs:589-619`) so outlives constraints can be emitted later.
- `ty::Adt(adt_def, _)` (excluding `Box`, guarded by `if !ty.is_box()`, `tree.rs:346`) -> dispatches to `from_struct`, `from_enum`, or `from_union`:
  - `from_struct` wraps `Def::Adt(def)` and calls `from_variant` (`tree.rs:397-405`).
  - `from_enum` returns `Tree::uninhabited()` for `Variants::Empty`, delegates directly for `Variants::Single { index }`, and for `Variants::Multiple { tag_encoding, tag_field, .. }` asserts `tag_field == FieldIdx::ZERO` and folds all discriminants via `Tree::or`, prefixed with `Def::Adt(def)` (`tree.rs:412-465`). Inside `from_variant`, `TagEncoding::Direct` advances `size += tag.size()`, while `TagEncoding::Niche { niche_variants, .. }` advances `size += tag.size()` only when `!niche_variants.contains(index)` before appending `Self::from_tag(*tag)` (`tree.rs:498-510`).
  - `from_union` requires `FieldsShape::Union` and builds `Def::Adt(def).then(or_i (field_i.then(trailing_padding_i)))` (`tree.rs:558-586`).

**Root cause of `NonZero<u8>` and `Option<NonZero<u8>>` failure (`rust-lang/rust#148449`):**
In `Tree::from_variant` (`compiler/rustc_transmute/src/layout/tree.rs:485-487`):
```rust
let FieldsShape::Arbitrary { offsets, in_memory_order } = layout.fields() else {
    return Err(Err::NotYetSupported);
};
```
Because `core::num::NonZero<u8>` is a `#[repr(transparent)]` wrapper around an internal struct annotated with `#[rustc_layout_scalar_valid_range_start(1)]`, `rustc`'s layout engine assigns that struct `FieldsShape::Primitive` rather than `FieldsShape::Arbitrary`. When `Tree::from_ty` lowers either standalone `NonZero<u8>` or the `Some(NonZero<u8>)` variant of `Option<NonZero<u8>>`, `from_struct` -> `from_variant` hits line 486 and returns `Err(Err::NotYetSupported)`, surfacing `Reason::SrcIsNotYetSupported` or `Reason::DstIsNotYetSupported`. Notably, `Tree::nonzero(width_in_bytes: u64)` already exists in `tree.rs:117-129` with `#[allow(dead_code)]`, but is never wired into `Tree::from_ty`. Open PR `rust-lang/rust#148449` (still open as of `2026-11-22`) proposes handling `FieldsShape::Primitive` scalar-backed ADTs and `NonZero` ranges.

By contrast, `Option<bool>` uses `TagEncoding::Niche` over the *primitive* `ty::Bool` (which takes the `ty::Bool` arm of `from_ty`, never calling `from_variant` on `bool`), while `Option<bool>`'s own variants have `FieldsShape::Arbitrary`. Empirically (`support/probe_rustc_transmute_results.json`), `opt_bool_to_u8_nothing` and `u8_to_opt_bool_safety_validity` both **succeed** under both legacy and next solvers, whereas `nonzero_u8_to_u8_nothing`, `opt_nonzero_u8_to_u8_nothing`, and `u8_to_opt_nonzero_u8_safety` all **fail** with `analyzing the transmutability of ... is not yet supported`.

#### 1.3 `Def::has_safety_invariants` Pruning (All ADTs and `MaybeUninit<T>`)

In `compiler/rustc_transmute/src/layout/mod.rs:144-158` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; `:140-154` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
```rust
pub enum Def<'tcx> {
    Adt(ty::AdtDef<'tcx>),
    Variant(&'tcx ty::VariantDef),
    Field(&'tcx ty::FieldDef),
    Primitive,
}

impl<'tcx> super::Def for Def<'tcx> {
    fn has_safety_invariants(&self) -> bool {
        // Conservatively treat every ADT, variant, and field definition as
        // potentially carrying safety invariants. This check does not
        // inspect `unsafe` field annotations.
        self != &Self::Primitive
    }
}
```

In `MaybeTransmutableQuery<Tree<...>>::answer` (`maybe_transmutable/mod.rs:88-130`):
1. **Source definitions are always stripped:** `let src = src.prune(&|_def| false);` converts every `Tree::Def(_)` in `src` to `Tree::unit()` (`Seq([])`). Thus user ADTs in `src` position (`ZeroOrOne -> bool`, `Cell<u8> -> u8`, `MaybeUninit<u8> -> u8` under `Assume::VALIDITY`) never require `Assume::SAFETY`.
2. **Uninhabited destination check precedes pruning:** `if src.is_inhabited() && !dst.is_inhabited() { return Answer::No(Reason::DstUninhabited); }` (`mod.rs:96-98`). Therefore `u8 -> Void` returns `DstUninhabited` even if `Assume { alignment: true, lifetimes: true, safety: true, validity: true }`.
3. **Destination pruning when `!assume.safety`:** `dst.prune(&|def| def.has_safety_invariants())` converts every non-`Primitive` `Tree::Def` into `Tree::uninhabited()` (`Alt([])`), which annihilates its enclosing `Seq` (`tree.rs:162-173`). Because `from_struct`, `from_enum`, and `from_union` all prepend `Def::Adt(def)` (or `Def::Variant`), **every** ADT destination—including fieldless `#[repr(u8)] enum ZeroOrOne`, plain `#[repr(C)] struct PlainU8(u8)`, `#[repr(C, align(2))] struct PaddedAlign2(u8)`, and `core::mem::MaybeUninit<u8>` (a `#[repr(transparent)] union`)—prunes to `Tree::uninhabited()` and fails `Dfa::from_tree(dst)` with `Reason::DstMayHaveSafetyInvariants` (`mod.rs:124-127`). Only primitives, tuples of primitives, arrays of primitives, and references to primitives survive without `Assume::SAFETY`.
4. **Uninhabited source check:** `Dfa::from_tree(src)` returning `Err(layout::Uninhabited)` immediately yields `Answer::Yes` (`mod.rs:116-119`), so `Void -> u128` compiles with `Assume::NOTHING`.

#### 1.4 `Tree -> Dfa` Compilation Invariants (`layout/dfa.rs`)

`Dfa::from_tree` (`dfa.rs:104-124`) builds an acyclic automaton with a unique `start` and unique `accept` state:
- `Dfa::concat` (`dfa.rs:127-154`) merges `other.start` into `self.accept` (preserving identity on zero-sized `start == accept`).
- `Dfa::union` (`dfa.rs:157-255`) performs a lazy product-automaton construction over `(Option<State>, Option<State>)` pairs, mapping any pair where either component is accepting to a single `accept` state (`dfa.rs:170-178`). Crucially, when `src == accept`, the loop executes `continue;` (`dfa.rs:203-216`), **guaranteeing that `accept` has no outgoing transitions**—an invariant directly relied upon by our Lean formalization (`AcceptHasNoOutEdges`).

---

### 2. DFA Comparison, Union-Transmute Semantics, `Assume::VALIDITY` Quantifier Flip, `Answer::or` Quirk, and `IfAny`-as-`IfAll`

Basis: normative documentation + source + execution (`library/core/src/mem/transmutability.rs`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`, `compiler/rustc_type_ir/src/transmute.rs`, `compiler/rustc_next_trait_solver/src/solve/mod.rs`, `support/probe_rustc_transmute_results.json`)

#### 2.1 Union-Transmute Operational Definition

`core::mem::TransmuteFrom::transmute` (`library/core/src/mem/transmutability.rs:116-141`) is implemented directly as a `#[repr(C)]` union read:

```rust
#[repr(C)]
union Transmute<Src, Dst> {
    src: ManuallyDrop<Src>,
    dst: ManuallyDrop<Dst>,
}
let transmute = Transmute { src: ManuallyDrop::new(src) };
let dst = unsafe { transmute.dst };
ManuallyDrop::into_inner(dst)
```

Because `#[repr(C)]` places both fields at byte offset `0`, reading `transmute.dst` performs:
- **Prefix truncation** when `size_of::<Dst>() <= size_of::<Src>()`: trailing bytes `[size_of::<Dst>()..size_of::<Src>())` are discarded (e.g., `u32 -> u8`).
- **Trailing-uninit extension** when `size_of::<Src>() <= size_of::<Dst>()`: trailing bytes `[size_of::<Src>()..size_of::<Dst>())` in the union are uninitialized (`UNINIT = 256`), which is sound iff `Dst` permits uninitialized bytes at every tail offset (e.g., `u8 -> PaddedAlign2(u8)` where byte 1 is alignment padding).

Empirically (`support/probe_rustc_transmute_results.json`), Miri executes both operations cleanly with `rc = 0` and prints `EXT=66 TRUNC=0x44` (`PaddedAlign2(66)` extended from `66u8`, and `0x44u8` truncated from `0x11223344u32` on little-endian `x86_64`).

#### 2.2 Memoized DFA Comparison and `Assume::VALIDITY` Quantifier Flip

`MaybeTransmutableQuery<Dfa<...>>::answer_impl` (`compiler/rustc_transmute/src/maybe_transmutable/mod.rs:170-301` at `342d74463a`) memoizes over `(src_state, dst_state)` pairs in `answer_memo`:

1. **Prefix truncation (`mod.rs:180-185`):** `if dst_state == self.dst.accept { return Answer::Yes; }`. Once `dst` reaches its accept state, any remaining suffix of `src` is truncated unconditionally (`u32 -> u8` succeeds under `Assume::NOTHING`).
2. **Trailing-uninit extension (`mod.rs:186-192`):** `else if src_state == self.src.accept`: looks up `self.dst.get_uninit_edge_dst(dst_state)`. If `Some(dst_state_prime)`, recurses on `(src_state, dst_state_prime)`; otherwise returns `Answer::No(Reason::DstIsTooBig)`. Thus `u8 -> PaddedAlign2` (with `Assume::SAFETY`) succeeds because byte 1 of `PaddedAlign2` has `[0, 257)` containing `UNINIT = 256`, whereas `u8 -> u16` fails with `DstIsTooBig` because byte 1 of `u16` has `[0, 256)` lacking `UNINIT`.
3. **Quantifier selection (`mod.rs:194-203`):**
   - When `!self.assume.validity`: `src_quantifier = Quantifier::ForAll` (`Answer::Yes` identity, combines with `Answer::and`, short-circuits on `Answer::No`). Every byte range covered by `src` must have a matching `dst` transition whose successor pair succeeds; any `(Some(_), None)` slice yields `Answer::No(Reason::DstIsBitIncompatible)`. For equal-size byte-only types, this enforces language inclusion $L(\text{Src}) \subseteq L(\text{Dst})$.
   - When `self.assume.validity`: `src_quantifier = Quantifier::ThereExists` (`Answer::No(DstIsBitIncompatible)` identity, combines with `Answer::or`, short-circuits on `Answer::Yes`). At least one overlapping byte range `(Some(s'), Some(d'))` must lead to a compatible continuation. For equal-size byte-only types, this enforces **non-empty intersection** $L(\text{Src}) \cap L(\text{Dst}) \neq \emptyset$.
   - **Critical consequence:** `Assume::VALIDITY` does **not** disable validity checking. `u8 -> bool` (`[0..256) ∩ [0..2) = [0..2) ≠ ∅`), `u32 -> char`, and `MaybeUninit<u8> -> u8` succeed under `Assume::VALIDITY`, whereas `TwoOnly -> bool` (`{2} ∩ {0, 1} = ∅`) **still fails** with `error[E0277]` even under `Assume::VALIDITY`!
4. **Combining `bytes_answer` and `refs_answer` (`mod.rs:232-236, 295-299`):** Early returns exit on `Answer::No(_)` when `!assume.validity` and on `Answer::Yes` when `assume.validity`; otherwise the two answers combine via `bytes_answer.or(refs_answer)` (if `assume.validity`) or `bytes_answer.and(refs_answer)` (if `!assume.validity`).

#### 2.3 Non-Boolean `Answer::or` Quirk and Empirically Verified Variant-Order Asymmetry

In `compiler/rustc_type_ir/src/transmute.rs:102-131` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; previously `compiler/rustc_transmute/src/maybe_transmutable/mod.rs:350-374` at `14210df0e`):

```rust
/// Currently, combining `Yes` with `If` retains the condition. This differs
/// from Boolean disjunction, where unconditional success would suffice.
pub fn or(self, rhs: Answer<R, T>) -> Answer<R, T> {
    let lhs = self;
    match (lhs, rhs) {
        (Answer::No(Reason::DstIsBitIncompatible), Answer::No(reason))
        | (Answer::No(reason), Answer::No(_)) => Answer::No(reason),
        (Answer::No(_), other) | (other, Answer::No(_)) => other.or(Answer::Yes),
        (Answer::Yes, other) | (other, Answer::Yes) => other,
        ...
    }
}
```

Look at the interaction between `Answer::or` and `Quantifier::ThereExists.apply` (`maybe_transmutable/mod.rs:321-329`):
- `ThereExists` folds from `accum = Answer::No(DstIsBitIncompatible)` using `accum.or(next)`, and breaks early **only when `accum.or(next)` is `Answer::Yes`**.
- Suppose an enum under `Assume::SAFETY.and(Assume::VALIDITY)` has two variants: one variant matching a reference pair that emits an unsatisfied `Answer::If(Immutable(Cell<u8>))`, and another variant matching a pure byte pair (`u8 -> u8`) that returns `Answer::Yes`:
  - **Ref arm at discriminant `0`, byte arm at discriminant `1` (`SrcMixRefFirst -> DstMixRefFirst`):**
    1. Iteration 0 (`tag = 0`): `No.or(If(c))` -> `If(c).or(Yes)` -> `If(c)` (does not break).
    2. Iteration 1 (`tag = 1`): `If(c).or(Yes)` -> **`If(c)`** (fails Boolean absorption `If(c) ∨ Yes = Yes`!).
    3. Final result: `Answer::If(Immutable(Cell<u8>))` -> **compilation fails** (`UnsafeCell<u8>: Freeze` is not satisfied).
  - **Byte arm at discriminant `0`, ref arm at discriminant `1` (`SrcMixByteFirst -> DstMixByteFirst`):**
    1. Iteration 0 (`tag = 0`): `No.or(Yes)` -> `Yes.or(Yes)` -> **`Yes`** -> immediately `Break(Answer::Yes)`!
    2. Final result: `Answer::Yes` -> **compilation succeeds** (even on `1.98.0-nightly -Z next-solver=globally`, because `Answer::Yes` bypasses `Answer::If`!).

Both outcomes were empirically confirmed in `support/probe_rustc_transmute_results.json` (`answer_or_ref_first_safety_validity`: `legacy=False, next=False`; `answer_or_byte_first_safety_validity`: `legacy=True, next=True`) and proved in Lean (`upstream_answer_or_order_asymmetry`).

#### 2.4 `flatten_answer_tree` Flattens `Condition::IfAny` as Conjunction (`IfAll`)

In `compiler/rustc_next_trait_solver/src/solve/mod.rs:446-481` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), invoked by **both** the legacy solver (`confirmation.rs:302`) and the next solver (`trait_goals.rs:727`):

```rust
pub fn flatten_answer_tree<I: Interner>(
    interner: I,
    predicate: TraitClause<I>,
    cond: Condition<Region<I>, I::Ty>,
) -> ThinVec<I::Predicate> {
    match cond {
        // FIXME(bryangarza): Add separate `IfAny` case, instead of treating as `IfAll`
        // Not possible until the trait solver supports disjunctions of obligations
        Condition::IfAll(conds) | Condition::IfAny(conds) => conds
            .into_iter()
            .flat_map(|cond| flatten_answer_tree(interner, predicate, cond))
            .collect(),
        Condition::Immutable { ty } => { /* ty: Freeze */ }
        Condition::Outlives { long, short } => { /* long: short */ }
        Condition::Transmutable { src, dst } => { /* dst: TransmuteFrom<src, ASSUME> */ }
    }
}
```

Because `Condition::IfAny` is flattened conjunctively, whenever a destination DFA has multiple reference transitions from the same state—for example, `#[repr(C)] union DstRefUnion<'a> { good: &'a u8, bad: &'a Cell<u8> }`—`Quantifier::ThereExists` over `dst.refs_from(dst_state)` builds `Condition::IfAny([good_cond, bad_cond])`, and the trait solver demands **both** `u8: Freeze` and `Cell<u8>: Freeze`. Empirically (`ifany_as_ifall_ref_union_safety`), transmuting `&'a u8 -> DstRefUnion<'a>` with `Assume::SAFETY` is rejected with `error[E0277]: the trait bound UnsafeCell<u8>: Freeze is not satisfied in Cell<u8>`, even though the `good: &'a u8` union variant is an identity match. This is an over-conservative incompleteness (never an unsoundness).

---

### 3. Reference Transmutability, Coinduction, Solver Evolution, and Live Soundness Defect `rust-lang/rust#164247`

Basis: source + execution + derived (`compiler/rustc_transmute/src/maybe_transmutable/mod.rs`, `compiler/rustc_trait_selection/src/solve/delegate.rs`, `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs`, `rust-lang/rust#164247`, `support/probe_rustc_transmute_results.json`)

#### 3.1 Reference Transition Rules and Coinduction

For every `(src_ref, src_state_prime)` in `src.refs_from(src_state)` and `(dst_ref, dst_state_prime)` in `dst.refs_from(dst_state)` (`maybe_transmutable/mod.rs:238-293` at `342d74463a`; `:257-312` at `14210df0e`):

1. **Uniqueness guard (`mod.rs:244-245`):** `if !src_ref.is_mut && dst_ref.is_mut => Answer::No(Reason::DstIsMoreUnique)`. Rejects `&T -> &mut U` regardless of `Assume` flags. Note that `&mut T -> &U` (`src_ref.is_mut && !dst_ref.is_mut`) passes this guard.
2. **Alignment guard (`mod.rs:246-252`):** `if !self.assume.alignment && src_ref.referent_align < dst_ref.referent_align => Answer::No(Reason::DstHasStricterAlignment { ... })`. Bypassed by `Assume::ALIGNMENT` (e.g., `&[u8; 2] -> &u16` fails under `Assume::NOTHING` and succeeds under `Assume::ALIGNMENT`).
3. **Referent size guard (`mod.rs:253-259`):** `if dst_ref.referent_size > src_ref.referent_size => Answer::No(Reason::DstRefIsTooBig { ... })`. Unlike by-value union transmutation, reference transmutation forbids extending behind a pointer even into trailing padding (`&u8 -> &PaddedAlign2` cannot read out-of-bounds byte 1 behind the pointer); prefix truncation (`dst_ref.referent_size <= src_ref.referent_size`, e.g., `&u32 -> &u8`) is allowed for shared references.
4. **Generated nested obligations (`mod.rs:261-289`):**
   ```rust
   let mut conditions = Vec::with_capacity(4);
   let mut is_transmutable = |src: Reference<_, _>, dst: Reference<_, _>| {
       conditions.push(Condition::Transmutable { src: src.referent, dst: dst.referent });
       if !self.assume.lifetimes {
           conditions.push(Condition::Outlives { long: src.region, short: dst.region });
       }
   };

   is_transmutable(src_ref, dst_ref);

   if dst_ref.is_mut {
       is_transmutable(dst_ref, src_ref);
   } else {
       conditions.push(Condition::Immutable { ty: dst_ref.referent });
   }

   Answer::If(Condition::IfAll(conditions)).and(self.answer_memo(cache, src_state_prime, dst_state_prime))
   ```
   - **Forward obligation:** `dst_ref.referent: TransmuteFrom<src_ref.referent, ASSUME>` (inheriting the outer `ASSUME` const parameter in `flatten_answer_tree`, `next_trait_solver/src/solve/mod.rs:472-476`), plus `src_ref.region: dst_ref.region` unless `Assume::LIFETIMES` is set (`&'static u8 -> &'a u8` succeeds; `&'a u8 -> &'static u8` fails with `lifetime may not live long enough` unless `Assume::LIFETIMES`).
   - **Bidirectional `&mut` obligation (`if dst_ref.is_mut`):** Emits the reverse `Transmutable { src: dst_ref.referent, dst: src_ref.referent }` and reverse `Outlives { long: dst_ref.region, short: src_ref.region }` (invariant lifetime!). Consequently, `&mut u32 -> &mut u8` fails because the reverse `u8 -> u32` check fails (`DstIsTooBig`), and `&mut Cell<u8> -> &mut u8` requires `Assume::SAFETY` because the reverse `u8 -> Cell<u8>` places `Cell<u8>` in `dst` position (`Def::Adt(Cell)`).
   - **Coinduction for recursive references (`#[rustc_coinductive]`):** Because `TransmuteFrom` carries `#[rustc_coinductive]` (`library/core/src/mem/transmutability.rs:90`), cyclic obligations such as `&'a NodeA<'a> -> &'a NodeB<'a>` (where `struct NodeA<'a> { next: &'a NodeA<'a>, val: u8 }` and `struct NodeB<'a> { next: &'a NodeB<'a>, val: u8 }`) succeed via coinductive cycle acceptance under `Assume::SAFETY` (`coinductive_node_a_to_node_b_safety`).

#### 3.2 Legacy vs. `-Z next-solver=globally` Solver Evolution (`1.98.0-nightly` vs. `1.102.0-nightly` / `HEAD`)

Comparing our live execution on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) against `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and `HEAD` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) uncovered an exact version transition:
- **At `14210df0e` (`2026-05-31`, `1.98.0-nightly`):** In `compiler/rustc_trait_selection/src/solve/delegate.rs:363-382`, `SolverDelegate::is_transmutable` returned `Result<Certainty, NoSolution>` and explicitly rejected all `Answer::If(_)` outcomes:
  ```rust
  match rustc_transmute::TransmuteTypeEnv::new(self.0.tcx).is_transmutable(src, dst, assume) {
      rustc_transmute::Answer::Yes => Ok(Certainty::Yes),
      rustc_transmute::Answer::No(_) | rustc_transmute::Answer::If(_) => Err(NoSolution),
  }
  ```
  Consequently, on `1.98.0-nightly`, `-Z next-solver=globally` diverged from the legacy solver on **11 of 38 core cases** (every reference case that succeeded in legacy, plus `ref_mut_u8_to_ref_mut_cell_u8_safety` in the extended suite), because every reference transition produces `Answer::If(Condition::IfAll(...))`.
- **At `cee2a0ddf022ee393e384ff576c6a190915f19a1` (`2026-10-12`, PR `#163946`, including `5b216e01a117532b30f061f3dff8a61408113c77`):** `Answer`, `Condition`, and `Reason` were lifted into `rustc_type_ir::transmute`, and `consider_builtin_transmute_candidate` in `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:714-734` was updated to call `flatten_answer_tree(tcx, goal.predicate, cond)` and register nested goals—matching legacy `confirm_transmutability_candidate` (`confirmation.rs:298-314`).
- **From `cee2a0ddf0` onward (`1.102.0-nightly` `3ef0c22cd` and `HEAD` `342d74463a`):** Legacy and `-Z next-solver=globally` achieve **38/38 parity (0 divergences)**, which simultaneously propagated the `#164247` soundness defect into `-Z next-solver=globally`.

#### 3.3 Forensic Dissection of Live Soundness Defect `rust-lang/rust#164247`

Open issue `rust-lang/rust#164247` (filed `2026-10-13`, labeled `I-unsound`, `C-bug`, `F-transmutability`, `T-compiler`, `T-libs`; still open at `HEAD 342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) arises directly from lines 278-282 of `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`:

```rust
if dst_ref.is_mut {
    is_transmutable(dst_ref, src_ref);
} else {
    conditions.push(Condition::Immutable { ty: dst_ref.referent });
}
```

Trace of `<&u8 as TransmuteFrom<&Cell<u8>, { Assume::NOTHING }>>::transmute(&cell)`:
1. Outer query: `src = &'a Cell<u8>`, `dst = &'a u8`, `assume = Assume::NOTHING`.
2. Neither `src_ref` nor `dst_ref` is mutable (`!src_ref.is_mut && !dst_ref.is_mut`), alignments are both `1`, sizes are both `1`.
3. Lines 276-282 emit `IfAll([Transmutable { src: Cell<u8>, dst: u8 }, Outlives { 'a, 'a }, Immutable { ty: u8 }])`. **No `Condition::Immutable { ty: Cell<u8> }` is emitted.**
4. `u8: Freeze` holds; `'a: 'a` holds; and the nested query `u8: TransmuteFrom<Cell<u8>, { Assume::NOTHING }>` builds `Tree` for `Cell<u8>` (`Seq([Def(Adt(Cell)), Def(Adt(UnsafeCell)), Byte(0..256)])`), strips all `Def` nodes from `src` (`src.prune(&|_def| false)`), leaves primitive `u8` (`Byte(0..256)`) intact on `dst`, and returns `Answer::Yes`!
5. By contrast, `&u8 -> &Cell<u8>`, `&mut u8 -> &Cell<u8>`, and even the identity `&Cell<u8> -> &Cell<u8>` are all **rejected even with `Assume::SAFETY`** because `dst_ref.referent = Cell<u8>` fails `Condition::Immutable { ty: Cell<u8> }` (`UnsafeCell<u8>: Freeze` is not implemented).

**Empirical miscompilation on native silicon (`support/probe_rustc_transmute_results.json`):**
Running `observe_alias(&cell, ro)` where `let ro: &u8 = unsafe { <&u8 as TransmuteFrom<&Cell<u8>, { Assume::NOTHING }>>::transmute(&cell) };` reads `before = *ro`, calls `cell.set(99)`, and reads `after = *ro`:
- **`-Copt-level=0`:** `BEFORE=7 AFTER=99 CELL=99` (`compile_rc = 0, run_rc = 0`).
- **`-Copt-level=2`:** `BEFORE=7 AFTER=7 CELL=99` (`compile_rc = 0, run_rc = 0`) — silent miscompilation where `*ro` returns the stale cached value `7` even though `cell.get() == 99`.
- **Direct LLVM IR causal proof (`rustc -Copt-level=2 --emit=llvm-ir`):**
  ```llvm
  define internal fastcc noundef range(i24 6488064, 6553600) i24
    @_RNvCsgfC7Vt8Orkn_14repro164247_ir13observe_alias(
      ptr noundef nonnull writeonly captures(none) initializes((0, 1)) %cell,
      ptr noalias noundef nonnull readonly captures(none) dereferenceable(1) %ro
    ) unnamed_addr #3
  ```
  Because `u8: Freeze`, `rustc` emits **`noalias`** and **`readonly`** on `%ro` (while omitting `noalias` on `%cell` because `Cell<u8>` contains `UnsafeCell`), licensing LLVM to hoist/reuse the load `*ro` across `cell.set(99)`.
- **Miri Undefined Behavior (all four configurations exit `rc = 1`):**
  - *Stacked Borrows (protected `observe_alias` boundary):* faults at `cell.set(99)` with `Undefined Behavior: not granting access to tag <353> because that would remove [SharedReadOnly for <346>] which is strongly protected`.
  - *Tree Borrows (protected `observe_alias` boundary):* faults at `cell.set(99)` with `Undefined Behavior: write access through <341> at alloc158[0x0] is forbidden ... this foreign write access would cause the protected tag <331> (currently Frozen) to become Disabled`.
  - *Stacked Borrows (unprotected inline `main`):* faults at the second `*ro` read with `Undefined Behavior: attempting a read access using <341> at alloc158[0x0], but that tag does not exist in the borrow stack for this location`.
  - *Tree Borrows (unprotected inline `main`):* faults at the second `*ro` read with `Undefined Behavior: read access through <326> at alloc158[0x0] is forbidden`.

#### 3.4 Exact Interior-Mutability Repair Rule and Precision Boundary

What is the minimal sound condition on `src_ref`?
- **Shared-to-shared (`!src_ref.is_mut && !dst_ref.is_mut`):** Because `&Src` implements `Copy`, the caller retains a live copy of the source reference alongside `dst: &Dst`. If `Src` contains interior mutability (`!Src: Freeze`) overlapping `[0, size_of::<Dst>())`, safe code can mutate the pointee through `src` while `dst: &Dst` asserts `SharedReadOnly` / `Frozen` / LLVM `noalias readonly`. Adding:
  ```rust
  if !src_ref.is_mut {
      conditions.push(Condition::Immutable { ty: src_ref.referent });
  }
  ```
  inside the `else` (`!dst_ref.is_mut`) branch closes `#164247` completely (rejecting `&Cell<u8> -> &u8`, `&UnsafeCell<u8> -> &u8`, and `&CellFirst(Cell<u8>, u8) -> &u8`).
- **Unique-to-shared (`src_ref.is_mut && !dst_ref.is_mut`, e.g., `&mut Cell<u8> -> &u8`):** Consuming a unique `&mut Cell<u8>` by value into `TransmuteFrom::transmute` leaves no surviving alias capable of mutating the cell during `'a`. Empirically, `mut_cell_to_ref_sb` and `mut_cell_to_ref_tb` both pass Miri with `rc = 0` (`MUT_CELL_TO_REF=42`), and `repaired_ref_allows_mut_cell_to_shared_ro` confirms the repaired rule retains this conversion (note, however, the open UCG discussion `rust-lang/unsafe-code-guidelines#592` cited in `#164247` comments regarding whether creating `&T` from `&mut T` via transmute rather than reborrow could ever be restricted by future operational-semantics decisions; see **Boundaries**).
- **Type-level `Freeze` vs. byte-offset `visit_freeze_sensitive` precision boundary:** Empirically in Miri:
  - `#[repr(C)] struct CellFirst(Cell<u8>, u8)`: transmuting `&CellFirst -> &u8` (`Assume::NOTHING`) aliases byte `0` (`Cell<u8>`), faulting UB (`rc = 1`) in both Stacked Borrows and Tree Borrows when `s.0.set(99)` runs between reads of `*ro`.
  - `#[repr(C)] struct CellSecond(u8, Cell<u8>)`: transmuting `&CellSecond -> &u8` (`Assume::NOTHING`) covers only byte `[0..1)`, which is frozen under `visit_freeze_sensitive`, while `Cell<u8>` occupies byte `[1..2)`. Mutating `s.1.set(99)` between reads of `*ro` **passes** both Stacked Borrows and Tree Borrows (`rc = 0`, `CELL_SECOND B=7 A=7 CELL=99`).
  - Therefore, requiring `Condition::Immutable { ty: src_ref.referent }` (`Src: Freeze`) is **sound** (sufficient) for all shared-to-shared reference transmutes, and conservatively rejects prefix-truncating transmutes like `&CellSecond -> &u8` whose `UnsafeCell` lies strictly beyond `size_of::<Dst>()`.

---

### 4. Complete Empirical `rustc` (Legacy & Next Solver) and Miri Matrix

Basis: execution (`support/probe_rustc_transmute.py`, `support/probe_rustc_transmute_results.json`, plus `1.102.0-nightly` comparison on `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`)

#### 4.1 Core 38-Case `TransmuteFrom<Src, ASSUME>` Matrix

| # | Case ID | Conversion & `Assume` | `1.98` Legacy | `1.98` Next | `1.102` Legacy | `1.102` Next | Primary Diagnostic / Mechanism |
| :-: | :--- | :--- | :-: | :-: | :-: | :-: | :--- |
| 1 | `bool_to_u8_nothing` | `bool -> u8` (`NOTHING`) | PASS | PASS | PASS | PASS | `[0, 2) ⊆ [0, 256)` |
| 2 | `u8_to_bool_nothing` | `u8 -> bool` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstIsBitIncompatible`: `2..256` not in `bool` |
| 3 | `u8_to_bool_validity` | `u8 -> bool` (`VALIDITY`) | PASS | PASS | PASS | PASS | `ThereExists`: `[0, 256) ∩ [0, 2) ≠ ∅` |
| 4 | `two_only_to_bool_validity` | `TwoOnly -> bool` (`VALIDITY`) | FAIL | FAIL | FAIL | FAIL | `ThereExists`: `{2} ∩ {0, 1} = ∅` |
| 5 | `zero_or_one_to_bool_nothing` | `ZeroOrOne -> bool` (`NOTHING`) | PASS | PASS | PASS | PASS | `src` `Def` stripped; `{0, 1} ⊆ {0, 1}` |
| 6 | `bool_to_zero_or_one_nothing` | `bool -> ZeroOrOne` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstMayHaveSafetyInvariants` (`Def::Adt`) |
| 7 | `bool_to_zero_or_one_safety` | `bool -> ZeroOrOne` (`SAFETY`) | PASS | PASS | PASS | PASS | Pruning skipped; `{0, 1} ⊆ {0, 1}` |
| 8 | `u32_to_u8_prefix_trunc_nothing` | `u32 -> u8` (`NOTHING`) | PASS | PASS | PASS | PASS | Union prefix truncation (`dst_state == accept`) |
| 9 | `u8_to_u16_too_big_nothing` | `u8 -> u16` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstIsTooBig`: byte 1 lacks `UNINIT` |
| 10 | `u8_to_padded_align2_safety` | `u8 -> PaddedAlign2` (`SAFETY`) | PASS | PASS | PASS | PASS | Trailing-uninit extension (`get_uninit_edge_dst`) |
| 11 | `u8_to_padded_align2_nothing` | `u8 -> PaddedAlign2` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstMayHaveSafetyInvariants` |
| 12 | `has_pad_to_u8_arr4_nothing` | `HasPad -> [u8; 4]` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstIsBitIncompatible`: pad `UNINIT` in `src` |
| 13 | `has_pad_to_mu_arr4_nothing` | `HasPad -> [MaybeUninit<u8>; 4]` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstMayHaveSafetyInvariants` (`MaybeUninit` ADT) |
| 14 | `has_pad_to_mu_arr4_safety` | `HasPad -> [MaybeUninit<u8>; 4]` (`SAFETY`) | PASS | PASS | PASS | PASS | `[0, 257) ⊆ [0, 257)` after `Assume::SAFETY` |
| 15 | `u8_to_plain_struct_nothing` | `u8 -> PlainU8` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstMayHaveSafetyInvariants` |
| 16 | `u8_to_plain_struct_safety` | `u8 -> PlainU8` (`SAFETY`) | PASS | PASS | PASS | PASS | `Def::Adt` retained under `Assume::SAFETY` |
| 17 | `opt_nonzero_u8_to_u8_nothing` | `Option<NonZero<u8>> -> u8` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `SrcIsNotYetSupported` (`FieldsShape::Primitive`, `#148449`) |
| 18 | `u8_to_opt_nonzero_u8_safety` | `u8 -> Option<NonZero<u8>>` (`SAFETY`) | FAIL | FAIL | FAIL | FAIL | `DstIsNotYetSupported` (`FieldsShape::Primitive`, `#148449`) |
| 19 | `void_to_u128_nothing` | `Void -> u128` (`NOTHING`) | PASS | PASS | PASS | PASS | Uninhabited `src` -> vacuous `Answer::Yes` |
| 20 | `u8_to_void_all_assumes` | `u8 -> Void` (all 4 `Assume`s `true`) | FAIL | FAIL | FAIL | FAIL | `DstUninhabited` (checked before pruning) |
| 21 | `ref_bool_to_ref_u8_nothing` | `&'a bool -> &'a u8` (`NOTHING`) | PASS | FAIL* | PASS | PASS | Valid shared ref; *`1.98` next-solver drops `Answer::If` |
| 22 | `ref_u8_to_ref_mut_u8_nothing` | `&'a u8 -> &'a mut u8` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstIsMoreUnique` |
| 23 | `ref_mut_u8_to_ref_u8_nothing` | `&'a mut u8 -> &'a u8` (`NOTHING`) | PASS | FAIL* | PASS | PASS | Unique-to-shared allowed; *`1.98` next-solver stub |
| 24 | `ref_mut_u32_to_ref_mut_u8_nothing` | `&'a mut u32 -> &'a mut u8` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | Reverse `u8 -> u32` fails (`DstIsTooBig`) |
| 25 | `ref_u32_to_ref_u8_nothing` | `&'a u32 -> &'a u8` (`NOTHING`) | PASS | FAIL* | PASS | PASS | Shared prefix truncation (`dst_size <= src_size`) |
| 26 | `ref_u8_arr2_to_ref_u16_nothing` | `&'a [u8; 2] -> &'a u16` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `DstHasStricterAlignment` (`1 < 2`) |
| 27 | `ref_u8_arr2_to_ref_u16_align` | `&'a [u8; 2] -> &'a u16` (`ALIGNMENT`) | PASS | FAIL* | PASS | PASS | Alignment guard bypassed by `Assume::ALIGNMENT` |
| 28 | `ref_static_to_ref_a_nothing` | `&'static u8 -> &'a u8` (`NOTHING`) | PASS | FAIL* | PASS | PASS | `'static: 'a` holds |
| 29 | `ref_a_to_ref_static_nothing` | `&'a u8 -> &'static u8` (`NOTHING`) | FAIL | FAIL | FAIL | FAIL | `Outlives` fails (`'a` must outlive `'static`) |
| 30 | `ref_a_to_ref_static_lifetimes` | `&'a u8 -> &'static u8` (`LIFETIMES`) | PASS | FAIL* | PASS | PASS | `Outlives` omitted under `Assume::LIFETIMES` |
| 31 | `ref_u8_to_ref_cell_u8_safety` | `&'a u8 -> &'a Cell<u8>` (`SAFETY`) | FAIL | FAIL | FAIL | FAIL | `Condition::Immutable { ty: Cell<u8> }` (`!Freeze`) |
| 32 | `ref_cell_u8_to_ref_u8_nothing` | `&'a Cell<u8> -> &'a u8` (`NOTHING`) | **PASS** | FAIL* | **PASS** | **PASS** | **BUG `#164247`:** missing `src` `Freeze` check |
| 33 | `ref_cell_u8_to_ref_cell_u8_safety` | `&'a Cell<u8> -> &'a Cell<u8>` (`SAFETY`) | FAIL | FAIL | FAIL | FAIL | `Condition::Immutable { ty: Cell<u8> }` (`!Freeze`) |
| 34 | `ref_mut_cell_u8_to_ref_u8_nothing` | `&'a mut Cell<u8> -> &'a u8` (`NOTHING`) | PASS | FAIL* | PASS | PASS | Consumed `&mut` + `u8: Freeze` |
| 35 | `ref_mut_u8_to_ref_cell_u8_safety` | `&'a mut u8 -> &'a Cell<u8>` (`SAFETY`) | FAIL | FAIL | FAIL | FAIL | `Condition::Immutable { ty: Cell<u8> }` (`!Freeze`) |
| 36 | `ref_unsafecell_u8_to_ref_u8_nothing` | `&'a UnsafeCell<u8> -> &'a u8` (`NOTHING`) | **PASS** | FAIL* | **PASS** | **PASS** | **BUG `#164247`:** missing `src` `Freeze` check |
| 37 | `ref_mut_cell_u8_to_ref_mut_u8_safety` | `&'a mut Cell<u8> -> &'a mut u8` (`SAFETY`) | PASS | FAIL* | PASS | PASS | Bidirectional (`u8 -> Cell<u8>` needs `SAFETY`) |
| 38 | `coinductive_node_a_to_node_b_safety` | `&'a NodeA<'a> -> &'a NodeB<'a>` (`SAFETY`) | PASS | FAIL* | PASS | PASS | `#[rustc_coinductive]` cyclic ref transmutability |

*\*All 11 `FAIL*` cells in `1.98` Next are caused identically by `delegate.rs:380` (`Answer::If(_) => Err(NoSolution)`), fixed in `cee2a0ddf022ee393e384ff576c6a190915f19a1` (`2026-10-12`, PR `#163946`).*

#### 4.2 Extended 14-Case Diagnostic Matrix (`rustc 1.98.0-nightly`, `14210df0e`)

| # | Case ID | Conversion & `Assume` | Legacy | Next | Observed Diagnostic / Mechanism |
| :-: | :--- | :--- | :-: | :-: | :--- |
| 1 | `nonzero_u8_to_u8_nothing` | `NonZero<u8> -> u8` (`NOTHING`) | FAIL | FAIL | `analyzing the transmutability of NonZero<u8> is not yet supported` (`FieldsShape::Primitive`) |
| 2 | `opt_bool_to_u8_nothing` | `Option<bool> -> u8` (`NOTHING`) | PASS | PASS | `TagEncoding::Niche` over primitive `bool` works |
| 3 | `u8_to_opt_bool_safety_validity` | `u8 -> Option<bool>` (`SAFETY \| VALIDITY`) | PASS | PASS | Niche enum destination succeeds with `SAFETY \| VALIDITY` |
| 4 | `u8_to_mu_u8_nothing` | `u8 -> MaybeUninit<u8>` (`NOTHING`) | FAIL | FAIL | `MaybeUninit<u8> may carry safety invariants` |
| 5 | `u8_to_mu_u8_safety` | `u8 -> MaybeUninit<u8>` (`SAFETY`) | PASS | PASS | `[0, 256) ⊆ [0, 257)` after `Assume::SAFETY` |
| 6 | `mu_u8_to_u8_nothing` | `MaybeUninit<u8> -> u8` (`NOTHING`) | FAIL | FAIL | `UNINIT = 256` not in `[0, 256)` |
| 7 | `mu_u8_to_u8_validity` | `MaybeUninit<u8> -> u8` (`VALIDITY`) | PASS | PASS | `[0, 257) ∩ [0, 256) ≠ ∅` |
| 8 | `char_to_u32_nothing` | `char -> u32` (`NOTHING`) | PASS | PASS | 3-branch UTF-32 scalar `Alt` included in `[0, 256)^4` |
| 9 | `u32_to_char_nothing` | `u32 -> char` (`NOTHING`) | FAIL | FAIL | Surrogates / `> 0x10FFFF` rejected by `ForAll` |
| 10 | `u32_to_char_validity` | `u32 -> char` (`VALIDITY`) | PASS | PASS | Non-empty intersection with valid scalar values |
| 11 | `ref_mut_u8_to_ref_mut_cell_u8_safety` | `&'a mut u8 -> &'a mut Cell<u8>` (`SAFETY`) | PASS | FAIL* | `dst_ref.is_mut == true` skips `Freeze`; bidirectional needs `SAFETY` |
| 12 | `ifany_as_ifall_ref_union_safety` | `&'a u8 -> DstRefUnion<'a>` (`SAFETY`) | FAIL | FAIL | `UnsafeCell<u8>: Freeze` unsatisfied (`IfAny` flattened as `IfAll`) |
| 13 | `answer_or_ref_first_safety_validity` | `SrcMixRefFirst -> DstMixRefFirst` (`SAFETY \| VALIDITY`) | FAIL | FAIL | `If(c).or(Yes) = If(c)` retains `Cell<u8>: Freeze` |
| 14 | `answer_or_byte_first_safety_validity` | `SrcMixByteFirst -> DstMixByteFirst` (`SAFETY \| VALIDITY`) | PASS | PASS | Swapping tags `0`/`1` breaks on `Yes` before inspecting `RefArm` |

#### 4.3 Runtime Execution Matrix (Native `-O0`/`-O2` and Miri Stacked/Tree Borrows)

| Probe | Mode | Exit Code | Observed Output / Diagnostic |
| :--- | :--- | :-: | :--- |
| Union transmute (`u8 -> PaddedAlign2`, `u32 -> u8`) | Miri (Stacked Borrows) | `0` | `EXT=66 TRUNC=0x44` |
| `#164247` (`&Cell<u8> -> &u8`, `observe_alias`) | Native `-Copt-level=0` | `0` | `BEFORE=7 AFTER=99 CELL=99` |
| `#164247` (`&Cell<u8> -> &u8`, `observe_alias`) | Native `-Copt-level=2` | `0` | `BEFORE=7 AFTER=7 CELL=99` (LLVM `noalias readonly` miscompile) |
| `#164247` (`&Cell<u8> -> &u8`, protected `observe_alias`) | Miri Stacked Borrows | `1` | UB at `cell.set(99)`: strongly protected `SharedReadOnly` tag |
| `#164247` (`&Cell<u8> -> &u8`, protected `observe_alias`) | Miri Tree Borrows | `1` | UB at `cell.set(99)`: foreign write disables protected `Frozen` tag |
| `#164247` (`&Cell<u8> -> &u8`, unprotected `main`) | Miri Stacked Borrows | `1` | UB at second `*ro`: tag missing from borrow stack |
| `#164247` (`&Cell<u8> -> &u8`, unprotected `main`) | Miri Tree Borrows | `1` | UB at second `*ro`: read access through `Disabled` tag forbidden |
| `&mut Cell<u8> -> &u8` (`Assume::NOTHING`) | Miri SB & Miri TB | `0` / `0` | `MUT_CELL_TO_REF=42` (clean in both models) |
| `&CellFirst(Cell<u8>, u8) -> &u8` (`Assume::NOTHING`) | Miri SB & Miri TB | `1` / `1` | UB at second `*ro` (aliasing byte `0` interior-mutable `Cell`) |
| `&CellSecond(u8, Cell<u8>) -> &u8` (`Assume::NOTHING`) | Miri SB & Miri TB | `0` / `0` | `CELL_SECOND B=7 A=7 CELL=99` (`Cell` at byte `1` outside `&u8`) |

---

### 5. Implications for Anneal's Trusted Boundary and Verified `rustc` Compilation

Basis: source + derived (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`)

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes four concrete interface constraints between `rustc_transmute` and a verified Rust MIR/compiler trusted computing base:

1. **Current Fail-Closed Status in Anneal (`MirAst.lean:312-321, 596-628`):**
   - `Trusted.MirTy` admits only `.bool`, `.int`, `.unit`, `.never`, admitted fieldless `.enum`, `.tuple`, `.ref`, and `.rawPtr`; structs, unions, arrays, `UnsafeCell`, `char`, and floats lower fail-closed to `.unsupported`.
   - `Trusted.Rvalue` admits only `.use`, `.binaryOp`, `.unaryOp`, `.discriminant`, `.ref`, `.addressOf`, and `.aggregateTuple`; `Rvalue::Cast` (including `CastKind::Transmute`) and `Aggregate(AggregateKind::Adt, ...)` (structs and unions) lower fail-closed to `.unsupported`.
   - Retagging `Rvalue::Use(_, WithRetag::Yes)` on any reference-containing type lowers fail-closed to `.unsupported` (`MirAst.lean:596-597`), and moving any non-ZST local unconditionally deinitializes the source place (`deinitMovedPlace = true`, `MirSemantics.lean:949-976`).
2. **Byte Alphabet Alignment vs. Provenance Gap (`MirSemantics.lean:422-424`):** `Trusted.AllocByte` (`| uninit | init (byte : UInt8) (prov : Option AllocId := none)`) refines `rustc_transmute`'s 257-symbol `Byte` alphabet (`0..=255 | UNINIT`) by attaching optional allocation provenance `Option AllocId`. A verified compiler or MIR semantics lifting `rustc_transmute` must not collapse provenance-bearing pointer bytes into raw `0..=255` integer bytes without separately tracking provenance stripping (e.g., CTFE forbids pointer provenance inside integer values).
3. **Hard Prohibition Against Importing Unrepaired `rustc` `TransmuteFrom` as a Trusted Oracle:** Because `rustc` accepts `<&u8 as TransmuteFrom<&Cell<u8>, { Assume::NOTHING }>>::transmute` across both legacy and `-Z next-solver=globally` (`#164247`), treating `rustc`'s `TransmuteFrom` trait-solver discharge as a trusted soundness axiom inside a verified MIR-to-LLVM or verified-optimizer pipeline would silently license LLVM `noalias readonly` miscompilations (`BEFORE=7 AFTER=7` vs `99`) and Stacked/Tree Borrows UB. Any verified transmutability checker MUST enforce the repaired rule (`!src_ref.is_mut && !dst_ref.is_mut -> Src: Freeze ∧ Dst: Freeze`, or a verified byte-range `visit_freeze_sensitive` check over `[0, size_of::<Dst>())`).
4. **Explicit Distinction Between Union-Transmute and Equal-Size `CastKind::Transmute`:** `TransmuteFrom::transmute` lowers to a `#[repr(C)]` union write/read (permitting prefix truncation and trailing-uninit padding extension), whereas MIR `CastKind::Transmute` requires equal sizes and resets destination/source padding bytes to `uninit` (`copy_op_allow_transmute` / `validate_place` with `reset_provenance_and_padding = true`). Verified lowering passes must keep these two operational contracts strictly separate.

---

### 6. Kernel-Checked `Lean v4.34.1` Formalization (`support/RustcTransmuteDfaAndRefSoundness.lean`)

Basis: mechanized proof (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `support/RustcTransmuteDfaAndRefSoundness.lean`, 1,097 lines)

`support/RustcTransmuteDfaAndRefSoundness.lean` is a standalone, Core-Lean-only, purely constructive formalization verified with:
```console
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/RustcTransmuteDfaAndRefSoundness.lean
```
It contains **0** `sorry`, **0** `Classical.choice`, **0** `omega`, **0** `bv_decide`, **0** `native_decide`, **0** `partial def`, and **0** `._unsafe_rec`. Every exported theorem depends at most on `[propext, Quot.sound]` (with concrete counterexamples and positive controls depending on zero axioms or `[propext]`).

#### 6.1 Core Definitions Modeled in Lean

- **257-Symbol Byte Alphabet & Trees:** `abbrev ByteSym := Fin 257`, `def uninitSym : ByteSym := ⟨256, by decide⟩`, `ByteRange` (`start`, `stop`, `contains`, `uninit := ⟨0, 257⟩`, `anyInit := ⟨0, 256⟩`, `boolRange := ⟨0, 2⟩`, `exact`), constructive enumeration `allBytes : List ByteSym` with `mem_allBytes`, `DefKind` (`adt | variant | field | primitive`), `DefKind.hasSafetyInvariants` (`primitive => false`, all others `true`), and `LayoutTree` with total mutual `LayoutTree.prune`.
- **Byte-Level DFA & Union-Transmute Checker:** `ByteDfa` (`start`, `accept`, `step : Nat → ByteSym → Option Nat`), computable `ByteDfa.acceptsFrom` / `accepts`, `getUninitEdgeDst`, structural invariants `AcceptHasNoOutEdges`, `FixedLen`, `Reachable`, `LiveFrom`, relational union-transmute compatibility:
  ```lean
  def UnionTransmuteCompat (dst : ByteDfa) (wSrc : List ByteSym) : Prop :=
    ∃ wDst : List ByteSym,
      dst.accepts wDst = true ∧
        ((∃ tail : List ByteSym, wSrc = wDst ++ tail) ∨
         (∃ k : Nat, wDst = wSrc ++ List.replicate k uninitSym))
  ```
  and fuel-indexed recursive `dfaTransmute (src dst : ByteDfa) (assumeValidity : Bool) : Nat → Nat → Nat → Bool` mirroring `MaybeTransmutableQuery::answer_impl` (`sDst == dst.accept` -> `true`; `sSrc == src.accept` -> follow `getUninitEdgeDst`; otherwise `allBytes.any` for `assumeValidity = true` and `allBytes.all` for `assumeValidity = false`).
- **Reference Obligation Generator & Operational Read-Only Aliasing Model:** `RefSpec` (`isMut`, `isFreeze`, `align`, `size`), `AssumeOpts`, `RefObligations`, `refConditionsUpstream` (`reqSrcFreeze := false`), `refConditionsRepaired` (`reqSrcFreeze := !src.isMut && !dst.isMut`), `refDischarged`, post-transmute capabilities `HandleCap` (`consumed | sharedRO | sharedRW | uniqueRW`), small-step `AliasState` / `AliasStep` (`readDst | readSrc | writeSrc | writeDst`), `TracePermitted`, `execAliasTrace`, and `ReadOnlyInvariant` (`ubOccurred = false`, neither `sharedRO` tag invalidated, and `dstCap = .sharedRO → memVal = initVal`).

#### 6.2 Verified Theorem Ledger and Axiom Audit

| Theorem | Exact Formal Property Proved | `#print axioms` |
| :--- | :--- | :--- |
| `union_transmute_trunc_and_pad_sound` | Under `AcceptHasNoOutEdges src`, `dfaTransmute src dst false fuel src.start dst.start = true` implies `∀ wSrc, src.accepts wSrc = true → UnionTransmuteCompat dst wSrc` (every valid source byte word is valid under prefix truncation or trailing `UNINIT` extension). | `[propext, Quot.sound]` |
| `dfa_transmute_forall_implies_language_inclusion` | Under `AcceptHasNoOutEdges src`, `FixedLen src n`, `FixedLen dst n`, `dfaTransmute src dst false fuel ... = true` implies `∀ w, src.accepts w = true → dst.accepts w = true` ($L(\text{Src}) \subseteq L(\text{Dst})$). | `[propext, Quot.sound]` |
| `dfa_transmute_exists_union_witness` | Under `AcceptHasNoOutEdges src` and `LiveFrom src`, `dfaTransmute src dst true fuel ... = true` implies `∃ wSrc, src.accepts wSrc = true ∧ UnionTransmuteCompat dst wSrc`. | `[propext, Quot.sound]` |
| `dfa_transmute_exists_implies_nonempty_intersection` | Under `AcceptHasNoOutEdges src`, `LiveFrom src`, `FixedLen src n`, `FixedLen dst n`, `dfaTransmute src dst true fuel ... = true` implies `∃ w, src.accepts w = true ∧ dst.accepts w = true` ($L(\text{Src}) \cap L(\text{Dst}) \neq \emptyset$). | `[propext, Quot.sound]` |
| `repaired_ref_transmute_preserves_readonly_invariant` | Whenever `refDischarged (refConditionsRepaired assume src dst) src dst fwdOk revOk outlivesOk = true`, every execution trace `tr` from `initAliasState src dst v0` preserves `ReadOnlyInvariant` (zero read-only tag invalidation, zero aliasing UB, constant observed value under `dstCap = .sharedRO`). | `[propext]` |
| `ce1_upstream_missing_src_freeze_allows_cell_to_readonly_ref_ub` | Constructive counterexample 1 (`#164247`): `refConditionsUpstream` accepts `&Cell<u8> -> &u8` (`Assume::NOTHING`), `refConditionsRepaired` rejects it, and `issue164247Trace = [.readDst, .writeSrc 99, .readDst]` from `v0 = 7` is well-typed (`TracePermitted`), sets `ubOccurred = true`, and leaves `memVal = 99` vs `initVal = 7`. | *(no axioms)* |
| `ce2_disjoint_valid_sets_fail_even_under_assume_validity` | Constructive counterexample 2 (`TwoOnly -> bool`): for every `fuel : Nat`, `dfaTransmute twoOnlyDfa boolDfa true fuel 0 0 = false`, and no `w` is accepted by both `twoOnlyDfa` and `boolDfa`. | `[propext]` |
| `ce3_unpruned_safety_invariant_adt_unsound_without_assume_safety` | Constructive counterexample 3 (`u8 -> EvenU8`): `evenU8Tree.prune DefKind.hasSafetyInvariants = .alt []`, whereas skipping pruning yields `u8Dfa -> u8Dfa` acceptance (`true`) while `threeWord = [3]` is `u8`-valid yet violates `evenU8SafetyInvariant`. | `[propext]` |
| `upstream_answer_or_order_asymmetry` | `thereExistsFold ... [.ifCond c, .yes] = .ifCond c` while `thereExistsFold ... [.yes, .ifCond c] = .yes`, formally capturing the non-Boolean `Answer::or` variant-ordering bug. | `[propext]` |
| `union_transmute_u32_to_u8_prefix_trunc_accepted`, `union_transmute_u8_to_padded_align2_pad_ext_accepted`, `union_transmute_u8_to_u16_rejected` | Concrete DFA witnesses verifying prefix truncation acceptance (`u32 -> u8`), trailing-uninit extension acceptance (`u8 -> PaddedAlign2`), and `DstIsTooBig` rejection (`u8 -> u16`). | `[propext]` |
| `prune_safety_rejects_maybe_uninit`, `prune_assume_safety_retains_maybe_uninit` | Concrete tree-pruning witnesses for `MaybeUninit<u8>` under `Assume::NOTHING` vs `Assume::SAFETY`. | `[propext]` |
| `repaired_ref_allows_mut_cell_to_shared_ro`, `repaired_ref_rejects_shared_to_mut`, `repaired_ref_requires_reverse_for_mut_to_mut` | Positive controls for `&mut Cell<u8> -> &u8` (accepted), `&u8 -> &mut u8` (rejected), and `&mut -> &mut` requiring reverse transmutability. | *(no axioms)* |

## Boundaries

Every boundary below is labeled with its exact negative-space category per `FORMAT.md`:

1. **Model-to-System Gap of `support/RustcTransmuteDfaAndRefSoundness.lean` (`not examined` / `known not to apply` as a refinement proof):**
   - No mechanized refinement theorem links `RustcTransmuteDfaAndRefSoundness.lean` to `rustc`'s actual Rust implementation, `rustc_abi::Layout`, LLVM IR codegen, or Miri's Stacked/Tree Borrows interpreter. The Lean proofs establish exact properties of the formalized 257-symbol byte DFA, tree pruning, `Answer::or` algebra, and single-location reference capability model; all claims about real `rustc` and Miri rest on direct primary-source inspection (`source`) and live compiler/Miri execution (`execution`).
   - Specifically, the Lean DFA model omits `Reference` transitions interleaved inside compound structs/unions, `Dfa::union` / `Dfa::concat` compilation from `LayoutTree` (modeled at the `ByteDfa` interface assuming `AcceptHasNoOutEdges` and `LiveFrom`), multi-byte per-offset `UnsafeCell` placement (the operational aliasing model tracks one location and whole-referent `isFreeze`), pointer provenance, lifetimes, concurrency/atomics, and `Drop` glue.
2. **Wide Pointers, DSTs, Raw Pointers, `Box<T>`, Function Pointers, and Generic Parameters (`unsupported` by `rustc_transmute`):**
   - At `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `Tree::from_ty` returns `Err(Err::NotYetSupported)` for `*const T`, `*mut T`, `Box<T>` (explicitly excluded by `if !ty.is_box()`), `fn(...)`, slices `[T]`, `str`, `dyn Trait`, closures, and coroutines.
   - Both legacy (`candidate_assembly.rs:1118`) and next (`trait_goals.rs:697`) trait solvers reject generic type or const parameters (`has_non_region_param()` / `has_non_region_placeholders()`), and `from_variant` rejects `FieldsShape::Primitive` ADTs (`NonZero<T>`, `Option<NonZero<T>>`, open PR `#148449`).
3. **`&mut T -> &T` Transmute Under Future Operational Semantics (`unknown`):**
   - While our Miri Stacked Borrows and Tree Borrows probes confirm that consuming `&mut Cell<u8>` via `TransmuteFrom::transmute` into `&u8` executes with `rc = 0` on `rustc 1.98.0-nightly` (`14210df0e`), an issue comment on `rust-lang/rust#164247` (`2026-11-08`) notes an unresolved debate in `rust-lang/unsafe-code-guidelines#592` over whether future Rust operational semantics might restrict creating `&T` from `&mut T` via raw transmutation rather than a shared reborrow. This report records current Miri behavior (`execution`) and does not claim normative permanence if UCG changes the retagging contract.
4. **Byte-Range-Precise Interior Mutability in Prefix-Truncated References (`known not to apply` to `Condition::Immutable`):**
   - Our Miri probe on `CellSecond(u8, Cell<u8>)` demonstrates that `&CellSecond -> &u8` is operationally sound under both Stacked Borrows and Tree Borrows when `Cell<u8>` lies strictly outside `[0, size_of::<u8>())`. Requiring `Condition::Immutable { ty: src_ref.referent }` (`Src: Freeze`) therefore is a **sufficient** soundness repair for `#164247`, not a necessary condition for every prefix-truncating shared reference transmute. Whether `rustc_transmute` should adopt whole-referent `Src: Freeze` or a byte-offset `visit_freeze_sensitive` check over `[0, dst_ref.referent_size)` is an upstream design choice (`unknown`).
5. **Non-`x86_64`, Big-Endian Targets, and `unsafe` Field Annotations (`not examined`):**
   - Execution probes were run solely on little-endian `x86_64-unknown-linux-gnu`. Big-endian byte ordering in `Tree::from_big_endian` (`char`) and `Tree::from_tag` (multi-byte enum discriminants) was inspected only in source, not executed on big-endian hardware.
   - `rustc`'s experimental `unsafe_fields` feature does **not** yet influence `Def::has_safety_invariants()` (`layout/mod.rs:154-156` explicitly notes "This check does not inspect `unsafe` field annotations"); interactions with unmerged PR `#148449`'s caller-module visibility checking were `not examined`.
6. **Direct Execution of the Extended 14 Cases on `1.102.0-nightly` (`not examined` by live execution; `derived` from source identity):**
   - The live-executed nightly toolchain is `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). All 38 core cases were empirically compared against `1.102.0-nightly` (`3ef0c22cd`), and `compiler/rustc_transmute/src/*` was diffed between `3ef0c22cd` and `HEAD 342d74463a` (confirming byte-for-byte identity). The 14 extended diagnostic cases and the 3 additional Miri aliasing-boundary probes were executed live on `1.98.0-nightly` (`14210df0e`); their identical behavior on `3ef0c22cd` / `HEAD` (with `ref_mut_u8_to_ref_mut_cell_u8_safety` flipping from `FAIL` to `PASS` under `-Z next-solver=globally`) is `derived` from the exact source diff of `delegate.rs` and `trait_goals.rs`.

## Evidence

### Primary Git Sources (Immutable 40-Hex Commits)

1. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`HEAD`, observed `2026-11-22`):**
   - `compiler/rustc_transmute/src/lib.rs:19-105` — `Assume`, `TransmuteTypeEnv::is_transmutable`, `Assume::from_const`.
   - `compiler/rustc_transmute/src/layout/mod.rs:19-57` — `Byte { start: u16, end: u16 }`, `UNINIT = 256`, `Byte::uninit() = [0, 257)`, `contains_uninit`.
   - `compiler/rustc_transmute/src/layout/mod.rs:144-158` — `layout::rustc::Def` and `Def::has_safety_invariants(&self) { self != &Self::Primitive }`.
   - `compiler/rustc_transmute/src/layout/tree.rs:97-129` — `Tree::char`, unused `#[allow(dead_code)] Tree::nonzero`.
   - `compiler/rustc_transmute/src/layout/tree.rs:157-197` — `Tree::prune`, `Tree::is_inhabited`.
   - `compiler/rustc_transmute/src/layout/tree.rs:304-587` — `Tree::from_ty`, `from_tuple`, `from_struct`, `from_enum`, `from_variant` (`FieldsShape::Arbitrary` guard at lines `485-487`), `from_tag`, `from_union`.
   - `compiler/rustc_transmute/src/layout/dfa.rs:104-260, 342-508` — `Dfa::from_tree`, `concat`, `union` (skipping `accept` out-edges at lines `203-216`), `EdgeSet::get_uninit_edge_dst` (`379-386`), `UnionIter`.
   - `compiler/rustc_transmute/src/maybe_transmutable/mod.rs:88-130` — `Tree` pruning order (strip `src` `Def`s -> `DstUninhabited` check -> prune `dst` when `!assume.safety` -> `src` `Uninhabited` -> `Answer::Yes` -> `dst` `Uninhabited` -> `DstMayHaveSafetyInvariants`).
   - `compiler/rustc_transmute/src/maybe_transmutable/mod.rs:170-341` — `answer_impl` (prefix truncation `180-185`, trailing-uninit extension `186-192`, `Assume::VALIDITY` quantifier flip `194-203`, byte loop `205-220`, ref guards `238-259`, **buggy reference obligations `276-282` omitting `Condition::Immutable { ty: src_ref.referent }`**, `Quantifier::apply` `313-341`).
   - `compiler/rustc_type_ir/src/transmute.rs:3-131` — `Answer`, `Condition`, `Reason`, `Answer::and`, and non-Boolean `Answer::or` (`104-131`).
   - `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:118-122, 1113-1128` — legacy `TransmutabilityCandidate` assembly.
   - `compiler/rustc_trait_selection/src/traits/select/confirmation.rs:275-318` — legacy `confirm_transmutability_candidate` calling `flatten_answer_tree`.
   - `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:686-739` — next-solver `consider_builtin_transmute_candidate` calling `flatten_answer_tree`.
   - `compiler/rustc_next_trait_solver/src/solve/mod.rs:446-481` — `flatten_answer_tree` collapsing `Condition::IfAny` into `Condition::IfAll` (`452-457`).
   - `library/core/src/mem/transmutability.rs:85-142, 151-407` — `#[lang = "transmute_trait"] #[rustc_coinductive] pub unsafe trait TransmuteFrom`, union-transmute default body (`116-141`), and `Assume`.
2. **`rust-lang/rust` @ `cee2a0ddf022ee393e384ff576c6a190915f19a1` (`2026-10-12`, PR `#163946`) and `5b216e01a117532b30f061f3dff8a61408113c77` (`2026-10-10`):** Commits lifting `Answer`/`Condition`/`Reason` into `rustc_type_ir` and enabling `Answer::If` nested goals in `-Z next-solver=globally`.
3. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`):**
   - `compiler/rustc_trait_selection/src/solve/delegate.rs:363-382` — pre-`#163946` next-solver stub rejecting `Answer::If(_) => Err(NoSolution)`.
   - `compiler/rustc_transmute/src/layout/mod.rs:148-153` and `maybe_transmutable/mod.rs:297-301` — identical `Def::has_safety_invariants` and `#164247` bug locations in `1.98.0-nightly`.
4. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`):** Byte-for-byte identical across `compiler/rustc_transmute/src/*` to `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; empirically confirms 38/38 legacy vs. `-Z next-solver=globally` parity and `#164247` reproduction under both solvers.
5. **Upstream GitHub Issues / PRs (queried live `2026-11-22`):**
   - `rust-lang/rust#164247` (*TransmuteFrom::<_, Assume::NOTHING> can transmute references to types with interior mutability*, state: `open`, created `2026-10-13`, updated `2026-11-08`).
   - `rust-lang/rust#148449` (*transmutability: model NonZero scalar ranges*, PR state: `open`, created `2025-11-03`, updated `2026-06-25`, tracking `#99571`).
6. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean:312-321, 596-628` — `MirTy` and `Rvalue` fail-closed `.unsupported` boundary.
   - `trusted/lean/Trusted/MirSemantics.lean:422-424, 949-976` — `AllocByte` (`uninit` / `init UInt8 (Option AllocId)`) and `deinitMovedPlace = true`.

### Preserved Package Support Artifacts

| File | Size (bytes) | SHA-256 | Purpose |
| :--- | ---: | :--- | :--- |
| `support/probe_rustc_transmute.py` | 22,840 | `1f8ef298f63dfa9232d3c66ecfcedb90af79d8ea0b1f1a16d17f75b29e2d5410` | Standalone Python 3.10+ probe executing all 52 `rustc` cases (legacy + `-Z next-solver=globally`), `-Copt-level={0,2}` binaries, LLVM IR signature capture, and 9 Miri Stacked/Tree Borrows runs with automatic path scrubbing. |
| `support/probe_rustc_transmute_results.json` | 41,805 | `3c30d269347483a08054642061f06ae76e13e8a07d78ef184d4936af6fdda525` | Complete captured JSON results from executing `probe_rustc_transmute.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0` / `LLVM 22.1.6` (`x86_64-unknown-linux-gnu`) on `2026-11-22`. |
| `support/RustcTransmuteDfaAndRefSoundness.lean` | 47,021 | `35556bb513dfdd2324996a05d7863bbeae8a74f6ea57d49c9bb11752f5afaba0` | 1,097-line constructive `Lean v4.34.1` formalization (Core Lean only; `-DwarningAsError=true`; `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`; axioms $\subseteq$ `{propext, Quot.sound}`). |

### Verification Commands Executed (`2026-11-22`)

1. **Live compiler & Miri suite:**
   ```console
   python3 support/probe_rustc_transmute.py support/probe_rustc_transmute_results.json
   ```
   Exit code `0`. Confirmed 38/38 legacy parity with `1.102.0-nightly`, exact 11/38 `1.98` next-solver `Answer::If` divergence, all 14 extended diagnostic cases, `EXT=66 TRUNC=0x44` in Miri, `-O0` (`BEFORE=7 AFTER=99 CELL=99`) vs `-O2` (`BEFORE=7 AFTER=7 CELL=99`), LLVM IR `ptr noalias noundef nonnull readonly ... %ro`, and Miri UB (`rc = 1`) in all 4 `#164247` configurations plus the 3 aliasing-boundary probes.
2. **Lean 4 kernel verification and axiom audit:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/RustcTransmuteDfaAndRefSoundness.lean
   ```
   Exit code `0` on `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`. Separate `#print axioms` audit over all 19 public theorems returned exit code `0` with axioms exclusively drawn from `{propext, Quot.sound}` (zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`).

## Revalidation

Use the following narrow, discriminating checks to detect upstream changes without repeating the full audit:

1. **Re-run the complete 52-case `rustc` + LLVM IR + Miri probe against any newer nightly toolchain:**
   ```console
   python3 support/probe_rustc_transmute.py /tmp/transmute_reval.json
   ```
   Check four high-signal discriminators in `/tmp/transmute_reval.json`:
   - **`rust-lang/rust#164247` fix:** `core_cases.ref_cell_u8_to_ref_u8_nothing` and `core_cases.ref_unsafecell_u8_to_ref_u8_nothing` flip from `true` to `false` (expected diagnostic: `Cell<u8>: Freeze` / `UnsafeCell<u8>: Freeze` unsatisfied). Also check whether `ref_aliasing_boundary_probes.cell_second_prefix_*` becomes compile-rejected (indicating whole-referent `Src: Freeze`) or stays accepted (indicating byte-range `visit_freeze_sensitive`).
   - **`rust-lang/rust#148449` merge (`NonZero` support):** `core_cases.opt_nonzero_u8_to_u8_nothing`, `core_cases.u8_to_opt_nonzero_u8_safety`, and `extended_cases.nonzero_u8_to_u8_nothing` flip from `false` (`NotYetSupported`) to `true` (or visibility-checked error).
   - **Next-solver parity:** `core_solver_divergences == 0` and `extended_solver_divergences == 0` on any toolchain newer than `cee2a0ddf022ee393e384ff576c6a190915f19a1`.
   - **`Answer::or` & `IfAny` fixes:** `extended_cases.answer_or_ref_first_safety_validity` flipping to `true` indicates `Answer::or` gained Boolean absorption (`If(c).or(Yes) == Yes`); `extended_cases.ifany_as_ifall_ref_union_safety` flipping to `true` indicates trait-solver disjunction support in `flatten_answer_tree`.
2. **Targeted upstream source diff (fastest static check):** Diff only five files in `rust-lang/rust` against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
   - `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` (lines `244-290` for `#164247`; `180-235` for DFA rules)
   - `compiler/rustc_transmute/src/layout/mod.rs` (`Def::has_safety_invariants`)
   - `compiler/rustc_transmute/src/layout/tree.rs` (`from_variant`'s `FieldsShape` handling for `#148449`)
   - `compiler/rustc_type_ir/src/transmute.rs` (`Answer::or`)
   - `compiler/rustc_next_trait_solver/src/solve/mod.rs` (`flatten_answer_tree`)
3. **Re-check the Lean 4.34.1 mechanization (takes `< 3s`):**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/RustcTransmuteDfaAndRefSoundness.lean
   ```
   Confirm exit code `0`, and append `#print axioms` checks on `union_transmute_trunc_and_pad_sound`, `dfa_transmute_forall_implies_language_inclusion`, `dfa_transmute_exists_implies_nonempty_intersection`, `repaired_ref_transmute_preserves_readonly_invariant`, and `ce1_*` / `ce2_*` / `ce3_*` to verify no classical or native-reduction axioms entered the proof.
4. **Re-check Anneal's trusted boundary when `CastKind::Transmute` or ADTs are added:** Inspect `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `Rvalue`) and `trusted/lean/Trusted/MirSemantics.lean` (`evalRvalue`, `AllocByte`) in `joshlf/anneal` for removal of `.unsupported` on `CastKind::Transmute`, unions, or reference retagging.
