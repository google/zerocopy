# `rustc_privacy` Module-Tree Visibility Lattice, RFC 2145 Interface Lints, Sealed-Trait Soundness, and `zerocopy` Sealing Enforcement

## Summary

Rust's visibility and privacy subsystem enforces lexical path encapsulation, semantic type-privacy checking, cross-crate API surface computation, and sealed-trait closure through four coupled compiler layers:

1. **Module-tree `Visibility` partial order (`compiler/rustc_middle/src/ty/mod.rs`)**: `ty::Visibility<Id>` (`Public` vs. `Restricted(Id)`) forms a rooted tree-ordered semilattice over module `DefId`s, NOT a linear total order and NOT merely the five syntactic keywords (`pub`, `pub(crate)`, `pub(super)`, `pub(self)`, `pub(in path)`). In `TyCtxt::def_id_partial_cmp`, ancestor modules compare **larger** than descendant modules, `Visibility::Public` is the unique top element, sibling modules within the same crate compare as `None` (unordered), and `DefId`s from different crates compare as `None`. Notably, `ty::Visibility` has **no** `is_at_least` method in either `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` or `20fe935d50367c0ff8872c2ebfa050c5c99d9201`; dominance and access checks use `Visibility::is_accessible_from` (via `TyCtxt::is_descendant_of`), `Visibility::partial_cmp`, and `Visibility::greater_than` (which emits a `delayed_bug` on `None`). Restricting `pub(in path)` to a non-ancestor module fails resolution with `E0742`.
2. **Four-level `EffectiveVisibilities` lattice (`compiler/rustc_middle/src/middle/privacy.rs`, `rustc_resolve/src/effective_visibilities.rs`, `rustc_privacy/src/lib.rs`)**: For each tracked `LocalDefId`, `EffectiveVisibility` stores a monotone tuple of four `Visibility` values: `private_vis <= direct <= reexported <= reachable <= reachable_through_impl_trait`, asserted in `EffectiveVisibilities::check_invariants`. Name resolution (`EffectiveVisibilitiesVisitor`) computes `Direct` (parent module chain without `use`) and `Reexported` (short-circuited `pub use` chains). Type-level `EmbargoVisitor` (`rustc_privacy`) then computes `Reachable` (interface, trait supertrait/where-clause, field, impl-header, and macro reachability, capped by `nominal_vis`) and `ReachableThroughImplTrait` (return-position `impl Trait` and TAIT opaque underlying types, populated by `reach_through_impl_trait` with `max_vis = None` and intentionally **not** capped by `nominal_vis`). Items whose nominal visibility equals their defining module's `private_vis` are omitted from `EffectiveVisibilities` unless reached by a more public alias, re-export, or opaque interface.
3. **RFC 2145 lints (`private_bounds`, `private_interfaces`, `unnameable_types`), `unreachable_pub`, and `E0446`**: `SearchInterfaceForPrivateItemsVisitor` checks interface components against `*effective_vis.at_level(Level::Reachable)` rather than nominal visibility, splitting primary interfaces (`PRIVATE_INTERFACES`, warn-by-default: function signatures, struct fields, trait impl `Self`/trait headers, type-alias right-hand sides, generic defaults/const-param types) from secondary interfaces (`PRIVATE_BOUNDS`, warn-by-default: generic bounds, `where` clauses, supertraits). Because `mod private { pub trait Sealed {} }` gives `Sealed` nominal visibility `Visibility::Public`, `pub trait PublicSealed: private::Sealed {}` satisfies `Public.greater_than(Public) == false` and compiles cleanly under `#![deny(private_bounds, private_interfaces, unreachable_pub)]`. `UNREACHABLE_PUB` (allow-by-default) suppresses warnings whenever `effective_visibilities.is_reachable(def_id)` is `true`—covering `private::Sealed` precisely because `PublicSealed`'s supertrait lifted `Sealed`'s `Reachable` visibility to `Public`, while flagging unused `pub trait UnusedSealed {}` in `mod private`. Opt-in `UNNAMEABLE_TYPES` (allow-by-default) triggers iff `reachable.is_public() && reexported != reachable`, flagging `private::Sealed` when denied while remaining silent for crate-restricted leaks such as `pub(in crate::outer)` functions returning private-module `pub` structs. In contrast, leaking a non-public type in an `impl` associated type sets `check.hard_error = is_assoc_ty` and emits unconditional `error[E0446]` (`InPublicInterface`), ignoring `#![allow(private_interfaces, private_bounds)]`. Separate privacy visitors emit `E0603` (`rustc_resolve` path bottlenecks), `E0616` (member field access), `E0451` (`NamePrivacyVisitor` struct constructor/pattern fields), and uncoded `"error: type X is private"` (`TypePrivacyVisitor`, catching inferred private return types unified with public type aliases even under `#![allow(private_interfaces)]`).
4. **Sealed-trait enforcement and `"sealed trait"` diagnostics (`rustc_trait_selection/src/error_reporting/traits/suggestions.rs`)**: Downstream crates can write generic bounds `T: PublicSealed`, call trait methods, and coerce to `&dyn PublicSealed`. Any external attempt to write `impl PublicSealed for Local` fails with `error[E0277]` on the inaccessible supertrait `private::Sealed`, and `suggestions.rs` detects that `private::Sealed` is externally inaccessible to emit `= note: ... is a "sealed trait"` together with existing upstream implementors (`all_impls`). Sealing fails immediately if `private::Sealed` is re-exported (`pub use private::Sealed`) anywhere reachable by downstream crates, and `#[doc(hidden)] pub mod` provides **zero** compiler-enforced sealing (`#[doc(hidden)]` affects `rustdoc`, not `rustc_privacy`).
5. **Real `google/zerocopy` sealing and closed-world composition**: `zerocopy::byteorder::ByteOrder` (supertrait `private::Sealed`, `BigEndian`/`LittleEndian`) and `zerocopy::pointer::invariant::{Invariants, Aliasing, Alignment, unsafe trait Validity, Reference}` (supertrait `sealed::Sealed`) enforce closed-world marker invariants at compile time (`E0277` on downstream `impl`/`unsafe impl`). Crucially, mechanized proof development established that complete **defining-crate fixity**—proving both that every `self` type belongs to `zerocopy`'s allowlist AND that every `impl` originates in crate `zerocopy`—requires composing unnameability (`E0603`/`E0277`, which excludes downstream types if `zerocopy` keeps its private allowlist closed) with the orphan rule (`E0117`, which prevents downstream crates from adding impls of `ByteOrder`/`Reference` on upstream types like `BigEndian` or `Shared`). Conversely, `zerocopy::pointer::invariant::Read<A, R>` is intentionally unsealed (compiled downstream impl verified), remaining sound because `Alignment::read` gates on `I::Aliasing: Reference` (`Shared` or `Exclusive`), whose sealed-trait closure fixes valid reason tokens. For `joshlf/anneal`, `anneal-rustc-capture` runs inside `Callbacks::after_analysis` gated on `tcx.dcx().has_errors().is_none()`, meaning all privacy and `E0277`/`E0446` checks complete before MIR capture.
6. **Empirical & kernel-checked verification**: All 33 live multi-crate `rustc` probes (`12` `rc=0` positive/suppression controls, `21` `rc=1` negative discriminators including 7 real `zerocopy 0.8.64` builds) pass on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, and the standalone `Lean v4.34.1` mechanization (`PrivacyVisibilityLatticeAndSealedTraitSoundness.lean`, 1,928 lines, 291 `noncomputable def`s, 144 theorems, `0` `sorry`, `0` `._unsafe_rec`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, kernel axioms `[propext]`) mechanically checks the module-tree visibility partial order, `EffectiveVisibility` invariants, RFC 2145 lint matrix, cross-crate impl impossibility, `zerocopy` closed-world `unsafe` soundness theorem, and re-export/`#[doc(hidden)]`/unsealed counterexamples.

## Applicability

This report characterizes the eight durable upstream subjects recorded in `REPORT.json` (`observed_at: 2026-11-24`):

1. **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`, commit date `2026-05-31`, host `x86_64-unknown-linux-gnu`, `LLVM 22.1.6`)**: Both primary source and live execution (`33` probes in `support/probe_results.json`) cover this exact toolchain revision.
2. **`rust-lang/rust` (`20fe935d50367c0ff8872c2ebfa050c5c99d9201`, upstream `main`)**: Inspected directly in source across `compiler/rustc_middle/src/{ty/mod.rs, middle/privacy.rs}`, `compiler/rustc_resolve/src/effective_visibilities.rs`, `compiler/rustc_privacy/src/{lib.rs, diagnostics.rs}`, `compiler/rustc_lint/src/builtin.rs`, `compiler/rustc_lint_defs/src/builtin.rs`, and `compiler/rustc_trait_selection/src/error_reporting/traits/suggestions.rs`. Source only; not executed in binary form.
3. **`google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0`, crate version `0.8.64`)**: Executed directly (`--edition=2021 --crate-type=lib --crate-name=zerocopy --cfg no_zerocopy_allocator_api_1_100_0` with `CARGO_PKG_VERSION=0.8.64` on `rustc 1.98.0-nightly 14210df0e`) together with six downstream `--edition=2024` consumer probes (`d02`–`d07`).
4. **`google/zerocopy` (`eb65abdaca712af129ba4ebb67a09e78c635a6cf`, upstream `main`)**: Audited against `zerocopy/src/byteorder.rs` and `zerocopy/src/pointer/invariant.rs`, confirming exact byte-for-byte identity with `907b9175fee081872ec883ca4709e6ad922f8ed0` on those sealed-trait definitions and `sealed` modules.
5. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `main`)**: Source audit of `trusted/rustc-capture/src/driver.rs` (built against `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, verifying `Callbacks::after_analysis` ordering relative to `rustc` error checks) and `trusted/lean/Trusted/MirAst.lean` (documenting Anneal's noncomputable definition discipline eliminating `._unsafe_rec` helpers). Not executed in this investigation.
6. **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`)**: `src/visibility-and-privacy.md` provides normative language rules for module-tree visibility, `pub(in path)` ancestor requirements, and `pub use` privacy short-circuiting.
7. **`rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`)**: `text/2145-type-privacy.md` provides design rationale and normative definitions for `EffectiveVisibilities`, primary vs. secondary interfaces, `private_interfaces`, `private_bounds`, and `unnameable_types` (including one subtle divergence noted in `Findings`).
8. **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Executed directly in strict single-file batch mode (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) on `support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean`.

### Shared Behavior vs. Revision Deltas Across the Two `rust-lang/rust` Revisions

All core lattice semantics—`Visibility` partial ordering via `is_descendant_of` and `def_id_partial_cmp`, the four `EffectiveVisibility` `Level` variants and `check_invariants` inequalities, `EmbargoVisitor`'s unconditional RPIT `reach_through_impl_trait` pass (`max_vis = None`), `PRIVATE_INTERFACES` vs. `PRIVATE_BOUNDS` vs. `UNNAMEABLE_TYPES` vs. `UNREACHABLE_PUB` conditions, associated-type `E0446` hard errors, `NamePrivacyVisitor` (`E0451`) and `TypePrivacyVisitor` (`ItemIsPrivate`), and `suggestions.rs` `"sealed trait"` note emission—are identical in substance across `14210df0e` (`1.98.0-nightly`) and `20fe935d5` (`main`). Specific structural differences between `14210df0e` and `20fe935d5` are:

| Subsystem | `14210df0e` (`rustc 1.98.0-nightly`, executed) | `20fe935d5` (`rust-lang/rust` `main`, source audit) | Behavioral Impact on Findings |
| --- | --- | --- | --- |
| `Visibility` generic ID parameter (`ty/mod.rs`) | `pub enum Visibility<Id = LocalDefId>` (L311); `Visibility::to_def_id` (L425); `TyCtxt::def_id_partial_cmp` is private (`fn def_id_partial_cmp`, L378) | `pub enum Visibility<Id = LocalModId>` (L257); `Visibility::to_mod_id` (L435); `TyCtxt::def_id_partial_cmp` is `pub fn` (L384) | Type-level narrowing from `LocalDefId` to `LocalModId`; tree comparison algorithm (`def_id_partial_cmp` + `is_descendant_of`) unchanged |
| `RestrictionKind` placement (`ty/mod.rs`) | Defined outside `ty/mod.rs` | Moved directly into `compiler/rustc_middle/src/ty/mod.rs` (L285–342) with `is_allowed_in` and `stricter_of` | Exposes explicit `is_allowed_in` / `stricter_of` using the same `tcx.is_descendant_of` partial order |
| `rustc_privacy` diagnostic module & traits/clauses (`lib.rs`) | `mod errors;` (`errors.rs`); `visit_predicates(explicit_predicates_of)` (`GenericPredicates`); `DefIds` only over `ty::Adt`, etc. | Renamed `mod diagnostics;` (`diagnostics.rs`); `LocalModDefId` -> `LocalModId`; `visit_gen_clauses(explicit_clauses_of)`; `DefIdVisitorSkeleton` also handles `ty::View` (L187) and `ClauseKind::CompressedTrait(_) => unreachable!()` (L158), plus `DefKind::TestBinderConstraints` unreachable arm (L830) | Identical diagnostic messages (`FieldIsPrivate`, `ItemIsPrivate`, `InPublicInterface`, `UnnameableTypesLint`, `PrivateInterfacesOrBoundsLint`); `CompressedTrait` unreachable assumes explicit user bounds remain uncompressed |
| Nested `pub use` and cycle guard (`rustc_resolve/src/effective_visibilities.rs`) | Inline loop inside `set_bindings_effective_visibilities` (L125–149); `update_import` directly recurses into `ambiguity_vis_max`; only updates `import.def_id()` (L110–112) | Factored `update_decl_chain` with `seen_most_visible` `FxHashSet` cycle guard (L145–170); also calls `r.effective_visibilities.update_eff_vis(root, eff_vis, r.tcx)` on `r.owners[&import.root_id].def_id` (L113–117) | Prevents mutual-glob cycles and ensures `unreachable_pub` recognizes nested `pub use` statements whose inner target is exported |

All synthetic Rust probes execute under `--edition=2024` (with `zerocopy` library built under `--edition=2021` to match its `Cargo.toml` edition). Results do not rely on Cargo dependency resolution, proc-macro crates, or host-specific filesystem layout.

## Findings

### 1. Module-Tree Visibility Partial Order (`ty::Visibility`)

Basis: normative + source + execution (`rust-lang/reference` `c9cc32825`, `rust-lang/rust` `14210df0e` & `20fe935d5`, probes `a01`–`a07`, Lean Part 1–2).

#### Tree Representation and Dominance Semantics

The Rust Reference (`src/visibility-and-privacy.md`, `r[vis]`, `r[vis.scoped]`, L15–192) specifies that every item has a lexical parent module, default visibility is module-private (`pub(self)`), and scoped visibility modifiers (`pub(crate)`, `pub(super)`, `pub(self)`, `pub(in path)`) restrict visibility only to ancestor modules of the defining item (`r[vis.scoped.in]`). Inside `compiler/rustc_middle/src/ty/mod.rs`, `rustc` models this semantics with a two-variant enum:

```rust
// compiler/rustc_middle/src/ty/mod.rs (20fe935d5 L256-262; 14210df0e L310-316 has Id = LocalDefId)
#[derive(Clone, Debug, PartialEq, Eq, Copy, Hash, Encodable, BlobDecodable, StableHash)]
pub enum Visibility<Id = LocalModId> {
    /// Visible everywhere (including in other crates).
    Public,
    /// Visible only in the given crate-local module.
    Restricted(Id),
}
```

Four facts govern this representation:

1. **Five syntactic forms collapse into two variants**: Unqualified private visibility and `pub(self)` both normalize to `Visibility::Restricted(parent_module)`; `pub(crate)` normalizes to `Visibility::Restricted(CRATE_MOD_ID)` (whose `is_top_level_module()` returns `true`); `pub(super)` and `pub(in path)` normalize to `Visibility::Restricted(resolved_ancestor_mod_id)`; and unqualified `pub` maps to `Visibility::Public`. Notice `Visibility::to_string` (`20fe935d5` L265–281; `14210df0e` L319–335) prints `"pub(crate)"`, `"pub(self)"`, `"pub(in crate...)"`, or `"pub"` directly from those cases.
2. **No `is_at_least` method exists**: Direct source inspection of `compiler/rustc_middle/src/ty/mod.rs` and `compiler/rustc_privacy/src/lib.rs` across both `14210df0e` and `20fe935d5` confirms that `ty::Visibility` defines `is_public`, `map_id`, `to_mod_id` (`to_def_id` in `14210df0e`), `is_accessible_from`, `partial_cmp`, `greater_than`, `expect_local`, and `is_visible_locally`—there is **no** `is_at_least` method. Comparisons are instead performed via `is_accessible_from`, `partial_cmp`, `greater_than`, and helper `min(vis1, vis2, tcx)` (`rustc_privacy/src/lib.rs` L342 in `20fe935d5` / L337 in `14210df0e`).
3. **Orientation of the partial order (`ancestor > descendant`)**: `TyCtxt::def_id_partial_cmp(lhs, rhs)` (`20fe935d5` L384–407; `14210df0e` L378–401) walks `opt_parent` up the `DefId` tree within the same `krate` (exploiting the invariant that parent `DefId` indices are allocated smaller than child indices):
   - Different `krate` values -> `None` (cross-crate `DefId`s are always unordered).
   - `lhs` is a strict ancestor of `rhs` -> `Some(Ordering::Greater)` (`ancestor > descendant`).
   - `lhs` is a strict descendant of `rhs` -> `Some(Ordering::Less)` (`descendant < ancestor`).
   - Neither is an ancestor of the other (sibling modules in the same crate) -> `None` (unordered).
   - `TyCtxt::is_descendant_of(descendant, ancestor)` (`20fe935d5` L409–418; `14210df0e` L403–408) returns `matches!(self.def_id_partial_cmp(descendant, ancestor), Some(Ordering::Less | Ordering::Equal))`.
4. **Partial-order traps (`greater_than` and `min`)**: `Visibility::partial_cmp` (`20fe935d5` L450–464; `14210df0e` L438–452) makes `Visibility::Public` strictly greater than every `Restricted(_)` and delegates `(Restricted(l), Restricted(r))` to `tcx.def_id_partial_cmp`. Crucially, `Visibility::greater_than` (`20fe935d5` L470–482; `14210df0e` L458–470) emits a `delayed_bug` on `None` (`unordered visibilities`) and returns `false`! Similarly, `min(vis1, vis2, tcx)` (`if vis1.greater_than(vis2, tcx) { vis2 } else { vis1 }`) assumes comparability (e.g., an item's nominal visibility is restricted to an ancestor module of its parent module, or `Public`, so comparing an enclosing module's effective visibility or a field's visibility against the item's visibility normally traverses a single ancestor chain—although comments in `middle/privacy.rs` L91 and L251 note `FIXME: figure out why unordered visibilities occur here` in edge cases). In `20fe935d5`, `RestrictionKind::stricter_of` (`ty/mod.rs` L328–341) explicitly tests `is_descendant_of` and returns `rhs` when unordered, after `bug!` on cross-crate inputs.

#### Path Bottlenecks vs. `pub use` Short-Circuiting and Distinct Privacy Diagnostics

Module access along a direct path `p_1::...::p_k::item` succeeds only if **every** prefix module `p_i` along the syntactic path is accessible from the use site (`visibility.is_accessible_from(caller_mod, tcx)`). Conversely, `pub use hidden::item;` creates a re-export binding in the exporting module whose effective visibility at `Level::Reexported` short-circuits the intermediate private ancestor (`visibility-and-privacy.md`, `r[vis.reexports.private-item]`, L213–214), allowing external crates to name `item` via the re-export while direct access via `hidden::item` still fails.

Live `rustc 1.98.0-nightly (14210df0e)` probes in Part A demonstrate each mechanism and distinguish the exact compiler passes that emit errors:

| Probe | Mechanism Tested | Outcome & Exit | Exact Diagnostic / Observed Rule |
| --- | --- | --- | --- |
| `a01` | `pub(in crate::a)` + `pub(super)` + `pub(crate)` inside child `a::sub` and sibling `b` | `rc=0`, `VIS_OK=149` | `crate::a::sub` accesses `pub(in crate::a)` (`41`), `pub(super)` (`10`), and `pub(crate)` (`49`); sibling `b` accesses `pub(crate)` (`49`). |
| `a02` | Sibling `crate::b` calling `crate::a::in_a` (`pub(in crate::a)`) | `rc=1`, `E0603` | `error[E0603]: function in_a is private`; sibling modules are incomparable to ancestor chains containing `crate::a`. |
| `a03` | Parent module accessing `inner::secret` (`pub(self)`) | `rc=1`, `E0603` | `error[E0603]: function secret is private`; visibility flows downward to descendants, never upward to parents (`r[vis.access]`). |
| `a04` | `mod a::b { pub(in crate::other) fn bad_vis() {} }` | `rc=1`, `E0742` | `error[E0742]: visibilities can only be restricted to ancestor modules` (`rustc_resolve`). |
| `a05a` / `a05b` | `a05_lib` (`mod priv_outer { pub fn f(); pub fn g(); } pub use priv_outer::g;`) consumed externally | `a05a`: `rc=0`, `REEXP_OK=22`; `a05b`: `rc=1`, `E0603` | Re-export `a05_lib::g()` succeeds; direct `a05_lib::priv_outer::f()` triggers `error[E0603]: module priv_outer is private` (`function f is not publicly re-exported`). |
| `a06a` / `a06b` | Accessing `s.y` vs. constructing `m::S { x: 1, y: 2 }` for private field `y` | `a06a`: `E0616`; `a06b`: `E0451` | Field projection emits `error[E0616]`; struct literal/pattern constructor privacy is checked in `NamePrivacyVisitor::check_field` (`rustc_privacy/src/lib.rs` L942–956, `FieldIsPrivate`) emitting `error[E0451]`. |
| `a07` | `#![allow(private_interfaces)]` with `mod m { struct Priv(u32); pub type Alias = Priv; pub fn mk() -> Priv }` consumed via `let _: m::Alias = m::mk();` | `rc=1`, uncoded `ItemIsPrivate` | Even with RFC 2145's `private_interfaces` lint suppressed, `TypePrivacyVisitor::check_def_id` (`lib.rs` L1165–1171, `diagnostics.rs` L51–59) walks the inferred call/pattern semantic types (`walk_types`, L1753–1771) and emits `error: type Priv is private` (hard error with no `E` code). |

The `a07` distinction is critical for downstream Rust semantics: suppressing `private_interfaces` does **not** allow callers outside `m` to instantiate expressions whose semantic inferred type (or explicit annotation, after resolving aliases and impls) mentions `m::Priv`—`check_mod_privacy`'s `TypePrivacyVisitor` enforces semantic type accessibility at every use site independently of RFC 2145 signature lints.

---

### 2. Four-Level `EffectiveVisibilities` Lattice and Worklist Fixed Point

Basis: source + execution + derived (`rust-lang/rust` `14210df0e` & `20fe935d5`, probe `b01`, Lean Part 3).

#### Lattice Definition and Monotonicity Invariants

`compiler/rustc_middle/src/middle/privacy.rs` defines the four effective visibility levels in ascending order of directness (`20fe935d5` L21–48; `14210df0e` L21–47):

```rust
// compiler/rustc_middle/src/middle/privacy.rs (20fe935d5 L21-48)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, StableHash)]
pub enum Level {
    /// Superset of `Reachable` including items leaked through return position `impl Trait`.
    ReachableThroughImplTrait,
    /// Item is either reexported, or leaked through any kind of interface.
    Reachable,
    /// Item is accessible either directly, or with help of `use` reexports.
    Reexported,
    /// Item is directly accessible, without help of reexports.
    Direct,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, StableHash)]
pub struct EffectiveVisibility {
    direct: Visibility,
    reexported: Visibility,
    reachable: Visibility,
    reachable_through_impl_trait: Visibility,
}
```

In `EffectiveVisibilities::check_invariants` (`20fe935d5` L158–208; `14210df0e` L157–207), `rustc` asserts under `cfg!(debug_assertions)` that every entry `(def_id, ev)` satisfies the total chain:

$$\text{private\_vis}(\text{def\_id}) \le \text{ev.direct} \le \text{ev.reexported} \le \text{ev.reachable} \le \text{ev.reachable\_through\_impl\_trait}$$

where $\text{private\_vis}(\text{def\_id}) = \text{Restricted}(\text{parent\_module}(\text{def\_id}))$. In addition, for every item except `Impl`s, trait-impl associated items, and ambiguous `UseKind::Glob` re-exports (`middle/privacy.rs` L184–206), `check_invariants` enforces the upper bound:

$$\text{ev.reachable} \le \text{nominal\_vis}(\text{def\_id})$$

Crucially, `ev.reachable_through_impl_trait` is intentionally excluded from the `nominal_vis` cap (`middle/privacy.rs` L184–185: `// All effective visibilities except reachable_through_impl_trait are limited to nominal visibility`).

#### Two-Phase Construction: `rustc_resolve` Fixed Point + `EmbargoVisitor`

`EffectiveVisibilities` is constructed in two sequential phases:

1. **Name-resolution phase (`rustc_resolve/src/effective_visibilities.rs`, `EffectiveVisibilitiesVisitor::compute_effective_visibilities`)**:
   - Seeds crate root `CRATE_DEF_ID` with `EffectiveVisibility::from_vis(Public)` (`update_root`).
   - Repeatedly walks modules (`while visitor.changed`) propagating `Level::Direct` from enclosing modules and `Level::Reexported` across `DeclKind::Import` (`pub use`) chains (`ParentId::Import` returns `Level::Reexported`; `ParentId::Def` returns `Level::Direct`).
   - Skips any edge where `nominal_vis == private_vis` or the parent's local visibility equals `private_vis` via `may_update` (`20fe935d5` L190–201; `14210df0e` L169–180). `EffectiveVisibilities::update` (`middle/privacy.rs` L228–277) caps levels `<= level` by `max_vis = Some(nominal_vis)` and only mutates upwards (`calculated_effective_vis > *current_effective_vis_at_level`), guaranteeing fixed-point termination.
   - `20fe935d5` adds two hardening refinements over `14210df0e`: `update_decl_chain` tracks `seen_most_visible` to avoid infinite recursion on cyclic glob `ambiguity_vis_max` edges (L145–169), and line L113–117 also updates `r.owners[&import.root_id].def_id` so nested `pub use a::{b, c}` trees are properly marked reachable for `unreachable_pub`.
2. **Type-interface embargo phase (`rustc_privacy/src/lib.rs`, `effective_visibilities` L1780–1880 / `14210df0e` L1775–1879)**:
   - Clones `tcx.resolutions(()).effective_visibilities` and runs `check_invariants`.
   - **Unconditional RPIT/TAIT pass** (L1797–1839, whenever `!tcx.sess.opts.actually_rustdoc`): iterates over every opaque type `krate.opaques()`—except required-only trait methods (`TraitFn::Required`)—and invokes `visitor.reach_through_impl_trait(opaque.def_id, EffectiveVisibility::from_vis(Public)).generics().clauses().ty()` (`.predicates()` in `14210df0e`). Inside `ReachEverythingInTheInterfaceVisitor::visit_def_id` (L844–859), `max_vis` is `(self.level != Level::ReachableThroughImplTrait).then(|| self.ev.tcx.local_visibility(def_id))` (`None` here!), so concrete hidden types returned by `pub fn ... -> impl Trait` are unconditionally marked reachable at `Level::ReachableThroughImplTrait = Public` for codegen/monomorphization reachability, regardless of nominal visibility, and `visitor.queue.clear()` discards opaque-only enqueues before the worklist loop.
   - **Macro-reachable ADTs & worklist fixed point** (L1843–1871): visits macro-exposed struct fields (`macro_reachable_adts`), all `free_items` and `foreign_items`, and pops `visitor.queue` until convergence.
   - Whenever an item `d` (such as `pub trait PublicSealed: hidden::Sealed`) has an entry in `effective_visibilities` (e.g., `Public`), `EmbargoVisitor::check_def_id` visits its `generics`, `clauses`/`predicates`, `ty`, and (for `DefKind::Trait`) `associated_items` via `self.reach(def_id, item_ev)`, which invokes `update_eff_vis(comp, item_ev, Some(nominal_vis(comp)), Level::Reachable)`. For `Impl`s, `check_def_id` computes `EffectiveVisibility::of_impl::<true>` (`SHALLOW = true`, skipping generic type arguments per issue `#57264`, L620–637) and lifts the impl header's types and trait ref at `Level::Reachable`.
   - Finally, `TestReachabilityVisitor` (`L863–918`) prints all 4 levels on items annotated with `#![feature(rustc_attrs)] #[rustc_effective_visibility]`.

#### Live `#[rustc_effective_visibility]` Inspection (`probe_results.json` `b01`)

Running probe `b01` (`rustc --edition=2024 --crate-type=lib --emit=metadata`, `#![feature(rustc_attrs)] #![allow(dead_code, private_interfaces)]`) directly observes all five canonical regimes inside a single crate:

| Item in `b01.rs` | `Direct` | `Reexported` | `Reachable` | `ReachableThroughImplTrait` | Compiler Mechanism Observed |
| --- | --- | --- | --- | --- | --- |
| `pub struct DirectPub;` | `pub` | `pub` | `pub` | `pub` | Root-level public item: all 4 levels immediately `Public` in `rustc_resolve`. |
| `mod hidden { pub struct ReexportedItem; }` (`pub use hidden::ReexportedItem;` at root) | `pub(crate)` | `pub` | `pub` | `pub` | Direct ancestor `hidden` bottlenecks `Direct` at `pub(crate)`, while root `pub use` lifts `Reexported` (and thus `Reachable` + RPIT) to `pub`. |
| `mod hidden { pub trait Sealed {} }` (with `pub trait PublicSealed: hidden::Sealed {}`) | `pub(crate)` | `pub(crate)` | `pub` | `pub` | Not exported by any `pub use` -> `Reexported = pub(crate)`, but `PublicSealed`'s clause lifts `Reachable` to `min(Public, nominal(Sealed)) = pub`. |
| `mod hidden { pub trait UnusedPub {} }` | `pub(crate)` | `pub(crate)` | `pub(crate)` | `pub(crate)` | No `pub use` and no public interface reference -> reaches no higher than parent module `pub(crate)`. |
| `mod hidden { pub trait RpitTrait {} }` (`pub fn leak_rpit() -> impl hidden::RpitTrait`) | `pub(crate)` | `pub(crate)` | `pub` | `pub` | Opaque return type trait bound lifts `RpitTrait`'s `Reachable` to `pub`. |
| `mod hidden { pub struct RpitHidden; }` (returned via `leak_rpit`) | `pub(crate)` | `pub(crate)` | `pub(crate)` | `pub` | **Strict separation `ReachableThroughImplTrait > Reachable`**: opaque hidden type is NOT part of `leak_rpit`'s interface, so `Reachable` stays `pub(crate)` while `impl_trait_pass` lifts `ReachableThroughImplTrait` to `pub`. |
| `pub(crate) fn crate_fn_rpit() -> impl hidden::RpitTrait` | `"not in the table"` | — | — | — | `nominal_vis == private_vis` at crate root (`pub(crate)`): skipped by `may_update`, and `impl_trait_pass` records the opaque `OpaqueTy` (`opaque.def_id`), not the enclosing function. |

---

### 3. RFC 2145 Lints, `unreachable_pub`, and `E0446` Hard Errors

Basis: documentation/normative + source + execution (`rust-lang/rfcs` `f43d5789b`, `rust-lang/rust` `14210df0e` & `20fe935d5`, probes `b02`–`b08`, Lean Part 4).

#### Primary Interface vs. Secondary Interface (`private_interfaces` vs. `private_bounds`)

`SearchInterfaceForPrivateItemsVisitor` (`rustc_privacy/src/lib.rs` L1358–1528) tracks a single flag `in_primary_interface: bool` and checks every local `DefId` visited during interface traversal:

- **Methods setting `in_primary_interface = true` (`PRIVATE_INTERFACES`, warn-by-default)**: `generics()` (const parameter types and generic parameter default values, L1370–1382), `ty()` (function signature inputs/outputs, struct/enum field types, static/const types, type alias RHS, impl self type, L1402–1407), and `trait_ref()` (trait impl header `impl Trait for Type`, L1409–1415).
- **Methods setting `in_primary_interface = false` (`PRIVATE_BOUNDS`, warn-by-default)**: `clauses()` / `predicates()` (`explicit_clauses_of` / `explicit_predicates_of`—explicitly excluding compiler-inferred outlives predicates via `#![rustc_privacy]` note on RFC 2093, L1384–1394) and `bounds()` (`explicit_item_bounds` on opaque types and trait associated types, L1396–1400).

When visiting a local dependency `def_id` with nominal visibility `vis = tcx.local_visibility(local_def_id)`, lines L1466–1491 fire a lint iff:

```rust
let reachable_at_vis = *effective_vis.at_level(Level::Reachable);
if reachable_at_vis.greater_than(vis, self.tcx) {
    let lint = if self.in_primary_interface { PRIVATE_INTERFACES } else { PRIVATE_BOUNDS };
    ...
}
```

Two immediate consequences explain why canonical trait sealing compiles warning-free even under `#![deny(private_bounds, private_interfaces, unreachable_pub)]`:

1. **Nominal vs. Effective Visibility of `private::Sealed`**: In `mod private { pub trait Sealed {} }`, `Sealed` sits inside a private module, so `effective_vis.at_level(Level::Reexported)` is `pub(crate)`, yet `Sealed`'s **nominal** visibility `vis` is `Visibility::Public` (`pub`). Checking `pub trait PublicSealed: private::Sealed {}` tests `PublicSealed`'s `reachable_at_vis` (`Public`) against `Sealed`'s **nominal** visibility `vis` (`Public`): `Public.greater_than(Public)` is `false`! Thus **neither `private_bounds` nor `private_interfaces` fires**, verified live in probe `b02` (`rc=0`). Contrast probe `b05`: writing `trait CrateTrait {}` (nominal `pub(crate)`) in `pub trait BadSuper: CrateTrait {}` and `pub fn bad_generic<T: CrateTrait>(_x: T) {}` fails `Public.greater_than(pub(crate)) == true` in `clauses()` (`in_primary_interface = false`), emitting two `private_bounds` errors (`b05`, `rc=1`). Contrast probe `b06`: `struct PrivateType(u32); pub fn leak_iface() -> PrivateType` fails `Public.greater_than(pub(crate)) == true` in `ty()` (`in_primary_interface = true`), emitting `private_interfaces` (`b06`, `rc=1`).
2. **`unreachable_pub` Suppression (`compiler/rustc_lint/src/builtin.rs`)**: `UnreachablePub::perform_lint` (`20fe935d5` L1121–1133; `14210df0e` L1230–1242) returns immediately whenever `!cx.tcx.visibility(def_id).is_public() || cx.effective_visibilities.is_reachable(def_id)`. Here `is_reachable(def_id)` checks `effective_vis.at_level(Level::Reachable).is_public()`. Because `EmbargoVisitor` lifted `private::Sealed`'s `Level::Reachable` to `Public` via `PublicSealed`'s supertrait bound (`b01`), `unreachable_pub` stays silent on `private::Sealed` (`b02`, `rc=0`)! Meanwhile, `mod private { pub trait UnusedSealed {} }` has `Reachable = pub(crate)` (`b01`), so `is_reachable` is `false` and `#![deny(unreachable_pub)]` rejects it with `"unreachable pub item"` and suggestion `pub(crate)` (`b04`, `rc=1`).

*(Edge-case note on impl blocks: in `check_item`, `DefKind::Impl` at `lib.rs:1662-1699` intentionally checks using non-shallow `EffectiveVisibility::of_impl::<false>` and sets `check.skip_assoc_tys = true`, while skipping `generics().clauses()` on trait impls per `#90586` to avoid false positives such as `impl From<Priv> for Pub`.)*

#### `unnameable_types` vs. RFC 2145 Trivial Aliases, and Unconditional `E0446`

`PrivateItemsInPublicInterfacesChecker::check_unnameable` (`rustc_privacy/src/lib.rs` L1551–1575; `14210df0e` L1552–1576) is invoked on `TyAlias`, `Trait`, `Enum`, `Struct`, `Union`, and `ForeignTy` (`check_item` / `check_foreign_item`):

```rust
let reexported_at_vis = effective_vis.at_level(Level::Reexported);
let reachable_at_vis = effective_vis.at_level(Level::Reachable);
if reachable_at_vis.is_public() && reexported_at_vis != reachable_at_vis {
    self.tcx.emit_node_span_lint(UNNAMEABLE_TYPES, ...);
}
```

Probes `b03` and `b07` together with primary source inspection establish three nuances of `UNNAMEABLE_TYPES` (allow-by-default):

1. **Sealing triggers `unnameable_types`**: For `mod private { pub trait Sealed {} }` bound by `pub trait PublicSealed: private::Sealed {}`, `Sealed` has `reachable = pub` and `reexported = pub(crate)` (`!= pub`). Under `#![deny(unnameable_types)]`, probe `b03` fails (`rc=1`) with `"error: trait Sealed is reachable but cannot be named"` and label `"reachable at visibility pub, but can only be named at visibility pub(crate)"`.
2. **Crate-internal reachability stays silent**: Notice the explicit `reachable_at_vis.is_public()` guard! In probe `b07`:
   ```rust
   #![deny(unnameable_types)]
   mod outer {
       mod inner { pub struct InnerUnnameable(pub u32); }
       pub(in crate::outer) fn crate_internal_leak() -> inner::InnerUnnameable { ... }
   }
   ```
   Here `InnerUnnameable` has `reexported = pub(in crate::outer::inner)` and `reachable = pub(in crate::outer)` (`reexported != reachable`), yet `reachable` is **not** `Public`, so `#![deny(unnameable_types)]` does not fire (`b07`, `rc=0`).
3. **Divergence between RFC 2145 prose and `rustc` source (`TyAlias`)**: RFC 2145 (`text/2145-type-privacy.md` L452–455) originally proposed firing `unnameable_types` only when effective visibility exceeded where a type could be named *"either directly, or through reexports, or through trivial type aliases (`type X = Y;`, no generics on both sides)"*. In `rustc`'s actual implementation (`lib.rs` L1559), `check_unnameable` compares only `Level::Reexported != Level::Reachable` and does **not** exempt non-generic type aliases (though `check_unnameable` itself is also called on `DefKind::TyAlias` at L1613).

Finally, **associated types remain hard errors (`E0446`)**: inside `check_assoc_item` (`lib.rs` L1577–1597), `check.hard_error = is_assoc_ty` sets `hard_error = true` whenever `item.is_type()` (unless `item.container == AssocContainer::Trait`, where line L1591–1596 resets `check.hard_error = false` before `check.bounds()`). When `self.hard_error && self.required_visibility.greater_than(vis, self.tcx)` (`L1436`), `check_def_id` emits `InPublicInterface` (`diagnostics.rs` L70, `code = E0446`), bypassing lint levels completely. Probe `b08` places `#![allow(private_interfaces, private_bounds, dead_code)]` on `impl Tr for Pub { type Assoc = Priv; }` and confirms `rustc` still aborts with `error[E0446]: private type Priv in public interface` (`rc=1`).

---

### 4. Multi-Crate Sealed-Trait Enforcement, Diagnostics, and Escape Mechanisms

Basis: source + execution + derived (`rust-lang/rust` `14210df0e` & `20fe935d5`, probes `c00`–`c07`, Lean Parts 5 & 7).

#### Downstream Usability vs. Implementation Blocking (`c00`–`c04`)

In Part C, upstream crate `up` compiles cleanly (`c00`, `rc=0`) under `#![deny(private_bounds, private_interfaces, unreachable_pub)]` with:

```rust
mod private {
    pub trait Sealed {}
    impl Sealed for super::Token {}
}
pub struct Token(pub u32);
pub trait PublicSealed: private::Sealed { fn value(&self) -> u32; }
impl PublicSealed for Token { fn value(&self) -> u32 { self.0 } }
```

Downstream crate behavior falls cleanly into two classes:

- **Downstream consumers succeed (`c01`, `rc=0`)**: Generic functions bounded by `T: up::PublicSealed`, method calls (`x.value()`), upstream helper calls (`up::consume`), and dynamic dispatch (`&dyn up::PublicSealed`) all compile and run (`SEALED_CALL_OK=42,dyn=21`). None of those operations require the downstream caller to name or prove `private::Sealed` directly; generic callers satisfy `up::PublicSealed` from their bound or from an upstream-exported concrete witness `Token`.
- **Downstream implementors are blocked at two distinct phases (`c02`, `c03`, `c04`)**:
  - `impl up::PublicSealed for Local` (`c02`, `rc=1`): Name resolution finds `up::PublicSealed` cleanly, then trait/well-formedness checking fails supertrait obligation `Local: up::private::Sealed` with `error[E0277]`.
  - `impl up::private::Sealed for Local` (`c03`, `rc=1`): Path resolution rejects `up::private` immediately with `error[E0603]: module private is private` (note: `trait Sealed is not publicly re-exported`). Note that `pub(crate) trait Sealed` would similarly be unnameable externally (`E0603`, illustrated on `pub(crate) fn crate_only()` in `c04`), though putting `pub trait Sealed` inside `mod private` additionally avoids `private_bounds` on `pub trait PublicSealed: private::Sealed` inside crate `up`!

#### Exact `"sealed trait"` Diagnostic Heuristic (`suggestions.rs`)

When `E0277` fails on a trait bound `clause` for `trait_pred` (`def_id`), `rustc_trait_selection/src/error_reporting/traits/suggestions.rs` (`20fe935d5` L4000–4095; `14210df0e` L3580–3669) determines whether to display the `"sealed trait"` note:

1. If `def_id` is **local** (`def_id.as_local()`), and `trait_pred.self_ty()` is `ty::Adt(adt, _)`, it checks `tcx.resolutions(()).effective_visibilities.effective_vis(local)` at `Level::Reexported.is_accessible_from(adt.did(), tcx)`.
2. If `def_id` is **foreign** (cross-crate sealed trait, the downstream case in `c02` and `d03`–`d06`), it checks `tcx.visible_parent_map(()).get(&def_id).is_some()` (`20fe935d5` L4017 / `14210df0e` L3598).
3. Whenever `DefKind::Trait = tcx.def_kind(item_def_id) && !visible_item`, `rustc` emits:
   - `= note: '<short_item_name>' is a "sealed trait", because to implement it you also need to implement '<def_path_str>', which is not accessible; this is usually done to force you to use one of the provided types that already implement it`
   - `= help: the following type(s) implement the trait:` listing up to **8** concrete types from `tcx.all_impls(def_id)` (truncating with `\nand N others` when `len > 9`, L4082–4084). Both the `c02` single-type note and the 11-impl truncation (`and 3 others` on `d04`–`d06`) are directly confirmed in `probe_results.json`.

#### Escape Mechanisms and Non-Sealing Patterns (`c05`, `c06`, `c07`)

Three closely related patterns test the boundaries of sealed traits:

1. **Re-export escape (`c05`, `rc=0`, stdout `ESCAPE_OK`)**: Adding a single `pub use private::LeakySealed;` at the public crate root lifts `LeakySealed`'s `Reexported` level to `Public`. A downstream crate then writes `impl up::LeakySealed for Local {}` and `impl up::PublicFromLeaky for Local { ... }` with zero errors or warnings. Sealing therefore depends **globally** on every path (`direct` module parent chain AND every `pub use` edge) into the private sealing trait staying blocked at `Level::Reexported`.
2. **`#[doc(hidden)]` does NOT seal (`c06`, `rc=0`, stdout `DOC_HIDDEN_NOT_SEALED`)**: Declaring `#[doc(hidden)] pub mod doc_hidden { pub trait NotSealed {} }` leaves `NotSealed` with `Direct = Reexported = Reachable = Public`. `#[doc(hidden)]` affects documentation rendering and IDE diagnostics only—`rustc_privacy` never consults it, and downstream crates freely implement both `up::doc_hidden::NotSealed` and `up::DocHiddenSuper` for local types.
3. **Method-signature witness trait sealing (`c07`, `rc=1`, `E0121`)**: Placing an unnameable parameter type `private::Witness` in a trait method signature (`fn secret(&self, _w: private::Witness) -> u32`) blocks downstream explicit signatures (`E0603`) and `_` placeholders (`E0121`: `"the placeholder _ is not allowed within types on item signatures for methods"`, verified in `c07`). However, unlike supertrait sealing (`b02`, zero lints), `MethodSigHidden` places `private::Witness` inside `ty()` (`in_primary_interface = true`) or `fn_sig`, triggering `private_interfaces` (`b06`) and requiring `#[allow(private_interfaces, unreachable_pub)]` on the trait in `up.rs` (`c00`), and any default trait method body or macro generating the impl within reach could inspect or omit overrides—making supertrait sealing strictly cleaner.

---

### 5. Real `google/zerocopy` Sealing Enforcement & Anneal Capture Boundary

Basis: source + execution + derived (`google/zerocopy` `907b9175f` & `eb65abdac`, `joshlf/anneal` `c131b320e`, probes `d01`–`d07`, Lean Part 6–7).

#### Audited `zerocopy` Sealed Traits (`byteorder.rs` and `pointer/invariant.rs`)

Both `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` and upstream `main` (`eb65abdaca712af129ba4ebb67a09e78c635a6cf`) use supertrait sealing for two foundational API families:

1. **`zerocopy::byteorder::ByteOrder` (`zerocopy/src/byteorder.rs` L87–118)**:
   - `pub trait ByteOrder: Copy + Clone + Debug + Display + Eq + PartialEq + Ord + PartialOrd + Hash + private::Sealed { const ORDER: Order; }`
   - `mod private { pub trait Sealed {} impl Sealed for super::BigEndian {} impl Sealed for super::LittleEndian {} }`
   - The `unsafe`-free closed domain `{BigEndian, LittleEndian}` ensures downstream generic consumers can rely on `Order` exhaustiveness (`BigEndian` / `LittleEndian`), verified in `d02` (`rc=0`, `ZC_SEALED_OK=true,be=BE,le=LE,...`) and rejected on downstream `LocalOrder` with `E0277` `"sealed trait"` (`d03`, `rc=1`, listing `zerocopy::BigEndian` and `zerocopy::LittleEndian`).
2. **`zerocopy::pointer::invariant` (`zerocopy/src/pointer/invariant.rs` L19–117, 288–309)**:
   - `pub trait Invariants: Sealed` (implemented only for triples `(A: Aliasing, AA: Alignment, V: Validity)`, L25–29)
   - `pub trait Aliasing: Sealed` (`Shared`, `Exclusive`, L37, 129–144, 294–295)
   - `pub trait Alignment: Sealed` (`Unaligned`, `Aligned`, L44, 147–174, 297–298)
   - `pub unsafe trait Validity: Sealed` (`Uninit`, `AsInitialized`, `Initialized`, `Safe`, L100, 178–239, 300–303)
   - `pub trait Reference: Aliasing + Sealed {}` (`Shared`, `Exclusive`, L117, 133, 144)
   - `mod sealed { pub trait Sealed {} ... }` (L288–309) also implements `Sealed` for `(A: Sealed, AA: Sealed, V: Sealed)`, `BecauseImmutable`, and `BecauseExclusive`.
   - Look closely at the `Safety` contract on `Reference` (`invariant.rs` L113–116): *"Given `A: Reference`, callers may assume that either `A = Shared` or `A = Exclusive`."* Because `Ptr<'a, T, I>` and `Alignment::read` base aliasing and dereferenceability assumptions on `I::Aliasing: Reference` (using `const IS_EXCLUSIVE: bool` and `Ptr::into_shared` / `Ptr::as_ref`), compiler-enforced sealing is **load-bearing for memory safety**—even though `Reference` itself is a **safe** (non-`unsafe`) trait, sealing guarantees no downstream crate can forge a third `Reference` type whose `IS_EXCLUSIVE` or aliasing semantics could bypass shared/exclusive soundness invariants!
   - Probes `d04` (`Alignment`), `d05` (`unsafe impl Validity`), and `d06` (`Aliasing`, `Reference`, `Invariants`) all compile-fail (`rc=1`) with `E0277` citing `invariant::sealed::Sealed`, `"sealed trait"`, and listing all 11 upstream `Sealed` impls (truncated after 8 with `and 3 others`).

#### Contrast: Unsealed `Read<A, R>` and `#[allow(unreachable_pub)]` Re-Export Pattern

Not every trait in `zerocopy::pointer::invariant` is sealed, and inspecting why illuminates intentional API design boundaries:

- **`pub trait Read<A: Aliasing, R> {}` (`invariant.rs` L273–286)**: Implemented for `T: ?Sized + Immutable` with `(A, BecauseImmutable)` and for all `T: ?Sized` with `(Exclusive, BecauseExclusive)`. `Read` intentionally does **not** carry `: Sealed`, and probe `d07` (`impl Read<Shared, LocalReason> for LocalTy {}`, `rc=0`, stdout `READ_UNSEALED_OK=true`) proves downstream crates CAN implement `Read` freely for local types or local reasons! Why does that remain sound? Because `Alignment::read` (`invariant.rs` L47–51) requires BOTH `I::Aliasing: Reference` (sealed to `{Shared, Exclusive}`), `I::Validity = Safe`, `T: Copy + Read<I::Aliasing, R>`, AND internally executes `Ptr::as_ref` (`L157`, `L172`), which independently validates whether dereferencing `Shared` requires `T: Immutable`—so a downstream `impl Read<Shared, LocalReason> for LocalTy` cannot unlock unsound unsynchronized reads on interior-mutable `T`.
- **`#[allow(unreachable_pub)]` on private-module `pub use` re-exports (`zerocopy/src/pointer/ptr.rs` L111–112, L834–835; `zerocopy/src/wrappers.rs` L605–607)**: `zerocopy` suppresses `unreachable_pub` on items such as `mod def { pub struct Ptr<...>; }` re-exported via `pub use def::Ptr;` (plus `TryWithError`, `ReadOnly`) with inline comment `// This is a false positive on our MSRV toolchain.`—reflecting historical compiler versions where `EffectiveVisibilitiesVisitor` or `UnreachablePub` did not always treat every re-export or MSRV construct symmetrically with modern `is_reachable` tracking.

#### Sealed Traits + Orphan Rule Composition for Defining-Crate Fixity

A key analytical finding—surfaced explicitly while constructing the machine-checked proofs in `PrivacyVisibilityLatticeAndSealedTraitSoundness.lean`—is that **sealing alone does not prevent a downstream crate from adding impls of an upstream public trait on an upstream public type**; rather:

1. **Sealing (`E0603` + `E0277`)** prevents downstream crates from implementing `pubTrait` for **downstream** types (`τ` owned by crate `c_ext != c_0`) because `sealedTrait` cannot be named externally, so crate `c_ext` cannot implement `sealedTrait`, and trait well-formedness (`E0277`) refuses `impl pubTrait` without `τ: sealedTrait` (and `c_0` itself cannot pre-implement `sealedTrait` for foreign downstream types it cannot depend on).
2. **Orphan checking (`E0117`)** prevents downstream crates from implementing `pubTrait` on **upstream** types owned by `c_0` (such as `BigEndian`, `LittleEndian`, `Shared`, `Exclusive`) even when `c_0` already implemented `sealedTrait` for those exact types! Without the orphan rule in `ValidWorld`, a downstream crate could satisfy `Shared: Reference` (`Shared` already implements `sealed::Sealed` and `Aliasing` in `zerocopy`) or forge `impl<T> ...` over upstream types.
3. Together, `(Sealing + Defining-Crate Closure on private::Sealed + Orphan Locality)` strictly yields **Complete Defining-Crate Fixity**: every `impl` of `pubTrait` anywhere in the multi-crate program MUST originate inside defining crate `c_0` AND have `Self` inside `c_0`'s finite allowlist (`Theorem 3b`, `sealed_trait_closed_world_invariant`).

#### Anneal `rustc-capture` and `noncomputable` TCB Alignment (`joshlf/anneal@c131b320e`)

In `joshlf/anneal/trusted/rustc-capture/src/driver.rs` (`L25–150`), `AnalysisCallbacks::after_analysis` (`L75–84`) captures compiler data only after `self.analysis_reached = tcx.dcx().has_errors().is_none()` and `rustc_driver::run_compiler` finishes cleanly without post-analysis diagnostics (`L137–147`). Because `check_mod_privacy` (`E0451`, `ItemIsPrivate`), `check_private_in_public` (`E0446`, `#![deny(...)]` lint promotions), and trait solving (`E0277` sealed-trait violations) all execute before/during analysis cleanly prior to `Compilation::Continue`, verified MIR extracted by Anneal already enjoys all closed-world guarantees of `rustc_privacy` and orphan checks. Furthermore, `anneal/trusted/lean/Trusted/MirAst.lean` (`L75–92`) mandates explicit `noncomputable` on every value `def` (while forbidding `noncomputable section`) so Lean 4 never emits `._unsafe_rec` `partial` codegen helpers rejected by `TrustedBoundary.validateRepoConstant`—the exact discipline verified below in our Lean 4 formalization.

---

### 6. Kernel-Checked Lean `v4.34.1` Formalization

Basis: source + execution (`PrivacyVisibilityLatticeAndSealedTraitSoundness.lean`, Lean `v4.34.1` strict batch execution & MetaM inspection).

`support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean` (1,928 lines, 80,967 bytes) formalizes `rustc`'s module-tree visibility lattice, four-level `EffectiveVisibilities`, RFC 2145 lint triggers, cross-crate sealed-trait unnameability, closed-world soundness of `google/zerocopy`, and all counterexamples in pure constructive Lean without importing `Mathlib` or using any automation outside kernel reduction and explicit structural proofs.

#### Purity and Audit Metrics (`MetaM` Environment Verification)

Strict Lean `v4.34.1` compilation (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) exited `0` with zero warnings, and a `Lean.MetaM` inspection pass over every local constant declared in `RustcPrivacyLattice` verified:

| Metric | Observed Value | Enforcement Detail |
| --- | --- | --- |
| Source size | `1,928` lines / `80,967` bytes | Standalone module (`import Lean` absent; pure Lean core prelude only) |
| Local declarations | `516` total constants (`291` defs, `144` theorems) | Every single term/value `def` marked `noncomputable def` |
| `._unsafe_rec` helpers | `0` | Verified across all `env.constants` (`none` containing `._unsafe_rec`) |
| `partial` / `unsafe` defs | `0` / `0` | Zero `partial`, zero `unsafe`, zero `deriving DecidableEq`/`Repr` on inductives |
| Forbidden tactics/axioms | `0` | Zero `sorry`/`sorryAx`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `ofReduceBool` |
| Kernel axioms across all 144 theorems | Only `[propext]` | Majority of lattice/closed-world theorems use **0** axioms (`[]`); `propext` enters solely via `Bool`-to-`Prop` iff bridges (`isPrefixBool_true_iff`, `visLeqBool_true_iff`, `boolAnd_true_left`) and `rw`/`subst` equality rewrites on `CrateWorld` fields in `zerocopy_closed_world_soundness`, `reexport_escape_breaks_sealing`, and `master_privacy_and_sealing_soundness`. |

*(Note: in Lean `v4.34.1`, `public` is a reserved module-system keyword, so the constructor for `Visibility::Public` is named `.visPublic`.)*

#### Formalized Architecture and Core Theorems (`Parts 1`–`8`)

| Part | Core Definitions (`PrivacyVisibilityLatticeAndSealedTraitSoundness.lean`) | Key Proved Theorems & Statements |
| --- | --- | --- |
| **Part 1** (`L90–428`) | `ModPath { crate, segs }`, `IsPrefix`, `IsAncestor`, `lcp` (longest common prefix), `parentMod` | `isPrefix_refl`, `isPrefix_trans`, `isPrefix_antisymm`, `lcp_isPrefix_left`, `lcp_isPrefix_right`, `isPrefix_lcp_greatest`, `isAncestor_refl`, `isAncestor_trans`, `isAncestor_antisymm`, `crateRoot_isAncestor_of_all`, `parentMod_isAncestor`, `parentMod_of_childMod`. |
| **Part 2** (`L429–749`) | `Visibility := visPublic \| restricted ModPath`, `IsAccessibleFrom`, `VisLeq`, `VisLt`, `visJoin` (via `lcp`), `visMin` | `visLeq_refl`, `visLeq_trans`, `visLeq_antisymm`, `visLeq_public_top`, `visLeq_public_only_public`, `pubCrate_dominates_local`, `validRestriction_covers_defMod`, `pubSelf_le_pubSuper`, **`visLeq_iff_pointwise_accessible`** (`VisLeq v₁ v₂ ↔ ∀ caller, IsAccessibleFrom v₁ caller → IsAccessibleFrom v₂ caller`), `sibling_visibilities_incomparable`, `cross_crate_visibilities_incomparable`, `non_ancestor_sibling_invalid_e0742`, `visJoin_left_le`, `visJoin_right_le`, `visJoin_least`, `visMin_ordered_le_both`. |
| **Part 3** (`L750–891`) | `EffectiveVisibility`, `EffVisWellFormed` (`priv <= direct <= reexported <= reachable <= rpit` and `reachable <= nominal`), `liftVis`, `markInterfaceReachable`, `markRpitReachable` | `effVis_fromVis_wellFormed`, `effVis_reexported_le_nominal`, `effVis_direct_le_nominal`, `effVis_reachable_public_implies_nominal_public`, `effVis_reexported_public_implies_reachable_public`, `effVis_direct_public_implies_reexported_public`, `liftVis_mono_left`, `liftVis_preserves_upper`, `markInterfaceReachable_preserves_wellFormed`, `markRpitReachable_preserves_wellFormed`, **`rpit_hidden_type_exceeds_nominal`**. |
| **Part 4** (`L892–1068`) | `ItemInterface`, `FiresPrivateInterfaces`, `FiresPrivateBounds`, `FiresUnnameableTypes`, `FiresUnreachablePub`, `FiresAssocTyHardError` | **`sealed_trait_lint_matrix`** (witnesses `PublicSealed: private::Sealed` passes `private_bounds`, `private_interfaces`, and `unreachable_pub`, while firing `unnameable_types`), `unused_pub_in_private_mod_fires_unreachable_pub`, `crate_private_bounds_and_interfaces_fire`, **`crate_internal_unnameable_silent`** (`b07`), `assoc_type_private_fires_e0446` (`b08`). |
| **Part 5** (`L1069–1346`) | `CrateWorld`, `ModExternallyExported`, `NameableExternally`, `CanNameTrait`, `SupertraitReachable`, `PathCrossesNonPublic`, `UnexportedTrait`, `ValidWorld` (incorporating nameability + orphan rule + supertrait closure) | `supertraitReachable_trans`, **`pathCrossesNonPublic_blocks_modExport`**, **`unexportedTrait_not_nameableExternally`**, `unexportedTrait_cannot_name_external`, `validWorld_supertrait_closure`, **`unnameable_supertrait_blocks_external_impl`**, **`external_type_cannot_impl_sealed_trait`**. |
| **Part 6** (`L1347–1621`) | `SealedTraitSpec`, `zcTraits`, `zcModVis`, `zcTypeOwner` | **`sealed_trait_closed_world_types`** (`Mem im.selfType spec.allowedTypes` solely via unnameability), **`sealed_trait_closed_world_invariant`** (`Mem im.selfType spec.allowedTypes ∧ im.inCrate = spec.c₀` via sealing + orphan composition), `zcPrivMod_unexported`, **`zerocopy_closed_world_soundness`** (simultaneously proves `Reference ∈ {Shared, Exclusive}`, `ByteOrder ∈ {BigEndian, LittleEndian}`, `Alignment ∈ {Unaligned, Aligned}`, `Validity ∈ {Uninit, AsInitialized, Initialized, Safe}`, all implemented strictly in crate `0`). |
| **Part 7** (`L1622–1869`) | `escapeWorld`, `docHiddenWorld`, `unsealedRefWorld` | **`reexport_escape_breaks_sealing`** (`pub use private::LeakySealed;` yields `ValidWorld` with downstream `LocalTy ≠ Token` implementing `PublicFromLeaky`), **`doc_hidden_mod_does_not_seal`**, **`unsealed_reference_allows_forged_aliasing`** (omitting `: Sealed` on `Reference` admits `tyBogus ∉ {Shared, Exclusive}`). |
| **Part 8** (`L1870–1928`) | Concrete witnesses + top-level conjunction | **`concrete_pub_in_a_dominance_witness`** (`a01`–`a03`), **`master_privacy_and_sealing_soundness`** (single unified theorem composing lattice equivalence, RFC 2145 lint matrix, closed-world fixity, re-export escape, and `#[doc(hidden)]` non-sealing). |

---

## Boundaries

The following negative space and scope boundaries qualify the findings above:

- **`not examined` — Direct binary execution of `rust-lang/rust` `20fe935d50367c0ff8872c2ebfa050c5c99d9201` (`main`)**: Only `14210df0e` (`rustc 1.98.0-nightly`) was executed live; `20fe935d5` was audited directly from primary compiler source, and runtime behavior on `20fe935d5` for newly added arms (`ty::View`, nested `pub use` `root_id` updates) is inferred from source rather than executed.
- **`not examined` — Rust Edition 2015 `pub(in path)` resolution, proc-macro hygiene, and ambiguous glob re-exports**: All live compiler probes tested Edition 2024 (and Edition 2021 for `zerocopy`). Edition 2015's root-relative `pub(in a::b)` syntax (`r[vis.scoped.edition2018]`), declarative/proc-macro `SyntaxContext` hygiene interactions inside `NamePrivacyVisitor::check_field`, and `UseKind::Glob` ambiguity exceptions in `EffectiveVisibilities::check_invariants` (`middle/privacy.rs` L191–195) were not probed empirically.
- **`not examined` — `export_private_dependencies` and Rustdoc output rendering (`actually_rustdoc = true`)**: `SearchInterfaceForPrivateItemsVisitor::leaks_private_dep` (`rustc_privacy/src/lib.rs` L1418–1429) and `EmbargoVisitor`'s `impl_trait_pass = !tcx.sess.opts.actually_rustdoc` branch (`L1797`) were inspected in source but not executed with private dependencies or `rustdoc`.
- **`not examined` — Additional `zerocopy` sealed traits outside `byteorder` and `pointer::invariant`**: Other sealed traits across `zerocopy` (such as internal `util` or derive-macro helper traits) were not inventoried exhaustively; execution covered `ByteOrder` and the core `pointer::invariant` hierarchy (`Invariants`, `Aliasing`, `Alignment`, `Validity`, `Reference`, and unsealed `Read`).
- **`known not to apply` — Closed-world type exclusivity when crate `c₀` provides a blanket `impl` of `private::Sealed`**: A trait `pub trait Public: private::Sealed` fixes its implementor set to a finite list of concrete types **only** when the defining crate `c₀` restricts `impl private::Sealed` to those types (`hclosedDef` in `SealedTraitSpec`). If `c₀` writes `impl<T: Clone> private::Sealed for T {}` (a partially sealed blanket pattern where `Public` adds extra items or `where` bounds), external crates can implement `Public` for any `Clone` type, so `c₀`-finite type closure does not hold.
- **`known not to apply` — Unsealed method-signature witness sealing without lint opt-out**: Placing a private type directly in a trait method parameter (`MethodSigHidden` in `c07`) requires `#[allow(private_interfaces)]` under warn-by-default RFC 2145 lints (`private_interfaces`), unlike supertrait sealing (`b02`), which triggers zero default-on lints (`unnameable_types` is `Allow` by default).
- **`known not to apply` — Standalone Lean formalization integration with `joshlf/anneal`'s `Trusted.MirSemantics`**: `support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean` is a standalone, self-contained mechanization of `rustc`'s module-tree visibility lattice, `EffectiveVisibilities`, RFC 2145 lint conditions, and crate-level `TraitImpl` coherence; it models nominal types (`TypeId`, `typeOwner`) and HIR/ty-level visibility rules rather than embedding `rustc` generics/blanket-impl overlap or linking against `Trusted.MirAst`.
- **`unsupported` — Suppressing `E0446` on impl associated types or coercing sibling visibilities**: `#![allow(private_interfaces, private_bounds)]` cannot downgrade `InPublicInterface` (`E0446`) on associated type implementations (`b08`), and Rust syntax offers no join/union visibility modifier across two disjoint sibling modules short of their shared least-common-ancestor module (`lcp`), even though `rustc`'s internal `RestrictionKind::stricter_of` / `visMin` compute meets within the module tree.

---

## Evidence

### 1. Primary Upstream Source Anchors

| Repository & Commit | File Path | Symbols & Verified Line Ranges | Evidence Role |
| --- | --- | --- | --- |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_middle/src/ty/mod.rs` | `Visibility<Id = LocalDefId>` (L311–336), `TyCtxt::{def_id_partial_cmp, is_descendant_of}` (L378–408), `Visibility::{to_def_id, is_accessible_from, partial_cmp, greater_than}` (L424–471) | `source` |
| `rust-lang/rust` @ `20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_middle/src/ty/mod.rs` | `Visibility<Id = LocalModId>` (L257–281), `RestrictionKind::{is_allowed_in, stricter_of}` (L285–342), `TyCtxt::{def_id_partial_cmp, is_descendant_of}` (L384–418), `Visibility::{to_mod_id, is_accessible_from, partial_cmp, greater_than}` (L435–483) | `source` |
| `rust-lang/rust` @ `14210df0e` / `20fe935d5` | `compiler/rustc_middle/src/middle/privacy.rs` | `Level` (`ReachableThroughImplTrait`, `Reachable`, `Reexported`, `Direct`), `EffectiveVisibility::{at_level, from_vis, min}`, `EffectiveVisibilities::{is_reachable, check_invariants, update}` (`20fe935d5` L21–278; `14210df0e` L21–277) | `source` |
| `rust-lang/rust` @ `14210df0e` / `20fe935d5` | `compiler/rustc_resolve/src/effective_visibilities.rs` | `EffectiveVisibilitiesVisitor::{compute_effective_visibilities, set_bindings_effective_visibilities, may_update, update_import, update_def}` (`14210df0e` L80–215; `20fe935d5` adds `import.root_id` L113–117 and cycle-guarded `update_decl_chain` L145–170) | `source` |
| `rust-lang/rust` @ `14210df0e` / `20fe935d5` | `compiler/rustc_privacy/src/lib.rs` | `DefIdVisitorSkeleton` (`ty::View`, `CompressedTrait` L158, L187 in `20fe935d5`), `VisibilityLike::of_impl` (`20fe935d5` L370–419 / `14210df0e` L365–414), `EmbargoVisitor` & `ReachEverythingInTheInterfaceVisitor::visit_def_id` (`20fe935d5` L483–859), `TestReachabilityVisitor` (L863–918), `NamePrivacyVisitor::check_field` (L925–1015), `TypePrivacyVisitor::check_def_id` (L1123–1171), `SearchInterfaceForPrivateItemsVisitor` (`20fe935d5` L1358–1528 / `14210df0e` L1353–1527), `PrivateItemsInPublicInterfacesChecker::{check_unnameable, check_assoc_item, check_item}` (`20fe935d5` L1530–1734), `check_mod_privacy`, `effective_visibilities` RPIT pass, `check_private_in_public` (`20fe935d5` L1745–1890 / `14210df0e` L1745–1889) | `source` |
| `rust-lang/rust` @ `14210df0e` / `20fe935d5` | `compiler/rustc_privacy/src/{errors.rs, diagnostics.rs}` | `FieldIsPrivate` (`E0451`, L6–25), `ItemIsPrivate` (uncoded, L51–59), `InPublicInterface` (`E0446`, L69–80), `UnnameableTypesLint` (L98–109), `PrivateInterfacesOrBoundsLint` (L114–127) | `source` |
| `rust-lang/rust` @ `14210df0e` / `20fe935d5` | `compiler/rustc_lint_defs/src/builtin.rs` & `compiler/rustc_lint/src/builtin.rs` | `PRIVATE_INTERFACES` (`20fe935d5` L4360 / `14210df0e` L4359), `PRIVATE_BOUNDS` (L4389 / L4388), `UNNAMEABLE_TYPES` (L4422 / L4421), `UNREACHABLE_PUB` & `UnreachablePub::perform_lint` (`20fe935d5` L1110–1165 / `14210df0e` L1219–1275) | `source` |
| `rust-lang/rust` @ `14210df0e` / `20fe935d5` | `compiler/rustc_trait_selection/src/error_reporting/traits/suggestions.rs` | `E0277` `"sealed trait"` detection (`effective_vis` / `visible_parent_map` + `all_impls` up to 8 types; `20fe935d5` L4000–4095 / `14210df0e` L3580–3669) | `source` |
| `google/zerocopy` @ `907b9175fee081872ec883ca4709e6ad922f8ed0` (`0.8.64`) & `eb65abdaca712af129ba4ebb67a09e78c635a6cf` | `zerocopy/src/byteorder.rs`, `zerocopy/src/pointer/invariant.rs`, `zerocopy/src/pointer/ptr.rs`, `zerocopy/src/wrappers.rs`, `zerocopy/src/lib.rs` | `ByteOrder: ... + private::Sealed` (`byteorder.rs` L87–99); `Invariants`, `Aliasing`, `Alignment`, `unsafe trait Validity`, `Reference`, unsealed `Read`, `mod sealed` (`invariant.rs` L19–309); `Ptr::as_ref` & `Ptr::into_shared` safety proofs relying on `I::Aliasing: Reference` exclusivity to `{Shared, Exclusive}` (`ptr.rs` L227–273, L675–685); `#[allow(unreachable_pub)]` on `pub use def::Ptr`, `pub use _casts::TryWithError`, `pub use read_only_def::*` (`ptr.rs` L111–112, L834–835; `wrappers.rs` L605–607) | `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean` | `AnalysisCallbacks::after_analysis` (`tcx.dcx().has_errors().is_none()`, L75–84, L137–150); `noncomputable` TCB policy forbidding `._unsafe_rec` / `noncomputable section` (`MirAst.lean` L75–92) | `source` |
| `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/visibility-and-privacy.md` | `r[vis]`, `r[vis.access]`, `r[vis.scoped]`, `r[vis.reexports]` (L1–214) | `normative` |
| `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | `text/2145-type-privacy.md` | Effective visibility design, primary vs. secondary interface split, `private_interfaces`, `private_bounds`, `unnameable_types` rationale and alias nuance (L410–475) | `documentation` / `normative` |

### 2. Preserved Package Support Artifacts (`support/`)

All machine-checked proofs and compiler probes are preserved inside this report package under `support/`:

1. **`support/probe_visibility_sealed_traits.py`** (`953` lines, Python `>= 3.10` stdlib only; `execution`): Executes all 33 `rustc` probe compilations and binary executions cleanly inside `tempfile.TemporaryDirectory()`, scrubs host/temp paths into `<tmp>/...` and `google/zerocopy:...`, parses `#[rustc_effective_visibility]` outputs (`b01`), and emits `probe_results.json`.
   - Part A (`a01`–`a07`, 10 runs): verifies `pub(in crate::a)` descendant access vs. sibling `E0603`, `pub(self)` parent `E0603`, non-ancestor `E0742`, re-export short-circuit vs. direct `E0603`, `E0616` vs. `E0451` field privacy, and `TypePrivacyVisitor` uncoded hard error under `#![allow(private_interfaces)]`.
   - Part B (`b01`–`b08`, 8 runs): extracts exact `#[rustc_effective_visibility]` tuples (`b01`), verifies `b02` (`rc=0`), `b03` (`unnameable_types` on `private::Sealed`), `b04` (`unreachable_pub`), `b05` (`private_bounds`), `b06` (`private_interfaces`), `b07` (`unnameable_types` silence on `pub(in crate::outer)`), and `b08` (`E0446` associated-type hard error).
   - Part C (`c00`–`c07`, 8 runs): compiles upstream `up` (`rc=0`), runs downstream consumer (`c01`, `SEALED_CALL_OK=42,dyn=21`), verifies `E0277` (`"sealed trait"`, `c02`), `E0603` (`c03`, `c04`), re-export escape (`c05`, `ESCAPE_OK`), `#[doc(hidden)]` non-sealing (`c06`, `DOC_HIDDEN_NOT_SEALED`), and method-sig placeholder rejection (`c07`, `E0121`).
   - Part D (`d01`–`d07`, 7 runs): compiles `zerocopy 0.8.64` (`d01`, `rc=0`), runs downstream sealed usage (`d02`, `ZC_SEALED_OK=true,be=BE,le=LE,shared_ex=false,excl_ex=true`), confirms `E0277` `"sealed trait"` rejection on `ByteOrder` (`d03`), `Alignment` (`d04`), `unsafe impl Validity` (`d05`), `Aliasing`/`Reference`/`Invariants` (`d06`), and compiles unsealed `Read<Shared, LocalReason>` (`d07`, `READ_UNSEALED_OK=true`).
2. **`support/probe_results.json`** (`406` lines; `execution`): Exact verbatim JSON transcript captured from `probe_visibility_sealed_traits.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` + `zerocopy 0.8.64` (`33` probe runs, `12` `rc=0`, `21` `rc=1`), observed on `2026-11-24`.
3. **`support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean`** (`1,928` lines, `80,967` bytes; `derived` + `execution`): Standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked formalization (`291` `noncomputable def`s, `144` theorems, `0` `sorry`, `0` `._unsafe_rec`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, only kernel axiom `[propext]`), observed passing `-DwarningAsError=true` on `2026-11-24`.

## Revalidation

All findings and theorems can be revalidated independently with zero external Python packages or Mathlib dependencies.

### 1. Re-run Live `rustc` Visibility, RFC 2145, Sealed-Trait, and `zerocopy` Probes

Run the preserved harness from this package directory against any target `rustc` binary and optional `zerocopy` checkout (omitting `--zerocopy-src` runs Parts A–C standalone, `26` probes; supplying `zerocopy/src/lib.rs` enables all `33` probes including Part D):

```console
python3 support/probe_visibility_sealed_traits.py \
  --zerocopy-src /path/to/zerocopy/zerocopy/src/lib.rs \
  --out /tmp/reval_probe_results.json
```

Expected invariants to check against `support/probe_results.json`:

1. `b01_rustc_effective_visibility_inspection`: `RpitHidden` reports `Direct: pub(crate), Reexported: pub(crate), Reachable: pub(crate), ReachableThroughImplTrait: pub`, and `hidden::Sealed` reports `Reexported: pub(crate), Reachable: pub`.
2. `b02` (`rc=0`), `b03` (`unnameable_types` on `Sealed`), `b07` (`unnameable_types` silent under `pub(in crate::outer)`, `rc=0`), `b08` (`E0446` despite `#![allow(private_interfaces, private_bounds)]`).
3. `c02` and `d03`–`d06` (`E0277` with `= note: ... is a "sealed trait"`), `c05` (`ESCAPE_OK`), `c06` (`DOC_HIDDEN_NOT_SEALED`), and `d07` (`READ_UNSEALED_OK=true`).

### 2. Re-verify the Lean `v4.34.1` Kernel Formalization and `0` `._unsafe_rec` Purity

Typecheck `support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean` with Lean `v4.34.1` kernel checking strictly enabled and warnings treated as errors:

```console
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean
```

To independently verify zero `._unsafe_rec` helpers, zero `partial` constants, zero `sorryAx`, zero `Classical.choice`, and `[propext]`-only axiom usage via Lean's own `MetaM` environment API (adjust only `support/` path if run from outside the package directory):

```console
lean --stdin <<'EOF'
import Lean
open Lean in
#eval show IO Unit from do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let input ← IO.FS.readFile "support/PrivacyVisibilityLatticeAndSealedTraitSoundness.lean"
  let some env ← Elab.runFrontend input {} "PrivacyVisibilityLatticeAndSealedTraitSoundness.lean" `Main
    | throw (IO.userError "elab failed")
  let mut unsafeRecs := 0
  let mut partials := 0
  let mut axioms : Std.HashSet Name := {}
  for (n, c) in env.constants.toList do
    if (toString n).startsWith "RustcPrivacyLattice." then
      if (toString n).endsWith "._unsafe_rec" then unsafeRecs := unsafeRecs + 1
      if c.isPartial then partials := partials + 1
      let (axArr, _) ← Core.CoreM.toIO (Lean.collectAxioms n) { fileName := "<check>", fileMap := default } { env := env }
      for a in axArr do
        axioms := axioms.insert a
  IO.println s!"unsafe_rec={unsafeRecs} partials={partials} axioms={axioms.toList}"
EOF
```

Expected output: `unsafe_rec=0 partials=0 axioms=[propext]` (with exit code `0`; ensure `lean` is in `PATH` and `LEAN_SYSROOT` resolves to the matching toolchain).

### 3. Upstream Differential Watchlist

When updating this report for newer `rust-lang/rust` or `google/zerocopy` commits, diff only the five high-leverage compiler regions:

1. `compiler/rustc_middle/src/ty/mod.rs` (`Visibility`, `RestrictionKind`, `def_id_partial_cmp`, `is_descendant_of`, `greater_than`) and `middle/privacy.rs` (`Level`, `EffectiveVisibilities::check_invariants`).
2. `compiler/rustc_resolve/src/effective_visibilities.rs` (import chains, `may_update`, `unreachable_pub` root tracking).
3. `compiler/rustc_privacy/src/lib.rs` (`EmbargoVisitor` RPIT pass, `SearchInterfaceForPrivateItemsVisitor` primary vs. secondary classification, `check_unnameable` trivial-alias rule if RFC 2145 is later extended to exempt non-generic aliases, `check_assoc_item` `hard_error` if `E0446` transitions into RFC 2145 lints, and `TypePrivacyVisitor`).
4. `compiler/rustc_trait_selection/src/error_reporting/traits/suggestions.rs` (`"sealed trait"` diagnostic heuristic).
5. `google/zerocopy`: `zerocopy/src/{byteorder.rs, pointer/invariant.rs}` for any new sealed markers, `pub use` re-exports from `private`/`sealed`, or changes to `Read`'s unsealed signature.
