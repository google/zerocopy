# `rustc` Name Resolution, Stable Item Identity (`DefId` vs. `DefPathHash`), Block-Local Nested Items, and Type Alias Lowering

## Summary

This report synthesizes four investigations into how `rustc` resolves source identifiers, assigns per-session `DefId` handles and cross-session `DefPathHash` fingerprints, identifies block-local items and closures, and lowers ordinary vs. associated/opaque type aliases across `nightly` (`1.98.0-nightly`) and `nightly` (`1.101.0-nightly`):

1. **Four Distinct Layers of Name Resolution and Item Identity in `rustc`:**
   - At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, source spelling is never a canonical item identity. `rustc` separates:
     1. *Source spelling and lexical scope* across four disjoint namespaces (`TypeNS`, `ValueNS`, `MacroNS`, `LifetimeNS`/labels), where inner bindings shadow outer bindings in the same namespace and `use` declarations (`DefKind::Use`) carry their own `DefId` distinct from the target item(s) returned by `DeclData::res()`.
     2. *Name-resolution result (`hir::def::Res`):* definitions resolve to `Res::Def(DefKind, DefId)`, whereas local `let` bindings and parameters resolve to `Res::Local(HirId)` (`owner: OwnerId` + `local_id: ItemLocalId`), and type-dependent paths (`T::Assoc`, `<T as Trait>::method`) produce `PartialRes` with `unresolved_segments > 0` resolved later by `rustc_hir_typeck`.
     3. *Session-local definition handle (`DefId { krate: CrateNum, index: DefIndex }`):* `CrateNum` (`LOCAL_CRATE == 0`) and `DefIndex` are dense per-compilation indices that depend on crate graph ordering and HIR creation order and are **not** stable across sessions or source edits.
     4. *Cross-session stable identity (`DefPathHash(Hash64, Hash64)`):* combines `StableCrateId` (a 64-bit SipHash-1-3 of crate name, `-C metadata` values, `is_exe`, and `CFG_VERSION`) with a hierarchical 64-bit hash of the item's `DefPath` (`parent` hash + `DisambiguatedDefPathData { data: DefPathData, disambiguator: u32 }`).
2. **Block-Local Items, Closures, Anonymous Constants, and Body-Ownership Traversal:**
   - Rust permits full item declarations (`fn`, `struct`, `enum`, `union`, `trait`, `impl`, `type`, `const`, `static`, `mod`) inside expression blocks (`fn`, `const`, `static`, and closure bodies), alongside closures (`DefKind::Closure`), anonymous/inline constants (`DefKind::{AnonConst, InlineConst}`), `impl Trait` opaque types (`DefKind::OpaqueTy`), and tuple struct/variant constructors (`DefKind::Ctor`).
   - Block-local item declarations do **not** capture outer runtime locals or generic parameters (unless explicitly parameterized and passed), whereas closures have unique anonymous types (`DefPathData::Closure`) that capture outer locals via compiler-synthesized environments.
   - Because block-local items, closures, and inline constants are nested under their enclosing value-namespace `DefKey` (`outer::inner`, `outer::{closure#0}`, `outer::{constant#0}`) rather than exported in a module tree, a verification tool (`anneal-rustc-capture`) cannot discover all items solely by walking module exports: it must iterate `tcx.hir_body_owners()` / `tcx.mir_keys(())` and key items by `DefId` / `DefPathHash` rather than user-written module paths.
3. **Multi-Version Execution Verification of Local Item `DefId` and Sibling Disambiguator Shifting (`1.98.0-nightly` vs. `1.101.0-nightly`):**
   - Executing the repaired 575-byte fixture ([`support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs)) and the 700-byte shifted control ([`support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs)) under both `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-31`) and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `2026-09-30`) produces the **exact same** 23-path and 25-path `DefId(0:N ~ local_identity[TAG]::...)` sequences across both toolchains (differing only in the 4-hex crate hash tag `18ae` in `1.98.0-nightly` vs. `fcc1` in `1.101.0-nightly`, because `StableCrateId` hashes `CFG_VERSION`).
   - Inserting one earlier closure and one earlier inline `const` inside `outer_a` shifts the pre-existing closure from `DefId(0:13 ~ ...::outer_a::{closure#0})` to `DefId(0:14 ~ ...::outer_a::{closure#1})`, shifts the pre-existing inline const from `{constant#0}` to `{constant#1}`, and shifts the numeric `DefIndex` of the completely unchanged sibling function `outer_b` from `0:18` to `0:20` and `main` from `0:20` to `0:22`.
4. **Eager Substitution of Ordinary Free Type Aliases vs. Preserved `TyKind::Alias` Forms:**
   - In `rustc` (`compiler/rustc_hir_analysis/src/collect/type_of.rs` and `hir_ty_lowering/src/lib.rs`), an ordinary free `type Alias<T> = Concrete<T>;` has a declaration-level `DefId` (`DefKind::TyAlias`) and HIR node (`hir::ItemKind::TyAlias`), and `tcx.type_of(def_id)` returns the lowered RHS `EarlyBinder<Ty<'tcx>>`.
   - When `HirTyLowerer::lower_path_segment` lowers a use site of a free `DefKind::TyAlias` without `-Z / #![feature(lazy_type_alias)]`, it immediately calls `tcx.at(span).type_of(def_id).instantiate(tcx, args).skip_norm_wip()`, **erasing the type alias from the resulting semantic `Ty<'tcx>`**.
   - By contrast, four related constructs are **not** erased during ordinary path lowering: (a) `#![feature(lazy_type_alias)]` (`TyKind::Alias(ty::Free, AliasTy)`), (b) associated type projections (`TyKind::Alias(ty::Projection | ty::Inherent, AliasTy)`), (c) `impl Trait` opaque types (`TyKind::Alias(ty::Opaque, AliasTy)` including `OpaqueTyOrigin::TyAlias`), and (d) value-namespace uses of a type alias to a tuple struct (`Alias(1, 2)`), which `rustc_resolve` rejects because a type alias imports only the type namespace (`TypeNS`), not the tuple struct's value-namespace constructor (`DefKind::Ctor`).

---

## Applicability

This report applies to the following pinned compilers, language references, and verification repositories recorded in `REPORT.json`:

| Component / Subject | Version / Toolchain Date | Commit / Revision | Scope & Role in Report |
| :--- | :--- | :--- | :--- |
| **`rust-lang/rust` (`nightly` source pin)** | `nightly` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Source audit of `rustc_resolve`, `DefId`, `DefPathHash`, `StableCrateId`, and `HirTyLowerer` (`type_of.rs`, `hir_ty_lowering`). |
| **`rust-lang/rust` (`nightly` binary)** | `1.98.0-nightly` (`2026-05-30`) | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | Executed `rustc` binary on `x86_64-unknown-linux-gnu` and `aarch64-apple-darwin` (`SHA-256: 2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) for block-local item probes and `DefId` shifting experiments. |
| **`rust-lang/rust` (`nightly` binary)** | `1.101.0-nightly` (`2026-09-29`) | `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` | Newer nightly comparison on `aarch64-apple-darwin` (`SHA-256: 29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d`) for `-Zunpretty=hir-tree` and `DefId` / disambiguator invariants. |
| **`rust-lang/reference`** | Normative Reference | `ad35aca481751a06afeb23820a672b0f3b11a476` | Normative rules for namespaces, scopes, shadowing, `use` declarations, nested items, closures, and `type` aliases. |
| **`joshlf/anneal`** | `main` | `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` | Anneal item-addressing and MIR capture architecture. |

---

## Findings

### 1. Four Layers of Name Resolution and Item Identity in `rustc` (`Res`, `DefId`, `StableCrateId`, and `DefPathHash`)

`Basis: normative, source`

Across `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/names/`) and `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`compiler/rustc_resolve/`, `compiler/rustc_hir/src/def.rs`, and `compiler/rustc_hir/src/definitions.rs`), `rustc` separates four identity layers:

| Layer | Compiler Representation | Scope & Stability Guarantees | Pitfalls for Verification & Capture Tools |
| :--- | :--- | :--- | :--- |
| **1. Source Spelling & Namespaces** | `Symbol` + `Namespace` (`TypeNS`, `ValueNS`, `MacroNS`) + lifetime/label scopes | Lexical only. A `struct S(u32);` populates both `TypeNS` (`DefKind::Struct`) and `ValueNS` (`DefKind::Ctor(CtorOf::Struct, CtorKind::Fn)`). | Identical source text (`S` or `foo`) in two blocks or namespaces denotes distinct entities; conversely, `use a::foo as bar;` aliases the same target `DefId`. |
| **2. Resolution Result (`Res`) & Type-Relative `PartialRes`** | `hir::def::Res<Id>` (`Res::Def(DefKind, DefId)`, `Res::Local(HirId)`, `Res::PrimTy`, `Res::SelfTyParam`, `Res::SelfTyAlias`, `Res::SelfCtor`) | Early name resolution (`rustc_resolve`) resolves module paths and lexical locals (`HirId`), but stops at type-dependent segments (`T::Assoc`, `<S>::method`), recording `PartialRes { base_res, unresolved_segments }` in `ResolutionMap` for `rustc_hir_typeck` to finish (`typeck_results.type_dependent_def(hir_id)`). | Notice that `use` items have their own `DefKind::Use` `DefId`, while `DeclData::res()` in `rustc_resolve` points directly to the imported target `Res`. |
| **3. Session Handle (`DefId` / `LocalDefId`)** | `DefId { krate: CrateNum, index: DefIndex }` | **Single-session only.** `CrateNum` (`0` for `LOCAL_CRATE`) and `DefIndex` are assigned sequentially as definitions are lowered into HIR or decoded from `.rmeta`. | Adding or reordering an item earlier in the crate shifts the numeric `DefIndex` of later unchanged items. Never persist raw `DefIndex` across builds. |
| **4. Cross-Session Identity (`DefPathHash`)** | `DefPathHash(Hash64, Hash64)`: `(StableCrateId, local_hash)` (`definitions.rs`) | Stable across separate invocations of the **same** `rustc` version on unchanged `DefPath` hierarchies. `StableCrateId::new` (`compiler/rustc_session/src/cgu_reuse_tracker.rs` / `rustc_middle`) hashes `crate_name`, `is_exe`, `-C metadata` strings, target triple, and `CFG_VERSION`. Each child `DefKey` hashes `(parent_def_path_hash, DisambiguatedDefPathData { data: DefPathData, disambiguator: u32 })`. | Because `StableCrateId` includes `CFG_VERSION` (`rustc` version/commit string), upgrading `rustc` changes the upper 64-bit `StableCrateId` half of `DefPathHash` even when the source crate is unchanged. Furthermore, unnamed sibling items (`impl`, closures, `{constant#k}`, duplicate block-local items) use a sequential sibling `disambiguator: u32` that shifts if an earlier sibling with the same `DefPathData` is inserted in the same parent scope. |

---

### 2. Block-Local Items, Closures, Anonymous Constants, and Body-Ownership Discovery

`Basis: normative, source, execution`

In `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/statements.md`, `src/expressions/closure-expr.md`) and `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, probed in [`support/rust-local-nested-items/probes/local.rs`](support/rust-local-nested-items/probes/local.rs) and [`support/rust-local-nested-items/probes/README.md`](support/rust-local-nested-items/probes/README.md)):

1. **Block-Local Item Declarations vs. Closures:**
   - Any item declaration (`fn`, `struct`, `enum`, `union`, `trait`, `impl`, `type`, `const`, `static`, `mod`) may appear inside a statement block (`fn`, `const`, `static`, or closure body).
   - A block-local `fn` or `struct` has no canonical user-callable path outside its block (though it can be returned via `impl Trait` or stored in a function pointer/vtable) and **cannot capture outer runtime locals or generic parameters of the enclosing function**.
   - By contrast, a closure (`|x| x + y`) has an anonymous compiler-generated type (`DefKind::Closure`, `DefPathData::Closure`), inherits the enclosing generic parameters in its `GenericArgs`, and captures outer locals (`y`) as fields of its closure environment.
2. **Complete Taxonomy of Non-Module-Path Definitions (`DefKind` and `DefPathData`):**
   - Inspecting HIR and MIR on [`support/rust-local-nested-items/probes/local.rs`](support/rust-local-nested-items/probes/local.rs) confirms how `rustc` parents and disambiguates body-nested definitions:

| Construct Inside a Function Body (`outer`) | `DefKind` | `DefPathData` | Displayed `DefPath` Pattern | Sibling Disambiguation Rule |
| :--- | :--- | :--- | :--- | :--- |
| **Block-local `fn helper()`** (in two blocks of `outer`) | `DefKind::Fn` | `ValueNs("helper")` | `outer::helper`, `outer::helper#1` | Second `helper` under the same parent `DefId` (`outer`) receives `disambiguator = 1` (`helper#1`) even though the two blocks are lexically disjoint! |
| **Block-local `struct Local(u32)`** | `DefKind::Struct` + `DefKind::Ctor(Struct, Fn)` | `TypeNs("Local")` + child `Ctor` | `outer::Local`, `outer::Local::{constructor#0}` | Tuple struct creates both a `TypeNs` `DefId` and a child `DefPathData::Ctor` `DefId`. |
| **Block-local `impl Local { fn get(&self) }`** | `DefKind::Impl { of_trait: false }` + `DefKind::AssocFn` | `Impl` + child `ValueNs("get")` | `outer::{impl#0}::get` | Unnamed `impl` blocks under `outer` are disambiguated as `{impl#0}`, `{impl#1}`, ... |
| **Closure `\|x\| x + 1`** | `DefKind::Closure` | `Closure` | `outer::{closure#0}` | Numbered sequentially `{closure#0}`, `{closure#1}`, ... per parent body owner. |
| **Array length `[u8; 4]` or inline `const { 1 + 2 }`** | `DefKind::AnonConst` / `DefKind::InlineConst` | `AnonConst` | `outer::{constant#0}`, `outer::{constant#1}` | Both `AnonConst` and `InlineConst` map to `DefPathData::AnonConst` and share the `{constant#k}` sibling counter under their parent `DefId`! |
| **Return-position `-> impl Trait`** | `DefKind::OpaqueTy` | `OpaqueTy` | `outer::{opaque#0}` | Assigned its own `DefId` with `DefPathData::OpaqueTy`. |

3. **Consequence for Item Discovery:**
   - Walking `tcx.hir_crate_items(())` or `tcx.mir_keys(())` visits all `LocalDefId`s in the crate regardless of whether they are nested inside statement blocks, closures, or inline `const` blocks, whereas top-down module-export traversal misses every block-local item.

---

### 3. Multi-Version Execution Comparison of Local Item Identities (`1.98.0-nightly` vs. `1.101.0-nightly`)

`Basis: execution`

In [`support/rustc-local-identity-r534-r565-may-to-september/`](support/rustc-local-identity-r534-r565-may-to-september/), three fixtures were tested under `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-31`) and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `2026-09-30`) on `aarch64-apple-darwin` (receipts in [`support/rustc-local-identity-r534-r565-may-to-september/results.json`](support/rustc-local-identity-r534-r565-may-to-september/results.json) and [`support/rustc-local-identity-r534-r565-may-to-september/analysis.json`](support/rustc-local-identity-r534-r565-may-to-september/analysis.json)):

1. **Historical Fixture Artifact vs. Repaired Baseline (`original-local.rs` vs. `repaired-local.rs`):**
   - The original 576-byte specimen [`support/rustc-local-identity-r534-r565-may-to-september/fixture/original-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/original-local.rs) began with a stray backslash (`\!#[allow(dead_code)]`), failing at parse time (`exit 1`) in both compilers.
   - Removing that single leading backslash yields the 575-byte [`support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs), which compiles cleanly (`exit 0`) and emits 23 `DefId` entries in `-Zunpretty=hir-tree`.
2. **Cross-Version `DefId` and `DefPath` Invariance (`1.98.0-nightly` vs. `1.101.0-nightly`):**
   - Normalizing the 4-hex `StableCrateId` display tag (`local_identity[18ae]` in `1.98.0-nightly` vs. `local_identity[fcc1]` in `1.101.0-nightly`), all 23 `DefId(0:N ~ ...)` entries in `repaired-local.rs` and all 25 `DefId(0:N ~ ...)` entries in [`support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs) match **100%** between `1.98.0-nightly` and `1.101.0-nightly`.
3. **Empirical Verification of Sibling Disambiguator and `DefIndex` Shifting (`repaired-local.rs` vs. `shifted-local.rs`):**
   - Inserting one earlier closure (`let early_closure = |v: u32| v + 10;`) and one earlier inline constant (`let early_inline = const { 1u32 + 1 };`) at the top of `outer_a` in `shifted-local.rs` produces four concrete identity shifts in both compilers:

| Item in `local_identity` | `DefId` & Path in `repaired-local.rs` | `DefId` & Path in `shifted-local.rs` | Observed Identity Shift |
| :--- | :--- | :--- | :--- |
| **Pre-existing closure in `outer_a`** | `DefId(0:13 ~ local_identity[..]::outer_a::{closure#0})` | `DefId(0:14 ~ local_identity[..]::outer_a::{closure#1})` | Both `DefIndex` (`13 -> 14`) and sibling `DefPath` disambiguator (`{closure#0} -> {closure#1}`) shift! |
| **Nested closure inside that closure** | `DefId(0:14 ~ ...::outer_a::{closure#0}::{closure#0})` | `DefId(0:15 ~ ...::outer_a::{closure#1}::{closure#0})` | Parent segment shifts (`{closure#0} -> {closure#1}`), altering its `DefPathHash`. |
| **Pre-existing `const { 2u32 + 3 }` in `outer_a`** | `DefId(0:16 ~ ...::outer_a::{constant#0})` | `DefId(0:18 ~ ...::outer_a::{constant#1})` | Both `DefIndex` (`16 -> 18`) and sibling `DefPath` disambiguator (`{constant#0} -> {constant#1}`) shift! |
| **Unchanged sibling `fn outer_b` & `fn main`** | `DefId(0:18 ~ ...::outer_b)`, `DefId(0:20 ~ ...::main)` | `DefId(0:20 ~ ...::outer_b)`, `DefId(0:22 ~ ...::main)` | `DefPath` (`outer_b`, `main`) is invariant, **but session `DefIndex` shifts by `+2` (`18 -> 20`, `20 -> 22`)!** |

---

### 4. Ordinary Free Type Alias Erasure vs. Preserved `TyKind::Alias` Forms in `rustc`

`Basis: normative, source`

At `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/items/type-aliases.md`) and `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`compiler/rustc_hir_analysis/src/collect/type_of.rs` and `compiler/rustc_hir_analysis/src/hir_ty_lowering/src/lib.rs`):

1. **Declaration Identity vs. Semantic `Ty<'tcx>` Erasure of Ordinary Free Type Aliases:**
   - A free type alias `type Pair<T> = (T, u32);` has its own HIR item (`hir::ItemKind::TyAlias`) and `DefId` (`DefKind::TyAlias`), and `tcx.type_of(def_id)` lowers its right-hand side into `EarlyBinder<Ty<'tcx>>` (`(T, u32)`).
   - However, when `HirTyLowerer::lower_path_segment` lowers a type path that resolves to `Res::Def(DefKind::TyAlias, def_id)` in standard Rust (when `#![feature(lazy_type_alias)]` is **not** enabled), it immediately substitutes the alias's lowered body:
     ```rust
     tcx.at(span).type_of(def_id).instantiate(tcx, args).skip_norm_wip()
     ```
   - Consequently, by the time `mir_built`, `mir_drops_elaborated_and_const_checked`, or `optimized_mir` inspects local variable types (`LocalDecl.ty`) or function signatures (`tcx.fn_sig(def_id)`), an ordinary free `type` alias has been **completely replaced by its underlying `Ty<'tcx>`**; no `TyKind::Alias` node remains in MIR.
   - Importantly, because `type_of(def_id)` substitutes the RHS without checking all where-clauses of the `type` alias declaration at use sites (giving rise to the well-known `type_alias_bounds` lint), a downstream verifier must not assume that where-clauses written on an ordinary `type` alias were enforced by `rustc`.
2. **Four Cases Where Type Aliases Are NOT Simply Erased:**

| Construct | `rustc` Representation & Behavior | Difference from Ordinary Free `type` Alias |
| :--- | :--- | :--- |
| **1. Unstable `#![feature(lazy_type_alias)]`** | `HirTyLowerer::lower_path_segment` checks `tcx.features().lazy_type_alias()` and emits `Ty::new_alias(tcx, ty::Free, AliasTy::new_from_args(tcx, def_id, args))` (`TyKind::Alias(AliasTyKind::Free, ..)`). | Preserves the alias as a lazy `ty::Free` projection normalized by the trait solver (and enforces the alias's where-bounds). |
| **2. Associated Type Projections (`<T as Trait>::Assoc`, `Self::Assoc`)** | Lowered to `TyKind::Alias(ty::Projection, AliasTy)` (or `ty::Inherent` for unstable inherent associated types). | Remains unnormalized in polymorphic MIR whenever `T` is still generic; normalized during monomorphization via `normalize_erasing_regions`. |
| **3. Type-Alias `impl Trait` (`type Opaque = impl Trait;`)** | Creates a child `DefKind::OpaqueTy` (`OpaqueTyOrigin::TyAlias`) lowered to `TyKind::Alias(ty::Opaque, AliasTy)`. | Hides the concrete underlying type behind an opaque `DefId` until `RevealAll` runs during `mir_drops_elaborated_and_const_checked` (`Runtime` lowering). |
| **4. Value-Namespace Tuple Struct Constructor Calls via a Type Alias** | Given `struct Tuple(u32); type Alias = Tuple;`, writing `Alias(5)` in expression position is **rejected** by `rustc_resolve` (`E0423`: expected function, tuple struct or tuple variant, found type alias `Alias`), whereas `Alias { 0: 5 }` (struct literal syntax in `TypeNS`) is accepted. | A `type` alias is defined only in `TypeNS`; it does not alias the tuple struct's `ValueNS` constructor function (`DefKind::Ctor`). |

---

## Boundaries

1. **Cross-Version `StableCrateId` Sensitivity:** While `DefPath` structure and relative `DefIndex` numbering on the local-identity fixtures are identical between `rustc 1.98.0-nightly` (`2026-05-31`) and `rustc 1.101.0-nightly` (`2026-09-30`), `StableCrateId` deliberately hashes `CFG_VERSION`, so the upper 64 bits of `DefPathHash` (and the 4-hex tag in `-Zunpretty=hir-tree`) change whenever the `rustc` compiler binary changes.
2. **Sibling Disambiguator Sensitivity Within a Body:** Because closures (`{closure#k}`), anonymous/inline constants (`{constant#k}`), unnamed `impl` blocks (`{impl#k}`), and duplicate block-local item names (`helper#k`) are disambiguated by creation order under their parent `DefId`, inserting a new closure or inline constant inside a function body shifts the `DefPathHash` of subsequent closures/constants in that same function body.

---

## Evidence

All supporting Rust fixtures, raw `-Zunpretty=hir-tree` and `.rmeta` outputs, and offline verification scripts are preserved under `support/`:

- **Block-Local Nested Items & `DefPathData` Probe (`support/rust-local-nested-items/`):**
  - [`support/rust-local-nested-items/probes/local.rs`](support/rust-local-nested-items/probes/local.rs), [`support/rust-local-nested-items/probes/README.md`](support/rust-local-nested-items/probes/README.md).
- **Multi-Version (`2026-05-31` vs. `2026-09-30`) Local Item Identity & `DefId` Shifting (`support/rustc-local-identity-r534-r565-may-to-september/`):**
  - Fixtures: [`support/rustc-local-identity-r534-r565-may-to-september/fixture/original-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/original-local.rs), [`support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs), [`support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs`](support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs).
  - Scripts and JSON receipts: [`support/rustc-local-identity-r534-r565-may-to-september/check.py`](support/rustc-local-identity-r534-r565-may-to-september/check.py), [`support/rustc-local-identity-r534-r565-may-to-september/probe.py`](support/rustc-local-identity-r534-r565-may-to-september/probe.py), [`support/rustc-local-identity-r534-r565-may-to-september/analyze.py`](support/rustc-local-identity-r534-r565-may-to-september/analyze.py), [`support/rustc-local-identity-r534-r565-may-to-september/results.json`](support/rustc-local-identity-r534-r565-may-to-september/results.json), [`support/rustc-local-identity-r534-r565-may-to-september/analysis.json`](support/rustc-local-identity-r534-r565-may-to-september/analysis.json).
  - Raw HIR and `.rmeta` artifacts across both nightlies: [`support/rustc-local-identity-r534-r565-may-to-september/raw/old--repaired--hir.stdout`](support/rustc-local-identity-r534-r565-may-to-september/raw/old--repaired--hir.stdout), [`support/rustc-local-identity-r534-r565-may-to-september/raw/new--repaired--hir.stdout`](support/rustc-local-identity-r534-r565-may-to-september/raw/new--repaired--hir.stdout), [`support/rustc-local-identity-r534-r565-may-to-september/raw/old--shifted--hir.stdout`](support/rustc-local-identity-r534-r565-may-to-september/raw/old--shifted--hir.stdout), [`support/rustc-local-identity-r534-r565-may-to-september/raw/new--shifted--hir.stdout`](support/rustc-local-identity-r534-r565-may-to-september/raw/new--shifted--hir.stdout).

---

## Revalidation

Run the following self-contained commands from this package directory to verify the multi-version `DefId` and sibling-disambiguator artifacts offline and reproduce the HIR dumps:

```bash
# 1. Verify the multi-version (2026-05-31 vs. 2026-09-30) local item identity artifacts and DefId shift checks offline
python3 -B support/rustc-local-identity-r534-r565-may-to-september/check.py

# 2. Reproduce the HIR tree dumps on repaired-local.rs and shifted-local.rs with rustc +nightly
mkdir -p build/local-identity
rustc +nightly --edition 2021 --crate-type lib --crate-name local_identity \
  -Zunpretty=hir-tree \
  support/rustc-local-identity-r534-r565-may-to-september/fixture/repaired-local.rs \
  > build/local-identity/repaired.hir
rustc +nightly --edition 2021 --crate-type lib --crate-name local_identity \
  -Zunpretty=hir-tree \
  support/rustc-local-identity-r534-r565-may-to-september/fixture/shifted-local.rs \
  > build/local-identity/shifted.hir
```
