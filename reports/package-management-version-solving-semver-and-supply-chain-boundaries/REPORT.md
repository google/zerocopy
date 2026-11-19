# Package Management: Version Solving, SemVer Soundness, and Supply-Chain Boundaries

## Summary

Package managers fail along four orthogonal boundaries that single-language tools routinely conflate:

1. **Resolution complexity (`NP-completeness` vs. lattice join):** Deciding package installability is **NP-complete** even without disjunctive `OR` dependencies or virtual `Provides` directives; version-varying requirements plus single-version exclusivity suffice to encode 3-SAT (Mancinelli et al., ASE 2006; Cox, 2016). Production resolvers avoid worst-case exponential backtracking either via version-set CDCL with derivation-tree explanations (`PubGrub` in `dart-lang/pub` and `pubgrub-rs/pubgrub`) or by forbidding upper bounds and exclusions in favor of deterministic $O(|V|+|E|)$ **Minimal Version Selection (`MVS`)** paired with explicit major-version path separation (`golang/go` Import Compatibility Rule; `bazelbuild/bazel` Bzlmod `Selection`).
2. **Multi-version coexistence fails at nominal type boundaries and flat C link namespaces:** `rust-lang/cargo` allows multiple SemVer-incompatible majors in one binary by keying activations on `(name, SemverCompatibility, SourceId)` (leftmost non-zero version component). That coexistence breaks in two places: (a) **public-dependency type-identity splits** (`expected foo::T, found foo::T` and silent `Any::downcast_ref` failures), where Rust RFC 3516 decoupled `--extern priv:<crate>` / `exported_private_dependencies` linting from RFC 1977's stalled resolver public-pool check; and (b) **global native `links` singleton exclusivity**, where Cargo forbids two crates from declaring the same `links = "<lib>"` anywhere in the graph regardless of SemVer major because C linkers share a flat global symbol namespace.
3. **Syntactic SemVer is unsound across API, coherence, binary ABI, and formal specifications:** SemVer 2.0.0 leaves "public API" and "backward compatibility" informal and assigns `0.y.z` zero compatibility guarantees. In Rust, RFC 1105 classifies shallow breaking changes as minor, while RFC 2451 amends it to classify adding *any* blanket impl or any impl for an existing trait lacking a newly added local type before uncovered type parameters (`&`, `&mut`, `Box` being `#[fundamental]` and non-covering) as **major**. Static API linters (`cargo-semver-checks`, 274 Trustfall queries over unstable `rustdoc` JSON) omit general field/parameter type changes, generics/lifetimes, `const`/macro bodies, feature subsets, and unchecked `--target` triples. For ELF binaries, `libabigail` (`abidiff`) separates unconditional breaks (`ABIDIFF_ABI_INCOMPATIBLE_CHANGE = 8`: exported symbol removal, C++ vtable slot shift) from context-dependent layout breaks (`ABIDIFF_ABI_CHANGE = 4`: struct size/offset growth) while missing header-inlined ODR breaks. In verified ecosystems, **Specification SemVer** requires Liskov-Wing behavioral subtyping—contravariant preconditions ($\text{Pre}_{\text{old}} \Rightarrow \text{Pre}_{\text{new}}$), covariant $\text{Pre}_{\text{old}}$-guarded postconditions ($(\text{Pre}_{\text{old}} \land \text{Post}_{\text{new}}) \Rightarrow \text{Post}_{\text{old}}$), and preserved invariants ($I_{\text{new}} \Rightarrow I_{\text{old}}$)—so tightening a precondition or weakening a postcondition breaks downstream proofs with zero type-signature change.
4. **Polyglot hermeticity and supply-chain authority:** Single-language managers run untrusted `build.rs`/proc-macros with ambient host privileges, contaminate builds via host `pkg-config`, and rely on wall-clock `mtime` freshness. Both Lean 4 Lake (`MTime.checkUpToDate`: strict `self < mtime`) and Cargo's default `FingerprintMethod::Mtime` collide with read-only content-addressed stores normalized to Unix epoch `1` (`1 < 1 == false`). Bounding supply-chain authority requires two-phase offline execution, content-addressed polyglot closures, capability-restricted build sandboxes, and `in-toto` v1 / SLSA Build L3–L4 provenance attestations where Build L4 enforces complete `resolvedDependencies`.

## Applicability

This report synthesizes **15 durable primary sources** pinned in `REPORT.json` and `## Evidence`:

- **Dependency resolution:** Mancinelli et al. (ASE 2006) and Abate et al. (JSS 2012) for FOSS installability complexity and CUDF solver decoupling; `dart-lang/pub@fe190660` (`doc/solver.md`) and `pubgrub-rs/pubgrub@65355b4a` for PubGrub CDCL; `golang/go@b496a304` (`src/cmd/go/internal/mvs/mvs.go`) and `bazelbuild/bazel@3a881392` (`Selection.java`) for MVS; and `rust-lang/cargo@e3535167` for SemVer-bucketed DFS backtracking, global `links` checks, and MSRV fallback (`resolver = "3"`, RFC 3537).
- **Compatibility semantics:** `semver/semver@f99d5485` (SemVer 2.0.0); `rust-lang/rfcs@f43d5789` (RFCs 1023, 1105, 1977, 2451, 3516, 3537); `obi1kenobi/cargo-semver-checks@8f25eea7`; `sourceware.org/git/libabigail.git@a769028c`; and Liskov & Wing (TOPLAS 1994).
- **Hermeticity and provenance:** `rust-lang/cargo@e3535167` (`custom_build.rs`, `fingerprint/*`), `leanprover/lean4@8009d0a6` (`src/lake/Lake/Build/Trace.lean`), `in-toto/attestation@50bf0171`, and `slsa-framework/slsa@8c316167` (post-v1.1 Working Draft introducing SLSA Build L4 `Dependencies complete` and the Source Track).
- **Adjacent corpus packages (cross-referenced, not duplicated):**
  - `incremental-computation-adapton-salsa-buck2-and-build-system-graphs` covers incremental query engines and proof-dependency invalidation; this package characterizes the *contract-refinement cutoff condition* (Specification SemVer) across package boundaries.
  - `nix-guix-immutable-closures-mutable-roots-and-toolchain-archive-equivalence` covers Nix/Guix immutable stores and relocatable archives; this package documents the *package-manager interface collisions* (`mtime` strict `<`, ambient `build.rs`/`pkg-config`, native `links` singletons).
  - `cargo-unit-graphs-feature-resolution-and-rustc-invocations`, `rust-reference-layout-guarantees-target-abi-limits-and-semver-snares`, and `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility` cover Cargo feature/unit-graph internals, Rust `repr(C)`/`repr(transparent)` layout rules, and binary section embedding (`.dep-v0`, DSSE), respectively.
- **Exact observation vs. broader applicability:** Source-line invariants apply strictly to the pinned revisions (e.g., Cargo's layout under `src/resolver/` and `src/compiler/` at `e3535167` rather than historical `src/cargo/core/`; SLSA Build L4 reflects Working Draft `8c316167`, whereas SLSA v1.0 stopped at Build L3). Mathematical results (NP-completeness, MVS lattice join, and Liskov-Wing subtyping variance) apply to any system satisfying their axioms.

## Findings

### 1. Computational Complexity of Dependency Resolution: 3-SAT Reductions, CDCL (`PubGrub`), and Minimal Version Selection (`MVS`)

Basis: normative + source + documentation + execution + derived

#### 1.1 NP-Completeness of Package Installability (EDOS / Mancoosi / Version SAT)

In the EDOS formalization by Mancinelli et al. (ASE 2006, `doi:10.1109/ASE.2006.49`), a package repository $R$ assigns each versioned package a conjunctive normal form of **dependencies** (conjunctions of disjunctive alternatives) and symmetric binary **conflicts**. Deciding whether a target package $p \in R$ admits a consistent installation $I \subseteq R$ ($p \in I$, all dependencies satisfied, zero conflicts) is **NP-complete** via reduction from 3-SAT. Abate et al. (JSS 2012, `doi:10.1016/j.jss.2012.05.018`) generalized this into the **Common Upgradeability Description Format (`CUDF`)**, decoupling multi-criteria upgrade optimization from package-manager mechanics so pluggable SAT, Pseudo-Boolean, or ASP solvers (e.g., `aspcud`, `mccs`) can solve installability cleanly.

Russ Cox's *Version SAT* (2016) proved that **explicit disjunctions (`A | B`) and virtual `Provides` directives are unnecessary for NP-completeness**. Any language package manager satisfying four minimal axioms is already NP-complete:

1. A package version declares zero or more exact or range-bounded dependencies.
2. Installing a package version requires installing all its dependencies.
3. Different versions of the same package may declare different dependencies.
4. Two different versions of the same package cannot be installed simultaneously (or explicit mutual-exclusion conflicts exist).

Given any 3-SAT formula $\Phi = \bigwedge_{i=1}^n (l_{i,0} \lor l_{i,1} \lor l_{i,2})$ over variables $x_1, \dots, x_m$:

- **Variables:** Create packages `X1`..`Xm`, each with versions `0.0.0` (False) and `1.0.0` (True). Single-version exclusivity enforces consistency of $x_j$.
- **Clauses:** Create packages `C1`..`Cn`, each with versions `0.0.0`, `1.0.0`, `2.0.0`, where `Ci:k` depends on the exact version of `Xj` satisfying literal $l_{i,k}$. Choosing a version of `Ci` simulates 3-way disjunction without an `OR` operator.
- **Root:** Create `F 1.0.0` depending on `C1`, ..., `Cn` (any version).

`F 1.0.0` is installable iff $\Phi$ is satisfiable. Replacing exact constraints with inequalities (`<= 0.0.0` / `>= 1.0.0`) preserves the proof. Relaxing Axiom 4 globally avoids installability NP-completeness only if no singleton resources exist—finding a *minimal-duplication* graph remains NP-hard, and introducing any global exclusion constraint (such as Cargo's native C `links` attribute) immediately restores NP-completeness.

#### 1.2 PubGrub: Version-Set CDCL and Derivation-Tree Conflict Reporting

Naive DFS backtracking solvers thrash exponentially on dead ends, while flattening version intervals into raw Boolean SAT discards the domain semantics needed to explain failures. Natalie Weizenbaum's **PubGrub** algorithm (`dart-lang/pub@fe190660`, `doc/solver.md`; `pubgrub-rs/pubgrub@65355b4a`) lifts Conflict-Driven Clause Learning (CDCL) directly to package version sets:

- **Incompatibilities:** Constraints are represented as sets of terms $\{t_1, \dots, t_k\}$ that cannot simultaneously hold. "`foo 1.0.0` depends on `bar ^1.0.0`" becomes $\{\text{foo} \in \{1.0.0\},\; \text{bar} \notin [1.0.0, 2.0.0)\}$.
- **Merging and Widening (`pubgrub-rs/pubgrub`, `src/internal/core.rs:127-143, 435-488`):** `merge_incompatibility` collapses identical dependency bounds across multiple versions of a dependent via `MergedDependencies`. Callers knowing the registry's version list can widen singleton versions via `Ranges::widen_versions` so rejecting adjacent versions (`boto3`/`botocore` lockstep pattern in `core.rs:706-734`) removes contiguous ranges rather than accumulating singleton holes.
- **Unit Propagation (`core.rs:247-328`):** When a partial solution satisfies all terms of an incompatibility except one (`Relation::AlmostSatisfied`), PubGrub records the negation of the remaining term as a **derivation** tagged with that incompatibility as its `cause` and marks the incompatibility contradicted (`mark_contradicted`).
- **Conflict Resolution and Backjumping (`core.rs:362-420`):** When all terms are satisfied (`Relation::Satisfied`), `conflict_resolution` queries `partial_solution.satisfier_search`:
  - While the newest satisfier shares its decision level with another satisfier (`SameDecisionLevels { satisfier_cause }`), PubGrub resolves the current incompatibility with `satisfier_cause` (`Incompatibility::prior_cause`). On the pivot package $p$, the resolved forbidden set is the **union** $A \cup C$ (eliminating $p$ when $A \cup C$ equals $p$'s domain, or keeping the partial satisfier otherwise); on every other package $q$, the combined set is the **intersection** $B_1 \cap B_2$. Both parent IDs are recorded.
  - Once all remaining satisfiers lie strictly below the newest satisfier's decision level (`DifferentDecisionLevels { previous_satisfier_level }`), PubGrub backjumps directly to `previous_satisfier_level`, stores the learned incompatibility, and immediately unit-propagates it.
- **Derivation Trees (`core.rs:492-528`, `doc/solver.md`):** Reaching a terminal incompatibility (empty or containing only the root package) yields a directed acyclic proof graph (`build_derivation_tree` deduplicating `shared_ids`), rendered into a concise narrative explaining *why* resolution failed.
- **Four Differences from Standard CDCL/ASP (`dart-lang/pub`, `doc/solver.md`):** (1) Terms range over arbitrary `VersionSet` algebras; (2) single-version exclusivity per package is implicit in term intersection rather than $O(V^2)$ pairwise clauses; (3) dependencies are fetched *lazily* via `DependencyProvider::get_dependencies`; and (4) PubGrub omits ASP unfounded-set detection (permitting cyclic graphs unless rejected externally).

#### 1.3 Minimal Version Selection (`MVS`) and the Import Compatibility Rule

Russ Cox's **Minimal Version Selection (`MVS`)** in Go Modules (`golang/go@b496a304`, `src/cmd/go/internal/mvs/mvs.go`) eliminates NP-completeness by rejecting Axioms 1 and 4:

1. **Lower-Bound-Only Requirements (`mvs.go:20-45`):** `Reqs.Required(m)` declares *only minimum required versions*, ordered by opaque `Max(p, v1, v2)` with bottom `"none"`. No upper bounds or transitive exclusions exist.
2. **Deterministic Lattice Join (`mvs.go:90-182`):** `BuildList` walks the requirement graph (10-way concurrent `par.Work`) and selects, for every visited module path, the **maximum of all required minimum versions**—the minimum version satisfying every requirement. Selection is $O(|V|+|E|)$, deterministic without a lockfile ("high-fidelity builds": publishing a new upstream minor release does not silently change existing builds), and cannot encounter version conflicts.
3. **Import Compatibility Rule (`research.swtch.com/vgo-import`):** *"If an old package and a new package have the same import path, the new package must be backwards compatible with the old package."* Major versions `v2+` **must** append `/v2`, `/v3`, ... to their module and import paths. Thus `example.com/mod` and `example.com/mod/v2` are distinct nodes to MVS and distinct packages to the Go type checker, making major-version coexistence explicit in source code.
4. **Minimization, Upgrades, and Downgrades (`mvs.go:187-450`):** `Req` computes a minimal transitive-reduction requirement list via reverse postorder; `UpgradeAll` and `Upgrade` inject upgrade edges and rerun `BuildList`; `Downgrade` propagates exclusions backward along reverse dependencies (`rdeps`) and recomputes `BuildList` to drop spurious transitive dependencies.

**Bazel Bzlmod (`bazelbuild/bazel@3a881392`, `Selection.java:43-311`)** applies MVS to polyglot build graphs: `Selection.run` maps each discovered module into a `SelectionGroup(moduleName, targetAllowedVersion)`, takes `Comparators::max` per group (lines 169–174), and runs a two-pass breadth-first `DepGraphWalker` (`ignoreNodeps = false` then `true`, lines 181–198) to prune modules reachable only through upgraded-away versions or `nodep` edges. For multi-major coexistence, Bzlmod adds root-controlled `multiple_version_override` bucketing via `allowedVersions.ceiling(version)` (lines 105–116), failing with `VERSION_RESOLUTION_ERROR` if a reachable dependency exceeds all allowed buckets or if one module resolves two repo names to the same `(name, version)` (lines 269–304).

#### 1.4 Comparative Solver Architecture Matrix

| Dimension | EDOS / CUDF (`apt`, `opam`, `libsolv`) | PubGrub (`dart pub`, `pubgrub-rs`, `uv`) | Cargo Resolver (`rust-lang/cargo`) | Go Modules MVS (`golang/go`) | Bazel Bzlmod MVS (`bazelbuild/bazel`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Worst-case complexity** | NP-complete (opt: NP-hard) | NP-complete (CDCL + learned clauses) | NP-complete (DFS + conflict cache) | $O(\|V\|+\|E\|)$ lattice join | $O(\|V\|+\|E\|)$ BFS + pruning |
| **Upper bounds / conflicts** | Arbitrary CNF + `Conflicts:` | Arbitrary `VersionSet` + custom incompats | SemVer ranges + global `links` + MSRV pref | Disallowed (`exclude`/`replace` root-only) | Disallowed (root overrides only) |
| **Multi-major coexistence** | Distinct package names only | Single version per package key | Automatic per `SemverCompatibility` (except `links`) | Explicit `/v2` module/import path | Opt-in `multiple_version_override` |
| **Failure explanation** | External UNSAT core | Native derivation-tree proof to root | Conflict path trace (`describe_path`) | No version conflicts (`FindPath` on I/O errors) | Override-ceiling / duplicate-repo error |
| **Selection bias** | User preference (usually newest) | Provider-defined (usually newest) | Highest SemVer-compatible (MSRV fallback in v3) | **Minimum** satisfying version | **Minimum** satisfying version |
| **Lockfile role** | Required for determinism | Required for determinism | Required (`Cargo.lock`) | Integrity hashes only (`go.sum`) | Caches registry & extension eval |

---

### 2. Multi-Version Coexistence, Public-Dependency Type Splits, and Flat-Namespace Native `links` Collisions

Basis: normative + source + documentation + execution

#### 2.1 Cargo's `ActivationsKey`, DFS Backtracking, and Feature/MSRV Coupling

In `rust-lang/cargo@e3535167` (`src/resolver/types.rs`, `src/resolver/context.rs:19-125`, `src/resolver/mod.rs:1-60`), Cargo partitions crate identity into SemVer-compatibility equivalence classes:

```rust
pub struct ActivationsKey(InternedString, SemverCompatibility, SourceId);

pub enum SemverCompatibility {
    Major(NonZeroU64), // >= 1.0.0 -> Major(ver.major)
    Minor(NonZeroU64), // 0.y.z (y > 0) -> Minor(ver.minor)
    Patch(u64),        // 0.0.z -> Patch(ver.patch)
}
```

`ResolverContext.activations` (`im_rc::HashMap<ActivationsKey, (Summary, ContextAge), FxBuildHasher>`) enforces **at most one version per `(name, SemverCompatibility, SourceId)`** (inserting a second key for `dep.source_id()` under `[patch]`, `context.rs:109-120`). Consequently, `syn 1.0.109` and `syn 2.0.90` coexist in one binary via `rustc` metadata-hash symbol disambiguation, whereas `syn 1.0.100` and `syn 1.0.109` trigger `ConflictReason::Semver`.

Cargo's production solver (`src/resolver/mod.rs`) remains a highest-version-first DFS backtracking search with a `ConflictCache` (`src/resolver/conflict_cache.rs`) rather than PubGrub. Cargo's differential test suite (`crates/resolver-tests/tests/pubgrub.rs:95-236`) records two concrete divergences between Cargo and its SAT test oracle: (1) Cargo rejects non-dev dependency cycles (`test_06`..`test_08`) because `rustc` requires an acyclic crate DAG; and (2) weak optional dependency features (`dep?/feat`, `test_12`..`test_14`) are handled in the separate feature resolver (`src/resolver/features.rs`). Under `resolver = "2"` (Edition 2021, Rust 1.51+), host/dev/target features stay decoupled (`cargo-unit-graphs-feature-resolution-and-rustc-invocations`). Under `resolver = "3"` (Edition 2024, Rust 1.84+, RFC 3537), `resolver.incompatible-rust-versions` defaults to `fallback`, preferring candidates with `rust-version <= MSRV` while falling back to newer candidates rather than failing if no MSRV-compatible version satisfies the SemVer range (`doc/book/src/reference/resolver.md`).

#### 2.2 Public-Dependency Type-Identity Splits (RFC 1977 vs. RFC 3516)

Multi-major coexistence is transparent only for **private** implementation dependencies. When two dependencies expose types from different SemVer-incompatible majors of `foo`, `rustc` assigns them disjoint nominal identities:

```rust
// lib_a depends publicly on foo 1.2; lib_b depends publicly on foo 2.0
let tok: foo_v1::Token = lib_a::make_token();
lib_b::consume_token(tok);
// error[E0308]: mismatched types: expected `foo::Token`, found `foo::Token`
// note: two different versions of crate `foo` are being used
```

Worse, across type-erased `Box<dyn std::any::Any>` interfaces, `TypeId::of::<foo_v1::Error>() != TypeId::of::<foo_v2::Error>()`, so `downcast_ref` compiles cleanly and silently returns `None` at runtime (`doc/book/src/reference/resolver.md`). Library authors work around major migrations via the **"SemVer trick"**—releasing a minor `1.N` version of `foo` that depends on `2.0` and re-exports `pub use foo_v2::Token;`, unifying `TypeId` across both buckets.

**Why RFC 3516 superseded RFC 1977 (`rust-lang/rfcs@f43d5789`, `text/3516-public-private-dependencies.md`):** RFC 1977 (2017) proposed making Cargo's resolver partition the graph into connected components of `public = true` edges ("pools of public types") and reject any graph where one consumer reaches two versions of a crate across public pools (RFC 3516:311-344). That resolver rule stalled stabilization for six years because marking a dependency `public = true` could retroactively break callers legitimately renaming two majors (`tokio_03` + `tokio_1`) and interacted intractably with feature- and `cfg`-gated visibility. RFC 3516 therefore decoupled linting from resolution: Cargo passes `--extern priv:<crate>` to `rustc` for non-public library dependencies, and `rustc` enforces `exported_private_dependencies` (`allow` pre-2024, `deny` in Edition 2024+, RFC 3516:179-181) whenever a private dependency leaks into a `pub` signature. Synchronizing sibling crates (`clap` + `clap_complete`) remains deferred to future mechanisms such as `version.from = [...]` delegation (RFC 3516:351-391).

#### 2.3 Hard Global Link Failures: Native C `links` Singleton Exclusivity

At the C FFI boundary, native ELF/Mach-O/PE linkers share a flat unmangled symbol namespace (`inflate`, `SSL_new`, `sqlite3_open`). Cargo enforces global singleton ownership of each native library name via `package.links = "<lib>"` in two places (`rust-lang/cargo@e3535167`):

1. **In the resolver (`src/resolver/context.rs:25, 81-91`):** `ResolverContext.links: im_rc::HashMap<InternedString, PackageId, FxBuildHasher>` is keyed **solely** by native library name. Inserting a second crate with the same `links` value fails with `ConflictReason::Links(link)`—even across different SemVer majors (`libgit2-sys 0.11` vs `0.12`) or distinct crate names (`libz-sys` vs `zlib-ng-sys` both setting `links = "z"`).
2. **Post-resolution UnitGraph sweep (`src/compiler/links.rs:21-60`):** `validate_links` re-checks the resolved `UnitGraph` because pre-2018 crates.io index entries omitted `links` metadata (`links.rs:11-18`).

Thus **any native C dependency collapses Cargo's multi-major coexistence back into a global single-version regime**, reintroducing NP-complete diamond deadlocks across transitive consumers. Conversely, because `links` is an unenforced string key (plus `DEP_<LINKS>_<KEY>` metadata propagation in `src/compiler/custom_build.rs:573-577`), two crates linking conflicting copies of a C library without matching `links` keys bypass Cargo completely and fail at link time—or silently collide with mismatched C struct ABIs at runtime.

---

### 3. Why Syntactic SemVer Is Unsound: API Evolution, Trait Coherence, Binary ABI, and Specification SemVer

Basis: normative + source + documentation + execution + derived

#### 3.1 The Informality of SemVer 2.0.0 and `0.y.z` Divergence

Semantic Versioning 2.0.0 (`semver/semver@f99d5485`, `semver.md`) specifies an exact precedence grammar (§§2, 9–11), but defines compatibility only informally: §1 allows the "public API" to exist strictly in prose documentation; §4 declares that `0.y.z` has *zero* stability promises ("Anything MAY change at any time"); and §§6–8 leave "backward compatible" undefined across types, coherence, binary layouts, and behavior. Consequently, ecosystems diverge on `0.y.z`: Cargo (`src/resolver/types.rs`) and `npm` treat `0.y.z` ($y > 0$) as minor-compatible (`^0.y.z` excludes `0.(y+1).0`) and `0.0.z` as exact, whereas Go's MVS upgrades `0.1.0 -> 0.2.0` automatically on a shared module path.

#### 3.2 Rust API Evolution, Trait Coherence Breakage, and `cargo-semver-checks` Blindspots

**RFC 1105 (`rust-lang/rfcs@f43d5789`, `text/1105-api-evolution.md:61-67`)** establishes the pragmatic Rust principle: **"all major changes are breaking, but not all breaking changes are major."** Minor changes explicitly allowed despite breaking or altering downstream code include:

- **Adding any public item** (`1105:162-183`): breaks downstream `use upstream::*;` glob imports.
- **Adding a defaulted trait method** (`1105:270-320`): introduces method-call ambiguity across two traits (major only if it breaks `dyn` object safety or interacts with defaulted associated types).
- **Adding an inherent method** (`1105:376-420`): inherent dispatch shadows trait methods—failing compilation if signatures differ, or **silently changing runtime dispatch without any compiler error** if signatures match.
- **Type inference & `#[non_exhaustive]`:** Adding a second `From` impl breaks `.into()` inference; adding `#[non_exhaustive]` is major, whereas adding variants/fields to an existing `#[non_exhaustive]` item is minor.

**Trait Coherence & Orphan-Rule SemVer Breakage (RFC 1023 & RFC 2451):**
RFC 1105 originally classified implementing any non-fundamental trait for an existing type as minor (`1105:340-372`). **RFC 2451** (`text/2451-re-rebalancing-coherence.md:165-177, 227-250`) formally amended RFC 1105 to resolve its contradiction with RFC 1023. Under Rust's concrete orphan rule (`2451:185-199`), `impl<P1..=Pn> Trait<T1..=Tn> for T0` for a foreign `Trait` is legal in a downstream crate iff:

1. At least one `Ti` in `T0..=Tn` is a local type (let `Ti` be the first such type); AND
2. No **uncovered** type parameter appears in `T0..Ti` (excluding `Ti`), where non-fundamental constructors (`Vec<T>`) cover `T`, while `#[fundamental]` wrappers (`&T`, `&mut T`, `Box<T>`) do **not** cover `T` and propagate locality from `T`.

Therefore, an upstream crate adding an impl for an *existing* trait is coherence-safe (minor) **only if** some `Ti` in `T0..=Tn` is a **newly added local type** in that release and no uncovered type parameter precedes `Ti` (`2451:229-239`):

```rust
// MAJOR coherence breaks (can collide with legal pre-existing downstream impls):
impl<T> OldTrait for T {}                      // collides with `impl OldTrait for Downstream`
impl<T> OldTrait<T> for OldType {}             // collides with `impl OldTrait<Downstream> for OldType`
impl<T> From<T> for Vec<T> {}                  // collides with `impl From<Downstream> for Vec<Downstream>`
impl<T> ForeignTrait<NewLocal> for Box<T> {}   // Box is #[fundamental] -> T uncovered before NewLocal;
                                               // collides with `impl<U> ForeignTrait<U> for Box<Downstream>`
// MINOR coherence-safe:
impl<T> ForeignTrait<NewLocal> for Vec<T> {}   // Vec covers T; no prior crate could name NewLocal
```

Implementing a **`#[fundamental]` trait** (`Sized`, `Fn`, RFC 1023 / RFC 1105:329-338) or silently removing an **auto-trait** (`Send`, `Sync`, `Unpin`) by adding a private `!Send` field (e.g., `PhantomData<*const ()>`) is likewise **major** despite zero public signature diff.

**Coverage and Structural Blindspots of `cargo-semver-checks` (`obi1kenobi/cargo-semver-checks@8f25eea7`):**
At `8f25eea7`, `cargo-semver-checks` ships **274 `.ron` Trustfall queries** (`59 trait_*`, `40 enum_*`, `23 function_*`, `20 inherent_*`, `16 pub_*`, `13 struct_*`, `13 union_*`, `11 repr_*`, etc.) over `rustdoc` JSON, backed by automated **witness compilation checks** (`README.md:239-255`) that compile a minimal failing downstream witness to eliminate false positives. Its documentation (`README.md:63-95, 169-222, 256-272`) highlights five structural limits:

1. **Types, generics, and lifetimes (`README.md:267-271`):** Does not yet catch general breaking changes in field/parameter/return types, lifetime constraints, or generic bounds.
2. **Executable bodies and macros:** `rustdoc` JSON omits function bodies, `const` evaluation values/panics, `macro_rules!` expansion semantics, and proc-macro codegen behavior.
3. **Feature-subset blindspots (`README.md:169-196, 271`):** Defaults to a single heuristic feature union (excluding `unstable`/`nightly`/`bench`/`no_std`/`_*`); breaks occurring only under a strict feature subset escape single-pass checking.
4. **Cross-target `cfg` matrices (`README.md:197-222`):** `rustdoc` evaluates `#[cfg(...)]` for one target triple per run; Linux-only CI misses breaking API/layout diffs gated by `#[cfg(windows)]`, `target_pointer_width = "32"`, or `wasm32`.
5. **Unstable metadata schema (`README.md:63-95`):** Coupling to unstable `rustdoc` JSON format versions restricts supported nightly/MSRV toolchains.

#### 3.3 C/C++ Binary ABI Compatibility (`libabigail` / `abidiff`)

Across C/C++ shared-library boundaries, source compatibility does not ensure binary ABI compatibility. `libabigail` (`sourceware.org/git/libabigail.git@a769028c`, `doc/manuals/abidiff.rst`, `include/abg-comparison.h`) builds an **ABI Corpus** from ELF symbol tables intersected with DWARF (or fallback CTF/BTF) type graphs reachable from exported symbols.

`abidiff` categorizes diffs across 28 `enum diff_category` bitflags (`include/abg-comparison.h`) and returns an 8-bit status mask (`doc/manuals/abidiff.rst`, *Return values*):

- `ABIDIFF_ERROR = 1`, `ABIDIFF_USAGE_ERROR = 2`.
- `ABIDIFF_ABI_CHANGE = 4`: harmful ABI difference detected.
- `ABIDIFF_ABI_INCOMPATIBLE_CHANGE = 8` (implies bit 4, exit code `12`): set **only** for unconditionally incompatible breaks:
  1. Removal of a defined, exported function or global variable symbol.
  2. Shift of a C++ virtual function table (vtable) slot index (`VIRTUAL_MEMBER_CHANGE_CATEGORY = 1 << 12`).

```cpp
// v1.hpp                                 // v2.hpp (source-compatible, binary ABI break!)
struct Widget {                           struct Widget {
  virtual void draw();    // vtable[0]      virtual void preload(); // vtable[0] -> SHIFT! (exit 12)
  virtual void resize();  // vtable[1]      virtual void draw();    // vtable[1]
  int width;              // offset 8       char tag;               // offset 8  -> SHIFT! (exit 4)
};                                          int width;              // offset 12
                                          };
```

Because `abidiff` cannot know from ELF/DWARF alone whether callers stack-allocate `Widget` by value or allocate it only behind an opaque factory pointer, `SIZE_OR_OFFSET_CHANGE_CATEGORY` (`1 << 11`), `FN_PARM_ADD_REMOVE_CHANGE_CATEGORY` (`1 << 21`), and `FN_PARM_TYPE_CV_CHANGE_CATEGORY` (`1 << 19`) set `ABIDIFF_ABI_CHANGE` (`4`) for human review rather than bit `8`. Worse, **header-inlined functions, C++ templates, and preprocessor macros** emit no exported ELF symbols; changing an inline accessor's assumptions across versions causes silent One Definition Rule (ODR) corruption invisible to binary diffing. (For Rust `repr(C)`/`repr(transparent)` layout guarantees, see `rust-reference-layout-guarantees-target-abi-limits-and-semver-snares`.)

#### 3.4 Specification SemVer in Verified Ecosystems (Liskov & Wing Behavioral Subtyping)

When downstream crates hold machine-checked proofs against upstream contracts (Lean, Verus, Kani, Dafny, Creusot, Rocq), syntactic API and binary ABI SemVer are both unsound: preserving every type signature and ELF symbol can still break downstream proofs.

The sound criterion for backwards-compatible specification evolution is **behavioral subtyping** (Liskov & Wing, TOPLAS 1994, `doi:10.1145/197320.197383`, Figure 4, p. 1823). Viewing $V_{\text{new}}$ as a behavioral subtype of $V_{\text{old}}$ ($V_{\text{new}} <: V_{\text{old}}$) under abstraction function $A : S_{\text{new}} \to S_{\text{old}}$, upgrading $V_{\text{old}} \to V_{\text{new}}$ preserves all downstream proofs established against $V_{\text{old}}$'s abstract contract iff:

1. **Contravariant Precondition Rule (weakening = minor; strengthening = major):**
   $$\forall x.\; \text{Pre}_{\text{old}}(A(x)) \implies \text{Pre}_{\text{new}}(x)$$
   Tightening `requires(x >= 0)` to `requires(x > 0)` is a **MAJOR** break with identical `fn(i32) -> i32` signature.
2. **Covariant Postcondition Rule, guarded by $\text{Pre}_{\text{old}}$ (strengthening = minor; weakening = major):**
   $$\forall x, y.\; \bigl(\text{Pre}_{\text{old}}(A(x)) \land \text{Post}_{\text{new}}(x, y)\bigr) \implies \text{Post}_{\text{old}}(A(x), A(y))$$
   The $\text{Pre}_{\text{old}}$ guard is essential: behavior on newly admitted inputs ($\text{Pre}_{\text{new}} \land \neg\text{Pre}_{\text{old}}$) cannot falsify callers already proven to satisfy $\text{Pre}_{\text{old}}$. Conversely, weakening `ensures(y >= x)` to `ensures(y >= 0)` breaks downstream monotonicity proofs.
3. **Invariant & History Constraint Rule (Liskov-Wing Fig. 4, clauses 1 & 3):**
   - For abstract values **produced** by the library (covariant position), strengthening $I$ is minor and weakening $I$ is major: $\forall s.\; I_{\text{new}}(s) \implies I_{\text{old}}(A(s))$, and for all state transitions $\rho \prec \psi$, $\text{Constraint}_{\text{new}}(\rho, \psi) \implies \text{Constraint}_{\text{old}}(A(\rho), A(\psi))$.
   - For caller-constructed values passed in **input** position (contravariant position), the invariant acts as a precondition: *strengthening* it breaks callers.
4. **Effect / Exception / Termination Monotonicity:** $V_{\text{new}}$ may emit at most a subset of the panics/exceptions/effects allowed by $V_{\text{old}}$ and may not weaken a termination guarantee.
5. **Proof-Reuse Cutoff:** A checked refinement certificate $V_{\text{new}} <: V_{\text{old}}$ provides an exact **incremental verification cutoff** (`incremental-computation-adapton-salsa-buck2-and-build-system-graphs`): callers verified strictly against $V_{\text{old}}$'s opaque contract need not be re-verified. Transparent definitions (Lean `def` without `@[irreducible]`, unfolded `const fn`) destroy this cutoff by leaking body equality across crate boundaries.

#### 3.5 Compatibility Layer Taxonomy

| Compatibility Layer | Checked Subject | Example Break Missed by Lower Layers | Primary Checker | Automation Completeness |
| :--- | :--- | :--- | :--- | :--- |
| **Syntactic SemVer** | Version tuple `X.Y.Z` | Removing a `pub fn` in a patch release | Package resolver (`Cargo`, `PubGrub`) | None (social convention) |
| **Static API SemVer** | Exported AST / `rustdoc` JSON | Changing param `u32 -> u64`; adding field to exhaustive struct | `cargo-semver-checks`, `elm diff` | Incomplete in Rust (macros, `cfg`, inference); near-complete in Elm |
| **Coherence SemVer** | Global trait/impl graph | Adding `impl<T> From<T> for Vec<T>` (RFC 2451) | RFC 2451 rules, `cargo-semver-checks` (partial) | Decidable per-impl under closed orphan rules; non-local across crates |
| **Binary ABI SemVer** | ELF symbols + DWARF/CTF/BTF | Reordering C++ virtual methods; shifting `struct` field offsets | `libabigail` (`abidiff`) | Incomplete (misses inline/template ODR & opaque-factory conventions) |
| **Specification SemVer** | Formal `(Pre, Post, Inv, Effects)` | Tightening `requires(x >= 0)` to `x > 0`; relaxing `ensures(y >= x)` to `y >= 0` | Refinement proof / SMT check | Undecidable in general; sound & checkable via refinement certificates |

---

### 4. Polyglot Hermeticity Failures, `mtime` Freshness Traps, and Supply-Chain Trust Boundaries

Basis: normative + source + documentation + execution + derived

#### 4.1 Why Single-Language Package Managers Fail Polyglot & Verified Toolchains

Single-language package managers (`Cargo`, `pip`, `npm`, `Lake`, `opam`) assume every managed dependency is a source package from one registry while compilers, C libraries, proof assistants, and SMT solvers live in the ambient host OS. In `rust-lang/cargo@e3535167` (`src/compiler/custom_build.rs:329-405, 550-585`):

- **Ambient `build.rs` and `proc-macro` authority:** Transitive `build.rs` scripts execute natively with full user credentials, filesystem write rights, environment variables, and network access; procedural macros load as native shared libraries directly inside `rustc`.
- **Host `pkg-config` and dynamic-linker contamination:** `-sys` crates probe `/usr/include`, `/usr/lib`, `PATH`, and `pkg-config`, silently linking unpinned host libraries absent from `Cargo.lock`.
- **Verification-toolchain closure gap:** Formally verified builds couple `rustc`, MIR extractors, proof assistants (`Lean 4`/`Lake`), SMT solvers (`Z3`/`cvc5` with exact version, seed, and timeout determinism), and native linkers. No language registry hashes that polyglot closure, necessitating external hermetic layers (`Nix`, `Guix`, `Bazel`) or relocatable archives (`nix-guix-immutable-closures-mutable-roots-and-toolchain-archive-equivalence`).

#### 4.2 The Read-Only Content-Addressed Store `mtime` Freshness Trap

Immutable content-addressed stores such as `/nix/store` mount outputs read-only and normalize every file's modification time (`mtime`) to **1 second after the Unix epoch** (`1970-01-01 00:00:01 UTC`), breaking build tools that equate freshness with wall-clock monotonicity:

1. **Lean 4 Lake strict `<` comparison (`leanprover/lean4@8009d0a6`, `src/lake/Lake/Build/Trace.lean:99-102, 306-311, 366-390`):**
   ```lean
   @[specialize] public def MTime.checkUpToDate
     [GetMTime i] (info : i) (self : MTime)
   : BaseIO Bool := do
     match (← getMTime info |>.toBaseIO) with
     | .ok mtime => return self < mtime
     | .error _ => return false
   ```
   `BuildTrace` combines `hash : Hash` and `mtime : MTime` (`max t1.mtime t2.mtime`, line 370). When `BuildTrace.checkAgainstTime` runs against a Nix-normalized archive where both `.lean` inputs and prebuilt `.olean` outputs have `mtime = 1`, `1 < 1` evaluates to **`false`**, causing Lake to declare prebuilt artifacts stale and fail attempting to rebuild into a read-only tree—unless inputs are backdated to `mtime = 0` (`0 < 1`) or hash traces match. Moreover, `Lake.Hash` (`Trace.lean:99-102`) is a non-cryptographic `UInt64` (`-- TODO: Use a secure hash rather than the builtin Lean hash function`), making it unsuitable as an adversarial integrity key.
2. **Cargo `FingerprintMethod::Mtime` default (`rust-lang/cargo@e3535167`, `src/compiler/fingerprint/mod.rs:238-280, 1591-1605`):**
   `LocalFingerprint::CheckDepInfo` defaults to `FingerprintMethod::Mtime` (`mod.rs:1599`), switching to content-hash checking only under unstable `-Z checksum-freshness` (`cli_unstable().checksum_freshness`, line 1591). Mixing epoch-`1` store inputs with writable `target/` outputs triggers spurious `DirtyReason::FsStatusOutdated` rebuilds (`dirty_reason.rs`) or stale cache hits when distinct builds share identical normalized timestamps. (Python `.pyc` timestamp headers and pre-1980 ZIP wheel errors without `SOURCE_DATE_EPOCH=315532800` exhibit the same impedance mismatch.)

#### 4.3 Cryptographic Provenance (`in-toto` v1 & SLSA Build L1–L4) and Capability-Bounded Builds

Bounding supply-chain risk across polyglot builds separates dependency fetching, isolated compilation, and control-plane attestation:

- **in-toto Attestation Framework v1 (`in-toto/attestation@50bf0171`, `spec/v1/statement.md`, `provenance.proto`):** Binds immutable `subject` digests (`_type: "https://in-toto.io/Statement/v1"`) to `predicateType` + `predicate`. Crucially, `spec/v1/statement.md:54-56` warns that **subjects are matched purely by digest regardless of content type**, so verifiers must check artifact names/media types explicitly.
- **SLSA Provenance (`https://slsa.dev/provenance/v1`) and Build Levels L1–L4 (`slsa-framework/slsa@8c316167`, `spec/build-provenance.md`, `spec/build-requirements.md`, `spec/whats-new.md`):**
  ```json
  {
    "_type": "https://in-toto.io/Statement/v1",
    "subject": [{"name": "artifact.tar.zst", "digest": {"sha256": "..."}}],
    "predicateType": "https://slsa.dev/provenance/v1",
    "predicate": {
      "buildDefinition": {
        "buildType": "https://example.org/hermetic-polyglot-builder/v1",
        "externalParameters": {"source": "https://example.org/repo", "ref": "refs/tags/v1.0.0"},
        "resolvedDependencies": [
          {"uri": "git+https://example.org/repo@refs/tags/v1.0.0", "digest": {"gitCommit": "..."}},
          {"uri": "sbom://build-deps.cdx.json", "mediaType": "application/vnd.cyclonedx+json", "digest": {"sha256": "..."}}
        ]
      },
      "runDetails": {"builder": {"id": "https://example.org/trusted-control-plane"}}
    }
  }
  ```
  - **Build L1:** Provenance exists (best effort).
  - **Build L2:** Hosted control plane signs authentic provenance; `resolvedDependencies` may still be tenant-reported (`build-requirements.md:229-232`).
  - **Build L3:** Isolated build environment; provenance is **unforgeable** (signing keys isolated from build steps) and `externalParameters` MUST be complete (`build-requirements.md:241-265`), while `resolvedDependencies` remains best effort.
  - **Build L4 (`Dependencies complete`, `build-requirements.md:266-318`):** Added in the post-v1.1 SLSA Working Draft (generalizing v0.1's "Hermetic" requirement while moving independent rebuild verification to the `SLSA_BUILD_REPRODUCED` Verified Property). The trusted control plane **must** technically enforce completeness of `resolvedDependencies`—via control-plane pre-fetch, trusted network interception, or verified vendoring (optionally referencing a digest-verified, builder-signed CycloneDX/SPDX build-time SBOM).
- **Four-Layer Defense-in-Depth Control Architecture:**
  1. **Two-phase fetch vs. offline execution:** Perform network resolution and hash verification (`Cargo.lock`, `go.sum`, Nix fixed-output derivations, Bazel `MODULE.bazel.lock`) strictly prior to network-isolated, environment-scrubbed compilation and proof checking.
  2. **Content-addressed polyglot closures:** Pin compilers, proof assistants, SMT solvers, and native headers/libraries by cryptographic digest rather than ambient OS paths or wall-clock `mtime`.
  3. **Capability-restricted build scripts & proc-macros:** Confine `build.rs` and proc-macros (WASI Component Model or OS seccomp/namespace sandboxes) to read-only declared inputs and a single writable `OUT_DIR`, lifting native C builds into declarative graph actions.
  4. **Incremental human audit chains (`cargo-vet`):** Distinguish **"safe-to-run"** (no build-time exfiltration/RCE) from **"safe-to-deploy"** (production soundness) via version-to-version delta audits, complementing provenance attestations (for binary-embedded dependency metadata and DSSE bundles, see `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`).

---

### 5. Executable Probe Verification Results (`support/verify_version_solving_and_semver.py`)

Basis: execution + derived

Running `python3 -B support/verify_version_solving_and_semver.py` (Python 3.10+ stdlib only, deterministic) verifies seven executable models matching Sections 1–4:

1. **3-SAT -> Version Installability Reduction (Cox 2016 / Mancinelli 2006):** Solves Russ Cox's 4-variable, 4-clause satisfiable formula via `PubGrubMiniSolver`, recovering the unique assignment `{x1: False, x2: True, x3: True, x4: False}` (3 decisions, 1 conflict), and proves the 5-clause extension unsatisfiable (2 decisions, 2 conflicts, 20 learned derivations).
2. **PubGrub CDCL Derivation Tree:** Solves the canonical `root -> menu/icons/intl/dropdown` unsatisfiable diamond (`pubgrub-rs/pubgrub`, `src/solver.rs:133-146`), terminating in 1 conflict (7 derived incompatibilities) with a complete derivation tree rooted at `⊥`.
3. **Go MVS Lattice Join & Import Compatibility Rule:** Computes `mvs_build_list` on a diamond combining `D 1.3`, `D 1.4`, and major `D/v2 2.1`, deterministically selecting `{'A': '1.0.0', 'B': '1.2.0', 'C': '1.1.0', 'D': '1.4.0', 'D/v2': '2.1.0'}` with zero conflicts.
4. **Cargo Multi-Major Coexistence, Public-Dep Split & Native `links` Conflict:** Resolves `foo[major:1] = 1.2.0` alongside `foo[major:2] = 2.0.0`, flags `consumer 'app 1.0.0' observes split public type identities for 'foo': versions [1.2.0, 2.0.0]`, and proves the identical diamond **UNSAT** once both majors declare `links = "z"` (derivation tree rooted at `#5 external: native 'links = "z"' conflict between libz_sys 1.1.0 and libz_sys 2.0.0`).
5. **Variance-Aware Specification SemVer Checker (Liskov & Wing 1994):** Accepts weakened precondition + strengthened `Pre_old`-guarded postcondition + strengthened invariant as `minor/patch`, and rejects precondition strengthening (`x > 0` at `x = 0`), postcondition weakening (`y >= 0` at `(x = 1, y = 0)`), and invariant weakening (`s >= -1` at `s = -1`) as `major`.
6. **Rust RFC 2451 Coherence & Orphan-Rule Checker:** Confirms `Vec<T>` covers `T` while `#[fundamental]` `Box<T>` does not, classifying `impl<T> OldTrait<T> for OldType`, `impl<T> OldTrait for T`, `impl<T> From<T> for Vec<T>`, and `impl<T> ForeignTrait<NewType> for Box<T>` as `MAJOR`, and `impl<T> ForeignTrait<NewType> for Vec<T>` as `MINOR`.
7. **Read-Only Store Epoch `mtime` Freshness Trap:** Confirms `input_mtime = 1, artifact_mtime = 1` fails Lake's strict `<` test (`strict_mtime_up_to_date = False`) while passing content-hash freshness (`True`), whereas backdating input to `0` satisfies `0 < 1`.

## Boundaries

- **not examined:**
  - Empirical ecosystem-wide SemVer breakage rates across crates.io, npm, PyPI, or Maven Central were not measured directly.
  - Non-ELF ABI formats (Mach-O TBD stubs, PE/COFF exports, Swift library-evolution witness tables, WebAssembly Component Model canonical ABI subtyping) were not inspected at source level.
  - Alternative solvers (`libsolv`, `aspcud`, `uv`'s Python marker extensions on `pubgrub-rs`, Unison's content-addressed AST model) and Cargo `-Z checksum-freshness` vs. `-C incremental` performance were not inspected.
- **unknown:**
  - Whether Cargo will replace its DFS backtracking resolver (`src/resolver/mod.rs`) with `pubgrub-rs` in production, and how it would encode non-PubGrub rules (weak `dep?/feat` edges, cycle rejection, MSRV fallback), remains undecided upstream.
  - Whether mainstream proof-assistant package managers (`Lake`, `opam`/Rocq, `Dafny`, `Verus`) will adopt machine-checked Specification SemVer certificates (`V_new <: V_old`) for cross-package proof-cache cutoff is unknown.
- **known not to apply:**
  - Go MVS's conflict-free $O(|V|+|E|)$ guarantee **does not apply** once upper bounds, conflict exclusions, or flat-namespace singleton native libraries (`links`) enter the graph.
  - Liskov-Wing Specification SemVer proof reuse **does not apply** when downstream proofs unfold transparent upstream bodies or depend on unmodeled operational properties (stack usage, timing side channels, resource bounds).
  - SLSA Build L3 **does not guarantee** complete `resolvedDependencies` or hermeticity (platform-enforced only at Build L4), nor does SLSA provenance alone establish bit-for-bit reproducibility (`SLSA_BUILD_REPRODUCED`).
- **unsupported:**
  - `cargo-semver-checks@8f25eea7` does not support custom registries directly, general field/parameter/generic/lifetime type checks, automatic multi-feature-subset or multi-target scans in one run, or semantic/body SemVer checks (`README.md:131-133, 208-222, 267-272`).
  - `libabigail` (`abidiff@a769028c`) does not flag `SIZE_OR_OFFSET_CHANGE_CATEGORY` as `ABIDIFF_ABI_INCOMPATIBLE_CHANGE` (`8`), and cannot detect binary ODR breaks in header-inlined functions or templates lacking exported ELF symbols.
  - `in-toto` Statement v1 (`50bf0171`) does not bind subject digests to content types during default matching (`spec/v1/statement.md:54-56`).

## Evidence

All primary sources were inspected and verified on `2026-11-19`:

1. **Mancinelli et al. (ASE 2006):** F. Mancinelli, J. Boender, R. Di Cosmo, J. Vouillon, B. Durak, X. Leroy, R. Treinen, *"Managing the Complexity of Large Free and Open Source Package-Based Software Distributions,"* ASE 2006, pp. 199–208, `doi:10.1109/ASE.2006.49`.
2. **Abate et al. (JSS 2012) & Treinen/Zacchiroli (2008):** P. Abate, R. Di Cosmo, R. Treinen, S. Zacchiroli, *"Dependency solving: a separate concern in component evolution management,"* JSS 85(10):2228–2240, `doi:10.1016/j.jss.2012.05.018`; R. Treinen & S. Zacchiroli, `arXiv:0811.3620` (`doi:10.48550/arXiv.0811.3620`).
3. **Russ Cox Versioning Essays (`documentation`):** `research.swtch.com/version-sat` (2016-12-13), `vgo-mvs` (2018-02-20), `vgo-import` (2018-02-21).
4. **`dart-lang/pub@fe190660d68a4dd3070fe33fc406ff58d754dccc` (`normative`/`documentation`):** `doc/solver.md` (PubGrub definitions, propagation, conflict resolution, error reporting, CDCL/ASP differences).
5. **`pubgrub-rs/pubgrub@65355b4a1192c5a0fadb81f301e6dea713ae78d8` (`source`):** `src/solver.rs:179-315`; `src/internal/core.rs:127-165, 247-328, 362-420, 435-528, 706-755`.
6. **`golang/go@b496a3044e1dcdc3eed0af3e0e89db92f740d764` (`source`):** `src/cmd/go/internal/mvs/mvs.go:30-72, 90-450` (`Reqs`, `BuildList`, `Req`, `UpgradeAll`, `Upgrade`, `Downgrade`).
7. **`bazelbuild/bazel@3a881392ced3ddf4b9ae0cfdaaf20765c7d17cdb` (`source`):** `src/main/java/com/google/devtools/build/lib/bazel/bzlmod/Selection.java:43-63, 86-208, 233-305`.
8. **`rust-lang/cargo@e35351676760e4c90ccad19aaf85cec75e1af8b3` (`source`/`documentation`):** `src/resolver/types.rs` (`ActivationsKey`, `SemverCompatibility`, `ConflictReason`), `src/resolver/context.rs:19-125`, `src/resolver/mod.rs:1-60`, `src/compiler/links.rs:21-60`, `src/compiler/custom_build.rs:329-405, 550-585`, `src/compiler/fingerprint/mod.rs:238-280, 1591-1605`, `src/compiler/fingerprint/dirty_reason.rs`, `crates/resolver-tests/tests/pubgrub.rs:95-248`, `doc/book/src/reference/resolver.md`.
9. **`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (`normative`):** `text/1105-api-evolution.md:54-67, 162-446`, `text/2451-re-rebalancing-coherence.md:58-84, 165-250`, `text/3516-public-private-dependencies.md:13-17, 171-207, 269-391`, `text/3537-msrv-resolver.md`.
10. **`obi1kenobi/cargo-semver-checks@8f25eea7e6869fc6710431c3dbd89f020d20a65c` (`source`/`documentation`):** 274 `.ron` lints under `src/lints/`; `README.md:63-95, 131-133, 169-272`.
11. **`sourceware.org/git/libabigail.git@a769028c7a8f760f9d712a2fbdcf6bc430c8cfc9` (`source`/`documentation`):** `include/abg-comparison.h` (`enum diff_category`), `doc/manuals/abidiff.rst` (*Return values*).
12. **`in-toto/attestation@50bf01716982189898823e90586075f37cd9bb7d` (`normative`):** `spec/v1/statement.md:9-67`, `protos/in_toto_attestation/predicates/provenance/v1/provenance.proto`.
13. **`slsa-framework/slsa@8c3161670b7a6cf7bd6d858b2332ae7eb0838b0c` (`normative`):** `spec/whats-new.md`, `spec/build-provenance.md:40-318`, `spec/build-requirements.md:22-67, 159-319`.
14. **`leanprover/lean4@8009d0a64d2860606c6a5ac5ff6702622b24921e` (`source`):** `src/lake/Lake/Build/Trace.lean:99-102, 268-311, 366-390`.
15. **Liskov & Wing (TOPLAS 1994, `normative`):** ACM TOPLAS 16(6):1811–1841, `doi:10.1145/197320.197383`, Figure 4 (p. 1823).
16. **`semver/semver@f99d5485190a47c0863949e7da810a5553e0ed4d` (`normative`):** `semver.md` (§§1–11).
17. **Executable Probe (`execution`):** `python3 -B support/verify_version_solving_and_semver.py` exited `0` (`ALL VERIFICATION CHECKS PASSED.`).

## Revalidation

Use these narrow discriminating checks to revalidate against newer upstream revisions without repeating the full crawl:

1. **Re-run the standalone verification probe:**
   ```console
   python3 -B reports/package-management-version-solving-semver-and-supply-chain-boundaries/support/verify_version_solving_and_semver.py
   ```
   Confirm exit code `0` across all 7 assertion suites. This revalidates the formal models (3-SAT reduction, PubGrub CDCL, MVS join, Cargo `links`/public-pool checks, Liskov-Wing variance, RFC 2451 coherence, strict `<` epoch `mtime`), not live `cargo`/`go`/`lake`/`abidiff` binaries.
2. **Diff Cargo resolver, `links`, and checksum-freshness (`rust-lang/cargo`):** Diff `src/resolver/{mod.rs,context.rs}`, `src/compiler/links.rs`, `src/compiler/fingerprint/mod.rs`, and `crates/resolver-tests/tests/pubgrub.rs` against `e3535167` to check whether PubGrub replaced DFS backtracking, RFC 3516 `public = true` stabilized or entered the resolver, `validate_links` changed, or `checksum_freshness` became default.
3. **Diff `cargo-semver-checks` coverage (`obi1kenobi/cargo-semver-checks`):** Compare the count of `src/lints/*.ron` (274 at `8f25eea7`) and the `Will cargo-semver-checks catch every semver violation?` FAQ against `8f25eea7` for general type/generic/lifetime or multi-target/feature-subset support.
4. **Diff `libabigail` exit codes (`sourceware.org/git/libabigail.git`):** Inspect `doc/manuals/abidiff.rst` (*Return values*) and `include/abg-comparison.h` (`enum diff_category`) against `a769028c` for new categories setting `ABIDIFF_ABI_INCOMPATIBLE_CHANGE`.
5. **Diff Lean 4 Lake freshness and hashing (`leanprover/lean4`):** Inspect `src/lake/Lake/Build/Trace.lean` against `8009d0a6` for changes to `MTime.checkUpToDate` (`<` vs `<=` / hash-only) and `Lake.Hash` (`UInt64` vs cryptographic hash).
6. **Diff SLSA Build L4 ratification (`slsa-framework/slsa`):** Inspect `spec/whats-new.md` and `spec/build-requirements.md` against `8c316167` to check whether Build L4 (`Dependencies complete`), the Source Track, and `SLSA_BUILD_REPRODUCED` have been ratified in a versioned SLSA release.
