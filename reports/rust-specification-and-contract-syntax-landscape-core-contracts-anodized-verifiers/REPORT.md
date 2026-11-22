# Rust Specification and Contract Syntax Landscape: `core::contracts`, `verify-rust-std`, `anodized`, Verifier DSLs, and Multi-Frontend Lowering

## Summary

No single Rust specification syntax simultaneously provides (a) official long-term standardization with zero third-party dependency, (b) stable-`rustc` compilation with IDE integration and cross-verifier portability today, and (c) full systems-Rust expressive power (non-`'static` `&mut` postconditions with `old!`, raw-pointer provenance/memory predicates, `unsafe trait` safety invariants, unwind vs. abort effect masks, unbounded quantifiers, relational 2-safety, and concurrency/protocol refinement).

Comparative primary-source inspection across Rust's official contract efforts, community Design-by-Contract (DbC) crates, nine Rust formal verification tools, historical Anneal designs, and cross-language contract systems establishes five load-bearing conclusions:

1. **Decouple specification *frontends* from a syntax-independent MIR contract core.** Any specification surface whose clauses compile to side-effect-free boolean Rust MIR closures or companion functions can be evaluated by the verifier's existing operational semantics (read-only execution returning `true` with unchanged caller memory), avoiding a second Rust expression evaluator in the Trusted Computing Base (TCB).
2. **`core::contracts` (`#![feature(contracts)]`, `rust-lang/rust#128044`) is the long-term standard but is structurally incomplete for systems Rust today.** Its dead-branch `if false` lowering at `-Zcontract-checks=no` enables zero-lock-in MIR extraction without runtime or Tree Borrows perturbation, but `build_check_ensures<Ret, C: Fn(&Ret) -> bool + Copy + 'static>` blocks `&T`/`&mut T` and non-`Copy` captures, the parser allows at most one `#[requires]` and one `#[ensures]`, side-effecting expressions in `#[ensures]` execute even under `-Zcontract-checks=no` (`rust-lang/rust#139548`), CTFE and `become` tail calls silently bypass checks, and Miri rejects active contract intrinsics.
3. **`verify-rust-std` (`model-checking/verify-rust-std`) supplies the canonical stdlib safety-predicate seam.** Its `library/contracts/safety` crate (`#[safety::{requires,ensures,loop_invariant,invariant}]`, `#[derive(Invariant)]`) explicitly dispatches per-tool modules, and its `core::ub_checks::{Invariant, predicates::{can_dereference, can_read_unaligned, can_write, can_write_unaligned, same_allocation}}` directly embodies Rust's Unsafe Code Guidelines validity-vs.-safety invariant split.
4. **`anodized` (`anodized-rs/anodized`, `v0.8.0`) is the strongest stable-Rust, multi-verifier community syntax today, with six concrete gaps to guard against.** It reuses Rust struct-initializer syntax (`#[spec(pure, total, requires: [...], maintains: [...], captures: [...], ensures: |out| [...], decreases: ...)]`), compiles on stable `rustc` with `rust-analyzer` and `anodized-fmt`, ships `anodized-logic` (`int`, `Logical<T>`, `forall`, `exists`, `implies!`), supports `anodized_embed_specs`, `anodized_charon` (for Charon/Aeneas), and `hax` lowering. However, its current release has non-short-circuiting `&` clause joins (`anodized#240`), non-zero-cost default `captures` (`anodized#232`), a `mut`-parameter postcondition bug (`anodized#235`), Cargo host-vs.-target `RUSTFLAGS` proc-macro `cfg` friction, no `unsafe` memory/trait/unwind vocabulary, and bus-factor-1 pre-1.0 churn.
5. **A four-layer multi-frontend architecture maximizes both standardization and expressivity without TCB bloat:**
   - **Layer 1 (Upstream Standard):** Native `core::contracts` (`-Zcontract-checks=no`) + `verify-rust-std` `#[safety::*]` / `ub_checks::Invariant` + Kani-compatible attribute adapters.
   - **Layer 2 (Stable Cross-Tool Standard):** `anodized` (`#[spec(...)]`) ingested via static companion MIR items (strictly outside the TCB, with short-circuit `&&` enforcement and upstream fixes for MIR lowering and zero-cost captures).
   - **Layer 3 (Minimal Systems-Rust Extensions, 0 TCB LOC):** Thin additive macros strictly for gaps absent from Layers 1–2 (`#[external_spec]`, `#[unsafe_trait]`/`#[unsafe_impl]`, ghost memory provenance predicates aligned 1-to-1 with `verify-rust-std`, `no_unwind` vs. `no_abort` / `post_unwind`, explicit `trusted` waivers, and 2-safety equivalence hooks).
   - **Layer 4 (Proof-Assistant Escape Hatch):** External declarative specification modules (e.g., tactic-free Lean 4 `Spec.lean`) for unbounded inductive models, relational 2-safety, weak-memory concurrency, and protocol refinement.

## Applicability

This report characterizes the Rust specification and contract syntax ecosystem as observed on `2026-11-22` across the exact upstream repository revisions and crate versions listed in `REPORT.json`:

- **Official Rust project:** `rust-lang/rust` (`ce66487ebbd7541212d22d01c39a808057d69f1f`), tracking issues `rust-lang/rust#128044`, `#123646`, `#132922`, `#130516`, `#128274`, `#139548`, and compiler-team MCPs `#759`, `#813`, `#942`. Empirical MIR/CTFE/Miri behavior of `#![feature(contracts)]` and `TyKind::Pat` is cross-referenced from sibling corpus reports observed on `2026-11-22` (`rustc-native-contracts-requires-ensures-runtime-checks-and-ctfe-soundness` and `rustc-pattern-types-niche-stacking-llvm-range-and-miri-validity-soundness`).
- **Standard-library verification:** `model-checking/verify-rust-std` (`1feeadd937956b8067ec2fb147ef55469361dab4`).
- **Community DbC & specification crates:** `anodized-rs/anodized` (`8fb862e952ab893643095a3365734af20b48e3bb`, crates.io `v0.8.0`), `x52dev/contracts` (`3d8bea443a5bd804e27fc1d78294cc18cbb1b1b4`, `v0.6.11`), plus crates.io metadata queried on `2026-11-22` for `pre` (`v0.2.1`), `mirai-annotations` (`v1.12.0`), `static_assertions` (`v1.1.0`), `dbc` (`v0.3.3`), `adhesion` (`v0.5.0`), `hoare` (`v0.1.1`), `deal` (`v0.1.0`), and `hax-lib` (`v0.5.0`).
- **Rust formal verification tools:** `verus-lang/verus` (`1ce6a59bd72713cf486a7660097fe5ac57519617`), `creusot-rs/creusot` (`faeb61f5b5a8ffda94fde1f100ef96a1d798088b`), `model-checking/kani` (`87c87010eda7797d7fa14033ca68bcbe17184a63`), `flux-rs/flux` (`828d6086c94a1171fce81fab449ace2abc9e1540`), `prusti/prusti` (`d1196b5dd0c5874969d1913b33a48022f4236913`), `pereq-dev/hax` (`0d2f66ed697c46d7c0f5038150b7c9679e4d954b`), `AeneasVerif/aeneas` (`2e3d4488280bb8a95411db81019a7854a784861f`), `GillianPlatform/gillian-rust` (`83d739e83034d71162fb66b569041cf301123df7`), and MPI-SWS RefinedRust (documentation/papers).
- **Anneal historical evolution:** `google/zerocopy` at `a007a51af473e5901915b003083e61c7c89c7bd1` (v2 documentation) and tag `anneal-v0.1.0-alpha.23` at `a3ad195abf85896be6f07f11acb486ceb7d61900` (v1 historical doc-comment DSL), plus `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).
- **Cross-language contract systems:** ACSL (Frama-C), SPARK/Ada 2012, Dafny, Spec#/JML, Swift, and C++26 Contracts (WG21 P2900), drawn from public specifications, literature, and sibling corpus reports (`ott-verso-antiquotations-spark-openjml-contracts-and-jdoctor-comment-drift`, `contract-instrumentation-multi-exit-ensures-check-erasure-equivalence-and-flag-scoping`).

Findings apply to behavioral specification authoring and MIR-level contract ingestion for Rust verification toolchains; they do not evaluate SMT solver performance or interactive proof-search tactics.

## Findings

### 1. Official Rust Project Efforts (`core::contracts`, `verify-rust-std`, Pattern Types, and `unsafe_fields`)

#### 1.1 `core::contracts` (`#![feature(contracts)]`, `rust-lang/rust#128044`)

`Basis: source + execution (sibling corpus probes) + documentation`

Rust's experimental native contract feature (`rust-lang/compiler-team#759`, initial implementation PR `rust-lang/rust#128045` merged `2025-02-05`, T-lang liaison `@Nadrieril`, de-facto owner `@celinval`, `#t-lang/contracts` Zulip channel) exposes `core::contracts::{requires, ensures}` via three compiler lang items:

```rust
// library/core/src/contracts.rs
#[lang = "contract_build_check_ensures"]
pub const fn build_check_ensures<Ret, C>(cond: C) -> C
where
    C: Fn(&Ret) -> bool + Copy + 'static,
{
    cond
}
```

alongside `core::intrinsics::contract_check_requires` (`#[lang = "contract_check_requires"]`) and `core::intrinsics::contract_check_ensures` (`#[lang = "contract_check_ensures"]`).

Measured compiler behaviors (cross-referenced from `rustc-native-contracts-requires-ensures-runtime-checks-and-ctfe-soundness`, observed `2026-11-22` on `1.98.0-nightly` through `1.102.0-nightly`) determine how static verifiers must ingest `core::contracts`:

1. **Dead-branch MIR preservation under default `-Zcontract-checks=no`:** AST-to-HIR lowering (`compiler/rustc_ast_lowering/src/contract.rs`) emits `if false { ... }` guards wrapping `contract_check_requires`, `build_check_ensures`, and `contract_check_ensures`. Because the guard is a `const false` `switchInt` in `Runtime(PostCleanup)` MIR, the typechecked, borrowchecked contract closures remain intact in `TyCtxt` while the runtime control-flow path is untouched.
2. **Unsoundness of capturing with `-Zcontract-checks=yes`:** Enabling runtime checks inserts shared borrows (`&_1`) of parameters before the body executes (perturbing Tree Borrows aliasing on `&mut T` arguments) and aborts via `panic_nounwind` on false preconditions (masking UB that occurs in production `-Zcontract-checks=no` builds). Static verifiers must therefore capture strictly at `-Zcontract-checks=no`.
3. **Hard expressivity limits in current `rustc`:**
   - `build_check_ensures`'s `+ Copy + 'static` bound prevents `#[ensures]` from capturing `&T` or `&mut T` parameters (failing lifetime checks), rejects non-`Copy` captures (`E0277`), rejects reference captures without `move` (`E0597`), and triggers `E0282` type inference errors on `ret.method()` without explicit annotations.
   - The parser permits at most one `#[requires]` and one `#[ensures]` per function (`#[requires]` must precede `#[ensures]`).
   - There is no `old(...)` construct, no type/trait invariant attribute, no quantifier vocabulary, and no pointer-provenance predicate.
4. **Measured dynamic/soundness surprises:**
   - **Side effects execute even under `-Zcontract-checks=no` (`rust-lang/rust#139548`, open):** `#[core::contracts::ensures({ *x = 0; |_ret| true })]` mutates `*x` unconditionally even with contract checks disabled, because the outer expression evaluates outside the closure.
   - **CTFE bypass:** Both contract intrinsics use `const_eval_select!` with an empty `if const {}` arm, silently skipping violated contracts during constant evaluation even with `-Zcontract-checks=yes`.
   - **Miri incompatibility:** Miri rejects active contract intrinsics with `unsupported operation` because they lack `#[miri::intrinsic_fallback_is_spec]`.
   - **Return-path gaps:** `#[ensures]` intercepts implicit returns, `return`, `?`, and `do yeet`, but is silently bypassed by explicit tail calls (`become`) and unwinding panics.
   - **Defining-crate flag scoping:** Cross-crate runtime checking follows the defining crate's `-Zcontract-checks` flag, even across `#[inline(always)]` and generic instantiations.
5. **Active evolution directions:** Open tracking items include `for safety:` vs. `for correctness:` contract forms (`compiler-team#759`), exhaustive vs. non-exhaustive contracts (`rust-lang/rust#128274`), post-borrow obligations (`#[safety::at_lifetime_end(|out| ...)]` on `#128044`), and Fulminate-style separation-logic ownership primitives (`owned` and `alloc_block`, `compiler-team#942`).

#### 1.2 `verify-rust-std` (`model-checking/verify-rust-std`) and the Safety-Critical Rust Consortium

`Basis: source + documentation`

`model-checking/verify-rust-std` (`1feeadd937956b8067ec2fb147ef55469361dab4`, 373 stars) coordinates formal verification of `core`, `alloc`, and `std` across six CI-approved tools (`doc/src/tools.md`: ESBMC, Flux, Kani, KMIR, RAPx, VeriFast), aligned with the Rust Foundation's Safety-Critical Rust Consortium (formed June 2024 targeting ISO 26262, IEC 61508, and DO-178C certification).

Its contract and predicate infrastructure consists of two reusable seams:

1. **Tool-dispatching `library/contracts/safety/src/lib.rs`:** Exports `#[safety::requires]`, `#[safety::ensures]`, `#[safety::loop_invariant]`, `#[safety::invariant(...)]`, and `#[derive(safety::Invariant)]`. Currently dispatches `#[cfg(kani_host)]` to `kani.rs` (`#[kani_core::*]`) and `#[cfg(not(kani_host))]` to no-ops in `runtime.rs`, explicitly documenting *"Each tool should implement their own version in a separate module of this crate."*
2. **Type invariants and ghost memory predicates in `library/core/src/ub_checks.rs`:**
   ```rust
   pub trait Invariant {
       /// Specify the type's safety invariants (UCG validity vs. safety invariant)
       fn is_safe(&self) -> bool;
   }
   ```
   plus `core::ub_checks::predicates::{can_dereference, can_read_unaligned, can_write, can_write_unaligned, same_allocation, float_to_int_in_range}` (backed by `kani::mem::*` under `#[cfg(kani)]` and returning `true` stubs otherwise).

Open `verify-rust-std` issues (`#693` aliasing in `Rc/Arc::get_mut_unchecked`, `#712` allocator provenance in `__rdl_dealloc`, `#783` `NonNull` dereferenceability, and `#734` polymorphic generic `T` verification without monomorphization) empirically confirm that pure runtime boolean predicates cannot capture raw-pointer provenance/aliasing and that bounded monomorphic tools struggle with generic library traits.

#### 1.3 Type-System and Compiler-Intrinsic Invariant Mechanisms

`Basis: source + execution (sibling corpus probes)`

- **Pattern Types (`TyKind::Pat`, `rust-lang/rust#123646`, perma-unstable):** By 2026, `pattern_type!(u8 is 1..=10)` and `!null` replaced legacy `#[rustc_layout_scalar_valid_range_{start,end}]` across `NonNull`, `NonZero`, and `BoxRaw`. They lower to a single contiguous modular `WrappingRange` (rejecting unsigned `Or`-patterns at layout time) with transmute-only construction (`compiler-team#807`). They encode **compiler language validity invariants** (enabling niche optimization and LLVM `!range`/`!nonnull`), not multi-field relational invariants (`start <= end`), heap invariants, or postconditions.
- **`unsafe_fields` (RFC 3458, `rust-lang/rust#132922`, RFC-approved) and `unsafe_binders` (`#130516`):** Statically mark struct fields whose mutation requires `unsafe` because they carry library safety invariants. This complements behavioral contract attributes by mechanically narrowing the encapsulation visibility cone that must preserve a type's safety invariant.
- **`core::hint::assert_unchecked` (stabilized Rust 1.81) and `core::ub_checks::assert_unsafe_precondition!`:** `assert_unchecked` turns a false condition into immediate UB/optimizer miscompilation and must be treated by static verifiers strictly as a **proof obligation**, never as a specification assumption. `assert_unsafe_precondition!` splits immediate AM UB (`check_language_ub`, disabled in Miri) from library checks (`check_library_ub`), lowering to `Operand::RuntimeChecks(UbChecks)` which cannot check provenance, initialization, or Tree Borrows aliasing.

---

### 2. Deep Analysis of `anodized` (`anodized-rs/anodized`) and Community DbC Crates

#### 2.1 `anodized` (`v0.8.0`, `8fb862e952ab893643095a3365734af20b48e3bb`)

`Basis: source + execution (crates.io/GitHub metadata query on 2026-11-22)`

- **Ecosystem Metrics:** Created `2025-08-19`, pushed `2026-11-11`, 121 GitHub stars, 8 forks, MIT/Apache-2.0, crates.io `v0.8.0` (`2026-10-29`) with 8,917 total downloads (5,123 recent). Primary author `mkovaxx` accounts for 125 of 139 commits (bus factor 1).
- **Architecture and Syntax:** Positions itself as a shared stable-Rust specification layer ("Serde for specifications") and explicitly plans a migration tool when native `core::contracts` stabilizes (`README.md`).
  - **Unified `#[spec(...)]` grammar (`crates/anodized-core/src/syntax/spec_attrib.rs`):** Reuses Rust's `struct`-initializer field grammar (`syn::FieldValue`), giving 100% standard Rust expressions checked by stable `rustc`, `rust-analyzer`, and a companion formatter (`anodized-fmt`).
  - **Seven behavioral qualifiers (`crates/anodized-core/src/qualifiers.rs`):** Bitflags `DETERMINISTIC` (`1<<0`), `EFFECTFREE` (`1<<1`), `INFALLIBLE` (`1<<2`, *"does not panic or abort"*), `TERMINATING` (`1<<3`, *"does not run forever"*), plus combinations `PURE` (`DETERMINISTIC | EFFECTFREE`), `TOTAL` (`INFALLIBLE | TERMINATING`), and `FUNCTIONAL` (`PURE | TOTAL`).
  - **Ordered clauses (`crates/anodized/REFERENCE.md`):** `requires`, `maintains` (both pre- and post-invariant), `captures` (entry-time bindings `old_x = *x` or destructuring patterns), `ensures` (plain `bool` or closure `|out|` / `|(a, b)|` / `|ref out|` supporting non-`Copy` return values via reconstruction), and loop `maintains`/`decreases`. Per-clause `#[cfg(...)]` attributes toggle runtime checks while still typechecking every clause in all builds.
  - **Traits and type refinements:** Trait-method specs enforce Liskov qualifier narrowing at compile time via `const { assert!(Self::__anodized_fn_qualifiers_f == Self::__anodized_fn_qualifiers_trait_f | Self::__anodized_fn_qualifiers_f) }` (`crates/anodized-core/src/instrument/fns.rs:139-146`). Struct/enum refinements (`#[spec(maintains: ...)]`) are selectively enforced at function boundaries via `Spec!(T)`, `Spec!(T, out)`, and `Spec!(T, inout)`.
  - **`anodized-logic`:** Provides arbitrary-precision `int` (`BigInt` with primitive interop), zero-sized `Copy + Eq` logical lifting `Logical<T: ?Sized>`, 1–5 arity `forall`/`exists` closures, `implies!(p, q)`, and planned `old!(x)` (`anodized#233`).
  - **Multi-backend instrumentation (`--cfg anodized_*`):**
    * Runtime modes: `anodized_panic`, `anodized_print`, `anodized_try` (`Result`-returning `try_call!`).
    * Static analysis modes: `anodized_embed_specs` (emits hidden companion functions `__anodized_fn_{requires,ensures,qualifiers}_<fn>` without modifying runtime bodies), `anodized_charon` (adds `#[charon::contract(kind = "precondition"|"postcondition", for = "<fn>")]` integrated with `AeneasVerif/charon#1361` for `cargo anodized verify-aeneas`, `anodized#247`), and Hax translation (`crates/anodized-core/src/instrument/hax.rs` emitting `#[hax_lib::requires/ensures]` and `loop_invariant!`). Open issue `anodized#226` tracks native MIR lowering.
- **Six Concrete Technical Gaps Identified in Source Inspection:**
  1. **Non-short-circuiting `&` clause join (`crates/anodized-core/src/instrument/fns.rs:591`, `anodized#240` open):** Clauses are combined via bitwise `&` (`let __anodized_pre = __anodized_pre & #expr;`) so runtime mode prints every failing clause. This causes panics/UB on dependent clauses such as `requires: [i < v.len(), v[i] == 42]`. Static MIR verifiers must enforce short-circuiting `&&` (matching SPARK/Dafny).
  2. **Non-zero-cost default `captures` (`REFERENCE.md:35`, `anodized#232` open):** With no `anodized_*` flags, `captures` expressions (such as `.clone()`) still execute at runtime unless `anodized_discard_specs` or `anodized_embed_specs` is set.
  3. **Host-vs.-target `RUSTFLAGS` proc-macro `cfg` friction:** Because `anodized-macros` selects `Mode::EmbedSpecs` via `cfg!(anodized_embed_specs)` during host proc-macro compilation, target `RUSTFLAGS` in cross-compilation do not activate embedded spec emission (tracked by `anodized#244` proposing an `ANODIZED_MODE` environment variable).
  4. **Exit-time `mut` by-value input bug (`anodized#235` open):** Postconditions currently read the mutated local value of a `mut x: T` parameter rather than its entry-time value.
  5. **No systems-Rust `unsafe` vocabulary:** Lacks raw-pointer provenance/validity predicates, `unsafe trait` type-level invariants, `postUnwind` / `no_unwind`-vs.-`no_abort` separation (`INFALLIBLE` merges unwind and abort), `#[external_spec]` sidecars for unowned crates, and explicit `trusted` waiver accounting.
  6. **Pre-1.0 churn and bus factor 1:** Syntax changed materially in recent releases (`#174`–`#177`), with further breaking refinements open (`#235`, `#239`, `#240`).

#### 2.2 Other Community Rust DbC Crates

`Basis: source + execution (crates.io API query on 2026-11-22)`

| Crate (`version`) | Repository & Last Update | Downloads (Recent) | Syntax & Mechanism | Static-Verifier Suitability |
| :--- | :--- | :---: | :--- | :--- |
| **`contracts`** (`0.6.11`) | `x52dev/contracts` (`2026-10-05`) | 1,829,364 (351,557) | `#[requires]`, `#[ensures(ret -> ... old(...))]`, `#[invariant]`, `#[debug_*]` | Runtime-only; rewrites function bodies directly with assertions and introduces non-Rust `->` implication syntax; no static companion-MIR mode. |
| **`pre`** (`0.2.1`) | `aticu/pre` (`2021-09-21`) | 142,460 (3,352) | `#[pre("prose")]` / `#[assure("prose", reason = "...")]` | Unsuitable: prose strings carry no formal semantics, and injecting a ZST parameter alters function signatures/ABI. |
| **`mirai-annotations`** (`1.12.0`) | `facebookexperimental/MIRAI` (`2021-07-06`) | 10,732,778 (482,395) | Imperative body macros (`precondition!`, `postcondition!`, `verify!`, `assume!`) | Unsuitable: embeds specifications inside implementation bodies rather than cleanly separable interface contracts; unmaintained since 2021. |
| **`static_assertions`** (`1.1.0`) | `nvzqz/static-assertions-rs` (`2019-11-03`) | 626,654,035 (160,955,666) | `const_assert!`, `assert_impl_all!` | Orthogonal: compile-time type/const checks only, not behavioral contracts. |
| **`dbc` / `adhesion` / `hoare`** | Unmaintained (`2015–2018`) | 4,909–14,175 | Legacy macros / pre-proc-macro compiler plugin | Obsolete historical precursors. |
| **`deal`** (`0.1.0`) | `schneedotdev/deal` (`2025-02-07`) | 839 (4) | Playing-card deck library | Not a DbC crate (name collision with Python's `deal` package). |

---

### 3. Rust Formal Verification Tool Syntaxes

`Basis: source + documentation`

Direct inspection of proc-macro exports and specification models across nine Rust verifiers shows a clear spectrum from **ordinary Rust expressions** to **embedded prover DSLs**:

| Tool (Stars, Last Push) | Verified Macro / Attribute Surface | Key Expressive Capabilities | Core Adoption Friction |
| :--- | :--- | :--- | :--- |
| **Verus** (`verus-lang/verus`, 3,902★, `2026-11-22`) | `verus!{}` whole-module macro; `spec`/`proof`/`exec` modes; `requires`, `ensures`, `recommends`, `decreases`, `old()`, `Ghost`, `Tracked`, `View`/`DeepView`, `PointsTo`, `PCM` | High SMT proof velocity on systems/OS Rust; linear ghost permissions; concurrent `AtomicInvariant` | Non-standard Rust DSL breaks `rustfmt`/`rust-analyzer` and unmodified-crate builds (requires wrappers or AST strippers); Z3 trigger brittleness and SMT in TCB. |
| **Creusot** (`creusot-rs/creusot`, 1,980★, `2026-11-20`) | `#[requires]`, `#[ensures]`, `#[invariant]`, `#[variant]`, `#[logic]`, `#[maintains]`, `#[trusted]`, `#[opaque]`, `pearlite!{}`, prophecy `^x` | Prophecies (`^x == *x + 1`) cleanly specify `&mut` updates without explicit captures; strong trait/iterator specs | Custom Pearlite expression syntax; nightly compiler driver; safe Rust only natively (raw-pointer `unsafe` delegated to Gillian-Rust). |
| **Kani** (`model-checking/kani`, 3,738★, `2026-11-22`) | `#[kani::requires]`, `#[kani::ensures]`, `#[kani::modifies]`, `#[kani::panics_if]`, `#[kani::panics_only_if]`, `#[kani::loop_invariant]`, `#[kani::loop_decreases]`, `#[kani::recursion]`, `#[derive(kani::Invariant)]`, `kani::mem::*` | Standard Rust boolean expressions; explicit `modifies` framing; explicit panic contracts; raw-pointer memory predicates; `verify-rust-std` adoption | Bounded model checking (unwinding limits); monomorphization-only; CBMC/SAT solver in TCB. |
| **Flux** (`flux-rs/flux`, 946★, `2026-11-21`) | `#[flux::sig(...)]`, `#[flux::spec]`, `#[flux::refined_by]`, `#[flux::invariant]`, `#[flux::qualifiers]`, `#[flux::trusted]` | Liquid type inference cuts annotation volume; strong mutable-borrow updates (`&strg`) | Bespoke refinement-type DSL inside attributes; limited `unsafe`/raw-pointer memory semantics; Z3 in TCB. |
| **Prusti** (`prusti/prusti`, 1,839★, `2026-11-22`) | `#[requires]`, `#[ensures]`, `#[invariant]`, `#[after_expiry]`, `#[assert_on_expiry]`, `#[pure]`, `#[trusted]`, `#[extern_spec]`, `#[refine_trait_spec]`, `#[model]` | Pioneered `#[extern_spec]` and `#[after_expiry]` pledges for functions returning `&mut T` | Custom expression parser; Viper/Boogie/Z3 TCB; limited `unsafe` coverage. |
| **hax** (`pereq-dev/hax`, 509★, `2026-11-19`; `hax-lib` 5.6M dl) | `#[hax_lib::requires]`, `#[hax_lib::ensures]`, `#[hax_lib::lemma]`, `loop_invariant!`, `loop_decreases!`, backend quotes (`fstar`/`lean`) — **also consumes `anodized`** | Multi-backend extraction (Lean via Aeneas, F*, Rocq, ProVerif) used on production cryptography | Functional/safe Rust subset; backend-quoting attributes leak prover-specific syntax into Rust source. |
| **Aeneas** (`AeneasVerif/aeneas`, 1,245★, `2026-11-22`) | External Lean 4 `@[step]` / `WP.spec` / `WP.dspec` theorems; `#[charon::contract]` via `anodized_charon` | Zero Rust source clutter; full Lean 4 expressivity | Safe Rust only (`unsafe` leaves remain axioms in `FunsExternal.lean`); requires Lean knowledge when authored externally. |
| **Gillian-Rust** (`GillianPlatform/gillian-rust`, 7★, `2025-05-21`) | Separation-logic predicates (`RustBelt` + `RustHornBelt`) bridging `unsafe` code into Creusot | Modular `unsafe`→safe verification bridge (`LinkedList`) | Early research prototype; specialist separation-logic notation. |
| **RefinedRust** (MPI-SWS, PLDI 2024) | `#[rr::params]`, `#[rr::args]`, `#[rr::exists]`, `#[rr::returns]`, `#[rr::requires]`, `#[rr::ensures]` | Foundational Iris/Rocq soundness for `unsafe` Rust with place types and spatial layouts | Embeds raw Rocq/Iris separation-logic strings (`"⌜x + 42 ∈ i32⌝"`) inside Rust attributes; no `rustc` checking of spec bodies; high specialist barrier. |

---

### 4. Historical Anneal Syntax Evolution and Lessons

`Basis: source`

Public `google/zerocopy` history (`#2777`, `#3031`, `#3062`, `#3086`, `#3091`, `#3203`, `#3380`, `#3697`, `#4102`, and tag `anneal-v0.1.0-alpha.23`) documents three architectural pivots:

1. **Safety-comment Lean extraction (`google/zerocopy#2777`, `#3031`, closed):** Attempted to extract Lean from `// SAFETY:` comments, motivating automatic propagation of `unsafe trait` invariants (`FromBytes`/`IntoBytes`) from `where`-bounds into generic bodies. Abandoned because comments are invisible to `rustc`/`rust-analyzer` and prone to code–comment drift.
2. **Fenced doc-comment DSL (`anneal-v0.1.0-alpha.23`, `anneal/docs/agent/04_specifications_and_syntax.md`, `#3062`, `#3086`):** Used `/// ```anneal` blocks with an indentation-sensitive off-side parser (`requires(name):`, `ensures(name):`, `isValid`, `isSafe`, `context:`, `unsafe(axiom):`, Lean strict implicit binders `{{ }}`, and `h_anon` singleton limits). Hit four walls: (a) forced Lean and Aeneas internals onto Rust authors (`#3697`), (b) custom whitespace-sensitive parser fragility, (c) `unsafe(axiom)` implicitly asserted termination/progress rather than partial correctness (`#3091`), and (d) implicit-return `ensures` could not express diverging (`-> !`) or conditionally panicking (`Option::unwrap`) functions (`#3203`).
3. **MIR-native contract core (`google/zerocopy:main` `anneal/docs/design.md`, `anneal/THREAT_MODEL.md`, `#4102`):** Separates bounded human review surfaces (stated specifications + TCB audit log) from unreviewed Lean proof scripts, enabling pure-Rust Tier-1 contracts to lower through `Runtime(PostCleanup)` MIR while retaining external declarative `Spec.lean` as a Tier-2 escape hatch.

---

### 5. Cross-Language Contract Lessons

`Basis: documentation + source (sibling corpus reports)`

- **C++26 Contracts (WG21 P2900):** Allowing side-effecting predicates while permitting compilers to elide or repeat checks, combined with conflicting per-translation-unit evaluation semantics (`ignore`/`enforce`/`observe`) and constification overload surprises, triggered major safety criticism. **Rule for Rust verifiers:** enforce pure, read-only contract evaluation (`mem' = callerMem`) and never condition static verification semantics on runtime check flags.
- **ACSL (Frama-C) and JML (OpenJML):** Comment-embedded DSLs (`/*@ ... @*/`) bypass host compiler typechecking and IDE refactoring (sibling report `ott-verso-antiquotations-spark-openjml-contracts-and-jdoctor-comment-drift` documents `Fraco`'s $>50\%$ rename fragility and `DocRef`'s $46.4\%$ code-name mismatch rate). Omitting `assigns` frame clauses destroys caller invariants across calls. **Rule:** specifications must be compiler-checked host-language syntax (or kernel-checked external modules), never comments; raw-pointer `unsafe` APIs require explicit framing beyond Rust's `&mut` borrow checker.
- **SPARK / Ada 2012:** Demonstrates the ergonomic sweet spot: host-language boolean expressions (`Pre`, `Post`, `Contract_Cases`), short-circuiting multi-clause conjunctions, `X'Old`, and dual runtime-test + static-proof semantics. GNATprove probes in the sibling report also show that weak/missing standard-library contracts block downstream proofs — confirming the necessity of sidecar `#[external_spec]` and direct dependency MIR verification.
- **Dafny and Spec#:** Highlight three mandatory guards: explicit termination metrics (`decreases`) so non-termination cannot vacuously satisfy postconditions, unambiguous distinction between fixed-width machine integers and unbounded mathematical integers (`int`), and realizability/anti-vacuity witnesses.
- **Swift:** Runtime `precondition(...)` (erased to UB under `-Ounchecked`) plus unchecked `- Precondition:` doc tags confirm that documentation conventions alone do not scale to static memory-safety assurance.

---

### 6. Synthesis: Trade-Off Matrix and Multi-Frontend / Single-Core Architecture

`Basis: derived`

#### 6.1 Power vs. Standardization Comparison Matrix

(`Yes` = native/strong; `Partial` = workaround, subset, or planned; `No` = absent or structurally blocked.)

| Candidate Syntax | Pure Pre/Post | `&mut` / `old!` / Prophecy | Quantifiers (`∀`/`∃`) | Raw-Ptr Provenance | `unsafe trait` Invariants | `modifies` / Framing | Effects (`term` / `no_panic` / `unwind`) | 2-Safety & Concurrency / TLA+ | Stable `rustc` + Zero Runtime Cost | Cross-Tool Portability | Clean MIR Lowering (No 2nd Eval) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`core::contracts` (`#128044`)** | Yes | No (`'static` trap) | No | Partial (`#942` MCP) | No | No | No | No | No (nightly) / Yes (`-Z=no`) | Highest (future std) | Yes (dead-branch lang items) |
| **`verify-rust-std` (`#[safety::*]`)** | Yes | Partial (Kani `old`) | Partial | Yes (`ub_checks::predicates`) | Partial (type `Invariant`) | Partial | Partial (Kani `panics_if`) | No | No (std fork) | High (6 CI tools, SCRC) | Yes (per-tool proc-macro module) |
| **`anodized` (`#[spec]` v0.8)** | Yes | Yes (`captures`; `old!` `#233`) | Yes (`anodized-logic`) | No | No (method specs + type `maintains`) | No | Partial (`pure`/`total`/`infallible`/`terminating`) | No | Yes (fix `#232` inert captures) | Rising (Runtime, Hax, Charon/Aeneas) | Yes (`__anodized_fn_*`; must fix `&`→`&&`) |
| **`contracts` (`x52dev`)** | Yes | Yes (`old()`) | No | No | No | No | No | No | Yes (feature disable) | Runtime-only | No (rewrites body; custom `->`) |
| **Pattern Types + `unsafe_fields`** | No | No | No | No | Partial (`unsafe_fields` marks `LibValid`) | No | No | No | No (nightly) | Official `rustc` | Yes (native MIR `TyKind::Pat`) |
| **Verus (`verus!{}`)** | Yes | Yes | Yes | Yes (`PointsTo`) | Partial | Yes | Yes (`decreases`) | Partial (PCM) | No (custom tool / strip) | Verus-only | No (custom DSL) |
| **Creusot (`pearlite!`)** | Yes | Best (`^x` prophecy) | Yes | No (safe Rust) | Partial | Yes | Partial (`#[variant]`) | No | No (nightly plugin) | Creusot-only | No (custom Pearlite DSL) |
| **Kani (`#[kani::*]`)** | Yes | Partial (bounded) | Partial | Yes (`kani::mem::*`) | Partial (`Invariant`) | Yes | Yes (`panics_if`/`only_if`) | No | Partial (`cfg_attr`) | High (`verify-rust-std`) | Yes (proc-macro adapter) |
| **Flux (`#[flux::sig]`)** | Yes | Yes (`&strg`) | Partial | No | Partial | No | No | No | No (nightly plugin) | Flux-only | No (separate type checker) |
| **RefinedRust (`#[rr::*]`)** | Yes | Yes (Iris) | Yes | Yes (Iris) | Yes | Yes | Partial | Partial | No (custom extractor) | Specialist-only | No (Rocq/Iris strings) |
| **External `Spec.lean`** | Yes | Yes | Yes | Yes | Yes | Yes | Yes (full effect mask) | Yes (full) | Yes (0 Rust edits) | Lean 4 / Aeneas | Yes (native) |

#### 6.2 Recommended Four-Layer Multi-Frontend / Single-Core Architecture

A Rust MIR verifier with an effect-indexed semantic core (`FnContract` over `{returned, unwound, aborted, diverges}`, read-only `SpecEval` reusing `Trusted.MirSemantics`, and stratified `InvariantEnv` for type/`unsafe trait` invariants) should lower four strictly layered frontends into that single core:

1. **Layer 1 — Upstream Standard (`core::contracts` + `verify-rust-std`):** Extract `contract_check_requires` / `build_check_ensures` / `contract_check_ensures` strictly at `-Zcontract-checks=no` + `-Zmir-preserve-ub`; fail closed if any side-effecting pre-closure statement escapes the dead `const false` scaffold (`rust-lang/rust#139548`). Provide a zero-TCB adapter for `verify-rust-std`'s `library/contracts/safety`, `core::ub_checks::{Invariant, predicates::*}`, and Kani contract attributes.
2. **Layer 2 — Stable Cross-Tool Standard (`anodized`):** Ingest `anodized` static companion MIR items (`__anodized_fn_{requires,ensures,qualifiers}_*` or a standardized MIR attribute from `anodized#226`), mapping `FnQualifiers` directly to the effect mask (`INFALLIBLE` → `noUnwind ∧ noAbort`, `TERMINATING` → `terminating`) while keeping `anodized` strictly outside the TCB. Require four safeguards (via upstream collaboration or capture-side enforcement): short-circuiting `&&` clause conjunction (`anodized#240`), host/target-independent embed activation (`anodized#244`), zero-cost inert captures (`anodized#232`), and `old!` / entry-time `mut` parameter semantics (`anodized#233`, `#235`).
3. **Layer 3 — Minimal Systems-Rust Extensions (0 TCB LOC):** Reserve tool-specific proc-macros strictly for capabilities absent from Layers 1 and 2: `#[external_spec(for = path, ...)]` sidecars for unowned crates, `#[unsafe_trait]`/`#[unsafe_impl]` invariant declarations, ghost memory provenance predicates aligned 1-to-1 with `verify-rust-std`'s `ub_checks::predicates`, fine-grained unwind/abort effects (`no_unwind`, `post_unwind`, `unwinds_if`), explicit audited `trusted` waivers, and 2-safety equivalence markers.
4. **Layer 4 — External Declarative Escape Hatch (`Spec.lean`):** Preserve tactic-free external Lean 4 specification modules (checked against silent traps like `autoImplicit` and unguarded `Nat.sub`/`/`/`%`) for unbounded inductive models, relational 2-safety, weak-memory concurrency, and TLA+/protocol refinement, and for verifying third-party crates with zero Rust source modifications.

## Boundaries

- **Not examined dynamically in this pass:** `x52dev/contracts`, `anodized`, `verus`, `creusot`, `kani`, `flux`, `prusti`, `hax`, and `gillian-rust` were inspected via upstream source, proc-macro exports, issue trackers, and crates.io/GitHub metadata, not compiled end-to-end against a shared benchmark crate in this session. Empirical `rustc` MIR/LLVM/Miri execution results for `core::contracts` and `TyKind::Pat` are drawn from sibling reports observed on `2026-11-22`.
- **Unknown / moving targets:**
  - Exact stabilization timeline and final syntax of `rust-lang/rust#128044` (including `for safety:`/`for correctness:` contract forms, `old(...)`, `'static` relaxation on `build_check_ensures`, and `compiler-team#942`'s `owned`/`alloc_block` primitives).
  - Whether `anodized-rs/anodized` will resolve `#226` (MIR lowering), `#232` (zero-cost inert captures), `#233` (`old!`), `#235` (`mut` inputs), `#240` (`&&` short-circuiting), and `#244` (`ANODIZED_MODE`) before `v1.0`, and whether maintainer bus factor expands beyond `mkovaxx`.
- **Known not to apply:**
  - Crates.io `deal` (`v0.1.0`) is a card-deck library, not a Rust DbC framework.
  - Capturing `core::contracts` with `-Zcontract-checks=yes` is known to be unsound for production MIR verification due to injected `&_1` borrows and UB-masking `panic_nounwind` checks.
  - Comment-based formal specification languages (ACSL/JML/Anneal v1 `/// ```anneal`) are known not to receive `rustc` typechecking or IDE refactoring support.

## Evidence

All primary observations below were acquired on `2026-11-22`:

1. **`rust-lang/rust` (`ce66487ebbd7541212d22d01c39a808057d69f1f`):**
   - Tracking issues & PRs queried via GitHub API: `rust-lang/rust#128044`, `#128045` (merged `2025-02-05`), `#128274`, `#137134`, `#139548`, `#123646`, `#132922`, `#130516`; `rust-lang/compiler-team#759`, `#813`, `#942`.
   - `library/core/src/contracts.rs:19-24` (`build_check_ensures<Ret, C: Fn(&Ret) -> bool + Copy + 'static>`).
   - Sibling corpus execution probes: `reports/rustc-native-contracts-requires-ensures-runtime-checks-and-ctfe-soundness/REPORT.md` and `reports/rustc-pattern-types-niche-stacking-llvm-range-and-miri-validity-soundness/REPORT.md` (both observed `2026-11-22`).
2. **`model-checking/verify-rust-std` (`1feeadd937956b8067ec2fb147ef55469361dab4`):**
   - `library/contracts/safety/src/{lib.rs,kani.rs,runtime.rs}`, `library/core/src/ub_checks.rs:194-275` (`predicates::{can_dereference, can_read_unaligned, can_write, can_write_unaligned, same_allocation, float_to_int_in_range}` and `pub trait Invariant`), `doc/src/{tools.md,general-rules.md}`, and issues `#44`, `#693`, `#712`, `#734`, `#783`.
3. **`anodized-rs/anodized` (`8fb862e952ab893643095a3365734af20b48e3bb`, crates.io `v0.8.0`):**
   - `README.md`, `crates/anodized/REFERENCE.md`, `crates/anodized-core/src/syntax/spec_attrib.rs`, `crates/anodized-core/src/qualifiers.rs`, `crates/anodized-core/src/instrument/{fns.rs,hax.rs}`, `crates/anodized-logic/src/{lib.rs,quantifiers.rs,values.rs,operators.rs,arithmetic.rs}`.
   - Open/closed issues `#132`, `#169`, `#174`–`#177`, `#211`, `#226`, `#232`, `#233`, `#235`, `#240`, `#244`, `#247`; contributor stats (`mkovaxx`: 125 commits) and crates.io API (`version: 0.8.0`, `downloads: 8917`, `recent_downloads: 5123`).
4. **Community DbC crates & FV verifiers:**
   - Crates.io API telemetry queried `2026-11-22` for `anodized`, `contracts`, `pre`, `deal`, `dbc`, `mirai-annotations`, `static_assertions`, `adhesion`, `hoare`, `hax-lib`.
   - Upstream proc-macro exports inspected at pinned SHAs: `x52dev/contracts` (`README.md`), `aticu/pre` (`README.md`), `model-checking/kani` (`library/kani_macros/src/lib.rs`), `creusot-rs/creusot` (`creusot-std-proc/src/lib.rs`), `flux-rs/flux` (`lib/flux-attrs/src/lib.rs`), `prusti/prusti` (`prusti-contracts/prusti-contracts-proc-macros/src/lib.rs`), `pereq-dev/hax` (`hax-lib/macros/src/lib.rs`), and `facebookexperimental/MIRAI` (`annotations/src/lib.rs`), plus sibling corpus reports `verus-vstd-views-permissions-prophecies-and-os-verification`, `creusot-std-prophetic-resolve-perm-containers-and-iterator-laws`, `flux-indexed-refinements-strong-borrows-and-qualifier-templates`, `refinedrust-lithium-place-types-and-laid-out-spatial-nodes`, and `ott-verso-antiquotations-spark-openjml-contracts-and-jdoctor-comment-drift`.
5. **Historical Anneal evolution:**
   - `google/zerocopy` tag `anneal-v0.1.0-alpha.23` (`a3ad195abf85896be6f07f11acb486ceb7d61900`, `anneal/README.md`, `anneal/docs/agent/04_specifications_and_syntax.md`), `google/zerocopy` `main` (`a007a51af473e5901915b003083e61c7c89c7bd1`, `anneal/docs/design.md`, `anneal/THREAT_MODEL.md`), and public issues `google/zerocopy#2777`, `#3031`, `#3062`, `#3086`, `#3091`, `#3203`, `#3380`, `#3697`, `#4102`.

## Revalidation

To cheaply detect whether any material finding has changed:

1. **`core::contracts` (`rust-lang/rust#128044`):** Inspect `library/core/src/contracts.rs` for relaxation of `+ Copy + 'static` on `build_check_ensures`, check status of `rust-lang/rust#139548` (side-effecting `#[ensures]`), and rerun `rustc +nightly -Zunpretty=mir` on a function with `#[core::contracts::requires]` / `#[ensures]` at `-Zcontract-checks=no` to confirm dead-branch lang-item preservation.
2. **`anodized` (`anodized-rs/anodized`):** Check resolution status of issues `#226` (MIR lowering), `#232` (zero-cost inert captures), `#233` (`old!`), `#235` (`mut` input semantics), `#240` (`&&` short-circuiting), and `#244` (`ANODIZED_MODE`), and diff `crates/anodized-core/src/instrument/fns.rs` around `build_precond_check` (`&` vs. `&&`).
3. **`verify-rust-std` (`model-checking/verify-rust-std`):** Diff `library/contracts/safety/src/lib.rs`, `library/core/src/ub_checks.rs`, and `doc/src/tools.md` to check for new contract forms (`#44`), new `ub_checks::predicates`, or newly approved verification tools.
4. **Ecosystem adoption:** Re-query crates.io `/api/v1/crates/{anodized,contracts,hax-lib}` and `gh repo view` on the listed repositories to detect major version bumps or maintainer changes.
