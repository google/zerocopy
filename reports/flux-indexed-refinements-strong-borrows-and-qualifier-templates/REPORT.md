# Flux Indexed Refinements, Strong Mutable Borrows, and Qualifier Templates as Untrusted Certificate Generators for 3-Axiom Lean 4 MIR Verification

## Summary

Flux (`flux-rs/flux`, formerly `liquid-rust/flux`, inspected at `7d9886b36347e9e245fa8b354da7fb9662a2087c`) embeds Liquid Types (`10.1145/1375581.1375602`, `10.1145/3591283`) into a `rustc_driver` plugin over Rust MIR. Rather than requiring manual loop invariants or interactive tactic scripts, Flux achieves low-annotation ergonomics through three front-end mechanisms while exhibiting sharp Trusted Computing Base (TCB) and arithmetic boundaries:

1. **Indexed vs. existential refinements and `detached_spec!` (`crates/flux-middle/src/rty/mod.rs`, `crates/flux-driver/src/collector/detached_specs.rs`):** Flux separates singleton *indexed types* `BaseTy[r]` (`TyKind::Indexed`, binding a runtime value to an exact logical index `r` across calls and mutations) from *existential subset types* `{v: BaseTy | p(v)}` (`TyKind::Exists(Binder<TyKind::Constr>)`), extended with trait-level `AssocReft` predicates (`10.1145/3704885`) and out-of-line `detached_spec!` blocks (`lib/flux-rs/src/lib.rs:18–36`). Critically, under Flux's default `OverflowMode::None` (`rty/mod.rs:3121–3232`), unsigned integers assume only `0 <= nu` (omitting `nu <= uN::MAX`) and signed integers inject *zero* bounds (`[]`), modeling unbounded `Sort::Int` unless `OverflowMode::Strict` or `Sort::BitVec` is enabled.
2. **Strong mutable references (`&strg`) and `PlacesTree` updates (`crates/flux-refineck/src/type_env/place_ty.rs`, `ghost_statements.rs`):** Flux splits invariant references (`BaseTy::Ref`) from flow-sensitive *strong references* `&strg<loc: T1>` (`TyKind::StrgRef` / `TyKind::Ptr(PtrKind::Mut, path)`) paired with post-call location updates `Ensures::Type(path, T2)`. In `rty::auto_strong` (`rty/mod.rs:3415–3513`), unannotated `&mut T` parameters upgrade automatically to `&strg` **except** when the return type mentions lifetime regions (`!can_auto_strong`, excluding reborrowing accessors such as `IndexMut::index_mut`), on closures, or on unsized slices (`!inner_ty.is_slice()`). Compiler-inserted `GhostStatement::{Unfold, Fold, Unblock, PtrToRef}` statements unpack structs, block borrowed places as `TyKind::Blocked(Ty)`, unblock them on borrow expiration, and re-check `#[invariant(...)]` on `Fold`. Raw pointers `*mut[base, addr, size] T` (`lib/flux-core/src/ptr/mod.rs`) check spatial bounds and alignment (`10.1145/3731569.3764856`) but set `is_strg = false` (`place_ty.rs:185–188`), omitting temporal safety and pointee value tracking.
3. **Qualifier templates, `$k` solution decoding, and native Lean exporter limits (`crates/flux-infer/`, `lib/liquid-fixpoint/`):** Loop and join invariants become Horn predicate variables `$k(v0, ...)` solved over 13 built-in `FIXPOINT_QUALIFIERS` (`fixpoint_qualifiers.rs:9–152`) plus user `qualifier!(...)` templates, with `FixpointCtxt::fixpoint_to_solution` (`decoding.rs:18–40`) decoding closed `rty::Binder<rty::Expr>` invariants from `VerificationResult.solution`. Conversely, Flux's native Lean 4 exporter (`lean_encoding.rs`, Flex `arXiv:2607.12226`) leaves ~450 KB of `flux-refineck` inside the TCB, emits `axiom PrimOp...` (`line 942`), `noncomputable def`, and `deriving Inhabited`, and audits proofs solely by scanning `lake build` stdout for `"sorryAx"` (`lines 330–351`).

For Anneal (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), inverting that boundary removes Flux and SMT solvers from the TCB entirely: Flux (`OverflowMode::Strict`) and `liquid-fixpoint` act as an **untrusted front-end and candidate invariant oracle**, feeding two proposed zero-TCB, Pass-1-compliant 3-axiom Lean 4 `theory/` certificate checkers defined in Section 5.2—`AiPcc` (`InitDom × Tnum × WrappedInterval × StridedCong`) and `OmegaCutCert` (sparse integer Farkas combinations + Chvátal–Gomory floor cuts)—whose soundness theorems discharge `Trusted.MirSemantics` obligations via kernel `rfl` reduction.

## Applicability

This report examines `flux-rs/flux` at commit `7d9886b36347e9e245fa8b354da7fb9662a2087c` (to which `liquid-rust/flux` redirects) and evaluates its integration as an untrusted specification front-end and certificate oracle targeting `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`. Five publications anchor the analysis: Liquid Types (`10.1145/1375581.1375602`, PLDI 2008), Flux (`10.1145/3591283`, `arXiv:2207.04034`, PLDI 2023), Generic Refinement Types (`10.1145/3704885`, POPL 2025), TickTock (`10.1145/3731569.3764856`, SOSP 2025), and Flex (`arXiv:2607.12226`, July 2026).

Configuration and toolchain boundaries apply to both systems:
- In `flux-rs/flux` (`7d9886b36347e9e245fa8b354da7fb9662a2087c`), integer width invariants depend on `OverflowMode` (`crates/flux-middle/src/rty/mod.rs:3075–3232`); any certificate pipeline targeting machine MIR **must** run Flux under `OverflowMode::Strict` (or `Sort::BitVec`) rather than default `OverflowMode::None`. Horn solving runs via either external Haskell `fixpoint` (Z3/CVC5) or in-tree `feature = "rust-fixpoint"` (`lib/liquid-fixpoint/src/lib.rs:20–26`); external Lean VC emission (`#[flux::proven_externally]`, `lean = "check" | "emit"`, `crates/flux-refineck/src/lib.rs:98–103`) targets `leanprover/lean4:v4.28.0` (`lean_encoding.rs:729`).
- In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), Pass 1 (`trusted/audit/TrustedBoundary.lean:439–610`, `trusted/lean/foundation-lock.json` on `leanprover/lean4:v4.34.1`) restricts `theory/` to `prelude` + 51 `Init.*` modules, pure syntax (noting that `allowedNotationSyntaxKinds` at `lines 521–527` excludes unary `-` and infix `/`), 22 structural tactics, zero `._unsafe_rec` helpers, three standard axioms (`propext`, `Quot.sound`, `Classical.choice`), and Statement-Origin Separation. `AiPcc` and `OmegaCutCert` in Section 5 are proposed Pass-1 `theory/` checker designs evaluated against existing `Trusted.MirSemantics` and `Anneal.PureLift.*` modules.

General refinement-type surveys appear in `anneal-deductive-logics-types-and-abstract-interp-survey`, and rational Farkas bounds-check certificates appear in `multi-premise-sparse-farkas-and-freeze-set-refinement-certificates` and `type-validity-seeded-range-and-farkas-bounds-check-elimination`; this report focuses on Flux's internal IRs, `&strg` `PlacesTree` typing, qualifier/CHC decoding, `lean_encoding.rs` audit, and integer-complete (`divCut` + `Tnum`) MIR certificates.

## Findings

### 1. Indexed vs. Existential Refinements, Overflow Modes, and Detached Specifications

`Basis: source + normative`

Flux lowers annotations across three IRs (`book/src/guide/architecture.md:25–48`): `surface` (`crates/flux-syntax/src/surface.rs`) $\to$ `fhir` (`crates/flux-middle/src/fhir.rs`) $\to$ De Bruijn–indexed `rty` (`crates/flux-middle/src/rty/mod.rs`).

#### 1.1 Stratification of `TyKind::Indexed`, `TyKind::Exists`, `AssocReft`, and `detached_spec!`
In `crates/flux-middle/src/rty/mod.rs:1934–1960`, value refinements split into distinct constructors:
- **`TyKind::Indexed(BaseTy, Expr)` (`T[e]`):** Binds `BaseTy` to a deterministic logical index `e` of sort `BaseTy::sort()`: `Sort::Int` for `i8..i128`/`u8..u128`/`isize`/`usize` and `[T]`/`Vec<T>` lengths; `Sort::Bool` for `bool`; `Sort::RawPtr` `(base, addr, size)` for `*const T`/`*mut T`; `AdtSortDef` field tuples for `#[refined_by(f1: s1, ...)]` structs (`rty/mod.rs:76–152`); or inductive sorts for `#[reflected]` enums (`lines 148–150`). Passing `usize[i]` and `&Vec<T>[n]` directly relates `i` and `n` across call boundaries (`fn index(&Vec<T>[@len], {I[@idx] | in_bounds(idx, len)})`, `lib/flux-alloc/src/vec/mod.rs:52`) without skolemizing nested existentials.
- **`TyKind::Constr(Expr, Ty)` and `TyKind::Exists(Binder<Ty>)` (`{v: T[ν] | p(ν)}`):** `Ty::exists_with_constr(bty, pred)` (`rty/mod.rs:1682–1686`) wraps `Ty::constr(pred, Ty::indexed(bty, Expr::nu()))` in `Binder`, while unannotated Rust types lift via `BaseTy::to_ty()` (`lines 2144–2154`) to `∃ ν. BaseTy[ν]`. Accessing a place via `PlacesTree::lookup_unfolding` (`place_ty.rs:97–99`) unpacks outer existentials into fresh context variables; CFG joins (`Goto(bb)`) repack values into `Exists` guarded by Horn variables `$k(...)`.
- **`AssocReft` (`10.1145/3704885`, `rty/mod.rs:773–820`) and `detached_spec!` (`lib/flux-rs/src/lib.rs:18–36`, `crates/flux-driver/src/collector/detached_specs.rs:54–426`):** Traits declare abstract predicate hooks (`#[assoc(fn in_bounds(idx: Self, len: int) -> bool)]`) projected via `ExprKind::Alias(AliasReft, args)`. Out-of-line `detached_spec! { ... }` expands to `#[flux_rs::specs { ... }] const _: () = ();`, matched by `DetachedSpecsCollector` against `tcx.module_children_local` and `tcx.all_local_trait_impls` to attach contracts to `FnSig`, `Struct`, `Enum`, `Trait`, and `Impl` `OwnerId`s with zero edits to audited Rust function bodies.

#### 1.2 The Default `OverflowMode::None` Divergence Against Machine MIR
Inspection of `crates/flux-middle/src/rty/mod.rs:3075–3232` exposes a critical gap between Flux's default arithmetic model and Rust MIR:
- `uint_invariants(uint_ty, overflow_mode)` (`lines 3121–3153`) under default `OverflowMode::None` injects **only** `DEFAULT = [ν >= 0]`, omitting `ν <= uint_max(uint_ty)`.
- `int_invariants(int_ty, overflow_mode)` (`lines 3199–3232`) under `OverflowMode::None` injects **`DEFAULT = []`**—neither `ν >= int_min(int_ty)` nor `ν <= int_max(int_ty)`.
- `slice_invariants` (`lines 3075–3119`) injects `T::size_of() * len <= isize::MAX` and `len <= usize::MAX` **only** under `Strict`, `Lazy`, or `StrictUnder`.

Under `OverflowMode::None`, Flux accepts `x + 1 > x` on `x: u32` or `x: i32` even when Rust MIR wraps modulo $2^{32}$ in release builds. Targeting `Trusted.MirSemantics` therefore requires running Flux under `OverflowMode::Strict` (for checked arithmetic / `Assert` obligations) or `Sort::BitVec(BvSize::Fixed(w))` (`lib/flux-rs/src/bitvec.rs`) for wrapping bitvectors.

---

### 2. Strong Mutable References, `PlacesTree` Unfold/Fold/Unblock, and Spatial Raw Pointers

`Basis: source + normative`

#### 2.1 `&mut T` vs. `&strg T`, `PlacesTree`, and the Three `auto_strong` Exclusions
Flux (`10.1145/3591283`) exploits `&mut` exclusivity by splitting mutable references into two modes (`rty/mod.rs:1939–1966`, `place_ty.rs:26–248`):
1. **Weak (invariant) `&mut T` (`BaseTy::Ref(re, ty, Mutability::Mut)`):** Dereferencing sets `is_strg = false` (`place_ty.rs:193–195`); writes must immediately re-establish the identical type `ty` and cannot change refinement indices (`Vec<T>[n]` $\to$ `Vec<T>[n + 1]`).
2. **Strong `&strg<ℓ: T₁>` with `ensures ℓ: T₂` (`TyKind::StrgRef` and `TyKind::Ptr(PtrKind::Mut(re), path)`):** `PlacesTree` maps abstract locations `Loc` (`Local`, `Box`, `LocalPtr`, `Universal`) to refined `Binding`s. Borrowing `r = &mut p` gives `r` singleton pointer type `Ptr(Mut(re), path_p)` (`is_strg = true`, `lines 189–191`), routing reads/writes through `path_p` for flow-sensitive strong updates. Coercing `r` to weak `&mut T` inserts `GhostStatement::PtrToRef(r)` (`ghost_statements.rs:67, 131–133`), marking `path_p` as **`TyKind::Blocked(T)`** (`rty/mod.rs:1722`) until `rustc_borrowck` expires the borrow and `GhostStatement::Unblock(p)` (`lines 126–145`) restores `T` with fresh existential indices. `GhostStatement::Unfold(p)` and `Fold(p)` (`lines 64–65`, `lib.rs:250–254`) lazily split ADTs into field bindings and re-verify `#[invariant(...)]` on `Fold`.

Surface signatures elide `&strg` via `#[spec(fn(self: &mut Vec<T>[@n], T) ensures self: Vec<T>[n + 1])]` (`vec/mod.rs:25`) and `rty::auto_strong` (`rty/mod.rs:3452–3513`), which upgrades unannotated `fn(x: &mut InnerTy) -> Out` to `forall<l0: Loc>. fn(x: &strg<l0: InnerTy>) -> Out ensures l0: InnerTy`. However, `rty/mod.rs:3415–3479` enforces **three hard exclusions**:
- **Region-returning functions (`!can_auto_strong`, `lines 3415–3435, 3460`):** Whenever `output.ret` mentions any region (e.g., `IndexMut::index_mut(&'a mut Vec<T>, usize) -> &'a mut T` at `vec/mod.rs:59–60` or `split_first_mut`), `&strg` cannot apply because `ensures ℓ: T₂` restores full ownership of `ℓ` at `return`, whereas reborrowing accessors return a live sub-borrow `&'a mut U` keeping `ℓ` frozen in the caller.
- **Closures (`DefKind::Closure`, `line 3461`)** and **Unsized slices (`!inner_ty.is_slice()`, `lines 3477–3478`):** Both are skipped (`!inner_ty.is_slice()` notes a `TODO(auto-strong)` regression on Tock OS).

#### 2.2 Spatial-Only Raw Pointers (`*const[base, addr, size] T`)
`lib/flux-core/src/ptr/mod.rs:1–260` and `rty/mod.rs:3155–3174` index raw pointers by `Sort::RawPtr` `(base: int, addr: int, size: int)` (`size` = remaining bytes to allocation end, `base >= 0`, `0 <= addr <= usize::MAX`, `addr + size <= usize::MAX`), verifying `ptr::add` shifts (`[base, addr + count * sizeof(T), size - count * sizeof(T)]` under `count * sizeof(T) <= size`, `ptr/mod.rs:84–89`), alignment (`addr % align == 0`, `line 29`), and Tock OS MMIO/MPU isolation (`10.1145/3731569.3764856`). However, `ptr/mod.rs:72–75` and `place_ty.rs:185–188` (`is_strg = false`) enforce that raw pointers prove neither temporal liveness nor strong pointee value updates (`ptr::read` returns unindexed `T`, `lines 156–159`).

---

### 3. Qualifier Templates, Predicate Abstraction, and `$k` Solution Decoding

`Basis: source + normative`

`check_body` (`crates/flux-refineck/src/lib.rs:64–117`) executes three sequential passes: Pass S1 (`run_in_shape_mode`) computes fixed-point `PlacesTree` shapes at loop headers and joins; Pass S2 (`run_in_refine_mode`) emits a nested tree `Constraint` (`ForAll | Conj | Pred`, `lib/liquid-fixpoint/src/constraint.rs`) over Horn predicate variables `$k_i(v_0, \dots, v_{m-1})`; Pass S3 discharges all `$k_i` via predicate abstraction (`10.1145/1375581.1375602`).

1. **13 Built-In `FIXPOINT_QUALIFIERS` and User `qualifier!` Templates (`crates/flux-infer/src/fixpoint_qualifiers.rs:9–152`, `lib/flux-rs/src/lib.rs:54–78`):** Flux seeds every task with 7 unary templates (`EqTrue: b`, `EqFalse: ¬b`, `EqZero: v = 0`, `GtZero: v > 0`, `GeZero: v ≥ 0`, `LtZero: v < 0`, `LeZero: v ≤ 0`) and 6 binary templates (`Eq: v₀ = v₁`, `Gt: v₀ > v₁`, `Ge: v₀ ≥ v₁`, `Lt: v₀ < v₁`, `Le: v₀ ≤ v₁`, `Le1: v₀ ≤ v₁ - 1`), plus constants scraped from signatures (`scrape_quals = true`, `lib/liquid-fixpoint/src/lib.rs:222`). Multi-variable loop relations ($\ge 3$ terms, e.g., `res + i == n` or `off == 8 * i`) lie outside unary/binary templates and are supplied locally via `flux_rs::macros::qualifier!(res: int, i: int ; res + i == n)` without writing loop invariants.
2. **Tarjan SCC Elimination and Closed `$k` Decoding (`lib/liquid-fixpoint/src/constraint_solving.rs:59–260`, `decoding.rs:18–40`):** The in-tree solver computes Tarjan SCCs (`topological_sort_sccs`, `line 101`), eliminates acyclic `$k` variables via `Constraint::elim` (`lines 233–260`), and solves cyclic loop `$k` variables iteratively by pruning falsified qualifier instantiations. Crucially, `VerificationResult.solution: Vec<KVarBind>` (`lib/liquid-fixpoint/src/lib.rs:278–280`) is decoded by `FixpointCtxt::fixpoint_to_solution` (`crates/flux-infer/src/fixpoint_encoding/decoding.rs:18–40`) directly into `$k`-free expressions `rty::Binder<rty::Expr>`.

---

### 4. Audit of Flux's Native Lean 4 Exporter (`lean_encoding.rs`) and Flex (`arXiv:2607.12226`)

`Basis: source + documentation`

For obligations beyond SMT decidability, Flux (`crates/flux-infer/src/{lean_encoding,lean_format}.rs`) and **Flex** (`arXiv:2607.12226`) export `LeanKConstraint` tasks (`∀ consts, ∃ k0 ... kn, constr`, `lean_format.rs:690–720`) to a `lake +v4.28.0` project, where Flex's `MetaM` tactics `Zap` and `Fix` synthesize acyclic and cyclic `$k_i` witnesses inside Lean. Direct inspection at `7d9886b36347e9e245fa8b354da7fb9662a2087c` identifies **five concrete reasons** why this exporter cannot satisfy Anneal's TCB and Pass 1 audit (`trusted/audit/TrustedBoundary.lean:442–596`):

1. **Unverified ~450 KB Rust-to-CHC Frontend Inside the TCB:** `LeanKConstraint` certifies only the post-VCgen output of `flux-desugar`, `flux-fhir-analysis`, `PlacesTree`, and `OverflowMode` lowering—not `rustc` MIR execution.
2. **Bypassable Stdout Text-Scraping Audit (`lean_encoding.rs:256–291, 330–351`):** `generate_checking_file` emits `#print axioms F.foo_proof`, and `ProofReport::status` (`lines 330–351`) checks *only* that `lake build` stdout contains `"axioms"` without `"sorryAx"`. It performs no `trustLevel := 0` `.olean` replay (`TrustedBoundary.lean:425–428`), accepts user `axiom bad : False`, `native_decide` (`Lean.ofReduceBool`), and `@[implemented_by]`, and is spoofable via `#eval IO.println`.
3. **Generated `axiom` Declarations (`lean_encoding.rs:753, 942`):** `generate_opaque_const_file` emits raw `axiom PrimOp...` declarations (`line 942`) and `sorry` stubs (`line 753`).
4. **Disallowed Syntax & Incomplete ADT Lowering (`lean_format.rs:197, 561–589`):** Emitted files use `set_option` (`lean_encoding.rs:633`), `deriving Inhabited` (`line 197`), and `noncomputable def` (`line 589`), while `Expr::IsCtor` and `Expr::WKVar` panic with `todo!("not yet implemented: datatypes in lean")` (`lines 561–581`).
5. **`MetaM` `Zap`/`Fix` Tactics Excluded from `theory/`:** `allowedTheoryTacticKinds` (`TrustedBoundary.lean:536–557`) forbids custom `macro`/`elab`/`run_tac` tactics, requiring external solving to emit pure data certificates checked by total `Bool` functions.

---

### 5. Untrusted Oracle & Certificate Architecture Feeding 3-Axiom Lean 4 Checkers

`Basis: source + derived`

#### 5.1 Zero-TCB Pipeline Over `Trusted.MirSemantics`
Inverting the trust boundary keeps `flux-driver`, `liquid-fixpoint`, Z3/CVC5, and witness extraction completely **outside** Anneal's TCB while preserving Flux's zero-loop-annotation UX:
- **Trusted Boundary (`rustc-capture` + Spec Surface):** Captures PostCleanup `Mir.program` (`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`) and translates human-audited public entry/exit refinements (`T[r]`, `detached_spec!`, under `OverflowMode::Strict`) into `Init.*` + `Trusted.*` propositions obeying Statement-Origin Separation.
- **Untrusted Oracle (`flux-refineck` + `liquid-fixpoint` + Dual Extractor):** Infers loop/join `$k_i` solutions via `fixpoint_to_solution` (`decoding.rs:18–40`) and emits pure Lean data certificates `(aiFixMap, cutProofs)`.
- **Zero-TCB `theory/` Checkers (`AiPcc` + `OmegaCutCert`):** Proposed Pass-1 checkers defined below verify (1) a 1-pass CFG abstract post-fixpoint (`AiPcc`: `InitDom × Tnum × WrappedInterval × StridedCong`) for initialization, bitwise masks, modular intervals, and alignment, and (2) sparse integer Farkas + Chvátal–Gomory floor-cut refutations (`OmegaCutCert`) for relational qualifier edges (`Le1`, `res + i == n`, `count * sz <= p.size`), discharging `Trusted.MirSemantics.BodyVerified` by kernel `rfl`.

#### 5.2 Self-Contained Pass-1 Lean 4 Checkers (`AiPcc` and `OmegaCutCert`)
The definitions below obey every Pass 1 rule in `TrustedBoundary.lean:442–596`: `prelude`, imports strictly within the 51-module `foundation-lock.json` graph, `List.foldr` recursion with zero `._unsafe_rec` helpers, `0 - Int.ofNat` and `Nat.div` in place of unary `-` and infix `/` (both absent from `allowedNotationSyntaxKinds` at `lines 521–527`), and a `Nat.ble widthBits 128` shift guard keeping `rfl` on Lean `v4.34.1`'s C++ GMP `reduce_nat` fast path:

```lean
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.FluxCertBridge

/-! ### 1. `AiPcc`: Reduced Product (`InitDom × Tnum × WrappedInterval × StridedCong`) -/

inductive InitDom where
  | bot | uninit | init | top

structure Tnum where
  val  : Nat
  mask : Nat

structure WrappedInterval where
  isEmpty : Bool
  isFull  : Bool
  lo      : Nat
  hi      : Nat

/-- Strided congruence `x % stride = rem % stride` (`stride = 0` => singleton `rem`),
    certifying Flux `aligned_to(p, align)` (`addr % align == 0`) and `offset_from`. -/
structure StridedCong where
  stride : Nat
  rem    : Nat

structure MirAbsVal where
  init : InitDom
  tnum : Tnum
  wrap : WrappedInterval
  cong : StridedCong

def reduceProduct (widthBits : Nat) (v : MirAbsVal) : MirAbsVal :=
  let maskCap := if Nat.ble widthBits 128 then Nat.shiftLeft 1 widthBits - 1 else 0
  let tVal := Nat.land v.tnum.val maskCap
  let tMsk := Nat.land v.tnum.mask (Nat.xor maskCap tVal)
  let tMax := tVal + tMsk
  let newLo := if v.wrap.isFull || Nat.blt v.wrap.lo tVal then tVal else v.wrap.lo
  let newHi := if v.wrap.isFull || Nat.blt tMax v.wrap.hi then tMax else v.wrap.hi
  { v with tnum := ⟨tVal, tMsk⟩, wrap := ⟨v.wrap.isEmpty, false, newLo, newHi⟩ }

/-! ### 2. `OmegaCutCert`: Sparse Integer Farkas + Chvátal–Gomory Cut Checker -/

structure SInt where
  neg : Bool
  mag : Nat

def SInt.toInt (x : SInt) : Int :=
  if x.neg then 0 - Int.ofNat x.mag else Int.ofNat x.mag

def SInt.add (a b : SInt) : SInt :=
  if a.neg == b.neg then
    ⟨a.neg, a.mag + b.mag⟩
  else if Nat.ble b.mag a.mag then
    ⟨if a.mag - b.mag == 0 then false else a.neg, a.mag - b.mag⟩
  else
    ⟨b.neg, b.mag - a.mag⟩

def SInt.mulNat (k : Nat) (a : SInt) : SInt :=
  if k == 0 || a.mag == 0 then ⟨false, 0⟩ else ⟨a.neg, k * a.mag⟩

structure LinIneq where
  terms : List (Nat × SInt)
  rhs   : SInt

def evalTerms (env : Nat → Int) (ts : List (Nat × SInt)) : Int :=
  ts.foldr (fun vc acc => vc.2.toInt * env vc.1 + acc) 0

def LinIneq.denote (env : Nat → Int) (ineq : LinIneq) : Prop :=
  evalTerms env ineq.terms ≤ ineq.rhs.toInt

/-- Exact integer floor `⌊rhs / d⌋` (`d > 0`) using `Nat.div` (Pass-1 notation-safe):
    for `-m` with `m > 0`, `⌊-m / d⌋ = - ((m + d - 1) / d)`. -/
def floorDivSInt (rhs : SInt) (d : Nat) : SInt :=
  if !rhs.neg || rhs.mag == 0 then
    ⟨false, Nat.div rhs.mag d⟩
  else
    ⟨true, Nat.div (rhs.mag + d - 1) d⟩

inductive CutStep where
  | hyp    (idx : Nat)
  | comb   (s1 k1 s2 k2 : Nat)
  | divCut (d s : Nat)

def nthOpt {α : Type} (xs : List α) (n : Nat) : Option α :=
  xs.foldr
    (fun x ih k => match k with | 0 => some x | k' + 1 => ih k')
    (fun _ => none)
    n

def divTermsOpt (d : Nat) (ts : List (Nat × SInt)) : Option (List (Nat × SInt)) :=
  if d == 0 then none
  else ts.foldr (fun vc acc =>
    match acc with
    | none => none
    | some rest =>
      if Nat.mod vc.2.mag d == 0 then
        some ((vc.1, ⟨vc.2.neg && (Nat.div vc.2.mag d != 0), Nat.div vc.2.mag d⟩) :: rest)
      else none) (some [])

def isContradiction (ineq : LinIneq) : Bool :=
  ineq.terms.foldr (fun vc ok => vc.2.mag == 0 && ok) true &&
  ineq.rhs.neg && (ineq.rhs.mag != 0)

end Anneal.FluxCertBridge
```

#### 5.3 Construct-by-Construct Lowering Into `PureLift` + `AiPcc` + `OmegaCutCert`
1. **Qualifiers $\to$ `OmegaCutCert` (`LinIneq`):** All 13 `FIXPOINT_QUALIFIERS` (`fixpoint_qualifiers.rs:9–152`) and affine `qualifier!` templates lower to `LinIneq` clauses (`x < y` on `Int` is Flux's `Le1: x - y ≤ -1`). Decoded `$k` solutions give inductive block cutpoints $I_{\text{bb}}$, and LP/MIP dual extraction emits compact `CutStep` refutations of $I_{\text{src}} \wedge \mathsf{Guard}_{\text{edge}} \wedge \neg I_{\text{dst}}[e/x]$ checked by `rfl`.
2. **Alignment & Strides (`ptr/mod.rs:29, 138`) $\to$ `StridedCong` + `divCut`:** Rational Farkas cannot refute integer parity/stride gaps such as `2 * i - 2 * n ≤ -1 ⊢ i - n ≤ -1` (admitting $i = 0.5, n = 1$). `CutStep.divCut 2` verifies `divTermsOpt 2` and tightens `floorDivSInt ⟨true, 1⟩ 2 = ⟨true, 1⟩` (`⌊-1/2⌋ = -1`) in a single step, while power-of-two mask checks (`addr & (align - 1) == 0`) discharge in `AiPcc`'s `Tnum × StridedCong` product.
3. **Strong Borrows `&strg` + Reborrows $\to$ `Anneal.PureLift.LoanGraph`:** Where `rty::auto_strong` fails on region-returning functions (`!can_auto_strong`, `rty/mod.rs:3415–3435`) and slices (`line 3477`), `Anneal.PureLift` (`LoanGraph.lean:53–97`) handles both call-scoped strong updates (`.direct` writebacks) and lifetime-returning reborrows (`.lensCall` / `.regionOut`) uniformly.

#### 5.4 Evaluation Against Anneal's Seven-Dimension `theory/` Rubric

| Dimension | Evaluation of Flux Front-End + `AiPcc` / `OmegaCutCert` Certificate Pipeline |
| :--- | :--- |
| **(T1) Zero-TCB Bridge & `Trusted.*` Gaps** | **0-TCB for inference and solving:** `flux-driver` (~450 KB), `liquid-fixpoint`, Z3/CVC5, and dual witness generation sit outside the TCB. Public `T[r]`/`detached_spec!` contracts translate to `Init.*` + `Trusted.*` Props (preserving Statement-Origin Separation), and `AiPcc`/`OmegaCutCert` compile inside Pass-1 `theory/`. Scalar/tuple/enum checks work on `Trusted.MirSemantics` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`; spatial pointer/slice checks require `Trusted.*` `CallerMemory` and `Allocation`/`Offset` additions. |
| **(P1) Human Specification Auditability** | **High for numeric, bounds, and state-machine APIs:** `T[r]` indices and out-of-line `detached_spec!` keep contracts quantifier-free and separated from implementation code. **Mandatory guardrail:** Reject `OverflowMode::None` so `u32[n]` unconditionally carries `0 ≤ n ≤ 2^32 - 1`. |
| **(P2) Authoring & Day-2 Edit Locality** | **Eliminates manual loop-invariant churn:** Local MIR edits inside loops trigger automatic `$k` re-inference over `FIXPOINT_QUALIFIERS` $\cup$ `qualifier!` and certificate regeneration without hand-editing Lean loop invariants. |
| **(P3) Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP Scaling** | **Sub-5ms kernel `rfl` checking:** Reifying variables as `Nat` IDs and coefficients as `SInt` (`Bool × Nat`) keeps symbolic `env : Nat → Int` out of reduced terms so Lean's C++ kernel stays on GMP `reduce_nat`, while `Nat.ble widthBits 128` blocks shift-allocation DoS. |
| **(P4) Heterogeneous Composability** | **Two-pass Modus Ponens with `PureLift` + `SpatialPin`:** `AiPcc` + `OmegaCutCert` discharge overflow, division-by-zero, bounds, and spatial `RawPtr` side conditions (`valid`, `aligned_to`), while `PureLift` + `SpatialPin` supply temporal ownership and value tracking across `&mut`, `MaybeUninit`, `UnsafeCell`, and unwind edges—closing Flux's temporal/value gaps (`ptr/mod.rs:72–75`). |
| **(P5) Failure Legibility** | **Dual-layer localization:** Pre-emission failures use Flux's `ConstrReason` spans (`Overflow`, `Fold`, `Div`, `Assert`, `Goto`, `flux-refineck/src/lib.rs:210–346`); corrupted certificates fail in Lean at an exact `(blockId, clauseIdx)` boolean check. |
| **(C1–C2) Conceptual Minimality & Refuted Collapses** | **Collapses `PlacesTree` blocking into `PureLift.PermTree` and Octagon constraints into 2-sparse `OmegaCutCert` steps.** **Three premature collapses fail with concrete counterexamples:** (1) *Collapsing reborrows into `&strg<l: T1> ensures l: T2` fails* on `fn get_mut(v: &mut (u32, u32)) -> &mut u32` (`!can_auto_strong`, `rty/mod.rs:3415`), where the tuple's final state depends on future caller writes to the returned `&mut u32` (`BackTarget`). (2) *Collapsing `AiPcc` into `OmegaCutCert` fails* on `(x & 0xFF) < 256` and modular wraparound `len.wrapping_sub(hdr) <= max`, which are `O(1)` in `Tnum × WrappedInterval` but exponential via linear bit-blasting. (3) *Dropping `CutStep.divCut` for rational Farkas fails* on integer stride obligations `2 * k == 2 * m + 1 ⊢ False` and `4 * idx + 4 <= 4 * len` (`ptr/mod.rs:138`). |

## Boundaries

- **Empirical Haskell `fixpoint` vs. `rust-fixpoint` solver timings (`not examined`):** `flux-rs/flux` was inspected statically at `7d9886b36347e9e245fa8b354da7fb9662a2087c` without executing `cargo flux` or benchmarking solver backends (`lib/liquid-fixpoint/src/constraint_solving.rs`); empirical solving throughput was `not examined`.
- **`auto_strong` slice failure on Tock OS (`unknown`):** Upstream disables `auto_strong` on `inner_ty.is_slice()` (`crates/flux-middle/src/rty/mod.rs:3477–3478`, `TODO(auto-strong): including 'slice' breaks 'tock' for some reason...`); the exact failure mechanism in `PlacesTree` or unsized `Loc` instantiation remains `unknown` from static inspection.
- **Default `OverflowMode::None` proofs and temporal raw-pointer safety (`known not to apply`):** Proofs checked under Flux's default `OverflowMode::None` (`rty/mod.rs:3121–3232`) are `known not to apply` to wrapping or panicking machine integers in `Trusted.MirSemantics`; Flux's `core::ptr` refinements (`lib/flux-core/src/ptr/mod.rs:72–75`) are `known not to apply` to temporal liveness (use-after-free) or pointee value updates across `ptr::write`.
- **Direct reuse of Flux's `LeanEncoder` or Flex `MetaM` tactics in Anneal Pass 1 (`unsupported`):** Emitting `axiom PrimOp...`, `noncomputable def`, `set_option`, `deriving Inhabited`, stdout `"sorryAx"` checks (`crates/flux-infer/src/lean_encoding.rs:330–351, 633, 942`), or running Flex's `Zap`/`Fix` metaprograms (`arXiv:2607.12226`) inside Anneal `theory/` is `unsupported` under `trusted/audit/TrustedBoundary.lean:442–596`.

## Evidence

- **Primary Git Repositories (inspected `2026-11-19`):**
  - `flux-rs/flux` at `7d9886b36347e9e245fa8b354da7fb9662a2087c`:
    - `book/src/guide/architecture.md:1–48`; `lib/flux-rs/src/{lib,bitvec}.rs`; `crates/flux-driver/src/collector/detached_specs.rs:54–426`.
    - `crates/flux-middle/src/rty/mod.rs:75–220, 773–828, 1615–2233, 3075–3232, 3415–3513`.
    - `crates/flux-refineck/src/lib.rs:64–346, 375–518`; `crates/flux-refineck/src/type_env/place_ty.rs:25–320`; `crates/flux-refineck/src/ghost_statements.rs:47–240`.
    - `lib/flux-alloc/src/vec/mod.rs:10–87`; `lib/flux-core/src/ptr/mod.rs:1–260`.
    - `crates/flux-infer/src/fixpoint_qualifiers.rs:9–152`; `lib/liquid-fixpoint/src/{lib,constraint,constraint_solving}.rs`; `crates/flux-infer/src/fixpoint_encoding/decoding.rs:18–160`.
    - `crates/flux-infer/src/lean_encoding.rs:225–1237`; `crates/flux-infer/src/lean_format.rs:60–720`; `tools/runlean.py:1–139`.
  - `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:
    - `trusted/audit/TrustedBoundary.lean:425–610`; `trusted/lean/foundation-lock.json`; `theory/Anneal/PureLift/{LoanGraph,SpatialPin,MirBridge}.lean`.
- **Peer-Reviewed Publications & Preprints:**
  - Patrick M. Rondon, Ming Kawaguchi, Ranjit Jhala, *"Liquid Types"*, PLDI 2008, DOI `10.1145/1375581.1375602`.
  - Nico Lehmann, Adam T. Geller, Niki Vazou, Ranjit Jhala, *"Flux: Liquid Types for Rust"*, PACMPL 7(PLDI), Article 169, 2023, DOI `10.1145/3591283` (`arXiv:2207.04034`).
  - Nico Lehmann, Cole Kurashige, Nikhil Akiti, Niroop Krishnakumar, Ranjit Jhala, *"Generic Refinement Types"*, PACMPL 9(POPL), Article 49, 2025, DOI `10.1145/3704885`.
  - Vivien Rindisbacher et al., *"TickTock: Verified Isolation in a Production Embedded OS"*, SOSP 2025, DOI `10.1145/3731569.3764856`.
  - Jam Kabeer Ali Khan, Petros Markopoulos, Nico Lehmann, Ranjit Jhala, *"Foundational Constraint Solving for Expressive Refinement Typing"*, July 2026, `arXiv:2607.12226`.

## Revalidation

1. **`OverflowMode` and `auto_strong` guards (`flux-rs/flux`):** Diff `crates/flux-middle/src/rty/mod.rs` (`uint_invariants`, `int_invariants`, `slice_invariants`, `auto_strong`, `can_auto_strong`) against `7d9886b36347e9e245fa8b354da7fb9662a2087c`.
2. **Qualifiers and `$k` solution decoding (`flux-rs/flux`):** Diff `crates/flux-infer/src/fixpoint_qualifiers.rs` (`FIXPOINT_QUALIFIERS`), `lib/liquid-fixpoint/src/lib.rs` (`VerificationResult`), and `crates/flux-infer/src/fixpoint_encoding/decoding.rs` (`fixpoint_to_solution`).
3. **Native Lean exporter audit (`flux-rs/flux`):** Diff `crates/flux-infer/src/lean_encoding.rs` (`ProofReport::status`, `generate_opaque_const_file`) and `crates/flux-infer/src/lean_format.rs` (`LeanKConstraint`, `Expr::IsCtor`).
4. **Anneal Pass 1 compatibility (`joshlf/anneal`):** Diff `trusted/audit/TrustedBoundary.lean` (`allowedNotationSyntaxKinds`, `allowedTheoryTacticKinds`) and `trusted/lean/foundation-lock.json` against `c131b320eeeb26ef692e5afd5ec8db49ee518613`, and kernel-check the `prelude` definitions in Section 5.2 under `lean` `v4.34.1` (`-Ddebug.skipKernelTC=false`).
