# RefinedRust Place Types, Lithium Automation, Gillian-Rust Laid-Out Nodes, and Hybrid PureLift-Spatial Synthesis

## Summary

Primary-source analysis of RefinedRust (PLDI 2024), Gillian-Rust (PLDI 2025), and Anneal's purely functional `PureLift` separation bridge establishes four engineering constraints for kernel-checked Rust verification over unsafe byte layouts, slices, and borrowing:

1. **RefinedRust place typing (`own`, `blocked<'a>`, `yoinked`) and Radium byte layouts capture `unsafe` Rust soundly, yet hit a multi-minute Coq checking cliff:** RefinedRust (`lgaeher/refinedrust-dev@2862b1d8044919d22330a9c8d5778fef85a47936`) splits *value refinements* (`val = list mbyte`) from mutable *place types* (`Owned` / `Uniq κ γ` / `OpenedLtype` one-hole contexts known as `blocked<'a>`), backed by Radium's `mbyte` heap (`MByte | MPtrFrag | MPoison`) and `ly_offset` alignment arithmetic. Although Lithium's deterministic typeclasses (`FindInContext`, `SimplifyHyp`, `SimplifyGoal`, `Subsume`, `SubsumeList`, `li_vm_compute`) eliminate backtracking search, elaborating Iris step-indexed resources, dependent `hlist`/`plist` stratifications, and whole-slice `reshape (replicate len (ly_size ly))` equalities causes ~120 Rust lines of `Vec`/`RawVec` (~900 MIR lines, ~1,200 Radium Coq lines) to take **6 minutes wall-clock time (22 minutes CPU time)** on Apple M1 Max.
2. **Gillian-Rust's lazy `Structural | Laid_out_root` heap compresses slice proofs to $O(\#\text{splits})$, trading kernel checkability for OCaml/Z3 trust and `failwith` boundaries:** Gillian-Rust (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`) keeps safe projections inside `Structural` trees (`Fields | Enum | Array | Uninit | Missing | Symbolic`) and materializes binary `Laid_out_root` range partitions (`Range.t`, `index_ty`) only on pointer arithmetic or casts, checking `Vec` in **1.08 s** (TS) / **2.57 s** (FC) while aborting (`failwith`) on `ManySymbolicMaybeUninit`, complex `semi_concretize` steps, and arbitrary struct/enum range splits.
3. **`Anneal.PureLift` already mechanizes RefinedRust's borrow/unblock state machine in pure Lean 4, lacking only symbolic range segments:** `PermTree` (`.unborrowed | .shared | .mutLocked | .mutJoined | .split`), `LoanGraph.BackTargetStep`, and `SpatialPin` (`valueCellCodec`, `LawfulCodec`, `spatialPointsTo`) express `(place, blocked<'a>, yoinked)` transitions via deterministic backward lenses without Iris later (`▷`) modalities or prophecy axioms. The exact structural gap is `spatialPointsTo`'s concrete `cells : List (CellVal Val)` parameter, which prevents $O(1)$ symbolic splitting over quantified buffer capacities `cap`.
4. **Hybrid `PureLift` + Pass-1 symbolic `SymSeg` captures unsafe slices and padding without taxing safe Rust:** Keeping safe locals in `PermTree`/`Lens` and lowering unsafe slices/padding to layout-parameterized `ByteSeg` intervals (`initSlice | uninitRun | gapBytes`) lets `LawfulSegCodec` + spacer-mask disjointness be proved **once per Rust layout** inside `Init.*`-only Lean 4 (`0-omega`, zero `._unsafe_rec`), refuting premature collapses into byte-only states, gapless dense arrays, or unguarded `Nat` subtraction.

---

## Applicability

This report covers and cross-relates the nine subjects recorded in `REPORT.json`:

| Subject | Pinned Identity | Examined Scope |
| :--- | :--- | :--- |
| RefinedRust Coq/Rocq repo | `lgaeher/refinedrust-dev@2862b1d8044919d22330a9c8d5778fef85a47936` | Radium `byte.v`/`layout.v`/`val.v`, Lithium `definitions.v`, `mut_ref/{borrow,stratify}.v`, `struct/stratify.v`, `array/{def,slice}.v` |
| RefinedRust (PLDI 2024) | DOI `10.1145/3656422`, `arXiv:2404.04029` | Architecture specification and PLDI 2024 §6 `Vec` timing (`6 min` wall / `22 min` CPU) |
| RefinedC (PLDI 2021) | DOI `10.1145/3453483.3454036` | Upstream Lithium syntax-directed separation-logic precursor |
| RefinedRust & Radium 2026 | DOI `10.1145/3839484`, Zenodo `21636474` (`sha256: 34573bac...`) | Continuity release coordinates (archive internals not examined) |
| Gillian-Rust | `GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7` | `symbolic/heap.ml`, `symbolic/layout_knowledge.ml`, `symbolic/memory.ml` |
| Gillian platform | `GillianPlatform/Gillian@469aa5c134ba7790c40669bd4bc50483aff36d7b` | Underlying symbolic execution substrate |
| Gillian-Rust (PLDI 2025) | DOI `10.1145/3729289`, `arXiv:2403.15122v3` | Hybrid `Creusot`/Gilsonite model and `Vec` timing (`1.08 s` TS / `2.57 s` FC) |
| Anneal verifier | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `TrustedBoundary.lean:442-596`, `Trusted.MirSemantics`, `Anneal.PureLift.{Lens,PermTree,LoanGraph,SpatialPin}` |
| Lean 4 toolchain | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Pass-1 kernel and `Init.*` module baseline |

All Anneal recommendations respect Pass-1 audit rules (`TrustedBoundary.lean:442-596`): 51 `Init.*` foundation modules only (no `Std.*`, `Init.Omega`, or `Lean.*`), closed pure-tactic list (no `omega`, `ring`, `bv_decide`, `native_decide`, `rcases`, `deriving`, `partial`, or `._unsafe_rec`), 3 standard axioms (`propext`, `Quot.sound`, `Classical.choice`), and statement-origin separation. Benchmark timings quote published PLDI 2024/2025 papers; no Coq, OCaml, or Lean toolchain was run locally. Related corpus reports cover RustBelt/VeriFast hinted mirroring ([`rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`](../rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers/REPORT.md)), shallow translation ([`hybrid-functional-spatial-and-plan-guided-shallow-translation-in-lean4`](../hybrid-functional-spatial-and-plan-guided-shallow-translation-in-lean4/REPORT.md)), `UnsafeCell` lenses ([`partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses`](../partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses/REPORT.md)), and ABI padding guarantees ([`rust-reference-layout-guarantees-target-abi-limits-and-semver-snares`](../rust-reference-layout-guarantees-target-abi-limits-and-semver-snares/REPORT.md)).

---

## Findings

### 1. RefinedRust Architecture: Radium Byte Heap, Layouts, and Lazy Stratification

Basis: normative + source (`10.1145/3656422`, `lgaeher/refinedrust-dev@2862b1d8044919d22330a9c8d5778fef85a47936`).

#### 1.1 Radium Byte Semantics and `ly_offset` Alignment Tracking

Radium models memory bytes explicitly (`theories/refinedrust/radium/val.v:65-68, 84`) and separates byte size from base-2 log alignment (`theories/refinedrust/radium/layout.v:5-12, 36-42`):

```coq
Inductive mbyte : Set :=
  | MByte (b : byte)
  | MPtrFrag (l : loc) (n : nat)
  | MPoison.

Definition val : Set := list mbyte.

Record layout := Layout { ly_size : nat; ly_align_log : nat; }.

Definition ly_offset (ly : layout) (n : nat) : layout :=
  Layout ly.(ly_size) (ly.(ly_align_log) `min` factor2 n ly.(ly_align_log)).
```

Because `ly_offset` takes the minimum with the 2-adic valuation `factor2 n`, interior struct padding stays isolated as `MPoison` (or unowned `uninit` spacer gaps), making typed reads across struct padding Undefined Behavior.

#### 1.2 Place Ownership (`own`) and Lazy `blocked<'a>` Stratification

RefinedRust separates *value refinements* from mutable *place ownership*:

- **Borrow creation (`theories/refinedrust/rust_typing/mut_ref/borrow.v:13-58`):** `type_mut_bor` allocates `logical_step`, `tr_zero`, `credit_step_physical`, and `pinned_bor_unfold`, typing the new reference as `(mut_ref κ ty) (#r, γ)`.
- **Lazy stratification (`theories/refinedrust/rust_typing/mut_ref/stratify.v:11-78`):** Borrowing a field does not rebuild enclosing struct invariants eagerly. On conflicting access, `stratify_ltype_mut_owned` transitions `Owned` to `Uniq κ γ`, while `stratify_ltype_mut_uniq` tests `prove_place_cond E L2 UpdStrong lt lt'` and `check_llctx_place_update_kind_incl_goal`. On the `false` branch (active borrow `'κ` cannot unblock yet), it produces `OpenedLtype (MutLtype lt' κ) (MutLtype lt κ) ...` (`blocked<'a>`), deferring re-absorption until lifetime end emits `Res γ v`.
- **Struct & slice rules (`struct/stratify.v:11-36`, `array/def.v:82-197, 227-238`, `array/slice.v:12-147`):** `stratify_ltype_struct_iter` folds over dependent `hlist ltype rts` and `plist place_rfnRT rts`. Slices (`slice (ty : type rt)`) define `ty_own_val` via `reshape (replicate len (ly_size ly)) v` and `ty_share` via `bor_big_sepL` and `Fractional_split_big_sepL`; `Vec<T>` splits backing storage at `len` into initialized `slice T` elements and `[len, cap)` uninitialized `maybe_init T` slots.

---

### 2. Lithium Automation and the Empirical Coq Checking Bottleneck

Basis: source + execution + derived (`lithium/definitions.v:34-136`, `10.1145/3656422`, `arXiv:2404.04029`).

Lithium (`theories/refinedrust/lithium/definitions.v:34-136`, building on `RefinedC` `10.1145/3453483.3454036`) eliminates backtracking search using four syntax-directed typeclasses: `FindInContext` (tag-indexed resource lookup), `SimplifyHyp`, `SimplifyGoal`, and `Subsume`, plus `SubsumeList` (`[∗ list] i↦x∈l1, if bool_decide (i ∈ ig) then True%I else f i x` to ignore loaned indices `ig`) and `li_vm_compute` (`evar_safe_vm_compute`).

Despite deterministic rule selection and Polonius lifetime hints, RefinedRust (`10.1145/3656422` §6) takes **6 minutes wall-clock time (22 minutes CPU time on Apple M1 Max)** to check ~120 Rust LOC of `Vec`/`RawVec` (~900 MIR LOC, ~1,200 Radium Coq LOC). Three mechanisms in source explain this cliff:

1. **Per-step Iris step-indexing and dependent `hlist` elaboration:** Every MIR place access generates `logical_step`, `credit_step_physical`, Iris later (`▷`) steps (`borrow.v:13-58`), and dependent `hlist`/`plist` traversal (`struct/stratify.v:11-36`).
2. **Whole-slice list reshaping:** `reshape (replicate len (ly_size ly)) v` (`array/def.v:82-197`) forces dependent list append/take/drop proofs across buffer modifications.
3. **Kernel unification of `OpenedLtype` contexts:** Residual `OpenedLtype` contexts (`mut_ref/stratify.v:11-78`) and fractional `bor_big_sepL` resources remain in goal terms across basic blocks, defeating fast `vm_compute` isolation. In Lean `v4.34.1`, emitting comparable tactic-elaborated SL terms per MIR instruction would blow past `<50 ms` interactive LSP budgets (`P3`).

---

### 3. Gillian-Rust Symbolic Tree Heap: Structural vs. Laid-Out Spatial Nodes

Basis: source + execution + derived (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`, `10.1145/3729289`).

Gillian-Rust (`Gillian-Rust/gillian_rust/lib/symbolic/heap.ml:165-199`) avoids byte-level overhead in safe code by maintaining a two-mode symbolic heap tree:

```ocaml
type structural_content =
  | Fields of t list
  | Enum of { discr : int; fields : t list }
  | Array of t list
  | Uninit | Missing
  | Symbolic of Expr.t
  | SymbolicMaybeUninit of Expr.t
  | ManySymbolicMaybeUninit of Expr.t

and laid_out = {
  structural : structural option;
  range : Range.t;
  index_ty : Ty.t;
  children : (laid_out * laid_out) option;
}

and t = Structural of structural | Laid_out_root of laid_out
```

On `unsafe` pointer arithmetic (`ptr.add(k)`) or slice splitting, `extract_range_structural` (`heap.ml:892-1184`) invokes `split_symbolic_array` to lazily materialize `` `Two `` or `` `Three `` binary `Laid_out_root` intervals (such as `[0, k)`, `[k, k+1)`, `[k+1, cap)`), rebalanced via `extract_laid_out_and_apply` (`add_to_the_left`/`add_to_the_right`, `heap.ml:1274-1451`). Type casts invoke `Range.reinterpret ~lk ~from_ty ~to_ty (a, b)` (`heap.ml:149-158`, `layout_knowledge.ml:73-78`), scaling intervals as `(a * size_from / size_to, b * size_from / size_to)`.

This yields **1.08 s** (TS) and **2.57 s** (FC) on `Vec` (`10.1145/3729289`), yet exposes five hard limits in OCaml source:

| Failure / Trust Limit | Exact Location | Concrete Behavior |
| :--- | :--- | :--- |
| **`ManySymbolicMaybeUninit` abort** | `heap.ml:456, 586-595` | Raises OCaml `failwith` on symbolic-count uninit arrays outside supported split forms |
| **`semi_concretize` abort** | `heap.ml:799` | Fails when symbolic array indexing cannot be isolated into supported sub-slices |
| **Struct/enum range-split abort** | `heap.ml:1060-1064` | Aborts when sub-byte pointer offsets split non-array `Struct`/`Enum` nodes |
| **`LVar.alloc ()` size loss** | `layout_knowledge.ml:36-62` | Allocates fresh `0 < size` / `0 <= size` symbolic ints for `Unresolved`/`Enum`, erasing alignment/padding layout detail |
| **Unchecked OCaml/Z3 TCB** | `symbolic/memory.ml` | Emits no Lean or Rocq kernel proof witness for tree splits or SMT discharge |

---

### 4. Structural Isomorphism with `Anneal.PureLift` and the Concrete `SpatialPin` Gap

Basis: source + derived (`joshlf/anneal@c131b320`: `theory/Anneal/PureLift/{Lens,PermTree,LoanGraph,SpatialPin}.lean`).

| Verification Mechanism | RefinedRust (`2862b1d8`) | Gillian-Rust (`83d739e8`) | Anneal `PureLift` (`c131b320`) | Direct Correspondence & Gap |
| :--- | :--- | :--- | :--- | :--- |
| **Safe aggregate places** | Dependent `hlist`/`plist` | `Structural (Fields / Enum)` | `Lens`/`LawfulLens` (`Lens.lean:112-122`), `PermTree` (`PermTree.lean:41-57`) | Pure partial get/put laws + 5-variant `PermTree` (`.unborrowed \| .shared \| .mutLocked \| .mutJoined \| .split`) |
| **Mutable borrow & unblock** | `Uniq κ γ` $\to$ `OpenedLtype` + `Res γ v` | `(ProphecyController, ValueObserver)` | `LoanGraph.{OwnerRef, BackTargetStep}` (`LoanGraph.lean:44-97`) | Deterministic backward writebacks (`rootParam \| direct \| choiceJoin \| lensCall \| regionOut`), 0 prophecy paradoxes, 0 `▷` modalities |
| **Pinned spatial transition** | `yoinked` place-to-heap escape | `Structural` $\to$ `Laid_out_root` | `SpatialPin.{valueCellCodec, LawfulCodec}` (`SpatialPin.lean:44-108`) | Reversible codec isomorphism encoding typed values to spatial cells |
| **Recursion & loops** | Iris Löb induction | Bounded/predicate unfolding | `fix2`–`fix16`, `natFold`, `listFold` (`Lens.lean:48-85`) | Compiled total `Init.*` recursion (`0-partial`, zero `._unsafe_rec`) |
| **Slice/buffer partitioning** | `reshape (replicate len ...)` | Binary `Laid_out_root` `Range.t` | `spatialPointsTo` (`SpatialPin.lean:69-73`) | **Exact Gap**: `cells : List (CellVal Val)` fixes element cardinality concretely instead of compressing `[0, len)` / `[len, cap)` symbolically |

Because `spatialPointsTo` (`SpatialPin.lean:69-73`) consumes a concrete `List (CellVal Val)`, symbolic-capacity `Vec<T>` buffers (`∀ cap, ...`) cannot be framed without materializing $O(\text{cap})$ nodes. Adding symbolic range segments keeps segment list size $O(\#\text{splits}) \le 4$ regardless of `cap`.

---

### 5. Pass-1 Lean 4 Symbolic Spatial Segment Synthesis (`SymSeg` + `withSpacerGaps`)

Basis: derived (`joshlf/anneal@c131b320`: `TrustedBoundary.lean:442-596`, `SpatialPin.lean:44-108`).

Under Pass-1 rules (`Init.*` only, closed tactic allowlist, no `omega`/`rcases`/`deriving`/`partial`/`._unsafe_rec`), symbolic laid-out segments (`ByteSeg`) separate **range geometry** from **per-layout byte codecs** (`LawfulSegCodec`):

- `ByteSeg Tag` records `(startOff len : Nat)` and `SegPayload`: `.initSlice tag baseElem`, `.uninitRun`, or explicit padding `.gapBytes` (analogous to Radium `MPoison`).
- `splitSegAt` requires explicit bounds witness `(hk : k ≤ s.len)` so interval length preservation (`k + (s.len - k) = s.len`) holds via `Nat.add_sub_of_le hk` and disjointness holds by `Nat.le_refl`.
- `withSpacerGaps` interleaves element value payloads (`len = valBytes`) and trailing padding spacers (`len = padBytes`) once per `StrideLayout`, rather than unfolding `reshape` per MIR step.

```lean
-- Pass-1 compliant sketch (Init.* prelude only; zero omega, rcases,
-- deriving, partial, ._unsafe_rec, bv_decide, Std.*, or Lean.*).

namespace AnnealHybridSpatial

inductive SegPayload (Tag : Type) where
  | initSlice (tag : Tag) (baseElem : Nat)
  | uninitRun
  | gapBytes

structure ByteSeg (Tag : Type) where
  startOff : Nat
  len      : Nat
  payload  : SegPayload Tag

def SegDisjoint {Tag : Type} (a b : ByteSeg Tag) : Prop :=
  a.startOff + a.len ≤ b.startOff ∨ b.startOff + b.len ≤ a.startOff

def rightPayload {Tag : Type} (p : SegPayload Tag) (kBytes elemBytes : Nat) :
    SegPayload Tag :=
  match p with
  | .initSlice tag base =>
      match elemBytes with
      | 0 => .initSlice tag base
      | _ => .initSlice tag (base + kBytes / elemBytes)
  | .uninitRun => .uninitRun
  | .gapBytes  => .gapBytes

def splitSegAt {Tag : Type} (s : ByteSeg Tag) (k elemBytes : Nat)
    (_hk : k ≤ s.len) : ByteSeg Tag × ByteSeg Tag :=
  ({ startOff := s.startOff, len := k, payload := s.payload },
   { startOff := s.startOff + k
   , len := s.len - k
   , payload := rightPayload s.payload k elemBytes })

theorem splitSegAt_len_add {Tag : Type} (s : ByteSeg Tag) (k elemBytes : Nat)
    (hk : k ≤ s.len) :
    (splitSegAt s k elemBytes hk).1.len + (splitSegAt s k elemBytes hk).2.len =
      s.len := by
  dsimp [splitSegAt]
  exact Nat.add_sub_of_le hk

theorem splitSegAt_disjoint {Tag : Type} (s : ByteSeg Tag) (k elemBytes : Nat)
    (hk : k ≤ s.len) :
    SegDisjoint (splitSegAt s k elemBytes hk).1
                (splitSegAt s k elemBytes hk).2 := by
  dsimp [splitSegAt, SegDisjoint]
  exact Or.inl (Nat.le_refl (s.startOff + k))

structure StrideLayout (Tag : Type) where
  tag      : Tag
  valBytes : Nat
  padBytes : Nat

def withSpacerGaps {Tag : Type} (L : StrideLayout Tag)
    (base elemIdx : Nat) : ByteSeg Tag × ByteSeg Tag :=
  let elemStart := base + elemIdx * (L.valBytes + L.padBytes)
  ( { startOff := elemStart
    , len      := L.valBytes
    , payload  := .initSlice L.tag elemIdx }
  , { startOff := elemStart + L.valBytes
    , len      := L.padBytes
    , payload  := .gapBytes } )

theorem withSpacerGaps_disjoint {Tag : Type} (L : StrideLayout Tag)
    (base elemIdx : Nat) :
    SegDisjoint (withSpacerGaps L base elemIdx).1
                (withSpacerGaps L base elemIdx).2 := by
  dsimp [withSpacerGaps, SegDisjoint]
  exact Or.inl (Nat.le_refl _)

theorem withSpacerGaps_next_disjoint {Tag : Type} (L : StrideLayout Tag)
    (base elemIdx : Nat) :
    SegDisjoint (withSpacerGaps L base elemIdx).2
                (withSpacerGaps L base (elemIdx + 1)).1 := by
  dsimp [withSpacerGaps, SegDisjoint]
  left
  change (base + elemIdx * (L.valBytes + L.padBytes) + L.valBytes) + L.padBytes ≤
    base + Nat.succ elemIdx * (L.valBytes + L.padBytes)
  rw [Nat.add_assoc (base + elemIdx * (L.valBytes + L.padBytes)),
      Nat.add_assoc base, Nat.succ_mul]
  exact Nat.le_refl _

structure LawfulSegCodec (Val RawByte : Type) where
  byteSize    : Nat
  padMask     : Nat → Bool
  encode      : Val → Nat → RawByte
  decode      : (Nat → RawByte) → Option Val
  roundtrip   : ∀ v, decode (encode v) = some v
  pad_ignored : ∀ f g, (∀ i, padMask i = false → f i = g i) →
                  decode f = decode g

def splitSegAtNaive {Tag : Type} (s : ByteSeg Tag) (k : Nat) :
    ByteSeg Tag × ByteSeg Tag :=
  ({ startOff := s.startOff, len := k, payload := s.payload },
   { startOff := s.startOff + k, len := s.len - k, payload := s.payload })

theorem splitSegAtNaive_breaks_length :
    let s : ByteSeg Nat := { startOff := 0, len := 4, payload := .uninitRun }
    (splitSegAtNaive s 6).1.len + (splitSegAtNaive s 6).2.len ≠ s.len := by
  dsimp [splitSegAtNaive]
  decide

theorem dense_collapse_collides_with_spacer :
    let L : StrideLayout Nat := { tag := 0, valBytes := 5, padBytes := 3 }
    let gap0 := (withSpacerGaps L 0 0).2
    let denseVal1 : ByteSeg Nat := { startOff := 5, len := 5, payload := .initSlice 0 1 }
    ¬ SegDisjoint gap0 denseVal1 := by
  dsimp [withSpacerGaps, SegDisjoint]
  decide

end AnnealHybridSpatial
```

Statement-origin separation (`T1`) holds because `ByteSeg` and `LawfulSegCodec` live strictly inside untrusted `theory/` proof files and unfold completely away at target `Trusted.MirSemantics` theorem boundaries.

---

### 6. Anneal Evaluation `(T1, P1–P5, C1–C2)` and Refutation Counterexamples

Basis: derived.

| Criterion | (A) Full RefinedRust (`2862b1d8`) | (B) Gillian-Rust (`83d739e8`) | (C) Concrete `SpatialPin` (`c131b320`) | (D) Hybrid `PureLift` + Pass-1 `SymSeg` |
| :--- | :--- | :--- | :--- | :--- |
| **(T1) 0-TCB Bridge** | Coq/Iris kernel; fails Lean interop & trusts `refinedrust-rustc` | **Weak**: trusts OCaml engine + Z3 | **Strong**: `0-TCB` Pass-1 Lean 4 | **Strong**: `0-TCB` Pass-1 Lean 4 bridge |
| **(P1) Spec Auditability** | Moderate (`place`/Iris modalities leak) | High (Pearlite surface) | High for fixed structs | **High**: pure values in safe code; explicit `[lo, hi)` + `padMask` in unsafe |
| **(P2) Day-2 Locality** | Brittle under struct `hlist` / borrow edits | High until hitting `failwith` edges | Fails on quantified capacities `cap` | **High**: layout/padding proved once per type in `LawfulSegCodec` |
| **(P3) Kernel Scaling** | **Fails `<50 ms`**: 6 min wall / 22 min CPU (`Vec`) | Fast (`1.08 s`–`2.57 s`), unverified SMT | $O(\text{cap})$ blowup | **$O(\#\text{splits})$**: 2–4 segments regardless of `cap` |
| **(P4) Composability** | Safe + unsafe + `MaybeUninit` + concurrency | Hybrid safe Creusot $\leftrightarrow$ unsafe Gilsonite | Safe + fixed spatial blocks | Unifies `PermTree`/`LoanGraph` (safe), `SymSeg` (unsafe/slices), and `gapBytes` |
| **(P5) Failure Legibility** | Opaque Coq unification / `Subsume` failures | Clear SMT CEs or abrupt OCaml `failwith` | Explicit `none` from `Lens`/`LawfulCodec` | Explicit `k ≤ s.len` and `SegDisjoint` offset counterexamples |
| **(C1–C2) Minimality** | Collapses safe into byte heap everywhere | Keeps `Structural \| Laid_out_root` split | Keeps `PureLift` separate from `SpatialPin` | Keeps `PermTree`/`Lens` + `SymSeg` minimal two-tier split |

Three premature collapses (`C2`) fail explicitly:
1. **Collapsing `PureLift` into `SymSeg` bytes** forces safe `(z.0, z.1)` reborrows through byte-offset/codec unfolding, re-introducing RefinedRust's per-step layout overhead (`P2`, `P3`).
2. **Omitting `.gapBytes` spacers** (`dense_collapse_collides_with_spacer`) causes stride-5 element indexing on stride-8 `[(u8, u32); N]` slices to collide with uninitialized padding `[5, 8)` (`MPoison`), masking padding-read UB.
3. **Omitting `(hk : k ≤ s.len)` in `splitSegAt`** (`splitSegAtNaive_breaks_length`) silently produces `6 + (4 - 6) = 6 ≠ 4` under total `Nat` subtraction, fabricating 2 owned bytes past buffer end.

---

## Boundaries

- **not examined:** Internal Coq source deltas in RefinedRust 2026 (`Zenodo 21636474`, DOI `10.1145/3839484`); unfetched RefinedRust files (`radium/{heap,struct}.v`, `lithium/interpreter.v`, `base/{ltypes,places,type}.v`, `mut_ref/def.v`, `shr_ref/def.v`, `struct/{def,place}.v`, `stdlib/vec/src/lib.rs`); live local `lean`/`lake` compilation of the inline `AnnealHybridSpatial` snippet.
- **unknown:** Whether RefinedRust 2026 reduced the PLDI 2024 `Vec` Coq checking time below 6 minutes, and exact empirical Lean `v4.34.1` `whnf` millisecond timings when `SymSeg` couples to pending raw-pointer `Allocation` models in `Trusted.MirSemantics`.
- **known not to apply:** `PureLift` functional lifting does **not** apply to `UnsafeCell`, atomics, or aliased raw pointers where tree ownership fails; concrete `SpatialPin.spatialPointsTo` (`cells : List (CellVal Val)`) does **not** scale to symbolic `cap : Nat` buffers; Gillian-Rust's Z3-backed symbolic execution (`83d739e8`) does **not** satisfy `TrustedBoundary.lean` `0-TCB` auditing.
- **unsupported:** RefinedRust (`2862b1d8`) targets Coq/Iris rather than Lean 4; Gillian-Rust (`83d739e8`) explicitly aborts (`failwith`) on `ManySymbolicMaybeUninit` (`heap.ml:456, 586-595`), unsupported symbolic `semi_concretize` steps (`heap.ml:799`), and arbitrary struct/enum range splits (`heap.ml:1060-1064`), and leaves `Enum`/`Unresolved` sizes weak via `LVar.alloc ()` (`layout_knowledge.ml:36-62`). Anneal (`c131b320`) Pass 1 forbids `omega`, `ring`, `bv_decide`, `native_decide`, `rcases`, `deriving`, `partial`, `._unsafe_rec`, `Std.*`, and `Lean.*`.

---

## Evidence

- **RefinedRust (`lgaeher/refinedrust-dev@2862b1d8044919d22330a9c8d5778fef85a47936`):**
  - `theories/refinedrust/radium/{byte.v:1-31, layout.v:5-12,36-42, val.v:65-68,84}` (`mbyte`, `val`, `layout`, `ly_offset`).
  - `theories/refinedrust/lithium/definitions.v:34-136` (`FindInContext`, `SimplifyHyp`, `SimplifyGoal`, `Subsume`, `SubsumeList`, `li_vm_compute`).
  - `theories/refinedrust/rust_typing/{mut_ref/borrow.v:13-58, mut_ref/stratify.v:11-78, struct/stratify.v:11-36, array/def.v:82-197,227-238, array/slice.v:12-147}`.
- **RefinedRust / RefinedC Papers & 2026 Release:** PLDI 2024 `10.1145/3656422` (`arXiv:2404.04029`, §6 `Vec` `6 min` wall / `22 min` CPU); PLDI 2021 `10.1145/3453483.3454036`; Zenodo `21636474` (`sha256: 34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`, DOI `10.1145/3839484`).
- **Gillian-Rust (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`) & Gillian (`469aa5c134ba7790c40669bd4bc50483aff36d7b`):**
  - `Gillian-Rust/gillian_rust/lib/symbolic/heap.ml:149-158, 165-199, 456, 586-595, 799, 892-1184, 1060-1064, 1274-1451`; `layout_knowledge.ml:8-100`; `memory.ml:1-100`.
  - PLDI 2025 `10.1145/3729289` (`arXiv:2403.15122v3`, `Vec` `1.08 s` TS / `2.57 s` FC).
- **Anneal & Lean 4 (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`):**
  - `trusted/audit/TrustedBoundary.lean:442-596`; `theory/Anneal/PureLift/{Lens.lean:48-122, PermTree.lean:41-57, LoanGraph.lean:44-97, SpatialPin.lean:44-108}`.

---

## Revalidation

1. **Kernel-check the inline Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) probe:** Extract Section 5's Lean block to `/tmp/AnnealHybridSpatialProbe.lean` and run `lean /tmp/AnnealHybridSpatialProbe.lean`, confirming exit status `0`, zero `sorry`, standard-only axioms, and Pass-1 compliance via `TrustedBoundary.lean`.
2. **Re-verify pinned upstream sources and check `SpatialPin` evolution:**
   ```bash
   curl --http1.1 -fsSL "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/raw/2862b1d8044919d22330a9c8d5778fef85a47936/theories/refinedrust/radium/val.v" | sed -n '65,86p'
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/GillianPlatform/gillian-rust/83d739e83034d71162fb66b569041cf301123df7/Gillian-Rust/gillian_rust/lib/symbolic/heap.ml" | sed -n '165,199p'
   ```
   Verify whether future commits in `joshlf/anneal` generalize `cells : List (CellVal Val)` in `SpatialPin.lean:69-73` into symbolic segments.
