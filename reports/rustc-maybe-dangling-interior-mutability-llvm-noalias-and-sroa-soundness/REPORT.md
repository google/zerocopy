# `MaybeDangling`-like types in rustc: `Freeze`/`Unpin`-driven LLVM parameter attributes, retained scalar validity, and the SROA exclusion

## Summary

Two `rust-lang/rust` revisions are compared throughout. **R98** is
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (rustc 1.98.0-nightly, 2026-05-31, LLVM 22.1.6).
**R102** is `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (rustc 1.102.0-nightly, 2026-11-11,
LLVM 23.1.5). R98 was executed for this report; R102 was read as source and is represented
on the execution side only by a retained record that was not re-run (see Applicability).

- **What LLVM is told about a pointer argument is decided by `Freeze`, `Unpin` and the
  wrapper, in three steps.** `ty_and_layout_pointee_info_at` computes a
  `PointeeInfo { safe, size, align }`; `arg_attrs_for_rust_scalar` turns that plus the ABI
  scalar into `ArgAttributes`; `get_attrs` in the LLVM backend turns those into attributes.
  `&T` is `frozen` iff `T: Freeze`; `&mut T` is `unpin` iff `T: Unpin` and `T: UnsafeUnpin`.
  Only frozen shared and unpin mutable references get a non-zero `size`, `noalias` and (R102
  only) `nofree`; only frozen shared references get `readonly` and
  `captures(address, read_provenance)`. `&mut UnsafeCell<u64>` is therefore fully
  attributed (interior mutability is irrelevant under `&mut`), while `&UnsafeCell<u64>` and
  `&mut PinnedU64` are reduced to `noundef nonnull align 8`.
- **A maybe-dangling-like wrapper erases everything memory-dependent and nothing else.**
  The patched `PointeeInfo` is `{ safe: None, size: 0, align: <inner align> }`; the ABI
  scalar is untouched, so `noundef`, `nonnull`, `align 8` and the null niche survive.
  `MaybeDangling<&u64>` and `ManuallyDrop<&u64>` lower to `ptr noundef nonnull align 8` and
  `Option` of either is 8 bytes; `MaybeUninit<&u64>` (a union) lowers to bare `ptr` and
  `Option` of it is 16 bytes.
- **The same split is what the interpreter checks.** Under Miri a dangling reference inside
  `MaybeDangling`/`ManuallyDrop` is accepted, a null or misaligned one is undefined
  behaviour, and taking the reference out (`into_inner`) while it dangles is undefined
  behaviour again.
- **At R102 one predicate, `Ty::is_like_maybe_dangling`, names the affected types** —
  `MaybeDangling<T>`, `ManuallyDrop<T>` and coroutines — and it has exactly four call sites
  in the whole tree: pointee info, interpreter validity, the experimental codegen retag
  plan, and the SROA exclusion. At R98 the predicate does not exist: only
  `AdtDef::is_maybe_dangling` is consulted (two call sites), `ManuallyDrop<T>` gets the
  semantics by containing a `MaybeDangling<T>` field, coroutines are not covered, and SROA
  has no exclusion.
- **Without the exclusion SROA is observably wrong.** At R98
  `ScalarReplacementOfAggregates` rewrites a whole-value copy of a `MaybeDangling<&u64>` or
  `ManuallyDrop<&u64>` into a copy at type `&u64`. A program that Miri accepts at its
  defaults is reported as undefined behaviour ("constructing invalid value of type `&u64`:
  encountered a dangling reference (use-after-free)") when Miri interprets the MIR as SROA
  leaves it, and is accepted again when SROA alone is switched off. Upstream fixed this in
  `rust-lang/rust` PR #164568 (issue #164176); the fix is in R102.
- **The `nofree` attribute and the meaning of `dereferenceable` changed between the two
  LLVM generations.** In the LLVM 23 LangRef `dereferenceable` speaks only about function
  entry and `nofree` forbids frees through pointers based on the argument for the duration
  of the call; rustc R102 emits `nofree` and gates
  `dereferenceable` on `LLVM >= 23 || NoFree`. R98 has no `NoFree` attribute. The R98
  parameter strings observed here equal the R102 ones with `nofree` deleted.
- **A Lean 4 model (58 theorems, no `sorry`, axioms limited to `propext`)** transcribes the
  lowering, the validity invariant, a small call-time aliasing machine and the SROA rewrite,
  and proves: the nine rows; that every emitted value-level attribute holds of every valid
  value; that `noalias`/`nofree`/`dereferenceable`/`readonly` are emitted only for kinds
  whose call-time contract justifies them; that the null niche is kept by every non-union
  wrapper and lost under a union; and that peeling a wrapper off a typed copy is sound
  exactly for the wrappers the R102 SROA predicate does not exclude.

## Applicability

**Subjects and how they relate.** `REPORT.json` lists six subjects.

1. `rust-lang/rust` at R102 — source audit of the compiler, the standard library wrappers and
   one codegen test. It is also the toolchain of the retained execution record.
2. `rust-lang/rust` at R98 — source audit of the same files, and the toolchain (rustc and the
   Miri built from the same commit) on which every probe in this report was run.
3. `rust-lang/llvm-project` at `0a5579eb649d3634a9c30ac873300cc2944fa070`, the
   `src/llvm-project` submodule commit of R102 (branch `rustc/23.1-2026-07-22`) — normative
   text of the parameter attributes for LLVM 23.
4. `rust-lang/llvm-project` at `08c84e69a84d95936296dfcab0e38b34100725d5`, the submodule
   commit of R98 — the same text for LLVM 22.
5. `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` — inspected only to state
   which of these notions its trusted MIR semantics and its vendored interpreter model
   represent (Findings, last subsection).
6. `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`) — the
   checker for the Lean file.

**What was executed, and where.** Host and target `x86_64-unknown-linux-gnu`; 64-bit
pointers; edition 2021; `#![feature(maybe_dangling)]`.

- *Re-run for this report (2026-11-21), R98 only:* LLVM IR at
  `-C opt-level=2 -C no-prepopulate-passes` and at `-C opt-level=0`; `size_of`; nine Miri
  programs at Miri defaults (Stacked Borrows, validation on, MIR optimisations off); MIR
  dumps around `ScalarReplacementOfAggregates` at `-C opt-level=2`; and the SROA hazard
  programs under Miri with explicit `-Zmir-opt-level` / `-Zmir-enable-passes` flags.
- *Not re-run:* anything at R102. No R102 toolchain (and no LLVM 23) was available on the
  host that ran the probe, and none could be installed there. The file
  `support/retained_record_rustc_1_102_0_nightly_3ef0c22cd_llvm_23_1_5.json` is the output
  of an earlier run of a predecessor of the probe on that toolchain; its acquisition date
  is not recorded in it (between the toolchain's commit date 2026-11-11 and 2026-11-21).
  In this report it is cited as **execution (retained record)** and is never the only basis
  for a claim: each R102 row is also derived from R102 source, and the R98 run reproduces
  it up to the differences that the source diff predicts.

**Shared versus revision-specific behaviour.**

| Behaviour | R98 | R102 |
| :-- | :-- | :-- |
| `Freeze`/`Unpin` drive `frozen`/`unpin`, `size`, `noalias`, `readonly` | yes | yes |
| `MaybeDangling<&T>` lowers to `noundef nonnull align N` | yes | yes |
| `ManuallyDrop<&T>` lowers the same way | yes, through its `MaybeDangling<T>` field | yes, natively |
| `nofree` emitted | no (no such `ArgAttribute`) | yes |
| Dangling accepted, null/misaligned rejected inside the wrappers (Miri) | yes | yes (retained record) |
| Coroutine types are named by the maybe-dangling rule | no | yes |
| SROA excludes maybe-dangling-like locals | **no** | yes |
| Experimental codegen retag plan (`-Zcodegen-emit-retag`) exists | no | yes |

**Scope limits that bound every finding.** Only thin references to 8-byte, 8-aligned
pointees, passed as a direct scalar argument, were lowered and executed. `Box`, wide
pointers, return values, scalar pairs, indirect passing, other targets, other backends
(Cranelift, GCC), `-Zbox-noalias`, `-Zmutable-noalias`, `-Zllvm-writable` and sanitizers
were not exercised. Miri results are for Stacked Borrows; Tree Borrows was not run. The
Lean model is a model: it is tied to rustc only by transcription and by agreement with the
observed rows.

## Findings

### The predicate and its three type families (R102)

Basis: source.

```rust
// compiler/rustc_middle/src/ty/sty.rs:2167-2181 (R102)
/// Returns `true` if this is a `MaybeDangling<T>`-like type, i.e., a type whose inner
/// references are not required to be dereferenceable and are not reborrowed.
#[inline]
pub fn is_like_maybe_dangling(self) -> bool {
    match self.kind() {
        ty::Adt(def, _) => {
            // ManuallyDrop is "natively" like maybe-dangling so that we don't have
            // to nest field types even deeper.
            def.flags().contains(AdtFlags::IS_MAYBE_DANGLING)
                || def.flags().contains(AdtFlags::IS_MANUALLY_DROP)
        }
        ty::Coroutine(..) => true,
        _ => false,
    }
}
```

`AdtFlags::IS_MAYBE_DANGLING` (`1 << 14`) and `IS_MANUALLY_DROP` (`1 << 7`) are set from the
lang items `maybe_dangling` and `manually_drop` (`compiler/rustc_middle/src/ty/adt.rs:53-71,
399-409`). The flag's own doc comment warns: "Note that this is not the only type with
"maybe dangling" semantics! Use `ty.is_like_maybe_dangling()` to check for that."

Why three families, from the history of `rust-lang/rust` (PR and issue numbers in this
report are that repository's; each SHA below was read from the GitHub API on 2026-11-21):

| When (merge) | Change | Effect on the set |
| :-- | :-- | :-- |
| 2025-12-27, PR #149775, merge `08509492139968a96a005ba811a995e2f1d6a2ac` | "Add `MaybeDangling` to `core`"; includes commit `722e3102a22c529bade40c61f63bb3d88845360a` "use `MaybeDangling` in `ManuallyDrop`" | The type exists and `ManuallyDrop<T>` wraps a `MaybeDangling<T>` field; no compiler semantics yet |
| 2026-03-05, PR #150447, merge `64b72a1fa5449d928d5f553b01a596b78ee255d2` | "Implement `MaybeDangling` compiler support"; commits `7cefcb41ff7e27f3619bfecff429f72b5f3bface` "add an adt flag for `MaybeDangling`" and `8aafa5350435352a227c266c3d757e5235d96a98` "add semantics to `MaybeDangling`" (touches `rustc_abi`, `rustc_middle/src/ty/layout.rs`, `rustc_ty_utils/src/abi.rs`) | Codegen side: patched `PointeeInfo` for `{MaybeDangling}` via `AdtDef::is_maybe_dangling` |
| 2026-03-09, PR #150446, merge `8fc4e47ee1a36862be751ef148618659ba9c7999` | "miri/const eval: support `MaybeDangling`" | Interpreter side (by its title); the change issue #164176 names as having made the affected programs defined |
| 2026-09-05, PR #160745, merge `015777700540b3876f2b5b513b9e79160f83f4dd` | commit `e7c3734a6a8d0e1f0e9de055c91ea008372beaf2` introduces `is_like_maybe_dangling` with `ty::Closure(..) \| ty::Coroutine(..) \| ty::CoroutineClosure(..)`; commit `b7e5447e85cc1869c7dd26d14310cd351d3f8cf0` adds `IS_MANUALLY_DROP` and changes the library definition to `ManuallyDrop<T> { value: T }` | `{MaybeDangling, ManuallyDrop, closures, coroutines, coroutine-closures}` |
| 2026-09-24, PR #162361, merge `ad2e756c7093149e25f67a747e579a49b7e6976e` | commit `8201a7b4bd655461299236b4e7b815411f1a42e5` "give noalias back to refs in closures" removes `ty::Closure(..)` | closures leave |
| 2026-09-25, PR #163308, merge `02bc9556f4176a80df3bf9971edd50afa270adaa` | commit `4b538231e35e6edbc13ed012dd788a8f432d73fd` removes `ty::CoroutineClosure(..)` | `{MaybeDangling, ManuallyDrop, coroutines}` — the R102 set |

The stated motivations are primary-source text, not this report's inference. PR #160745:
moving a closure or generator "will alter its contents (by retagging)", and for movable
generators that hold a mutable reference reborrowed from another reference stored in the
same generator "the only way this is sound is if the reborrowed-from references are inside
MaybeDangling"; it also notes that making `ManuallyDrop` native reduces "field nesting",
which is what the code comment "so that we don't have to nest field types even deeper"
refers to. PR #162361 describes itself as reverting parts of #160745 for closures.

At **R98** none of this exists yet: `AdtDef::is_maybe_dangling`
(`compiler/rustc_middle/src/ty/adt.rs:510-514`) is the only query, and the library has
`pub struct ManuallyDrop<T: ?Sized> { value: MaybeDangling<T> }`
(`library/core/src/mem/manually_drop.rs:157-163`). The definition of `MaybeDangling` is
the same in both revisions: `#[repr(transparent)] #[rustc_pub_transparent] #[lang = "maybe_dangling"]
pub struct MaybeDangling<P: ?Sized>(P);`, unstable under feature `maybe_dangling`
(issue 118166). Its documentation states the retained requirement directly
(`library/core/src/mem/maybe_dangling.rs:50-51`, R102): "Note that the bit pattern must
still be valid for the wrapped type. That is, [references] (and [boxes]) still must be
aligned and non-null."

### The four call sites (R102)

Basis: source. A search of the complete R102 source archive finds the identifier six times:
the definition, the doc comment in `adt.rs`, and these four uses.

| # | Location (R102) | What the use does |
| :-- | :-- | :-- |
| 1 | `compiler/rustc_middle/src/ty/layout.rs:1204-1217`, in `ty_and_layout_pointee_info_at` (`:1054-1231`) | After finding the inner pointer's `PointeeInfo`, "Patch result if we are a MaybeDangling-like type": `safe: None` ("thus removing noalias/readonly/etc in case of the llvm backend"), `size: Size::ZERO` ("Make sure we don't assert dereferenceability of the pointer"), `align: info.align` ("Preserve the alignment assertion! That is required even inside `MaybeDangling`"). |
| 2 | `compiler/rustc_const_eval/src/interpret/validity.rs:1543-1556` | `self.may_dangle \|= val.layout.ty.is_like_maybe_dangling();` around the default `walk_value`, restored afterwards. The flag is sticky for everything nested inside. |
| 3 | `compiler/rustc_codegen_ssa/src/mir/retag.rs:90-91`, in `RetagPlan::build` (`:67-94`) | `_ if layout.ty.is_like_maybe_dangling() => None`: "Skip traversing for everything inside of `MaybeDangling`", so no retag call is planned for any pointer inside. |
| 4 | `compiler/rustc_mir_transform/src/sroa.rs:65-68`, in the `is_excluded_ty` closure of `escaping_locals` (`:56-76`) | "Types like MaybeDangling relax validity requirements of inner references." A local of such a type is never flattened. |

At R98 the corresponding sites are two: `layout.rs:1061-1073` (a dedicated match arm
`ty::Adt(adt_def, ..) if adt_def.is_maybe_dangling()` producing the same patched
`PointeeInfo`) and `validity.rs:1549-1556` (`mem::replace(&mut self.may_dangle, true)` around
the single field). `retag.rs` does not exist at R98, and `sroa.rs:65-87` has no such test.

### From type to LLVM parameter attributes

Basis: source (both revisions) + normative LangRef text.

**Step 1 — `PointeeInfo`** (`compiler/rustc_abi/src/lib.rs:2349-2381`, R102):
`safe: Option<PointerKind>` ("If this is `None`, then this is a raw pointer"), `size` ("If
`size` is not zero, then the pointer is either null or dereferenceable for this many
bytes … "Dereferenceable" means that it's sound to add a speculative (spurious) read of
the pointer"), `align`. `PointerKind` is `SharedRef { frozen }`, `MutableRef { unpin }` or
`Box { unpin, global }`.

For references (`layout.rs:1071-1108`, R102; condensed, the comments give the source
lines):

```rust
let optimize = tcx.sess.opts.optimize != OptLevel::No;            // :1065
// &T
let frozen = optimize && ty.is_freeze(tcx, typing_env);          // :1078
kind = PointerKind::SharedRef { frozen };
size = layout.size * frozen as _;                                // :1092
// &mut T
let unpin = optimize && ty.is_unpin(tcx, typing_env)
    && ty.is_unsafe_unpin(tcx, typing_env);                       // :1095-1097
kind = PointerKind::MutableRef { unpin };
size = layout.size * unpin as _;                                 // :1102
```

The comment at `:1081-1092` gives the reason for the zero size: "`PointeeInfo::size` is
defined to allow adding spurious reads. Adding spurious reads is only valid for `&Freeze`
and `&mut Unpin` references, as otherwise the spurious read can invalidate aliasing
references." R98 computes the same values (`layout.rs:1007-1037`) with an older rationale
("not necessarily dereferenceable for the entire duration of the function"). Unions are
skipped ("We're not interested in any unions", `:1170-1175`), so nothing is found inside
`MaybeUninit`.

**Step 2 — `ArgAttributes`** (`compiler/rustc_ty_utils/src/abi.rs:318-414`, R102,
`arg_attrs_for_rust_scalar`). In order: `NoUndef` unless `scalar.is_uninit_valid()`; stop
unless the scalar is an initialized pointer; `NonNull` if `!valid_range.contains(0)`; then,
if a `PointeeInfo` was found, `pointee_align` when it exceeds 1 and `pointee_size`; and, only
if `pointee.safe` is `Some(kind)` and this is an argument: `NoAlias` for `frozen` / `unpin`,
`NoFree` for `frozen` / `unpin` (never for `Box`), `ReadOnly` and `CapturesReadOnly` for
`SharedRef { frozen: true }`. Because `NonNull` and `NoUndef` come from the scalar and not
from `PointeeInfo`, the maybe-dangling patch cannot remove them. `Scalar::is_uninit_valid`
is `true` exactly for `Scalar::Union` (`compiler/rustc_abi/src/lib.rs:1668-1675`), and a
union layout has `largest_niche: None` (`compiler/rustc_abi/src/layout.rs:404-525`).
R98's function (`:322-418`) differs for pointer arguments at default flags only in lacking
`NoFree`; it additionally consults `-Zmutable-noalias`, which defaults to on there
(`compiler/rustc_session/src/options.rs:2476`, R98) and no longer exists at R102.
`is_unsafe_unpin` "Checks whether values of this type `T` implement the `UnsafeUnpin`
trait" (`compiler/rustc_middle/src/ty/util.rs:1223-1226`, R102).

**Step 3 — LLVM attributes** (`compiler/rustc_codegen_llvm/src/abi.rs:39-116`, R102,
`get_attrs`). ABI-affecting attributes, `align` and extension are always emitted. Under
"Only apply remaining attributes when optimizing" (`:80-81`; the two attribute pushes are
abbreviated to comments):

```rust
let deref = this.pointee_size.bytes();
// Prior to <https://github.com/llvm/llvm-project/pull/204795> dereferenceable in LLVM
// implied nofree, so only emit dereferenceable on older versions of LLVM if nofree
// is also set.
if deref != 0 && (llvm_version >= (23, 0, 0) || regular.contains(ArgAttribute::NoFree)) {
    if regular.contains(ArgAttribute::NonNull) { /* dereferenceable(deref) */ }
    else { /* dereferenceable_or_null(deref) */ }
    regular -= ArgAttribute::NonNull;
}
```

followed by `noalias`, `nonnull`, `readonly`, `noundef`, `writable`, `nofree` and one
`captures(...)` form. This explains two details of the matrix: a row with
`dereferenceable(8)` never shows `nonnull` (it is subsumed and removed), and a row without
a pointee size shows `nonnull` explicitly. `compiler/rustc_codegen_llvm/src/attributes.rs:29-39`
only applies the resulting list to a function or call site; it holds no mapping logic.
R98's `get_attrs` (`:38-107`) has five optimisation attributes instead of six (no `NoFree`)
and the unconditional test `if deref != 0`.

**Why `-C opt-level=0` leaves only `align`.** Two independent gates: `optimize` is false in
step 1, so `frozen`/`unpin` are false and `size` is zero; and step 3 skips every
optimisation attribute. `align` is emitted before the gate. `MaybeUninit<&u64>` has no
`PointeeInfo` at all and so not even `align`.

**What the attributes mean** (normative; LLVM 23 `llvm/docs/LangRef.md`, LLVM 22
`llvm/docs/LangRef.rst`, at the submodule commits above):

| Attribute | LLVM 23 text | Difference in LLVM 22 |
| :-- | :-- | :-- |
| `dereferenceable(<n>)` (`:1622-1640`) | "can be loaded from speculatively without a risk of trapping"; implies `nonnull` and `noundef`; "only implies dereferenceability at the point of the attribute (i.e. on function entry for arguments …). The underlying object may still get freed after that point. Other attributes such as `nofree` can be used to exclude frees." | The last paragraph is absent (`:1565-1580`). |
| `nofree` (`:1574-1588`) | "a pointer based on this argument cannot be freed during the execution of the function … This includes frees of the pointer on other threads if the free *happens-before* the function return. Notably, it is still possible to free the underlying object through a pointer that is not based on the argument." | "This indicates that the callee does not free the pointer argument." (`:1533-1535`) |
| `noalias` (`:1512-1523`) | Locations accessed via pointers based on the argument "are not also accessed, during the execution of the function, via pointer values not *based* on the argument"; "only holds for memory locations that are *modified*". | Same (`:1471-1482`). |
| `readonly` (`:1797-1803`) | "the function does not write through this pointer argument". | Same (`:1750-1756`). |
| `nonnull` (`:1609-1618`), `noundef` (`:1699-1706`) | Null gives poison; with `noundef` it is undefined behaviour. | Same. |
| `captures(address, read_provenance)` (`:1538-1572`) | "Both address and provenance captured, but only for read-only access." | Present (`:1497`). |

### The nine-row matrix

Basis: execution at R98 (`support/probe_result_…llvm_22_1_6.json`, `part_a`); execution
(retained record) at R102; derived from the three steps above for both.

`-C opt-level=2 -C no-prepopulate-passes`, one argument `%x`:

| # | Rust type | R102 / LLVM 23.1.5 (retained record) | R98 / LLVM 22.1.6 (re-run) | `Option<T>` |
| :-- | :-- | :-- | :-- | :-- |
| 1 | `&u64` | `ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(8)` | same without `nofree` | 8 |
| 2 | `&mut u64` | `ptr noalias nofree noundef align 8 dereferenceable(8)` | same without `nofree` | 8 |
| 3 | `&UnsafeCell<u64>` | `ptr noundef nonnull align 8` | identical | 8 |
| 4 | `&mut UnsafeCell<u64>` | `ptr noalias nofree noundef align 8 dereferenceable(8)` | same without `nofree` | 8 |
| 5 | `&mut PinnedU64` | `ptr noundef nonnull align 8` | identical | 8 |
| 6 | `PlainWrap<&u64>` | as row 1 | as row 1 at R98 | 8 |
| 7 | `ManuallyDrop<&u64>` | `ptr noundef nonnull align 8` | identical | 8 |
| 8 | `MaybeDangling<&u64>` | `ptr noundef nonnull align 8` | identical | 8 |
| 9 | `MaybeUninit<&u64>` | `ptr` | identical | 16 |

`PinnedU64` is `struct PinnedU64 { v: u64, _pin: PhantomPinned }` (no `UnsafeCell`, so
`Freeze`; `!Unpin`). `PlainWrap` is `#[repr(transparent)] struct PlainWrap<T>(T)`, not a
lang item. At `-C opt-level=0` rows 1-8 are `ptr align 8` and row 9 is `ptr` on both
toolchains. `size_of::<T>()` is 8 for all nine types (R98); `size_of::<Option<T>>()` is
`[8, 8, 8, 8, 8, 8, 8, 8, 16]` on both.

Reading the rows against the source:

- Row 3 versus row 1: `!Freeze` makes `frozen` false, which removes `noalias`, `nofree`,
  `readonly`, `captures` *and* (through `size = 0`) `dereferenceable`; `nonnull` reappears
  because nothing subsumes it.
- Row 4: under `&mut` only `Unpin`/`UnsafeUnpin` are consulted, so `UnsafeCell<u64>` behaves
  like `u64`.
- Row 5: a type with no `UnsafeCell` at all still loses `noalias`, `nofree` and
  `dereferenceable` under `&mut` once it is `!Unpin`.
- Row 6: a user transparent wrapper is invisible to all three steps.
- Rows 7-8: `safe: None` removes the reference-kind attributes, `size: 0` removes
  `dereferenceable`, `align` and the scalar's `noundef`/`nonnull` remain. Upstream pins the
  same strings in `tests/codegen-llvm/maybe_dangling_refs.rs` at R102 (for example
  `define … noundef nonnull align 4 ptr @j(ptr noundef nonnull align 4 %x)` for
  `MaybeDangling<&u32>`, and `@f2` for `ManuallyDrop<Box<u8>>`).
- Row 9: the union scalar allows uninitialized bytes, so `arg_attrs_for_rust_scalar`
  returns before any pointer attribute, and there is no niche.
- The `nofree` column difference is exactly the source difference: R98 has no
  `ArgAttribute::NoFree`.

### What the interpreter checks inside the wrappers

Basis: source (R102 `validity.rs`) + execution at R98 (`part_b`) + execution (retained
record) at R102 for the five programs marked †.

`ValidityVisitor::check_safe_pointer` (`validity.rs:561-722`, R102) does, in order: if
`!self.may_dangle`, `check_ptr_access` for the pointee size (errors become "encountered a
dangling reference (use-after-free)" and similar) and, when provenance is being reset, the
machine's `retag_ptr_value`; otherwise only an address-space-end overflow check
(`:601-676`). Then, unconditionally: the null check ("Make sure this is non-null. This is
obviously needed when `may_dangle` is set", `:685-698`), the inhabitedness check, and the
alignment check (`:709-721`). Recursion through the reference is skipped when
`may_dangle` (`:723-726`).

| Program (value stored, then moved once) | R98 Miri | Message |
| :-- | :-- | :-- |
| `&u64` to a freed `Box<u64>` | UB | constructing invalid value of type `&u64`: encountered a dangling reference (use-after-free) |
| `PlainWrap<&u64>`, freed † | UB | … of type `PlainWrap<&u64>`: at .0, encountered a dangling reference (use-after-free) |
| `ManuallyDrop<&u64>`, freed † | accepted | — |
| `MaybeDangling<&u64>`, freed † | accepted | — |
| `MaybeDangling<&u64>`, freed, then `.into_inner()` | UB | … of type `&u64`: encountered a dangling reference (use-after-free), raised inside `into_inner` |
| `MaybeDangling<&u64>` at address `0x1` † | UB | … of type `std::mem::MaybeDangling<&u64>`: encountered an unaligned reference (required 8 byte alignment but found 1) |
| `MaybeDangling<&u64>` null † | UB | … of type `std::mem::MaybeDangling<&u64>`: encountered a null reference |
| `ManuallyDrop<&u64>` null | UB | … of type `std::mem::ManuallyDrop<&u64>`: at .value, encountered a null reference |
| `MaybeUninit<&u64>` null, and uninitialized | accepted | — |

The retained R102 record agrees on the five † verdicts; its messages for the two
`MaybeDangling` failures carry a path ("at .0, encountered …") that the R98 messages lack.

**Retag suppression.** In the interpreter, retagging of references found in a value is part
of validation (`validity.rs:623-644`, and the comment "we do retagging during validation",
`:1647-1648`), inside the `!self.may_dangle` branch. So the same flag that waives
dereferenceability also suppresses the retag. This is visible at R98 in the upstream
reproducer described in the SROA subsection: a `ManuallyDrop<&mut u8>` whose target was
written through a raw pointer can be moved without a Stacked Borrows error at Miri
defaults, and the error ("trying to retag from <325> for Unique permission … that tag does
not exist in the borrow stack") appears only once SROA has hoisted the `&mut u8` out of the
wrapper. The second suppression site, `RetagPlan::build` in the codegen backend, is
"Experimental support for emitting retags as function calls in generated code"
(`retag.rs:1-6`, flag `codegen_emit_retag` at `compiler/rustc_session/src/options.rs:2475-2476`);
it was read, not executed.

### SROA: behaviour with and without the exclusion

Basis: source (both revisions) + execution at R98 (`part_c`, `part_d`) + execution
(retained record) at R102 + upstream issue and regression test.

**Mechanism (both revisions).** `ScalarReplacementOfAggregates` runs at MIR optimisation
level 2 and above. A local is flattened unless it "escapes": it is an argument or the
return place, its type is excluded, or it is used other than through a field projection or
as the destination of an aggregate or plain `Use` assignment (`sroa.rs:56-136`, R102). When
the destination of `a = move? place` is flattened, the assignment is replaced by one
assignment per field, `a_0 = move? place.0; …` (`:379-417`). The pass loops until no local
is flattened, so one wrapper layer is peeled per iteration. The consequence that matters
here: a whole-value copy *at the wrapper type* becomes a copy *at the field type*.

**The exclusion (R102 only).** The diff of `sroa.rs` between R98 and R102 consists of
bit-set plumbing, the pass-policy interface, a generalisation of the SIMD/`DynMetadata`
test into `!def.can_project_fields(tcx)`, and this addition (commit `26988e752251694e4f68527417aa418d5ff845e3`,
PR #164568, merged 2026-10-20 as `cd2a75d9d58d7bd7b59cde543684fc83c3e785d2`, "Fixes
rust-lang/rust#164176"):

```rust
// Types like MaybeDangling relax validity requirements of inner references.
if ty.is_like_maybe_dangling() {
    return true;
}
```

Its commit message: "References inside a MaybeDangling doesn't have to satisfy any
memory-depended validity properties. SROA cannot rewrite operations in terms of an inner
type, which might require it." The exclusion is on the type of the *local*. A local of a
plain struct that has a maybe-dangling field is still flattened, but the fragment created
for that field is itself a local of the wrapper type and is excluded on the next iteration,
so the inner reference never becomes a bare local.

**Observed MIR after the pass.**

| Function | R98 (re-run) | R102 (retained record / upstream test) |
| :-- | :-- | :-- |
| `let w = PlainWrap(RefPair(r, k + 1)); let RefPair(_a, b) = w.0;` | flattened: `debug (((w: PlainWrap<RefPair<'_>>).0: RefPair<'_>).0: &u64) => _11` | flattened |
| same with `MaybeDangling::new` / `.into_inner()` | **flattened**: `debug (((w: MaybeDangling<RefPair<'_>>).0: RefPair<'_>).0: &u64) => _18` | kept: `debug w => _3`, `_3 = MaybeDangling::<RefPair<'_>>(copy _4)`, `_9 = move _3` |
| same with `ManuallyDrop::new` / `ManuallyDrop::into_inner` | kept, but only because R98's `into_inner` takes `&raw const` of the local | kept: `_3 = ManuallyDrop::<RefPair<'_>> { value: copy _4 }`, `_9 = move _3` |
| `fn f(a: S<&u64>) { let b = a; }` | `_3 = copy (_1.0: &u64)` | upstream test expects the field copy |
| `fn f(a: MaybeDangling<&u64>) { let b = a; }` | **`_3 = copy (_1.0: &u64)`** | upstream test expects `[[B]] = copy [[A]]` |
| `fn f(a: ManuallyDrop<&u64>) { let b = a; }` | **`_4 = copy ((_1.0: std::mem::MaybeDangling<&u64>).0: &u64)`** | upstream test expects `[[B]] = move [[A]]` |

The last three rows are the shape of the regression test added by the fix,
`tests/mir-opt/sroa/dangling.rs`, instantiated here at `&u64`.

**The hazard, executed at R98.** The program

```rust
struct RefPair<'a>(&'a u64, u64);
struct Outer<'a> { md: MaybeDangling<RefPair<'a>>, tag: u64 }
fn victim() -> u64 {
    let b = Box::new(41u64);
    let r: &'static u64 = unsafe { &*(&raw const *b) };
    let o = Outer { md: MaybeDangling::new(RefPair(r, 7)), tag: 1 };
    drop(b);        // the reference stored inside `o.md` dangles from here on
    let o2 = o;     // whole-value move; the only reference sits under MaybeDangling
    o2.tag
}
```

never copies the reference at a type that requires it to be dereferenceable after the
`drop`. Results under Miri:

| Configuration | Exit | Diagnostic |
| :-- | :-- | :-- |
| Miri defaults (`-Zmir-opt-level=0`) | 0 | none |
| `-Zmir-opt-level=2` | 0 | none |
| `-Zmir-opt-level=2` with the eight clean-up passes after SROA disabled | 1 | Undefined Behavior: constructing invalid value of type `&u64`: encountered a dangling reference (use-after-free), located at the `o` of `let o2 = o;` (recorded as `sroa_hazard_outer.rs:18:14`) |
| the previous line plus `-Zmir-enable-passes=-ScalarReplacementOfAggregates` | 0 | none |
| control: the same program with `PlainWrap` instead of `MaybeDangling`, Miri defaults | 1 | … of type `Outer<'_>`: at .md.0.0, encountered a dangling reference (use-after-free) |

The MIR that Miri interpreted in the third configuration shows what happened: before the
pass, `_5 = Outer::<'_> { md: move _6, tag: const 1_u64 }` and, after the `drop`,
`_11 = move _5`; after the pass, `_22 = move ((_6.0: RefPair<'_>).0: &u64)` before the
`drop` and `_20 = move _22` after it, with
`debug ((((o2: Outer<'_>).0: std::mem::MaybeDangling<RefPair<'_>>).0: RefPair<'_>).0: &u64) => _20`.
The disabled passes are `SimplifyLocals-before-const-prop`, `DeadStoreElimination-initial`,
`SimplifyLocals-after-value-numbering`, `DeadStoreElimination-final`, `SimplifyLocals-final`,
`CopyProp`, `DestinationPropagation` and `SingleUseConsts`; with them enabled the hoisted
copy is dead and is deleted before interpretation, which is why the second configuration is
clean. The control row shows that `MaybeDangling` is what makes the source program
defined.

The reproducer from upstream issue #164176 (a `ManuallyDrop<&mut u8>` that is moved after
its target was written through a raw pointer) behaves at R98 as the issue reports: exit 0
at Miri defaults and with `-Zmir-enable-passes=+Inline`, exit 1 with
`-Zmir-enable-passes=+Inline,+ScalarReplacementOfAggregates` (Stacked Borrows retag error
quoted above). The issue names PR #150446 as the change that made such programs defined:
"We changed the semantics to permit some programs that were previously forbidden and MIR
opts still assume those programs are forbidden."

Derived: R98 lies inside the interval in which the interpreter semantics existed (from
merge `8fc4e47ee1a36862be751ef148618659ba9c7999`, 2026-03-09) and the exclusion did not
(until merge `cd2a75d9d58d7bd7b59cde543684fc83c3e785d2`, 2026-10-20). Other revisions in
that interval were not run.

### The Lean model and what it proves

Basis: mechanised (derived); `support/MaybeDanglingAttrsAndSroaSoundness.lean`, checked by
Lean 4.34.1 with `-DwarningAsError=true`; 58 theorems; `#print axioms` on the 32 headline
theorems reports no axioms for 16 and `[propext]` for 16.

Definitions (namespace `MaybeDanglingModel`):

- `Ty` is `ref (m : Mutbl) (t : Pointee) | wrap (w : Wrapper) (inner : Ty)` with pointees
  `u64`, `unsafeCellU64`, `pinnedU64` and wrappers `plain`, `manuallyDrop`, `maybeDangling`,
  `coroutine`, `maybeUninit`. `Wrapper.isLikeMaybeDangling` is true for the middle three.
- `pointeeInfoAt`, `scalarOf`, `argAttrs`, `lowerPost` (R102 `get_attrs`, parameterised by
  `optimize` and `llvmGe23`) and `lowerPre` (R98 `get_attrs`) transcribe the three steps;
  `llvmParamAttrs` and `llvmParamAttrsPre` compose them.
- `validSlot h mayDangle ty s` is the validity invariant over a heap of live or freed
  allocations (`HeapState`) and a slot that is uninitialized or a pointer with an address
  and optional provenance: a reference must be non-null and 8-aligned, and dereferenceable
  unless `mayDangle`; a non-union wrapper recurses with
  `mayDangle || isLikeMaybeDangling`; a union accepts everything.
- `Level` is the four-level chain `fullRef frozen unpin`, `mayDangleAlignedNonNull align`,
  `rawAligned align`, `uninitOrArbitrary`, with `Level.admits`.
- `step`/`run` execute read, write and free events by the callee or by pointers not derived
  from the argument on a state `(live, other, val)`; a callee read turns an
  exclusive foreign alias from `uniqueActive` into `uniqueFrozen`, after which that alias
  can no longer write. `admissibleInit` gives, per `RefKind`, the states in which a call
  may start.
- `sroaStmt excluded` rewrites `copyAt (wrap w inner)` to `copyAt inner` unless
  `excluded w`; `exec` runs `free`/`copyAt` lists; `sroaExcludedPost` is
  `isUnion || isLikeMaybeDangling`, `sroaExcludedPre` is `isUnion`.

Theorems:

| Theorem | Statement in words |
| :-- | :-- |
| `matrix_post_llvm23_opt2`, `matrix_pre_opt2`, `matrix_opt0`, `matrix_post_llvm22_opt2` | The transcribed lowering yields the nine R102 rows, the nine R98 rows, the `-C opt-level=0` rows, and (R102 compiler on an LLVM older than 23) the R102 rows again. |
| `pre_eq_post_erase_nofree` | For every `ArgAttrs`, hence every type: R98 `get_attrs` equals R102 `get_attrs` on LLVM 23 with `nofree` erased. |
| `validSlot_eq_level`, `levels_of_rows`, `level_chain`, `level_chain_strict` | `levelOf` characterises validity exactly for every type; rows 1-6 are `fullRef`, rows 7-8 `mayDangleAlignedNonNull 8`, row 9 `uninitOrArbitrary`; each level admits the previous one; a freed allocation, null and an uninitialized slot separate them. |
| `lowering_sound_entry` | For every type, heap, optimisation level, LLVM generation and both compiler revisions: a value valid at the type satisfies every asserted `noundef`, `nonnull`, `align`, `dereferenceable`, `dereferenceable_or_null`. |
| `attrs_only_for_strong_kinds`, `lowering_sound_call` | For every type: `noalias`, `nofree` and `dereferenceable` are emitted only when the kind read off the type is `&Freeze` or `&mut Unpin`, and `readonly` only for `&Freeze`; and for those kinds a speculative read at entry never changes the outcome, no defined execution contains a foreign write or a free, the pointee is live at the end, and under `readonly` the value is unchanged. |
| `option_sizes_of_rows`, `niche_preserved`, `niche_lost_under_union`, `null_not_valid_of_niche`, `niche_roundtrip`, `niche_ambiguous_for_maybe_uninit`, `option_maybe_dangling_is_rawAligned` | `Option` sizes are `[8 ×8, 16]`; every non-union wrapper keeps the niche and a union removes it; where the lowering reports a niche, null is invalid on every heap in every context, so the 8-byte encoding round-trips; null is a valid `MaybeUninit<&u64>` and collides with `None`; `Option<MaybeDangling<&u64>>` is exactly the `rawAligned 8` level. |
| `sroaValid_iff`, `pre_predicate_admits_unsound_peel`, `sroa_post_preserves` | Peeling wrapper `w` off a typed copy preserves definedness on all heaps and values iff `sroaExcludedPost w = false`; the R98 predicate admits an unsound peel for each maybe-dangling-like family; with the R102 predicate the rewrite preserves every defined execution of every statement list. |
| `ce1_sroa_flattening_maybe_dangling_introduces_dangling_ref_ub` | Copy, free, copy at `MaybeDangling<&u64>` (and `ManuallyDrop`, coroutine) is defined; after the R98-predicate rewrite it is undefined; the R102 predicate leaves it unchanged; the hoisted `&u64` carries `dereferenceable(8)`, false on the freed heap. |
| `ce2_dereferenceable_on_shared_unsafecell_or_pinned_mut_unsound`, `ce2_maybe_dangling_spurious_read_unsound` | Rows 3 and 5 get none of the strong attributes, and each would be unsound for the kind: a speculative entry read makes a defined execution undefined; a defined execution frees the pointee; a defined execution has a foreign write between two callee reads. Likewise a speculative read through an already-dangling `MaybeDangling<&u64>`. |
| `ce3_null_or_unaligned_inside_maybe_dangling_violates_retained_scalar_validity` | On every heap and in every context, null and address 1 are invalid `MaybeDangling<&u64>`/`ManuallyDrop<&u64>` values and falsify the emitted `nonnull`/`align 8`; address 8 with no allocation is valid. |

How the model and the execution meet: `ce1` is the abstract form of the R98 hazard run
(defined source, undefined after the rewrite, defined again with the later predicate);
`ce3` and the niche theorems match the Miri null/misaligned verdicts and the measured
`Option` sizes; the matrix theorems reproduce the two observed attribute tables.

### Relation to `joshlf/anneal` at `c131b320`

Basis: source.

- The trusted MIR type language `Trusted.MirAst.MirTy`
  (`trusted/lean/Trusted/MirAst.lean:312-321`) has `bool`, `int`, `unit`, `never`, `enum`,
  `tuple`, `ref`, `rawPtr` and `unsupported`. Its documentation (`:308-311`) maps
  non-fieldless-enum `Adt`, `Closure`, `CoroutineClosure`, `Coroutine` and others to
  `.unsupported`, on which that semantics fails closed with `FaultKind.unsupported`. So
  `MaybeDangling<T>`, `ManuallyDrop<T>` and coroutines are outside the trusted semantics at
  this commit; none of the SROA or attribute questions above can arise inside it.
- The vendored interpreter model does represent the notion, as an input fact rather than a
  definition: `vendor/lean-miri/Miri/Input/CompilerFactAdapters.lean:176-179` builds
  `.aggregate (← CompilerFacts.boolean context id "is_like_maybe_dangling") …` for ADTs,
  tuples, closures, coroutines and coroutine-closures, and
  `vendor/lean-miri/Miri/Input/Decoder.lean:806-809` lists `is_like_maybe_dangling`,
  `is_freeze`, `is_unpin`, `is_unsafe_unpin` among the compiler-fact boolean queries.
  `vendor/lean-miri/Miri/Memory/Validity.lean:627-641` (`withMaybeDangling`) and
  `vendor/lean-miri/Miri/Interpreter/ValidityVisitor.lean:205-230, 409-411` mirror the R102
  control flow: access check and retag only when `!mayDangle`, null and alignment checks
  always.
- Derived consequence: a consumer that takes `is_like_maybe_dangling` as a compiler fact
  inherits the revision dependence documented here. A fact file produced by an R98-era
  compiler cannot carry it (the query does not exist there), and the set of closure-like
  types it covers changed on 2026-09-05, 2026-09-24 and 2026-09-25.
- The Lean file in this package imports nothing from that repository and is not checked
  against it.

## Boundaries

**Not examined.**

- R102 was not executed for this report. Every R102 execution claim rests on the retained
  record plus source derivation.
- `Box<T>` under the wrappers (upstream's codegen test covers it; this probe does not),
  wide pointers, return-position attributes, scalar pairs, indirect arguments, other
  targets and pointer widths, non-LLVM backends.
- The codegen retag plan (`-Zcodegen-emit-retag`) and Tree Borrows.
- Coroutines on the execution side: no probe constructs a coroutine holding a dangling
  reference; the coroutine family is covered by source reading and by the model only. In
  rustc a coroutine's saved locals are additionally laid out as `MaybeUninit<T>`
  (`compiler/rustc_ty_utils/src/layout.rs:567-576`, R102) while its upvars are not; the
  model's one-field `coroutine` wrapper does not reproduce that structure.
- Revisions between R98 and R102 other than through the cited commits.
- What LLVM passes do with the attributes; the IR is taken before optimisation
  (`-C no-prepopulate-passes`).

**Unknown.**

- Whether the R98 SROA behaviour can produce a wrong *machine-code* result. The hoisted
  copy in the hazard program is dead and is removed by the default pipeline; the
  demonstration needs the clean-up passes disabled. No end-to-end miscompilation was
  constructed or found.
- The acquisition date and host of the retained R102 record.

**Known not to apply.**

- `MaybeDangling` does not waive non-nullness or alignment (source, Miri, `ce3`), and does
  not make `into_inner`/`as_ref` on a dangling value defined (Miri).
- The R102 exclusion does not stop SROA from flattening a plain struct that *contains* a
  maybe-dangling field; it stops the flattening at the field.
- `&mut UnsafeCell<T>` is not weakened by interior mutability (row 4).
- At R102 closures and coroutine-closures are not maybe-dangling-like, although they were
  for parts of September 2026.

**Unsupported.**

- `MaybeDangling` is unstable (`#![feature(maybe_dangling)]`); none of this is a stable
  language guarantee. The upstream PR that extended the semantics to closure-like types
  says it "just implements the semantics without updating any docs".

**Stronger conclusions the evidence does not establish.**

- That the Lean theorems are about rustc or LLVM. They are about transcriptions restricted
  to a small type family. `captures` has no semantics in the model; the aliasing machine is
  not Stacked or Tree Borrows; LLVM 23's `nofree` (frees through based-on pointers) is
  weaker than the model's "no free at all", so the model proves more than LLVM assumes.
- That the nine rows hold on other targets or for other pointee sizes and alignments.
- That `sroa_post_preserves` covers the real pass. It covers one rewrite (a whole-value copy
  re-typed to the field) on one observed value.

## Evidence

All GitHub commit identifiers were read from the GitHub REST API on 2026-11-21. Source line
numbers refer to the files at the stated commits.

**`rust-lang/rust` at R102 (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, committed 2026-11-11).**

- `compiler/rustc_middle/src/ty/sty.rs:2167-2181` — `is_like_maybe_dangling`.
- `compiler/rustc_middle/src/ty/adt.rs:53-71, 399-409` — `AdtFlags`, lang-item mapping.
- `compiler/rustc_middle/src/ty/layout.rs:1054-1231` — `ty_and_layout_pointee_info_at`
  (`:1062-1065` optimize; `:1071-1108` references; `:1170-1175` unions; `:1204-1217` patch).
- `compiler/rustc_abi/src/lib.rs:2349-2381` (`PointerKind`, `PointeeInfo`), `:1668-1675`
  (`is_uninit_valid`); `compiler/rustc_abi/src/layout.rs:404-525` (`layout_of_union`).
- `compiler/rustc_ty_utils/src/abi.rs:318-414` — `arg_attrs_for_rust_scalar`.
- `compiler/rustc_target/src/callconv/mod.rs:131-149, 166-174` — `ArgAttribute`,
  `ArgAttributes`.
- `compiler/rustc_codegen_llvm/src/abi.rs:39-116` — `get_attrs`;
  `compiler/rustc_codegen_llvm/src/attributes.rs:29-39`.
- `compiler/rustc_const_eval/src/interpret/validity.rs:367-368, 561-726, 1543-1556,
  1647-1648, 1719-1730`.
- `compiler/rustc_codegen_ssa/src/mir/retag.rs:1-6, 67-94`;
  `compiler/rustc_session/src/options.rs:2475-2476`.
- `compiler/rustc_mir_transform/src/sroa.rs:17-20, 56-136, 379-417`.
- `compiler/rustc_middle/src/ty/util.rs:1223-1226` (`is_unsafe_unpin`).
- `library/core/src/mem/maybe_dangling.rs:50-73`, `manually_drop.rs:152-158`,
  `maybe_uninit.rs:351-358`; `tests/codegen-llvm/maybe_dangling_refs.rs:1-52`.
- Identifier count: the string `is_like_maybe_dangling` occurs 6 times in the source
  archive of this commit (submodules excluded).

**`rust-lang/rust` at R98 (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, committed 2026-05-31).**

- `compiler/rustc_middle/src/ty/layout.rs:990-1073`; `adt.rs:66-67, 380-382, 510-514`.
- `compiler/rustc_const_eval/src/interpret/validity.rs:416-417, 1549-1556`.
- `compiler/rustc_mir_transform/src/sroa.rs:65-87` (no maybe-dangling test);
  `compiler/rustc_codegen_llvm/src/abi.rs:38-107`; `compiler/rustc_ty_utils/src/abi.rs:322-418`;
  `compiler/rustc_session/src/options.rs:2476` (`mutable_noalias`, default `true`).
- `library/core/src/mem/manually_drop.rs:157-163`, `maybe_dangling.rs:70-74`.
- `compiler/rustc_codegen_ssa/src/mir/retag.rs` is absent.

**Upstream history (`rust-lang/rust`).** PR #149775 (merge
`08509492139968a96a005ba811a995e2f1d6a2ac`; commit `722e3102a22c529bade40c61f63bb3d88845360a`);
PR #150447 (merge `64b72a1fa5449d928d5f553b01a596b78ee255d2`; commits
`7cefcb41ff7e27f3619bfecff429f72b5f3bface`, `8aafa5350435352a227c266c3d757e5235d96a98`);
PR #150446 (merge `8fc4e47ee1a36862be751ef148618659ba9c7999`);
PR #160745 (merge `015777700540b3876f2b5b513b9e79160f83f4dd`; commits
`e7c3734a6a8d0e1f0e9de055c91ea008372beaf2`, `b7e5447e85cc1869c7dd26d14310cd351d3f8cf0`);
PR #162361 (merge `ad2e756c7093149e25f67a747e579a49b7e6976e`; commit
`8201a7b4bd655461299236b4e7b815411f1a42e5`); PR #163308 (merge
`02bc9556f4176a80df3bf9971edd50afa270adaa`; commit `4b538231e35e6edbc13ed012dd788a8f432d73fd`);
issue #164176 (opened 2026-10-11) and PR #164568 (merge
`cd2a75d9d58d7bd7b59cde543684fc83c3e785d2`; commit `26988e752251694e4f68527417aa418d5ff845e3`,
which adds `tests/mir-opt/sroa/dangling.rs`). PR titles, bodies, merge dates and the
commit-to-PR associations were read from the same API.

**LLVM LangRef.** `rust-lang/llvm-project` `0a5579eb649d3634a9c30ac873300cc2944fa070`,
`llvm/docs/LangRef.md:1512-1523, 1538-1572, 1574-1588, 1609-1618, 1622-1640, 1699-1706,
1797-1803`; `rust-lang/llvm-project` `08c84e69a84d95936296dfcab0e38b34100725d5`,
`llvm/docs/LangRef.rst:1471-1482, 1497, 1533-1535, 1554-1562, 1565-1580, 1635, 1750-1756`.

**`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (committed 2026-11-19).**
`trusted/lean/Trusted/MirAst.lean:308-321`;
`vendor/lean-miri/Miri/Input/CompilerFactAdapters.lean:176-179`;
`vendor/lean-miri/Miri/Input/Decoder.lean:806-809`;
`vendor/lean-miri/Miri/Memory/Validity.lean:627-641`;
`vendor/lean-miri/Miri/Interpreter/ValidityVisitor.lean:205-230, 409-411`.

**Execution, re-run on 2026-11-21.** Toolchain: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`,
`LLVM version: 22.1.6`, host `x86_64-unknown-linux-gnu`; Miri reporting the same commit;
Miri sysroot built with `cargo miri setup`.

- `support/probe_maybe_dangling_llvm_attrs_and_sroa.py` — the probe. All Rust inputs are
  embedded in it; it writes them to a temporary directory, runs the tools and emits JSON
  with host paths replaced by placeholders.
- `support/probe_result_rustc_1_98_0_nightly_14210df0e_llvm_22_1_6.json` — its output:
  `part_a` (signatures at both optimisation levels, sizes), `part_b` (nine Miri programs),
  `part_c` (MIR before and after SROA for six functions), `part_d` (hazard runs and the MIR
  Miri interpreted), `discriminators`. Exit status 0; the list
  `toolchain_independent_expectation_failures` is empty.

**Execution, retained record (not re-run).**
`support/retained_record_rustc_1_102_0_nightly_3ef0c22cd_llvm_23_1_5.json`:
`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, `LLVM version: 23.1.5`; nine signatures at
both optimisation levels, `OPT_SIZES=[8, 8, 8, 8, 8, 8, 8, 8, 16]`, five Miri verdicts,
three post-SROA MIR bodies. Its `provenance` object states the two edits made to it.
Internal consistency with R102 source that supports its origin: the MIR shows
`ManuallyDrop::<RefPair<'_>> { value: copy _4 }` (the R102 one-level definition, not the
R98 nested one) and `nofree` on exactly the rows where R102 sets `NoFree`.

**Mechanisation.** `support/MaybeDanglingAttrsAndSroaSoundness.lean` (no imports) and
`support/lean_check_output.txt` (the checker's version line, the command, the
`#print axioms` output and exit status 0). Checker: Lean 4.34.1,
`leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52`. The file contains no
`sorry`, no `native_decide`, no `bv_decide`, no `omega`, no `partial def`, no `axiom`.

## Revalidation

Cheapest first.

1. **Does the predicate still name the same types and have the same uses?** In a checkout
   of the revision of interest:
   `grep -rn "is_like_maybe_dangling" compiler/ src/tools/miri/src/`. Expect one
   definition in `rustc_middle/src/ty/sty.rs` and uses in `layout.rs`, `validity.rs`,
   `retag.rs` and `sroa.rs`. A new arm in the definition changes every finding that
   mentions "three families"; a new use is a new consumer; a missing `sroa.rs` use
   reopens the hazard.
2. **Do the nine rows, the validity verdicts and the SROA behaviour still hold?** Run the
   probe on the toolchain of interest:

   ```sh
   MIRI_SYSROOT=/tmp/miri-sysroot cargo miri setup
   python3 support/probe_maybe_dangling_llvm_attrs_and_sroa.py \
       --rustc "$(rustc --print sysroot)/bin/rustc" \
       --miri "$(rustc --print sysroot)/bin/miri" --miri-sysroot /tmp/miri-sysroot \
       --out /tmp/probe.json
   ```

   Exit status 0 means the attribute matrix (ignoring `nofree`), the `-C opt-level=0` rows,
   the `Option` sizes and the nine Miri verdicts match. Then read `discriminators`:
   `nofree_emitted_on` (empty at R98; expected `sig_1, sig_2, sig_4, sig_6` on a compiler
   with `NoFree`), `sroa_rewrites_whole_copy_of_maybe_dangling_argument` and
   `sroa_rewrites_whole_copy_of_manually_drop_argument` (true at R98; expected false once
   the exclusion is present), and `hazard_outer_ub_only_with_sroa_and_no_cleanup` (true at
   R98; expected false once the exclusion is present, because the third configuration
   should then exit 0). The hazard runs name eight MIR passes; if a later compiler has
   renamed one, check that the hoisted copy is still not being cleaned away before reading
   an exit status of 0 as "fixed". Running it on an R102-or-later toolchain is the missing
   execution this report could not perform; it would turn the retained record into a
   re-run.
3. **Did the attribute mapping change?** Diff three functions against R102:
   `ty_and_layout_pointee_info_at` (`rustc_middle/src/ty/layout.rs`),
   `arg_attrs_for_rust_scalar` (`rustc_ty_utils/src/abi.rs`) and `get_attrs`
   (`rustc_codegen_llvm/src/abi.rs`). If any changed, update the corresponding Lean
   definition (`pointeeInfoAt`, `argAttrs`, `lowerPost`) and the expected rows; the
   `matrix_*` theorems will fail until the transcription and the rows agree again.
4. **Did LLVM's attribute meaning change?** Compare the `dereferenceable(<n>)` and `nofree`
   entries of `llvm/docs/LangRef.md` at the new `src/llvm-project` commit with the text
   quoted above; the version gate in `get_attrs` is the rustc-side dependency.
5. **Re-check the Lean file:**
   `lean -DwarningAsError=true support/MaybeDanglingAttrsAndSroaSoundness.lean` with Lean
   4.34.1; expect exit status 0 and an axiom report mentioning only `propext`. This
   confirms the model, not rustc.

A passing probe says nothing about `Box`, wide pointers, return positions, other targets or
Tree Borrows; those need new probe inputs.
