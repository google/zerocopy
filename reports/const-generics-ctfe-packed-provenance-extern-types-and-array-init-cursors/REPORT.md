# Const Generics, Bit-Packed CTFE Provenance, RFC 1861 Extern Types, and Parametric Array Initialization Cursors

## Summary

Verifying const-generic code, compile-time pointers, FFI opaque handles, and slice/array initialization loops in Rust requires capturing four coupled semantics beyond fixed scalar MIR:

1. **`ty::Const` Stratification and `Rvalue::Repeat` Zero-Length Move Deinitialization (`rustc_type_ir`, `lean-miri` `ExecutionMachine.lean`):** While `Runtime(PostCleanup)` monomorphized bodies instantiate `ConstKind::Value`, polymorphic `core` libraries and unevaluated expressions (`ConstKind::Param`, `ConstKind::Expr`, `AliasConstKind`) carry symbolic `N : usize` across `Rvalue::Repeat(Operand, ty::Const)`. Crucially, `lean-miri`'s `writeRepeat` shows that `[move src; 0]` is **not** a no-op: even when `length == 0`, it forces destination allocation mutability (`getPlaceAllocMut`) and deinitializes a non-ZST moved `src` via `takePendingMoveDeinit`.
2. **64-Bit Bit-Packed `CtfeProvenance` (`rustc_middle`, `lean-miri` `CtfeProvenance.lean`):** CTFE pointers pack a nonzero `62`-bit `AllocId` (`< 2^62`), `shared_ref` (bit `62`), and `immutable` (bit `63`) into `NonZero<u64>` under the invariant `immutable = true → shared_ref = true`, collapsing the high bits to a 3-state permission lattice (`00` unique mutable, `01` shared interior-mutable, `11` immutable frozen). With `OFFSET_IS_ADDR = false` and `WILDCARD = None`, reading pointer bytes as raw integers faults (`ReadPointerAsBytes`).
3. **RFC 1861 `extern type` Thin-Pointer Unknown-Footprint Hazards (`text/1861-extern-types.md`, `core::ptr::metadata`, `lean-miri`):** Under the `Sized: MetaSized: PointeeSized` hierarchy, `extern type` implements `Thin` (`Pointee<Metadata = ()>`) without `MetaSized`. While `lean-miri` `DynamicLayout` returns `none` for `.foreign` (failing `size_of_val`/`align_of_val` cleanly), `TypedRetag.retagPlace` falls back via `.getD` to `place.layout.layout.size` (`0` or static header size), creating a false-disjointness hazard against aliasing pointers inside an opaque C tail unless modeled explicitly as `PtrMeta.externOpaque`.
4. **Parametric `[MaybeUninit<T>; N]` Cursors and Chunked Volatile Erasure (`core::array::try_from_fn`, `zeroize::bulk`):** Length-parametric initialization (`Guard`, `GuardBack`) and chunked zeroization (`as_chunks_mut` + `write_bytes` + `asm!` barrier / `write_volatile`) partition `[0..N)` via symbolic `InitPrefixCursor`/`InitSuffixCursor` and `ChunkPartition` predicates in `prelude` Lean 4 without dependent `Fin N` `HEq` blowup or $N$-step loop unrolling.

## Applicability

This report examines and synthesizes five upstream codebases, three Rust RFCs, four peer-reviewed papers, and one execution probe:

1. **`rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`) & `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** Covers `ConstKind`, `AliasConstKind`, `ty::Expr` (`rustc_type_ir/src/const_kind.rs`, `rustc_middle/src/ty/consts/{mod.rs, kind.rs}`), `Rvalue::Repeat` (`rustc_middle/src/mir/syntax.rs`), `CtfeProvenance` (`rustc_middle/src/mir/interpret/pointer.rs`), `ty::Foreign` layout (`rustc_ty_utils/src/layout.rs`), `Sized`/`MetaSized`/`PointeeSized` (`core/src/marker.rs`), `Pointee`/`Thin`/`DynMetadata` (`core/src/ptr/metadata.rs`), `size_of_val_raw` (`core/src/mem/mod.rs`), `MaybeUninit::{array_assume_init, assume_init_drop}` (`core/src/mem/maybe_uninit.rs`), `array::{from_fn, try_from_fn, Guard, GuardBack}` (`core/src/array/mod.rs`), and RFCs 1861, 2000, and 2580.
2. **`proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Covers `Miri/Memory/CtfeProvenance.lean`, `ExecutionMachine.lean` (`writeRepeat`), `DynamicLayout.lean` (`.foreign`), `Intrinsics.lean` (`size_of_val`/`align_of_val`), and `TypedRetag.lean` (`retagPlace`).
3. **`RustCrypto/utils` (`0feca06cf87e61567033a333feb79ecf3c427fea`):** Covers `zeroize/src/{lib.rs, bulk.rs, barrier.rs}` (`Zeroize`, `Zeroizing`, `MaybeUninit` zeroing, `zeroize_flat_type`, `as_chunks_mut`, `volatile_fill_chunked`, `optimization_barrier`).
4. **Foundational Papers & Anneal Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`):** Grounded in Pointer Provenance (`10.1145/3290380`), RustBelt (`10.1145/3158154`), Tree Borrows (`10.1145/3735592`), and compiler side-effect elimination (`10.1109/EuroSP.2018.00009`). Lean 4 formalizations adhere to `TrustedBoundary.lean:L442–596` and `foundation-lock.json` (`prelude`, 51 locked `Init.*` modules, `{propext, Quot.sound, Classical.choice}`, zero `._unsafe_rec`, Statement-Origin Separation).
5. **Relationship to Existing Corpus Reports:** Extends `rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence` (`GlobalAlloc` taxonomy and `TypeId` hashing) and `ctfe-const-eval-select-and-reflection-intrinsic-verification-contracts` (`const_eval_select` MIR selection) to `ty::Const` symbolic structure, bit-packed `CtfeProvenance`, `Rvalue::Repeat`, RFC 1861 `extern type`, and parametric array/zeroize cursors.

## Findings

### 1. `ty::Const` Representation Stratification and `Rvalue::Repeat` Zero-Length Move Semantics

Basis: documentation (`rust-lang/rfcs@f43d5789...`: `text/2000-const-generics.md:L56–248`) + source (`rust-lang/rust@8144389c...`: `rustc_type_ir/src/const_kind.rs:L21–149`, `rustc_middle/src/ty/consts.rs:L15–21`, `rustc_middle/src/ty/consts/kind.rs:L13–141`, `rustc_middle/src/mir/syntax.rs:L1365–1373`; `proofs-rs/lean-miri@c92d1d97...`: `ExecutionMachine.lean:L243–260`) + execution (`probe_pkg2.py`) + derived

1. **`ConstKind` and `AliasConstKind` Across Polymorphic vs. Monomorphized MIR:**
   `rustc_type_ir::ConstKind<I>` (`const_kind.rs:L21–49`, 32 bytes on 64-bit targets per `consts.rs:L20–21`) classifies compile-time constants into 8 variants: `Param`, `Infer`, `Bound`, `Placeholder`, `Alias(IsRigid, AliasConst)`, `Value(ValueConst)`, `Error`, and `Expr(ExprConst)`. `AliasConstKind` (`L108–149`) distinguishes `Projection`, `InherentSelf` (carrying `Self` as argument 0), `InherentImpl`, `Free`, and `Anon` (such as `1 + 2` in `[u8; 1 + 2]`), while `ty::consts::kind::Expr` (`consts/kind.rs:L13–141`, 16 bytes) encodes unevaluated `feature(generic_const_exprs)` AST nodes (`Binop`, `UnOp`, `FunctionCall`, `Cast`). As RFC 2000 (`L200–248`) emphasizes, prior to monomorphization, structurally distinct syntactic anonymous const expressions (`N + 1` at two sites) are treated as distinct un-unifiable projections rather than algebraically equal values. Consequently, verifying `Runtime(PostCleanup)` monomorphized bodies sees concrete `ConstKind::Value`, whereas verifying library functions polymorphically over `<const N: usize>` requires explicit symbolic `nConst : Nat` parameters.
2. **Non-Vacuous `Rvalue::Repeat(Operand, ty::Const)` at `count = 0` (`syntax.rs:L1372`, `ExecutionMachine.lean:L243–260`):**
   `Rvalue::Repeat(op, count)` constructs `[op; count]`. In `lean-miri`'s `writeRepeat` (`ExecutionMachine.lean:L243–260`):
   - First, it evaluates `source` (`evalOperandAt`) and fails if `!source.layout.layout.isSized` (`L244–245`).
   - Second, it unconditionally forces `dest` into mutable memory (`forceAllocation`, `L246`).
   - **Zero-length hazard (`length == 0`, `L248–253`):** When `length == 0`, `writeRepeat` writes zero elements to `dest`, **yet still executes `aggregate.getPlaceAllocMut c dest`** (checking mutability/aliasing of `dest`) **and checks `if ← place.takePendingMoveDeinit` to write `.uninit` over `source`'s indirect memory**! Only when `length > 0` (`L254–259`) does it copy `source` into element `0` (`copyOp`) and replicate `elemSize` bytes `length - 1` times via `memCopyRepeatedly`. Treating `[move x; 0]` as a dead no-op therefore misses both mutable-place reborrows on `dest` and source move-deinitialization (`probe_pkg2.py`).

### 2. 64-Bit Bit-Packed `CtfeProvenance` and the 3-State CTFE Permission Lattice

Basis: normative (`Exploring C Semantics and Pointer Provenance`, POPL 2019 `10.1145/3290380`) + source (`rust-lang/rust@8144389c...`: `rustc_middle/src/mir/interpret/pointer.rs:L59–191, L226–365`; `proofs-rs/lean-miri@c92d1d97...`: `Miri/Memory/CtfeProvenance.lean:L13–131`) + execution (`probe_pkg2.py`) + derived

`rustc`'s `Provenance` trait (`pointer.rs:L59–80`) separates address-space-independent interpreters (`OFFSET_IS_ADDR = false`, `WILDCARD = None`, forbidding pointer-to-integer byte reads with `ReadPointerAsBytes` because relative offsets are not global addresses) from Miri's concrete/wildcard runtime provenance. `CtfeProvenance(NonZero<u64>)` (`pointer.rs:L90–164`) packs three fields into one nonzero 64-bit word (`Pointer` is 16 bytes, `L231–234`):

| Bit Range / Mask (`pointer.rs:L114–116`) | Field | Representation Invariant (`CtfeProvenance.lean:L17–24`) |
| :--- | :--- | :--- |
| Bits `0..61` (`ALLOC_ID_MASK = 2^62 - 1`) | `alloc_id : AllocId` | `0 < alloc_id.value < 2^62` (`4611686018427387904`); overflowing into bits `62–63` panics / returns `.allocationIdUsesFlagBits`. |
| Bit `62` (`SHARED_REF_MASK = 1 << 62`) | `shared_ref : Bool` | Derived from a shared reference (`as_shared_ref`). |
| Bit `63` (`IMMUTABLE_MASK = 1 << 63`) | `immutable : Bool` | **Coupled invariant (`L88–89, L143–145`):** `immutable = true → shared_ref = true` (`as_immutable` sets both bits `62` and `63`). |

Because `(immutable = true, shared_ref = false)` is unconstructible via `from_parts` (`pointer.rs:L141–151`, `CtfeProvenance.lean:L42–47`), the two flag bits span a **3-state permission lattice** (`probe_pkg2.py`):
- **`0b00` (mutable/unique):** Neither `shared_ref` nor `immutable` set; permits mutation of mutable CTFE allocations.
- **`0b01` (`shared_ref = true, immutable = false`):** Pointer obtained through `&T` where interior mutability (`!Freeze` / `UnsafeCell`) allows writes inside `UnsafeCell` during const evaluation.
- **`0b11` (`shared_ref = true, immutable = true`):** Frozen read-only pointer (`Freeze` behind `&T`, or static/promoted `.rodata`); forbids all writes.

`Miri/Memory/CtfeProvenance.lean` (`L55–115`) proves exact round-trip decoding (`packed_allocation_bits`, `packed_immutable_bit`, `packed_shared_bit`, `packed_nonzero`, `immutable_is_shared`) via kernel-checked `Nat.testBit` bitwise lemmas without `native_decide` or `omega`. Bridging CTFE constants into runtime verification requires preserving `(allocId, immutable, sharedRef)` metadata on static/promoted `GlobalAlloc` pointers: treating every CTFE pointer as flat `(allocId, offset)` erases frozen/interior-mutable provenance constraints before Tree Borrows retagging (`TypedRetag.lean`).

### 3. RFC 1861 `extern type`, `PointeeSized`/`MetaSized`, and Unknown-Footprint Aliasing Traps

Basis: documentation (`rust-lang/rfcs@f43d5789...`: `text/1861-extern-types.md:L1–138`, `text/2580-ptr-meta.md:L1–120`) + source (`rust-lang/rust@8144389c...`: `library/core/src/marker.rs:L145–192`, `library/core/src/ptr/metadata.rs:L59–170`, `library/core/src/mem/mod.rs:L410–517`, `compiler/rustc_ty_utils/src/layout.rs:L495–547`; `proofs-rs/lean-miri@c92d1d97...`: `DynamicLayout.lean:L85`, `Intrinsics.lean:L384–389`, `TypedRetag.lean:L158–171`) + execution (`probe_pkg2.py`) + derived

Before RFC 1861 (`text/1861-extern-types.md:L20–46`), Rust represented opaque C types using two unsound or misleading patterns: uninhabited `enum Opaque {}` (implying references/values can never exist, inviting dead-code/UB assumptions) or zero-sized `struct Opaque { _priv: () }` (claiming `size_of == 0`, stack allocability, and no-op `ptr::read`). An `extern type` (such as `unsafe extern "C" { type VTable; }` inside `core/src/ptr/metadata.rs:L164–170`) solves both by defining an unsized type whose pointer metadata is `()`.

1. **Position in `Sized: MetaSized: PointeeSized` (`marker.rs:L158–190`, `metadata.rs:L59–85`, `layout.rs:L495–547`):**
   - `rustc_ty_utils/src/layout.rs` assigns `ty::Foreign(..)` an unsized unit layout (`LayoutData::unit(cx, false)` at `L544–547`), yet assigns `*const T` / `&T` (including structs whose unsized tail is `ty::Foreign(..)`, `L498–500`) a **thin** scalar pointer (`LayoutData::scalar(cx, data_ptr)`).
   - Thus `extern type` satisfies `Thin` (`Pointee<Metadata = ()> + PointeeSized`, `metadata.rs:L85`), **refutes `Sized`**, and **refutes `MetaSized`** (once guarded statically per `marker.rs:L162–177`): pointers carry no runtime size or alignment token.
2. **Fail-Closed `size_of_val` vs. `TypedRetag.retagPlace` Zero/Prefix-Size Fallback (`DynamicLayout.lean:L85`, `Intrinsics.lean:L386`, `TypedRetag.lean:L160`):**
   - In `DynamicLayout.sizeAndAlignFromMeta`, `.foreign` returns `none` (`L85`), propagated upwards through enclosing `.adt`/`.tuple` containers (`L57–58`). Calling `size_of_val` or `align_of_val` (`Intrinsics.lean:L384–389`) fails closed with `.unsupported "extern type does not have known layout"`.
   - **Critical aliasing discrepancy (`TypedRetag.lean:L160`):** During Tree Borrows retagging (`retagPlace`), `size := ((← h.sizeAndAlign place).map Prod.fst).getD place.layout.layout.size` replaces `none` with the static prefix size `place.layout.layout.size` (`0` for `ExternOpaque`, or `4` for `#[repr(C)] struct FfiStruct { hdr: u32, tail: ExternOpaque }`!). Consequently, `insidePermissions` (`L128`) only tags `[0, 4)` of a 20-byte foreign allocation (`probe_pkg2.py`), leaving `[4, 20)` untagged. Any deductive verifier that encodes thin pointers uniformly as `PtrMeta.unit` and derives byte footprint solely from `layout.size` (`4` bytes) would **falsely prove disjointness** against a second C pointer aliasing bytes `[8, 12)` inside the opaque tail! Verifiers must distinguish `PtrMeta.unit` (`Sized`) from **`PtrMeta.externOpaque`**, binding spatial permissions to an explicit FFI allocation/capability contract rather than Rust type layout.

### 4. Parametric `[MaybeUninit<T>; N]` Initialization Cursors and Chunked Volatile Erasure

Basis: normative (`What You Get is What You C`, EuroS&P 2018 `10.1109/EuroSP.2018.00009`) + source (`rust-lang/rust@8144389c...`: `core/src/array/mod.rs:L109–161, L923–1034`, `core/src/mem/maybe_uninit.rs:L481–505, L826–834, L1048–1058, L1554–1564`; `RustCrypto/utils@0feca06c...`: `zeroize/src/{lib.rs:L278–453, L733–801, bulk.rs:L7–114, barrier.rs:L52–89}`; `joshlf/anneal@c131b320...`: `MirSemantics.lean`) + execution (`probe_pkg2.py`) + derived

1. **Prefix/Suffix Panic-Guard Cursors (`core/src/array/mod.rs:L923–1034`):**
   `core::array::from_fn` (`L109–114`) and `try_from_fn` (`L148–161`) allocate `let mut array = [const { MaybeUninit::uninit() }; N];` (`L153`) and delegate to `try_from_fn_erased` (`L923–938`), maintaining `Guard { array_mut: &mut [MaybeUninit<T>], initialized: usize }` (`L951–956`):
   - **Loop invariant (`0 <= initialized <= N`):** Indices `[0 .. initialized)` hold valid initialized `T` values; `[initialized .. N)` remain uninitialized (`MaybeUninit`).
   - **Transition (`L966–974`):** On `generator(initialized).branch()?` returning `Continue(item)`, `push_unchecked` writes element `initialized` and increments `initialized` via `unchecked_add(1)`.
   - **Cleanup vs. Commit (`L936, L978–987, L158`):** On early `Break` or panic unwind, `Guard::drop` runs `array_mut.get_unchecked_mut(..self.initialized).assume_init_drop()` (`L984`)—dropping `[0 .. initialized)` exactly once while never touching `[initialized .. N)`. On loop completion (`initialized == N`), `mem::forget(guard)` disarms the drop guard and `MaybeUninit::array_assume_init(array)` (`maybe_uninit.rs:L1048–1058`) asserts `T` inhabited and transmutes `[MaybeUninit<T>; N]` to `[T; N]`. `GuardBack` (`L998–1034`) maintains the mirror suffix invariant `[N - initialized .. N)` initialized. Exhaustive simulation across `N in 0..9`, every break index, and both directions (`90` cases in `probe_pkg2.py`) confirms `0` uninitialized drops, `0` leaks, and `0` double drops.
2. **Chunked Volatile Scrubbing vs. Dead Store Elimination (`zeroize/src/{lib.rs, bulk.rs, barrier.rs}`):**
   - `zeroize` (`lib.rs:L148–164`) resists Dead Store Elimination (DSE, `10.1109/EuroSP.2018.00009`) via two backends in `bulk.rs` (`L21–94`): on architectures in `HAS_ASM` (`L7–17`), `zeroize_byte_ptr` executes `ptr::write_bytes(dst, 0, len)` followed by `optimization_barrier` (`barrier.rs:L67–73`: `asm!("# {}", in(reg) ptr, options(readonly, preserves_flags, nostack))`, falling back to `core::hint::black_box` under Miri or unsupported arches); otherwise `volatile_fill_slice` uses `as_chunks_mut::<T, N>` (`bulk.rs:L78–114`) to split length `L` into `L / N` chunks `[0 .. (L / N) * N)` overwritten via `write_volatile([src; N])` plus remainder `[(L / N) * N .. L)` (`325` partitions checked across `L in 0..65`, `N in {1,2,4,8,16}` in `probe_pkg2.py`).
   - **Bit-validity vs. `MaybeUninit` erasure (`lib.rs:L307–440, L740–795`):** `MaybeUninit<Z>` and `[MaybeUninit<Z>]` implement `Zeroize` unconditionally via `MaybeUninit::zeroed()` / `zeroize_byte_ptr` because `MaybeUninit` removes type validity invariants (`L416–440`). Conversely, `NonZero*` (`L307–336`) zeroes to `1` (`ONE`), and `unsafe fn zeroize_flat_type` (`L740–795`) explicitly forbids references (`&T`, `&mut T`), `NonNull`/`NonZero*`, non-zero-tag enums, and owning containers (`Vec`, `Box`) because all-zero bytes violate their validity invariants on later reads or drops. Moreover, MIR `SlotVal.uninit` move-deinitialization (`deinitMovedPlace`) only prevents *source program reads* after a move—it does **not** verify that physical stack/heap memory was scrubbed by a `write_volatile` or `asm!` barrier prior to `StorageDead` (`lib.rs:L166–175`).

### 5. Parametric Unindexed `InitPrefixCursor`, `CtfeProv`, and `PtrMeta` in 3-Axiom `prelude` Lean 4

Basis: source (`joshlf/anneal@c131b320...`: `trusted/audit/TrustedBoundary.lean:L442–596`, `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/MirAst.lean:L308–321`) + execution (`probe_pkg2.py`) + derived

Modeling `[MaybeUninit<T>; N]` loops in Lean 4 using dependent length-indexed vectors (`Vector SlotState N` / `Fin N`) forces `HEq` transport across `k + 1` and `(L / N) * N + L % N = L` (`Nat.add_comm`), stalling kernel reduction (`whnf`) on symbolic `N`. Separating array element states (`List SlotState`) from symbolic length bounds (`nConst initCount : Nat`) eliminates dependent transports completely. Under `TrustedBoundary.lean:L442–596` (`prelude`, locked `Init.*` imports, no `/`, `%`, `&&&`, `|||`, `<<<` syntax, no `omega`/`native_decide`/`sorry`), the core algebra compiles with `Nat.div`/`Nat.mod`/`Nat.land`/`Nat.lor`/`Nat.shiftLeft` and `rfl`/induction:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Data.List.Notation

namespace Anneal.ConstCtfeArray

/-- 64-bit `CtfeProvenance` (`pointer.rs:90-164`, `CtfeProvenance.lean:17-53`). -/
structure CtfeProv where
  allocId   : Nat
  immutable : Bool
  sharedRef : Bool

def CtfeProv.wf (p : CtfeProv) : Bool :=
  Nat.blt 0 p.allocId &&
  Nat.blt p.allocId (Nat.shiftLeft 1 62) &&
  (match p.immutable with | true => p.sharedRef | false => true)

def CtfeProv.pack (p : CtfeProv) : Nat :=
  let immBit := match p.immutable with | true => Nat.shiftLeft 1 63 | false => 0
  let shBit  := match p.sharedRef with | true => Nat.shiftLeft 1 62 | false => 0
  Nat.lor p.allocId (Nat.lor immBit shBit)

/-- Pointer metadata distinguishing RFC 1861 `extern type` from `Sized` `unit`. -/
inductive PtrMeta where
  | unit
  | sliceLen (len : Nat)
  | externOpaque (capToken : Nat)

def ptrFootprintKnown : PtrMeta → Option Nat
  | .unit           => some 0
  | .sliceLen len   => some len
  | .externOpaque _ => none

inductive SlotState where
  | init
  | uninit

def matchPrefixAux (idx initCount : Nat) : List SlotState → Bool
  | [] => true
  | s :: rest =>
    let expected := Nat.blt idx initCount
    let ok := match s, expected with
      | .init, true   => true
      | .uninit, false => true
      | _, _          => false
    ok && matchPrefixAux (idx + 1) initCount rest

/-- Parametric prefix-init cursor for `core::array::Guard` (`[0..k)` init, `[k..N)` uninit). -/
def initPrefixCursorWf (nConst initCount : Nat) (slots : List SlotState) : Bool :=
  Nat.beq slots.length nConst &&
  Nat.ble initCount nConst &&
  matchPrefixAux 0 initCount slots

def matchSuffixAux (idx nConst initCount : Nat) : List SlotState → Bool
  | [] => true
  | s :: rest =>
    let startIdx := nConst - initCount
    let expected := Nat.ble startIdx idx
    let ok := match s, expected with
      | .init, true   => true
      | .uninit, false => true
      | _, _          => false
    ok && matchSuffixAux (idx + 1) nConst initCount rest

/-- Parametric suffix-init cursor for `core::array::GuardBack`. -/
def initSuffixCursorWf (nConst initCount : Nat) (slots : List SlotState) : Bool :=
  Nat.beq slots.length nConst &&
  Nat.ble initCount nConst &&
  matchSuffixAux 0 nConst initCount slots

/-- Chunk partition invariant for `zeroize::bulk::as_chunks_mut` (`len = (len / N) * N + rem`). -/
def chunkPartitionWf (sliceLen chunkN : Nat) : Bool :=
  if Nat.beq chunkN 0 then false
  else
    let chunks := Nat.div sliceLen chunkN
    let rem    := Nat.mod sliceLen chunkN
    Nat.beq (chunks * chunkN + rem) sliceLen && Nat.blt rem chunkN

theorem ctfe_imm_requires_shared_rejected :
    CtfeProv.wf ⟨7, true, false⟩ = false := rfl

theorem ctfe_imm_shared_ok :
    CtfeProv.wf ⟨7, true, true⟩ = true := rfl

theorem extern_opaque_no_known_footprint :
    ptrFootprintKnown (.externOpaque 42) = none := rfl

theorem prefix_cursor_step_ok :
    initPrefixCursorWf 3 2 [.init, .init, .uninit] = true := rfl

theorem prefix_cursor_hole_rejected :
    initPrefixCursorWf 3 2 [.init, .uninit, .init] = false := rfl

theorem suffix_cursor_ok :
    initSuffixCursorWf 3 1 [.uninit, .uninit, .init] = true := rfl

theorem chunk_partition_65_by_16 :
    chunkPartitionWf 65 16 = true := rfl

end Anneal.ConstCtfeArray
```

Transfer into `joshlf/anneal@c131b320...`:
- **TCB Gap:** `Trusted.MirAst` and `Trusted.MirSemantics` currently reject `Array`, `Foreign`, and `Rvalue::Repeat` as `.unsupported` (`MirAst.lean:L308–321, L612–628`). Supporting const generics and CTFE pointers requires extending `Trusted.*` with: (i) parametric `MirTy.array elem len` + `Rvalue.repeat` preserving zero-length `deinitMovedPlace` (`ExecutionMachine.lean:L248–253`), (ii) `CtfeProv` propagation on `GlobalAlloc` pointers, (iii) `PtrMeta.externOpaque` returning `.none` on size/align queries (never silently falling back to static layout size for disjointness), and (iv) an explicit `VolatileEvent` trace for `ptr::write_volatile` / barriered scrub proofs (`10.1109/EuroSP.2018.00009`).
- **0-TCB Theory Scaling:** Once `Trusted.*` exposes array element slots and `const N`, `initPrefixCursorWf`, `initSuffixCursorWf`, and `chunkPartitionWf` live 100% in untrusted `theory/`, verifying arbitrary symbolic `N` in $O(1)$ loop steps without `Fin N` casts or unrolling, while preserving RustBelt-style (`10.1145/3158154`) clean separation between initialized ownership and `MaybeUninit` raw storage.

## Boundaries

- **not examined**:
  - Completeness of `feature(generic_const_exprs)` constraint normalization inside `rustc_trait_selection` beyond `ty::consts::kind::Expr` AST representation (`consts/kind.rs:L13–141`).
  - Hardware ISA-level stack-frame clearing (`zeroize_stack` in `zeroize/src/stack.rs`, CPU register spilling) beyond Rust source/LLVM IR volatile/barrier semantics.
  - Live Lean `v4.34.1` compilation timing of `Anneal.ConstCtfeArray` under `anneal-audit` (only static compliance with `TrustedBoundary.lean:L442–596` and `foundation-lock.json` was checked).
- **unknown**:
  - Whether future `rustc` `SizedHierarchy` (`MetaSized`, `PointeeSized` in `core/src/marker.rs:L162–192`) stabilization will alter `mem::size_of_val` trait bounds so calling `size_of_val` on `extern type` becomes a compile-time error rather than a runtime/CTFE `.unsupported` check.
- **known not to apply**:
  - `zeroize::zeroize_flat_type` (`zeroize/src/lib.rs:L740–795`) does **not** safely apply to `&T`, `&mut T`, `NonNull`, `NonZero*`, enums with non-zero discriminants, or `Vec`/`Box` values (overwrite with all-zero bytes creates invalid bit patterns and UB upon drop/use).
  - `MirSemantics` `SlotVal.uninit` move deinitialization (`deinitMovedPlace = true`) does **not** establish physical RAM scrubbing against LLVM Dead Store Elimination (`zeroize/src/lib.rs:L166–175`).
  - `TypedRetag.retagPlace` (`TypedRetag.lean:L160`) falling back to `place.layout.layout.size` on `.foreign` does **not** prove spatial disjointness between an FFI struct and pointers into its trailing `extern type` bytes.
- **unsupported**:
  - In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` and `Trusted.MirSemantics` fail closed (`FaultKind.unsupported`) on `Array`, `Foreign`, `Rvalue::Repeat`, `ConstKind::Param`/`Expr`, raw pointer dereferences, `write_volatile`, and inline `asm!` (`MirAst.lean:L308–321, L612–628`).

## Evidence

### Primary Repositories, Commits, Files, and Peer-Reviewed Sources

| Subject | Exact Identity | Inspected Paths & Anchors |
| :--- | :--- | :--- |
| **Rust & std** | `rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd` | `compiler/rustc_type_ir/src/const_kind.rs` (`L21–149`); `compiler/rustc_middle/src/ty/consts.rs` (`L1–21`); `compiler/rustc_middle/src/ty/consts/kind.rs` (`L13–141`); `compiler/rustc_middle/src/mir/syntax.rs` (`L1365–1373`); `compiler/rustc_middle/src/mir/interpret/pointer.rs` (`L59–191`, `L226–365`); `compiler/rustc_ty_utils/src/layout.rs` (`L478–547`); `library/core/src/marker.rs` (`L145–192`); `library/core/src/ptr/metadata.rs` (`L59–170`); `library/core/src/mem/mod.rs` (`L405–517`); `library/core/src/mem/maybe_uninit.rs` (`L481–505`, `L826–834`, `L1048–1058`, `L1554–1564`); `library/core/src/array/mod.rs` (`L109–161`, `L923–1034`) |
| **lean-miri** | `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/Memory/CtfeProvenance.lean` (`L13–131`); `Miri/Interpreter/ExecutionMachine.lean` (`L243–260`); `Miri/Interpreter/DynamicLayout.lean` (`L10–86`); `Miri/Interpreter/Intrinsics.lean` (`L384–389`); `Miri/Interpreter/TypedRetag.lean` (`L114–171`) |
| **Rust RFCs** | `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | `text/1861-extern-types.md` (`L1–138`); `text/2000-const-generics.md` (`L1–250`); `text/2580-ptr-meta.md` (`L1–120`) |
| **zeroize** | `RustCrypto/utils` @ `0feca06cf87e61567033a333feb79ecf3c427fea` | `zeroize/src/lib.rs` (`L28–38`, `L148–180`, `L278–453`, `L733–801`); `zeroize/src/bulk.rs` (`L7–114`); `zeroize/src/barrier.rs` (`L52–89`) |
| **Anneal & Lean 4** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/audit/TrustedBoundary.lean` (`L442–596`); `trusted/lean/foundation-lock.json`; `trusted/lean/Trusted/MirAst.lean` (`L308–321`, `L612–628`); `trusted/lean/Trusted/MirSemantics.lean` (`L578–599`, `L803`) |
| **Literature** | POPL 2019 (`10.1145/3290380`); POPL 2018 (`10.1145/3158154`); PLDI 2025 (`10.1145/3735592`); EuroS&P 2018 (`10.1109/EuroSP.2018.00009`) | Memarian et al.; Jung et al. (RustBelt); Villani et al. (Tree Borrows); Simon, Chisnall, & Anderson |

### Executable Probe (`CPython 3.13.15`, `x86_64`, `2026-11-20`)

```python
IMMUTABLE_MASK, SHARED_REF_MASK = 1 << 63, 1 << 62
ALLOC_ID_MASK = ((1 << 64) - 1) & ~IMMUTABLE_MASK & ~SHARED_REF_MASK

def ctfe_pack(aid, imm, sh):
    assert 0 < aid < (1 << 62)
    return aid | (IMMUTABLE_MASK | SHARED_REF_MASK if imm else (SHARED_REF_MASK if sh else 0))

def ctfe_decode(p):
    return (p & ALLOC_ID_MASK, (p & IMMUTABLE_MASK) != 0, (p & SHARED_REF_MASK) != 0)

states = set()
for aid in (1, 2, 42, (1 << 62) - 1):
    for imm in (False, True):
        for sh in (False, True):
            p = ctfe_pack(aid, imm, sh)
            da, di, ds = ctfe_decode(p)
            assert p != 0 and da == aid and ((not di) or ds)
            states.add((di, ds))
assert states == {(False, False), (False, True), (True, True)}

def repeat_move(src, n, zst=False):
    return (True, n, "UNINIT" if not zst else src)

r_real = repeat_move("INIT_42", 0, False)
r_naive = (False, 0, "INIT_42")
assert r_real[2] == "UNINIT" and r_naive[2] == "INIT_42"

def dyn_size(kind, prefix_sz): return None if kind == "foreign" else (prefix_sz, 4)
def size_of_val(kind): return "ERR_UNSUPPORTED_FOREIGN" if dyn_size(kind, 0) is None else 0
def retag_sz(kind, prefix_sz): return d[0] if (d := dyn_size(kind, prefix_sz)) else prefix_sz

ffi_real, ffi_retag, alias = (0, 20), (0, retag_sz("foreign", 4)), (8, 12)
assert size_of_val("foreign") == "ERR_UNSUPPORTED_FOREIGN"
assert ffi_retag[1] <= alias[0] and ffi_real[0] < alias[1] and alias[0] < ffi_real[1]

def sim_guard(n, fail=None, back=False):
    slots, drops, k = [None] * n, [], 0
    while k < n:
        idx = (n - 1 - k) if back else k
        if fail is not None and k == fail:
            rng = range(n - k, n) if back else range(0, k)
            for j in rng:
                assert slots[j] is not None
                drops.append(slots[j]); slots[j] = None
            return ("ERR", k, drops, slots)
        slots[idx] = f"v{idx}"; k += 1
    return ("OK", k, drops, slots)

g_cases = 0
for n in range(9):
    for f in list(range(n)) + [None]:
        for b in (False, True):
            st, k, dr, sl = sim_guard(n, f, b); g_cases += 1
            if f is None: assert st == "OK" and k == n and dr == [] and sl == [f"v{i}" for i in range(n)]
            else:
                exp = list(range(n - f, n) if b else range(f))
                assert st == "ERR" and dr == [f"v{i}" for i in exp] and all(x is None for x in sl)

chunks_ok = 0
for ln in range(65):
    for w in (1, 2, 4, 8, 16):
        rd = (ln // w) * w
        cs = [(i * w, (i + 1) * w) for i in range(ln // w)]
        assert sum(b - a for a, b in cs) + (ln - rd) == ln and 0 <= (ln - rd) < w
        chunks_ok += 1

print("PROBE_CONST_CTFE_OK", {"lattice": sorted(states), "repeat0": (r_real[2], r_naive[2]), "extern_sz": size_of_val("foreign"), "retag_vs_real": (ffi_retag, ffi_real), "false_disjoint_vs_catch": (ffi_retag[1] <= alias[0], alias[0] < ffi_real[1]), "guard_cases": g_cases, "chunks": chunks_ok})
```

Observed output (`2026-11-20`, `CPython 3.13.15`): `PROBE_CONST_CTFE_OK {'lattice': [(False, False), (False, True), (True, True)], 'repeat0': ('UNINIT', 'INIT_42'), 'extern_sz': 'ERR_UNSUPPORTED_FOREIGN', 'retag_vs_real': ((0, 4), (0, 20)), 'false_disjoint_vs_catch': (True, True), 'guard_cases': 90, 'chunks': 325}`.

## Revalidation

1. **Rust & CTFE check:** Diff `rustc_middle/src/mir/interpret/pointer.rs`, `rustc_type_ir/src/const_kind.rs`, `library/core/src/ptr/metadata.rs`, and `library/core/src/array/mod.rs` at a newer `rust-lang/rust` commit against `8144389c895da997dbdecaa635e41d6a50be6ffd` for changes to `CtfeProvenance`, `PointeeSized`/`MetaSized`, or `Guard`.
2. **`lean-miri` & `zeroize` check:** Diff `Miri/Memory/CtfeProvenance.lean`, `ExecutionMachine.lean` (`writeRepeat`), and `TypedRetag.lean` (`retagPlace`) against `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, and `zeroize/src/{lib,bulk,barrier}.rs` against `0feca06cf87e61567033a333feb79ecf3c427fea`.
3. **Anneal and Lean kernel check:** Inspect `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` for `Array`/`Foreign`/`Repeat` admission, and compile `Anneal.ConstCtfeArray` under Lean `v4.34.1` (`--trust=0`) plus Anneal's boundary auditor to verify `{propext, Quot.sound, Classical.choice}` closure.
4. **Executable probe:** Run the Python 3 script in **Evidence** (`python3` $\ge 3.10$) and verify `PROBE_CONST_CTFE_OK` prints with exit code `0`.
