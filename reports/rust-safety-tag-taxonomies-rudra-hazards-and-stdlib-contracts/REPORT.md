# Empirical Safety-Tag Taxonomies, Rudra Unsoundness Classes, and Standard-Library Safety Contracts for Zero-TCB MIR Verification

## Summary

Real-world `unsafe` Rust obligations cluster around layout, pointer provenance, initialization, aliasing, concurrency capability, and unwind preservation. Synthesizing ecosystem empirical studies, primary `// SAFETY:` comments, Rudra and SafeDrop bug classes, and `core::ub_checks` runtime preconditions yields four findings for a `0`-TCB Lean 4 proof library over `Trusted.MirSemantics`:

1. **Finite Tag Concentration (`96.1%` of `libstd`):** Rao et al. (`arXiv:2504.21312v2`) distill **21 primitive safety tags** (`Layout`, `Pointer`, `Content`, `Alias`, `Contextual`), four compound tags, and three contractual roles (`precondition`, `hazard`, `option`), covering **96.1%** of **516** public `unsafe` APIs (`core`: **98.3%**, `alloc`: **82.8%**, `std`: **84.2%**). Auditing `zerocopy`, `hashbrown`, `bytes`, `crossbeam`, `tock`, `asterinas`, and Fuchsia `starnix` adds four patterns beyond `tag-std`: segmented `[0..w) ++ Hole[w..r) ++ [r..n)` `MaybeUninit` slices, ZST pointer-integer overloading (`without_provenance_mut`), negative-offset container indexing (`Bucket::sub`), and demonic DMA/usercopy memory.
2. **Unsoundness at Unwind & Trait Seams:** Rudra (`10.1145/3477132.3483570`) identified **264** memory-safety bugs (>50% of RustSec advisories then tracked), led by **panic-unwind state corruption** (`UnsafeDataflowChecker`), **higher-order safe-trait assumptions** (`Read`, `Iterator`, `Ord`), **`Send`/`Sync` variance errors** (`SendSyncVarianceChecker`), and **`#[may_dangle]` / drop-glue errors** (`UnsafeDestructorChecker`, SafeDrop `10.1145/3542948`).
3. **`core::ub_checks` Cannot Substitute for Spatial/Aliasing Contracts:** `assert_unsafe_precondition!` separates `check_language_ub` (off in CTFE/Miri via `const_eval_select!`) from `check_library_ub` (`intrinsics::ub_checks()`), emitting `Operand::RuntimeChecks(UbChecks)`. Dynamic booleans cannot observe cross-allocation provenance, uninitialized bits, Tree Borrows protectors, or linear ownership; `Trusted.MirAst` fails closed on `RuntimeChecks`.
4. **5-Family Pass-1 Combinators + Minimal TCB Gap Ledger:** Under Anneal's Pass-1 envelope (`trusted/audit/TrustedBoundary.lean`: 51 locked `Init.*` modules, zero `Init.Omega`/`bv_decide`/`Std.*`/`._unsafe_rec`, 22 structural tactics, Statement-Origin Separation), all 25 obligations collapse onto **five orthogonal `theory/` families** (`CertCheck`, `RegionSpan`, `BitValidity`, `TwoTrackUnwind`, `ProtocolCap`) with seven minimal `Trusted.*` extensions (`G1`–`G7`) verifiable against `lean-miri`.

## Applicability

This report relates four classes of primary artifacts pinned in `REPORT.json`:

- **Production Rust Corpora:** `rust-lang/rust` (`8144389c`), `google/zerocopy` (`ec133ce4`), `rust-lang/hashbrown` (`f3e9f0fc`), `tokio-rs/bytes` (`67edc2b9`), `crossbeam-rs/crossbeam` (`a28f40fd`), `tock/tock` (`ba6aa7ed`), `asterinas/asterinas` (`7fecb4ff`), and Fuchsia Starnix `usercopy` (`fa0843ce`)—exact 40-char SHAs in `## Evidence` and `REPORT.json`.
- **Safety-Contract & Bug-Finding Frameworks:** `safer-rust/safety-tags` (`52077ed1`, `safety-tool` v0.4.1, `arXiv:2504.21312v2`, `rust-lang/rfcs@f43d5789`), `sslab-gatech/Rudra` (`fc9add2c`, `10.1145/3477132.3483570`), SafeDrop (`10.1145/3542948`), `model-checking/verify-rust-std` (`a43ef3d4`), plus empirical studies (`10.1145/3377811.3380413`, `10.1145/3428204`, `10.1145/3385412.3386036`).
- **Target Zero-TCB Verifier:** `joshlf/anneal` (`c131b320`) on Lean 4 `v4.34.1` (`leanprover/lean4@5045d005`) with CI Pass 2 validation against `proofs-rs/lean-miri` (`c92d1d97`).
- **Lean 4 Pass-1 Constraint Envelope (`trusted/audit/TrustedBoundary.lean` L442–596):** Combinators in `theory/` import only the 51 locked `Init.*` modules (no `Init.Omega`, `Init.Data.BitVec.Lemmas`, `Std.*`, `Lean.*`), use only `{propext, Quot.sound, Classical.choice}`, prohibit `partial` and `._unsafe_rec` (structural `@Nat.rec`/`List.foldr` only), stay within the 22 structural tactics (banning `omega`, `ring`, `linarith`, `bv_decide`, `native_decide`, `decide!`, `grind`, `rcases`, `sorry`, `set_option`, `noncomputable section`, and custom syntax/macros; allowing `@[irreducible]`), and maintain **Statement-Origin Separation** (target theorems mention only `Init.*`, `Trusted.*`, `Mir.*`, never `Anneal.*`).

Direct observations of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` characterize its live scalar/bool/unit/never/fieldless-enum MIR subset and `PureLift.MirBridge`; extensions beyond that surface are derived against `lean-miri`.

## Findings

### 1. Quantitative Safety-Tag Distribution vs. Real-World `// SAFETY:` Corpora

`Basis: source + documentation + derived`

#### 1.1 Empirical Structure and the 21-Tag `tag-std` Taxonomy

Four empirical investigations establish the structure of `unsafe` Rust obligations:

- **Call-Marker Dominance (Evans et al., ICSE 2020, `10.1145/3377811.3380413`):** Under **30%** of crates contain literal `unsafe` syntax, yet **50–75%+** depend on `unsafe` transitively; **64–89%** of `unsafe` markers are calls to `unsafe fn`s (chiefly `core`/`std` pointer/slice/SIMD APIs and ~22.5% C FFI), making caller-callee contract propagation the primary audit burden.
- **Tiny Blocks & Implicit Module Invariants (Astrauskas et al., OOPSLA 2020, `10.1145/3428204`; Qin et al., PLDI 2020, `10.1145/3385412.3386036`):** Most `unsafe` blocks are **1–5** statements across six motivations (FFI, bounds-bypass, aliasing data structures, OS/hardware, `transmute`, concurrency), relying silently on struct/module invariants across safe methods.
- **`tag-std` Primitive Tags and Audit Rules (`arXiv:2504.21312v2`, `safer-rust/safety-tags@52077ed142e6`):** Auditing **516** public `unsafe` APIs in Rust 1.84.0 (`414` `core`, `64` `alloc`, `38` `std`, excluding 171 `#[rustc_intrinsic_must_be_overridden]` compiler intrinsics), Rao et al. synthesize **21 primitive tags** and **4 compound abbreviations** (`Deref ≡ Allocated ∧ InBound`, `ValidPtr ≡ ZST ∨ (!ZST ∧ Deref)`, `Ptr2Ref ≡ Align ∧ Deref ∧ Alias`, `Layout ≡ ValidNum ∧ Allocated`), achieving **96.1%** overall coverage (**98.3%** `core` / 744 tags; **82.8%** `alloc` / 105 tags; **84.2%** `std` / 44 tags).

| Category | Primitive Tags (`tag-std`) | Formal Contract Summary | Contractual Role(s) |
| :--- | :--- | :--- | :--- |
| **Layout** | `Align`, `Size`, `!Padding` | `p % align(T) == 0 ∧ sz(T) % align(T) == 0`; `sz(T) ∈ S` (e.g., `!ZST`); `padding(T) == 0` | `precondition`, `option` (`Size`) |
| **Pointer** | `!Null`, `Allocated`, `InBound`, `!Overlap` | `p ≠ 0`; `alloc(p..p+sz*len) = α`; `[p, p+sz*len) ⊆ single_obj`; `\|dst - src\| ≥ sz*len` | `precondition` |
| **Content** | `ValidNum`, `ValidString`, `ValidCStr`, `Init`, `Unwrap`, `Typed` | `expr ∈ range ∧ no_overflow`; UTF-8; null-terminated C-str; initialized valid `T`; enum variant `unwrap(v)=τ`; `typeOf(*p)=τ` | `precondition`, `hazard` (`ValidString`, `Init`) |
| **Alias** | `Owning`, `Alias`, `Alive` | Unique ownership (`ownership(*p) = 0`); no conflicting mutable alias; `lifetime(*p) ≥ λ_t` | `precondition` (`Owning`, `Alive`), `hazard` (`Alias`) |
| **Contextual** | `Pinned`, `!Volatile`, `Opened`, `Trait`, `!Reachable` | Address stability until drop; no concurrent volatile/DMA writes; open FD (RFC 3128); `τ : χ`; `SAT(cond) = false` | `hazard` (`Pinned`), `precondition`, `option` (`Trait`) |

Critically, `tag-std` separates three contractual roles—**`precondition`** (must hold at call entry), **`hazard`** (persistent post-call obligation such as `Pinned`, `Alias` after raw-pointer-to-reference conversion, `!Init`, or `ValidString` after `&mut str::as_bytes_mut`), and **`option`** (sufficient alternative, e.g., `Trait(T, Unpin)` waiving `Pinned`)—and checks **Audit Units** (**71.11%** function-level in `core`, shifting to **37.92%** method-level in `alloc` and **49.37%** in `std`) via three rules: **Rule I** (Call-Site check/delegation), **Rule II** (Constructor Guarantee matching later safe methods like `Box::drop`), and **Rule III** (State Exposure banning unguarded public fields like `Pin<Ptr>`'s `pub pointer`, motivating RFC PR `#3458` Unsafe Fields and RFC PR `#3842` Safety Tags). Applying these rules fixed **27** `libstd` APIs (**61** tags, including missing `Allocator` provenance on `Box`/`Arc`/`Weak::from_raw`, missing `Alias` on `Box`/`CString::from_raw`, and **2** false `!Null` tags on `ptr::read_unaligned`/`write_unaligned` for ZSTs). `safety-tool` (`v0.4.1`, `safety-tool/Cargo.toml`) checks `#[safety::requires]`/`#[safety::checked]` propagation across `std`, `rfl`, and `asterinas` profiles.

#### 1.2 Production Crate `// SAFETY:` Patterns Beyond `tag-std`

Inspecting primary `// SAFETY:` comments across foundational and OS crates reveals four additional obligation classes:

1. **Interior Mutability & Non-Wrapping Provenance (`google/zerocopy@ec133ce4d799`):** `PtrInner<'a, T>` (`zerocopy/src/pointer/inner.rs` L65–102) stores `NonNull<T>` with `PhantomData<&'a core::cell::UnsafeCell<T>>` (covariant in `'a`, invariant in `T` in `const fn`), requiring `base + o` non-wrapping in `usize`. `Unalign<T>::deref_unchecked` (`wrappers.rs` L239–269) pairs `#[repr(C, packed)]` layout equivalence with caller-promised alignment, while `SplitAt::split_at_mut` (`split_at.rs` L198–285) couples an `unsafe trait` postcondition (`MetadataOf::new_in_bounds`) with `IntoBytes` (`!Padding`).
2. **Backwards Negative-Offset Indexing & ZST Address Punning (`rust-lang/hashbrown@f3e9f0fc110f`):** `Bucket::next_n` (`src/raw.rs` L428–474) stores control bytes at the allocation boundary and indexes elements **backwards** via `self.ptr.as_ptr().sub(offset)` when `!T::IS_ZERO_SIZED` (`to_base_index() + offset <= bucket_mask`), switching to provenance-free `ptr::without_provenance_mut(self.ptr.as_ptr().addr() + offset)` when `T::IS_ZERO_SIZED`.
3. **LSB Pointer Tagging & Handmade Vtables (`tokio-rs/bytes@67edc2b999d6`):** `src/bytes.rs` (L1323–1365) hides `KIND_ARC` in bit 0 of `*mut Shared` (`const _: () = assert!(mem::align_of::<Shared>() % 2 == 0)`), dispatching refcounted operations via `static SHARED_VTABLE: Vtable`.
4. **Demonic External Memory & Segmented Buffers (`asterinas`, `tock`, `crossbeam`, Fuchsia `starnix`):** `asterinas/asterinas@7fecb4ffabc7` (`ostd/src/mm/dma/dma_coherent.rs` L84–144) treats physical frames as *"untyped DMA memory before `drop`"* and uses `ManuallyDrop::new(self)` + `ptr::read(&this.inner)` in `DmaCoherent::split` to avoid double-`unprepare_dma`. Fuchsia Starnix `usercopy` (`fa0843ce71880308`, `src/starnix/lib/usercopy/src/lib.rs`) casts `&mut [T]` to `&mut [MaybeUninit<T>]` (`slice_to_maybe_uninit_mut`) and copies across user addresses (`copyin`/`copyout`) via exception-table assembly `hermetic_copy`. `tock/tock@ba6aa7edc014` (`kernel/src/collections/ring_buffer.rs` L53–76) splits circular `&[MaybeUninit<T>]` storage into `[head..tail)` or wrapped `[head..cap) ++ [0..tail)`, while `crossbeam-rs/crossbeam@a28f40fdddb7` (`crossbeam-queue/src/array_queue.rs` L247–272) guards `UnsafeCell<MaybeUninit<T>>` slots via power-of-2 mask `(tail & (one_lap - 1))` and monotonic `stamp` counters.

**Informal Prose Failure Modes:** Upstream comments exhibit imprecise invariants (`core::slice::binary_search_by` `library/core/src/slice/mod.rs` L3000–3003 writes `mid < size: mid = size / 2 + ...` instead of `base + size <= self.len()`), unstated `isize::MAX` bounds, and bare `// SAFETY:` headers (`asterinas` `dma_coherent.rs` L177, 190).

---

### 2. Rudra Bug Classes and SafeDrop Deallocation Hazards

`Basis: normative + source + derived`

Inspecting `sslab-gatech/Rudra@fc9add2c4721` (`src/analysis.rs` L64–135, `unsafe_dataflow.rs` L149–284, `send_sync_variance/mod.rs` L74–142, L198–232, `unsafe_destructor.rs` L36–177), Bae et al. (`10.1145/3477132.3483570`), and Cui et al. (*SafeDrop*, `10.1145/3542948`) categorizes ecosystem unsoundness into four structural mechanisms:

1. **Panic Safety / Unwind-Induced Double-Drop & Uninit Exposure (`UnsafeDataflowChecker`):** Rudra tracks intraprocedural taint from **lifetime bypasses** to **unresolvable generic panic sinks** (`Instance::resolve(tcx, param_env, callee_did, callee_substs)` returning `Ok(None)`—representing user-supplied `F: FnMut`, `I: Iterator`, `R: Read`, `T::clone`, or `T::drop`). *Strong bypasses* (`ptr::read` on `!Copy`, `Vec::set_len(n)` with `n != 0`, `slice::from_raw_parts`, `ptr::as_ref`, `slice::get_unchecked`) and *weak bypasses* (`ptr::write`, `ptr::copy` on `!Copy`) break type invariants transiently (duplicating ownership or exposing uninitialized slots). Any unwind across a subsequent generic call triggers `Drop` on the broken container, turning local `unsafe` state into safe-caller UB.
2. **Higher-Order Safe-Trait Invariant Trust:** Unsafe callers frequently assume semantic postconditions on *safe* traits (`Read::read` not reading uninitialized destination bytes; `Iterator::size_hint` returning exact bounds). Safe implementations may legally violate both; soundness requires either zero-initializing / tracking written counts (`Vec::splice` increments `vec.len += 1` per yielded element in `library/alloc/src/vec/splice.rs` L114–122) or gating on an **`unsafe trait`** (`TrustedLen`, `zerocopy::IntoBytes`, `MetadataOf`).
3. **`Send` / `Sync` Variance Errors (`SendSyncVarianceChecker`):** Manual `unsafe impl Send/Sync for Wrapper<T>` bypasses auto-trait checking. `send_sync_variance/mod.rs` (L198–232) classifies 7 `BehaviorFlag` defects, led by `API_SEND_FOR_SYNC` (implementing `Sync` without `T: Send` when `&Wrapper<T>` can transfer ownership or `&mut T` across threads, allowing non-`Send` `Rc` refcount races) alongside `RELAX_SEND`/`RELAX_SYNC` and `PHANTOM_SEND_FOR_SEND`.
4. **Destructor Drop-Check & Alias Deallocation Hazards (`UnsafeDestructorChecker` & `SafeDrop`):** Rudra flags `unsafe` blocks inside `Drop::drop` (catching `#[may_dangle]` dereferences of dead generic references); SafeDrop (`10.1145/3542948`) performs Tarjan-guided path-sensitive MIR alias/drop-state dataflow to detect partial-move and manual-deallocation double-frees across call chains.

---

### 3. Standard-Library Runtime Preconditions (`ub_checks`), Built-in Contracts, and MIR Lowering

`Basis: source + normative`

Inspection of `library/core/src/ub_checks.rs` (L51–184), `library/core/src/contracts.rs` (L1–25), `library/core/src/ptr/mod.rs` (L549–735, L1399–1410), `library/core/src/slice/raw.rs` (L124–195), and `library/core/src/slice/mod.rs` (L949–960, L1339–1510, L2054–2065) at `rust-lang/rust@8144389c895da997` establishes how `core` instruments preconditions:

1. **`check_language_ub` vs. `check_library_ub`:** `assert_unsafe_precondition!` distinguishes immediate Abstract Machine UB (`check_language_ub()`, returning `const_eval_select!(const: false, runtime: !cfg!(miri)) && intrinsics::ub_checks()` so Miri reports root-cause UB directly without redundant panics—used in `ptr::copy_nonoverlapping`, `slice::from_raw_parts`, and `as_chunks_unchecked`) from library contract checks (`check_library_ub` aliasing `intrinsics::ub_checks`, active even in Miri/CTFE—used in `slice::split_at_unchecked`'s `mid <= len`, `slice::swap_unchecked`, and `ptr::swap_nonoverlapping`).
2. **MIR Persistence and `Operand::RuntimeChecks`:** Calls expand to `if ::core::ub_checks::$kind() { precondition_check(args) }`, where `precondition_check` carries `#[rustc_no_mir_inline] #[inline] #[rustc_nounwind]`. Because `intrinsics::ub_checks()` lowers to `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` evaluated during downstream crate codegen, `Trusted/MirAst.lean` (L548–556) **rejects `RuntimeChecks` fail-closed** rather than folding it to a constant boolean across crates.
3. **Expressiveness Boundary vs. `verify-rust-std` & `core::contracts`:** While `ub_checks.rs` checks alignments (`maybe_is_aligned`), non-nullity (`is_zst || !ptr.is_null()`), allocation overflow (`len <= isize::MAX / size`), and numeric address separation (`src.addr().abs_diff(dst.addr()) >= size`, stubbed to `true` in `const`), dynamic booleans **cannot check** cross-allocation provenance (`InBound` when two distinct heap blocks are adjacent), uninitialized memory reads (`Init`), Tree Borrows tags (`Alias`), unique ownership (`Owning`), or concurrent DMA writes (`!Volatile`). Likewise, `core::contracts::build_check_ensures` (`contracts.rs` L18–25, `#![feature(contracts_internals)]`) wraps `Fn(&Ret) -> bool` executable checks, so `model-checking/verify-rust-std@a43ef3d40d9f` (`Kani`, `ESBMC`, `VeriFast`, `Flux`, `KMIR`) relies on symbolic memory/ghost contracts beyond runtime predicates.

---

### 4. Orthogonal Mapping onto Pass-1 Lean 4 Combinators and Conceptual Minimality

`Basis: source + derived`

#### 4.1 Collapsing 25 Obligations into Five Minimal Pass-1 Combinator Families

| Combinator Family (`theory/Anneal/`) | Covered Obligations (`tag-std` + Audit) | Pass-1 Mechanization (`Init.*`-Only, Zero `._unsafe_rec`) | Day-2 & Kernel Scaling Advantage |
| :--- | :--- | :--- | :--- |
| **`1. CertCheck`** (Total GMP `Nat` Reflection) | `ValidNum`, `Align`, `Size`, `!Reachable` | Reified `VarId := Nat` AST checked via `@Nat.rec`/`List.foldr` **Sparse Farkas + Chvátal–Gomory cuts** and **`Tnum` `(val, mask)` × Wrapped Intervals**; discharged by `exact sound env g cert rfl` | Executes in Lean's C++ GMP `reduce_nat` kernel (`<5 ms`), replacing banned `omega`/`bv_decide`; `Nat.ble shift 128` blocks GMP DoS |
| **`2. RegionSpan`** (`PureLift` + `AnchoredSpan`) | `Allocated`, `InBound`, `!Overlap`, `ZstDualMode`, `NegativeOffsetContainer`, `!Volatile`, `PinAddrStable` | Extends `Anneal.PureLift` (`PermTree`, `LoanGraph`, `SpatialPin`) with **`AnchoredSpan`** `(allocId, baseOff, totalLen)` supporting `.sub` offsets and ZST `without_provenance` mode, plus **`OpaqueDma`** blocking CSE on DMA/VMO memory | Safe code remains pure (`spatial = .leaf`) via `PureLift`; `freezeToSpatial` localizes byte logic to `unsafe` spans; `PTree` keys give $O(\log N)$ framing |
| **`3. BitValidity`** (`ValidBytes` + `withspacer`) | `Init`, `InitSegmented`, `Typed`, `!Padding`, `ValidString`, `ValidCStr`, `Unwrap` | Relational `ValidBytes : MirTy → List AllocByte → Prop` over segmented `[0..w) ++ Hole[w..r) ++ [r..n)` runs; **`withspacer`** padding gap lists collapse to `rfl` on `IntoBytes` (`gaps = []`) and force `.uninit` on padded moves | Parametric `LayoutEnv` insulates proofs from `repr(Rust)` field layouts; avoids unsound total byte decoders |
| **`4. TwoTrackUnwind`** (`(onRet, onUnw)` + `LibInv`) | **Rudra `UnsafeDataflow` panic safety**, `UnwindDropSafe`, `SafeDrop` | Block-indexed `(onRet : Out → Prop, onUnw : CallerMemory → Prop)` WP over `MirWp`, requiring **`AdmissibleLibInv`** at `.vis` generic/trait callbacks and checking cleanup pads once per cutpoint | Avoids $O(2^k)$ cleanup-path blowup; catches half-mutated container unwinds mechanically |
| **`5. ProtocolCap`** (`Option`-PCM + `TraitContract`) | `Owning`, `Alias`, `Alive`, `Pinned`, `Opened`, `Trait`, **`Send`/`Sync` variance**, `HigherOrderPost` | Constructive **`Option`-PCM** (`op : M → M → Option M` for exclusive/fractional/refcount capabilities) + **`UnsafeTraitSummary`** (trusted only on `unsafe trait`, never safe `Read`/`Ord`/`FnMut`), hidden inside `Proof.*` | Preserves Statement-Origin Separation (specs stay `Anneal.*`-free); enforces `T: Send` on `Sync` shares |

#### 4.2 Self-Contained Pass-1 GMP Reflection Checker Example (`CertCheck`)

Without `Init.Omega`, `bv_decide`, `rcases`, or `._unsafe_rec`, linear difference chains (`0 ≤ write ≤ read < len ≤ isizeMax`) reduce via `List.foldr` over reified `VarId` indices cleanly inside `Init.*`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace Anneal.SafetyCertExample

/-- Reified difference constraint `env lhs + k ≤ env rhs`. -/
structure DiffLe where
  lhs : Nat
  k   : Nat
  rhs : Nat

def DiffLe.denote (env : Nat → Nat) (c : DiffLe) : Prop :=
  env c.lhs + c.k ≤ env c.rhs

/-- Total structural-fold checker (zero `_unsafe_rec`) verifying a chain of
    difference inequalities reduces by `rfl` in Lean's GMP `Nat` kernel. -/
def checkDiffStep (edge : DiffLe) (acc : Option (Nat × Nat)) : Option (Nat × Nat) :=
  match acc with
  | none => none
  | some (cur, sumK) =>
    if Nat.beq cur edge.lhs then some (edge.rhs, sumK + edge.k) else none

def checkDiffChain (src dst needK : Nat) (chain : List DiffLe) : Bool :=
  match chain.foldr checkDiffStep (some (src, 0)) with
  | some (endNode, totalK) => Nat.beq endNode dst && Nat.ble needK totalK
  | none => false

/-- Alignment mask subset check (`addr &&& alignMask == 0`) reduces to closed
    `Nat.land` equality via `rfl` without unfolding symbolic `BitVec` widths. -/
theorem nat_le_trans_add {a b c k1 k2 : Nat}
    (h1 : a + k1 ≤ b) (h2 : b + k2 ≤ c) : a + (k1 + k2) ≤ c := by
  have h1' : (a + k1) + k2 ≤ b + k2 := Nat.add_le_add_right h1 k2
  rw [Nat.add_assoc] at h1'
  exact Nat.le_trans h1' h2

end Anneal.SafetyCertExample
```

#### 4.3 Counterexamples Refuting Premature Conceptual Collapses (`C1`–`C2`)

1. **Counterexample 1 — Why `ub_checks` Runtime Booleans Cannot Replace `RegionSpan` / `ProtocolCap`:** Given adjacent allocations `allocA` at `[0x1000..0x1004)` and `allocB` at `[0x1004..0x1008)`, `ptr::copy_nonoverlapping(src = 0x1004 /* allocA end */, dst = 0x1005 /* allocB+1 */, 1)` satisfies `src.addr().abs_diff(dst.addr()) >= 1` (`maybe_is_nonoverlapping` returns `true`), yet dereferencing `src` is **immediate UB** due to invalid provenance (`InBound`). Likewise, double-freeing via `Box::from_raw(p)` passes every per-pointer check twice while violating linear `Owning`.
2. **Counterexample 2 — Why `PureLift` Cannot Collapse into Untyped `RegionSpan` Bytes:** Lowering every safe Rust local and tuple into raw `List AllocByte` spans with alignment/Tree-Borrows retags triggers `isDefEq` term blowup on trivial `&mut` borrows. Keeping pure safe values in `PureLift` (`spatial = .leaf`) and crossing via `freezeToSpatial` (`SpatialPin.lean`) keeps safe Rust `<50 ms` while handling `unsafe` aliasing locally.
3. **Counterexample 3 — Why `unsafe trait` Contracts Cannot Merge with Safe Trait Calls:** Safe `impl Read` or `impl Ord` callbacks may legally inspect uninitialized bytes (`Read`) or panic mid-mutation (`Ord` in `slice::sort`, guarded by `FreezeMarker` + `CopyOnDrop`). `ProtocolCap` must require `AdmissibleLibInv` at safe trait callbacks while admitting audited postconditions only for `unsafe trait`s (`TrustedLen`, `MetadataOf`).

---

### 5. `Trusted.MirSemantics` Coverage Ledger and Evaluation Rubric

`Basis: source + derived`

#### 5.1 Exact `Trusted.MirAst` / `Trusted.MirSemantics` Gap Matrix (`joshlf/anneal@c131b320eeeb`)

| Gap ID | Exact Source Anchor (`joshlf/anneal@c131b320eeeb`) | Blocked Safety / Rudra Pattern (Fails Closed to `.unsupported`) | Minimal Auditable `Trusted.*` Extension (Anchored to `lean-miri`) |
| :--- | :--- | :--- | :--- |
| **`G1`** | `MirSemantics.lean:803–804, 1686–1690` (`initState` rejects `!q.callerMem.allocations.isEmpty`; `isSupportedScalarOrUnitTy` L721–724 rejects `.ref`/`.rawPtr`) | Library entry points accepting `&T`, `&mut T`, `&[T]`, `*const T`, `*mut T` | Admit `.ref`/`.rawPtr` parameters pointing into live `q.callerMem.allocations` matching `Miri.Memory` descriptors |
| **`G2`** | `MirAst.lean:596–597, 625–626, 785–795`; `MirSemantics.lean:1407–1408` (non-empty `.projection`, `Deref`, `BinOp.offset`, `WithRetag.Yes`) | `Ptr2Ref`, `Allocated`, `InBound`, `!Overlap`, `Alias`, `ZstDualMode`, `Bucket::sub` | Byte-level `Allocation` read/write (`AllocByte` + `PtrVal`), `ProjectionElem.{deref, index}`, `BinOp.offset`, `PtrMetadata`, ZST `addr`, and `WithRetag` wired to `Miri/TreeBorrows` |
| **`G3`** | `MirAst.lean:612–618` (ADTs, unions, `CastKind.transmute`, non-tuple `Aggregate`, `Downcast`) | `Init` (`MaybeUninit<T>`), `!Padding` (`IntoBytes`), `Unwrap`, `ReprPrefixCompat` | Structural `MirTy.{struct_, union_, array, slice}`, `CastKind.transmute`, and `Downcast` |
| **`G4`** | `MirAst.lean` omits interior-mutability metadata on `MirTy` | `UnsafeCell`, `FreezeMarker` observation safety, sound CSE (`!Freeze`) | Export `isFreeze : Bool` from `rustc` `Ty::is_freeze` onto `MirTy` |
| **`G5`** | `MirAst.lean` lacks parametric `LayoutEnv` | Target-independent `Align`, `Size`, `!Padding` across `repr(Rust)` | `Program.layouts : LayoutTable` matching `Miri.ABI.Layout` |
| **`G6`** | `MirAst.lean:548–556, 782–795`; `MirSemantics.lean:1568–1569` (`RuntimeChecks(UbChecks)`, `.assert`, `.drop`, `.unwindResume`, `.unwindTerminate`) | `core::ub_checks` dual-profile verification, `PanicGuard`, Rudra panic-safety | `UbChecks : Bool` profile flag, `TerminatorKind.{assert, drop, unwindResume, unwindTerminate}` execution, `TerminalOut.{unwound, aborted}` |
| **`G7`** | `MirSemantics.lean:646–647, 1568–1569, 1599–1614` (`ValidChoice` pinned to `c = 0`; `.call` unsupported; single frame) | Multi-frame calls, `FnMut`/trait calls, `Atomic*` (`Send`/`Sync`), `InlineAsm`, `!Volatile` DMA | Multi-frame `Call` stack, `Atomic*` transitions, demonic `ValidChoice` for DMA/VMO, and open `.vis` traces for FFI/`InlineAsm`/traits |

#### 5.2 Mandatory 7-Axis Evaluation Matrix

| Criterion | `1. CertCheck` | `2. RegionSpan` | `3. BitValidity` | `4. TwoTrackUnwind` | `5. ProtocolCap` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **(T1) 0-TCB Bridge** | **0-TCB today** (`Init.*`); needs `G6` (`UbChecks`) | `PureLift` **0-TCB today**; raw spans need `G1`–`G2` | `LeBytes` **0-TCB today**; unions/pad need `G3`, `G5` | `wpOutcomeState` **0-TCB today**; pads need `G6` | Tokens **0-TCB today**; `UnsafeCell`/calls need `G4`, `G7` |
| **(P1) Spec Auditability** | High: clean arithmetic bounds in `Specs` | High: hides `AllocId`/`PermTree` details | High: matches `FromBytes`/`IntoBytes` | High: explicit normal post + panic guarantee | High: `PCM` tokens remain inside `Proof.*` |
| **(P2) Day-2 Locality** | High: reified `VarId` survives renumbering | High: `PTree` frames untouched fields | High: parametric `LayoutEnv` survives reorder | Very High: localizes cleanup to cutpoints | High: callers read `CallSummary` / `UnsafeTraitSummary` |
| **(P3) `v4.34.1` `<50ms` Scaling** | **Optimal (<5 ms)**: GMP `reduce_nat` (`rfl`) | **Good**: uses `@[irreducible]` cut firewalls | **Good**: reflection avoids `List` quantifiers | **High**: cutpoint sharing stops $O(2^k)$ blowup | **High**: opaque `CallSummary` bounds traversal |
| **(P4) Composability** | Safe `Assert`, `unchecked_*`, offsets | `PureLift` ↔ `*mut T` ↔ ZST ↔ `OpaqueDma` | Typed reads ↔ `copy_nonoverlapping` ↔ `#[repr(C)]` | Return ↔ `?` ↔ `Drop` ↔ `mem::forget` | Locks, refcounts, `Pin`, `Send`/`Sync`, `FnMut` |
| **(P5) Failure Legibility** | Names missing edge or mask bit | Reports `(AllocId, lo, hi, missingPerm)` | Names `.uninit` padding byte or invalid tag | Splits normal `onRet` vs. unwind `onUnw` fault | Names violated `PCM` token, `Send`/`Sync`, or `LibInv` |
| **(C1–C2) Minimality** | Unifies Farkas, alignment, and `Tnum` | Unifies `PureLift`, ZST dual, `.sub`, DMA | Unifies `FromBytes`, `IntoBytes`, `withspacer` | Minimal 2-lift over `MirWp` | Unifies ownership, locks, refcounts, trait contracts |

## Boundaries

- **Direct `Trusted.MirSemantics` execution of `RuntimeChecks`, pointers, `Drop`, `Assert`, and `Call` is `unsupported`:** At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted/MirAst.lean` (L548–556, L782–795) and `Trusted/MirSemantics.lean` (L803–804, L1568–1569, L1599–1614) step fail-closed to `.fault .unsupported` on `Operand::RuntimeChecks`, non-empty `q.callerMem`, pointer dereferences, `TerminatorKind.{assert, drop, call, unwindResume, unwindTerminate}`, and multi-frame stacks.
- **`core::ub_checks` runtime instrumentation is `known not to apply` as a complete formal specification:** Dynamic boolean checks in `ub_checks.rs` cannot observe cross-allocation provenance (`InBound`), uninitialized memory (`Init`), Tree Borrows tags (`Alias`), linear deallocation (`Owning`), or concurrent DMA writes (`!Volatile`), and `const_eval_select!` stubs alignment/overlap checks to `true` during CTFE.
- **`safety-tool` tag propagation checking is `known not to apply` as a soundness proof:** `safer-rust/safety-tags` (`v0.4.1`) checks syntactic tag alignment between `#[safety::requires]` and `#[safety::checked]` annotations without proving the underlying arithmetic, aliasing, or unwind obligations.
- **Concrete execution of `crossbeam` weak-memory interleavings and Starnix `hermetic_copy` machine instructions was `not examined`:** Both crates were inspected at their Rust `unsafe` interface and safety-comment boundaries without hardware execution.
- **Interprocedural false-negative rates of `Rudra`'s `UnsafeDataflowChecker` remain `unknown`:** As noted in `unsafe_dataflow.rs` (L163–165), Rudra skips functions without internal `unsafe` blocks and performs no cross-function taint propagation.

## Evidence

1. **Rao et al. (`arXiv:2504.21312v2`, DOI `10.48550/arXiv.2504.21312`), `safer-rust/safety-tags@52077ed142e618ddf2e694c9f552fc2c860644f8`, & `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`** (`2026-11-19`, `Basis: normative + documentation + source`): Table 2 (21 primitive tags, 4 compound tags), §4.4 (contract roles), §5.3 (Audit Rules I–III), §7.1–7.2 Table 3 (516 `libstd` APIs, 96.1% coverage, 27 fixed APIs / 61 tags, `Pin<Ptr>` exposure); `safety-tool/Cargo.toml` (v0.4.1); RFC PR `#3842`, PR `#3458`, RFC 3128.
2. **Empirical & Static Bug-Finding Literature (`Basis: normative`):** Evans et al., ICSE 2020 (`10.1145/3377811.3380413`); Astrauskas et al., OOPSLA 2020 (`10.1145/3428204`); Qin et al., PLDI 2020 (`10.1145/3385412.3386036`); Bae et al., *Rudra*, SOSP 2021 (`10.1145/3477132.3483570`); Cui et al., *SafeDrop*, TOSEM 2023 (`10.1145/3542948`).
3. **`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`** (`2026-11-19`, `Basis: source`): `src/analysis.rs:64-135`; `src/analysis/unsafe_dataflow.rs:149-284`; `src/analysis/send_sync_variance/mod.rs:74-142, 198-232`; `src/analysis/unsafe_destructor.rs:36-177`.
4. **`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` & `model-checking/verify-rust-std@a43ef3d40d9ff54b0c65c9f69005cb9d8c833c86`** (`2026-11-19`, `Basis: source + normative`): `library/core/src/ub_checks.rs:51-184`; `library/core/src/contracts.rs:1-25`; `library/core/src/ptr/mod.rs:549-735, 1399-1410`; `library/core/src/slice/raw.rs:124-195`; `library/core/src/slice/mod.rs:949-960, 1339-1510, 2054-2065, 2982-3034`; `library/alloc/src/vec/splice.rs:78-122`.
5. **Production Crate `// SAFETY:` Corpus (`2026-11-19`, `Basis: source`):**
   - `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897`: `zerocopy/src/pointer/inner.rs:65-102`; `zerocopy/src/wrappers.rs:239-269`; `zerocopy/src/split_at.rs:198-285`.
   - `rust-lang/hashbrown@f3e9f0fc110f55ca55d73d6eddc0bdf5e85eb223`: `src/raw.rs:428-474`.
   - `tokio-rs/bytes@67edc2b999d669eb4f471aff576e213dbcb58871`: `src/bytes.rs:1323-1365`.
   - `crossbeam-rs/crossbeam@a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`: `crossbeam-queue/src/array_queue.rs:247-272`.
   - `tock/tock@ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`: `kernel/src/collections/ring_buffer.rs:53-76`.
   - `asterinas/asterinas@7fecb4ffabc72d0767277a9ffb66168bc512034c`: `ostd/src/mm/dma/dma_coherent.rs:84-144, 177-190`.
   - Fuchsia Starnix (`https://fuchsia.googlesource.com/fuchsia@fa0843ce71880308fd4d114f7bf0e7d878faad24`): `src/starnix/lib/usercopy/src/lib.rs` (`slice_to_maybe_uninit_mut`, `copyout`, `copyin`, `do_hermetic_copy`).
6. **Anneal, Lean 4, & `lean-miri` (`2026-11-19`, `Basis: source`):** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/TrustedBoundary.lean:442-596`; `trusted/lean/Trusted/MirAst.lean:530-820`; `trusted/lean/Trusted/MirSemantics.lean:548-860, 1380-1720`; `theory/Anneal/MirWp.lean:1-120`; `theory/Anneal/PureLift/{SpatialPin,MirBridge}.lean`); `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`); `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`.

## Revalidation

1. **Check `core::ub_checks` gating and `RuntimeChecks` persistence:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/<sha>/library/core/src/ub_checks.rs | grep -n -E "pub const macro|pub\(crate\) const fn check_language_ub|pub use intrinsics::ub_checks"
   ```
   Verify whether `check_language_ub` remains suppressed in CTFE/Miri and whether `core::contracts` remains unstable.
2. **Check `safer-rust/safety-tags` tooling and tag updates:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/safer-rust/safety-tags/<sha>/safety-tool/Cargo.toml
   ```
3. **Check `Rudra` detector passes:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/sslab-gatech/Rudra/<sha>/src/analysis.rs | grep -n -A 45 "pub enum AnalysisKind"
   ```
4. **Check `joshlf/anneal` `Trusted.*` gap closure and Pass-1 allowlist:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/joshlf/anneal/<sha>/trusted/lean/Trusted/MirAst.lean | grep -n -C 5 "inductive Operand\|inductive TerminatorKind"
   curl --http1.1 -fsSL https://raw.githubusercontent.com/joshlf/anneal/<sha>/trusted/audit/TrustedBoundary.lean | grep -n -A 25 "def allowedTheoryTacticKinds"
   ```
   Confirm which of `G1`–`G7` remain `.unsupported` and whether `Init.Omega` or additional tactics remain excluded from Pass 1.
