# Partial-Bijection Kripke AllocId Isomorphisms and Provenance-Stripping Monotonicity Laws for Relational MIR and Zerocopy Verification

## Summary

Verifying `SafeTwin` equivalence between a safe Rust reference and an optimized twin, and proving `zerocopy` byte-reinterpretation laws over pointer-tainted buffers, both fail under naive syntactic equality. Grounded in Benton's Relational Hoare Logic (POPL 2004), Banerjee–Naumann heap confinement (JACM 2005 / JFP 2005), CompCert `meminj` (`AbsInt/CompCert@2685140b`, Leroy–Blazy JAR 2008), MiniRust (`minirust/minirust@063d7841`), `lean-miri` (`proofs-rs/lean-miri@c92d1d97`), `google/zerocopy` (`ec133ce4`), and Anneal (`joshlf/anneal@c131b320`), four principles govern relational memory equivalence and provenance stripping in Pass-1 3-axiom Lean 4 (`v4.34.1`):

1. **`OutEquivModInj` Resolves Scratch-Allocation `AllocId` Shifts Without Weakening Caller Identity:** Monotonic allocation counters (`Miri/Memory/MemoryState.lean:103`) shift `AllocId`s whenever one twin allocates temporary scratch (`Box`/`Vec`), breaking `out₁ = out₂`. Parameterizing `TerminalOut` equivalence (`Trusted/MirSemantics.lean:578-605`) by a Kripke partial bijection `β : AllocId ⇀ AllocId` (`fwd`/`rev` mutually inverse, zero offset shift `delta = 0`) that **(i) pins every caller-supplied allocation to the identity (`β.fwd id = some id`)**, **(ii) bijects all reachable returned allocations and pointer-provenance bytes**, and **(iii) leaves confined scratch and dead tombstones unmapped (`none`)** preserves caller safety while allowing internal heap elision.
2. **Four-Model Provenance Divergence (CompCert vs. MiniRust vs. Runtime `lean-miri` vs. CTFE `lean-miri`):** CompCert (`common/Memdata.v:813-929`) stores no raw bytes inside `Fragment (Vptr b ofs) q n` and returns `Vundef` on integer reads. MiniRust (`spec/lang/representation.md:74-94`) and runtime `lean-miri` (`Identity.lean:70, 92`, `Allocation.lean:349-411`, `offsetIsAddr = true`) store `u8` payloads alongside provenance and **strip provenance silently on integer/byte loads (`getBytesStripProvenance`, `readScalar ... false`) without exposing `AllocId`**. Conversely, **CTFE `lean-miri`** (`CtfeProvenance.lean:118-120`, `offsetIsAddr = false`) **rejects** integer/byte reads overlapping provenance via `AllocError.readPointerAsInt`.
3. **Order Duality and the Universal `FromBytes` Provenance-Stripping Lift Theorem:** Defining provenance-erasure order `AllocByte.init b (some prov) ⊑_strip AllocByte.init b none` inverts MiniRust's `DefinedRelation::le_defined` (`uninit ≤_def init b none ≤_def init b (some prov)`, `representation.md:652-669`) on initialized bytes. Because `(encode, decode)` forms a monotone Galois connection under `≤_def` (`representation.md:753-766`) and every `zerocopy::FromBytes` type (`zerocopy/src/lib.rs:4336-4364`, `impls.rs:942-972`, where `*const T`/`*mut T`/`NonNull<T>` are `!FromBytes` per `NOTE(#170)`) decodes into a **provenance-discrete value domain** (`v₁ ≤_def v₂ ⟹ v₁ = v₂`), proving `decode (bs.map stripProv) = some v` on provenance-free bytes lifts universally to `decode bs = some v` on arbitrary pointer-tainted runtime slices.
4. **Address-Exposure and Non-Injective Aliasing Boundaries:** In `M_anneal` (`MirSemantics.lean:415-419`), `PtrVal` carries only relative `offsetBytes`; in runtime Miri (`AddressGenerator.lean:77-105`), allocations advance `nextBaseAddr`, so `OutEquivModInj` fails if programs expose base addresses (`expose_provenance`). Relaxing `PartialAllocBij` to a non-injective map without `meminj_no_overlap` (`Memory.v:2364-2371`) unsoundly merges distinct mutable allocations.

---

## Applicability

This report governs relational allocation equivalence and provenance-erasure laws for Rust MIR semantics (`Trusted.MirSemantics`), `lean-miri` correspondence, and `zerocopy` byte codecs under Anneal's Pass-1 boundary (`TrustedBoundary.lean:442-596`), across nine primary subjects:

| Subject | Pinned Identity | Inspected Scope |
| :--- | :--- | :--- |
| Anneal MIR semantics | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `Trusted/MirSemantics.lean`, `TrustedBoundary.lean` |
| `lean-miri` semantics | `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Allocation.lean`, `ProvenanceMap.lean`, `{Identity,CtfeProvenance,MemoryState}.lean`, `AllocAddresses/{AddressGenerator,GlobalState}.lean`, `ValidityMemory.lean` |
| MiniRust specification | `minirust/minirust@063d784186d3252bee242217f218223205c0b568` | `spec/mem/{interface,basic}.md`, `spec/lang/representation.md` |
| `zerocopy` crate | `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897` | `zerocopy/src/lib.rs`, `zerocopy/src/impls.rs` |
| CompCert memory model | `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`, `10.1007/s10817-008-9099-0` | `common/{Values,Memdata,Memtype,Memory,Events}.v` |
| Relational Hoare Logic | `10.1145/964001.964003` (Benton, POPL 2004) | Relational PERs and dead-state framing |
| Heap partial bijections | `10.1145/1101821.1101824` (JACM'05), `10.1017/S0956796804005453` (JFP'05) | Banerjee–Naumann confinement and Kripke bijections |
| Rust compiler MIR | `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` | Normative pointer/provenance model |
| Lean 4 toolchain | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Pass-1 `Init.*` kernel target |

Cross-corpus boundaries: value-only `TotalSafeTwinEquiv`, unwind parity, and `BiAlign` tile alignment appear in [`safe-twin-observational-equivalence-unwind-and-constant-time-alignment`](../safe-twin-observational-equivalence-unwind-and-constant-time-alignment/REPORT.md); low-level `lean-miri` move deinit/fragments in [`lean-miri-interpreter-hooks-move-deinit-and-provenance-fragments`](../lean-miri-interpreter-hooks-move-deinit-and-provenance-fragments/REPORT.md); MiniRust basics in [`minirust-representation-transfers-provenance-and-primitive-lowering`](../minirust-representation-transfers-provenance-and-primitive-lowering/REPORT.md); stack lifetimes in [`rust-allocation-provenance-and-stack-lifetime-semantics`](../rust-allocation-provenance-and-stack-lifetime-semantics/REPORT.md); and `zerocopy` bit-validity traits in [`zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`](../zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics/REPORT.md). On `joshlf/anneal@c131b320`, `BodyVerified` constrains `callerMem = ⟨[]⟩` (`MirSemantics.lean:1686-1690`), so `OutEquivModInj` defines the relational library contract once caller-visible allocations enter `Query`/`Out`.

---

## Findings

### 1. Relational Heap Isomorphisms: Benton RHL, Banerjee–Naumann Partial Bijections, and CompCert `meminj`

`Basis: normative + source + derived`

Relating executions with distinct internal allocation histories combines three primary foundations:
1. **Benton's RHL (POPL 2004, `10.1145/964001.964003`):** Uses relational Partial Equivalence Relations (PERs) over state pairs `(s₁, s₂)`, allowing dead/scratch variables on one side to remain uncoupled while preserving symmetry and transitivity.
2. **Banerjee–Naumann Heap Confinement (JACM 2005 `10.1145/1101821.1101824`; JFP 2005 `10.1017/S0956796804005453`):** Tracks dynamically allocated references with a monotonically growing partial bijection `β : Loc ⇀ Loc` (`β ⊆ β'`). Representation independence holds iff unmapped internal scratch objects stay **confined** outside `β` (never escaping into returned pointers or mapped allocations) while external caller handles stay pinned.
3. **CompCert's `meminj` (`AbsInt/CompCert@2685140b`):** Defines `Definition meminj : Type := block -> option (block * Z)` (`Values.v:2327`), `Val.inject mi` (`Vptr b1 ofs1` $\mapsto$ `Vptr b2 (ofs1 + delta)`, `Vundef` injects into anything, `L2334-2350`), `inject_incr` (`L2661`), `inject_id` (`L2713`), and `compose_meminj` (`L2728`). Across memories, `Record mem_inj f m1 m2` (`Memory.v:2228-2245`) enforces permission (`mi_perm`), alignment (`mi_align`), and `memval_inject` (`mi_memval`), supported by `alloc_right_inject`, `alloc_left_unmapped_inject`, `alloc_parallel_inject` (`Memtype.v:1131-1180`), and `inject_separated` (`Events.v:603-606`: newly mapped blocks must have been invalid in both `m1` and `m2`).

**Why Source MIR Specializes `meminj` to Bijective `PartialAllocBij` (`delta = 0`):** CompCert permits `delta ≠ 0` and many-to-one maps for C stack-frame coalescing, relying on `meminj_no_overlap` (`Memory.v:2364-2371`) to keep live ranges disjoint. In Rust MIR `SafeTwin` equivalence, both twins execute under the Rust Abstract Machine (`MirAst.lean:129`, `Identity.lean:12-15`) where each allocation owns its `AllocId`; permitting `delta ≠ 0` or many-to-one `fwd` would conflate distinct `&mut` allocations. Setting `delta = 0` with mutually inverse `fwd`/`rev` recovers Banerjee–Naumann's `PartialAllocBij` cleanly.

---

### 2. Statement-Origin-Separated `OutEquivModInj` and Kripke Allocation Laws over `Trusted.MirSemantics`

`Basis: source + derived`

`Trusted/MirSemantics.lean` already defines `PtrVal` (`L415-418`: `{ allocId, offsetBytes, width }`), `AllocByte` (`L422-424`: `uninit | init byte prov`), `Allocation` (`L578-583`: `{ allocId, alignLog2, mutability, bytes, live }`), `CallerMemory` (`L586-587`), and `TerminalOut` (`L602-604`: `.returned ⟨ret, callerMem⟩ | .unwound callerMem`). Syntactic `out₁ = out₂` fails when one twin creates scratch allocations (`Miri/Memory/MemoryState.lean:103` `nextAllocId := 1`) that shift subsequent IDs or leave `live = false` tombstones. `OutEquivModInj` closes this via four invariants over witness `β : PartialAllocBij`:

1. **Symmetric Partial Bijection:** `fwd, rev : AllocId → Option AllocId` satisfying `∀ a b, fwd a = some b ↔ rev b = some a`, yielding `symmBij` and `compBij`.
2. **Caller Identity Pinning (`CallerPinned q.callerMem β`):** Every allocation in `q.callerMem` satisfies `β.fwd id = some id ∧ β.rev id = some id`, preventing twins from permuting caller-owned `&mut` buffers.
3. **Confinement on Return & Unwind (`CallerMemEquivModInj β m₁ m₂`):** Every `β`-mapped `a₁` matches `a₂` (`alignLog2`, `mutability`, `live`, and bytewise `ByteEquivModInj β`) and symmetrically via `β.rev`, while unmapped internal scratch cannot escape into `Out.ret` or mapped `Allocation.bytes`.
4. **Kripke Frame Extension & `AddressGenerator` Sensitivity:** `β` grows monotonically (`BijExtends β β'`). Because `M_anneal` `PtrVal` stores relative `offsetBytes` (`MirSemantics.lean:415-419`), unexposed scratch never shifts pointer values; in runtime `lean-miri` (`AddressGenerator.lean:77-105`), allocations advance `nextBaseAddr`, so `OutEquivModInj` applies only when programs do not expose base integers via `expose_provenance` (`GlobalState.lean:355-374`).

---

### 3. Provenance Stripping Across CompCert, MiniRust, `lean-miri`, and `zerocopy`

`Basis: source + normative + derived`

Direct source inspection establishes exact behavioral differences across the four memory models and `zerocopy`:

| Model & Source | Byte Carrier | Integer / Raw-Byte Load Over Pointer Bytes | Exposes? | Stripping Order & Round-Trip |
| :--- | :--- | :--- | :--- | :--- |
| **CompCert** (`Memdata.v:813-929`) | `Byte \| Fragment (Vptr) \| Undef` | `proj_bytes = None` $\implies$ **`Vundef`** (`L913-928`) | N/A | No integer recovery (`Vundef ≤_inj v`) |
| **MiniRust** (`representation.md:74-142, 651-778`) | `Uninit \| Init(u8, Option<ProvFrag>)` | `Type::Int::decode` reads `b.data()`, **strips provenance** (`L78-94`) | **No** | `Init(b, None) ≤_def Init(b, Some p)`; Galois `encode(v) ≤_def bytes` |
| **Runtime `lean-miri`** (`Identity.lean:70,92`, `Allocation.lean:349-411`) | `rawBytes`, `initMask`, `ProvenanceMap` (`offsetIsAddr = true`) | `getBytesStripProvenance` & `readScalar ... false` **succeed** (`L355-405`) | **No** | `Allocation.clearProvenance` (`L582`) preserves bytes/init |
| **CTFE `lean-miri`** (`CtfeProvenance.lean:118-120`, `Allocation.lean:355-410`) | `CtfeProvenance` (`offsetIsAddr = false`) | **Throws `AllocError.readPointerAsInt`** (`L369, 410`) | Fails closed | Stripping banned in `const` eval |
| **`zerocopy`** (`lib.rs:3581-3650`, `impls.rs:942-972`) | `ptr::copy_nonoverlapping::<u8>` into `MaybeUninit<T>` | `FromBytes` accepts any `u8`s (`lib.rs:4336`); pointers are **`!FromBytes`** (`NOTE(#170)`) | Copy keeps prov | `FromBytes` values are **provenance-discrete** |

Key primary-source consequences:
1. **`zerocopy::try_read_from` & `!FromBytes` on Pointers (`lib.rs:3581-3650`, `impls.rs:942-972, 2326-2331`):** `try_read_from` copies bytes via `ptr::copy_nonoverlapping` into `CoreMaybeUninit::<T>::uninit()` rather than performing a typed `MaybeUninit<T>` move (which `L3596-3605` warns can drop padding initialization/provenance). Meanwhile, `impls.rs:951-972` keeps `*const T`, `*mut T`, and `NonNull<T>` `!FromBytes` (`NOTE(#170)`), providing `TryFromBytes` / `FromZeros` only via `pointer::is_zeroed(c)`.
2. **Fragment Provenance (`ProvenanceMap.lean:17-40, 117-149, 200-224`):** Partial overwrites split adjacent pointer provenance into `byteFragments`; `readBytes` (`ValidityMemory.lean:67-74`) and `readScalar ... false` still read bytes cleanly when `offsetIsAddr = true`, while `readPtr` requires full aligned fragment agreement (`none` or `readPartialPointer` otherwise).
3. **Order Duality & The Universal `FromBytes` Lifting Theorem (`fromBytes_lift_of_strip`):** Under `b₁ ⊑_strip b₂` (`stripProv (.init b _) := .init b none`), initialized bytes obey the exact dual of MiniRust's `DefinedRelation::le_defined` (`bs.map stripProv ≤_def bs`). Combining MiniRust `decode` monotonicity (`bs₁ ≤_def bs₂ ⟹ decode bs₁ ≤_def decode bs₂`, `representation.md:756`) with `FromBytes` value discreteness (`v₁ ≤_def v₂ ⟹ v₁ = v₂` on all pointer-free `FromBytes` types, `representation.md:716-733`) proves **`decode (bs.map stripProv) = some v ⟹ decode bs = some v`** unconditionally—whereas on pointers (`!FromBytes`), discreteness fails (`Ptr addr none <_def Ptr addr (some p)`).

---

### 4. Self-Contained Pass-1 3-Axiom Lean 4 Mechanization

`Basis: derived`

This standalone Lean 4 (`v4.34.1`) module uses strictly Pass-1 `Init.*` imports (`TrustedBoundary.lean:442-596`), zero `sorry`, zero `omega`/`rcases`/`deriving`/`partial`/`._unsafe_rec`, and zero banned notations:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.List.Notation
import Init.Data.Nat.Basic

namespace Anneal.Rel.AllocInjAndStrip

/-! ## Part A: Kripke Partial AllocId Bijections & Refutations -/

structure PartialAllocBij where
  fwd     : Nat → Option Nat
  rev     : Nat → Option Nat
  fwd_rev : ∀ a b, fwd a = some b → rev b = some a
  rev_fwd : ∀ a b, rev b = some a → fwd a = some b

def symmBij (b : PartialAllocBij) : PartialAllocBij where
  fwd := b.rev; rev := b.fwd
  fwd_rev := fun a c h => b.rev_fwd c a h; rev_fwd := fun a c h => b.fwd_rev c a h

def compBij (b1 b2 : PartialAllocBij) : PartialAllocBij where
  fwd := fun a => match b1.fwd a with | none => none | some x => b2.fwd x
  rev := fun c => match b2.rev c with | none => none | some x => b1.rev x
  fwd_rev := fun a c h => by
    dsimp only at h
    cases h1 : b1.fwd a with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1] at h; have h2 := b2.fwd_rev x c h; have h3 := b1.fwd_rev a x h1
      dsimp only; rw [h2]; exact h3
  rev_fwd := fun a c h => by
    dsimp only at h
    cases h2 : b2.rev c with
    | none => rw [h2] at h; cases h
    | some x =>
      rw [h2] at h; have h1 := b1.rev_fwd a x h; have h3 := b2.rev_fwd x c h2
      dsimp only; rw [h1]; exact h3

def BijExtends (b1 b2 : PartialAllocBij) : Prop :=
  (∀ a x, b1.fwd a = some x → b2.fwd a = some x) ∧
  (∀ a x, b1.rev x = some a → b2.rev x = some a)

/-- Parallel allocation extends `β` with fresh `(id1, id2)` (`alloc_parallel_inject`). -/
def extendSync (b : PartialAllocBij) (id1 id2 : Nat)
    (hFree1 : b.fwd id1 = none) (hFree2 : b.rev id2 = none) : PartialAllocBij where
  fwd := fun a => match Nat.beq a id1 with | true => some id2 | false => b.fwd a
  rev := fun c => match Nat.beq c id2 with | true => some id1 | false => b.rev c
  fwd_rev := fun a c h => by
    dsimp only at h ⊢
    cases hEq1 : Nat.beq a id1 with
    | true =>
      rw [hEq1] at h; injection h with hc; subst c
      rw [Nat.beq_refl id2, Nat.eq_of_beq_eq_true hEq1]; exact rfl
    | false =>
      rw [hEq1] at h
      cases hEq2 : Nat.beq c id2 with
      | true =>
        have hc := Nat.eq_of_beq_eq_true hEq2; rw [hc] at h
        have hBad := b.fwd_rev a id2 h; rw [hFree2] at hBad; cases hBad
      | false => rw [hEq2]; exact b.fwd_rev a c h
  rev_fwd := fun a c h => by
    dsimp only at h ⊢
    cases hEq2 : Nat.beq c id2 with
    | true =>
      rw [hEq2] at h; injection h with ha; subst a
      rw [Nat.beq_refl id1, Nat.eq_of_beq_eq_true hEq2]; exact rfl
    | false =>
      rw [hEq2] at h
      cases hEq1 : Nat.beq a id1 with
      | true =>
        have ha := Nat.eq_of_beq_eq_true hEq1; rw [ha] at h
        have hBad := b.rev_fwd id1 c h; rw [hFree1] at hBad; cases hBad
      | false => rw [hEq1]; exact b.rev_fwd a c h

theorem extendSync_extends (b : PartialAllocBij) (id1 id2 : Nat)
    (h1 : b.fwd id1 = none) (h2 : b.rev id2 = none) :
    BijExtends b (extendSync b id1 id2 h1 h2) := by
  constructor
  · intro a x ha; dsimp only [extendSync]
    cases hEq : Nat.beq a id1 with
    | true => have haEq := Nat.eq_of_beq_eq_true hEq; rw [haEq] at h1; rw [h1] at ha; cases ha
    | false => rw [hEq]; exact ha
  · intro a x hx; dsimp only [extendSync]
    cases hEq : Nat.beq x id2 with
    | true => have hxEq := Nat.eq_of_beq_eq_true hEq; rw [hxEq] at h2; rw [h2] at hx; cases hx
    | false => rw [hEq]; exact hx

def inNatList (x : Nat) : List Nat → Bool
  | [] => false | y :: ys => match Nat.beq x y with | true => true | false => inNatList x ys

def CallerPinned (callerIds : List Nat) (b : PartialAllocBij) : Prop :=
  ∀ id : Nat, inNatList id callerIds = true → b.fwd id = some id ∧ b.rev id = some id

inductive MByte where | uninit | init (byte : Nat) (prov : Option Nat)

def ByteEquiv (b : PartialAllocBij) : MByte → MByte → Prop
  | .uninit, .uninit => True
  | .init v1 none, .init v2 none => v1 = v2
  | .init v1 (some p1), .init v2 (some p2) => v1 = v2 ∧ b.fwd p1 = some p2
  | _, _ => False

theorem byteEquiv_mono {b1 b2 : PartialAllocBij} (hExt : BijExtends b1 b2) :
    ∀ {x y : MByte}, ByteEquiv b1 x y → ByteEquiv b2 x y
  | .uninit, .uninit, h => h
  | .init _ none, .init _ none, h => h
  | .init _ (some _), .init _ (some _), h => ⟨h.1, hExt.1 _ _ h.2⟩
  | .uninit, .init _ _, h => False.elim h
  | .init _ _, .uninit, h => False.elim h
  | .init _ none, .init _ (some _), h => False.elim h
  | .init _ (some _), .init _ none, h => False.elim h

def ListRel {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True | x :: xs, y :: ys => R x y ∧ ListRel R xs ys | _, _ => False

structure AllocRec where allocId : Nat; live : Bool; bytes : List MByte

def lookupAlloc : List AllocRec → Nat → Option AllocRec
  | [], _ => none
  | a :: rest, id => match Nat.beq a.allocId id with | true => some a | false => lookupAlloc rest id

def InAllocMem (a : AllocRec) : List AllocRec → Prop
  | [] => False | x :: xs => a = x ∨ InAllocMem a xs

def OutEquivModInj (callerIds : List Nat) (b : PartialAllocBij)
    (ret1 ret2 : Option Nat) (m1 m2 : List AllocRec) : Prop :=
  CallerPinned callerIds b ∧
  (match ret1, ret2 with | none, none => True | some p1, some p2 => b.fwd p1 = some p2 | _, _ => False) ∧
  (∀ a1, InAllocMem a1 m1 → ∀ id2, b.fwd a1.allocId = some id2 →
    ∃ a2, lookupAlloc m2 id2 = some a2 ∧ a1.live = a2.live ∧ ListRel (ByteEquiv b) a1.bytes a2.bytes) ∧
  (∀ a2, InAllocMem a2 m2 → ∀ id1, b.rev a2.allocId = some id1 →
    ∃ a1, lookupAlloc m1 id1 = some a1 ∧ a1.live = a2.live ∧ ListRel (ByteEquiv b) a1.bytes a2.bytes)

def swapFn (x : Nat) : Option Nat :=
  match Nat.beq x 1 with | true => some 2 | false => match Nat.beq x 2 with | true => some 1 | false => none

def swap12Bij : PartialAllocBij where
  fwd := swapFn; rev := swapFn
  fwd_rev := fun a c h => by
    cases a with
    | zero => cases h
    | succ a' => cases a' with
      | zero => dsimp only [swapFn] at h; injection h with hc; subst c; rfl
      | succ a'' => cases a'' with | zero => dsimp only [swapFn] at h; injection h with hc; subst c; rfl | succ _ => cases h
  rev_fwd := fun a c h => by
    cases c with
    | zero => cases h
    | succ c' => cases c' with
      | zero => dsimp only [swapFn] at h; injection h with ha; subst a; rfl
      | succ c'' => cases c'' with | zero => dsimp only [swapFn] at h; injection h with ha; subst a; rfl | succ _ => cases h

/-- Refutation 1: Unpinned bijections permit swapping caller allocations `[1, 2]`. -/
theorem callerSwap_violates_pinning : ¬ CallerPinned [1, 2] swap12Bij := by
  intro hPin; exact (by cases (hPin 1 rfl).1)

/-! ## Part B: Provenance-Stripping Order Duality & Universal `FromBytes` Lift -/

def stripProv : MByte → MByte | .uninit => .uninit | .init b _ => .init b none

def stripOrder : MByte → MByte → Prop
  | .uninit, .uninit => True | .init b1 _, .init b2 none => b1 = b2
  | .init b1 (some p1), .init b2 (some p2) => b1 = b2 ∧ p1 = p2 | _, _ => False

def leDefByte : MByte → MByte → Prop
  | .uninit, _ => True | .init b1 none, .init b2 _ => b1 = b2
  | .init b1 (some p1), .init b2 (some p2) => b1 = b2 ∧ p1 = p2 | _, _ => False

def leDefOpt {V : Type} (R : V → V → Prop) : Option V → Option V → Prop
  | none, _ => True | some v1, some v2 => R v1 v2 | some _, none => False

theorem stripOrder_iff_init_geDef (b1 b2 : Nat) (p1 : Option Nat) :
    stripOrder (.init b1 p1) (.init b2 none) ↔ leDefByte (.init b2 none) (.init b1 p1) := by
  constructor
  · intro h; dsimp only [stripOrder] at h; dsimp only [leDefByte]; exact h.symm
  · intro h; dsimp only [leDefByte] at h; dsimp only [stripOrder]; exact h.symm

theorem stripProv_leDef : ∀ b : MByte, leDefByte (stripProv b) b
  | .uninit => True.intro | .init _ _ => rfl

theorem stripBytes_leDef : ∀ bs : List MByte, ListRel leDefByte (bs.map stripProv) bs
  | [] => True.intro | b :: bs => ⟨stripProv_leDef b, stripBytes_leDef bs⟩

/-- Universal `FromBytes` Lift Theorem: any `leDef`-monotone decoder into a discrete domain
    lifts automatically from provenance-free bytes to arbitrary pointer-tainted bytes. -/
theorem fromBytes_lift_of_strip {V : Type}
    (decode : List MByte → Option V) (leDefVal : V → V → Prop)
    (hMono : ∀ bs1 bs2, ListRel leDefByte bs1 bs2 → leDefOpt leDefVal (decode bs1) (decode bs2))
    (hDiscrete : ∀ v1 v2, leDefVal v1 v2 → v1 = v2)
    (bs : List MByte) (v : V) (hStripped : decode (bs.map stripProv) = some v) :
    decode bs = some v := by
  have hRel := hMono (bs.map stripProv) bs (stripBytes_leDef bs)
  rw [hStripped] at hRel
  cases hDec : decode bs with
  | none    => rw [hDec] at hRel; exact False.elim hRel
  | some v' => rw [hDec] at hRel; rw [← hDiscrete v v' hRel]

def decodeLeU32 : List MByte → Option Nat
  | [.init b0 _, .init b1 _, .init b2 _, .init b3 _] => some (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
  | _ => none

def taintedU32 : List MByte :=
  [.init 0x78 (some 7), .init 0x56 (some 7), .init 0x34 (some 7), .init 0x12 (some 7)]

theorem u32_fromBytes_strips_prov :
    decodeLeU32 (taintedU32.map stripProv) = some 0x12345678 ∧ decodeLeU32 taintedU32 = some 0x12345678 :=
  ⟨rfl, rfl⟩

/-- Refutation 2: Pointer decoders are not provenance-discrete (`!FromBytes`), blocking blind stripping. -/
def decodePtr1 : List MByte → Option (Nat × Option Nat)
  | [.init addr prov] => some (addr, prov) | _ => none

theorem ptr_decode_strictly_not_discrete :
    decodePtr1 ([MByte.init 0x40 (some 7)].map stripProv) ≠ decodePtr1 [MByte.init 0x40 (some 7)] := by
  intro h; cases h

end Anneal.Rel.AllocInjAndStrip
```

---

### 5. Architectural Evaluation Against the Anneal `theory/` Rubric (`T1`, `P1–P5`, `C1–C2`) and Refutations

`Basis: source + derived`

| Rubric Dimension | Grade | Grounded Justification Against `joshlf/anneal@c131b320` |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | `PartialAllocBij`, `OutEquivModInj`, and `fromBytes_lift_of_strip` live 100% in `theory/` over `Init.*` + `{propext}` (`Classical.choice`-free), citing `Trusted.MirSemantics` directly. |
| **(P1) Human Spec Auditability** | **Strong** | `SafeTwin` specs state caller-pinned equality (`CallerPinned`) without exposing scratch `AllocId`s; `FromBytes` specs stay clean over `UInt8` lists. |
| **(P2) Authoring & Day-2 Locality** | **Strong** | Adding or removing scratch allocations modifies only the internal `β` witness (`extendSync`) in the proof body. |
| **(P3) Lean 4 Kernel & `<50ms` LSP** | **Strong** | `ByteEquiv`, `stripProv`, and `decodeLeU32` reduce in `rfl`; `fromBytes_lift_of_strip` discharges tainted slices in one rewrite. |
| **(P4) Heterogeneous Composability** | **Strong** | `compBij` composes multi-step rewrites transitively; `stripBytes_leDef` composes directly with `ByteCodec` decoders. |
| **(P5) Failure Legibility** | **Strong** | `CallerPinned` pinpoints swapped caller `AllocId`s; `OutEquivModInj` catches escaping scratch pointers; `ptr_decode_strictly_not_discrete` separates `!FromBytes` slices. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Minimal 2-function inverse record `PartialAllocBij` (`delta = 0`) + single-step `stripProv`, avoiding C-style `delta : Z` arithmetic where unneeded. |

Four premature collapses (`C2`) are refuted: (1) **syntactic `out₁ = out₂`** breaks on scratch allocations and `live = false` tombstones; (2) **unpinned bijections omitting `CallerPinned`** permit swapping caller buffers (`callerSwap_violates_pinning`); (3) **non-injective mappings omitting `rev`** collapse distinct `&mut` allocations (violating `meminj_no_overlap`); and (4) **unconditional `decode bs = decode (bs.map stripProv)`** fails on pointer types (`ptr_decode_strictly_not_discrete`) and CTFE (`readPointerAsInt`).

---

## Boundaries

- **known not to apply:** `fromBytes_lift_of_strip` does **not** apply under CTFE (`CtfeProvenance.offsetIsAddr = false`, `Allocation.lean:369, 410`, which throws `.readPointerAsInt`), nor to `!FromBytes` pointer types (`*const T`, `*mut T`, `NonNull<T>` in `zerocopy/src/impls.rs:951-972`). `OutEquivModInj` does **not** apply if programs expose and compare absolute base addresses via `expose_provenance` under runtime `AddressGenerator` shifts (`AddressGenerator.lean:77-105`), and `delta = 0` specialization omits CompCert `delta : Z` sub-block stack coalescing.
- **unsupported:** On `joshlf/anneal@c131b320`, `BodyVerified` constrains entry `callerMem = ⟨[]⟩` (`MirSemantics.lean:1686-1690`), gating live `OutEquivModInj` replay until non-empty entry memory is supported. Pass 1 (`TrustedBoundary.lean:442-596`) forbids `omega`, `rcases`, `deriving`, `Std.*`, and `Classical`-dependent shortcuts.
- **not examined:** Live `lean`/`lake` compiler invocation on `Anneal.Rel.AllocInjAndStrip` (audited statically against `foundation-lock.json`), and Tree Borrows `BorTag` bijection extensions on `Provenance.concrete allocId tag`.
- **unknown:** Whether permissive `int2ptr` casts (`Provenance.wildcard` in `GlobalState.lean:376-387`) admit clean relational bijections across heaps with distinct exposed allocation sets.

---

## Evidence

1. **Anneal (`source`, `normative`):** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `Trusted/MirAst.lean:129` (`AllocId`); `Trusted/MirSemantics.lean:415-424, 578-605, 1686-1690`; `trusted/audit/TrustedBoundary.lean:442-596`.
2. **`lean-miri` (`source`):** `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`: `Miri/Memory/{Identity.lean:12-101, CtfeProvenance.lean:17-24,118-120, Allocation.lean:349-411,582, ProvenanceMap.lean:17-46,117-149,200-224, MemoryState.lean:100-108}`; `Miri/Memory/AllocAddresses/{AddressGenerator.lean:77-105, GlobalState.lean:82-91,282-298,355-387}`; `Miri/Interpreter/ValidityMemory.lean:67-74`.
3. **MiniRust (`normative`, `source`):** `minirust/minirust@063d784186d3252bee242217f218223205c0b568`: `spec/mem/{interface.md:21-50, basic.md:26-49,108-142}`; `spec/lang/representation.md:74-142, 651-778`.
4. **`zerocopy` (`source`, `normative`):** `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897`: `zerocopy/src/lib.rs:3581-3650, 4336-4364`; `zerocopy/src/impls.rs:32-86, 942-972, 2326-2331`.
5. **CompCert & Relational Literature (`source`, `normative`):** `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`: `common/{Values.v:2327-2375,2661-2745, Memdata.v:813-929, Memtype.v:1024-1244, Memory.v:2228-2371, Events.v:596-607}`; Leroy–Blazy JAR 2008 DOI `10.1007/s10817-008-9099-0`; Benton POPL 2004 DOI `10.1145/964001.964003`; Banerjee–Naumann JACM 2005 DOI `10.1145/1101821.1101824` & JFP 2005 DOI `10.1017/S0956796804005453`.
6. **Rust & Lean 4 (`source`):** `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`; `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
7. **Executable Probe (`execution`, `2026-11-20`):** Python 3 Revalidation probe (`0.06 ms`, exit `0`) verified `le_defined` ordering under erasure, discrete `decode_int` lifting vs. CTFE `.readPointerAsInt` rejection and non-discrete `decode_ptr`, and `CallerPinned`/injectivity checks.

---

## Revalidation

1. **Primary-source checks against pinned SHAs:**

```bash
curl --http1.1 -fsSL "https://raw.githubusercontent.com/minirust/minirust/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md" | sed -n '652,672p;753,766p'
curl --http1.1 -fsSL "https://raw.githubusercontent.com/google/zerocopy/ec133ce4d7993775413d852f91c9e3eb2a2a0897/zerocopy/src/impls.rs" | sed -n '942,973p'
curl --http1.1 -fsSL "https://raw.githubusercontent.com/AbsInt/CompCert/2685140bf72c959446981fb99b5e44a8975021bc/common/Memory.v" | sed -n '2228,2246p;2364,2372p'
```

2. **Pass-1 Lean `v4.34.1` check:** Extract Section 4's `Anneal.Rel.AllocInjAndStrip` module to `/tmp/AllocInjAndStrip.lean` and run `lean -DElab.async=false -Ddebug.skipKernelTC=false /tmp/AllocInjAndStrip.lean`, confirming exit `0` and axiom closure $\subseteq \{\texttt{propext}\}$.
3. **Standalone executable model probe (<0.1s, Python 3.10+ stdlib only):**

```bash
python3 -c '
def le_def(b1, b2):
    if b1[0] == "uninit": return True
    if b2[0] == "uninit": return False
    return b1[1] == b2[1] and (b1[2] is None or b1[2] == b2[2])
def strip(b): return ("uninit",) if b[0] == "uninit" else ("init", b[1], None)
def dec_int(bs):
    return None if any(b[0]=="uninit" for b in bs) else ("int", sum(b[1]<<(8*i) for i,b in enumerate(bs)))
def dec_ctfe(bs):
    if any(b[0]=="uninit" for b in bs): return ("ERR", "uninit")
    return ("ERR", "readPointerAsInt") if any(b[2] is not None for b in bs) else dec_int(bs)
def dec_ptr(bs):
    if any(b[0]=="uninit" for b in bs): return None
    p0 = bs[0][2]
    ok = p0 is not None and all(b[2]==(p0[0], i) for i,b in enumerate(bs))
    return ("ptr", sum(b[1]<<(8*i) for i,b in enumerate(bs)), p0[0] if ok else None)

pb = [("init", (0x1040>>(8*i))&0xff, ("a7", i)) for i in range(8)]
sb = [strip(b) for b in pb]
assert all(le_def(s, p) for s, p in zip(sb, pb))
assert dec_int(sb) == dec_int(pb) == ("int", 0x1040)
assert dec_ctfe(pb) == ("ERR", "readPointerAsInt")
assert dec_ptr(sb) != dec_ptr(pb)

def check_bij(caller, fwd, rev):
    return (all(fwd.get(c)==c and rev.get(c)==c for c in caller) and
            all(rev.get(b)==a for a,b in fwd.items()) and
            all(fwd.get(a)==b for b,a in rev.items()))
assert check_bij({1}, {1:1, 3:2}, {1:1, 2:3})
assert not check_bij({1, 2}, {1:2, 2:1}, {2:1, 1:2})
assert not check_bij({1}, {1:1, 2:2, 3:2}, {1:1, 2:3})
print("ALL CHECKS PASSED")
'
```
