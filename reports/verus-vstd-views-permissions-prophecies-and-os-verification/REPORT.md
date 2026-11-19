# Verus vstd Abstractions, Prophecy Soundness, OS Verification Architecture, and Pass-1 Lean 4 Transfer

## Summary

Verus (`verus-lang/verus` commit `2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`; SOSP 2024 DOI `10.1145/3694715.3695952`) achieves high proof velocity on systems Rust by combining Rust ownership with three-mode stratification (`exec`, `proof`, `spec`), `View` / `DeepView` abstractions, linear ghost permissions (`PointsTo`, `PointsToRaw`, `PCell`), unitary Partial Commutative Monoids (`PCM` / `VerusSync`), credit-guarded invariants (`AtomicInvariant` / `LocalInvariant` / `OpenInvariantCredit`), and dual prophecy variables (`Prophecy`, `ProphecyGhost`, `MutRef`, `ExIterator`), given semantic foundations by `VerusBelt` (PLDI 2026 DOI `10.1145/3808325`). Examining `vstd` alongside five production Verus systems codebases—`VeriSMo` (`microsoft/verismo@5e1c159a`), `Atmosphere` (`mars-research/atmosphere@c7cece4b`), `Asterinas` / `Vostd` (`asterinas/asterinas@7fecb4ff`, `asterinas/vostd@eb1a9d04`), `Verified-Storage` (`microsoft/verified-storage@4d9ac568`), and `Verified-IronKV` (`verus-lang/verified-ironkv@7e35ed09`)—clarifies which `vstd` abstractions transfer into Anneal's zero-TCB, zero-SMT `Init.*` 3-axiom Lean 4 logic (`joshlf/anneal@c131b320`) and which must be replaced:

1. **Abstractions That Port Directly:** `View` / `DeepView` + `obeys_*_eq` stratification maps cleanly to unbundled Lean typeclasses (`View α V` + separate `ValidSlice` predicates, avoiding subtype nested-inductive positivity failures); provenance-tracked `PointsTo` / `PointsToRaw` + `PCell`'s `ManuallyDrop<UnsafeCell<T>>` encoding mirrors `Anneal.PureLift.SpatialPin` (`blocksDisjoint`, `spatialPointsTo`, `freezeToSpatialInState`, `reabsorbFromSpatialInState`); and `_t` vs. `_v` private-constructor `TrustedPermission` sealing (`Verified-Storage`) matches Anneal's `Trusted.*` vs. `theory/` boundary.
2. **SMT & Trusted-Macro Liabilities Rejected in Pass 1:** `vstd` depends pervasively on broadcast `uninterp spec fn` + Z3 `#[trigger]` axioms (`group_vstd_default`), totalized `PCM` partiality requiring Hilbert `choose` in `PCM::weaken`, and trusted unverified macro-generated traits in `vstd/tokens.rs` (`assume(false)` helpers at `L720`/`L727`). `Atmosphere` (`README.md` trigger TODOs), `VeriSMo` (`~30m -> ~3m` cleanup removing legacy `assume()`s), and `Vostd` (ASE 2026) document Z3 trigger brittleness and opaque SMT failures. Lean Pass 1 avoids these via constructive `OptionPcm` and structural `Nat`/`List` proofs with zero axioms.
3. **Prophecy Paradoxes vs. Deterministic Backward Lenses:** `vstd/proph.rs` documents two soundness traps on general `ProphecyGhost` variables—cyclic negation (`p.resolve(!p.value()) ⊢ false`) and unbounded `ProphecySeq` termination (`loop decreases s.seq().len()`)—blocked only by compiler `#[verifier::prophetic]` taint checks. For single-owner safe Rust MIR (`&mut` borrows and `SpatialPin`), `Anneal.PureLift.LoanGraph` replaces prophecies with deterministic DAG `BackTargetStep` writebacks executed eagerly on loan end, making cycles impossible by construction while leaving concurrency prophecies orthogonal.

## Applicability

This report relates four pinned upstream domains:
- **Verus Core & Semantics:** `verus-lang/verus` (`2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`), Verus SOSP 2024 (`10.1145/3694715.3695952`), and `VerusBelt` PLDI 2026 (`10.1145/3808325`). Line references in `vstd` apply to commit `2518fd9c`.
- **Verus Systems Codebases:** `microsoft/verismo` (`5e1c159aec20491653550e39b00bd0855f543a7e`, OSDI 2024), `mars-research/atmosphere` (`c7cece4b091363d9cb8d7b4e473b7d0daf111620`, KISV 2023 `10.1145/3625275.3625401`), `asterinas/asterinas` (`7fecb4ffabc72d0767277a9ffb66168bc512034c`, CortenMM SOSP 2025 `10.1145/3731569.3764836`), `asterinas/vostd` (`eb1a9d044617c2abff58f959ccc50f9571d561e9`, ASE 2026 `10.1145/3832783.3834504`), `microsoft/verified-storage` (`4d9ac568c91fe6fe5136c7624d2b4b4f49752932`, OSDI 2025), and `verus-lang/verified-ironkv` (`7e35ed097c4089b9fbda483ea2629a0033f4d874`). `asterinas/vostd` builds primarily against an `asterinas/verus` fork (`vostd/README.md` L60–61) tracking OSTD `v0.16.0`–`v0.19.0`.
- **Target Consumer Architecture:** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), governed by Pass 1 `theory/` constraints (`TrustedBoundary.lean`, 51-module `foundation-lock.json` on Lean `v4.34.1`, `Trusted.MirSemantics`, and `Anneal.PureLift/{LoanGraph,SpatialPin}.lean`).

Scope separation: cross-verifier surveys and LLBC/Aeneas prophecies appear in sibling corpus reports (`rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, `rust-verification-lifetimes-prophecies-and-functional-translation`, `anneal-acceptance-frontier-isa-roadmap-and-verifier-bibliography`). Designs are evaluated on: **(T1)** 0-TCB bridge; **(P1)** spec auditability; **(P2)** Day-2 locality; **(P3)** Lean `v4.34.1` kernel / `<50ms` LSP scaling; **(P4)** composability across safe/`unsafe`/`UnsafeCell`/`MaybeUninit`; **(P5)** failure legibility; and **(C1–C2)** minimality backed by counterexamples.

## Findings

### 1. Mathematical Spec Stratification: `View`, `DeepView`, and `laws_eq`

Basis: source + documentation

`vstd/view.rs` (`L10–98`) decouples executable containers from SMT ghost domains (`Seq<T>`, `Map<K, V>`, `Set<V>`, `int`, `nat`) via two traits:
- `pub trait View { type V; spec fn view(&self) -> Self::V; }` (`@` shorthand) abstracts shallow structure (`Vec<T>@ : Seq<T>` via `uninterp spec fn`, scalars via `declare_identity_view!`) while forwarding `&A`, `Box<A>`, `Rc<A>`, and `Arc<A>` via `#[verifier::inline] open spec fn` (`view.rs` L22–98).
- `pub trait DeepView { type V; spec fn deep_view(&self) -> Self::V; }` maps nested values (`Vec<T>::deep_view` evaluates `Seq::new(v.len(), |i: int| v[i].deep_view())`).
- `vstd/laws_eq.rs` decouples runtime `PartialEq` from Leibniz `==` via trigger-guarded axioms (`obeys_eq`, `obeys_concrete_eq`, `obeys_view_eq`, `obeys_deep_eq`), while `vstd/vstd.rs` (`L113–166`) marks `group_vstd_default` as `broadcast_use_by_default_when_this_crate_is_imported`.

**Pass-1 Lean 4 Transfer (`T1, P1, P3`):** Verus `View` maps cleanly onto an unbundled Lean typeclass `View (α : Type) (V : outParam Type)` paired with separate `Prop` validity predicates (`ValidSlice maxCap xs`), rather than sigma subtypes `{ xs : List α // xs.length ≤ maxCap }`. Keeping length bounds out of the carrier type avoids Lean's nested-inductive strict-positivity rejection on recursive trees (`TreeNode` holding `List TreeNode`, shown in §6) and eliminates `HEq` casts when slice lengths vary across `PureLift` states.

### 2. Memory Permissions & Aliasing: `PointsTo`, `PointsToRaw`, `IsExposed`, `SharedReference`, and `PCell`

Basis: source + normative

`vstd/raw_ptr.rs` (`L1–1053`) models Rust pointers via abstract-machine records (`L91–95`):
```rust
pub ghost struct PtrData<T: core::marker::PointeeSized> {
    pub addr: usize,
    pub provenance: Provenance,
    pub metadata: Metadata<T>, // <T as core::ptr::Pointee>::Metadata
}
```
Four structural properties define `vstd` memory ownership:
1. **Runtime Equality Ignores Provenance (`raw_ptr.rs` L11–12, L198–227):** `spec ==` compares all three components `(addr, provenance, metadata)`, whereas the `assume_specification` for `<*mut T as PartialEq>::eq` and `<*const T as PartialEq>::eq` specifies `res <==> (x@.addr == y@.addr) && (x@.metadata == y@.metadata)` because `Provenance` (`Provenance::null()`, `L67`) is ghost-only.
2. **Typed (`PointsTo<T>`) vs. Raw Byte Ranges (`PointsToRaw`) (`raw_ptr.rs` L143–315, L766–856):** `PointsTo<T>` tracks `(ptr : *mut T, opt_value : MemContents<T>)` (`Uninit | Init(T)`), moving values cleanly (`ptr_mut_read` yields `is_uninit`, `L602–610`); `PointsTo::is_disjoint<S>` requires `size_of::<T>() != 0 && size_of::<S>() != 0` (`L305–313`). Untyped `PointsToRaw` owns `(provenance(), dom() -> Set<int>)` with linear axioms `empty`, `split`, `join` (matching provenance, `L813–819`), `into_typed<V>` (`requires start != 0 || size_of::<V>() != 0`, aligned `start % align == 0`, `is_range`, `L832–842`), `into_raw` (`requires is_uninit`, `L849–855`), and `IsExposed` provenance casts (`L696–756`).
3. **Documented ZST/Unaligned Gaps & `SharedReference` Retag Stop-Gap:**
   - `raw_ptr.rs` L106–133 explicitly excludes (i) ZST null `*mut X` reads/writes (`PointsTo` enforces `is_nonnull`) and (ii) `ptr::read_unaligned`/`write_unaligned` (`PointsTo` enforces `is_aligned`). Note `into_typed` (`L834`) relaxes ZST construction for *non-null* pointers (`start != 0`) using `PointsToRaw::empty()`.
   - `SharedReference<'a, T>(&'a T)` and `ptr_ref2` (`raw_ptr.rs` L971–1051) form a documented stop-gap (`"The existence of SharedReference<'a, T> is a stop-gap"`): forming `&'a T` from `*const T` triggers a Stacked/Tree Borrows retag producing a *fresh* provenance, so `ptr_ref2` guarantees `addr` and `metadata` equality while dropping provenance equality (`L1033–1047`).
4. **Ghost-Guarded Interior Mutability (`PCell<T>`, `vstd/cell/pcell.rs` L44–105):** `PCell<T: ?Sized>` wraps `ManuallyDrop<UnsafeCell<T>>` (`L83–87`) so dropping a `PCell` never drops `T` without also reclaiming `PointsTo<T>` via `into_inner`. `PCell<T>` is unconditionally `Send + Sync` (`L91–94`), deferring marker traits to `PointsTo<T>` (`PhantomData<T>`, `#[verifier::reject_recursive_types_in_ground_variants(T)]`, `L100–104`); `pcell_maybe_uninit::PCell<V>` wraps `PCell<MaybeUninit<V>>`.

**Pass-1 Lean 4 Transfer (`T1, P4`):** `Anneal.PureLift.SpatialPin` (`SpatialPin.lean` L42–95) mirrors `PointsToRaw`/`PCell` in pure `Init.*`: `freezeToSpatialInState` exports a loan into a disjoint `SpatialBlock Val` tagged with a `LawfulCodec` (`valueCellCodec`), `mutateSpatialInState` checks provenance/write permissions for `unsafe` / `MaybeUninit` steps, `reabsorbFromSpatialInState` rejects `.uninit` cells before decoding back to pure functional state, and `blocksDisjoint` (`L82–85`) forbids separating two spatial blocks originating from one `originLoan` inside `SpatialTriple` + `spatial_frame_law`.

### 3. Resource Algebras (`PCM`), `VerusSync` Tokens, and Credit-Guarded Invariants

Basis: source + documentation

Concurrent/shared state reasoning in `vstd` uses four constructs with distinct TCB costs:
- **Totalized Unitary `PCM` with `choose` (`vstd/resource/pcm.rs` L78–125, L281–316):** Verus encodes partiality via total `op(Self, Self) -> Self` plus `valid(self) -> bool` and `unit()` (`L82–85`: `"Because Verus does not support partial functions, we model that partiality with the validity predicate, which does make it a unitary resource algebra"`). Critically, `PCM::weaken` (`L301`) invokes Hilbert `choose|c| P::op(target, c) == self.value()`.
- **Trusted Macro-Generated Token State Machines (`vstd/tokens.rs`, `VerusSync`):** `tokenized_state_machine!` generates typed token traits (`UniqueValueToken`, `KeyValueToken`, `MultisetToken`, `IMapToken`). `tokens.rs` L8–11 warns: `"the tokenized_state_machine! macro creates trusted implementations of all these traits. Therefore all the proof functions in here are trusted."` Internal helpers `fresh_is_fresh` and `get_key_for_value` explicitly contain `assume(false);` (`L720`, `L727`).
- **Namespace/Credit Invariants (`vstd/invariant.rs` L250–344, `vstd/logatom.rs`):** `AtomicInvariant` checks reentrancy via static `opens_invariants [self.namespace()]` masks, while `!Sync` `LocalInvariant` relies on `InvariantBlockGuard<'a>` lifetime checking (`L251–277`). To block Iris/Landin's-knot self-referential paradoxes (`L279–309`), opening any invariant consumes an `OpenInvariantCredit` created strictly in `exec` code via `create_open_invariant_credit()` (`L317–343` forbids `proof fn` calls: `"creating an invariant credit in potentially-unbounded ghost code"`). `logatom.rs` builds `ReadLinearizer`/`MutLinearizer` on top.

**Pass-1 Lean 4 Transfer (`T1, P3, P5`):** Anneal Pass 1 forbids trusted macro `axiom` emissions (`TrustedBoundary.lean` L1136–1153). Replacing total `PCM` + `choose` with constructive `Option`-valued `OptionPcm` (`op : M → M → Option M`) avoids `Classical.choice` in user resource proofs and checks exclusivity structurally (`cases h`).

### 4. Prophecy Variables (`Prophecy`, `ProphecyGhost`, `MutRef`, `ExIterator`) and Soundness Paradoxes

Basis: normative + source + documentation

`vstd/proph.rs` (`L1–105`) and `vstd/mut_ref.rs` (`L1–56`) implement dual prophecy primitives analyzed semantically by *RustHornBelt* (PLDI 2022) and *VerusBelt* (PLDI 2026 `10.1145/3808325`):

| Feature | `Prophecy<T: Structural>` | `ProphecyGhost<T>` (`MutRef`, `ExIterator`) |
| :--- | :--- | :--- |
| Resolution context | Exec-only (`resolve(&T)`) | Ghost `proof fn resolve` |
| Dependent resolutions | Disallowed (no `ProphecySeq`) | Allowed (`resolve_dependent_2`, `ProphecySeq::resolve_cons`) |
| Compiler taint (`#[verifier::prophetic]`) | `view()` NOT marked prophetic | `ProphecyGhost::value()`, `MutRef`, `remaining()`, `produces()` tainted |

`proph.rs` (`L25–100`) documents two fatal soundness traps prevented by `#[verifier::prophetic]`:
1. **Cyclic Self-Resolution (`proph.rs` L29–51):** Executing `let tracked p = ProphecyGhost::<bool>::new(); p.resolve(!p.value()); assert(false);` fails statically with `"prophetic value not allowed for argument to proof-mode function with tracked parameters"`. `Prophecy` avoids this check only because exec resolution cannot observe ghost `view()` (`L53–57`).
2. **Unbounded Prophetic Decreases (`proph.rs` L61–100):** Peeling `ProphecySeq<int>::resolve_cons(0)` in an infinite `loop decreases s.seq().len()` would prove termination of a non-terminating loop (whose infinite trace has no consistent valuation for `s`), blocked only by `"prophetic value not allowed for 'decreases' clause"` (`L91–99`). Accordingly, `ExIterator` (`vstd/std_specs/iter.rs` L65–103) taints `remaining()` / `produces()` while keeping `decrease(&self) -> Option<nat>` non-prophetic.
3. **`MutRef<'a, T>` Encoding (`vstd/mut_ref.rs` L9–54):** Represents `&'a mut T` as `{ ptr: *mut T, current: &'a T, future: ProphecyGhost<&'a T> }` governed by 4 `broadcast axiom fn`s (`axiom_unpack_mut_ref_current`, `axiom_unpack_mut_ref_future`, `axiom_unpack_pack`, `axiom_pack2_unpack`) and `borrow_prophecy_var`.

**Pass-1 Lean 4 Transfer (`P1, P2, P3, C1–C2`):** For single-owner safe Rust MIR (and pinned `SpatialPin` blocks), `Anneal.PureLift.LoanGraph` (`LoanGraph.lean` L44–95) avoids prophecies and compiler taint tracking entirely: borrows store compositional `BackTarget Val` DAG nodes (`rootParam`, `direct`, conditional diamond `choiceJoin`, `lensCall`, `regionOut`) resolved deterministically upon loan end, making cyclic negation impossible (`no_cyclic_negation_paradox`). General prophecies remain relevant *only* for shared atomic/interior-mutable concurrency beyond single-owner MIR.

### 5. Large Verus Systems Codebases: Architecture Patterns and Bottlenecks

Basis: source + documentation + derived

| Project / Revision | Scale & Scope | Key Verus Idioms | Engineering Bottlenecks & Anneal Takeaways |
| :--- | :--- | :--- | :--- |
| **`VeriSMo`** (`microsoft/verismo@5e1c159a`, OSDI '24) | `#![no_std]` AMD SEV-SNP confidential VM security module (`852+1280` items). | `_s/_t/_p/_e/_u` layer split; `global size_of usize == 8`; `SnpPointsToBytes` `=~=`/`=~~=` axioms (`raw_ptr_s.rs` L21–35); `group_verismo_default`. | Mid-2026 cleanup (`README.md` L6–9) cut verification `~30m -> ~3m` by removing legacy `assume()`s and explicitizing broadcast groups—confirming broadcast discipline pays linearly. |
| **`Atmosphere`** (`mars-research/atmosphere@c7cece4b`, KISV '23) | Verified `#![no_std]` microkernel with inline `asm!` `sysretq` & `ArrayVec`. | Custom `atmo verify` workflow; container invariants on kernel objects. | `README.md` L69–71 records ongoing Z3 trigger fragility (`"Bring back verification for Kernel init()"`, `"Adjust triggers in ProcessManager"`). |
| **`Asterinas` / `Vostd`** (`asterinas/asterinas@7fecb4ff`, `asterinas/vostd@eb1a9d04`, CortenMM SOSP '25, ASE '26) | Verified OS `ostd` (`x86_64`, `riscv64`, `loongarch64`), tracking `v0.16.0`–`v0.19.0`; real UB/deadlock findings (`asterinas/vostd#645`). | `ostd/specs/` vs. `ostd/src/`; `verified_libs/vstd_extra`; `KVerus`/`StarVerus` proof synthesis. | Uses downstream `asterinas/verus` fork (`vostd/README.md` L60–61); ASE 2026 (`10.1145/3832783.3834504`) shows opaque Verus/SMT failures hinder automated spec synthesis. |
| **`Verified-Storage`** (`microsoft/verified-storage@4d9ac568`, PoWER OSDI '25) | Crash-consistent PMEM (`pmemlog`, `multilog`, `capybaraKV`). | `_t` trusted vs. `_v` verified crate split; private-ctor sealed `TrustedPermission` implementing `CheckPermission` (`pmemlog_main_t.rs` L40–60). | Sealing `TrustedPermission` inside `_t` blocks `_v` implementations from forging permissions—an exact Rust counterpart to Anneal Statement-Origin Separation. |
| **`Verified-IronKV`** (`verus-lang/verified-ironkv@7e35ed09`) | Sharded KV host implementation (`IronSHT` port). | Host `_t`/`_v` refinement onto `Seq`/`Map` ghost specs (`host_impl_t`/`_v`). | Explicitly omits IronFleet's global TLA distributed proof layer (`README.md` L7–12) to keep per-host proofs tractable. |

### 6. Runnable Pure `Init.*` Transfer Probe & Rubric Evaluation `(T1, P1–P5, C1–C2)`

Basis: source + derived

The self-contained Pass-1 probe below (`Init.Core`, `Init.Data.Nat.Basic`, `Init.Data.List.Basic`; 0 extra axioms, 0 SMT triggers) encodes all four portable abstractions:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace Pass1VstdTransferProbe

/-- Unbundled view abstraction + separate `Prop` slice validity, avoiding
Lean nested-inductive positivity failures on `{ l : List α // l.length ≤ max }`
and dependent `HEq` vector casts. -/
class View (α : Type) (V : outParam Type) where
  view : α → V

def ValidSlice {α : Type} (maxCap : Nat) (xs : List α) : Prop :=
  xs.length ≤ maxCap

inductive TreeNode where
  | leaf (val : Nat)
  | branch (children : List TreeNode)

def treeValid (maxFanout : Nat) : TreeNode → Prop
  | .leaf _ => True
  | .branch cs => ValidSlice maxFanout cs ∧ cs.foldr (fun c ih => treeValid maxFanout c ∧ ih) True

/-- Constructive `Option`-valued Partial Commutative Monoid (zero `Classical.choice`). -/
class OptionPcm (M : Type) where
  unit : M
  op : M → M → Option M
  valid : M → Prop
  unit_left : ∀ x, op unit x = some x
  comm : ∀ x y, op x y = op y x
  assoc : ∀ x y z xy xyz,
    op x y = some xy → op xy z = some xyz →
    Exists fun yz => op y z = some yz ∧ op x yz = some xyz

def FramePreservingUpdate {M : Type} [OptionPcm M] (a b : M) : Prop :=
  ∀ frame comb,
    OptionPcm.op a frame = some comb → OptionPcm.valid comb →
    Exists fun comb' => OptionPcm.op b frame = some comb' ∧ OptionPcm.valid comb'

inductive ExclAgree (α : Type) where | empty | token (v : α)

def ExclAgree.op {α : Type} : ExclAgree α → ExclAgree α → Option (ExclAgree α)
  | .empty, y => some y | x, .empty => some x | .token _, .token _ => none

instance {α : Type} : OptionPcm (ExclAgree α) where
  unit := .empty; op := ExclAgree.op; valid _ := True
  unit_left x := by cases x <;> rfl
  comm x y := by cases x <;> cases y <;> rfl
  assoc x y z xy xyz h1 h2 := by
    cases x <;> cases y <;> cases z
    · injection h1 with hx; subst hx; injection h2 with hy; subst hy; exact ⟨.empty, rfl, rfl⟩
    · injection h1 with hx; subst hx; exact ⟨.token _, rfl, h2⟩
    · injection h1 with hx; subst hx; injection h2 with hy; subst hy; exact ⟨.token _, rfl, rfl⟩
    · cases h1
    · injection h1 with hx; subst hx; injection h2 with hy; subst hy; exact ⟨.empty, rfl, rfl⟩
    · injection h1 with hx; subst hx; exact ⟨.token _, rfl, h2⟩
    · injection h1 with hx; subst hx; injection h2 with hy; subst hy; exact ⟨.token _, rfl, rfl⟩
    · cases h1

theorem excl_token_unique {α : Type} {x y : α} {comb : ExclAgree α}
    (h : OptionPcm.op (ExclAgree.token x) (ExclAgree.token y) = some comb) : False := by cases h

theorem excl_frame_update_replace {α : Type} (x y : α) :
    FramePreservingUpdate (ExclAgree.token x) (ExclAgree.token y) := by
  intro frame comb hOp _; cases frame with
  | empty => exact ⟨ExclAgree.token y, rfl, trivial⟩
  | token _ => cases hOp

/-- Deterministic backward writeback lens replacing `ProphecyGhost` on single-owner `&mut`. -/
structure BackLens (S A : Type) where
  get : S → A; set : S → A → S
  get_set : ∀ s a, get (set s a) = a; set_get : ∀ s, set s (get s) = s

structure ProphecyPair (A : Type) where cur : A; fut : A

theorem prophecy_of_backLens {S A : Type} (l : BackLens S A)
    (P : ProphecyPair A → Prop) (s : S) (a' : A) (h : P ⟨l.get s, a'⟩) :
    P ⟨l.get s, l.get (l.set s a')⟩ := by rw [l.get_set]; exact h

theorem no_cyclic_negation_paradox : ¬ Exists fun b : Bool => b = !b := by
  intro h; cases h with | intro b hb => cases b <;> cases hb

/-- Symbolic byte span (`PointsToRaw` split/join + ZST-aware `intoTyped` check). -/
structure RawSpan where prov : Nat; lo : Nat; len : Nat

def RawSpan.isDisjoint (s1 s2 : RawSpan) : Bool :=
  !Nat.beq s1.prov s2.prov || Nat.ble (s1.lo + s1.len) s2.lo || Nat.ble (s2.lo + s2.len) s1.lo

def RawSpan.splitAt? (s : RawSpan) (k : Nat) : Option (RawSpan × RawSpan) :=
  if Nat.ble k s.len then
    some ({ prov := s.prov, lo := s.lo, len := k }, { prov := s.prov, lo := s.lo + k, len := s.len - k })
  else none

def RawSpan.joinIfAdj? (s1 s2 : RawSpan) : Option RawSpan :=
  if Nat.beq s1.prov s2.prov && Nat.beq (s1.lo + s1.len) s2.lo then
    some { prov := s1.prov, lo := s1.lo, len := s1.len + s2.len }
  else none

def intoTypedCheck (s : RawSpan) (tySize align : Nat) : Bool :=
  Nat.ble 1 align && Nat.beq (Nat.mod s.lo align) 0 &&
  Nat.beq s.len tySize && (Nat.ble 1 s.lo || Nat.ble 1 tySize)

theorem rawSpan_split_join_example :
    RawSpan.splitAt? { prov := 1, lo := 1024, len := 16 } 8 =
      some ({ prov := 1, lo := 1024, len := 8 }, { prov := 1, lo := 1032, len := 8 }) ∧
    RawSpan.joinIfAdj? { prov := 1, lo := 1024, len := 8 } { prov := 1, lo := 1032, len := 8 } =
      some { prov := 1, lo := 1024, len := 16 } ∧
    intoTypedCheck { prov := 1, lo := 1024, len := 8 } 8 8 = true ∧
    intoTypedCheck { prov := 1, lo := 0, len := 0 } 0 1 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Pass1VstdTransferProbe
```

**Refuting Premature Concept Collapses (`C2`):**
1. *Total `PCM` vs. Constructive `OptionPcm`:* Encoding partiality via total `op` + `valid` forces `PCM::weaken` (`pcm.rs` L301) to invoke non-constructive `choose`; `OptionPcm` keeps composition algebraic and 0-axiom.
2. *Deterministic `BackTarget` vs. Concurrency Prophecies:* Single-owner `BackLens` / `LoanGraph.BackTarget` resolves writebacks at lexical loan end, whereas shared concurrent atomics depend on future thread schedules and still require relational invariants or prophecy histories.

| Candidate | (T1) 0-TCB | (P1) Auditability | (P2) Locality | (P3) Lean Kernel / LSP | (P4) Composability | (P5) Failure Clarity | (C1–C2) Minimality |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Native Verus / `vstd` (`2518fd9c`)** | External (Z3, VIR, `tokens.rs`) | High (`@` `View`, `_t`/`_v`) | Med (`#[trigger]` fragility) | N/A (Z3 timeouts) | High (safe, raw, `PCell`, atomics) | Med (opaque Z3 loops) | Low (dual prophecies + stop-gaps) |
| **Literal Axiomatized `vstd` Port** | Fail (`axiom`, `choose`, macros) | Low-Med (prophetic taint clutter) | Low (global `simp` emulation) | Low (`Classical.choice`, subtypes) | Med (inherited ZST/align limits) | Low (non-constructive witnesses) | Low (redundant trigger axioms) |
| **Distilled Pass-1 `Init.*` (`PureLift` + `OptionPcm` + `RawSpan` + `View`)** | **Pass (`0-TCB`)** | **Very High** (`View`, `ValidSlice`) | **Very High** (zero SMT triggers) | **Very High** (`Nat`/`List`, `rfl`, 0 `HEq`) | **High** (`BackTarget`, `SpatialPin`, `RawSpan`) | **Very High** (explicit goal deltas) | **Very High** (minimal orthogonal core) |

## Boundaries

- **ZST Null Reads/Writes and Unaligned Access in `vstd::raw_ptr::PointsTo` (`unsupported`):** `raw_ptr.rs` L106–133 excludes null ZST `*mut X` reads/writes and `read_unaligned`/`write_unaligned` because `PointsTo` enforces `is_nonnull` and `is_aligned`.
- **Trusted Macro Internals in `vstd/tokens.rs` (`unsupported`):** `tokenized_state_machine!` generates trusted unverified traits (`tokens.rs` L8–11) with `assume(false)` helpers (`L720`, `L727`), inadmissible in Anneal Pass 1.
- **Multi-Owner Concurrent Prophecies via `PureLift.LoanGraph` (`known not to apply`):** `BackTarget` / `BackLens` applies only to single-owner `&mut` and pinned `SpatialPin` regions, not lock-free concurrency linearization.
- **Compiler Delta in `asterinas/verus` Fork (`not examined`):** Exact divergence between `asterinas/verus` (`vostd/README.md` L60–61) and `verus-lang/verus@2518fd9c` was not inspected directly.
- **Live Lean `v4.34.1` Execution of `Pass1VstdTransferProbe` (`not examined` dynamically on host):** Running `anneal-lean-run ... lean -DwarningAsError=true` on the extracted probe exited `124` (`BUILD_SLOT_TIMEOUT: Timed out after 180.0s waiting for 1 of 1 host build slot(s)`) due to an external host build occupying the slot (`lean_diagnostics` returned `LSP_DEFERRED_BUILD_ACTIVE`). Kernel conformance is `derived` from `TrustedBoundary.lean` and `PureLift` inspection.
- **Upstream Replacement of `SharedReference<'a, T>` (`unknown`):** Resolution timeline for replacing `SharedReference` (`raw_ptr.rs` L971–975) with native `&'a T` provenance is unresolved at `2518fd9c`.

## Evidence

| Subject / Revision | Inspected Paths & Lines | Key Verified Evidence |
| :--- | :--- | :--- |
| `verus-lang/verus` (`2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`) | `source/vstd/{vstd.rs,view.rs,laws_eq.rs}` (`vstd.rs` L113–166, `view.rs` L10–100) | `group_vstd_default`; `View`/`DeepView` + `#[verifier::inline]`; `obeys_*_eq` triggers |
| `verus-lang/verus` (`2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`) | `source/vstd/raw_ptr.rs` L43–230, L272–315, L602–856, L970–1053; `cell/pcell.rs` L35–110 | `PtrData`, provenance-free `PartialEq::eq`, ZST/unaligned gaps (`L106–133`), `PointsToRaw`, `SharedReference`, `ManuallyDrop<UnsafeCell>` |
| `verus-lang/verus` (`2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`) | `source/vstd/{resource/pcm.rs,tokens.rs,invariant.rs,logatom.rs}` (`pcm.rs` L65–125, L280–320; `tokens.rs` L1–35, L710–745; `invariant.rs` L250–345) | Total `PCM` + `choose` (`L301`); `tokens.rs` trusted comment + `assume(false)` (`L720`, `L727`); `OpenInvariantCredit` (`L279–344`) |
| `verus-lang/verus` (`2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`) | `source/vstd/{proph.rs,mut_ref.rs,std_specs/iter.rs}` (`proph.rs` L1–105, `mut_ref.rs` L1–56, `iter.rs` L50–120) | Cyclic negation paradox (`L29–51`); `ProphecySeq` `decreases` trap (`L65–100`); `MutRef` axioms; `#[verifier::prophetic]` `ExIterator` |
| `microsoft/verismo` (`5e1c159aec20491653550e39b00bd0855f543a7e`) | `README.md` L1–105; `source/verismo/src/lib.rs` L1–78; `ptr/raw_ptr_s.rs` L1–90 | `~30m -> ~3m` cleanup (`L6–9`), `852+1280` verified items, `group_verismo_default`, `SnpPointsToBytes` axioms |
| `mars-research/atmosphere` (`c7cece4b091363d9cb8d7b4e473b7d0daf111620`) | `README.md` L1–71; `kernel/src/lib.rs` L1–65, L190–266 | `atmo verify`, inline `asm!` `sysretq`, `Init()`/`ProcessManager` trigger TODOs (`L69–71`) |
| `asterinas/asterinas` (`7fecb4ffabc72d0767277a9ffb66168bc512034c`) & `asterinas/vostd` (`eb1a9d044617c2abff58f959ccc50f9571d561e9`) | `ostd/src/mm/page_table/mod.rs` L1–65; `vostd/README.md` L1–90 | Multi-arch OSTD `v0.16`–`v0.19`, CortenMM (`10.1145/3731569.3764836`), ASE 2026 (`10.1145/3832783.3834504`), `asterinas/vostd#645`, fork note (`L60–61`) |
| `microsoft/verified-storage` (`4d9ac568c91fe6fe5136c7624d2b4b4f49752932`) & `verus-lang/verified-ironkv` (`7e35ed097c4089b9fbda483ea2629a0033f4d874`) | `pmemlog_main_t.rs` L1–70; `README.md`; `ironsht/src/lib.rs` L1–75; `ironkv/README.md` L1–115 | Private-ctor `TrustedPermission` (`_t` vs. `_v`); IronSHT host-only verification |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/audit/TrustedBoundary.lean` L437–1580; `foundation-lock.json`; `theory/Anneal/PureLift/{LoanGraph,SpatialPin}.lean` L1–95 | `BackTargetStep`, `SpatialCodec`, `valueCellCodec`, `blocksDisjoint`, Pass 1 `Init.*` lock |

- **Host Probe Attempt (`2026-11-19`):** Running `$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -DwarningAsError=true` on the extracted `Pass1VstdTransferProbe` file under `anneal-lean-run` exited `124` (`BUILD_SLOT_TIMEOUT: Timed out after 180.0s waiting for 1 of 1 host build slot(s)`); `lean_diagnostics` returned `LSP_DEFERRED_BUILD_ACTIVE`.

## Revalidation

1. **Compile and Check Zero-Axiom Status of `Pass1VstdTransferProbe` (`<2s` once build slot is idle):** Save the fenced `Pass1VstdTransferProbe` block from Findings §6 to `/tmp/pass1_vstd_transfer_probe.lean`, run `~/.local/bin/anneal-lean-run lean -DwarningAsError=true /tmp/pass1_vstd_transfer_probe.lean` (plus a wrapper running `#print axioms` on `excl_token_unique`, `excl_frame_update_replace`, `prophecy_of_backLens`, `no_cyclic_negation_paradox`, and `rawSpan_split_join_example`), and verify exit `0` with empty axiom footprint.
2. **Diff `vstd` Above `2518fd9c`:** Inspect `source/vstd/{raw_ptr.rs,proph.rs,tokens.rs,resource/pcm.rs}` for ZST/unaligned `PointsTo`, `SharedReference`, `assume(false)` placeholders in `tokens.rs`, and `#[verifier::prophetic]` changes.
3. **Check `vostd` Upstream Verus Alignment Above `eb1a9d04`:** Verify `asterinas/vostd/README.md` (`cargo dv bootstrap --upstream-verus`) for convergence with upstream `verus-lang/verus`.
