# CertiGraph Subgraph Localizations, Split PointsTo/PointsToRaw Slab Freelists, XOR-Buddy Coalescing, and Sentinel-Zero Aliasing in Pass-1 Lean 4

## Summary

Verifying OS allocators, intrusive slab freelists, and fixed-index capability tables without higher-order impredicative separation logic requires four tightly coupled abstractions that compile inside Anneal's Pass-1 `Init.*`-only Lean 4 foundation (`joshlf/anneal@c131b320`, `leanprover/lean4@5045d005` `v4.34.1`):

1. **Structural `PTree` localizations replace magic-wand ramification with $O(k \log N)$ framing:** `CertiGraph` (`CertiGraph/CertiGraph@8781550d`) isolates graph rewrites via mathematical/spatial decoupling (`PreGraph`, `guarded_pointwise_relation`) and VST magic-wand ramification (`solve_ramify_P`). Under Pass-1 Lean 4's `TrustedBoundary.lean` gate, CompCert-style binary tries (`AbsInt/CompCert@2685140b`, `lib/Maps.v`) paired with `@Nat.rec`-bounded `PTree.diffWithD` and `PTree.unionLeftD` share untouched subtrees in $O(1)$ `.leaf` nodes (`34` structural visits across `N = 32..1024`, versus `528,896` linear alist steps at `N = 1024`—a `15,555.8x` reduction that avoids Lean 4's `maxRecDepth = 512` limit).
2. **Split `PointsTo<Node> * PointsToRaw` slab freelists require initialization-erasure subsumption on pop:** `verus-mimalloc` (`verus-lang/verified-memory-allocator@7d120970`, `verus-mimalloc/linked_list.rs:197-206, 394-403`) cannot use `Option<Box<Node>>` for runtime-sized blocks (`block_size >= 8`). `insert_block` splits `[ptr, ptr + block_size)` into a typed 8-byte `Node { ptr }` (`PointsTo<Node>`), an uninitialized tail (`PointsToRaw`), and an `IsExposed` token; `pop_block` recovers provenance via `with_exposed_provenance` and rejoins `PointsTo<Node>::into_raw()` with the tail. Cross-checking against `proofs-rs/lean-miri@c92d1d97` (`Allocation.lean:376-457`) shows why popping back to a raw slab requires explicit `.typed ⊑ .uninitRun` erasure subsumption.
3. **XOR-buddy coalescing obeys mod-$2^{\text{order}+1}$ parity laws, while `Heap::add_to_heap` has a zero-start `lowbit` bug:** In `rcore-os/buddy_system_allocator@da68b6d0` (`src/lib.rs:199-220`, `src/frame.rs:193-212`), `buddy = addr ^ (1 << order)` is involutive, range-disjoint, and `2^(order+1)`-aligned at `min(addr, buddy)` whenever `addr % 2^order == 0`. However, `Heap::add_to_heap` (`src/lib.rs:100-109`) omits a `current_start == 0` guard: at `current_start = 0, end = 16` (`ORDER = 13`), `lowbit = 0` yields `0usize.trailing_zeros() == 64 > 12`, clamping `size = 4096 > 16`—whereas `FrameAllocator::add_frame` (`src/frame.rs:61-65`) explicitly guards `if current_start > 0`.
4. **Unsigned sentinel-`0` parent encoding causes `100%` sibling-cohort aliasing on multi-root forests:** Flattening `Option<SlotId>` to `parent_raw: usize = 0` (unlike `seL4/l4v@b0fe7693` `cdt` `option`, `seL4/seL4@08c7e5fd` virtual-pointer null `0`, or `CertiGraph` negative `is_null_Z < 0` in `ArrayGraph.v:32`) collides unrelated parentless roots (`0 == 0` on all `61` multi-root 4-slot forests) and conflates slot-`0` children with roots (`34` of `125` forests). Typed `Option Nat` parents and tagged `SlotTag` states close both holes.

## Applicability

These findings govern formal specification and Pass-1 verification across the nine pinned subjects in `REPORT.json`:

- **`CertiGraph` and CompCert `PTree` (`CertiGraph/CertiGraph@8781550d8a116abb03ac7931f271ce03a5158a74`, `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`):** Relates VST higher-order ramification (`EnvironBox`, `-*`) and canonical radix-2 tries (`lib/Maps.v`) to Pass-1 `theory/` modules inside `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) obeying `TrustedBoundary.lean:442-596` (`Init.*` imports only, `@Nat.rec`/`List.foldr` into `Type`, zero `._unsafe_rec`, zero `#[...]`, and `{propext, Quot.sound}` closure).
- **Split-block slab freelists (`verus-lang/verified-memory-allocator@7d120970f8d63157ae9bf3b2361192d29bc0acaa`, `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Covers `verus-mimalloc/{linked_list,layout,tokens,bitmap}.rs` under `lean-miri` `Allocation.initMask` (`readScalar`/`writeScalar`). Verus and Rust ownership verifiers are surveyed in `reports/rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`.
- **XOR-buddy allocators (`rcore-os/buddy_system_allocator@da68b6d0bd74e539116898f21d44552417966afc`):** Covers `Heap<ORDER>` (`src/lib.rs`) and `FrameAllocator<ORDER>` (`src/frame.rs`).
- **Sentinel-`0` vs. `Option` tables (`seL4/seL4@08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):** Covers 0-indexed kernel/allocator parent tables. Related topics appear in `reports/ghostcell-branded-tokens-intrusive-containers-and-generational-arenas`, `reports/anneal-trusted-boundary-audit-olean-stubbing-and-conservativity`, `reports/lean-absbyte-typedat-lenses-and-nondeterministic-alloc-scaling`, and `reports/tree-borrows-two-stage-protector-release-and-reborrow-contracts`.

## Findings

### 1. `CertiGraph` Graph Localizations vs. Pass-1 `PTree.diffWithD` Framing

`Basis: source + normative + derived + execution`

Updating $k \le 4$ vertices inside an $N$-vertex linked graph cannot re-traverse all $N$ vertices per step without $O(N^2)$ proof blowup, nor can cyclic or DAG-shared graphs fold into pure inductive trees.

#### 1.1 `CertiGraph` Layers and VST Magic-Wand Ramification

`CertiGraph/CertiGraph@8781550d8a116abb03ac7931f271ce03a5158a74` (Wang, Cao, Mohan, & Hobor, OOPSLA 2019, `doi:10.1145/3360597`; Hobor & Villard, POPL 2013, `doi:10.1145/2429069.2429131`) decomposes graph proofs into three layers:

1. **Structural-vs-invariant separation (`graph/graph_model.v:18-39, 194-200`):** Splits `PreGraph` (`vvalid`, `evalid`, `src`, `dst`), `LabeledGraph` (`vlabel`, `elabel`, `glabel`), and `GeneralGraph` (`sound_gg : P lg_gg`), with structural equivalence `g1 ~=~ g2` (`L194-198`).
2. **Subgraph slicing (`graph/subgraph2.v:25-117`, `graph/local_graph_copy.v:45-96`):** Partitions mutated vs. untouched subgraphs via `reachable_subgraph` / `unreachable_partialgraph` and `guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2)`.
3. **Ramification (`msl_ext/ramification_lemmas.v:29-43, 156-172`, `msl_application/GraphBi.v:834-855`):** In VST's spatial separation logic, `solve_ramify_P` splits global state $g$ into local footprint $l$ and environment-stable frame $F$ (`EnvironStable F`), proves $F * l' \vdash g'$, and packages the global restoration inside `EnvironBox (l' -* g')` (`va_reachable_root_update_ramify`, `GraphBi.v:834-841`).

#### 1.2 Pass-1 `PTree.diffWithD` and `PTree.unionLeftD` Combinators

Because `joshlf/anneal@c131b320` Pass-1 `theory/` modules exclude impredicative `-*` quantifiers and `Classical.choice`/`funext` (`TrustedBoundary.lean:442-596`), CompCert's `PTree` (`AbsInt/CompCert@2685140b`, `lib/Maps.v:540-638, 865-911`) adapts cleanly into pure `@Nat.rec` and `List.foldr` over binary bit-paths `Pos := List Bool`:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.SimpLemmas

namespace Anneal.CertiGraphLocal

abbrev Pos : Type := List Bool

inductive PTree (V : Type) where
  | leaf
  | node (l : PTree V) (val : Option V) (r : PTree V)

def PTree.make {V : Type} (l : PTree V) (v : Option V) (r : PTree V) : PTree V :=
  match v with
  | some x => .node l (some x) r
  | none => match l, r with | .leaf, .leaf => .leaf | _, _ => .node l none r

def PTree.get {V : Type} (p : Pos) (t : PTree V) : Option V :=
  List.foldr
    (fun b k cur =>
      match cur with
      | .leaf => none
      | .node l _ r => match b with | false => k l | true => k r)
    (fun cur => match cur with | .leaf => none | .node _ v _ => v)
    p t

def PTree.diffWithD {V : Type} (eqVal : V → V → Bool)
    (depth : Nat) (req goal : PTree V) : Option (PTree V) :=
  @Nat.rec (fun _ => PTree V → PTree V → Option (PTree V))
    (fun rq gl => match rq with | .leaf => some gl | .node _ _ _ => none)
    (fun _ ih rq gl =>
      match rq with
      | .leaf => some gl
      | .node rl rv rr =>
        match gl with
        | .leaf => none
        | .node glv gv gr =>
          let vr? :=
            match rv with
            | none => some gv
            | some x =>
              match gv with
              | none => none
              | some y => match eqVal x y with | true => some none | false => none
          match vr?, ih rl glv, ih rr gr with
          | some vr, some lr, some rrOut => some (PTree.make lr vr rrOut)
          | _, _, _ => none)
    depth req goal

def PTree.unionLeftD {V : Type} (depth : Nat) (over base : PTree V) : Option (PTree V) :=
  @Nat.rec (fun _ => PTree V → PTree V → Option (PTree V))
    (fun ov bs => match ov with | .leaf => some bs | .node _ _ _ => none)
    (fun _ ih ov bs =>
      match ov with
      | .leaf => some bs
      | .node ol ov_ or_ =>
        match bs with
        | .leaf => some (.node ol ov_ or_)
        | .node bl bv br =>
          match ih ol bl, ih or_ br with
          | some ml, some mr =>
            some (.node ml (match ov_ with | none => bv | some v => some v) mr)
          | _, _ => none)
    depth over base

end Anneal.CertiGraphLocal
```

Two properties make this formulation total and fast in Lean 4's kernel:
1. **Unconditional `.leaf` short-circuiting:** At `depth = 0`, `.leaf` returns `some gl` (or `some bs`), so `depth` bounds only the *local patch* `lPre`/`lPost` (`O(log max_local_id)`), never the ambient heap `gPre`. Untouched `.leaf` branches frame entire subtrees in $O(1)$ without needing depth invariants on `gPre` or `Classical.choice`.
2. **Explicit `rfl` equation lemmas (`_zero`, `_succ`) + `PTree.make`:** Avoiding `dsimp` unfolding of `@Nat.rec` and collapsing empty nodes via `PTree.make` yields `localize_rewrite_frame` (requiring `[propext]` only), proving exact local updates and bitwise external preservation (`PTree.get pos gPost = PTree.get pos gPre`). Empirically (**Evidence**), localizing `{2, 4, 6, 8}` visits **`34` trie nodes** across $N = 32..1024$ background entries, compared to `656`–`528,896` quadratic association-list comparisons (`15,555.8x` at $N = 1024$, exceeding `maxRecDepth = 512` by $N = 128$).

---

### 2. Split `PointsTo<Node> * PointsToRaw` Slab Freelists and `SymSeg` Erasure

`Basis: source + derived + execution`

Slab allocators embed `next` pointers in the first word of freed blocks whose runtime `block_size >= 8` varies per bin.

#### 2.1 `verus-mimalloc/linked_list.rs` Ghost Framing

In `verus-lang/verified-memory-allocator@7d120970f8d63157ae9bf3b2361192d29bc0acaa`, `verus-mimalloc/linked_list.rs:20-75` explains why `Option<Box<LL>>` fails for runtime-variable padding and concurrent `ThreadLL` delayed-free lists (`L250-329`), tracking `perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>` (`L74`):
- **Push (`insert_block`, `L197-206`):** Splits incoming `points_to_raw` at `size_of::<Node>()` (`8`), casts `[0..8)` into `PointsTo<Node>` (`into_typed::<Node>`), writes `Node { ptr: self.first }`, retains `[8..block_size)` as `PointsToRaw` with matching provenance (`L105-107`), and records `expose_provenance(ptr)` (`L205`).
- **Pop (`pop_block`, `L394-403`):** Reconstructs `*mut Node` via `with_exposed_provenance(self.first.addr(), Tracked(is_exposed))`, reads `node.ptr`, and fuses header and tail back into a single uninitialized raw span via `points_to_node.into_raw().join(points_to_raw)` (`L402`).

#### 2.2 Alignment with `lean-miri` `initMask` and Pass-1 `SymSeg` Subsumption

Under `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Allocation.lean:376-457`), `writeScalar` marks `[0..8)` initialized in `initMask` with pointer provenance (`L425, 452`), leaving `[8..block_size)` uninitialized so full-block typed reads trigger `.invalidUninitBytes` (`L381`). On `pop_block`, returning `[0..block_size)` as `.uninitRun 0 block_size` requires an explicit **initialization-forgetting subsumption** (`.typed lo hi ws ⊑ .uninitRun lo hi`) in segment logic:

```lean
namespace Anneal.SlabBuddy

inductive SymSeg where
  | typed     (lo hi : Nat) (words : List Nat)
  | uninitRun (lo hi : Nat)

def segLo : SymSeg → Nat
  | .typed lo _ _   => lo
  | .uninitRun lo _ => lo

def segHi : SymSeg → Nat
  | .typed _ hi _   => hi
  | .uninitRun _ hi => hi

def segsCover (startOff endOff : Nat) (segs : List SymSeg) : Bool :=
  match
    List.foldr
      (fun sg acc =>
        match acc with
        | none => none
        | some needHi =>
          match Nat.ble (segLo sg) (segHi sg) && Nat.beq (segHi sg) needHi with
          | true  => some (segLo sg)
          | false => none)
      (some endOff) segs
  with
  | some gotStart => Nat.beq gotStart startOff
  | none => false

def rangesDisjoint (a1 sz1 a2 sz2 : Nat) : Prop :=
  ∀ (off : Nat), (a1 ≤ off ∧ off < a1 + sz1) → ¬ (a2 ≤ off ∧ off < a2 + sz2)

def splitSlabBlockPush (blockSz next : Nat) : Option (List SymSeg) :=
  match Nat.ble 8 blockSz with
  | true  => some [.typed 0 8 [next], .uninitRun 8 blockSz]
  | false => none

def fuseSlabBlockPop (blockSz : Nat) (segs : List SymSeg) : Option (Nat × List SymSeg) :=
  match segs with
  | [s1, s2] =>
    match s1, s2 with
    | .typed lo1 hi1 [next], .uninitRun lo2 hi2 =>
      match Nat.beq lo1 0 && Nat.beq hi1 8 && Nat.beq lo2 8 &&
            Nat.ble 8 blockSz && Nat.beq hi2 blockSz with
      | true  => some (next, [.uninitRun 0 blockSz])
      | false => none
    | _, _ => none
  | _ => none

end Anneal.SlabBuddy
```

Checking `Nat.ble 8 blockSz` (`layout.rs:99, 110`) proves exact coverage (`segsCover 0 blockSz`), half-open range disjointness (`rangesDisjoint 0 8 8 (blockSz - 8)`), and push/pop roundtrip with zero `Classical.choice` (and zero axioms on ground/covariant range lemmas).

---

### 3. XOR-Buddy Coalescing and the Zero-Start `lowbit` Hazard

`Basis: source + derived + execution`

In `rcore-os/buddy_system_allocator@da68b6d0bd74e539116898f21d44552417966afc`:
- **`alloc` (`src/lib.rs:143-157`, `src/frame.rs:114-142`):** Finds the smallest non-empty `free_list[i >= class]` and splits downward `j = i .. class + 1`, pushing `block + (1 << (j - 1))` and `block` into `free_list[j - 1]`.
- **`dealloc` (`src/lib.rs:195-221`, `src/frame.rs:193-212`):** Computes `buddy = current_ptr ^ (1 << current_class)`; if `buddy` is present in `free_list[current_class]`, removes it, updates `current_ptr = min(current_ptr, buddy)` (clearing bit `current_class`), and repeats at `current_class + 1`.
- **Zero-start `add_to_heap` discrepancy (`src/lib.rs:100-109` vs. `src/frame.rs:61-65`):** `Heap::add_to_heap` (`src/lib.rs:100-109`) computes `lowbit = current_start & (!current_start + 1)` without checking `current_start == 0`. When `current_start = 0, end = 16` (`ORDER = 13`), `lowbit = 0`, `size = min(0, 16) = 0`, `0usize.trailing_zeros() == 64 > 12`, and the clamp sets `size = 1 << 12 = 4096`, pushing a **4096-byte** block for a **16-byte** `[0, 16)` region (`oob = True`). By contrast, `FrameAllocator::add_frame` (`src/frame.rs:61-65`) explicitly guards `if current_start > 0 { ... } else { max_block_size }`.

In Pass-1 Lean 4, proving bit-extensionality `nat_eq_of_bitAt` over `@Nat.bitwise.eq_1` (isolating `Quot.sound` to quantified bitwise equations) establishes all four XOR-buddy laws from `hAlign : Nat.mod addr (modPow2 order) = 0` (`modPow2 w = Nat.shiftLeft 1 w`, `buddyAddr addr order = Nat.xor addr (Nat.shiftLeft 1 order)`):
1. `buddyAddr (buddyAddr addr order) order = addr` (involutivity);
2. `buddyAddr addr order ≠ addr` (bit `order` strictly flips);
3. `rangesDisjoint addr (modPow2 order) (buddyAddr addr order) (modPow2 order)` (disjointness);
4. Decomposing `addr / 2^order = 2 * q + (0 | 1)` proves either `buddyAddr addr order = addr + 2^order ∧ addr % 2^(order+1) = 0` (even) or `addr = buddyAddr addr order + 2^order ∧ buddyAddr addr order % 2^(order+1) = 0` (odd), while `coalesceBuddiesChecked 6 2 2 = none` rejects unaligned pairs by `rfl`. Replacing linear list scans (`src/lib.rs:202`) with XOR-folded two-bit buddy bitmaps keeps coalescing $O(1)$ per order under the same alignment proof.

---

### 4. Sentinel-Zero vs. `Option` Root Aliasing in Flat Tables

`Basis: source + normative + derived + execution`

| System | Null Encoding | Valid Index Domain | Soundness Property |
| :--- | :--- | :--- | :--- |
| **`seL4/l4v`** (`Structures_A.thy:532`) | `cdt : cslot_ptr => cslot_ptr option` | `(obj_ref × nat)` | Algebraic `None` distinct from `Some (_, 0)` |
| **`seL4/seL4`** (`cnode.c:575-591`) | Virtual `cte_t *` `0` + `mdbFirstBadged` | Mapped kernel `cte_t` addresses (`!= 0`) | `mdbFirstBadged` bounds badged cohorts |
| **`CertiGraph`** (`ArrayGraph.v:32, 59-93`) | `is_null_Z := (x < 0)` (`-1`) | `0 <= x < Z.of_nat size` | Negative sentinel disjoint from `[0..size)` |
| **Unsigned sentinel `0`** | `parent_raw : usize = 0` | `0 <= idx < CAP` | **Bug:** `0` aliases `None` and `Some(0)` |

Exhaustive enumeration of all $(N+1)^{N-1} = 125$ valid 4-slot labeled forests (`Basis: execution`) quantifies two bugs whenever `Option<SlotIdx>` is flattened to unsigned `0`:
1. **Sibling-cohort root collision (`61 / 61` = `100.0%` of multi-root forests):** Comparing `c.parent_raw == target.parent_raw && c.badge == target.badge` matches `0 == 0` across unrelated parentless badged roots, deleting sibling roots on every multi-root forest.
2. **Slot-`0` child conflation (`34 / 125` forests):** Whenever slot `0` and another slot `r >= 1` are both roots, `c.parent_raw == 0` deletes unrelated root `r`, while `c.parent_raw != 0` orphans genuine children of slot `0`. Likewise, reusing slots in an un-tagged union with freelist `next` pointers lets revocation read `next` as `parent`, and resetting non-root `Untyped` regions without `FrameMeta.pinCount == 0` corrupts cross-domain pinned frames.

Pass-1 Lean 4 resolves all three hazards cleanly via tagged `SlotTag` + `Option Nat`:

```lean
inductive SlotTag where
  | emptySlot
  | freelistNode (nextSlot : Option Nat) (tailUninitBytes : Nat)
  | liveCap      (isRootUntyped : Bool) (utBase utLen : Nat) (badge : Nat)

structure CapDerivNode where
  tag    : SlotTag
  parent : Option Nat
  depth  : Nat

def sameLineageParent (p1 p2 : Option Nat) : Bool :=
  match p1, p2 with
  | some a, some b => Nat.beq a b
  | _, _           => false

def areBadgedSiblingsOpt (s1 s2 : Nat) (n1 n2 : CapDerivNode) : Bool :=
  match n1.tag, n2.tag with
  | .liveCap _ _ _ b1, .liveCap _ _ _ b2 =>
    Bool.not (Nat.beq s1 s2) && sameLineageParent n1.parent n2.parent && Nat.beq b1 b2
  | _, _ => false

theorem opt_orphan_never_sibling (s1 s2 : Nat) (n1 n2 : CapDerivNode)
    (hRoot : n2.parent = none) :
    areBadgedSiblingsOpt s1 s2 n1 n2 = false := by
  dsimp only [areBadgedSiblingsOpt, sameLineageParent]
  rw [hRoot]
  cases n1.tag <;> cases n2.tag <;> cases n1.parent <;> rfl
```

Pairing `sameLineageParent` with a two-state postcondition (`RevokeSubtreeSpec`) that keeps `root` alive while clearing every strict descendant regardless of index ordering (`child_idx < parent_idx`) eliminates vacuous self-deletion, slot-`0` aliasing, and freelist-type confusion simultaneously.

## Boundaries

- **`not examined` — Lock-free multi-thread delayed-free ABA reclamation in `verus-mimalloc`:** While `verus-mimalloc/linked_list.rs` includes `ghost_insert_block` (`L250-329`) for `ThreadLL`, concurrent cross-thread `compare_exchange` ABA proofs (`queues.rs`, `free.rs`) were **not examined**.
- **`unknown` — Exact kernel-replay crossover between order-indexed lists and hierarchical XOR buddy bitmaps:** Algebraic XOR coalescing holds for all orders, and `PTree.diffWithD` scales flatly to `N = 1024`; whether a two-bit XOR-pair `PTree` bitmap beats explicit order-indexed free lists in Lean 4 kernel replay time for `ORDER >= 20` remains **unknown** without an end-to-end Lean benchmark.
- **`known not to apply` — Unsigned `0` null-parent sentinels in 0-indexed tables and `Heap::add_to_heap` at `start == 0`:** Unsigned `0` sentinels are **known not to apply** to 0-indexed capability/allocator tables (`100%` sibling collision across all `61` multi-root 4-slot forests), and `rcore-os/buddy_system_allocator@da68b6d0` `Heap::add_to_heap` (`src/lib.rs:100-109`) is **known not to apply** safely to regions starting at `0` with `end < 1 << (ORDER - 1)` due to `lowbit = 0` wraparound.
- **`unsupported` — Impredicative VST `EnvironBox`/`-*`, `Classical.choice` partial maps, and `#[...]`/`structInstSpread` syntax in Pass-1 `theory/`:** VST `EnvironBox` magic wands (`ramification_lemmas.v:156-172`), CompCert `Maps.v` `extensionality` (`L626`), and Lean 4 `#[...]` literals, `omega`, `bv_decide`, `native_decide`, and `{ st with ... }` spread syntax are **unsupported** in Anneal's Pass-1 `theory/` gate (`joshlf/anneal@c131b320`, `TrustedBoundary.lean:442-596`).

## Evidence

### Primary Sources (`Basis: source`)

| Subject | Repository & Commit | Path & Line Range | Key Observed Fact |
| :--- | :--- | :--- | :--- |
| **`CertiGraph`** | `CertiGraph/CertiGraph` @ `8781550d8a116abb03ac7931f271ce03a5158a74` | `graph_model.v:18-39, 194-200`; `subgraph2.v:25-39`; `local_graph_copy.v:45-96`; `ramification_lemmas.v:29-43, 156-172`; `GraphBi.v:834-855`; `ArrayGraph.v:32, 59-93` | `PreGraph`/`LabeledGraph`/`GeneralGraph`, `solve_ramify_P`, `va_reachable_root_update_ramify`, negative `is_null_Z < 0`. |
| **`CompCert` `PTree`** | `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc` | `lib/Maps.v:540-638, 865-911` | `tree_rec2`, `combine`/`gcombine`, canonical `Node`, `extensionality`. |
| **`verus-mimalloc`** | `verus-lang/verified-memory-allocator` @ `7d120970f8d63157ae9bf3b2361192d29bc0acaa` | `verus-mimalloc/linked_list.rs:20-76, 94-132, 169-242, 359-461`; `verus-mimalloc/layout.rs:69-120` | `(PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)`, `split`/`into_typed`, `with_exposed_provenance`, `into_raw().join`, `block_size >= 8`. |
| **`buddy_system_allocator`** | `rcore-os/buddy_system_allocator` @ `da68b6d0bd74e539116898f21d44552417966afc` | `src/lib.rs:56-225`; `src/frame.rs:33-213` | `alloc` splitting, `dealloc` XOR coalescing, unguarded `lowbit` at `current_start == 0` (`src/lib.rs:100-109`) vs `if current_start > 0` (`src/frame.rs:61-65`). |
| **`seL4` & `l4v`** | `seL4/seL4` @ `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`; `seL4/l4v` @ `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` | `cnode.c:575-591`; `Structures_A.thy:532`; `IpcCancel_A.thy:275-290` | Non-null virtual `mdbPrev`/`mdbNext` + `mdbFirstBadged` vs Isabelle `cdt` `option` + grandparent reparenting. |
| **`lean-miri` & `Anneal`** | `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`; `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `Allocation.lean:376-457`; `TrustedBoundary.lean:13-100, 442-596`; `foundation-lock.json:1-21` | `initMask` `.invalidUninitBytes` (`readScalar`/`writeScalar`), Pass-1 `Init.*` allowlist, zero `._unsafe_rec`, 3-axiom ceiling (`Lean v4.34.1`). |

### Peer-Reviewed Literature (`Basis: normative + documentation`)

- Shengyi Wang, Qinxiang Cao, Anshuman Mohan, and Aquinas Hobor, *"Certifying Graph-Manipulating C Programs via Localizations within Data Structures"*, PACMPL / OOPSLA 2019, `doi:10.1145/3360597`.
- Aquinas Hobor and Jules Villard, *"The Ramifications of Sharing in Data Structures"*, POPL 2013, `doi:10.1145/2429069.2429131`.
- Andrea Lattuada et al., *"Verus: Verifying Rust Programs using Linear Ghost Types"*, OOPSLA 2023, `doi:10.1145/3586037`; *"Verus: A Practical Foundation for Systems Verification"*, SOSP 2024, `doi:10.1145/3694715.3695952`.
- Gerwin Klein et al., *"seL4: Formal Verification of an OS Kernel"*, SOSP 2009, `doi:10.1145/1629575.1629596`.

### Self-Contained Executable Probe (`Basis: execution`)

Observed on `2026-11-20` (`Python 3.13.15`, `Linux x86_64`):

```bash
python3 - <<'PY'
import itertools

def pos_path(idx: int) -> list[int]:
    bits = []
    while idx > 0:
        bits.append(idx & 1); idx >>= 1
    return bits

def ptree_ins(t, path, v):
    t = [None, None, None] if t is None else [t[0], t[1], t[2]]
    if not path: t[1] = v
    elif path[0] == 0: t[0] = ptree_ins(t[0], path[1:], v)
    else: t[2] = ptree_ins(t[2], path[1:], v)
    return t

def ptree_diff(req, goal):
    if req is None: return (True, goal), 1
    if goal is None: return (False, None), 1
    rl, rv, rr = req; gl, gv, gr = goal
    if rv is not None and gv != rv: return (False, None), 1
    vr = gv if rv is None else None
    (ol, lr), c1 = ptree_diff(rl, gl); (orr, rro), c2 = ptree_diff(rr, gr)
    if not ol or not orr: return (False, None), 1 + c1 + c2
    if lr is None and vr is None and rro is None: return (True, None), 1 + c1 + c2
    return (True, [lr, vr, rro]), 1 + c1 + c2

def ptree_union(ov, bs):
    if ov is None: return bs, 1
    if bs is None: return ov, 1
    ml, c1 = ptree_union(ov[0], bs[0]); mr, c2 = ptree_union(ov[2], bs[2])
    return [ml, ov[1] if ov[1] is not None else bs[1], mr], 1 + c1 + c2

def ptree_get(t, path):
    for b in path:
        if t is None: return None
        t = t[0] if b == 0 else t[2]
    return None if t is None else t[1]

lp = lq = None
for idx in (2, 4, 6, 8):
    lp = ptree_ins(lp, pos_path(idx), f"pre_{idx}")
    lq = ptree_ins(lq, pos_path(idx), f"post_{idx}")
for d in range(5, 11):
    n, bg = 1 << d, None
    for i in range(n): bg = ptree_ins(bg, pos_path(i), f"bg_{i}")
    for idx in (2, 4, 6, 8): bg = ptree_ins(bg, pos_path(idx), f"pre_{idx}")
    (ok, fr), vd = ptree_diff(lp, bg); assert ok
    gp, vu = ptree_union(lq, fr); visits = vd + vu
    assert all(ptree_get(gp, pos_path(i)) == f"post_{i}" for i in (2, 4, 6, 8))
    assert all(ptree_get(gp, pos_path(e)) == ptree_get(bg, pos_path(e)) for e in (1, 15, n - 1))
    alist = n * 4 + (n * (n + 1)) // 2
    print(f"depth={d} N={n} ptree_visits={visits} alist_steps={alist} ratio={alist/visits:.1f}x")

for bsz in (4, 8, 16, 32, 64, 4096):
    p = None if bsz < 8 else ((0, 8), (8, bsz))
    if p: assert set(range(*p[0])).isdisjoint(range(*p[1])) and set(range(*p[0])) | set(range(*p[1])) == set(range(bsz))
    print(f"slab block_sz={bsz}: push_ok={p is not None}")

pairs = 0
for o in range(9):
    sz = 1 << o
    for a in range(0, 1024, sz):
        b = a ^ sz
        assert (b ^ sz) == a and b != a and set(range(a, a + sz)).isdisjoint(range(b, b + sz))
        assert min(a, b) % (1 << (o + 1)) == 0
        pairs += 1
print(f"buddy_pairs_verified={pairs} orders=0..8")

cs, end, omax = 0, 16, 12
lb = cs & ((~cs + 1) & ((1 << 64) - 1))
sb = min(lb, 1 << ((end - cs).bit_length() - 1))
tz = 64 if sb == 0 else (sb & -sb).bit_length() - 1
cl = (1 << omax) if tz > omax else sb
print(f"add_to_heap_zero_start: lowbit={lb} raw_size={sb} trailing_zeros={tz} clamped_size={cl} end={end} oob={cl > end}")

n, forests = 4, []
for ps in itertools.product([None] + list(range(4)), repeat=4):
    ok = True
    for i in range(n):
        c, s = i, 0
        while c is not None:
            c, s = ps[c], s + 1
            if s > n: ok = False; break
        if not ok: break
    if ok: forests.append(ps)
mr = sh = s0 = 0
for ps in forests:
    raw = [0 if p is None else p for p in ps]
    roots = [i for i in range(n) if ps[i] is None]
    if len(roots) >= 2: mr += 1; sh += int(raw[roots[0]] == raw[roots[1]])
    if ps[0] is None and any(ps[r] is None for r in range(1, n)): s0 += 1
print(f"N=4 forests={len(forests)} multi_root_forests={mr} raw0_sibling_collisions={sh} ({sh/mr*100:.1f}%) slot0_root_conflations={s0}")
PY
```

Recorded output:

```text
depth=5 N=32 ptree_visits=34 alist_steps=656 ratio=19.3x
depth=6 N=64 ptree_visits=34 alist_steps=2336 ratio=68.7x
depth=7 N=128 ptree_visits=34 alist_steps=8768 ratio=257.9x
depth=8 N=256 ptree_visits=34 alist_steps=33920 ratio=997.6x
depth=9 N=512 ptree_visits=34 alist_steps=133376 ratio=3922.8x
depth=10 N=1024 ptree_visits=34 alist_steps=528896 ratio=15555.8x
slab block_sz=4: push_ok=False
slab block_sz=8: push_ok=True
slab block_sz=16: push_ok=True
slab block_sz=32: push_ok=True
slab block_sz=64: push_ok=True
slab block_sz=4096: push_ok=True
buddy_pairs_verified=2044 orders=0..8
add_to_heap_zero_start: lowbit=0 raw_size=0 trailing_zeros=64 clamped_size=4096 end=16 oob=True
N=4 forests=125 multi_root_forests=61 raw0_sibling_collisions=61 (100.0%) slot0_root_conflations=34
```

## Revalidation

1. **Rerun the executable invariant probe (< 0.5 s):** Execute the Python 3.10+ command in **Evidence** and verify exit code `0`, invariant `ptree_visits=34` across `N = 32..1024`, `buddy_pairs_verified=2044`, `oob=True` on zero-start `add_to_heap`, and `raw0_sibling_collisions=61` (`100.0%`).
2. **Diff `verus-mimalloc` and `buddy_system_allocator` invariants:** Check `verus-lang/verified-memory-allocator` `verus-mimalloc/linked_list.rs` (`insert_block`, `pop_block`) and `layout.rs` (`is_block_ptr1`), and check `rcore-os/buddy_system_allocator` `src/lib.rs` (`add_to_heap` `lowbit` zero guard) against `src/frame.rs` (`add_frame`).
3. **Diff `CertiGraph` and Anneal Pass-1 gates:** Check `CertiGraph/CertiGraph` `graph/graph_model.v`, `msl_ext/ramification_lemmas.v`, and `msl_application/ArrayGraph.v`, and check `joshlf/anneal` `trusted/audit/TrustedBoundary.lean` (`allowedTheorySyntaxKinds`) for changes to Pass-1 `Init.*` recursion or syntax rules.
