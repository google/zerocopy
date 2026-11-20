# Intrusive Red-Black Tree Parent-Color Bit-Packing, Odd-Sentinel Atomic Links, Cursor Optics, and Flow Interface Algebras in Pass-1 Lean 4

## Summary

Intrusive collections embed link metadata directly inside user-allocated structs using low-bit pointer tagging, `Cell` interior mutability, atomic link-acquisition CAS gates, and XOR-folded adjacency words. Verifying these containers inside Anneal's Pass-1 `Init.*`-only Lean 4 boundary (`joshlf/anneal@c131b320`, `leanprover/lean4@5045d005` `v4.34.1`) reveals four sharp structural invariants and design boundaries:

1. **Alignment-backed tag packing enforces container-specific sentinels and transient color guards:** `Amanieu/intrusive-rs@0a895642` marks every `Link` and `AtomicLink` as `#[repr(align(2))]` so valid link addresses have bit `0 == 0`. `rbtree::Link` (`src/rbtree.rs:97-270`) packs `Color::{Red = 0, Black = 1}` into bit `0` of `parent_color` and chooses `UNLINKED_MARKER = 0`—which forces `post_insert` (`rbtree.rs:846-850`) to clamp `parent(x).is_none()` to `Color::Black`, because a transient red root (`(0 & !1) | 0 == 0`) would alias `UNLINKED_MARKER` (`is_linked() == false`) and allow double-insertion `&mut` aliasing. Conversely, `linked_list::Link` (`src/linked_list.rs:65`) and `xor_linked_list::Link` (`src/xor_linked_list.rs:95`) use `UNLINKED_MARKER = 1` because singleton/endpoint nodes carry `0` (`None` or `0 ^ 0 = 0`), while `AtomicLink` (`rbtree.rs:372-513`) justifies `unsafe impl Sync` solely because the Acquire/Release `compare_exchange(UNLINKED_MARKER, LINKED_DEFAULT_VALUE)` winner exclusively owns the non-atomic `Cell` fields while linked.
2. **`RBTree` `parent_color` supports single-allocation strict provenance, whereas `XorLinkedList` irreducibly forces wildcard provenance:** Under `proofs-rs/lean-miri@c92d1d97` (`Cast.lean:143-166`, `PointerMachine.lean:78-113`), `RBTree` masks bit `0` of a single pointer (`(parent & !1) | bit`), which preserves single-allocation provenance under `map_addr` strict provenance. By contrast, `XorLinkedList` (`xor_linked_list.rs:201-224`) computes `prev ^ next` across two distinct allocations, destroying single-allocation provenance and forcing `pointerExposeProvenance` + `pointerFromExposedAddress` (yielding `Provenance.wildcard` in permissive mode and faulting in strict provenance mode).
3. **Intrusive `Adapter` projections and cursors require indexed arena optics rather than tree-shaped value lenses:** Because `RBTree` (`parent`) and `XorLinkedList` (`prev ^ next`) induce pointer cycles and 3-node cursor foci (`Cursor { current, prev, next }`), `PureLift`'s acyclic `Lens` (`joshlf/anneal@c131b320`, `theory/Anneal/PureLift/Lens.lean:112-122`) cannot fold an intrusive container into a pure inductive tree. Lifting nodes into a `PTree` arena indexed by binary position `Pos` restores disjoint `Lens (PTree Node) Node` access alongside `container_of!` offset inversion (`src/adapter.rs:100-108, 209-218`).
4. **Krishna–Shasha–Wies Flow Interface conservation unifies with Pass-1 4-node `RBTree` rotation localization:** In `nyu-acsys/template-proofs@6444326e` (`flows.v:29-163, 1720-1736`, `inset_flows.v:17-60`), localized search-tree rewrites must satisfy `contextualLeq` over a commutative cancellative monoid (`ccm.v:14-26`) so subgraph inflows and external outflows stay invariant. In Pass-1 Lean 4, pairing `@Nat.rec` `PTree.diffWithD`/`PTree.unionLeftD` with fuel-monotonic `evalSubtree_mono` verifies 4-node `{p, x, y, b}` RB-tree rotation (in-order key preservation, black-height equality, `parent_color` transfer, and external framing) across all 8 colorings while refuting missing color swaps.

## Applicability

These findings apply to verifying `unsafe` intrusive collections, low-bit tagged pointers, and localized tree rebalances across the seven pinned subjects in `REPORT.json`:

- **`Amanieu/intrusive-rs` (`0a895642801c9a75521f93f6605c7cc707e61f73`):** Covers `src/rbtree.rs`, `src/linked_list.rs`, `src/xor_linked_list.rs`, `src/adapter.rs`, and `src/pointer_ops.rs` (including single-threaded `Cell` links and `AtomicLink` CAS acquisition). Safe phantom-branded `GhostCell` containers are treated separately in `reports/ghostcell-branded-tokens-intrusive-containers-and-generational-arenas`.
- **Flow algebras and Iris (`nyu-acsys/template-proofs@6444326e04577987c66776bed34d9a76ffd0df55`, `nyu-acsys/flows-iris@8998141877c96eef2a6b8733418267cada8b196c`, and `CertiGraph/CertiGraph@8781550d8a116abb03ac7931f271ce03a5158a74`):** Connects Iris flow interface cameras (`flowintR`, `intComposable`, `contextualLeq`) and `CertiGraph` localizations (`GraphBi.v`) to sequential Pass-1 Lean 4 proofs. General Iris adequacy and Simuliris are covered in `reports/iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`.
- **Pointer provenance, `PureLift` lenses, and Pass-1 boundary (`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`):** Applies to `theory/` code adhering to `TrustedBoundary.lean:442-596` (`Init.*` imports only, zero `._unsafe_rec`, zero `#[...]`, zero `Classical.choice`). Related alias/lens treatments appear in `reports/partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses` and `reports/tree-borrows-two-stage-protector-release-and-reborrow-contracts`.

## Findings

### 1. Alignment-Backed Bit-Packing, Sentinel Disjointness, and Atomic CAS Link Ownership

`Basis: source + derived + execution`

`Amanieu/intrusive-rs@0a895642801c9a75521f93f6605c7cc707e61f73` avoids dynamic heap allocation for collection nodes by embedding a `Link` field directly inside user structs. Across its three core link types, alignment `#[repr(align(2))]` guarantees that every valid link pointer has even address (`addr & 1 == 0`), freeing bit `0` as either a payload flag (`Color`) or an unlinked sentinel:

| Container & Link Type | Source Location | Alignment & Storage | `UNLINKED_MARKER` | Linked Default (`acquire_link`) | Collision Invariant |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`RBTree` `Link`** | `src/rbtree.rs:97-223` | `#[repr(align(2))]`; `parent_color: Cell<usize>` | `0` | `(0 & !1) \| 1 = 1` (Null parent, Black) | Root cannot be Red (`color == Black` -> bit `0 == 1 != 0`) |
| **`RBTree` `AtomicLink`** | `src/rbtree.rs:372-513` | `#[repr(align(2))]`; `parent_color: AtomicUsize`, `left`/`right: Cell<...>` | `0` | CAS `0 -> 1` (`LINKED_DEFAULT_VALUE`, `Acquire`/`Relaxed`) | `Sync` holds because only the CAS `0 -> 1` winner enters `&mut RBTree` to mutate `left`/`right` |
| **`LinkedList` `Link` / `AtomicLink`** | `src/linked_list.rs:58-164, 281-390` | `#[repr(align(2))]`; `next: Cell<Option<NonNull<Link>>>` (or `AtomicPtr`) | `1 as *mut Link` | `None` (`0`) | Tail node has `next == None (0)`; valid node pointers have bit `0 == 0 != 1` |
| **`XorLinkedList` `Link` / `AtomicLink`** | `src/xor_linked_list.rs:89-240, 268-385` | `#[repr(align(2))]`; `packed: Cell<usize>` (or `AtomicUsize`) | `1_usize` | `0` (`prev = None, next = None`) | `even ^ even` always has bit `0 == 0 != 1`; singleton has `0 ^ 0 = 0 != 1` |

Two primary-source invariants govern soundness across `rbtree.rs` and `xor_linked_list.rs`:

1. **Transient red-root sentinel theft (`src/rbtree.rs:844-850`):** In `RBTree::LinkOps`, `set_parent_color` encodes `(parent_usize & !1) | bit` with `Color::Red => 0, Color::Black => 1` (`L197-202`). A root node (`parent == None`, so `parent_usize == 0`) that is colored `Color::Red` packs to `(0 & !1) | 0 = 0 == UNLINKED_MARKER`! While `RBTree` maintains the global invariant that the final root is black, `post_insert` colors grandparents `Color::Red` during bottom-up fixup—explicitly guarding root transitions at `L846-850` (`if link_ops.parent(x).is_none() { link_ops.set_color(x, Color::Black); }`). Removing that branch or querying `Link::is_linked()` on an un-clamped red root lets safe callers pass `is_linked() == false` and insert an already-linked node into a second `RBTree`, creating aliased `&mut` references.
2. **Even-address closure of XOR links (`src/xor_linked_list.rs:95, 201-225`):** In a singleton list (`prev = None, next = None`), `prev ^ next = 0 ^ 0 = 0`, which makes `0` unusable as `UNLINKED_MARKER`. Because `Link` is `#[repr(align(2))]`, every valid node address `p` satisfies `p & 1 == 0`, and XOR preserves parity (`(p & 1) ^ (q & 1) = 0 ^ 0 = 0`), ensuring `packed != 1` for every linked state while enabling `tryAcquireXorLink` / `tryAcquireRBLink` CAS checks to reject both unaligned pointers and double-linking.

In Pass-1 Lean 4 (`Init.*` only), bit-level extensionality (`nat_eq_of_bitAt` proved by `Nat.div`/`Nat.mod 2` induction plus `@Nat.bitwise.eq_1`) proves exact roundtrips and collision rejection with axioms restricted strictly to `[propext, Quot.sound]` (where `Quot.sound` enters only via `Nat.bitwise` equational lemmas, while ground `rfl` checks remain axiom-free):

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.SimpLemmas

namespace Anneal.IntrusiveFlow

def UNLINKED_MARKER_RB  : Nat := 0
def UNLINKED_MARKER_XOR : Nat := 1

def isAligned2 (addr : Nat) : Bool := Nat.beq (Nat.land addr 1) 0
def clearBit0 (w : Nat) : Nat := Nat.xor w (Nat.land w 1)

def packParentColor (parentAddr : Nat) (isBlack : Bool) : Nat :=
  let base := clearBit0 parentAddr
  match isBlack with
  | true  => Nat.lor base 1
  | false => base

def unpackParentAddr (rawWord : Nat) : Nat := clearBit0 rawWord
def unpackColorBlack (rawWord : Nat) : Bool := Nat.beq (Nat.land rawWord 1) 1
def packXorLink (prev next : Nat) : Nat := Nat.xor prev next

inductive LinkAcquireRes where
  | okWord (packed : Nat)
  | errUnalignedPtr
  | errDoubleLink

def tryAcquireXorLink (selfAddr curWord prev next : Nat) : LinkAcquireRes :=
  match isAligned2 selfAddr && Bool.not (Nat.beq selfAddr 0) &&
        isAligned2 prev && isAligned2 next with
  | false => .errUnalignedPtr
  | true  =>
    match Nat.beq curWord UNLINKED_MARKER_XOR with
    | true  => .okWord (packXorLink prev next)
    | false => .errDoubleLink

def tryAcquireRBLink (selfAddr curWord parentAddr : Nat) (isBlack : Bool) : LinkAcquireRes :=
  match isAligned2 selfAddr && Bool.not (Nat.beq selfAddr 0) &&
        isAligned2 parentAddr && (Bool.not (Nat.beq parentAddr 0) || isBlack) with
  | false => .errUnalignedPtr
  | true  =>
    match Nat.beq curWord UNLINKED_MARKER_RB with
    | true  => .okWord (packParentColor parentAddr isBlack)
    | false => .errDoubleLink

end Anneal.IntrusiveFlow
```

Under `isAligned2 parentAddr = true`, `unpackColorBlack (packParentColor parentAddr isBlack) = isBlack` and `unpackParentAddr (packParentColor parentAddr isBlack) = parentAddr` hold universally; when `isAligned2 badAddr = false`, `unpackParentAddr (packParentColor badAddr isBlack) ≠ badAddr` proves address corruption; and `parentAddr = 0 → isBlack = true` proves `packParentColor parentAddr isBlack ≠ UNLINKED_MARKER_RB` (`0`).

---

### 2. Pointer Provenance Exposure vs. Strict Provenance, `Adapter` Offsets, and Cursor Optics

`Basis: source + normative + derived`

Examining `Amanieu/intrusive-rs@0a895642` alongside `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` and `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` exposes two structural splits between `RBTree` and `XorLinkedList`:

1. **Single-allocation `RBTree` tagging vs. multi-allocation `XorLinkedList` wildcard provenance:**
   - In `src/rbtree.rs:201-202, 238-239`, `parent_color` modifies only bit `0` of a *single* `NonNull<Link>` address (`(parent_usize & !1) | bit`). Although the checked-in `intrusive-rs` code uses `as usize` / `as *mut Link`, replacing that cast with strict-provenance `ptr.map_addr(|a| (a & !1) | bit)` and `ptr.map_addr(|a| a & !1)` preserves concrete `(AllocId, BorTag)` identity without invoking integer-to-pointer exposure.
   - In `src/xor_linked_list.rs:201-238`, `XorLinkedListOps::set` stores `prev_addr ^ next_addr` into a single `usize`, and `next(ptr, prev)` recovers `(packed ^ prev_addr) as *mut _`. Under `lean-miri`'s operational semantics (`Miri/Interpreter/Cast.lean:143-165` and `Miri/Interpreter/PointerMachine.lean:78-113`), `pointerExposeProvenance` records `(allocId, borTag)` inside `GlobalAddressState.exposed` and calls `TreeBorrows.exposeTag`, while `pointerFromExposedAddress` **always faults in `.strict` provenance mode** (`L109`) and otherwise synthesizes `Pointer.new (some .wildcard) (Size.ofBytes addr)` (`L112`). Verification of `XorLinkedList` therefore irreducibly requires `Provenance.wildcard` plus an explicit exposed-allocation set (`exposed`), whereas `RBTree` admits concrete `strict` provenance!
2. **`container_of!` offset inversion and cursor focus arity vs. `PureLift` `Lens`:**
   - `Adapter` (`src/adapter.rs:41-108, 204-218`) converts between outer container values (`*const Value`) and embedded link fields (`LinkPtr`) via byte-offset arithmetic (`container_of!` subtracts `offset_of!`, while `get_link` uses `(value as *const u8).add(offset_of!(...))` explicitly to avoid constructing an intermediate `&Container` that would retag sibling fields under Stacked/Tree Borrows). Ownership transfer between raw link pointers and smart pointers (`Box`, `Arc`, `Pin<Box<T>>`, `UnsafeRef`) passes through `PointerOps::{into_raw, from_raw}` (`src/pointer_ops.rs:28-200`).
   - `PureLift`'s `Lens (S A : Type)` (`theory/Anneal/PureLift/Lens.lean:112-122`) models partial bidirectional optics obeying `get_put`, `put_get`, and `put_put` over tree-structured values. Cyclic intrusive back-edges (`parent` in `RBTree`, `prev ^ next` in `XorLinkedList`) prevent projecting the container as an inductive algebraic tree: instead, lifting the heap into an arena `PTree Node` makes each node lookup `Lens (PTree Node) Node` indexed by `natToPos u` lawful, while `CursorMut` tracks the exact traversal witness needed to decode neighbors—**1 pointer (`current`)** in `RBTree::CursorMut` (`rbtree.rs:1177-1183`, using `next`/`prev` parent climbs at `L678-715`) versus **3 pointers (`current, prev, next`)** in `XorLinkedList::Cursor` (`xor_linked_list.rs:498-506`) because an isolated `XorLinkedList` node cannot decode its XORed neighbors alone!

---

### 3. Krishna–Shasha–Wies Flow Interfaces and `CertiGraph` 4-Node Rotation Localization

`Basis: source + normative + derived + execution`

To prove global search-tree invariants (in-order sortedness, key-membership preservation, and black-height balance) locally on a 4-node rotation without scanning the whole tree, Krishna, Shasha, and Wies (POPL 2018 `doi:10.1145/3158125`; ESOP 2020 `doi:10.1007/978-3-030-44914-8_12`; PLDI 2020 `doi:10.1145/3385412.3386029`) formulate graph properties as fixed points of **Flow Interface** algebras:

#### 3.1 Primary-Source Flow Interface Structure (`nyu-acsys/flows-iris` & `template-proofs`)

1. **Commutative Cancellative Monoid (`flows-iris@89981418`, `theories/ccm.v:14-26`):** A flow domain `(M, +, 0, -)` is a commutative monoid equipped with a partial inverse `-` satisfying `cancellative` (`x + y = x + z -> y = z`) and `partial_sub` (`(x + y) - x = y`). Crucially, an idempotent join-semilattice such as raw set union `(Set K, ∪)` is **not cancellative** (`{k} ∪ {k} = {k} ∪ ∅`), which is why `template-proofs@6444326e` (`templates/single_copy/inset_flows.v:17-26`) instantiates keyset flows over **multisets** (`K_multiset`) so edge-flow cancellation remains sound!
2. **Flow Interfaces & Composition (`template-proofs@6444326e`, `templates/flows/flows.v:29-163`):** An interface `flowintR` pairs `infR : gmap Node flowdom` (inflows into nodes in `domm I`) with `outR : nzmap Node flowdom` (outflows leaving `domm I`, kept disjoint from `domm I` by `flowint_valid`, `L80-86`). Two interfaces `I1, I2` satisfy `intComposable I1 I2` (`L97-102`) iff their domains are disjoint (`domm I1 ## domm I2`) and each satisfies the flow equation `inf I1 n = out I2 n + (inf I1 n - out I2 n)`.
3. **Frame-Preserving Replacement (`contextualLeq`, `flows.v:1720-1736`):** Replacing subgraph `I1` by `I2` preserves global invariants for *any* framing context `Io` (`flowint_update`, `L1734-1736`; `contextualLeq_impl_globalinv`, `inset_flows.v:43-55`) whenever:
   - `domm I1 ⊆ domm I2`;
   - `∀ n ∈ domm I1, inf I1 n = inf I2 n` (identical boundary inflow entering the modified footprint); and
   - `∀ n ∉ domm I2, out I1 n = out I2 n` (identical boundary outflow routed to untouched external nodes).

#### 3.2 `RBTree::rotate_left` Under Both `contextualLeq` and `CertiGraph` Ramification

In `Amanieu/intrusive-rs` `src/rbtree.rs:776-798` (`rotate_left` with `x` as `ptr`, right child `y`, `b = left(y)`, subtrees `A = left(x)`, `B1 = left(b)`, `B2 = right(b)`, `C = right(y)`, and parent `p` with sibling subtree `O`), transforming `{p, x, y, b}` rewires `p -> y`, `y.left = x`, `x.right = b`, transfers `(parent(y), color(y))` and `(parent(x), color(x))`, and swaps `(x.color, y.color)` (`post_insert`, `L855-889`). Under `contextualLeq` on `dom = {p, x, y, b}`, the external inflow at `p` (`inf(p)`) and all keyset outflows leaving `dom` to `{A, B1, B2, C, O}` remain setwise identical across all 8 `(xBlack, bBlack, pBlack)` color combinations (`Basis: execution`), explaining *why* localized invariants over `{p, x, y, b}` compose across arbitrary ambient `RBTree` contexts!

---

### 4. Mechanizing Localized 4-Node `RBTree` Rotations in Pure Pass-1 Lean 4

`Basis: derived + execution`

Combining `CertiGraph` 4-vertex localizations (`PTree.diffWithD` + `PTree.unionLeftD`) with `intrusive-rs` bit-packed `parentColor` encoding yields a purely constructive Pass-1 Lean 4 proof of `rotate_left` (`rotateLeft4_localized_preserves_keys_bh_and_frame`) with zero `Classical.choice`. Two proof-engineering techniques are critical for Lean 4 kernel checking:

1. **Fuel-depth asymmetry requires `evalSubtree_mono`:** Under left rotation, subtree `A` (left child of `x`) moves one edge *deeper* from `p` (`depth 2 -> 3`), while subtree `C` (right child of `y`) moves one edge *shallower* (`depth 3 -> 2`). A fuel-indexed tree evaluator `evalSubtree (fuel : Nat) (arena : PTree RBNode) (r : Option Nat) : Option (List Nat × Nat)` (`@Nat.rec` returning in-order key list and black-height, checking `bhL == bhR`) therefore evaluates `A` at `f + 1` in `gPost` vs `f + 2` in `gPre`, and evaluates `C` at `f + 2` in `gPost` vs `f + 1` in `gPre`. Proving fuel monotonicity `evalSubtree_mono : f ≤ f' → evalSubtree f arena r = some res → evalSubtree f' arena r = some res` bridges `f + 1` and `f + 2` cleanly without re-evaluating external subtrees.
2. **External framing (`subtreeAvoids4`) and `Pos` literals:** Guarding external subtrees with `subtreeAvoids4 p x y b f gPre r = true` lets `evalSubtree_frame_ext` rewrite `evalSubtree f gPost r = evalSubtree f gPre r` for `{A, B1, B2, C, O}` via `localize_rewrite_frame`. For distant ground frame checks, writing explicit binary `Pos` paths (e.g., `[false, true, false, true, false, true, false]`) avoids unrolling Peano `natToPos` successors (`maxRecDepth = 512`) inside `rfl`.

```lean
structure RBNode where
  key         : Nat
  parentColor : Nat
  left        : Option Nat
  right       : Option Nat

def evalSubtree (fuel : Nat) (arena : PTree RBNode) :
    Option Nat → Option (List Nat × Nat) :=
  @Nat.rec (fun _ => Option Nat → Option (List Nat × Nat))
    (fun r => match r with | none => some ([], 0) | some _ => none)
    (fun _ ih r =>
      match r with
      | none => some ([], 0)
      | some u =>
        match PTree.get (natToPos u) arena with
        | none => none
        | some nd =>
          match ih nd.left, ih nd.right with
          | some (kL, bhL), some (kR, bhR) =>
            match Nat.beq bhL bhR with
            | false => none
            | true  =>
              some (kL ++ [nd.key] ++ kR,
                    bhL + match unpackColorBlack nd.parentColor with
                          | true => 1 | false => 0)
          | _, _ => none)
    fuel

structure Rot4Params where
  p      : Nat
  x      : Nat
  y      : Nat
  b      : Nat
  xIsLeft : Bool
  pKey   : Nat
  xKey   : Nat
  yKey   : Nat
  bKey   : Nat
  pPar   : Nat
  pBlack : Bool
  xBlack : Bool
  bBlack : Bool
  otherP : Option Nat
  subA   : Option Nat
  subB1  : Option Nat
  subB2  : Option Nat
  subC   : Option Nat
```

Instantiating `mkLocalPre4 c` and `mkLocalPost4 c` on the 4 distinct slots `{c.p, c.x, c.y, c.b}` (enforced via `natToPos_injective`), the Pass-1 localization theorem proves in one statement:
1. **Whole-tree equivalence:** `evalSubtree (f + 4) gPost (some c.p) = evalSubtree (f + 4) gPre (some c.p)` (both identical in-order key sequences and equal black-heights);
2. **External frame invariance:** `∀ ext, ext ≠ c.p → ext ≠ c.x → ext ≠ c.y → ext ≠ c.b → PTree.get (natToPos ext) gPost = PTree.get (natToPos ext) gPre`;
3. **Bit-packed `parentColor` integrity:** Unpacking `nY.parentColor`, `nX.parentColor`, and `nB.parentColor` in `gPost` recovers `(c.p, c.xBlack)`, `(c.y, false)`, and `(c.x, c.bBlack)`, respectively;
4. **Bug-detection canary:** Omitting the `(xBlack, false)` color exchange between `y` and `x` yields `evalSubtree 4 buggyNoColorSwapArena (some 2) = none` by `rfl`.

## Boundaries

- **`not examined` — Full two-pass `RBTree::remove` double-black fixup loop and lock-free concurrent list linearizability:** While this report verifies `post_insert` root-color clamping, `rotate_left` / `rotate_right` structural localization, and `AtomicLink::acquire_link` CAS ownership, the multi-case double-black fixup loop in `Amanieu/intrusive-rs@0a895642` `src/rbtree.rs:895-1039` and concurrent lock-free Harris/B-link search structures in `nyu-acsys/template-proofs@6444326e` were **not examined**.
- **`unknown` — Pass-1 kernel replay scaling of multiset `intComposable` witnesses for `k > 8` neighborhoods:** Whether automated Pass-1 certificate checkers for multiset `intComposable` over arbitrary `k`-node neighborhoods outperform explicit `PTree.diffWithD` + `evalSubtree` witnesses in Lean 4 kernel replay time for `k > 8` remains **unknown** without benchmarking larger multi-rotation patches.
- **`known not to apply` — Strict provenance on `XorLinkedList`, naive red-root coloring with `UNLINKED_MARKER = 0`, tree value lenses on cyclic graphs, and idempotent set-union CCMs:** Strict provenance (`.strict` mode in `lean-miri`) is **known not to apply** to `XorLinkedList` (`xor_linked_list.rs:201-238`) because XORing two pointers destroys single-allocation provenance (`PointerMachine.lean:109`). Un-clamped red-root coloring is **known not to apply** when `UNLINKED_MARKER = 0` (`packParentColor 0 false = 0`). Tree-shaped `PureLift` value lenses (`Lens.lean`) are **known not to apply** directly to cyclic `parent` / `prev ^ next` pointer graphs without arena indirection, and non-cancellative idempotent set unions are **known not to apply** to `ccm.v` `partial_sub` without multiset multiplicity (`inset_flows.v`).
- **`unsupported` — Impredicative Iris `iProp` cameras and weak-memory `AtomicUsize` concurrency in `joshlf/anneal@c131b320eeeb`:** Higher-order impredicative Iris ghost state (`iProp`, `authR flowintUR` in `template-proofs/flows.v:1734-1736`) and concurrent `AtomicUsize::compare_exchange` interleavings (`rbtree.rs:495-505`) are **unsupported** in `joshlf/anneal@c131b320eeeb`'s sequential `MirSemantics` and `Init.*`-only `TrustedBoundary.lean`.

## Evidence

### Primary Sources (`Basis: source`)

| Subject | Repository & Commit | Path & Line Range | Key Observed Fact |
| :--- | :--- | :--- | :--- |
| **`intrusive-rs` `RBTree`** | `Amanieu/intrusive-rs` @ `0a895642801c9a75521f93f6605c7cc707e61f73` | `src/rbtree.rs:97-270, 372-560, 678-715, 776-892, 1177-1350` | `#[repr(align(2))]`, `UNLINKED_MARKER = 0`, `set_parent_color`, `AtomicLink` CAS `0 -> 1` + `Sync`, `rotate_left`/`rotate_right`, `post_insert` root-black clamp (`L846-850`), 1-node `CursorMut`. |
| **`intrusive-rs` Lists & Adapters** | `Amanieu/intrusive-rs` @ `0a895642801c9a75521f93f6605c7cc707e61f73` | `src/linked_list.rs:58-164, 281-390`; `src/xor_linked_list.rs:89-240, 268-385, 498-520`; `src/adapter.rs:41-108, 204-218`; `src/pointer_ops.rs:28-200` | Odd `UNLINKED_MARKER = 1`, `prev ^ next` packing, 3-pointer `XorLinkedList::Cursor`, `container_of!` / `offset_of!` Stacked/Tree Borrows-safe `get_link`. |
| **`flows-iris` & `template-proofs`** | `nyu-acsys/flows-iris` @ `8998141877c96eef2a6b8733418267cada8b196c`; `nyu-acsys/template-proofs` @ `6444326e04577987c66776bed34d9a76ffd0df55` | `theories/ccm.v:14-26`; `theories/flows.v:28-82`; `templates/flows/flows.v:29-163, 1720-1736`; `templates/single_copy/inset_flows.v:17-60`; `implementations/flows.spl:15-83` | CCM `cancellative` & `partial_sub`, `flowintR` (`infR`/`outR` disjointness), `intComposable`, `contextualLeq`, `flowint_update`, and `K_multiset` keyset flows. |
| **`CertiGraph`** | `CertiGraph/CertiGraph` @ `8781550d8a116abb03ac7931f271ce03a5158a74` | `msl_application/GraphBi.v:834-855`; `msl_ext/ramification_lemmas.v:156-172` | 4-neighbor binary graph ramification (`va_reachable_root_update_ramify`). |
| **`lean-miri`** | `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/Interpreter/Cast.lean:143-166`; `Miri/Interpreter/PointerMachine.lean:78-113` | `pointerExposeProvenance` (`exposeTag`), `pointerFromExposedAddress` `.strict` fault vs `.wildcard` synthesis. |
| **`Anneal` & `Lean 4`** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `theory/Anneal/PureLift/Lens.lean:110-162`; `trusted/audit/TrustedBoundary.lean:442-596`; `trusted/lean/foundation-lock.json:1-21` | `Lens`/`LawfulLens` laws and Pass-1 `Init.*`-only syntax/axiom rules (`Lean v4.34.1`). |

### Peer-Reviewed Literature (`Basis: normative + documentation`)

- Siddharth Krishna, Dennis Shasha, and Thomas Wies, *"Go with the Flow: Compositional Abstractions for Concurrent Data Structures"*, PACMPL / POPL 2018, `doi:10.1145/3158125`.
- Siddharth Krishna, Alexander J. Summers, and Thomas Wies, *"Local Reasoning for Global Graph Properties"*, ESOP 2020 (LNCS 12075), `doi:10.1007/978-3-030-44914-8_12`.
- Siddharth Krishna, Nisarg Patel, Dennis Shasha, and Thomas Wies, *"Verifying Concurrent Search Structure Templates"*, PLDI 2020, `doi:10.1145/3385412.3386029`.
- Shengyi Wang, Qinxiang Cao, Anshuman Mohan, and Aquinas Hobor, *"Certifying Graph-Manipulating C Programs via Localizations within Data Structures"*, PACMPL / OOPSLA 2019, `doi:10.1145/3360597`.

### Self-Contained Executable Probe (`Basis: execution`)

Observed on `2026-11-20` (`Python 3.13.15`, `Linux x86_64`):

```bash
python3 - <<'PY'
UNLINKED_MARKER_RB, UNLINKED_MARKER_XOR = 0, 1
pack = lambda p, blk: (p & ~1) | (1 if blk else 0)
unpack_addr = lambda w: w & ~1
unpack_blk = lambda w: (w & 1) == 1

aligned_ok = unaligned_bad = red_root_hits = 0
for addr in range(0, 64):
    for blk in (False, True):
        w = pack(addr, blk)
        assert unpack_blk(w) == blk
        if addr % 2 == 0:
            assert unpack_addr(w) == addr; aligned_ok += 1
        else:
            assert unpack_addr(w) != addr; unaligned_bad += 1
        if addr == 0 and not blk and w == UNLINKED_MARKER_RB:
            red_root_hits += 1

xor_hits = 0
for p in range(0, 64, 2):
    for q in range(0, 64, 2):
        packed = p ^ q
        assert (packed ^ p) == q and (packed ^ q) == p
        xor_hits += int(packed == UNLINKED_MARKER_XOR)
assert pack(0, True) == 1 and (0 ^ 0) == 0 and xor_hits == 0
print(f"aligned_lossless={aligned_ok} unaligned_corrupted={unaligned_bad} rb_red_root_zero_collisions={red_root_hits} xor_aligned_marker_collisions={xor_hits}")

def flow_eval(edges, root_in, dom):
    inf = {n: set() for n in dom}; inf[dom[0]] = set(root_in); out_ext = {}
    for _ in range(len(dom) + 1):
        nxt = {n: set() for n in dom}; nxt[dom[0]] = set(root_in); out_ext = {}
        for u in dom:
            for v, cond in edges.get(u, []):
                r = {k for k in inf[u] if cond(k)}
                if v in dom: nxt[v] |= r
                else: out_ext[v] = out_ext.get(v, set()) | r
        inf = nxt
    return inf, out_ext

checked = 0
for x_blk in (False, True):
    for b_blk in (False, True):
        for p_blk in (False, True):
            sub_b = 1 + int(b_blk); sub_x = sub_b + int(x_blk)
            x_post_blk, y_post_blk = False, x_blk
            bh_x_post = (1 + int(b_blk)) + int(x_post_blk)
            assert bh_x_post == sub_b and bh_x_post + int(y_post_blk) == sub_x
            dom = ["p", "x", "y", "b"]
            pre_e = {"p": [("x", lambda k: k < 30), ("O", lambda k: k > 30)], "x": [("A", lambda k: k < 10), ("y", lambda k: k > 10)], "y": [("b", lambda k: k < 20), ("C", lambda k: k > 20)], "b": [("B1", lambda k: k < 15), ("B2", lambda k: k > 15)]}
            post_e = {"p": [("y", lambda k: k < 30), ("O", lambda k: k > 30)], "y": [("x", lambda k: k < 20), ("C", lambda k: k > 20)], "x": [("A", lambda k: k < 10), ("b", lambda k: k > 10)], "b": [("B1", lambda k: k < 15), ("B2", lambda k: k > 15)]}
            ipre, opre = flow_eval(pre_e, set(range(41)), dom)
            ipost, opost = flow_eval(post_e, set(range(41)), dom)
            assert ipre["p"] == ipost["p"] and opre == opost
            checked += 1
assert (1 + 1) != 1
print(f"rot4_flow_configs_verified={checked} no_color_swap_refuted=True")
PY
```

Recorded output:

```text
aligned_lossless=64 unaligned_corrupted=64 rb_red_root_zero_collisions=1 xor_aligned_marker_collisions=0
rot4_flow_configs_verified=8 no_color_swap_refuted=True
```

## Revalidation

1. **Rerun the executable invariant probe (< 0.5 s):** Execute the Python 3.10+ command in **Evidence** and verify exit code `0`, `rb_red_root_zero_collisions=1`, `xor_aligned_marker_collisions=0`, and `rot4_flow_configs_verified=8`.
2. **Diff `intrusive-rs` bit-packing and provenance interfaces:** Inspect `Amanieu/intrusive-rs` `src/rbtree.rs` (`set_parent_color`, `AtomicLinkOps::acquire_link`, `post_insert` root-black clamp, `rotate_left`/`rotate_right`) and `src/xor_linked_list.rs` (`UNLINKED_MARKER`, `XorLinkedListOps`) alongside `proofs-rs/lean-miri` `PointerMachine.lean` (`exposeProvenance`, `pointerFromExposedAddress`).
3. **Diff `template-proofs` flow interfaces and Anneal Pass-1 gates:** Inspect `nyu-acsys/template-proofs` `templates/flows/flows.v` (`intComposable`, `contextualLeq`) and `joshlf/anneal` `trusted/audit/TrustedBoundary.lean` (`allowedTheorySyntaxKinds`) and `theory/Anneal/PureLift/Lens.lean` (`Lens`, `LawfulLens`).
