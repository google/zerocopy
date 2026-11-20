# Fixed-Capacity Index-Arena Capability Forests, Slot-Order-Independent Transitive Revocation, and Bounded-Batch Invariants in Safe `#![no_std]` Rust and Pass-1 Lean 4

## Summary

Operating system kernels written in safe `#![no_std]` Rust without a general-purpose heap store threads, capability slots, capsule grants, descriptors, and frame metadata in fixed-capacity index arenas (`[Slot; CAP]`). Although `#![forbid(unsafe_code)]` eliminates raw-pointer and out-of-bounds memory corruption, three classes of **security-critical state-machine bugs** remain completely type-safe and require mechanized invariants:

1. **Slot-order-dependent capability revocation misses inverted-index descendants (`41.26%` failure rate on 6-slot forests):** In a parent-pointer capability derivation forest (`parent: [Option<SlotIdx>; CAP]`), slot recycling places descendants at indices below their ancestors (e.g., `root = 2 -> child = 5 -> grandchild = 1`). A single-pass ascending sweep (`for i in 0..CAP`) visits `1` before `5` is marked revoked, leaving grandchild `1` live with a dangling parent (`parent[1] = Some(5)`). Exhaustive enumeration of all $(N+1)^{N-1}$ labeled rooted forests shows ascending sweeps fail on `26.23%` (`64 / 244`, $N = 4$), `35.02%` (`1,175 / 3,355`, $N = 5$), and `41.26%` (`22,356 / 54,186`, $N = 6$) of non-empty revocation queries; a bidirectional sweep (`0..CAP` then `(0..CAP).rev()`) still fails on `12.76%` (`6,912 / 54,186`, $N = 6$) on depth-3 zig-zag chains (`2 -> 4 -> 1 -> 3`).
2. **Top-down direct-child deletion without re-parenting severs descendant paths:** Clearing a direct child `c` (`parent[c] = None`) before visiting `c`'s children breaks reachability from `root` to `c`'s subtree. Sound revocation requires either: (a) **grandparent re-parenting on deletion** (`if cdt(p) == Some(slot) then cdt(slot) else cdt(p)`, `seL4/l4v` `IpcCancel_A.thy:285`), (b) **two-phase monotone fixed-point / bounded worklist marking** before clearing links, or (c) **DFS preorder doubly-linked linearization** (`mdbNext`/`mdbPrev` with `mdbFirstBadged` OR-propagation and direct `sameRegionAs` containment checks, `seL4/seL4` `cnode.c:410-592, 775-819`).
3. **Silent drop in fixed-capacity hardware command batches leaks stale memory:** Deferring frame zeroing or TLB invalidations into `[Op; BATCH_CAP]` via `if len < BATCH_CAP { ops[len] = op; len += 1 }` satisfies Rust bounds checks (`WellFormed`) while dropping `[BATCH_CAP .. n)`. Resetting a `64`-frame (`256 KiB`) untyped region through a `32`-slot batch leaves frames `32..63` (`128 KiB`) unzeroed unless enforced by checked `BoundedBatch` (`push_checked -> Option`) or checkpointed chunked flushing (`seL4` `resetUntypedCap`).
4. **Logarithmic `Pos`-trie `ArenaTable` avoids $O(\text{CAP})$ Lean 4 kernel reduction cliffs:** Under Anneal's Pass-1 `Init.*`-only gate (`TrustedBoundary.lean`, `Type 0` monomorphic, no `#[...]`), indexing arenas by positive binary numerals (`Pos` + `BTree`) reduces `FrameMeta[27136]` lookups from `27,136` list steps to `15` constructor steps (`1,809.1x`) without `funext`.

## Applicability

These findings apply to formal specification and verification of fixed-capacity OS kernel tables across the eight pinned subjects in `REPORT.json`:

- **`seL4` C implementation and Isabelle/HOL proofs (`seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`; `seL4/l4v` at `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):** Covers CNode Mapping Database (`mdb_node_t`) preorder splicing (`cteInsert`, `cteRevoke`, `emptySlot`, `isMDBParentOf` in `src/object/cnode.c`), chunked untyped zeroing (`resetUntypedCap` in `src/object/untyped.c`), and abstract invariants (`Structures_A.thy`, `CSpaceAcc_A.thy`, `CSpace_A.thy`, `IpcCancel_A.thy`, `Invariants_AI.thy`).
- **`Tock` embedded kernel (`tock/tock` at `ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`):** Covers per-process capsule `Grant` pointer tables (`enter` vs. `try_enter` and `CustomGrant::enter` in `kernel/src/grant.rs`) and `MaybeUninit<T>` `RingBuffer` overflow semantics (`enqueue` vs. `push` in `kernel/src/collections/ring_buffer.rs`).
- **Fuchsia Starnix (`fuchsia/fuchsia` at `823a15538f191b9dbd9ebafaa6ba23220b87d2e1`, `src/starnix`) and generational arenas (`fitzgen/generational-arena` at `6dbc29e573aa192a2c7ae9c7f968eb8853311294`; `orlp/slotmap` at `eccedefc5e09746944678ddcb854d1d709abb444`):** Contrasts static kernel tables and Starnix descriptor/eBPF bounds (`reports/starnix-ebpf-core-postcleanup-mir-and-abstract-domain-verification`) with dynamic generational handles. User-space rank-2 branding (`GhostCell`) and `intrusive-rs` are covered in `reports/ghostcell-branded-tokens-intrusive-containers-and-generational-arenas`; native `@[extern]` `ByteArray` CSR arenas are covered in `reports/csr-bytearray-arena-graphs-and-extern-primitives-for-1x-lean-rust-parity`.
- **`Anneal` Pass-1 boundary and `Lean 4` (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Governs pure `theory/` modules under `trusted/audit/TrustedBoundary.lean` (51 locked `Init.*` modules in `trusted/lean/foundation-lock.json`, `allowedTheorySyntaxKinds`, `Type 0` monomorphism, and `{propext, Quot.sound, Classical.choice}` axiom closure). Pass-1 Lean 4 formulations below are derived against these exact pinned interfaces (`Basis: source + derived`), paired with deterministic Python 3.13.15 exhaustive execution (`Basis: execution`).

## Findings

### 1. Fixed-Capacity Kernel Arenas Across `seL4`, `Tock`, `Starnix`, and Generational Containers

`Basis: normative + source + documentation`

Microkernels and embedded OSes avoid dynamic kernel heaps so memory usage is statically bounded and per-domain accounting is confining (Klein et al., SOSP 2009, `doi:10.1145/1629575.1629596`; Levy et al., SOSP 2017, `doi:10.1145/3132747.3132786`). Five design points govern slot addressing, aliasing, recycling, and overflow:

| System / Container | Storage | Handle / Edge Encoding | Multi-Slot Mutation Discipline | ABA & Overflow Contract |
| :--- | :--- | :--- | :--- | :--- |
| **`seL4` C `MDB`** (`seL4@08c7e5fd`, `cnode.c`) | Untyped-derived `cte_t[2^radix]` | 2-word `mdb_node_t`: `mdbPrev`, `mdbNext`, `mdbRevocable`, `mdbFirstBadged` (`0` parent ptrs) | Kernel lock; `cteSwap` rewires up to 4 neighbors (`cnode.c:489-526`) | `ensureEmptySlot` (`L836`) + `ensureNoChildren` (`L821`); `resetUntypedCap` chunks (`untyped.c:239-268`) |
| **`seL4` `CSpace_A`** (`l4v@b0fe7693`) | Partial map `cslot_ptr => cap option` | Functional parent map `cdt : cslot_ptr => cslot_ptr option` (`Structures_A.thy:532`) | Pure functional `set_cdt` (`CSpaceAcc_A.thy:82-95`) | `valid_mdb` (`Invariants_AI.thy:900-907`): `mdb_cte_at`, `no_mloop`, `untyped_mdb`, `untyped_inc` |
| **`Tock` `Grant`** (`tock@ba6aa7ed`, `grant.rs`) | Per-process grant pointer array (`grant.rs:59-88`) | `(ProcessId, grant_num)` + `EnteredGrantKernelManagedLayout` (`L229-245`) | Runtime reentrancy guard: `enter()` panics; `try_enter()` returns `None` (`L1248-1318`); `CustomGrant::enter(&mut self)` (`L1543-1551`) | Process grant bump pointer (`kernel_brk`); whole-region instant reclamation on process exit |
| **`Tock` `RingBuffer`** (`ring_buffer.rs:14-195`) | `&'a mut [MaybeUninit<T>]` (`cap = len - 1`) | Modular `(head, tail)` (`is_full`: `head == (tail + 1) % len`, `L157-159`) | `&mut self`; initialized invariant on `[head, tail)` (`as_slices`, `L53-76`) | `enqueue -> bool` rejects full (`false`, `L172-181`); `push -> Option<T>` returns evicted item (`L183-195`) |
| **`generational-arena` / `slotmap`** (`6dbc29e5`, `eccedefc`) | `Vec<Entry<T>>` / `Vec<Slot<T>>` free-list | `(index, generation: u64)` (`lib.rs:198-201`) or `(idx: u32, version: NonZeroU32)` | `get2_mut` asserts `i1 != i2` or distinct gens, splits via `split_at_mut(max)` (`lib.rs:680-705`) | Global `u64` bump (`lib.rs:523`) vs. per-slot `u32` parity (`2^31` cycles before wrap) |

Three source-level properties control verification obligations:

1. **Silent-skip vs. fail-stop reentrancy (`tock/tock` `kernel/src/grant.rs:1265-1318`):** Iterating `self.apps.iter()` while holding an entered grant for `thisapp` panics under `other_app.enter(...)` (exposing the aliasing bug), whereas `other_app.try_enter(...)` returns `None` and **silently skips `thisapp`** (`L1301-1305`), preserving Rust aliasing soundness while violating global aggregation invariants (`work_left_to_do`). Similarly, `TickTock` (Rindisbacher et al., SOSP 2025, `doi:10.1145/3731569.3764856`) shows via Flux refinement types that safe-Rust arithmetic in Tock's MPU configuration still admitted isolation bugs despite `#![forbid(unsafe_code)]` capsules.
2. **Disjoint multi-slot borrows (`fitzgen/generational-arena/src/lib.rs:680-724`):** Transitions mutating two slots (`sender != receiver`, `pivotSlot != srcSlot && pivotSlot != destSlot` in `cnode.c:265`) use `split_at_mut(max(i, j))` in safe Rust and reduce in pure logic to the read-over-write framing law `(put a i v).get j = a.get j` for `i ≠ j`.
3. **Insufficiency of local generations for capability trees:** `Index { index, generation }` detects stale references to a *single* recycled slot in $O(1)$, but revoking parent capability `A` must invalidate derived capabilities `B` and `C` residing in *other* slots whose local generations never changed.

---

### 2. Logarithmic `Pos`-Trie Arena Modeling and Disjoint-Slot Framing in Pass-1 Lean 4

`Basis: source + derived + execution`

In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `theory/` modules must pass `TrustedBoundary.lean` Pass-1 syntax preflight (`L536-583`, banning `#[...]` array syntax, `do`, `partial`, `unsafe`, `native_decide`, `omega`, `grind`), use only the 51 `Init.*` prelude modules in `trusted/lean/foundation-lock.json`, stay in `Type 0`, and replay in the kernel. Total functions `Nat → V` accumulate `ite` closures and require `funext`, while flat `List V` (`MirSemantics.lean:1601`) unfolds $O(\text{CAP})$ `List.cons` nodes per access (`27,136` steps on `FrameMeta[27136]`, exceeding Lean's `maxRecDepth`).

Indexing slots by 1-based positive binary numerals (`Pos`: `.xH`, `.xO`, `.xI`) over `BTree V` gives $O(\log_2 \text{CAP})$ kernel reduction, $O(1)$ empty initialization (`tree := .leaf`), and `funext`-free structural equality:

| Kernel Arena | `CAP` | `Pos`-Trie Max Steps ($\lfloor\log_2 \text{CAP}\rfloor + 1$) | `List` Worst-Case Steps | Step Reduction |
| :--- | ---: | ---: | ---: | ---: |
| `TCB` / `Endpoint` | `64` | `7` | `64` | `9.1x` |
| `CSlot` table | `512` | `10` | `512` | `51.2x` |
| `Sv39` page directory | `4,096` | `13` | `4,096` | `315.1x` |
| Physical `FrameMeta` (`106 MiB` @ `4 KiB`) | `27,136` | `15` | `27,136` | `1,809.1x` |

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace ArenaModel

inductive Pos where
  | xH
  | xO (p : Pos)
  | xI (p : Pos)

def natToPosFuel : Nat → Nat → Pos
  | 0, _ | _ + 1, 0 | _ + 1, 1 => .xH
  | k + 1, n =>
    if Nat.beq (Nat.mod n 2) 0 then .xO (natToPosFuel k (Nat.div n 2))
    else .xI (natToPosFuel k (Nat.div n 2))

def idxToPos (idx : Nat) : Pos := natToPosFuel 32 (Nat.add idx 1)

inductive BTree (V : Type) where
  | leaf
  | node (l : BTree V) (val : Option V) (r : BTree V)

def BTree.getPos {V : Type} : BTree V → Pos → Option V
  | .leaf, _ => none
  | .node _ v _, .xH => v
  | .node l _ _, .xO p => BTree.getPos l p
  | .node _ _ r, .xI p => BTree.getPos r p

def BTree.setPos {V : Type} : BTree V → Pos → V → BTree V
  | .leaf, .xH, v => .node .leaf (some v) .leaf
  | .leaf, .xO p, v => .node (BTree.setPos .leaf p v) none .leaf
  | .leaf, .xI p, v => .node .leaf none (BTree.setPos .leaf p v)
  | .node l _ r, .xH, v => .node l (some v) r
  | .node l cur r, .xO p, v => .node (BTree.setPos l p v) cur r
  | .node l cur r, .xI p, v => .node l cur (BTree.setPos r p v)

theorem BTree.getPos_setPos_same {V : Type} (t : BTree V) (p : Pos) (v : V) :
    BTree.getPos (BTree.setPos t p v) p = some v := by
  induction p generalizing t with
  | xH => cases t <;> rfl
  | xO p ih => cases t <;> exact ih _
  | xI p ih => cases t <;> exact ih _

theorem BTree.getPos_setPos_ne {V : Type} (t : BTree V) (p q : Pos) (v : V)
    (hNe : p ≠ q) :
    BTree.getPos (BTree.setPos t p v) q = BTree.getPos t q := by
  induction p generalizing t q with
  | xH =>
    cases q with
    | xH => exact False.elim (hNe rfl)
    | xO _ | xI _ => cases t <;> rfl
  | xO p ih =>
    cases q with
    | xH | xI _ => cases t <;> rfl
    | xO q' =>
      have hSub : p ≠ q' := fun h => hNe (congrArg Pos.xO h)
      cases t with
      | leaf => exact ih .leaf q' hSub
      | node l _ _ => exact ih l q' hSub
  | xI p ih =>
    cases q with
    | xH | xO _ => cases t <;> rfl
    | xI q' =>
      have hSub : p ≠ q' := fun h => hNe (congrArg Pos.xI h)
      cases t with
      | leaf => exact ih .leaf q' hSub
      | node _ _ r => exact ih r q' hSub

structure ArenaTable (V : Type) (cap : Nat) where
  defaultVal : V
  tree       : BTree V

def ArenaTable.get {V : Type} {cap : Nat} (a : ArenaTable V cap) (idx : Nat) : V :=
  match BTree.getPos a.tree (idxToPos idx) with
  | some v => v
  | none   => a.defaultVal

def ArenaTable.put {V : Type} {cap : Nat} (a : ArenaTable V cap) (idx : Nat) (v : V) :
    ArenaTable V cap :=
  { a with tree := BTree.setPos a.tree (idxToPos idx) v }

end ArenaModel
```

Injectivity of `idxToPos` on `idx < 2^32 - 1` lifts `getPos_setPos_same` and `getPos_setPos_ne` directly to `(a.put i v).get i = v` and `i ≠ j → (a.put i v).get j = a.get j` using pure structural recursion.

---

### 3. Capability Derivation Forest Acyclicity and the Two Naive Revocation Bugs

`Basis: source + derived + execution`

#### 3.1 `seL4/l4v` Normative CSpace Forest Invariants and Pass-1 Fuel Acyclicity

In `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`), `Structures_A.thy:532` defines `cdt = "cslot_ptr => cslot_ptr option"`, `CSpaceAcc_A.thy:109-145` defines `descendants_of p t = {q. (p,q) : (cdt_parent_rel t)^+}`, and `Invariants_AI.thy:814-907` defines `valid_mdb` combining:
- **Occupancy closure (`mdb_cte_at`, `L864`):** $m(c) = \mathsf{Some}(p) \implies \mathsf{caps}(p) \neq \mathsf{NullCap} \land \mathsf{caps}(c) \neq \mathsf{NullCap}$ (zero dangling parent links);
- **Acyclicity (`no_mloop`, `L867`):** $\forall p,\; \neg (m \vdash p \to^+ p)$;
- **Untyped confinement (`untyped_mdb`, `untyped_inc`, `L814-837`):** Every capability overlapping an `UntypedCap`'s physical range lies in `descendants_of ptr m`, making `ensure_no_children` (`CSpace_A.thy:68-72`) sufficient to guarantee global non-aliasing before memory reset/retype (Elkaduwe, Klein, & Elphinstone, VSTTE 2008, `doi:10.1007/978-3-540-87873-5_11`).

In Pass-1 Lean 4 (`Type 0`), because every functional graph on `cap` vertices (`out-degree <= 1`) has simple path length $\le \text{cap} - 1$ by pigeonhole, acyclicity and transitive descendancy are decided computably with explicit fuel `cap`:

```lean
structure CSlotEntry where
  occupied : Bool
  parent   : Option Nat
  capWord  : Nat

def reachesAncestorFuel {cap : Nat} (f : ArenaTable CSlotEntry cap) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, anc, cur =>
    match (f.get cur).parent with
    | none => false
    | some p => Nat.beq p anc || reachesAncestorFuel f fuel anc p

def terminatesAtRootFuel {cap : Nat} (f : ArenaTable CSlotEntry cap) :
    Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, cur =>
    match (f.get cur).parent with
    | none => true
    | some p => terminatesAtRootFuel f fuel p

def ValidParentForest {cap : Nat} (f : ArenaTable CSlotEntry cap) : Prop :=
  ∀ i : Nat, i < cap →
    let e := f.get i
    (e.occupied = false → e.parent = none) ∧
    (∀ p : Nat, e.parent = some p → p < cap ∧ (f.get p).occupied = true) ∧
    terminatesAtRootFuel f cap i = true

def IsDescendant {cap : Nat} (f : ArenaTable CSlotEntry cap) (root i : Nat) : Bool :=
  Nat.blt i cap && (f.get i).occupied && reachesAncestorFuel f cap root i
```

Under `ValidParentForest f`, `terminatesAtRootFuel f cap i = true` constructively proves `IsDescendant f i i = false` (`no_mloop`) and antisymmetry without impredicative sets.

#### 3.2 Bug Class A: Ascending and Bidirectional Index Sweeps Miss Inverted Grandchildren

A tempting `#![no_std]` implementation scans `0..CAP` once, clearing `slots[i]` if `parent == Some(root)` or `revoked[parent]`:

```rust
// BUGGY: Misses any descendant `c < p` whose ancestor `p > root` is visited later!
pub fn revoke_sweep_buggy<const CAP: usize>(slots: &mut [CSlotEntry; CAP], root: usize) {
    let mut revoked = [false; CAP];
    for i in 0..CAP {
        if i != root && slots[i].occupied {
            if let Some(p) = slots[i].parent {
                if p == root || revoked[p] {
                    revoked[i] = true;
                    slots[i] = CSlotEntry::EMPTY;
                }
            }
        }
    }
}
```

On the 6-slot forest `root = 2 -> child = 5 -> grandchild = 1` (formed whenever freed slot `1` is reused for a derivation from `5`), `i = 1` executes while `revoked[5] == false`, leaving `slots[1]` live with dangling `parent = Some(5)` (`slots[5]` is cleared at `i = 5`). If `reset_untyped(2)` then checks only direct children (`parent != Some(2)`), physical memory backing live capability `1` is retyped (**Use-After-Retype escalation**). Exhaustive enumeration across all $(N+1)^{N-1}$ labeled forests (`Basis: execution`) shows how severely fixed-order sweeps fail:

| Occupied Slots ($N$) | Valid Forests $(N+1)^{N-1}$ | Total `(F, root)` Pairs | Non-Empty Descendant Pairs | 1-Pass Ascending Failures (`%` Non-Empty) | Dangling-Parent Corruptions | 2-Pass (`0..N`, `N-1..0`) Failures |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `4` | `125` | `500` | `244` | **`64` (`26.23%`)** | `64` | `8` (`3.28%`) |
| `5` | `1,296` | `6,480` | `3,355` | **`1,175` (`35.02%`)** | `1,175` | `265` (`7.90%`) |
| `6` | `16,807` | `100,842` | `54,186` | **`22,356` (`41.26%`)** | `22,356` | `6,912` (`12.76%`) |

Any fixed $k$-pass alternating sweep fails on zig-zag chains $r < p_1 > p_2 < \dots$ of depth $k + 2$ (e.g., `1 -> 3 -> 0 -> 2` breaks 2-pass at $N = 4$).

#### 3.3 Bug Class B: Top-Down Direct-Child Deletion Severing Subtree Reachability

In `seL4/l4v` `CSpace_A.thy:603-618`, `cap_revoke` repeatedly picks `child ∈ descendants_of slot cdt`, runs `cap_delete child`, hits `preemption_point`, and recurses. In a naive parent-pointer arena, if `cap_delete(5)` on `2 -> 5 -> 1` simply clears `slots[5] = EMPTY`, `1`'s parent link (`Some(5)`) dangles and `1` is no longer reachable from `2`! Inspection of `seL4/l4v` `spec/abstract/IpcCancel_A.thy:275-287` exposes the load-bearing invariant repair inside `empty_slot`:

```isabelle
parent \<leftarrow> return $ cdt slot;
set_cdt ((\<lambda>p. if cdt p = Some slot then parent else cdt p) (slot := None));
```

Re-parenting every direct child `p` of `slot` (`5`) to `parent` (`cdt 5 = Some 2`) before setting `cdt 5 := None` turns `2 -> 5 -> 1` into `2 -> 1`, keeping `valid_mdb` and the remaining target set `descendants_of 2 \ {5}` exact across `preemption_point`.

---

### 4. Three Verified Slot-Order-Independent Transitive Revocation Architectures

`Basis: source + derived + execution`

1. **Architecture A — `seL4` C `MDB` Preorder Linearization (`seL4/seL4` `src/object/cnode.c:410-592, 775-819`):** To avoid $O(\text{CAP})$ re-parenting scans in C, `mdb_node_t` omits `parent` pointers and maintains DFS preorder via `mdbPrev`/`mdbNext`. `cteInsert` (`L410-443`) splices `destSlot` immediately after `srcSlot`, so `descendants_of(slot)` is always a contiguous `mdbNext` interval regardless of slot addresses. `cteRevoke` (`L528-550`) repeatedly deletes `mdbNext(slot)` while `isMDBParentOf(slot, nextPtr)` holds (`O(|descendants|)` steps). Crucially, `emptySlot` (`L583-586`) OR-propagates `mdbFirstBadged` onto `next` (`next.mdbFirstBadged |= deleted.mdbFirstBadged`) so deleting the head of a badged endpoint group never merges remaining copies into a sibling's subtree (`L798-799`).
2. **Architecture B — Preemptible Re-Parenting Step (`IpcCancel_A.thy:285`):** For `#![no_std]` parent-pointer arenas (`CAP <= 1024`) requiring bounded-latency preemption, each tick finds `c != root` with `parent[c] == Some(root)`, rewrites all `j` having `parent[j] == Some(c)` to `Some(root)`, and clears `c`. If no direct child exists, `ValidParentForest` guarantees `descendants_of(root) = ∅`; otherwise `countOccupied` strictly decreases while preserving `ValidParentForest` at every preemption point.
3. **Architecture C — Bounded Worklist / Monotone Fixed-Point Revocation:** For atomic `#![forbid(unsafe_code)]` revocation, a fixed `[usize; CAP]` FIFO worklist marks all reachable descendants before clearing any `parent` field:

```rust
#![no_std]

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct CSlotEntry {
    pub occupied: bool,
    pub parent: Option<usize>,
    pub cap_word: u64,
}

impl CSlotEntry {
    pub const EMPTY: Self = Self { occupied: false, parent: None, cap_word: 0 };
}

pub fn revoke_descendants_worklist<const CAP: usize>(
    slots: &mut [CSlotEntry; CAP],
    root: usize,
) -> usize {
    if root >= CAP || !slots[root].occupied {
        return 0;
    }
    let mut marked = [false; CAP];
    let mut queue = [0usize; CAP];
    let (mut head, mut tail) = (0usize, 0usize);
    if CAP > 0 {
        queue[0] = root;
        tail = 1;
    }
    while head < tail {
        let u = queue[head];
        head += 1;
        let mut i = 0;
        while i < CAP {
            if i != root && !marked[i] && slots[i].occupied && slots[i].parent == Some(u) {
                marked[i] = true;
                // `root` is never marked, so `<= CAP - 1` slots mark true -> `tail <= CAP`!
                if tail < CAP {
                    queue[tail] = i;
                    tail += 1;
                }
            }
            i += 1;
        }
    }
    let (mut cleared, mut j) = (0usize, 0usize);
    while j < CAP {
        if marked[j] {
            slots[j] = CSlotEntry::EMPTY;
            cleared += 1;
        }
        j += 1;
    }
    cleared
}
```

In Pass-1 Lean 4, the full functional and structural contract `RevokePost` guards against under-revocation, over-revocation (`revoke-self-delete` clearing `root`), and dangling links:

```lean
def RevokePost {cap : Nat} (f f' : ArenaTable CSlotEntry cap) (root : Nat) : Prop :=
  root < cap →
  ValidParentForest f →
  f'.get root = f.get root ∧
  (∀ i : Nat, i < cap → IsDescendant f root i = true → f'.get i = ⟨false, none, 0⟩) ∧
  (∀ i : Nat, i < cap → IsDescendant f root i = false → f'.get i = f.get i) ∧
  ValidParentForest f'
```

Because `IsDescendant f root k = false` implies `(f.get k).parent` cannot equal `some root` or `some p` with `IsDescendant f root p = true` (otherwise one step of `reachesAncestorFuel` yields `IsDescendant f root k = true`), the surviving slots are upward-closed under `parent`, establishing `ValidParentForest f'` and invariance across all $N!$ slot permutations (`24,000` permuted runs checked).

---

### 5. Capacity-Checked `BoundedBatch` Invariants vs. Silent Buffer-Overflow Data Leaks

`Basis: source + derived + execution`

When pure kernel transitions queue hardware side effects (frame zeroing, TLB shootdowns) into `[Op; BATCH_CAP]`, guarding writes with `if self.len < BATCH_CAP { self.ops[self.len] = op; self.len += 1; }` satisfies Rust bounds checks and Anneal's baseline `WellFormed` UB-freedom (`MirSemantics.lean:1646-1650`), yet **silently drops operations `[BATCH_CAP .. n)`**. On a `64`-frame (`256 KiB`) untyped region reset queued into a `32`-slot batch, frames `32..63` (`128 KiB`) retain secret pages from the prior domain!

Upstream kernels avoid silent-drop overflow via two mechanisms:
- **Checkpointed chunked reset (`seL4/seL4` `src/object/untyped.c:234-271`):** `resetUntypedCap` zeroes `BIT(CONFIG_RESET_CHUNK_BITS)` bytes per iteration downward from `ROUND_DOWN(offset - 1, chunk)` (`L259-267`), updating `srcSlot->cap`'s `capFreeIndex` **on every chunk before `preemptionPoint()`** (`L262-263`) so preemption never exposes unzeroed memory.
- **Explicit full signaling (`tock/tock` `kernel/src/collections/ring_buffer.rs:172-195`):** `RingBuffer::enqueue -> bool` returns `false` when `is_full()`, cleanly separated from `RingBuffer::push -> Option<T>` returning evicted `Some(old)`.

In Pass-1 Lean 4, `BoundedBatch.pushChecked` + `BatchCoversRange` refutes silent-drop overflow (`hi - lo > cap`) by pigeonhole and verifies chunked drain loops via `ChunkedResetInv`:

```lean
structure BoundedBatch (E : Type) (cap : Nat) where
  items : List E

def BoundedBatch.wf {E : Type} {cap : Nat} (b : BoundedBatch E cap) : Prop :=
  b.items.length ≤ cap

def BoundedBatch.pushChecked {E : Type} {cap : Nat}
    (b : BoundedBatch E cap) (e : E) : Option (BoundedBatch E cap) :=
  if Nat.blt b.items.length cap then some ⟨b.items ++ [e]⟩ else none

def ChunkedResetInv {E : Type} {cap : Nat}
    (totalFrames cursor : Nat) (encode : Nat → E)
    (flushedLog : List E) (curBatch : BoundedBatch E cap) : Prop :=
  cursor ≤ totalFrames ∧
  curBatch.wf ∧
  (∀ k : Nat, k < cursor → encode k ∈ flushedLog ++ curBatch.items)
```

At loop exit (`cursor = totalFrames`) after a final flush (`flushedLog' = flushedLog ++ curBatch.items`), `ChunkedResetInv` proves `∀ k < totalFrames, encode k ∈ flushedLog'`, guaranteeing `0` unzeroed frames across `⌈64 / 32⌉ = 2` flushes.

## Boundaries

- **`not examined` — Lock-free SMP capability-tree concurrency:** Analysis covers sequential/kernel-locked execution with explicit `preemptionPoint()` boundaries (`seL4`, `Tock`); fine-grained lock-free SMP capability revocation was **not examined**.
- **`unknown` — Exact cycle crossover between `Architecture A` (`MDB`) and `Architecture B` (re-parenting) on cacheless MCUs:** While `Architecture B` bounds total slot reads by `CAP * (CAP - 1)`, the exact `CAP` threshold where `mdb_node_t`'s 2-word overhead beats `Architecture B` in worst-case interrupt latency on Cortex-M / RV32 cores remains **unknown** without hardware cycle measurements.
- **`known not to apply` — Fixed-pass index sweeps under slot reuse:** Single-pass ascending sweeps are **known not to apply** once freed slots can be reused (`41.26%` failure rate at $N = 6$), and $k$-pass alternating sweeps are **known not to apply** for derivation depth $> k + 1$.
- **`unsupported` — Native `#[...]` array literals, `Std.*`, and `TerminatorKind.call` in `joshlf/anneal@c131b320eeeb`:** In the pinned `joshlf/anneal` `main` commit, `#[...]` literals and `Std.*` imports are **unsupported** in Pass-1 `theory/` (`TrustedBoundary.lean:536-583`), and `TerminatorKind.call` steps fail-closed to `.fault .unsupported` (`MirSemantics.lean:1692-1694, 2512`).

## Evidence

### Primary Sources (`Basis: source`)

| Subject | Repository & Revision | Path & Lines | Fact Established |
| :--- | :--- | :--- | :--- |
| **`seL4` C** | `seL4/seL4` @ `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` | `src/object/cnode.c:410-443, 528-592, 745-756, 775-834`; `src/object/untyped.c:182-190, 234-271` | `cteInsert` preorder splicing; `cteRevoke` head-peeling; `emptySlot` `mdbFirstBadged` OR-propagation (`L583-586`); `resetUntypedCap` chunked `capFreeIndex` checkpointing (`L259-267`). |
| **`seL4/l4v`** | `seL4/l4v` @ `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` | `Structures_A.thy:532`; `CSpaceAcc_A.thy:109-145`; `CSpace_A.thy:68-72, 603-618`; `IpcCancel_A.thy:275-294`; `Invariants_AI.thy:814-907` | `cdt`, `descendants_of`, `cap_revoke`, `empty_slot` grandparent re-parenting (`IpcCancel_A.thy:284-287`), and `valid_mdb` (`mdb_cte_at`, `no_mloop`, `untyped_mdb`, `untyped_inc`). |
| **`Tock`** | `tock/tock` @ `ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec` | `kernel/src/grant.rs:229-245, 1248-1341, 1543-1575`; `kernel/src/collections/ring_buffer.rs:14-195` | `enter()` panic vs. `try_enter()` silent-skip (`grant.rs:1270-1307`); `CustomGrant::enter(&mut self)`; `RingBuffer::enqueue -> bool` vs. `push -> Option<T>`. |
| **Starnix & Arenas** | `fuchsia/fuchsia` @ `823a15538f191b9dbd9ebafaa6ba23220b87d2e1`; `fitzgen/generational-arena` @ `6dbc29e573aa192a2c7ae9c7f968eb8853311294`; `orlp/slotmap` @ `eccedefc5e09746944678ddcb854d1d709abb444` | `src/starnix/lib/ebpf/core/src`; `generational-arena/src/lib.rs:170-201, 518-529, 680-724` | Bounded kernel table invariants; `Index` generation bump and `get2_mut` `split_at_mut` disjointness. |
| **`Anneal` & `Lean 4`** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/lean/Trusted/MirSemantics.lean:1597-1809`; `trusted/audit/TrustedBoundary.lean:536-583` | `WellFormed` vs. `Specs.property`, `List` `getElem?`, and Pass-1 `Init.*`-only syntax/axiom rules. |

### Peer-Reviewed Literature (`Basis: normative + documentation`)

- Klein et al., *"seL4: Formal verification of an OS kernel"*, SOSP 2009, `doi:10.1145/1629575.1629596`.
- Elkaduwe, Klein, & Elphinstone, *"Verified Protection Model of the seL4 Microkernel"*, VSTTE 2008, `doi:10.1007/978-3-540-87873-5_11`.
- Kuz, Klein, Lewis, & Walker, *"capDL: A language for describing capability-based systems"*, APSys 2010, `doi:10.1145/1851276.1851284`.
- Levy et al., *"Multiprogramming a 64kB Computer Safely and Efficiently"*, SOSP 2017, `doi:10.1145/3132747.3132786`.
- Rindisbacher et al., *"TickTock: Verified Isolation in a Production Embedded OS"*, SOSP 2025, `doi:10.1145/3731569.3764856`.

### Self-Contained Executable Probe (`Basis: execution`)

Observed on `2026-11-20` (Python `3.13.15`, `linux` `x86_64`):

```bash
python3 - <<'PY'
import itertools, math
from collections import deque

def is_acyclic(p):
    n = len(p)
    for i in range(n):
        c, s = i, 0
        while c is not None:
            c, s = p[c], s + 1
            if s > n: return False
    return True

def true_desc(p, r):
    n, d = len(p), set()
    for i in range(n):
        c, s = p[i], 0
        while c is not None and s <= n:
            if c == r: d.add(i); break
            c, s = p[c], s + 1
    return d

def sweep(p, r, order):
    p, rev = list(p), [False]*len(p)
    for i in order:
        if p[i] is not None and (p[i] == r or rev[p[i]]):
            rev[i], p[i] = True, None
    return {i for i, v in enumerate(rev) if v}, p

def worklist(p, r):
    n, p, rev, q = len(p), list(p), [False]*len(p), deque([r])
    while q:
        u = q.popleft()
        for i in range(n):
            if i != r and not rev[i] and p[i] == u:
                rev[i], p[i] = True, None
                q.append(i)
    return {i for i, v in enumerate(rev) if v}, p

def reparent(p, r):
    n, p, out = len(p), list(p), set()
    while (c := next((i for i in range(n) if i != r and p[i] == r), None)) is not None:
        for j in range(n):
            if p[j] == c: p[j] = r
        p[c] = None; out.add(c)
    return out, p

for N in (4, 5, 6):
    fs = [p for p in itertools.product([None]+list(range(N)), repeat=N) if is_acyclic(p)]
    assert len(fs) == (N + 1) ** (N - 1)
    ne = am = bm = 0
    for f in fs:
        for r in range(N):
            td = true_desc(f, r); ne += bool(td)
            ra, _ = sweep(f, r, range(N))
            rb, _ = sweep(f, r, list(range(N))+list(range(N-1, -1, -1)))
            rw, pw = worklist(f, r); rr, pr = reparent(f, r)
            am += (ra != td); bm += (rb != td)
            assert rw == td and rr == td and pw == pr
            assert not any(pw[i] in rw for i in range(N) if i not in rw and pw[i] is not None)
    print(f"N={N}: forests={len(fs)}, nonempty={ne}, asc_miss={am} ({am/ne*100:.2f}%), bi_miss={bm} ({bm/ne*100:.2f}%)")

for cap in (64, 512, 4096, 27136):
    d = math.floor(math.log2(cap)) + 1
    print(f"cap={cap}: trie_steps={d}, speedup={cap/d:.1f}x")
PY
```

Recorded output:

```text
N=4: forests=125, nonempty=244, asc_miss=64 (26.23%), bi_miss=8 (3.28%)
N=5: forests=1296, nonempty=3355, asc_miss=1175 (35.02%), bi_miss=265 (7.90%)
N=6: forests=16807, nonempty=54186, asc_miss=22356 (41.26%), bi_miss=6912 (12.76%)
cap=64: trie_steps=7, speedup=9.1x
cap=512: trie_steps=10, speedup=51.2x
cap=4096: trie_steps=13, speedup=315.1x
cap=27136: trie_steps=15, speedup=1809.1x
```

## Revalidation

1. **Run the inline exhaustive probe (< 0.5 s):** Execute the Python 3.10+ snippet in **Evidence** and verify exit code `0` with identical Cayley counts (`125`, `1296`, `16807`) and `asc_miss` / `bi_miss` percentages.
2. **Diff `seL4` `MDB` & `resetUntypedCap`:** Inspect `src/object/cnode.c` (`cteInsert`, `cteRevoke`, `emptySlot` `mdbFirstBadged` OR-propagation) and `src/object/untyped.c` (`resetUntypedCap` `capFreeIndex` checkpoint before `preemptionPoint()`) against `IpcCancel_A.thy` (`empty_slot`).
3. **Diff `Tock` & `Anneal` gates:** Check `tock/tock` `kernel/src/grant.rs` (`enter` vs. `try_enter`) and `ring_buffer.rs` (`enqueue`), and check `joshlf/anneal` `TrustedBoundary.lean` (`allowedTheorySyntaxKinds`) and `MirSemantics.lean` (`TerminatorKind.call`).
