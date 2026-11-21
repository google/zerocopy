# Aliasing models and reference-based optimizations: a toy borrow stack, a toy borrow tree, and which accesses may move across unknown code (Lean 4)

## Summary

This package mechanizes, in Lean 4 with the core library only, a deliberately small
borrow-tracking model in the style of Stacked Borrows (one memory location, a stack of tagged
permission items, protectors, fresh tags) and a small tree-structured model in the style of Tree
Borrows (one location, a tree of tagged nodes with local and foreign transitions). Unknown code
is a finite, non-adaptive sequence of callee operations that may use any tag it was given or
derived, act observably without touching the location (`emit`), or end the program (`halt`).
Over this model the package proves five refinement theorems about moving or eliminating an
access through a freshly reborrowed reference across one call to unknown code, a general
commutation theorem for reads in the tree model, and two concrete programs on which the two toy
models disagree. Every hypothesis of every theorem has a proved counterexample showing that it
cannot be dropped, and every theorem has a proved instance in which all its hypotheses hold.
Model–system relation: none proved (the refinement theorems relate source and target programs
inside the toy stack model, and R4a and R4d compare the package's two toy models with each
other). These are theorems about the toy models; these theorems neither establish nor refute the
corresponding claims about Stacked Borrows, Tree Borrows, Miri, or the Rust compiler, and every
connection to those systems is a separately labelled modeling bridge under **Findings**.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The results (the plain-language claim of each card, verbatim; `x` is the tag created by the
function-entry reborrow `x := retag a p prot`, `ts` the tags handed to the unknown code):

- **R1a (read elimination, `&mut`, reference not passed).** For a mutable reference (p = unique)
  whose tag the unknown code is not given, and whose tag is fresh or whose entry reborrow is
  protected, replacing a read after an unknown call by the value read before the call is a
  refinement, for all callee code (including callees that hold parent tags, act observably, or
  never return) and all initial states.
- **R2a (read elimination, `&T` without interior mutability).** For a read-only shared reference
  (p = sharedRO, no interior mutability) whose tag is fresh or whose entry reborrow is protected,
  replacing a read after an unknown call by the value read before the call is a refinement, for
  any tags handed to the callee (including the reference itself), all callee code, and all
  initial states.
- **R1b (moving a read down across the call, protected `&mut`).** For a mutable reference
  (p = unique) whose entry reborrow is protected and whose tag the unknown code is not given,
  moving a read from before an unknown call to after it is a refinement, for all callee code and
  all initial states; no freshness assumption is needed.
- **R2b (moving a read down across the call, protected `&T`).** For a read-only shared reference
  (p = sharedRO) whose entry reborrow is protected, moving a read from before an unknown call to
  after it is a refinement, for any tags given to the callee (including the reference), all
  callee code, and all initial states.
- **R3 (dead-store elimination before unknown code, protected `&mut`).** For a mutable reference
  (p = unique) whose entry reborrow is protected and whose tag the unknown code is not given,
  removing the first store in *x = v1; f(ts); *x = v2 is a refinement, for all callee code
  (including callees that never return), all values, and all initial states.
- **R4a (stack UB, tree defined).** The program let x = &mut *root; read root; *x = 5; read x is
  UB in the toy stack model and defined (observing [0, 5]) in the toy tree model, because a
  not-yet-written mutable reference is reserved and tolerates foreign reads.
- **R4c (reads commute in the tree model).** In the toy tree model, two reads through any tags
  commute on every state: the same values, the same final tree, and UB in one order exactly when
  in the other.
- **R4d (stack defined, tree UB).** The program let tmp = &mut *root; let ptr = tmp as *mut _;
  *ptr = 1; read root; *ptr = 2 is defined (observing [1]) in the toy stack model and UB in the
  toy tree model, because the stack keeps the raw pointer's own item when the parent read removes
  tmp, while the tree gives the raw pointer tmp's tag, which the parent read freezes after the
  first write.

Verdicts in the toy stack model at a glance (each "needed" entry is a hypothesis with a proved
counterexample):

| optimization | protector | permission | `x` not passed to the callee | fresh tag |
|---|---|---|---|---|
| read elimination, `&mut` (R1a) | not needed if the tag is fresh | `unique` (fails for `sharedRW`) | needed | fresh **or** protected |
| read elimination, `&T` (R2a) | not needed if the tag is fresh | `sharedRO` (fails for `sharedRW`) | not needed | fresh **or** protected |
| read deferral, `&mut` (R1b) | needed | `unique` (fails for `sharedRW`) | needed | not needed |
| read deferral, `&T` (R2b) | needed | `sharedRO` (fails for `sharedRW`) | not needed | not needed |
| dead-store elimination, `&mut` (R3) | needed | `unique` (fails for `sharedRW`; for `sharedRO` the source is always UB) | needed | not needed |
| store elimination without a later overwrite | fails even under all of R3's hypotheses and a fresh tag (`storeElim_without_overwrite_not_refines`) | | | |

What these results do **not** say is recorded under **Boundaries**, non-claims first; the most
important are: the models are toys with one tracked location and permanent protectors;
`Refines` compares the exact final state; unknown code is non-adaptive; and nothing about the
Rust compiler, Miri, Stacked Borrows, or Tree Borrows follows from a Lean statement alone.

## Applicability

**Model fidelity.** Both models are toys, not Stacked Borrows and not Tree Borrows. They keep
the mechanisms the questions turn on and omit everything else.

- *Toy stack model* (`lean/ToyAlias/Stack.lean`, `lean/ToyAlias/Callee.lean`). Meant to capture
  the per-location borrow stack of Stacked Borrows (Jung, Dang, Kang, Dreyer, POPL 2020): items
  with permissions `unique` (`&mut T`), `sharedRW` (a shared reference to interior-mutable data,
  or a raw pointer), `sharedRO` (`&T` without interior mutability); a granting-item search;
  removal of items invalidated by an access; protectors that make removing an item UB; and
  reborrows that create a fresh tag. Known gaps, as deviations from the paper's rules (its rules
  `read-2` and `write-1`, Fig. 3 `Access`/`FindFirstWIncompat` p. 41:24, Fig. 4 `GrantTag`
  p. 41:25):
  1. a read access *removes* the `unique` items above the granting item, where `read-2` marks
     them `Disabled` (a later access through such a tag is UB under both rules);
  2. a write access removes *every* item above the granting item, where `write-1` keeps the
     adjacent group of `SharedRW` items directly above a `SharedRW` granting item;
  3. a new `sharedRW` item is inserted directly above the granting item, where `GrantTag`
     inserts it at `FindFirstWIncompat`: directly above the granting item when that item is
     `Unique` (the rules then agree) and above the adjacent `SharedRW` group when it is
     `SharedRW`;
  4. protectors are a flag that stays active for the whole run, where the paper uses call IDs
     that become inactive when the call returns;
  5. raw pointers appear only as tagged `sharedRW` items, where the paper uses an untagged `⊥`;
     the Miri implementation of Stacked Borrows was later changed to tag raw pointers (Tree
     Borrows paper, Section 4.1, p. 188:14, citing Unsafe Code Guidelines issue #248).

  A consequence of deviations 2 and 3 that the real model lacks: in the toy a `sharedRW` item can
  remove a `sharedRW` item above it by writing. No result depends on deviations 1-3: in every
  counterexample and witness, each `sharedRW` insertion has a `unique` granting item, each write
  through a `sharedRW` item has nothing above it, and each removed `unique` item is never used
  again or its use is UB under both rules. Also omitted: provenance, allocation and deallocation,
  multiple locations and ranges, `Box`, two-phase borrows, retag kinds other than an explicit
  reborrow, unwinding, concurrency.
- *Toy tree model* (`lean/ToyAlias/Tree.lean`). Meant to capture the per-location borrow tree of
  Tree Borrows (Villani, Hostert, Dreyer, Jung, PLDI 2025): local versus foreign accesses
  (Section 2.1), the default state machine of its Fig. 1 restricted to `Reserved`, `Unique`,
  `Frozen`, `Disabled`, the implicit read of a reborrow (Section 3.2), and raw pointers that reuse
  the tag of the reference they are created from (Section 2.3). Omitted: protectors (hence the
  conflicted `Reserved` behaviour and protector-end accesses), `ReservedIM`, ranges and lazily
  initialized permissions, multiple locations. Tree states are unconstrained (duplicate tags,
  parent cycles, and dangling parents are allowed); well-formed trees arise from `initTMem` and
  `runTree`.
- *Unknown code and refinement* (`lean/ToyAlias/Callee.lean`). The callee is a fixed operation
  sequence (it cannot branch on values it reads; its reborrows are unprotected). The semantics is
  deterministic, so "every target behaviour is a source behaviour, and source UB permits
  anything" is exactly `Refines tgt src := src ≠ ub → tgt = src`, which compares observations,
  halting, and for returning runs the exact final state (value, borrow stack, tag counter).
- *Program shapes* (`lean/ToyAlias/Optimizations.lean`). Each optimization is one fixed pair of
  bodies that begins with the function-entry reborrow of the reference argument; soundness in
  arbitrary surrounding code is not shown.

**Subjects and how they relate.** The theorems are about the Lean definitions in `lean/` only,
checked by the Lean 4 kernel of the toolchain `leanprover/lean4` `v4.34.1` (core Lean, no
Mathlib, no Lake dependencies). The Stacked Borrows and Tree Borrows papers and the cited Miri
commit are the systems the toy definitions are meant to resemble; each claim that a toy verdict
agrees with one of them is a separate `derived (modeling bridge)` claim, argued per result
under **Findings** and never established by the Lean kernel. The Stacked Borrows artifact,
Simuliris, and the Tree Borrows artifact are prior art for the tier labels only.

## Findings

### Definitions (unfolded)

All definitions are in namespace `Toy.Alias` (stack model, unknown code, optimizations) or
`Toy.Alias.Tree` (tree model). Each core definition has proved positive and negative examples,
listed after its block.

#### Borrow stack for one location (`lean/ToyAlias/Stack.lean`)

```text
Tag        := Nat
Perm       := unique | sharedRW | sharedRO
Item       := { perm : Perm, tag : Tag, prot : Bool }
Mem        := { val : Nat, stack : List Item     -- head of the list = TOP of the stack
              , next : Tag }                     -- next fresh tag

grants p read  = true
grants p write = (p = unique ∨ p = sharedRW)

findGranting k t s    -- topmost item g of s with g.tag = t ∧ grants g.perm k
  = some (above, g, below)  with s = above ++ g :: below,   or none

invalidatedBy read  i = (i.perm = unique)     -- reads remove the unique items above
invalidatedBy write i = true                  -- writes remove everything above

accessStack k t s =
  match findGranting k t s with
  | none                   => none (UB)
  | some (above, g, below) =>
      if ∃ i ∈ above, invalidatedBy k i ∧ i.prot then none (UB: protector violated)
      else some ((above.filter (¬ invalidatedBy k ·)) ++ g :: below)

read  t m   = (m.val, m with stack := accessStack read t m.stack)      -- none = UB
write t v m = m with val := v, stack := accessStack write t m.stack    -- none = UB

insertAboveGranting k t new s = (findGranting k t s).map (above ++ new :: g :: below)

retag parent p prot m =          -- creates tag m.next, then next := m.next + 1
  new := ⟨p, m.next, prot⟩
  p = sharedRW : insertAboveGranting write parent new m.stack     (no access)
  p = unique   : new :: accessStack write parent m.stack
  p = sharedRO : new :: accessStack read  parent m.stack

NextFresh m     := ∀ i ∈ m.stack, i.tag ≠ m.next
TagsBelowNext m := ∀ i ∈ m.stack, i.tag < m.next
initMem         := ⟨0, [⟨unique, 0, false⟩], 1⟩
```

`prot = true` means the item was created by a protected function-entry reborrow and (since
protectors never end here) the function is still running. `TagsBelowNext` implies `NextFresh`
(`nextFresh_of_tagsBelowNext`), holds for `initMem` (`tagsBelowNext_initMem`), and is preserved
by `read`, `write`, `retag`, and unknown code (`tagsBelowNext_read`, `tagsBelowNext_write`,
`tagsBelowNext_retag`, `tagsBelowNext_runCallee`). So `NextFresh` holds on every state reachable
from `initMem`; it is a well-formedness fact about the tag counter, not an aliasing condition.

Examples (proved by `decide` or `rfl`): `Perm.grants_unique_write`,
`Perm.not_grants_sharedRO_write`, `findGranting_example_pos`, `findGranting_example_neg`,
`invalidatedBy_read_unique`, `invalidatedBy_read_sharedRW`,
`accessStack_parent_read_pops_child`, `accessStack_parent_read_protected_child_ub`,
`accessStack_write_popped_ub`, `read_example_pos`, `read_example_neg`, `write_example_pos`,
`write_example_neg`, `insertAboveGranting_example_pos`, `insertAboveGranting_example_neg`,
`retag_example_pos`, `retag_example_neg`, `nextFresh_initMem`, `not_nextFresh_example`,
`tagsBelowNext_initMem`, `not_tagsBelowNext_example`, `nextFresh_not_tagsBelowNext`; and the
basic fact `retag_tag` (the created tag is always `m.next`).

#### Unknown code, outcomes, refinement (`lean/ToyAlias/Callee.lean`)

```text
COp     := read i | write i v | retag i p | emit v | halt   -- i indexes the callee's tag environment
Outcome := ub | halted (obs : List Nat) | done (obs : List Nat) (m : Mem)

liftO none k                = ub            -- a failed partial step (none) is UB
liftO (some a) k            = k a
Outcome.bind ub k           = ub            -- written (runCallee ts c m).bind k below
Outcome.bind (halted obs) k = halted obs    -- ub and halted propagate unchanged
Outcome.bind (done obs m) k = k obs m

runCallee env [] m               = done [] m
runCallee env (halt :: _) m      = halted []                 -- never returns (exit, abort, divergence)
runCallee env (emit v :: c) m    = prepend v to the observations of runCallee env c m
runCallee env (read i :: c) m    = t := env[i] (UB if out of range); (v, m') := read t m;
                                   prepend v to the observations of runCallee env c m'
runCallee env (write i v :: c) m = t := env[i]; m' := write t v m; runCallee env c m'
runCallee env (retag i p :: c) m = t := env[i]; (t', m') := retag t p false m;
                                   runCallee (env ++ [t']) c m'

Refines tgt src            := src ≠ ub → tgt = src
Outcome.visible ub         = none
Outcome.visible (halted o) = some (false, o, none)
Outcome.visible (done o m) = some (true, o, some m.val)
VisiblyRefines tgt src     := src ≠ ub → tgt.visible = src.visible      (Refines → VisiblyRefines)
```

The callee starts with the tags it is passed and can use only those and the tags it creates.
`emit v` is an externally observable action that does not touch the tracked location (output, or
an access to memory that no item of this location constrains). Every value the callee reads or
emits is observable. `Refines` compares the final state exactly; any continuation running on it
behaves identically, but since protectors never end in this toy, such a continuation still runs
with the entry protector active (function return is not modelled). Exact equality of the borrow
stack is stronger than what a simulation-based contextual refinement requires. `VisiblyRefines`
ignores the borrow stack and tag counter; every counterexample below refutes both relations, so
each exhibits a difference in UB, halting, observations, or the stored value.

Examples: `runCallee_example_pos`, `runCallee_example_child`, `runCallee_example_emit`,
`runCallee_example_neg`, `refines_of_src_ub`, `refines_refl_example`, `not_refines_tgt_ub`,
`not_refines_obs`, `visiblyRefines_example_pos` (visible refinement without `Refines`),
`visiblyRefines_example_neg`; `Refines.visibly` proves `Refines → VisiblyRefines`.

#### Program shapes (`lean/ToyAlias/Optimizations.lean`)

Every body starts with the function-entry reborrow `x := retag a p prot` of the reference
argument (caller's tag `a`, permission `p`, protector flag `prot`); `x = m.next`. The callee `f`
gets the tag list `ts` (arbitrary; `m.next ∈ ts` means `x` itself is passed). Observations are
the callee's reads and emitted values followed by the returned values. Each step is UB if the
underlying operation is UB; a callee outcome `ub` or `halted` ends the body with that outcome.

| shape | source | target |
|---|---|---|
| read elimination | `x:=retag a p prot; v₁:=*x; f(ts); v₂:=*x; return (v₁,v₂)` | `x:=retag a p prot; v₁:=*x; f(ts); return (v₁,v₁)` |
| read deferral | `x:=retag a p prot; v:=*x; f(ts); return v` | `x:=retag a p prot; f(ts); v:=*x; return v` |
| dead-store elimination | `x:=retag a p prot; *x=v₁; f(ts); *x=v₂; return` | `x:=retag a p prot; f(ts); *x=v₂; return` |
| store elimination, no overwrite | `x:=retag a p prot; *x=v₁; f(ts); return` | `x:=retag a p prot; f(ts); return` |

Lean: `readElimSrc/readElimTgt p prot a ts c m`, `readDeferSrc/readDeferTgt p prot a ts c m`,
`dseSrc p prot a ts c v₁ v₂ m` / `dseTgt p prot a ts c v₂ m`, `storeElimSrc p prot a ts c v₁ m` /
`storeElimTgt p prot a ts c m`. For example,

```lean
def readElimSrc (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  liftO (read x m) fun (v₁, m) =>
  (runCallee ts c m).bind fun obs m =>
  liftO (read x m) fun (v₂, m) =>
  .done (obs ++ [v₁, v₂]) m
```

Examples: `readElim_shapes_example_pos`, `readElim_shapes_example_neg`,
`dse_shapes_example_pos`, `readDefer_shapes_example_neg`, `storeElim_shapes_example`.

Two fixed states are used by counterexamples:
`memDupNext = ⟨0, [⟨unique,0,false⟩, ⟨unique,1,false⟩], 1⟩` violates `NextFresh` and
`TagsBelowNext`, hence is unreachable from `initMem` (`not_tagsBelowNext_memDupNext`);
`memSibling = ⟨0, [⟨sharedRW,1,false⟩, ⟨unique,0,false⟩], 2⟩` has a raw-pointer or
interior-mutable sibling above the root, satisfies `NextFresh` (`nextFresh_memSibling`), and is
reached from `initMem` by one `sharedRW` reborrow of the root (`memSibling_reachable`).

**Single-location boundary facts** (fully proved). `COp.touchesLocation` is true for `read`,
`write`, `retag _ unique`, `retag _ sharedRO` and false for `retag _ sharedRW`, `emit`, `halt`;
`TouchesBeforeHalt c` says some operation of `c` before its first `halt` touches the location
(examples `touchesBeforeHalt_example_pos`, `touchesBeforeHalt_example_neg`).

```text
runCallee_ub_of_touches_of_protected_unique_head :
  m.stack = ⟨unique, x, true⟩ :: rest → x ∉ env → x < m.next → TouchesBeforeHalt c = true →
  runCallee env c m = ub
dseSrc_ub_of_touches              : m.next ∉ ts → TouchesBeforeHalt c = true →
                                    dseSrc unique true a ts c v₁ v₂ m = ub
readDeferSrc_unique_ub_of_touches : m.next ∉ ts → TouchesBeforeHalt c = true →
                                    readDeferSrc unique true a ts c m = ub
dseSrc_sharedRO_protected_ub      : ∀ a ts c v₁ v₂ m, dseSrc sharedRO true a ts c v₁ v₂ m = ub
dse_sharedRO_tgt_defined_src_ub   : dseSrc sharedRO true 0 [] [halt] 5 7 initMem = ub ∧
                                    dseTgt sharedRO true 0 [] [halt] 7 initMem = halted []
```

#### Tree model (`lean/ToyAlias/Tree.lean`)

```text
TPerm := reserved | unique | frozen | disabled
Node  := { tag : Tag, parent : Option Tag, perm : TPerm }
TMem  := { val : Nat, nodes : List Node, next : Tag }

isLocal ns acc u := acc = u, or acc is a descendant of u (parent links, at most |ns| steps)
step read  local  : disabled ↦ UB, q ↦ q
step read  foreign: unique ↦ frozen, q ↦ q
step write local  : reserved ↦ unique, unique ↦ unique, frozen ↦ UB, disabled ↦ UB
step write foreign: q ↦ disabled
treeAccess k t ns := UB unless t is a node; every node n takes step k (isLocal ns t n.tag) n.perm
tread t m, twrite t v m := treeAccess on m.nodes (twrite also stores v)
tretag parent init m := treeAccess read parent; append ⟨m.next, some parent, init⟩; next := m.next + 1
initTMem := ⟨0, [⟨0, none, unique⟩], 1⟩
```

A shared straight-line language
`Op := reborrowMut i | reborrowShared i | reborrowRaw i | read i | write i v` is run in both
models. `runStack` uses unprotected reborrows (`unique` for `reborrowMut`, `sharedRO` for
`reborrowShared`, and `retag t sharedRW false` for `reborrowRaw`, modelling a `*mut` pointer: it
needs an item carrying the parent tag that grants writes, and inserts a fresh tagged `sharedRW`
item). `runTree` uses `tretag t reserved` for `reborrowMut` and `tretag t frozen` for
`reborrowShared`; for `reborrowRaw` it creates no node and performs no access, appending the
parent tag itself to the environment without checking its permission or that it is a node, so
later accesses through the raw pointer are accesses through the parent tag.

Examples: `TPerm.step_reserved_foreign_read`, `TPerm.step_unique_foreign_read`,
`TPerm.step_frozen_local_write`, `isLocal_child_for_root`, `not_isLocal_root_for_child`,
`treeAccess_example_pos`, `treeAccess_example_neg`, `tread_example_pos`, `tread_example_neg`,
`twrite_example_pos`, `twrite_example_neg`, `tretag_example_pos`, `tretag_example_neg`,
`run_example_pos`, `run_example_neg`.

#### How the refinement theorems are proved (`lean/ToyAlias/CalleeInvariant.lean`)

R1a, R2a, R1b and R2b rest on one invariant of unknown code, `CalleeInv.Inv` (namespace
`Toy.Alias.CalleeInv`; these declarations are proof infrastructure, not published results).
After the entry
reborrow with `p = unique` or `p = sharedRO`, the item `⟨p, x, prot⟩` is on top of the stack.
The invariant says: either that item is still in the stack, only `sharedRO` items carrying other
tags lie above it, and the stored value is unchanged; or (only without a protector, and only when
no older item carries the tag `x`) no item with tag `x` is left at all. Every callee operation
preserves it (`CalleeInv.inv_runCallee`): a write or a `unique`/`sharedRO` reborrow through a tag
below the item removes the item (UB if it is protected), a `sharedRW` reborrow is inserted below
it, and reads only remove `unique` items; the hypotheses `p = unique → x ∉ ts` and
`NextFresh m ∨ prot = true` are exactly what the step cases use. A later read through `x` then
either returns the unchanged value without changing the state, or is UB
(`CalleeInv.read_at_inv_good`). R3 uses value-independence instead
(`CalleeInv.runCallee_val_indep_under_protected_unique`): below a protected `unique` item whose
tag the callee does not hold, every callee access to the location is UB, so callee runs from
states that differ only in the stored value agree in outcome, observations, and final stack.
Through private lemmas of `lean/ToyAlias/Optimizations.lean` (not published results), the proofs
of R1b, R2b and R3 in fact establish that target and source have equal outcomes under the
theorems' hypotheses; the published statements are the refinements.

### R1a — Read elimination through an unpassed `&mut`

Card id `R1a-read-elim-mut-unpassed`.

- **Kind and tier:** theorem; T0. The Stacked Borrows paper's example1 (store-to-load forwarding, Section 3.4) is justified by moving the read *x of an unprotected &mut up across unknown code (Section 4, p. 41:16); the paper reports mechanized correctness proofs of its example transformations (Section 7.2), and the artifact proves example1 in theories/opt/ex1.v. R1a applies the same step when the value before the call comes from a read instead of a write, in the toy model, with each hypothesis shown necessary.
- **Plain claim:** For a mutable reference (p = unique) whose tag the unknown code is not given, and whose tag is fresh or whose entry reborrow is protected, replacing a read after an unknown call by the value read before the call is a refinement, for all callee code (including callees that hold parent tags, act observably, or never return) and all initial states.
- **Lean statement** (verbatim from `lean/ToyAlias/Optimizations.lean`; proof omitted): `Toy.Alias.readElim_refines_of_fresh_or_protected_of_unique_of_unpassed`

```lean
-- lean/ToyAlias/Optimizations.lean:221-224
theorem readElim_refines_of_fresh_or_protected_of_unique_of_unpassed
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hfresh : NextFresh m ∨ prot = true) (hp : p = .unique) (hts : m.next ∉ ts) :
    Refines (readElimTgt p prot a ts c m) (readElimSrc p prot a ts c m)
```

- **Reading with key definitions unfolded:** For all `p prot a ts c m`: if `NextFresh m ∨ prot = true` (that is, `(∀ i ∈ m.stack, i.tag ≠ m.next) ∨ prot = true`), `p = unique`, and `m.next ∉ ts` (the callee is not given `x = m.next`), then `readElimSrc p prot a ts c m ≠ ub → readElimTgt p prot a ts c m = readElimSrc p prot a ts c m`. Source: `x := retag a p prot; v₁ := *x; f(ts); v₂ := *x; return (v₁, v₂)`; target: `x := retag a p prot; v₁ := *x; f(ts); return (v₁, v₁)`. Equality of outcomes means the same observations (callee reads and emits, then the returned values), the same halting behaviour, and for returning runs the same final value, borrow stack, and tag counter.
- **Hypothesis ledger:**
  - `hfresh : NextFresh m ∨ prot = true` — Without freshness and without a protector, an old item can carry x's tag; after the callee removes x through a parent write, the source's second read silently uses the old item. Only unreachable states violate NextFresh (see non-claims). Tightness: **tight** (counterexample `Toy.Alias.readElim_fresh_or_protected_needed`).
  - `hp : p = unique` — With p = sharedRW the new item sits below an existing sharedRW sibling (here a raw pointer created earlier from the same parent), and a write through the sibling does not remove x. In Stacked Borrows the sibling also survives (its granting item is unique, where the toy's insertion rule and the paper's coincide). p = sharedRO is covered by R2a. Tightness: **tight** (counterexample `Toy.Alias.readElim_unique_needed`).
  - `hts : m.next ∉ ts` — Otherwise the callee holds x itself and writes through it. Tightness: **tight** (counterexample `Toy.Alias.readElim_unpassed_needed`).
- **Depth:** shallow: one stack-shape invariant (`CalleeInv.Inv`), preserved by an induction over the callee operations (`CalleeInv.inv_runCallee`), followed by a case analysis of the final read through `x` (`CalleeInv.read_at_inv_good`).
- **Non-vacuity witness:** Unprotected &mut reborrowed from the root of initMem; the callee holds the parent tag, emits 3, creates a sharedRW child of the parent, emits 4, and returns; the source is defined with observations [3, 4, 0, 0]. A second witness has a callee that writes 9 through the parent, reads it, and halts (both sides halt with [9]). (`Toy.Alias.readElim_unpassed_nonvacuous`)
- **Companion and boundary theorems** (proved, statement-hashed): `Toy.Alias.readElim_unpassed_nonvacuous_halting`, `Toy.Alias.memSibling_reachable`, `Toy.Alias.not_tagsBelowNext_memDupNext`.
- **Prior art:**
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4, POPL, Article 41 (January 2020). https://doi.org/10.1145/3371109 (Section 3.4, example1; Section 4, p. 41:16; Section 7.2).
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust - Artifact (2019). https://doi.org/10.5281/zenodo.3541779 (Coq development; public repository https://gitlab.mpi-sws.org/FP/stacked-borrows, README and theories/opt read on 2026-11-20, branch master, commit not pinned) (theories/opt/ex1.v).
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 (Section 5, pp. 188:20-21: the Stacked Borrows paper proved that a read can be hoisted up across unknown code for an unprotected reference when an access of that reference is already next to the destination).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: Can reads through &mut be cached across opaque calls, and does that need a protector?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R1a-read-elim-mut-unpassed`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** R1a's verdicts agree with Stacked Borrows: caching a read of an unprotected, unpassed &mut across unknown code is justified, and passing x or using an interior-mutable or raw-pointer permission breaks it. **Reasoning:** The paper justifies moving a read of an unprotected &mut up across unknown code when the reference was used right before (Section 3.4 and Section 4, p. 41:16; restated in the Tree Borrows paper, Section 5). The toy's mechanism is the same: any access by unknown code through a tag below x removes x's unique item, so a later use of x is UB. None of R1a's counterexamples depends on the toy's rule deviations: every sharedRW insertion in them has a unique granting item, every write through a sharedRW item has nothing above it, and the read-removes-versus-disables difference only affects unique items whose later use is UB under both rules. **Sources:** [SB] Sections 3.4, 4 (p. 41:16), Fig. 3 and Fig. 4 (pp. 41:24-25); [TB] Section 5 (pp. 188:20-21); [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### R2a — Read elimination through a read-only shared reference

Card id `R2a-read-elim-shared-ro`.

- **Kind and tier:** theorem; T0. The Stacked Borrows paper's example2 (Section 3.6, proof sketch in Section 3.7): a read through &i32 is deduplicated across a call f(x) that receives the reference; mechanized in the artifact (theories/opt/ex2.v). Restated in the toy model with each hypothesis shown necessary.
- **Plain claim:** For a read-only shared reference (p = sharedRO, no interior mutability) whose tag is fresh or whose entry reborrow is protected, replacing a read after an unknown call by the value read before the call is a refinement, for any tags handed to the callee (including the reference itself), all callee code, and all initial states.
- **Lean statement** (verbatim from `lean/ToyAlias/Optimizations.lean`; proof omitted): `Toy.Alias.readElim_refines_of_fresh_or_protected_of_sharedRO`

```lean
-- lean/ToyAlias/Optimizations.lean:287-290
theorem readElim_refines_of_fresh_or_protected_of_sharedRO
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hfresh : NextFresh m ∨ prot = true) (hp : p = .sharedRO) :
    Refines (readElimTgt p prot a ts c m) (readElimSrc p prot a ts c m)
```

- **Reading with key definitions unfolded:** For all `p prot a ts c m`: if `(∀ i ∈ m.stack, i.tag ≠ m.next) ∨ prot = true` and `p = sharedRO`, then `readElimSrc p prot a ts c m ≠ ub → readElimTgt p prot a ts c m = readElimSrc p prot a ts c m`, with the read-elimination shapes as in R1a; `ts` is arbitrary and may contain `x = m.next`.
- **Hypothesis ledger:**
  - `hfresh : NextFresh m ∨ prot = true` — Without freshness and without a protector, an old write-capable item can carry the reference's tag, and a callee write through that tag changes the value without UB. Only unreachable states violate NextFresh. Tightness: **tight** (counterexample `Toy.Alias.readElim_sharedRO_fresh_or_protected_needed`).
  - `hp : p = sharedRO` — With interior mutability (sharedRW) the callee may write through the reference it is given. Tightness: **tight** (counterexample `Toy.Alias.readElim_sharedRO_needed`).
- **Depth:** shallow: one stack-shape invariant (`CalleeInv.Inv`), preserved by an induction over the callee operations (`CalleeInv.inv_runCallee`), followed by a case analysis of the final read through `x` (`CalleeInv.read_at_inv_good`).
- **Non-vacuity witness:** The unprotected shared reference is handed to the callee, which reads through it, reborrows it, and reads through the reborrow; the source is defined with observations [0, 0, 0, 0]. (`Toy.Alias.readElim_sharedRO_nonvacuous`)
- **Prior art:**
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4, POPL, Article 41 (January 2020). https://doi.org/10.1145/3371109 (Sections 3.6-3.7, example2; Section 7.2).
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust - Artifact (2019). https://doi.org/10.5281/zenodo.3541779 (Coq development; public repository https://gitlab.mpi-sws.org/FP/stacked-borrows, README and theories/opt read on 2026-11-20, branch master, commit not pinned) (theories/opt/ex2.v).
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 (Section 5, Example 17, pp. 188:18-19: the corresponding read deletion for an unprotected shared reference passed to unknown code, proved for Tree Borrows with a simulation relation).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: Can reads through &T be cached across opaque calls that receive the same &T, and what does interior mutability change?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R2a-read-elim-shared-ro`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** R2a's verdicts agree with Stacked Borrows' treatment of example2 and of interior mutability. **Reasoning:** In the paper, every write access pops all SharedRO items, which sit on top of the stack (Section 3.7); the toy's write rule removes every item above the granting item, so the same argument applies. A sharedRW (interior-mutable) reference grants writes in both, which is the counterexample. The toy's rule deviations do not affect the counterexamples (the only sharedRW insertion has a unique granting item and the write through it has nothing above it). **Sources:** [SB] Sections 3.6-3.7 (pp. 41:14-15), Section 5; [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### R1b — Moving a read through a protected `&mut` down across the call

Card id `R1b-read-defer-mut-protected`.

- **Kind and tier:** theorem; T0. The Stacked Borrows artifact proves exactly this transformation for a protected &mut i32 argument and an unknown call f() (theories/opt/ex1_down.v, lemma ex1_down_sim_fun; its README states that example1_down did not appear in the paper but was verified). The paper states in prose that reads through mutable references can similarly be moved down across code that does not need them (Section 4, p. 41:16). Simuliris contains an adapted version (theories/stacked_borrows/examples/opt1_down.v).
- **Plain claim:** For a mutable reference (p = unique) whose entry reborrow is protected and whose tag the unknown code is not given, moving a read from before an unknown call to after it is a refinement, for all callee code and all initial states; no freshness assumption is needed.
- **Lean statement** (verbatim from `lean/ToyAlias/Optimizations.lean`; proof omitted): `Toy.Alias.readDefer_refines_of_protected_of_unique_of_unpassed`

```lean
-- lean/ToyAlias/Optimizations.lean:420-423
theorem readDefer_refines_of_protected_of_unique_of_unpassed
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hprot : prot = true) (hp : p = .unique) (hts : m.next ∉ ts) :
    Refines (readDeferTgt p prot a ts c m) (readDeferSrc p prot a ts c m)
```

- **Reading with key definitions unfolded:** For all `p prot a ts c m`: if `prot = true`, `p = unique`, and `m.next ∉ ts`, then `readDeferSrc p prot a ts c m ≠ ub → readDeferTgt p prot a ts c m = readDeferSrc p prot a ts c m`. Source: `x := retag a p prot; v := *x; f(ts); return v`; target: `x := retag a p prot; f(ts); v := *x; return v`. No hypothesis on `NextFresh m`.
- **Hypothesis ledger:**
  - `hprot : prot = true` — Without a protector, a callee that merely reads through a parent tag removes x, so the deferred read is UB while the source is defined. Tightness: **tight** (counterexample `Toy.Alias.readDefer_protected_needed`).
  - `hp : p = unique` — With p = sharedRW the reference sits below a sharedRW sibling (here a raw pointer created earlier from the same parent), through which the callee writes without removing it. In Stacked Borrows the sibling also survives (its granting item is unique, where the toy's insertion rule and the paper's coincide). p = sharedRO is covered by R2b. Tightness: **tight** (counterexample `Toy.Alias.readDefer_unique_needed`).
  - `hts : m.next ∉ ts` — Otherwise the callee writes through x itself. Tightness: **tight** (counterexample `Toy.Alias.readDefer_unpassed_needed`).
- **Depth:** shallow: one stack-shape invariant (`CalleeInv.Inv`), preserved by an induction over the callee operations (`CalleeInv.inv_runCallee`), followed by a case analysis of the final read through `x` (`CalleeInv.read_at_inv_good`).
- **Non-vacuity witness:** A protected &mut reborrowed from the root of initMem; the callee holds the parent tag, emits 3, and creates a sharedRW child of the parent; the source is defined with observations [3, 0]. (`Toy.Alias.readDefer_unpassed_nonvacuous`)
- **Companion and boundary theorems** (proved, statement-hashed): `Toy.Alias.readDeferSrc_unique_ub_of_touches`, `Toy.Alias.runCallee_ub_of_touches_of_protected_unique_head`.
- **Prior art:**
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust - Artifact (2019). https://doi.org/10.5281/zenodo.3541779 (Coq development; public repository https://gitlab.mpi-sws.org/FP/stacked-borrows, README and theories/opt read on 2026-11-20, branch master, commit not pinned) (theories/opt/ex1_down.v, lemma ex1_down_sim_fun).
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4, POPL, Article 41 (January 2020). https://doi.org/10.1145/3371109 (Section 4, p. 41:16; Section 4.1, protectors).
  - Lennard Gäher, Michael Sammler, Simon Spies, Ralf Jung, Hoang-Hai Dang, Robbert Krebbers, Jeehoon Kang, Derek Dreyer. Simuliris: A Separation Logic Framework for Verifying Concurrent Program Optimizations. Proc. ACM Program. Lang. 6, POPL (2022). https://doi.org/10.1145/3498689 (Coq development https://gitlab.mpi-sws.org/iris/simuliris, file theories/stacked_borrows/examples/opt1_down.v read on 2026-11-20, commit not pinned).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: What do protectors buy for &mut function arguments?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R1b-read-defer-mut-protected`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** R1b's verdicts agree with Stacked Borrows: deferring a read of a &mut argument across unknown code needs the function-entry protector. **Reasoning:** In the paper, the protector makes it UB for unknown code to pop the reference's item while the call runs (Section 4.1, Rule (protector)); in the toy, removing a protected item is UB. Without the protector, a parent read by the callee pops x in the toy and disables x in the paper (rule read-2); either way the deferred read is UB. **Sources:** [SB] Section 4.1 (pp. 41:16-18), Fig. 3 (p. 41:24); [SB-artifact] theories/opt/ex1_down.v; [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### R2b — Moving a read through a protected read-only shared reference down across the call

Card id `R2b-read-defer-shared-ro-protected`.

- **Kind and tier:** theorem; T0. The Stacked Borrows paper's example2_down: introduced in Section 4 (p. 41:16), counterexample without protectors and the protector rules in Section 4.1 (pp. 41:16-18), proof sketch with protectors in Section 4.2 (p. 41:18); mechanized in the artifact (theories/opt/ex2_down.v).
- **Plain claim:** For a read-only shared reference (p = sharedRO) whose entry reborrow is protected, moving a read from before an unknown call to after it is a refinement, for any tags given to the callee (including the reference), all callee code, and all initial states.
- **Lean statement** (verbatim from `lean/ToyAlias/Optimizations.lean`; proof omitted): `Toy.Alias.readDefer_refines_of_protected_of_sharedRO`

```lean
-- lean/ToyAlias/Optimizations.lean:510-513
theorem readDefer_refines_of_protected_of_sharedRO
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hprot : prot = true) (hp : p = .sharedRO) :
    Refines (readDeferTgt p prot a ts c m) (readDeferSrc p prot a ts c m)
```

- **Reading with key definitions unfolded:** For all `p prot a ts c m`: if `prot = true` and `p = sharedRO`, then `readDeferSrc p prot a ts c m ≠ ub → readDeferTgt p prot a ts c m = readDeferSrc p prot a ts c m`, with the read-deferral shapes as in R1b; `ts` is arbitrary and may contain `x = m.next`.
- **Hypothesis ledger:**
  - `hprot : prot = true` — Without a protector, a callee holding a parent tag writes through it and removes the reference; the deferred read is UB. Tightness: **tight** (counterexample `Toy.Alias.readDefer_sharedRO_protected_needed`).
  - `hp : p = sharedRO` — With interior mutability (sharedRW) the callee may write through the reference it is given. Tightness: **tight** (counterexample `Toy.Alias.readDefer_sharedRO_needed`).
- **Depth:** shallow: one stack-shape invariant (`CalleeInv.Inv`), preserved by an induction over the callee operations (`CalleeInv.inv_runCallee`), followed by a case analysis of the final read through `x` (`CalleeInv.read_at_inv_good`).
- **Non-vacuity witness:** The protected shared reference is handed to the callee, which reads through it; the source is defined with observations [0, 0]. (`Toy.Alias.readDefer_sharedRO_nonvacuous`)
- **Prior art:**
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4, POPL, Article 41 (January 2020). https://doi.org/10.1145/3371109 (Section 4, p. 41:16; Section 4.1, pp. 41:16-18; Section 4.2, p. 41:18; example2_down).
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust - Artifact (2019). https://doi.org/10.5281/zenodo.3541779 (Coq development; public repository https://gitlab.mpi-sws.org/FP/stacked-borrows, README and theories/opt read on 2026-11-20, branch master, commit not pinned) (theories/opt/ex2_down.v).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: What do protectors buy for &T function arguments?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R2b-read-defer-shared-ro-protected`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** R2b's verdicts agree with Stacked Borrows' treatment of example2_down. **Reasoning:** The paper's counterexample without protectors (a raw-pointer write by the callee pops the shared reference) and its proof sketch with protectors (any write would pop the protected SharedRO item, which is UB) match the toy's counterexample and statement; in the toy, the raw pointer is replaced by the parent tag. **Sources:** [SB] Sections 4.1-4.2 (pp. 41:16-18); [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### R3 — Dead-store elimination through a protected `&mut` before unknown code

Card id `R3-dead-store-elim-protected`.

- **Kind and tier:** theorem; T0. The Stacked Borrows paper's example3_down: introduced in Section 4 (p. 41:16), proof sketch with protectors in Section 4.2 (p. 41:18), including the remark that the argument holds even if f runs into an infinite loop; mechanized in the artifact (theories/opt/ex3_down.v).
- **Plain claim:** For a mutable reference (p = unique) whose entry reborrow is protected and whose tag the unknown code is not given, removing the first store in *x = v1; f(ts); *x = v2 is a refinement, for all callee code (including callees that never return), all values, and all initial states.
- **Lean statement** (verbatim from `lean/ToyAlias/Optimizations.lean`; proof omitted): `Toy.Alias.dse_refines_of_protected_of_unique_of_unpassed`

```lean
-- lean/ToyAlias/Optimizations.lean:601-604
theorem dse_refines_of_protected_of_unique_of_unpassed
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat) (m : Mem)
    (hprot : prot = true) (hp : p = .unique) (hts : m.next ∉ ts) :
    Refines (dseTgt p prot a ts c v₂ m) (dseSrc p prot a ts c v₁ v₂ m)
```

- **Reading with key definitions unfolded:** For all `p prot a ts c v₁ v₂ m`: if `prot = true`, `p = unique`, and `m.next ∉ ts`, then `dseSrc p prot a ts c v₁ v₂ m ≠ ub → dseTgt p prot a ts c v₂ m = dseSrc p prot a ts c v₁ v₂ m`. Source: `x := retag a p prot; *x = v₁; f(ts); *x = v₂; return`; target: `x := retag a p prot; f(ts); *x = v₂; return`. The observations are the callee's reads and emits only (nothing is returned), so equality of `done` outcomes includes equality of the final stored value (`v₂` on both sides).
- **Hypothesis ledger:**
  - `hprot : prot = true` — Without a protector, the callee can read the stored value through a parent tag (removing x) and then halt, so the source's second store, which would be UB, is never reached and the callee's observation differs (5 versus 0). Tightness: **tight** (counterexample `Toy.Alias.dse_protected_needed`).
  - `hp : p = unique` — A protected sharedRW reference survives a read through the parent, so the callee observes the first store. For p = sharedRO the source is UB at its first store (dseSrc_sharedRO_protected_ub), so that case is excluded rather than counted as a refinement. Tightness: **tight** (counterexample `Toy.Alias.dse_unique_needed`).
  - `hts : m.next ∉ ts` — Otherwise the callee reads the first store through x itself. Tightness: **tight** (counterexample `Toy.Alias.dse_unpassed_needed`).
- **Depth:** shallow: one value-independence lemma (`CalleeInv.runCallee_val_indep_under_protected_unique`, proved by an induction over the callee operations: runs from states that differ only in the stored value agree in outcome, observations, and final stack), followed by a case analysis of the two callee runs and the final store through `x`.
- **Non-vacuity witness:** A protected &mut reborrowed from the root of initMem; the callee holds the parent tag, emits 3, and creates a sharedRW child of the parent; the source is defined with observations [3] and final value 7. A second witness has a callee that emits 3 and halts. (`Toy.Alias.dse_nonvacuous`)
- **Companion and boundary theorems** (proved, statement-hashed): `Toy.Alias.dse_nonvacuous_halting`, `Toy.Alias.storeElim_without_overwrite_not_refines`, `Toy.Alias.dseSrc_sharedRO_protected_ub`, `Toy.Alias.dse_sharedRO_tgt_defined_src_ub`, `Toy.Alias.dseSrc_ub_of_touches`, `Toy.Alias.runCallee_ub_of_touches_of_protected_unique_head`.
- **Prior art:**
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4, POPL, Article 41 (January 2020). https://doi.org/10.1145/3371109 (Section 4, p. 41:16; Section 4.2 and footnote 4, p. 41:18; example3_down).
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust - Artifact (2019). https://doi.org/10.5281/zenodo.3541779 (Coq development; public repository https://gitlab.mpi-sws.org/FP/stacked-borrows, README and theories/opt read on 2026-11-20, branch master, commit not pinned) (theories/opt/ex3_down.v).
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 (Section 5, p. 188:20, and Section 7, p. 188:22: activating writes).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: When is a store through &mut before an opaque call dead?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R3-dead-store-elim-protected`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** R3's verdicts agree with Stacked Borrows' treatment of example3_down, including the need for the protector and the role of non-returning callees. **Reasoning:** The paper argues that any access by f to x would pop x's protected item, so f cannot observe the stored value, and that this holds even if f never returns (Section 4.2). In the toy, the halting callee is what makes the protector necessary: with callees that always return and a fresh tag, the source's own second store would be UB after a parent access. The counterexample for the protector uses only a parent read and a halt, where the toy's rules and the paper's agree. **Sources:** [SB] Section 4.2 (p. 41:18); [SB-artifact] theories/opt/ex3_down.v; [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### R4a — Parent read before the first child write: stack UB, tree defined

Card id `R4a-parent-read-before-child-write`.

- **Kind and tier:** counterexample; T0. Direct instance of the Tree Borrows paper's account: mutable references start Reserved, which allows foreign reads until the first local write (Section 2.2, pp. 188:7-8, footnote 3: this applies to all mutable references, not only two-phase borrows), whereas in Stacked Borrows mutable references start Unique and are invalidated by any foreign access (Section 4.1, pp. 188:13-14).
- **Plain claim:** The program let x = &mut *root; read root; *x = 5; read x is UB in the toy stack model and defined (observing [0, 5]) in the toy tree model, because a not-yet-written mutable reference is reserved and tolerates foreign reads.
- **Lean statement** (verbatim from `lean/ToyAlias/Tree.lean`; proof omitted): `Toy.Alias.Tree.stack_ub_tree_defined_parentReadThenChildWrite`

```lean
-- lean/ToyAlias/Tree.lean:259-261
theorem stack_ub_tree_defined_parentReadThenChildWrite :
    runStack [0] parentReadThenChildWrite initMem = none ∧
      (runTree [0] parentReadThenChildWrite initTMem).map Prod.fst = some [0, 5]
```

- **Reading with key definitions unfolded:** `parentReadThenChildWrite = [reborrowMut 0, read 0, write 1 5, read 1]` with environment `[0]` (the root tag): `runStack [0] parentReadThenChildWrite initMem = none` (UB) and `(runTree [0] parentReadThenChildWrite initTMem).map Prod.fst = some [0, 5]` (defined; the observations are the two reads). In the stack model the read through the root removes the child's `unique` item, so the write through the child finds no granting item; in the tree model the child is `reserved`, which a foreign read leaves unchanged and a local write turns into `unique`.
- **Hypothesis ledger:** none (a closed statement about one concrete program).
- **Depth:** definitional: evaluation of two concrete runs, checked by `decide`.
- **Non-vacuity witness:** Closed statement about one concrete program (no hypotheses).
- **Prior art:**
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 (Section 2.2, Example 8 and footnote 3; Section 4.1).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: Where do stack-structured and tree-structured permission models differ (reads before the first write through a fresh &mut)?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R4a-parent-read-before-child-write`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** The same verdict pair holds for an explicit &mut in Stacked Borrows (UB) and Tree Borrows (defined), absent protectors. **Reasoning:** Tree Borrows paper: all mutable references start Reserved, which allows foreign reads (Section 2.2); Stacked Borrows has no Reserved state and mutable references become Disabled on any foreign access (Section 4.1). The toy's transitions for this program are exactly these. **Sources:** [TB] Sections 2.2 and 4.1 (pp. 188:7-8, 188:13-14); [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/tree_borrows/perms.rs: PermissionPriv (lines 10-53: Cell, ReservedFrz, ReservedIM, Unique, Frozen, Disabled) and the transitions child_read, foreign_read, child_write, foreign_write (lines 136-218: an unprotected Unique becomes Frozen on a foreign read, Reserved becomes Unique on a child write, a foreign write disables everything except Cell and ReservedIM); src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### R4c — In the toy tree model, any two reads commute

Card id `R4c-tree-reads-commute`.

- **Kind and tier:** theorem; T0. The Tree Borrows paper proves in Rocq that executing two adjacent reads in either order from an arbitrary state ends in the exact same state (Section 5, Example 19, p. 188:20), relying on foreign reads freezing rather than disabling (Section 2.2, p. 188:8). This is the toy restatement.
- **Plain claim:** In the toy tree model, two reads through any tags commute on every state: the same values, the same final tree, and UB in one order exactly when in the other.
- **Lean statement** (verbatim from `lean/ToyAlias/Tree.lean`; proof omitted): `Toy.Alias.Tree.tree_read_read_commute`

```lean
-- lean/ToyAlias/Tree.lean:457-459
theorem tree_read_read_commute (t₁ t₂ : Tag) (m : TMem) :
    ((tread t₁ m).bind fun (v₁, m₁) => (tread t₂ m₁).map fun (v₂, m₂) => ((v₁, v₂), m₂)) =
      ((tread t₂ m).bind fun (v₂, m₁) => (tread t₁ m₁).map fun (v₁, m₂) => ((v₁, v₂), m₂))
```

- **Reading with key definitions unfolded:** For all tags `t₁ t₂` and every tree state `m` (no well-formedness hypothesis): reading through `t₁` and then `t₂`, returning `((v₁, v₂), m₂)`, gives the same `Option` value as reading through `t₂` and then `t₁` and returning the values in the same `(v₁, v₂)` order. Since both sides are `Option` values, one order is UB (`none`) exactly when the other is. `tread t m = (treeAccess read t m.nodes).map (m.val, m with nodes := ·)`; the proof uses that locality depends only on tags and parent links, which reads never change, and that the per-node read transitions commute. The companion `readRead_swap_stack_rejects_tree_agrees` runs, with environment `[0]` (the root tag), `readReadSrc = [reborrowMut 0, write 1 42, read 1, read 0]` (`let x = &mut *root; *x = 42; read x; read root`) and `readReadTgt = [reborrowMut 0, write 1 42, read 0, read 1]` (`let x = &mut *root; *x = 42; read root; read x`).
- **Hypothesis ledger:** none (universally quantified over all tags and all tree states, with no premises).
- **Depth:** shallow: locality depends only on the unchanged tags and parent links, and the per-node read transitions commute (`rd_comm`).
- **Non-vacuity witness:** Reading through the root and then an active child of a two-node tree is defined and changes the tree (the child becomes frozen). (`Toy.Alias.Tree.tree_read_read_commute_nonvacuous`)
- **Positive control:** `Toy.Alias.Tree.stack_read_read_not_commute` — in the toy stack model two reads need not commute: reading through a mutable child and then its parent is defined, while reading through the parent and then the child is UB.
- **Companion and boundary theorems** (proved, statement-hashed): `Toy.Alias.Tree.readRead_swap_stack_rejects_tree_agrees`.
- **Prior art:**
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 (Section 2.2, p. 188:8; Section 5, Example 19, p. 188:20).
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows - Artifact (2025). https://doi.org/10.5281/zenodo.15002703 (record as given in the reference list of the Tree Borrows paper; contents not inspected).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: Which reorderings does the tree structure enable that the stack structure does not?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R4c-tree-reads-commute`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** Read-read reordering is valid in Tree Borrows and invalid in Stacked Borrows for a written &mut and its parent. **Reasoning:** Tree Borrows paper: proven state-identical read-read reordering (Section 5, Example 19); the enabling mechanism is that a foreign read transitions Unique to Frozen (Section 2.2), which the toy reproduces; it also states that Stacked Borrows does not support this reordering (Section 5, p. 188:20). **Sources:** [TB] Sections 2.2 and 5 (pp. 188:8, 188:20); [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/tree_borrows/perms.rs: PermissionPriv (lines 10-53: Cell, ReservedFrz, ReservedIM, Unique, Frozen, Disabled) and the transitions child_read, foreign_read, child_write, foreign_write (lines 136-218: an unprotected Unique becomes Frozen on a foreign read, Reserved becomes Unique on a child write, a foreign write disables everything except Cell and ReservedIM). This claim is not established by the Lean kernel.

### R4d — Raw-pointer writes around a parent read: stack defined, tree UB

Card id `R4d-raw-write-around-parent-read`.

- **Kind and tier:** counterexample; T0. The Tree Borrows paper's Example 16 (Section 4.1, pp. 188:14-15): accepted by Stacked Borrows, rejected by Tree Borrows. Restated in the toy models.
- **Plain claim:** The program let tmp = &mut *root; let ptr = tmp as *mut _; *ptr = 1; read root; *ptr = 2 is defined (observing [1]) in the toy stack model and UB in the toy tree model, because the stack keeps the raw pointer's own item when the parent read removes tmp, while the tree gives the raw pointer tmp's tag, which the parent read freezes after the first write.
- **Lean statement** (verbatim from `lean/ToyAlias/Tree.lean`; proof omitted): `Toy.Alias.Tree.stack_defined_tree_ub_rawWriteAroundParentRead`

```lean
-- lean/ToyAlias/Tree.lean:290-292
theorem stack_defined_tree_ub_rawWriteAroundParentRead :
    (runStack [0] rawWriteAroundParentRead initMem).map Prod.fst = some [1] ∧
      runTree [0] rawWriteAroundParentRead initTMem = none
```

- **Reading with key definitions unfolded:** `rawWriteAroundParentRead = [reborrowMut 0, reborrowRaw 1, write 2 1, read 0, write 2 2]` with environment `[0]`: `(runStack [0] rawWriteAroundParentRead initMem).map Prod.fst = some [1]` (defined; the one read through the root observes `1`) and `runTree [0] rawWriteAroundParentRead initTMem = none` (UB). Stack: the raw pointer is a fresh `sharedRW` item (tag 2) above `tmp` (tag 1); the read through the root removes `tmp` but not the raw pointer's item, so the second write is allowed. Tree: the raw pointer uses `tmp`'s tag; the first write activates `tmp` (`unique`), the foreign read through the root freezes it, and the second write, local to the frozen node, is UB.
- **Hypothesis ledger:** none (a closed statement about one concrete program).
- **Depth:** definitional: evaluation of two concrete runs, checked by `decide`.
- **Non-vacuity witness:** Closed statement about one concrete program (no hypotheses).
- **Prior art:**
  - Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 (Section 2.3, p. 188:9: raw pointers inherit the parent's tag; Section 4.1, Example 16, pp. 188:14-15).
  - Rust Unsafe Code Guidelines, issue #248, 'Stacked Borrows: track raw pointers more precisely' (2020). https://github.com/rust-lang/unsafe-code-guidelines/issues/248 (cited by the Tree Borrows paper, Section 4.1, for the change of the Stacked Borrows implementation to tagged raw pointers).
- **Design question:** Rust's aliasing models (Stacked Borrows, Tree Borrows) exist to justify compiler optimizations that move or eliminate memory accesses through references across code the compiler cannot see. In a deliberately small borrow-tracking model, which optimizations are justified? What does each one need: protectors for function arguments, no interior mutability, or no prior reads? Where do stack-structured and tree-structured permission models differ? Specifically: Where do stack-structured and tree-structured permission models differ (raw pointers derived from a &mut)?
- **Non-claims:** listed under **Boundaries** (the global non-claims and those of `R4d-raw-write-around-parent-read`).

Basis: execution (Lean kernel check) — the statement above and every Lean name in its ledger, witness, control, and companion lines are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** Stacked Borrows accepts and Tree Borrows rejects this program. **Reasoning:** Stated by the Tree Borrows paper for its Example 16 (Section 4.1): in Stacked Borrows the read from root invalidates tmp but not the raw pointer, which stays SharedRW; in Tree Borrows the raw pointer is tmp, which becomes Unique at the first write and Frozen at the read from root. The toy reproduces both traces. **Sources:** [TB] Section 4.1 (pp. 188:14-15); [Miri] rust-lang/miri commit 0a0ce195cb0e91890c21ed717cca6eefef5e1ff3 (commit dated 2026-11-20; observed 2026-11-20), src/borrow_tracker/tree_borrows/perms.rs: PermissionPriv (lines 10-53: Cell, ReservedFrz, ReservedIM, Unique, Frozen, Disabled) and the transitions child_read, foreign_read, child_write, foreign_write (lines 136-218: an unprotected Unique becomes Frozen on a foreign read, Reserved becomes Unique on a child write, a foreign write disables everything except Cell and ReservedIM); src/borrow_tracker/stacked_borrows/mod.rs: NewPermission::from_ref_ty (lines 62-131: &mut gets Unique with a write access and, at function entry, a protector; a frozen &T gets SharedReadOnly with a read access; *mut gets SharedReadWrite with no access and no protector), Stack::find_first_write_incompatible (lines 201-225), Stack::access (lines 271-355: a write pops every item above the first write-incompatible item; a read disables the Unique items above the granting item), Stack::grant (lines 382-441: a SharedReadWrite reborrow without access is inserted at the first write-incompatible position). This claim is not established by the Lean kernel.

### Counterexample instances at a glance

Each tightness theorem states: the listed instance satisfies every *other* hypothesis of its
result exactly as stated, the dropped hypothesis is false, and both `¬ Refines tgt src` and
`¬ VisiblyRefines tgt src` hold. Parent tag `a = 0` throughout. Visible outcomes are written
`(returned?, observations, stored value)`; `T`/`F` = returned / halted. The outcome columns were
evaluated with `#eval` and agree with the theorems' statements.

| theorem | `p` | `prot` | `ts` | callee | state | source (visible) | target (visible) |
|---|---|---|---|---|---|---|---|
| `readElim_unpassed_needed` | unique | false | `[1]` (= x) | `write 0 9` | `initMem` | `(T, [0,9], 9)` | `(T, [0,0], 9)` |
| `readElim_unique_needed` | sharedRW | false | `[1]` (sibling) | `write 0 9` | `memSibling` | `(T, [0,9], 9)` | `(T, [0,0], 9)` |
| `readElim_fresh_or_protected_needed` | unique | false | `[0]` (parent) | `write 0 9` | `memDupNext` | `(T, [0,9], 9)` | `(T, [0,0], 9)` |
| `readElim_sharedRO_needed` | sharedRW | false | `[1]` (= x) | `write 0 9` | `initMem` | `(T, [0,9], 9)` | `(T, [0,0], 9)` |
| `readElim_sharedRO_fresh_or_protected_needed` | sharedRO | false | `[1]` (= x) | `write 0 9` | `memDupNext` | `(T, [0,9], 9)` | `(T, [0,0], 9)` |
| `readDefer_protected_needed` | unique | false | `[0]` (parent) | `read 0` | `initMem` | `(T, [0,0], 0)` | UB |
| `readDefer_unpassed_needed` | unique | true | `[1]` (= x) | `write 0 9` | `initMem` | `(T, [0], 9)` | `(T, [9], 9)` |
| `readDefer_unique_needed` | sharedRW | true | `[1]` (sibling) | `write 0 9` | `memSibling` | `(T, [0], 9)` | `(T, [9], 9)` |
| `readDefer_sharedRO_protected_needed` | sharedRO | false | `[0]` (parent) | `write 0 9` | `initMem` | `(T, [0], 9)` | UB |
| `readDefer_sharedRO_needed` | sharedRW | true | `[1]` (= x) | `write 0 9` | `initMem` | `(T, [0], 9)` | `(T, [9], 9)` |
| `dse_protected_needed` (v₁=5, v₂=7) | unique | false | `[0]` (parent) | `read 0; halt` | `initMem` | `(F, [5], –)` | `(F, [0], –)` |
| `dse_unique_needed` (5, 7) | sharedRW | true | `[0]` (parent) | `read 0` | `initMem` | `(T, [5], 7)` | `(T, [0], 7)` |
| `dse_unpassed_needed` (5, 7) | unique | true | `[1]` (= x) | `read 0` | `initMem` | `(T, [5], 7)` | `(T, [0], 7)` |
| `storeElim_without_overwrite_not_refines` (v₁=5) | unique | true | `[]` | (none) | `initMem` | `(T, [], 5)` | `(T, [], 0)` |

Tree-model runs: `runStack [0] parentReadThenChildWrite initMem = none` and
`runTree [0] parentReadThenChildWrite initTMem = some ([0, 5], ⟨5, [⟨0, none, unique⟩, ⟨1, some 0, unique⟩], 2⟩)`;
`runStack [0] rawWriteAroundParentRead initMem = some ([1], ⟨2, [⟨sharedRW, 2, false⟩, ⟨unique, 0, false⟩], 3⟩)`
and `runTree [0] rawWriteAroundParentRead initTMem = none`.

### Verbatim statements of counterexamples, witnesses, controls, and companions

Every Lean name referenced by a card other than the main statements above, verbatim (proofs omitted; all proved by `decide` unless stated otherwise in the source).

#### `Toy.Alias.readElim_fresh_or_protected_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:254-260
theorem readElim_fresh_or_protected_needed :
    ¬ (NextFresh memDupNext ∨ false = true) ∧ Perm.unique = .unique ∧
      memDupNext.next ∉ [0] ∧
      ¬ Refines (readElimTgt .unique false 0 [0] [.write 0 9] memDupNext)
          (readElimSrc .unique false 0 [0] [.write 0 9] memDupNext) ∧
      ¬ VisiblyRefines (readElimTgt .unique false 0 [0] [.write 0 9] memDupNext)
          (readElimSrc .unique false 0 [0] [.write 0 9] memDupNext)
```

#### `Toy.Alias.readElim_unique_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:241-247
theorem readElim_unique_needed :
    (NextFresh memSibling ∨ false = true) ∧ ¬ Perm.sharedRW = .unique ∧
      memSibling.next ∉ [1] ∧
      ¬ Refines (readElimTgt .sharedRW false 0 [1] [.write 0 9] memSibling)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] memSibling) ∧
      ¬ VisiblyRefines (readElimTgt .sharedRW false 0 [1] [.write 0 9] memSibling)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] memSibling)
```

#### `Toy.Alias.readElim_unpassed_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:230-235
theorem readElim_unpassed_needed :
    (NextFresh initMem ∨ false = true) ∧ Perm.unique = .unique ∧ ¬ initMem.next ∉ [1] ∧
      ¬ Refines (readElimTgt .unique false 0 [1] [.write 0 9] initMem)
          (readElimSrc .unique false 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readElimTgt .unique false 0 [1] [.write 0 9] initMem)
          (readElimSrc .unique false 0 [1] [.write 0 9] initMem)
```

#### `Toy.Alias.readElim_unpassed_nonvacuous` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:266-269
theorem readElim_unpassed_nonvacuous :
    (NextFresh initMem ∨ false = true) ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (readElimSrc .unique false 0 [0] [.emit 3, .retag 0 .sharedRW, .emit 4] initMem).visible =
        some (true, [3, 4, 0, 0], some 0)
```

#### `Toy.Alias.readElim_unpassed_nonvacuous_halting` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:275-278
theorem readElim_unpassed_nonvacuous_halting :
    (NextFresh initMem ∨ false = true) ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (readElimSrc .unique false 0 [0] [.write 0 9, .read 0, .halt] initMem).visible =
        some (false, [9], none)
```

#### `Toy.Alias.memSibling_reachable` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:152
theorem memSibling_reachable : retag 0 .sharedRW false initMem = some (1, memSibling)
```

#### `Toy.Alias.not_tagsBelowNext_memDupNext` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:141
theorem not_tagsBelowNext_memDupNext : ¬ TagsBelowNext memDupNext
```

#### `Toy.Alias.readElim_sharedRO_fresh_or_protected_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:347-352
theorem readElim_sharedRO_fresh_or_protected_needed :
    ¬ (NextFresh memDupNext ∨ false = true) ∧ Perm.sharedRO = .sharedRO ∧
      ¬ Refines (readElimTgt .sharedRO false 0 [1] [.write 0 9] memDupNext)
          (readElimSrc .sharedRO false 0 [1] [.write 0 9] memDupNext) ∧
      ¬ VisiblyRefines (readElimTgt .sharedRO false 0 [1] [.write 0 9] memDupNext)
          (readElimSrc .sharedRO false 0 [1] [.write 0 9] memDupNext)
```

#### `Toy.Alias.readElim_sharedRO_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:335-340
theorem readElim_sharedRO_needed :
    (NextFresh initMem ∨ false = true) ∧ ¬ Perm.sharedRW = .sharedRO ∧
      ¬ Refines (readElimTgt .sharedRW false 0 [1] [.write 0 9] initMem)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readElimTgt .sharedRW false 0 [1] [.write 0 9] initMem)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] initMem)
```

#### `Toy.Alias.readElim_sharedRO_nonvacuous` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:357-360
theorem readElim_sharedRO_nonvacuous :
    (NextFresh initMem ∨ false = true) ∧ Perm.sharedRO = .sharedRO ∧
      (readElimSrc .sharedRO false 0 [1] [.read 0, .retag 0 .sharedRO, .read 1]
        initMem).visible = some (true, [0, 0, 0, 0], some 0)
```

#### `Toy.Alias.readDefer_protected_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:430-435
theorem readDefer_protected_needed :
    ¬ false = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      ¬ Refines (readDeferTgt .unique false 0 [0] [.read 0] initMem)
          (readDeferSrc .unique false 0 [0] [.read 0] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .unique false 0 [0] [.read 0] initMem)
          (readDeferSrc .unique false 0 [0] [.read 0] initMem)
```

#### `Toy.Alias.readDefer_unique_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:449-454
theorem readDefer_unique_needed :
    true = true ∧ ¬ Perm.sharedRW = .unique ∧ memSibling.next ∉ [1] ∧
      ¬ Refines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] memSibling)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] memSibling) ∧
      ¬ VisiblyRefines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] memSibling)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] memSibling)
```

#### `Toy.Alias.readDefer_unpassed_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:439-444
theorem readDefer_unpassed_needed :
    true = true ∧ Perm.unique = .unique ∧ ¬ initMem.next ∉ [1] ∧
      ¬ Refines (readDeferTgt .unique true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .unique true 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .unique true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .unique true 0 [1] [.write 0 9] initMem)
```

#### `Toy.Alias.readDefer_unpassed_nonvacuous` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:459-462
theorem readDefer_unpassed_nonvacuous :
    true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (readDeferSrc .unique true 0 [0] [.emit 3, .retag 0 .sharedRW] initMem).visible =
        some (true, [3, 0], some 0)
```

#### `Toy.Alias.readDeferSrc_unique_ub_of_touches` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:872-874
theorem readDeferSrc_unique_ub_of_touches (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hts : m.next ∉ ts) (htouch : TouchesBeforeHalt c = true) :
    readDeferSrc .unique true a ts c m = .ub
```

#### `Toy.Alias.runCallee_ub_of_touches_of_protected_unique_head` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:773-777
theorem runCallee_ub_of_touches_of_protected_unique_head
    (c : List COp) (env : List Tag) (x : Tag) (m : Mem) (rest : List Item)
    (hstack : m.stack = ⟨.unique, x, true⟩ :: rest) (henv : x ∉ env) (hnext : x < m.next)
    (htouch : TouchesBeforeHalt c = true) :
    runCallee env c m = .ub
```

#### `Toy.Alias.readDefer_sharedRO_protected_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:519-524
theorem readDefer_sharedRO_protected_needed :
    ¬ false = true ∧ Perm.sharedRO = .sharedRO ∧
      ¬ Refines (readDeferTgt .sharedRO false 0 [0] [.write 0 9] initMem)
          (readDeferSrc .sharedRO false 0 [0] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .sharedRO false 0 [0] [.write 0 9] initMem)
          (readDeferSrc .sharedRO false 0 [0] [.write 0 9] initMem)
```

#### `Toy.Alias.readDefer_sharedRO_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:529-534
theorem readDefer_sharedRO_needed :
    true = true ∧ ¬ Perm.sharedRW = .sharedRO ∧
      ¬ Refines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] initMem)
```

#### `Toy.Alias.readDefer_sharedRO_nonvacuous` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:538-541
theorem readDefer_sharedRO_nonvacuous :
    true = true ∧ Perm.sharedRO = .sharedRO ∧
      (readDeferSrc .sharedRO true 0 [1] [.read 0] initMem).visible =
        some (true, [0, 0], some 0)
```

#### `Toy.Alias.dse_protected_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:613-618
theorem dse_protected_needed :
    ¬ false = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      ¬ Refines (dseTgt .unique false 0 [0] [.read 0, .halt] 7 initMem)
          (dseSrc .unique false 0 [0] [.read 0, .halt] 5 7 initMem) ∧
      ¬ VisiblyRefines (dseTgt .unique false 0 [0] [.read 0, .halt] 7 initMem)
          (dseSrc .unique false 0 [0] [.read 0, .halt] 5 7 initMem)
```

#### `Toy.Alias.dse_unique_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:623-628
theorem dse_unique_needed :
    true = true ∧ ¬ Perm.sharedRW = .unique ∧ initMem.next ∉ [0] ∧
      ¬ Refines (dseTgt .sharedRW true 0 [0] [.read 0] 7 initMem)
          (dseSrc .sharedRW true 0 [0] [.read 0] 5 7 initMem) ∧
      ¬ VisiblyRefines (dseTgt .sharedRW true 0 [0] [.read 0] 7 initMem)
          (dseSrc .sharedRW true 0 [0] [.read 0] 5 7 initMem)
```

#### `Toy.Alias.dse_unpassed_needed` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:632-637
theorem dse_unpassed_needed :
    true = true ∧ Perm.unique = .unique ∧ ¬ initMem.next ∉ [1] ∧
      ¬ Refines (dseTgt .unique true 0 [1] [.read 0] 7 initMem)
          (dseSrc .unique true 0 [1] [.read 0] 5 7 initMem) ∧
      ¬ VisiblyRefines (dseTgt .unique true 0 [1] [.read 0] 7 initMem)
          (dseSrc .unique true 0 [1] [.read 0] 5 7 initMem)
```

#### `Toy.Alias.dse_nonvacuous` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:642-645
theorem dse_nonvacuous :
    true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (dseSrc .unique true 0 [0] [.emit 3, .retag 0 .sharedRW] 5 7 initMem).visible =
        some (true, [3], some 7)
```

#### `Toy.Alias.dse_nonvacuous_halting` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:650-653
theorem dse_nonvacuous_halting :
    true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (dseSrc .unique true 0 [0] [.emit 3, .halt] 5 7 initMem).visible =
        some (false, [3], none)
```

#### `Toy.Alias.storeElim_without_overwrite_not_refines` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:659-669
theorem storeElim_without_overwrite_not_refines :
    (true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ ([] : List Tag) ∧
        NextFresh initMem) ∧
      storeElimSrc .unique true 0 [] [] 5 initMem =
        .done [] ⟨5, [⟨.unique, 1, true⟩, ⟨.unique, 0, false⟩], 2⟩ ∧
      storeElimTgt .unique true 0 [] [] initMem =
        .done [] ⟨0, [⟨.unique, 1, true⟩, ⟨.unique, 0, false⟩], 2⟩ ∧
      ¬ Refines (storeElimTgt .unique true 0 [] [] initMem)
          (storeElimSrc .unique true 0 [] [] 5 initMem) ∧
      ¬ VisiblyRefines (storeElimTgt .unique true 0 [] [] initMem)
          (storeElimSrc .unique true 0 [] [] 5 initMem)
```

#### `Toy.Alias.dseSrc_sharedRO_protected_ub` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:685-687
theorem dseSrc_sharedRO_protected_ub
    (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat) (m : Mem) :
    dseSrc .sharedRO true a ts c v₁ v₂ m = .ub
```

#### `Toy.Alias.dse_sharedRO_tgt_defined_src_ub` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:715-717
theorem dse_sharedRO_tgt_defined_src_ub :
    dseSrc .sharedRO true 0 [] [.halt] 5 7 initMem = .ub ∧
      dseTgt .sharedRO true 0 [] [.halt] 7 initMem = .halted []
```

#### `Toy.Alias.dseSrc_ub_of_touches` (`lean/ToyAlias/Optimizations.lean`)

```lean
-- lean/ToyAlias/Optimizations.lean:851-853
theorem dseSrc_ub_of_touches (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat)
    (m : Mem) (hts : m.next ∉ ts) (htouch : TouchesBeforeHalt c = true) :
    dseSrc .unique true a ts c v₁ v₂ m = .ub
```

#### `Toy.Alias.Tree.tree_read_read_commute_nonvacuous` (`lean/ToyAlias/Tree.lean`)

```lean
-- lean/ToyAlias/Tree.lean:479-484
theorem tree_read_read_commute_nonvacuous :
    let m0 : TMem := ⟨42, [⟨0, none, .unique⟩, ⟨1, some 0, .unique⟩], 2⟩
    let lhs := (tread 0 m0).bind fun (v₁, m₁) =>
      (tread 1 m₁).map fun (v₂, m₂) => ((v₁, v₂), m₂)
    lhs = some ((42, 42), ⟨42, [⟨0, none, .unique⟩, ⟨1, some 0, .frozen⟩], 2⟩) ∧
      lhs.map Prod.snd ≠ some m0
```

#### `Toy.Alias.Tree.stack_read_read_not_commute` (`lean/ToyAlias/Tree.lean`)

```lean
-- lean/ToyAlias/Tree.lean:489-493
theorem stack_read_read_not_commute :
    ((read 1 ⟨42, [⟨.unique, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩).bind fun (_, m) => read 0 m).isSome
        = true ∧
      ((read 0 ⟨42, [⟨.unique, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩).bind fun (_, m) => read 1 m)
        = none
```

#### `Toy.Alias.Tree.readRead_swap_stack_rejects_tree_agrees` (`lean/ToyAlias/Tree.lean`)

```lean
-- lean/ToyAlias/Tree.lean:274-278
theorem readRead_swap_stack_rejects_tree_agrees :
    (runStack [0] readReadSrc initMem).isSome = true ∧
      runStack [0] readReadTgt initMem = none ∧
      (runTree [0] readReadSrc initTMem).isSome = true ∧
      runTree [0] readReadTgt initTMem = runTree [0] readReadSrc initTMem
```

With the program definitions unfolded (`lean/ToyAlias/Tree.lean`): `readReadSrc = [reborrowMut 0, write 1 42, read 1, read 0]` (`let x = &mut *root; *x = 42; read x; read root`) and `readReadTgt = [reborrowMut 0, write 1 42, read 0, read 1]` (`let x = &mut *root; *x = 42; read root; read x`), both run with environment `[0]` (the root tag; `x` receives tag 1). In the toy stack model the source is defined and the target is UB (the read through `root` removes `x`'s `unique` item, so the later read through `x` fails); in the toy tree model both are defined and produce the same observations and final tree (the write through `x` turns its node from `reserved` into `unique`, the active state; the foreign read through `root` then makes it `frozen`, which still permits the read through `x`).

## Boundaries

### Non-claims (global; they apply to every stack result R1a, R2a, R1b, R2b, R3)

- **Toy, not the real models.** One tracked location; no provenance, no allocation or
  deallocation, no multiple locations or ranges; no `Box`; no two-phase borrows; only explicit
  reborrows (no other retag kinds); no unwinding; no concurrency. The rule deviations 1-5 listed
  under **Applicability** apply.
- **Single location.** Unknown code can only act on the tracked location or act observably
  (`emit`). Below a protected unpassed `&mut`, every callee that accesses the location before
  halting has UB (`runCallee_ub_of_touches_of_protected_unique_head`); R1a, R1b and R3 test
  same-location conflict detection, not unknown code reading or writing other memory.
- **Protectors and refinement.** Protectors never end, and `Refines` compares the exact final
  state. Not modelled: the end of a protector at function return, continuations after return,
  or simulation-based contextual refinement in which internal borrow states may differ.
- **Unknown code** is a fixed, non-adaptive operation sequence: it cannot branch on values it
  reads, and its reborrows are unprotected. It can act observably and halt. Not shown: that the
  results extend to adaptive callees.
- **Fixed shapes.** Each optimization is one program shape placed immediately after the
  function-entry reborrow. Not shown: soundness in arbitrary contexts or after other code in the
  body.
- **No deallocation.** Nothing here shows that protectors prevent unknown code from deallocating
  the location.
- **One-way.** Only refinement is stated; whether the reverse transformation is also a
  refinement is not claimed. Refinement is for a deterministic semantics with a single outcome
  per program; nothing is claimed about nondeterministic or concurrent refinement.
- **No transfer by proof.** A proof in this package says nothing about the Rust compiler, Miri,
  Stacked Borrows, or Tree Borrows; each such connection is a separate `derived (modeling
  bridge)` claim, stated per result under **Findings**.
- **Proof-internal declarations.** The declarations of `lean/ToyAlias/CalleeInvariant.lean` and
  the private lemmas of `lean/ToyAlias/Optimizations.lean` are proof infrastructure; they carry
  no card, no tightness analysis, and no recorded statement hash.

### Non-claims of each result (verbatim from `results.json`)

#### R1a — Read elimination through an unpassed `&mut` (`R1a-read-elim-mut-unpassed`)

- Does not say a protector is needed for this shape: when the tag is fresh it is not (a callee that uses an aliasing tag and returns makes the source's own second read UB; a callee that halts stops both sides before that read).
- Proves read-then-read elimination (v1 := *x; f(ts); v2 := *x becomes return v1 twice). It is not store-to-load forwarding (*x = v; f(ts); return *x, the Stacked Borrows paper's example1), and it is not moving a read down across the call (that needs a protector: R1b).
- Does not cover passing a reborrow or raw pointer derived from x (such as &mut *x, &*x, or x as *mut T) to the callee.
- For a read-only shared reference (p = sharedRO) see R2a, which also allows passing the reference to the callee.
- The hypothesis NextFresh m or prot = true matters only on states that violate TagsBelowNext; initMem satisfies TagsBelowNext and read, write, retag and runCallee preserve it (tagsBelowNext_read, tagsBelowNext_write, tagsBelowNext_retag, tagsBelowNext_runCallee), and its counterexample uses the unreachable state memDupNext. It is a well-formedness condition on the tag counter, not an aliasing condition.
- Does not transfer without qualification to Tree Borrows for mutable references to interior-mutable data (&mut Cell<T>): without a protector, Tree Borrows starts such references in ReservedIM, which tolerates foreign writes before activation (Tree Borrows paper, Section 2.4), so a callee writing through a parent would not make the second read UB.
- Single location: a returning callee that accesses the location through a parent makes the source UB, so the returning executions covered non-trivially are those whose callee only emits or creates sharedRW reborrows; callees that access the location are covered only when they halt.
- Toy model with one tracked location: not Stacked Borrows or Tree Borrows. Omitted: provenance, allocation and deallocation, multiple locations and ranges, Box, two-phase borrows, retag kinds other than an explicit reborrow, unwinding, concurrency.
- Deviations from the Stacked Borrows paper's rules: a read removes (rather than disables) the unique items above the granting item; a write removes every item above the granting item (the paper keeps the adjacent group of SharedRW items above a SharedRW granting item); a new sharedRW item is inserted directly above the granting item (the paper inserts it above the adjacent SharedRW group when the granting item is SharedRW). Consequently, in this toy a sharedRW item can remove another sharedRW item above it by writing, whereas in Stacked Borrows adjacent SharedRW items do not remove each other. Raw pointers appear only as tagged sharedRW items (the paper uses the untagged ⊥; the later Miri implementation tags raw pointers).
- Protectors are permanent flags that never end, and Refines compares the exact final state (value, borrow stack, tag counter). Not modelled: the end of a protector at function return, continuations after return, or simulation-based contextual refinement in which internal borrow states may differ.
- Unknown code is a fixed, non-adaptive operation sequence (it cannot branch on values it reads; its reborrows are unprotected); it may act observably (emit) and may halt. Extension to adaptive callees is not proved.
- The optimization is a fixed program shape placed immediately after the function-entry reborrow; soundness in arbitrary surrounding code is not shown.
- Allocation and deallocation are not modelled; nothing here shows that protectors prevent unknown code from deallocating the location.
- Only one-way refinement is stated; whether the reverse transformation is also a refinement is not claimed.
- Nothing about the Rust compiler, Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R2a — Read elimination through a read-only shared reference (`R2a-read-elim-shared-ro`)

- Does not model partial interior mutability (such as &(T, Cell<U>)), which needs per-location (per-byte) tracking of read-only versus read-write permissions.
- Does not justify inserting a read where the source performs none (for example hoisting a load out of a loop that may run zero times); in Tree Borrows such spurious reads rely on protectors and on the implicit read at retag (Tree Borrows paper, Section 3.2, Example 15).
- Equality of final states is an artifact of the toy: in Tree Borrows, deleting a read through a shared reference can leave different internal conflicted flags on protected Reserved references, and the paper's proof of that optimization uses a simulation relation (Tree Borrows paper, Section 5, Example 17).
- Says nothing about Cell or UnsafeCell beyond the counterexample with a sharedRW permission. No claim that the read may be moved down without a protector (it may not: R2b).
- The hypothesis NextFresh m or prot = true matters only on states that violate TagsBelowNext; initMem satisfies TagsBelowNext and read, write, retag and runCallee preserve it (tagsBelowNext_read, tagsBelowNext_write, tagsBelowNext_retag, tagsBelowNext_runCallee), and its counterexample uses the unreachable state memDupNext. It is a well-formedness condition on the tag counter, not an aliasing condition.
- Toy model with one tracked location: not Stacked Borrows or Tree Borrows. Omitted: provenance, allocation and deallocation, multiple locations and ranges, Box, two-phase borrows, retag kinds other than an explicit reborrow, unwinding, concurrency.
- Deviations from the Stacked Borrows paper's rules: a read removes (rather than disables) the unique items above the granting item; a write removes every item above the granting item (the paper keeps the adjacent group of SharedRW items above a SharedRW granting item); a new sharedRW item is inserted directly above the granting item (the paper inserts it above the adjacent SharedRW group when the granting item is SharedRW). Consequently, in this toy a sharedRW item can remove another sharedRW item above it by writing, whereas in Stacked Borrows adjacent SharedRW items do not remove each other. Raw pointers appear only as tagged sharedRW items (the paper uses the untagged ⊥; the later Miri implementation tags raw pointers).
- Protectors are permanent flags that never end, and Refines compares the exact final state (value, borrow stack, tag counter). Not modelled: the end of a protector at function return, continuations after return, or simulation-based contextual refinement in which internal borrow states may differ.
- Unknown code is a fixed, non-adaptive operation sequence (it cannot branch on values it reads; its reborrows are unprotected); it may act observably (emit) and may halt. Extension to adaptive callees is not proved.
- The optimization is a fixed program shape placed immediately after the function-entry reborrow; soundness in arbitrary surrounding code is not shown.
- Allocation and deallocation are not modelled; nothing here shows that protectors prevent unknown code from deallocating the location.
- Only one-way refinement is stated; whether the reverse transformation is also a refinement is not claimed.
- Nothing about the Rust compiler, Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R1b — Moving a read through a protected `&mut` down across the call (`R1b-read-defer-mut-protected`)

- For a read-only shared reference (p = sharedRO) see R2b, which also allows passing the reference.
- Does not model deallocation or function return: deferring a read past a deallocation performed by the callee, or past the end of the protector's call, is not covered.
- Does not cover moving the read down past code other than one unknown call.
- Only one location is tracked, and unknown code can otherwise only act observably (emit). Under the hypotheses, every callee that accesses the location before halting makes the source UB (readDeferSrc_unique_ub_of_touches); the result tests same-location conflict detection, not unknown code reading or writing other memory.
- Toy model with one tracked location: not Stacked Borrows or Tree Borrows. Omitted: provenance, allocation and deallocation, multiple locations and ranges, Box, two-phase borrows, retag kinds other than an explicit reborrow, unwinding, concurrency.
- Deviations from the Stacked Borrows paper's rules: a read removes (rather than disables) the unique items above the granting item; a write removes every item above the granting item (the paper keeps the adjacent group of SharedRW items above a SharedRW granting item); a new sharedRW item is inserted directly above the granting item (the paper inserts it above the adjacent SharedRW group when the granting item is SharedRW). Consequently, in this toy a sharedRW item can remove another sharedRW item above it by writing, whereas in Stacked Borrows adjacent SharedRW items do not remove each other. Raw pointers appear only as tagged sharedRW items (the paper uses the untagged ⊥; the later Miri implementation tags raw pointers).
- Protectors are permanent flags that never end, and Refines compares the exact final state (value, borrow stack, tag counter). Not modelled: the end of a protector at function return, continuations after return, or simulation-based contextual refinement in which internal borrow states may differ.
- Unknown code is a fixed, non-adaptive operation sequence (it cannot branch on values it reads; its reborrows are unprotected); it may act observably (emit) and may halt. Extension to adaptive callees is not proved.
- The optimization is a fixed program shape placed immediately after the function-entry reborrow; soundness in arbitrary surrounding code is not shown.
- Allocation and deallocation are not modelled; nothing here shows that protectors prevent unknown code from deallocating the location.
- Only one-way refinement is stated; whether the reverse transformation is also a refinement is not claimed.
- Nothing about the Rust compiler, Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R2b — Moving a read through a protected read-only shared reference down across the call (`R2b-read-defer-shared-ro-protected`)

- Moves an existing pre-call read down; does not justify inserting a read where the source performs none.
- Does not model deallocation or function return: deferring a read past a deallocation or past the end of the protector's call is not covered.
- Toy model with one tracked location: not Stacked Borrows or Tree Borrows. Omitted: provenance, allocation and deallocation, multiple locations and ranges, Box, two-phase borrows, retag kinds other than an explicit reborrow, unwinding, concurrency.
- Deviations from the Stacked Borrows paper's rules: a read removes (rather than disables) the unique items above the granting item; a write removes every item above the granting item (the paper keeps the adjacent group of SharedRW items above a SharedRW granting item); a new sharedRW item is inserted directly above the granting item (the paper inserts it above the adjacent SharedRW group when the granting item is SharedRW). Consequently, in this toy a sharedRW item can remove another sharedRW item above it by writing, whereas in Stacked Borrows adjacent SharedRW items do not remove each other. Raw pointers appear only as tagged sharedRW items (the paper uses the untagged ⊥; the later Miri implementation tags raw pointers).
- Protectors are permanent flags that never end, and Refines compares the exact final state (value, borrow stack, tag counter). Not modelled: the end of a protector at function return, continuations after return, or simulation-based contextual refinement in which internal borrow states may differ.
- Unknown code is a fixed, non-adaptive operation sequence (it cannot branch on values it reads; its reborrows are unprotected); it may act observably (emit) and may halt. Extension to adaptive callees is not proved.
- The optimization is a fixed program shape placed immediately after the function-entry reborrow; soundness in arbitrary surrounding code is not shown.
- Allocation and deallocation are not modelled; nothing here shows that protectors prevent unknown code from deallocating the location.
- Only one-way refinement is stated; whether the reverse transformation is also a refinement is not claimed.
- Nothing about the Rust compiler, Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R3 — Dead-store elimination through a protected `&mut` before unknown code (`R3-dead-store-elim-protected`)

- Stated for p = unique only; for p = sharedRO the source is UB at its first store (dseSrc_sharedRO_protected_ub), so a statement for that case would hold only because the source is UB.
- The three hypotheses form a minimal uniform sufficient condition over all (possibly halting) callees, values, and states, each shown necessary by a counterexample; they are not an exact characterization of individual instances (for example, when the callee does nothing, removing the store is a refinement without a protector).
- Requires an unconditional overwrite *x = v2 through the same tag after the call: without it, removing the store changes the final stored value (storeElim_without_overwrite_not_refines). Conditional overwrites and overwrites through another pointer are not covered.
- Unwinding is not modelled. In Rust, if the callee unwinds, the overwrite never runs; the Stacked Borrows paper notes that the transformation then requires placing the first store on the unwinding path as well (Section 4.2, footnote 4). Removing the store outright, as here, is not justified for callees that may unwind.
- In Tree Borrows the first store is the activating write of x; the Tree Borrows paper's proof framework cannot move an activating write down (its Section 5, p. 188:20, and limitation (a) in Section 7, p. 188:22), so nothing here establishes this transformation for Tree Borrows.
- The callee cannot observe the first store without UB; nothing here concerns stores that unknown code may legitimately observe.
- Only one location is tracked, and unknown code can otherwise only act observably (emit). Under the hypotheses, every callee that accesses the location before halting makes the source UB (dseSrc_ub_of_touches); the result tests same-location conflict detection, not unknown code reading or writing other memory.
- Toy model with one tracked location: not Stacked Borrows or Tree Borrows. Omitted: provenance, allocation and deallocation, multiple locations and ranges, Box, two-phase borrows, retag kinds other than an explicit reborrow, unwinding, concurrency.
- Deviations from the Stacked Borrows paper's rules: a read removes (rather than disables) the unique items above the granting item; a write removes every item above the granting item (the paper keeps the adjacent group of SharedRW items above a SharedRW granting item); a new sharedRW item is inserted directly above the granting item (the paper inserts it above the adjacent SharedRW group when the granting item is SharedRW). Consequently, in this toy a sharedRW item can remove another sharedRW item above it by writing, whereas in Stacked Borrows adjacent SharedRW items do not remove each other. Raw pointers appear only as tagged sharedRW items (the paper uses the untagged ⊥; the later Miri implementation tags raw pointers).
- Protectors are permanent flags that never end, and Refines compares the exact final state (value, borrow stack, tag counter). Not modelled: the end of a protector at function return, continuations after return, or simulation-based contextual refinement in which internal borrow states may differ.
- Unknown code is a fixed, non-adaptive operation sequence (it cannot branch on values it reads; its reborrows are unprotected); it may act observably (emit) and may halt. Extension to adaptive callees is not proved.
- The optimization is a fixed program shape placed immediately after the function-entry reborrow; soundness in arbitrary surrounding code is not shown.
- Allocation and deallocation are not modelled; nothing here shows that protectors prevent unknown code from deallocating the location.
- Only one-way refinement is stated; whether the reverse transformation is also a refinement is not claimed.
- Nothing about the Rust compiler, Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R4a — Parent read before the first child write: stack UB, tree defined (`R4a-parent-read-before-child-write`)

- One program; no general theorem about either model.
- If x were a protected function argument, Tree Borrows would mark the Reserved reference conflicted at the foreign read and the later write would be UB (Tree Borrows paper, Section 3.1), so the verdicts would agree; the toy tree model has no protectors.
- Does not imply that Tree Borrows accepts more programs than Stacked Borrows in general: R4d gives a program accepted by the toy stack model and rejected by the toy tree model (the Tree Borrows paper's Example 16).
- Models an explicit &mut reborrow. The Miri implementation of Stacked Borrows treats implicit two-phase borrows like raw pointers (Tree Borrows paper, Section 4.1) and may accept the corresponding two-phase pattern for that reason.
- Toy tree model: one location, no protectors (hence no conflicted Reserved state and no protector-end accesses), no ReservedIM, no ranges or lazy initialization; raw pointers only as reuse of the parent's tag. Not Tree Borrows. The toy stack model is not Stacked Borrows (see the deviations listed for the stack results).
- Nothing about Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R4c — In the toy tree model, any two reads commute (`R4c-tree-reads-commute`)

- The toy tree model has one location, no protectors, no ReservedIM, no ranges or lazy initialization, and no concurrency; both reads read the same location, so the two values are always the stored value.
- Only two immediately adjacent sequential reads; nothing about reordering reads across writes, reborrows, or unknown code, or about concurrent or atomic reads.
- The companion program readRead_swap_stack_rejects_tree_agrees (source readReadSrc = [reborrowMut 0, write 1 42, read 1, read 0], i.e. let x = &mut *root; *x = 42; read x; read root; target readReadTgt = [reborrowMut 0, write 1 42, read 0, read 1], i.e. the same program with the last two reads swapped) assumes no protector: if x were a protected argument, the foreign read through root after the write would be UB in Tree Borrows in both orders (a foreign read of a protected Unique reference is UB, Tree Borrows paper, Section 3.1).
- Does not imply that read-read swaps fail in Stacked Borrows in general: reads through shared read-only references commute there; the positive control is one specific state.
- Holds on every TMem without a well-formedness assumption because locality depends only on tags and parent links; this says nothing about how the toy's other definitions behave on ill-formed trees.
- Nothing about Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

#### R4d — Raw-pointer writes around a parent read: stack defined, tree UB (`R4d-raw-write-around-parent-read`)

- One program; no general theorem about either model, and no claim about which model accepts more programs overall (R4a differs in the other direction).
- The toy stack model represents the raw pointer as a tagged sharedRW item (as the later Miri implementation of Stacked Borrows does; the Stacked Borrows paper uses an untagged ⊥, with the same verdict here); the toy tree model gives the raw pointer its parent's tag, as Tree Borrows does. Other raw-pointer behaviour (ranges, provenance, casts to integers) is not modelled.
- Toy tree model: one location, no protectors (hence no conflicted Reserved state and no protector-end accesses), no ReservedIM, no ranges or lazy initialization; raw pointers only as reuse of the parent's tag. Not Tree Borrows. The toy stack model is not Stacked Borrows (see the deviations listed for the stack results).
- Nothing about Miri, Stacked Borrows, or Tree Borrows follows from the Lean statement alone; the connection stated under modeling_bridge is a separate modelling argument.

### Escape hatches, unknown tightness, disproved or dropped statements

- **Escape hatches.** No result of this package is an impossibility result. The negative
  results are single concrete programs (R4a, R4d, and R3's shape companion
  `storeElim_without_overwrite_not_refines`) and the tightness counterexamples; each shows only
  that its specific instance fails. In particular, R4a's verdict pair depends on the absence of a
  protector: with a protected `&mut`, Tree Borrows marks the `Reserved` reference conflicted at the
  foreign read and the later write is UB (Tree Borrows paper, Section 3.1), which the toy tree
  model does not model.
- **Unknown tightness.** None: every hypothesis of every theorem is labelled `tight` and has a
  proved counterexample stating that all other hypotheses hold and both `Refines` and
  `VisiblyRefines` fail.
- **Disproved or dropped statements.** None. All eight results, and all their counterexamples,
  witnesses, controls, and companions, are proved exactly as stated.

### Not examined

- The design question's "no prior reads" condition corresponds in Tree Borrows to protected
  `Reserved` references becoming conflicted after a foreign read, after which a local write is
  UB ("UB for this reference to encounter both a foreign read and a local write—in any order",
  Tree Borrows paper, Section 3.1). The toy tree model has no protectors, so this condition is not
  examined; R4a's non-claims record how a protector would change its verdict.
- Tree Borrows' `ReservedIM` (and Miri's `Cell` state) for interior mutability is not modelled,
  so no toy-tree result covers `&mut` or `&` to interior-mutable data.
- Moving writes up, store-to-load forwarding (the Stacked Borrows paper's `example1`), and
  multiple unknown calls are not examined.

## Evidence

**Kernel-check record.** Toolchain `leanprover/lean4:v4.34.1` (`leanprover/lean4`, tag `v4.34.1`,
commit `5045d0056413266e57c625dcd7c365b10e377c52`, read from the GitHub API on 2026-11-20); Lake
project `lean/` with one library `ToyAlias` (modules `ToyAlias.Stack`, `ToyAlias.Callee`,
`ToyAlias.CalleeInvariant`, `ToyAlias.Optimizations`, `ToyAlias.Tree`) and no dependencies (core
Lean only, no Mathlib). Observed 2026-11-20: `lake build` succeeds with no `sorry` warnings; no
Lean source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations,
`implemented_by`, `@[extern]` or `unsafe`; all 539 non-internal declarations of the
library depend only on axioms among `propext`, `Classical.choice`, `Quot.sound` (in fact only on
`propext` and `Quot.sound`; per declaration in `audit/axioms.json`). Every result is
`Basis: execution (Lean kernel check)`.

**Statement and closure hashes.** For each Lean name in the fields `lean`, `lean_names`,
`nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample` of
`results.json`, `audit/statements.json` records the SHA-256 of the statement and of its
definition closure (computed as described under **Revalidation**). Roles: `R` result, `CE`
tightness counterexample, `NV` non-vacuity witness, `PC` positive control, `C` companion or
boundary theorem.

| Lean name | Used by (result: role) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `Toy.Alias.readElim_refines_of_fresh_or_protected_of_unique_of_unpassed` | R1a:R | Quot.sound, propext | `ed996e2bae8822fabc70db0c452ba5a8be944b82895d18883558e77108da20d1` | `8e7a47c94ee68342d723ef1035a0d91ff015a113d6e07e4a5caad4c75f3af4f1` (73) |
| `Toy.Alias.readElim_fresh_or_protected_needed` | R1a:CE | Quot.sound, propext | `cfb0ef08eac70aea4e0ac12e1783c5aa10a06061acf1be47112122189461a776` | `9da9cd64c49b391b59a15965fe5a82adf55ed1d6acd6185f5c04fe1863ee4e19` (76) |
| `Toy.Alias.readElim_unique_needed` | R1a:CE | Quot.sound, propext | `488d3da01c76154a95042472edb68a7b5d476872cff5229fb99fe8dc22286254` | `f96dfd4d30ae95e0889f5c5cba58cbb598c013481b00cb6a3c20087bf2fd69df` (76) |
| `Toy.Alias.readElim_unpassed_needed` | R1a:CE | Quot.sound, propext | `624f8f00d6229689ccade179ab59631e45e7e46c0e67678e7941bd61e948d631` | `8e3f9ff6ef02ceeeeeb37b8c2a6a64020a2c08e542657eabc839ebf99a023e6d` (76) |
| `Toy.Alias.readElim_unpassed_nonvacuous` | R1a:NV | Quot.sound, propext | `8453d45d6c027984456ebbaa7fbb5c410f05f19d2ac39310a290310093f6a9b4` | `e78fa535c39f38287f035ef61d8d9efd0c17b25f425b35d4504dfcb51c811d93` (73) |
| `Toy.Alias.readElim_unpassed_nonvacuous_halting` | R1a:C | Quot.sound, propext | `2679850b40fed5a4366b9fcde2f8567d10b7111cbf6efbd54b7092c79e8a791e` | `e78fa535c39f38287f035ef61d8d9efd0c17b25f425b35d4504dfcb51c811d93` (73) |
| `Toy.Alias.memSibling_reachable` | R1a:C | (none) | `383a28bb6f6142d5f8eeadafa9bf8008bfff2ab55cb48aa8a2e850126b6c6e42` | `b607f38f8926411484264fe86a23865d034ec2bff0bbef02351b380973366239` (42) |
| `Toy.Alias.not_tagsBelowNext_memDupNext` | R1a:C | (none) | `4761367436625c9e6ccf1610b427bea2c1a1e4112b0e97b7de52f7eeda296e22` | `2c3285811cc733d859a8b124e03949abb225e3108f845e39470dfad7f2a5bfd7` (14) |
| `Toy.Alias.readElim_refines_of_fresh_or_protected_of_sharedRO` | R2a:R | Quot.sound, propext | `bf70fe22758296a7973953a296191340b23de78807808dd453dfd1f9792c98cd` | `8e7a47c94ee68342d723ef1035a0d91ff015a113d6e07e4a5caad4c75f3af4f1` (73) |
| `Toy.Alias.readElim_sharedRO_fresh_or_protected_needed` | R2a:CE | propext | `85c5ead2b722d6090897e078f3bb0671698d41e8dda81d8abb7308ff9fcf7eac` | `9da9cd64c49b391b59a15965fe5a82adf55ed1d6acd6185f5c04fe1863ee4e19` (76) |
| `Toy.Alias.readElim_sharedRO_needed` | R2a:CE | propext | `4f725fc3f919362445d0906db89c8251ae41f873ce40e50f789af77155e19e43` | `8e3f9ff6ef02ceeeeeb37b8c2a6a64020a2c08e542657eabc839ebf99a023e6d` (76) |
| `Toy.Alias.readElim_sharedRO_nonvacuous` | R2a:NV | propext | `eafa7d15ba4b822ea41888cce0bfe2fc2527815cc776d793f0f930187a978667` | `e78fa535c39f38287f035ef61d8d9efd0c17b25f425b35d4504dfcb51c811d93` (73) |
| `Toy.Alias.readDefer_refines_of_protected_of_unique_of_unpassed` | R1b:R | Quot.sound, propext | `73062649b48e064f760e5b935b69c0d06d48b8c3fbe8738aadf593b6bb204ed5` | `f4855b84418598ed006966fb2a8858b1cbd1222e3e3a91cffb68a1a95f747ff5` (72) |
| `Toy.Alias.readDefer_protected_needed` | R1b:CE | Quot.sound, propext | `003a37a6b91b7a7d7accbaa9b482b9b53218b588ed8e8cd86c6029d3d1cf89b4` | `a5dbc0051761f794051363e7016ff49f378e696336208f7cf7ea422350a48600` (75) |
| `Toy.Alias.readDefer_unique_needed` | R1b:CE | Quot.sound, propext | `845d1e1dd84b67ee0b8f46dcf3fb36163f3e776344dfa42d7cba998414aa4c4d` | `977567f1b0a706c1186e98ac2cbdd44b3adc397e9f5694af75b73d1437fc97c0` (75) |
| `Toy.Alias.readDefer_unpassed_needed` | R1b:CE | Quot.sound, propext | `d69cc6adb20a7f85f32a8e95d14f6e8fbff1be615e787c120fde92a2c842a90a` | `a5dbc0051761f794051363e7016ff49f378e696336208f7cf7ea422350a48600` (75) |
| `Toy.Alias.readDefer_unpassed_nonvacuous` | R1b:NV | Quot.sound, propext | `06bdf2bcc97836db82942973834f791a00c1ed9e0aa54dd8628659134c27e6be` | `317d3abd36a20148f11f54c7cb233567ec5544b32da8a99ff918f315e6a0e8a3` (72) |
| `Toy.Alias.readDeferSrc_unique_ub_of_touches` | R1b:C | Quot.sound, propext | `3521dcaf5c135355b9f421cb4b07dc5245cb95b883cee123b82008d53231e13f` | `a68cd4fcd8063996a4c08a212c09d2e3e9342b1b390e90cd549643949454533c` (77) |
| `Toy.Alias.runCallee_ub_of_touches_of_protected_unique_head` | R1b:C, R3:C | Quot.sound, propext | `33c7d97f00adb34b4ac478c4fccd8c7c64e7416a3ab1659cd18300a426cab252` | `66e7bae98a0bed9444bd1af1b102687f636089dd45c8a2b17678a5e90b3e71ba` (72) |
| `Toy.Alias.readDefer_refines_of_protected_of_sharedRO` | R2b:R | Quot.sound, propext | `6bd65e4a0f49fedf59d890f3b252da8cc3e6cf9a9247a458edd561de9a81dde8` | `f4855b84418598ed006966fb2a8858b1cbd1222e3e3a91cffb68a1a95f747ff5` (72) |
| `Toy.Alias.readDefer_sharedRO_protected_needed` | R2b:CE | propext | `bcdbc72efb66769e7bf9655bd3bf691d722b073e653c18faf7bce0588754a34a` | `a5dbc0051761f794051363e7016ff49f378e696336208f7cf7ea422350a48600` (75) |
| `Toy.Alias.readDefer_sharedRO_needed` | R2b:CE | propext | `d80cdef1103eab058dbc24be0fd80f9c474e2c0ef176610e64679376a378a820` | `a5dbc0051761f794051363e7016ff49f378e696336208f7cf7ea422350a48600` (75) |
| `Toy.Alias.readDefer_sharedRO_nonvacuous` | R2b:NV | propext | `02aa9b9007bab7043789d3d6b3d5b8001ecc306ba12d026d25e9c1d4dae82852` | `317d3abd36a20148f11f54c7cb233567ec5544b32da8a99ff918f315e6a0e8a3` (72) |
| `Toy.Alias.dse_refines_of_protected_of_unique_of_unpassed` | R3:R | Quot.sound, propext | `64b518d68590428583c4e8f0e221c27f1ce20d64888245e1bf2772b6a9fe15ad` | `cccb2db13d16adab97408b9ee973779b364709f53c03fcfdc38ea168658b02bf` (71) |
| `Toy.Alias.dse_protected_needed` | R3:CE | Quot.sound, propext | `fb640c59a3eb52c7b6b7e17a3810f124334b68de5be387c6e218d4dd3fe42787` | `0ddaea7cc5da383c5f479fcb7a771cb5aad46cabaa81a31a4060d9e0421b9287` (74) |
| `Toy.Alias.dse_unique_needed` | R3:CE | Quot.sound, propext | `55694edac7a6b3200f5541d57292760577d893c8a6831d37bc4af961ad6bc14a` | `0ddaea7cc5da383c5f479fcb7a771cb5aad46cabaa81a31a4060d9e0421b9287` (74) |
| `Toy.Alias.dse_unpassed_needed` | R3:CE | Quot.sound, propext | `259e3c957cde3cb25720b0d94011bc99bb15025b0358b0e000f87240db98b9aa` | `0ddaea7cc5da383c5f479fcb7a771cb5aad46cabaa81a31a4060d9e0421b9287` (74) |
| `Toy.Alias.dse_nonvacuous` | R3:NV | Quot.sound, propext | `0947c0c3389fe6ab81ca558e462dea8724c3f767d6b9e1c16404cdec619315d6` | `2b6f96b397ca6898a18cade1b7d33aead428506cae3cba651debbea89dc94853` (71) |
| `Toy.Alias.dse_nonvacuous_halting` | R3:C | Quot.sound, propext | `c7cc43bb1adffa269454f5af578e8cccb8ed510b60cc1a205616141be3818315` | `2b6f96b397ca6898a18cade1b7d33aead428506cae3cba651debbea89dc94853` (71) |
| `Toy.Alias.storeElim_without_overwrite_not_refines` | R3:C | Quot.sound, propext | `572cb2300b826f79e5724cae7f44ddc69fbb63bba55a59e876ce8f7caf3e3efc` | `75eaf5a7894096eed438ab5d977bd100b5cacaaa23d67575a8154a735d3aee5e` (75) |
| `Toy.Alias.dseSrc_sharedRO_protected_ub` | R3:C | Quot.sound, propext | `34f98b729212e27a7f109b945613368648b1de00b66411007bd977efe9f39757` | `05da33334e52868cb58a83d008d3a469d905fa71afab4bc6c138aaec0118a469` (69) |
| `Toy.Alias.dse_sharedRO_tgt_defined_src_ub` | R3:C | propext | `c2f3a6aae780ed7f5fb83047bc709486e76f65a6c119fe832463f18acb8dbad7` | `c41c1ba3ba533eae4e66637144f52c084d72b64bff031b546301d0cdb8aaa932` (71) |
| `Toy.Alias.dseSrc_ub_of_touches` | R3:C | Quot.sound, propext | `40072a3d34d63fa0d8f92d87fe02ddc35b4c3096f9330fc6ce46dd91e82ae9b2` | `8374344251e45caaaee067be84146d01e64cada82c97acbdc906f41f3a01cc89` (76) |
| `Toy.Alias.Tree.stack_ub_tree_defined_parentReadThenChildWrite` | R4a:R | propext | `0f813e294db17c6ed2e6161a2b4d64fed6d741b799c5150b904867ba7d6d0d8c` | `615a0d6e2481ff72f2621685c66316570510bebfed4360787822cd1305d3cfda` (102) |
| `Toy.Alias.Tree.tree_read_read_commute` | R4c:R | Quot.sound, propext | `6b8fff1c615e18e76d25db32be77f7d2c343395e8725ad7869cfa384cfe830ba` | `1cde18f479410fc3e1fafc2625236a6df2c6ceeff05561129132359111a19323` (42) |
| `Toy.Alias.Tree.tree_read_read_commute_nonvacuous` | R4c:NV | propext | `20f426ee4a57d1cc54b11b61dd116587a2928aa6974b835255c9d694dd04bcf2` | `1cde18f479410fc3e1fafc2625236a6df2c6ceeff05561129132359111a19323` (42) |
| `Toy.Alias.Tree.stack_read_read_not_commute` | R4c:PC | (none) | `478816dce634f4f83b1d0b7cf017205d8622337a3c2e8e2bee40f352250e1299` | `ceca1620f9aa7d17cf9b5d1c3d046322829adf1a4280ff5231faab174db7e427` (38) |
| `Toy.Alias.Tree.readRead_swap_stack_rejects_tree_agrees` | R4c:C | propext | `86a17309ecd6ee07fdebd02bef3d3b48e5bfab33d2ebaea1b83b8f1ce3385d37` | `f7793063740dbb78789b80bb751abc10073a58c146c85e22f59d031478a47a1f` (103) |
| `Toy.Alias.Tree.stack_defined_tree_ub_rawWriteAroundParentRead` | R4d:R | propext | `5da17777cebb21c645f5c54f561220e8f609d07f75e8787eb251968ccff3fd1c` | `b594c7803b78c1ea63b5467df811dcd2575e51f5d17e13f037e70b510a1cb0b9` (102) |

**Primary sources** (each read at the source on 2026-11-20 unless stated otherwise):

- **[SB]** Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. *Stacked Borrows: An Aliasing
  Model for Rust.* Proc. ACM Program. Lang. 4, POPL, Article 41 (January 2020).
  https://doi.org/10.1145/3371109 . Read from the authors' PDF: `example1` (Section 3.4),
  `example2` (Sections 3.6-3.7), Section 4 (p. 41:16: `example2_down`, `example3_down`, "For
  mutable references, we can similarly move reads down across code that does not need them"),
  Section 4.1 (protectors; counterexample for `example2_down`), Section 4.2 (proof sketches;
  "even if f runs into an infinite loop"; footnote 4 on unwinding), Section 5 (rules `write-1`,
  `read-2`), Fig. 3-4 (`FindFirstWIncompat`, `Access`, `GrantTag`, pp. 41:24-25), Section 7.2
  (mechanized proofs of the example transformations).
- **[SB-artifact]** Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. *Stacked Borrows: An
  Aliasing Model for Rust - Artifact* (2019). https://doi.org/10.5281/zenodo.3541779 (DOI as
  given in [SB]'s reference list). Coq development at https://gitlab.mpi-sws.org/FP/stacked-borrows
  (README and `theories/opt/` read on 2026-11-20, branch `master`, commit not pinned): proofs of
  `example1` (`ex1.v`), `example2` (`ex2.v`), `example2_down` (`ex2_down.v`), `example3_down`
  (`ex3_down.v`), and of `example1_down` (`ex1_down.v`, lemma `ex1_down_sim_fun`) and `example3`,
  which "did not appear in the paper".
- **[Simuliris]** Lennard Gäher, Michael Sammler, Simon Spies, Ralf Jung, Hoang-Hai Dang, Robbert
  Krebbers, Jeehoon Kang, Derek Dreyer. *Simuliris: A Separation Logic Framework for Verifying
  Concurrent Program Optimizations.* Proc. ACM Program. Lang. 6, POPL, Article 28 (January 2022).
  https://doi.org/10.1145/3498689 . File `theories/stacked_borrows/examples/opt1_down.v` of
  https://gitlab.mpi-sws.org/iris/simuliris read on 2026-11-20 (commit not pinned). [TB]
  (Section 5, pp. 188:20-21) reports a flaw in its operational semantics that invalidates its
  concurrent extension of the unprotected read-hoisting proof.
- **[TB]** Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. *Tree Borrows.* Proc. ACM
  Program. Lang. 9, PLDI, Article 188 (June 2025). https://doi.org/10.1145/3735592 . Read from the
  publisher PDF: Section 2.1 (local and foreign accesses), Section 2.2 (Example 8, `Reserved`,
  footnote 3, `Frozen` and read-read reordering), Section 2.3 (p. 188:9: raw pointers use the
  parent's tag), Section 2.4 (`ReservedIM`), Section 3.1 (protectors, conflicted `Reserved`),
  Section 3.2 (implicit reads, Example 15), Section 4.1 (differences from Stacked Borrows; tagged
  raw pointers in the Stacked Borrows implementation, citing [UCG #248]; Example 16,
  pp. 188:14-15), Section 4.3 (31 tests from 12 crates newly rejected), Section 5 (Examples 17-19,
  activating writes), Section 7 (limitation (a)).
- **[TB-artifact]** Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. *Tree Borrows -
  Artifact* (2025). https://doi.org/10.5281/zenodo.15002703 (record as given in [TB]'s reference
  list; contents not inspected).
- **[Miri]** `rust-lang/miri`, commit `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3` ("Merge pull
  request #5638 from WhySoBad/udp-blocking-io", committed 2026-11-20T09:25:48Z, read from the
  GitHub API and raw files on 2026-11-20):
  - `README.md`: lists violations of the Stacked Borrows and Tree Borrows rules among Miri's
    experimental checks (lines 20-23); `-Zmiri-tree-borrows` "replaces [Stacked Borrows] with the
    [Tree Borrows] rules" (line 521).
  - `src/borrow_tracker/stacked_borrows/mod.rs`: `NewPermission::from_ref_ty` (lines 62-131: a
    regular `&mut` (pointee `Unpin`) gets `Unique` with a write access and, at function entry, a
    protector; a two-phase `&mut` gets `SharedReadWrite` "exactly like raw pointers"; a frozen
    `&T` gets `SharedReadOnly` with a read access; `*mut` gets `SharedReadWrite` with no access
    and no protector), `Stack::find_first_write_incompatible` (lines 201-225), `Stack::access`
    (lines 271-355: a write pops every item above the first write-incompatible item; a read
    disables the `Unique` items above the granting item), `Stack::grant` (lines 382-441: a
    `SharedReadWrite` reborrow without access is inserted at the first write-incompatible
    position, i.e. above the adjacent `SharedReadWrite` group).
  - `src/borrow_tracker/tree_borrows/perms.rs`: `PermissionPriv` (lines 10-53: `Cell`,
    `ReservedFrz`, `ReservedIM`, `Unique`, `Frozen`, `Disabled`) and the transitions
    `child_read`, `foreign_read`, `child_write`, `foreign_write` (lines 136-218: an unprotected
    `Unique` becomes `Frozen` on a foreign read, `Reserved` becomes `Unique` on a child write, a
    foreign write disables every state except `Cell` and `ReservedIM`). The active state is named
    `Unique`, as in [TB].
- **[UCG #248]** Rust Unsafe Code Guidelines issue #248, "Stacked Borrows: track raw pointers
  more precisely", opened 2020-08-26, https://github.com/rust-lang/unsafe-code-guidelines/issues/248
  (title and date read from the GitHub API on 2026-11-20; cited by [TB] Section 4.1).
- **Background, not relied on by any result.** [RustBelt] Ralf Jung, Jacques-Henri Jourdan,
  Robbert Krebbers, Derek Dreyer. *RustBelt: Securing the Foundations of the Rust Programming
  Language.* Proc. ACM Program. Lang. 2, POPL, Article 66 (January 2018).
  https://doi.org/10.1145/3158154 (type-system soundness, not an aliasing model). Ralf Jung.
  *Understanding and Evolving the Rust Programming Language.* PhD thesis, Saarland University,
  defended August 2020, https://doi.org/10.22028/D291-31946 (abstract only). Daniël Louwrink.
  *A Separation Logic for Stacked Borrows.* Master's thesis (2021),
  https://eprints.illc.uva.nl/id/eprint/1790/ (record as given in [TB]'s reference list; not
  inspected). C and LLVM aliasing rules, surveyed in [SB] Section 8 and [TB] Section 6 (records
  as given in their reference lists, not inspected): Xavier Leroy and Sandrine Blazy, *Formal
  Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations*,
  J. Autom. Reason. 41(1), 1-31 (2008), https://doi.org/10.1007/s10817-008-9099-0 ; Robbert
  Krebbers, *Aliasing Restrictions of C11 Formalized in Coq*, CPP 2013, 50-65; Chris Hathhorn,
  Chucky Ellison, Grigore Rosu, *Defining the Undefinedness of C*, PLDI 2015, 336-345.

All evidence was acquired or revalidated on 2026-11-20.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; the Lean project has no dependencies.

**Primary check (one command).** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`,
rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration,
and then elaborates an inline audit program that (1) computes, with Lean's `collectAxioms`, the
axioms of every declaration of the `ToyAlias` library and fails if any uses an axiom other than
`propext`, `Classical.choice`, `Quot.sound`; and (2) for every Lean name referenced by
`results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`,
and hypothesis `counterexample`s) and every name recorded in `audit/statements.json`, recomputes
two SHA-256 hashes and compares them with `audit/statements.json`:

- the **statement hash**: SHA-256 of `toString (repr ci.type)`, the Lean `repr` of the
  declaration's elaborated type;
- the **closure hash**: SHA-256 of the newline-joined, sorted list of entries
  `name : repr(type)` (plus ` := repr(value)` for non-theorems) for every constant of the
  `ToyAlias` library reachable from the statement's type through types, definition bodies and
  inductive constructors (theorem bodies excluded). A change to any definition a statement depends
  on therefore changes its closure hash; documentation comments are not part of either hash.

It prints `REVALIDATED` and exits with status 0 iff every check passes. Expected output ends with
`ok   axioms (539 declarations)`, `ok   statement hashes (39 hashed names; 0 referenced
names exist but carry no recorded hash)` and `REVALIDATED`.

**Manual equivalent.**

```sh
cd lean
lake build                              # builds library ToyAlias; must succeed with no `sorry` warnings
lake env lean RevalidationAudit.lean    # prints `#print axioms` for every name cited in REPORT.md
```

`lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`). It
imports `ToyAlias` and issues `#print axioms` for every Lean name cited in `REPORT.md` or
`results.json`, including the definition examples, boundary facts, and proof-infrastructure
declarations that carry no recorded hash; elaboration fails if any name is missing, and each
printed line must list only (a subset of) `propext`, `Classical.choice`, `Quot.sound`. The
recorded per-declaration axioms are in `audit/axioms.json`.

**Cheaper discriminating checks.** If only the Lean toolchain changes, re-running the primary
check is sufficient: a changed elaboration of any statement or definition shows up as a hash
mismatch even when the build succeeds. If a definition in `lean/ToyAlias/` is edited, every card
whose closure includes it is stale; the closure hashes identify which. A passing revalidation
establishes only the kernel-checked statements; it does not re-check any modeling-bridge claim or
citation, which must be re-read against the sources listed under **Evidence** (for Miri, diff the
cited files between commit `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3` and the revision of
interest).
