# rustc MIR move elimination: `TailCopyToMove`, `MoveElimination`, place unification and borrowed-local NRVO

## Summary

At `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (rustc 1.102.0-nightly, 2026-11-11) the
unstable flag `-Z mir-move-elimination` (default off) replaces the MIR pass `DestinationPropagation` with
two new passes that run in its slot at `mir-opt-level >= 2`:

1. **`TailCopyToMove`** walks backwards from every `Return` through straight-line code and rewrites a
   `copy x` operand into `move x` when nothing later on that path touches `x`. It stops at any indirect
   (`Deref`-first) place, at any write to a borrowed local, and at any statement or rvalue it does not model.
2. **`MoveElimination`** computes, per local, the set of program points at which the local must have its own
   allocation (a `SparseIntervalMatrix` with an *early* and a *late* point per statement), then maps a local
   onto another place (`_2 -> _0`, `_3 -> _2.1`, transitively) whenever the two sides of an assignment have
   disjoint rows. It rewrites the body once, deletes all storage markers and rebuilds them from the merged
   matrix, and finally repairs assignments whose source and destination now overlap.

What a later reader should retain:

- **The two passes exist to unify address-observed locals.** `DestinationPropagation` refuses every local
  whose address is taken. `MoveElimination` accepts them, but an address-observed local stays "allocated"
  until `StorageDead` or a whole-local `move`, so a `Copy`-typed `_0 = copy buf` keeps `buf` alive across the
  write of `_0`. `TailCopyToMove` turns that final copy into a move so the rows become disjoint.
- **Observed effect (borrowed-local return).** For
  `let mut buf = [0u8; 8192]; fill_buf(&mut buf, seed); buf` on x86-64 at `-C opt-level=2`: the default
  pipeline keeps `_0 = copy _2`, a frame whose CFA offset peaks at **8,224 bytes** (two 4,096-byte probed
  steps), and a `memcpy` of 8,192 bytes into the `sret` pointer. With `-Z mir-move-elimination=yes` the
  optimized MIR builds the array directly in `_0`; the function's CFA offset peaks at **16 bytes** (one
  `pushq %rbx`) and it contains **no `memcpy`**.
- **Evidence split, stated up front.** The default arm was executed for this report with rustc
  1.98.0-nightly (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), where neither the flag nor the two passes
  exist (`error: unknown unstable option: mir-move-elimination`). Its final MIR is byte-identical, and its
  assembly identical modulo the crate hash, to the default arm of a preserved execution capture taken with
  rustc 1.102.0-nightly. **The `-Z mir-move-elimination=yes` arm (the 16-byte / zero-`memcpy` result and the
  zerocopy per-pass numbers below) comes only from that preserved capture; it was not re-executed here.**
  A hand evaluation of the audited source on the probe's pre-pass MIR reproduces the captured enabled-arm
  MIR statement for statement.
- **zerocopy (preserved capture, 4,302 MIR bodies).** `TailCopyToMove` turned 110 copy assignments into
  moves; `MoveElimination` removed 3,779 assignment statements (2,403 copies, 624 moves) and 659 storage
  markers; the following `SimplifyLocals-final` removed 6,908 local declarations (29,733 to 22,825).
- **Semantics status.** The passes rely on the local-lifetime semantics of the *open, unmerged* RFC pull
  request `rust-lang/rfcs#3943` ("MIR move elimination"): a local is allocated by its first direct write
  and freed by a whole-local `move`. The option's own help text calls this "experimental MIR semantics".
- **Mechanization.** `support/MoveEliminationAndTailCopySoundness.lean` (Lean v4.34.1, core library only)
  proves, in four deliberately small models: exact outcome equivalence of the tail scan; a value and
  address-observation refinement for whole-local unification under disjoint live ranges; the algebra of
  the transitive `Local -> Place` substitution; and correctness of the aggregate aliasing fixup; plus three
  sharpness counterexamples. 27 audited theorems depend on at most `propext` and `Quot.sound`.

## Applicability

**Subjects and how they relate.**

| Subject | Revision | Role |
|---|---|---|
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (1.102.0-nightly, 2026-11-11) | Source audited line by line; toolchain of the preserved two-arm execution capture. |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (1.98.0-nightly, 2026-05-31) | Toolchain actually executed for this report. `tail_copy_to_move.rs` and `move_elimination.rs` do not exist at this revision (HTTP 404) and the flag is rejected. |
| `rust-lang/rust` | `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (default-branch head, 2026-11-20) | Continuity check only. |
| `Amanieu/rfcs` | `084380e84a27f8414e61daad2bd7d273f139b76b` | Head of open pull request `rust-lang/rfcs#3943`; file `text/0000-mir-move-elimination.md`. Descriptive, not normative. |
| `google/zerocopy` | `907b9175fee081872ec883ca4709e6ad922f8ed0` (crate 0.8.64) | Input of the default-arm census executed here. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Its trusted MIR semantics is compared with the models used here. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (v4.34.1) | Kernel that checked the mechanization. |

**Shared versus revision-specific behaviour.**

- `tail_copy_to_move.rs`, `move_elimination.rs`, `precise_liveness.rs` and `dest_prop.rs` are byte-identical
  between `3ef0c22c` and `c7d5ba59`. `rustc_mir_transform/src/lib.rs` differs between the two only in lines
  unrelated to the pass list (`const_eval_select` intrinsic test, placement of `PostAnalysisNormalize`).
  Source findings therefore hold for both; nothing else about `c7d5ba59` was examined.
- At `14210df0e` only `DestinationPropagation` exists. Everything said about the default arm applies to it.
- File history on the default branch: `tail_copy_to_move.rs` was added by commit
  `7ce6f3f689efaedd5713b3fc3a208a35fcd7d840` ("Add a MIR pass which turns copies into moves just before a
  return", committer date 2026-09-23); the oldest commit touching `move_elimination.rs` is
  `0a266baf9e4ed0f185955614550b7da940caed92` (committer date 2026-10-19).

**Configuration the findings assume.** `-Z mir-move-elimination=yes` and `mir-opt-level >= 2`; `rustc -Z help`
on the executed toolchain documents the MIR optimization level as "default: 1 in non optimized builds and 2
in optimized builds", and the probes pass `-C opt-level=2`. Host and target `x86_64-unknown-linux-gnu`. Assembly facts are specific to that target
and to the LLVM bundled with each toolchain (22.1.6 for 1.98.0-nightly, 23.1.5 for 1.102.0-nightly). Storage
markers are rebuilt only when `tcx.sess.emit_lifetime_markers()` holds.

**Exact observation versus extension.**

- Source findings are exact for the listed revisions.
- Execution findings for the enabled arm are exact for one capture (one program, one toolchain) whose
  command lines were not preserved; see Evidence. Extending them to other programs rests on the source
  audit, not on measurement.
- The mechanized theorems are exact for the models defined in the Lean file. Their relevance to rustc rests
  on the correspondence argued under Findings and is limited by the gaps listed under Boundaries.

## Findings

### 1. Gating and pipeline position

Basis: source (`rust-lang/rust` `3ef0c22c`).

- `compiler/rustc_session/src/options.rs` lines 2721-2722 declare `mir_move_elimination: bool`, default
  `false`, help text: "enable the experimental MIR semantics for the move elimination optimization
  (default: no)".
- `tail_copy_to_move.rs` lines 51-55 and `move_elimination.rs` lines 132-136 both use

  ```rust
  PassPolicy::optional(ctx.mir_opt_level() >= 2 && ctx.opts.unstable_opts.mir_move_elimination)
  ```

  while `dest_prop.rs` lines 157-161 (the condition is on line 159) uses
  `ctx.mir_opt_level() >= 2 && !ctx.opts.unstable_opts.mir_move_elimination`. The two families are therefore
  mutually exclusive under the option; a pass can still be forced individually with
  `-Z mir-enable-passes`, which this report did not exercise.
- `rustc_mir_transform/src/lib.rs` lines 772-778 fix the order inside the optimization pass list:
  `CopyProp`, `DeadStoreElimination::Final`, `DestinationPropagation`, `TailCopyToMove`,
  `MoveElimination`, `SimplifyLocals::Final`, `MultipleReturnTerminators`.

### 2. `TailCopyToMove`

Basis: source (`compiler/rustc_mir_transform/src/tail_copy_to_move.rs`, 258 lines).

- `run_pass` (lines 58-104) computes `borrowed_locals(body)` once, seeds one work item per block ending in
  `Return` with `used_after = {_0}`, and processes items from a stack. After a block is scanned completely,
  it continues only into predecessors whose terminator is a plain `Goto` to that block (lines 86-102); every
  other terminator ends the walk. Because a `Goto` block has exactly one successor, each scanned statement
  has a unique straight-line continuation to the `Return`.
- `scan_block` (lines 119-187) iterates the statements in reverse:
  - `StorageLive`, `StorageDead`, `Nop`: ignored (line 131).
  - `Assign(place, rhs)`: break if `place.is_indirect_first_projection()` (line 136); break if
    `borrowed.contains(place.local)` (line 143); otherwise add every local the place evaluation accesses
    (base and `Index` locals) to `used_after` and process the rvalue.
  - `SetDiscriminant`: same two breaks, then the place's locals are added (lines 157-176).
  - anything else: break (lines 177-182).
- `process_rvalue` (lines 198-221) accepts only `Use` and `Aggregate`; aggregate operands are visited right
  to left so that `used_after` already contains the operands evaluated later in the same statement. Any
  other rvalue breaks.
- `process_operand` (lines 224-258): an operand whose place is indirect breaks. A direct `Copy(place)` with
  `place.local` not in `used_after` becomes `Move(place)`; then the place's locals are added. Constants and
  `RuntimeChecks` are ignored.
- A break is `ControlFlow::Break` propagated with `?` out of loops that mutate in place, so rewrites made
  before the break (statements later in program order, and operands to the right inside an aggregate)
  persist.
- The stated reason for the borrowed-write stop (lines 140-142): "Writing to a borrowed local can start a
  new allocation range. Shortening an earlier borrowed local could remove an overlap with that new range."

Derived consequence for the headline shape: with `StorageDead(_4); _0 = copy _2; StorageDead(_2); return`
and `_0` not borrowed, the scan rewrites the assignment to `_0 = move _2` even though `_2` is borrowed;
the walk then ends because the predecessor block ends in a `Call`.

**Model and Theorem 1** (basis: derived, kernel-checked; namespace `Tail` of the Lean file).

- Store: each cell (a local, or a cell outside the frame reachable only through pointers) is `dead`,
  `live` (in scope, no allocation) or `alloc v`. A direct write to a `dead` local, any access through a
  pointer to a non-allocated cell, and any read of a non-allocated local are undefined. A whole-local
  `move` leaves the local `live`; a projected move behaves like a copy; `StorageLive` gives `live`,
  `StorageDead` gives `dead`. Operands are evaluated left to right, then the destination is written.
  These rules transcribe the state table of the RFC text (Finding 7).
- Projections, partial writes, `SetDiscriminant`, aggregate construction, unmodelled rvalues and unmodelled
  statements are uninterpreted functions bundled in `Interp`; the theorem quantifies over all of them.
- `scanOperand`, `scanOperands`, `scanRvalue`, `scanStmt`, `scanRev` and `tailCopyToMoveWith` transcribe
  `process_operand`, the aggregate loop, `process_rvalue`, one `scan_block` iteration, the block loop and
  the pass on one straight-line return tail (`backwardReturnTailScan`), including persistence of partial
  rewrites. A configuration record switches the two stops individually.
- `tailCopyToMove_exact_return_value_and_memory_equivalence`: for every configuration with the indirect
  stop enabled, every `Interp`, every borrowed set, every tail and every initial store, the original and
  rewritten tails are either both undefined or both defined with identical `_0` and identical contents of
  every cell outside the frame (all other locals are dead after the return in both).
  `tailCopyToMove_ub_iff` and `tailCopyToMove_preserves_return_and_heap` restate the two halves.
- `ce1_tail_copy_to_move_past_indirect_borrow_read_unsound`: for `_2 = copy _1; _0 = copy (*_3)` with
  `_3 = &_1`, the scan *without* the indirect stop rewrites the first statement to `_2 = move _1`; the
  original tail returns `7`, the rewritten tail is undefined; the upstream configuration leaves the tail
  unchanged.
- `tailCopyToMove_equivalence_without_borrowed_write_stop`: the same equivalence holds with the
  borrowed-write stop disabled. In this model that stop is therefore not what makes the rewrite sound; see
  Boundaries.

### 3. Precise liveness matrix

Basis: source (`compiler/rustc_mir_dataflow/src/impls/precise_liveness.rs`, 596 lines). No file named
`liveness_matrix.rs` exists at the audited revisions; `liveness_matrix` is a function in this file.

- Output: `SparseIntervalMatrix<Local, SplitPointIndex>`, one row per local; "Two locals may share the same
  address only if their rows are disjoint" (lines 3-4).
- `SplitPointIndex` (lines 349-379) is `(point << 1) | effect` with `Early = 0`, `Late = 1`: operands are
  read at the early point, destinations written at the late point.
- A range **starts** at the late point of any statement or terminator that writes the local without a
  `Deref` projection (`DefUse::Def | DefUse::PartialWrite`, lines 50-62), and at block entry for locals
  live on entry; arguments start live (lines 266-271).
- A range **ends** at the early point of `StorageLive`/`StorageDead` of the local or of a bare-local `move`
  operand (lines 66-93), and, only for locals that are never borrowed, at their last use on the path (kill
  points, lines 114-232). Borrowed locals are "conservatively treat[ed] as always live in the backwards
  pass" (lines 103-107).
- `Call` terminators: `move` arguments that are not indirect are regenerated at the late point so they
  conflict with each other and with the destination (lines 534-558); the comment adds "this *doesn't* apply
  to TailCall".
- Blocks ending in `Return`: every range except `_0`'s is closed before the terminator so that rebuilt
  `StorageDead` statements land before the `return` (lines 454-469 and 500-512).
- Every range is closed at the end of its block and reopened from the successor's entry state (lines
  560-563).

### 4. `MoveElimination`: unification

Basis: source (`compiler/rustc_mir_transform/src/move_elimination.rs`, 1,264 lines).

`run_pass` (lines 139-172) runs, in order: `liveness_matrix`; `UnprojectableLocals::find`;
`find_rust_call_tuples`; `PlaceUnification::run`; `apply_mappings`; `reconstruct_storage` (only if lifetime
markers are emitted); `apply_alias_fixup`.

Candidates (`visit_assign`, lines 467-548): `dest = copy/move src` proposes unifying `src` with `dest`;
`dest = Aggregate(..)` for arrays, tuples, unions and ADTs whose fields may be projected proposes unifying
each bare-local operand with the corresponding field place of `dest` (`ConstantIndex` for arrays,
`Field` for tuples/structs/unions, `Downcast` then `Field` for enum variants). Both sides must pass
`check_projections`: every projection element satisfies `is_stable_offset()` and `can_use_in_debuginfo()`
(lines 463-465).

`can_unify_places(a, b)` (lines 326-395) first resolves both places through the current mapping and then
rejects when any of the following holds:

1. same base local (identical or different projections);
2. either base local is a tuple passed to a `"rust-call"` ABI call;
3. both places carry projections;
4. the bare local is *unprojectable* and the other place has projections. Unprojectable locals are `_0`,
   the arguments, any local used as a `Deref` base, and any local used as a bare `Local` outside a place
   such as an `Index` operand (lines 181-231);
5. both are bare locals and both are an argument or the return place; otherwise a temporary is always the
   side that is replaced;
6. the target place has a packed field projection (`most_packed_projection`);
7. `!liveness_matrix.disjoint_rows(local, place.local)`;
8. the local's type differs from the place's type (comment `FIXME(#112651)`: subtyping).

`remap_local` (lines 398-411) records `local -> place`, unions the local's row into the row of
`place.local`, clears the local's row, and propagates unprojectability. For aggregates all field candidates
are checked first and remapped afterwards (lines 437-455), "sound because they will each be mapped to a
disjoint field of the destination place"; a repeated operand keeps only its first mapping.

Mappings are transitive: `resolve_place` (lines 318-323) loops
`place = new_place.project_deeper(place.projection)` while the base is mapped, and `run` finalizes every
entry through it (lines 304-312). `PlaceUpdater` (lines 562-606) then rewrites every place in one pass and
turns every `StorageLive`/`StorageDead` into a `Nop`.

**`unifyPlaces` algebra** (basis: derived, kernel-checked; namespace `Places`).
`resolve_projectDeeper`: resolution commutes with projecting deeper.
`resolve_reaches_unmapped` and `unifyPlaces_idempotent`: given an acyclicity witness (a rank that every
mapping step strictly decreases) and fuel at least the maximal rank, resolution ends at an unmapped base
and the finalized substitution is idempotent, which is what justifies a single rewrite pass.
`unifyPlaces_transitive_example` evaluates the documentation example (`_3 -> _2.1`, `_2 -> _1.0`, hence
`_3 -> _1.0.1`). The model's field paths stand for stable-offset projections only.

### 5. Storage reconstruction

Basis: source (`move_elimination.rs` lines 608-945).

For every temporary with a non-empty row, each interval is split at block boundaries
(`split_range_by_block`). An interval starting inside a block gets `StorageLive` before the statement; one
that is live-in gets `StorageLive` in each predecessor where the local is not live at the terminator,
splitting the edge when that predecessor has several successors, and only if the backward analysis
`InitializedBeforeUse` says some continuation initializes the local before reading it. An interval ending
inside a block gets `StorageDead` after the statement; one that reaches the terminator gets `StorageDead`
at the start of each successor where the local is dead on entry. All `StorageLive` insertions are queued
after the `StorageDead` insertions so that at a shared location `StorageDead` comes first (lines 937-942).
This runs for all locals, merged or not, so storage ranges can also shrink for untouched locals. Arguments
and `_0` get no markers. This component is not mechanized here.

### 6. Aliasing fixup

Basis: source (`move_elimination.rs` lines 947-1264) and the RFC text for the motivation.

MIR assignments of non-scalar-backend types require non-overlapping source and destination (codegen may
lower them to `memcpy`). After unification that can be violated, so `apply_alias_fixup` visits every
assignment:

| Assignment after unification | Rewrite | Lines |
|---|---|---|
| `Use(copy/move src)` with `src == dest` | statement becomes `Nop` | 1136-1141 |
| `Use(copy/move src)`, `src` and `dest` alias but differ | `StorageLive(tmp); tmp = <rvalue>; dest = move tmp; StorageDead(tmp)` | 1142-1148, 1012-1028 |
| `Aggregate` (array, tuple, union, ADT with projectable fields) with at least one operand that directly aliases `dest` | split per field: identity fields skipped; aliasing or indirect operands hoisted to temporaries; then every remaining field written with `Use(op, WithRetag::No)`; the original statement becomes `Nop`; for an enum, `SetDiscriminant` is added after the field writes | 1030-1124, 1151-1224 |
| other `Aggregate`, `Repeat`, `Cast`, `CopyForDeref`, `WrapUnsafeBinder` with any accessed place aliasing `dest` | whole rvalue hoisted to a temporary, then `dest = move tmp` | 1229-1249 |
| `Use(const)`, `Ref`, `ThreadLocalRef`, `BinaryOp`, `UnaryOp`, `Discriminant`, `RawPtr`, `Reborrow` | untouched ("only operate on scalar backend types") | 1253-1260 |

`places_directly_alias(a, b)` (lines 963-1003) is false for different base locals or when either place is
indirect; walking the two projection lists in parallel, the first mismatch decides: two `Field` elements
alias only if the parent type is a union; two `ConstantIndex` elements with the same `from_end` and different
offsets do not alias; any other mismatch is treated as aliasing; identical paths or a prefix relation alias.
The aggregate fast path looks only at direct aliases; the comment (lines 1041-1063) argues that an indirect
source can overlap the destination only if a direct source also does, which is why indirect operands are
hoisted exactly when a direct alias exists.

The pretty-printed marker `no_retag` on an assignment is the `WithRetag::No` argument of `Rvalue::Use`
emitted by this fixup.

**Model and Theorem 3** (basis: derived, kernel-checked; namespace `Fixup`).

- Store `local -> field -> scalar`; an operand is a constant or one field of one local; a simple assignment
  writes one field and reads its source when it executes.
- `specAggregate`: read every operand, then write the fields (the meaning of `d = Aggregate(ops)`).
  `naiveLower`: field-by-field writes with no fixup (field `i` is written before operand `i + 1` is read).
  `aliasFixup`: unchanged when no operand reads `d`; otherwise hoists followed by per-field writes, with
  identity fields skipped, for any number of fields.
- `aliasFixup_emits_nonoverlapping_copies` (any arity): if the temporaries differ from `d`, no emitted
  assignment reads the local it writes.
- `aliasFixup_pair_matches_specification` (two fields, every combination of operand shapes: constant, field
  of another local, identity field, other field of `d`): with fresh temporaries the fixup output, executed
  sequentially, equals `specAggregate` on every local other than the temporaries.
- `aliasFixup_self_swap_correct`: `d = Aggregate(d.1, d.0)` becomes two hoists and two writes and yields the
  swapped pair.
- `ce3_aggregate_self_swap_without_aliasing_fixup_clobbers_field`: without the fixup, field 1 receives the
  already overwritten field 0, so the result is `(b, b)` instead of `(b, a)` whenever `a != b`.
- `aliasFixup_three_field_rotation_instance` evaluates a three-field rotation on a concrete store:
  fixup `(20, 30, 10)` equals the specification, unfixed lowering gives `(20, 30, 20)`.
- `aliasFixup_identity_field_dropped_instance`: `_2 = Aggregate(_2.0, _1.0)` becomes the single write
  `_2.1 = _1.0`, the shape seen in the captured MIR of Finding 9.

### 7. The semantics the passes assume

Basis: documentation (RFC text at `Amanieu/rfcs` `084380e8`, an open pull request; it proposes, it does not
define, Rust semantics) cross-read with source comments at `3ef0c22c` that cite "RFC 3943".

- Locals are **dead**, **live** or **allocated**. Arguments start allocated; the return place starts live;
  other locals start dead if they have storage markers and live otherwise.
- `StorageLive` gives live (a previous allocation is lost); `StorageDead` gives dead.
- Evaluating the base local of a destination place without `Deref` is undefined if dead and otherwise
  makes it allocated. Every other evaluation of a base local is undefined unless it is allocated.
- A `move` operand of a bare local is undefined unless allocated and leaves the local live, freeing the
  allocation. A `move` with projections "behaves identically to `copy`" outside calls.
- Operands are evaluated left to right and destination places last, so in `_1 = move _2` "the source place
  is deallocated before the destination place is allocated. Since the two places are never allocated at
  the same time, they are allowed to share the same address."
- A local that is freed and later re-initialized "will receive a new allocation which may have a different
  address than it previously had".
- The RFC warns pass authors: "MIR optimizations also need to be careful not to shorten the live range of
  a local whose address has been taken by moving or eliminating assignments or moves."
- It lists as a future possibility that `Copy` types inhibit the optimization because "a copy doesn't
  invalidate any borrows". `TailCopyToMove` is the in-tree answer for the return path only.

### 8. Whole-local unification is a refinement when live ranges are disjoint

Basis: derived, kernel-checked (namespace `Unify`).

- Store: each local is unallocated or has a slot `(address, value)`. A write to an unallocated local takes
  the address from an explicit allocator choice attached to the statement; a write to an allocated local
  keeps its address. `d = move x` reads `x`, frees `x`, then allocates and writes `d`. Values are integers
  or pointers `(pointee local, address)`; `ptrEq` compares addresses only; a load or store through a pointer
  requires the pointee to be allocated at that address. Statements: constant, copy, move, address-of,
  pointer equality, load, store, `StorageDead`, no-op. This model has two states per local (it does not
  make writes to a dead local undefined), which only enlarges the set of original executions covered.
- `unifyStmt σ` renames every local through the map `σ`, replaces copies and moves that became
  self-assignments by no-ops, and erases storage markers (the real pass rebuilds them afterwards).
- `ClassDisjoint σ s`: no two different locals with the same image under `σ` are allocated in `s`.
- `moveElimination_value_and_address_bisimulation` (Theorem 2a): take any execution of the unified program
  with any allocator choices. Let the original program run with the choices `origAnnot` reads off that
  execution (the original allocates each destination where the unified program has, or is about to put,
  its representative). If the original run is defined and every state it passes through is
  `ClassDisjoint`, then the unified run is defined and the final stores are related: every allocated
  original local sits at the same address as its representative and holds the same value up to renaming
  of pointer targets.
- `moveElimination_original_choices_valid` (2b): if the unified execution keeps simultaneously live
  allocations at distinct addresses, so does that original execution. Together: each behaviour of the
  unified program is a behaviour of the original program under a legal allocator.
- `moveElimination_return_observation` (2c): with `σ 0 = 0`, the returned slot has the same address and the
  same observable value (integers as themselves, pointers as addresses).
- `AllocationInterval`, `Row.disjoint`, `earlyPoint i = 2i`, `latePoint i = 2i + 1`:
  `early_end_late_start_disjoint` shows a range ending at a statement's early point never overlaps one
  starting at its late point; `Row.disjoint_sound` shows disjoint rows share no point;
  `disjointLiveRanges_sound` (2d) shows that row disjointness (`DisjointLiveRanges`) of a matrix that covers
  the execution implies the `ClassDisjoint` hypothesis. That the real dataflow produces a covering matrix
  is assumed, not proved.
- `nrvo_model_instance`: for `_2 = 0; _4 = &mut _2; *_4 = copy _1; StorageDead(_4); _0 = move _2` with
  `σ = {_2 -> _0}`, the unified program builds the value in `_0`, the pointer handed out is the address of
  `_0`, and the original program driven by `origAnnot` returns the same value at the same address.
- `ce2_unifying_overlapping_address_observed_locals_breaks_ptr_inequality`: for
  `_1 = 5; _2 = 5; _3 = &_1; _4 = &_2; _0 = (_3 == _4)`, every legal allocator makes the original return
  `0`; after unifying `_2` into `_1` every allocator returns `1`; the `ClassDisjoint` hypothesis fails and
  the row check on the two overlapping rows is `false`.

### 9. Borrowed-local array return and pair swap, default pipeline versus move elimination

Probe program (`nrvo_and_swap.rs`, embedded in `support/probe_move_elimination_and_nrvo.py`):

```rust
#[inline(never)]
fn fill_buf(buf: &mut [u8; 8192], seed: u8) { buf[0] = seed; buf[8191] = seed.wrapping_add(1); }

#[inline(never)]
fn make_borrowed_array_nrvo(seed: u8) -> [u8; 8192] {
    let mut buf = [0u8; 8192];
    fill_buf(&mut buf, seed);
    buf
}

#[inline(never)]
fn swap_big_pair_fields(mut p: BigPair) -> BigPair {   // BigPair { a: [u64; 4], b: [u64; 4] }, Copy
    let q = BigPair { a: p.b, b: p.a };
    p = q;
    p
}
```

`make_borrowed_array_nrvo`, optimized MIR and assembly:

| | default (`DestinationPropagation`) | `-Z mir-move-elimination=yes` |
|---|---|---|
| Evidence | executed here (1.98.0-nightly) and preserved capture (1.102.0-nightly), identical | preserved capture (1.102.0-nightly) only |
| locals | `_0`, `_2` (`buf`), `_3: ()`, `_4: &mut [u8; 8192]` | `_0` (`buf`), `_2: ()`, `_3: &mut [u8; 8192]` |
| body | `_2 = [const 0_u8; 8192]; _4 = &mut _2; _3 = fill_buf(move _4, move _1)`; then `_0 = copy _2` | `_0 = [const 0_u8; 8192]; _3 = &mut _0; _2 = fill_buf(move _3, move _1)`; no assignment to `_0` afterwards |
| CFA offset high-water mark | 8,224 bytes (`pushq %r14`, `pushq %rbx`, two `subq $4096, %rsp` each followed by a probe store, `pushq %rax`) | 16 bytes (`pushq %rbx`) |
| `.stack_sizes` entry | 8,216 bytes (measured here) | not recorded |
| `memcpy` calls | 1 (`movl $8192, %edx`, destination the saved `sret` pointer) | 0 |
| `memset` calls | 1, of 8,191 bytes starting at byte 1 of the stack buffer | 1, of 8,191 bytes starting at `1(%rdi)`, i.e. inside the caller's `sret` buffer |
| pointer passed to `fill_buf` | address of the stack buffer | the `sret` pointer itself |
| instruction lines | 24 | 11 |

Basis: execution. The default column is this report's run and agrees with the capture exactly (final MIR
byte-identical; assembly identical after replacing the crate hash and the local label number). The
right-hand column is the capture. The CFA figure includes the 8-byte return address and the register
pushes; the buffer itself is 8,192 bytes.

Basis: derived. The right-hand MIR is what the audited algorithm yields: the tail scan rewrites
`_0 = copy _2` to `_0 = move _2` (Finding 2); `_2`'s row then ends at the early point of that statement and
`_0`'s starts at its late point, so candidate `(_2, _0)` passes check 7 of Finding 4 with the temporary
`_2` replaced by `_0`; `_0 = move _0` is deleted by the fixup.

`swap_big_pair_fields`. Pre-pass MIR (dumped here before `DestinationPropagation`):

```text
_3 = copy (_1.1: [u64; 4]);
_4 = copy (_1.0: [u64; 4]);
_2 = BigPair { a: move _3, b: move _4 };
_1 = copy _2;
_0 = copy _1;
```

| | default | `-Z mir-move-elimination=yes` (capture) |
|---|---|---|
| final body | `_2 = copy (_1.1); _3 = copy (_1.0); _1 = BigPair { a: move _2, b: move _3 }; _0 = copy _1` | `(_2.0) = copy (_1.1); (_2.1) = no_retag move (_1.0); _1 = move _2; _0 = move _1` |

Basis: derived (hand evaluation of the source on the pre-pass MIR; it reproduces the captured body exactly).
The tail scan rewrites `_0 = copy _1` and `_1 = copy _2` to moves and leaves the two field copies alone
because `_1` is used later. Unification rejects `_3 -> _1.1` (rows overlap), accepts `_4 -> _1.0` (the read
of `_1.0` is `_1`'s last use before `_1` is overwritten, so `_1`'s first range ends at that statement's
early point), accepts `_3 -> _2.0` from the aggregate, rejects the aggregate's second field (both sides
projected), rejects `_2 -> _1` (rows overlap after the unions) and rejects `_1`/`_0` (argument and return
place). The fixup deletes `(_1.0) = copy (_1.0)`, and splits
`_2 = BigPair { a: move (_2.0), b: move (_1.0) }`: field 0 is an identity and is skipped, field 1 does not
alias `_2` and is kept as a plain field write with `WithRetag::No`. **No temporary is introduced for this
program**; the hoisting branch of the fixup is not exercised by the capture.

Miri. Basis: execution. Here (1.98.0-nightly) the probe program exits 0 under Miri's default flags, under
`-Zmir-opt-level=2`, and under `-Zmir-preserve-ub=yes -Zmir-opt-level=2`; the last two print Miri's warning
that MIR optimizations "may hide UB". The capture records exit code 0 under Miri for both arms but not the
Miri flags used.

Controls (`address_and_alias_controls.rs`). Basis: execution here, default pipeline only; native output
`CONTROLS_OK distinct=true`, Miri exit 0 in all three modes.

| Control | Default-pipeline result | What the enabled arm must show (not executed) |
|---|---|---|
| `make_unborrowed_array_nrvo` (no borrow) | `DestinationPropagation` already builds the array in `_0`; CFA peak 32 bytes, 0 `memcpy`, `.stack_sizes` 24 | same shape |
| `two_borrowed_locals_overlap` (`b = a`, both borrowed, both used afterwards) | body unchanged by `DestinationPropagation`; the two addresses differ at run time | `a` and `b` must stay separate locals (rows overlap) |
| `return_after_indirect_read` (`_7 = copy _2; _8 = copy (*_3)[0 of 1]; _0 = (copy _7, copy _8)`) | body unchanged | `_7 = copy _2` must remain a copy: the scan breaks at the indirect read |
| `swap_big_pair_in_place` (`p = BigPair { a: p.b, b: p.a }`) | `_1 = BigPair { a: move _2, b: move _3 }; _0 = copy _1` | prediction below |

Hypothesis, not a finding (derived from the source, never executed): for `swap_big_pair_in_place` the
second temporary unifies with `_1.0`, the aggregate becomes `_1 = BigPair { a: move _2, b: move (_1.0) }`,
and the fixup must hoist `(_1.0)` into a fresh temporary before writing `(_1.0) = move _2`. This is the
program on which the hoisting branch should be observable.

### 10. zerocopy per-pass census

Basis: execution. The two tables come from different toolchains, possibly different zerocopy revisions,
and different counting code; compare deltas within a table, never absolute values across tables.

Preserved capture, rustc 1.102.0-nightly with move elimination enabled (zerocopy revision, `--cfg` flags and
counter definitions not recorded):

| Pass | bodies | locals | assignments | copy assignments | move assignments | storage markers |
|---|---|---|---|---|---|---|
| before `TailCopyToMove` | 4,302 | 29,733 | 20,618 | 7,070 | 1,315 | 31,171 |
| after `TailCopyToMove` | 4,302 | 29,733 | 20,618 | 6,960 (-110) | 1,425 (+110) | 31,171 |
| after `MoveElimination` | 4,302 | 29,733 | 16,839 (-3,779) | 4,557 (-2,403) | 801 (-624) | 30,512 (-659) |
| after `SimplifyLocals-final` | 4,302 | 22,825 (-6,908) | 16,839 | 4,557 | 801 | 30,512 |

The assignment delta (-3,779) exceeds the copy and move deltas together (-3,027) by 752; the capture does
not say which assignment kinds make up the remainder.

Executed here, rustc 1.98.0-nightly default pipeline, zerocopy 0.8.64 at `907b9175` (clean tree),
`-Copt-level=2 -Zmir-opt-level=2 --cfg no_zerocopy_allocator_api_1_100_0`, counters as defined in the probe
script's `count_mir`:

| Pass | bodies | locals | assignments | copy assignments | move assignments | storage markers |
|---|---|---|---|---|---|---|
| before `DestinationPropagation` | 4,476 | 21,677 | 16,653 | 2,991 | 972 | 29,642 |
| after `DestinationPropagation` | 4,476 | 21,677 | 16,035 (-618) | 2,447 (-544) | 898 (-74) | 27,245 (-2,397) |
| after `SimplifyLocals-final` | 4,476 | 20,053 (-1,624) | 16,035 | 2,447 | 898 | 27,019 (-226) |

`DestinationPropagation` changed 483 of 4,476 bodies.

### 11. Relation to Anneal's trusted MIR semantics

Basis: source (`joshlf/anneal` `c131b320`) and derived.

- `trusted/lean/Trusted/MirSemantics.lean` defines `LocalSlot` as `dead | live (val : Option Val)` (lines
  621-623) and, in `evalOperandToSlot` (lines 949-975), evaluates `.move place` by reading the slot and
  resetting it to the live-uninitialized slot, whereas `.copy place` leaves it unchanged. The file states
  this as its one intentional difference from the upstream interpreter: "`Operand.move` deliberately and
  conservatively deinitializes non-ZST local storage upon evaluation" (lines 67-69). Both operand forms
  return `.unsupported` when the place has projections.
- `trusted/lean/Trusted/MirAst.lean` (lines 583-597) maps `Rvalue::Use(op, withRetag)` to `.use op` when the
  retag is an operational no-op, which includes `WithRetag::No`.
- Derived: Anneal's slot states line up with the `Tail` model (`dead`, `live none` as "live", `live (some v)`
  as "allocated") for unprojected locals, so a `copy` to `move` rewrite that is *not* a final direct use
  faults in Anneal's semantics at the later read. Anneal's slots carry no addresses, so nothing in it
  observes which locals were unified; the address side of Finding 8 has no counterpart there.
- Derived: `MoveElimination` output with projected operands or destinations, such as
  `(_2.1: [u64; 4]) = no_retag move (_1.0: [u64; 4])`, falls into the `.unsupported` branch quoted above.
- Anneal pins its interpreter correspondence to `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd` (2026-10-20). At that revision `tail_copy_to_move.rs` exists and
  `move_elimination.rs` does not (HTTP 200 and 404 on the raw paths).

## Boundaries

**Not examined**

- Executing `-Z mir-move-elimination=yes` for this report. No toolchain that accepts the flag was available
  when the package was assembled; the enabled-arm rows of Findings 9 and 10 are a preserved capture.
- Any target other than `x86_64-unknown-linux-gnu`; any codegen backend other than LLVM; debuginfo
  quality after unification (`can_use_in_debuginfo` is cited, not tested); compile-time or run-time
  performance; unwinding paths; coroutines (`Yield` is special-cased in the liveness code); `TailCall`;
  inline assembly; the `"rust-call"` exclusion; packed projections; the subtyping check.
- `reconstruct_storage` and `InitializedBeforeUse` are described from source and are not mechanized.
- The `Use`-with-partial-overlap, `Repeat`/`Cast`, enum `SetDiscriminant` and indirect-operand branches of
  the fixup are described from source; the Lean model covers aggregates whose operands are scalar fields.
- Cross-function address observation. The models are intra-procedural. Whether a caller that knows the
  address of its call destination can compare it with a pointer the callee leaked to one of its own
  borrowed locals, and what the proposed semantics says about that comparison once the callee's local is
  unified with `_0`, was not investigated.
- Interaction with `-Z mir-enable-passes` (forcing both pass families at once).
- The Miri implementation of the proposed semantics and the MiniRust branch the RFC links to.

**Unknown**

- Whether the borrowed-write stop of `TailCopyToMove` is necessary. Theorem 1 holds without it in a model
  with allocation identity but no addresses. The upstream comment justifies it by address overlap; no
  intra-procedural witness was constructed here, and none is obvious, because nothing in a pure return tail
  can take the address of the newly started range.
- The zerocopy revision, flags and counter definitions behind the captured census, and the Rust source
  text of the captured probe. The probe source in this package is a reconstruction; that it is the same
  program is supported by the byte-identical default-arm MIR and assembly, not by the capture itself.
- Whether `swap_big_pair_in_place` behaves as hypothesized in Finding 9.
- Whether the RFC will be accepted in its current form. It is an open pull request.

**Known not to apply**

- rustc 1.98.0-nightly (`14210df0e`): the flag is rejected and neither pass exists.
- Locals whose rows overlap are not unified, including two address-observed locals connected by a copy
  that are both used afterwards (source: check 7; counterexample `ce2` shows why the check matters).
- The 8,224-byte and 16-byte figures are CFA high-water marks, not sizes of the local frame, and they are
  not a general statement about stack savings: they describe one function on one target.
- `aliasFixup_pair_matches_specification` is proved for two fields. For other arities only the
  non-overlap property is proved in general and one three-field instance is evaluated.

**Unsupported**

- `can_unify_places` never unifies two projected places, two special locals (arguments or `_0`), a
  `"rust-call"` tuple, or a place under a packed field.
- `TailCopyToMove` does not look through any terminator other than `Goto`, and models no rvalue other than
  `Use` and `Aggregate`.

**Stronger conclusions this report does not establish**

- That rustc's implementation is correct. The theorems are about small models; the liveness dataflow's
  covering property is a hypothesis of Theorem 2d; no proof connects the Rust code to the Lean definitions.
- That the optimization is observationally invisible to all Rust programs. By design it makes previously
  impossible address coincidences possible and makes access after a whole-local move undefined; the RFC
  text describes this as a technically breaking change.
- That the captured zerocopy deltas would be reproduced by the census code in this package.

## Evidence

**Primary source** (fetched 2026-11-21 from `raw.githubusercontent.com`; commit identifiers resolved the same
day through the GitHub REST API `repos/<owner>/<repo>/commits/<ref>`):

| Repository and revision | Path | What was read | SHA-256 of the file |
|---|---|---|---|
| `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/tail_copy_to_move.rs` | whole file (258 lines) | `da30e9fe99a008912bb49cc095c7f73b661899c2a35208d00970c9579196c331` |
| same | `compiler/rustc_mir_transform/src/move_elimination.rs` | whole file (1,264 lines) | `b8b47bbf3f468cec0b3f3705a7ac53f3740299f9899bd78e6cd03b2de3d38a7f` |
| same | `compiler/rustc_mir_dataflow/src/impls/precise_liveness.rs` | whole file (596 lines) | `c78e0da584eced0ae7729e0027d5948439fa1272749dee5af5189537df53b0f0` |
| same | `compiler/rustc_mir_transform/src/dest_prop.rs` | module documentation, lines 140-175, borrowed-local filter near line 406 | `ceae89039ab9649cec48eff10d9b28b0d98eeeda59916396335c8fb7a15b6672` |
| same | `compiler/rustc_mir_dataflow/src/impls/borrowed_locals.rs` | `gen_statement`, `gen_terminator` | `e59c3fece138783aa72906c7f17f77960d43cd31d021e1fd30b10398050ff714` |
| same | `compiler/rustc_mir_transform/src/lib.rs` | lines 149, 168, 210, 735-780 | not recorded |
| same | `compiler/rustc_session/src/options.rs` | lines 2719-2727 | not recorded |
| same | `compiler/rustc_mir_dataflow/src/impls/liveness_matrix.rs` | does not exist (HTTP 404) | n/a |
| `rust-lang/rust` `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` | the first four files above and `lib.rs` | byte comparison with `3ef0c22c`: four identical, `lib.rs` differs outside the pass list | n/a |
| `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `tail_copy_to_move.rs`, `move_elimination.rs` | both HTTP 404 | n/a |
| `Amanieu/rfcs` `084380e84a27f8414e61daad2bd7d273f139b76b` (commit date 2026-09-24) | `text/0000-mir-move-elimination.md` | whole file (589 lines); pull request `rust-lang/rfcs#3943`, state open, created 2026-04-03, last updated 2026-11-02 | not recorded |
| `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean`, `trusted/lean/Trusted/MirAst.lean` | lines cited in Finding 11 | not recorded |

In the `borrowed_locals` analysis a local counts as borrowed when it is the base of a non-indirect place in
`Rvalue::RawPtr`, `Rvalue::Ref` with a shared or mutable borrow kind, or `Rvalue::Reborrow`, or the base of
the non-indirect place of a `Drop` terminator (the source comment explains that drop glue receives
`&mut self`).

**Execution performed for this report** (2026-11-21):

- Toolchain: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, LLVM 22.1.6,
  with the `miri` and `llvm-tools` components.
- Command: `python3 support/probe_move_elimination_and_nrvo.py --zerocopy-lib-rs <zerocopy>/src/lib.rs --out support/probe_results.json`
  (about one minute). The script compiles with
  `rustc --edition=2021 -Copt-level=2 -Csymbol-mangling-version=v0 --emit=asm,link -Zdump-mir=DestinationPropagation|TailCopyToMove|MoveElimination|SimplifyLocals-final`,
  builds a second object with `-Zemit-stack-sizes` and reads it with `llvm-readobj --stack-sizes`, runs the
  binary, and runs Miri in three modes.
- Result file: `support/probe_results.json` (all paths scrubbed). It records `arms_run: ["default"]`, the
  rejection message for the flag, final MIR per function, assembly and metrics, Miri results, the
  comparison with the capture, and the zerocopy census.

**Preserved execution capture** (`support/captured_rustc_1_102_move_elimination.json`):

- Toolchain recorded in the capture: `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, commit
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, host `x86_64-unknown-linux-gnu`, LLVM 23.1.5. File last
  modified 2026-11-21.
- Contents: for each arm of the probe program the native output, Miri exit code, final MIR of both
  functions and the assembly of `make_borrowed_array_nrvo`; and the zerocopy census of Finding 10.
- Not recorded: command lines, probe source text, zerocopy revision and flags, counter definitions, Miri
  flags. The capture carries two boolean fields named `nrvo_asm_has_8k_stack_sub`, both `false`; they are
  not used here because the 8,192-byte reservation appears as two 4,096-byte steps, which this package's
  parser counts explicitly.
- Cross-checks performed here: default-arm MIR and assembly reproduced on 1.98.0-nightly
  (`part_c_comparison_with_preserved_capture` in the result file); enabled-arm MIR reproduced by hand
  evaluation of the audited source (Finding 9); assembly metrics of both captured arms recomputed by the
  probe script's parser.

**Mechanization** (`support/MoveEliminationAndTailCopySoundness.lean`, 1,826 lines, core library only):

- Checked with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` under
  Lean `version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release`:
  exit code 0, no diagnostics.
- `support/check_lean.py` wrote `support/lean_check_receipt.json`: 27 theorems audited with
  `#print axioms`; 4 depend on no axioms, 8 on `propext`, 15 on `propext` and `Quot.sound`; none on
  `Classical.choice`, `sorryAx` or `Lean.ofReduceBool`. Zero occurrences in the whole file, comments
  included, of the tokens the script counts (placeholder proofs, external decision procedures, compiled
  evaluation, `partial def`, axiom declarations, `implemented_by`, `extern`). Zero unsafe or `_unsafe_rec`
  declarations in the elaborated environment (recursive definitions are marked `noncomputable`).
- One lint option is disabled for one theorem (`linter.unusedSimpArgs` on
  `aliasFixup_pair_matches_specification`, whose 64-way case analysis reuses a single simplification lemma
  list, not all of which is needed in every case).

**Package files**

| File | Bytes | SHA-256 |
|---|---|---|
| `support/MoveEliminationAndTailCopySoundness.lean` | 80,075 | `1c8fb3947c41cd329972131eb39fb879aeddb492aeee7cceb52bbe68e8308c73` |
| `support/captured_rustc_1_102_move_elimination.json` | 7,172 | `0e62423af41cdcb9e1073841e9863bf4c9ce24815923af92e310f964a283516d` |
| `support/check_lean.py` | 9,486 | `12ba8c1693af60baa82ce09e2613cbd8f3767f3639c11814b24764197b1158ce` |
| `support/lean_check_receipt.json` | 4,172 | `8439663190b6e172e6ba7fd8094c072ba09c4a968eeaf7ba2aa440570331476a` |
| `support/probe_move_elimination_and_nrvo.py` | 26,018 | `3be7e90252f527dac6c5a607cfde1aed99250c59c5fc3bd3712aeab2145856ae` |
| `support/probe_results.json` | 25,204 | `e18b66b1369019f59d82c1a8a9d0d503b2d02442a51bb33373995112aa4227c9` |

## Revalidation

Cheapest checks first.

1. **Do the passes still exist and is the gating unchanged?** At the revision of interest, read
   `fn policy` in `tail_copy_to_move.rs`, `move_elimination.rs` and `dest_prop.rs`, and the pass list in
   `rustc_mir_transform/src/lib.rs`. Then compare the SHA-256 of the four audited files with the table
   above; identical hashes carry Findings 1-6 over unchanged.
2. **Does the installed toolchain accept the flag?**
   `echo 'pub fn f(){}' > /tmp/f.rs && rustc --crate-type=lib --emit=metadata -Zmir-move-elimination=yes -o /tmp/f.rmeta /tmp/f.rs`.
   An "unknown unstable option" error means only the default arm can be observed.
3. **Re-run the probe.** `python3 support/probe_move_elimination_and_nrvo.py --out /tmp/probe.json`
   (add `--skip-zerocopy` for a run of a few seconds). With a toolchain that accepts the flag the script
   runs both arms and fills in everything this report could not execute. Check, in order:
   `part_c_comparison_with_preserved_capture.mir_move_elimination` (all three booleans true means the
   capture is reproduced); `asm.make_borrowed_array_nrvo.metrics` of the enabled arm (expect a CFA peak of
   16 and no `memcpy`); in the controls, that `two_borrowed_locals_overlap` still has two array locals and
   prints `distinct=true`, that `return_after_indirect_read` keeps `copy _2` ahead of the indirect read, and
   what `swap_big_pair_in_place` looks like (the hypothesis of Finding 9); Miri exit codes in all modes; the
   `TailCopyToMove` and `MoveElimination` rows of the zerocopy census.
4. **Has the proposed semantics moved?** Compare the head commit of `rust-lang/rfcs#3943` with
   `084380e84a27f8414e61daad2bd7d273f139b76b` and re-read its state table and the sections on addresses and
   re-initialization and on evaluation order; those are the rules the `Tail` and `Unify` models encode.
5. **Re-check the proofs.** `python3 support/check_lean.py --out /tmp/receipt.json` with Lean v4.34.1
   (set `LEAN_BIN` if it is not found automatically); expect `all_checks_passed: true`. A passing check says
   the models have the stated properties; it says nothing about whether rustc still matches the models, for
   which step 1 is the discriminator.
6. **If the fixup or the liveness rules changed**, the cited line ranges are stale: re-audit
   `places_directly_alias`, `AliasFixup::visit_aggregate_assign`, `can_unify_places` and the range start
   and end rules in `precise_liveness.rs` before reusing Findings 3-6.
