# Zero-sized access elimination, UB erasure, and unreachable switch pruning with `assume`

## Summary

This package formalizes, in a deterministic toy control-flow-graph language with undefined behaviour (UB), when three kinds of compiler transformation preserve UB (equivalence of behaviours) and when they erase it (a forward refinement that is not an equivalence): deleting or inserting zero-size memory accesses, pruning `switch` arms whose target is an unreachable block (with or without inserting an `assume`), and replacing a block by an `unreachable` block. Refinement comes in two disciplines: prefix-preserving (`RefinesPP`: where the source reaches UB after emitting a trace `t`, the target may have any behaviour whose trace extends `t`) and whole-trace (`RefinesWT`: where the source reaches UB, the target may have any behaviour). Two further groups of results relate UB-erasing passes to UB checking of their output and to facts that hold on the runs that never reach UB. All statements are kernel-checked in Lean 4 (namespace `Toy.ZstAssume`, no Mathlib).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

**Two meanings of `assume`.** In this package `assume c` is the UB-on-false compiler assumption (in the style of an `assume` intrinsic of a compiler IR): executing it with `c` false is UB. Its weakest-precondition rule is `wp (assume c) Q = c ∧ wp Q`, the rule of `assert c` in Dijkstra-style verification-condition calculi. The miraculous verification-condition `assume c` (rule `c → wp Q`) is a different construct and is not modelled.

One sentence per result (each is the result's plain claim; the full card is under Findings):

- **`delete-zero-size-access-refines`** (theorem, T1): For every zero-size contract `K`, every program `P` and point `(l, i)`: if the `i`-th statement `s` of block `l` is a zero-size access (a `read` or `write` of a type of size 0, or a `copy` of `τ.size * n = 0` bytes, the product taken in unbounded natural numbers), then deleting it gives a prefix-preserving refinement of the source (and hence, by `refinesWT_of_refinesPP`, a whole-trace refinement).
- **`delete-zero-size-access-equivalence-exact-condition`** (characterization, T1): For every zero-size contract `K`, every program `P` and point `(l, i)`: if the `i`-th statement `s` of block `l` is a zero-size access, then deleting it is a prefix-preserving equivalence iff, for every reachable state at `(l, i)` in which `pre₀` of `s` fails, the target run from the point after the deleted statement reaches UB with empty trace; and it is a whole-trace equivalence iff, for every such state, that target run reaches UB after some trace.
- **`delete-zero-size-access-equivalence-sufficient-conditions`** (theorem, T1): For every program `P` and point `(l, i)` whose `i`-th statement `s` of block `l` is a zero-size access: for every zero-size contract `K`, if `pre₀` of `s` holds on every reachable state at `(l, i)`, deleting `s` is a prefix-preserving equivalence; under the contract `pre₀ = True` (`anyPtr`) deleting `s` is a prefix-preserving equivalence; and for every contract `K` other than `nonnullAligned` (that is, permitting null, within the three toy shapes), if every accessed type of `s` has alignment 1, deleting `s` is a prefix-preserving equivalence.
- **`delete-zero-size-access-equivalence-despite-pre-failure`** (counterexample, T0): In the program `pTwoZstReads` (two identical zero-size reads through local 0 at alignment 4, then `halt`) under the `aligned` contract, `pre₀` of the first read fails at a reachable state (local 0 = 1), the target continuation from that state reaches UB with empty trace, and deleting the first read is nevertheless a prefix-preserving equivalence.
- **`zero-size-deletion-erases-ub-instances`** (counterexample, T1): Each of four concrete pairs has UB in the source on a stated input, terminates in the target on that input, is a prefix-preserving refinement and is not a whole-trace equivalence: deleting a zero-size read at alignment 4 through address 1 (contract `aligned`); deleting `copy src dst ⟨4, 4⟩ 0` with `src = 1`, `dst = 8` (contract `aligned`); deleting a zero-size read at alignment 1 through address 0 (contract `nonnullAligned`); and lowering that zero-count copy to the element loop `copyLoopProg 0 1 2 ⟨4, 4⟩ 0`. The loop lowering also overwrites its counter local 2, so on the aligned input with locals `8, 8, 42` the source satisfies `wp` for "local 2 is 42" and the loop does not.
- **`insert-zero-size-access-exact-condition`** (characterization, T1): For every zero-size contract `K`, program `P`, point `(l, i)` and zero-size access `s`: inserting `s` before the `i`-th statement of block `l` is a prefix-preserving refinement iff, for every reachable state at `(l, i)` in which `pre₀` of `s` fails, the source run from `(l, i)` reaches UB with empty trace; and it is a whole-trace refinement iff, for every such state, that source run reaches UB after some trace.
- **`insert-zero-size-access-sufficient-condition`** (theorem, T1): For every zero-size contract `K`, program `P`, point `(l, i)` and zero-size access `s`: if `pre₀` of `s` holds on every reachable state at `(l, i)`, then inserting `s` there is a prefix-preserving equivalence (in particular a refinement).
- **`introducing-zero-size-access-introduces-ub`** (counterexample, T0): Under the `aligned` contract, inserting a zero-size read at alignment 4 through local 0 into `halt` is not a whole-trace refinement (on local 0 = 1 the source halts and the target reaches UB), and hoisting the zero-size read of `pBranchRead` above its branch is not a whole-trace refinement (on locals 0 ↦ 5, 1 ↦ 1).
- **`ub-check-of-output-incomplete`** (counterexample, T0): There is a source program (`pReadZst4`, contract `aligned`) and a pass (deleting its zero-size read) such that the pass is a prefix-preserving refinement and every exact UB checker accepts the output as `UBFree`, yet the source is not `UBFree`; exact checkers exist (noncomputably, `exactUBChecker_exists`).
- **`ub-check-of-output-complete-under-reverse-refinement`** (theorem, T0): For every zero-size contract `K`: for all programs `src`, `tgt`, if `src` whole-trace-refines `tgt` (`RefinesWT K tgt src`) and `tgt` is `UBFree`, then `src` is `UBFree`; for every program `P` and list `Qs` forming a pipeline in which each pass's input whole-trace-refines its output (`RevChainWT K P Qs`, including the empty pipeline), if the last program is `UBFree` then `P` is `UBFree`; and if `EquivPP K src tgt` and `tgt` is `UBFree`, then `src` is `UBFree`.
- **`prune-arm-with-assume-equivalence`** (theorem, T1): For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and the label selected for `v` is an unreachable block (no statements, `unreachable` terminator), then removing every arm with value `v` and appending the UB-on-false `assume (x ≠ v)` to block `l` is a prefix-preserving equivalence, hence (by `equivWT_of_equivPP`) a whole-trace equivalence, and for every postcondition `Q` on trace and final state and every input, the target's demonic total-correctness `wp` holds iff the source's does.
- **`prune-otherwise-with-assume-equivalence`** (theorem, T1): For every zero-size contract `K`, program `P`, block `l`, variable `x`, value `v` and labels `b`, `ow`: if block `l` ends in the single-arm switch `switch x [(v, b)] ow` and `ow` is an unreachable block, then replacing the switch by the UB-on-false `assume (x = v)` followed by `goto b` is a prefix-preserving equivalence, and for every postcondition and input the target's demonic total-correctness `wp` holds iff the source's does.
- **`prune-arm-without-assume-refines`** (theorem, T1): For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and the label selected for `v` is an unreachable block, then removing every arm with value `v` without an `assume` (so that `x = v` goes to `ow`) is a prefix-preserving refinement, and for every postcondition `Q` and input, the source's demonic total-correctness `wp` implies the target's.
- **`prune-arm-without-assume-exact-condition`** (characterization, T1): For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and the label selected for `v` is an unreachable block, then pruning the arms with value `v` without `assume` is a prefix-preserving equivalence iff, for every reachable state at the switch with `x = v`, the target run from the entry of `ow` reaches UB with empty trace; and it is a whole-trace equivalence iff, for every such state, that run reaches UB after some trace.
- **`prune-arm-without-assume-unreachable-otherwise`** (theorem, T1): For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow`, the label selected for `v` is an unreachable block and `ow` is an unreachable block, then pruning the arms with value `v` without `assume` is a prefix-preserving equivalence.
- **`prune-arm-without-assume-invariant`** (theorem, T1): For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and `x ≠ v` holds on every reachable state at the switch (`ReachableAt`, including runs that reach UB later), then pruning the arms with value `v` without `assume` is a prefix-preserving equivalence, with no condition on the pruned label.
- **`prune-arm-without-assume-not-equivalence-and-vc-one-way`** (counterexample, T0): For `pSw` (arm 5 → unreachable block, otherwise halt) and every contract, pruning the arm without `assume`: the target's demonic total-correctness `wp` for the postcondition `True` holds on every input, the source's `wp` for `True` holds exactly when local 0 ≠ 5, so at local 0 = 5 it holds for the target and fails for the source; the pruning is a prefix-preserving refinement but not a whole-trace equivalence.
- **`replace-block-by-unreachable-exact-condition`** (characterization, T1): For every zero-size contract `K`, program `P` and label `b`: replacing block `b` by `Block.unreach` is a prefix-preserving refinement iff, from every reachable state at the entry of `b`, the source run reaches UB with empty trace; and it is a whole-trace refinement iff, from every such state, the source run reaches UB after some trace (events before the UB are permitted; divergence is not).
- **`replace-block-by-unreachable-counterexamples`** (counterexample, T0): For every contract, replacing the block `emit 7; unreachable` of `pEmitBeforeUnreach` by `Block.unreach` is not a prefix-preserving refinement but is a whole-trace refinement; and replacing the loop block of `pLoopBeforeUnreach` (which diverges silently on local 0 = 0) by `Block.unreach` is not a whole-trace refinement.
- **`prune-with-assume-preserves-ub-derived-facts`** (theorem, T1): For every zero-size contract `K`, program `P`, block `l`, value `v`, program point `(l', i')` and state predicate `F`: if `F` holds at `(l', i')` on every run of `P` that never reaches UB, then `F` holds at `(l', i')` on every run of `pruneArmAssume P l v` that never reaches UB.
- **`prune-without-assume-loses-ub-derived-facts`** (counterexample, T1): For every contract: in `pFact` the fact `local 0 ≠ 5` holds at the switch on every non-UB run but fails on a non-UB run of the program pruned without `assume`; in `pStale`, a fold of block 1 to `goto 4` justified by the fact `local 0 ≠ 5` computed on the source is not a whole-trace refinement of its actual input (the program pruned without `assume`), although both that input and the composite are prefix-preserving refinements of the source; with the `assume` kept, the same fold is a prefix-preserving refinement of its input `pruneArmAssume pStale 0 5`. In `pEmitFact`, the fact `local 0 ≠ 5` holds at block 0's switch on every non-UB run, and folding block 0 to `goto 4` with it gives a whole-trace refinement of the source `pEmitFact` that is not a prefix-preserving refinement of `pEmitFact`; the composite that first prunes block 1's arm for 5 without `assume` (a prefix-preserving refinement of `pEmitFact`) and then applies the same fold is likewise a whole-trace refinement of the source `pEmitFact` and not a prefix-preserving refinement of `pEmitFact`, and it is not a whole-trace refinement of its actual input `pruneArm pEmitFact 1 5`.

Every result has non-claims. They are listed first under **Boundaries** (per result, each list complete on its own); read them before relying on a result. In particular: behaviours record emitted values and no final state, `assume` is UB-on-false (not the miraculous verification `assume`), `wp` is demonic total correctness, and `K : ZContract` ranges over exactly three zero-size contract shapes.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### Model fidelity

This is a toy model. Nothing in it mirrors a production definition. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

- **Language.** A program is a list of basic blocks (entry label 0); a block is a list of statements and a terminator. Statements: assignment to integer locals, `emit` of an integer (emitted values form the trace), zero-size or nonzero `read`/`write` of a type `τ = ⟨size, align⟩` through a pointer expression, `copy src dst τ n` of `τ.size * n` bytes with a literal count `n`, and the UB-on-false `assume c`. Terminators: `goto`, `switch x arms ow` (first matching arm), `halt`, `unreachable`. Locals are unbounded integers (no wrapping); memory is a byte-granular map recording which addresses are dereferenceable; loaded values are discarded and stored values are not modelled. The semantics is deterministic, with a single UB class (failed access precondition, failed `assume`, reaching `unreachable`); no provenance, allocation, concurrency or calls.
- **What it is meant to capture.** (1) Zero-size accesses in a Rust-like language, whose documented requirements can include alignment and, in some documented versions, non-nullness although no memory is touched: the precondition of a zero-size access is `pre₀`, given by a contract shape `K : ZContract` (`anyPtr`: always true; `aligned`; `nonnullAligned`). (2) Pruning `switch` arms that lead to an unreachable block, with or without recording the removed case as an `assume`, and replacing a block from which every run reaches UB by `unreachable` (transformations of the kind described in the comments of rustc's `unreachable_prop.rs`, quoted under the switch cards' prior art). (3) Running a UB checker on the output of UB-erasing passes. (4) Facts that hold on the runs that never reach UB, which an optimizer may use.
- **Known gaps.** Contract shapes outside the three constructors (for example "non-null, no alignment requirement", the shape of `read_unaligned`/`write_unaligned`) are not covered; value validity is not modelled (a toy `read` produces no value, so uninhabited zero-size types have no counterpart); counts computed at run time, overlapping copies and volatile accesses are not modelled; behaviours discard final states, so the refinement relations neither establish nor refute preservation of final states or of `wp`; reachability ranges over all initial toy states (no calling context or input precondition); alignment 0 is a degenerate edge (`aligned 0 p` holds iff `p = 0`, Euclidean `Int` remainder); divergence is a behaviour and is never UB (no forward-progress assumption); `wp` is demonic total correctness, and the miraculous verification `assume` (rule `c → wp Q`) is not modelled.

**Scope.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library. The parameter `K : ZContract` ranges over the three zero-size contract shapes the toy defines (`anyPtr`: `pre₀ = True`; `aligned`; `nonnullAligned`); a statement universally quantified over `K` holds in the toy for each of these shapes, and no documented contract version is selected. Contract shapes outside these three (for example "non-null, no alignment requirement") are not covered.

### Subjects and how they relate

- The Lean 4 toolchain `leanprover/lean4:v4.34.1` is the kernel that checked every theorem (no Mathlib; core Lean only).
- rust-lang/rust at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` and at tags `1.80.0` and `1.88.0`, the Rust Reference, Miri, MiniRust and CompCert at the pinned commits listed under Evidence, and the papers listed there, are sources whose text is quoted as motivation for definitions and as prior art. No formal relation is proved between any of them and the toy. Any reading of a quoted source as matching a toy definition is labelled `Basis: derived (modeling bridge)` in the card where it is made.
- Several documented versions of the zero-size requirements of `core::ptr` functions are quoted (tags `1.80.0`, `1.88.0` and commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`). The toy does not select a version: statements about all `K : ZContract` hold for each of the three shapes. Which shape a given function at a given version corresponds to is a reading of the quoted text, not a proved fact.

### Toolchain

Lean `leanprover/lean4:v4.34.1`; the Lake project in `lean/` has one library `Toy` and no dependencies (no Mathlib, no `Std` import). See Revalidation.

## Findings

Namespace `Toy.ZstAssume`; Lean `leanprover/lean4:v4.34.1`, no Mathlib. Every Lean block below is a verbatim quote of the package source, labelled `-- path:lines` relative to the Lake project root `lean/`; proofs are elided as `:= by …` or `:= …`.

Basis for every theorem in this section: execution (Lean kernel check); axioms and statement hashes are recorded under Evidence. Any claim about a real system is a separate `Basis: derived (modeling bridge)` line in the card where it is made.

### Key definitions unfolded (prose)

Unfolded (prose):
- `run K P n c` performs at most `n` steps of `step K P` from `c`; it ends in `done t s` (halted with trace `t`, final state `s`), `ub t` (UB after trace `t`) or `running c' t`. Each step emits at most one value.
- `HasBehFrom K P c b`: `term t` iff some fuel gives `done t _` (the final state is discarded); `wrong t` iff some fuel gives `ub t`; `div t` iff every fuel gives a running outcome and the trace is eventually constantly `t`; `react f` iff every fuel gives a running outcome and every finite prefix of `f` is the trace at some fuel. Exactly one behaviour holds from every configuration: totality and uniqueness are proved (`hasBehFrom_exists`, `hasBehFrom_unique`).
- Behaviours record emitted values and no final state. `RefinesPP K src tgt` iff for every input `σ` and target behaviour `bt` there is a source behaviour `bs` with `bt = bs`, or `bs = wrong t` for a prefix `t` of `bt`'s trace. `RefinesWT` replaces the last disjunct by "`bs = wrong t` for some `t`". `EquivPP`/`EquivWT` are refinement in both directions. None of these relations observes final states.
- `ReachableAt K P l i st` iff for some input the run reaches the configuration `P.at l i st` (block `l`, statements from index `i` on, state `st`) at some fuel; runs that reach UB later count.
- `wp K P Q σ` (demonic total correctness) iff the run from `σ` terminates without UB in some fuel with trace `t` and final state `s` satisfying `Q t s`; UB and divergence both make it false. Proved: `wp` at an `unreachable` terminator is false (`wpFrom_unreachable`), and `wp` of `assume c :: rest` is `c ∧ wp rest` (`wpFrom_assume`).
- `FactOnDefinedRuns K P l i F` iff `F` holds at every configuration `P.at l i st` reached on an input whose whole run never reaches UB (also excluding runs that reach UB later, after further events).
- `IsZeroSizeAccess s` iff `s` is `read p τ` or `write p τ` with `τ.size = 0`, or `copy src dst τ n` with `τ.size * n = 0` (unbounded natural-number product, so the degenerate edges are size 0 or count 0). For such `s`, `s.pre K st = s.zeroPre K st` (`pre_eq_zeroPre_of_isZeroSize`).
- Degenerate edges: `aligned 0 p` holds iff `p = 0` (`aligned_zero_iff`; Euclidean `Int` remainder, `p % 0 = p`); labels outside the program denote `Block.unreach`; `deleteStmt` at an out-of-range index and `List.set` at an out-of-range label change nothing; `insertStmt` at an index past the end inserts before the terminator.

### Definitions (verbatim) with examples

| Definition | Captures | Positive example | Negative example |
|---|---|---|---|
| `Ty` | layout of an accessed type (size, alignment); `1 ≤ align` is the intended convention, not enforced | `ty_fields` | `ty_align_distinguishes` |
| `aligned` | address is a multiple of the alignment (`Int` Euclidean remainder; for alignment 0 the address 0 and no other, `aligned_zero_iff`) | `aligned_pos`, `aligned_zero_align_zero_addr` | `aligned_neg`, `aligned_zero_align_nonzero_addr` |
| `ZContract` | the three toy shapes of zero-size contract `pre₀` | `holds_anyPtr_null_misaligned` | `holds_nonnullAligned_rejects_null` |
| `ZContract.holds` | evaluation of `pre₀` | `holds_aligned_admits_null` | `holds_aligned_rejects_misaligned` |
| `State` | integer locals and a byte-granular dereferenceability map | `state_locals_example` | `state_noMem_example` |
| `State.set` | update one local | `state_set_updates` | `state_set_frames` |
| `Expr` | integer expressions | `expr_eval_add` | `expr_eval_no_wrap` |
| `Expr.eval` | expression evaluation (unbounded `Int`, no wrapping) | `expr_eval_add` | `expr_eval_no_wrap` |
| `Cond` | `assume` conditions | `cond_eval_pos` | `cond_eval_neg` |
| `Cond.eval` | condition evaluation | `cond_eval_pos` | `cond_eval_neg` |
| `Stmt` | statements (`assume` is UB on false) | `isZeroSize_read_zst` | `not_isZeroSize_emit` |
| `Term` | terminators; `switch` takes the first matching arm | `selectTarget_first_match` | `selectTarget_otherwise` |
| `Block` | a basic block | `isUnreachableBlock_unreach` | `not_isUnreachableBlock_halt` |
| `Block.unreach` | no statements, `unreachable` terminator | `isUnreachableBlock_unreach` | `not_isUnreachableBlock_emit_unreach` |
| `Prog` | list of blocks, entry label 0 | `hasBeh_emit7` | `not_hasBeh_emit7_wrong` |
| `Prog.blk` | block lookup; out-of-range labels denote `Block.unreach` | `isUnreachableBlock_out_of_range` | `not_isUnreachableBlock_halt` |
| `bytesDeref` | all bytes of a range are dereferenceable | `bytesDeref_pos` | `bytesDeref_neg` |
| `accessOK` | UB precondition of an access: `pre₀` for zero bytes, non-null + aligned + dereferenceable otherwise | `accessOK_zero_ignores_deref` | `accessOK_nonzero_null` |
| `Stmt.pre` | UB precondition of a statement | `pre_read_aligned` | `pre_read_misaligned` |
| `IsZeroSizeAccess` | zero-size `read`/`write` or `copy` of `τ.size * n = 0` bytes | `isZeroSize_copy_zero_count`, `isZeroSize_copy_zst` | `not_isZeroSize_copy_one`, `not_isZeroSize_read_byte` |
| `Stmt.zeroPre` | `pre₀` of an access statement (both pointers for `copy`) | `zeroPre_read_aligned` | `zeroPre_read_misaligned`, `zeroPre_copy_checks_src` |
| `Stmt.accessTy?` | accessed type of an access statement | `accessTy_read` | `accessTy_emit` |
| `Cfg` | configuration: label, remaining statements, state | `at_entry` | `at_terminator` |
| `Prog.entry` | configuration at a block entry | `reachableAt_entry` | `not_reachableAt_dead_block` |
| `Prog.init` | initial configuration | `reachableAt_entry` | `not_reachableAt_dead_block` |
| `Prog.at` | configuration at program point `(l, i)` | `at_entry` | `at_terminator` |
| `selectTarget` | switch target selection | `selectTarget_first_match` | `selectTarget_otherwise` |
| `StepResult` | result of one step (continue, halt or UB) | `step_emit7` | `step_unreach` |
| `execStmt` | statement execution (`none` is UB) | `execStmt_assume_pass` | `execStmt_assume_fail` |
| `step` | one small step | `step_emit7` | `step_unreach` |
| `Outcome` | fuel-bounded outcome | `outcome_isRunning_running` | `outcome_isRunning_ub` |
| `Outcome.cons` | prepend an optional emitted value | `outcome_cons_some` | `cons_none` |
| `Outcome.trace` | trace of an outcome | `outcome_trace_done` | `outcome_trace_ub_ne` |
| `Outcome.isRunning` | still running | `outcome_isRunning_running` | `outcome_isRunning_ub` |
| `run` | fuel-indexed iteration of `step` | `run_spin` | `run_pHalt` |
| `Beh` | the four behaviours (emitted values, no final state) | `hasBeh_react` | `hasBeh_spin` |
| `prefixOf` | finite prefix of an infinite sequence | `prefixOf_example` | `prefixOf_neg` |
| `HasBehFrom` | behaviours of the run from a configuration | `hasBeh_spin` | `not_hasBeh_emit7_wrong` |
| `HasBeh` | behaviours of a program on an input | `hasBeh_emit7` | `not_hasBeh_emit7_wrong` |
| `GoesWrongFrom` | the run reaches UB after a given trace | `goesWrongFrom_unreach` | `not_goesWrongFrom_halt` |
| `Beh.HasPrefix` | finite prefix of a behaviour's trace | `improvesPP_pos` | `improvesPP_neg` |
| `ImprovesPP` | prefix-preserving improvement (CompCert `behavior_improves`, arguments swapped) | `improvesPP_pos` | `improvesPP_neg` |
| `ImprovesWT` | whole-trace improvement | `improvesWT_pos` | `improvesWT_neg` |
| `RefinesPP` | prefix-preserving refinement (`RefinesPP K src tgt`: `tgt` refines `src`) | `refinesPP_of_src_unreach` | `not_refinesPP_emitUnreach_unreach` |
| `RefinesWT` | whole-trace refinement | `refinesWT_emitUnreach_unreach` | `not_refinesWT_halt_unreach` |
| `EquivPP` | refinement both ways (prefix-preserving) | `zstRead_align_one_alignedContract_deletion_equivPP` | `not_equivPP_emitUnreach_unreach` |
| `EquivWT` | refinement both ways (whole-trace) | `equivWT_emitUnreach_unreach` | `not_equivWT_halt_unreach` |
| `ReachableAt` | a state is reached at a program point for some input (runs reaching UB later included) | `reachableAt_entry` | `not_reachableAt_dead_block` |
| `UBFree` | no input reaches UB (semantic property, distinct from a checker's verdict) | `ubFree_halt` | `not_ubFree_unreach` |
| `wpFrom` | demonic total-correctness weakest precondition from a configuration | `wpFrom_assume` | `wpFrom_unreachable` |
| `wp` | demonic total-correctness weakest precondition of a program | `wp_halt_true` | `not_wp_unreach` |
| `FactOnDefinedRuns` | a state predicate holds at a point on every run that never reaches UB (a whole-run condition) | `pFact_fact` | `pruneArmAssume_fact_hypothesis_counterexample` |
| `deleteStmt` | delete the `i`-th statement of a block | `deleteStmt_example` | `deleteStmt_out_of_range` |
| `insertStmt` | insert a statement | `insertStmt_example` | `insertStmt_past_end` |
| `replaceUnreachable` | replace a block by `Block.unreach` | `replaceUnreachable_example` | `replaceUnreachable_out_of_range` |
| `setTerm` | replace a terminator | `foldToGoto_example` | `setTerm_out_of_range` |
| `IsUnreachableBlock` | a label denotes `Block.unreach` | `isUnreachableBlock_out_of_range` | `not_isUnreachableBlock_emit_unreach` |
| `dropArms` | remove the arms with a value | `dropArms_example` | `dropArms_keeps` |
| `pruneArm` | prune arms without `assume` | `pruneArm_example` | `pruneArm_non_switch` |
| `pruneArmAssume` | prune arms and insert `assume (x ≠ v)` | `pruneArmAssume_example` | `pruneArmAssume_non_switch` |
| `pruneOtherwiseAssume` | single-arm shape `switch x [(v, b)] ow` to `assume (x = v); goto b`; identity on switches with another number of arms | `pruneOtherwiseAssume_example` | `pruneOtherwiseAssume_two_arms` |
| `foldToGoto` | fact-based folding of a terminator to `goto` | `foldToGoto_example` | `staleFact_fold_after_pruneArm` |
| `copyProg` | one-block copy program | `copyProg_aligned_term` | `copyProg_misaligned_wrong` |
| `copyLoopProg` | element-loop lowering of a copy: sets counter `i`, and its loop body advances `s` and `d` (at count 0 the body does not run: under every contract and from every input state, `copyLoopProg 0 1 2 ⟨4, 4⟩ 0` halts with locals `0`, `1` unchanged and local `2` set to 0, `copyLoopProg_zeroCount_run`; `copyLoopProg_zeroCount_preserves_src_dst` is the instance with locals `8, 12, 42` under `aligned`) | `copyLoopProg_zero_term` | `copyLoopProg_one_misaligned_wrong` |
| `ExactUBChecker` | a Boolean checker whose verdict is exactly `UBFree` | `exactUBChecker_exists` | `not_exactUBChecker_const_true` |
| `RevChainWT` | pipeline whose passes' inputs whole-trace-refine their outputs | `revChainWT_nil` | `not_revChainWT_unreach_halt` |

```lean
-- Toy/ZstAssume/Syntax.lean:17
abbrev Var := Nat
```

```lean
-- Toy/ZstAssume/Syntax.lean:20
abbrev Label := Nat
```

```lean
-- Toy/ZstAssume/Syntax.lean:25-28
structure Ty where
  size : Nat
  align : Nat
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:32
def aligned (a : Nat) (p : Int) : Bool := p % (a : Int) == 0
```

```lean
-- Toy/ZstAssume/Syntax.lean:43-47
inductive ZContract where
  | anyPtr
  | aligned
  | nonnullAligned
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:51-54
def ZContract.holds : ZContract → Nat → Int → Bool
  | .anyPtr, _, _ => true
  | .aligned, a, p => Toy.ZstAssume.aligned a p
  | .nonnullAligned, a, p => p != 0 && Toy.ZstAssume.aligned a p
```

```lean
-- Toy/ZstAssume/Syntax.lean:58-60
structure State where
  locals : Var → Int
  deref : Int → Bool
```

```lean
-- Toy/ZstAssume/Syntax.lean:63-64
def State.set (s : State) (x : Var) (v : Int) : State :=
  { s with locals := fun y => if y = x then v else s.locals y }
```

```lean
-- Toy/ZstAssume/Syntax.lean:67-71
inductive Expr where
  | const (v : Int)
  | var (x : Var)
  | add (a b : Expr)
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:74-77
def Expr.eval (s : State) : Expr → Int
  | .const v => v
  | .var x => s.locals x
  | .add a b => a.eval s + b.eval s
```

```lean
-- Toy/ZstAssume/Syntax.lean:80-83
inductive Cond where
  | eq (x : Var) (v : Int)
  | ne (x : Var) (v : Int)
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:86-88
def Cond.eval (s : State) : Cond → Bool
  | .eq x v => s.locals x == v
  | .ne x v => s.locals x != v
```

```lean
-- Toy/ZstAssume/Syntax.lean:104-111
inductive Stmt where
  | emit (e : Expr)
  | assume (c : Cond)
  | assign (x : Var) (e : Expr)
  | read (p : Expr) (τ : Ty)
  | write (p : Expr) (τ : Ty)
  | copy (src dst : Expr) (τ : Ty) (n : Nat)
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:115-120
inductive Term where
  | goto (b : Label)
  | switch (x : Var) (arms : List (Int × Label)) (ow : Label)
  | unreachable
  | halt
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:123-126
structure Block where
  stmts : List Stmt
  term : Term
deriving DecidableEq, Repr
```

```lean
-- Toy/ZstAssume/Syntax.lean:129
def Block.unreach : Block := ⟨[], .unreachable⟩
```

```lean
-- Toy/ZstAssume/Syntax.lean:133
abbrev Prog := List Block
```

```lean
-- Toy/ZstAssume/Syntax.lean:137
def Prog.blk (P : Prog) (l : Label) : Block := P.getD l Block.unreach
```

```lean
-- Toy/ZstAssume/Syntax.lean:140-142
def bytesDeref (d : Int → Bool) (p : Int) : Nat → Bool
  | 0 => true
  | k + 1 => d (p + k) && bytesDeref d p k
```

```lean
-- Toy/ZstAssume/Syntax.lean:148-149
def accessOK (K : ZContract) (d : Int → Bool) (a : Nat) (p : Int) (bytes : Nat) : Bool :=
  if bytes = 0 then K.holds a p else p != 0 && aligned a p && bytesDeref d p bytes
```

```lean
-- Toy/ZstAssume/Syntax.lean:153-161
def Stmt.pre (K : ZContract) (s : State) : Stmt → Bool
  | .emit _ => true
  | .assign _ _ => true
  | .assume c => c.eval s
  | .read p τ => accessOK K s.deref τ.align (p.eval s) τ.size
  | .write p τ => accessOK K s.deref τ.align (p.eval s) τ.size
  | .copy src dst τ n =>
      accessOK K s.deref τ.align (src.eval s) (τ.size * n) &&
        accessOK K s.deref τ.align (dst.eval s) (τ.size * n)
```

```lean
-- Toy/ZstAssume/Syntax.lean:165-169
def IsZeroSizeAccess : Stmt → Prop
  | .read _ τ => τ.size = 0
  | .write _ τ => τ.size = 0
  | .copy _ _ τ n => τ.size * n = 0
  | _ => False
```

```lean
-- Toy/ZstAssume/Syntax.lean:177-181
def Stmt.zeroPre (K : ZContract) (s : State) : Stmt → Bool
  | .read p τ => K.holds τ.align (p.eval s)
  | .write p τ => K.holds τ.align (p.eval s)
  | .copy src dst τ _ => K.holds τ.align (src.eval s) && K.holds τ.align (dst.eval s)
  | _ => true
```

```lean
-- Toy/ZstAssume/Syntax.lean:184-188
def Stmt.accessTy? : Stmt → Option Ty
  | .read _ τ => some τ
  | .write _ τ => some τ
  | .copy _ _ τ _ => some τ
  | _ => none
```

```lean
-- Toy/ZstAssume/Semantics.lean:22-25
structure Cfg where
  lbl : Label
  rest : List Stmt
  st : State
```

```lean
-- Toy/ZstAssume/Semantics.lean:28
def Prog.entry (P : Prog) (b : Label) (st : State) : Cfg := ⟨b, (P.blk b).stmts, st⟩
```

```lean
-- Toy/ZstAssume/Semantics.lean:31
def Prog.init (P : Prog) (σ : State) : Cfg := P.entry 0 σ
```

```lean
-- Toy/ZstAssume/Semantics.lean:35-36
def Prog.at (P : Prog) (l : Label) (i : Nat) (st : State) : Cfg :=
  ⟨l, (P.blk l).stmts.drop i, st⟩
```

```lean
-- Toy/ZstAssume/Semantics.lean:40-42
def selectTarget : List (Int × Label) → Label → Int → Label
  | [], ow, _ => ow
  | (v, b) :: arms, ow, x => if x = v then b else selectTarget arms ow x
```

```lean
-- Toy/ZstAssume/Semantics.lean:46-49
inductive StepResult where
  | next (out : Option Int) (c : Cfg)
  | halt (s : State)
  | ub
```

```lean
-- Toy/ZstAssume/Semantics.lean:53-57
def execStmt (K : ZContract) (stmt : Stmt) (s : State) : Option (Option Int × State) :=
  match stmt with
  | .emit e => some (some (e.eval s), s)
  | .assign x e => some (none, s.set x (e.eval s))
  | other => if other.pre K s then some (none, s) else none
```

```lean
-- Toy/ZstAssume/Semantics.lean:60-71
def step (K : ZContract) (P : Prog) (c : Cfg) : StepResult :=
  match c.rest with
  | stmt :: rest =>
      match execStmt K stmt c.st with
      | some (o, s') => .next o ⟨c.lbl, rest, s'⟩
      | none => .ub
  | [] =>
      match (P.blk c.lbl).term with
      | .goto b => .next none (P.entry b c.st)
      | .switch x arms ow => .next none (P.entry (selectTarget arms ow (c.st.locals x)) c.st)
      | .unreachable => .ub
      | .halt => .halt c.st
```

```lean
-- Toy/ZstAssume/Semantics.lean:75-78
inductive Outcome where
  | done (t : List Int) (s : State)
  | ub (t : List Int)
  | running (c : Cfg) (t : List Int)
```

```lean
-- Toy/ZstAssume/Semantics.lean:81-84
def Outcome.cons (o : Option Int) : Outcome → Outcome
  | .done t s => .done (o.toList ++ t) s
  | .ub t => .ub (o.toList ++ t)
  | .running c t => .running c (o.toList ++ t)
```

```lean
-- Toy/ZstAssume/Semantics.lean:87-90
def Outcome.trace : Outcome → List Int
  | .done t _ => t
  | .ub t => t
  | .running _ t => t
```

```lean
-- Toy/ZstAssume/Semantics.lean:93-95
def Outcome.isRunning : Outcome → Bool
  | .running _ _ => true
  | _ => false
```

```lean
-- Toy/ZstAssume/Semantics.lean:98-104
def run (K : ZContract) (P : Prog) : Nat → Cfg → Outcome
  | 0, c => .running c []
  | n + 1, c =>
      match step K P c with
      | .next o c' => (run K P n c').cons o
      | .halt s => .done [] s
      | .ub => .ub []
```

```lean
-- Toy/ZstAssume/Semantics.lean:111-115
inductive Beh where
  | term (t : List Int)
  | wrong (t : List Int)
  | div (t : List Int)
  | react (f : Nat → Int)
```

```lean
-- Toy/ZstAssume/Semantics.lean:118
def prefixOf (f : Nat → Int) (k : Nat) : List Int := (List.range k).map f
```

```lean
-- Toy/ZstAssume/Semantics.lean:123-129
def HasBehFrom (K : ZContract) (P : Prog) (c : Cfg) : Beh → Prop
  | .term t => ∃ n s, run K P n c = .done t s
  | .wrong t => ∃ n, run K P n c = .ub t
  | .div t => (∀ n, (run K P n c).isRunning = true) ∧
      ∃ N, ∀ n, N ≤ n → (run K P n c).trace = t
  | .react f => (∀ n, (run K P n c).isRunning = true) ∧
      ∀ k, ∃ n, (run K P n c).trace = prefixOf f k
```

```lean
-- Toy/ZstAssume/Semantics.lean:132-133
def HasBeh (K : ZContract) (P : Prog) (σ : State) (b : Beh) : Prop :=
  HasBehFrom K P (P.init σ) b
```

```lean
-- Toy/ZstAssume/Semantics.lean:136-137
def GoesWrongFrom (K : ZContract) (P : Prog) (c : Cfg) (t : List Int) : Prop :=
  ∃ n, run K P n c = .ub t
```

```lean
-- Toy/ZstAssume/Semantics.lean:140-144
def Beh.HasPrefix : Beh → List Int → Prop
  | .term u, t => t <+: u
  | .wrong u, t => t <+: u
  | .div u, t => t <+: u
  | .react f, t => t = prefixOf f t.length
```

```lean
-- Toy/ZstAssume/Semantics.lean:148-149
def ImprovesPP (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .wrong t ∧ bt.HasPrefix t
```

```lean
-- Toy/ZstAssume/Semantics.lean:152-153
def ImprovesWT (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .wrong t
```

```lean
-- Toy/ZstAssume/Semantics.lean:158-159
def RefinesPP (K : ZContract) (src tgt : Prog) : Prop :=
  ∀ σ bt, HasBeh K tgt σ bt → ∃ bs, HasBeh K src σ bs ∧ ImprovesPP bt bs
```

```lean
-- Toy/ZstAssume/Semantics.lean:163-164
def RefinesWT (K : ZContract) (src tgt : Prog) : Prop :=
  ∀ σ bt, HasBeh K tgt σ bt → ∃ bs, HasBeh K src σ bs ∧ ImprovesWT bt bs
```

```lean
-- Toy/ZstAssume/Semantics.lean:167
def EquivPP (K : ZContract) (p q : Prog) : Prop := RefinesPP K p q ∧ RefinesPP K q p
```

```lean
-- Toy/ZstAssume/Semantics.lean:170
def EquivWT (K : ZContract) (p q : Prog) : Prop := RefinesWT K p q ∧ RefinesWT K q p
```

```lean
-- Toy/ZstAssume/Semantics.lean:175-176
def ReachableAt (K : ZContract) (P : Prog) (l : Label) (i : Nat) (st : State) : Prop :=
  ∃ σ n t, run K P n (P.init σ) = .running (P.at l i st) t
```

```lean
-- Toy/ZstAssume/Semantics.lean:180-181
def UBFree (K : ZContract) (P : Prog) : Prop :=
  ∀ σ t, ¬ HasBeh K P σ (.wrong t)
```

```lean
-- Toy/ZstAssume/Semantics.lean:189-190
def wpFrom (K : ZContract) (P : Prog) (Q : List Int → State → Prop) (c : Cfg) : Prop :=
  ∃ n t s, run K P n c = .done t s ∧ Q t s
```

```lean
-- Toy/ZstAssume/Semantics.lean:193-194
def wp (K : ZContract) (P : Prog) (Q : List Int → State → Prop) (σ : State) : Prop :=
  wpFrom K P Q (P.init σ)
```

```lean
-- Toy/ZstAssume/Semantics.lean:202-205
def FactOnDefinedRuns (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (F : State → Prop) : Prop :=
  ∀ σ st, (∃ n t, run K P n (P.init σ) = .running (P.at l i st) t) →
    (∀ t, ¬ HasBeh K P σ (.wrong t)) → F st
```

```lean
-- Toy/ZstAssume/Transforms.lean:13-14
def deleteStmt (P : Prog) (l : Label) (i : Nat) : Prog :=
  P.set l { P.blk l with stmts := (P.blk l).stmts.eraseIdx i }
```

```lean
-- Toy/ZstAssume/Transforms.lean:18-19
def insertStmt (P : Prog) (l : Label) (i : Nat) (s : Stmt) : Prog :=
  P.set l { P.blk l with stmts := (P.blk l).stmts.take i ++ s :: (P.blk l).stmts.drop i }
```

```lean
-- Toy/ZstAssume/Transforms.lean:22-23
def replaceUnreachable (P : Prog) (b : Label) : Prog :=
  P.set b Block.unreach
```

```lean
-- Toy/ZstAssume/Transforms.lean:26-27
def setTerm (P : Prog) (l : Label) (t : Term) : Prog :=
  P.set l { P.blk l with term := t }
```

```lean
-- Toy/ZstAssume/Transforms.lean:31
def IsUnreachableBlock (P : Prog) (b : Label) : Prop := P.blk b = Block.unreach
```

```lean
-- Toy/ZstAssume/Transforms.lean:38-39
def dropArms (arms : List (Int × Label)) (v : Int) : List (Int × Label) :=
  arms.filter (fun a => a.1 != v)
```

```lean
-- Toy/ZstAssume/Transforms.lean:44-47
def pruneArm (P : Prog) (l : Label) (v : Int) : Prog :=
  match (P.blk l).term with
  | .switch x arms ow => setTerm P l (.switch x (dropArms arms v) ow)
  | _ => P
```

```lean
-- Toy/ZstAssume/Transforms.lean:51-55
def pruneArmAssume (P : Prog) (l : Label) (v : Int) : Prog :=
  match (P.blk l).term with
  | .switch x arms ow =>
      P.set l ⟨(P.blk l).stmts ++ [.assume (.ne x v)], .switch x (dropArms arms v) ow⟩
  | _ => P
```

```lean
-- Toy/ZstAssume/Transforms.lean:59-62
def pruneOtherwiseAssume (P : Prog) (l : Label) : Prog :=
  match (P.blk l).term with
  | .switch x [(v, b)] _ => P.set l ⟨(P.blk l).stmts ++ [.assume (.eq x v)], .goto b⟩
  | _ => P
```

```lean
-- Toy/ZstAssume/Transforms.lean:67
def foldToGoto (P : Prog) (l : Label) (b : Label) : Prog := setTerm P l (.goto b)
```

```lean
-- Toy/ZstAssume/Transforms.lean:70-71
def copyProg (s d : Var) (τ : Ty) (n : Nat) : Prog :=
  [⟨[.copy (.var s) (.var d) τ n], .halt⟩]
```

```lean
-- Toy/ZstAssume/Transforms.lean:76-83
def copyLoopProg (s d i : Var) (τ : Ty) (n : Nat) : Prog :=
  [ ⟨[.assign i (.const n)], .goto 1⟩,
    ⟨[], .switch i [(0, 3)] 2⟩,
    ⟨[.copy (.var s) (.var d) τ 1,
      .assign s (.add (.var s) (.const τ.size)),
      .assign d (.add (.var d) (.const τ.size)),
      .assign i (.add (.var i) (.const (-1)))], .goto 1⟩,
    ⟨[], .halt⟩ ]
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:631-632
def ExactUBChecker (K : ZContract) (chk : Prog → Bool) : Prop :=
  ∀ P, chk P = true ↔ UBFree K P
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:687-689
def RevChainWT (K : ZContract) : Prog → List Prog → Prop
  | _, [] => True
  | P, Q :: Qs => RefinesWT K Q P ∧ RevChainWT K Q Qs
```

#### Concrete programs and states used by the examples

```lean
-- Toy/ZstAssume/Examples.lean:13
def mkState (xs : List Int) : State := ⟨fun i => xs.getD i 0, fun _ => true⟩
```

```lean
-- Toy/ZstAssume/Examples.lean:16
def mkStateNoMem (xs : List Int) : State := ⟨fun i => xs.getD i 0, fun _ => false⟩
```

```lean
-- Toy/ZstAssume/Examples.lean:134
def pEmit7 : Prog := [⟨[.emit (.const 7)], .halt⟩]
```

```lean
-- Toy/ZstAssume/Examples.lean:136
def pUnreach : Prog := [Block.unreach]
```

```lean
-- Toy/ZstAssume/Examples.lean:138
def pHalt : Prog := [⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Examples.lean:140
def pSpin : Prog := [⟨[], .goto 0⟩]
```

```lean
-- Toy/ZstAssume/Examples.lean:142
def pReact : Prog := [⟨[.emit (.const 1)], .goto 0⟩]
```

```lean
-- Toy/ZstAssume/Examples.lean:247
def pEmitUnreach : Prog := [⟨[.emit (.const 7)], .unreachable⟩]
```

```lean
-- Toy/ZstAssume/Examples.lean:270
def pTwoHalts : Prog := [⟨[], .halt⟩, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:248
def pTwoZstReads : Prog := [⟨[.read (.var 0) ⟨0, 4⟩, .read (.var 0) ⟨0, 4⟩], .halt⟩]
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:293
def pReadZst4 : Prog := [⟨[.read (.var 0) ⟨0, 4⟩], .halt⟩]
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:296
def pReadZst1 : Prog := [⟨[.read (.var 0) ⟨0, 1⟩], .halt⟩]
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:300
def pCopy0 : Prog := copyProg 0 1 ⟨4, 4⟩ 0
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:588-589
def pBranchRead : Prog :=
  [⟨[], .switch 0 [(0, 1)] 2⟩, ⟨[.read (.var 1) ⟨0, 4⟩], .halt⟩, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:592-593
def pBranchReadHoisted : Prog :=
  deleteStmt (insertStmt pBranchRead 0 0 (.read (.var 1) ⟨0, 4⟩)) 1 0
```

```lean
-- Toy/ZstAssume/Switch.lean:68
def pSw : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, Block.unreach, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:116-117
def pSwEmitUnreach : Prog :=
  [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 7)], .unreachable⟩, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:155
def pSwLive : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:245-246
def pSwLiveUnreachOw : Prog :=
  [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 1)], .halt⟩, Block.unreach]
```

```lean
-- Toy/ZstAssume/Switch.lean:293
def pSwOne : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, ⟨[], .halt⟩, Block.unreach]
```

```lean
-- Toy/ZstAssume/Switch.lean:504-505
def pSwAssumeOw : Prog :=
  [⟨[], .switch 0 [(5, 1)] 2⟩, Block.unreach, ⟨[.assume (.ne 0 5)], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:534
def pSwInv : Prog := [⟨[.assign 0 (.const 1)], .switch 0 [(5, 1)] 2⟩, Block.unreach, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:562-563
def pSwDiffVar : Prog :=
  [⟨[.assign 0 (.const 1)], .switch 1 [(5, 1)] 2⟩, ⟨[.emit (.const 1)], .halt⟩, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:611
def pSwDead : Prog := [⟨[], .switch 0 [(5, 1)] 2⟩, Block.unreach, Block.unreach]
```

```lean
-- Toy/ZstAssume/Switch.lean:647
def pFact : Prog := [⟨[], .switch 0 [(5, 2)] 1⟩, ⟨[.emit (.var 0)], .halt⟩, Block.unreach]
```

```lean
-- Toy/ZstAssume/Switch.lean:720-722
def pStale : Prog :=
  [⟨[], .switch 0 [(5, 3)] 1⟩, ⟨[], .switch 0 [(5, 2)] 4⟩, ⟨[.emit (.const 1)], .halt⟩,
    Block.unreach, ⟨[.emit (.const 0)], .halt⟩]
```

```lean
-- Toy/ZstAssume/Switch.lean:792-797
def pEmitFact : Prog :=
  [ ⟨[], .switch 0 [(5, 2)] 4⟩,
    ⟨[], .switch 0 [(5, 3)] 4⟩,
    ⟨[.emit (.const 7)], .goto 1⟩,
    Block.unreach,
    ⟨[.emit (.const 0)], .halt⟩ ]
```

```lean
-- Toy/ZstAssume/Backward.lean:33
def pEmitBeforeUnreach : Prog := [⟨[], .goto 1⟩, ⟨[.emit (.const 7)], .unreachable⟩]
```

```lean
-- Toy/ZstAssume/Backward.lean:65
def pLoopBeforeUnreach : Prog := [⟨[], .switch 0 [(0, 0)] 1⟩, Block.unreach]
```

```lean
-- Toy/ZstAssume/Backward.lean:101-102
def pSilentToUnreach : Prog :=
  [⟨[], .goto 1⟩, ⟨[.assign 0 (.const 1)], .goto 2⟩, Block.unreach]
```

### Results

Each card gives the plain claim, kind, tier and depth, the verbatim Lean statement, the hypothesis ledger (each `tight` entry names a kernel-checked counterexample in which every other hypothesis holds and every conclusion of the listed theorems fails, and records the class of that witness), the non-vacuity witness, the positive control for counterexample results, prior art and the design question. Non-claims are under Boundaries.

#### `delete-zero-size-access-refines`

**Plain claim.** For every zero-size contract `K`, every program `P` and point `(l, i)`: if the `i`-th statement `s` of block `l` is a zero-size access (a `read` or `write` of a type of size 0, or a `copy` of `τ.size * n = 0` bytes, the product taken in unbounded natural numbers), then deleting it gives a prefix-preserving refinement of the source (and hence, by `refinesWT_of_refinesPP`, a whole-trace refinement).

**Kind / tier / depth.** theorem / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:125-127
theorem deleteZeroSizeAccess_refinesPP (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    RefinesPP K P (deleteStmt P l i) := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some s` | `deleteZeroSizeAccess_refinesPP` | identifies `s` as the statement deleted at point `(l, i)` | tight: `deleteStmt_hs_counterexample` | one-block program `pEmit7` (position `(0, 0)` holds `emit 7`) with `s := read (var 0) ⟨0, 1⟩`, for each contract `K ≠ .nonnullAligned` (so `K = .anyPtr` and `K = .aligned`); `hz` holds |
| `hz : IsZeroSizeAccess s` | `deleteZeroSizeAccess_refinesPP` | restricts the deleted statement to a zero-size `read`/`write` or a `copy` of `τ.size * n = 0` bytes | tight: `deleteStmt_hz_counterexample` | one-block program `pEmit7` with `s := emit 7`, for every contract `K`; `hs` holds |

**Non-vacuity.** `pReadZst4` (a zero-size read at alignment 4) satisfies `hs` and `hz` at `(0, 0)`; its deletion under `aligned` is proved to be a prefix-preserving refinement independently in `zstRead_misaligned_deletion_erases_ub`. (Lean: `deleteZeroSizeAccess_refinesPP_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `delete-zero-size-access-refines`"; read them before relying on this result.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65–79, doi:10.1145/3453483.3454030 (refinement in which source UB permits any target behaviour).
- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs: L18 "* A [null] pointer is *never* valid for reads/writes."; L19 "* For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes."; L61–62 "When a function requires proper alignment, it does so even if the access has size 0, i.e., even if memory is not actually touched."; `copy_nonoverlapping` L479 "* `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.", L483 "* Both `src` and `dst` must be properly aligned."; `read` L1613 "* `src` must be [valid] for reads or `T` must be a ZST.", L1620 "Note that even if `T` has size `0`, the pointer must be properly aligned."; `drop_in_place` L776 "* `to_drop` must be properly aligned, even if `T` has size 0.", L778 "* `to_drop` must be nonnull, even if `T` has size 0."
- Contract history (documentation): rust-lang/rust tag 1.80.0, library/core/src/ptr/mod.rs L18 "* For operations of [size zero][zst], *every* pointer is valid, including the [null] pointer." and `read` L1191 "Note that even if `T` has size `0`, the pointer must be non-null and properly aligned."; library/core/src/intrinsics.rs (1.80.0) `copy_nonoverlapping` L2875–2876 "Note that even if the effectively copied size (`count * size_of::<T>()`) is `0`, the pointers must be non-null and properly aligned." Tag 1.88.0: ptr/mod.rs L18–19 "* For memory accesses of [size zero][zst], *every* pointer is valid, including the [null] pointer.", `read` L1320 "Note that even if `T` has size `0`, the pointer must be properly aligned."; intrinsics/mod.rs `copy_nonoverlapping` L3668–3669 "... is `0`, the pointers must be properly aligned." The definition of validity was changed by rust-lang/rust#152615 ('refactor 'valid for read/write' definition: exclude null', merged 2026-02-28, https://github.com/rust-lang/rust/pull/152615), which states it is an attempt to resolve rust-lang/rust#138351 ('core::ptr::replace implementation is unsound since Rust 1.80', closed 2026-02-28, https://github.com/rust-lang/rust/issues/138351). The parameter `K : ZContract` covers all of these versions; no version is selected.
- MiniRust (an executable specification of Rust semantics; not the official Rust semantics), minirust/minirust 98043a70de612f6af4eaf1e35cf0b8a6ebea22ce, spec/mem/basic.md L198–203: "// For zero-sized accesses, there is nothing to check." / "// (Provenance monotonicity says that if we allow zero-sized accesses" / "// for `None` provenance we have to allow it for all provenance.)" / "if len.is_zero() {" / "return ret(None);" / "}"; `store` L234–236: "if !align.is_aligned(ptr.addr) {" / "throw_ub!(\"store to a misaligned pointer\");" / "}"; `load` L260–262: "if !align.is_aligned(ptr.addr) {" / "throw_ub!(\"load from a misaligned pointer\");" / "}". In that model a zero-sized load or store is UB through a misaligned pointer and is not rejected by `check_ptr` for any address, which matches the toy shape `aligned` (derived reading of the quoted lines).
- N. Popov, A. Ballman, 'Allow zero length operations on null pointers', ISO/IEC JTC1/SC22/WG14 N3322, 2024-08-28, https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3322.pdf, abstract: "Proposes allowing null + 0, null - null and passing null to certain C standard library functions if the length argument is also zero. This removes a class of undefined behavior and brings the specification more in line with C++." (a proposal for C2y; its adoption status is not recorded here).

**Design question.** Deleting a zero-size access or a zero-count copy removes code whose sole effect is a possible UB event (the precondition `pre₀` of the access). A verified compiler must know when the deletion is an equivalence (UB-preserving) and when it is merely a forward refinement (UB-erasing), for each documented zero-size contract.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's zero-size access, whose UB precondition is `pre₀` of a `ZContract` shape, is read as a model of the zero-size requirements quoted under Prior art (the `core::ptr` documentation and, where cited, the MiniRust load/store checks), which state alignment and, depending on the function and version, non-null requirements for accesses that touch no memory. Which shape matches a given function and version is a reading of the quoted text, made explicitly in the prior-art items marked "derived reading of the quoted lines". No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `delete-zero-size-access-equivalence-exact-condition`

**Plain claim.** For every zero-size contract `K`, every program `P` and point `(l, i)`: if the `i`-th statement `s` of block `l` is a zero-size access, then deleting it is a prefix-preserving equivalence iff, for every reachable state at `(l, i)` in which `pre₀` of `s` fails, the target run from the point after the deleted statement reaches UB with empty trace; and it is a whole-trace equivalence iff, for every such state, that target run reaches UB after some trace.

**Kind / tier / depth.** characterization / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:134-138
theorem deleteZeroSizeAccess_equivPP_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivPP K P (deleteStmt P l i) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        GoesWrongFrom K (deleteStmt P l i) ((deleteStmt P l i).at l i st) [] := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:145-149
theorem deleteZeroSizeAccess_equivWT_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivWT K P (deleteStmt P l i) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        ∃ t, GoesWrongFrom K (deleteStmt P l i) ((deleteStmt P l i).at l i st) t := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some s` | `deleteZeroSizeAccess_equivPP_iff`, `deleteZeroSizeAccess_equivWT_iff` | identifies `s` as the statement deleted at point `(l, i)` | tight: `deleteStmt_hs_counterexample` | one-block program `pEmit7` (position `(0, 0)` holds `emit 7`) with `s := read (var 0) ⟨0, 1⟩`, for each contract `K ≠ .nonnullAligned` (so `K = .anyPtr` and `K = .aligned`); `hz` holds; the left-hand sides of both characterizations are false and the right-hand sides hold vacuously (`zeroPre` of `s` is `true` in every state) |
| `hz : IsZeroSizeAccess s` | `deleteZeroSizeAccess_equivPP_iff`, `deleteZeroSizeAccess_equivWT_iff` | restricts the deleted statement to a zero-size `read`/`write` or a `copy` of `τ.size * n = 0` bytes | tight: `deleteStmt_hz_counterexample` | one-block program `pEmit7` with `s := emit 7`, for every contract `K`; `hs` holds; the left-hand sides of both characterizations are false and the right-hand sides hold vacuously (`zeroPre` of `s` is `true` in every state) |

**Non-vacuity.** `pTwoZstReads` satisfies `hs` and `hz` at `(0, 0)`. Under `aligned` it is also an instance in which the right-hand sides hold although a reachable state violates `pre₀` (`deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure`); `zstRead_misaligned_deletion_erases_ub` is an instance in which both sides are false. (Lean: `deleteZeroSizeAccess_iff_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `delete-zero-size-access-equivalence-exact-condition`"; read them before relying on this result.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65–79, doi:10.1145/3453483.3454030 (refinement in which source UB permits any target behaviour).
- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs: L18 "* A [null] pointer is *never* valid for reads/writes."; L19 "* For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes."; L61–62 "When a function requires proper alignment, it does so even if the access has size 0, i.e., even if memory is not actually touched."; `copy_nonoverlapping` L479 "* `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.", L483 "* Both `src` and `dst` must be properly aligned."; `read` L1613 "* `src` must be [valid] for reads or `T` must be a ZST.", L1620 "Note that even if `T` has size `0`, the pointer must be properly aligned."; `drop_in_place` L776 "* `to_drop` must be properly aligned, even if `T` has size 0.", L778 "* `to_drop` must be nonnull, even if `T` has size 0."
- MiniRust (an executable specification of Rust semantics; not the official Rust semantics), minirust/minirust 98043a70de612f6af4eaf1e35cf0b8a6ebea22ce, spec/mem/basic.md L198–203: "// For zero-sized accesses, there is nothing to check." / "// (Provenance monotonicity says that if we allow zero-sized accesses" / "// for `None` provenance we have to allow it for all provenance.)" / "if len.is_zero() {" / "return ret(None);" / "}"; `store` L234–236: "if !align.is_aligned(ptr.addr) {" / "throw_ub!(\"store to a misaligned pointer\");" / "}"; `load` L260–262: "if !align.is_aligned(ptr.addr) {" / "throw_ub!(\"load from a misaligned pointer\");" / "}". In that model a zero-sized load or store is UB through a misaligned pointer and is not rejected by `check_ptr` for any address, which matches the toy shape `aligned` (derived reading of the quoted lines).

**Design question.** Deleting a zero-size access or a zero-count copy removes code whose sole effect is a possible UB event (the precondition `pre₀` of the access). A verified compiler must know when the deletion is an equivalence (UB-preserving) and when it is merely a forward refinement (UB-erasing), for each documented zero-size contract.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's zero-size access, whose UB precondition is `pre₀` of a `ZContract` shape, is read as a model of the zero-size requirements quoted under Prior art (the `core::ptr` documentation and, where cited, the MiniRust load/store checks), which state alignment and, depending on the function and version, non-null requirements for accesses that touch no memory. Which shape matches a given function and version is a reading of the quoted text, made explicitly in the prior-art items marked "derived reading of the quoted lines". No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `delete-zero-size-access-equivalence-sufficient-conditions`

**Plain claim.** For every program `P` and point `(l, i)` whose `i`-th statement `s` of block `l` is a zero-size access: for every zero-size contract `K`, if `pre₀` of `s` holds on every reachable state at `(l, i)`, deleting `s` is a prefix-preserving equivalence; under the contract `pre₀ = True` (`anyPtr`) deleting `s` is a prefix-preserving equivalence; and for every contract `K` other than `nonnullAligned` (that is, permitting null, within the three toy shapes), if every accessed type of `s` has alignment 1, deleting `s` is a prefix-preserving equivalence.

**Kind / tier / depth.** theorem / T1 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:154-157
theorem deleteZeroSizeAccess_equivPP_of_zeroPre_reachable (K : ZContract) (P : Prog)
    (l : Label) (i : Nat) (s : Stmt) (hs : (P.blk l).stmts[i]? = some s)
    (hz : IsZeroSizeAccess s) (hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true) :
    EquivPP K P (deleteStmt P l i) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:162-164
theorem deleteZeroSizeAccess_equivPP_of_anyPtr (P : Prog) (l : Label) (i : Nat) (s : Stmt)
    (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivPP .anyPtr P (deleteStmt P l i) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:171-175
theorem deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted (K : ZContract)
    (P : Prog) (l : Label) (i : Nat) (s : Stmt) (hs : (P.blk l).stmts[i]? = some s)
    (hz : IsZeroSizeAccess s) (hK : K ≠ .nonnullAligned)
    (ha : ∀ τ, s.accessTy? = some τ → τ.align = 1) :
    EquivPP K P (deleteStmt P l i) := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some s` | `deleteZeroSizeAccess_equivPP_of_zeroPre_reachable`, `deleteZeroSizeAccess_equivPP_of_anyPtr`, `deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted` | identifies `s` as the statement deleted at point `(l, i)` | tight: `deleteStmt_hs_counterexample` | one-block program `pEmit7` (position `(0, 0)` holds `emit 7`) with `s := read (var 0) ⟨0, 1⟩`, for each contract `K ≠ .nonnullAligned` (so `K = .anyPtr` and `K = .aligned`); `hz` holds; `ha` holds and `zeroPre` of `s` is `true` in every state, so `hpre` holds |
| `hz : IsZeroSizeAccess s` | `deleteZeroSizeAccess_equivPP_of_zeroPre_reachable`, `deleteZeroSizeAccess_equivPP_of_anyPtr`, `deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted` | restricts the deleted statement to a zero-size `read`/`write` or a `copy` of `τ.size * n = 0` bytes | tight: `deleteStmt_hz_counterexample` | one-block program `pEmit7` with `s := emit 7`, for every contract `K`; `hs` holds; `emit 7` has no accessed type, so `ha` holds vacuously, and its `zeroPre` is `true`, so `hpre` holds; `K = .anyPtr` and `K = .aligned` (which satisfies `hK`) are included |
| `hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true` | `deleteZeroSizeAccess_equivPP_of_zeroPre_reachable` | the zero-size precondition never fails where the access executes | tight: `deleteZeroSizeAccess_pReadZst4_counterexample` | one-block program `pReadZst4`, contract `aligned`, alignment 4, reachable local `0 = 1`; `hs` and `hz` hold |
| `K = .anyPtr` | `deleteZeroSizeAccess_equivPP_of_anyPtr` | makes `pre₀` true for every pointer | tight: `deleteZeroSizeAccess_pReadZst4_counterexample` | the same instance with contract `aligned` (not `anyPtr`) |
| `hK : K ≠ .nonnullAligned` | `deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted` | the contract permits null | tight: `deleteZeroSizeAccess_pReadZst1_nonnull_counterexample` | one-block program `pReadZst1` (alignment 1), contract `nonnullAligned`, null pointer; `hs`, `hz`, `ha` hold |
| `ha : ∀ τ, s.accessTy? = some τ → τ.align = 1` | `deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted` | every address is aligned | tight: `deleteZeroSizeAccess_pReadZst4_counterexample` | `pReadZst4`, alignment 4, contract `aligned` (which satisfies `hK`); `hs`, `hz` hold |

**Non-vacuity.** `pReadZst1` under `aligned`: all hypotheses of the three theorems hold (for `deleteZeroSizeAccess_equivPP_of_anyPtr`, `hs` and `hz`); the equivalence for that instance is proved independently in `zstRead_align_one_alignedContract_deletion_equivPP`. At alignment 1 under a contract permitting null, `zeroPre` holds in every state (`zeroPre_of_align_one`). (Lean: `deleteZeroSizeAccess_sufficient_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `delete-zero-size-access-equivalence-sufficient-conditions`"; read them before relying on this result.

**Prior art.**

- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs: L18 "* A [null] pointer is *never* valid for reads/writes."; L19 "* For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes."; L61–62 "When a function requires proper alignment, it does so even if the access has size 0, i.e., even if memory is not actually touched."; `copy_nonoverlapping` L479 "* `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.", L483 "* Both `src` and `dst` must be properly aligned."; `read` L1613 "* `src` must be [valid] for reads or `T` must be a ZST.", L1620 "Note that even if `T` has size `0`, the pointer must be properly aligned."; `drop_in_place` L776 "* `to_drop` must be properly aligned, even if `T` has size 0.", L778 "* `to_drop` must be nonnull, even if `T` has size 0."
- Contract history (documentation): rust-lang/rust tag 1.80.0, library/core/src/ptr/mod.rs L18 "* For operations of [size zero][zst], *every* pointer is valid, including the [null] pointer." and `read` L1191 "Note that even if `T` has size `0`, the pointer must be non-null and properly aligned."; library/core/src/intrinsics.rs (1.80.0) `copy_nonoverlapping` L2875–2876 "Note that even if the effectively copied size (`count * size_of::<T>()`) is `0`, the pointers must be non-null and properly aligned." Tag 1.88.0: ptr/mod.rs L18–19 "* For memory accesses of [size zero][zst], *every* pointer is valid, including the [null] pointer.", `read` L1320 "Note that even if `T` has size `0`, the pointer must be properly aligned."; intrinsics/mod.rs `copy_nonoverlapping` L3668–3669 "... is `0`, the pointers must be properly aligned." The definition of validity was changed by rust-lang/rust#152615 ('refactor 'valid for read/write' definition: exclude null', merged 2026-02-28, https://github.com/rust-lang/rust/pull/152615), which states it is an attempt to resolve rust-lang/rust#138351 ('core::ptr::replace implementation is unsound since Rust 1.80', closed 2026-02-28, https://github.com/rust-lang/rust/issues/138351). The parameter `K : ZContract` covers all of these versions; no version is selected.
- Documentation, rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs: `read_unaligned` Safety L1768 "* `src` must be [valid] for reads." and `write_unaligned` Safety L1986 "* `dst` must be [valid] for writes.", with no ZST disjunct and no alignment requirement, unlike `read` L1613 (quoted above) and `write` L1873 "* `dst` must be [valid] for writes or `T` must be a ZST.". Read together with module L18–19 (quoted above), a zero-size `read_unaligned` requires a non-null pointer and no alignment (derived reading of the quoted lines).
- The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L59 "* Producing an [invalid value][invalid-values]. \"Producing\" a value happens any time a value is assigned to or read from a place, passed to a function/primitive operation or returned from a function/primitive operation." and L117 "The Rust compiler assumes that all values produced during program execution are \"valid\", and producing an invalid value is hence immediate UB."; rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs `read` L1618 "* `src` must point to a properly initialized value of type `T`."
- MiniRust (an executable specification of Rust semantics; not the official Rust semantics), minirust/minirust 98043a70de612f6af4eaf1e35cf0b8a6ebea22ce, spec/mem/basic.md L198–203: "// For zero-sized accesses, there is nothing to check." / "// (Provenance monotonicity says that if we allow zero-sized accesses" / "// for `None` provenance we have to allow it for all provenance.)" / "if len.is_zero() {" / "return ret(None);" / "}"; `store` L234–236: "if !align.is_aligned(ptr.addr) {" / "throw_ub!(\"store to a misaligned pointer\");" / "}"; `load` L260–262: "if !align.is_aligned(ptr.addr) {" / "throw_ub!(\"load from a misaligned pointer\");" / "}". In that model a zero-sized load or store is UB through a misaligned pointer and is not rejected by `check_ptr` for any address, which matches the toy shape `aligned` (derived reading of the quoted lines).
- N. Popov, A. Ballman, 'Allow zero length operations on null pointers', ISO/IEC JTC1/SC22/WG14 N3322, 2024-08-28, https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3322.pdf, abstract: "Proposes allowing null + 0, null - null and passing null to certain C standard library functions if the length argument is also zero. This removes a class of undefined behavior and brings the specification more in line with C++." (a proposal for C2y; its adoption status is not recorded here).

**Design question.** Deleting a zero-size access or a zero-count copy removes code whose sole effect is a possible UB event (the precondition `pre₀` of the access). A verified compiler must know when the deletion is an equivalence (UB-preserving) and when it is merely a forward refinement (UB-erasing), for each documented zero-size contract.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's zero-size access, whose UB precondition is `pre₀` of a `ZContract` shape, is read as a model of the zero-size requirements quoted under Prior art (the `core::ptr` documentation and, where cited, the MiniRust load/store checks), which state alignment and, depending on the function and version, non-null requirements for accesses that touch no memory. Which shape matches a given function and version is a reading of the quoted text, made explicitly in the prior-art items marked "derived reading of the quoted lines". No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `delete-zero-size-access-equivalence-despite-pre-failure`

**Plain claim.** In the program `pTwoZstReads` (two identical zero-size reads through local 0 at alignment 4, then `halt`) under the `aligned` contract, `pre₀` of the first read fails at a reachable state (local 0 = 1), the target continuation from that state reaches UB with empty trace, and deleting the first read is nevertheless a prefix-preserving equivalence.

**Kind / tier / depth.** counterexample / T0 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:261-266
theorem deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure :
    ReachableAt .aligned pTwoZstReads 0 0 (mkState [1]) ∧
      (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [1]) = false ∧
      GoesWrongFrom .aligned (deleteStmt pTwoZstReads 0 0)
        ((deleteStmt pTwoZstReads 0 0).at 0 0 (mkState [1])) [] ∧
      EquivPP .aligned pTwoZstReads (deleteStmt pTwoZstReads 0 0) := by …
```

**Hypothesis ledger.** No hypotheses: a concrete instance.

**Non-vacuity.** Concrete instance (no hypotheses).

**Positive control.** Without the second read (`pReadZst4`), deleting the read is not an equivalence. (Lean: `zstRead_misaligned_deletion_erases_ub`)

**Non-claims.** Listed under Boundaries, "Non-claims: `delete-zero-size-access-equivalence-despite-pre-failure`"; read them before relying on this result.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.

**Design question.** Deleting a zero-size access or a zero-count copy removes code whose sole effect is a possible UB event (the precondition `pre₀` of the access). A verified compiler must know when the deletion is an equivalence (UB-preserving) and when it is merely a forward refinement (UB-erasing), for each documented zero-size contract.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — this card's statement concerns one concrete program, `pTwoZstReads`, under the single contract shape `aligned`, where each of its two zero-size reads (alignment 4) is UB exactly when its address is not a multiple of 4. It is read as an instance in which deleting a zero-size access whose alignment requirement fails is nevertheless UB-preserving, because the identical access that follows fails in the same state with nothing emitted in between. This card's Prior art quotes sources for the behaviour and refinement notions only (Leroy; CompCert's `behavior_improves`); reading the shape `aligned` as a documented zero-size requirement relies on the `core::ptr` documentation and the MiniRust `load`/`store` checks quoted under `delete-zero-size-access-refines`. No model–system relation is proved; the theorem of this card neither establishes nor refutes the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `zero-size-deletion-erases-ub-instances`

**Plain claim.** Each of four concrete pairs has UB in the source on a stated input, terminates in the target on that input, is a prefix-preserving refinement and is not a whole-trace equivalence: deleting a zero-size read at alignment 4 through address 1 (contract `aligned`); deleting `copy src dst ⟨4, 4⟩ 0` with `src = 1`, `dst = 8` (contract `aligned`); deleting a zero-size read at alignment 1 through address 0 (contract `nonnullAligned`); and lowering that zero-count copy to the element loop `copyLoopProg 0 1 2 ⟨4, 4⟩ 0`. The loop lowering also overwrites its counter local 2, so on the aligned input with locals `8, 8, 42` the source satisfies `wp` for "local 2 is 42" and the loop does not.

**Kind / tier / depth.** counterexample / T1 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:313-317
theorem zstRead_misaligned_deletion_erases_ub :
    HasBeh .aligned pReadZst4 (mkState [1]) (.wrong []) ∧
      HasBeh .aligned (deleteStmt pReadZst4 0 0) (mkState [1]) (.term []) ∧
      RefinesPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) ∧
      ¬ EquivWT .aligned pReadZst4 (deleteStmt pReadZst4 0 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:331-335
theorem zeroCountCopy_misalignedSrc_deletion_erases_ub :
    HasBeh .aligned pCopy0 (mkState [1, 8]) (.wrong []) ∧
      HasBeh .aligned (deleteStmt pCopy0 0 0) (mkState [1, 8]) (.term []) ∧
      RefinesPP .aligned pCopy0 (deleteStmt pCopy0 0 0) ∧
      ¬ EquivWT .aligned pCopy0 (deleteStmt pCopy0 0 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:348-352
theorem zstRead_null_nonnullContract_deletion_erases_ub :
    HasBeh .nonnullAligned pReadZst1 (mkState [0]) (.wrong []) ∧
      HasBeh .nonnullAligned (deleteStmt pReadZst1 0 0) (mkState [0]) (.term []) ∧
      RefinesPP .nonnullAligned pReadZst1 (deleteStmt pReadZst1 0 0) ∧
      ¬ EquivWT .nonnullAligned pReadZst1 (deleteStmt pReadZst1 0 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:440-444
theorem copyLoopLowering_zeroCount_erases_ub :
    HasBeh .aligned pCopy0 (mkState [1, 8]) (.wrong []) ∧
      HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (mkState [1, 8]) (.term []) ∧
      RefinesPP .aligned pCopy0 (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) ∧
      ¬ EquivWT .aligned pCopy0 (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:463-466
theorem copyLoopLowering_zeroCount_clobbers_counter :
    wp .aligned pCopy0 (fun _ s => s.locals 2 = 42) (mkState [8, 8, 42]) ∧
      ¬ wp .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (fun _ s => s.locals 2 = 42)
        (mkState [8, 8, 42]) := by …
```

**Hypothesis ledger.** No hypotheses: concrete instances.

**Non-vacuity.** Concrete instances (no hypotheses).

**Positive control.** The same deletion at alignment 1 under `aligned` is an equivalence. (Lean: `zstRead_align_one_alignedContract_deletion_equivPP`)

**Non-claims.** Listed under Boundaries, "Non-claims: `zero-size-deletion-erases-ub-instances`"; read them before relying on this result.

**Prior art.**

- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs: L18 "* A [null] pointer is *never* valid for reads/writes."; L19 "* For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes."; L61–62 "When a function requires proper alignment, it does so even if the access has size 0, i.e., even if memory is not actually touched."; `copy_nonoverlapping` L479 "* `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.", L483 "* Both `src` and `dst` must be properly aligned."; `read` L1613 "* `src` must be [valid] for reads or `T` must be a ZST.", L1620 "Note that even if `T` has size `0`, the pointer must be properly aligned."; `drop_in_place` L776 "* `to_drop` must be properly aligned, even if `T` has size 0.", L778 "* `to_drop` must be nonnull, even if `T` has size 0."
- Contract history (documentation): rust-lang/rust tag 1.80.0, library/core/src/ptr/mod.rs L18 "* For operations of [size zero][zst], *every* pointer is valid, including the [null] pointer." and `read` L1191 "Note that even if `T` has size `0`, the pointer must be non-null and properly aligned."; library/core/src/intrinsics.rs (1.80.0) `copy_nonoverlapping` L2875–2876 "Note that even if the effectively copied size (`count * size_of::<T>()`) is `0`, the pointers must be non-null and properly aligned." Tag 1.88.0: ptr/mod.rs L18–19 "* For memory accesses of [size zero][zst], *every* pointer is valid, including the [null] pointer.", `read` L1320 "Note that even if `T` has size `0`, the pointer must be properly aligned."; intrinsics/mod.rs `copy_nonoverlapping` L3668–3669 "... is `0`, the pointers must be properly aligned." The definition of validity was changed by rust-lang/rust#152615 ('refactor 'valid for read/write' definition: exclude null', merged 2026-02-28, https://github.com/rust-lang/rust/pull/152615), which states it is an attempt to resolve rust-lang/rust#138351 ('core::ptr::replace implementation is unsound since Rust 1.80', closed 2026-02-28, https://github.com/rust-lang/rust/issues/138351). The parameter `K : ZContract` covers all of these versions; no version is selected.
- The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L19 "* Accessing (loading from or storing to) a place that is [dangling] or [based on a misaligned pointer]." and L110 "> This also implies that if the [size is 0][zero-sized], then the pointer is trivially never \"dangling\" (even if it is a null pointer)."
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.

**Design question.** Deleting a zero-size access or a zero-count copy removes code whose sole effect is a possible UB event (the precondition `pre₀` of the access). A verified compiler must know when the deletion is an equivalence (UB-preserving) and when it is merely a forward refinement (UB-erasing), for each documented zero-size contract.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the instances are read against the zero-size requirements quoted under this card's Prior art. The misaligned zero-size read and the misaligned zero-count `copy` (shape `aligned`) are read as violating alignment requirements that apply even when no memory is touched: `core::ptr` L61–62, `read` L1620 and `copy_nonoverlapping` L483 at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, and the Rust Reference's rule on places based on a misaligned pointer (L19), read together with its statement that a zero-size place is never dangling, even if null (L110). The null zero-size read under the shape `nonnullAligned` is read as violating the non-null requirement in the tag 1.80.0 wording of `read` (L1191) and of `copy_nonoverlapping` (`intrinsics.rs` L2875–2876). These are derived readings of the quoted lines, not proved facts. The element-loop lowering `copyLoopProg` is a toy pass; no source is quoted for it. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `insert-zero-size-access-exact-condition`

**Plain claim.** For every zero-size contract `K`, program `P`, point `(l, i)` and zero-size access `s`: inserting `s` before the `i`-th statement of block `l` is a prefix-preserving refinement iff, for every reachable state at `(l, i)` in which `pre₀` of `s` fails, the source run from `(l, i)` reaches UB with empty trace; and it is a whole-trace refinement iff, for every such state, that source run reaches UB after some trace.

**Kind / tier / depth.** characterization / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:484-488
theorem insertZeroSizeAccess_refinesPP_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hz : IsZeroSizeAccess s) :
    RefinesPP K P (insertStmt P l i s) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        GoesWrongFrom K P (P.at l i st) [] := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:495-499
theorem insertZeroSizeAccess_refinesWT_iff (K : ZContract) (P : Prog) (l : Label) (i : Nat)
    (s : Stmt) (hz : IsZeroSizeAccess s) :
    RefinesWT K P (insertStmt P l i s) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        ∃ t, GoesWrongFrom K P (P.at l i st) t := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hz : IsZeroSizeAccess s` | `insertZeroSizeAccess_refinesPP_iff`, `insertZeroSizeAccess_refinesWT_iff` | restricts the inserted statement to a zero-size access | tight: `insertEmit_counterexample` | inserting `emit 1` into the one-block program `pHalt`, for every contract `K` (left-hand sides false, right-hand sides vacuously true) |

**Non-vacuity.** Inserting a zero-size read at alignment 4 in front of the identical read of `pReadZst4` under `aligned`: `hz` holds, `pre₀` fails at a reachable state, the source run from the insertion point reaches UB with empty trace, and the insertion is proved to be a prefix-preserving refinement; `insertZstRead_misaligned_not_refinesWT` is an instance in which both sides are false. (Lean: `insertZstRead_before_failing_read_refinesPP`)

**Non-claims.** Listed under Boundaries, "Non-claims: `insert-zero-size-access-exact-condition`"; read them before relying on this result.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65–79, doi:10.1145/3453483.3454030 (refinement in which source UB permits any target behaviour).
- J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, 'Taming undefined behavior in LLVM', PLDI 2017, pp. 633–647, doi:10.1145/3062341.3062343, §2.2: "If integer overflow triggered immediate undefined behavior, this transformation would be illegal because it makes the domain of definedness smaller: the code would execute UB when x was INT_MAX, even if n was zero." (hoisting an operation with immediate UB can introduce UB; the paper's remedy, deferred UB, is not modelled in the toy).

**Design question.** Materializing or hoisting a zero-size access adds a possible UB event; when is that a refinement of the source?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — inserting a zero-size access at a program point is read as materializing or hoisting an operation whose only effect in the toy is a possible immediate UB event; Lee et al. (quoted under Prior art) raise the same concern for hoisting an integer operation with immediate UB, not a memory access. The characterization holds for each of the three contract shapes; reading a shape as the documented zero-size requirement of a particular Rust function and version relies on the `core::ptr` documentation and the MiniRust `load`/`store` checks quoted under `delete-zero-size-access-refines` and `delete-zero-size-access-equivalence-sufficient-conditions`, not on this card's Prior art. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `insert-zero-size-access-sufficient-condition`

**Plain claim.** For every zero-size contract `K`, program `P`, point `(l, i)` and zero-size access `s`: if `pre₀` of `s` holds on every reachable state at `(l, i)`, then inserting `s` there is a prefix-preserving equivalence (in particular a refinement).

**Kind / tier / depth.** theorem / T1 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:505-508
theorem insertZeroSizeAccess_equivPP_of_zeroPre_reachable (K : ZContract) (P : Prog)
    (l : Label) (i : Nat) (s : Stmt) (hz : IsZeroSizeAccess s)
    (hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true) :
    EquivPP K P (insertStmt P l i s) := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hz : IsZeroSizeAccess s` | `insertZeroSizeAccess_equivPP_of_zeroPre_reachable` | restricts the inserted statement to a zero-size access | tight: `insertEmit_counterexample` | inserting `emit 1` into `pHalt`, every contract; `hpre` holds (its `zeroPre` is `true`) |
| `hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true` | `insertZeroSizeAccess_equivPP_of_zeroPre_reachable` | the inserted access never fails where it executes | tight: `insertZeroSizeAccess_hpre_counterexample` | inserting a zero-size read at alignment 4 into `pHalt`, contract `aligned`, reachable local `0 = 1`; `hz` holds |

**Non-vacuity.** Inserting a zero-size read into `pHalt` under `anyPtr`: `hz` holds and `zeroPre` is `true` in every state. (Lean: `insertZeroSizeAccess_anyPtr_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `insert-zero-size-access-sufficient-condition`"; read them before relying on this result.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, 'Taming undefined behavior in LLVM', PLDI 2017, pp. 633–647, doi:10.1145/3062341.3062343, §2.2: "If integer overflow triggered immediate undefined behavior, this transformation would be illegal because it makes the domain of definedness smaller: the code would execute UB when x was INT_MAX, even if n was zero." (hoisting an operation with immediate UB can introduce UB; the paper's remedy, deferred UB, is not modelled in the toy).

**Design question.** Materializing or hoisting a zero-size access adds a possible UB event; when is that a refinement of the source?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — this card's statement says that inserting a zero-size access whose `pre₀` holds at every reachable state of the insertion point adds no UB event; it is read as hoisting or materializing a zero-size access whose zero-size requirement is met wherever it executes, the safe case of the hoisting concern raised by Lee et al. (quoted under Prior art) for an integer operation with immediate UB, not a memory access. The statement holds for each of the three contract shapes; reading a shape as the documented zero-size requirement of a particular Rust function and version relies on the `core::ptr` documentation and the MiniRust `load`/`store` checks quoted under `delete-zero-size-access-refines` and `delete-zero-size-access-equivalence-sufficient-conditions`, not on this card's Prior art. No model–system relation is proved; the theorem of this card neither establishes nor refutes the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `introducing-zero-size-access-introduces-ub`

**Plain claim.** Under the `aligned` contract, inserting a zero-size read at alignment 4 through local 0 into `halt` is not a whole-trace refinement (on local 0 = 1 the source halts and the target reaches UB), and hoisting the zero-size read of `pBranchRead` above its branch is not a whole-trace refinement (on locals 0 ↦ 5, 1 ↦ 1).

**Kind / tier / depth.** counterexample / T0 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:562-565
theorem insertZstRead_misaligned_not_refinesWT :
    HasBeh .aligned pHalt (mkState [1]) (.term []) ∧
      HasBeh .aligned (insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩)) (mkState [1]) (.wrong []) ∧
      ¬ RefinesWT .aligned pHalt (insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩)) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:604-607
theorem hoistZstRead_out_of_branch_not_refinesWT :
    HasBeh .aligned pBranchRead (mkState [5, 1]) (.term []) ∧
      HasBeh .aligned pBranchReadHoisted (mkState [5, 1]) (.wrong []) ∧
      ¬ RefinesWT .aligned pBranchRead pBranchReadHoisted := by …
```

**Hypothesis ledger.** No hypotheses: concrete instances.

**Non-vacuity.** Concrete instances (no hypotheses).

**Positive control.** Hoisting the same read under `anyPtr` is a prefix-preserving equivalence; insertion where `pre₀` holds on every reachable state is an equivalence. (Lean: `hoistZstRead_anyPtr_equivPP`, `insertZeroSizeAccess_equivPP_of_zeroPre_reachable`)

**Non-claims.** Listed under Boundaries, "Non-claims: `introducing-zero-size-access-introduces-ub`"; read them before relying on this result.

**Prior art.**

- J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, 'Taming undefined behavior in LLVM', PLDI 2017, pp. 633–647, doi:10.1145/3062341.3062343, §2.2: "If integer overflow triggered immediate undefined behavior, this transformation would be illegal because it makes the domain of definedness smaller: the code would execute UB when x was INT_MAX, even if n was zero." (hoisting an operation with immediate UB can introduce UB; the paper's remedy, deferred UB, is not modelled in the toy).
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.

**Design question.** Materializing or hoisting a zero-size access adds a possible UB event; when is that a refinement of the source?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the two instances, inserting a misaligned zero-size read into `halt` and hoisting the zero-size read of `pBranchRead` above its branch, are read as zero-size access counterparts of the example of Lee et al. (quoted under Prior art), in which hoisting an operation with immediate UB makes it execute where the original code would not (there, a loop that runs zero times); that example concerns integer overflow, not memory accesses. Both instances use the single shape `aligned`; reading `aligned` as a documented zero-size requirement relies on the `core::ptr` documentation and the MiniRust `load`/`store` checks quoted under `delete-zero-size-access-refines`, not on this card's Prior art. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `ub-check-of-output-incomplete`

**Plain claim.** There is a source program (`pReadZst4`, contract `aligned`) and a pass (deleting its zero-size read) such that the pass is a prefix-preserving refinement and every exact UB checker accepts the output as `UBFree`, yet the source is not `UBFree`; exact checkers exist (noncomputably, `exactUBChecker_exists`).

**Kind / tier / depth.** counterexample / T0 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:647-650
theorem ubCheck_of_output_misses_source_ub :
    RefinesPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) ∧
      ∀ chk, ExactUBChecker .aligned chk →
        chk (deleteStmt pReadZst4 0 0) = true ∧ ¬ UBFree .aligned pReadZst4 := by …
```

**Hypothesis ledger.** No hypotheses: a concrete instance, universally quantified over exact checkers.

**Non-vacuity.** `exactUBChecker_exists` shows the universally quantified checker is not vacuous. (Lean: `exactUBChecker_exists`)

**Positive control.** When the source whole-trace-refines the output (for example an equivalence), checking the output is complete. (Lean: `ubFree_positive_control_instance`, `ubFree_src_of_ubFree_output_of_revChainWT`)

**Non-claims.** Listed under Boundaries, "Non-claims: `ub-check-of-output-incomplete`"; read them before relying on this result.

**Prior art.**

- rustc option description, rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_session/src/options.rs L2654–2656: `mir_preserve_ub` "keep place mention statements and reads in trivial SwitchInt terminators, which are interpreted e.g., by miri; implies -Zmir-opt-level=0 (default: no)". rust-lang/miri 7e679961edcfe2c526f19153bb8b03de346efa5c, src/lib.rs L200–205: `MIRI_DEFAULT_ARGS` contains "-Zmir-preserve-ub" and "-Zmir-opt-level=0". rust-lang/miri#5565 ('Miri vs `#[optimize]`', closed 2026-11-17, labels include `I-misses-UB`, https://github.com/rust-lang/miri/issues/5565) reports that `#[optimize(speed)]` leads to a function being optimized even when run in Miri and proposes `-Zmir-opt-level=0` as the signal that no optimizations at all should be applied.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- V. D'Silva, M. Payer, D. Song, 'The correctness-security gap in compiler optimization', 2015 IEEE Security and Privacy Workshops, pp. 73–87, doi:10.1109/SPW.2015.33 (bibliographic data verified; the text was not consulted here, and no claim of this card relies on it).

**Design question.** Can a UB checker be run on optimized code and still certify the source? Checking the output of a UB-erasing pipeline is incomplete for source UB.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — `UBFree` and `ExactUBChecker` idealize a dynamic UB checker applied to a program after transformation passes; the quoted rustc option `mir_preserve_ub` and Miri's default arguments (`-Zmir-preserve-ub`, `-Zmir-opt-level=0`) document the configuration in which Miri limits MIR optimization before interpreting a program (derived reading of the quoted lines). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `ub-check-of-output-complete-under-reverse-refinement`

**Plain claim.** For every zero-size contract `K`: for all programs `src`, `tgt`, if `src` whole-trace-refines `tgt` (`RefinesWT K tgt src`) and `tgt` is `UBFree`, then `src` is `UBFree`; for every program `P` and list `Qs` forming a pipeline in which each pass's input whole-trace-refines its output (`RevChainWT K P Qs`, including the empty pipeline), if the last program is `UBFree` then `P` is `UBFree`; and if `EquivPP K src tgt` and `tgt` is `UBFree`, then `src` is `UBFree`.

**Kind / tier / depth.** theorem / T0 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/ZeroSize.lean:675-676
theorem ubFree_src_of_ubFree_tgt_of_refinesWT_rev (K : ZContract) (src tgt : Prog)
    (hrev : RefinesWT K tgt src) (htgt : UBFree K tgt) : UBFree K src := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:707-709
theorem ubFree_src_of_ubFree_output_of_revChainWT (K : ZContract) :
    ∀ (P : Prog) (Qs : List Prog), RevChainWT K P Qs →
      UBFree K ((P :: Qs).getLast (List.cons_ne_nil _ _)) → UBFree K P := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:726-727
theorem ubFree_src_of_ubFree_tgt_of_equivPP (K : ZContract) (src tgt : Prog)
    (h : EquivPP K src tgt) (htgt : UBFree K tgt) : UBFree K src := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:687-689
def RevChainWT (K : ZContract) : Prog → List Prog → Prop
  | _, [] => True
  | P, Q :: Qs => RefinesWT K Q P ∧ RevChainWT K Q Qs
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hrev : RefinesWT K tgt src` | `ubFree_src_of_ubFree_tgt_of_refinesWT_rev` | the source whole-trace-refines the output | tight: `ubCheck_pReadZst4_hypotheses_counterexample` | `pReadZst4` and its UB-erasing deletion, contract `aligned`; the output is `UBFree` |
| `htgt : UBFree K tgt` | `ubFree_src_of_ubFree_tgt_of_refinesWT_rev`, `ubFree_src_of_ubFree_tgt_of_equivPP` | the checked output has no UB | tight: `ubFree_output_hypothesis_counterexample` | source and output both `pUnreach`, every contract (reverse refinement and equivalence by reflexivity) |
| `RevChainWT K P Qs` | `ubFree_src_of_ubFree_output_of_revChainWT` | every pass's input whole-trace-refines its output | tight: `ubCheck_pReadZst4_hypotheses_counterexample` | one-pass pipeline `pReadZst4 → deleteStmt pReadZst4 0 0`, contract `aligned`; the last program is `UBFree` |
| `UBFree K ((P :: Qs).getLast _)` | `ubFree_src_of_ubFree_output_of_revChainWT` | the last program of the pipeline has no UB | tight: `ubFree_output_hypothesis_counterexample` | empty pipeline from `pUnreach`, every contract |
| `h : EquivPP K src tgt` | `ubFree_src_of_ubFree_tgt_of_equivPP` | the pass is a prefix-preserving equivalence | tight: `ubCheck_pReadZst4_hypotheses_counterexample` | `pReadZst4` and its UB-erasing deletion, contract `aligned`; the output is `UBFree` |

**Non-vacuity.** The `aligned`-contract deletion of the alignment-1 read of `pReadZst1`: all hypotheses of the three theorems hold. (Lean: `ubFree_src_of_ubFree_tgt_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `ub-check-of-output-complete-under-reverse-refinement`"; read them before relying on this result.

**Prior art.**

- rustc option description, rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_session/src/options.rs L2654–2656: `mir_preserve_ub` "keep place mention statements and reads in trivial SwitchInt terminators, which are interpreted e.g., by miri; implies -Zmir-opt-level=0 (default: no)". rust-lang/miri 7e679961edcfe2c526f19153bb8b03de346efa5c, src/lib.rs L200–205: `MIRI_DEFAULT_ARGS` contains "-Zmir-preserve-ub" and "-Zmir-opt-level=0". rust-lang/miri#5565 ('Miri vs `#[optimize]`', closed 2026-11-17, labels include `I-misses-UB`, https://github.com/rust-lang/miri/issues/5565) reports that `#[optimize(speed)]` leads to a function being optimized even when run in Miri and proposes `-Zmir-opt-level=0` as the signal that no optimizations at all should be applied.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.

**Design question.** Positive control for `ub-check-of-output-incomplete`: which passes may run before a UB checker without losing completeness.

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — `UBFree` and `ExactUBChecker` idealize a dynamic UB checker applied to a program after transformation passes; the quoted rustc option `mir_preserve_ub` and Miri's default arguments (`-Zmir-preserve-ub`, `-Zmir-opt-level=0`) document the configuration in which Miri limits MIR optimization before interpreting a program (derived reading of the quoted lines). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-arm-with-assume-equivalence`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and the label selected for `v` is an unreachable block (no statements, `unreachable` terminator), then removing every arm with value `v` and appending the UB-on-false `assume (x ≠ v)` to block `l` is a prefix-preserving equivalence, hence (by `equivWT_of_equivPP`) a whole-trace equivalence, and for every postcondition `Q` on trace and final state and every input, the target's demonic total-correctness `wp` holds iff the source's does.

**Kind / tier / depth.** theorem / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:20-24
theorem pruneArmAssume_equivPP (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivPP K P (pruneArmAssume P l v) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:29-33
theorem pruneArmAssume_equivWT (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivWT K P (pruneArmAssume P l v) := …
```

```lean
-- Toy/ZstAssume/Switch.lean:39-44
theorem pruneArmAssume_wp_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v))
    (Q : List Int → State → Prop) (σ : State) :
    wp K (pruneArmAssume P l v) Q σ ↔ wp K P Q σ := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hterm : (P.blk l).term = .switch x arms ow` | `pruneArmAssume_equivPP`, `pruneArmAssume_equivWT`, `pruneArmAssume_wp_iff` | names the switch whose arms are pruned | tight: `pruneArm_hterm_counterexample` | three-block program `pSwLive`, stated arms `[(5, 3)]` (out-of-range label, so `hU` holds), actual arm for 5 live; every contract |
| `hU : IsUnreachableBlock P (selectTarget arms ow v)` | `pruneArmAssume_equivPP`, `pruneArmAssume_equivWT`, `pruneArmAssume_wp_iff` | the pruned arm's target is UB with no event | tight: `pruneArm_hU_counterexample`, `pruneArmAssume_emit_before_unreachable_not_refinesPP` | `pSwLive` (live arm; `hterm` holds; all three conclusions fail), every contract; for the prefix-preserving refinement also `pSwEmitUnreach`, whose arm emits before `unreachable` (whole-trace refinement still holds) |

**Non-vacuity.** `pSw` (arm 5 → unreachable block 1, otherwise halt) satisfies both hypotheses; equivalence and `wp` equality for it are proved independently in `pruneArmAssume_pSw_equivPP_and_wp`. (Lean: `pSw_hyps`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-arm-with-assume-equivalence`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/hint.rs: `unreachable_unchecked` L16 "Reaching this function is *Undefined Behavior*."; `assert_unchecked` L146 "`cond` must be `true`. It is immediate UB to call this with `false`."
- LLVM Language Reference Manual, https://llvm.org/docs/LangRef.html (rendered page retrieved 2026-11-21), section on assume operand bundles: "Just like for the argument of llvm.assume, if any of the provided guarantees are violated at runtime the behavior is undefined." The `unreachable` instruction's semantics paragraph was not retrieved verbatim and is not quoted. The page is unpinned: no llvm/llvm-project revision is recorded for this quote.
- M. Barnett, K. R. M. Leino, 'Weakest-precondition of unstructured programs', PASTE 2005, pp. 82–87, doi:10.1145/1108792.1108813, §2: "wp(assert P, Q) = P ∧ Q" and "wp(assume P, Q) = P ⇒ Q", and §1: a trace "ends in error if an assert statement evaluates to false, and ends in infeasibility if an assume statement evaluates to false". The toy's UB-on-false `assume` follows the first rule (`wpFrom_assume`); the second, miraculous rule is not modelled.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`), the quoted `core::hint` documentation and the quoted LLVM Language Reference sentence on `llvm.assume`. The toy rule for `wp` of `assume` is the `assert` rule quoted from Barnett and Leino. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-otherwise-with-assume-equivalence`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, variable `x`, value `v` and labels `b`, `ow`: if block `l` ends in the single-arm switch `switch x [(v, b)] ow` and `ow` is an unreachable block, then replacing the switch by the UB-on-false `assume (x = v)` followed by `goto b` is a prefix-preserving equivalence, and for every postcondition and input the target's demonic total-correctness `wp` holds iff the source's does.

**Kind / tier / depth.** theorem / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:50-53
theorem pruneOtherwiseAssume_equivPP (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (v : Int) (b ow : Label) (hterm : (P.blk l).term = .switch x [(v, b)] ow)
    (hU : IsUnreachableBlock P ow) :
    EquivPP K P (pruneOtherwiseAssume P l) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:58-61
theorem pruneOtherwiseAssume_wp_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (v : Int) (b ow : Label) (hterm : (P.blk l).term = .switch x [(v, b)] ow)
    (hU : IsUnreachableBlock P ow) (Q : List Int → State → Prop) (σ : State) :
    wp K (pruneOtherwiseAssume P l) Q σ ↔ wp K P Q σ := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hterm : (P.blk l).term = .switch x [(v, b)] ow` | `pruneOtherwiseAssume_equivPP`, `pruneOtherwiseAssume_wp_iff` | names the single-arm switch | tight: `pruneOtherwiseAssume_live_otherwise_not_refinesWT` | `pSw` with stated `otherwise` label 3 (out of range, so `hU` holds) while the actual one, 2, halts; every contract |
| `hU : IsUnreachableBlock P ow` | `pruneOtherwiseAssume_equivPP`, `pruneOtherwiseAssume_wp_iff` | the `otherwise` target is UB with no event | tight: `pruneOtherwiseAssume_live_otherwise_not_refinesWT` | `pSw` (`hterm` holds), whose `otherwise` block halts; UB introduced on local 0 = 0; every contract |

**Non-vacuity.** `pSwOne` satisfies both hypotheses; the equivalence for it is proved independently in `pruneOtherwiseAssume_pSwOne_equivPP`. (Lean: `pSwOne_hyps`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-otherwise-with-assume-equivalence`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- Documented design (source), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L120–122: "// We remove this target from the switch, so record the inequality using `Assume`." / "if is_unreachable && !otherwise_unreachable {" / "add_assumption(BinOp::Ne, value);" (no inequality is recorded when the `otherwise` target is itself unreachable); L136–140: "(2, true) => {" / "// All targets are unreachable except one. Record the equality, and make it a goto." / "let (value, target) = new_targets.iter().next().unwrap();" / "add_assumption(BinOp::Eq, value);" / "TerminatorKind::Goto { target }"; L19–20: "// Enable only under -Zmir-opt-level=2 as this can make programs less debuggable." / "PassPolicy::optimization(sess.mir_opt_level() >= 2)".
- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/hint.rs: `unreachable_unchecked` L16 "Reaching this function is *Undefined Behavior*."; `assert_unchecked` L146 "`cond` must be `true`. It is immediate UB to call this with `false`."
- M. Barnett, K. R. M. Leino, 'Weakest-precondition of unstructured programs', PASTE 2005, pp. 82–87, doi:10.1145/1108792.1108813, §2: "wp(assert P, Q) = P ∧ Q" and "wp(assume P, Q) = P ⇒ Q", and §1: a trace "ends in error if an assert statement evaluates to false, and ends in infeasibility if an assume statement evaluates to false". The toy's UB-on-false `assume` follows the first rule (`wpFrom_assume`); the second, miraculous rule is not modelled.

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`) and the quoted `core::hint` documentation. The toy rule for `wp` of `assume` is the `assert` rule quoted from Barnett and Leino. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-arm-without-assume-refines`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and the label selected for `v` is an unreachable block, then removing every arm with value `v` without an `assume` (so that `x = v` goes to `ow`) is a prefix-preserving refinement, and for every postcondition `Q` and input, the source's demonic total-correctness `wp` implies the target's.

**Kind / tier / depth.** theorem / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:348-352
theorem pruneArm_refinesPP (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    RefinesPP K P (pruneArm P l v) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:409-414
theorem pruneArm_wp_of_wp_src (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v))
    (Q : List Int → State → Prop) (σ : State) :
    wp K P Q σ → wp K (pruneArm P l v) Q σ := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hterm : (P.blk l).term = .switch x arms ow` | `pruneArm_refinesPP`, `pruneArm_wp_of_wp_src` | names the switch whose arms are pruned | tight: `pruneArm_hterm_counterexample` | `pSwLive`, stated arms `[(5, 3)]` (so `hU` holds), actual arm for 5 live; every contract |
| `hU : IsUnreachableBlock P (selectTarget arms ow v)` | `pruneArm_refinesPP`, `pruneArm_wp_of_wp_src` | the pruned arm's target is UB with no event | tight: `pruneArm_hU_counterexample` | `pSwLive` (`hterm` holds, arm for 5 live), every contract; the trace postcondition `t = [1]` refutes the `wp` transfer |

**Non-vacuity.** `pSw` satisfies both hypotheses; the refinement for it is proved independently in `pruneArm_pSw_refinesPP_not_equivWT`. (Lean: `pSw_hyps`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-arm-without-assume-refines`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- M. Barnett, K. R. M. Leino, 'Weakest-precondition of unstructured programs', PASTE 2005, pp. 82–87, doi:10.1145/1108792.1108813, §2: "wp(assert P, Q) = P ∧ Q" and "wp(assume P, Q) = P ⇒ Q", and §1: a trace "ends in error if an assert statement evaluates to false, and ends in infeasibility if an assume statement evaluates to false". The toy's UB-on-false `assume` follows the first rule (`wpFrom_assume`); the second, miraculous rule is not modelled.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`). The toy rule for `wp` of `assume` is the `assert` rule quoted from Barnett and Leino. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-arm-without-assume-exact-condition`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and the label selected for `v` is an unreachable block, then pruning the arms with value `v` without `assume` is a prefix-preserving equivalence iff, for every reachable state at the switch with `x = v`, the target run from the entry of `ow` reaches UB with empty trace; and it is a whole-trace equivalence iff, for every such state, that run reaches UB after some trace.

**Kind / tier / depth.** characterization / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:359-365
theorem pruneArm_equivPP_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivPP K P (pruneArm P l v) ↔
      ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x = v →
        GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) [] := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:372-378
theorem pruneArm_equivWT_iff (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivWT K P (pruneArm P l v) ↔
      ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x = v →
        ∃ t, GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) t := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hterm : (P.blk l).term = .switch x arms ow` | `pruneArm_equivPP_iff`, `pruneArm_equivWT_iff` | names the switch whose arms are pruned | tight: `pruneArm_iff_counterexample` | `pSwLiveUnreachOw` with stated arms `[(5, 3)]` (so `hU` holds): right-hand sides hold, equivalences fail; every contract |
| `hU : IsUnreachableBlock P (selectTarget arms ow v)` | `pruneArm_equivPP_iff`, `pruneArm_equivWT_iff` | the pruned arm's target is UB with no event | tight: `pruneArm_iff_counterexample` | `pSwLiveUnreachOw` (`hterm` holds; arm for 5 live, `otherwise` unreachable): right-hand sides hold, equivalences fail; every contract |

**Non-vacuity.** `pSwAssumeOw` satisfies both hypotheses; there the value 5 is reachable at the switch, `otherwise` is not an unreachable block, the redirected run reaches UB with empty trace, and the equivalence is proved independently (`pruneArm_pSwAssumeOw_equivPP`); `pSw` is an instance in which both sides are false. (Lean: `pSwAssumeOw_hyps`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-arm-without-assume-exact-condition`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-arm-without-assume-unreachable-otherwise`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow`, the label selected for `v` is an unreachable block and `ow` is an unreachable block, then pruning the arms with value `v` without `assume` is a prefix-preserving equivalence.

**Kind / tier / depth.** theorem / T1 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:384-388
theorem pruneArm_equivPP_of_otherwise_unreachable (K : ZContract) (P : Prog) (l : Label)
    (x : Var) (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) (hOw : IsUnreachableBlock P ow) :
    EquivPP K P (pruneArm P l v) := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hterm : (P.blk l).term = .switch x arms ow` | `pruneArm_equivPP_of_otherwise_unreachable` | names the switch whose arms are pruned | tight: `pruneArm_iff_counterexample` | `pSwLiveUnreachOw` with stated arms `[(5, 3)]` (`hU` and `hOw` hold); every contract |
| `hU : IsUnreachableBlock P (selectTarget arms ow v)` | `pruneArm_equivPP_of_otherwise_unreachable` | the pruned arm's target is UB with no event | tight: `pruneArm_iff_counterexample` | `pSwLiveUnreachOw` (`hterm`, `hOw` hold; arm for 5 live); every contract |
| `hOw : IsUnreachableBlock P ow` | `pruneArm_equivPP_of_otherwise_unreachable` | redirected values reach UB with no event | tight: `pruneArm_pSw_hyps_counterexample` | `pSw` (`hterm`, `hU` hold), whose `otherwise` block halts; every contract |

**Non-vacuity.** `pSwDead` satisfies `hterm`, `hU` and `hOw`. (Lean: `pruneArm_equivPP_of_otherwise_unreachable_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-arm-without-assume-unreachable-otherwise`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- Documented design (source), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L120–122: "// We remove this target from the switch, so record the inequality using `Assume`." / "if is_unreachable && !otherwise_unreachable {" / "add_assumption(BinOp::Ne, value);" (no inequality is recorded when the `otherwise` target is itself unreachable); L136–140: "(2, true) => {" / "// All targets are unreachable except one. Record the equality, and make it a goto." / "let (value, target) = new_targets.iter().next().unwrap();" / "add_assumption(BinOp::Eq, value);" / "TerminatorKind::Goto { target }"; L19–20: "// Enable only under -Zmir-opt-level=2 as this can make programs less debuggable." / "PassPolicy::optimization(sess.mir_opt_level() >= 2)".

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-arm-without-assume-invariant`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, switch `x arms ow` and value `v`: if block `l` ends in `switch x arms ow` and `x ≠ v` holds on every reachable state at the switch (`ReachableAt`, including runs that reach UB later), then pruning the arms with value `v` without `assume` is a prefix-preserving equivalence, with no condition on the pruned label.

**Kind / tier / depth.** theorem / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:398-402
theorem pruneArm_equivPP_of_invariant_ne (K : ZContract) (P : Prog) (l : Label) (x : Var)
    (arms : List (Int × Label)) (ow : Label) (v : Int)
    (hterm : (P.blk l).term = .switch x arms ow)
    (hinv : ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x ≠ v) :
    EquivPP K P (pruneArm P l v) := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hterm : (P.blk l).term = .switch x arms ow` | `pruneArm_equivPP_of_invariant_ne` | names the switch whose arms are pruned and its variable | tight: `pruneArm_invariant_ne_hterm_counterexample` | `pSwDiffVar`: block 0 sets local 0 := 1 and switches on local 1; with stated variable `x = 0`, `hinv` holds; every contract |
| `hinv : ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x ≠ v` | `pruneArm_equivPP_of_invariant_ne` | the pruned value never reaches the switch | tight: `pruneArm_pSw_hyps_counterexample` | `pSw` (`hterm` holds) on local 0 = 5; every contract |

**Non-vacuity.** `pSwInv` (local 0 := 1 before the switch) satisfies `hterm` and `hinv`. In `pSwInv` the pruned arm targets `Block.unreach`, so the hypothesis `hU` of `pruneArm_equivPP_iff` also holds there; the theorem has no hypothesis on the pruned label, and `pruneArm_equivPP_of_invariant_ne_live_arm_witness` proves, for every contract, an instance (`pSwLiveInv`) whose pruned arm targets a block that emits 9 and halts (not an unreachable block), with all hypotheses holding and the equivalence holding. (Lean: `pruneArm_equivPP_of_invariant_ne_nonvacuous`, `pruneArm_equivPP_of_invariant_ne_live_arm_witness`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-arm-without-assume-invariant`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- X. Wang, N. Zeldovich, M. F. Kaashoek, A. Solar-Lezama, 'Towards Optimization-Safe Systems: Analyzing the Impact of Undefined Behavior', SOSP 2013, pp. 260–275, doi:10.1145/2517349.2522728 (optimizations that use the assumption that UB does not occur).

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-arm-without-assume-not-equivalence-and-vc-one-way`

**Plain claim.** For `pSw` (arm 5 → unreachable block, otherwise halt) and every contract, pruning the arm without `assume`: the target's demonic total-correctness `wp` for the postcondition `True` holds on every input, the source's `wp` for `True` holds exactly when local 0 ≠ 5, so at local 0 = 5 it holds for the target and fails for the source; the pruning is a prefix-preserving refinement but not a whole-trace equivalence.

**Kind / tier / depth.** counterexample / T0 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:425-429
theorem pruneArm_pSw_wp_transfers_one_way (K : ZContract) :
    (∀ σ, wp K (pruneArm pSw 0 5) (fun _ _ => True) σ) ∧
      (∀ σ, wp K pSw (fun _ _ => True) σ ↔ σ.locals 0 ≠ 5) ∧
      wp K (pruneArm pSw 0 5) (fun _ _ => True) (mkState [5]) ∧
      ¬ wp K pSw (fun _ _ => True) (mkState [5]) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:448-449
theorem pruneArm_pSw_refinesPP_not_equivWT (K : ZContract) :
    RefinesPP K pSw (pruneArm pSw 0 5) ∧ ¬ EquivWT K pSw (pruneArm pSw 0 5) := by …
```

**Hypothesis ledger.** No hypotheses: a concrete instance (universally quantified over the contract).

**Non-vacuity.** Concrete instance (no hypotheses).

**Positive control.** With the `assume` kept, the same pruning is an equivalence with equal `wp`. (Lean: `pruneArmAssume_pSw_equivPP_and_wp`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-arm-without-assume-not-equivalence-and-vc-one-way`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/hint.rs: `unreachable_unchecked` L16 "Reaching this function is *Undefined Behavior*."; `assert_unchecked` L146 "`cond` must be `true`. It is immediate UB to call this with `false`."
- M. Barnett, K. R. M. Leino, 'Weakest-precondition of unstructured programs', PASTE 2005, pp. 82–87, doi:10.1145/1108792.1108813, §2: "wp(assert P, Q) = P ∧ Q" and "wp(assume P, Q) = P ⇒ Q", and §1: a trace "ends in error if an assert statement evaluates to false, and ends in infeasibility if an assume statement evaluates to false". The toy's UB-on-false `assume` follows the first rule (`wpFrom_assume`); the second, miraculous rule is not modelled.

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — the toy's `switch`, `unreachable` terminator and UB-on-false `assume` are read as models of the switch, unreachable and assume constructs described in the quoted rustc source comments (`unreachable_prop.rs`) and the quoted `core::hint` documentation. The toy rule for `wp` of `assume` is the `assert` rule quoted from Barnett and Leino. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `replace-block-by-unreachable-exact-condition`

**Plain claim.** For every zero-size contract `K`, program `P` and label `b`: replacing block `b` by `Block.unreach` is a prefix-preserving refinement iff, from every reachable state at the entry of `b`, the source run reaches UB with empty trace; and it is a whole-trace refinement iff, from every such state, the source run reaches UB after some trace (events before the UB are permitted; divergence is not).

**Kind / tier / depth.** characterization / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Backward.lean:17-19
theorem replaceUnreachable_refinesPP_iff (K : ZContract) (P : Prog) (b : Label) :
    RefinesPP K P (replaceUnreachable P b) ↔
      ∀ st, ReachableAt K P b 0 st → GoesWrongFrom K P (P.entry b st) [] := by …
```

```lean
-- Toy/ZstAssume/Backward.lean:25-27
theorem replaceUnreachable_refinesWT_iff (K : ZContract) (P : Prog) (b : Label) :
    RefinesWT K P (replaceUnreachable P b) ↔
      ∀ st, ReachableAt K P b 0 st → ∃ t, GoesWrongFrom K P (P.entry b st) t := by …
```

**Hypothesis ledger.** No side hypotheses: both characterizations are universally quantified over every contract `K`, program `P` and label `b`, so there is no hypothesis whose tightness could be recorded.

**Non-vacuity.** `pSilentToUnreach` (block 1 assigns and jumps to an unreachable block): both sides are proved true independently; `replaceUnreachable_emit_before_unreachable` and `replaceUnreachable_diverging_loop_not_refinesWT` are instances in which sides are false. (Lean: `replaceUnreachable_pSilentToUnreach`)

**Non-claims.** Listed under Boundaries, "Non-claims: `replace-block-by-unreachable-exact-condition`"; read them before relying on this result.

**Prior art.**

- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- S. D. Herring, 'Partial program correctness', ISO/IEC JTC1/SC22/WG21 P1494R5, 2025-02-14, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p1494r5.html: "The “time travel” aspect of such optimizations (explicitly authorized by [intro.abstract]/5) is surprising to many programmers in that it can sometimes eliminate tests meant to detect the invalid operation in question." and "A call to std::observable prevents the propagation of assumptions based on the potential for undefined behavior after it into code before it." (in C++, UB may affect behaviour before it, as in the toy's whole-trace discipline; the proposed checkpoint restores a prefix guarantee, as in the prefix-preserving discipline).
- N. P. Lopes et al., Alive2 (PLDI 2021, doi:10.1145/3453483.3454030), §5 (author's version): "In LLVM, loops tagged with the mustprogress attribute must either terminate or perform externally observable actions infinitely often. The function triggers UB otherwise." (a forward-progress assumption under which silent divergence is UB; not modelled in the toy).

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — replacing a block by `Block.unreach` is read as the propagation of unreachability to a block, as discussed in the quoted sources; divergence is a behaviour of the toy and never UB, unlike the forward-progress assumption quoted from the Alive2 paper. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `replace-block-by-unreachable-counterexamples`

**Plain claim.** For every contract, replacing the block `emit 7; unreachable` of `pEmitBeforeUnreach` by `Block.unreach` is not a prefix-preserving refinement but is a whole-trace refinement; and replacing the loop block of `pLoopBeforeUnreach` (which diverges silently on local 0 = 0) by `Block.unreach` is not a whole-trace refinement.

**Kind / tier / depth.** counterexample / T0 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/Backward.lean:42-44
theorem replaceUnreachable_emit_before_unreachable :
    ∀ K, ¬ RefinesPP K pEmitBeforeUnreach (replaceUnreachable pEmitBeforeUnreach 1) ∧
      RefinesWT K pEmitBeforeUnreach (replaceUnreachable pEmitBeforeUnreach 1) := by …
```

```lean
-- Toy/ZstAssume/Backward.lean:81-84
theorem replaceUnreachable_diverging_loop_not_refinesWT (K : ZContract) :
    HasBeh K pLoopBeforeUnreach (mkState [0]) (.div []) ∧
      HasBeh K (replaceUnreachable pLoopBeforeUnreach 0) (mkState [0]) (.wrong []) ∧
      ¬ RefinesWT K pLoopBeforeUnreach (replaceUnreachable pLoopBeforeUnreach 0) := by …
```

**Hypothesis ledger.** No hypotheses: concrete instances (universally quantified over the contract).

**Non-vacuity.** Concrete instances (no hypotheses).

**Positive control.** A block from which every run reaches UB silently can be replaced. (Lean: `replaceUnreachable_pSilentToUnreach`)

**Non-claims.** Listed under Boundaries, "Non-claims: `replace-block-by-unreachable-counterexamples`"; read them before relying on this result.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (observable behaviours with traces: termination, divergence, going wrong). Quoted from the author's version (§2.1; printed page not checked): "compiler optimizations can optimize away “going wrong” behaviors" and property (2) "S safe =⇒ (∀B, C ⇓ B =⇒ S ⇓ B)", a whole-trace inclusion for sources that cannot go wrong; property (4) "S |= Spec =⇒ C |= Spec" is forward preservation of specifications. The prefix-preserving relation used here (`ImprovesPP`) is CompCert's `behavior_improves`, not a definition of that paper.
- CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` (`beh1` is the source behaviour). `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- S. D. Herring, 'Partial program correctness', ISO/IEC JTC1/SC22/WG21 P1494R5, 2025-02-14, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p1494r5.html: "The “time travel” aspect of such optimizations (explicitly authorized by [intro.abstract]/5) is surprising to many programmers in that it can sometimes eliminate tests meant to detect the invalid operation in question." and "A call to std::observable prevents the propagation of assumptions based on the potential for undefined behavior after it into code before it." (in C++, UB may affect behaviour before it, as in the toy's whole-trace discipline; the proposed checkpoint restores a prefix guarantee, as in the prefix-preserving discipline).
- N. P. Lopes et al., Alive2 (PLDI 2021, doi:10.1145/3453483.3454030), §5 (author's version): "In LLVM, loops tagged with the mustprogress attribute must either terminate or perform externally observable actions infinitely often. The function triggers UB otherwise." (a forward-progress assumption under which silent divergence is UB; not modelled in the toy).

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — replacing a block by `Block.unreach` is read as the propagation of unreachability to a block, as discussed in the quoted sources; divergence is a behaviour of the toy and never UB, unlike the forward-progress assumption quoted from the Alive2 paper. No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-with-assume-preserves-ub-derived-facts`

**Plain claim.** For every zero-size contract `K`, program `P`, block `l`, value `v`, program point `(l', i')` and state predicate `F`: if `F` holds at `(l', i')` on every run of `P` that never reaches UB, then `F` holds at `(l', i')` on every run of `pruneArmAssume P l v` that never reaches UB.

**Kind / tier / depth.** theorem / T1 / substantive.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:632-634
theorem pruneArmAssume_preserves_factOnDefinedRuns (K : ZContract) (P : Prog) (l : Label)
    (v : Int) (l' : Label) (i' : Nat) (F : State → Prop)
    (hF : FactOnDefinedRuns K P l' i' F) : FactOnDefinedRuns K (pruneArmAssume P l v) l' i' F := by …
```

**Hypothesis ledger.**

| Hypothesis | Theorem(s) | Purpose | Tightness | Witness class |
|---|---|---|---|---|
| `hF : FactOnDefinedRuns K P l' i' F` | `pruneArmAssume_preserves_factOnDefinedRuns` | the fact holds in the source | tight: `pruneArmAssume_fact_hypothesis_counterexample` | `pFact` with `F = False` at `(0, 0)`, `l = 0`, `v = 5`; every contract |

**Non-vacuity.** `pFact` with the UB-derived fact `local 0 ≠ 5` at its switch satisfies `hF`. (Lean: `pruneArmAssume_preserves_factOnDefinedRuns_nonvacuous`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-with-assume-preserves-ub-derived-facts`"; read them before relying on this result.

**Prior art.**

- X. Wang, N. Zeldovich, M. F. Kaashoek, A. Solar-Lezama, 'Towards Optimization-Safe Systems: Analyzing the Impact of Undefined Behavior', SOSP 2013, pp. 260–275, doi:10.1145/2517349.2522728 (optimizations that use the assumption that UB does not occur).
- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- S. D. Herring, 'Partial program correctness', ISO/IEC JTC1/SC22/WG21 P1494R5, 2025-02-14, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p1494r5.html: "The “time travel” aspect of such optimizations (explicitly authorized by [intro.abstract]/5) is surprising to many programmers in that it can sometimes eliminate tests meant to detect the invalid operation in question." and "A call to std::observable prevents the propagation of assumptions based on the potential for undefined behavior after it into code before it." (in C++, UB may affect behaviour before it, as in the toy's whole-trace discipline; the proposed checkpoint restores a prefix guarantee, as in the prefix-preserving discipline).

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — `FactOnDefinedRuns` is read as a fact that an optimizer derives from the assumption that UB does not occur (the optimizations studied by Wang et al., quoted under Prior art). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### `prune-without-assume-loses-ub-derived-facts`

**Plain claim.** For every contract: in `pFact` the fact `local 0 ≠ 5` holds at the switch on every non-UB run but fails on a non-UB run of the program pruned without `assume`; in `pStale`, a fold of block 1 to `goto 4` justified by the fact `local 0 ≠ 5` computed on the source is not a whole-trace refinement of its actual input (the program pruned without `assume`), although both that input and the composite are prefix-preserving refinements of the source; with the `assume` kept, the same fold is a prefix-preserving refinement of its input `pruneArmAssume pStale 0 5`. In `pEmitFact`, the fact `local 0 ≠ 5` holds at block 0's switch on every non-UB run, and folding block 0 to `goto 4` with it gives a whole-trace refinement of the source `pEmitFact` that is not a prefix-preserving refinement of `pEmitFact`; the composite that first prunes block 1's arm for 5 without `assume` (a prefix-preserving refinement of `pEmitFact`) and then applies the same fold is likewise a whole-trace refinement of the source `pEmitFact` and not a prefix-preserving refinement of `pEmitFact`, and it is not a whole-trace refinement of its actual input `pruneArm pEmitFact 1 5`.

**Kind / tier / depth.** counterexample / T1 / shallow.

**Statement.**

```lean
-- Toy/ZstAssume/Switch.lean:677-679
theorem pruneArm_breaks_ubDerivedFact (K : ZContract) :
    FactOnDefinedRuns K pFact 0 0 (fun st => st.locals 0 ≠ 5) ∧
      ¬ FactOnDefinedRuns K (pruneArm pFact 0 5) 0 0 (fun st => st.locals 0 ≠ 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:730-734
theorem staleFact_fold_after_pruneArm (K : ZContract) :
    FactOnDefinedRuns K pStale 1 0 (fun st => st.locals 0 ≠ 5) ∧
      RefinesPP K pStale (pruneArm pStale 0 5) ∧
      ¬ RefinesWT K (pruneArm pStale 0 5) (foldToGoto (pruneArm pStale 0 5) 1 4) ∧
      RefinesPP K pStale (foldToGoto (pruneArm pStale 0 5) 1 4) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:773-774
theorem staleFact_fold_after_pruneArmAssume_refinesPP (K : ZContract) :
    RefinesPP K (pruneArmAssume pStale 0 5) (foldToGoto (pruneArmAssume pStale 0 5) 1 4) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:806-812
theorem factOnDefinedRuns_fold_refinesWT_not_refinesPP (K : ZContract) :
    FactOnDefinedRuns K pEmitFact 0 0 (fun st => st.locals 0 ≠ 5) ∧
      ¬ RefinesPP K pEmitFact (foldToGoto pEmitFact 0 4) ∧
      RefinesWT K pEmitFact (foldToGoto pEmitFact 0 4) ∧
      RefinesPP K pEmitFact (pruneArm pEmitFact 1 5) ∧
      ¬ RefinesPP K pEmitFact (foldToGoto (pruneArm pEmitFact 1 5) 0 4) ∧
      RefinesWT K pEmitFact (foldToGoto (pruneArm pEmitFact 1 5) 0 4) := by …
```

```lean
-- Toy/ZstAssume/Companion.lean:18-19
theorem emitFact_fold_after_pruneArm_not_refinesWT_input (K : ZContract) :
    ¬ RefinesWT K (pruneArm pEmitFact 1 5) (foldToGoto (pruneArm pEmitFact 1 5) 0 4) := by …
```

**Hypothesis ledger.** No hypotheses: concrete instances (universally quantified over the contract).

**Non-vacuity.** Concrete instances (no hypotheses).

**Positive control.** With the `assume` kept, the fact-based fold is a prefix-preserving refinement of its input `pruneArmAssume pStale 0 5` (also one of this card's results, quoted in its statement block). (Lean: `staleFact_fold_after_pruneArmAssume_refinesPP`)

**Non-claims.** Listed under Boundaries, "Non-claims: `prune-without-assume-loses-ub-derived-facts`"; read them before relying on this result.

**Prior art.**

- X. Wang, N. Zeldovich, M. F. Kaashoek, A. Solar-Lezama, 'Towards Optimization-Safe Systems: Analyzing the Impact of Undefined Behavior', SOSP 2013, pp. 260–275, doi:10.1145/2517349.2522728 (optimizations that use the assumption that UB does not occur).
- Documented design (source comments), rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/unreachable_prop.rs L1–3: "A pass that propagates the unreachable terminator of a block to its predecessors when all of their successors are unreachable. This is achieved through a post-order traversal of the blocks."; L89–90: "In order to preserve this information, we record reachable and unreachable targets as `Assume` statements in MIR."; L120: "We remove this target from the switch, so record the inequality using `Assume`."
- S. D. Herring, 'Partial program correctness', ISO/IEC JTC1/SC22/WG21 P1494R5, 2025-02-14, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p1494r5.html: "The “time travel” aspect of such optimizations (explicitly authorized by [intro.abstract]/5) is surprising to many programmers in that it can sometimes eliminate tests meant to detect the invalid operation in question." and "A call to std::observable prevents the propagation of assumptions based on the potential for undefined behavior after it into code before it." (in C++, UB may affect behaviour before it, as in the toy's whole-trace discipline; the proposed checkpoint restores a prefix guarantee, as in the prefix-preserving discipline).

**Design question.** Pruning a switch arm whose target is `Unreachable`, and propagating unreachability backwards, again deletes code whose sole effect is UB. When is pruning an equivalence for traces and for `wp`, when is it a forward refinement, and what does an inserted `assume` guard buy?

**Basis.** execution (Lean kernel check) for every declaration quoted in the statement block above.

Basis: derived (modeling bridge) — `FactOnDefinedRuns` is read as a fact that an optimizer derives from the assumption that UB does not occur (the optimizations studied by Wang et al., quoted under Prior art). No model–system relation is proved; the theorems of this card neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

### Auxiliary declarations cited by name (verbatim)

Every package declaration mentioned by name above and not quoted in the definitions or card statements is quoted here.

```lean
-- Toy/ZstAssume/RunLemmas.lean:190-191
theorem refinesWT_of_refinesPP {K : ZContract} {src tgt : Prog} (h : RefinesPP K src tgt) :
    RefinesWT K src tgt := by …
```

```lean
-- Toy/ZstAssume/RunLemmas.lean:197
theorem equivWT_of_equivPP {K : ZContract} {p q : Prog} (h : EquivPP K p q) : EquivWT K p q := …
```

```lean
-- Toy/ZstAssume/Examples.lean:20
theorem state_set_updates : ((mkState [1, 2]).set 0 5).locals 0 = 5 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:22
theorem state_set_frames : ((mkState [1, 2]).set 0 5).locals 1 = 2 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:23
theorem expr_eval_add : Expr.eval (mkState [3]) (.add (.var 0) (.const 2)) = 5 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:25-26
theorem expr_eval_no_wrap :
    Expr.eval (mkState []) (.add (.const 18446744073709551615) (.const 1)) ≠ 0 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:27
theorem cond_eval_pos : Cond.eval (mkState [5]) (.eq 0 5) = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:28
theorem cond_eval_neg : Cond.eval (mkState [5]) (.ne 0 5) = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:29
theorem bytesDeref_pos : bytesDeref (fun p => decide (p < 10)) 8 2 = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:31
theorem bytesDeref_neg : bytesDeref (fun p => decide (p < 10)) 9 2 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:32
theorem accessTy_read : (Stmt.read (.var 0) ⟨0, 4⟩).accessTy? = some ⟨0, 4⟩ := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:33
theorem accessTy_emit : (Stmt.emit (.const 0)).accessTy? = none := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:37
theorem aligned_pos : aligned 4 8 = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:38
theorem aligned_neg : aligned 4 6 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:40
theorem aligned_zero_align_zero_addr : aligned 0 0 = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:41
theorem aligned_zero_align_nonzero_addr : aligned 0 4 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:43
theorem aligned_zero_iff (p : Int) : aligned 0 p = true ↔ p = 0 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:48-49
theorem holds_anyPtr_null_misaligned : ZContract.anyPtr.holds 4 0 = true ∧
    ZContract.anyPtr.holds 4 1 = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:50
theorem holds_aligned_rejects_misaligned : ZContract.aligned.holds 4 1 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:51
theorem holds_aligned_admits_null : ZContract.aligned.holds 4 0 = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:52
theorem holds_nonnullAligned_rejects_null : ZContract.nonnullAligned.holds 1 0 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:62-64
theorem accessOK_zero_ignores_deref :
    accessOK .aligned (fun _ => false) 4 8 0 = true ∧
      accessOK .aligned (fun _ => true) 4 9 0 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:67
theorem accessOK_nonzero_null (K : ZContract) : accessOK K (fun _ => true) 1 0 1 = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:72
theorem isZeroSize_read_zst : IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:73
theorem isZeroSize_copy_zero_count : IsZeroSizeAccess (.copy (.var 0) (.var 1) ⟨4, 4⟩ 0) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:75
theorem isZeroSize_copy_zst : IsZeroSizeAccess (.copy (.var 0) (.var 1) ⟨0, 2⟩ 3) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:76
theorem not_isZeroSize_read_byte : ¬ IsZeroSizeAccess (.read (.var 0) ⟨1, 1⟩) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:77
theorem not_isZeroSize_copy_one : ¬ IsZeroSizeAccess (.copy (.var 0) (.var 1) ⟨4, 4⟩ 1) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:79
theorem not_isZeroSize_emit : ¬ IsZeroSizeAccess (.emit (.const 0)) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:83-84
theorem pre_eq_zeroPre_of_isZeroSize (K : ZContract) (st : State) (s : Stmt)
    (hz : IsZeroSizeAccess s) : s.pre K st = s.zeroPre K st := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:97-98
theorem zeroPre_read_misaligned :
    (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [1]) = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:99-100
theorem zeroPre_read_aligned :
    (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [8]) = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:101-102
theorem zeroPre_copy_checks_src :
    (Stmt.copy (.var 0) (.var 1) ⟨4, 4⟩ 0).zeroPre .aligned (mkState [1, 8]) = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:106-107
theorem zeroPre_of_align_one {K : ZContract} (hK : K ≠ .nonnullAligned) (s : Stmt)
    (st : State) (ha : ∀ τ, s.accessTy? = some τ → τ.align = 1) : s.zeroPre K st = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:127
theorem selectTarget_first_match : selectTarget [(5, 1), (5, 2)] 0 5 = 1 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:129
theorem selectTarget_otherwise : selectTarget [(5, 1)] 0 6 = 0 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:144-145
theorem step_emit7 (K : ZContract) (σ : State) :
    step K pEmit7 (pEmit7.init σ) = .next (some 7) ⟨0, [], σ⟩ := …
```

```lean
-- Toy/ZstAssume/Examples.lean:147
theorem step_unreach (K : ZContract) (σ : State) : step K pUnreach (pUnreach.init σ) = .ub := …
```

```lean
-- Toy/ZstAssume/Examples.lean:148
theorem at_terminator (σ : State) : (pEmit7.at 0 1 σ).rest = [] := …
```

```lean
-- Toy/ZstAssume/Examples.lean:149
theorem at_entry (σ : State) : (pEmit7.at 0 0 σ).rest = [.emit (.const 7)] := …
```

```lean
-- Toy/ZstAssume/Examples.lean:150
theorem prefixOf_example : prefixOf (fun n => (n : Int)) 3 = [0, 1, 2] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:152
theorem hasBeh_emit7 (K : ZContract) (σ : State) : HasBeh K pEmit7 σ (.term [7]) := …
```

```lean
-- Toy/ZstAssume/Examples.lean:155-156
theorem not_hasBeh_emit7_wrong (K : ZContract) (σ : State) (t : List Int) :
    ¬ HasBeh K pEmit7 σ (.wrong t) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:165-166
theorem run_spin (K : ZContract) (σ : State) :
    ∀ n, run K pSpin n (pSpin.init σ) = .running (pSpin.init σ) [] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:174-175
theorem hasBeh_spin (K : ZContract) (σ : State) (b : Beh) :
    HasBeh K pSpin σ b ↔ b = .div [] := …
```

```lean
-- Toy/ZstAssume/Examples.lean:207
theorem hasBeh_react (K : ZContract) (σ : State) : HasBeh K pReact σ (.react fun _ => 1) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:214
theorem improvesPP_pos : ImprovesPP (.term [1, 2]) (.wrong [1]) := …
```

```lean
-- Toy/ZstAssume/Examples.lean:216
theorem improvesPP_neg : ¬ ImprovesPP (.term [2]) (.wrong [1]) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:221
theorem improvesWT_pos : ImprovesWT (.term [2]) (.wrong [1]) := …
```

```lean
-- Toy/ZstAssume/Examples.lean:222
theorem improvesWT_neg : ¬ ImprovesWT (.term [1]) (.term [2]) := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:228
theorem refinesPP_of_src_unreach (K : ZContract) (P : Prog) : RefinesPP K pUnreach P := …
```

```lean
-- Toy/ZstAssume/Examples.lean:233
theorem not_refinesWT_halt_unreach (K : ZContract) : ¬ RefinesWT K pHalt pUnreach := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:249
theorem refinesWT_emitUnreach_unreach (K : ZContract) : RefinesWT K pEmitUnreach pUnreach := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:256-257
theorem not_refinesPP_emitUnreach_unreach (K : ZContract) :
    ¬ RefinesPP K pEmitUnreach pUnreach := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:272
theorem reachableAt_entry (K : ZContract) (P : Prog) (σ : State) : ReachableAt K P 0 0 σ := …
```

```lean
-- Toy/ZstAssume/Examples.lean:276-277
theorem not_reachableAt_dead_block (K : ZContract) (st : State) :
    ¬ ReachableAt K pTwoHalts 1 0 st := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:287
theorem ubFree_halt (K : ZContract) : UBFree K pHalt := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:293
theorem not_ubFree_unreach (K : ZContract) : ¬ UBFree K pUnreach := …
```

```lean
-- Toy/ZstAssume/Examples.lean:298
theorem cons_none (r : Outcome) : r.cons none = r := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:302-304
theorem wpFrom_unreachable {K : ZContract} {P : Prog} {l : Label} {st : State}
    (Q : List Int → State → Prop) (hl : (P.blk l).term = .unreachable) :
    ¬ wpFrom K P Q ⟨l, [], st⟩ := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:314-316
theorem wpFrom_assume {K : ZContract} {P : Prog} {l : Label} {st : State} {rest : List Stmt}
    (Q : List Int → State → Prop) (c : Cond) :
    wpFrom K P Q ⟨l, .assume c :: rest, st⟩ ↔ c.eval st = true ∧ wpFrom K P Q ⟨l, rest, st⟩ := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:336
theorem wp_halt_true (K : ZContract) (σ : State) : wp K pHalt (fun _ _ => True) σ := …
```

```lean
-- Toy/ZstAssume/Examples.lean:339-340
theorem not_wp_unreach (K : ZContract) (Q : List Int → State → Prop) (σ : State) :
    ¬ wp K pUnreach Q σ := …
```

```lean
-- Toy/ZstAssume/Examples.lean:345-347
theorem deleteStmt_example :
    deleteStmt [⟨[.read (.var 0) ⟨0, 4⟩, .emit (.const 1)], .halt⟩] 0 0 =
      [⟨[.emit (.const 1)], .halt⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:349
theorem deleteStmt_out_of_range : deleteStmt pEmit7 0 5 = pEmit7 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:352-354
theorem insertStmt_past_end :
    insertStmt pEmit7 0 5 (.read (.var 0) ⟨0, 4⟩) =
      [⟨[.emit (.const 7), .read (.var 0) ⟨0, 4⟩], .halt⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:356-358
theorem insertStmt_example :
    insertStmt pEmit7 0 1 (.read (.var 0) ⟨0, 4⟩) =
      [⟨[.emit (.const 7), .read (.var 0) ⟨0, 4⟩], .halt⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:360
theorem dropArms_example : dropArms [(5, 1), (6, 2), (5, 3)] 5 = [(6, 2)] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:362
theorem dropArms_keeps : dropArms [(6, 2)] 5 = [(6, 2)] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:364-365
theorem pruneArm_example :
    pruneArm [⟨[], .switch 0 [(5, 1), (6, 2)] 3⟩] 0 5 = [⟨[], .switch 0 [(6, 2)] 3⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:368
theorem pruneArm_non_switch : pruneArm pEmit7 0 5 = pEmit7 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:370-372
theorem pruneArmAssume_example :
    pruneArmAssume [⟨[], .switch 0 [(5, 1), (6, 2)] 3⟩] 0 5 =
      [⟨[.assume (.ne 0 5)], .switch 0 [(6, 2)] 3⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:373
theorem pruneArmAssume_non_switch : pruneArmAssume pEmit7 0 5 = pEmit7 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:375-377
theorem pruneOtherwiseAssume_example :
    pruneOtherwiseAssume [⟨[], .switch 0 [(5, 1)] 2⟩] 0 =
      [⟨[.assume (.eq 0 5)], .goto 1⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:379-381
theorem pruneOtherwiseAssume_two_arms :
    pruneOtherwiseAssume [⟨[], .switch 0 [(5, 1), (6, 1)] 2⟩] 0 =
      [⟨[], .switch 0 [(5, 1), (6, 1)] 2⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:383
theorem replaceUnreachable_example : replaceUnreachable pEmit7 0 = pUnreach := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:385
theorem replaceUnreachable_out_of_range : replaceUnreachable pEmit7 3 = pEmit7 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:388
theorem setTerm_out_of_range : setTerm pEmit7 3 (.goto 0) = pEmit7 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:390-391
theorem foldToGoto_example :
    foldToGoto [⟨[], .switch 0 [(5, 1)] 2⟩] 0 2 = [⟨[], .goto 2⟩] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:393
theorem isUnreachableBlock_out_of_range : IsUnreachableBlock pHalt 7 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:394
theorem isUnreachableBlock_unreach : IsUnreachableBlock pUnreach 0 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:395
theorem not_isUnreachableBlock_halt : ¬ IsUnreachableBlock pHalt 0 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:397
theorem not_isUnreachableBlock_emit_unreach : ¬ IsUnreachableBlock pEmitUnreach 0 := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:402
theorem ty_fields : (⟨0, 4⟩ : Ty).size = 0 ∧ (⟨0, 4⟩ : Ty).align = 4 := …
```

```lean
-- Toy/ZstAssume/Examples.lean:404
theorem ty_align_distinguishes : (⟨0, 4⟩ : Ty) ≠ ⟨0, 1⟩ := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:407
theorem state_locals_example : (mkState [3, 4]).locals 1 = 4 ∧ (mkState []).deref 0 = true := …
```

```lean
-- Toy/ZstAssume/Examples.lean:410
theorem state_noMem_example : (mkStateNoMem [3, 4]).deref 0 = false := …
```

```lean
-- Toy/ZstAssume/Examples.lean:413
theorem pre_read_aligned : (Stmt.read (.var 0) ⟨0, 4⟩).pre .aligned (mkState [8]) = true := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:416-417
theorem pre_read_misaligned :
    (Stmt.read (.var 0) ⟨0, 4⟩).pre .aligned (mkState [1]) = false := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:420-421
theorem execStmt_assume_pass (K : ZContract) :
    (execStmt K (.assume (.eq 0 5)) (mkState [5])).isSome = true := …
```

```lean
-- Toy/ZstAssume/Examples.lean:423-424
theorem execStmt_assume_fail (K : ZContract) :
    execStmt K (.assume (.eq 0 5)) (mkState [4]) = none := …
```

```lean
-- Toy/ZstAssume/Examples.lean:427
theorem outcome_trace_done : (Outcome.done [7] (mkState [])).trace = [7] := …
```

```lean
-- Toy/ZstAssume/Examples.lean:429
theorem outcome_trace_ub_ne : (Outcome.ub [1]).trace ≠ [7] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:431
theorem outcome_isRunning_running (c : Cfg) : (Outcome.running c [1]).isRunning = true := …
```

```lean
-- Toy/ZstAssume/Examples.lean:433
theorem outcome_isRunning_ub : (Outcome.ub [1]).isRunning = false := …
```

```lean
-- Toy/ZstAssume/Examples.lean:435
theorem outcome_cons_some : ((Outcome.ub [2]).cons (some 1)).trace = [1, 2] := …
```

```lean
-- Toy/ZstAssume/Examples.lean:438
theorem prefixOf_neg : prefixOf (fun n => (n : Int)) 3 ≠ [0, 1] := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:441-442
theorem goesWrongFrom_unreach (K : ZContract) (σ : State) :
    GoesWrongFrom K pUnreach (pUnreach.init σ) [] := …
```

```lean
-- Toy/ZstAssume/Examples.lean:444-445
theorem not_goesWrongFrom_halt (K : ZContract) (σ : State) (t : List Int) :
    ¬ GoesWrongFrom K pHalt (pHalt.init σ) t := by …
```

```lean
-- Toy/ZstAssume/Examples.lean:453
theorem equivWT_emitUnreach_unreach (K : ZContract) : EquivWT K pEmitUnreach pUnreach := …
```

```lean
-- Toy/ZstAssume/Examples.lean:455
theorem not_equivPP_emitUnreach_unreach (K : ZContract) : ¬ EquivPP K pEmitUnreach pUnreach := …
```

```lean
-- Toy/ZstAssume/Examples.lean:458
theorem not_equivWT_halt_unreach (K : ZContract) : ¬ EquivWT K pHalt pUnreach := …
```

```lean
-- Toy/ZstAssume/Examples.lean:462-463
theorem copyProg_aligned_term :
    HasBeh .aligned (copyProg 0 1 ⟨4, 4⟩ 0) (mkState [8, 8]) (.term []) := …
```

```lean
-- Toy/ZstAssume/Examples.lean:465-466
theorem copyProg_misaligned_wrong :
    HasBeh .aligned (copyProg 0 1 ⟨4, 4⟩ 0) (mkState [1, 8]) (.wrong []) := …
```

```lean
-- Toy/ZstAssume/Examples.lean:468-469
theorem copyLoopProg_zero_term :
    HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (mkState [1, 8]) (.term []) := …
```

```lean
-- Toy/ZstAssume/Examples.lean:472-473
theorem copyLoopProg_one_misaligned_wrong :
    HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 1) (mkState [1, 8]) (.wrong []) := …
```

```lean
-- Toy/ZstAssume/Sim.lean:167
theorem hasBehFrom_exists (K : ZContract) (P : Prog) (c : Cfg) : ∃ b, HasBehFrom K P c b := by …
```

```lean
-- Toy/ZstAssume/Sim.lean:216-217
theorem hasBehFrom_unique {K : ZContract} {P : Prog} {c : Cfg} {b b' : Beh}
    (h : HasBehFrom K P c b) (h' : HasBehFrom K P c b') : b = b' := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:185-196
theorem deleteStmt_hz_counterexample (K : ZContract) :
    (pEmit7.blk 0).stmts[0]? = some (.emit (.const 7)) ∧
      ¬ IsZeroSizeAccess (.emit (.const 7)) ∧
      (∀ τ, (Stmt.emit (.const 7)).accessTy? = some τ → τ.align = 1) ∧
      (∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.emit (.const 7)).zeroPre K st = true) ∧
      ¬ RefinesWT K pEmit7 (deleteStmt pEmit7 0 0) ∧
      ¬ (EquivPP K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.emit (.const 7)).zeroPre K st = false →
          GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) []) ∧
      ¬ (EquivWT K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.emit (.const 7)).zeroPre K st = false →
          ∃ t, GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) t) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:211-224
theorem deleteStmt_hs_counterexample (K : ZContract) (hK : K ≠ .nonnullAligned) :
    (pEmit7.blk 0).stmts[0]? ≠ some (.read (.var 0) ⟨0, 1⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 1⟩) ∧
      (∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1) ∧
      (∀ st, ReachableAt K pEmit7 0 0 st → (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = true) ∧
      ¬ RefinesWT K pEmit7 (deleteStmt pEmit7 0 0) ∧
      ¬ (EquivPP K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st →
          (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = false →
          GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) []) ∧
      ¬ (EquivWT K pEmit7 (deleteStmt pEmit7 0 0) ↔
        ∀ st, ReachableAt K pEmit7 0 0 st →
          (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre K st = false →
          ∃ t, GoesWrongFrom K (deleteStmt pEmit7 0 0) ((deleteStmt pEmit7 0 0).at 0 0 st) t) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:252-254
theorem deleteZeroSizeAccess_iff_nonvacuous :
    (pTwoZstReads.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 4⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:306
theorem run_pHalt (K : ZContract) (σ : State) : run K pHalt 1 (pHalt.init σ) = .done [] σ := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:364-366
theorem deleteZeroSizeAccess_refinesPP_nonvacuous :
    (pReadZst4.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 4⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:372-378
theorem deleteZeroSizeAccess_sufficient_nonvacuous :
    (pReadZst1.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 1⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 1⟩) ∧
      (∀ st, ReachableAt .aligned pReadZst1 0 0 st →
        (Stmt.read (.var 0) ⟨0, 1⟩).zeroPre .aligned st = true) ∧
      ZContract.aligned ≠ .nonnullAligned ∧
      (∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:392-399
theorem deleteZeroSizeAccess_pReadZst4_counterexample :
    (pReadZst4.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 4⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ZContract.aligned ≠ .nonnullAligned ∧ ZContract.aligned ≠ .anyPtr ∧
      ¬ (∀ st, ReachableAt .aligned pReadZst4 0 0 st →
        (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned st = true) ∧
      ¬ (∀ τ, (Stmt.read (.var 0) ⟨0, 4⟩).accessTy? = some τ → τ.align = 1) ∧
      ¬ EquivPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:411-416
theorem deleteZeroSizeAccess_pReadZst1_nonnull_counterexample :
    (pReadZst1.blk 0).stmts[0]? = some (.read (.var 0) ⟨0, 1⟩) ∧
      IsZeroSizeAccess (.read (.var 0) ⟨0, 1⟩) ∧
      (∀ τ, (Stmt.read (.var 0) ⟨0, 1⟩).accessTy? = some τ → τ.align = 1) ∧
      ¬ (ZContract.nonnullAligned ≠ .nonnullAligned) ∧
      ¬ EquivPP .nonnullAligned pReadZst1 (deleteStmt pReadZst1 0 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:426-427
theorem zstRead_align_one_alignedContract_deletion_equivPP :
    EquivPP .aligned pReadZst1 (deleteStmt pReadZst1 0 0) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:515-524
theorem insertEmit_counterexample (K : ZContract) :
    ¬ IsZeroSizeAccess (.emit (.const 1)) ∧
      (∀ st, ReachableAt K pHalt 0 0 st → (Stmt.emit (.const 1)).zeroPre K st = true) ∧
      ¬ RefinesWT K pHalt (insertStmt pHalt 0 0 (.emit (.const 1))) ∧
      ¬ (RefinesPP K pHalt (insertStmt pHalt 0 0 (.emit (.const 1))) ↔
        ∀ st, ReachableAt K pHalt 0 0 st → (Stmt.emit (.const 1)).zeroPre K st = false →
          GoesWrongFrom K pHalt (pHalt.at 0 0 st) []) ∧
      ¬ (RefinesWT K pHalt (insertStmt pHalt 0 0 (.emit (.const 1))) ↔
        ∀ st, ReachableAt K pHalt 0 0 st → (Stmt.emit (.const 1)).zeroPre K st = false →
          ∃ t, GoesWrongFrom K pHalt (pHalt.at 0 0 st) t) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:538-543
theorem insertZstRead_before_failing_read_refinesPP :
    IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ReachableAt .aligned pReadZst4 0 0 (mkState [1]) ∧
      (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [1]) = false ∧
      GoesWrongFrom .aligned pReadZst4 (pReadZst4.at 0 0 (mkState [1])) [] ∧
      RefinesPP .aligned pReadZst4 (insertStmt pReadZst4 0 0 (.read (.var 0) ⟨0, 4⟩)) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:553-555
theorem insertZeroSizeAccess_anyPtr_nonvacuous :
    IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ∀ st, ReachableAt .anyPtr pHalt 0 0 st → (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .anyPtr st = true := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:576-580
theorem insertZeroSizeAccess_hpre_counterexample :
    IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) ∧
      ¬ (∀ st, ReachableAt .aligned pHalt 0 0 st →
        (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned st = true) ∧
      ¬ EquivPP .aligned pHalt (insertStmt pHalt 0 0 (.read (.var 0) ⟨0, 4⟩)) := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:617
theorem hoistZstRead_anyPtr_equivPP : EquivPP .anyPtr pBranchRead pBranchReadHoisted := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:636
theorem exactUBChecker_exists (K : ZContract) : ∃ chk, ExactUBChecker K chk := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:641
theorem not_exactUBChecker_const_true (K : ZContract) : ¬ ExactUBChecker K (fun _ => true) := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:661-662
theorem not_ubFree_src_of_not_ubFree_tgt_of_refinesWT (K : ZContract) (src tgt : Prog)
    (h : RefinesWT K src tgt) (htgt : ¬ UBFree K tgt) : ¬ UBFree K src := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:698
theorem revChainWT_nil (K : ZContract) (P : Prog) : RevChainWT K P [] := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:701
theorem not_revChainWT_unreach_halt (K : ZContract) : ¬ RevChainWT K pUnreach [pHalt] := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:721-722
theorem revRefinement_admits_ub_introduction (K : ZContract) :
    RefinesWT K pUnreach pHalt ∧ ¬ RefinesWT K pHalt pUnreach := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:734-737
theorem ubFree_output_hypothesis_counterexample (K : ZContract) :
    RefinesWT K pUnreach pUnreach ∧ RevChainWT K pUnreach [] ∧ EquivPP K pUnreach pUnreach ∧
      ¬ UBFree K (([pUnreach] : List Prog).getLast (List.cons_ne_nil _ _)) ∧
      ¬ UBFree K pUnreach := …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:746-752
theorem ubCheck_pReadZst4_hypotheses_counterexample :
    ¬ RefinesWT .aligned (deleteStmt pReadZst4 0 0) pReadZst4 ∧
      ¬ RevChainWT .aligned pReadZst4 [deleteStmt pReadZst4 0 0] ∧
      ¬ EquivPP .aligned pReadZst4 (deleteStmt pReadZst4 0 0) ∧
      UBFree .aligned (deleteStmt pReadZst4 0 0) ∧
      UBFree .aligned ((pReadZst4 :: [deleteStmt pReadZst4 0 0]).getLast (List.cons_ne_nil _ _)) ∧
      ¬ UBFree .aligned pReadZst4 := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:764-766
theorem ubFree_positive_control_instance :
    EquivPP .aligned pReadZst1 (deleteStmt pReadZst1 0 0) ∧
      UBFree .aligned (deleteStmt pReadZst1 0 0) ∧ UBFree .aligned pReadZst1 := by …
```

```lean
-- Toy/ZstAssume/ZeroSize.lean:776-781
theorem ubFree_src_of_ubFree_tgt_nonvacuous :
    RefinesWT .aligned (deleteStmt pReadZst1 0 0) pReadZst1 ∧
      RevChainWT .aligned pReadZst1 [deleteStmt pReadZst1 0 0] ∧
      EquivPP .aligned pReadZst1 (deleteStmt pReadZst1 0 0) ∧
      UBFree .aligned (deleteStmt pReadZst1 0 0) ∧
      UBFree .aligned ((pReadZst1 :: [deleteStmt pReadZst1 0 0]).getLast (List.cons_ne_nil _ _)) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:70-71
theorem pSw_hyps : (pSw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
    IsUnreachableBlock pSw (selectTarget [(5, 1)] 2 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:78-80
theorem pruneArmAssume_pSw_equivPP_and_wp (K : ZContract) :
    EquivPP K pSw (pruneArmAssume pSw 0 5) ∧
      ∀ Q σ, wp K (pruneArmAssume pSw 0 5) Q σ ↔ wp K pSw Q σ := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:124-128
theorem pruneArmAssume_emit_before_unreachable_not_refinesPP (K : ZContract) :
    (pSwEmitUnreach.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwEmitUnreach (selectTarget [(5, 1)] 2 5) ∧
      ¬ RefinesPP K pSwEmitUnreach (pruneArmAssume pSwEmitUnreach 0 5) ∧
      RefinesWT K pSwEmitUnreach (pruneArmAssume pSwEmitUnreach 0 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:209-218
theorem pruneArm_hU_counterexample (K : ZContract) :
    (pSwLive.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwLive (selectTarget [(5, 1)] 2 5) ∧
      ¬ EquivPP K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ EquivWT K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ (wp K (pruneArmAssume pSwLive 0 5) (fun _ _ => True) (mkState [5]) ↔
        wp K pSwLive (fun _ _ => True) (mkState [5])) ∧
      ¬ RefinesPP K pSwLive (pruneArm pSwLive 0 5) ∧
      ¬ (wp K pSwLive (fun t _ => t = [1]) (mkState [5]) →
        wp K (pruneArm pSwLive 0 5) (fun t _ => t = [1]) (mkState [5])) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:230-239
theorem pruneArm_hterm_counterexample (K : ZContract) :
    (pSwLive.blk 0).term ≠ .switch 0 [(5, 3)] 2 ∧
      IsUnreachableBlock pSwLive (selectTarget [(5, 3)] 2 5) ∧
      ¬ EquivPP K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ EquivWT K pSwLive (pruneArmAssume pSwLive 0 5) ∧
      ¬ (wp K (pruneArmAssume pSwLive 0 5) (fun _ _ => True) (mkState [5]) ↔
        wp K pSwLive (fun _ _ => True) (mkState [5])) ∧
      ¬ RefinesPP K pSwLive (pruneArm pSwLive 0 5) ∧
      ¬ (wp K pSwLive (fun t _ => t = [1]) (mkState [5]) →
        wp K (pruneArm pSwLive 0 5) (fun t _ => t = [1]) (mkState [5])) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:256-275
theorem pruneArm_iff_counterexample (K : ZContract) :
    (pSwLiveUnreachOw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwLiveUnreachOw (selectTarget [(5, 1)] 2 5) ∧
      (pSwLiveUnreachOw.blk 0).term ≠ .switch 0 [(5, 3)] 2 ∧
      IsUnreachableBlock pSwLiveUnreachOw (selectTarget [(5, 3)] 2 5) ∧
      IsUnreachableBlock pSwLiveUnreachOw 2 ∧
      (∀ st, GoesWrongFrom K (pruneArm pSwLiveUnreachOw 0 5)
        ((pruneArm pSwLiveUnreachOw 0 5).entry 2 st) []) ∧
      ¬ RefinesWT K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ∧
      ¬ EquivPP K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ∧
      ¬ (EquivPP K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ↔
        ∀ st, ReachableAt K pSwLiveUnreachOw 0 (pSwLiveUnreachOw.blk 0).stmts.length st →
          st.locals 0 = 5 →
          GoesWrongFrom K (pruneArm pSwLiveUnreachOw 0 5)
            ((pruneArm pSwLiveUnreachOw 0 5).entry 2 st) []) ∧
      ¬ (EquivWT K pSwLiveUnreachOw (pruneArm pSwLiveUnreachOw 0 5) ↔
        ∀ st, ReachableAt K pSwLiveUnreachOw 0 (pSwLiveUnreachOw.blk 0).stmts.length st →
          st.locals 0 = 5 →
          ∃ t, GoesWrongFrom K (pruneArm pSwLiveUnreachOw 0 5)
            ((pruneArm pSwLiveUnreachOw 0 5).entry 2 st) t) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:295-296
theorem pSwOne_hyps : (pSwOne.blk 0).term = .switch 0 [(5, 1)] 2 ∧
    IsUnreachableBlock pSwOne 2 := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:299-300
theorem pruneOtherwiseAssume_pSwOne_equivPP (K : ZContract) :
    EquivPP K pSwOne (pruneOtherwiseAssume pSwOne 0) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:318-326
theorem pruneOtherwiseAssume_live_otherwise_not_refinesWT (K : ZContract) :
    (pSw.blk 0).term = .switch 0 [(5, 1)] 2 ∧ ¬ IsUnreachableBlock pSw 2 ∧
      (pSw.blk 0).term ≠ .switch 0 [(5, 1)] 3 ∧ IsUnreachableBlock pSw 3 ∧
      ¬ RefinesWT K pSw (pruneOtherwiseAssume pSw 0) ∧
      ¬ EquivPP K pSw (pruneOtherwiseAssume pSw 0) ∧
      wp K pSw (fun _ _ => True) (mkState [0]) ∧
      ¬ wp K (pruneOtherwiseAssume pSw 0) (fun _ _ => True) (mkState [0]) ∧
      ¬ (wp K (pruneOtherwiseAssume pSw 0) (fun _ _ => True) (mkState [0]) ↔
        wp K pSw (fun _ _ => True) (mkState [0])) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:464-469
theorem pruneArm_pSw_hyps_counterexample (K : ZContract) :
    (pSw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      IsUnreachableBlock pSw (selectTarget [(5, 1)] 2 5) ∧
      ¬ IsUnreachableBlock pSw 2 ∧
      ¬ (∀ st, ReachableAt K pSw 0 (pSw.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      ¬ EquivPP K pSw (pruneArm pSw 0 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:479-482
theorem pSw_fact_not_invariant (K : ZContract) :
    FactOnDefinedRuns K pSw 0 0 (fun st => st.locals 0 ≠ 5) ∧
      ¬ (∀ st, ReachableAt K pSw 0 (pSw.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      ¬ EquivWT K pSw (pruneArm pSw 0 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:509-510
theorem pSwAssumeOw_hyps : (pSwAssumeOw.blk 0).term = .switch 0 [(5, 1)] 2 ∧
    IsUnreachableBlock pSwAssumeOw (selectTarget [(5, 1)] 2 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:516-521
theorem pruneArm_pSwAssumeOw_equivPP (K : ZContract) :
    ReachableAt K pSwAssumeOw 0 0 (mkState [5]) ∧
      ¬ IsUnreachableBlock pSwAssumeOw 2 ∧
      GoesWrongFrom K (pruneArm pSwAssumeOw 0 5) ((pruneArm pSwAssumeOw 0 5).entry 2
        (mkState [5])) [] ∧
      EquivPP K pSwAssumeOw (pruneArm pSwAssumeOw 0 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:555-557
theorem pruneArm_equivPP_of_invariant_ne_nonvacuous (K : ZContract) :
    (pSwInv.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ∀ st, ReachableAt K pSwInv 0 (pSwInv.blk 0).stmts.length st → st.locals 0 ≠ 5 := …
```

```lean
-- Toy/ZstAssume/Switch.lean:569-573
theorem pruneArm_invariant_ne_hterm_counterexample (K : ZContract) :
    (pSwDiffVar.blk 0).term ≠ .switch 0 [(5, 1)] 2 ∧
      (∀ st, ReachableAt K pSwDiffVar 0 (pSwDiffVar.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      ¬ EquivPP K pSwDiffVar (pruneArm pSwDiffVar 0 5) ∧
      ¬ EquivWT K pSwDiffVar (pruneArm pSwDiffVar 0 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:615-617
theorem pruneArm_equivPP_of_otherwise_unreachable_nonvacuous :
    (pSwDead.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      IsUnreachableBlock pSwDead (selectTarget [(5, 1)] 2 5) ∧ IsUnreachableBlock pSwDead 2 := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:641-642
theorem factOnDefinedRuns_unreach (K : ZContract) (l : Label) (i : Nat) (F : State → Prop) :
    FactOnDefinedRuns K pUnreach l i F := …
```

```lean
-- Toy/ZstAssume/Switch.lean:654-655
theorem pFact_fact (K : ZContract) :
    FactOnDefinedRuns K pFact 0 0 (fun st => st.locals 0 ≠ 5) := by …
```

```lean
-- Toy/ZstAssume/Switch.lean:689-690
theorem pruneArmAssume_preserves_factOnDefinedRuns_nonvacuous (K : ZContract) :
    FactOnDefinedRuns K pFact 0 0 (fun st => st.locals 0 ≠ 5) := …
```

```lean
-- Toy/ZstAssume/Switch.lean:696-698
theorem pruneArmAssume_fact_hypothesis_counterexample (K : ZContract) :
    ¬ FactOnDefinedRuns K pFact 0 0 (fun _ => False) ∧
      ¬ FactOnDefinedRuns K (pruneArmAssume pFact 0 5) 0 0 (fun _ => False) := by …
```

```lean
-- Toy/ZstAssume/Backward.lean:107-110
theorem replaceUnreachable_pSilentToUnreach (K : ZContract) :
    (∀ st, ReachableAt K pSilentToUnreach 1 0 st →
        GoesWrongFrom K pSilentToUnreach (pSilentToUnreach.entry 1 st) []) ∧
      RefinesPP K pSilentToUnreach (replaceUnreachable pSilentToUnreach 1) := by …
```

Supplementary instances (module `Toy/ZstAssume/Supplement.lean`):

```lean
-- Toy/ZstAssume/Supplement.lean:16-17
def pSwLiveInv : Prog :=
  [⟨[.assign 0 (.const 1)], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 9)], .halt⟩, ⟨[], .halt⟩]
```

```lean
-- Toy/ZstAssume/Supplement.lean:23-27
theorem pruneArm_equivPP_of_invariant_ne_live_arm_witness (K : ZContract) :
    (pSwLiveInv.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwLiveInv (selectTarget [(5, 1)] 2 5) ∧
      (∀ st, ReachableAt K pSwLiveInv 0 (pSwLiveInv.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      EquivPP K pSwLiveInv (pruneArm pSwLiveInv 0 5) := by …
```

```lean
-- Toy/ZstAssume/Supplement.lean:50-56
theorem copyLoopProg_zeroCount_preserves_src_dst :
    run .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) 4
      ((copyLoopProg 0 1 2 ⟨4, 4⟩ 0).init (mkState [8, 12, 42])) =
      .done [] ((mkState [8, 12, 42]).set 2 0) ∧
      ((mkState [8, 12, 42]).set 2 0).locals 0 = 8 ∧
      ((mkState [8, 12, 42]).set 2 0).locals 1 = 12 ∧
      ((mkState [8, 12, 42]).set 2 0).locals 2 = 0 := by …
```

Companion facts (module `Toy/ZstAssume/Companion.lean`; its other theorem, `emitFact_fold_after_pruneArm_not_refinesWT_input`, is quoted in the statement block of `prune-without-assume-loses-ub-derived-facts`):

```lean
-- Toy/ZstAssume/Companion.lean:39-44
theorem copyLoopProg_zeroCount_run (K : ZContract) (σ : State) :
    run K (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) 4 ((copyLoopProg 0 1 2 ⟨4, 4⟩ 0).init σ) =
        .done [] (σ.set 2 0) ∧
      (σ.set 2 0).locals 0 = σ.locals 0 ∧
      (σ.set 2 0).locals 1 = σ.locals 1 ∧
      (σ.set 2 0).locals 2 = 0 := by …
```

## Boundaries

### Non-claims (per result)

Each list below is complete for its result: shared non-claims are repeated wherever they apply, so a result can be cited in isolation together with its list.

#### Non-claims: `delete-zero-size-access-refines`

- Does not say the deletion is an equivalence; `zstRead_misaligned_deletion_erases_ub` shows it can erase UB.
- Does not cover deleting other statements whose sole effect is a possible UB event (nonzero accesses, `assume`); that they are also refinements in the toy is plausible but not proved here. Because the toy models no stored or loaded values, deleting a nonzero-size access would not change data in the toy either, so the zero-size restriction is about the theorem's scope, not about a data effect the toy represents.
- Behaviours record emitted values and no final state: `Beh.term` discards the final locals and memory, so `RefinesPP`, `RefinesWT`, `EquivPP` and `EquivWT` neither establish nor refute preservation of final states or of `wp` (`copyLoopLowering_zeroCount_clobbers_counter` is a prefix-preserving refinement that changes a final local and does not preserve `wp`).
- Value validity is not modelled: a toy `read` produces no value, so a zero-size type of alignment 1 whose values cannot exist (such as Rust's `!`) has no counterpart, and reading it, which is UB in Rust for a reason the toy does not represent (prior art: the Rust Reference's invalid-value rule), lies outside these statements; they neither establish nor refute anything about it.
- `copy src dst τ n` takes a literal natural-number count `n` (byte count `τ.size * n`, an unbounded natural-number product, so the zero-size edges are size 0 or count 0), not a run-time value, and does not check overlap of the two regions; counts computed at run time, overlapping copies and volatile accesses are not modelled.
- Degenerate edges: if `l` is outside the block list, `P.blk l` is `Block.unreach` (no statements, so a statement hypothesis `hs` fails); `deleteStmt`, `insertStmt`, `setTerm` and `List.set` leave a program unchanged at an out-of-range label.
- `ZContract` has the three constructors `anyPtr`, `aligned`, `nonnullAligned` (definition quoted above). A zero-size contract that forbids null without requiring alignment (the shape of the documented requirements of `read_unaligned`/`write_unaligned` quoted under the prior art of `delete-zero-size-access-equivalence-sufficient-conditions`) is not among them; it agrees with `nonnullAligned` at alignment 1 and with no constructor at larger alignments. Within the toy, `K ≠ .nonnullAligned` means "the contract permits null".
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `delete-zero-size-access-equivalence-exact-condition`

- The condition is not "`pre₀` holds on every reachable state": that is sufficient (`deleteZeroSizeAccess_equivPP_of_zeroPre_reachable`) but not necessary (`deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure`).
- The continuation is run in the target program (loops re-entering block `l` see the deleted version).
- `GoesWrongFrom` requires reaching UB in finitely many steps: a continuation that diverges does not satisfy the right-hand sides.
- Reachability (`ReachableAt`) ranges over all initial toy states, including runs that reach UB later; no calling context, type invariant or precondition on inputs (such as a caller-guaranteed aligned pointer) is modelled.
- Behaviours record emitted values and no final state: `Beh.term` discards the final locals and memory, so `RefinesPP`, `RefinesWT`, `EquivPP` and `EquivWT` neither establish nor refute preservation of final states or of `wp` (`copyLoopLowering_zeroCount_clobbers_counter` is a prefix-preserving refinement that changes a final local and does not preserve `wp`).
- Value validity is not modelled: a toy `read` produces no value, so a zero-size type of alignment 1 whose values cannot exist (such as Rust's `!`) has no counterpart, and reading it, which is UB in Rust for a reason the toy does not represent (prior art: the Rust Reference's invalid-value rule), lies outside these statements; they neither establish nor refute anything about it.
- `ZContract` has the three constructors `anyPtr`, `aligned`, `nonnullAligned` (definition quoted above). A zero-size contract that forbids null without requiring alignment (the shape of the documented requirements of `read_unaligned`/`write_unaligned` quoted under the prior art of `delete-zero-size-access-equivalence-sufficient-conditions`) is not among them; it agrees with `nonnullAligned` at alignment 1 and with no constructor at larger alignments. Within the toy, `K ≠ .nonnullAligned` means "the contract permits null".
- `copy src dst τ n` takes a literal natural-number count `n` (byte count `τ.size * n`, an unbounded natural-number product, so the zero-size edges are size 0 or count 0), not a run-time value, and does not check overlap of the two regions; counts computed at run time, overlapping copies and volatile accesses are not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `delete-zero-size-access-equivalence-sufficient-conditions`

- These are sufficient conditions; the exact condition is `deleteZeroSizeAccess_equivPP_iff`.
- `ZContract` has the three constructors `anyPtr`, `aligned`, `nonnullAligned` (definition quoted above). A zero-size contract that forbids null without requiring alignment (the shape of the documented requirements of `read_unaligned`/`write_unaligned` quoted under prior art) is not among them; it agrees with `nonnullAligned` at alignment 1 and with no constructor at larger alignments. Within the toy, `K ≠ .nonnullAligned` means "the contract permits null".
- Value validity is not modelled: a toy `read` produces no value, so a zero-size type of alignment 1 whose values cannot exist (such as Rust's `!`) has no counterpart, and reading it, which is UB in Rust for a reason the toy does not represent (prior art: the Rust Reference's invalid-value rule), lies outside these statements; they neither establish nor refute anything about it.
- Alignment 0 is a degenerate edge of the toy (`aligned 0 p` holds iff `p = 0`, `aligned_zero_iff`, by the Euclidean `Int` remainder `p % 0 = p`); the statements quantify over it but no intended contract uses it.
- Reachability (`ReachableAt`) ranges over all initial toy states, including runs that reach UB later; no calling context, type invariant or precondition on inputs (such as a caller-guaranteed aligned pointer) is modelled.
- `copy src dst τ n` takes a literal natural-number count `n` (byte count `τ.size * n`, an unbounded natural-number product, so the zero-size edges are size 0 or count 0), not a run-time value, and does not check overlap of the two regions; counts computed at run time, overlapping copies and volatile accesses are not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `delete-zero-size-access-equivalence-despite-pre-failure`

- Shows that "`pre₀` holds on every reachable state" is not necessary for an equivalent deletion; it is one instance, not a description of all such programs.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `zero-size-deletion-erases-ub-instances`

- Not a whole-trace equivalence also implies not a prefix-preserving equivalence (`equivWT_of_equivPP`).
- The loop lowering is checked for count 0; for counts of at least 1 nothing is proved here.
- `RefinesPP` for the loop lowering holds because behaviours ignore final states: at the count 0 of this card, under every contract and from every input state, `copyLoopProg 0 1 2 ⟨4, 4⟩ 0` sets its counter local `2` to 0 and leaves locals `0` and `1` unchanged (`copyLoopProg_zeroCount_run`; the loop body, which advances locals `0` and `1`, does not run at count 0; `copyLoopProg_zeroCount_preserves_src_dst` is the concrete instance with locals `8, 12, 42` under `aligned`), and `copyLoopLowering_zeroCount_clobbers_counter` shows that `wp` for a postcondition reading local 2 does not transfer from the source to the lowering.
- `copy src dst τ n` takes a literal natural-number count `n` (byte count `τ.size * n`, an unbounded natural-number product, so the zero-size edges are size 0 or count 0), not a run-time value, and does not check overlap of the two regions; counts computed at run time, overlapping copies and volatile accesses are not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `insert-zero-size-access-exact-condition`

- If `i` is at least the number of statements, the access is inserted before the terminator, and `(l, i)` denotes that point. If `l` is outside the block list, `insertStmt P l i s` is `P` and `P.blk l` is `Block.unreach`; both sides of each equivalence then hold.
- Hoisting (insert at one point, delete at another) is not characterized as a whole; `hoistZstRead_out_of_branch_not_refinesWT` is a counterexample and `hoistZstRead_anyPtr_equivPP` an instance in which hoisting is an equivalence.
- Reachability (`ReachableAt`) ranges over all initial toy states, including runs that reach UB later; no calling context, type invariant or precondition on inputs (such as a caller-guaranteed aligned pointer) is modelled.
- Value validity is not modelled: a toy `read` produces no value, so a zero-size type of alignment 1 whose values cannot exist (such as Rust's `!`) has no counterpart, and reading it, which is UB in Rust for a reason the toy does not represent (prior art: the Rust Reference's invalid-value rule), lies outside these statements; they neither establish nor refute anything about it.
- `copy src dst τ n` takes a literal natural-number count `n` (byte count `τ.size * n`, an unbounded natural-number product, so the zero-size edges are size 0 or count 0), not a run-time value, and does not check overlap of the two regions; counts computed at run time, overlapping copies and volatile accesses are not modelled.
- `ZContract` has the three constructors `anyPtr`, `aligned`, `nonnullAligned` (definition quoted above). A zero-size contract that forbids null without requiring alignment (the shape of the documented requirements of `read_unaligned`/`write_unaligned` quoted under the prior art of `delete-zero-size-access-equivalence-sufficient-conditions`) is not among them; it agrees with `nonnullAligned` at alignment 1 and with no constructor at larger alignments. Within the toy, `K ≠ .nonnullAligned` means "the contract permits null".
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `insert-zero-size-access-sufficient-condition`

- This is a sufficient condition, not a necessary one: inserting a failing zero-size access immediately before an identical one is still a prefix-preserving refinement (`insertZstRead_before_failing_read_refinesPP`); the exact condition is `insertZeroSizeAccess_refinesPP_iff`.
- If `i` is at least the number of statements, `s` is inserted before the terminator; if `l` is outside the block list, `insertStmt` is the identity.
- Value validity is not modelled: a toy `read` produces no value, so a zero-size type of alignment 1 whose values cannot exist (such as Rust's `!`) has no counterpart, and reading it, which is UB in Rust for a reason the toy does not represent (prior art: the Rust Reference's invalid-value rule), lies outside these statements; they neither establish nor refute anything about it.
- `ZContract` has the three constructors `anyPtr`, `aligned`, `nonnullAligned` (definition quoted above). A zero-size contract that forbids null without requiring alignment (the shape of the documented requirements of `read_unaligned`/`write_unaligned` quoted under the prior art of `delete-zero-size-access-equivalence-sufficient-conditions`) is not among them; it agrees with `nonnullAligned` at alignment 1 and with no constructor at larger alignments. Within the toy, `K ≠ .nonnullAligned` means "the contract permits null".
- `copy src dst τ n` takes a literal natural-number count `n` (byte count `τ.size * n`, an unbounded natural-number product, so the zero-size edges are size 0 or count 0), not a run-time value, and does not check overlap of the two regions; counts computed at run time, overlapping copies and volatile accesses are not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `introducing-zero-size-access-introduces-ub`

- Not a refinement under whole-trace UB implies not a refinement under prefix-preserving UB (`refinesWT_of_refinesPP`).
- Does not show that hoisting a zero-size access is always unsound: under `anyPtr` the same hoist is an equivalence (`hoistZstRead_anyPtr_equivPP`); hoisting as a combined pass is not characterized here, and the insertion half is characterized by `insertZeroSizeAccess_refinesPP_iff`.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `ub-check-of-output-incomplete`

- Establishes incompleteness (a `UBFree` output does not certify a `UBFree` source), not that UB reported in the output is spurious: if the output whole-trace-refines the source, UB of the output is UB of the source (`not_ubFree_src_of_not_ubFree_tgt_of_refinesWT`).
- Checking the output is complete when every pass's input whole-trace-refines its output, including the empty pipeline (`ubFree_src_of_ubFree_output_of_revChainWT`).
- Concerns semantic UB-freedom and perfect checkers; it does not model any real checker's coverage.
- The toy has one UB class; per-class checking is not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `ub-check-of-output-complete-under-reverse-refinement`

- Reverse refinement (`RefinesWT K tgt src`, `RevChainWT`) does not make a pass a refinement: the UB-introducing pass from `pHalt` to `pUnreach` satisfies it (`revRefinement_admits_ub_introduction`). A whole-trace equivalence (`EquivWT`) satisfies both this reverse direction and the refinement direction, by definition.
- `UBFree` quantifies over all input states; passing a finite set of test inputs does not establish it.
- The toy has one UB class; the statement is about all UB, not a sub-class.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-arm-with-assume-equivalence`

- `dropArms` removes every arm with value `v` (a filter); for a switch with distinct arm values (as in a well-formed switch) that is a single arm. If `v` occurs in no arm and `ow` is an unreachable block, `dropArms` changes nothing and the `assume` is still appended.
- `IsUnreachableBlock` requires an empty statement list: a target block that emits before `unreachable` does not qualify (`pruneArmAssume_emit_before_unreachable_not_refinesPP`); target blocks with silent statements before `unreachable` are excluded by the hypothesis although pruning them may still preserve behaviours (not proved here).
- Here `assume c` is the UB-on-false compiler assumption: its total-correctness rule is `wp (assume c) Q = c ∧ wp Q` (`wpFrom_assume`), and `wp` at an `unreachable` terminator is false (`wpFrom_unreachable`); in Dijkstra-style calculi these are the rules of `assert c` and `abort`. It is not the miraculous verification-condition `assume c` (rule `c → wp Q`, with `wp (assume false) Q` true); these statements neither establish nor refute anything about that reading. `wp` is demonic total correctness: UB and divergence both make it false; partial correctness (`wlp`) is not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-otherwise-with-assume-equivalence`

- `pruneOtherwiseAssume` acts on single-arm switches; on a switch with any other number of arms it is the identity (`pruneOtherwiseAssume_two_arms`), and shapes with two or more arms are not covered by this statement.
- Here `assume c` is the UB-on-false compiler assumption: its total-correctness rule is `wp (assume c) Q = c ∧ wp Q` (`wpFrom_assume`), and `wp` at an `unreachable` terminator is false (`wpFrom_unreachable`); in Dijkstra-style calculi these are the rules of `assert c` and `abort`. It is not the miraculous verification-condition `assume c` (rule `c → wp Q`, with `wp (assume false) Q` true); these statements neither establish nor refute anything about that reading. `wp` is demonic total correctness: UB and divergence both make it false; partial correctness (`wlp`) is not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-arm-without-assume-refines`

- Not an equivalence in general (`pruneArm_pSw_refinesPP_not_equivWT`); `wp` does not transfer from target to source (`pruneArm_pSw_wp_transfers_one_way`).
- Here `assume c` is the UB-on-false compiler assumption: its total-correctness rule is `wp (assume c) Q = c ∧ wp Q` (`wpFrom_assume`), and `wp` at an `unreachable` terminator is false (`wpFrom_unreachable`); in Dijkstra-style calculi these are the rules of `assert c` and `abort`. It is not the miraculous verification-condition `assume c` (rule `c → wp Q`, with `wp (assume false) Q` true); these statements neither establish nor refute anything about that reading. `wp` is demonic total correctness: UB and divergence both make it false; partial correctness (`wlp`) is not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-arm-without-assume-exact-condition`

- The condition is evaluated in the target program; if `ow` loops back to block `l`, the pruned switch is used.
- `GoesWrongFrom` requires reaching UB in finitely many steps; a redirected target that diverges does not satisfy the condition.
- `EquivPP` and `EquivWT` compare behaviours, which ignore final states; `wp` equivalence is not stated in this card.
- Reachability (`ReachableAt`) ranges over all initial toy states, including runs that reach UB later; no calling context, type invariant or precondition on inputs (such as a caller-guaranteed aligned pointer) is modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-arm-without-assume-unreachable-otherwise`

- A sufficient condition; the exact condition is `pruneArm_equivPP_iff`.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-arm-without-assume-invariant`

- `hinv` quantifies over all reachable states (`ReachableAt`), not over the runs that never reach UB (`FactOnDefinedRuns`): an unreachable arm for `v` makes `x ≠ v` a fact on the non-UB runs but not a reachable-state invariant, and pruning it without `assume` is then not an equivalence (`pSw_fact_not_invariant`).
- Not a special case of `pruneArm_equivPP_iff`, which assumes that the pruned label is an unreachable block (that is why this card is labelled substantive).
- Reachability (`ReachableAt`) ranges over all initial toy states, including runs that reach UB later; no calling context, type invariant or precondition on inputs (such as a caller-guaranteed aligned pointer) is modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-arm-without-assume-not-equivalence-and-vc-one-way`

- Verification results about the pruned program do not transfer back to the source in this instance; the positive control shows they do when the `assume` is kept.
- Does not show that pruning without `assume` always breaks equivalence or `wp` transfer back to the source: when `ow` is also unreachable, or `x ≠ v` holds on every reachable state at the switch, pruning without `assume` is a prefix-preserving equivalence (`pruneArm_equivPP_of_otherwise_unreachable`, `pruneArm_equivPP_of_invariant_ne`).
- Here `assume c` is the UB-on-false compiler assumption: its total-correctness rule is `wp (assume c) Q = c ∧ wp Q` (`wpFrom_assume`), and `wp` at an `unreachable` terminator is false (`wpFrom_unreachable`); in Dijkstra-style calculi these are the rules of `assert c` and `abort`. It is not the miraculous verification-condition `assume c` (rule `c → wp Q`, with `wp (assume false) Q` true); these statements neither establish nor refute anything about that reading. `wp` is demonic total correctness: UB and divergence both make it false; partial correctness (`wlp`) is not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `replace-block-by-unreachable-exact-condition`

- Models replacing a single block `b`, not a pass that iterates to a fixed point over several blocks.
- A label outside the program already denotes `Block.unreach`; replacing it changes nothing.
- Whether divergence may itself be UB (a forward-progress assumption) is not modelled; in this toy a silently diverging run is a defined behaviour. Total-correctness `wp` maps both divergence and UB to false and does not distinguish them.
- Reachability (`ReachableAt`) ranges over all initial toy states, including runs that reach UB later; no calling context, type invariant or precondition on inputs (such as a caller-guaranteed aligned pointer) is modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `replace-block-by-unreachable-counterexamples`

- The whole-trace half of the first statement is itself a positive control: under whole-trace UB, backward propagation over an event is a refinement in this instance.
- `replaceUnreachable_diverging_loop_not_refinesWT` relies on silent divergence being a defined behaviour (`Beh.div []`). Under a semantics with a forward-progress assumption that makes side-effect-free infinite loops UB, the replacement would be a refinement (not modelled here).
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-with-assume-preserves-ub-derived-facts`

- The theorem has no hypothesis on the pruned arm; whether the pruned program refines or equals the source is a separate result (`pruneArmAssume_equivPP`).
- `FactOnDefinedRuns` is a whole-run condition, not a prefix invariant: a fact may rely on UB that occurs after observable events, and folding a branch with it need not be a prefix-preserving refinement even on the unmodified source (`factOnDefinedRuns_fold_refinesWT_not_refinesPP`, where the fold is a whole-trace refinement).
- `FactOnDefinedRuns` is antitone in UB: every fact holds on the non-UB runs of an always-UB program (`factOnDefinedRuns_unreach`), although replacing a program by it is not a refinement in general (`not_refinesWT_halt_unreach`). Preserving such facts therefore neither establishes nor implies that a transformation is a refinement.
- At block `l` itself, index `i' = (P.blk l).stmts.length` denotes the switch in `P` and the point before the inserted `assume` in `pruneArmAssume P l v`; `F` holds there in the target because runs failing the `assume` are excluded as UB runs.
- Facts are state predicates at program points of the toy; analyses that summarise over paths are not modelled.
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

#### Non-claims: `prune-without-assume-loses-ub-derived-facts`

- In `pStale` the end-to-end result still refines the source; the failure there is that the fact-using pass is not a refinement of its own input, which breaks per-pass validation.
- In `pEmitFact` the composite (prune block 1 without `assume`, then fold block 0 with the fact computed on the source) is not a prefix-preserving refinement of the source, but the same fold applied to the source already fails, so that failure comes from the fact being a whole-run fact, not from its staleness. The whole-trace refinement proved for that composite is relative to the source `pEmitFact`; relative to its actual input `pruneArm pEmitFact 1 5` the composite is not a whole-trace refinement (`emitFact_fold_after_pruneArm_not_refinesWT_input`). No instance is given here in which such a composite fails to be a whole-trace refinement of the source.
- Losing a fact requires pruning to erase UB: when `pruneArm` is an equivalence (for example `pruneArm_equivPP_of_otherwise_unreachable`, `pruneArm_equivPP_of_invariant_ne`), the non-UB runs are unchanged and such facts are preserved (not proved here).
- The toy language is deterministic, with integer locals and a byte-granular dereferenceability map: no stored values, no provenance, no allocation or deallocation, no concurrency and no calls. It has a single UB class (failed access precondition, failed `assume`, reaching `unreachable`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, Miri, LLVM or the Rust standard library.

### Escape hatches

For each counterexample result, a nearby setting in which its conclusion fails (its positive control, kernel-checked) or a stated weakening that would defeat it:

- `delete-zero-size-access-equivalence-despite-pre-failure`: Without the second read (`pReadZst4`), deleting the read is not an equivalence. (`zstRead_misaligned_deletion_erases_ub`)
- `zero-size-deletion-erases-ub-instances`: The same deletion at alignment 1 under `aligned` is an equivalence. (`zstRead_align_one_alignedContract_deletion_equivPP`)
- `introducing-zero-size-access-introduces-ub`: Hoisting the same read under `anyPtr` is a prefix-preserving equivalence; insertion where `pre₀` holds on every reachable state is an equivalence. (`hoistZstRead_anyPtr_equivPP`, `insertZeroSizeAccess_equivPP_of_zeroPre_reachable`)
- `ub-check-of-output-incomplete`: When the source whole-trace-refines the output (for example an equivalence), checking the output is complete. (`ubFree_positive_control_instance`, `ubFree_src_of_ubFree_output_of_revChainWT`)
- `prune-arm-without-assume-not-equivalence-and-vc-one-way`: With the `assume` kept, the same pruning is an equivalence with equal `wp`. (`pruneArmAssume_pSw_equivPP_and_wp`)
- `replace-block-by-unreachable-counterexamples`: A block from which every run reaches UB silently can be replaced. (`replaceUnreachable_pSilentToUnreach`)
- `prune-without-assume-loses-ub-derived-facts`: With the `assume` kept, the fact-based fold is a prefix-preserving refinement of its input `pruneArmAssume pStale 0 5` (also one of this card's results, quoted in its statement block). (`staleFact_fold_after_pruneArmAssume_refinesPP`)
- `prune-without-assume-loses-ub-derived-facts`: losing a fact requires pruning to erase UB; when `pruneArm` is an equivalence (for example under `pruneArm_equivPP_of_otherwise_unreachable` or `pruneArm_equivPP_of_invariant_ne`), the non-UB runs are unchanged and such facts are preserved (not proved here).

### Hypotheses whose tightness is unknown

None: every hypothesis in every ledger is marked `tight` and names a kernel-checked counterexample.

### Disproved or dropped draft statements

None: no statement of this package was disproved, weakened or dropped; every result listed in Summary is proved as quoted.

### Not examined

- Rust programs, rustc, Miri and LLVM were not run; no claim about their behaviour is made beyond the quoted documentation (see the derived bridges in the cards).
- Loop lowering of copies with counts of at least 1, deletion or insertion of nonzero accesses, and deletion of `assume` statements were not examined (see the non-claims of the zero-size results).

## Evidence

### Kernel check

- Toolchain: Lean 4 `leanprover/lean4:v4.34.1` (leanprover/lean4 tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib; the Lake project `lean/` has no dependencies.
- A fresh `lake build` of `lean/` (Lake artifact cache disabled) succeeds with no errors and no warnings. Observed 2026-11-21.
- Axiom audit: every one of the 983 declarations of the library `Toy` depends on at most `propext`, `Classical.choice` and `Quot.sound` (computed with `Lean.collectAxioms`; per-declaration lists in `audit/axioms.json`). Outside comments, the Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declaration, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`.
- Statement hashes: `audit/statements.json` records 299 names. For each, `statement_sha256` is the SHA-256 of the Lean `repr` of the declaration's type, and `closure_sha256` is the SHA-256 of the sorted, newline-joined lines `name : repr(type)` (followed by ` := repr(value)` for non-theorems) of every package constant reachable from the type through types, definition bodies and constructors (theorem bodies excluded).

### Per-result record

Axioms: `P` = `propext`, `C` = `Classical.choice`, `Q` = `Quot.sound`; `—` = none.

#### `delete-zero-size-access-refines`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `deleteZeroSizeAccess_refinesPP` | result | P, C, Q | `1c0f30becb03feab92b8414e71e57d580d6c037c69e064ad42904d193f15bafb` | `098d745fe0979459f60ad4c8c3f5fbd3200869c4495b90e79bc0ce0e49adb6c8` |
| `deleteZeroSizeAccess_refinesPP_nonvacuous` | non-vacuity witness | P | `f2c9d36bd113be7002c06737eb7ae42a91f477ec9201818bde6b835ae93c4738` | `df0848250bab0a80e12f7b3ae220dc8767132dcb0f9b9d16f3a80d03114fd1e5` |
| `deleteStmt_hs_counterexample` | counterexample (`hs`) | P, C, Q | `c449ed1e8ae6a8c4de39b690e24243fc12e8f18e3d6f920bb62c1601263fd39e` | `4287b7bdb30810192cb2a8d8c3ee0cdb11adb05a344f06f16d2f1be95a8f972c` |
| `deleteStmt_hz_counterexample` | counterexample (`hz`) | P | `8960701853324f8e3acb1955aabf2d5a4719edc27186a3165c1ff0851d725575` | `4287b7bdb30810192cb2a8d8c3ee0cdb11adb05a344f06f16d2f1be95a8f972c` |

#### `delete-zero-size-access-equivalence-exact-condition`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `deleteZeroSizeAccess_equivPP_iff` | result | P, C, Q | `5a4db130502208dfae50b9fbf7018db8e8f509eda1e3761893579d17b720db69` | `d0ae7f60d892140a0eab10ebc5b9472a78e327576f3a894def0790df3f30b4a1` |
| `deleteZeroSizeAccess_equivWT_iff` | result | P, C, Q | `fbbf2e44d342eeca4d761cd1836b062d7e0666bf9e69d4ecbdf646f22038bcc4` | `da419af52732e1fbe96c07e0f204ae437d89a9aa7c32e3907115730a951d366b` |
| `deleteZeroSizeAccess_iff_nonvacuous` | non-vacuity witness | P | `df18aeeb48c0d6dc26c2dc3f68008ee5a84404e53850a878a2cef2bd9876239c` | `17a2fef6d8e4b85cd23a5fb14d5197203d162a72c7ec00c06e7ea32d1ebdafb3` |
| `deleteStmt_hs_counterexample` | counterexample (`hs`) | P, C, Q | `c449ed1e8ae6a8c4de39b690e24243fc12e8f18e3d6f920bb62c1601263fd39e` | `4287b7bdb30810192cb2a8d8c3ee0cdb11adb05a344f06f16d2f1be95a8f972c` |
| `deleteStmt_hz_counterexample` | counterexample (`hz`) | P | `8960701853324f8e3acb1955aabf2d5a4719edc27186a3165c1ff0851d725575` | `4287b7bdb30810192cb2a8d8c3ee0cdb11adb05a344f06f16d2f1be95a8f972c` |

#### `delete-zero-size-access-equivalence-sufficient-conditions`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `deleteZeroSizeAccess_equivPP_of_zeroPre_reachable` | result | P, C, Q | `edc28599a9f92ed18d85c95e5bb544f430e52c2c741650dcfbd765334814a46d` | `d9bc3e45c09170d68403f081a47601d0c50704351eeae28c19ce56701a45fc7a` |
| `deleteZeroSizeAccess_equivPP_of_anyPtr` | result | P, C, Q | `99bf1022408412ec821eb00c600ae84dfaee6c89b56166a3c00c8a01ae08be6d` | `d0b6657a3263def3e3eb4302f9993672a6bf3816de4bfe2ea553e25b98836d12` |
| `deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted` | result | P, C, Q | `3a72ce4a68df5b38ea7a2fc6d6244b52e0350274cd6e44f38b224d7f6b9290e6` | `651aed8913f7ea1f7a49227271e00d70289f7abda590dacec92a9068797c936a` |
| `deleteZeroSizeAccess_sufficient_nonvacuous` | non-vacuity witness | P, C, Q | `6c86afe4111aa1f7a8fe742aa53619b45038a949b794c6b52d86be68f4cb25c6` | `a54d95a9010cdf6621b9ee83dfa3286b07b0d19e279e7f53f10b4ab4351ffa4a` |
| `deleteStmt_hs_counterexample` | counterexample (`hs`) | P, C, Q | `c449ed1e8ae6a8c4de39b690e24243fc12e8f18e3d6f920bb62c1601263fd39e` | `4287b7bdb30810192cb2a8d8c3ee0cdb11adb05a344f06f16d2f1be95a8f972c` |
| `deleteStmt_hz_counterexample` | counterexample (`hz`) | P | `8960701853324f8e3acb1955aabf2d5a4719edc27186a3165c1ff0851d725575` | `4287b7bdb30810192cb2a8d8c3ee0cdb11adb05a344f06f16d2f1be95a8f972c` |
| `deleteZeroSizeAccess_pReadZst4_counterexample` | counterexample (`hpre`) | P | `86985933f6ab2e2e64d7cb897fec134fe77fd3350bc6893b5edbc9d1cc348502` | `0f98a5c3cf9393ea51ae0477adde283e8b50b62d6de092c9792741e965521ced` |
| `deleteZeroSizeAccess_pReadZst4_counterexample` | counterexample (`K = .anyPtr`) | P | `86985933f6ab2e2e64d7cb897fec134fe77fd3350bc6893b5edbc9d1cc348502` | `0f98a5c3cf9393ea51ae0477adde283e8b50b62d6de092c9792741e965521ced` |
| `deleteZeroSizeAccess_pReadZst1_nonnull_counterexample` | counterexample (`hK`) | P, C, Q | `ee5d15551a742de2cf142f832078613aeade8d1575d050500eaeba116d171b12` | `fe4864169043de3c9fc0e7b365a76ed46c48fc044b6d468bcfcfd6a2cdf8a7b3` |
| `deleteZeroSizeAccess_pReadZst4_counterexample` | counterexample (`ha`) | P | `86985933f6ab2e2e64d7cb897fec134fe77fd3350bc6893b5edbc9d1cc348502` | `0f98a5c3cf9393ea51ae0477adde283e8b50b62d6de092c9792741e965521ced` |

#### `delete-zero-size-access-equivalence-despite-pre-failure`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure` | result | P | `fbe88547204ce0cbf2ed305d2dc04a97525df10dde03bf91ff8db91a9f273d08` | `c2d8972c0ffe45d18469feba5e4263d3b093f7639ec570b5800a22685ed332ca` |
| `zstRead_misaligned_deletion_erases_ub` | positive control | P | `781fdc3fb0ab26c5a1c146db906f7e25b07e727b26eba4453de0c1461ea4b344` | `faf80828f20e46d4d54e4844508a6cc427ca21e7a244ae893825156aa0cb4d19` |

#### `zero-size-deletion-erases-ub-instances`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `zstRead_misaligned_deletion_erases_ub` | result | P | `781fdc3fb0ab26c5a1c146db906f7e25b07e727b26eba4453de0c1461ea4b344` | `faf80828f20e46d4d54e4844508a6cc427ca21e7a244ae893825156aa0cb4d19` |
| `zeroCountCopy_misalignedSrc_deletion_erases_ub` | result | P | `a6d27634755c201b8645282cf8b676d8c790e0e4517522984aab71157a703e2a` | `717e9bddf46beacc953755afe624da55ee2d3e24457f65cc6c61447e006d9fc5` |
| `zstRead_null_nonnullContract_deletion_erases_ub` | result | P, C, Q | `e5f817874a398b99a6144754ea08787a408c7e336f02c1a7139a34f3bc2d498c` | `0d48d5999e836f3768d12b604d520cfefbee8a3805f69294c303f6c0135ef68d` |
| `copyLoopLowering_zeroCount_erases_ub` | result | P, Q | `8afd833c39983e768cf2f2132774e126b34523e4de454b8e86f5fe8d8d43e24e` | `e530b650eb7c2eb8df6084e4b69e8438f12348abbf20ac081e18209284d8e262` |
| `copyLoopLowering_zeroCount_clobbers_counter` | result | P, C, Q | `813180f10549db502c4f289ddb44e122a6d54e9b9463c668de83a9796573d9d8` | `343f078f156026ead40562bd53d42875b380cd6caf943c7fefed00816b1e41f4` |
| `zstRead_align_one_alignedContract_deletion_equivPP` | positive control | P, C, Q | `c4c40eb2c86181e046236f80fb9e29da9371ea6c2274e874ba01ecbafcef3563` | `e8ed8cb16a36e32bd2c98f1af673889bcdaef4cf8636dcf5d053bd8558fe0811` |

#### `insert-zero-size-access-exact-condition`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `insertZeroSizeAccess_refinesPP_iff` | result | P, C, Q | `5dd2870021b3247e16bb7a7e4f246c2b34c20d6ece17919579be67525c3dc945` | `8e50c893cc780c54c237f18be8fa1b0423601e0213c1a7e5f59999ffe82ee723` |
| `insertZeroSizeAccess_refinesWT_iff` | result | P, C, Q | `f8ce3e61e9c972b89f3075b335f1aa784f4135f8f41a178f4ed57fc4ca3d6c5a` | `6030170a1f8a077fd1de408d78c98043728091e772cfbf21bd445ff3bed0be39` |
| `insertZstRead_before_failing_read_refinesPP` | non-vacuity witness | P | `6a86ffc23669baf526e13c4d0e5a101d051906197de576cae8a11685c794e68a` | `dcd2216fe04eb126bb76619bc345a864b9794fa85659953b864a86e741f8f29b` |
| `insertEmit_counterexample` | counterexample (`hz`) | P | `2a931b1058861756a5136c4b3fa931b23889bc5ce031e51cf6e0dae05789047b` | `5fdd988ea76b76d14ceb2e9c1144dc65acb294f94625ded0aa9d0e13295d194a` |

#### `insert-zero-size-access-sufficient-condition`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `insertZeroSizeAccess_equivPP_of_zeroPre_reachable` | result | P, C, Q | `d05c602d7e36aaaf12691e1f311b94590bf9abb037d672d095dd552449d356f3` | `5d3c52fe8d787a970c59217a03ff299855779d49692d5e911d874ede2e228821` |
| `insertZeroSizeAccess_anyPtr_nonvacuous` | non-vacuity witness | P | `81b8b16d29d17a58a2a75888eed0543de7912463df9d59deecea367a2945ce1d` | `647fac77d9ae70bc6c24b36d9b0dab792cca80d31caf5febd34b3517d971dd8f` |
| `insertEmit_counterexample` | counterexample (`hz`) | P | `2a931b1058861756a5136c4b3fa931b23889bc5ce031e51cf6e0dae05789047b` | `5fdd988ea76b76d14ceb2e9c1144dc65acb294f94625ded0aa9d0e13295d194a` |
| `insertZeroSizeAccess_hpre_counterexample` | counterexample (`hpre`) | P | `f1c2e04dd48fe56a1cefa1f3c274a3b74e319f938e488a6f2cb56e4441eac0d4` | `259dfb42a60c6dac45dd399cb01c859d3bde6b91b7abe7680f54816fc0f1fbe2` |

#### `introducing-zero-size-access-introduces-ub`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `insertZstRead_misaligned_not_refinesWT` | result | P | `0c08a36aec6ea6cdda73606fd885a1db0db8d433e91d14d9f0e78a3a5c0195bf` | `c38e9ea478ce395c0e5fbdffaf1e8c0217e1064d6dbae3df9b23bd0a20380850` |
| `hoistZstRead_out_of_branch_not_refinesWT` | result | P | `f074ff1935f125a0f92f5f65dbabf9ce2ca2539690f97d21553a08c4e9aed781` | `b5c348fda589a30aec3e7f418b9f4cc4b9498bd5f469757a9b3882bf7749a626` |
| `hoistZstRead_anyPtr_equivPP` | positive control | P | `9a2cae4ce90138ef831e768dbc3403498f4e4c4c1a6d062e0b0b3ac48d3ff7fc` | `05b1586210ffd51abe990362ae4f531b49bfe7d733a607cc2afd08bd486502c2` |
| `insertZeroSizeAccess_equivPP_of_zeroPre_reachable` | positive control | P, C, Q | `d05c602d7e36aaaf12691e1f311b94590bf9abb037d672d095dd552449d356f3` | `5d3c52fe8d787a970c59217a03ff299855779d49692d5e911d874ede2e228821` |

#### `ub-check-of-output-incomplete`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `ubCheck_of_output_misses_source_ub` | result | P | `ff64d03110843780adc305e5754d776f83c2d25780856c4d8cbcd0f62158f4a5` | `7198fc35699c87767c38bbcf850f4cf6afbb5d208321462b7f6a5c57a43ce5ab` |
| `exactUBChecker_exists` | non-vacuity witness | P, C, Q | `003105a3addca6f9f9c4c4f5c67f0a64c1e7ac5559f13e1c405c985383e3ad8f` | `6add152d6a69604d1f9313f8f19874b93ed5c804abe9c20754b41fc1bf10ce22` |
| `ubFree_positive_control_instance` | positive control | P, C, Q | `c2a793e7e5e0c8ad10f32b841596b6d9626995ab74a1df801f84e8f278ddd93f` | `7a4c8c3ed80a521c2df2f1869efaaf7714c3804d5244835b7a89307b57d0bca8` |
| `ubFree_src_of_ubFree_output_of_revChainWT` | positive control | P | `a499bd37c5b559d6f516b44d95dcbbba5bd583b2ed7ac6aa4868505dd12fcd4a` | `d6ba87db16261b09c349802f7392ad252e23b72fbb1cfdf0b8c1ede0ec405cea` |

#### `ub-check-of-output-complete-under-reverse-refinement`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `ubFree_src_of_ubFree_tgt_of_refinesWT_rev` | result | P | `449a177c62e52d8f2211dd282d47020c0e7685993bea219c21d054e231dd58c5` | `39cb0a3d0eaae03977523a80b1fb5506caddfe01c19c4b6fa6576eaf7af9a48f` |
| `ubFree_src_of_ubFree_output_of_revChainWT` | result | P | `a499bd37c5b559d6f516b44d95dcbbba5bd583b2ed7ac6aa4868505dd12fcd4a` | `d6ba87db16261b09c349802f7392ad252e23b72fbb1cfdf0b8c1ede0ec405cea` |
| `ubFree_src_of_ubFree_tgt_of_equivPP` | result | P | `28c6f37c29bd66325bcc89b540ce9b6b155dfa1b443285ae1c3c80032505da18` | `b6824d3e03e354668ccf4b7a9d961dfd15376bfc8280480cefbeda564aa54f60` |
| `ubFree_src_of_ubFree_tgt_nonvacuous` | non-vacuity witness | P, C, Q | `1e82e5836e6bbf3c26f245ed1805847f669daa086bbae066822dec44bf6a2014` | `0689e301c84c9e7519c38377f0fd05e19d614e84f066aaa883276d8637495d9c` |
| `ubCheck_pReadZst4_hypotheses_counterexample` | counterexample (`hrev`) | P | `c511bbc7ae0e98a7a9c67805be30dfdb4f8e2199056f856ca718e19e2a322474` | `ac4691391a4ae35f88ec67841ce1da917eb7a3456a89d7bf3e9538b90ed499e5` |
| `ubFree_output_hypothesis_counterexample` | counterexample (`htgt`) | P | `0502c6844f63b73b9dc98f83cbecec46cb56e75fe15d783d6a1a87f8e6101249` | `d3f942fa7f36b7c6111ede97edb64a992424fa4933b80621cb24c526799fd5ab` |
| `ubCheck_pReadZst4_hypotheses_counterexample` | counterexample (`RevChainWT K P Qs`) | P | `c511bbc7ae0e98a7a9c67805be30dfdb4f8e2199056f856ca718e19e2a322474` | `ac4691391a4ae35f88ec67841ce1da917eb7a3456a89d7bf3e9538b90ed499e5` |
| `ubFree_output_hypothesis_counterexample` | counterexample (`UBFree K ((P :: Qs).getLast _)`) | P | `0502c6844f63b73b9dc98f83cbecec46cb56e75fe15d783d6a1a87f8e6101249` | `d3f942fa7f36b7c6111ede97edb64a992424fa4933b80621cb24c526799fd5ab` |
| `ubCheck_pReadZst4_hypotheses_counterexample` | counterexample (`h`) | P | `c511bbc7ae0e98a7a9c67805be30dfdb4f8e2199056f856ca718e19e2a322474` | `ac4691391a4ae35f88ec67841ce1da917eb7a3456a89d7bf3e9538b90ed499e5` |

#### `prune-arm-with-assume-equivalence`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArmAssume_equivPP` | result | P, C, Q | `4f29460c58e1f0b1cacb5b08b0b9ff302b4e78ac2d306f3b758de9fc9c0f0026` | `e3ebb0ed3281642bb15d56e3861b7725e988c2ce1dc67abf892d6982e4227d26` |
| `pruneArmAssume_equivWT` | result | P, C, Q | `08e055c2eac10e802b74e114650d2bb7f8ae439356650f2e8c5af8f2bc9e0218` | `2effa901ac9baa81bd3f067733ab422c322ff12bf7b100ac14b7903b13d2ccfc` |
| `pruneArmAssume_wp_iff` | result | P, C, Q | `1994a9b3c064ec1bdf2804229fcd15ca2b3bce57d9970d85aa33d5fd51b4442c` | `aeac1bbafad6b6a7a9656b6af42db04c2bf04a22b76566a4d67ec4236e3487ee` |
| `pSw_hyps` | non-vacuity witness | P | `7cc59f17833bcf3003883caecb16e7441963e933a187840986a9e9d729138d3a` | `7112c7f69d8cf4e7e7d886057cb1ba322bb4188bd26c0e6726be293d123d0bbe` |
| `pruneArm_hterm_counterexample` | counterexample (`hterm`) | P | `ecb7aa946001091a741acc7f9a45900bc20cfd7bb456312e2ba7bbc3a93fdb11` | `a5af8baf5c5463276c81af6206c442320954db2146e10cea42b47e28f6f5fb46` |
| `pruneArm_hU_counterexample` | counterexample (`hU`) | P | `3bbd6fbb6db643fac9daef78f1509573c82ae653c10bfe3e4a2d7680b3460a82` | `a5af8baf5c5463276c81af6206c442320954db2146e10cea42b47e28f6f5fb46` |
| `pruneArmAssume_emit_before_unreachable_not_refinesPP` | counterexample (`hU`) | P, Q | `6d7c9008201f1c7e526f4c7d6eee2d9956b59d1f8f3db4b59fc26d64c461f6d3` | `18afcccc736846cd9e403d4df929ab715591f9eb63b207fd61581798c5df0983` |

#### `prune-otherwise-with-assume-equivalence`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneOtherwiseAssume_equivPP` | result | P, C, Q | `e3f7f2490324d6abfe65eea7659a11166d05add0dcd42aea68c61412319e2765` | `5e0be4f3d595520f0f7c8056fccce1b4426c83b7396c3cf5b89383ebf944a0df` |
| `pruneOtherwiseAssume_wp_iff` | result | P, C, Q | `f60b1bdc58eae18c8a48f84ee2ae723f48f850c634b6485593eb5b842b3e7dbf` | `a3f7f109a326c304af0608c7cc2bfd8f8e47794c75b817d00917d5cbe0b2fedd` |
| `pSwOne_hyps` | non-vacuity witness | P | `901e27f598174f2125a3fb00115c861345c8ba602f2fb2a75535228f72c71fe4` | `1294bbb945052afd1498acd87a64f792b9ee487c15b07e797a5730ced6049bdd` |
| `pruneOtherwiseAssume_live_otherwise_not_refinesWT` | counterexample (`hterm`) | P | `ec3bed8466d527943a54bc6abea2cc96112b402fda484c57377481b1468f49f9` | `6700a263d6162af6d44a021727cc75992e1a6eac4064baac0ec262f8880db3cf` |
| `pruneOtherwiseAssume_live_otherwise_not_refinesWT` | counterexample (`hU`) | P | `ec3bed8466d527943a54bc6abea2cc96112b402fda484c57377481b1468f49f9` | `6700a263d6162af6d44a021727cc75992e1a6eac4064baac0ec262f8880db3cf` |

#### `prune-arm-without-assume-refines`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArm_refinesPP` | result | P, C, Q | `b85ab5b77b933e279b88f43f595f4c01c6409b9a5661f6552a6cae359808eabf` | `9261aadb830002c355e75dee9153c00f5bb942fed94ed04f639831929d1078b6` |
| `pruneArm_wp_of_wp_src` | result | P, Q | `36acd75af6a0068084ad2d9c19a73da76bc4b600644d0d0dfb741c3c48f0d9f1` | `2f7e1db6108e4d4617a42bb52099e3fe25211775fb6ff9f1a68a8931339ab637` |
| `pSw_hyps` | non-vacuity witness | P | `7cc59f17833bcf3003883caecb16e7441963e933a187840986a9e9d729138d3a` | `7112c7f69d8cf4e7e7d886057cb1ba322bb4188bd26c0e6726be293d123d0bbe` |
| `pruneArm_hterm_counterexample` | counterexample (`hterm`) | P | `ecb7aa946001091a741acc7f9a45900bc20cfd7bb456312e2ba7bbc3a93fdb11` | `a5af8baf5c5463276c81af6206c442320954db2146e10cea42b47e28f6f5fb46` |
| `pruneArm_hU_counterexample` | counterexample (`hU`) | P | `3bbd6fbb6db643fac9daef78f1509573c82ae653c10bfe3e4a2d7680b3460a82` | `a5af8baf5c5463276c81af6206c442320954db2146e10cea42b47e28f6f5fb46` |

#### `prune-arm-without-assume-exact-condition`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArm_equivPP_iff` | result | P, C, Q | `1ecf9776363bbc72581943172c7cb27d664c4c63c7c319ab4fe02c212f799289` | `ddeec7087234dfc6fe9b11ab0ba626c490de05456238d00d5b990baa1af6080a` |
| `pruneArm_equivWT_iff` | result | P, C, Q | `6a084e2078d47d31fc8bf541f0278ab93f7687e13672c123ad2721b6d1e2910a` | `69a81b1706b44edc04854e9e2ef1dd5cdf5b074a20e1b96ef10dfff762f3cbc1` |
| `pSwAssumeOw_hyps` | non-vacuity witness | P | `0bda71567f3657fa58ee18f0fe7c98e54d040cf697f90177cc00dddc58259451` | `011e08423e756af4c52b7aae566e8a64f4066737a77c049c7c45ed5929e05cd0` |
| `pruneArm_iff_counterexample` | counterexample (`hterm`) | P | `3175632a2306a60067fb497a9322addea7aa82a1d014b1b223ffd0ea2ec99b07` | `154fa1ae17f94dc5e6deff3e62741f027563417ccfa43a9f0512abcadeb3a5a0` |
| `pruneArm_iff_counterexample` | counterexample (`hU`) | P | `3175632a2306a60067fb497a9322addea7aa82a1d014b1b223ffd0ea2ec99b07` | `154fa1ae17f94dc5e6deff3e62741f027563417ccfa43a9f0512abcadeb3a5a0` |

#### `prune-arm-without-assume-unreachable-otherwise`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArm_equivPP_of_otherwise_unreachable` | result | P, C, Q | `bf2997d5e96bd5bebb7a50d68b02e6a7a8525c3c312babbc02bf41934756eff6` | `1d9e266ade264128529d1d8025f00c5736b60457cb86196aaaf7711a07efdf35` |
| `pruneArm_equivPP_of_otherwise_unreachable_nonvacuous` | non-vacuity witness | P | `82528930ff542b805ef2e69a1ffc86240b40f770fcea92abaab01e6b8d3584a4` | `ba3b3d7ae266f76e448e8f251bdb6cfd191293f50e7b139271e28f18a23e937e` |
| `pruneArm_iff_counterexample` | counterexample (`hterm`) | P | `3175632a2306a60067fb497a9322addea7aa82a1d014b1b223ffd0ea2ec99b07` | `154fa1ae17f94dc5e6deff3e62741f027563417ccfa43a9f0512abcadeb3a5a0` |
| `pruneArm_iff_counterexample` | counterexample (`hU`) | P | `3175632a2306a60067fb497a9322addea7aa82a1d014b1b223ffd0ea2ec99b07` | `154fa1ae17f94dc5e6deff3e62741f027563417ccfa43a9f0512abcadeb3a5a0` |
| `pruneArm_pSw_hyps_counterexample` | counterexample (`hOw`) | P | `c070d2980db62b53d824fdc20fc086aca3b8794ebcc0abc89d1e1c5da531bcb2` | `52e5dde709ac0ed3f650bab0af8a5e616bc68eb7e1992204f17710af60205dc3` |

#### `prune-arm-without-assume-invariant`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArm_equivPP_of_invariant_ne` | result | P, C, Q | `9b5db4569593434bb2732ba9099787200db8974249e66c483fb8ccfb440af787` | `a770fb2b0fd4f43ecfdec6e97e4423afcb931d6165d49b0ea9781f98ce78fafa` |
| `pruneArm_equivPP_of_invariant_ne_nonvacuous` | non-vacuity witness | P, Q | `24f3761c2f45f3716827bd731cc8ff66ae9e93e5e709b766781e08edc7048233` | `b350a5c3f42574dd56eefb3aae9550ea4ef296b5092ead6bb0a855ca944120ef` |
| `pruneArm_equivPP_of_invariant_ne_live_arm_witness` | non-vacuity witness | P, C, Q | `f1b2b6b44d695f531077da3d48be3e0b53b3a67a53810b518d46883e6afffcb3` | `6deae0f4d80e310b70636c5e0ca88a3e835510848426f3c212c3daf618fae645` |
| `pruneArm_invariant_ne_hterm_counterexample` | counterexample (`hterm`) | P, Q | `b1b00fd18174d929b47a80cc6fba2662015a2f1d64feaf4ea34878e785176c58` | `2b1565646c577b8b03a32bba5e331a0c3666011af660705e0ab21a4357e540a6` |
| `pruneArm_pSw_hyps_counterexample` | counterexample (`hinv`) | P | `c070d2980db62b53d824fdc20fc086aca3b8794ebcc0abc89d1e1c5da531bcb2` | `52e5dde709ac0ed3f650bab0af8a5e616bc68eb7e1992204f17710af60205dc3` |

#### `prune-arm-without-assume-not-equivalence-and-vc-one-way`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArm_pSw_wp_transfers_one_way` | result | P | `542c25907a8e5b183c9bfc2d61b351201fd3bb4f5236435c423b1b0f1e33fb30` | `e5ded399e26e7a2f48810d4adc50e4f87e57f9abcd16395540e21c311b3246a7` |
| `pruneArm_pSw_refinesPP_not_equivWT` | result | P | `6b5af73a94cc669a658d37a28d147ed017936c42b2ab7dfae4115a58559729cf` | `5f281f1ffccd397c2518991551d691bdd10ef5d9fb19217acde9c8e2f626eab8` |
| `pruneArmAssume_pSw_equivPP_and_wp` | positive control | P, Q | `4867dba740fcf23a77b91484250629536c0cb08370430ff3b59054b9b3720134` | `e8a4c896195719324652889183e4cd42626cbfc8bd1c68f6bb4b9ee334d8747f` |

#### `replace-block-by-unreachable-exact-condition`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `replaceUnreachable_refinesPP_iff` | result | P, C, Q | `f5add085cdf54256b3a063723d21776f8c7ee1e765d9bef7ecd55387e3388fff` | `cec56e23478c153a4adab853efdd461b7b16a963d554423c3ee4a520de9eab43` |
| `replaceUnreachable_refinesWT_iff` | result | P, C, Q | `3732ce550a2a19459fb0f316eb649dc93a39b2aa5391d81def124633db58dfd2` | `6886d4394f6e3788f41e0b243401eb8fed35e7b4ccc6fa214160159ee36e81c7` |
| `replaceUnreachable_pSilentToUnreach` | non-vacuity witness | P | `f741254d5c9f47db6fb9c49bd599d806136808476fec600ffbbc87caf9c214d4` | `4a26a32486f6a14ba58964a118219d35f1d3b87861c6fe969fae198e846056d4` |

#### `replace-block-by-unreachable-counterexamples`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `replaceUnreachable_emit_before_unreachable` | result | P | `fc8ee0560de471511497298dbf4c03e39bb65f5b630f4661c94c9b40152afc71` | `36b3bdd3ff57f7b236db66ff00d04fe28d8ada48965e4eda9051e2199cdce683` |
| `replaceUnreachable_diverging_loop_not_refinesWT` | result | P | `9b15d04326f5afa69a5724dddfc9a7c5f6ef98b4ded9a4a986cfcf022a10dd5b` | `c0b21ce2e679a0b8df024c855409bd7b743c9212a8934b14e719398aed010491` |
| `replaceUnreachable_pSilentToUnreach` | positive control | P | `f741254d5c9f47db6fb9c49bd599d806136808476fec600ffbbc87caf9c214d4` | `4a26a32486f6a14ba58964a118219d35f1d3b87861c6fe969fae198e846056d4` |

#### `prune-with-assume-preserves-ub-derived-facts`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArmAssume_preserves_factOnDefinedRuns` | result | P, C, Q | `af98cb810a6d446f095c70e0ea914da908808e722d9e6f637477ba2271db1ec1` | `a62dfeafd7347147271e259366bf0da4e4fcfd6933ff5f68244488ae674c1b52` |
| `pruneArmAssume_preserves_factOnDefinedRuns_nonvacuous` | non-vacuity witness | P | `61e6d05ea810ce85e7caf4025cdc41e6c9ec6e660100781c341cf0777ef038cc` | `64e42ad5fa4dcddc4025fc2dea316b8e63da8f178f81d795a5c90e04f74e02d4` |
| `pruneArmAssume_fact_hypothesis_counterexample` | counterexample (`hF`) | P, Q | `e40c709d92e5c319644be80373708ce0db49a8450f2623f3379ea0759beccaba` | `2df91aaaf6f705c7a3d6b0a5beb1e5a0151043468d8e1d25ff39895e68ed30f2` |

#### `prune-without-assume-loses-ub-derived-facts`

| Lean name (`Toy.ZstAssume.`) | role | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|---|
| `pruneArm_breaks_ubDerivedFact` | result | P | `5c1141bae904da712165ed96529cb6f1e56dc85fb510b004cc49332094976b22` | `f741df7ebb911de3602b0e453f7358ec56a6a0fc42a53afa06826ccd9521abaa` |
| `staleFact_fold_after_pruneArm` | result | P | `0a8d224ab4f70279944287d8c52d8f6b518d026451f39a863ce6d39b92166723` | `feae91c43875a59454bc6cb47c6c744f5fd08b7957f9784bc3e1982e18b67fa5` |
| `staleFact_fold_after_pruneArmAssume_refinesPP` | result | P, Q | `76470307dd0dc38994ae590fdb52116958e95ae7933acc59e38325b032fed3f0` | `0d30f6750f04bc152c7578b86e172030859f03565670b9efef0d24e4bbebe216` |
| `factOnDefinedRuns_fold_refinesWT_not_refinesPP` | result | P, Q | `fdbfaa32be9cb87e4269b71093b1d273612c6b57dddaba0c5c2fd49d5e8acaa5` | `e4638a1554b7741578e77525f72b0b957e9e0ee8d9d887b3cda93f371df5f875` |
| `emitFact_fold_after_pruneArm_not_refinesWT_input` | result | P | `dcfb2aadafef9f03ff7eef16595bcd2656415a8c94b73dc3bb56d40780013fa9` | `6de52c836114dbb7403a6808ce31c4e56d3e2cfd17039e16d07b4d3a146bd267` |
| `staleFact_fold_after_pruneArmAssume_refinesPP` | positive control | P, Q | `76470307dd0dc38994ae590fdb52116958e95ae7933acc59e38325b032fed3f0` | `0d30f6750f04bc152c7578b86e172030859f03565670b9efef0d24e4bbebe216` |

#### Other recorded declarations

All other names recorded in `audit/statements.json`. The recorded names are exactly the declarations quoted verbatim in Findings (definitions, definition examples, concrete programs and auxiliary lemmas); each name below is written in full after the column prefix `Toy.ZstAssume.`:

| Lean name (`Toy.ZstAssume.`) | axioms | statement SHA-256 | closure SHA-256 |
|---|---|---|---|
| `Beh` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Beh.HasPrefix` | — | `dd94d38a3a283278485ded8787ad7a2e6f645b9dc16705975684e347e5961247` | `bc6cf5b3856c8c6e0c4df4bc5750684affbf715667eb69e4251fe0c0b9ec2561` |
| `Block` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Block.unreach` | — | `81fd4a8fbbebf526e3cc53e97d08a2e1ae943e4ab08b93ab41bed6d12e458c8f` | `a63cf26af3ccea4c0f39657b1d2deeb235813e6de934e387c7c9d0f82c9ee288` |
| `Cfg` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Cond` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Cond.eval` | — | `4749181c1d767d77382eb6a506a4aa6b46725982afe84f6365371864bbaafae7` | `d669e7b5c2f96e381ff62269cb6ec46aacb8de3d19cd0713be1fea99a4255ae6` |
| `EquivPP` | P | `21a52a2993bb24621211247c72cc008a60a28b514e994ff634341aef2a5b37bb` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `EquivWT` | P | `21a52a2993bb24621211247c72cc008a60a28b514e994ff634341aef2a5b37bb` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `ExactUBChecker` | P | `db6996ccd024380b72e402cd73e2695eb25364a78d2ab749b2b7f4688fc77db4` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `Expr` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Expr.eval` | — | `b9f468ad0ad7924c980f7d9640396a949925c004768c4d24e5db7878dfa62626` | `fa688a612d4ff51a1fa07a6623557f245de805b977bb021125af4f3458332483` |
| `FactOnDefinedRuns` | P | `db2565f986a26d0ec1451243d05bd16570730a2f8b229eb39f5c7c26d1f906dd` | `22295ca7036d7571803db66201ca9bf6f305ce3afd4a6e04f3dac1df37fce821` |
| `GoesWrongFrom` | P | `f7d9b01ac17d9130f09cb8ba6ab16aadc4022f90f57d372076689d0a1fe4d91c` | `a08dc4f7d2c9a8b31e3ad425faa722c720345b8b542318320006ee05c31ccb15` |
| `HasBeh` | P | `8ccb6d85a079c373e4de50c7f3b8ec76cd9a014877db62c2d91a6595cee8a31d` | `9da106807b8784f712c8fa4f2db5ed6db4d38694f744a37e1e9620ebcc6a92a8` |
| `HasBehFrom` | P | `53aae498527c1c3f70123c1b9fe892aee3960aa87b239b45e510443b795c8f9c` | `79608aa4a044708270da3132f9bec1c59c52f2cab514cf414a5048ea6714aa24` |
| `ImprovesPP` | — | `4a0d2320545e52a364f34ef405db991ebfd64acbd8bf4478eee0661134249a97` | `bc6cf5b3856c8c6e0c4df4bc5750684affbf715667eb69e4251fe0c0b9ec2561` |
| `ImprovesWT` | — | `4a0d2320545e52a364f34ef405db991ebfd64acbd8bf4478eee0661134249a97` | `bc6cf5b3856c8c6e0c4df4bc5750684affbf715667eb69e4251fe0c0b9ec2561` |
| `IsUnreachableBlock` | P | `8ce3772f8ffc7c1095eca2a9134dcdc5e2fe321f1808e5c5ca8b96af7b5af712` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `IsZeroSizeAccess` | P | `a21e0cd5b97d4bc3f0f4582cd2395cd23d622e3418f4cca95f914ed3ac1d43f5` | `013923e2ad3249be166131878d3b65963148ffec7944a9344b5de59f4309e48c` |
| `Label` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Outcome` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Outcome.cons` | — | `0cf99ddffb241f7f845fee0f0b1670ccb017567bbd9a24dbcada3a8f3384d13d` | `95df5ee753e52f04c12fabb65981b3f978577fa306908f34a861897ae6aef3c4` |
| `Outcome.isRunning` | P | `ffddbc1428d3e6e421795b32dbf556ef978a7c064e6066726235e706c492790d` | `95df5ee753e52f04c12fabb65981b3f978577fa306908f34a861897ae6aef3c4` |
| `Outcome.trace` | — | `e4cad3ce95b1df2af15ed435ba8c275d3daf15fd081d7e0d582e214f378c4f26` | `95df5ee753e52f04c12fabb65981b3f978577fa306908f34a861897ae6aef3c4` |
| `Prog` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Prog.at` | P | `edfc7932e5bf0bb26f6c9f4768d0dfb45f132d9aaf43b7cfab90d11886817431` | `65eb586ba36e25075dc17c6e205a09b2683c09b94fb9d4421264860e15576e44` |
| `Prog.blk` | P | `2bd0bbedf12140867605f556a505bd9861752b2c030f6e95d5e2bfe4e7bda7fb` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `Prog.entry` | P | `e8f8af69f7ab45465f68b63c2fdbfc2927fc8dd9a432bdd83c82ea9b9e4f89b6` | `65eb586ba36e25075dc17c6e205a09b2683c09b94fb9d4421264860e15576e44` |
| `Prog.init` | P | `a5bdaaa2dfe4eeff66132990425586e5828316bd80846e59a7d27b5195a0825b` | `65eb586ba36e25075dc17c6e205a09b2683c09b94fb9d4421264860e15576e44` |
| `ReachableAt` | P | `dd24c3d83857a132b30e3dba012bf494c9b7a874db09a8cd91701f4425b5e456` | `22295ca7036d7571803db66201ca9bf6f305ce3afd4a6e04f3dac1df37fce821` |
| `RefinesPP` | P | `fe7726cd986f85d45721f577fef6b62b3e42e77c9f45414ddd70a229bde5594c` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `RefinesWT` | P | `fe7726cd986f85d45721f577fef6b62b3e42e77c9f45414ddd70a229bde5594c` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `RevChainWT` | P | `1feca80c5cc143cfa63de40645f0f69ad1aa850cca1e54172d521ad175f213cb` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `State` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `State.set` | — | `183e6194b859d5ca8edc2e0b889adfc20f6738935a0ba1172fa5c6856e701cba` | `fac62285e13ab2c22f6759170398416e303a9f49892fb5a09c19d53eaa332962` |
| `StepResult` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Stmt` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Stmt.accessTy?` | P | `1fbc6175e7f020aa870562216d67b9c2694ebae956d5323bc3cb31781277872e` | `013923e2ad3249be166131878d3b65963148ffec7944a9344b5de59f4309e48c` |
| `Stmt.pre` | — | `4ff88017ad627aef4f51998830086f98942930469158ba84d37f1792a63a01e1` | `d22770ada64aaaef78e49e29480c375704b3c34d4e00a2fc0020e145c96c1b2e` |
| `Stmt.zeroPre` | P | `4ff88017ad627aef4f51998830086f98942930469158ba84d37f1792a63a01e1` | `d22770ada64aaaef78e49e29480c375704b3c34d4e00a2fc0020e145c96c1b2e` |
| `Term` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ty` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `UBFree` | P | `9aa39a57094b25c9d21b1ae95b54a698d3911c2130578c03b6dd803d0ee0dd96` | `85ae7f55227b0a3176bd7c5b9ee93230492b6a94953cf75588193862da1fc111` |
| `Var` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ZContract` | — | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ZContract.holds` | — | `d7c7b34fafbd0aeb8b5308e37ca8553bbf28f240554b20f9c0488e49c665630c` | `9c3edfe535aae55bb4556bb348900035a6d278df20dd9d53a8c2a1833f117c0a` |
| `accessOK` | — | `81a439f64a491664d3cee1776644e5639f6ef0c85fa787f5ac8d06a587628c42` | `9c3edfe535aae55bb4556bb348900035a6d278df20dd9d53a8c2a1833f117c0a` |
| `accessOK_nonzero_null` | — | `465c94ea2841f939f52e91169ad727b4b2e2f71c02dee260e895b8694695a23d` | `e527d26e25d118df12fa283eb7be279c3ce215ff308c1e9ba31e61d7843c0a1d` |
| `accessOK_zero_ignores_deref` | — | `679daad7375bbc5e11143941eb9ae239b2ed87ced3d11d0ca1f1c57f96be5f07` | `e527d26e25d118df12fa283eb7be279c3ce215ff308c1e9ba31e61d7843c0a1d` |
| `accessTy_emit` | P | `1714f2161b41d36e9f3e672c85e7a697b596c718f3896de66e01d75966940f4b` | `7b1579cdfcb5263032c4682f9e00767fbd64ec6b29f1e77ca69a881623045542` |
| `accessTy_read` | P | `431cc8fe0ee3790690c0b82dec64cfa0fbd0b64bd31c79f042fcb95901623c45` | `7b1579cdfcb5263032c4682f9e00767fbd64ec6b29f1e77ca69a881623045542` |
| `aligned` | — | `9f6801e6bc98959c40bb6f13d7b9821ba21799746b550ad5957f7d9331710dd9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `aligned_neg` | — | `8e2221a6c163951915f6a5b1c9968df68a8cae4dd4153cc25dac4eb1cd543ea2` | `e4cee25e03c63812df84794516fa00b1c2fcae6b8495ac1e8c59b6c73a4e3d30` |
| `aligned_pos` | — | `7ffa40bebcd61482f394b015c3ebff2531a3e0320bdde1964684ff6064eeecc5` | `e4cee25e03c63812df84794516fa00b1c2fcae6b8495ac1e8c59b6c73a4e3d30` |
| `aligned_zero_align_nonzero_addr` | — | `ab6267bafde8eb5261c8d9c5f6c039675acda272e430531ee46659e8a3137233` | `e4cee25e03c63812df84794516fa00b1c2fcae6b8495ac1e8c59b6c73a4e3d30` |
| `aligned_zero_align_zero_addr` | — | `83a6bdd5769dd44f3e0f7ef7dbce21ce6b42a3d7ef33230aec5db1950b06865e` | `e4cee25e03c63812df84794516fa00b1c2fcae6b8495ac1e8c59b6c73a4e3d30` |
| `aligned_zero_iff` | P, Q | `3257a10026c28640dbef1bda1d2753750b2c199e6b3fef492fd58a56ea6ddf89` | `e4cee25e03c63812df84794516fa00b1c2fcae6b8495ac1e8c59b6c73a4e3d30` |
| `at_entry` | P | `71fbb5ea8f6748b7420a008c01830138c0e3a65ac32249c2a48989fc11bddb04` | `ba40a37c0d56260fb3985cd4af70f7b81655603c9839523e083a2278eabb3973` |
| `at_terminator` | P | `1e2948a654e85041733be4fa3bda6ecabe7f0f61aee6f9456c611f06f963a07c` | `ba40a37c0d56260fb3985cd4af70f7b81655603c9839523e083a2278eabb3973` |
| `bytesDeref` | — | `a71fa637857d183d0b8a4f91427fec8cdafb473d8af514dc02546b5a40d7916a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `bytesDeref_neg` | — | `8b5ae1cc48806d49339ac223cf25a4f51ecd7dc2c8dc0f7b2483a6e42a7ff704` | `4453c0a983bce3dcf942eeb2c9f5a0a5f3b977b45b995305a537488bf8927add` |
| `bytesDeref_pos` | — | `1c0bf8187f2686c5e99666e4486d31232621e939007dc8fd3bc96d2d0328f6e8` | `4453c0a983bce3dcf942eeb2c9f5a0a5f3b977b45b995305a537488bf8927add` |
| `cond_eval_neg` | P | `2d3a8530e6771f9000a38a2fa12b0a243ea01a9e4ba689e32b8ad9171a3b7f31` | `f181cc4e87003095d8c59a0aa162408b942fe2d290035bb9916737616d959ce2` |
| `cond_eval_pos` | P | `b6a4c8db74d69c87ee744b9ac123bbd750b7ef04852e8bff41e1f6ee8cd9f84e` | `f181cc4e87003095d8c59a0aa162408b942fe2d290035bb9916737616d959ce2` |
| `cons_none` | P | `6891a179188734cc378e8862b3f710b7fabb748e7061dbd3f951184e8b8a4d79` | `694df8c8b0600610dc01e3447406ac5ea73e32f2848b866eb1d23d6dc9add79c` |
| `copyLoopProg` | — | `779bb63630b7b68505376850cb47bd1a9191d040d5154fe11b234a57c846c7e9` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `copyLoopProg_one_misaligned_wrong` | P | `858a41a2b45c00ae21b7e9db4b2025004211cfb7fa7de6b5c6de6b99174d3222` | `467800fa750e5703364feed5f4d2bf12e0187edfcde5ef46adb03675c897d3c8` |
| `copyLoopProg_zeroCount_preserves_src_dst` | P, Q | `bef3b5e52de1effcb5b626b085e50cd78f1e87fd3883b7dd20f7351394a468f4` | `d8d7607e348e25cacd3ca2ad63e5f73d86be04e226dba7d936d7133b38b33e76` |
| `copyLoopProg_zeroCount_run` | P, Q | `7aaf3165d223c12cb5b7730eac9d1c266c3a68a8580640d37384bd1a2cfaf8fc` | `f566465051e53e51c5896604b877cc72749b660d02e84d6ade1ae0c0fef70b22` |
| `copyLoopProg_zero_term` | P | `0f7006e0a7e42575cde47eb1215aa871cd6ccaa4527dca4b7d755f1228f86ca9` | `467800fa750e5703364feed5f4d2bf12e0187edfcde5ef46adb03675c897d3c8` |
| `copyProg` | — | `9f6ffa0321e0aac6de663ae556ae8fcc0eb8f22ae3d1fedbe233820e24dd2f64` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `copyProg_aligned_term` | P | `979564511eea960b6e85e77b12e28024547ddb86e0e9661c7fe5db3e787ddf7d` | `fe4994e693fb6e0aeb11776c5df2cbc84baea53f3a11f568ac27904c3bceed46` |
| `copyProg_misaligned_wrong` | P | `ee20655ffd03258989910c2c199e1f6687b4180618c3187a685d29433c4525b9` | `fe4994e693fb6e0aeb11776c5df2cbc84baea53f3a11f568ac27904c3bceed46` |
| `deleteStmt` | P | `2082ac08bf9368e1456eb6f97cd800e5cd5d1f00ee9f91f8a28994a37a861565` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `deleteStmt_example` | P | `4257612427a9c555b9ef507ec926185a8adf7a13250025a3ae363daeca46a061` | `c0cb906b06f2a64884a469d0e0c41b0752df299da87bd618117411b377f21bea` |
| `deleteStmt_out_of_range` | P | `28d4f2fd9595f04f03d97d5df0de21588bfa53d3a31940ae1817f2f08c61ef3c` | `ad15f5643578de78b7be7f4161c0a6814a10e5b2545bb41f6a189b77b172199d` |
| `dropArms` | — | `4a3a7be8cf4d6adbc0734570a13f2bb0aed7e5e708ff456cd7e71a2f202bf937` | `6756bc3acdb351f0469a9b85d7f6a72b7bc55cd7ad08861439644e6e752ade6f` |
| `dropArms_example` | — | `708d929d90a33eab1e05b4bb9e43b2da42124a67555e38031b6a2b891eeadb87` | `6b8ebacfac907a4e2f1306627eebd5acdc59287f7ead0de552ff5ce149c02b6b` |
| `dropArms_keeps` | — | `eadd33a8e26fb51f3769c0e42b3776e42e682638ec1cf0bd912f4eac095e85fd` | `6b8ebacfac907a4e2f1306627eebd5acdc59287f7ead0de552ff5ce149c02b6b` |
| `equivWT_emitUnreach_unreach` | P | `c8192502b47aa345246e815169c256be57211d57649da3900b32471af15eb9e1` | `0ce74cabf12e811c0b95ee412d055030a7c57687856eb051c8c5187ac6fef1e2` |
| `equivWT_of_equivPP` | P | `3b6cd969817c8fae6a262f1e8fbe2850794ba1d5a069801a05e789b39eed6be5` | `5da57b80df3a8892b60cb85cdf2930c843d67b62a7e7ce231313c68fb87bd76e` |
| `execStmt` | P | `2147a42529f32ff6738f4282f16f040337cb80a32731114dd7009f8608b876af` | `d22770ada64aaaef78e49e29480c375704b3c34d4e00a2fc0020e145c96c1b2e` |
| `execStmt_assume_fail` | P | `c76c8ee3dec263c0b431693eab388ff821254dd6cf50e6e36c3cc70ede0a34bb` | `adb2a9f1a130bd1f33663d748155612720441dc26a49a34cd875834654d745a1` |
| `execStmt_assume_pass` | P | `640c778ddc5f7aa16e5a44670578e434169c0103938255f0c820ca5297ce2e79` | `adb2a9f1a130bd1f33663d748155612720441dc26a49a34cd875834654d745a1` |
| `expr_eval_add` | P | `ef5fda7a58a4f3b6d4a99c0782158006af65966988d8456fce686f49a10d6eae` | `75baec660530a9931f4f059ee8ae4929f182f40b30bcefb2049be5186d7e56be` |
| `expr_eval_no_wrap` | P | `0f221d09b0d4feed5adbfb07407f268180905aead409a2d5f8cb1f22b8038033` | `75baec660530a9931f4f059ee8ae4929f182f40b30bcefb2049be5186d7e56be` |
| `factOnDefinedRuns_unreach` | P | `cf3edbb9be422ced99e704d996e7dacfc596e6fb1752dc66eacd687bc72cb6b1` | `82497a4b8a3f294b9b5b3053a0e1a30eadec295b3925b545dfa74cae37339016` |
| `foldToGoto` | P | `0ab09f9e1e96fee0b983d02f91b487392d6a43dcbe93fe906a3db99946e34d53` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `foldToGoto_example` | P | `5abaf074c6b52f1729bfca6c988f3c3ea433eebe8b1b8fd697f1bb573f8c06b2` | `8e9cf0da5c6b39b7cbbaab94df8c6b77adf10fee205f367e24d3911010666e90` |
| `goesWrongFrom_unreach` | P | `f768df9a96a40f93d91f8bfc60f6aa33176dab78151b39df51e2dcd617cdfe32` | `3acd1dc6af74f57444ffef37752eccb9be3d52690f27fb0ba039d92363004288` |
| `hasBehFrom_exists` | P, C, Q | `267d436fc7e72812998e563ae9ac7f85f77081efc9e4bbabb14d33ae03a08836` | `b6e639b97f151cb395b510db88a00d4851573a4f09509209736718070db3fcb9` |
| `hasBehFrom_unique` | P, Q | `b577c786c7699f5c1d9d85f2bc072518a9c8f1fd2c6f442cd5e3a212453ea46f` | `b6e639b97f151cb395b510db88a00d4851573a4f09509209736718070db3fcb9` |
| `hasBeh_emit7` | P | `65b734eeebd8071da4cf35347f185314bcce0daaea62b09839eea00148d40587` | `a1fe3e024a62b6d1c2336535629cf1a9c6d14956329e89a7e05104d4a56b9bc2` |
| `hasBeh_react` | P, Q | `f93aa20ee9a15497bee4f0fa098ac9e98877be0948afca1e03f0c0d2f64f8d8d` | `db4ce5c1bda88978e93d40e24e5873d873a7699d7b1fdb31f7c5d600637641ed` |
| `hasBeh_spin` | P | `54c8205dcf55ee47b0165dccb58e31d95ac61d7f0875efec0a6bd584875fc671` | `681a0b69b2ae665e7cc2e35de7539575b2df524d4689291b1fe47e82a5f63472` |
| `holds_aligned_admits_null` | — | `af5b4a4dac33e50a0f565479d06a58b8fc3ae4fd1a28574aa6891855b8ab9b29` | `63bcf19f23f8ceb1d2d248cff5b3417e57355e36ae7551a3e211262ba14b02e8` |
| `holds_aligned_rejects_misaligned` | — | `3e32f24f55383fcbd8cefc646f8e1134b39a8961f25f72b2244892b0fc64c113` | `63bcf19f23f8ceb1d2d248cff5b3417e57355e36ae7551a3e211262ba14b02e8` |
| `holds_anyPtr_null_misaligned` | — | `97c0cbe7fbf28aa49019f51bdfdf85d18df71549543bdf265e61fc668071b64a` | `63bcf19f23f8ceb1d2d248cff5b3417e57355e36ae7551a3e211262ba14b02e8` |
| `holds_nonnullAligned_rejects_null` | — | `43e2d71ec045590c724fdfbed9ec7628ac2cb5912a74e0c9aae3b8011835034a` | `63bcf19f23f8ceb1d2d248cff5b3417e57355e36ae7551a3e211262ba14b02e8` |
| `improvesPP_neg` | P, Q | `a3e5f9c8c3750be05d657f047a3c94072ac0246d6ead244d3c536615782896e5` | `c097dfe085ca069d129b1b2d44eb6cda6dcd9cccdf6744ed57343652607c8a9c` |
| `improvesPP_pos` | — | `2a51a9f9adedca253d24b4fc64efa8ef8a2561eb33ed2d5e26c7ede083e81ccd` | `c097dfe085ca069d129b1b2d44eb6cda6dcd9cccdf6744ed57343652607c8a9c` |
| `improvesWT_neg` | P | `c815ecc1680387bab8b75a39e046336c2a3c8f2653a4ddb0fcabd544a4f2aace` | `065f08055adeb82eccef1f7d5b196b4dfcd2108849424decb94393fe7bbe2917` |
| `improvesWT_pos` | — | `a1d341ffb65dfd406f2971ab87c348bcf0ba6bd5eaffbfc16d3f81cb51e7dcde` | `065f08055adeb82eccef1f7d5b196b4dfcd2108849424decb94393fe7bbe2917` |
| `insertStmt` | P | `e1339de2b0369ce04707f5e4b746d24ba0e77dca1c2d2b318a02454463c134ae` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `insertStmt_example` | P | `c14c1445c6b486cba08407330513078751cf3602afd786e5ea90c4557c8c9891` | `8f0bd68cf36773f82e6e0691f5539a4ebe35c2b288b3bcc2d6a09452eb863fde` |
| `insertStmt_past_end` | P | `7a07a99c99dd8079b9b4589f2c1236ea703c9671f41190cfb97a171bf375c236` | `8f0bd68cf36773f82e6e0691f5539a4ebe35c2b288b3bcc2d6a09452eb863fde` |
| `isUnreachableBlock_out_of_range` | P | `8ed680f7a17d2a9bd26f3e28aa953842b18230e31bdb6ec9fcb68cde14b75c8e` | `0e2ca1bfdb2a340d7c98997dba10155b96a9b865724b22a552f5c4de46ddbe90` |
| `isUnreachableBlock_unreach` | P | `3df878fe4f4379b6d941bf10864415b7ee2f7a30ada26cc7348dda83d52ce7f3` | `e1e76370c6757fe9f3c41b6fa76e9a9aebef51ca34da1f6cb98dd616176123cc` |
| `isZeroSize_copy_zero_count` | P | `15020179b6f58c4b0d3db113d21c1c7cc062f2d84daa7895bae65b6706a76f78` | `10597e6e00d6fc121db6a30b6145768dbd379cd7aaa9e4e1956625a3f199369c` |
| `isZeroSize_copy_zst` | P | `02ee991b02d622e42a491a9ebee8a18440a5e5e26da14d26ab668cdf91ae3d16` | `10597e6e00d6fc121db6a30b6145768dbd379cd7aaa9e4e1956625a3f199369c` |
| `isZeroSize_read_zst` | P | `accfbab13bc49a5ffb5fa0d24eb762a473eb733fc0e92532b467d1190274bf9b` | `10597e6e00d6fc121db6a30b6145768dbd379cd7aaa9e4e1956625a3f199369c` |
| `mkState` | P | `2735e0e9bfd81323b63aa4e30476f202bd2490ebb90e1b5ddce522fcd7cffefc` | `fac62285e13ab2c22f6759170398416e303a9f49892fb5a09c19d53eaa332962` |
| `mkStateNoMem` | P | `2735e0e9bfd81323b63aa4e30476f202bd2490ebb90e1b5ddce522fcd7cffefc` | `fac62285e13ab2c22f6759170398416e303a9f49892fb5a09c19d53eaa332962` |
| `not_equivPP_emitUnreach_unreach` | P | `9d67d8eb2307b760bc4106d14f6fce3e8351b6827779fe9324d708ce20560735` | `9b4b7d6de14c5ad12143c945b883392a153f35515f1db1b2a965236656b1562d` |
| `not_equivWT_halt_unreach` | P | `9ecac77996168888a789d0390033c06c62ce2b028be8f953186f35e7634a3f94` | `59a36328c63a614e5442ea5d82b7ba1c1fdcd2fe2720e377434ff11cfa7e98bb` |
| `not_exactUBChecker_const_true` | P | `07f0e30abbef4d660d2721dedac49e9ddd678c6c3dcf6bdc19f7ce4587445dc7` | `6add152d6a69604d1f9313f8f19874b93ed5c804abe9c20754b41fc1bf10ce22` |
| `not_goesWrongFrom_halt` | P | `42a7a32369f881b8efa92857019755e77cbc77f4a3dddae505cc2b74e671a48a` | `58cdc50c33ef9f3de9872528191b307dec68143b0ecb7404d780979e55622206` |
| `not_hasBeh_emit7_wrong` | P | `f11f54d560a74e29790171d3accfa83ed7cc306e98fac96c4206ecebcee6f2f8` | `a1fe3e024a62b6d1c2336535629cf1a9c6d14956329e89a7e05104d4a56b9bc2` |
| `not_isUnreachableBlock_emit_unreach` | P | `c3d8b33174a35ab7577875701fe077dd636ff28b619020eca6bbf797cb5e917a` | `d643b525c567366e671b16ed85dac94a00aaddac1387fc3b5a3fb91cd0d30786` |
| `not_isUnreachableBlock_halt` | P | `bcc5f50cb5385fea0825245e1a953ae657aebdad904532ec836cfc90dac0b837` | `0e2ca1bfdb2a340d7c98997dba10155b96a9b865724b22a552f5c4de46ddbe90` |
| `not_isZeroSize_copy_one` | P | `25e59b5639dd219403877f4bb986a8ba385065ec7ffbf53f486af48d2677f0b7` | `10597e6e00d6fc121db6a30b6145768dbd379cd7aaa9e4e1956625a3f199369c` |
| `not_isZeroSize_emit` | P | `920ed1e337256a847eca57bae6051649c6e1bcda73dde780018cd504a0eb6017` | `10597e6e00d6fc121db6a30b6145768dbd379cd7aaa9e4e1956625a3f199369c` |
| `not_isZeroSize_read_byte` | P | `a834c57e32704dae1dc8d1c81aa7a36afa02b4f1705e244fddf8eea82b995ccc` | `10597e6e00d6fc121db6a30b6145768dbd379cd7aaa9e4e1956625a3f199369c` |
| `not_reachableAt_dead_block` | P | `4ba6d65c06964510245f3a13545831768b255880d893301ec3b859767a84db77` | `f0ffc811271e5cfb395690a99f61f7bea2d8091843d4f9f25e9b46f975ba5abf` |
| `not_refinesPP_emitUnreach_unreach` | P | `3a2c0a78546e0739a15196a3784a4517b506357b5f37b3a778b6bd0c17111b38` | `bee30e6866faf53134e4f148e188b595939636a5ed3bb90412d22ef89de511f2` |
| `not_refinesWT_halt_unreach` | P | `45770769ff70a0f10c9d3476fbc0f7bb1e2226899e2ec650aa491e9ca8469f27` | `9ceb0aacb2b4e3173905aa4a5cae6ff28c3753520db59c48e9cf1f895c9f8aea` |
| `not_revChainWT_unreach_halt` | P | `a51c27752d5a88919e1122be776df9324c96197cef778246f6553e4a9853c7be` | `18a8776fcfe363b7a029b6501033282ca97c529c9e9b1a3855516f560ae9ed78` |
| `not_ubFree_src_of_not_ubFree_tgt_of_refinesWT` | P | `419ab9641d5d9162927279e9739354ba0cda22ab603c4fa9f754190fe3a934e8` | `39cb0a3d0eaae03977523a80b1fb5506caddfe01c19c4b6fa6576eaf7af9a48f` |
| `not_ubFree_unreach` | P | `32d1618294c8f0fb5d3315869aada5653d45686950429114b023c1be895310e0` | `ef2c916155ca9a238280658728e41dc58d0c9e3c8d0e26b6a2ab9847d4eaf374` |
| `not_wp_unreach` | P | `7c7c89fc9337a6147fd4c5144ae8b6f043e8af12e53083089e1f8853fba384fe` | `d1b7d8da41a7d96b6d9eb38eed3b2b06ece527273a28ec331b42e4a6b0f0153f` |
| `outcome_cons_some` | — | `c7b7c57bfad27f5c2d7fffbdb86d05a51a4125a162e78f432c9719e7b35e8f5d` | `ba26f21a4ffb34f4b0b853917840cd5fef94fff97296442ec00bc8c3c0310ef4` |
| `outcome_isRunning_running` | P | `83128ec62a811056de2b5e77ff4ab592bf2d8011b750dff81916a286935d4bbd` | `ccd154d42e3f2089ece57704702e749d50853ca5bca522e1348288f07522158a` |
| `outcome_isRunning_ub` | P | `2d869e3d24f315aacdaa620418ae7d215e360eed1899a49727dee37cc422f5d8` | `ccd154d42e3f2089ece57704702e749d50853ca5bca522e1348288f07522158a` |
| `outcome_trace_done` | P | `3fac4acd302f74dc2d5201fcc1a3159df149616455b6428ecd2c4afcc1befc02` | `a71e09121d3469c9025e4cbafcf13593d2b30f32fe05375861501adc680d430f` |
| `outcome_trace_ub_ne` | — | `04e23a8b26025dc9c33400b4d6aa987ce628b4f14586ec1e8934f943b910cd23` | `5c7510abb25ddf611e6eae1c47a95795f3538af4ea70b4ee71096ccac55b39b1` |
| `pBranchRead` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pBranchReadHoisted` | P | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pCopy0` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pEmit7` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pEmitBeforeUnreach` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pEmitFact` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pEmitUnreach` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pFact` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pFact_fact` | P | `61e6d05ea810ce85e7caf4025cdc41e6c9ec6e660100781c341cf0777ef038cc` | `64e42ad5fa4dcddc4025fc2dea316b8e63da8f178f81d795a5c90e04f74e02d4` |
| `pHalt` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pLoopBeforeUnreach` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pReact` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pReadZst1` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pReadZst4` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSilentToUnreach` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSpin` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pStale` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSw` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwAssumeOw` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwDead` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwDiffVar` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwEmitUnreach` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwInv` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwLive` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwLiveInv` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwLiveUnreachOw` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSwOne` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pSw_fact_not_invariant` | P | `cb1775f16530197557947f0a458c587b1f7a2f0e044014c52f9114000d3f40a9` | `16921593d0d47b420835eb7e541faf2a622a490da9e915172b75ae88eb718116` |
| `pTwoHalts` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pTwoZstReads` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pUnreach` | — | `d4a2b061919fc733f0cb4ce49f47e2ae6bccf1d74af41747b9b01b0570910fc7` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pre_eq_zeroPre_of_isZeroSize` | P | `e071150ceeae57cbdbad76f0b6ad3799b783ec406d8c34c9645b49c9e0e412cc` | `b1bd2e931b06cb85ea2ac5c2c16f7a56918926d6d1df7125c19d9ebe1f2c55bf` |
| `pre_read_aligned` | P | `04e43a1c0bad76aceb2c669924a010f20960148e700a9f1e99e9425cd5b48e50` | `d41f28345b60db7a9bbc31f0b9b478c092d1f891d8ac4fbb522609df42eac481` |
| `pre_read_misaligned` | P | `f7feaac9cc7493ea87fb95651d83e6069e2da1a9e4d02b723e71db6536e31cda` | `d41f28345b60db7a9bbc31f0b9b478c092d1f891d8ac4fbb522609df42eac481` |
| `prefixOf` | — | `8c49aa324a68adb900cf14aa103d2ef1bf2f7f05432c35cd4530d56a6e1d77fa` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `prefixOf_example` | — | `3da62581bea8c7818b0d8d239ea2dceae01b703ab4fac6a9ae6f50e16dd4bc85` | `3dddec07c3efc6c25dc1536cf72ef64aabfb369627b35cf21b7b95f095e19aa9` |
| `prefixOf_neg` | — | `871013310183aa8feddfa6c49326e1686a73b16697c96dc72e8491d97b2c7ef1` | `3dddec07c3efc6c25dc1536cf72ef64aabfb369627b35cf21b7b95f095e19aa9` |
| `pruneArm` | P | `ca0e528a9e5d29b1d51da4c8c44b386a5dde65871a55ab60710dd2e1b208c622` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pruneArmAssume` | P | `ca0e528a9e5d29b1d51da4c8c44b386a5dde65871a55ab60710dd2e1b208c622` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pruneArmAssume_example` | P | `91c1b7e74b7d8464d5a1e1abdb406900516a4af32517fad81582905e3f872fd1` | `e5bc6df2340cc342e8b3b53c6a622143d87c97edbec4986f336bdde98ed04dad` |
| `pruneArmAssume_non_switch` | P | `5402ac48edc4b68446aff1f254678f6e7b614ab5ef929152ea17f7268e44d9bc` | `e3400603ae4ca6c3308a0c88f26a8277c282d71ee25961aada4f26849af4f8a0` |
| `pruneArm_example` | P | `f6e6fd3042d401a772a9cd1c2815c6c48c7dd141bc99103b16526f12f7923d5b` | `dd20567e9ed8bbac871e5b24b37e31a7eb702da718537330a91badb55bc7621d` |
| `pruneArm_non_switch` | P | `5aa05a5811edce76fc95938d148080f4d434264519f3272ce0d4b9841340749f` | `7294c08d58c69987ea33bb66feb3cdfc93323da4803cd27b633e73ff46cb9182` |
| `pruneArm_pSwAssumeOw_equivPP` | P, Q | `1364eaeb43da495b8682598b6980bb21cb954a1b3d90ae2778f7567748cf318b` | `241f837d48953614f11f059408c65a2df13fc0c554e5ca7a8e4858fb6a68f81c` |
| `pruneOtherwiseAssume` | P | `042899ea6e0e10d84a2f03c09190defd0020c1a46400138187bb14c971058138` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `pruneOtherwiseAssume_example` | P | `49db88cbd3e75895f2235af65f67e4d6392aad905d24fe24b0329b24044f940e` | `74d6a6a0fb0da6a43a1ca307ba950b0461bb7d37c2c9b2a762458468f880dc38` |
| `pruneOtherwiseAssume_pSwOne_equivPP` | P, C, Q | `b93cbc7ef956729826f22f08831f6607b1b0d7608dbd2c1844b3b598d463a9c1` | `4902e053a3d20533d3fd9366b5a91e0a80ff237d730edfcadf91d530e712e99b` |
| `pruneOtherwiseAssume_two_arms` | P | `f9f81b1b6ee6b0121d74d3b74bb3a3619e8e44f7a699a42429b9fe9752927318` | `74d6a6a0fb0da6a43a1ca307ba950b0461bb7d37c2c9b2a762458468f880dc38` |
| `reachableAt_entry` | P | `b53e475dbe23b15b3c7709b5f65400d1f840a9135b92840f45708a7adbce2144` | `c53ebb6cf2bdbd32ffea9294044e0aa456701cd8be0d166b3dd10f373c9c9052` |
| `refinesPP_of_src_unreach` | P | `684c53a0201f91fe1524bd2db25e2c9521a3be18702bf25b4df8b2584f67c744` | `28cd046739c84febd53f4327be2588d1cf627cec4c54a0f44643911eb3a1eb71` |
| `refinesWT_emitUnreach_unreach` | P | `da38d78a45dd763c152df2ca490e3108e54c545f4b7acae8a5efb625a94e33ea` | `cbaf69ebefd791f89af44dca43d6ad8f8936230fcb130763475c05425e14574b` |
| `refinesWT_of_refinesPP` | P | `bd988f8a3f297c3a08781b40d50d00986ddc6413edd3ee18bcd2d3305fb3be9b` | `ae75ca7cc240e1fd14229f47756fd74649d646570caf2ca8ff404f90c914da5f` |
| `replaceUnreachable` | — | `87e713ca11c4cf6c54d504e9b267d65bf71bc93d0f87659c0a069aafe32137f5` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `replaceUnreachable_example` | — | `0a5a0ae3350b21b927075a3e267a9caa8e4895c693d9b3965545a1a34e7e48b4` | `75c1224a18f464ecbe28a7235f3d3e7325aad69c443e811e0cee5da7ebfdf2e3` |
| `replaceUnreachable_out_of_range` | — | `ce5b3e2a6c63e2a3f7438797350078ffbb448123ef702389f4e24fd5ecc04068` | `c72b447d7afb2ceec98f0384117ed3bd7ef39f31298f12b9bc5b50f13e0cc1ee` |
| `revChainWT_nil` | P | `686d1b76cb4b3dd91bbe261a53b3acdd79b81ccb7421fe166b539bab8943da0d` | `3b0afbc1b4d5b973a4cf8f8520d57d29c40efea9499817254f2395facb22f88b` |
| `revRefinement_admits_ub_introduction` | P | `952690c2dafd4e4acfde55cd90a952cb68efdf53b9dc8a14d249358c1e6a540d` | `9ceb0aacb2b4e3173905aa4a5cae6ff28c3753520db59c48e9cf1f895c9f8aea` |
| `run` | P | `2b100f281fdfb6d0d5d5137886a7765de02bdc8c06f8b56c13cdbe8b9ac2d3ab` | `7f43e3ac12544d421ba89ea4b20a1e8680c2a175adc6aef4d07b1df477a7ce11` |
| `run_pHalt` | P | `7047f7981b14decd1c1765e73227a53c546de174dd2a3dc1441a713365a413c6` | `32d7560e7d098fdfa230e8d24345b61e0e6bee190384ad1f84e06a3202ce5667` |
| `run_spin` | P | `746f9c9489351234dede975534031a2ed2a555f0eccd0347fed5acc8ef5ff108` | `32fc2fac3559195b1d253af80d37d313c756e483b14b90ed57884a258143ab63` |
| `selectTarget` | — | `d801956ac0fbdcf078517768276f9730d86467694f0dd2dc93a94378dc45fbb6` | `6756bc3acdb351f0469a9b85d7f6a72b7bc55cd7ad08861439644e6e752ade6f` |
| `selectTarget_first_match` | — | `ad61aab7acda7403e95f83ff44b2cee2f8642e4b6457ddbcb7ad38e17704c2a2` | `ed7b650d05427bed27007682cd15204a55c2a26b3dfffb8be179d24ddbb41afd` |
| `selectTarget_otherwise` | — | `d5a97e354c3d12c6a5f48b4bd30e7dc939cfcf0c6202817837f026846a6e298b` | `ed7b650d05427bed27007682cd15204a55c2a26b3dfffb8be179d24ddbb41afd` |
| `setTerm` | P | `4ec7ddd7c51dec25f73548ee624dc273487bd42bf62bc278d8703435405ff773` | `60d9db909ef7e19f2a036b32db563bac8018b499722edd75ab8087fee8c0b870` |
| `setTerm_out_of_range` | P | `f2b685b290c131fca068272c344db2936063f098cf8f911a5b209f3ecdabe707` | `a365914b069ad778374d59d5ee7109cf2d5a269f810772a8814bd954b8d0fe34` |
| `state_locals_example` | P | `0f6e29606d2756d83fbf004f795e95f97fe2a333e3725aa6db355e25fad50156` | `a5c4fc773eedb09453cc28895dc4444d3c064b0105d0d8c3019fbf490dc90de9` |
| `state_noMem_example` | P | `236fdbe04b4d3bbed00c190330436bf8e3b1804824e8e2643a2e104587b2e86a` | `5ed96beb3367def0b72ec6ac78e85f9ab68a86d00f0a6582d62a9214d4c750dd` |
| `state_set_frames` | P | `86297b1622dc021d20c51d7c818ea5fbf975ff82544afbd68c2235a90a384382` | `3349baad3e8eac9bfa1f061eb502ec199586c45a1c6438e24999cfb9024eb46b` |
| `state_set_updates` | P | `916a60cd2fa650c79066275708589403a7261b027a85f84878a6bb232f2cfc1d` | `3349baad3e8eac9bfa1f061eb502ec199586c45a1c6438e24999cfb9024eb46b` |
| `step` | P | `da2590014d8febf4647d9894ac812f6f3b9ef57500dc8e2b7f7efc63fa52e7bd` | `ab7ab0ef8cf49c09f94d14b2aaf9de5e761addc36719fb6e98355844084f7090` |
| `step_emit7` | P | `9368d4ff54d65576c462278a52363dc049b5e1b8d1d4fc273e5f5b8bdac99bfb` | `ff623eb1e5cabdc3b943ac904f086aa8d228c2cc7b999182604c2934a98f0bdb` |
| `step_unreach` | P | `f2d447b4ccf9f197b4abcf29582e37d4dce3476333a9fcbf735d54a1cf386dd0` | `da55997da7728242de17953a439f980174c0d0e32daede215598bdb8424e4f59` |
| `ty_align_distinguishes` | — | `6c9cef3b35795a4b02c617b7a977311953693065eb08cd8aee4eb16405ac1eca` | `f847284b71ce5d212c05229c3eed65396d6a9b22244869e43fbdb10624862c85` |
| `ty_fields` | — | `de6be43c51be1cdc1347c7f4c05e3f0e22df4c04af6d66c8653b8402052f0c89` | `c3b15a7725e3a812bc8cfee14275047a62c9d8529105a59eb3273970925c1719` |
| `ubFree_halt` | P | `5433fd10a6bd2071652ec305209da3b7ba9911707510cbd3ccd1a5776be82447` | `e3ac4b9234da1bb6e6abebad7baef5363e043681d49d051b4dc95949d2078536` |
| `wp` | P | `768bc32ae2c10812d5bb09eead5845fa6c4eac6ce0f391b58d4c517e78841190` | `22295ca7036d7571803db66201ca9bf6f305ce3afd4a6e04f3dac1df37fce821` |
| `wpFrom` | P | `711364ccfa4f7efba6726cc578dffa57a61f9715428ffcbce067631078b7f4e2` | `a08dc4f7d2c9a8b31e3ad425faa722c720345b8b542318320006ee05c31ccb15` |
| `wpFrom_assume` | P | `b2b43176bfb8ff7f4070a91dfac2c96b497d6dfe343b4f897a062ad2d447ef9f` | `400948e02829aed37b7cd44b1c8c8a62bed87dbc70024381c7fec29216165d18` |
| `wpFrom_unreachable` | P | `68f67c892fa1823e0302ed7b65e608d73e9cc017ac54c1ca0a34c1ac0c6b1035` | `400948e02829aed37b7cd44b1c8c8a62bed87dbc70024381c7fec29216165d18` |
| `wp_halt_true` | P | `d597a1153796f902253cdab07e47c86e98f95c7eebef84e6f4b6edf4d799779f` | `2161a8e4bff870f1d258e6c52b591ba032e04fcbcfae83b57162588cb0239aa6` |
| `zeroPre_copy_checks_src` | P | `8ec048c2509acff9efb05037b37a283557b404b733d43102dd2464815204879f` | `5af41a836d3efd11cf89681de6f69538a8f4158c2e40e9cb4ecd452558dd8c2d` |
| `zeroPre_of_align_one` | P, C, Q | `74739d53971babca7a01f4a526a53206f2e309464cac1db80c7dc6482b04f3bf` | `091e9bd202bab6553878a770f5bf5f7254e64f840a760d2c53c6f0fd0731986a` |
| `zeroPre_read_aligned` | P | `b04b9cbf0b2cb8e45477374eebadee5fa7a3d68416862a986cf2267150a8bbaf` | `5af41a836d3efd11cf89681de6f69538a8f4158c2e40e9cb4ecd452558dd8c2d` |
| `zeroPre_read_misaligned` | P | `450a702e573a122aa2918b04151d42a33cb7bdfd32e2b2a137fba6bdab984551` | `5af41a836d3efd11cf89681de6f69538a8f4158c2e40e9cb4ecd452558dd8c2d` |

### Primary sources

All source quotations were checked on 2026-11-21. Line numbers refer to the pinned revisions.

- rust-lang/rust, commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`: `library/core/src/ptr/mod.rs` L18–19 (module safety bullets), L61–62, L479, L483, L776, L778, L1613, L1618, L1620, L1768, L1873, L1986; `library/core/src/hint.rs` L16, L146; `compiler/rustc_mir_transform/src/unreachable_prop.rs` L1–3, L19–20, L89–90, L120–122, L136–140; `compiler/rustc_session/src/options.rs` L2654–2656 (documentation and source).
- rust-lang/rust, tag `1.80.0` (commit `051478957371ee0084a7c0913941d2a8c4757bb9`): `library/core/src/ptr/mod.rs` L18, L1191; `library/core/src/intrinsics.rs` L2875–2876 (documentation).
- rust-lang/rust, tag `1.88.0` (commit `6b00bc3880198600130e1cf62b8f8a93494488cc`): `library/core/src/ptr/mod.rs` L18–19, L1320; `library/core/src/intrinsics/mod.rs` L3668–3669 (documentation).
- The Rust Reference, rust-lang/reference commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/behavior-considered-undefined.md` L19, L59, L110, L117 (normative for Rust as far as the Reference is; the toy is not).
- Miri, rust-lang/miri commit `7e679961edcfe2c526f19153bb8b03de346efa5c`: `src/lib.rs` L200–205 (source).
- MiniRust, minirust/minirust commit `98043a70de612f6af4eaf1e35cf0b8a6ebea22ce`: `spec/mem/basic.md` L198–203, L234–236, L260–262 (an executable specification; not the official Rust semantics).
- CompCert, AbsInt/CompCert commit `5e4ef44c57b22cdc2e1893770843fd693a5f82e1`: `common/Behaviors.v` L81–82 (`behavior_improves`).
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814 (author's version, §2.1).
- M. Barnett, K. R. M. Leino, 'Weakest-precondition of unstructured programs', PASTE 2005, pp. 82–87, doi:10.1145/1108792.1108813 (§1, §2).
- J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, 'Taming undefined behavior in LLVM', PLDI 2017, pp. 633–647, doi:10.1145/3062341.3062343 (§2.2).
- N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65–79, doi:10.1145/3453483.3454030 (§5, author's version).
- X. Wang, N. Zeldovich, M. F. Kaashoek, A. Solar-Lezama, 'Towards Optimization-Safe Systems: Analyzing the Impact of Undefined Behavior', SOSP 2013, pp. 260–275, doi:10.1145/2517349.2522728.
- S. D. Herring, 'Partial program correctness', ISO/IEC JTC1/SC22/WG21 P1494R5, 2025-02-14, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p1494r5.html.
- N. Popov, A. Ballman, 'Allow zero length operations on null pointers', ISO/IEC JTC1/SC22/WG14 N3322, 2024-08-28, https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3322.pdf (a proposal; its adoption status is not recorded here).
- V. D'Silva, M. Payer, D. Song, 'The correctness-security gap in compiler optimization', 2015 IEEE Security and Privacy Workshops, pp. 73–87, doi:10.1109/SPW.2015.33 (bibliographic data only; the text was not consulted and no claim relies on it).
- LLVM Language Reference Manual, https://llvm.org/docs/LangRef.html, rendered page retrieved 2026-11-21. This quote is unpinned: no llvm/llvm-project revision is recorded for it, so the quoted sentence may differ in other versions of the page.
- Public tracker items cited for context (not relied on as normative): rust-lang/rust#152615 (merged pull request, https://github.com/rust-lang/rust/pull/152615), rust-lang/rust#138351 (closed issue, https://github.com/rust-lang/rust/issues/138351), rust-lang/miri#5565 (closed issue, https://github.com/rust-lang/miri/issues/5565).

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The Lean project has no dependencies.

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and runs `lake build` there; rejects `sorry`, `admit`, `native_decide` and `axiom` declarations in the sources; writes and runs a small Lean audit program (`RevalidateAudit.lean`, in the temporary copy) that computes `Lean.collectAxioms` for every declaration of the library `Toy` and requires at most `propext`, `Classical.choice`, `Quot.sound`; and, for every name recorded in `audit/statements.json` or referenced by `results.json`, recomputes the statement hash (SHA-256 of the Lean `repr` of the type) and the closure hash (SHA-256 of the sorted, newline-joined lines `name : repr(type)`, with ` := repr(value)` for non-theorems, of every package constant reachable from the type through types, definition bodies and constructors; theorem bodies excluded), and compares both with `audit/statements.json`. It prints `REVALIDATED` and exits 0 when every check passes.

Manual spot check of the build and of the axioms of the main results:

```sh
cd lean
lake build
cat > /tmp/ZstAssumeAxioms.lean <<'EOF'
import Toy
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_refinesPP
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_equivPP_iff
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_equivWT_iff
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_equivPP_of_zeroPre_reachable
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_equivPP_of_anyPtr
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_equivPP_of_align_one_of_null_permitted
#print axioms Toy.ZstAssume.deleteZeroSizeAccess_equivPP_despite_reachable_zeroPre_failure
#print axioms Toy.ZstAssume.zstRead_misaligned_deletion_erases_ub
#print axioms Toy.ZstAssume.zeroCountCopy_misalignedSrc_deletion_erases_ub
#print axioms Toy.ZstAssume.zstRead_null_nonnullContract_deletion_erases_ub
#print axioms Toy.ZstAssume.copyLoopLowering_zeroCount_erases_ub
#print axioms Toy.ZstAssume.copyLoopLowering_zeroCount_clobbers_counter
#print axioms Toy.ZstAssume.insertZeroSizeAccess_refinesPP_iff
#print axioms Toy.ZstAssume.insertZeroSizeAccess_refinesWT_iff
#print axioms Toy.ZstAssume.insertZeroSizeAccess_equivPP_of_zeroPre_reachable
#print axioms Toy.ZstAssume.insertZstRead_misaligned_not_refinesWT
#print axioms Toy.ZstAssume.hoistZstRead_out_of_branch_not_refinesWT
#print axioms Toy.ZstAssume.ubCheck_of_output_misses_source_ub
#print axioms Toy.ZstAssume.ubFree_src_of_ubFree_tgt_of_refinesWT_rev
#print axioms Toy.ZstAssume.ubFree_src_of_ubFree_output_of_revChainWT
#print axioms Toy.ZstAssume.ubFree_src_of_ubFree_tgt_of_equivPP
#print axioms Toy.ZstAssume.pruneArmAssume_equivPP
#print axioms Toy.ZstAssume.pruneArmAssume_equivWT
#print axioms Toy.ZstAssume.pruneArmAssume_wp_iff
#print axioms Toy.ZstAssume.pruneOtherwiseAssume_equivPP
#print axioms Toy.ZstAssume.pruneOtherwiseAssume_wp_iff
#print axioms Toy.ZstAssume.pruneArm_refinesPP
#print axioms Toy.ZstAssume.pruneArm_wp_of_wp_src
#print axioms Toy.ZstAssume.pruneArm_equivPP_iff
#print axioms Toy.ZstAssume.pruneArm_equivWT_iff
#print axioms Toy.ZstAssume.pruneArm_equivPP_of_otherwise_unreachable
#print axioms Toy.ZstAssume.pruneArm_equivPP_of_invariant_ne
#print axioms Toy.ZstAssume.pruneArm_pSw_wp_transfers_one_way
#print axioms Toy.ZstAssume.pruneArm_pSw_refinesPP_not_equivWT
#print axioms Toy.ZstAssume.replaceUnreachable_refinesPP_iff
#print axioms Toy.ZstAssume.replaceUnreachable_refinesWT_iff
#print axioms Toy.ZstAssume.replaceUnreachable_emit_before_unreachable
#print axioms Toy.ZstAssume.replaceUnreachable_diverging_loop_not_refinesWT
#print axioms Toy.ZstAssume.pruneArmAssume_preserves_factOnDefinedRuns
#print axioms Toy.ZstAssume.pruneArm_breaks_ubDerivedFact
#print axioms Toy.ZstAssume.staleFact_fold_after_pruneArm
#print axioms Toy.ZstAssume.staleFact_fold_after_pruneArmAssume_refinesPP
#print axioms Toy.ZstAssume.factOnDefinedRuns_fold_refinesWT_not_refinesPP
#print axioms Toy.ZstAssume.emitFact_fold_after_pruneArm_not_refinesWT_input
EOF
lake env lean /tmp/ZstAssumeAxioms.lean
```

Each `#print axioms` line must report a subset of `[propext, Classical.choice, Quot.sound]` (or no axioms).

The theorems are about the toy and do not depend on any upstream revision. To re-check the modeling bridges against a newer Rust revision, diff the cited regions instead of repeating the research: the module-level validity bullets and the Safety sections of `read`, `write`, `read_unaligned`, `write_unaligned`, `copy_nonoverlapping` and `drop_in_place` in `library/core/src/ptr/mod.rs`, and `compiler/rustc_mir_transform/src/unreachable_prop.rs` (L118–141 at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`). If a zero-size requirement changes to a shape other than `anyPtr`, `aligned` or `nonnullAligned`, the zero-size results do not cover it.
