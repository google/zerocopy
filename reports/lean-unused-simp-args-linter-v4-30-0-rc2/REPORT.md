# Lean `linter.unusedSimpArgs` behavior at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
(`v4.30.0-rc2`), `linter.unusedSimpArgs` is enabled by default and reports
explicit `simp` or `simp_all` arguments for which the simplifier recorded no
supported use. The implementation is not a counterfactual minimizer: it does not
rerun the proof after deleting each argument. Instead, a successful simplifier
invocation records which tracked theorem, unfolding, simproc, and local-let
origins were actually used, stores a Boolean mask in the elaboration info tree,
and lets a command linter turn false mask entries into warnings.

That distinction controls how the warning should be interpreted in generated
proofs. An argument reported unused was not observed as a tracked simplifier use
for that source occurrence. The warning does **not** establish that removing the
argument preserves the proof in every case. Lean explicitly documents one
important exception: `simp [← thm]` can affect the active simp set by disabling
the opposite direction even when the reversed theorem itself is never recorded as
used. The warning therefore includes a special caveat for reversed arguments.

The implementation also deliberately trades completeness for safety and
practicality. Several argument classes are always treated as used because their
use is not tracked. Equation-theorem origin collapsing and duplicate explicit
arguments can suppress warnings. Calls produced inside macros are intentionally
excluded when they lack a source range. If the same source `simp` syntax executes
multiple times, Lean ORs its usage masks and warns only when an argument is unused
in every execution.

Two control-flow details are easy to miss. First, tracking happens only after a
successful `simp`/`simp_all` call reaches the post-execution hook, so a default
`failIfUnchanged` failure produces no unused-argument mask. Second,
`tactic.simp.trace` and unused-argument tracking are mutually exclusive in this
implementation: when that trace option is enabled, the tactic emits the simp
trace instead of recording the linter mask.

No Lean executable was run for this report. The findings come from exact pinned
implementation source and checked-in regression tests.

## Applicability

This report applies to Lean 4 revision
`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, released as `v4.30.0-rc2`.
It covers the built-in `linter.unusedSimpArgs` option and command linter, together
with the `simp` and `simp_all` tactic hooks that feed it.

The relevant implementation is split across three layers:

1. `Lean.Elab.Tactic.Simp` registers the option, executes the simplifier, turns
   `Simp.UsedSimps` into per-argument masks, and writes custom info-tree nodes.
2. `Lean.Linter.UnusedSimpArgs` scans those nodes after command elaboration,
   aggregates repeated executions, and emits warnings plus edit hints.
3. `Lean.Linter.Basic` determines whether the linter is enabled from the specific
   option, `linter.all`, linter sets, and the option's default.

Checked-in tests at the same revision document intended behavior for direct
theorem/definition arguments, duplicates, equation theorems, local hypotheses,
simprocs, lets, repeated tactic execution, macros, option scoping,
`failIfUnchanged`, and reversed simp arguments.

The report does not claim that this behavior is stable across Lean versions. In
particular, the set of tracked argument classes, the representation of
`Simp.UsedSimps`, the info-tree aggregation policy, and the interaction with
tracing are implementation details at this exact revision.

## Findings

### The linter is default-on, but ordinary linter option precedence still applies

`Lean.Elab.Tactic.Simp` registers `linter.unusedSimpArgs` with
`defValue := true`. A user therefore gets the linter without setting an option
explicitly.

`Lean.Linter.Basic.getLinterValue` still applies the standard linter precedence.
An explicit value for `linter.unusedSimpArgs` wins first. If the specific option
is absent, an explicit `linter.all` value controls the result; otherwise enabled
linter sets and the linter's own default provide the fallback. Because this
linter's default is true, an explicitly scoped `set_option linter.all false`
can suppress it, while an explicit `set_option linter.unusedSimpArgs true`
overrides that global setting.

The regression test `tests/elab/12559.lean` checks that `linter.all true`
enables the warning and that a scoped `linter.all false` suppresses it.

Basis: **source** plus checked-in **source** tests.

### The warning is based on recorded use, not on deleting each argument and replaying the proof

After a successful `simp` or `simp_all`, the tactic receives
`stats.usedTheorems`, a `Simp.UsedSimps` set that records origins used by the
simplifier. `warnUnusedSimpArgs` walks the elaborated explicit simp arguments and
asks whether each supported argument contributed an origin present in that set.
It then stores the resulting Boolean mask in an `UnusedSimpArgsInfo` custom
info-tree node.

The later command linter reads that mask. A false bit means the corresponding
explicit argument had no supported recorded use in the executions represented by
that source occurrence. The linter does not prove necessity by rerunning the
tactic without the argument, nor does it compare the final proof term before and
after deletion.

This makes "unused" a concrete implementation notion: "not observed in the
tracked simplifier-use set," subject to the tracking and aggregation rules below.
It should not be read as a general semantic guarantee that deleting the syntax is
behavior-preserving.

Basis: **source**; the interpretation is **derived** directly from the data flow.

### The implementation tracks theorem/unfolding entries, simprocs, and local lets

For an elaborated simp argument represented as `.addEntries`, the collector marks
the argument used if any contributed theorem or unfolding origin occurs in
`Simp.UsedSimps`. For `.addSimproc`, it checks the registered simproc declaration
origin. For `.addLetToUnfold`, it checks the corresponding local free-variable
origin.

These are the direct argument classes for which the pinned collector tries to
distinguish used from unused. The warning can therefore identify ordinary named
theorems and definitions, tracked simprocs, and explicit local-let unfolding when
the simplifier reports their use.

Basis: **source**.

### Several argument classes are deliberately never reported unused

The same collector unconditionally returns `true`—that is, "treat as used"—for
`.erase`, `.eraseSimproc`, `.ext`, `.star`, and `.none`. The source comment says
these cases are "not supported yet."

This is a deliberate false-negative boundary. For example, the linter does not
attempt to prove that `*`, an erase directive, or an extension-set argument was
irrelevant. The absence of a warning for these forms says nothing about whether
they changed simplification.

The `.none` case also means an argument elaboration result represented by that
variant is conservatively excluded from unused reporting. This report does not
generalize that statement to failures that abort tactic elaboration altogether.

Basis: **source**.

### Equation-theorem identity collapsing can hide unused explicit arguments

For theorem entries, `warnUnusedSimpArgs` does not always compare the exact theorem
name supplied by the user with the recorded origin. If the theorem is recognized
as an equation theorem such as `foo.eq_1`, the helper
`usedThmIdOfSimpTheorem` maps it to the parent declaration origin because the
simplifier's use tracker records the declaration name.

The source explicitly notes the consequence: an explicitly supplied equation
theorem can be considered used when only another equation associated with the
same declaration actually mattered. This can suppress an unused warning.

The checked-in `simpUnusedArgs.lean` tests preserve several equation-theorem cases,
including one called out in a comment as a warning that could be emitted but is
not yet.

Basis: **source** plus checked-in **source** tests.

### Duplicate explicit arguments can produce false negatives

The test suite states that duplicate arguments are not warned about "yet." This
follows naturally from origin-based accounting: two syntactically distinct
arguments that contribute the same tracked origin cannot be distinguished merely
because that origin appears in `Simp.UsedSimps`.

Consequently, `simp [some_def, some_def]` may use the definition once while both
explicit occurrences escape an unused warning. The linter is useful for pruning
many redundant generated arguments, but it is not a uniqueness checker for the
argument list.

Basis: checked-in **source** tests plus a **derived** explanation from the pinned
origin-tracking implementation.

### Repeated execution of one source occurrence is aggregated with logical OR

One source-level `simp` syntax can execute more than once, for example under a
tactic combinator that applies it to multiple goals. Each execution can produce a
different usage mask. The command linter groups `UnusedSimpArgsInfo` nodes by
`Syntax.Range` and combines masks with elementwise logical OR.

An argument is therefore warned about only if its mask bit is false in **every**
execution of that same ranged source occurrence. If any execution used the
argument, the aggregate bit is true and no warning is emitted for that argument.

This behavior is intentional: the comment on `warnUnusedSimpArgs` explains that
the same syntax can execute multiple times and different arguments may be used on
different steps. The test suite includes multi-branch examples that exercise this
policy.

Distinct source occurrences have distinct ranges and are linted independently,
even when their text is identical.

Basis: **source** plus checked-in **source** tests.

### Macro-expanded simp calls without a source range are intentionally skipped

While scanning custom info nodes, the command linter requires `info.range?`.
When no range is available it skips the node. The source comment explicitly
connects this behavior to macros: it prevents warnings for unused simp arguments
inside macros, where the linter may not be able to see all uses of that macro and
a warning could therefore be incomplete.

The pinned test suite defines macros that expand to `simp [...]` and confirms that
their internal extra simp argument does not produce a warning, including a
variant that preserves a macro syntax anchor.

This is another completeness boundary rather than evidence that macro-generated
simp arguments are semantically necessary.

Basis: **source** plus checked-in **source** tests.

### Warnings are emitted later by a command linter, not directly by the tactic

The tactic-side `warnUnusedSimpArgs` name is slightly misleading from a lifecycle
perspective: it computes a mask and pushes an info-tree node. It does not itself
log the final unused-argument warning.

`Lean.Linter.UnusedSimpArgs.unusedSimpArgs` is registered with
`addLinter`. During command linting it walks the elaboration info trees, collects
the custom masks, sorts source occurrences by position, and calls
`warnUnused` for false bits.

This split lets Lean reconcile multiple executions of one syntax occurrence before
deciding which arguments to report. It also means that both phases' option and
source-information conditions matter.

Basis: **source**.

### Option scoping can suppress either data collection or final linting

The tactic hook checks `linter.unusedSimpArgs` before it writes an info-tree mask,
and the command linter checks the option again before scanning the command's info
trees.

A scoped option around a particular tactic can therefore suppress collection for
that tactic even if the surrounding command is otherwise linted. The checked-in
tests include an `example` whose tactic body locally sets
`linter.unusedSimpArgs false`; no warning is expected. A command-level scoped
setting can suppress the linter at the command layer as well.

For generated proof tooling, this means the presence of the default-on linter is
not solely a property of the final source text's explicit simp arguments; option
scope around the tactic or command is part of the diagnostic behavior.

Basis: **source** plus checked-in **source** tests.

### A simplifier failure before the post-execution hook produces no unused-argument mask

Both `evalSimp` and `evalSimpAll` invoke the simplifier before running the
unused-argument collector. If simplification throws, control never reaches the
collector for that invocation.

The most visible checked-in case uses the default `failIfUnchanged` behavior. A
`simp [some_rdef]` that makes no progress emits the `simp made no progress` error
and no unused-argument warning. The same example with
`-failIfUnchanged` reaches the post-execution hook and reports `some_rdef` as an
unused argument while leaving the original goal unsolved.

The safe general statement is control-flow based: if the tactic aborts before
post-execution tracking, this linter has no mask from that invocation. The report
does not claim that every possible simplifier error follows an otherwise identical
diagnostic path.

Basis: **source** plus checked-in **source** tests.

### `tactic.simp.trace` suppresses unused-argument tracking in this revision

After simplification, both `evalSimp` and `evalSimpAll` use an `if`/`else if`
chain. If `tactic.simp.trace` is enabled, they call `traceSimpCall`. Only in the
`else if` branch do they call `warnUnusedSimpArgs`.

Therefore enabling this trace option prevents these tactic hooks from writing the
unused-argument mask, even when `linter.unusedSimpArgs` is otherwise enabled.
The later command linter cannot warn for a call whose mask was never emitted.

This interaction is easy to misread as a linter result: turning on the trace can
make warnings disappear because tracking is bypassed, not because all explicit
arguments suddenly became used.

Basis: **source**.

### The edit hint removes one argument, but reversed arguments get an explicit semantic caveat

For each false bit, `warnUnused` reconstructs the simp syntax without that one
argument and attaches the resulting syntax as an edit suggestion. The warning
therefore gives a direct "omit this argument" fix.

A reversed simp lemma is special. `simp [← thm]` does more than offer the theorem
in reverse: it can also remove the opposite-direction simp rule from the active
set. That side effect may matter even if the reversed rule itself was never
recorded as used. For a `←` argument, the linter adds a note explaining that the
omission hint may fail and suggests replacing `←` with `-` when the intent is only
to disable the ordinary direction.

The test for issue #9909 preserves a case where ordinary `simp` succeeds
undesirably, while `simp [← ab]` succeeds with a warning whose note explains this
exact distinction.

This is direct evidence that the linter's warning is not a proof of semantic
redundancy.

Basis: **source** plus checked-in **source** tests.

### For generated proof scripts, the linter is best treated as a pruning diagnostic with explicit blind spots

For a generator that emits large explicit simp sets, the linter provides useful
feedback about arguments the pinned simplifier did not record using. Its
source-range aggregation also avoids flagging an argument merely because one
branch among repeated executions did not need it.

The strongest sound operational interpretation is narrower than "safe to delete":
a warning identifies a candidate for pruning. Before mechanically rewriting
generated source, a consumer should account for the reversed-rule side effect and,
where proof stability matters, recheck the resulting proof. Conversely, absence
of a warning does not establish necessity because unsupported argument classes,
macro expansion, duplicates, and equation-theorem origin collapsing all create
known false-negative paths.

Basis: **derived** from the pinned **source** behavior and tests.

## Boundaries

No fresh Lean executable or Lake environment was available for this report. The
checked-in test files are upstream source evidence about intended behavior; they
were inspected but not executed here.

This report does not establish the exact warning text, source-span rendering, or
edit-diff formatting produced by every frontend or editor. It records the pinned
message construction and representative checked-in expectations.

The report does not characterize `simp?`/`simp_all?` suggestion generation,
ordinary simp tracing beyond the `tactic.simp.trace` branch relevant here, or the
full semantics of `Simp.UsedSimps`. Those subjects are broader than the
unused-argument linter.

The report does not claim that an unreported explicit simp argument is necessary.
Known false-negative mechanisms include unsupported argument classes,
equation-theorem origin collapsing, duplicate origins, and macro-expanded calls
that lack a source range.

The report also does not claim that every warned argument is behavior-preserving
to remove. The reversed-argument note is a documented counterexample to such a
strong interpretation because `←` can disable the opposite-direction rule even
when its own rewrite is unused.

The source contains a command-level `cmdStx.getRange?` guard in the linter. This
report does not attempt to enumerate every generated or synthetic command context
in which that range can be absent.

No evidence was gathered that `linter.unusedSimpArgs` belongs to a named linter
set at this revision. Its default-on behavior and the `linter.all` precedence
described above do not depend on such membership.

## Evidence

**Subject.**
`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
(`v4.30.0-rc2`). Evidence was materially revalidated on 2026-09-27.

Primary pinned **source**:

- `src/Lean/Elab/Tactic/Simp.lean`, blob
  `3e6308c7cf806f921484155e8ff8295804b0ef45`:
  `register_builtin_option linter.unusedSimpArgs` (default-on option);
  `pushUnusedSimpArgsInfo`; `warnUnusedSimpArgs`; its
  `usedThmIdOfSimpTheorem` helper; and `evalSimp`/`evalSimpAll`. These regions
  establish tracked argument classes, equation-theorem normalization, post-success
  mask creation, option checks, and the `tactic.simp.trace` interaction.
- `src/Lean/Linter/UnusedSimpArgs.lean`, blob
  `1c8f04bef6604d01fcf3151400c16ea4807c1399`:
  `warnUnused` and `unusedSimpArgs`. These establish edit-hint construction,
  the reverse-argument caveat, command-linter registration, info-tree scanning,
  source-range grouping, logical-OR aggregation, macro/range exclusion, source
  ordering, and warning emission.
- `src/Lean/Linter/Basic.lean`, blob
  `052c9fc1b3e5c1a256ee27560075ed9135a40b4c`:
  `linter.all`, `getLinterAll`, and `getLinterValue`. These establish option
  precedence.

Pinned checked-in **source** tests:

- `tests/elab/simpUnusedArgs.lean`, blob
  `1864f5b84ae8ae0b781651bd57d760d3ba20703f`: expected warnings and
  non-warnings for definitions, theorem entries, equation theorems, duplicates,
  no-progress failure, `-failIfUnchanged`, local hypotheses, `*`, simprocs, lets,
  repeated branches, macros, option scoping, and the issue-9909 reversed-rule
  caveat.
- `tests/elab/12559.lean`, blob
  `7dd8f27e35e5f0ec66ee30383a14852206f9ef12`: expected interaction with
  `linter.all`.

There is no fresh **execution** evidence in this package. Statements about why a
particular implementation choice causes a false negative or what generated-proof
tooling should infer are labeled **derived** where they go beyond the source's
direct wording.

## Revalidation

For another Lean revision, first diff the narrow implementation regions that
define the diagnostic:

1. `src/Lean/Elab/Tactic/Simp.lean`:
   `register_builtin_option linter.unusedSimpArgs`,
   `warnUnusedSimpArgs`, `usedThmIdOfSimpTheorem`, `evalSimp`, and
   `evalSimpAll`;
2. `src/Lean/Linter/UnusedSimpArgs.lean`:
   `warnUnused` and `unusedSimpArgs`;
3. `src/Lean/Linter/Basic.lean`:
   `getLinterValue` and the `linter.all` option;
4. `tests/elab/simpUnusedArgs.lean` and `tests/elab/12559.lean`.

A small execution probe can then distinguish the behavior most relevant to
generated proofs. At minimum, include:

- one used and one unused ordinary theorem/definition argument;
- two duplicate explicit arguments;
- explicit equation theorems from one recursive definition;
- one source `simp` occurrence executed over multiple goals where different
  arguments are used in different executions;
- two separate source occurrences to confirm independent ranges;
- a macro that expands to `simp`;
- a no-progress call with default `failIfUnchanged` and with
  `-failIfUnchanged`;
- a scoped `linter.unusedSimpArgs false`;
- `linter.all false` with and without an explicit specific override;
- a reversed `←` argument whose opposite-direction removal matters; and
- the same unused explicit argument with `tactic.simp.trace` off and on.

Record the exact Lean revision, source input, invocation, and complete diagnostic
output. A passing probe establishes only these cases; source inspection is still
needed to recover newly supported argument classes, aggregation changes, or
different origin-accounting semantics.
