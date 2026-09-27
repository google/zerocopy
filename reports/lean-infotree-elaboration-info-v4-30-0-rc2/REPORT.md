# Lean `InfoTree` and elaboration information at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), an `InfoTree` is elaboration-time metadata attached to language-processing snapshots. It preserves information that the kernel environment alone cannot reconstruct cheaply or at all: the syntax and source position associated with an elaboration step, local and metavariable contexts, elaborated expressions and expected types, tactic goals before and after a tactic, macro-expansion input and output, completion state, and several other interaction-specific records.

The representation is a context-sensitive tree, not a flat position map. An `InfoTree` has context nodes, information nodes with nested children, and holes for postponed elaboration. Traversal must combine surrounding partial contexts to recover the `Environment`, `MetavarContext`, options, namespace, open declarations, name generator, parent declaration, and auto-implicit state that apply to a node. Server utilities then use syntax ranges plus explicit selection heuristics because tree nesting alone does not imply a unique or smallest source range.

The tree is also not a persisted replacement for `.olean` or `.ilean`. Ordinary `.olean` serialization writes the final environment. `.ilean` generation traverses available `InfoTree`s to derive a smaller references/declarations index and serializes that projection. The full `InfoTree`, including tactic states and elaboration contexts, remains snapshot metadata for the current elaboration. A later tool that needs exact local proof state or elaborator context therefore needs a live/reconstructed elaboration snapshot rather than only the compiled environment or `.ilean` index.

No fresh Lean execution was performed. The report is based on the exact pinned source and its server documentation.

## Applicability

Primary subject:

- Lean repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- version: `v4.30.0-rc2`
- relationship to Anneal: this is the Lean release selected by the Aeneas/Anneal toolchain described by the current reference corpus.

This report describes the representation and recovery boundary of `Lean.Elab.InfoTree` at that exact revision. It complements `lean-server-tactic-state-v4-30-0-rc2`, which records how the language server exposes tactic state. The server report uses `InfoTree` as an implementation substrate; this report inventories the substrate itself and what information it preserves.

“Persisted” below means serialized into a build artifact for reuse after the elaborating process and its snapshots are gone. It does not mean that an in-memory `InfoTree` cannot survive for the lifetime of a server worker or reused snapshot.

## Findings

### `InfoTree` preserves elaboration state that the kernel environment does not

The pinned server documentation calls `InfoTree` a central server metadata structure and says it carries information that cannot easily be recovered from kernel declarations: goal and subterm information with the precise local/metavariable contexts used during elaboration, macro-expansion steps, and related interactive metadata.

That distinction is visible in the type definitions. `TermInfo` stores the elaborator name, syntax, local context, optional expected type, elaborated `Expr`, binder status, and a display flag. `TacticInfo` stores the metavariable context and goal list both before and after tactic execution. `MacroExpansionInfo` stores both source syntax and expanded syntax. These are properties of an elaboration event, not merely of the final declaration installed in the environment.

Basis: upstream **documentation** + **source**.

### The tree has context, information, and hole nodes

At this revision:

```text
InfoTree
  = context PartialContextInfo InfoTree
  | node Info (PersistentArray InfoTree)
  | hole MVarId
```

An information node owns child trees produced by nested term elaboration or tactic evaluation. Context nodes do not carry ordinary `Info`; they refine the elaboration context that applies below them. Holes represent postponed terms or tactics whose information will be supplied later.

The representation therefore cannot be interpreted correctly as a collection of independent `Info` records. A consumer must traverse the structural context and account for unresolved/substituted holes.

Basis: **source**.

### Context recovery carries enough state to re-enter `MetaM`

`CommandContextInfo` stores the environment, optional final command environment, file map, metavariable context, options, current namespace, open declarations, and name generator. `ContextInfo` extends it with the surrounding declaration and auto-implicit expressions.

`PartialContextInfo` then permits nested context nodes to replace only selected pieces: a full command context, a parent-declaration context, or an auto-implicit context. Its documented invariant requires every non-command partial context to be nested under a command context. `mergeIntoOuter?` enforces this model while walking inward.

`ContextInfo.runMetaM` uses the saved environment, options, name generator, metavariable context, and a node's saved local context to run later meta operations. The pinned server utility therefore describes a contextualized info node as a “thunked” elaboration computation from which type information and symbol locations can be recovered retroactively.

Basis: **source**.

### Information-node kinds encode several different interactive questions

The `Info` sum type includes, among others:

- tactic information;
- complete and partial term information;
- command information;
- macro-expansion information;
- completion information;
- option and named-error information;
- field information;
- user-widget and custom dynamic information;
- free-variable aliases;
- field redeclarations;
- delaborated-term information;
- overloaded-choice information; and
- documentation/elaborator information.

These cases have different payloads and different positional semantics. For example, `TermInfo` carries an expression and local context, while a completion record may instead carry a partially resolved identifier and expected type. `CustomInfo` contains a `Dynamic` value, so the closed `Info` sum still admits extension-specific payloads.

A generic consumer should therefore match the information kind it needs rather than assuming every node has an expression, goal state, or even a common `ElabInfo` payload.

Basis: **source**.

### Source correspondence is carried through `Syntax`, but position selection needs policy

`ElabInfo` stores the `Syntax` for which an elaborator created the record, and the source comments explicitly note that its `SourceInfo` implicitly carries the code position. Several other `Info` cases also carry syntax directly.

This does not make the tree a unique interval index. The pinned server utilities explicitly warn that sibling info nodes may have overlapping spans, including cases created by canonical syntax expansion. `smallestInfo?` and hover selection therefore examine source ranges and apply ordering rules rather than simply picking the deepest tree node. Hover selection additionally distinguishes stop-position hits, span size, variables versus constants, and partial versus complete term information.

For position-sensitive tooling, “the `InfoTree` node at this position” is consequently incomplete without the query's selection semantics.

Basis: **source**.

### Tactic-state records preserve both sides of a tactic step

`TacticInfo` stores `mctxBefore`, `goalsBefore`, `mctxAfter`, and `goalsAfter`. The goal-selection utility uses source positions and nested tactic information to decide whether a query should expose the state before or after a tactic. It can therefore answer a position query without rerunning the tactic, provided the relevant snapshot and tree are still available.

The resulting tactic state is still tied to the saved elaboration contexts. Goal identifiers alone are not sufficient: pretty-printing and metavariable interpretation use the corresponding saved `MetavarContext` and surrounding `ContextInfo`.

Basis: **source**.

### Failed and postponed elaboration can still leave useful information

`PartialTermInfo` exists specifically for terms that did not elaborate successfully; its documentation says the purpose is to retain nested `InfoTree`s so the language server can remain interactive. `ChoiceInfo` similarly retains the partial trees of failed overloaded elaborators when all alternatives fail.

Postponed elaboration uses `hole MVarId`. `InfoState` has an immediate assignment map and a separate `lazyAssignment` map whose values are tasks. `InfoTree.substitute` recursively replaces assigned holes, while `InfoState.substituteLazy` waits for lazy assignments and applies them before the final information tree is reported.

A tree observed during asynchronous elaboration can therefore be incomplete in a principled way. Traversal helpers generally treat an unfilled hole as yielding no information rather than fabricating a result.

Basis: **source**.

### `InfoTree` is attached to snapshots and participates in incremental server reuse

The generic language `Snapshot` has an optional `infoTree?` field for “general elaboration metadata produced by this step.” Snapshot tasks are asynchronous and may form a tree. The server documentation says request handlers find and, when necessary, wait for the relevant snapshot before reading its syntax and `InfoTree`.

At the Lean-language layer, final command processing waits for lazy info assignments, obtains the command's tree, and stores it in the finished snapshot. Nested snapshots can also expose information earlier. Thus the lifetime and version of an `InfoTree` are governed by the snapshot that owns it.

This is why an interactive client must respect document-version and snapshot invalidation. The tree is a record of a particular elaboration state, not an immutable database keyed only by source text.

Basis: **source** + upstream **documentation**.

### `.olean` does not serialize the full `InfoTree`; `.ilean` stores a projection derived from it

The frontend's artifact-writing path separates the two operations. `.olean` serialization calls `writeModule` on the final environment. When `.ilean` output is requested, the frontend separately collects `infoTree?` values from snapshots, calls `Lean.Server.findModuleRefs`, converts those results to module references/declarations, constructs an `Ilean` object, and writes that object as JSON.

The source therefore supports two narrower conclusions:

1. the full `InfoTree` is not what `.olean` serialization writes; and
2. `.ilean` is derived from `InfoTree` but stores a reduced reference/declaration index rather than the full tree with local contexts, tactic before/after states, completion records, and arbitrary custom information.

A tool that has only compiled artifacts cannot assume it can reconstruct every interactive elaboration fact that existed in the original tree.

Basis: **source**.

### The same tree supports many server features, but each feature defines its own extraction semantics

At the pinned revision, the server's `InfoUtils` supplies generic traversals (`visitM`, bottom-up collection, deepest-node selection, folds) and specialized position queries. The file-worker request layer uses `InfoTree` for completion, hover, go-to/navigation, tactic goals, and term-goal information.

This shared substrate is useful for an interactive Anneal integration: a single elaboration can feed multiple proof-development queries. But the tree is not itself an LSP or RPC schema. Exposing it remotely requires a server-side operation that selects, contextualizes, and serializes the particular information needed.

Basis: **source** + **derived** interface consequence.

## Boundaries

- No fresh Lean process, LSP session, or `trace.Elab.info` probe was run.
- This report inventories the exact v4.30.0-rc2 representation. It does not claim that `Info` constructors, context fields, traversal APIs, or snapshot ownership are stable public protocols across Lean releases.
- `CustomInfo` is dynamic and can carry extension-specific values. The report does not inventory every custom payload used by Lean, Mathlib, or Aeneas.
- The report does not claim that every `InfoTree` node has a canonical source range. Some syntax is synthetic, and server queries explicitly handle overlapping or missing ranges.
- The report does not claim that every failed elaboration produces useful information. It establishes mechanisms for retaining partial/choice information and unresolved holes.
- `.ilean` is derived from `InfoTree`, but this report does not inventory the full `.ilean` schema; that is a separate reference subject.
- The full tree's absence from `.olean`/`.ilean` does not imply that all of its information is lost forever: some facts can be recomputed by re-elaboration, and some selected facts are projected into other artifacts.
- Existing server reports cover RPC/session behavior and exact tactic-state queries. This report does not repeat the full Lean server protocol.
- No claim is made here about the semantic equivalence of reused versus freshly elaborated snapshots; only the ownership and representation boundary is established.

## Evidence

**Source — primary Lean revision.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Lean/Elab/InfoTree/Types.lean`, blob `fdd5cf8581192220ef44328c757ee3f3daa2e781`: `CommandContextInfo`, `ContextInfo`, `PartialContextInfo`, `ElabInfo`, concrete info payload structures, `Info`, `InfoTree`, and `InfoState`.
- `src/Lean/Elab/InfoTree/Main.lean`, blob `7091272391123485ee731b6eedb528324ef515fe`: context merging, hole substitution, `ContextInfo.runCoreM`/`runMetaM`, formatting, tree construction, context capture, and hole assignment.
- `src/Lean/Server/InfoUtils.lean`, blob `a4b04b2b451473b4200b882f84d6142f9178a833`: contextual tree traversal, range/hover selection, contextualized info, and tactic-goal selection.
- `src/Lean/Language/Basic.lean`, blob `08f9b688fc869224c316175220403c2aeb5eb415`: `Snapshot.infoTree?`, asynchronous snapshot tasks, and snapshot-tree ownership.
- `src/Lean/Language/Lean.lean`, blob `124d4739bc910eb30ec35844348c785bf9f6c70a`: command-level info-tree finalization and attachment to snapshots after lazy hole substitution.
- `src/Lean/Elab/Frontend.lean`, blob `fd3760667db96a351b4f654720193c89bbee356e`: separate `.olean` environment serialization and `.ilean` reference/declaration extraction from `InfoTree`s.
- `src/Lean/Elab/InfoTree.lean`, blob `2bd30aea830988c19fc51176c45c2498cb96c787`: public module boundary importing the pinned `Types` and `Main` implementation.

**Documentation — same revision.**

- `src/Lean/Server/README.md`, blob `4bac3026e17b604888324821f5725e0338f802e3`: server snapshot architecture, request waiting, `InfoTree`'s role as elaboration metadata, and the `trace.Elab.info` inspection hook.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For another Lean revision, first diff these five boundaries:

1. `Lean/Elab/InfoTree/Types.lean` for `InfoTree`, `Info`, context, and payload changes;
2. `Lean/Elab/InfoTree/Main.lean` for hole assignment/substitution and context reconstruction;
3. the server's info-query utilities for traversal and position-selection semantics;
4. `Lean/Language/Basic.lean` and the Lean processor for snapshot ownership and finalization; and
5. `Lean/Elab/Frontend.lean` for the `.olean`/`.ilean` persistence boundary.

A cheap execution probe on a capable surface should elaborate one file containing a normal term, a tactic proof, a macro expansion, and an intentionally failing or postponed term with `set_option trace.Elab.info true`. Preserve the printed tree and exact Lean revision. Then query hover and tactic goals at positions that lie inside nested/overlapping syntax and compare the selected records with the tree.

To revalidate persistence, compile the same file with `.olean` and `.ilean` output, inspect the `.ilean` JSON, and confirm which reference/declaration facts survive after the live server process is gone. This probe establishes the artifact projection and query behavior for that revision; it does not make the internal `InfoTree` layout a stable external protocol.