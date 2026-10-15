# Aeneas symbolic ownership, borrow ending, and backward continuations

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Aeneas at `21345f80fa212c596f6437378d7d57984fa2ea77` carries an ownership graph and a computation for returning values through that graph. The graph uses regular values, region abstractions, borrow/loan projectors, and ended forms. A parallel expression representation (`evalue`) preserves the computation that pure translation needs. Borrow ending is an ordered transformation with dependencies and synthesized continuations, not deletion of a reference. In backward synthesis, preventing unrelated return regions from ending is explicitly part of the implementation's soundness discipline.

The presence of representations for nested borrows and sub-abstractions does not establish general support. Several destructuring, join, and pure-translation paths reject or leave unfinished such cases. The strongest reusable distinction is between an analysis state that describes ownership and a synthesis-ready state that also has valid computational provenance.

## Applicability

This report covers selected OCaml implementation paths in [AeneasVerif/aeneas at the exact pin](https://github.com/AeneasVerif/aeneas/tree/21345f80fa212c596f6437378d7d57984fa2ea77), acquired through read-only GitHub file tools on 2026-10-15. It addresses investigation questions A13 (symbolic values and projections), A14 (borrow ending and invariants), and A17 (backward functions/continuations). It examines source, including source comments as documentation; it does not report an execution, proof check, or whole-repository audit.

The state described here is Aeneas's interpreter state over its LLBC input, not a spatial memory model of arbitrary Rust. The report does not identify a Charon revision or establish correctness of extraction, unsafe code, external function models, or Lean extraction. Those are separate links in a semantic correspondence argument.

## Findings

### 1. Three value layers preserve different information

Basis: source + documentation. [`Values.ml`, `symbolic_value`, `value`, `borrow_content`, `loan_content`, `mvalue`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L86-L213).

| Layer | Representation and purpose | Consequence |
| --- | --- | --- |
| Regular runtime-like values | `tvalue = { value; ty }`, literals, ADTs, bottom, borrows, loans, symbolic values | Locals retain concrete shape until abstraction or expansion is needed. Bottom means unavailable/uninitialized/moved, not an arbitrary value. |
| Ownership abstractions | `tavalue`, `AProjLoans`, `AProjBorrows`, concrete abstract borrows/loans, ignored and ended forms | A call can hide the internal borrow graph while retaining links needed for later ending. |
| Continuation expressions | `tevalue`, `ELet`, `EApp`, projection expressions, `EValue`, ignored and ended forms | Pure synthesis can reconstruct the values given back, even after the graph has been simplified. |

A regular `VSymbolic` has a symbolic identifier and region-bearing type. Its regular-value occurrence is interpreted as a **borrow** projector; loan projection occurs inside abstractions. This prevents interpreting every occurrence of a symbolic identifier as another independent owned value. `BorrowId` is also the loan-identifier space. A `VMutBorrow` contains its borrowed value, whereas a `VMutLoan` marks its original location. A shared loan retains the shared value; shared borrows use an additional `SharedBorrowId` to distinguish occurrences. The source documents that second identifier as an implementation convenience absent from the formalism.

Meta-values and captured meta-environments are intentionally omitted from normal symbolic traversal/equality. For example, `equal_mvalue` always returns true; `menv` compares equal regardless of its stored environment. This permits analysis convergence without requiring identical synthesis snapshots. It does **not** justify discarding snapshots during pure translation: `EValue (menv, mvalue)` captures an environment because translating a shared borrow requires looking up its loan there. [`Values.ml`, `evalue`, `menv`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L1134-L1188), [meta-environment equality](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L1572-L1576).

### 2. Projection is a region-sensitive ownership operation

Basis: source + documentation. [`InterpProjectors.apply_proj_borrows`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpProjectors.ml#L102-L253).

The projection algorithm takes a region set, a regular value, and its region-bearing type. It checks the erased type against the value type. If the type contains none of the selected regions, it produces `AIgnored (Some v)`. Otherwise it recursively projects ADT/array fields. At a reference whose region belongs to the abstraction, it creates the corresponding owned abstract borrow. At a reference outside the abstraction's region set, it may ignore the outer reference while still projecting the inner value. For shared references, this can require following the shared loan to discover inner borrows. A reserved mutable borrow cannot be projected directly; the corresponding branch explicitly raises an error.

“Ignored” therefore means that this projection does not own that component. It does not mean that the component has no semantic effect. In particular, ignored mutable-loan and mutable-borrow forms retain optional identifiers and child structure so that giving back an outer value can project its inner loans/borrows into the proper abstraction. Ended forms separately preserve the projected value and meta-value consumed or returned. [`Values.ml`, `EIgnoredMutLoan`, `EEndedMutLoan`, `EIgnoredMutBorrow`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L1241-L1443).

Loan projectors have `consumed` and `borrows` lists; borrow projectors have a `loans` list. These are needed when an ancestor region ends or only part of a projected symbolic value is returned. A loan projector becomes ended only after intersecting borrow projectors have been dealt with, rather than after an arbitrary single return. Some examples immediately following these definitions are marked wrong/obsolete upstream; the record fields and current algorithms are the firmer basis. [`Values.ml`, `aproj_loans`, `aproj_borrows`, ended projector records](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L544-L610).

### 3. Expansion updates all relevant views of the same symbolic object

Basis: source. [`InterpExpansion.expand_symbolic_value_borrow`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpExpansion.ml#L494-L529), [`apply_symbolic_expansion_to_target_aevalues`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpExpansion.ml#L48-L217).

For a mutable symbolic reference, the interpreter checks that its region has not ended, creates a fresh borrow identifier and fresh symbolic referent, replaces the regular symbolic occurrence with the mutable-borrow shape, updates both abstraction and expression projections, and emits a symbolic-expansion continuation. The regular mutable occurrence is constrained to at most one substitution. Shared expansion instead creates a shared loan/referent and distinguishes shared-borrow occurrences, including reborrows required by projections. These are graph transformations across the context, not merely a local destructuring of one variable.

The greedy expansion pass is deliberately limited to values selected as greedily expandable. Its documentation explains why unrestricted expansion of a recursive type would loop and why branching ADTs require a different path. It must not be read as a total normalization procedure that eagerly expands every recursive borrowed structure. [`greedy_expand_symbolics_with_borrows`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpExpansion.ml#L668-L742).

Branching refinement has a distinct algorithm: boolean expansion creates true and false contexts; ADT expansion enumerates structural expansions and substitutes each in its own context; integer-switch expansion substitutes each explicit target but leaves the otherwise context symbolic. Thus the implementation retains an overapproximate otherwise state rather than encoding a precise arithmetic exclusion predicate there. This describes source control flow, not a proof that all concrete executions are covered. Partial-move handling through place-access helpers was not traced here; bottom's representation alone is insufficient to justify it. [`expand_symbolic_bool`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpExpansion.ml#L531-L552), [`expand_symbolic_adt`, `expand_symbolic_int`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpExpansion.ml#L607-L666).

### 4. Borrow ending resolves priorities and returns values

Basis: source + documentation. [`InterpBorrows.end_concrete_borrow_get_borrow_core`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.ml#L15-L120), [`end_borrow_aux`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.ml#L940-L1018).

An executable outline of `end_borrow_aux` is:

1. Add the target to the dependency chain; the chain detects cyclic ending requests.
2. Search the context for the concrete borrow while remembering enclosing mutable borrows, shared loans, abstractions, and levels.
3. If an enclosing borrow/shared loan or inner loan has priority, end that loan and retry the original target. If the target is inside an abstraction outside the allowed special case, end that abstraction at the recorded level.
4. If found and eligible, replace the borrow occurrence with bottom, then give its value back to the matching loan. A mutable borrowed value must not still contain loans at this point.
5. Check disappearance and retain a synthesis snapshot when requested. Compose the symbolic continuation produced by any prerequisite endings.

A missing borrow is permitted in symbolic mode because an earlier abstraction ending may have ended several borrows together. This is a specific idempotence accommodation, not a general “missing ownership evidence is acceptable” rule. For concrete mutable borrowing, the simple shape is `x = ML l; p = MB l v` becoming `x = v; p = bottom`; abstractions require fresh symbolic values, projections, and continuation application as well.

Reserved mutable borrowing implements a two-phase discipline: creation behaves as shared borrowing; promotion ends competing shared borrows and changes the shared loan into a mutable loan. Its public contract is explicit about this ordering. [`InterpBorrows.mli`, `promote_reserved_mut_borrow`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.mli#L89-L99).

### 5. Ending abstractions follows a different dependency order

Basis: source. [`end_abs_aux`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.ml#L1175-L1288), [`end_abs_borrows`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.ml#L1357-L1455), [`end_abs_synthesize`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.ml#L1553-L1571).

An abstraction ending checks endability; ends parent abstractions completely; ends strict sub-abstractions; ends loans at the relevant level; and then redistributes the abstraction's borrows. Borrow traversal is depth-first at the selected level. Mutable abstract borrows are converted into fresh symbolic given-back values, with ended ownership and expression forms recording that transition. The interpreter updates `ended_regions`, records the ended level, removes a level-zero abstraction or retains the remaining levels, and synthesizes an end-abstraction expression.

`'static` is special: eliminating an abstraction tracking it does not mark the static region ended. `Contexts.abs_is_endable` combines `can_end` with the static-region policy and whether the abstraction still has borrowing content. An attempted ending of a frozen abstraction raises an error; an abstraction owning static may remain non-endable even with its own `can_end` flag set. [`Contexts.abs_is_endable`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Contexts.ml#L811-L840).

### 6. A call abstraction connects forward results to a backward computation

Basis: source. [`InterpStatements.eval_function_call_symbolic_from_inst_sig`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpStatements.ml#L1346-L1535).

A symbolic call validates supported signature types, evaluates operands, creates a fresh symbolic result, and creates abstractions associated with instantiated region groups. Borrow projections consume relevant input references; loan projections describe the result. The expression continuation contains `EApp (EFunCall abs.abs_id, ...)`: the backward computation receives values returned through the result-side loans and supplies values for the input-side borrows. The call then assigns its symbolic result to the destination and emits the regular symbolic call node. Some loan-free abstractions for unit-returning calls can end immediately under the configured rule.

`abs_cont` stores optional input and output expressions. An ordinary call abstraction has both. Input synthesis abstractions are a deliberate exception and must not be merged indiscriminately with ordinary abstractions. During analysis, a continuation may be absent. `ELoop` and `EJoin` identify analogous backward computations introduced by loops and branch joins. These constructors retain abstraction identity so later merging does not lose the origin of a backward call. [`Values.abs_fun`, `abs_cont`, `abs`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L1111-L1132), [continuation and abstraction fields](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/Values.ml#L1464-L1542).

Pure translation first uses ownership `avalues` to choose a stable order of consumed inputs, translates the continuation expression, builds its output pattern, and uses `avalues` again to order given-back outputs. It builds a lambda over the inputs; an empty-input/empty-output continuation can disappear. Translating an ordinary continuation with `cont = None` is an internal error. The ordering is not whatever traversal order the continuation expression happens to have. [`SymbolicToPureAbs.abs_cont_to_texpr_aux`, `translate_abs_to_cont`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPureAbs.ml#L1050-L1109).

### 7. Backward synthesis restricts which regions may end

Basis: source + documentation. [`Interp.evaluate_function_symbolic_synthesize_backward_from_return`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/Interp.ml#L387-L506).

For one backward region group, Aeneas freshly instantiates the return signature, determines ancestor region groups, and projects the returned value into return abstractions. It marks only the current and ancestor return groups endable. It then marks the corresponding **input** abstractions endable and ends them in hierarchy order; their dependencies force the necessary return-side endings. Static backward synthesis additionally enables static abstraction ending. The source explicitly describes restricting return-region endings as important for soundness and part of borrow checking.

Derived requirement: a computation for region `'a` must not silently require consuming an unrelated return component for region `'b`. Freezing that component turns an otherwise hidden dependence into a failed ending request. Removing the restriction to make an input pass would change the admission discipline; the inspected source provides no theorem licensing such a change.

The region hierarchy is computed from signature lifetime constraints and type structure, grouping mutually outliving regions into SCCs. Edges run from longer to shorter lifetimes; group dependencies prescribe ending order. The code has a special static group and explicitly ignores locally bound regions when adding these edges, so this account is not a general higher-ranked lifetime solver. [`RegionsHierarchy.compute_regions_hierarchy_for_sig`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/RegionsHierarchy.ml#L60-L127), [group and static construction](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/RegionsHierarchy.ml#L295-L356).

The following interpretations are **derived comparisons**, not equivalence theorems. A continuation is the most literal account here: an `EApp` computation consumes future returned values and computes restored ones. A lens analogy highlights a forward view and a later update, but ordinary lens laws are not established, and panic plus region dependencies complicate them. A resource-transformer view highlights consumed loans and restored borrows together with ending permissions. A separation-logic implication analogy would require an independently specified assertion model and frame rule; the inspected OCaml types do not provide such a model. Likewise, `can_end`, static permission, levels, and dependency chains act as dynamic permissions; they are not an inspected capability-indexed type system. Chain-cycle detection is executable failure handling, not a proved well-founded termination measure for all recursive ending requests.

### 8. Invariant checks are useful evidence, with an explicit runtime gate

Basis: source. [`Invariants.check_invariants`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/Invariants.ml#L1002-L1011) checks borrow/loan relations, borrowed-value restrictions, typing, symbolic projection consistency, and unique abstraction identifiers only when `Config.sanity_checks` is enabled (default false in `Config.ml`). The borrow/loan checker first registers loans, then borrows, including checks for ignored identifiers. Borrowed-value checks exclude mutable loans under shared loans and reserved mutable borrows inside another borrow; bottom below a borrow is configurable and allowed by the inspected default.

The symbolic-value checker computes unions of loan and borrow projections, uses mutable/conflict regions when deciding collisions, and checks containment of borrow projections by loan projections. Shared-region overlap must not be mistaken for conflicting mutable ownership. A nearby TODO does not negate the implemented later collision checks; conversely, those checks do not establish a mechanized preservation theorem. [`check_borrowed_values_invariant`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/Invariants.ml#L310-L381), [`check_symbolic_values`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/Invariants.ml#L901-L988).

## Boundaries

- **Unsupported in identified paths:** destructuring abstractions rejects several nested-borrow shapes; join matching also has explicit nested-borrow rejection branches. This is narrower than declaring every nested reference program unsupported. The representation and some algorithms handle nested structure, but that does not make all consuming paths total. [`destructure_abs`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpBorrows.ml#L1935-L2132).
- **Unsupported in identified translation path:** `ended_abs_cont_to_texpr_aux` asserts `abs_level = 0` with “Unimplemented”; ordinary continuation translation contains a TODO to handle sub-abstractions properly and fixes its local level to zero. The source therefore does not support inferring full pure translation of arbitrary sub-abstraction levels. [`SymbolicToPureAbs`](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPureAbs.ml#L1250-L1290).
- **Unknown:** a complete admissible subset of nested references across all expansion, join, and backend paths; a proof connecting these exact OCaml transitions to a published calculus; and a theorem that the exact generated backward expressions preserve the concrete Rust behavior for all admitted programs. No such theorem was located or checked in this bounded source reading.
- **Not examined:** unsafe/spatial memory, raw pointers, concurrency, exceptional unwinding, FFI, destructor fidelity, all backend implementations, or all tests.
- **Current versus paper:** source comments explicitly refer to an underlying formalism, and the join-marker comment points to a paper. This report establishes the current pin's records, checks, and transitions. It does not silently identify current `evalue`, meta-state, static-region, or sub-abstraction machinery with a paper definition or extend a paper theorem to it. The paper's theorem statements and artifacts require separate exact-subject evidence.

For a semantic correspondence argument, the source facts imply distinct obligations: relate instantiated LLBC types and regions to concrete borrowing; preserve the borrow/loan and projector invariants under every transition; justify abstraction introduction and ending; prove that each evalue continuation returns the same values as the ownership transition; preserve that relation under merging and projection; and establish the symbolic-to-pure and backend links. These are derived obligations, not established theorems in this report. Passing optional runtime checks or seeing a well-typed generated function discharges neither the entire relation nor extraction correctness.

## Evidence

All immutable links above point to repository `AeneasVerif/aeneas`, revision `21345f80fa212c596f6437378d7d57984fa2ea77`. `source-reading.json` preserves blob identities, exact paths, inspected regions, and a question-to-finding crosswalk. Acquisition used the connected GitHub file API, with full file responses held transiently for targeted reading; no upstream code was executed. Evidence roles are source, documentation where explaining source comments, and derived where explicitly labeled. There is no execution or normative proof evidence in this package.

## Revalidation

For another pin, first compare the records and equality/traversal behavior of `Values.ml`: particularly `mvalue`, `menv`, projector lists, `evalue`, `abs_cont`, `abs`, and `ended_subabs`. Then inspect `apply_proj_borrows`, mutable/shared symbolic expansion, `end_borrow_aux`, `end_abs_aux`, and `end_abs_synthesize`. Changes to ignored forms, child levels, dependency ordering, or continuation absence require reviewing both graph updates and pure translation.

The cheapest discriminator for the soundness restriction is the `region_can_end` predicate in backward-from-return synthesis plus `Contexts.abs_is_endable`; preserve the distinction between input and return abstractions. The cheapest discriminator for the representation/support gap is the level-zero assertion in `ended_abs_cont_to_texpr_aux` together with nested-borrow rejection branches in `destructure_abs` and `InterpMatchCtxs`.

For future execution-based revalidation, a narrow useful probe set is: returning either of two independently borrowed inputs; an outer mutable reference containing an inner lifetime; copying shared symbolic references before expansion; and a two-phase borrow promoted while a competing shared borrow remains. Record the LLBC, interpreter mode, sanity-check flag, outcome, and emitted continuation. These are proposed revalidation inputs, not runs performed here. Source comparisons establish that guards remain; only execution or proof can establish the corresponding behavior on concrete inputs.
