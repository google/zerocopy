# Aeneas symbolic ownership, borrow ending, backward continuations, resource boundaries, separation logic, and mechanized LLBC results

## Summary

Across the Aeneas symbolic interpreter, the functional Rust-to-Lean translation pipeline, the emerging Lean first-order sequential separation logic, the published ICFP 2022 / ICFP 2024 / 2024 PhD thesis / 2025–2026 formal literature, the `AeneasVerif/mechanized-llbc` Rocq development, and an executable returned-borrow update certificate on legacy `alpha24`, Aeneas's ownership and resource semantics divide into five distinct technical layers:

1. **Symbolic ownership graph, region projectors, borrow ending, and backward continuation synthesis (`21345f80fa212c596f6437378d7d57984fa2ea77`)**:
   - In `src/llbc/Values.ml` (L86–213, L544–610, L1111–1188, L1241–1576), Aeneas maintains three parallel value layers: runtime-like typed values (`tvalue`: literals, ADTs, `VBottom`, `VMutBorrow` / `VSharedBorrow`, `VMutLoan` / `VSharedLoan`, and `VSymbolic`), ownership abstractions (`tavalue`: `AProjLoans`, `AProjBorrows`, concrete abstract borrows/loans, `AIgnored`, and ended forms), and continuation expressions (`tevalue`: `ELet`, `EApp`, projection expressions, `EValue (menv, mvalue)`, and ended/ignored forms).
   - `InterpProjectors.apply_proj_borrows` (`src/interp/InterpProjectors.ml` L102–253) projects region-bearing values into abstractions (producing `AIgnored (Some v)` when no selected region appears, retaining ignored child structure for later give-back, and rejecting unpromoted reserved mutable borrows). `InterpExpansion` (`src/interp/InterpExpansion.ml` L48–217, L494–742) expands symbolic references, booleans, ADTs, and integers across regular values, `avalue` projections, and `evalue` continuations simultaneously.
   - `InterpBorrows.end_borrow_aux` (L940–1018) and `end_abs_aux` / `end_abs_borrows` / `end_abs_synthesize` (L1175–1288, L1357–1455, L1553–1571) enforce priority-ordered loan, borrow, and abstraction termination (`Contexts.abs_is_endable` in `src/llbc/Contexts.ml` L811–840). During backward function synthesis (`Interp.evaluate_function_symbolic_synthesize_backward_from_return`, `src/interp/Interp.ml` L387–506), Aeneas marks **only** the target return region group and its ancestors (`RegionsHierarchy.compute_regions_hierarchy_for_sig`, `src/llbc/RegionsHierarchy.ml` L60–127, L295–356) as endable (`can_end = true`), freezing unrelated return regions as an explicit borrow-checking soundness guard.
2. **Lifetime erasure and proof-facing functional resource boundaries (`ac9f1bc5262a5e4ff1e24ca78617121382202727` and `ca282ec2312a96f6a985a4d23a663690816d3f3e`)**:
   - In `SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`) and `Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), ordinary functional translation eliminates heap and memory reasoning by turning references `TRef (_, rty, _)` into pure values `rty`, `Box<T>` into `T` (erasing allocation identity), mutable-borrow updates into backward functions, and generic lifetime parameters into region-group interfaces before erasing them from pure types.
   - Raw pointer types (`TRawPtr`) survive in `Pure.ml` only as non-operational signature markers (`raw pointers don't make sense in the pure world`), while `src/interp/InterpPaths.ml` (blobs `ec23375a5ca0680500daea0248d2372c9901156e` and `3197a7b0367f2037611f20456d781b2ebb0739e0`, L111–112) fails closed on raw-pointer dereference (`Aeneas does not yet support dereferencing raw pointers`, preserved in `tests/src/raw_pointers.lean.out` blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`). Pure AST `mplace` metadata records variable-naming origin, **not** Rust pointer provenance.
3. **Lean separation-logic evolution across selected release, `main` prerequisites, and draft `PR #1352`**:
   - Anneal's pinned release (`nightly-2026.06.03` / `ac9f1bc5262a5e4ff1e24ca78617121382202727`) has **no** separation-logic backend.
   - Later Aeneas `main` (`b86120db3183b0107eb5f2637b11c424cd06ef1c` and `ca282ec2312a96f6a985a4d23a663690816d3f3e`) merges coinductive interaction-tree infrastructure (`Aeneas.Data.Coinductive.Effect`, `ITree` from `PR #1180`) and generic `step` specification registration (`Aeneas.Std.Spec`, `SpecInfo`, `#register_spec_info` from `PR #1267`), while `Std/RawPtr.lean` on `main` (blob `79de0729e3f3f755e10852c33de2d5f4e60f6124`) merely wraps a value `T` with `fail undef` scalar casts and `Aeneas.lean` imports no `SepLogic`.
   - Open draft `AeneasVerif/aeneas#1352` (observed at heads `75fb1479040d32d43d31b74510167ee3b873d28a` and `92552f503cd19ca023ae9897cf521db49ee8d887`) adds an affine heap assertion logic (`IProp` closed under heap extension), a typed slot-granular heap (`Std/Heap.lean`: allocation ID + `Nat` slot offset -> dependent `(ty, val)` cell, retaining freed slots so allocation IDs are never reused), interaction-tree heap effects (`RustEffect.guardedModify`), frame-quantified total (`ispec` / `DWP` least fixed point) and partial (`dispec` / `DWLP` greatest fixed point) weakest preconditions (`Std/WPDef.lean`, `Std/WP.lean`), `RawPtr` / `Buffer` models (`mut_to_raw` / `end_mut_to_raw`), and spatial tactics (`iframe`, `iintro`, `irewrite`). Even on `PR #1352`, `InterpPaths.ml` still rejects Rust raw-pointer dereference, and `Std/Heap.lean` explicitly excludes uninitialized memory, byte layout/type punning, pointer-integer casts, and concurrency.
4. **Published formal results, `mechanized-llbc` Rocq status, and end-to-end trust boundaries**:
   - The ICFP 2022 paper (`arXiv:2206.07185v2`) formalizes value-based LLBC semantics and pure lambda-calculus translation (demonstrated on a resizing hash table in F\*) while explicitly classifying the Aeneas compiler as generating a **trusted** pure translation.
   - The ICFP 2024 paper (`arXiv:2404.02680v2`, 37 numbered semantic results + 3 definitions) and Son Ho's 2024 PhD thesis (38 numbered semantic results in Chapters 9–12; trusted translation in Chapters 13–14) prove that LLBC refines a lower-level pointer language (`PL`/`HLPL`), that symbolic semantics (`LLBC#`) abstract concrete `LLBC+` execution (`Theorem 4.1`, permitting concrete divergence or panic as non-stuck outcomes under a borrow-checked function environment), and that symbolic borrow checking implies low-level memory safety (`Theorem 4.2`).
   - In `AeneasVerif/mechanized-llbc` (`1268d802a59ddb0672528f24d873ed4b3b28ca0c` and `2762a26a3c0792017fa7a731aab1683d9a4cf23a`), `src/lang.v` models a restricted common grammar (`TInt`, `TRef`, `TTuple`; `BAdd`, `BLe`; `BorrowMut`; `Nop`, `Assign`, `Seq`, `SwitchBool`, `Loop`, `Panic`, `Break`, `Continue` — with **no** function calls, returns, shared references, traits, destructors, or pure-target AST), and `src/` contains **9 `Admitted` declarations** (`7` in `src/simulations/Simulation_HLPL_plus.v` and `2` in `src/PL.v`), **11 `Abort` proof attempts** in `src/PL.v`, and **`Axiom blockof_inj`** in `src/PL.v` (`support/aeneas-published-results-and-mechanized-llbc/proof-marker-audit.json`).
5. **Executable returned-borrow update certificate on legacy `alpha24` (`aeneas-pair-returned-update-alpha24`)**:
   - For `support/aeneas-pair-returned-update-alpha24/probe.rs` (`choose` and `pub fn update_second(p: &mut (u8, u8), x: u8) { p.1 = x; }`), the `alpha24` Aeneas binary emits `choose b x y = Result.ok (if b then x else y)` and `update_second p x = Result.ok (p.1, x)` (`support/aeneas-pair-returned-update-alpha24/CapturedFuns.lean`), verified axiom-free in Lean `4.30.0-rc2` (`choose_emitted`, `update_emitted`).
   - `support/aeneas-pair-returned-update-alpha24/UpdateCertificate.lean` (`returned_update_correspondence`, depending only on `[propext, Quot.sound]`) certifies that the exact 7-step imported LLBC sequence (`support/aeneas-pair-returned-update-alpha24/selected-update.llbc.json`) updates only the root pair's second field to `(p.1, input)`, preserves all outside heap cells `j ≠ root`, cleans up temporary `_3`, initializes `_0`, and matches the emitted pure function, corroborated by an exhaustive `131,072`-case `choose` and `16,777,216`-case `update_second` native `rustc` harness (`support/aeneas-pair-returned-update-alpha24/native_control.rs`) and negative proof controls (`WrongChoose.lean`, `WrongUpdate.lean`, `ConcreteCounterexamples.lean`).

---

## Applicability

This report synthesizes findings across all repositories, revisions, tool artifacts, and publications recorded in `REPORT.json`:

1. **Aeneas Repositories and Revisions (`AeneasVerif/aeneas`)**:
   - **`ac9f1bc5262a5e4ff1e24ca78617121382202727` (`release: nightly-2026.06.03`)**: The functional translation release selected by Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` in `anneal/flake.nix`).
   - **`21345f80fa212c596f6437378d7d57984fa2ea77`**: Inspected on 2026-10-15 for the detailed symbolic value layers (`Values.ml`), borrow/loan projectors (`InterpProjectors.ml`), symbolic expansion (`InterpExpansion.ml`), priority-ordered borrow/abstraction ending (`InterpBorrows.ml`), backward continuation synthesis (`Interp.ml`, `SymbolicToPureAbs.ml`), and optional runtime invariant checks (`Invariants.ml`).
   - **`b86120db3183b0107eb5f2637b11c424cd06ef1c`** (observed 2026-09-26) and **`ca282ec2312a96f6a985a4d23a663690816d3f3e`** (observed 2026-10-14, paired with Charon `AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`): Post-June-3 `main` revisions containing merged coinductive `ITree`/`Effect` and generic `SpecInfo`/`step` prerequisites, plus `Translate.ml`, `Config.ml`, `ExtractErrors.ml`, and `Std/RawPtr.lean`.
   - **Draft `PR #1352` heads `75fb1479040d32d43d31b74510167ee3b873d28a` (observed 2026-09-26) and `92552f503cd19ca023ae9897cf521db49ee8d887` (observed 2026-10-14)**: Open draft pull request `"Extending Aeneas with first-order sequential separation logic"` (`Aeneas.SepLogic`, `Std.Heap`, `Std.WPDef`, `Std.WP`, `ITreeWP.DWP` / `DWLP`, `Std.RawPtr`, `Std.Buffer`).
2. **Mechanized LLBC and Publications**:
   - **`AeneasVerif/mechanized-llbc@1268d802a59ddb0672528f24d873ed4b3b28ca0c`** (observed 2026-09-27) and **`2762a26a3c0792017fa7a731aab1683d9a4cf23a`** (observed 2026-10-15, full 28-file `src/` audit).
   - **Literature**: Ho & Protzenko ICFP 2022 (`DOI 10.1145/3547647`, `arXiv:2206.07185v2`, PDF SHA-256 `5a75ed1543f5db5a47b7506753898443bc7b88ecb7a2f76325e80ed5494664bc`), Ho, Fromherz & Protzenko ICFP 2024 (`DOI 10.1145/3674640`, `arXiv:2404.02680v2`, PDF SHA-256 `ff1f01d5bcd98c6387b24dcc06ce76e5f15d6c1234d199c0b1311ce7645bebda`), Ho 2024 PhD thesis (`https://www.sonho.fr/papers/thesis-manuscript.pdf`, SHA-256 `0c1b720ff28c004211f47aa288efe3f22a471531f28e427a576b7926264bce07`), Ho et al. Charon tool paper (`arXiv:2410.18042v2`, CAV 2025), Ho et al. SymCrypt draft (`arXiv:2609.15648v1`), and Klaus, Tolmach & Conejero experience report (`arXiv:2605.30106v1`, citing `runtimeverification/p3-hax-lean-fri-pipeline@4fab6ff08a8e515321675ca121f9ad36c38268ab`).
3. **Legacy `alpha24` Executable Certificate Bundle (`aeneas-pair-returned-update-alpha24`)**:
   - Aeneas binary (`sha256: 244397c4178329f2b8ab48240cd19dafd6511efb6c4e78be6345011ca8786f8e`), Charon `0.1.210` (`sha256: 51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`), `rustc 1.98.0-nightly` (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `sha256: 2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`), Lean `4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `sha256: b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`), and Lean kernel nested-inductive validation commit `leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808`.

### Shared vs. Revision-Specific Behavior

| Capability / Layer | Anneal-Selected Release (`ac9f1bc5262a...` / `alpha24`) | Later Aeneas `main` (`b86120db...`, `ca282ec2...`, `21345f80...`) | Open Draft `PR #1352` (`75fb1479...`, `92552f50...`) |
| --- | --- | --- | --- |
| Safe-borrow functionalization (`&T` -> `T`, `&mut T` -> forward + backward function, `Box<T>` -> `T`, lifetime erasure) | **Active** (`SymbolicToPureTypes.ml`, `Pure.ml`) | **Active** (detailed `tvalue`/`tavalue`/`tevalue` & `region_can_end` audited at `21345f80...`) | **Active** alongside spatial library |
| OCaml interpreter handling of `Deref` on `TRawPtr` (`src/interp/InterpPaths.ml`) | **Rejected** (`blob ec23375a...`) | **Rejected** (`blob 3197a7b0...`, L111–112) | **Still rejected** (`blob 3197a7b0...`, L111–112) |
| Coinductive `ITree` / `Effect` and generic `SpecInfo` / `#register_spec_info` (`step`) | **Absent** (`Result` is 3-constructor inductive `ok \| fail \| div`) | **Merged** (`PR #1180`, `PR #1267`) | **Present** (`Result = ITree RustEffect`, `DWP` / `DWLP`) |
| `Aeneas.SepLogic` (`IProp`), typed-slot `Std/Heap.lean`, `ispec`/`dispec`, `iframe`/`iintro`/`irewrite` | **Absent** | **Absent** (`Aeneas.lean` does not import `SepLogic`) | **Present in draft** (slot-granular `(AllocId, Nat)` heap) |

---

## Findings

### 1. Symbolic Ownership Graph, Region Projectors, Borrow Ending, and Backward Continuations

#### 1.1 Three Value Layers (`tvalue`, `tavalue`, `tevalue`) and Meta-Environment Equality (`Values.ml`)

In `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (`src/llbc/Values.ml` L86–213, L544–610, L1111–1188, L1241–1576; indexed in `support/aeneas-symbolic-ownership-continuations-21345f80/source-reading.json`), Aeneas separates ownership analysis from pure-expression synthesis across three representations:

| Layer | Core Types and Constructors (`src/llbc/Values.ml`) | Semantic Role and Invariants |
| --- | --- | --- |
| Regular runtime-like values | `tvalue = { value; ty }`: literals, ADTs, `VBottom`, `VMutBorrow` / `VSharedBorrow`, `VMutLoan` / `VSharedLoan`, `VSymbolic` | Locals keep concrete shape until expansion or abstraction is required. `VBottom` denotes moved/uninitialized/unavailable storage, not an arbitrary value. A regular `VSymbolic` acts as a **borrow** projector so multiple occurrences of a symbolic ID are not misread as independent owned copies. |
| Ownership abstractions | `tavalue`: `AProjLoans`, `AProjBorrows`, concrete abstract borrows/loans, `AIgnored`, ended forms (`aproj_loans`, `aproj_borrows`) | Hides internal call/join/loop borrow graphs while tracking `consumed` and `borrows` lists on loan projectors and `loans` lists on borrow projectors. `BorrowId` is shared between loans and mutable borrows; shared borrows add an implementation-level `SharedBorrowId` to distinguish occurrences while the shared loan retains the underlying value. |
| Continuation expressions | `tevalue`: `ELet`, `EApp (EFunCall \| ELoop \| EJoin, ...)`, projection expressions, `EValue (menv, mvalue)`, `EIgnoredMutLoan`, `EEndedMutLoan`, `EIgnoredMutBorrow` | Records the computational provenance needed by `SymbolicToPure` to reconstruct given-back values after the ownership graph is simplified or ended. |

- **Deliberate meta-value equality omission**: `equal_mvalue` unconditionally returns `true` and `menv` compares equal regardless of its captured environment (`Values.ml` L1572–1576). This allows fixed-point and join equivalence checks (`InterpMatchCtxs`) to converge on ownership structure without requiring identical synthesis snapshots, while `EValue (menv, mvalue)` still preserves the snapshot environment needed to look up shared loans during pure translation (`Values.ml` L1134–1188).

Basis: **source** + source-comment **documentation**.

#### 1.2 Region-Sensitive Projection (`InterpProjectors.apply_proj_borrows`) and Symbolic Expansion (`InterpExpansion`)

- **Region-sensitive projection (`src/interp/InterpProjectors.ml` L102–253)**:
  - `apply_proj_borrows` takes a region set, a regular value, and a region-bearing type (checking its erased type against the value type).
  - If the type contains none of the selected regions, it returns `AIgnored (Some v)`. Otherwise it recurses through ADT/array fields: at a reference whose region belongs to the abstraction, it creates an owned abstract borrow; at a reference outside the abstraction's region set, it produces an ignored outer wrapper while still projecting inner values (following shared loans when needed to discover nested borrows).
  - Attempting to project an unpromoted **reserved mutable borrow** directly raises an internal error.
  - Because `EIgnoredMutLoan`, `EEndedMutLoan`, and `EIgnoredMutBorrow` (`Values.ml` L1241–1443) retain optional identifiers and child structure, giving back an outer value properly routes inner loans/borrows into their owning abstractions. A loan projector (`aproj_loans`, `Values.ml` L544–610) transitions to its ended form only after all intersecting borrow projectors have been resolved.
- **Synchronized symbolic expansion (`src/interp/InterpExpansion.ml` L48–217, L494–742)**:
  - `expand_symbolic_value_borrow` (L494–529) and `apply_symbolic_expansion_to_target_aevalues` (L48–217) update all views of a symbolic value across the context simultaneously: for a mutable symbolic reference (whose region must not have ended), it allocates a fresh `BorrowId` and fresh symbolic referent, replaces the unique regular `VSymbolic` occurrence with `VMutBorrow`, updates all matching `avalue` and `evalue` projectors, and emits a symbolic-expansion continuation; for a shared reference, it creates a shared loan/referent and distinct `SharedBorrowId` occurrences (including reborrows for projections).
  - `greedy_expand_symbolics_with_borrows` (L668–742) restricts eager expansion to non-recursive borrow-bearing types so recursive ADTs do not diverge.
  - Branching expansions (`expand_symbolic_bool` L531–552; `expand_symbolic_adt` and `expand_symbolic_int` L607–666) split execution into per-branch contexts; integer switches substitute concrete values on explicit target arms while leaving the `otherwise` branch symbolic (an overapproximate symbolic state rather than an arithmetic negation predicate).

Basis: **source** + **documentation**.

#### 1.3 Priority-Ordered Borrow and Abstraction Ending (`InterpBorrows.ml`, `Contexts.ml`)

- **Concrete borrow ending (`src/interp/InterpBorrows.ml`, `end_concrete_borrow_get_borrow_core` L15–120, `end_borrow_aux` L940–1018)**:
  1. Appends the target borrow/abstraction to the active dependency chain (detecting cyclic ending requests).
  2. Searches the context for the concrete borrow while recording enclosing mutable borrows, shared loans, abstractions, and abstraction levels.
  3. If an enclosing borrow/shared loan or inner loan has priority, ends that prerequisite first and retries; if the borrow sits inside an abstraction outside the permitted direct case, ends that abstraction at the recorded level.
  4. Replaces the borrow occurrence with `VBottom` and returns its carried value (which must no longer contain active loans) to the matching loan (`x = ML l; p = MB l v` becomes `x = v; p = VBottom`). In symbolic mode, a missing borrow is tolerated as an idempotence case when an earlier abstraction ending already closed multiple borrows together.
  5. Records synthesis snapshots when requested and composes prerequisite symbolic continuations.
- **Two-phase reserved mutable borrows (`src/interp/InterpBorrows.mli` L89–99)**: Creation behaves like a shared borrow; `promote_reserved_mut_borrow` ends competing shared borrows and promotes the shared loan to a mutable loan.
- **Abstraction ending (`end_abs_aux` L1175–1288, `end_abs_borrows` L1357–1455, `end_abs_synthesize` L1553–1571)**:
  - Verifies endability via `Contexts.abs_is_endable` (`src/llbc/Contexts.ml` L811–840, which combines `can_end`, static-region policy, and remaining borrow content; ending a frozen abstraction raises an error, and eliminating a `'static`-tracking abstraction does not mark `'static` ended).
  - Ends parent abstractions completely, ends strict sub-abstractions, ends loans at the selected level, and traverses borrows depth-first at that level to convert mutable abstract borrows into fresh symbolic given-back values, updating `ended_regions` and synthesizing an end-abstraction continuation.

Basis: **source** + **documentation**.

#### 1.4 Call Abstractions, Backward Region-Group Synthesis, and Runtime Invariant Gates

- **Call abstractions and continuation ordering (`src/interp/InterpStatements.ml` L1346–1535, `src/symbolic/SymbolicToPureAbs.ml` L1050–1109)**:
  - `eval_function_call_symbolic_from_inst_sig` creates one region abstraction per instantiated signature region group, projecting consumed input borrows and returned result loans and attaching `EApp (EFunCall abs.abs_id, ...)` in `abs_cont` (`Values.ml` L1111–1132, L1464–1542).
  - During pure translation (`abs_cont_to_texpr_aux` and `translate_abs_to_cont` in `SymbolicToPureAbs.ml` L1050–1109), Aeneas uses ownership `avalues` (not raw `evalue` traversal order) to fix the canonical order of consumed inputs and given-back outputs around the translated lambda continuation (raising an internal error if an ordinary abstraction has `cont = None`).
- **Soundness restriction on return-region ending (`src/interp/Interp.ml` L387–506, `src/llbc/RegionsHierarchy.ml` L60–127, L295–356)**:
  - `RegionsHierarchy.compute_regions_hierarchy_for_sig` groups mutually outliving signature regions into SCCs ordered from longer to shorter lifetimes (with a dedicated `'static` group and ignoring locally bound higher-ranked regions).
  - For each backward region group, `evaluate_function_symbolic_synthesize_backward_from_return` projects the returned value into fresh return abstractions and marks **only** the current region group and its ancestor return groups endable (`region_can_end`), freezing all unrelated return region groups before ending the corresponding input abstractions in hierarchy order. As documented in `Interp.ml`, preventing a backward function for `'a` from ending an unrelated return region `'b` is an essential borrow-checking soundness invariant.
- **Optional runtime invariant checks (`src/interp/Invariants.ml` L310–381, L901–988, L1002–1011)**:
  - Gated by `Config.sanity_checks` (default `false` in `Config.ml`), `Invariants.check_invariants` checks loan/borrow bijection (including ignored IDs), borrowed-value restrictions (`check_borrowed_values_invariant`: no mutable loans under shared loans, no nested reserved mutable borrows), typing, symbolic projection containment and mutable-region collision freedom (`check_symbolic_values`), and abstraction-ID uniqueness.

Basis: **source** + **documentation** + **derived** soundness consequence.

---

### 2. Lifetime Erasure, Safe-Borrow Functionalization, and Proof-Facing Resource Boundaries

#### 2.1 Functionalization of References and `Box<T>` vs. Non-Operational `TRawPtr` Markers

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`release: nightly-2026.06.03`) and `ca282ec2312a96f6a985a4d23a663690816d3f3e`:

| Rust Construct | Symbolic Interpreter Treatment | Pure AST (`Pure.ml`, `SymbolicToPureTypes.ml`) | Proof-Facing Resource Consequence |
| --- | --- | --- | --- |
| Lifetime parameters `'a` | Grouped into region hierarchies (`RegionsHierarchy.ml`) to drive borrow projections and backward signatures | Omitted from pure generic parameters | Lifetimes shape the generated functional interface but cannot be inspected as type parameters in emitted Lean. |
| `&'a T` (shared borrow) | Tracked as `VSharedBorrow` / `VSharedLoan`; freezes underlying mutable update paths | `TRef (_, rty, _)` translates recursively to `rty`; backward traversal stops below shared references | Becomes an ordinary pure value; reference identity and runtime alias sets are erased. |
| `&'a mut T` (mutable borrow) | Tracked as `VMutBorrow` / `VMutLoan` with region-group continuations | Forward value `T` plus backward update function(s) returning updated owners | Preserves value flow back to owners, **not** an allocation ID, reference address, or persistent capability token. |
| `Box<T>` | Treated as owned pointer value | Eliminated in forward and backward types (`Box<T>` -> `T`) | Intentionally quotients away heap indirection and allocation identity (`documentation/aeneas-overview.md` blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`). |
| `*const T` / `*mut T` (raw pointers) | `InterpPaths.ml` (blobs `ec23375a...` & `3197a7b0...`, L111–112) rejects `Deref` of `TRawPtr` | Retained as `TRawPtr` marker in `Pure.ml` (blob `acde8579...`); at `main`, `Std/RawPtr.lean` (blob `79de0729...`) wraps `T` with `fail undef` cast | Signatures mentioning raw pointers can be represented, but raw-pointer dereference fails closed (`tests/src/raw_pointers.rs` blob `c77fa473...`, `tests/src/raw_pointers.lean.out` blob `74eb81fc...`). |
| `mplace` metadata | Attached from symbolic places | `Pure.ml` `mplace` ("provenance information about the values") | Used solely to generate human-readable variable names; **not** a Rust pointer-provenance or aliasing model. |

- Consequently, the ordinary pure functional model (`README.md` blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`) has no general heap object capable of expressing that two raw pointers share allocation provenance, that a byte range is partially uninitialized, that unsafe aliases overlap an active reference, or that deallocation invalidates a derived pointer.

Basis: **source** + upstream **documentation** + checked-in failure artifact + **derived** resource boundary.

#### 2.2 Pipeline Interfaces Across Charon and Aeneas (`cf02e3f2...` and `ca282ec2...`)

In `AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d` and `AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e`:

- **Charon pass sequence and error flags**: `charon/src/transform/mod.rs` (blob `6fc5af78e919be7c23f882d0a250a9735326117f`, L97–100) runs pre/post type-consistency checks, drop normalization, control-flow reconstruction, builtin replacement, associated-type normalization, partial monomorphization, layout computation, and declaration reordering (optionally printing raw imported ULLBC before passes). `charon/src/export.rs` (blob `825319eeb8317127c61de7da83aaaeda05364518`) serializes `CrateData` with `charon_version`, `translated`, and `has_errors` (indicating partial output after frontend errors).
- **Aeneas translation vs. borrow-check-only mode**: `src/Translate.ml` (blob `2b9c4b5f8db404d2250b0ba2fe7e9b3ea1914c46`, L15–34, L129–168) runs symbolic execution to produce symbolic ASTs and translates them to pure ASTs; `src/Config.ml` (blob `6ac7f87ac268041a0c92cdcf47b3540c919a8da5`, L49–58) separates borrow-check-only mode from pure code generation; and `src/extract/ExtractErrors.ml` (blob `9169ab076be376ee6150ef7f04b298b92a840965`) records extraction failures and can emit admitted target declarations (`sorry` / `admit`) for diagnostics.

Basis: **source**.

---

### 3. Lean Separation-Logic Evolution: Selected Release vs. Main Prerequisites vs. Draft PR #1352

#### 3.1 Merged Coinductive `ITree` and Generic `step` Registration on Aeneas `main` (`b86120db...`)

While Anneal's selected release (`ac9f1bc5262a5e4ff1e24ca78617121382202727`) contains no spatial logic, Aeneas `main` at `b86120db3183b0107eb5f2637b11c424cd06ef1c` includes two merged foundational PRs:

1. **Coinductive interaction trees (`PR #1180`, merged 2026-09-08 as `df7059b918e91cd1ac37c6812f642a935948025e`)**:
   - `backends/lean/Aeneas/Data/Coinductive/Effect.lean` (blob `0015e858c1ebd2a923435be811082fa655bf531f`): generic effect signatures (input type + input-indexed output type), effect sums, and subeffect injections.
   - `backends/lean/Aeneas/Data/Coinductive/ITree.lean` (blob `0674c6ffafa146f91f7f1b8ced10428d2f148a25`): coinductive trees with `ret`, `div`, and visible-effect nodes, monadic bind, and partial-fixpoint combinators.
2. **Generalized `step` specification registry (`PR #1267`, merged 2026-08-24 as `089704f2476812da48a0c027840c9619b8d546f9`)**:
   - `backends/lean/Aeneas/Std/Spec.lean` (blob `84f7f99e38b530629bbd2cd0e0fa486d57918211`): defines `SpecInfo` and `#register_spec_info`, allowing `step` to drive proofs over user-registered Hoare triples by specifying program position, postcondition position, monotonicity rule, bind rule, and discharge tactics.
   - `backends/lean/Aeneas/Tactic/Step/Tests/Triple.lean` (blob `af674153793bf4a15c79499e419230c978c94786`): demonstrates `step` discharging sequencing and branch-splitting goals on a custom state-monad triple.
3. **Absence of `SepLogic` on `main`**: At `b86120db3183b0107eb5f2637b11c424cd06ef1c`, `backends/lean/Aeneas.lean` (blob `45ba4ca89d0e056a52e6b7920d390718b5d253b4`) and `backends/lean/Aeneas/Std.lean` (blob `19e5d842450d4ed2df711a83b3b3c5a863f1f2a8`) do not import `Aeneas.SepLogic` or `Std.Heap`, and `README.md` (blob `7326e8ea5223171dec810a0cb669b8683c48eddc`) still lists unsafe code and concurrency as ongoing separation-logic work.

Basis: **source** + repository history + **documentation**.

#### 3.2 Draft First-Order Sequential Separation Logic (`PR #1352` at `75fb1479...` and `92552f50...`)

In open draft PR `AeneasVerif/aeneas#1352` (inspected at head `75fb1479040d32d43d31b74510167ee3b873d28a` on 2026-09-26 and head `92552f503cd19ca023ae9897cf521db49ee8d887` on 2026-10-14):

- **Affine heap propositions (`IProp`)**:
  - `backends/lean/Aeneas/SepLogic/Basic.lean` (blob `5b50eb4a1532251386955d754bb5d711600d384b` at `75fb1479...`) and `SepLogic/IProp.lean` (blob `3e6957f5f1dcbd0eeeaf6e04275ea6536442ea1f` at `92552f50...` L19–21) define `IProp` as a predicate over `Heap` closed under heap extension (making the logic **affine**: `emp` holds on all heaps and `H ⊢ emp`), with standalone Iris-like syntax (`iprop(...)`, `∗`, `-∗`, `⊢`, `⊣⊢`, `↦`), disjoint-union separating conjunction, and points-to exclusivity (`q ↦ v1 ∗ q ↦ v2 ⊢ False`).
- **Typed slot-granular heap with allocation identity (`Std/Heap.lean`)**:
  - `backends/lean/Aeneas/Std/Heap.lean` (blob `d635192c03e4b49ab57f6581e4f93a2a17ed265c` at `75fb1479...`; blob `9ddd88e92d101232654988167443ac147de1bf3f` at `92552f50...`) models an address as `(AllocId, Nat)` (allocation identifier plus natural-number slot offset) and a heap cell as a dependent `(ty, value)` pair composed via a `PartialCommMonoid` disjoint-union relation (with contiguous slot-range heaps splitting/joining at slot boundaries).
  - Crucially, `Heap.lean` **retains freed slots** so allocation identifiers are never reused and tracks end-markers for whole-allocation deallocation.
  - However, the `Heap.lean` header explicitly excludes uninitialized memory, byte representation/type punning, pointer-to-integer casts, higher-order store, permissions inside the heap value itself, and the byte allocator/`Layout` API.
- **Interaction-tree heap effects and frame-quantified `ispec` / `dispec` (`Std/Primitives.lean`, `Std/WPDef.lean`, `Std/WP.lean`, `DWP.lean`, `DWLP.lean`)**:
  - `Std/Primitives.lean` (blob `915ff412447fd47ccbb3f4bbf34d84628e13a77e`) defines `Result = ITree RustEffect`, where `RustEffect` provides `guardedModify` (carrying a heap precondition `P` and a state transformer requiring a proof of `P`) and `fail`.
  - `Data/Coinductive/Spec.lean` (blob `b494834d2aab861331255738ab291c52e767e833`), `ITreeWP/DWP.lean` (blob `0049da5e2933a9d750e3cac477a5e17c6290e473`), and `ITreeWP/DWLP.lean` (blob `b3f96020f77199d80c939aa31189fbb3244a436c` L19, L36) define total weakest precondition `DWP` as the **least fixed point** of `FunctionalWP` (`DWP div = False`) and liberal/partial weakest precondition `DWLP` as the **greatest fixed point** (permitting divergence), while **both** assign `False` to explicit `fail` (`Std/WPDef.lean` blob `c3dbdaffe8008be2065f214a05733454edf3a783`).
  - `Std/WP.lean` (blob `134d8b9f7dfb24e8afdefd730cae547ba540d2ce` at `75fb1479...`; blob `2e4d0f3f4492608bf8618b03263e0eae01777858` L49–67, `ispec_dispec` L69–74 at `92552f50...`) defines `iwp`, total `ispec P m Q`, and partial `dispec P m Q` by universally quantifying over an arbitrary separating frame `R` and requiring the postcondition to preserve `R`, proving `ispec_frame`, `ispec_mono`, `ispec_bind`, and `ispec → dispec`.
- **Modeled `RawPtr` / `Buffer` bridges, spatial tactics, and translator/CI status**:
  - `Std/RawPtr.lean` (blob `33e3dc4b7c06c9b7c46703ec19199d991d023ed1`), `Aeneas/SepLogic.lean` (blob `99f53b5889fde9a05e0056a65edcc063b0176da8`), `Aeneas/Tactic/SepLogic.lean` (blob `acda33446e1affbe56abcea888218c04a78d5e2e`), `Aeneas.lean` (blob `a6e11f94c356814ec1b5e3c1881d4c46cd1acdce`), and `Std.lean` (blob `66c388bdf6960f41b0c92cfd586891be0718f9ae`) provide `MutRawPtr`/`ConstRawPtr` `(AllocId, Nat)` addresses, points-to/slice assertions (`q ↦ v`, `q ↦* vs`), and tactics `iframe`, `iintro`, and `irewrite` integrated with `step`.
  - `tests/lean/SepLogic.lean` (blob `39b8a26c80327cf0ad07b80d358483c9ec3b33e2`), `Fixtures.lean` (blob `2cabc1995755db0114bc55dbfd940ff1ba788c8f`), `Buffer.lean` (blob `8e3ba96449781dd5ea4ddf787731f4940bc9b8c8`, including `mut_to_raw` and `end_mut_to_raw` bridges between functional arrays/slices and raw heap buffers), and `Run.lean` (blob `72b77a126443528dc5bd0b790bf2c259c0e38235`) exercise the Lean model, while `src/interp/InterpPaths.ml` (blob `3197a7b0367f2037611f20456d781b2ebb0739e0`) **still rejects Rust raw-pointer dereference** (the only `src/` change in `PR #1352` at `75fb1479...` is a 2-line edit to `ExtractBuiltinLean.ml`).
  - At `75fb1479040d32d43d31b74510167ee3b873d28a`, `tests/lean/SepLogic/README.md` (blob `b80a670f32e8a4d7e8bba0219013763279b3dbdf`) is stale relative to the tree (referencing absent `StateMachine.lean`, `SepLogic/Semantics.lean`, and `MutableData/` and claiming `SepLogic` is not a default target when `tests/lean/lakefile.lean` blob `57668f29144358eca20b1f58ea239fafd2406dd5` marks `@[default_target] lean_lib SepLogic`), and upstream GitHub check runs on 2026-09-25 failed in both the `lean` and `nix` jobs.

Basis: **source** + upstream CI **execution** metadata + **derived** model/translator distinction.

---

### 4. Published Formal Results, Mechanized LLBC Scope, and End-to-End Trust Decomposition

#### 4.1 Publication Inventory and Exact Theorem Scope

As cataloged in `support/aeneas-published-results-and-mechanized-llbc/publication-results.md`, `support/aeneas-published-results-and-mechanized-llbc/publication-results-inventory.json`, and `support/aeneas-published-results-and-mechanized-llbc/publication-application-inventory.json`:

| Publication | Formal / Empirical Contributions | Explicit Scope & Trust Boundaries |
| --- | --- | --- |
| Ho & Protzenko, *Aeneas: Rust Verification by Functional Translation*, PACMPL / ICFP 2022 (`DOI 10.1145/3547647`, `arXiv:2206.07185v2`) | Value-based ownership semantics for LLBC; functional translation to a pure lambda calculus with forward/backward functions (`choose` §2.3 p. 6); F\* verification of a resizing hash table. | Explicitly calls the Aeneas compiler a **trusted** pure translation (contrasting with Cogent's per-run refinement proofs) and lists mechanical soundness of ownership semantics and translation as future work (§7 p. 38). Excludes unsafe code and interior mutability. |
| Ho, Fromherz & Protzenko, *Sound Borrow-Checking for Rust via Symbolic Semantics*, PACMPL / ICFP 2024 (`DOI 10.1145/3674640`, `arXiv:2404.02680v2`, 37 numbered results + 3 definitions) | Proves 3 core results: (1) LLBC refines a lower-level pointer/address model (`PL`/`HLPL`); (2) symbolic semantics (`LLBC#`) soundly abstract concrete `LLBC+` execution (`Theorem 4.1` p. 18, including join preservation for loops); (3) symbolically borrow-checked programs do not get stuck in `PL` (`Theorem 4.2` p. 22). | `Theorem 4.1` assumes all functions in the environment borrow-check and related initial states, and counts concrete **divergence** and **panic** as admissible non-stuck outcomes. Leaves functional-translation correctness to future work (§1 p. 3). |
| Son Ho, *Formal Verification of Rust Programs by Functional Translation*, PhD thesis, 2024 (`thesis-manuscript.pdf`, 38 numbered results in Ch. 9–12) | Develops the full ownership/symbolic soundness chain (Ch. 9–12), updated pure translation rules (Ch. 13), and backend engineering (Ch. 14). | Thesis `Theorem 5` omits an initial related-state premise in its printed display that the surrounding proof text uses; the introduction and evaluation explicitly classify the translator implementation as trusted. |
| Ho et al., *Charon: An Analysis Framework for Rust* (`arXiv:2410.18042v2`, CAV 2025 tool paper) | Describes `rustc` MIR import, ULLBC/LLBC transformation passes, and multi-tool integration. | Engineering frontend interface, not a mechanized `rustc`-to-LLBC semantics-preservation theorem. |
| Ho et al., *Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean* (`arXiv:2609.15648v1`, Sept 2026) | Industrial Rust-to-Lean verification of SymCrypt routines using Aeneas, custom models, and platform intrinsics. | Retains explicit trust assumptions for extraction and hand-written intrinsic/external models. |
| Klaus, Tolmach & Conejero, *A Rust-to-Lean Verification Pipeline with AI Provers* (`arXiv:2605.30106v1`, `p3-hax-lean-fri-pipeline@4fab6ff0...`) | Downstream verification experience report using Aeneas/Charon or `hax` with AI provers. | Downstream model proof experience; does not prove compiler or frontend soundness. |

*(Note: The 2023 paper "Modularity, Code Specialization, and Zero-Cost Abstractions for Program Verification" by overlapping authors concerns F\*, Low\*, and HACL\*, not Aeneas.)*

Basis: **documentation** (publications) + **source** (`README.md`) + **derived** boundary analysis.

#### 4.2 `AeneasVerif/mechanized-llbc` Grammar and Explicit Proof-Marker Audit (`2762a26a...`)

Direct inspection of all 28 `.v` files and `_RocqProject` in `AeneasVerif/mechanized-llbc@2762a26a3c0792017fa7a731aab1683d9a4cf23a` (and comparison with `1268d802a59ddb0672528f24d873ed4b3b28ca0c`; recorded in `support/aeneas-published-results-and-mechanized-llbc/source-inventory.json` and `support/aeneas-published-results-and-mechanized-llbc/proof-marker-audit.json`) establishes two concrete boundaries between the Rocq mechanization and production Aeneas:

1. **Restricted formal syntax in `src/lang.v`**:
   - Types: `TInt` (natural-number integers, without fixed-width Rust overflow semantics), `TRef` (mutable reference without full shared/mutable, lifetime-binder, or trait-environment distinctions), and `TTuple` (with `type_list`).
   - Expressions and statements: constants (`Nat` and `Bool`), operands (`Const`, `Move`, `Copy`, `Tuple`), binary ops (`BAdd`, `BLe`), rvalues (`Use`, `BinaryOp`, `BorrowMut`), statements (`Nop`, `Assign`, `Seq`, `SwitchBool`, `Loop`, `Panic`, `Break`, `Continue`), and flow tokens (`panic`, ordinary completion, `break`, `continue`).
   - **Omissions**: `src/lang.v` contains **no function call or return statement**, no trait dispatch, no destructors, no frontend JSON decoder, and no pure functional target AST. (`src/PL.v` separately defines a pointer language / `HLPL` importing Chamois memory blocks.)
2. **Explicit proof endings and axioms across `src/` (`support/aeneas-published-results-and-mechanized-llbc/proof-marker-audit.json`)**:

| File (`AeneasVerif/mechanized-llbc@2762a26a...`) | Source Declarations and Proof Endings | Consequence for Assurance Claims |
| --- | --- | --- |
| `src/simulations/Simulation_LLBC_sharp_LLBC_plus.v` | `simulation_LLBC_sharp_LLBC_plus` (forward simulation from `LLBC_sharp.eval_stmt` to `LLBC_plus.eval_stmt` under `leq_branching` and step index) ends in `Qed`. | Completed source proof script for the symbolic-to-hybrid simulation step. |
| `src/simulations/Simulation_LLBC_plus.v` | `stmt_preserves_LLBC_plus_rel` ends in `Qed`. | Completed source proof script at the `LLBC+` hybrid layer. |
| `src/simulations/Simulation_HLPL_plus.v` | `stmt_preserves_HLPL_plus_rel` ends in `Qed`, but the file contains **7 `Admitted` declarations** (including `operand_preserves_HLPL_plus_rel` and `operand_preserves_well_formedness`). | Because `stmt_preserves_HLPL_plus_rel` invokes operand lemmas in this module, a `Qed` ending on the top-level theorem does **not** make its transitive dependency closure axiom-free. |
| `src/PL.v` | Contains **2 `Admitted` declarations** (`offset_less_modulus`, `WellTypedState_equiv`), **`Axiom blockof_inj`**, and **11 `Abort` endings** (with 4 internal `admit` tactics inside aborted proof attempts, plus `Assign_Preserves_PL_HLPL_Rel`). | The 9 total `Admitted` lemmas (`7 + 2`) and `Axiom blockof_inj` enter the logical environment as unproven assumptions, whereas the 11 `Abort` blocks do not register theorems. |

Basis: **source** (`AeneasVerif/mechanized-llbc`) + **derived** dependency analysis.

#### 4.3 Eight-Stage End-to-End Specification-Transfer Chain

Combining the Charon/Aeneas pipeline audit with the formal literature yields the exact 8-boundary correspondence chain required for any source-level Rust verification claim:

| Stage Boundary | Required Semantic Relation / Evidence | Status in Current Toolchain & Literature |
| --- | --- | --- |
| 1. Build subject -> `rustc` MIR | Exact crate/feature/target identity and source-to-MIR semantics preservation | Assumed (`rustc` trusted). |
| 2. `rustc` MIR -> imported ULLBC -> normalized LLBC | Preservation of evaluation, failure/unwind, and UB across `charon/src/transform/mod.rs` passes (`has_errors = false` in `export.rs`) | Unverified engineering passes (CAV 2025 tool paper). |
| 3. Concrete pointer memory (`PL`) -> ownership `LLBC` | Value/resource representation, aliasing, and non-stuckness | Modeled for the restricted `src/lang.v` / `PL.v` fragment in ICFP 2024 (`Theorem 4.2`), with 9 `Admitted` declarations and `Axiom blockof_inj` in `mechanized-llbc@2762a26a...`. |
| 4. Concrete `LLBC+` -> symbolic `LLBC#` (with joins/loops) | Sound concretization, branch/loop join preservation, and signature hypotheses | Modeled in ICFP 2024 (`Theorem 4.1`, permitting panic/divergence) and `simulation_LLBC_sharp_LLBC_plus` (`Qed`). Production OCaml `Interp*` conformance is unverified. |
| 5. Symbolic execution -> pure functional AST | Adequacy of forward values and backward continuation reconstruction (`SymbolicToPure*`) and pure micro-passes | Formalized on paper in ICFP 2022 / 2024 thesis (Ch. 13), but explicitly **trusted** (unproved). Representative specimen certified in `UpdateCertificate.lean` (§5 below). |
| 6. Pure AST -> emitted & elaborated Lean definitions | Denotational preservation of printing (`Extract*`) and absence of diagnostic admissions (`ExtractErrors.ml`) | Checked per-specimen via hash capture and Lean `#print axioms`. |
| 7. External/library operations -> handwritten Lean models | Refinement between Rust std/core/intrinsic implementations and `Aeneas.Std` / registered `SpecInfo` models | Assumed per external model unless independently proved. |
| 8. Lean model theorem -> source Rust specification | Alignment of quantifiers (total vs. partial, panic exclusion, frame preservation, and checker soundness) | Requires explicit transfer theorem; note that ICFP 2024 `Theorem 4.1`/`4.2` permit panic and divergence, whereas `WP.spec` and `DWP`/`ispec` forbid `fail` and `div`. |

Basis: **derived** synthesis across **source** and **documentation**.

---

### 5. End-to-End Returned-Borrow Update Certification on Legacy Alpha24 (`choose` and `update_second`)

In `aeneas-pair-returned-update-alpha24` (`support/aeneas-pair-returned-update-alpha24/coverage.json`, `support/aeneas-pair-returned-update-alpha24/artifact-index.json`, `support/aeneas-pair-returned-update-alpha24/execution-results.json`, `support/aeneas-pair-returned-update-alpha24/fresh-scratch-results.json`), an actual end-to-end returned-borrow update from legacy Anneal `alpha24` was captured, executed, and kernel-certified in Lean `4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`):

1. **Specimen capture and binary recovery (`probe.rs`, `CapturedTypes.lean`, `CapturedFuns.lean`)**:
   - The standalone Rust source `support/aeneas-pair-returned-update-alpha24/probe.rs` (SHA-256 `cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0`) defines `choose` and function ID `1`:
     ```rust
     pub fn update_second(p: &mut (u8, u8), x: u8) { p.1 = x; }
     ```
   - After recovering the missing task-local `libgmp.10.dylib` loader dependency by linking the bundled static GMP archive with `clang -dynamiclib -Wl,-all_load` (leaving the `alpha24` `aeneas` binary `244397c4...` and `charon` `0.1.210` `51bb6d23...` unmodified; recorded in `support/aeneas-pair-returned-update-alpha24/tool-identities.json` and `support/aeneas-pair-returned-update-alpha24/aeneas-run.stdout`), Aeneas exited `0` and emitted `Types.lean` and `Funs.lean` (`support/aeneas-pair-returned-update-alpha24/CapturedTypes.lean`, `support/aeneas-pair-returned-update-alpha24/CapturedFuns.lean`, `support/aeneas-pair-returned-update-alpha24/capture-identities.json`):
     ```lean
     choose b x y = Result.ok (if b then x else y)
     update_second p x = Result.ok (p.1, x)
     ```
   - In `CapturedFuns.lean` (`support/aeneas-pair-returned-update-alpha24/CapturedFuns.stdout`, `CapturedFuns.stderr`), `choose_emitted` and `update_emitted` prove these equations for all Booleans and `Aeneas.Std.U8` (`UScalar .U8` wrapping `BitVec 8`) pairs with **empty `#print axioms` output**.
2. **Exact ULLBC/LLBC operation sequence and admission gate (`check_capture.py`)**:
   - In `support/aeneas-pair-returned-update-alpha24/selected-update.llbc.json` and `support/aeneas-pair-returned-update-alpha24/selected-update.ullbc.json`, the final selected LLBC body for `update_second` executes 7 steps in exact order:
     1. Initialize return place `_0` to `()`;
     2. `StorageLive(_3)`;
     3. Copy byte argument `_2` (`x`) into temporary `_3`;
     4. Assign by moving `_3` through dereferenced reference local `*_1` into tuple field `.1` (arity 2);
     5. `StorageDead(_3)`;
     6. Initialize `_0` to `()` (expressed as a constant unit in raw serialized ULLBC and an empty aggregate in LLBC; note that Charon's earlier Aeneas-preset ULLBC debug print omits the entry unit initialization);
     7. `Return`.
   - `support/aeneas-pair-returned-update-alpha24/check_capture.py` (`support/aeneas-pair-returned-update-alpha24/capture-check.stdout`, `capture-check.stderr`) verifies whole-file SHA-256 digests, region/local inventories, projection paths, unit representations, operand modes, and the complete 7-step operation sequence, failing closed on any modified field or unmodeled operation.
3. **Lean frame and correspondence certificate (`UpdateCertificate.lean`) and negative controls**:
   - `support/aeneas-pair-returned-update-alpha24/UpdateCertificate.lean` (`UpdateCertificate.stdout`, `UpdateCertificate.stderr`) models a pair-cell heap `Nat → Option (U8 × U8)` and an execution state tracking `root`, `input`, `canWriteRoot`, return initialization, temporary `_3` liveness/value, and ordered event trace.
   - `returned_update_correspondence` proves (with `#print axioms` restricted to `[propext, Quot.sound]`, and `[propext]` for `sourcePlaceUpdate` heap equality) that for **every** entry state with `heap root = some p` and `canWriteRoot = true` (and arbitrary initial temporary/return flags, prior events, and outside heap cells):
     - `actualLLBCUpdate` succeeds and produces `expectedState`;
     - `update_second p input = Result.ok (p.1, input)`;
     - the updated heap at `root` holds `(p.1, input)` and every outside cell `j ≠ root` is unchanged (`heap' j = heap j`);
     - temporary `_3` is dead and cleared, `_0` is initialized, and the 7 storage/move/update/unit/return events are recorded in order (while `canWriteRoot = false` or `heap root = none` evaluates to `none`).
   - Negative controls (`support/aeneas-pair-returned-update-alpha24/proof-controls.json`): `support/aeneas-pair-returned-update-alpha24/ConcreteCounterexamples.lean` (`ConcreteCounterexamples.stdout`, `ConcreteCounterexamples.stderr`) proves kernel-checked byte counterexamples against swapped branches/fields, and `support/aeneas-pair-returned-update-alpha24/WrongChoose.lean` (`WrongChoose.stdout`, `WrongChoose.stderr`) and `support/aeneas-pair-returned-update-alpha24/WrongUpdate.lean` (`WrongUpdate.stdout`, `WrongUpdate.stderr`) exit `1` as expected when attempting to elaborate false universal correspondence claims.
4. **Exhaustive native `rustc` control (`native_control.rs`)**:
   - `support/aeneas-pair-returned-update-alpha24/native_control.rs` (`native-compile.stdout`, `native-compile.stderr`, `native-run.stdout`, `native-run.stderr`), compiled with bundled `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) using `black_box` inputs, exhaustively executes all `2 × 256 × 256 = 131,072` `choose` cases and all `256³ = 16,777,216` `update_second` cases (verifying first-field preservation and an adjacent frame cell), outputting `choose_cases=131072 update_cases=16777216 digest=551903232000`.

Basis: **source** + **execution** + **derived** correspondence theorem.

---

## Boundaries

- **Not examined**:
  - No fresh execution of Rocq (`mechanized-llbc`), current `main` Aeneas, or draft `PR #1352` was performed; only the `alpha24` returned-pair specimen (`aeneas-pair-returned-update-alpha24`) includes fresh tool, Lean, and native `rustc` executions.
  - Unsafe representation operations, safe wrappers over unsafe code, raw-pointer casting/aliasing/lifetime-extension counterexamples, FFI, inline assembly, unwinding, and concurrency were not executed or verified.
  - Partial-move handling through place-access helpers in `InterpPaths.ml` and non-Lean backends (F\*, Coq/Rocq, HOL4 extraction) were not audited in full.
- **Unknown**:
  - The complete admissible subset of nested borrows across all symbolic expansion, join, and pure-translation paths at `21345f80fa212c596f6437378d7d57984fa2ea77`.
  - The exact transitive `Print Assumptions` closure of each compiled theorem in `AeneasVerif/mechanized-llbc@2762a26a3c0792017fa7a731aab1683d9a4cf23a` and whether that full tree builds cleanly without modification.
  - Any mechanized refinement proof connecting production OCaml `Interp*` / `SymbolicToPure*` transitions to the ICFP 2022 / 2024 paper calculi.
- **Known not to apply**:
  - Presence of nested-borrow or sub-abstraction data types in `Values.ml` does **not** establish general support: `destructure_abs` (`src/interp/InterpBorrows.ml` L1935–2132) and `InterpMatchCtxs` reject several nested-borrow shapes, and `ended_abs_cont_to_texpr_aux` (`src/symbolic/SymbolicToPureAbs.ml` L1250–1290) asserts `abs_level = 0` with `"Unimplemented"`.
  - `Pure.ml` `mplace` metadata is variable-naming origin metadata, **not** Rust pointer provenance.
  - Passing optional runtime sanity checks (`Invariants.check_invariants`, disabled by default in `Config.ml`), borrow-check-only mode (`Config.ml` L49–58), or target type-checking does **not** certify functional translation correctness.
  - The ICFP 2024 non-stuckness theorems (`Theorem 4.1`, `Theorem 4.2`) permit **panic** and **divergence**, so they do **not** by themselves discharge specifications requiring panic-freedom or termination.
  - Even on `PR #1352`, the typed slot-granular heap (`Std/Heap.lean`) does **not** model byte-level layout, uninitialized padding, type punning, pointer-integer casts, or concurrency, and `UpdateCertificate.lean`'s logical pair heap (`Nat → Option (U8 × U8)`) and `canWriteRoot` flag do **not** prove `rustc` frontend import adequacy or byte-level aliasing freedom.
  - **Lean kernel nested-inductive validation caveat**: Both legacy Lean `4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and Lean `4.31` precede commit `leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808` (documented in the Lean `4.32.2` release notes as fixing a nested-inductive parameter validation bug in `src/kernel/inductive.cpp` that permitted false theorem acceptance). While this does not invalidate the simple non-inductive terms in `UpdateCertificate.lean`, clean `#print axioms` output on unpatched kernels is conditional on trusted producer discipline.
- **Unsupported**:
  - Dereferencing raw pointers (`Deref` of `TRawPtr` in `src/interp/InterpPaths.ml` L111–112) is rejected across **all** inspected Aeneas revisions (`ac9f1bc5262a...`, `b86120db...`, `ca282ec2...`, `21345f80...`, and `PR #1352` heads `75fb1479...` and `92552f50...`).
  - Projecting an unpromoted reserved mutable borrow directly in `InterpProjectors.apply_proj_borrows`, ending a frozen abstraction (`can_end = false` in `Contexts.abs_is_endable`), and translating non-zero sub-abstraction levels (`abs_level > 0`) in `SymbolicToPureAbs.ended_abs_cont_to_texpr_aux`.

---

## Evidence

### 1. Aeneas Symbolic Ownership and Functional Resource Boundary Sources

- **`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`** (`support/aeneas-symbolic-ownership-continuations-21345f80/source-reading.json`):
  - `src/llbc/Values.ml` (L86–213, L544–610, L1111–1188, L1241–1443, L1464–1576), `src/llbc/Contexts.ml` (`abs_is_endable` L811–840), `src/llbc/RegionsHierarchy.ml` (`compute_regions_hierarchy_for_sig` L60–127, L295–356).
  - `src/interp/InterpProjectors.ml` (`apply_proj_borrows` L102–253), `src/interp/InterpExpansion.ml` (L48–217, L494–742), `src/interp/InterpBorrows.mli` (`promote_reserved_mut_borrow` L89–99), `src/interp/InterpBorrows.ml` (L15–120, L940–1018, L1175–1288, L1357–1455, L1553–1571, `destructure_abs` L1935–2132).
  - `src/interp/InterpStatements.ml` (`eval_function_call_symbolic_from_inst_sig` L1346–1535), `src/interp/Interp.ml` (`evaluate_function_symbolic_synthesize_backward_from_return` L387–506), `src/interp/Invariants.ml` (L310–381, L901–988, L1002–1011), `src/symbolic/SymbolicToPureAbs.ml` (L1050–1109, L1250–1290), `README.md`.
- **`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)**:
  - `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), `src/interp/InterpPaths.ml` (blob `ec23375a5ca0680500daea0248d2372c9901156e`), `src/interp/InterpBorrows.ml` (blob `f3dcde1455af1402a1099ae1d9651c4ba8aea46e`), `src/interp/InterpBorrowsCore.ml` (blob `9232a193ed20fbeb989624187663f2ef464a3406`).
  - `README.md` (blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`), `documentation/aeneas-overview.md` (blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`), `tests/src/raw_pointers.rs` (blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`), `tests/src/raw_pointers.lean.out` (blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`).
- **`AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e` & `AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`**:
  - Aeneas: `src/interp/InterpPaths.ml` (blob `3197a7b0367f2037611f20456d781b2ebb0739e0`, L111–112), `backends/lean/Aeneas/Std/RawPtr.lean` (blob `79de0729e3f3f755e10852c33de2d5f4e60f6124`), `src/Translate.ml` (blob `2b9c4b5f8db404d2250b0ba2fe7e9b3ea1914c46`), `src/Config.ml` (blob `6ac7f87ac268041a0c92cdcf47b3540c919a8da5`), `src/extract/ExtractErrors.ml` (blob `9169ab076be376ee6150ef7f04b298b92a840965`).
  - Charon: `charon/src/transform/mod.rs` (blob `6fc5af78e919be7c23f882d0a250a9735326117f`, L97–100), `charon/src/export.rs` (blob `825319eeb8317127c61de7da83aaaeda05364518`).

### 2. Separation-Logic Sources (`b86120db...`, `75fb1479...`, `92552f50...`)

- **Aeneas `main` (`b86120db3183b0107eb5f2637b11c424cd06ef1c`)**:
  - `README.md` (blob `7326e8ea5223171dec810a0cb669b8683c48eddc`), `backends/lean/Aeneas/Data/Coinductive/Effect.lean` (blob `0015e858c1ebd2a923435be811082fa655bf531f`), `backends/lean/Aeneas/Data/Coinductive/ITree.lean` (blob `0674c6ffafa146f91f7f1b8ced10428d2f148a25`), `backends/lean/Aeneas/Std/Spec.lean` (blob `84f7f99e38b530629bbd2cd0e0fa486d57918211`), `backends/lean/Aeneas/Tactic/Step/Tests/Triple.lean` (blob `af674153793bf4a15c79499e419230c978c94786`), `backends/lean/Aeneas.lean` (blob `45ba4ca89d0e056a52e6b7920d390718b5d253b4`), `backends/lean/Aeneas/Std.lean` (blob `19e5d842450d4ed2df711a83b3b3c5a863f1f2a8`), `src/interp/InterpPaths.ml` (blob `3197a7b0367f2037611f20456d781b2ebb0739e0`).
- **Draft `PR #1352` head `75fb1479040d32d43d31b74510167ee3b873d28a`**:
  - `backends/lean/Aeneas/SepLogic/Basic.lean` (blob `5b50eb4a1532251386955d754bb5d711600d384b`), `backends/lean/Aeneas/Std/Heap.lean` (blob `d635192c03e4b49ab57f6581e4f93a2a17ed265c`), `backends/lean/Aeneas/Std/Primitives.lean` (blob `915ff412447fd47ccbb3f4bbf34d84628e13a77e`), `backends/lean/Aeneas/Data/Coinductive/Spec.lean` (blob `b494834d2aab861331255738ab291c52e767e833`), `backends/lean/Aeneas/Std/WP.lean` (blob `134d8b9f7dfb24e8afdefd730cae547ba540d2ce`), `backends/lean/Aeneas/Std/RawPtr.lean` (blob `33e3dc4b7c06c9b7c46703ec19199d991d023ed1`), `backends/lean/Aeneas/SepLogic.lean` (blob `99f53b5889fde9a05e0056a65edcc063b0176da8`), `backends/lean/Aeneas/Tactic/SepLogic.lean` (blob `acda33446e1affbe56abcea888218c04a78d5e2e`), `backends/lean/Aeneas.lean` (blob `a6e11f94c356814ec1b5e3c1881d4c46cd1acdce`), `backends/lean/Aeneas/Std.lean` (blob `66c388bdf6960f41b0c92cfd586891be0718f9ae`).
  - `tests/lean/SepLogic.lean` (blob `39b8a26c80327cf0ad07b80d358483c9ec3b33e2`), `tests/lean/SepLogic/Fixtures.lean` (blob `2cabc1995755db0114bc55dbfd940ff1ba788c8f`), `tests/lean/SepLogic/Buffer.lean` (blob `8e3ba96449781dd5ea4ddf787731f4940bc9b8c8`), `tests/lean/SepLogic/Run.lean` (blob `72b77a126443528dc5bd0b790bf2c259c0e38235`), `tests/lean/SepLogic/README.md` (blob `b80a670f32e8a4d7e8bba0219013763279b3dbdf`), `tests/lean/lakefile.lean` (blob `57668f29144358eca20b1f58ea239fafd2406dd5`).
- **Draft `PR #1352` head `92552f503cd19ca023ae9897cf521db49ee8d887`**:
  - `backends/lean/Aeneas/Std/Heap.lean` (blob `9ddd88e92d101232654988167443ac147de1bf3f`), `backends/lean/Aeneas/SepLogic/IProp.lean` (blob `3e6957f5f1dcbd0eeeaf6e04275ea6536442ea1f`), `backends/lean/Aeneas/Std/WPDef.lean` (blob `c3dbdaffe8008be2065f214a05733454edf3a783`), `backends/lean/Aeneas/Std/WP.lean` (blob `2e4d0f3f4492608bf8618b03263e0eae01777858`), `backends/lean/Aeneas/Data/Coinductive/ITreeWP/DWP.lean` (blob `0049da5e2933a9d750e3cac477a5e17c6290e473`), `backends/lean/Aeneas/Data/Coinductive/ITreeWP/DWLP.lean` (blob `b3f96020f77199d80c939aa31189fbb3244a436c`).

### 3. Publications and `AeneasVerif/mechanized-llbc` Sources and Support Inventories

- **`AeneasVerif/mechanized-llbc@1268d802a59ddb0672528f24d873ed4b3b28ca0c`**:
  - `README.md` (blob `997fe7d2f11f12a903c986780db488ddb90fa459`), `src/simulations/Simulation_LLBC_plus.v` (blob `2239c02de5f64f051f377fb3a87c1e6e3f855f8c`), `src/simulations/Simulation_HLPL_plus.v` (blob `d5e987271903ebd7030089bcb7ed373e071f4087`), `src/simulations/Simulation_LLBC_sharp_LLBC_plus.v` (blob `5da80dd4db01dfd7dc17b344aaad47744b69d3ee`).
- **`AeneasVerif/mechanized-llbc@2762a26a3c0792017fa7a731aab1683d9a4cf23a`** (`support/aeneas-published-results-and-mechanized-llbc/source-inventory.json`, `support/aeneas-published-results-and-mechanized-llbc/proof-marker-audit.json`):
  - `src/lang.v`, `src/PL.v`, `_RocqProject`, `src/simulations/SimulationUtils.v`, `src/simulations/Simulation_HLPL_plus.v`, `src/simulations/Simulation_LLBC_plus.v`, `src/simulations/Simulation_LLBC_sharp_LLBC_plus.v`.
- **Publication Inventories (`support/aeneas-published-results-and-mechanized-llbc/`)**:
  - `support/aeneas-published-results-and-mechanized-llbc/publication-results.md`
  - `support/aeneas-published-results-and-mechanized-llbc/publication-results-inventory.json`
  - `support/aeneas-published-results-and-mechanized-llbc/publication-application-inventory.json`
  - `support/aeneas-published-results-and-mechanized-llbc/publication-source-identities.json`

### 4. Legacy `alpha24` Returned-Pair Update Certificate Artifacts (`support/aeneas-pair-returned-update-alpha24/`)

- **Rust Specimen, Native Control, and Tool/Capture Metadata**:
  - `support/aeneas-pair-returned-update-alpha24/probe.rs` (SHA-256 `cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0`)
  - `support/aeneas-pair-returned-update-alpha24/selected-update.ullbc.json` and `support/aeneas-pair-returned-update-alpha24/selected-update.llbc.json`
  - `support/aeneas-pair-returned-update-alpha24/aeneas-run.stdout`, `support/aeneas-pair-returned-update-alpha24/tool-identities.json`, `support/aeneas-pair-returned-update-alpha24/capture-identities.json`, `support/aeneas-pair-returned-update-alpha24/artifact-index.json`, `support/aeneas-pair-returned-update-alpha24/coverage.json`
  - `support/aeneas-pair-returned-update-alpha24/check_capture.py` (`support/aeneas-pair-returned-update-alpha24/capture-check.stdout`, `support/aeneas-pair-returned-update-alpha24/capture-check.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/native_control.rs` (`support/aeneas-pair-returned-update-alpha24/native-compile.stdout`, `support/aeneas-pair-returned-update-alpha24/native-compile.stderr`, `support/aeneas-pair-returned-update-alpha24/native-run.stdout`, `support/aeneas-pair-returned-update-alpha24/native-run.stderr`)
- **Lean Proofs, Counterexamples, and Revalidation Scripts**:
  - `support/aeneas-pair-returned-update-alpha24/CapturedTypes.lean` (`support/aeneas-pair-returned-update-alpha24/CapturedTypes.stdout`, `support/aeneas-pair-returned-update-alpha24/CapturedTypes.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/CapturedFuns.lean` (`support/aeneas-pair-returned-update-alpha24/CapturedFuns.stdout`, `support/aeneas-pair-returned-update-alpha24/CapturedFuns.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/UpdateCertificate.lean` (`support/aeneas-pair-returned-update-alpha24/UpdateCertificate.stdout`, `support/aeneas-pair-returned-update-alpha24/UpdateCertificate.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/ConcreteCounterexamples.lean` (`support/aeneas-pair-returned-update-alpha24/ConcreteCounterexamples.stdout`, `support/aeneas-pair-returned-update-alpha24/ConcreteCounterexamples.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/WrongChoose.lean` (`support/aeneas-pair-returned-update-alpha24/WrongChoose.stdout`, `support/aeneas-pair-returned-update-alpha24/WrongChoose.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/WrongUpdate.lean` (`support/aeneas-pair-returned-update-alpha24/WrongUpdate.stdout`, `support/aeneas-pair-returned-update-alpha24/WrongUpdate.stderr`)
  - `support/aeneas-pair-returned-update-alpha24/proof-controls.json`, `support/aeneas-pair-returned-update-alpha24/execution-results.json`, `support/aeneas-pair-returned-update-alpha24/fresh-scratch-results.json`, and `support/aeneas-pair-returned-update-alpha24/revalidate.py`.

---

## Revalidation

To revalidate this report when Anneal updates its Aeneas, Charon, Lean, or `mechanized-llbc` pins:

1. **Symbolic ownership and backward continuation synthesis (`src/llbc/`, `src/interp/`, `src/symbolic/`)**:
   - Diff `Values.ml` (`tvalue`, `tavalue`, `tevalue`, `equal_mvalue`, `menv`), `InterpProjectors.apply_proj_borrows`, `InterpExpansion.expand_symbolic_value_borrow`, `InterpBorrows.end_borrow_aux` / `end_abs_aux`, `Contexts.abs_is_endable`, and `Interp.evaluate_function_symbolic_synthesize_backward_from_return` (`region_can_end`).
   - Check whether `ended_abs_cont_to_texpr_aux` (`SymbolicToPureAbs.ml`) still asserts `abs_level = 0` and whether `destructure_abs` (`InterpBorrows.ml`) still rejects nested borrows.
2. **Resource boundaries and Lean separation-logic status (`src/interp/InterpPaths.ml`, `backends/lean/Aeneas/`)**:
   - Inspect `anneal/flake.nix` to resolve the active Aeneas commit.
   - Check `src/interp/InterpPaths.ml` to see whether `Deref` of `TRawPtr` is still rejected or translated to a heap effect.
   - Check `backends/lean/Aeneas.lean`, `Aeneas/SepLogic/`, `Std/Heap.lean`, `Std/WPDef.lean`, `Std/WP.lean`, and `Std/RawPtr.lean` to determine whether `PR #1352` (or a successor) has merged into `main`, whether the heap remains typed-slot `(AllocId, Nat)` vs. byte-addressed, and whether `lean` / `nix` CI checks pass.
3. **Mechanized LLBC and formal correspondence (`AeneasVerif/mechanized-llbc`)**:
   - Inspect `src/lang.v` for function-call/return additions, audit `src/**/*.v` for remaining `Admitted`, `Abort`, and `Axiom` declarations (`support/aeneas-published-results-and-mechanized-llbc/proof-marker-audit.json`), and run `Print Assumptions` on `simulation_LLBC_sharp_LLBC_plus`, `stmt_preserves_LLBC_plus_rel`, and `stmt_preserves_HLPL_plus_rel`.
4. **Executable returned-pair update certificate (`support/aeneas-pair-returned-update-alpha24/revalidate.py`)**:
   - Run `python3 -B support/aeneas-pair-returned-update-alpha24/revalidate.py --legacy-runtime <path-to-alpha24-runtime> --out <scratch-output-dir>` to re-verify `check_capture.py`, recompile `CapturedTypes.lean`, `CapturedFuns.lean`, `UpdateCertificate.lean`, and `ConcreteCounterexamples.lean`, verify that `WrongChoose.lean` and `WrongUpdate.lean` fail elaboration as expected, and re-run the exhaustive `16,777,216`-case native `rustc` harness.
