# Place evaluation, `PlaceMention` erasure, in-bounds projections, equal-target switch erasure and storage-marker erasure in a toy MIR-like language (Lean 4)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Model–system relation: none proved. These are statements about the toy model (namespace `Toy.PlaceEval`); they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference. Real systems enter as separate `derived (modeling bridge)` remarks that cite their documented behaviour; no tool was run.

Every result below is kernel-checked in Lean 4 (`leanprover/lean4:v4.34.1`, no Mathlib) with the standard axioms `propext`, `Classical.choice` and `Quot.sound` at most. Each bullet is the card's plain-language claim, verbatim.

* **`place-evaluation-ub-exact-conditions`** (characterization, T1): In the toy, for every state `st` (reachable or not) and place `p`, evaluating `p` is UB (`evalPlace st p = none`) iff (a) `st.basePtr p.base = none` (the frame records no allocation for the base local, or records an allocation index missing from the table; a frame entry naming a freed allocation still yields a pointer, `basePtr_freed_in_frame_eq_some`), or, for some projection index `i` such that the first `i` projections evaluate to a pointer `q` (`evalPrefix`), projection `i` is (b) a `deref` whose pointer load at `q` fails (`¬ DerefLoadOk`: `q` is not dereferenceable for `ptrSize` bytes, is not aligned for `ptrAlign`, or its cells do not hold a pointer value), (c) a `field off` with `off ≠ 0` whose byte range is not in bounds of a live allocation that `q` is derived from (`Mem.inBounds`), (d) an `index j sz` whose read of the index local `j` fails (`State.readIndex`), or (e) an `index j sz` whose index value `n` gives a non-zero offset `n * sz` (unbounded natural-number product) that is not in bounds. Degenerate edges: a zero offset (`off = 0`, or `n = 0` or `sz = 0`) is never checked, even for a null or dangling `q` (`evalPlace_ex_pos_index_zero_size`). No disjunct constrains the pointer that evaluation finally produces.
* **`place-evaluation-ignores-final-pointee`** (theorem, T1): In the toy, for every state `st`, local `x`, projection list `pre` and `k`, the place `pre ++ [deref] ++ k × [field 0]` evaluates to exactly the pointer loaded by its final `deref` (`evalPlace_deref_zeroFields`); hence `pre ++ [deref]` evaluates iff `pre` evaluates to some `q` with `DerefLoadOk` at `q` (`evalPlace_append_deref_isSome_iff`), whatever the loaded pointer is: null, dangling, pointing into a freed allocation, misaligned, or pointing to uninitialized cells.
* **`place-computation-not-free`** (counterexample, T0): Under the deterministic example semantics `SEx`: `placeMention (*(*pp))` with `*pp` uninitialized is UB (`pDerefUninit`: the intermediate pointer load fails); `r := &raw (*p).field 2` with `p` pointing into a freed allocation is UB (`pDanglingRaw 2`); and `r := &raw (*p).field 2` with `p` null is UB (`pNull 2`). Positive control (`place_computation_zero_offset_and_bare_deref_ok`): `r := &raw (*p).field 0` and `placeMention ((*p).field 0)` with `p` pointing into a freed allocation, `placeMention (*p)` and `r := &raw (*p).field 0` with `p` null, and the same two statements with `p` misaligned (with provenance), are UB-free.
* **`place-mention-erasure-refines`** (theorem, T1): In the toy, under every semantics `S` (fresh addresses, or any static slot assignment), for every program `P`, block `l` and index `i`: if statement `i` of block `l` is `placeMention p`, then deleting it gives a prefix-preserving refinement of `P` (every behaviour of the edited program equals a behaviour of `P` or extends the trace of a UB behaviour of `P`).
* **`place-mention-erasure-equivalence-sufficient-condition`** (theorem, T1): In the toy, under every semantics `S`, for every program `P`: if statement `i` of block `l` is `placeMention p` and evaluating `p` succeeds in every state in which `(l, i)` is reachable, then deleting the statement is a prefix-preserving equivalence (refinement in both directions).
* **`place-mention-erasure-equivalence-exact-condition-static-slots`** (characterization, T1): In the toy, under the deterministic semantics `slots s` for every slot assignment `s`, for every program `P`: if statement `i` of block `l` is `placeMention p`, then deleting it is a prefix-preserving equivalence iff, for every reachable state at `(l, i)` in which evaluating `p` is UB, the run of the edited program from the point after the deleted statement reaches UB before emitting any event.
* **`place-mention-erasure-equivalence-despite-reachable-failure`** (counterexample, T0): Under `SEx`, in `pTwoMentions` (two identical statements `placeMention (*(*pp))` with `*pp` uninitialized) evaluation of the first fails at a reachable state, yet deleting it is a prefix-preserving equivalence: both programs reach UB before any event (`pTwoMentions_beh`, `pTwoMentions_erased_beh`), the edited one at the second statement. So place-evaluation UB-freedom at the erased point is sufficient for equivalence but not necessary.
* **`ub-check-after-erasure-incomplete`** (counterexample, T0): Under `SEx`, `pDerefUninit` with its `placeMention` (statement `(0, 2)`) deleted is UB-free while `pDerefUninit` is not, so every exact UB checker for `SEx` (a Boolean function `chk` with `chk P = true ↔ UBFree SEx P`; such checkers exist noncomputably, `exactUBChecker_exists`) accepts the edited program (`ubCheck_after_erasePlaceMention_misses_place_ub`). Under fresh addresses, every exact UB checker for `.fresh` accepts `pStale` with the markers of local `0` erased, although `pStale` (a read of `x` after a re-`storageLive`) is not UB-free (`ubCheck_after_eraseMarkers_misses_stale_read`).
* **`ub-check-after-place-mention-erasure-complete-outside-place-ub`** (theorem, T0): In the toy, under every semantics `S`, for every program `P`: if statement `i` of block `l` is `placeMention p`, evaluating `p` succeeds at every reachable state at `(l, i)`, and the program with that statement deleted is UB-free, then `P` is UB-free. Equivalently, if the edited program is UB-free and `P` is not, some reachable state at `(l, i)` has a failing evaluation of `p`.
* **`switch-operand-ub-conditions`** (characterization, T0): In the toy, for every state `st`, place `p` and type `τ`, the operand `copy p τ` fails to evaluate to an integer iff evaluating `p` fails (`evalPlace_eq_none_iff`), or the resulting pointer `q` is not dereferenceable for `τ.size` bytes, or is not aligned for `τ.align`, or its cells do not decode to an integer at `τ`. At an enum type the cells decode to `n` iff they are bytes encoding `n` and `n` is a valid tag (`decode_enum_eq_some_iff`); at an integer type, iff they are bytes encoding `n` (`decode_int_eq_some_iff`), each byte contributing `b % 256` (Nat remainder); an uninitialized cell or a pointer fragment never decodes via `decodeLE`. Degenerate edges: if `τ.size = 0`, then every pointer, including null, is dereferenceable for `τ.size` bytes (`dereferenceable_of_size_eq_zero`), the cells read form the empty list (`readCells_of_size_eq_zero`), and they decode at `τ` to the integer `n` iff `n = 0` and, when `τ` is an enum type `Ty.enum s a valid`, `0 ∈ valid` (`decode_readCells_of_size_eq_zero_iff`); instances in `mEx`: a zero-size read through null succeeds with `0` at `Ty.int 0 1` (`load_ex_pos_zero_size_null`) and at `Ty.enum 0 1 [0]` (`load_ex_pos_zero_size_enum`), and fails at `Ty.enum 0 1 [1]`, whose valid tags exclude `0` (`load_ex_neg_zero_size_enum`); for `τ.align = 0` exactly address `0` is aligned (`aligned_zero_ex_pos`, `aligned_zero_ex_neg`).
* **`equal-target-switch-erasure-refines`** (theorem, T1): In the toy, under every semantics `S`, for every program `P`: if block `l` ends in `switchInt o arms b` and every arm targets `b`, then replacing that terminator by `goto b` gives a prefix-preserving refinement of `P`.
* **`equal-target-switch-erasure-equivalence-sufficient-condition`** (theorem, T1): In the toy, under every semantics `S`, for every program `P`: if block `l` ends in `switchInt o arms b`, every arm targets `b`, and `o` evaluates to an integer in every reachable state at the switch (for `o = copy p τ`: place evaluation succeeds and the read is a valid integer, or a valid tag for an enum type, `switch-operand-ub-conditions`), then replacing the switch by `goto b` is a prefix-preserving equivalence.
* **`equal-target-switch-erasure-equivalence-exact-condition-static-slots`** (characterization, T1): In the toy, under the deterministic semantics `slots s` for every slot assignment `s`, for every program `P`: if block `l` ends in `switchInt o arms b` and every arm targets `b`, then replacing the switch by `goto b` is a prefix-preserving equivalence iff, for every reachable state at the switch in which `o` does not evaluate to an integer, the run of the edited program from the entry of `b` reaches UB before emitting any event.
* **`raw-and-shared-reference-ub-conditions`** (characterization, T0): In the toy, for every state `st`, place `p` and layout `L`: `&raw p` fails to evaluate iff evaluating `p` fails (`rawRef_eval_eq_none_iff`); `&p` with pointee layout `L` fails iff evaluating `p` fails or the resulting pointer `q` violates `RefOk` (`q` has address `0`, i.e. `q.addr = 0` regardless of provenance, or is not aligned for `L.align`, or is not dereferenceable for `L.size` bytes) (`ref_eval_eq_none_iff`).
* **`reference-to-raw-rewrite-refines`** (theorem, T0): In the toy, under every semantics `S`, for every program `P`: if statement `i` of block `l` is `dst := &p` at type `τ` with pointee layout `L`, then replacing it by `dst := &raw p` gives a prefix-preserving refinement of `P`.
* **`raw-and-shared-reference-rewrites-not-equivalences`** (counterexample, T0): Under `SEx`: rewriting `r := &raw (*p)` to `r := &(*p)` (pointee layout `⟨4, 2⟩`) for `p` pointing into a freed allocation (`pRawDangling`), and rewriting `r := &raw (s.b)` to `r := &(s.b)` for the 2-aligned field at offset 1 of a packed 3-byte local (`pRawPacked`), are not refinements (each introduces UB: `pRawDangling_beh`, `pRefDangling_beh`, `pRawPacked_beh`, `pRawPacked_ref_beh`); rewriting `r := &(*p)` to `r := &raw (*p)` in `pRefDangling` is a refinement but not an equivalence (it erases UB). So neither rewrite is an equivalence in either direction.
* **`storage-marker-erasure-refines`** (theorem, T1): In the toy, under every semantics `S` (fresh addresses, or any static slot assignment, including one in which `x` shares its slot with another local), for every program `P` and local `x`: if no operand of `P` is a pointer constant carrying an allocation identifier (`NoProvConst P`), then erasing every `storageLive x` and `storageDead x` (so that, for `x < P.locals.length`, `x` is allocated at entry for the whole run) gives a prefix-preserving refinement of `P`. Without `NoProvConst` the statement is false (`refuted_eraseMarkers_refinesPP`).
* **`storage-marker-erasure-end-to-end-with-static-slots`** (theorem, T0): In the toy, for every slot assignment `s`, program `P` and local `x`: if no operand of `P` is a pointer constant carrying an allocation identifier (`NoProvConst P`) and the slot execution of `P` refines its fresh-address execution (`RefinesAcross .fresh P (.slots s) P`), then the slot execution of `P` with the markers of `x` erased, with the same `s`, refines the fresh-address execution of `P`. Without `NoProvConst` the statement is false (`refuted_eraseMarkers_slots_refinesAcross_fresh`).
* **`storage-marker-erasure-shared-slot-lowering-mismatch`** (counterexample, T1): Under the slot assignment `sShare`, which places locals `0` and `1` of `pShare` at the same address (their live ranges are disjoint, and `pShare` reaches UB at its final read: `pShare_fresh_wrong`, `pShare_slots_beh`): the slot execution of `pShare` refines its fresh-address execution; the slot execution of `pShare` with the markers of local `0` erased still refines the fresh-address execution of `pShare`; but it does not refine the fresh-address execution of the marker-erased program itself: the write of `7` to local `1` overwrites the shared cell, so the slot execution emits `7` (`pShare_erased_slots_beh`), while every fresh-address execution of the marker-erased program emits `5` or blocks (`pShare_erased_fresh_beh`).
* **`storage-marker-erasure-equivalence-sufficient-condition`** (theorem, T1): In the toy, under fresh addresses, for every program `P` and local `x`: if every local of `P` has alignment at least `1` (`hwf`), no statement of `P` observes an address (`NoAddrObs`: no `ptrEq` and no `addrOf`), and `P` is UB-free (`UBFree .fresh P`), then erasing the markers of `x` is a prefix-preserving equivalence (traces coincide, and UB-freedom transfers in both directions). Each of the three hypotheses is tight (`eraseMarkers_hwf_counterexample`, `eraseMarkers_hobs_counterexample`, `eraseMarkers_hub_counterexample`).
* **`storage-marker-erasure-equivalence-conditions-not-necessary`** (counterexample, T0): Under fresh addresses: erasing the markers of `pDeadUse` (which writes `x` while it is unallocated and then reaches `unreachable`, so it is not UB-free) is an equivalence: both programs reach UB before any event, the marker-erased one at `unreachable` (`pDeadUse_fresh_beh`, `pDeadUse_erased_fresh_beh`); erasing the markers of `pAddrSelf` (which compares `&raw x` with itself within one live range, so `NoAddrObs` fails) is an equivalence (both emit `1` or block: `pAddrSelf_fresh_beh`, `pAddrSelf_erased_fresh_beh`); and erasing the markers of `pAlignZeroOne` (one local of alignment `0`, no address observation, UB-free) is an equivalence (`eraseMarkers_fresh_equivPP_without_alignPos`).

Non-claims for every card are listed under **Boundaries** (non-claims first); read them before relying on a result. Two earlier candidate statements about the toy model were false; the theorems `refuted_eraseMarkers_refinesPP` and `refuted_eraseMarkers_slots_refinesAcross_fresh` are refutations of those earlier candidate statements (marker erasure without the condition `NoProvConst` on pointer constants), recorded under **Boundaries**, subsection *Refuted earlier formulations (reference points, not results)*; they are not claims about rustc or any other compiler.

## Applicability

### Model fidelity

This is a toy model. Its definitions are meant to capture the parts of a Rust-like abstract machine (in the style of rustc MIR and MiniRust) that decide whether computing a place or accessing a value is undefined behaviour, and four MIR-level edits whose soundness depends on them: deleting a `PlaceMention`, turning a `switchInt` whose arms all jump to one block into a `goto`, rewriting `&p` to `&raw p`, and erasing the storage markers of a local. The known gaps are:

- The toy is one CFG language with places, storage markers and two allocation modes. Its rules are modelled on documented behaviour of rustc MIR, MiniRust and the Rust Reference (`derived (modeling bridge)`); no correspondence is proved.
- Locals without storage markers are allocated at entry for the whole run (the rule documented for rustc MIR); MiniRust's `create_frame` allocates only the return local and the arguments.
- `decodePtr` rejects mixed or mismatched pointer fragments (UB on load); MiniRust's `decode_ptr` yields a pointer without provenance for initialized bytes with mismatched provenance.
- `Ty.enum` is a field-less enum read directly by an operand; MiniRust and rustc MIR read the discriminant of an enum with fields through a separate expression (`ValueExpr::GetDiscriminant`).
- No aliasing model: creating `&p` and `&raw p` differ only in `RefOk`; MiniRust's `ValueExpr::AddrOf` also retags the pointer.
- Toy simplifications: `Mem.store` does not check that the stored value matches the type; `Ty.decode` ignores the size field of `Ty.int` and `Ty.enum` (the length comes from `Mem.load`); bytes decode with Nat remainder `b % 256`; index locals have the one-byte type `idxTy`; pointers have size `ptrSize = 2` and alignment `ptrAlign = 2`; addresses are unbounded natural numbers (no wrapping, no out-of-memory).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

### Toolchain and project

* Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`); no Mathlib and no other dependency (`lean/lakefile.toml` has one `[[lean_lib]]`, `Toy`, and no `[[require]]`).
* Namespace `Toy.PlaceEval`. Definitions: `Memory.lean`, `Place.lean`, `Lang.lean`, `Semantics.lean`, `Transforms.lean`; example programs: `Programs.lean`, `ConstProv.lean`; results and examples: `PlaceUB.lean`, `Examples.lean`, `Erasure.lean`, `MarkerBehaviours.lean`, `Markers.lean`, `NonVacuity.lean`, `ZeroSize.lean`; general simulation arguments: `RunLemmas.lean`, `Simulation.lean`, `EditSim.lean`; the proof of the two storage-marker theorems: `LazySim.lean`, `MarkerSim.lean`, `MarkerStep.lean`, `MarkerFwd.lean`, `MarkerRevMem.lean`, `MarkerRevAlloc.lean`, `MarkerRevRel.lean`, `MarkerRev.lean`, `MarkerEquiv.lean` (all under `lean/Toy/PlaceEval/`).
* `lean/RevalidationAudit.lean` is outside the library target; it prints the axioms of every main result (see **Revalidation**).

### Subjects

`REPORT.json` lists the Lean toolchain release that checks every proof; the upstream revisions whose documentation is quoted in prior-art entries and modeling-bridge remarks (rust-lang/rust `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, rust-lang/reference `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, rust-lang/rfcs `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, minirust/minirust `063d784186d3252bee242217f218223205c0b568`, AbsInt/CompCert `5e4ef44c57b22cdc2e1893770843fd693a5f82e1`); and the papers cited as prior art. The toy model is written in the style of the documented rules of those systems; the report establishes facts about the toy (kernel-checked) and, separately, quotes what those systems document. No relation between the toy and any of them is proved, and no tool of theirs was run.

## Findings

### Definitions (verbatim) with examples

Every Lean block in this report is a verbatim quote of the package source, labelled `-- path:lines` relative to the package root (the Lake project is `lean/`); theorem quotes end at the line that ends the statement.

| Definition | Captures | Positive example | Negative example |
|---|---|---|---|
| `Ptr` | a pointer: optional provenance (an allocation identifier) and an unbounded address | `decodePtr_ex_pos_frags` | `decodePtr_ex_neg_mismatch` |
| `Alloc` | an allocation: base, size, liveness (freed allocations stay in the table) | `inBounds_ex_pos` | `inBounds_ex_neg_freed` |
| `Cell` | one byte of storage: uninitialized, a byte, or a pointer fragment | `load_ex_pos_int` | `load_ex_neg_uninit` |
| `Mem` | allocation table and physically addressed cells | `load_ex_pos_ptr` | `load_ex_neg_freed` |
| `aligned` | address is a multiple of the alignment (Nat remainder; for alignment 0 exactly address 0) | `aligned_ex_pos`, `aligned_zero_ex_pos` | `aligned_ex_neg`, `aligned_zero_ex_neg` |
| `Mem.inBounds` | pointer derived from a live allocation, whole range within it | `inBounds_ex_pos_end` | `inBounds_ex_neg_past` |
| `Mem.dereferenceable` | access of `n` bytes permitted (zero bytes: every pointer) | `dereferenceable_ex_pos_zero_null` | `dereferenceable_ex_neg_freed` |
| `Mem.offsetInbounds` | in-bounds offset rule with the zero-offset exemption | `offsetInbounds_ex_pos_one_past_end`, `offsetInbounds_ex_pos_zero_null` | `offsetInbounds_ex_neg_freed` |
| `Ty` | scalar types: integers, the raw pointer type, field-less enums with valid tags | `decode_enum_ex_pos` | `decode_enum_ex_neg_tag` |
| `Val` | values: integers and pointers (no uninitialized value) | `load_ex_pos_int` | `decode_int_ex_neg_uninit` |
| `decodePtr` | cells holding a pointer value | `decodePtr_ex_pos_bytes` | `decodePtr_ex_neg_uninit` |
| `Ty.decode` | cells decoding at a type (validity of the read value) | `decode_enum_ex_pos` | `decode_int_ex_neg_uninit` |
| `Mem.load` | a value read (a zero-size read passes the dereferenceability check on every pointer; alignment and decoding are still checked) | `load_ex_pos_ptr`, `load_ex_pos_zero_size_null`, `load_ex_pos_zero_size_enum` | `load_ex_neg_misaligned`, `load_ex_neg_zero_size_enum` |
| `Mem.store` | a value write | `store_ex_pos` | `store_ex_neg_freed` |
| `DerefLoadOk` | the pointer load of a `deref` projection succeeds | `derefLoadOk_ex_pos` | `derefLoadOk_ex_neg_not_a_pointer` |
| `State` | memory and the frame (local ↦ backing allocation or unallocated) | `evalPlace_ex_pos_deref` | `evalPlace_ex_neg_unallocated_local` |
| `State.basePtr` | the pointer to a local (none if the frame records no allocation, or a missing one) | `evalPlace_ex_pos_deref`, `basePtr_freed_in_frame_eq_some` | `evalPlace_ex_neg_unallocated_local`, `basePtr_missing_alloc_eq_none` |
| `State.readIndex` | the read of an index local | `readIndex_ex_pos` | `readIndex_ex_neg_unallocated` |
| `evalPlace` | place evaluation (no access to the final place) | `evalPlace_ex_pos_index`, `evalPlace_ex_pos_index_zero_size` | `evalPlace_ex_neg_inner_not_pointer`, `evalPlace_ex_neg_index_dangling` |
| `evalPrefix` | evaluation of the first `i` projections | `evalPrefix_ex_pos` | `evalPrefix_ex_neg_unallocated` |
| `RefOk` | reference validity: address `≠ 0` (regardless of provenance), aligned, dereferenceable | `refOk_ex_pos` | `refOk_ex_neg_misaligned`, `refOk_ex_neg_align_zero` |
| `Operand.evalInt` | an operand evaluating to an integer | `evalInt_ex_pos` | `evalInt_copy_instance` |
| `allocate` | allocation of a local under an allocation mode | `allocate_fresh_ex_pos` | `allocate_fresh_ex_neg_overlap` |
| `deallocate` | freeing a local (a no-op if unallocated) | `deallocate_ex` | `deallocate_ex_noop` |
| `Prog.hasMarkers` | a local has storage markers | `hasMarkers_ex_pos` | `hasMarkers_ex_neg` |
| `HasBeh` | behaviours under a semantics (union over oracles) | `pAddrCmp_fresh_term_zero`, `pNull_zero_beh` | `hasBeh_ex_neg_erased_addrCmp`, `eraseMarkers_alignZero_not_equivPP` |
| `ImprovesPP` | prefix-preserving behaviour improvement | `improvesPP_ex_pos_prefix` | `improvesPP_ex_neg_nonprefix` |
| `RefinesAcross` | refinement between two (program, semantics) pairs | `eraseMarkers_slots_nonvacuous` | `eraseMarkers_slots_invalid_counterexample` |
| `EquivPP` | refinement in both directions | `switchToGoto_validTag_equivPP` | `switchToGoto_erases_operand_ub` |
| `ReachableAt` | a program point reached in a state, for some oracle | `reachableAt_ex_pos` | `reachableAt_ex_neg` |
| `GoesWrongFrom` | the run from a configuration reaches UB after a given trace | `goesWrongFrom_ex_pos` | `goesWrongFrom_ex_neg` |
| `UBFree` | no behaviour is UB (semantic property) | `noAddrObs_ubFree_pLive` | `ubCheck_after_erasePlaceMention_misses_place_ub` |
| `ExactUBChecker` | a Boolean verdict equal to `UBFree` | `exactUBChecker_exists` | `not_exactUBChecker_const_true` |
| `deleteStmt` | delete one statement (out-of-range indices: no change) | `deleteStmt_ex` | `deleteStmt_ex_out_of_range` |
| `setTerm` | replace a terminator (out-of-range labels: no change) | `setTerm_ex` | `setTerm_ex_out_of_range` |
| `setStmt` | replace a statement (out-of-range labels or indices: no change) | `setStmt_ex` | `setStmt_ex_out_of_range_blk`, `setStmt_ex_out_of_range_idx` |
| `eraseMarkers` | erase all markers of one local | `eraseMarkers_ex` | `eraseMarkers_ex_other_local` |
| `NoAddrObs` | no statement observes an address | `noAddrObs_ex_pos` | `noAddrObs_ex_neg` |
| `NoProvConst` | no operand is a pointer constant carrying an allocation identifier | `noProvConst_ex_pos` | `noProvConst_ex_neg` |

Syntax declarations (no admissibility condition; instances are the concrete programs): `Layout`, `Proj`, `Place`, `Operand`, `Rvalue`, `Stmt`, `Term`, `Block`, `Prog`, `AllocMode`, `Sem`, `Cfg`, `Beh`, `Outcome`.

```lean
-- lean/Toy/PlaceEval/Memory.lean:17
abbrev Local := Nat
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:20
abbrev AllocId := Nat
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:26-28
structure Ptr where
  prov : Option AllocId
  addr : Nat
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:32
def Ptr.offset (q : Ptr) (k : Nat) : Ptr := ⟨q.prov, q.addr + k⟩
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:37-40
structure Alloc where
  base : Nat
  size : Nat
  live : Bool
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:45-48
inductive Cell where
  | uninit
  | byte (b : Nat)
  | ptrFrag (q : Ptr) (i : Nat)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:54-56
structure Mem where
  allocs : List Alloc
  cells : List (Nat × Cell)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:60-63
def Mem.get (m : Mem) (a : Nat) : Cell :=
  match m.cells.find? (fun e => e.1 == a) with
  | some e => e.2
  | none => .uninit
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:66-67
def Mem.readCells (m : Mem) (a n : Nat) : List Cell :=
  (List.range n).map fun i => m.get (a + i)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:70-72
def placeCells : Nat → List Cell → List (Nat × Cell)
  | _, [] => []
  | a, c :: cs => (a, c) :: placeCells (a + 1) cs
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:75-76
def Mem.writeCells (m : Mem) (a : Nat) (cs : List Cell) : Mem :=
  { m with cells := placeCells a cs ++ m.cells }
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:82
def aligned (al a : Nat) : Bool := a % al == 0
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:88-94
def Mem.inBounds (m : Mem) (q : Ptr) (n : Nat) : Bool :=
  match q.prov with
  | none => false
  | some k =>
    match m.allocs[k]? with
    | none => false
    | some al => al.live && decide (al.base ≤ q.addr) && decide (q.addr + n ≤ al.base + al.size)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:99-100
def Mem.dereferenceable (m : Mem) (q : Ptr) (n : Nat) : Bool :=
  n == 0 || m.inBounds q n
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:107-108
def Mem.offsetInbounds (m : Mem) (q : Ptr) (k : Nat) : Bool :=
  k == 0 || m.inBounds q k
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:119-122
inductive Ty where
  | int (size align : Nat)
  | ptr
  | enum (size align : Nat) (valid : List Nat)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:126
def ptrSize : Nat := 2
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:129
def ptrAlign : Nat := 2
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:132-135
def Ty.size : Ty → Nat
  | .int s _ => s
  | .ptr => ptrSize
  | .enum s _ _ => s
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:138-141
def Ty.align : Ty → Nat
  | .int _ a => a
  | .ptr => ptrAlign
  | .enum _ a _ => a
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:145-147
inductive Val where
  | int (n : Nat)
  | ptr (q : Ptr)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:152-155
def decodeLE : List Cell → Option Nat
  | [] => some 0
  | .byte b :: cs => (decodeLE cs).map fun v => b % 256 + 256 * v
  | _ :: _ => none
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:159-161
def encodeLE : Nat → Nat → List Cell
  | 0, _ => []
  | n + 1, v => .byte (v % 256) :: encodeLE n (v / 256)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:167-169
def decodePtr : List Cell → Option Ptr
  | [.ptrFrag q 0, .ptrFrag q' 1] => if q = q' then some q else none
  | cs => if cs.length = ptrSize then (decodeLE cs).map fun a => ⟨none, a⟩ else none
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:173-179
def Ty.decode : Ty → List Cell → Option Val
  | .int _ _, cs => (decodeLE cs).map Val.int
  | .ptr, cs => (decodePtr cs).map Val.ptr
  | .enum _ _ valid, cs =>
    match decodeLE cs with
    | some n => if n ∈ valid then some (.int n) else none
    | none => none
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:183-185
def Val.encode (n : Nat) : Val → List Cell
  | .int v => encodeLE n v
  | .ptr q => (List.range n).map (Cell.ptrFrag q)
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:189-192
def Mem.load (m : Mem) (q : Ptr) (τ : Ty) : Option Val :=
  if m.dereferenceable q τ.size && aligned τ.align q.addr then
    τ.decode (m.readCells q.addr τ.size)
  else none
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:196-199
def Mem.store (m : Mem) (q : Ptr) (τ : Ty) (v : Val) : Option Mem :=
  if m.dereferenceable q τ.size && aligned τ.align q.addr then
    some (m.writeCells q.addr (v.encode τ.size))
  else none
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:202-205
def Mem.loadPtr (m : Mem) (q : Ptr) : Option Ptr :=
  match m.load q .ptr with
  | some (.ptr r) => some r
  | _ => none
```

```lean
-- lean/Toy/PlaceEval/Memory.lean:210-212
def DerefLoadOk (m : Mem) (q : Ptr) : Prop :=
  m.dereferenceable q ptrSize = true ∧ aligned ptrAlign q.addr = true ∧
    ∃ r, decodePtr (m.readCells q.addr ptrSize) = some r
```

```lean
-- lean/Toy/PlaceEval/Place.lean:17-19
structure Layout where
  size : Nat
  align : Nat
```

```lean
-- lean/Toy/PlaceEval/Place.lean:23-26
inductive Proj where
  | field (off : Nat)
  | index (j : Local) (elemSize : Nat)
  | deref
```

```lean
-- lean/Toy/PlaceEval/Place.lean:30-32
structure Place where
  base : Local
  proj : List Proj
```

```lean
-- lean/Toy/PlaceEval/Place.lean:38-40
structure State where
  mem : Mem
  frame : List (Option AllocId)
```

```lean
-- lean/Toy/PlaceEval/Place.lean:44
def State.allocOf (st : State) (x : Local) : Option AllocId := st.frame.getD x none
```

```lean
-- lean/Toy/PlaceEval/Place.lean:48-51
def State.basePtr (st : State) (x : Local) : Option Ptr :=
  match st.allocOf x with
  | none => none
  | some k => (st.mem.allocs[k]?).map fun al => ⟨some k, al.base⟩
```

```lean
-- lean/Toy/PlaceEval/Place.lean:54
def idxTy : Ty := .int 1 1
```

```lean
-- lean/Toy/PlaceEval/Place.lean:58-59
def State.readLocal (st : State) (j : Local) (τ : Ty) : Option Val :=
  (st.basePtr j).bind fun q => st.mem.load q τ
```

```lean
-- lean/Toy/PlaceEval/Place.lean:62-65
def State.readIndex (st : State) (j : Local) : Option Nat :=
  match st.readLocal j idxTy with
  | some (.int n) => some n
  | _ => none
```

```lean
-- lean/Toy/PlaceEval/Place.lean:70-76
def projStep (st : State) (q : Ptr) : Proj → Option Ptr
  | .deref => st.mem.loadPtr q
  | .field off => if st.mem.offsetInbounds q off then some (q.offset off) else none
  | .index j sz =>
    match st.readIndex j with
    | some n => if st.mem.offsetInbounds q (n * sz) then some (q.offset (n * sz)) else none
    | none => none
```

```lean
-- lean/Toy/PlaceEval/Place.lean:79-81
def evalProjs (st : State) : Ptr → List Proj → Option Ptr
  | q, [] => some q
  | q, π :: πs => (projStep st q π).bind fun q' => evalProjs st q' πs
```

```lean
-- lean/Toy/PlaceEval/Place.lean:86-87
def evalPlace (st : State) (p : Place) : Option Ptr :=
  (st.basePtr p.base).bind fun q => evalProjs st q p.proj
```

```lean
-- lean/Toy/PlaceEval/Place.lean:91-92
def evalPrefix (st : State) (p : Place) (i : Nat) : Option Ptr :=
  (st.basePtr p.base).bind fun q => evalProjs st q (p.proj.take i)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:22
abbrev Label := Nat
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:25-27
inductive Operand where
  | copy (p : Place) (τ : Ty)
  | const (v : Val)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:33-38
inductive Rvalue where
  | use (o : Operand)
  | rawRef (p : Place)
  | ref (p : Place) (L : Layout)
  | ptrEq (a b : Operand)
  | addrOf (a : Operand)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:43-48
inductive Stmt where
  | placeMention (p : Place)
  | assign (dst : Place) (τ : Ty) (rv : Rvalue)
  | emit (rv : Rvalue)
  | storageLive (x : Local)
  | storageDead (x : Local)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:53-57
inductive Term where
  | goto (b : Label)
  | switchInt (o : Operand) (arms : List (Nat × Label)) (ow : Label)
  | halt
  | unreachable
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:61-63
structure Block where
  stmts : List Stmt
  term : Term
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:67
def Block.unreach : Block := ⟨[], .unreachable⟩
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:71-73
structure Prog where
  locals : List Layout
  blocks : List Block
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:77
def Prog.blk (P : Prog) (l : Label) : Block := P.blocks.getD l Block.unreach
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:80
def Prog.layout (P : Prog) (x : Local) : Layout := P.locals.getD x ⟨0, 1⟩
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:83-86
def Stmt.isMarkerOf (x : Local) : Stmt → Bool
  | .storageLive y => y == x
  | .storageDead y => y == x
  | _ => false
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:90-91
def Prog.hasMarkers (P : Prog) (x : Local) : Bool :=
  P.blocks.any fun b => b.stmts.any (Stmt.isMarkerOf x)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:96-98
inductive AllocMode where
  | fresh (ω : Nat → Nat)
  | slots (s : Local → Nat)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:102-103
def disjointRanges (a n b m : Nat) : Bool :=
  n == 0 || m == 0 || decide (a + n ≤ b) || decide (b + m ≤ a)
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:108-120
def allocate (mode : AllocMode) (st : State) (x : Local) (L : Layout) : Option State :=
  let k := st.mem.allocs.length
  let a := match mode with
    | .fresh ω => L.align * (ω k + 1)
    | .slots s => s x
  let ok := match mode with
    | .fresh _ => st.mem.allocs.all fun al => !al.live || disjointRanges a L.size al.base al.size
    | .slots _ => true
  if ok then
    some { mem := { allocs := st.mem.allocs ++ [⟨a, L.size, true⟩],
                    cells := placeCells a (List.replicate L.size .uninit) ++ st.mem.cells },
           frame := st.frame.set x (some k) }
  else none
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:124-129
def deallocate (st : State) (x : Local) : State :=
  match st.allocOf x with
  | none => st
  | some k =>
    { mem := { st.mem with allocs := st.mem.allocs.modify k fun al => { al with live := false } },
      frame := st.frame.set x none }
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:134-136
def Operand.eval (st : State) : Operand → Option Val
  | .copy p τ => (evalPlace st p).bind fun q => st.mem.load q τ
  | .const v => some v
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:141-142
def RefOk (m : Mem) (q : Ptr) (L : Layout) : Prop :=
  q.addr ≠ 0 ∧ aligned L.align q.addr = true ∧ m.dereferenceable q L.size = true
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:149-160
def Rvalue.eval (st : State) : Rvalue → Option Val
  | .use o => o.eval st
  | .rawRef p => (evalPlace st p).map Val.ptr
  | .ref p L => (evalPlace st p).bind fun q => if RefOk st.mem q L then some (.ptr q) else none
  | .ptrEq a b =>
    match a.eval st, b.eval st with
    | some (.ptr q), some (.ptr r) => some (.int (if q.addr = r.addr then 1 else 0))
    | _, _ => none
  | .addrOf a =>
    match a.eval st with
    | some (.ptr q) => some (.int q.addr)
    | _ => none
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:163-166
def Operand.evalInt (st : State) (o : Operand) : Option Nat :=
  match o.eval st with
  | some (.int n) => some n
  | _ => none
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:172-175
inductive StmtResult where
  | ok (ev : Option Nat) (st : State)
  | ub
  | block
```

```lean
-- lean/Toy/PlaceEval/Lang.lean:181-201
def execStmt (mode : AllocMode) (P : Prog) (st : State) : Stmt → StmtResult
  | .placeMention p => if (evalPlace st p).isSome then .ok none st else .ub
  | .assign dst τ rv =>
    match evalPlace st dst with
    | none => .ub
    | some q =>
      match rv.eval st with
      | none => .ub
      | some v =>
        match st.mem.store q τ v with
        | some m => .ok none { st with mem := m }
        | none => .ub
  | .emit rv =>
    match rv.eval st with
    | some (.int n) => .ok (some n) st
    | _ => .ub
  | .storageLive x =>
    match allocate mode (deallocate st x) x (P.layout x) with
    | some st' => .ok none st'
    | none => .block
  | .storageDead x => .ok none (deallocate st x)
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:20-23
structure Cfg where
  lbl : Label
  rest : List Stmt
  st : State
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:27
def Prog.entry (P : Prog) (b : Label) (st : State) : Cfg := ⟨b, (P.blk b).stmts, st⟩
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:31-32
def Prog.at (P : Prog) (l : Label) (i : Nat) (st : State) : Cfg :=
  ⟨l, (P.blk l).stmts.drop i, st⟩
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:35-39
def allocEntry (mode : AllocMode) (P : Prog) : List Local → State → Option State
  | [], st => some st
  | x :: xs, st =>
    if P.hasMarkers x then allocEntry mode P xs st
    else (allocate mode st x (P.layout x)).bind (allocEntry mode P xs)
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:43-45
def Prog.initState (mode : AllocMode) (P : Prog) : Option State :=
  allocEntry mode P (List.range P.locals.length)
    ⟨⟨[], []⟩, List.replicate P.locals.length none⟩
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:48-50
def selectTarget : List (Nat × Label) → Label → Nat → Label
  | [], ow, _ => ow
  | (v, b) :: arms, ow, n => if n = v then b else selectTarget arms ow n
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:53-57
inductive StepResult where
  | next (ev : Option Nat) (c : Cfg)
  | halt (st : State)
  | ub
  | block
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:60-75
def step (mode : AllocMode) (P : Prog) (c : Cfg) : StepResult :=
  match c.rest with
  | s :: rest =>
    match execStmt mode P c.st s with
    | .ok ev st' => .next ev ⟨c.lbl, rest, st'⟩
    | .ub => .ub
    | .block => .block
  | [] =>
    match (P.blk c.lbl).term with
    | .goto b => .next none (P.entry b c.st)
    | .switchInt o arms ow =>
      match o.evalInt c.st with
      | some n => .next none (P.entry (selectTarget arms ow n) c.st)
      | none => .ub
    | .halt => .halt c.st
    | .unreachable => .ub
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:78-82
inductive Outcome where
  | done (t : List Nat) (st : State)
  | ub (t : List Nat)
  | running (c : Cfg) (t : List Nat)
  | blocked
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:86-90
def Outcome.cons (ev : Option Nat) : Outcome → Outcome
  | .done t s => .done (ev.toList ++ t) s
  | .ub t => .ub (ev.toList ++ t)
  | .running c t => .running c (ev.toList ++ t)
  | .blocked => .blocked
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:93-97
def Outcome.trace : Outcome → List Nat
  | .done t _ => t
  | .ub t => t
  | .running _ t => t
  | .blocked => []
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:100-102
def Outcome.isRunning : Outcome → Bool
  | .running _ _ => true
  | _ => false
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:105-112
def run (mode : AllocMode) (P : Prog) : Nat → Cfg → Outcome
  | 0, c => .running c []
  | n + 1, c =>
    match step mode P c with
    | .next ev c' => (run mode P n c').cons ev
    | .halt s => .done [] s
    | .ub => .ub []
    | .block => .blocked
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:116-120
inductive Beh where
  | term (t : List Nat)
  | wrong (t : List Nat)
  | div (t : List Nat)
  | react (f : Nat → Nat)
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:123
def prefixOf (f : Nat → Nat) (k : Nat) : List Nat := (List.range k).map f
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:126-132
def HasBehFrom (mode : AllocMode) (P : Prog) (c : Cfg) : Beh → Prop
  | .term t => ∃ n s, run mode P n c = .done t s
  | .wrong t => ∃ n, run mode P n c = .ub t
  | .div t => (∀ n, (run mode P n c).isRunning = true) ∧
      ∃ N, ∀ n, N ≤ n → (run mode P n c).trace = t
  | .react f => (∀ n, (run mode P n c).isRunning = true) ∧
      ∀ k, ∃ n, (run mode P n c).trace = prefixOf f k
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:136-137
def HasBehIn (mode : AllocMode) (P : Prog) (b : Beh) : Prop :=
  ∃ st0, P.initState mode = some st0 ∧ HasBehFrom mode P (P.entry 0 st0) b
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:140-142
inductive Sem where
  | fresh
  | slots (s : Local → Nat)
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:145-147
def Sem.mode : Sem → (Nat → Nat) → AllocMode
  | .fresh, ω => .fresh ω
  | .slots s, _ => .slots s
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:150
def HasBeh (S : Sem) (P : Prog) (b : Beh) : Prop := ∃ ω, HasBehIn (S.mode ω) P b
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:153-157
def Beh.HasPrefix : Beh → List Nat → Prop
  | .term u, t => t <+: u
  | .wrong u, t => t <+: u
  | .div u, t => t <+: u
  | .react f, t => t = prefixOf f t.length
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:161-162
def ImprovesPP (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .wrong t ∧ bt.HasPrefix t
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:166-167
def RefinesAcross (Ss : Sem) (src : Prog) (St : Sem) (tgt : Prog) : Prop :=
  ∀ bt, HasBeh St tgt bt → ∃ bs, HasBeh Ss src bs ∧ ImprovesPP bt bs
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:170
def RefinesPP (S : Sem) (src tgt : Prog) : Prop := RefinesAcross S src S tgt
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:173
def EquivPP (S : Sem) (p q : Prog) : Prop := RefinesPP S p q ∧ RefinesPP S q p
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:177-179
def ReachableAt (S : Sem) (P : Prog) (l : Label) (i : Nat) (st : State) : Prop :=
  ∃ ω st0 n t, P.initState (S.mode ω) = some st0 ∧
    run (S.mode ω) P n (P.entry 0 st0) = .running (P.at l i st) t
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:182-183
def GoesWrongFrom (S : Sem) (P : Prog) (c : Cfg) (t : List Nat) : Prop :=
  ∃ ω n, run (S.mode ω) P n c = .ub t
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:187
def UBFree (S : Sem) (P : Prog) : Prop := ∀ t, ¬ HasBeh S P (.wrong t)
```

```lean
-- lean/Toy/PlaceEval/Semantics.lean:191
def ExactUBChecker (S : Sem) (chk : Prog → Bool) : Prop := ∀ P, chk P = true ↔ UBFree S P
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:12-13
def Prog.setBlk (P : Prog) (l : Label) (B : Block) : Prog :=
  { P with blocks := P.blocks.set l B }
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:16-17
def deleteStmt (P : Prog) (l : Label) (i : Nat) : Prog :=
  P.setBlk l { P.blk l with stmts := (P.blk l).stmts.eraseIdx i }
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:20-21
def setTerm (P : Prog) (l : Label) (t : Term) : Prog :=
  P.setBlk l { P.blk l with term := t }
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:24-25
def setStmt (P : Prog) (l : Label) (i : Nat) (s : Stmt) : Prog :=
  P.setBlk l { P.blk l with stmts := (P.blk l).stmts.set i s }
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:30-32
def eraseMarkers (P : Prog) (x : Local) : Prog :=
  { P with blocks := P.blocks.map fun b =>
      { b with stmts := b.stmts.filter fun s => !s.isMarkerOf x } }
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:35-38
def Rvalue.observesAddr : Rvalue → Bool
  | .ptrEq _ _ => true
  | .addrOf _ => true
  | _ => false
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:41-44
def Stmt.rvalue? : Stmt → Option Rvalue
  | .assign _ _ rv => some rv
  | .emit rv => some rv
  | _ => none
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:48-49
def NoAddrObs (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, ∀ s ∈ b.stmts, ∀ rv, s.rvalue? = some rv → rv.observesAddr = false
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:52-54
def Operand.provFree : Operand → Bool
  | .const (.ptr q) => q.prov.isNone
  | _ => true
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:57-61
def Rvalue.provFree : Rvalue → Bool
  | .use o => o.provFree
  | .ptrEq a b => a.provFree && b.provFree
  | .addrOf a => a.provFree
  | _ => true
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:64-67
def Stmt.provFree : Stmt → Bool
  | .assign _ _ rv => rv.provFree
  | .emit rv => rv.provFree
  | _ => true
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:70-72
def Term.provFree : Term → Bool
  | .switchInt o _ _ => o.provFree
  | _ => true
```

```lean
-- lean/Toy/PlaceEval/Transforms.lean:79-80
def NoProvConst (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, (∀ s ∈ b.stmts, s.provFree = true) ∧ b.term.provFree = true
```


### Key definitions unfolded (prose)

Unfolded (prose):
- `evalPlace st p` takes the pointer of the base local (`State.basePtr`: provenance = the backing allocation,
  address = its base; `none` if the frame records no allocation for the local or names a missing one) and applies `projStep` to each projection. `deref` loads a
  pointer (`Mem.loadPtr`: dereferenceable for `ptrSize = 2` bytes, `ptrAlign = 2`-aligned, cells decoding to a
  pointer value); `field off` adds `off` subject to `Mem.offsetInbounds`; `index j sz` reads local `j` at the
  one-byte integer type `idxTy` and adds `n * sz` subject to `Mem.offsetInbounds`. The final place is never read.
- `Mem.inBounds m q n`: `q.prov = some k`, allocation `k` exists and is live, `base ≤ q.addr` and
  `q.addr + n ≤ base + size` (the end may be one past the last byte; unbounded natural numbers, no wrapping).
  `Mem.dereferenceable m q n` and `Mem.offsetInbounds m q n` are both `n = 0 ∨ Mem.inBounds m q n` (definitionally
  equal, `offsetInbounds_eq_dereferenceable`). Degenerate edges: a zero-byte access or a zero offset is permitted for
  every pointer, including null; `aligned 0 a` holds exactly for `a = 0` (`a % 0 = a`).
- Value reads (`Mem.load`) require dereferenceability for the type's size, alignment for the type's alignment, and
  decoding: integers need byte cells (`b % 256` per byte, little-endian), the pointer type needs two fragments of one
  pointer or two bytes (a pointer without provenance), an enum needs byte cells encoding a member of its valid-tag list.
- `allocate mode st x L`: under `fresh ω`, the `k`-th allocation (`k` = number of allocations so far) is placed at
  `L.align * (ω k + 1)` and refused (the run blocks, no behaviour) if its range overlaps a live allocation; under
  `slots s` it is placed at `s x` without an overlap check. Fresh memory is uninitialized. `storageLive x` runs
  `deallocate` then `allocate`; `storageDead x` runs `deallocate` (a no-op if `x` is unallocated). Locals without
  markers are allocated at entry, in index order (`Prog.initState`); a local `x ≥ P.locals.length` is never recorded in the frame.
- `HasBeh S P b` is `∃ ω, HasBehIn (S.mode ω) P b`; `HasBehFrom` defines `term t` (some fuel reaches `done t _`),
  `wrong t` (some fuel reaches `ub t`), `div t` and `react f` (every fuel is still running; the trace is eventually
  `t`, resp. every prefix of `f` occurs). A blocked run has no behaviour.
- `ImprovesPP bt bs` is `bt = bs ∨ ∃ t, bs = .wrong t ∧ bt.HasPrefix t`; `RefinesAcross Ss P St Q` is
  `∀ bt, HasBeh St Q bt → ∃ bs, HasBeh Ss P bs ∧ ImprovesPP bt bs`; `RefinesPP S P Q = RefinesAcross S P S Q`;
  `EquivPP S P Q = RefinesPP S P Q ∧ RefinesPP S Q P`. `RefinesPP` does not require the target to have a behaviour.
- `ReachableAt S P l i st`: for some oracle, the run from the initial state reaches the configuration `P.at l i st`
  (block `l`, statements from index `i` on, state `st`) while still running.
- `NoProvConst P`: no operand of `P` is a pointer constant `.const (.ptr ⟨some k, a⟩)`.

### Cards

Each card gives the plain claim, kind, tier and depth, the verbatim Lean statement, the hypothesis ledger with tightness counterexamples, the non-vacuity witness, prior art and the design question. The non-claims of every card are under **Boundaries**.

#### `place-evaluation-ub-exact-conditions` (characterization)

**Plain claim.** In the toy, for every state `st` (reachable or not) and place `p`, evaluating `p` is UB (`evalPlace st p = none`) iff (a) `st.basePtr p.base = none` (the frame records no allocation for the base local, or records an allocation index missing from the table; a frame entry naming a freed allocation still yields a pointer, `basePtr_freed_in_frame_eq_some`), or, for some projection index `i` such that the first `i` projections evaluate to a pointer `q` (`evalPrefix`), projection `i` is (b) a `deref` whose pointer load at `q` fails (`¬ DerefLoadOk`: `q` is not dereferenceable for `ptrSize` bytes, is not aligned for `ptrAlign`, or its cells do not hold a pointer value), (c) a `field off` with `off ≠ 0` whose byte range is not in bounds of a live allocation that `q` is derived from (`Mem.inBounds`), (d) an `index j sz` whose read of the index local `j` fails (`State.readIndex`), or (e) an `index j sz` whose index value `n` gives a non-zero offset `n * sz` (unbounded natural-number product) that is not in bounds. Degenerate edges: a zero offset (`off = 0`, or `n = 0` or `sz = 0`) is never checked, even for a null or dangling `q` (`evalPlace_ex_pos_index_zero_size`). No disjunct constrains the pointer that evaluation finally produces.

**Kind / tier / depth.** characterization / T1 (The conditions are stated in prose by the MIR `Place` documentation and executably by MiniRust's `eval_place`; a mechanized iff over a projection list appears uncommon. No novelty is claimed.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/PlaceUB.lean:106-114
theorem evalPlace_eq_none_iff (st : State) (p : Place) :
    evalPlace st p = none ↔
      st.basePtr p.base = none ∨
      ∃ i q, evalPrefix st p i = some q ∧
        ((p.proj[i]? = some .deref ∧ ¬ DerefLoadOk st.mem q) ∨
         (∃ off, p.proj[i]? = some (.field off) ∧ off ≠ 0 ∧ st.mem.inBounds q off = false) ∨
         (∃ j sz, p.proj[i]? = some (.index j sz) ∧ st.readIndex j = none) ∨
         (∃ j sz n, p.proj[i]? = some (.index j sz) ∧ st.readIndex j = some n ∧
            n * sz ≠ 0 ∧ st.mem.inBounds q (n * sz) = false)) := by
-- lean/Toy/PlaceEval/PlaceUB.lean:55-56
theorem projStep_deref_eq_none_iff (st : State) (q : Ptr) :
    projStep st q .deref = none ↔ ¬ DerefLoadOk st.mem q := by
-- lean/Toy/PlaceEval/PlaceUB.lean:62-63
theorem projStep_field_eq_none_iff (st : State) (q : Ptr) (off : Nat) :
    projStep st q (.field off) = none ↔ off ≠ 0 ∧ st.mem.inBounds q off = false := by
-- lean/Toy/PlaceEval/PlaceUB.lean:73-76
theorem projStep_index_eq_none_iff (st : State) (q : Ptr) (j : Local) (sz : Nat) :
    projStep st q (.index j sz) = none ↔
      st.readIndex j = none ∨
        ∃ n, st.readIndex j = some n ∧ n * sz ≠ 0 ∧ st.mem.inBounds q (n * sz) = false := by
```

Unfolded (prose): `evalPlace st p` starts from `State.basePtr` of the base local (`none` if the frame records no allocation for it or records an allocation index missing from the table) and applies `projStep` left to right. `projStep st q .deref` is `st.mem.loadPtr q`; `projStep st q (.field off)` is `q.offset off` if `Mem.offsetInbounds q off` (that is, `off = 0` or `Mem.inBounds q off`), else UB; `projStep st q (.index j sz)` reads local `j` at `idxTy` (a one-byte integer) and then behaves like `field (n * sz)`. The per-step lemmas `projStep_deref_eq_none_iff`, `projStep_field_eq_none_iff` and `projStep_index_eq_none_iff` state the three failure conditions; the theorem combines them with induction on the projection list. The disjuncts of the Lean statement appear in the order (a), (b), (c), (d), (e) of the plain claim.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** No hypotheses. `evalPlace_eq_none_iff_instance`: in `stEx` the place `*(*l0)` fails (disjunct (b): the second load reads a byte and an uninitialized cell) while `*l0` evaluates; further instances: `evalPlace_ex_neg_unallocated_local` and `basePtr_missing_alloc_eq_none` (disjunct (a)), `evalPlace_ex_neg_misaligned_load` (disjunct (b), misaligned load), `evalPlace_ex_neg_field_past_end` (disjunct (c)), `evalPlace_ex_neg_index_dangling` (disjunct (e)).

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L1152–1160 (doc comment of `Place`; `///` markers removed, typos as in the source): "The "validity invariant" of places is the same as that of raw pointers, meaning that e.g. `*ptr` on a dangling or unaligned pointer is never UB. (Later doing a load/store on that place or turning it into a reference can be UB though!) The only ways for a place computation can cause UB are: - On a `Deref` projection, we do an actual load of the inner place, with all the usual consequences (the inner place must be based on an aligned pointer, it must point to allocated memory, the aliasig model must allow reads, this must not be a data race). - For the projections that perform pointer arithmetic, the offset must in-bounds of an allocation (i.e., the preconditions of `ptr::offset` must be met)."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L1145–1150 (doc comment of `Place`, `Deref` projections; `///` markers removed): "- [`Deref`](ProjectionElem::Deref): Derefs are the last type of projection, and the most complicated. They are only legal on parent places that are references, pointers, or `Box`. A `Deref` projection begins by loading a value from the parent place, as if by [`Operand::Copy`]. It then dereferences the resulting pointer, creating a place of the pointee's type. The resulting address is the address that was stored in the pointer. If the pointee type is unsized, the pointer additionally stored the value of the metadata."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L1139–1144 (doc comment of `Place`, `Index` projections; `///` markers removed): "- [`Index`](ProjectionElem::Index): Like `ConstantIndex`, only legal on `[T; N]` or `[T]`. However, `Index` additionally takes a local from which the value of the index is computed at runtime. Computing the value of the index involves interpreting the `Local` as a `Place { local, projection: [] }`, and then computing its value as if done via [`Operand::Copy`]. The array/slice is then indexed with the resulting value. The local must have type `usize`."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L364–381 (doc comment of `StatementKind::StorageLive`/`StorageDead`; `///` markers removed): "`StorageLive` and `StorageDead` statements mark the live range of a local. At any point during the execution of a function, each local is either allocated or unallocated. Except as noted below, all locals except function parameters are initially unallocated. `StorageLive` statements cause memory to be allocated for the local while `StorageDead` statements cause the memory to be freed. In other words, `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for stack-allocated local variables. Using a local in any way (not only reading/writing from it) while it is unallocated is UB. Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body. These locals are implicitly allocated for the full duration of the function. There is a convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for computing these locals. If the local is already allocated, calling `StorageLive` again will implicitly free the local and then allocate fresh uninitialized memory. If a local is already deallocated, calling `StorageDead` again is a NOP."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/docs/offset.md L16–19 (Safety of `pointer::offset`): "* If the computed offset is non-zero, then `self` must be [derived from][crate::ptr#provenance] a pointer to some [allocation], and the entire memory range between `self` and `result` (i.e., `min(self.addr(), result)..max(self.addr(), result)`) must be in bounds of that allocation."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989 (pull request #117329, "offset: allow zero-byte offset on arbitrary pointers", merged 2024-05-22); cited in prose for the zero-offset exemption that the toy's `Mem.offsetInbounds` encodes (a zero offset is permitted on every pointer).
- [documentation; connection to the toy: derived (modeling bridge)] The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L19: "* Accessing (loading from or storing to) a place that is [dangling] or [based on a misaligned pointer]."; L22: "* Performing an offsetting place projection that violates the requirements of [in-bounds pointer arithmetic](pointer#method.offset). An offsetting place projection is a [field expression][project-field], a [tuple index expression][project-tuple], or an [array/slice index expression][project-slice]."; L104: "A reference/pointer is "dangling" if not all of the bytes it [points to] are part of the same live [allocation] (so in particular they all have to be part of *some* allocation)."; L110: "> This also implies that if the [size is 0][zero-sized], then the pointer is trivially never "dangling" (even if it is a null pointer)."
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md: L214 "Like a raw pointer, the result can be misaligned or null!" (doc of `eval_place`); L228–235 (`PlaceExpr::Local`: a dead local raises UB "access to a dead local"); L246–263 (`PlaceExpr::Deref`: the operand is evaluated as a value; for safe pointer types the pointer must also be dereferenceable; misalignment is recorded in the place rather than raised); L271–299 (`PlaceExpr::Field`: `ptr_offset_inbounds`); L301–329 (`PlaceExpr::Index`: an index outside the array or slice length raises UB "access to out-of-bounds index", then `ptr_offset_inbounds`); spec/lang/step/operators.md L389–399 (`ptr_offset_inbounds` checks `signed_dereferenceable`).
- reference corpus package `pointer-provenance-models-and-integer-pointer-cast-optimizations`, cards `R5a-integer-load-of-pointer-bytes-strips-or-exposes` and `R5c-integer-value-roundtrip-does-not-carry-provenance` (provenance on stored pointer bytes; the toy here uses a minimal provenance, an optional allocation identifier, and treats pointer fragments read at an integer type as UB rather than stripping or exposing provenance).
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/representation.md L102–103: "When decoding, we have to deal with the possibility of the pointer bytes not all having the same provenance;
  this is defined to yield a pointer without provenance."

**Design question.** What exactly makes a place computation UB, so that a verifier knows which obligations a `PlaceMention`, a `&raw` or the place part of an access must discharge?

Basis: execution (Lean kernel check) — `evalPlace_eq_none_iff` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `place-evaluation-ub-exact-conditions`.

#### `place-evaluation-ignores-final-pointee` (theorem)

**Plain claim.** In the toy, for every state `st`, local `x`, projection list `pre` and `k`, the place `pre ++ [deref] ++ k × [field 0]` evaluates to exactly the pointer loaded by its final `deref` (`evalPlace_deref_zeroFields`); hence `pre ++ [deref]` evaluates iff `pre` evaluates to some `q` with `DerefLoadOk` at `q` (`evalPlace_append_deref_isSome_iff`), whatever the loaded pointer is: null, dangling, pointing into a freed allocation, misaligned, or pointing to uninitialized cells.

**Kind / tier / depth.** theorem / T1 (Documented in prose (MIR `Place` docs, `addr_of!` docs, MiniRust's `eval_place` doc); stated here as an equation.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/PlaceUB.lean:154-156
theorem evalPlace_deref_zeroFields (st : State) (x : Local) (pre : List Proj) (k : Nat) :
    evalPlace st ⟨x, pre ++ .deref :: List.replicate k (.field 0)⟩ =
      (evalPlace st ⟨x, pre⟩).bind st.mem.loadPtr := by
-- lean/Toy/PlaceEval/PlaceUB.lean:175-177
theorem evalPlace_append_deref_isSome_iff (st : State) (x : Local) (pre : List Proj) :
    (evalPlace st ⟨x, pre ++ [.deref]⟩).isSome = true ↔
      ∃ q, evalPlace st ⟨x, pre⟩ = some q ∧ DerefLoadOk st.mem q := by
```

Unfolded (prose): Both sides are `Option Ptr`; the right-hand side of `evalPlace_deref_zeroFields` is `(evalPlace st ⟨x, pre⟩).bind st.mem.loadPtr`: no check is applied to the loaded pointer, and each `field 0` step is the identity.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** No hypotheses. `evalPlace_deref_zeroFields_instance` (`k = 2` in `stEx`); `evalPlace_ex_pos_field_one_past_end` shows a result that is not dereferenceable.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L1152–1160 (doc comment of `Place`; `///` markers removed, typos as in the source): "The "validity invariant" of places is the same as that of raw pointers, meaning that e.g. `*ptr` on a dangling or unaligned pointer is never UB. (Later doing a load/store on that place or turning it into a reference can be UB though!) The only ways for a place computation can cause UB are: - On a `Deref` projection, we do an actual load of the inner place, with all the usual consequences (the inner place must be based on an aligned pointer, it must point to allocated memory, the aliasig model must allow reads, this must not be a data race). - For the projections that perform pointer arithmetic, the offset must in-bounds of an allocation (i.e., the preconditions of `ptr::offset` must be met)."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs L2707–2710 (Safety of `addr_of!`; `///` markers removed): "The `expr` in `addr_of!(expr)` is evaluated as a place expression, but never loads from the place or requires the place to be dereferenceable. This means that `addr_of!((*ptr).field)` still requires the projection to `field` to be in-bounds, using the same rules as [`offset`]. However, `addr_of!(*ptr)` is defined behavior even if `ptr` is null, dangling, or misaligned."
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md: L214 "Like a raw pointer, the result can be misaligned or null!" (doc of `eval_place`); L228–235 (`PlaceExpr::Local`: a dead local raises UB "access to a dead local"); L246–263 (`PlaceExpr::Deref`: the operand is evaluated as a value; for safe pointer types the pointer must also be dereferenceable; misalignment is recorded in the place rather than raised); L271–299 (`PlaceExpr::Field`: `ptr_offset_inbounds`); L301–329 (`PlaceExpr::Index`: an index outside the array or slice length raises UB "access to out-of-bounds index", then `ptr_offset_inbounds`); spec/lang/step/operators.md L389–399 (`ptr_offset_inbounds` checks `signed_dereferenceable`).
- [documentation; connection to the toy: derived (modeling bridge)] RFC 2582 (raw reference MIR operator, merged), rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2582-raw-reference-mir-operator.md L44: "No intermediate reference exists, so no invariants have to be adhered to: the pointer may be unaligned and/or dangling."; L211: "which is better, but still UB: we emit a `getelementptr inbounds` for the `.field` offset computation." (said of `&raw mut (*x).field` for a dangling `x`; the RFC predates the zero-offset exemption of `library/core/src/ptr/docs/offset.md`, introduced by rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989).

**Design question.** May a verifier treat `*p` (and `(*p).first` at offset 0) as free of obligations on the pointee when the place is not accessed?

Basis: execution (Lean kernel check) — `evalPlace_deref_zeroFields` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `place-evaluation-ignores-final-pointee`.

#### `place-computation-not-free` (counterexample)

**Plain claim.** Under the deterministic example semantics `SEx`: `placeMention (*(*pp))` with `*pp` uninitialized is UB (`pDerefUninit`: the intermediate pointer load fails); `r := &raw (*p).field 2` with `p` pointing into a freed allocation is UB (`pDanglingRaw 2`); and `r := &raw (*p).field 2` with `p` null is UB (`pNull 2`). Positive control (`place_computation_zero_offset_and_bare_deref_ok`): `r := &raw (*p).field 0` and `placeMention ((*p).field 0)` with `p` pointing into a freed allocation, `placeMention (*p)` and `r := &raw (*p).field 0` with `p` null, and the same two statements with `p` misaligned (with provenance), are UB-free.

**Kind / tier / depth.** counterexample / T0 (Concrete instances of documented rules (MIR `Place` docs, `offset` docs, RFC 2582 L211); a re-derivation in the toy's vocabulary.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:77-80
theorem place_computation_not_free :
    (∀ b, HasBeh SEx pDerefUninit b ↔ b = .wrong []) ∧
    (∀ b, HasBeh SEx (pDanglingRaw 2) b ↔ b = .wrong []) ∧
    (∀ b, HasBeh SEx (pNull 2) b ↔ b = .wrong []) :=
-- lean/Toy/PlaceEval/Erasure.lean:87-91
theorem place_computation_zero_offset_and_bare_deref_ok :
    (∀ b, HasBeh SEx (pDanglingRaw 0) b ↔ b = .term []) ∧
    (∀ b, HasBeh SEx (pDanglingMention 0) b ↔ b = .term []) ∧
    (∀ b, HasBeh SEx (pNull 0) b ↔ b = .term []) ∧
    (∀ b, HasBeh SEx pMisaligned b ↔ b = .term []) :=
```

Unfolded (prose): Each conjunct states the exact behaviour set of a concrete program, e.g. `∀ b, HasBeh SEx pDerefUninit b ↔ b = .wrong []` (UB before any event) or `∀ b, HasBeh SEx (pNull 0) b ↔ b = .term []`.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** Counterexample (concrete programs, fully evaluated).

**Positive control.** `place_computation_zero_offset_and_bare_deref_ok`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L1152–1160 (doc comment of `Place`; `///` markers removed, typos as in the source): "The "validity invariant" of places is the same as that of raw pointers, meaning that e.g. `*ptr` on a dangling or unaligned pointer is never UB. (Later doing a load/store on that place or turning it into a reference can be UB though!) The only ways for a place computation can cause UB are: - On a `Deref` projection, we do an actual load of the inner place, with all the usual consequences (the inner place must be based on an aligned pointer, it must point to allocated memory, the aliasig model must allow reads, this must not be a data race). - For the projections that perform pointer arithmetic, the offset must in-bounds of an allocation (i.e., the preconditions of `ptr::offset` must be met)."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/docs/offset.md L16–19 (Safety of `pointer::offset`): "* If the computed offset is non-zero, then `self` must be [derived from][crate::ptr#provenance] a pointer to some [allocation], and the entire memory range between `self` and `result` (i.e., `min(self.addr(), result)..max(self.addr(), result)`) must be in bounds of that allocation."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs L2707–2710 (Safety of `addr_of!`; `///` markers removed): "The `expr` in `addr_of!(expr)` is evaluated as a place expression, but never loads from the place or requires the place to be dereferenceable. This means that `addr_of!((*ptr).field)` still requires the projection to `field` to be in-bounds, using the same rules as [`offset`]. However, `addr_of!(*ptr)` is defined behavior even if `ptr` is null, dangling, or misaligned."
- [documentation; connection to the toy: derived (modeling bridge)] RFC 2582 (raw reference MIR operator, merged), rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2582-raw-reference-mir-operator.md L44: "No intermediate reference exists, so no invariants have to be adhered to: the pointer may be unaligned and/or dangling."; L211: "which is better, but still UB: we emit a `getelementptr inbounds` for the `.field` offset computation." (said of `&raw mut (*x).field` for a dangling `x`; the RFC predates the zero-offset exemption of `library/core/src/ptr/docs/offset.md`, introduced by rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989).
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989 (pull request #117329, "offset: allow zero-byte offset on arbitrary pointers", merged 2024-05-22); cited in prose for the zero-offset exemption that the toy's `Mem.offsetInbounds` encodes (a zero offset is permitted on every pointer).

**Design question.** Is "place computations are free" a sound simplification for a verifier? (No.)

Basis: execution (Lean kernel check) — `place_computation_not_free` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `place-computation-not-free`.

#### `place-mention-erasure-refines` (theorem)

**Plain claim.** In the toy, under every semantics `S` (fresh addresses, or any static slot assignment), for every program `P`, block `l` and index `i`: if statement `i` of block `l` is `placeMention p`, then deleting it gives a prefix-preserving refinement of `P` (every behaviour of the edited program equals a behaviour of `P` or extends the trace of a UB behaviour of `P`).

**Kind / tier / depth.** theorem / T1 (Instance of the standard fact that deleting a statement whose only possible effect is UB is a behaviour-improving refinement (CompCert's `behavior_improves`; LLVM UB-removing refinement); mechanized here over the toy.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:99-101
theorem erasePlaceMention_refinesPP (S : Sem) (P : Prog) (l : Label) (i : Nat) (p : Place)
    (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    RefinesPP S P (deleteStmt P l i) :=
```

Unfolded (prose): `RefinesPP S P Q` unfolds to `∀ bt, HasBeh S Q bt → ∃ bs, HasBeh S P bs ∧ (bt = bs ∨ ∃ t, bs = .wrong t ∧ bt.HasPrefix t)`; `HasBeh S` quantifies existentially over the allocation oracle. The proof is a simulation: the edited program runs in lockstep with `P`, and `P` executes the deleted `placeMention` as an extra silent step or reaches UB there (`deleteStmt_refinesPP`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some (.placeMention p)` | identifies the deleted statement as a `placeMention` | tight | `deleteStmt_emit_counterexample` (one-block program `pEmitL` under `SEx` whose statement `(0, 0)` is `emit 1`) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `erasePlaceMention_nonvacuous`: `pDerefUninit` at `(0, 2)` satisfies `hs`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/remove_place_mention.rs L1 (module doc, the pass's documented intent; `//!` marker removed): "This pass removes `PlaceMention` statement, which has no effect at codegen."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L387–392 (doc comment of `StatementKind::PlaceMention`; `///` markers removed): "This statement exists to preserve a trace of a scrutinee matched against a wildcard binding. This is especially useful for `let _ = PLACE;` bindings that desugar to a single `PlaceMention(PLACE)`. When executed at runtime, this computes the given place, but then discards it without doing a load. `let _ = *ptr;` is fine even if the pointer is dangling."
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/statements.md L44–46: "This is what `let _ = place;` compiles to. The place expression is still evaluated (so e.g. projections in there must be in-bounds), but no load occurs. This means `let _ = *danling_ptr;` is legal."; L48–55 (`Statement::PlaceMention` evaluates the place and discards it).
- CompCert, AbsInt/CompCert 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: "Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2." (`beh1` is the source behaviour); `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814 (behaviour-improvement refinement for a verified compiler; the improvement relation here is CompCert's, prefix-preserving).
- Juneyoung Lee et al., "Taming Undefined Behavior in LLVM", PLDI 2017, DOI 10.1145/3062341.3062343 (refinement that may remove UB, for compiler transformations).

**Design question.** May an optimizer or a verification pipeline delete `PlaceMention` statements, and in which direction do properties transfer?

Basis: execution (Lean kernel check) — `erasePlaceMention_refinesPP` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `place-mention-erasure-refines`.

#### `place-mention-erasure-equivalence-sufficient-condition` (theorem)

**Plain claim.** In the toy, under every semantics `S`, for every program `P`: if statement `i` of block `l` is `placeMention p` and evaluating `p` succeeds in every state in which `(l, i)` is reachable, then deleting the statement is a prefix-preserving equivalence (refinement in both directions).

**Kind / tier / depth.** theorem / T1 (The standard erasure pattern (deleting a statement whose UB condition never holds on reachable states is an equivalence), stated over the toy; folklore made precise and mechanized.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:107-110
theorem erasePlaceMention_equivPP_of_evalPlace_reachable (S : Sem) (P : Prog) (l : Label)
    (i : Nat) (p : Place) (hs : (P.blk l).stmts[i]? = some (.placeMention p))
    (hok : ∀ st, ReachableAt S P l i st → (evalPlace st p).isSome = true) :
    EquivPP S P (deleteStmt P l i) :=
```

Unfolded (prose): `EquivPP S P Q` is `RefinesPP S P Q ∧ RefinesPP S Q P`. The reverse direction is a simulation in which `P`'s execution of the `placeMention` is matched by no step of the edited program; `hok` excludes its failure at every state the run of `P` reaches (`deleteStmt_rev_refinesPP`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some (.placeMention p)` | identifies the deleted statement as a `placeMention` | tight | `erasePlaceMention_equiv_hs_counterexample` (`pEmitL` under `SEx`: a one-statement program whose deleted statement is `emit 1`; evaluation of `⟨0, []⟩` succeeds at every reachable state at `(0, 0)` and deleting the statement is not an equivalence) |
| `hok : ∀ st, ReachableAt S P l i st → (evalPlace st p).isSome = true` | excludes place-evaluation UB at the deleted statement | tight | `erasePlaceMention_equiv_hok_counterexample` (`pDerefUninit` under `SEx`: the deleted `placeMention (*(*pp))` with `*pp` uninitialized; the source reaches UB, the edited program terminates (`erasePlaceMention_erases_place_ub`)) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `erasePlaceMention_equiv_nonvacuous`: `pDanglingMention 0` at `(0, 3)` under `SEx` (the place `(*p).field 0` evaluates at every reachable state although `p` dangles).

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/remove_place_mention.rs L1 (module doc, the pass's documented intent; `//!` marker removed): "This pass removes `PlaceMention` statement, which has no effect at codegen."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L387–392 (doc comment of `StatementKind::PlaceMention`; `///` markers removed): "This statement exists to preserve a trace of a scrutinee matched against a wildcard binding. This is especially useful for `let _ = PLACE;` bindings that desugar to a single `PlaceMention(PLACE)`. When executed at runtime, this computes the given place, but then discards it without doing a load. `let _ = *ptr;` is fine even if the pointer is dangling."
- CompCert, AbsInt/CompCert 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: "Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2." (`beh1` is the source behaviour); `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814 (behaviour-improvement refinement for a verified compiler; the improvement relation here is CompCert's, prefix-preserving).

**Design question.** Under what checkable condition does deleting a `PlaceMention` lose no UB?

Basis: execution (Lean kernel check) — `erasePlaceMention_equivPP_of_evalPlace_reachable` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `place-mention-erasure-equivalence-sufficient-condition`.

#### `place-mention-erasure-equivalence-exact-condition-static-slots` (characterization)

**Plain claim.** In the toy, under the deterministic semantics `slots s` for every slot assignment `s`, for every program `P`: if statement `i` of block `l` is `placeMention p`, then deleting it is a prefix-preserving equivalence iff, for every reachable state at `(l, i)` in which evaluating `p` is UB, the run of the edited program from the point after the deleted statement reaches UB before emitting any event.

**Kind / tier / depth.** characterization / T1 (Folklore made precise: the exact condition is a continuation condition (the edited program reaches UB from the point after the edit before any event), stated for a deterministic semantics and mechanized.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:121-125
theorem erasePlaceMention_equivPP_iff_slots (s : Local → Nat) (P : Prog) (l : Label)
    (i : Nat) (p : Place) (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    EquivPP (.slots s) P (deleteStmt P l i) ↔
      ∀ st, ReachableAt (.slots s) P l i st → evalPlace st p = none →
        GoesWrongFrom (.slots s) (deleteStmt P l i) ((deleteStmt P l i).at l i st) [] := by
```

Unfolded (prose): `GoesWrongFrom (.slots s) Q c []` is `∃ ω n, run (.slots s) Q n c = .ub []`; the start point is `Q.at l i st`, i.e. block `l` of the edited program from index `i` (the statements after the deleted one).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some (.placeMention p)` | identifies the deleted statement as a `placeMention` | tight | `erasePlaceMention_iff_hs_counterexample` (`pEmitL` under `SEx`: the deleted statement is `emit 1`; the right-hand side holds (evaluation never fails) while the equivalence fails, so the biconditional is false) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** Both sides true: `erasePlaceMention_equivPP_despite_reachable_failure`; both sides false: `erasePlaceMention_erases_place_ub`; `hs` holds for `pDerefUninit` at `(0, 2)` (`erasePlaceMention_nonvacuous`).

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/remove_place_mention.rs L1 (module doc, the pass's documented intent; `//!` marker removed): "This pass removes `PlaceMention` statement, which has no effect at codegen."
- CompCert, AbsInt/CompCert 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: "Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2." (`beh1` is the source behaviour); `ImprovesPP bt bs` is this relation with `bs` as `beh1`.

**Design question.** When exactly is deleting a `PlaceMention` a prefix-preserving equivalence (`EquivPP`) under a deterministic semantics?

Basis: execution (Lean kernel check) — `erasePlaceMention_equivPP_iff_slots` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `place-mention-erasure-equivalence-exact-condition-static-slots`.

#### `place-mention-erasure-equivalence-despite-reachable-failure` (counterexample)

**Plain claim.** Under `SEx`, in `pTwoMentions` (two identical statements `placeMention (*(*pp))` with `*pp` uninitialized) evaluation of the first fails at a reachable state, yet deleting it is a prefix-preserving equivalence: both programs reach UB before any event (`pTwoMentions_beh`, `pTwoMentions_erased_beh`), the edited one at the second statement. So place-evaluation UB-freedom at the erased point is sufficient for equivalence but not necessary.

**Kind / tier / depth.** counterexample / T0 (A concrete instance of a known phenomenon (a later identical UB can mask the deleted one); re-derived in the toy.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:173-175
theorem erasePlaceMention_equivPP_despite_reachable_failure :
    (∃ st, ReachableAt SEx pTwoMentions 0 2 st ∧ evalPlace st ⟨0, [.deref, .deref]⟩ = none) ∧
      EquivPP SEx pTwoMentions (deleteStmt pTwoMentions 0 2) := by
```

Unfolded (prose): The first conjunct exhibits a state `stTwoMentions` with `ReachableAt SEx pTwoMentions 0 2 stTwoMentions` and a failing evaluation; the second is `EquivPP SEx pTwoMentions (deleteStmt pTwoMentions 0 2)`.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** Counterexample (concrete program).

**Prior art.**

- Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814 (behaviour-improvement refinement for a verified compiler; the improvement relation here is CompCert's, prefix-preserving).

**Design question.** Is "place evaluation is UB-free wherever the `PlaceMention` executes" necessary? (No.)

Basis: execution (Lean kernel check) — `erasePlaceMention_equivPP_despite_reachable_failure` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Non-claims: see **Boundaries**, *Non-claims*, `place-mention-erasure-equivalence-despite-reachable-failure`.

#### `ub-check-after-erasure-incomplete` (counterexample)

**Plain claim.** Under `SEx`, `pDerefUninit` with its `placeMention` (statement `(0, 2)`) deleted is UB-free while `pDerefUninit` is not, so every exact UB checker for `SEx` (a Boolean function `chk` with `chk P = true ↔ UBFree SEx P`; such checkers exist noncomputably, `exactUBChecker_exists`) accepts the edited program (`ubCheck_after_erasePlaceMention_misses_place_ub`). Under fresh addresses, every exact UB checker for `.fresh` accepts `pStale` with the markers of local `0` erased, although `pStale` (a read of `x` after a re-`storageLive`) is not UB-free (`ubCheck_after_eraseMarkers_misses_stale_read`).

**Kind / tier / depth.** counterexample / T0 (Concrete instances of the known fact that a UB check of a refined (UB-erasing) program does not transfer back to the source; re-derived in the toy.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:205-208
theorem ubCheck_after_erasePlaceMention_misses_place_ub :
    (pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) ∧
      UBFree SEx (deleteStmt pDerefUninit 0 2) ∧ ¬ UBFree SEx pDerefUninit ∧
      ∀ chk, ExactUBChecker SEx chk → chk (deleteStmt pDerefUninit 0 2) = true := by
-- lean/Toy/PlaceEval/Markers.lean:374-376
theorem ubCheck_after_eraseMarkers_misses_stale_read :
    ∀ chk, ExactUBChecker .fresh chk →
      chk (eraseMarkers pStale 0) = true ∧ ¬ UBFree .fresh pStale := by
-- lean/Toy/PlaceEval/Semantics.lean:191
def ExactUBChecker (S : Sem) (chk : Prog → Bool) : Prop := ∀ P, chk P = true ↔ UBFree S P
-- lean/Toy/PlaceEval/RunLemmas.lean:248
theorem exactUBChecker_exists (S : Sem) : ∃ chk, ExactUBChecker S chk := by
```

Unfolded (prose): `UBFree S P` is `∀ t, ¬ HasBeh S P (.wrong t)`; `ExactUBChecker S chk` is `∀ P, chk P = true ↔ UBFree S P`.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** Counterexamples; exact checkers exist for every semantics (`exactUBChecker_exists`), so the universally quantified checker is not vacuous.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L364–381 (doc comment of `StatementKind::StorageLive`/`StorageDead`; `///` markers removed): "`StorageLive` and `StorageDead` statements mark the live range of a local. At any point during the execution of a function, each local is either allocated or unallocated. Except as noted below, all locals except function parameters are initially unallocated. `StorageLive` statements cause memory to be allocated for the local while `StorageDead` statements cause the memory to be freed. In other words, `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for stack-allocated local variables. Using a local in any way (not only reading/writing from it) while it is unallocated is UB. Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body. These locals are implicitly allocated for the full duration of the function. There is a convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for computing these locals. If the local is already allocated, calling `StorageLive` again will implicitly free the local and then allocate fresh uninitialized memory. If a local is already deallocated, calling `StorageDead` again is a NOP."
- Juneyoung Lee et al., "Taming Undefined Behavior in LLVM", PLDI 2017, DOI 10.1145/3062341.3062343 (refinement that may remove UB, for compiler transformations).

**Design question.** Does a UB check run after `PlaceMention` erasure or storage-marker erasure find UB of the source? (No: place-evaluation UB at the erased statement and stale reads are missed.)

Basis: execution (Lean kernel check) — `ubCheck_after_erasePlaceMention_misses_place_ub`, `ubCheck_after_eraseMarkers_misses_stale_read` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `ub-check-after-erasure-incomplete`.

#### `ub-check-after-place-mention-erasure-complete-outside-place-ub` (theorem)

**Plain claim.** In the toy, under every semantics `S`, for every program `P`: if statement `i` of block `l` is `placeMention p`, evaluating `p` succeeds at every reachable state at `(l, i)`, and the program with that statement deleted is UB-free, then `P` is UB-free. Equivalently, if the edited program is UB-free and `P` is not, some reachable state at `(l, i)` has a failing evaluation of `p`.

**Kind / tier / depth.** theorem / T0 (Corollary of the sufficient condition and of the standard reverse-refinement argument (UB-freedom transfers backwards along a refinement); re-derived in the toy.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:219-222
theorem ubFree_of_ubFree_erasePlaceMention_of_evalPlace_reachable (S : Sem) (P : Prog)
    (l : Label) (i : Nat) (p : Place) (hs : (P.blk l).stmts[i]? = some (.placeMention p))
    (hok : ∀ st, ReachableAt S P l i st → (evalPlace st p).isSome = true)
    (htgt : UBFree S (deleteStmt P l i)) : UBFree S P :=
```

Unfolded (prose): Proved from `erasePlaceMention_equivPP_of_evalPlace_reachable` and `ubFree_of_refinesPP_rev`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some (.placeMention p)` | identifies the deleted statement as a `placeMention` | tight | `deleteStmt_ubAssign_counterexample` (`pUBAssign` under `SEx`: the deleted statement is an assignment that reads an uninitialized local) |
| `hok : ∀ st, ReachableAt S P l i st → (evalPlace st p).isSome = true` | excludes place-evaluation UB at the erased statement | tight | `ubCheck_after_erasePlaceMention_misses_place_ub` (`pDerefUninit` under `SEx`: the edited program is UB-free, the source is not) |
| `htgt : UBFree S (deleteStmt P l i)` | the verdict being transferred (UB-freedom of the edited program) | tight | `ubFree_erasePlaceMention_htgt_counterexample` (`pMentionUnreach` under `SEx`: a valid `placeMention` followed by `unreachable`; `hs` and `hok` hold and the program is not UB-free) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `ubFree_erasePlaceMention_nonvacuous`: `pDanglingMention 0` at `(0, 3)` under `SEx`.

**Prior art.**

- Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814 (behaviour-improvement refinement for a verified compiler; the improvement relation here is CompCert's, prefix-preserving).

**Design question.** Which UB does a check after `PlaceMention` erasure miss? (Place-evaluation UB at the erased statement.)

Basis: execution (Lean kernel check) — `ubFree_of_ubFree_erasePlaceMention_of_evalPlace_reachable` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Non-claims: see **Boundaries**, *Non-claims*, `ub-check-after-place-mention-erasure-complete-outside-place-ub`.

#### `switch-operand-ub-conditions` (characterization)

**Plain claim.** In the toy, for every state `st`, place `p` and type `τ`, the operand `copy p τ` fails to evaluate to an integer iff evaluating `p` fails (`evalPlace_eq_none_iff`), or the resulting pointer `q` is not dereferenceable for `τ.size` bytes, or is not aligned for `τ.align`, or its cells do not decode to an integer at `τ`. At an enum type the cells decode to `n` iff they are bytes encoding `n` and `n` is a valid tag (`decode_enum_eq_some_iff`); at an integer type, iff they are bytes encoding `n` (`decode_int_eq_some_iff`), each byte contributing `b % 256` (Nat remainder); an uninitialized cell or a pointer fragment never decodes via `decodeLE`. Degenerate edges: if `τ.size = 0`, then every pointer, including null, is dereferenceable for `τ.size` bytes (`dereferenceable_of_size_eq_zero`), the cells read form the empty list (`readCells_of_size_eq_zero`), and they decode at `τ` to the integer `n` iff `n = 0` and, when `τ` is an enum type `Ty.enum s a valid`, `0 ∈ valid` (`decode_readCells_of_size_eq_zero_iff`); instances in `mEx`: a zero-size read through null succeeds with `0` at `Ty.int 0 1` (`load_ex_pos_zero_size_null`) and at `Ty.enum 0 1 [0]` (`load_ex_pos_zero_size_enum`), and fails at `Ty.enum 0 1 [1]`, whose valid tags exclude `0` (`load_ex_neg_zero_size_enum`); for `τ.align = 0` exactly address `0` is aligned (`aligned_zero_ex_pos`, `aligned_zero_ex_neg`).

**Kind / tier / depth.** characterization / T0 (A definitional unfolding of documented rules (copy semantics; validity of integers and enum tags); a reference point for the switch cards.) / definitional.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:257-262
theorem evalInt_copy_eq_none_iff (st : State) (p : Place) (τ : Ty) :
    (Operand.copy p τ).evalInt st = none ↔
      evalPlace st p = none ∨
        ∃ q, evalPlace st p = some q ∧
          (st.mem.dereferenceable q τ.size = false ∨ aligned τ.align q.addr = false ∨
            ∀ n, τ.decode (st.mem.readCells q.addr τ.size) ≠ some (.int n)) := by
-- lean/Toy/PlaceEval/Erasure.lean:236-237
theorem decode_enum_eq_some_iff (s a : Nat) (valid : List Nat) (cs : List Cell) (n : Nat) :
    (Ty.enum s a valid).decode cs = some (.int n) ↔ decodeLE cs = some n ∧ n ∈ valid := by
-- lean/Toy/PlaceEval/Erasure.lean:229-230
theorem decode_int_eq_some_iff (s a : Nat) (cs : List Cell) (n : Nat) :
    (Ty.int s a).decode cs = some (.int n) ↔ decodeLE cs = some n := by
```

Unfolded (prose): Little-endian decoding uses `b % 256` per byte (Nat remainder); `decodeLE` fails on any cell that is not a byte.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** No hypotheses. `evalInt_copy_instance`: in `stEx` local `0` holds pointer fragments, so reading it at `bool2` fails.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/terminators.md L34–48 (`Terminator::Switch` evaluates its value expression, then jumps).
- reference corpus package `undefined-values-poison-undef-freeze-and-refinement`, cards `source-ub-refined-by-anything` and `poison-refines-eager-uninit` (value-level reads of uninitialized data; the toy here uses the eager reading: reading an uninitialized byte at an integer, pointer or enum type is UB).
- reference corpus package `enum-niche-layout-guarantees-and-validity-invariants`, card `nicheLayout_lawful_iff_isNiche` (validity sets of enum representations); the toy's `Ty.enum` validity is a finite list of valid tags.
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md L104–128 (`ValueExpr::GetDiscriminant`, paraphrase): reading the discriminant of an enum is a separate value expression that loads only the bytes the discriminator touches.

**Design question.** What must hold for the read performed by a `switchInt` operand to be UB-free?

Basis: execution (Lean kernel check) — `evalInt_copy_eq_none_iff` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `switch-operand-ub-conditions`.

#### `equal-target-switch-erasure-refines` (theorem)

**Plain claim.** In the toy, under every semantics `S`, for every program `P`: if block `l` ends in `switchInt o arms b` and every arm targets `b`, then replacing that terminator by `goto b` gives a prefix-preserving refinement of `P`.

**Kind / tier / depth.** theorem / T1 (Documented as a transformation that may remove UB-causing reads (rustc `simplify.rs` comment at L309); a standard UB-removing refinement, mechanized over the toy.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:284-287
theorem switchToGoto_refinesPP (S : Sem) (P : Prog) (l : Label) (o : Operand)
    (arms : List (Nat × Label)) (b : Label) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b) :
    RefinesPP S P (setTerm P l (.goto b)) :=
```

Unfolded (prose): `setTerm P l (.goto b)` replaces the terminator of block `l` and keeps its statements.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `ht : (P.blk l).term = .switchInt o arms b` | identifies the replaced terminator as the switch | tight | `setTerm_nonSwitch_counterexample` (`pHaltEmit` under `SEx`: block `0` ends in `halt`, arms `[]`) |
| `hall : ∀ a ∈ arms, a.2 = b` | every arm targets the `otherwise` label `b` | tight | `switchToGoto_differentTargets_counterexample` (`pSwDiff` under `SEx`: arm `0 → 1`, `otherwise` `2`) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `switchToGoto_nonvacuous`: `pSwUninit` at block `0`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/simplify.rs L307 (comment on `simplify_branch`; `//` marker removed): "turn a branch with all successors identical to a goto"; and (paraphrase, not a quote) the first clause of the comment sentence at L309 states that removing a `SwitchInt` terminator may remove reads that result in UB.
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/terminators.md L34–48 (`Terminator::Switch` evaluates its value expression, then jumps).
- CompCert, AbsInt/CompCert 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: "Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2." (`beh1` is the source behaviour); `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- Juneyoung Lee et al., "Taming Undefined Behavior in LLVM", PLDI 2017, DOI 10.1145/3062341.3062343 (refinement that may remove UB, for compiler transformations).

**Design question.** May an equal-target `SwitchInt` be turned into a `Goto`?

Basis: execution (Lean kernel check) — `switchToGoto_refinesPP` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `equal-target-switch-erasure-refines`.

#### `equal-target-switch-erasure-equivalence-sufficient-condition` (theorem)

**Plain claim.** In the toy, under every semantics `S`, for every program `P`: if block `l` ends in `switchInt o arms b`, every arm targets `b`, and `o` evaluates to an integer in every reachable state at the switch (for `o = copy p τ`: place evaluation succeeds and the read is a valid integer, or a valid tag for an enum type, `switch-operand-ub-conditions`), then replacing the switch by `goto b` is a prefix-preserving equivalence.

**Kind / tier / depth.** theorem / T1 (The standard erasure pattern for a terminator whose UB condition never holds on reachable states, stated over the toy; folklore made precise and mechanized.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:293-297
theorem switchToGoto_equivPP_of_operand_reachable (S : Sem) (P : Prog) (l : Label)
    (o : Operand) (arms : List (Nat × Label)) (b : Label)
    (ht : (P.blk l).term = .switchInt o arms b) (hall : ∀ a ∈ arms, a.2 = b)
    (hok : ∀ st, ReachableAt S P l (P.blk l).stmts.length st → (o.evalInt st).isSome = true) :
    EquivPP S P (setTerm P l (.goto b)) :=
```

Unfolded (prose): The switch point is `(l, (P.blk l).stmts.length)`, after the last statement of block `l`. The reverse direction is a lockstep simulation; `hok` excludes a failing operand at every state the run of `P` reaches (`setTerm_rev_refinesPP`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `ht : (P.blk l).term = .switchInt o arms b` | identifies the replaced terminator as the switch | tight | `switchToGoto_equiv_ht_counterexample` (`pHaltEmit` under `SEx`: a `halt` terminator replaced by `goto 1` (arms `[]`, constant operand)) |
| `hall : ∀ a ∈ arms, a.2 = b` | all arms target the `otherwise` label | tight | `switchToGoto_equiv_hall_counterexample` (`pSwDiff` under `SEx`: the arm `0 → 1` differs from the `otherwise` label `2`) |
| `hok : ∀ st, ReachableAt S P l (P.blk l).stmts.length st → (o.evalInt st).isSome = true` | excludes operand UB at the switch | tight | `switchToGoto_equiv_hok_counterexample` (`pSwUninit` under `SEx`: the operand is an uninitialized one-byte integer) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `switchToGoto_equiv_nonvacuous`: `pSwTag 1` (tag `1` valid) under `SEx`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/simplify.rs L307 (comment on `simplify_branch`; `//` marker removed): "turn a branch with all successors identical to a goto"; and (paraphrase, not a quote) the first clause of the comment sentence at L309 states that removing a `SwitchInt` terminator may remove reads that result in UB.
- reference corpus package `enum-niche-layout-guarantees-and-validity-invariants`, card `nicheLayout_lawful_iff_isNiche` (validity sets of enum representations); the toy's `Ty.enum` validity is a finite list of valid tags.
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md L104–128 (`ValueExpr::GetDiscriminant`, paraphrase): reading the discriminant of an enum is a separate value expression that loads only the bytes the discriminator touches.

**Design question.** Under what condition does switch-to-goto lose no UB, in particular for enum discriminants?

Basis: execution (Lean kernel check) — `switchToGoto_equivPP_of_operand_reachable` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `equal-target-switch-erasure-equivalence-sufficient-condition`.

#### `equal-target-switch-erasure-equivalence-exact-condition-static-slots` (characterization)

**Plain claim.** In the toy, under the deterministic semantics `slots s` for every slot assignment `s`, for every program `P`: if block `l` ends in `switchInt o arms b` and every arm targets `b`, then replacing the switch by `goto b` is a prefix-preserving equivalence iff, for every reachable state at the switch in which `o` does not evaluate to an integer, the run of the edited program from the entry of `b` reaches UB before emitting any event.

**Kind / tier / depth.** characterization / T1 (Folklore made precise: the exact condition is a continuation condition (the edited program reaches UB from the entry of `b` before any event), stated for a deterministic semantics and mechanized.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:307-312
theorem switchToGoto_equivPP_iff_slots (s : Local → Nat) (P : Prog) (l : Label)
    (o : Operand) (arms : List (Nat × Label)) (b : Label)
    (ht : (P.blk l).term = .switchInt o arms b) (hall : ∀ a ∈ arms, a.2 = b) :
    EquivPP (.slots s) P (setTerm P l (.goto b)) ↔
      ∀ st, ReachableAt (.slots s) P l (P.blk l).stmts.length st → o.evalInt st = none →
        GoesWrongFrom (.slots s) (setTerm P l (.goto b)) ((setTerm P l (.goto b)).entry b st) [] := by
```

Unfolded (prose): `GoesWrongFrom (.slots s) Q (Q.entry b st) []` with `Q = setTerm P l (.goto b)`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `ht : (P.blk l).term = .switchInt o arms b` | identifies the replaced terminator as the switch | tight | `switchToGoto_iff_ht_counterexample` (`pHaltEmit` under `SEx`: a `halt` terminator replaced by `goto 1`; the right-hand side holds (the constant operand always evaluates) while the equivalence fails) |
| `hall : ∀ a ∈ arms, a.2 = b` | all arms target the `otherwise` label | tight | `switchToGoto_iff_hall_counterexample` (`pSwDiff` under `SEx`: the operand always evaluates, so the right-hand side holds, while the equivalence fails) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** Hypotheses: `switchToGoto_nonvacuous` (`pSwUninit` at block `0`). Both sides false: `switchToGoto_erases_operand_ub`; both sides true: `switchToGoto_validTag_equivPP`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/simplify.rs L307 (comment on `simplify_branch`; `//` marker removed): "turn a branch with all successors identical to a goto"; and (paraphrase, not a quote) the first clause of the comment sentence at L309 states that removing a `SwitchInt` terminator may remove reads that result in UB.

**Design question.** When exactly is replacing an equal-target `SwitchInt` by a `Goto` a prefix-preserving equivalence (`EquivPP`) under a deterministic semantics?

Basis: execution (Lean kernel check) — `switchToGoto_equivPP_iff_slots` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `equal-target-switch-erasure-equivalence-exact-condition-static-slots`.

#### `raw-and-shared-reference-ub-conditions` (characterization)

**Plain claim.** In the toy, for every state `st`, place `p` and layout `L`: `&raw p` fails to evaluate iff evaluating `p` fails (`rawRef_eval_eq_none_iff`); `&p` with pointee layout `L` fails iff evaluating `p` fails or the resulting pointer `q` violates `RefOk` (`q` has address `0`, i.e. `q.addr = 0` regardless of provenance, or is not aligned for `L.align`, or is not dereferenceable for `L.size` bytes) (`ref_eval_eq_none_iff`).

**Kind / tier / depth.** characterization / T0 (A definitional re-derivation of documented rules (`addr_of!` docs, RFC 2582, the Reference); a reference point for the rewrite cards.) / definitional.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:388-390
theorem ref_eval_eq_none_iff (st : State) (p : Place) (L : Layout) :
    (Rvalue.ref p L).eval st = none ↔
      evalPlace st p = none ∨ ∃ q, evalPlace st p = some q ∧ ¬ RefOk st.mem q L := by
-- lean/Toy/PlaceEval/Erasure.lean:381-382
theorem rawRef_eval_eq_none_iff (st : State) (p : Place) :
    (Rvalue.rawRef p).eval st = none ↔ evalPlace st p = none := by
-- lean/Toy/PlaceEval/Lang.lean:141-142
def RefOk (m : Mem) (q : Ptr) (L : Layout) : Prop :=
  q.addr ≠ 0 ∧ aligned L.align q.addr = true ∧ m.dereferenceable q L.size = true
```

Unfolded (prose): `RefOk m q L` is `q.addr ≠ 0 ∧ aligned L.align q.addr = true ∧ m.dereferenceable q L.size = true`.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** No hypotheses. `ref_eval_instance`: in `stEx`, `&raw (*l0).field 1` evaluates to the odd address `7` while `&(*l0).field 1` at a 2-aligned pointee fails.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs L2707–2710 (Safety of `addr_of!`; `///` markers removed): "The `expr` in `addr_of!(expr)` is evaluated as a place expression, but never loads from the place or requires the place to be dereferenceable. This means that `addr_of!((*ptr).field)` still requires the projection to `field` to be in-bounds, using the same rules as [`offset`]. However, `addr_of!(*ptr)` is defined behavior even if `ptr` is null, dangling, or misaligned."
- [documentation; connection to the toy: derived (modeling bridge)] RFC 2582 (raw reference MIR operator, merged), rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2582-raw-reference-mir-operator.md L44: "No intermediate reference exists, so no invariants have to be adhered to: the pointer may be unaligned and/or dangling."; L211: "which is better, but still UB: we emit a `getelementptr inbounds` for the `.field` offset computation." (said of `&raw mut (*x).field` for a dangling `x`; the RFC predates the zero-offset exemption of `library/core/src/ptr/docs/offset.md`, introduced by rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989).
- [documentation; connection to the toy: derived (modeling bridge)] The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L152: "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be [dangling], and it must point to a valid value (in case of dynamically sized types, using the actual dynamic type of the pointee as determined by the [metadata]). Note that the last point (about pointing to a valid value) remains a subject of some debate."; L94: "`&`/`&mut` on a place requires the alignment of the field type (or else the program would be "producing an invalid value"), which generally is a less restrictive requirement than being based on an aligned pointer."; L83: "A place is said to be "based on a misaligned pointer" if the last `*` projection during place computation was performed on a pointer that was not aligned for its type. (If there is no `*` projection in the place expression, then this is accessing the field of a local or `static` and rustc will guarantee proper alignment. If there are multiple `*` projections, then each of them incurs a load of the pointer-to-be-dereferenced itself from memory, and each of these loads is subject to the alignment constraint. Note that some `*` projections can be omitted in surface Rust syntax due to automatic dereferencing; we are considering the fully expanded place expression here.)"
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md: L214 "Like a raw pointer, the result can be misaligned or null!" (doc of `eval_place`); L228–235 (`PlaceExpr::Local`: a dead local raises UB "access to a dead local"); L246–263 (`PlaceExpr::Deref`: the operand is evaluated as a value; for safe pointer types the pointer must also be dereferenceable; misalignment is recorded in the place rather than raised); L271–299 (`PlaceExpr::Field`: `ptr_offset_inbounds`); L301–329 (`PlaceExpr::Index`: an index outside the array or slice length raises UB "access to out-of-bounds index", then `ptr_offset_inbounds`); spec/lang/step/operators.md L389–399 (`ptr_offset_inbounds` checks `signed_dereferenceable`).
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md L170–173 (`ValueExpr::AddrOf`): "        // Let the aliasing model know.
          let lookup = self.vtable_lookup();
          let ptr = self.mutate_cur_frame(|frame, mem| {
              mem.retag_ptr(&mut frame.extra, place.ptr, ptr_ty, /* fn_entry */ false, /* fn_implicit_writes */ true, lookup)"
- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer, "Stacked Borrows: An Aliasing Model for Rust", POPL 2020, DOI 10.1145/3371109 (creating a reference retags the pointer; not modelled here).

**Design question.** How do `&raw` and `&` of a place differ in their UB conditions?

Basis: execution (Lean kernel check) — `ref_eval_eq_none_iff` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `raw-and-shared-reference-ub-conditions`.

#### `reference-to-raw-rewrite-refines` (theorem)

**Plain claim.** In the toy, under every semantics `S`, for every program `P`: if statement `i` of block `l` is `dst := &p` at type `τ` with pointee layout `L`, then replacing it by `dst := &raw p` gives a prefix-preserving refinement of `P`.

**Kind / tier / depth.** theorem / T0 (Folklore (dropping a validity assertion is a refinement), re-derived over the toy and mechanized.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:399-401
theorem refToRaw_refinesPP (S : Sem) (P : Prog) (l : Label) (i : Nat) (dst : Place) (τ : Ty)
    (p : Place) (L : Layout) (hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))) :
    RefinesPP S P (setStmt P l i (.assign dst τ (.rawRef p))) :=
```

Unfolded (prose): `setStmt P l i s` replaces statement `i` of block `l`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))` | identifies the replaced statement as a reference creation | tight | `setStmt_nonRef_counterexample` (`pEmitL` under `SEx`: replacing `emit 1` by `x := &raw x`) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `refToRaw_nonvacuous`: `pRefDangling` at `(0, 3)`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, library/core/src/ptr/mod.rs L2707–2710 (Safety of `addr_of!`; `///` markers removed): "The `expr` in `addr_of!(expr)` is evaluated as a place expression, but never loads from the place or requires the place to be dereferenceable. This means that `addr_of!((*ptr).field)` still requires the projection to `field` to be in-bounds, using the same rules as [`offset`]. However, `addr_of!(*ptr)` is defined behavior even if `ptr` is null, dangling, or misaligned."
- [documentation; connection to the toy: derived (modeling bridge)] RFC 2582 (raw reference MIR operator, merged), rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2582-raw-reference-mir-operator.md L44: "No intermediate reference exists, so no invariants have to be adhered to: the pointer may be unaligned and/or dangling."; L211: "which is better, but still UB: we emit a `getelementptr inbounds` for the `.field` offset computation." (said of `&raw mut (*x).field` for a dangling `x`; the RFC predates the zero-offset exemption of `library/core/src/ptr/docs/offset.md`, introduced by rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989).
- CompCert, AbsInt/CompCert 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v L81–82: "Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2." (`beh1` is the source behaviour); `ImprovesPP bt bs` is this relation with `bs` as `beh1`.
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/expressions.md L170–173 (`ValueExpr::AddrOf`): "        // Let the aliasing model know.
          let lookup = self.vtable_lookup();
          let ptr = self.mutate_cur_frame(|frame, mem| {
              mem.retag_ptr(&mut frame.extra, place.ptr, ptr_ty, /* fn_entry */ false, /* fn_implicit_writes */ true, lookup)"
- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer, "Stacked Borrows: An Aliasing Model for Rust", POPL 2020, DOI 10.1145/3371109 (creating a reference retags the pointer; not modelled here).

**Design question.** Which direction of the `&` / `&raw` rewrite is a sound refinement, and does it preserve UB for verification?

Basis: execution (Lean kernel check) — `refToRaw_refinesPP` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `reference-to-raw-rewrite-refines`.

#### `raw-and-shared-reference-rewrites-not-equivalences` (counterexample)

**Plain claim.** Under `SEx`: rewriting `r := &raw (*p)` to `r := &(*p)` (pointee layout `⟨4, 2⟩`) for `p` pointing into a freed allocation (`pRawDangling`), and rewriting `r := &raw (s.b)` to `r := &(s.b)` for the 2-aligned field at offset 1 of a packed 3-byte local (`pRawPacked`), are not refinements (each introduces UB: `pRawDangling_beh`, `pRefDangling_beh`, `pRawPacked_beh`, `pRawPacked_ref_beh`); rewriting `r := &(*p)` to `r := &raw (*p)` in `pRefDangling` is a refinement but not an equivalence (it erases UB). So neither rewrite is an equivalence in either direction.

**Kind / tier / depth.** counterexample / T0 (Concrete instances of documented rules (RFC 2582; the Reference's packed-field note); re-derived in the toy.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Erasure.lean:408-412
theorem raw_ref_rewrites_not_equivalences :
    ¬ RefinesPP SEx pRawDangling (setStmt pRawDangling 0 3 refDerefStmt) ∧
    ¬ RefinesPP SEx pRawPacked (setStmt pRawPacked 0 0 refPackedStmt) ∧
    RefinesPP SEx pRefDangling (setStmt pRefDangling 0 3 rawDerefStmt) ∧
    ¬ RefinesPP SEx (setStmt pRefDangling 0 3 rawDerefStmt) pRefDangling := by
```

Unfolded (prose): Conjunction of `¬ RefinesPP`, `¬ RefinesPP`, `RefinesPP`, `¬ RefinesPP` facts on concrete programs.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** Counterexample (concrete programs).

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] RFC 2582 (raw reference MIR operator, merged), rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2582-raw-reference-mir-operator.md L44: "No intermediate reference exists, so no invariants have to be adhered to: the pointer may be unaligned and/or dangling."; L211: "which is better, but still UB: we emit a `getelementptr inbounds` for the `.field` offset computation." (said of `&raw mut (*x).field` for a dangling `x`; the RFC predates the zero-offset exemption of `library/core/src/ptr/docs/offset.md`, introduced by rust-lang/rust merge commit 5d328a1f62fe7c9d3a31d14b88dfa13310b7c989).
- [documentation; connection to the toy: derived (modeling bridge)] The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L152: "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be [dangling], and it must point to a valid value (in case of dynamically sized types, using the actual dynamic type of the pointee as determined by the [metadata]). Note that the last point (about pointing to a valid value) remains a subject of some debate."; L94: "`&`/`&mut` on a place requires the alignment of the field type (or else the program would be "producing an invalid value"), which generally is a less restrictive requirement than being based on an aligned pointer."; L83: "A place is said to be "based on a misaligned pointer" if the last `*` projection during place computation was performed on a pointer that was not aligned for its type. (If there is no `*` projection in the place expression, then this is accessing the field of a local or `static` and rustc will guarantee proper alignment. If there are multiple `*` projections, then each of them incurs a load of the pointer-to-be-dereferenced itself from memory, and each of these loads is subject to the alignment constraint. Note that some `*` projections can be omitted in surface Rust syntax due to automatic dereferencing; we are considering the fully expanded place expression here.)"

**Design question.** Is `&` ↔ `&raw` an equivalence in either direction? (No.)

Basis: execution (Lean kernel check) — `raw_ref_rewrites_not_equivalences` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `raw-and-shared-reference-rewrites-not-equivalences`.

#### `storage-marker-erasure-refines` (theorem)

**Plain claim.** In the toy, under every semantics `S` (fresh addresses, or any static slot assignment, including one in which `x` shares its slot with another local), for every program `P` and local `x`: if no operand of `P` is a pointer constant carrying an allocation identifier (`NoProvConst P`), then erasing every `storageLive x` and `storageDead x` (so that, for `x < P.locals.length`, `x` is allocated at entry for the whole run) gives a prefix-preserving refinement of `P`. Without `NoProvConst` the statement is false (`refuted_eraseMarkers_refinesPP`).

**Kind / tier / depth.** theorem / T1 (Folklore that lifetime extension refines (more memory allocated for longer), here with the condition on pointer constants made explicit; stated for nondeterministic fresh addresses and for static slot assignments.) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Markers.lean:115-117
theorem eraseMarkers_refinesPP_of_noProvConst (S : Sem) (P : Prog) (x : Local)
    (hnp : NoProvConst P) :
    RefinesPP S P (eraseMarkers P x) := by
-- lean/Toy/PlaceEval/Transforms.lean:79-80
def NoProvConst (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, (∀ s ∈ b.stmts, s.provFree = true) ∧ b.term.provFree = true
-- lean/Toy/PlaceEval/Markers.lean:80-81
theorem refuted_eraseMarkers_refinesPP :
    ¬ ∀ (S : Sem) (P : Prog) (x : Local), RefinesPP S P (eraseMarkers P x) := by
```

Unfolded (prose): `eraseMarkers P x` filters the markers of `x` out of every block; for `x < P.locals.length`, `x` then has no markers, so `Prog.initState` allocates it at entry. Under `fresh` the address of the `k`-th allocation is `align * (ω k + 1)` and an overlap with a live allocation blocks the run (no behaviour); under `slots s` every allocation of local `y` is at `s y`. `NoProvConst P` says that every operand of every statement and `switchInt` terminator of `P` satisfies `Operand.provFree` (it is not `.const (.ptr ⟨some k, a⟩)`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hnp : NoProvConst P` | excludes pointer constants that name an allocation identifier; erasure allocates `x` at entry and shifts the identifiers of later allocations, so such a constant can denote another allocation after the edit | tight | `eraseMarkers_noProvConst_counterexample` (`pConstProvSlots` under `SEx`: a one-block program whose constant `⟨some 0, 8⟩` denotes local `1` in the source and is out of bounds after erasure; for fresh addresses see also `eraseMarkers_fresh_noProvConst_counterexample` (`pConstProvFresh`, UB-free, all alignments `1`)) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `eraseMarkers_refinesPP_nonvacuous`: `pStale` has no pointer constant with provenance; the refinement for it holds under fresh addresses (`eraseMarkers_staleRead_not_equivPP`).

**Proof** (prose). A forward simulation between a run of `P` (source) and a run of `eraseMarkers P x` (target) under the same semantics. Source allocations are renamed to target allocations by a partial map that grows during the run; every source allocation of `x` is mapped to the target's single allocation of `x`, and the zero-size allocations made for a local `x ≥ P.locals.length` are mapped to nothing. Source and target addresses coincide, frames agree up to the renaming (the source may have `x` unallocated), every source cell is uninitialized or equal to the target cell with pointer provenance renamed, and `NoProvConst P` makes every pointer constant provenance-free, so constants are related to themselves. The source's marker steps for `x` are silent steps in front of a matched step; whenever the source succeeds, the target succeeds with a related result, so target UB is matched by source UB. Under fresh addresses the source oracle cannot be fixed in advance (which source allocation corresponds to which target allocation depends on the run), so it is chosen step by step and assembled into one oracle along the paired run (`lean/Toy/PlaceEval/LazySim.lean`); a source allocation receives the address of its target counterpart, and its overlap check succeeds because every live source allocation corresponds to a live target allocation with the same range. Files: `LazySim.lean`, `MarkerSim.lean`, `MarkerStep.lean`, `MarkerFwd.lean`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L364–381 (doc comment of `StatementKind::StorageLive`/`StorageDead`; `///` markers removed): "`StorageLive` and `StorageDead` statements mark the live range of a local. At any point during the execution of a function, each local is either allocated or unallocated. Except as noted below, all locals except function parameters are initially unallocated. `StorageLive` statements cause memory to be allocated for the local while `StorageDead` statements cause the memory to be freed. In other words, `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for stack-allocated local variables. Using a local in any way (not only reading/writing from it) while it is unallocated is UB. Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body. These locals are implicitly allocated for the full duration of the function. There is a convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for computing these locals. If the local is already allocated, calling `StorageLive` again will implicitly free the local and then allocate fresh uninitialized memory. If a local is already deallocated, calling `StorageDead` again is a NOP."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/remove_storage_markers.rs L1 (module doc, the pass's documented intent; `//!` marker removed): "This pass removes storage markers if they won't be emitted during codegen."
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/statements.md L160–201 (`storage_live` first runs `storage_dead`, then allocates fresh storage through the memory model's `allocate`; `storage_dead` deallocates if allocated).
- reference corpus package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing`, card `marker-reset-breaks-slot-sharing` (address-free base case: merging two slots breaks lockstep bisimulation when a `StorageLive` of one resets the other).
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/terminators.md L196–200 (in `create_frame`): "        // Allocate all the initially live locals.
          frame.storage_live(&mut self.mem, func.ret)?;
          for arg_local in func.args {
              frame.storage_live(&mut self.mem, arg_local)?;
          }" (only the return local and the arguments are allocated when a frame is created).
- Juneyoung Lee et al., "Reconciling High-Level Optimizations and Low-Level Code in LLVM", OOPSLA 2018 (PACMPL 2), DOI 10.1145/3276495 (a memory model with nondeterministic allocation addresses, address observation and allocation lifetimes).

**Design question.** Is erasing storage markers a refinement, and under which address model and which condition on constants?

Basis: execution (Lean kernel check) — `eraseMarkers_refinesPP_of_noProvConst` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `storage-marker-erasure-refines`.

#### `storage-marker-erasure-end-to-end-with-static-slots` (theorem)

**Plain claim.** In the toy, for every slot assignment `s`, program `P` and local `x`: if no operand of `P` is a pointer constant carrying an allocation identifier (`NoProvConst P`) and the slot execution of `P` refines its fresh-address execution (`RefinesAcross .fresh P (.slots s) P`), then the slot execution of `P` with the markers of `x` erased, with the same `s`, refines the fresh-address execution of `P`. Without `NoProvConst` the statement is false (`refuted_eraseMarkers_slots_refinesAcross_fresh`).

**Kind / tier / depth.** theorem / T0 (Transitivity of refinement (CompCert's `behavior_improves` is transitive) applied to `eraseMarkers_refinesPP_of_noProvConst`; re-derived in the toy.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Markers.lean:141-143
theorem eraseMarkers_slots_refinesAcross_fresh_of_noProvConst (s : Local → Nat) (P : Prog)
    (x : Local) (hnp : NoProvConst P) (hvalid : RefinesAcross .fresh P (.slots s) P) :
    RefinesAcross .fresh P (.slots s) (eraseMarkers P x) :=
-- lean/Toy/PlaceEval/Semantics.lean:166-167
def RefinesAcross (Ss : Sem) (src : Prog) (St : Sem) (tgt : Prog) : Prop :=
  ∀ bt, HasBeh St tgt bt → ∃ bs, HasBeh Ss src bs ∧ ImprovesPP bt bs
-- lean/Toy/PlaceEval/Markers.lean:127-129
theorem refuted_eraseMarkers_slots_refinesAcross_fresh :
    ¬ ∀ (s : Local → Nat) (P : Prog) (x : Local),
      RefinesAcross .fresh P (.slots s) P → RefinesAcross .fresh P (.slots s) (eraseMarkers P x) := by
```

Unfolded (prose): `RefinesAcross Ss src St tgt` is `∀ bt, HasBeh St tgt bt → ∃ bs, HasBeh Ss src bs ∧ ImprovesPP bt bs`. Proved from `eraseMarkers_refinesPP_of_noProvConst` and `refinesAcross_trans`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hnp : NoProvConst P` | excludes pointer constants that name an allocation identifier | tight | `eraseMarkers_slots_noProvConst_counterexample` (`pConstProvFresh` with `sEx`: `sEx` is valid for it, and the slot execution of its marker-erased version reaches UB, improving no fresh behaviour) |
| `hvalid : RefinesAcross .fresh P (.slots s) P` | the slot assignment is valid for the source | tight | `eraseMarkers_slots_invalid_counterexample` (`pAlias` with `sAlias`: two simultaneously live locals share a slot; `NoProvConst pAlias` holds and the end-to-end refinement fails) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `eraseMarkers_slots_nonvacuous`: `pLive` has no pointer constant with provenance and `sEx` is valid for it.

**Prior art.**

- reference corpus package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing`, card `marker-reset-breaks-slot-sharing` (address-free base case: merging two slots breaks lockstep bisimulation when a `StorageLive` of one resets the other).
- Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814 (behaviour-improvement refinement for a verified compiler; the improvement relation here is CompCert's, prefix-preserving).

**Design question.** May a static slot assignment computed for `P` be kept when lowering the marker-erased program directly, with no other pass in between?

Basis: execution (Lean kernel check) — `eraseMarkers_slots_refinesAcross_fresh_of_noProvConst` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Non-claims: see **Boundaries**, *Non-claims*, `storage-marker-erasure-end-to-end-with-static-slots`.

#### `storage-marker-erasure-shared-slot-lowering-mismatch` (counterexample)

**Plain claim.** Under the slot assignment `sShare`, which places locals `0` and `1` of `pShare` at the same address (their live ranges are disjoint, and `pShare` reaches UB at its final read: `pShare_fresh_wrong`, `pShare_slots_beh`): the slot execution of `pShare` refines its fresh-address execution; the slot execution of `pShare` with the markers of local `0` erased still refines the fresh-address execution of `pShare`; but it does not refine the fresh-address execution of the marker-erased program itself: the write of `7` to local `1` overwrites the shared cell, so the slot execution emits `7` (`pShare_erased_slots_beh`), while every fresh-address execution of the marker-erased program emits `5` or blocks (`pShare_erased_fresh_beh`).

**Kind / tier / depth.** counterexample / T1 (A concrete instance distinguishing slot-assignment validity for the source from validity for the marker-erased program; the address-free analogue is the cited slot-compaction card.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Markers.lean:171-175
theorem eraseMarkers_sharedSlot_lowering_mismatch :
    sShare 0 = sShare 1 ∧
    RefinesAcross .fresh pShare (.slots sShare) pShare ∧
    RefinesAcross .fresh pShare (.slots sShare) (eraseMarkers pShare 0) ∧
    ¬ RefinesAcross .fresh (eraseMarkers pShare 0) (.slots sShare) (eraseMarkers pShare 0) := by
```

Unfolded (prose): Conjunction: `sShare 0 = sShare 1`, two `RefinesAcross` facts and one negated `RefinesAcross`.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** Counterexample (concrete program; the fresh side is analysed for every oracle).

**Prior art.**

- reference corpus package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing`, card `marker-reset-breaks-slot-sharing` (address-free base case: merging two slots breaks lockstep bisimulation when a `StorageLive` of one resets the other).
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L364–381 (doc comment of `StatementKind::StorageLive`/`StorageDead`; `///` markers removed): "`StorageLive` and `StorageDead` statements mark the live range of a local. At any point during the execution of a function, each local is either allocated or unallocated. Except as noted below, all locals except function parameters are initially unallocated. `StorageLive` statements cause memory to be allocated for the local while `StorageDead` statements cause the memory to be freed. In other words, `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for stack-allocated local variables. Using a local in any way (not only reading/writing from it) while it is unallocated is UB. Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body. These locals are implicitly allocated for the full duration of the function. There is a convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for computing these locals. If the local is already allocated, calling `StorageLive` again will implicitly free the local and then allocate fresh uninitialized memory. If a local is already deallocated, calling `StorageDead` again is a NOP."

**Design question.** Does erasing markers after slot sharing let one local's writes clobber another, and does that break end-to-end refinement?

Basis: execution (Lean kernel check) — `eraseMarkers_sharedSlot_lowering_mismatch` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `storage-marker-erasure-shared-slot-lowering-mismatch`.

#### `storage-marker-erasure-equivalence-sufficient-condition` (theorem)

**Plain claim.** In the toy, under fresh addresses, for every program `P` and local `x`: if every local of `P` has alignment at least `1` (`hwf`), no statement of `P` observes an address (`NoAddrObs`: no `ptrEq` and no `addrOf`), and `P` is UB-free (`UBFree .fresh P`), then erasing the markers of `x` is a prefix-preserving equivalence (traces coincide, and UB-freedom transfers in both directions). Each of the three hypotheses is tight (`eraseMarkers_hwf_counterexample`, `eraseMarkers_hobs_counterexample`, `eraseMarkers_hub_counterexample`).

**Kind / tier / depth.** theorem / T1 (Folklore made precise (lifetime extension is unobservable when addresses are not observed and the program has no UB), with the conditions sharpened (alignment at least `1`, whole-program absence of address observation, UB-freedom under every oracle).) / substantive.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Markers.lean:190-192
theorem eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree (P : Prog) (x : Local)
    (hwf : ∀ L ∈ P.locals, 1 ≤ L.align) (hobs : NoAddrObs P) (hub : UBFree .fresh P) :
    EquivPP .fresh P (eraseMarkers P x) := by
-- lean/Toy/PlaceEval/Transforms.lean:48-49
def NoAddrObs (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, ∀ s ∈ b.stmts, ∀ rv, s.rvalue? = some rv → rv.observesAddr = false
```

Unfolded (prose): `EquivPP .fresh P (eraseMarkers P x)`; behaviour sets are unions over all oracles. `NoAddrObs P` says that no right-hand side of a statement of `P` is a `ptrEq` or an `addrOf` (`Rvalue.observesAddr`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample (witness class) |
|---|---|---|---|
| `hwf : ∀ L ∈ P.locals, 1 ≤ L.align` | with alignment `0` every fresh allocation sits at address `0`, so pinning `x` there refuses every later allocation of another alignment-0 local | tight | `eraseMarkers_hwf_counterexample` (`pAlignZero`: two alignment-0 locals with disjoint live ranges; no address observation, UB-free, and the marker-erased program has no behaviour) |
| `hobs : NoAddrObs P` | no statement compares or casts addresses | tight | `eraseMarkers_hobs_counterexample` (`pAddrCmp`: two live ranges of `x` with their addresses compared (two iterations of a loop body, unrolled); alignments at least `1`, UB-free) |
| `hub : UBFree .fresh P` | excludes stale reads and other UB that erasure removes | tight | `eraseMarkers_hub_counterexample` (`pStale`: a read of `x` after a re-`storageLive`; alignment `1`, no address observation) |

Each counterexample is stated in the canonical form "all other hypotheses hold and the conclusion fails"; its verbatim statement is in "Auxiliary declarations cited by name".

**Non-vacuity witness.** `noAddrObs_ubFree_pLive`: `pLive` satisfies all three hypotheses.

**Proof** (prose). Forward direction: the simulation used for `eraseMarkers_refinesPP_of_noProvConst`, with every source address shifted up by a constant `D` that is a multiple of every positive alignment occurring in `P` (types, reference layouts, locals and the pointer alignment) and larger than every address of a pointer constant of `P`; `hwf` makes the shifted addresses valid fresh addresses and keeps target addresses positive, and `NoAddrObs` ensures that the shift is never observed. Every non-zero-size access through a pointer constant then fails in the source (source UB, allowed by refinement); pointer constants are related to themselves. This half of the proof does not use `hub`; that weaker forward statement is not exported as a card result. Reverse direction: a simulation in which the source is a run of `eraseMarkers P x` and the target a run of `P` that, by `hub`, never reaches UB; the source places `x` once at an address above every pointer constant and every other allocation at the target's address shifted by `D` (so the source's allocations never overlap and the run never blocks), relates allocations one by one with their bases (every target allocation of `x` is related to the source's single allocation of `x`), and treats the target's marker steps for `x` as silent steps measured by the length of the remaining block. Whenever source and target both succeed their results are related; a source failure is allowed. Files: `MarkerRevMem.lean`, `MarkerRevAlloc.lean`, `MarkerRevRel.lean`, `MarkerRev.lean`, `MarkerEquiv.lean`.

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L364–381 (doc comment of `StatementKind::StorageLive`/`StorageDead`; `///` markers removed): "`StorageLive` and `StorageDead` statements mark the live range of a local. At any point during the execution of a function, each local is either allocated or unallocated. Except as noted below, all locals except function parameters are initially unallocated. `StorageLive` statements cause memory to be allocated for the local while `StorageDead` statements cause the memory to be freed. In other words, `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for stack-allocated local variables. Using a local in any way (not only reading/writing from it) while it is unallocated is UB. Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body. These locals are implicitly allocated for the full duration of the function. There is a convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for computing these locals. If the local is already allocated, calling `StorageLive` again will implicitly free the local and then allocate fresh uninitialized memory. If a local is already deallocated, calling `StorageDead` again is a NOP."
- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/remove_storage_markers.rs L1 (module doc, the pass's documented intent; `//!` marker removed): "This pass removes storage markers if they won't be emitted during codegen."
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/statements.md L160–201 (`storage_live` first runs `storage_dead`, then allocates fresh storage through the memory model's `allocate`; `storage_dead` deallocates if allocated).
- [documentation; connection to the toy: derived (modeling bridge)] minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/terminators.md L196–200 (in `create_frame`): "        // Allocate all the initially live locals.
          frame.storage_live(&mut self.mem, func.ret)?;
          for arg_local in func.args {
              frame.storage_live(&mut self.mem, arg_local)?;
          }" (only the return local and the arguments are allocated when a frame is created).
- Juneyoung Lee et al., "Reconciling High-Level Optimizations and Low-Level Code in LLVM", OOPSLA 2018 (PACMPL 2), DOI 10.1145/3276495 (a memory model with nondeterministic allocation addresses, address observation and allocation lifetimes).

**Design question.** When do properties proved for the marker-erased program transfer back to the source?

Basis: execution (Lean kernel check) — `eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `storage-marker-erasure-equivalence-sufficient-condition`.

#### `storage-marker-erasure-equivalence-conditions-not-necessary` (counterexample)

**Plain claim.** Under fresh addresses: erasing the markers of `pDeadUse` (which writes `x` while it is unallocated and then reaches `unreachable`, so it is not UB-free) is an equivalence: both programs reach UB before any event, the marker-erased one at `unreachable` (`pDeadUse_fresh_beh`, `pDeadUse_erased_fresh_beh`); erasing the markers of `pAddrSelf` (which compares `&raw x` with itself within one live range, so `NoAddrObs` fails) is an equivalence (both emit `1` or block: `pAddrSelf_fresh_beh`, `pAddrSelf_erased_fresh_beh`); and erasing the markers of `pAlignZeroOne` (one local of alignment `0`, no address observation, UB-free) is an equivalence (`eraseMarkers_fresh_equivPP_without_alignPos`).

**Kind / tier / depth.** counterexample / T0 (Concrete instances analysed for every oracle; re-derived in the toy.) / shallow.

**Lean statement** (verbatim):

```lean
-- lean/Toy/PlaceEval/Markers.lean:306-308
theorem eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs :
    (EquivPP .fresh pDeadUse (eraseMarkers pDeadUse 0) ∧ ¬ UBFree .fresh pDeadUse) ∧
    (EquivPP .fresh pAddrSelf (eraseMarkers pAddrSelf 1) ∧ ¬ NoAddrObs pAddrSelf) := by
-- lean/Toy/PlaceEval/Markers.lean:353-356
theorem eraseMarkers_fresh_equivPP_without_alignPos :
    NoAddrObs pAlignZeroOne ∧ UBFree .fresh pAlignZeroOne ∧
      ¬ (∀ L ∈ pAlignZeroOne.locals, 1 ≤ L.align) ∧
      EquivPP .fresh pAlignZeroOne (eraseMarkers pAlignZeroOne 0) := by
```

Unfolded (prose): `(EquivPP … ∧ ¬ UBFree …) ∧ (EquivPP … ∧ ¬ NoAddrObs …)`, and `NoAddrObs … ∧ UBFree … ∧ ¬ (∀ L ∈ …, 1 ≤ L.align) ∧ EquivPP …`.

**Hypothesis ledger.**

No hypotheses (beyond the types of the bound variables).

**Non-vacuity witness.** Counterexamples (concrete programs, analysed for every oracle).

**Prior art.**

- [documentation; connection to the toy: derived (modeling bridge)] rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/syntax.rs L364–381 (doc comment of `StatementKind::StorageLive`/`StorageDead`; `///` markers removed): "`StorageLive` and `StorageDead` statements mark the live range of a local. At any point during the execution of a function, each local is either allocated or unallocated. Except as noted below, all locals except function parameters are initially unallocated. `StorageLive` statements cause memory to be allocated for the local while `StorageDead` statements cause the memory to be freed. In other words, `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for stack-allocated local variables. Using a local in any way (not only reading/writing from it) while it is unallocated is UB. Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body. These locals are implicitly allocated for the full duration of the function. There is a convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for computing these locals. If the local is already allocated, calling `StorageLive` again will implicitly free the local and then allocate fresh uninitialized memory. If a local is already deallocated, calling `StorageDead` again is a NOP."

**Design question.** Are the hypotheses `UBFree`, `NoAddrObs` and `hwf` of `eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree` necessary for marker-erasure equivalence? (No.)

Basis: execution (Lean kernel check) — `eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs`, `eraseMarkers_fresh_equivPP_without_alignPos` and the counterexamples and witnesses named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — prior-art entries tagged `derived (modeling bridge)` quote documented behaviour of rustc MIR, MiniRust, the Rust Reference or CompCert, and the toy's corresponding rule is written to follow it; no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about those systems.

Non-claims: see **Boundaries**, *Non-claims*, `storage-marker-erasure-equivalence-conditions-not-necessary`.

### Auxiliary declarations cited by name (verbatim)

Verbatim quotes of every other package declaration named above.

```lean
-- lean/Toy/PlaceEval/Memory.lean:110-111
theorem offsetInbounds_eq_dereferenceable (m : Mem) (q : Ptr) (k : Nat) :
    m.offsetInbounds q k = m.dereferenceable q k := rfl
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:43-44
theorem decodePtr_ex_pos_frags :
    decodePtr [.ptrFrag ⟨some 0, 6⟩ 0, .ptrFrag ⟨some 0, 6⟩ 1] = some ⟨some 0, 6⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:46-47
theorem decodePtr_ex_neg_mismatch :
    decodePtr [.ptrFrag ⟨some 0, 6⟩ 0, .ptrFrag ⟨some 1, 6⟩ 1] = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:29
theorem inBounds_ex_pos : mEx.inBounds ⟨some 0, 4⟩ 4 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:32
theorem inBounds_ex_neg_freed : mEx.inBounds ⟨some 1, 8⟩ 1 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:56
theorem load_ex_pos_int : mEx.load ⟨some 0, 6⟩ u8 = some (.int 3) := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:57
theorem load_ex_neg_uninit : mEx.load ⟨some 0, 7⟩ u8 = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:54
theorem load_ex_pos_ptr : mEx.load ⟨some 0, 4⟩ .ptr = some (.ptr ⟨some 0, 6⟩) := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:58
theorem load_ex_neg_freed : mEx.load ⟨some 1, 8⟩ u8 = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:23
theorem aligned_ex_pos : aligned 2 4 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:25
theorem aligned_zero_ex_pos : aligned 0 0 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:24
theorem aligned_ex_neg : aligned 2 5 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:26
theorem aligned_zero_ex_neg : aligned 0 3 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:30
theorem inBounds_ex_pos_end : mEx.inBounds ⟨some 0, 6⟩ 2 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:31
theorem inBounds_ex_neg_past : mEx.inBounds ⟨some 0, 6⟩ 3 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:34
theorem dereferenceable_ex_pos_zero_null : mEx.dereferenceable ⟨none, 0⟩ 0 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:35
theorem dereferenceable_ex_neg_freed : mEx.dereferenceable ⟨some 1, 8⟩ 1 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:37
theorem offsetInbounds_ex_pos_one_past_end : mEx.offsetInbounds ⟨some 0, 4⟩ 4 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:36
theorem offsetInbounds_ex_pos_zero_null : mEx.offsetInbounds ⟨none, 0⟩ 0 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:39
theorem offsetInbounds_ex_neg_freed : mEx.offsetInbounds ⟨some 1, 8⟩ 1 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:49
theorem decode_enum_ex_pos : bool2.decode [.byte 1] = some (.int 1) := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:50
theorem decode_enum_ex_neg_tag : bool2.decode [.byte 2] = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:51
theorem decode_int_ex_neg_uninit : u8.decode [.uninit] = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:45
theorem decodePtr_ex_pos_bytes : decodePtr [.byte 1, .byte 2] = some ⟨none, 513⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:48
theorem decodePtr_ex_neg_uninit : decodePtr [.uninit, .uninit] = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:61
theorem load_ex_pos_zero_size_null : mEx.load ⟨none, 0⟩ (.int 0 1) = some (.int 0) := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:55
theorem load_ex_neg_misaligned : mEx.load ⟨some 0, 5⟩ .ptr = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:64
theorem store_ex_pos : (mEx.store ⟨some 0, 6⟩ u8 (.int 9)).isSome = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:65
theorem store_ex_neg_freed : mEx.store ⟨some 1, 8⟩ u8 (.int 9) = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:69
theorem derefLoadOk_ex_pos : DerefLoadOk mEx ⟨some 0, 4⟩ :=
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:71
theorem derefLoadOk_ex_neg_not_a_pointer : ¬ DerefLoadOk mEx ⟨some 0, 6⟩ := fun h =>
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:75
theorem evalPlace_ex_pos_deref : evalPlace stEx ⟨0, [.deref]⟩ = some ⟨some 0, 6⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:81
theorem evalPlace_ex_neg_unallocated_local : evalPlace stEx ⟨1, []⟩ = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:196-198
theorem basePtr_freed_in_frame_eq_some :
    stFreedInFrame.basePtr 0 = some ⟨some 0, 4⟩ ∧
      evalPlace stFreedInFrame ⟨0, []⟩ = some ⟨some 0, 4⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:193-195
theorem basePtr_missing_alloc_eq_none :
    stMissingAlloc.allocOf 0 = some 0 ∧ stMissingAlloc.basePtr 0 = none ∧
      evalPlace stMissingAlloc ⟨0, []⟩ = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:171
theorem readIndex_ex_pos : stIdx.readIndex 0 = some 1 := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:172
theorem readIndex_ex_neg_unallocated : stEx.readIndex 1 = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:174
theorem evalPlace_ex_pos_index : evalPlace stIdx ⟨0, [.index 0 2]⟩ = some ⟨some 0, 6⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:184-185
theorem evalPlace_ex_pos_index_zero_size :
    evalPlace stDangIdx ⟨0, [.deref, .index 1 0]⟩ = some ⟨some 1, 8⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:77
theorem evalPlace_ex_neg_inner_not_pointer : evalPlace stEx ⟨0, [.deref, .deref]⟩ = none := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:187-188
theorem evalPlace_ex_neg_index_dangling :
    evalPlace stDangIdx ⟨0, [.deref, .index 1 1]⟩ = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:167
theorem evalPrefix_ex_pos : evalPrefix stEx ⟨0, [.deref, .deref]⟩ 1 = some ⟨some 0, 6⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:168
theorem evalPrefix_ex_neg_unallocated : evalPrefix stEx ⟨1, []⟩ 0 = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:89
theorem refOk_ex_pos : RefOk mEx ⟨some 0, 6⟩ ⟨2, 2⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:90
theorem refOk_ex_neg_misaligned : ¬ RefOk mEx ⟨some 0, 5⟩ ⟨2, 2⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:95
theorem refOk_ex_neg_align_zero : ¬ RefOk mEx ⟨some 0, 4⟩ ⟨0, 0⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:199
theorem evalInt_ex_pos : (Operand.copy ⟨0, []⟩ u8).evalInt stIdx = some 1 := by decide
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:255
theorem evalInt_copy_instance : (Operand.copy ⟨0, []⟩ bool2).evalInt stEx = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:104
theorem allocate_fresh_ex_pos : (allocate (.fresh fun _ => 4) stEx 1 ⟨2, 2⟩).isSome = true := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:100-101
theorem allocate_fresh_ex_neg_overlap :
    allocate (.fresh fun _ => 1) stEx 1 ⟨2, 2⟩ = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:115
theorem deallocate_ex : (deallocate stEx 0).basePtr 0 = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:116
theorem deallocate_ex_noop : deallocate (deallocate stEx 0) 0 = deallocate stEx 0 := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:119
theorem hasMarkers_ex_pos : pStale.hasMarkers 0 = true := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:120
theorem hasMarkers_ex_neg : pAddrCmp.hasMarkers 0 = false := by decide
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:54
theorem pAddrCmp_fresh_term_zero : HasBeh .fresh pAddrCmp (.term [0]) :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:31
theorem pNull_zero_beh (b : Beh) : HasBeh SEx (pNull 0) b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:68
theorem hasBeh_ex_neg_erased_addrCmp : ¬ HasBeh .fresh (eraseMarkers pAddrCmp 1) (.term [0]) := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:229-232
theorem eraseMarkers_alignZero_not_equivPP :
    NoAddrObs pAlignZero ∧ UBFree .fresh pAlignZero ∧
      (∀ b, ¬ HasBeh .fresh (eraseMarkers pAlignZero 0) b) ∧
      ¬ RefinesPP .fresh (eraseMarkers pAlignZero 0) pAlignZero := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:141
theorem improvesPP_ex_pos_prefix : ImprovesPP (.term [1, 2]) (.wrong [1]) :=
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:147
theorem improvesPP_ex_neg_nonprefix : ¬ ImprovesPP (.term [1]) (.wrong [2]) := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:148-149
theorem eraseMarkers_slots_nonvacuous :
    NoProvConst pLive ∧ RefinesAcross .fresh pLive (.slots sEx) pLive :=
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:308-310
theorem eraseMarkers_slots_invalid_counterexample :
    NoProvConst pAlias ∧ eraseMarkers pAlias 0 = pAlias ∧
      ¬ RefinesAcross .fresh pAlias (.slots sAlias) (eraseMarkers pAlias 0) := by
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:374
theorem switchToGoto_validTag_equivPP : EquivPP SEx (pSwTag 1) (setTerm (pSwTag 1) 0 (.goto 1)) :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:356-363
theorem switchToGoto_erases_operand_ub :
    ((pSwUninit.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1 ∧
      RefinesPP SEx pSwUninit (setTerm pSwUninit 0 (.goto 1)) ∧
      ¬ RefinesPP SEx (setTerm pSwUninit 0 (.goto 1)) pSwUninit) ∧
    (((pSwTag 2).blk 0).term = .switchInt (.copy ⟨0, []⟩ bool2) [(0, 1)] 1 ∧
      RefinesPP SEx (pSwTag 2) (setTerm (pSwTag 2) 0 (.goto 1)) ∧
      ¬ RefinesPP SEx (setTerm (pSwTag 2) 0 (.goto 1)) (pSwTag 2)) ∧
    (∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:323-327
theorem reachableAt_ex_pos :
    ReachableAt SEx (pDanglingMention 0) 0 3
      (match runFromInit (.slots sEx) (pDanglingMention 0) 3 with
       | .running c _ => c.st
       | _ => ⟨⟨[], []⟩, []⟩) :=
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:331
theorem reachableAt_ex_neg (st : State) : ¬ ReachableAt SEx pHaltEmit 1 0 st := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:338-339
theorem goesWrongFrom_ex_pos :
    GoesWrongFrom SEx pDerefUninit (pDerefUninit.entry 0 (initEx pDerefUninit)) [] :=
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:343-344
theorem goesWrongFrom_ex_neg (t : List Nat) :
    ¬ GoesWrongFrom SEx pHalt (pHalt.entry 0 (initEx pHalt)) t := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:196-197
theorem noAddrObs_ubFree_pLive :
    (∀ L ∈ pLive.locals, 1 ≤ L.align) ∧ NoAddrObs pLive ∧ UBFree .fresh pLive := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:356
theorem not_exactUBChecker_const_true : ¬ ExactUBChecker SEx (fun _ => true) := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:126-127
theorem deleteStmt_ex : (deleteStmt pDerefUninit 0 2).blocks =
    [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩)], .halt⟩] := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:128
theorem deleteStmt_ex_out_of_range : deleteStmt pDerefUninit 3 0 = pDerefUninit := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:129
theorem setTerm_ex : (setTerm pSwUninit 0 (.goto 1)).blk 0 = ⟨[], .goto 1⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:133
theorem setTerm_ex_out_of_range : setTerm pSwUninit 9 (.goto 1) = pSwUninit := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:130-131
theorem setStmt_ex : ((setStmt pRawDangling 0 3 refDerefStmt).blk 0).stmts[3]? =
    some refDerefStmt := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:134
theorem setStmt_ex_out_of_range_blk : setStmt pRawDangling 9 0 refDerefStmt = pRawDangling := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:136
theorem setStmt_ex_out_of_range_idx : setStmt pRawDangling 0 99 refDerefStmt = pRawDangling := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:121-122
theorem eraseMarkers_ex : (eraseMarkers pStale 0).blocks =
    [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int 5))), .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩] := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:125
theorem eraseMarkers_ex_other_local : eraseMarkers pAddrCmp 0 = pAddrCmp := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:155
theorem noAddrObs_ex_pos : NoAddrObs pStale := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:161
theorem noAddrObs_ex_neg : ¬ NoAddrObs pAddrCmp := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:74
theorem noProvConst_ex_pos : NoProvConst pStale := by decide
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:75
theorem noProvConst_ex_neg : ¬ NoProvConst pConstProvSlots := by decide
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:23
def SEx : Sem := .slots sEx
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:30-33
def pDerefUninit : Prog :=
  ⟨[ptrL, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .placeMention ⟨0, [.deref, .deref]⟩], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:44-47
def pDanglingRaw (off : Nat) : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .assign ⟨2, []⟩ .ptr (.rawRef ⟨0, [.deref, .field off]⟩)], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:50-53
def pNull (off : Nat) : Prog :=
  ⟨[ptrL, ptrL],
   [⟨[.assign ⟨0, []⟩ .ptr (.use (.const nullV)), .placeMention ⟨0, [.deref]⟩,
      .assign ⟨1, []⟩ .ptr (.rawRef ⟨0, [.deref, .field off]⟩)], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:37-40
def pDanglingMention (off : Nat) : Prog :=
  ⟨[ptrL, ⟨4, 2⟩],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .placeMention ⟨0, [.deref, .field off]⟩], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:58-61
def pMisaligned : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.assign ⟨0, []⟩ .ptr (.rawRef ⟨1, [.field 1]⟩), .placeMention ⟨0, [.deref]⟩,
      .assign ⟨2, []⟩ .ptr (.rawRef ⟨0, [.deref, .field 0]⟩)], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:64-67
def pTwoMentions : Prog :=
  ⟨[ptrL, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .placeMention ⟨0, [.deref, .deref]⟩, .placeMention ⟨0, [.deref, .deref]⟩], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:124-127
def pStale : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.storageLive 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 5))), .storageDead 0,
      .storageLive 0, .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:91-94
def pRawDangling : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1, rawDerefStmt],
     .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:85
def refDerefStmt : Stmt := .assign ⟨2, []⟩ .ptr (.ref ⟨0, [.deref]⟩ ⟨4, 2⟩)
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:105-106
def pRawPacked : Prog :=
  ⟨[⟨3, 1⟩, ptrL], [⟨[.assign ⟨1, []⟩ .ptr (.rawRef ⟨0, [.field 1]⟩)], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:109
def refPackedStmt : Stmt := .assign ⟨1, []⟩ .ptr (.ref ⟨0, [.field 1]⟩ ⟨2, 2⟩)
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:97-100
def pRefDangling : Prog :=
  ⟨[ptrL, ⟨4, 2⟩, ptrL],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1, refDerefStmt],
     .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:88
def rawDerefStmt : Stmt := .assign ⟨2, []⟩ .ptr (.rawRef ⟨0, [.deref]⟩)
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:112
def sShare : Local → Nat := fun x => if x ≤ 1 then 4 else 4 * x + 4
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:117-121
def pShare : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩],
   [⟨[.storageLive 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 5))), .storageDead 0,
      .storageLive 1, .assign ⟨1, []⟩ u8 (.use (.const (.int 7))), .storageDead 1,
      .storageLive 0, .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:141-144
def pDeadUse : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.storageLive 0, .storageDead 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 1)))],
      .unreachable⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:148-151
def pAddrSelf : Prog :=
  ⟨[ptrL, ⟨1, 1⟩],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .emit (.ptrEq (.copy ⟨0, []⟩ .ptr) (.copy ⟨0, []⟩ .ptr))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:330-331
def pAlignZeroOne : Prog :=
  ⟨[⟨1, 0⟩], [⟨[.storageLive 0, .emit (.use (.const (.int 1))), .storageDead 0], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:15-16
theorem evalPlace_eq_none_iff_instance :
    evalPlace stEx ⟨0, [.deref, .deref]⟩ = none ∧ evalPlace stEx ⟨0, [.deref]⟩ ≠ none := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:20
def stEx : State := ⟨mEx, [some 0, none]⟩
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:15-17
def mEx : Mem :=
  ⟨[⟨4, 4, true⟩, ⟨8, 2, false⟩],
   [(4, .ptrFrag ⟨some 0, 6⟩ 0), (5, .ptrFrag ⟨some 0, 6⟩ 1), (6, .byte 3)]⟩
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:79
theorem evalPlace_ex_neg_misaligned_load : evalPlace stEx ⟨0, [.field 1, .deref]⟩ = none := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:85
theorem evalPlace_ex_neg_field_past_end : evalPlace stEx ⟨0, [.deref, .field 3]⟩ = none := by
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:190
def stMissingAlloc : State := ⟨⟨[], []⟩, [some 0]⟩
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:192
def stFreedInFrame : State := ⟨⟨[⟨4, 4, false⟩], []⟩, [some 0]⟩
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:179-181
def stDangIdx : State :=
  ⟨⟨[⟨4, 4, true⟩, ⟨8, 2, false⟩, ⟨12, 1, true⟩],
    [(4, .ptrFrag ⟨some 1, 8⟩ 0), (5, .ptrFrag ⟨some 1, 8⟩ 1), (12, .byte 3)]⟩, [some 0, some 2]⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:20-21
theorem evalPlace_deref_zeroFields_instance :
    evalPlace stEx ⟨0, [.deref, .field 0, .field 0]⟩ = some ⟨some 0, 6⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:83-84
theorem evalPlace_ex_pos_field_one_past_end :
    evalPlace stEx ⟨0, [.deref, .field 2]⟩ = some ⟨some 0, 8⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:20
def sEx : Local → Nat := fun x => 4 * x + 4
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:26
def nullV : Val := .ptr ⟨none, 0⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:14
def ptrL : Layout := ⟨ptrSize, ptrAlign⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:27-28
theorem erasePlaceMention_nonvacuous :
    (pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) := by decide
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:186-192
theorem erasePlaceMention_erases_place_ub :
    ((pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) ∧
      RefinesPP SEx pDerefUninit (deleteStmt pDerefUninit 0 2) ∧
      ¬ RefinesPP SEx (deleteStmt pDerefUninit 0 2) pDerefUninit) ∧
    (((pDanglingMention 2).blk 0).stmts[3]? = some (.placeMention ⟨0, [.deref, .field 2]⟩) ∧
      RefinesPP SEx (pDanglingMention 2) (deleteStmt (pDanglingMention 2) 0 3) ∧
      ¬ RefinesPP SEx (deleteStmt (pDanglingMention 2) 0 3) (pDanglingMention 2)) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:65-67
theorem deleteStmt_emit_counterexample :
    (∀ st, ReachableAt SEx pEmitL 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
      ¬ RefinesPP SEx pEmitL (deleteStmt pEmitL 0 0) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:57
def pEmitL : Prog := ⟨[⟨1, 1⟩], [⟨[.emit (.use (.const (.int 1)))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/RunLemmas.lean:228-230
theorem refinesAcross_trans {S₁ S₂ S₃ : Sem} {P₁ P₂ P₃ : Prog}
    (h₁₂ : RefinesAcross S₁ P₁ S₂ P₂) (h₂₃ : RefinesAcross S₂ P₂ S₃ P₃) :
    RefinesAcross S₁ P₁ S₃ P₃ := by
```

```lean
-- lean/Toy/PlaceEval/EditSim.lean:221-222
theorem deleteStmt_refinesPP (S : Sem) (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    RefinesPP S P (deleteStmt P l i) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:33-36
theorem erasePlaceMention_equiv_nonvacuous :
    ((pDanglingMention 0).blk 0).stmts[3]? = some (.placeMention ⟨0, [.deref, .field 0]⟩) ∧
      ∀ st, ReachableAt SEx (pDanglingMention 0) 0 3 st →
        (evalPlace st ⟨0, [.deref, .field 0]⟩).isSome = true := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:80-82
theorem erasePlaceMention_equiv_hs_counterexample :
    (∀ st, ReachableAt SEx pEmitL 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
      ¬ EquivPP SEx pEmitL (deleteStmt pEmitL 0 0) :=
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:86-88
theorem erasePlaceMention_equiv_hok_counterexample :
    (pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) ∧
      ¬ EquivPP SEx pDerefUninit (deleteStmt pDerefUninit 0 2) :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:15
theorem pDerefUninit_beh (b : Beh) : HasBeh SEx pDerefUninit b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:17-18
theorem pDerefUninit_erased_beh (b : Beh) :
    HasBeh SEx (deleteStmt pDerefUninit 0 2) b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:24
theorem pDanglingMention_two_beh (b : Beh) : HasBeh SEx (pDanglingMention 2) b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:26-27
theorem pDanglingMention_two_erased_beh (b : Beh) :
    HasBeh SEx (deleteStmt (pDanglingMention 2) 0 3) b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/EditSim.lean:204-209
theorem deleteStmt_rev_refinesPP (S : Sem) (hs : (P.blk l).stmts[i]? = some (.placeMention p))
    (hfail : ∀ ω st0 st, P.initState (S.mode ω) = some st0 →
      Reach (S.mode ω) P (P.entry 0 st0) ⟨l, (P.blk l).stmts.drop i, st⟩ →
      evalPlace st p = none →
      SrcUB (S.mode ω) (deleteStmt P l i) ⟨l, (P.blk l).stmts.drop (i + 1), st⟩) :
    RefinesPP S (deleteStmt P l i) P := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:93-96
theorem erasePlaceMention_iff_hs_counterexample :
    ¬ (EquivPP SEx pEmitL (deleteStmt pEmitL 0 0) ↔
        ∀ st, ReachableAt SEx pEmitL 0 0 st → evalPlace st ⟨0, []⟩ = none →
          GoesWrongFrom SEx (deleteStmt pEmitL 0 0) ((deleteStmt pEmitL 0 0).at 0 0 st) []) := by
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:37
theorem pTwoMentions_beh (b : Beh) : HasBeh SEx pTwoMentions b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:39-40
theorem pTwoMentions_erased_beh (b : Beh) :
    HasBeh SEx (deleteStmt pTwoMentions 0 2) b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:164-167
def stTwoMentions : State :=
  match runFromInit (.slots sEx) pTwoMentions 2 with
  | .running c _ => c.st
  | _ => ⟨⟨[], []⟩, []⟩
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:161
def initEx (P : Prog) : State := (P.initState (.slots sEx)).getD ⟨⟨[], []⟩, []⟩
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:51
theorem pStale_fresh_wrong : HasBeh .fresh pStale (.wrong []) :=
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:45-46
theorem pStale_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pStale 0) b) : b = .term [5] := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:46-50
theorem ubFree_erasePlaceMention_nonvacuous :
    ((pDanglingMention 0).blk 0).stmts[3]? = some (.placeMention ⟨0, [.deref, .field 0]⟩) ∧
      (∀ st, ReachableAt SEx (pDanglingMention 0) 0 3 st →
        (evalPlace st ⟨0, [.deref, .field 0]⟩).isSome = true) ∧
      UBFree SEx (deleteStmt (pDanglingMention 0) 0 3) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:368-370
theorem deleteStmt_ubAssign_counterexample :
    (∀ st, ReachableAt SEx pUBAssign 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
      UBFree SEx (deleteStmt pUBAssign 0 0) ∧ ¬ UBFree SEx pUBAssign := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:111-114
theorem ubFree_erasePlaceMention_htgt_counterexample :
    (pMentionUnreach.blk 0).stmts[0]? = some (.placeMention ⟨0, []⟩) ∧
    (∀ st, ReachableAt SEx pMentionUnreach 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
    ¬ UBFree SEx pMentionUnreach := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:105-106
def pMentionUnreach : Prog :=
  ⟨[⟨1, 1⟩], [⟨[.placeMention ⟨0, []⟩], .unreachable⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:361-362
def pUBAssign : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩], [⟨[.assign ⟨0, []⟩ u8 (.use (.copy ⟨1, []⟩ u8))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/RunLemmas.lean:238-239
theorem ubFree_of_refinesPP_rev {S : Sem} {src tgt : Prog} (hrev : RefinesPP S tgt src)
    (htgt : UBFree S tgt) : UBFree S src := by
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:75
def bool2 : Ty := .enum 1 1 [0, 1]
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:128-130
theorem switchToGoto_nonvacuous :
    (pSwUninit.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1 ∧
      ∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1 := by decide
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:186-190
theorem setTerm_nonSwitch_counterexample :
    (∀ a ∈ ([] : List (Nat × Label)), a.2 = 1) ∧
      (∀ st, ReachableAt SEx pHaltEmit 0 (pHaltEmit.blk 0).stmts.length st →
        ((Operand.const (.int 0)).evalInt st).isSome = true) ∧
      ¬ RefinesPP SEx pHaltEmit (setTerm pHaltEmit 0 (.goto 1)) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:160-164
theorem switchToGoto_differentTargets_counterexample :
    (pSwDiff.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2 ∧
      (∀ st, ReachableAt SEx pSwDiff 0 (pSwDiff.blk 0).stmts.length st →
        ((Operand.copy ⟨0, []⟩ u8).evalInt st).isSome = true) ∧
      ¬ RefinesPP SEx pSwDiff (setTerm pSwDiff 0 (.goto 2)) := by
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:71-72
def pSwUninit : Prog :=
  ⟨[⟨1, 1⟩], [⟨[], .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1⟩, ⟨[], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:147-150
def pSwDiff : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int 0)))], .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2⟩,
    ⟨[.emit (.use (.const (.int 1)))], .halt⟩, ⟨[.emit (.use (.const (.int 2)))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:175
def pHaltEmit : Prog := ⟨[], [⟨[], .halt⟩, ⟨[.emit (.use (.const (.int 1)))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:79-82
def pSwTag (v : Nat) : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int v)))],
      .switchInt (.copy ⟨0, []⟩ bool2) [(0, 1)] 1⟩, ⟨[], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/EditSim.lean:348-349
theorem setTerm_refinesPP (S : Sem) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b) : RefinesPP S P (setTerm P l (.goto b)) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:133-137
theorem switchToGoto_equiv_nonvacuous :
    ((pSwTag 1).blk 0).term = .switchInt (.copy ⟨0, []⟩ bool2) [(0, 1)] 1 ∧
      (∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1) ∧
      ∀ st, ReachableAt SEx (pSwTag 1) 0 ((pSwTag 1).blk 0).stmts.length st →
        ((Operand.copy ⟨0, []⟩ bool2).evalInt st).isSome = true := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:197-201
theorem switchToGoto_equiv_ht_counterexample :
    (∀ a ∈ ([] : List (Nat × Label)), a.2 = 1) ∧
      (∀ st, ReachableAt SEx pHaltEmit 0 (pHaltEmit.blk 0).stmts.length st →
        ((Operand.const (.int 0)).evalInt st).isSome = true) ∧
      ¬ EquivPP SEx pHaltEmit (setTerm pHaltEmit 0 (.goto 1)) :=
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:207-211
theorem switchToGoto_equiv_hall_counterexample :
    (pSwDiff.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2 ∧
      (∀ st, ReachableAt SEx pSwDiff 0 (pSwDiff.blk 0).stmts.length st →
        ((Operand.copy ⟨0, []⟩ u8).evalInt st).isSome = true) ∧
      ¬ EquivPP SEx pSwDiff (setTerm pSwDiff 0 (.goto 2)) :=
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:218-221
theorem switchToGoto_equiv_hok_counterexample :
    (pSwUninit.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1 ∧
      (∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1) ∧
      ¬ EquivPP SEx pSwUninit (setTerm pSwUninit 0 (.goto 1)) :=
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:17
def u8 : Ty := .int 1 1
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:42
theorem pSwUninit_beh (b : Beh) : HasBeh SEx pSwUninit b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:44
theorem pSwUninit_goto_beh (b : Beh) : HasBeh SEx (setTerm pSwUninit 0 (.goto 1)) b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:46
theorem pSwTag_two_beh (b : Beh) : HasBeh SEx (pSwTag 2) b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:48-49
theorem pSwTag_two_goto_beh (b : Beh) :
    HasBeh SEx (setTerm (pSwTag 2) 0 (.goto 1)) b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/EditSim.lean:359-364
theorem setTerm_rev_refinesPP (S : Sem) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b)
    (hfail : ∀ ω st0 st, P.initState (S.mode ω) = some st0 →
      Reach (S.mode ω) P (P.entry 0 st0) ⟨l, [], st⟩ → o.evalInt st = none →
      SrcUB (S.mode ω) (setTerm P l (.goto b)) ((setTerm P l (.goto b)).entry b st)) :
    RefinesPP S (setTerm P l (.goto b)) P := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:226-232
theorem switchToGoto_iff_ht_counterexample :
    (∀ a ∈ ([] : List (Nat × Label)), a.2 = 1) ∧
    ¬ (EquivPP SEx pHaltEmit (setTerm pHaltEmit 0 (.goto 1)) ↔
        ∀ st, ReachableAt SEx pHaltEmit 0 (pHaltEmit.blk 0).stmts.length st →
          (Operand.const (.int 0)).evalInt st = none →
          GoesWrongFrom SEx (setTerm pHaltEmit 0 (.goto 1))
            ((setTerm pHaltEmit 0 (.goto 1)).entry 1 st) []) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:240-246
theorem switchToGoto_iff_hall_counterexample :
    (pSwDiff.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2 ∧
    ¬ (EquivPP SEx pSwDiff (setTerm pSwDiff 0 (.goto 2)) ↔
        ∀ st, ReachableAt SEx pSwDiff 0 (pSwDiff.blk 0).stmts.length st →
          (Operand.copy ⟨0, []⟩ u8).evalInt st = none →
          GoesWrongFrom SEx (setTerm pSwDiff 0 (.goto 2))
            ((setTerm pSwDiff 0 (.goto 2)).entry 2 st) []) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:275-277
theorem ref_eval_instance :
    (Rvalue.rawRef ⟨0, [.deref, .field 1]⟩).eval stEx = some (.ptr ⟨some 0, 7⟩) ∧
      (Rvalue.ref ⟨0, [.deref, .field 1]⟩ ⟨2, 2⟩).eval stEx = none := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:92
theorem refOk_ex_pos_dangling_zero_size : RefOk mEx ⟨none, 8⟩ ⟨0, 1⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:91
theorem refOk_ex_neg_null_zero_size : ¬ RefOk mEx ⟨none, 0⟩ ⟨0, 1⟩ := by decide
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:260-261
theorem refToRaw_nonvacuous :
    (pRefDangling.blk 0).stmts[3]? = some (.assign ⟨2, []⟩ .ptr (.ref ⟨0, [.deref]⟩ ⟨4, 2⟩)) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:266-267
theorem setStmt_nonRef_counterexample :
    ¬ RefinesPP SEx pEmitL (setStmt pEmitL 0 0 (.assign ⟨0, []⟩ .ptr (.rawRef ⟨0, []⟩))) := by
```

```lean
-- lean/Toy/PlaceEval/EditSim.lean:479-481
theorem setStmt_ref_refinesPP (S : Sem)
    (hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))) :
    RefinesPP S P (setStmt P l i (.assign dst τ (.rawRef p))) := by
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:56
theorem pRawDangling_beh (b : Beh) : HasBeh SEx pRawDangling b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:58
theorem pRefDangling_beh (b : Beh) : HasBeh SEx pRefDangling b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:60
theorem pRawPacked_beh (b : Beh) : HasBeh SEx pRawPacked b ↔ b = .term [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:62-63
theorem pRawPacked_ref_beh (b : Beh) :
    HasBeh SEx (setStmt pRawPacked 0 0 refPackedStmt) b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:66
theorem setStmt_pRawDangling_ref : setStmt pRawDangling 0 3 refDerefStmt = pRefDangling := by
```

```lean
-- lean/Toy/PlaceEval/Erasure.lean:68
theorem setStmt_pRefDangling_raw : setStmt pRefDangling 0 3 rawDerefStmt = pRawDangling := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:122
theorem eraseMarkers_refinesPP_nonvacuous : NoProvConst pStale := noProvConst_ex_pos
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:88-89
theorem eraseMarkers_noProvConst_counterexample :
    ¬ RefinesPP SEx pConstProvSlots (eraseMarkers pConstProvSlots 0) := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:97-99
theorem eraseMarkers_fresh_noProvConst_counterexample :
    (∀ L ∈ pConstProvFresh.locals, 1 ≤ L.align) ∧ UBFree .fresh pConstProvFresh ∧
      ¬ RefinesPP .fresh pConstProvFresh (eraseMarkers pConstProvFresh 0) := by
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:20-25
def pConstProvSlots : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩, ptrL],
   [⟨[.assign ⟨1, []⟩ u8 (.use (.const (.int 5))),
      .assign ⟨2, []⟩ .ptr (.use (.const (.ptr ⟨some 0, 8⟩))),
      .emit (.use (.copy ⟨2, [.deref]⟩ u8)),
      .storageDead 0], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:46-55
def pConstProvFresh : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩, ptrL, ⟨1, 1⟩],
   [⟨[.assign ⟨2, []⟩ .ptr (.rawRef ⟨1, []⟩),
      .assign ⟨3, []⟩ u8 (.ptrEq (.copy ⟨2, []⟩ .ptr) (.const (.ptr ⟨none, 8⟩)))],
     .switchInt (.copy ⟨3, []⟩ u8) [(1, 1)] 2⟩,
    ⟨[.assign ⟨1, []⟩ u8 (.use (.const (.int 5))),
      .assign ⟨2, []⟩ .ptr (.use (.const (.ptr ⟨some 0, 8⟩))),
      .emit (.use (.copy ⟨2, [.deref]⟩ u8)),
      .storageDead 0], .halt⟩,
    ⟨[.emit (.use (.const (.int 9)))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:30
theorem pConstProvSlots_beh (b : Beh) : HasBeh SEx pConstProvSlots b ↔ b = .term [5] :=
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:33-34
theorem pConstProvSlots_erased_beh (b : Beh) :
    HasBeh SEx (eraseMarkers pConstProvSlots 0) b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:60-61
theorem pConstProvFresh_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) pConstProvFresh b) : b = .term [5] ∨ b = .term [9] := by
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:136-137
theorem pConstProvFresh_erased_fresh_wrong :
    HasBeh .fresh (eraseMarkers pConstProvFresh 0) (.wrong []) :=
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:129
theorem pConstProvFresh_ubFree : UBFree .fresh pConstProvFresh := by
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:57
theorem pConstProvFresh_alignPos : ∀ L ∈ pConstProvFresh.locals, 1 ≤ L.align := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:284-287
theorem eraseMarkers_staleRead_not_equivPP :
    (∀ L ∈ pStale.locals, 1 ≤ L.align) ∧
    NoAddrObs pStale ∧ RefinesPP .fresh pStale (eraseMarkers pStale 0) ∧
      ¬ RefinesPP .fresh (eraseMarkers pStale 0) pStale := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:259-263
theorem eraseMarkers_addrObserved_not_equivPP :
    (∀ L ∈ pAddrCmp.locals, 1 ≤ L.align) ∧
    UBFree .fresh pAddrCmp ∧ RefinesPP .fresh pAddrCmp (eraseMarkers pAddrCmp 1) ∧
    HasBeh .fresh pAddrCmp (.term [0]) ∧ ¬ HasBeh .fresh (eraseMarkers pAddrCmp 1) (.term [0]) ∧
    ¬ RefinesPP .fresh (eraseMarkers pAddrCmp 1) pAddrCmp := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:210-212
def pAlignZero : Prog :=
  ⟨[⟨1, 0⟩, ⟨1, 0⟩],
   [⟨[.storageLive 0, .storageDead 0, .storageLive 1, .emit (.use (.const (.int 1)))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:155-157
theorem eraseMarkers_slots_noProvConst_counterexample :
    RefinesAcross .fresh pConstProvFresh (.slots sEx) pConstProvFresh ∧
      ¬ RefinesAcross .fresh pConstProvFresh (.slots sEx) (eraseMarkers pConstProvFresh 0) := by
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:282-285
def pAlias : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩],
   [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int 1))), .assign ⟨1, []⟩ u8 (.use (.const (.int 2))),
      .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:288
def sAlias : Local → Nat := fun _ => 4
```

```lean
-- lean/Toy/PlaceEval/NonVacuity.lean:290-291
theorem pAlias_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAlias b) :
    b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:154-157
def pLive : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.storageLive 0, .assign ⟨0, []⟩ u8 (.use (.const (.int 5))),
      .emit (.use (.copy ⟨0, []⟩ u8)), .storageDead 0], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:148-149
theorem pConstProvFresh_slots_valid :
    RefinesAcross .fresh pConstProvFresh (.slots sEx) pConstProvFresh :=
```

```lean
-- lean/Toy/PlaceEval/ConstProv.lean:144-145
theorem pConstProvFresh_erased_slots_beh (b : Beh) :
    HasBeh (.slots sEx) (eraseMarkers pConstProvFresh 0) b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:27
theorem pShare_fresh_wrong : HasBeh .fresh pShare (.wrong []) :=
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:34
theorem pShare_slots_beh (b : Beh) : HasBeh (.slots sShare) pShare b ↔ b = .wrong [] :=
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:30-31
theorem pShare_erased_slots_beh (b : Beh) :
    HasBeh (.slots sShare) (eraseMarkers pShare 0) b ↔ b = .term [7] :=
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:17-18
theorem pShare_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pShare 0) b) : b = .term [5] := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:249-251
theorem eraseMarkers_hwf_counterexample :
    NoAddrObs pAlignZero ∧ UBFree .fresh pAlignZero ∧
      ¬ EquivPP .fresh pAlignZero (eraseMarkers pAlignZero 0) :=
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:276-278
theorem eraseMarkers_hobs_counterexample :
    (∀ L ∈ pAddrCmp.locals, 1 ≤ L.align) ∧ UBFree .fresh pAddrCmp ∧
      ¬ EquivPP .fresh pAddrCmp (eraseMarkers pAddrCmp 1) :=
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:296-298
theorem eraseMarkers_hub_counterexample :
    (∀ L ∈ pStale.locals, 1 ≤ L.align) ∧ NoAddrObs pStale ∧
      ¬ EquivPP .fresh pStale (eraseMarkers pStale 0) :=
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:133-137
def pAddrCmp : Prog :=
  ⟨[⟨4, 2⟩, ⟨1, 1⟩],
   [⟨[.storageLive 1, .assign ⟨0, []⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .storageLive 1, .assign ⟨0, [.field 2]⟩ .ptr (.rawRef ⟨1, []⟩), .storageDead 1,
      .emit (.ptrEq (.copy ⟨0, []⟩ .ptr) (.copy ⟨0, [.field 2]⟩ .ptr))], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:13-14
theorem pAddrCmp_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAddrCmp b) :
    b = .term [1] ∨ b = .term [0] := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:40-41
theorem pAddrCmp_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAddrCmp 1) b) : b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:38-39
theorem pStale_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pStale b) :
    b = .wrong [] := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:214-215
theorem pAlignZero_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAlignZero b) :
    b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:220-221
theorem pAlignZero_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAlignZero 0) b) : False := by
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:58-59
theorem pDeadUse_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pDeadUse b) :
    b = .wrong [] := by
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:65-66
theorem pDeadUse_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pDeadUse 0) b) : b = .wrong [] := by
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:78-79
theorem pAddrSelf_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAddrSelf b) :
    b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/MarkerBehaviours.lean:88-89
theorem pAddrSelf_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAddrSelf 1) b) : b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:333-334
theorem pAlignZeroOne_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) pAlignZeroOne b) : b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/Markers.lean:339-340
theorem pAlignZeroOne_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAlignZeroOne 0) b) : b = .term [1] := by
```

```lean
-- lean/Toy/PlaceEval/Simulation.lean:384
def Reach (mode : AllocMode) (P : Prog) (c0 c : Cfg) : Prop := ∃ n t, run mode P n c0 = .running c t
```

```lean
-- lean/Toy/PlaceEval/Simulation.lean:110
def SrcUB (ms : AllocMode) (Ps : Prog) (cs : Cfg) : Prop := ∃ k, run ms Ps k cs = .ub []
```

```lean
-- lean/Toy/PlaceEval/Programs.lean:160
def pHalt : Prog := ⟨[], [⟨[], .halt⟩]⟩
```

```lean
-- lean/Toy/PlaceEval/RunLemmas.lean:254-257
def runFromInit (mode : AllocMode) (P : Prog) (n : Nat) : Outcome :=
  match P.initState mode with
  | some st0 => run mode P n (P.entry 0 st0)
  | none => .blocked
```

```lean
-- lean/Toy/PlaceEval/Examples.lean:170
def stIdx : State := ⟨⟨[⟨4, 4, true⟩], [(4, .byte 1)]⟩, [some 0]⟩
```

```lean
-- lean/Toy/PlaceEval/ZeroSize.lean:16-17
theorem dereferenceable_of_size_eq_zero (m : Mem) (q : Ptr) (τ : Ty) (h : τ.size = 0) :
    m.dereferenceable q τ.size = true := by
```

```lean
-- lean/Toy/PlaceEval/ZeroSize.lean:21-22
theorem readCells_of_size_eq_zero (m : Mem) (a : Nat) (τ : Ty) (h : τ.size = 0) :
    m.readCells a τ.size = [] := by
```

```lean
-- lean/Toy/PlaceEval/ZeroSize.lean:27-30
theorem decode_readCells_of_size_eq_zero_iff (m : Mem) (a : Nat) (τ : Ty) (h : τ.size = 0)
    (n : Nat) :
    τ.decode (m.readCells a τ.size) = some (.int n) ↔
      n = 0 ∧ ∀ s al valid, τ = Ty.enum s al valid → 0 ∈ valid := by
```

```lean
-- lean/Toy/PlaceEval/ZeroSize.lean:48-49
theorem load_ex_pos_zero_size_enum :
    mEx.load ⟨none, 0⟩ (.enum 0 1 [0]) = some (.int 0) := by decide
```

```lean
-- lean/Toy/PlaceEval/ZeroSize.lean:52
theorem load_ex_neg_zero_size_enum : mEx.load ⟨none, 0⟩ (.enum 0 1 [1]) = none := by decide
```

## Boundaries

### Non-claims

Non-claims first, per card. Each bullet is part of the card.

#### `place-evaluation-ub-exact-conditions` (characterization)

- Disjunct (a) is stated over arbitrary states. On states reached by the semantics a frame entry always names an existing allocation and the allocation of an allocated local is live, so (a) means the base local is unallocated (not proved here as a standalone invariant); the theorem itself does not assume this (`basePtr_missing_alloc_eq_none`, `basePtr_freed_in_frame_eq_some`).
- Disjunct (a) models the `StorageLive` documentation's rule that using an unallocated local in any way is UB; (b) and (c) model the MIR `Place` documentation; (d) models its description of `Index` as reading the index local as if by `Operand::Copy`.
- Degenerate edges of `index j sz`: for index value `n = 0` or element size `sz = 0` the byte offset `n * sz` is `0` and no bounds check happens, even on a null or dangling pointer (`evalPlace_ex_pos_index_zero_size`); MiniRust's `PlaceExpr::Index` first checks the index against the array or slice length (not modelled). Index locals are one-byte integers (`idxTy`) decoded with Nat remainder `b % 256`.
- Not modelled: the safe-pointer dereferenceability check and the array-length check on `index` that MiniRust's `eval_place` performs; with either, the characterization would need an extra disjunct.
- In-bounds offsets require a live allocation: an offset of a pointer into a freed allocation is UB unless it is zero (the toy identifies `Mem.offsetInbounds` with `Mem.dereferenceable`, as MiniRust's `ptr_offset_inbounds` uses `signed_dereferenceable`).
- Offsets are non-negative and addresses are unbounded natural numbers: there is no wrapping, no `isize` bound and no negative offset.
- `decodePtr` treats two fragments of different pointers, or a fragment next to a byte, as not a pointer value (UB on load); MiniRust's `decode_ptr` instead decodes initialized bytes with mismatched provenance as a pointer without provenance (spec/lang/representation.md L102–103), so `DerefLoadOk` is stricter than MiniRust on partially overwritten pointers.
- Toy simplifications: `Mem.store` does not check that the stored value matches the type (`Val.encode` writes pointer fragments for a pointer at any type, and little-endian bytes for an integer); `Ty.decode` ignores the size field of `Ty.int` and `Ty.enum` (the length comes from `Mem.load` reading `τ.size` cells); bytes decode with Nat remainder `b % 256`; index locals have the one-byte type `idxTy`; pointers have size `ptrSize = 2` and alignment `ptrAlign = 2`.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `place-evaluation-ignores-final-pointee` (theorem)

- The pointee of the final `deref` is unconstrained, but evaluating the inner place `pre` and loading the pointer from it still requires `DerefLoadOk` (a dereferenceable, aligned cell pair holding a pointer value), by `evalPlace_append_deref_isSome_iff`.
- A non-zero `field` offset after the last `deref` does inspect the loaded pointer (it must be in bounds of a live allocation the pointer is derived from); see `evalPlace_eq_none_iff` and `place_computation_not_free`.
- `field 0` stands for a field at byte offset `0`; Rust's default representation does not guarantee that the first field in source order has offset `0`.
- Equal evaluated pointers for `*p` and `(*p).field 0` do not imply equal access semantics in Rust or MiniRust, where a place also records whether its pointer is aligned for the pointee type (the Reference's "based on a misaligned pointer"); the toy checks the accessed type's alignment at the final address instead.
- The theorem says nothing about loads or stores through the resulting place, which check dereferenceability, alignment and contents.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `place-computation-not-free` (counterexample)

- The instances use the slot assignment `sEx`; the place-evaluation outcome does not depend on the allocation mode, but the program-level statements are proved for `SEx`.
- A misaligned pointer here has provenance and lies inside a live allocation; the null pointer has no provenance.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `place-mention-erasure-refines` (theorem)

- The refinement may erase UB, so it is not an equivalence: `erasePlaceMention_erases_place_ub` (under `SEx`, the failing `placeMention` of `pDerefUninit` and of `pDanglingMention 2` are deleted; each source reaches UB, each edited program terminates).
- Refinement is one-directional: it is the direction a compiler needs, not the direction a verifier of the edited program needs. UB-freedom of the edited program does not imply UB-freedom of `P` (`erasePlaceMention_erases_place_ub`).
- The theorem concerns deleting one statement. Forward refinement composes over several deletions (`refinesAcross_trans`), but single-statement equivalence does not compose to the deletion of several statements: in `pTwoMentions`, deleting either failing `placeMention` alone is an equivalence (`erasePlaceMention_equivPP_despite_reachable_failure` for the first), whereas deleting both erases the UB (not proved here as a separate theorem).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `place-mention-erasure-equivalence-sufficient-condition` (theorem)

- The condition is sufficient, not necessary: `erasePlaceMention_equivPP_despite_reachable_failure`.
- Without `hok` deletion can erase UB: `erasePlaceMention_erases_place_ub` (under `SEx`, deleting the failing `placeMention (*(*pp))` of `pDerefUninit` and the failing `placeMention ((*p).field 2)` of `pDanglingMention 2`; each source reaches UB before any event, each edited program terminates).
- The theorem concerns deleting one statement. Forward refinement composes over several deletions (`refinesAcross_trans`), but single-statement equivalence does not compose to the deletion of several statements: in `pTwoMentions`, deleting either failing `placeMention` alone is an equivalence (`erasePlaceMention_equivPP_despite_reachable_failure` for the first), whereas deleting both erases the UB (not proved here as a separate theorem).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `place-mention-erasure-equivalence-exact-condition-static-slots` (characterization)

- The characterization is exact for prefix-preserving equivalence (`EquivPP`), which requires the edited continuation to reach UB before emitting any event (`[]`). The weaker property that UB-freedom of the edited program implies UB-freedom of `P` can hold when the edited continuation emits further events before reaching UB (not proved here).
- Stated for the deterministic `slots` semantics; exactness under fresh addresses is unknown (not examined).
- The theorem concerns deleting one statement. Forward refinement composes over several deletions (`refinesAcross_trans`), but single-statement equivalence does not compose to the deletion of several statements: in `pTwoMentions`, deleting either failing `placeMention` alone is an equivalence (`erasePlaceMention_equivPP_despite_reachable_failure` for the first), whereas deleting both erases the UB (not proved here as a separate theorem).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `place-mention-erasure-equivalence-despite-reachable-failure` (counterexample)

- Refutes the converse of `erasePlaceMention_equivPP_of_evalPlace_reachable`, not the theorem itself.
- Deleting both failing statements of `pTwoMentions` erases the UB (not proved here as a separate theorem); single-statement equivalence does not compose.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `ub-check-after-erasure-incomplete` (counterexample)

- The checker is an idealized exact decision of `UBFree` (noncomputable), not a tool. A sound over-approximating checker (`chk P = true → UBFree S P`, allowed to reject UB-free programs) is not covered and need not accept the edited programs.
- UB found in the edited program is UB of the source, provided `NoProvConst P` holds for storage-marker erasure: both erasures are forward refinements (`erasePlaceMention_refinesPP`; `eraseMarkers_refinesPP_of_noProvConst`, which assumes `NoProvConst P`), so a UB behaviour of the edited program improves a UB behaviour of the source with a prefix of its trace (consequence of refinement; not stated as a separate theorem). Without `NoProvConst P`, UB in the marker-erased program need not be UB of the source: in `eraseMarkers_fresh_noProvConst_counterexample` the source `pConstProvFresh` is UB-free under fresh addresses while the marker-erased program has a UB behaviour that improves no source behaviour.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `ub-check-after-place-mention-erasure-complete-outside-place-ub` (theorem)

- Proved from `erasePlaceMention_equivPP_of_evalPlace_reachable` and `ubFree_of_refinesPP_rev`.
- The theorem concerns deleting one statement. Forward refinement composes over several deletions (`refinesAcross_trans`), but single-statement equivalence does not compose to the deletion of several statements: in `pTwoMentions`, deleting either failing `placeMention` alone is an equivalence (`erasePlaceMention_equivPP_despite_reachable_failure` for the first), whereas deleting both erases the UB (not proved here as a separate theorem).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `switch-operand-ub-conditions` (characterization)

- Pointer-typed values never evaluate to integers (`Operand.evalInt` rejects `.ptr`), so a `switchInt` on a pointer operand is UB in the toy; at `Ty.ptr`, `decodePtr` does decode pointer fragments, but the result is a pointer, not an integer.
- `decode_int_eq_some_iff` and `decode_enum_eq_some_iff` do not constrain the length of the cell list; in `evalInt_copy_eq_none_iff` the cells are `readCells q.addr τ.size`, of length `τ.size`.
- `Ty.enum` models a field-less enum or `bool` read directly by the operand. In rustc MIR and MiniRust (`ValueExpr::GetDiscriminant`), the discriminant of an enum with fields is read by a separate statement before the `SwitchInt`.
- Toy simplifications: `Mem.store` does not check that the stored value matches the type (`Val.encode` writes pointer fragments for a pointer at any type, and little-endian bytes for an integer); `Ty.decode` ignores the size field of `Ty.int` and `Ty.enum` (the length comes from `Mem.load` reading `τ.size` cells); bytes decode with Nat remainder `b % 256`; index locals have the one-byte type `idxTy`; pointers have size `ptrSize = 2` and alignment `ptrAlign = 2`.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `equal-target-switch-erasure-refines` (theorem)

- The refinement may erase UB, so it is not an equivalence: `switchToGoto_erases_operand_ub`.
- Refinement is one-directional: it is the direction a compiler needs, not the direction a verifier of the edited program needs. UB-freedom of the edited program does not imply UB-freedom of `P` (`switchToGoto_erases_operand_ub`).
- `Ty.enum` models a field-less enum or `bool` read directly by the switch operand. In rustc MIR and MiniRust, switching on an enum with fields reads the discriminant in a separate statement; replacing the `SwitchInt` by a `Goto` does not by itself remove that read.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `equal-target-switch-erasure-equivalence-sufficient-condition` (theorem)

- Without `hok` the replacement can erase UB: `switchToGoto_erases_operand_ub` (under `SEx`, in `pSwUninit` the operand is uninitialized and in `pSwTag 2` it holds the invalid tag `2` of `bool2`; each source reaches UB before any event and each edited program terminates). Positive control: for `pSwTag 1` (valid tag) the replacement is an equivalence (`switchToGoto_validTag_equivPP`).
- Sufficient, not necessary (as for `PlaceMention`, an identical later UB can make the replacement an equivalence; not proved here for switches).
- `Ty.enum` models a field-less enum or `bool` read directly by the switch operand; for enums with fields, rustc MIR and MiniRust read the discriminant in a separate statement (`ValueExpr::GetDiscriminant`), which the replacement does not remove.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `equal-target-switch-erasure-equivalence-exact-condition-static-slots` (characterization)

- The characterization is exact for prefix-preserving equivalence (`EquivPP`), which requires the edited continuation to reach UB before emitting any event (`[]`). The weaker property that UB-freedom of the edited program implies UB-freedom of `P` can hold when the edited continuation emits further events before reaching UB (not proved here).
- Stated for the deterministic `slots` semantics; exactness under fresh addresses is unknown (not examined).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `raw-and-shared-reference-ub-conditions` (characterization)

- `RefOk` does not require the pointee to be initialized or valid (the Reference records that requirement as debated); a zero-size `&` needs an aligned pointer whose address is `≠ 0` (regardless of provenance) and nothing else (`refOk_ex_pos_dangling_zero_size`, `refOk_ex_neg_null_zero_size`).
- Degenerate edge: for pointee alignment `L.align = 0`, `RefOk m q L` fails for every pointer, since `q.addr ≠ 0` contradicts `aligned 0 q.addr` (`refOk_ex_neg_align_zero`).
- `L` is the pointee layout written in the statement; the toy has no type checker relating it to the place.
- Under an aliasing model (Stacked Borrows, Tree Borrows, or MiniRust's `ValueExpr::AddrOf` calling `mem.retag_ptr`), creating `&p` and `&raw p` also differ in retagging and aliasing permissions; not modelled.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `reference-to-raw-rewrite-refines` (theorem)

- Not an equivalence in general: `raw_ref_rewrites_not_equivalences`.
- The refinement goes in the compilation direction: the rewrite `&` → `&raw` can erase UB (in `pRefDangling` the source reaches UB and the rewritten program terminates, `raw_ref_rewrites_not_equivalences`), so UB-freedom of the `&raw` program does not imply UB-freedom of the `&` program.
- Under an aliasing model (Stacked Borrows, Tree Borrows, or MiniRust's `mem.retag_ptr`), `&` → `&raw` also changes retagging and permissions; not modelled.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `raw-and-shared-reference-rewrites-not-equivalences` (counterexample)

- In Rust, `&packed.field` for an under-aligned field is rejected at compile time (the Reference, L97); `&(*raw_ptr).field` through a raw pointer to a packed struct compiles in `unsafe` code and is subject to the runtime alignment requirement that `pRawPacked` illustrates (the toy has no type checker).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `storage-marker-erasure-refines` (theorem)

- Refuted without `NoProvConst`: `refuted_eraseMarkers_refinesPP` (and `eraseMarkers_fresh_noProvConst_counterexample` for fresh addresses, with a UB-free source whose locals all have alignment `1`).
- No slot-disjointness hypothesis is needed for this statement under a fixed slot assignment: in the toy, a source read of a cell that a shared slot clobbers in the edited program is UB in the source (a read after a re-`storageLive` before a write, a read of another live local whose shared cell was reset to `.uninit` by a `storageLive x` of the source, or an access to an unallocated local). This explains `eraseMarkers_sharedSlot_lowering_mismatch`; it is not a statement that slot mismatches require source UB in general: for programs that observe addresses they do not (not proved here).
- Not an equivalence in general: `eraseMarkers_addrObserved_not_equivPP`, `eraseMarkers_staleRead_not_equivPP`.
- `RefinesPP` is behavioural inclusion; it does not require the target to have any behaviour. Under fresh addresses a target whose every oracle choice is refused refines every source vacuously (`eraseMarkers_alignZero_not_equivPP`: the marker-erased `pAlignZero` has no behaviour). For locals of alignment at least `1` the edited program's allocations are not refused merely because of the erasure (not proved here as a separate non-blocking theorem).
- Addresses are unbounded natural numbers, so the fresh-address semantics never runs out of memory and has no stack bound; on a machine with a finite stack or address space, extending lifetimes by erasing storage markers can exhaust memory (not modelled).
- The toy follows the rule documented for rustc MIR that locals without storage markers are allocated for the whole function: for `x < P.locals.length`, erasing all markers of `x` makes `Prog.initState` allocate `x` at entry; a local `x ≥ P.locals.length` is never recorded in the frame in either program. MiniRust's `create_frame` allocates only the return local and the arguments (spec/lang/step/terminators.md L196–200), so deleting `StorageLive`/`StorageDead` there would leave the local unallocated (not modelled).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `storage-marker-erasure-end-to-end-with-static-slots` (theorem)

- The conclusion is an end-to-end refinement from the fresh execution of `P` to the slot execution of the marker-erased program. It does not make `s` a valid slot assignment for the marker-erased program itself: `eraseMarkers_sharedSlot_lowering_mismatch` shows this for a program with UB; for a UB-free program that observes addresses the same can happen (not proved here).
- The theorem covers lowering the marker-erased program directly with `s`. It says nothing about composing marker erasure with a further transformation that is sound under fresh addresses (for example one that moves a write of `x` across another local's live range, which is valid when the two are disjoint) before lowering with `s`; such a composition can clobber values, so `s` must then be recomputed (not proved here).
- Refuted without `NoProvConst`: `refuted_eraseMarkers_slots_refinesAcross_fresh`.
- Addresses are unbounded natural numbers, so the fresh-address semantics never runs out of memory and has no stack bound; on a machine with a finite stack or address space, extending lifetimes by erasing storage markers can exhaust memory (not modelled).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `storage-marker-erasure-shared-slot-lowering-mismatch` (counterexample)

- This is not a counterexample to end-to-end refinement: the clobbered value is observed on a run where the source has UB (the read after the re-`storageLive`).
- It shows that a slot assignment valid for the source need not be valid for the marker-erased program. Every run of `pShare` has UB; the theorem says nothing about UB-free programs (for UB-free programs that observe addresses a slot assignment valid for the source can also be invalid for the marker-erased program; not proved here).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `storage-marker-erasure-equivalence-sufficient-condition` (theorem)

- The hypotheses are sufficient, not necessary: `eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs` and `eraseMarkers_fresh_equivPP_without_alignPos`.
- `NoAddrObs` is a whole-program syntactic condition: it also rejects address observations in unreachable blocks and benign self-comparisons (`pAddrSelf`).
- Stated for fresh addresses. Under a static slot assignment `.slots s`, local `x` receives the fixed address `s x` on every live range and allocation never blocks, so a different (possibly weaker) condition may suffice there (not proved here).
- The statement does not require `NoProvConst`, and it is not derived from `eraseMarkers_refinesPP_of_noProvConst`: its forward direction is proved directly, by a simulation in which every source allocation is placed above the addresses of all pointer constants of `P`, which uses `hwf` (with alignment `0` an allocation sits at address `0` under every oracle and cannot be moved). It is not claimed that `UBFree .fresh P` and `NoAddrObs P` without `hwf` exclude a successful access through a pointer constant with provenance; with an alignment-0 local such an access can succeed under every oracle (not proved here).
- Addresses are unbounded natural numbers, so the fresh-address semantics never runs out of memory and has no stack bound; on a machine with a finite stack or address space, extending lifetimes by erasing storage markers can exhaust memory (not modelled).
- The toy follows the rule documented for rustc MIR that locals without storage markers are allocated for the whole function: for `x < P.locals.length`, erasing all markers of `x` makes `Prog.initState` allocate `x` at entry; a local `x ≥ P.locals.length` is never recorded in the frame in either program. MiniRust's `create_frame` allocates only the return local and the arguments (spec/lang/step/terminators.md L196–200), so deleting `StorageLive`/`StorageDead` there would leave the local unallocated (not modelled).
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

#### `storage-marker-erasure-equivalence-conditions-not-necessary` (counterexample)

- A characterization (iff) of marker-erasure equivalence is not stated. These instances refute the converse of the sufficient condition, one hypothesis at a time: equivalence does not imply UB-freedom, the absence of address observation, or alignment at least `1`.
- `pDeadUse` exercises a use of an unallocated local followed by `unreachable`; it is not a stale read after a re-`storageLive`.
- Programs are closed: there are no inputs and no calls, and reachability ranges over the allocation oracle from a fixed initial state.
- The toy has raw pointers and no reference or `Box` types (MiniRust additionally requires a dereferenced pointer of a safe pointer type to be dereferenceable; not modelled), no unsized places, no `ConstantIndex`, `Subslice`, `Downcast` or `OpaqueCast` projections, no array-length check on `index` (MiniRust additionally makes an index outside the array or slice length UB; not modelled), no aliasing model and no concurrency. Value accesses check the alignment of the accessed type at the final address, not the Reference's 'based on a misaligned pointer' condition.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's MIR semantics, Miri, MiniRust or the Rust Reference.

### Escape hatches

The counterexample cards refute specific candidate statements. For each hypothesis of a theorem card the ledger names a counterexample in which all other hypotheses hold and the conclusion fails, so dropping that hypothesis defeats the theorem as stated; it is not claimed that every weakening of a hypothesis does. In particular: storage-marker erasure is not a refinement once a pointer constant names an allocation identifier (`eraseMarkers_noProvConst_counterexample`, `eraseMarkers_fresh_noProvConst_counterexample`); its equivalence fails once an address is observed (`eraseMarkers_hobs_counterexample`), once the source has UB (`eraseMarkers_hub_counterexample`) or with alignment-0 locals (`eraseMarkers_hwf_counterexample`); and none of these three conditions is necessary (`eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs`, `eraseMarkers_fresh_equivPP_without_alignPos`). The ledgers of the `PlaceMention` and switch cards name the corresponding counterexamples for their hypotheses.

### Hypotheses whose tightness is `unknown`

None: every hypothesis in every ledger is `tight`, with a counterexample theorem stating that all other hypotheses hold and the conclusion fails.

### Dropped or disproved statements

No statement of this package was found false or left unproved: all 21 cards are fully proved. The earlier candidate statements below were found false before the statements were fixed and are kept as proved refutations.

### Refuted earlier formulations (reference points, not results)

The following theorems are refutations of earlier candidate statements about the toy model; they are not claims about rustc or any other compiler. Both refuted candidates lacked the hypothesis `NoProvConst P`; the corrected statements are the cards `storage-marker-erasure-refines` and `storage-marker-erasure-end-to-end-with-static-slots`.

```lean
-- lean/Toy/PlaceEval/Markers.lean:80-81
theorem refuted_eraseMarkers_refinesPP :
    ¬ ∀ (S : Sem) (P : Prog) (x : Local), RefinesPP S P (eraseMarkers P x) := by
-- lean/Toy/PlaceEval/Markers.lean:127-129
theorem refuted_eraseMarkers_slots_refinesAcross_fresh :
    ¬ ∀ (s : Local → Nat) (P : Prog) (x : Local),
      RefinesAcross .fresh P (.slots s) P → RefinesAcross .fresh P (.slots s) (eraseMarkers P x) := by
```

`refuted_eraseMarkers_refinesPP`: under the static slot assignment `SEx`, `pConstProvSlots` emits `5` while its marker-erased version reaches UB. `refuted_eraseMarkers_slots_refinesAcross_fresh`: `sEx` is valid for `pConstProvFresh`, but the slot execution of the marker-erased program reaches UB.

## Evidence

Kernel check (`execution (Lean kernel check)`): `lake build` of `lean/` with `leanprover/lean4:v4.34.1`; Lean's `collectAxioms` over all 1760 declarations of the library reports at most `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declaration occurs. Statement hash = SHA-256 of the Lean `repr` of the declaration's type; closure hash = SHA-256 of the sorted `name : type := value` texts of every package-local constant reachable from the statement (theorem bodies excluded). Both are recorded in `audit/statements.json`, the per-declaration axioms in `audit/axioms.json`. Observed 2026-11-21.

### Main results (card `lean` fields)

| Card | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 |
|---|---|---|---|---|
| `place-evaluation-ub-exact-conditions` | `evalPlace_eq_none_iff` | `Classical.choice`, `Quot.sound`, `propext` | `a9eda40bcd76b2927cde7e2196b21215f7799b4e9ebe522e825042cff97d3231` | `00cdb6991e256167bf7d970ab52ee8911d2906d03d85633b056fcd8404b239d7` |
| `place-evaluation-ignores-final-pointee` | `evalPlace_deref_zeroFields` | `Classical.choice`, `Quot.sound`, `propext` | `6e7b6f67a6cce1ea0b4daa33adccc868d190032b7e870edcc92f04d6078ed166` | `b345c970556b25df721a30663d72e03747e8995dac2f0fe3b0b83e037f2d4cc9` |
| `place-computation-not-free` | `place_computation_not_free` | `Quot.sound`, `propext` | `68972c78dac24ccb7f804e9eb9e020af82d309f9a4c3155810c44ed8e9b4bac9` | `26f99aea93e8700cd88533d21d7f4917e6dd6738fe9d58d4c009103ca8bfe055` |
| `place-mention-erasure-refines` | `erasePlaceMention_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `5494c4b6b94b0f64508c5278c61abafb81ca9d4ce46728da0d20c23d0e25cf3c` | `d72de7e12ebfd103f1febaa2bef7de34e66df652553d87322f401abbb833df9f` |
| `place-mention-erasure-equivalence-sufficient-condition` | `erasePlaceMention_equivPP_of_evalPlace_reachable` | `Classical.choice`, `Quot.sound`, `propext` | `d8a925dfa075da65912dc390f4b83016826c4507334c01ca3977c487adcd3c90` | `725a1d363e27501f6a15710970020c99bb6f0df65367644adddc9fa2f0b19128` |
| `place-mention-erasure-equivalence-exact-condition-static-slots` | `erasePlaceMention_equivPP_iff_slots` | `Classical.choice`, `Quot.sound`, `propext` | `1601438e0385da1263f45131b0f27edb70a45a3beec1d2a705e5c1bdf8a917f2` | `b74f30877f9b4f9b9e4fa3bdaa911819bbe498e2235a2ca1d3134daec2556909` |
| `place-mention-erasure-equivalence-despite-reachable-failure` | `erasePlaceMention_equivPP_despite_reachable_failure` | `Quot.sound`, `propext` | `704678ef9f6a23a445db44d8c679aad42a3a5ec5e319370dec76b297499c042c` | `67d197c247efa7e6c6615f1d1ee8f5fed7f5c715af89b0d808a599958ea6285c` |
| `ub-check-after-erasure-incomplete` | `ubCheck_after_erasePlaceMention_misses_place_ub` | `Quot.sound`, `propext` | `063256defdbf1f33ce4dbee13b86b60ba55db698a19277dae1c115e50ba20fec` | `12640439d85d05eff3caff351c6d91b17c962d3369170eaf1a3314abd7c92056` |
| `ub-check-after-erasure-incomplete` | `ubCheck_after_eraseMarkers_misses_stale_read` | `Classical.choice`, `Quot.sound`, `propext` | `9ce3e04b1783d3ce93fec6f55d4db97ff6344c0a00614a92fbcf461c46886a79` | `1b23c9ffa9a7a400e75a5621ffd516513e84693a68abae7a664cdfd145f2be93` |
| `ub-check-after-place-mention-erasure-complete-outside-place-ub` | `ubFree_of_ubFree_erasePlaceMention_of_evalPlace_reachable` | `Classical.choice`, `Quot.sound`, `propext` | `6d260aae1e313362591b913351cce72ba2d691539dfb3f417781764c20385af8` | `8293af4c44e2c571a033373092796c622513709e53901bd04bac9cc5f6c79769` |
| `switch-operand-ub-conditions` | `evalInt_copy_eq_none_iff` | `Quot.sound`, `propext` | `c422ef776c9835ac30e3c283d9b05d1afa9ee1858cd6590616d3c54995d27d7e` | `9db7a93e667a1c06db2c3c2c1c9abd664211f68e8027800ba1679bd7912ade76` |
| `equal-target-switch-erasure-refines` | `switchToGoto_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `c186879bf33cbcc0ae5d9d96cf8790e18b36559f4a0a47668e02d31023f57f8d` | `2257b1557aef4c0b287994880988ff829fcde1f2062e48870eef395c02b42b49` |
| `equal-target-switch-erasure-equivalence-sufficient-condition` | `switchToGoto_equivPP_of_operand_reachable` | `Classical.choice`, `Quot.sound`, `propext` | `d0675bce4764e192385d62513dd6a523974f94df636fab368a100663c2b6441b` | `558f55434a12e8dd71560841ea751623c30167bbc0e072adf6a7c68edc99b64f` |
| `equal-target-switch-erasure-equivalence-exact-condition-static-slots` | `switchToGoto_equivPP_iff_slots` | `Classical.choice`, `Quot.sound`, `propext` | `e08c91553286a00be5baecbe21e09f326c58f43da53672e19add7393d9b3b232` | `78e8b94e145d569424ca5d070a5bd587a4df27f2a445500986d1e87afc65f770` |
| `raw-and-shared-reference-ub-conditions` | `ref_eval_eq_none_iff` | `Quot.sound`, `propext` | `7d05a33018ff40f950beb99f14b61fe62b2243e968b6065afbf1bce3cbca9453` | `d1cdb3b1b7e62e926a043e8528c388b1d05e3196af1fe61ea89769ee5d35a3e0` |
| `reference-to-raw-rewrite-refines` | `refToRaw_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `e0026c5775ff28b2d515e50b0f2f18546092011a00e850360875c3f056d01d23` | `766ea6e97de79b43125175dcd36f261f2572fb2d4ae4e9d9d5b1b8807e491eab` |
| `raw-and-shared-reference-rewrites-not-equivalences` | `raw_ref_rewrites_not_equivalences` | `Quot.sound`, `propext` | `73d91d71cae433303408afbce0d3889329ff0b9031d344147f2ce360981c3bc5` | `d8f74a8193385b4ed527b5f2db50841b9d2dbf627cd3d68bb5d7ce64ae1bb7da` |
| `storage-marker-erasure-refines` | `eraseMarkers_refinesPP_of_noProvConst` | `Classical.choice`, `Quot.sound`, `propext` | `24beb311f198e3b9978e0cae8c47298b869f4e54dd017efa1414e2b2b1c2266e` | `377184495e82f77d30c291896a1d14a184fe445e83369b3f4294bec5f4c49715` |
| `storage-marker-erasure-end-to-end-with-static-slots` | `eraseMarkers_slots_refinesAcross_fresh_of_noProvConst` | `Classical.choice`, `Quot.sound`, `propext` | `4b8eb297ce9b6e8d9375e9d62295a96fcede49312924ec1e3316871e6ebe9696` | `cc7c5e744c01924df09c1c3747f9e52d9d6fbe7ca17deebb69c5a1b5c17f05bf` |
| `storage-marker-erasure-shared-slot-lowering-mismatch` | `eraseMarkers_sharedSlot_lowering_mismatch` | `Classical.choice`, `Quot.sound`, `propext` | `420ae915c4b77027d07caed0a2cd11e4880cb9e08545a4fbddbf6a689b2ae0be` | `bc39b18630ff4c9e20173a4d72edbc7a99dee0311f6f23609d51b30478b95342` |
| `storage-marker-erasure-equivalence-sufficient-condition` | `eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree` | `Classical.choice`, `Quot.sound`, `propext` | `d675b6e56859f22470ad636f89a397c029cae124416fbca17241b98c8192acbf` | `3ad29e2416a18399030d4e48e4cf8a8a70b7be663d03a91744db127fa9c36449` |
| `storage-marker-erasure-equivalence-conditions-not-necessary` | `eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs` | `Classical.choice`, `Quot.sound`, `propext` | `53c3959e9b1f2fdaf2fc34d4452dbf173ec6f2cd0de75439235eae80450e6828` | `a7fa0a222796a18980a7c81930f61e7756a55cc89be289e6335a05d1de705bbe` |
| `storage-marker-erasure-equivalence-conditions-not-necessary` | `eraseMarkers_fresh_equivPP_without_alignPos` | `Classical.choice`, `Quot.sound`, `propext` | `666c4c57a1dbc655473508f81b556ae25f070c27bf3c366071df59b36f2fbef3` | `e3273d6a1b91cfd22565a008846ad368818a73901f0068307af7f31b4d925c73` |

### Non-vacuity witnesses, positive controls and tightness counterexamples

| Card | Role | Declaration | Axioms | Statement SHA-256 | Closure SHA-256 |
|---|---|---|---|---|---|
| `place-evaluation-ub-exact-conditions` | non-vacuity | `evalPlace_eq_none_iff_instance` | `Quot.sound`, `propext` | `12c3da6bcfde01cff5af37447b33d5ae33eb689d0402716ed3d721ecfed80a8e` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `place-evaluation-ignores-final-pointee` | non-vacuity | `evalPlace_deref_zeroFields_instance` | `Quot.sound`, `propext` | `cd91a9790978b279507b051fd73964e57af7d38b6566a40e7ee572357ea850a1` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `place-computation-not-free` | non-vacuity | `place_computation_not_free` | `Quot.sound`, `propext` | `68972c78dac24ccb7f804e9eb9e020af82d309f9a4c3155810c44ed8e9b4bac9` | `26f99aea93e8700cd88533d21d7f4917e6dd6738fe9d58d4c009103ca8bfe055` |
| `place-computation-not-free` | positive control | `place_computation_zero_offset_and_bare_deref_ok` | `Quot.sound`, `propext` | `c8cbe5feab75653373e70866c8e06211bd875fd157a0c549527fac392631a728` | `b9689b8ce9b2383241e78203779e41eec2a84b6d34ca62782fc86c111f0bc7d4` |
| `place-mention-erasure-refines` | non-vacuity | `erasePlaceMention_nonvacuous` | `propext` | `68d2062bed3849b471707d36d6a97b33763827296b6ddeb7c30d9c2ba98517ca` | `1a1c593da934f7ad127a81873ae228d3af72d4a1419a6292ee81d66d8f15c78f` |
| `place-mention-erasure-refines` | tightness of `hs` | `deleteStmt_emit_counterexample` | `Quot.sound`, `propext` | `8fe106450a5c677c8404d549ea2134431ebf73dfbbcf8bc7dd4f9f621b854475` | `dfa945913f1670031210f7e0956cf34c49d692e74293e61c7652468049564f66` |
| `place-mention-erasure-equivalence-sufficient-condition` | non-vacuity | `erasePlaceMention_equiv_nonvacuous` | `Quot.sound`, `propext` | `c6ffc375fb9e9402d052c31c33bb5868e1b9caca88a2759dc86a547864598152` | `5ffb5c440b7de5e5d886e92f5e997334a4e0fd784b577d9011697893304ce06a` |
| `place-mention-erasure-equivalence-sufficient-condition` | tightness of `hs` | `erasePlaceMention_equiv_hs_counterexample` | `Quot.sound`, `propext` | `ae870ca08ad85b1b524d22344d9b92cd772f8c2ff705668b302e4d4aab8df417` | `8998ce6f83a190f4f002575ade7b8ed5c72d9bd643b6ea7e016f57cf21c9d635` |
| `place-mention-erasure-equivalence-sufficient-condition` | tightness of `hok` | `erasePlaceMention_equiv_hok_counterexample` | `Quot.sound`, `propext` | `c27f6894a0d938f562cf9fcc567cc22f986062ce6ca573beba6eac64812f258b` | `b94dd406abf06af57e39cd84b39c490e2169745926feb0e79809754181c3ecb1` |
| `place-mention-erasure-equivalence-exact-condition-static-slots` | non-vacuity | `erasePlaceMention_nonvacuous` | `propext` | `68d2062bed3849b471707d36d6a97b33763827296b6ddeb7c30d9c2ba98517ca` | `1a1c593da934f7ad127a81873ae228d3af72d4a1419a6292ee81d66d8f15c78f` |
| `place-mention-erasure-equivalence-exact-condition-static-slots` | tightness of `hs` | `erasePlaceMention_iff_hs_counterexample` | `Quot.sound`, `propext` | `0a859a439410f56103ad97fa1155e774edc55c98694904b9fd53043fe3f2a0d1` | `2e8459bcd542f6b805ca0104d924aa053816e022faaf53ed34dbf6c4a736e171` |
| `place-mention-erasure-equivalence-despite-reachable-failure` | non-vacuity | `erasePlaceMention_equivPP_despite_reachable_failure` | `Quot.sound`, `propext` | `704678ef9f6a23a445db44d8c679aad42a3a5ec5e319370dec76b297499c042c` | `67d197c247efa7e6c6615f1d1ee8f5fed7f5c715af89b0d808a599958ea6285c` |
| `ub-check-after-erasure-incomplete` | non-vacuity | `exactUBChecker_exists` | `Classical.choice`, `Quot.sound`, `propext` | `136640db49a551a2ca338a2cd149224ccc70ae972c77664fd29b07855845cd6e` | `7baf5996a35893818fea9f0c24512205676dbc44077e08781ee9ac1de582a0cd` |
| `ub-check-after-place-mention-erasure-complete-outside-place-ub` | non-vacuity | `ubFree_erasePlaceMention_nonvacuous` | `Quot.sound`, `propext` | `392df714deefcc5132858e0ef3110f5edc301b6c4ef882895e6bda9ba0923970` | `d3544f3b7647082cb4eb76c310c6d62bd9ff680a569beb6f2aefefed79b6337b` |
| `ub-check-after-place-mention-erasure-complete-outside-place-ub` | tightness of `hs` | `deleteStmt_ubAssign_counterexample` | `Quot.sound`, `propext` | `b4aba322c216e9f4cc59eb13c588f6088c567d36a11912da835c7b8f3b4ac892` | `b48570f5733000dc543361d2ec781f66cfeee777b219d7ce5529f733a6e3013f` |
| `ub-check-after-place-mention-erasure-complete-outside-place-ub` | tightness of `hok` | `ubCheck_after_erasePlaceMention_misses_place_ub` | `Quot.sound`, `propext` | `063256defdbf1f33ce4dbee13b86b60ba55db698a19277dae1c115e50ba20fec` | `12640439d85d05eff3caff351c6d91b17c962d3369170eaf1a3314abd7c92056` |
| `ub-check-after-place-mention-erasure-complete-outside-place-ub` | tightness of `htgt` | `ubFree_erasePlaceMention_htgt_counterexample` | `Quot.sound`, `propext` | `441ebe80ac52bfad87d066e3cd43b8ef85156eef2f705ff0710d06d9de546a5e` | `4bc35ea660dbe2697a86b685a60ab42ccd35fd8a244302989ca3f086a7c1aa4c` |
| `switch-operand-ub-conditions` | non-vacuity | `evalInt_copy_instance` | `Quot.sound`, `propext` | `59955056d23473b19ac9d6c65861f35daf4d3a79b9c07e9ba23fd8c709dc5a79` | `781b35c1b5e850247f73c483460329ead1148bb60b23b86f4bba361a679e5c3f` |
| `equal-target-switch-erasure-refines` | non-vacuity | `switchToGoto_nonvacuous` | `propext` | `03bc01f3ddad85196042979bd1510c840af2bd18d6830eb2f97530ef5749bb4b` | `8974657061b6c034b33c986cf7584e20339a3c15e856d13a71dc21ed45073ca7` |
| `equal-target-switch-erasure-refines` | tightness of `ht` | `setTerm_nonSwitch_counterexample` | `Quot.sound`, `propext` | `b9b404a42af86d09b6641e8016b0287a4aa0c16aa3f99d8c413503d261af1a5b` | `a6890729eb376413d5b267a597cfe503532091c8e6f583d55a8c69d25757cdd7` |
| `equal-target-switch-erasure-refines` | tightness of `hall` | `switchToGoto_differentTargets_counterexample` | `Quot.sound`, `propext` | `664458b18e7ef9f610203ddfc6d0cc19d0804ec51409e77d7286eda996aa4d30` | `d303662f9f1ff51b7be16a71fb36f960bfa7a5686b8e684aca2123a40723a0b4` |
| `equal-target-switch-erasure-equivalence-sufficient-condition` | non-vacuity | `switchToGoto_equiv_nonvacuous` | `Quot.sound`, `propext` | `22224973b7569528c48646f72e1b834d22fb681d90e882875dd031c601d9afa8` | `9668a9a2cc4366f15f9c4dd575f0a1c1e492ca41d36466ba3dc5395fec175890` |
| `equal-target-switch-erasure-equivalence-sufficient-condition` | tightness of `ht` | `switchToGoto_equiv_ht_counterexample` | `Quot.sound`, `propext` | `4e8eecd3589ddcf3921b10b8431381be7c7a51805787a408ba23e491878b03b5` | `e00d416bb5bf38831266ab6e75bdfdbefc7e539bb4c5e3b9293864d283ccf9e5` |
| `equal-target-switch-erasure-equivalence-sufficient-condition` | tightness of `hall` | `switchToGoto_equiv_hall_counterexample` | `Quot.sound`, `propext` | `1635e021974bf506e523cc872c81a6522242f81f57bdbe40e5ae30f00d7b10a8` | `999a612141eac3e398d530411fb27e6b0340957c5dd67fd60d0c6824717227bc` |
| `equal-target-switch-erasure-equivalence-sufficient-condition` | tightness of `hok` | `switchToGoto_equiv_hok_counterexample` | `Quot.sound`, `propext` | `fd6b8eabdb0985df0e00d185e9399d029d16c920ef52c26e1986ff9149c09c61` | `9796d2206e8f71b958999f9fc26ef3fd92dc425ff14b694a2b4bbdcea49edc7d` |
| `equal-target-switch-erasure-equivalence-exact-condition-static-slots` | non-vacuity | `switchToGoto_nonvacuous` | `propext` | `03bc01f3ddad85196042979bd1510c840af2bd18d6830eb2f97530ef5749bb4b` | `8974657061b6c034b33c986cf7584e20339a3c15e856d13a71dc21ed45073ca7` |
| `equal-target-switch-erasure-equivalence-exact-condition-static-slots` | tightness of `ht` | `switchToGoto_iff_ht_counterexample` | `Quot.sound`, `propext` | `3d24ad2767c0a5cccb5c6e4dee856811e381838914a67805ad05adda6077bd20` | `656289fe9195c628cc2ab97aaf65b8c82857bf7bfb2b0f4252919152f13d0e01` |
| `equal-target-switch-erasure-equivalence-exact-condition-static-slots` | tightness of `hall` | `switchToGoto_iff_hall_counterexample` | `Quot.sound`, `propext` | `7403fe21f8eeccf911722a97cc38c43d96406ebdae86f0678bad7c7d28fe4665` | `dcd3d7ef35c577bc3980c228c6674fab3c92a90975a955c4c6f563826f85d40e` |
| `raw-and-shared-reference-ub-conditions` | non-vacuity | `ref_eval_instance` | `Quot.sound`, `propext` | `b86f83c44ebd5dfd311dc6d2f34d015d1cb2fc1dbe6b25952212e2a464ed0a38` | `dcbd63630bb13de0b035970b0aa2599f19d891a9eea298c5980e237126f3b7da` |
| `reference-to-raw-rewrite-refines` | non-vacuity | `refToRaw_nonvacuous` | `propext` | `30eb57c4f773bc15b375972a2a83916666084f660f0d4739ab2764fd8570a225` | `4cf3594dc1ac39eb7814ff0cd839cd1390ce9771b1123d24f5576cfa0bf9f4b5` |
| `reference-to-raw-rewrite-refines` | tightness of `hs` | `setStmt_nonRef_counterexample` | `Quot.sound`, `propext` | `6174a9ac23c051d24fdcdaf6d022263466173b8e18a793d33ecbbe9552993670` | `487d0ea216a0997aafc98baa87eb9523d54a496d31a4df3623dcd6249410ffdd` |
| `raw-and-shared-reference-rewrites-not-equivalences` | non-vacuity | `raw_ref_rewrites_not_equivalences` | `Quot.sound`, `propext` | `73d91d71cae433303408afbce0d3889329ff0b9031d344147f2ce360981c3bc5` | `d8f74a8193385b4ed527b5f2db50841b9d2dbf627cd3d68bb5d7ce64ae1bb7da` |
| `storage-marker-erasure-refines` | non-vacuity | `eraseMarkers_refinesPP_nonvacuous` | `propext` | `975e58b99047b0b6ea173f3de669532e856360c4f79870e57f9db06b2fbfdb19` | `45fe87c18d38b6e9954a9e452defdb0e4adcf2f16b3a0260644888af51102082` |
| `storage-marker-erasure-refines` | tightness of `hnp` | `eraseMarkers_noProvConst_counterexample` | `Quot.sound`, `propext` | `5d0ba2e3444aa5ec44d7f0cd631dc7626f4b7970197b287e2dc9d0a4db5216c5` | `6789cf6007faffac9b63807c1f2464f1eb23dae130712de9229716105544e1dd` |
| `storage-marker-erasure-end-to-end-with-static-slots` | non-vacuity | `eraseMarkers_slots_nonvacuous` | `Quot.sound`, `propext` | `123800e1ac8b0816efb40f3227f820a2271c8990214d7bc6895724afb50cc8b0` | `6dad1042f5d3510627adf08ccc2f3172e0d93df6089977618dcf7115e6af4c20` |
| `storage-marker-erasure-end-to-end-with-static-slots` | tightness of `hnp` | `eraseMarkers_slots_noProvConst_counterexample` | `Classical.choice`, `Quot.sound`, `propext` | `1b51cf7e87af2aba0de78acb20dbe729e8ae65847426806614a094d1ac3534b4` | `3858754b0cdae49ac4694afc1f8a6875dc23b90e231cc68ff6ce31ea9e7558a0` |
| `storage-marker-erasure-end-to-end-with-static-slots` | tightness of `hvalid` | `eraseMarkers_slots_invalid_counterexample` | `Classical.choice`, `Quot.sound`, `propext` | `a3bafc1cbe21a544002934d340c6d0e498723b685bb74e9b6b4989b6cbd9f8e4` | `282fe8bf73570dc4dc3a671778e6b8983429703b8d4cdbf247f927e05f8d6d15` |
| `storage-marker-erasure-shared-slot-lowering-mismatch` | non-vacuity | `eraseMarkers_sharedSlot_lowering_mismatch` | `Classical.choice`, `Quot.sound`, `propext` | `420ae915c4b77027d07caed0a2cd11e4880cb9e08545a4fbddbf6a689b2ae0be` | `bc39b18630ff4c9e20173a4d72edbc7a99dee0311f6f23609d51b30478b95342` |
| `storage-marker-erasure-equivalence-sufficient-condition` | non-vacuity | `noAddrObs_ubFree_pLive` | `Classical.choice`, `Quot.sound`, `propext` | `d6a35d6f41f5b7308faed725d344202e8ce044b930574ebf55c77ee2d7989692` | `a4a1ee408b0fd52e45d6c11175bb64a036ae5ce475513d8be78774ea252c0ad8` |
| `storage-marker-erasure-equivalence-sufficient-condition` | tightness of `hwf` | `eraseMarkers_hwf_counterexample` | `Classical.choice`, `Quot.sound`, `propext` | `b5bd43147d5ffca08c6fcbcb3b9f8eb0f286a04111e64e9943ecb7448d536a7a` | `d0e811bada73342c0bab7366e02d5bedee331542e971033f28e7f73dd96f5158` |
| `storage-marker-erasure-equivalence-sufficient-condition` | tightness of `hobs` | `eraseMarkers_hobs_counterexample` | `Classical.choice`, `Quot.sound`, `propext` | `0ea2660a16300c82b786163e889e014f6b94f5acddfad8eebf326c951e482b25` | `8db2246766425fb488d9b0c0e285d90ee126624d9e08f711b03936707c7b035d` |
| `storage-marker-erasure-equivalence-sufficient-condition` | tightness of `hub` | `eraseMarkers_hub_counterexample` | `Classical.choice`, `Quot.sound`, `propext` | `e5b1e90df68aa297c8dfac908e568b41e3d171d35baa82cdb0c6d338b62a7fa1` | `5f3d4d0ec3e9d9b31667dbda46eceb1327da11edf0f589ca5fcba604de7b0524` |
| `storage-marker-erasure-equivalence-conditions-not-necessary` | non-vacuity | `eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs` | `Classical.choice`, `Quot.sound`, `propext` | `53c3959e9b1f2fdaf2fc34d4452dbf173ec6f2cd0de75439235eae80450e6828` | `a7fa0a222796a18980a7c81930f61e7756a55cc89be289e6335a05d1de705bbe` |

### Definitions and auxiliary declarations cited by name (`lean_names`)

| Declaration | Axioms | Statement SHA-256 | Closure SHA-256 |
|---|---|---|---|
| `Alloc` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `AllocId` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `AllocMode` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Beh` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Beh.HasPrefix` | none | `26f89e1a072ef3a93a730f13d631076b1ddf84704e2db5b49d9ff00302b817a7` | `6009d50f06d5ceba3c7c702f8c1f5e99d2b7bef8400d3cccfcdf966d6888275a` |
| `Block` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Block.unreach` | none | `e46a6775e006d055aebb5309723e9a78a75af6037c809a901c6a0f4ae9e1e1c7` | `c7f03bef57bc2108220e7f8522a7a4528228737390fa3d36362e22b9e01e671d` |
| `Cell` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Cfg` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `DerefLoadOk` | `propext` | `c4a5d11cfff628600b17d3cf13b84df26daad843e8f34121bc4bcd7192564a7c` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `EquivPP` | `Quot.sound`, `propext` | `226a0d6522f2e71817c562376b600774fd5acf7b62b49422fc16880ebe14d4a1` | `20fd9eec067bbec2ef02dd0d326c444d4734b516493e6b9df68dc03c93789039` |
| `ExactUBChecker` | `Quot.sound`, `propext` | `2401411dd12566da58cc81cdaa82d961170e62753ea56627c0a306063bdb4e26` | `20fd9eec067bbec2ef02dd0d326c444d4734b516493e6b9df68dc03c93789039` |
| `GoesWrongFrom` | `Quot.sound`, `propext` | `5bef751fc2c6008d817f48d8ff7254ccbb3c736a8373c3beef00c89a4bcf50b3` | `6e48be2c955dc991eb7927a6645651088d6ddc118c484ad3aa03e1b8ec581721` |
| `HasBeh` | `Quot.sound`, `propext` | `93f945ca7cf9f417fe911d4b6e76c058fcd72f74708334e1b73b7015b1e9483c` | `cbff3f43acb63883b39b66030117c8ae41946ee627913d4b79256ef667d2c253` |
| `HasBehFrom` | `Quot.sound`, `propext` | `e6394c04b3459b4cd72dccba70d583431430daf2d580704a61f3248ab4cdaeeb` | `4256862ce7ad921e7c3500db43a974012835a5a9899409645104bc21fee6481f` |
| `HasBehIn` | `Quot.sound`, `propext` | `531c715a1bd7279d057969faaea22600240d369ce6031c66f5312eb86886aea7` | `134a74390dbbea2cd9f02dcceab309d3a92ae90e0bc1b44881d4d25b617d89c5` |
| `ImprovesPP` | none | `26207f14509503fd5c8a67bf2aee74a8194c4251d679a5324c6f6dd3de3d4e07` | `6009d50f06d5ceba3c7c702f8c1f5e99d2b7bef8400d3cccfcdf966d6888275a` |
| `Label` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Layout` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Local` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Mem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Mem.dereferenceable` | `propext` | `db857a070b1086405356db143667c25dd1c3329fdc1a96f242eeb8a6ce64fed4` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `Mem.get` | none | `d6644d8b1e67cb71ad3054582664fb52edc2747134ffcad57f5e4ed5fc9a73a9` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `Mem.inBounds` | `propext` | `db857a070b1086405356db143667c25dd1c3329fdc1a96f242eeb8a6ce64fed4` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `Mem.load` | `Quot.sound`, `propext` | `9daae29e2b9c8ef81ac8cddb90c48e9d82645b02b08ab5b9df3918309999c38a` | `41bbde78379a99ff984f49be5a7887f6d029ca0bab9ad260818939e2adba88d4` |
| `Mem.loadPtr` | `Quot.sound`, `propext` | `1f66296acbf27232a072b15612b5a7a8548bbcbbab9876cd15091cefe5a30e8e` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `Mem.offsetInbounds` | `propext` | `a49e443351ed628bc378459ad17ba425eb75c30069838ff9cead392b5a8bec2a` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `Mem.readCells` | none | `c56b6105d9ddcf08705cab88ac2489e4ece5a4d71c00097b1c51a3de39addd58` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `Mem.store` | `propext` | `582c966d54b286f39ce6e15a4999041adfbfccc8c566585ba363ce562480bea2` | `41bbde78379a99ff984f49be5a7887f6d029ca0bab9ad260818939e2adba88d4` |
| `Mem.writeCells` | none | `ec1801a30b25af64cfb64f9c8789e098677f142996052ae025718e446a9b0ebd` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `NoAddrObs` | `propext` | `e5dbc6af24176d603a2af3725aee2315b563d0c23322ee37573f7e0f1d91f588` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `NoProvConst` | `propext` | `e5dbc6af24176d603a2af3725aee2315b563d0c23322ee37573f7e0f1d91f588` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `Operand` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Operand.eval` | `Quot.sound`, `propext` | `5ce99d1f62185d56e0867763dbfe8efcc50c4f2a35d727e8f0fea71e9c10e057` | `ba0cd58df5f95dd524341dc5bbf6c86ee78dc6f88551f37011c3d639b8cd7abb` |
| `Operand.evalInt` | `Quot.sound`, `propext` | `bc64cfb055389a514b4c51ea330e4ac4a53ecdfdbbe77ac57af1b4f17e3e5bff` | `ba0cd58df5f95dd524341dc5bbf6c86ee78dc6f88551f37011c3d639b8cd7abb` |
| `Operand.provFree` | `propext` | `68582f72bf638cac064329d9be75694a8d2ca14349d0a80662c3db948c542bce` | `a5d45257ebb269f69e86ca6dab2545cc816e42259c6a40eacc1afc6a280c54f1` |
| `Outcome` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Outcome.cons` | none | `8340f118274fe4c061864c3820fb56f88e2a7e17a131b2046ebe65b80e6749e6` | `d6061571bc0b80a6504e7573d4813dd3f25602d75392032264fab786fdf369cc` |
| `Outcome.isRunning` | `propext` | `eb135b09dd7f27ff0c7f25d6cd7b1eeff78c332b67f9270d8871e4d0e5a72649` | `d6061571bc0b80a6504e7573d4813dd3f25602d75392032264fab786fdf369cc` |
| `Outcome.trace` | none | `56127b2b623721c06b3a3b577b0d839b97d76ddd84c390454c898a8f2041e1bc` | `d6061571bc0b80a6504e7573d4813dd3f25602d75392032264fab786fdf369cc` |
| `Place` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Prog.at` | `propext` | `6593a6eb348c78027923d4c698bf32e3af01d68f9fc486c5fb61510c250f982b` | `69235449ce04e0c652f83bbad0f44bff588d32ed8e684aa5677af4fa5e535fe0` |
| `Prog.blk` | `propext` | `a86c005e2f5bfc62df382a43d476e9a9ccb83835fd2ba064ae7ff10ab834e04e` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `Prog.entry` | `propext` | `4af5daecb3cdf3cac5eee2764e78d7b49fcb3cad08de4255c9efa966ac0697a0` | `69235449ce04e0c652f83bbad0f44bff588d32ed8e684aa5677af4fa5e535fe0` |
| `Prog.hasMarkers` | `propext` | `1ddd6340ab6e8c5d80c0c305f0ce3935f6debbd5b0f45dcc0ca183547e2e4c19` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `Prog.initState` | `propext` | `f705ca8ea4a35f374227dee9ecf23fc91e4df136006f259e81a4b21a732c020c` | `bfde42801ea8a41a0e3368224747cc65daa97c5d4cb6942c64594dd275fb7dc7` |
| `Prog.layout` | `propext` | `4c8ff802b3ffbf7fa15af116752e45f090d5459cf42f852d3ce96100bfec736e` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `Prog.setBlk` | none | `dac8d5e73c1e18bd88b101a3b80f9145c7ea3a28e4673760769018bf4dfdcbab` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `Proj` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ptr` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ptr.offset` | none | `49377dea4dd2fe63d2be1a95675e334012d15dce1ac706afa7211177f0d59792` | `ea9227670ef3077951659ae3931e2121fc7cc185cdfa47cf9e32e9de0b66fde5` |
| `Reach` | `Quot.sound`, `propext` | `5a5702124255954be3a693717f3804d70ef32eb3f1ded56070848acb5f4bdbd0` | `1922248d6b996e066b8e145b2e5928db28056856577c27c40ce4912cb781b905` |
| `ReachableAt` | `Quot.sound`, `propext` | `28ce16b8930ca2e2278d2ac21a4ef30f2cbedd26d845cb78bb3f1c0de5b3332f` | `e6cd9e48181a962d10f16dc1ec0f48c47081e636dc11e123991f85cec2b89dc8` |
| `RefOk` | `propext` | `feac55f385dd27881ff3d57f0dd2b7f3a10d088ea39e89d409ec7626939ed179` | `b570b7f2d87f58a6c9eac0ae48838f1bd5a1998c4799fc1f659e96d966c112ce` |
| `RefinesAcross` | `Quot.sound`, `propext` | `d5dd348271a7ff1e54f8dc43b432308c694647c09c0c7431cf04a2a114af7b3f` | `20fd9eec067bbec2ef02dd0d326c444d4734b516493e6b9df68dc03c93789039` |
| `RefinesPP` | `Quot.sound`, `propext` | `841a523875728dfbd42fd1ba2f8697ed560a9ff841f68837bcf05c129aa4a5e5` | `20fd9eec067bbec2ef02dd0d326c444d4734b516493e6b9df68dc03c93789039` |
| `Rvalue` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Rvalue.eval` | `Quot.sound`, `propext` | `fe79bf6876f61850cbbef7fec4030ab3d8c370c1ee1125671b1fdefd66bc49dc` | `f4ea7742b61c78e5e0cd06559d5774b84b858b941d2e7f6278e85d26e667d2d7` |
| `Rvalue.observesAddr` | `propext` | `ce8a404b46f254341d3bab0a6592a90fb5e3fa84cf14c38e80adfb3166cc847a` | `e2dee48c5da7ef4eb7836367d0dcf071e98382816fc3441b98c25a1dcef30723` |
| `Rvalue.provFree` | `propext` | `ce8a404b46f254341d3bab0a6592a90fb5e3fa84cf14c38e80adfb3166cc847a` | `e2dee48c5da7ef4eb7836367d0dcf071e98382816fc3441b98c25a1dcef30723` |
| `SEx` | none | `316b344511732acb06f9cb6fd3232ae9aa6e8e8e2045e6bde7c3b99c5f414ecf` | `396ce0629852a5451de185bc3593cf8c8eb35942f50705309b5c70b655649048` |
| `Sem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Sem.mode` | none | `faa5e6c5b37acdc6c79bb0055b500a40315ce93413d9e893a771992b55f61865` | `b5efd2cad6b7680947f38a14d67e028df30376217b464b048c5b2c3906ba0657` |
| `SrcUB` | `Quot.sound`, `propext` | `e100deead5d2b4b4b97957bc4208522ae6cd401e205423ba375585a22f2ad068` | `1922248d6b996e066b8e145b2e5928db28056856577c27c40ce4912cb781b905` |
| `State` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `State.allocOf` | `propext` | `8d838bc12bc699a6dad3b022b89cbafe101e7b7daf802d91ad682f0f674c7b2e` | `17e11fb8bcb6384cf5e0e48c1e860905104fe81ceecd9d9e0df9b1c207242bd9` |
| `State.basePtr` | `propext` | `c3b0d5b3337c218a78578ceb47e14dede7b33434f2c2a46ef91616c3acef4de0` | `17e11fb8bcb6384cf5e0e48c1e860905104fe81ceecd9d9e0df9b1c207242bd9` |
| `State.readIndex` | `Quot.sound`, `propext` | `4372879f84072e7b8f17315332a063096ae10a15d6692ee9ad2f63791ae3391a` | `17e11fb8bcb6384cf5e0e48c1e860905104fe81ceecd9d9e0df9b1c207242bd9` |
| `State.readLocal` | `Quot.sound`, `propext` | `a590857d83dc4c37921b80f828520e38372ea92e1dc7642dc7226285c8f5a416` | `58dfa63ecf951c40c28891d4faaadc2bfb095dde5e06928dc166cea976a782aa` |
| `StepResult` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Stmt` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Stmt.isMarkerOf` | `propext` | `3e542f36239b376751e7b219861a6dd582537efe1d2a6331581c54d55cf9ff29` | `b0bc851740216dda5ff1ee859dfa28582dc33d05e16259f7a8785cfea19ae844` |
| `Stmt.provFree` | `propext` | `3c8ea45d37a8fce8e0f54a4ca1d90263b153d934f606edfdde034d030ceacae1` | `b0bc851740216dda5ff1ee859dfa28582dc33d05e16259f7a8785cfea19ae844` |
| `Stmt.rvalue?` | `propext` | `2647e92ebfe3bbd5b821df05643b027e225078e3e2534b7843312f77919b4218` | `b0bc851740216dda5ff1ee859dfa28582dc33d05e16259f7a8785cfea19ae844` |
| `StmtResult` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Term` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Term.provFree` | `propext` | `53287684b2ddeae07c40c1304f3c73164d58ab32ca4f48fd4b0f5a31f77c40e2` | `8f62ef23038b9c85b143cabe33c435b2c082676d9cb67484106e05930083f215` |
| `Ty` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ty.align` | none | `5b196060a1ae3363eb0d53fe6523aff762c17f3e18d357369844008dc59e12c8` | `310e28576f0941ff5da3498561704497e13d233ec01f18410c5f2bba807424dd` |
| `Ty.decode` | `Quot.sound`, `propext` | `b957912a29521470c92ffd6ef329b7f1231134af2abe2b69b8b8448bf92cd8ec` | `dcca4cd6cfdbec9f76396adbbd56e115ee84174d1a2eb0fb87b8d2dbbb0a6db8` |
| `Ty.size` | none | `5b196060a1ae3363eb0d53fe6523aff762c17f3e18d357369844008dc59e12c8` | `310e28576f0941ff5da3498561704497e13d233ec01f18410c5f2bba807424dd` |
| `UBFree` | `Quot.sound`, `propext` | `48954c04e2bb7261ae650ee6feb9e31a756c6d987bc30da00053297d46b0b345` | `20fd9eec067bbec2ef02dd0d326c444d4734b516493e6b9df68dc03c93789039` |
| `Val` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Val.encode` | none | `790bb02b0730fbe1a3a9ffe6a488a89c88d3a5d2fbd61a677e34cc0ac56473e8` | `6ebb710f91d2f0c33f11aaa9ba7a50db5775a0013d9252eeccc8bee48b36405d` |
| `aligned` | none | `bd46913f091fa235d036ed0f29de791c7be62b24ab984df0630d6e6087730a91` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `aligned_ex_neg` | none | `2f5213f5b745345d5ed209f00eca50f77a60700219f43d4ce06c4aee290c4736` | `e72144ff46576273c80f133c3d5427781dec363c2788e8a04997ef3692f8542c` |
| `aligned_ex_pos` | none | `4be7ed75c0e754df7cd82132aabaeb7cdadd6ec3e594c8307a8fbbaf07999dc8` | `e72144ff46576273c80f133c3d5427781dec363c2788e8a04997ef3692f8542c` |
| `aligned_zero_ex_neg` | none | `d9177f9d24bb1e644806613081f860c2ada3cd19b62ebcc5ce692db247f1af1e` | `e72144ff46576273c80f133c3d5427781dec363c2788e8a04997ef3692f8542c` |
| `aligned_zero_ex_pos` | none | `41e30a9dbb7a750644e3a7424b0730d1d85d4742f3842dae7126e0ceb4def77a` | `e72144ff46576273c80f133c3d5427781dec363c2788e8a04997ef3692f8542c` |
| `allocEntry` | `propext` | `05fec5c652309561f15a9b0aa2e950eecc0891de69105cbb5e880efc8528b28a` | `bfde42801ea8a41a0e3368224747cc65daa97c5d4cb6942c64594dd275fb7dc7` |
| `allocate` | none | `1d353f9e4dc15949f99088b1fd31f91cbc4b31f163e6d20fd027be0f23b90482` | `34a94ead2bc65cd773320eb640ea57d395263e2c46981323bda44de17edfb960` |
| `allocate_fresh_ex_neg_overlap` | none | `11dc919c61d99a534d821f747bb215eeb7157f7aa2025652ea64b20db8a50483` | `0eb0eb91f6b8bbb1726cd3544202b184b6ac7f9550cc352fd7c5d5d8152c8163` |
| `allocate_fresh_ex_pos` | none | `b7231e5b68ffe5874cf4908223f9701bd824f1c3e45d9722e2dc37058c77d662` | `0eb0eb91f6b8bbb1726cd3544202b184b6ac7f9550cc352fd7c5d5d8152c8163` |
| `basePtr_freed_in_frame_eq_some` | `Quot.sound`, `propext` | `7d57538ff84859f758c5c049d500ebac5228184569a8b4f601152f1dba82a4de` | `e0ce14391d928475187da180e4ee4c42f3462b31a3a433b4994fc6e15e4b4c70` |
| `basePtr_missing_alloc_eq_none` | `Quot.sound`, `propext` | `e8d49c158854d0bfb6359904691ddcaa7713c1840382e8c0325fc4506bbbfca4` | `698fddad43cedb0302a41804211d88f4946bbcc7717c3f0def3cb032f441f87e` |
| `bool2` | none | `5b2c786b78f362c0ccbd2922fff5944f2af0b820835e224182fee1a08495e24c` | `310e28576f0941ff5da3498561704497e13d233ec01f18410c5f2bba807424dd` |
| `deallocate` | `propext` | `c26958281de8bd552c18370b272e6716600b174aa8ed3235e3575482b2fbaec3` | `17e11fb8bcb6384cf5e0e48c1e860905104fe81ceecd9d9e0df9b1c207242bd9` |
| `deallocate_ex` | `propext` | `ddd636c911c4bc84c8e73d006e5023cfefbb9832b43a5032dca6209252058561` | `81c820e96b4bf9ebe2f9dd2fd0126fa1cf1d5d4293ca6fb6bd4e4e53884f0465` |
| `deallocate_ex_noop` | `propext` | `c86c090288d79c920d5819c6c0f21aafbc381f126a050cf46369ae6b001a743a` | `f7f813336f3bb2861dddea27419a323885a5d105c4b5d241f98d5f1d58e51eee` |
| `decodeLE` | `propext` | `b342e035a99b7447c3f0887cbd82460ecbcc30a500c4e10ffcfe92a74483f988` | `96b57538ed7294537adf2cada28bddacb158f14a55987eb91e703bafefba0af6` |
| `decodePtr` | `propext` | `3221c40a43ea9a09fdf99a40bb0885361d0a93f6b512949087b307c57c7451e3` | `96b57538ed7294537adf2cada28bddacb158f14a55987eb91e703bafefba0af6` |
| `decodePtr_ex_neg_mismatch` | `propext` | `14bdb3d808d266ec31e7afce0c56836f20f998dab057626fe4bc46721e083624` | `2f1ba8cb342c2298469948a3ae1fa78f662ce0e2179049b99fb10d467f4c4472` |
| `decodePtr_ex_neg_uninit` | `propext` | `644d53297456e012475e86b5ba85d036353d0bdc7a547dba463ccfb6a35a4d38` | `2f1ba8cb342c2298469948a3ae1fa78f662ce0e2179049b99fb10d467f4c4472` |
| `decodePtr_ex_pos_bytes` | `propext` | `12ee421f7febdc3510143b88a3e56b13bd213286d8b712a9766eccdc7c945958` | `2f1ba8cb342c2298469948a3ae1fa78f662ce0e2179049b99fb10d467f4c4472` |
| `decodePtr_ex_pos_frags` | `propext` | `2a80bf543bc01f7c61c9129e3a80617273815465127323e1248acabeea0ec4e7` | `2f1ba8cb342c2298469948a3ae1fa78f662ce0e2179049b99fb10d467f4c4472` |
| `decode_enum_eq_some_iff` | `Quot.sound`, `propext` | `b4204c6cd435a4e93ed09f7901857d1f3a7af68bf7e3b4ab5ad6dfb3dfede248` | `233434b9b1064e0998260b453437f6adac9918ee699078d4936787aa6805f9b7` |
| `decode_enum_ex_neg_tag` | `Quot.sound`, `propext` | `d1dda99a06ff210b683c0dc97be7e047f5c6b5c0ee029fc92040b32fc5ca872b` | `63651117e6438d35a7012d3f183e05324438552d94696fa6aa00f4f2ad382a44` |
| `decode_enum_ex_pos` | `Quot.sound`, `propext` | `da0f6d79d6a08adf1f36ab770f1857b5b502ce6487ba87bb7ad283acd7a54dfe` | `63651117e6438d35a7012d3f183e05324438552d94696fa6aa00f4f2ad382a44` |
| `decode_int_eq_some_iff` | `Quot.sound`, `propext` | `f1309610b365cbc44293a9604bae0d8ad3701671c596aa6308ccacbd84b7e4d9` | `233434b9b1064e0998260b453437f6adac9918ee699078d4936787aa6805f9b7` |
| `decode_int_ex_neg_uninit` | `Quot.sound`, `propext` | `422d9f4dc9105f6a649bc6ea81961f7c13a9f077f46301c18e590bf369c1e027` | `3b7468efdeff89b33bbde502e930b33bc0dca792e348b729ead2742ac24a4a41` |
| `decode_readCells_of_size_eq_zero_iff` | `Quot.sound`, `propext` | `261d3279fbbdf43b1d0de3459fa2e50cf4d7b5afe6f9b624800f3d57c83b31b7` | `459d0be98a46acc9863ddf69c8044f6e74bfd5f438851e3f65c0883718116a2d` |
| `deleteStmt` | `propext` | `e77d8920dd6a121725f3e47d5dad72bb78a2b687808d63c34a13f018a33aa77f` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `deleteStmt_ex` | `propext` | `059d2d28893db3e4cc84f69ba499c951de8a445b5c01ed75e873c40841d66652` | `e5b41dab7e80680e4869cb5017bc4ee7ac7495ddabf5481495a923323245b799` |
| `deleteStmt_ex_out_of_range` | `propext` | `fb6176111d73b333c43414df3d489066dbd07ff069dfd0edd04161e5e46404e1` | `e5b41dab7e80680e4869cb5017bc4ee7ac7495ddabf5481495a923323245b799` |
| `deleteStmt_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `a5cc8b3ff49cffa13b3afcb325629cc3c340563490c341ab1376177090811e6a` | `d72de7e12ebfd103f1febaa2bef7de34e66df652553d87322f401abbb833df9f` |
| `deleteStmt_rev_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `212d11e7e0ea8cbe36c885abbb939de49345603bf8fa08e6c5ed3e50af64a80e` | `78737ae5981fcf6a2cb79aad4949f6cc0b01f9eee24f71d347e739c991515523` |
| `derefLoadOk_ex_neg_not_a_pointer` | `Quot.sound`, `propext` | `99089bfc9acdd13ecce246ace700a680321961cc512933bb99c067924cc0f209` | `e31a474145e9a44f357f727fd203924a58cad4aa2f4981e0259d167e89285bbf` |
| `derefLoadOk_ex_pos` | `Quot.sound`, `propext` | `df5b3b82f872df97e73466155e3da7bb8b86fbf4b7f7dcd0a0deae8a0b7d4781` | `e31a474145e9a44f357f727fd203924a58cad4aa2f4981e0259d167e89285bbf` |
| `dereferenceable_ex_neg_freed` | `propext` | `2be1abb83c744c900abffd8ccb5a593280127f544edcdf3ba3dc2c7c70ba9ac4` | `d42579d101a254dd3cafa1bc095dc7fdafc085759d4434e453c15e316909db5f` |
| `dereferenceable_ex_pos_zero_null` | `propext` | `879b3d5d59c4aa3936ea48fa6af25c9810a4946902d0b77d59f8c462fd9ec2d5` | `d42579d101a254dd3cafa1bc095dc7fdafc085759d4434e453c15e316909db5f` |
| `dereferenceable_of_size_eq_zero` | `Classical.choice`, `Quot.sound`, `propext` | `7109e49cc6c08dc95cccab1206709aab1bd1ea45f2d7eff41eb9b4a19147433e` | `c17908084f5de4524f3f00f44098565de63edf641b2bb7a6759a7dd789a1c064` |
| `disjointRanges` | none | `0a718321208e0a6504dbcc4b1dd653b174bb64ad54f7d850ae3a6fa3f1c679bd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `encodeLE` | none | `ec7242b103b46cf0ad37d44727b8a9eebf9b40a0adcce563c4d693b925cba560` | `96b57538ed7294537adf2cada28bddacb158f14a55987eb91e703bafefba0af6` |
| `eraseMarkers` | `propext` | `1867fbe2d514b1df1f32a46df7b8f18d642605a400da87f48dac7caa5e8330af` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `eraseMarkers_addrObserved_not_equivPP` | `Classical.choice`, `Quot.sound`, `propext` | `f637c7a0ea4afdf18ec3fd5de4b5b207374d8b75929bc7607f232e725e8e76a8` | `644dadd00a697a025259983a6e1d26ba05a5662766bb3610909b1b7a964fbe4f` |
| `eraseMarkers_alignZero_not_equivPP` | `Classical.choice`, `Quot.sound`, `propext` | `d45a68a382677837592061370d5ceabd76fc2c8320143adffc667cdb831d950f` | `11931fe7ba108f55d2cffedca14d167b2a2ca4b663043fb14210a9d0a2a578b2` |
| `eraseMarkers_ex` | `propext` | `5b79f8e2d4252f7135112c15e3e7a9dfb7605cb57656cc9ecc7bd6105c35e8bc` | `eb8efef2abcd87a515f5ec673c4676d90265e1dd50a535ff36acbbad7d7ce4c8` |
| `eraseMarkers_ex_other_local` | `propext` | `30b360a937adcaf20946f9af5f2184e8726020dc4dc2b6bc715ea3759e37b322` | `cbb1294046d96717e7e20f86fbad49fb1b52537ba18308f4c5e4f9eaed1224db` |
| `eraseMarkers_fresh_noProvConst_counterexample` | `Classical.choice`, `Quot.sound`, `propext` | `d05d3888a485cd6cf25938d66c68033939d7baad9c08bed1f92efff6f3a9fcef` | `8a81a57aa5929d6d8e7bc45055aef61b6d16535b8fc7f0ecd742b3e31d2bffa1` |
| `eraseMarkers_staleRead_not_equivPP` | `Classical.choice`, `Quot.sound`, `propext` | `48248defe4d0d5a7493526e94d3853932d2add26b9d3df432969e3f88713639c` | `786cc6e36a0d45d97b41678c776ff7cc45bd39fb5bf22810bb7994a66a51aee6` |
| `erasePlaceMention_erases_place_ub` | `Quot.sound`, `propext` | `3b4a344e9cd81760ca8d30332343d51f7597628bd623a6f12076510512916da6` | `d03f790992096b19faeac354dbab454310f0a003304a0fd0ccb2a09d6ee38b5a` |
| `evalInt_ex_pos` | `Quot.sound`, `propext` | `95de92c8034565021ba44cec2f73541f4ad1dd291ff8081f70a747d64fc025f3` | `84914311ff2a75548d9c17350a6400472a745386cbf4277c2c5e0b21e9b762bb` |
| `evalPlace` | `Quot.sound`, `propext` | `01b4907b4f459d57b72fac74e14ef41ba6f3650a07a78548c26eda5bea93da05` | `1c59682a5754e73dcf77184c4ed0b1f6787a5fcdf91329ddb062893510de21ef` |
| `evalPlace_append_deref_isSome_iff` | `Classical.choice`, `Quot.sound`, `propext` | `8cf667f5c9dde294a7ddaa05fc3870d82afb11d218b633cd8a09c5dfcf2f1ecc` | `753088fb3dda128a622640cd40b88b1e827ecb2b9434e8f2765c6ee7b6a05e30` |
| `evalPlace_ex_neg_field_past_end` | `Quot.sound`, `propext` | `b591556c85e8a2346d919b5353b25b1d757d1714e39d27899e2281f0adfdb1ce` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `evalPlace_ex_neg_index_dangling` | `Quot.sound`, `propext` | `4dfdf75b0c9497351b7eaefc46c934666983496eab52d2bfafc377ba0df47232` | `be6a7d23d2dcff3c1b2633da3dda2e54e6b7b632b9aba67b6d2e8a0b1c585f30` |
| `evalPlace_ex_neg_inner_not_pointer` | `Quot.sound`, `propext` | `f7c12ccc5c0d1b940fa2f210586706be041a77bbd1760e66dd90a6c316426494` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `evalPlace_ex_neg_misaligned_load` | `Quot.sound`, `propext` | `f4ffe61f5d4fce47c6c025bef8e76c63c6fdfc6b3a85ade6c6e35729909c771a` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `evalPlace_ex_neg_unallocated_local` | `Quot.sound`, `propext` | `de51b43935b1e7d1c1c2829cf0e1d76d2c1f8e346e9fabc22b87fb442dc503ac` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `evalPlace_ex_pos_deref` | `Quot.sound`, `propext` | `f5431f8a4dac0728ac121450ba8aeb3fbab35b2c5a6eafc8885c2ecc0aaa812e` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `evalPlace_ex_pos_field_one_past_end` | `Quot.sound`, `propext` | `55d74503f6e46c5ecc526c758af55ba6f3f823174b80fff36f9ce6968818f38d` | `70926c30e7d65e71a9943a74cfc600bd610ad2ed5143755583f1e796c8779d05` |
| `evalPlace_ex_pos_index` | `Quot.sound`, `propext` | `1c56c4be6f36a21a646c65f8aef9a5035a87517551c61feb9ff325e565cfbdbb` | `c747c476e73c6297a8ae82f5f73e43d33331186e50a32b3dc730111485f2680c` |
| `evalPlace_ex_pos_index_zero_size` | `Quot.sound`, `propext` | `5a3cec110829654831d9f5376b152b6263205703e4297e7f7cde02064b2895cf` | `be6a7d23d2dcff3c1b2633da3dda2e54e6b7b632b9aba67b6d2e8a0b1c585f30` |
| `evalPrefix` | `Quot.sound`, `propext` | `234a117df3f1cfcd04bc3b83d089488e41ec41d343136b82992bd13031ef91ea` | `1c59682a5754e73dcf77184c4ed0b1f6787a5fcdf91329ddb062893510de21ef` |
| `evalPrefix_ex_neg_unallocated` | `Quot.sound`, `propext` | `8dacb46bcc9d96d9a9dec8d44b8c12e70acfcfdabe673e22cc467a8b6c2461df` | `306d5095c4fd94ec23940491e469f48a4a5b0db46e0952ad429ba39884598d0d` |
| `evalPrefix_ex_pos` | `Quot.sound`, `propext` | `f1c0ab3b42ba6891c5a535f9df4a410f9c0cb739ae5e299ab141e5d576707a2b` | `306d5095c4fd94ec23940491e469f48a4a5b0db46e0952ad429ba39884598d0d` |
| `evalProjs` | `Quot.sound`, `propext` | `e649cb93eeaf720d688eac96bf0177dd1980e9d3776a646d2cbd9ca1562d4d1a` | `739ea9b4e74e738d8bcff05cf64fa17778a2c5821ab5d5d09677136bfe1a7b79` |
| `execStmt` | `Quot.sound`, `propext` | `ba262e656c4f7864dfca767c1b0f6be4827e59ee210e5918f2678efb10a1d264` | `2ca8ce8b2baf37da0b52f89e8b66b22647a36f5237da1556b193abdc575055ff` |
| `goesWrongFrom_ex_neg` | `Quot.sound`, `propext` | `b2677fdef89fd6d9cd1b266c6281fe5d5d185e3804236b5d18170101f2b66dca` | `73b38660eab3c5c1123d33df4b769f290e2f103d684febdd43332b6cec1276d2` |
| `goesWrongFrom_ex_pos` | `Quot.sound`, `propext` | `044b435922388463d307ddbe70f74eafbc4306737fca0269c4559e09106f717d` | `14d4fb900b224ab738c1d3c043c473261b44ad7d8bcad52e012c8ee3785c6259` |
| `hasBeh_ex_neg_erased_addrCmp` | `Classical.choice`, `Quot.sound`, `propext` | `f7c3e63d9f5032df15b87b626b7f38b5dc087e51fb44791dc79b514b83956fb3` | `a3b73907ec23fc20009e948f66b3c3d9ca02d15043a3a717dc23a652e8f706d0` |
| `hasMarkers_ex_neg` | `propext` | `25440a4f38c1f446598a84561e277badb3b46f05dcac38e31bf10364bf1e9768` | `4dccc9f9c65745120e55a016fc8254b1a6b1e660dfdb39416a1fc22b69be3a0d` |
| `hasMarkers_ex_pos` | `propext` | `a964fb6450c444d048b5dd87705a89f3df5a1ed4ffe4a712435d44f7781f9de9` | `2028133cdde4b2088174918124e4cf975f68ffe08462d886b1ad60275090f263` |
| `idxTy` | none | `5b2c786b78f362c0ccbd2922fff5944f2af0b820835e224182fee1a08495e24c` | `310e28576f0941ff5da3498561704497e13d233ec01f18410c5f2bba807424dd` |
| `improvesPP_ex_neg_nonprefix` | `propext` | `db0644f2d075f8b9d18ad409293a0a405cd78c815ea9c1fbf9cad47ebb6b773d` | `c953d7eb68715cf82901b95b6cc7a1e28a446c1fa54e1e51f77bea3f0ac348c5` |
| `improvesPP_ex_pos_prefix` | none | `7c75364f8dcbf57e440d8ed325420e4c6a86dd78d2df559cdf1752d77cae7a4f` | `c953d7eb68715cf82901b95b6cc7a1e28a446c1fa54e1e51f77bea3f0ac348c5` |
| `inBounds_ex_neg_freed` | `propext` | `be41961d5e16cbd71d5629454c3db8c3e1fa1b9d00ab3085e689d61b547e4e1c` | `61771e13b36102eff99e3232dbac1ebe7b7ed46b0c813835b4bacef7ca27537a` |
| `inBounds_ex_neg_past` | `propext` | `0015b3c8391bf98e924985c552f5a68192c781d667f37e0cb943ae6ed0ea1823` | `61771e13b36102eff99e3232dbac1ebe7b7ed46b0c813835b4bacef7ca27537a` |
| `inBounds_ex_pos` | `propext` | `e4aa76ed2a3842f0c25b9b960a0e62e240cc92cef4b2b9f3c3e7ae7f03602792` | `61771e13b36102eff99e3232dbac1ebe7b7ed46b0c813835b4bacef7ca27537a` |
| `inBounds_ex_pos_end` | `propext` | `0f4cd87532f8f0711cf121a8126eb47c96dfcb3e439da41e642132f3982a92db` | `61771e13b36102eff99e3232dbac1ebe7b7ed46b0c813835b4bacef7ca27537a` |
| `initEx` | `propext` | `d80208ed7d2b4f4e3818d7666f3175ad6b4b374e28549b68490030a8fffe6a85` | `11bf536f4c2a2aa95208414d1482e85a42fc05f1afbb8ab4ed401d50cc73168e` |
| `load_ex_neg_freed` | `Quot.sound`, `propext` | `00d7d16954683a2bd6f691c8a760708249e721170e744516ec4f1bf94ec6866d` | `48919982df50b476bea6a0355a0c6a97ca820745844c805a9e8400c4d62a0278` |
| `load_ex_neg_misaligned` | `Quot.sound`, `propext` | `9fb1bd9dcd9b7a8c7a1434535194ea6bb78845896147a47f6e60ddc8e6371a2d` | `23b57501805077e83488840b1b00e8a3c759d2befabcbcf2011c4dabf43d081c` |
| `load_ex_neg_uninit` | `Quot.sound`, `propext` | `8e1081edbe425af2f07ef822b5473f43f9a058ce0d93f3ac5ce9a7910f067e17` | `48919982df50b476bea6a0355a0c6a97ca820745844c805a9e8400c4d62a0278` |
| `load_ex_neg_zero_size_enum` | `Quot.sound`, `propext` | `c1ced3dbcd53ec2a3c3e5d2bf4e03a29bcb3859dec87c70895389c5437cba6b8` | `23b57501805077e83488840b1b00e8a3c759d2befabcbcf2011c4dabf43d081c` |
| `load_ex_pos_int` | `Quot.sound`, `propext` | `c7e9870089ade63ce05f89a394af00c7f000ddcffbf0bacb90bbc8b8c5f94c32` | `48919982df50b476bea6a0355a0c6a97ca820745844c805a9e8400c4d62a0278` |
| `load_ex_pos_ptr` | `Quot.sound`, `propext` | `fddb98883285b0c26a9e67ee030f0d836731429c97f126e5d8e4888bc6b425de` | `23b57501805077e83488840b1b00e8a3c759d2befabcbcf2011c4dabf43d081c` |
| `load_ex_pos_zero_size_enum` | `Quot.sound`, `propext` | `b0c91b9ce22356db3aa5ad7a08ad51fdf76472eea3fa600b001194a5c8d6a9ca` | `23b57501805077e83488840b1b00e8a3c759d2befabcbcf2011c4dabf43d081c` |
| `load_ex_pos_zero_size_null` | `Quot.sound`, `propext` | `7f3cd2140a7ba9a04d268d8de36bf763e5d40a6e19ba3df0ea6fb0f08e85429c` | `23b57501805077e83488840b1b00e8a3c759d2befabcbcf2011c4dabf43d081c` |
| `mEx` | none | `4669682e61414313e12d35cecc093131fa8cffb998552587f74676e52f819c9f` | `4b33ebb97ecda9c37ef13250ed50dd89dc253594e1a8e6a9dd88c7e17155e7d1` |
| `noAddrObs_ex_neg` | `propext` | `f750c2b10a7a5eef627ed2306d646f0603bf2441c25caa1e1582fb9c15e316a7` | `5839670c7f5f82c579b8ed8afd05ae6bbbac2bd91ae032a03402022ecb01bc13` |
| `noAddrObs_ex_pos` | `propext` | `cb9b96935ee95ac21961e78777b66b0dc8f884a1e7d885a82400864df0dcf89e` | `174180834e3e533cafa17d426275df943363710d143f5124f6cb04243a927384` |
| `noProvConst_ex_neg` | `propext` | `4fbd47d3f4422c087c4bc5b47ad4b2f21fd7e9e0e9b8dab11ca98e8356b3553b` | `3c44ad1f25de7b9fe6242fad48d3e89e83cce46dd9dd582f92d3e968e62559e0` |
| `noProvConst_ex_pos` | `propext` | `975e58b99047b0b6ea173f3de669532e856360c4f79870e57f9db06b2fbfdb19` | `45fe87c18d38b6e9954a9e452defdb0e4adcf2f16b3a0260644888af51102082` |
| `not_exactUBChecker_const_true` | `Quot.sound`, `propext` | `e910252c23e1988e364edbbd3da3c341081c758cda7eabfe9da0a178541736a1` | `228a9d14effa124769624be3cf00db85cd4b363f81b4dba400b3f47f77f4d350` |
| `nullV` | none | `5f67c819bf65e28d8a25935222511f8fbd4390014f75d50edb982739de45e463` | `9156b5e7dea4b3252934deabec150f672e542d7bc889e9e6089dad17811d9b48` |
| `offsetInbounds_eq_dereferenceable` | `propext` | `edb5433626753e59510a0059379c10388978ca97d6e8126693b007578c4ae317` | `5c581244fb556f13d98c0b367095738f12bbcb1f32efbd02ca9cacdca36da141` |
| `offsetInbounds_ex_neg_freed` | `propext` | `3f657ae5732b23685fe9bed12faabd58f585e679d0fa2884feb56a67f58b51fb` | `ec881141cc0165618c46347488281d81d64c0b5920e5b61373cd1e32eba48d19` |
| `offsetInbounds_ex_pos_one_past_end` | `propext` | `cdf817c8e9476ae36f631f83025ed8ef11872c1ae6dfa7939d4afa17e784cce2` | `ec881141cc0165618c46347488281d81d64c0b5920e5b61373cd1e32eba48d19` |
| `offsetInbounds_ex_pos_zero_null` | `propext` | `d998f2be39db4bcc908ba6c48ffda95b189583441acae7244efafd8a93b5c157` | `ec881141cc0165618c46347488281d81d64c0b5920e5b61373cd1e32eba48d19` |
| `pAddrCmp` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pAddrCmp_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `43d39484ec1308a4d89ce87d3e8e8d7f61ffa223b0f092f9799ceee8847d8238` | `9e649381f6d20a130ae7b6b92ddc22776ba4d8bef64a4b82081f44ac4f2103f3` |
| `pAddrCmp_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `5a4fdd3e0b8a3ccf10fdae37a09519630be17c5303d6aa92f16a5d305b085de5` | `3c2ca2f1348ae6f874c70deb93951a3e6d536a05e3963fc557f55b66a155294f` |
| `pAddrCmp_fresh_term_zero` | `Quot.sound`, `propext` | `fc799b031c63881e69630070c7ad0b90626886e9f897eda26f9c30a593c2b9a1` | `75ba79d3bb617cb89556983e97b18c7d78b3e173a84275b06c86b399077f583c` |
| `pAddrSelf` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pAddrSelf_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `0165d52fbacaa71a2f26710eb0b95d7ce9df16d1e7416d33ff2fb69d2c5a770a` | `7821e35771aa3994ab1667f10edf38669ef841c53590c20253044b259b84a76c` |
| `pAddrSelf_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `d1db3ec55270d73f5a5771d775c74f91e28b312e719017d7771be9ca0b239b2c` | `bb06f93b415fff8fcd84325d6c658e4e4c630ec426fcfd5bfc90940ff3ea3e38` |
| `pAlias` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pAlias_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `64c7d432881262ad395c0df292925ae7c19287f61be309c88819df7612d6da2f` | `86a0d3f00dde98282829bad2a4f0b146d6e19e7707a4d5e463c346967f3e292a` |
| `pAlignZero` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pAlignZeroOne` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pAlignZeroOne_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `532bbc4bfa5d19a62110b1dca3867a8113ab4442b6ae918c39c1c0a6988cfb1e` | `dd3a9b55d6d2f19409f5acb585ed0e81c6333c38687a57bcca27a5d5ecdb36e4` |
| `pAlignZeroOne_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `40315c3d9f5051b714bcf3b9290c0a91abdc9969fc87569065892a15194f3ee4` | `49a2cfcb1677a8bd3a59bd70fdde2fca31fbb61c84bfb53aed1a2b92528bc782` |
| `pAlignZero_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `f92336a6ca17dc48d8d071934f503370cb59e7fcf794af839060eef32a6794ad` | `05229a7b5a474ba5af1e1a7734c7575f6703db853e946515fb931e6a56290a73` |
| `pAlignZero_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `c541506c7bd3c1ca36cd431fa2a9012de8767a234096f0022d4cd8eb782a30da` | `64ea514db773062f7c22f7c1a94753643b4fad9595afd29058295df0baea206f` |
| `pConstProvFresh` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pConstProvFresh_alignPos` | none | `b810f6e2e9e5dbeaf7b73ab44c7657f9f55f9a767f577c6a9101ca6320c20e2f` | `97a09a461aec0eb2315da63f97c3b98867cae1faf6a17576d7645b0c1b70222a` |
| `pConstProvFresh_erased_fresh_wrong` | `Quot.sound`, `propext` | `5c5a4d1417a31f7349a41cc6f45938cdee39ff842e9f6555d0e0409e71b99313` | `38f1b59597de158a000aca4c24676915d1acb9c6c7641c051dcfba9209bbdb69` |
| `pConstProvFresh_erased_slots_beh` | `Quot.sound`, `propext` | `69eebc5c75f1648c4a957d58a6ab7426f48b4d06d97b8d2a7343c326da119d36` | `082b01d9bf3b879f6db53720d42012d361e0161654c6c8149d75c3d458dacc10` |
| `pConstProvFresh_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `a4f7bd43c4252558a2adc8858402d7b4b85d53ac0c6dbadc7d7eb3041e537288` | `d0002f9347fcf9f0abae6df5f0b09f9bd984edbb3129ad61ea81e64e81251c76` |
| `pConstProvFresh_slots_valid` | `Quot.sound`, `propext` | `7b460d68d84055e69522752a5e149ffdf0b5a05ad4ca09a09b4b553ede0d7824` | `0e92a03078aefcef8595f26335bcee1087c8145d3d0c0bae511144a843f4c05a` |
| `pConstProvFresh_ubFree` | `Classical.choice`, `Quot.sound`, `propext` | `313970391b1f5cbebe73d2288077606aac2d42e133480dced586d97ea47293ec` | `f5584025f27be67b6523341974442860113b9e481546a64ffb498ab5c4a85b3d` |
| `pConstProvSlots` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pConstProvSlots_beh` | `Quot.sound`, `propext` | `cfedf3fbf5b8895e6b049c905959de369f1d03d1db5835996fcaa584c9b4e39d` | `1c1af6dcf96fdf5222cdee38f489c87cc0644e5e41d453f2655cba7af77a8d67` |
| `pConstProvSlots_erased_beh` | `Quot.sound`, `propext` | `feb4e9a82fa0927cd42fd1efc5e0f83f52bc6c0d1e59de25621f8d0c347c19c4` | `5abbe98659b65e0373a1c2ba6181a23e277ebb88dabdcb15b1dd1cdec357a2cd` |
| `pDanglingMention` | none | `347ff246bf5b2f52633f9503744537a8d01cd85bcc2fe967797e46942e1975eb` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pDanglingMention_two_beh` | `Quot.sound`, `propext` | `443d9293d6a4e9a8f284bb06457bd622098a27197cb0e89b4f64cd8c61fffaa3` | `b6c97356fd93f19b709bfeb600b800a481a620b4831dde590f2366195dad23a7` |
| `pDanglingMention_two_erased_beh` | `Quot.sound`, `propext` | `f6c351398f5c6fad9c15396782d0abbe98c93be3cc32bb840269f9fa82bf7eb0` | `4a1f9d397f9a4e5fe3772f6f1b8b57cc79b870e5681de38370a1803bd98e99e3` |
| `pDanglingRaw` | none | `347ff246bf5b2f52633f9503744537a8d01cd85bcc2fe967797e46942e1975eb` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pDeadUse` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pDeadUse_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `4122098c08f39cf96c2ffaf0b790ea4acaf27a7ad1fff7c551dcf873199e2863` | `1300ddd2a66673482b132e12dfa48c7cda1aa2ad15df0dc1dc53f47a7015a3e9` |
| `pDeadUse_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `974907a1755154293e00f06e5f99e164d37f1a11d001b8088a9ad8448f685d95` | `ca8a099e61766ae29717954348f6893bb336db5e8cfd4be13a9c45529fcc7cdb` |
| `pDerefUninit` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pDerefUninit_beh` | `Quot.sound`, `propext` | `67b39a7f36ee7c2c5c3974f1f95ed5017f277de251078772f43f0b225da07d15` | `3d49479f75b745aef6fd45413e785d4c0e98899a584161e33d4afb4ffe1a02a7` |
| `pDerefUninit_erased_beh` | `Quot.sound`, `propext` | `a5788a2f550fa63befc668c9fb5776386e70b7e6d66eb115d2016ad468f80a7a` | `0411d69ebc2b72bbb4924462fad17e3a54feb9878ffd12b1249244e5d04db654` |
| `pEmitL` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pHalt` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pHaltEmit` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pLive` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pMentionUnreach` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pMisaligned` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pNull` | none | `347ff246bf5b2f52633f9503744537a8d01cd85bcc2fe967797e46942e1975eb` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pNull_zero_beh` | `Quot.sound`, `propext` | `85bf101b79fb0289a0c04dec0dd05c9625af6e31d57e1a25114c9b7c31b733eb` | `7a49ebbf87d77fb3b13d9b368725af050ea2b639f652c04bcf7664b78b410109` |
| `pRawDangling` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pRawDangling_beh` | `Quot.sound`, `propext` | `ca15a6522add09c7202a3d518dd1dc43adbddb731387b8967bdc0373249fb84c` | `9fead0cd6390a112bdaad694e8f88c52b731807c610554a6e7d23871c378d1d3` |
| `pRawPacked` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pRawPacked_beh` | `Quot.sound`, `propext` | `937327f550a371b69f1c4354ca4e4422d7b8a3db38332ba12be654d4eca0d8cc` | `a834517706e069f570d6a86c83713a79ec282e4bb8ececa1e75b00d348a85419` |
| `pRawPacked_ref_beh` | `Quot.sound`, `propext` | `1270595c38e0adacbee89dd7157482f8756295b57da472d308a2a4fcd1ee711b` | `be5ea087bc58896f4b9b17d4c226c1686a1024447be10f2e8f19a769aa62f68c` |
| `pRefDangling` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pRefDangling_beh` | `Quot.sound`, `propext` | `464f7f01d4b18c568f361a4ef2fcd9f3921acd75d866555cb822e413a2b3651c` | `9d669c1f8a34c81f2b56fcf83d9386e1914b11c75fba0f9ce7b749b10619a572` |
| `pShare` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pShare_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `445f181f1995846a58136b452a64a5c741fa05d2edd957db983b5ef0d121c53c` | `8ad42ccdc273ae1e6028a736cc5798dd33b53b882f2f1b8021dc71682dbcee54` |
| `pShare_erased_slots_beh` | `Quot.sound`, `propext` | `7cf074e7a9bf9600e2dc8b8c22769e8dd8c1b7de584007dcf88ff5348e58b111` | `1d4c9c8e3954b4c1188e27a4db4dd1964387bf1633c460218c8355e0bac1edd6` |
| `pShare_fresh_wrong` | `Quot.sound`, `propext` | `081c2d1536b0a2e5d0ab465b591c2fefaeb33397cc889286bbd94df19ccdb948` | `a65b2afcfb1abb644883f316886ab085d1379334e9ebcfd35e6ab4bdf51c9212` |
| `pShare_slots_beh` | `Quot.sound`, `propext` | `f827fdadafdbd284a294051aaca70ffd30ce815a0fcf0d8ad8164c524e184e3a` | `298be471cbe014d559ea75eb205684116bc5b342dee8be455c8ec96c1120e77e` |
| `pStale` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pStale_erased_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `d26f23d528031710e1e0489bd36f8e493e02216eb6c6f72a8ff604f709167493` | `490d39028986ff7b37837c7fe91a36cdfb7c78469c8ce3e50dad6553d1047d2f` |
| `pStale_fresh_beh` | `Classical.choice`, `Quot.sound`, `propext` | `d4bfdf8fe4a646e1f0e01f5dcb00d86b669b4fe83ae80f91982594af27c24f64` | `0349b2a890a4d1adc983b7fc6ac0ccb7962b7c94ef05ca3a8c71cfc1a05502e1` |
| `pStale_fresh_wrong` | `Quot.sound`, `propext` | `8920f87a1f4fb79792cfd2c7f45e55689023662f207f96f219c91d55f4ae3433` | `cfadac8e5d5a3d307b5c7241a26813cb680afc5f145c0f7b4405ff85af3dcc93` |
| `pSwDiff` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pSwTag` | none | `b75a8c6b4a56f917f1678f84ad0c69dba32725933279e5782773b51c8826f6c9` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pSwTag_two_beh` | `Quot.sound`, `propext` | `9ec24c6b710b770edbb529f0177f92e990a2b38d9960f515e1b84a1661721785` | `aa15f72afd7158c2d746690834c0f391a724ecb4416df6a7303614154d5a8a43` |
| `pSwTag_two_goto_beh` | `Quot.sound`, `propext` | `4c6154701b11afb9c071a1ef618dd9af55cdba15b08fbf6ac0804113cf696575` | `e6d5b47ea1c9a57955fc05f75a78c0af251411bf53c41701159f9f6112604d14` |
| `pSwUninit` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pSwUninit_beh` | `Quot.sound`, `propext` | `6d81192a50d3981f8567414cd655d6098d71da49703ae6b2db90ddcfad1340a4` | `851b1a4ceeaa817735abe1473cbbff67c2fffa85992d9d69ac3adac7d8247ac9` |
| `pSwUninit_goto_beh` | `Quot.sound`, `propext` | `8618f101e06799458e6bf1a445c9e65c585da4f041b542f106f9ce8dbfbae611` | `c0fc138776c386910922acedb70e3cd0eab948f86d2ed05e4f0d29807b13796f` |
| `pTwoMentions` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `pTwoMentions_beh` | `Quot.sound`, `propext` | `913f11155a194fdb965d457a8b64d0e93fba6224ef5622abe6653e091b797b5c` | `f5f086325fa9606cc440c3b33741afe308a7fb9975c9b212bf6d8be67512225c` |
| `pTwoMentions_erased_beh` | `Quot.sound`, `propext` | `45ce6f572b4eed77cb9936ea1e2a0953b735da02268082b49a184a1157d4e8e4` | `1ae673a33e8a26bb3eca1420ba8d068d1788bf65c0f0c0e665b681990b136183` |
| `pUBAssign` | none | `365e83451b75296f97ee762adca0a76d06b24ae22c0f3da3c332a7d58a9ee407` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `placeCells` | none | `ee72397dac7bc54ad39b89378d79c5c2d76ed1147d9d6b2521e1bfe685ea11dc` | `96b57538ed7294537adf2cada28bddacb158f14a55987eb91e703bafefba0af6` |
| `prefixOf` | none | `3490137269aa7a07735185d65b470c546875c629874d8e06fd501833e08fba38` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `projStep` | `Quot.sound`, `propext` | `305ed4d5cd55ab5be85929f51a849cc151813350be676b3beacb8c4e50c658ce` | `739ea9b4e74e738d8bcff05cf64fa17778a2c5821ab5d5d09677136bfe1a7b79` |
| `projStep_deref_eq_none_iff` | `Quot.sound`, `propext` | `1ddd88f2abeda1159e01de8197956b0c586a3c31e737ffb9887cdcf7a9a957d6` | `315621ff23d0797df73fb9b7891d3d18d5ea76748e56ea4154d0b44f309ee999` |
| `projStep_field_eq_none_iff` | `Classical.choice`, `Quot.sound`, `propext` | `e81c0731d1fac123e47604dab5ac6bba7ead00b5879a0dbb8001085f2e34bdc8` | `e5bef1a75a057fcb3424619d65e521ab461c5fb4f5a7e451dbf112502b7be2df` |
| `projStep_index_eq_none_iff` | `Classical.choice`, `Quot.sound`, `propext` | `00230b376f8c67e60fbc12bb7f71b9a33fbd216be43da86ec8fcf3cdbef72b9d` | `e5bef1a75a057fcb3424619d65e521ab461c5fb4f5a7e451dbf112502b7be2df` |
| `ptrAlign` | none | `6ae12e5ef6e1af0bef4803bd311e986ce997f77beed3198cba4ded901a7554e2` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ptrL` | none | `bb4c47c92fcf1ae90fdb02450e94256b5c28a87df3c8ce8a4cf09bb16d6e0c65` | `c06156225aeee52b266e7c40b927b4dd00b2a3fbb9ba2ed1b58db1083c1bb7ca` |
| `ptrSize` | none | `6ae12e5ef6e1af0bef4803bd311e986ce997f77beed3198cba4ded901a7554e2` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `rawDerefStmt` | none | `1268e624832584911f58f1b22ef48e2756c5a905e8b1f52de2609f3c4ab7785e` | `b0bc851740216dda5ff1ee859dfa28582dc33d05e16259f7a8785cfea19ae844` |
| `rawRef_eval_eq_none_iff` | `Quot.sound`, `propext` | `4989ee81a471313c95c4a052be61a2dd4cc19a933627d69375386b4b0a4657e1` | `d1cdb3b1b7e62e926a043e8528c388b1d05e3196af1fe61ea89769ee5d35a3e0` |
| `reachableAt_ex_neg` | `Quot.sound`, `propext` | `581a2f23ed23cdfe1f96eb66072bce5a78520dfe40a65b0815ec642ee53556ed` | `d1f6ddafedd2b27982ca49cd58b8b707cfe323ac0df29597c7fd9af16698e89d` |
| `reachableAt_ex_pos` | `Quot.sound`, `propext` | `4618779aafb2e97c4e99af7b5455e7bc8534633bc42e3a3ab16e3cfc7bd58699` | `f8a6daaacef9b18018aa373995410a6c4ab1fc287af40e7667fbfb2b842a7c78` |
| `readCells_of_size_eq_zero` | `propext` | `cd1749f53991942e84dcfc868e1e52d5a6ca94782c13b0167af540898d103abb` | `7990669db275718dd8b49c29c47bc35638f02bb440f0b2cd5ccb1e5b281403fd` |
| `readIndex_ex_neg_unallocated` | `Quot.sound`, `propext` | `8bd7cc7d2b81c2a954efca7486fef0a45bd77be3d71078517b7b0024119151c2` | `c6528c8daaadf079348bf295f690105064c6f523a095ddd5c819e0d83d7c399a` |
| `readIndex_ex_pos` | `Quot.sound`, `propext` | `f99d7609d6cd1e533af48061edacad0ac3a678f1092f91774068b1ec73425b67` | `919131d2047c1b4b52238ccfddc932e366289cfcd4c5358f5a0980e5ab7006b4` |
| `refDerefStmt` | none | `1268e624832584911f58f1b22ef48e2756c5a905e8b1f52de2609f3c4ab7785e` | `b0bc851740216dda5ff1ee859dfa28582dc33d05e16259f7a8785cfea19ae844` |
| `refOk_ex_neg_align_zero` | `propext` | `07880923b2141308a301018d878d04c189b1d9a3e16ff9ce48b7e89d5062e9aa` | `b8e64e7dc37d43cadc79c08e9785434f74933f5bad8c589d4c78739a49517bb4` |
| `refOk_ex_neg_misaligned` | `propext` | `066a0bcf73542787c10de197ae137b38472c8929e323b0bc41d5ac85b6406256` | `b8e64e7dc37d43cadc79c08e9785434f74933f5bad8c589d4c78739a49517bb4` |
| `refOk_ex_neg_null_zero_size` | `propext` | `03f7c050a86c41b6df4f4c635353ebd615ac593a146a778d185d7a752c9e3d46` | `b8e64e7dc37d43cadc79c08e9785434f74933f5bad8c589d4c78739a49517bb4` |
| `refOk_ex_pos` | `propext` | `f0f9937f55a821c90a9886f7c14bbe550e353360a7dee82dd7e1f7b8e1056a2c` | `b8e64e7dc37d43cadc79c08e9785434f74933f5bad8c589d4c78739a49517bb4` |
| `refOk_ex_pos_dangling_zero_size` | `propext` | `afe4105cfb6f5ea387a40afda049aacfa826d815e2d1d475878152f539a98e20` | `b8e64e7dc37d43cadc79c08e9785434f74933f5bad8c589d4c78739a49517bb4` |
| `refPackedStmt` | none | `1268e624832584911f58f1b22ef48e2756c5a905e8b1f52de2609f3c4ab7785e` | `b0bc851740216dda5ff1ee859dfa28582dc33d05e16259f7a8785cfea19ae844` |
| `refinesAcross_trans` | `Quot.sound`, `propext` | `bccf65b990fba33f69bd5f1832a267c48c12640d9f4cc4f9cf0da55f198fcca2` | `df56ad55272c6dd2f2d13eb643d21b9a46f7791a1be52446a101900e008fd797` |
| `refuted_eraseMarkers_refinesPP` | `Quot.sound`, `propext` | `d16cc56d92a98771caec0e49136edca5c9d1f019ec6de4ccbedb50f6a73ea7da` | `c36dc6732e9969aee7a8d75f8c65de9019e81c1d8e24e5346698cb7ca6a78726` |
| `refuted_eraseMarkers_slots_refinesAcross_fresh` | `Classical.choice`, `Quot.sound`, `propext` | `37548d42f5a895430ac0609bf3c4ba13befa91666a3dd49ba6a7f1839e77bf05` | `0430b4f9e77cc021d947b2d27a55bb78736e2e75ba9770d38ba8ab7a8682921a` |
| `run` | `Quot.sound`, `propext` | `5519710cbb2b64143c503d1fab5c93dae5907edb638885b5f722aaa281f5b305` | `135ad0467abd078e667c0d345ea867b9029927b16189f9ad43ef4706d9ffbe7e` |
| `runFromInit` | `Quot.sound`, `propext` | `217678f1919b33c0dfcb917be21e385c550db1c00695f83107d2bc34443e2dc9` | `135ad0467abd078e667c0d345ea867b9029927b16189f9ad43ef4706d9ffbe7e` |
| `sAlias` | none | `1a3184f00731af3f4ba43bf87fe46e059a9bd9c9305aefe6a9e1c3d0ada270cd` | `6f89115c6b0530bb83d712a9c0175094dbcf550e9edaec95af02a1689d9aaa81` |
| `sEx` | none | `1a3184f00731af3f4ba43bf87fe46e059a9bd9c9305aefe6a9e1c3d0ada270cd` | `6f89115c6b0530bb83d712a9c0175094dbcf550e9edaec95af02a1689d9aaa81` |
| `sShare` | none | `1a3184f00731af3f4ba43bf87fe46e059a9bd9c9305aefe6a9e1c3d0ada270cd` | `6f89115c6b0530bb83d712a9c0175094dbcf550e9edaec95af02a1689d9aaa81` |
| `selectTarget` | none | `d20800ead0a111643b6a7e2d316941218459b1cf64ac1e988b2944a0b9108609` | `915e220b2052c635b98ef7ae264bef9f2a4f72c4b0395d41b117cf6f2008f63f` |
| `setStmt` | `propext` | `b74ab3957e49472404f49e7e7548f28e3c8478225ae5dc5ccf4f5178cb7abd11` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `setStmt_ex` | `propext` | `a26f34ffee7ae6831c74690ecf60237b064582a47bd0b701324a817de0b004b5` | `45df7e5dbc1efa31f29325541ec54de59c3229cb14871043cc4aa78023652b8f` |
| `setStmt_ex_out_of_range_blk` | `propext` | `5f25aee875f3bf952f77501bfc0b44a633a9430e042fe90e4460e2e0c73ba006` | `45df7e5dbc1efa31f29325541ec54de59c3229cb14871043cc4aa78023652b8f` |
| `setStmt_ex_out_of_range_idx` | `propext` | `9fe362f3f07ee0ac52120d5fb555788b35f52291bb6f6e3259dbbe5e37d763b6` | `45df7e5dbc1efa31f29325541ec54de59c3229cb14871043cc4aa78023652b8f` |
| `setStmt_pRawDangling_ref` | `propext` | `6c05506a78f25076db81e22cd61e5eaf727be6353114bd61839f9b81205fea51` | `09ab9833ac0d9ad7c98168a9c5d0730c05fdeec3e7d63899dd863cbec885e664` |
| `setStmt_pRefDangling_raw` | `propext` | `3ecce085d1af47c7119678c84acaed5487b0cd2f3de87f0bbffeea7a6a2a5b60` | `09ab9833ac0d9ad7c98168a9c5d0730c05fdeec3e7d63899dd863cbec885e664` |
| `setStmt_ref_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `c3a0eedab946692f848420bb98d51da65176aec637dc084495d5cef1a10f2b31` | `766ea6e97de79b43125175dcd36f261f2572fb2d4ae4e9d9d5b1b8807e491eab` |
| `setTerm` | `propext` | `b9a7c7c5bba7460d61dd0f1e89e7d940df730aeb2cd2a6df164127bcdaa509dc` | `fdb92380aa490a3470c9cdc374cd10365ab92632fe61d63d1e74299d26ea2c0c` |
| `setTerm_ex` | `propext` | `fee1cdc881c1901b328b5a63bd6e5bf89fd3b658d82ac17126b7ed38ac368acf` | `d1f665897c65ea4aceea51e9c180b4121f6c7be59780daba4e92dbe3a5fb8e8f` |
| `setTerm_ex_out_of_range` | `propext` | `25a4e12f06806a7f23f9805345f8d33c62cd94f360fbaac92ecb73603f2c542e` | `d1f665897c65ea4aceea51e9c180b4121f6c7be59780daba4e92dbe3a5fb8e8f` |
| `setTerm_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `20c8aada05b793a0e81533db32c8712f7a107ed06b0de5174ccd4bfba155d34d` | `2257b1557aef4c0b287994880988ff829fcde1f2062e48870eef395c02b42b49` |
| `setTerm_rev_refinesPP` | `Classical.choice`, `Quot.sound`, `propext` | `59c9833f39edcccac182771cf089e711fc84b57c7a713e472e45217f0c383379` | `c67e55458ead8bf87fca691deeabdcd571905946ff928602f11554e07f348d63` |
| `stDangIdx` | none | `23327cccd1aa827788f54e8a0a23f520e40d77e375734afff83bfbbac8854c4d` | `80503d7556da2832c4fbf777b68c247cf6cd25af563688402e6b0bc776246aea` |
| `stEx` | none | `23327cccd1aa827788f54e8a0a23f520e40d77e375734afff83bfbbac8854c4d` | `80503d7556da2832c4fbf777b68c247cf6cd25af563688402e6b0bc776246aea` |
| `stFreedInFrame` | none | `23327cccd1aa827788f54e8a0a23f520e40d77e375734afff83bfbbac8854c4d` | `80503d7556da2832c4fbf777b68c247cf6cd25af563688402e6b0bc776246aea` |
| `stIdx` | none | `23327cccd1aa827788f54e8a0a23f520e40d77e375734afff83bfbbac8854c4d` | `80503d7556da2832c4fbf777b68c247cf6cd25af563688402e6b0bc776246aea` |
| `stMissingAlloc` | none | `23327cccd1aa827788f54e8a0a23f520e40d77e375734afff83bfbbac8854c4d` | `80503d7556da2832c4fbf777b68c247cf6cd25af563688402e6b0bc776246aea` |
| `stTwoMentions` | `Quot.sound`, `propext` | `23327cccd1aa827788f54e8a0a23f520e40d77e375734afff83bfbbac8854c4d` | `80503d7556da2832c4fbf777b68c247cf6cd25af563688402e6b0bc776246aea` |
| `step` | `Quot.sound`, `propext` | `599c062d65f506bc36c37b769e556a1268a75dace009c9a14e0c38254be9e18f` | `dbcb656e7cecd147ba0485981e0fd68ccb86afea08a3cdf6de2ac55ebc9a602b` |
| `store_ex_neg_freed` | `propext` | `7bcc8770700fcad22e5a9e3fd6e95acb2a8411a9a185f83694b517de5a1ad788` | `5dd23b5379d3ebe48a1b82d62d905dd8df4f489ec840508d412e7525a7e9a9d3` |
| `store_ex_pos` | `propext` | `92cd5203e420aa9570f0c227c0d70ed0dda87b3c1c8efcd25017804cbfac8e54` | `5dd23b5379d3ebe48a1b82d62d905dd8df4f489ec840508d412e7525a7e9a9d3` |
| `switchToGoto_erases_operand_ub` | `Quot.sound`, `propext` | `e6cf0365986aca971566777f4688714c29333734d81d449015fef5f9f0ab7faf` | `ad4245cc10d56172e259728cd2d3bd29d85173da9df7e3b36b4ad7f299cf6c35` |
| `switchToGoto_validTag_equivPP` | `Quot.sound`, `propext` | `d6c70b253aa78caf6681c018e387897f48c0ade659f2a5da0cfe7d91c23dcd7f` | `9480e480eb67cf5a5d58e40248208d0d1f562961661225dadd0ecd05bf9a6a28` |
| `u8` | none | `5b2c786b78f362c0ccbd2922fff5944f2af0b820835e224182fee1a08495e24c` | `310e28576f0941ff5da3498561704497e13d233ec01f18410c5f2bba807424dd` |
| `ubFree_of_refinesPP_rev` | `Quot.sound`, `propext` | `6c0bae3b18482de38523847f4bb86282fe4f68c482c2f90a5d3ee7487d6f963e` | `05b8adff1733e90564b46904f02f3e825f3639bbe51f6fef1672289b737b47b5` |

### Primary sources

* Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814.
* Juneyoung Lee et al., "Taming Undefined Behavior in LLVM", PLDI 2017, DOI 10.1145/3062341.3062343.
* Juneyoung Lee et al., "Reconciling High-Level Optimizations and Low-Level Code in LLVM", OOPSLA 2018 (PACMPL 2), DOI 10.1145/3276495.
* Ralf Jung, Hoang-Hai Dang, Jeehoon Kang and Derek Dreyer, "Stacked Borrows: An Aliasing Model for Rust", POPL 2020, DOI 10.1145/3371109.
* rust-lang/rust `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`; rust-lang/rust merge commit `5d328a1f62fe7c9d3a31d14b88dfa13310b7c989` (pull request #117329, merged 2024-05-22; cited in prose for the zero-offset exemption of `library/core/src/ptr/docs/offset.md`); rust-lang/reference `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`; rust-lang/rfcs `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`; minirust/minirust `063d784186d3252bee242217f218223205c0b568`; AbsInt/CompCert `5e4ef44c57b22cdc2e1893770843fd693a5f82e1`. Paths and full line ranges of every quoted passage are given in the prior-art entries of the cards; the commits were confirmed to exist on 2026-11-21.
* Published reference-corpus packages cited in prior art (by package name, not as subjects): `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing`, `enum-niche-layout-guarantees-and-validity-invariants`, `pointer-provenance-models-and-integer-pointer-cast-optimizations`, `undefined-values-poison-undef-freeze-and-refinement`.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No other tool and no network access beyond the toolchain download are needed.

Primary command, run from the package directory:

```text
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It then (1) runs `lake build`; (2) checks that no Lean source contains `sorry`, `admit` or `native_decide` or declares an `axiom`; (3) computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and checks that only `propext`, `Classical.choice` and `Quot.sound` occur; and (4) for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` lists) recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its definition closure (the sorted `name : type := value` texts of every package-local constant reachable from the statement, theorem bodies excluded) and compares them with `audit/statements.json`. Exit status 0 means all four checks passed.

Manual alternative (build and print the axioms of the main results):

```text
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs `#print axioms` on every main result of the cards. Each line of its output must list only `propext`, `Classical.choice` and `Quot.sound` (or no axioms).

To check that a later Lean release still accepts the proofs, change `lean/lean-toolchain` and rerun the primary command; a statement-hash mismatch then means that the statement or its definitions elaborate differently and the card text must be re-checked against the new statement.
