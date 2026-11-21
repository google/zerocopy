# Address-taken slot coalescing in a toy language: copy-to-move upgrades under three `move` semantics, merges into subplaces, lifetime notions, and overlap staging (Lean 4)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler. Connections to rustc are separate `derived (modeling bridge)` remarks citing documented design.

* **`upgrade-moveAsCopy-equivalence`** (theorem, T0): Under `MoveSem.asCopy`, for either assignment order, every program `P`, every body index `k` and every layout `A`, the program `P.upgradeAt k` (whose statement `k`, if it is `lhs := [copy q]`, `call fn (copy q)` or `out (copy q)`, has `copy q` replaced by `move q`) has the same outcome as `P`.
* **`upgrade-moveDeinit-iff-no-read-before-reinit`** (characterization, T2): Under `MoveSem.deinit` (either assignment order), for an upgrade site `k` of place `q` (`lhs := [copy q]` with `lhs` disjoint from `q`, `call fn (copy q)` with the callee parameter different from `q.base`, or `out (copy q)`) and a layout on which the source run is neither undefined nor excluded, the upgraded program has the same outcome iff every cell of `q` is not read after the use (inside the callee at tick `k`, at later ticks, through pointers, or in the destructor block) before it is written or reset; and, for an upgrade site, if that condition holds on every layout whose source run is neither undefined nor excluded, the upgrade is a refinement.
* **`upgrade-moveInPlaceCall-sufficient-conditions`** (theorem, T2): Under `MoveSem.inPlaceCall` (either assignment order): upgrading a body statement that is not a call leaves the outcome unchanged on every layout; and, for a call site `call fn (copy q)` whose callee parameter is different from `q.base`, upgrading the argument is a refinement if (a) on every layout whose source run is neither undefined nor excluded, no cell of `q` is read after the call returns before it is written or reset, (b) on every such layout, the callee accesses no cell of `q` during the call, and (c) the callee's parameter local is not address-taken anywhere in `P` (`¬ AddrTaken P (P.fn fn).prm`; the parameter is a local of the caller's frame, so taking its address outside the callee also counts).
* **`destructor-load-breaks-deinit-upgrade`** (counterexample, T1): Under `MoveSem.deinit` with atomic assignments (`semD`): in `pDtor` (x := 7; p := &x; y := copy x at body index 5; out y; a destructor block that loads through p), body index 5 is an upgrade site, the source completes with `[7, 7]` on layout `A0` while the `MoveSem.deinit` upgrade has undefined behaviour there, the no-read-before-re-initialization condition fails, and the upgrade is not a refinement; without the destructor block the same upgrade is a refinement (positive control `pNoDtor_upgrade_refines`).
* **`in-place-call-upgrade-counterexamples`** (counterexample, T1): Under `MoveSem.inPlaceCall` with atomic assignments (`semI`), each of the conditions (a) no read of `q` after the call, (b) the callee does not access `q`, (c) the callee's parameter local is not address-taken can fail alone, with the call site and the other two holding (the dynamic ones on every layout whose source run is neither undefined nor excluded), and the call-argument upgrade then is not a refinement; (c) can fail through the caller alone, under either assignment order (the caller takes the parameter local's address, or allocates it and compares its address, while the callee body never takes it); and, with atomic assignments (`semI`, `semD`), a callee that writes its parameter and then loads through an escaped pointer to the argument breaks the upgrade under both `MoveSem.inPlaceCall` and `MoveSem.deinit`.
* **`moveDeinit-moveInPlaceCall-incomparable`** (counterexample, T1): Under atomic assignments (`semD` = `MoveSem.deinit`, `semI` = `MoveSem.inPlaceCall`), the two semantics admit incomparable sets of refining upgrades: on `pIPStore` (callee stores 2 through an escaped pointer to x, then prints its parameter) the call-argument upgrade is a refinement under `MoveSem.deinit` but not under `MoveSem.inPlaceCall`; on `pReuse` (y := copy x; out x) the assignment upgrade is a refinement under `MoveSem.inPlaceCall` but not under `MoveSem.deinit`.
* **`observation-certificate-checker-and-least-solution`** (characterization, T0): The Boolean checker `checkObs` accepts a mask exactly when it satisfies the gen/transfer certificate conditions over the body and the destructor block (gen: by-name reads, any `load` if the local is address-taken, and the same inside called callees; kill: storage statements and whole-local assignments), and the backward scan `obsAnalysis` is such a certificate and is below every certificate at every tick up to the end and every local of the program.
* **`observation-certificate-licenses-upgrades`** (theorem, T1): If a mask `O` satisfies the certificate conditions and `q.base ∉ O (k+1)`, then on every layout and under every semantics no cell of `q` is read at a tick after `k` before it is written or reset; and, for an upgrade site `k` of `q`, a certificate that licenses the upgrade under the chosen `move` semantics (`Licensed`: always for `MoveSem.asCopy`; `q.base ∉ O (k+1)` plus a callee summary with no possible read of `q.base` for `MoveSem.deinit`; for `MoveSem.inPlaceCall`, always for non-call sites and, for call sites, `q.base ∉ O (k+1)`, a callee that does not read or assign a place based at `q.base` by name nor store through a pointer held in one, does no `load` and no `store` if `q.base` is address-taken, and whose parameter local is not address-taken anywhere in `P`) makes the upgrade a refinement, under either assignment order.
* **`destructor-blind-analysis-admits-unsound-upgrade`** (counterexample, T1): A version of the analysis that checks the certificate conditions over the body and not over the destructor block produces, for `pDtor`, a mask that licenses the `MoveSem.deinit` upgrade at body index 5, which is not a refinement under atomic assignments (`semD`); the full analysis of `pDtor` is accepted by `checkObs` (hence is a certificate, `ex_obsCert_pos`) and does not license it (positive control).
* **`single-merge-into-field-sufficient`** (theorem, T2): Under atomic assignments and every `move` semantics, for the single merge of local `x` into the field window at offset `f` of local `y`: if the forest is well formed (`ForestWF`, including that every top-level call names an existing callee), `NoValueClobberStmt` holds (no read in the source run observes a clobber in the merged memory; checked on the atomic-assignment access log of every non-UB, non-excluded run), and, if `x` and `y` are both address-taken, they are never lexically allocated during a common tick, then the coalesced program refines the source.
* **`address-taken-merge-overlap-breaks-refinement`** (counterexample, T1): Under atomic assignments and every `move` semantics: in `p3` (x and y allocated together; `y.1 := 5; x := 7; out x; y.0 := 9; ptrInRange(&x, &y, 2); out y`) the merge `x ↦ y.0` is well formed and satisfies `NoValueClobberStmt` but not the lexical address condition (both are address-taken and allocated together); the source comparison is `false` on every non-excluded layout (`p3_outcome`) and the coalesced one is `true` on `A0`, so it is not a refinement; in `pClobber` (no address-taken local) a value clobber breaks the same merge; in `p3x` an address-taken `x` merged into a non-address-taken `y` allocated at the same time, with `NoValueClobberStmt`, is a refinement.
* **`forest-coalescing-root-level-check-sufficient`** (theorem, T2): Under atomic assignments and every `move` semantics, for a well-formed merge forest (`ForestWF`, including that every top-level call names an existing callee): `NoValueClobberStmt` together with the root-level check `ClassAddrDisjoint` (any two distinct address-taken locals of the same class whose root-relative windows intersect are never lexically allocated during a common tick) gives a refinement; the window-insensitive check `ClassAddrDisjointW` (all pairs of distinct address-taken class members) implies `ClassAddrDisjoint`.
* **`pairwise-merge-checks-do-not-compose`** (counterexample, T1): Under atomic assignments and every `move` semantics: in `pChain`, the merges `x ↦ y.1` and `y ↦ z.1`, checked independently against the original program, each satisfy `NoValueClobberStmt` as single merges and the per-edge address check, and the forest satisfies `NoValueClobberStmt` and the per-edge check; but `x` and its final root `z` are address-taken and allocated together, and the composite coalescing is not a refinement; in `pSib`, the sibling merges `x1 ↦ y.0`, `x2 ↦ y.0` pass the per-edge and the member-versus-root checks and `NoValueClobberStmt`, but the siblings are address-taken and allocated together, and the coalescing is not a refinement.
* **`union-find-interval-union-decides-root-check`** (characterization, T0): For a well-formed forest, the disjoint-set pass `ufCheck` (each block keeps the union of the lexical tick sets of its address-taken members; merging two blocks is rejected if their unions intersect or they are already one block) accepts iff the window-insensitive root-level check `ClassAddrDisjointW` holds.
* **`lifetime-policy-soundness-iff-lexical-for-address-taken`** (characterization, T2): For a uniform interference policy that assigns one of the two lifetime notions of `Notion` (lexical storage liveness, or precise by-name liveness: the hull of by-name access points at half-statement granularity, where a call marks both halves for every local its callee body touches by name) to address-taken locals and one to the other locals, and checks that distinct class members with intersecting root-relative windows have non-overlapping intervals: the policy is sound (every forest satisfying `ForestWF`, including that calls name existing callees, that passes the check yields a refinement, under atomic assignments and every `move` semantics) iff it uses lexical intervals for address-taken locals; a policy that uses precise intervals for address-taken locals is not sound, whatever it uses for the other locals; precise liveness for the other locals is allowed.
* **`overlap-staging-behavioural-equivalence`** (theorem, T1): Under every `move` semantics: if no assignment of a program needs staging (top-level: two or more operands, one of which is a load or reads a place intersecting the left side; in a callee: the same, where in addition a place based at the callee parameter and one not based at it count as possibly overlapping), in-order and atomic assignment give the same outcome on every layout; staging (each such top-level assignment of the body and destructors becomes `storageLive tmp; tmp := rhs; lhs := [move tmp]; storageDead tmp` with a fresh `tmp`) under in-order writes refines the unstaged program under atomic assignment when no callee assignment needs staging and every callee parameter local exists, and the behaviour sets are equal (`BehEq`) when no callee assignment needs staging and every local the program mentions exists.
* **`coalesce-then-stage-pipeline`** (theorem, T1): Under in-order field writes and every `move` semantics, for a well-formed forest (`ForestWF`) with `NoValueClobberStmt` and the root-level address check `ClassAddrDisjoint`: if no assignment of the source needs staging, no callee assignment of the coalesced program needs staging, and every callee parameter local exists, the staged coalesced program refines the source; and if no assignment of the coalesced program needs staging (a coalescer that respects the no-overlap constraint), the unstaged coalesced program refines the source.
* **`coalescing-creates-overlap-and-recoalescing-pitfall`** (counterexample, T1): Under every `move` semantics: in `pSwap` (y := (1, 2); y' := (y.1, y.0); out y') the merge `y' ↦ y.0` is well formed and satisfies `NoValueClobberStmt` and the root-level address check, and the source needs no staging, but the coalesced program contains `y := (y.1, y.0)` (`coalesce_pSwap_contains_overlap`), prints `(2, 2)` on every non-excluded layout under in-order field writes (`coalesce_pSwap_outcome_inOrder`) and is not a refinement there (it is one under atomic assignment, and its staged version is one under in-order writes); re-running the coalescer on the staged program with the merge of the staging temporary into `y` satisfies the same conditions but again contains an assignment that needs staging and is not a refinement under in-order writes.
* **`vc-transfer-address-free-and-address-mentioning`** (theorem, T2): Under atomic assignments and every `move` semantics, for a well-formed forest (`ForestWF`) with `NoValueClobberStmt`: an address-free postcondition (one that gives the same verdict on traces that agree after erasing printed addresses and comparison results) valid for the source is valid for the coalesced program, with no address condition (in this toy addresses reach nothing but printed pointers and comparison results); it transfers back if moreover the source has no undefined behaviour; and an arbitrary postcondition valid for the source transfers forward when the root-level address check `ClassAddrDisjoint` also holds.
* **`vc-transfer-counterexamples`** (counterexample, T1): Under atomic assignments and `MoveSem.deinit`: the address-mentioning postcondition 'no comparison returned true' holds for `p3` and `pPrecise` but fails after a merge that violates the root-level address check (also when the merge passes the precise-everywhere policy); an address-free postcondition fails to transfer across a value clobber (`pClobber`, both directions); backward transfer fails when coalescing removes undefined behaviour (`pUBRemoved`, a read of an uninitialized local) and for an address-mentioning postcondition (`p3`, where the root-level address check also fails).

Non-claims for every card are listed under **Boundaries** (non-claims first); read them before relying on a result. Earlier candidate formulations of several statements were false; the 15 `refuted_*` theorems recorded under **Boundaries**, subsection *Refuted earlier formulations (reference points, not results)*, are refutations of those earlier candidate statements about the toy model, not claims about rustc or any other compiler.

## Applicability

### Model fidelity

This is a toy model (namespace `Toy.Coalesce`). Its definitions are meant to capture the shape of
storage-merging optimizations once a slot's address can be taken: upgrading the last `copy` of a
place to `move`; merging a local into a field window of another local, possibly transitively
(destination propagation, return-slot reuse, local-to-field coalescing); and staging assignments
whose left side overlaps a place read by their right side.

* **Language.** A program (`Prog`) is a straight-line body followed by a straight-line destructor
  block (the return tail) and a table of callees. Statements (`Stmt`): `storageLive x`,
  `storageDead x`, aggregate assignment `lhs := [o₀, …]`, `store p v` (write through a pointer),
  `ptrEq`, `ptrInRange`, `out o`, `call fn arg`, `nop`. Operands (`Operand`): `copy q`, `move q`,
  `lit n`, `addrOf q`, `load p len`. A place (`Place`) is a local with a field window
  `[off, off+len)` (the flattened form of a projection path; nested projections compose by adding
  offsets).
* **Memory.** Per-(local, offset) cells holding `uninit`, an integer, or a pointer `ptr l o` whose
  provenance is the local `l`. Loads and stores through a pointer access local `l` and are undefined
  behaviour unless `l` is allocated and the access is in bounds. Reading an uninitialized cell
  through `copy`, `move` or `load` is undefined behaviour.
* **Addresses and allocation.** A layout (`Layout`) gives each local one base address for the whole
  run (a static frame layout). Absolute addresses are observable through pointer comparisons and
  printed pointers and through nothing else: there is no address-dependent control flow, no
  integer-pointer cast and no address-dependent indexing. Runs whose layout makes two
  simultaneously allocated locals overlap are excluded, so distinct simultaneously allocated
  locals have disjoint address ranges. Allocation is lexical: storage statements allocate and
  deallocate; callee parameters are allocated for the duration of a copy-passed call.
* **Callees.** A callee (`Callee`) has a parameter local `prm` and a body. Callee bodies run in the
  caller's frame: the parameter is a local of the caller's frame, so the caller can allocate it,
  take its address or compare its address outside the call. Storage statements and nested calls
  inside a callee are undefined behaviour. A call to an absent callee index is run as
  `P.fn fn = ⟨0, []⟩` (parameter local `0`, empty body); the coalescing results exclude such calls
  through the `CallsInBounds` clause of `ForestWF`.
* **`move` semantics** (a parameter, none chosen): `MoveSem.asCopy` (`move` is `copy`);
  `MoveSem.deinit` (the source cells become uninitialized after the read); `MoveSem.inPlaceCall`
  (outside calls `move` is `copy`; a moved call argument is passed in place: during the call the
  callee's parameter is the argument place, and the parameter local is not allocated).
* **Assignment order** (`AssignMode`, a parameter): `AssignMode.atomic` (all operands evaluated,
  then all fields written) or `AssignMode.inOrder` (in-order field writes).
* **Observables.** Event traces (`out` values with pointers printed as addresses, comparison
  results), undefined behaviour, or exclusion. Refinement (`Refines`): every behaviour of the
  target is a behaviour of the source, unless the source has undefined behaviour on some
  non-excluded run. `BehEq` is equality of behaviour sets.
* **Terminology.** `AddrTaken P u` ("address-taken") is a syntactic over-approximation of address
  observation: it holds whenever some statement of the body, the destructors or any callee (called
  or not) applies `addrOf` to a place based at `u`, or passes such a place by `move` to a callee
  that takes its parameter's address, even if the resulting address is never compared or printed.
  Semantic address exposure is not tracked separately.
* **Degenerate edges.** Address ranges are `[a, a+m)` over natural numbers with no wrapping; an empty
  range (a local of size `0`) is disjoint from every range (`Disj`). A place of width `0` reads and
  writes nothing. `WindowsDisjoint` and `Forest.windowsOverlap` treat a width-`0` window strictly
  inside another window of the same local as overlapping it (`ex_windowsDisjoint_empty_interior`);
  every use of these predicates is then conservative (more upgrade sites rejected, more staging,
  more pairs checked). A non-existent local has size `0` and can never be allocated (`storageLive`
  of it is undefined behaviour), so every access to it is undefined behaviour. Half-statement
  points `p` belong to tick `p / 2` (floor division): `2t` is the read half and `2t + 1` the write
  half of top-level statement `t`; a call marks both halves for every local its callee body touches
  by name.

Model–system relation: none proved. No embedding, abstraction or simulation between the toy and
rustc MIR (or any other IR or compiler) is stated or proved; the refinements proved here relate two
toy programs. These are statements about the toy model; they neither establish nor refute the
corresponding claims about rustc or any other compiler.

Known gaps (modeling choices, not findings): no branches or loops; static per-local addresses (a
re-allocated local reuses its address, and old pointers stay valid, unlike real MIR storage
reallocation); provenance is per local, without allocation generations; no integer-pointer casts
or pointer arithmetic; callee bodies run in the caller's frame, may name caller locals, and may not
contain storage statements or calls (undefined behaviour); the in-place reading of `move` is
deterministic and has no de-initialization; no aliasing-model protectors, drop elaboration,
unwinding or concurrency; no alignment or padding; values are naturals.

### Relation to the published address-free package

The published package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing`
(namespace `Toy.SlotCompact`, google/zerocopy branch `reference`, commit
a85598234b05e6dcc9afb9e81d2e396cc1218751) proves value-level soundness of slot renaming and scalar
slot sharing in an address-free language, a certificate-checked liveness analysis
(`checkLive_eq_true_iff`, `checkLive_sound`) and verification-condition transfer. It excludes memory,
pointers, address-taken slots, projections and aggregates. Its results are cited by name below as
the address-free baseline. They are not re-proved and no theorem here applies them: the two
languages differ, and `NoValueClobberStmt` here is a dynamic, trace-level counterpart of its static
no-clobber conditions. No module of this package imports or restates its declarations. Model–system
relation between the two packages: none proved.

### Toolchain and project

* Lean `leanprover/lean4` release `v4.34.1`; no Mathlib; `lakefile.toml` with one `[[lean_lib]]`
  (`ToyCoalesce`) and no `[[require]]`.
* Modules: `Basic` (language, semantics, refinement), `Upgrade` (copy-to-move upgrades),
  `ObsAnalysis` (the backward analysis and its certificate), `Merge` (coalescing, address checks,
  union–find, lifetime policies), `Staging` (overlap staging), `VC` (verification-condition
  transfer); proof modules `Infra` (frame properties of the interpreter, layout independence of
  everything but the trace, a layout respecting every allocation pair), `Inv` (allocation and
  pointer-provenance invariants of runs), `PfObs`, `PfInPlace`, `PfLicensed` (upgrade results),
  `PfUF` (union–find), `PfStage` (in-order versus atomic assignment, staging), `PfCoalesce`
  (coalescing simulation and the address-free verification-condition transfers), `PfPolicy`
  (lifetime-policy soundness), `PfCompose` (results composed from the others); `Tactics`
  (evaluation tactics used by proofs about concrete programs), `Programs` (concrete programs),
  `CexUpgrade`, `CexMerge`, `CexExtra`, `CexAdj`, `CexSupport` (counterexamples, positive
  controls, non-vacuity, and canonical-form restatements of them), `Examples` (definition examples), `Refuted` (earlier formulations shown false).
  The main theorems are stated in the proof modules; the definitions they use are in the first six
  modules.

### Subjects

`REPORT.json` lists the Lean release used to check every theorem; the rust-lang/rust revision whose
MIR and destination-propagation documentation is quoted for the `derived (modeling bridge)` remarks
(the documentation is quoted; the implementation is not examined); the CompCert revision whose
validator file is quoted as related work; and the published papers cited as prior art (bibliographic
records checked; full texts not inspected unless a card says so). The report concerns the toy model;
it states no formal relation between the toy and any of these subjects.

## Findings

### Definitions (verbatim)

All declarations live in namespace `Toy.Coalesce` (files under `lean/ToyCoalesce/`). Every definition below is quoted verbatim with its file and line range; proofs of theorems are elided.

#### `ToyCoalesce/Basic.lean`

```lean
-- lean/ToyCoalesce/Basic.lean:34-38
inductive Val where
  | uninit
  | int (n : Nat)
  | ptr (loc off : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:42-46
structure Place where
  base : Nat
  off : Nat
  len : Nat
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:49-49
def Place.proj (q : Place) (o l : Nat) : Place := ⟨q.base, q.off + o, l⟩
```

```lean
-- lean/ToyCoalesce/Basic.lean:52-52
def Place.whole (x size : Nat) : Place := ⟨x, 0, size⟩
```

```lean
-- lean/ToyCoalesce/Basic.lean:61-67
inductive Operand where
  | copy (q : Place)
  | move (q : Place)
  | lit (n : Nat)
  | addrOf (q : Place)
  | load (p : Place) (len : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:70-75
def Operand.len : Operand → Nat
  | .copy q => q.len
  | .move q => q.len
  | .lit _ => 1
  | .addrOf _ => 1
  | .load _ l => l
```

```lean
-- lean/ToyCoalesce/Basic.lean:88-98
inductive Stmt where
  | storageLive (x : Nat)
  | storageDead (x : Nat)
  | assign (lhs : Place) (rhs : List Operand)
  | store (p : Place) (v : Operand)
  | ptrEq (a b : Operand)
  | ptrInRange (a b : Operand) (n : Nat)
  | out (o : Operand)
  | call (fn : Nat) (arg : Operand)
  | nop
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:103-106
structure Callee where
  prm : Nat
  body : List Stmt
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:110-115
structure Prog where
  sizes : List Nat
  body : List Stmt
  dtors : List Stmt
  fns : List Callee
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:118-118
def Prog.size (P : Prog) (x : Nat) : Nat := P.sizes.getD x 0
```

```lean
-- lean/ToyCoalesce/Basic.lean:121-121
def Prog.nloc (P : Prog) : Nat := P.sizes.length
```

```lean
-- lean/ToyCoalesce/Basic.lean:125-125
def Prog.code (P : Prog) : List Stmt := P.body ++ P.dtors
```

```lean
-- lean/ToyCoalesce/Basic.lean:128-128
def Prog.fn (P : Prog) (fn : Nat) : Callee := P.fns.getD fn ⟨0, []⟩
```

```lean
-- lean/ToyCoalesce/Basic.lean:138-142
inductive MoveSem where
  | asCopy
  | deinit
  | inPlaceCall
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:149-152
inductive AssignMode where
  | atomic
  | inOrder
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:155-158
structure Sem where
  move : MoveSem
  assign : AssignMode
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:161-161
abbrev Layout := Nat → Nat
```

```lean
-- lean/ToyCoalesce/Basic.lean:165-165
def Disj (a m b n : Nat) : Prop := m = 0 ∨ n = 0 ∨ a + m ≤ b ∨ b + n ≤ a
```

```lean
-- lean/ToyCoalesce/Basic.lean:172-175
inductive EVal where
  | int (n : Nat)
  | addr (a : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:178-181
inductive Event where
  | vals (vs : List EVal)
  | cmp (b : Bool)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:185-189
inductive Outcome where
  | done (t : List Event)
  | ub
  | badLayout
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:194-198
inductive AccKind where
  | read
  | write
  | reset
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:202-208
structure Access where
  tick : Nat
  inCall : Bool
  loc : Nat
  off : Nat
  kind : AccKind
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:211-214
inductive Status where
  | running
  | ub
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Basic.lean:217-227
structure St where
  mem : Nat → Nat → Val
  live : Nat → Bool
  alias : Option (Nat × Place)
  trace : List Event
  log : List Access
  tick : Nat
  inCall : Bool
  status : Status
  /-- Pairs of locals that were simultaneously allocated (recorded at allocation time). -/
  conflicts : List (Nat × Nat)
```

```lean
-- lean/ToyCoalesce/Basic.lean:230-231
def St.init : St :=
  ⟨fun _ _ => .uninit, fun _ => false, none, [], [], 0, false, .running, []⟩
```

```lean
-- lean/ToyCoalesce/Basic.lean:233-233
def St.fail (s : St) (k : Status) : St := { s with status := k }
```

```lean
-- lean/ToyCoalesce/Basic.lean:235-236
def St.logAcc (s : St) (loc off : Nat) (k : AccKind) : St :=
  { s with log := s.log ++ [⟨s.tick, s.inCall, loc, off, k⟩] }
```

```lean
-- lean/ToyCoalesce/Basic.lean:238-238
def St.emit (s : St) (e : Event) : St := { s with trace := s.trace ++ [e] }
```

```lean
-- lean/ToyCoalesce/Basic.lean:241-243
def St.wr (s : St) (k : AccKind) (loc off : Nat) (v : Val) : St :=
  let s := s.logAcc loc off k
  { s with mem := fun l o => if l = loc ∧ o = off then v else s.mem l o }
```

```lean
-- lean/ToyCoalesce/Basic.lean:246-248
def writeCellsK (k : AccKind) (s : St) (loc off : Nat) : List Val → St
  | [] => s
  | v :: vs => writeCellsK k (s.wr k loc off v) loc (off + 1) vs
```

```lean
-- lean/ToyCoalesce/Basic.lean:251-251
def writeCells (s : St) (loc off : Nat) (vs : List Val) : St := writeCellsK .write s loc off vs
```

```lean
-- lean/ToyCoalesce/Basic.lean:255-255
def resetCells (s : St) (loc n : Nat) : St := writeCellsK .reset s loc 0 (List.replicate n .uninit)
```

```lean
-- lean/ToyCoalesce/Basic.lean:259-267
def readCells (s : St) (loc off : Nat) : Nat → St × Option (List Val)
  | 0 => (s, some [])
  | n + 1 =>
    let v := s.mem loc off
    let s := s.logAcc loc off .read
    if v = .uninit then (s.fail .ub, none) else
    match readCells s loc (off + 1) n with
    | (s', some vs) => (s', some (v :: vs))
    | (s', none) => (s', none)
```

```lean
-- lean/ToyCoalesce/Basic.lean:271-281
def resolvePlace (P : Prog) (s : St) (q : Place) : Option Place :=
  let q' : Option Place :=
    match s.alias with
    | some (prm, t) =>
      if q.base = prm then
        (if q.off + q.len ≤ t.len then some ⟨t.base, t.off + q.off, q.len⟩ else none)
      else some q
    | none => some q
  match q' with
  | some r => if s.live r.base = true ∧ r.off + r.len ≤ P.size r.base then some r else none
  | none => none
```

```lean
-- lean/ToyCoalesce/Basic.lean:284-286
def Val.addr? (A : Layout) : Val → Option Nat
  | .ptr l o => some (A l + o)
  | _ => none
```

```lean
-- lean/ToyCoalesce/Basic.lean:289-292
def Val.obs (A : Layout) : Val → EVal
  | .int n => .int n
  | .ptr l o => .addr (A l + o)
  | .uninit => .int 0
```

```lean
-- lean/ToyCoalesce/Basic.lean:295-325
def evalOp (ms : MoveSem) (P : Prog) (s : St) : Operand → St × Option (List Val)
  | .lit n => (s, some [.int n])
  | .addrOf q =>
    match resolvePlace P s q with
    | some r => (s, some [.ptr r.base r.off])
    | none => (s.fail .ub, none)
  | .copy q =>
    match resolvePlace P s q with
    | some r => readCells s r.base r.off r.len
    | none => (s.fail .ub, none)
  | .move q =>
    match resolvePlace P s q with
    | some r =>
      match readCells s r.base r.off r.len with
      | (s', some vs) =>
        if ms = .deinit then (writeCells s' r.base r.off (List.replicate r.len .uninit), some vs)
        else (s', some vs)
      | (s', none) => (s', none)
    | none => (s.fail .ub, none)
  | .load p len =>
    match resolvePlace P s p with
    | some r =>
      if r.len = 1 then
        match readCells s r.base r.off 1 with
        | (s', some [.ptr l o]) =>
          if s'.live l = true ∧ o + len ≤ P.size l then readCells s' l o len
          else (s'.fail .ub, none)
        | (s', some _) => (s'.fail .ub, none)
        | (s', none) => (s', none)
      else (s.fail .ub, none)
    | none => (s.fail .ub, none)
```

```lean
-- lean/ToyCoalesce/Basic.lean:328-336
def evalOps (ms : MoveSem) (P : Prog) (s : St) : List Operand → St × Option (List Val)
  | [] => (s, some [])
  | o :: os =>
    match evalOp ms P s o with
    | (s', some vs) =>
      match evalOps ms P s' os with
      | (s'', some ws) => (s'', some (vs ++ ws))
      | (s'', none) => (s'', none)
    | (s', none) => (s', none)
```

```lean
-- lean/ToyCoalesce/Basic.lean:339-344
def writeInOrder (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat) : List Operand → St
  | [] => s
  | o :: os =>
    match evalOp ms P s o with
    | (s', some vs) => writeInOrder ms P (writeCells s' loc off vs) loc (off + vs.length) os
    | (s', none) => s'
```

```lean
-- lean/ToyCoalesce/Basic.lean:347-348
def liveOthers (P : Prog) (s : St) (x : Nat) : List Nat :=
  (List.range P.nloc).filter fun z => z != x && s.live z
```

```lean
-- lean/ToyCoalesce/Basic.lean:352-356
def allocate (P : Prog) (s : St) (x : Nat) : St :=
  if x < P.nloc then
    let s := { s with conflicts := s.conflicts ++ (liveOthers P s x).map fun z => (x, z) }
    resetCells { s with live := fun z => if z = x then true else s.live z } x (P.size x)
  else s.fail .ub
```

```lean
-- lean/ToyCoalesce/Basic.lean:359-363
def deallocate (P : Prog) (s : St) (x : Nat) : St :=
  if s.live x = true then
    let s := resetCells s x (P.size x)
    { s with live := fun z => if z = x then false else s.live z }
  else s
```

```lean
-- lean/ToyCoalesce/Basic.lean:366-378
def cmpOp (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) : St :=
  match evalOp ms P s a with
  | (s1, some [va]) =>
    match evalOp ms P s1 b with
    | (s2, some [vb]) =>
      match va.addr? A, vb.addr? A with
      | some x, some y => s2.emit (.cmp (f x y))
      | _, _ => s2.fail .ub
    | (s2, some _) => s2.fail .ub
    | (s2, none) => s2
  | (s1, some _) => s1.fail .ub
  | (s1, none) => s1
```

```lean
-- lean/ToyCoalesce/Basic.lean:383-421
def execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) : St :=
  if s.status ≠ .running then s else
  match st with
  | .storageLive x => if s.inCall then s.fail .ub else allocate P s x
  | .storageDead x => if s.inCall then s.fail .ub else deallocate P s x
  | .assign lhs rhs =>
    if (rhs.map Operand.len).sum ≠ lhs.len then s.fail .ub else
    match resolvePlace P s lhs with
    | none => s.fail .ub
    | some r =>
      match sem.assign with
      | .atomic =>
        match evalOps sem.move P s rhs with
        | (s', some vs) => writeCells s' r.base r.off vs
        | (s', none) => s'
      | .inOrder => writeInOrder sem.move P s r.base r.off rhs
  | .store p v =>
    match resolvePlace P s p with
    | some r =>
      if r.len = 1 then
        match readCells s r.base r.off 1 with
        | (s1, some [.ptr l o]) =>
          match evalOp sem.move P s1 v with
          | (s2, some vs) =>
            if s2.live l = true ∧ o + vs.length ≤ P.size l then writeCells s2 l o vs
            else s2.fail .ub
          | (s2, none) => s2
        | (s1, some _) => s1.fail .ub
        | (s1, none) => s1
      else s.fail .ub
    | none => s.fail .ub
  | .ptrEq a b => cmpOp sem.move P A s a b (fun x y => decide (x = y))
  | .ptrInRange a b n => cmpOp sem.move P A s a b (fun x y => decide (y ≤ x ∧ x < y + n))
  | .out o =>
    match evalOp sem.move P s o with
    | (s', some vs) => s'.emit (.vals (vs.map (Val.obs A)))
    | (s', none) => s'
  | .call _ _ => s.fail .ub
  | .nop => s
```

```lean
-- lean/ToyCoalesce/Basic.lean:424-425
def execCallee (sem : Sem) (P : Prog) (A : Layout) (s : St) (b : List Stmt) : St :=
  b.foldl (execBasic sem P A) s
```

```lean
-- lean/ToyCoalesce/Basic.lean:428-450
def execStmt (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) : St :=
  if s.status ≠ .running then s else
  match st with
  | .call fn arg =>
    let c := P.fn fn
    match sem.move, arg with
    | .inPlaceCall, .move q =>
      match resolvePlace P s q with
      | none => s.fail .ub
      | some r =>
        if r.len ≠ P.size c.prm then s.fail .ub else
        let s1 := execCallee sem P A { s with alias := some (c.prm, r), inCall := true } c.body
        { s1 with alias := none, inCall := false }
    | _, _ =>
      match evalOp sem.move P s arg with
      | (s1, some vs) =>
        if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
        let s2 := allocate P s1 c.prm
        let s3 := writeCells s2 c.prm 0 vs
        let s4 := execCallee sem P A { s3 with inCall := true } c.body
        deallocate P { s4 with inCall := false } c.prm
      | (s1, none) => s1
  | st => execBasic sem P A s st
```

```lean
-- lean/ToyCoalesce/Basic.lean:453-455
def execTop (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) : St :=
  let s' := execStmt sem P A s st
  { s' with tick := s'.tick + 1 }
```

```lean
-- lean/ToyCoalesce/Basic.lean:458-459
def run (sem : Sem) (P : Prog) (A : Layout) : St :=
  P.code.foldl (execTop sem P A) St.init
```

```lean
-- lean/ToyCoalesce/Basic.lean:462-463
def layoutOK (P : Prog) (A : Layout) (cs : List (Nat × Nat)) : Bool :=
  cs.all fun c => decide (Disj (A c.1) (P.size c.1) (A c.2) (P.size c.2))
```

```lean
-- lean/ToyCoalesce/Basic.lean:466-472
def outcome (sem : Sem) (P : Prog) (A : Layout) : Outcome :=
  let s := run sem P A
  if layoutOK P A s.conflicts then
    match s.status with
    | .running => .done s.trace
    | .ub => .ub
  else .badLayout
```

```lean
-- lean/ToyCoalesce/Basic.lean:475-476
def Beh (sem : Sem) (P : Prog) (o : Outcome) : Prop :=
  ∃ A : Layout, outcome sem P A = o ∧ o ≠ .badLayout
```

```lean
-- lean/ToyCoalesce/Basic.lean:480-481
def Refines (semT : Sem) (T : Prog) (semS : Sem) (S : Prog) : Prop :=
  ∀ o, Beh semT T o → Beh semS S .ub ∨ Beh semS S o
```

```lean
-- lean/ToyCoalesce/Basic.lean:484-485
def BehEq (semT : Sem) (T : Prog) (semS : Sem) (S : Prog) : Prop :=
  ∀ o, Beh semT T o ↔ Beh semS S o
```

```lean
-- lean/ToyCoalesce/Basic.lean:490-492
def Operand.takesAddr (u : Nat) : Operand → Bool
  | .addrOf q => q.base == u
  | _ => false
```

```lean
-- lean/ToyCoalesce/Basic.lean:495-502
def Stmt.takesAddr (u : Nat) : Stmt → Bool
  | .assign _ rhs => rhs.any (Operand.takesAddr u)
  | .store _ v => v.takesAddr u
  | .ptrEq a b => a.takesAddr u || b.takesAddr u
  | .ptrInRange a b _ => a.takesAddr u || b.takesAddr u
  | .out o => o.takesAddr u
  | .call _ a => a.takesAddr u
  | _ => false
```

```lean
-- lean/ToyCoalesce/Basic.lean:506-509
def Stmt.escapesInPlace (P : Prog) (u : Nat) : Stmt → Bool
  | .call fn (.move q) => q.base == u && (P.fns.getD fn ⟨0, []⟩).body.any
      (Stmt.takesAddr (P.fns.getD fn ⟨0, []⟩).prm)
  | _ => false
```

```lean
-- lean/ToyCoalesce/Basic.lean:516-518
def AddrTaken (P : Prog) (u : Nat) : Prop :=
  (P.code.any (Stmt.takesAddr u) || P.fns.any (fun c => c.body.any (Stmt.takesAddr u)) ||
    P.code.any (Stmt.escapesInPlace P u)) = true
```

#### `ToyCoalesce/Upgrade.lean`

```lean
-- lean/ToyCoalesce/Upgrade.lean:15-19
def Stmt.upgradeCopy : Stmt → Stmt
  | .assign lhs [.copy q] => .assign lhs [.move q]
  | .call fn (.copy q) => .call fn (.move q)
  | .out (.copy q) => .out (.move q)
  | st => st
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:22-25
def modifyAt (f : Stmt → Stmt) : List Stmt → Nat → List Stmt
  | [], _ => []
  | st :: sts, 0 => f st :: sts
  | st :: sts, k + 1 => st :: modifyAt f sts k
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:28-29
def Prog.upgradeAt (P : Prog) (k : Nat) : Prog :=
  { P with body := modifyAt Stmt.upgradeCopy P.body k }
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:35-36
def WindowsDisjoint (a b : Place) : Prop :=
  a.base ≠ b.base ∨ a.off + a.len ≤ b.off ∨ b.off + b.len ≤ a.off
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:44-47
def UpgradeSite (P : Prog) (k : Nat) (q : Place) : Prop :=
  (∃ lhs, P.body[k]? = some (.assign lhs [.copy q]) ∧ WindowsDisjoint lhs q) ∨
  (∃ fn, P.body[k]? = some (.call fn (.copy q)) ∧ (P.fn fn).prm ≠ q.base) ∨
  P.body[k]? = some (.out (.copy q))
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:50-51
def CallSite (P : Prog) (k fn : Nat) (q : Place) : Prop :=
  P.body[k]? = some (.call fn (.copy q)) ∧ (P.fn fn).prm ≠ q.base
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:55-56
def afterUse (inclCall : Bool) (k : Nat) (e : Access) : Bool :=
  decide (k < e.tick) || (inclCall && decide (e.tick = k) && e.inCall)
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:60-64
def firstTouchNotRead (after : Access → Bool) (loc off : Nat) : List Access → Bool
  | [] => true
  | e :: es =>
    if after e && e.loc == loc && e.off == off then e.kind != .read
    else firstTouchNotRead after loc off es
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:70-71
def NoReadBeforeReinit (log : List Access) (k : Nat) (inclCall : Bool) (q : Place) : Prop :=
  ∀ j, j < q.len → firstTouchNotRead (afterUse inclCall k) q.base (q.off + j) log = true
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:78-80
def CalleeAvoids (log : List Access) (k : Nat) (q : Place) : Prop :=
  log.all (fun e => !(decide (e.tick = k) && e.inCall && decide (e.loc = q.base) &&
    decide (q.off ≤ e.off) && decide (e.off < q.off + q.len))) = true
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:86-87
def CalleeNoParamAddr (P : Prog) (fn : Nat) : Prop :=
  (P.fn fn).body.any (Stmt.takesAddr (P.fn fn).prm) = false
```

#### `ToyCoalesce/ObsAnalysis.lean`

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:17-21
def Operand.readsName (u : Nat) : Operand → Bool
  | .copy q => q.base == u
  | .move q => q.base == u
  | .load p _ => p.base == u
  | _ => false
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:24-26
def Operand.isLoad : Operand → Bool
  | .load _ _ => true
  | _ => false
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:29-36
def Stmt.operands : Stmt → List Operand
  | .assign _ rhs => rhs
  | .store _ v => [v]
  | .ptrEq a b => [a, b]
  | .ptrInRange a b _ => [a, b]
  | .out o => [o]
  | .call _ a => [a]
  | _ => []
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:40-43
def Stmt.mayReadNoCall (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  st.operands.any (Operand.readsName u) ||
  (match st with | .store p _ => p.base == u | _ => false) ||
  (decide (AddrTaken P u) && st.operands.any Operand.isLoad)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:47-49
def Stmt.mayRead (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  st.mayReadNoCall P u ||
  (match st with | .call fn _ => (P.fn fn).body.any (Stmt.mayReadNoCall P u) | _ => false)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:53-57
def Stmt.kills (P : Prog) (u : Nat) : Stmt → Bool
  | .storageLive x => x == u
  | .storageDead x => x == u
  | .assign lhs _ => lhs.base == u && lhs.off == 0 && lhs.len == P.size u
  | _ => false
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:60-60
abbrev ObsMask := Nat → Nat → Bool
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:65-68
def ObsCert (P : Prog) (O : ObsMask) : Prop :=
  ∀ t, t < P.code.length → ∀ u, u < P.nloc →
    ((P.code.getD t .nop).mayRead P u = true → O t u = true) ∧
    (O (t + 1) u = true → (P.code.getD t .nop).kills P u = false → O t u = true)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:72-75
def ObsCertBodyOnly (P : Prog) (O : ObsMask) : Prop :=
  ∀ t, t < P.body.length → ∀ u, u < P.nloc →
    ((P.code.getD t .nop).mayRead P u = true → O t u = true) ∧
    (O (t + 1) u = true → (P.code.getD t .nop).kills P u = false → O t u = true)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:78-81
def checkObs (P : Prog) (O : ObsMask) : Bool :=
  (List.range P.code.length).all fun t => (List.range P.nloc).all fun u =>
    (!(P.code.getD t .nop).mayRead P u || O t u) &&
    (!(O (t + 1) u && !(P.code.getD t .nop).kills P u) || O t u)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:85-87
def obsFrom (P : Prog) (u : Nat) : List Stmt → Bool
  | [] => false
  | st :: sts => st.mayRead P u || (!st.kills P u && obsFrom P u sts)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:90-90
def obsAnalysis (P : Prog) : ObsMask := fun t u => obsFrom P u (P.code.drop t)
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:101-119
def Licensed (ms : MoveSem) (P : Prog) (O : ObsMask) (k : Nat) (q : Place) : Prop :=
  match ms with
  | .asCopy => True
  | .deinit =>
    O (k + 1) q.base = false ∧
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      (P.fn fn).body.any (Stmt.mayReadNoCall P q.base) = false
  | .inPlaceCall =>
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      O (k + 1) q.base = false ∧
      (P.fn fn).body.any (fun st => st.operands.any (Operand.readsName q.base) ||
        (match st with
         | .store p _ => p.base == q.base
         | .assign lhs _ => lhs.base == q.base
         | _ => false)) = false ∧
      (decide (AddrTaken P q.base) && (P.fn fn).body.any (fun st =>
        st.operands.any Operand.isLoad || (match st with | .store _ _ => true | _ => false)))
        = false ∧
      ¬ AddrTaken P (P.fn fn).prm
```

#### `ToyCoalesce/Merge.lean`

```lean
-- lean/ToyCoalesce/Merge.lean:16-20
structure Edge where
  child : Nat
  parent : Nat
  off : Nat
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Merge.lean:23-23
abbrev Forest := List Edge
```

```lean
-- lean/ToyCoalesce/Merge.lean:26-26
def Forest.parentOf (μ : Forest) (x : Nat) : Option Edge := μ.find? (·.child == x)
```

```lean
-- lean/ToyCoalesce/Merge.lean:29-34
def Forest.resolveF (μ : Forest) : Nat → Nat → Nat × Nat
  | 0, x => (x, 0)
  | n + 1, x =>
    match μ.parentOf x with
    | some e => let r := μ.resolveF n e.parent; (r.1, r.2 + e.off)
    | none => (x, 0)
```

```lean
-- lean/ToyCoalesce/Merge.lean:37-37
def Forest.resolve (μ : Forest) (x : Nat) : Nat × Nat := μ.resolveF μ.length x
```

```lean
-- lean/ToyCoalesce/Merge.lean:39-39
def Forest.root (μ : Forest) (x : Nat) : Nat := (μ.resolve x).1
```

```lean
-- lean/ToyCoalesce/Merge.lean:41-41
def Forest.offset (μ : Forest) (x : Nat) : Nat := (μ.resolve x).2
```

```lean
-- lean/ToyCoalesce/Merge.lean:44-44
def Forest.inClass (μ : Forest) (x : Nat) : Bool := μ.any fun e => e.child == x || e.parent == x
```

```lean
-- lean/ToyCoalesce/Merge.lean:47-49
def nubNat : List Nat → List Nat
  | [] => []
  | x :: xs => x :: (nubNat xs).filter (· != x)
```

```lean
-- lean/ToyCoalesce/Merge.lean:52-52
def Forest.roots (μ : Forest) : List Nat := nubNat (μ.map fun e => μ.root e.child)
```

```lean
-- lean/ToyCoalesce/Merge.lean:57-58
def CallsInBounds (P : Prog) : Prop :=
  P.code.all (fun st => match st with | .call fn _ => decide (fn < P.fns.length) | _ => true) = true
```

```lean
-- lean/ToyCoalesce/Merge.lean:66-72
def ForestWF (P : Prog) (μ : Forest) : Prop :=
  (μ.map Edge.child).Nodup ∧
  (∀ e ∈ μ, e.child < P.nloc ∧ e.parent < P.nloc ∧ e.child ≠ e.parent ∧
    e.off + P.size e.child ≤ P.size e.parent) ∧
  (∀ x, x < P.nloc → μ.parentOf (μ.root x) = none) ∧
  (∀ c ∈ P.fns, μ.inClass c.prm = false) ∧
  CallsInBounds P
```

```lean
-- lean/ToyCoalesce/Merge.lean:79-84
def Operand.mapPlaces (f : Place → Place) : Operand → Operand
  | .copy q => .copy (f q)
  | .move q => .move (f q)
  | .lit n => .lit n
  | .addrOf q => .addrOf (f q)
  | .load p l => .load (f p) l
```

```lean
-- lean/ToyCoalesce/Merge.lean:87-96
def Stmt.mapPlaces (f : Place → Place) : Stmt → Stmt
  | .storageLive x => .storageLive x
  | .storageDead x => .storageDead x
  | .assign lhs rhs => .assign (f lhs) (rhs.map (Operand.mapPlaces f))
  | .store p v => .store (f p) (v.mapPlaces f)
  | .ptrEq a b => .ptrEq (a.mapPlaces f) (b.mapPlaces f)
  | .ptrInRange a b n => .ptrInRange (a.mapPlaces f) (b.mapPlaces f) n
  | .out o => .out (o.mapPlaces f)
  | .call fn a => .call fn (a.mapPlaces f)
  | .nop => .nop
```

```lean
-- lean/ToyCoalesce/Merge.lean:99-100
def Forest.mapPlace (μ : Forest) (q : Place) : Place :=
  ⟨μ.root q.base, μ.offset q.base + q.off, q.len⟩
```

```lean
-- lean/ToyCoalesce/Merge.lean:103-106
def Forest.coalesceStmt (μ : Forest) : Stmt → Stmt
  | .storageLive x => if μ.inClass x then .nop else .storageLive x
  | .storageDead x => if μ.inClass x then .nop else .storageDead x
  | st => st.mapPlaces μ.mapPlace
```

```lean
-- lean/ToyCoalesce/Merge.lean:109-113
def coalesce (μ : Forest) (P : Prog) : Prog :=
  { P with
    body := μ.roots.map Stmt.storageLive ++ P.body.map μ.coalesceStmt
    dtors := P.dtors.map μ.coalesceStmt
    fns := P.fns.map fun c => { c with body := c.body.map μ.coalesceStmt } }
```

```lean
-- lean/ToyCoalesce/Merge.lean:116-116
def single (x y f : Nat) : Forest := [⟨x, y, f⟩]
```

```lean
-- lean/ToyCoalesce/Merge.lean:121-121
def Forest.tcell (μ : Forest) (loc off : Nat) : Nat × Nat := (μ.root loc, μ.offset loc + off)
```

```lean
-- lean/ToyCoalesce/Merge.lean:127-137
def clobberFreeAux (μ : Forest) : List Access → (Nat × Nat → Option (Nat × Nat)) → Bool
  | [], _ => true
  | e :: es, lw =>
    match e.kind with
    | .read =>
      (match lw (μ.tcell e.loc e.off) with
       | some c => c == (e.loc, e.off)
       | none => true) && clobberFreeAux μ es lw
    | .write =>
      clobberFreeAux μ es fun t => if t = μ.tcell e.loc e.off then some (e.loc, e.off) else lw t
    | .reset => clobberFreeAux μ es lw
```

```lean
-- lean/ToyCoalesce/Merge.lean:141-142
def NoValueClobber (μ : Forest) (log : List Access) : Prop :=
  clobberFreeAux μ log (fun _ => none) = true
```

```lean
-- lean/ToyCoalesce/Merge.lean:151-153
def NoValueClobberStmt (ms : MoveSem) (μ : Forest) (P : Prog) : Prop :=
  ∀ A, outcome ⟨ms, .atomic⟩ P A ≠ .ub → outcome ⟨ms, .atomic⟩ P A ≠ .badLayout →
    NoValueClobber μ (run ⟨ms, .atomic⟩ P A).log
```

```lean
-- lean/ToyCoalesce/Merge.lean:159-164
def lexLiveBefore (P : Prog) (u t : Nat) : Bool :=
  (P.code.take t).foldl (fun b st =>
    match st with
    | .storageLive x => if x == u then true else b
    | .storageDead x => if x == u then false else b
    | _ => b) false
```

```lean
-- lean/ToyCoalesce/Merge.lean:167-168
def LexLiveAt (P : Prog) (u t : Nat) : Bool :=
  lexLiveBefore P u t || (P.code.getD t .nop == .storageLive u)
```

```lean
-- lean/ToyCoalesce/Merge.lean:171-174
def Stmt.readsByName (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  let loc1 := fun (s : Stmt) => s.operands.any (Operand.readsName u) ||
    (match s with | .store p _ => p.base == u | _ => false)
  loc1 st || (match st with | .call fn _ => (P.fn fn).body.any loc1 | _ => false)
```

```lean
-- lean/ToyCoalesce/Merge.lean:179-183
def Stmt.writesByName (P : Prog) (u : Nat) (st : Stmt) : Bool :=
  let loc1 := fun (s : Stmt) => match s with | .assign lhs _ => lhs.base == u | _ => false
  loc1 st || (match st with
    | .call fn a => (P.fn fn).body.any loc1 || (match a with | .move q => q.base == u | _ => false)
    | _ => false)
```

```lean
-- lean/ToyCoalesce/Merge.lean:187-191
def Stmt.calleeTouchesByName (P : Prog) (u : Nat) : Stmt → Bool
  | .call fn _ => (P.fn fn).body.any fun s =>
      s.operands.any (Operand.readsName u) ||
      (match s with | .store p _ => p.base == u | .assign lhs _ => lhs.base == u | _ => false)
  | _ => false
```

```lean
-- lean/ToyCoalesce/Merge.lean:198-201
def AccessPt (P : Prog) (u p : Nat) : Bool :=
  (P.code.getD (p / 2) .nop).calleeTouchesByName P u ||
  (if p % 2 = 0 then (P.code.getD (p / 2) .nop).readsByName P u
   else (P.code.getD (p / 2) .nop).writesByName P u)
```

```lean
-- lean/ToyCoalesce/Merge.lean:204-207
inductive Notion where
  | lexical
  | precise
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Merge.lean:212-217
def InIv (nt : Notion) (P : Prog) (u p : Nat) : Bool :=
  match nt with
  | .lexical => LexLiveAt P u (p / 2)
  | .precise =>
    (List.range (p + 1)).any (AccessPt P u) &&
    ((List.range (2 * P.code.length + 2)).filter (p ≤ ·)).any (AccessPt P u)
```

```lean
-- lean/ToyCoalesce/Merge.lean:220-221
def IvOverlap (nu nv : Notion) (P : Prog) (u v : Nat) : Prop :=
  ∃ p, p < 2 * P.code.length + 2 ∧ InIv nu P u p = true ∧ InIv nv P v p = true
```

```lean
-- lean/ToyCoalesce/Merge.lean:227-227
def LexOverlap (P : Prog) (u v : Nat) : Prop := IvOverlap .lexical .lexical P u v
```

```lean
-- lean/ToyCoalesce/Merge.lean:235-236
def Forest.sameClass (μ : Forest) (u v : Nat) : Bool :=
  μ.inClass u && μ.inClass v && μ.root u == μ.root v
```

```lean
-- lean/ToyCoalesce/Merge.lean:241-242
def Forest.windowsOverlap (μ : Forest) (P : Prog) (u v : Nat) : Bool :=
  decide (μ.offset u < μ.offset v + P.size v ∧ μ.offset v < μ.offset u + P.size u)
```

```lean
-- lean/ToyCoalesce/Merge.lean:246-248
def ClassAddrDisjoint (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    μ.windowsOverlap P u v = true → AddrTaken P u → AddrTaken P v → ¬ LexOverlap P u v
```

```lean
-- lean/ToyCoalesce/Merge.lean:256-258
def ClassAddrDisjointW (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    AddrTaken P u → AddrTaken P v → ¬ LexOverlap P u v
```

```lean
-- lean/ToyCoalesce/Merge.lean:265-266
def EdgeAddrCheck (P : Prog) (μ : Forest) : Prop :=
  ∀ e ∈ μ, AddrTaken P e.child → AddrTaken P e.parent → ¬ LexOverlap P e.child e.parent
```

```lean
-- lean/ToyCoalesce/Merge.lean:272-274
def RootAddrCheck (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → μ.inClass u = true → u ≠ μ.root u → AddrTaken P u →
    AddrTaken P (μ.root u) → ¬ LexOverlap P u (μ.root u)
```

```lean
-- lean/ToyCoalesce/Merge.lean:284-287
structure UFBlock where
  members : List Nat
  ticks : List Nat
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyCoalesce/Merge.lean:290-291
def aoTicks (P : Prog) (u : Nat) : List Nat :=
  if AddrTaken P u then (List.range (P.code.length + 1)).filter (LexLiveAt P u) else []
```

```lean
-- lean/ToyCoalesce/Merge.lean:294-294
def ufInit (P : Prog) : List UFBlock := (List.range P.nloc).map fun u => ⟨[u], aoTicks P u⟩
```

```lean
-- lean/ToyCoalesce/Merge.lean:298-305
def ufStep (bs : List UFBlock) (e : Edge) : Option (List UFBlock) :=
  match bs.find? (·.members.contains e.child), bs.find? (·.members.contains e.parent) with
  | some b1, some b2 =>
    if b1 = b2 then none
    else if b1.ticks.any (b2.ticks.contains ·) then none
    else some (⟨b1.members ++ b2.members, b1.ticks ++ b2.ticks⟩ ::
      bs.filter fun b => b != b1 && b != b2)
  | _, _ => none
```

```lean
-- lean/ToyCoalesce/Merge.lean:308-308
def ufCheck (P : Prog) (μ : Forest) : Bool := (μ.foldlM ufStep (ufInit P)).isSome
```

```lean
-- lean/ToyCoalesce/Merge.lean:335-335
abbrev Policy := Bool → Notion
```

```lean
-- lean/ToyCoalesce/Merge.lean:340-343
def PolicyCheck (pol : Policy) (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    μ.windowsOverlap P u v = true →
    ¬ IvOverlap (pol (decide (AddrTaken P u))) (pol (decide (AddrTaken P v))) P u v
```

```lean
-- lean/ToyCoalesce/Merge.lean:350-352
def PolicySound (pol : Policy) : Prop :=
  ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWF P μ → PolicyCheck pol P μ →
    Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P
```

#### `ToyCoalesce/Staging.lean`

```lean
-- lean/ToyCoalesce/Staging.lean:16-20
def Operand.mayOverlap (lhs : Place) : Operand → Bool
  | .copy q => !decide (WindowsDisjoint lhs q)
  | .move q => !decide (WindowsDisjoint lhs q)
  | .load _ _ => true
  | _ => false
```

```lean
-- lean/ToyCoalesce/Staging.lean:24-25
def NeedsStaging (lhs : Place) (rhs : List Operand) : Bool :=
  decide (2 ≤ rhs.length) && rhs.any (Operand.mayOverlap lhs)
```

```lean
-- lean/ToyCoalesce/Staging.lean:28-31
def stmtsNoStaging (sts : List Stmt) : Bool :=
  sts.all fun st => match st with
    | .assign lhs rhs => !NeedsStaging lhs rhs
    | _ => true
```

```lean
-- lean/ToyCoalesce/Staging.lean:36-36
def Place.paramSplit (prm : Nat) (a b : Place) : Bool := (a.base == prm) != (b.base == prm)
```

```lean
-- lean/ToyCoalesce/Staging.lean:41-45
def Operand.mayOverlapParam (prm : Nat) (lhs : Place) : Operand → Bool
  | .copy q => !decide (WindowsDisjoint lhs q) || Place.paramSplit prm lhs q
  | .move q => !decide (WindowsDisjoint lhs q) || Place.paramSplit prm lhs q
  | .load _ _ => true
  | _ => false
```

```lean
-- lean/ToyCoalesce/Staging.lean:49-50
def NeedsStagingParam (prm : Nat) (lhs : Place) (rhs : List Operand) : Bool :=
  decide (2 ≤ rhs.length) && rhs.any (Operand.mayOverlapParam prm lhs)
```

```lean
-- lean/ToyCoalesce/Staging.lean:53-56
def calleeNoStaging (c : Callee) : Bool :=
  c.body.all fun st => match st with
    | .assign lhs rhs => !NeedsStagingParam c.prm lhs rhs
    | _ => true
```

```lean
-- lean/ToyCoalesce/Staging.lean:59-60
def NoStagingNeeded (P : Prog) : Prop :=
  (stmtsNoStaging P.code && P.fns.all calleeNoStaging) = true
```

```lean
-- lean/ToyCoalesce/Staging.lean:65-65
def CalleesNoStaging (P : Prog) : Prop := P.fns.all calleeNoStaging = true
```

```lean
-- lean/ToyCoalesce/Staging.lean:72-86
def stageList (next : Nat) : List Stmt → List Stmt × List Nat
  | [] => ([], [])
  | st :: sts =>
    match st with
    | .assign lhs rhs =>
      if NeedsStaging lhs rhs then
        let r := stageList (next + 1) sts
        ([.storageLive next, .assign ⟨next, 0, lhs.len⟩ rhs,
          .assign lhs [.move ⟨next, 0, lhs.len⟩], .storageDead next] ++ r.1, lhs.len :: r.2)
      else
        let r := stageList next sts
        (st :: r.1, r.2)
    | _ =>
      let r := stageList next sts
      (st :: r.1, r.2)
```

```lean
-- lean/ToyCoalesce/Staging.lean:90-93
def stage (P : Prog) : Prog :=
  let b := stageList P.nloc P.body
  let d := stageList (P.nloc + b.2.length) P.dtors
  { P with sizes := P.sizes ++ b.2 ++ d.2, body := b.1, dtors := d.1 }
```

```lean
-- lean/ToyCoalesce/Staging.lean:96-101
def Operand.locals : Operand → List Nat
  | .copy q => [q.base]
  | .move q => [q.base]
  | .lit _ => []
  | .addrOf q => [q.base]
  | .load p _ => [p.base]
```

```lean
-- lean/ToyCoalesce/Staging.lean:103-112
def Stmt.locals (P : Prog) : Stmt → List Nat
  | .storageLive x => [x]
  | .storageDead x => [x]
  | .assign lhs rhs => lhs.base :: rhs.flatMap Operand.locals
  | .store p v => p.base :: v.locals
  | .ptrEq a b => a.locals ++ b.locals
  | .ptrInRange a b _ => a.locals ++ b.locals
  | .out o => o.locals
  | .call fn a => (P.fn fn).prm :: a.locals
  | .nop => []
```

```lean
-- lean/ToyCoalesce/Staging.lean:114-115
def LocalsInRange (P : Prog) : Prop :=
  ((P.code ++ P.fns.flatMap (·.body)).all fun st => (st.locals P).all (· < P.nloc)) = true
```

```lean
-- lean/ToyCoalesce/Staging.lean:120-120
def ParamsInRange (P : Prog) : Prop := P.fns.all (fun c => decide (c.prm < P.nloc)) = true
```

#### `ToyCoalesce/VC.lean`

```lean
-- lean/ToyCoalesce/VC.lean:16-17
def Valid (sem : Sem) (P : Prog) (Post : List Event → Prop) : Prop :=
  ∀ o, Beh sem P o → ∃ t, o = .done t ∧ Post t
```

```lean
-- lean/ToyCoalesce/VC.lean:21-23
def Event.erase : Event → Event
  | .vals vs => .vals (vs.map fun v => match v with | .int n => .int n | .addr _ => .addr 0)
  | .cmp _ => .cmp false
```

```lean
-- lean/ToyCoalesce/VC.lean:26-27
def AddrFree (Post : List Event → Prop) : Prop :=
  ∀ t t', t.map Event.erase = t'.map Event.erase → (Post t ↔ Post t')
```

```lean
-- lean/ToyCoalesce/VC.lean:30-30
def UBFree (sem : Sem) (P : Prog) : Prop := ¬ Beh sem P .ub
```

#### Key definitions unfolded (prose)

* Unfolded (prose) `Refines semT T semS S`: for every outcome `o` produced by `T` under `semT` on some
  layout that does not exclude the run, either `S` has undefined behaviour under `semS` on some
  non-excluded layout, or `o` is produced by `S` under `semS` on some non-excluded layout.
* Unfolded (prose) `NoReadBeforeReinit log k inclCall q`: for each offset `j < q.len`, scanning `log`
  in order and considering the entries made after the use at tick `k` (later ticks, plus, if
  `inclCall`, the entries made inside the callee at tick `k`) that touch cell `(q.base, q.off + j)`,
  the first such entry, if any, is a write or a reset, not a read.
* Unfolded (prose) `NoValueClobber μ log`: scanning `log`, keep for each coalesced cell the source
  cell of its last data write (resets ignored); every read of a source cell must find either no such
  write or a write to that same source cell. `NoValueClobberStmt ms μ P` requires this of the
  atomic-assignment log of every run of `P` that is neither undefined nor excluded.
* Unfolded (prose) `ClassAddrDisjoint P μ`: for all distinct locals `u`, `v` of `P` in the same
  nontrivial class whose root-relative windows intersect, if both are address-taken then there is
  no tick during which both are lexically allocated.
* Unfolded (prose) `ForestWF P μ`: edges have distinct children; each edge joins two distinct
  existing locals and the child's window fits in the parent; following edges from any local ends at
  a local with no parent; no callee parameter local occurs in an edge; and every top-level call
  names an existing callee (`CallsInBounds P`).
* Unfolded (prose) `AccessPt P u p`: with `t = p / 2` (floor division) and `st` the top-level
  statement at tick `t`, the point `p` is an access point of `u` if `st` is a call whose callee body
  reads or writes `u` by name (both halves), or if `p` is even and `st` reads `u` by name, or if `p` is
  odd and `st` writes `u` by name (an assignment to a place based at `u`, or a call passing a place
  based at `u` by `move`).
* Unfolded (prose) `NoStagingNeeded P`: no top-level assignment with two or more operands has an
  operand that is a `load` or reads a place whose window intersects the left side; and, for every
  callee `c`, no assignment of `c.body` with two or more operands has an operand that is a `load`,
  reads a place whose window intersects the left side, or reads a place of which exactly one of it
  and the left side is based at `c.prm` (`Place.paramSplit`).

### Cards

In every hypothesis ledger, `tight` means: the named counterexample theorem exhibits an instance, in the stated witness class, satisfying all the other hypotheses of the theorem the hypothesis belongs to, in which the conclusion fails. It does not mean the hypothesis is necessary outside that class.

#### `upgrade-moveAsCopy-equivalence` (theorem)

**Plain claim.** Under `MoveSem.asCopy`, for either assignment order, every program `P`, every body index `k` and every layout `A`, the program `P.upgradeAt k` (whose statement `k`, if it is `lhs := [copy q]`, `call fn (copy q)` or `out (copy q)`, has `copy q` replaced by `move q`) has the same outcome as `P`.

**Tier.** T0 — Reference point: under `MoveSem.asCopy`, `move q` and `copy q` take identical branches of the interpreter (`evalOp_move_eq_copy`); recorded as the baseline against which the other two `move` semantics are compared.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/Upgrade.lean:201-202
theorem upgrade_outcome_eq_moveAsCopy (am : AssignMode) (P : Prog) (k : Nat) (A : Layout) :
    outcome ⟨.asCopy, am⟩ (P.upgradeAt k) A = outcome ⟨.asCopy, am⟩ P A := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** Any program; e.g. `pDtor` with `k = 5` on `A0` (`ex_moveSem_outcomes`). (Lean: `ex_moveSem_outcomes`)

**Non-claims.** Listed under `## Boundaries` (card `upgrade-moveAsCopy-equivalence`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/unsafe-code-guidelines#188, "What about: use-after-move and (maybe) use-after-drop" (open issue; mentioned in prose, not a subject, not normative).
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.

**Design question.** When may the last `copy` of a slot be upgraded to `move`? Under the copy reading of `move`: always (reference point).

#### `upgrade-moveDeinit-iff-no-read-before-reinit` (characterization)

**Plain claim.** Under `MoveSem.deinit` (either assignment order), for an upgrade site `k` of place `q` (`lhs := [copy q]` with `lhs` disjoint from `q`, `call fn (copy q)` with the callee parameter different from `q.base`, or `out (copy q)`) and a layout on which the source run is neither undefined nor excluded, the upgraded program has the same outcome iff every cell of `q` is not read after the use (inside the callee at tick `k`, at later ticks, through pointers, or in the destructor block) before it is written or reset; and, for an upgrade site, if that condition holds on every layout whose source run is neither undefined nor excluded, the upgrade is a refinement.

**Tier.** T2 — The informal rule in the `Operand::Move` documentation ("should not emit MIR that may attempt a subsequent second load ... without first re-initializing it") made precise as an exact per-run characterization, covering reads through pointers, in callees and in destructors.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfObs.lean:2360-2364
theorem upgrade_moveDeinit_outcome_eq_iff_noReadBeforeReinit (am : AssignMode) (P : Prog)
    (k : Nat) (q : Place) (hsite : UpgradeSite P k q) (A : Layout)
    (hub : outcome ⟨.deinit, am⟩ P A ≠ .ub) (hbad : outcome ⟨.deinit, am⟩ P A ≠ .badLayout) :
    outcome ⟨.deinit, am⟩ (P.upgradeAt k) A = outcome ⟨.deinit, am⟩ P A ↔
      NoReadBeforeReinit (run ⟨.deinit, am⟩ P A).log k true q := by …
```

```lean
-- lean/ToyCoalesce/PfObs.lean:2382-2386
theorem upgrade_moveDeinit_refines_of_noReadBeforeReinit (am : AssignMode) (P : Prog)
    (k : Nat) (q : Place) (hsite : UpgradeSite P k q)
    (hno : ∀ A, outcome ⟨.deinit, am⟩ P A ≠ .ub → outcome ⟨.deinit, am⟩ P A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.deinit, am⟩ P A).log k true q) :
    Refines ⟨.deinit, am⟩ (P.upgradeAt k) ⟨.deinit, am⟩ P := by …
```

**Hypothesis ledger.**

* `hsite (iff form)` — restricts to statements in which the upgraded operand is the single read of `q` and the write of the statement cannot re-initialize `q` — **tight**: cex_upgrade_deinit_iff_lhs_overlap (witness class: a one-local program `x := copy x`)
* `hub` — the source run is not undefined behaviour (otherwise both runs may be UB while the condition fails) — **tight**: cex_upgrade_deinit_iff_source_ub (witness class: a two-local program with an undefined destructor)
* `hbad` — the source run is not excluded (excluded runs have equal outcomes regardless) — **tight**: cex_upgrade_deinit_iff_bad_layout (witness class: the all-zero layout)
* `hsite (refinement form)` — ties the condition to the upgraded place; tight as a whole (a place other than the upgraded one); its left-side-disjointness and parameter conjuncts are not shown needed for the refinement form — **tight**: cex_upgrade_deinit_refines_needs_site (witness class: a two-local program, `q` a place other than the upgraded one)
* `hno (refinement form)` — the dynamic condition on every non-UB, non-excluded layout — **tight**: cex_upgrade_moveDeinit_dtorLoad (witness class: three locals and a one-statement destructor block)

**Depth.** substantive

**Non-vacuity witness.** `pNoDtor` (the destructor-load program without its destructor), site 5, layout `A0`. (Lean: `nonvacuous_upgrade_moveDeinit_iff`, `nonvacuous_upgrade_moveDeinit_refines`)

**Non-claims.** Listed under `## Boundaries` (card `upgrade-moveDeinit-iff-no-read-before-reinit`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/unsafe-code-guidelines#188, "What about: use-after-move and (maybe) use-after-drop" (open issue; mentioned in prose, not a subject, not normative).
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.

**Design question.** Under the de-initializing reading of `move`, when is a copy-to-move upgrade sound? Per layout: exactly when no cell of the place is read before re-initialization; as a refinement: whenever that holds on every non-UB, non-excluded layout.

#### `upgrade-moveInPlaceCall-sufficient-conditions` (theorem)

**Plain claim.** Under `MoveSem.inPlaceCall` (either assignment order): upgrading a body statement that is not a call leaves the outcome unchanged on every layout; and, for a call site `call fn (copy q)` whose callee parameter is different from `q.base`, upgrading the argument is a refinement if (a) on every layout whose source run is neither undefined nor excluded, no cell of `q` is read after the call returns before it is written or reset, (b) on every such layout, the callee accesses no cell of `q` during the call, and (c) the callee's parameter local is not address-taken anywhere in `P` (`¬ AddrTaken P (P.fn fn).prm`; the parameter is a local of the caller's frame, so taking its address outside the callee also counts).

**Tier.** T2 — Makes precise, for an in-place reading of call arguments, which conditions suffice; each of the three conditions is shown tight.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfInPlace.lean:1818-1827
theorem upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_paramNotAddrTaken
    (am : AssignMode) (P : Prog) (k fn : Nat) (q : Place) (hsite : CallSite P k fn q)
    (ha : ∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ P A).log k false q)
    (hb : ∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
      CalleeAvoids (run ⟨.inPlaceCall, am⟩ P A).log k q)
    (hc : ¬ AddrTaken P (P.fn fn).prm) :
    Refines ⟨.inPlaceCall, am⟩ (P.upgradeAt k) ⟨.inPlaceCall, am⟩ P := by …
```

```lean
-- lean/ToyCoalesce/Upgrade.lean:212-214
theorem upgrade_outcome_eq_moveInPlaceCall_of_not_call (am : AssignMode) (P : Prog) (k : Nat)
    (hnc : ∀ fn a, P.body[k]? ≠ some (.call fn a)) (A : Layout) :
    outcome ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A = outcome ⟨.inPlaceCall, am⟩ P A := by …
```

**Hypothesis ledger.**

* `hnc (non-call form)` — the statement is not a call — **tight**: cex_upgrade_inPlaceCall_call_site (witness class: the call program pIPStore)
* `hsite` — the statement is a call whose argument is `copy q` and whose callee parameter is not `q.base` — **unknown**
* `ha` — after the call, `q` holds the callee's final parameter contents — **tight**: cex_upgrade_moveInPlaceCall_noReadAfterCall, with pIPAfter_violates_noReadAfterCall (the hypothesis `ha` itself fails: the source run on `A0` completes) (witness class: three locals, one-statement callee)
* `hb` — the callee must not reach `q` (by name or through escaped pointers, reads or writes) — **tight**: cex_upgrade_moveInPlaceCall_calleeAvoids, with pIPStore_violates_calleeAvoids (the hypothesis `hb` itself fails: the source run on `A0` completes) (witness class: callee storing through an escaped pointer, then reading its parameter)
* `hc` — in place, the parameter local is never allocated and its address is an address inside `q`; a pointer to it or a comparison with its address anywhere in `P` observes the difference — **tight**: cex_upgrade_moveInPlaceCall_noParamAddr (witness class: callee comparing `&param` with an escaped pointer); cex_inPlaceCall_param_addrTaken_in_caller and cex_inPlaceCall_param_conflict (witness class: callee body never takes its parameter's address, the caller does)

**Depth.** substantive

**Non-vacuity witness.** `pIPOk` (the callee reads its parameter and does nothing else), call site 4; `pReuse`, body index 3 (not a call). (Lean: `nonvacuous_upgrade_moveInPlaceCall`, `nonvacuous_upgrade_outcome_eq_moveInPlaceCall_of_not_call`)

**Non-claims.** Listed under `## Boundaries` (card `upgrade-moveInPlaceCall-sufficient-conditions`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/unsafe-code-guidelines#188, "What about: use-after-move and (maybe) use-after-drop" (open issue; mentioned in prose, not a subject, not normative).
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.
* R. Jung, H.-H. Dang, J. Kang, D. Dreyer, "Stacked Borrows: An Aliasing Model for Rust", PACMPL 4 (POPL), Article 41, 2020, doi:10.1145/3371109: an aliasing model with function-call protectors, which `MoveSem.inPlaceCall` does not model (bibliographic data verified; full text not inspected).

**Design question.** Under in-place passing of moved call arguments, what must a copy-to-move upgrade of a call argument check?

#### `destructor-load-breaks-deinit-upgrade` (counterexample)

**Plain claim.** Under `MoveSem.deinit` with atomic assignments (`semD`): in `pDtor` (x := 7; p := &x; y := copy x at body index 5; out y; a destructor block that loads through p), body index 5 is an upgrade site, the source completes with `[7, 7]` on layout `A0` while the `MoveSem.deinit` upgrade has undefined behaviour there, the no-read-before-re-initialization condition fails, and the upgrade is not a refinement; without the destructor block the same upgrade is a refinement (positive control `pNoDtor_upgrade_refines`).

**Tier.** T1 — The destructor-on-return-path hazard, made concrete and kernel-checked. Paired with `upgrade-moveDeinit-iff-no-read-before-reinit` (tightness witness of its `hno`) and `destructor-blind-analysis-admits-unsound-upgrade`.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:70-75
theorem cex_upgrade_moveDeinit_dtorLoad :
    UpgradeSite pDtor 5 qx ∧
    outcome semD pDtor A0 = .done [.vals [.int 7], .vals [.int 7]] ∧
    outcome semD (pDtor.upgradeAt 5) A0 = .ub ∧
    ¬ NoReadBeforeReinit (run semD pDtor A0).log 5 true qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := by …
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:82-82
theorem pNoDtor_upgrade_refines : Refines semD (pNoDtor.upgradeAt 5) semD pNoDtor := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** The program `pDtor` itself (all claims are about it). (Lean: `cex_upgrade_moveDeinit_dtorLoad`)

**Positive control.** `pNoDtor_upgrade_refines` (quoted above).

**Non-claims.** Listed under `## Boundaries` (card `destructor-load-breaks-deinit-upgrade`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/unsafe-code-guidelines#188, "What about: use-after-move and (maybe) use-after-drop" (open issue; mentioned in prose, not a subject, not normative).

**Design question.** Must copy-to-move analyses consider reads in destructors run on the return path? Yes (in the toy, under `MoveSem.deinit`).

#### `in-place-call-upgrade-counterexamples` (counterexample)

**Plain claim.** Under `MoveSem.inPlaceCall` with atomic assignments (`semI`), each of the conditions (a) no read of `q` after the call, (b) the callee does not access `q`, (c) the callee's parameter local is not address-taken can fail alone, with the call site and the other two holding (the dynamic ones on every layout whose source run is neither undefined nor excluded), and the call-argument upgrade then is not a refinement; (c) can fail through the caller alone, under either assignment order (the caller takes the parameter local's address, or allocates it and compares its address, while the callee body never takes it); and, with atomic assignments (`semI`, `semD`), a callee that writes its parameter and then loads through an escaped pointer to the argument breaks the upgrade under both `MoveSem.inPlaceCall` and `MoveSem.deinit`.

**Tier.** T1 — Concrete witnesses for each in-place condition. Paired with `upgrade-moveInPlaceCall-sufficient-conditions` (tightness witnesses of `ha`, `hb`, `hc`).

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:90-96
theorem cex_upgrade_moveInPlaceCall_calleeAvoids :
    CallSite pIPStore 4 0 qx ∧
    (∀ A, outcome semI pIPStore A ≠ .ub → outcome semI pIPStore A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPStore A).log 4 false qx) ∧
    ¬ AddrTaken pIPStore (pIPStore.fn 0).prm ∧
    ¬ CalleeAvoids (run semI pIPStore A0).log 4 qx ∧
    ¬ Refines semI (pIPStore.upgradeAt 4) semI pIPStore := by …
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:109-116
theorem cex_upgrade_moveInPlaceCall_noParamAddr :
    CallSite pIPAddr 4 0 qx ∧
    (∀ A, outcome semI pIPAddr A ≠ .ub → outcome semI pIPAddr A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPAddr A).log 4 false qx) ∧
    (∀ A, outcome semI pIPAddr A ≠ .ub → outcome semI pIPAddr A ≠ .badLayout →
      CalleeAvoids (run semI pIPAddr A).log 4 qx) ∧
    AddrTaken pIPAddr (pIPAddr.fn 0).prm ∧
    ¬ Refines semI (pIPAddr.upgradeAt 4) semI pIPAddr := by …
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:130-136
theorem cex_upgrade_moveInPlaceCall_noReadAfterCall :
    CallSite pIPAfter 4 0 qx ∧
    (∀ A, outcome semI pIPAfter A ≠ .ub → outcome semI pIPAfter A ≠ .badLayout →
      CalleeAvoids (run semI pIPAfter A).log 4 qx) ∧
    ¬ AddrTaken pIPAfter (pIPAfter.fn 0).prm ∧
    ¬ NoReadBeforeReinit (run semI pIPAfter A0).log 4 false qx ∧
    ¬ Refines semI (pIPAfter.upgradeAt 4) semI pIPAfter := by …
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:149-154
theorem cex_upgrade_callee_load_escaped :
    ¬ CalleeAvoids (run semI pIPLoad A0).log 4 qx ∧
    ¬ NoReadBeforeReinit (run semD pIPLoad A0).log 4 true qx ∧
    outcome semI (pIPLoad.upgradeAt 4) A0 = .done [.vals [.int 2]] ∧
    ¬ Refines semI (pIPLoad.upgradeAt 4) semI pIPLoad ∧
    ¬ Refines semD (pIPLoad.upgradeAt 4) semD pIPLoad := by …
```

```lean
-- lean/ToyCoalesce/Refuted.lean:111-123
theorem cex_inPlaceCall_param_addrTaken_in_caller (am : AssignMode) :
    CallSite pPrmEscaped 6 0 qx ∧ UpgradeSite pPrmEscaped 6 qx ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ pPrmEscaped A).log 6 false qx) ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .badLayout →
      CalleeAvoids (run ⟨.inPlaceCall, am⟩ pPrmEscaped A).log 6 qx) ∧
    CalleeNoParamAddr pPrmEscaped 0 ∧ AddrTaken pPrmEscaped (pPrmEscaped.fn 0).prm ∧
    ObsCert pPrmEscaped (obsAnalysis pPrmEscaped) ∧
    LicensedNoParamAddr .inPlaceCall pPrmEscaped (obsAnalysis pPrmEscaped) 6 qx ∧
    outcome ⟨.inPlaceCall, am⟩ (pPrmEscaped.upgradeAt 6) A0 = .ub ∧
    ¬ Refines ⟨.inPlaceCall, am⟩ (pPrmEscaped.upgradeAt 6) ⟨.inPlaceCall, am⟩ pPrmEscaped := by …
```

```lean
-- lean/ToyCoalesce/Refuted.lean:146-155
theorem cex_inPlaceCall_param_conflict (am : AssignMode) :
    CallSite pPrmConflict 5 0 ⟨2, 0, 1⟩ ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ pPrmConflict A).log 5 false ⟨2, 0, 1⟩) ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .badLayout →
      CalleeAvoids (run ⟨.inPlaceCall, am⟩ pPrmConflict A).log 5 ⟨2, 0, 1⟩) ∧
    CalleeNoParamAddr pPrmConflict 0 ∧ AddrTaken pPrmConflict (pPrmConflict.fn 0).prm ∧
    ¬ Refines ⟨.inPlaceCall, am⟩ (pPrmConflict.upgradeAt 5) ⟨.inPlaceCall, am⟩ pPrmConflict := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** The programs `pIPStore`, `pIPAddr`, `pIPAfter`, `pIPLoad`, `pPrmEscaped`, `pPrmConflict`. (Lean: `cex_upgrade_moveInPlaceCall_calleeAvoids`)

**Non-claims.** Listed under `## Boundaries` (card `in-place-call-upgrade-counterexamples`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/unsafe-code-guidelines#188, "What about: use-after-move and (maybe) use-after-drop" (open issue; mentioned in prose, not a subject, not normative).

**Design question.** Which in-place passing hazards does a copy-to-move upgrade of a call argument face?

#### `moveDeinit-moveInPlaceCall-incomparable` (counterexample)

**Plain claim.** Under atomic assignments (`semD` = `MoveSem.deinit`, `semI` = `MoveSem.inPlaceCall`), the two semantics admit incomparable sets of refining upgrades: on `pIPStore` (callee stores 2 through an escaped pointer to x, then prints its parameter) the call-argument upgrade is a refinement under `MoveSem.deinit` but not under `MoveSem.inPlaceCall`; on `pReuse` (y := copy x; out x) the assignment upgrade is a refinement under `MoveSem.inPlaceCall` but not under `MoveSem.deinit`.

**Tier.** T1 — Makes precise that the two candidate operational readings of `move` license different upgrades.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:166-170
theorem moveDeinit_moveInPlaceCall_upgrades_incomparable :
    (Refines semD (pIPStore.upgradeAt 4) semD pIPStore ∧
      ¬ Refines semI (pIPStore.upgradeAt 4) semI pIPStore) ∧
    (Refines semI (pReuse.upgradeAt 3) semI pReuse ∧
      ¬ Refines semD (pReuse.upgradeAt 3) semD pReuse) := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** The two programs. (Lean: `moveDeinit_moveInPlaceCall_upgrades_incomparable`)

**Non-claims.** Listed under `## Boundaries` (card `moveDeinit-moveInPlaceCall-incomparable`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/unsafe-code-guidelines#188, "What about: use-after-move and (maybe) use-after-drop" (open issue; mentioned in prose, not a subject, not normative).

**Design question.** Can an optimizer be agnostic between the two readings of `move`? An upgrade satisfying both sets of conditions is sound under both (each by its own theorem); no weaker semantics-agnostic condition is proved.

#### `observation-certificate-checker-and-least-solution` (characterization)

**Plain claim.** The Boolean checker `checkObs` accepts a mask exactly when it satisfies the gen/transfer certificate conditions over the body and the destructor block (gen: by-name reads, any `load` if the local is address-taken, and the same inside called callees; kill: storage statements and whole-local assignments), and the backward scan `obsAnalysis` is such a certificate and is below every certificate at every tick up to the end and every local of the program.

**Tier.** T0 — Standard backward may-analysis and certificate checking restated for this language; the claimed-and-checked certificate pattern is the one of the published address-free package (card `liveness-checker-characterization-and-soundness`), cited, not re-proved.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:124-124
theorem checkObs_eq_true_iff (P : Prog) (O : ObsMask) : checkObs P O = true ↔ ObsCert P O := by …
```

```lean
-- lean/ToyCoalesce/ObsAnalysis.lean:153-156
theorem obsAnalysis_least_cert (P : Prog) :
    ObsCert P (obsAnalysis P) ∧
    ∀ O, ObsCert P O → ∀ t, t ≤ P.code.length → ∀ u, u < P.nloc →
      obsAnalysis P t u = true → O t u = true := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** `pDtor` with `obsAnalysis pDtor` (`ex_obsCert_pos`). (Lean: `ex_obsCert_pos`)

**Non-claims.** Listed under `## Boundaries` (card `observation-certificate-checker-and-least-solution`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): card `liveness-checker-characterization-and-soundness` (`checkLive_eq_true_iff`, Liveness.lean:107; `checkLive_sound`, Liveness.lean:112): the claimed-and-checked certificate pattern reused here.
* G. A. Kildall, "A Unified Approach to Global Program Optimization", POPL 1973, pp. 194-206, doi:10.1145/512927.512945: the lattice framework for data-flow analysis; the least-solution part of `obsAnalysis_least_cert` is its straight-line instance (bibliographic data verified; full text not inspected).
* S. Rideau, X. Leroy, "Validating Register Allocation and Spilling", CC 2010, LNCS 6011, pp. 224-243, doi:10.1007/978-3-642-11970-5_13, implemented in AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc backend/Allocation.v (line 13: "Register allocation by external oracle and a posteriori validation."; lines 22-25 cite this paper): a posteriori validation of an untrusted allocation result, the same claimed-and-checked pattern as the certificate here; not formalized here.

**Design question.** Can the return-tail analysis be checked rather than trusted? Yes, as a certificate.

#### `observation-certificate-licenses-upgrades` (theorem)

**Plain claim.** If a mask `O` satisfies the certificate conditions and `q.base ∉ O (k+1)`, then on every layout and under every semantics no cell of `q` is read at a tick after `k` before it is written or reset; and, for an upgrade site `k` of `q`, a certificate that licenses the upgrade under the chosen `move` semantics (`Licensed`: always for `MoveSem.asCopy`; `q.base ∉ O (k+1)` plus a callee summary with no possible read of `q.base` for `MoveSem.deinit`; for `MoveSem.inPlaceCall`, always for non-call sites and, for call sites, `q.base ∉ O (k+1)`, a callee that does not read or assign a place based at `q.base` by name nor store through a pointer held in one, does no `load` and no `store` if `q.base` is address-taken, and whose parameter local is not address-taken anywhere in `P`) makes the upgrade a refinement, under either assignment order.

**Tier.** T1 — Soundness of a conservative backward analysis that includes destructor bodies and callee summaries, connected to the three `move` semantics.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfObs.lean:2330-2332
theorem noReadBeforeReinit_of_obsCert (sem : Sem) (P : Prog) (O : ObsMask) (hcert : ObsCert P O)
    (k : Nat) (q : Place) (hO : O (k + 1) q.base = false) (A : Layout) :
    NoReadBeforeReinit (run sem P A).log k false q := by …
```

```lean
-- lean/ToyCoalesce/PfLicensed.lean:624-627
theorem upgrade_refines_of_obsCert_licensed (sem : Sem) (P : Prog) (O : ObsMask) (k : Nat)
    (q : Place) (hsite : UpgradeSite P k q) (hcert : ObsCert P O)
    (hlic : Licensed sem.move P O k q) :
    Refines sem (P.upgradeAt k) sem P := by …
```

**Hypothesis ledger.**

* `hcert` — the mask must be a certificate, not just claimed — **tight**: cex_noRead_needs_obsCert; cex_licensed_needs_obsCert (witness class: the all-false mask on two small programs)
* `hO` — the local must be absent from the mask after the use — **tight**: cex_noRead_needs_not_in_mask (witness class: pReuse with its computed certificate)
* `hlic` — licensing condition per semantics — **tight**: cex_licensed_needs_licensing (witness class: pDtor with its computed certificate, `MoveSem.deinit`)
* `hsite` — the statement is an upgrade site — **unknown**

**Depth.** substantive

**Non-vacuity witness.** `pNoDtor` with `obsAnalysis pNoDtor`, site 5, `MoveSem.deinit`; `pIPOk` with `obsAnalysis pIPOk`, call site 4, `MoveSem.inPlaceCall`. (Lean: `nonvacuous_upgrade_refines_of_obsCert_licensed`, `nonvacuous_upgrade_refines_of_obsCert_licensed_inPlaceCall`)

**Non-claims.** Listed under `## Boundaries` (card `observation-certificate-licenses-upgrades`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): card `liveness-checker-characterization-and-soundness` (`checkLive_eq_true_iff`, Liveness.lean:107; `checkLive_sound`, Liveness.lean:112): the claimed-and-checked certificate pattern reused here.
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.
* S. Rideau, X. Leroy, "Validating Register Allocation and Spilling", CC 2010, LNCS 6011, pp. 224-243, doi:10.1007/978-3-642-11970-5_13, implemented in AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc backend/Allocation.v (line 13: "Register allocation by external oracle and a posteriori validation."; lines 22-25 cite this paper): a posteriori validation of an untrusted allocation result, the same claimed-and-checked pattern as the certificate here; not formalized here.

**Design question.** Which static analysis licenses copy-to-move upgrades of address-taken slots, including destructor and callee reads?

#### `destructor-blind-analysis-admits-unsound-upgrade` (counterexample)

**Plain claim.** A version of the analysis that checks the certificate conditions over the body and not over the destructor block produces, for `pDtor`, a mask that licenses the `MoveSem.deinit` upgrade at body index 5, which is not a refinement under atomic assignments (`semD`); the full analysis of `pDtor` is accepted by `checkObs` (hence is a certificate, `ex_obsCert_pos`) and does not license it (positive control).

**Tier.** T1 — Shows, in the toy under `MoveSem.deinit`, that the analysis is unsound when its return tail omits the destructor block.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:191-193
theorem cex_obsCertBodyOnly_licenses_dtorLoad :
    ObsCertBodyOnly pDtor (obsBodyOnly pDtor) ∧ Licensed .deinit pDtor (obsBodyOnly pDtor) 5 qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := by …
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:200-201
theorem obsAnalysis_rejects_dtorLoad :
    checkObs pDtor (obsAnalysis pDtor) = true ∧ ¬ Licensed .deinit pDtor (obsAnalysis pDtor) 5 qx := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** `pDtor`. (Lean: `cex_obsCertBodyOnly_licenses_dtorLoad`, `ex_obsCert_pos`)

**Positive control.** `obsAnalysis_rejects_dtorLoad` (quoted above).

**Non-claims.** Listed under `## Boundaries` (card `destructor-blind-analysis-admits-unsound-upgrade`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:1289-1293 and :1295-1303 (`Operand::Move`: may overwrite the place with `uninit`; in-place passing of `Call` arguments; operational impact unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.

**Design question.** Must the return-tail analysis include destructor bodies? Yes (in the toy, under `MoveSem.deinit`).

#### `single-merge-into-field-sufficient` (theorem)

**Plain claim.** Under atomic assignments and every `move` semantics, for the single merge of local `x` into the field window at offset `f` of local `y`: if the forest is well formed (`ForestWF`, including that every top-level call names an existing callee), `NoValueClobberStmt` holds (no read in the source run observes a clobber in the merged memory; checked on the atomic-assignment access log of every non-UB, non-excluded run), and, if `x` and `y` are both address-taken, they are never lexically allocated during a common tick, then the coalesced program refines the source.

**Tier.** T2 — Generalizes the address-free no-clobber criterion to subplace merges of address-taken locals, with the address condition stated two-sidedly; a specialization of the forest theorem.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfCompose.lean:16-20
theorem coalesce_single_refines_of_noValueClobber_of_lexDisjoint_addrTaken (ms : MoveSem)
    (P : Prog) (x y f : Nat) (hwf : ForestWF P (single x y f))
    (hi : NoValueClobberStmt ms (single x y f) P)
    (hii : AddrTaken P x → AddrTaken P y → ¬ LexOverlap P x y) :
    Refines ⟨ms, .atomic⟩ (coalesce (single x y f) P) ⟨ms, .atomic⟩ P := …
```

**Hypothesis ledger.**

* `hwf` — well-formed forest (fits, acyclic, parameters not merged, calls in bounds) — **tight**: cex_coalesce_needs_forestWF (witness class: a two-cell local merged into a one-cell local); cex_coalesce_needs_callsInBounds (witness class: a call to an absent callee)
* `hi` — the value-level condition `NoValueClobberStmt` — **tight**: cex_coalesce_single_valueClobber (witness class: two locals, no address-taken local)
* `hii` — the lexical address condition, two-sided form — **tight**: cex_coalesce_single_addrTaken_lexOverlap (witness class: two locals, `ptrInRange(&x, &y, 2)`)

**Depth.** shallow

**Non-vacuity witness.** `p3x` with the merge `x ↦ y.0` (`x` address-taken, `y` not). (Lean: `nonvacuous_coalesce_single`)

**Non-claims.** Listed under `## Boundaries` (card `single-merge-into-field-sufficient`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): `compact_silentBisim_of_noClobber` (lean/ToySlotCompact/Bisim.lean:74-77) and `compact_lockstepBisim_of_noClobber` (Bisim.lean:209), card `compact-bisim-no-clobber`: value-level soundness of merging slots with disjoint liveness in an address-free language. Cited as the address-free baseline; not re-proved and not applied (the languages differ).
* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): cards `merging-simultaneously-live-slots-breaks-compaction` (`cex_bisim_noClobber_noAssignClobber`, Counterexamples.lean:34) and `marker-reset-breaks-slot-sharing` (`cex_bisim_noClobber_noMarkerClobber`, Counterexamples.lean:40): the address-free baseline counterexamples.
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:370-381 (`StorageLive`/`StorageDead`: allocate/deallocate; using an unallocated local is UB; locals without storage statements are allocated for the whole function; re-`StorageLive` frees and reallocates). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis, "A Formal C Memory Model Supporting Integer-Pointer Casts", PLDI 2015, doi:10.1145/2737924.2738005: memory models in which allocations have identities and pointer values can be observed as concrete addresses. Bibliographic data verified by search; full text not inspected; the toy model does not reproduce its definitions.
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.
* S. Blazy, B. Robillard, A. W. Appel, "Formal Verification of Coalescing Graph-Coloring Register Allocation", ESOP 2010, LNCS 6012, pp. 145-164, doi:10.1007/978-3-642-11957-6_9: mechanized coalescing for register allocation in an address-free setting (bibliographic data verified; full text not inspected).
* X. Leroy, S. Blazy, "Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations", Journal of Automated Reasoning 41(1):1-31, 2008, doi:10.1007/s10817-008-9099-0: block-and-offset memory, of which the per-local cell memory with per-local pointer provenance here is a small instance (bibliographic data verified; full text not inspected).
* K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell, "Exploring C Semantics and Pointer Provenance", Proc. ACM Program. Lang. 3(POPL), Article 67, 2019, doi:10.1145/3290380: pointer provenance and address exposure in a C memory object model; cited for the distinction between provenance and observed addresses that this toy's per-local provenance and observable absolute addresses also draw (bibliographic data verified; full text not inspected; no formal relation is stated).

**Design question.** When may a local be merged into a subplace of another local once addresses can be observed?

#### `address-taken-merge-overlap-breaks-refinement` (counterexample)

**Plain claim.** Under atomic assignments and every `move` semantics: in `p3` (x and y allocated together; `y.1 := 5; x := 7; out x; y.0 := 9; ptrInRange(&x, &y, 2); out y`) the merge `x ↦ y.0` is well formed and satisfies `NoValueClobberStmt` but not the lexical address condition (both are address-taken and allocated together); the source comparison is `false` on every non-excluded layout (`p3_outcome`) and the coalesced one is `true` on `A0`, so it is not a refinement; in `pClobber` (no address-taken local) a value clobber breaks the same merge; in `p3x` an address-taken `x` merged into a non-address-taken `y` allocated at the same time, with `NoValueClobberStmt`, is a refinement.

**Tier.** T1 — The pointer-comparison observation of a merged address, kernel-checked, with its positive control. Paired with `single-merge-into-field-sufficient` (tightness witnesses of `hi`, `hii`) and its one-sided-condition remark.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexMerge.lean:85-90
theorem cex_coalesce_single_addrTaken_lexOverlap (ms : MoveSem) :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3 ∧
    AddrTaken p3 0 ∧ AddrTaken p3 1 ∧ LexOverlap p3 0 1 ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 0 1 0) p3) A0 =
      .done [.vals [.int 7], .cmp true, .vals [.int 9, .int 5]] ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) p3) ⟨ms, .atomic⟩ p3 := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:116-121
theorem cex_coalesce_single_valueClobber (ms : MoveSem) :
    ForestWF pClobber (single 0 1 0) ∧
    (AddrTaken pClobber 0 → AddrTaken pClobber 1 → ¬ LexOverlap pClobber 0 1) ∧
    ClassAddrDisjoint pClobber (single 0 1 0) ∧
    ¬ NoValueClobberStmt ms (single 0 1 0) pClobber ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) pClobber) ⟨ms, .atomic⟩ pClobber := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:100-103
theorem coalesce_single_refines_addrTaken_child_only (ms : MoveSem) :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3x ∧
    AddrTaken p3x 0 ∧ ¬ AddrTaken p3x 1 ∧ LexOverlap p3x 0 1 ∧
    Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) p3x) ⟨ms, .atomic⟩ p3x := by …
```

Supporting outcome lemma (cited in the plain claim; not a main result of the card):

```lean
-- lean/ToyCoalesce/CexMerge.lean:40-42
theorem p3_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ p3 A = .done [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]] ∨
      outcome ⟨ms, .atomic⟩ p3 A = .badLayout := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** The programs `p3`, `pClobber`, `p3x`. (Lean: `cex_coalesce_single_addrTaken_lexOverlap`)

**Positive control.** `coalesce_single_refines_addrTaken_child_only` (quoted above).

**Non-claims.** Listed under `## Boundaries` (card `address-taken-merge-overlap-breaks-refinement`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): cards `merging-simultaneously-live-slots-breaks-compaction` (`cex_bisim_noClobber_noAssignClobber`, Counterexamples.lean:34) and `marker-reset-breaks-slot-sharing` (`cex_bisim_noClobber_noMarkerClobber`, Counterexamples.lean:40): the address-free baseline counterexamples.
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis, "A Formal C Memory Model Supporting Integer-Pointer Casts", PLDI 2015, doi:10.1145/2737924.2738005: memory models in which allocations have identities and pointer values can be observed as concrete addresses. Bibliographic data verified by search; full text not inspected; the toy model does not reproduce its definitions.

**Design question.** Which address condition is needed for merging address-taken locals?

#### `forest-coalescing-root-level-check-sufficient` (theorem)

**Plain claim.** Under atomic assignments and every `move` semantics, for a well-formed merge forest (`ForestWF`, including that every top-level call names an existing callee): `NoValueClobberStmt` together with the root-level check `ClassAddrDisjoint` (any two distinct address-taken locals of the same class whose root-relative windows intersect are never lexically allocated during a common tick) gives a refinement; the window-insensitive check `ClassAddrDisjointW` (all pairs of distinct address-taken class members) implies `ClassAddrDisjoint`.

**Tier.** T2 — Transitive (forest) merges into subplaces with a root-relative address check; not found mechanized.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfCoalesce.lean:2655-2658
theorem coalesce_refines_of_noValueClobber_of_classAddrDisjoint (ms : MoveSem) (P : Prog)
    (μ : Forest) (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P)
    (hii : ClassAddrDisjoint P μ) :
    Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P := by …
```

```lean
-- lean/ToyCoalesce/Merge.lean:329-330
theorem classAddrDisjoint_of_classAddrDisjointW (P : Prog) (μ : Forest)
    (h : ClassAddrDisjointW P μ) : ClassAddrDisjoint P μ := …
```

**Hypothesis ledger.**

* `hwf` — well-formed forest (fits, acyclic, parameters not merged, calls in bounds) — **tight**: cex_coalesce_needs_forestWF (witness class: a one-edge forest that does not fit); cex_coalesce_needs_callsInBounds (witness class: a call to an absent callee)
* `hi` — the value-level condition `NoValueClobberStmt` for the whole forest — **tight**: cex_coalesce_single_valueClobber (witness class: a one-edge forest)
* `hii` — root-level address check — **tight**: cex_edgeAddrCheck_does_not_compose; cex_rootAddrCheck_insufficient_siblings; cex_coalesce_single_addrTaken_lexOverlap (witness classes: two- and three-local programs)
* `h` — the window-insensitive check `ClassAddrDisjointW` (hypothesis of `classAddrDisjoint_of_classAddrDisjointW`) — **tight**: cex_classAddrDisjoint_of_classAddrDisjointW_needs_h (witness class: the one-edge forest `single 0 1 0` of `p3`, for which `ClassAddrDisjoint` fails)

**Depth.** substantive

**Non-vacuity witness.** `pChainOk` with the forest `x ↦ y.1`, `y ↦ z.1` (`μChain`), for both theorems: all hypotheses of the forest theorem hold, and `ClassAddrDisjointW pChainOk μChain` holds. (Lean: `nonvacuous_coalesce_refines_of_noValueClobber_of_classAddrDisjoint`, `nonvacuous_classAddrDisjoint_of_classAddrDisjointW`, `nonvacuous_ufCheck`)

**Non-claims.** Listed under `## Boundaries` (card `forest-coalescing-root-level-check-sufficient`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): `compact_silentBisim_of_noClobber` (lean/ToySlotCompact/Bisim.lean:74-77) and `compact_lockstepBisim_of_noClobber` (Bisim.lean:209), card `compact-bisim-no-clobber`: value-level soundness of merging slots with disjoint liveness in an address-free language. Cited as the address-free baseline; not re-proved and not applied (the languages differ).
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* G. J. Chaitin, "Register allocation & spilling via graph coloring", SIGPLAN '82 Symposium on Compiler Construction, doi:10.1145/800230.806984; L. George and A. W. Appel, "Iterated register coalescing", TOPLAS 18(3), 1996, doi:10.1145/229542.229546: interference-based coalescing (the address-free analogue). Bibliographic data verified by search; full texts not inspected here. A textbook section number for Appel's Modern Compiler Implementation could not be verified at the source and is not cited.
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.
* S. Rideau, X. Leroy, "Validating Register Allocation and Spilling", CC 2010, LNCS 6011, pp. 224-243, doi:10.1007/978-3-642-11970-5_13, implemented in AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc backend/Allocation.v (line 13: "Register allocation by external oracle and a posteriori validation."; lines 22-25 cite this paper): a posteriori validation of an untrusted allocation result, cited as related verified-compiler work that validates a slot and register assignment a posteriori; not formalized here, and no formal comparison is made.
* S. Blazy, B. Robillard, A. W. Appel, "Formal Verification of Coalescing Graph-Coloring Register Allocation", ESOP 2010, LNCS 6012, pp. 145-164, doi:10.1007/978-3-642-11957-6_9: mechanized coalescing for register allocation in an address-free setting (bibliographic data verified; full text not inspected).
* K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell, "Exploring C Semantics and Pointer Provenance", Proc. ACM Program. Lang. 3(POPL), Article 67, 2019, doi:10.1145/3290380: pointer provenance and address exposure in a C memory object model; cited for the distinction between provenance and observed addresses that this toy's per-local provenance and observable absolute addresses also draw (bibliographic data verified; full text not inspected; no formal relation is stated).

**Design question.** Do pairwise-valid merges compose, and what check suffices for merge forests?

#### `pairwise-merge-checks-do-not-compose` (counterexample)

**Plain claim.** Under atomic assignments and every `move` semantics: in `pChain`, the merges `x ↦ y.1` and `y ↦ z.1`, checked independently against the original program, each satisfy `NoValueClobberStmt` as single merges and the per-edge address check, and the forest satisfies `NoValueClobberStmt` and the per-edge check; but `x` and its final root `z` are address-taken and allocated together, and the composite coalescing is not a refinement; in `pSib`, the sibling merges `x1 ↦ y.0`, `x2 ↦ y.0` pass the per-edge and the member-versus-root checks and `NoValueClobberStmt`, but the siblings are address-taken and allocated together, and the coalescing is not a refinement.

**Tier.** T1 — Refutes, in the address-taken setting, the folklore that merge edges validated independently against the original program can be combined into one forest.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexMerge.lean:135-139
theorem cex_edgeAddrCheck_does_not_compose (ms : MoveSem) :
    ForestWF pChain μChain ∧ NoValueClobberStmt ms μChain pChain ∧
    NoValueClobberStmt ms (single 0 1 1) pChain ∧ NoValueClobberStmt ms (single 1 2 1) pChain ∧
    EdgeAddrCheck pChain μChain ∧ ¬ ClassAddrDisjoint pChain μChain ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce μChain pChain) ⟨ms, .atomic⟩ pChain := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:156-159
theorem cex_rootAddrCheck_insufficient_siblings (ms : MoveSem) :
    ForestWF pSib μSib ∧ NoValueClobberStmt ms μSib pSib ∧ EdgeAddrCheck pSib μSib ∧
    RootAddrCheck pSib μSib ∧ ¬ ClassAddrDisjoint pSib μSib ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce μSib pSib) ⟨ms, .atomic⟩ pSib := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** The programs `pChain`, `pSib`. (Lean: `cex_edgeAddrCheck_does_not_compose`)

**Non-claims.** Listed under `## Boundaries` (card `pairwise-merge-checks-do-not-compose`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* G. J. Chaitin, "Register allocation & spilling via graph coloring", SIGPLAN '82 Symposium on Compiler Construction, doi:10.1145/800230.806984; L. George and A. W. Appel, "Iterated register coalescing", TOPLAS 18(3), 1996, doi:10.1145/229542.229546: interference-based coalescing (the address-free analogue). Bibliographic data verified by search; full texts not inspected here. A textbook section number for Appel's Modern Compiler Implementation could not be verified at the source and is not cited.

**Design question.** Does the root-level check need information beyond each member versus its root? Yes: pairs of members.

#### `union-find-interval-union-decides-root-check` (characterization)

**Plain claim.** For a well-formed forest, the disjoint-set pass `ufCheck` (each block keeps the union of the lexical tick sets of its address-taken members; merging two blocks is rejected if their unions intersect or they are already one block) accepts iff the window-insensitive root-level check `ClassAddrDisjointW` holds.

**Tier.** T0 — Standard disjoint-set merging with summarised interval unions (as in equivalence-class live-range coalescing), stated for this check.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfUF.lean:503-504
theorem ufCheck_eq_true_iff_classAddrDisjointW (P : Prog) (μ : Forest) (hwf : ForestWF P μ) :
    ufCheck P μ = true ↔ ClassAddrDisjointW P μ := by …
```

**Hypothesis ledger.**

* `hwf` — well-formed forest (classes by root agree with classes by edges; no cycles) — **tight**: cex_ufCheck_needs_forestWF (witness class: a two-cycle forest over a two-local program)

**Depth.** substantive

**Non-vacuity witness.** `pChainOk` / `μChain`: the forest is well formed, `ufCheck` accepts and `ClassAddrDisjointW` holds. (Lean: `nonvacuous_ufCheck`)

**Non-claims.** Listed under `## Boundaries` (card `union-find-interval-union-decides-root-check`); read them before relying on this card.

**Prior art.**

* G. J. Chaitin, "Register allocation & spilling via graph coloring", SIGPLAN '82 Symposium on Compiler Construction, doi:10.1145/800230.806984; L. George and A. W. Appel, "Iterated register coalescing", TOPLAS 18(3), 1996, doi:10.1145/229542.229546: interference-based coalescing (the address-free analogue). Bibliographic data verified by search; full texts not inspected here. A textbook section number for Appel's Modern Compiler Implementation could not be verified at the source and is not cited.
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.
* Z. Budimlić, K. D. Cooper, T. J. Harvey, K. Kennedy, T. S. Oberg, S. W. Reeves, "Fast Copy Coalescing and Live-Range Identification", PLDI 2002, pp. 25-32, doi:10.1145/512529.512534: copy coalescing over equivalence classes of live ranges (bibliographic data verified; full text not inspected).
* B. Boissinot, A. Darte, F. Rastello, B. Dupont de Dinechin, C. Guillon, "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency", CGO 2009, pp. 114-125, doi:10.1109/CGO.2009.19: congruence-class coalescing and parallel-copy sequentialization (bibliographic data verified; full text not inspected).

**Design question.** Can the root-level check be decided incrementally from per-class summaries? Yes, with interval unions.

#### `lifetime-policy-soundness-iff-lexical-for-address-taken` (characterization)

**Plain claim.** For a uniform interference policy that assigns one of the two lifetime notions of `Notion` (lexical storage liveness, or precise by-name liveness: the hull of by-name access points at half-statement granularity, where a call marks both halves for every local its callee body touches by name) to address-taken locals and one to the other locals, and checks that distinct class members with intersecting root-relative windows have non-overlapping intervals: the policy is sound (every forest satisfying `ForestWF`, including that calls name existing callees, that passes the check yields a refinement, under atomic assignments and every `move` semantics) iff it uses lexical intervals for address-taken locals; a policy that uses precise intervals for address-taken locals is not sound, whatever it uses for the other locals; precise liveness for the other locals is allowed.

**Tier.** T2 — Which lifetime notion an interference check must use, by address observation; both directions are proved.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfPolicy.lean:1158-1159
theorem policySound_of_lexical_for_addrTaken (pol : Policy) (h : pol true = .lexical) :
    PolicySound pol := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:202-203
theorem not_policySound_of_precise_for_addrTaken (pol : Policy) (h : pol true = .precise) :
    ¬ PolicySound pol := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:221-221
theorem policySound_iff (pol : Policy) : PolicySound pol ↔ pol true = .lexical := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:193-196
theorem cex_policy_precise_for_addrTaken (ms : MoveSem) :
    ForestWF pPrecise (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pPrecise ∧
    PolicyCheck (fun _ => .precise) pPrecise (single 1 0 0) ∧ LexOverlap pPrecise 0 1 ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pPrecise) ⟨ms, .atomic⟩ pPrecise := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:232-236
theorem policy_mixed_accepts_pPreciseOk (ms : MoveSem) :
    ForestWF pPreciseOk (single 1 0 0) ∧
    PolicyCheck (fun b => if b then .lexical else .precise) pPreciseOk (single 1 0 0) ∧
    ¬ PolicyCheck (fun _ => .lexical) pPreciseOk (single 1 0 0) ∧
    Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pPreciseOk) ⟨ms, .atomic⟩ pPreciseOk := by …
```

**Hypothesis ledger.**

* `h (sufficiency)` — lexical intervals for address-taken locals — **tight**: not_policySound_of_precise_for_addrTaken / cex_policy_precise_for_addrTaken (witness class: two address-taken locals, precisely disjoint, lexically overlapping)
* `h (necessity form)` — precise intervals for address-taken locals (the hypothesis of `not_policySound_of_precise_for_addrTaken`) — **tight**: cex_not_policySound_of_precise_needs_h (witness class: the mixed policy, lexical intervals for address-taken locals and precise intervals for the others, which does not satisfy `h` and is sound)

**Depth.** substantive

**Non-vacuity witness.** For `policySound_of_lexical_for_addrTaken`: the mixed policy on `pPreciseOk` (accepted, refinement holds). For `not_policySound_of_precise_for_addrTaken`: the precise-everywhere policy, which satisfies `pol true = .precise`. (Lean: `policy_mixed_accepts_pPreciseOk`, `nonvacuous_not_policySound_of_precise_for_addrTaken`)

**Positive control.** `policy_mixed_accepts_pPreciseOk` (quoted above).

**Non-claims.** Listed under `## Boundaries` (card `lifetime-policy-soundness-iff-lexical-for-address-taken`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:370-381 (`StorageLive`/`StorageDead`: allocate/deallocate; using an unallocated local is UB; locals without storage statements are allocated for the whole function; re-`StorageLive` frees and reallocates). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.

**Design question.** Which allocation-lifetime notion must a coalescer use for address-taken locals?

#### `overlap-staging-behavioural-equivalence` (theorem)

**Plain claim.** Under every `move` semantics: if no assignment of a program needs staging (top-level: two or more operands, one of which is a load or reads a place intersecting the left side; in a callee: the same, where in addition a place based at the callee parameter and one not based at it count as possibly overlapping), in-order and atomic assignment give the same outcome on every layout; staging (each such top-level assignment of the body and destructors becomes `storageLive tmp; tmp := rhs; lhs := [move tmp]; storageDead tmp` with a fresh `tmp`) under in-order writes refines the unstaged program under atomic assignment when no callee assignment needs staging and every callee parameter local exists, and the behaviour sets are equal (`BehEq`) when no callee assignment needs staging and every local the program mentions exists.

**Tier.** T1 — Staging through a fresh temporary as a semantics bridge between in-order and atomic aggregate assignment.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfStage.lean:2875-2877
theorem outcome_inOrder_eq_atomic_of_noStagingNeeded (ms : MoveSem) (P : Prog)
    (h : NoStagingNeeded P) (A : Layout) :
    outcome ⟨ms, .inOrder⟩ P A = outcome ⟨ms, .atomic⟩ P A := by …
```

```lean
-- lean/ToyCoalesce/PfStage.lean:2884-2886
theorem stage_inOrder_refines_atomic (ms : MoveSem) (Q : Prog) (hc : CalleesNoStaging Q)
    (hp : ParamsInRange Q) :
    Refines ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := by …
```

```lean
-- lean/ToyCoalesce/PfStage.lean:2902-2904
theorem stage_inOrder_behEq_atomic_of_localsInRange (ms : MoveSem) (Q : Prog)
    (hc : CalleesNoStaging Q) (hl : LocalsInRange Q) :
    BehEq ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := by …
```

**Hypothesis ledger.**

* `h (no staging needed)` — no overlapping aggregate, including in-place aliasing inside callees — **tight**: cex_inOrder_eq_atomic_needs_noStaging (witness class: the coalesced swap program)
* `hc` — callee bodies are not staged — **tight**: cex_stage_needs_calleesNoStaging (witness class: a callee swapping its parameter; both forms)
* `hp (refinement form)` — the fresh temporaries do not take the index of a callee parameter local — **tight**: cex_stage_refines_needs_paramsInRange (witness class: a one-local program whose callee parameter does not exist, `MoveSem.inPlaceCall`)
* `hl (equality form)` — the fresh temporaries are not mentioned by the program — **tight**: cex_stage_behEq_needs_localsInRange (witness class: coalesced swap plus uses of local 2)

**Depth.** substantive

**Non-vacuity witness.** `pSwap` (needs no staging) and the coalesced `pSwap` (needs staging; no callee assignment needs staging; parameters and mentioned locals exist). (Lean: `nonvacuous_staging`)

**Non-claims.** Listed under `## Boundaries` (card `overlap-staging-behavioural-equivalence`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:328-333 (`StatementKind::Assign`: LHS must not overlap places read by the RHS for some rvalues; under discussion; evaluation order of components unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/rust#68364, "Semantics of MIR assignments, around aliasing, ordering, and primitives." (open issue; mentioned in prose, not a subject, not normative).
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.
* L. Rideau, B. P. Serpette, X. Leroy, "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves", Journal of Automated Reasoning 40(4):307-326, 2008, doi:10.1007/s10817-007-9096-8: Coq-verified sequentialization of parallel moves, using a temporary to break cycles such as swaps; compared in prose with staging (staging here sequentializes one aggregate assignment through a fresh local), not formalized here.
* P. Briggs, K. D. Cooper, T. J. Harvey, L. T. Simpson, "Practical Improvements to the Construction and Destruction of Static Single Assignment Form", Software: Practice and Experience 28(8):859-881, 1998, doi:10.1002/(SICI)1097-024X(19980710)28:8<859::AID-SPE188>3.0.CO;2-8: the swap problem when sequentializing copies (bibliographic data verified; full text not inspected).
* B. Boissinot, A. Darte, F. Rastello, B. Dupont de Dinechin, C. Guillon, "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency", CGO 2009, pp. 114-125, doi:10.1109/CGO.2009.19: congruence-class coalescing and parallel-copy sequentialization (bibliographic data verified; full text not inspected).

**Design question.** What fixup makes overlapping assignments created by coalescing safe under in-order field writes, and what must the overlap check consider inside callees?

#### `coalesce-then-stage-pipeline` (theorem)

**Plain claim.** Under in-order field writes and every `move` semantics, for a well-formed forest (`ForestWF`) with `NoValueClobberStmt` and the root-level address check `ClassAddrDisjoint`: if no assignment of the source needs staging, no callee assignment of the coalesced program needs staging, and every callee parameter local exists, the staged coalesced program refines the source; and if no assignment of the coalesced program needs staging (a coalescer that respects the no-overlap constraint), the unstaged coalesced program refines the source.

**Tier.** T1 — A composition (by `Refines.trans`) of the forest theorem with the staging theorems; recorded because the hypotheses of the composite (in particular the callee and parameter conditions) are not obvious.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfCompose.lean:28-31
theorem stage_coalesce_refines_inOrder (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hii : ClassAddrDisjoint P μ)
    (hns : NoStagingNeeded P) (hc : CalleesNoStaging (coalesce μ P)) (hp : ParamsInRange P) :
    Refines ⟨ms, .inOrder⟩ (stage (coalesce μ P)) ⟨ms, .inOrder⟩ P := …
```

```lean
-- lean/ToyCoalesce/PfCompose.lean:39-42
theorem coalesce_refines_inOrder_of_noStagingNeeded (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hii : ClassAddrDisjoint P μ)
    (hnc : NoStagingNeeded (coalesce μ P)) :
    Refines ⟨ms, .inOrder⟩ (coalesce μ P) ⟨ms, .inOrder⟩ P := …
```

**Hypothesis ledger.**

* `hwf` — well-formed forest — **tight**: cex_coalesce_needs_callsInBounds (witness class: a call to an absent callee; both forms)
* `hi` — the value-level condition `NoValueClobberStmt` — **tight**: cex_pipeline_needs_noValueClobber (witness class: two locals, no address-taken local; both forms)
* `hii` — root-level address check — **tight**: cex_pipeline_needs_classAddrDisjoint (witness class: two locals, `ptrInRange(&x, &y, 2)`; both forms)
* `hns (staged form)` — the source needs no staging — **tight**: cex_pipeline_needs_noStagingNeeded (witness class: one two-cell local, empty forest)
* `hc (staged form)` — callee bodies of the coalesced program need no staging (they are not staged) — **tight**: cex_pipeline_needs_calleesNoStaging (witness class: a merge that creates an overlapping callee assignment)
* `hp (staged form)` — staging temporaries do not take the index of a callee parameter local — **tight**: cex_pipeline_needs_paramsInRange (witness class: the swap program plus an in-place call to a callee whose parameter does not exist, `MoveSem.inPlaceCall`)
* `hnc (no-overlap coalescer form)` — the coalesced program needs no staging — **tight**: cex_coalesce_without_staging_inOrder (witness class: the swap program)

**Depth.** shallow

**Non-vacuity witness.** `pSwap` with `y' ↦ y.0` (staged form, `stage_coalesce_pSwap`); `p3x` with `x ↦ y.0` (no-overlap form). (Lean: `stage_coalesce_pSwap`, `nonvacuous_coalesce_refines_inOrder_of_noStagingNeeded`)

**Non-claims.** Listed under `## Boundaries` (card `coalesce-then-stage-pipeline`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:328-333 (`StatementKind::Assign`: LHS must not overlap places read by the RHS for some rvalues; under discussion; evaluation order of components unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/rust#68364, "Semantics of MIR assignments, around aliasing, ordering, and primitives." (open issue; mentioned in prose, not a subject, not normative).
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.

**Design question.** How do coalescing and overlap staging compose, and what must a re-run of the coalescer respect?

#### `coalescing-creates-overlap-and-recoalescing-pitfall` (counterexample)

**Plain claim.** Under every `move` semantics: in `pSwap` (y := (1, 2); y' := (y.1, y.0); out y') the merge `y' ↦ y.0` is well formed and satisfies `NoValueClobberStmt` and the root-level address check, and the source needs no staging, but the coalesced program contains `y := (y.1, y.0)` (`coalesce_pSwap_contains_overlap`), prints `(2, 2)` on every non-excluded layout under in-order field writes (`coalesce_pSwap_outcome_inOrder`) and is not a refinement there (it is one under atomic assignment, and its staged version is one under in-order writes); re-running the coalescer on the staged program with the merge of the staging temporary into `y` satisfies the same conditions but again contains an assignment that needs staging and is not a refinement under in-order writes.

**Tier.** T1 — Refutes "coalescing never creates overlapping assignments" and exhibits the fixpoint pitfall.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexMerge.lean:248-253
theorem cex_coalesce_without_staging_inOrder (ms : MoveSem) :
    ForestWF pSwap (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pSwap ∧
    ClassAddrDisjoint pSwap (single 1 0 0) ∧ NoStagingNeeded pSwap ∧
    ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) ∧
    ¬ Refines ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pSwap) ⟨ms, .inOrder⟩ pSwap ∧
    Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSwap) ⟨ms, .atomic⟩ pSwap := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:285-289
theorem cex_recoalesce_staging_temp (ms : MoveSem) :
    ForestWF pSwapStaged (single 2 0 0) ∧ NoValueClobberStmt ms (single 2 0 0) pSwapStaged ∧
    ClassAddrDisjoint pSwapStaged (single 2 0 0) ∧ NoStagingNeeded pSwapStaged ∧
    ¬ NoStagingNeeded (coalesce (single 2 0 0) pSwapStaged) ∧
    ¬ Refines ⟨ms, .inOrder⟩ (coalesce (single 2 0 0) pSwapStaged) ⟨ms, .inOrder⟩ pSwapStaged := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:262-266
theorem stage_coalesce_pSwap (ms : MoveSem) :
    ForestWF pSwap (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pSwap ∧
    ClassAddrDisjoint pSwap (single 1 0 0) ∧ NoStagingNeeded pSwap ∧
    CalleesNoStaging (coalesce (single 1 0 0) pSwap) ∧ ParamsInRange pSwap ∧
    Refines ⟨ms, .inOrder⟩ (stage (coalesce (single 1 0 0) pSwap)) ⟨ms, .inOrder⟩ pSwap := by …
```

Supporting lemmas (cited in the plain claim; not main results of the card):

```lean
-- lean/ToyCoalesce/CexSupport.lean:46-48
theorem coalesce_pSwap_contains_overlap :
    Stmt.assign ⟨0, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩] ∈
      (coalesce (single 1 0 0) pSwap).body := by …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:53-55
theorem coalesce_pSwap_outcome_inOrder (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A = .done [.vals [.int 2, .int 2]] ∨
      outcome ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A = .badLayout := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** `pSwap` and `pSwapStaged`. (Lean: `cex_coalesce_without_staging_inOrder`)

**Positive control.** `stage_coalesce_pSwap` (quoted above).

**Non-claims.** Listed under `## Boundaries` (card `coalescing-creates-overlap-and-recoalescing-pitfall`); read them before relying on this card.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:328-333 (`StatementKind::Assign`: LHS must not overlap places read by the RHS for some rvalues; under discussion; evaluation order of components unclear). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* rust-lang/rust#68364, "Semantics of MIR assignments, around aliasing, ordering, and primitives." (open issue; mentioned in prose, not a subject, not normative).
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/dest_prop.rs:49-57 (write-versus-liveness condition; locals with their address taken are excluded), :64-66 (disjoint live ranges at half-statement granularity), :72-75 (future work: merging storage liveness ranges instead of removing storage statements; merging into places with projections). Documentation; used in derived (modeling bridge) remarks, not as a finding.
* L. Rideau, B. P. Serpette, X. Leroy, "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves", Journal of Automated Reasoning 40(4):307-326, 2008, doi:10.1007/s10817-007-9096-8: Coq-verified sequentialization of parallel moves, using a temporary to break cycles such as swaps; compared in prose with staging (staging here sequentializes one aggregate assignment through a fresh local), not formalized here.

**Design question.** Does coalescing create overlapping assignments? Yes; and staging is not a fixpoint of coalescing.

#### `vc-transfer-address-free-and-address-mentioning` (theorem)

**Plain claim.** Under atomic assignments and every `move` semantics, for a well-formed forest (`ForestWF`) with `NoValueClobberStmt`: an address-free postcondition (one that gives the same verdict on traces that agree after erasing printed addresses and comparison results) valid for the source is valid for the coalesced program, with no address condition (in this toy addresses reach nothing but printed pointers and comparison results); it transfers back if moreover the source has no undefined behaviour; and an arbitrary postcondition valid for the source transfers forward when the root-level address check `ClassAddrDisjoint` also holds.

**Tier.** T2 — The address-free / address-mentioning split for verification-condition transfer across coalescing of address-taken locals.

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/PfCoalesce.lean:2682-2685
theorem vc_forward_addrFree_of_noValueClobber (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (Post : List Event → Prop)
    (hpost : AddrFree Post) (hv : Valid ⟨ms, .atomic⟩ P Post) :
    Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := by …
```

```lean
-- lean/ToyCoalesce/PfCoalesce.lean:2704-2708
theorem vc_backward_addrFree_of_noValueClobber_of_ubFree (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hsafe : UBFree ⟨ms, .atomic⟩ P)
    (Post : List Event → Prop) (hpost : AddrFree Post)
    (hv : Valid ⟨ms, .atomic⟩ (coalesce μ P) Post) :
    Valid ⟨ms, .atomic⟩ P Post := by …
```

```lean
-- lean/ToyCoalesce/PfCompose.lean:53-56
theorem vc_forward_of_noValueClobber_of_classAddrDisjoint (ms : MoveSem) (P : Prog) (μ : Forest)
    (hwf : ForestWF P μ) (hi : NoValueClobberStmt ms μ P) (hii : ClassAddrDisjoint P μ)
    (Post : List Event → Prop) (hv : Valid ⟨ms, .atomic⟩ P Post) :
    Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := …
```

**Hypothesis ledger.**

* `hwf (forward forms)` — well-formed forest — **tight**: cex_coalesce_needs_forestWF (witness class: a forest that does not fit); cex_coalesce_needs_callsInBounds, with its canonical form cex_vc_forward_needs_callsInBounds (witness class: a call to an absent callee)
* `hwf (backward form)` — well-formed forest — **tight**: cex_vc_backward_needs_forestWF (witness class: a three-local program whose callee parameter is merged into a caller local, under `MoveSem.inPlaceCall`)
* `hi` — the value-level condition `NoValueClobberStmt` — **tight**: cex_vc_forward_addrFree_needs_noValueClobber; cex_vc_forward_needs_noValueClobber_classAddrDisjoint (the same witness with the root-level check `ClassAddrDisjoint`, for `vc_forward_of_noValueClobber_of_classAddrDisjoint`); cex_vc_backward_needs_noValueClobber (witness class: two locals, no address-taken local)
* `hpost` — address-freedom of the postcondition — **tight**: cex_vc_forward_addrPost_needs_classAddrDisjoint (forward; witness class: `p3` with 'no comparison returned true'); cex_vc_backward_addrPost (backward; witness class: `p3` with 'some comparison returned true')
* `hsafe (backward)` — the source has no undefined behaviour — **tight**: cex_vc_backward_needs_ubFree (witness class: coalescing removes a read of an uninitialized local)
* `hii (address-mentioning forward)` — root-level address check — **tight**: cex_vc_forward_addrPost_needs_classAddrDisjoint; cex_vc_forward_addrPost_precisePolicy (witness class: two locals compared while allocated together)
* `hv` — validity on the side the condition is transferred from — **tight**: cex_vc_needs_valid (witness class: `p3x` with the unsatisfiable postcondition)

**Depth.** substantive

**Non-vacuity witness.** `p3x` with the merge `x ↦ y.0` and the address-free postcondition 'the erased trace is `[7], [address], [9, 5]`' (all hypotheses of the three theorems, including validity on both sides); `p3` (`vc_forward_addrFree_p3`, positive control where `ClassAddrDisjoint` fails). (Lean: `nonvacuous_vc_p3x`, `vc_forward_addrFree_p3`)

**Non-claims.** Listed under `## Boundaries` (card `vc-transfer-address-free-and-address-mentioning`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): `vc_transfer_of_noClobber` (lean/ToySlotCompact/WP.lean:212), `vc_forward_of_noClobber` (WP.lean:181), `vc_backward_of_noClobber` (WP.lean:196), cards `vc-transfer-original-to-compacted` / `vc-transfer-compacted-to-original`. Cited as the address-free analogue; not applied.
* Novelty search (2026-11-21; web search for mechanized results on destination propagation / move semantics / stack-slot coalescing with observable pointer comparisons): no mechanized statement of this criterion was found; the phenomena are documented informally (sources above). No T3 claim is made.

**Design question.** Which verification conditions survive coalescing of address-taken locals, and which need the address check?

#### `vc-transfer-counterexamples` (counterexample)

**Plain claim.** Under atomic assignments and `MoveSem.deinit`: the address-mentioning postcondition 'no comparison returned true' holds for `p3` and `pPrecise` but fails after a merge that violates the root-level address check (also when the merge passes the precise-everywhere policy); an address-free postcondition fails to transfer across a value clobber (`pClobber`, both directions); backward transfer fails when coalescing removes undefined behaviour (`pUBRemoved`, a read of an uninitialized local) and for an address-mentioning postcondition (`p3`, where the root-level address check also fails).

**Tier.** T1 — Witnesses for each hypothesis of the transfer card. Paired with `vc-transfer-address-free-and-address-mentioning` (tightness witnesses of its hypotheses).

**Statement.** Basis: execution (Lean kernel check).

```lean
-- lean/ToyCoalesce/CexMerge.lean:299-302
theorem cex_vc_forward_addrPost_needs_classAddrDisjoint :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    ¬ ClassAddrDisjoint p3 (single 0 1 0) ∧ ¬ AddrFree cmpAllFalse ∧ Valid semD p3 cmpAllFalse ∧
    ¬ Valid semD (coalesce (single 0 1 0) p3) cmpAllFalse := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:323-327
theorem cex_vc_forward_addrPost_precisePolicy :
    ForestWF pPrecise (single 1 0 0) ∧ NoValueClobberStmt .deinit (single 1 0 0) pPrecise ∧
    ¬ ClassAddrDisjoint pPrecise (single 1 0 0) ∧
    PolicyCheck (fun _ => .precise) pPrecise (single 1 0 0) ∧
    Valid semD pPrecise cmpAllFalse ∧ ¬ Valid semD (coalesce (single 1 0 0) pPrecise) cmpAllFalse := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:352-356
theorem cex_vc_forward_addrFree_needs_noValueClobber :
    ForestWF pClobber (single 0 1 0) ∧ ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    Valid semD pClobber (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    ¬ Valid semD (coalesce (single 0 1 0) pClobber) (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:375-379
theorem cex_vc_backward_needs_ubFree :
    ForestWF pUBRemoved (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) pUBRemoved ∧
    AddrFree (erasedIs [.vals [.int 5]]) ∧ ¬ UBFree semD pUBRemoved ∧
    Valid semD (coalesce (single 0 1 0) pUBRemoved) (erasedIs [.vals [.int 5]]) ∧
    ¬ Valid semD pUBRemoved (erasedIs [.vals [.int 5]]) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:196-200
theorem cex_vc_backward_needs_noValueClobber :
    ForestWF pClobber (single 0 1 0) ∧ ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    UBFree semD pClobber ∧ AddrFree (erasedIs [.vals [.int 9], .vals [.int 9, .int 5]]) ∧
    Valid semD (coalesce (single 0 1 0) pClobber) (erasedIs [.vals [.int 9], .vals [.int 9, .int 5]]) ∧
    ¬ Valid semD pClobber (erasedIs [.vals [.int 9], .vals [.int 9, .int 5]]) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:225-228
theorem cex_vc_backward_addrPost :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    UBFree semD p3 ∧ ¬ AddrFree someCmpTrue ∧
    Valid semD (coalesce (single 0 1 0) p3) someCmpTrue ∧ ¬ Valid semD p3 someCmpTrue := by …
```

**Hypothesis ledger.**

* (no hypotheses beyond the quantified data)

**Depth.** shallow

**Non-vacuity witness.** The programs named. (Lean: `cex_vc_forward_addrPost_needs_classAddrDisjoint`)

**Non-claims.** Listed under `## Boundaries` (card `vc-transfer-counterexamples`); read them before relying on this card.

**Prior art.**

* Published reference package `dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing` (namespace `Toy.SlotCompact`), google/zerocopy branch `reference`, commit a85598234b05e6dcc9afb9e81d2e396cc1218751 (no later commit touches the package as of 2026-11-21; no correction commit exists): `vc_transfer_of_noClobber` (lean/ToySlotCompact/WP.lean:212), `vc_forward_of_noClobber` (WP.lean:181), `vc_backward_of_noClobber` (WP.lean:196), cards `vc-transfer-original-to-compacted` / `vc-transfer-compacted-to-original`. Cited as the address-free analogue; not applied.

**Design question.** Which hypotheses of verification-condition transfer are needed?

### Auxiliary declarations cited by name (verbatim)

```lean
-- lean/ToyCoalesce/Upgrade.lean:177-178
theorem evalOp_move_eq_copy (ms : MoveSem) (h : ms ≠ .deinit) (P : Prog) (s : St) (q : Place) :
    evalOp ms P s (.move q) = evalOp ms P s (.copy q) := by …
```

```lean
-- lean/ToyCoalesce/Staging.lean:273-274
theorem noStagingNeeded_of_noStagingNeeded_coalesce (P : Prog) (μ : Forest) (hwf : ForestWF P μ)
    (hnc : NoStagingNeeded (coalesce μ P)) : NoStagingNeeded P := by …
```

```lean
-- lean/ToyCoalesce/Staging.lean:293-294
theorem Refines.trans {s1 s2 s3 : Sem} {P1 P2 P3 : Prog} (h12 : Refines s1 P1 s2 P2)
    (h23 : Refines s2 P2 s3 P3) : Refines s1 P1 s3 P3 := by …
```

```lean
-- lean/ToyCoalesce/VC.lean:35-36
theorem valid_of_refines {semT semS : Sem} {T S : Prog} {Post : List Event → Prop}
    (h : Refines semT T semS S) (hv : Valid semS S Post) : Valid semT T Post := by …
```

```lean
-- lean/ToyCoalesce/Programs.lean:14-14
def A0 : Layout := fun x => 10 * x + 10
```

```lean
-- lean/ToyCoalesce/Programs.lean:20-26
def pDtor : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .storageLive 2,
    .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .assign ⟨2, 0, 1⟩ [.copy ⟨0, 0, 1⟩], .out (.copy ⟨2, 0, 1⟩)]
  dtors := [.out (.load ⟨1, 0, 1⟩ 1)]
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:29-29
def pNoDtor : Prog := { pDtor with dtors := [] }
```

```lean
-- lean/ToyCoalesce/Programs.lean:53-53
def pIPLoad : Prog := pCall [.assign ⟨2, 0, 1⟩ [.lit 2], .out (.load ⟨1, 0, 1⟩ 1)] []
```

```lean
-- lean/ToyCoalesce/Programs.lean:56-56
def pIPStore : Prog := pCall [.store ⟨1, 0, 1⟩ (.lit 2), .out (.copy ⟨2, 0, 1⟩)] []
```

```lean
-- lean/ToyCoalesce/Programs.lean:59-59
def pIPAddr : Prog := pCall [.ptrEq (.addrOf ⟨2, 0, 1⟩) (.copy ⟨1, 0, 1⟩)] []
```

```lean
-- lean/ToyCoalesce/Programs.lean:62-62
def pIPAfter : Prog := pCall [.assign ⟨2, 0, 1⟩ [.lit 2]] [.out (.copy ⟨0, 0, 1⟩)]
```

```lean
-- lean/ToyCoalesce/Programs.lean:65-65
def pIPOk : Prog := pCall [.out (.copy ⟨2, 0, 1⟩)] []
```

```lean
-- lean/ToyCoalesce/Programs.lean:68-73
def pReuse : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.copy ⟨0, 0, 1⟩], .out (.copy ⟨0, 0, 1⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:94-94
def qx : Place := ⟨0, 0, 1⟩
```

```lean
-- lean/ToyCoalesce/Programs.lean:104-110
def p3 : Prog where
  sizes := [1, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨1, 1, 1⟩ [.lit 5], .assign ⟨0, 0, 1⟩ [.lit 7],
    .out (.copy ⟨0, 0, 1⟩), .assign ⟨1, 0, 1⟩ [.lit 9],
    .ptrInRange (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨1, 0, 2⟩) 2, .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:113-119
def p3x : Prog where
  sizes := [1, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨1, 1, 1⟩ [.lit 5], .assign ⟨0, 0, 1⟩ [.lit 7],
    .out (.copy ⟨0, 0, 1⟩), .assign ⟨1, 0, 1⟩ [.lit 9], .out (.addrOf ⟨0, 0, 1⟩),
    .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:122-127
def pClobber : Prog where
  sizes := [1, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨1, 0, 1⟩ [.lit 9],
    .assign ⟨1, 1, 1⟩ [.lit 5], .out (.copy ⟨0, 0, 1⟩), .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:132-140
def pChain : Prog where
  sizes := [1, 2, 3]
  body := [.storageLive 0, .storageLive 2, .assign ⟨0, 0, 1⟩ [.lit 4], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨2, 0, 3⟩ [.lit 1, .lit 2, .lit 3],
    .ptrInRange (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨2, 0, 3⟩) 3, .out (.copy ⟨2, 0, 3⟩),
    .storageDead 0, .storageDead 2, .storageLive 1, .assign ⟨1, 0, 2⟩ [.lit 5, .lit 6],
    .out (.copy ⟨1, 0, 2⟩), .out (.addrOf ⟨1, 0, 2⟩), .storageDead 1]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:146-153
def pChainOk : Prog where
  sizes := [1, 2, 3]
  body := [.storageLive 0, .storageLive 2, .assign ⟨0, 0, 1⟩ [.lit 4], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨2, 0, 3⟩ [.lit 1, .lit 2, .lit 3], .out (.copy ⟨2, 0, 3⟩),
    .storageDead 0, .storageDead 2, .storageLive 1, .assign ⟨1, 0, 2⟩ [.lit 5, .lit 6],
    .out (.copy ⟨1, 0, 2⟩), .out (.addrOf ⟨1, 0, 2⟩), .storageDead 1]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:158-166
def pSib : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨1, 0, 1⟩ [.lit 2], .out (.copy ⟨1, 0, 1⟩),
    .ptrEq (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨1, 0, 1⟩), .storageDead 0, .storageDead 1,
    .storageLive 2, .assign ⟨2, 0, 1⟩ [.lit 3], .out (.copy ⟨2, 0, 1⟩),
    .out (.addrOf ⟨2, 0, 1⟩), .storageDead 2]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:174-180
def pPrecise : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨1, 0, 1⟩ [.lit 2], .out (.copy ⟨1, 0, 1⟩),
    .ptrEq (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨1, 0, 1⟩), .storageDead 0, .storageDead 1]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:183-188
def pPreciseOk : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨1, 0, 1⟩ [.lit 2], .out (.copy ⟨1, 0, 1⟩), .storageDead 0, .storageDead 1]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:192-197
def pSwap : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .storageLive 1,
    .assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:201-206
def pUBRemoved : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 5], .storageDead 0, .storageLive 1,
    .out (.copy ⟨1, 0, 1⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:214-220
def pPrmConflict : Prog where
  sizes := [1, 1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .storageLive 2, .assign ⟨2, 0, 1⟩ [.lit 42], .call 0 (.copy ⟨2, 0, 1⟩), .storageDead 0,
    .storageDead 2, .storageLive 3, .ptrEq (.copy ⟨1, 0, 1⟩) (.addrOf ⟨3, 0, 1⟩)]
  dtors := []
  fns := [⟨3, []⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:232-237
def pPrmEscaped : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 2, .storageLive 1, .assign ⟨1, 0, 1⟩ [.addrOf ⟨2, 0, 1⟩], .storageDead 2,
    .storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 7], .call 0 (.copy ⟨0, 0, 1⟩)]
  dtors := []
  fns := [⟨2, [.out (.load ⟨1, 0, 1⟩ 1)]⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:240-244
def pOobCall : Prog where
  sizes := [1, 1]
  body := [.storageLive 1, .assign ⟨1, 0, 1⟩ [.lit 7], .out (.copy ⟨1, 0, 1⟩), .call 0 (.lit 9)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:248-253
def pCalleeReorder : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .call 0 (.lit 0),
    .out (.copy ⟨1, 0, 1⟩)]
  dtors := []
  fns := [⟨2, [.assign ⟨1, 0, 1⟩ [.lit 99], .out (.copy ⟨0, 0, 1⟩)]⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:257-261
def pAliasSwap : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .call 0 (.move ⟨0, 0, 2⟩)]
  dtors := []
  fns := [⟨1, [.assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩)]⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:265-270
def pAliasCoalSwap : Prog where
  sizes := [2, 2, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2],
    .call 0 (.move ⟨1, 0, 2⟩)]
  dtors := []
  fns := [⟨2, [.assign ⟨2, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨2, 0, 2⟩)]⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:274-279
def pStageOobPrm : Prog where
  sizes := [2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2],
    .assign ⟨0, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .call 0 (.move ⟨0, 0, 0⟩)]
  dtors := []
  fns := [⟨1, []⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:283-288
def pCalleeCoalSwap : Prog where
  sizes := [2, 2, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .call 0 (.lit 0),
    .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := [⟨2, [.assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩]]⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:292-296
def pSmallParent : Prog where
  sizes := [1, 2]
  body := [.storageLive 1, .assign ⟨1, 0, 2⟩ [.lit 1, .lit 2], .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/Programs.lean:300-306
def pSwapPrm : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .storageLive 1,
    .assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩),
    .call 0 (.move ⟨0, 0, 0⟩)]
  dtors := []
  fns := [⟨2, []⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:310-317
def pLoadOther : Prog where
  sizes := [1, 1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .storageLive 2, .storageLive 3,
    .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨3, 0, 1⟩ [.lit 3], .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .assign ⟨1, 0, 1⟩ [.addrOf ⟨3, 0, 1⟩], .assign ⟨2, 0, 1⟩ [.copy ⟨0, 0, 1⟩],
    .out (.load ⟨1, 0, 1⟩ 1), .out (.copy ⟨2, 0, 1⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:10-10
abbrev semC : Sem := ⟨.asCopy, .atomic⟩
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:11-11
abbrev semD : Sem := ⟨.deinit, .atomic⟩
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:12-12
abbrev semI : Sem := ⟨.inPlaceCall, .atomic⟩
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:186-186
def obsBodyOnly (P : Prog) : ObsMask := fun t u => obsFrom P u (P.body.drop t)
```

```lean
-- lean/ToyCoalesce/CexUpgrade.lean:207-209
theorem nonvacuous_upgrade_refines_of_obsCert_licensed :
    UpgradeSite pNoDtor 5 qx ∧ ObsCert pNoDtor (obsAnalysis pNoDtor) ∧
    Licensed .deinit pNoDtor (obsAnalysis pNoDtor) 5 qx := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:21-21
def cmpAllFalse (t : List Event) : Prop := t.all (fun e => e != .cmp true) = true
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:176-178
theorem nonvacuous_coalesce_refines_of_noValueClobber_of_classAddrDisjoint (ms : MoveSem) :
    ForestWF pChainOk μChain ∧ NoValueClobberStmt ms μChain pChainOk ∧
    ClassAddrDisjoint pChainOk μChain := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:183-185
theorem nonvacuous_coalesce_single (ms : MoveSem) :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3x ∧
    (AddrTaken p3x 0 → AddrTaken p3x 1 → ¬ LexOverlap p3x 0 1) := by …
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:273-273
def pSwapStaged : Prog := stage (coalesce (single 1 0 0) pSwap)
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:340-340
def erasedIs (t0 : List Event) (t : List Event) : Prop := t.map Event.erase = t0
```

```lean
-- lean/ToyCoalesce/CexMerge.lean:400-404
theorem vc_forward_addrFree_p3 :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    ¬ ClassAddrDisjoint p3 (single 0 1 0) ∧
    Valid semD p3 (erasedIs [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]]) ∧
    Valid semD (coalesce (single 0 1 0) p3) (erasedIs [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]]) := by …
```

```lean
-- lean/ToyCoalesce/Examples.lean:43-43
theorem ex_obsCert_pos : ObsCert pDtor (obsAnalysis pDtor) := by …
```

```lean
-- lean/ToyCoalesce/Examples.lean:110-114
theorem ex_moveSem_outcomes :
    outcome semC (pDtor.upgradeAt 5) A0 = .done [.vals [.int 7], .vals [.int 7]] ∧
    outcome semD (pDtor.upgradeAt 5) A0 = .ub ∧
    outcome semI (pIPStore.upgradeAt 4) A0 = .done [.vals [.int 2]] ∧
    outcome semD (pIPStore.upgradeAt 4) A0 = .done [.vals [.int 1]] := by …
```

```lean
-- lean/ToyCoalesce/Examples.lean:134-134
theorem ex_windowsDisjoint_empty_interior : ¬ WindowsDisjoint ⟨0, 1, 0⟩ ⟨0, 0, 2⟩ := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:12-17
def pSelf : Prog where
  sizes := [1]
  body := [.storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 1], .assign ⟨0, 0, 1⟩ [.copy ⟨0, 0, 1⟩],
    .out (.copy ⟨0, 0, 1⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:22-26
theorem cex_upgrade_deinit_iff_lhs_overlap :
    pSelf.body[2]? = some (.assign qx [.copy qx]) ∧ ¬ WindowsDisjoint qx qx ∧
    outcome semD pSelf A0 = .done [.vals [.int 1]] ∧
    outcome semD (pSelf.upgradeAt 2) A0 = outcome semD pSelf A0 ∧
    ¬ NoReadBeforeReinit (run semD pSelf A0).log 2 true qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:31-31
def pReuseUB : Prog := { pReuse with dtors := [.out (.copy ⟨5, 0, 1⟩)] }
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:35-38
theorem cex_upgrade_deinit_iff_source_ub :
    UpgradeSite pReuseUB 3 qx ∧ outcome semD pReuseUB A0 = .ub ∧
    outcome semD (pReuseUB.upgradeAt 3) A0 = outcome semD pReuseUB A0 ∧
    ¬ NoReadBeforeReinit (run semD pReuseUB A0).log 3 true qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:45-48
theorem cex_upgrade_deinit_iff_bad_layout :
    UpgradeSite pReuse 3 qx ∧ outcome semD pReuse (fun _ => 0) = .badLayout ∧
    outcome semD (pReuse.upgradeAt 3) (fun _ => 0) = outcome semD pReuse (fun _ => 0) ∧
    ¬ NoReadBeforeReinit (run semD pReuse (fun _ => 0)).log 3 true qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:54-57
theorem nonvacuous_upgrade_moveDeinit_iff :
    UpgradeSite pNoDtor 5 qx ∧ outcome semD pNoDtor A0 ≠ .ub ∧
    outcome semD pNoDtor A0 ≠ .badLayout ∧
    NoReadBeforeReinit (run semD pNoDtor A0).log 5 true qx := …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:62-65
theorem nonvacuous_upgrade_moveDeinit_refines :
    UpgradeSite pNoDtor 5 qx ∧
    ∀ A, outcome semD pNoDtor A ≠ .ub → outcome semD pNoDtor A ≠ .badLayout →
      NoReadBeforeReinit (run semD pNoDtor A).log 5 true qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:71-73
theorem cex_upgrade_inPlaceCall_call_site :
    pIPStore.body[4]? = some (.call 0 (.copy qx)) ∧
    outcome semI (pIPStore.upgradeAt 4) A0 ≠ outcome semI pIPStore A0 := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:79-85
theorem nonvacuous_upgrade_moveInPlaceCall :
    CallSite pIPOk 4 0 qx ∧
    (∀ A, outcome semI pIPOk A ≠ .ub → outcome semI pIPOk A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPOk A).log 4 false qx) ∧
    (∀ A, outcome semI pIPOk A ≠ .ub → outcome semI pIPOk A ≠ .badLayout →
      CalleeAvoids (run semI pIPOk A).log 4 qx) ∧
    ¬ AddrTaken pIPOk (pIPOk.fn 0).prm := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:94-96
theorem cex_noRead_needs_obsCert :
    ¬ ObsCert pReuse (fun _ _ => false) ∧ (fun _ _ => false : ObsMask) (3 + 1) qx.base = false ∧
    ¬ NoReadBeforeReinit (run semD pReuse A0).log 3 false qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:102-104
theorem cex_noRead_needs_not_in_mask :
    ObsCert pReuse (obsAnalysis pReuse) ∧ obsAnalysis pReuse 4 0 = true ∧
    ¬ NoReadBeforeReinit (run semD pReuse A0).log 3 false qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:110-113
theorem cex_licensed_needs_obsCert :
    UpgradeSite pDtor 5 qx ∧
    ¬ ObsCert pDtor (fun _ _ => false) ∧ Licensed .deinit pDtor (fun _ _ => false) 5 qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:120-123
theorem cex_licensed_needs_licensing :
    UpgradeSite pDtor 5 qx ∧
    ObsCert pDtor (obsAnalysis pDtor) ∧ ¬ Licensed .deinit pDtor (obsAnalysis pDtor) 5 qx ∧
    ¬ Refines semD (pDtor.upgradeAt 5) semD pDtor := …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:129-133
def pCalleeSwap : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .call 0 (.copy ⟨0, 0, 2⟩)]
  dtors := []
  fns := [⟨1, [.assign ⟨1, 0, 2⟩ [.copy ⟨1, 1, 1⟩, .copy ⟨1, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩)]⟩]
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:139-142
theorem cex_stage_needs_calleesNoStaging :
    LocalsInRange pCalleeSwap ∧ ParamsInRange pCalleeSwap ∧ ¬ CalleesNoStaging pCalleeSwap ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage pCalleeSwap) ⟨.deinit, .atomic⟩ pCalleeSwap ∧
    ¬ BehEq ⟨.deinit, .inOrder⟩ (stage pCalleeSwap) ⟨.deinit, .atomic⟩ pCalleeSwap := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:150-153
def pTmpClash : Prog :=
  { coalesce (single 1 0 0) pSwap with
    body := (coalesce (single 1 0 0) pSwap).body ++
      [.storageLive 2, .assign ⟨2, 0, 2⟩ [.lit 3, .lit 4], .out (.copy ⟨2, 0, 2⟩)] }
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:158-160
theorem cex_stage_behEq_needs_localsInRange :
    CalleesNoStaging pTmpClash ∧ ¬ LocalsInRange pTmpClash ∧
    ¬ BehEq ⟨.deinit, .inOrder⟩ (stage pTmpClash) ⟨.deinit, .atomic⟩ pTmpClash := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:172-177
def pOverlapSrc : Prog where
  sizes := [2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2],
    .assign ⟨0, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨0, 0, 2⟩)]
  dtors := []
  fns := []
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:181-185
theorem cex_pipeline_needs_noStagingNeeded :
    ForestWF pOverlapSrc [] ∧ NoValueClobberStmt .deinit [] pOverlapSrc ∧
    ClassAddrDisjoint pOverlapSrc [] ∧ CalleesNoStaging (coalesce [] pOverlapSrc) ∧
    ParamsInRange pOverlapSrc ∧ ¬ NoStagingNeeded pOverlapSrc ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce [] pOverlapSrc)) ⟨.deinit, .inOrder⟩ pOverlapSrc := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:219-219
def someCmpTrue (t : List Event) : Prop := t.any (fun e => e == .cmp true) = true
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:253-256
theorem cex_inOrder_eq_atomic_needs_noStaging :
    ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) ∧
    outcome ⟨.deinit, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A0 ≠
      outcome ⟨.deinit, .atomic⟩ (coalesce (single 1 0 0) pSwap) A0 := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:271-277
theorem cex_pipeline_needs_classAddrDisjoint :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    NoStagingNeeded p3 ∧ CalleesNoStaging (coalesce (single 0 1 0) p3) ∧ ParamsInRange p3 ∧
    NoStagingNeeded (coalesce (single 0 1 0) p3) ∧
    ¬ ClassAddrDisjoint p3 (single 0 1 0) ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce (single 0 1 0) p3)) ⟨.deinit, .inOrder⟩ p3 ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (coalesce (single 0 1 0) p3) ⟨.deinit, .inOrder⟩ p3 := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:286-293
theorem cex_pipeline_needs_noValueClobber :
    ForestWF pClobber (single 0 1 0) ∧ ClassAddrDisjoint pClobber (single 0 1 0) ∧
    NoStagingNeeded pClobber ∧ CalleesNoStaging (coalesce (single 0 1 0) pClobber) ∧
    ParamsInRange pClobber ∧ NoStagingNeeded (coalesce (single 0 1 0) pClobber) ∧
    ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce (single 0 1 0) pClobber)) ⟨.deinit, .inOrder⟩
      pClobber ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (coalesce (single 0 1 0) pClobber) ⟨.deinit, .inOrder⟩ pClobber := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:302-303
theorem nonvacuous_upgrade_outcome_eq_moveInPlaceCall_of_not_call :
    ∀ fn a, pReuse.body[3]? ≠ some (.call fn a) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:310-314
theorem cex_upgrade_deinit_refines_needs_site :
    ¬ UpgradeSite pReuse 3 ⟨1, 0, 1⟩ ∧
    (∀ A, outcome semD pReuse A ≠ .ub → outcome semD pReuse A ≠ .badLayout →
      NoReadBeforeReinit (run semD pReuse A).log 3 true ⟨1, 0, 1⟩) ∧
    ¬ Refines semD (pReuse.upgradeAt 3) semD pReuse := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:320-322
theorem nonvacuous_upgrade_refines_of_obsCert_licensed_inPlaceCall :
    UpgradeSite pIPOk 4 qx ∧ ObsCert pIPOk (obsAnalysis pIPOk) ∧
    Licensed .inPlaceCall pIPOk (obsAnalysis pIPOk) 4 qx := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:329-332
theorem cex_licensed_incomplete :
    UpgradeSite pLoadOther 8 qx ∧
    (∀ O, ObsCert pLoadOther O → ¬ Licensed .deinit pLoadOther O 8 qx) ∧
    Refines semD (pLoadOther.upgradeAt 8) semD pLoadOther := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:355-364
theorem cex_coalesce_needs_forestWF (ms : MoveSem) :
    ¬ ForestWF pSmallParent (single 1 0 0) ∧
    NoValueClobberStmt ms (single 1 0 0) pSmallParent ∧
    (AddrTaken pSmallParent 1 → AddrTaken pSmallParent 0 → ¬ LexOverlap pSmallParent 1 0) ∧
    ClassAddrDisjoint pSmallParent (single 1 0 0) ∧
    PolicyCheck (fun _ => .lexical) pSmallParent (single 1 0 0) ∧
    AddrFree (fun _ => True) ∧ Valid ⟨ms, .atomic⟩ pSmallParent (fun _ => True) ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSmallParent) A0 = .ub ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSmallParent) ⟨ms, .atomic⟩ pSmallParent ∧
    ¬ Valid ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSmallParent) (fun _ => True) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:390-403
theorem cex_coalesce_needs_callsInBounds (ms : MoveSem) :
    ¬ CallsInBounds pOobCall ∧ ¬ ForestWF pOobCall (single 1 0 0) ∧
    NoValueClobberStmt ms (single 1 0 0) pOobCall ∧
    (AddrTaken pOobCall 1 → AddrTaken pOobCall 0 → ¬ LexOverlap pOobCall 1 0) ∧
    ClassAddrDisjoint pOobCall (single 1 0 0) ∧
    (∀ pol : Policy, PolicyCheck pol pOobCall (single 1 0 0)) ∧
    NoStagingNeeded pOobCall ∧ NoStagingNeeded (coalesce (single 1 0 0) pOobCall) ∧
    CalleesNoStaging (coalesce (single 1 0 0) pOobCall) ∧ ParamsInRange pOobCall ∧
    Valid ⟨ms, .atomic⟩ pOobCall (fun _ => True) ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) A0 = .ub ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) ⟨ms, .atomic⟩ pOobCall ∧
    ¬ Refines ⟨ms, .inOrder⟩ (stage (coalesce (single 1 0 0) pOobCall)) ⟨ms, .inOrder⟩ pOobCall ∧
    ¬ Refines ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pOobCall) ⟨ms, .inOrder⟩ pOobCall ∧
    ¬ Valid ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) (fun _ => True) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:433-435
theorem nonvacuous_ufCheck :
    ForestWF pChainOk μChain ∧ ufCheck pChainOk μChain = true ∧
    ClassAddrDisjointW pChainOk μChain := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:440-445
theorem cex_ufCheck_needs_forestWF :
    ¬ ForestWF pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] ∧
    ClassAddrDisjointW pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] ∧
    ufCheck pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] = false ∧
    ¬ (ufCheck pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] = true ↔
      ClassAddrDisjointW pPreciseOk [⟨0, 1, 0⟩, ⟨1, 0, 0⟩]) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:457-464
theorem cex_callee_reorder_rejected_by_policy (ms : MoveSem) :
    ForestWF pCalleeReorder (single 0 1 0) ∧
    ¬ AddrTaken pCalleeReorder 0 ∧ ¬ AddrTaken pCalleeReorder 1 ∧
    ¬ PolicyCheck (fun b => if b then .lexical else .precise) pCalleeReorder (single 0 1 0) ∧
    ¬ NoValueClobberStmt ms (single 0 1 0) pCalleeReorder ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 0 1 0) pCalleeReorder) A0 =
      .done [.vals [.int 99], .vals [.int 99]] ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) pCalleeReorder) ⟨ms, .atomic⟩ pCalleeReorder := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:477-481
theorem nonvacuous_staging :
    NoStagingNeeded pSwap ∧ ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) ∧
    CalleesNoStaging (coalesce (single 1 0 0) pSwap) ∧
    ParamsInRange (coalesce (single 1 0 0) pSwap) ∧
    LocalsInRange (coalesce (single 1 0 0) pSwap) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:484-486
theorem nonvacuous_coalesce_refines_inOrder_of_noStagingNeeded (ms : MoveSem) :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3x ∧
    ClassAddrDisjoint p3x (single 0 1 0) ∧ NoStagingNeeded (coalesce (single 0 1 0) p3x) := …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:498-505
theorem cex_pipeline_needs_calleesNoStaging :
    ForestWF pCalleeCoalSwap (single 1 0 0) ∧
    NoValueClobberStmt .deinit (single 1 0 0) pCalleeCoalSwap ∧
    ClassAddrDisjoint pCalleeCoalSwap (single 1 0 0) ∧ NoStagingNeeded pCalleeCoalSwap ∧
    ParamsInRange pCalleeCoalSwap ∧
    ¬ CalleesNoStaging (coalesce (single 1 0 0) pCalleeCoalSwap) ∧
    ¬ Refines ⟨.deinit, .inOrder⟩ (stage (coalesce (single 1 0 0) pCalleeCoalSwap))
      ⟨.deinit, .inOrder⟩ pCalleeCoalSwap := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:520-523
theorem cex_stage_refines_needs_paramsInRange :
    CalleesNoStaging pStageOobPrm ∧ ¬ ParamsInRange pStageOobPrm ∧
    outcome ⟨.inPlaceCall, .inOrder⟩ (stage pStageOobPrm) A0 = .ub ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage pStageOobPrm) ⟨.inPlaceCall, .atomic⟩ pStageOobPrm := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:536-542
theorem cex_pipeline_needs_paramsInRange :
    ForestWF pSwapPrm (single 1 0 0) ∧
    NoValueClobberStmt .inPlaceCall (single 1 0 0) pSwapPrm ∧
    ClassAddrDisjoint pSwapPrm (single 1 0 0) ∧ NoStagingNeeded pSwapPrm ∧
    CalleesNoStaging (coalesce (single 1 0 0) pSwapPrm) ∧ ¬ ParamsInRange pSwapPrm ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage (coalesce (single 1 0 0) pSwapPrm))
      ⟨.inPlaceCall, .inOrder⟩ pSwapPrm := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:553-559
theorem nonvacuous_vc_p3x :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3x ∧
    ClassAddrDisjoint p3x (single 0 1 0) ∧ UBFree semD p3x ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) ∧
    Valid semD p3x (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) ∧
    Valid semD (coalesce (single 0 1 0) p3x)
      (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) := by …
```

```lean
-- lean/ToyCoalesce/CexExtra.lean:581-584
theorem cex_vc_needs_valid :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3x ∧
    ClassAddrDisjoint p3x (single 0 1 0) ∧ UBFree semD p3x ∧ AddrFree (fun _ => False) ∧
    ¬ Valid semD p3x (fun _ => False) ∧ ¬ Valid semD (coalesce (single 0 1 0) p3x) (fun _ => False) := by …
```

```lean
-- lean/ToyCoalesce/Refuted.lean:270-275
theorem cex_staging_inPlaceCall_alias :
    NoStagingNeededSyn pAliasSwap ∧ CalleesNoStagingSyn pAliasSwap ∧ LocalsInRange pAliasSwap ∧
    ParamsInRange pAliasSwap ∧ ¬ CalleesNoStaging pAliasSwap ∧
    outcome ⟨.inPlaceCall, .inOrder⟩ pAliasSwap A0 ≠ outcome ⟨.inPlaceCall, .atomic⟩ pAliasSwap A0 ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage pAliasSwap) ⟨.inPlaceCall, .atomic⟩ pAliasSwap ∧
    ¬ BehEq ⟨.inPlaceCall, .inOrder⟩ (stage pAliasSwap) ⟨.inPlaceCall, .atomic⟩ pAliasSwap := by …
```

```lean
-- lean/ToyCoalesce/Refuted.lean:314-324
theorem cex_pipeline_inPlaceCall_alias :
    ForestWF pAliasCoalSwap (single 0 1 0) ∧
    NoValueClobberStmt .inPlaceCall (single 0 1 0) pAliasCoalSwap ∧
    ClassAddrDisjoint pAliasCoalSwap (single 0 1 0) ∧ NoStagingNeededSyn pAliasCoalSwap ∧
    NoStagingNeededSyn (coalesce (single 0 1 0) pAliasCoalSwap) ∧
    CalleesNoStagingSyn (coalesce (single 0 1 0) pAliasCoalSwap) ∧ ParamsInRange pAliasCoalSwap ∧
    ¬ CalleesNoStaging (coalesce (single 0 1 0) pAliasCoalSwap) ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage (coalesce (single 0 1 0) pAliasCoalSwap))
      ⟨.inPlaceCall, .inOrder⟩ pAliasCoalSwap ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (coalesce (single 0 1 0) pAliasCoalSwap)
      ⟨.inPlaceCall, .inOrder⟩ pAliasCoalSwap := by …
```

#### Further declarations cited by name

```lean
-- lean/ToyCoalesce/Programs.lean:143-143
def μChain : Forest := [⟨0, 1, 1⟩, ⟨1, 2, 1⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:169-169
def μSib : Forest := [⟨0, 2, 0⟩, ⟨1, 2, 0⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:34-39
def pCall (cb tail : List Stmt) : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩], .call 0 (.copy ⟨0, 0, 1⟩)] ++ tail
  dtors := []
  fns := [⟨2, cb⟩]
```

```lean
-- lean/ToyCoalesce/Programs.lean:223-228
def A_eq03 : Layout := fun
  | 0 => 100
  | 1 => 200
  | 2 => 300
  | 3 => 100
  | n => 1000 + 10 * n
```

```lean
-- lean/ToyCoalesce/CexAdj.lean:17-22
def pBackHwf : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.lit 2], .call 0 (.move ⟨1, 0, 1⟩)]
  dtors := []
  fns := [⟨2, [.out (.copy ⟨2, 0, 1⟩)]⟩]
```

```lean
-- lean/ToyCoalesce/CexAdj.lean:38-44
theorem cex_vc_backward_needs_forestWF :
    ¬ ForestWF pBackHwf (single 2 0 0) ∧
    NoValueClobberStmt .inPlaceCall (single 2 0 0) pBackHwf ∧
    UBFree semI pBackHwf ∧
    AddrFree (erasedIs [.vals [.int 1]]) ∧
    Valid semI (coalesce (single 2 0 0) pBackHwf) (erasedIs [.vals [.int 1]]) ∧
    ¬ Valid semI pBackHwf (erasedIs [.vals [.int 1]]) := by …
```

```lean
-- lean/ToyCoalesce/CexAdj.lean:60-61
theorem cex_classAddrDisjoint_of_classAddrDisjointW_needs_h :
    ¬ ClassAddrDisjointW p3 (single 0 1 0) ∧ ¬ ClassAddrDisjoint p3 (single 0 1 0) := by …
```

```lean
-- lean/ToyCoalesce/CexAdj.lean:66-66
theorem nonvacuous_classAddrDisjoint_of_classAddrDisjointW : ClassAddrDisjointW pChainOk μChain := by …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:18-19
theorem nonvacuous_not_policySound_of_precise_for_addrTaken :
    (fun _ => Notion.precise : Policy) true = .precise ∧ ¬ PolicySound (fun _ => .precise) := …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:25-27
theorem cex_not_policySound_of_precise_needs_h :
    (fun b => if b then Notion.lexical else .precise : Policy) true ≠ .precise ∧
    PolicySound (fun b => if b then .lexical else .precise) := …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:34-36
theorem not_policySoundWith_noCallCheck (pol : Policy) :
    ForestWFNoCallCheck pOobCall (single 1 0 0) ∧ PolicyCheck pol pOobCall (single 1 0 0) ∧
    ¬ PolicySoundWith ForestWFNoCallCheck PolicyCheck pol := by …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:64-70
theorem cex_vc_forward_needs_noValueClobber_classAddrDisjoint :
    ForestWF pClobber (single 0 1 0) ∧ ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    ClassAddrDisjoint pClobber (single 0 1 0) ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    Valid semD pClobber (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    ¬ Valid semD (coalesce (single 0 1 0) pClobber)
      (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) := by …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:78-82
theorem cex_vc_forward_needs_callsInBounds (ms : MoveSem) :
    ¬ ForestWF pOobCall (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pOobCall ∧
    ClassAddrDisjoint pOobCall (single 1 0 0) ∧ AddrFree (fun _ => True) ∧
    Valid ⟨ms, .atomic⟩ pOobCall (fun _ => True) ∧
    ¬ Valid ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pOobCall) (fun _ => True) := by …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:92-95
theorem pIPAfter_violates_noReadAfterCall :
    outcome semI pIPAfter A0 = .done [.vals [.int 1]] ∧
    ¬ (∀ A, outcome semI pIPAfter A ≠ .ub → outcome semI pIPAfter A ≠ .badLayout →
      NoReadBeforeReinit (run semI pIPAfter A).log 4 false qx) := by …
```

```lean
-- lean/ToyCoalesce/CexSupport.lean:104-107
theorem pIPStore_violates_calleeAvoids :
    outcome semI pIPStore A0 = .done [.vals [.int 1]] ∧
    ¬ (∀ A, outcome semI pIPStore A ≠ .ub → outcome semI pIPStore A ≠ .badLayout →
      CalleeAvoids (run semI pIPStore A).log 4 qx) := by …
```

### External quotes and modeling bridge (derived)

Each quote is verbatim from a pinned upstream file; the remark after it is a `derived (modeling bridge)` statement, not a finding about rustc.

#### rustc destination propagation module documentation

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/dest_prop.rs:49-57
//! * Finally, we want `p` and `q` to use the same memory - however, we still need to make sure that
//!   each of them has enough "ownership" of that memory to continue "doing its job." More
//!   precisely, what we will check is that whenever the program performs a write to `p`, then it
//!   does not currently care about what the value in `q` is (and vice versa). We formalize the
//!   notion of "does not care what the value in `q` is" by checking the *liveness* of `q`.
//!
//!   Because of the difficulty of computing liveness of places that have their address taken, we do
//!   not even attempt to do it. Any places that are in a local that has its address taken is
//!   excluded from the optimization.
```

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/dest_prop.rs:64-66
//! The current implementation relies on live range computation to check for conflicts. We only
//! allow to merge locals that have disjoint live ranges. The live range are defined with
//! half-statement granularity, so as to make all writes be live for at least a half statement.
```

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/dest_prop.rs:72-75
//! * Merging storage liveness ranges instead of removing storage statements completely. This may
//!   improve stack usage.
//!
//! * Allow merging locals into places with projections, eg `_5` into `_6.foo`.
```

Derived (modeling bridge): the documented design merges unprojected locals with disjoint live ranges and excludes locals whose address is taken; merging into projections and merging storage ranges are listed as future work. The toy studies exactly the excluded region (address-taken locals, merges into field windows, erased storage statements of merged classes). Nothing here describes the behaviour of the implementation.

#### MIR `Operand::Move`

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1289-1293
    /// Creates a value by performing loading the place, just like the `Copy` operand.
    ///
    /// This *may* additionally overwrite the place with `uninit` bytes, depending on how we decide
    /// in [UCG#188]. You should not emit MIR that may attempt a subsequent second load of this
    /// place without first re-initializing it.
```

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1295-1303
    /// **Needs clarification:** The operational impact of `Move` is unclear. Currently (both in
    /// Miri and codegen) it has no effect at all unless it appears in an argument to `Call`; for
    /// `Call` it allows the argument to be passed to the callee "in-place", i.e. the callee might
    /// just get a reference to this place instead of a full copy. Miri implements this with a
    /// combination of aliasing model "protectors" and putting `uninit` into the place. Ralf
    /// proposes that we don't want these semantics for `Move` in regular assignments, because
    /// loading a place should not have side-effects, and the aliasing model "protectors" are
    /// inherently tied to a function call. Are these the semantics we want for MIR? Is this
    /// something we can even decide without knowing more about Rust's memory model?
```

Derived (modeling bridge): `MoveSem.deinit` models the documented possibility of overwriting the place with `uninit`; `MoveSem.inPlaceCall` models in-place passing of `Call` arguments, without the protectors and without the `uninit` write that the documentation describes for Miri. The documentation leaves the choice open (rust-lang/unsafe-code-guidelines#188, an open issue), so every result here is stated per semantics.

#### MIR `Assign` overlap

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:328-333
    /// **Needs clarification**: We currently require that the LHS place not overlap with any place
    /// read as part of computation of the RHS for some rvalues. This requirement is under
    /// discussion in [#68364]. Specifically, overlap is permitted only for assignments of a type
    /// with `BackendRepr::Scalar | BackendRepr::ScalarPair` where all the scalar fields are
    /// [`Scalar::Initialized`][rustc_abi::Scalar::Initialized]. As a part of this discussion, it is
    /// also unclear in what order the components are evaluated.
```

Derived (modeling bridge): the toy has no overlap requirement; instead it fixes two evaluation orders (`atomic`, `inOrder`) and shows that coalescing can create overlapping assignments whose in-order result differs, and that staging removes the difference. rust-lang/rust#68364 is an open issue and is not relied on.

#### MIR storage statements

```text
-- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:370-381
    /// `StorageLive`/`StorageDead` act like the heap operations `allocate`/`deallocate`, but for
    /// stack-allocated local variables. Using a local in any way (not only reading/writing from it)
    /// while it is unallocated is UB.
    ///
    /// Some locals have no `StorageLive` or `StorageDead` statements within the entire MIR body.
    /// These locals are implicitly allocated for the full duration of the function. There is a
    /// convenience method at `rustc_mir_dataflow::storage::always_storage_live_locals` for
    /// computing these locals.
    ///
    /// If the local is already allocated, calling `StorageLive` again will implicitly free the
    /// local and then allocate fresh uninitialized memory. If a local is already deallocated,
    /// calling `StorageDead` again is a NOP.
```

Derived (modeling bridge): the toy allocates through storage statements and copy-passed call parameters and in no other way; a coalesced class root is allocated once at entry, which plays the role of a local without storage statements.

#### Cited address-free baseline (published package)

```text
-- google/zerocopy@a85598234b05e6dcc9afb9e81d2e396cc1218751:reports/dead-slot-compaction-injective-reindexing-bisimulation-and-indexed-store-framing/lean/ToySlotCompact/Bisim.lean:74-77
theorem compact_silentBisim_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) :
    SilentBisim p (compact p L π) (CompactRel p L π) := by …
```

#### CompCert register allocation by a posteriori validation

```text
-- AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:backend/Allocation.v:13-13
(** Register allocation by external oracle and a posteriori validation. *)
```

```text
-- AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:backend/Allocation.v:22-25
(** The validation algorithm used here is described in
  "Validating register allocation and spilling",
  by Silvain Rideau and Xavier Leroy,
  in Compiler Construction (CC 2010), LNCS 6011, Springer, 2010. *)
```

Derived (modeling bridge): the certificate of `observation-certificate-checker-and-least-solution` follows the same pattern (an untrusted analysis result is checked rather than trusted); CompCert's validator concerns register and spill-slot allocation, not this toy's address-taken locals, and no formal relation between the two is stated.

## Boundaries

### Non-claims

Non-claims come first: each card's list says what the card does not show. Read the list of a card before relying on it.

#### `upgrade-moveAsCopy-equivalence` (theorem)

* Says nothing about `MoveSem.deinit` or `MoveSem.inPlaceCall`, where upgrades can change behaviour (`cex_upgrade_moveDeinit_dtorLoad`, `cex_upgrade_moveInPlaceCall_calleeAvoids`).
* `Prog.upgradeAt` rewrites a single-operand assignment, a `call` or an `out` statement of `P.body`; multi-operand aggregates, `store`, `ptrEq`, `ptrInRange`, destructor statements (`P.dtors`) and callee bodies (`P.fns`) are left unchanged.
* Does not claim that `MoveSem.asCopy` is the intended semantics of `move` in any real IR.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `upgrade-moveDeinit-iff-no-read-before-reinit` (characterization)

* The condition is dynamic (over the source run's access log); it is not a static analysis. A static, sound over-approximation is the separate card `observation-certificate-licenses-upgrades`.
* The `↔` is per layout (outcome equality on one layout whose source run is neither undefined nor excluded). No converse of the refinement form is proved: `Refines` is not characterized (for example, by the definition of `Refines`, refinement holds whenever the source has undefined behaviour on some non-excluded run).
* The per-layout `↔` is stated for upgrade sites; with a left side overlapping `q` it fails (`cex_upgrade_deinit_iff_lhs_overlap`); multi-operand aggregates are not covered.
* Reads of uninitialized cells are undefined behaviour in this toy for every operand kind; a semantics in which copying uninitialized bytes is allowed would change the 'only if' direction (not proved here).
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `upgrade-moveInPlaceCall-sufficient-conditions` (theorem)

* These are sufficient conditions; no converse is proved. For example, a callee that never writes its parameter can accept a moved argument even if the caller reads `q` afterwards, violating (a) (not proved here).
* Condition (c) is about the whole program, not the callee body: the weaker condition `CalleeNoParamAddr P fn` (the callee body never takes its parameter's address) does not suffice (`cex_inPlaceCall_param_addrTaken_in_caller`, `cex_inPlaceCall_param_conflict`; earlier formulation refuted by `refuted_upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_noParamAddr`).
* The in-place reading here is deterministic (the parameter always aliases the argument) and performs no de-initialization; a semantics that may or may not alias, and a combined de-initializing and in-place semantics, are not modeled.
* `MoveSem.inPlaceCall` models no aliasing-model protectors (such as the function-call protectors of Stacked Borrows; the cited `Operand::Move` documentation, `syntax.rs:1295-1303`, says that Miri implements in-place argument passing with protectors); how protectors would affect these results is not examined here.
* Callee bodies run in the caller's frame and may name caller locals; storage statements and nested calls inside callees are undefined behaviour in this toy.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `destructor-load-breaks-deinit-upgrade` (counterexample)

* Destructors are modeled as one straight-line block `P.dtors` run after `P.body`; drop elaboration, drop flags, reverse drop order and unwinding paths are not modeled.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `in-place-call-upgrade-counterexamples` (counterexample)

* Each counterexample exhibits one hazard: `pIPAfter` the callee writing its parameter; `pIPStore`, `pIPAddr` and `pIPLoad` an escaped pointer to `x` reaching the callee; `pPrmEscaped` and `pPrmConflict` the caller taking the address of the parameter local. That removing its hazard from each program restores refinement is not proved here; `pIPOk`, a separate program with none of these hazards, satisfies all three conditions (`nonvacuous_upgrade_moveInPlaceCall`).
* The load-through-escaped-pointer program `pIPLoad` violates (b) and also the `MoveSem.deinit` condition; it is not a canonical witness for (b) alone (that is `pIPStore`).
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `moveDeinit-moveInPlaceCall-incomparable` (counterexample)

* Incomparability is shown between the two separate readings (`MoveSem.deinit` alone, `MoveSem.inPlaceCall` alone) under `AssignMode.atomic`; a combined semantics performing both de-initialization and in-place passing is not modeled, and its relation to either reading is not proved here.
* Does not say which reading real MIR adopts (the cited `Operand::Move` documentation, `syntax.rs:1295-1303`, says that the operational impact of `Move` is unclear, and rust-lang/unsafe-code-guidelines#188 is an open issue).
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `observation-certificate-checker-and-least-solution` (characterization)

* Says nothing about soundness with respect to the semantics (that is `observation-certificate-licenses-upgrades`).
* The analysis is over straight-line code (no control-flow joins, loops or fixpoint iteration); callee summaries are single-level because nested calls inside callees are undefined behaviour in this toy.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `observation-certificate-licenses-upgrades` (theorem)

* The analysis is whole-local and treats every `load` as possibly reading every address-taken local (no points-to precision); stores do not kill.
* No completeness: some sound upgrades are licensed by no certificate. On `pLoadOther` no certificate licenses the `MoveSem.deinit` upgrade at body index 8, yet the upgrade is a refinement (`cex_licensed_incomplete`).
* For `MoveSem.inPlaceCall` the licensing condition on the parameter is `¬ AddrTaken P (P.fn fn).prm`; the earlier condition `CalleeNoParamAddr P fn` is insufficient (`refuted_upgrade_refines_of_obsCert_licensed_noParamAddr`).
* The analysis is over straight-line code (no control-flow joins, loops or fixpoint iteration); callee summaries are single-level because nested calls inside callees are undefined behaviour in this toy.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `destructor-blind-analysis-admits-unsound-upgrade` (counterexample)

* `pDtor` is a counterexample for `MoveSem.deinit` at a non-call site; under `MoveSem.asCopy` and `MoveSem.inPlaceCall` the same upgrade leaves the outcome unchanged on every layout (`upgrade_outcome_eq_moveAsCopy`, `upgrade_outcome_eq_moveInPlaceCall_of_not_call`).
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `single-merge-into-field-sufficient` (theorem)

* This is a sufficient condition; no 'iff' is proved for a fixed program (for example, whether a program that takes both addresses without ever comparing them admits the merge when the lexical address condition fails is not proved here).
* The one-sided condition 'if `x` is address-taken, `x` and the whole of `y` are lexically disjoint' is not necessary: `coalesce_single_refines_addrTaken_child_only` merges an address-taken `x` into a non-address-taken `y` that is allocated at the same time.
* `NoValueClobberStmt` is a dynamic condition; no static checker for it is proved here (the cited address-free package proves static certificate conditions for its own language).
* Under in-order field writes the coalesced program may need staging (card `coalescing-creates-overlap-and-recoalescing-pitfall`).
* `coalesce` yields one-way `Refines`, not `BehEq`: erasing the storage statements of class members can remove undefined behaviour from reading an unallocated or uninitialized member (`pUBRemoved`, `cex_vc_backward_needs_ubFree`).
* `coalesce` hoists the allocation of each class root to function entry (extending its storage lifetime to the whole run); alignment and padding are not modeled.
* Layouts give one static address per local, without allocation generations: a re-allocated local reuses its address and old pointers to it stay valid, whereas the cited MIR storage documentation (`syntax.rs:370-381`) describes a repeated `StorageLive` as freeing the local and allocating fresh memory.
* `AddrTaken` is a syntactic over-approximation (any `addrOf`, or an in-place escape, anywhere in the program, even in a callee that is never called); semantic address exposure is not tracked separately.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `address-taken-merge-overlap-breaks-refinement` (counterexample)

* The failure in `p3` uses both locals being address-taken, allocated together and compared. `p3x`, where `y` is not address-taken, is a refinement (`coalesce_single_refines_addrTaken_child_only`), and the card `single-merge-into-field-sufficient` gives a refinement whenever the lexical address condition holds together with its other hypotheses; whether a variant of `p3` that takes both addresses but never compares them breaks refinement is not proved here.
* The observation uses an explicit range comparison on absolute addresses; a pointer-comparison semantics that is nondeterministic across allocations is not examined.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `forest-coalescing-root-level-check-sufficient` (theorem)

* The check involves pairs of class members, not each member against its root local alone (that is insufficient: `cex_rootAddrCheck_insufficient_siblings`).
* Pairs with disjoint root-relative windows are not checked; the card's theorem shows that this is sound in this toy (informally, a static frame layout can place them at the same relative offsets in the source); it is not claimed for other layout models.
* `coalesce` yields one-way `Refines`, not `BehEq`: erasing the storage statements of class members can remove undefined behaviour from reading an unallocated or uninitialized member (`pUBRemoved`, `cex_vc_backward_needs_ubFree`).
* `coalesce` hoists the allocation of each class root to function entry (extending its storage lifetime to the whole run); alignment and padding are not modeled.
* Layouts give one static address per local, without allocation generations: a re-allocated local reuses its address and old pointers to it stay valid, whereas the cited MIR storage documentation (`syntax.rs:370-381`) describes a repeated `StorageLive` as freeing the local and allocating fresh memory.
* `AddrTaken` is a syntactic over-approximation (any `addrOf`, or an in-place escape, anywhere in the program, even in a callee that is never called); semantic address exposure is not tracked separately.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `pairwise-merge-checks-do-not-compose` (counterexample)

* What fails is validating edges independently against the original program and combining them into one forest. Sequential composition of refinements holds (`Refines.trans`): if each later merge is shown to be a refinement of the already-coalesced program (with its widened lifetimes), the composite is a refinement of the source.
* `pSib` merges both siblings into the same root-relative offset `y.0`; siblings merged into disjoint subfields (such as `y.0` and `y.1`) have non-intersecting windows and are not refuted by `pSib`.
* The per-edge facts proved for `pChain` are `NoValueClobberStmt` and the per-edge address check for each edge; refinement of each single-edge coalescing is not separately proved.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `union-find-interval-union-decides-root-check` (characterization)

* Decides the window-insensitive check `ClassAddrDisjointW`, which implies `ClassAddrDisjoint` (`classAddrDisjoint_of_classAddrDisjointW`); the converse implication is not proved here.
* `ufCheck P μ = true` decides the address-disjointness check; it does not check `NoValueClobberStmt`, `ForestWF` or the staging conditions, and does not by itself license coalescing.
* The 'union–find' is a list of blocks; no complexity claim is made.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `lifetime-policy-soundness-iff-lexical-for-address-taken` (characterization)

* `Policy` ranges over the two-element type `Notion` (`Notion.lexical` and the by-name access hull `Notion.precise`); the characterization neither establishes nor refutes the soundness of other, pointer-aware lifetime notions (for example from allocation or `addrOf` to the last pointer use).
* The characterization covers uniform policies (depending on whether a local is address-taken); per-local or program-dependent policies are not covered.
* Precise liveness here is the hull of by-name access points (calls that pass a place by `move` count as writes; a call marks both halves for locals its callee touches by name); it is not a full liveness analysis. With access points that split a call into a read half and a write half, the mixed policy is not sound (`refuted_policySound_mixed_halfPoints`).
* `PolicySound` quantifies over forests satisfying `ForestWF`, and its `CallsInBounds` clause cannot be dropped: with `ForestWFNoCallCheck` (`ForestWF` without `CallsInBounds`) in place of `ForestWF`, no policy is sound for `PolicyCheck` (`not_policySoundWith_noCallCheck`, from `cex_coalesce_needs_callsInBounds`: `pOobCall` calls an absent callee, passes every policy check for the merge `1 ↦ 0.0`, and its coalescing is not a refinement); the earlier formulation with half-statement access points is refuted by the same program (`refuted_policySound_of_lexical_noCallCheck_halfPoints`).
* Whether precise liveness becomes safe for address-taken locals under a weaker pointer-comparison semantics is not examined.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `overlap-staging-behavioural-equivalence` (theorem)

* `BehEq` is equality of behaviour sets (`∀ o, Beh T o ↔ Beh S o`), not a step-level bisimulation and not per-layout outcome equality (a layout that collides with a fresh staging temporary may be excluded for the staged program and not for the source; not proved here).
* The staging criterion is syntactic and conservative (any multi-operand assignment with a load is staged; in callees, any multi-operand assignment mixing places based at the parameter with other places); single-operand assignments are exempt because the toy evaluates a single operand completely before writing; IRs in which a single overlapping copy is undefined are not modeled.
* With callee assignments checked syntactically, ignoring in-place binding of the parameter, the three statements are false under `MoveSem.inPlaceCall` (`cex_staging_inPlaceCall_alias`; refuted earlier formulations `refuted_outcome_inOrder_eq_atomic_synStaging`, `refuted_stage_inOrder_refines_atomic_synStaging`, `refuted_stage_inOrder_behEq_atomic_synStaging`).
* `stage` does not rewrite callee bodies and adds one local per staged assignment (more locals and stack space).
* The temporary is never address-taken; staging of address-taken temporaries is not examined.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `coalesce-then-stage-pipeline` (theorem)

* For the no-overlap form, the absence of staging needs in the source is not a hypothesis: it follows from the hypothesis on the coalesced program for a well-formed forest (`noStagingNeeded_of_noStagingNeeded_coalesce`).
* Excluding staging temporaries from later coalescing is not shown sufficient by itself: the proved alternatives are re-staging after every coalescing, or a coalescer whose output needs no staging.
* The staging conditions are checked alias-aware inside callees; with syntactic callee checks the pipeline statements are false under `MoveSem.inPlaceCall` (`cex_pipeline_inPlaceCall_alias`).
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `coalescing-creates-overlap-and-recoalescing-pitfall` (counterexample)

* Both the overlap hazard and the re-coalescing pitfall are under `AssignMode.inOrder`; under `AssignMode.atomic` the unstaged coalescing of `pSwap` is a refinement (`cex_coalesce_without_staging_inOrder`), and a coalescer whose output needs no staging is covered by `coalesce_refines_inOrder_of_noStagingNeeded`.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `vc-transfer-address-free-and-address-mentioning` (theorem)

* Address-free transfer without `ClassAddrDisjoint` relies on this toy having no address-dependent control flow, no integer-pointer casts and no address-dependent indexing, so that addresses affect no integer value, memory content or undefined behaviour; in a language where a branch or an integer computation can depend on a pointer comparison (for example `if &x == &y { out 1 } else { out 2 }`), address-free postconditions need not transfer without an address condition (not proved here).
* Backward transfer of address-mentioning postconditions is not proved; it can fail even when `ClassAddrDisjoint` and `UBFree` hold, for example when two simultaneously live address-taken locals are merged into adjacent disjoint subfields of one root, which fixes a range comparison that the source may answer either way (not proved here).
* All transfer theorems here are stated under `AssignMode.atomic`; no verification-condition transfer theorem under `AssignMode.inOrder` is stated or proved here. Composing `valid_of_refines` with the refinements of the card `coalesce-then-stage-pipeline` gives forward transfer of arbitrary postconditions under that card's hypotheses (a sufficient condition; the composition is not stated as a separate theorem). Whether those staging conditions are necessary for verification-condition transfer under `AssignMode.inOrder` is not proved here, and neither is address-free transfer without `ClassAddrDisjoint` or backward transfer under `AssignMode.inOrder`.
* Validity here is total correctness over all non-excluded runs; partial-correctness variants are not examined.
* Forward transfer across copy-to-move upgrades and staging follows by composing `valid_of_refines` with those cards' refinement theorems (the compositions are not stated as separate theorems); no backward transfer across them is stated or proved here.
* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

#### `vc-transfer-counterexamples` (counterexample)

* These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about rustc MIR or any other compiler.

### Escape hatches

* `not_policySound_of_precise_for_addrTaken` (the impossibility half of
  `lifetime-policy-soundness-iff-lexical-for-address-taken`) is a statement about uniform policies
  over the two notions of `Notion`, about forests satisfying `ForestWF`, and about the toy's
  observation model, in which pointer comparisons (`ptrEq`, `ptrInRange`) and printed pointers
  expose absolute addresses. Its witness (`cex_policy_precise_for_addrTaken`) uses a `ptrEq` of two
  simultaneously allocated address-taken locals. A model without observable absolute addresses, a
  pointer-aware lifetime notion, or per-local policies falls outside the statement; whether
  precise liveness is then sound for address-taken locals is not examined (not proved here).
* Every counterexample card refutes one transformation instance under the hypotheses it lists. One
  way to escape such a counterexample is to restore the hypothesis whose failure it exhibits, where
  the paired theorem card proves that hypothesis sufficient together with its other hypotheses.
  Other changes can also defeat a particular witness program: for `pDtor`, under `MoveSem.asCopy`
  or `MoveSem.inPlaceCall` the same upgrade leaves the outcome unchanged on every layout
  (`upgrade_outcome_eq_moveAsCopy`, `upgrade_outcome_eq_moveInPlaceCall_of_not_call`); further
  candidates, such as avoiding the triggering observation or write, are mentioned in the cards'
  non-claims and are not proved here. Which changes defeat a witness is not characterized here.
  For example, `cex_coalesce_single_addrTaken_lexOverlap` uses two
  address-taken locals that are lexically allocated during a common tick and compared, and
  `cex_upgrade_moveDeinit_dtorLoad` uses a read through a pointer in the destructor block under
  `MoveSem.deinit`. The positive controls named in each card show nearby settings where the
  conclusion holds.

### Hypotheses whose tightness is `unknown`

* `upgrade-moveInPlaceCall-sufficient-conditions`, hypothesis `hsite` of
  `upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_paramNotAddrTaken` (the statement
  is a call whose argument is `copy q` and whose callee parameter is not `q.base`).
* `observation-certificate-licenses-upgrades`, hypothesis `hsite` of
  `upgrade_refines_of_obsCert_licensed` (the statement is an upgrade site).

No counterexample is proved for these; dropping them is not shown to break the conclusion.

### Dropped or disproved statements

None. Every main statement of the cards is proved as stated (no statement was weakened, dropped
or found false).

### Refuted earlier formulations (reference points, not results)

Each theorem in this section proves that an earlier formulation of a statement of this package is false. The earlier formulations used the definitions quoted first (which reproduce the earlier forms under new names); the current statements and definitions are in the cards above. These theorems are reference points, not results.

#### Earlier definitions

```lean
-- lean/ToyCoalesce/Refuted.lean:15-20
def ForestWFNoCallCheck (P : Prog) (μ : Forest) : Prop :=
  (μ.map Edge.child).Nodup ∧
  (∀ e ∈ μ, e.child < P.nloc ∧ e.parent < P.nloc ∧ e.child ≠ e.parent ∧
    e.off + P.size e.child ≤ P.size e.parent) ∧
  (∀ x, x < P.nloc → μ.parentOf (μ.root x) = none) ∧
  (∀ c ∈ P.fns, μ.inClass c.prm = false)
```

```lean
-- lean/ToyCoalesce/Refuted.lean:29-47
def LicensedNoParamAddr (ms : MoveSem) (P : Prog) (O : ObsMask) (k : Nat) (q : Place) : Prop :=
  match ms with
  | .asCopy => True
  | .deinit =>
    O (k + 1) q.base = false ∧
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      (P.fn fn).body.any (Stmt.mayReadNoCall P q.base) = false
  | .inPlaceCall =>
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      O (k + 1) q.base = false ∧
      (P.fn fn).body.any (fun st => st.operands.any (Operand.readsName q.base) ||
        (match st with
         | .store p _ => p.base == q.base
         | .assign lhs _ => lhs.base == q.base
         | _ => false)) = false ∧
      (decide (AddrTaken P q.base) && (P.fn fn).body.any (fun st =>
        st.operands.any Operand.isLoad || (match st with | .store _ _ => true | _ => false)))
        = false ∧
      CalleeNoParamAddr P fn
```

```lean
-- lean/ToyCoalesce/Refuted.lean:51-53
def AccessPtHalf (P : Prog) (u p : Nat) : Bool :=
  if p % 2 = 0 then (P.code.getD (p / 2) .nop).readsByName P u
  else (P.code.getD (p / 2) .nop).writesByName P u
```

```lean
-- lean/ToyCoalesce/Refuted.lean:56-61
def InIvHalf (nt : Notion) (P : Prog) (u p : Nat) : Bool :=
  match nt with
  | .lexical => LexLiveAt P u (p / 2)
  | .precise =>
    (List.range (p + 1)).any (AccessPtHalf P u) &&
    ((List.range (2 * P.code.length + 2)).filter (p ≤ ·)).any (AccessPtHalf P u)
```

```lean
-- lean/ToyCoalesce/Refuted.lean:64-65
def IvOverlapHalf (nu nv : Notion) (P : Prog) (u v : Nat) : Prop :=
  ∃ p, p < 2 * P.code.length + 2 ∧ InIvHalf nu P u p = true ∧ InIvHalf nv P v p = true
```

```lean
-- lean/ToyCoalesce/Refuted.lean:71-74
def PolicyCheckHalf (pol : Policy) (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    μ.windowsOverlap P u v = true →
    ¬ IvOverlapHalf (pol (decide (AddrTaken P u))) (pol (decide (AddrTaken P v))) P u v
```

```lean
-- lean/ToyCoalesce/Refuted.lean:80-83
def PolicySoundWith (wf : Prog → Forest → Prop) (chk : Policy → Prog → Forest → Prop)
    (pol : Policy) : Prop :=
  ∀ (ms : MoveSem) (P : Prog) (μ : Forest), wf P μ → chk pol P μ →
    Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P
```

```lean
-- lean/ToyCoalesce/Refuted.lean:87-88
def NoStagingNeededSyn (P : Prog) : Prop :=
  (stmtsNoStaging P.code && P.fns.all (fun c => stmtsNoStaging c.body)) = true
```

```lean
-- lean/ToyCoalesce/Refuted.lean:94-94
def CalleesNoStagingSyn (P : Prog) : Prop := P.fns.all (fun c => stmtsNoStaging c.body) = true
```

#### Refutations

**`refuted_upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_noParamAddr`** (refuted, not a result). The earlier in-place upgrade theorem assumed `CalleeNoParamAddr P fn` (the callee body never takes its parameter's address) where the current theorem assumes `¬ AddrTaken P (P.fn fn).prm`. Witness: `pPrmEscaped` (`cex_inPlaceCall_param_addrTaken_in_caller`), whose caller takes the address of the parameter local; `cex_inPlaceCall_param_conflict` is a second witness without any pointer to the parameter at the call.

```lean
-- lean/ToyCoalesce/Refuted.lean:164-173
theorem refuted_upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_noParamAddr :
    ¬ ∀ (am : AssignMode) (P : Prog) (k fn : Nat) (q : Place), CallSite P k fn q →
      (∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
        outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
        NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ P A).log k false q) →
      (∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
        outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
        CalleeAvoids (run ⟨.inPlaceCall, am⟩ P A).log k q) →
      CalleeNoParamAddr P fn →
      Refines ⟨.inPlaceCall, am⟩ (P.upgradeAt k) ⟨.inPlaceCall, am⟩ P := by …
```

**`refuted_upgrade_refines_of_obsCert_licensed_noParamAddr`** (refuted, not a result). The earlier licensed-upgrade theorem used `LicensedNoParamAddr` (with `CalleeNoParamAddr`). Witness: `pPrmEscaped` under `semI`.

```lean
-- lean/ToyCoalesce/Refuted.lean:180-182
theorem refuted_upgrade_refines_of_obsCert_licensed_noParamAddr :
    ¬ ∀ (sem : Sem) (P : Prog) (O : ObsMask) (k : Nat) (q : Place), UpgradeSite P k q →
      ObsCert P O → LicensedNoParamAddr sem.move P O k q → Refines sem (P.upgradeAt k) sem P := by …
```

**`refuted_coalesce_single_refines_noCallCheck`** (refuted, not a result). The earlier single-merge theorem used `ForestWFNoCallCheck` (no `CallsInBounds`). Witness: `pOobCall` with the merge `1 ↦ 0.0` (`cex_coalesce_needs_callsInBounds`): the absent callee is run with parameter local `0`, which coalescing allocates at entry.

```lean
-- lean/ToyCoalesce/Refuted.lean:190-194
theorem refuted_coalesce_single_refines_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (x y f : Nat), ForestWFNoCallCheck P (single x y f) →
      NoValueClobberStmt ms (single x y f) P →
      (AddrTaken P x → AddrTaken P y → ¬ LexOverlap P x y) →
      Refines ⟨ms, .atomic⟩ (coalesce (single x y f) P) ⟨ms, .atomic⟩ P := by …
```

**`refuted_coalesce_refines_noCallCheck`** (refuted, not a result). The earlier forest theorem used `ForestWFNoCallCheck`. Witness: `pOobCall`.

```lean
-- lean/ToyCoalesce/Refuted.lean:200-203
theorem refuted_coalesce_refines_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ →
      Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P := by …
```

**`refuted_policySound_of_lexical_noCallCheck_halfPoints`** (refuted, not a result). The earlier policy-soundness statement used `ForestWFNoCallCheck` and `AccessPtHalf`; it fails already for the lexical-everywhere policy. Witness: `pOobCall`.

```lean
-- lean/ToyCoalesce/Refuted.lean:211-212
theorem refuted_policySound_of_lexical_noCallCheck_halfPoints :
    ¬ ∀ pol : Policy, pol true = .lexical → PolicySoundWith ForestWFNoCallCheck PolicyCheckHalf pol := by …
```

**`refuted_policySound_iff_noCallCheck_halfPoints`** (refuted, not a result). The earlier characterization (same definitions) fails because its sufficiency half fails.

```lean
-- lean/ToyCoalesce/Refuted.lean:223-224
theorem refuted_policySound_iff_noCallCheck_halfPoints :
    ¬ ∀ pol : Policy, PolicySoundWith ForestWFNoCallCheck PolicyCheckHalf pol ↔ pol true = .lexical := …
```

**`refuted_policySound_mixed_halfPoints`** (refuted, not a result). Independently of absent callees: with `AccessPtHalf`, which puts all by-name reads of a callee body in the read half of the call and all by-name writes in the write half, the mixed policy is not sound even over forests satisfying `ForestWF`. Witness: `pCalleeReorder` (`cex_callee_reorder_rejected_by_policy`), whose callee writes `y` before reading `x`.

```lean
-- lean/ToyCoalesce/Refuted.lean:231-232
theorem refuted_policySound_mixed_halfPoints :
    ¬ PolicySoundWith ForestWF PolicyCheckHalf (fun b => if b then .lexical else .precise) := by …
```

**`refuted_vc_forward_addrFree_noCallCheck`** (refuted, not a result). The earlier address-free forward-transfer theorem used `ForestWFNoCallCheck`. Witness: `pOobCall` with the trivial postcondition.

```lean
-- lean/ToyCoalesce/Refuted.lean:238-241
theorem refuted_vc_forward_addrFree_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ∀ Post : List Event → Prop, AddrFree Post →
      Valid ⟨ms, .atomic⟩ P Post → Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := by …
```

**`refuted_vc_forward_of_classAddrDisjoint_noCallCheck`** (refuted, not a result). The earlier address-mentioning forward-transfer theorem used `ForestWFNoCallCheck`. Witness: `pOobCall` with the trivial postcondition.

```lean
-- lean/ToyCoalesce/Refuted.lean:249-252
theorem refuted_vc_forward_of_classAddrDisjoint_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ → ∀ Post : List Event → Prop,
      Valid ⟨ms, .atomic⟩ P Post → Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := by …
```

**`refuted_outcome_inOrder_eq_atomic_synStaging`** (refuted, not a result). The earlier statement checked callee assignments syntactically (`NoStagingNeededSyn`), ignoring that under `MoveSem.inPlaceCall` a place based at the callee parameter resolves into the argument place. Witness: `pAliasSwap` (`cex_staging_inPlaceCall_alias`).

```lean
-- lean/ToyCoalesce/Refuted.lean:283-285
theorem refuted_outcome_inOrder_eq_atomic_synStaging :
    ¬ ∀ (ms : MoveSem) (P : Prog), NoStagingNeededSyn P → ∀ A : Layout,
      outcome ⟨ms, .inOrder⟩ P A = outcome ⟨ms, .atomic⟩ P A := …
```

**`refuted_stage_inOrder_refines_atomic_synStaging`** (refuted, not a result). The earlier staging refinement assumed `CalleesNoStagingSyn` alone. Witness: `pAliasSwap`. (`refuted_stage_inOrder_refines_atomic_noParamsInRange` shows that the alias-aware condition alone does not suffice either.)

```lean
-- lean/ToyCoalesce/Refuted.lean:290-292
theorem refuted_stage_inOrder_refines_atomic_synStaging :
    ¬ ∀ (ms : MoveSem) (Q : Prog), CalleesNoStagingSyn Q →
      Refines ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := …
```

**`refuted_stage_inOrder_behEq_atomic_synStaging`** (refuted, not a result). The earlier behavioural-equivalence form assumed `CalleesNoStagingSyn` and `LocalsInRange`. Witness: `pAliasSwap`.

```lean
-- lean/ToyCoalesce/Refuted.lean:298-300
theorem refuted_stage_inOrder_behEq_atomic_synStaging :
    ¬ ∀ (ms : MoveSem) (Q : Prog), CalleesNoStagingSyn Q → LocalsInRange Q →
      BehEq ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := …
```

**`refuted_stage_coalesce_refines_inOrder_noCallCheck_synStaging`** (refuted, not a result). The earlier staged pipeline used `ForestWFNoCallCheck`, `NoStagingNeededSyn` and `CalleesNoStagingSyn`. Witness: `pAliasCoalSwap` (`cex_pipeline_inPlaceCall_alias`), which also satisfies `ForestWF` and `ParamsInRange`; `pOobCall` is a second, independent witness (`cex_coalesce_needs_callsInBounds`; it has no callee, so the syntactic and alias-aware staging conditions coincide on it).

```lean
-- lean/ToyCoalesce/Refuted.lean:333-337
theorem refuted_stage_coalesce_refines_inOrder_noCallCheck_synStaging :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ → NoStagingNeededSyn P →
      CalleesNoStagingSyn (coalesce μ P) →
      Refines ⟨ms, .inOrder⟩ (stage (coalesce μ P)) ⟨ms, .inOrder⟩ P := by …
```

**`refuted_coalesce_refines_inOrder_noCallCheck_synStaging`** (refuted, not a result). The earlier no-overlap pipeline (which also assumed `NoStagingNeededSyn P`) used the same earlier definitions. Witness: `pAliasCoalSwap`.

```lean
-- lean/ToyCoalesce/Refuted.lean:345-349
theorem refuted_coalesce_refines_inOrder_noCallCheck_synStaging :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ → NoStagingNeededSyn P →
      NoStagingNeededSyn (coalesce μ P) →
      Refines ⟨ms, .inOrder⟩ (coalesce μ P) ⟨ms, .inOrder⟩ P := by …
```

**`refuted_stage_inOrder_refines_atomic_noParamsInRange`** (refuted, not a result). Staging refinement under the alias-aware `CalleesNoStaging` alone, without `ParamsInRange`, is false. Witness: `pStageOobPrm` (`cex_stage_refines_needs_paramsInRange`), whose callee parameter does not exist and receives the index of a staging temporary.

```lean
-- lean/ToyCoalesce/Refuted.lean:357-359
theorem refuted_stage_inOrder_refines_atomic_noParamsInRange :
    ¬ ∀ (ms : MoveSem) (Q : Prog), CalleesNoStaging Q →
      Refines ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q := …
```

## Evidence

Basis for every theorem below: execution (Lean kernel check). Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib; `lake build` of `lean/` succeeds with no `sorry`. The axiom audit (`Lean.collectAxioms`, recorded in `audit/axioms.json`) covers all 2437 non-internal declarations of the library (including generated equation lemmas); 0 of them depend on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. The statement hash is the SHA-256 of the Lean `repr` of the declaration's type; the closure hash is the SHA-256 of the sorted `name : type := value` texts of every package-local constant reachable from the statement (theorem bodies excluded), as recorded in `audit/statements.json` and recomputed by `support/revalidate.py`.

Where the main results are proved: the statements of the main theorems are in the proof modules `PfObs`, `PfInPlace`, `PfLicensed`, `PfUF`, `PfStage`, `PfCoalesce`, `PfPolicy` and `PfCompose` (quoted with their file and line range in each card); the definitions they mention are in `Basic`, `Upgrade`, `ObsAnalysis`, `Merge`, `Staging` and `VC`. Shared proof lemmas are in `Infra` and `Inv`. The proofs are simulations between runs of the interpreter, relating states statement by statement and using the access log of the source run for the dynamic conditions.

### Main results (card `lean` fields)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Coalesce.upgrade_outcome_eq_moveAsCopy` | `Quot.sound`, `propext` | `64774215183a62b360af0b9aba645aea1032bd7846587f008f2ad70fe2541d98` | `59945b4342b909d2e270f5b6eb9126ad44e1bde7b450e101ec257471942f33f2` |
| `Toy.Coalesce.upgrade_moveDeinit_outcome_eq_iff_noReadBeforeReinit` | `Classical.choice`, `Quot.sound`, `propext` | `d69e420a041d3a79d7c15f92a2024adf93c7f3d3ecf718c1e71de5aa752c2a36` | `f26210d328ca97896b96debe16b285ba0089a4a61d110c0b90a0a8f09018603d` |
| `Toy.Coalesce.upgrade_moveDeinit_refines_of_noReadBeforeReinit` | `Classical.choice`, `Quot.sound`, `propext` | `6eed17937729d15984efa3e4490869e232c2ba6fd2d5c86df2349641aff73352` | `da01f7e5da2b568e15a8489acf388711fa3d4868dea5f74216b56ccd4ecdd147` |
| `Toy.Coalesce.upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_paramNotAddrTaken` | `Classical.choice`, `Quot.sound`, `propext` | `e6dc29da9bf7a4b02ea19b65dffbe64449251db37006819a9c0b6d506596408d` | `0ecdf1dad38be2f6e36c55e04cba46ab947151fdfde74888aa19a8f24afa9f0d` |
| `Toy.Coalesce.upgrade_outcome_eq_moveInPlaceCall_of_not_call` | `Quot.sound`, `propext` | `11deda75534d9b103d56d4a1b6a4b036cfa9693eff2d8b7e100a48112512d0e0` | `59945b4342b909d2e270f5b6eb9126ad44e1bde7b450e101ec257471942f33f2` |
| `Toy.Coalesce.cex_upgrade_moveDeinit_dtorLoad` | `Classical.choice`, `Quot.sound`, `propext` | `207ddc7ae07512a8e14dfd9b0340a66156b26461b1c66228cb0262c2ed377f04` | `c251769021953629e6933b0664689cd8358622b669fcecc74a0579731f54c3df` |
| `Toy.Coalesce.pNoDtor_upgrade_refines` | `Classical.choice`, `Quot.sound`, `propext` | `3c0714587f152e9f99616a91f788c8552123589c0312c74978a05fffd538bc41` | `723fc4374f5a5703bdcd70ff6a91e49bfe184360e6c0ba8b1774a1b6bc592f23` |
| `Toy.Coalesce.cex_upgrade_moveInPlaceCall_calleeAvoids` | `Classical.choice`, `Quot.sound`, `propext` | `73760540ef58e849ce305bba5e620bb1f7217e99c48589b0c5fc01cd5d9d3738` | `0dd10e0870064c0cc0e24c2322b84d18bf19ad2669ffbe14e7e6fbc269893daa` |
| `Toy.Coalesce.cex_upgrade_moveInPlaceCall_noParamAddr` | `Classical.choice`, `Quot.sound`, `propext` | `f9ff22f723d2628b3c5e7bc11c4eab0f90a4b110a729ad57bec15bdec0154d75` | `0827f4d88b85abd2bb9b5e4b1ac760f3650ab33273f526e5f31b8a2e8b91bb31` |
| `Toy.Coalesce.cex_upgrade_moveInPlaceCall_noReadAfterCall` | `Classical.choice`, `Quot.sound`, `propext` | `5ecce5048791d281b9fbfc98345177748e92d9b7bb34bec8624b0399bf8b651a` | `d7f3ac60d3b1c4873d4e63ece1512b29c8a1b5591e59f8fd07553335e9bb2b37` |
| `Toy.Coalesce.cex_upgrade_callee_load_escaped` | `Classical.choice`, `Quot.sound`, `propext` | `3a1b03159c6b05f95b4405f73e3936a8bf83e68b65c2a7f03a4704f0f647ac9d` | `ae6d3b2612508d2b8147ab25c68f157b5026a102418a7a4ac764eb7ec7f2e43c` |
| `Toy.Coalesce.cex_inPlaceCall_param_addrTaken_in_caller` | `Classical.choice`, `Quot.sound`, `propext` | `0b58c8bcfcd1e881c7c43a5666b3eeb42a876cdb24d9a107e37d8c8ed519ce39` | `e727eda11b176ad246d0d58a8b11e0e13e308385e429a1ad0eb44670c8b00be2` |
| `Toy.Coalesce.cex_inPlaceCall_param_conflict` | `Classical.choice`, `Quot.sound`, `propext` | `3f9d9854cab08045889136ddd70aafe2cd610b3e1b6423d1397f268c2d1eb5a3` | `688e14563b5540244a3a2c1abc7d5c98f68a3ff011780e0329f6f229ed663ed8` |
| `Toy.Coalesce.moveDeinit_moveInPlaceCall_upgrades_incomparable` | `Classical.choice`, `Quot.sound`, `propext` | `4a4403abb2fc2d9bcd848340c1672b2fbd3d58f43dc96e1935e006b0a487c97b` | `09cb5c34ab25fa566ec091278c45997a3f01f56d7d3c09bbe9dc942062f46e01` |
| `Toy.Coalesce.checkObs_eq_true_iff` | `Quot.sound`, `propext` | `36b3b16296e4417e192dd038130e34d78731f77924e94f4efe2051b373379efa` | `82a43f504853f633eb05296b133a370467bdd8a9f2c07e6b9192084ad7737cc6` |
| `Toy.Coalesce.obsAnalysis_least_cert` | `Quot.sound`, `propext` | `b8c6cd76d416d38ca03a289dcfd2188e657dcdb2b5fdbe920245bd9abe1f1e0a` | `1be1024f793dc9590a005cd412dbc7f965b7af198117850cf57b02f9104e6e07` |
| `Toy.Coalesce.noReadBeforeReinit_of_obsCert` | `Classical.choice`, `Quot.sound`, `propext` | `95725b0084d29bdf30f966b54c720dbd6405420d143b5832ff4a9f4992a38ec0` | `9e8f47c5c5e79966cc044c0fe1595fa8580b0d7baea9b08ccffa2fcdd57d6109` |
| `Toy.Coalesce.upgrade_refines_of_obsCert_licensed` | `Classical.choice`, `Quot.sound`, `propext` | `f001488ad6df2ef7d3fc8eef0a3a594dcc1f9a8e2c4fbf0233756261ba3e386c` | `8cd6e0764bbc26096e4dc517e060774e34e43d78b72637bf523001987863f676` |
| `Toy.Coalesce.cex_obsCertBodyOnly_licenses_dtorLoad` | `Classical.choice`, `Quot.sound`, `propext` | `9b67431b0d9f5b27d56b6cd3d69e233843122f839314a2718394d3f60b9fcf23` | `cc894c6be72b74866c51787cd507aba4b58bb2589b834b681b18ecba144b75dc` |
| `Toy.Coalesce.coalesce_single_refines_of_noValueClobber_of_lexDisjoint_addrTaken` | `Classical.choice`, `Quot.sound`, `propext` | `0f19a7cc8ca29de789206d41365d4fc9f505998af113c34bbc890edc205bdfbb` | `978e41d75185c1d0036d745a589434217551368ad2405dc21ce6f81dc453964c` |
| `Toy.Coalesce.cex_coalesce_single_addrTaken_lexOverlap` | `Classical.choice`, `Quot.sound`, `propext` | `ab9f0571feb439c1a0e584f7de206844d9f66f46f540125fefb80efde8c93e33` | `2f4476a3aacb91f6b9523eb82c015ae8d10be7a9c8f440d33d749f5d364432db` |
| `Toy.Coalesce.cex_coalesce_single_valueClobber` | `Classical.choice`, `Quot.sound`, `propext` | `3e34564a6c6b440ae42a0ca6eeef7bf6f75d6862a89031765c1053866367a10a` | `ef63ba94f7003321452b9b10c2c57a320edfb78d7ce1063fbd63b9e678d01a09` |
| `Toy.Coalesce.coalesce_single_refines_addrTaken_child_only` | `Classical.choice`, `Quot.sound`, `propext` | `b57090cdc47f04b83279ba29abaef1929d31b2d2e95404a3a77a6e6c0233b690` | `8e3377dbbeb9e6bc2765ab417d8a5955e79ccfa8c26cf60ac785aedd65e2464f` |
| `Toy.Coalesce.coalesce_refines_of_noValueClobber_of_classAddrDisjoint` | `Classical.choice`, `Quot.sound`, `propext` | `cffee09e646df92638859128e5a2112131e29c6889bb565f526fbbe50724bc0b` | `326aca8f3d606da137cce873e97eceb78365147ed4ce0f0ed4f07afcf9476fb9` |
| `Toy.Coalesce.classAddrDisjoint_of_classAddrDisjointW` | `propext` | `d3f8812c393eb9cb0357f249b4cba2f2d11d4201c771d2c144e41e744681768e` | `440488956aba500d971d97b1ceb42e946d9f233c9d87687b9ea25f98e3c7958d` |
| `Toy.Coalesce.cex_edgeAddrCheck_does_not_compose` | `Classical.choice`, `Quot.sound`, `propext` | `f28633a115b36496688889a217c01f73289bdc73a978002f1a3794acb6b66582` | `a4340f09802a7421bfe914b227ed021f7cbe5482732b305b7a597aa1dcf34e1e` |
| `Toy.Coalesce.cex_rootAddrCheck_insufficient_siblings` | `Classical.choice`, `Quot.sound`, `propext` | `35c154900558ee3e159b5f0d7e0bf98463a11e50f19ca65680538573f71b98e5` | `2145f27b1f5fe0e8e210d1ffcecb03da14669ce4487b61f247d184c6caef1515` |
| `Toy.Coalesce.ufCheck_eq_true_iff_classAddrDisjointW` | `Classical.choice`, `Quot.sound`, `propext` | `4cf02f6639fb7539e1c245404098fef521ea895d699c907b91e7d8a86778e31f` | `34a184258b2a270f0907ba9626abb0257cca8827eec08110382d554066dd0b25` |
| `Toy.Coalesce.policySound_of_lexical_for_addrTaken` | `Classical.choice`, `Quot.sound`, `propext` | `f776d324f7bb0e968ce8bfa8d3e732e708e96cae97ff56bb464361a7f8d4b58d` | `950822f887f0cd80ba5717cc3b6fe6fc9aac876600581df334bf05593b1d2cd1` |
| `Toy.Coalesce.not_policySound_of_precise_for_addrTaken` | `Classical.choice`, `Quot.sound`, `propext` | `23fbdaf10629d424c6f61c1d3934751e0651ae935a5706e7a24625aacd831140` | `950822f887f0cd80ba5717cc3b6fe6fc9aac876600581df334bf05593b1d2cd1` |
| `Toy.Coalesce.policySound_iff` | `Classical.choice`, `Quot.sound`, `propext` | `36f21c97e96c30545a2ce1f9f2810dc38552cb48dcf7a5cf7685ed4321a2fdc9` | `950822f887f0cd80ba5717cc3b6fe6fc9aac876600581df334bf05593b1d2cd1` |
| `Toy.Coalesce.cex_policy_precise_for_addrTaken` | `Classical.choice`, `Quot.sound`, `propext` | `69122b8d9009b0ece9bac5868629239c02f6a0ea1f62152778df81436f790b42` | `715a6f4c411a934e739154fe95f59a30391aaa0fb5adabb654f87e8379674573` |
| `Toy.Coalesce.outcome_inOrder_eq_atomic_of_noStagingNeeded` | `Classical.choice`, `Quot.sound`, `propext` | `31f754c4782c32dd3207eef9d57d29afd37b38e4f4dceabfc8854013734eb22a` | `41121b6b3bb4185c53a6cb7be123fd2f411ad2be3a3a081f60a34ffeffbcae3f` |
| `Toy.Coalesce.stage_inOrder_refines_atomic` | `Classical.choice`, `Quot.sound`, `propext` | `855220e663cdf18b404b951dd0feaad90933dba90d09a8bd12eb916bdfefa2fd` | `9b11751e50bc4185dcd30b7b97a2f6bbabcd0162297ebfbac5f37bae39050a78` |
| `Toy.Coalesce.stage_inOrder_behEq_atomic_of_localsInRange` | `Classical.choice`, `Quot.sound`, `propext` | `05b9ed58116f5ee8ec2ed54382f2bee37657f1346290cf38278632e7cbc77563` | `ee473bf2c83797fad4318367863075ec3fe674abb1ca66de0f249651b6045c38` |
| `Toy.Coalesce.stage_coalesce_refines_inOrder` | `Classical.choice`, `Quot.sound`, `propext` | `f3db8462abbe3d55f151a996b572d5d82122ddf1f447d84bbf3f83e42e347da7` | `ed1b61a26a47c329f14640f56c45f3f079c7b6b6a22d3db45a4e233b3feac797` |
| `Toy.Coalesce.coalesce_refines_inOrder_of_noStagingNeeded` | `Classical.choice`, `Quot.sound`, `propext` | `6197608c8de9213fb2281a0aada09ef8da467bd0fd2a406c2834a09388245ba3` | `c9e4d527f9f8f279753e450edc95c9b3d6774bc3b27bb7deb2129bf37c5e8bdd` |
| `Toy.Coalesce.cex_coalesce_without_staging_inOrder` | `Classical.choice`, `Quot.sound`, `propext` | `4d75bb7dad712065f5dac13272ac018acc4d1fb5dedd7edde05baa423f0b3ef6` | `7646f61a7c07e7e7b7b1fb27598549ee8d30496deebc2a37ac68a28eb94d1ca0` |
| `Toy.Coalesce.cex_recoalesce_staging_temp` | `Classical.choice`, `Quot.sound`, `propext` | `3ffb8f889fbf6102d084bbb14b3d2d9315c24093296fb25162fec6ef66ffae85` | `53ca5fa8b8e724e2d7de088d0696558757348442acff9186ef29c346e4c384df` |
| `Toy.Coalesce.vc_forward_addrFree_of_noValueClobber` | `Classical.choice`, `Quot.sound`, `propext` | `af2e86e6c7a85a09a026a22378dc7eed1c0a82bfb87f146d4b5d037923acb0b4` | `9973334466bdd49123fd2d7e5957ca628158f9e42d59ede9022c22bd4b4e1a25` |
| `Toy.Coalesce.vc_backward_addrFree_of_noValueClobber_of_ubFree` | `Classical.choice`, `Quot.sound`, `propext` | `c496f8aa1f02a80bb4f6de8710a18a21c5264e25b403ce0662893e90567b05c9` | `f4a56556997e1e99572e8b90b6bfb3513521c9b94c2f8201fe80cdc567636852` |
| `Toy.Coalesce.vc_forward_of_noValueClobber_of_classAddrDisjoint` | `Classical.choice`, `Quot.sound`, `propext` | `77ec1a95996274b40c01ef5b41beb551e10d94f946d6225a54c2c82b1b0dda7c` | `bf4a52d810d4c55bbc9f438e4bce77462aa0715d0a100fea491c7cfcc628a554` |
| `Toy.Coalesce.cex_vc_forward_addrPost_needs_classAddrDisjoint` | `Classical.choice`, `Quot.sound`, `propext` | `5e299462037fe94e40becc4e57a0006821be27353120d992f194de9d40de0aca` | `d0b02524000de56eb95a53106ab2f9dcd18856cc17bf347b45bb72ae86006167` |
| `Toy.Coalesce.cex_vc_forward_addrPost_precisePolicy` | `Classical.choice`, `Quot.sound`, `propext` | `8504fbf7b139cc1ed79b47b1bd05c508787301cd7fee7236e22e2de33b6745ee` | `6d34a5aa200e54f2463410963ef3bd74f880c804679e284b2a2ff097d18ada1c` |
| `Toy.Coalesce.cex_vc_forward_addrFree_needs_noValueClobber` | `Classical.choice`, `Quot.sound`, `propext` | `549e4ecb81fa2627b0aa9cf96903e72d0c0558a3ef17cb5480d28c3fc38a16e8` | `bd7f2275cb0d1ce8e2a76e6cb1c542bb8afb3f18b374e16a37dbc78b6c300574` |
| `Toy.Coalesce.cex_vc_backward_needs_ubFree` | `Classical.choice`, `Quot.sound`, `propext` | `fd7c199f7231276de2558d51f763013b2bda67e212915985725f2e27e5403212` | `a7073cf1a0f93ff21a60e6200f8f447b33ce9795afd999f012af866b1acd9ce4` |
| `Toy.Coalesce.cex_vc_backward_needs_noValueClobber` | `Classical.choice`, `Quot.sound`, `propext` | `5b8a39ec1b01a1757a87749e7ef3f0efa24d4b00ed132ac09b9aa7f547499e55` | `2fc0fcc5976d99ea9a3253be185b260db1d9ce95d7e99a788a181d692e77842f` |
| `Toy.Coalesce.cex_vc_backward_addrPost` | `Classical.choice`, `Quot.sound`, `propext` | `877b2fed620ccfdbbbcb56d5f7f926d55609f31bb09b79cd2c23c6307d064705` | `d7e7b7a0ca72a0137bb5e007af928f0f7e919574d5c408a03135f0fc18f8e011` |

### Non-vacuity witnesses, positive controls and tightness counterexamples

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Coalesce.ex_moveSem_outcomes` | `propext` | `deb343a4df56a8683d52773c7aff9714d5eb497dc80c6985897f07338ac95f30` | `652ec923f964401e7011e2c9c56eb414e14e52517b0a060e5390352d3a5a5fd8` |
| `Toy.Coalesce.nonvacuous_upgrade_moveDeinit_iff` | `propext` | `477a97e78192d2d3c7b626fe49c81b031f91518e9ebc7eec9e176718c59a8149` | `622ce171630a35f8a2f64be0738de8cb4c2d9e6d3edcbc36552173b94a426822` |
| `Toy.Coalesce.nonvacuous_upgrade_moveDeinit_refines` | `Quot.sound`, `propext` | `03c47dda2b7752b34057aafd0c2063cc4590af14dbb992277f669d86156e1d7f` | `50de4be6e9006f29f96d4021d8b20f1a5db834f559e3da647fefbc4d7d75a3f2` |
| `Toy.Coalesce.cex_upgrade_deinit_iff_lhs_overlap` | `propext` | `79da93eed8580e4839b34ebbbee783bfbb8961b9c7d1ee17d90f5c598224e632` | `ab80f0af98ace10ceec11f843cb70bef2797c6e9b55ce44522d9ae4335fd36f8` |
| `Toy.Coalesce.cex_upgrade_deinit_iff_source_ub` | `propext` | `48d24b511c84a3d1216b28ff742f1ded85e6e62ad70438b0095469e580a04dfb` | `97fa06ff0e43c8d7f3e68043686bade00bfc26aedc5d4e94a4c10c39bf933305` |
| `Toy.Coalesce.cex_upgrade_deinit_iff_bad_layout` | `propext` | `c760188da3bb5c92c7dda8e42e44d6abdf352ab49a2f1dc93e6e6a046b19e2a1` | `30936365dc15440303cd8e3bada746c9d45bad387ca3f7604861623602518e42` |
| `Toy.Coalesce.cex_upgrade_deinit_refines_needs_site` | `Classical.choice`, `Quot.sound`, `propext` | `f10868bee7ae1742f9161e32099fb25b756bc4ce3aff04845e987534dedf2503` | `6ecca90131ee0183f140a0fe7bf75f479d673f1acf370cb3010e1c2222557ade` |
| `Toy.Coalesce.nonvacuous_upgrade_moveInPlaceCall` | `Quot.sound`, `propext` | `b0b8c829fd44beded202182ffa6f971e06b8007f6cb0cca7a751767a44ca1b35` | `edf2c57d53b880a86bf1073657ecf951a021dec34286f22eedb968bfc9f0b245` |
| `Toy.Coalesce.nonvacuous_upgrade_outcome_eq_moveInPlaceCall_of_not_call` | `propext` | `eae209cec2a975cf21a83c645fdcb08e868550156788e9acfaedc128370b8a03` | `0f0385c7fe87026ea71fc9345372384cba399509203086e32575557c9ad2088d` |
| `Toy.Coalesce.cex_upgrade_inPlaceCall_call_site` | `propext` | `9116274c551ddcc44340450b5b659a6f5108ebfeea9719fa8965dff73a5c84d7` | `86265689f2409f38a4698c1da0849d0b427ed6879d3f5ea7b81f772c084f663d` |
| `Toy.Coalesce.ex_obsCert_pos` | `propext` | `8fa7fd2ac6e96c15bad108da1d57f7ad49889c01651a6f4ad298318997ad05af` | `df717ee2effb8658a6970f27cb283e297720e87a3e37db2dcd1d14eb00969897` |
| `Toy.Coalesce.nonvacuous_upgrade_refines_of_obsCert_licensed` | `propext` | `a146b910f404c92710beb2537b9442c99d9ff3a8449d5df1fe780a7bc5fb03f2` | `8b9fb3e581e62745c5a3ecd0b9c6c771366db8d707443d770c87c3edefd35e22` |
| `Toy.Coalesce.nonvacuous_upgrade_refines_of_obsCert_licensed_inPlaceCall` | `Quot.sound`, `propext` | `beb14ba2c43a91c1c4557b53f550f551a9cb4b1d10f6e5fc4cc87227ea0989b9` | `a0e28d5e7c7d555c6c7f2a170d3fc60e5873280cc45149332ab82deded1c4df1` |
| `Toy.Coalesce.cex_noRead_needs_obsCert` | `propext` | `f435f5163c48b893a1704394d6e7ccc93dda1f79b3d9ed8318ebf7cbf18231e2` | `a93b9a335b07142df8b79e23c3ab015007ff555c12ed1c60818aae3d99a43853` |
| `Toy.Coalesce.cex_licensed_needs_obsCert` | `Classical.choice`, `Quot.sound`, `propext` | `7e43ffbb389dd96efa89997fbcd8b24dde41128c8529bf90f4ff8da5b3d0d5a0` | `1b10e1a96cfc0e6a00b3be148f94109aaddd30c689a4ed549cd3d5b73a150e54` |
| `Toy.Coalesce.cex_noRead_needs_not_in_mask` | `propext` | `2fc03c0ed97d4507710bb6982ebea5acdf26d645cc53abe3a556d4caf49ed374` | `6c5e665419ca345e4c47b6902a11833d5fc5fe8735775b648aa0232786f662db` |
| `Toy.Coalesce.cex_licensed_needs_licensing` | `Classical.choice`, `Quot.sound`, `propext` | `3cae2f98b66df9a201226454fb577f091ea1e61adb50fd7f7c0758c4c4775230` | `8f05b68017005535e8d05d1d5219c366073c4ba95322fe78daed408b4479d260` |
| `Toy.Coalesce.obsAnalysis_rejects_dtorLoad` | `propext` | `9563ee3edab56e9bbb10c47a4e7ad9a5e4229a7c6c9a0b16391f8eded2d2a4da` | `1518b2a163b72308343ec2eb35115b86d8743a9362f8dd33ae732df5eb51753b` |
| `Toy.Coalesce.nonvacuous_coalesce_single` | `Quot.sound`, `propext` | `000ba8afe9b60ed59e4d55937e95eae16a8a88f80a41c62eca4368689ea6364b` | `50b453ba31abb83f047110ec499507d0b312ba65aadc5ad1b3738e127d932fdf` |
| `Toy.Coalesce.cex_coalesce_needs_forestWF` | `Quot.sound`, `propext` | `c44dece9c841c27e042af9f487877e2740e838e0adb701f510292cad888ad212` | `85c295f79857e0434ec399572a5a7c069301e89f731afbe63f604790b52c778a` |
| `Toy.Coalesce.cex_coalesce_needs_callsInBounds` | `Classical.choice`, `Quot.sound`, `propext` | `dd9729c313d31f941cd956f8f0bf47b2d42f372162d02580363ad7865c98ca1b` | `6812755da15949d8ddf131c0f8b30fac5827c8f60eaf85cd34794218cd968d81` |
| `Toy.Coalesce.nonvacuous_coalesce_refines_of_noValueClobber_of_classAddrDisjoint` | `Quot.sound`, `propext` | `fff0da8b23a21aa732636d686db72834e3af6050b146aa12fe27b19516c26321` | `6fd1a80a2f524c52b52b09a548fe617ec2944fc9ee22e736827989c91be92860` |
| `Toy.Coalesce.nonvacuous_classAddrDisjoint_of_classAddrDisjointW` | `Quot.sound`, `propext` | `50b5b8747d180bb4bd7ff32cbc8c205419f66e9d86e60f778996690e812e0cfb` | `64dc948647da13aa9b306beb37eb980915060579bf32c3a4473107f64e3f0b60` |
| `Toy.Coalesce.nonvacuous_ufCheck` | `Quot.sound`, `propext` | `80a25dc1b0568430527cc0510a53b4a56beb943b4c4460c8b0b7e71bf5c6b4c4` | `7c091dbfdaf2592fce8078191162ac39f81ad18bf7568121a22d7219472ae46e` |
| `Toy.Coalesce.cex_classAddrDisjoint_of_classAddrDisjointW_needs_h` | `Quot.sound`, `propext` | `022c7bdc75a0b3a137c265392e2757e65573ce94303c2d52fa6879338e1c1b7e` | `3c1bdd43b53dad0657b29b7690d8e6f5498c690e08342c52cb78af31394b422d` |
| `Toy.Coalesce.cex_ufCheck_needs_forestWF` | `Quot.sound`, `propext` | `9f5a80b76785daf97594c6526fe2269a5583052a607674c0edd420b3571d72ec` | `49637a4a232b76805d2d68ff8839048a2da762b2028e5c90518602f615f4f67d` |
| `Toy.Coalesce.policy_mixed_accepts_pPreciseOk` | `Classical.choice`, `Quot.sound`, `propext` | `e34bea07d1e3cd82a84d63152fa771ba45e7c4f1da8598edd4efa7f586379a70` | `b5747028a5c31d83e8e3350bda9c0a8fc7cd55de030f54dfe4adc85a2bcbaea5` |
| `Toy.Coalesce.nonvacuous_staging` | `propext` | `8220f48ea5bb0837a71a1af84d76fa66fe0b2c16976a46a1785fb9458ac5bc32` | `df917d6a13889e38364bba7b18e12f544b45310f0a9d7a91d853814ec9335fe0` |
| `Toy.Coalesce.cex_inOrder_eq_atomic_needs_noStaging` | `propext` | `66385245385463be424e95d4b4cd863e29299444c05318073114798f6b7367fc` | `92fb014219c54a9f9a80e8b24e57b77e1677a199db250f354e61455d09bb3bee` |
| `Toy.Coalesce.cex_stage_needs_calleesNoStaging` | `Classical.choice`, `Quot.sound`, `propext` | `87c9ac464897f4a3957aaf605ab569eb409a152ebac362fe29a734af43ab9f55` | `da1afd448201ecd2e213050e792a90f36bb32efa8aab7eb76249b47086bb2fa3` |
| `Toy.Coalesce.cex_stage_refines_needs_paramsInRange` | `Quot.sound`, `propext` | `9e57f013d5ef5a948ac59274eb13e4e11c3439a1a6e80e2aaa693cb802a93250` | `436ab9a3495e30fea4042011b29585e86eac2e3dce755558dccdf71e65ccc5a8` |
| `Toy.Coalesce.cex_stage_behEq_needs_localsInRange` | `Classical.choice`, `Quot.sound`, `propext` | `f3e8a4afb063130d815e71da551fa65cd5b9a9b937471065c6defa2498ba87d4` | `7baf4315c3621f56ae28c1dbae742c53c2b55a0df3c55ac43a83d803d592c58e` |
| `Toy.Coalesce.stage_coalesce_pSwap` | `Classical.choice`, `Quot.sound`, `propext` | `5f4fc49ca5d8ad4e957f3a1670def7497ce9b27390fec92b85404c30353dc64d` | `d314aaa209349bb7c678a6fd6a910923901d4b3d3a52de850fdfbf64e7e02492` |
| `Toy.Coalesce.nonvacuous_coalesce_refines_inOrder_of_noStagingNeeded` | `Quot.sound`, `propext` | `69e5328ca03a31f9419ba673d9a94f80069c859489a1aa794f4065fbd4b9def5` | `5db323916e39795460c1ab29d8d51dbb97a3741e8181022bad34e857b6d0a3db` |
| `Toy.Coalesce.cex_pipeline_needs_noValueClobber` | `Classical.choice`, `Quot.sound`, `propext` | `d9d2794f64d00d92256a069c720a5c6cc578eb8fa0fc7508769b05c8e3de7eb5` | `6e79029587884f1b0096cb8965d693e662a1bc6226be5f340dd98430a015e3cd` |
| `Toy.Coalesce.cex_pipeline_needs_classAddrDisjoint` | `Classical.choice`, `Quot.sound`, `propext` | `e9095885a8a34dafa1ae828bf5a316cdf20809f63122db3d393683fe27676fff` | `f68ed35cb6d73913e3f004e148190d913258a4b5bb7fadff3d92cc66b71fa543` |
| `Toy.Coalesce.cex_pipeline_needs_noStagingNeeded` | `Quot.sound`, `propext` | `d70d2178a219ca6f9c28fd94c02e05f3423b7ede136781769529d10617d72b83` | `3f137883bbb70b1aeb6daf6a6b8feec4ea82b20e374da0d73d58799038273087` |
| `Toy.Coalesce.cex_pipeline_needs_calleesNoStaging` | `Classical.choice`, `Quot.sound`, `propext` | `7f7740b659ac5cd5e80705d5044172a69df4cc61c02aaebdf8d77a1f113f4893` | `e4f9d90b08a62fd0c4dfc061548446c70bc990187d99e59dc62ffecb48921fc1` |
| `Toy.Coalesce.cex_pipeline_needs_paramsInRange` | `Classical.choice`, `Quot.sound`, `propext` | `ca8b0266329a8156b6f726f8b38a12ef95293b40fedf69a1e2b049b47f7300ef` | `64a716a878559471c5ed8c7b8ebd4c3ca29cb965f92abb0918ad8032b993dc25` |
| `Toy.Coalesce.nonvacuous_vc_p3x` | `Classical.choice`, `Quot.sound`, `propext` | `e3e476d3b3ebb9954d4e766964b0603d74cf09820a307c1246846554866f2f8b` | `c9fe3f982da4e320724d39387e98745c7afb0e67fb53136f9ecc6662fa4fec96` |
| `Toy.Coalesce.vc_forward_addrFree_p3` | `Classical.choice`, `Quot.sound`, `propext` | `a444662011c2462a4d9e0a7aa1597721423ef9ee0a7c0175d85674b1bf16ee4a` | `e15faf37aad36eaf32591e29c81ab8778e1bcaff7828b3ecd109013854a2f69b` |
| `Toy.Coalesce.cex_vc_backward_needs_forestWF` | `Classical.choice`, `Quot.sound`, `propext` | `4adf8c0b26ecdeff69e7921025003b955330f0ba4fe9c22c6f0e1c5b48bab339` | `fce839be05388af06b3682f7430f4f3f9511fb06f989e34159180bab36547144` |
| `Toy.Coalesce.cex_vc_needs_valid` | `Classical.choice`, `Quot.sound`, `propext` | `2e7fc2e594b2bb6247508d0cd30a998404bf2698d9f142a1c0aa96b0bbbc8258` | `8f67bd9009f6a26540755dd120aa4052b2f30b350e9c1abb54978de241e71cef` |
| `Toy.Coalesce.nonvacuous_not_policySound_of_precise_for_addrTaken` | `Classical.choice`, `Quot.sound`, `propext` | `53cf1a1ad0febd4e089b480dd4c8a98bdc9a06ceb818590e5a825e330680f30a` | `950822f887f0cd80ba5717cc3b6fe6fc9aac876600581df334bf05593b1d2cd1` |
| `Toy.Coalesce.cex_not_policySound_of_precise_needs_h` | `Classical.choice`, `Quot.sound`, `propext` | `4442fce91b9f01f560d0d4ad81c0e38257ef4784b5e4132973e878f99172c82d` | `950822f887f0cd80ba5717cc3b6fe6fc9aac876600581df334bf05593b1d2cd1` |
| `Toy.Coalesce.cex_vc_forward_needs_noValueClobber_classAddrDisjoint` | `Classical.choice`, `Quot.sound`, `propext` | `439717bb0e904dd3a2020c502f169586f16e915a1401d72653252b8be3092849` | `035fac97570e66d57c3e161a44d0fd62d9d434551a31549e29301d9e906101b4` |
| `Toy.Coalesce.cex_vc_forward_needs_callsInBounds` | `Classical.choice`, `Quot.sound`, `propext` | `f225b661eb97c8d35a71bc4ad9085e94529aab13d4fc5de6657b1b345a85fe42` | `71b69895aafa7f2745ae7451a7b0a8f31fa0cd9a42993978b3361ee4529c4c61` |
| `Toy.Coalesce.pIPAfter_violates_noReadAfterCall` | `Classical.choice`, `Quot.sound`, `propext` | `00c97887dc0f13e87faa3b0be83351336ee9539265925db55510e5d830141702` | `fad03c5cca8b6076aaddb72bcb7c08f7a8ff57a01ba5b7796bb08d3406829f12` |
| `Toy.Coalesce.pIPStore_violates_calleeAvoids` | `Classical.choice`, `Quot.sound`, `propext` | `b8cd6c6aafc52b9ed6ef3470584a74f95b145c85c295f7ae379bebebb5a0a410` | `88a9f01ba6b934d74668085585ad207fe75144079178131fb7cc28a050d7ad7c` |

### Definitions and auxiliary declarations cited by name (`lean_names`)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Coalesce.A0` | none | `bbb57b8990b364a7466282e30bccf1cde417610a309549dd7a82d90c8dce4d2f` | `58986cc9f5bceff31fe09b1c829356cd793a55097f602bddc278665b7232efb0` |
| `Toy.Coalesce.AccKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Access` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.AccessPt` | `propext` | `d3095f329727f0881003bdfbf1392725b545da665ed5b704af97fdac8e17e8e3` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.AccessPtHalf` | `propext` | `d3095f329727f0881003bdfbf1392725b545da665ed5b704af97fdac8e17e8e3` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.AddrFree` | none | `01b560b504365edee7f4ab8824e8e8e0788db8f09bb283a0f11c3c1a3c4fb4c0` | `61ef84aa0e8e36e705d63b48b0b12581d64e5feadd750d736341cae23a6eb870` |
| `Toy.Coalesce.CallSite` | `propext` | `85fa0a22c83d9071a1dbd9c7172821b75aa54cdf9235da46122185448c884e8f` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Callee` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.CalleeAvoids` | none | `c9357aedc56dbddc9a97b45d7677ea372f01685bffc9a61925eaa87aae044df9` | `177afc4d508e31480b44d64760ab194e8f950725392f5b858cb3c8d1ed642a39` |
| `Toy.Coalesce.CalleesNoStaging` | `propext` | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.CalleesNoStagingSyn` | `propext` | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Disj` | none | `45431201b03db718edc66fdcc68d2c8d2e4c7a0e6fbc574f787b135943f6cc23` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.EVal` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Edge` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.EdgeAddrCheck` | `propext` | `fddc8c9e8bf0c2f34995e6312a2cc540bf71d398c4b86797284024238a9a91b3` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.Event` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Event.erase` | none | `2e9e476e86459a11beeb4594320767ca1ea6f66ca7b59a9f1e7b97a92d7a5860` | `61ef84aa0e8e36e705d63b48b0b12581d64e5feadd750d736341cae23a6eb870` |
| `Toy.Coalesce.Forest` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Forest.coalesceStmt` | `propext` | `918ffed4afc97aec57e0f7f47908c0aa2762fae607244bf08337a33e590ee151` | `e0454ee11d6091fb3a78d44833df0c273de4385fe0dfe91452f44f056b24fa5b` |
| `Toy.Coalesce.Forest.inClass` | none | `d0b1eecc891c207d2e951c7f07a6423da7fe291be9eb552cc58c3501295fab62` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.mapPlace` | none | `b125a7743ee4a62efd6e8ed77dc80bbb1e8ce8574f087d86c5dd30abebfd2a43` | `d72f2e7bd0f90fab56bf8fd18ff94a6228721879f254ca297ffcb39eca1166f5` |
| `Toy.Coalesce.Forest.offset` | none | `58b35628e3313803c6faf819159b18e5525c34d75c3250c8e1fba6620b48de33` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.parentOf` | none | `fd2ca8bc561182f89cef378bbfc0cde21d6ca50faa525ca9277c5073ada18ec6` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.resolve` | none | `b7b34ec70020d221f02401491170b3735b67e183b18f67d77acf545a836a1f7e` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.resolveF` | none | `d8995a282e058cc4f8f033557eb8d93711c230890d904764da57578f444536c2` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.root` | none | `58b35628e3313803c6faf819159b18e5525c34d75c3250c8e1fba6620b48de33` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.roots` | none | `d9e5148414a5feb331c62889a6899f43a4a516eb63c083f14c500163e9d270d0` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.sameClass` | none | `db65f720c0d2810b030e5de8b5df21093dbe03ec487ebc8034022d335e75e01a` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.tcell` | none | `d9ea1f1137d8adf7d0d1138b845bda8e55c12656eea74a14e6fd1bac3af08ad2` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Forest.windowsOverlap` | `propext` | `b9b53a3e10db07cd9aa280dd06e66f5227ce28566b2cbe79644f8f9302dca41f` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.ForestWFNoCallCheck` | `propext` | `fddc8c9e8bf0c2f34995e6312a2cc540bf71d398c4b86797284024238a9a91b3` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.InIv` | `propext` | `1a50e46be955da5ee28162b83798e482cf6bc3f1d0d279e86184b30d6e043019` | `293542176838ba5c498acef38d3b47c0c6090256823f23e013dd2422f1221326` |
| `Toy.Coalesce.InIvHalf` | `propext` | `1a50e46be955da5ee28162b83798e482cf6bc3f1d0d279e86184b30d6e043019` | `293542176838ba5c498acef38d3b47c0c6090256823f23e013dd2422f1221326` |
| `Toy.Coalesce.IvOverlap` | `propext` | `12f77a22801ba44f6aa270e4aec8151b986fc6b022f6409031748c3612f0fb21` | `293542176838ba5c498acef38d3b47c0c6090256823f23e013dd2422f1221326` |
| `Toy.Coalesce.IvOverlapHalf` | `propext` | `12f77a22801ba44f6aa270e4aec8151b986fc6b022f6409031748c3612f0fb21` | `293542176838ba5c498acef38d3b47c0c6090256823f23e013dd2422f1221326` |
| `Toy.Coalesce.Layout` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.LexLiveAt` | `propext` | `592326b9718deb195daf55494e1e5b3a506a7b59a342c3faabb1b9e681121ebb` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.LexOverlap` | `propext` | `d708865357f9baea3c198780ef0b7f7908aad6cfccd6bbc649e71e73b2800de7` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.LicensedNoParamAddr` | `propext` | `fa824af28212cf3053006a1eb6311f7f7dd9e222d4747a61784fad60f24d2a84` | `700a902d3373c472bb3fb9e8d1cd3913b3aee6e76dbef51fba2908e6d29bff64` |
| `Toy.Coalesce.LocalsInRange` | `propext` | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.MoveSem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.NeedsStaging` | `propext` | `9139550400d17e32273924a3ab257ae99df44079fce1834d68468c940712be08` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.NeedsStagingParam` | `propext` | `79bdea7318ed565ab320323c7da03f04e01fa5fbb940f3b29a86d0a6d368244c` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.NoReadBeforeReinit` | none | `d81a00fe0a256a8f40cedede6ba84206526e92ebfe010bafcebce7d623a81488` | `177afc4d508e31480b44d64760ab194e8f950725392f5b858cb3c8d1ed642a39` |
| `Toy.Coalesce.NoStagingNeeded` | `propext` | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.NoStagingNeededSyn` | `propext` | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.NoValueClobber` | none | `0b63d8eb88689378e499d010e56a19e8ff6062ee1b5cb661caf24407c2d580b8` | `9920e68c6b54ab469c915e3435a9dc2bb453602b4a11e51f1e3793b5821327f0` |
| `Toy.Coalesce.ObsCert` | `propext` | `aeaf56fb1ec521d82ff7c0c9e3386256a7ef36d0c27aa1e9bcd02f58ca72bf7b` | `8de80da1cb73231aa40f56a595b07ac5e22b3de7ab08708f13bc2601a1523675` |
| `Toy.Coalesce.ObsCertBodyOnly` | `propext` | `aeaf56fb1ec521d82ff7c0c9e3386256a7ef36d0c27aa1e9bcd02f58ca72bf7b` | `8de80da1cb73231aa40f56a595b07ac5e22b3de7ab08708f13bc2601a1523675` |
| `Toy.Coalesce.ObsMask` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Operand` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Operand.isLoad` | `propext` | `68ce2c00b93f3abd27afe16f84bc5b82b78580829711c9c42f9127c8f9c33bf8` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.len` | none | `a5aa2d38bf99f89e9cbc3bb941692538075a1a47a544597ed0d3e6cc71426600` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.locals` | none | `97176368e4f97a8e4e6e2351a149684652d9f737bee41871e33b5cb86512a567` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.mapPlaces` | none | `226d6950b245dfeb788d0e6f7225a34dca75686b0a855daa338c2d71d3124d1f` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.mayOverlap` | `propext` | `beea6e8e439783fa33b3eae781fd053ebc8cc5cea39682ae11e3d4d974035313` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.mayOverlapParam` | `propext` | `a7b3184c290d56e7c635b877eee8ddc403f40f8dbf8aa4a12d5bdb816191f26c` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.readsName` | `propext` | `6ae465ee5484ee6e3d1625cce87297fc5d23bcf80a330ec2a297bc728ac329eb` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Operand.takesAddr` | `propext` | `6ae465ee5484ee6e3d1625cce87297fc5d23bcf80a330ec2a297bc728ac329eb` | `c26584406cab73d6c8c3acf68846dcccca9e5d8a83066991372dc3572ffad906` |
| `Toy.Coalesce.Outcome` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.ParamsInRange` | none | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Place` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Place.paramSplit` | none | `9434a0cc13c0932e3077cadb472617e5f597ec77a4ff12ccf0df20bda7c5e51a` | `f5549ac3d655fd8313b2d805f927ef0da722856b9b55b2e0934e21b654d43beb` |
| `Toy.Coalesce.Place.proj` | none | `df3d9d5c5240442c81b800a6c0d6c8aa41615fe765e3a32e28ca17c7ef68817b` | `f5549ac3d655fd8313b2d805f927ef0da722856b9b55b2e0934e21b654d43beb` |
| `Toy.Coalesce.Place.whole` | none | `15052b5cc365946279db09af25c7709b1f2425087bfbd141fd0622bf377e04de` | `f5549ac3d655fd8313b2d805f927ef0da722856b9b55b2e0934e21b654d43beb` |
| `Toy.Coalesce.PolicyCheck` | `propext` | `6998eeaacf230324897502d7c5f142eadc5365eed6cedfbd258857917b891819` | `cb9f6509cc758c3ff237a0d04ae5e64bcb2706b7ac2f0573b6280e1a661f8bdf` |
| `Toy.Coalesce.PolicyCheckHalf` | `propext` | `6998eeaacf230324897502d7c5f142eadc5365eed6cedfbd258857917b891819` | `cb9f6509cc758c3ff237a0d04ae5e64bcb2706b7ac2f0573b6280e1a661f8bdf` |
| `Toy.Coalesce.PolicySoundWith` | `propext` | `133dfbdbc324fea0e8c01028260efc18b89529537bb303b0f07b0641b3f949b1` | `cb9f6509cc758c3ff237a0d04ae5e64bcb2706b7ac2f0573b6280e1a661f8bdf` |
| `Toy.Coalesce.Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Prog.code` | none | `4ddd436e6ebe2b6254efa4fa1853dbf8b842f91ce188b5380ef99ebac0ebe541` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Prog.nloc` | none | `502adbb22d94167564ade785d8073ac254b3cc8ebe5d811f734d97cbcbf94ed6` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Prog.size` | `propext` | `0d3291630a8a896dfa2bb2e4e3b13ec27257e14a68259f7560218d416aeffeb9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Prog.upgradeAt` | `propext` | `01df59c233d45e8df680650db85bf4a3c105da2294c7b7c1b5a9627aa15f4b02` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.RootAddrCheck` | `propext` | `fddc8c9e8bf0c2f34995e6312a2cc540bf71d398c4b86797284024238a9a91b3` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.Sem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.St` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.St.emit` | none | `0b05e649529c6fde2d1dca0fa81536af53c2c514d63adca09385828159d7a325` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.St.fail` | none | `23d62ce930fd4917465c08b270701be8e8ced1a62e9a97013bb972168860d074` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.St.init` | none | `8938ed716c343c84c1465f33d8e6b148760c7193bc6f55962bf8cc3592c5cbd6` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.St.logAcc` | none | `55c366f24bc4cc3d98d8885069d3c706fd516cc79f1c8ecd08491df114789434` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.St.wr` | none | `9f1685cf7598ddde0a438cba6d923e545e6f72d46037b5b69aef1c57371ac129` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.Status` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Stmt` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Stmt.calleeTouchesByName` | `propext` | `85f4d299387ec8f57f1a7a9cac45d77e33caf080eeb02654c7ff12fca81f3b01` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.escapesInPlace` | `propext` | `85f4d299387ec8f57f1a7a9cac45d77e33caf080eeb02654c7ff12fca81f3b01` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.kills` | `propext` | `85f4d299387ec8f57f1a7a9cac45d77e33caf080eeb02654c7ff12fca81f3b01` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.locals` | `propext` | `9892cd4ee95d2752d7878c05b89417710eb2a9f0cc957457bb46185210459038` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.mapPlaces` | none | `4bfd7ff14fab8b2a40c8cfa1a7c7e7286ac198ee0d773cbd0eed39726aa6b7c5` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.Stmt.mayRead` | `propext` | `7251b0352f5176e26a7180a9469325fac21c4ad859b85616a9f8b493aebbd86f` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.mayReadNoCall` | `propext` | `7251b0352f5176e26a7180a9469325fac21c4ad859b85616a9f8b493aebbd86f` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.operands` | `propext` | `76fa39c2f99f73faf2be148ac004cfaad383f5ea804985d44c990f77bceb1341` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.Stmt.readsByName` | `propext` | `7251b0352f5176e26a7180a9469325fac21c4ad859b85616a9f8b493aebbd86f` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Stmt.takesAddr` | `propext` | `5aaf27663da2e95ef0618d2bc10692492c504ee8ce4a2d45655b1c3947a48fc2` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.Stmt.upgradeCopy` | `propext` | `95b565a3c02fb14f44e5368e50dfb5020a5df26e992eaddf616107df95a23b3e` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.Stmt.writesByName` | `propext` | `7251b0352f5176e26a7180a9469325fac21c4ad859b85616a9f8b493aebbd86f` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.UFBlock` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.UpgradeSite` | `propext` | `b7e53dc5eee3558c83e10c29c00ff3ca8a3cfca3a5b1a91e97f7e96757e589d8` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Val` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Val.addr?` | `propext` | `882ce4d9869c88e47e22e3bd18cc1e00a50a9af4e146646ee9ebbffba1aff286` | `cf158e4ac683015383620f042b6c3e5696216513ef3e23b2bbf2b29329f21fa5` |
| `Toy.Coalesce.Val.obs` | none | `e1d0260cfbe5dc7f6dca86659ee971eb0f31c26b70cbcbdae5cb4102f858f36b` | `a18f4fa7aa40086ea09cce23b6dc9341069b0fea8380aa23230f9bbefac5ff40` |
| `Toy.Coalesce.Valid` | `propext` | `a86f327e44663c0857aee603149ac6022258797fd97b91487e185c101c1452d5` | `e7d16f09a5314450ffb96bef7738d6c06c97fb176d1502106a3a61da37b9cea1` |
| `Toy.Coalesce.WindowsDisjoint` | none | `fb79415127fbc580bcdf5cb0785082453ded960994c2555755947e426d6a81ef` | `f5549ac3d655fd8313b2d805f927ef0da722856b9b55b2e0934e21b654d43beb` |
| `Toy.Coalesce.afterUse` | none | `4ce1badb907856df34dac7e713c417839cddf7d84d9136790ecf19a271bcec25` | `820d0a8fea2a4d5eb52647b786c493fe4e7821953a640ba25277c46c968b06c4` |
| `Toy.Coalesce.allocate` | `propext` | `1b2ea16e1fb156668f29cfccb70397f7a94bcd5ffaf9594c799a26f647f8a2cd` | `be12429e1c90aeec564c389f650bc76255b44b639952c05e6359a6018f6579e4` |
| `Toy.Coalesce.aoTicks` | `propext` | `bad1259910cb326a433356d3c79f01717baed76056a2c292f4e9b4030fd27df3` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.calleeNoStaging` | `propext` | `8386d4ad71f218597d4cf0aaf624efe86dc8049204a19adbb4dceae9a5e66227` | `65cde15a34718a57fbd2830cb5a762a29504df49be722c8f1550078088a2ac86` |
| `Toy.Coalesce.cex_callee_reorder_rejected_by_policy` | `Classical.choice`, `Quot.sound`, `propext` | `e0e35ba1cf4273a68821a3249dd1c3f7241f6f7da642126e8308d9a152427473` | `9a2cbe51aef34ed5e879ef93245a816b77b2881b2bad985a56a9c72f4f948a41` |
| `Toy.Coalesce.clobberFreeAux` | none | `dd5366307ecc89dd2d97e28aeb26114f40bfe36843ae9841c44c688ac4d8bf22` | `9920e68c6b54ab469c915e3435a9dc2bb453602b4a11e51f1e3793b5821327f0` |
| `Toy.Coalesce.cmpAllFalse` | none | `398ee8ba635cbb9218ba6dcfcfd465d48a1fd04c3c2753f3db92bd3de397ec7a` | `61ef84aa0e8e36e705d63b48b0b12581d64e5feadd750d736341cae23a6eb870` |
| `Toy.Coalesce.cmpOp` | `propext` | `8606211d7555e443f21564b5d622f4cdefa38b885784a76d31f8e38c73c79b7d` | `e36938cefc6637ceb79c1fe181c0be0ea8b1c0f344c90bca3763087f68adebb2` |
| `Toy.Coalesce.deallocate` | `propext` | `1b2ea16e1fb156668f29cfccb70397f7a94bcd5ffaf9594c799a26f647f8a2cd` | `be12429e1c90aeec564c389f650bc76255b44b639952c05e6359a6018f6579e4` |
| `Toy.Coalesce.erasedIs` | none | `d533a2f054a861b4f5646b38deafa6b9a0eefb126e9f867379dabf5c0ba28d24` | `61ef84aa0e8e36e705d63b48b0b12581d64e5feadd750d736341cae23a6eb870` |
| `Toy.Coalesce.evalOp` | `propext` | `dfd5f564c8d25afd73082c0406a63a8d090209687d6740b3d334597592e99a41` | `ec79a6c109dac52f249a88c17de3c105149884382d498d4a7c725eb36d829280` |
| `Toy.Coalesce.evalOp_move_eq_copy` | `propext` | `d0b3cdac5e3a3e60e3b9dddfda749b774f12d0f7802126a52fb2bf66337baf97` | `001c0a8b0bc24899c93062cf924065d111daad215fcb7e2d3b00aaee80f9ae8d` |
| `Toy.Coalesce.evalOps` | `propext` | `4d3c38797a445cab6c9d13203e49104bea1e52d8ad2c730c66893edbd86909d9` | `ec79a6c109dac52f249a88c17de3c105149884382d498d4a7c725eb36d829280` |
| `Toy.Coalesce.ex_windowsDisjoint_empty_interior` | none | `8023aa9140595e86eada06b370a92a51d01531de55959865989f532f41d7be52` | `7165304cb662dc0d840da19c38432e96d3777ec48dd039570425365762ce0ef2` |
| `Toy.Coalesce.execBasic` | `propext` | `014def7a015fa1aae3ba3086502af3789f98595a788455cb2ab2b84a9a10544f` | `c80f5debf79ad26250abb72e6529dfcc44e685d7255a183824c006c9f1517194` |
| `Toy.Coalesce.execCallee` | `propext` | `1aa93177d195568c317a352de1de2de1da822bf5c2e1150d51393e1bb332fbcf` | `c80f5debf79ad26250abb72e6529dfcc44e685d7255a183824c006c9f1517194` |
| `Toy.Coalesce.execStmt` | `propext` | `014def7a015fa1aae3ba3086502af3789f98595a788455cb2ab2b84a9a10544f` | `c80f5debf79ad26250abb72e6529dfcc44e685d7255a183824c006c9f1517194` |
| `Toy.Coalesce.execTop` | `propext` | `014def7a015fa1aae3ba3086502af3789f98595a788455cb2ab2b84a9a10544f` | `c80f5debf79ad26250abb72e6529dfcc44e685d7255a183824c006c9f1517194` |
| `Toy.Coalesce.firstTouchNotRead` | none | `3b82d8f850f9daa2e836fc71fafa46a0a9002710cd2ec1e178d55c1c9fbd429b` | `820d0a8fea2a4d5eb52647b786c493fe4e7821953a640ba25277c46c968b06c4` |
| `Toy.Coalesce.layoutOK` | `propext` | `2b538f0a5a8999c5b41b1e2e5f79888ae5bc32760baf20b63e8e8890364326e5` | `e7da71b65329f048957876c2a56068a4039312beac4bf3dee4dbe9f541f090ec` |
| `Toy.Coalesce.lexLiveBefore` | `propext` | `592326b9718deb195daf55494e1e5b3a506a7b59a342c3faabb1b9e681121ebb` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.liveOthers` | none | `5c188a3bfa247c446e1c7945e36ac55b67b972bb47c1b1444a353a79dbbcc5c2` | `be12429e1c90aeec564c389f650bc76255b44b639952c05e6359a6018f6579e4` |
| `Toy.Coalesce.modifyAt` | none | `3d4ba19da83e259de91a0830f313f1ab33f57490987942636aaf1527db590c2e` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.nubNat` | none | `561c24b550f373db40946508681dc775e868caa7c87d5ef9967c73029d6083da` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.obsBodyOnly` | `propext` | `fcec0472b5428133d99bb26ce79c7aa35d53ad74f483a4d39495d613e5fdcdf2` | `8de80da1cb73231aa40f56a595b07ac5e22b3de7ab08708f13bc2601a1523675` |
| `Toy.Coalesce.obsFrom` | `propext` | `9abeb84ef492b2c211a3290d2e9c54278fa60005f5a21135390fca4ba51731cc` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.outcome` | `propext` | `52ade8ba4a8b51d0ec158fddb485c6e1c7549ea79b9e3482b2accc3cd71d6440` | `5b27d1fd69068602bf6c85d3cd5c0e44b712e8d11989d1e7eef4525442b1e9c6` |
| `Toy.Coalesce.pAliasCoalSwap` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pAliasSwap` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pCalleeCoalSwap` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pCalleeReorder` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pCalleeSwap` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pDtor` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pOobCall` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pOverlapSrc` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pReuseUB` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pSelf` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pSmallParent` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pStageOobPrm` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pSwapPrm` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pTmpClash` | `propext` | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.qx` | none | `08c424769f1ad8f881ec3c1caf14cbf8943086094d78701c80e67125e7a294af` | `f5549ac3d655fd8313b2d805f927ef0da722856b9b55b2e0934e21b654d43beb` |
| `Toy.Coalesce.readCells` | none | `7464891efad0bd109388759cd59445fb6ad107d93d1a6527ec5b424b3943e139` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.refuted_coalesce_refines_inOrder_noCallCheck_synStaging` | `Classical.choice`, `Quot.sound`, `propext` | `fabc08c283aa558c2d22d014d0f5a25ac113b0d7b616a8a8cbe86b3ba1c57d29` | `4b7eb192802ec6de3d4ea1f8ac7b9fe0a9d4c27fcab2c54cbe0ce3980f61e2a3` |
| `Toy.Coalesce.refuted_coalesce_refines_noCallCheck` | `Classical.choice`, `Quot.sound`, `propext` | `b44e01be0670078143811175667392aa89565fb2f1a9a8882761e189ea18f44f` | `c42522e375316f25ef07af13a0a26d8c59304ca25a6e9d86f5b1d38f62a174e1` |
| `Toy.Coalesce.refuted_coalesce_single_refines_noCallCheck` | `Classical.choice`, `Quot.sound`, `propext` | `79627171bfbfebc939028e31b2d5e0de5828702352737752fd7792cd623dbea3` | `4eb6e0f5817d1de43fa7d5d40fa5cc6a9e701b66e6cfb906300a298c01a768ea` |
| `Toy.Coalesce.refuted_policySound_iff_noCallCheck_halfPoints` | `Classical.choice`, `Quot.sound`, `propext` | `f14a14118f8bc2dcd3d08db4952d22c24e8c1f2c2611665cf2fc4f864e800b7a` | `d687174cf758c07b91633d361e2ee8f426cbf4ca715855ccbec38e43d469ec7d` |
| `Toy.Coalesce.refuted_stage_coalesce_refines_inOrder_noCallCheck_synStaging` | `Classical.choice`, `Quot.sound`, `propext` | `d3a049d966220bdb31eeb4094c2abbedde7b73505bbe5581c7d5ca6610d7b831` | `9c67427037303eed26b0b0330959fc399ed1dd0187163bd530e19d32f8b72d14` |
| `Toy.Coalesce.refuted_stage_inOrder_refines_atomic_noParamsInRange` | `Quot.sound`, `propext` | `4322b110731f05e9189646703b7b37c0127e5afef1072118ab93148aaa6318a9` | `91d7f5d33b0e7b02a9e8a5a7a849bfd64097f47976ccea79702c8fb77888f81f` |
| `Toy.Coalesce.refuted_vc_forward_addrFree_noCallCheck` | `Classical.choice`, `Quot.sound`, `propext` | `d250b40543914b6e6ef5aaa9d32966bdb5cc86783abc31ac0f0177f3c29df8f0` | `b6ee0350a2d4d5adeb3743ee8a10232258ad7061c18693025cde2a5b856298e8` |
| `Toy.Coalesce.refuted_vc_forward_of_classAddrDisjoint_noCallCheck` | `Classical.choice`, `Quot.sound`, `propext` | `b88273adeec3bcf1f3ff78b5fc8bd3338138adb5091c99978d67a06efe8e40fc` | `9636b304545d2f61ee198380245c3d7d1418e0b9444695152b37cc2914c46b43` |
| `Toy.Coalesce.resetCells` | none | `499e4218d98486cc15f3452d7efeba9165e72baca1c40adb8f87d6973b8b687b` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.resolvePlace` | `propext` | `23b1d321a331c418e3d1ab10489dc3a82487f1d018cbf4716081781da400a4c2` | `be12429e1c90aeec564c389f650bc76255b44b639952c05e6359a6018f6579e4` |
| `Toy.Coalesce.run` | `propext` | `a85a4c85e1def4d4180d1b915919eb7f30887556d4a8e298bd283ccddb8a1634` | `c80f5debf79ad26250abb72e6529dfcc44e685d7255a183824c006c9f1517194` |
| `Toy.Coalesce.semC` | none | `afb99fe8077a715c331c4c074105603172eca598662a9fb83b00347d99efca11` | `c3e69c07fd969b7d5d43557204234cd923f708cbb34786023e9cb83a614f2a82` |
| `Toy.Coalesce.someCmpTrue` | none | `398ee8ba635cbb9218ba6dcfcfd465d48a1fd04c3c2753f3db92bd3de397ec7a` | `61ef84aa0e8e36e705d63b48b0b12581d64e5feadd750d736341cae23a6eb870` |
| `Toy.Coalesce.stageList` | `propext` | `e22d5c4f1e9690316883139ac63c1cd774a1acdd7a0b9c24d22f1aead6409c0a` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.stmtsNoStaging` | `propext` | `82df93e9da16a3b44bf88e26a4c177311aa8b893a1441d39dd8089cdfe0061e7` | `f4d4edd3535ca1d83f0260531a28382fe7f173d256c20206f3521fd34d6af7f5` |
| `Toy.Coalesce.ufInit` | `propext` | `0998a27cb7325724731a4f77e019b8263cf35bb776d3aad95b32883c7ab0db18` | `81be66c4ee158a74c658bdb9e6f76e01d13ff71c01b370a9b9c383e6f39db6ec` |
| `Toy.Coalesce.ufStep` | `propext` | `7cd7ec317c217b6efb8f5e79c0688a1689d180621c3eb51c5fbd506720297f68` | `abcf0e75b42fcd8a895b9e1dbe5996c612fdf9c00fbc3e5ff341f33fe55d4588` |
| `Toy.Coalesce.writeCells` | none | `23089636692d9614b6a281eeb3e8c5ebcdb1f26cd31e8867acb5ceb320f0c2cf` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.writeCellsK` | none | `4cb0a6fa63f643d2365a1ca604b4b94b56c3ca9b73b0700240c3035bea4b3608` | `cd5d69c46b304e63b3d7ee0deaa8e2bc035b8e5a7ddf543e53f5c7ff6137ba81` |
| `Toy.Coalesce.writeInOrder` | `propext` | `18c9562c6a162abd9990c3a413de372840a0b3ba23903ff754b4ebca29b2d5e5` | `ec79a6c109dac52f249a88c17de3c105149884382d498d4a7c725eb36d829280` |
| `Toy.Coalesce.Refines` | `propext` | `e6464542c4f348d4ef224dd42524e2e96d11e69c01352e28684035536e98ba2b` | `14e0c0f035004e0702055e62660d73da84f24854a8c568be1c5c2186dd06ee18` |
| `Toy.Coalesce.pNoDtor` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.AddrTaken` | `propext` | `8afa1f1f22713e797a1c8518be37cdad15f86ce840b4be109edd72a28e0be668` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.CalleeNoParamAddr` | `propext` | `416fe61ff2034d2c6610b2911de78014607209f0a7784845798a2882e0454c74` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Prog.fn` | `propext` | `d1e707bd3b7988c22e7e91af9c795068d65fd9915ad68d23194a307b1aa45d41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pIPOk` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pReuse` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.refuted_upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_noParamAddr` | `Classical.choice`, `Quot.sound`, `propext` | `696d8f0063f20322c7482e44293962ea6423a429d6c7f531333b6d9400b86898` | `530e1dfdce8c5da2767514d340e7144ae0f79c215c7b461b7d42c7a41171808b` |
| `Toy.Coalesce.A_eq03` | none | `bbb57b8990b364a7466282e30bccf1cde417610a309549dd7a82d90c8dce4d2f` | `58986cc9f5bceff31fe09b1c829356cd793a55097f602bddc278665b7232efb0` |
| `Toy.Coalesce.pCall` | none | `eeacd8ddf7668e5361f27aaf489b4e6ab20389f3ff7a66c7643e3a30be16dec0` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pIPAddr` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pIPAfter` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pIPLoad` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pIPStore` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pPrmConflict` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pPrmEscaped` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.AssignMode` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.semD` | none | `afb99fe8077a715c331c4c074105603172eca598662a9fb83b00347d99efca11` | `c3e69c07fd969b7d5d43557204234cd923f708cbb34786023e9cb83a614f2a82` |
| `Toy.Coalesce.semI` | none | `afb99fe8077a715c331c4c074105603172eca598662a9fb83b00347d99efca11` | `c3e69c07fd969b7d5d43557204234cd923f708cbb34786023e9cb83a614f2a82` |
| `Toy.Coalesce.checkObs` | `propext` | `d6431dda72fcfa448e56c6027948655ec564956c48281c1c143008ddfd65ee13` | `8de80da1cb73231aa40f56a595b07ac5e22b3de7ab08708f13bc2601a1523675` |
| `Toy.Coalesce.obsAnalysis` | `propext` | `fcec0472b5428133d99bb26ce79c7aa35d53ad74f483a4d39495d613e5fdcdf2` | `8de80da1cb73231aa40f56a595b07ac5e22b3de7ab08708f13bc2601a1523675` |
| `Toy.Coalesce.Licensed` | `propext` | `fa824af28212cf3053006a1eb6311f7f7dd9e222d4747a61784fad60f24d2a84` | `700a902d3373c472bb3fb9e8d1cd3913b3aee6e76dbef51fba2908e6d29bff64` |
| `Toy.Coalesce.cex_licensed_incomplete` | `Classical.choice`, `Quot.sound`, `propext` | `d68412eb6921b713a8564dc3e958f3bb349fffb5ee1fd8c107c50d6c67ec7028` | `dfc99f46aaf289f1bd4475177fee19db1f8d5fda7a2962250b037dc2783e8f26` |
| `Toy.Coalesce.pLoadOther` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.refuted_upgrade_refines_of_obsCert_licensed_noParamAddr` | `Classical.choice`, `Quot.sound`, `propext` | `11aa23b3a7974d114e16f8a8feb9df0a60118dbf8586e3507d29415cfb7c2311` | `cc4305a0bd1f673b7e1ba3e04ae122da9b3a7e846eb1dd54062eaf588b9c7fea` |
| `Toy.Coalesce.BehEq` | `propext` | `e6464542c4f348d4ef224dd42524e2e96d11e69c01352e28684035536e98ba2b` | `14e0c0f035004e0702055e62660d73da84f24854a8c568be1c5c2186dd06ee18` |
| `Toy.Coalesce.ForestWF` | `propext` | `fddc8c9e8bf0c2f34995e6312a2cc540bf71d398c4b86797284024238a9a91b3` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.NoValueClobberStmt` | `propext` | `a44fd826240ccbec40bd9539797379e1cae85604682547a22374ed0f2e222afa` | `9b5ae33329a801bbc3c6cc696edfb1de9059a2b3b1b16a4db3134d7b8edbb1d4` |
| `Toy.Coalesce.coalesce` | `propext` | `8bdc2fb1e28b3007878d07116aac79c3d9e347a8433713efb2a9f5a149d75dbd` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.p3x` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pUBRemoved` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.p3` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pClobber` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.single` | none | `75d2a8bed4e4e7f9570fa2d69829017b4f94be866735f21cb2874dbf66ad6fa8` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.ClassAddrDisjoint` | `propext` | `fddc8c9e8bf0c2f34995e6312a2cc540bf71d398c4b86797284024238a9a91b3` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.ClassAddrDisjointW` | `propext` | `fddc8c9e8bf0c2f34995e6312a2cc540bf71d398c4b86797284024238a9a91b3` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.pChainOk` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.μChain` | none | `a6bfcffa27559f2dfaad76c520e618b64e94ad5f986a2aa247f55fb2f843be79` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.Refines.trans` | `propext` | `470c56d1f70212143a6a5a12dd11493c4ee18ef29ca669816946cb5c303df971` | `0bf7b57b424af345f2a1954c5b73dad8581e22d9ffdf7f3a477a3bd685f591c5` |
| `Toy.Coalesce.pChain` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.pSib` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.μSib` | none | `a6bfcffa27559f2dfaad76c520e618b64e94ad5f986a2aa247f55fb2f843be79` | `c5c9ad9ebbdeb92016eceb6219173f913488e34e0bcacbdd8bcb5bfd496d4f90` |
| `Toy.Coalesce.ufCheck` | `propext` | `fc77cc62defaf85b456ee8f15733d2c1abaf19cf3b79824c6d5122e2448ed886` | `d836dcc934e6422d9af1496f614531ffa1125a89835b791310b4a0503b417d26` |
| `Toy.Coalesce.CallsInBounds` | `propext` | `12134405af9bab58b5f9aa70d8e0d49e0ccc80a4d10f84aa3cfd507bc130cc41` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.Notion` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.Policy` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Coalesce.PolicySound` | `propext` | `ff21082aa96826fda00b21f5c374c1965578d7586a99648792a9e6eea40091c0` | `f4f7511a2e99458b423a87f57e236b1600822747532d7913943c7443a0bdfe6e` |
| `Toy.Coalesce.pPreciseOk` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.refuted_policySound_mixed_halfPoints` | `Classical.choice`, `Quot.sound`, `propext` | `2975ae20ede3f70226b7190c725c7673bf4a9a54317c7d6c45b58e8e57dee699` | `05e104d9d11f4aebf2b20aef8099bd60a94312faf50d595c7ab67699f8ee03d6` |
| `Toy.Coalesce.refuted_policySound_of_lexical_noCallCheck_halfPoints` | `Classical.choice`, `Quot.sound`, `propext` | `fa737355acb3a777806795ee4a1b9074a2186d2b1739f653a501aac220dd9ce6` | `d687174cf758c07b91633d361e2ee8f426cbf4ca715855ccbec38e43d469ec7d` |
| `Toy.Coalesce.Beh` | `propext` | `6fd25d734a75007660a03634e43a868685b677738e143893a8323d175131f8eb` | `42be2b3b69bc2a6a316063bb16f2883ceafc946a95f9c8122b68c2d4c4f70316` |
| `Toy.Coalesce.cex_staging_inPlaceCall_alias` | `Quot.sound`, `propext` | `78ed5d298e6560a19647e689504920b713f1068d08d4871f6646f31503a1df03` | `424f79ac99680c466c177fac60b0a84eb715b091d3653c9ec39a237e9eccf31d` |
| `Toy.Coalesce.pSwap` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.refuted_outcome_inOrder_eq_atomic_synStaging` | `Quot.sound`, `propext` | `690b1e457cc637df7d9c4b4f8f75dc239d9a1e943faed7a14b0d1a2d45894b62` | `0f7398cf4f5383fde235abf412120d4e6d2b3f4d71b5863d7440c5bc360dc367` |
| `Toy.Coalesce.refuted_stage_inOrder_behEq_atomic_synStaging` | `Quot.sound`, `propext` | `4c64ee7fd19a47855825c125640088c0dd51a5461259685cf1564f1ad0c84c56` | `83a34c639a1eb98025c2128cedbaa116067f63e20cacad1e5a844e4ebf121ed3` |
| `Toy.Coalesce.refuted_stage_inOrder_refines_atomic_synStaging` | `Quot.sound`, `propext` | `6069bd34f72db30323907028f8f27b184de28a9c1846466e72d3703e63995216` | `0ef39646593817e6d715d3491bbd966be8ad624b709ea83cdedbb89a191a91ff` |
| `Toy.Coalesce.stage` | `propext` | `762f5a897c5a911a5f99fe15df4bf70059a13d97240f2607e9969a034cae4635` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.cex_pipeline_inPlaceCall_alias` | `Classical.choice`, `Quot.sound`, `propext` | `f9d7ca30a599dbc53fad2d41591d0fe1efcd63d87e1d2679a10060af05dcafbe` | `e9abb2487f2ffffd7c9fd9acfa1571669ff39c3a99f1312134f0a7764aa02d3b` |
| `Toy.Coalesce.noStagingNeeded_of_noStagingNeeded_coalesce` | `Classical.choice`, `Quot.sound`, `propext` | `e7ed22be444d5618eb6b2efdd567e8f37c97f3ac31766b0951d6e00b890727d1` | `3a70fe8738dacc6bb9ed0cf187d627b2366fcc020346a4713e4d2d8653c770bd` |
| `Toy.Coalesce.pSwapStaged` | `propext` | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.UBFree` | `propext` | `bc4c7afb0654d80f28babab1f3562d3a336348a9cc9775d66b0e8dd100e3cdbc` | `14e0c0f035004e0702055e62660d73da84f24854a8c568be1c5c2186dd06ee18` |
| `Toy.Coalesce.pBackHwf` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.valid_of_refines` | `propext` | `b991996585d4a33d83d4bf618fa60c8b667731a879ed39607205e6f2764efd17` | `4414a0dac30f1a124e93795726f085361a5b185f8f166a118a1b01db2ced07bf` |
| `Toy.Coalesce.pPrecise` | none | `18f8bf9eee5a824a01bafd739c3f3cb5d1a05d5234b1be7a91391346d37991e9` | `a9ae4fe2436d6d328f501c1bd972b267a714a8402d992bc681780c7b829e0a68` |
| `Toy.Coalesce.p3_outcome` | `Classical.choice`, `Quot.sound`, `propext` | `3f38a3a7efad903ae679b53e16e840b8dfd042a6628437f4476e6d45ff051682` | `326300d1321971647b9f015ec5820ad6dbafdcd710896f5889255d0a55cf1860` |
| `Toy.Coalesce.coalesce_pSwap_contains_overlap` | `propext` | `04aeadbc497d54237d9ab71f2392114fad8829c1b5c15ee27ed1ab1b61d64ffa` | `886ce8483d08d61ca26fbd1199bbed601a4cd5fd129b06983337c3fb9e18bba4` |
| `Toy.Coalesce.coalesce_pSwap_outcome_inOrder` | `Classical.choice`, `Quot.sound`, `propext` | `9dc6bb6f34812be3b8735b67834e54e27deb43f4c3bfec83adbca4e1a21a5e08` | `62e7d9fde289dac8b1ecd0359ea7da1a0084bcb6a72b3bf109aff1528642d490` |
| `Toy.Coalesce.not_policySoundWith_noCallCheck` | `Classical.choice`, `Quot.sound`, `propext` | `f2f2f76f9c4605a194e13612e620f1baa06cc956edc1374f62ea64cfde0deb6a` | `c4a84ea97cdfab68db416feb06a328ad1b3e3981589f275ed3e1d1ccdfb0bc44` |

### Primary sources

External sources were fetched on 2026-11-21: rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe `compiler/rustc_middle/src/mir/syntax.rs` (sha256 24450e48c164243648410aefa13dfe2faaf632c1681b418b0d0d0687495b6b39) and `compiler/rustc_mir_transform/src/dest_prop.rs` (sha256 c5ea1288ebdaf7cfbdc132f3d98ce3c878051bf3d8ec1be28096ba3f08c8973d); AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc `backend/Allocation.v` (sha256 0b1b9aca55b9058c44dcb1624b88781daa090c86d163b1f4a0eb4feaac718cc6). Bibliographic records of the cited papers were checked against their DOI metadata; their full texts were not inspected unless stated. The Lean release tag `v4.34.1` resolves to commit 5045d0056413266e57c625dcd7c365b10e377c52 of leanprover/lean4.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No other tool and no network access beyond the
toolchain download are needed.

Primary command, run from the package directory:

```text
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It then (1) runs
`lake build`; (2) checks that no Lean source contains `sorry`, `admit` or `native_decide` or
declares an `axiom`; (3) computes, with Lean's `collectAxioms`, the axioms of every declaration of
the library and checks that only `propext`, `Classical.choice` and `Quot.sound` occur; and (4) for
every Lean name referenced by `results.json` (fields `lean`, `lean_names`,
`nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` lists)
recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its
definition closure (the sorted `name : type := value` texts of every package-local constant
reachable from the statement, theorem bodies excluded) and compares them with
`audit/statements.json`. Exit status 0 means all four checks passed.

Manual alternative (build and print the axioms of the main results):

```text
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs
`#print axioms` on every main result of the cards. Each line of its output must list only
`propext`, `Classical.choice` and `Quot.sound` (or no axioms).
