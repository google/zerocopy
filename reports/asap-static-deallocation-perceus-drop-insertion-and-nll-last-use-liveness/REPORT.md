# Liveness-driven reclamation versus compositional translation: ASAP, Perceus, Lean 4 RC passes, safe-for-space closure conversion, and rustc NLL, drop and storage liveness

## Summary

- **Where liveness is computed matters more than which mechanism reclaims storage.** The systems examined split into four groups:
  - **Syntax-directed given free-variable sets:** Perceus elaboration over explicit control flow; flat closure conversion.
  - **Intraprocedural backward liveness with fixpoints at join points and loops:** Lean 4 `explicitRc`; Koka `Parc`; rustc `MaybeLiveLocals`, `MaybeRequiresStorage` and the drop-elaboration init/uninit dataflow.
  - **Interprocedural fixpoints over a mutually recursive declaration block:** Lean 4 `inferBorrow`; CertiRocq dead-parameter elimination.
  - **Whole-program, single compilation unit:** ASAP.

  Basis: source + documentation.
- **rustc keeps three liveness notions apart.**
  - *Borrow liveness* (NLL region liveness from "use-live" and "drop-live" points) decides only whether borrows type-check.
  - *Value drop timing* is lexical: MIR building schedules drops at scope exit; elaboration adds runtime **drop flags** where control-flow joins disagree on initialization.
  - *Storage* (`StorageLive`/`StorageDead`) is lexical too.

  No pass feeds NLL borrow ends into storage reuse. Basis: source + execution.
- **Measured on rustc 1.102.0-nightly with a 4096-byte non-`Copy` buffer, `size_of_val` of the future:**

  | Variant | Size |
  |---|---:|
  | Buffer borrowed and the borrow dead by NLL before `.await` | **4100 B** |
  | Buffer moved before `.await` without ever being borrowed | **4 B** |
  | Buffer confined to an inner block | **4 B** |
  | Borrowed, then moved with `drop(buf)` | still **4100 B** |
  | Same body as a movable coroutine | **2 B** |
  | Same body as a `static` (immovable) coroutine | **4098 B** |

  This is exactly the `!movable` branch of `locals_live_across_suspend_points`, which unions in `MaybeBorrowedLocals`, plus `MaybeRequiresStorage`, which "kill[s] locals that are fully moved and have not been borrowed". In ordinary stack frames at `opt-level=3`, two 4096-byte buffers share a slot only when the first is in a disjoint block: 4144 B frame versus 8240 B when both are in the same scope, whether the first was moved or only borrowed. Basis: execution + source.
- **Lean 4 v4.35.0 output on four small functions:**
  - inferred `@&xs` (borrowed) for a read-only traversal, with no `inc`/`dec` on `xs`;
  - `reset`/`reuse` for an in-place map;
  - no `inc xs` when a borrowed use precedes the consuming last use;
  - a per-branch `dec xs` at the entry of the arm where `xs` is dead.

  Basis: execution.
- **Felleisen's criterion (derived; not mechanized here).** Annotations that put explicit `drop`/`dup` (or last-use `move`) into the source term make the reclamation translation homomorphic on every construct, because these are λ1's own `drop`/`dup`, which Perceus's syntax-directed algorithm otherwise infers. The ingredients that remain non-local are:
  - (i) branch arms that consume different owned sets: these need either a typing rule requiring the arms to agree, or a runtime bit, like Rust's drop flags;
  - (ii) sharing (`dup`), which needs runtime counts or a static uniqueness discipline;
  - (iii) callee parameter modes (owned versus borrowed), which must be part of the callee's interface and are not inferred from its body;
  - (iv) self-borrowing suspended frames, where storage reuse is bounded by lexical storage markers.

## Applicability

- **Source subjects** (read at the pinned revisions in `REPORT.json`):
  - the Lean 4 compiler at a development revision;
  - rustc at a development revision;
  - Polonius;
  - CertiRocq's LambdaANF closure conversion and dead-parameter elimination;
  - Koka's Perceus implementation.
- **Executed subjects:**
  - Lean 4 **v4.35.0** (release commit pinned).
  - rustc **1.102.0-nightly** built from the pinned commit dated 2026-11-11.
- **Version-overlap checks.**
  - The rustc files that drive the probed behaviour are byte-identical between the executed and the source revision: `rustc_mir_dataflow/src/impls/storage_liveness.rs` and `borrowed_locals.rs`.
  - In `rustc_mir_transform/src/coroutine/layout.rs`, the function `locals_live_across_suspend_points` (lines 83–160) is the same; the differences are an identifier spelling (`MustNotSupend` → `MustNotSuspend`) and a new `pack` field.
  - `elaborate_drops.rs` differs by a single hunk, the `typing_env` computation (executed-pin lines 55–57). The `drop_style` match is the same at both revisions: lines 183–187 at the source pin, 185–189 at the executed pin.
  - Lean `Passes.lean` is identical between v4.35.0 and the source revision.
  - Lean `InferBorrow.lean` differs by 15 changed lines: a new `literalResult` ownership reason and a refactor of `collectLetValue`.
  - Lean `ExplicitRC.lean` differs by 267 changed lines. Its header contract ("performs a liveness analysis, inserting decrements at the first position where values need not be alive anymore") and the per-alternative prolog logic are present in both. **Lean output is evidence only for v4.35.0.**
- **Papers.** Perceus, safe-for-space closure conversion, ASAP and Counting Immutable Beans are paper subjects read from their PDF or arXiv texts. RFC 2094 is the NLL design document; the current rustc implementation is the authoritative subject.
- **Host for all executions.** x86-64 Linux, Intel Xeon @ 2.60 GHz, 96 logical CPUs. Every number is specific to that target's layout rules, for example the alignment of a coroutine discriminant.
- **Scope.** In scope: **static** placement of reclamation, meaning drop, dec and free insertion, and storage overlap. Out of scope: tracing-GC tuning and cycle collection. Region inference and destination-passing style appear only where they bear on these questions.

## Findings

### 1. Where each system's reclamation analysis lives

| System / pass | What is inserted | Analysis required | Locality class | Basis |
|---|---|---|---|---|
| Perceus declarative calculus λ1 | `dup`, `drop` | None: rules are non-deterministic and "closely related to linear typing" | Typing derivation | documentation |
| Perceus syntax-directed algorithm (Koka `Backend/C/Parc.hs`) | `dup`/`drop`, drop specialization, reuse | Live-variable sets computed by visiting "the expression tree *in reverse*"; borrowed set from `^` parameter annotations | Intraprocedural; callee borrow modes from interface | source + documentation |
| Lean 4 `inferBorrow` | Parameter modes (owned or `@&` borrowed) for functions and join points | Dataflow fixpoint (`loop` while `modified`) over the `decls` array of the unit being compiled; `@[export]` functions start owned | Interprocedural within a declaration block; signatures recorded for later units | source |
| Lean 4 `explicitRc` | `inc`/`dec` | Backward liveness; `jpLiveVarMap` for join points; per-`cases` union of live sets plus per-alternative prolog | Intraprocedural | source + execution |
| Lean 4 `expandResetReuse`, `coalesceRC` | Fast/slow paths for `reset`/`reuse`; merges RC operations within a basic block | Local (within a basic block) | Local | source |
| ASAP (Proust 2017) | Compile-time `SCAN`/`CLEAN` deallocation code | Path-based heap abstraction; interprocedural summaries computed in topological order of the call graph. A joint fixpoint for mutual recursion is sketched, but the core language µL "does not support" mutual recursion | **Whole program**: "We only consider programs consisting of a single compilation unit" | documentation |
| Flat closure conversion (CertiRocq `CC_Efun`; Paraskevopoulou–Appel) | Environment record holding the function's free variables | Free variables of the function block (`occurs_free_fundefs B \\ GFuns <--> FromList FVs'`) | Syntax-directed (synthesized attribute) | source + documentation |
| CertiRocq dead-parameter elimination | Removes dead parameters | Iterates `live` over all hoisted function definitions to a fixpoint (`find_live_helper`); escaping functions keep all parameters | Interprocedural | source |
| rustc MIR building (`scope.rs`) | `Drop` terminators and `StorageDead` on every scope exit edge | Lexical scope stack ("Each lexical scope thus corresponds to a single-entry, multiple-exit (SEME) region") | Local / lexical | source |
| rustc drop elaboration (`elaborate_drops.rs`) | Drop flags; `DropStyle::{Dead, Static, Conditional, Open}` | `MaybeInitializedPlaces` and `MaybeUninitializedPlaces` forward dataflow to a fixpoint | Intraprocedural | source + execution |
| rustc NLL liveness (`type_check/liveness/trace.rs`) | Region liveness constraints | Backward search from uses (USE-LIVE) and from drops (DROP-LIVE) | Intraprocedural (with dropck queries on types) | source |
| rustc coroutine layout (`coroutine/layout.rs`) | Overlapping layout of saved locals | `MaybeStorageLive`, `MaybeBorrowedLocals`, `MaybeRequiresStorage`, `MaybeLiveLocals` | Intraprocedural | source + execution |

### 2. Lean 4: borrow inference, explicit RC, and reset/reuse

Basis: source (pinned development revision) + execution (v4.35.0).

- **Pass order.** The impure pipeline (`Passes.lean`, `impurePasses`) runs `pushProj`, `insertResetReuse`, `elimDeadVars`, `simpCase`, **`inferBorrow`**, `explicitBoxing`, **`explicitRc`**, **`expandResetReuse`**, **`coalesceRC`**, and then later passes. `coalesceRC` "must be placed after `expandResetReuse` as that one relies on `inc`s still being present in their original location".
- **`inferBorrow`.**
  - "The inference is done with a data flow analysis which initially assumes all arguments are passed as borrowed and subsequently refines this by marking parameters as owned as required".
  - Correctness reasons for ownership: "We preserve tail calls to recursive functions and join points by ensuring we never have to insert a `dec` after a tail call", and reset/reuse targets must be owned.
  - Performance heuristics are skipped "if there is a user-defined borrow annotation".
  - The fixpoint is `partial def infer (decls : Array (Decl .impure))` with a `loop` that reruns while `modified`.
- **`explicitRc`.**
  - "performs a liveness analysis, inserting decrements at the first position where values need not be alive anymore. Furthermore, it inserts increments whenever values are used in an 'owned' fashion … and continue being used later on".
  - It treats "values that are projected from borrowed values as borrowed themselves" ("derived borrows").
  - At `cases` it collects "the union of all live values and then insert[s] an alternative specific prolog that decrements values which are not used in the respective alternative" (`addPrologForAlt`).
- **`expandResetReuse`.** It rewrites `let token := reset nfields orig; k` into a join point plus `cases isShared orig`. Reuse therefore costs a **runtime uniqueness test**: the static analysis decides only where reuse is *possible*.

**Executed output (v4.35.0, `trace.Compiler.inferBorrow` and `trace.Compiler.explicitRc`).** Excerpts:

```
def sumLen @&xs : tobj :=            -- parameter inferred borrowed; no inc/dec on xs
  ... let _x.4 := sumLen tail.2; let _x.5 := Nat.add _x.3 _x.4; dec _x.4; return _x.5
def incAll xs : tobj :=              -- owned; in-place reuse
  ... inc head.1; ... inc tail.2; let _x.3 := reset[2] xs; ...
      let _x.7 := reuse _x.3 in ctor_1[List.cons] _x.5 _x.6; return _x.7
def twoUses xs : obj :=              -- borrowed call first, consuming call last: no inc xs
  let _x.1 := sumLen xs; let _x.2 := incAll xs; ...
def branchUse b xs @&ys : tobj :=    -- per-arm prolog: xs dead in the false arm
  cases b | Bool.false => dec xs; inc ys; return ys
          | Bool.true  => let _x.1 := incAll xs; return _x.1
```

Readings of this output:

- `branchUse` shows the cost of an *inferred* borrow signature. `ys` is inferred borrowed although it is returned, so the false arm must `inc ys`. The boxed wrapper `branchUse._boxed` then performs `dec ys`.
- With an explicit owned annotation the `inc`/`dec` pair would move to the caller. That alternative was not executed.
- Cost of the run: the whole 4-definition file took **7.40 s wall** and **427 072 KB max RSS**, dominated by loading the prelude. Per-pass time was not measured.

### 3. Perceus (paper) and Koka (source)

Basis: documentation + source.

- **λ1, the linear resource calculus.** "each resource (i.e., owned variable) is consumed exactly once. That is, a resource needs to be explicitly duplicated (in rule dup) if it is needed more than once; or be explicitly dropped (in rule drop) if it is not needed."
  - The application rule splits the owned environment Γ into Γ1 and Γ2. Because "Γ2 is consumed in the e2 derivation … we can borrow Γ2 in the e1 derivation".
  - The `lam` rule requires `Γ = fv(λx. e)`: "a lambda is allocated as a closure at runtime that holds all free variables".
- **Algorithm and guarantees.** Perceus is "a deterministic syntax-directed version of λ1". The paper proves it "both sound (i.e. never drops a live reference), and garbage free (i.e. only retains reachable references)" (Theorems 1 and 2 of the technical report). Precision depends on "explicit control flow".
- **Per-branch elaboration.** For `match`, "we therefore generate the required dup and drop operations during elaboration for each branch". This is the same per-arm-prolog strategy as Lean's `addPrologForAlt`.
- **Borrowing in Koka.** Borrowing is a **user annotation**. `Syntax/Parse.hs` `paramInfo = do specialOp "^"; return Borrow <|> return Own`. Contrast Lean's inferred `@&`.
  - `Parc.hs` notes: "The live variable set is a state … To calculate the live variables we visit the expression tree _in reverse_".
  - `parcBorrowApp` "let-float[s] borrowed arguments to the top so that we can drop them after the function call".
  - `optimizeGuard True` applies drop specialization through `optimizeDupDrops`, which fuses dups with drops using constructor shape information.
- **Performance claim (paper).** "on the tree insertion benchmark, the purely functional Koka implementation is within 10% of the performance of the in-place mutating algorithm in C++ (using std::map)". This is a paper claim and was not re-measured here.

### 4. ASAP (technical report)

Basis: documentation.

- **Mechanism.** ASAP "is fully automatic (not even annotations are required) and makes heavy use of static analysis. At compile time it inserts, in the original program, code that deallocates memory blocks as they become useless." Deallocation is compiled into `SCAN`/`CLEAN` code that walks *paths* (compile-time heap descriptions) at run time.
- **Scope of analysis.** "We only consider programs consisting of a single compilation unit … Allowing split programs degrades the precision of our inter-procedural analyses." The improved live-variable analysis "is inter-procedural". Function summaries are "context-insensitive" and computed "in the topological order of the dependency graph of functions". For mutually recursive groups the report describes a joint fixpoint but states "we do not analyse mutually recursive functions (which µL does not support)".
- **Classification.** ASAP sits at the opposite end from annotation-driven schemes: no source annotations, whole-program summaries, and run-time scanning cost.

### 5. Safe-for-space closure conversion

Basis: documentation + source.

- **Theorem shape.** Paraskevopoulou and Appel (ICFP 2019) prove, for CertiCoq's CPS IR, that if a source program uses time c1 and space m1, the closure-converted program uses `c1 ≤ c2 ≤ Ktime·c1` and `m2 ≤ m1 + cost_space(e)`. The additive term is proportional to the size of the source program e.
- **Space measure.** The measure counts reachable heap under garbage collection. The paper notes "linked closures are not safe for space; suppose k is live but g is not, then with flat closures w is garbage-collectible but with linked closures w is still reachable".
- **Coverage.** Footnote: "The other phases are not (yet) proved safe-for-space."
- **In current CertiRocq.**
  - `closure_conversion.v` rule `CC_Efun` requires `(occurs_free_fundefs B) \\ GFuns <--> (FromList FVs')`, with the comment "The environment contains all the variables that are free in B", and `NoDup FVs'` "(* needed for cost preservation *)".
  - `bounds.v` defines **time and fuel** post-conditions (`inline_bound`, `simple_bound`, `hoisting_bound`) over cost counters `c` and `tapp`. It is not a space-bound file.
  - `dead_param_elim.v` implements an interprocedural live-parameter fixpoint (`live_fun : M.t (list bool)`, `find_live_helper`, `escaping_fun_exp`). Its line-1 header comment still reads "Correctness proof for lambda lifting".
- **Locality (derived).** Safe-for-space closure conversion needs only free variables, a bottom-up synthesized attribute. It does not need liveness. Under a reachability meter, dead-but-captured values are still charged, and that is acceptable: the source meter charges them too.

### 6. rustc: borrow liveness, drop timing, drop flags, and storage

Basis: source + execution.

- **Two meanings of "lifetime".** RFC 2094 separates "the lifetime of a reference, corresponding to the span of time in which that reference is used" from "the lifetime of a value … before the destructor for the value runs". NLL changes only the first.
- **Drop liveness extends borrow liveness.** `trace.rs`: USE-LIVE is found by "a reverse depth-first search … stop[ping] when we find a definition"; DROP-LIVE comes from a search starting at each drop, whose points are added to "the regions found in the `dropck_outlives` result of the variable's type". RFC 2094 adds a false unwind edge so "the compiler essentially always assumes that a destructor may run". A lexically scheduled drop of a value whose type implements `Drop` therefore keeps borrows inside that value live until scope end.
- **Drop scheduling is lexical.** `scope.rs`: "we also accumulate places that need to be dropped upon exit from each scope … whenever we branch out we will insert drops of all those places onto the outgoing edge".
- **Drop flags at joins.** `elaborate_drops.rs` "refines Drop to only run the destructor if the target is initialized … by inserting drop flags for every variable that may be dropped". `drop_style` maps `(maybe_init, maybe_uninit, multipart)` as follows:

  | `(maybe_init, maybe_uninit, multipart)` | Drop style |
  |---|---|
  | `(false, _, _)` | `Dead` |
  | `(true, false, _)` | `Static` |
  | `(true, true, false)` | `Conditional` |
  | `(true, true, true)` | `Open` |

  **Measured** with `--emit=mir`:
  - At `opt-level=0`, `cond_move` (`if c { sink(s) }`) gets a flag local `_7: bool` with writes `_7 = const false`, `_7 = const true`, `_7 = const false` and a `switchInt(copy _7)` guarding `drop(_2)`.
  - `both_arms_move` has no flag and no `drop`; `no_move` has no flag and static drops.
  - At `opt-level=2` the flag in `cond_move` is gone, and a single `drop(_2)` sits on the non-moving path.
  - The runtime bit is created by the dataflow join, and in this simple case MIR optimization can remove it.
- **Storage.** Three dataflow analyses decide storage:
  - `MaybeStorageLive` gens and kills only on `StorageLive`/`StorageDead`.
  - `MaybeBorrowedLocals` inserts a local on `&`, `&mut`, `&raw` or a reborrow and removes it only at `StorageDead` ("When we reach a `StorageDead` statement, we can assume that any pointers to this memory are now invalid"). It ignores NLL.
  - `MaybeRequiresStorage` kills a local after a `Move` only when it is not maybe-borrowed: "Kill locals that are fully moved and have not been borrowed".
- **Coroutines.** `locals_live_across_suspend_points`: "for immovable coroutines we need to account for borrows, so we conservatively assume that all borrowed locals are live until we find a StorageDead statement". It computes `live_locals.union(borrowed_locals)` and then intersects with `requires_storage`. `compute_storage_conflicts` lets saved locals overlap when they are never storage-live together.
- **Polonius.** The repository's README warns: "This implementation of Polonius is mainly used for experiments. The Rust compiler uses its own implementation". Its `compute_live_origins` encodes the same split as rustc: `var_live_on_entry` from uses, and `var_drop_live_on_entry` from drops of maybe-partly-initialized variables. It offers `Naive`, `DatafrogOpt`, `LocationInsensitive`, `Compare` and `Hybrid` algorithms.

**Measured coroutine and future sizes** (`size_of_val`, identical at `opt-level=0` and `3`). `Buf([u8; 4096])` is not `Copy` and has no `Drop`; `LoudBuf` has a `Drop` impl.

| Variant (state before the single `.await`/`yield`) | Bytes |
|---|---:|
| async: `buf` moved into `consume(buf)` (never borrowed) | 4 |
| async: `peek(&buf)`, borrow dead (by NLL) before the await | **4100** |
| async: `{ let buf = …; peek(&buf) }` inner block | 4 |
| async: `buf` used after the await | 4099 |
| async: `peek(&buf); drop(buf);` before the await | **4100** |
| async: `LoudBuf` unused but dropped at scope end, after the await | 4100 |
| async: `LoudBuf` moved into `drop(g)` before the await, never borrowed | 4 |
| async: `LoudBuf` borrowed inside an inner block | 4 |
| async: no buffer | 4 |
| movable `#[coroutine] \|x\| { let buf; peek(&buf); yield; }` | **2** |
| `#[coroutine] static \|x\| { …same… }` | **4098** |

**Measured ordinary stack frames** (`--emit=asm`, x86-64; frame = Σ `sub rsp` + 8·pushes + return address):

| Function | opt-level=0 | opt-level=3 |
|---|---:|---:|
| two `Buf`s in disjoint blocks | 16400 | **4144** |
| same scope, first only borrowed | 16400 | **8240** |
| same scope, first moved into `consume` | 24592 | **8240** |

Derived reading: at `opt-level=3` the backend overlapped the two buffers only when `StorageDead` of the first preceded `StorageLive` of the second. That is consistent with storage markers lowering to the backend's stack-colouring lifetime ranges; the rustc codegen and LLVM source for this lowering were not examined.

### 7. When moving a value versus ending a borrow changes peak live storage

Basis: execution + source + derived.

- **Ending a borrow (NLL)** never shrinks storage in any measured configuration:
  - immovable coroutines keep the local until `StorageDead`;
  - ordinary frames keep it until `StorageDead`.
- **Moving a never-borrowed local** shrinks the state that an *immovable coroutine* must save: 4100 → 4 B. It does not shrink an *ordinary frame*: 8240 B either way.
- **Moving a previously borrowed local** shrinks nothing (4100 B).
- **An inner lexical block** (earlier `StorageDead`) shrinks both.
- **Implication for an explicit-annotation design (derived).** In rustc today, the only source construct that reliably bounds peak *storage* is a lexical block. `drop(x)` and moves end the *value* and its destructor obligations, not the *storage*, unless the local was never borrowed and the context is a coroutine.

### 8. Felleisen macro-expressibility of liveness-driven reclamation (derived analysis)

**Definitions used.**

- Felleisen (1991) calls a construct *macro-expressible* when a translation is homomorphic on all other constructs and maps the construct to a fixed context whose holes are filled with the translations of its immediate subterms.
- A **strict macro** cannot inspect subterms. In particular it cannot ask whether a variable is free in a continuation.
- The analysis also uses finer locality classes:
  - **S** — strict macro;
  - **FV** — structural recursion with bottom-up free-variable sets (synthesized attributes);
  - **CTX** — inherited live-after sets from the continuation;
  - **FIX-intra** — a fixpoint over join points and loops in one body;
  - **FIX-inter** — a fixpoint over a call graph.

**Claims, each derived from the sources above.**

1. **Explicit `drop`/`dup` in the source make RC insertion class S.** λ1 *is* the annotated language. Erasing `dup x ↦ inc x` and `drop x ↦ dec x` (or `free` when uniqueness is statically known) is homomorphic. Perceus's contribution is inferring these annotations (classes FV + CTX). Lean's `explicitRc` infers them with class FIX-intra. Soundness of the annotated program becomes a **type-checking** obligation, namely λ1's linear discipline, rather than a translation property. Target peak space equals source peak space exactly when the source meter frees at the annotated positions.
2. **Last-use `move` markers alone are weaker than `drop`.** A marker at the last use in one arm says nothing about the other arm. At a join where arms disagree, one of three things must happen:
   - (a) the type system demands an explicit `drop` in the non-consuming arm, which is Perceus's per-branch elaboration written by the programmer;
   - (b) the translation inserts a runtime flag, which is class S but costs one bit per conditionally initialized path (rustc's `Conditional` drop style);
   - (c) a FIX-intra analysis proves the join consistent.

   rustc chooses (b) and lets MIR optimizations remove flags; λ1 corresponds to (a).
3. **Sharing breaks static freeing, not compositionality.** With `dup`, a `drop` compiles to a counted decrement. This is still class S, but the target needs per-object count metadata. Turning `dec` into `free` or in-place `reuse` needs a runtime uniqueness check (`isShared` in Lean's `expandResetReuse`) or a static uniqueness type. Both choices keep the translation local.
4. **Borrow-annotated call boundaries.** If the callee's parameter modes are written in its interface (Koka `^x`), call translation is class S. If they are inferred from the callee body (Lean `inferBorrow`), they are FIX-inter within the declaration block, and become a recorded interface for later compilation units. Inferred modes can also move RC work across the boundary in surprising ways (`branchUse` above).
5. **Closures.** Capture is a move of exactly `fv(λ)`, class FV, both in Perceus's `lam` rule and in CertiRocq's `CC_Efun`. Under a reachability meter, flat closures are safe for space with an additive constant. A capture analysis that drops dead captured variables would need CTX inside the body (not examined in any subject).
6. **Recursion and tail calls.** With annotations, recursion is unproblematic. Lean makes tail-called parameters owned so that no `dec` follows a tail call. That is a constraint *on placement*: in the annotated source, drops must precede tail calls.
7. **Suspended frames with self-borrows (immovable coroutines)** are where rustc stops being liveness-precise: storage reuse is bounded by lexical markers (§6–§7). An annotation-based design would need either a lexical "storage end" construct (which rustc already has, as blocks) or borrow-end information flowing into layout. No examined compiler does the latter.

**Mapping of source annotations to the minimal locality class needed for sound, peak-preserving reclamation.** All entries are derived.

| Source annotation | Straight-line code | Conditionals | Closures | Recursion / loops |
|---|---|---|---|---|
| None (inference) | CTX | CTX + per-arm prolog | FV | FIX-intra (join points); FIX-inter for borrow modes |
| Last-use `move` markers | S | Runtime flag, or CTX | FV | FIX-intra for loop-carried ownership |
| Explicit `drop`/`dup` with a linear check | S | S (arms must agree by typing) | FV (capture = move) | S |
| Plus borrow-annotated signatures | S | S | FV | S |
| Lexical storage blocks (Rust) | S for storage | S | FV | S |

### 9. Performance and resource footprint (L1–L6)

| Level | Lean 4 RC passes | Koka / Perceus | ASAP | CertiRocq closure conversion | rustc drop and storage passes |
|---|---|---|---|---|---|
| L1 authoring | not measured | not measured | not measured | not measured | not measured |
| L2 toolchain build | not measured | not measured | not measured | not measured | not measured |
| L3 compile latency | 7.40 s wall for a 4-definition file including prelude load (measured, v4.35.0); per-pass time not measured | not measured | not examined (scalability chapter not read) | not measured | `fut2.rs` compile + link 0.09 s wall at `opt-level=0` and `3`; `flags.rs` to MIR 0.04 s (measured); per-pass time not measured |
| L4 generated code | not measured | Within 10% of C++ `std::map` on tree insertion (paper) | not measured | Time overhead `c2 ≤ Ktime·c1` (paper theorem) | One drop-flag byte and branch per conditional move at `opt-level=0`, removed at `opt-level=2` in the probe (measured) |
| L5 proof checking | n/a | n/a | n/a | not measured | n/a |
| L6 footprint | 427 072 KB max RSS for the compile (measured); RC header per object (not measured) | RC word per object (paper design; size not measured) | not measured | Space overhead `m2 ≤ m1 + cost_space(e)` (paper theorem) | Future size 4 B vs 4100 B and frame 4144 B vs 8240 B depending on scope, move and borrow; rustc max RSS 126–131 MB on the probes (measured) |

### 10. Comprehensibility and simplicity (C1, C2)

- **C1 (human).**
  - Inferred borrow modes (Lean) are invisible in source, and their effects are non-local. `branchUse` incurred `inc ys` because of an inference heuristic.
  - Koka's explicit `^` keeps the mode in the signature, where a reader sees it.
  - Rust's split between borrow liveness, drop timing and storage is a three-concept mental model, and the measured coroutine sizes contradict the natural single-concept intuition that "the borrow ended, so the buffer is gone".
  - Drop flags are invisible in source; they appear only in MIR.
- **C2 (simplicity).**
  - Per-arm prologs (Lean `addPrologForAlt`, Perceus per-branch elaboration) and drop flags (rustc) are two mechanisms enforcing one invariant: each owned value is released exactly once on every path. They differ only in whether the join is resolved statically by code duplication or dynamically by a bit.
  - λ1's linear discipline is the minimal abstraction that makes both ordinary. Requiring arms to agree turns the dynamic flag into an explicit, statically checked `drop`. Whether that pushes boilerplate onto programmers is the open cost (Boundaries).

### 11. Validation (V1–V4)

- **V1 (specification adequacy).**
  - Perceus's soundness and garbage-freedom theorems are paper proofs; whether they are mechanized was not checked.
  - CertiRocq's closure-conversion cost preservation is mechanized in Coq/Rocq. The paper also provides a standalone artifact, `zoep/safe-for-space`, which was not examined.
  - No spec-mutation or property-based testing of RC insertion was found in the examined sources.
- **V2 (differential testing).**
  - Polonius's `Compare` algorithm runs `Naive` and `DatafrogOpt` side by side "to ensure they indeed compute the same errors". That is a differential check between two implementations of the same rules.
  - The probes here are small differential runs across optimization levels and annotation variants.
- **V3 (concurrency, crash, physical).** Lean's reset/reuse depends on a runtime `isShared` test; its multi-threaded refcount semantics were not examined.
- **V4 (human mental models).** Not examined. The coroutine-size table is a candidate litmus test for programmers' mental models of Rust storage.

## Boundaries

- **Not examined.**
  - LLVM stack colouring, and how rustc codegen lowers `StorageLive`/`StorageDead`. §6 is consistent with that lowering but does not prove it.
  - rustc's in-tree Polonius implementation (`-Zpolonius=next`).
  - Koka execution (no Koka compiler was run).
  - ASAP's implementation and scalability chapter: the fetched report text was truncated before chapter 7.
  - Lean multi-threaded RC.
  - Mechanization status of Perceus's theorems.
  - The standalone safe-for-space artifact.
  - Capture analyses that trim dead captured variables.
  - Swift/ARC, C++ RAII, and region-based systems.
- **Unknown.**
  - Whether rustc MIR optimizations remove drop flags in general, beyond the single `if c { sink(s) }` pattern measured.
  - Whether any production compiler feeds NLL borrow ends into storage reuse or coroutine layout. None of the examined passes does.
- **Known not to apply.**
  - NLL does not change drop timing or storage. This follows from the source together with the measured 4100-byte futures.
  - `drop(x)` on a `Copy` type is a no-op (rustc warns), so it cannot end storage either.
  - CertiRocq `bounds.v` is not a space-bounds file.
  - The examined closure-conversion proof covers only the closure-conversion phase.
- **Stronger conclusions this evidence does not establish.**
  - That explicit `drop`/`dup` annotations yield a *verified* compositional translation into a particular capability-backed target with preserved peak space. §8 is a derived argument, not a mechanized theorem.
  - That annotation burden is acceptable to programmers.
  - That the measured byte counts generalize beyond this target, rustc nightly and Lean version.
  - That ASAP's run-time scanning is cheaper or costlier than reference counting (no measurement).

## Evidence

All observations were made on 2026-11-20 (UTC).

**leanprover/lean4 @ 9b60f0232c9bdbbff3df8320aaa71ed13f254eb2 (source)**

| Path | Lines | Content |
|---|---|---|
| `src/Lean/Compiler/LCNF/Passes.lean` | 144–158 | `impurePasses` order |
| `src/Lean/Compiler/LCNF/InferBorrow.lean` | 19–49 | Header contract |
| same | 266–288 | `infer` fixpoint (`loop` while `modified`, from line 279) |
| `src/Lean/Compiler/LCNF/ExplicitRC.lean` | 15–28 | Header |
| same | 389–415 | `addPrologForAlt` |
| same | 597–612 | `cases` handling |
| `src/Lean/Compiler/LCNF/ExpandResetReuse.lean` | 12–63 | Hot and cold path shape with `isShared` |
| `src/Lean/Compiler/LCNF/CoalesceRC.lean` | 14–29 | Coalescing rules and ordering constraint |
| `src/Lean/Compiler/BorrowedAnnotation.lean` | 14–18 | `markBorrowed` / `isMarkedBorrowed` |

**leanprover/lean4 @ eb6cafb7290e8bd5f2937522d8d804f58f02bafc (v4.35.0, executed)**

- `ExplicitRC.lean`: `addPrologForAlt` at line 421; the `cases` comment at line 626.
- `InferBorrow.lean`: `infer` at line 263.

**rust-lang/rust @ ec65cd52bba13d491ff65c9d218b39753755c84a (source)**

| Path | Lines | Content |
|---|---|---|
| `compiler/rustc_borrowck/src/type_check/liveness/trace.rs` | 29–43 | USE-LIVE / DROP-LIVE doc |
| `compiler/rustc_mir_build/src/builder/scope.rs` | 1–85 | Module doc: SEME regions, Drops, Early exit |
| `compiler/rustc_mir_transform/src/elaborate_drops.rs` | 21–49 | Pass doc |
| same | 165–188 | `drop_style` |
| `compiler/rustc_mir_transform/src/elaborate_drop.rs` | 21–38 | `DropStyle` |
| `compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs` | 12–24 | `always_storage_live_locals` |
| same | 64–65 | `MaybeStorageLive` gen/kill |
| same | 118–156 | `MaybeRequiresStorage` and `KillableLocalsVisitor`, with the `Move`-and-not-borrowed test at 136–142 |
| same | 349–357 | `check_for_move` |
| `compiler/rustc_mir_dataflow/src/impls/borrowed_locals.rs` | 1–37 | Doc and gen rules |
| same | 99–102 | Kill at `StorageDead` |
| `compiler/rustc_mir_transform/src/coroutine/layout.rs` | 83–160 | `locals_live_across_suspend_points`, with `if !movable` at 121–134 |
| same | 235–292 | `compute_storage_conflicts` |
| `compiler/rustc_borrowck/src/region_infer/mod.rs` | — | Region SCC solver (context only) |

**rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 (executed nightly)**

- `storage_liveness.rs` and `borrowed_locals.rs` are byte-identical to the source pin.
- `layout.rs` has `if !movable` at line 121.
- `elaborate_drops.rs` has the same `drop_style` match at lines 185–189.

**rust-lang/polonius @ bfd4c945b7713d0e66a3cde80475d9a4494740df**

| Path | Lines | Content |
|---|---|---|
| `README.md` | 1–4 | Experimental-implementation warning |
| `polonius-engine/src/output/mod.rs` | 25–43 | `Algorithm` |
| `polonius-engine/src/output/liveness.rs` | 48–85 | `var_live_on_entry`, `var_drop_live_on_entry`, `origin_live_on_entry` |

**CertiRocq/certirocq @ ab66e0164e7ecb63e5af95c90c8e479068bf95c2**

| Path | Lines | Content |
|---|---|---|
| `theories/LambdaANF/closure_conversion.v` | 160–175 | `CC_Efun`, including the free-variable premise and "(* needed for cost preservation *)" at 164 |
| `theories/LambdaANF/dead_param_elim.v` | 1 | Stale header comment |
| same | 19–20 | `live_fun` |
| same | 71 | `escaping_fun_exp` |
| same | 103 | `live_expr` |
| same | 158–182 | `find_live_helper`, `find_live` |
| `theories/LambdaANF/bounds.v` | 91–95 | `inline_bound` (time/fuel) |

**koka-lang/koka @ b66091b2a5a7ea20c5ed9498ad1e1f03caee9589**

| Path | Lines | Content |
|---|---|---|
| `src/Backend/C/Parc.hs` | 10–21 | Notes on reverse traversal and borrowed/owned environments |
| same | 192–230 | `parcBorrowApp`, `parcBorrowArg` |
| same | 241–265 | Per-branch live sets |
| same | 319–330 | `optimizeGuard` and drop specialization |
| `src/Syntax/Parse.hs` | 1249–1253 | `paramInfo`, the `^` borrow annotation |

**Literature.** Identifiers were checked against bibliographic search results or arXiv on 2026-11-20.

- A. Reinking, N. Xie, L. de Moura, D. Leijen. *Perceus: Garbage Free Reference Counting with Reuse.* PLDI 2021. DOI 10.1145/3453483.3454032. Text read from the MSR technical report v4 linked from `Parc.hs`.
- Z. Paraskevopoulou, A. W. Appel. *Closure Conversion Is Safe for Space.* ICFP 2019, PACMPL 3, Article 83. DOI 10.1145/3341687. Text read from cs.princeton.edu/~appel/papers/safe-closure.pdf.
- R. L. Proust. *ASAP: As Static As Possible memory management.* University of Cambridge Technical Report UCAM-CL-TR-908, July 2017. DOI 10.48456/tr-908. Abstract and chapters 1–2 read; the text available here was truncated.
- S. Ullrich, L. de Moura. *Counting Immutable Beans: Reference Counting Optimized for Purely Functional Programming.* arXiv:1908.05647 (v3, 5 Mar 2020). Abstract verified.
- N. D. Matsakis, F. S. Klock II et al. *Rust RFC 2094: Non-Lexical Lifetimes.* Start date 2017-08-02, rust-lang/rfcs#2094. No DOI.
- M. Felleisen. *On the Expressive Power of Programming Languages.* Science of Computer Programming 17(1–3):35–75, 1991. DOI 10.1016/0167-6423(91)90036-W. Bibliographic only.
- Z. Shao, A. W. Appel. *Space-Efficient Closure Representations.* LFP 1994. DOI 10.1145/182409.156783. *Efficient and Safe-for-Space Closure Conversion.* ACM TOPLAS 22(1), 2000. DOI 10.1145/345099.345125. Both bibliographic only.
- Y. Minamide, G. Morrisett, R. Harper. *Typed Closure Conversion.* POPL 1996. DOI 10.1145/237721.237791. Bibliographic only.

**Execution environment.** x86-64 Linux, Intel Xeon @ 2.60 GHz.

- `rustc -vV`: `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5.
- Lean: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.

## Revalidation

1. **Coroutine storage rule (cheapest discriminator).** Save the program below as `/tmp/p2/fut2.rs` and run `rustc --edition 2021 -C opt-level=3 fut2.rs && ./fut2`.
   - The finding holds while `b_borrowed` is far larger than `a_moved`, and `static` is far larger than movable.
   - A change to roughly 4 B for `b_borrowed` would mean borrow ends now inform layout. That would be a material change to this report.
   ```rust
   #![feature(coroutines, stmt_expr_attributes)]
   use std::{future::Future, pin::Pin, task::{Context, Poll}};
   struct Buf([u8; 4096]);
   struct YieldOnce(bool);
   impl Future for YieldOnce { type Output = ();
     fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
       if self.0 { Poll::Ready(()) } else { self.0 = true; Poll::Pending } } }
   #[inline(never)] fn consume(b: Buf) -> u8 { b.0[0] ^ b.0[4095] }
   #[inline(never)] fn peek(b: &Buf) -> u8 { b.0[1] }
   async fn a_moved(x: u8) -> u8 { let buf = Buf([x; 4096]); let r = consume(buf); YieldOnce(false).await; r }
   async fn b_borrowed(x: u8) -> u8 { let buf = Buf([x; 4096]); let r = peek(&buf); YieldOnce(false).await; r }
   async fn c_inner(x: u8) -> u8 { let r = { let buf = Buf([x; 4096]); peek(&buf) }; YieldOnce(false).await; r }
   async fn e_borrow_drop(x: u8) -> u8 { let buf = Buf([x; 4096]); let r = peek(&buf); drop(buf); YieldOnce(false).await; r }
   fn main() {
     println!("{} {} {} {}", std::mem::size_of_val(&a_moved(1)), std::mem::size_of_val(&b_borrowed(1)),
              std::mem::size_of_val(&c_inner(1)), std::mem::size_of_val(&e_borrow_drop(1)));
     let m = #[coroutine] |x: u8| { let buf = Buf([x; 4096]); let r = peek(&buf); yield (); r };
     let s = #[coroutine] static |x: u8| { let buf = Buf([x; 4096]); let r = peek(&buf); yield (); r };
     println!("{} {}", std::mem::size_of_val(&m), std::mem::size_of_val(&s));
   }
   ```
   Expected on the examined nightly: `4 4100 4 4100`, then `2 4098`.
2. **Source diff check for rustc.** At a new revision, diff:
   - `locals_live_across_suspend_points` in `compiler/rustc_mir_transform/src/coroutine/layout.rs`;
   - `MaybeRequiresStorage::check_for_move` and `KillableLocalsVisitor` in `compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs`;
   - the `StorageDead` kill in `borrowed_locals.rs`.
3. **Drop flags.** Compile this with `rustc --crate-type lib --emit=mir -C opt-level=0` and look for a `bool` local assigned `const true`/`const false` that guards `drop(_2)`:
   ```rust
   pub struct S(pub Vec<u8>);
   #[inline(never)] pub fn sink(_s: S) {}
   pub fn cond_move(c: bool) { let s = S(vec![1,2,3]); if c { sink(s); } }
   ```
4. **Frame overlap.** Save `frames.rs` (two `Buf`s in disjoint blocks, or in the same scope with the first borrowed or moved; each passed to an `#[inline(never)]` function that applies `std::hint::black_box`). Compile with `--emit=asm -C opt-level=3` and sum the `sub rsp` immediates. Expected: disjoint well below same-scope (4144 B versus 8240 B on x86-64).
5. **Lean RC placement.** With `lean` v4.35.0, run a file containing `set_option trace.Compiler.explicitRc true in` before each of these definitions, and confirm `@&xs` on `sumLen`, `reset`/`reuse` in `incAll`, and `dec xs` at the false-arm entry in `branchUse`:
   - `def sumLen (xs : List Nat) : Nat := match xs with | [] => 0 | _ :: t => 1 + sumLen t`
   - `def incAll (xs : List Nat) : List Nat := match xs with | [] => [] | h :: t => (h + 1) :: incAll t`
   - `def branchUse (b : Bool) (xs ys : List Nat) : List Nat := if b then incAll xs else ys`

   Other Lean versions may print different IR. The pinned development revision's `ExplicitRC.lean` differs from v4.35.0.
6. **Paper-derived claims** (Perceus theorems, ASAP scope, closure-conversion bound) have no cheap probe. Revalidate them by rereading the cited sections.
