# Multi-Region Outlives Backward Frames, Guarded Early-Return Control Flow, and Pre-Order Computable AST Folding in Constructive Proof Kernels

## Summary

Translating Rust functions with interdependent lifetime bounds (`'a : 'b`), explicit control-flow joins, and mixed conditional early returns into a pure functional representation audited inside Lean 4 (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `10.1007/978-3-030-79876-5_37`) without `partial def`, `WellFounded.fix`, or auxiliary `._unsafe_rec` constants requires resolving three structural bottlenecks across borrow checking, CFG lowering, and kernel reduction:

1. **Staggered multi-region `'a : 'b` call frames require producer-tagged deposit ordering, active shared-child rejection, sentinel-lock liveness checks, and stack-escape walks.** Polonius (`rust-lang/polonius` at `bfd4c945b7713d0e66a3cde80475d9a4494740df`), Charon (`AeneasVerif/charon` at `b23c297f57c0b2072de7967c7f17088db0278a8c`), and Aeneas (`AeneasVerif/aeneas` at `2e3d4488280bb8a95411db81019a7854a784861f`, `10.1145/3547647`, `10.1145/3674640`) stratify function lifetimes into a DAG of strongly connected region groups (`RegionsHierarchy.ml:165–486`). Operational backward-frame retirement additionally requires six soundness guards: consuming `regionDeposits` tagged by producer `RegionGroupId` in `requiredChildren` order (`takeChildDeposits_two_children_comm`), banning active shared-child consumers, retiring unborrowed `.regionOut` output loans strictly inside `endRegionGroup`, verifying `lockLid` names no live non-output loan, checking output permission flavors against pre-retirement loan status, and walking `.parentLoan` chains (`targetOutlivesFrame`) to reject stack-backed `&mut` returns.
2. **Explicit CFG joins and mixed symbolic early returns require simultaneous bijective loan evacuation (`base + i`) and branch-projected continuation wrappers.** Sequential in-place loan renaming fails on swapped loan cycles (`[(2, 3), (3, 2)]`) and pre-`StorageDead` scratch handles; `relabelJoinLoans` resolves both via fresh temporary IDs `base + i` and a `moved` forwarding table. Conditional early returns (`if sym_c { return e; }`) thread `ExecFlow.guardedContinuing` continuations paired with `projectBranchFuncOut` / `projectBranchMutRet` stripping of opposite-arm `.choice` artifacts and inductive CFG handle-freedom (`handleFreeOutOpt`).
3. **Zero-`._unsafe_rec` pre-order `listFold`/`natFold` folding, single-pass destructuring, and key-indexed `@[irreducible]` barriers overcome Lean 4 kernel cliffs.** Lean 4's structural recursion compiler emits `._unsafe_rec` via `addAndCompilePartialRec` (`Main.lean:183–199`), while `WellFounded.fix` (`WF.lean:135–141`) is `noncomputable`. Flattening recursive ASTs into pre-order `List` streams evaluated right-to-left via `listFold` (`List.foldr` threading `(tail, ih)`) and `natFold` (`@Nat.recCompiled`) provides unbounded computable recursion with zero `._unsafe_rec` and zero depth caps, while single-pass linear destructuring drops $O(4^N)$ multi-projection WHNF blowup (crashing `maxRecDepth` at $N = 20$) to $O(N)$ through $N = 80$ (sharded at $\le 64$ ops). Conversely, `rw`/`simp` (`Rewrite.lean:47–52`) penetrate explicit `Prop` arguments inside `Hold P` and `@[irreducible] def CutFirewall tag P := P`, whereas key-indexed `@[irreducible]` named predicates (`CutBarrier ctx k`) block inner AST traversal and cut 256-leaf 16-pass tactic wall time by `22.5%–29.7%`.

## Applicability

This report examines primary compiler/prover sources and Lean `v4.34.1` kernel measurements across six repositories and four peer-reviewed papers as observed on `2026-11-20`:

- **Lifetime, outlives, and symbolic join pipelines:** `rust-lang/polonius` (`bfd4c945b7713d0e66a3cde80475d9a4494740df`), `AeneasVerif/charon` (`b23c297f57c0b2072de7967c7f17088db0278a8c`), and `AeneasVerif/aeneas` (`2e3d4488280bb8a95411db81019a7854a784861f`) govern origin subsets (`subset`), region binders, region-group SCC construction (`RegionsHierarchy.ml`), abstraction continuation typing (`SymbolicToPureAbs.ml`), and context-matching maps (`InterpMatchCtxs.ml`).
- **Lean 4 kernel, elaboration, and trust-boundary checkers:** `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`), `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`), and `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`) define strict `prelude` verification (`Init.Core`, `Init.NotationExtra`, `Init.Data.Nat.Basic`, `Init.Data.List.Basic`, `Init.SimpLemmas`, zero `._unsafe_rec`, zero `noncomputable`, zero `Classical.choice`/`Quot.sound`/`sorryAx`).

Prior corpus packages cover single-region Aeneas translation (`aeneas-borrows-symbolic-ownership-and-resource-semantics`, `aeneas-architecture-translation-pipeline-and-pure-extraction`), Polonius limits (`borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits`), `partial` encoding rules (`lean-partial-definitions-termination-and-wp-encoding`), and Lean 4 WHNF memory ceilings (`lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`). This report focuses on multi-region `'a : 'b` call frames, simultaneous bijective joins, guarded early-return CFGs, and pre-order `listFold` / rewrite-barrier mechanics.

## Findings

### 1. Region SCC Hierarchies and Outlives Graphs Across Polonius, Charon, and Aeneas

Basis: source + normative

Across Rust borrow checking and functional lifting, lifetime constraints form a directed graph where an edge `'long -> 'short` expresses Rust's outlives relation `'long : 'short`:

- **Polonius origin subset constraints (`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`):** `polonius-engine/src/output/datafrog_opt.rs:19–62` solves `subset(origin1, origin2, point)` and `origin_contains_loan_on_entry(origin, loan, point)` across CFG edges to check loan validity, without synthesizing backward functions.
- **Charon region AST (`AeneasVerif/charon@b23c297f57c0b2072de7967c7f17088db0278a8c`):** `charon/src/ast/type_level/regions.rs:10–22` models `Region` as `Var(RegionDbVar) | Lub(Ty) | Static | Body(RegionId) | Erased`, while `charon/src/ast/type_level/types.rs:57–64` attaches `RegionBinder` to `FnDef`/`FnPtr`.
- **Aeneas region-group SCC decomposition (`AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f`):** `src/llbc/RegionsHierarchy.ml:165–486` turns signature outlives clauses and nested reference types into a DAG of `region_group = { id; regions; parents }` (`line 428`):
  1. Initializes edges from `RStatic` to all free region variables `RVar (Free r.index)` (`lines 184–193`), adding signature `outlives` constraints (`lines 224–232`).
  2. Walks `output :: inputs` (`explore_ty outer ty`, `lines 235–278`): each `TRef (r, ty, _)` emits `add_edges ~long:r ~shorts:outer` (`line 273`, capturing Rust's rule that outer references live at least as long as inner referenced borrows unless constrained otherwise), and ADT arguments instantiate `decl.generics` predicates (`lines 251–265`).
  3. Runs `SCC.Make` (`lines 334–335`) to merge mutually outliving lifetimes (`'a : 'b ∧ 'b : 'a`) into single equivalence classes and compute parent dependencies (`lines 422–425`).
  4. **Conservative `'static` detachment (`lines 132–164, 461–472`):** `sig_static_interacts_with_other_regions` detaches `'static` (`parents := []`) when `'static` appears solely inside shared borrows neither nested under other borrows nor inside multi-region ADTs (`contains_static_mut == false`), avoiding spurious parent dependencies for `&'static str` fields.
  5. **Abstraction synthesis limit (`src/symbolic/SymbolicToPureAbs.ml:94, 181, 202–237`):** `abs_to_input_output_tys` and `abs_to_ty` synthesize backward continuation signatures only for `abs_level = 0`, raising `"Unimplemented"` on deeper sub-abstractions.

---

### 2. Staggered Multi-Region Backward Call Frames, Producer-Tagged Deposits, and Stack-Escape Rejection

Basis: source + derived

When a callee signature imposes `'a : 'b` and `'a : 'c` (so child region groups `'b` and `'c` must retire before parent `'a`), backward evaluation passes intermediate values from child groups to `'a`'s backward function via `RegionGroupEntry`:

```lean
structure RegionGroupEntry (Val : Type) where
  groupId          : Nat
  active           : Bool
  lockLid          : Nat
  inputTargets     : List (OwnerRef × List Nat)
  outputLoans      : List Nat
  requiredChildren : List Nat
  backFn           : List Val → List Val → Option (List Val × List Val)
```

Six invariants prevent multi-region backward soundness bugs:

1. **Order-independent producer-tagged deposits (`takeChildDeposits`):** Independent children `'b` and `'c` have no outlives edge between them, so different paths may retire `'b` before `'c` or `'c` before `'b`. Storing untagged `List Val` deposits flips the argument order passed to `g.backFn`! Tagging deposits `(producerGid, val)` and extracting via `takeChildDeposits g.requiredChildren deps` (folding over `g.requiredChildren` in canonical signature order) guarantees `takeChildDeposits [c1, c2] [(c1, v1), (c2, v2)] = takeChildDeposits [c1, c2] [(c2, v2), (c1, v1)]` (`takeChildDeposits_two_children_comm`, proved with zero axioms).
2. **Active shared-child starvation ban (`childShared`):** Because `takeChildDeposits` consumes matched deposits when a parent retires, if two distinct active groups `g` and `o` both list `c ∈ requiredChildren`, the first parent consumes `(c, v)` and leaves `o` with `[]`. `endRegionGroupInState` must fail closed if any other active group shares a required child.
3. **Unborrowed output-loan retirement & direct-end blocking:** Retiring `gid` checks that every `lid` at index `idx` of `g.outputLoans` is unique, active, unborrowed (`isUnborrowed e.cell.perm`), free of active child loan/region edges, and targets `BackTarget.regionOut gid idx` (`isMatchingRegionOut`). Ordinary `endLoanInState` simultaneously blocks retiring `.regionOut` targets via `activeTargetHasSpecial`, forbidding out-of-band partial retirement.
4. **Live non-output `lockLid` exclusion & pre-retirement flavor checking:** Because `writebackRegionTargets` exempts `g.lockLid` from live-loan overlap checks, it must enforce `st.loans.all (fun e => e.id != lockLid || e.status.isEnded)` (so a forged frame cannot exempt a live unrelated loan!), while passing the *pre-retirement* `st.loans` snapshot (`phaseLoans`) to `releasedPermFlavorsMatch` so each retired output loan's mutable vs. shared role in `ownerPerm` is checked before retirement strips permissions.
5. **Invocation-unique `groupId` & disjoint `inputTargets`:** Duplicate `groupId` entries (`!hasUniqueRegionGroupId`) or overlapping `inputTargets` (`!ownerPathsDisjoint`) fail closed.
6. **Stack-escape rejection (`targetOutlivesFrame`):** When synthesizing `&mut`-returning callees (`synthesizeMutReturnFromVal`), `targetOutlivesFrame` walks `.parentLoan l` leaves via `@Nat.recCompiled` (`loans.length + 1` steps) and returns `false` on any `.localReg` leaf (stack frame local escaping via `&mut`) or broken parent chain, while gating both `fwdVal` and `backFn` outputs with `handleFreeVal`.

---

### 3. Simultaneous Bijective Loan Relabeling Across Explicit CFG Joins (`[(2, 3), (3, 2)]` and Pre-`StorageDead` Handles)

Basis: source + derived

In `AeneasVerif/aeneas` (`src/interp/InterpMatchCtxs.ml:22–168`), context matching builds injective `MarkedUniqueBorrowId` and `MarkedLoanId` maps across branches. When lifting explicit CFG merges into a canonical post-join loan namespace via `joinPairs : List (LoanId × LoanId)` (aligning true-arm `tLid` with false-arm `fLid`), naive sequential `renameLoan tLid fLid` breaks on two common Rust patterns:

1. **Swapped loan cycles (`[(2, 3), (3, 2)]`):** Opposite-order borrows (`if c { p = &mut a; q = &mut b } else { q = &mut b; p = &mut a }`) yield `[(2, 3), (3, 2)]`. Sequential renaming `3 → 2` immediately collides with active loan `2`!
2. **Dead pre-`StorageDead` scratch handles:** A local variable holding a handle to an `.ended` borrow `5` before `StorageDead` executes often remains in `locals` at a join where the true arm allocates live loan `5`. Rejecting every occupied ID fails valid MIR, while overwriting `5` without renaming stale handles violates referential hygiene.

#### Simultaneous Two-Step Evacuation (`relabelJoinLoans`)

```lean
def relabelJoinLoans (alg : ValAlgebra Val) (pairs : List (LoanId × LoanId))
    (base : LoanId) (st : SymState Val) : Option (SymState Val) :=
  listFold (fun _ _ s => some s)
    (fun (tLid, fLid) rest ih i moved s =>
      if tLid == fLid then ih (i + 1) moved s
      else
        let src := match moved.find? (fun m => m.1 == fLid) with | some m => m.2 | none => fLid
        match findLoan src s.loans with
        | none => none
        | some eF =>
          if !eF.status.isActive then none
          else match renameLoanInState alg tLid src s with
          | some s' => ih (i + 1) moved s'
          | none =>
            match findLoan tLid s.loans with
            | none => none
            | some eT =>
              let movedLater := rest.any (fun q => q.1 != q.2 && q.2 == tLid)
              if !eT.status.isEnded && !(eT.status.isActive && movedLater) then none
              else match renameLoanInState alg (base + i) tLid s with
              | none => none
              | some s1 => match renameLoanInState alg tLid src s1 with
                | none => none
                | some s2 =>
                  let moved' := if eT.status.isActive then (tLid, base + i) :: moved else moved
                  ih (i + 1) moved' s2)
    pairs 0 [] st
```

Given `validJoinPairs` (bijectivity on `tLid` and `fLid`), `joinPairFits` (active loans in matching `LoanStatus`, never renaming root parameter loans), and `base > maxLoanId`: on `[(2, 3), (3, 2)]` with `base = 10`, step `0` sees `movedLater = true` for `2`, evacuates `2 → 10`, moves `3 → 2`, and records `(2, 10)` in `moved`; step `1` resolves `src = 10` via `moved` and moves `10 → 3` (leaving `10` as a harmless trailing `.ended` entry). Non-bijective pairs `[(3, 3), (6, 3)]` and live un-evacuated collisions `[(2, 5)]` fail closed (`none`).

---

### 4. Mixed Symbolic Early Returns (`ExecFlow.guardedContinuing`), Branch Projection, and CFG Handle-Freedom

Basis: derived

Rust's `?` operator and conditional `return` statements (`if sym_c { return e; }`) mix early returns with fallthrough paths under symbolic guards. Modeling evaluation with `ExecFlow Val := continuing st | returned out valClean mutOut | guardedContinuing wrapOut st valClean wrapMut` threads pending early-return wrappers `wrapOut : FuncOut Val → FuncOut Val` across subsequent statements, loops, and CFG blocks, governed by two invariants:

1. **Opposite-arm `.choice` projection (`projectBranchFuncOut` / `projectBranchMutRet`):** When an `if sym_c` branch returns `out1` on `true` and continues with `st` on `false`, subsequent joins along the fallthrough path can introduce `zipVal sym_c vA vB`. Wrapping the eventual fallthrough `outFall` requires projecting `projectBranchFuncOut alg sym_c false outFall` (`alg.projectBranchVal`) before merging via `mergeFuncOut`, preventing unreachable `sym_c = true` subterms from leaking into the `sym_c = false` wrapper.
2. **Inductive CFG handle-freedom (`handleFreeOutOpt`) & universal nondeterministic adequacy:** Routing every basic-block exit (`.ret`, `.jumpWrapped`, `.convergedJump`, `.branchJump`) through `handleFreeOutOpt` (`handleFreeVal alg out.ret && out.mutFinals.all (handleFreeVal alg)`) yields an inductive theorem (`runBlockCfg ... = .ret out → handleFreeOut alg out = true`), ensuring no frame-local borrow handle escapes via a wrapped early return. Binding CFG runs to structured plans via evidence-carrying `CfgCertificate { blocks, entryBb, fuel, plan, retExpr, sound }` prevents mismatched pairs. Crucially, when connecting lifted functions to a *nondeterministic* operational target (`M2`), existential trace adequacy (`∃ trace`) is unsound—certifying a stepping relation `0 ↦ .choice [1, 2]`, `1 ↦ .terminated 77`, `2 ↦ .failed` via arm `1` while arm `2` faults! Soundness under nondeterminism requires universal quantification (`∀ choice, ValidChoice p st choice → wpOutcomeState ...`).

---

### 5. Pre-Order Computable AST Serialization (`listFold` / `natFold`) and Single-Pass Linear State Destructuring

Basis: source + execution + derived

Strict trust-boundary auditors in Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`, `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e`, `leanprover/lean4checker@91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`) reject `partial def`, `noncomputable` recursive checkers, `Classical.choice`/`Quot.sound` in computational definitions, and equation-compiler `._unsafe_rec` artifacts. Lean `v4.34.1` explains why ordinary recursive AST evaluators fail these checks:
- `structuralRecursion` (`src/Lean/Elab/PreDefinition/Structural/Main.lean:183–199`) invokes `addAndCompilePartialRec docCtx preDefs` (`line 198`), generating auxiliary `._unsafe_rec` constants.
- `WellFounded.fix` (`src/Init/WF.lean:135–141`) is `noncomputable def`, and user-defined tree recursors `@Tree.rec` lack codegen without `noncomputable`.

**Solution (`listFold` + `natFold` + `@List.rec`):** Serializing recursive trees (`BackTargetStep`, `FlowPlanOp`) as flat pre-order `List` streams evaluated right-to-left via `listFold` (`List.foldr` from `src/Init/Data/List/Basic.lean:544–546` threading `(tail, ih)`) and `natFold` (`@Nat.recCompiled` from `src/Init/Data/Nat/Basic.lean:22–29`) achieves unbounded computable evaluation with **`0` `._unsafe_rec`**, **`0` `noncomputable`**, **`0` fixed depth truncation**, and **`0` `Classical.choice`/`Quot.sound`**. Defining auxiliary stack relations (`FnStackRel`) via `@List.rec` rather than recursive `def` avoids `FnStackRel._unsafe_rec` and `funext`/`Quot.sound` (`propext`-only).

#### Empirical Multi-Projection WHNF Cliff (`N = 20` Crash vs. `N = 64–80` Linear Scaling)

Under Lean 4's lazy call-by-name `whnf`, chaining 4 record field projections (`upd3 (upd2 (upd1 (upd0 d st)))`) over a `FlowPlanOp` stream duplicates `st` thunks exponentially ($O(4^N)$). Destructuring `st` once via `strictPlanState` (`match st with | PlanState.mk r0 r1 lg cs => k r0 r1 lg cs`) plus `strictNat` achieves $O(N)$ reduction. Measured on Lean `v4.34.1` (`-j1 -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `3` trials per passing case):

| Evaluator Mode | Plan Depth `N` (`1 + 2N` Ops) | Exit | Median Wall (`Min–Max`) | Max Peak RSS | Outcome |
| :--- | :---: | :---: | :--- | :---: | :--- |
| **Naive 4-step proj** | `16` (`33` ops) | `[0,0,0]` | `0.4128 s` (`0.3920–0.4563`) | `156.14 MiB` | `rfl` ok |
| **Naive 4-step proj** | **`20` (`41` ops)** | **`[1]`** | `0.4306 s` | `152.79 MiB` | **CRASH (`maxRecDepth`)** |
| **Linear `strictPlanState`** | `32` (`65` ops) | `[0,0,0]` | `0.5833 s` (`0.5478–0.6515`) | `171.56 MiB` | `rfl` ok |
| **Linear `strictPlanState`** | **`64` (`129` ops)** | **`[0,0,0]`** | **`1.2331 s`** (`1.1638–1.2830`) | **`204.44 MiB`** | **`rfl` ok** (`PlanState.mk 2081 45889 64 816529`) |
| **Linear `strictPlanState`** | `80` (`161` ops) | `[0]` (`1` run) | `1.7226 s` | `222.15 MiB` | `rfl` ok |
| **Linear `strictPlanState`** | **`96` (`193` ops)** | **`[1]`** | `0.5563 s` | `159.51 MiB` | **CRASH (`maxRecDepth` inside `List.foldr`/`++`)** |

Single-pass destructuring extends ground `rfl` evaluation `4×` (`N = 16 → 80`) and establishes **`<= 64` ops per compositional `seq` shard** (`<= 129` ops keeps RSS `< 205 MiB`; unsharded `193` ops overflows Lean's `512` `maxRecDepth`).

---

### 6. Why `Hold P` and `@[irreducible] def CutFirewall tag P := P` Fail to Block `rw`/`simp` vs. Key-Indexed `@[irreducible]` Barriers

Basis: source + execution + derived

In Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), `@[irreducible]` sets `ReducibilityStatus.irreducible` in `reducibilityCoreExt` (`src/Lean/ReducibilityAttrs.lean:35–55`), blocking unfolding of the *head constant* below `TransparencyMode.all`. However, `rw` (`src/Lean/Meta/Tactic/Rewrite.lean:47–52`, calling `kabstract e lhs config.occs`) and `simp` traverse directly into **explicit application arguments (`Expr.app fn arg`)** without unfolding `fn`! Consequently, both `structure Hold (P : Prop) : Prop where val : P` and `@[irreducible] def CutFirewall (_ : Nat) (P : Prop) : Prop := P` fail to shield explicit payload `P`:

| Shield Mechanism | Tactic on 64-Term / 256-Leaf Goal | Exit | Median Wall (`256`-Leaf `16`-Pass) | Max Peak RSS | Outcome |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `Hold (payloadChain ...)` | `rw` / `simp only` | `[0,0,0]` | `0.9423 s` / `0.9417 s` | `180.88 MiB` | **PENETRATED:** rewrote inside arg `P` |
| `@[irreducible] CutFirewall tag P` | `rw` / `simp only` | `[0,0,0]` | `0.9066 s` / `0.8556 s` | `183.29 MiB` | **PENETRATED:** congruence descended into `P` |
| `@[irreducible] CutBarrier ctx k` | `rw` (`Barrier256 x`) | **`[1]`** | **`0.7028 s`** (`-22.5%` vs `CF`) | **`171.80 MiB`** | **BLOCKED (`rc = 1`):** `Did not find an occurrence` |
| `@[irreducible] CutBarrier ctx k` | `simp only` (`Barrier256 x`) | **`[1]`** | **`0.6618 s`** (`-22.7%` vs `CF`) | **`172.06 MiB`** | **BLOCKED (`rc = 1`):** `` `simp` made no progress `` |

Keeping the heavy proposition behind an `@[irreducible]` named body `CutBarrier ctx k` blocks AST traversal (saving `22.5%–29.7%` wall time and `6.1–11.5 MiB` RSS at 256 leaves), provided `ctx` itself avoids inline reducible expressions (or is named via an anchor constant). Separately, passing algebraic dictionaries explicitly (`(dict : Carrier M)`) rather than via typeclasses (`[ClassCarrier M]`) improves marginal elaboration speed by **`1.58×` to `2.34×`** (`+114.2 ms` vs `+267.6 ms` on 32 layered framing lemmas; `-8.9%` `.olean` size on polymorphic lemmas).

---

## Boundaries

- **Higher-ranked function-pointer lifetimes (`for<'a> fn(&'a mut T)`) in Polonius/codegen (`not examined`):** Locally quantified arrow-type region binders (`RegionBinder<FunSig>`, `charon/src/ast/type_level/types.rs:63`) and dynamic codegen interaction were `not examined`.
- **Automatic cutpoint selection for irreducible multi-entry `goto` CFGs (`unknown`):** While `<= 64`-op `seq` sharding prevents `List.foldr` `maxRecDepth` overflows on structured `FlowPlan` trees, optimal automated sharding of arbitrary irreducible cyclic CFGs without SESE structuring remains `unknown`.
- **Sequential loan renaming on swaps, existential adequacy under nondeterminism, and `Hold`/`CutFirewall` rewrite blocking (`known not to apply`):** Sequential `renameLoan` without fresh `base + i` evacuation is `known not to apply` to swapped cycles `[(2, 3), (3, 2)]`; existential adequacy (`∃ trace`) is `known not to apply` as a soundness guarantee under nondeterminism; and `Hold P` / `@[irreducible] CutFirewall tag P` are `known not to apply` as `rw`/`simp` shields in Lean `v4.34.1`.
- **Locally bound `TFnPtr`/`TFnDef` regions and sub-abstractions in Aeneas, and unsharded `List.foldr` above `~190` ops (`unsupported`):** `AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f` marks locally bound `TFnPtr`/`TFnDef` regions (`src/llbc/RegionsHierarchy.ml:289–303`) and `abs_level > 0` sub-abstractions (`src/symbolic/SymbolicToPureAbs.ml:94, 181`) as `unsupported`; unsharded `List.foldr` at `N = 96` (`193` ops) is `unsupported` under Lean `v4.34.1`'s default `maxRecDepth = 512` without compositional `seq` sharding.

## Evidence

- **Primary Upstream Repositories (inspected `2026-11-20`):**
  - `AeneasVerif/aeneas` at `2e3d4488280bb8a95411db81019a7854a784861f`: `src/llbc/RegionsHierarchy.ml:47–486`; `src/symbolic/SymbolicToPureAbs.ml:14–237`; `src/interp/InterpMatchCtxs.ml:22–180`; `src/interp/InterpStatements.ml:334–345, 449–485`.
  - `AeneasVerif/charon` at `b23c297f57c0b2072de7967c7f17088db0278a8c`: `charon/src/ast/type_level/regions.rs:10–22`; `charon/src/ast/type_level/types.rs:23–64`.
  - `rust-lang/polonius` at `bfd4c945b7713d0e66a3cde80475d9a4494740df`: `polonius-engine/src/output/datafrog_opt.rs:19–62`.
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): `src/Lean/Elab/PreDefinition/Structural/Main.lean:183–199`; `src/Init/WF.lean:135–141`; `src/Init/Data/Nat/Basic.lean:20–30`; `src/Init/Data/List/Basic.lean:544–549`; `src/Lean/Meta/Tactic/Rewrite.lean:47–52`; `src/Lean/ReducibilityAttrs.lean:35–55`.
  - `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`) and `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`).
- **Peer-Reviewed Publications:**
  - Son Ho and Jonathan Protzenko, *"Aeneas: Rust Verification by Functional Translation"*, ICFP 2022, DOI `10.1145/3547647`.
  - Son Ho, Aymeric Fromherz, and Jonathan Protzenko, *"Sound Borrow-Checking for Rust via Symbolic Semantics"*, ICFP 2024, DOI `10.1145/3674640`.
  - Xavier Denis, Jacques-Henri Jourdan, and Claude Marché, *"Creusot: A Foundry for the Deductive Verification of Rust Programs"*, ICFEM 2022, DOI `10.1007/978-3-031-17244-1_6`.
  - Leonardo de Moura and Sebastian Ullrich, *"The Lean 4 Theorem Prover and Programming Language"*, CADE-28, 2021, DOI `10.1007/978-3-030-79876-5_37`.
- **Lean 4 (`v4.34.1`) Kernel Measurements & Standalone `prelude` Reproducer (`observed_at: 2026-11-20`):**
  Flags: `lean -j1 -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`MemorySwapMax=0`, `os.wait4` child timing/RSS). Save below to `/tmp/multiregion_probe.lean` and run to verify zero-axiom deposit commutativity and `CutBarrier` blocking:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.SimpLemmas

def takeChildDeposits {Val : Type} (children : List Nat) (deps : List (Nat × Val)) : List Val × List (Nat × Val) :=
  children.foldl (fun (acc : List Val × List (Nat × Val)) c =>
    match acc with
    | (taken, rest) => (taken ++ (rest.filter (fun d => d.1 == c)).map Prod.snd, rest.filter (fun d => d.1 != c))) ([], deps)

theorem takeChildDeposits_two_children_comm {Val : Type} (c1 c2 : Nat) (hNe : c1 ≠ c2) (v1 v2 : Val) :
    takeChildDeposits [c1, c2] [(c1, v1), (c2, v2)] = takeChildDeposits [c1, c2] [(c2, v2), (c1, v1)] := by
  have h12 : (c1 == c2) = false := beq_false_of_ne hNe
  have h21 : (c2 == c1) = false := beq_false_of_ne (fun h => hNe h.symm)
  dsimp only [takeChildDeposits, List.foldl, List.filter, List.map, bne]
  rw [BEq.rfl, h12, h21]
  dsimp only [Bool.not_false, Bool.not_true, List.nil_append, List.cons_append]

def stepFn (x : Nat) : Nat := Nat.add x 0
theorem stepFn_eq (x : Nat) : stepFn x = x := rfl
@[irreducible] def CutFirewall (_ : Nat) (P : Prop) : Prop := P
@[irreducible] def CutBarrier (x : Nat) : Prop := stepFn x = x

example (x : Nat) (h : CutFirewall 1 (stepFn x = x)) : CutFirewall 1 (x = x) := by rw [stepFn_eq] at h; exact h
example (x : Nat) : CutBarrier x := by fail_if_success rw [stepFn_eq]; unfold CutBarrier; exact stepFn_eq x
#print axioms takeChildDeposits_two_children_comm
```

## Revalidation

1. **Aeneas region hierarchy & sub-abstractions (`AeneasVerif/aeneas`):** Diff `src/llbc/RegionsHierarchy.ml` and `src/symbolic/SymbolicToPureAbs.ml` against `2e3d4488280bb8a95411db81019a7854a784861f`.
2. **Lean 4 recursion & rewrite engine (`leanprover/lean4`):** Diff `src/Lean/Elab/PreDefinition/Structural/Main.lean` and `src/Lean/Meta/Tactic/Rewrite.lean` against `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
3. **Standalone Lean 4 kernel probe:** Run `lean -j1 -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/multiregion_probe.lean` and confirm `rc = 0`, `does not depend on any axioms` (`[]`), and `fail_if_success rw [stepFn_eq]` passing on `CutBarrier`.
