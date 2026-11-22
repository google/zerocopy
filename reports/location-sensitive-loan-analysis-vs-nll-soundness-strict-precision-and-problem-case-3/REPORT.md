# Location-sensitive loan analysis vs. location-insensitive regions: soundness, strict precision, and problem case #3

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved. Connections to documented designs of real systems are separate `derived (modeling bridge)` claims (Findings, Modeling bridges; Evidence, Primary sources), and no real compiler or engine was executed. Lean project: `lean/` (library `ToyLoanFlow`, namespace `Toy.LoanFlow`), Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean without Mathlib or external dependencies. Every theorem, definition example, tightness counterexample, non-vacuity witness, and positive control is proved; `Lean.collectAxioms` across all 657 declarations in `ToyLoanFlow` reports at most `propext`, `Classical.choice`, and `Quot.sound` (Evidence).

- **R1a** (Soundness of the location-insensitive checker). For every toy program `p` (any finite CFG over `Fin n`, cycles allowed, any number `m` of locals) that is well typed at every node of `Fin n`, reachable from `p.entry` or not (`WellTyped p`), and that the location-insensitive checker accepts (`NLLAccepts p`, which tests every node of `Fin n` against every loan in scope there), no walk `π` of `p.succ` with `π.head? = some p.entry` reaches UB when `run p RState.init π` executes it one `exec` step per node (`Safe p`).
- **R1c** (Soundness of the location-sensitive checker (any CFG)). For every toy program `p` (any finite CFG over `Fin n`, cycles allowed, any number `m` of locals) that is well typed at every node of `Fin n`, reachable from `p.entry` or not (`WellTyped p`), and that the location-sensitive checker accepts (`LSAccepts p`: kills at overwrites, invariant `&mut`, every node of `Fin n` tested), no walk `π` of `p.succ` with `π.head? = some p.entry` reaches UB when `run p RState.init π` executes it one `exec` step per node (`Safe p`).
- **R2** (The location-sensitive checker accepts whatever the location-insensitive one accepts). For every variance mode `vm` (`VarMode.inv` or `VarMode.cov`) and every toy program `p` that is well typed at every node of `Fin n`, reachable from `p.entry` or not (`WellTyped p`), if the location-insensitive checker with that variance mode accepts `p` (`NLL.Accepts vm p`), then the location-sensitive checker with kills at overwrites and the same variance mode accepts `p` (`LS.Accepts .overwrite vm p`).
- **R3a** (Strictness on problem case #3). The toy program `pc3` (6 nodes, exactly 3 locals), a rendering of RFC 2094's Problem case #3 (`r := &mut x`; a nondeterministic branch to `return r` or to `write x; s := &mut x; return s`), is well typed (`WellTyped pc3`) and safe (`Safe pc3`: no walk of `pc3.succ` from `pc3.entry` reaches UB under `run` from `RState.init`), the location-sensitive checker accepts it (`LSAccepts pc3`), and the location-insensitive checker rejects it (`¬ NLLAccepts pc3`).
- **R3b** (Strictness on a loop variant of problem case #3). The toy program `pc3Loop` (4 nodes, exactly 2 locals, one back edge), in which a mutable borrow of the plain-data local `x` taken inside a loop is either returned or followed by a write of `x` and another iteration, is well typed (`WellTyped pc3Loop`) and safe (`Safe pc3Loop`, under `run` from `RState.init`), the location-sensitive checker accepts it (`LSAccepts pc3Loop`), and the location-insensitive checker rejects it (`¬ NLLAccepts pc3Loop`).
- **R3c** (The mechanism in problem case #3). In `pc3`, node `3` (the write of `x`) conflicts with the loan created at node `0` (`Conflicts pc3 0 3`); the outermost origin `(1, 0)` of the returned local `r` contains every node of `pc3` (`NLL.InRegion .inv pc3 (1, 0) q` for every `q : Fin 6`), and that loan is in scope at node `3` for the location-insensitive checker (`NLL.InScope .inv pc3 0 3`); it is not live at node `3` for the location-sensitive checker (`¬ LS.LoanLive .overwrite .inv pc3 0 3`).
- **R4a** (Removing kills from `LS.Holds`). The toy program `pReassign` (`r := &mut x; write *r; r := &mut y; write x; write *r`; 5 nodes, exactly 3 locals) is well typed, safe (`Safe pReassign`, under `run` from `RState.init`), accepted by the location-insensitive checker (`NLLAccepts pReassign`) and by the location-sensitive checker (`LSAccepts pReassign`), and rejected by the location-sensitive variant whose propagation along CFG edges is limited neither by kills nor by liveness (`¬ LS.Accepts .none .inv pReassign`).
- **R4b** (Kills at copy sources are unsound). The toy program `pCopyThenUse` (`r := &mut x; s := r; write x; write *r`; 4 nodes, exactly 3 locals) is well typed and not safe (there is a walk from its entry that reaches UB under `run` from `RState.init`), the location-sensitive checker with additional kills at copy sources accepts it (`LS.Accepts .overwriteAndCopySrc .inv pCopyThenUse`), and the checker with kills at overwrites alone rejects it (`¬ LSAccepts pCopyThenUse`). The shared-reference program `pCopyThenUseShr` (`r := &x; s := r; write x; read *r`) satisfies the same four statements.
- **R4c** (Kills at overwrites are equivalent to liveness gating). For every variance mode `vm` and every toy program `p` (well typed or not, any CFG), the location-sensitive checker with kills at overwrites accepts `p` (`LS.Accepts .overwrite vm p`) if and only if the liveness-gated variant without kills accepts `p` (`LS.LiveAccepts vm p`); more precisely, for every loan `l` and node `q`, `LS.LoanLive .overwrite vm p l q ↔ LS.LiveLoanLive vm p l q` (`lsLoanLive_overwrite_iff_liveLoanLive`).
- **R5** (Invariance of `&mut T` in `T`). The toy program `pVariance` (`c := &x; pp := &mut c; s := &y; *pp := s; write y; read *c`; 6 nodes, exactly 5 locals) is well typed and not safe (there is a walk from its entry that reaches UB under `run` from `RState.init`); with `&mut T` treated as covariant in `T` (`VarMode.cov`) both checkers accept it (`LS.Accepts .overwrite .cov pVariance`, `NLL.Accepts .cov pVariance`), and with the invariant rule both reject it (`¬ LSAccepts pVariance`, `¬ NLLAccepts pVariance`).

Non-claims, unexamined extensions, proved failures of weakened statements, and escape hatches appear first in Boundaries and on each card in Findings.

## Applicability

**Model fidelity and scope.** `Toy.LoanFlow` is a self-contained finite-CFG toy model, not a mirror of rustc MIR or of any Polonius implementation. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.

The model captures two static borrow-checking disciplines over the same finite control-flow graph `Prog n m` (`n` nodes in `Fin n`, `m` locals in `Fin m`, multi-layer `&` / `&mut` types `List Mutbl`, and statement-generated outlives pairs `gen`):

1. a **location-insensitive region checker** (`NLL.InRegion`, `NLL.InScope`, `NLL.Accepts`, `NLLAccepts`), where each origin `(v, k)` denotes a single set of CFG nodes closed globally under variable liveness, outlives constraints generated anywhere in the body, and a universal-region rule putting every node of `Fin n` into the outermost origin `(v, 0)` of any local returned by `Stmt.ret v`; and
2. a **location-sensitive loan-flow checker** (`LS.SubAt`, `LS.Holds`, `LS.LoanLive`, `LS.Accepts`, `LSAccepts`) together with its zero-kill liveness-gated counterpart (`LS.LiveHolds`, `LS.LiveLoanLive`, `LS.LiveAccepts`), where subset relations and loan-containment facts are tracked per CFG node and loans flow along successor edges subject to holder-overwrite kills (`KillMode.overwrite`) or target-entry origin liveness (`LiveAt`).

Both checkers are judged against an operational reference machine (`Rec`, `RState`, `exec`, `run`, `Safe`) in the tag-invalidation style of Stacked Borrows and Tree Borrows: each `Stmt.borrow mu d s` at node `q` mints a fresh record `⟨s, mu, q, true⟩`, conflicting direct or through-reference reads and writes invalidate incompatible tags across all locals, and `deref`, `store`, or `ret` on a record with `valid = false` yields `Outcome.ub`.

**Known gaps between the toy model and Rust / MIR / Polonius:**

- **Places and loans:** Every local holds either plain opaque data (`ty v = []`) or a reference value (`Rec n m`). There are no struct fields, projections, slices, heap allocations, reads of a reference through a reference (`t := *p`), reborrow loans (`&mut *r`), or loans on places behind references. Consequently, Polonius's `loan_killed_at` rule (assignment to a prefix of the borrowed path) has no counterpart; `killsAt .overwrite` instead drops origins of an overwritten reference-holding local.
- **Copies without moves:** `Stmt.copy d s` copies a reference of either mutability keeping its tag, so two locals holding copies of one mutable record share one tag permission; `WellTyped` includes no move checker.
- **Initialization and `none` halting:** `RState.init` initializes all `m` locals to `none`, `WellTyped` performs no definite-initialization check, and `exec` maps `deref`, `store`, and `ret` on `none` (as well as writes through `.shr`) to `Outcome.halt`, not `Outcome.ub`.
- **No `StorageDead` or stack deallocation on `ret`:** Every plain-data local stands for storage outliving the body (such as `*map` behind a parameter), and `Stmt.ret v` checks validity of `v`'s record and halts without deallocating locals or continuing execution in a caller.
- **Depth-1 `deref` and `ret`:** `StmtWellTyped` restricts `deref` and `ret` to depth-1 references (`[.shr]` or `[.mut]`); higher-depth references (`k ≥ 1`, e.g. `[.mut, .shr]` in `pVariance` and `pStoreSafe`) are created by `borrow`, copied by `copy`, and mutated through `Stmt.store`, which moves a depth-1 record into the target local where a subsequent `deref` or `ret` observes it.
- **Control flow and quantifiers:** Branching in `p.succ : Fin n → List (Fin n)` is nondeterministic (branch conditions are unmodelled), and `WellTyped`, `Acyclic`, `NLL.Accepts`, `LS.Accepts`, and `LS.LiveAccepts` quantify over every node of `Fin n`, reachable from `p.entry` or not.
- **Degenerate edges and arithmetic:** At `n = 0`, `Prog 0 m` is uninhabited because `entry : Fin 0`. At `m = 0` (`n ≥ 1`), `Fin 0` is empty so every node's statement is `Stmt.nop`, and `WellTyped`, `Safe`, and all checker acceptance predicates hold. Origin layer indices (`Origin m = Fin m × Nat`) use `Nat` indexing (`0` = outermost) via `<` and `+`; no truncating `Nat` subtraction, division, modulo, or fixed-width wrapping arithmetic occurs in any definition or statement.

**Relation among the subjects in `REPORT.json`.** The Lean 4 toolchain (`leanprover/lean4` `v4.34.1`, revision `5045d0056413266e57c625dcd7c365b10e377c52`) is the kernel verifier of the `ToyLoanFlow` library; no Mathlib or external Lake package is used. Rust RFC 2094 (`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`), the `rustc-dev-guide` region-inference chapters (`rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11`), the Polonius book (`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`), Matsakis's 2018 and 2023 blog posts (`nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687`), and the Rust project Polonius posts (`rust-lang/blog.rust-lang.org@8666f7c3a86260ec58e4d914d451b14613c690a4`) are upstream design and documentation artifacts compared to the toy definitions in `derived (modeling bridge)` prose (`B1`–`B6`). Stacked Borrows (`doi:10.1145/3371109`) and Tree Borrows (`doi:10.1145/3735592`) motivate the tag-invalidation operational style of `exec`, while RustBelt (`doi:10.1145/3158154`), Ho et al. (`doi:10.1145/3674640`), Oxide (`arXiv:1903.00982v4`), Pearce (`doi:10.1145/3443420`), RefinedRust (`doi:10.1145/3656422`), and Place Capability Graphs (`doi:10.1145/3763122`) situate related formalizations of Rust borrowing.

### Definitions

Every package-local `def` or `abbrev` value/predicate (excluding `Type`/`Sort` formers) appearing directly in any card's verbatim `lean` theorem statement is listed below, with its characterization, positive/negative test pair, or short-body (`≤ 120` chars, quantifier-alternation-free) transparency status.

| Definition | Status | Notes |
| :--- | :--- | :--- |
| `WellTyped` | `tests: Toy.LoanFlow.pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts, Toy.LoanFlow.lsAccepts_not_safe_without_wellTyped` | Requires `StmtWellTyped` at every node of `Fin n` (reachable from `p.entry` or not), with no definite-initialization or move check. |
| `Safe` | `tests: Toy.LoanFlow.pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts, Toy.LoanFlow.wellTyped_acyclic_not_safe` | Tests walks of `p.succ` from `p.entry` under `run` from `RState.init`; `deref`, `store`, and `ret` on `none` halt (`.halt`) rather than reaching `.ub`. |
| `Conflicts` | `transparent` | 90-char existential over `loanOf` and `Stmt.accesses`: write to the borrowed local, or any access to the source of a mutable loan. |
| `LS.LoanLive` | `characterized: Toy.LoanFlow.lsLoanLive_overwrite_iff_liveLoanLive` | At `KillMode.overwrite`, equivalent to `LS.LiveLoanLive` for every `vm`, `p`, `l`, and `q`; 84-char existential over predecessor `LS.Holds` and entry `LiveAt`. |
| `LS.Accepts` | `characterized: Toy.LoanFlow.lsAccepts_overwrite_iff_liveAccepts` | At `KillMode.overwrite`, equivalent to `LS.LiveAccepts` for every `vm` and `p`; tests all `(l, q)` in `Fin n × Fin n` with `Conflicts p l q`. |
| `LSAccepts` | `tests: Toy.LoanFlow.pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts, Toy.LoanFlow.pCopyThenUse_not_lsAccepts` | Abbreviation fixing `KillMode.overwrite` and `VarMode.inv` in `LS.Accepts`. |
| `LS.LiveLoanLive` | `transparent` | 85-char existential matching `LS.LoanLive` with `LS.LiveHolds` in place of `LS.Holds` (equivalent to `LS.LoanLive .overwrite` by `lsLoanLive_overwrite_iff_liveLoanLive`). |
| `LS.LiveAccepts` | `transparent` | 56-char universal over `Fin n × Fin n` matching `LS.Accepts` with `LS.LiveLoanLive` in place of `LS.LoanLive` (equivalent to `LS.Accepts .overwrite` by `lsAccepts_overwrite_iff_liveAccepts`). |
| `NLL.Accepts` | `transparent` | 51-char universal over `Fin n × Fin n` testing every `(l, q)` with `Conflicts p l q` against `NLL.InScope vm p l q`. |
| `NLLAccepts` | `tests: Toy.LoanFlow.pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts, Toy.LoanFlow.pVariance_not_nllAccepts` | Abbreviation fixing `VarMode.inv` in `NLL.Accepts`. |
| `pc3` | `tests: Toy.LoanFlow.pc3_loan0_at_insertion, Toy.LoanFlow.pc3_wellTyped_safe_lsAccepts_not_nllAccepts` | Closed 6-node branching `Prog 6 3` rendering Problem Case #3 (`r := &mut x`; branch to `return r` or `write x; s := &mut x; return s`). |
| `pReassign` | `tests: Toy.LoanFlow.refuted_result2_needs_kills, Toy.LoanFlow.pReassign_r_dead_at_2` | Closed 5-node straight-line `Prog 5 3` overwriting `r` at node `2` before writing `x` at node `3`. |
| `pCopyThenUse` | `tests: Toy.LoanFlow.pCopyThenUse_lsCopySrcKill_accepts, Toy.LoanFlow.pCopyThenUse_not_lsAccepts` | Closed 4-node `Prog 4 3` copying `&mut D` (`r := &mut x; s := r; write x; write *r`): accepted with copy-source kills, unsafe (`pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe`) and rejected by `LSAccepts`. |
| `pc3Loop` | `tests: Toy.LoanFlow.pc3Loop_safe, Toy.LoanFlow.pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts` | Closed 4-node cyclic `Prog 4 2` (back edge `3 → 0`) borrowing plain-data local `0`: safe and accepted by `LSAccepts`, rejected by `NLLAccepts`. |
| `pCopyThenUseShr` | `tests: Toy.LoanFlow.pCopyThenUseShr_lsCopySrcKill_accepts, Toy.LoanFlow.pCopyThenUseShr_not_lsAccepts` | Closed 4-node `Prog 4 3` copying shared `&D` (`r := &x; s := r; write x; read *r`): accepted with copy-source kills, unsafe (`pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe`) and rejected by `LSAccepts`. |
| `pVariance` | `tests: Toy.LoanFlow.pVariance_lsCov_accepts, Toy.LoanFlow.pVariance_not_lsAccepts` | Closed 6-node `Prog 6 5` storing `&y` through `&mut &D`: accepted under `VarMode.cov`, unsafe (`pVariance_wellTyped_covAccepts_not_safe`) and rejected under `VarMode.inv`. |

### Model definitions

#### `Mutbl`

Mutability of one reference layer.

```lean
-- ToyLoanFlow/Syntax.lean:16-18
/-- Mutability of one reference layer. -/
inductive Mutbl | shr | mut
  deriving DecidableEq, Repr
```

#### `Acc`

Read or write.

```lean
-- ToyLoanFlow/Syntax.lean:20-22
/-- Kind of an access. -/
inductive Acc | rd | wr
  deriving DecidableEq, Repr
```

#### `Stmt`

The statements of the toy language.

```lean
-- ToyLoanFlow/Syntax.lean:24-36
/-- Statements. `borrow mu d s` is `d := &mu s` (a new loan identified by the node that
executes it); `copy d s` is `d := s` (the reference value is copied, keeping its loan);
`deref a v` reads (`rd`) or writes (`wr`) the data behind `v`; `access a v` reads or writes the
local `v` itself; `store p s` is `*p := s`; `ret v` returns `v` to the caller. -/
inductive Stmt (m : Nat)
  | nop
  | borrow (mu : Mutbl) (d s : Fin m)
  | copy (d s : Fin m)
  | deref (a : Acc) (v : Fin m)
  | access (a : Acc) (v : Fin m)
  | store (p s : Fin m)
  | ret (v : Fin m)
  deriving DecidableEq, Repr
```

#### `Edges`

Successor lists.

```lean
-- ToyLoanFlow/Syntax.lean:38-39
/-- Successor lists over the nodes `Fin n`. -/
abbrev Edges (n : Nat) := Fin n → List (Fin n)
```

#### `Prog`

A function body: entry node, successor lists, one statement per node, declared types of the locals.

```lean
-- ToyLoanFlow/Syntax.lean:41-47
/-- A function body: entry node, successor lists, one statement per node, and the declared
type (reference layers, outermost first) of every local. -/
structure Prog (n m : Nat) where
  entry : Fin n
  succ : Edges n
  stmt : Fin n → Stmt m
  ty : Fin m → List Mutbl
```

#### `Origin`

A region variable: one per reference layer of each local.

```lean
-- ToyLoanFlow/Syntax.lean:49-50
/-- An origin (region variable): local `v`, reference layer `k` (`0` = outermost). -/
abbrev Origin (m : Nat) := Fin m × Nat
```

#### `Stmt.defs`

Locals overwritten by a statement.

```lean
-- ToyLoanFlow/Syntax.lean:56-60
/-- Locals overwritten by the statement. -/
def defs : Stmt m → List (Fin m)
  | .borrow _ d _ => [d]
  | .copy d _ => [d]
  | _ => []
```

#### `Stmt.uses`

Locals read by a statement.

```lean
-- ToyLoanFlow/Syntax.lean:62-71
/-- Locals read (mentioned other than as the overwritten destination). A borrow of `s` counts
as a use of `s`. -/
def uses : Stmt m → List (Fin m)
  | .nop => []
  | .borrow _ _ s => [s]
  | .copy _ s => [s]
  | .deref _ v => [v]
  | .access _ v => [v]
  | .store p s => [p, s]
  | .ret v => [v]
```

#### `Stmt.accesses`

Accesses to locals-as-places tested against live loans.

```lean
-- ToyLoanFlow/Syntax.lean:73-86
/-- Accesses to locals-as-places that the borrow checkers test against live loans: a mutable
borrow writes (for conflict purposes) its source and a shared borrow reads it; overwriting a
local writes it; every other mention of a local reads it. Accesses through a reference (the
data behind `deref`, the target of `store`) are not tested: the toy has no reborrow loans, so no
loan is ever taken on the place behind a reference. -/
def accesses : Stmt m → List (Fin m × Acc)
  | .nop => []
  | .borrow .mut d s => [(s, .wr), (d, .wr)]
  | .borrow .shr d s => [(s, .rd), (d, .wr)]
  | .copy d s => [(s, .rd), (d, .wr)]
  | .deref _ v => [(v, .rd)]
  | .access a v => [(v, a)]
  | .store p s => [(p, .rd), (s, .rd)]
  | .ret v => [(v, .rd)]
```

#### `VarMode`

The sound (`inv`) and the covariant (`cov`) treatment of layers nested inside `&mut`.

```lean
-- ToyLoanFlow/Syntax.lean:92-96
/-- How the constraint generator treats a reference layer nested inside `&mut`:
`inv` (the sound rule, two-way constraints) or `cov` (the ablation treating `&mut T` as
covariant in `T`, one-way constraints). -/
inductive VarMode | inv | cov
  deriving DecidableEq, Repr
```

#### `invariantAt`

Whether a layer is invariant.

```lean
-- ToyLoanFlow/Syntax.lean:98-103
/-- Layer `k` of type `T` is invariant iff some layer strictly outside it is `mut`
(and the mode is `inv`). -/
def invariantAt (vm : VarMode) (T : List Mutbl) (k : Nat) : Bool :=
  match vm with
  | .inv => (T.take k).contains .mut
  | .cov => false
```

#### `relate`

Constraints relating the layers of two values of the same type.

```lean
-- ToyLoanFlow/Syntax.lean:105-114
/-- Constraints relating layer `k` of a value of type `T` held in origins `(a, k + da)` to the
layer `k` of a destination typed `T` held in origins `(b, k + db)`: for every layer `k < |T|`,
`(a, k+da) ⊆ (b, k+db)` (loans flow from the value into the destination), and also the reverse
pair when layer `k` is invariant. Pairs `(o₁, o₂)` are read "loans of `o₁` flow into `o₂`",
i.e. the outlives constraint `o₁ : o₂`. -/
def relate (vm : VarMode) (T : List Mutbl) (a : Fin m) (da : Nat) (b : Fin m) (db : Nat) :
    List (Origin m × Origin m) :=
  (List.range T.length).flatMap fun k =>
    if invariantAt vm T k then [((a, k + da), (b, k + db)), ((b, k + db), (a, k + da))]
    else [((a, k + da), (b, k + db))]
```

#### `gen`

Outlives constraints generated at a node.

```lean
-- ToyLoanFlow/Syntax.lean:116-128
/-- Outlives constraints generated by the statement at a node. `d := &mu s` relates layer `k`
of `s` to layer `k+1` of `d` with the variance of layer `k+1` in `mu :: ty s`; `d := s` relates
equal layers; `*p := s` relates layer `k` of `s` to layer `k+1` of `p`. The outermost layer of
the new loan's own region is handled by loan introduction, not by a constraint. -/
def gen (vm : VarMode) (p : Prog n m) (q : Fin n) : List (Origin m × Origin m) :=
  match p.stmt q with
  | .borrow mu d s =>
      (List.range (p.ty s).length).flatMap fun k =>
        if invariantAt vm (mu :: p.ty s) (k + 1) then [((s, k), (d, k + 1)), ((d, k + 1), (s, k))]
        else [((s, k), (d, k + 1))]
  | .copy d s => relate vm (p.ty s) s 0 d 0
  | .store q' s => relate vm (p.ty s) s 0 q' 1
  | _ => []
```

#### `StmtWellTyped`

Statement-level typing.

```lean
-- ToyLoanFlow/Syntax.lean:132-143
/-- The statement at a node is well typed: `d := &mu s` needs `ty d = mu :: ty s`; `d := s`
needs equal reference types; `deref` needs a reference to data (`mut` for a write); `access`
needs plain data; `*p := s` needs `ty p = mut :: ty s`; `ret v` needs a reference to data. -/
def StmtWellTyped (p : Prog n m) : Stmt m → Prop
  | .nop => True
  | .borrow mu d s => p.ty d = mu :: p.ty s
  | .copy d s => p.ty d = p.ty s ∧ p.ty s ≠ []
  | .deref .rd v => p.ty v = [.shr] ∨ p.ty v = [.mut]
  | .deref .wr v => p.ty v = [.mut]
  | .access _ v => p.ty v = []
  | .store q s => p.ty q = .mut :: p.ty s
  | .ret v => p.ty v = [.shr] ∨ p.ty v = [.mut]
```

#### `WellTyped`

Every node of `Fin n`, reachable from `p.entry` or not, is well typed.

```lean
-- ToyLoanFlow/Syntax.lean:155-156
/-- Every node's statement is well typed. -/
def WellTyped (p : Prog n m) : Prop := ∀ q : Fin n, StmtWellTyped p (p.stmt q)
```

#### `loanOf`

The loan created at a node.

```lean
-- ToyLoanFlow/Syntax.lean:160-164
/-- The loan created at node `l`, if `l` is a borrow: its source local and mutability. -/
def loanOf (p : Prog n m) (l : Fin n) : Option (Fin m × Mutbl) :=
  match p.stmt l with
  | .borrow mu _ s => some (s, mu)
  | _ => none
```

#### `loanDst`

The local receiving the loan created at a node.

```lean
-- ToyLoanFlow/Syntax.lean:166-170
/-- The local that receives the loan created at node `l`, if `l` is a borrow. -/
def loanDst (p : Prog n m) (l : Fin n) : Option (Fin m) :=
  match p.stmt l with
  | .borrow _ d _ => some d
  | _ => none
```

#### `Conflicts`

An access at `q` conflicts with the loan created at `l`.

```lean
-- ToyLoanFlow/Syntax.lean:172-175
/-- Node `q` performs an access that conflicts with the loan created at `l`: a write to the
loan's source, or any access to the source of a mutable loan. -/
def Conflicts (p : Prog n m) (l q : Fin n) : Prop :=
  ∃ s mu a, loanOf p l = some (s, mu) ∧ (s, a) ∈ (p.stmt q).accesses ∧ (a = .wr ∨ mu = .mut)
```

#### `IsWalk`

Walks along successor lists.

```lean
-- ToyLoanFlow/Semantics.lean:36-42
/-- `IsWalk E π`: `π` is a nonempty list of nodes in which each node is followed by one of
its `E`-successors. (Copied from `lean/ToyTwoPhase/Graph.lean:20-25` of the package cited above,
git blob `d80d4d0f36d0386d3ec3d32cdba33afb4e5e4a8d` at the commit cited above.) -/
def IsWalk (E : Edges n) : List (Fin n) → Prop
  | [] => False
  | [_] => True
  | a :: b :: rest => b ∈ E a ∧ IsWalk E (b :: rest)
```

#### `Reach`

Reflexive-transitive reachability.

```lean
-- ToyLoanFlow/Semantics.lean:53-56
/-- Reflexive-transitive reachability along `E`. -/
inductive Reach (E : Edges n) : Fin n → Fin n → Prop
  | refl (u : Fin n) : Reach E u u
  | step {u v w : Fin n} : v ∈ E u → Reach E v w → Reach E u w
```

#### `Rec`

A reference value (record).

```lean
-- ToyLoanFlow/Semantics.lean:58-64
/-- A reference value. -/
structure Rec (n m : Nat) where
  tgt : Fin m
  mu : Mutbl
  tag : Fin n
  valid : Bool
  deriving DecidableEq, Repr
```

#### `RState`

Machine state: the record held by each local.

```lean
-- ToyLoanFlow/Semantics.lean:66-68
/-- Machine state: the record (if any) held by each local, as a list indexed by the local's
number (entries beyond the list read as `none`). -/
abbrev RState (n m : Nat) := List (Option (Rec n m))
```

#### `RState.get`

The record held by a local.

```lean
-- ToyLoanFlow/Semantics.lean:70-71
/-- The record held by local `v`. -/
def RState.get (σ : RState n m) (v : Fin m) : Option (Rec n m) := (σ[v.val]?).getD none
```

#### `RState.init`

Initial state: no local holds a record.

```lean
-- ToyLoanFlow/Semantics.lean:73-74
/-- Initial state: no local holds a reference. -/
def RState.init : RState n m := List.replicate m none
```

#### `Outcome`

Result of one step.

```lean
-- ToyLoanFlow/Semantics.lean:76-80
/-- Result of executing one node. -/
inductive Outcome (n m : Nat)
  | ok (σ : RState n m)
  | halt
  | ub
```

#### `invalidate`

Invalidate selected records.

```lean
-- ToyLoanFlow/Semantics.lean:82-84
/-- Invalidate the records selected by `sel`. -/
def invalidate (sel : Rec n m → Bool) (σ : RState n m) : RState n m :=
  σ.map fun x => x.map fun R => if sel R then { R with valid := false } else R
```

#### `placeWrite`

Place write.

```lean
-- ToyLoanFlow/Semantics.lean:86-88
/-- Place write to local `t`. -/
def placeWrite (t : Fin m) : RState n m → RState n m :=
  invalidate fun R => R.tgt == t
```

#### `placeRead`

Place read.

```lean
-- ToyLoanFlow/Semantics.lean:90-92
/-- Place read of local `t`. -/
def placeRead (t : Fin m) : RState n m → RState n m :=
  invalidate fun R => R.tgt == t && R.mu == .mut
```

#### `thruWrite`

Write through a record.

```lean
-- ToyLoanFlow/Semantics.lean:94-96
/-- Write through record `R`. -/
def thruWrite (R : Rec n m) : RState n m → RState n m :=
  invalidate fun R' => R'.tgt == R.tgt && R'.tag != R.tag
```

#### `thruRead`

Read through a record.

```lean
-- ToyLoanFlow/Semantics.lean:98-100
/-- Read through record `R`. -/
def thruRead (R : Rec n m) : RState n m → RState n m :=
  invalidate fun R' => R'.tgt == R.tgt && R'.mu == .mut && R'.tag != R.tag
```

#### `RState.set`

Update one local.

```lean
-- ToyLoanFlow/Semantics.lean:102-104
/-- Update one local. -/
def RState.set (σ : RState n m) (v : Fin m) (x : Option (Rec n m)) : RState n m :=
  List.set σ v.val x
```

#### `exec`

One step of the reference semantics (the ground truth).

```lean
-- ToyLoanFlow/Semantics.lean:106-143
/-- One step of the reference semantics at node `q`. -/
def exec (p : Prog n m) (q : Fin n) (σ : RState n m) : Outcome n m :=
  match p.stmt q with
  | .nop => .ok σ
  | .borrow mu d s =>
      let σ1 := (match mu with | .mut => placeWrite s σ | .shr => placeRead s σ)
      .ok ((placeWrite d σ1).set d (some ⟨s, mu, q, true⟩))
  | .copy d s =>
      let σ1 := placeRead s σ
      .ok ((placeWrite d σ1).set d (σ1.get s))
  | .deref a v =>
      let σ1 := placeRead v σ
      match σ1.get v with
      | none => .halt
      | some R =>
        if R.valid = false then .ub
        else match a, R.mu with
          | .rd, _ => .ok (thruRead R σ1)
          | .wr, .mut => .ok (thruWrite R σ1)
          | .wr, .shr => .halt
  | .access a v =>
      match a with
      | .rd => .ok (placeRead v σ)
      | .wr => .ok (placeWrite v σ)
  | .store q' s =>
      let σ1 := placeRead s (placeRead q' σ)
      match σ1.get q' with
      | none => .halt
      | some R =>
        if R.valid = false then .ub
        else match R.mu with
          | .shr => .halt
          | .mut => .ok ((thruWrite R σ1).set R.tgt (σ1.get s))
  | .ret v =>
      let σ1 := placeRead v σ
      match σ1.get v with
      | none => .halt
      | some R => if R.valid = false then .ub else .halt
```

#### `run`

Execution of a list of nodes, one `exec` step per node.

```lean
-- ToyLoanFlow/Semantics.lean:145-152
/-- Execute the nodes of a list in order from state `σ`. -/
def run (p : Prog n m) : RState n m → List (Fin n) → Outcome n m
  | σ, [] => .ok σ
  | σ, i :: rest =>
    match exec p i σ with
    | .ok σ' => run p σ' rest
    | .halt => .halt
    | .ub => .ub
```

#### `Outcome.isUB`

Whether an outcome is UB.

```lean
-- ToyLoanFlow/Semantics.lean:154-157
/-- `run` reaches UB. -/
def Outcome.isUB : Outcome n m → Bool
  | .ub => true
  | _ => false
```

#### `Safe`

No walk from the entry node reaches UB under `run` from `RState.init`.

```lean
-- ToyLoanFlow/Semantics.lean:159-161
/-- `Safe p`: no walk from `entry` reaches UB. -/
def Safe (p : Prog n m) : Prop :=
  ∀ π : List (Fin n), IsWalk p.succ π → π.head? = some p.entry → (run p RState.init π).isUB = false
```

#### `ReachesUB`

A walk from the entry node whose execution reaches UB.

```lean
-- ToyLoanFlow/Semantics.lean:163-165
/-- `ReachesUB p π`: `π` is a walk from `entry` whose execution reaches UB. -/
def ReachesUB (p : Prog n m) (π : List (Fin n)) : Prop :=
  IsWalk p.succ π ∧ π.head? = some p.entry ∧ (run p RState.init π).isUB = true
```

#### `LiveAt`

Liveness of a local on entry to a node.

```lean
-- ToyLoanFlow/Analyses.lean:31-36
/-- `LiveAt p v q`: local `v` is live on entry to node `q`: some walk from `q` reaches a node
that uses `v` without first passing a node that overwrites `v` (a node that both uses and
overwrites `v` counts as a use). -/
inductive LiveAt (p : Prog n m) (v : Fin m) : Fin n → Prop
  | use {q : Fin n} : v ∈ (p.stmt q).uses → LiveAt p v q
  | step {q q' : Fin n} : v ∉ (p.stmt q).defs → q' ∈ p.succ q → LiveAt p v q' → LiveAt p v q
```

#### `KillMode`

Kill rules of the location-sensitive checker.

```lean
-- ToyLoanFlow/Analyses.lean:38-46
/-- Where the location-sensitive checker drops loans from an origin: `none` (never — the
ablation without kills), `overwrite` (at a node that overwrites the origin's local without
reading it — the checker's rule), `overwriteAndCopySrc` (additionally at the source local `s` of
a copy `d := s` — the unsound ablation). A kill blocks `LS.Holds.carry` into the node; the
`LS.Holds.step` rule of a copy `d := s` with `s ≠ d` still moves the loans of `s` into `d`
there, so the copy behaves like a move. For a self-copy `v := v` the kill blocks `carry` and
`step` excludes the overwritten local, so the loans of `v` are dropped. -/
inductive KillMode | none | overwrite | overwriteAndCopySrc
  deriving DecidableEq, Repr
```

#### `killsAt`

Whether a node kills the origins of a local.

```lean
-- ToyLoanFlow/Analyses.lean:48-57
/-- `killsAt km p q v`: node `q` drops the loans of every origin of local `v`. -/
def killsAt (km : KillMode) (p : Prog n m) (q : Fin n) (v : Fin m) : Bool :=
  match km with
  | .none => false
  | .overwrite => (p.stmt q).defs.contains v && !(p.stmt q).uses.contains v
  | .overwriteAndCopySrc =>
      ((p.stmt q).defs.contains v && !(p.stmt q).uses.contains v) ||
        (match p.stmt q with
         | .copy _ s => s == v
         | _ => false)
```

#### `LS.SubAt`

Location-sensitive subset relations between origins.

```lean
-- ToyLoanFlow/Analyses.lean:61-71
/-- `SubAt vm p o₁ o₂ q`: after node `q` executes, loans of `o₁` flow into `o₂`. Constraints
generated by `q` hold at `q`; they are closed under transitivity at each node; and a relation
holding at `q` still holds at a successor `q'` when the locals of both origins are live on entry
to `q'` (constraints hold from their node onward while both ends are live). -/
inductive SubAt (vm : VarMode) (p : Prog n m) : Origin m → Origin m → Fin n → Prop
  | base {o₁ o₂ : Origin m} {q : Fin n} : (o₁, o₂) ∈ gen vm p q → SubAt vm p o₁ o₂ q
  | trans {o₁ o₂ o₃ : Origin m} {q : Fin n} :
      SubAt vm p o₁ o₂ q → SubAt vm p o₂ o₃ q → SubAt vm p o₁ o₃ q
  | persist {o₁ o₂ : Origin m} {q q' : Fin n} :
      SubAt vm p o₁ o₂ q → q' ∈ p.succ q → LiveAt p o₁.1 q' → LiveAt p o₂.1 q' →
        SubAt vm p o₁ o₂ q'
```

#### `LS.Holds`

Location-sensitive loan flow (propagation along edges limited by kills).

```lean
-- ToyLoanFlow/Analyses.lean:73-91
/-- `Holds km vm p l o q`: after node `q` executes, origin `o` may contain the loan created at
node `l` (location-sensitive loan flow, kill mode `km`, variance mode `vm`). -/
inductive Holds (km : KillMode) (vm : VarMode) (p : Prog n m) (l : Fin n) :
    Origin m → Fin n → Prop
  /-- the loan enters the outermost origin of the receiving local at its borrow -/
  | intro {mu : Mutbl} {d s : Fin m} : p.stmt l = .borrow mu d s → Holds km vm p l (d, 0) l
  /-- the loan stays in its origin across a CFG edge unless the next node kills the origin -/
  | carry {o : Origin m} {q q' : Fin n} :
      Holds km vm p l o q → q' ∈ p.succ q → killsAt km p q' o.1 = false → Holds km vm p l o q'
  /-- a constraint `(o₁, o₂)` generated by the next node propagates the loan from `o₁` into
  `o₂` (the loan is copied, not removed from `o₁`), provided that node does not overwrite the
  local of `o₁`; in particular a self-copy `v := v` propagates nothing by this rule, since it
  overwrites `v` -/
  | step {o₁ o₂ : Origin m} {q q' : Fin n} :
      Holds km vm p l o₁ q → q' ∈ p.succ q → (o₁, o₂) ∈ gen vm p q' →
        o₁.1 ∉ (p.stmt q').defs → Holds km vm p l o₂ q'
  /-- relations holding at a node move the loan between origins there -/
  | sub {o₁ o₂ : Origin m} {q : Fin n} :
      Holds km vm p l o₁ q → SubAt vm p o₁ o₂ q → Holds km vm p l o₂ q
```

#### `LS.LoanLive`

A loan is live on entry to a node.

```lean
-- ToyLoanFlow/Analyses.lean:93-96
/-- The loan created at `l` is live on entry to `q`: after some predecessor of `q`, some origin
of a local that is live at `q` may contain it. -/
def LoanLive (km : KillMode) (vm : VarMode) (p : Prog n m) (l q : Fin n) : Prop :=
  ∃ (o : Origin m) (q₀ : Fin n), Holds km vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q
```

#### `LS.Accepts`

The location-sensitive checker.

```lean
-- ToyLoanFlow/Analyses.lean:98-101
/-- The location-sensitive checker (kill mode `km`, variance mode `vm`) accepts `p`: no node
performs an access that conflicts with a loan live on entry to it. -/
def Accepts (km : KillMode) (vm : VarMode) (p : Prog n m) : Prop :=
  ∀ l q : Fin n, Conflicts p l q → ¬ LoanLive km vm p l q
```

#### `LS.LiveHolds`

Liveness-gated loan flow without kills.

```lean
-- ToyLoanFlow/Analyses.lean:103-114
/-- `LiveHolds vm p l o q`: after node `q` executes, origin `o` may contain the loan created at
node `l`, in the variant of `Holds` without kills whose propagation along a CFG edge requires the
origin's local to be live on entry to the next node (rule `carry`). -/
inductive LiveHolds (vm : VarMode) (p : Prog n m) (l : Fin n) : Origin m → Fin n → Prop
  | intro {mu : Mutbl} {d s : Fin m} : p.stmt l = .borrow mu d s → LiveHolds vm p l (d, 0) l
  | carry {o : Origin m} {q q' : Fin n} :
      LiveHolds vm p l o q → q' ∈ p.succ q → LiveAt p o.1 q' → LiveHolds vm p l o q'
  | step {o₁ o₂ : Origin m} {q q' : Fin n} :
      LiveHolds vm p l o₁ q → q' ∈ p.succ q → (o₁, o₂) ∈ gen vm p q' →
        o₁.1 ∉ (p.stmt q').defs → LiveHolds vm p l o₂ q'
  | sub {o₁ o₂ : Origin m} {q : Fin n} :
      LiveHolds vm p l o₁ q → SubAt vm p o₁ o₂ q → LiveHolds vm p l o₂ q
```

#### `LS.LiveLoanLive`

Loan liveness for the liveness-gated variant.

```lean
-- ToyLoanFlow/Analyses.lean:116-118
/-- The loan created at `l` is live on entry to `q` for the liveness-gated variant. -/
def LiveLoanLive (vm : VarMode) (p : Prog n m) (l q : Fin n) : Prop :=
  ∃ (o : Origin m) (q₀ : Fin n), LiveHolds vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q
```

#### `LS.LiveAccepts`

The liveness-gated location-sensitive checker without kills.

```lean
-- ToyLoanFlow/Analyses.lean:120-122
/-- The liveness-gated location-sensitive checker without kills accepts `p`. -/
def LiveAccepts (vm : VarMode) (p : Prog n m) : Prop :=
  ∀ l q : Fin n, Conflicts p l q → ¬ LiveLoanLive vm p l q
```

#### `NLL.InRegion`

Location-insensitive regions.

```lean
-- ToyLoanFlow/Analyses.lean:128-140
/-- `InRegion vm p o q`: node `q` belongs to the (location-insensitive) region of origin `o`:
the least sets of nodes closed under liveness, global outlives and the caller's region. -/
inductive InRegion (vm : VarMode) (p : Prog n m) : Origin m → Fin n → Prop
  /-- every origin of a local contains the nodes where the local is live -/
  | live {v : Fin m} {k : Nat} {q : Fin n} :
      LiveAt p v q → k < (p.ty v).length → InRegion vm p (v, k) q
  /-- `(o₁, o₂) ∈ gen` (generated anywhere) is the outlives constraint `o₁ : o₂`, imposed at
  every node: the region of `o₁` contains the region of `o₂` -/
  | outlives {o₁ o₂ : Origin m} {b q : Fin n} :
      (o₁, o₂) ∈ gen vm p b → InRegion vm p o₂ q → InRegion vm p o₁ q
  /-- a returned local's outermost origin outlives the caller's region, which contains every
  node of the body -/
  | universal {v : Fin m} {b q : Fin n} : p.stmt b = .ret v → InRegion vm p (v, 0) q
```

#### `NLL.InScope`

A loan is in scope on entry to a node.

```lean
-- ToyLoanFlow/Analyses.lean:142-150
/-- `InScope vm p l q`: the loan created at node `l` is in scope on entry to `q`: some walk of
one or more steps from `l` reaches `q` with every node after `l` in the region of the outermost
origin of the local that received the loan. -/
inductive InScope (vm : VarMode) (p : Prog n m) (l : Fin n) : Fin n → Prop
  | first {d : Fin m} {q : Fin n} :
      loanDst p l = some d → q ∈ p.succ l → InRegion vm p (d, 0) q → InScope vm p l q
  | next {d : Fin m} {q q' : Fin n} :
      loanDst p l = some d → InScope vm p l q → q' ∈ p.succ q → InRegion vm p (d, 0) q' →
        InScope vm p l q'
```

#### `NLL.Accepts`

The location-insensitive checker.

```lean
-- ToyLoanFlow/Analyses.lean:152-155
/-- The location-insensitive checker (variance mode `vm`) accepts `p`: no node performs an
access that conflicts with a loan in scope on entry to it. -/
def Accepts (vm : VarMode) (p : Prog n m) : Prop :=
  ∀ l q : Fin n, Conflicts p l q → ¬ InScope vm p l q
```

#### `LSAccepts`

The location-sensitive checker of this package.

```lean
-- ToyLoanFlow/Analyses.lean:159-160
/-- The location-sensitive checker of this package: kills at overwrites, invariant `&mut`. -/
abbrev LSAccepts (p : Prog n m) : Prop := LS.Accepts .overwrite .inv p
```

#### `NLLAccepts`

The location-insensitive checker of this package.

```lean
-- ToyLoanFlow/Analyses.lean:162-163
/-- The location-insensitive checker of this package: invariant `&mut`. -/
abbrev NLLAccepts (p : Prog n m) : Prop := NLL.Accepts .inv p
```

#### `Acyclic`

No cycle anywhere in `Fin n`, reachable from `p.entry` or not.

```lean
-- ToyLoanFlow/Results.lean:17-18
/-- `Acyclic p`: no node reaches itself by a walk of one or more steps (along `p.succ`). -/
def Acyclic (p : Prog n m) : Prop := ∀ q q' : Fin n, q' ∈ p.succ q → ¬ Reach p.succ q' q
```

Each definition has fully proved positive and negative examples in `ToyLoanFlow/DefExamples.lean`.

### Concrete programs

#### `pc3`

```lean
-- ToyLoanFlow/Programs.lean:12-35
/-- Problem case #3 (conditional return of a loan, otherwise a fresh mutable loan of the same
place), as in a get-or-insert on a map. Locals: `0 = x` (data; stands for `*map`),
`1 = r : &mut D`, `2 = s : &mut D`.

    0: r := &mut x        -> 1
    1: (branch)           -> 2, 3
    2: return r
    3: write x            -> 4      (the insertion)
    4: s := &mut x        -> 5
    5: return s
-/
def pc3 : Prog 6 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2, 3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 2 => .ret 1
    | 3 => .access .wr 0
    | 4 => .borrow .mut 2 0
    | 5 => .ret 2
    | _ => .nop
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]
```

#### `pc3Loop`

```lean
-- ToyLoanFlow/Programs.lean:37-57
/-- Loop variant of problem case #3: a mutable borrow of the plain-data local `x` (standing for
`*map`), taken inside a loop, is returned conditionally; otherwise `x` is written and the loop
repeats. Each iteration borrows `x` directly; there is no reference through which a reborrow
could be taken. Locals: `0 = x` (data), `1 = r : &mut D`.

    0: r := &mut x        -> 1
    1: (branch)           -> 2, 3
    2: return r
    3: write x            -> 0
-/
def pc3Loop : Prog 4 2 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2, 3] | 3 => [0] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 2 => .ret 1
    | 3 => .access .wr 0
    | _ => .nop
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]
```

#### `pc3NoReturn`

```lean
-- ToyLoanFlow/Programs.lean:165-187
/-- Problem case #3 without the return: the first loan is used at node `2` instead of being
returned. Locals: `0 = x` (data), `1 = r : &mut D`, `2 = s : &mut D`.

    0: r := &mut x        -> 1
    1: (branch)           -> 2, 3
    2: read *r
    3: write x            -> 4
    4: s := &mut x        -> 5
    5: read *s
-/
def pc3NoReturn : Prog 6 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2, 3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 2 => .deref .rd 1
    | 3 => .access .wr 0
    | 4 => .borrow .mut 2 0
    | 5 => .deref .rd 2
    | _ => .nop
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]
```

#### `pReassign`

```lean
-- ToyLoanFlow/Programs.lean:59-79
/-- Reassignment of the reference that holds a loan. Locals: `0 = x`, `1 = y` (data),
`2 = r : &mut D`.

    0: r := &mut x        -> 1
    1: write *r           -> 2
    2: r := &mut y        -> 3
    3: write x            -> 4
    4: write *r
-/
def pReassign : Prog 5 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 2 0
    | 1 => .deref .wr 2
    | 2 => .borrow .mut 2 1
    | 3 => .access .wr 0
    | _ => .deref .wr 2
  ty := fun v => match v.val with
    | 2 => [.mut] | _ => []
```

#### `pCopyThenUse`

```lean
-- ToyLoanFlow/Programs.lean:81-99
/-- A copy of a mutable reference followed by a write to the place and a use of the original.
Locals: `0 = x` (data), `1 = r : &mut D`, `2 = s : &mut D`.

    0: r := &mut x        -> 1
    1: s := r             -> 2
    2: write x            -> 3
    3: write *r
-/
def pCopyThenUse : Prog 4 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 1 => .copy 2 1
    | 2 => .access .wr 0
    | _ => .deref .wr 1
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]
```

#### `pCopyThenUseShr`

```lean
-- ToyLoanFlow/Programs.lean:189-207
/-- The shared-reference counterpart of `pCopyThenUse`. Locals: `0 = x` (data),
`1 = r : &D`, `2 = s : &D`.

    0: r := &x            -> 1
    1: s := r             -> 2
    2: write x            -> 3
    3: read *r
-/
def pCopyThenUseShr : Prog 4 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 1 0
    | 1 => .copy 2 1
    | 2 => .access .wr 0
    | _ => .deref .rd 1
  ty := fun v => match v.val with
    | 0 => [] | _ => [.shr]
```

#### `pVariance`

```lean
-- ToyLoanFlow/Programs.lean:101-123
/-- A shorter loan written through `&mut &D` into a longer-lived reference. Locals:
`0 = x`, `1 = y` (data), `2 = c : &D`, `3 = pp : &mut &D`, `4 = s : &D`.

    0: c := &x            -> 1
    1: pp := &mut c       -> 2
    2: s := &y            -> 3
    3: *pp := s           -> 4
    4: write y            -> 5
    5: read *c
-/
def pVariance : Prog 6 5 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 2 0
    | 1 => .borrow .mut 3 2
    | 2 => .borrow .shr 4 1
    | 3 => .store 3 4
    | 4 => .access .wr 1
    | _ => .deref .rd 2
  ty := fun v => match v.val with
    | 2 => [.shr] | 3 => [.mut, .shr] | 4 => [.shr] | _ => []
```

#### `pStoreSafe`

```lean
-- ToyLoanFlow/Programs.lean:209-231
/-- A safe program that stores through `&mut &D`, so that the generated constraints are not
empty. Locals: `0 = x`, `1 = y` (data), `2 = c : &D`, `3 = pp : &mut &D`, `4 = s : &D`.

    0: c := &x            -> 1
    1: pp := &mut c       -> 2
    2: s := &y            -> 3
    3: *pp := s           -> 4
    4: read *c            -> 5
    5: write y
-/
def pStoreSafe : Prog 6 5 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 2 0
    | 1 => .borrow .mut 3 2
    | 2 => .borrow .shr 4 1
    | 3 => .store 3 4
    | 4 => .deref .rd 2
    | _ => .access .wr 1
  ty := fun v => match v.val with
    | 2 => [.shr] | 3 => [.mut, .shr] | 4 => [.shr] | _ => []
```

#### `pUntypedHolder`

```lean
-- ToyLoanFlow/Programs.lean:125-140
/-- An ill-typed program: the loan is received by a local declared as plain data, which has no
origin. Locals: `0 = x` (data), `1 = r` (declared data).

    0: r := &mut x        -> 1
    1: write x            -> 2
    2: write *r
-/
def pUntypedHolder : Prog 3 2 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 1 => .access .wr 0
    | _ => .deref .wr 1
  ty := fun _ => []
```

#### `pUntypedStore`

```lean
-- ToyLoanFlow/Programs.lean:142-163
/-- An ill-typed program: a reference is stored, through a `&mut` to a local declared as plain
data, into that local, which is then dereferenced. Locals: `0 = y` (data), `1 = c` (declared
data), `2 = pp : &mut D`, `3 = s : &D`.

    0: s := &y            -> 1
    1: pp := &mut c       -> 2
    2: *pp := s           -> 3
    3: write y            -> 4
    4: read *c
-/
def pUntypedStore : Prog 5 4 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 3 0
    | 1 => .borrow .mut 2 1
    | 2 => .store 2 3
    | 3 => .access .wr 0
    | _ => .deref .rd 1
  ty := fun v => match v.val with
    | 2 => [.mut] | 3 => [.shr] | _ => []
```

#### `pUnreachUntyped`

```lean
-- ToyLoanFlow/Programs.lean:233-250
/-- `pUntypedHolder` placed in nodes `1`–`3`, unreachable from the entry node `0` (a `nop` with
no successor). Locals: `0 = x` (data), `1 = r` (declared data).

    0: (nop)
    1: r := &mut x        -> 2
    2: write x            -> 3
    3: write *r
-/
def pUnreachUntyped : Prog 4 2 where
  entry := 0
  succ := fun q => match q.val with
    | 1 => [2] | 2 => [3] | _ => []
  stmt := fun q => match q.val with
    | 1 => .borrow .mut 1 0
    | 2 => .access .wr 0
    | 3 => .deref .wr 1
    | _ => .nop
  ty := fun _ => []
```

## Findings

### R1a — `safe_of_wellTyped_of_nllAccepts`

**Plain claim.** For every toy program `p` (any finite CFG over `Fin n`, cycles allowed, any number `m` of locals) that is well typed at every node of `Fin n`, reachable from `p.entry` or not (`WellTyped p`), and that the location-insensitive checker accepts (`NLLAccepts p`, which tests every node of `Fin n` against every loan in scope there), no walk `π` of `p.succ` with `π.head? = some p.entry` reaches UB when `run p RState.init π` executes it one `exec` step per node (`Safe p`).

**Kind / tier / depth.** theorem / T1 / shallow (a two-line corollary of Results 1c and 2, which are substantive).

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:64-68
/-- **Result 1a.** Every program that is well typed at every node and accepted by the
location-insensitive checker is safe: no walk of `p.succ` from `p.entry`, executed by `run` with
`exec` from `RState.init`, reaches UB. -/
theorem safe_of_wellTyped_of_nllAccepts (p : Prog n m) (hwt : WellTyped p)
    (hacc : NLLAccepts p) : Safe p := …
```

Explicit rendering of `safe_of_wellTyped_of_nllAccepts` (definitional unfolding of `WellTyped`, `NLLAccepts`, `NLL.Accepts` and `Safe`; it elaborates with `autoImplicit` off in `namespace Toy.LoanFlow`, with the theorem's binders `n m` as locals, and is definitionally equal to the theorem's statement):

```lean
∀ (p : Prog n m), (∀ q : Fin n, StmtWellTyped p (p.stmt q)) →
    (∀ l q : Fin n, Conflicts p l q → ¬ NLL.InScope .inv p l q) →
    ∀ π : List (Fin n), IsWalk p.succ π → π.head? = some p.entry →
      (run p RState.init π).isUB = false
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hwt : WellTyped p` | a loan received by a local declared as plain data has no origin, so the location-insensitive checker never reports its conflicts | tight: `nllAccepts_not_safe_without_wellTyped` (witness class: a 3-node straight-line program with exactly 2 locals) |
| `hacc : NLLAccepts p` | the checker's verdict | tight: `wellTyped_acyclic_not_safe` (witness class: a 4-node straight-line well-typed program with exactly 3 locals) |
| variance mode `.inv` inside `hacc` (`NLLAccepts p` is `NLL.Accepts .inv p`) | two-way constraints for every layer nested inside `&mut` | tight: `safe_of_wellTyped_of_nllCovAccepts_fails` (witness class: `NLL.Accepts .cov` in place of `NLLAccepts`; a 6-node straight-line well-typed program with exactly 5 locals) |

A `tight` entry means: there is a counterexample, satisfying all the other hypotheses, in which the conclusion fails; it lies in the stated witness class.

**Non-vacuity witness.** `pReassign` is well typed and accepted by `NLLAccepts`; `pStoreSafe` is well typed and accepted by `NLLAccepts`, and its generated constraints are not empty (`gen .inv pStoreSafe 3 ≠ []`). (`safe_of_wellTyped_of_nllAccepts_nonvacuous`)

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- `NLLAccepts` is the package's own location-insensitive checker, modelled on the outlives propagation documented in the rustc-dev-guide; RFC 2094's own proposal is location-aware (`('a: 'b) @ P`) and is not what `NLLAccepts` models.
- `Safe p` excludes the UB that `exec` defines: dereferencing, storing through, or returning an invalidated record. Copies of a reference keep its tag, so two locals holding copies of one mutable record are one permission and may be used interleaved without UB; `Safe` is not the statement that no two usable `&mut` references alias.
- `WellTyped p` checks statement-level layer shapes at every node of `Fin n`, reachable from `p.entry` or not, and performs no definite-initialization check: `RState.init` gives every local `none`, and `exec` maps `deref`, `store` and `ret` on a local holding `none` to `.halt`, not `.ub`; so `Safe p` does not exclude uses of uninitialized reference locals.
- There is no `StorageDead`: every plain-data local outlives the body (standing for storage reachable from the parameters, such as `*map`), and `exec` on `ret` checks the returned record's validity and nothing else; returning a valid reference to a local is not UB in the toy (no frame is deallocated), so dangling references to stack storage are not modelled.
- `StmtWellTyped` restricts `deref` and `ret` to depth-1 references (`[.shr]` or `[.mut]`), so no reference of depth at least 2 is dereferenced or returned; inner origins `(v, k)` with `k ≥ 1` matter for `Safe` through `Stmt.store`, the one statement that moves a record into the local behind a reference.
- The toy language has no reads of a reference through a reference (`t := *p`), no reborrow loans (`&mut *r`) and no loans on places behind references, no moves and no move checker, no two-phase borrows and no calls; whether the result survives adding any of these is not examined.
- Whether the conclusion survives requiring well-typedness at the nodes reachable from `p.entry` alone is not examined for this result (for Result 2 that weakening is false: `lsAccepts_of_reachWellTyped_of_nllAccepts_fails`).
- It says nothing about precision: `NLLAccepts` rejects the safe program `pc3` (`pc3_wellTyped_safe_lsAccepts_not_nllAccepts`, Result 3a).
- Without `hwt` the conclusion fails (`nllAccepts_not_safe_without_wellTyped`); with covariant `&mut` it fails (`safe_of_wellTyped_of_nllCovAccepts_fails`).

**Prior art.**

- rustc-dev-guide, rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11: src/borrow-check/region-inference/constraint-propagation.md:33-36 (liveness constraints and outlives constraints `R1: R2` propagated by `Values(R1) = Values(R1) union Values(R2)`); src/borrow-check/region-inference/lifetime-parameters.md:82-84 (universal regions contain the entire function body). Documentation.
- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md: Problem case #3 at :201-335; location-aware subtyping at :438-448; the requirement on the first borrow in Problem case #3 at :1464-1466; 'allows us to handle cases like Problem Case #3' at :2017-2019. Documentation (design RFC).
- Corpus package two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges (google/zerocopy branch reference, added at commit a92dad5d362315aa1e07acade3aeedb183dd2d18): loan model and reference-semantics style reused; `IsWalk` copied from its lean/ToyTwoPhase/Graph.lean:20-25 (git blob d80d4d0f36d0386d3ec3d32cdba33afb4e5e4a8d).
- R. Jung, H.-H. Dang, J. Kang, D. Dreyer, 'Stacked Borrows: An Aliasing Model for Rust', Proc. ACM Program. Lang. 4 (POPL), 2020, doi:10.1145/3371109 (tag-based permission machine; the toy semantics is in this style).
- N. Villani, J. Hostert, D. Dreyer, R. Jung, 'Tree Borrows', Proc. ACM Program. Lang. 9 (PLDI), 2025, doi:10.1145/3735592 (tag-based permission machine; the toy semantics is in this style).
- A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982v4 (2021) (a type-systems account of Rust's borrow checker with lifetimes viewed as approximations of the provenances of references; not examined in depth).
- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2 (POPL), 2018, doi:10.1145/3158154 (semantic soundness of a Rust core language; it does not formalize NLL- or Polonius-style region inference).
- D. J. Pearce, 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust', ACM TOPLAS 43(1), 2021, doi:10.1145/3443420 (a core calculus with borrowing; not examined in depth).
- Novelty search: web searches for mechanized (Coq/Rocq, Isabelle, Lean) formalizations of Polonius-style location-sensitive loan analyses, and the sources above; none found that proves soundness of a location-sensitive loan-flow checker together with inclusion of, and strict separation from, a location-insensitive region checker. T1 is claimed, not T3.

**Design question.** Is a location-insensitive region checker (regions as node sets, outlives constraints imposed at every node, the caller's region containing the whole body) a sound baseline against which more permissive checkers can be compared?

### R1c — `safe_of_wellTyped_of_lsAccepts`

**Plain claim.** For every toy program `p` (any finite CFG over `Fin n`, cycles allowed, any number `m` of locals) that is well typed at every node of `Fin n`, reachable from `p.entry` or not (`WellTyped p`), and that the location-sensitive checker accepts (`LSAccepts p`: kills at overwrites, invariant `&mut`, every node of `Fin n` tested), no walk `π` of `p.succ` with `π.head? = some p.entry` reaches UB when `run p RState.init π` executes it one `exec` step per node (`Safe p`).

**Kind / tier / depth.** theorem / T1 / substantive.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:44-48
/-- **Result 1c.** Every program that is well typed at every node and accepted by the
location-sensitive checker is safe: no walk of `p.succ` from `p.entry`, executed by `run` with
`exec` from `RState.init`, reaches UB (any CFG, including cycles). -/
theorem safe_of_wellTyped_of_lsAccepts (p : Prog n m) (hwt : WellTyped p)
    (hacc : LSAccepts p) : Safe p := by …
```

Explicit rendering of `safe_of_wellTyped_of_lsAccepts` (definitional unfolding of `WellTyped`, `LSAccepts`, `LS.Accepts`, `LS.LoanLive` and `Safe`; it elaborates with `autoImplicit` off in `namespace Toy.LoanFlow`, with the theorem's binders `n m` as locals, and is definitionally equal to the theorem's statement):

```lean
∀ (p : Prog n m), (∀ q : Fin n, StmtWellTyped p (p.stmt q)) →
    (∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.Holds .overwrite .inv p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q) →
    ∀ π : List (Fin n), IsWalk p.succ π → π.head? = some p.entry →
      (run p RState.init π).isUB = false
```

**Proof structure.** The proof is an inductive invariant `Sound.Inv p q σ` over the configurations reached by `run` (node `q` about to execute, state `σ`), established at `(p.entry, RState.init)` by `Sound.inv_init`, preserved by every `.ok` step (`Sound.step_inv`), and excluding `.ub` (`Sound.exec_ne_ub`); `Sound.run_not_ub` is the induction over walks. For every local live at `q`, the invariant records that its record is valid, that its loan is held (`LS.Holds`) in the local's outermost origin after some predecessor of `q`, and, for a mutable record, the two-way `LS.SubAt` relations between the holder's inner origins and the target's origins; globally, records carry their loan's source and mutability with the holder typed accordingly (`Sound.WF`), and a valid mutable record excludes valid records of other tags on its target (`Sound.Uniq`).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hwt : WellTyped p` | a store through a `&mut` to a local declared as plain data generates no relation to the stored-into local, so the stored loan is lost | tight: `lsAccepts_not_safe_without_wellTyped` (witness class: a 5-node straight-line program with exactly 4 locals) |
| `hacc : LSAccepts p` | the checker's verdict | tight: `wellTyped_acyclic_not_safe` (witness class: a 4-node straight-line well-typed program with exactly 3 locals) |
| kill mode `.overwrite` inside `hacc` | kills drop the loans of the origins of an overwritten local, not those of a copy source | tight: `safe_of_wellTyped_of_lsCopySrcKillAccepts_fails` (witness class: `LS.Accepts .overwriteAndCopySrc .inv` in place of `LSAccepts`; a 4-node straight-line well-typed program with exactly 3 locals) |
| variance mode `.inv` inside `hacc` | two-way constraints for every layer nested inside `&mut` | tight: `safe_of_wellTyped_of_lsCovAccepts_fails` (witness class: `LS.Accepts .overwrite .cov` in place of `LSAccepts`; a 6-node straight-line well-typed program with exactly 5 locals) |

A `tight` entry means: there is a counterexample, satisfying all the other hypotheses, in which the conclusion fails; it lies in the stated witness class.

**Non-vacuity witness.** `pc3Loop` (a cyclic CFG) is well typed and accepted by `LSAccepts`; `pStoreSafe` is well typed and accepted by `LSAccepts`, and its generated constraints are not empty. (`safe_of_wellTyped_of_lsAccepts_nonvacuous`)

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- `LSAccepts` is the package's own location-sensitive checker. Its kill rule (`killsAt .overwrite`: a node that overwrites a local without reading it) is not Polonius's `loan_killed_at` (an assignment to a prefix of the borrowed path), and in `LS.Holds` propagation along edges is limited by kills, not by liveness; its acceptance coincides with that of the liveness-gated variant without kills `LS.LiveAccepts` (`lsAccepts_overwrite_iff_liveAccepts`, Result 4c).
- `Safe p` excludes the UB that `exec` defines: dereferencing, storing through, or returning an invalidated record. Copies of a reference keep its tag, so two locals holding copies of one mutable record are one permission and may be used interleaved without UB; `Safe` is not the statement that no two usable `&mut` references alias.
- `WellTyped p` checks statement-level layer shapes at every node of `Fin n`, reachable from `p.entry` or not, and performs no definite-initialization check: `RState.init` gives every local `none`, and `exec` maps `deref`, `store` and `ret` on a local holding `none` to `.halt`, not `.ub`; so `Safe p` does not exclude uses of uninitialized reference locals.
- There is no `StorageDead`: every plain-data local outlives the body (standing for storage reachable from the parameters, such as `*map`), and `exec` on `ret` checks the returned record's validity and nothing else; returning a valid reference to a local is not UB in the toy (no frame is deallocated), so dangling references to stack storage are not modelled.
- `StmtWellTyped` restricts `deref` and `ret` to depth-1 references (`[.shr]` or `[.mut]`), so no reference of depth at least 2 is dereferenced or returned; inner origins `(v, k)` with `k ≥ 1` matter for `Safe` through `Stmt.store`, the one statement that moves a record into the local behind a reference.
- The toy language has no reads of a reference through a reference (`t := *p`), no reborrow loans (`&mut *r`) and no loans on places behind references, no moves and no move checker, no two-phase borrows and no calls; whether the result survives adding any of these is not examined.
- `LSAccepts` represents no caller region at `ret`; Result 1c relies on `exec` ending the run at `ret`, and it says nothing about checkers of languages in which execution continues after a function returns a reference.
- `LS.SubAt` propagates relations forward along `p.succ`; whether `LSAccepts` agrees with any location-sensitive design that also propagates relations backward along CFG edges is not examined.
- Whether the conclusion survives requiring well-typedness at the nodes reachable from `p.entry` alone is not examined.
- It does not say that kills at copy sources or covariant `&mut` keep the checker sound; both make it unsound (`safe_of_wellTyped_of_lsCopySrcKillAccepts_fails`, `safe_of_wellTyped_of_lsCovAccepts_fails`).

**Prior art.**

- Polonius book, rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md: goals :9-12; `loan_killed_at` :29-34; subset rules R1-R3 :69-91; loan rules R4-R6 :93-115 (R6, propagation along CFG edges gated by both `!loan_killed_at` and origin liveness, :109-114); loan liveness R7 and errors R8 :117-136. Documentation.
- N. Matsakis, 'An alias-based formulation of the borrow checker', 27 April 2018, https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2018-04-27-an-alias-based-formulation-of-the-borrow-checker.markdown (git blob 338f3cec9fb3d9941232a9c8890d5783e1b710dd); section 'Refining constraint propagation with liveness' at :667-743 resolves a reassignment example of the `pReassign` pattern (with shared loans) by gating propagation on liveness. Blog post.
- N. Matsakis, 'Polonius revisited, part 1', 22 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-22-polonius-part-1.markdown (git blob dd8bd8d9d359062a4f42f42b72e9b1095df35408). Blog post.
- N. Matsakis, 'Polonius revisited, part 2', 29 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/29/polonius-part-2/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-29-polonius-part-2.markdown (git blob d93a78cd9bf41f84f9ff532631988fec653e48ec). Blog post.
- Rust project blogs, rust-lang/blog.rust-lang.org@8666f7c3a86260ec58e4d914d451b14613c690a4: content/inside-rust/polonius-update/index.md (R. Rakic and N. Matsakis, 'Polonius update', 6 October 2023; git blob 4e860b1d76b8fdcd473ed09302356b09d8ae5ab7) and content/enabling-polonius-alpha-on-nightly/index.md (J. Huey, 'Enabling the next iteration of the borrow checker on nightly', 4 August 2026; git blob f99931718eecc43da0ae083dbead70b8c376eb1f). Documentation of design plans; cited, not relied on.
- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md: Problem case #3 at :201-335; location-aware subtyping at :438-448; the requirement on the first borrow in Problem case #3 at :1464-1466; 'allows us to handle cases like Problem Case #3' at :2017-2019. Documentation (design RFC).
- Corpus package two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges (google/zerocopy branch reference, added at commit a92dad5d362315aa1e07acade3aeedb183dd2d18): loan model and reference-semantics style reused; `IsWalk` copied from its lean/ToyTwoPhase/Graph.lean:20-25 (git blob d80d4d0f36d0386d3ec3d32cdba33afb4e5e4a8d).
- R. Jung, H.-H. Dang, J. Kang, D. Dreyer, 'Stacked Borrows: An Aliasing Model for Rust', Proc. ACM Program. Lang. 4 (POPL), 2020, doi:10.1145/3371109 (tag-based permission machine; the toy semantics is in this style).
- N. Villani, J. Hostert, D. Dreyer, R. Jung, 'Tree Borrows', Proc. ACM Program. Lang. 9 (PLDI), 2025, doi:10.1145/3735592 (tag-based permission machine; the toy semantics is in this style).
- S. Ho, A. Fromherz, J. Protzenko, 'Sound Borrow-Checking for Rust via Symbolic Semantics', Proc. ACM Program. Lang. 8 (ICFP), 2024, doi:10.1145/3674640; long version arXiv:2404.02680 (a different, symbolic-execution borrow checker proved sound against a heap model; whether its proofs are mechanized is not examined here).
- A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982v4 (2021) (a type-systems account of Rust's borrow checker with lifetimes viewed as approximations of the provenances of references; not examined in depth).
- L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', Proc. ACM Program. Lang. 8 (PLDI), 2024, doi:10.1145/3656422 (not examined in depth).
- Z. Grannan, A. Bílý, J. Fiala, J. Geer, M. de Medeiros, P. Müller, A. J. Summers, 'Place Capability Graphs: A General-Purpose Model of Rust's Ownership and Borrowing Guarantees', Proc. ACM Program. Lang. 9 (OOPSLA2), 2025, doi:10.1145/3763122 (not examined in depth).
- Novelty search: web searches for mechanized (Coq/Rocq, Isabelle, Lean) formalizations of Polonius-style location-sensitive loan analyses, and the sources above; none found that proves soundness of a location-sensitive loan-flow checker together with inclusion of, and strict separation from, a location-insensitive region checker. T1 is claimed, not T3.

**Design question.** Is a location-sensitive loan-flow checker (kills at overwrites, invariant `&mut`) sound on arbitrary CFGs, including loops where loans re-enter along back edges?

### R2 — `lsAccepts_of_wellTyped_of_nllAccepts`

**Plain claim.** For every variance mode `vm` (`VarMode.inv` or `VarMode.cov`) and every toy program `p` that is well typed at every node of `Fin n`, reachable from `p.entry` or not (`WellTyped p`), if the location-insensitive checker with that variance mode accepts `p` (`NLL.Accepts vm p`), then the location-sensitive checker with kills at overwrites and the same variance mode accepts `p` (`LS.Accepts .overwrite vm p`).

**Kind / tier / depth.** theorem / T1 / substantive.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:57-61
/-- **Result 2.** For every variance mode `vm`, every program that is well typed at every node
and accepted by the location-insensitive checker `NLL.Accepts vm` is accepted by the
location-sensitive checker with kills at overwrites `LS.Accepts .overwrite vm`. -/
theorem lsAccepts_of_wellTyped_of_nllAccepts (vm : VarMode) (p : Prog n m) (hwt : WellTyped p)
    (h : NLL.Accepts vm p) : LS.Accepts .overwrite vm p := …
```

Explicit rendering of `lsAccepts_of_wellTyped_of_nllAccepts` (definitional unfolding of `WellTyped`, `NLL.Accepts`, `LS.Accepts` and `LS.LoanLive`; it elaborates with `autoImplicit` off in `namespace Toy.LoanFlow`, with the theorem's binders `n m` as locals, and is definitionally equal to the theorem's statement):

```lean
∀ (vm : VarMode) (p : Prog n m), (∀ q : Fin n, StmtWellTyped p (p.stmt q)) →
    (∀ l q : Fin n, Conflicts p l q → ¬ NLL.InScope vm p l q) →
    ∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.Holds .overwrite vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q
```

**Proof structure.** By Result 4c it suffices to show the inclusion for the liveness-gated variant `LS.LiveAccepts` (`liveAccepts_of_wellTyped_of_nllAccepts`): along every `LS.LiveHolds` derivation for the loan created at `l`, well-typedness keeps the origin's layer index in range and every generated constraint is an `NLL.InRegion` outlives step back to the receiving origin, so every node after `l` on the loan's path lies in the location-insensitive region of the receiving local (`Incl.liveHolds_to_nll`), which gives `NLL.InScope`.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hwt : WellTyped p` | the location-insensitive checker gives a loan received by a local without origins an empty region, while the location-sensitive checker still tracks it | tight: `lsAccepts_of_nllAccepts_fails_without_wellTyped` (witness class: `vm = .inv`; a 3-node straight-line program with exactly 2 locals) |
| "every node of `Fin n`, reachable from `p.entry` or not" (the quantifier range of `hwt`) | both checkers inspect every node, so an ill-typed unreachable component can make them disagree | tight: `lsAccepts_of_reachWellTyped_of_nllAccepts_fails` (witness class: `vm = .inv`; a 4-node program with exactly 2 locals whose entry node has no successor, well typed at every node reachable from the entry node) |
| `h : NLL.Accepts vm p` | the premise of the inclusion | tight: `wellTyped_not_lsAccepts` (witness class: `vm = .inv`; a 4-node straight-line well-typed program with exactly 3 locals) |

A `tight` entry means: there is a counterexample, satisfying all the other hypotheses, in which the conclusion fails; it lies in the stated witness class.

**Non-vacuity witness.** `pReassign` (with `vm = .inv`), `pVariance` (with `vm = .cov`) and `pStoreSafe` (with `vm = .inv`, non-empty generated constraints) are well typed and accepted by `NLL.Accepts vm`. (`lsAccepts_of_wellTyped_of_nllAccepts_nonvacuous`)

**Non-claims.**

- It is a statement about the two toy checkers of this package; it neither establishes nor refutes any inclusion between the acceptance sets of rustc's borrow checker and of any Polonius implementation. Model–system relation: none proved.
- The converse inclusion fails (`pc3_wellTyped_safe_lsAccepts_not_nllAccepts`, Result 3a).
- Requiring well-typedness at the nodes reachable from `p.entry` alone falsifies the inclusion (`lsAccepts_of_reachWellTyped_of_nllAccepts_fails`); `WellTyped p`, `NLL.Accepts vm p` and `LS.Accepts .overwrite vm p` all inspect every node of `Fin n`.
- With `LS.Accepts .none` in the conclusion the inclusion fails (`lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails`), but this does not show that the inclusion needs kills: the liveness-gated variant without kills `LS.LiveAccepts` satisfies it (`refuted_result2_needs_kills`, Result 4c).
- It holds for `VarMode.cov` as well, where both checkers are unsound (`pVariance_wellTyped_covAccepts_not_safe`, Result 5); the inclusion is a statement about acceptance sets, not about safety.
- `LSAccepts` is the package's own location-sensitive checker. Its kill rule (`killsAt .overwrite`: a node that overwrites a local without reading it) is not Polonius's `loan_killed_at` (an assignment to a prefix of the borrowed path), and in `LS.Holds` propagation along edges is limited by kills, not by liveness; its acceptance coincides with that of the liveness-gated variant without kills `LS.LiveAccepts` (`lsAccepts_overwrite_iff_liveAccepts`, Result 4c).
- `NLLAccepts` is the package's own location-insensitive checker, modelled on the outlives propagation documented in the rustc-dev-guide; RFC 2094's own proposal is location-aware (`('a: 'b) @ P`) and is not what `NLLAccepts` models.
- No comparison is established between `LSAccepts` and RFC 2094's location-aware proposal (`('a: 'b) @ P` with `end('r)` regions), nor between `LSAccepts` and any version of rustc's borrow checker or of Polonius; not examined.

**Prior art.**

- N. Matsakis, 'An alias-based formulation of the borrow checker', 27 April 2018, https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2018-04-27-an-alias-based-formulation-of-the-borrow-checker.markdown (git blob 338f3cec9fb3d9941232a9c8890d5783e1b710dd); section 'Refining constraint propagation with liveness' at :667-743 resolves a reassignment example of the `pReassign` pattern (with shared loans) by gating propagation on liveness. Blog post.
- N. Matsakis, 'Polonius revisited, part 1', 22 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-22-polonius-part-1.markdown (git blob dd8bd8d9d359062a4f42f42b72e9b1095df35408). Blog post.
- N. Matsakis, 'Polonius revisited, part 2', 29 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/29/polonius-part-2/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-29-polonius-part-2.markdown (git blob d93a78cd9bf41f84f9ff532631988fec653e48ec). Blog post.
- Polonius book, rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md: goals :9-12; `loan_killed_at` :29-34; subset rules R1-R3 :69-91; loan rules R4-R6 :93-115 (R6, propagation along CFG edges gated by both `!loan_killed_at` and origin liveness, :109-114); loan liveness R7 and errors R8 :117-136. Documentation.
- rustc-dev-guide, rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11: src/borrow-check/region-inference/constraint-propagation.md:33-36 (liveness constraints and outlives constraints `R1: R2` propagated by `Values(R1) = Values(R1) union Values(R2)`); src/borrow-check/region-inference/lifetime-parameters.md:82-84 (universal regions contain the entire function body). Documentation.
- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md: Problem case #3 at :201-335; location-aware subtyping at :438-448; the requirement on the first borrow in Problem case #3 at :1464-1466; 'allows us to handle cases like Problem Case #3' at :2017-2019. Documentation (design RFC).
- Novelty search: web searches for mechanized (Coq/Rocq, Isabelle, Lean) formalizations of Polonius-style location-sensitive loan analyses, and the sources above; none found that proves soundness of a location-sensitive loan-flow checker together with inclusion of, and strict separation from, a location-insensitive region checker. T1 is claimed, not T3.

**Design question.** Does replacing location-insensitive constraints by location-sensitive loan flow lose any program that the location-insensitive checker accepts?

### R3a — `pc3_wellTyped_safe_lsAccepts_not_nllAccepts`

**Plain claim.** The toy program `pc3` (6 nodes, exactly 3 locals), a rendering of RFC 2094's Problem case #3 (`r := &mut x`; a nondeterministic branch to `return r` or to `write x; s := &mut x; return s`), is well typed (`WellTyped pc3`) and safe (`Safe pc3`: no walk of `pc3.succ` from `pc3.entry` reaches UB under `run` from `RState.init`), the location-sensitive checker accepts it (`LSAccepts pc3`), and the location-insensitive checker rejects it (`¬ NLLAccepts pc3`).

**Kind / tier / depth.** counterexample / T0 / shallow.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:135-138
/-- **Result 3a.** `pc3` is well typed and safe, the location-sensitive checker accepts it,
and the location-insensitive checker rejects it. -/
theorem pc3_wellTyped_safe_lsAccepts_not_nllAccepts :
    WellTyped pc3 ∧ Safe pc3 ∧ LSAccepts pc3 ∧ ¬ NLLAccepts pc3 := …
```

**Hypothesis ledger.** No hypotheses (a statement about concrete programs).

**Non-vacuity witness.** `pc3` itself. (`pc3_wellTyped_safe_lsAccepts_not_nllAccepts`)

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- It does not say that any real toolchain accepts or rejects the Rust function `get_default` of RFC 2094.
- `pc3` abstracts `map.get_mut` as a mutable borrow of the data local `x` (standing for `*map`) and `map.insert` as a write of `x`; keys, values, `Option` and the calls themselves are not modelled.
- It exhibits two programs in the gap between the checkers (with Result 3b); it does not characterize the gap.
- `NLLAccepts` is the package's own location-insensitive checker, modelled on the outlives propagation documented in the rustc-dev-guide; RFC 2094's own proposal is location-aware (`('a: 'b) @ P`) and is not what `NLLAccepts` models.
- Branching in `Prog` is nondeterministic (`p.succ`) and branch conditions are not modelled, so neither checker uses correlations between branches; programs whose safety depends on such correlations are not examined.

**Prior art.**

- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md: Problem case #3 at :201-335; location-aware subtyping at :438-448; the requirement on the first borrow in Problem case #3 at :1464-1466; 'allows us to handle cases like Problem Case #3' at :2017-2019. Documentation (design RFC).
- rustc-dev-guide, rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11: src/borrow-check/region-inference/constraint-propagation.md:33-36 (liveness constraints and outlives constraints `R1: R2` propagated by `Values(R1) = Values(R1) union Values(R2)`); src/borrow-check/region-inference/lifetime-parameters.md:82-84 (universal regions contain the entire function body). Documentation.
- N. Matsakis, 'Polonius revisited, part 1', 22 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-22-polonius-part-1.markdown (git blob dd8bd8d9d359062a4f42f42b72e9b1095df35408). Blog post.
- Rust project blogs, rust-lang/blog.rust-lang.org@8666f7c3a86260ec58e4d914d451b14613c690a4: content/inside-rust/polonius-update/index.md (R. Rakic and N. Matsakis, 'Polonius update', 6 October 2023; git blob 4e860b1d76b8fdcd473ed09302356b09d8ae5ab7) and content/enabling-polonius-alpha-on-nightly/index.md (J. Huey, 'Enabling the next iteration of the borrow checker on nightly', 4 August 2026; git blob f99931718eecc43da0ae083dbead70b8c376eb1f). Documentation of design plans; cited, not relied on.

**Design question.** Is location sensitivity alone (without per-path region values) enough to accept problem case #3?

### R3b — `pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts`

**Plain claim.** The toy program `pc3Loop` (4 nodes, exactly 2 locals, one back edge), in which a mutable borrow of the plain-data local `x` taken inside a loop is either returned or followed by a write of `x` and another iteration, is well typed (`WellTyped pc3Loop`) and safe (`Safe pc3Loop`, under `run` from `RState.init`), the location-sensitive checker accepts it (`LSAccepts pc3Loop`), and the location-insensitive checker rejects it (`¬ NLLAccepts pc3Loop`).

**Kind / tier / depth.** counterexample / T1 / shallow.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:141-144
/-- **Result 3b.** The loop variant `pc3Loop` is well typed and safe, the location-sensitive
checker accepts it, and the location-insensitive checker rejects it. -/
theorem pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts :
    WellTyped pc3Loop ∧ Safe pc3Loop ∧ LSAccepts pc3Loop ∧ ¬ NLLAccepts pc3Loop := …
```

**Hypothesis ledger.** No hypotheses (a statement about concrete programs).

**Non-vacuity witness.** `pc3Loop` itself. (`pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts`)

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- `pc3Loop` is a construction of this package; RFC 2094 does not contain it.
- In `pc3Loop`, local `0` (`x`) has plain-data type `[]`, so node `0` (`r := &mut x`) borrows a fixed local directly on each iteration; it is not a reborrow through a reference. Loops that reborrow and advance a mutable reference across iterations are outside the toy language.
- It does not say that the location-sensitive checker accepts every loop that conditionally returns a borrow.
- `NLLAccepts` is the package's own location-insensitive checker, modelled on the outlives propagation documented in the rustc-dev-guide; RFC 2094's own proposal is location-aware (`('a: 'b) @ P`) and is not what `NLLAccepts` models.
- Branching in `Prog` is nondeterministic (`p.succ`) and branch conditions are not modelled, so neither checker uses correlations between branches; programs whose safety depends on such correlations are not examined.

**Prior art.**

- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md: Problem case #3 at :201-335; location-aware subtyping at :438-448; the requirement on the first borrow in Problem case #3 at :1464-1466; 'allows us to handle cases like Problem Case #3' at :2017-2019. Documentation (design RFC).
- N. Matsakis, 'Polonius revisited, part 1', 22 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-22-polonius-part-1.markdown (git blob dd8bd8d9d359062a4f42f42b72e9b1095df35408). Blog post.
- Rust project blogs, rust-lang/blog.rust-lang.org@8666f7c3a86260ec58e4d914d451b14613c690a4: content/inside-rust/polonius-update/index.md (R. Rakic and N. Matsakis, 'Polonius update', 6 October 2023; git blob 4e860b1d76b8fdcd473ed09302356b09d8ae5ab7) and content/enabling-polonius-alpha-on-nightly/index.md (J. Huey, 'Enabling the next iteration of the borrow checker on nightly', 4 August 2026; git blob f99931718eecc43da0ae083dbead70b8c376eb1f). Documentation of design plans; cited, not relied on.

**Design question.** Does the separation survive back edges, where the returned loan's origin is re-entered on each iteration?

### R3c — `pc3_loan0_at_insertion`

**Plain claim.** In `pc3`, node `3` (the write of `x`) conflicts with the loan created at node `0` (`Conflicts pc3 0 3`); the outermost origin `(1, 0)` of the returned local `r` contains every node of `pc3` (`NLL.InRegion .inv pc3 (1, 0) q` for every `q : Fin 6`), and that loan is in scope at node `3` for the location-insensitive checker (`NLL.InScope .inv pc3 0 3`); it is not live at node `3` for the location-sensitive checker (`¬ LS.LoanLive .overwrite .inv pc3 0 3`).

**Kind / tier / depth.** theorem / T0 / shallow.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:147-153
/-- **Result 3c** (the mechanism). In `pc3` the write at node `3` conflicts with the loan
created at node `0`; the outermost origin of the returned local `r` contains every node; that
loan is in scope at node `3` for the location-insensitive checker and not live there for the
location-sensitive checker. -/
theorem pc3_loan0_at_insertion :
    Conflicts pc3 0 3 ∧ (∀ q : Fin 6, NLL.InRegion .inv pc3 (1, 0) q) ∧
      NLL.InScope .inv pc3 0 3 ∧ ¬ LS.LoanLive .overwrite .inv pc3 0 3 := …
```

**Hypothesis ledger.** No hypotheses (a statement about concrete programs).

**Non-vacuity witness.** `pc3` itself. (`pc3_loan0_at_insertion`)

Reference point: when the first loan is used at node `2` instead of returned (`pc3NoReturn`), both checkers accept the program (`pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- `NLL.InScope` belongs to the package's location-insensitive checker, modelled on the rustc-dev-guide's outlives propagation; RFC 2094's location-aware rules (`('a: 'b) @ P` with `end('r)`) are not what `NLL.InScope` models.
- It records the verdicts for loan `0` at node `3`; other conflicting nodes are not analysed.
- The reference point `pc3NoReturn` changes the program (a read of `*r` instead of `return r`); it is not an ablation of the rule `NLL.InRegion.universal` alone.

**Prior art.**

- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md: Problem case #3 at :201-335; location-aware subtyping at :438-448; the requirement on the first borrow in Problem case #3 at :1464-1466; 'allows us to handle cases like Problem Case #3' at :2017-2019. Documentation (design RFC).
- rustc-dev-guide, rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11: src/borrow-check/region-inference/constraint-propagation.md:33-36 (liveness constraints and outlives constraints `R1: R2` propagated by `Values(R1) = Values(R1) union Values(R2)`); src/borrow-check/region-inference/lifetime-parameters.md:82-84 (universal regions contain the entire function body). Documentation.

**Design question.** Which constraint makes the location-insensitive checker reject problem case #3?

### R4a — `pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts`

**Plain claim.** The toy program `pReassign` (`r := &mut x; write *r; r := &mut y; write x; write *r`; 5 nodes, exactly 3 locals) is well typed, safe (`Safe pReassign`, under `run` from `RState.init`), accepted by the location-insensitive checker (`NLLAccepts pReassign`) and by the location-sensitive checker (`LSAccepts pReassign`), and rejected by the location-sensitive variant whose propagation along CFG edges is limited neither by kills nor by liveness (`¬ LS.Accepts .none .inv pReassign`).

**Kind / tier / depth.** counterexample / T1 / shallow.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:164-169
/-- **Result 4a.** `pReassign` is well typed and safe and both checkers of the package accept
it, while the location-sensitive checker without kills (`LS.Accepts .none`, whose propagation
along edges is limited neither by kills nor by liveness) rejects it. -/
theorem pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts :
    WellTyped pReassign ∧ Safe pReassign ∧ NLLAccepts pReassign ∧ LSAccepts pReassign ∧
      ¬ LS.Accepts .none .inv pReassign := …
```

**Hypothesis ledger.** No hypotheses (a statement about concrete programs).

**Non-vacuity witness.** `pReassign` itself. (`pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts`)

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- The rejection relies on `LS.Holds.carry` not checking liveness: `r` is dead on entry to node `2` (`pReassign_r_dead_at_2`), and the liveness-gated variant without kills accepts `pReassign` (`refuted_result2_needs_kills`) and accepts exactly the programs that `LSAccepts` accepts (`lsAccepts_overwrite_iff_liveAccepts`, Result 4c). So it shows that removing kills from `LS.Holds` without adding liveness gating loses precision and breaks Result 2 (`lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails`); it does not show that kills are needed in a checker whose propagation is gated by liveness.
- It concerns precision. The variant without kills accepts a subset of the programs that `LSAccepts` accepts (`lsAccepts_of_lsNoKillAccepts`), so it is sound on well-typed programs by Result 1c.
- `LSAccepts` is the package's own location-sensitive checker. Its kill rule (`killsAt .overwrite`: a node that overwrites a local without reading it) is not Polonius's `loan_killed_at` (an assignment to a prefix of the borrowed path), and in `LS.Holds` propagation along edges is limited by kills, not by liveness; its acceptance coincides with that of the liveness-gated variant without kills `LS.LiveAccepts` (`lsAccepts_overwrite_iff_liveAccepts`, Result 4c).

**Prior art.**

- N. Matsakis, 'An alias-based formulation of the borrow checker', 27 April 2018, https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2018-04-27-an-alias-based-formulation-of-the-borrow-checker.markdown (git blob 338f3cec9fb3d9941232a9c8890d5783e1b710dd); section 'Refining constraint propagation with liveness' at :667-743 resolves a reassignment example of the `pReassign` pattern (with shared loans) by gating propagation on liveness. Blog post.
- Polonius book, rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md: goals :9-12; `loan_killed_at` :29-34; subset rules R1-R3 :69-91; loan rules R4-R6 :93-115 (R6, propagation along CFG edges gated by both `!loan_killed_at` and origin liveness, :109-114); loan liveness R7 and errors R8 :117-136. Documentation.

**Design question.** In a location-sensitive checker whose edge propagation is not gated by liveness, does removing kills at overwrites lose programs that the location-insensitive checker accepts?

### R4b — `pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe`, `pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe`

**Plain claim.** The toy program `pCopyThenUse` (`r := &mut x; s := r; write x; write *r`; 4 nodes, exactly 3 locals) is well typed and not safe (there is a walk from its entry that reaches UB under `run` from `RState.init`), the location-sensitive checker with additional kills at copy sources accepts it (`LS.Accepts .overwriteAndCopySrc .inv pCopyThenUse`), and the checker with kills at overwrites alone rejects it (`¬ LSAccepts pCopyThenUse`). The shared-reference program `pCopyThenUseShr` (`r := &x; s := r; write x; read *r`) satisfies the same four statements.

**Kind / tier / depth.** counterexample / T1 / shallow.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:178-183
/-- **Result 4b.** Adding kills at the source of a copy makes the location-sensitive checker
accept an unsafe well-typed program, `pCopyThenUse`; the checker with kills at overwrites
alone rejects it (positive control). -/
theorem pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe :
    WellTyped pCopyThenUse ∧ LS.Accepts .overwriteAndCopySrc .inv pCopyThenUse ∧
      ¬ Safe pCopyThenUse ∧ ¬ LSAccepts pCopyThenUse := …

-- ToyLoanFlow/Results.lean:187-190
/-- The shared-reference counterpart of Result 4b, with `pCopyThenUseShr` copying `&D`. -/
theorem pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe :
    WellTyped pCopyThenUseShr ∧ LS.Accepts .overwriteAndCopySrc .inv pCopyThenUseShr ∧
      ¬ Safe pCopyThenUseShr ∧ ¬ LSAccepts pCopyThenUseShr := …
```

**Hypothesis ledger.** No hypotheses (a statement about concrete programs).

**Non-vacuity witness.** `pCopyThenUse` and `pCopyThenUseShr` themselves. (`pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe`, `pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe`)

**Positive control.** `pCopyThenUse_not_lsAccepts`

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- `Stmt.copy` copies references of either mutability and `WellTyped` includes no move checker. Whether a move checker that forbids later uses of a copied-from `&mut` local would make kills at copy sources sound is not examined; `pCopyThenUseShr` exhibits the unsoundness without copying a `&mut` (`pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe`).
- Whether kills at copy sources are sound on a restricted class of programs (for example, programs whose copy sources are dead after the copy) is not examined.

**Prior art.**

- Polonius book, rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md: goals :9-12; `loan_killed_at` :29-34; subset rules R1-R3 :69-91; loan rules R4-R6 :93-115 (R6, propagation along CFG edges gated by both `!loan_killed_at` and origin liveness, :109-114); loan liveness R7 and errors R8 :117-136. Documentation.

**Design question.** May a location-sensitive checker treat a copy as moving the loan out of the source?

### R4c — `lsAccepts_overwrite_iff_liveAccepts`, `lsLoanLive_overwrite_iff_liveLoanLive`

**Plain claim.** For every variance mode `vm` and every toy program `p` (well typed or not, any CFG), the location-sensitive checker with kills at overwrites accepts `p` (`LS.Accepts .overwrite vm p`) if and only if the liveness-gated variant without kills accepts `p` (`LS.LiveAccepts vm p`); more precisely, for every loan `l` and node `q`, `LS.LoanLive .overwrite vm p l q ↔ LS.LiveLoanLive vm p l q` (`lsLoanLive_overwrite_iff_liveLoanLive`).

**Kind / tier / depth.** characterization / T1 / substantive.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Inclusion.lean:228-232
/-- For every program and variance mode, the location-sensitive checker with kills at
overwrites accepts exactly the programs that the liveness-gated variant without kills
accepts. -/
theorem lsAccepts_overwrite_iff_liveAccepts (vm : VarMode) (p : Prog n m) :
    LS.Accepts .overwrite vm p ↔ LS.LiveAccepts vm p := by …

-- ToyLoanFlow/Inclusion.lean:218-221
/-- For every program and variance mode, a loan is live for the location-sensitive checker with
kills at overwrites iff it is live for the liveness-gated variant without kills. -/
theorem lsLoanLive_overwrite_iff_liveLoanLive (vm : VarMode) (p : Prog n m) (l q : Fin n) :
    LS.LoanLive .overwrite vm p l q ↔ LS.LiveLoanLive vm p l q := by …
```

Explicit rendering of `lsAccepts_overwrite_iff_liveAccepts` (definitional unfolding of `LS.Accepts`, `LS.LoanLive`, `LS.LiveAccepts` and `LS.LiveLoanLive`; it elaborates with `autoImplicit` off in `namespace Toy.LoanFlow`, with the theorem's binders `n m` as locals, and is definitionally equal to the theorem's statement):

```lean
∀ (vm : VarMode) (p : Prog n m),
    (∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.Holds .overwrite vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q) ↔
    (∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.LiveHolds vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q)
```

**Proof structure.** Every `LS.LiveHolds` step is an `LS.Holds` step, because a local live at the next node is not killed there (`Incl.holds_of_liveHolds`). Conversely, an `LS.Holds` fact whose origin's local is live at the node, killed there, or live at a successor has an `LS.LiveHolds` derivation: a `carry` into a node that does not kill the local, towards a later live point, passes through points at which the local is live (`Incl.liveHolds_of_holds`).

**Hypothesis ledger.** No hypotheses (an equivalence for every variance mode and every program).

**Non-vacuity witness.** `pReassign` is accepted by both checkers and `pCopyThenUse` by neither. (`lsAccepts_overwrite_iff_liveAccepts_nonvacuous`)

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- It equates acceptance and loan liveness on entry to a node; the underlying facts differ: `LS.Holds` may record a loan in an origin of a local that is dead at that point, where `LS.LiveHolds` has no fact (not proved here).
- It relies on the toy kill rule (a node that overwrites a local without reading it): a local that is dead on entry to a node and not overwritten there is dead at every successor, so it stays dead until a node that overwrites it without reading it, where the toy rule kills its origins. It does not say that Polonius's `loan_killed_at` (an assignment to a prefix of the borrowed path) is redundant: the toy language has no loans on places behind references, so it has no counterpart of those kills.
- `KillMode.overwriteAndCopySrc` is not covered: it kills origins of locals that are read, and is unsound (`pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe`, Result 4b).

**Prior art.**

- N. Matsakis, 'An alias-based formulation of the borrow checker', 27 April 2018, https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2018-04-27-an-alias-based-formulation-of-the-borrow-checker.markdown (git blob 338f3cec9fb3d9941232a9c8890d5783e1b710dd); section 'Refining constraint propagation with liveness' at :667-743 resolves a reassignment example of the `pReassign` pattern (with shared loans) by gating propagation on liveness. Blog post.
- Polonius book, rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md: goals :9-12; `loan_killed_at` :29-34; subset rules R1-R3 :69-91; loan rules R4-R6 :93-115 (R6, propagation along CFG edges gated by both `!loan_killed_at` and origin liveness, :109-114); loan liveness R7 and errors R8 :117-136. Documentation.
- N. Matsakis, 'Polonius revisited, part 1', 22 September 2023, https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/; source nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2023-09-22-polonius-part-1.markdown (git blob dd8bd8d9d359062a4f42f42b72e9b1095df35408). Blog post.
- Novelty search: web searches for mechanized (Coq/Rocq, Isabelle, Lean) formalizations of Polonius-style location-sensitive loan analyses, and the sources above; none found that proves soundness of a location-sensitive loan-flow checker together with inclusion of, and strict separation from, a location-insensitive region checker. T1 is claimed, not T3.

**Design question.** Can a location-sensitive checker drop explicit kills at reference overwrites when its propagation along CFG edges is gated by origin liveness?

### R5 — `pVariance_wellTyped_covAccepts_not_safe`

**Plain claim.** The toy program `pVariance` (`c := &x; pp := &mut c; s := &y; *pp := s; write y; read *c`; 6 nodes, exactly 5 locals) is well typed and not safe (there is a walk from its entry that reaches UB under `run` from `RState.init`); with `&mut T` treated as covariant in `T` (`VarMode.cov`) both checkers accept it (`LS.Accepts .overwrite .cov pVariance`, `NLL.Accepts .cov pVariance`), and with the invariant rule both reject it (`¬ LSAccepts pVariance`, `¬ NLLAccepts pVariance`).

**Kind / tier / depth.** counterexample / T0 / shallow.

**Basis.** `execution (Lean kernel check)`. Correspondences with external designs in Prior art: `derived (modeling bridge)` — see Modeling bridges below.

**Statement.**

```lean
-- ToyLoanFlow/Results.lean:223-227
/-- **Result 5.** With `&mut T` treated as covariant in `T`, both checkers accept the unsafe
well-typed program `pVariance`; with the invariant rule both reject it (positive control). -/
theorem pVariance_wellTyped_covAccepts_not_safe :
    WellTyped pVariance ∧ LS.Accepts .overwrite .cov pVariance ∧ NLL.Accepts .cov pVariance ∧
      ¬ Safe pVariance ∧ ¬ LSAccepts pVariance ∧ ¬ NLLAccepts pVariance := …
```

**Hypothesis ledger.** No hypotheses (a statement about concrete programs).

**Non-vacuity witness.** `pVariance` itself. (`pVariance_wellTyped_covAccepts_not_safe`)

**Positive control.** `pVariance_not_lsAccepts`, `pVariance_not_nllAccepts`

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- It shows, by one 6-node straight-line program with exactly 5 locals, that Results 1a and 1c fail for these checkers with `VarMode.cov`; it does not re-prove soundness of a variance table.
- The ablation changes constraint generation for every layer nested inside `&mut`; it is not a statement about any single real subtyping rule.
- Escape hatches: on programs whose generated constraints contain no layer nested inside `&mut` (for example programs without `Stmt.store` whose locals all have reference depth at most 1), `VarMode.cov` and `VarMode.inv` generate the same constraints (not proved here); and `VarMode.inv` already treats layers nested inside shared layers alone covariantly (`invariantAt`), with Results 1a and 1c holding for it.

**Prior art.**

- Corpus package lifetime-variance-subtyping-soundness-and-mutable-reference-invariance (google/zerocopy branch reference, added at commit 0e97e73c8621f82be465f1a54d25aac4f74ac0a5): soundness of a variance table including invariance of `&mut T` in `T`; not re-proved here.
- RFC 2094 (non-lexical lifetimes), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md:778-787 (`&mut T` is invariant: subtyping `&'a mut T_a <: &'b mut T_b` requires `T_a <: T_b` and `T_b <: T_a`). Documentation (design RFC).

**Design question.** Must a location-sensitive checker generate two-way constraints for data behind `&mut`?

### Modeling bridges

**Basis.** `derived (modeling bridge)` + `documentation` / `source` inspection of the pinned upstream commits below.

Each item below is a `derived (modeling bridge)` claim: it relates a toy definition to the documented design of a real
system, with the reasoning stated. Model–system relation: none proved. No measurement was made, and no claim is made
about the acceptance set of any implementation.

**B1 — `NLLAccepts` follows the outlives propagation documented for rustc.** The rustc-dev-guide documents outlives
constraints without locations and their propagation by union:

```text
-- rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11 src/borrow-check/region-inference/constraint-propagation.md:33-36
As a simple example, if we have a liveness constraint `R live at E`,
then we can apply `Values(R) = Values(R) union {E}` to make the constraint be satisfied.
Similarly, if we have an outlives constraints `R1: R2`,
we can apply `Values(R1) = Values(R1) union Values(R2)`.
```

and universal regions containing the whole body:

```text
-- rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11 src/borrow-check/region-inference/lifetime-parameters.md:82-84
All universal regions have an initial liveness constraint that includes the entire function body.
This is because lifetime parameters are defined in the caller and must include the entirety of the
function call that invokes this particular function.
```

`NLL.InRegion` has three kinds of rules matching these (`live`, `outlives` imposed at every node, `universal` for a
returned local). Reasoning: rule-by-rule correspondence. Differences: no `end('a)` elements, no member constraints, no
placeholders, and loans leave scope at region gaps (no kill on assignment to the borrowed path).

**B2 — RFC 2094's proposal is location-aware; `NLLAccepts` is not RFC 2094's proposal.**

```text
-- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md:438-448
However, in order to successfully type the full range of examples that
we would like, we have to go a bit further than just changing
lifetimes to a portion of the control-flow graph. **We also have to
take location into account when doing subtyping checks**. This is in
contrast to how the compiler works today, where subtyping relations
are "absolute". That is, in the current compiler, the type `&'a ()` is
a subtype of the type `&'b ()` whenever `'a` outlives `'b` (`'a: 'b`),
which means that `'a` corresponds to a bigger portion of the function.
Under this proposal, subtyping can instead be established **at a
particular point P**. In that case, the lifetime `'a` must only
outlive those portions of `'b` that are reachable from P.
```

The RFC's discussion of Problem Case #3 states what its design requires:

```text
-- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md:1464-1466
The key to this example is that the first borrow of `map`, with the
lifetime `'m1`, must extend to the end of the `'r`, but only if we
branch to SOME. Otherwise, it should end once we enter the NONE block.
```

and states at `text/2094-nll.md:2017-2019` that "This more flexible setup allows us to handle cases like Problem Case
#3, which RFC 396 would not have accepted." Result 3c is the toy counterpart of the requirement for the
location-insensitive checker: the returned local's region contains every node, so loan `0` stays in scope on the NONE
path.

**B3 — `LS.SubAt` / `LS.Holds` follow the Polonius book's naive rules, with a different kill and no liveness limit on
loan propagation; `LS.LiveHolds` follows rule R6 without kills.**

```text
-- rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md:9-12
Broadly speaking, the goals of the analysis are 1) to track loans:
- from the point and origin in which they are issued, to the points where they are invalidated
- flowing from origin to origin at a single point, via their `subset` relationships
- flowing from point to point in the CFG, according to the origins' liveness (stopping at points where a loan is killed)
```

```text
-- rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df book/src/rules/loans.md:109-114
// R6: propagate loans along the CFG, according to liveness
origin_contains_loan_on_entry(Origin, Loan, TargetPoint) :-
  origin_contains_loan_on_entry(Origin, Loan, SourcePoint),
  !loan_killed_at(Loan, SourcePoint),
  cfg_edge(SourcePoint, TargetPoint),
  (origin_live_on_entry(Origin, TargetPoint); placeholder(Origin, _)).
```

Correspondence: `LS.SubAt.base/trans/persist` ↔ rules R1–R3 (`loans.md:69-91`); `LS.Holds.intro/sub` ↔ R4–R5;
`LS.LoanLive` ↔ R7; `LS.Accepts` ↔ R8 (`loans.md:93-136`). Differences: (i) `LS.Holds.carry` propagates along an edge
unless `killsAt` holds, where R6 requires the origin to be live at the target and the loan not to be killed;
`LS.LiveHolds.carry` requires liveness and has no kills; (ii) `killsAt .overwrite` drops the origins of an overwritten
local, whereas Polonius's `loan_killed_at` (`loans.md:29-34`) fires on assignment to a prefix of the borrowed path;
(iii) the toy uses on-exit facts and moves loans out of read locals across the edge (`step`); (iv) placeholder origins
are not represented. In the toy, (i) is immaterial for acceptance: Result 4c proves that kills at overwrites and liveness
gating accept the same programs.

**B4 — Liveness instead of kills for reassigned references.** The reassignment pattern of `pReassign` (with shared
loans) is the example that Matsakis's 2018 formulation resolves by gating propagation on liveness:

```text
-- nikomatsakis/babysteps@75f5a77af61eddc5a881122fbc216d283acd5687 content/blog/2018-04-27-an-alias-based-formulation-of-the-borrow-checker.markdown:738-742
Using these rules, our original program is accepted. The key point is
that on entry to the line `p = &y`, the variable `p` is dead (its
value is about to be overwritten), and hence its region `'0` is also
dead. Therefore, the `requires` (and `subset`) constraints that affect
it do not propagate forward.
```

Result 4a is the toy counterpart of the rejection without either mechanism, and Result 4c of the observation that
liveness gating makes kills at holder overwrites unnecessary.

**B5 — `&mut` invariance in constraint generation.**

```text
-- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2094-nll.md:778-787
    (T_a <: T_b) @ P
    ('a: 'b) @ P      // <-- a constraint for our inference algorithm
    ------------------------
    (&'a T_a <: &'b T_b) @ P

    (T_a <: T_b) @ P
    (T_b <: T_a) @ P  // (&mut T is invariant)
    ('a: 'b) @ P      // <-- another constraint
    ------------------------
    (&'a mut T_a <: &'b mut T_b) @ P
```

`invariantAt .inv` produces the two-way pairs for layers nested inside `&mut`; `VarMode.cov` drops the reverse pair.
Result 5 is the toy consequence; soundness of a variance table is the subject of the corpus package
`lifetime-variance-subtyping-soundness-and-mutable-reference-invariance` and is not re-proved here.

**B6 — `pc3` renders Problem case #3** (`text/2094-nll.md:201-335`): `x` stands for `*map`, node `0` for the borrow
taken by `map.get_mut(&key)`, node `2` for returning `value`, node `3` for `map.insert(..)`, node `4` for the second
`map.get_mut(&key)`, node `5` for returning its result. The `Option` match is a nondeterministic branch.

### Auxiliary declarations cited by name

Every package declaration named elsewhere in this document and not quoted above, with its statement (proofs elided).

```lean
-- ToyLoanFlow/Facts.lean:46
theorem pc3Loop_safe : Safe pc3Loop := …
```

```lean
-- ToyLoanFlow/Facts.lean:91
theorem pCopyThenUse_lsCopySrcKill_accepts : LS.Accepts .overwriteAndCopySrc .inv pCopyThenUse := …
```

```lean
-- ToyLoanFlow/Facts.lean:95
theorem pVariance_lsCov_accepts : LS.Accepts .overwrite .cov pVariance := …
```

```lean
-- ToyLoanFlow/Facts.lean:119-120
theorem pCopyThenUseShr_lsCopySrcKill_accepts :
    LS.Accepts .overwriteAndCopySrc .inv pCopyThenUseShr := …
```

```lean
-- ToyLoanFlow/Facts.lean:161
theorem pCopyThenUse_not_lsAccepts : ¬ LSAccepts pCopyThenUse := …
```

```lean
-- ToyLoanFlow/Facts.lean:209
theorem pCopyThenUseShr_not_lsAccepts : ¬ LSAccepts pCopyThenUseShr := …
```

```lean
-- ToyLoanFlow/Facts.lean:185
theorem pVariance_not_lsAccepts : ¬ LSAccepts pVariance := …
```

```lean
-- ToyLoanFlow/Facts.lean:188
theorem pVariance_not_nllAccepts : ¬ NLLAccepts pVariance := by …
```

```lean
-- ToyLoanFlow/Facts.lean:219-220
/-- In `pReassign`, `r` is dead on entry to node `2`, which overwrites it. -/
theorem pReassign_r_dead_at_2 : ¬ LiveAt pReassign 2 2 := …
```

```lean
-- ToyLoanFlow/Soundness.lean:90-93
/-- Every record carries the source and mutability of the loan that created it, and its holder's
type is the record's mutability over its target's type. -/
def WF (p : Prog n m) (σ : RState n m) : Prop :=
  ∀ w R, σ.get w = some R → loanOf p R.tag = some (R.tgt, R.mu) ∧ p.ty w = R.mu :: p.ty R.tgt
```

```lean
-- ToyLoanFlow/Soundness.lean:95-98
/-- A valid mutable record excludes valid records of other tags on its target. -/
def Uniq (σ : RState n m) : Prop :=
  ∀ w₁ w₂ (R₁ R₂ : Rec n m), σ.get w₁ = some R₁ → σ.get w₂ = some R₂ → R₁.valid = true →
    R₂.valid = true → R₁.tgt = R₂.tgt → R₁.mu = .mut → R₂.tag = R₁.tag
```

```lean
-- ToyLoanFlow/Soundness.lean:164-169
/-- The invariant at a configuration (node `q` about to execute, state `σ`). -/
structure Inv (p : Prog n m) (q : Fin n) (σ : RState n m) : Prop where
  len : σ.length = m
  wf : WF p σ
  uniq : Uniq σ
  live : ∀ w R, σ.get w = some R → LiveAt p w q → LocalOK p q w R
```

```lean
-- ToyLoanFlow/Soundness.lean:171-172
theorem inv_init (p : Prog n m) : Inv p p.entry RState.init where
  len := …
```

```lean
-- ToyLoanFlow/Soundness.lean:641-643
theorem step_inv {p : Prog n m} {q q'' : Fin n} {σ σ' : RState n m} (hwt : WellTyped p)
    (hacc : LSAccepts p) (hI : Inv p q σ) (hex : exec p q σ = .ok σ')
    (hq'' : q'' ∈ p.succ q) : Inv p q'' σ' := by …
```

```lean
-- ToyLoanFlow/Soundness.lean:698-699
theorem exec_ne_ub {p : Prog n m} {q : Fin n} {σ : RState n m}
    (hacc : LSAccepts p) (hI : Inv p q σ) : exec p q σ ≠ .ub := by …
```

```lean
-- ToyLoanFlow/Soundness.lean:745-747
theorem run_not_ub {p : Prog n m} (hwt : WellTyped p) (hacc : LSAccepts p) :
    ∀ (π : List (Fin n)) (x : Fin n) (σ : RState n m), IsWalk p.succ (x :: π) →
      Inv p x σ → (run p σ (x :: π)).isUB = false := by …
```

```lean
-- ToyLoanFlow/Inclusion.lean:95-96
theorem holds_of_liveHolds {vm : VarMode} {p : Prog n m} {l : Fin n} {o : Origin m}
    {q : Fin n} (h : LS.LiveHolds vm p l o q) : LS.Holds .overwrite vm p l o q := by …
```

```lean
-- ToyLoanFlow/Inclusion.lean:103-107
theorem liveHolds_of_holds {vm : VarMode} {p : Prog n m} {l : Fin n} {o : Origin m}
    {q : Fin n} (h : LS.Holds .overwrite vm p l o q)
    (hneed : LiveAt p o.1 q ∨ killsAt .overwrite p q o.1 = true ∨
      ∃ q' ∈ p.succ q, LiveAt p o.1 q') :
    LS.LiveHolds vm p l o q := by …
```

```lean
-- ToyLoanFlow/Inclusion.lean:169-173
theorem liveHolds_to_nll {vm : VarMode} {p : Prog n m} (hwt : WellTyped p)
    {l : Fin n} {o : Origin m} {q : Fin n} (h : LS.LiveHolds vm p l o q) :
    ∃ d : Fin m, loanDst p l = some d ∧ o.2 < (p.ty o.1).length ∧
      (∀ u : Fin n, NLL.InRegion vm p o u → NLL.InRegion vm p (d, 0) u) ∧
      (q = l ∨ NLL.InScope vm p l q) := by …
```

```lean
-- ToyLoanFlow/Inclusion.lean:212-215
/-- For every program and variance mode, the location-sensitive checker without kills accepts
a subset of the programs that the checker with kills at overwrites accepts. -/
theorem lsAccepts_of_lsNoKillAccepts (vm : VarMode) (p : Prog n m)
    (h : LS.Accepts .none vm p) : LS.Accepts .overwrite vm p := …
```

```lean
-- ToyLoanFlow/Inclusion.lean:235-239
/-- Every well-typed program accepted by the location-insensitive checker `NLL.Accepts vm` is
accepted by the liveness-gated location-sensitive variant without kills `LS.LiveAccepts vm`,
for every variance mode `vm`. -/
theorem liveAccepts_of_wellTyped_of_nllAccepts (vm : VarMode) (p : Prog n m)
    (hwt : WellTyped p) (h : NLL.Accepts vm p) : LS.LiveAccepts vm p := by …
```

```lean
-- ToyLoanFlow/Results.lean:71-74
/-- Counterexample for `hwt` in Result 1a: an ill-typed program that the location-insensitive
checker accepts and that reaches UB. -/
theorem nllAccepts_not_safe_without_wellTyped :
    ¬ WellTyped pUntypedHolder ∧ NLLAccepts pUntypedHolder ∧ ¬ Safe pUntypedHolder := …
```

```lean
-- ToyLoanFlow/Results.lean:77-81
/-- Counterexample for `hwt` in Result 1c: an ill-typed program with an acyclic CFG that the
location-sensitive checker accepts and that reaches UB. -/
theorem lsAccepts_not_safe_without_wellTyped :
    ¬ WellTyped pUntypedStore ∧ Acyclic pUntypedStore ∧ LSAccepts pUntypedStore ∧
      ¬ Safe pUntypedStore := …
```

```lean
-- ToyLoanFlow/Results.lean:85-88
/-- Counterexample for the acceptance hypothesis of Results 1a and 1c: a well-typed program
with an acyclic CFG that reaches UB (both checkers reject it). -/
theorem wellTyped_acyclic_not_safe :
    WellTyped pCopyThenUse ∧ Acyclic pCopyThenUse ∧ ¬ Safe pCopyThenUse := …
```

```lean
-- ToyLoanFlow/Results.lean:91-94
/-- Non-vacuity of Result 1a, including a witness with non-empty generated constraints. -/
theorem safe_of_wellTyped_of_nllAccepts_nonvacuous :
    (WellTyped pReassign ∧ NLLAccepts pReassign) ∧
      (WellTyped pStoreSafe ∧ NLLAccepts pStoreSafe ∧ gen .inv pStoreSafe 3 ≠ []) := …
```

```lean
-- ToyLoanFlow/Results.lean:98-101
/-- Non-vacuity of Result 1c, with a cyclic CFG and with non-empty generated constraints. -/
theorem safe_of_wellTyped_of_lsAccepts_nonvacuous :
    (WellTyped pc3Loop ∧ ¬ Acyclic pc3Loop ∧ LSAccepts pc3Loop) ∧
      (WellTyped pStoreSafe ∧ LSAccepts pStoreSafe ∧ gen .inv pStoreSafe 3 ≠ []) := …
```

```lean
-- ToyLoanFlow/Results.lean:105-107
/-- Counterexample for `hwt` in Result 2 (at `vm = .inv`). -/
theorem lsAccepts_of_nllAccepts_fails_without_wellTyped :
    ¬ WellTyped pUntypedHolder ∧ NLLAccepts pUntypedHolder ∧ ¬ LSAccepts pUntypedHolder := …
```

```lean
-- ToyLoanFlow/Results.lean:110-116
/-- Result 2 fails when well-typedness is required only at the nodes reachable from the entry
node: `pUnreachUntyped` is well typed at every reachable node and accepted by the
location-insensitive checker, and the location-sensitive checker rejects it. -/
theorem lsAccepts_of_reachWellTyped_of_nllAccepts_fails :
    (∀ q, Reach pUnreachUntyped.succ pUnreachUntyped.entry q →
      StmtWellTyped pUnreachUntyped (pUnreachUntyped.stmt q)) ∧
      NLLAccepts pUnreachUntyped ∧ ¬ LSAccepts pUnreachUntyped := …
```

```lean
-- ToyLoanFlow/Results.lean:119-121
/-- Counterexample for `h` in Result 2: a well-typed program that the location-sensitive
checker rejects. -/
theorem wellTyped_not_lsAccepts : WellTyped pCopyThenUse ∧ ¬ LSAccepts pCopyThenUse := …
```

```lean
-- ToyLoanFlow/Results.lean:124-129
/-- Non-vacuity of Result 2, for both variance modes and with non-empty generated
constraints. -/
theorem lsAccepts_of_wellTyped_of_nllAccepts_nonvacuous :
    (WellTyped pReassign ∧ NLLAccepts pReassign) ∧
      (WellTyped pVariance ∧ NLL.Accepts .cov pVariance) ∧
      (WellTyped pStoreSafe ∧ NLLAccepts pStoreSafe ∧ gen .inv pStoreSafe 3 ≠ []) := …
```

```lean
-- ToyLoanFlow/Results.lean:156-159
/-- Reference point for Result 3c: when the first loan of problem case #3 is used instead of
returned (`pc3NoReturn`), both checkers accept the program. -/
theorem pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts :
    WellTyped pc3NoReturn ∧ Safe pc3NoReturn ∧ NLLAccepts pc3NoReturn ∧ LSAccepts pc3NoReturn := …
```

```lean
-- ToyLoanFlow/Results.lean:173-175
/-- Result 2 fails for the location-sensitive checker without kills (canonical form). -/
theorem lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails :
    ¬ ∀ p : Prog 5 3, WellTyped p → NLLAccepts p → LS.Accepts .none .inv p := …
```

```lean
-- ToyLoanFlow/Results.lean:194-196
/-- Result 1c fails with kills at copy sources (canonical form). -/
theorem safe_of_wellTyped_of_lsCopySrcKillAccepts_fails :
    ¬ ∀ p : Prog 4 3, WellTyped p → LS.Accepts .overwriteAndCopySrc .inv p → Safe p := …
```

```lean
-- ToyLoanFlow/Results.lean:199-203
/-- Non-vacuity of Result 4c: `pReassign` is accepted by both sides of the equivalence and
`pCopyThenUse` by neither. -/
theorem lsAccepts_overwrite_iff_liveAccepts_nonvacuous :
    (LSAccepts pReassign ∧ LS.LiveAccepts .inv pReassign) ∧
      (¬ LSAccepts pCopyThenUse ∧ ¬ LS.LiveAccepts .inv pCopyThenUse) := …
```

```lean
-- ToyLoanFlow/Results.lean:209-216
/-- The statement "Result 2 needs kills in the location-sensitive checker" is false: the
liveness-gated variant without kills `LS.LiveAccepts` satisfies the inclusion of Result 2 for
every variance mode and accepts `pReassign`, which the variant with neither kills nor liveness
gating (`LS.Accepts .none`) rejects. -/
theorem refuted_result2_needs_kills :
    (∀ {n m : Nat} (vm : VarMode) (p : Prog n m), WellTyped p → NLL.Accepts vm p →
      LS.LiveAccepts vm p) ∧
      LS.LiveAccepts .inv pReassign ∧ ¬ LS.Accepts .none .inv pReassign := …
```

```lean
-- ToyLoanFlow/Results.lean:231-233
/-- Result 1c fails with covariant `&mut` (canonical form). -/
theorem safe_of_wellTyped_of_lsCovAccepts_fails :
    ¬ ∀ p : Prog 6 5, WellTyped p → LS.Accepts .overwrite .cov p → Safe p := …
```

```lean
-- ToyLoanFlow/Results.lean:236-238
/-- Result 1a fails with covariant `&mut` (canonical form). -/
theorem safe_of_wellTyped_of_nllCovAccepts_fails :
    ¬ ∀ p : Prog 6 5, WellTyped p → NLL.Accepts .cov p → Safe p := …
```

## Boundaries

### Non-claims (all results)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker or about any Polonius implementation. Model–system relation: none proved.
- `LSAccepts`, `LS.LiveAccepts`, and `NLLAccepts` are the package's own checkers. `NLLAccepts` is not RFC 2094's location-aware proposal, and `killsAt .overwrite` is not Polonius's `loan_killed_at`.
- `Safe p` excludes the UB that `exec` defines: dereferencing, storing through, or returning an invalidated record. Copies of a reference keep its tag, so two locals holding copies of one mutable record are one permission and may be used interleaved without UB; `Safe` is not the statement that no two usable `&mut` references alias.
- `WellTyped p` checks statement-level layer shapes at every node of `Fin n`, reachable from `p.entry` or not, and performs no definite-initialization check: `RState.init` gives every local `none`, and `exec` maps `deref`, `store`, and `ret` on a local holding `none` to `.halt`, not `.ub`; so `Safe p` does not exclude uses of uninitialized reference locals.
- There is no `StorageDead`: every plain-data local outlives the body (standing for storage reachable from the parameters, such as `*map`), and `exec` on `ret` checks the returned record's validity and nothing else; returning a valid reference to a local is not UB in the toy (no frame is deallocated), so dangling references to stack storage are not modelled.
- `StmtWellTyped` restricts `deref` and `ret` to depth-1 references (`[.shr]` or `[.mut]`), so no reference of depth at least 2 is dereferenced or returned; inner origins `(v, k)` with `k ≥ 1` matter for `Safe` through `Stmt.store`, the one statement that moves a record into the local behind a reference.
- Every hypothesis named "well typed" or "accepted" quantifies over every node of `Fin n`, reachable from `p.entry` or not. For Result 2 the weakening to reachable nodes is false (`lsAccepts_of_reachWellTyped_of_nllAccepts_fails`); for Results 1a and 1c it is not examined.

### Attractive stronger conclusions not established

- That rustc's NLL rejects, or that any Polonius implementation accepts, the Rust function `get_default` of RFC 2094.
- That the toy `LS` checker coincides with Polonius, or that the acceptance sets of `NLLAccepts` and `LSAccepts` differ exclusively on Problem Case #3 variants such as `pc3` and `pc3Loop`.
- That `Safe` rules out aliasing `&mut` copies created via `Stmt.copy`.
- That Polonius's `loan_killed_at` (assignment to a prefix of the borrowed path) is redundant given origin liveness: Result 4c concerns `killsAt .overwrite` on overwrites of the reference-holding local in a language without loans on places behind references.

### Escape hatches

- **Result 4a (`pReassign` rejected without kills):** The rejection disappears when CFG-edge loan propagation is gated by target-entry origin liveness (`LiveAt`): `LS.LiveAccepts` has no kills, accepts `pReassign` (`refuted_result2_needs_kills`), and accepts the exact same programs as `LS.Accepts .overwrite` (`lsAccepts_overwrite_iff_liveAccepts`, Result 4c).
- **Result 4b (copy-source kills unsound):** Adding a move checker on `&mut` alone would not eliminate the toy counterexample mechanism on shared references, because `pCopyThenUseShr` exhibits the same four-part failure using shared `&D` references (`pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe`). Restricting copy-source kills to copy sources dead after the copy is not examined.
- **Result 5 (`VarMode.cov` unsound):** Unsoundness requires a reference layer nested inside `&mut` in the generated constraints; `VarMode.inv` already treats layers nested solely inside `.shr` covariantly (`invariantAt`), for which Results 1a and 1c prove soundness, and on programs whose generated constraints contain no layer nested inside `&mut`, `VarMode.cov` and `VarMode.inv` emit the same constraints (not proved here).

### Known not to apply (proved)

- **Result 2 without kills and without liveness gating:** False (`lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails`, witnessed by `pReassign`).
- **Draft prose conjecture "Result 2 needs kills in the location-sensitive checker":** Disproved in Lean (`refuted_result2_needs_kills`): the zero-kill liveness-gated checker `LS.LiveAccepts` satisfies the Result 2 inclusion for every `VarMode` and accepts `pReassign`.
- **Result 2 weakened to well-typedness on entry-reachable nodes:** False (`lsAccepts_of_reachWellTyped_of_nllAccepts_fails`, witnessed by `pUnreachUntyped`).
- **Results 1a and 1c without `WellTyped`:** False (`nllAccepts_not_safe_without_wellTyped` on `pUntypedHolder`; `lsAccepts_not_safe_without_wellTyped` on `pUntypedStore`).
- **Result 1c with copy-source kills (`KillMode.overwriteAndCopySrc`):** False (`safe_of_wellTyped_of_lsCopySrcKillAccepts_fails`, witnessed by `pCopyThenUse`).
- **Results 1a and 1c with covariant `&mut` (`VarMode.cov`):** False (`safe_of_wellTyped_of_nllCovAccepts_fails` and `safe_of_wellTyped_of_lsCovAccepts_fails`, witnessed by `pVariance`).

### Not examined

Reads of a reference through a reference (`t := *p`); reborrow loans (`&mut *r`) and loans on places behind references; moves and a move checker; two-phase borrows (examined in a separate model in corpus package `two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges`, cited under prior art); match guards and fake borrows; `StorageDead` and stack-frame deallocation on return; function calls and unwinding; placeholder-region errors; compound data other than one opaque value per local; backward CFG propagation of origin subset relations; whether Results 1a and 1c survive requiring well-typedness at entry-reachable nodes alone; whether kills at copy sources are sound when restricted to dead copy sources; and any empirical or formal comparison with rustc's borrow checker, any Polonius implementation, or RFC 2094's location-aware (`('a: 'b) @ P` / `end('r)`) specification.

### Unknown

None of the hypotheses in the card ledgers has tightness `unknown`, and no frozen statement was left unproved, weakened, or dropped.

## Evidence

### Kernel check and toolchain

- **Basis:** `execution (Lean kernel check)`.
- **Toolchain:** `leanprover/lean4:v4.34.1` (GitHub repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).
- **Library target:** `ToyLoanFlow` (`lean/lakefile.toml`, core Lean only, no Mathlib, no `[[require]]` dependencies; 12 library modules: `lean/ToyLoanFlow.lean` and 11 submodules under `lean/ToyLoanFlow/*.lean`).
- **Axiom audit (`audit/axioms.json`):** `Lean.collectAxioms` over all 657 non-internal declarations in `ToyLoanFlow` confirms zero `sorry`, `admit`, `native_decide`, `axiom`, or `opaque` declarations; every declaration depends on a subset of `propext`, `Classical.choice`, and `Quot.sound`.
- **Statement and closure hashes (`audit/statements.json`):** Records SHA-256 of `toString (repr ci.type)` (`statement_sha256`), SHA-256 of the newline-joined sorted `name : repr type [:= repr value]` transitive package-constant closure excluding theorem proof terms (`closure_sha256`), and `closure_size` for all 112 declarations referenced in `results.json`.

### Main result theorems

| Card | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 | Closure size |
| :--- | :--- | :--- | :--- | :--- | ---: |
| R1a | `Toy.LoanFlow.safe_of_wellTyped_of_nllAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `7c7035a419fa9f4024e32f52addc2d9c5105e225f03fb95a48126ce8d4ef2be5` | `0d8df54d27fdb5cf17700efa5b2a3653ad0b14f9b81969f311b8490440d3bcd3` | 111 |
| R1c | `Toy.LoanFlow.safe_of_wellTyped_of_lsAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `50fed8016f24f63ab02e6798cd8726ea15bd80629930974fd0e39e21360bab40` | `83e8481e9158a830a3012d3b342ef88a069af4bfd65c6e7d6fd0e6a058ae8bf1` | 123 |
| R2 | `Toy.LoanFlow.lsAccepts_of_wellTyped_of_nllAccepts` | `Quot.sound`, `propext` | `ba06799cb9fc2ef0dd1bc88fd9cac4e065f0403e786eadb3acfd29f92a9e08f5` | `2e13a2bda4eb6101cc6e9999701c4b857a043d9688ceb4e694f06fe0e8c81cf5` | 90 |
| R3a | `Toy.LoanFlow.pc3_wellTyped_safe_lsAccepts_not_nllAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `2805d6e4d14dc8fd71bfc91f98985bdf52455d91fd95d8eb179f5fa7037f98ce` | `3af972c2c14c29c2b3f634db35ce1d345fde170a301fb4d4baed9e0980ebb1ad` | 139 |
| R3b | `Toy.LoanFlow.pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `cf8e2d220048bea947fbb4782671d88f038fa119f8bbf8be5bfbc7cbc411f95e` | `9d731437af1a19c49c42df0c653f2246b104e1aa63b071a6f4175662557b9a40` | 139 |
| R3c | `Toy.LoanFlow.pc3_loan0_at_insertion` | `Classical.choice`, `Quot.sound`, `propext` | `196faa2644c570b8c5403208f757567ad33116f43ed50b78a05cdb991efe2e62` | `4621df4c01f218293601bc4766007a0ac98cbc9726d5b8411b816ebf0ad6953d` | 89 |
| R4a | `Toy.LoanFlow.pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `41cc1d6d26c4004061928d0ca0bba5ead5ad36f8ce86e88c77cad2f4b3e3464a` | `c97766f7a9fe7c2489c086d2a8ec0fbc89aeb96e83cfee225f4768a0e1e00d10` | 138 |
| R4b | `Toy.LoanFlow.pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe` | `Classical.choice`, `Quot.sound`, `propext` | `2b441ac63bb2acb12c60e7c381c6d242a50550b16ef60b01df918bdc007556fe` | `569c58784a484e6c3ea1f9a1412f6bb86db41dc2d330804d9424fbae87642256` | 128 |
| R4b | `Toy.LoanFlow.pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe` | `Classical.choice`, `Quot.sound`, `propext` | `4b60cd1943ac2e4fa9ddbef579e4cb71397904e632c12693956c49f7ac7b27b0` | `73918def80c9f56d7ecb67a9b61a5a5de4cdbb7d254fe489133c25b36b5ea882` | 128 |
| R4c | `Toy.LoanFlow.lsAccepts_overwrite_iff_liveAccepts` | `Quot.sound`, `propext` | `ade3a95d55db0de74c0c5e51a8d251e22558238b322c7745a8e69f657b1cec8c` | `55f552dcfe38356776dbb0d3b7b7604f946172f6aa27e3c6aaee365a6e423ee9` | 83 |
| R4c | `Toy.LoanFlow.lsLoanLive_overwrite_iff_liveLoanLive` | `Quot.sound`, `propext` | `4a7bd8de56c805217301612845672f995cc3a8878b930bc081e4f2b1a1f89ac8` | `934708dfd66e5ae10e92e10aa4c810d6a9c429fb115e66a73791c3fa04ed62b6` | 75 |
| R5 | `Toy.LoanFlow.pVariance_wellTyped_covAccepts_not_safe` | `Classical.choice`, `Quot.sound`, `propext` | `adf0238b2ec3da581f4a799a810a9f54e4217706e5701e756fe9419e2d486c71` | `1c022606b17c20385fec1949c3c24a726f82c35afd57149cce45030abd5aa7db` | 138 |

### Complete statement and closure hash record (all 112 card-referenced declarations)

| Declaration | Axioms | Statement SHA-256 | Closure SHA-256 | Closure size |
| :--- | :--- | :--- | :--- | ---: |
| `Toy.LoanFlow.Acc` | *(none)* | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.Acyclic` | *(none)* | `b20597b47da54d7a1ff9c38016effc735d1f0d882d967535e1bb37f894dfd027` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.Conflicts` | `propext` | `e15f08d05e8dbf7f7de56d24b6b10d2bb6faa3d04c1ce0ca7653ad32f81c06b4` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.Edges` | *(none)* | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.Incl.holds_of_liveHolds` | `propext` | `39060cf8971a972b0f8d3fd58d66401ed8d4b6e914328c9dc2d68edfa6d8e8d0` | `2869bb28b7a653411da87ea49e02425b465e072e792acd9ccfd445c0127d6a61` | 73 |
| `Toy.LoanFlow.Incl.liveHolds_of_holds` | `Quot.sound`, `propext` | `3f9c88ef3f51f7e98df264e987b6cbbe86ac48ba07a372b425f3b3aad364a8b1` | `2869bb28b7a653411da87ea49e02425b465e072e792acd9ccfd445c0127d6a61` | 73 |
| `Toy.LoanFlow.Incl.liveHolds_to_nll` | `Quot.sound`, `propext` | `791edd51c01e07334dfbb040a41d18ac491f7f4efb1c22ea0019633fb4fa9615` | `1023fa17997e9bcce8a1c75ffc8e62d828a310095fc8f18b43d184520597e658` | 73 |
| `Toy.LoanFlow.IsWalk` | *(none)* | `acd4cfbb57fa020ec6fe39e8b1dcf155410c70005a3f89cfd3f36ccdb340ed35` | `101db1d537c833b5c08d04a1201f0318f49117955221b0d0d86f2aaf0800af58` | 1 |
| `Toy.LoanFlow.KillMode` | *(none)* | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.LS.Accepts` | `propext` | `885ea89edc93935a3b30ee75cb9b183af6bc9096ce164c775b8fbcdd8b3ff5cb` | `9e7581d0d72e69fb7574772439d188ce259c2ea4e21cfd976779abfefb919ec4` | 24 |
| `Toy.LoanFlow.LS.Holds` | `propext` | `07fcd8d763088d2b5f8544376bf04bc1967d808e90e966cedf73907c18315d2c` | `3ea4814f819352eb9fcbc655e9cd9232e5cd78bb1629478d59c5a834a2945998` | 25 |
| `Toy.LoanFlow.LS.LiveAccepts` | `propext` | `bb48b7a84b2345fd5e265e4960924d4da7fd8b0a44cbd462609288ec266ab8ce` | `9ab6b1914cf100c906e858be5939ce8adbf3836031f674c7c8a7ca9bc09a3048` | 20 |
| `Toy.LoanFlow.LS.LiveHolds` | `propext` | `86ff7a62d39e76033ed8215ac0425063ecf686a8220cc1aa8eb62404c907ed92` | `e6eef169f182f5b8503d8fa919fdc3ae7b72b9b0090a27629d29ef014e3d4acc` | 21 |
| `Toy.LoanFlow.LS.LiveLoanLive` | `propext` | `5dc9cf2b5617eb329b6474048232993a9dd17b31f3406329c6c9463704562020` | `9ab6b1914cf100c906e858be5939ce8adbf3836031f674c7c8a7ca9bc09a3048` | 20 |
| `Toy.LoanFlow.LS.LoanLive` | `propext` | `a214535fde54692001cd1e291172c0e641bd8d264d5f4b61c0446545f70fe633` | `9e7581d0d72e69fb7574772439d188ce259c2ea4e21cfd976779abfefb919ec4` | 24 |
| `Toy.LoanFlow.LS.SubAt` | `propext` | `f1221f7718858473096b7babf6215904d2ac2edb0bd6001fae4d97328e305ba0` | `e6eef169f182f5b8503d8fa919fdc3ae7b72b9b0090a27629d29ef014e3d4acc` | 21 |
| `Toy.LoanFlow.LSAccepts` | `propext` | `b20597b47da54d7a1ff9c38016effc735d1f0d882d967535e1bb37f894dfd027` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.LiveAt` | `propext` | `2bdc2fd330e2ed890692365ea9ec48c949476b54e21386e17365420330fed359` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.Mutbl` | *(none)* | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.NLL.Accepts` | `propext` | `bb48b7a84b2345fd5e265e4960924d4da7fd8b0a44cbd462609288ec266ab8ce` | `9ab6b1914cf100c906e858be5939ce8adbf3836031f674c7c8a7ca9bc09a3048` | 20 |
| `Toy.LoanFlow.NLL.InRegion` | `propext` | `54796ca87795c6ac2c3459290611382f2f35c95381b35230b0a26a582f189889` | `e6eef169f182f5b8503d8fa919fdc3ae7b72b9b0090a27629d29ef014e3d4acc` | 21 |
| `Toy.LoanFlow.NLL.InScope` | `propext` | `22730db97ab63df99d127a503cce3cd7a1e9b503750d9dfe52688aa09ec09851` | `9ab6b1914cf100c906e858be5939ce8adbf3836031f674c7c8a7ca9bc09a3048` | 20 |
| `Toy.LoanFlow.NLLAccepts` | `propext` | `b20597b47da54d7a1ff9c38016effc735d1f0d882d967535e1bb37f894dfd027` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.Origin` | *(none)* | `f90689f02c7655dad6c5a27959ac8ac133356b1596ff28fa512baf22ef8416cd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.Outcome` | *(none)* | `59c83c6c1a2d8daa2e6fdc35fdd9d3f4d73008fd4fa4f9258813d0bd42f98061` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.Outcome.isUB` | `propext` | `4e15d4fd9b2461353bc63648ddb5ad925d2ae8006fdd510c3e89f0db6b171be8` | `1de391c376eb29d3af994be36bb659b556f96e394f1e770cd70268b46fa6a1be` | 10 |
| `Toy.LoanFlow.Prog` | *(none)* | `59c83c6c1a2d8daa2e6fdc35fdd9d3f4d73008fd4fa4f9258813d0bd42f98061` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.RState` | *(none)* | `59c83c6c1a2d8daa2e6fdc35fdd9d3f4d73008fd4fa4f9258813d0bd42f98061` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.RState.get` | `propext` | `6454d19f760c4d1e5c98c717ea77b88f63a63395f541326402924ed82ad3c990` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.RState.init` | *(none)* | `c23ff0b23fb55ba2adcc8a1f3c199409121dc2db6c39af9280ee963ec822a6a5` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.RState.set` | *(none)* | `d1f2d7903d73ea9949da9b8489f344eb6ba2cbddc947c87758f13b4ddb0e1565` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.Reach` | *(none)* | `648004def33f39493ccb35bf5894cb110e85d78887a1e73deaac2c3d0799b14d` | `101db1d537c833b5c08d04a1201f0318f49117955221b0d0d86f2aaf0800af58` | 1 |
| `Toy.LoanFlow.ReachesUB` | `propext` | `4226408202ffc2521ea4ab2374bf791f3e2f1bee186dc3c6a792c45542edfc97` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.Rec` | *(none)* | `59c83c6c1a2d8daa2e6fdc35fdd9d3f4d73008fd4fa4f9258813d0bd42f98061` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.Safe` | `propext` | `b20597b47da54d7a1ff9c38016effc735d1f0d882d967535e1bb37f894dfd027` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.Sound.Inv` | `propext` | `e19cda2ff63068bf3fdd5d47bdd3f5411bcd4fbdec86249dd61997f0c85340a7` | `84a5f53f0a5d101bdf2939628ced4e556b4a7151761476a37e34bf5e58e44bce` | 20 |
| `Toy.LoanFlow.Sound.Uniq` | `propext` | `3d0309eefd5058b0fa1d362dc274032614adcd508fb61bb52f9731ee7d338b70` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.Sound.WF` | `propext` | `7755f5c9a221b3bf258813dc612c7ff99ca50999edfe97a6d90813fd9fd9a1d9` | `84a5f53f0a5d101bdf2939628ced4e556b4a7151761476a37e34bf5e58e44bce` | 20 |
| `Toy.LoanFlow.Sound.exec_ne_ub` | `propext` | `bf7e47e2df5b78b40c03b4831d5c9015edf5947d70c7db7aeeda9a16773f37e1` | `95702fd7c68031344cfef4c4c7cd312036bc1a54cc695627421cf49eee33ad13` | 109 |
| `Toy.LoanFlow.Sound.inv_init` | `propext` | `23b04f219287b87a331a43874685172496ece912d0442b26a35e790bf6682452` | `8e877cb17fe91b84cdaacbb99cd2d8cdf97599b04a6b34796e056b4ee1e1ba2d` | 86 |
| `Toy.LoanFlow.Sound.run_not_ub` | `Classical.choice`, `Quot.sound`, `propext` | `4d6debaa47c279d95d9d274087a5a3cae1182c661ef69b081a43941668817666` | `b75ccfc775625d77c688ce4e301c751ff6c859159a9187410a28ac2f057b4fd5` | 125 |
| `Toy.LoanFlow.Sound.step_inv` | `Classical.choice`, `Quot.sound`, `propext` | `a513a2f1728130a54d1e7483b6b006743127611b1dc37915ea2e05624f8c6736` | `5bec546cb5a6a78b519c7b48dfb4ac908473bfab98449d4d685507f2a6c5087b` | 112 |
| `Toy.LoanFlow.Stmt` | *(none)* | `f90689f02c7655dad6c5a27959ac8ac133356b1596ff28fa512baf22ef8416cd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.Stmt.accesses` | *(none)* | `15c09b96db21aee7702a206f777145433442e5d4181f64fa1e402d3ecb1d7aad` | `29a6d5184bf2351858944bb82cb10d15f70aa4edb9f3f135a27ff0e10f3d2770` | 14 |
| `Toy.LoanFlow.Stmt.defs` | `propext` | `6bf674567b8a8870437bfbce45e40a5cb41f741e1a950b21fffd2aef831fc874` | `29a6d5184bf2351858944bb82cb10d15f70aa4edb9f3f135a27ff0e10f3d2770` | 14 |
| `Toy.LoanFlow.Stmt.uses` | *(none)* | `6bf674567b8a8870437bfbce45e40a5cb41f741e1a950b21fffd2aef831fc874` | `29a6d5184bf2351858944bb82cb10d15f70aa4edb9f3f135a27ff0e10f3d2770` | 14 |
| `Toy.LoanFlow.StmtWellTyped` | *(none)* | `40e5dbf043b03d9a90714aeb60b2b06e10a9f22ae006a02902dbfcf2dcbe7c9b` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.VarMode` | *(none)* | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Toy.LoanFlow.WellTyped` | *(none)* | `b20597b47da54d7a1ff9c38016effc735d1f0d882d967535e1bb37f894dfd027` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.exec` | `propext` | `a4fc0f058dbe9a7f45565be3882c40e2eaa3b9b5948b49c67e2365a5263a5a4a` | `b2ac8864f165142abb609bb74a08dfee4bd1d578a44efca36884f7972153851c` | 24 |
| `Toy.LoanFlow.gen` | `propext` | `2488dc75fe654ccc923626d4db93e9bbaedba4e8e528ee58a313099e42e95454` | `e6eef169f182f5b8503d8fa919fdc3ae7b72b9b0090a27629d29ef014e3d4acc` | 21 |
| `Toy.LoanFlow.invalidate` | *(none)* | `9b31e126d8dce4e2d819f8b33fa29d2f8731bd0ac405bf2460420db167edbb72` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.invariantAt` | *(none)* | `36c83de8d05b269a1e8e39e91c4bc678812d4a1e2152d93e9da64e7bf7e6abfc` | `34af60586fce0d7d7e60d221b9a4f83476e4b1782d683e74ce0ba840023d76c3` | 6 |
| `Toy.LoanFlow.killsAt` | `propext` | `4d57318431e03135b431c2b6a1aca2248d941141c8e59f31a10ff22d30fd684f` | `4d388c8405c189f9a3a2f3e7692cc36afc5965626c84eee6b454d42a456cb1d6` | 21 |
| `Toy.LoanFlow.liveAccepts_of_wellTyped_of_nllAccepts` | `Quot.sound`, `propext` | `e1675ad3a8960c546c52a5b85783ebaa8b7220f20098b6a304af7efbafc8d071` | `c0e6935a5a27ba1716fef77bb9a8e99d3d36d9b2be3c0e9a14d436f886507247` | 80 |
| `Toy.LoanFlow.loanDst` | `propext` | `88b21a3d0fa71b6837524d8d7b3a22c40fde6b7577fc678ff8b859886f0b5c66` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.loanOf` | `propext` | `1e3d625852682efe8c7d454639b04ffc6c8517c636aafb523928921460b265cc` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.lsAccepts_not_safe_without_wellTyped` | `Classical.choice`, `Quot.sound`, `propext` | `7e822e45770b072784361105d306b5ec8b80cc0715cb2084d5b9b03caf2f8265` | `082e326723ac59cd380e5e973eeb40bde963e1a824b10a6d4fc8b606b7dcf05e` | 132 |
| `Toy.LoanFlow.lsAccepts_of_lsNoKillAccepts` | `propext` | `fd0fcfbde36fa2954910a99dd9c39003171326e535c38c386afd6d5e6095cdaf` | `f40fbfb0ee426931452b49beb156206564b4e9cb6ec045a2cb821221d67622fa` | 76 |
| `Toy.LoanFlow.lsAccepts_of_nllAccepts_fails_without_wellTyped` | `Quot.sound`, `propext` | `5642fd180c58c7ee04acba47ff23856e2d4b6afe8c3c6189cd8feefa49838e92` | `125c85f78e77bbc23f731ff306d74839e501c45c8bd0ef91a40d4efe30c890b7` | 96 |
| `Toy.LoanFlow.lsAccepts_of_reachWellTyped_of_nllAccepts_fails` | `Quot.sound`, `propext` | `e5df89a3ab26b74644766928385ff048c81de40a9de6faf22d702ad42ce0469a` | `654d8358023d7e7ee80cd0f7511e4ca392e688b974977bc14b84e71b84bfb0a3` | 100 |
| `Toy.LoanFlow.lsAccepts_of_wellTyped_of_nllAccepts` | `Quot.sound`, `propext` | `ba06799cb9fc2ef0dd1bc88fd9cac4e065f0403e786eadb3acfd29f92a9e08f5` | `2e13a2bda4eb6101cc6e9999701c4b857a043d9688ceb4e694f06fe0e8c81cf5` | 90 |
| `Toy.LoanFlow.lsAccepts_of_wellTyped_of_nllAccepts_nonvacuous` | `Quot.sound`, `propext` | `a1d2ab84e9c2e3c81167366810ad10830c3fb9003a7720d0359b68a19b8c4650` | `bbd350431918d33845f69451395b2d5a6e964350a24429730a435e24acfc5d51` | 80 |
| `Toy.LoanFlow.lsAccepts_overwrite_iff_liveAccepts` | `Quot.sound`, `propext` | `ade3a95d55db0de74c0c5e51a8d251e22558238b322c7745a8e69f657b1cec8c` | `55f552dcfe38356776dbb0d3b7b7604f946172f6aa27e3c6aaee365a6e423ee9` | 83 |
| `Toy.LoanFlow.lsAccepts_overwrite_iff_liveAccepts_nonvacuous` | `Classical.choice`, `Quot.sound`, `propext` | `ab8f3a08d93b58d6f63c2ba9a16f7a93fbfda7f1eb222d34b8204d36ab2814de` | `f32166ac2f7349e03b894019a9cce93339f5e73a8966ac99208f8824e9ccb078` | 93 |
| `Toy.LoanFlow.lsLoanLive_overwrite_iff_liveLoanLive` | `Quot.sound`, `propext` | `4a7bd8de56c805217301612845672f995cc3a8878b930bc081e4f2b1a1f89ac8` | `934708dfd66e5ae10e92e10aa4c810d6a9c429fb115e66a73791c3fa04ed62b6` | 75 |
| `Toy.LoanFlow.lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails` | `Quot.sound`, `propext` | `55579d743b3c031fd9a8628ddc40af01280e521c6dd0f69b41a3bf265aa496ee` | `8acc26cea1d56780911424c23860122ae9f89b62e6dab4c65f7637ff02022a24` | 91 |
| `Toy.LoanFlow.nllAccepts_not_safe_without_wellTyped` | `Quot.sound`, `propext` | `d4fbeb4671808a448ba41461db00caec35fff53ae13fae24636fba8843fd6b63` | `aa908c388e02bd36e80930e15912a4dd5c94c65d3ba23eded642613305a7d5c8` | 115 |
| `Toy.LoanFlow.pCopyThenUse` | `propext` | `bf9afeea715a61ff8005536b95f5d5fc9c1df6dc381ef991302bdf0f53dde56d` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pCopyThenUseShr` | `propext` | `bf9afeea715a61ff8005536b95f5d5fc9c1df6dc381ef991302bdf0f53dde56d` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pCopyThenUseShr_lsCopySrcKill_accepts` | `Classical.choice`, `Quot.sound`, `propext` | `5393feb991e10057b0c5ab11a81c9362044d8e172c60dd43ae0c4d4df47b4dfe` | `889a5bb0573c0497bf1889eb522373f9933a896e459b40c66785461eacb1bfb3` | 81 |
| `Toy.LoanFlow.pCopyThenUseShr_not_lsAccepts` | `Quot.sound`, `propext` | `9cb2edc7bdedb654b42ce96cbecc564bc484ff4ca603b784106f3c8060f1a448` | `4a7721c6009c406e818f80a4784ab78c0730fe988a671a74e6bb848cb3f0550f` | 82 |
| `Toy.LoanFlow.pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe` | `Classical.choice`, `Quot.sound`, `propext` | `4b60cd1943ac2e4fa9ddbef579e4cb71397904e632c12693956c49f7ac7b27b0` | `73918def80c9f56d7ecb67a9b61a5a5de4cdbb7d254fe489133c25b36b5ea882` | 128 |
| `Toy.LoanFlow.pCopyThenUse_lsCopySrcKill_accepts` | `Classical.choice`, `Quot.sound`, `propext` | `f2fd90803bfe93bc1901384e7c1edc1cc7dbe975e7b9fea13e52102eee281cc3` | `d4be8cbcad6d8a9596963197c8b437b9e7a43a5bbb571d0ea5a4b8cff0b7f2f7` | 81 |
| `Toy.LoanFlow.pCopyThenUse_not_lsAccepts` | `Quot.sound`, `propext` | `7579872336aa8a300d691dd456a9f8caef03ad1d326a33f112c2f08b8f9c99d3` | `f4c0ec997a35c486e6e45474fbba93e56187cfc9fd8819f2e1e75f5c1d4e3de8` | 82 |
| `Toy.LoanFlow.pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe` | `Classical.choice`, `Quot.sound`, `propext` | `2b441ac63bb2acb12c60e7c381c6d242a50550b16ef60b01df918bdc007556fe` | `569c58784a484e6c3ea1f9a1412f6bb86db41dc2d330804d9424fbae87642256` | 128 |
| `Toy.LoanFlow.pReassign` | `propext` | `aeebf7274e68b20369858efea184bb72e8eb2199bf039786bacf8f9b155cb021` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pReassign_r_dead_at_2` | `Quot.sound`, `propext` | `5895c808bd022b291eb6910f64db72ded933189a4b7127dff641da9f453b5f81` | `e6a4815fc507e63d66b8a78a03876c9dba5065dcb4375113813300f45413b778` | 35 |
| `Toy.LoanFlow.pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `41cc1d6d26c4004061928d0ca0bba5ead5ad36f8ce86e88c77cad2f4b3e3464a` | `c97766f7a9fe7c2489c086d2a8ec0fbc89aeb96e83cfee225f4768a0e1e00d10` | 138 |
| `Toy.LoanFlow.pStoreSafe` | `propext` | `3cee1010162e861d16998762c0491db41c0b97a822b630c1532ef2f8dadbea0f` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pUnreachUntyped` | `propext` | `91db09539f6e82645ce68121b5e2d2b17b964a1d019c5ea54c80f9ea15604e76` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pUntypedHolder` | `propext` | `27513b36fd39f661b2e496da4f7894703be20f4b1c9cdcd1fd425ea9346ec4a9` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pUntypedStore` | `propext` | `a1eafee4afabd9894f51c4fdde67e6e5980e3298ea1e1d7ca2941f3d6f312f7e` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pVariance` | `propext` | `3cee1010162e861d16998762c0491db41c0b97a822b630c1532ef2f8dadbea0f` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pVariance_lsCov_accepts` | `Classical.choice`, `Quot.sound`, `propext` | `7942bc674a626690858e480d023c70523e48113f1d1a7605dacd38943ee5cdf1` | `1281de5be65213f60b93cc8025f2f8c46ebf5ac83feb13c165e399ea0c40fa38` | 81 |
| `Toy.LoanFlow.pVariance_not_lsAccepts` | `Quot.sound`, `propext` | `ad6230ff5716799f4dcb32a9fbd4e346321fab57bce8a3d69c87e3938fb1304b` | `f99c247963800261fcc20dc89355a15027354ddcf0e4fff4d9e19c250baf23ea` | 82 |
| `Toy.LoanFlow.pVariance_not_nllAccepts` | `Quot.sound`, `propext` | `13453d05806c99ff037cbe0d62068fe7ef6d676c1f16f1d9e14ce22b9ce3682c` | `52c4a3a54c5df86fb28a895a70054fb750befb68f7f3783fead0052283900a41` | 70 |
| `Toy.LoanFlow.pVariance_wellTyped_covAccepts_not_safe` | `Classical.choice`, `Quot.sound`, `propext` | `adf0238b2ec3da581f4a799a810a9f54e4217706e5701e756fe9419e2d486c71` | `1c022606b17c20385fec1949c3c24a726f82c35afd57149cce45030abd5aa7db` | 138 |
| `Toy.LoanFlow.pc3` | `propext` | `0db2be051b1d8605e8aeb5e12a61ddb1bf48a846f356767c1fddd70d83266540` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pc3Loop` | `propext` | `91db09539f6e82645ce68121b5e2d2b17b964a1d019c5ea54c80f9ea15604e76` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pc3Loop_safe` | `Quot.sound`, `propext` | `8cb25bfbb8fc6fac670040c0c750699a2f07e2052f0f6958ee2e7398b9b96081` | `1c509fb41f4b8224e7294c24853c4e790b9808575f34336e0672c67b81a72585` | 76 |
| `Toy.LoanFlow.pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `cf8e2d220048bea947fbb4782671d88f038fa119f8bbf8be5bfbc7cbc411f95e` | `9d731437af1a19c49c42df0c653f2246b104e1aa63b071a6f4175662557b9a40` | 139 |
| `Toy.LoanFlow.pc3NoReturn` | `propext` | `0db2be051b1d8605e8aeb5e12a61ddb1bf48a846f356767c1fddd70d83266540` | `6c881e8f2f20cde14d4b22a44c342fe7c6c475e0feb53335668094df7c49c48c` | 17 |
| `Toy.LoanFlow.pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `9543596a8b47a7a24476c5ab64093380103eb8b85d73ce903541ef987723e094` | `8a916c9401fc97dbd9401cd2172fe14bc8d24305687947706ffbbe793130738b` | 139 |
| `Toy.LoanFlow.pc3_loan0_at_insertion` | `Classical.choice`, `Quot.sound`, `propext` | `196faa2644c570b8c5403208f757567ad33116f43ed50b78a05cdb991efe2e62` | `4621df4c01f218293601bc4766007a0ac98cbc9726d5b8411b816ebf0ad6953d` | 89 |
| `Toy.LoanFlow.pc3_wellTyped_safe_lsAccepts_not_nllAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `2805d6e4d14dc8fd71bfc91f98985bdf52455d91fd95d8eb179f5fa7037f98ce` | `3af972c2c14c29c2b3f634db35ce1d345fde170a301fb4d4baed9e0980ebb1ad` | 139 |
| `Toy.LoanFlow.placeRead` | *(none)* | `8fa06d83f150ad03d7ccf2645d18bfae24773c9768a893c6f0dac4c3f11d045e` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.placeWrite` | *(none)* | `8fa06d83f150ad03d7ccf2645d18bfae24773c9768a893c6f0dac4c3f11d045e` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.refuted_result2_needs_kills` | `Classical.choice`, `Quot.sound`, `propext` | `9265832306ada724d1b03e3db585dbc6cdd9c73df20fe8c7efd82e75259d5d59` | `e4f2df30d32b205bc60267921c7f465232981913f5ce716feb6a63673fca2cbe` | 102 |
| `Toy.LoanFlow.relate` | *(none)* | `ee3cc8d7bcabba036c7a57e753cfdf35aebb0613d19ed52c13c9dc688e17df56` | `db7e76b4659bda381fea41d57689effbcf4f8c94114b1219313444e3d14a026d` | 7 |
| `Toy.LoanFlow.run` | `propext` | `166945601543d131936c6ccee833b1d202ee18780e23176f90c4c9ec2df9c3e5` | `b2ac8864f165142abb609bb74a08dfee4bd1d578a44efca36884f7972153851c` | 24 |
| `Toy.LoanFlow.safe_of_wellTyped_of_lsAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `50fed8016f24f63ab02e6798cd8726ea15bd80629930974fd0e39e21360bab40` | `83e8481e9158a830a3012d3b342ef88a069af4bfd65c6e7d6fd0e6a058ae8bf1` | 123 |
| `Toy.LoanFlow.safe_of_wellTyped_of_lsAccepts_nonvacuous` | `Classical.choice`, `Quot.sound`, `propext` | `c2954da17670e0a5112e6fc7ecd001c59d2b23075f0bf7e096967c389d792479` | `8f122fe00f8c949b250788c251292c7d3a75402a0c182cec765d504c9455bc6e` | 97 |
| `Toy.LoanFlow.safe_of_wellTyped_of_lsCopySrcKillAccepts_fails` | `Classical.choice`, `Quot.sound`, `propext` | `e80bd2f6bdc1be4cb33d580e2c31948748cac959885e798d6b4224422518bf1e` | `39a5c4525ffa26ac9d1953d8bd689b7f662b7218c17830789b43085c59f577ee` | 122 |
| `Toy.LoanFlow.safe_of_wellTyped_of_lsCovAccepts_fails` | `Classical.choice`, `Quot.sound`, `propext` | `9613b10cb7cb635eafc1eaf635f1fa0d271eba279d01cdc0c15ff83a375fb829` | `39a5c4525ffa26ac9d1953d8bd689b7f662b7218c17830789b43085c59f577ee` | 122 |
| `Toy.LoanFlow.safe_of_wellTyped_of_nllAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `7c7035a419fa9f4024e32f52addc2d9c5105e225f03fb95a48126ce8d4ef2be5` | `0d8df54d27fdb5cf17700efa5b2a3653ad0b14f9b81969f311b8490440d3bcd3` | 111 |
| `Toy.LoanFlow.safe_of_wellTyped_of_nllAccepts_nonvacuous` | `Quot.sound`, `propext` | `ba1e72cf802e7b66ddf664d3a80f15ac44752baf9d65ababf9942f47bd230075` | `720e247cc4bc2c03fb7d8ec05a457bfb8867ca0f8abb353ac182a5d7bca523d4` | 79 |
| `Toy.LoanFlow.safe_of_wellTyped_of_nllCovAccepts_fails` | `Quot.sound`, `propext` | `813fbd8826a6e4aa1be495067399c9a80c7cf35de783c58e27ef0f33fe27bf0b` | `7915f7adee743164cb9327fb8a09df1c880baa45dc9894772ad3e9ba62886485` | 110 |
| `Toy.LoanFlow.thruRead` | *(none)* | `5f94d8420160762e378b06637e41811689124604371066f8e26fcd3148ef5a1f` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.thruWrite` | *(none)* | `5f94d8420160762e378b06637e41811689124604371066f8e26fcd3148ef5a1f` | `8ac6c3851930e54e889bd7d1f920f13d7c84c14f33f1c21eb594e498fc3a4182` | 6 |
| `Toy.LoanFlow.wellTyped_acyclic_not_safe` | `Quot.sound`, `propext` | `f9bf234b81c73192dcfb7eb08ead06d2769d4e5f4c40ab268503668b5f191e32` | `d92aa96d378820bc355c83ce0c4cf6ad412295afd59e569ada66aa4e880cdea4` | 83 |
| `Toy.LoanFlow.wellTyped_not_lsAccepts` | `Quot.sound`, `propext` | `60a287fe860e177d26091a3fa2919c4ac308b55401ff1763f8949c294d40e211` | `a772d1b1535d3ca4d92e470462f230a8d6a07e5af7fa002e5f4f7d15c65bacae` | 87 |

### Primary sources

- **Lean 4 toolchain (`v4.34.1`):** `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, `https://github.com/leanprover/lean4/commit/5045d0056413266e57c625dcd7c365b10e377c52`.
- **Rust RFC 2094 (Non-Lexical Lifetimes):** `rust-lang/rfcs`, commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2094-nll.md` (Problem Case #3 at `:201-335`, location-aware subtyping at `:438-448`, `&mut T` invariance rules at `:778-787`, Layer 4 named-lifetime requirement on Problem Case #3 at `:1464-1466`, summary remark at `:2017-2019`). Role: `documentation` (design RFC).
- **Guide to Rustc Development (region inference):** `rust-lang/rustc-dev-guide`, commit `d946d7402d269990f3b64baabaf6592409791c11`, `src/borrow-check/region-inference/constraint-propagation.md:33-36` (union propagation of liveness and location-insensitive outlives constraints) and `src/borrow-check/region-inference/lifetime-parameters.md:82-84` (universal regions initialized to the entire function body). Role: `documentation`.
- **The Polonius Book (loan analysis rules):** `rust-lang/polonius`, commit `bfd4c945b7713d0e66a3cde80475d9a4494740df`, `book/src/rules/loans.md` (analysis goals at `:9-12`, `loan_killed_at` at `:29-34`, subset rules R1–R3 at `:69-91`, loan rules R4–R6 at `:93-115` including R6 at `:109-114`, loan liveness R7 and errors R8 at `:117-136`). Role: `documentation`.
- **N. Matsakis (2018), "An alias-based formulation of the borrow checker":** *Baby Steps* blog, 27 April 2018, `https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/`; source `nikomatsakis/babysteps`, commit `75f5a77af61eddc5a881122fbc216d283acd5687`, `content/blog/2018-04-27-an-alias-based-formulation-of-the-borrow-checker.markdown` (git blob `338f3cec9fb3d9941232a9c8890d5783e1b710dd`, lines `:667-743`, quoted at `:738-742`). Role: `documentation` (blog post).
- **N. Matsakis (2023), "Polonius revisited, part 1" and "Polonius revisited, part 2":** *Baby Steps* blog, 22 September 2023 and 29 September 2023, `https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/` and `https://smallcultfollowing.com/babysteps/blog/2023/09/29/polonius-part-2/`; source `nikomatsakis/babysteps`, commit `75f5a77af61eddc5a881122fbc216d283acd5687`, `content/blog/2023-09-22-polonius-part-1.markdown` (git blob `dd8bd8d9d359062a4f42f42b72e9b1095df35408`) and `content/blog/2023-09-29-polonius-part-2.markdown` (git blob `d93a78cd9bf41f84f9ff532631988fec653e48ec`). Role: `documentation` (blog posts).
- **Rust project blog posts on Polonius:** `rust-lang/blog.rust-lang.org`, commit `8666f7c3a86260ec58e4d914d451b14613c690a4`, `content/inside-rust/polonius-update/index.md` (R. Rakic and N. Matsakis, "Polonius update", 6 October 2023, git blob `4e860b1d76b8fdcd473ed09302356b09d8ae5ab7`) and `content/enabling-polonius-alpha-on-nightly/index.md` (J. Huey, "Enabling the next iteration of the borrow checker on nightly", 4 August 2026, git blob `f99931718eecc43da0ae083dbead70b8c376eb1f`). Role: `documentation` (cited for context, not relied on as normative).
- **Academic papers:**
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, "Stacked Borrows: An Aliasing Model for Rust", *Proc. ACM Program. Lang.* 4 (POPL), 2020, `doi:10.1145/3371109`.
  - N. Villani, J. Hostert, D. Dreyer, R. Jung, "Tree Borrows", *Proc. ACM Program. Lang.* 9 (PLDI), 2025, `doi:10.1145/3735592`.
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: Securing the Foundations of the Rust Programming Language", *Proc. ACM Program. Lang.* 2 (POPL), 2018, `doi:10.1145/3158154`.
  - S. Ho, A. Fromherz, J. Protzenko, "Sound Borrow-Checking for Rust via Symbolic Semantics", *Proc. ACM Program. Lang.* 8 (ICFP), 2024, `doi:10.1145/3674640` (extended preprint `arXiv:2404.02680`).
  - A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, "Oxide: The Essence of Rust", `arXiv:1903.00982v4` (2021).
  - D. J. Pearce, "A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust", *ACM TOPLAS* 43(1), 2021, `doi:10.1145/3443420`.
  - L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust Programs", *Proc. ACM Program. Lang.* 8 (PLDI), 2024, `doi:10.1145/3656422`.
  - Z. Grannan, A. Bílý, J. Fiala, J. Geer, M. de Medeiros, P. Müller, A. J. Summers, "Place Capability Graphs: A General-Purpose Model of Rust's Ownership and Borrowing Guarantees", *Proc. ACM Program. Lang.* 9 (OOPSLA2), 2025, `doi:10.1145/3763122`.
- **Related corpus provenance (not `REPORT.json` subjects):** `IsWalk` (`ToyLoanFlow/Semantics.lean:36-42`) is copied verbatim from `lean/ToyTwoPhase/Graph.lean:20-25` (git blob `d80d4d0f36d0386d3ec3d32cdba33afb4e5e4a8d`) of `two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges` (`google/zerocopy` branch `reference`, commit `a92dad5d362315aa1e07acade3aeedb183dd2d18`); variance-table soundness is mechanized separately in `lifetime-variance-subtyping-soundness-and-mutable-reference-invariance` (`google/zerocopy` branch `reference`, commit `0e97e73c8621f82be465f1a54d25aac4f74ac0a5`).

## Revalidation

Requirements: `elan` (so that `lake` selects the pinned toolchain `leanprover/lean4:v4.34.1` from `lean/lean-toolchain`) and `python3`.

### Primary automated check

Run from the package root directory:

```bash
python3 support/revalidate.py .
```

`support/revalidate.py` leaves the package directory untouched: it copies `lean/` to a temporary directory and checks that:

1. `lake build` succeeds cleanly on the `ToyLoanFlow` library;
2. no `.lean` source file (after stripping line and nested block comments) contains `sorry`, `admit`, `native_decide`, or an `axiom` declaration;
3. `Lean.collectAxioms` on every non-internal declaration of `ToyLoanFlow` is a subset of `{propext, Classical.choice, Quot.sound}`; and
4. for every Lean declaration referenced in `results.json` (`lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` fields) and recorded in `audit/statements.json`, the recomputed `statement_sha256` (SHA-256 of the UTF-8 string `toString (repr ci.type)`), `closure_sha256` (SHA-256 of the newline-joined sorted lines `c : repr cc.type` plus ` := repr v` for non-theorem constants across all `ToyLoanFlow` constants reachable from `ci.type` via types, non-theorem values, and inductive constructors, excluding theorem proof bodies), and `closure_size` match `audit/statements.json` byte-for-byte.

It prints `REVALIDATED` and exits with status `0` iff all four checks pass.

### Direct `lake` + `lean/RevalidationAudit.lean` check

To run the Lean build and inspect axioms and statement/closure hashes directly without `support/revalidate.py`, run from the package root directory:

```bash
(cd lean && lake build && lake env lean RevalidationAudit.lean) > /tmp/reval_out.txt
python3 - <<'PY'
import hashlib, json, re

raw = open("/tmp/reval_out.txt", encoding="utf-8").read()
m = re.search(r"LEANLIB_REVAL_JSON (\{.*\})", raw)
assert m, "missing LEANLIB_REVAL_JSON output"
payload = json.loads(m.group(1))

allowed = {"propext", "Classical.choice", "Quot.sound"}
rec_ax = json.load(open("audit/axioms.json", encoding="utf-8"))["declarations"]
got_ax = {d["name"]: sorted(d["axioms"]) for d in payload["decls"]}
assert all(set(v) <= allowed for v in got_ax.values()), "disallowed axiom"
assert got_ax == rec_ax, "axiom map differs from audit/axioms.json"

rec_st = json.load(open("audit/statements.json", encoding="utf-8"))["statements"]
got_st = {}
for s in payload["stmts"]:
    assert not s.get("missing"), f"missing declaration: {s['name']}"
    got_st[s["name"]] = {
        "statement_sha256": hashlib.sha256(s["type_repr"].encode("utf-8")).hexdigest(),
        "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode("utf-8")).hexdigest(),
        "closure_size": len(s["closure"]),
    }
assert got_st == rec_st, "statement/closure hash mismatch against audit/statements.json"
print(f"OK: {len(got_ax)} declarations audited, {len(got_st)} hashes verified")
PY
```

### Scope of revalidation

A passing run re-verifies the Lean kernel proofs, axiom bounds, and exact statement and definition-closure hashes of `ToyLoanFlow` under `leanprover/lean4:v4.34.1`. It does not re-verify the `derived (modeling bridge)` prose against newer upstream revisions of RFC 2094, `rustc-dev-guide`, or the Polonius book; to check whether upstream documentation changed, diff the files and line ranges listed under Evidence (Primary sources) against their pinned commits.
