# Call-site inlining: slot renaming, cleanup splicing, capability guards and caller locations (toy model, Lean 4)

## Summary

This package is a Lean 4 toy model of call-site inlining in a MIR-like control-flow-graph language: functions with numbered locals, basic blocks marked normal or cleanup, calls with unwind actions, per-frame cleanup and unwinding, source scopes with `inlined` / `inlinedParent` links, per-function capability lists with a program-wide ABI map, and caller-location (`trackCaller`) frames. Lean project: `lean/` (library `ToyInline`, namespace `Toy.Inline`), Lean `v4.34.1`, core Lean and no Mathlib. It contains 19 results (R1–R19), every one proved and kernel-checked; every declaration of the library depends on at most the axioms `propext` and `Quot.sound`. The four whole-program inlining theorems (R2, R3, R8, R9) are proved by a stuttering forward simulation between each original toy program and its inlined toy program (Findings, "How the whole-program inlining theorems are proved").

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler. Real systems appear under Findings, "Modeling bridge", as `derived (modeling bridge)` prose citing documented behaviour.

- **R1** (`frameRel_step_of_injective_of_avoids`; theorem, T0, proved): For a renaming `ρ` that is injective on callee locals below `n` (`RenameInjectiveOn ρ n`) and maps them outside the list `L` of caller locals live across the call (`RenameAvoids ρ n L`), a statement `s` mentioning only locals below `n` (`StmtLocalsLt n s`), and stores with `FrameRel ρ n L C G M` (the merged store `M` agrees with the caller store `C` on `L` and with the callee store `G` through `ρ` below `n`): executing `s` on `G` and its renaming `s.rename ρ ns` on `M` with the auxiliary store-level function `stmtStore` again yields stores related by `FrameRel ρ n L C`, and the two lists of emitted values are equal, for every scope shift `ns`. `stmtStore` updates the store for `assign`, emits a value for `emit`, and maps `needCap` and `loc` to `(st, [])`, so the statement says nothing about capability faults or `loc` events.
- **R2** (`inline_behEquiv_retTemp_of_capsEq`; theorem, T1, proved): At a call site `IsCallSite p f b F ci G` (function `f` of `p` is `F`, its block `b` ends in the call `ci`, whose callee is `G`), suppose: every local mentioned by `F` and by `G` is below its declared count (`LocalsBounded F`, `LocalsBounded G`); every jump target of `F` is one of its blocks (`BlocksBounded F`); `F` and `G` satisfy `ScopesWF` (scope `0` exists and carries neither `inlined` nor `inlinedParent`, every `inlinedParent` link of scope `i` points to an index `t < i`, and every scope named by a `loc` statement or call is in range); callee locals `1 ≤ i < G.nlocals` go to host slots at or above `F.nlocals` (`SlotsFresh`) that are pairwise distinct (`SlotsInjective`); the return place goes to a temporary `t` (`cfg.ret = .temp t`) with `F.nlocals ≤ t` and `t` different from every callee slot (`TempFresh`); `continue` edges are redirected, `resume` is rewritten by the call's unwind action and the `rustc` scope-link rule is used; and `F.caps = G.caps` (equal lists). Then `BehEquiv p (inline p f b cfg)`: from every entry, every finite observation of `run` of either program is a prefix of an observation of the other, so the maximal event sequences (including cleanup `out` events, in order, and `loc` events) and the outcomes (including `ub`, `capFault`, `aborted` and `unwound`) coincide.
- **R3** (`inline_behEquiv_retDest_of_destUnobservedOnUnwind`; theorem, T1, proved): At a call site `IsCallSite p f b F ci G`, suppose `LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G` and `SlotsInjective cfg G` (as in `inline_behEquiv_retTemp_of_capsEq`); the callee's return place is the call's destination (`cfg.ret = .dest`; there is no return temporary); every unwind edge of `F` leads to a cleanup block and every successor of a cleanup block of `F` is a cleanup block (`CleanupClosed F`); no cleanup block of `F` reads `ci.dest` (`DestNotReadInCleanup F ci.dest`); `continue` edges are redirected, `resume` is rewritten by the call's unwind action, the `rustc` scope-link rule is used; and `F.caps = G.caps`. Then `BehEquiv p (inline p f b cfg)`: from every entry the maximal event sequences and outcomes of `run` coincide.
- **R4** (`terminalHolds_iff_of_behEquivAt`; theorem, T0, proved): If `p` and `q` are behaviourally equivalent from entry `e` (`BehEquivAt p q e`, defined from `run`), then for every predicate `P` on observations, `P` holds of every halted `run` of `p` from `e` (`TerminalHolds P p e`) iff `P` holds of every halted `run` of `q` from `e`.
- **R5** (`safetyHolds_iff_of_behEquivAt_of_prefixClosed`; theorem, T0, proved): If `p` and `q` are behaviourally equivalent from entry `e` and the predicate `S` on observations is closed under observation prefixes (`PrefixClosed S`), then `S` holds of the observation of `run` of `p` from `e` at every step budget (`SafetyHolds S p e`) iff it holds of every such observation of `q`.
- **R6** (`inlined_vc_not_callee_contract`; counterexample, T1, proved): In the program `vcP`, whose caller passes the constant `7` to the callee `gP` (which panics into its cleanup on argument `0`), and its canonical inlining `vcQ`: "no escaped panic" (`NoPanic`) holds of every halted `run` of `vcQ` and of `vcP` from the caller's entry `e0`; from the callee's own entry with argument `0` (`⟨1, [0], 0⟩`), `run` of `vcP` and of `vcQ` with step budget 30 (at most 30 steps) both give the events `[out 100]` and the outcome `unwound`, so `NoPanic` fails for both programs from that entry.
- **R7** (`capsSubset_needed_inlined_needCap_faults`; counterexample, T1, proved): In `needP` the callee `needG` holds and uses capability `3` and the host `capF []` holds none. With the canonical configuration for one host local (temp mode, `t = 1`), every hypothesis of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` and of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree` other than `CapsSubset G F` holds, and `CapsSubset needG (capF [])` fails. `run` of `needP` from `e0` gives `[out 1]` and `returned 0`; `run` of the inlined program, in temp mode and in destination mode, gives no events and the outcome `capFault`; neither inlined program is behaviourally equivalent to `needP`.
- **R8** (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive`; theorem, T1, proved): At a call site `IsCallSite p f b F ci G`, suppose every hypothesis of `inline_behEquiv_retTemp_of_capsEq` other than `F.caps = G.caps` holds: `LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G`, `SlotsInjective cfg G`, `cfg.ret = .temp t`, `TempFresh t cfg F G` (`F.nlocals ≤ t` and `t` differs from every callee slot), redirected `continue` edges, `resume` rewritten by the call's unwind action and the `rustc` link rule. Suppose further that every capability in the callee's list is in the caller's list (`CapsSubset G F`), every `needCap c` in the callee names a capability in the callee's list (`CapLegal G`), no block of the callee (reachable or not) terminates in an ABI-sensitive call (`AbiInsensitive G`) and the inlined call itself is not ABI-sensitive (`ci.abiSensitive = false`). Then `BehEquiv p (inline p f b cfg)`.
- **R9** (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`; theorem, T1, proved): At a call site `IsCallSite p f b F ci G`, suppose every hypothesis of `inline_behEquiv_retTemp_of_capsEq` other than `F.caps = G.caps` holds (`LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G`, `SlotsInjective cfg G`, `cfg.ret = .temp t`, `TempFresh t cfg F G`, redirected `continue` edges, `resume` rewritten by the call's unwind action, the `rustc` link rule), every capability in the callee's list is in the caller's list (`CapsSubset G F`), every `needCap c` in the callee names a capability in the callee's list (`CapLegal G`), and `p.abi F.caps = p.abi G.caps` (`AbiAgree p F G`). Then `BehEquiv p (inline p f b cfg)`, also when ABI-sensitive calls are present.
- **R10** (`capsSubset_guard_insufficient`, `capsSubset_guard_insufficient_witness`; impossibility, T1, proved): `capsSubset_guard_insufficient`: it is not the case that for every program, call site and configuration satisfying `IsCallSite p f b F ci G`, `LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G`, `SlotsInjective cfg G`, `cfg.ret = .temp t`, `TempFresh t cfg F G`, redirected `continue` edges, `resume` rewritten by the call's unwind action, the `rustc` link rule, `CapsSubset G F`, `CapLegal G` and `ci.abiSensitive = false`, the inlined program is behaviourally equivalent to the original. `capsSubset_guard_insufficient_witness` exposes the instance: in `abiP` (ABI map `abiC`) the host `capF [1]` has capability list `[1]` and the callee `abiG` has `[]`; all those hypotheses hold (canonical configuration, `t = 1`); `abiP.abi [1] ≠ abiP.abi []`; the callee's ABI-sensitive call passes `5` in the original (`run` gives `[out 5]`, `returned 0`) and `6` after inlining (`[out 6]`, `returned 0`); so `¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1))`.
- **R11** (`locValue_inline_calleeScope`; theorem, T1, proved): For any `trackCaller` predicate `tr`, if every `inlinedParent` link of the host's scope table points to a smaller index (`ScopeParentsBelow F.scopes`), the callee's table satisfies `ScopeTreeWF` (scope `0` exists and carries neither `inlined` nor `inlinedParent`, and its links point to smaller indices), `s < G.scopes.length`, and the `rustc` link rule is used, then the caller-location value `locValue` at the shifted scope `F.scopes.length + s` of the merged table `F.scopes ++ linkScopes link F ci G`, with span `sp` and implicit location `il`, equals `locValue` at `s` in the callee's own table with implicit location `some (locValue tr F.scopes ci.scope ci.span il)` if `tr ci.callee` and `none` otherwise. (`locValue` runs the `inlinedParent` walk `walk` with fuel equal to the table length; if the walk stops at an inlined scope of an untracked callee it returns the current span, and if it reaches the end of the chain it returns the implicit location if present and the current span otherwise.)
- **R12** (`locValue_inline_callerScope`; theorem, T1, proved): For any `trackCaller` predicate `tr`, any link rule, call data `ci` and callee `G`, if every `inlinedParent` link of the host's table points to a smaller index (`ScopeParentsBelow F.scopes`) and `s < F.scopes.length`, then `locValue` at `s` in the merged table `F.scopes ++ linkScopes link F ci G` equals `locValue` at `s` in `F.scopes`, for every span `sp` and implicit location `il`.
- **R13** (`scopesWF_inlineFn`; theorem, T1, proved): For any configuration `cfg` and any call data `ci`: if block `b` of `F` is `B`, `F` satisfies `ScopesWF` (clean scope `0`, links pointing to smaller indices, scope references in range), every `inlinedParent` link of the callee's table points to a smaller index (`ScopeParentsBelow G.scopes`) and the callee's scope references are in range (`ScopeRefsBounded G`), then `inlineFn F b B ci G cfg` satisfies `ScopesWF`.
- **R14** (`innermost_policy_wrong_for_tracked_chain`; counterexample, T1, proved): For tracked `k` called (span `20`) by tracked `g` called (span `10`) by untracked `f` (`chainP true`), and `chainQ true` obtained by inlining `g` into `f` and then the copied call to `k`: `runWith pol (chainP true)` with step budget 30 (at most 30 steps) from `e0` gives `[loc 10]` and `returned 0` for every policy `pol` (`.walk`, `.innermost`, `.outermost`); `run` (the scope walk) of `chainQ true` with step budget 40 (at most 40 steps) gives `[loc 10]`, `returned 0`, and `BehEquivAt (chainP true) (chainQ true) e0`; the innermost-span policy on `chainQ true` gives `[loc 20]`, `returned 0`, so `chainP true` and `chainQ true` are not behaviourally equivalent from `e0` under `.innermost`.
- **R15** (`outermost_policy_wrong_for_untracked_wrapper`; counterexample, T1, proved): For tracked `k` called (span `20`) by an untracked wrapper `g` called (span `10`) by `f` (`chainP false`), and `chainQ false` obtained by inlining both calls: `runWith pol (chainP false)` with step budget 30 (at most 30 steps) from `e0` gives `[loc 20]` and `returned 0` for every policy `pol`; `run` of `chainQ false` with step budget 40 (at most 40 steps) gives `[loc 20]`, `returned 0`, and `BehEquivAt (chainP false) (chainQ false) e0`; the outermost-span policy on `chainQ false` gives `[loc 10]`, `returned 0`, so the two programs are not behaviourally equivalent from `e0` under `.outermost`.
- **R16** (`linkRule_ignoreParent_changes_location`; counterexample, T1, proved): In `linkP1`, the host `linkF1` already contains the inlined body of the tracked `linkG` (called from the untracked host with span `10`); its block `3` holds the copied call `linkCi1` to the tracked `linkK`, issued from a nested, non-inlined scope of the inlined callee with span `20`. With `linkCfg` (the canonical configuration for 2 host locals except `link = .ignoreParent`, the variant that sets the outermost callee scope's `inlinedParent` to none when the callsite scope is not inlined), every hypothesis of `inline_behEquiv_retTemp_of_capsEq` other than `hlink` holds (`t = 2`), and `CleanupClosed linkF1` and `DestNotReadInCleanup linkF1 linkCi1.dest` hold. `run` of `linkP1` from `e0` gives `[loc 10]`, `returned 0`; `run` of the inlined program with `linkCfg` and with `linkCfg.withDest` gives `[loc 20]`, `returned 0`; neither inlined program is behaviourally equivalent to `linkP1`.
- **R17** (`behEquiv_trans`; theorem, T0, proved): If `BehEquiv p q` and `BehEquiv q r` (behavioural equivalence from every entry), then `BehEquiv p r`.
- **R18** (`inline_order_changes_body`; counterexample, T1, proved): With the canonical configuration, in `ordP` (`h` calls `f`, `f` calls `g`): inlining `g` into `f` and then the new `f` into `h` (`ordQ1`) gives function `0` (`h`) a body with 11 statements; inlining `f` into `h` and then `g` into the copied call (`ordQ2`) gives 9 statements; so the two bodies of `h` differ; from the entry `e0 = ⟨0, [], 0⟩` both programs are behaviourally equivalent to `ordP`.
- **R19** (`localsBounded_inlineFn`; theorem, T1, proved): For any configuration `cfg`: if block `b` of `F` is `B`, `B` ends in the call `ci` (`B.term = .call ci`), and `F` and `G` satisfy `LocalsBounded`, then the new body `inlineFn F b B ci G cfg` satisfies `LocalsBounded`. Its declared-local count is `max (max F.nlocals (maxSucc (cfg.rename ci.dest) G.nlocals)) (retTempSucc cfg)`, which also covers the return temporary when the callee declares no locals.

Non-claims for every result are listed with its card under Findings and collected under Boundaries.

## Applicability

### Model fidelity

A toy MIR-like control-flow-graph language, not a mirror of any compiler's data structures. It is meant to capture the bookkeeping a call-site inliner performs: moving callee locals into fresh host slots, substituting the return place, rewriting `ret`/`resume`/unwind edges, appending and linking source scopes, and the capability (target-feature) and ABI conditions under which moved code behaves the same. Known gaps: no places with projections, borrows, storage markers, `catch`, search-phase unwinding, generics, debug information or code generation; capabilities are lists, not sets; the ABI is one program-wide Boolean function of a capability list (no dependence on argument types or on the call, no implication between capabilities); the caller-location value is a bare span. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

The theorems relate programs of the toy language to each other: an original program `p` and the program `inline p f b cfg` produced by the toy inliner, both run by the same reference semantics `run`. No compiler is executed, and the toy does not mirror any compiler's data structures.

### Lean environment and subjects

Lean `v4.34.1` (`lean/lean-toolchain`), core Lean and its standard library, with no Mathlib and no Lake dependencies (`lean/lakefile.toml` declares the single library `ToyInline`). `REPORT.json` lists the Lean toolchain release, which performs every kernel check; the pinned upstream revisions of rust-lang/rust, rust-lang/reference, rust-lang/rfcs, AbsInt/CompCert, llvm/llvm-project and CakeML/cakeml, whose source and documentation the modeling bridge and the prior-art notes quote; and the papers cited as prior art. These are statements about the toy model; they neither establish nor refute the corresponding claims about those systems, which appear in prose comparisons and are not related to the toy by any proved theorem.

### Definitions

#### 1.1 Syntax (`lean/ToyInline/Syntax.lean`)

```lean
-- lean/ToyInline/Syntax.lean:16
abbrev Local := Nat
-- lean/ToyInline/Syntax.lean:17
abbrev BlockId := Nat
-- lean/ToyInline/Syntax.lean:18
abbrev FnId := Nat
-- lean/ToyInline/Syntax.lean:19
abbrev Cap := Nat
-- lean/ToyInline/Syntax.lean:20
abbrev Span := Nat
-- lean/ToyInline/Syntax.lean:21
abbrev ScopeId := Nat
-- lean/ToyInline/Syntax.lean:26
abbrev CapSet := List Cap
-- lean/ToyInline/Syntax.lean:29-32
def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n
```
```lean
-- lean/ToyInline/Syntax.lean:35-38
inductive Operand
  | const (n : Nat)
  | var (x : Local)
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:41-44
inductive Rvalue
  | use (o : Operand)
  | add (a b : Operand)
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:52-57
inductive Stmt
  | assign (x : Local) (rv : Rvalue)
  | emit (o : Operand)
  | needCap (c : Cap)
  | loc (sp : Span) (sc : ScopeId)
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:61-65
inductive Unwind
  | cleanup (b : BlockId)
  | «continue»
  | terminate
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:70-79
structure CallInfo where
  callee : FnId
  args : List Operand
  dest : Local
  target : Option BlockId
  unwind : Unwind
  span : Span
  scope : ScopeId
  abiSensitive : Bool
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:84-93
inductive Term
  | goto (b : BlockId)
  | branch (o : Operand) (ifZero ifNonZero : BlockId)
  | call (ci : CallInfo)
  | ret
  | resume
  | panic (u : Unwind)
  | unreachable
  | abort
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:96-100
structure Block where
  stmts : List Stmt
  term : Term
  isCleanup : Bool
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:105-108
structure Scope where
  inlined : Option (FnId × Span)
  inlinedParent : Option ScopeId
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:112-118
structure Fn where
  nlocals : Nat
  caps : CapSet
  trackCaller : Bool
  blocks : List Block
  scopes : List Scope
  deriving DecidableEq, Repr
-- lean/ToyInline/Syntax.lean:124-126
structure Program where
  fns : List Fn
  abi : CapSet → Bool
-- lean/ToyInline/Syntax.lean:129-132
def Program.tracked (p : Program) (g : FnId) : Bool :=
  match nth? p.fns g with
  | some G => G.trackCaller
  | none => false
```
```lean
-- lean/ToyInline/Syntax.lean:136-138
def Operand.locals : Operand → List Local
  | .const _ => []
  | .var x => [x]
-- lean/ToyInline/Syntax.lean:140-142
def Rvalue.locals : Rvalue → List Local
  | .use o => o.locals
  | .add a b => a.locals ++ b.locals
-- lean/ToyInline/Syntax.lean:144-148
def Stmt.locals : Stmt → List Local
  | .assign x rv => x :: rv.locals
  | .emit o => o.locals
  | .needCap _ => []
  | .loc _ _ => []
-- lean/ToyInline/Syntax.lean:151-155
def Term.locals : Term → List Local
  | .branch o _ _ => o.locals
  | .call ci => ci.dest :: ci.args.flatMap Operand.locals
  | .ret => [0]
  | _ => []
-- lean/ToyInline/Syntax.lean:157-158
def Block.locals (B : Block) : List Local :=
  B.stmts.flatMap Stmt.locals ++ B.term.locals
-- lean/ToyInline/Syntax.lean:162-164
def Unwind.blocks : Unwind → List BlockId
  | .cleanup b => [b]
  | _ => []
-- lean/ToyInline/Syntax.lean:167-172
def Term.succs : Term → List BlockId
  | .goto b => [b]
  | .branch _ z nz => [z, nz]
  | .call ci => (match ci.target with | some t => [t] | none => []) ++ ci.unwind.blocks
  | .panic u => u.blocks
  | _ => []
-- lean/ToyInline/Syntax.lean:174-176
def Stmt.scopes : Stmt → List ScopeId
  | .loc _ sc => [sc]
  | _ => []
-- lean/ToyInline/Syntax.lean:178-180
def Term.scopes : Term → List ScopeId
  | .call ci => [ci.scope]
  | _ => []
-- lean/ToyInline/Syntax.lean:182-183
def Block.scopeRefs (B : Block) : List ScopeId :=
  B.stmts.flatMap Stmt.scopes ++ B.term.scopes
-- lean/ToyInline/Syntax.lean:186-188
def Term.abiSensitive : Term → Bool
  | .call ci => ci.abiSensitive
  | _ => false
```

* Local `0` is the return place, locals `1..k` receive the arguments. Block `0` is the entry; scope `0` is the outermost scope.
* `emit o` produces the observable event `out v`; drop events are `emit`s in cleanup blocks. `isCleanup` is metadata the semantics does not consult.
* `needCap c` is legal if the enclosing function's capability list contains `c`; executing it in a function whose list does not contain `c` ends the run with outcome `capFault`.
* `panic u` models a call to a panicking function with unwind action `u`; `branch o z nz` tests `o = 0`.
* Values are unbounded natural numbers: `Rvalue.add` is `Nat` addition (no wrapping).

#### 1.2 Reference semantics (`lean/ToyInline/Semantics.lean`)

A frame stack. A call pushes a callee frame whose store binds the arguments (`bindArgs`: local `i + 1` holds argument `i`, a missing argument reads as `0`, all other locals `0`); `ret` pops and writes the return value into the caller's destination, continuing at the call's target (undefined behaviour if there is none); a panic with `cleanup b` continues in block `b` of the same frame, with `continue` pops the frame and lets the caller's call decide (`unwindInto`), with `terminate` aborts; `resume` pops and lets the caller's call decide. Each frame therefore runs its own cleanup before its caller's.

```lean
-- lean/ToyInline/Semantics.lean:25-28
inductive WalkRes
  | stop (sp : Span)
  | top (sp : Span)
  deriving DecidableEq, Repr
-- lean/ToyInline/Semantics.lean:33-49
def walk (tr : FnId → Bool) (scopes : List Scope) : Nat → ScopeId → Span → WalkRes
  | 0, _, sp => .top sp
  | fuel + 1, s, sp =>
    match nth? scopes s with
    | none => .top sp
    | some sc =>
      match sc.inlined with
      | some (g, csp) =>
        if tr g then
          (match sc.inlinedParent with
           | none => .top csp
           | some t => walk tr scopes fuel t csp)
        else .stop sp
      | none =>
        match sc.inlinedParent with
        | none => .top sp
        | some t => walk tr scopes fuel t sp
-- lean/ToyInline/Semantics.lean:54-58
def locValue (tr : FnId → Bool) (scopes : List Scope) (s : ScopeId) (sp : Span)
    (il : Option Span) : Span :=
  match walk tr scopes scopes.length s sp with
  | .stop sp' => sp'
  | .top sp' => il.getD sp'
-- lean/ToyInline/Semantics.lean:64-75
def firstInlined (scopes : List Scope) : Nat → ScopeId → Option (FnId × Span)
  | 0, _ => none
  | fuel + 1, s =>
    match nth? scopes s with
    | none => none
    | some sc =>
      match sc.inlined with
      | some x => some x
      | none =>
        match sc.inlinedParent with
        | none => none
        | some t => firstInlined scopes fuel t
-- lean/ToyInline/Semantics.lean:78-89
def lastInlinedSpan (scopes : List Scope) : Nat → ScopeId → Option Span → Option Span
  | 0, _, acc => acc
  | fuel + 1, s, acc =>
    match nth? scopes s with
    | none => acc
    | some sc =>
      let acc' := match sc.inlined with
        | some (_, csp) => some csp
        | none => acc
      match sc.inlinedParent with
      | none => acc'
      | some t => lastInlinedSpan scopes fuel t acc'
-- lean/ToyInline/Semantics.lean:95-99
inductive LocPolicy
  | walk
  | innermost
  | outermost
  deriving DecidableEq, Repr
-- lean/ToyInline/Semantics.lean:101-113
def locValueWith (pol : LocPolicy) (tr : FnId → Bool) (scopes : List Scope) (s : ScopeId)
    (sp : Span) (il : Option Span) : Span :=
  match pol with
  | .walk => locValue tr scopes s sp il
  | .innermost =>
    match firstInlined scopes scopes.length s with
    | none => il.getD sp
    | some (g, csp) => if tr g then csp else sp
  | .outermost =>
    match firstInlined scopes scopes.length s with
    | none => il.getD sp
    | some (g, csp) =>
      if tr g then (lastInlinedSpan scopes scopes.length s none).getD csp else sp
```
```lean
-- lean/ToyInline/Semantics.lean:118-121
inductive Event
  | out (v : Nat)
  | loc (sp : Span)
  deriving DecidableEq, Repr
-- lean/ToyInline/Semantics.lean:126-132
inductive Outcome
  | returned (v : Nat)
  | unwound
  | aborted
  | ub
  | capFault
  deriving DecidableEq, Repr
-- lean/ToyInline/Semantics.lean:136-141
structure Frame where
  fn : FnId
  block : BlockId
  pc : Nat
  store : Local → Nat
  il : Option Span
-- lean/ToyInline/Semantics.lean:143-145
inductive Config
  | running (stack : List Frame)
  | halted (o : Outcome)
-- lean/ToyInline/Semantics.lean:147-149
def evalOp (st : Local → Nat) : Operand → Nat
  | .const n => n
  | .var x => st x
-- lean/ToyInline/Semantics.lean:151-153
def evalRv (st : Local → Nat) : Rvalue → Nat
  | .use o => evalOp st o
  | .add a b => evalOp st a + evalOp st b
-- lean/ToyInline/Semantics.lean:155-156
def upd (st : Local → Nat) (x : Local) (v : Nat) : Local → Nat :=
  fun y => if y = x then v else st y
-- lean/ToyInline/Semantics.lean:160-162
def bindArgs (vals : List Nat) : Local → Nat
  | 0 => 0
  | i + 1 => (nth? vals i).getD 0
-- lean/ToyInline/Semantics.lean:165-171
def curTerm (p : Program) (fr : Frame) : Option Term :=
  match nth? p.fns fr.fn with
  | none => none
  | some F =>
    match nth? F.blocks fr.block with
    | none => none
    | some B => if fr.pc = B.stmts.length then some B.term else none
-- lean/ToyInline/Semantics.lean:175-184
def unwindInto (p : Program) : List Frame → Config
  | [] => .halted .unwound
  | c :: rest =>
    match curTerm p c with
    | some (.call ci) =>
      match ci.unwind with
      | .cleanup b => .running ({ c with block := b, pc := 0 } :: rest)
      | .continue => unwindInto p rest
      | .terminate => .halted .aborted
    | _ => .halted .ub
-- lean/ToyInline/Semantics.lean:187-190
def startUnwind (p : Program) (fr : Frame) (rest : List Frame) : Unwind → Config
  | .cleanup b => .running ({ fr with block := b, pc := 0 } :: rest)
  | .continue => unwindInto p rest
  | .terminate => .halted .aborted
-- lean/ToyInline/Semantics.lean:193-201
def returnInto (p : Program) (v : Nat) : List Frame → Config
  | [] => .halted (.returned v)
  | c :: rest =>
    match curTerm p c with
    | some (.call ci) =>
      match ci.target with
      | some t => .running ({ c with block := t, pc := 0, store := upd c.store ci.dest v } :: rest)
      | none => .halted .ub
    | _ => .halted .ub
```
```lean
-- lean/ToyInline/Semantics.lean:206-246
def step (pol : LocPolicy) (p : Program) : List Frame → Config × List Event
  | [] => (.halted .ub, [])
  | fr :: rest =>
    match nth? p.fns fr.fn with
    | none => (.halted .ub, [])
    | some F =>
    match nth? F.blocks fr.block with
    | none => (.halted .ub, [])
    | some B =>
    match nth? B.stmts fr.pc with
    | some s =>
      let fr' := { fr with pc := fr.pc + 1 }
      match s with
      | .assign x rv =>
        (.running ({ fr' with store := upd fr.store x (evalRv fr.store rv) } :: rest), [])
      | .emit o => (.running (fr' :: rest), [.out (evalOp fr.store o)])
      | .needCap c =>
        if F.caps.contains c then (.running (fr' :: rest), []) else (.halted .capFault, [])
      | .loc sp sc =>
        (.running (fr' :: rest), [.loc (locValueWith pol p.tracked F.scopes sc sp fr.il)])
    | none =>
      match B.term with
      | .goto b => (.running ({ fr with block := b, pc := 0 } :: rest), [])
      | .branch o z nz =>
        (.running ({ fr with block := if evalOp fr.store o = 0 then z else nz, pc := 0 } :: rest), [])
      | .call ci =>
        match nth? p.fns ci.callee with
        | none => (.halted .ub, [])
        | some G =>
          let vals0 := ci.args.map (evalOp fr.store)
          let vals := if ci.abiSensitive && (p.abi F.caps != p.abi G.caps)
            then vals0.map (· + 1) else vals0
          let il' := if G.trackCaller
            then some (locValueWith pol p.tracked F.scopes ci.scope ci.span fr.il) else none
          (.running ({ fn := ci.callee, block := 0, pc := 0, store := bindArgs vals, il := il' }
            :: { fr with pc := B.stmts.length } :: rest), [])
      | .ret => (returnInto p (fr.store 0) rest, [])
      | .resume => (unwindInto p rest, [])
      | .panic u => (startUnwind p fr rest u, [])
      | .unreachable => (.halted .ub, [])
      | .abort => (.halted .aborted, [])
```
```lean
-- lean/ToyInline/Semantics.lean:249-252
structure Obs where
  events : List Event
  outcome : Option Outcome
  deriving DecidableEq, Repr
-- lean/ToyInline/Semantics.lean:255-261
def runWith (pol : LocPolicy) (p : Program) : Nat → Config → Obs
  | _, .halted o => ⟨[], some o⟩
  | 0, .running _ => ⟨[], none⟩
  | n + 1, .running s =>
    let r := step pol p s
    let o := runWith pol p n r.1
    ⟨r.2 ++ o.events, o.outcome⟩
-- lean/ToyInline/Semantics.lean:265-269
structure Entry where
  fn : FnId
  args : List Nat
  loc : Span
  deriving DecidableEq, Repr
-- lean/ToyInline/Semantics.lean:271-276
def init (p : Program) (e : Entry) : Config :=
  match nth? p.fns e.fn with
  | none => .halted .ub
  | some F =>
    .running [{ fn := e.fn, block := 0, pc := 0, store := bindArgs e.args,
                il := if F.trackCaller then some e.loc else none }]
-- lean/ToyInline/Semantics.lean:280-281
def Obs.Prefix (o₁ o₂ : Obs) : Prop :=
  o₁.events <+: o₂.events ∧ (o₁.outcome.isSome → o₂ = o₁)
-- lean/ToyInline/Semantics.lean:287-289
def BehEquivAtWith (pol : LocPolicy) (p q : Program) (e : Entry) : Prop :=
  (∀ n, ∃ m, (runWith pol p n (init p e)).Prefix (runWith pol q m (init q e))) ∧
  (∀ m, ∃ n, (runWith pol q m (init q e)).Prefix (runWith pol p n (init p e)))
-- lean/ToyInline/Semantics.lean:292
abbrev run (p : Program) (n : Nat) (c : Config) : Obs := runWith .walk p n c
-- lean/ToyInline/Semantics.lean:294
abbrev BehEquivAt (p q : Program) (e : Entry) : Prop := BehEquivAtWith .walk p q e
-- lean/ToyInline/Semantics.lean:298
def BehEquiv (p q : Program) : Prop := ∀ e, BehEquivAt p q e
```

* Implicit caller locations: a `trackCaller` frame carries `il = some l`. A call to a tracked callee passes `locValue` of the call's scope and span in the caller's frame; for a body without inlined scopes this is the caller's own implicit location if the caller is tracked, and the call's span otherwise.
* ABI: an ABI-sensitive call from host `F` to callee `G` garbles every argument value `v` to `v + 1` when `p.abi F.caps ≠ p.abi G.caps`. `p.abi` is one function of the whole capability list.
* `BehEquivAt p q e`: every finite observation (`run` for `n` steps) of either program from entry `e` is a prefix of some observation of the other; a halted observation is a prefix of itself and of no other observation. Step counts are ignored. Because the semantics is deterministic this says the maximal observations coincide, *including* the outcomes `ub`, `capFault` and `aborted` and values changed by ABI garbling: it is the strongest notion of semantic preservation (Leroy 2009, Section 2.1, Definition 1, "Bisimulation"), not a refinement that allows a transformed program to differ where the source goes wrong. Several tightness witnesses under Findings have a source run that ends in `ub` or `capFault` or passes a garbled argument; the cards say so.

Unfolded (prose): `BehEquiv p q` means: for every entry `e` (function, argument values, implicit location), for every `n` there is an `m` such that `run p n (init p e)` is a prefix of `run q m (init q e)`, and vice versa.

```lean
-- lean/ToyInline/RunLemmas.lean:13-14
theorem runWith_halted (pol : LocPolicy) (p : Program) (n : Nat) (o : Outcome) :
    runWith pol p n (.halted o) = ⟨[], some o⟩ := …
-- lean/ToyInline/RunLemmas.lean:17
theorem Obs.Prefix.refl (o : Obs) : o.Prefix o := …
-- lean/ToyInline/RunLemmas.lean:19
theorem Obs.Prefix.trans {a b c : Obs} (h1 : a.Prefix b) (h2 : b.Prefix c) : a.Prefix c := …
-- lean/ToyInline/RunLemmas.lean:26-27
theorem runWith_mono (pol : LocPolicy) (p : Program) :
    ∀ (n m : Nat) (c : Config), n ≤ m → (runWith pol p n c).Prefix (runWith pol p m c) := …
-- lean/ToyInline/RunLemmas.lean:53-55
theorem runWith_prefix_of_halted {pol : LocPolicy} {p : Program} {n : Nat} {c : Config}
    (hn : (runWith pol p n c).outcome.isSome) (n' : Nat) :
    (runWith pol p n' c).Prefix (runWith pol p n c) := …
-- lean/ToyInline/RunLemmas.lean:63-65
theorem runWith_halted_unique {pol : LocPolicy} {p : Program} {n m : Nat} {c : Config}
    (hn : (runWith pol p n c).outcome.isSome) (hm : (runWith pol p m c).outcome.isSome) :
    runWith pol p n c = runWith pol p m c := …
-- lean/ToyInline/RunLemmas.lean:71-74
theorem behEquivAtWith_of_halted_eq {pol : LocPolicy} {p q : Program} {e : Entry} {n m : Nat}
    (hh : (runWith pol p n (init p e)).outcome.isSome)
    (heq : runWith pol p n (init p e) = runWith pol q m (init q e)) :
    BehEquivAtWith pol p q e := …
-- lean/ToyInline/RunLemmas.lean:81-86
theorem not_behEquivAtWith_of_halted_ne {pol : LocPolicy} {p q : Program} {e : Entry}
    {n m : Nat}
    (hp : (runWith pol p n (init p e)).outcome.isSome)
    (hq : (runWith pol q m (init q e)).outcome.isSome)
    (hne : runWith pol p n (init p e) ≠ runWith pol q m (init q e)) :
    ¬ BehEquivAtWith pol p q e := …
-- lean/ToyInline/RunLemmas.lean:94-95
theorem behEquivAtWith_refl (pol : LocPolicy) (p : Program) (e : Entry) :
    BehEquivAtWith pol p p e := …
-- lean/ToyInline/RunLemmas.lean:98-99
theorem behEquivAtWith_symm {pol : LocPolicy} {p q : Program} {e : Entry}
    (h : BehEquivAtWith pol p q e) : BehEquivAtWith pol q p e := …
```
#### 1.3 The inliner (`lean/ToyInline/Inline.lean`)

```lean
-- lean/ToyInline/Inline.lean:23-26
inductive RetMode
  | temp (t : Local)
  | dest
  deriving DecidableEq, Repr
-- lean/ToyInline/Inline.lean:31-34
inductive LinkRule
  | rustc
  | ignoreParent
  deriving DecidableEq, Repr
-- lean/ToyInline/Inline.lean:38-41
inductive ResumeMap
  | unwind
  | normal
  deriving DecidableEq, Repr
-- lean/ToyInline/Inline.lean:44-49
structure InlineCfg where
  slot : Nat → Local
  ret : RetMode
  redirectContinue : Bool
  resumeMap : ResumeMap
  link : LinkRule
-- lean/ToyInline/Inline.lean:53-54
def InlineCfg.rename (cfg : InlineCfg) (dest : Local) (i : Nat) : Local :=
  if i = 0 then (match cfg.ret with | .temp t => t | .dest => dest) else cfg.slot i
-- lean/ToyInline/Inline.lean:58-63
def InlineCfg.canonical (hostN : Nat) : InlineCfg where
  slot i := hostN + i
  ret := .temp hostN
  redirectContinue := true
  resumeMap := .unwind
  link := .rustc
-- lean/ToyInline/Inline.lean:66
def InlineCfg.withDest (cfg : InlineCfg) : InlineCfg := { cfg with ret := .dest }
```
```lean
-- lean/ToyInline/Inline.lean:68-70
def Operand.rename (ρ : Nat → Local) : Operand → Operand
  | .const n => .const n
  | .var x => .var (ρ x)
-- lean/ToyInline/Inline.lean:72-74
def Rvalue.rename (ρ : Nat → Local) : Rvalue → Rvalue
  | .use o => .use (o.rename ρ)
  | .add a b => .add (a.rename ρ) (b.rename ρ)
-- lean/ToyInline/Inline.lean:77-81
def Stmt.rename (ρ : Nat → Local) (ns : Nat) : Stmt → Stmt
  | .assign x rv => .assign (ρ x) (rv.rename ρ)
  | .emit o => .emit (o.rename ρ)
  | .needCap c => .needCap c
  | .loc sp sc => .loc sp (sc + ns)
-- lean/ToyInline/Inline.lean:84-91
structure SpliceCtx where
  ρ : Nat → Local
  base : Nat
  ns : Nat
  retBlk : Option BlockId
  callUnwind : Unwind
  redirectContinue : Bool
  resumeMap : ResumeMap
-- lean/ToyInline/Inline.lean:95-98
def SpliceCtx.mapUnwind (c : SpliceCtx) : Unwind → Unwind
  | .cleanup b => .cleanup (b + c.base)
  | .continue => if c.redirectContinue then c.callUnwind else .continue
  | .terminate => .terminate
-- lean/ToyInline/Inline.lean:102-124
def SpliceCtx.term (c : SpliceCtx) : Term → Term
  | .goto b => .goto (b + c.base)
  | .branch o z nz => .branch (o.rename c.ρ) (z + c.base) (nz + c.base)
  | .call ci => .call { ci with
      args := ci.args.map (Operand.rename c.ρ),
      dest := c.ρ ci.dest,
      target := ci.target.map (· + c.base),
      unwind := c.mapUnwind ci.unwind,
      scope := ci.scope + c.ns }
  | .ret => match c.retBlk with
    | some r => .goto r
    | none => .unreachable
  | .resume => match c.resumeMap with
    | .unwind => match c.callUnwind with
      | .cleanup b => .goto b
      | .continue => .resume
      | .terminate => .abort
    | .normal => match c.retBlk with
      | some r => .goto r
      | none => .unreachable
  | .panic u => .panic (c.mapUnwind u)
  | .unreachable => .unreachable
  | .abort => .abort
-- lean/ToyInline/Inline.lean:126-129
def SpliceCtx.block (c : SpliceCtx) (B : Block) : Block where
  stmts := B.stmts.map (Stmt.rename c.ρ c.ns)
  term := c.term B.term
  isCleanup := B.isCleanup
```
```lean
-- lean/ToyInline/Inline.lean:132-133
def argOr (args : List Operand) (i : Nat) : Operand :=
  (nth? args (i - 1)).getD (.const 0)
-- lean/ToyInline/Inline.lean:138-140
def prologue (ρ : Nat → Local) (args : List Operand) (n : Nat) : List Stmt :=
  (List.range n).tail.map (fun i => .assign (ρ i) (.use (argOr args i))) ++
    (if n = 0 then [] else [.assign (ρ 0) (.use (.const 0))])
-- lean/ToyInline/Inline.lean:143-146
def retStmts (cfg : InlineCfg) (ci : CallInfo) : List Stmt :=
  match cfg.ret with
  | .temp t => [.assign ci.dest (.use (.var t))]
  | .dest => []
-- lean/ToyInline/Inline.lean:149-150
def maxSucc (ρ : Nat → Local) (n : Nat) : Nat :=
  (List.range n).foldl (fun m i => max m (ρ i + 1)) 0
-- lean/ToyInline/Inline.lean:154-157
def retTempSucc (cfg : InlineCfg) : Nat :=
  match cfg.ret with
  | .temp t => t + 1
  | .dest => 0
-- lean/ToyInline/Inline.lean:159-161
def mapIdxFrom {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | i, a :: as => f i a :: mapIdxFrom f (i + 1) as
-- lean/ToyInline/Inline.lean:167-183
def linkScope (link : LinkRule) (csScope : ScopeId) (cs : Option Scope) (callee : FnId)
    (span : Span) (ns : Nat) (j : Nat) (sc : Scope) : Scope :=
  if j = 0 then
    { inlined := some (callee, span),
      inlinedParent :=
        match cs with
        | some c =>
          if c.inlined.isSome then some csScope
          else (match link with
                | .rustc => c.inlinedParent
                | .ignoreParent => none)
        | none => none }
  else
    { inlined := sc.inlined,
      inlinedParent := match sc.inlinedParent with
        | none => some ns
        | some t => some (t + ns) }
-- lean/ToyInline/Inline.lean:186-188
def linkScopes (link : LinkRule) (F : Fn) (ci : CallInfo) (G : Fn) : List Scope :=
  mapIdxFrom (linkScope link ci.scope (nth? F.scopes ci.scope) ci.callee ci.span
    F.scopes.length) 0 G.scopes
```
```lean
-- lean/ToyInline/Inline.lean:193-213
def inlineFn (F : Fn) (b : BlockId) (B : Block) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) :
    Fn :=
  let nb := F.blocks.length
  let ρ := cfg.rename ci.dest
  let base := nb + (match ci.target with | some _ => 1 | none => 0)
  let ctx : SpliceCtx :=
    { ρ := ρ, base := base, ns := F.scopes.length, retBlk := ci.target.map (fun _ => nb),
      callUnwind := ci.unwind, redirectContinue := cfg.redirectContinue,
      resumeMap := cfg.resumeMap }
  let callBlk : Block :=
    { stmts := B.stmts ++ prologue ρ ci.args G.nlocals, term := .goto base,
      isCleanup := B.isCleanup }
  let rb : List Block := match ci.target with
    | some t => [{ stmts := retStmts cfg ci, term := .goto t,
                   isCleanup := ((nth? F.blocks t).map Block.isCleanup).getD false }]
    | none => []
  { nlocals := max (max F.nlocals (maxSucc ρ G.nlocals)) (retTempSucc cfg),
    caps := F.caps,
    trackCaller := F.trackCaller,
    blocks := F.blocks.set b callBlk ++ rb ++ G.blocks.map ctx.block,
    scopes := F.scopes ++ linkScopes cfg.link F ci G }
-- lean/ToyInline/Inline.lean:217-229
def inline (p : Program) (f b : Nat) (cfg : InlineCfg) : Program :=
  match nth? p.fns f with
  | none => p
  | some F =>
    match nth? F.blocks b with
    | none => p
    | some B =>
      match B.term with
      | .call ci =>
        match nth? p.fns ci.callee with
        | none => p
        | some G => { p with fns := p.fns.set f (inlineFn F b B ci G cfg) }
      | _ => p
-- lean/ToyInline/Inline.lean:232-235
def hostNLocals (p : Program) (f : FnId) : Nat :=
  match nth? p.fns f with
  | some F => F.nlocals
  | none => 0
-- lean/ToyInline/Inline.lean:238-239
def inlineCanon (p : Program) (f b : Nat) : Program :=
  inline p f b (InlineCfg.canonical (hostNLocals p f))
```

* Layout follows the rustc MIR inliner: old blocks (the call block now ends with the prologue and a jump to the callee's entry), then one return block if the call had a target, then the shifted callee blocks; callee scopes are appended and linked.
* `argOr args i` reads argument `i - 1` with truncated subtraction; the prologue calls it for `1 ≤ i < G.nlocals` only, so the truncation at `i = 0` is never used. A missing argument becomes the constant `0`; extra arguments are ignored.
* The declared-local count of the new body is `max (max F.nlocals (maxSucc (cfg.rename ci.dest) G.nlocals)) (retTempSucc cfg)`; the last term covers the return temporary, which the return block reads even when the callee declares no locals (`inlineFn_nlocals_covers_retTemp`).
* `cfg.redirectContinue = false`, `cfg.resumeMap = .normal` and `cfg.link = .ignoreParent` are deliberately wrong variants used by counterexamples.

#### 1.4 Hypotheses and observation properties (`lean/ToyInline/Props.lean`)

```lean
-- lean/ToyInline/Props.lean:17-19
def IsCallSite (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) : Prop :=
  nth? p.fns f = some F ∧ (nth? F.blocks b).map Block.term = some (.call ci) ∧
    nth? p.fns ci.callee = some G
-- lean/ToyInline/Props.lean:29
def LocalsBounded (F : Fn) : Prop := ∀ B ∈ F.blocks, ∀ x ∈ B.locals, x < F.nlocals
-- lean/ToyInline/Props.lean:32
def BlocksBounded (F : Fn) : Prop := ∀ B ∈ F.blocks, ∀ t ∈ B.term.succs, t < F.blocks.length
-- lean/ToyInline/Props.lean:35-38
def Scope.parentBelow (sc : Scope) (i : Nat) : Bool :=
  match sc.inlinedParent with
  | none => true
  | some t => decide (t < i)
-- lean/ToyInline/Props.lean:43-44
def ScopeParentsBelow (scopes : List Scope) : Prop :=
  ∀ i, i < scopes.length → (nth? scopes i).all (·.parentBelow i) = true
-- lean/ToyInline/Props.lean:49-50
def ScopeTreeWF (scopes : List Scope) : Prop :=
  nth? scopes 0 = some ⟨none, none⟩ ∧ ScopeParentsBelow scopes
-- lean/ToyInline/Props.lean:53
def ScopeRefsBounded (F : Fn) : Prop := ∀ B ∈ F.blocks, ∀ s ∈ B.scopeRefs, s < F.scopes.length
-- lean/ToyInline/Props.lean:56
def ScopesWF (F : Fn) : Prop := ScopeTreeWF F.scopes ∧ ScopeRefsBounded F
```
```lean
-- lean/ToyInline/Props.lean:62-63
def SlotsFresh (cfg : InlineCfg) (F G : Fn) : Prop :=
  ∀ i, i < G.nlocals → 1 ≤ i → F.nlocals ≤ cfg.slot i
-- lean/ToyInline/Props.lean:66-67
def SlotsInjective (cfg : InlineCfg) (G : Fn) : Prop :=
  ∀ i, i < G.nlocals → ∀ j, j < G.nlocals → 1 ≤ i → 1 ≤ j → cfg.slot i = cfg.slot j → i = j
-- lean/ToyInline/Props.lean:70-71
def TempFresh (t : Local) (cfg : InlineCfg) (F G : Fn) : Prop :=
  F.nlocals ≤ t ∧ ∀ i, i < G.nlocals → 1 ≤ i → cfg.slot i ≠ t
-- lean/ToyInline/Props.lean:76
def cleanupAt (F : Fn) (t : BlockId) : Bool := ((nth? F.blocks t).map Block.isCleanup).getD false
-- lean/ToyInline/Props.lean:79-82
def Term.unwindTargets : Term → List BlockId
  | .call ci => ci.unwind.blocks
  | .panic u => u.blocks
  | _ => []
-- lean/ToyInline/Props.lean:86-88
def CleanupClosed (F : Fn) : Prop :=
  ∀ B ∈ F.blocks, (∀ c ∈ B.term.unwindTargets, cleanupAt F c = true) ∧
    (B.isCleanup = true → ∀ t ∈ B.term.succs, cleanupAt F t = true)
-- lean/ToyInline/Props.lean:90-93
def Stmt.reads : Stmt → List Local
  | .assign _ rv => rv.locals
  | .emit o => o.locals
  | _ => []
-- lean/ToyInline/Props.lean:95-99
def Term.reads : Term → List Local
  | .branch o _ _ => o.locals
  | .call ci => ci.args.flatMap Operand.locals
  | .ret => [0]
  | _ => []
-- lean/ToyInline/Props.lean:101
def Block.reads (B : Block) : List Local := B.stmts.flatMap Stmt.reads ++ B.term.reads
-- lean/ToyInline/Props.lean:104-105
def DestNotReadInCleanup (F : Fn) (d : Local) : Prop :=
  ∀ B ∈ F.blocks, B.isCleanup = true → d ∉ B.reads
```
```lean
-- lean/ToyInline/Props.lean:110
def CapsSubset (G F : Fn) : Prop := ∀ c ∈ G.caps, c ∈ F.caps
-- lean/ToyInline/Props.lean:112-114
def Stmt.capOk (caps : CapSet) : Stmt → Bool
  | .needCap c => caps.contains c
  | _ => true
-- lean/ToyInline/Props.lean:117
def CapLegal (G : Fn) : Prop := ∀ B ∈ G.blocks, ∀ s ∈ B.stmts, s.capOk G.caps = true
-- lean/ToyInline/Props.lean:120
def AbiInsensitive (G : Fn) : Prop := ∀ B ∈ G.blocks, B.term.abiSensitive = false
-- lean/ToyInline/Props.lean:124
def AbiAgree (p : Program) (F G : Fn) : Prop := p.abi F.caps = p.abi G.caps
```
```lean
-- lean/ToyInline/Props.lean:132-136
def stmtStore (st : Local → Nat) : Stmt → (Local → Nat) × List Nat
  | .assign x rv => (upd st x (evalRv st rv), [])
  | .emit o => (st, [evalOp st o])
  | .needCap _ => (st, [])
  | .loc _ _ => (st, [])
-- lean/ToyInline/Props.lean:141-148
theorem step_storeStmt (pol : LocPolicy) (p : Program) (fr : Frame) (rest : List Frame)
    (F : Fn) (B : Block) (s : Stmt)
    (hF : nth? p.fns fr.fn = some F) (hB : nth? F.blocks fr.block = some B)
    (hs : nth? B.stmts fr.pc = some s)
    (hst : (∃ x rv, s = .assign x rv) ∨ (∃ o, s = .emit o)) :
    step pol p (fr :: rest) =
      (.running ({ fr with pc := fr.pc + 1, store := (stmtStore fr.store s).1 } :: rest),
        (stmtStore fr.store s).2.map Event.out) := …
-- lean/ToyInline/Props.lean:153-154
def FrameRel (ρ : Nat → Local) (n : Nat) (L : List Local) (C G M : Local → Nat) : Prop :=
  (∀ x ∈ L, M x = C x) ∧ (∀ i, i < n → M (ρ i) = G i)
-- lean/ToyInline/Props.lean:157-158
def RenameInjectiveOn (ρ : Nat → Local) (n : Nat) : Prop :=
  ∀ i, i < n → ∀ j, j < n → ρ i = ρ j → i = j
-- lean/ToyInline/Props.lean:161-162
def RenameAvoids (ρ : Nat → Local) (n : Nat) (L : List Local) : Prop :=
  ∀ i, i < n → ρ i ∉ L
-- lean/ToyInline/Props.lean:165
def StmtLocalsLt (n : Nat) (s : Stmt) : Prop := ∀ x ∈ s.locals, x < n
```
```lean
-- lean/ToyInline/Props.lean:172-173
def TerminalHolds (P : Obs → Prop) (p : Program) (e : Entry) : Prop :=
  ∀ n, (run p n (init p e)).outcome.isSome → P (run p n (init p e))
-- lean/ToyInline/Props.lean:178-179
def SafetyHolds (S : Obs → Prop) (p : Program) (e : Entry) : Prop :=
  ∀ n, S (run p n (init p e))
-- lean/ToyInline/Props.lean:182
def PrefixClosed (S : Obs → Prop) : Prop := ∀ o o', o.Prefix o' → S o' → S o
-- lean/ToyInline/Props.lean:185
def NoPanic (o : Obs) : Prop := o.outcome ≠ some .unwound
-- lean/ToyInline/Props.lean:190-192
theorem terminalHolds_of_halted {P : Obs → Prop} {p : Program} {e : Entry} {n : Nat}
    (hh : (run p n (init p e)).outcome.isSome) (hP : P (run p n (init p e))) :
    TerminalHolds P p e := …
-- lean/ToyInline/Props.lean:198-200
theorem not_terminalHolds_of_halted {P : Obs → Prop} {p : Program} {e : Entry} {n : Nat}
    (hh : (run p n (init p e)).outcome.isSome) (hP : ¬ P (run p n (init p e))) :
    ¬ TerminalHolds P p e := …
```

* `ScopeParentsBelow` (every `inlinedParent` link of scope `i` points to some `t < i`) is stronger than acyclicity: `scopeParentsBelow_neg` is an acyclic table it rejects. `ScopeTreeWF` adds a clean scope `0`.
* `TerminalHolds P p e` holds vacuously when the run from `e` never halts. `SafetyHolds S p e` checks every step budget, including `n = 0`; it is a safety property in the usual sense when `S` is `PrefixClosed`, which the definition does not require.
* Each hypothesis has a proved positive and negative example in `lean/ToyInline/Examples.lean`, named after it with suffixes `_pos` and `_neg` (all listed under Findings, "Declarations cited by name").

## Findings

In every hypothesis ledger, *tight* means: a fully proved counterexample theorem (named) states that every other hypothesis holds and the conclusion fails; the class of that witness is recorded. A ledger entry marked *unknown* has no such witness here. Every card's statement block is a verbatim quote of the Lean source, labelled with its `file:line` range; proofs are elided (`:= …`).

### How the whole-program inlining theorems are proved

Basis: execution (Lean kernel check)

R2, R3, R8 and R9 are proved by one stuttering forward simulation in `lean/ToyInline/Simulation.lean`; each of the four theorems derives the simulation's side conditions from its own hypotheses. Write `q` for `inline p f b cfg` and `ρ` for `cfg.rename ci.dest` (callee local `0` goes to the temporary or to the destination, callee local `i ≥ 1` to `cfg.slot i`).

- **Stack relation.** The frame stack of `p` is paired with that of `q` segment by segment. A frame of a function other than `f` is paired with an identical frame. A frame of `f` is paired with a frame of `q` at the same block (a block of `F`, below `F.blocks.length`), statement index and implicit location, whose store agrees with it on the declared host locals `x < F.nlocals` (in destination mode, except at `ci.dest` while control is in a cleanup block of `F`). A callee frame of the inlined call together with the suspended frame of `f` below it (at block `b`, at its call terminator) is paired with one merged frame of `q`: its block is the callee's block shifted past the host blocks and the return block, its store agrees with the suspended caller store on the declared host locals (in destination mode, except possibly at `ci.dest`) and with the callee store through `ρ` on the callee locals below `G.nlocals`, and its implicit location is the caller's.
- **Step matching.** Every step of `p` is matched by at least one step of `q` with the same events: the inlined call by the argument-binding prologue (`prologue`) followed by the jump to the shifted callee entry; the callee's `ret` by the jump to the return block, the move of the temporary into `ci.dest` (temp mode; no statement in destination mode) and the jump to the call's target; every other step by exactly one step. This includes unwinding through `continue` chains (the redirected unwind action), the rewritten `resume`, calls made by the moved code (their callee frames are paired as above), and `loc` events and implicit locations passed by calls, which agree by the scope-walk facts stated as R11 and R12 (re-proved in that file, which `lean/ToyInline/Results.lean` imports).
- **From simulation to `BehEquiv`.** Both machines are deterministic and each step of `p` is matched by at least one step of `q`, so for every `n` the observation `run p n (init p e)` equals `run q m (init q e)` for some `m ≥ n`. This gives the first conjunct of `BehEquivAt p q e` directly and the second through `runWith_mono`, for every entry `e`.
- **Destination mode (R3).** The relation additionally lets the destination `ci.dest` differ between the two machines in two places. Inside the merged callee segment, the merged frame's store may differ from the suspended caller store at `ci.dest` (in destination mode `ρ 0 = ci.dest`, which the prologue zeroes when `G.nlocals ≥ 1` and the moved callee code writes directly). In a frame of `f` (for example after an unwind out of the inlined body), it may differ at `ci.dest` while control is in a cleanup block of `F`, and nowhere else: `CleanupClosed F` keeps control in cleanup blocks, and `DestNotReadInCleanup F ci.dest` ensures that none of them reads the destination. A normal return from the callee writes the destination on both sides.
- **Capability guards (R8, R9).** Under `CapsSubset G F` and `CapLegal G` every `needCap` of the moved code succeeds in the host exactly when it succeeds in the callee. `AbiInsensitive G` with `ci.abiSensitive = false` (R8), or `AbiAgree p F G` (R9), makes ABI garbling identical on both sides.

The proof uses no axiom beyond `propext` and `Quot.sound`. It does not use the clean-scope-`0` conjunct of `ScopesWF F` (`nth? F.scopes 0 = some ⟨none, none⟩`); no theorem with that conjunct dropped is stated in this package.

### R1. `frameRel_step_of_injective_of_avoids` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For a renaming `ρ` that is injective on callee locals below `n` (`RenameInjectiveOn ρ n`) and maps them outside the list `L` of caller locals live across the call (`RenameAvoids ρ n L`), a statement `s` mentioning only locals below `n` (`StmtLocalsLt n s`), and stores with `FrameRel ρ n L C G M` (the merged store `M` agrees with the caller store `C` on `L` and with the callee store `G` through `ρ` below `n`): executing `s` on `G` and its renaming `s.rename ρ ns` on `M` with the auxiliary store-level function `stmtStore` again yields stores related by `FrameRel ρ n L C`, and the two lists of emitted values are equal, for every scope shift `ns`. `stmtStore` updates the store for `assign`, emits a value for `emit`, and maps `needCap` and `loc` to `(st, [])`, so the statement says nothing about capability faults or `loc` events.

**Tier.** T0: CompCert mechanizes the corresponding register-agreement step of its inlining proof (`agree_set_reg`, backend/Inliningproof.v L141-153, for a shift of pseudo-registers); this re-derives it for the toy store and an arbitrary renaming that is injective and avoids the live caller locals.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:29-34
theorem frameRel_step_of_injective_of_avoids
    (ρ : Nat → Local) (n : Nat) (L : List Local) (C G M : Local → Nat) (s : Stmt) (ns : Nat)
    (hinj : RenameInjectiveOn ρ n) (havoid : RenameAvoids ρ n L)
    (hs : StmtLocalsLt n s) (hR : FrameRel ρ n L C G M) :
    FrameRel ρ n L C (stmtStore G s).1 (stmtStore M (s.rename ρ ns)).1 ∧
      (stmtStore M (s.rename ρ ns)).2 = (stmtStore G s).2 := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hinj : RenameInjectiveOn ρ n` | a write to one callee local must not change another callee local's image | tight: counterexample `cex_frame_injective` (all other hypotheses hold and the conclusion fails; witness class: callee locals 0 and 1 share host local 5 (`n = 2`, `L = []`)) |
| `havoid : RenameAvoids ρ n L` | a write to a callee local must not change a live caller local | tight: counterexample `cex_frame_avoids` (all other hypotheses hold and the conclusion fails; witness class: callee local 1 renamed onto live caller local 2) |
| `hs : StmtLocalsLt n s` | the relation covers every local the statement touches | tight: counterexample `cex_frame_stmtLocals` (all other hypotheses hold and the conclusion fails; witness class: a statement reading callee local 2 with `n = 2`) |
| `hR : FrameRel ρ n L C G M` | the invariant before the step | tight: counterexample `cex_frame_rel` (all other hypotheses hold and the conclusion fails; witness class: unrelated stores (`cst 1` and `cst 2`, `n = 1`)) |

**Depth.** shallow: Case analysis on the four statement forms; the `assign` case uses injectivity and avoidance.

**Non-vacuity witness.** `ρ = (· + 2)`, `n = 2`, `L = [1]`, statement `assign 0 (use (var 1))`, stores `cst 4`, `cst 7`, `upd (cst 7) 1 4`. (`nonvacuity_frameRel_step`)

**Non-claims.**

- Applies to the auxiliary store-level function `stmtStore`, which maps `needCap` and `loc` to `(st, [])`: it ignores capability faults and `loc` events, which `step` does produce. `step_storeStmt` relates `stmtStore` to `step` for `assign` and `emit` only; for `needCap` and `loc` no bridge to `step` is stated.
- Covers one statement step. The argument-binding prologue, the return block, terminators, unwinding and caller locations are not covered; whole-program behaviour is the subject of `inline_behEquiv_retTemp_of_capsEq` and its variants.
- `cex_frame_injective` shows failure when callee locals `0` and `1` map to the same host local. It does not show that a call whose destination is also one of its arguments (`x = f(x)`) breaks injectivity: under `SlotsFresh` and `LocalsBounded F` the inliner's renaming `InlineCfg.rename` maps the destination (below `F.nlocals`) and the callee slots (at or above `F.nlocals`) to different host locals, and under `TempFresh` the temporary differs from every slot (not proved here as a separate lemma).
- The store is a total map `Local → Nat`: no uninitialised values, no places with projections, no borrows and no aliasing through references.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- CompCert v3.18 (AbsInt/CompCert commit 14d616046360a0b2611ebdfc2f98368af402e1f7), backend/Inliningproof.v L98-153: `agree_regs F ctx rs rs'` (L98-100) relates source registers to their shifted images `sreg ctx r`, and `agree_set_reg` (L141-153) proves that setting a register and its image preserves this agreement — the Coq-mechanized register-renaming step of CompCert's inlining proof.
- CompCert v3.18 (AbsInt/CompCert commit 14d616046360a0b2611ebdfc2f98368af402e1f7), backend/Inlining.v L166-186 (`Record context`: a source instruction at PC `n` is relocated to `n + ctx.(dpc)`, pseudo-registers are shifted by `ctx.(dreg)`, and "return" instructions become "return" or "move" instructions as governed by `ctx.(retinfo)`) and backend/Inliningproof.v L1297-1305 (`Theorem transf_program_correct: forward_simulation (semantics prog) (semantics tprog).`). RTL has no unwinding, cleanup blocks, capability guards or caller-location scopes.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1193-1206 (`map_local`: the return place maps to `self.destination`, argument `i` to `self.args[i]`, other locals to a fresh range) and L1120-1146 (`create_temp_if_necessary`: "Reuse the operand if it is a moved temporary."; otherwise a fresh temporary is assigned the argument). Unlike the toy, rustc may use an existing caller temporary as a callee argument local instead of copying into a fresh slot.

**Design question.** Which renaming conditions make the merged frame track both original frames step by step?

### R2. `inline_behEquiv_retTemp_of_capsEq` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** At a call site `IsCallSite p f b F ci G` (function `f` of `p` is `F`, its block `b` ends in the call `ci`, whose callee is `G`), suppose: every local mentioned by `F` and by `G` is below its declared count (`LocalsBounded F`, `LocalsBounded G`); every jump target of `F` is one of its blocks (`BlocksBounded F`); `F` and `G` satisfy `ScopesWF` (scope `0` exists and carries neither `inlined` nor `inlinedParent`, every `inlinedParent` link of scope `i` points to an index `t < i`, and every scope named by a `loc` statement or call is in range); callee locals `1 ≤ i < G.nlocals` go to host slots at or above `F.nlocals` (`SlotsFresh`) that are pairwise distinct (`SlotsInjective`); the return place goes to a temporary `t` (`cfg.ret = .temp t`) with `F.nlocals ≤ t` and `t` different from every callee slot (`TempFresh`); `continue` edges are redirected, `resume` is rewritten by the call's unwind action and the `rustc` scope-link rule is used; and `F.caps = G.caps` (equal lists). Then `BehEquiv p (inline p f b cfg)`: from every entry, every finite observation of `run` of either program is a prefix of an observation of the other, so the maximal event sequences (including cleanup `out` events, in order, and `loc` events) and the outcomes (including `ub`, `capFault`, `aborted` and `unwound`) coincide.

**Tier.** T1: Correctness of call-site inlining is mechanized for CompCert's RTL (forward simulation, no unwinding or caller locations) and for CakeML's BVL (with exceptions, no CFG cleanup splicing); stated here for a toy MIR-like CFG language with per-frame cleanup, unwind actions, rustc's rewriting rules and the scope-link rule.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:74-84
theorem inline_behEquiv_retTemp_of_capsEq
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) (t : Local)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hcaps : F.caps = G.caps) :
    BehEquiv p (inline p f b cfg) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsite : IsCallSite p f b F ci G` | names the objects the other hypotheses talk about: function `f` of `p` is `F`, its block `b` ends in the call `ci`, and the callee of `ci` is `G`; without it the other hypotheses constrain unrelated bodies | tight: counterexample `cex_isCallSite` (all other hypotheses hold and the conclusion fails; witness class: a two-function program whose function 0 is `freshF`, checked against the mismatched `F := emptyF` (no locals, no blocks); temp-mode part) |
| `hlocF : LocalsBounded F` | every local mentioned by `F` (including the return place read by `ret`) is below `F.nlocals`, so slots at or above `F.nlocals` cannot clobber caller locals | tight: counterexample `cex_localsBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller declaring 1 local that keeps local 1 live across the call (slot 1 = local 1); temp-mode part) |
| `hlocG : LocalsBounded G` | every local mentioned by `G` is below `G.nlocals`, so the prologue binds or zeroes all of them | tight: counterexample `cex_localsBoundedG` (all other hypotheses hold and the conclusion fails; witness class: a callee declaring 1 local that reads local 1 (its argument), which the prologue does not bind; temp-mode part) |
| `hblkF : BlocksBounded F` | every jump target of `F` (goto, branch, call target, cleanup target) is one of `F`'s blocks; a missing block would become the return block or a callee block after inlining | tight: counterexample `cex_blocksBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller jumping to missing block 4: the original run ends in `ub`, the inlined run (block 4 is now a callee block) in `aborted`; the witness relies on `BehEquiv` distinguishing `ub` (see non-claims); temp-mode part) |
| `hscF : ScopesWF F` | `ScopesWF F` = `ScopeTreeWF F.scopes` (scope `0` exists and carries neither `inlined` nor `inlinedParent`; every `inlinedParent` link of scope `i` points to an index `t < i`) ∧ `ScopeRefsBounded F` (every scope named by a `loc` statement or call of `F` is in range); the caller-location walk inside the merged body then agrees with the original (`locValue_inline_callerScope`, `locValue_inline_calleeScope`) | tight: counterexample `cex_scopesWFF` (all other hypotheses hold and the conclusion fails; witness class: a caller `loc` naming missing scope 1, which after inlining is the callee's inlined tracked scope; temp-mode part). Conjuncts: `cex_scopesWFF` breaks the `ScopeRefsBounded F` conjunct while `ScopeTreeWF F.scopes` holds (`cex_scopesWF_breaks_refs_conjunct`). The links-point-below conjunct (`ScopeParentsBelow F.scopes`) is tight for the walk theorems (`cex_walkCallee_F`, `cex_walkCaller_F`: a 3-scope table with a 2-cycle); a program-level witness for it is not given (unknown). The clean-scope-`0` conjunct of `ScopeTreeWF F.scopes`: unknown — no counterexample is given; `locValue_inline_calleeScope` and `locValue_inline_callerScope` are proved without it, and the proof of this theorem does not use it, but no theorem with it dropped is stated here. |
| `hscG : ScopesWF G` | the same well-formedness for the callee's scope table and scope references | tight: counterexamples `cex_scopesWFG`, `cex_scopesWFG_root` (all other hypotheses hold and the conclusion fails; witness class: `cex_scopesWFG`: a tracked callee `loc` naming missing scope 1; `cex_scopesWFG_root`: a tracked callee whose scope 0 carries `inlined` (both return modes); temp-mode part). Conjuncts: `cex_scopesWFG` breaks the `ScopeRefsBounded G` conjunct (`ScopeTreeWF G.scopes` holds, `cex_scopesWF_breaks_refs_conjunct`); `cex_scopesWFG_root` breaks the clean-scope-`0` conjunct while `ScopeParentsBelow G.scopes` and `ScopeRefsBounded G` hold. The links-point-below conjunct of `G` is tight for the walk theorem (`cex_walkCallee_Gparents`); a program-level witness is not given (unknown). |
| `hfresh : SlotsFresh cfg F G` | callee locals `1 ≤ i < G.nlocals` go to host locals `≥ F.nlocals`, a range disjoint from every declared host local | tight: counterexample `cex_slotsFresh` (all other hypotheses hold and the conclusion fails; witness class: slot range overlapping caller local 1, which is live across the call; temp-mode part) |
| `hinj : SlotsInjective cfg G` | distinct callee locals `1 ≤ i, j < G.nlocals` go to distinct host locals | tight: counterexample `cex_slotsInjective` (all other hypotheses hold and the conclusion fails; witness class: two callee arguments sharing host local 5; temp-mode part) |
| `hret : cfg.ret = .temp t` | selects the fresh-temporary treatment of the return place: the callee writes `t` and the return block moves `t` into the destination | tight: counterexample `cex_destNotReadInCleanup` (all other hypotheses hold and the conclusion fails; witness class: the destination-mode configuration `(InlineCfg.canonical 2).withDest` (`ret = .dest ≠ .temp 2`) of a caller whose cleanup reads the destination; every other temp-mode hypothesis holds for it with `t = 2`, including `TempFresh 2`) |
| `htemp : TempFresh t cfg F G` | `TempFresh t cfg F G` = `F.nlocals ≤ t` ∧ `t` differs from every callee slot `cfg.slot i` (`1 ≤ i < G.nlocals`) | tight: counterexamples `cex_tempFresh`, `cex_tempFresh_callerLocal` (all other hypotheses hold and the conclusion fails; witness class: `cex_tempFresh`: the temporary equals the argument's slot, so the callee's early write to its return place clobbers the argument; `cex_tempFresh_callerLocal`: the temporary is the caller's live local 1). Conjuncts: Each conjunct is tight on its own: `cex_tempFresh` breaks the slot-disjointness conjunct while `F.nlocals ≤ t` holds (`cex_tempFresh_breaks_slot_conjunct`); `cex_tempFresh_callerLocal` breaks `F.nlocals ≤ t` while the slot-disjointness conjunct holds. |
| `hcont : cfg.redirectContinue = true` | the callee's `continue` unwind edges get the call's own unwind action | tight: counterexample `cex_redirectContinue` (all other hypotheses hold and the conclusion fails; witness class: a callee whose inner call continues unwinding: the caller's cleanup event `out 200` is skipped; temp-mode part) |
| `hres : cfg.resumeMap = .unwind` | the callee's `resume` is rewritten by the call's unwind action, not as a jump to the normal continuation | tight: counterexample `cex_resumeMap` (all other hypotheses hold and the conclusion fails; witness class: a callee panicking into its own cleanup: after it the inlined caller returns normally; temp-mode part) |
| `hlink : cfg.link = .rustc` | the outermost callee scope's `inlinedParent` is the callsite scope if that scope carries `inlined`, else the callsite scope's own `inlinedParent` | tight: counterexample `cex_linkRule` (all other hypotheses hold and the conclusion fails; witness class: second-level inlining at a call in a nested, non-inlined scope of an inlined tracked callee inside an untracked host (location `10` becomes `20`); temp-mode part) |
| `hcaps : F.caps = G.caps` | equal capability lists: `needCap` and ABI-sensitive calls in the moved code behave as in the callee | tight: counterexample `cex_capsAbi` (all other hypotheses hold and the conclusion fails; witness class: host capability list `[1]`, callee `[]` making an ABI-sensitive call, `abiC [1] ≠ abiC []`; temp-mode part) |

**Depth.** substantive: A stuttering forward simulation between the two-frame machine of the original program and the merged-frame machine of the inlined program, covering the argument-binding prologue, returns through the return block, unwinding through cleanup code and `continue` chains, the rewritten `resume`, and the scope walk; proved in `lean/ToyInline/Simulation.lean` (see "How the whole-program inlining theorems are proved" under Findings).

**Non-vacuity witness.** `progP` (caller with a cleanup block emitting `200`; callee that panics into its own cleanup on argument `0`) with `cfgP = InlineCfg.canonical 2`; also the second-level site of `linkP1` (`nonvacuity_inline_capsEq_secondLevel`). On argument `0` both programs produce `[out 100, out 200]` and `unwound` (`run_progP_lifo`, `behEquivAt_pos`). (`nonvacuity_inline_capsEq`, `nonvacuity_inline_capsEq_secondLevel`)

**Non-claims.**

- `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witness of `BlocksBounded F` (`cex_blocksBoundedF`) has a source run ending in `ub` whose inlined run ends in `aborted`; under a criterion in which `ub` permits any behaviour it would not refute the conclusion. Whether these hypotheses are needed for a refinement criterion is not examined here.
- `BehEquiv` compares event sequences and outcomes from each entry; it says nothing about step counts, code size, stack depth or performance.
- `F.caps = G.caps` is equality of lists (order and multiplicity matter), not equality as sets; `p.abi` is an arbitrary function of the list. Whether set-equal, order-distinct lists suffice is not examined (no counterexample for them is proved here).
- One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined.
- The toy has no `catch` or search-phase unwinding, no double-panic rule beyond explicit `terminate` actions, no projections, borrows, storage markers, generics, recursion limits or debug information; values are unbounded naturals (`Rvalue.add` does not wrap); a missing call argument is read as `0` and extra arguments are ignored (`argOr`, `bindArgs`).
- The return place goes to a fresh temporary. With the destination as return place and no further hypotheses the conclusion fails (`cex_destNotReadInCleanup`, `cex_cleanupClosed`); `inline_behEquiv_retDest_of_destUnobservedOnUnwind` states a destination-mode version with two extra hypotheses.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- CompCert v3.18 (AbsInt/CompCert commit 14d616046360a0b2611ebdfc2f98368af402e1f7), backend/Inlining.v L166-186 (`Record context`: a source instruction at PC `n` is relocated to `n + ctx.(dpc)`, pseudo-registers are shifted by `ctx.(dreg)`, and "return" instructions become "return" or "move" instructions as governed by `ctx.(retinfo)`) and backend/Inliningproof.v L1297-1305 (`Theorem transf_program_correct: forward_simulation (semantics prog) (semantics tprog).`). RTL has no unwinding, cleanup blocks, capability guards or caller-location scopes.
- Yong Kiam Tan, Magnus O. Myreen, Ramana Kumar, Anthony Fox, Scott Owens and Michael Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29:e2, 2019, doi:10.1017/S0956796818000229; CakeML/cakeml commit 16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9, compiler/backend/bvl_inlineScript.sml L14-41 (`tick_inline_def`, inlining of known calls in BVL, a first-order language with `Raise`/`Handle`) and compiler/backend/proofs/bvl_inlineProofScript.sml L2030-2039 (`compile_prog_semantics`: if the source semantics is not `Fail`, the compiled program has the same semantics). Mechanized inlining in the presence of exceptions; no CFG cleanup-block splicing, capability guards or caller-location scopes.
- Xavier Leroy, "A formally verified compiler back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), Section 2.1, Definitions 1–5: "Bisimulation" (`∀B, S ⇓ B ⇐⇒ C ⇓ B`, "exactly the same sets of observable behaviors") versus backward and forward simulation, including the variants restricted to safe source programs; the paper notes that Definitions 1 and 2 imply that if the source always goes wrong, so does the compiled program.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L869-883 (a new return block is pushed; L870-871 verbatim: "Prepare a new block for code that should execute when call returns. We don't use / target block directly since it might have other predecessors.") and L919-928 (L919-920 verbatim: "Always create a local to hold the destination, as `RETURN_PLACE` may appear / where a full `Place` is not allowed."; when the destination is a plain local it is used directly).
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1193-1206 (`map_local`: the return place maps to `self.destination`, argument `i` to `self.args[i]`, other locals to a fresh range) and L1120-1146 (`create_temp_if_necessary`: "Reuse the operand if it is a moved temporary."; otherwise a fresh temporary is assigned the argument). Unlike the toy, rustc may use an existing caller temporary as a callee argument local instead of copying into a fresh slot.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1220-1236 (`map_unwind`: inside a callee cleanup block, `Cleanup`/`Continue` unwind actions are a compiler bug (`bug!("cleanup on cleanup block")`); otherwise `Cleanup(target)` is shifted and `Continue` becomes the call's own unwind action, "Add an unwind edge to the original call's cleanup block") and L1326-1340 (`Return` becomes `Goto` the return block, or `Unreachable` without one; `UnwindResume` becomes `Goto` for `Cleanup`, stays `UnwindResume` for `Continue`, becomes `Unreachable`/`UnwindTerminate` for `Unreachable`/`Terminate`); L505-507 skip call sites in cleanup blocks. The toy has no `Unreachable` unwind action, allows unwind actions inside callee cleanup blocks, and does not skip call sites in cleanup blocks.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1248-1268 (`visit_source_scope_data`: the outermost callee scope, recognised by `parent_scope.is_none()`, gets the callsite scope as lexical `parent_scope`, `inlined = Some((callee, callsite span))` and `inlined_parent_scope` = the callsite scope if it is inlined, else the callsite scope's own `inlined_parent_scope`; inner scopes without `inlined_parent_scope` get the mapped outermost callee scope). The toy has no lexical `parent_scope` and recognises the outermost scope by index `0`.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L706-710 (direct self-recursion is refused: `return Err("self-recursion")`) and L829-840 (inlining is refused for incompatible sanitizer sets or instruction sets). The toy's `inline` performs none of these checks.
- LLVM llvmorg-21.1.0 (llvm/llvm-project commit 3623fe661ae35c6c80ac221f14d85be76aa870f1), llvm/lib/Transforms/Utils/InlineFunction.cpp L235-253 (`LandingPadInliningInfo::forwardResume`: "Forward the 'resume' instruction to the caller's landing pad block."), L557-613 (`HandleCallsInBlockInlinedThroughInvoke`: calls that can throw in a body inlined into an `invoke` become invokes that unwind to the invoke's destination), L615-670 and L672-799 (`HandleInlinedLandingPad`, `HandleInlinedEHPad`). The analogues of the toy's `resume` rewriting and `continue`-edge redirection in a production inliner; not mechanized.

**Design question.** When is a spliced CFG equivalent to the original two-frame execution, including unwinding with per-frame cleanup order?

### R3. `inline_behEquiv_retDest_of_destUnobservedOnUnwind` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** At a call site `IsCallSite p f b F ci G`, suppose `LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G` and `SlotsInjective cfg G` (as in `inline_behEquiv_retTemp_of_capsEq`); the callee's return place is the call's destination (`cfg.ret = .dest`; there is no return temporary); every unwind edge of `F` leads to a cleanup block and every successor of a cleanup block of `F` is a cleanup block (`CleanupClosed F`); no cleanup block of `F` reads `ci.dest` (`DestNotReadInCleanup F ci.dest`); `continue` edges are redirected, `resume` is rewritten by the call's unwind action, the `rustc` scope-link rule is used; and `F.caps = G.caps`. Then `BehEquiv p (inline p f b cfg)`: from every entry the maximal event sequences and outcomes of `run` coincide.

**Tier.** T1: As R2; the destination-mode variant corresponds to rustc's use of a plain-local destination as the callee's return place.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:96-107
theorem inline_behEquiv_retDest_of_destUnobservedOnUnwind
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .dest)
    (hclosed : CleanupClosed F) (hdest : DestNotReadInCleanup F ci.dest)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hcaps : F.caps = G.caps) :
    BehEquiv p (inline p f b cfg) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsite : IsCallSite p f b F ci G` | names the objects the other hypotheses talk about: function `f` of `p` is `F`, its block `b` ends in the call `ci`, and the callee of `ci` is `G`; without it the other hypotheses constrain unrelated bodies | tight: counterexample `cex_isCallSite` (all other hypotheses hold and the conclusion fails; witness class: a two-function program whose function 0 is `freshF`, checked against the mismatched `F := emptyF` (no locals, no blocks); dest-mode part (configuration `cfg.withDest`)) |
| `hlocF : LocalsBounded F` | every local mentioned by `F` (including the return place read by `ret`) is below `F.nlocals`, so slots at or above `F.nlocals` cannot clobber caller locals | tight: counterexample `cex_localsBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller declaring 1 local that keeps local 1 live across the call (slot 1 = local 1); dest-mode part (configuration `cfg.withDest`)) |
| `hlocG : LocalsBounded G` | every local mentioned by `G` is below `G.nlocals`, so the prologue binds or zeroes all of them | tight: counterexample `cex_localsBoundedG` (all other hypotheses hold and the conclusion fails; witness class: a callee declaring 1 local that reads local 1 (its argument), which the prologue does not bind; dest-mode part (configuration `cfg.withDest`)) |
| `hblkF : BlocksBounded F` | every jump target of `F` (goto, branch, call target, cleanup target) is one of `F`'s blocks; a missing block would become the return block or a callee block after inlining | tight: counterexample `cex_blocksBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller jumping to missing block 4: the original run ends in `ub`, the inlined run (block 4 is now a callee block) in `aborted`; the witness relies on `BehEquiv` distinguishing `ub` (see non-claims); dest-mode part (configuration `cfg.withDest`)) |
| `hscF : ScopesWF F` | `ScopesWF F` = `ScopeTreeWF F.scopes` (scope `0` exists and carries neither `inlined` nor `inlinedParent`; every `inlinedParent` link of scope `i` points to an index `t < i`) ∧ `ScopeRefsBounded F` (every scope named by a `loc` statement or call of `F` is in range); the caller-location walk inside the merged body then agrees with the original (`locValue_inline_callerScope`, `locValue_inline_calleeScope`) | tight: counterexample `cex_scopesWFF` (all other hypotheses hold and the conclusion fails; witness class: a caller `loc` naming missing scope 1, which after inlining is the callee's inlined tracked scope; dest-mode part (configuration `cfg.withDest`)). Conjuncts: `cex_scopesWFF` breaks the `ScopeRefsBounded F` conjunct while `ScopeTreeWF F.scopes` holds (`cex_scopesWF_breaks_refs_conjunct`). The links-point-below conjunct (`ScopeParentsBelow F.scopes`) is tight for the walk theorems (`cex_walkCallee_F`, `cex_walkCaller_F`: a 3-scope table with a 2-cycle); a program-level witness for it is not given (unknown). The clean-scope-`0` conjunct of `ScopeTreeWF F.scopes`: unknown — no counterexample is given; `locValue_inline_calleeScope` and `locValue_inline_callerScope` are proved without it, and the proof of this theorem does not use it, but no theorem with it dropped is stated here. |
| `hscG : ScopesWF G` | the same well-formedness for the callee's scope table and scope references | tight: counterexamples `cex_scopesWFG`, `cex_scopesWFG_root` (all other hypotheses hold and the conclusion fails; witness class: `cex_scopesWFG`: a tracked callee `loc` naming missing scope 1; `cex_scopesWFG_root`: a tracked callee whose scope 0 carries `inlined` (both return modes); dest-mode part (configuration `cfg.withDest`)). Conjuncts: `cex_scopesWFG` breaks the `ScopeRefsBounded G` conjunct (`ScopeTreeWF G.scopes` holds, `cex_scopesWF_breaks_refs_conjunct`); `cex_scopesWFG_root` breaks the clean-scope-`0` conjunct while `ScopeParentsBelow G.scopes` and `ScopeRefsBounded G` hold. The links-point-below conjunct of `G` is tight for the walk theorem (`cex_walkCallee_Gparents`); a program-level witness is not given (unknown). |
| `hfresh : SlotsFresh cfg F G` | callee locals `1 ≤ i < G.nlocals` go to host locals `≥ F.nlocals`, a range disjoint from every declared host local | tight: counterexample `cex_slotsFresh` (all other hypotheses hold and the conclusion fails; witness class: slot range overlapping caller local 1, which is live across the call; dest-mode part (configuration `cfg.withDest`)) |
| `hinj : SlotsInjective cfg G` | distinct callee locals `1 ≤ i, j < G.nlocals` go to distinct host locals | tight: counterexample `cex_slotsInjective` (all other hypotheses hold and the conclusion fails; witness class: two callee arguments sharing host local 5; dest-mode part (configuration `cfg.withDest`)) |
| `hret : cfg.ret = .dest` | selects the destination treatment of the return place | tight: counterexample `cex_tempFresh` (all other hypotheses hold and the conclusion fails; witness class: the temp-mode configuration `tempCfg` (`ret = .temp 2 ≠ .dest`); every dest-mode hypothesis holds for it (temp-mode part)) |
| `hclosed : CleanupClosed F` | after a panic the caller executes only cleanup blocks, which do not read the destination | tight: counterexample `cex_cleanupClosed` (all other hypotheses hold and the conclusion fails; witness class: a cleanup block jumping to a normal block that reads the destination) |
| `hdest : DestNotReadInCleanup F ci.dest` | the callee's writes to its return place (and the prologue's zeroing of it) are invisible on the unwind path | tight: counterexample `cex_destNotReadInCleanup` (all other hypotheses hold and the conclusion fails; witness class: a caller cleanup block emitting the destination) |
| `hcont : cfg.redirectContinue = true` | the callee's `continue` unwind edges get the call's own unwind action | tight: counterexample `cex_redirectContinue` (all other hypotheses hold and the conclusion fails; witness class: a callee whose inner call continues unwinding: the caller's cleanup event `out 200` is skipped; dest-mode part) |
| `hres : cfg.resumeMap = .unwind` | the callee's `resume` is rewritten by the call's unwind action, not as a jump to the normal continuation | tight: counterexample `cex_resumeMap` (all other hypotheses hold and the conclusion fails; witness class: a callee panicking into its own cleanup: after it the inlined caller returns normally; dest-mode part) |
| `hlink : cfg.link = .rustc` | the outermost callee scope's `inlinedParent` is the callsite scope if that scope carries `inlined`, else the callsite scope's own `inlinedParent` | tight: counterexample `cex_linkRule` (all other hypotheses hold and the conclusion fails; witness class: second-level inlining at a call in a nested, non-inlined scope of an inlined tracked callee inside an untracked host (location `10` becomes `20`); dest-mode part) |
| `hcaps : F.caps = G.caps` | equal capability lists: `needCap` and ABI-sensitive calls in the moved code behave as in the callee | tight: counterexample `cex_capsAbi` (all other hypotheses hold and the conclusion fails; witness class: host capability list `[1]`, callee `[]` making an ABI-sensitive call, `abiC [1] ≠ abiC []`; dest-mode part) |

**Depth.** substantive: As R2, with a store relation that lets the destination `ci.dest` differ between the two machines after an unwind out of the inlined body while control is in cleanup blocks of `F`: `CleanupClosed F` keeps control in cleanup blocks and `DestNotReadInCleanup F ci.dest` ensures that none of them reads the destination; proved in `lean/ToyInline/Simulation.lean`.

**Non-vacuity witness.** `progP` with `cfgPd` (destination local 1; the caller's single cleanup block emits a constant). (`nonvacuity_inline_retDest`)

**Non-claims.**

- `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witness of `BlocksBounded F` has a source run ending in `ub`. Whether these hypotheses are needed for a refinement criterion is not examined here.
- `BehEquiv` compares event sequences and outcomes from each entry; it says nothing about step counts, code size, stack depth or performance.
- `F.caps = G.caps` is equality of lists (order and multiplicity matter), not equality as sets; `p.abi` is an arbitrary function of the list. Whether set-equal, order-distinct lists suffice is not examined (no counterexample for them is proved here).
- No destination-mode theorem under `CapsSubset` (the analogue of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` or `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`) is stated or refuted here.
- One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined.
- `CleanupClosed` and `DestNotReadInCleanup` are syntactic sufficient conditions; liveness of the destination on the unwind path is not modelled. rustc's inliner uses a plain-local destination directly (inline.rs L919-928) and contains no such syntactic check in inline.rs; whether MIR's own invariants (for example that the destination is not initialised on the unwind edge of a call) exclude cleanup code that reads the destination is not examined here.
- Says nothing about destinations with projections (rustc borrows those through a temporary, inline.rs L901-917); the toy has plain locals.
- The toy has no `catch` or search-phase unwinding, no double-panic rule beyond explicit `terminate` actions, no projections, borrows, storage markers, generics, recursion limits or debug information; values are unbounded naturals (`Rvalue.add` does not wrap); a missing call argument is read as `0` and extra arguments are ignored (`argOr`, `bindArgs`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L869-883 (a new return block is pushed; L870-871 verbatim: "Prepare a new block for code that should execute when call returns. We don't use / target block directly since it might have other predecessors.") and L919-928 (L919-920 verbatim: "Always create a local to hold the destination, as `RETURN_PLACE` may appear / where a full `Place` is not allowed."; when the destination is a plain local it is used directly).
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1220-1236 (`map_unwind`: inside a callee cleanup block, `Cleanup`/`Continue` unwind actions are a compiler bug (`bug!("cleanup on cleanup block")`); otherwise `Cleanup(target)` is shifted and `Continue` becomes the call's own unwind action, "Add an unwind edge to the original call's cleanup block") and L1326-1340 (`Return` becomes `Goto` the return block, or `Unreachable` without one; `UnwindResume` becomes `Goto` for `Cleanup`, stays `UnwindResume` for `Continue`, becomes `Unreachable`/`UnwindTerminate` for `Unreachable`/`Terminate`); L505-507 skip call sites in cleanup blocks. The toy has no `Unreachable` unwind action, allows unwind actions inside callee cleanup blocks, and does not skip call sites in cleanup blocks.
- CompCert v3.18 (AbsInt/CompCert commit 14d616046360a0b2611ebdfc2f98368af402e1f7), backend/Inlining.v L166-186 (`Record context`: a source instruction at PC `n` is relocated to `n + ctx.(dpc)`, pseudo-registers are shifted by `ctx.(dreg)`, and "return" instructions become "return" or "move" instructions as governed by `ctx.(retinfo)`) and backend/Inliningproof.v L1297-1305 (`Theorem transf_program_correct: forward_simulation (semantics prog) (semantics tprog).`). RTL has no unwinding, cleanup blocks, capability guards or caller-location scopes.

**Design question.** When may the callee's return place be the call's destination rather than a fresh temporary?

### R4. `terminalHolds_iff_of_behEquivAt` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** If `p` and `q` are behaviourally equivalent from entry `e` (`BehEquivAt p q e`, defined from `run`), then for every predicate `P` on observations, `P` holds of every halted `run` of `p` from `e` (`TerminalHolds P p e`) iff `P` holds of every halted `run` of `q` from `e`.

**Tier.** T0: Equivalence of behaviours preserves specifications that are predicates of the observable behaviour (Leroy 2009, Section 2.1, Definition 6); a restatement for halted observations.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:120-122
theorem terminalHolds_iff_of_behEquivAt (P : Obs → Prop) (p q : Program) (e : Entry)
    (h : BehEquivAt p q e) :
    TerminalHolds P p e ↔ TerminalHolds P q e := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : BehEquivAt p q e` | the two programs have the same halted observations from `e` | tight: counterexample `cex_terminal_behEquiv` (all other hypotheses hold and the conclusion fails; witness class: a returning and a panicking one-block program, `P = NoPanic`) |

**Depth.** definitional: Unfolds the definitions: halted observations are maximal in the prefix order.

**Non-vacuity witness.** `progP` and its canonical inlining from entry `⟨0, [0], 0⟩`. (`nonvacuity_terminalHolds_iff`)

**Non-claims.**

- `TerminalHolds P p e` holds vacuously, for every `P` (including `fun _ => False`), when the run from `e` never halts; so it transfers partial correctness and says nothing about termination.
- Applies to predicates of the observation (`Obs`: emitted events and outcome) under the reference caller-location policy (`run` uses `.walk`) from one entry; internal state (local values, stack depth, visited blocks), relations between different entries, liveness, step counts and resource use are not covered.
- Combined with `inline_behEquiv_retTemp_of_capsEq` (whose conclusion `BehEquiv` gives `BehEquivAt` from every entry) it transfers such conditions between `p` and `inline p f b cfg` under that theorem's hypotheses (a composition of two proved theorems, not stated as a separate theorem here); it does not say that a condition proved for the inlined program establishes the callee's standalone contract (`inlined_vc_not_callee_contract`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- Xavier Leroy, "A formally verified compiler back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), Section 2.1, Definition 6 ("Preservation of a specification", `S |= Spec =⇒ C |= Spec`, for a specification given as a predicate `Spec(B)` of the observable behaviour).

**Design question.** What do verification conditions proved after inlining say about the original program?

### R5. `safetyHolds_iff_of_behEquivAt_of_prefixClosed` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** If `p` and `q` are behaviourally equivalent from entry `e` and the predicate `S` on observations is closed under observation prefixes (`PrefixClosed S`), then `S` holds of the observation of `run` of `p` from `e` at every step budget (`SafetyHolds S p e`) iff it holds of every such observation of `q`.

**Tier.** T0: Equivalence of behaviours preserves properties closed under prefixes of finite observations; a restatement.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:136-138
theorem safetyHolds_iff_of_behEquivAt_of_prefixClosed (S : Obs → Prop) (p q : Program)
    (e : Entry) (h : BehEquivAt p q e) (hS : PrefixClosed S) :
    SafetyHolds S p e ↔ SafetyHolds S q e := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : BehEquivAt p q e` | each finite observation of one program is a prefix of one of the other | tight: counterexample `cex_safety_behEquiv` (all other hypotheses hold and the conclusion fails; witness class: a returning and a panicking one-block program, `S = NoPanic`) |
| `hS : PrefixClosed S` | finite observations of equivalent programs are related by prefixes, not equal, because inlining changes step counts | tight: counterexample `cex_safety_prefixClosed` (all other hypotheses hold and the conclusion fails; witness class: `S` = "has halted"; a program with a missing entry function versus one taking a silent step first) |

**Depth.** definitional: A two-line term: each observation of one program is a prefix of an observation of the other.

**Non-vacuity witness.** `progP` and its canonical inlining from `⟨0, [0], 0⟩`, `S = NoPanic` (`prefixClosed_noPanic`). (`nonvacuity_safetyHolds_iff`)

**Non-claims.**

- `SafetyHolds S p e` checks `S` at every step budget `n`, including `n = 0`; the definition does not require `S` to be prefix-closed, so for a predicate that is not, such as "has halted", `SafetyHolds` requires the initial configuration to be halted already, and such predicates need not transfer (`cex_safety_prefixClosed`).
- Applies to single-entry predicates of the observation under `run` (policy `.walk`); hyperproperties (relating several entries or runs), liveness and termination properties, internal-state invariants and other caller-location policies are not covered.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- Bowen Alpern and Fred B. Schneider, "Defining liveness", Information Processing Letters 21(4):181–185, 1985, doi:10.1016/0020-0190(85)90056-0: the safety/liveness distinction for properties of infinite executions. `PrefixClosed` here is a closure condition on finite observations; no formal correspondence with their definition of safety is proved.

**Design question.** Which safety properties transfer across inlining?

### R6. `inlined_vc_not_callee_contract` (counterexample)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** In the program `vcP`, whose caller passes the constant `7` to the callee `gP` (which panics into its cleanup on argument `0`), and its canonical inlining `vcQ`: "no escaped panic" (`NoPanic`) holds of every halted `run` of `vcQ` and of `vcP` from the caller's entry `e0`; from the callee's own entry with argument `0` (`⟨1, [0], 0⟩`), `run` of `vcP` and of `vcQ` with step budget 30 (at most 30 steps) both give the events `[out 100]` and the outcome `unwound`, so `NoPanic` fails for both programs from that entry.

**Tier.** T1: Folklore (facts that hold at a call site are not the callee's contract) made concrete and mechanized in the toy.

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:143-147
theorem inlined_vc_not_callee_contract :
    TerminalHolds NoPanic vcQ e0 ∧ TerminalHolds NoPanic vcP e0 ∧
      run vcP 30 (init vcP ⟨1, [0], 0⟩) = ⟨[.out 100], some .unwound⟩ ∧
      run vcQ 30 (init vcQ ⟨1, [0], 0⟩) = ⟨[.out 100], some .unwound⟩ ∧
      ¬ TerminalHolds NoPanic vcP ⟨1, [0], 0⟩ ∧ ¬ TerminalHolds NoPanic vcQ ⟨1, [0], 0⟩ := …
```

**Hypothesis ledger.** None (a closed statement about concrete programs).

**Depth.** shallow: Decided by evaluation.

**Non-vacuity witness.** The theorem is itself the instance. (`inlined_vc_not_callee_contract`)

**Non-claims.**

- One instance: a verification condition proved for an inlined caller need not hold for the callee's standalone entry, because the inlined code is executed with the call-site arguments. It does not say every such condition fails for the callee.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- No primary source states this specific observation; it is common knowledge in modular verification (not relied on as a citation).

**Design question.** What do verification conditions proved after inlining not say about the callee?

### R7. `capsSubset_needed_inlined_needCap_faults` (counterexample)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** In `needP` the callee `needG` holds and uses capability `3` and the host `capF []` holds none. With the canonical configuration for one host local (temp mode, `t = 1`), every hypothesis of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` and of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree` other than `CapsSubset G F` holds, and `CapsSubset needG (capF [])` fails. `run` of `needP` from `e0` gives `[out 1]` and `returned 0`; `run` of the inlined program, in temp mode and in destination mode, gives no events and the outcome `capFault`; neither inlined program is behaviourally equivalent to `needP`.

**Tier.** T1: That inlining into a host lacking a callee's capability is wrong is folklore (the Rust Reference's call rule for safe `#[target_feature]` functions has the same shape); here a concrete mechanized toy witness.

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:479-495
theorem capsSubset_needed_inlined_needCap_faults :
    (IsCallSite needP 0 0 (capF []) plainCi needG ∧ LocalsBounded (capF []) ∧
      LocalsBounded needG ∧ BlocksBounded (capF []) ∧ ScopesWF (capF []) ∧ ScopesWF needG ∧
      SlotsFresh (InlineCfg.canonical 1) (capF []) needG ∧
      SlotsInjective (InlineCfg.canonical 1) needG ∧
      (InlineCfg.canonical 1).ret = .temp 1 ∧ TempFresh 1 (InlineCfg.canonical 1) (capF []) needG ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapLegal needG ∧ AbiInsensitive needG ∧ plainCi.abiSensitive = false ∧
      AbiAgree needP (capF []) needG ∧ ¬ CapsSubset needG (capF [])) ∧
    run needP 30 (init needP e0) = ⟨[.out 1], some (.returned 0)⟩ ∧
    run (inline needP 0 0 (InlineCfg.canonical 1)) 40
        (init (inline needP 0 0 (InlineCfg.canonical 1)) e0) = ⟨[], some .capFault⟩ ∧
    run (inline needP 0 0 (InlineCfg.canonical 1).withDest) 40
        (init (inline needP 0 0 (InlineCfg.canonical 1).withDest) e0) = ⟨[], some .capFault⟩ ∧
    ¬ BehEquiv needP (inline needP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv needP (inline needP 0 0 (InlineCfg.canonical 1).withDest) := …
```

**Hypothesis ledger.** None (a closed statement about concrete programs).

**Depth.** shallow: Decided by evaluation.

**Non-vacuity witness.** The theorem is itself the instance. (`capsSubset_needed_inlined_needCap_faults`)

**Non-claims.**

- Shows that `CapsSubset` cannot be dropped from the two subset-guard theorems in the toy (with every other hypothesis kept); it does not show that it suffices — it does not (`capsSubset_guard_insufficient`).
- The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled.
- In the toy a missing capability is a deterministic fault (`capFault`); the Rust Reference makes calling code compiled with a feature the platform does not support undefined behaviour (codegen.md L462-465).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/attributes/codegen.md L467-475, rule attributes.codegen.target_feature.safety-restrictions; L470-471 (verbatim): "- Safe `#[target_feature]` functions (and closures that inherit the attribute) can only be safely called within a caller that enables all the `target_feature`s that the callee enables. / This restriction does not apply in an `unsafe` context."; L475 adds that implicitly enabled features are included (an `sse2` function can call ones marked with `sse`), and L462-465 (attributes.codegen.target_feature.target-ub) make calling a function compiled with a feature the running platform does not support undefined behaviour unless the platform documents it as safe.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L842-851: inlining is refused when the callee's and the caller's target-feature lists differ; comment, L845-849 verbatim: "In general it is not correct to inline a callee with target features that are a / subset of the caller. This is because the callee might contain calls, and the ABI of / those calls depends on the target features of the surrounding function. By moving a / `Call` terminator from one MIR body to another with more target features, we might / change the ABI of that call!"
- LLVM llvmorg-21.1.0 (llvm/llvm-project commit 3623fe661ae35c6c80ac221f14d85be76aa870f1), llvm/lib/Target/X86/X86TargetTransformInfo.cpp L6494-6550 (`X86TTIImpl::areInlineCompatible`: equal feature sets apart from an ignore list are compatible; otherwise the callee's features must be a subset of the caller's — L6510-6511 verbatim: "If the features are a subset, we need to additionally check for calls / that may become ABI-incompatible as a result of inlining." — and each call in the callee whose argument or return types include a vector or aggregate is accepted if it is inline assembly, an intrinsic, or a direct call that `areTypesABICompatible` accepts, and rejected if it is an indirect call) and L6552-6572 (`areTypesABICompatible`: after the generic check, a caller and callee that differ in `useAVX512Regs()` are treated as compatible when no type is a vector or aggregate and as incompatible otherwise); llvm/include/llvm/Analysis/TargetTransformInfo.h L1746-1752 (L1746-1747 verbatim: "\returns True if the caller and callee agree on how \p Types will be / passed to or returned from the callee."). LLVM checks ABI compatibility per moved call and per argument type, where the toy uses one Boolean ABI class per capability list.

**Design question.** Which capability guard prevents inlining code into a host lacking the callee's capabilities?

### R8. `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** At a call site `IsCallSite p f b F ci G`, suppose every hypothesis of `inline_behEquiv_retTemp_of_capsEq` other than `F.caps = G.caps` holds: `LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G`, `SlotsInjective cfg G`, `cfg.ret = .temp t`, `TempFresh t cfg F G` (`F.nlocals ≤ t` and `t` differs from every callee slot), redirected `continue` edges, `resume` rewritten by the call's unwind action and the `rustc` link rule. Suppose further that every capability in the callee's list is in the caller's list (`CapsSubset G F`), every `needCap c` in the callee names a capability in the callee's list (`CapLegal G`), no block of the callee (reachable or not) terminates in an ABI-sensitive call (`AbiInsensitive G`) and the inlined call itself is not ABI-sensitive (`ci.abiSensitive = false`). Then `BehEquiv p (inline p f b cfg)`.

**Tier.** T1: Folklore made precise: a subset guard suffices when the moved code's behaviour depends on the host's capabilities only through `needCap` legality — here when the callee is statically capability-legal (`CapLegal G`), has no block (reachable or not) terminating in an ABI-sensitive call (`AbiInsensitive G`), and the inlined call itself is not ABI-sensitive (`ci.abiSensitive = false`).

**Statement.**

```lean
-- lean/ToyInline/Results.lean:149-160
theorem inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) (t : Local)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hsub : CapsSubset G F) (hlegal : CapLegal G) (habi : AbiInsensitive G)
    (hcs : ci.abiSensitive = false) :
    BehEquiv p (inline p f b cfg) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsite : IsCallSite p f b F ci G` | names the objects the other hypotheses talk about: function `f` of `p` is `F`, its block `b` ends in the call `ci`, and the callee of `ci` is `G`; without it the other hypotheses constrain unrelated bodies | tight: counterexample `cex_isCallSite` (all other hypotheses hold and the conclusion fails; witness class: a two-function program whose function 0 is `freshF`, checked against the mismatched `F := emptyF` (no locals, no blocks); temp-mode part) |
| `hlocF : LocalsBounded F` | every local mentioned by `F` (including the return place read by `ret`) is below `F.nlocals`, so slots at or above `F.nlocals` cannot clobber caller locals | tight: counterexample `cex_localsBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller declaring 1 local that keeps local 1 live across the call (slot 1 = local 1); temp-mode part) |
| `hlocG : LocalsBounded G` | every local mentioned by `G` is below `G.nlocals`, so the prologue binds or zeroes all of them | tight: counterexample `cex_localsBoundedG` (all other hypotheses hold and the conclusion fails; witness class: a callee declaring 1 local that reads local 1 (its argument), which the prologue does not bind; temp-mode part) |
| `hblkF : BlocksBounded F` | every jump target of `F` (goto, branch, call target, cleanup target) is one of `F`'s blocks; a missing block would become the return block or a callee block after inlining | tight: counterexample `cex_blocksBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller jumping to missing block 4: the original run ends in `ub`, the inlined run (block 4 is now a callee block) in `aborted`; the witness relies on `BehEquiv` distinguishing `ub` (see non-claims); temp-mode part) |
| `hscF : ScopesWF F` | `ScopesWF F` = `ScopeTreeWF F.scopes` (scope `0` exists and carries neither `inlined` nor `inlinedParent`; every `inlinedParent` link of scope `i` points to an index `t < i`) ∧ `ScopeRefsBounded F` (every scope named by a `loc` statement or call of `F` is in range); the caller-location walk inside the merged body then agrees with the original (`locValue_inline_callerScope`, `locValue_inline_calleeScope`) | tight: counterexample `cex_scopesWFF` (all other hypotheses hold and the conclusion fails; witness class: a caller `loc` naming missing scope 1, which after inlining is the callee's inlined tracked scope; temp-mode part). Conjuncts: `cex_scopesWFF` breaks the `ScopeRefsBounded F` conjunct while `ScopeTreeWF F.scopes` holds (`cex_scopesWF_breaks_refs_conjunct`). The links-point-below conjunct (`ScopeParentsBelow F.scopes`) is tight for the walk theorems (`cex_walkCallee_F`, `cex_walkCaller_F`: a 3-scope table with a 2-cycle); a program-level witness for it is not given (unknown). The clean-scope-`0` conjunct of `ScopeTreeWF F.scopes`: unknown — no counterexample is given; `locValue_inline_calleeScope` and `locValue_inline_callerScope` are proved without it, and the proof of this theorem does not use it, but no theorem with it dropped is stated here. |
| `hscG : ScopesWF G` | the same well-formedness for the callee's scope table and scope references | tight: counterexamples `cex_scopesWFG`, `cex_scopesWFG_root` (all other hypotheses hold and the conclusion fails; witness class: `cex_scopesWFG`: a tracked callee `loc` naming missing scope 1; `cex_scopesWFG_root`: a tracked callee whose scope 0 carries `inlined` (both return modes); temp-mode part). Conjuncts: `cex_scopesWFG` breaks the `ScopeRefsBounded G` conjunct (`ScopeTreeWF G.scopes` holds, `cex_scopesWF_breaks_refs_conjunct`); `cex_scopesWFG_root` breaks the clean-scope-`0` conjunct while `ScopeParentsBelow G.scopes` and `ScopeRefsBounded G` hold. The links-point-below conjunct of `G` is tight for the walk theorem (`cex_walkCallee_Gparents`); a program-level witness is not given (unknown). |
| `hfresh : SlotsFresh cfg F G` | callee locals `1 ≤ i < G.nlocals` go to host locals `≥ F.nlocals`, a range disjoint from every declared host local | tight: counterexample `cex_slotsFresh` (all other hypotheses hold and the conclusion fails; witness class: slot range overlapping caller local 1, which is live across the call; temp-mode part) |
| `hinj : SlotsInjective cfg G` | distinct callee locals `1 ≤ i, j < G.nlocals` go to distinct host locals | tight: counterexample `cex_slotsInjective` (all other hypotheses hold and the conclusion fails; witness class: two callee arguments sharing host local 5; temp-mode part) |
| `hret : cfg.ret = .temp t` | selects the fresh-temporary treatment of the return place: the callee writes `t` and the return block moves `t` into the destination | tight: counterexample `cex_destNotReadInCleanup` (all other hypotheses hold and the conclusion fails; witness class: the destination-mode configuration `(InlineCfg.canonical 2).withDest` (`ret = .dest ≠ .temp 2`) of a caller whose cleanup reads the destination; every other temp-mode hypothesis holds for it with `t = 2`, including `TempFresh 2`) |
| `htemp : TempFresh t cfg F G` | `TempFresh t cfg F G` = `F.nlocals ≤ t` ∧ `t` differs from every callee slot `cfg.slot i` (`1 ≤ i < G.nlocals`) | tight: counterexamples `cex_tempFresh`, `cex_tempFresh_callerLocal` (all other hypotheses hold and the conclusion fails; witness class: `cex_tempFresh`: the temporary equals the argument's slot, so the callee's early write to its return place clobbers the argument; `cex_tempFresh_callerLocal`: the temporary is the caller's live local 1). Conjuncts: Each conjunct is tight on its own: `cex_tempFresh` breaks the slot-disjointness conjunct while `F.nlocals ≤ t` holds (`cex_tempFresh_breaks_slot_conjunct`); `cex_tempFresh_callerLocal` breaks `F.nlocals ≤ t` while the slot-disjointness conjunct holds. |
| `hcont : cfg.redirectContinue = true` | the callee's `continue` unwind edges get the call's own unwind action | tight: counterexample `cex_redirectContinue` (all other hypotheses hold and the conclusion fails; witness class: a callee whose inner call continues unwinding: the caller's cleanup event `out 200` is skipped; temp-mode part) |
| `hres : cfg.resumeMap = .unwind` | the callee's `resume` is rewritten by the call's unwind action, not as a jump to the normal continuation | tight: counterexample `cex_resumeMap` (all other hypotheses hold and the conclusion fails; witness class: a callee panicking into its own cleanup: after it the inlined caller returns normally; temp-mode part) |
| `hlink : cfg.link = .rustc` | the outermost callee scope's `inlinedParent` is the callsite scope if that scope carries `inlined`, else the callsite scope's own `inlinedParent` | tight: counterexample `cex_linkRule` (all other hypotheses hold and the conclusion fails; witness class: second-level inlining at a call in a nested, non-inlined scope of an inlined tracked callee inside an untracked host (location `10` becomes `20`); temp-mode part) |
| `hsub : CapsSubset G F` | every capability in the callee's list is in the caller's list, so legal `needCap`s of the callee stay legal in the host | tight: counterexample `capsSubset_needed_inlined_needCap_faults` (all other hypotheses hold and the conclusion fails; witness class: callee `[3]` using capability 3, host `[]`: the inlined `needCap 3` ends in `capFault`) |
| `hlegal : CapLegal G` | every `needCap c` in the callee names a capability in the callee's list, so the callee does not rely on a fault that the richer host would let through | tight: counterexample `cex_capLegal` (all other hypotheses hold and the conclusion fails; witness class: callee `[]` executing `needCap 3`, host `[3]`: the original ends in `capFault`, the inlined program returns normally (relies on `BehEquiv` preserving `capFault`, see non-claims)) |
| `habi : AbiInsensitive G` | moved calls do not depend on `p.abi` | tight: counterexample `cex_capsAbi` (all other hypotheses hold and the conclusion fails; witness class: an ABI-sensitive call in the callee with host list `[1]`, callee `[]`, `abiC [1] ≠ abiC []`) |
| `hcs : ci.abiSensitive = false` | the inlined call's own argument passing is not ABI-sensitive (inlining removes that call) | tight: counterexample `cex_callAbiSensitive` (all other hypotheses hold and the conclusion fails; witness class: an ABI-sensitive inlined call from host `[1]` to callee `[]`: the original garbles the argument (`out 6`), the inlined prologue binds it unchanged (`out 5`); relies on `BehEquiv` preserving garbled values) |

**Depth.** substantive: As R2, plus capability reasoning: under `CapsSubset G F` and `CapLegal G` every `needCap` of the moved code succeeds in the host exactly when it succeeds in the callee, and with `AbiInsensitive G` and `ci.abiSensitive = false` no argument is garbled on either side; proved in `lean/ToyInline/Simulation.lean`.

**Non-vacuity witness.** `nv5P`: host list `[1, 2]`, callee `[2]` using capability 2, no ABI-sensitive calls; the host and callee ABI classes differ (`abiC`). (`nonvacuity_inline_capsSubset_abiInsensitive`)

**Non-claims.**

- `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witnesses of `BlocksBounded F` (source `ub`), `CapLegal G` (`cex_capLegal`: source `capFault`, inlined normal return) and `ci.abiSensitive = false` (`cex_callAbiSensitive`: source garbled argument `6`, inlined `5`) all have a source execution that the toy treats as a defined outcome but that a criterion treating capability faults and ABI mismatches as undefined behaviour would not constrain. Whether these hypotheses are needed for a refinement criterion is not examined here.
- Stated for the temporary return mode (`cfg.ret = .temp t`); no destination-mode companion under `CapsSubset` is established or refuted here.
- The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled.
- `CapsSubset` is list inclusion of capability lists.
- One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L842-851: inlining is refused when the callee's and the caller's target-feature lists differ; comment, L845-849 verbatim: "In general it is not correct to inline a callee with target features that are a / subset of the caller. This is because the callee might contain calls, and the ABI of / those calls depends on the target features of the surrounding function. By moving a / `Call` terminator from one MIR body to another with more target features, we might / change the ABI of that call!"
- The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/attributes/codegen.md L467-475, rule attributes.codegen.target_feature.safety-restrictions; L470-471 (verbatim): "- Safe `#[target_feature]` functions (and closures that inherit the attribute) can only be safely called within a caller that enables all the `target_feature`s that the callee enables. / This restriction does not apply in an `unsafe` context."; L475 adds that implicitly enabled features are included (an `sse2` function can call ones marked with `sse`), and L462-465 (attributes.codegen.target_feature.target-ub) make calling a function compiled with a feature the running platform does not support undefined behaviour unless the platform documents it as safe.
- LLVM llvmorg-21.1.0 (llvm/llvm-project commit 3623fe661ae35c6c80ac221f14d85be76aa870f1), llvm/lib/Target/X86/X86TargetTransformInfo.cpp L6494-6550 (`X86TTIImpl::areInlineCompatible`: equal feature sets apart from an ignore list are compatible; otherwise the callee's features must be a subset of the caller's — L6510-6511 verbatim: "If the features are a subset, we need to additionally check for calls / that may become ABI-incompatible as a result of inlining." — and each call in the callee whose argument or return types include a vector or aggregate is accepted if it is inline assembly, an intrinsic, or a direct call that `areTypesABICompatible` accepts, and rejected if it is an indirect call) and L6552-6572 (`areTypesABICompatible`: after the generic check, a caller and callee that differ in `useAVX512Regs()` are treated as compatible when no type is a vector or aggregate and as incompatible otherwise); llvm/include/llvm/Analysis/TargetTransformInfo.h L1746-1752 (L1746-1747 verbatim: "\returns True if the caller and callee agree on how \p Types will be / passed to or returned from the callee."). LLVM checks ABI compatibility per moved call and per argument type, where the toy uses one Boolean ABI class per capability list.

**Design question.** Is "caller ⊇ callee" enough when no block of the inlined body (reachable or not) terminates in an ABI-sensitive call?

### R9. `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** At a call site `IsCallSite p f b F ci G`, suppose every hypothesis of `inline_behEquiv_retTemp_of_capsEq` other than `F.caps = G.caps` holds (`LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G`, `SlotsInjective cfg G`, `cfg.ret = .temp t`, `TempFresh t cfg F G`, redirected `continue` edges, `resume` rewritten by the call's unwind action, the `rustc` link rule), every capability in the callee's list is in the caller's list (`CapsSubset G F`), every `needCap c` in the callee names a capability in the callee's list (`CapLegal G`), and `p.abi F.caps = p.abi G.caps` (`AbiAgree p F G`). Then `BehEquiv p (inline p f b cfg)`, also when ABI-sensitive calls are present.

**Tier.** T1: Folklore made precise: subset plus ABI agreement is the condition rustc's comment points at (inline.rs L842-851); LLVM's X86 hook checks a per-call version.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:176-186
theorem inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) (t : Local)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hsub : CapsSubset G F) (hlegal : CapLegal G) (hagree : AbiAgree p F G) :
    BehEquiv p (inline p f b cfg) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsite : IsCallSite p f b F ci G` | names the objects the other hypotheses talk about: function `f` of `p` is `F`, its block `b` ends in the call `ci`, and the callee of `ci` is `G`; without it the other hypotheses constrain unrelated bodies | tight: counterexample `cex_isCallSite` (all other hypotheses hold and the conclusion fails; witness class: a two-function program whose function 0 is `freshF`, checked against the mismatched `F := emptyF` (no locals, no blocks); temp-mode part) |
| `hlocF : LocalsBounded F` | every local mentioned by `F` (including the return place read by `ret`) is below `F.nlocals`, so slots at or above `F.nlocals` cannot clobber caller locals | tight: counterexample `cex_localsBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller declaring 1 local that keeps local 1 live across the call (slot 1 = local 1); temp-mode part) |
| `hlocG : LocalsBounded G` | every local mentioned by `G` is below `G.nlocals`, so the prologue binds or zeroes all of them | tight: counterexample `cex_localsBoundedG` (all other hypotheses hold and the conclusion fails; witness class: a callee declaring 1 local that reads local 1 (its argument), which the prologue does not bind; temp-mode part) |
| `hblkF : BlocksBounded F` | every jump target of `F` (goto, branch, call target, cleanup target) is one of `F`'s blocks; a missing block would become the return block or a callee block after inlining | tight: counterexample `cex_blocksBoundedF` (all other hypotheses hold and the conclusion fails; witness class: a caller jumping to missing block 4: the original run ends in `ub`, the inlined run (block 4 is now a callee block) in `aborted`; the witness relies on `BehEquiv` distinguishing `ub` (see non-claims); temp-mode part) |
| `hscF : ScopesWF F` | `ScopesWF F` = `ScopeTreeWF F.scopes` (scope `0` exists and carries neither `inlined` nor `inlinedParent`; every `inlinedParent` link of scope `i` points to an index `t < i`) ∧ `ScopeRefsBounded F` (every scope named by a `loc` statement or call of `F` is in range); the caller-location walk inside the merged body then agrees with the original (`locValue_inline_callerScope`, `locValue_inline_calleeScope`) | tight: counterexample `cex_scopesWFF` (all other hypotheses hold and the conclusion fails; witness class: a caller `loc` naming missing scope 1, which after inlining is the callee's inlined tracked scope; temp-mode part). Conjuncts: `cex_scopesWFF` breaks the `ScopeRefsBounded F` conjunct while `ScopeTreeWF F.scopes` holds (`cex_scopesWF_breaks_refs_conjunct`). The links-point-below conjunct (`ScopeParentsBelow F.scopes`) is tight for the walk theorems (`cex_walkCallee_F`, `cex_walkCaller_F`: a 3-scope table with a 2-cycle); a program-level witness for it is not given (unknown). The clean-scope-`0` conjunct of `ScopeTreeWF F.scopes`: unknown — no counterexample is given; `locValue_inline_calleeScope` and `locValue_inline_callerScope` are proved without it, and the proof of this theorem does not use it, but no theorem with it dropped is stated here. |
| `hscG : ScopesWF G` | the same well-formedness for the callee's scope table and scope references | tight: counterexamples `cex_scopesWFG`, `cex_scopesWFG_root` (all other hypotheses hold and the conclusion fails; witness class: `cex_scopesWFG`: a tracked callee `loc` naming missing scope 1; `cex_scopesWFG_root`: a tracked callee whose scope 0 carries `inlined` (both return modes); temp-mode part). Conjuncts: `cex_scopesWFG` breaks the `ScopeRefsBounded G` conjunct (`ScopeTreeWF G.scopes` holds, `cex_scopesWF_breaks_refs_conjunct`); `cex_scopesWFG_root` breaks the clean-scope-`0` conjunct while `ScopeParentsBelow G.scopes` and `ScopeRefsBounded G` hold. The links-point-below conjunct of `G` is tight for the walk theorem (`cex_walkCallee_Gparents`); a program-level witness is not given (unknown). |
| `hfresh : SlotsFresh cfg F G` | callee locals `1 ≤ i < G.nlocals` go to host locals `≥ F.nlocals`, a range disjoint from every declared host local | tight: counterexample `cex_slotsFresh` (all other hypotheses hold and the conclusion fails; witness class: slot range overlapping caller local 1, which is live across the call; temp-mode part) |
| `hinj : SlotsInjective cfg G` | distinct callee locals `1 ≤ i, j < G.nlocals` go to distinct host locals | tight: counterexample `cex_slotsInjective` (all other hypotheses hold and the conclusion fails; witness class: two callee arguments sharing host local 5; temp-mode part) |
| `hret : cfg.ret = .temp t` | selects the fresh-temporary treatment of the return place: the callee writes `t` and the return block moves `t` into the destination | tight: counterexample `cex_destNotReadInCleanup` (all other hypotheses hold and the conclusion fails; witness class: the destination-mode configuration `(InlineCfg.canonical 2).withDest` (`ret = .dest ≠ .temp 2`) of a caller whose cleanup reads the destination; every other temp-mode hypothesis holds for it with `t = 2`, including `TempFresh 2`) |
| `htemp : TempFresh t cfg F G` | `TempFresh t cfg F G` = `F.nlocals ≤ t` ∧ `t` differs from every callee slot `cfg.slot i` (`1 ≤ i < G.nlocals`) | tight: counterexamples `cex_tempFresh`, `cex_tempFresh_callerLocal` (all other hypotheses hold and the conclusion fails; witness class: `cex_tempFresh`: the temporary equals the argument's slot, so the callee's early write to its return place clobbers the argument; `cex_tempFresh_callerLocal`: the temporary is the caller's live local 1). Conjuncts: Each conjunct is tight on its own: `cex_tempFresh` breaks the slot-disjointness conjunct while `F.nlocals ≤ t` holds (`cex_tempFresh_breaks_slot_conjunct`); `cex_tempFresh_callerLocal` breaks `F.nlocals ≤ t` while the slot-disjointness conjunct holds. |
| `hcont : cfg.redirectContinue = true` | the callee's `continue` unwind edges get the call's own unwind action | tight: counterexample `cex_redirectContinue` (all other hypotheses hold and the conclusion fails; witness class: a callee whose inner call continues unwinding: the caller's cleanup event `out 200` is skipped; temp-mode part) |
| `hres : cfg.resumeMap = .unwind` | the callee's `resume` is rewritten by the call's unwind action, not as a jump to the normal continuation | tight: counterexample `cex_resumeMap` (all other hypotheses hold and the conclusion fails; witness class: a callee panicking into its own cleanup: after it the inlined caller returns normally; temp-mode part) |
| `hlink : cfg.link = .rustc` | the outermost callee scope's `inlinedParent` is the callsite scope if that scope carries `inlined`, else the callsite scope's own `inlinedParent` | tight: counterexample `cex_linkRule` (all other hypotheses hold and the conclusion fails; witness class: second-level inlining at a call in a nested, non-inlined scope of an inlined tracked callee inside an untracked host (location `10` becomes `20`); temp-mode part) |
| `hsub : CapsSubset G F` | every capability in the callee's list is in the caller's list, so legal `needCap`s of the callee stay legal in the host | tight: counterexample `capsSubset_needed_inlined_needCap_faults` (all other hypotheses hold and the conclusion fails; witness class: callee `[3]` using capability 3, host `[]`: the inlined `needCap 3` ends in `capFault`) |
| `hlegal : CapLegal G` | every `needCap c` in the callee names a capability in the callee's list, so the callee does not rely on a fault that the richer host would let through | tight: counterexample `cex_capLegal` (all other hypotheses hold and the conclusion fails; witness class: callee `[]` executing `needCap 3`, host `[3]`: the original ends in `capFault`, the inlined program returns normally (relies on `BehEquiv` preserving `capFault`, see non-claims)) |
| `hagree : AbiAgree p F G` | an ABI-sensitive call passes arguments the same way from host and callee (one global ABI class per list) | tight: counterexample `cex_capsAbi` (all other hypotheses hold and the conclusion fails; witness class: host list `[1]`, callee `[]` making an ABI-sensitive call, `abiC [1] ≠ abiC []`) |

**Depth.** substantive: As R2, plus capability and ABI reasoning: under `CapsSubset G F` and `CapLegal G` every `needCap` of the moved code succeeds in the host exactly when it succeeds in the callee, and under `AbiAgree p F G` every ABI-sensitive call of the moved code, and the inlined call itself, garbles its arguments in the inlined program exactly when it does in the original; proved in `lean/ToyInline/Simulation.lean`.

**Non-vacuity witness.** `nv6P`: host list `[0, 2]`, callee `[2]` using capability 2 and making an ABI-sensitive call; `abiC` agrees on both lists. (`nonvacuity_inline_capsSubset_abiAgree`)

**Non-claims.**

- `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witnesses of `BlocksBounded F` (source `ub`) and `CapLegal G` (`cex_capLegal`: source `capFault`, inlined normal return) have a source execution that a criterion treating these outcomes as undefined behaviour would not constrain. Whether these hypotheses are needed for a refinement criterion is not examined here.
- Stated for the temporary return mode (`cfg.ret = .temp t`); no destination-mode companion is established or refuted here.
- The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled.
- `inline_behEquiv_retTemp_of_capsEq` (equal lists) is not a corollary of this theorem: it does not assume `CapLegal G`.
- One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L842-851: inlining is refused when the callee's and the caller's target-feature lists differ; comment, L845-849 verbatim: "In general it is not correct to inline a callee with target features that are a / subset of the caller. This is because the callee might contain calls, and the ABI of / those calls depends on the target features of the surrounding function. By moving a / `Call` terminator from one MIR body to another with more target features, we might / change the ABI of that call!"
- LLVM llvmorg-21.1.0 (llvm/llvm-project commit 3623fe661ae35c6c80ac221f14d85be76aa870f1), llvm/lib/Target/X86/X86TargetTransformInfo.cpp L6494-6550 (`X86TTIImpl::areInlineCompatible`: equal feature sets apart from an ignore list are compatible; otherwise the callee's features must be a subset of the caller's — L6510-6511 verbatim: "If the features are a subset, we need to additionally check for calls / that may become ABI-incompatible as a result of inlining." — and each call in the callee whose argument or return types include a vector or aggregate is accepted if it is inline assembly, an intrinsic, or a direct call that `areTypesABICompatible` accepts, and rejected if it is an indirect call) and L6552-6572 (`areTypesABICompatible`: after the generic check, a caller and callee that differ in `useAVX512Regs()` are treated as compatible when no type is a vector or aggregate and as incompatible otherwise); llvm/include/llvm/Analysis/TargetTransformInfo.h L1746-1752 (L1746-1747 verbatim: "\returns True if the caller and callee agree on how \p Types will be / passed to or returned from the callee."). LLVM checks ABI compatibility per moved call and per argument type, where the toy uses one Boolean ABI class per capability list.
- rust-lang/rfcs commit f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/2396-target-feature-1.1.md L55-58, a bullet in the Motivation section describing behaviour at the time of the RFC (not a normative rule), verbatim: "* `#[target_feature]` functions are not inlined across mismatching contexts, / which can have disastrous performance implications. Currently calling / `#[target_feature]` function from all contexts looks identical which makes it / easy for users to make these mistakes (which get reported often)."

**Design question.** What must a capability guard check when moved code contains ABI-sensitive calls?

### R10. `capsSubset_guard_insufficient`, `capsSubset_guard_insufficient_witness` (impossibility)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** `capsSubset_guard_insufficient`: it is not the case that for every program, call site and configuration satisfying `IsCallSite p f b F ci G`, `LocalsBounded F`, `LocalsBounded G`, `BlocksBounded F`, `ScopesWF F`, `ScopesWF G`, `SlotsFresh cfg F G`, `SlotsInjective cfg G`, `cfg.ret = .temp t`, `TempFresh t cfg F G`, redirected `continue` edges, `resume` rewritten by the call's unwind action, the `rustc` link rule, `CapsSubset G F`, `CapLegal G` and `ci.abiSensitive = false`, the inlined program is behaviourally equivalent to the original. `capsSubset_guard_insufficient_witness` exposes the instance: in `abiP` (ABI map `abiC`) the host `capF [1]` has capability list `[1]` and the callee `abiG` has `[]`; all those hypotheses hold (canonical configuration, `t = 1`); `abiP.abi [1] ≠ abiP.abi []`; the callee's ABI-sensitive call passes `5` in the original (`run` gives `[out 5]`, `returned 0`) and `6` after inlining (`[out 6]`, `returned 0`); so `¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1))`.

**Tier.** T1: rustc's source comment states the reason informally (inline.rs L842-851); made concrete and mechanized in the toy.

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:159-167
theorem capsSubset_guard_insufficient :
    ¬ (∀ (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg)
        (t : Local),
        IsCallSite p f b F ci G → LocalsBounded F → LocalsBounded G → BlocksBounded F →
        ScopesWF F → ScopesWF G → SlotsFresh cfg F G → SlotsInjective cfg G →
        cfg.ret = .temp t → TempFresh t cfg F G → cfg.redirectContinue = true →
        cfg.resumeMap = .unwind → cfg.link = .rustc →
        CapsSubset G F → CapLegal G → ci.abiSensitive = false →
        BehEquiv p (inline p f b cfg)) := …
-- lean/ToyInline/OtherCounterexamples.lean:179-192
theorem capsSubset_guard_insufficient_witness :
    (IsCallSite abiP 0 0 (capF [1]) plainCi abiG ∧ LocalsBounded (capF [1]) ∧
      LocalsBounded abiG ∧ BlocksBounded (capF [1]) ∧ ScopesWF (capF [1]) ∧ ScopesWF abiG ∧
      SlotsFresh (InlineCfg.canonical 1) (capF [1]) abiG ∧
      SlotsInjective (InlineCfg.canonical 1) abiG ∧
      (InlineCfg.canonical 1).ret = .temp 1 ∧ TempFresh 1 (InlineCfg.canonical 1) (capF [1]) abiG ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset abiG (capF [1]) ∧ CapLegal abiG ∧ plainCi.abiSensitive = false) ∧
    (capF [1]).caps = [1] ∧ abiG.caps = [] ∧ abiP.abi [1] ≠ abiP.abi [] ∧
    run abiP 30 (init abiP e0) = ⟨[.out 5], some (.returned 0)⟩ ∧
    run (inline abiP 0 0 (InlineCfg.canonical 1)) 40
        (init (inline abiP 0 0 (InlineCfg.canonical 1)) e0) = ⟨[.out 6], some (.returned 0)⟩ ∧
    ¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1)) := …
```

**Hypothesis ledger.** None (a closed negated universal statement, together with a closed witness statement about concrete programs).

**Depth.** shallow: Instantiates the universal with the decided instance.

**Non-vacuity witness.** `capsSubset_guard_insufficient_witness` (instance `abiP`, all hypotheses of the refuted universal hold). (`capsSubset_guard_insufficient_witness`)

**Positive control.** `capsSubset_guard_positiveControl`: a nearby setting (the same call site with a capability-independent ABI map) in which every hypothesis of the ABI-agreement theorem holds and the conclusion of the refuted universal holds from every entry.

**Non-claims.**

- Escape hatches (each removes this counterexample; (a) is backed by the proved theorems it names, while (b) and (c) are not modelled here): (a) add `AbiAgree p F G` (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`), `AbiInsensitive G` (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive`) or require equal capability lists (`inline_behEquiv_retTemp_of_capsEq`); (b) change the IR so that each call carries its own ABI or feature annotation instead of inheriting the ABI class of the enclosing function's capabilities (not modelled here); (c) check ABI compatibility per call actually present in the callee and per argument type, as LLVM's `X86TTIImpl::areInlineCompatible` does, instead of one global comparison (not modelled here).
- The refuted universal is the temp-mode statement (`cfg.ret = .temp t`); the same instance also fails in destination mode (`cex_capsAbi`), but no destination-mode universal is stated here.
- Positive control: with the capability-independent ABI map of `abiPc`, the same call site satisfies every hypothesis of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`, and the inlined program is behaviourally equivalent to the original from every entry (`capsSubset_guard_positiveControl`, proved).
- The garbling `v ↦ v + 1` is a toy stand-in for a calling-convention mismatch. The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L842-851: inlining is refused when the callee's and the caller's target-feature lists differ; comment, L845-849 verbatim: "In general it is not correct to inline a callee with target features that are a / subset of the caller. This is because the callee might contain calls, and the ABI of / those calls depends on the target features of the surrounding function. By moving a / `Call` terminator from one MIR body to another with more target features, we might / change the ABI of that call!"
- LLVM llvmorg-21.1.0 (llvm/llvm-project commit 3623fe661ae35c6c80ac221f14d85be76aa870f1), llvm/lib/Target/X86/X86TargetTransformInfo.cpp L6494-6550 (`X86TTIImpl::areInlineCompatible`: equal feature sets apart from an ignore list are compatible; otherwise the callee's features must be a subset of the caller's — L6510-6511 verbatim: "If the features are a subset, we need to additionally check for calls / that may become ABI-incompatible as a result of inlining." — and each call in the callee whose argument or return types include a vector or aggregate is accepted if it is inline assembly, an intrinsic, or a direct call that `areTypesABICompatible` accepts, and rejected if it is an indirect call) and L6552-6572 (`areTypesABICompatible`: after the generic check, a caller and callee that differ in `useAVX512Regs()` are treated as compatible when no type is a vector or aggregate and as incompatible otherwise); llvm/include/llvm/Analysis/TargetTransformInfo.h L1746-1752 (L1746-1747 verbatim: "\returns True if the caller and callee agree on how \p Types will be / passed to or returned from the callee."). LLVM checks ABI compatibility per moved call and per argument type, where the toy uses one Boolean ABI class per capability list.
- rust-lang/rfcs commit f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/2396-target-feature-1.1.md L55-58, a bullet in the Motivation section describing behaviour at the time of the RFC (not a normative rule), verbatim: "* `#[target_feature]` functions are not inlined across mismatching contexts, / which can have disastrous performance implications. Currently calling / `#[target_feature]` function from all contexts looks identical which makes it / easy for users to make these mistakes (which get reported often)."

**Design question.** Is "caller ⊇ callee" enough as an inlining guard in general?

### R11. `locValue_inline_calleeScope` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For any `trackCaller` predicate `tr`, if every `inlinedParent` link of the host's scope table points to a smaller index (`ScopeParentsBelow F.scopes`), the callee's table satisfies `ScopeTreeWF` (scope `0` exists and carries neither `inlined` nor `inlinedParent`, and its links point to smaller indices), `s < G.scopes.length`, and the `rustc` link rule is used, then the caller-location value `locValue` at the shifted scope `F.scopes.length + s` of the merged table `F.scopes ++ linkScopes link F ci G`, with span `sp` and implicit location `il`, equals `locValue` at `s` in the callee's own table with implicit location `some (locValue tr F.scopes ci.scope ci.span il)` if `tr ci.callee` and `none` otherwise. (`locValue` runs the `inlinedParent` walk `walk` with fuel equal to the table length; if the walk stops at an inlined scope of an untracked callee it returns the current span, and if it reaches the end of the chain it returns the implicit location if present and the current span otherwise.)

**Tier.** T1: Makes precise why rustc's scope-link rule plus `caller_location_span` implement implicit caller locations across inlining; no earlier mechanization is known to us (no systematic search recorded).

**Statement.**

```lean
-- lean/ToyInline/Results.lean:203-209
theorem locValue_inline_calleeScope (tr : FnId → Bool) (link : LinkRule) (F : Fn)
    (ci : CallInfo) (G : Fn) (s : ScopeId) (sp : Span) (il : Option Span)
    (hF : ScopeParentsBelow F.scopes) (hG : ScopeTreeWF G.scopes) (hs : s < G.scopes.length)
    (hlink : link = .rustc) :
    locValue tr (F.scopes ++ linkScopes link F ci G) (F.scopes.length + s) sp il =
      locValue tr G.scopes s sp
        (if tr ci.callee then some (locValue tr F.scopes ci.scope ci.span il) else none) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hF : ScopeParentsBelow F.scopes` | host links point to smaller indices, so the host part of the walk ends within the host prefix and does not depend on its fuel (which grows with the table) | tight: counterexample `cex_walkCallee_F` (all other hypotheses hold and the conclusion fails; witness class: a 3-scope host table with a 2-cycle (`1 → 2 → 1`) and a 2-scope callee table) |
| `hG : ScopeTreeWF G.scopes` | the callee's scope 0 carries no `inlined` or `inlinedParent` (the link rule overwrites it) and its links point to smaller indices | tight: counterexamples `cex_walkCallee_G`, `cex_walkCallee_Gparents` (all other hypotheses hold and the conclusion fails; witness class: `cex_walkCallee_G`: a callee whose scope 0 is an inlined untracked scope; `cex_walkCallee_Gparents`: a callee table with clean scope 0 and a 2-cycle). Conjuncts: Each conjunct is tight on its own: `cex_walkCallee_G` breaks the clean-scope-`0` conjunct (links point below there); `cex_walkCallee_Gparents` breaks the links-point-below conjunct (scope 0 is clean there). |
| `hs : s < G.scopes.length` | `s` is a callee scope | tight: counterexample `cex_walkCallee_s` (all other hypotheses hold and the conclusion fails; witness class: `s = 1` for a 1-scope callee) |
| `hlink : link = .rustc` | the outermost callee scope links to the callsite scope's own `inlinedParent` when the callsite scope is not inlined | tight: counterexample `cex_walkCallee_link` (all other hypotheses hold and the conclusion fails; witness class: second-level inlining inside a nested scope of an inlined tracked callee (`linkP1`)) |

**Depth.** substantive: Strong induction on the callee scope index through three regions of the merged table, with a prefix lemma for host scopes.

**Non-vacuity witness.** `linkF1` (a host already containing an inlined tracked callee and a nested scope), `linkCi1`, `linkK`, `s = 0`. (`nonvacuity_locValue_calleeScope`)

**Non-claims.**

- Together with `locValue_inline_callerScope`, `scopesWF_inlineFn` and `localsBounded_inlineFn` this is the scope part of the inductive step for nested inlinings; the induction itself, and the whole-program statement (`inline_behEquiv_retTemp_of_capsEq`), are separate.
- `ScopeTreeWF` requires every link to point to a strictly smaller index, which is stronger than acyclicity (`scopeParentsBelow_neg`: an acyclic table with a link to a larger index is rejected). A callsite scope `ci.scope` outside the host table is treated on both sides as the end of the chain, so the answer falls back to `il.getD ci.span`.
- Closures, function-pointer and trait-object shims (Rust Reference attributes.codegen.track_caller.decay, codegen.md L1046-1050) and lexical `parent_scope` chains are not modelled. The caller-location value is a span; file/line/column structure and the Reference's statement that the information is a hint are not modelled.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1248-1268 (`visit_source_scope_data`: the outermost callee scope, recognised by `parent_scope.is_none()`, gets the callsite scope as lexical `parent_scope`, `inlined = Some((callee, callsite span))` and `inlined_parent_scope` = the callsite scope if it is inlined, else the callsite scope's own `inlined_parent_scope`; inner scopes without `inlined_parent_scope` get the mapped outermost callee scope). The toy has no lexical `parent_scope` and recognises the outermost scope by index `0`.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/mod.rs L683-715 (`Body::caller_location_span`: follow `inlined_parent_scope`; at a scope with `inlined = Some((callee, callsite_span))` return the current span if the callee does not require a caller location, otherwise replace the span by `callsite_span`; at the end return the frame's caller location if present, else the current span).
- rust-lang/rfcs commit f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/2091-inline-semantic.md, section "Propagation of tracker" (L292-310); L294-295 (verbatim): "When your `#[track_caller]` function calls another `#[track_caller]` function, the caller location / will be propagated downwards:".
- The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/attributes/codegen.md, rule attributes.codegen.track_caller.behavior, L960-966; L964-966 (verbatim): "an / implementation behaves as if it walks up the stack from `f`'s frame to find the nearest frame of an / *unattributed* function `outer`, and it returns the [`Location`] of the tracked call in `outer`." (the sentence begins on L964 with "At the point of observation, an"); L1043-1044: "This information is a hint and implementations are not required to preserve it."; L1046-1050 (attributes.codegen.track_caller.decay): coercion to a function pointer creates a shim that loses the caller location.

**Design question.** How is caller-location information preserved across multi-level inlining, through tracked and untracked wrappers?

### R12. `locValue_inline_callerScope` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For any `trackCaller` predicate `tr`, any link rule, call data `ci` and callee `G`, if every `inlinedParent` link of the host's table points to a smaller index (`ScopeParentsBelow F.scopes`) and `s < F.scopes.length`, then `locValue` at `s` in the merged table `F.scopes ++ linkScopes link F ci G` equals `locValue` at `s` in `F.scopes`, for every span `sp` and implicit location `il`.

**Tier.** T1: Companion of R11 (host part of the merged table).

**Statement.**

```lean
-- lean/ToyInline/Results.lean:225-228
theorem locValue_inline_callerScope (tr : FnId → Bool) (link : LinkRule) (F : Fn)
    (ci : CallInfo) (G : Fn) (s : ScopeId) (sp : Span) (il : Option Span)
    (hF : ScopeParentsBelow F.scopes) (hs : s < F.scopes.length) :
    locValue tr (F.scopes ++ linkScopes link F ci G) s sp il = locValue tr F.scopes s sp il := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hF : ScopeParentsBelow F.scopes` | host links point to smaller indices (the walk's fuel grows with the table) | tight: counterexample `cex_walkCaller_F` (all other hypotheses hold and the conclusion fails; witness class: a host table with a 2-cycle) |
| `hs : s < F.scopes.length` | `s` is a host scope | tight: counterexample `cex_walkCaller_s` (all other hypotheses hold and the conclusion fails; witness class: `s` equal to the host table's length (the appended callee scope 0)) |

**Depth.** shallow: Host chains stay inside the host prefix (one prefix lemma).

**Non-vacuity witness.** `linkF1`, scope 2. (`nonvacuity_locValue_callerScope`)

**Non-claims.**

- Holds for every `LinkRule`, including the wrong `LinkRule.ignoreParent`, so it does not validate the scope-link rule (that is `locValue_inline_calleeScope` with `hlink`).
- The hypothesis `s < F.scopes.length` restricts the statement to host scopes; for `s` at or beyond the host table the value can change (`cex_walkCaller_s`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/mod.rs L683-715 (`Body::caller_location_span`: follow `inlined_parent_scope`; at a scope with `inlined = Some((callee, callsite_span))` return the current span if the callee does not require a caller location, otherwise replace the span by `callsite_span`; at the end return the frame's caller location if present, else the current span).

**Design question.** Does inlining disturb caller-location values of the host's own code?

### R13. `scopesWF_inlineFn` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For any configuration `cfg` and any call data `ci`: if block `b` of `F` is `B`, `F` satisfies `ScopesWF` (clean scope `0`, links pointing to smaller indices, scope references in range), every `inlinedParent` link of the callee's table points to a smaller index (`ScopeParentsBelow G.scopes`) and the callee's scope references are in range (`ScopeRefsBounded G`), then `inlineFn F b B ci G cfg` satisfies `ScopesWF`.

**Tier.** T1: Bookkeeping lemma making R11 iterable; folklore made precise.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:239-242
theorem scopesWF_inlineFn (F : Fn) (b : BlockId) (B : Block) (ci : CallInfo) (G : Fn)
    (cfg : InlineCfg) (hB : nth? F.blocks b = some B) (hF : ScopesWF F)
    (hGpb : ScopeParentsBelow G.scopes) (hGref : ScopeRefsBounded G) :
    ScopesWF (inlineFn F b B ci G cfg) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hB : nth? F.blocks b = some B` | the call block passed in is the host's block `b` | tight: counterexample `cex_scopesWF_B` (all other hypotheses hold and the conclusion fails; witness class: a block naming a missing scope passed in place of block 0) |
| `hF : ScopesWF F` | host well-formedness (the merged table starts with the host table) | tight: counterexamples `cex_scopesWF_F`, `cex_scopesWF_Froot`, `cex_scopesWF_Fparents` (all other hypotheses hold and the conclusion fails; witness class: `cex_scopesWF_F`: a host `loc` naming a missing scope; `cex_scopesWF_Froot`: a host whose scope 0 carries `inlined`; `cex_scopesWF_Fparents`: a host scope linking to itself). Conjuncts: Each of the three conjuncts is tight on its own: `cex_scopesWF_F` breaks `ScopeRefsBounded F`, `cex_scopesWF_Froot` the clean-scope-`0` conjunct, `cex_scopesWF_Fparents` the links-point-below conjunct, each with the other two holding. |
| `hGpb : ScopeParentsBelow G.scopes` | shifted callee links stay below their (shifted) scope | tight: counterexample `cex_scopesWF_Gparents` (all other hypotheses hold and the conclusion fails; witness class: a callee scope linking to itself) |
| `hGref : ScopeRefsBounded G` | shifted callee scope references stay in range | tight: counterexample `cex_scopesWF_G` (all other hypotheses hold and the conclusion fails; witness class: a callee `loc` naming a missing scope) |

**Depth.** shallow: Index arithmetic on the appended table and case analysis on the spliced blocks.

**Non-vacuity witness.** `linkF`, its block 0, `linkCi0`, `linkG`. (`nonvacuity_scopesWF_inlineFn`)

**Non-claims.**

- Holds for every `cfg` (including the wrong `LinkRule.ignoreParent`, a wrong `resumeMap` or overlapping slots) and for any `ci` (not required to be `B`'s call), so `ScopesWF` preservation does not validate the semantic correctness of scope linking or of the splice.
- The callee's scope 0 need not be clean (`linkScope` overwrites it); `ScopesWF G`, as assumed by the inlining theorems, implies both callee hypotheses.
- Of the other hypotheses that the inlining theorems assume and that a further inlining step would have to re-establish, `LocalsBounded` preservation is proved (`localsBounded_inlineFn`) and `BlocksBounded` preservation fails when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` preservation is not examined.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1248-1268 (`visit_source_scope_data`: the outermost callee scope, recognised by `parent_scope.is_none()`, gets the callsite scope as lexical `parent_scope`, `inlined = Some((callee, callsite span))` and `inlined_parent_scope` = the callsite scope if it is inlined, else the callsite scope's own `inlined_parent_scope`; inner scopes without `inlined_parent_scope` get the mapped outermost callee scope). The toy has no lexical `parent_scope` and recognises the outermost scope by index `0`.

**Design question.** Does the scope-link rule keep scope tables well formed under repeated inlining?

### R14. `innermost_policy_wrong_for_tracked_chain` (counterexample)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For tracked `k` called (span `20`) by tracked `g` called (span `10`) by untracked `f` (`chainP true`), and `chainQ true` obtained by inlining `g` into `f` and then the copied call to `k`: `runWith pol (chainP true)` with step budget 30 (at most 30 steps) from `e0` gives `[loc 10]` and `returned 0` for every policy `pol` (`.walk`, `.innermost`, `.outermost`); `run` (the scope walk) of `chainQ true` with step budget 40 (at most 40 steps) gives `[loc 10]`, `returned 0`, and `BehEquivAt (chainP true) (chainQ true) e0`; the innermost-span policy on `chainQ true` gives `[loc 20]`, `returned 0`, so `chainP true` and `chainQ true` are not behaviourally equivalent from `e0` under `.innermost`.

**Tier.** T1: A concrete mechanized witness against a naive caller-location policy.

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:237-244
theorem innermost_policy_wrong_for_tracked_chain :
    (∀ pol : LocPolicy, runWith pol (chainP true) 30 (init (chainP true) e0) =
        ⟨[.loc 10], some (.returned 0)⟩) ∧
      run (chainQ true) 40 (init (chainQ true) e0) = ⟨[.loc 10], some (.returned 0)⟩ ∧
      runWith .innermost (chainQ true) 40 (init (chainQ true) e0) =
        ⟨[.loc 20], some (.returned 0)⟩ ∧
      BehEquivAt (chainP true) (chainQ true) e0 ∧
      ¬ BehEquivAtWith .innermost (chainP true) (chainQ true) e0 := …
```

**Hypothesis ledger.** None (a closed statement about concrete programs).

**Depth.** shallow: Decided by evaluation.

**Non-vacuity witness.** The theorem is itself the instance. (`innermost_policy_wrong_for_tracked_chain`)

**Non-claims.**

- Refutes `.innermost` on one two-level tracked-chain instance from one entry. It does not show that `.walk` is the only policy that preserves behaviour, and it does not show that `.innermost` fails for single-level inlining into an untracked host (not examined here).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rfcs commit f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/2091-inline-semantic.md, section "Propagation of tracker" (L292-310); L294-295 (verbatim): "When your `#[track_caller]` function calls another `#[track_caller]` function, the caller location / will be propagated downwards:".
- The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/attributes/codegen.md, rule attributes.codegen.track_caller.behavior, L960-966; L964-966 (verbatim): "an / implementation behaves as if it walks up the stack from `f`'s frame to find the nearest frame of an / *unattributed* function `outer`, and it returns the [`Location`] of the tracked call in `outer`." (the sentence begins on L964 with "At the point of observation, an"); L1043-1044: "This information is a hint and implementations are not required to preserve it."; L1046-1050 (attributes.codegen.track_caller.decay): coercion to a function pointer creates a shim that loses the caller location.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/mod.rs L683-715 (`Body::caller_location_span`: follow `inlined_parent_scope`; at a scope with `inlined = Some((callee, callsite_span))` return the current span if the callee does not require a caller location, otherwise replace the span by `callsite_span`; at the end return the frame's caller location if present, else the current span).

**Design question.** Which caller-location computation is correct after inlining tracked chains?

### R15. `outermost_policy_wrong_for_untracked_wrapper` (counterexample)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For tracked `k` called (span `20`) by an untracked wrapper `g` called (span `10`) by `f` (`chainP false`), and `chainQ false` obtained by inlining both calls: `runWith pol (chainP false)` with step budget 30 (at most 30 steps) from `e0` gives `[loc 20]` and `returned 0` for every policy `pol`; `run` of `chainQ false` with step budget 40 (at most 40 steps) gives `[loc 20]`, `returned 0`, and `BehEquivAt (chainP false) (chainQ false) e0`; the outermost-span policy on `chainQ false` gives `[loc 10]`, `returned 0`, so the two programs are not behaviourally equivalent from `e0` under `.outermost`.

**Tier.** T1: A concrete mechanized witness against a naive caller-location policy.

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:254-261
theorem outermost_policy_wrong_for_untracked_wrapper :
    (∀ pol : LocPolicy, runWith pol (chainP false) 30 (init (chainP false) e0) =
        ⟨[.loc 20], some (.returned 0)⟩) ∧
      run (chainQ false) 40 (init (chainQ false) e0) = ⟨[.loc 20], some (.returned 0)⟩ ∧
      runWith .outermost (chainQ false) 40 (init (chainQ false) e0) =
        ⟨[.loc 10], some (.returned 0)⟩ ∧
      BehEquivAt (chainP false) (chainQ false) e0 ∧
      ¬ BehEquivAtWith .outermost (chainP false) (chainQ false) e0 := …
```

**Hypothesis ledger.** None (a closed statement about concrete programs).

**Depth.** shallow: Decided by evaluation.

**Non-vacuity witness.** The theorem is itself the instance. (`outermost_policy_wrong_for_untracked_wrapper`)

**Non-claims.**

- Refutes `.outermost` on one two-level instance with an untracked wrapper, from one entry. It does not show that `.walk` is the only policy that preserves behaviour, and it does not show that `.outermost` fails when every intermediate inlined callee is tracked (not examined here).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/attributes/codegen.md, rule attributes.codegen.track_caller.behavior, L960-966; L964-966 (verbatim): "an / implementation behaves as if it walks up the stack from `f`'s frame to find the nearest frame of an / *unattributed* function `outer`, and it returns the [`Location`] of the tracked call in `outer`." (the sentence begins on L964 with "At the point of observation, an"); L1043-1044: "This information is a hint and implementations are not required to preserve it."; L1046-1050 (attributes.codegen.track_caller.decay): coercion to a function pointer creates a shim that loses the caller location.
- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/mod.rs L683-715 (`Body::caller_location_span`: follow `inlined_parent_scope`; at a scope with `inlined = Some((callee, callsite_span))` return the current span if the callee does not require a caller location, otherwise replace the span by `callsite_span`; at the end return the frame's caller location if present, else the current span).

**Design question.** Which caller-location computation is correct after inlining through untracked wrappers?

### R16. `linkRule_ignoreParent_changes_location` (counterexample)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** In `linkP1`, the host `linkF1` already contains the inlined body of the tracked `linkG` (called from the untracked host with span `10`); its block `3` holds the copied call `linkCi1` to the tracked `linkK`, issued from a nested, non-inlined scope of the inlined callee with span `20`. With `linkCfg` (the canonical configuration for 2 host locals except `link = .ignoreParent`, the variant that sets the outermost callee scope's `inlinedParent` to none when the callsite scope is not inlined), every hypothesis of `inline_behEquiv_retTemp_of_capsEq` other than `hlink` holds (`t = 2`), and `CleanupClosed linkF1` and `DestNotReadInCleanup linkF1 linkCi1.dest` hold. `run` of `linkP1` from `e0` gives `[loc 10]`, `returned 0`; `run` of the inlined program with `linkCfg` and with `linkCfg.withDest` gives `[loc 20]`, `returned 0`; neither inlined program is behaviourally equivalent to `linkP1`.

**Tier.** T1: Determines which link variant breaks, with a concrete mechanized witness.

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:510-524
theorem linkRule_ignoreParent_changes_location :
    (IsCallSite linkP1 0 3 linkF1 linkCi1 linkK ∧ LocalsBounded linkF1 ∧ LocalsBounded linkK ∧
      BlocksBounded linkF1 ∧ ScopesWF linkF1 ∧ ScopesWF linkK ∧
      SlotsFresh linkCfg linkF1 linkK ∧ SlotsInjective linkCfg linkK ∧
      linkCfg.ret = .temp 2 ∧ TempFresh 2 linkCfg linkF1 linkK ∧
      linkCfg.redirectContinue = true ∧ linkCfg.resumeMap = .unwind ∧
      linkF1.caps = linkK.caps ∧ CleanupClosed linkF1 ∧ DestNotReadInCleanup linkF1 linkCi1.dest ∧
      linkCfg.link = .ignoreParent) ∧
    run linkP1 40 (init linkP1 e0) = ⟨[.loc 10], some (.returned 0)⟩ ∧
    run (inline linkP1 0 3 linkCfg) 60 (init (inline linkP1 0 3 linkCfg) e0) =
      ⟨[.loc 20], some (.returned 0)⟩ ∧
    run (inline linkP1 0 3 linkCfg.withDest) 60 (init (inline linkP1 0 3 linkCfg.withDest) e0) =
      ⟨[.loc 20], some (.returned 0)⟩ ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg) ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg.withDest) := …
```

**Hypothesis ledger.** None (a closed statement about concrete programs).

**Depth.** shallow: Decided by evaluation.

**Non-vacuity witness.** The theorem is itself the instance. (`linkRule_ignoreParent_changes_location`)

**Non-claims.**

- Varies only the branch of `linkScope` for the outermost callee scope (`j = 0`) when the callsite scope is not inlined; the branch for an inlined callsite scope (`c.inlined.isSome`) and the rule linking inner callee scopes without `inlinedParent` to the outermost callee scope (`none => some ns`) are not varied here.
- `linkP1 = inlineCanon linkP0 0 0` (`linkP1_eq`). The walk-level form of the same failure is `cex_walkCallee_link`.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_mir_transform/src/inline.rs L1248-1268 (`visit_source_scope_data`: the outermost callee scope, recognised by `parent_scope.is_none()`, gets the callsite scope as lexical `parent_scope`, `inlined = Some((callee, callsite span))` and `inlined_parent_scope` = the callsite scope if it is inlined, else the callsite scope's own `inlined_parent_scope`; inner scopes without `inlined_parent_scope` get the mapped outermost callee scope). The toy has no lexical `parent_scope` and recognises the outermost scope by index `0`.

**Design question.** Which part of the scope-link rule is needed for nested inlining?

### R17. `behEquiv_trans` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** If `BehEquiv p q` and `BehEquiv q r` (behavioural equivalence from every entry), then `BehEquiv p r`.

**Tier.** T0: Transitivity of behavioural equivalence (cf. composition of verified passes, Leroy 2009, Section 2.3); a structural reference point.

**Statement.**

```lean
-- lean/ToyInline/Results.lean:373-374
theorem behEquiv_trans {p q r : Program} (h₁ : BehEquiv p q) (h₂ : BehEquiv q r) :
    BehEquiv p r := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h₁ : BehEquiv p q` | first step | tight: counterexample `cex_trans_left` (all other hypotheses hold and the conclusion fails; witness class: one-block returning versus panicking programs) |
| `h₂ : BehEquiv q r` | second step | tight: counterexample `cex_trans_right` (all other hypotheses hold and the conclusion fails; witness class: one-block returning versus panicking programs) |

**Depth.** definitional: Composition of prefix witnesses (`Obs.Prefix.trans`).

**Non-vacuity witness.** Three pairwise distinct programs: `pMissing`, `pUnr`, `pGotoUnr`, with `BehEquiv pMissing pUnr` and `BehEquiv pUnr pGotoUnr`. (`nonvacuity_behEquiv_trans`)

**Non-claims.**

- A structural reference point: it composes equivalences but does not mention `inline`. It does not re-establish the hypotheses of the inlining theorems on an intermediate program; for that, `scopesWF_inlineFn` and `localsBounded_inlineFn` are proved, `BlocksBounded` can fail (`cex_blocksBounded_inlineFn_oob`), and the remaining hypotheses must be checked on each intermediate program.
- Says nothing about whether different inlining orders produce the same program; in this toy they need not (`inline_order_changes_body`), and whether they agree up to renaming of locals, blocks and scopes is unknown.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- Xavier Leroy, "A formally verified compiler back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137), Section 2.3 ("Composition of compilation passes": verified passes compose when the semantic preservation property is transitive).
- Martin Desharnais, "A Generic Framework for Verified Compilers", Archive of Formal Proofs, February 2020, https://isa-afp.org/entries/VeriComp.html (Isabelle/HOL locales for simulations and their composition).

**Design question.** Reference point: do behaviour-preserving inlining steps compose?

### R18. `inline_order_changes_body` (counterexample)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** With the canonical configuration, in `ordP` (`h` calls `f`, `f` calls `g`): inlining `g` into `f` and then the new `f` into `h` (`ordQ1`) gives function `0` (`h`) a body with 11 statements; inlining `f` into `h` and then `g` into the copied call (`ordQ2`) gives 9 statements; so the two bodies of `h` differ; from the entry `e0 = ⟨0, [], 0⟩` both programs are behaviourally equivalent to `ordP`.

**Tier.** T1: That the result of successive inlining steps depends on their order is informal common knowledge about inliners; here a mechanized instance in this toy's conventions (a reference point).

**Statement.**

```lean
-- lean/ToyInline/OtherCounterexamples.lean:455-458
theorem inline_order_changes_body :
    (nth? ordQ1.fns 0).map Fn.totalStmts = some 11 ∧ (nth? ordQ2.fns 0).map Fn.totalStmts = some 9 ∧
      nth? ordQ1.fns 0 ≠ nth? ordQ2.fns 0 ∧
      BehEquivAt ordP ordQ1 e0 ∧ BehEquivAt ordP ordQ2 e0 := …
```

**Hypothesis ledger.** None (a closed statement about concrete programs).

**Depth.** shallow: Decided by evaluation.

**Non-vacuity witness.** The theorem is itself the instance. (`inline_order_changes_body`)

**Non-claims.**

- A reference point about this toy's conventions: the difference comes from the prologue zero-initialising every callee local (the first order initialises the inner callee's slots twice); it is not a statement about any real inliner.
- Compares function `0` (`h`) only; `ordQ1` also replaces `f` (function `1`) while `ordQ2` leaves it unchanged (`inline_order_other_fns`). Behavioural equivalence is shown from the single entry `e0`, not from every entry.
- Equality up to renaming and dead-statement removal is not examined (unknown).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- Simon Peyton Jones and Simon Marlow, "Secrets of the Glasgow Haskell Compiler inliner", Journal of Functional Programming 12(4–5):393–434, 2002, doi:10.1017/S0956796802004331 (design of a production inliner; a bibliographic pointer, not relied on for any statement of this card).

**Design question.** Reference point: should a verified inliner's composition property be stated up to behaviour rather than syntax?

### R19. `localsBounded_inlineFn` (theorem)

**Status.** proved.

Basis: execution (Lean kernel check)

**Plain claim.** For any configuration `cfg`: if block `b` of `F` is `B`, `B` ends in the call `ci` (`B.term = .call ci`), and `F` and `G` satisfy `LocalsBounded`, then the new body `inlineFn F b B ci G cfg` satisfies `LocalsBounded`. Its declared-local count is `max (max F.nlocals (maxSucc (cfg.rename ci.dest) G.nlocals)) (retTempSucc cfg)`, which also covers the return temporary when the callee declares no locals.

**Tier.** T1: Bookkeeping lemma making the inlining theorems iterable with respect to `LocalsBounded`; folklore made precise.

**Statement.**

```lean
-- lean/ToyInline/Preservation.lean:46-49
theorem localsBounded_inlineFn (F : Fn) (b : BlockId) (B : Block) (ci : CallInfo) (G : Fn)
    (cfg : InlineCfg) (hB : nth? F.blocks b = some B) (hterm : B.term = .call ci)
    (hF : LocalsBounded F) (hG : LocalsBounded G) :
    LocalsBounded (inlineFn F b B ci G cfg) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hB : nth? F.blocks b = some B` | the call block passed in is the host's block `b` | tight: counterexample `cex_localsBoundedInline_B` (all other hypotheses hold and the conclusion fails; witness class: a block mentioning `var 9` passed in place of block 0) |
| `hterm : B.term = .call ci` | the call's destination and arguments, which the return block and prologue mention, are locals of `B` | tight: counterexample `cex_localsBoundedInline_term` (all other hypotheses hold and the conclusion fails; witness class: block 0 ends in `goto 0` while `ci` has destination 7, which the return block writes) |
| `hF : LocalsBounded F` | host blocks are kept | tight: counterexample `cex_localsBoundedInline_F` (all other hypotheses hold and the conclusion fails; witness class: a host block mentioning `var 3` with one declared local) |
| `hG : LocalsBounded G` | renamed callee locals stay below the new count | tight: counterexample `cex_localsBoundedInline_G` (all other hypotheses hold and the conclusion fails; witness class: a callee mentioning `var 5` with one declared local (renamed to host local 6)) |

**Depth.** shallow: Case analysis on the spliced blocks with a bound for `maxSucc`.

**Non-vacuity witness.** `linkF`, its block 0 (ending in `linkCi0`), `linkG`. (`nonvacuity_localsBounded_inlineFn`)

**Non-claims.**

- Says nothing about behaviour; it is one of the side conditions for applying the inlining theorems again. `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`).
- Holds for every configuration `cfg`, including slot maps that are not fresh or not injective (`SlotsFresh`, `SlotsInjective` are not assumed) and the wrong rewriting variants, so it does not validate the renaming. In temp mode (`cfg.ret = .temp t`) the declared-local count includes `t + 1` (`retTempSucc cfg`) even when `ci.target = none`, where `inlineFn` adds no return block and nothing reads the temporary; the count is an upper bound, not the least bound.
- `inlineFn_nlocals_covers_retTemp` checks the edge case of a callee with no locals in temp mode (new count `2` for one host local).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

**Prior art.**

- CompCert v3.18 (AbsInt/CompCert commit 14d616046360a0b2611ebdfc2f98368af402e1f7), backend/Inlining.v L166-186 (`Record context`: a source instruction at PC `n` is relocated to `n + ctx.(dpc)`, pseudo-registers are shifted by `ctx.(dreg)`, and "return" instructions become "return" or "move" instructions as governed by `ctx.(retinfo)`) and backend/Inliningproof.v L1297-1305 (`Theorem transf_program_correct: forward_simulation (semantics prog) (semantics tprog).`). RTL has no unwinding, cleanup blocks, capability guards or caller-location scopes.

**Design question.** Does one inlining step keep bodies free of undeclared locals, so that inlining can be iterated?

### Declarations cited by name

Every package-local declaration named in this document or in `results.json` and not quoted above, grouped by file.

#### `lean/ToyInline/Build.lean`

```lean
-- lean/ToyInline/Build.lean:30-37
def cfgWith (hostN : Nat) (slot : Option (Nat → Local) := none) (ret : Option RetMode := none)
    (redirect : Bool := true) (rm : ResumeMap := .unwind) (link : LinkRule := .rustc) :
    InlineCfg where
  slot := slot.getD (fun i => hostN + i)
  ret := ret.getD (.temp hostN)
  redirectContinue := redirect
  resumeMap := rm
  link := link
```

#### `lean/ToyInline/Preservation.lean`

```lean
-- lean/ToyInline/Preservation.lean:26
theorem lt_maxSucc (ρ : Nat → Local) (n i : Nat) (hi : i < n) : ρ i < maxSucc ρ n := …
```

#### `lean/ToyInline/Instances.lean`

```lean
-- lean/ToyInline/Instances.lean:14
def abiC (s : CapSet) : Bool := s.contains 1
```

```lean
-- lean/ToyInline/Instances.lean:20-22
def gP : Fn := mkFn 2 [blk [] (.branch (.var 1) 1 2), blk [] (.panic (.cleanup 3)),
  blk [.emit (.var 1), .assign 0 (.add (.var 1) (.const 1))] .ret,
  blk [.emit (.const 100)] .resume true]
```

```lean
-- lean/ToyInline/Instances.lean:26-27
def fP : Fn := mkFn 2 [blk [] (mkCall 1 [.var 1] 1 (some 1) (.cleanup 2)),
  blk [.emit (.var 1)] .ret, blk [.emit (.const 200)] .resume true]
```

```lean
-- lean/ToyInline/Instances.lean:29
def ciP : CallInfo := mkCallInfo 1 [.var 1] 1 (some 1) (.cleanup 2)
```

```lean
-- lean/ToyInline/Instances.lean:30
def progP : Program := mkProg [fP, gP]
```

```lean
-- lean/ToyInline/Instances.lean:31
def cfgP : InlineCfg := InlineCfg.canonical 2
```

```lean
-- lean/ToyInline/Instances.lean:32
def cfgPd : InlineCfg := { cfgP with ret := .dest }
```

```lean
-- lean/ToyInline/Instances.lean:53-54
def freshF : Fn := mkFn 2 [blk [.assign 1 (.use (.const 5))]
  (mkCall 1 [.const 9] 0 (some 1) .continue), blk [.emit (.var 1)] .ret]
```

```lean
-- lean/ToyInline/Instances.lean:75
def tempCfg : InlineCfg := cfgWith 1 (slot := some (fun i => 1 + i)) (ret := some (.temp 2))
```

```lean
-- lean/ToyInline/Instances.lean:99
def plainCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue
```

```lean
-- lean/ToyInline/Instances.lean:113
def emptyF : Fn := mkFn 0 []
```

```lean
-- lean/ToyInline/Instances.lean:118
def linkF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 10)), blk [] .ret]
```

```lean
-- lean/ToyInline/Instances.lean:120-121
def linkG : Fn := mkFn 1 [blk [] (mkCall 2 [] 0 (some 1) .continue (span := 20) (scope := 1)),
  blk [] .ret] (tc := true) (scopes := [⟨none, none⟩, ⟨none, none⟩])
```

```lean
-- lean/ToyInline/Instances.lean:123
def linkK : Fn := mkFn 1 [blk [.loc 30 0] .ret] (tc := true)
```

```lean
-- lean/ToyInline/Instances.lean:124
def linkP0 : Program := mkProg [linkF, linkG, linkK]
```

```lean
-- lean/ToyInline/Instances.lean:125
def linkCi0 : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue (span := 10)
```

```lean
-- lean/ToyInline/Instances.lean:127
def linkF1 : Fn := inlineFn linkF 0 (blk [] (.call linkCi0)) linkCi0 linkG (InlineCfg.canonical 1)
```

```lean
-- lean/ToyInline/Instances.lean:128
def linkP1 : Program := mkProg [linkF1, linkG, linkK]
```

```lean
-- lean/ToyInline/Instances.lean:130
def linkCi1 : CallInfo := mkCallInfo 2 [] 1 (some 4) .continue (span := 20) (scope := 2)
```

```lean
-- lean/ToyInline/Instances.lean:131
def linkCfg : InlineCfg := cfgWith 2 (link := .ignoreParent)
```

```lean
-- lean/ToyInline/Instances.lean:133
theorem linkP1_eq : inlineCanon linkP0 0 0 = linkP1 := …
```

```lean
-- lean/ToyInline/Instances.lean:137-138
def capF (caps : CapSet) : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue),
  blk [] .ret] (caps := caps)
```

```lean
-- lean/ToyInline/Instances.lean:141-142
def abiG : Fn := mkFn 1 [blk [] (mkCall 2 [.const 5] 0 (some 1) .continue (abiSens := true)),
  blk [] .ret]
```

```lean
-- lean/ToyInline/Instances.lean:143
def abiK : Fn := mkFn 2 [blk [.emit (.var 1)] .ret]
```

```lean
-- lean/ToyInline/Instances.lean:144
def abiP : Program := mkProg [capF [1], abiG, abiK] (abi := abiC)
```

```lean
-- lean/ToyInline/Instances.lean:146
def abiPc : Program := mkProg [capF [1], abiG, abiK] (abi := fun _ => false)
```

```lean
-- lean/ToyInline/Instances.lean:149
def needG : Fn := mkFn 1 [blk [.needCap 3, .emit (.const 1)] .ret] (caps := [3])
```

```lean
-- lean/ToyInline/Instances.lean:150
def needP : Program := mkProg [capF [], needG] (abi := abiC)
```

```lean
-- lean/ToyInline/Instances.lean:180
def chainF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 10)), blk [] .ret]
```

```lean
-- lean/ToyInline/Instances.lean:181-182
def chainG (tc : Bool) : Fn :=
  mkFn 1 [blk [] (mkCall 2 [] 0 (some 1) .continue (span := 20)), blk [] .ret] (tc := tc)
```

```lean
-- lean/ToyInline/Instances.lean:183
def chainK : Fn := mkFn 1 [blk [.loc 30 0] .ret] (tc := true)
```

```lean
-- lean/ToyInline/Instances.lean:186
def chainP (tc : Bool) : Program := mkProg [chainF, chainG tc, chainK]
```

```lean
-- lean/ToyInline/Instances.lean:188
def chainQ (tc : Bool) : Program := inlineCanon (inlineCanon (chainP tc) 0 0) 0 3
```

#### `lean/ToyInline/Counterexamples.lean`

```lean
-- lean/ToyInline/Counterexamples.lean:24-53
theorem cex_isCallSite :
    (¬ (IsCallSite freshP 0 0 emptyF freshCi freshG) ∧
    LocalsBounded emptyF ∧
    LocalsBounded freshG ∧
    BlocksBounded emptyF ∧
    ScopesWF emptyF ∧
    ScopesWF freshG ∧
    SlotsFresh freshCfg emptyF freshG ∧
    SlotsInjective freshCfg freshG ∧
    freshCfg.ret = .temp 2 ∧
    TempFresh 2 freshCfg emptyF freshG ∧
    freshCfg.redirectContinue = true ∧
    freshCfg.resumeMap = .unwind ∧
    freshCfg.link = .rustc ∧
    emptyF.caps = freshG.caps ∧
    CapsSubset freshG emptyF ∧
    CapLegal freshG ∧
    AbiInsensitive freshG ∧
    freshCi.abiSensitive = false ∧
    AbiAgree freshP emptyF freshG ∧
    SlotsFresh freshCfg.withDest emptyF freshG ∧
    SlotsInjective freshCfg.withDest freshG ∧
    freshCfg.withDest.ret = .dest ∧
    freshCfg.withDest.redirectContinue = true ∧
    freshCfg.withDest.resumeMap = .unwind ∧
    freshCfg.withDest.link = .rustc ∧
    CleanupClosed emptyF ∧
    DestNotReadInCleanup emptyF freshCi.dest) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:57-86
theorem cex_localsBoundedF :
    (IsCallSite locFP 0 0 locFF locFCi locFG ∧
    ¬ (LocalsBounded locFF) ∧
    LocalsBounded locFG ∧
    BlocksBounded locFF ∧
    ScopesWF locFF ∧
    ScopesWF locFG ∧
    SlotsFresh locFCfg locFF locFG ∧
    SlotsInjective locFCfg locFG ∧
    locFCfg.ret = .temp 2 ∧
    TempFresh 2 locFCfg locFF locFG ∧
    locFCfg.redirectContinue = true ∧
    locFCfg.resumeMap = .unwind ∧
    locFCfg.link = .rustc ∧
    locFF.caps = locFG.caps ∧
    CapsSubset locFG locFF ∧
    CapLegal locFG ∧
    AbiInsensitive locFG ∧
    locFCi.abiSensitive = false ∧
    AbiAgree locFP locFF locFG ∧
    SlotsFresh locFCfg.withDest locFF locFG ∧
    SlotsInjective locFCfg.withDest locFG ∧
    locFCfg.withDest.ret = .dest ∧
    locFCfg.withDest.redirectContinue = true ∧
    locFCfg.withDest.resumeMap = .unwind ∧
    locFCfg.withDest.link = .rustc ∧
    CleanupClosed locFF ∧
    DestNotReadInCleanup locFF locFCi.dest) ∧
    ¬ BehEquiv locFP (inline locFP 0 0 locFCfg) ∧
    ¬ BehEquiv locFP (inline locFP 0 0 locFCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:90-119
theorem cex_localsBoundedG :
    (IsCallSite locGP 0 0 locGF locGCi locGG ∧
    LocalsBounded locGF ∧
    ¬ (LocalsBounded locGG) ∧
    BlocksBounded locGF ∧
    ScopesWF locGF ∧
    ScopesWF locGG ∧
    SlotsFresh (InlineCfg.canonical 1) locGF locGG ∧
    SlotsInjective (InlineCfg.canonical 1) locGG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) locGF locGG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    locGF.caps = locGG.caps ∧
    CapsSubset locGG locGF ∧
    CapLegal locGG ∧
    AbiInsensitive locGG ∧
    locGCi.abiSensitive = false ∧
    AbiAgree locGP locGF locGG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest locGF locGG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest locGG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed locGF ∧
    DestNotReadInCleanup locGF locGCi.dest) ∧
    ¬ BehEquiv locGP (inline locGP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv locGP (inline locGP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:123-152
theorem cex_blocksBoundedF :
    (IsCallSite blkFP 0 0 blkFF blkFCi blkFG ∧
    LocalsBounded blkFF ∧
    LocalsBounded blkFG ∧
    ¬ (BlocksBounded blkFF) ∧
    ScopesWF blkFF ∧
    ScopesWF blkFG ∧
    SlotsFresh (InlineCfg.canonical 1) blkFF blkFG ∧
    SlotsInjective (InlineCfg.canonical 1) blkFG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) blkFF blkFG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    blkFF.caps = blkFG.caps ∧
    CapsSubset blkFG blkFF ∧
    CapLegal blkFG ∧
    AbiInsensitive blkFG ∧
    blkFCi.abiSensitive = false ∧
    AbiAgree blkFP blkFF blkFG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest blkFF blkFG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest blkFG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed blkFF ∧
    DestNotReadInCleanup blkFF blkFCi.dest) ∧
    ¬ BehEquiv blkFP (inline blkFP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv blkFP (inline blkFP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:156-185
theorem cex_scopesWFF :
    (IsCallSite scFP 0 0 scFF spanCi scFG ∧
    LocalsBounded scFF ∧
    LocalsBounded scFG ∧
    BlocksBounded scFF ∧
    ¬ (ScopesWF scFF) ∧
    ScopesWF scFG ∧
    SlotsFresh (InlineCfg.canonical 1) scFF scFG ∧
    SlotsInjective (InlineCfg.canonical 1) scFG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) scFF scFG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    scFF.caps = scFG.caps ∧
    CapsSubset scFG scFF ∧
    CapLegal scFG ∧
    AbiInsensitive scFG ∧
    spanCi.abiSensitive = false ∧
    AbiAgree scFP scFF scFG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest scFF scFG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest scFG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed scFF ∧
    DestNotReadInCleanup scFF spanCi.dest) ∧
    ¬ BehEquiv scFP (inline scFP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv scFP (inline scFP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:189-218
theorem cex_scopesWFG :
    (IsCallSite scGP 0 0 scGF spanCi scGG ∧
    LocalsBounded scGF ∧
    LocalsBounded scGG ∧
    BlocksBounded scGF ∧
    ScopesWF scGF ∧
    ¬ (ScopesWF scGG) ∧
    SlotsFresh (InlineCfg.canonical 1) scGF scGG ∧
    SlotsInjective (InlineCfg.canonical 1) scGG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) scGF scGG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    scGF.caps = scGG.caps ∧
    CapsSubset scGG scGF ∧
    CapLegal scGG ∧
    AbiInsensitive scGG ∧
    spanCi.abiSensitive = false ∧
    AbiAgree scGP scGF scGG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest scGF scGG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest scGG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed scGF ∧
    DestNotReadInCleanup scGF spanCi.dest) ∧
    ¬ BehEquiv scGP (inline scGP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv scGP (inline scGP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:222-251
theorem cex_slotsFresh :
    (IsCallSite freshP 0 0 freshF freshCi freshG ∧
    LocalsBounded freshF ∧
    LocalsBounded freshG ∧
    BlocksBounded freshF ∧
    ScopesWF freshF ∧
    ScopesWF freshG ∧
    ¬ (SlotsFresh freshCfg freshF freshG) ∧
    SlotsInjective freshCfg freshG ∧
    freshCfg.ret = .temp 2 ∧
    TempFresh 2 freshCfg freshF freshG ∧
    freshCfg.redirectContinue = true ∧
    freshCfg.resumeMap = .unwind ∧
    freshCfg.link = .rustc ∧
    freshF.caps = freshG.caps ∧
    CapsSubset freshG freshF ∧
    CapLegal freshG ∧
    AbiInsensitive freshG ∧
    freshCi.abiSensitive = false ∧
    AbiAgree freshP freshF freshG ∧
    ¬ (SlotsFresh freshCfg.withDest freshF freshG) ∧
    SlotsInjective freshCfg.withDest freshG ∧
    freshCfg.withDest.ret = .dest ∧
    freshCfg.withDest.redirectContinue = true ∧
    freshCfg.withDest.resumeMap = .unwind ∧
    freshCfg.withDest.link = .rustc ∧
    CleanupClosed freshF ∧
    DestNotReadInCleanup freshF freshCi.dest) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:255-284
theorem cex_slotsInjective :
    (IsCallSite injP 0 0 injF injCi injG ∧
    LocalsBounded injF ∧
    LocalsBounded injG ∧
    BlocksBounded injF ∧
    ScopesWF injF ∧
    ScopesWF injG ∧
    SlotsFresh injCfg injF injG ∧
    ¬ (SlotsInjective injCfg injG) ∧
    injCfg.ret = .temp 1 ∧
    TempFresh 1 injCfg injF injG ∧
    injCfg.redirectContinue = true ∧
    injCfg.resumeMap = .unwind ∧
    injCfg.link = .rustc ∧
    injF.caps = injG.caps ∧
    CapsSubset injG injF ∧
    CapLegal injG ∧
    AbiInsensitive injG ∧
    injCi.abiSensitive = false ∧
    AbiAgree injP injF injG ∧
    SlotsFresh injCfg.withDest injF injG ∧
    ¬ (SlotsInjective injCfg.withDest injG) ∧
    injCfg.withDest.ret = .dest ∧
    injCfg.withDest.redirectContinue = true ∧
    injCfg.withDest.resumeMap = .unwind ∧
    injCfg.withDest.link = .rustc ∧
    CleanupClosed injF ∧
    DestNotReadInCleanup injF injCi.dest) ∧
    ¬ BehEquiv injP (inline injP 0 0 injCfg) ∧
    ¬ BehEquiv injP (inline injP 0 0 injCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:288-318
theorem cex_tempFresh :
    (IsCallSite tempP 0 0 tempF tempCi tempG ∧
    LocalsBounded tempF ∧
    LocalsBounded tempG ∧
    BlocksBounded tempF ∧
    ScopesWF tempF ∧
    ScopesWF tempG ∧
    SlotsFresh tempCfg tempF tempG ∧
    SlotsInjective tempCfg tempG ∧
    tempCfg.ret = .temp 2 ∧
    tempCfg.ret ≠ .dest ∧
    ¬ (TempFresh 2 tempCfg tempF tempG) ∧
    tempCfg.redirectContinue = true ∧
    tempCfg.resumeMap = .unwind ∧
    tempCfg.link = .rustc ∧
    tempF.caps = tempG.caps ∧
    CapsSubset tempG tempF ∧
    CapLegal tempG ∧
    AbiInsensitive tempG ∧
    tempCi.abiSensitive = false ∧
    AbiAgree tempP tempF tempG ∧
    SlotsFresh tempCfg.withDest tempF tempG ∧
    SlotsInjective tempCfg.withDest tempG ∧
    tempCfg.withDest.ret = .dest ∧
    ¬ (TempFresh 2 tempCfg.withDest tempF tempG) ∧
    tempCfg.withDest.redirectContinue = true ∧
    tempCfg.withDest.resumeMap = .unwind ∧
    tempCfg.withDest.link = .rustc ∧
    CleanupClosed tempF ∧
    DestNotReadInCleanup tempF tempCi.dest) ∧
    ¬ BehEquiv tempP (inline tempP 0 0 tempCfg) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:322-351
theorem cex_redirectContinue :
    (IsCallSite contP 0 0 contF contCi contG ∧
    LocalsBounded contF ∧
    LocalsBounded contG ∧
    BlocksBounded contF ∧
    ScopesWF contF ∧
    ScopesWF contG ∧
    SlotsFresh contCfg contF contG ∧
    SlotsInjective contCfg contG ∧
    contCfg.ret = .temp 2 ∧
    TempFresh 2 contCfg contF contG ∧
    ¬ (contCfg.redirectContinue = true) ∧
    contCfg.resumeMap = .unwind ∧
    contCfg.link = .rustc ∧
    contF.caps = contG.caps ∧
    CapsSubset contG contF ∧
    CapLegal contG ∧
    AbiInsensitive contG ∧
    contCi.abiSensitive = false ∧
    AbiAgree contP contF contG ∧
    SlotsFresh contCfg.withDest contF contG ∧
    SlotsInjective contCfg.withDest contG ∧
    contCfg.withDest.ret = .dest ∧
    ¬ (contCfg.withDest.redirectContinue = true) ∧
    contCfg.withDest.resumeMap = .unwind ∧
    contCfg.withDest.link = .rustc ∧
    CleanupClosed contF ∧
    DestNotReadInCleanup contF contCi.dest) ∧
    ¬ BehEquiv contP (inline contP 0 0 contCfg) ∧
    ¬ BehEquiv contP (inline contP 0 0 contCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:355-384
theorem cex_resumeMap :
    (IsCallSite resP 0 0 contF contCi resG ∧
    LocalsBounded contF ∧
    LocalsBounded resG ∧
    BlocksBounded contF ∧
    ScopesWF contF ∧
    ScopesWF resG ∧
    SlotsFresh resCfg contF resG ∧
    SlotsInjective resCfg resG ∧
    resCfg.ret = .temp 2 ∧
    TempFresh 2 resCfg contF resG ∧
    resCfg.redirectContinue = true ∧
    ¬ (resCfg.resumeMap = .unwind) ∧
    resCfg.link = .rustc ∧
    contF.caps = resG.caps ∧
    CapsSubset resG contF ∧
    CapLegal resG ∧
    AbiInsensitive resG ∧
    contCi.abiSensitive = false ∧
    AbiAgree resP contF resG ∧
    SlotsFresh resCfg.withDest contF resG ∧
    SlotsInjective resCfg.withDest resG ∧
    resCfg.withDest.ret = .dest ∧
    resCfg.withDest.redirectContinue = true ∧
    ¬ (resCfg.withDest.resumeMap = .unwind) ∧
    resCfg.withDest.link = .rustc ∧
    CleanupClosed contF ∧
    DestNotReadInCleanup contF contCi.dest) ∧
    ¬ BehEquiv resP (inline resP 0 0 resCfg) ∧
    ¬ BehEquiv resP (inline resP 0 0 resCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:388-417
theorem cex_linkRule :
    (IsCallSite linkP1 0 3 linkF1 linkCi1 linkK ∧
    LocalsBounded linkF1 ∧
    LocalsBounded linkK ∧
    BlocksBounded linkF1 ∧
    ScopesWF linkF1 ∧
    ScopesWF linkK ∧
    SlotsFresh linkCfg linkF1 linkK ∧
    SlotsInjective linkCfg linkK ∧
    linkCfg.ret = .temp 2 ∧
    TempFresh 2 linkCfg linkF1 linkK ∧
    linkCfg.redirectContinue = true ∧
    linkCfg.resumeMap = .unwind ∧
    ¬ (linkCfg.link = .rustc) ∧
    linkF1.caps = linkK.caps ∧
    CapsSubset linkK linkF1 ∧
    CapLegal linkK ∧
    AbiInsensitive linkK ∧
    linkCi1.abiSensitive = false ∧
    AbiAgree linkP1 linkF1 linkK ∧
    SlotsFresh linkCfg.withDest linkF1 linkK ∧
    SlotsInjective linkCfg.withDest linkK ∧
    linkCfg.withDest.ret = .dest ∧
    linkCfg.withDest.redirectContinue = true ∧
    linkCfg.withDest.resumeMap = .unwind ∧
    ¬ (linkCfg.withDest.link = .rustc) ∧
    CleanupClosed linkF1 ∧
    DestNotReadInCleanup linkF1 linkCi1.dest) ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg) ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg.withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:421-450
theorem cex_capsAbi :
    (IsCallSite abiP 0 0 (capF [1]) plainCi abiG ∧
    LocalsBounded (capF [1]) ∧
    LocalsBounded abiG ∧
    BlocksBounded (capF [1]) ∧
    ScopesWF (capF [1]) ∧
    ScopesWF abiG ∧
    SlotsFresh (InlineCfg.canonical 1) (capF [1]) abiG ∧
    SlotsInjective (InlineCfg.canonical 1) abiG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) (capF [1]) abiG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    ¬ ((capF [1]).caps = abiG.caps) ∧
    CapsSubset abiG (capF [1]) ∧
    CapLegal abiG ∧
    ¬ (AbiInsensitive abiG) ∧
    plainCi.abiSensitive = false ∧
    ¬ (AbiAgree abiP (capF [1]) abiG) ∧
    SlotsFresh (InlineCfg.canonical 1).withDest (capF [1]) abiG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest abiG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed (capF [1]) ∧
    DestNotReadInCleanup (capF [1]) plainCi.dest) ∧
    ¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:454-483
theorem cex_capLegal :
    (IsCallSite legalP 0 0 (capF [3]) plainCi legalG ∧
    LocalsBounded (capF [3]) ∧
    LocalsBounded legalG ∧
    BlocksBounded (capF [3]) ∧
    ScopesWF (capF [3]) ∧
    ScopesWF legalG ∧
    SlotsFresh (InlineCfg.canonical 1) (capF [3]) legalG ∧
    SlotsInjective (InlineCfg.canonical 1) legalG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) (capF [3]) legalG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    ¬ ((capF [3]).caps = legalG.caps) ∧
    CapsSubset legalG (capF [3]) ∧
    ¬ (CapLegal legalG) ∧
    AbiInsensitive legalG ∧
    plainCi.abiSensitive = false ∧
    AbiAgree legalP (capF [3]) legalG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest (capF [3]) legalG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest legalG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed (capF [3]) ∧
    DestNotReadInCleanup (capF [3]) plainCi.dest) ∧
    ¬ BehEquiv legalP (inline legalP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv legalP (inline legalP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:487-516
theorem cex_callAbiSensitive :
    (IsCallSite cabP 0 0 cabF cabCi cabG ∧
    LocalsBounded cabF ∧
    LocalsBounded cabG ∧
    BlocksBounded cabF ∧
    ScopesWF cabF ∧
    ScopesWF cabG ∧
    SlotsFresh (InlineCfg.canonical 1) cabF cabG ∧
    SlotsInjective (InlineCfg.canonical 1) cabG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) cabF cabG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    ¬ (cabF.caps = cabG.caps) ∧
    CapsSubset cabG cabF ∧
    CapLegal cabG ∧
    AbiInsensitive cabG ∧
    ¬ (cabCi.abiSensitive = false) ∧
    ¬ (AbiAgree cabP cabF cabG) ∧
    SlotsFresh (InlineCfg.canonical 1).withDest cabF cabG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest cabG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed cabF ∧
    DestNotReadInCleanup cabF cabCi.dest) ∧
    ¬ BehEquiv cabP (inline cabP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv cabP (inline cabP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:520-548
theorem cex_cleanupClosed :
    (IsCallSite clP 0 0 clF clCi dG ∧
    LocalsBounded clF ∧
    LocalsBounded dG ∧
    BlocksBounded clF ∧
    ScopesWF clF ∧
    ScopesWF dG ∧
    SlotsFresh (InlineCfg.canonical 2) clF dG ∧
    SlotsInjective (InlineCfg.canonical 2) dG ∧
    (InlineCfg.canonical 2).ret = .temp 2 ∧
    TempFresh 2 (InlineCfg.canonical 2) clF dG ∧
    (InlineCfg.canonical 2).redirectContinue = true ∧
    (InlineCfg.canonical 2).resumeMap = .unwind ∧
    (InlineCfg.canonical 2).link = .rustc ∧
    clF.caps = dG.caps ∧
    CapsSubset dG clF ∧
    CapLegal dG ∧
    AbiInsensitive dG ∧
    clCi.abiSensitive = false ∧
    AbiAgree clP clF dG ∧
    SlotsFresh (InlineCfg.canonical 2).withDest clF dG ∧
    SlotsInjective (InlineCfg.canonical 2).withDest dG ∧
    (InlineCfg.canonical 2).withDest.ret = .dest ∧
    (InlineCfg.canonical 2).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 2).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 2).withDest.link = .rustc ∧
    ¬ (CleanupClosed clF) ∧
    DestNotReadInCleanup clF clCi.dest) ∧
    ¬ BehEquiv clP (inline clP 0 0 (InlineCfg.canonical 2).withDest) := …
```

```lean
-- lean/ToyInline/Counterexamples.lean:552-582
theorem cex_destNotReadInCleanup :
    (IsCallSite dcP 0 0 dcF dcCi dG ∧
    LocalsBounded dcF ∧
    LocalsBounded dG ∧
    BlocksBounded dcF ∧
    ScopesWF dcF ∧
    ScopesWF dG ∧
    SlotsFresh (InlineCfg.canonical 2) dcF dG ∧
    SlotsInjective (InlineCfg.canonical 2) dG ∧
    (InlineCfg.canonical 2).ret = .temp 2 ∧
    TempFresh 2 (InlineCfg.canonical 2) dcF dG ∧
    (InlineCfg.canonical 2).redirectContinue = true ∧
    (InlineCfg.canonical 2).resumeMap = .unwind ∧
    (InlineCfg.canonical 2).link = .rustc ∧
    dcF.caps = dG.caps ∧
    CapsSubset dG dcF ∧
    CapLegal dG ∧
    AbiInsensitive dG ∧
    dcCi.abiSensitive = false ∧
    AbiAgree dcP dcF dG ∧
    SlotsFresh (InlineCfg.canonical 2).withDest dcF dG ∧
    SlotsInjective (InlineCfg.canonical 2).withDest dG ∧
    (InlineCfg.canonical 2).withDest.ret = .dest ∧
    (InlineCfg.canonical 2).withDest.ret ≠ .temp 2 ∧
    TempFresh 2 (InlineCfg.canonical 2).withDest dcF dG ∧
    (InlineCfg.canonical 2).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 2).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 2).withDest.link = .rustc ∧
    CleanupClosed dcF ∧
    ¬ (DestNotReadInCleanup dcF dcCi.dest)) ∧
    ¬ BehEquiv dcP (inline dcP 0 0 (InlineCfg.canonical 2).withDest) := …
```

#### `lean/ToyInline/OtherCounterexamples.lean`

```lean
-- lean/ToyInline/OtherCounterexamples.lean:16
def cst (v : Nat) : Local → Nat := fun _ => v
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:21-27
theorem cex_frame_injective :
    (RenameAvoids (fun _ => 5) 2 [] ∧ StmtLocalsLt 2 (.assign 0 (.use (.const 7))) ∧
      FrameRel (fun _ => 5) 2 [] (cst 0) (cst 3) (cst 3) ∧ ¬ RenameInjectiveOn (fun _ => 5) 2) ∧
    ¬ (FrameRel (fun _ => 5) 2 [] (cst 0) (stmtStore (cst 3) (.assign 0 (.use (.const 7)))).1
          (stmtStore (cst 3) ((Stmt.assign 0 (.use (.const 7))).rename (fun _ => 5) 0)).1 ∧
        (stmtStore (cst 3) ((Stmt.assign 0 (.use (.const 7))).rename (fun _ => 5) 0)).2 =
          (stmtStore (cst 3) (.assign 0 (.use (.const 7)))).2) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:33-39
theorem cex_frame_avoids :
    (RenameInjectiveOn (· + 1) 2 ∧ StmtLocalsLt 2 (.assign 1 (.use (.const 7))) ∧
      FrameRel (· + 1) 2 [2] (cst 4) (cst 4) (cst 4) ∧ ¬ RenameAvoids (· + 1) 2 [2]) ∧
    ¬ (FrameRel (· + 1) 2 [2] (cst 4) (stmtStore (cst 4) (.assign 1 (.use (.const 7)))).1
          (stmtStore (cst 4) ((Stmt.assign 1 (.use (.const 7))).rename (· + 1) 0)).1 ∧
        (stmtStore (cst 4) ((Stmt.assign 1 (.use (.const 7))).rename (· + 1) 0)).2 =
          (stmtStore (cst 4) (.assign 1 (.use (.const 7)))).2) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:43-50
theorem cex_frame_stmtLocals :
    (RenameInjectiveOn (· + 10) 2 ∧ RenameAvoids (· + 10) 2 [] ∧
      FrameRel (· + 10) 2 [] (cst 0) (cst 1) (upd (cst 1) 12 9) ∧
      ¬ StmtLocalsLt 2 (.emit (.var 2))) ∧
    ¬ (FrameRel (· + 10) 2 [] (cst 0) (stmtStore (cst 1) (.emit (.var 2))).1
          (stmtStore (upd (cst 1) 12 9) ((Stmt.emit (.var 2)).rename (· + 10) 0)).1 ∧
        (stmtStore (upd (cst 1) 12 9) ((Stmt.emit (.var 2)).rename (· + 10) 0)).2 =
          (stmtStore (cst 1) (.emit (.var 2))).2) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:54-60
theorem cex_frame_rel :
    (RenameInjectiveOn (· + 10) 1 ∧ RenameAvoids (· + 10) 1 [] ∧ StmtLocalsLt 1 (.emit (.var 0)) ∧
      ¬ FrameRel (· + 10) 1 [] (cst 0) (cst 1) (cst 2)) ∧
    ¬ (FrameRel (· + 10) 1 [] (cst 0) (stmtStore (cst 1) (.emit (.var 0))).1
          (stmtStore (cst 2) ((Stmt.emit (.var 0)).rename (· + 10) 0)).1 ∧
        (stmtStore (cst 2) ((Stmt.emit (.var 0)).rename (· + 10) 0)).2 =
          (stmtStore (cst 1) (.emit (.var 0))).2) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:65
def pRet : Program := mkProg [mkFn 1 [blk [] .ret]]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:66
def pPan : Program := mkProg [mkFn 1 [blk [] (.panic .continue)]]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:67
def pMissing : Program := mkProg []
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:68
def pUnr : Program := mkProg [mkFn 1 [blk [] .unreachable]]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:69
def e0 : Entry := ⟨0, [], 0⟩
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:71
theorem behEquiv_refl (p : Program) : BehEquiv p p := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:76
theorem prefixClosed_noPanic : PrefixClosed NoPanic := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:99-100
theorem cex_terminal_behEquiv :
    ¬ BehEquivAt pRet pPan e0 ∧ ¬ (TerminalHolds NoPanic pRet e0 ↔ TerminalHolds NoPanic pPan e0) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:106-108
theorem cex_safety_behEquiv :
    (PrefixClosed NoPanic ∧ ¬ BehEquivAt pRet pPan e0) ∧
      ¬ (SafetyHolds NoPanic pRet e0 ↔ SafetyHolds NoPanic pPan e0) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:115-118
theorem cex_safety_prefixClosed :
    (BehEquivAt pMissing pUnr e0 ∧ ¬ PrefixClosed (fun o => o.outcome.isSome = true)) ∧
      ¬ (SafetyHolds (fun o => o.outcome.isSome = true) pMissing e0 ↔
          SafetyHolds (fun o => o.outcome.isSome = true) pUnr e0) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:133-134
def vcF : Fn := mkFn 2 [blk [] (mkCall 1 [.const 7] 1 (some 1) .continue),
  blk [.emit (.var 1)] .ret]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:135
def vcP : Program := mkProg [vcF, gP]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:136
def vcQ : Program := inlineCanon vcP 0 0
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:200-210
theorem capsSubset_guard_positiveControl :
    (IsCallSite abiPc 0 0 (capF [1]) plainCi abiG ∧ LocalsBounded (capF [1]) ∧
      LocalsBounded abiG ∧ BlocksBounded (capF [1]) ∧ ScopesWF (capF [1]) ∧ ScopesWF abiG ∧
      SlotsFresh (InlineCfg.canonical 1) (capF [1]) abiG ∧
      SlotsInjective (InlineCfg.canonical 1) abiG ∧
      (InlineCfg.canonical 1).ret = .temp 1 ∧ TempFresh 1 (InlineCfg.canonical 1) (capF [1]) abiG ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset abiG (capF [1]) ∧ CapLegal abiG ∧ plainCi.abiSensitive = false ∧
      AbiAgree abiPc (capF [1]) abiG) ∧
    BehEquiv abiPc (inline abiPc 0 0 (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:276-285
theorem cex_walkCallee_F :
    (ScopeTreeWF (scopesFn [⟨none, none⟩, ⟨none, none⟩]).scopes ∧ 0 < 2 ∧
      LinkRule.rustc = LinkRule.rustc ∧ ¬ ScopeParentsBelow (scopesFn cycScopes).scopes) ∧
    locValue trAll ((scopesFn cycScopes).scopes ++
        linkScopes .rustc (scopesFn cycScopes) ci50 (scopesFn [⟨none, none⟩, ⟨none, none⟩]))
        ((scopesFn cycScopes).scopes.length + 0) 7 none ≠
      locValue trAll (scopesFn [⟨none, none⟩, ⟨none, none⟩]).scopes 0 7
        (if trAll ci50.callee then
          some (locValue trAll (scopesFn cycScopes).scopes ci50.scope ci50.span none)
        else none) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:291-301
theorem cex_walkCallee_G :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧ 0 < 1 ∧ LinkRule.rustc = LinkRule.rustc ∧
      ScopeParentsBelow (scopesFn [⟨some (3, 50), none⟩]).scopes ∧
      ¬ ScopeTreeWF (scopesFn [⟨some (3, 50), none⟩]).scopes) ∧
    locValue (fun g => g == 1) ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn [⟨some (3, 50), none⟩]))
        ((scopesFn rootScopes).scopes.length + 0) 7 none ≠
      locValue (fun g => g == 1) (scopesFn [⟨some (3, 50), none⟩]).scopes 0 7
        (if (fun g => g == 1) ci99.callee then
          some (locValue (fun g => g == 1) (scopesFn rootScopes).scopes ci99.scope ci99.span none)
        else none) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:306-318
theorem cex_walkCallee_Gparents :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧
      nth? (scopesFn cycScopes).scopes 0 = some ⟨none, none⟩ ∧
      ¬ ScopeParentsBelow (scopesFn cycScopes).scopes ∧
      ¬ ScopeTreeWF (scopesFn cycScopes).scopes ∧
      1 < (scopesFn cycScopes).scopes.length ∧ LinkRule.rustc = LinkRule.rustc) ∧
    locValue trAll ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn cycScopes))
        ((scopesFn rootScopes).scopes.length + 1) 7 none ≠
      locValue trAll (scopesFn cycScopes).scopes 1 7
        (if trAll ci99.callee then
          some (locValue trAll (scopesFn rootScopes).scopes ci99.scope ci99.span none)
        else none) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:322-331
theorem cex_walkCallee_s :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧ ScopeTreeWF (scopesFn rootScopes).scopes ∧
      LinkRule.rustc = LinkRule.rustc ∧ ¬ (1 < (scopesFn rootScopes).scopes.length)) ∧
    locValue trAll ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn rootScopes))
        ((scopesFn rootScopes).scopes.length + 1) 7 none ≠
      locValue trAll (scopesFn rootScopes).scopes 1 7
        (if trAll ci99.callee then
          some (locValue trAll (scopesFn rootScopes).scopes ci99.scope ci99.span none)
        else none) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:335-343
theorem cex_walkCallee_link :
    (ScopeParentsBelow linkF1.scopes ∧ ScopeTreeWF linkK.scopes ∧ 0 < linkK.scopes.length ∧
      LinkRule.ignoreParent ≠ LinkRule.rustc) ∧
    locValue linkP1.tracked (linkF1.scopes ++ linkScopes .ignoreParent linkF1 linkCi1 linkK)
        (linkF1.scopes.length + 0) 30 none ≠
      locValue linkP1.tracked linkK.scopes 0 30
        (if linkP1.tracked linkCi1.callee then
          some (locValue linkP1.tracked linkF1.scopes linkCi1.scope linkCi1.span none)
        else none) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:347-352
theorem cex_walkCaller_s :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧
      ¬ (1 < (scopesFn rootScopes).scopes.length)) ∧
    locValue trAll ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn rootScopes)) 1 7 none ≠
      locValue trAll (scopesFn rootScopes).scopes 1 7 none := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:356-360
theorem cex_walkCaller_F :
    (¬ ScopeParentsBelow (scopesFn cycScopes).scopes ∧ 1 < (scopesFn cycScopes).scopes.length) ∧
    locValue trAll ((scopesFn cycScopes).scopes ++
        linkScopes .rustc (scopesFn cycScopes) ci50 (scopesFn rootScopes)) 1 7 none ≠
      locValue trAll (scopesFn cycScopes).scopes 1 7 none := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:364-369
theorem cex_scopesWF_B :
    (ScopesWF (mkFn 1 [blk [] (.goto 0)]) ∧ ScopeParentsBelow (mkFn 1 []).scopes ∧
      ScopeRefsBounded (mkFn 1 []) ∧
      nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 ≠ some (blk [.loc 0 9] (.goto 0))) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [.loc 0 9] (.goto 0)) ci99
        (mkFn 1 []) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:374-380
theorem cex_scopesWF_F :
    (nth? (mkFn 1 [blk [.loc 0 5] (.goto 0)]).blocks 0 = some (blk [.loc 0 5] (.goto 0)) ∧
      ScopeParentsBelow (mkFn 1 []).scopes ∧ ScopeRefsBounded (mkFn 1 []) ∧
      ScopeTreeWF (mkFn 1 [blk [.loc 0 5] (.goto 0)]).scopes ∧
      ¬ ScopesWF (mkFn 1 [blk [.loc 0 5] (.goto 0)])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [.loc 0 5] (.goto 0)]) 0 (blk [.loc 0 5] (.goto 0)) ci99
        (mkFn 1 []) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:384-390
theorem cex_scopesWF_G :
    (nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 = some (blk [] (.goto 0)) ∧
      ScopesWF (mkFn 1 [blk [] (.goto 0)]) ∧
      ScopeParentsBelow (mkFn 1 [blk [.loc 0 5] .ret]).scopes ∧
      ¬ ScopeRefsBounded (mkFn 1 [blk [.loc 0 5] .ret])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [] (.goto 0)) ci99
        (mkFn 1 [blk [.loc 0 5] .ret]) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:395-401
theorem cex_scopesWF_Gparents :
    (nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 = some (blk [] (.goto 0)) ∧
      ScopesWF (mkFn 1 [blk [] (.goto 0)]) ∧
      ¬ ScopeParentsBelow (mkFn 1 [] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])).scopes ∧
      ScopeRefsBounded (mkFn 1 [] (scopes := [⟨none, none⟩, ⟨none, some 1⟩]))) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [] (.goto 0)) ci99
        (mkFn 1 [] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:406-414
theorem cex_scopesWF_Froot :
    (nth? (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])).blocks 0 =
        some (blk [] (.goto 0)) ∧
      ScopeParentsBelow (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])).scopes ∧
      ScopeRefsBounded (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])) ∧
      ¬ ScopesWF (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])) ∧
      ScopeParentsBelow (mkFn 1 []).scopes ∧ ScopeRefsBounded (mkFn 1 [])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])) 0
        (blk [] (.goto 0)) ci99 (mkFn 1 []) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:419-427
theorem cex_scopesWF_Fparents :
    (nth? (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])).blocks 0 =
        some (blk [] (.goto 0)) ∧
      ¬ ScopeParentsBelow
        (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])).scopes ∧
      ScopeRefsBounded (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])) ∧
      ScopeParentsBelow (mkFn 1 []).scopes ∧ ScopeRefsBounded (mkFn 1 [])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])) 0
        (blk [] (.goto 0)) ci99 (mkFn 1 []) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:432
theorem cex_trans_left : BehEquiv pPan pPan ∧ ¬ BehEquiv pRet pPan := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:435
theorem cex_trans_right : BehEquiv pRet pRet ∧ ¬ BehEquiv pRet pPan := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:440
def ordH : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:441
def ordF : Fn := mkFn 2 [blk [] (mkCall 2 [] 1 (some 1) .continue), blk [.emit (.var 1)] .ret]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:442
def ordG : Fn := mkFn 2 [blk [.assign 1 (.use (.const 4)), .assign 0 (.use (.var 1))] .ret]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:443
def ordP : Program := mkProg [ordH, ordF, ordG]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:445
def ordQ1 : Program := inlineCanon (inlineCanon ordP 1 0) 0 0
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:447
def ordQ2 : Program := inlineCanon (inlineCanon ordP 0 0) 0 3
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:449
def Fn.totalStmts (F : Fn) : Nat := (F.blocks.flatMap Block.stmts).length
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:465-466
theorem inline_order_other_fns :
    nth? ordQ1.fns 1 ≠ nth? ordP.fns 1 ∧ nth? ordQ2.fns 1 = nth? ordP.fns 1 := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:535-536
theorem cex_tempFresh_breaks_slot_conjunct :
    tempF.nlocals ≤ 2 ∧ ¬ (∀ i, i < tempG.nlocals → 1 ≤ i → tempCfg.slot i ≠ 2) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:553-562
theorem cex_tempFresh_callerLocal :
    (IsCallSite tfP 0 0 tfF tfCi tfG ∧ LocalsBounded tfF ∧ LocalsBounded tfG ∧
      BlocksBounded tfF ∧ ScopesWF tfF ∧ ScopesWF tfG ∧
      SlotsFresh tfCfg tfF tfG ∧ SlotsInjective tfCfg tfG ∧ tfCfg.ret = .temp 1 ∧
      ¬ (tfF.nlocals ≤ 1) ∧ (∀ i, i < tfG.nlocals → 1 ≤ i → tfCfg.slot i ≠ 1) ∧
      ¬ TempFresh 1 tfCfg tfF tfG ∧
      tfCfg.redirectContinue = true ∧ tfCfg.resumeMap = .unwind ∧ tfCfg.link = .rustc ∧
      tfF.caps = tfG.caps ∧ CapsSubset tfG tfF ∧ CapLegal tfG ∧ AbiInsensitive tfG ∧
      tfCi.abiSensitive = false ∧ AbiAgree tfP tfF tfG) ∧
    ¬ BehEquiv tfP (inline tfP 0 0 tfCfg) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:568-570
theorem cex_scopesWF_breaks_refs_conjunct :
    ScopeTreeWF scFF.scopes ∧ ¬ ScopeRefsBounded scFF ∧
      ScopeTreeWF scGG.scopes ∧ ¬ ScopeRefsBounded scGG := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:584-617
theorem cex_scopesWFG_root :
    (IsCallSite rtP 0 0 rtF spanCi rtG ∧
    LocalsBounded rtF ∧
    LocalsBounded rtG ∧
    BlocksBounded rtF ∧
    ScopesWF rtF ∧
    ¬ (ScopesWF rtG) ∧
    ScopeParentsBelow rtG.scopes ∧ ScopeRefsBounded rtG ∧
    SlotsFresh (InlineCfg.canonical 1) rtF rtG ∧
    SlotsInjective (InlineCfg.canonical 1) rtG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) rtF rtG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    rtF.caps = rtG.caps ∧
    CapsSubset rtG rtF ∧
    CapLegal rtG ∧
    AbiInsensitive rtG ∧
    spanCi.abiSensitive = false ∧
    AbiAgree rtP rtF rtG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest rtF rtG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest rtG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed rtF ∧
    DestNotReadInCleanup rtF spanCi.dest) ∧
    run rtP 30 (init rtP e0) = ⟨[.loc 7], some (.returned 0)⟩ ∧
    run (inline rtP 0 0 (InlineCfg.canonical 1)) 40
      (init (inline rtP 0 0 (InlineCfg.canonical 1)) e0) = ⟨[.loc 77], some (.returned 0)⟩ ∧
    ¬ BehEquiv rtP (inline rtP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv rtP (inline rtP 0 0 (InlineCfg.canonical 1).withDest) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:627
def zeroG : Fn := mkFn 0 [blk [] (.panic .continue)]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:628
def zeroF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:629
def zeroCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:633-637
theorem inlineFn_nlocals_covers_retTemp :
    LocalsBounded zeroF ∧ LocalsBounded zeroG ∧
      (inlineFn zeroF 0 (blk [] (.call zeroCi)) zeroCi zeroG (InlineCfg.canonical 1)).nlocals = 2 ∧
      LocalsBounded (inlineFn zeroF 0 (blk [] (.call zeroCi)) zeroCi zeroG
        (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:643-651
theorem cex_localsBoundedInline_F :
    (nth? (mkFn 1 [blk [.emit (.var 3)] (.call zeroCi)]).blocks 0 =
        some (blk [.emit (.var 3)] (.call zeroCi)) ∧
      (blk [.emit (.var 3)] (.call zeroCi)).term = .call zeroCi ∧
      ¬ LocalsBounded (mkFn 1 [blk [.emit (.var 3)] (.call zeroCi)]) ∧
      LocalsBounded (mkFn 1 [blk [] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [.emit (.var 3)] (.call zeroCi)]) 0
        (blk [.emit (.var 3)] (.call zeroCi)) zeroCi (mkFn 1 [blk [] .ret])
        (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:655-661
theorem cex_localsBoundedInline_G :
    (nth? (mkFn 1 [blk [] (.call zeroCi)]).blocks 0 = some (blk [] (.call zeroCi)) ∧
      (blk [] (.call zeroCi)).term = .call zeroCi ∧
      LocalsBounded (mkFn 1 [blk [] (.call zeroCi)]) ∧
      ¬ LocalsBounded (mkFn 1 [blk [.emit (.var 5)] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [] (.call zeroCi)]) 0 (blk [] (.call zeroCi)) zeroCi
        (mkFn 1 [blk [.emit (.var 5)] .ret]) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:665-670
theorem cex_localsBoundedInline_term :
    (nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 = some (blk [] (.goto 0)) ∧
      (blk [] (.goto 0)).term ≠ .call (mkCallInfo 1 [] 7 (some 0) .continue) ∧
      LocalsBounded (mkFn 1 [blk [] (.goto 0)]) ∧ LocalsBounded (mkFn 1 [blk [] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [] (.goto 0))
        (mkCallInfo 1 [] 7 (some 0) .continue) (mkFn 1 [blk [] .ret]) (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:674-680
theorem cex_localsBoundedInline_B :
    (nth? (mkFn 1 [blk [] (.call zeroCi)]).blocks 0 ≠ some (blk [.emit (.var 9)] (.call zeroCi)) ∧
      (blk [.emit (.var 9)] (.call zeroCi)).term = .call zeroCi ∧
      LocalsBounded (mkFn 1 [blk [] (.call zeroCi)]) ∧ LocalsBounded (mkFn 1 [blk [] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [] (.call zeroCi)]) 0
        (blk [.emit (.var 9)] (.call zeroCi)) zeroCi (mkFn 1 [blk [] .ret])
        (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:684
def oobG : Fn := mkFn 1 [blk [] (.goto 5)]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:688-691
theorem cex_blocksBounded_inlineFn_oob :
    BlocksBounded zeroF ∧ ¬ BlocksBounded oobG ∧
      ¬ BlocksBounded (inlineFn zeroF 0 (blk [] (.call zeroCi)) zeroCi oobG
        (InlineCfg.canonical 1)) := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:696
def pGotoUnr : Program := mkProg [mkFn 1 [blk [] (.goto 1), blk [] .unreachable]]
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:700
theorem behEquiv_pMissing_pUnr : BehEquiv pMissing pUnr := …
```

```lean
-- lean/ToyInline/OtherCounterexamples.lean:707
theorem behEquiv_pUnr_pGotoUnr : BehEquiv pUnr pGotoUnr := …
```

#### `lean/ToyInline/Examples.lean`

```lean
-- lean/ToyInline/Examples.lean:16-17
theorem run_progP_lifo :
    run progP 40 (init progP ⟨0, [0], 0⟩) = ⟨[.out 100, .out 200], some .unwound⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:49-50
theorem run_chain_tracked :
    run (chainP true) 30 (init (chainP true) e0) = ⟨[.loc 10], some (.returned 0)⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:53-54
theorem run_chain_wrapper :
    run (chainP false) 30 (init (chainP false) e0) = ⟨[.loc 20], some (.returned 0)⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:92
theorem prefix_pos : Obs.Prefix ⟨[.out 1], none⟩ ⟨[.out 1, .out 2], some .ub⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:96
theorem prefix_neg : ¬ Obs.Prefix ⟨[.out 1], some .ub⟩ ⟨[.out 1, .out 2], some .ub⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:101
theorem behEquivAt_pos : BehEquivAt progP (inline progP 0 0 cfgP) ⟨0, [0], 0⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:104
theorem behEquivAt_neg : ¬ BehEquivAt contP (inline contP 0 0 contCfg) e0 := …
```

```lean
-- lean/ToyInline/Examples.lean:109
theorem isCallSite_pos : IsCallSite progP 0 0 fP ciP gP := …
```

```lean
-- lean/ToyInline/Examples.lean:110
theorem isCallSite_neg : ¬ IsCallSite progP 0 1 fP ciP gP := …
```

```lean
-- lean/ToyInline/Examples.lean:112
theorem localsBounded_pos : LocalsBounded fP := …
```

```lean
-- lean/ToyInline/Examples.lean:113
theorem localsBounded_neg : ¬ LocalsBounded locFF := …
```

```lean
-- lean/ToyInline/Examples.lean:115
theorem blocksBounded_pos : BlocksBounded fP := …
```

```lean
-- lean/ToyInline/Examples.lean:116
theorem blocksBounded_neg : ¬ BlocksBounded blkFF := …
```

```lean
-- lean/ToyInline/Examples.lean:118
theorem scopeParentsBelow_pos : ScopeParentsBelow linkF1.scopes := …
```

```lean
-- lean/ToyInline/Examples.lean:120-121
theorem scopeParentsBelow_neg :
    ¬ ScopeParentsBelow [⟨none, some 2⟩, ⟨none, none⟩, ⟨none, none⟩] := …
```

```lean
-- lean/ToyInline/Examples.lean:123
theorem scopeTreeWF_pos : ScopeTreeWF linkF1.scopes := …
```

```lean
-- lean/ToyInline/Examples.lean:124
theorem scopeTreeWF_neg : ¬ ScopeTreeWF cycScopes := …
```

```lean
-- lean/ToyInline/Examples.lean:126
theorem scopeRefsBounded_pos : ScopeRefsBounded linkF1 := …
```

```lean
-- lean/ToyInline/Examples.lean:127
theorem scopeRefsBounded_neg : ¬ ScopeRefsBounded scFF := …
```

```lean
-- lean/ToyInline/Examples.lean:129
theorem scopesWF_pos : ScopesWF linkG := …
```

```lean
-- lean/ToyInline/Examples.lean:130
theorem scopesWF_neg : ¬ ScopesWF scGG := …
```

```lean
-- lean/ToyInline/Examples.lean:132
theorem slotsFresh_pos : SlotsFresh cfgP fP gP := …
```

```lean
-- lean/ToyInline/Examples.lean:133
theorem slotsFresh_neg : ¬ SlotsFresh freshCfg freshF freshG := …
```

```lean
-- lean/ToyInline/Examples.lean:135
theorem slotsInjective_pos : SlotsInjective (InlineCfg.canonical 1) injG := …
```

```lean
-- lean/ToyInline/Examples.lean:136
theorem slotsInjective_neg : ¬ SlotsInjective injCfg injG := …
```

```lean
-- lean/ToyInline/Examples.lean:138
theorem tempFresh_pos : TempFresh 2 cfgP fP gP := …
```

```lean
-- lean/ToyInline/Examples.lean:139
theorem tempFresh_neg : ¬ TempFresh 2 tempCfg tempF tempG := …
```

```lean
-- lean/ToyInline/Examples.lean:141
theorem cleanupClosed_pos : CleanupClosed dcF := …
```

```lean
-- lean/ToyInline/Examples.lean:142
theorem cleanupClosed_neg : ¬ CleanupClosed clF := …
```

```lean
-- lean/ToyInline/Examples.lean:144
theorem destNotReadInCleanup_pos : DestNotReadInCleanup clF 1 := …
```

```lean
-- lean/ToyInline/Examples.lean:145
theorem destNotReadInCleanup_neg : ¬ DestNotReadInCleanup dcF 1 := …
```

```lean
-- lean/ToyInline/Examples.lean:147
theorem capsSubset_pos : CapsSubset abiG (capF [1]) := …
```

```lean
-- lean/ToyInline/Examples.lean:148
theorem capsSubset_neg : ¬ CapsSubset needG (capF []) := …
```

```lean
-- lean/ToyInline/Examples.lean:150
theorem capLegal_pos : CapLegal needG := …
```

```lean
-- lean/ToyInline/Examples.lean:151
theorem capLegal_neg : ¬ CapLegal legalG := …
```

```lean
-- lean/ToyInline/Examples.lean:153
theorem abiInsensitive_pos : AbiInsensitive gP := …
```

```lean
-- lean/ToyInline/Examples.lean:154
theorem abiInsensitive_neg : ¬ AbiInsensitive abiG := …
```

```lean
-- lean/ToyInline/Examples.lean:156
theorem abiAgree_pos : AbiAgree abiPc (capF [1]) abiG := …
```

```lean
-- lean/ToyInline/Examples.lean:157
theorem abiAgree_neg : ¬ AbiAgree abiP (capF [1]) abiG := …
```

```lean
-- lean/ToyInline/Examples.lean:161
theorem frameRel_pos : FrameRel (· + 2) 2 [1] (cst 4) (cst 7) (upd (cst 7) 1 4) := …
```

```lean
-- lean/ToyInline/Examples.lean:162
theorem frameRel_neg : ¬ FrameRel (· + 2) 2 [1] (cst 4) (cst 7) (cst 7) := …
```

```lean
-- lean/ToyInline/Examples.lean:164
theorem renameInjectiveOn_pos : RenameInjectiveOn (· + 2) 3 := …
```

```lean
-- lean/ToyInline/Examples.lean:165
theorem renameInjectiveOn_neg : ¬ RenameInjectiveOn (fun _ => 5) 2 := …
```

```lean
-- lean/ToyInline/Examples.lean:167
theorem renameAvoids_pos : RenameAvoids (· + 2) 2 [0, 1] := …
```

```lean
-- lean/ToyInline/Examples.lean:168
theorem renameAvoids_neg : ¬ RenameAvoids (· + 1) 2 [2] := …
```

```lean
-- lean/ToyInline/Examples.lean:170
theorem stmtLocalsLt_pos : StmtLocalsLt 2 (.assign 1 (.add (.var 0) (.const 3))) := …
```

```lean
-- lean/ToyInline/Examples.lean:171
theorem stmtLocalsLt_neg : ¬ StmtLocalsLt 2 (.emit (.var 2)) := …
```

```lean
-- lean/ToyInline/Examples.lean:175
theorem noPanic_pos : NoPanic ⟨[], some (.returned 0)⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:176
theorem noPanic_neg : ¬ NoPanic ⟨[], some .unwound⟩ := …
```

```lean
-- lean/ToyInline/Examples.lean:178
theorem terminalHolds_pos : TerminalHolds NoPanic pRet e0 := …
```

```lean
-- lean/ToyInline/Examples.lean:180
theorem terminalHolds_neg : ¬ TerminalHolds NoPanic pPan e0 := …
```

```lean
-- lean/ToyInline/Examples.lean:183
theorem safetyHolds_pos : SafetyHolds NoPanic pRet e0 := …
```

```lean
-- lean/ToyInline/Examples.lean:185
theorem safetyHolds_neg : ¬ SafetyHolds NoPanic pPan e0 := …
```

```lean
-- lean/ToyInline/Examples.lean:187
theorem prefixClosed_pos : PrefixClosed NoPanic := …
```

```lean
-- lean/ToyInline/Examples.lean:188
theorem prefixClosed_neg : ¬ PrefixClosed (fun o => o.outcome.isSome = true) := …
```

#### `lean/ToyInline/NonVacuity.lean`

```lean
-- lean/ToyInline/NonVacuity.lean:11-14
theorem nonvacuity_frameRel_step :
    RenameInjectiveOn (· + 2) 2 ∧ RenameAvoids (· + 2) 2 [1] ∧
      StmtLocalsLt 2 (.assign 0 (.use (.var 1))) ∧
      FrameRel (· + 2) 2 [1] (cst 4) (cst 7) (upd (cst 7) 1 4) := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:18-22
theorem nonvacuity_inline_capsEq :
    IsCallSite progP 0 0 fP ciP gP ∧ LocalsBounded fP ∧ LocalsBounded gP ∧ BlocksBounded fP ∧
      ScopesWF fP ∧ ScopesWF gP ∧ SlotsFresh cfgP fP gP ∧ SlotsInjective cfgP gP ∧
      cfgP.ret = .temp 2 ∧ TempFresh 2 cfgP fP gP ∧ cfgP.redirectContinue = true ∧
      cfgP.resumeMap = .unwind ∧ cfgP.link = .rustc ∧ fP.caps = gP.caps := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:27-35
theorem nonvacuity_inline_capsEq_secondLevel :
    IsCallSite linkP1 0 3 linkF1 linkCi1 linkK ∧ LocalsBounded linkF1 ∧ LocalsBounded linkK ∧
      BlocksBounded linkF1 ∧ ScopesWF linkF1 ∧ ScopesWF linkK ∧
      SlotsFresh (InlineCfg.canonical 2) linkF1 linkK ∧
      SlotsInjective (InlineCfg.canonical 2) linkK ∧
      (InlineCfg.canonical 2).ret = .temp 2 ∧ TempFresh 2 (InlineCfg.canonical 2) linkF1 linkK ∧
      (InlineCfg.canonical 2).redirectContinue = true ∧
      (InlineCfg.canonical 2).resumeMap = .unwind ∧ (InlineCfg.canonical 2).link = .rustc ∧
      linkF1.caps = linkK.caps := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:37-42
theorem nonvacuity_inline_retDest :
    IsCallSite progP 0 0 fP ciP gP ∧ LocalsBounded fP ∧ LocalsBounded gP ∧ BlocksBounded fP ∧
      ScopesWF fP ∧ ScopesWF gP ∧ SlotsFresh cfgPd fP gP ∧ SlotsInjective cfgPd gP ∧
      cfgPd.ret = .dest ∧ CleanupClosed fP ∧ DestNotReadInCleanup fP ciP.dest ∧
      cfgPd.redirectContinue = true ∧ cfgPd.resumeMap = .unwind ∧ cfgPd.link = .rustc ∧
      fP.caps = gP.caps := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:44
theorem nonvacuity_terminalHolds_iff : BehEquivAt progP (inline progP 0 0 cfgP) ⟨0, [0], 0⟩ := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:47-48
theorem nonvacuity_safetyHolds_iff :
    BehEquivAt progP (inline progP 0 0 cfgP) ⟨0, [0], 0⟩ ∧ PrefixClosed NoPanic := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:53
def nv5F : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret] (caps := [1, 2])
```

```lean
-- lean/ToyInline/NonVacuity.lean:54
def nv5G : Fn := mkFn 1 [blk [.needCap 2, .emit (.const 1)] .ret] (caps := [2])
```

```lean
-- lean/ToyInline/NonVacuity.lean:55
def nv5P : Program := mkProg [nv5F, nv5G] (abi := abiC)
```

```lean
-- lean/ToyInline/NonVacuity.lean:57-66
theorem nonvacuity_inline_capsSubset_abiInsensitive :
    IsCallSite nv5P 0 0 nv5F plainCi nv5G ∧ LocalsBounded nv5F ∧ LocalsBounded nv5G ∧
      BlocksBounded nv5F ∧ ScopesWF nv5F ∧ ScopesWF nv5G ∧
      SlotsFresh (InlineCfg.canonical 1) nv5F nv5G ∧
      SlotsInjective (InlineCfg.canonical 1) nv5G ∧ (InlineCfg.canonical 1).ret = .temp 1 ∧
      TempFresh 1 (InlineCfg.canonical 1) nv5F nv5G ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset nv5G nv5F ∧ CapLegal nv5G ∧ AbiInsensitive nv5G ∧
      plainCi.abiSensitive = false ∧ nv5F.caps ≠ nv5G.caps := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:70
def nv6F : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret] (caps := [0, 2])
```

```lean
-- lean/ToyInline/NonVacuity.lean:71-72
def nv6G : Fn := mkFn 1 [blk [.needCap 2] (mkCall 2 [.const 5] 0 (some 1) .continue
  (abiSens := true)), blk [] .ret] (caps := [2])
```

```lean
-- lean/ToyInline/NonVacuity.lean:73
def nv6K : Fn := mkFn 2 [blk [.emit (.var 1)] .ret] (caps := [2])
```

```lean
-- lean/ToyInline/NonVacuity.lean:74
def nv6P : Program := mkProg [nv6F, nv6G, nv6K] (abi := abiC)
```

```lean
-- lean/ToyInline/NonVacuity.lean:76-85
theorem nonvacuity_inline_capsSubset_abiAgree :
    IsCallSite nv6P 0 0 nv6F plainCi nv6G ∧ LocalsBounded nv6F ∧ LocalsBounded nv6G ∧
      BlocksBounded nv6F ∧ ScopesWF nv6F ∧ ScopesWF nv6G ∧
      SlotsFresh (InlineCfg.canonical 1) nv6F nv6G ∧
      SlotsInjective (InlineCfg.canonical 1) nv6G ∧ (InlineCfg.canonical 1).ret = .temp 1 ∧
      TempFresh 1 (InlineCfg.canonical 1) nv6F nv6G ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset nv6G nv6F ∧ CapLegal nv6G ∧ AbiAgree nv6P nv6F nv6G ∧
      ¬ AbiInsensitive nv6G ∧ nv6F.caps ≠ nv6G.caps := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:90-92
theorem nonvacuity_locValue_calleeScope :
    ScopeParentsBelow linkF1.scopes ∧ ScopeTreeWF linkK.scopes ∧ 0 < linkK.scopes.length ∧
      LinkRule.rustc = LinkRule.rustc := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:95-96
theorem nonvacuity_locValue_callerScope :
    ScopeParentsBelow linkF1.scopes ∧ 2 < linkF1.scopes.length := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:99-101
theorem nonvacuity_scopesWF_inlineFn :
    nth? linkF.blocks 0 = some (blk [] (.call linkCi0)) ∧ ScopesWF linkF ∧
      ScopeParentsBelow linkG.scopes ∧ ScopeRefsBounded linkG := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:106-109
theorem nonvacuity_localsBounded_inlineFn :
    nth? linkF.blocks 0 = some (blk [] (.call linkCi0)) ∧
      (blk [] (.call linkCi0)).term = .call linkCi0 ∧ LocalsBounded linkF ∧
      LocalsBounded linkG := …
```

```lean
-- lean/ToyInline/NonVacuity.lean:114-116
theorem nonvacuity_behEquiv_trans :
    pMissing.fns ≠ pUnr.fns ∧ pUnr.fns ≠ pGotoUnr.fns ∧ pMissing.fns ≠ pGotoUnr.fns ∧
      BehEquiv pMissing pUnr ∧ BehEquiv pUnr pGotoUnr := …
```

### Modeling bridge

Basis: derived (modeling bridge)

Model–system relation: none proved (no embedding, abstraction or simulation between the toy and any real system is stated). The paragraphs below compare the toy with documented behaviour at pinned revisions; they neither establish nor refute any claim about those systems.

- **Capability guard.** rustc's MIR inliner (rust-lang/rust commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe) refuses unequal target-feature lists and gives as reason that a moved `Call` may change ABI in a host with more features (compiler/rustc_mir_transform/src/inline.rs L842-851). In the toy this reason is `capsSubset_guard_insufficient`, and the equality guard corresponds to `inline_behEquiv_retTemp_of_capsEq`. LLVM's X86 hook `X86TTIImpl::areInlineCompatible` (llvmorg-21.1.0, X86TargetTransformInfo.cpp L6494-6550) accepts a callee whose features are a subset of the caller's after checking, per moved call and per argument type, that vector and aggregate arguments are passed compatibly (`areTypesABICompatible`, L6552-6572). Derived: the toy's `p.abi` stands for the feature-dependent part of argument passing, collapsed to one Boolean class per capability list; the toy's `AbiAgree` is a coarser, global version of LLVM's per-call check. The Rust Reference counts implicitly enabled features (codegen.md L475); the toy has no implication between capabilities.
- **Return place, return block, unwinding.** rustc's return block (inline.rs L869-883), destination handling (L919-928), local mapping (L1193-1206), unwind mapping (L1220-1236) and `Return`/`UnwindResume` rewriting (L1326-1340) correspond to the toy's return block, `RetMode`, `InlineCfg.rename`, `SpliceCtx.mapUnwind` and `SpliceCtx.term` with the intended configuration. Divergences, all from reading the pinned source: (1) rustc reuses a moved caller temporary as the callee's argument local (`create_temp_if_necessary`, L1120-1146), whereas the toy copies every argument into a fresh slot (`SlotsFresh`, `prologue`); (2) rustc uses a plain-local destination directly as the callee's return place (L919-928) with no syntactic check like the toy's `CleanupClosed`/`DestNotReadInCleanup` in inline.rs — whether MIR's own invariants exclude cleanup code that reads such a destination is not examined here; (3) rustc treats `Cleanup`/`Continue` unwind actions inside callee cleanup blocks as a compiler bug (L1221-1228), whereas the toy allows and rewrites them; (4) rustc skips call sites in cleanup blocks (L505-507), refuses direct self-recursion (L706-710) and checks sanitizer and instruction-set compatibility (L829-840); the toy's `inline` does none of these, and `IsCallSite` allows `ci.callee = f`. LLVM's inliner forwards an inlined `resume` to the caller's landing pad and turns throwing calls in a body inlined through an `invoke` into invokes (InlineFunction.cpp L235-253, L557-613), the analogues of the toy's `resume` rewriting and `continue`-edge redirection.
- **Scopes and caller locations.** rustc's scope chaining (inline.rs L1248-1268) and `Body::caller_location_span` (compiler/rustc_middle/src/mir/mod.rs L683-715) correspond to `linkScope` with `LinkRule.rustc` and to `locValue`. Divergence: rustc also maintains a lexical `parent_scope` and recognises the outermost callee scope by `parent_scope.is_none()` (L1250); the toy has no lexical parent and recognises it by index `0`. RFC 2091 ("Propagation of tracker") and the Rust Reference (attributes.codegen.track_caller.behavior, codegen.md L960-966) describe the implicit-argument semantics the toy's frame semantics implements; the Reference also says the information is a hint that implementations are not required to preserve (L1043-1044) and that function-pointer shims lose it (L1046-1050), which the toy does not model.
- **Mechanized inlining proofs.** CompCert v3.18's inlining pass and its forward-simulation proof (backend/Inlining.v, backend/Inliningproof.v, including the register-agreement lemma `agree_set_reg`, L141-153) and CakeML's verified BVL inliner (`compile_prog_semantics`, bvl_inlineProofScript.sml L2030-2039, under the premise that the source semantics is not `Fail`) are established mechanized results for languages without CFG cleanup splicing or caller-location scopes; both state a refinement-style correctness, whereas `BehEquiv` is a two-sided equality of observations.

## Boundaries

### Non-claims common to several results

- **Semantic preservation notion:** `BehEquiv` preserves `ub`, `capFault`, `aborted` and garbled argument values in both directions (see the definition of `BehEquivAt` under Applicability). The tightness witnesses of `BlocksBounded F`, `CapLegal G` and `ci.abiSensitive = false` depend on this; whether those hypotheses are needed for a refinement criterion is not examined.
- **Not examined:** places with projections and borrows; storage markers and uninitialised locals (the toy zero-initialises every callee local in the prologue); `catch`/search-phase unwinding; recursion limits and cost heuristics; code size; debug information; codegen of capability-dependent instructions; per-call or per-type ABI rules; destination-mode theorems under `CapsSubset`; preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` by inlining; program-level tightness of the links-point-below conjuncts of `ScopesWF F` and `ScopesWF G` and of the clean-scope-`0` conjunct of `ScopesWF F` in the whole-program theorems.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, CompCert or any other compiler.

### Non-claims per result

- **R1**: Applies to the auxiliary store-level function `stmtStore`, which maps `needCap` and `loc` to `(st, [])`: it ignores capability faults and `loc` events, which `step` does produce. `step_storeStmt` relates `stmtStore` to `step` for `assign` and `emit` only; for `needCap` and `loc` no bridge to `step` is stated. Covers one statement step. The argument-binding prologue, the return block, terminators, unwinding and caller locations are not covered; whole-program behaviour is the subject of `inline_behEquiv_retTemp_of_capsEq` and its variants. `cex_frame_injective` shows failure when callee locals `0` and `1` map to the same host local. It does not show that a call whose destination is also one of its arguments (`x = f(x)`) breaks injectivity: under `SlotsFresh` and `LocalsBounded F` the inliner's renaming `InlineCfg.rename` maps the destination (below `F.nlocals`) and the callee slots (at or above `F.nlocals`) to different host locals, and under `TempFresh` the temporary differs from every slot (not proved here as a separate lemma). The store is a total map `Local → Nat`: no uninitialised values, no places with projections, no borrows and no aliasing through references.
- **R2**: `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witness of `BlocksBounded F` (`cex_blocksBoundedF`) has a source run ending in `ub` whose inlined run ends in `aborted`; under a criterion in which `ub` permits any behaviour it would not refute the conclusion. Whether these hypotheses are needed for a refinement criterion is not examined here. `BehEquiv` compares event sequences and outcomes from each entry; it says nothing about step counts, code size, stack depth or performance. `F.caps = G.caps` is equality of lists (order and multiplicity matter), not equality as sets; `p.abi` is an arbitrary function of the list. Whether set-equal, order-distinct lists suffice is not examined (no counterexample for them is proved here). One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined. The toy has no `catch` or search-phase unwinding, no double-panic rule beyond explicit `terminate` actions, no projections, borrows, storage markers, generics, recursion limits or debug information; values are unbounded naturals (`Rvalue.add` does not wrap); a missing call argument is read as `0` and extra arguments are ignored (`argOr`, `bindArgs`). The return place goes to a fresh temporary. With the destination as return place and no further hypotheses the conclusion fails (`cex_destNotReadInCleanup`, `cex_cleanupClosed`); `inline_behEquiv_retDest_of_destUnobservedOnUnwind` states a destination-mode version with two extra hypotheses.
- **R3**: `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witness of `BlocksBounded F` has a source run ending in `ub`. Whether these hypotheses are needed for a refinement criterion is not examined here. `BehEquiv` compares event sequences and outcomes from each entry; it says nothing about step counts, code size, stack depth or performance. `F.caps = G.caps` is equality of lists (order and multiplicity matter), not equality as sets; `p.abi` is an arbitrary function of the list. Whether set-equal, order-distinct lists suffice is not examined (no counterexample for them is proved here). No destination-mode theorem under `CapsSubset` (the analogue of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` or `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`) is stated or refuted here. One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined. `CleanupClosed` and `DestNotReadInCleanup` are syntactic sufficient conditions; liveness of the destination on the unwind path is not modelled. rustc's inliner uses a plain-local destination directly (inline.rs L919-928) and contains no such syntactic check in inline.rs; whether MIR's own invariants (for example that the destination is not initialised on the unwind edge of a call) exclude cleanup code that reads the destination is not examined here. Says nothing about destinations with projections (rustc borrows those through a temporary, inline.rs L901-917); the toy has plain locals. The toy has no `catch` or search-phase unwinding, no double-panic rule beyond explicit `terminate` actions, no projections, borrows, storage markers, generics, recursion limits or debug information; values are unbounded naturals (`Rvalue.add` does not wrap); a missing call argument is read as `0` and extra arguments are ignored (`argOr`, `bindArgs`).
- **R4**: `TerminalHolds P p e` holds vacuously, for every `P` (including `fun _ => False`), when the run from `e` never halts; so it transfers partial correctness and says nothing about termination. Applies to predicates of the observation (`Obs`: emitted events and outcome) under the reference caller-location policy (`run` uses `.walk`) from one entry; internal state (local values, stack depth, visited blocks), relations between different entries, liveness, step counts and resource use are not covered. Combined with `inline_behEquiv_retTemp_of_capsEq` (whose conclusion `BehEquiv` gives `BehEquivAt` from every entry) it transfers such conditions between `p` and `inline p f b cfg` under that theorem's hypotheses (a composition of two proved theorems, not stated as a separate theorem here); it does not say that a condition proved for the inlined program establishes the callee's standalone contract (`inlined_vc_not_callee_contract`).
- **R5**: `SafetyHolds S p e` checks `S` at every step budget `n`, including `n = 0`; the definition does not require `S` to be prefix-closed, so for a predicate that is not, such as "has halted", `SafetyHolds` requires the initial configuration to be halted already, and such predicates need not transfer (`cex_safety_prefixClosed`). Applies to single-entry predicates of the observation under `run` (policy `.walk`); hyperproperties (relating several entries or runs), liveness and termination properties, internal-state invariants and other caller-location policies are not covered.
- **R6**: One instance: a verification condition proved for an inlined caller need not hold for the callee's standalone entry, because the inlined code is executed with the call-site arguments. It does not say every such condition fails for the callee.
- **R7**: Shows that `CapsSubset` cannot be dropped from the two subset-guard theorems in the toy (with every other hypothesis kept); it does not show that it suffices — it does not (`capsSubset_guard_insufficient`). The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled. In the toy a missing capability is a deterministic fault (`capFault`); the Rust Reference makes calling code compiled with a feature the platform does not support undefined behaviour (codegen.md L462-465).
- **R8**: `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witnesses of `BlocksBounded F` (source `ub`), `CapLegal G` (`cex_capLegal`: source `capFault`, inlined normal return) and `ci.abiSensitive = false` (`cex_callAbiSensitive`: source garbled argument `6`, inlined `5`) all have a source execution that the toy treats as a defined outcome but that a criterion treating capability faults and ABI mismatches as undefined behaviour would not constrain. Whether these hypotheses are needed for a refinement criterion is not examined here. Stated for the temporary return mode (`cfg.ret = .temp t`); no destination-mode companion under `CapsSubset` is established or refuted here. The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled. `CapsSubset` is list inclusion of capability lists. One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined.
- **R9**: `BehEquiv` is equality of maximal observations, including the outcomes `ub`, `capFault` and `aborted` and argument values changed by ABI garbling, in both directions — the "Bisimulation" notion of Leroy (2009, Section 2.1, Definition 1), not a refinement that lets the inlined program differ where the source goes wrong (as CompCert's `forward_simulation` for safe programs or CakeML's `compile_prog_semantics` under the premise `≠ Fail` allow). The tightness witnesses of `BlocksBounded F` (source `ub`) and `CapLegal G` (`cex_capLegal`: source `capFault`, inlined normal return) have a source execution that a criterion treating these outcomes as undefined behaviour would not constrain. Whether these hypotheses are needed for a refinement criterion is not examined here. Stated for the temporary return mode (`cfg.ret = .temp t`); no destination-mode companion is established or refuted here. The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled. `inline_behEquiv_retTemp_of_capsEq` (equal lists) is not a corollary of this theorem: it does not assume `CapLegal G`. One inlining step. `inline p f b cfg` replaces function `f` and leaves the callee `G` in `p.fns`, so this says nothing about removing `G`. `IsCallSite` allows direct self-recursion (`ci.callee = f`) and call sites inside cleanup blocks; no claim is made about termination of an inlining pass. For applying an inlining theorem again to the result: preservation of `ScopesWF` (`scopesWF_inlineFn`) and of `LocalsBounded` (`localsBounded_inlineFn`) is proved; `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); preservation of `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` is not examined.
- **R10**: Escape hatches (each removes this counterexample; (a) is backed by the proved theorems it names, while (b) and (c) are not modelled here): (a) add `AbiAgree p F G` (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`), `AbiInsensitive G` (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive`) or require equal capability lists (`inline_behEquiv_retTemp_of_capsEq`); (b) change the IR so that each call carries its own ABI or feature annotation instead of inheriting the ABI class of the enclosing function's capabilities (not modelled here); (c) check ABI compatibility per call actually present in the callee and per argument type, as LLVM's `X86TTIImpl::areInlineCompatible` does, instead of one global comparison (not modelled here). The refuted universal is the temp-mode statement (`cfg.ret = .temp t`); the same instance also fails in destination mode (`cex_capsAbi`), but no destination-mode universal is stated here. Positive control: with the capability-independent ABI map of `abiPc`, the same call site satisfies every hypothesis of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`, and the inlined program is behaviourally equivalent to the original from every entry (`capsSubset_guard_positiveControl`, proved). The garbling `v ↦ v + 1` is a toy stand-in for a calling-convention mismatch. The ABI model is one program-wide map `p.abi : CapSet → Bool` on capability lists. It does not depend on argument or return types or on the individual call (LLVM's `areTypesABICompatible` does), it need not respect set equality of lists or any implication between capabilities (the Rust Reference counts implicitly enabled features, codegen.md L475), and a mismatch garbles every argument deterministically (`v ↦ v + 1`). Capabilities affect only `needCap` statements and ABI-sensitive calls; instruction selection and other code-generation effects of target features are not modelled.
- **R11**: Together with `locValue_inline_callerScope`, `scopesWF_inlineFn` and `localsBounded_inlineFn` this is the scope part of the inductive step for nested inlinings; the induction itself, and the whole-program statement (`inline_behEquiv_retTemp_of_capsEq`), are separate. `ScopeTreeWF` requires every link to point to a strictly smaller index, which is stronger than acyclicity (`scopeParentsBelow_neg`: an acyclic table with a link to a larger index is rejected). A callsite scope `ci.scope` outside the host table is treated on both sides as the end of the chain, so the answer falls back to `il.getD ci.span`. Closures, function-pointer and trait-object shims (Rust Reference attributes.codegen.track_caller.decay, codegen.md L1046-1050) and lexical `parent_scope` chains are not modelled. The caller-location value is a span; file/line/column structure and the Reference's statement that the information is a hint are not modelled.
- **R12**: Holds for every `LinkRule`, including the wrong `LinkRule.ignoreParent`, so it does not validate the scope-link rule (that is `locValue_inline_calleeScope` with `hlink`). The hypothesis `s < F.scopes.length` restricts the statement to host scopes; for `s` at or beyond the host table the value can change (`cex_walkCaller_s`).
- **R13**: Holds for every `cfg` (including the wrong `LinkRule.ignoreParent`, a wrong `resumeMap` or overlapping slots) and for any `ci` (not required to be `B`'s call), so `ScopesWF` preservation does not validate the semantic correctness of scope linking or of the splice. The callee's scope 0 need not be clean (`linkScope` overwrites it); `ScopesWF G`, as assumed by the inlining theorems, implies both callee hypotheses. Of the other hypotheses that the inlining theorems assume and that a further inlining step would have to re-establish, `LocalsBounded` preservation is proved (`localsBounded_inlineFn`) and `BlocksBounded` preservation fails when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`); `CleanupClosed`, `DestNotReadInCleanup`, `CapLegal` and `AbiInsensitive` preservation is not examined.
- **R14**: Refutes `.innermost` on one two-level tracked-chain instance from one entry. It does not show that `.walk` is the only policy that preserves behaviour, and it does not show that `.innermost` fails for single-level inlining into an untracked host (not examined here).
- **R15**: Refutes `.outermost` on one two-level instance with an untracked wrapper, from one entry. It does not show that `.walk` is the only policy that preserves behaviour, and it does not show that `.outermost` fails when every intermediate inlined callee is tracked (not examined here).
- **R16**: Varies only the branch of `linkScope` for the outermost callee scope (`j = 0`) when the callsite scope is not inlined; the branch for an inlined callsite scope (`c.inlined.isSome`) and the rule linking inner callee scopes without `inlinedParent` to the outermost callee scope (`none => some ns`) are not varied here. `linkP1 = inlineCanon linkP0 0 0` (`linkP1_eq`). The walk-level form of the same failure is `cex_walkCallee_link`.
- **R17**: A structural reference point: it composes equivalences but does not mention `inline`. It does not re-establish the hypotheses of the inlining theorems on an intermediate program; for that, `scopesWF_inlineFn` and `localsBounded_inlineFn` are proved, `BlocksBounded` can fail (`cex_blocksBounded_inlineFn_oob`), and the remaining hypotheses must be checked on each intermediate program. Says nothing about whether different inlining orders produce the same program; in this toy they need not (`inline_order_changes_body`), and whether they agree up to renaming of locals, blocks and scopes is unknown.
- **R18**: A reference point about this toy's conventions: the difference comes from the prologue zero-initialising every callee local (the first order initialises the inner callee's slots twice); it is not a statement about any real inliner. Compares function `0` (`h`) only; `ordQ1` also replaces `f` (function `1`) while `ordQ2` leaves it unchanged (`inline_order_other_fns`). Behavioural equivalence is shown from the single entry `e0`, not from every entry. Equality up to renaming and dead-statement removal is not examined (unknown).
- **R19**: Says nothing about behaviour; it is one of the side conditions for applying the inlining theorems again. `BlocksBounded` is not preserved when the callee jumps out of range (`cex_blocksBounded_inlineFn_oob`). `inlineFn_nlocals_covers_retTemp` checks the edge case of a callee with no locals in temp mode (new count `2` for one host local). Holds for every configuration `cfg`, including slot maps that are not fresh or not injective (`SlotsFresh`, `SlotsInjective` are not assumed) and the wrong rewriting variants, so it does not validate the renaming. In temp mode (`cfg.ret = .temp t`) the declared-local count includes `t + 1` (`retTempSucc cfg`) even when `ci.target = none`, where `inlineFn` adds no return block and nothing reads the temporary; the count is an upper bound, not the least bound.

### Escape hatches from the impossibility result

`capsSubset_guard_insufficient` (R10) refutes "caller ⊇ callee" with `CapLegal G` and a non-ABI-sensitive inlined call as a sufficient guard, in temp mode. Each of the following removes its counterexample: (a) add `AbiAgree p F G` (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`), `AbiInsensitive G` (`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive`) or require equal capability lists (`inline_behEquiv_retTemp_of_capsEq`); (b) change the IR so that each call carries its own ABI or feature annotation instead of inheriting the ABI class of the enclosing function's capabilities (not modelled here); (c) check ABI compatibility per call actually present in the callee and per argument type, as LLVM's `X86TTIImpl::areInlineCompatible` does, instead of one global comparison (not modelled here).

### Hypotheses whose tightness is not established

- The links-point-below conjuncts (`ScopeParentsBelow F.scopes`, `ScopeParentsBelow G.scopes`) of `ScopesWF F` and `ScopesWF G` in R2, R3, R8 and R9: tight for the scope-walk theorems (`cex_walkCallee_F`, `cex_walkCaller_F`, `cex_walkCallee_Gparents`); a program-level witness is not given (unknown).
- The clean-scope-`0` conjunct of `ScopesWF F` in R2, R3, R8 and R9: unknown as a ledger status (no counterexample is given, and no theorem without it is stated). The proofs of R2, R3, R8 and R9 do not use it, and R11 and R12 are proved without it.

### Unknown questions

- **Unknown:** whether inlining `g` into `f` and then `f` into `h` gives the same body for `h` as the reverse order up to renaming of locals, blocks and scopes and removal of redundant initialisations. In this toy the two bodies are not syntactically equal (`inline_order_changes_body`).

### Known not to apply

- **Known not to apply (in the toy, proved):** "caller ⊇ callee" with `CapLegal G` and a non-ABI-sensitive inlined call is not a sufficient guard (`capsSubset_guard_insufficient`, witness `capsSubset_guard_insufficient_witness`); a verification condition proved for an inlined caller is not the callee's contract (`inlined_vc_not_callee_contract`); the innermost- and outermost-span policies are not the implicit-argument semantics on the instances of `innermost_policy_wrong_for_tracked_chain` and `outermost_policy_wrong_for_untracked_wrapper`; the `ignoreParent` link variant breaks two-level inlining (`linkRule_ignoreParent_changes_location`); `BlocksBounded` is not preserved by `inlineFn` (`cex_blocksBounded_inlineFn_oob`).

### Disproved, dropped or unresolved statements

None. Every result listed in `results.json` is proved as stated; no statement was weakened, disproved or dropped.

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4:v4.34.1` (GitHub tag `v4.34.1` of `leanprover/lean4` = commit `5045d0056413266e57c625dcd7c365b10e377c52`, a lightweight tag read from the GitHub API on 2026-11-21). The project builds with no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations and no warnings about `sorry`. `audit/axioms.json` records `collectAxioms` for all 1423 package declarations; each depends on at most `propext` and `Quot.sound`. `audit/statements.json` records, for each of the 336 Lean names referenced by `results.json` (results, auxiliary declarations, counterexamples, non-vacuity witnesses and positive controls), the SHA-256 of its statement (Lean `repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement, theorem bodies excluded). The main theorem of each result:

| Result | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- | :--- |
| R1 | `frameRel_step_of_injective_of_avoids` | propext | `93320ca43dd983c017300580f844299b8d102c7ff5cbcb0d53320df59e4a3416` | `d3522b3f14179fb5d35580bd8af8a24f7bc579ab816f292e0bfcb382d20f33f7` |
| R2 | `inline_behEquiv_retTemp_of_capsEq` | Quot.sound, propext | `a7ee31f4180d61ec45c7384decc42123555e3518b5ab6fca8f7681e275751162` | `6f3566794383c007e79ef29b0e7910e70ccfceeea3a96d3a7c025fcf8bf215c0` |
| R3 | `inline_behEquiv_retDest_of_destUnobservedOnUnwind` | Quot.sound, propext | `6b3d8ca295c6a93457fb2089a816840d96369678df6ca1a2ac53daa7e2ec960d` | `69ad2da512728e9e2cdd277f4cfd527bd37759ea9815f41b6dfa5d3c53ccfcc7` |
| R4 | `terminalHolds_iff_of_behEquivAt` | propext | `809f33dc90ab1591a950bb38999e83ead4645aa3caad66da3bfcd994631f2e60` | `d9fddd9e17f33d83ab7ffb404efa35acfa65fd08c2821c7eff5a89efecee7a35` |
| R5 | `safetyHolds_iff_of_behEquivAt_of_prefixClosed` | propext | `a47f4a2878ab9a4e2b58a230c95669264ee0b8005638b4e94087bd6eac7aea82` | `89b4c08636ef4b2a17b90d4ccd6fd8f3bab28e6918bf1bc975bd11382b2a0875` |
| R6 | `inlined_vc_not_callee_contract` | Quot.sound, propext | `b26c04b154899accb5c597ab90c97a90265a8a2212a039a68666f714a0b4649f` | `f68df996de99927d0696887117e40d6bdc09343239c4462a5b3405cd63502e7e` |
| R7 | `capsSubset_needed_inlined_needCap_faults` | Quot.sound, propext | `4edebd87cd535ec4d886057fea1957bc6eede44c23102e9451a6d9261a407dce` | `5dce398a77056db394ba90022d56c2474d822da25e65c4caa4056cd0298922bf` |
| R8 | `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` | Quot.sound, propext | `f68fe4ba53d2127c5b4fb317b6489947844c9b52a95a3ba825cb3e1de05f4881` | `41b8c74637198f4cb94efbd56f66dfd6ef0a73139c7aa8f1a28d48683c71c4af` |
| R9 | `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree` | Quot.sound, propext | `73fa5b5c7cb6474e145f6b10b4bba7ee4012787f7bb1d5f0ca4c2fbb778a6ff6` | `2c95eebc99751d48146d64df82571a281c6ddeee6482292919bd54034859de23` |
| R10 | `capsSubset_guard_insufficient` | Quot.sound, propext | `e3fbc61309ce758a6fc7d79619dc3ba52da9ce84a4ed1c95f17891f339047d3a` | `103f7e7c8cf5159f6415061da9418bd2f836c61383dd96007b9edc958d0b5e6a` |
| R10 | `capsSubset_guard_insufficient_witness` | Quot.sound, propext | `ba302a65d254144fa3b066353f3b787843fbf7b3f6e52f4e94c759bb375195d9` | `856f33af336703b9dcbd904a5535258dc4c5e81923711faf8b8d92da7591150d` |
| R11 | `locValue_inline_calleeScope` | Quot.sound, propext | `83d2e6ace56298f6aa9dda0c44627eb576d957e325f7ac0c43e621a413b402ed` | `8ee8c24b47fdb69e91df7522ce81bf471cb97b04b5fde32ae6d9d141afa3d225` |
| R12 | `locValue_inline_callerScope` | Quot.sound, propext | `1bb4479251a64bae4ec98c40730f4fcb82dcd2674e7fa2b75731d2ea1f362849` | `aafd13e675c43afdb934f162cb4721bcc1e78daa18eb8fbd8bb76ac0eff52f46` |
| R13 | `scopesWF_inlineFn` | Quot.sound, propext | `0db5eb766407e16a84c8984296ea5fa7ff69c79061caec392ad854f2fad3231e` | `55e303bc2e0a8cac4511f1f49251b30ab5be4c5cb65305b23983085cbf81f8d9` |
| R14 | `innermost_policy_wrong_for_tracked_chain` | Quot.sound, propext | `7579ab4cdc5b89f263bf3490ea3be252774505a3833dcb36a58913cc110f1c14` | `a88c3b040e3525d0d01562d3a00b6d542ffaa82f545e3c920c2b556266b51cc6` |
| R15 | `outermost_policy_wrong_for_untracked_wrapper` | Quot.sound, propext | `f4b842f53e84db15e8e3d81732727600038305c9b624d00f6cb140831c7fa7c6` | `a88c3b040e3525d0d01562d3a00b6d542ffaa82f545e3c920c2b556266b51cc6` |
| R16 | `linkRule_ignoreParent_changes_location` | Quot.sound, propext | `36e4ea4dfe54c383935ccef6f0946038922f43490ddd59ab5b4404a136966ba5` | `22cbb7e91023ec0dc88b1155e424178ce945f148db0a08f8917197d32f47bdaf` |
| R17 | `behEquiv_trans` | propext | `ff1026b430a709b717549a5793679bde8f367c796421b41e8af02f423194d19a` | `0ee1e128e1913e0eeb9f06aa6a92b3f0e9a61065b21138dc54c1ecac8d925f8c` |
| R18 | `inline_order_changes_body` | Quot.sound, propext | `b8da3cd5d6396fd2437454496271544218385ea4e3166a7884fd5ead0db16865` | `7a02657eebb2ae82750d98de48896e2d1453937c240178a44724fe4188fd22df` |
| R19 | `localsBounded_inlineFn` | Quot.sound, propext | `91614053c932e278625152a92c1dcdb613c66b82e473eb1b7f7aebdec4986f99` | `5818a9af2be04fbe78e249953881f75062bcb2824b205d438a432b040b6f780a` |

The proofs of R2, R3, R8 and R9 are in `lean/ToyInline/Results.lean` and rely on the auxiliary development in `lean/ToyInline/Simulation.lean`, which adds definitions used only inside proofs and changes no definition in any statement's closure.

### Primary sources

All verified at the pinned revision or DOI on 2026-11-21 (revisions resolved through the GitHub API):

- rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`: `compiler/rustc_mir_transform/src/inline.rs` (line ranges quoted in the cards and the modeling bridge) and `compiler/rustc_middle/src/mir/mod.rs` L683-715.
- rust-lang/reference commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/attributes/codegen.md` (line ranges quoted in the cards).
- rust-lang/rfcs commit `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/2091-inline-semantic.md` (RFC 2091, implicit caller location) and `text/2396-target-feature-1.1.md` (RFC 2396, `#[target_feature]` 1.1).
- AbsInt/CompCert v3.18 = commit `14d616046360a0b2611ebdfc2f98368af402e1f7`: `backend/Inlining.v`, `backend/Inliningproof.v`.
- llvm/llvm-project tag `llvmorg-21.1.0` (tag object `827731c0bf12b0ce8d70e15ebf9f731e7961fe51`) = commit `3623fe661ae35c6c80ac221f14d85be76aa870f1`: `llvm/lib/Transforms/Utils/InlineFunction.cpp`, `llvm/lib/Target/X86/X86TargetTransformInfo.cpp`, `llvm/include/llvm/Analysis/TargetTransformInfo.h`.
- CakeML/cakeml commit `16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9`: `compiler/backend/bvl_inlineScript.sml`, `compiler/backend/proofs/bvl_inlineProofScript.sml`.
- Xavier Leroy, "A formally verified compiler back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4.
- Yong Kiam Tan, Magnus O. Myreen, Ramana Kumar, Anthony Fox, Scott Owens and Michael Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29:e2, 2019, doi:10.1017/S0956796818000229.
- Bowen Alpern and Fred B. Schneider, "Defining liveness", Information Processing Letters 21(4):181–185, 1985, doi:10.1016/0020-0190(85)90056-0.
- Simon Peyton Jones and Simon Marlow, "Secrets of the Glasgow Haskell Compiler inliner", Journal of Functional Programming 12(4–5):393–434, 2002, doi:10.1017/S0956796802004331 (a bibliographic pointer only).
- Martin Desharnais, "A Generic Framework for Verified Compilers", Archive of Formal Proofs, February 2020, https://isa-afp.org/entries/VeriComp.html.

Exact line ranges and verbatim quotes for each source are given with the card that cites it.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` in the sources, computes `collectAxioms` for every package declaration (allowed: `propext`, `Classical.choice`, `Quot.sound`), and recomputes for every Lean name referenced by `results.json` (and every name recorded in `audit/statements.json`) the SHA-256 of the statement (Lean `repr` of the type) and of the definition closure (types and values of every package constant reachable from the statement; theorem bodies excluded), comparing them with `audit/statements.json`. Exit status 0 means that every check passed.

A narrower manual check, from the package directory:

```sh
cd lean
lake build
lake env lean axioms_audit.lean
```

`lean/axioms_audit.lean` is outside the library target; it runs `#print axioms` for every Lean name referenced by `results.json`. Every line must list at most `propext` and `Quot.sound` (in particular, no `sorryAx`). To check the four whole-program inlining theorems alone:

```sh
cd lean
cat > /tmp/InlineAxioms.lean <<'EOF'
import ToyInline
#print axioms Toy.Inline.inline_behEquiv_retTemp_of_capsEq
#print axioms Toy.Inline.inline_behEquiv_retDest_of_destUnobservedOnUnwind
#print axioms Toy.Inline.inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive
#print axioms Toy.Inline.inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree
EOF
lake env lean /tmp/InlineAxioms.lean
```

After a change to the model, rerun `support/revalidate.py`: a change to any definition in a statement's closure changes its closure hash, and the script reports which statements are affected. For the modeling bridge, re-read the cited line ranges at the pinned revisions.
