# Law-dependent rewrites after capture: safe vs unsafe trait laws and relational semantics

## Summary

**Scope.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR. Real systems appear in a separately labelled `derived (modeling bridge)` subsection under `## Applicability` citing documented behaviour and source at pinned public revisions.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

- **`law-on-reached-calls-suffices` (`refinesPP_capDirect_apply_of_lawOnReached`, T1):** For every environment `env`, relies position `pos`, call-free inline rewrite `ρ`, straight-line program `p`, and store `σ`, if `LawOnReached env ρ p σ` holds (each targeted call reached by the law-free execution of `p` from `σ` obeys `env.impl i v = ρ.repl i v`), then `compiled env (ρ.apply p) σ` prefix-preservingly refines `capDirect env pos p σ`.
- **`contextual-refinement-iff-pointwise-context-safety` (`refinesPP_every_context_iff_contextSafeAt`, T1):** For every fixed `env`, `pos`, and call-free inline rewrite `ρ`, `compiled env (ρ.apply p) σ` prefix-preservingly refines `capDirect env pos p σ` for every straight-line program `p` and initial store `σ` iff `ContextSafeAt env pos ρ i v` holds at every targeted instance `i` and argument `v` (assuming `capDirect` encodes unsafe contract violations as operational UB via `directCalls`).
- **`safe-target-refinement-on-probe-forces-law` (`lawAt_of_refinesPP_probe_of_safe_of_targets`, T1):** For every `env`, `pos`, `ρ`, `i`, `v`, and `σ`, if `env.safety i = .safeTrait`, `ρ.targets i = true`, and `compiled env (ρ.apply (probe i v)) σ` prefix-preservingly refines `capDirect env pos (probe i v) σ`, then `LawAt env ρ i v` holds.
- **`nontrivial-clone-breaks-copy-rewrite` (`cex_nontrivial_clone_copy_rewrite`, T1):** In `envSafeLog` from `σ0`, `cloneToCopy` satisfies `ReplIsContract`, violates `LawOnReached` on `probe 0 5`, and breaks both prefix-preserving refinement (at relies point `before`) and whole-trace refinement (at relies point `after`).
- **`unsafe-relies-before-rewrite-refines-without-law` (`refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract`, T1):** If `TargetsUnsafe env ρ` and `ReplIsContract env ρ` hold (in the `capDirect` model where unsafe contract violations trigger UB at the call), then for every straight-line program `p` and store `σ`, `compiled env (ρ.apply p) σ` prefix-preservingly refines `capDirect env .before p σ` with the relies point `before` the impl and with no law hypothesis on `env.impl`.
- **`relies-after-effect-breaks-lawless-refinement-under-prefix-ub` (`cex_relies_after_effect_not_refined`, T1):** In `envUnsafeLog` with `cloneToCopy` on `probe 0 5` from `σ0`, `TargetsUnsafe` and `ReplIsContract` hold, yet with the relies point `after` the impl's effect `9`, `capDirect` is `[.ub [9]]`, `compiled` is `[.done [5]]`, and prefix-preserving refinement fails while whole-trace refinement holds.
- **`whole-trace-ub-unsafe-rewrite-refines-either-position` (`refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract`, T0):** Under `TargetsUnsafe env ρ` and `ReplIsContract env ρ` (with `capDirect`'s relies-point UB injection), for either relies position `pos`, `compiled env (ρ.apply p) σ` refines `capDirect env pos p σ` in the whole-trace sense (`RefinesWT`) for every `p` and `σ`.
- **`ub-free-verification-transfers-through-unsafe-contract-rewrite` (`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`, T0):** Under `TargetsUnsafe env ρ`, `ReplIsContract env ρ`, and `UBFreeSpec spec`, if `Sat (capDirect env pos p σ) spec` holds (where `capDirect` injects UB on unsafe contract violations), then `Sat (compiled env (ρ.apply p) σ) spec` holds.
- **`ub-free-verification-discharges-contract-at-reached-unsafe-calls` (`contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`, T1):** For every `env`, `pos`, `p`, `σ`, `spec`, `i`, and `v`, if `env.safety i = .unsafeTrait`, `Reaches env p σ i v`, `UBFreeSpec spec`, and `Sat (capDirect env pos p σ) spec` hold, then `env.impl i v = env.contract i v`.
- **`relational-capture-sound-for-every-partial-rewrite` (`sat_compiled_applyAt_of_sat_capRel`, `sat_compiled_and_apply_of_sat_capRel`, T0):** In the law-free semantics (`capRel` and `compiled`, which ignore `env.safety` and `env.contract`), if `Sat (capRel env [ρ] p σ) spec` holds, then `Sat (compiled env (ρ.applyAt S 0 p) σ) spec` holds for every site selection `S : Nat → Bool` (including `p` and `ρ.apply p`).
- **`relational-capture-weakest-for-per-site-rewriting` (`mem_capRel_iff_exists_applyAt`, `capRel_subset_of_sound_for_every_applyAt`, T1):** For straight-line programs (where each syntactic site executes at most once), `b ∈ capRel env [ρ] p σ` iff `b ∈ compiled env (ρ.applyAt S 0 p) σ` for some `S : Nat → Bool`, and every `D : Beh → Prop` sound over all predicates `spec : Beh → Prop` and all site selections `S` contains `capRel env [ρ] p σ` (whereas `capRel` is not weakest for all-or-nothing `ρ.apply`: `cex_capRel_not_weakest_for_all_or_nothing`).
- **`fail-closed-rejection-of-rewritable-calls-sound-and-incomplete` (`capRejectRewritable_compiledDen_transferSound`, `capRejectRewritable_incomplete`, T0):** If `∀ i, ρ.targets i = true → R i = true` and `VerifierSound (compiledDen env) verified` (for the law-free semantics `compiledDen`), then `TransferSound` holds through `capRejectRewritable R` to `fun p => compiledDen env (ρ.apply p)`, while `capRejectRewritable cloneToCopy.targets` rejects `probe 0 5` even in `envSafeTriv`.
- **`rewrite-sequence-refines-of-laws-on-reached-calls` (`refinesPP_capDirect_applySeq_of_lawOnReached`, T0):** For call-free inline rewrites `ρs`, if `∀ ρ ∈ ρs, LawOnReached env ρ p σ`, then `compiled env (applySeq ρs p) σ` prefix-preservingly refines `capDirect env pos p σ`.
- **`disjoint-rewrite-sequence-contextual-iff-conjunction` (`refinesPP_every_context_applySeq_iff_of_pairwise_disjoint`, T1):** For call-free inline rewrites `ρs` satisfying `ρs.Pairwise TargetsDisjoint`, `applySeq ρs` prefix-preservingly refines `capDirect env pos` over every straight-line program `p` and store `σ` iff every `ρ ∈ ρs` satisfies `ContextSafeAt env pos ρ i v` at all targeted `i` and `v`.
- **`relational-capture-of-rewrite-list-covers-every-covered-sequence` (`mem_capRel_of_mem_compiled_applySeq_of_coveredBy`, T0):** In the law-free semantics, if `∀ ρ ∈ ρs', CoveredBy ρs ρ`, then every behaviour in `compiled env (applySeq ρs' p) σ` belongs to `capRel env ρs p σ`.

Every claim above is subject to the scope and modeling guardrails in the per-card non-claims below — most importantly: (1) the unsafe-trait refinement and UB-free transfer results (`capDirect`) hold because `directCalls` explicitly injects operational UB at every unsafe call whose impl violates its single-call pointwise `env.contract`, whereas a verifier that captures user impl bodies without encoding the unsafe trait's contract as a relies-point UB check is in the `safeTrait`/`compiled` regime (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`); and (2) the relational-capture and fail-closed remedies (`capRel`, `compiledDen`) are proved over law-free semantics that ignore `env.safety` and `env.contract` (`capRel_unsafe_ignores_contract_example`, `cex_capRejectRewritable_not_transferSound_for_capDirect`).

## Applicability

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.

**Model fidelity and semantic regimes.**
- **Language fragment:** Programs (`Prog`) are finite straight-line lists of statements over a total store `Store = Var → Val` (`Val = Nat`), without loops, branches, recursion, pointers, or unwinding. Each statement position executes at most once, which makes static per-site selection (`Rewrite.applyAt`) coincide with dynamic per-call choice (`capRel`).
- **Trait contracts vs. rewrite laws:** `Env` equips each instance `i` with a total deterministic user `impl : Val → List Val × Val`, a single-call stateless `contract : Val → List Val × Val` (the behaviour prescribed by `i`'s trait), and a `Safety` mark (`safeTrait` or `unsafeTrait`). Separately, `LawAt env ρ i v` (`env.impl i v = ρ.repl i v`) states that `i`'s impl agrees with rewrite `ρ`'s inline replacement `ρ.repl i` at `v`. They coincide when `ReplIsContract env ρ` holds.
- **Direct capture (`capDirect`) vs. law-free semantics (`compiled`, `capRel`):** `capDirect` (`directCalls`) executes `env.impl i v` on `safeTrait` calls and, on `unsafeTrait` calls where `env.impl i v ≠ env.contract i v`, emits `.ubAfter` at relies position `before` or `after`. By contrast, `compiled` (`compiledCalls`) and `capRel` (`relCalls`) never inspect `env.safety` or `env.contract` and never emit relies-point UB. Consequently, Remedy 1 (discharging unsafe contracts via UB-free verification of `capDirect`) requires the verifier's captured semantics to encode unsafe contracts as UB checks, whereas Remedies 2 and 3 (`capRel` and `capRejectRewritable` over `compiledDen`) transfer specifications to `compiled` without checking unsafe contracts.

**Toolchain, dependencies, and `REPORT.json` subject relationships.**
- **Mechanization environment:** Namespace `Toy.LawRewrite` (with self-contained capture-bridge definitions in `Toy.LawRewrite.CaptureBridge`), verified under `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) using core Lean alone (no Mathlib, no external Lake packages). Every theorem, lemma, definition example, counterexample, positive control, and non-vacuity witness in `lean/` is kernel-checked without `sorry`, `admit`, or `native_decide`. Every Lean code fence in this report is a verbatim quote of the package source under `lean/`, labelled `-- path:lines` (with proofs elided as `:= …` or `:= by …`).
- **How `REPORT.json` subjects relate:** `leanprover/lean4` (`v4.34.1`) is the kernel that checks the `Toy.LawRewrite` mechanization. `rust-lang/rust` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) is inspected only in `### Modeling bridge — derived (modeling bridge)` to document motivating safe-trait (`Clone`/`Copy`), codegen-rewrite (`optimize_use_clone`), and unsafe-trait (`TrustedLen`) patterns, with `Model–system relation: none proved`. `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`) and the primary research publications listed in `REPORT.json` define the prior-art refinement, rewrite-rule, deductive-verification, and nondeterministic-over-approximation concepts restated or contrasted in the `T0` and `T1` cards.

### Definitions

Every package-local `def` or `abbrev` value/predicate appearing in any card's verbatim `lean` theorem statement (together with its direct semantic helpers), classified by how the package pins down its meaning:

| Definition | Status | Design choice / convention |
| :--- | :--- | :--- |
| `Val` | transparent | Alias `Nat` for variable and trace-event values. |
| `Inst` | transparent | Alias `Nat` for single-method trait instance identifiers. |
| `σ0` | transparent | Constant-zero initial store `fun _ => 0`. |
| `probe` | transparent | Three-statement context `[.set 0 v, .call i 1 0, .out 1]` observing both emitted call effects and returned value. |
| `cloneToCopy` | tests: `apply_pos`, `apply_neg` | Rewrites calls of instance `0` to inline `copyImpl` (`fun v => ([], v)`) and leaves other instances unchanged. |
| `envSafeTriv` | transparent | Concrete all-safe environment with `copyImpl` as both `impl` and `contract`. |
| `envSafeLog` | transparent | Concrete all-safe environment with effectful `loggingClone` as `impl` and `copyImpl` as `contract`. |
| `envUnsafeLog` | transparent | Concrete all-unsafe environment with effectful `loggingClone` as `impl` and `copyImpl` as `contract`. |
| `Rewrite.apply` | tests: `apply_pos`, `apply_neg` | Maps `Rewrite.rwStmt` once over `p`, turning targeted `call` statements into call-free `prim` statements. |
| `Rewrite.applyAt` | tests: `applyAt_example`, `cex_capRel_sound_unverified` | Indexes statements from `0` and rewrites position `k` iff `S k = true` (targeting still gated by `ρ.targets`). |
| `applySeq` | characterized: `applySeq_eq_firstMatch` | Left fold of single-rewrite passes, algebraically equal to one pass of `firstMatch ρs` because replacements introduce no calls. |
| `firstMatch` | tests: `firstMatch_pos`, `firstMatch_neg` | Selects the earliest rewrite in `ρs` with `targets i = true` (`List.find?`), defaulting untargeted `repl` to `copyImpl`. |
| `compiled` | tests: `compiled_example`, `cex_nontrivial_clone_copy_rewrite` | Executes every `call i` via `env.impl i` without inspecting `env.safety` or `env.contract`. |
| `capDirect` | tests: `capDirect_unsafe_lawful_example`, `cex_without_targetsUnsafe` | Runs `env.impl` on `safeTrait` calls and injects operational UB at `pos` (`before` or `after` impl effects) when an `unsafeTrait` call violates `env.contract`. |
| `capRel` | tests: `capRel_unsafe_ignores_contract_example`, `cex_capRel_not_weakest_for_all_or_nothing` | Branches nondeterministically at each dynamic call between `env.impl i` and every matching `ρ.repl i` in `ρs`, ignoring `env.safety` and `env.contract`. |
| `ImprovesPP` | tests: `improvesPP_pos`, `improvesPP_neg` | Target-first argument order (`ImprovesPP bt bs`): `bt = bs`, or `bs = .ub t` with prefix `t <+: bt.trace`. |
| `ImprovesWT` | tests: `improvesWT_pos`, `improvesWT_neg` | Target-first argument order (`ImprovesWT bt bs`): `bt = bs`, or `bs = .ub t` for any trace `t` without prefix preservation. |
| `RefinesPP` | tests: `refinesPP_pos`, `refinesPP_neg` | Source-first argument order (`RefinesPP src tgt`): every target behaviour `bt ∈ tgt` `ImprovesPP`-improves some `bs ∈ src`. |
| `RefinesWT` | tests: `refinesWT_pos`, `refinesWT_neg` | Source-first argument order (`RefinesWT src tgt`): every target behaviour `bt ∈ tgt` `ImprovesWT`-improves some `bs ∈ src`. |
| `Toy.LawRewrite.Sat` | tests: `sat_pos`, `sat_neg` | Universal satisfaction `∀ b ∈ bs, spec b` over finite behaviour lists (including `.ub` entries unless excluded by `spec`). |
| `UBFreeSpec` | tests: `ubFreeSpec_pos`, `ubFreeSpec_neg` | Requires `∀ t, ¬ spec (.ub t)` across all UB trace prefixes `t`. |
| `LawAt` | tests: `lawAt_pos`, `lawAt_neg` | Pointwise pair equality `env.impl i v = ρ.repl i v` (both emitted effects and return value), independent of `env.contract`. |
| `Reaches` | tests: `reaches_pos`, `reaches_neg_after_ub` | Reachability along law-free `env.impl` execution: stops at `[]` or `Stmt.ub`, and continues past unsafe contract violations. |
| `LawOnReached` | tests: `lawOnReached_unreached`, `lawOnReached_neg` | Restricts `LawAt env ρ i v` to targeted pairs `(i, v)` satisfying `Reaches env p σ i v` (vacuously true on unreachable calls). |
| `LawOnTargets` | tests: `lawOnTargets_pos`, `lawOnTargets_neg` | Universal law satisfaction `LawAt env ρ i v` across all targeted instances `i` and all arguments `v : Val`. |
| `ContextSafeAt` | tests: `contextSafeAt_pos`, `contextSafeAt_neg_after` | Holds iff `LawAt` holds, or `i` is `unsafeTrait` with `impl ≠ contract` and either `pos = .before` or `(impl).1 <+: (repl).1`. |
| `TargetsUnsafe` | tests: `targetsUnsafe_pos`, `targetsUnsafe_neg` | Requires `env.safety i = .unsafeTrait` for every instance with `ρ.targets i = true`. |
| `ReplIsContract` | tests: `replIsContract_pos`, `replIsContract_neg` | Requires function equality `ρ.repl i = env.contract i` on every instance with `ρ.targets i = true`. |
| `TargetsDisjoint` | tests: `targetsDisjoint_pos`, `targetsDisjoint_neg` | Disjoint target predicates: `ρ₁.targets i = true → ρ₂.targets i = false` for all `i`. |
| `CoveredBy` | tests: `coveredBy_pos`, `coveredBy_neg` | For each `i` targeted by `ρ`, requires some `ρ' ∈ ρs` targeting `i` with `ρ'.repl i = ρ.repl i` across all arguments. |
| `callsSome` | tests: `callsSome_pos`, `callsSome_neg` | Purely syntactic scan returning `true` iff some statement of `p` is `Stmt.call i _ _` with `R i = true` (including unreachable calls). |
| `compiledDen` | tests: `compiledDen_pos`, `compiledDen_neg` | Lifts `compiled env p` to a `Store × Beh` run predicate `fun r => r.2 ∈ compiled env p r.1`. |
| `capDirectDen` | tests: `capDirectDen_pos`, `capDirectDen_neg` | Lifts `capDirect env pos p` to a `Store × Beh` run predicate `fun r => r.2 ∈ capDirect env pos p r.1`. |
| `capRejectRewritable` | tests: `nonvacuity_capRejectRewritable`, `cex_capRejectRewritable_target_outside_R` | Fail-closed guard `failClosed (fun p => callsSome R p = false) id ()` (accepts `[.call 1 1 0]` under `cloneToCopy.targets` in `nonvacuity_capRejectRewritable`, fails `TransferSound` when `R` omits a targeted instance in `cex_capRejectRewritable_target_outside_R`, and returns `Except.error ()` on `probe 0 5` in `capRejectRewritable_incomplete`). |
| `Toy.LawRewrite.CaptureBridge.Sat` | transparent | Universal run satisfaction `∀ b, d b → spec b` over a predicate denotation `d : Den B`. |
| `Toy.LawRewrite.CaptureBridge.DenIncl` | transparent | Denotation inclusion `∀ b, d₁ b → d₂ b`. |
| `Toy.LawRewrite.CaptureBridge.OverApproxOnOk` | transparent | On every `cap p = .ok q`, requires `DenIncl (semS p) (semV q)` (specialized to `failClosed` by `failClosed_overApproxOnOk_iff`). |
| `Toy.LawRewrite.CaptureBridge.VerifierSound` | tests: `nonvacuity_capRejectRewritable`, `cex_capRejectRewritable_unsound_verifier` | Soundness of abstract verdict relation `verified q spec` against `CaptureBridge.Sat (semV q) spec`. |
| `Toy.LawRewrite.CaptureBridge.TransferSound` | tests: `capRejectRewritable_compiledDen_transferSound`, `cex_capRejectRewritable_not_transferSound_for_capDirect` | Transfers `verified q spec` across `cap p = .ok q` to `CaptureBridge.Sat (semS p) spec`, imposing no condition on `.error`. |

### Core definitions, unfolded prose, and concrete instances

#### Language, behaviours and execution

A store maps variables to natural-number values; an `Impl` maps an argument value to emitted observable events and a returned value. `copyImpl` is the identity impl with no emitted events.

```lean
-- lean/Toy/LawRewrite/Basic.lean:29
abbrev Val := Nat
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:31
abbrev Var := Nat
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:33
abbrev Inst := Nat
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:36
abbrev Store := Var → Val
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:39-40
def Store.upd (σ : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else σ y
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:46
abbrev Impl := Val → List Val × Val
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:50
def copyImpl : Impl := fun v => ([], v)
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:55-58
inductive Safety where
  | safeTrait
  | unsafeTrait
  deriving DecidableEq
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:64-67
inductive RelyPos where
  | before
  | after
  deriving DecidableEq
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:73-76
structure Env where
  impl : Inst → Impl
  contract : Inst → Impl
  safety : Inst → Safety
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:85-90
inductive Stmt where
  | set (x : Var) (v : Val)
  | out (x : Var)
  | prim (f : Impl) (dst src : Var)
  | call (i : Inst) (dst src : Var)
  | ub
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:93
abbrev Prog := List Stmt
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:97-100
inductive Beh where
  | done (t : List Val)
  | ub (t : List Val)
  deriving DecidableEq
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:103-105
def Beh.trace : Beh → List Val
  | .done t => t
  | .ub t => t
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:108-110
def Beh.prepend (e : List Val) : Beh → Beh
  | .done t => .done (e ++ t)
  | .ub t => .ub (e ++ t)
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:114-117
inductive CallRes where
  | ret (res : List Val × Val)
  | ubAfter (effs : List Val)
  deriving DecidableEq
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:123-133
def exec (calls : Inst → Val → List CallRes) : Prog → Store → List Beh
  | [], _ => [.done []]
  | .set x v :: p, σ => exec calls p (σ.upd x v)
  | .out x :: p, σ => (exec calls p σ).map (Beh.prepend [σ x])
  | .prim f dst src :: p, σ =>
      (exec calls p (σ.upd dst (f (σ src)).2)).map (Beh.prepend (f (σ src)).1)
  | .call i dst src :: p, σ =>
      (calls i (σ src)).flatMap fun
        | .ret r => (exec calls p (σ.upd dst r.2)).map (Beh.prepend r.1)
        | .ubAfter e => [.ub e]
  | .ub :: _, _ => [.ub []]
```

`exec` is total by structural recursion on `Prog`. Every execution under `compiled` produces a singleton behaviour list (`compiled_singleton`), every execution under `capDirect` produces a singleton behaviour list (`capDirect_singleton`), and every execution under `capRel` produces a non-empty behaviour list (`capRel_ne_nil`).

#### Rewrites

A `Rewrite` replaces calls of targeted instances by call-free inline `Stmt.prim` statements. `Rewrite.applyAt` restricts replacement to selected statement indices; `applySeq` folds `Rewrite.apply` left-to-right across a list of rewrites and is algebraically equal to `(firstMatch ρs).apply` (`applySeq_eq_firstMatch`).

```lean
-- lean/Toy/LawRewrite/Basic.lean:140-142
structure Rewrite where
  targets : Inst → Bool
  repl : Inst → Impl
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:145-147
def Rewrite.rwStmt (ρ : Rewrite) : Stmt → Stmt
  | .call i dst src => if ρ.targets i then .prim (ρ.repl i) dst src else .call i dst src
  | s => s
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:150
def Rewrite.apply (ρ : Rewrite) (p : Prog) : Prog := p.map ρ.rwStmt
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:155-157
def Rewrite.applyAt (ρ : Rewrite) (S : Nat → Bool) : Nat → Prog → Prog
  | _, [] => []
  | k, s :: p => (if S k then ρ.rwStmt s else s) :: ρ.applyAt S (k + 1) p
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:160-161
def applySeq (ρs : List Rewrite) (p : Prog) : Prog :=
  ρs.foldl (fun q ρ => ρ.apply q) p
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:221-225
def firstMatch (ρs : List Rewrite) : Rewrite where
  targets i := ρs.any (fun ρ => ρ.targets i)
  repl i := match ρs.find? (fun ρ => ρ.targets i) with
    | some ρ => ρ.repl i
    | none => copyImpl
```

#### The meaning of calls: compiled code, direct capture, relational capture

`compiled` runs `env.impl` with no contract check. `capDirect` runs `env.impl` and, at an `unsafeTrait` call violating `env.contract`, triggers UB at `before` or `after`. `capRel` nondeterministically chooses between `env.impl` and any matching replacement in `ρs`, ignoring `env.safety` and `env.contract`.

```lean
-- lean/Toy/LawRewrite/Basic.lean:166-167
def compiledCalls (env : Env) : Inst → Val → List CallRes :=
  fun i v => [.ret (env.impl i v)]
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:175-184
def directCalls (env : Env) (pos : RelyPos) : Inst → Val → List CallRes :=
  fun i v =>
    match env.safety i with
    | .safeTrait => [.ret (env.impl i v)]
    | .unsafeTrait =>
      if env.impl i v = env.contract i v then [.ret (env.impl i v)]
      else
        match pos with
        | .before => [.ubAfter []]
        | .after => [.ubAfter (env.impl i v).1]
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:190-193
def relCalls (env : Env) (ρs : List Rewrite) : Inst → Val → List CallRes :=
  fun i v =>
    .ret (env.impl i v) ::
      ρs.filterMap (fun ρ => if ρ.targets i then some (.ret (ρ.repl i v)) else none)
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:196-197
def compiled (env : Env) (p : Prog) (σ : Store) : List Beh :=
  exec (compiledCalls env) p σ
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:200-201
def capDirect (env : Env) (pos : RelyPos) (p : Prog) (σ : Store) : List Beh :=
  exec (directCalls env pos) p σ
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:204-205
def capRel (env : Env) (ρs : List Rewrite) (p : Prog) (σ : Store) : List Beh :=
  exec (relCalls env ρs) p σ
```

#### Refinement and verification

`ImprovesPP` restates CompCert's `behavior_improves` (target behaviour first); `ImprovesWT` lets any source `.ub` behaviour permit any target behaviour. Note the two distinct `Sat` predicates in this package: `Toy.LawRewrite.Sat` (below) quantifies over a `List Beh`, whereas `Toy.LawRewrite.CaptureBridge.Sat` (in the capture-bridge subsection) quantifies over a predicate denotation `Den B = B → Prop`.

```lean
-- lean/Toy/LawRewrite/Basic.lean:211-212
def ImprovesPP (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .ub t ∧ t <+: bt.trace
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:215-216
def ImprovesWT (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .ub t
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:220-221
def RefinesPP (src tgt : List Beh) : Prop :=
  ∀ bt ∈ tgt, ∃ bs ∈ src, ImprovesPP bt bs
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:225-226
def RefinesWT (src tgt : List Beh) : Prop :=
  ∀ bt ∈ tgt, ∃ bs ∈ src, ImprovesWT bt bs
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:230-231
def Sat (bs : List Beh) (spec : Beh → Prop) : Prop :=
  ∀ b ∈ bs, spec b
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:234-235
def UBFreeSpec (spec : Beh → Prop) : Prop :=
  ∀ t, ¬ spec (.ub t)
```

#### Laws, reached calls, and side conditions

```lean
-- lean/Toy/LawRewrite/Basic.lean:285-286
def LawAt (env : Env) (ρ : Rewrite) (i : Inst) (v : Val) : Prop :=
  env.impl i v = ρ.repl i v
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:291-298
def Reaches (env : Env) : Prog → Store → Inst → Val → Prop
  | [], _, _, _ => False
  | .set x v :: p, σ, i, w => Reaches env p (σ.upd x v) i w
  | .out _ :: p, σ, i, w => Reaches env p σ i w
  | .prim f dst src :: p, σ, i, w => Reaches env p (σ.upd dst (f (σ src)).2) i w
  | .call j dst src :: p, σ, i, w =>
      (j = i ∧ σ src = w) ∨ Reaches env p (σ.upd dst (env.impl j (σ src)).2) i w
  | .ub :: _, _, _, _ => False
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:302-303
def LawOnReached (env : Env) (ρ : Rewrite) (p : Prog) (σ : Store) : Prop :=
  ∀ i v, ρ.targets i = true → Reaches env p σ i v → LawAt env ρ i v
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:306-307
def LawOnTargets (env : Env) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → ∀ v, LawAt env ρ i v
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:315-318
def ContextSafeAt (env : Env) (pos : RelyPos) (ρ : Rewrite) (i : Inst) (v : Val) : Prop :=
  LawAt env ρ i v ∨
    (env.safety i = .unsafeTrait ∧ env.impl i v ≠ env.contract i v ∧
      (pos = .before ∨ (env.impl i v).1 <+: (ρ.repl i v).1))
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:321-322
def TargetsUnsafe (env : Env) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → env.safety i = .unsafeTrait
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:326-327
def ReplIsContract (env : Env) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → ρ.repl i = env.contract i
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:330-331
def TargetsDisjoint (ρ₁ ρ₂ : Rewrite) : Prop :=
  ∀ i, ρ₁.targets i = true → ρ₂.targets i = false
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:335-336
def CoveredBy (ρs : List Rewrite) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → ∃ ρ' ∈ ρs, ρ'.targets i = true ∧ ρ'.repl i = ρ.repl i
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:340-341
def probe (i : Inst) (v : Val) : Prog :=
  [.set 0 v, .call i 1 0, .out 1]
```

```lean
-- lean/Toy/LawRewrite/Basic.lean:345-348
def callsSome (R : Inst → Bool) (p : Prog) : Bool :=
  p.any fun
    | .call i _ _ => R i
    | _ => false
```

#### Capture bridge (copied) and the fail-closed capture of rewritable calls

The ten declarations in `Toy.LawRewrite.CaptureBridge` are copied verbatim (namespace changed from `Toy.Capture` to `Toy.LawRewrite.CaptureBridge`) from the corpus report `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`, file `lean/Toy/Capture/Basic.lean` (Git blob `5e5d90b0cde9fd5ef3772f2543298cad654861b3`, SHA-256 `c7a687dcf3b6e787cf01aaa4c1da2a0b34c9c78d61d2f164a81140119aaa8123`). As noted above, `CaptureBridge.Sat` takes `d : Den B` (`B → Prop`), distinct from `Toy.LawRewrite.Sat` on `List Beh`. When `capRejectRewritable_compiledDen_transferSound` instantiates `CaptureBridge`, `semS` is the post-rewrite compiled semantics `fun p => compiledDen env (ρ.apply p)` and `semV` is the pre-rewrite `compiledDen env`.

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:21
abbrev Den (B : Type) : Type := B → Prop
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:25-26
def Sat {B : Type} (d : Den B) (spec : B → Prop) : Prop :=
  ∀ b, d b → spec b
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:29-30
def DenIncl {B : Type} (d₁ d₂ : Den B) : Prop :=
  ∀ b, d₁ b → d₂ b
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:35-37
def OverApproxOnOk {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (cap : S → Except E V) : Prop :=
  ∀ p q, cap p = .ok q → DenIncl (semS p) (semV q)
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:42-44
def VerifierSound {V B : Type} (semV : V → Den B) (verified : V → (B → Prop) → Prop) :
    Prop :=
  ∀ q spec, verified q spec → Sat (semV q) spec
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:48-50
def TransferSound {S V E B : Type} (semS : S → Den B) (cap : S → Except E V)
    (verified : V → (B → Prop) → Prop) : Prop :=
  ∀ p q spec, cap p = .ok q → verified q spec → Sat (semS p) spec
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:52-53
theorem Sat.of_denIncl {B : Type} {d₁ d₂ : Den B} {spec : B → Prop}
    (h : DenIncl d₁ d₂) (hs : Sat d₂ spec) : Sat d₁ spec := …
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:60-64
theorem transfer_to_capture_input {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (cap : S → Except E V) (verified : V → (B → Prop) → Prop)
    (hV : VerifierSound semV verified) (hcap : OverApproxOnOk semS semV cap)
    {p : S} {q : V} {spec : B → Prop}
    (hok : cap p = .ok q) (hver : verified q spec) : Sat (semS p) spec := …
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:69-71
def failClosed {S V E : Type} (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E)
    (p : S) : Except E V :=
  if M p then .ok (tr p) else .error e
```

```lean
-- lean/Toy/LawRewrite/CaptureBridge.lean:75-78
theorem failClosed_overApproxOnOk_iff {S V E B : Type} (semS : S → Den B)
    (semV : V → Den B) (M : S → Prop) [DecidablePred M] (tr : S → V) (e : E) :
    OverApproxOnOk semS semV (failClosed M tr e) ↔
      ∀ p, M p → DenIncl (semS p) (semV (tr p)) := by …
```

```lean
-- lean/Toy/LawRewrite/Main.lean:515-516
def compiledDen (env : Env) (p : Prog) : Den (Store × Beh) :=
  fun r => r.2 ∈ compiled env p r.1
```

```lean
-- lean/Toy/LawRewrite/Main.lean:519-520
def capDirectDen (env : Env) (pos : RelyPos) (p : Prog) : Den (Store × Beh) :=
  fun r => r.2 ∈ capDirect env pos p r.1
```

```lean
-- lean/Toy/LawRewrite/Main.lean:524-525
def capRejectRewritable (R : Inst → Bool) : Prog → Except Unit Prog :=
  failClosed (fun p => callsSome R p = false) id ()
```

#### Key definitions unfolded (prose)

- Unfolded (prose): `RefinesPP src tgt` says: for every target behaviour `bt` in `tgt` there is a source behaviour `bs` in `src` such that `bt = bs`, or `bs = .ub t` for some trace `t` that is a prefix of `bt.trace`.
- Unfolded (prose): `capDirect env .before p σ` at `call i dst src` with `v = σ src`: if `i` is `safeTrait`, or `unsafeTrait` with `env.impl i v = env.contract i v`, emit `(env.impl i v).1` and continue with `dst := (env.impl i v).2`; otherwise terminate in `.ub` with the trace emitted so far (or, for `.after`, with `(env.impl i v).1` appended before `.ub`).
- Unfolded (prose): `capRel env [ρ] p σ` at a call of instance `i` with argument `v` branches nondeterministically between `env.impl i v` and (when `ρ.targets i = true`) `ρ.repl i v`, independently at each dynamic call and without checking `env.contract`.
- Unfolded (prose): `ContextSafeAt env pos ρ i v` holds iff `env.impl i v = ρ.repl i v`, or (`env.safety i = .unsafeTrait`, `env.impl i v ≠ env.contract i v`, and (`pos = .before` or `(env.impl i v).1 <+: (ρ.repl i v).1`)).
- For a safe instance `i`, `ContextSafeAt env pos ρ i v` is equivalent to `LawAt env ρ i v` (`contextSafeAt_iff_lawAt_of_safe`), and across safe targets its universal closure is equivalent to `LawOnTargets env ρ` (`contextSafeAt_forall_iff_lawOnTargets_of_targetsSafe`).

#### Concrete instances and definition examples (all fully proved)

```lean
-- lean/Toy/LawRewrite/Examples.lean:18
def loggingClone : Impl := fun v => ([9], v)
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:22
def succClone : Impl := fun v => ([], v + 1)
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:26-27
def envSafeLog : Env :=
  { impl := fun _ => loggingClone, contract := fun _ => copyImpl, safety := fun _ => .safeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:30-31
def envUnsafeLog : Env :=
  { impl := fun _ => loggingClone, contract := fun _ => copyImpl, safety := fun _ => .unsafeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:34-35
def envSafeTriv : Env :=
  { impl := fun _ => copyImpl, contract := fun _ => copyImpl, safety := fun _ => .safeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:38-39
def envUnsafeTriv : Env :=
  { impl := fun _ => copyImpl, contract := fun _ => copyImpl, safety := fun _ => .unsafeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:42-43
def envSafeSucc : Env :=
  { impl := fun _ => succClone, contract := fun _ => copyImpl, safety := fun _ => .safeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:47-48
def envUnsafeSucc : Env :=
  { impl := fun _ => succClone, contract := fun _ => copyImpl, safety := fun _ => .unsafeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:52-55
def envUnsafeSelective : Env :=
  { impl := fun _ v => if v = 5 then ([], 5) else ([9], v)
    contract := fun _ => copyImpl
    safety := fun _ => .unsafeTrait }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:58
def cloneToCopy : Rewrite := { targets := fun i => i == 0, repl := fun _ => copyImpl }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:61
def cloneToCopy1 : Rewrite := { targets := fun i => i == 1, repl := fun _ => copyImpl }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:65
def succRewrite : Rewrite := { targets := fun i => i == 0, repl := fun _ => succClone }
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:68
def σ0 : Store := fun _ => 0
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:71
def twoCalls : Prog := [.set 0 5, .call 0 1 0, .call 0 1 0]
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:74
def deadCall : Prog := [.set 0 5, .call 0 1 0]
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:414-417
def envSeqChain : Env :=
  { impl := fun i _ => if i == 0 then ([], 10) else ([], 0)
    contract := fun _ => copyImpl
    safety := fun _ => .safeTrait }
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:421-423
def guardTenRewrite : Rewrite :=
  { targets := fun i => i == 1
    repl := fun _ v => if v == 10 then ([], 0) else ([], 99) }
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:427-428
def seqChainProg : Prog :=
  [.set 0 5, .call 0 1 0, .call 1 2 1, .out 2]
```

### Modeling bridge — `derived (modeling bridge)`

Basis: `derived (modeling bridge)` + `documentation` + `source`.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR. The following documents what the toy's vocabulary is meant to capture, citing upstream documentation and source at a pinned public revision of `rust-lang/rust` (commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, verified identical to the files served by GitHub at that commit).

**Key modeling gap on unsafe traits (`capDirect` vs. raw MIR capture).** In `Toy.LawRewrite`, `capDirect` (`directCalls`) directly checks `env.impl i v = env.contract i v` at every `unsafeTrait` call and emits operational UB when that single-call equation fails. In Rust, by contrast, calling a method on an unsound `unsafe impl` is not automatically operational UB at the trait-method call boundary itself: UB arises only if an `unsafe` consumer executes an unsound operation that relies on the violated invariant, or if a verifier injects the unsafe trait's safety contract as a relies-point UB check in its captured semantics. A verifier that captures MIR by executing the user's impl body without encoding the unsafe contract as UB lies in the toy's `safeTrait`/`compiled` regime (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`), not its `capDirect` `unsafeTrait` regime. Moreover, `env.contract` models only a single-call stateless function `Val → List Val × Val`, not multi-method or multi-call stateful invariants.

**Safe-trait law (`Clone` for `Copy` types).** The `core::clone` documentation states the law as a "should" and says unsafe code must not rely on it:

```rust
// rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1:library/core/src/clone.rs:82-85
/// Types that are [`Copy`] should have a trivial implementation of `Clone`. More formally:
/// if `T: Copy`, `x: T`, and `y: &T`, then `let x = y.clone();` is equivalent to `let x = *y;`.
/// Manual implementations should be careful to uphold this invariant; however, unsafe code
/// must not rely on it to ensure memory safety.
```

In the toy's vocabulary this is a `safeTrait` contract (`copyImpl`): a violation is defined behaviour, and `envSafeLog` models an impl violating it with an observable effect.

**A codegen rewrite of `clone` calls into copies, gated on an unstable feature.** The feature gate list declares `ergonomic_clones` as an incomplete unstable feature:

```rust
// rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1:compiler/rustc_feature/src/unstable.rs:525-526
    /// Allows the .use postfix syntax `x.use` and use closures `use |x| { ... }`
    (incomplete, ergonomic_clones, "1.87.0", Some(132290)),
```

Codegen calls the rewrite inside a check of that feature:

```rust
// rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1:compiler/rustc_codegen_ssa/src/mir/mod.rs:217-224
    if tcx.features().ergonomic_clones() {
        let monomorphized_mir = instance.instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(mir.clone()),
        );
        mir = tcx.arena.alloc(optimize_use_clone::<Bx>(cx, monomorphized_mir));
    }
```

The function it calls is documented as:

```rust
// rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1:compiler/rustc_codegen_ssa/src/mir/mod.rs:350-350
/// Replace `clone` calls that come from `use` statements with direct copies if possible.
```

Its body (`compiler/rustc_codegen_ssa/src/mir/mod.rs:350-407` at the same commit) matches call terminators whose call source is `mir::CallSource::Use`, whose single argument has a shared-reference type `&T` with `T` `Copy` modulo regions and is a place, and replaces each such call by an assignment of a copy of the dereferenced argument followed by a jump to the call's target block. In the toy's vocabulary this has the shape of `cloneToCopy` running after any capture taken from the MIR before codegen. The toy neither establishes nor refutes claims about which source programs produce `CallSource::Use` calls, about the intended semantics of the unstable `.use` syntax, or about whether any real program's behaviour changes.

**Unsafe-trait contract (`TrustedLen`).** The documentation of the unstable unsafe marker trait `TrustedLen` states its contract and its safety requirement:

```rust
// rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1:library/core/src/iter/traits/marker.rs:37-47
/// An iterator that reports an accurate length using size_hint.
///
/// The iterator reports a size hint where it is either exact
/// (lower bound is equal to upper bound), or the upper bound is [`None`].
/// The upper bound must only be [`None`] if the actual iterator length is
/// larger than [`usize::MAX`]. In that case, the lower bound must be
/// [`usize::MAX`], resulting in an [`Iterator::size_hint()`] of
/// `(usize::MAX, None)`.
///
/// The iterator must produce exactly the number of elements it reported
/// or diverge before reaching the end.
```

```rust
// rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1:library/core/src/iter/traits/marker.rs:60-67
/// # Safety
///
/// This trait must only be implemented when the contract is upheld. Consumers
/// of this trait must inspect [`Iterator::size_hint()`]’s upper bound.
#[unstable(feature = "trusted_len", issue = "37572")]
#[rustc_unsafe_specialization_marker]
#[rustc_const_unstable(feature = "const_iter", issue = "92476")]
pub const unsafe trait TrustedLen: [const] Iterator {}
```

In Rust, `TrustedLen` is an `unsafe` marker trait (`#[rustc_unsafe_specialization_marker]`) relied on by `unsafe` library consumers (such as standard-library iterator specializations) rather than by a built-in compiler call-rewriting pass like `optimize_use_clone`, and its invariant relates `Iterator::size_hint()` across repeated `Iterator::next()` calls and divergence rather than a single stateless call. The toy abstracts a consumer's or verifier's reliance on an unsafe trait contract into a single-call `directCalls` relies point and does not model iterators, multi-call protocols, or library specialization.

## Findings

Design question informed by every card: Exactly when does a law-dependent rewrite that runs after the capture point refine the captured semantics, how does the answer differ between safe-trait and unsafe-trait laws, and which verifier-side remedies (discharging the law, relational capture, fail-closed rejection) are sound?

### `law-on-reached-calls-suffices`

- **Kind:** theorem. **Tier:** T1 — Correctness of a law-justified rewrite when the law holds is folklore (cf. GHC `RULES`); the per-program form, demanding the law at the calls reached by the law-free execution and at no other argument, against a direct capture with UB as top, is made precise here (and serves as the single-rewrite entry point to `refinesPP_capDirect_applySeq_of_lawOnReached`).
- **Lean:** `Toy.LawRewrite.refinesPP_capDirect_apply_of_lawOnReached`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env` (any safety marks), relies position `pos`, rewrite `ρ`, program `p` and store `σ`: if the law of `ρ` holds at every call of a targeted instance that the law-free execution of `p` from `σ` reaches, at the argument it is reached with (`LawOnReached env ρ p σ`), then every behaviour of the compiled rewritten program `ρ.apply p` from `σ` improves, prefix-preservingly, some behaviour of the direct capture of `p` from `σ` (`RefinesPP (capDirect env pos p σ) (compiled env (ρ.apply p) σ)`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:110-112
theorem refinesPP_capDirect_apply_of_lawOnReached (env : Env) (pos : RelyPos)
    (ρ : Rewrite) (p : Prog) (σ : Store) (hlaw : LawOnReached env ρ p σ) :
    RefinesPP (capDirect env pos p σ) (compiled env (ρ.apply p) σ) := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hlaw : LawOnReached env ρ p σ` | the replacement must agree with the impl wherever the program actually calls a targeted instance | tight: counterexample `cex_nontrivial_clone_copy_rewrite` (witness class: a concrete environment whose every instance is safe (`envSafeLog`), `cloneToCopy` on instance 0, initial store `σ0`, and `probe 0 5` of at most three (specifically, three) statements) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_lawOnReached`: in `envSafeTriv` the law holds at the reached call of `probe 0 5` from `σ0` and the conclusion holds; in `envSafeLog` the law holds vacuously for `[.ub, .call 0 1 0]` from `σ0` (the call is unreachable) although the impl violates it at every argument, and the conclusion holds.
- **Non-claims:**
  - The hypothesis `LawOnReached` is sufficient, not necessary, for a single fixed program: in `envSafeSucc` (effect-free `succClone`) from initial store `σ0` with relies point `before`, `deadCall` reaches a law-violating call at argument `5` whose return value is never emitted, and `cloneToCopy` still refines (`cex_lawOnReached_not_necessary_for_one_program`). When the safe impl has observable effects (`envSafeLog`), even `deadCall` from `σ0` fails to refine (`cex_deadCall_effectful_not_refined`).
  - Prefix-preserving refinement `RefinesPP (capDirect env pos p σ) (compiled env (ρ.apply p) σ)` does not imply behavioural equality and does not transfer specifications satisfied by UB behaviours (for instance, when `p` hits an untargeted unsafe contract violation, `capDirect` is UB while `compiled` terminates normally: `capDirect_before_example`, `compiled_example`).
  - The law is demanded at the calls reached by the law-free execution (`Reaches`), which continues past an unsafe call at which `capDirect` is already UB; a weaker hypothesis that stops at unsafe contract violations is not stated (not examined). This theorem is the singleton specialization (`ρs = [ρ]`) of `refinesPP_capDirect_applySeq_of_lawOnReached`.
  - Nothing is said about rewrites whose replacement code contains calls; every replacement here is inline code `prim f`.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
  - A. Farmer, N. Sculthorpe, A. Gill, "Reasoning with the HERMIT: tool support for equational reasoning on GHC core programs", Proceedings of the 2015 ACM SIGPLAN Symposium on Haskell, pp. 23–34, 2015, doi:10.1145/2804302.2804303: interactive equational reasoning for verifying GHC Core transformations against algebraic and typeclass laws.
  - J. Breitner, A. Spector-Zabusky, Y. Li, C. Rizkallah, J. Wiegley, S. Weirich, "Ready, set, verify! applying hs-to-coq to real-world Haskell code (experience report)", PACMPL 2(ICFP):1–16, 2018, doi:10.1145/3236784: mechanized Coq verification of Haskell library code against specifications including typeclass laws; does not treat post-capture compiler rewrites.
  - B. H. Liskov, J. M. Wing, "A behavioral notion of subtyping", ACM TOPLAS 16(6):1811–1841, 1994, doi:10.1145/197320.197383 (metadata verified at Crossref): substituting a subtype implementation for a supertype specification preserves properties provable from the specification when the implementation meets the behavioral subtyping rules; related in spirit, not a statement about compiler rewrites after capture.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
  - Reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`: UB-erasing eliminations stated with the same two refinement disciplines (prefix-preserving `ImprovesPP`, whole-trace `ImprovesWT`) in a different toy; this package restates the disciplines independently.
  - Reference corpus report `closure-upvar-defunctionalization-symbolic-vtables-and-trait-coherence-laws`: coherence-keyed law registries against dictionary spoofing — which law instance a proof may assume; related, it does not treat rewrites that depend on a law.

### `contextual-refinement-iff-pointwise-context-safety`

- **Kind:** characterization. **Tier:** T1 — The contrast between safe-trait laws (whose violation is defined behaviour) and unsafe-trait contracts (whose violation is UB at a relies point) is folklore; the exact pointwise condition across both safety marks and both relies positions is made precise here.
- **Lean:** `Toy.LawRewrite.refinesPP_every_context_iff_contextSafeAt`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos` and rewrite `ρ`: the compiled rewritten program refines, prefix-preservingly, the direct capture on every program and every initial store iff, at every targeted instance `i` and every argument `v`, `ContextSafeAt env pos ρ i v` holds — that is, the impl agrees with the replacement at `v`, or `i` belongs to an unsafe trait, its impl violates the contract at `v`, and either the relies point is `before` or the impl's effects at `v` are a prefix of the replacement's effects at `v`.

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:153-157
theorem refinesPP_every_context_iff_contextSafeAt (env : Env) (pos : RelyPos)
    (ρ : Rewrite) :
    (∀ (p : Prog) (σ : Store),
        RefinesPP (capDirect env pos p σ) (compiled env (ρ.apply p) σ)) ↔
      ∀ i, ρ.targets i = true → ∀ v, ContextSafeAt env pos ρ i v := by …
```

Hypothesis ledger: no hypotheses beyond the universally quantified parameters.

- **Depth:** substantive.
- **Non-vacuity witness:** `nonvacuity_contextSafeAt`: the right-hand side holds across all three positive branches — a lawful impl (`envSafeTriv`, relies point `after`), an unsafe contract violation with relies point `before` (`envUnsafeLog`), and an unsafe contract violation with relies point `after` whose impl effects are a prefix of the replacement's (`envUnsafeSucc`, `contextSafeAt_pos_after_prefix`) — and fails for a safe law violation (`envSafeLog`), for an unsafe violation with relies point `after` an effect the replacement lacks (`envUnsafeLog`), and for a non-contract replacement on a lawful unsafe impl (`envUnsafeTriv`, `succRewrite`, `contextSafeAt_neg_unsafe_lawful_noncontract`).
- **Non-claims:**
  - The unsafe-trait behaviour relies on `capDirect` explicitly injecting UB at every call of an unsafe instance whose impl violates `env.contract` (`directCalls`). If a verifier captures a program under a semantics that executes the user impl without encoding the unsafe trait's contract as a relies-point UB check (equivalent to `compiled` or `safeTrait` in this toy), neither lawless refinement nor automatic contract discharge/transfer holds (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`).
  - Every contract `env.contract i` here is a single-call, stateless pointwise behaviour (`Val → List Val × Val`); multi-call or multi-method relational trait contracts (such as `TrustedLen` relating `size_hint` to repeated `next` calls) are not modelled.
  - The quantifier ranges over every program and every initial store of the toy language; for one fixed program the condition is not necessary (`cex_lawOnReached_not_necessary_for_one_program`).
  - For a safe instance `ContextSafeAt` is equivalent to `LawAt` (`contextSafeAt_iff_lawAt_of_safe`), and when every targeted instance is safe the right-hand side is equivalent to `LawOnTargets env ρ` (`contextSafeAt_forall_iff_lawOnTargets_of_targetsSafe`); the statement gives no license to rewrite, in every context, calls of a safe-trait instance whose impl violates the law at some argument.
  - The characterization holds for a fixed environment `env`: if a specific unsafe impl violates `env.contract` at every argument, even a replacement `ρ.repl` that disagrees with `env.contract` satisfies `ContextSafeAt` with relies point `before`; agreement with the contract (`ReplIsContract`) is forced when quantifying over environments that include lawful impls (`cex_without_replIsContract`, `contextSafeAt_neg_unsafe_lawful_noncontract`).
  - User impls (`Impl`) cannot themselves trigger UB; if a safe-trait impl could trigger UB before emitting incompatible effects, a rewrite could refine it without satisfying `LawAt` (not examined).
  - The characterization is stated for prefix-preserving refinement; the whole-trace analogue is not stated as an iff (not examined).
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
  - J. Cockx, N. Tabareau, T. Winterhalter, "The taming of the rew: a type theory with computational assumptions", PACMPL 5(POPL):1–29, 2021, doi:10.1145/3434341: soundness criteria for user-supplied rewrite rules in dependently typed proof assistants; does not treat imperative IR capture or UB refinement.
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: securing the foundations of the Rust programming language", PACMPL 2(POPL):1–34, 2018, doi:10.1145/3158154: Coq/Iris semantic-typing foundation of Rust's safe-vs-unsafe boundary, where `unsafe` trait invariants are semantic proof obligations of implementers while safe code cannot cause UB.
  - X. Denis, J.-H. Jourdan, C. Marché, "Creusot: A Foundry for the Deductive Verification of Rust Programs", ICFEM 2022, LNCS 13478, pp. 90–105, Springer, 2022, doi:10.1007/978-3-031-17244-1_6: deductive MIR verification supporting explicit `#[law]` trait laws discharged on implementations.
  - The Rust Reference, "Traits — Unsafe traits" (`[items.traits.safety]`, https://doc.rust-lang.org/reference/items/traits.html#unsafe-traits): documents that implementing an `unsafe` trait carries safety obligations that callers and unsafe consumers may rely on.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
  - J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, "Taming undefined behavior in LLVM", PLDI 2017, pp. 633–647, 2017, doi:10.1145/3062341.3062343: formalizes LLVM's immediate/whole-execution UB refinement, contrasting with CompCert's prefix-preserving `Goes_wrong` refinement.
  - Reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`: UB-erasing eliminations stated with the same two refinement disciplines (prefix-preserving `ImprovesPP`, whole-trace `ImprovesWT`) in a different toy; this package restates the disciplines independently.
  - Reference corpus report `closure-upvar-defunctionalization-symbolic-vtables-and-trait-coherence-laws`: coherence-keyed law registries against dictionary spoofing — which law instance a proof may assume; related, it does not treat rewrites that depend on a law.
  - Reference corpus report `anneal-trusted-mir-gvn-instsimplify-algebraic-and-discriminant-folding`: algebraic identities used by simplification passes, with no user-implementable trait law; related prior art (cited by its slug; no claim is made about any verifier's implementation).

### `safe-target-refinement-on-probe-forces-law`

- **Kind:** theorem. **Tier:** T1 — Observing a replaced call through its emitted effects and returned value is folklore; stated here for the three-statement probe context `probe i v`.
- **Lean:** `Toy.LawRewrite.lawAt_of_refinesPP_probe_of_safe_of_targets`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos`, rewrite `ρ`, instance `i`, argument `v` and store `σ`: if `i` belongs to a safe trait (`env.safety i = .safeTrait`), `ρ` targets `i` (`ρ.targets i = true`), and the compiled rewritten probe `ρ.apply (probe i v)` refines, prefix-preservingly, the direct capture of `probe i v` from `σ` (where `probe i v` sets variable `0` to `v`, calls `i` on it into variable `1`, and emits variable `1`), then the impl of `i` agrees with the replacement at `v` (`LawAt env ρ i v`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:250-255
theorem lawAt_of_refinesPP_probe_of_safe_of_targets (env : Env) (pos : RelyPos)
    (ρ : Rewrite) (i : Inst) (v : Val) (σ : Store) (hsafe : env.safety i = .safeTrait)
    (ht : ρ.targets i = true)
    (href : RefinesPP (capDirect env pos (probe i v) σ)
      (compiled env (ρ.apply (probe i v)) σ)) :
    LawAt env ρ i v := …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsafe : env.safety i = .safeTrait` | for an unsafe trait the direct capture may be UB at the call, which permits the rewrite without LawAt | tight: counterexample `cex_probe_unsafe_before` (witness class: a concrete environment whose every instance is unsafe (`envUnsafeLog`), relies point `before`, `cloneToCopy`, initial store `σ0`, and `probe 0 5`) |
| `ht : ρ.targets i = true` | an untargeted call is not rewritten, so the probe observes the impl against itself | tight: counterexample `cex_probe_untargeted` (witness class: the rewrite `cloneToCopy1` targeting instance 1, probed at safe instance 0 on `probe 0 5` from `σ0`) |
| `href : RefinesPP (capDirect env pos (probe i v) σ) (compiled env (ρ.apply (probe i v)) σ)` | the observational refinement hypothesis on the probe context | tight: counterexample `cex_probe_no_refinement` (witness class: safe instance 0 in `envSafeLog`, `cloneToCopy`, relies point `before`, initial store `σ0`, and `probe 0 5`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_probe_safe`: `envSafeTriv`, instance `0`, `cloneToCopy`, relies point `before`, initial store `σ0`, argument `5`.
- **Non-claims:**
  - The probe emits the returned value; `deadCall`, which ignores the returned value of an effect-free call, does not force the law (`cex_lawOnReached_not_necessary_for_one_program`).
  - User impls (`Impl`) cannot themselves trigger UB; if a safe-trait impl could trigger UB on `probe i v`, prefix-preserving refinement would not force agreement after that UB (not modelled).
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
  - B. H. Liskov, J. M. Wing, "A behavioral notion of subtyping", ACM TOPLAS 16(6):1811–1841, 1994, doi:10.1145/197320.197383 (metadata verified at Crossref): substituting a subtype implementation for a supertype specification preserves properties provable from the specification when the implementation meets the behavioral subtyping rules; related in spirit, not a statement about compiler rewrites after capture.

### `nontrivial-clone-breaks-copy-rewrite`

- **Kind:** counterexample. **Tier:** T1 — That an effectful or non-identity `Clone` on a `Copy` type is observable when a copy is substituted is folklore; this concrete toy instance pins down the exact failure of both prefix-preserving and whole-trace refinement.
- **Lean:** `Toy.LawRewrite.cex_nontrivial_clone_copy_rewrite`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** In the concrete environment `envSafeLog` (every instance belongs to a safe trait; the impl `loggingClone` emits `9` and returns its argument; the contract is `copyImpl`), `cloneToCopy` on instance `0` satisfies `ReplIsContract`, `LawOnReached` fails on `probe 0 5` from initial store `σ0`, the direct capture of `probe 0 5` from `σ0` with relies point `before` equals `[.done [9, 5]]`, the compiled rewritten program from `σ0` equals `[.done [5]]`, prefix-preserving refinement fails with relies point `before`, and whole-trace refinement fails with relies point `after`.

Statement:

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:28-36
theorem cex_nontrivial_clone_copy_rewrite :
    ReplIsContract envSafeLog cloneToCopy ∧
      ¬ LawOnReached envSafeLog cloneToCopy (probe 0 5) σ0 ∧
      capDirect envSafeLog .before (probe 0 5) σ0 = [.done [9, 5]] ∧
      compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0 = [.done [5]] ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envSafeLog .after (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) := …
```

Hypothesis ledger: no hypotheses (a concrete counterexample instance).

- **Depth:** definitional.
- **Non-vacuity witness:** The statement is itself a concrete instance.
- **Non-claims:**
  - This exhibits one concrete toy program and environment; it neither shows nor refutes that any real compiler changes the behaviour of any real program.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
  - B. H. Liskov, J. M. Wing, "A behavioral notion of subtyping", ACM TOPLAS 16(6):1811–1841, 1994, doi:10.1145/197320.197383 (metadata verified at Crossref): substituting a subtype implementation for a supertype specification preserves properties provable from the specification when the implementation meets the behavioral subtyping rules; related in spirit, not a statement about compiler rewrites after capture.

### `unsafe-relies-before-rewrite-refines-without-law`

- **Kind:** theorem. **Tier:** T1 — That a compiler may rely on an unsafe trait's contract because a violation is UB is folklore; the law-free prefix-preserving refinement theorem — requiring both `ReplIsContract` and relies point `before` — is made precise here (and follows as a corollary of `refinesPP_every_context_iff_contextSafeAt`).
- **Lean:** `Toy.LawRewrite.refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, rewrite `ρ`, program `p` and store `σ`: if every instance `ρ` targets belongs to an unsafe trait (`TargetsUnsafe env ρ`) and `ρ` substitutes at every targeted instance the exact behaviour its contract prescribes (`ReplIsContract env ρ`), then, with no law hypothesis on any impl, the compiled rewritten program refines, prefix-preservingly, the direct capture of `p` from `σ` with the relies point `before` the impl.

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:262-265
theorem refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract (env : Env)
    (ρ : Rewrite) (p : Prog) (σ : Store) (hunsafe : TargetsUnsafe env ρ)
    (hrepl : ReplIsContract env ρ) :
    RefinesPP (capDirect env .before p σ) (compiled env (ρ.apply p) σ) := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hunsafe : TargetsUnsafe env ρ` | a violated safe-trait law is defined behaviour, so `capDirect` runs the impl without UB and the divergence is observable | tight: counterexample `cex_without_targetsUnsafe` (witness class: a concrete environment whose every instance is safe (`envSafeLog`), `cloneToCopy`, initial store `σ0`, and `probe 0 5`) |
| `hrepl : ReplIsContract env ρ` | the relies-point UB covers only impls that violate `env.contract`; a replacement other than `env.contract` diverges from a contract-satisfying impl | tight: counterexample `cex_without_replIsContract` (witness class: every instance unsafe with a lawful copy impl (`envUnsafeTriv`), replacement `succRewrite` (`succClone`), initial store `σ0`, and `probe 0 5`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_unsafe`: `envUnsafeLog` (every instance unsafe, the impl violates the copy contract at every argument) with `cloneToCopy`; both hypotheses hold and the conclusion holds on `probe 0 5` from `σ0`.
- **Positive control (blocking qualifier):** `cex_relies_after_effect_not_refined`.
- **Non-claims:**
  - The relies point is `before` the impl in the statement. With the relies point `after` the impl's effects, there is a contract-violating impl with effects (`envUnsafeLog`, `loggingClone` on `probe 0 5` from `σ0`) for which prefix-preserving refinement fails (`cex_relies_after_effect_not_refined`); this is a blocking qualifier, not a presentational choice.
  - The unsafe-trait behaviour relies on `capDirect` explicitly injecting UB at every call of an unsafe instance whose impl violates `env.contract` (`directCalls`). If a verifier captures a program under a semantics that executes the user impl without encoding the unsafe trait's contract as a relies-point UB check (equivalent to `compiled` or `safeTrait` in this toy), neither lawless refinement nor automatic contract discharge/transfer holds (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`).
  - Every contract `env.contract i` here is a single-call, stateless pointwise behaviour (`Val → List Val × Val`); multi-call or multi-method relational trait contracts (such as `TrustedLen` relating `size_hint` to repeated `next` calls) are not modelled.
  - The statement does not say a verifier may ignore the contract: `capDirect` is UB wherever the contract is violated, and verification of a UB-tolerant property does not transfer (`cex_ub_tolerant_spec_no_transfer`). This theorem is a specialization of the right-to-left direction of `refinesPP_every_context_iff_contextSafeAt` at `pos = .before`.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: securing the foundations of the Rust programming language", PACMPL 2(POPL):1–34, 2018, doi:10.1145/3158154: Coq/Iris semantic-typing foundation of Rust's safe-vs-unsafe boundary, where `unsafe` trait invariants are semantic proof obligations of implementers while safe code cannot cause UB.
  - X. Denis, J.-H. Jourdan, C. Marché, "Creusot: A Foundry for the Deductive Verification of Rust Programs", ICFEM 2022, LNCS 13478, pp. 90–105, Springer, 2022, doi:10.1007/978-3-031-17244-1_6: deductive MIR verification supporting explicit `#[law]` trait laws discharged on implementations.
  - The Rust Reference, "Traits — Unsafe traits" (`[items.traits.safety]`, https://doc.rust-lang.org/reference/items/traits.html#unsafe-traits): documents that implementing an `unsafe` trait carries safety obligations that callers and unsafe consumers may rely on.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
  - J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, "Taming undefined behavior in LLVM", PLDI 2017, pp. 633–647, 2017, doi:10.1145/3062341.3062343: formalizes LLVM's immediate/whole-execution UB refinement, contrasting with CompCert's prefix-preserving `Goes_wrong` refinement.
  - Reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`: UB-erasing eliminations stated with the same two refinement disciplines (prefix-preserving `ImprovesPP`, whole-trace `ImprovesWT`) in a different toy; this package restates the disciplines independently.
  - Reference corpus package `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches`: further UB-erasing rewrites under prefix-preserving refinement; related, no shared definitions.

### `relies-after-effect-breaks-lawless-refinement-under-prefix-ub`

- **Kind:** counterexample. **Tier:** T1 — The sensitivity of UB-exploiting rewrites to whether observable events precede the UB point under CompCert-style prefix-preserving refinement vs. LLVM-style whole-trace UB is made concrete here for unsafe-trait relies placement.
- **Lean:** `Toy.LawRewrite.cex_relies_after_effect_not_refined`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** In the concrete environment `envUnsafeLog` (every instance belongs to an unsafe trait; the impl emits `9` and returns its argument; the contract is `copyImpl`) with `cloneToCopy`, both `TargetsUnsafe` and `ReplIsContract` hold; from initial store `σ0` with the relies point `after` the impl, the direct capture of `probe 0 5` equals `[.ub [9]]`, the compiled rewritten program equals `[.done [5]]`, and prefix-preserving refinement fails; whole-trace refinement holds at relies point `after`, and prefix-preserving refinement holds at relies point `before`.

Statement:

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:128-137
theorem cex_relies_after_effect_not_refined :
    TargetsUnsafe envUnsafeLog cloneToCopy ∧ ReplIsContract envUnsafeLog cloneToCopy ∧
      capDirect envUnsafeLog .after (probe 0 5) σ0 = [.ub [9]] ∧
      compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0 = [.done [5]] ∧
      ¬ RefinesPP (capDirect envUnsafeLog .after (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      RefinesWT (capDirect envUnsafeLog .after (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      RefinesPP (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) := …
```

Hypothesis ledger: no hypotheses (a concrete counterexample instance).

- **Depth:** definitional.
- **Non-vacuity witness:** The statement is itself a concrete instance.
- **Non-claims:**
  - This does not show that every relies-after capture requires `LawAt`: `ContextSafeAt` also admits an unsafe contract violation under relies point `after` when the impl's effects are a prefix of the replacement's effects, as witnessed by the effect-free `envUnsafeSucc` (`contextSafeAt_pos_after_prefix`).
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
  - J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, "Taming undefined behavior in LLVM", PLDI 2017, pp. 633–647, 2017, doi:10.1145/3062341.3062343: formalizes LLVM's immediate/whole-execution UB refinement, contrasting with CompCert's prefix-preserving `Goes_wrong` refinement.
  - Reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`: UB-erasing eliminations stated with the same two refinement disciplines (prefix-preserving `ImprovesPP`, whole-trace `ImprovesWT`) in a different toy; this package restates the disciplines independently.

### `whole-trace-ub-unsafe-rewrite-refines-either-position`

- **Kind:** theorem. **Tier:** T0 — Direct consequence of whole-trace UB acting as top regardless of prior trace events (Leroy 2009 Section 2.1 Definition 3; Lee et al. 2017), restated for unsafe-contract rewrites in this toy.
- **Lean:** `Toy.LawRewrite.refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos` (`before` or `after`), rewrite `ρ`, program `p` and store `σ`: if every instance `ρ` targets belongs to an unsafe trait (`TargetsUnsafe env ρ`) and `ρ` substitutes at every targeted instance the exact behaviour its contract prescribes (`ReplIsContract env ρ`), then, with no law hypothesis on any impl, the compiled rewritten program refines the direct capture of `p` from `σ` in the whole-trace sense (`RefinesWT`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:275-278
theorem refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract (env : Env)
    (pos : RelyPos) (ρ : Rewrite) (p : Prog) (σ : Store) (hunsafe : TargetsUnsafe env ρ)
    (hrepl : ReplIsContract env ρ) :
    RefinesWT (capDirect env pos p σ) (compiled env (ρ.apply p) σ) := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hunsafe : TargetsUnsafe env ρ` | a violated safe-trait law is defined behaviour rather than UB in `capDirect`, so the rewritten program's divergence is not masked by source UB | tight: counterexample `cex_without_targetsUnsafe` (witness class: every instance safe (`envSafeLog`), `cloneToCopy`, initial store `σ0`, `probe 0 5`, either relies position) |
| `hrepl : ReplIsContract env ρ` | when the unsafe impl obeys `env.contract`, `capDirect` terminates normally without UB, so `ρ.repl` must agree with `env.contract` | tight: counterexample `cex_without_replIsContract` (witness class: every instance unsafe with a lawful copy impl (`envUnsafeTriv`), replacement `succRewrite` (`succClone`), initial store `σ0`, `probe 0 5`, either relies position) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_unsafe`: `envUnsafeLog` with `cloneToCopy`, relies point `after`, initial store `σ0`; the conclusion holds on `probe 0 5`.
- **Non-claims:**
  - The unsafe-trait behaviour relies on `capDirect` explicitly injecting UB at every call of an unsafe instance whose impl violates `env.contract` (`directCalls`). If a verifier captures a program under a semantics that executes the user impl without encoding the unsafe trait's contract as a relies-point UB check (equivalent to `compiled` or `safeTrait` in this toy), neither lawless refinement nor automatic contract discharge/transfer holds (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`).
  - Every contract `env.contract i` here is a single-call, stateless pointwise behaviour (`Val → List Val × Val`); multi-call or multi-method relational trait contracts (such as `TrustedLen` relating `size_hint` to repeated `next` calls) are not modelled.
  - Whole-trace refinement discards events emitted before UB; the prefix-preserving analogue fails at relies point `after` for `envUnsafeLog` on `probe 0 5` from `σ0` (`cex_relies_after_effect_not_refined`).
  - The statement does not say a verifier may ignore the contract: `capDirect` is UB wherever the contract is violated, and verification of a UB-tolerant specification does not transfer (`cex_ub_tolerant_spec_no_transfer`).
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137, Section 2.1, Definition 3, p. 4): backward simulation for safe source programs (`Safe(S) ⇒ ∀ B, C ⇓ B ⇒ S ⇓ B`, where `Safe(S)` rules out `Wrong` behaviours), corresponding to whole-trace UB exemption (`RefinesWT`) rather than CompCert's later prefix-preserving `behavior_improves`.
  - J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, "Taming undefined behavior in LLVM", PLDI 2017, pp. 633–647, 2017, doi:10.1145/3062341.3062343: formalizes LLVM's immediate/whole-execution UB refinement, contrasting with CompCert's prefix-preserving `Goes_wrong` refinement.
  - N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, "Alive2: bounded translation validation for LLVM", PLDI 2021, pp. 65–79, 2021, doi:10.1145/3453483.3454030: automated translation validation of LLVM optimizations under whole-trace UB refinement.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
  - Reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`: UB-erasing eliminations stated with the same two refinement disciplines (prefix-preserving `ImprovesPP`, whole-trace `ImprovesWT`) in a different toy; this package restates the disciplines independently.

### `ub-free-verification-transfers-through-unsafe-contract-rewrite`

- **Kind:** theorem. **Tier:** T0 — Direct instance of specification preservation for UB-ruling-out specifications under safe backward simulation (Leroy 2009 Section 2.1 Definition 6, mechanized in CompCert), applied to `refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract`.
- **Lean:** `Toy.LawRewrite.sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos`, rewrite `ρ`, program `p`, store `σ` and specification `spec`: if every instance `ρ` targets belongs to an unsafe trait (`TargetsUnsafe env ρ`), `ρ` substitutes at every targeted instance the exact behaviour its contract prescribes (`ReplIsContract env ρ`), no UB behaviour satisfies `spec` (`UBFreeSpec spec`), and every behaviour of the direct capture of `p` from `σ` satisfies `spec` (`Sat (capDirect env pos p σ) spec`), then every behaviour of the compiled rewritten program from `σ` satisfies `spec` (`Sat (compiled env (ρ.apply p) σ) spec`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:323-327
theorem sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect
    (env : Env) (pos : RelyPos) (ρ : Rewrite) (p : Prog) (σ : Store) (spec : Beh → Prop)
    (hunsafe : TargetsUnsafe env ρ) (hrepl : ReplIsContract env ρ)
    (hub : UBFreeSpec spec) (hsat : Sat (capDirect env pos p σ) spec) :
    Sat (compiled env (ρ.apply p) σ) spec := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hunsafe : TargetsUnsafe env ρ` | a safe-trait law is not checked as UB by `capDirect`, so UB-free verification does not discharge it | tight: counterexample `cex_transfer_safe_target` (witness class: every instance safe (`envSafeLog`), `cloneToCopy`, initial store `σ0`, `probe 0 5`) |
| `hrepl : ReplIsContract env ρ` | UB-freedom of `capDirect` forces agreement with `env.contract`, not with a different replacement | tight: counterexample `cex_transfer_repl_not_contract` (witness class: every instance unsafe with a lawful copy impl (`envUnsafeTriv`), replacement `succRewrite` (`succClone`), initial store `σ0`, `probe 0 5`) |
| `hub : UBFreeSpec spec` | a specification satisfied by UB behaviours does not force the relies-point contract checks in `capDirect` to succeed | tight: counterexample `cex_ub_tolerant_spec_no_transfer` (witness class: every instance unsafe (`envUnsafeLog`), `cloneToCopy`, relies point `before`, initial store `σ0`, `probe 0 5`, and the UB-admitting specification `fun b => b = .ub [] ∨ b = .done [9, 5]`) |
| `hsat : Sat (capDirect env pos p σ) spec` | the verified `capDirect` verdict to transfer | tight: counterexample `cex_transfer_unverified` (witness class: every instance unsafe with a lawful impl (`envUnsafeTriv`), `cloneToCopy`, initial store `σ0`, `probe 0 5`, and an unverified UB-free specification) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_ubFree_verification`: in `envUnsafeSelective` (where the unsafe impl agrees with `copyImpl` at `5` and violates it at every other argument, so `LawOnTargets` fails globally), with `cloneToCopy`, relies point `after`, and initial store `σ0`, `fun b => b = .done [5]` is UB-free, holds of `capDirect` on `probe 0 5`, and transfers to the compiled rewritten program.
- **Non-claims:**
  - The unsafe-trait behaviour relies on `capDirect` explicitly injecting UB at every call of an unsafe instance whose impl violates `env.contract` (`directCalls`). If a verifier captures a program under a semantics that executes the user impl without encoding the unsafe trait's contract as a relies-point UB check (equivalent to `compiled` or `safeTrait` in this toy), neither lawless refinement nor automatic contract discharge/transfer holds (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`).
  - Every contract `env.contract i` here is a single-call, stateless pointwise behaviour (`Val → List Val × Val`); multi-call or multi-method relational trait contracts (such as `TrustedLen` relating `size_hint` to repeated `next` calls) are not modelled.
  - The hypothesis `UBFreeSpec spec` cannot be dropped in general: there is a UB-tolerant specification (`fun b => b = .ub [] ∨ b = .done [9, 5]`) verified of `capDirect envUnsafeLog .before (probe 0 5) σ0` that fails for the rewritten program (`cex_ub_tolerant_spec_no_transfer`). Not every UB-tolerant specification fails to transfer (for instance, `fun _ => True` holds of every behaviour list; not separately stated as a theorem here).
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137, Section 2.1, Definition 6, p. 5): preservation of specifications ruling out `Wrong` behaviours (`Spec(B) ⇒ B ∉ Wrong`, `S |= Spec ⇒ C |= Spec`), proved there from backward simulation for safe programs; `UBFreeSpec` and `sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect` instantiate this condition for unsafe-contract rewrites.
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: securing the foundations of the Rust programming language", PACMPL 2(POPL):1–34, 2018, doi:10.1145/3158154: Coq/Iris semantic-typing foundation of Rust's safe-vs-unsafe boundary, where `unsafe` trait invariants are semantic proof obligations of implementers while safe code cannot cause UB.
  - X. Denis, J.-H. Jourdan, C. Marché, "Creusot: A Foundry for the Deductive Verification of Rust Programs", ICFEM 2022, LNCS 13478, pp. 90–105, Springer, 2022, doi:10.1007/978-3-031-17244-1_6: deductive MIR verification supporting explicit `#[law]` trait laws discharged on implementations.
  - L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust Programs", PACMPL 8(PLDI):1115–1139, 2024, doi:10.1145/3656422: foundational MIR-level refinement-type verification in Coq/Iris; does not treat post-capture law-dependent codegen rewrites.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
  - Reference corpus package `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets`, card `R6-spec-transfer`: verification of a closed target transfers when, among other hypotheses, every user impl body (trait method, user `Drop`, user `Clone`) verifies against its spec — the analogous obligation on user impls in a monomorphization model.

### `ub-free-verification-discharges-contract-at-reached-unsafe-calls`

- **Kind:** theorem. **Tier:** T1 — That a UB-free verdict entails every UB-guarding obligation reached along the run is folklore; made precise here for the relies-point checks of `capDirect` against the law-free reachability predicate `Reaches`.
- **Lean:** `Toy.LawRewrite.contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos`, program `p`, store `σ`, specification `spec`, instance `i` and argument `v`: if `i` belongs to an unsafe trait (`env.safety i = .unsafeTrait`), the law-free execution of `p` from `σ` reaches a call of `i` with argument `v` (`Reaches env p σ i v`), no UB behaviour satisfies `spec` (`UBFreeSpec spec`), and every behaviour of the direct capture of `p` from `σ` satisfies `spec` (`Sat (capDirect env pos p σ) spec`), then the impl of `i` agrees with the contract at `v` (`env.impl i v = env.contract i v`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:339-343
theorem contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec (env : Env)
    (pos : RelyPos) (p : Prog) (σ : Store) (spec : Beh → Prop) (i : Inst) (v : Val)
    (hunsafe : env.safety i = .unsafeTrait) (hreach : Reaches env p σ i v)
    (hub : UBFreeSpec spec) (hsat : Sat (capDirect env pos p σ) spec) :
    env.impl i v = env.contract i v := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hunsafe : env.safety i = .unsafeTrait` | `capDirect` checks `env.contract` only at unsafe-trait instances; safe-trait calls never trigger relies-point UB | tight: counterexample `cex_contract_discharge_safe_call` (witness class: safe instance 0 in `envSafeLog`, `probe 0 5` from `σ0`, relies point `before`, and UB-free specification `fun b => b = .done [9, 5]`) |
| `hreach : Reaches env p σ i v` | `capDirect` executes only the calls and arguments actually reached from `σ`; unreached arguments are never tested | tight: counterexample `cex_contract_discharge_unreached_arg` (witness class: unsafe instance 0 in `envUnsafeSelective` at unreached argument `0` during `probe 0 5` from `σ0`, relies point `after`) |
| `hub : UBFreeSpec spec` | a specification satisfied by UB does not exclude a failing relies-point check | tight: counterexample `cex_contract_discharge_ub_tolerant` (witness class: unsafe instance 0 in `envUnsafeLog`, reached `(0, 5)` on `probe 0 5` from `σ0`, and the trivial specification `fun _ => True`) |
| `hsat : Sat (capDirect env pos p σ) spec` | the verified `capDirect` verdict ruling out UB along the run | tight: counterexample `cex_contract_discharge_unverified` (witness class: unsafe instance 0 in `envUnsafeLog`, reached `(0, 5)` on `probe 0 5` from `σ0`, and an unverified UB-free specification) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_ubFree_verification`: in `envUnsafeSelective` (where the contract fails at every argument other than `5`), `probe 0 5` from `σ0` reaches unsafe call `(0, 5)`, `fun b => b = .done [5]` is UB-free and holds of `capDirect` at relies point `after`, and `envUnsafeSelective.impl 0 5 = envUnsafeSelective.contract 0 5`.
- **Non-claims:**
  - The unsafe-trait behaviour relies on `capDirect` explicitly injecting UB at every call of an unsafe instance whose impl violates `env.contract` (`directCalls`). If a verifier captures a program under a semantics that executes the user impl without encoding the unsafe trait's contract as a relies-point UB check (equivalent to `compiled` or `safeTrait` in this toy), neither lawless refinement nor automatic contract discharge/transfer holds (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`).
  - Every contract `env.contract i` here is a single-call, stateless pointwise behaviour (`Val → List Val × Val`); multi-call or multi-method relational trait contracts (such as `TrustedLen` relating `size_hint` to repeated `next` calls) are not modelled.
  - The contract is established at the reached arguments `(i, v)` of reached unsafe calls (`cex_contract_discharge_unreached_arg`), and safe-trait contracts are not discharged (`cex_contract_discharge_safe_call`).
  - The implication is one-way: satisfying the contract at every reached unsafe call does not by itself imply `Sat (capDirect env pos p σ) spec` for an arbitrary `spec` (`cex_transfer_unverified`). Moreover, `Reaches` stops at `.ub` (`reaches_neg_after_ub`), and any `.ub` before a call already falsifies `Sat (capDirect env pos p σ) spec` when `UBFreeSpec spec` holds.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137, Section 2.1, Definition 6, p. 5): preservation of specifications ruling out `Wrong` behaviours (`Spec(B) ⇒ B ∉ Wrong`, `S |= Spec ⇒ C |= Spec`), proved there from backward simulation for safe programs; `UBFreeSpec` and `sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect` instantiate this condition for unsafe-contract rewrites.
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: securing the foundations of the Rust programming language", PACMPL 2(POPL):1–34, 2018, doi:10.1145/3158154: Coq/Iris semantic-typing foundation of Rust's safe-vs-unsafe boundary, where `unsafe` trait invariants are semantic proof obligations of implementers while safe code cannot cause UB.
  - X. Denis, J.-H. Jourdan, C. Marché, "Creusot: A Foundry for the Deductive Verification of Rust Programs", ICFEM 2022, LNCS 13478, pp. 90–105, Springer, 2022, doi:10.1007/978-3-031-17244-1_6: deductive MIR verification supporting explicit `#[law]` trait laws discharged on implementations.
  - L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust Programs", PACMPL 8(PLDI):1115–1139, 2024, doi:10.1145/3656422: foundational MIR-level refinement-type verification in Coq/Iris; does not treat post-capture law-dependent codegen rewrites.
  - Reference corpus package `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets`, card `R6-spec-transfer`: verification of a closed target transfers when, among other hypotheses, every user impl body (trait method, user `Drop`, user `Clone`) verifies against its spec — the analogous obligation on user impls in a monomorphization model.

### `relational-capture-sound-for-every-partial-rewrite`

- **Kind:** theorem. **Tier:** T0 — Over-approximating deterministic implementation choices by demonic nondeterministic choice is textbook in refinement calculus (Back & von Wright 1998) and mechanized in Isabelle/HOL (`Refine_Monadic`, Lammich 2012) and Coq (`Fiat`, Delaware et al. 2015); restated here for per-site post-capture rewrite selections.
- **Lean:** `Toy.LawRewrite.sat_compiled_applyAt_of_sat_capRel`, `Toy.LawRewrite.sat_compiled_and_apply_of_sat_capRel`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, rewrite `ρ`, program `p`, store `σ` and specification `spec`: if every behaviour of the relational capture of `p` for `[ρ]` from `σ` satisfies `spec` (`Sat (capRel env [ρ] p σ) spec`), then for every site selection `S : Nat → Bool`, every behaviour from `σ` of the compiled program with `ρ` applied at the selected statement positions (`ρ.applyAt S 0 p`) satisfies `spec` (`sat_compiled_applyAt_of_sat_capRel`), and in particular `spec` holds both of the unrewritten compiled program `p` and of the fully rewritten compiled program `ρ.apply p` (`sat_compiled_and_apply_of_sat_capRel`); no law is assumed.

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:473-476
theorem sat_compiled_applyAt_of_sat_capRel (env : Env) (ρ : Rewrite) (p : Prog)
    (σ : Store) (spec : Beh → Prop) (hsat : Sat (capRel env [ρ] p σ) spec)
    (S : Nat → Bool) :
    Sat (compiled env (ρ.applyAt S 0 p) σ) spec := …
```

```lean
-- lean/Toy/LawRewrite/Main.lean:482-484
theorem sat_compiled_and_apply_of_sat_capRel (env : Env) (ρ : Rewrite) (p : Prog)
    (σ : Store) (spec : Beh → Prop) (hsat : Sat (capRel env [ρ] p σ) spec) :
    Sat (compiled env p σ) spec ∧ Sat (compiled env (ρ.apply p) σ) spec := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hsat : Sat (capRel env [ρ] p σ) spec` | the verified relational-capture verdict | tight: counterexample `cex_capRel_sound_unverified` (witness class: `envSafeLog`, `cloneToCopy`, initial store `σ0`, `probe 0 5`, an unverified specification `fun b => b = .done [5]`, and `S = fun _ => false`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_capRel_sound`: `fun b => b.trace.getLast? = some 5` holds of `capRel envSafeLog [cloneToCopy] (probe 0 5) σ0`.
- **Non-claims:**
  - Both `capRel` and `compiled` are law-free semantics that ignore `env.safety` and `env.contract` and perform no relies-point UB checks (`capRel_unsafe_ignores_contract_example`). Verifying a specification of `capRel` transfers to `compiled` and neither establishes `Sat (capDirect env pos p σ) spec` nor rules out unsafe-trait UB in other passes or unsafe consumers.
  - Properties that depend on the impl's observable effects may fail for `capRel` even when they hold of `capDirect`: on `probe 0 5` from `σ0` in `envSafeLog` with relies point `before`, `fun b => b = .done [9, 5]` holds of `capDirect` and fails for `capRel` (`cex_capRel_loses_effect_property`). That lost property is also false of the compiled rewritten program (`compiled_envSafeLog_probe_rewritten`, `cex_nontrivial_clone_copy_rewrite`), so dropping it is required to remain sound when `cloneToCopy` runs.
  - Sites are statement positions of a straight-line program; in languages where one syntactic site executes multiple times, `capRel` chooses independently on each dynamic call whereas a static site selection must choose once per site (not examined).
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - R.-J. Back, J. von Wright, Refinement Calculus: A Systematic Introduction, Springer, 1998, doi:10.1007/978-1-4612-1674-2: textbook treatment of demonic nondeterministic choice as the universal over-approximation (least upper bound) of possible implementations, and of non-distributivity between local step choice and global choice.
  - P. Lammich, "Refinement for Monadic Programs", Archive of Formal Proofs (Isabelle/HOL), 2012, ISSN 2150-914X (https://isa-afp.org/entries/Refine_Monadic.html): mechanizes nondeterministic result-set over-approximation and refinement with failure as top.
  - B. Delaware, C. Pit-Claudel, J. Gross, A. Chlipala, "Fiat: Deductive Synthesis of Abstract Data Types in a Proof Assistant", POPL 2015, pp. 689–700, 2015, doi:10.1145/2676726.2677006: Coq mechanization of refinement from nondeterministic relational specifications to deterministic implementations.

### `relational-capture-weakest-for-per-site-rewriting`

- **Kind:** characterization. **Tier:** T1 — Characterizing per-call relational nondeterminism as the exact union of syntactic per-site partial rewrite applications (`applyAt`) in a straight-line program, and contrasting it with all-or-nothing pass application, makes precise when relational capture is and is not weakest.
- **Lean:** `Toy.LawRewrite.mem_capRel_iff_exists_applyAt`, `Toy.LawRewrite.capRel_subset_of_sound_for_every_applyAt`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, rewrite `ρ`, program `p` and store `σ`: a behaviour `b` belongs to `capRel env [ρ] p σ` iff there is a site selection `S : Nat → Bool` for which `b` belongs to `compiled env (ρ.applyAt S 0 p) σ` (`mem_capRel_iff_exists_applyAt`); and for every behaviour predicate `D : Beh → Prop` such that every specification `spec : Beh → Prop` implied by `D` holds of `compiled env (ρ.applyAt S 0 p) σ` under every site selection `S`, `D` contains every behaviour in `capRel env [ρ] p σ` (`capRel_subset_of_sound_for_every_applyAt`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:494-496
theorem mem_capRel_iff_exists_applyAt (env : Env) (ρ : Rewrite) (p : Prog) (σ : Store)
    (b : Beh) :
    b ∈ capRel env [ρ] p σ ↔ ∃ S : Nat → Bool, b ∈ compiled env (ρ.applyAt S 0 p) σ := …
```

```lean
-- lean/Toy/LawRewrite/Main.lean:503-507
theorem capRel_subset_of_sound_for_every_applyAt (env : Env) (ρ : Rewrite) (p : Prog)
    (σ : Store) (D : Beh → Prop)
    (hD : ∀ spec : Beh → Prop, (∀ b, D b → spec b) →
      ∀ S : Nat → Bool, Sat (compiled env (ρ.applyAt S 0 p) σ) spec) :
    ∀ b ∈ capRel env [ρ] p σ, D b := …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hD : ∀ spec : Beh → Prop, (∀ b, D b → spec b) → ∀ S : Nat → Bool, Sat (compiled env (ρ.applyAt S 0 p) σ) spec` | `D` is sound for every specification `spec` and every per-site partial application `S` (applies to `capRel_subset_of_sound_for_every_applyAt`; `mem_capRel_iff_exists_applyAt` is unconditional) | tight: counterexample `cex_capRel_subset_without_soundness` (witness class: the empty behaviour predicate `fun _ => False` on `probe 0 5` from `σ0` in `envSafeLog` with `cloneToCopy`) |

- **Depth:** substantive.
- **Non-vacuity witness:** `nonvacuity_capRel_subset`: the two-element predicate `fun b => b = .done [9, 5] ∨ b = .done [5]` satisfies `hD` for `probe 0 5` from `σ0` in `envSafeLog` with `cloneToCopy`.
- **Positive control (blocking qualifier):** `cex_capRel_not_weakest_for_all_or_nothing`.
- **Non-claims:**
  - Both `capRel` and `compiled` are law-free semantics that ignore `env.safety` and `env.contract` and perform no relies-point UB checks (`capRel_unsafe_ignores_contract_example`). Verifying a specification of `capRel` transfers to `compiled` and neither establishes `Sat (capDirect env pos p σ) spec` nor rules out unsafe-trait UB in other passes or unsafe consumers.
  - Weakest relative to per-site partial application (`applyAt`), not relative to all-or-nothing whole-program application (`apply`): on `twoCalls` (containing two calls of instance `0`) from `σ0` in `envSafeLog` with `cloneToCopy`, `fun b => b ≠ .done [9]` holds both without the rewrite and with `cloneToCopy.apply`, yet fails on `capRel` because `capRel` admits mixed per-site runs (`cex_capRel_not_weakest_for_all_or_nothing`).
  - Weakest relative to per-site rewriting relies on the straight-line assumption that every syntactic call site executes at most once. In a language with loops or reusable functions where one site can execute multiple times, a static per-site selection `S` must make the same choice on every execution of that site, whereas `capRel` chooses independently on every dynamic call; `capRel` is therefore strictly weaker than static per-site rewriting once sites can execute repeatedly (not proved here).
  - The hypothesis `hD` quantifies over every predicate `spec : Beh → Prop` (including `spec = D`). For a verifier restricted to a proper subclass of trace predicates (such as UB-freedom alone, or properties ignoring some emitted events), a strictly smaller behaviour set `D` can remain sound for every site selection (not proved here).
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - R.-J. Back, J. von Wright, Refinement Calculus: A Systematic Introduction, Springer, 1998, doi:10.1007/978-1-4612-1674-2: textbook treatment of demonic nondeterministic choice as the universal over-approximation (least upper bound) of possible implementations, and of non-distributivity between local step choice and global choice.
  - P. Lammich, "Refinement for Monadic Programs", Archive of Formal Proofs (Isabelle/HOL), 2012, ISSN 2150-914X (https://isa-afp.org/entries/Refine_Monadic.html): mechanizes nondeterministic result-set over-approximation and refinement with failure as top.
  - B. Delaware, C. Pit-Claudel, J. Gross, A. Chlipala, "Fiat: Deductive Synthesis of Abstract Data Types in a Proof Assistant", POPL 2015, pp. 689–700, 2015, doi:10.1145/2676726.2677006: Coq mechanization of refinement from nondeterministic relational specifications to deterministic implementations.

### `fail-closed-rejection-of-rewritable-calls-sound-and-incomplete`

- **Kind:** theorem. **Tier:** T0 — Direct instantiation of the copied fail-closed characterization `failClosed_overApproxOnOk_iff` and `transfer_to_capture_input`, with `semS` instantiated to the post-rewrite compiled semantics and `semV` to `compiledDen env`.
- **Lean:** `Toy.LawRewrite.capRejectRewritable_compiledDen_transferSound`, `Toy.LawRewrite.capRejectRewritable_incomplete`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, rejected-instance predicate `R : Inst → Bool` and rewrite `ρ`: if every instance `ρ` targets satisfies `R`, then for every verdict relation `verified` sound for the law-free semantics `compiledDen env`, verification transfers (`TransferSound`) through `capRejectRewritable R` — which rejects every program containing a syntactic call of an instance in `R` and captures every other program unchanged — to the compiled program rewritten by `ρ` (`capRejectRewritable_compiledDen_transferSound`); and the capture is incomplete: `capRejectRewritable cloneToCopy.targets` rejects `probe 0 5` although in `envSafeTriv` every compiled run of the rewritten probe is already a run of the unrewritten probe (`capRejectRewritable_incomplete`).

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:552-556
theorem capRejectRewritable_compiledDen_transferSound (env : Env) (R : Inst → Bool)
    (ρ : Rewrite) (hR : ∀ i, ρ.targets i = true → R i = true)
    (verified : Prog → (Store × Beh → Prop) → Prop)
    (hV : VerifierSound (compiledDen env) verified) :
    TransferSound (fun p => compiledDen env (ρ.apply p)) (capRejectRewritable R) verified := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:310-313
theorem capRejectRewritable_incomplete :
    capRejectRewritable cloneToCopy.targets (probe 0 5) = .error () ∧
      DenIncl (compiledDen envSafeTriv (cloneToCopy.apply (probe 0 5)))
        (compiledDen envSafeTriv (probe 0 5)) := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hR : ∀ i, ρ.targets i = true → R i = true` | every call site that `ρ` can rewrite must be rejected by `capRejectRewritable R` (applies to `capRejectRewritable_compiledDen_transferSound`) | tight: counterexample `cex_capRejectRewritable_target_outside_R` (witness class: `R = fun _ => false`, `envSafeLog`, `cloneToCopy`, and the exact verifier of `compiledDen envSafeLog` on `probe 0 5`) |
| `hV : VerifierSound (compiledDen env) verified` | accepted verdicts must hold of the pre-rewrite law-free semantics `compiledDen env` (applies to `capRejectRewritable_compiledDen_transferSound`) | tight: counterexample `cex_capRejectRewritable_unsound_verifier` (witness class: the unsound verifier `fun _ _ => True` accepting every specification on the empty program `[]` in `envSafeTriv`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_capRejectRewritable`: `R = cloneToCopy.targets`, the exact verifier of `compiledDen envSafeLog`, and an accepted program `[.call 1 1 0]` calling untargeted instance `1`.
- **Non-claims:**
  - The verifier semantics in `hV` is the law-free semantics `compiledDen env` (every call runs its impl, no relies check). For a verifier sound for `capDirectDen` instead, `TransferSound` does not hold in general: for the exact verifier `fun q spec => CaptureBridge.Sat (capDirectDen envUnsafeLog .before q) spec`, `capRejectRewritable cloneToCopy.targets` accepts `probe 1 5` and fails to transfer the UB-tolerant specification `fun r => r.2 = .ub []` (`cex_capRejectRewritable_not_transferSound_for_capDirect`). Note also the `CaptureBridge` parameter roles: `semS` is instantiated to the post-rewrite compiled program `fun p => compiledDen env (ρ.apply p)` and `semV` to the pre-rewrite `compiledDen env`.
  - `callsSome` is a purely syntactic check over `p`, so `capRejectRewritable` also rejects programs whose targeted calls are unreachable (such as `[.ub, .call 0 1 0]`) or dead (`deadCall`).
  - The hypothesis `hR` covers a single rewrite `ρ`; extending the `env`-universal sufficiency theorem `capRejectRewritable_compiledDen_transferSound` from `ρ.apply` to a rewrite sequence `applySeq ρs` would take `R` covering every rewrite in `ρs` (or `(firstMatch ρs).targets`) (not stated as a separate theorem here; for a fixed `env` where `ρs` acts as an observational identity, such as `envSafeTriv`, `TransferSound` can hold without `R` covering `ρs`).
  - Incompleteness is witnessed by one concrete program in `envSafeTriv`; how much coverage a real verifier loses by rejecting rewritable calls is not examined.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - Reference corpus package `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`: the capture bridge (`OverApproxOnOk`, `TransferSound`, `failClosed`) for passes before the capture point; its card `fail-closed-and-fail-open-obligations` (`failClosed_overApproxOnOk_iff`) is copied verbatim into `CaptureBridge.lean`. This package treats rewrites after the capture point.

### `rewrite-sequence-refines-of-laws-on-reached-calls`

- **Kind:** theorem. **Tier:** T0 — Because every replacement in `Rewrite` is call-free inline code `prim f` that no later `Rewrite` matches, `applySeq ρs` collapses algebraically to the single rewrite `(firstMatch ρs).apply` (`applySeq_eq_firstMatch`), reducing sequence refinement directly to `refinesPP_capDirect_apply_of_lawOnReached`.
- **Lean:** `Toy.LawRewrite.refinesPP_capDirect_applySeq_of_lawOnReached`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos`, list of rewrites `ρs`, program `p` and store `σ`: if for every rewrite `ρ ∈ ρs` its law holds at every call of a targeted instance that the law-free execution of `p` from `σ` reaches (`LawOnReached env ρ p σ`), then the compiled program obtained by applying the rewrites of `ρs` in order (`applySeq ρs p`) refines, prefix-preservingly, the direct capture of `p` from `σ`.

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:570-572
theorem refinesPP_capDirect_applySeq_of_lawOnReached (env : Env) (pos : RelyPos)
    (ρs : List Rewrite) (p : Prog) (σ : Store) (hlaw : ∀ ρ ∈ ρs, LawOnReached env ρ p σ) :
    RefinesPP (capDirect env pos p σ) (compiled env (applySeq ρs p) σ) := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hlaw : ∀ ρ ∈ ρs, LawOnReached env ρ p σ` | every rewrite in `ρs` must agree with the impl at the reached calls of `p` that it may replace | tight: counterexample `cex_applySeq_without_law` (witness class: a sequence `[cloneToCopy]` of exactly one rewrite, `envSafeLog`, initial store `σ0`, relies point `before`, and `probe 0 5`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_applySeq`: `envSafeTriv`, `[cloneToCopy, cloneToCopy1]` on a program calling both instance `0` and instance `1` from `σ0`.
- **Non-claims:**
  - Within this call-free `prim` model, `applySeq ρs p = (firstMatch ρs).apply p` (`applySeq_eq_firstMatch`), so no sequence of `LawOnReached`-satisfying rewrites can interact to break refinement. That non-interaction relies on two strong restrictions: (1) per-program refinement `RefinesPP` itself is NOT closed under sequential composition when an earlier rewrite refines `p` without obeying `LawOnReached`, because changing an unobserved intermediate return value can change the argument reaching a later rewrite's call site (`cex_refining_rewrites_seq_not_refining`); and (2) rewrites whose replacements contain trait calls (such as redirecting one method to another) are not modelled — if an earlier rewrite can introduce a call to an instance unreached in `p`, `LawOnReached` on the original program `p` no longer suffices (not proved here).
  - Composing unsafe-trait rewrites without `LawOnReached` (under `TargetsUnsafe` and `ReplIsContract`) and laws relating two instances (such as cross-trait consistency between `Eq` and `Hash`) are not covered by this theorem.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
  - A. Farmer, N. Sculthorpe, A. Gill, "Reasoning with the HERMIT: tool support for equational reasoning on GHC core programs", Proceedings of the 2015 ACM SIGPLAN Symposium on Haskell, pp. 23–34, 2015, doi:10.1145/2804302.2804303: interactive equational reasoning for verifying GHC Core transformations against algebraic and typeclass laws.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).

### `disjoint-rewrite-sequence-contextual-iff-conjunction`

- **Kind:** characterization. **Tier:** T1 — Folklore made precise: call-free rewrites with pairwise-disjoint targets compose conjunctively over all contexts without shadowing, whereas overlapping targets allow an earlier rewrite to shadow a later invalid rewrite.
- **Lean:** `Toy.LawRewrite.refinesPP_every_context_applySeq_iff_of_pairwise_disjoint`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, relies position `pos` and list of rewrites `ρs`: if no two rewrites in `ρs` target a common instance (`ρs.Pairwise TargetsDisjoint`), then `applySeq ρs` refines, prefix-preservingly, the direct capture on every program and every initial store iff every rewrite `ρ ∈ ρs` satisfies `ContextSafeAt env pos ρ i v` at every instance `i` it targets and every argument `v`.

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:602-606
theorem refinesPP_every_context_applySeq_iff_of_pairwise_disjoint (env : Env)
    (pos : RelyPos) (ρs : List Rewrite) (hdisj : ρs.Pairwise TargetsDisjoint) :
    (∀ (p : Prog) (σ : Store),
        RefinesPP (capDirect env pos p σ) (compiled env (applySeq ρs p) σ)) ↔
      ∀ ρ ∈ ρs, ∀ i, ρ.targets i = true → ∀ v, ContextSafeAt env pos ρ i v := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hdisj : ρs.Pairwise TargetsDisjoint` | with overlapping targets an earlier rewrite replaces the calls a later rewrite would match, so the shadowed later rewrite need not satisfy `ContextSafeAt` | tight: counterexample `cex_overlapping_rewrites_conjunction_not_necessary` (witness class: the sequence `[cloneToCopy, succRewrite]` of at most two (specifically, two) rewrites targeting instance 0 in `envSafeTriv` at relies point `before`, quantified over all programs and stores) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_applySeq`: `[cloneToCopy, cloneToCopy1]` in `envSafeTriv` at relies point `before` (pairwise disjoint targets; `ContextSafeAt` holds everywhere).
- **Non-claims:**
  - Under the stronger `LawOnReached` hypothesis (`LawAt` rather than `ContextSafeAt`), per-program sufficiency holds without `hdisj` (`refinesPP_capDirect_applySeq_of_lawOnReached`); sufficiency of the `ContextSafeAt` conjunction without `hdisj` is not proved here. Without `hdisj`, the left-to-right (necessity) direction fails for `[cloneToCopy, succRewrite]` in `envSafeTriv` at relies point `before`, where the earlier `cloneToCopy` satisfies `LawOnTargets` and shadows `succRewrite`, which fails `ContextSafeAt` at instance `0` and argument `0` (`cex_overlapping_rewrites_conjunction_not_necessary`).
  - Because replacements are call-free `prim` statements and targets are pairwise disjoint, the rewrites in `ρs` do not create or consume matches for one another; pass-ordering sensitivity in real compilers (where one pass creates or enables matches for another) and multi-instance laws are not modelled.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
  - A. Farmer, N. Sculthorpe, A. Gill, "Reasoning with the HERMIT: tool support for equational reasoning on GHC core programs", Proceedings of the 2015 ACM SIGPLAN Symposium on Haskell, pp. 23–34, 2015, doi:10.1145/2804302.2804303: interactive equational reasoning for verifying GHC Core transformations against algebraic and typeclass laws.
  - CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).

### `relational-capture-of-rewrite-list-covers-every-covered-sequence`

- **Kind:** theorem. **Tier:** T0 — Monotonicity of nondeterministic over-approximation under inclusion of per-step choices (Back & von Wright 1998; `Refine_Monadic`, Lammich 2012), restated for `applySeq` and `CoveredBy`.
- **Lean:** `Toy.LawRewrite.mem_capRel_of_mem_compiled_applySeq_of_coveredBy`
- **Basis:** `execution (Lean kernel check)`.
- **Plain claim:** For every environment `env`, lists of rewrites `ρs` and `ρs'`, program `p` and store `σ`: if every replacement of every rewrite `ρ ∈ ρs'` is the replacement of some rewrite in `ρs` at the same instance (`∀ ρ ∈ ρs', CoveredBy ρs ρ`), then every behaviour from `σ` of the compiled program `applySeq ρs' p` belongs to `capRel env ρs p σ`.

Statement:

```lean
-- lean/Toy/LawRewrite/Main.lean:627-629
theorem mem_capRel_of_mem_compiled_applySeq_of_coveredBy (env : Env)
    (ρs ρs' : List Rewrite) (p : Prog) (σ : Store) (hcov : ∀ ρ ∈ ρs', CoveredBy ρs ρ) :
    ∀ b ∈ compiled env (applySeq ρs' p) σ, b ∈ capRel env ρs p σ := by …
```

Hypothesis ledger:

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hcov : ∀ ρ ∈ ρs', CoveredBy ρs ρ` | every replacement that `applySeq ρs'` may substitute at an instance must appear among `capRel env ρs`'s choices at that instance | tight: counterexample `cex_without_coveredBy` (witness class: empty capture list `ρs = []`, `ρs' = [cloneToCopy]`, `envSafeLog`, initial store `σ0`, and `probe 0 5`) |

- **Depth:** shallow.
- **Non-vacuity witness:** `nonvacuity_coveredBy`: `ρs' = [succRewrite]` covered by `ρs = [cloneToCopy, succRewrite]` on `probe 0 5` from `σ0` in `envSafeLog`.
- **Non-claims:**
  - Both `capRel` and `compiled` are law-free semantics that ignore `env.safety` and `env.contract` and perform no relies-point UB checks (`capRel_unsafe_ignores_contract_example`). Verifying a specification of `capRel` transfers to `compiled` and neither establishes `Sat (capDirect env pos p σ) spec` nor rules out unsafe-trait UB in other passes or unsafe consumers.
  - `capRel env ρs` is an over-approximation, not weakest, for whole-program sequences `applySeq ρs'`: even for a singleton list `[cloneToCopy]`, `applySeq [cloneToCopy]` rewrites all matching sites uniformly, whereas `capRel` admits mixed per-site runs (`cex_capRel_not_weakest_for_all_or_nothing`).
  - Every rewrite of `ρs'` in the statement is applied at all sites via `applySeq`; per-site partial application of a multi-rewrite list is not stated (per-site partial application of a single rewrite is characterized in `mem_capRel_iff_exists_applyAt`). Separately, `relCalls_append` shows that at each call `(i, v)`, `relCalls env (ρs₁ ++ ρs₂) i v` is the list concatenation (`++`, preserving order and duplicates) of `relCalls env ρs₁ i v` with `(relCalls env ρs₂ i v).tail`.
  - The toy language is straight-line: no loops, branches, recursion, heap, references or unwinding, and every statement runs at most once per execution. Behaviour for languages with control flow is not examined.
  - Impls are total, deterministic functions of the argument value alone; impls that diverge, panic, trigger UB, read or write shared state, or behave nondeterministically are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Prior art:**
  - R.-J. Back, J. von Wright, Refinement Calculus: A Systematic Introduction, Springer, 1998, doi:10.1007/978-1-4612-1674-2: textbook treatment of demonic nondeterministic choice as the universal over-approximation (least upper bound) of possible implementations, and of non-distributivity between local step choice and global choice.
  - P. Lammich, "Refinement for Monadic Programs", Archive of Formal Proofs (Isabelle/HOL), 2012, ISSN 2150-914X (https://isa-afp.org/entries/Refine_Monadic.html): mechanizes nondeterministic result-set over-approximation and refinement with failure as top.
  - B. Delaware, C. Pit-Claudel, J. Gross, A. Chlipala, "Fiat: Deductive Synthesis of Abstract Data Types in a Proof Assistant", POPL 2015, pp. 689–700, 2015, doi:10.1145/2676726.2677006: Coq mechanization of refinement from nondeterministic relational specifications to deterministic implementations.

### Auxiliary declarations cited by name

Every remaining package-local theorem and lemma cited in the tables, ledgers, and non-claims above, quoted verbatim.

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:94-95
theorem applyAt_const_false (ρ : Rewrite) :
    ∀ (k : Nat) (p : Prog), ρ.applyAt (fun _ => false) k p = p := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:84-85
theorem applyAt_const_true (ρ : Rewrite) :
    ∀ (k : Nat) (p : Prog), ρ.applyAt (fun _ => true) k p = ρ.apply p := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:169-171
theorem applyAt_example :
    cloneToCopy.applyAt (fun k => k == 1) 0 twoCalls =
      [.set 0 5, .prim copyImpl 1 0, .call 0 1 0] := …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:266-267
theorem applySeq_eq_firstMatch (ρs : List Rewrite) (p : Prog) :
    applySeq ρs p = (firstMatch ρs).apply p := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:174-176
theorem applySeq_example :
    applySeq [cloneToCopy, cloneToCopy1] [.call 0 1 0, .call 1 1 0] =
      [.prim copyImpl 1 0, .prim copyImpl 1 0] := …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:104-105
theorem applySeq_pair (ρ₁ ρ₂ : Rewrite) (p : Prog) :
    applySeq [ρ₁, ρ₂] p = ρ₂.apply (ρ₁.apply p) := …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:62-64
theorem apply_apply_of_targets_le (ρ₁ ρ₂ : Rewrite)
    (h : ∀ i, ρ₂.targets i = true → ρ₁.targets i = true) (p : Prog) :
    ρ₂.apply (ρ₁.apply p) = ρ₁.apply p := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:166
theorem apply_neg : cloneToCopy.apply [.call 1 1 0] = [.call 1 1 0] := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:162-163
theorem apply_pos :
    cloneToCopy.apply (probe 0 5) = [.set 0 5, .prim copyImpl 1 0, .out 1] := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:291
theorem callsSome_neg : callsSome cloneToCopy.targets [.set 0 1, .out 0] = false := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:294
theorem callsSome_neg_untargeted : callsSome cloneToCopy.targets [.call 1 1 0] = false := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:288
theorem callsSome_pos : callsSome cloneToCopy.targets (probe 0 5) = true := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:372
theorem capDirectDen_neg : ¬ capDirectDen envUnsafeLog .before (probe 1 5) (σ0, .done [9, 5]) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:368
theorem capDirectDen_pos : capDirectDen envUnsafeLog .before (probe 1 5) (σ0, .ub []) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:135
theorem capDirect_after_example : capDirect envUnsafeLog .after (probe 0 5) σ0 = [.ub [9]] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:130
theorem capDirect_before_example : capDirect envUnsafeLog .before (probe 0 5) σ0 = [.ub []] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:20-21
theorem capDirect_eq_compiled_of_allSafe (env : Env) (pos : RelyPos)
    (h : ∀ i, env.safety i = .safeTrait) : capDirect env pos = compiled env := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:125
theorem capDirect_safe_example : capDirect envSafeLog .before (probe 0 5) σ0 = [.done [9, 5]] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:157-158
theorem capDirect_singleton (env : Env) (pos : RelyPos) (p : Prog) (σ : Store) :
    ∃ b, capDirect env pos p σ = [b] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:139-140
theorem capDirect_unsafe_lawful_example :
    capDirect envUnsafeTriv .before (probe 0 5) σ0 = [.done [5]] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:147-148
theorem capRel_example :
    capRel envSafeLog [cloneToCopy] (probe 0 5) σ0 = [.done [9, 5], .done [5]] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:193-194
theorem capRel_ne_nil (env : Env) (ρs : List Rewrite) (p : Prog) (σ : Store) :
    capRel env ρs p σ ≠ [] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:152
theorem capRel_nil_example : capRel envSafeLog [] (probe 0 5) σ0 = [.done [9, 5]] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:156-158
theorem capRel_unsafe_ignores_contract_example :
    capDirect envUnsafeLog .before (probe 0 5) σ0 = [.ub []] ∧
      capRel envUnsafeLog [cloneToCopy] (probe 0 5) σ0 = [.done [9, 5], .done [5]] := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:406-409
theorem cex_applySeq_without_law :
    ¬ (∀ ρ ∈ [cloneToCopy], LawOnReached envSafeLog ρ (probe 0 5) σ0) ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (applySeq [cloneToCopy] (probe 0 5)) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:380-386
theorem cex_capRejectRewritable_not_transferSound_for_capDirect :
    (∀ i, cloneToCopy.targets i = true → cloneToCopy.targets i = true) ∧
      VerifierSound (capDirectDen envUnsafeLog .before)
        (fun q spec => CaptureBridge.Sat (capDirectDen envUnsafeLog .before q) spec) ∧
      ¬ TransferSound (fun p => compiledDen envUnsafeLog (cloneToCopy.apply p))
        (capRejectRewritable cloneToCopy.targets)
        (fun q spec => CaptureBridge.Sat (capDirectDen envUnsafeLog .before q) spec) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:323-329
theorem cex_capRejectRewritable_target_outside_R :
    ¬ (∀ i, cloneToCopy.targets i = true → (fun _ => false : Inst → Bool) i = true) ∧
      VerifierSound (compiledDen envSafeLog)
        (fun q spec => CaptureBridge.Sat (compiledDen envSafeLog q) spec) ∧
      ¬ TransferSound (fun p => compiledDen envSafeLog (cloneToCopy.apply p))
        (capRejectRewritable (fun _ => false))
        (fun q spec => CaptureBridge.Sat (compiledDen envSafeLog q) spec) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:347-351
theorem cex_capRejectRewritable_unsound_verifier :
    (∀ i, cloneToCopy.targets i = true → cloneToCopy.targets i = true) ∧
      ¬ VerifierSound (compiledDen envSafeTriv) (fun _ _ => True) ∧
      ¬ TransferSound (fun p => compiledDen envSafeTriv (cloneToCopy.apply p))
        (capRejectRewritable cloneToCopy.targets) (fun _ _ => True) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:276-278
theorem cex_capRel_loses_effect_property :
    Sat (capDirect envSafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      ¬ Sat (capRel envSafeLog [cloneToCopy] (probe 0 5) σ0) (fun b => b = .done [9, 5]) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:266-269
theorem cex_capRel_not_weakest_for_all_or_nothing :
    Sat (compiled envSafeLog twoCalls σ0) (fun b => b ≠ .done [9]) ∧
      Sat (compiled envSafeLog (cloneToCopy.apply twoCalls) σ0) (fun b => b ≠ .done [9]) ∧
      ¬ Sat (capRel envSafeLog [cloneToCopy] twoCalls σ0) (fun b => b ≠ .done [9]) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:249-255
theorem cex_capRel_sound_unverified :
    ¬ Sat (capRel envSafeLog [cloneToCopy] (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      ¬ Sat (compiled envSafeLog (cloneToCopy.applyAt (fun _ => false) 0 (probe 0 5)) σ0)
        (fun b => b = .done [5]) ∧
      ¬ (Sat (compiled envSafeLog (probe 0 5) σ0) (fun b => b = .done [5]) ∧
          Sat (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0)
            (fun b => b = .done [5])) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:284-289
theorem cex_capRel_subset_without_soundness :
    ¬ (∀ spec : Beh → Prop, (∀ b, (fun _ => False : Beh → Prop) b → spec b) →
        ∀ S : Nat → Bool,
          Sat (compiled envSafeLog (cloneToCopy.applyAt S 0 (probe 0 5)) σ0) spec) ∧
      ¬ (∀ b ∈ capRel envSafeLog [cloneToCopy] (probe 0 5) σ0,
          (fun _ => False : Beh → Prop) b) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:199-204
theorem cex_contract_discharge_safe_call :
    envSafeLog.safety 0 ≠ .unsafeTrait ∧
      Reaches envSafeLog (probe 0 5) σ0 0 5 ∧
      UBFreeSpec (fun b => b = .done [9, 5]) ∧
      Sat (capDirect envSafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      envSafeLog.impl 0 5 ≠ envSafeLog.contract 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:224-229
theorem cex_contract_discharge_ub_tolerant :
    envUnsafeLog.safety 0 = .unsafeTrait ∧
      Reaches envUnsafeLog (probe 0 5) σ0 0 5 ∧
      ¬ UBFreeSpec (fun _ => True) ∧
      Sat (capDirect envUnsafeLog .before (probe 0 5) σ0) (fun _ => True) ∧
      envUnsafeLog.impl 0 5 ≠ envUnsafeLog.contract 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:212-217
theorem cex_contract_discharge_unreached_arg :
    envUnsafeSelective.safety 0 = .unsafeTrait ∧
      ¬ Reaches envUnsafeSelective (probe 0 5) σ0 0 0 ∧
      UBFreeSpec (fun b => b = .done [5]) ∧
      Sat (capDirect envUnsafeSelective .after (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      envUnsafeSelective.impl 0 0 ≠ envUnsafeSelective.contract 0 0 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:236-241
theorem cex_contract_discharge_unverified :
    envUnsafeLog.safety 0 = .unsafeTrait ∧
      Reaches envUnsafeLog (probe 0 5) σ0 0 5 ∧
      UBFreeSpec (fun b => b = .done [9, 5]) ∧
      ¬ Sat (capDirect envUnsafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      envUnsafeLog.impl 0 5 ≠ envUnsafeLog.contract 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:56-58
theorem cex_deadCall_effectful_not_refined :
    ¬ RefinesPP (capDirect envSafeLog .before deadCall σ0)
      (compiled envSafeLog (cloneToCopy.apply deadCall) σ0) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:44-47
theorem cex_lawOnReached_not_necessary_for_one_program :
    ¬ LawOnReached envSafeSucc cloneToCopy deadCall σ0 ∧
      RefinesPP (capDirect envSafeSucc .before deadCall σ0)
        (compiled envSafeSucc (cloneToCopy.apply deadCall) σ0) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:464-472
theorem cex_overlapping_rewrites_conjunction_not_necessary :
    ¬ [cloneToCopy, succRewrite].Pairwise TargetsDisjoint ∧
      LawOnTargets envSafeTriv cloneToCopy ∧
      (∀ (p : Prog) (σ : Store),
        RefinesPP (capDirect envSafeTriv .before p σ)
          (compiled envSafeTriv (applySeq [cloneToCopy, succRewrite] p) σ)) ∧
      ¬ ContextSafeAt envSafeTriv .before succRewrite 0 0 ∧
      ¬ (∀ ρ ∈ [cloneToCopy, succRewrite], ∀ i, ρ.targets i = true → ∀ v,
          ContextSafeAt envSafeTriv .before ρ i v) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:85-89
theorem cex_probe_no_refinement :
    envSafeLog.safety 0 = .safeTrait ∧ cloneToCopy.targets 0 = true ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ LawAt envSafeLog cloneToCopy 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:65-69
theorem cex_probe_unsafe_before :
    envUnsafeLog.safety 0 ≠ .safeTrait ∧ cloneToCopy.targets 0 = true ∧
      RefinesPP (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ LawAt envUnsafeLog cloneToCopy 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:75-79
theorem cex_probe_untargeted :
    envSafeLog.safety 0 = .safeTrait ∧ cloneToCopy1.targets 0 = false ∧
      RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy1.apply (probe 0 5)) σ0) ∧
      ¬ LawAt envSafeLog cloneToCopy1 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:436-444
theorem cex_refining_rewrites_seq_not_refining :
    ¬ LawOnReached envSeqChain cloneToCopy seqChainProg σ0 ∧
      RefinesPP (capDirect envSeqChain .before seqChainProg σ0)
        (compiled envSeqChain (cloneToCopy.apply seqChainProg) σ0) ∧
      LawOnReached envSeqChain guardTenRewrite seqChainProg σ0 ∧
      RefinesPP (capDirect envSeqChain .before seqChainProg σ0)
        (compiled envSeqChain (guardTenRewrite.apply seqChainProg) σ0) ∧
      ¬ RefinesPP (capDirect envSeqChain .before seqChainProg σ0)
        (compiled envSeqChain (applySeq [cloneToCopy, guardTenRewrite] seqChainProg) σ0) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:160-165
theorem cex_transfer_repl_not_contract :
    TargetsUnsafe envUnsafeTriv succRewrite ∧ ¬ ReplIsContract envUnsafeTriv succRewrite ∧
      UBFreeSpec (fun b => b = .done [5]) ∧
      Sat (capDirect envUnsafeTriv .before (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      ¬ Sat (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0)
        (fun b => b = .done [5]) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:147-152
theorem cex_transfer_safe_target :
    ¬ TargetsUnsafe envSafeLog cloneToCopy ∧ ReplIsContract envSafeLog cloneToCopy ∧
      UBFreeSpec (fun b => b = .done [9, 5]) ∧
      Sat (capDirect envSafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      ¬ Sat (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .done [9, 5]) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:187-192
theorem cex_transfer_unverified :
    TargetsUnsafe envUnsafeTriv cloneToCopy ∧ ReplIsContract envUnsafeTriv cloneToCopy ∧
      UBFreeSpec (fun b => b = .done [7]) ∧
      ¬ Sat (capDirect envUnsafeTriv .before (probe 0 5) σ0) (fun b => b = .done [7]) ∧
      ¬ Sat (compiled envUnsafeTriv (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .done [7]) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:173-179
theorem cex_ub_tolerant_spec_no_transfer :
    TargetsUnsafe envUnsafeLog cloneToCopy ∧ ReplIsContract envUnsafeLog cloneToCopy ∧
      ¬ UBFreeSpec (fun b => b = .ub [] ∨ b = .done [9, 5]) ∧
      Sat (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (fun b => b = .ub [] ∨ b = .done [9, 5]) ∧
      ¬ Sat (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .ub [] ∨ b = .done [9, 5]) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:492-495
theorem cex_without_coveredBy :
    ¬ (∀ ρ ∈ [cloneToCopy], CoveredBy [] ρ) ∧
      ¬ (∀ b ∈ compiled envSafeLog (applySeq [cloneToCopy] (probe 0 5)) σ0,
          b ∈ capRel envSafeLog [] (probe 0 5) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:111-118
theorem cex_without_replIsContract :
    TargetsUnsafe envUnsafeTriv succRewrite ∧ ¬ ReplIsContract envUnsafeTriv succRewrite ∧
      ¬ RefinesPP (capDirect envUnsafeTriv .before (probe 0 5) σ0)
        (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envUnsafeTriv .before (probe 0 5) σ0)
        (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envUnsafeTriv .after (probe 0 5) σ0)
        (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:96-103
theorem cex_without_targetsUnsafe :
    ¬ TargetsUnsafe envSafeLog cloneToCopy ∧ ReplIsContract envSafeLog cloneToCopy ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envSafeLog .after (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:363
theorem compiledDen_neg : ¬ compiledDen envSafeLog (probe 0 5) (σ0, .done [5]) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:359
theorem compiledDen_pos : compiledDen envSafeLog (probe 0 5) (σ0, .done [9, 5]) := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:30-32
theorem compiled_apply_eq_of_repl_eq_impl (env : Env) (ρ : Rewrite)
    (h : ∀ i, ρ.targets i = true → ρ.repl i = env.impl i) :
    ∀ (p : Prog) (σ : Store), compiled env (ρ.apply p) σ = compiled env p σ := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:299-300
theorem compiled_envSafeLog_probe (σ : Store) :
    compiled envSafeLog (probe 0 5) σ = [.done [9, 5]] := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:303-304
theorem compiled_envSafeLog_probe_rewritten (σ : Store) :
    compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ = [.done [5]] := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:144
theorem compiled_example : compiled envUnsafeLog (probe 0 5) σ0 = [.done [9, 5]] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:137-138
theorem compiled_singleton (env : Env) (p : Prog) (σ : Store) :
    ∃ b, compiled env p σ = [b] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:126-128
theorem contextSafeAt_forall_iff_lawOnTargets_of_targetsSafe (env : Env) (pos : RelyPos)
    (ρ : Rewrite) (hsafe : ∀ i, ρ.targets i = true → env.safety i = .safeTrait) :
    (∀ i, ρ.targets i = true → ∀ v, ContextSafeAt env pos ρ i v) ↔ LawOnTargets env ρ := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:108-110
theorem contextSafeAt_iff_lawAt_of_safe (env : Env) (pos : RelyPos) (ρ : Rewrite)
    (i : Inst) (v : Val) (hsafe : env.safety i = .safeTrait) :
    ContextSafeAt env pos ρ i v ↔ LawAt env ρ i v := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:224
theorem contextSafeAt_neg_after : ¬ ContextSafeAt envUnsafeLog .after cloneToCopy 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:217
theorem contextSafeAt_neg_safe : ¬ ContextSafeAt envSafeLog .before cloneToCopy 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:241-243
theorem contextSafeAt_neg_unsafe_lawful_noncontract :
    envUnsafeTriv.safety 0 = .unsafeTrait ∧
      ¬ ContextSafeAt envUnsafeTriv .before succRewrite 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:212
theorem contextSafeAt_pos : ContextSafeAt envUnsafeLog .before cloneToCopy 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:233-235
theorem contextSafeAt_pos_after_prefix :
    ¬ LawAt envUnsafeSucc cloneToCopy 0 5 ∧
      ContextSafeAt envUnsafeSucc .after cloneToCopy 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:282
theorem coveredBy_neg : ¬ CoveredBy [] cloneToCopy := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:278
theorem coveredBy_pos : CoveredBy [cloneToCopy] cloneToCopy := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:305
theorem firstMatch_neg : (firstMatch [cloneToCopy]).targets 1 = false := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:299-301
theorem firstMatch_pos :
    (firstMatch [cloneToCopy, succRewrite]).targets 0 = true ∧
      (firstMatch [cloneToCopy, succRewrite]).repl 0 = copyImpl := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:90
theorem improvesPP_neg : ¬ ImprovesPP (.done [2]) (.ub [1]) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:86
theorem improvesPP_pos : ImprovesPP (.done [1, 2]) (.ub [1]) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:97
theorem improvesWT_neg : ¬ ImprovesWT (.done [1]) (.done [2]) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:94
theorem improvesWT_pos : ImprovesWT (.done [2]) (.ub [1]) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:82
theorem lawAt_neg : ¬ LawAt envSafeLog cloneToCopy 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:79
theorem lawAt_pos : LawAt envSafeTriv cloneToCopy 0 5 := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:195
theorem lawOnReached_neg : ¬ LawOnReached envSafeLog cloneToCopy (probe 0 5) σ0 := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:191
theorem lawOnReached_pos : LawOnReached envSafeTriv cloneToCopy (probe 0 5) σ0 := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:199
theorem lawOnReached_unreached : LawOnReached envSafeLog cloneToCopy [.ub, .call 0 1 0] σ0 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:207
theorem lawOnTargets_neg : ¬ LawOnTargets envSafeLog cloneToCopy := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:204
theorem lawOnTargets_pos : LawOnTargets envSafeTriv cloneToCopy := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:640-649
theorem nonvacuity_applySeq :
    [cloneToCopy, cloneToCopy1].Pairwise TargetsDisjoint ∧
      (∀ ρ ∈ [cloneToCopy, cloneToCopy1],
        LawOnReached envSafeTriv ρ [.set 0 5, .call 0 1 0, .call 1 2 0, .out 1, .out 2] σ0) ∧
      (∀ ρ ∈ [cloneToCopy, cloneToCopy1], ∀ i, ρ.targets i = true → ∀ v,
        ContextSafeAt envSafeTriv .before ρ i v) ∧
      RefinesPP (capDirect envSafeTriv .before [.set 0 5, .call 0 1 0, .call 1 2 0, .out 1, .out 2] σ0)
        (compiled envSafeTriv
          (applySeq [cloneToCopy, cloneToCopy1] [.set 0 5, .call 0 1 0, .call 1 2 0, .out 1, .out 2])
          σ0) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:628-632
theorem nonvacuity_capRejectRewritable :
    (∀ i, cloneToCopy.targets i = true → cloneToCopy.targets i = true) ∧
      VerifierSound (compiledDen envSafeLog)
        (fun q spec => CaptureBridge.Sat (compiledDen envSafeLog q) spec) ∧
      capRejectRewritable cloneToCopy.targets [.call 1 1 0] = .ok [.call 1 1 0] := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:592-593
theorem nonvacuity_capRel_sound :
    Sat (capRel envSafeLog [cloneToCopy] (probe 0 5) σ0) (fun b => b.trace.getLast? = some 5) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:599-602
theorem nonvacuity_capRel_subset :
    ∀ spec : Beh → Prop,
      (∀ b, (b = .done [9, 5] ∨ b = .done [5]) → spec b) →
      ∀ S : Nat → Bool, Sat (compiled envSafeLog (cloneToCopy.applyAt S 0 (probe 0 5)) σ0) spec := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:521-532
theorem nonvacuity_contextSafeAt :
    (∀ i, cloneToCopy.targets i = true → ∀ v, ContextSafeAt envSafeTriv .after cloneToCopy i v) ∧
      (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envUnsafeLog .before cloneToCopy i v) ∧
      (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envUnsafeSucc .after cloneToCopy i v) ∧
      ¬ (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envSafeLog .before cloneToCopy i v) ∧
      ¬ (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envUnsafeLog .after cloneToCopy i v) ∧
      ¬ (∀ i, succRewrite.targets i = true → ∀ v,
        ContextSafeAt envUnsafeTriv .before succRewrite i v) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:666-669
theorem nonvacuity_coveredBy :
    (∀ ρ ∈ [succRewrite], CoveredBy [cloneToCopy, succRewrite] ρ) ∧
      (∀ b ∈ compiled envSafeLog (applySeq [succRewrite] (probe 0 5)) σ0,
        b ∈ capRel envSafeLog [cloneToCopy, succRewrite] (probe 0 5) σ0) := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:504-510
theorem nonvacuity_lawOnReached :
    LawOnReached envSafeTriv cloneToCopy (probe 0 5) σ0 ∧
      RefinesPP (capDirect envSafeTriv .before (probe 0 5) σ0)
        (compiled envSafeTriv (cloneToCopy.apply (probe 0 5)) σ0) ∧
      LawOnReached envSafeLog cloneToCopy [.ub, .call 0 1 0] σ0 ∧
      RefinesPP (capDirect envSafeLog .before [.ub, .call 0 1 0] σ0)
        (compiled envSafeLog (cloneToCopy.apply [.ub, .call 0 1 0]) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:545-548
theorem nonvacuity_probe_safe :
    envSafeTriv.safety 0 = .safeTrait ∧ cloneToCopy.targets 0 = true ∧
      RefinesPP (capDirect envSafeTriv .before (probe 0 5) σ0)
        (compiled envSafeTriv (cloneToCopy.apply (probe 0 5)) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:571-581
theorem nonvacuity_ubFree_verification :
    ¬ LawOnTargets envUnsafeSelective cloneToCopy ∧
      TargetsUnsafe envUnsafeSelective cloneToCopy ∧
      ReplIsContract envUnsafeSelective cloneToCopy ∧
      envUnsafeSelective.safety 0 = .unsafeTrait ∧
      Reaches envUnsafeSelective (probe 0 5) σ0 0 5 ∧
      UBFreeSpec (fun b => b = .done [5]) ∧
      Sat (capDirect envUnsafeSelective .after (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      Sat (compiled envUnsafeSelective (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .done [5]) ∧
      envUnsafeSelective.impl 0 5 = envUnsafeSelective.contract 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Counterexamples.lean:555-560
theorem nonvacuity_unsafe :
    TargetsUnsafe envUnsafeLog cloneToCopy ∧ ReplIsContract envUnsafeLog cloneToCopy ∧
      RefinesPP (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      RefinesWT (capDirect envUnsafeLog .after (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:187
theorem reaches_neg_after_ub : ¬ Reaches envSafeLog [.ub, .call 0 1 0] σ0 0 0 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:183
theorem reaches_neg_arg : ¬ Reaches envSafeLog (probe 0 5) σ0 0 4 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:179
theorem reaches_pos : Reaches envSafeLog (probe 0 5) σ0 0 5 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:103
theorem refinesPP_neg : ¬ RefinesPP [.done [1]] [.done [1], .done [2]] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:100
theorem refinesPP_pos : RefinesPP [.ub [1]] [.done [1, 2], .ub [1, 3]] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:15
theorem refinesPP_refl (l : List Beh) : RefinesPP l l := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:109
theorem refinesWT_neg : ¬ RefinesWT [.done [1]] [.done [2]] := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:106
theorem refinesWT_pos : RefinesWT [.ub [1]] [.done [2]] := by …
```

```lean
-- lean/Toy/LawRewrite/Lemmas.lean:120-121
theorem relCalls_append (env : Env) (ρs₁ ρs₂ : List Rewrite) (i : Inst) (v : Val) :
    relCalls env (ρs₁ ++ ρs₂) i v = relCalls env ρs₁ i v ++ (relCalls env ρs₂ i v).tail := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:261
theorem replIsContract_neg : ¬ ReplIsContract envUnsafeTriv succRewrite := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:258
theorem replIsContract_pos : ReplIsContract envUnsafeLog cloneToCopy := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:115
theorem sat_neg : ¬ Sat [.done [1], .done [2]] (fun b => b.trace = [1]) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:112
theorem sat_pos : Sat [.done [1], .ub [1]] (fun b => b.trace = [1]) := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:274
theorem targetsDisjoint_neg : ¬ TargetsDisjoint cloneToCopy succRewrite := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:267
theorem targetsDisjoint_pos : TargetsDisjoint cloneToCopy cloneToCopy1 := by …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:254
theorem targetsUnsafe_neg : ¬ TargetsUnsafe envSafeLog cloneToCopy := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:251
theorem targetsUnsafe_pos : TargetsUnsafe envUnsafeLog cloneToCopy := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:122
theorem ubFreeSpec_neg : ¬ UBFreeSpec (fun _ => True) := …
```

```lean
-- lean/Toy/LawRewrite/Examples.lean:118
theorem ubFreeSpec_pos : UBFreeSpec (fun b => ∃ t, b = .done t) := by …
```

## Boundaries

### Non-claims and scope boundaries

- **Model–system relation (`not examined`; no transfer proved):** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, about any other compiler, or about any verifier that captures compiler IR.
- **Built-in unsafe contract UB in `capDirect` vs. raw IR capture (`known not to apply` without relies-point UB encoding):** All unsafe-trait refinement, UB-free specification transfer, and contract-discharge theorems (`refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract`, `refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract`, `sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`, `contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`) depend on `directCalls` explicitly emitting operational UB whenever an `unsafeTrait` call violates its single-call `env.contract`. A verifier whose captured semantics executes user impl bodies without encoding the unsafe trait's contract as a relies-point UB check operates in the `safeTrait`/`compiled` regime of this toy, where neither lawless refinement nor UB-free specification transfer holds (`cex_without_targetsUnsafe`, `cex_transfer_safe_target`).
- **Law-free semantics of relational and fail-closed remedies (`known not to apply` to `capDirect`):** `compiled`, `capRel`, and `compiledDen` never inspect `env.safety` or `env.contract` and never emit relies-point UB (`capRel_unsafe_ignores_contract_example`). Verification of `capRel` transfers to `compiled`, not to `capDirect` and not to other passes or unsafe consumers that rely on `env.contract`. Likewise, for a verifier sound for `capDirectDen` instead of `compiledDen`, `TransferSound` through `capRejectRewritable` fails to hold in general: for the exact verifier `fun q spec => CaptureBridge.Sat (capDirectDen envUnsafeLog .before q) spec`, `capRejectRewritable cloneToCopy.targets` accepts `probe 1 5` and fails to transfer the UB-tolerant specification `fun r => r.2 = .ub []` (`cex_capRejectRewritable_not_transferSound_for_capDirect`).
- **Attractive stronger conclusions that fail (`known not to apply`):**
  - `LawOnReached` is sufficient, not necessary, for refinement on a single fixed program (`cex_lawOnReached_not_necessary_for_one_program`, contrasted with `cex_deadCall_effectful_not_refined`).
  - Per-program prefix-preserving refinement (`RefinesPP`) is not closed under sequential pass composition (`applySeq`) when an earlier rewrite refines a program without satisfying `LawOnReached` (`cex_refining_rewrites_seq_not_refining`).
  - Pointwise `ContextSafeAt` across every rewrite in `ρs` is not necessary for `applySeq ρs` when targets overlap without `Pairwise TargetsDisjoint`, because an earlier lawful rewrite can shadow a later invalid rewrite (`cex_overlapping_rewrites_conjunction_not_necessary`).
  - Verification of UB-tolerant specifications on `capDirect` does not transfer in general through unsafe-contract rewrites (`cex_ub_tolerant_spec_no_transfer`).
  - Relational capture `capRel` drops properties correlating distinct dynamic calls (`cex_capRel_not_weakest_for_all_or_nothing`) or relying on an impl's non-contract observable effects (`cex_capRel_loses_effect_property`).
- **Unmodelled language, contract, and pass features (`not examined` / `unsupported`):**
  - Multi-call or multi-method stateful trait contracts (such as Rust's `TrustedLen` relating `Iterator::size_hint` to repeated `Iterator::next` calls and divergence) are not modelled; `env.contract i` is a stateless single-call map `Val → List Val × Val`.
  - User impls (`Impl`) are total, deterministic functions of a single `Val` argument; impls that diverge, panic, trigger operational UB themselves, read or mutate shared state/heap, or behave nondeterministically are not modelled.
  - Every rewrite replaces a targeted `call` with inline call-free `prim` code; rewrites whose replacement introduces new trait calls (such as method-to-method forwarding) and laws relating multiple trait instances (such as `Eq`/`Hash` coherence) are not modelled.
  - Programs (`Prog`) are finite straight-line statement lists without branches, loops, recursion, pointers, references, or unwinding; each syntactic statement executes at most once per run.

### Escape hatches

- **`nontrivial-clone-breaks-copy-rewrite` (`cex_nontrivial_clone_copy_rewrite`):** Observable divergence of `cloneToCopy` on a safe trait disappears if `LawOnReached` holds at reached calls (`refinesPP_capDirect_apply_of_lawOnReached`), if the violating impl is effect-free and its return value is dead (`cex_lawOnReached_not_necessary_for_one_program`), if the trait is `unsafeTrait` with relies point `before` and `ReplIsContract` (`refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract`), or if the verifier captures rewritable calls via `capRel` (`sat_compiled_and_apply_of_sat_capRel`) or rejects them via `capRejectRewritable` (`capRejectRewritable_compiledDen_transferSound`).
- **`relies-after-effect-breaks-lawless-refinement-under-prefix-ub` (`cex_relies_after_effect_not_refined`):** Lawless unsafe-contract refinement is recovered by placing the relies point `before` the impl (`refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract`), by relaxing `RefinesPP` to whole-trace `RefinesWT` (`refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract`), by restricting transferred specifications to `UBFreeSpec` (`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`), or by restricting to unsafe impls whose emitted effects are a prefix of the replacement's effects (`contextSafeAt_pos_after_prefix`).
- **`relational-capture-weakest-for-per-site-rewriting` (`capRel_subset_of_sound_for_every_applyAt`):** `capRel env [ρ] p σ` ceases to be the weakest sound capture if the compiler is restricted to all-or-nothing whole-program `ρ.apply` rather than per-site `ρ.applyAt` (`cex_capRel_not_weakest_for_all_or_nothing`), if loops or reusable functions allow one syntactic site to execute multiple times so static per-site `S` cannot vary across dynamic calls (not proved here), or if `hD` quantifies over a proper subclass of trace predicates rather than all `spec : Beh → Prop` (not proved here).
- **`fail-closed-rejection-of-rewritable-calls-sound-and-incomplete` (`capRejectRewritable_incomplete`):** Rejecting all syntactically rewritable calls is avoided by discharging `LawOnReached` (`refinesPP_capDirect_apply_of_lawOnReached`), by discharging reached unsafe contracts via UB-free `capDirect` verification (`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`), or by branching relationally via `capRel` (`sat_compiled_and_apply_of_sat_capRel`).

### Hypotheses with `unknown` tightness

None (`0` `unknown` hypothesis rows across all 15 cards). Every hypothesis in every card's hypothesis ledger (`17` hypothesis rows total) is proved `tight` by a kernel-checked counterexample theorem in `lean/Toy/LawRewrite/Counterexamples.lean` satisfying all remaining hypotheses and falsifying the conclusion.

### Disproved or dropped statements

None. Every target statement in the package is proved in Lean.

## Evidence

### Toolchain, axiom audit, and hash specification

- **Toolchain:** `leanprover/lean4:v4.34.1` (`leanprover/lean4` tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), configured in `lean/lean-toolchain` with single library target `Toy` in `lean/lakefile.toml` and zero external `[[require]]` dependencies (no Mathlib).
- **Observation and kernel verification date:** `2026-11-22`.
- **Axiom audit (`audit/axioms.json`):** `413` non-internal declarations under `Toy.*` were audited with `Lean.collectAxioms`. Zero declarations use `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or custom axioms; every declaration depends only on a subset of `{propext, Classical.choice, Quot.sound}`.
- **Statement and closure hash definition (`audit/statements.json`):** For each of the `203` declarations referenced across `results.json` (`lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` fields):
  - `statement_sha256` is the SHA-256 hex digest of `toString (repr ci.type)` for the compiled `ConstantInfo` `ci` in the Lean environment.
  - `closure_sha256` is the SHA-256 hex digest of the `\n`-joined lexicographically sorted array of entries `c ++ " : " ++ toString (repr cc.type)` (plus `" := " ++ toString (repr v)` whenever `cc` is not a theorem and `cc.value? (allowOpaque := true) = some v`) over every `Toy.*` constant `c` transitively reachable from `ci.type` (traversing types, non-theorem definition values, and inductive constructors, while excluding theorem proof terms). `closure_size` is the number of `Toy.*` constants in that transitive closure.
- **Copied definitions provenance (`lean/Toy/LawRewrite/CaptureBridge.lean`):** Copied verbatim (changing only namespace `Toy.Capture` to `Toy.LawRewrite.CaptureBridge`) from corpus package `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`, file `lean/Toy/Capture/Basic.lean` (Git blob `5e5d90b0cde9fd5ef3772f2543298cad654861b3`, SHA-256 `c7a687dcf3b6e787cf01aaa4c1da2a0b34c9c78d61d2f164a81140119aaa8123`), lines 26–29 (`Den`), 31–34 (`Sat`), 36–38 (`DenIncl`), 50–55 (`OverApproxOnOk`), 57–62 (`VerifierSound`), 70–74 (`TransferSound`), 142–144 (`Sat.of_denIncl`), 186–195 (`transfer_to_capture_input`), 384–388 (`failClosed`), and 433–448 (`failClosed_overApproxOnOk_iff`).

### Primary card declarations: kernel axioms and hashes

| Card | Lean declaration | Axioms | `statement_sha256` | `closure_sha256` (`closure_size`) |
| :--- | :--- | :--- | :--- | :--- |
| `law-on-reached-calls-suffices` | `Toy.LawRewrite.refinesPP_capDirect_apply_of_lawOnReached` | Quot.sound, propext | `ea441cdfde596ecfb90b37818fff1dd8093bee803f0b972490b99ed3b2ce22e9` | `617e77fe160cd350146091003ebb93f06f5bad99edb4c98ccab1035bbf8b64d1` (69) |
| `contextual-refinement-iff-pointwise-context-safety` | `Toy.LawRewrite.refinesPP_every_context_iff_contextSafeAt` | Classical.choice, Quot.sound, propext | `642621e6c2f3c90257888935127bd6597bc8882e835b668f981150d4db8b4ac8` | `00e689a1e512f9e13fc05ada8d3d14c88729258139d25867106d8e4a823295a3` (66) |
| `safe-target-refinement-on-probe-forces-law` | `Toy.LawRewrite.lawAt_of_refinesPP_probe_of_safe_of_targets` | Classical.choice, Quot.sound, propext | `611fee77584ee40dc28479f0509be7a884e3dfe21a4162bd01c1e8fe1612f2d3` | `f0ed4f9630af7f8189e9ac2053d9fa87948191e62e0a717d248f6144125f44f3` (66) |
| `nontrivial-clone-breaks-copy-rewrite` | `Toy.LawRewrite.cex_nontrivial_clone_copy_rewrite` | Quot.sound, propext | `f5529a943467419784c9a91fa9adea86d0a6becfe15247c7d7286180890a232c` | `770bf7a9cb076bb46c1546f53226c093154f50877aa88bd85c6f87ae197efce6` (78) |
| `unsafe-relies-before-rewrite-refines-without-law` | `Toy.LawRewrite.refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract` | Classical.choice, Quot.sound, propext | `11bb05237c819c81b233dd7967549ceacb534c1becc2031e42797ee5672439c7` | `976c51da3c4aafae5e185ec9f46e997c392b4fc09a3f01f42282dbf3d6e00d7d` (66) |
| `relies-after-effect-breaks-lawless-refinement-under-prefix-ub` | `Toy.LawRewrite.cex_relies_after_effect_not_refined` | Quot.sound, propext | `4cef06e0012459ae994ed88a61fcd5f3320526ad0266b7461f7b9d15e1c6d3d1` | `be02a1251cda6fbf9b7ac1d6a9d3122e18bbae78f1c2f2cdd93738df6fefeffb` (74) |
| `whole-trace-ub-unsafe-rewrite-refines-either-position` | `Toy.LawRewrite.refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract` | Quot.sound, propext | `c19427417b8060dac0e38412a5d7826bae44c537e88807644512ede8694b17bd` | `64dce4018940512d57acc8e6b7ee5e04eca1c7c36c242337c0809acb1645389c` (65) |
| `ub-free-verification-transfers-through-unsafe-contract-rewrite` | `Toy.LawRewrite.sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect` | Quot.sound, propext | `542b67bfcb2bd016cd3812316bdfb60359de97d93dbbb8d82b3b38bfaf26e5e7` | `ccb35be50f0389be00f0a76593b636427498a5023915684ce5ca2b736aae4cd4` (65) |
| `ub-free-verification-discharges-contract-at-reached-unsafe-calls` | `Toy.LawRewrite.contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec` | Quot.sound, propext | `e5401cc62466436e7c8eb95cb791bf36b45a8c54eee525da14cdb256586abe66` | `3e5bf81c66dff04ed1beb9372e7071c94926ec984e4aeface30e40b30dcd6f04` (55) |
| `relational-capture-sound-for-every-partial-rewrite` | `Toy.LawRewrite.sat_compiled_applyAt_of_sat_capRel` | Quot.sound, propext | `9f60ce8dd3ebbbdee2c2ea04fcd9e2f5ade2e749a7ae73d9f36fadcf06efd9f0` | `faffb5cbbf3ee1db788adae662df73f5910a943c4721a0533c1b7af3b8d96d04` (53) |
| `relational-capture-sound-for-every-partial-rewrite` | `Toy.LawRewrite.sat_compiled_and_apply_of_sat_capRel` | Quot.sound, propext | `611e44226640e56306bd0abc2e750de1073bdc1171fff7c6a9a40a30d9dfe542` | `a99d4bfeb23eba36dbe6cd98d4ed90166e08fadf9b5f187d5c492d8e5e5d64e5` (51) |
| `relational-capture-weakest-for-per-site-rewriting` | `Toy.LawRewrite.mem_capRel_iff_exists_applyAt` | Quot.sound, propext | `1f8e929610ed26ea2a7ef3a38ed1f625b91122a7bb1d1a8423c1f9f190868480` | `01f195c4d47e10c2514e0d88247ab835873bf534e7647f4e140c1620447aee6e` (52) |
| `relational-capture-weakest-for-per-site-rewriting` | `Toy.LawRewrite.capRel_subset_of_sound_for_every_applyAt` | Quot.sound, propext | `30459f2a349ecf0d98b10952d96c1479f52045ae6e5a64c38eed4bf6b5ec6589` | `faffb5cbbf3ee1db788adae662df73f5910a943c4721a0533c1b7af3b8d96d04` (53) |
| `fail-closed-rejection-of-rewritable-calls-sound-and-incomplete` | `Toy.LawRewrite.capRejectRewritable_compiledDen_transferSound` | propext | `54dc8fed92cce2a9d4fa86ac230bdf551ca9aaf15da262d917d10caccf4dcec9` | `bc6e9e57d9db058ae7ca38be02e3650b9b12b7521ff3dd69d32ef381264ef547` (56) |
| `fail-closed-rejection-of-rewritable-calls-sound-and-incomplete` | `Toy.LawRewrite.capRejectRewritable_incomplete` | propext | `335501dd609cc0d381d64a523c9528c0e2280254324da4d586b4fc2a506254fb` | `795b291e338d1c5139d1824269e2d05953e7929d4200dc5b403623a12ce730fd` (58) |
| `rewrite-sequence-refines-of-laws-on-reached-calls` | `Toy.LawRewrite.refinesPP_capDirect_applySeq_of_lawOnReached` | Quot.sound, propext | `e206aedf5b32e0a8ae588b170ce9f75ccb0218e8011a930a07345389c3ed7946` | `241efe9018ed403f0d765df5e5a0fe12dd4a1101891c4aac45d9dce3e9a04972` (70) |
| `disjoint-rewrite-sequence-contextual-iff-conjunction` | `Toy.LawRewrite.refinesPP_every_context_applySeq_iff_of_pairwise_disjoint` | Classical.choice, Quot.sound, propext | `b37386c76408bbbd7b677c86838655e778780610b4b30737a311bcd4fc7dd790` | `748ed3aa1329609e84e99d34401e09d80ebfc5f221bd6af9f77993d857e0457d` (68) |
| `relational-capture-of-rewrite-list-covers-every-covered-sequence` | `Toy.LawRewrite.mem_capRel_of_mem_compiled_applySeq_of_coveredBy` | Quot.sound, propext | `a41e51f400f4730a47be45e6582c4cfdc1c4cbf1229fe9d72dc078bab2f40fcd` | `0a733dad9db4abac6401a5b0bd7a86f913b1816fa97ba0fc1436027b92b89847` (52) |

### Complete recorded declaration hashes (`203` declarations)

| Declaration | Axioms | `statement_sha256` | `closure_sha256` (`closure_size`) |
| :--- | :--- | :--- | :--- |
| `Toy.LawRewrite.Beh` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Beh.prepend` | none | `0a8edcc0e67276bc54622fdf002eda42fd89ba9435de193e5a6bb001b266e9f0` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.Beh.trace` | none | `422b04e0087d2f7f93a2d8312fe019c4a81e8d65316cebd49f8f404aee5ef8f6` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.CallRes` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.CaptureBridge.Den` | none | `ac04b7a8462b88437b2fcc81d013f2d2454df5a6ca33ffae5d54ebdd38ba7c3d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.CaptureBridge.DenIncl` | none | `ef5ad6c8eda7c1844c6307412a280b4de0ddfdab7c00ff80d55d77ad8bbfee05` | `9508c77b8f5434f597da7c46f633c7f855d785ee49978a6bf6014e900bac8f0e` (1) |
| `Toy.LawRewrite.CaptureBridge.OverApproxOnOk` | none | `2fe0bd8d1768239616e84928c1f9e5009a5d7efef9f34e4eb38cede6ce2db05a` | `9508c77b8f5434f597da7c46f633c7f855d785ee49978a6bf6014e900bac8f0e` (1) |
| `Toy.LawRewrite.CaptureBridge.Sat` | none | `4320ce7c7172d24ffb6abdd0680e3a65dac692957faa302186996ce36a99c8f9` | `9508c77b8f5434f597da7c46f633c7f855d785ee49978a6bf6014e900bac8f0e` (1) |
| `Toy.LawRewrite.CaptureBridge.Sat.of_denIncl` | none | `d2239f35b3fe953ecb0351878d74b8180f09e6d6d7abd83c780a5bfeb5a81534` | `fcaf11bc375a67b98c06db09f74255fcc3cd648df5ce7f5ba69076e458ea83b4` (3) |
| `Toy.LawRewrite.CaptureBridge.TransferSound` | none | `4d299f104c684059d0a8c9bfaf2b6358496d0cf4628944b2ccd2a9e8e688923a` | `9508c77b8f5434f597da7c46f633c7f855d785ee49978a6bf6014e900bac8f0e` (1) |
| `Toy.LawRewrite.CaptureBridge.VerifierSound` | none | `1576cc2c698bfba8cb5f92db4d880db930fc7440f1ada8a684a1c43bbc29899c` | `9508c77b8f5434f597da7c46f633c7f855d785ee49978a6bf6014e900bac8f0e` (1) |
| `Toy.LawRewrite.CaptureBridge.failClosed` | none | `64d09c08878cadfff5956a9b749545165b3e65095c9d3d26bf418765a81871f6` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.CaptureBridge.failClosed_overApproxOnOk_iff` | propext | `5431b788438284b0514a507fe4060a07295b17dabc7f3104fa40162a8f1b198d` | `bb0630f752ff3cc4c85f2231512bd2310b07d658d4f5839f1a5c8f03a1f52597` (4) |
| `Toy.LawRewrite.CaptureBridge.transfer_to_capture_input` | none | `0aecf9fb7caaf8fcbccf00b9b50d0c62abdb8b4934149c43f40aa4f96be67054` | `aaad2ff5b6065f30858a203514a58cbc2d7219cba870cac5429ebd17fffb38d0` (5) |
| `Toy.LawRewrite.ContextSafeAt` | none | `dd7af1fc9c075ad6ad77d52ac02d81720f9689e086c5f1a86cc00ce5b67447c7` | `167d1d70eb687e72833effb03f81d0a2d646ad9c637d40b45ef042b4b52c3caf` (13) |
| `Toy.LawRewrite.CoveredBy` | none | `3b6b2c347ddb6f4e07bf18a6f2ab36cb86106edf0406b5f881ff82da427fba3a` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.Env` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Impl` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.ImprovesPP` | none | `c156e4c5a485c3464d5783613cbb16c5b52414378167c3bbf3245e86a0e58724` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.ImprovesWT` | none | `c156e4c5a485c3464d5783613cbb16c5b52414378167c3bbf3245e86a0e58724` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.Inst` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.LawAt` | none | `56b21f4eb51123d7eebaefb21627250aa5ae0d17ff5eb6651d22e3b63e33e919` | `c7917e4ea8d4775c5345af4ab66a96a5b7bddd635de9d72a6f065a2ee2084336` (10) |
| `Toy.LawRewrite.LawOnReached` | none | `2d5cccf87baf9aa96e6d88138b50b84044f7ea7a3d317843e388d00f3f6c32a1` | `6e04db4bdde71163986b5024693e4d6ae8ee145d5d41d58163a8b7dcd6d14253` (19) |
| `Toy.LawRewrite.LawOnTargets` | none | `4f1f63d3197628a8c278c341234e3c3457a03dcfc869c4a18deb2db04424c2d9` | `c7917e4ea8d4775c5345af4ab66a96a5b7bddd635de9d72a6f065a2ee2084336` (10) |
| `Toy.LawRewrite.Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Reaches` | none | `d1cb6011f64965fb5662ee34c6aea23f675fb01f854bf0eb9f5bdf56256ba40a` | `c843b6d5f4cf29825322c14ceb246d1031d07063376ce7b0213438840424a326` (17) |
| `Toy.LawRewrite.RefinesPP` | none | `7d081c2ec213989714a8a50178e6d353c143f67fa77226bec515fa1cdc574a8a` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.RefinesWT` | none | `7d081c2ec213989714a8a50178e6d353c143f67fa77226bec515fa1cdc574a8a` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.RelyPos` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.ReplIsContract` | none | `4f1f63d3197628a8c278c341234e3c3457a03dcfc869c4a18deb2db04424c2d9` | `c7917e4ea8d4775c5345af4ab66a96a5b7bddd635de9d72a6f065a2ee2084336` (10) |
| `Toy.LawRewrite.Rewrite` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Rewrite.apply` | propext | `caa55cb304be3ce919b7540e263875259a6a8cbe1764aae9f3fe997ccbddca5a` | `d596c8e923c66e6371cfa5968f8b9324d7f7e2ef7821b8ef2de764361c5ed07c` (13) |
| `Toy.LawRewrite.Rewrite.applyAt` | propext | `858ee9e1de1f644cd01ba816c788c985812a9945c6c5e589b3eff1a66e050f72` | `d596c8e923c66e6371cfa5968f8b9324d7f7e2ef7821b8ef2de764361c5ed07c` (13) |
| `Toy.LawRewrite.Rewrite.rwStmt` | propext | `fae360151d96864e8839f8bac1df0e8ad3cf8236a9a2caf4242f8242d5f007b0` | `ed5b22d24eaea04f36e3eab55401d291da3baac9c86fffd081ffa32e21317ae0` (12) |
| `Toy.LawRewrite.Safety` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Sat` | none | `9c45ec08305b41e3673e10142a74faad07b561e06659c7700743f9a7c0d1aea4` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.Stmt` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Store` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Store.upd` | none | `d372f2441422f5286777b9f2470dea13a56f1b43f645d540506ef96bd6e24190` | `cc1a5c4f6b1d23eddd2c54eeb1b66a5d84c6c3e172d9796e4c0bf43b81a1e737` (3) |
| `Toy.LawRewrite.TargetsDisjoint` | none | `025b2f66447eb8efa1610f05c195fcf7935549eb849d8980284a4bd0e4dafd5b` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.TargetsUnsafe` | none | `4f1f63d3197628a8c278c341234e3c3457a03dcfc869c4a18deb2db04424c2d9` | `c7917e4ea8d4775c5345af4ab66a96a5b7bddd635de9d72a6f065a2ee2084336` (10) |
| `Toy.LawRewrite.UBFreeSpec` | none | `bc98efc302abd37e35dc42ed910e0030e35b367291f3d3d3136795553028c1e2` | `f3914fe578525129491d6fd77ccdb7365f294653ff274f51ddc55d0f17fba696` (4) |
| `Toy.LawRewrite.Val` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.Var` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.LawRewrite.applyAt_const_false` | propext | `9842e8a735a169abb99b3993dad3cbd152a81253050dd7f0de0418980ee1deb8` | `b1d15c03556f97a34490d0e21c1b23429a3f79d9b0747f14fbb901e8c8f4894a` (24) |
| `Toy.LawRewrite.applyAt_const_true` | propext | `430fe5873329ba7608531bf95de1b5a23d7de6a9d2a43ab838fb1603a1cbd81d` | `3aa0de35539b23720e10f83d936bf961e5d18884e9257d642da2f31d4c685ddd` (25) |
| `Toy.LawRewrite.applyAt_example` | propext | `5c521c60602045f8e31779014cc1b2b08dcc4534a1559582f6c2d1047bbefd55` | `ab08400353b985aa343de1e0c5a519a925c31a214c2353e768e351402dc6632d` (27) |
| `Toy.LawRewrite.applySeq` | propext | `fdce5dd843d5fe4de4d4e7f08994ec3c042c8cbe1c4abd44f8adc28c9f869625` | `d596c8e923c66e6371cfa5968f8b9324d7f7e2ef7821b8ef2de764361c5ed07c` (13) |
| `Toy.LawRewrite.applySeq_eq_firstMatch` | Quot.sound, propext | `dd7da02e6f2567755ddd012256a6aa54713b62a3147fdee25d9393392952b8a9` | `b2bbe44f319f59b0677390270534773d76af1d4c48457670ae7cc92436c751f4` (26) |
| `Toy.LawRewrite.applySeq_example` | propext | `1651eef909c97bb971c2fedf1898824f71bd038e10f5c48d7c293fc7760fd6e6` | `23cfae9dd6fbb3d59a91cd6c22a7e95594ed650f08d9a7367666eca8382d2298` (26) |
| `Toy.LawRewrite.applySeq_pair` | propext | `3523210fa7dd93500d0cc8793c8000f1381c5ce809edb2e0c7ddd6a5d5f6a9e1` | `086140175d50d2b4286b33b265e5a97c0ac02606562b7a75c0a0a667b35c7da7` (23) |
| `Toy.LawRewrite.apply_apply_of_targets_le` | propext | `771f6981623835161a4888acfb38dbab6305188153fca160901a1678ef02086e` | `dcee43c2fa1f81fe858c043f9b52d41de55c52a3872cdfcc7aa0fa90ba4fa2da` (22) |
| `Toy.LawRewrite.apply_neg` | propext | `4530d35b5caa985d5af00a0c854e0f1de5735d373aad6f3d6f1f0d6d780898a4` | `593bd1e013d1ec87f7f82348fd131924e1e76dcc5d6160b81f78e64286ef26d8` (24) |
| `Toy.LawRewrite.apply_pos` | propext | `f7edaef72452abe99873d24acecfddf70c217281b86e56b3e8348b611808a218` | `ca40a4426afe121a9c6f31c43ecb73fcd04e26337eff7886ba5dc312bd18da8c` (25) |
| `Toy.LawRewrite.callsSome` | propext | `3c177d55de1ab4af8606a068c4dbe9df129d8a5a8d2718c3324b368c6ba936bf` | `db149dc5c5a8946bceb34b1b557da7246b730f044cefc79d736472a288d59f7c` (11) |
| `Toy.LawRewrite.callsSome_neg` | propext | `674d2ce6078f45cfd9b0d4a9ee8c1a3334516ed1c997a8c4ac458153e55a8478` | `c354fc87eca9484bedc06feebfe547de000590f2fe47674b9e68ede52b8c6958` (22) |
| `Toy.LawRewrite.callsSome_neg_untargeted` | propext | `9682fad39de8e66dd4be7a9cd9ddd7ecbb5af5d69bbfd6f40ad68a54e7672cb2` | `c354fc87eca9484bedc06feebfe547de000590f2fe47674b9e68ede52b8c6958` (22) |
| `Toy.LawRewrite.callsSome_pos` | propext | `dbc8b4acd6f5e4418a5f6a2786dd68a29929e98946e6efbd22ed8786d760da59` | `f504bc0a7867de672de4fa8c205fd81f7871b179515229f68b774ca40dc0f343` (23) |
| `Toy.LawRewrite.capDirect` | none | `0adf546c6018a822558d8d7aceb33d41b7617a8d77614fd1b900b6b2b2d756f7` | `1b1ebab35e697d923548f8bb33727bd4b70e1c4da89f44c0cccd4b6717492c7a` (23) |
| `Toy.LawRewrite.capDirectDen` | none | `2c2b57f2cd2b04b376dc5f1e7411792a531e838d0b32c582f120ea3ae17bbbc1` | `0a7ccaccf81dbf3783c77571a768d70847d00908d0bedc09227b1ba7d25b66c0` (24) |
| `Toy.LawRewrite.capDirectDen_neg` | propext | `d44a9be0e912d0f2ebecb49bceb23b3ca13b0f7821079e5e39f4725b56897331` | `15bdd910e078b3bcf490473acf3bc96e61b6a565968a4e84bb639cf64a480b08` (57) |
| `Toy.LawRewrite.capDirectDen_pos` | propext | `bfc023b1dc348577e90c5872e3d0114cf7555b25213327a12134ef7d725fc5c5` | `15bdd910e078b3bcf490473acf3bc96e61b6a565968a4e84bb639cf64a480b08` (57) |
| `Toy.LawRewrite.capDirect_after_example` | none | `d01925c130dcf25aa64066df4c9c2f42aa6050e085f73b55637cc31aa8e032cd` | `ecf4b93c8d8004a6afed365232d07d2c8883b38adeedd828a02eb70b6957c87a` (55) |
| `Toy.LawRewrite.capDirect_before_example` | none | `b57d91456cd9190b9abe4d37064df0c1984d533745cb909c77a79a685f53ca9a` | `ecf4b93c8d8004a6afed365232d07d2c8883b38adeedd828a02eb70b6957c87a` (55) |
| `Toy.LawRewrite.capDirect_eq_compiled_of_allSafe` | Quot.sound, propext | `d62f95a4d3c038ee382a3e53c5542fc1b836dd05e5d87db8fddd30db30c2bc66` | `072c090f5a4e718d806074886224ad7c6499bac61e36018f61ee4262796784b5` (52) |
| `Toy.LawRewrite.capDirect_safe_example` | none | `860639a63326fec602a307b2386b08792a9e03132dbf53f2c054c65c5630b97e` | `9c9bd47e4d1f3d45c20ca2c972655ac87bc585a952392b613e594fa27b676a40` (55) |
| `Toy.LawRewrite.capDirect_singleton` | propext | `017835f807fcd3a07ef0eb328d5da73c4232222cbced405e36adc725b84a5231` | `20cc9055211cff606a77c12a9789c4db383c895bf1b63bebb59e95ed541af15b` (50) |
| `Toy.LawRewrite.capDirect_unsafe_lawful_example` | none | `5cd5306bf3aca73af17b57b5b52b7cbb14865a0505c2961643b237c64cb49949` | `0159becef7d6e10b45d80438c09300e0af3710c3c0de041fdebf6af1d64d8f57` (54) |
| `Toy.LawRewrite.capRejectRewritable` | propext | `eb1e1409976da3cb7b2c7037678d95d0e94c8f07160ecb8ad907872f652daa3d` | `db149dc5c5a8946bceb34b1b557da7246b730f044cefc79d736472a288d59f7c` (11) |
| `Toy.LawRewrite.capRejectRewritable_compiledDen_transferSound` | propext | `54dc8fed92cce2a9d4fa86ac230bdf551ca9aaf15da262d917d10caccf4dcec9` | `bc6e9e57d9db058ae7ca38be02e3650b9b12b7521ff3dd69d32ef381264ef547` (56) |
| `Toy.LawRewrite.capRejectRewritable_incomplete` | propext | `335501dd609cc0d381d64a523c9528c0e2280254324da4d586b4fc2a506254fb` | `795b291e338d1c5139d1824269e2d05953e7929d4200dc5b403623a12ce730fd` (58) |
| `Toy.LawRewrite.capRel` | none | `682acb93f6393e16a9dad69ff65dfb11930c52bce21f3a7928abdc1645a072d3` | `cd10649507004eb241008491cc2f5af21ad68fb6d890b89c41bb33be3fa17266` (22) |
| `Toy.LawRewrite.capRel_example` | none | `7fb2de86e5f08b8a8c2ed0317a6f8192f90aaa8ec8328c62d40b17af038641c8` | `9e567b0ea37e1988243649d70f9897db44a926b2f8019582080d4178741074a5` (49) |
| `Toy.LawRewrite.capRel_ne_nil` | propext | `9134cd09c800bd1453c2cfd8b00bbde78b12f16445ab5c6056bb4fb64c0daed6` | `0e8b8738ac2c945d46da6f061c100b6b46ec7e2b8a07580a89dfcb908fa7f14b` (43) |
| `Toy.LawRewrite.capRel_nil_example` | none | `37ed53396e923cea946ed9eeed808a167bfd9b1b828f2419473007390d2ad328` | `2c4421179bad92779c354d218f1fb3d45730ff61e4aed3254079b697dadb1972` (48) |
| `Toy.LawRewrite.capRel_subset_of_sound_for_every_applyAt` | Quot.sound, propext | `30459f2a349ecf0d98b10952d96c1479f52045ae6e5a64c38eed4bf6b5ec6589` | `faffb5cbbf3ee1db788adae662df73f5910a943c4721a0533c1b7af3b8d96d04` (53) |
| `Toy.LawRewrite.capRel_unsafe_ignores_contract_example` | none | `bcf53cc8bf99b45781734906741f46a41e86ee214103d420d3e6a104f212238a` | `e2a2ed70fba3cca05784990f2d29820230ec33a4096e592e363396cb3aabd8e7` (62) |
| `Toy.LawRewrite.cex_applySeq_without_law` | Quot.sound, propext | `4273a2ba4e0f2e6d9b8152294ed0efb245ea13f92f006d498b22dd41bbddfe3e` | `7c09462ee1145cab3d81c54341d766b08bce01e954314551d556f018da6cf800` (76) |
| `Toy.LawRewrite.cex_capRejectRewritable_not_transferSound_for_capDirect` | propext | `38dd005bf0b9d7f481d9c80539a71dbf27a1a1dfe183ed1ed80c2a83f0f4c534` | `200a3635a0484bfcd9280593c9ea54e3f66ceff68d09dc36356f3b03c80676ca` (74) |
| `Toy.LawRewrite.cex_capRejectRewritable_target_outside_R` | propext | `95135cfbd17085da71a8e2d46b2a94fc796ba77340822fea3713eb137e1c765f` | `18e6270bc99e69ce04b3323621a84392935ece0b32c122f77407ce8861ec4d11` (60) |
| `Toy.LawRewrite.cex_capRejectRewritable_unsound_verifier` | propext | `40c129543f06da6ed902e383bf6cc6380810e3c0053ebd75cb04c201479b2260` | `0c4738a647d5f51067219a6d0aa69c1d83c7005e5f5027a9a885c08f7f6f7289` (59) |
| `Toy.LawRewrite.cex_capRel_loses_effect_property` | none | `31a9a6a2848dbd7250921360bcce0a6c6c92d2918a187e849ff1ebdfe45c1b8b` | `e6ad5122cf7e476970290800046b5fbe3cadbff80aa1aac44a1a71c3722eebc8` (63) |
| `Toy.LawRewrite.cex_capRel_not_weakest_for_all_or_nothing` | propext | `58fbaba42df9124fbc6f1572ce6b4d51c14c175032a8cc8a328b55b2a7b2dbab` | `f95c63fea46878eebb4fb79c5edb70c95a81b77eb84850c6c20ba57d8b04e471` (57) |
| `Toy.LawRewrite.cex_capRel_sound_unverified` | propext | `68e162abc182cff1ee8d4215612fa9e300a3ae80cf78f88be44f5d9a8e0925b7` | `dd0a50f50d546fd2cb3612471b1aa02f9494a30a082cc2b8dbc664fc2c2571a6` (60) |
| `Toy.LawRewrite.cex_capRel_subset_without_soundness` | propext | `0050df3de8cd5294f35be29076f4d3291373d3fc6d927f5d5b560d5fd1b85333` | `19ac6e9cf3dfa639024348c762af17e33af20108f452f54061fbb75075b7b4d2` (59) |
| `Toy.LawRewrite.cex_contract_discharge_safe_call` | propext | `373f29e01af74c7dbd373b1c5fe7102e78cafccd6a18bf242b379210263c0917` | `bc247cfb23802af83ccf901ed9f6016655472a5d828f9778878ccff78eac76d1` (60) |
| `Toy.LawRewrite.cex_contract_discharge_ub_tolerant` | propext | `6d910da5a88510f920527fd73a6249f951f126ecc2575683307c76f6c976d4fc` | `9b8c33ec7323be03b16ffccf0c1ddb5dfcb2c61c0c336e66fd5a6921cfb7745b` (60) |
| `Toy.LawRewrite.cex_contract_discharge_unreached_arg` | propext | `1506c1bf21bfc584b70f1b14f7710fee50a3e04a859f0dd878c93c75c68b2578` | `64634a468050ea7e723cb828c3a6df18d567971f7651d7521ee3565d92649d31` (59) |
| `Toy.LawRewrite.cex_contract_discharge_unverified` | propext | `0ab65304de1ac71634b434724f57b424c3d6bb49afd2cbae924ab5abce48f2b6` | `9b8c33ec7323be03b16ffccf0c1ddb5dfcb2c61c0c336e66fd5a6921cfb7745b` (60) |
| `Toy.LawRewrite.cex_deadCall_effectful_not_refined` | Quot.sound, propext | `208f542c1a777a75715d43da3e3fa966a22b9b99cada9612a1c764f66e0a7313` | `f59e587f073a157945f00e6ec6c9ab91e735fbf06f36a1f396fd11fb3d0d2a52` (70) |
| `Toy.LawRewrite.cex_lawOnReached_not_necessary_for_one_program` | Quot.sound, propext | `542c7ed71852e753ad18100f58141d1222a6a44b4db20fad46ba01a9e7201305` | `74e856667ba1919f9cb2882ffdb1b2eb241bdd3669f5097d462249dbda1fa8ea` (75) |
| `Toy.LawRewrite.cex_nontrivial_clone_copy_rewrite` | Quot.sound, propext | `f5529a943467419784c9a91fa9adea86d0a6becfe15247c7d7286180890a232c` | `770bf7a9cb076bb46c1546f53226c093154f50877aa88bd85c6f87ae197efce6` (78) |
| `Toy.LawRewrite.cex_overlapping_rewrites_conjunction_not_necessary` | Quot.sound, propext | `44e51d9acee2bd73262fc9c6ce4624cadcd08debcd93249d7bc4a18eddcf2d79` | `75759e21f75c5c72a534096a4424fe991602b328428c5ae7351b7ce0b7dd29f0` (74) |
| `Toy.LawRewrite.cex_probe_no_refinement` | Quot.sound, propext | `a6741e12e57605d7e1155b10501cf5e0676b87e8dafbdfa0eba03a34108c866a` | `9113e1c4dd4ae9eddaec52b924fb5f4b9c5f36381e7d5fdd3aaac429d1136656` (71) |
| `Toy.LawRewrite.cex_probe_unsafe_before` | Quot.sound, propext | `397a5b31461973a7b2c02d79089399186983d1906d64127456b3ef4290edbb4e` | `bb5d29f870b39b97e0fe0400b8a85f9db324fde15d74a91ffea3dc470c27a053` (71) |
| `Toy.LawRewrite.cex_probe_untargeted` | Quot.sound, propext | `4fbbab510c00a07e8cbd7e293a9a8c1230e936e24fb7ebfe4b117436546c4d67` | `574128a89f92de333453f9be02829ad6ac710c55a6f76167c54e7aae09398e3d` (71) |
| `Toy.LawRewrite.cex_refining_rewrites_seq_not_refining` | Quot.sound, propext | `cbf746e0fbfbdeb4e5580bfae2aff7fd8550c080f73faff5e6a4327be952b3d6` | `eb46e5c72900e5915eadc2b78129ea4056eff9248748ff54d6287e89a665c3da` (76) |
| `Toy.LawRewrite.cex_relies_after_effect_not_refined` | Quot.sound, propext | `4cef06e0012459ae994ed88a61fcd5f3320526ad0266b7461f7b9d15e1c6d3d1` | `be02a1251cda6fbf9b7ac1d6a9d3122e18bbae78f1c2f2cdd93738df6fefeffb` (74) |
| `Toy.LawRewrite.cex_transfer_repl_not_contract` | propext | `8650cd9b1d5a38232262746ae42b18f89bcc18171dc6f1ac440bcaf590a64080` | `a1bc66b96007f9ae96c4165aa90b1b41181bac82db016a12095f69c4b6e61088` (71) |
| `Toy.LawRewrite.cex_transfer_safe_target` | propext | `831031a38ffede4ac19305981f0998ac0797098cc63019d2a684bfea723898fa` | `57ad908000a3beca68a90d6b9e53ba7fac840f3d25f6429cce079b7ff028d4ad` (71) |
| `Toy.LawRewrite.cex_transfer_unverified` | propext | `7525443ca37bb8f79cd788ae7b156cd673e6e9aff4b0f620feae6fc580206fc2` | `3e988bcb6ea6a08b0aeda58b5345a9f73970d869a419ecd6ff96b0c5f3023086` (70) |
| `Toy.LawRewrite.cex_ub_tolerant_spec_no_transfer` | propext | `d60121384a61bf16dc447ee165fb907621e33bd07e48fed3e49483208d4b6756` | `ff7d1f459849344d70f0d4874ff5908b162564af2c9f5f81afe34be2e682943e` (71) |
| `Toy.LawRewrite.cex_without_coveredBy` | propext | `fb207e86557ca5667c80d556aba1fa8756769ba24b5ae8f50b6aab6fcf3b72e5` | `d2e321a26fc1a47a5ed7c0a37276f8799835a9d0ca85fce43cb300e15048ca70` (58) |
| `Toy.LawRewrite.cex_without_replIsContract` | Quot.sound, propext | `e6833b14afa0d982681a882c84a4c306646c52a37d37c0b36f107a16ffe2bd4b` | `7bcffc2a70db943fb5bfb8e4acf9a0f4b37bf231506c8e71f2ce80a79a363712` (74) |
| `Toy.LawRewrite.cex_without_targetsUnsafe` | Quot.sound, propext | `e7142fef9ce9049612cb4a506b26e8d469e9ae1df2f54acbf4efab2a7491f62a` | `7fdd56a5bee2f778d7ead0ad87602323d019f1ab0827a4a07aacb0ba5c0fad95` (74) |
| `Toy.LawRewrite.cloneToCopy` | none | `9503010093613d9aba2ebf88ff59514e6e218cd1b228bf6672f051cbff6eb055` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.cloneToCopy1` | none | `9503010093613d9aba2ebf88ff59514e6e218cd1b228bf6672f051cbff6eb055` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.compiled` | none | `60945bbd2d3127bc80efc1dbbcb1639b9515fbbaab8b4cf62bca1d7addff9a09` | `ad6935c85ccf4d4d9f2e312a88c5d4a4e728b69503912062abc031359d634958` (20) |
| `Toy.LawRewrite.compiledCalls` | none | `d4e2f6e451f42052e4d45270493b535a9e558b6327aef302b336292746a0a534` | `75284d68a9dae00dc70532c86999796586f10b220920946f206ab6ab1eb370e9` (11) |
| `Toy.LawRewrite.compiledDen` | none | `e96b1bbd57cf5da31fde864d44ef83b3123ca22ff6c32620724104f8eae7d43a` | `4cca5b32d2e919f45e939ea3f1a7ddaac3c842e6d614c39c045430f2c4ebeaca` (21) |
| `Toy.LawRewrite.compiledDen_neg` | propext | `ef9fc88df8516cdfbad434f5cd0a03c5dddbade5e72532586e97407da90d1d64` | `d3eb732f3ee1fa7b1613ca2d98ab64f2868116d93671945fa6678579f10c6abf` (46) |
| `Toy.LawRewrite.compiledDen_pos` | propext | `408c6422468963c9bc835a9e041ff52cc295bfba66ca52a21189e4134811df66` | `d3eb732f3ee1fa7b1613ca2d98ab64f2868116d93671945fa6678579f10c6abf` (46) |
| `Toy.LawRewrite.compiled_apply_eq_of_repl_eq_impl` | propext | `dab075dfcf2496271d6d529ee9b8d58411fae815cddfdea939e80346187ed482` | `ff916fa2192666e87d0ea906f14649b49be41fe37c53ff6bb2af681284c7b117` (48) |
| `Toy.LawRewrite.compiled_envSafeLog_probe` | none | `65870da9744ebcc74234db1c32e5c222ba1b90bd0853c3b2503ee49f16d0e572` | `c1413f76500fe33558c54947e91fa85b950e6ced1e6f00f4517c10ebef6e39f4` (43) |
| `Toy.LawRewrite.compiled_envSafeLog_probe_rewritten` | propext | `2c66b77b7a131351af215fda63ab6c3dfaf3fda6dd1e8bcb698d903b3a94f4de` | `a09f314ac5ffd5f7603dd9b8153c286b9a489c0c5220ea70e8d2234b6ce9d672` (53) |
| `Toy.LawRewrite.compiled_example` | none | `8869b0e2c7a2981d3dcd78fe8d64f8bc0aba4f27f10d7d6c20c813ad5621c040` | `4e10e94bdc918f45bd05dd1013f7b6a7d28c3acf97935555a006722f6b2a9dd0` (44) |
| `Toy.LawRewrite.compiled_singleton` | propext | `f629647b47f85e9ced1c303b1fb8107cb3bd80dd63ef75abdd1a6a838cc52910` | `c35fe26a8a524fa6a81e069535cc62b052a636260b0e2a314d46d18bc7d67329` (39) |
| `Toy.LawRewrite.contextSafeAt_forall_iff_lawOnTargets_of_targetsSafe` | none | `8b4de91e393d2e638a149b3eaefeb769d2da5c03620457d7650f35313236657f` | `e6b0ebdc49df0b889dc07d901978cb01fafbdaa26705163b6948ea05146eaaef` (21) |
| `Toy.LawRewrite.contextSafeAt_iff_lawAt_of_safe` | none | `db864019dcd7da114a600e909e7e140f6e303f8a613f6aa3511985132a5190b4` | `3b84dc3c506f792169546b1dd36c2a3dc3a768d07d6c3a0c9c3c980ce2ea7a3e` (19) |
| `Toy.LawRewrite.contextSafeAt_neg_after` | Quot.sound, propext | `2f36119067ad4d22074f7cb8f196c8f1f12f2a11165e0bf7ba976046268b433d` | `987089accf0b9ce741157425cb115abb80a143faf86db504a3b7ee63660691aa` (23) |
| `Toy.LawRewrite.contextSafeAt_neg_safe` | none | `23a1e90acb1b8a0bfd111e74f9afcb8c847dbc814c299e8d0c852d4074b1ed3c` | `85d36e776b9c1e32de03b89d1982eede1905ad4af064d46b72c770fdad4dfebb` (23) |
| `Toy.LawRewrite.contextSafeAt_neg_unsafe_lawful_noncontract` | propext | `fbc25dfe4ed478985803009c22d4afe7c077a5aa9e981000fa9d9d3998d9a6a0` | `a94cfca1d7eee87fa4599ea3957284dadced6e27fe8f29de08bb513355f64c20` (23) |
| `Toy.LawRewrite.contextSafeAt_pos` | none | `c7a5f9b9313e90401ddad693824092a1a455537676382061cf114b1477b04258` | `987089accf0b9ce741157425cb115abb80a143faf86db504a3b7ee63660691aa` (23) |
| `Toy.LawRewrite.contextSafeAt_pos_after_prefix` | none | `28745981a53ac0256dd28a923fa34ca9de9ae626970ff73d3d82367b7d80339e` | `f3976b0e6062e98e7c01e56a675b9764080290abc5fca5bf15e419c9400b5616` (23) |
| `Toy.LawRewrite.contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec` | Quot.sound, propext | `e5401cc62466436e7c8eb95cb791bf36b45a8c54eee525da14cdb256586abe66` | `3e5bf81c66dff04ed1beb9372e7071c94926ec984e4aeface30e40b30dcd6f04` (55) |
| `Toy.LawRewrite.copyImpl` | none | `756300c806fd9ef56c39467b179111e34d6aa7519631871d96395742a110a422` | `3480346ea9b1b7f1c361e9fcd695843cd47fae63aee88b1711521089fef36981` (2) |
| `Toy.LawRewrite.coveredBy_neg` | none | `7ac50950db1d3f99ebf134f02a1532679ce54425f696ec95a4765d47a4d825a4` | `ccf49556f0b343318bfbb019ed358b8084dbe87ff7b59f7b129f9cc04927b05c` (10) |
| `Toy.LawRewrite.coveredBy_pos` | propext | `577176bdce4094c7c1d0d36a000fc4503dc87f5584e03776bcc94443d9718769` | `ccf49556f0b343318bfbb019ed358b8084dbe87ff7b59f7b129f9cc04927b05c` (10) |
| `Toy.LawRewrite.deadCall` | none | `68ef9a0103e3d5d64b9c0271a6269b1277de5bd710ca31f790b7a74525d4afff` | `db149dc5c5a8946bceb34b1b557da7246b730f044cefc79d736472a288d59f7c` (11) |
| `Toy.LawRewrite.directCalls` | none | `4fc2f8aa4409dd2942679ee0fe248b8729dfe3d90182fb0731f471f9cb05a0f3` | `e84c6d326ba9918cfb9e64afbc63a8da2c3c1a0f101f09308beea49b4580f887` (14) |
| `Toy.LawRewrite.envSafeLog` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envSafeSucc` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envSafeTriv` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envSeqChain` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envUnsafeLog` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envUnsafeSelective` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envUnsafeSucc` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.envUnsafeTriv` | none | `15fa703b4128a606833045a5d8b007df16292c03b64af5baaf6d9309ea20378b` | `1580b2053eac99dc748dde08397018b34ba2456630c9f1d078d47a3b39a7b281` (8) |
| `Toy.LawRewrite.exec` | none | `f9cc40729d6ac4941d49b36292e7b1d6e287755621844bc55501c29ab08b38be` | `07e0db5e862a767d06fbae1af19889d87e6457e7497aff37ae7330e0c0484973` (18) |
| `Toy.LawRewrite.firstMatch` | none | `4332f36bee64e0881de949ca1537ad344fd1cdf75013dae53c4f77287e4d0080` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.firstMatch_neg` | none | `697c452c53bba5362868a239df9215cdb40f5899fac90369ebed8bd3e703c56d` | `da186982b8e1a80104b164b5d9c58c2633a6f0237e659cb8e82f8ea93a8a8af8` (11) |
| `Toy.LawRewrite.firstMatch_pos` | none | `4d5e61895981f32822973bfaa1583e1b2514ef1f1f1e09ce96f763e94077e53b` | `8d2f6f0fd0c99407a317b57aa4528ab1b569c245f324c5445451d600106ed778` (13) |
| `Toy.LawRewrite.guardTenRewrite` | none | `9503010093613d9aba2ebf88ff59514e6e218cd1b228bf6672f051cbff6eb055` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.improvesPP_neg` | Quot.sound, propext | `43eea266ae1bf36fb5dd68c29bb213371c50a04e8b63a985ab8a6f5cd85a3758` | `0746e893e9f43b7399ad762b129e9e700c8a95fa56d83aa0411db341eda2a92f` (9) |
| `Toy.LawRewrite.improvesPP_pos` | Quot.sound, propext | `cddfd85549991b8985ef4c525859151e941aa382faf4c7514d3c1dc7d0f7c0a6` | `0746e893e9f43b7399ad762b129e9e700c8a95fa56d83aa0411db341eda2a92f` (9) |
| `Toy.LawRewrite.improvesWT_neg` | none | `f262a6d423af0529b9652d2bf606834c0e92671173d07e2371bc3e620cd2d399` | `0e490f0410963fea2dbfb639d6900044a1ec491908c099ce42dfc55f7eb5abeb` (5) |
| `Toy.LawRewrite.improvesWT_pos` | none | `9708586b7fcc141922277a8258513de6082a0ab41661b7d7f65a0d079e118847` | `0e490f0410963fea2dbfb639d6900044a1ec491908c099ce42dfc55f7eb5abeb` (5) |
| `Toy.LawRewrite.lawAt_neg` | none | `d274ce48eb3e61f3e65afc4bc1cfc16021c10fc2284f0a74c6a26dcc9353ff45` | `1ded940031b993f9599337213044f8e6decf38acf4e4505425b86a192a4a6293` (17) |
| `Toy.LawRewrite.lawAt_of_refinesPP_probe_of_safe_of_targets` | Classical.choice, Quot.sound, propext | `611fee77584ee40dc28479f0509be7a884e3dfe21a4162bd01c1e8fe1612f2d3` | `f0ed4f9630af7f8189e9ac2053d9fa87948191e62e0a717d248f6144125f44f3` (66) |
| `Toy.LawRewrite.lawAt_pos` | none | `3764a17e2e05b6bbf10f5ce62e5150e72cacb14bd2e72ccbd0e9537877def699` | `82df7d9f6cd61e434b2ce4c049bfa70c2c46ba1a01210b3fdb00137b8f2114a7` (16) |
| `Toy.LawRewrite.lawOnReached_neg` | propext | `eeaabcf6f2013c0f23c2e15cb40d0628496724e384a3d875176259b418a6729c` | `712e2abc454a38df606b684e39117cf8c4be3292712e6958faa0459ab96ecf4a` (36) |
| `Toy.LawRewrite.lawOnReached_pos` | none | `58719e541d42fc740baa15fefc2f7b5a689545b9fdf8c5ec1ada3d13b0633158` | `0f4c199c340e23e9f116105fe2ce3bb5e571f29cd4299cea2b9154b3fd16dc66` (35) |
| `Toy.LawRewrite.lawOnReached_unreached` | none | `d089c0625780fd1a46c76d3b9690042450301f078e0c6083d6e2499a1ac98626` | `709d99819c2fa835736acb2a77556e4bebb19af35076ec529d402328e20739c9` (35) |
| `Toy.LawRewrite.lawOnTargets_neg` | none | `ef7122e534e29cca9f9d3f6baa5b5019647a64bc63da9302ffcd0def6553a8d6` | `ed5d703c84f37905094efe4f1658a2e4f6379516740016b638db7a066f434be5` (19) |
| `Toy.LawRewrite.lawOnTargets_pos` | none | `013ed52ecd7cd0a925754e81d8aa31d678cbfea26c40ce4bccf060e986058bd4` | `bfd23a1e2ab5b2cfcb080f5cb3b826148da2fece3f00a78fe81c53b1d82a007b` (18) |
| `Toy.LawRewrite.loggingClone` | none | `756300c806fd9ef56c39467b179111e34d6aa7519631871d96395742a110a422` | `3480346ea9b1b7f1c361e9fcd695843cd47fae63aee88b1711521089fef36981` (2) |
| `Toy.LawRewrite.mem_capRel_iff_exists_applyAt` | Quot.sound, propext | `1f8e929610ed26ea2a7ef3a38ed1f625b91122a7bb1d1a8423c1f9f190868480` | `01f195c4d47e10c2514e0d88247ab835873bf534e7647f4e140c1620447aee6e` (52) |
| `Toy.LawRewrite.mem_capRel_of_mem_compiled_applySeq_of_coveredBy` | Quot.sound, propext | `a41e51f400f4730a47be45e6582c4cfdc1c4cbf1229fe9d72dc078bab2f40fcd` | `0a733dad9db4abac6401a5b0bd7a86f913b1816fa97ba0fc1436027b92b89847` (52) |
| `Toy.LawRewrite.nonvacuity_applySeq` | Quot.sound, propext | `49a6b71b5f112e93e0ffa4c0ccb3059dd09c7e23776e351b5b6c9db6d0ae512c` | `de9c71a5059196aae2856a4ecb57d47ed6a92c8984e22812d798ee51c38e256e` (77) |
| `Toy.LawRewrite.nonvacuity_capRejectRewritable` | propext | `d2357f83c9e44895d15ec6093c3e9fe55211a64ca5cc392973b3675b08ae00be` | `ea04a456fca9272ea696fd19a427ed2e93deee2248f90532fa6cfb3be588d9f4` (56) |
| `Toy.LawRewrite.nonvacuity_capRel_sound` | none | `0d76173142a47efdaf2eab5e5b2d470d6b15ede8af0c4036c6274fd0418956a5` | `7f59a9e8ee58565ec3eb49d07eb2ce64b415611c5bae959d7cb04872a71dde2a` (51) |
| `Toy.LawRewrite.nonvacuity_capRel_subset` | propext | `0ab0f159779b1e677b7c1af799b74db2bd94c3a3093ba227d3f7d0b356f8b38f` | `a0c049ec75044e6de7ebb18bf6cf669b0d16a308365540fc53bcd0bf61088100` (57) |
| `Toy.LawRewrite.nonvacuity_contextSafeAt` | Classical.choice, Quot.sound, propext | `92354d74da2358604520439394e763f2bc0717e7b409f33ddefbe3d9fbdb317d` | `61628f5a1f4a7a0470ba647e8e59af9bdb268981656a6de76741f107f6ce1919` (30) |
| `Toy.LawRewrite.nonvacuity_coveredBy` | propext | `f829aa3417f2ac37ed9097980353b2345aab985cad2499682011a5692ca37837` | `28bd5394867aee0f7f01ee37f504a7b41cd9caa439c220e8dc57412ddd5aab34` (60) |
| `Toy.LawRewrite.nonvacuity_lawOnReached` | Quot.sound, propext | `f75d7af69fb50c3600ce533686b0786622f3a57ae2f59c8dba1c8ab29b93b5f0` | `675c6de206c73803df3752595853334f4719f242e78569e2561d8fa12bc85d32` (76) |
| `Toy.LawRewrite.nonvacuity_probe_safe` | Quot.sound, propext | `82b53f6def6de8db54767038bb496f2222059ad0658acf6aa79b6085c3eb22ac` | `9606c2a7ff6469f26865b6453865cdfa69d8931d108bf0ce130201805782d628` (69) |
| `Toy.LawRewrite.nonvacuity_ubFree_verification` | propext | `1d65310d1598eae2f8e029c074b75da5081c835c43dc5711d2c35ae19aaa199f` | `90911e4e25f8c2c3666562b91a6797ec20fd7a80af0360b0b8f769761c82a732` (75) |
| `Toy.LawRewrite.nonvacuity_unsafe` | Quot.sound, propext | `575b7991e7ae0f78e36985bdb26e9b565d3ed98a8f341d6130b65799c596c4ae` | `be02a1251cda6fbf9b7ac1d6a9d3122e18bbae78f1c2f2cdd93738df6fefeffb` (74) |
| `Toy.LawRewrite.probe` | none | `3f3f940245ec165a2ada8ba5fd0d19dec3d0c36e349ae28e57c028e5f8e47d97` | `db149dc5c5a8946bceb34b1b557da7246b730f044cefc79d736472a288d59f7c` (11) |
| `Toy.LawRewrite.reaches_neg_after_ub` | propext | `8b706f577a905835ab6c0a13414369d91dc772f8975b41887bd879f2004dbcc0` | `e58b0a5970f25a916941c7df5cfb149bd76a185c80607b4ef7b97d8ec17e4eac` (28) |
| `Toy.LawRewrite.reaches_neg_arg` | propext | `1f55ec60796cc4d1b39373d8f717ef576f7fd021951f35d04c418f070b088cf6` | `b8bd84d75c755d69d052e34111375b862da1151efc51ecf74008f64bf55d3371` (29) |
| `Toy.LawRewrite.reaches_pos` | propext | `df871410ea2388148dc5cef44086898dd1a8e1a7bc728d61b0c02da6eafcf3a0` | `b8bd84d75c755d69d052e34111375b862da1151efc51ecf74008f64bf55d3371` (29) |
| `Toy.LawRewrite.refinesPP_capDirect_applySeq_of_lawOnReached` | Quot.sound, propext | `e206aedf5b32e0a8ae588b170ce9f75ccb0218e8011a930a07345389c3ed7946` | `241efe9018ed403f0d765df5e5a0fe12dd4a1101891c4aac45d9dce3e9a04972` (70) |
| `Toy.LawRewrite.refinesPP_capDirect_apply_of_lawOnReached` | Quot.sound, propext | `ea441cdfde596ecfb90b37818fff1dd8093bee803f0b972490b99ed3b2ce22e9` | `617e77fe160cd350146091003ebb93f06f5bad99edb4c98ccab1035bbf8b64d1` (69) |
| `Toy.LawRewrite.refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract` | Classical.choice, Quot.sound, propext | `11bb05237c819c81b233dd7967549ceacb534c1becc2031e42797ee5672439c7` | `976c51da3c4aafae5e185ec9f46e997c392b4fc09a3f01f42282dbf3d6e00d7d` (66) |
| `Toy.LawRewrite.refinesPP_every_context_applySeq_iff_of_pairwise_disjoint` | Classical.choice, Quot.sound, propext | `b37386c76408bbbd7b677c86838655e778780610b4b30737a311bcd4fc7dd790` | `748ed3aa1329609e84e99d34401e09d80ebfc5f221bd6af9f77993d857e0457d` (68) |
| `Toy.LawRewrite.refinesPP_every_context_iff_contextSafeAt` | Classical.choice, Quot.sound, propext | `642621e6c2f3c90257888935127bd6597bc8882e835b668f981150d4db8b4ac8` | `00e689a1e512f9e13fc05ada8d3d14c88729258139d25867106d8e4a823295a3` (66) |
| `Toy.LawRewrite.refinesPP_neg` | Quot.sound, propext | `83c7638c0a46349d455c22382c6bec4e69f0dafcb9f26481e6867f5ef60d2cd8` | `2b95aff2953fb333022c86da8568a0699aed7184ad92eba13c6948d7d3b648e7` (10) |
| `Toy.LawRewrite.refinesPP_pos` | Quot.sound, propext | `26a124e2cc37e22e1b13c93364bacdbee06f47a7d8f0f43b6d2bb7a4e074aa47` | `2b95aff2953fb333022c86da8568a0699aed7184ad92eba13c6948d7d3b648e7` (10) |
| `Toy.LawRewrite.refinesPP_refl` | none | `0b15e22496c7a8a979fa59e6632b1c35593e3e09fd4e257540d359b96ddbf0e2` | `2b95aff2953fb333022c86da8568a0699aed7184ad92eba13c6948d7d3b648e7` (10) |
| `Toy.LawRewrite.refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract` | Quot.sound, propext | `c19427417b8060dac0e38412a5d7826bae44c537e88807644512ede8694b17bd` | `64dce4018940512d57acc8e6b7ee5e04eca1c7c36c242337c0809acb1645389c` (65) |
| `Toy.LawRewrite.refinesWT_neg` | none | `14e03a66e962de7e0545ba7791fff834a116c98da7394359c0c9c97488a96975` | `d08a0b2ce55f52f79e98c0a99290ecd74b776f70fcb36e5b6d95afcb58829584` (6) |
| `Toy.LawRewrite.refinesWT_pos` | none | `e4066df46221c0ce5c82a2ea4959dcfa59e0f63028388d80bc91e0945b237321` | `d08a0b2ce55f52f79e98c0a99290ecd74b776f70fcb36e5b6d95afcb58829584` (6) |
| `Toy.LawRewrite.relCalls` | none | `818fa0440e6385a8d8ac9c5c8acad2a0fcb3709ffaa031e108c9f48efa621b21` | `fe117e2859bdf716bedccc40442a62521d85e12c1b4c4fbabe4cb001cbc03a54` (13) |
| `Toy.LawRewrite.relCalls_append` | propext | `ec5cfc685d3fd8749e236461a31d5ec6f626f47e3b6b8f20b779d32280647595` | `636586452b88b793748abf00c7dc76e08a493d8dc137de1eb88de660309ffa67` (17) |
| `Toy.LawRewrite.replIsContract_neg` | propext | `38bbe362bdcad37ab6021b82feb92f6ef5ecc29a0407db8316ffc8792ca99465` | `a57bf9ce92d15171520d6a7bf64f0d54f9e92ffd854fb76d124079cc2f0282c6` (18) |
| `Toy.LawRewrite.replIsContract_pos` | none | `87f33eaf3f8f188724cfeabd55d648ffe791889aa6d266e7f4f43534d54650a6` | `1e73183c12a7c0969bd914988f9bdbf939a5ad7eabca22b0d5ac6240c1be8854` (18) |
| `Toy.LawRewrite.sat_compiled_and_apply_of_sat_capRel` | Quot.sound, propext | `611e44226640e56306bd0abc2e750de1073bdc1171fff7c6a9a40a30d9dfe542` | `a99d4bfeb23eba36dbe6cd98d4ed90166e08fadf9b5f187d5c492d8e5e5d64e5` (51) |
| `Toy.LawRewrite.sat_compiled_applyAt_of_sat_capRel` | Quot.sound, propext | `9f60ce8dd3ebbbdee2c2ea04fcd9e2f5ade2e749a7ae73d9f36fadcf06efd9f0` | `faffb5cbbf3ee1db788adae662df73f5910a943c4721a0533c1b7af3b8d96d04` (53) |
| `Toy.LawRewrite.sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect` | Quot.sound, propext | `542b67bfcb2bd016cd3812316bdfb60359de97d93dbbb8d82b3b38bfaf26e5e7` | `ccb35be50f0389be00f0a76593b636427498a5023915684ce5ca2b736aae4cd4` (65) |
| `Toy.LawRewrite.sat_neg` | none | `70093237b6ff39b4d925649a9484e4bb5d28acffa7bdca3871e8e75877f63034` | `96c5ad54aa60a6bdc1fd9f8fe88d0f548a98766b92208c2562e33a61ff0fed3c` (9) |
| `Toy.LawRewrite.sat_pos` | none | `bf18fb9aa5ff47008626086451e079419676aca504a17f1a879efdbd33180f3b` | `96c5ad54aa60a6bdc1fd9f8fe88d0f548a98766b92208c2562e33a61ff0fed3c` (9) |
| `Toy.LawRewrite.seqChainProg` | none | `68ef9a0103e3d5d64b9c0271a6269b1277de5bd710ca31f790b7a74525d4afff` | `db149dc5c5a8946bceb34b1b557da7246b730f044cefc79d736472a288d59f7c` (11) |
| `Toy.LawRewrite.succClone` | none | `756300c806fd9ef56c39467b179111e34d6aa7519631871d96395742a110a422` | `3480346ea9b1b7f1c361e9fcd695843cd47fae63aee88b1711521089fef36981` (2) |
| `Toy.LawRewrite.succRewrite` | none | `9503010093613d9aba2ebf88ff59514e6e218cd1b228bf6672f051cbff6eb055` | `bd1a3fc2147ff4783996b2d0097f05aab880e78bc469e021b9897da222b97a95` (5) |
| `Toy.LawRewrite.targetsDisjoint_neg` | none | `ed450a9bc3d413c97bfe55350c1704213065b83d69ad9805afa7be5d1c310e55` | `5fde270868064865b7bd5c114dafd9c53ba01ef13e91c4c0092f907b49247152` (11) |
| `Toy.LawRewrite.targetsDisjoint_pos` | Quot.sound, propext | `84dfd01343376c5f3203d07a09474b655c2195ac90c63c54d3db09e2d80df74f` | `86513342ff6e67d77c68b2da72004c35dbaac93530318b564d8dfea4f1d19581` (10) |
| `Toy.LawRewrite.targetsUnsafe_neg` | none | `f6c1a98011d0dc74301cb98b1bf277a2888b9225ac8fa8bf6aa7e2656ebcc51d` | `aa23a1d0cb1644160dbe17c6bd35e331c4128f5650821c166dfa6c8204ce58fc` (17) |
| `Toy.LawRewrite.targetsUnsafe_pos` | none | `2129621649623409ae5f45bb59c568aafa365a2973808436c65f6a1f20bea750` | `18e3b87096cf4717cbda4ad94e5d7c0b26f92b2dbc3125e7b4841edc4062a773` (17) |
| `Toy.LawRewrite.twoCalls` | none | `68ef9a0103e3d5d64b9c0271a6269b1277de5bd710ca31f790b7a74525d4afff` | `db149dc5c5a8946bceb34b1b557da7246b730f044cefc79d736472a288d59f7c` (11) |
| `Toy.LawRewrite.ubFreeSpec_neg` | none | `3d26764297f7cbcd95feba9b9c02cf83503527d017027fd83d8322db8e1caebe` | `89b3301092c7f9d624534b2568c3da0600a97e56f0e20e2929366b2b35a2f069` (5) |
| `Toy.LawRewrite.ubFreeSpec_pos` | none | `6294a3b360185c5758283951bbbc88ba5f18d0f6d5e85a8ddedbd911c4122eed` | `89b3301092c7f9d624534b2568c3da0600a97e56f0e20e2929366b2b35a2f069` (5) |
| `Toy.LawRewrite.σ0` | none | `9c34ca9326592be362e815476b7e7c5cb4c76923518df63d455e16f32e1bc382` | `cc1a5c4f6b1d23eddd2c54eeb1b66a5d84c6c3e172d9796e4c0bf43b81a1e737` (3) |

### Primary sources and pinned external artifacts

- **Pinned Rust upstream source (`rust-lang/rust` commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, quoted in `### Modeling bridge — derived (modeling bridge)`):** `library/core/src/clone.rs:82-85` (`Clone` law on `Copy` types), `compiler/rustc_feature/src/unstable.rs:525-526` (`ergonomic_clones` unstable feature gate), `compiler/rustc_codegen_ssa/src/mir/mod.rs:217-224` and `350-407` (`optimize_use_clone`), and `library/core/src/iter/traits/marker.rs:37-47, 60-67` (`TrustedLen`).
- **Pinned CompCert upstream source (`AbsInt/CompCert` commit `2685140bf72c959446981fb99b5e44a8975021bc`):** `common/Behaviors.v:81-82` (`behavior_improves`).
- **Rolling upstream specification note:** The Rust Reference section "Traits — Unsafe traits" (`https://doc.rust-lang.org/reference/items/traits.html#unsafe-traits`, rule identifier `[items.traits.safety]`, verified `2026-11-22`) is cited as descriptive documentation by stable rule identifier and URL; `REPORT.json` records the immutable `rust-lang/rust` repository commit above rather than the rolling web manual.
- S. Peyton Jones, A. Tolmach, T. Hoare, "Playing by the rules: rewriting as a practical optimisation technique in GHC", Proceedings of the 2001 ACM SIGPLAN Haskell Workshop (Utrecht University Technical Report UU-CS-2001-23), pp. 203–233, 2001 (https://www.microsoft.com/en-us/research/publication/playing-by-the-rules-rewriting-as-a-practical-optimisation-technique-in-ghc/): GHC `{-# RULES #-}` pragmas apply domain-specific and typeclass-law-dependent Core rewrites without compiler checking of the law, placing soundness on law satisfaction.
- A. Farmer, N. Sculthorpe, A. Gill, "Reasoning with the HERMIT: tool support for equational reasoning on GHC core programs", Proceedings of the 2015 ACM SIGPLAN Symposium on Haskell, pp. 23–34, 2015, doi:10.1145/2804302.2804303: interactive equational reasoning for verifying GHC Core transformations against algebraic and typeclass laws.
- J. Breitner, A. Spector-Zabusky, Y. Li, C. Rizkallah, J. Wiegley, S. Weirich, "Ready, set, verify! applying hs-to-coq to real-world Haskell code (experience report)", PACMPL 2(ICFP):1–16, 2018, doi:10.1145/3236784: mechanized Coq verification of Haskell library code against specifications including typeclass laws; does not treat post-capture compiler rewrites.
- J. Cockx, N. Tabareau, T. Winterhalter, "The taming of the rew: a type theory with computational assumptions", PACMPL 5(POPL):1–29, 2021, doi:10.1145/3434341: soundness criteria for user-supplied rewrite rules in dependently typed proof assistants; does not treat imperative IR capture or UB refinement.
- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: securing the foundations of the Rust programming language", PACMPL 2(POPL):1–34, 2018, doi:10.1145/3158154: Coq/Iris semantic-typing foundation of Rust's safe-vs-unsafe boundary, where `unsafe` trait invariants are semantic proof obligations of implementers while safe code cannot cause UB.
- X. Denis, J.-H. Jourdan, C. Marché, "Creusot: A Foundry for the Deductive Verification of Rust Programs", ICFEM 2022, LNCS 13478, pp. 90–105, Springer, 2022, doi:10.1007/978-3-031-17244-1_6: deductive MIR verification supporting explicit `#[law]` trait laws discharged on implementations.
- L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust Programs", PACMPL 8(PLDI):1115–1139, 2024, doi:10.1145/3656422: foundational MIR-level refinement-type verification in Coq/Iris; does not treat post-capture law-dependent codegen rewrites.
- The Rust Reference, "Traits — Unsafe traits" (`[items.traits.safety]`, https://doc.rust-lang.org/reference/items/traits.html#unsafe-traits): documents that implementing an `unsafe` trait carries safety obligations that callers and unsafe consumers may rely on.
- B. H. Liskov, J. M. Wing, "A behavioral notion of subtyping", ACM TOPLAS 16(6):1811–1841, 1994, doi:10.1145/197320.197383 (metadata verified at Crossref): substituting a subtype implementation for a supertype specification preserves properties provable from the specification when the implementation meets the behavioral subtyping rules; related in spirit, not a statement about compiler rewrites after capture.
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137, Section 2.1, Definition 3, p. 4): backward simulation for safe source programs (`Safe(S) ⇒ ∀ B, C ⇓ B ⇒ S ⇓ B`, where `Safe(S)` rules out `Wrong` behaviours), corresponding to whole-trace UB exemption (`RefinesWT`) rather than CompCert's later prefix-preserving `behavior_improves`.
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4 (arXiv:0902.2137, Section 2.1, Definition 6, p. 5): preservation of specifications ruling out `Wrong` behaviours (`Spec(B) ⇒ B ∉ Wrong`, `S |= Spec ⇒ C |= Spec`), proved there from backward simulation for safe programs; `UBFreeSpec` and `sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect` instantiate this condition for unsafe-contract rewrites.
- CompCert `common/Behaviors.v` at AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc:81-82, `Definition behavior_improves (beh1 beh2: program_behavior) : Prop := beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.` — the prefix-preserving trace improvement (introduced in CompCert after Leroy 2009) that `ImprovesPP` restates (source behaviour first there, target behaviour first here).
- J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes, "Taming undefined behavior in LLVM", PLDI 2017, pp. 633–647, 2017, doi:10.1145/3062341.3062343: formalizes LLVM's immediate/whole-execution UB refinement, contrasting with CompCert's prefix-preserving `Goes_wrong` refinement.
- N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, "Alive2: bounded translation validation for LLVM", PLDI 2021, pp. 65–79, 2021, doi:10.1145/3453483.3454030: automated translation validation of LLVM optimizations under whole-trace UB refinement.
- R.-J. Back, J. von Wright, Refinement Calculus: A Systematic Introduction, Springer, 1998, doi:10.1007/978-1-4612-1674-2: textbook treatment of demonic nondeterministic choice as the universal over-approximation (least upper bound) of possible implementations, and of non-distributivity between local step choice and global choice.
- P. Lammich, "Refinement for Monadic Programs", Archive of Formal Proofs (Isabelle/HOL), 2012, ISSN 2150-914X (https://isa-afp.org/entries/Refine_Monadic.html): mechanizes nondeterministic result-set over-approximation and refinement with failure as top.
- B. Delaware, C. Pit-Claudel, J. Gross, A. Chlipala, "Fiat: Deductive Synthesis of Abstract Data Types in a Proof Assistant", POPL 2015, pp. 689–700, 2015, doi:10.1145/2676726.2677006: Coq mechanization of refinement from nondeterministic relational specifications to deterministic implementations.
- Reference corpus package `zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume`: UB-erasing eliminations stated with the same two refinement disciplines (prefix-preserving `ImprovesPP`, whole-trace `ImprovesWT`) in a different toy; this package restates the disciplines independently.
- Reference corpus package `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches`: further UB-erasing rewrites under prefix-preserving refinement; related, no shared definitions.
- Reference corpus package `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets`, card `R6-spec-transfer`: verification of a closed target transfers when, among other hypotheses, every user impl body (trait method, user `Drop`, user `Clone`) verifies against its spec — the analogous obligation on user impls in a monomorphization model.
- Reference corpus package `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`: the capture bridge (`OverApproxOnOk`, `TransferSound`, `failClosed`) for passes before the capture point; its card `fail-closed-and-fail-open-obligations` (`failClosed_overApproxOnOk_iff`) is copied verbatim into `CaptureBridge.lean`. This package treats rewrites after the capture point.
- Reference corpus report `closure-upvar-defunctionalization-symbolic-vtables-and-trait-coherence-laws`: coherence-keyed law registries against dictionary spoofing — which law instance a proof may assume; related, it does not treat rewrites that depend on a law.
- Reference corpus report `anneal-trusted-mir-gvn-instsimplify-algebraic-and-discriminant-folding`: algebraic identities used by simplification passes, with no user-implementable trait law; related prior art (cited by its slug; no claim is made about any verifier's implementation).

## Revalidation

Requirements: `elan` (so that `lake` selects `leanprover/lean4:v4.34.1` from `lean/lean-toolchain`) and `python3`.

### Primary automated check

Run from the package root directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` into a fresh temporary directory without modifying the package. It:
1. scans every `.lean` source file (with comments stripped) to reject `sorry`, `admit`, `native_decide`, and `axiom` declarations;
2. runs `lake build` on the clean copy;
3. executes an inline Lean `CommandElabM` audit over the compiled `Toy` environment that calls `Lean.collectAxioms` on every non-internal `Toy.*` constant and rejects any axiom outside `{propext, Classical.choice, Quot.sound}`; and
4. recomputes `statement_sha256` (SHA-256 of `toString (repr ci.type)`), `closure_sha256` (SHA-256 of the sorted newline-joined `name : repr type [:= repr value]` strings of all `Toy.*` constants transitively reachable from `ci.type`, excluding theorem bodies), and `closure_size` for every declaration referenced by `results.json` or recorded in `audit/statements.json`, verifying exact equality with `audit/statements.json`.

Expected output ends with `REVALIDATED` and exit status `0`.

### Standalone build, `#print axioms`, and hash check using `elan`, `lake`, and `python3`

To rebuild the Lean library directly and run the shipped `#print axioms` suite (`lean/Audit.lean`, outside the `Toy` library target, covering all 129 public theorems):

```sh
(cd lean && lake build && lake env lean Audit.lean)
```

Expected: `lake build` succeeds with zero warnings, and every `#print axioms` line in `Audit.lean` reports either `does not depend on any axioms` or a subset of `[propext, Classical.choice, Quot.sound]`.

To recompute the full `collectAxioms` and statement/closure SHA-256 audit directly without `support/revalidate.py`, run from the package root directory:

```sh
python3 - <<'PY'
import hashlib, json, os, re, shutil, subprocess, tempfile

pkg = os.path.abspath(".")
recorded = json.load(open(os.path.join(pkg, "audit/statements.json")))["statements"]
allowed = {"propext", "Classical.choice", "Quot.sound"}

def lit(n):
    return "`" + ".".join(p if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?]*", p) else f"«{p}»" for p in n.split("."))

lean_src = f'''import Lean
import Toy
open Lean Elab Command

private def wanted : List Name := [{", ".join(lit(n) for n in sorted(recorded))}]

private def inToy (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inToy env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with | .inductInfo iv => iv.ctors | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inToy env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in wanted do
    if let some ci := env.find? n then
      let cl := closure env (ci.type.getUsedConstants.toList) {{}}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ("AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
'''

with tempfile.TemporaryDirectory() as tmp:
    work = os.path.join(tmp, "lean")
    shutil.copytree(os.path.join(pkg, "lean"), work, ignore=shutil.ignore_patterns(".lake"))
    subprocess.run(["lake", "build"], cwd=work, check=True)
    open(os.path.join(work, "ManualAudit.lean"), "w").write(lean_src)
    out = subprocess.run(["lake", "env", "lean", "ManualAudit.lean"], cwd=work, check=True, capture_output=True, text=True).stdout
    data = json.loads(re.search(r"AUDIT_JSON (\{.*\})", out).group(1))
    bad_ax = [d for d in data["decls"] if set(d["axioms"]) - allowed]
    assert not bad_ax, f"Disallowed axioms: {bad_ax}"
    got = {
        s["name"]: {
            "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
            "closure_size": len(s["closure"]),
        }
        for s in data["stmts"]
    }
    assert got == recorded, "Statement/closure hash mismatch!"
    print(f"OK: {len(data['decls'])} declarations axiom-clean, {len(got)} statement/closure hashes verified.")
PY
```

### Revalidating the modeling bridge

Passing the Lean checks above revalidates the `Toy.LawRewrite` theorems under `leanprover/lean4:v4.34.1`; it does not revalidate claims about any external compiler. To revalidate `### Modeling bridge — derived (modeling bridge)` against a newer revision of `rust-lang/rust`, inspect `library/core/src/clone.rs`, `compiler/rustc_feature/src/unstable.rs`, `compiler/rustc_codegen_ssa/src/mir/mod.rs`, and `library/core/src/iter/traits/marker.rs` at the target revision and compare their documented contracts and pass conditions against the ranges recorded under `## Evidence`.
