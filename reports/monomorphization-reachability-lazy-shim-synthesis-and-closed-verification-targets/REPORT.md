# Monomorphization reachability, on-demand shim synthesis and closed verification targets in a toy model (Lean 4)

## Summary

This package is a Lean 4 toy model of whole-program monomorphization with compiler-synthesized shims. Its programs have generic functions, trait methods implemented at literal types, user `Drop` and `Clone` bodies, trait objects created by unsizing, function pointers created by reification (including the reify shim that a `trackCaller` function needs when reified), and three kinds of shim keys (drop glue, clone shims, reify shims) whose bodies a synthesizer supplies. One fuel-indexed interpreter, `runKey`, runs under two resolvers: the source semantics `runS` (generic bodies instantiated by substitution followed by single-pass associated-type normalization; drop and clone behaviour of shim keys given by the source rules `glueSrc` and `cloneSrc`) and the mono semantics `runM` (the table `tableM P cfg T`, restricted to a key list `T`, that holds the synthesized shim bodies). The worklist collector `collect` gathers the keys reachable from a root list under an edge function. A key list `T` is *closed* (`Closed`) when every key of `T` has a body in the table and every runtime reference of that body lies in `T`. The package contains 14 results (R1–R14); every theorem is kernel-checked, and the axiom audit lists at most `propext`, `Classical.choice` and `Quot.sound` for every declaration.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier. Every connection to rustc or the Rust Reference is a separate claim labelled `derived (modeling bridge)` (Findings, Modeling bridges).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One entry per result: its plain-language claim, verbatim from its card, with every hypothesis. Hypothesis labels ((HR), (HE), (H1), (H2), (H2t), (H3a), (H3b), (H0)) are defined at the start of Findings.

- **R1** (`closed_of_edgesIn_covering_total_canonicalRefs_instDefined`; theorem, T1): In the toy pipeline, for every program `P`, configuration `cfg` and key list `T`: if `T` is closed under the collector's edge function `edgesM P cfg` (HE), the edge function `cfg.E` covers every runtime reference of every body (H1: `call`, `invoke`, `mcall`, operand-position `reify`, every trait method at an unsized type plus that type's drop glue, drops on normal and cleanup paths, clones, and the clones and drops of `cloneAgg`), the synthesizer is defined on every shim key of `T` (H2t), every key referenced by a body the compiler emits for a key of `T` is in normal form (H3b), and the source defines every non-shim key of `T` (H0), then the table restricted to `T` is closed: every key of `T` has a body and every runtime reference of that body lies in `T`.
- **R2** (`runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical`; theorem, T1): For every program, configuration, root list and key list `T`: if every root is in `T` (HR), `T` is closed under the collector's edge function (HE), the edge function covers every runtime reference (H1), on every shim key of `T` the synthesized body is defined exactly when the source construct is and, when both are defined, is behaviourally equivalent to it under every call oracle (H2), every key of `T` is in normal form (H3a), and every key referenced by a body the compiler emits for a key of `T` is in normal form (H3b), then for every root, every fuel and every initial state, the mono semantics restricted to `T` (`runM`) yields the same outcome and final state as the source semantics (`runS`); both are runs of the shared interpreter `runKey`.
- **R3** (`cleanup_edges_missing_break_closure`, `vtable_edges_missing_break_closure`, `operand_edges_missing_break_closure`, `reify_shim_edges_missing_break_closure`; counterexample, T1): For each of four collector edge functions that omit one runtime reference kind — (a) drops on cleanup paths (`refsNoCleanup`), (b) the method entries of a vtable created by unsizing (`refsNoVtable`), (c) functions reified in operand position (`refsNoOperand`), (d) the reify shim a `trackCaller` function needs when reified (`refsNoReifyShim`) — there is a concrete program on which every other hypothesis of R1 and of R2 holds (roots in `T`, edge-closure, synthesizer agreement and totality, source definedness, canonical keys and references), the collected target is not closed, the adequacy conclusion fails, and the run of the collected program from the root ends in `Res.link` of a specific missing key, while the source run completes or unwinds normally.
- **R4** (`ladder_exec_eq_cloneAgg`; theorem, T1): For every call oracle, every list of field types, every frame and every state, executing the explicit ladder `ladder fs` (clone field `i` left to right; if that unwinds, drop the clones of fields `i-1, …, 0`; a panic in such a drop aborts) gives exactly the same outcome, frame and state as the source aggregate clone `cloneAgg fs` (clone operands left to right; on unwinding drop the evaluated operands in reverse order of creation; a panic in cleanup aborts).
- **R5** (`no_source_only_verdict_correct_for_every_synthesizer`, `source_defs_verified_yet_program_violates_spec_under_reverse_glue`; impossibility, T1): For every Boolean verdict `V` that is a function of a program and its spec assignment (any function `Program → (Key → Spec) → Bool`, computable or not): in program `P4a` (a guard type whose destructor emits 10, a data type whose destructor emits 20, `main` drops a pair of them) with the specs `Q4a` ("release before free"), every generic body is verified (`GenericVerified`) and every user impl in `T4a` conforms (`ImplsConform`), and there is a configuration — the standard one or the reverse-declaration-order glue variant `cfgRev`, which differ in the synthesized glue of the pair — whose table restricted to `T4a` is closed and for which `V P4a Q4a = true` disagrees with whether `main` meets its spec in that table. Concretely, under `cfgRev` the target is closed, the user side is verified, and `main` emits `[20, 10]` and violates its spec, while under the standard configuration every key meets its spec (`P4a_std_meets_specs`). Escape hatch (positive control `srcVerdict_correct_of_adequacy`): for every program, spec assignment, configuration and target such that R2's hypotheses hold with roots `[main]` — (HR), (HE), (H1), (H2), (H3a) and (H3b) — the noncomputable verdict `srcVerdict` ("`main` meets its spec in `runS`"), a function of the program and specs alone, is true exactly when `main` meets its spec in the table restricted to the target.
- **R6** (`closed_target_meets_specs_of_generic_impl_synth_verified`, `closed_target_meets_specs_in_source_semantics`; theorem, T0): For every program, configuration, key list `T` and spec assignment `Q`: if the table restricted to `T` is closed, every generic body is verified at every instantiation against its spec assuming `Q` on the keys it requests, every user impl body (trait method, user `Drop`, user `Clone`) of a key in `T` verifies against its spec, and every synthesized body for a shim key of `T` verifies against its spec, then every key of `T` meets its spec in the monomorphic table `tableM P cfg T` (`MeetsAt`: every run of `runKey` over that table, at every fuel and initial state, satisfies the spec), in the partial-correctness sense (out-of-fuel outcomes exempt). If, in addition, on every shim key of `T` the synthesized body is defined exactly when the source construct is and is behaviourally equivalent to it under every call oracle (H2), and every key of `T` is in normal form (H3a), then every key of `T` meets its spec in the source semantics `runS` (`closed_target_meets_specs_in_source_semantics`). Edge-closure, (H1) and (H3b) are not hypotheses of that theorem: the edge function `cfg.E` does not occur in `tableM`, and on a closed target (H3b) follows from (H3a) (`canonicalRefs_of_closed_canonicalKeys`).
- **R7** (`collect_mem_iff_reach`, `collect_order_independent`; characterization, T0): For every edge function, every admissible scheduler (one that neither loses nor invents worklist entries), every root list and fuel: if the worklist collector `collect` returns `T`, then `T` contains exactly the keys reachable from the roots; hence two admissible schedulers that both return a set return sets with the same members.
- **R8** (`polyrec_runs_finite`, `polyrec_instances_reachable`, `polyrec_collector_diverges`; counterexample, T0): In program `P5` (`main` calls `f::<base 0>`; `f<T>` calls `f::<Box<T>>` under the counter guard), for every initial counter value `c` the source run of `main` with fuel `c + 3` completes normally; yet every `f::<Box^k<base 0>>` is reachable, and for every admissible scheduler and every fuel the worklist collector returns `none`.
- **R9** (`collect_terminates_of_rankCheck_of_assocNormal`; theorem, T1): For every program `P`, every rank function `rank` such that `rankCheck P rank = true` (every function-instance reference in a function body from `f` to `g` has `rank g ≤ rank f`, strictly `<` when some type argument mentions a type parameter under `box`, `pair` or `proj`), if every right-hand side of `P.assoc` is in normal form (`assocNormal P = true`), then for every admissible scheduler and every root list there is a fuel at which the standard collector returns a set.
- **R10** (`precomputed_and_on_demand_synthesis_same_target`; theorem, T0): For every program, edge function, synthesizer `synth`, precomputed shim table `pre`, roots, admissible schedulers and fuels: if `pre` agrees with `synth` on every shim key reachable under the on-demand pipeline, and both pipelines' collectors return sets, then the sets have the same members and the emitted tables coincide on every key.
- **R11** (`linkUnits_eq_tableM_of_deterministic`; theorem, T0): For every program, edge function, synthesizer `synth`, key list `T` and list of codegen units: if every unit's synthesizer agrees with `synth` on the shim keys that unit lists, and the units together list exactly the keys of `T` (shim keys may be listed by several units), then the linked table (first listing unit wins) equals the single-target table on `T` at every key.
- **R12** (`canonicalRefs_stdCfg_of_assocNormal`, `noncanonical_refs_break_closure`; theorem, T1): For every program `P` and key list `T`: if every right-hand side of `P.assoc` is in normal form (`assocNormal P = true`) and every key of `T` is in normal form (H3a), then every key referenced by a body the standard pipeline emits for a key of `T` is in normal form (H3b). By contrast, in program `P6chain` (as `P6`, with the chained associated-type table `<base 0 as 0>::Out = <base 0 as 1>::Out`, `<base 0 as 1>::Out = base 1`, on which `assocNormal` fails), with the full edge function and the standard synthesizer, every hypothesis of R1 and R2 except (H3b) holds, the target is not closed, and the collected program's run ends in a link error at the once-normalized key `h::<<base 0 as 1>::Out>`, while the source run emits 9.
- **R13** (`collected_set_includes_dead_code_not_minimal`; counterexample, T0): In program `P7a` (`main` panics before calling function 1), the collector includes `inst 1 []`, yet removing it from the table changes no run from the root at any fuel and state; the smaller set is not closed under the collector's edges.
- **R14** (`per_crate_collection_has_holes`; counterexample, T0): In program `P7b` (`main` calls `ext`, a non-generic function whose body drops a value with a destructor), a per-crate collector that creates no node for the unavailable key `inst 1 []` returns a target that is not closed, and the run from `main` ends in a link error at that key while the source run emits 3; collecting with every body available yields a closed target whose run from `main` agrees with the source at every fuel and state.

Non-claims for every result come first under **Boundaries** (scope of all results, then per result); escape hatches, tightness status and open questions follow them there.

## Applicability

### Model fidelity

This is a toy model. Its definitions are meant to capture the structure that rustc's mono-item collector documents (mono items as the nodes of a graph whose edges are uses, collected from roots until no new nodes are found), the compiler-generated shims that a collected program relies on (drop glue, clone shims, the reify shim of a `#[track_caller]` function), and the obligation that a whole-program verification target have a body for every key that its bodies can reach at run time. Known gaps, each restated in the non-claims of the cards it affects:

- Every impl entry is for one literal type; there are no generic `impl<T>` blocks, no generic `Drop`/`Clone` impls, and no parametric associated-type rules (§1.1, "Restrictions of the toy").
- There are no value arguments, closures, statics, constants, "mentioned" items, `FnPtr`/`ClosureOnce`/`VTable` receiver shims, async drop glue, enums or drop flags (§1.1, R1).
- `Ty.norm` is a single bottom-up normalization pass, not rustc's normalization (§1.1, R12).
- The toy has no type system (R8), no heap, frame rule or ownership in its specifications (R6), no function-pointer or vtable-pointer address comparison and no linker (R11), and no parallel collection or used/mentioned distinction (R7).
- Fuel bounds call depth; outcomes are fuel-indexed, and `outOfFuel` is an outcome of the interpreter (§1.3).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier. The Lean statements are about the definitions quoted below; whether those definitions faithfully describe rustc is a separate question, addressed for individual constructs by `derived (modeling bridge)` claims that cite rustc's documentation and the Rust Reference.

### Lean environment

Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`), core Lean and `Std`, without Mathlib. The Lake project in `lean/` declares one library, `MonoShim` (namespace `Toy.MonoShim`), and no dependencies. Every statement block in this report is a verbatim quote of the Lean source with its `file:line` range; proofs are elided.

### Subjects and how they relate

The Lean toolchain is the checker of every theorem. `rust-lang/rust` at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (the mono-item collector, the shim builder, the instance kinds, drop elaboration, and the documentation of `core::ptr::eq` and `core::ptr::fn_addr_eq`) and `rust-lang/reference` at commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (destructors, `#[track_caller]`) were read as documentation and source for the modeling bridges and the prior-art notes; they were neither built nor executed, and none of their behaviour is kernel-checked. The papers listed under **Evidence** are prior art for the tiers; none of their theorems is used in a proof.

### 1. The toy model (definitions)

#### 1.1 Syntax

Types (`pair a b` is a two-field tuple; `param i` a type parameter; `proj tr τ` the projection `<τ as tr>::Out`):

```lean
-- lean/MonoShim/Core.lean:15-23
inductive Ty where
  | base : Nat → Ty
  | box : Ty → Ty
  | pair : Ty → Ty → Ty
  | dyn : Nat → Ty
  | fnPtr : Ty
  | param : Nat → Ty
  | proj : Nat → Ty → Ty
  deriving DecidableEq, Repr
```

Symbol keys (mono items). `dropGlue`, `cloneShim` and `reifyShim` are shim keys, answered by the synthesizer:

```lean
-- lean/MonoShim/Core.lean:30-38
inductive Key where
  | inst : Nat → List Ty → Key
  | meth : Nat → Nat → Ty → Key
  | userDrop : Nat → Key
  | userClone : Nat → Key
  | dropGlue : Ty → Key
  | cloneShim : Ty → Key
  | reifyShim : Nat → List Ty → Key
  deriving DecidableEq, Repr
```
```lean
-- lean/MonoShim/Core.lean:41-45
def Key.isShim : Key → Bool
  | .dropGlue _ => true
  | .cloneShim _ => true
  | .reifyShim _ _ => true
  | _ => false
```

Statements. Calls carry no value arguments; a frame holds the function pointers and trait objects created by `reify` and `unsize`:

```lean
-- lean/MonoShim/Core.lean:54-72
inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | emit : Nat → Stmt
  | panic : Stmt
  | call : Nat → List Ty → Stmt
  | invoke : Key → Stmt
  | mcall : Nat → Nat → Ty → Stmt
  | drop : Ty → Stmt
  | clone : Ty → Stmt
  | reify : Nat → Nat → List Ty → Stmt
  | callPtr : Nat → Stmt
  | unsize : Nat → Ty → Nat → Stmt
  | callDyn : Nat → Nat → Stmt
  | dropDyn : Nat → Stmt
  | onUnwind : Stmt → Stmt → Stmt
  | cloneAgg : List Ty → Stmt
  | guard : Stmt → Stmt
  deriving DecidableEq, Repr
```

Programs, impl entries, and the static signature both semantics share:

```lean
-- lean/MonoShim/Core.lean:75-78
structure FnDef where
  trackCaller : Bool
  body : Stmt
  deriving Repr
```
```lean
-- lean/MonoShim/Core.lean:81-86
structure ImplEntry where
  tr : Nat
  m : Nat
  ty : Ty
  body : Stmt
  deriving Repr
```
```lean
-- lean/MonoShim/Core.lean:91-97
structure Program where
  fns : List FnDef
  methods : List (Nat × List Nat)
  impls : List ImplEntry
  dropImpls : List (Nat × Stmt)
  cloneImpls : List (Nat × Stmt)
  assoc : List (Nat × Ty × Ty)
```
```lean
-- lean/MonoShim/Core.lean:100-102
structure Sig where
  tc : Nat → Bool
  methods : Nat → List Nat
```
```lean
-- lean/MonoShim/Core.lean:104-106
def Program.sig (P : Program) : Sig where
  tc f := ((P.fns[f]?).map FnDef.trackCaller).getD false
  methods tr := (P.methods.lookup tr).getD []
```

**Restrictions of the toy that later cards rely on.** Every impl entry is for one literal type: `implLookup` (§1.3) matches `ImplEntry.ty` by equality and never substitutes into an impl body, so there are no generic `impl<T>` blocks. User `Drop`/`Clone` bodies (`dropImpls`, `cloneImpls`) attach to nominal leaf types `base n`, which have no fields; there are no generic `Drop`/`Clone` impls. Associated types (`assoc`) are literal triples `(tr, ty, out)`; there are no parametric associated-type rules. There are no value arguments, closures, statics, constants, "mentioned" items, `FnPtr`/`ClosureOnce`/`VTable` receiver shims, or async drop glue.

Substitution and normalization. `Ty.norm` is a single bottom-up pass: the right-hand side found in the table is returned without being normalized again, so on a table whose outputs contain reducible projections it is not idempotent (`assocNormal_examples`); `ty_norm_idem_of_assocNormal` (§1.5) gives idempotence when every right-hand side is already normal. Source bodies are instantiated by `Stmt.subst` followed by `Stmt.norm`.

```lean
-- lean/MonoShim/Core.lean:110-115
def Ty.subst (σ : List Ty) : Ty → Ty
  | .param i => σ.getD i (.param i)
  | .box t => .box (t.subst σ)
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .proj tr t => .proj tr (t.subst σ)
  | t => t
```
```lean
-- lean/MonoShim/Core.lean:117-123
def Key.subst (σ : List Ty) : Key → Key
  | .inst f τs => .inst f (τs.map (Ty.subst σ))
  | .meth tr m t => .meth tr m (t.subst σ)
  | .dropGlue t => .dropGlue (t.subst σ)
  | .cloneShim t => .cloneShim (t.subst σ)
  | .reifyShim f τs => .reifyShim f (τs.map (Ty.subst σ))
  | k => k
```
```lean
-- lean/MonoShim/Core.lean:125-137
def Stmt.subst (σ : List Ty) : Stmt → Stmt
  | .seq a b => .seq (a.subst σ) (b.subst σ)
  | .call f τs => .call f (τs.map (Ty.subst σ))
  | .invoke k => .invoke (k.subst σ)
  | .mcall tr m t => .mcall tr m (t.subst σ)
  | .drop t => .drop (t.subst σ)
  | .clone t => .clone (t.subst σ)
  | .reify j f τs => .reify j f (τs.map (Ty.subst σ))
  | .unsize j t tr => .unsize j (t.subst σ) tr
  | .onUnwind a b => .onUnwind (a.subst σ) (b.subst σ)
  | .cloneAgg ts => .cloneAgg (ts.map (Ty.subst σ))
  | .guard s => .guard (s.subst σ)
  | s => s
```
```lean
-- lean/MonoShim/Core.lean:139-140
def assocLookup (A : List (Nat × Ty × Ty)) (tr : Nat) (t : Ty) : Option Ty :=
  (A.find? (fun e => decide (e.1 = tr ∧ e.2.1 = t))).map (fun e => e.2.2)
```
```lean
-- lean/MonoShim/Core.lean:147-151
def Ty.norm (A : List (Nat × Ty × Ty)) : Ty → Ty
  | .box t => .box (t.norm A)
  | .pair a b => .pair (a.norm A) (b.norm A)
  | .proj tr t => (assocLookup A tr (t.norm A)).getD (.proj tr (t.norm A))
  | t => t
```
```lean
-- lean/MonoShim/Core.lean:153-159
def Key.norm (P : Program) : Key → Key
  | .inst f τs => .inst f (τs.map (Ty.norm P.assoc))
  | .meth tr m t => .meth tr m (t.norm P.assoc)
  | .dropGlue t => .dropGlue (t.norm P.assoc)
  | .cloneShim t => .cloneShim (t.norm P.assoc)
  | .reifyShim f τs => .reifyShim f (τs.map (Ty.norm P.assoc))
  | k => k
```
```lean
-- lean/MonoShim/Core.lean:163-175
def Stmt.norm (P : Program) : Stmt → Stmt
  | .seq a b => .seq (a.norm P) (b.norm P)
  | .call f τs => .call f (τs.map (Ty.norm P.assoc))
  | .invoke k => .invoke (k.norm P)
  | .mcall tr m t => .mcall tr m (t.norm P.assoc)
  | .drop t => .drop (t.norm P.assoc)
  | .clone t => .clone (t.norm P.assoc)
  | .reify j f τs => .reify j f (τs.map (Ty.norm P.assoc))
  | .unsize j t tr => .unsize j (t.norm P.assoc) tr
  | .onUnwind a b => .onUnwind (a.norm P) (b.norm P)
  | .cloneAgg ts => .cloneAgg (ts.map (Ty.norm P.assoc))
  | .guard s => .guard (s.norm P)
  | s => s
```

Examples: `isShim_pos_example`, `isShim_neg_example`, `norm_pos_example`, `norm_neg_example`, `assocNormal_examples`.

#### 1.2 Runtime references

`refs sig s` lists every key that running `s` may request, or store in a frame slot to be requested later through a pointer or a vtable: calls (`call`, and `invoke` of an explicit key), method calls (`mcall`), operand-position reification (`reifyKey` designates the reify shim of a `trackCaller` function), unsizing (every method of the trait at the type, plus the type's drop glue, which becomes the vtable's drop entry), drops on normal and cleanup paths, clones, and the clones and drops of an aggregate clone `cloneAgg`.

```lean
-- lean/MonoShim/Core.lean:180-182
def cloneKey : Ty → Key
  | .base n => .userClone n
  | t => .cloneShim t
```
```lean
-- lean/MonoShim/Core.lean:186-187
def reifyKey (sig : Sig) (f : Nat) (τs : List Ty) : Key :=
  if sig.tc f then .reifyShim f τs else .inst f τs
```
```lean
-- lean/MonoShim/Core.lean:190-191
def vtEntries (sig : Sig) (t : Ty) (tr : Nat) : List (Nat × Key) :=
  (sig.methods tr).map fun m => (m, .meth tr m t)
```
```lean
-- lean/MonoShim/Core.lean:197-214
def refs (sig : Sig) : Stmt → List Key
  | .skip => []
  | .seq a b => refs sig a ++ refs sig b
  | .emit _ => []
  | .panic => []
  | .call f τs => [.inst f τs]
  | .invoke k => [k]
  | .mcall tr m t => [.meth tr m t]
  | .drop t => [.dropGlue t]
  | .clone t => [cloneKey t]
  | .reify _ f τs => [reifyKey sig f τs]
  | .callPtr _ => []
  | .unsize _ t tr => (vtEntries sig t tr).map Prod.snd ++ [.dropGlue t]
  | .callDyn _ _ => []
  | .dropDyn _ => []
  | .onUnwind a b => refs sig a ++ refs sig b
  | .cloneAgg ts => ts.map cloneKey ++ ts.map Key.dropGlue
  | .guard s => refs sig s
```

Examples: `refs_pos_example`, `refs_neg_example`, `reifyKey_examples`, `cloneKey_examples`.

#### 1.3 One interpreter, two resolvers

Both semantics run the same fuel-indexed interpreter. `execS` executes one body against a call oracle; `runKey` looks a key up in a resolver, runs its body in a fresh frame, and answers nested calls with one less unit of fuel (fuel bounds call depth; `runKey` with fuel 0 returns `outOfFuel`). An undefined key gives `Res.link k`.

```lean
-- lean/MonoShim/Core.lean:220-223
inductive SlotVal where
  | fn : Key → SlotVal
  | vt : List (Nat × Key) → Key → SlotVal
  deriving DecidableEq, Repr
```
```lean
-- lean/MonoShim/Core.lean:225
abbrev Frame := List (Nat × SlotVal)
```
```lean
-- lean/MonoShim/Core.lean:228-231
structure St where
  evs : List Nat
  ctr : Nat
  deriving DecidableEq, Repr
```
```lean
-- lean/MonoShim/Core.lean:235-242
inductive Res where
  | ok : Res
  | unwind : Res
  | abort : Res
  | link : Key → Res
  | stuck : Res
  | outOfFuel : Res
  deriving DecidableEq, Repr
```
```lean
-- lean/MonoShim/Core.lean:245
abbrev Call := Key → St → Res × St
```
```lean
-- lean/MonoShim/Core.lean:248-254
def cleanupDrops (c : Call) : List Ty → St → Res × St
  | [], st => (.unwind, st)
  | t :: ts, st =>
    match c (.dropGlue t) st with
    | (.ok, st') => cleanupDrops c ts st'
    | (.unwind, st') => (.abort, st')
    | r => r
```
```lean
-- lean/MonoShim/Core.lean:258-264
def aggClone (c : Call) : List Ty → List Ty → St → Res × St
  | _, [], st => (.ok, st)
  | done, t :: ts, st =>
    match c (cloneKey t) st with
    | (.ok, st') => aggClone c (t :: done) ts st'
    | (.unwind, st') => cleanupDrops c done st'
    | r => r
```
```lean
-- lean/MonoShim/Core.lean:267-307
def execS (sig : Sig) (c : Call) : Stmt → Frame → St → Res × Frame × St
  | .skip, fr, st => (.ok, fr, st)
  | .seq a b, fr, st =>
    match execS sig c a fr st with
    | (.ok, fr', st') => execS sig c b fr' st'
    | r => r
  | .emit e, fr, st => (.ok, fr, { st with evs := st.evs ++ [e] })
  | .panic, fr, st => (.unwind, fr, st)
  | .call f τs, fr, st => ((c (.inst f τs) st).1, fr, (c (.inst f τs) st).2)
  | .invoke k, fr, st => ((c k st).1, fr, (c k st).2)
  | .mcall tr m t, fr, st => ((c (.meth tr m t) st).1, fr, (c (.meth tr m t) st).2)
  | .drop t, fr, st => ((c (.dropGlue t) st).1, fr, (c (.dropGlue t) st).2)
  | .clone t, fr, st => ((c (cloneKey t) st).1, fr, (c (cloneKey t) st).2)
  | .reify j f τs, fr, st => (.ok, (j, .fn (reifyKey sig f τs)) :: fr, st)
  | .callPtr j, fr, st =>
    match fr.lookup j with
    | some (.fn k) => ((c k st).1, fr, (c k st).2)
    | _ => (.stuck, fr, st)
  | .unsize j t tr, fr, st => (.ok, (j, .vt (vtEntries sig t tr) (.dropGlue t)) :: fr, st)
  | .callDyn j m, fr, st =>
    match fr.lookup j with
    | some (.vt es _) =>
      match es.lookup m with
      | some k => ((c k st).1, fr, (c k st).2)
      | none => (.stuck, fr, st)
    | _ => (.stuck, fr, st)
  | .dropDyn j, fr, st =>
    match fr.lookup j with
    | some (.vt _ d) => ((c d st).1, fr, (c d st).2)
    | _ => (.stuck, fr, st)
  | .onUnwind a b, fr, st =>
    match execS sig c a fr st with
    | (.unwind, fr', st') =>
      match execS sig c b fr' st' with
      | (.ok, fr'', st'') => (.unwind, fr'', st'')
      | (.unwind, fr'', st'') => (.abort, fr'', st'')
      | r => r
    | r => r
  | .cloneAgg ts, fr, st => ((aggClone c [] ts st).1, fr, (aggClone c [] ts st).2)
  | .guard s, fr, st =>
    if st.ctr = 0 then (.ok, fr, st) else execS sig c s fr { st with ctr := st.ctr - 1 }
```
```lean
-- lean/MonoShim/Core.lean:312-317
def runKey (sig : Sig) (R : Key → Option Stmt) : Nat → Key → St → Res × St
  | 0, _, st => (.outOfFuel, st)
  | n + 1, k, st =>
    match R k with
    | none => (.link k, st)
    | some b => ((execS sig (runKey sig R n) b [] st).1, (execS sig (runKey sig R n) b [] st).2.2)
```

Unfolded (prose): `guard s` tests the counter and, when it is nonzero, runs `s` with the counter decremented; `st.ctr - 1` is truncated natural-number subtraction, evaluated when `st.ctr ≠ 0`, so no truncation occurs. `onUnwind a c` runs `c` when `a` unwinds; if `c` completes normally, unwinding continues; if `c` unwinds, the outcome is `abort`.

**Source semantics `S`.** Instances instantiate the generic body by substitution followed by normalization; method and user `Drop`/`Clone` bodies are looked up and normalized; drop and clone behaviour of shim keys is computed from the type; requested keys are normalized at run time (`srcDef`).

```lean
-- lean/MonoShim/Pipeline.lean:12
def natLookup (l : List (Nat × Stmt)) (n : Nat) : Option Stmt := l.lookup n
```
```lean
-- lean/MonoShim/Pipeline.lean:15-16
def implLookup (P : Program) (tr m : Nat) (t : Ty) : Option Stmt :=
  (P.impls.find? (fun e => decide (e.tr = tr ∧ e.m = m ∧ e.ty = t))).map ImplEntry.body
```
```lean
-- lean/MonoShim/Pipeline.lean:25-30
def glueSrc (P : Program) : Ty → Option Stmt
  | .base n => some (if (natLookup P.dropImpls n).isSome then .invoke (.userDrop n) else .skip)
  | .box t => some (.drop t)
  | .pair a b => some (.seq (.onUnwind (.drop a) (.drop b)) (.drop b))
  | .fnPtr => some .skip
  | _ => none
```
```lean
-- lean/MonoShim/Pipeline.lean:35-38
def cloneSrc : Ty → Option Stmt
  | .pair a b => some (.cloneAgg [a, b])
  | .fnPtr => some .skip
  | _ => none
```
```lean
-- lean/MonoShim/Pipeline.lean:44-51
def srcDef0 (P : Program) : Key → Option Stmt
  | .inst f τs => (P.fns[f]?).map fun fd => (fd.body.subst τs).norm P
  | .meth tr m t => (implLookup P tr m t).map (Stmt.norm P)
  | .userDrop n => (natLookup P.dropImpls n).map (Stmt.norm P)
  | .userClone n => (natLookup P.cloneImpls n).map (Stmt.norm P)
  | .dropGlue t => glueSrc P t
  | .cloneShim t => cloneSrc t
  | .reifyShim f τs => (P.fns[f]?).map fun _ => .call f τs
```
```lean
-- lean/MonoShim/Pipeline.lean:55
def srcDef (P : Program) (k : Key) : Option Stmt := srcDef0 P (k.norm P)
```
```lean
-- lean/MonoShim/Pipeline.lean:58
def runS (P : Program) (n : Nat) (k : Key) (st : St) : Res × St := runKey P.sig (srcDef P) n k st
```

Examples: `glueSrc_pos_example`, `glueSrc_neg_example`, `glue_pair_unwind_drops_remaining_field_example`, `srcDef_pos_example`, `srcDef_neg_example`.

`derived (modeling bridge)` for `glueSrc`. The Rust Reference (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/destructors.md`, `destructors.operation`, L10–14) states the destructor of a value as "If `T: Drop`, calling `<T as core::ops::Drop>::drop`", then "The fields of a [struct] are dropped in declaration order." and "The fields of a [tuple] are dropped in order."; reverse order is the rule for variables and temporaries leaving a scope ("dropped in reverse order of declaration (for variables) or creation (for temporaries)", `destructors.scope.intro`, `src/destructors.md` L59). rustc's drop elaboration builds a two-half drop ladder; its documentation comment (`rust-lang/rust` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_mir_transform/src/elaborate_drop.rs` L897–912) reads, for three fields:

```text
/// Creates a full drop ladder, consisting of 2 connected half-drop-ladders
///
/// For example, with 3 fields, the drop ladder is
///
/// ```text
/// .d0:
///     ELAB(drop location.0 [target=.d1, unwind=.c1])
/// .d1:
///     ELAB(drop location.1 [target=.d2, unwind=.c2])
/// .d2:
///     ELAB(drop location.2 [target=`self.succ`, unwind=`self.unwind`])
/// .c1:
///     ELAB(drop location.1 [target=.c2])
/// .c2:
///     ELAB(drop location.2 [target=`self.unwind`])
/// ```
```

and the cleanup half-ladder is built with `vec![Unwind::InCleanup; fields.len() + 1]` (L952), so a panic in a cleanup drop terminates. The toy's two-field glue `seq (onUnwind (drop a) (drop b)) (drop b)` mirrors this: if dropping `a` unwinds, `b` is dropped on the unwind path and a panic there aborts (`glue_pair_unwind_drops_remaining_field_example`). A `base n` type has no fields, so its glue is the user `Drop::drop` or nothing.

`derived (modeling bridge)` for `srcDef0`. The collector monomorphizes the types and values of an instance's MIR with `instantiate_mir_and_normalize_erasing_regions` (`rust-lang/rust` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_monomorphize/src/collector.rs` L700–710, `fn monomorphize`). The toy instantiates by `Stmt.subst` and normalizes with the single-pass `Stmt.norm`; rustc's normalization is not modelled beyond this.

`derived (modeling bridge)` for `cloneSrc`: a tuple clone is the tuple expression of field clones, whose partially evaluated operands are dropped in reverse order of creation when an operand panics (Reference `destructors.scope.operands`, `src/destructors.md` L352–355). `box τ` has no clone behaviour in the toy (`cloneKey (box τ)` is the shim key `cloneShim (box τ)`, on which `cloneSrc` and `synthStd` are both `none`).

**Synthesizer and mono semantics `M`.**

```lean
-- lean/MonoShim/Pipeline.lean:64-66
def ladder : List Ty → Stmt
  | [] => .skip
  | t :: ts => .seq (.clone t) (.onUnwind (ladder ts) (.drop t))
```
```lean
-- lean/MonoShim/Pipeline.lean:70-75
def synthStd (P : Program) : Key → Option Stmt
  | .dropGlue t => glueSrc P t
  | .cloneShim (.pair a b) => some (ladder [a, b])
  | .cloneShim .fnPtr => some .skip
  | .reifyShim f τs => (P.fns[f]?).map fun _ => .call f τs
  | _ => none
```
```lean
-- lean/MonoShim/Pipeline.lean:81-83
structure MonoCfg where
  E : Stmt → List Key
  synth : Key → Option Stmt
```
```lean
-- lean/MonoShim/Pipeline.lean:86
def stdCfg (P : Program) : MonoCfg := ⟨refs P.sig, synthStd P⟩
```
```lean
-- lean/MonoShim/Pipeline.lean:90-91
def bodyM (P : Program) (cfg : MonoCfg) (k : Key) : Option Stmt :=
  if k.isShim then cfg.synth k else srcDef0 P k
```
```lean
-- lean/MonoShim/Pipeline.lean:95-98
def edgesM (P : Program) (cfg : MonoCfg) (k : Key) : List Key :=
  match bodyM P cfg k with
  | some b => (cfg.E b).map (Key.norm P)
  | none => []
```
```lean
-- lean/MonoShim/Pipeline.lean:101-102
def tableM (P : Program) (cfg : MonoCfg) (T : List Key) (k : Key) : Option Stmt :=
  if k ∈ T then bodyM P cfg k else none
```
```lean
-- lean/MonoShim/Pipeline.lean:106-107
def runM (P : Program) (cfg : MonoCfg) (T : List Key) (n : Nat) (k : Key) (st : St) : Res × St :=
  runKey P.sig (tableM P cfg T) n k st
```

Examples: `synthStd_pos_example`, `synthStd_neg_example`, `ladder_shape_example`.

#### 1.4 Collection and closed targets

```lean
-- lean/MonoShim/Pipeline.lean:110-112
inductive Reach (edges : Key → List Key) (roots : List Key) : Key → Prop
  | root {k : Key} : k ∈ roots → Reach edges roots k
  | step {k k' : Key} : Reach edges roots k → k' ∈ edges k → Reach edges roots k'
```
```lean
-- lean/MonoShim/Pipeline.lean:116-117
def Closed (sig : Sig) (tbl : Key → Option Stmt) (T : List Key) : Prop :=
  ∀ k ∈ T, (tbl k).isSome ∧ ∀ b ∈ (tbl k).toList, ∀ k' ∈ refs sig b, k' ∈ T
```
```lean
-- lean/MonoShim/Pipeline.lean:125-131
def collectGo (edges : Key → List Key) (sched : List Key → List Key → List Key) :
    Nat → List Key → List Key → Option (List Key)
  | 0, _, _ => none
  | _ + 1, [], done => some done
  | n + 1, k :: work, done =>
    if k ∈ done then collectGo edges sched n work done
    else collectGo edges sched n (sched work (edges k)) (k :: done)
```
```lean
-- lean/MonoShim/Pipeline.lean:133-135
def collect (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (roots : List Key) (fuel : Nat) : Option (List Key) :=
  collectGo edges sched fuel roots []
```
```lean
-- lean/MonoShim/Pipeline.lean:137
def fifo (work new : List Key) : List Key := work ++ new
```
```lean
-- lean/MonoShim/Pipeline.lean:138
def lifo (work new : List Key) : List Key := new ++ work
```
```lean
-- lean/MonoShim/Pipeline.lean:141-142
def SchedOK (sched : List Key → List Key → List Key) : Prop :=
  ∀ w n x, x ∈ sched w n ↔ x ∈ w ∨ x ∈ n
```

Examples: `reach_pos_example`, `reach_neg_example`, `schedOK_pos_example`, `schedOK_neg_example`, `edgesIn_examples`, `rootsIn_examples`, `closed_examples`.

#### 1.5 Hypotheses as separate properties

```lean
-- lean/MonoShim/Pipeline.lean:147-148
def CoversRefs (sig : Sig) (E : Stmt → List Key) : Prop :=
  ∀ b k, k ∈ refs sig b → k ∈ E b
```
```lean
-- lean/MonoShim/Pipeline.lean:152-155
def BodyEquiv (sig : Sig) (b b' : Stmt) : Prop :=
  ∀ (c : Call) (st : St),
    ((execS sig c b [] st).1, (execS sig c b [] st).2.2) =
    ((execS sig c b' [] st).1, (execS sig c b' [] st).2.2)
```
```lean
-- lean/MonoShim/Pipeline.lean:158-161
def OptEquiv (sig : Sig) : Option Stmt → Option Stmt → Prop
  | none, none => True
  | some b, some b' => BodyEquiv sig b b'
  | _, _ => False
```
```lean
-- lean/MonoShim/Pipeline.lean:165-166
def SynthAgrees (P : Program) (cfg : MonoCfg) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = true → OptEquiv P.sig (cfg.synth k) (srcDef0 P k)
```
```lean
-- lean/MonoShim/Pipeline.lean:169-170
def CanonicalKeys (P : Program) (T : List Key) : Prop :=
  ∀ k ∈ T, k.norm P = k
```
```lean
-- lean/MonoShim/Pipeline.lean:177-178
def CanonicalRefs (P : Program) (cfg : MonoCfg) (T : List Key) : Prop :=
  ∀ k ∈ T, ∀ b ∈ (bodyM P cfg k).toList, ∀ k' ∈ refs P.sig b, k'.norm P = k'
```
```lean
-- lean/MonoShim/Pipeline.lean:184-185
def InstDefined (P : Program) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = false → (srcDef0 P k).isSome
```
```lean
-- lean/MonoShim/Pipeline.lean:191-192
def SynthTotal (cfg : MonoCfg) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = true → (cfg.synth k).isSome
```
```lean
-- lean/MonoShim/Pipeline.lean:198
def RootsIn (roots T : List Key) : Prop := ∀ k ∈ roots, k ∈ T
```
```lean
-- lean/MonoShim/Pipeline.lean:204
def EdgesIn (edges : Key → List Key) (T : List Key) : Prop := ∀ k ∈ T, ∀ k' ∈ edges k, k' ∈ T
```
```lean
-- lean/MonoShim/Pipeline.lean:213-214
def assocNormal (P : Program) : Bool :=
  P.assoc.all fun e => decide (e.2.2.norm P.assoc = e.2.2)
```
```lean
-- lean/MonoShim/Pipeline.lean:217-218
theorem ty_norm_idem_of_assocNormal (P : Program) (h : assocNormal P = true) :
    ∀ t : Ty, (t.norm P.assoc).norm P.assoc = t.norm P.assoc := by
```

Examples: `coversRefs_pos_example`, `coversRefs_neg_example`, `bodyEquiv_pos_example`, `bodyEquiv_neg_example`, `synthAgrees_pos_example`, `synthAgrees_neg_example`, `canonical_pos_example`, `canonical_neg_example`, `instDefined_examples`, `synthTotal_examples`, `assocNormal_examples`.

#### 1.6 Specifications (for R5–R6)

```lean
-- lean/MonoShim/SourceOnly.lean:10
abbrev Spec := St → Res × St → Prop
```
```lean
-- lean/MonoShim/SourceOnly.lean:13
def SatOut (Q : Spec) (st : St) (o : Res × St) : Prop := o.1 = .outOfFuel ∨ Q st o
```
```lean
-- lean/MonoShim/SourceOnly.lean:16-17
def MeetsAt (sig : Sig) (R : Key → Option Stmt) (Q : Spec) (k : Key) : Prop :=
  ∀ n st, SatOut Q st (runKey sig R n k st)
```
```lean
-- lean/MonoShim/SourceOnly.lean:21-23
def VerifiedBody (sig : Sig) (A : Key → Spec) (b : Stmt) (Q : Spec) : Prop :=
  ∀ c : Call, (∀ k ∈ refs sig b, ∀ st, SatOut (A k) st (c k st)) →
    ∀ st, SatOut Q st ((execS sig c b [] st).1, (execS sig c b [] st).2.2)
```
```lean
-- lean/MonoShim/SourceOnly.lean:26-30
def Key.isImpl : Key → Bool
  | .meth _ _ _ => true
  | .userDrop _ => true
  | .userClone _ => true
  | _ => false
```
```lean
-- lean/MonoShim/SourceOnly.lean:37-39
def GenericVerified (P : Program) (Q : Key → Spec) : Prop :=
  ∀ f fd τs, P.fns[f]? = some fd →
    VerifiedBody P.sig Q ((fd.body.subst τs).norm P) (Q (.inst f τs))
```
```lean
-- lean/MonoShim/SourceOnly.lean:43-44
def ImplsConform (P : Program) (Q : Key → Spec) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isImpl = true → ∀ b ∈ (srcDef0 P k).toList, VerifiedBody P.sig Q b (Q k)
```
```lean
-- lean/MonoShim/SourceOnly.lean:48-49
def SynthVerified (P : Program) (cfg : MonoCfg) (Q : Key → Spec) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = true → ∀ b ∈ (cfg.synth k).toList, VerifiedBody P.sig Q b (Q k)
```
```lean
-- lean/MonoShim/SourceOnlyExamples.lean:185-186
noncomputable def srcVerdict (P : Program) (Q : Key → Spec) : Bool :=
  @decide (MeetsAt P.sig (srcDef P) (Q (.inst 0 [])) (.inst 0 [])) (Classical.propDecidable _)
```

Unfolded (prose): `GenericVerified P Q` asks, for every function and every concrete type-argument list `τs` (of any length, including lists naming types without impls), that the instantiated and normalized body verify against `Q (.inst f τs)` assuming `Q` on every key it may request; for method keys `Q` plays the role of the trait-method spec, indexed by the concrete receiver type. Partial correctness: `SatOut` accepts every out-of-fuel outcome. `MeetsAt sig R Q k` is a semantic property of the resolver `R`; `srcVerdict` and the verdicts `V` of R5 are Boolean functions of `(Program, Key → Spec)`. The verdicts `V` range over all such functions, computable or not. `srcVerdict` is noncomputable: it is the classical Boolean indicator (via `Classical.propDecidable`) of a proposition that quantifies over every fuel and initial state, not a decision procedure.

Examples: `verifiedBody_pos_example`, `verifiedBody_neg_example`, `specs_pos_example`, `specs_neg_example`, `genericVerified_neg_example`, `meetsAt_examples`.

#### 1.7 Per-unit linking, precomputed synthesis, rank check

```lean
-- lean/MonoShim/Worklist.lean:142
def preCfg (E : Stmt → List Key) (pre : List (Key × Stmt)) : MonoCfg := ⟨E, fun k => pre.lookup k⟩
```
```lean
-- lean/MonoShim/Worklist.lean:183-186
def linkUnits (P : Program) (E : Stmt → List Key) :
    List (List Key × (Key → Option Stmt)) → Key → Option Stmt
  | [], _ => none
  | (ks, sy) :: us, k => if k ∈ ks then bodyM P ⟨E, sy⟩ k else linkUnits P E us k
```
```lean
-- lean/MonoShim/Worklist.lean:190-192
def DeterministicUnits (synth : Key → Option Stmt) (units : List (List Key × (Key → Option Stmt))) :
    Prop :=
  ∀ u ∈ units, ∀ k ∈ u.1, k.isShim = true → u.2 k = synth k
```
```lean
-- lean/MonoShim/Worklist.lean:195-196
def UnitsCover (units : List (List Key × (Key → Option Stmt))) (T : List Key) : Prop :=
  ∀ k, k ∈ T ↔ ∃ u ∈ units, k ∈ u.1
```
```lean
-- lean/MonoShim/Termination.lean:15-19
def Ty.size : Ty → Nat
  | .box t => t.size + 1
  | .pair a b => a.size + b.size + 1
  | .proj _ t => t.size + 1
  | _ => 1
```
```lean
-- lean/MonoShim/Termination.lean:10-12
def boxIter : Nat → Ty → Ty
  | 0, t => t
  | k + 1, t => .box (boxIter k t)
```
```lean
-- lean/MonoShim/Termination.lean:122-127
def Ty.hasParam : Ty → Bool
  | .param _ => true
  | .box t => t.hasParam
  | .pair a b => a.hasParam || b.hasParam
  | .proj _ t => t.hasParam
  | _ => false
```
```lean
-- lean/MonoShim/Termination.lean:131-133
def Ty.grows : Ty → Bool
  | .param _ => false
  | t => t.hasParam
```
```lean
-- lean/MonoShim/Termination.lean:137-145
def instRefs : Stmt → List (Nat × List Ty)
  | .seq a b => instRefs a ++ instRefs b
  | .onUnwind a b => instRefs a ++ instRefs b
  | .guard s => instRefs s
  | .call f τs => [(f, τs)]
  | .reify _ f τs => [(f, τs)]
  | .invoke (.inst f τs) => [(f, τs)]
  | .invoke (.reifyShim f τs) => [(f, τs)]
  | _ => []
```
```lean
-- lean/MonoShim/Termination.lean:149-154
def rankCheck (P : Program) (rank : Nat → Nat) : Bool :=
  (List.range P.fns.length).all fun f =>
    match P.fns[f]? with
    | none => true
    | some fd => (instRefs fd.body).all fun r =>
        if r.2.any Ty.grows then decide (rank r.1 < rank f) else decide (rank r.1 ≤ rank f)
```

`rankCheck P rank` checks a supplied rank certificate `rank : Nat → Nat` against the function bodies `P.fns` (through `instRefs`); it does not inspect `P.impls`, `P.dropImpls`, `P.cloneImpls` or `P.assoc`. In the toy those are literal, non-generic tables (§1.1), so the bodies they contribute are fixed statements. Examples: `deterministicUnits_examples`, `rankCheck_examples`, `grows_examples`.

## Findings

Each card below gives the tier, the Lean statement (verbatim quote with its `file:line` range; definitions are quoted under Applicability, and auxiliary declarations under Evidence), the plain claim, the hypothesis ledger, the depth, the non-vacuity witness, the positive control where one applies, prior art and the design question. Each card's non-claims are under **Boundaries**. The theorems of every card have evidential basis `execution (Lean kernel check)`; claims about rustc or the Rust Reference are separate and appear under Modeling bridges at the end of this section, with basis `derived (modeling bridge)`.

Common hypothesis names: (HR) roots in `T`; (HE) `T` closed under the collector's edges; (H1) the edge function covers every runtime reference; (H2) synthesizer agreement with matched definedness; (H2t) synthesizer totality; (H3a) canonical target keys; (H3b) canonical referenced keys; (H0) source defines every non-shim key. In a hypothesis ledger, "tight" means: a proved counterexample in which every other hypothesis holds and the conclusion fails; the class of the witness is given in parentheses.

### R1. Closure of an edge-closed target

```lean
-- lean/MonoShim/Adequacy.lean:215-219
theorem closed_of_edgesIn_covering_total_canonicalRefs_instDefined
    (P : Program) (cfg : MonoCfg) (T : List Key)
    (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E) (h2t : SynthTotal cfg T)
    (h3b : CanonicalRefs P cfg T) (h0 : InstDefined P T) :
    Closed P.sig (tableM P cfg T) T := by
```

- **Plain claim.** In the toy pipeline, for every program `P`, configuration `cfg` and key list `T`: if `T` is closed under the collector's edge function `edgesM P cfg` (HE), the edge function `cfg.E` covers every runtime reference of every body (H1: `call`, `invoke`, `mcall`, operand-position `reify`, every trait method at an unsized type plus that type's drop glue, drops on normal and cleanup paths, clones, and the clones and drops of `cloneAgg`), the synthesizer is defined on every shim key of `T` (H2t), every key referenced by a body the compiler emits for a key of `T` is in normal form (H3b), and the source defines every non-shim key of `T` (H0), then the table restricted to `T` is closed: every key of `T` has a body and every runtime reference of that body lies in `T`.
- **Tier.** T1: the closure obligation is the documented design of rustc's mono-item collector ("Mono items and the uses between them form a directed graph, where the mono items are the nodes and uses form the edges.", `collector.rs` L46–47), made precise for a toy with synthesized shims; no mechanized version was found.
- **Hypothesis ledger.**
  - (HE) `hE` — every emitted edge must land in `T`. Tight: `target_not_edge_closed_breaks_closure_and_adequacy` (a 2-function program whose target stops at the root).
  - (H1) `h1` — a missed reference kind leaves its target outside `T`. Tight: `vtable_edges_missing_break_closure` (a 1-function program with one impl; `SynthTotal` holds non-vacuously on its shim key `dropGlue (base 2)`); also `cleanup_edges_missing_break_closure`, `operand_edges_missing_break_closure`, `reify_shim_edges_missing_break_closure` (R3), each asserting every other hypothesis of R1, including (H2t) and (H0).
  - (H2t) `h2t` — a shim key without a synthesized body is a hole. Tight: `partial_synth_breaks_closure` (a 2-function program with one destructor; the synthesizer returns `none` everywhere).
  - (H3b) `h3b` — the collector records normalized keys; a referenced key that is not normal is missed. Tight: `noncanonical_refs_break_closure` (a 3-function program whose associated-type table is chained, so one normalization pass is not idempotent).
  - (H0) `h0` — a call to an undefined function is a hole. Tight: `undefined_instance_breaks_closure` (a 1-function program calling an undefined function).
  - Derivable relative: (H2t) follows from (H2) plus source-definedness of every shim key of `T` (`synthTotal_of_synthAgrees`); it is stated separately because closure does not use the equivalence part of (H2). For the standard configuration, (H3b) follows from `assocNormal` and (H3a) (`canonicalRefs_stdCfg_of_assocNormal`, R12).
- **Depth.** shallow.
- **Non-vacuity.** `Pall_all_hypotheses_hold`: `Pall` with the standard pipeline; its source uses `unsize`, `callDyn`, `mcall`, `dropDyn`, `reify` of a `trackCaller` function, `callPtr`, `clone` of a function pointer, a pair clone whose second field panics (ladder cleanup), and an `onUnwind` cleanup drop; the synthesized drop glue uses `invoke`.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R1).
- **Prior art.** rustc `compiler/rustc_monomorphize/src/collector.rs` module documentation at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (L1–195; quotes under R3). Tolmach and Oliva, "From ML to Ada: Strongly-typed language interoperability via source translation", Journal of Functional Programming 8(4):367–412, 1998, doi:10.1017/S0956796898003086 (whole-program monomorphization of ML). Weeks, "Whole-program compilation in MLton", Proc. 2006 ACM Workshop on ML, p. 1, doi:10.1145/1159876.1159877 (a one-page invited-talk abstract). Wu, Wang, Yu, Meng, "RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust", arXiv:2602.07455v1 (2026; submitted to Rust Verify 2026 as a workshop-presentation proposal describing ongoing work on Rustlight, a sequential subset of Rust whose main unsupported features, as the preprint lists them, include concurrency, polymorphism, traits and higher-order functions): its verified frontend includes drop elaboration and "generates drop glue functions for types that require destructors" (a verified compiler for a subset without polymorphism or traits, not a collector-closure theorem).
- **Design question.** Which reference kinds must a collector follow, and what must a synthesizer supply, for a whole-program verification target to have no undefined symbols?

Basis: execution (Lean kernel check)

### R2. Adequacy: under (H1), (H2), (H3a) and (H3b), an edge-closed target containing the roots behaves like the source

```lean
-- lean/MonoShim/Adequacy.lean:276-280
theorem runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical
    (P : Program) (cfg : MonoCfg) (roots T : List Key)
    (hR : RootsIn roots T) (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E)
    (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T) (h3b : CanonicalRefs P cfg T) :
    ∀ r ∈ roots, ∀ (n : Nat) (st : St), runM P cfg T n r st = runS P n r st :=
```

- **Plain claim.** For every program, configuration, root list and key list `T`: if every root is in `T` (HR), `T` is closed under the collector's edge function (HE), the edge function covers every runtime reference (H1), on every shim key of `T` the synthesized body is defined exactly when the source construct is and, when both are defined, is behaviourally equivalent to it under every call oracle (H2), every key of `T` is in normal form (H3a), and every key referenced by a body the compiler emits for a key of `T` is in normal form (H3b), then for every root, every fuel and every initial state, the mono semantics restricted to `T` (`runM`) yields the same outcome and final state as the source semantics (`runS`); both are runs of the shared interpreter `runKey`.
- **Tier.** T1: re-derives, for a toy with synthesized shims, the shape of the monomorphisation correctness theorem of Featherweight Generic Go (Griesemer et al. 2020, Theorem 5.4, a bisimulation proved on paper for a different calculus).
- **Hypothesis ledger.**
  - (HR) `hR` — a root outside `T` is a link error. Tight: `root_outside_target_breaks_adequacy` (a 2-function program and the empty target).
  - (HE) `hE`. Tight: `target_not_edge_closed_breaks_closure_and_adequacy` (a 2-function program whose target stops at the root).
  - (H1) `h1`. Tight: `cleanup_edges_missing_break_closure` (a 2-function program whose one drop is on a cleanup path); also the other three R3 witnesses.
  - (H2) `h2` — the mono run executes synthesized bodies. Tight: `synth_disagreement_breaks_adequacy` (reverse-declaration-order glue for a 2-field pair).
  - (H3a) `h3a` — the source normalizes a requested key, the table is keyed literally. Tight: `noncanonical_root_breaks_adequacy` (a program without functions, one associated type, and a root drop-glue key over an unnormalized projection).
  - (H3b) `h3b`. Tight: `noncanonical_refs_break_closure` (a 3-function program with a chained associated-type table).
  - Each tightness witness asserts `¬ (∀ r ∈ roots, ∀ n st, runM … = runS …)` explicitly, together with the concrete differing runs.
- **Depth.** shallow (induction on fuel; the one non-obvious invariant is that every key stored in a frame slot lies in `T`, `execS_congr`).
- **Non-vacuity.** `Pall_all_hypotheses_hold`.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R2).
- **Prior art.** Griesemer, Hu, Kokke, Lange, Taylor, Toninho, Wadler, Yoshida, "Featherweight Go", Proc. ACM Program. Lang. 4 (OOPSLA), pp. 1–29, 2020, doi:10.1145/3428217 (arXiv:2005.11710v4), Theorem 5.4 (Bisimulation) for the FGG-to-FG monomorphisation. Ellis, Zhu, Yoshida, Song, "Generic Go to Go: Dictionary-Passing, Monomorphisation, and Hybrid", Proc. ACM Program. Lang. 6 (OOPSLA2), pp. 1207–1235, 2022, doi:10.1145/3563331: formalizes and compares dictionary-passing, monomorphisation and hybrid translations; its main proved behavioural-equivalence result is for the dictionary-passing translation.
- **Design question.** Under which conditions may a verifier reason about the collected monomorphic program instead of the generic source, or vice versa?

Basis: execution (Lean kernel check)

### R3. Omitting any one of four edge kinds can break closure

```lean
-- lean/MonoShim/MissingEdges.lean:74-84
theorem cleanup_edges_missing_break_closure :
    ¬ CoversRefs P2a.sig cfg2a.E ∧
    collect (edgesM P2a cfg2a) fifo [.inst 0 []] 10 = some T2a ∧
    RootsIn [.inst 0 []] T2a ∧ EdgesIn (edgesM P2a cfg2a) T2a ∧ SynthAgrees P2a cfg2a T2a ∧
    SynthTotal cfg2a T2a ∧ InstDefined P2a T2a ∧
    CanonicalKeys P2a T2a ∧ CanonicalRefs P2a cfg2a T2a ∧
    ¬ Closed P2a.sig (tableM P2a cfg2a T2a) T2a ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2a cfg2a T2a n r st = runS P2a n r st) ∧
    runM P2a cfg2a T2a 3 (.inst 0 []) st0 = (.link (.dropGlue (.base 1)), st0) ∧
    runS P2a 3 (.inst 0 []) st0 = (.unwind, ⟨[7], 0⟩) := by
```
```lean
-- lean/MonoShim/MissingEdges.lean:108-118
theorem vtable_edges_missing_break_closure :
    ¬ CoversRefs P2b.sig cfg2b.E ∧
    collect (edgesM P2b cfg2b) fifo [.inst 0 []] 10 = some T2b ∧
    RootsIn [.inst 0 []] T2b ∧ EdgesIn (edgesM P2b cfg2b) T2b ∧ SynthAgrees P2b cfg2b T2b ∧
    SynthTotal cfg2b T2b ∧ InstDefined P2b T2b ∧
    CanonicalKeys P2b T2b ∧ CanonicalRefs P2b cfg2b T2b ∧
    ¬ Closed P2b.sig (tableM P2b cfg2b T2b) T2b ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2b cfg2b T2b n r st = runS P2b n r st) ∧
    runM P2b cfg2b T2b 3 (.inst 0 []) st0 = (.link (.meth 0 0 (.base 2)), st0) ∧
    runS P2b 3 (.inst 0 []) st0 = (.ok, ⟨[5], 0⟩) := by
```
```lean
-- lean/MonoShim/MissingEdges.lean:140-150
theorem operand_edges_missing_break_closure :
    ¬ CoversRefs P2c.sig cfg2c.E ∧
    collect (edgesM P2c cfg2c) fifo [.inst 0 []] 10 = some T2c ∧
    RootsIn [.inst 0 []] T2c ∧ EdgesIn (edgesM P2c cfg2c) T2c ∧ SynthAgrees P2c cfg2c T2c ∧
    SynthTotal cfg2c T2c ∧ InstDefined P2c T2c ∧
    CanonicalKeys P2c T2c ∧ CanonicalRefs P2c cfg2c T2c ∧
    ¬ Closed P2c.sig (tableM P2c cfg2c T2c) T2c ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2c cfg2c T2c n r st = runS P2c n r st) ∧
    runM P2c cfg2c T2c 3 (.inst 0 []) st0 = (.link (.inst 1 []), st0) ∧
    runS P2c 3 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) := by
```
```lean
-- lean/MonoShim/MissingEdges.lean:172-182
theorem reify_shim_edges_missing_break_closure :
    ¬ CoversRefs P2d.sig cfg2d.E ∧
    collect (edgesM P2d cfg2d) fifo [.inst 0 []] 10 = some T2d ∧
    RootsIn [.inst 0 []] T2d ∧ EdgesIn (edgesM P2d cfg2d) T2d ∧ SynthAgrees P2d cfg2d T2d ∧
    SynthTotal cfg2d T2d ∧ InstDefined P2d T2d ∧
    CanonicalKeys P2d T2d ∧ CanonicalRefs P2d cfg2d T2d ∧
    ¬ Closed P2d.sig (tableM P2d cfg2d T2d) T2d ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2d cfg2d T2d n r st = runS P2d n r st) ∧
    runM P2d cfg2d T2d 3 (.inst 0 []) st0 = (.link (.reifyShim 1 []), st0) ∧
    runS P2d 3 (.inst 0 []) st0 = (.ok, ⟨[4], 0⟩) := by
```

- **Plain claim.** For each of four collector edge functions that omit one runtime reference kind — (a) drops on cleanup paths (`refsNoCleanup`), (b) the method entries of a vtable created by unsizing (`refsNoVtable`), (c) functions reified in operand position (`refsNoOperand`), (d) the reify shim a `trackCaller` function needs when reified (`refsNoReifyShim`) — there is a concrete program on which every other hypothesis of R1 and of R2 holds (roots in `T`, edge-closure, synthesizer agreement and totality, source definedness, canonical keys and references), the collected target is not closed, the adequacy conclusion fails, and the run of the collected program from the root ends in `Res.link` of a specific missing key, while the source run completes or unwinds normally.
- **Tier.** T1.
- **Hypothesis ledger.** None (concrete instances).
- **Depth.** definitional (kernel evaluation).
- **Positive control.** `full_edges_close_missing_edge_examples`: with the full edge function each example collects a target that contains the missing key and is closed.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R3).
- **Prior art (documentation, rustc collector at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`).** (c): "whenever we encounter a function or method in operand position, we treat it as a use of the current mono item. Calls are just a special case of that." (L109–111). (b): "Since the resulting wide-pointer contains a reference to a vtable, we need to instantiate all dyn-compatible methods of the trait, as we need to store pointers to these functions even if they never get called anywhere." (L122–124). Drop glue: "Drop glue mono items are introduced by MIR drop-statements." (L114). (d): `compiler/rustc_middle/src/ty/instance.rs` L114–118 (`ShimKind::Reify`; `#[track_caller]` functions "must have their implicit caller location argument populated for a call"); the Rust Reference (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/attributes/codegen.md`, `attributes.codegen.track_caller.decay`, L1047): "coercing a function with `#[track_caller]` to a function pointer creates a shim". VanHattum, Schwartz-Narbonne, Chong, Sampson, "Verifying Dynamic Trait Objects in Rust", ICSE-SEIP 2022, pp. 321–330, doi:10.1145/3510457.3513031 (vtables and trait objects in a Rust verifier). `derived (modeling bridge)`: the toy's `reifyKey` mirrors the reify shim with a distinct `reifyShim` key.
- **Design question.** Which edge kinds must a whole-program collector feeding a verifier follow?

Basis: execution (Lean kernel check)

### R4. The clone ladder is exact

```lean
-- lean/MonoShim/Ladder.lean:47-48
theorem ladder_exec_eq_cloneAgg (sig : Sig) (c : Call) (fs : List Ty) (fr : Frame) (st : St) :
    execS sig c (ladder fs) fr st = execS sig c (.cloneAgg fs) fr st := by
```

- **Plain claim.** For every call oracle, every list of field types, every frame and every state, executing the explicit ladder `ladder fs` (clone field `i` left to right; if that unwinds, drop the clones of fields `i-1, …, 0`; a panic in such a drop aborts) gives exactly the same outcome, frame and state as the source aggregate clone `cloneAgg fs` (clone operands left to right; on unwinding drop the evaluated operands in reverse order of creation; a panic in cleanup aborts).
- **Tier.** T1.
- **Hypothesis ledger.** None.
- **Depth.** shallow (induction on the field list with an accumulator of completed clones, `ladder_post`).
- **Non-vacuity.** `ladder_cloneAgg_unwind_and_abort_examples` exercises the unwinding branch (event trace `[1, 2]`) and the abort branch on two fields; `ladder_cloneAgg_three_fields_reverse_cleanup_example` shows the reverse cleanup order on three statement-level fields (trace `[1, 2, 20, 10]`).
- **Counterexamples.** `ladderNoCleanup_ne_cloneAgg`: on `P3`, a ladder without cleanup skips the destructor event (a leak, observably different). `ladder_drop_refs_missing_break_closure`: on `P3`, with the cleanup-blind edge function `refsNoCleanup` (under which the clone shim's references omit the field type's drop glue), the collected target is not closed and the run calls the missing glue.
- **Consequence.** `synthStd_optEquiv`, `synthStd_agrees`: the standard synthesizer satisfies (H2) for every target.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R4).
- **Prior art.** `compiler/rustc_mir_transform/src/shim.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `clone_fields` (L658–705, comments L673–678: "Block 2*i attempts to clone the field. If successful it branches to 2*i + 2 (the next clone block). If unsuccessful it branches to the previous unwind block, which is initially the `unwind` argument passed to this function." and "Block 2*i + 1 is the unwind block for this iteration. It drops the cloned value created by block 2*i."); the drop in the unwind block carries `unwind: UnwindAction::Terminate(UnwindTerminateReason::InCleanup)` (L694); `build_clone_shim` (L508–531) uses `tuple_like_shim` for tuples. Rust Reference `destructors.scope.intro`, `destructors.scope.operands` (commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/destructors.md` L58–59, L352–355).
- **Design question.** What must a verified clone-shim synthesizer establish, and against which source rule?

Basis: execution (Lean kernel check)

### R5. No verdict determined by the program and its specs alone is correct for every synthesizer; the source-semantics verdict is correct for every configuration and target satisfying R2's hypotheses with root `main`

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:166-171
theorem no_source_only_verdict_correct_for_every_synthesizer (V : Program → (Key → Spec) → Bool) :
    GenericVerified P4a Q4a ∧ ImplsConform P4a Q4a T4a ∧
    ∃ cfg : MonoCfg, (cfg = stdCfg P4a ∨ cfg = cfgRev P4a) ∧
      Closed P4a.sig (tableM P4a cfg T4a) T4a ∧
      ¬ (V P4a Q4a = true ↔
          MeetsAt P4a.sig (tableM P4a cfg T4a) (Q4a (.inst 0 [])) (.inst 0 [])) := by
```
```lean
-- lean/MonoShim/SourceOnlyExamples.lean:140-145
theorem source_defs_verified_yet_program_violates_spec_under_reverse_glue :
    Closed P4a.sig (tableM P4a (cfgRev P4a) T4a) T4a ∧ GenericVerified P4a Q4a ∧
    ImplsConform P4a Q4a T4a ∧ ¬ SynthVerified P4a (cfgRev P4a) Q4a T4a ∧
    runM P4a (cfgRev P4a) T4a 4 (.inst 0 []) st0 = (.ok, ⟨[20, 10], 0⟩) ∧
    ¬ MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) ∧
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a k) k) := by
```

- **Plain claim.** For every Boolean verdict `V` that is a function of a program and its spec assignment (any function `Program → (Key → Spec) → Bool`, computable or not): in program `P4a` (a guard type whose destructor emits 10, a data type whose destructor emits 20, `main` drops a pair of them) with the specs `Q4a` ("release before free"), every generic body is verified (`GenericVerified`) and every user impl in `T4a` conforms (`ImplsConform`), and there is a configuration — the standard one or the reverse-declaration-order glue variant `cfgRev`, which differ in the synthesized glue of the pair — whose table restricted to `T4a` is closed and for which `V P4a Q4a = true` disagrees with whether `main` meets its spec in that table. Concretely, under `cfgRev` the target is closed, the user side is verified, and `main` emits `[20, 10]` and violates its spec, while under the standard configuration every key meets its spec (`P4a_std_meets_specs`).
- **Kind.** impossibility (relative to the class of all synthesizers, including ones that violate (H2)).
- **Tier.** T1 (folklore: a verifier of source definitions must account for compiler-generated glue; no mechanized statement found).
- **Hypothesis ledger.** None (the theorem quantifies over every verdict `V`; the program is concrete).
- **Depth.** shallow (case split on `V P4a Q4a`; the facts are R6 instances and kernel evaluation).
- **Positive control (escape hatch).** `srcVerdict_correct_of_adequacy`: for every program, spec assignment, configuration and target such that R2's hypotheses hold with roots `[main]` — (HR), (HE), (H1), (H2) (synthesizer agreement with the source rules `glueSrc`/`cloneSrc`), (H3a) and (H3b) — the verdict `srcVerdict` ("`main` meets its spec in `runS`"), a function of the program and specs alone, is true exactly when `main` meets its spec in the table restricted to the target. `srcVerdict` is noncomputable (the classical indicator of that proposition, via `Classical.propDecidable`), not a decision procedure. `srcVerdict_correct_example` shows these hypotheses hold for `P4a` with the standard configuration. The reverse-glue configuration violates (H2) (`synth_disagreement_breaks_adequacy`). `srcVerdict_correct_of_adequacy` takes R2's hypothesis bundle as a sufficient condition; no necessity is claimed for any single hypothesis of that bundle in this corollary (in particular, none is claimed for (H3a) when the root is fixed to `.inst 0 []`).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R5).
- **Prior art.** Rust Reference `destructors.operation` (commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/destructors.md` L12–14): "The fields of a [struct] are dropped in declaration order." (L12); "The fields of a [tuple] are dropped in order." (L14). RustCompCert (arXiv:2602.07455v1, a workshop-presentation proposal describing ongoing work on a sequential subset of Rust without polymorphism or traits), which verifies drop elaboration and generated drop glue inside a compiler, is an instance of the escape hatch (the synthesizer is verified against the source semantics).
- **Design question.** Must a whole-program verification target contain the synthesized shims, or must the synthesizer be verified against a stated drop/clone semantics?

Basis: execution (Lean kernel check)

### R6. Spec transfer to a closed target

```lean
-- lean/MonoShim/SourceOnly.lean:53-56
theorem closed_target_meets_specs_of_generic_impl_synth_verified (P : Program) (cfg : MonoCfg)
    (T : List Key) (Q : Key → Spec) (hC : Closed P.sig (tableM P cfg T) T)
    (hG : GenericVerified P Q) (hI : ImplsConform P Q T) (hS : SynthVerified P cfg Q T) :
    ∀ k ∈ T, MeetsAt P.sig (tableM P cfg T) (Q k) k := by
```
```lean
-- lean/MonoShim/SourceOnly.lean:150-154
theorem closed_target_meets_specs_in_source_semantics (P : Program) (cfg : MonoCfg)
    (T : List Key) (Q : Key → Spec) (hC : Closed P.sig (tableM P cfg T) T)
    (hG : GenericVerified P Q) (hI : ImplsConform P Q T) (hS : SynthVerified P cfg Q T)
    (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T) :
    ∀ k ∈ T, MeetsAt P.sig (srcDef P) (Q k) k := by
```

- **Plain claim.** For every program, configuration, key list `T` and spec assignment `Q`: if the table restricted to `T` is closed, every generic body is verified at every instantiation against its spec assuming `Q` on the keys it requests, every user impl body (trait method, user `Drop`, user `Clone`) of a key in `T` verifies against its spec, and every synthesized body for a shim key of `T` verifies against its spec, then every key of `T` meets its spec in the monomorphic table `tableM P cfg T` (`MeetsAt`: every run of `runKey` over that table, at every fuel and initial state, satisfies the spec), in the partial-correctness sense (out-of-fuel outcomes exempt). If, in addition, on every shim key of `T` the synthesized body is defined exactly when the source construct is and is behaviourally equivalent to it under every call oracle (H2), and every key of `T` is in normal form (H3a), then every key of `T` meets its spec in the source semantics `runS` (`closed_target_meets_specs_in_source_semantics`). Edge-closure, (H1) and (H3b) are not hypotheses of that theorem: the edge function `cfg.E` does not occur in `tableM`, and on a closed target (H3b) follows from (H3a) (`canonicalRefs_of_closed_canonicalKeys`).
- **Tier.** T0: soundness of verifying mutually recursive procedures against assumed specs, by induction on the call-depth index, restated for a closed monomorphic table.
- **Hypothesis ledger** (for `closed_target_meets_specs_of_generic_impl_synth_verified`).
  - `hC` — callees must be inside the target. Tight: `nonclosed_target_breaks_spec_transfer` (a 2-function program whose target stops at the root).
  - `hG` — user bodies must be verified. Tight: `unverified_generic_body_breaks_spec_transfer` (a 1-function program ignoring its spec).
  - `hI` — generic bodies rely on trait-method specs. Tight: `generic_verified_wrong_at_nonconforming_impl` (a 1-function generic program with two impls, one violating the trait-method spec; positive control at the conforming impl: `generic_verified_right_at_conforming_impl`).
  - `hS` — synthesized glue decides drop-event order. Tight: `source_defs_verified_yet_program_violates_spec_under_reverse_glue` (`P4a` with the reverse-glue synthesizer).
  - Each witness asserts `¬ (∀ k ∈ T, MeetsAt …)` explicitly.
- **Hypothesis ledger** (for `closed_target_meets_specs_in_source_semantics`; six hypotheses).
  - `hC` — keys outside the target are not covered by `hI` and `hS`. Tight: `nonclosed_target_breaks_source_transfer` (`P4a` with the target `[main]` and the "free before release" specs `Q4aRev`).
  - `hG` — user bodies must be verified. Tight: `unverified_generic_body_breaks_source_transfer` (a 1-function program ignoring its spec).
  - `hI` — generic bodies rely on trait-method specs. Tight: `nonconforming_impl_breaks_source_transfer` (a 1-function generic program with two impls, one violating the trait-method spec).
  - `hS` — the synthesized glue must meet its spec. Tight: `unverified_synth_breaks_source_transfer` (`P4a` with the standard synthesizer and `Q4aRev`).
  - `h2` (H2) — the source semantics runs the source rules, not the synthesized bodies. Tight: `synth_disagreement_breaks_source_transfer` (`P4a` with the reverse-glue synthesizer and `Q4aRev`; every key of `T4a` meets its spec in the table, and `main` violates it in `runS`).
  - `h3a` (H3a) — the source normalizes a key, the table is keyed literally. Tight: `noncanonical_key_breaks_source_transfer` (a program without functions, one associated type, and impls of one method at `<base 0 as 0>::Out` and at `base 1`).
  - Each witness asserts the other five hypotheses and `¬ (∀ k ∈ T, MeetsAt P.sig (srcDef P) (Q k) k)` explicitly.
- **Depth.** shallow (the source-transfer theorem composes the table theorem with `meetsAt_tableM_iff_srcDef_of_closed`, which applies `meetsAt_tableM_iff_srcDef_of_adequacy`, a consequence of R2, to the configuration with the same synthesizer and the full edge function).
- **Non-vacuity.** `P4a_std_meets_specs` (all four hypotheses of `closed_target_meets_specs_of_generic_impl_synth_verified` hold for `P4a` with the standard configuration and `Q4a`); `P4a_std_meets_specs_in_source_semantics` (all six hypotheses of `closed_target_meets_specs_in_source_semantics` hold for the same instance).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R6).
- **Prior art.** Hoare, "Procedures and parameters: an axiomatic approach", LNM 188, pp. 102–116, 1971, doi:10.1007/BFb0059696; Apt, "Ten Years of Hoare's Logic: A Survey—Part I", TOPLAS 3(4):431–483, 1981, doi:10.1145/357146.357150; Nipkow, "Hoare Logics for Recursive Procedures and Unbounded Nondeterminism", CSL 2002, LNCS 2471, pp. 103–119, doi:10.1007/3-540-45793-3_8 (mechanized in Isabelle/HOL). Liskov and Wing, "A Behavioral Notion of Subtyping", ACM TOPLAS 16(6):1811–1841, 1994, doi:10.1145/197320.197383 (impl conformance, `hI`).
- **Design question.** What suffices, beyond verifying generic source, for every instance of a closed target to be correct?

Basis: execution (Lean kernel check)

### R7. Least fixpoint, independent of the order of an admissible worklist scheduler

```lean
-- lean/MonoShim/Worklist.lean:91-94
theorem collect_mem_iff_reach (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (hs : SchedOK sched) (roots : List Key) (fuel : Nat) (T : List Key)
    (h : collect edges sched roots fuel = some T) :
    ∀ k, k ∈ T ↔ Reach edges roots k := by
```
```lean
-- lean/MonoShim/Worklist.lean:120-123
theorem collect_order_independent (edges : Key → List Key) (s1 s2 : List Key → List Key → List Key)
    (hs1 : SchedOK s1) (hs2 : SchedOK s2) (roots : List Key) (n1 n2 : Nat) (T1 T2 : List Key)
    (h1 : collect edges s1 roots n1 = some T1) (h2 : collect edges s2 roots n2 = some T2) :
    ∀ k, k ∈ T1 ↔ k ∈ T2 := by
```

- **Plain claim.** For every edge function, every admissible scheduler (one that neither loses nor invents worklist entries), every root list and fuel: if the worklist collector `collect` returns `T`, then `T` contains exactly the keys reachable from the roots; hence two admissible schedulers that both return a set return sets with the same members.
- **Tier.** T0: worklist computation of graph reachability, restated for the toy collector.
- **Hypothesis ledger** (for `collect_mem_iff_reach`).
  - `hs` — the worklist must neither lose nor invent entries. Tight: `inadmissible_scheduler_misses_keys` (a 2-function program and a scheduler that discards new keys; asserts `¬ (∀ k, k ∈ T ↔ Reach …)`).
  - `h` — the collector returns a set; this defines `T` (`harmless`: it names the output being characterized).
- **Hypothesis ledger** (for `collect_order_independent`).
  - `hs1` — the first scheduler must be admissible. Tight: `inadmissible_first_scheduler_breaks_order_independence` (a 2-function program; `schedDrop` first, FIFO second; asserts `¬ (∀ k, k ∈ T1 ↔ k ∈ T2)`).
  - `hs2` — the second scheduler must be admissible. Tight: `inadmissible_second_scheduler_breaks_order_independence` (the same program with the schedulers swapped).
  - `h1`, `h2` — both collectors return sets; these define `T1` and `T2` (`harmless`: they name the outputs being compared).
- **Depth.** shallow.
- **Non-vacuity.** `fifo_lifo_same_set_example` (FIFO and LIFO, both admissible, on `Pall`).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R7).
- **Prior art.** rustc `collector.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` L57–59: "Starting from the roots, find uses by inspecting the MIR representation of the item corresponding to a given node, until no more new nodes are found." (documentation). Mechanized worklist and graph-search reachability: Lammich and Neumann, "A Framework for Verifying Depth-First Search Algorithms", CPP 2015, pp. 137–146, doi:10.1145/2676724.2693165; Wimmer and Lammich, "Worklist Algorithms", Archive of Formal Proofs, 2024, https://isa-afp.org/entries/Worklist_Algorithms.html.
- **Design question.** Is the collected target independent of collection order?

Basis: execution (Lean kernel check)

### R8. Polymorphic recursion: finite runs, divergent collection

```lean
-- lean/MonoShim/Termination.lean:65-66
theorem polyrec_runs_finite (c : Nat) (evs : List Nat) :
    (runS P5 (c + 3) (.inst 0 []) ⟨evs, c⟩).1 = .ok := by
```
```lean
-- lean/MonoShim/Termination.lean:73-74
theorem polyrec_instances_reachable (k : Nat) :
    Reach (edgesM P5 (stdCfg P5)) [.inst 0 []] (.inst 1 [boxIter k (.base 0)]) := by
```
```lean
-- lean/MonoShim/Termination.lean:108-109
theorem polyrec_collector_diverges (sched : List Key → List Key → List Key) (hs : SchedOK sched)
    (fuel : Nat) : collect (edgesM P5 (stdCfg P5)) sched [.inst 0 []] fuel = none := by
```

- **Plain claim.** In program `P5` (`main` calls `f::<base 0>`; `f<T>` calls `f::<Box<T>>` under the counter guard), for every initial counter value `c` the source run of `main` with fuel `c + 3` completes normally; yet every `f::<Box^k<base 0>>` is reachable, and for every admissible scheduler and every fuel the worklist collector returns `none`.
- **Tier.** T0: polymorphic recursion defeats static whole-program monomorphization (Mycroft 1984; Tolmach and Oliva 1998; Griesemer et al. 2020, §2.4 and Fig. 10), restated in the toy.
- **Hypothesis ledger.**
  - `hs` (in `polyrec_collector_diverges`) — an inadmissible scheduler may stop early. Tight: `polyrec_inadmissible_scheduler_terminates` (the same program; a scheduler that discards new keys returns a set at fuel 5).
- **Depth.** shallow.
- **Non-vacuity.** `P5` itself (the theorems are about this program). The hypothesis `hs : SchedOK sched` of `polyrec_collector_diverges` is satisfiable: `polyrec_fails_rankCheck_and_diverges` proves `SchedOK fifo` and that the FIFO collector returns no set on `P5` at any fuel.
- **Positive control.** `P5flat_collects`: non-growing self-recursion collects a finite set.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R8).
- **Prior art.** Mycroft, "Polymorphic type schemes and recursive definitions", International Symposium on Programming, LNCS 167, pp. 217–228, 1984, doi:10.1007/3-540-12925-1_41. Tolmach and Oliva 1998 (doi:10.1017/S0956796898003086). Griesemer et al., "Featherweight Go", PACMPL 4 (OOPSLA), pp. 1–29, 2020, doi:10.1145/3428217 (arXiv:2005.11710v4), §2.4 and Fig. 10.
- **Design question.** Can a verifier assume that the collected target is finite?

Basis: execution (Lean kernel check)

### R9. Termination under a rank check, a normal associated-type table and an admissible scheduler

```lean
-- lean/MonoShim/RankTermination.lean:1087-1090
theorem collect_terminates_of_rankCheck_of_assocNormal (P : Program) (rank : Nat → Nat)
    (hrank : rankCheck P rank = true) (hassoc : assocNormal P = true)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key) :
    ∃ fuel T, collect (edgesM P (stdCfg P)) sched roots fuel = some T := by
```

- **Plain claim.** For every program `P`, every rank function `rank` such that `rankCheck P rank = true` (every function-instance reference in a function body from `f` to `g` has `rank g ≤ rank f`, strictly `<` when some type argument mentions a type parameter under `box`, `pair` or `proj`), if every right-hand side of `P.assoc` is in normal form (`assocNormal P = true`), then for every admissible scheduler and every root list there is a fuel at which the standard collector returns a set.
- **Tier.** T1: function-level termination certificates for monomorphization are folklore (cf. the `nomono` check of Featherweight Generic Go, a different, instance-level occurs check); not mechanized for a collector with synthesized shims.
- **Hypothesis ledger.**
  - `hrank` — rules out type-growing call cycles. Tight: `polyrec_fails_rankCheck_and_diverges` (a 2-function program with polymorphic recursion and no traits or impls; `rankCheck` fails for every rank, `assocNormal` and `SchedOK fifo` hold, no fuel returns a set).
  - `hassoc` — every right-hand side of `P.assoc` must be in normal form (`assocNormal P = true`, a condition on the table under which single-pass normalization is idempotent, `ty_norm_idem_of_assocNormal`; whether idempotence of `Ty.norm` alone would suffice is not examined), or each normalization step can grow a type. Tight: `nonnormal_assoc_breaks_termination` (a 2-function program with no growing type argument, a canonical root, and one self-referential associated type).
  - `hs` — the worklist must neither lose nor invent entries. Tight: `inadmissible_scheduler_breaks_termination` (the empty program and a scheduler that invents fresh keys).
- **Depth.** substantive.
- **Non-vacuity.** `P5ok_rankCheck_and_collects` (growth along a non-recursive chain; `rankCheck`, `assocNormal` and `SchedOK fifo` hold and the collector returns a set).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R9).
- **Prior art.** Griesemer et al., "Featherweight Go", PACMPL 4 (OOPSLA), pp. 1–29, 2020, doi:10.1145/3428217 (arXiv:2005.11710v4): Theorem 5.1 (Decidability), Theorem 5.2 (Monomorphisable), §5.3 (`nomono` is conservative). Tolmach and Oliva 1998 (doi:10.1017/S0956796898003086), whole-program monomorphization of ML, which has no polymorphic recursion.
- **Design question.** Which decidable check guarantees a finite verification target?

Basis: execution (Lean kernel check)

### R10. Precomputed versus on-demand shim synthesis

```lean
-- lean/MonoShim/Worklist.lean:147-154
theorem precomputed_and_on_demand_synthesis_same_target (P : Program) (E : Stmt → List Key)
    (synth : Key → Option Stmt) (pre : List (Key × Stmt)) (roots : List Key)
    (s1 s2 : List Key → List Key → List Key) (hs1 : SchedOK s1) (hs2 : SchedOK s2)
    (n1 n2 : Nat) (T1 T2 : List Key)
    (hpre : ∀ k, Reach (edgesM P ⟨E, synth⟩) roots k → k.isShim = true → pre.lookup k = synth k)
    (c1 : collect (edgesM P ⟨E, synth⟩) s1 roots n1 = some T1)
    (c2 : collect (edgesM P (preCfg E pre)) s2 roots n2 = some T2) :
    (∀ k, k ∈ T1 ↔ k ∈ T2) ∧ ∀ k, tableM P ⟨E, synth⟩ T1 k = tableM P (preCfg E pre) T2 k := by
```

- **Plain claim.** For every program, edge function, synthesizer `synth`, precomputed shim table `pre`, roots, admissible schedulers and fuels: if `pre` agrees with `synth` on every shim key reachable under the on-demand pipeline, and both pipelines' collectors return sets, then the sets have the same members and the emitted tables coincide on every key.
- **Tier.** T0: an instance of the fact that reachability is determined by the values of the edge function at reachable keys (`reach_congr`), with R7.
- **Hypothesis ledger.**
  - `hpre` — a stale table changes the bodies, hence the edges. Tight: `stale_precomputed_table_changes_target` (a 2-function program with one destructor; the empty table misses the reachable glue key).
  - `hs1` — least-fixpoint characterization of the on-demand output. Tight: `inadmissible_on_demand_scheduler_breaks_precomputed_equality` (a 2-function program without shim keys; a scheduler discarding new keys on the on-demand side, FIFO on the precomputed side).
  - `hs2` — least-fixpoint characterization of the precomputed output. Tight: `inadmissible_scheduler_breaks_precomputed_equality` (the same program; FIFO on the on-demand side, a scheduler discarding new keys on the precomputed side).
  - `c1`, `c2` — both collectors return sets; these define `T1` and `T2` (`harmless`: they name the outputs being compared).
- **Depth.** shallow.
- **Non-vacuity.** `precomputed_example` (all hypotheses hold on `P2a` with `pre2a`, FIFO and LIFO).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R10).
- **Prior art.** rustc `collector.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` L141–154 (eager and lazy collection strategies) and L23–29 ("The following things also result in LLVM artifacts, but are not collected here, since we instantiate them locally on demand when needed in a given codegen unit:", listing Constants, VTables and Object Shims) (documentation).
- **Design question.** May a verification target be assembled from shims synthesized lazily during collection?

Basis: execution (Lean kernel check)

### R11. Per-unit duplication of shims

```lean
-- lean/MonoShim/Worklist.lean:201-204
theorem linkUnits_eq_tableM_of_deterministic (P : Program) (E : Stmt → List Key)
    (synth : Key → Option Stmt) (T : List Key) (units : List (List Key × (Key → Option Stmt)))
    (hdet : DeterministicUnits synth units) (hcov : UnitsCover units T) :
    ∀ k, linkUnits P E units k = tableM P ⟨E, synth⟩ T k := by
```

- **Plain claim.** For every program, edge function, synthesizer `synth`, key list `T` and list of codegen units: if every unit's synthesizer agrees with `synth` on the shim keys that unit lists, and the units together list exactly the keys of `T` (shim keys may be listed by several units), then the linked table (first listing unit wins) equals the single-target table on `T` at every key.
- **Tier.** T0: a partial-map merge lemma.
- **Hypothesis ledger.**
  - `hdet` — duplicate copies must be identical. Tight: `nondeterministic_units_break_link_equality` (two units of `P4a`, one with reverse-order glue).
  - `hcov` — every key of `T` must be emitted by some unit. Tight: `uncovering_units_break_link_equality` (one unit of `P4a` missing glue keys).
- **Depth.** shallow.
- **Non-vacuity.** `deterministic_units_example` (two units of `P4a` sharing the pair's glue, both with the standard synthesizer).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R11).
- **Prior art.** rustc `collector.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` L23–29 (documentation). `library/core/src/ptr/mod.rs` at the same commit, L2471–2474 (`ptr::eq`): "However, note that comparing trait object pointers (`*const dyn Trait`) is unreliable: pointers to values of the same underlying type can compare inequal (because vtables are duplicated in multiple codegen units), and pointers to values of *different* underlying type can compare equal (since identical vtables can be deduplicated within a codegen unit)."; L2558–2559 (`ptr::fn_addr_eq`): "(From an implementation perspective, this is possible because functions may sometimes be processed more than once by the compiler, resulting in duplicate machine code.)" (documentation).
- **Design question.** Is duplicating shims across codegen units harmless for a verification target?

Basis: execution (Lean kernel check)

### R12. Normal associated-type tables give canonical references; a chained table on which one normalization pass is not idempotent can break closure

```lean
-- lean/MonoShim/Canonical.lean:98-99
theorem canonicalRefs_stdCfg_of_assocNormal (P : Program) (T : List Key)
    (hA : assocNormal P = true) (h3a : CanonicalKeys P T) : CanonicalRefs P (stdCfg P) T := by
```
```lean
-- lean/MonoShim/Canonical.lean:219-231
theorem noncanonical_refs_break_closure :
    assocNormal P6chain = false ∧
    collect (edgesM P6chain (stdCfg P6chain)) fifo [.inst 0 []] 10 = some T6 ∧
    CoversRefs P6chain.sig (stdCfg P6chain).E ∧ RootsIn [.inst 0 []] T6 ∧
    EdgesIn (edgesM P6chain (stdCfg P6chain)) T6 ∧
    SynthAgrees P6chain (stdCfg P6chain) T6 ∧ SynthTotal (stdCfg P6chain) T6 ∧
    InstDefined P6chain T6 ∧ CanonicalKeys P6chain T6 ∧ ¬ CanonicalRefs P6chain (stdCfg P6chain) T6 ∧
    ¬ Closed P6chain.sig (tableM P6chain (stdCfg P6chain) T6) T6 ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P6chain (stdCfg P6chain) T6 n r st = runS P6chain n r st) ∧
    runM P6chain (stdCfg P6chain) T6 4 (.inst 0 []) st0 =
      (.link (.inst 2 [.proj 1 (.base 0)]), st0) ∧
    runS P6chain 4 (.inst 0 []) st0 = (.ok, ⟨[9], 0⟩) := by
```

- **Plain claim.** For every program `P` and key list `T`: if every right-hand side of `P.assoc` is in normal form (`assocNormal P = true`) and every key of `T` is in normal form (H3a), then every key referenced by a body the standard pipeline emits for a key of `T` is in normal form (H3b). By contrast, in program `P6chain` (as `P6`, with the chained associated-type table `<base 0 as 0>::Out = <base 0 as 1>::Out`, `<base 0 as 1>::Out = base 1`, on which `assocNormal` fails), with the full edge function and the standard synthesizer, every hypothesis of R1 and R2 except (H3b) holds, the target is not closed, and the collected program's run ends in a link error at the once-normalized key `h::<<base 0 as 1>::Out>`, while the source run emits 9.
- **Tier.** T1: that referrers and definers must key instances by the same (idempotent) normal form is folklore; rustc normalizes before keying (`collector.rs` L700–710).
- **Hypothesis ledger** (for `canonicalRefs_stdCfg_of_assocNormal`).
  - `hA` — every right-hand side of `P.assoc` must be in normal form (`assocNormal P = true`, a condition on the table under which single-pass normalization is idempotent, `ty_norm_idem_of_assocNormal`; whether idempotence of `Ty.norm` alone would suffice is not examined). Tight: `noncanonical_refs_break_closure` (a 3-function program with a chained table; (H3a) holds, (H3b) fails).
  - `h3a` — the glue of a key that is not normal references keys that are not normal. Tight: `noncanonical_key_breaks_canonicalRefs` (a program without functions, one associated type, and the target key `dropGlue (Box<<base 0 as 0>::Out>)`).
- **Depth.** shallow (structural induction on statements; `refs_norm_canonical`).
- **Non-vacuity.** `canonical_refs_close_positive_control`: on `P6` (a normal table and a generic function whose body references a reducible projection), the standard pipeline collects a target satisfying (H3a) and (H3b) that is closed and agrees with the source at every fuel and state; the end-to-end lemma `collect_stdCfg_closed_and_adequate_of_assocNormal` combines R1, R2, R7 and this card.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R12).
- **Prior art.** rustc `collector.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` L700–710 (`fn monomorphize`, calling `instantiate_mir_and_normalize_erasing_regions`) (source).
- **Design question.** Must referrers and definers key instances by the same normal form, and when does the standard pipeline guarantee it?

Basis: execution (Lean kernel check)

### R13. The collected set can contain keys that never run (reference point)

```lean
-- lean/MonoShim/Relativity.lean:35-39
theorem collected_set_includes_dead_code_not_minimal :
    collect (edgesM P7a (stdCfg P7a)) fifo [.inst 0 []] 10 = some T7a ∧
    Key.inst 1 [] ∈ T7a ∧ ¬ EdgesIn (edgesM P7a (stdCfg P7a)) [.inst 0 []] ∧
    ∀ (n : Nat) (st : St),
      runM P7a (stdCfg P7a) T7a n (.inst 0 []) st = runM P7a (stdCfg P7a) [.inst 0 []] n (.inst 0 []) st := by
```

- **Plain claim.** In program `P7a` (`main` panics before calling function 1), the collector includes `inst 1 []`, yet removing it from the table changes no run from the root at any fuel and state; the smaller set is not closed under the collector's edges.
- **Tier.** T0 reference point.
- **Hypothesis ledger.** None (concrete instance).
- **Depth.** definitional.
- **Non-claims.** Listed under Boundaries (Non-claims per result, R13).
- **Prior art.** rustc `collector.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` L145–147 (lazy strategy: "Lazy strategy means that items will only be instantiated when actually used. The goal is to produce the least amount of machine code possible."), a goal statement, not a minimality claim (documentation).
- **Design question.** Reference point: is the collected target the set of instances that run?

Basis: execution (Lean kernel check)

### R14. Closure is relative to available bodies (reference point)

```lean
-- lean/MonoShim/Relativity.lean:75-82
theorem per_crate_collection_has_holes :
    collect (edgesAvail P7b (stdCfg P7b) availLocal) fifo [.inst 0 []] 10 = some [.inst 0 []] ∧
    ¬ Closed P7b.sig (tableM P7b (stdCfg P7b) [.inst 0 []]) [.inst 0 []] ∧
    runM P7b (stdCfg P7b) [.inst 0 []] 4 (.inst 0 []) st0 = (.link (.inst 1 []), st0) ∧
    runS P7b 4 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) ∧
    collect (edgesM P7b (stdCfg P7b)) fifo [.inst 0 []] 10 = some T7b ∧
    Closed P7b.sig (tableM P7b (stdCfg P7b) T7b) T7b ∧
    ∀ (n : Nat) (st : St), runM P7b (stdCfg P7b) T7b n (.inst 0 []) st = runS P7b n (.inst 0 []) st := by
```

- **Plain claim.** In program `P7b` (`main` calls `ext`, a non-generic function whose body drops a value with a destructor), a per-crate collector that creates no node for the unavailable key `inst 1 []` returns a target that is not closed, and the run from `main` ends in a link error at that key while the source run emits 3; collecting with every body available yields a closed target whose run from `main` agrees with the source at every fuel and state.
- **Tier.** T0 reference point.
- **Hypothesis ledger.** None (concrete instance).
- **Depth.** definitional (plus one application of R2).
- **Non-claims.** Listed under Boundaries (Non-claims per result, R14).
- **Prior art.** rustc `collector.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` L130–139: "The binary of a crate will not only contain machine code for the items defined in the source code of that crate. It will also contain monomorphic instantiations of any extern generic functions and of functions marked with `#[inline]`. The collection algorithm handles this more or less mono. If it is about to create a mono item for something with an external `DefId`, it will take a look if the MIR for that item is available, and if so just proceed normally. If the MIR is not available, it assumes that the item is just linked to and no node is created; which is exactly what we want, since no machine code should be generated in the current crate for such an item." (documentation).
- **Design question.** Reference point: does a per-crate target suffice for whole-program verification?

Basis: execution (Lean kernel check)

### Modeling bridges

Each item is a separate claim connecting the toy model to a real system, reasoned from the sources listed under **Evidence** (read, not executed). None is kernel-checked, and none is implied by the theorems above (model–system relation: none proved). The bridges for `glueSrc`, `srcDef0` and `cloneSrc` are stated with their definitions in §1.3.

- **Collector graph (R1, R7).** rustc's collector documentation describes mono items and their uses as a directed graph ("Mono items and the uses between them form a directed graph, where the mono items are the nodes and uses form the edges.", `collector.rs` L46–47) and collection as a traversal from the roots "until no more new nodes are found" (L57–59). The toy's `edgesM`, `Reach` and `collect` are modelled on this description; R7 shows that whenever the toy collector, run with an admissible scheduler (`SchedOK`), returns a key list, the members of that list are exactly the reachable keys. Nothing is derived about which edges rustc's implementation follows or about its parallel collection.

  Basis: derived (modeling bridge)

- **Reference kinds (R3).** The four edge kinds that R3 removes correspond to documented rules: (a) drops on cleanup paths are drop statements, and "Drop glue mono items are introduced by MIR drop-statements." (`collector.rs` L114); (b) for a vtable created by unsizing, the documentation says "we need to instantiate all dyn-compatible methods of the trait" (L122–124); (c) "whenever we encounter a function or method in operand position, we treat it as a use of the current mono item" (L109–111); (d) the reify shim of a `#[track_caller]` function corresponds to `ShimKind::Reify` (`compiler/rustc_middle/src/ty/instance.rs` L114–118: such functions "must have their implicit caller location argument populated for a call") and to the Reference's statement that "coercing a function with `#[track_caller]` to a function pointer creates a shim" (`src/attributes/codegen.md` L1047). The toy represents that shim by a distinct key, `reifyShim`, produced by `reifyKey`. R3 shows that each edge kind cannot be removed from (H1) in the toy; it makes no claim about rustc's behaviour.

  Basis: derived (modeling bridge)

- **Clone ladder (R4).** `ladder` follows the block structure documented in `clone_fields` of `compiler/rustc_mir_transform/src/shim.rs` (comments L673–678: clone field `i`; on unwinding, drop the clones made so far through a chain of unwind blocks), whose cleanup drops terminate on a panic (`UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`, L694). `cloneAgg` follows the Reference's rule that the temporaries holding evaluated operands are dropped, in reverse order of creation, when a later operand panics (`destructors.scope.intro` and `destructors.scope.operands`, `src/destructors.md` L58–59 and L352–355). The correspondence is by reading; no shim produced by rustc was inspected.

  Basis: derived (modeling bridge)

- **Field drop order (R5, R6, R11).** The standard synthesizer's glue for `pair a b` drops `a` then `b`, the order the Reference states for the fields of structs and tuples ("The fields of a [struct] are dropped in declaration order.", L12; "The fields of a [tuple] are dropped in order.", L14 of `src/destructors.md`). `synthRev`, used by `cfgRev`, drops the fields in reverse declaration order; it is a hypothetical synthesizer variant, and the package attributes it to no compiler.

  Basis: derived (modeling bridge)

- **Polymorphic recursion (R8, R9).** `P5` is the classical polymorphic-recursion pattern (`f<T>` calls `f<Box<T>>`) discussed by Mycroft (1984), Tolmach and Oliva (1998) and Griesemer et al. (2020, §2.4, Fig. 10). Whether rustc accepts, rejects or limits such programs is not examined. `rankCheck` is not the `nomono` check of Featherweight Generic Go, and no equivalence is claimed.

  Basis: derived (modeling bridge)

- **Eager and lazy synthesis (R10).** rustc's collector documents an eager and a lazy collection strategy (`collector.rs` L141–154) and lists constants, vtables and object shims among the things instantiated "locally on demand when needed in a given codegen unit" (L23–29). R10 concerns when shim bodies are computed in the toy (on demand, or looked up in a precomputed table); it does not model the eager strategy's extra roots.

  Basis: derived (modeling bridge)

- **Duplication across codegen units (R11).** The documentation of `core::ptr::eq` (`library/core/src/ptr/mod.rs` L2471–2474) states that vtables can be duplicated in multiple codegen units, and that of `core::ptr::fn_addr_eq` (L2558–2559) that functions may be processed more than once by the compiler. In the toy, duplicated shim bodies are not observable, because the toy has no address comparison; R11 therefore does not transfer to Rust programs that compare function or vtable addresses.

  Basis: derived (modeling bridge)

- **Normalization before keying (R12).** rustc's collector monomorphizes an instance's MIR with `instantiate_mir_and_normalize_erasing_regions` (`collector.rs` L700–710, `fn monomorphize`). The toy normalizes with the single-pass `Ty.norm`, which is idempotent when every right-hand side of the associated-type table is normal (`assocNormal`, `ty_norm_idem_of_assocNormal`). Nothing is claimed about how rustc keys instances.

  Basis: derived (modeling bridge)

- **Lazy collection is not minimal (R13).** The lazy strategy's documentation says "The goal is to produce the least amount of machine code possible." (`collector.rs` L145–147). This is a goal statement, not a minimality claim; R13 shows that, in the toy, the reachable set can contain keys that never run.

  Basis: derived (modeling bridge)

- **External items without available bodies (R14).** rustc's documentation (`collector.rs` L130–139) says that a crate's binary also contains instantiations of extern generic functions and of `#[inline]` functions, and that when the MIR of an external item is not available, "it assumes that the item is just linked to and no node is created". `P7b`'s unavailable function is neither generic nor `#[inline]`, so it corresponds to the case the documentation describes as linked to; a generic external function is not this case.

  Basis: derived (modeling bridge)

## Boundaries

### Scope of every result

- (R1–R14) Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier. Connections to real systems are the separate `derived (modeling bridge)` claims under Findings.
- (R1–R14) The constructs listed as absent in §1.1 ("Restrictions of the toy") are not examined: generic impls, generic `Drop`/`Clone` impls, parametric associated types, value arguments, closures, statics, constants, "mentioned" items, `FnPtr`/`ClosureOnce`/`VTable` receiver shims and async drop glue.
- (R1–R14) No existing compiler, linker or program verifier is modelled or tested; no result describes a defect in any of them.

### Non-claims per result

Verbatim from the cards.

#### R1

Does not show that any algorithm computes such a `T` (R7) or that collection terminates (R8, R9). `Closed` is key membership of runtime references; it does not by itself give behavioural agreement (R2). None of the constructs listed as absent in §1.1 is covered. (H1) is stated against the toy's own `refs`; nothing is claimed about which edges rustc's collector follows. The closed set need not be dynamically minimal (R13). `glueSrc` models the two-field drop ladder (§1.3); drops through a panicking cleanup drop abort, and nothing further about rustc's drop elaboration (drop flags, async drop, enums) is modelled. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R2

R2 does not assume `Closed`, (H2t) or (H0): its hypotheses can hold on a target with a key that is undefined both in the table and in the source, and `runM` and `runS` can then agree by both returning the same `Res.link` outcome (`adequacy_holds_on_nonclosed_target`: every hypothesis of R2 holds on a target that is not closed, and both runs from the root end in `Res.link`). The hypotheses of R2 do not exclude `Res.link` outcomes (the run in `adequacy_holds_on_nonclosed_target` ends in one). On a closed target, no run from a key of the target ends in `Res.link` (`closed_excludes_link`), and R1 derives closedness from its hypotheses; closedness is not necessary for runs from the roots to avoid `Res.link`: in `dead_undefined_call_never_links` the hypotheses of R2 hold, the target is neither closed nor source-defined, and no run from the root ends in `Res.link` (the undefined call is unreachable). `S` and `M` are the same interpreter with two resolvers; agreement is equality of fuel-indexed outcomes, not a bisimulation between independently defined semantics, and `S` is a toy, not the semantics of Rust. The claim quantifies over runs produced by `runKey` at every fuel (out-of-fuel outcomes included). (H2) asks for equivalence under every call oracle, which is stronger than any single program needs; weaker notions are not examined. "Link error" is the toy's undefined-key outcome; nothing is claimed about symbol mangling or linkers. `Ty.norm` is a single pass (§1.1); if `assocNormal P = true` and every root is in normal form, then (H3a) holds for every target that the collector returns when run with an admissible scheduler (`SchedOK`) (`collect_canonicalKeys_of_assocNormal`), and for the standard configuration (H3b) follows from (H3a) and `assocNormal P = true` for every key list `T` (`canonicalRefs_stdCfg_of_assocNormal`, R12); no other normalization strategy is examined. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R3

Each witness is one small program; it shows that the named edge kind cannot be dropped from (H1) in the toy, not how often real programs need it. No claim that rustc misses any edge. The reify-shim case models the ABI mismatch as a distinct key; caller locations are not modelled. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R4

Statement-level aggregates have any arity, but the toy type grammar has binary pairs and no wider tuples, so the clone shim of a toy type has two fields. Clones are not values: events come from user `Clone`/`Drop` bodies. `box τ` has no clone behaviour in the toy (§1.3). Both `ladder` and `refs` of `cloneAgg` reference the drop glue of the last field, which no unwind path drops (as in rustc's unused final cleanup block); such a key can be collected without ever running. Nothing is proved about rustc's shim implementation; the correspondence to its documented block structure is a `derived (modeling bridge)`. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R5

The impossibility rests on letting the synthesizer range over configurations that disagree with the source drop rule; for configurations and targets satisfying (H2) and the other hypotheses of R2 (with roots `[main]`), the verdict `srcVerdict` — a function of the program and specs alone that checks the source semantics, including the language-defined glue `glueSrc` — is correct (`srcVerdict_correct_of_adequacy`). `srcVerdict` is noncomputable; nothing here gives a decision procedure for `MeetsAt` or claims one exists. R5 therefore does not say that whole-program specs cannot be verified from source, nor that synthesized shims must be extracted and verified separately; it says that a verdict blind to the synthesizer cannot be correct for every synthesizer. No program verifier is modelled; nothing here is a statement about any existing tool. `synthRev` is a hypothetical synthesizer variant, not a claim about any compiler. Generic verification is per instantiation (`∀ τs`). A related but distinct failure — a generic body verified against a trait-method spec and wrong at a non-conforming user impl — is the tightness witness of `ImplsConform` in R6 (`generic_verified_wrong_at_nonconforming_impl`), not a synthesizer effect. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R6

`closed_target_meets_specs_of_generic_impl_synth_verified` establishes `MeetsAt` in `tableM P cfg T` (the `runM` resolver), not in `runS`: with a synthesizer that disagrees with `srcDef0` (violating (H2)), every key of `T` can meet `Q` in the table while `runS` violates `Q` (`synth_disagreement_breaks_source_transfer`, with `cfgRev` and specs demanding `[20, 10]`). For transfer to `runS` on a closed target, (H2) and (H3a) suffice together with the four hypotheses of that theorem, and each of the six is tight (see the hypothesis ledger of `closed_target_meets_specs_in_source_semantics`); edge-closure, (H1) and (H3b) are not assumed (`source_transfer_without_covering_or_edge_closure` is an instance in which (H1) and edge-closure both fail and the conclusion holds). `GenericVerified` quantifies over every concrete type-argument list (any length, including types without impls), not a single parametric proof, and `Q (.meth tr m t)` is indexed by the concrete type `t` rather than a `Self`-parametric trait spec. `T` is any closed key list; it need not be the collected set. Partial correctness; termination is not claimed. Specs are outcome predicates per key; there is no heap, frame rule or ownership. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R7

Says nothing when the collector does not return a set (R8, R9). The conclusion is equality of membership: the list order of `T` can depend on the scheduler (`fifo_lifo_same_set_example` shows two orders), nothing is claimed about the fuel each scheduler needs, and `SchedOK` permits a scheduler to duplicate worklist entries; neither equal order, equal fuel, nor absence of duplicates in the worklist is claimed. No model of rustc's parallel collection or of its used/mentioned distinction. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R8

The toy has no type system; the result refutes, in the toy, that every program whose runs are finite has finitely many reachable instances; it is not a statement about Rust's type system or about whether rustc accepts such programs. Finite runs are proved for fuel `c + 3`, not for every fuel. Escape hatches that defeat divergence: (1) compiling without monomorphization (dictionary passing, type erasure, or `dyn` boxing) compiles polymorphic recursion to a finite program (not proved here; Ellis et al. 2022 study dictionary passing for Featherweight Generic Go); (2) the collector's reference relation `refs` ignores the counter guard, so it is flow- and value-insensitive; for a fixed initial counter `c` the run of `main` calls `f` at `c + 1` type arguments (not proved here); (3) rejecting such programs statically: the rank check of R9 rejects `P5` for every rank (`polyrec_fails_rankCheck_and_diverges`). Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R9

Together with `assocNormal P = true`, a passing rank check makes the standard collector return a set under every admissible scheduler (R9); the check is not necessary: `rankCheck_not_necessary` gives a program on which the collector with the FIFO scheduler `fifo` returns a set and the check fails for every rank. `rankCheck` checks a supplied certificate; the package defines no procedure that finds a rank from `P` alone and does not prove `∃ rank, rankCheck P rank = true` decidable. `rankCheck` inspects function bodies; it can ignore impl, drop and clone tables and associated types because in the toy these are literal, non-generic tables (§1.1). In a language with generic trait, `Drop` or `Clone` impls, or parametric associated types, a function-level check does not rule out non-terminating monomorphization through impls (not proved here). `Ty.grows` counts a projection of a parameter as growing although normalization may shrink it (conservative). It is not Featherweight Go's `nomono` check (an occurs check over a closure of instances); no equivalence is claimed. Whether every divergent collection has a reachable type-growing cycle is unknown. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R10

R10 assumes that `pre` is already populated and equal to `synth` on every reachable shim key, and that both collectors terminate (`c1`, `c2`); it does not model how an eager pre-pass discovers which shim keys will be reachable, nor transfer termination from one pipeline to the other. rustc's documented eager strategy instantiates drop glue for every drop-able type even without a drop call; R10 is about when shim bodies are computed, not about adding roots. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R11

Linking is modelled as a first-listing-unit merge, not as internal linkage with each unit calling its own copy; with deterministic synthesis all copies are equal, so in the toy the choice does not matter. The toy has no function-pointer or vtable-pointer address comparison; in Rust, duplicating functions or vtables across codegen units is observable through address comparison even when every copy behaves identically (`core::ptr::eq` and `core::ptr::fn_addr_eq` document this; see Prior art). Symbol visibility and linker duplicate-symbol errors are not modelled. The edge-function argument `E` of `linkUnits` does not affect its result. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R12

`Ty.norm` is a toy single-pass normalizer; rustc's normalization (to a fixpoint, with regions erased) is not modelled, and nothing is claimed about how rustc keys instances. (H3b) for configurations other than the standard one is not examined. No claim that any compiler mis-keys instances. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R13

R13 refutes dynamic minimality (the collected set is the set of keys that run), not static minimality: every key list containing the roots and closed under the edges contains every reachable key (`reach_subset_of_rootsIn_edgesIn`), and by R7, whenever the collector run with an admissible scheduler (`SchedOK`) returns a key list, the members of that list are exactly the reachable keys. Computing the set of keys that run is not examined (undecidability in general is not proved here). Given R2's other hypotheses — (H1), (H2), (H3a) and (H3b) — adequacy (R2) holds for every key list `T` that contains the roots (HR) and is closed under the collector's edges (HE), not only for the collected set. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

#### R14

R14 shows that leaving unavailable external bodies out yields a table that is not closed; it does not rule out modular per-crate verification in which unavailable external items are checked against verified interface specifications (contracts), and does not model other crates supplying symbols or separate compilation. `P7b`'s unavailable function is neither generic nor marked `#[inline]`; rustc's documentation says a crate's binary also contains instantiations of extern generic functions and of `#[inline]` functions (see Prior art), so a generic external function is not this case (`derived (modeling bridge)`). Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, or any program verifier.

### Escape hatches

- **From R5 (no verdict determined by the program and its specs alone is correct for every synthesizer).** The impossibility is relative to the class of all synthesizers, including ones that violate (H2): for each verdict, the configuration it exhibits is either the standard one or `cfgRev`, and `cfgRev` violates (H2) (`synth_disagreement_breaks_adequacy`). Restricting to configurations and targets that satisfy R2's hypotheses with roots `[main]` — (HR), (HE), (H1), (H2), (H3a), (H3b) — defeats it: the noncomputable verdict `srcVerdict` is then correct (`srcVerdict_correct_of_adequacy`; instance `srcVerdict_correct_example`). (H2) is a property of the synthesizer relative to the source rules `glueSrc` and `cloneSrc`; `synthStd_agrees` (R4) establishes it for the standard synthesizer and every target. RustCompCert (arXiv:2602.07455v1, a workshop-presentation proposal describing ongoing work on a sequential subset of Rust without polymorphism or traits), which verifies generated drop glue inside a compiler, is cited in R5's prior art as an instance of verifying the synthesizer against a source semantics; nothing about it is kernel-checked here.
- **From R8 (divergent collection).** (1) Compiling without monomorphization (dictionary passing, type erasure, or `dyn` boxing) compiles polymorphic recursion to a finite program (not proved here). (2) The collector's reference relation `refs` ignores the counter guard; for a fixed initial counter `c` the run of `main` calls `f` at `c + 1` type arguments (not proved here). (3) Rejecting such programs statically: the rank check of R9 rejects `P5` for every rank (`polyrec_fails_rankCheck_and_diverges`). An inadmissible scheduler can also stop early (`polyrec_inadmissible_scheduler_terminates`), but its output is then not characterized by R7.

### Hypotheses whose tightness is not established

None among the ledgered hypotheses: every hypothesis in the hypothesis ledgers of R1–R14 is either `tight`, with a named counterexample theorem in which all other hypotheses hold and the conclusion fails, or `harmless` (R7's `h`, `h1`, `h2` and R10's `c1`, `c2`, which name the collector outputs being characterized or compared). The positive control `srcVerdict_correct_of_adequacy` (R5) is stated under R2's hypothesis bundle as a sufficient condition, and no necessity is claimed for any single hypothesis of it. The auxiliary lemmas quoted under Evidence carry no tightness claims of their own.

### Questions considered and left open

- **unknown:** whether every divergent collection has a reachable type-growing cycle (R9). Together with `assocNormal P = true`, a passing rank check is sufficient for termination of the standard collector under every admissible scheduler (R9); it is not necessary (`rankCheck_not_necessary`, with the FIFO scheduler `fifo`).
- **not examined:** a procedure that finds a rank from `P` alone, and decidability of the existence of a rank (R9); termination transfer between the precomputed and on-demand pipelines (R10); weaker notions than equivalence under every call oracle for (H2) (R2); normalization strategies other than single-pass `Ty.norm` (R2, R12); (H3b) for configurations other than the standard one (R12); computing the set of keys that run (R13).

### Disproved, dropped or unresolved statements

None. Every statement of R1–R14 is kernel-checked in the form quoted in Findings; none was found false, and none is left unproved.

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4:v4.34.1` (GitHub tag `v4.34.1` of `leanprover/lean4` = commit `5045d0056413266e57c625dcd7c365b10e377c52`, fetched from the GitHub API on 2026-11-21). Core Lean and `Std`, no Mathlib. The project builds from a fresh copy with Lake's artifact cache disabled, so every proof is re-elaborated and kernel-checked; its sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `extern` or `unsafe`. `audit/axioms.json` records `collectAxioms` for all 1147 package declarations; each depends on at most `propext`, `Classical.choice` and `Quot.sound`.

`audit/statements.json` records, for each of the 286 declarations that `results.json` references (results, hypothesis counterexamples, non-vacuity witnesses, positive controls, and every declaration this report names), the SHA-256 of its statement (the Lean `repr` of its type) and of its definition closure (the types and values of every package constant reachable from the statement; theorem bodies excluded). The table repeats those records, with the axioms of each declaration (names are in namespace `Toy.MonoShim`; "none" means no axiom). Basis for every theorem: execution (Lean kernel check).

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- | :--- |
| `adequacy_holds_on_nonclosed_target` | cited by name (R2) | Classical.choice, Quot.sound, propext | `5d964d5780747106f939265d4c80f63acc7b03af9ed2d0a6e76ed092859dec38` | `7b6a3082b445e075adf1b94802dab810501f52f3451c24c15f7941af057dd541` |
| `aggClone` | cited by name (R1) | propext | `ce8bf6a23201e26bf05f510b3ca7dc6c1f0b65af2065084487268cac3be28732` | `45a76f508cc81257437fbebdd67a9e8ab6cf2caecd2a80118537183521f556ce` |
| `appends` | cited by name (R1) | none | `746e75cc20cad3d7366c56b718710bdb1d72cc199a5b6b3cd251a005bc98f765` | `cb263d9fd9f216cbb55a67f3c53a40c2ada076a8e3358b7344a9a1c29b2b24e8` |
| `assocLookup` | cited by name (R1) | none | `f0436887b3d22fd083ec8a185ac3d1b1c1a5e6bfbb9fa6b5f420d0b4ac0f06e6` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `assocNormal` | cited by name (R1) | propext | `0232a214b0f58ce29df0777705ed1e5d7c48ffc290cb94ec26b5a59ec210b5f8` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `assocNormal_examples` | cited by name (R1) | propext | `8e144bd04a0f966a84af94d72fc0e097c5617f7bf5fad2c1e2b40bebd5040949` | `42395f0389d5bbf4fd17dd2a529ba61ba68c90f06aece95adbc39ef54ffddbc3` |
| `availLocal` | cited by name (R14) | propext | `52a989f5aa15bd74e0b3d58142c8b3cc93248c3035e7f8a7857fe5437e31be1b` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `BodyEquiv` | cited by name (R1) | propext | `5e6497134eb20c24a39125fb9bb59e82617b0ece9629410c41537321d02aee64` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `bodyEquiv_neg_example` | cited by name (R1) | propext | `4d67f7956a461a4c03b2920397d799e93520c6934d674d308cd84a9c0cfd3453` | `30c1f26fbdeaaabcb8d78493d6932bdaf64c94ed16de9acb9ac79db26bcda0a0` |
| `bodyEquiv_pos_example` | cited by name (R1) | propext | `dc7596b125edf046aeceaa6ba31a4f8b058d62741bdb8c6132dfe8a2e7295386` | `8b8168c208d3d0e3783ba91572e1834f96cd99194646fee7f67b37c9ae154d29` |
| `bodyM` | cited by name (R1) | propext | `963c0ec5ac2defa95b400f0890d5af1d72cfe54db9f01d3d8134a12c87b0b1a5` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `boxIter` | cited by name (R8) | none | `bf555988212c2459867a285e4ed9d1d6637b33660a18abbf997dc28e2d757766` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `Call` | cited by name (R4) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `canonical_neg_example` | cited by name (R1) | propext | `c1afe796290403cb5ddd3f4c652497726f34ab75c0f57998a133af29ccb0207c` | `adb9ff224e2c0d2b726962f0dbd13ff832a3ef74ad336419149c0dcb7fcf6e5f` |
| `canonical_pos_example` | cited by name (R1) | propext | `7d7b0d5ed6ec230b21ef97eddc95c46d5ea73a532d6b95a20ed1d775c9b41cd5` | `8cc7d20da4ce104234de32f9d74d33eb7d0e43925a1ad61984cf1b732d596046` |
| `canonical_refs_close_positive_control` | R12 non-vacuity | Classical.choice, Quot.sound, propext | `dfc49ed3175bb8edc4db4609eef823d12f59f7a135b3ec72bb6a26e4998b816a` | `c39753a2c545e78deb1b726db2418b25daa54e1365b6260b2fef2a6bd2d7c37e` |
| `CanonicalKeys` | cited by name (R2) | propext | `8034a89d1d726daa217cf1c2565dafca27bbc3cc4b39e84a13cb7482cd221808` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `CanonicalRefs` | cited by name (R1) | propext | `c672f7922f48f62c971c508a75cd7c2f4aea6b5ad09a8383a1ba6d5ec97b40bc` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `canonicalRefs_of_closed_canonicalKeys` | cited by name (R6) | propext | `ad20ad09d594f6849e6f546a5d682ce0ef19c3800f8023c525f60507f6ce8b80` | `06312a8f3f249291931a5a530a5f5a8af6d5505c364588adaa080d6cda6e81f8` |
| `canonicalRefs_stdCfg_of_assocNormal` | cited by name (R1); R12 result | Quot.sound, propext | `8674c1095d4d33c755260a4418fca8293d41941976ce60fe288321f3708eef82` | `6e998c6b6e617e1e13fbbdae6f3329da5d62b2ac5d8f59aae54e9ea567bf9f2e` |
| `cfg2a` | cited by name (R3) | propext | `eaf90c578079e499c783b1405ffe4207d82ff00cae49b447626c1e6f92edc7d0` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `cfg2b` | cited by name (R3) | propext | `eaf90c578079e499c783b1405ffe4207d82ff00cae49b447626c1e6f92edc7d0` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `cfg2c` | cited by name (R3) | propext | `eaf90c578079e499c783b1405ffe4207d82ff00cae49b447626c1e6f92edc7d0` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `cfg2d` | cited by name (R3) | propext | `eaf90c578079e499c783b1405ffe4207d82ff00cae49b447626c1e6f92edc7d0` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `cfg3` | cited by name (R1) | propext | `eaf90c578079e499c783b1405ffe4207d82ff00cae49b447626c1e6f92edc7d0` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `cfgJunkEdges` | cited by name (R6) | propext | `51418056cccb4103ae134769ec30303a7841d625a4a14fc894858b4b98d43593` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `cfgNoSynth` | cited by name (R1) | propext | `51418056cccb4103ae134769ec30303a7841d625a4a14fc894858b4b98d43593` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `cfgRev` | cited by name (R5) | propext | `51418056cccb4103ae134769ec30303a7841d625a4a14fc894858b4b98d43593` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `cleanup_edges_missing_break_closure` | cited by name (R1); R2 counterexample (h1); R3 result | Quot.sound, propext | `8aae30694c28a7f3d1045a08a9c4681d75569f3fd634023b3fbce1c6ff54d4b5` | `dd8d228157ab4222d2299d890a3030b780edbbe4c9acf3cea46563057d9b5be5` |
| `cleanupDrops` | cited by name (R1) | propext | `22f15fbc42d143f8d3463ff24d8156df6153b1dd78bb3963679683dbe6104b32` | `45a76f508cc81257437fbebdd67a9e8ab6cf2caecd2a80118537183521f556ce` |
| `cloneKey` | cited by name (R1) | propext | `da37d7a32ed96551ec9ea9ae4e859cf38ab4c873eeeab5b2bc0880effafc9141` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `cloneKey_examples` | cited by name (R1) | propext | `5efd92b458329e89fd510023869ebefcc237ed5802a10fd8c1e69f837253ba1e` | `c7e2301dbc05f4241569e198d34fc4c87d58f7f511316a9fb9ab26ca20265da1` |
| `cloneSrc` | cited by name (R1) | propext | `49cd6de7f2f54286cee54bfd7ad81788335c9587e9500a53c6ce57c6b8c53f15` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `Closed` | cited by name (R1) | propext | `5b85860908d678afa1175e42bb2c0dd0681cf2459b7014d2505f3f8b153c4a8e` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `closed_examples` | cited by name (R1) | propext | `92a41a6d44e4940e787892aa4cd26d52771c16c65fc2f171122caedbc486f5c6` | `e3b77923376c280a146ca18a7914388ca687c43ee6531612de0a2f8520cce302` |
| `closed_excludes_link` | cited by name (R2) | Classical.choice, Quot.sound, propext | `4d8c5fc44be594f3a234f7c4ed7f02b7f9f17ccf8cd3877bdd4a54df74b544ca` | `ca35fc284230a3f2c159ab622b7f174a001b63577cc87a87a79fd7dc93a93a6c` |
| `closed_of_edgesIn_covering_total_canonicalRefs_instDefined` | R1 result | Quot.sound, propext | `62ffe720e0032e2a9e97bf848385dffc7ff12f633e79452d6267cc5eb4475966` | `911c9d00412d65478e463964c8f81744be7e94a557877735ec179585bfd319ed` |
| `closed_target_meets_specs_in_source_semantics` | R6 result | Classical.choice, Quot.sound, propext | `cf4378fa5782d663e32d04a9df09b754d2e05e754e44a519b77baf2bfbb828e2` | `91985bf7fbc5b9d2bbe60961a2049cbffc92df8e80a53ed49ea1e480ed38ce72` |
| `closed_target_meets_specs_of_generic_impl_synth_verified` | R6 result | propext | `b901ff4eefe5264b29c668d8f6459b0ca9c9bb4fc17a89f48f07701cfa54e0bb` | `0ea72bb3873248da881aa428c72e320a2ea904eee78d701ab2cb4f64fb7a2ad3` |
| `collect` | cited by name (R7) | propext | `48f36b707c739b7b0e889a27cf1bc44ae81012ecc9acf873b6a09996eecce6e3` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `collect_canonicalKeys_of_assocNormal` | cited by name (R2) | Quot.sound, propext | `909d424d8ddfef7c2da1b87e3b648c92076b6396f3325f507366e6e06a0991d8` | `159986d77f92495baa2ecd7713b637b7f0c1fbd4847e88c79e0adfc7536e7365` |
| `collect_mem_iff_reach` | R7 result | Quot.sound, propext | `b627ce7c81a67d9724e8de9a31683e4730392a32de040395dda4572a33db7de9` | `cf1413b03ec9f3197cddd71bf8095c87ed4d947e83fd1b8436618cb1d5a3fcad` |
| `collect_order_independent` | R7 result | Quot.sound, propext | `3562895b2800fad1e368ca0369916cd0d476fa7bf765bbd992541590c5fcb363` | `fc1ebd050ac534f48ccf7fc432edc54f156661a7108e4b9dfd3a429d00f19280` |
| `collect_stdCfg_closed_and_adequate_of_assocNormal` | cited by name (R12) | Classical.choice, Quot.sound, propext | `657b3476728b7eb9da6a36b118c805a8e667857c7194df282305d83b4d9bbe85` | `30afeba62637d9eabf1bb402722a045a855c14de4fd4e66b0e049dd65109f37a` |
| `collect_terminates_of_rankCheck_of_assocNormal` | R9 result | Classical.choice, Quot.sound, propext | `ecf12dcb2c27086ad852e0356ca58664ac2720d1875d1eac548290203ebae65a` | `eadfb7d104f862ea8fcb0834cd0f225ddd9cd557d83e9dd84023222d7245ad54` |
| `collected_set_includes_dead_code_not_minimal` | R13 result | propext | `05154515e9c68c47658046d85f8ffc9cae56dd84a75bbd31c86e033549893642` | `a5c7d76215b317806a6cd62e22417b94c1f0f954a8f58cde13a2b4dba11bc0eb` |
| `collectGo` | cited by name (R1) | propext | `ff7c0cb1feac50adfed74303d4d76ed987e6ce2e4f04061b35c6777a95829509` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `CoversRefs` | cited by name (R1) | propext | `c2cdc31889c551be2fa5b2e7242fe13cd535332a25218f92cfd596702b2e7285` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `coversRefs_neg_example` | cited by name (R1) | Quot.sound, propext | `9bdc630dd2f1fc5159a23c79bddd2e18a6d76bf62e24af686760810c229d12c3` | `7d22390a8fa891fe07ffa61ba0966ecbc64f1f01ab4193fd58a1b2f08f4e4abd` |
| `coversRefs_pos_example` | cited by name (R1) | propext | `4a09ad50903e8df0b733301b2d94e8674fd05341492aab7ad96ebf8aa36dd063` | `b48af3387256380b716f542ae096dc0e6505e7de68fc7204522245c75f2db0da` |
| `dead_undefined_call_never_links` | cited by name (R2) | Quot.sound, propext | `91964f558b013c57770aa6485b3eb45ff340bff216f3feca1f89d402a835afdb` | `0421bc8649eb215efd05ac623b9a684ed9b2fd3de162446aaf93fd33e4a3a30e` |
| `deterministic_units_example` | R11 non-vacuity | Classical.choice, Quot.sound, propext | `1ad7d1b9781e181ce5260d8e475b9541c16a4dcb3bef3943aef64c4923013650` | `c6174247e736f5d0fb6f6e100f405ea251127d5f6735c0e732d5b2daad9410b0` |
| `DeterministicUnits` | cited by name (R11) | propext | `75dc341af7ed0dbab01649a48f4b1655c45f9ae55be0d8ef17239d8639c6d7b3` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `deterministicUnits_examples` | cited by name (R1) | Classical.choice, Quot.sound, propext | `c09827a8dc474b6a2b0c413fb15aa9964339cce7cc8e13182544357e105f9019` | `9c364b13f3c8a4fb25a8fefd562d86fa1533f5a82d5a2e044008d4ab9a35f87b` |
| `edgesAvail` | cited by name (R14) | propext | `590b6dc98cf4d44cc7db099d157c546d6b90cb342209ee64ec384ac27b4fb543` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `EdgesIn` | cited by name (R1) | none | `0aa40435bba8b227b5d0f4af2b5f9d8f2832eaef7dd12a03877a3a52751426f8` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `edgesIn_examples` | cited by name (R1) | propext | `faf9bba3845a71dd9d9495b75cb239e26cfe43028b7cda69755c9b66b855e9e3` | `48706ba35d327209ab5481c8a5d155c4192b77d5845d452a840173d1302419cc` |
| `edgesM` | cited by name (R1) | propext | `0bd4b1728c9826f51436d56032d070fe0c8158be2d4e0092209fa771f5993ea4` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `execS` | cited by name (R1) | propext | `85b506eaf9f6967e0dfa6719e70581f4ac6eedd3905e91baa5d9f35c5caa3bc5` | `cf044f6d9291f7cc80ab655ef5817a30cb9afc01e4f204968312aa7a753d320c` |
| `execS_congr` | cited by name (R2) | Classical.choice, Quot.sound, propext | `6054f3e21eb7a20ad4190a7a03c167b2be1a34c70a7c7bccda8b5fe95707473d` | `483375a8ea9e6bb6cdde24a37827b891a03549f2976ad50920d427d8b18c3308` |
| `fifo` | cited by name (R7) | none | `c73c6a5b9c65fc9829c121e08d9ef5929496178d238d526d5df638adc0866e85` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `fifo_lifo_same_set_example` | R7 non-vacuity | propext | `6c924f1a165906fec01f757edc178c8d2c26590db487d4da56574e25478916d7` | `5117654db75b36e686983ccc779f56faf87119ef29a6205ead4a15f278f9bc20` |
| `fifo_ok` | cited by name (R1) | propext | `b41e3932da8e5542b352839598b9de3bbfae7c1eee93d897b0de01fa7db0ed1d` | `a6fb272a4a6143a4878625801b45bb1f08ef076da10442ca0283e2e18257641f` |
| `FnDef` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Frame` | cited by name (R4) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `FrameIn` | cited by name (R1) | none | `6b5df3eed15d08c44706deb685e19568bcf59b0519b078bba0d042e4cefb05d7` | `ad95dd988c462be339718bf8af95807ae6616ef5a550c22f8173c18f6b82d0e2` |
| `full_edges_close_missing_edge_examples` | R3 positive control | propext | `6ce7a7dd451ddee5e1a7ecd1362f5760e3f640c9bfc42bf13e85cbfd2878bf7a` | `2b92de2cccae5249a3953535733a7cd47e1a8f191329baf542e8344826c88338` |
| `generic_verified_right_at_conforming_impl` | cited by name (R6) | propext | `b704ac1601dd1bead43eec771556cbb4d63ed0e405a2edcc0aaa4efe66be67e4` | `8583a2f89d6f743ab21177f7538d6fed4c80b2f152ed16997f1fe614aa66d111` |
| `generic_verified_wrong_at_nonconforming_impl` | cited by name (R5); R6 counterexample (hI) | propext | `326ba593aa3412617d9a8f372726fecb6d4debb860badf635c9b299a79f9b81e` | `b8bc905ceee3f6298d01af0fa9415b9f60fec98694591423cf1946a9717ec654` |
| `GenericVerified` | cited by name (R1) | propext | `8148dca447fec1740d5794c4ed72cb10a6045cc096bfd154a4806d4db88976d8` | `87d3f6cb0efa57fb743d5fd659f5466d675bedbb2b72577ae831c26226b00238` |
| `genericVerified_neg_example` | cited by name (R1) | Quot.sound, propext | `a9c32470ba22edc589cf0858e24eedef838dc8de6c6847d61e2f7ef0eac9e6ed` | `7b789dde19e43a49e5c566ad8d901d079978a0a490b741371c51d5c2b70d54d2` |
| `glue_pair_unwind_drops_remaining_field_example` | cited by name (R1) | propext | `787619819505e626ad1f1ad3934d551a04ae636b3af7978ac34fc49e00e54064` | `210d024178f2d11138adfd575a0624a434c48a8433c4b25401a97092a512a889` |
| `glueKey4a` | cited by name (R1) | none | `3fe92497a7942c3a0cf240407feced10e3a10255febeba811f1f85d67c0339f6` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `glueSrc` | cited by name (R1) | propext | `1a31aa288f5437ef781edfc7979cf1100d81b7c2bff592c9e2653a3bc9b3d289` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `glueSrc_neg_example` | cited by name (R1) | propext | `74be267d2ba5bb9f6efb9233e60050c7454231ba691b253edcad9daf36ede390` | `5ec21e0f9b88c1451c5ebd4391676331c055d213354aa76ad58433e819f3d403` |
| `glueSrc_pos_example` | cited by name (R1) | propext | `208e1f73e7d3ca5cb132110714da5b201107ee5e921637cd005c527a934fefc3` | `5ec21e0f9b88c1451c5ebd4391676331c055d213354aa76ad58433e819f3d403` |
| `grows_examples` | cited by name (R1) | propext | `56492f06ba8e376945f99303dbe0f90453ca837c57b6935f83c3c19c72fac08b` | `97c30a21f3ae85fec0302ab8377c716832fd20274cba273fc4c4cf5aca59866e` |
| `ImplEntry` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `implLookup` | cited by name (R1) | none | `8a8ad1ab9b729067930db3c4c118e415d35c0941e458f952153a16c231b01b2b` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `ImplsConform` | cited by name (R5) | propext | `0a1e62bd027ed29f8eefeb02fe050b2a518c540accd75f3d15848565061f78e5` | `87d3f6cb0efa57fb743d5fd659f5466d675bedbb2b72577ae831c26226b00238` |
| `inadmissible_first_scheduler_breaks_order_independence` | R7 counterexample (hs1) | propext | `272b15df0bb8550de4c70e93c1b86cc4eb28cf29459167e9d6daf2eba60ca38b` | `c34fd11f0d232a58e72ea7f98ec82a53c51be0d45043a0f5d44ec3416664650b` |
| `inadmissible_on_demand_scheduler_breaks_precomputed_equality` | R10 counterexample (hs1) | Quot.sound, propext | `f78e8b436efe28cc2e8228adcd63345531585eaf3021fa24f28e4c0b127ef947` | `e3365633f6e9ea0074aa37c840d0f5ff9ecb346cbb7dd66ab5b0318ff92aa047` |
| `inadmissible_scheduler_breaks_precomputed_equality` | R10 counterexample (hs2) | Quot.sound, propext | `8ebf465a05f9f6163260f4d9ae918bf6094a6448fdd56c803ade10c480443926` | `e3365633f6e9ea0074aa37c840d0f5ff9ecb346cbb7dd66ab5b0318ff92aa047` |
| `inadmissible_scheduler_breaks_termination` | R9 counterexample (hs) | Quot.sound, propext | `095a2bb52e4b912f301aa6e59b89f5e606918e6d3de75fa3eb837c212addbf3e` | `f008f8905eee365b25485203d404327deafacb371ffd0fdce8e36cd5ab6a6f60` |
| `inadmissible_scheduler_misses_keys` | R7 counterexample (hs) | propext | `3dfe3aee9bb32555552b0959cfab558bcd038af72599202d37afab6c13608e88` | `a619c77e4aa4ffdc9ee4df611f2e75153061182e561b6edec1326fb5f13f19a5` |
| `inadmissible_second_scheduler_breaks_order_independence` | R7 counterexample (hs2) | propext | `62b94a948fd534750e2fa541f4a70ff7625469b4f995dec72b64184a5c637488` | `c34fd11f0d232a58e72ea7f98ec82a53c51be0d45043a0f5d44ec3416664650b` |
| `InstDefined` | cited by name (R1) | propext | `8034a89d1d726daa217cf1c2565dafca27bbc3cc4b39e84a13cb7482cd221808` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `instDefined_examples` | cited by name (R1) | propext | `8e9c17b982b2d81836d5ecba01386a6d936f90f7123de12b3e0c576bd94ae83b` | `bb1ad7710d05b96bc26f64b1376d804de00e46be533756c0e0ffaf0fdfca1cdb` |
| `instRefs` | cited by name (R1) | propext | `fe96e2e125f3c5eaa0725b4af0de55e1c7f41b12d237d0d59d966be13333b096` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `isShim_neg_example` | cited by name (R1) | propext | `f5a952181c8fff34d766a08a7d28622950f8494be3321e62e509578e92fb0f60` | `05e2eb30cf3fddc4394f44e4cc445f636915cb101f30fd553368e78062141d24` |
| `isShim_pos_example` | cited by name (R1) | propext | `db111ba30538db0953330f994477e1721e307d9a8b75494c7481869264ba6656` | `05e2eb30cf3fddc4394f44e4cc445f636915cb101f30fd553368e78062141d24` |
| `Key` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Key.isImpl` | cited by name (R1) | propext | `52a989f5aa15bd74e0b3d58142c8b3cc93248c3035e7f8a7857fe5437e31be1b` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `Key.isShim` | cited by name (R1) | propext | `52a989f5aa15bd74e0b3d58142c8b3cc93248c3035e7f8a7857fe5437e31be1b` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `Key.norm` | cited by name (R1) | propext | `e7682e345c76f64992e05a73422818bd12ffaed8cd0215623050b79f2bc54ee0` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Key.subst` | cited by name (R1) | propext | `3f68d20e3076c4dca2db2f4663f9a699fe863202be625a55a6b1ff50742b4be2` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `ladder` | cited by name (R4) | none | `1621bd96aee7d5cf0ba0c29beabb8e7c4033857840e1c4d6a925279f4e280d6f` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `ladder_bodyEquiv_cloneAgg` | cited by name (R1) | propext | `066b77d872b1fa8a43b1234a44976994a8f17f11f81db5d421b10d626f470a13` | `8b8168c208d3d0e3783ba91572e1834f96cd99194646fee7f67b37c9ae154d29` |
| `ladder_cloneAgg_three_fields_reverse_cleanup_example` | R4 non-vacuity | propext | `67058ed23dc032d81f1ea7982c6f21b0a7a6e68d1727f22566b40c3f6a485402` | `7c2c0fb595525174664bec8da6212f340b5bfec8a6fb4fc3491a3612101beaa6` |
| `ladder_cloneAgg_unwind_and_abort_examples` | R4 non-vacuity | propext | `0755f045c60c3ea6eaeade42b8c34c1c18aad0a036ec0f4e6a52582f96c5e4f2` | `c225912b64e13e7bab2d3a56d977e3863595a283d998c400bccf9b36bc075860` |
| `ladder_drop_refs_missing_break_closure` | cited by name (R4) | propext | `65e1798c3e6cacec37d73621a121aa5102561efd4535469f28730bb9d53139db` | `da7de13a4dd2b37371a2e83b3c26c5dba52061795dc0cd778cbc99c7196bb895` |
| `ladder_exec_eq_cloneAgg` | R4 result | propext | `8ad776cdfb8e7e4ff03d01aaaba82cb8d596baf1ba5e7dd385fbb41513f093be` | `621ad75f30ac97b1c300d47e2d441b2f2287bf7ffa811aa25d2306f007a08459` |
| `ladder_post` | cited by name (R4) | propext | `e614cea7ecf7b5bb70cc9caffc462b9d843c8686abcd2c3a94188100b86d7099` | `0dee3092ab359e1b4c91f07df0d328323af398934ac8bdce5feacbd5df15c553` |
| `ladder_shape_example` | cited by name (R1) | none | `c19b881b4b5e8a8fcf97499add5b151ba505d7bd48f03f3a678efa755ee0cc68` | `531d34b7753ad65f8dc06da5e06d9b7252a0401f6b3ede245ba37fc29247cb53` |
| `ladderNoCleanup` | cited by name (R1) | none | `1621bd96aee7d5cf0ba0c29beabb8e7c4033857840e1c4d6a925279f4e280d6f` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `ladderNoCleanup_ne_cloneAgg` | cited by name (R4) | propext | `6a64c25297b63c2be2ce48301c6eb6d1605221940983e76c0eeba7ee7cd0b199` | `eea851174bc05edb9012a1810b333fc9a3e2ff8a4ab9153e657a640dfd98ef28` |
| `lifo` | cited by name (R1) | none | `c73c6a5b9c65fc9829c121e08d9ef5929496178d238d526d5df638adc0866e85` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `lifo_ok` | cited by name (R1) | propext | `42de97e2e8a12143b206f59ebc2523a773ac300a3e30b1cb99d43c63f96ec5a8` | `93a1025b48b3e0e8af9a8a76faef13be1a12c1f96577028710e17a48a642a8a9` |
| `linkUnits` | cited by name (R11) | propext | `6590b3de5d0b292dccc432a488cff34f31dcac338bc98b29ee065f4d2b663595` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `linkUnits_eq_tableM_of_deterministic` | R11 result | Classical.choice, Quot.sound, propext | `1aafc6a7f9368f2738c89504d2d815990629425d42477c58d5ab8cdc2328f912` | `a01713e26025f637f488b0fadb3a25fc5dc5d801778accd2a1e5f338c873201a` |
| `MeetsAt` | cited by name (R1) | propext | `a383ddccc20d11946586e7a4fc812294009a438e311c159d5a585bd3042f7137` | `d9c608ed8898ceaf748a258f652c5413a3e261ad67f555ab402de9429a9e1848` |
| `meetsAt_examples` | cited by name (R1) | propext | `d66c3bb24f53eccfb58f17aee2bcf23e238d48624b78a0ff5077740c1587969c` | `ea25234c18165e366c53a402d61af18d9a5647666e75b9e9d620ec8cd3743c79` |
| `meetsAt_tableM_iff_srcDef_of_adequacy` | cited by name (R6) | Classical.choice, Quot.sound, propext | `174fd341364b759d41effeaf67d4419ffc6f6980c5460ae2b6e8616d306a2555` | `ca1dc7bb1c90c6f015fb2f9c8934d913986ea87483359b3cc4355d9235785d00` |
| `meetsAt_tableM_iff_srcDef_of_closed` | cited by name (R6) | Classical.choice, Quot.sound, propext | `555f5e345f1d4a317f1979c98c8872caca1adb304e08854035af6581a071aca7` | `3a76a8f67a841b8c612db38d4668e1d4ff90fe1ea24fb22ea9d9b65f24c94825` |
| `MonoCfg` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `natLookup` | cited by name (R1) | none | `a79f081cf96e765b9e8b827054482bb9451fed9626bdddb6c7b42342d374669d` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `no_source_only_verdict_correct_for_every_synthesizer` | R5 result | propext | `734d44a960c6e4fe908287e2853af668c06d7a65c20be67c65d532ed2b5dab17` | `fc6cdb3cdf8d8282778a22746768f9da3151cd660bdd806c972ab9febc41593d` |
| `noncanonical_key_breaks_canonicalRefs` | R12 counterexample (h3a) | propext | `53e8db91777ca27c23bdd025f1ef63bf6804060d550c925fd091c15e2ff1cd9b` | `bc8b129d2b6e3e0036d80be51ecd4e788b431f45ee861dac95071fe0e2c150bd` |
| `noncanonical_key_breaks_source_transfer` | R6 counterexample (h3a) | Quot.sound, propext | `cf56dd3290a7847382362c77e99df3499a9d897befd7c509fa6e1b64c8bd1615` | `72fb76dd7d29352059cf27f3de86885468e4fa50ee5f9d91926ff987544240b7` |
| `noncanonical_refs_break_closure` | R1 counterexample (h3b); R2 counterexample (h3b); R12 result; R12 counterexample (hA) | Quot.sound, propext | `bddbd598289ab177c35a276652b9c9880492743a6e62b4f456062f64b367020c` | `603154688722f25600b17132d26a1ca1bd11989eb6df51b24133600de67f812d` |
| `noncanonical_root_breaks_adequacy` | R2 counterexample (h3a) | Quot.sound, propext | `fac5f41959e9810dfd86712cc55c41649b12d8ec8f0e49e00e1050796bbf8d64` | `488e9884e7ccea5c23ad2f58beda0f24ea58e90f24ef487dca8dff09be6c4af0` |
| `nonclosed_target_breaks_source_transfer` | R6 counterexample (hC) | Quot.sound, propext | `756c0eb6a035230ff0fc12ca507c9c21303662a7c38ec0fb688c2fcd47f0fde3` | `6d5a94284169152a6366dc9bc71f790cff6b1da8e76cfee4f27c049da4565051` |
| `nonclosed_target_breaks_spec_transfer` | R6 counterexample (hC) | propext | `8dbc1e9dabf0b3475ac1b31cdcd0cde0abae9c73e3fd90245f263d04d92f01e4` | `7f4e31993ee88e50f9790d5ecf943a92466035bcba3aaa37fa17a53c41284cc2` |
| `nonconforming_impl_breaks_source_transfer` | R6 counterexample (hI) | Quot.sound, propext | `b548009bdd57f7dc0a3c3e5f3d91fcc6053b714a60eee681930a61f3be00b0eb` | `91d05bee6c904ce08adcd107d0b86c954d45a505dec84e7ad4524995a4a14654` |
| `nondeterministic_units_break_link_equality` | R11 counterexample (hdet) | Classical.choice, Quot.sound, propext | `12ae861230320f7a922e37761418bd891513cb743e96f5c1bcc6b61cae026855` | `5e130f1cfe63dabaec1bdfcac2ae7f2082fbe0ae2418432896c92398e7ae6b37` |
| `nonnormal_assoc_breaks_termination` | R9 counterexample (hassoc) | Quot.sound, propext | `774048ae1be6c9f05e39d816aa38af5224324ed0d9544d7eee7bfaae54b0626a` | `dc0d8c017182fb2311630d5396ba399b528c664f4e5b72e310a5baf842655917` |
| `norm_neg_example` | cited by name (R1) | propext | `cae8185e3340a52c60664cabc11005cea565474508c74595c77e6b6a60fd57d3` | `3b6a40ae6b1aa122c01a2cac37298cf0dee29c30d5eabd435616f2af3dd7c717` |
| `norm_pos_example` | cited by name (R1) | propext | `3630f5b9c335765028870399e7a339b75a08fbc38377752630def8c3f27ca7bc` | `3b6a40ae6b1aa122c01a2cac37298cf0dee29c30d5eabd435616f2af3dd7c717` |
| `operand_edges_missing_break_closure` | cited by name (R1); R3 result | Quot.sound, propext | `f9f870a5675e70cc6430180bf1a6577af08259df88286684133ecdd1f80cdc2e` | `38b3a554e2989e74ff3bb4e04f925ac6032ed85c7e25dd8966e2279d752f8295` |
| `OptEquiv` | cited by name (R1) | propext | `23525aeeff893d91753ab9c6c51aef4f2766289c0dc14d27c7ac8b4b76d5a5c9` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `P2a` | cited by name (R10) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P2b` | cited by name (R3) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P2c` | cited by name (R3) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P2d` | cited by name (R3) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P3` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P3abort` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P3three` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P4a` | cited by name (R5) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P4a_std_meets_specs` | R5 non-vacuity; R6 non-vacuity | propext | `116a25ddadc99259d449b3b68178a3d5e00c8d806840b4f4ce6f12431fb46815` | `9ef29485e0df5698bbbe37d6cbcf42c115f423975397084df7bd73d19829bf63` |
| `P4a_std_meets_specs_in_source_semantics` | R6 non-vacuity | Classical.choice, Quot.sound, propext | `b795acd6018292f87393543e9f61442bf08e9534645ede45e7acd233c3f49b9c` | `129b31a1d48cff1a436e6d9d0165ddec37dfef3064235d7d2642e21b858f0f0b` |
| `P4b` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P4bad` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P5` | cited by name (R8) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P5flat` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P5flat_collects` | R8 positive control | propext | `89ab8c466a8e20e680d46971feba62f5c01c23c5867b538f177840d4704909bf` | `2a89354ff54fa447f840000395effef9869ce13d178254097a0bae3db783cb31` |
| `P5mut` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P5ok` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P5ok_rankCheck_and_collects` | R9 non-vacuity | propext | `322955f5c6be2b06a8bb3f99bfda220216e3274e136d5e855672e45e8cb13c21` | `3919837c5988c560746d1131e42409aba019b476f643f7a31f0a27030738cb8e` |
| `P6` | cited by name (R12) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P6chain` | cited by name (R12) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P7a` | cited by name (R13) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P7b` | cited by name (R14) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `P9assoc` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Pall` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Pall_all_hypotheses_hold` | R1 non-vacuity; R2 non-vacuity | Quot.sound, propext | `03d16b5a91ba1af00b5efbb38e944cf5fb6487494489a439cc9a8330da97f212` | `e8c3ac7d977ff8579a19a99c66a1dbcf3112876548e8e80d9c339ed25852ea81` |
| `partial_synth_breaks_closure` | R1 counterexample (h2t) | propext | `01a4c0e757a96410e018326bdba0fee36ed8f6401c33d4c604e21f64bea43c94` | `9d379d0275de4ca864a939100f9d382364858d636826ed9ad0599ec4a71e9f1c` |
| `PdeadUndef` | cited by name (R2) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `PdropAbort` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `PdropUnwind` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Pempty` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `per_crate_collection_has_holes` | R14 result | Classical.choice, Quot.sound, propext | `51b48ba01c80d3cca11b539131c6f1c61bf837015a87e19e78475cdf9ba2b16b` | `d05b444a7edfc8ec787e6dd589e217eb901b7939506f158d4de7da99d64e6186` |
| `Pnc` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Pnc0` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `PncMeth` | cited by name (R6) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `polyrec_collector_diverges` | R8 result | Quot.sound, propext | `43c012fa276bdcc433c49af813e1093ec8e11880a2535c3a31cef5b17e30bc82` | `628146d4b04b8a4b4f3a37aa038dd4410a54ff348ad7bf9af9f86b766668de86` |
| `polyrec_fails_rankCheck_and_diverges` | R8 non-vacuity (hs); R9 counterexample (hrank) | Quot.sound, propext | `44b4d58f2d20cc99de8739f8faab849b14e4086ba5078e3f939a4897c8ca20b3` | `f531c6b4cacfae5c26368578325b50c0aeb6786915dbc64b7799a7ee33616444` |
| `polyrec_inadmissible_scheduler_terminates` | R8 counterexample (hs) | propext | `ae265e0457235336318de8beb2bbeb39bf71e25b32729c97f99516e321e56b19` | `fe31aed878fdcd7d92775996d956c7460f49837913b23764058764a642869c55` |
| `polyrec_instances_reachable` | R8 result | Quot.sound, propext | `81972747d1847ee3dd9f37e9c3f7245fc78886215b37b8ff92bb3abd31f235af` | `3b6fc64c1a4aa803b227cd9354d53ed9c226b396f70bece650d102829c8f4d4f` |
| `polyrec_runs_finite` | R8 result | Quot.sound, propext | `ffc72e8d15f8e48ab48be016fe9b7c30779380a175c74955b0f8e70bb31b5a8b` | `325debfc2c7ea6d93ac7396d0436bb0508e4ebf4fd4a560b789f125d4612e9c1` |
| `postClean` | cited by name (R1) | propext | `1efeb078abdfaf854ea10b28373bbf21a5785116d5c94722fd7919107267be33` | `45a76f508cc81257437fbebdd67a9e8ab6cf2caecd2a80118537183521f556ce` |
| `pre2a` | cited by name (R10) | none | `078229ad2765c97d3dd50a97e5b4728b543a2d68731b3930eae9f02f6e127229` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `preCfg` | cited by name (R10) | none | `8cf9034dbb3c10adae54d9d21b6ebda3562e8f410ea287acea65b607045943ad` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `precomputed_and_on_demand_synthesis_same_target` | R10 result | Quot.sound, propext | `2b840112792af739178ac20e2257e6f9997cdcca9d20e5d316e41dfc36f82e01` | `a23f2fcb4f190838bcab0b29dfe222f1197e8ecaaeb1a2d5d0e932091541149d` |
| `precomputed_example` | R10 non-vacuity | Quot.sound, propext | `d41dc3aba8c888fdaf863daa8967d69490b058eafe738c4dc413481d5522d2fd` | `65c5069ddef226d890dcc23793ae787645ec9fc3830ac83febb7e91476608854` |
| `Program` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Program.sig` | cited by name (R1) | propext | `7bf21425cb4de314fd6de33054179b8def260ba705f9c5de2ee1324685f96ed6` | `f3f91939ec11a165a289e46493334b13f70b4fbd1cb428ee7b9288dac923e987` |
| `Pundef` | cited by name (R1) | none | `edf62cf887660174b1d3009f7403d3b6e8bb1de75f86e2ce0afc3694cf9d1594` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Q2c` | cited by name (R1) | none | `debc6fe1f4fa7c8722cb736ca2bdef9bffcd8773029edfcf5992568ea1eb26e8` | `cb263d9fd9f216cbb55a67f3c53a40c2ada076a8e3358b7344a9a1c29b2b24e8` |
| `Q4a` | cited by name (R5) | propext | `debc6fe1f4fa7c8722cb736ca2bdef9bffcd8773029edfcf5992568ea1eb26e8` | `cb263d9fd9f216cbb55a67f3c53a40c2ada076a8e3358b7344a9a1c29b2b24e8` |
| `Q4aRev` | cited by name (R6) | propext | `debc6fe1f4fa7c8722cb736ca2bdef9bffcd8773029edfcf5992568ea1eb26e8` | `cb263d9fd9f216cbb55a67f3c53a40c2ada076a8e3358b7344a9a1c29b2b24e8` |
| `Q4b` | cited by name (R1) | none | `debc6fe1f4fa7c8722cb736ca2bdef9bffcd8773029edfcf5992568ea1eb26e8` | `cb263d9fd9f216cbb55a67f3c53a40c2ada076a8e3358b7344a9a1c29b2b24e8` |
| `rank5ok` | cited by name (R1) | none | `e2aa04b5dbcde90dac959502e8d8fa0046c9d754e461bf6e56e3479a43180ccd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `rankCheck` | cited by name (R1) | propext | `2995c1b782adca43f9b619ef945b1e23b63edcdbd1a7d36e6a9d1c131abd5823` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `rankCheck_examples` | cited by name (R1) | Quot.sound, propext | `461c46cdd07bc3457b45e6ff88f19461aad1ef402ff1787851909e87644c6f51` | `5abc5ef8c845abdcc584482a6d447e3fa8745704abc29293be8c59047b8a6bbc` |
| `rankCheck_not_necessary` | cited by name (R9) | Quot.sound, propext | `adefda90fc3e2ac549368438d1438a8e7b7e034139c59be2002ca2c3f88fa396` | `ebee32c0bdaf91c7125782cf8e7f1b41421aaa1b16d3de5050395752322c32bf` |
| `Reach` | cited by name (R7) | none | `2e2efb9f2a83a76c3f94689ddfa823f257d7869d9c3532c570f2259042d653d8` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `reach_congr` | cited by name (R10) | none | `b7cabc6418830d1f34392f14647ead4f4c74bc29a0d9c379cf43253e3e8a1129` | `f773226bf4c50428df0669c2f49f44e10e7b178d7b2601556338932359355c7f` |
| `reach_neg_example` | cited by name (R1) | Quot.sound, propext | `56319708efe394eb1bf9622fc8084078a9e054b6a7cfad0b1ee78640f346ece6` | `999fc6902faa60a3332c4392c9bcc7d190cd599cee76ef958e8d8b75bd8cd43d` |
| `reach_pos_example` | cited by name (R1) | Quot.sound, propext | `3646d1ff1f800180c0eaf6ed26e038fae180b7e0e300220270d6df23d6464af1` | `999fc6902faa60a3332c4392c9bcc7d190cd599cee76ef958e8d8b75bd8cd43d` |
| `reach_subset_of_rootsIn_edgesIn` | cited by name (R13) | none | `63c445deb40021db98c1d8483270a7f362286dd19ef2cfeddec78bd9e13a9f10` | `5b9e5440aaf7eaf3364f54353aa88cc3e21c317d39883e4ca697231ea790f12c` |
| `refs` | cited by name (R1) | propext | `aaf9cea04274d993f77958d950918a97e6663cc946ea59c85fc90d09ce8ef0df` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `refs_neg_example` | cited by name (R1) | propext | `3d47d12d5dc01ac68bc3cc3f041451314604beb9f6384f84d9fec88079cbf028` | `1f79dc8993e2b163be989c7ee74b5f8eab57672c2c577f0553c315210b8aef53` |
| `refs_norm_canonical` | cited by name (R12) | Quot.sound, propext | `499d11576d090badfa22f3defb76db9f9967efb41fb6dd4f70722e0b06de1489` | `58f0bfb150711080095cbcc29f2447a5b76cda40a9d81f7f25291a6fb5b53e76` |
| `refs_pos_example` | cited by name (R1) | propext | `6a64307262dd6f57f555ea13c301cf533200f8b655a0e2104efeb14ba953de92` | `b83bf0c9ddd748ff6ea3334339014bd662c803a365e5d370ef95865df3680a57` |
| `refsNoCleanup` | cited by name (R3) | propext | `aaf9cea04274d993f77958d950918a97e6663cc946ea59c85fc90d09ce8ef0df` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `refsNoOperand` | cited by name (R3) | propext | `aaf9cea04274d993f77958d950918a97e6663cc946ea59c85fc90d09ce8ef0df` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `refsNoReifyShim` | cited by name (R3) | propext | `aaf9cea04274d993f77958d950918a97e6663cc946ea59c85fc90d09ce8ef0df` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `refsNoVtable` | cited by name (R3) | propext | `aaf9cea04274d993f77958d950918a97e6663cc946ea59c85fc90d09ce8ef0df` | `1875f8b993d3348a0a43d64cb8cd61b9b4edbe214f979a178f3486fead1eb63f` |
| `reify_shim_edges_missing_break_closure` | cited by name (R1); R3 result | Quot.sound, propext | `116c5b106003c3b7b9787ba1504e2626b5800ae3baeae1d8b5c3668001537a6b` | `3e06b52fe7547554fbcc15e2bd29acf0f9f7bd41c74eee7476af64cb805b187e` |
| `reifyKey` | cited by name (R1) | none | `917ffed040dafa8b112f3515177021b29df7ae570d007839294f6d2c4ae53ccb` | `ffd924f7dfbb7c18538c9d487f2aeeff7aa0e376f8da0952a86ec46f5de23d1d` |
| `reifyKey_examples` | cited by name (R1) | propext | `cba0a9f4f6378c3f3066e770e8649f54ad937d60b78ac0d9e37f0cc6b788dabf` | `6671f5d8a1c9b31cafd7889e1b441d76472a23b1d6131cfed0f380e38ae12623` |
| `Res` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `root_outside_target_breaks_adequacy` | R2 counterexample (hR) | Quot.sound, propext | `77b09abe0620d79400d5889bd82d3e54061d56df922ad34c9c30952aabd4d06f` | `e3c7282cb94345efa9b8842294ef23f6f69ce150f2186aec4c4dc9df4aedd279` |
| `RootsIn` | cited by name (R2) | none | `3539f9aadbfeb2d7b925b80862dee3e5d6675a534bd9a309e2858a6739331c22` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `rootsIn_examples` | cited by name (R1) | propext | `26e14e8301e0334eb1a781a7130d5d9d6e9d1dbf933dac2f837be98722403334` | `7a668863eab2c37d1fb3783c8373e9dd6d1610ccd36843b864176e2dba77bada` |
| `runKey` | cited by name (R1) | propext | `522ebd41c6556c714b54cef82523c9b7cfa01087ec867d371e9f1a25b39fc3a3` | `d6e1678154209c04a1614b4f6b1a17aafe562111db473f5bbf5a941a33d01e20` |
| `runM` | cited by name (R2) | propext | `715c66c3be96e07c94e0bc00a69e8296a42a7b5759ef9214af0765793eb632dc` | `26fe8cbef954da646dc55fad3d4e5e8e57a42fbf296042b65f803c1547e095ff` |
| `runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical` | R2 result | Classical.choice, Quot.sound, propext | `6137fe258b72e3b1604332e3f17c1622d4f85a295f42f807a9453d3d7a55f1b1` | `51693dc2e22b3d00563a747c2edb4e069c799c4921af6bc27960acc4e8a7d645` |
| `runS` | cited by name (R2) | propext | `0379a11e34ff8c1cb14cdaa01d2473a48e7088c7143f94488c00663290ba1c93` | `5910dc96cd0cb880a5beee908d188abbc22504e71407d25d6b5f075951a16dda` |
| `SatOut` | cited by name (R1) | none | `93b2b47cd1bbde94340114034444693ebd4f3d753b986938cd29a4c37bd946fa` | `cb263d9fd9f216cbb55a67f3c53a40c2ada076a8e3358b7344a9a1c29b2b24e8` |
| `schedBump` | cited by name (R1) | propext | `20e3113fdcd6d4a366dd38d2fef446b6583c07d7b3cbee212b02991266a1b67f` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `schedDrop` | cited by name (R1) | none | `11157a9fac2150d81aa14144e96edb0939b194adb592ac6a7af1e583ed9139d3` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `SchedOK` | cited by name (R7) | none | `fddf8bb3444361bb225785dcda68f26027d24db6520261a96465bf8fc5ab9145` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `schedOK_neg_example` | cited by name (R1) | propext | `22a9465f2c5e7d5180440bcc0f1b1ae63ca23d4efc79293952f789ddb2db7025` | `d74faba0109f8142b117751f063ad11a6cbb0aa1cc3e28ed6a26a6767d519da3` |
| `schedOK_pos_example` | cited by name (R1) | propext | `966d81a760d70a4b4e3f7a9583ba61023d2867dbb1b0b700c5903ee81d1d7ff7` | `e750cebf691afa1fb14e688de71c31f2163565f06289aea1eab34dd3ff7edfa1` |
| `Sig` | cited by name (R4) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `SlotVal` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source_defs_verified_yet_program_violates_spec_under_reverse_glue` | R5 result; R6 counterexample (hS) | propext | `e75b01aca166a31a6586bc46ed98440a79921cd1e1401f50489dccaa125070e9` | `ed14e7ff98903d2e21fafd48349e66d037623158bd1a9b0e2d8ee4a3a3ea2d44` |
| `source_transfer_without_covering_or_edge_closure` | cited by name (R6) | Classical.choice, Quot.sound, propext | `0245c073981013fe22af2b49466f7c4a984de0db2350b4cab43d780dc3e8a72f` | `5cd0f1f74ff2b437e1c0a59878f4223c807c43ebb3686ce0f112650492cdbd3c` |
| `Spec` | cited by name (R1) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `specs_neg_example` | cited by name (R1) | propext | `d7b56d3a235fa21fefe39aadc8a3ce4a63098fac81c9c94640e9a5df898a0435` | `fc18f7f35366cd7de1807c5048d3f3ae4514fc09c739b1a9eb54003bafc1c095` |
| `specs_pos_example` | cited by name (R1) | propext | `c842fbf4986eea97206264be03d21652eeb54ea83486cbf8a7168232f1f71abe` | `bd2b40a6d3a8bdfb636f754ab736b938e26a60633a44599ab86111489d8a4bc2` |
| `srcDef` | cited by name (R1) | propext | `0aeea3ae37c1d6d9d1434fd6545ec50846cbb8cd676c295e63ab49e14b311d37` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `srcDef0` | cited by name (R1) | propext | `3b9683cd0d4c80a7829eca01427c4e44923143d39b9e0fc6d537a6015ea6e403` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `srcDef_neg_example` | cited by name (R1) | propext | `c66560050c3e8d1a15f720098eea2fd13b57bbe19ed9b4fc1dfcefd403226592` | `28fb0d81806cc34d7481965035ca40ff75e2bcee7418689e4587be114714db52` |
| `srcDef_pos_example` | cited by name (R1) | propext | `3f84cd7bc7fe1643330184a3e60a2b71a0df6a81340b2cfd3656c653cd08c926` | `28fb0d81806cc34d7481965035ca40ff75e2bcee7418689e4587be114714db52` |
| `srcVerdict` | cited by name (R1) | Classical.choice, Quot.sound, propext | `961f75e1c3a108e13793f0e0b45bb5da7c70e25be52e6048bb5040644a9f5c2e` | `87d3f6cb0efa57fb743d5fd659f5466d675bedbb2b72577ae831c26226b00238` |
| `srcVerdict_correct_example` | R5 positive control | Classical.choice, Quot.sound, propext | `772420d52065a41c7962ba6ed8425438450996f7878ed194509e2e3f0a269fd4` | `f762e17320051afa4bd9b76f9e8c13c9ebcdd3f01bf67ac4462ba8104fd49cdf` |
| `srcVerdict_correct_of_adequacy` | R5 positive control | Classical.choice, Quot.sound, propext | `67f97b896997fc40c4f5a1d3991d490fdd1366fd126a5a13e093b2b5872a40e3` | `50caffb842ca0880229938a4be621b9cde90b2b18bd756a407e49f9a4e297bb0` |
| `St` | cited by name (R2) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `st0` | cited by name (R3) | none | `63d846359ef847611b69a5163a211804c71afc02275e490ec542a6c059687e9c` | `f439af5ad9d56e4abf963c2c0faa9e6dab2b6aa64acc01767503c138944b0c7a` |
| `stale_precomputed_table_changes_target` | R10 counterexample (hpre) | Quot.sound, propext | `c46e5d1d4df11fa03751f81201547fbdb80794bb1ff83a59f37c0107c6b4aa7d` | `8b03f36f28efd821b942c7d1faf24a45f2d0e1f89bf5020b7f2a92bfd256beef` |
| `stdCfg` | cited by name (R5) | propext | `51418056cccb4103ae134769ec30303a7841d625a4a14fc894858b4b98d43593` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `Stmt` | cited by name (R10) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Stmt.norm` | cited by name (R1) | propext | `769e4a2619690c833055823dce39759f214594c0fcddcf8f6884f2f3b7f51a4a` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `Stmt.subst` | cited by name (R1) | propext | `bcfeabcc054cf08921462095234d93fee8137a5b02261f7a4855e6a9af29c4f7` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `synth_disagreement_breaks_adequacy` | R2 counterexample (h2) | propext | `5d8b3752b5137648747a02329ac3ce97eea8edbdbd780693c87de5532442256e` | `dd375e8fd46b5579269ea6982eaca3db029d77d5340a93ee6b6977daa44f98eb` |
| `synth_disagreement_breaks_source_transfer` | R6 counterexample (h2) | propext | `ca764a35c9957a343a87d5ade75ffdd9fd2ebd1fcedd1eb9c35c9778e9183082` | `ec62bfaab7e4675469cd2217f4689236fc10ad2b7012e99395ee5cd88efecf9b` |
| `SynthAgrees` | cited by name (R2) | propext | `c672f7922f48f62c971c508a75cd7c2f4aea6b5ad09a8383a1ba6d5ec97b40bc` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `synthAgrees_neg_example` | cited by name (R1) | propext | `b35969d1e66c0cdb2bf6ce25b389c605f31f178bbc38a621b774491cd8bab468` | `338f318791b611c7398de91560efc620e776edc713fe3359f84b404a6a3040d1` |
| `synthAgrees_pos_example` | cited by name (R1) | Quot.sound, propext | `2196e071e0233f1a0e61a3e42ad37ca64f815c3a6885d43bfdfd8aaf13c521cb` | `552eab73251202af31af9cd95f72048df5a712878c0cb0a2abf14bf674ceaaf6` |
| `synthRev` | cited by name (R5) | propext | `3b9683cd0d4c80a7829eca01427c4e44923143d39b9e0fc6d537a6015ea6e403` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `synthStd` | cited by name (R1) | propext | `3b9683cd0d4c80a7829eca01427c4e44923143d39b9e0fc6d537a6015ea6e403` | `d01ad674d40190cb7d0fcec67d83b004bba3f182844f7565a945d626b2604335` |
| `synthStd_agrees` | cited by name (R4) | Quot.sound, propext | `0cad9a58e9789ece40f7ea450d55c75e4f3436ee7dc632b653b5a598cd60e2ea` | `dd7e96b084cac516f7f58e8809dd7b22035ebdfd6fa40247975bb11fce69be50` |
| `synthStd_neg_example` | cited by name (R1) | propext | `da354391d90ef2090f45bff6ce1081d3fa8146f465c570279a681239166152f6` | `6051f9b991dd4591fc152b91ea3f26192d5a1b67d5e3c41348b0e136f6dc7855` |
| `synthStd_optEquiv` | cited by name (R4) | Quot.sound, propext | `c72d9707256d464959604b28c695b54a92095984a122bb19a5f23c3e6e3a969b` | `7cc3b6590ce21dc6c80c815e3850a96a50b27f2e96102a20cc6e62b9e4048d7e` |
| `synthStd_pos_example` | cited by name (R1) | propext | `4d0deb2ee93149c123f4bf1c952c28ed5b2da015227c09da3a2ba9a06aed70be` | `6051f9b991dd4591fc152b91ea3f26192d5a1b67d5e3c41348b0e136f6dc7855` |
| `SynthTotal` | cited by name (R1) | propext | `198cd9471b90a587187a7263b7a703dc3b5d862d13a60aeccb6a93c7932ce8c5` | `0a0d7dab8a127e4a0c72b873cfdec40f3ee6895ffcbf14e4d7f505ac82a50b79` |
| `synthTotal_examples` | cited by name (R1) | propext | `4220478dc685bfcc3aafdedde16b6a3da85b4e21c81d804809e7519b7fb1bef3` | `bcdb4422a9da859f1bfb34a5218148c5ebe40a97fce766853958a9ae540a15ac` |
| `synthTotal_of_synthAgrees` | cited by name (R1) | propext | `d64b3f91e115a808c45d733b51100bb965eeb1ed2ea6317d2228280b98903b67` | `7100a9de0f142241619a44355b99fead226fbd1b69f9162906384ad92f9a484f` |
| `SynthVerified` | cited by name (R5) | propext | `b4362ffd05b485f98169153ae1a750ade997cb2249215ddd70ebac5512e5b587` | `39755b5fe3c1b932bc586ce6d95b48acaa8a2a3be095e6581d6944659ae2c2d0` |
| `T2a` | cited by name (R3) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T2b` | cited by name (R3) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T2c` | cited by name (R3) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T2d` | cited by name (R3) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T3` | cited by name (R1) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T4a` | cited by name (R5) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T4b` | cited by name (R1) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T6` | cited by name (R12) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T7a` | cited by name (R13) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `T7b` | cited by name (R14) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `tableM` | cited by name (R6) | propext | `73137e5e9ebcc1acbdb736b14972dd203999cd91e09304fd3d48114a9822fe1d` | `4dd9d2b51ba82d8dbe395eb38925eee76862fb49819894d4e721c334a1af09d6` |
| `Tall` | cited by name (R1) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `target_not_edge_closed_breaks_closure_and_adequacy` | R1 counterexample (hE); R2 counterexample (hE) | Quot.sound, propext | `44b49c3c6ecc03cda1f87e3ca2ef2e46401ae42beb370a5977cf8dcb79db7d74` | `21ff86bc575d4d667ce0359c4a0deb2463f628fb8b47c8386167d20959660f37` |
| `TdeadUndef` | cited by name (R2) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `TncMeth` | cited by name (R6) | none | `740ae5aad10318b929d1f2dfafa0549c21e044c2d366b64aee3b4bde0b02f2be` | `5dca7e8e8ed4b7849423ea2aa2186222c08b25c2f3eda2c9ec1faad10ea41ef1` |
| `Ty` | cited by name (R4) | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ty.grows` | cited by name (R9) | propext | `494c5fe189e7d8356ef25b26f47de0e3088b521c61bd1ee39e69dc2bdce77c67` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `Ty.hasParam` | cited by name (R1) | propext | `494c5fe189e7d8356ef25b26f47de0e3088b521c61bd1ee39e69dc2bdce77c67` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `Ty.norm` | cited by name (R1) | propext | `ff37ace7eafa647911e88abcb0c07684fcbaccd04870c07c7cb1b1cf9fba01f7` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `Ty.size` | cited by name (R1) | propext | `ace852a07b7ec1ff295efce1b8f3fa9e82aa674d02f4722f19f8be8d217f01c8` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `Ty.subst` | cited by name (R1) | propext | `91ba54225a6bc8d6c283200ff70c987a8df671fe22bce9cea13462d4ccd36ae9` | `6245a778b4ebd8cd338a43be7ed03c0435c72dbc982a16d8ec6dd400c3f08902` |
| `ty_norm_idem_of_assocNormal` | cited by name (R1) | Quot.sound, propext | `cd7ca3cd561b684e3e6eae546d162e6ed45f2e2da0575dda6cf17f5715769054` | `9f91bf1ecfef3b9b6164fe815d02dd104dbea6920c4c3e7af18f68ef7a88f227` |
| `uncovering_units_break_link_equality` | R11 counterexample (hcov) | propext | `8afcd4495532f2201bb662a16e0546ae85e9fbb0e6142d822640f5956fead26c` | `773b0a95062ddd7fcf17b90126a999913882e447cc6d03229805249f6392d9d8` |
| `undefined_instance_breaks_closure` | R1 counterexample (h0) | propext | `49b93cfddd8d1355157457400269faef11935c9e0babe4df167ff1be56cde77b` | `c91e53cdccef069fa10fa41bef5c980739a0ce1357c7539a3e1aeca446742f9e` |
| `unitA` | cited by name (R1) | none | `9671233791f7396fecfe02f34f905887b9156ab62f8c27f06874d8a5764e5270` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `unitB` | cited by name (R1) | none | `9671233791f7396fecfe02f34f905887b9156ab62f8c27f06874d8a5764e5270` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `UnitsCover` | cited by name (R11) | none | `1504c8f735e7a32e5f383e63714833633bfa818ef9f4492e3c1eed46dfc79273` | `55c018287d58b8d4c1bf5e439612cd1d5d571decaeac16b1109955b09bad848c` |
| `unverified_generic_body_breaks_source_transfer` | R6 counterexample (hG) | Quot.sound, propext | `2e32057b9c9e9dd3dce030e9eb751d86f34f895e50758a9ca9255a33414dbf89` | `0a70a08324f3fc0b84a19a50ebd3a4339011a28b2a9959d871ae41051b20f0d7` |
| `unverified_generic_body_breaks_spec_transfer` | R6 counterexample (hG) | Quot.sound, propext | `a080e84ca820925334201d58469a88c319105265ac28cd8eba0af25d4e8a838b` | `ade81b3d4b4375a10e82c0f9272f81bb0f96029f5ec09fb9bbdca4a2861a04c7` |
| `unverified_synth_breaks_source_transfer` | R6 counterexample (hS) | Classical.choice, Quot.sound, propext | `f4f12b49f6bebe0f51b65d517a078ffbfef4a2ca1dceb40fe1a68f8d4f3b3005` | `a0cb3a23e28ab6c27558261587afff2f0fad79e763f2c9a487bb0ded999cfe3f` |
| `VerifiedBody` | cited by name (R1) | propext | `cbb5b01c4abeb57a31c3657b15ba54b939069a3db76b3e09c47488cfd4b715f0` | `d9c608ed8898ceaf748a258f652c5413a3e261ad67f555ab402de9429a9e1848` |
| `verifiedBody_neg_example` | cited by name (R1) | Quot.sound, propext | `ade3cb1449dc6c69e0f402a3c497635ef1d079f29472e5b2372dd5cf23e52944` | `243ae2bcf02566c03faf69142ef2806dee35ecaa562f4a05fc76bbd29dbfb51c` |
| `verifiedBody_pos_example` | cited by name (R1) | propext | `9b837218fc8e5a5e1ad435fb51e8df9c21071743d45fe1a7ff9fb73932729399` | `243ae2bcf02566c03faf69142ef2806dee35ecaa562f4a05fc76bbd29dbfb51c` |
| `vtable_edges_missing_break_closure` | R1 counterexample (h1); R3 result | Quot.sound, propext | `71c5dd0e5cdd9c12579cdc04de8c7305c7d791874ec75f6bca49b4367886ddbb` | `c92589e4da68ddabaff0533c50cbc3a351ed9a48e8fe02b6b6c0f8656f51b12e` |
| `vtEntries` | cited by name (R1) | none | `a22868dd3274074d04c8a27f4cfd1b08a4c68d7aa72d68546172b796dcb5a010` | `ffd924f7dfbb7c18538c9d487f2aeeff7aa0e376f8da0952a86ec46f5de23d1d` |

### Auxiliary declarations cited by name

Every package-local declaration named above, appearing in a quoted statement, or listed in `results.json`, whose statement is not quoted in the preceding sections, quoted verbatim. Theorems are quoted through the end of their signature; definitions in full.

`FrameIn`:

```lean
-- lean/MonoShim/Adequacy.lean:10-14
def FrameIn (U : List Key) (fr : Frame) : Prop :=
  ∀ j v, (j, v) ∈ fr →
    match v with
    | .fn k => k ∈ U
    | .vt es d => (∀ e ∈ es, e.2 ∈ U) ∧ d ∈ U
```

`execS_congr`:

```lean
-- lean/MonoShim/Adequacy.lean:70-73
theorem execS_congr (sig : Sig) (U : List Key) (c1 c2 : Call)
    (hc : ∀ k ∈ U, ∀ st, c1 k st = c2 k st) :
    ∀ (s : Stmt) (fr : Frame) (st : St), (∀ k ∈ refs sig s, k ∈ U) → FrameIn U fr →
      execS sig c1 s fr st = execS sig c2 s fr st ∧ FrameIn U (execS sig c1 s fr st).2.1 := by
```

`Pall`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:17-27
def Pall : Program where
  fns := [⟨false,
      .seq (.unsize 0 (.base 2) 0) (.seq (.callDyn 0 0) (.seq (.mcall 0 0 (.base 2))
        (.seq (.dropDyn 0) (.seq (.reify 1 1 []) (.seq (.callPtr 1) (.seq (.clone .fnPtr)
          (.onUnwind (.clone (.pair (.base 0) (.base 3))) (.drop (.base 0))))))))) ⟩,
    ⟨true, .emit 4⟩]
  methods := [(0, [0])]
  impls := [⟨0, 0, .base 2, .emit 5⟩]
  dropImpls := [(0, .emit 2), (2, .emit 6)]
  cloneImpls := [(0, .emit 1), (3, .panic)]
  assoc := []
```

`Tall`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:29-32
def Tall : List Key :=
  [.userDrop 0, .dropGlue (.base 3), .userClone 3, .userClone 0, .inst 1 [], .userDrop 2,
    .dropGlue (.base 0), .cloneShim (.pair (.base 0) (.base 3)), .cloneShim .fnPtr, .reifyShim 1 [],
    .dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []]
```

`Pall_all_hypotheses_hold`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:38-46
theorem Pall_all_hypotheses_hold :
    collect (edgesM Pall (stdCfg Pall)) fifo [.inst 0 []] 40 = some Tall ∧
    RootsIn [.inst 0 []] Tall ∧ EdgesIn (edgesM Pall (stdCfg Pall)) Tall ∧
    CoversRefs Pall.sig (stdCfg Pall).E ∧ SynthAgrees Pall (stdCfg Pall) Tall ∧
    SynthTotal (stdCfg Pall) Tall ∧ InstDefined Pall Tall ∧
    CanonicalKeys Pall Tall ∧ CanonicalRefs Pall (stdCfg Pall) Tall ∧
    Closed Pall.sig (tableM Pall (stdCfg Pall) Tall) Tall ∧
    runM Pall (stdCfg Pall) Tall 5 (.inst 0 []) st0 = (.unwind, ⟨[5, 5, 6, 4, 1, 2, 2], 0⟩) ∧
    runS Pall 5 (.inst 0 []) st0 = (.unwind, ⟨[5, 5, 6, 4, 1, 2, 2], 0⟩) := by
```

`synth_disagreement_breaks_adequacy`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:52-59
theorem synth_disagreement_breaks_adequacy :
    RootsIn [.inst 0 []] T4a ∧ EdgesIn (edgesM P4a (cfgRev P4a)) T4a ∧
    CoversRefs P4a.sig (cfgRev P4a).E ∧ ¬ SynthAgrees P4a (cfgRev P4a) T4a ∧
    CanonicalKeys P4a T4a ∧ CanonicalRefs P4a (cfgRev P4a) T4a ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P4a (cfgRev P4a) T4a n r st = runS P4a n r st) ∧
    runM P4a (cfgRev P4a) T4a 4 (.inst 0 []) st0 = (.ok, ⟨[20, 10], 0⟩) ∧
    runS P4a 4 (.inst 0 []) st0 = (.ok, ⟨[10, 20], 0⟩) := by
```

`Pnc`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:67-73
def Pnc : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := [(1, .emit 8)]
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]
```

`noncanonical_root_breaks_adequacy`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:77-87
theorem noncanonical_root_breaks_adequacy :
    RootsIn [.dropGlue (.proj 0 (.base 0))] [.dropGlue (.proj 0 (.base 0))] ∧
    EdgesIn (edgesM Pnc (stdCfg Pnc)) [.dropGlue (.proj 0 (.base 0))] ∧
    CoversRefs Pnc.sig (stdCfg Pnc).E ∧ SynthAgrees Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] ∧
    ¬ CanonicalKeys Pnc [.dropGlue (.proj 0 (.base 0))] ∧
    CanonicalRefs Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] ∧
    ¬ (∀ r ∈ [.dropGlue (.proj 0 (.base 0))], ∀ (n : Nat) (st : St),
      runM Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] n r st = runS Pnc n r st) ∧
    runM Pnc (stdCfg Pnc) [.dropGlue (.proj 0 (.base 0))] 3 (.dropGlue (.proj 0 (.base 0))) st0
      = (.link (.dropGlue (.proj 0 (.base 0))), st0) ∧
    runS Pnc 3 (.dropGlue (.proj 0 (.base 0))) st0 = (.ok, ⟨[8], 0⟩) := by
```

`root_outside_target_breaks_adequacy`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:93-99
theorem root_outside_target_breaks_adequacy :
    ¬ RootsIn [.inst 0 []] [] ∧ EdgesIn (edgesM P2c (stdCfg P2c)) [] ∧
    CoversRefs P2c.sig (stdCfg P2c).E ∧ SynthAgrees P2c (stdCfg P2c) [] ∧
    CanonicalKeys P2c [] ∧ CanonicalRefs P2c (stdCfg P2c) [] ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St), runM P2c (stdCfg P2c) [] n r st = runS P2c n r st) ∧
    runM P2c (stdCfg P2c) [] 3 (.inst 0 []) st0 = (.link (.inst 0 []), st0) ∧
    runS P2c 3 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) := by
```

`target_not_edge_closed_breaks_closure_and_adequacy`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:104-113
theorem target_not_edge_closed_breaks_closure_and_adequacy :
    RootsIn [.inst 0 []] [.inst 0 []] ∧ ¬ EdgesIn (edgesM P2c (stdCfg P2c)) [.inst 0 []] ∧
    CoversRefs P2c.sig (stdCfg P2c).E ∧ SynthAgrees P2c (stdCfg P2c) [.inst 0 []] ∧
    SynthTotal (stdCfg P2c) [.inst 0 []] ∧ InstDefined P2c [.inst 0 []] ∧
    CanonicalKeys P2c [.inst 0 []] ∧ CanonicalRefs P2c (stdCfg P2c) [.inst 0 []] ∧
    ¬ Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) [.inst 0 []] ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2c (stdCfg P2c) [.inst 0 []] n r st = runS P2c n r st) ∧
    runM P2c (stdCfg P2c) [.inst 0 []] 3 (.inst 0 []) st0 = (.link (.inst 1 []), st0) ∧
    runS P2c 3 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) := by
```

`Pundef`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:119-125
def Pundef : Program where
  fns := [⟨false, .call 5 []⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`undefined_instance_breaks_closure`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:128-133
theorem undefined_instance_breaks_closure :
    EdgesIn (edgesM Pundef (stdCfg Pundef)) [.inst 5 [], .inst 0 []] ∧
    CoversRefs Pundef.sig (stdCfg Pundef).E ∧ SynthTotal (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    CanonicalRefs Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    ¬ InstDefined Pundef [.inst 5 [], .inst 0 []] ∧
    ¬ Closed Pundef.sig (tableM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []]) [.inst 5 [], .inst 0 []] := by
```

`adequacy_holds_on_nonclosed_target`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:139-152
theorem adequacy_holds_on_nonclosed_target :
    ¬ Closed Pundef.sig (tableM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []])
        [.inst 5 [], .inst 0 []] ∧
    RootsIn [.inst 0 []] [.inst 5 [], .inst 0 []] ∧
    EdgesIn (edgesM Pundef (stdCfg Pundef)) [.inst 5 [], .inst 0 []] ∧
    CoversRefs Pundef.sig (stdCfg Pundef).E ∧
    SynthAgrees Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    CanonicalKeys Pundef [.inst 5 [], .inst 0 []] ∧
    CanonicalRefs Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] ∧
    (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] n r st = runS Pundef n r st) ∧
    runM Pundef (stdCfg Pundef) [.inst 5 [], .inst 0 []] 3 (.inst 0 []) st0
      = (.link (.inst 5 []), st0) ∧
    runS Pundef 3 (.inst 0 []) st0 = (.link (.inst 5 []), st0) := by
```

`cfgNoSynth`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:160
def cfgNoSynth (P : Program) : MonoCfg := ⟨refs P.sig, fun _ => none⟩
```

`partial_synth_breaks_closure`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:164-173
theorem partial_synth_breaks_closure :
    collect (edgesM P2a (cfgNoSynth P2a)) fifo [.inst 0 []] 10 =
      some [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    EdgesIn (edgesM P2a (cfgNoSynth P2a)) [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    CoversRefs P2a.sig (cfgNoSynth P2a).E ∧
    ¬ SynthTotal (cfgNoSynth P2a) [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    CanonicalRefs P2a (cfgNoSynth P2a) [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    InstDefined P2a [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    ¬ Closed P2a.sig (tableM P2a (cfgNoSynth P2a) [.dropGlue (.base 1), .inst 1 [], .inst 0 []])
      [.dropGlue (.base 1), .inst 1 [], .inst 0 []] := by
```

`synthTotal_of_synthAgrees`:

```lean
-- lean/MonoShim/AdequacyTightness.lean:178-180
theorem synthTotal_of_synthAgrees (P : Program) (cfg : MonoCfg) (T : List Key)
    (h2 : SynthAgrees P cfg T) (hdef : ∀ k ∈ T, k.isShim = true → (srcDef0 P k).isSome) :
    SynthTotal cfg T := by
```

`P6`:

```lean
-- lean/MonoShim/Canonical.lean:12-18
def P6 : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.proj 0 (.param 0)]⟩, ⟨false, .emit 9⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]
```

`T6`:

```lean
-- lean/MonoShim/Canonical.lean:20
def T6 : List Key := [.inst 2 [.base 1], .inst 1 [.base 0], .inst 0 []]
```

`refs_norm_canonical`:

```lean
-- lean/MonoShim/Canonical.lean:41-42
theorem refs_norm_canonical (P : Program) (h : assocNormal P = true) :
    ∀ s : Stmt, ∀ k' ∈ refs P.sig (s.norm P), k'.norm P = k' := by
```

`collect_canonicalKeys_of_assocNormal`:

```lean
-- lean/MonoShim/Canonical.lean:167-170
theorem collect_canonicalKeys_of_assocNormal (P : Program) (cfg : MonoCfg)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key)
    (fuel : Nat) (T : List Key) (hc : collect (edgesM P cfg) sched roots fuel = some T)
    (hA : assocNormal P = true) (hR : CanonicalKeys P roots) : CanonicalKeys P T := by
```

`collect_stdCfg_closed_and_adequate_of_assocNormal`:

```lean
-- lean/MonoShim/Canonical.lean:187-193
theorem collect_stdCfg_closed_and_adequate_of_assocNormal (P : Program)
    (sched : List Key → List Key → List Key) (hs : SchedOK sched) (roots : List Key)
    (fuel : Nat) (T : List Key) (hc : collect (edgesM P (stdCfg P)) sched roots fuel = some T)
    (hA : assocNormal P = true) (hR : CanonicalKeys P roots) (h2t : SynthTotal (stdCfg P) T)
    (h0 : InstDefined P T) :
    Closed P.sig (tableM P (stdCfg P) T) T ∧
      ∀ r ∈ roots, ∀ (n : Nat) (st : St), runM P (stdCfg P) T n r st = runS P n r st := by
```

`P6chain`:

```lean
-- lean/MonoShim/Canonical.lean:207-213
def P6chain : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.proj 0 (.param 0)]⟩, ⟨false, .emit 9⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .proj 1 (.base 0)), (1, .base 0, .base 1)]
```

`canonical_refs_close_positive_control`:

```lean
-- lean/MonoShim/Canonical.lean:238-243
theorem canonical_refs_close_positive_control :
    assocNormal P6 = true ∧
    collect (edgesM P6 (stdCfg P6)) fifo [.inst 0 []] 10 = some T6 ∧
    CanonicalKeys P6 T6 ∧ CanonicalRefs P6 (stdCfg P6) T6 ∧
    Closed P6.sig (tableM P6 (stdCfg P6) T6) T6 ∧
    ∀ (n : Nat) (st : St), runM P6 (stdCfg P6) T6 n (.inst 0 []) st = runS P6 n (.inst 0 []) st := by
```

`Pnc0`:

```lean
-- lean/MonoShim/Canonical.lean:251-257
def Pnc0 : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]
```

`noncanonical_key_breaks_canonicalRefs`:

```lean
-- lean/MonoShim/Canonical.lean:262-264
theorem noncanonical_key_breaks_canonicalRefs :
    assocNormal Pnc0 = true ∧ ¬ CanonicalKeys Pnc0 [.dropGlue (.box (.proj 0 (.base 0)))] ∧
    ¬ CanonicalRefs Pnc0 (stdCfg Pnc0) [.dropGlue (.box (.proj 0 (.base 0)))] := by
```

`glueKey4a`:

```lean
-- lean/MonoShim/Canonical.lean:269
def glueKey4a : Key := .dropGlue (.pair (.base 0) (.base 1))
```

`unitA`:

```lean
-- lean/MonoShim/Canonical.lean:274
def unitA (sy : Key → Option Stmt) : List Key × (Key → Option Stmt) := ([.inst 0 [], glueKey4a], sy)
```

`unitB`:

```lean
-- lean/MonoShim/Canonical.lean:275-276
def unitB (sy : Key → Option Stmt) : List Key × (Key → Option Stmt) :=
  ([glueKey4a, .dropGlue (.base 0), .dropGlue (.base 1), .userDrop 0, .userDrop 1], sy)
```

`deterministic_units_example`:

```lean
-- lean/MonoShim/Canonical.lean:280-284
theorem deterministic_units_example :
    DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthStd P4a)] ∧
    UnitsCover [unitA (synthStd P4a), unitB (synthStd P4a)] T4a ∧
    ∀ k, linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a), unitB (synthStd P4a)] k =
      tableM P4a (stdCfg P4a) T4a k := by
```

`isShim_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:11-12
theorem isShim_pos_example : (Key.dropGlue (.base 0)).isShim = true ∧
    (Key.reifyShim 1 []).isShim = true := by decide
```

`isShim_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:13
theorem isShim_neg_example : (Key.inst 0 []).isShim = false ∧ (Key.userDrop 0).isShim = false := by
```

`norm_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:17
theorem norm_pos_example : (Key.inst 2 [.proj 0 (.base 0)]).norm P6 = .inst 2 [.base 1] := by decide
```

`norm_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:18-19
theorem norm_neg_example : (Key.inst 2 [.proj 1 (.base 0)]).norm P6 = .inst 2 [.proj 1 (.base 0)] ∧
    (Key.inst 2 [.proj 0 (.base 7)]).norm P6 = .inst 2 [.proj 0 (.base 7)] := by decide
```

`cloneKey_examples`:

```lean
-- lean/MonoShim/Examples.lean:21-22
theorem cloneKey_examples : cloneKey (.base 3) = .userClone 3 ∧
    cloneKey (.pair (.base 0) (.base 1)) = .cloneShim (.pair (.base 0) (.base 1)) := by decide
```

`reifyKey_examples`:

```lean
-- lean/MonoShim/Examples.lean:24-25
theorem reifyKey_examples : reifyKey P2d.sig 1 [] = .reifyShim 1 [] ∧
    reifyKey P2c.sig 1 [] = .inst 1 [] := by decide
```

`refs_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:30-32
theorem refs_pos_example :
    refs P2b.sig (.unsize 0 (.base 2) 0) = [.meth 0 0 (.base 2), .dropGlue (.base 2)] ∧
    refs P2a.sig (.onUnwind (.call 1 []) (.drop (.base 1))) = [.inst 1 [], .dropGlue (.base 1)] := by
```

`refs_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:36
theorem refs_neg_example : refs P2b.sig (.callDyn 0 0) = [] ∧ refs P2c.sig (.callPtr 0) = [] := by
```

`glueSrc_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:43-45
theorem glueSrc_pos_example :
    glueSrc P4a (.pair (.base 0) (.base 1)) =
      some (.seq (.onUnwind (.drop (.base 0)) (.drop (.base 1))) (.drop (.base 1))) := by
```

`PdropUnwind`:

```lean
-- lean/MonoShim/Examples.lean:49-55
def PdropUnwind : Program where
  fns := [⟨false, .drop (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .panic), (1, .emit 20)]
  cloneImpls := []
  assoc := []
```

`PdropAbort`:

```lean
-- lean/MonoShim/Examples.lean:58-64
def PdropAbort : Program where
  fns := [⟨false, .drop (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .panic), (1, .panic)]
  cloneImpls := []
  assoc := []
```

`glue_pair_unwind_drops_remaining_field_example`:

```lean
-- lean/MonoShim/Examples.lean:68-70
theorem glue_pair_unwind_drops_remaining_field_example :
    runS PdropUnwind 4 (.inst 0 []) st0 = (.unwind, ⟨[20], 0⟩) ∧
    runS PdropAbort 4 (.inst 0 []) st0 = (.abort, st0) := by
```

`glueSrc_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:73-74
theorem glueSrc_neg_example : glueSrc P4a (.dyn 0) = none ∧ glueSrc P4a (.param 0) = none ∧
    glueSrc P4a (.proj 0 (.base 0)) = none := by decide
```

`srcDef_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:76-77
theorem srcDef_pos_example : srcDef P6 (.inst 2 [.proj 0 (.base 0)]) = some (.emit 9) ∧
    srcDef P6 (.inst 1 [.base 0]) = some (.call 2 [.base 1]) := by decide
```

`srcDef_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:78
theorem srcDef_neg_example : srcDef P6 (.inst 7 []) = none := by decide
```

`synthStd_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:80-81
theorem synthStd_pos_example :
    synthStd P3 (.cloneShim (.pair (.base 0) (.base 1))) = some (ladder [.base 0, .base 1]) := by
```

`synthStd_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:83-84
theorem synthStd_neg_example : synthStd P3 (.cloneShim (.base 0)) = none ∧
    synthStd P3 (.inst 0 []) = none := by decide
```

`ladder_shape_example`:

```lean
-- lean/MonoShim/Examples.lean:86-88
theorem ladder_shape_example : ladder [.base 0, .base 1] =
    .seq (.clone (.base 0)) (.onUnwind (.seq (.clone (.base 1)) (.onUnwind .skip (.drop (.base 1))))
      (.drop (.base 0))) := rfl
```

`reach_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:92
theorem reach_pos_example : Reach (edgesM P2a (stdCfg P2a)) [.inst 0 []] (.userDrop 1) :=
```

`reach_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:95
theorem reach_neg_example : ¬ Reach (edgesM P2a (stdCfg P2a)) [.inst 0 []] (.inst 5 []) := by
```

`schedOK_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:100
theorem schedOK_pos_example : SchedOK fifo ∧ SchedOK lifo := ⟨fifo_ok, lifo_ok⟩
```

`schedOK_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:102
theorem schedOK_neg_example : ¬ SchedOK (fun w _ => w) := by
```

`edgesIn_examples`:

```lean
-- lean/MonoShim/Examples.lean:107-108
theorem edgesIn_examples : EdgesIn (edgesM P2c (stdCfg P2c)) [.inst 1 [], .inst 0 []] ∧
    ¬ EdgesIn (edgesM P2c (stdCfg P2c)) [.inst 0 []] := by decide
```

`rootsIn_examples`:

```lean
-- lean/MonoShim/Examples.lean:110-111
theorem rootsIn_examples : RootsIn [.inst 0 []] [.inst 1 [], .inst 0 []] ∧
    ¬ RootsIn [.inst 0 []] [.inst 1 []] := by decide
```

`closed_examples`:

```lean
-- lean/MonoShim/Examples.lean:113-115
theorem closed_examples :
    Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 1 [], .inst 0 []]) [.inst 1 [], .inst 0 []] ∧
    ¬ Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) [.inst 0 []] := by decide
```

`coversRefs_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:119
theorem coversRefs_pos_example (P : Program) : CoversRefs P.sig (refs P.sig) := fun _ _ h => h
```

`coversRefs_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:120
theorem coversRefs_neg_example : ¬ CoversRefs P2a.sig (refsNoCleanup P2a.sig) :=
```

`bodyEquiv_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:123-124
theorem bodyEquiv_pos_example (sig : Sig) : BodyEquiv sig (ladder [.base 0, .base 1])
    (.cloneAgg [.base 0, .base 1]) := ladder_bodyEquiv_cloneAgg sig _
```

`bodyEquiv_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:125-126
theorem bodyEquiv_neg_example :
    ¬ BodyEquiv P3.sig (ladderNoCleanup [.base 0, .base 1]) (.cloneAgg [.base 0, .base 1]) := by
```

`synthAgrees_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:131
theorem synthAgrees_pos_example : SynthAgrees P4a (stdCfg P4a) T4a := synthStd_agrees P4a T4a
```

`synthAgrees_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:132
theorem synthAgrees_neg_example : ¬ SynthAgrees P4a (cfgRev P4a) T4a :=
```

`canonical_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:135
theorem canonical_pos_example : CanonicalKeys P6 T6 ∧ CanonicalRefs P6 (stdCfg P6) T6 := by decide
```

`canonical_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:136-137
theorem canonical_neg_example : ¬ CanonicalRefs P6chain (stdCfg P6chain) T6 ∧
    ¬ CanonicalKeys Pnc [.dropGlue (.proj 0 (.base 0))] := by decide
```

`assocNormal_examples`:

```lean
-- lean/MonoShim/Examples.lean:141-144
theorem assocNormal_examples :
    assocNormal P6 = true ∧ assocNormal P6chain = false ∧ assocNormal P9assoc = false ∧
    (Ty.proj 0 (.base 0)).norm P6chain.assoc = .proj 1 (.base 0) ∧
    ((Ty.proj 0 (.base 0)).norm P6chain.assoc).norm P6chain.assoc = .base 1 := by
```

`instDefined_examples`:

```lean
-- lean/MonoShim/Examples.lean:147-148
theorem instDefined_examples : InstDefined P2c [.inst 1 [], .inst 0 []] ∧
    ¬ InstDefined Pundef [.inst 5 [], .inst 0 []] := by decide
```

`synthTotal_examples`:

```lean
-- lean/MonoShim/Examples.lean:150-151
theorem synthTotal_examples : SynthTotal (stdCfg P2a) [.dropGlue (.base 1)] ∧
    ¬ SynthTotal (cfgNoSynth P2a) [.dropGlue (.base 1)] := by decide
```

`verifiedBody_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:155
theorem verifiedBody_pos_example : VerifiedBody P4b.sig Q4b (.emit 1) (appends [1]) :=
```

`verifiedBody_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:158
theorem verifiedBody_neg_example : ¬ VerifiedBody P4b.sig Q4b (.emit 2) (appends [1]) := by
```

`specs_pos_example`:

```lean
-- lean/MonoShim/Examples.lean:163-164
theorem specs_pos_example : GenericVerified P4b Q4b ∧ ImplsConform P4a Q4a T4a ∧
    SynthVerified P4a (stdCfg P4a) Q4a T4a :=
```

`specs_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:166
theorem specs_neg_example : ¬ ImplsConform P4b Q4b T4b ∧ ¬ SynthVerified P4a (cfgRev P4a) Q4a T4a :=
```

`P4bad`:

```lean
-- lean/MonoShim/Examples.lean:171-177
def P4bad : Program where
  fns := [⟨false, .emit 2⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`genericVerified_neg_example`:

```lean
-- lean/MonoShim/Examples.lean:179
theorem genericVerified_neg_example : ¬ GenericVerified P4bad Q4b := by
```

`meetsAt_examples`:

```lean
-- lean/MonoShim/Examples.lean:184-186
theorem meetsAt_examples :
    MeetsAt P4a.sig (tableM P4a (stdCfg P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) ∧
    ¬ MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4a (.inst 0 [])) (.inst 0 []) :=
```

`deterministicUnits_examples`:

```lean
-- lean/MonoShim/Examples.lean:190-192
theorem deterministicUnits_examples :
    DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthStd P4a)] ∧
    ¬ DeterministicUnits (synthStd P4a) [unitA (synthStd P4a), unitB (synthRev P4a)] :=
```

`rankCheck_examples`:

```lean
-- lean/MonoShim/Examples.lean:195
theorem rankCheck_examples : rankCheck P5ok rank5ok = true ∧ rankCheck P5 rank5ok = false :=
```

`grows_examples`:

```lean
-- lean/MonoShim/Examples.lean:200-202
theorem grows_examples :
    Ty.grows (.param 0) = false ∧ Ty.grows (.base 3) = false ∧ Ty.grows (.box (.param 0)) = true ∧
    Ty.grows (.pair (.base 0) (.param 1)) = true ∧ Ty.grows (.proj 0 (.param 0)) = true := by
```

`postClean`:

```lean
-- lean/MonoShim/Ladder.lean:11-13
def postClean (c : Call) (done : List Ty) : Res × St → Res × St
  | (.unwind, st) => cleanupDrops c done st
  | r => r
```

`ladder_post`:

```lean
-- lean/MonoShim/Ladder.lean:15-17
theorem ladder_post (sig : Sig) (c : Call) : ∀ (ts done : List Ty) (fr : Frame) (st : St),
    postClean c done ((execS sig c (ladder ts) fr st).1, (execS sig c (ladder ts) fr st).2.2)
      = aggClone c done ts st ∧ (execS sig c (ladder ts) fr st).2.1 = fr := by
```

`ladder_bodyEquiv_cloneAgg`:

```lean
-- lean/MonoShim/Ladder.lean:58-59
theorem ladder_bodyEquiv_cloneAgg (sig : Sig) (fs : List Ty) :
    BodyEquiv sig (ladder fs) (.cloneAgg fs) := by
```

`synthStd_optEquiv`:

```lean
-- lean/MonoShim/Ladder.lean:64-65
theorem synthStd_optEquiv (P : Program) (k : Key) (hk : k.isShim = true) :
    OptEquiv P.sig (synthStd P k) (srcDef0 P k) := by
```

`synthStd_agrees`:

```lean
-- lean/MonoShim/Ladder.lean:80
theorem synthStd_agrees (P : Program) (T : List Key) : SynthAgrees P (stdCfg P) T :=
```

`ladderNoCleanup`:

```lean
-- lean/MonoShim/LadderExamples.lean:10-12
def ladderNoCleanup : List Ty → Stmt
  | [] => .skip
  | t :: ts => .seq (.clone t) (ladderNoCleanup ts)
```

`P3`:

```lean
-- lean/MonoShim/LadderExamples.lean:16-22
def P3 : Program where
  fns := [⟨false, .clone (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .emit 2)]
  cloneImpls := [(0, .emit 1), (1, .panic)]
  assoc := []
```

`P3abort`:

```lean
-- lean/MonoShim/LadderExamples.lean:25-31
def P3abort : Program where
  fns := [⟨false, .clone (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .panic)]
  cloneImpls := [(0, .emit 1), (1, .panic)]
  assoc := []
```

`ladder_cloneAgg_unwind_and_abort_examples`:

```lean
-- lean/MonoShim/LadderExamples.lean:36-44
theorem ladder_cloneAgg_unwind_and_abort_examples :
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (ladder [.base 0, .base 1]) [] st0
      = (.unwind, [], ⟨[1, 2], 0⟩) ∧
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (.cloneAgg [.base 0, .base 1]) [] st0
      = (.unwind, [], ⟨[1, 2], 0⟩) ∧
    execS P3abort.sig (runKey P3abort.sig (srcDef P3abort) 5) (ladder [.base 0, .base 1]) [] st0
      = (.abort, [], ⟨[1], 0⟩) ∧
    execS P3abort.sig (runKey P3abort.sig (srcDef P3abort) 5) (.cloneAgg [.base 0, .base 1]) [] st0
      = (.abort, [], ⟨[1], 0⟩) := by
```

`P3three`:

```lean
-- lean/MonoShim/LadderExamples.lean:49-55
def P3three : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := [(0, .emit 10), (1, .emit 20)]
  cloneImpls := [(0, .emit 1), (1, .emit 2), (2, .panic)]
  assoc := []
```

`ladder_cloneAgg_three_fields_reverse_cleanup_example`:

```lean
-- lean/MonoShim/LadderExamples.lean:60-64
theorem ladder_cloneAgg_three_fields_reverse_cleanup_example :
    execS P3three.sig (runKey P3three.sig (srcDef P3three) 5) (ladder [.base 0, .base 1, .base 2]) []
      st0 = (.unwind, [], ⟨[1, 2, 20, 10], 0⟩) ∧
    execS P3three.sig (runKey P3three.sig (srcDef P3three) 5) (.cloneAgg [.base 0, .base 1, .base 2])
      [] st0 = (.unwind, [], ⟨[1, 2, 20, 10], 0⟩) := by
```

`ladderNoCleanup_ne_cloneAgg`:

```lean
-- lean/MonoShim/LadderExamples.lean:69-73
theorem ladderNoCleanup_ne_cloneAgg :
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (ladderNoCleanup [.base 0, .base 1]) [] st0
      = (.unwind, [], ⟨[1], 0⟩) ∧
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (ladderNoCleanup [.base 0, .base 1]) [] st0 ≠
    execS P3.sig (runKey P3.sig (srcDef P3) 5) (.cloneAgg [.base 0, .base 1]) [] st0 := by
```

`cfg3`:

```lean
-- lean/MonoShim/LadderExamples.lean:79
def cfg3 : MonoCfg := ⟨refsNoCleanup P3.sig, synthStd P3⟩
```

`T3`:

```lean
-- lean/MonoShim/LadderExamples.lean:80
def T3 : List Key := [.userClone 1, .userClone 0, .cloneShim (.pair (.base 0) (.base 1)), .inst 0 []]
```

`ladder_drop_refs_missing_break_closure`:

```lean
-- lean/MonoShim/LadderExamples.lean:82-86
theorem ladder_drop_refs_missing_break_closure :
    collect (edgesM P3 cfg3) fifo [.inst 0 []] 10 = some T3 ∧
    ¬ Closed P3.sig (tableM P3 cfg3 T3) T3 ∧
    runM P3 cfg3 T3 4 (.inst 0 []) st0 = (.link (.dropGlue (.base 0)), ⟨[1], 0⟩) ∧
    runS P3 4 (.inst 0 []) st0 = (.unwind, ⟨[1, 2], 0⟩) := by
```

`closed_excludes_link`:

```lean
-- lean/MonoShim/LinkFree.lean:171-173
theorem closed_excludes_link (sig : Sig) (tbl : Key → Option Stmt) (T : List Key)
    (hC : Closed sig tbl T) :
    ∀ (n : Nat), ∀ k ∈ T, ∀ (st : St) (k' : Key), (runKey sig tbl n k st).1 ≠ .link k' := by
```

`PdeadUndef`:

```lean
-- lean/MonoShim/LinkFree.lean:187-193
def PdeadUndef : Program where
  fns := [⟨false, .seq .panic (.call 5 [])⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`TdeadUndef`:

```lean
-- lean/MonoShim/LinkFree.lean:195
def TdeadUndef : List Key := [.inst 5 [], .inst 0 []]
```

`dead_undefined_call_never_links`:

```lean
-- lean/MonoShim/LinkFree.lean:200-210
theorem dead_undefined_call_never_links :
    RootsIn [.inst 0 []] TdeadUndef ∧
    EdgesIn (edgesM PdeadUndef (stdCfg PdeadUndef)) TdeadUndef ∧
    CoversRefs PdeadUndef.sig (stdCfg PdeadUndef).E ∧
    SynthAgrees PdeadUndef (stdCfg PdeadUndef) TdeadUndef ∧
    CanonicalKeys PdeadUndef TdeadUndef ∧
    CanonicalRefs PdeadUndef (stdCfg PdeadUndef) TdeadUndef ∧
    ¬ Closed PdeadUndef.sig (tableM PdeadUndef (stdCfg PdeadUndef) TdeadUndef) TdeadUndef ∧
    ¬ InstDefined PdeadUndef TdeadUndef ∧
    ∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St) (k' : Key),
      (runM PdeadUndef (stdCfg PdeadUndef) TdeadUndef n r st).1 ≠ .link k' := by
```

`st0`:

```lean
-- lean/MonoShim/MissingEdges.lean:16
def st0 : St := ⟨[], 0⟩
```

`refsNoCleanup`:

```lean
-- lean/MonoShim/MissingEdges.lean:26-31
def refsNoCleanup (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoCleanup sig a ++ refsNoCleanup sig b
  | .onUnwind a _ => refsNoCleanup sig a
  | .cloneAgg ts => ts.map cloneKey
  | .guard s => refsNoCleanup sig s
  | s => refs sig s
```

`refsNoVtable`:

```lean
-- lean/MonoShim/MissingEdges.lean:35-40
def refsNoVtable (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoVtable sig a ++ refsNoVtable sig b
  | .onUnwind a b => refsNoVtable sig a ++ refsNoVtable sig b
  | .guard s => refsNoVtable sig s
  | .unsize _ t _ => [.dropGlue t]
  | s => refs sig s
```

`refsNoOperand`:

```lean
-- lean/MonoShim/MissingEdges.lean:43-48
def refsNoOperand (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoOperand sig a ++ refsNoOperand sig b
  | .onUnwind a b => refsNoOperand sig a ++ refsNoOperand sig b
  | .guard s => refsNoOperand sig s
  | .reify _ _ _ => []
  | s => refs sig s
```

`refsNoReifyShim`:

```lean
-- lean/MonoShim/MissingEdges.lean:52-57
def refsNoReifyShim (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoReifyShim sig a ++ refsNoReifyShim sig b
  | .onUnwind a b => refsNoReifyShim sig a ++ refsNoReifyShim sig b
  | .guard s => refsNoReifyShim sig s
  | .reify _ f τs => [.inst f τs]
  | s => refs sig s
```

`P2a`:

```lean
-- lean/MonoShim/MissingEdges.lean:63-69
def P2a : Program where
  fns := [⟨false, .onUnwind (.call 1 []) (.drop (.base 1))⟩, ⟨false, .panic⟩]
  methods := []
  impls := []
  dropImpls := [(1, .emit 7)]
  cloneImpls := []
  assoc := []
```

`cfg2a`:

```lean
-- lean/MonoShim/MissingEdges.lean:71
def cfg2a : MonoCfg := ⟨refsNoCleanup P2a.sig, synthStd P2a⟩
```

`T2a`:

```lean
-- lean/MonoShim/MissingEdges.lean:72
def T2a : List Key := [.inst 1 [], .inst 0 []]
```

`P2b`:

```lean
-- lean/MonoShim/MissingEdges.lean:97-103
def P2b : Program where
  fns := [⟨false, .seq (.unsize 0 (.base 2) 0) (.callDyn 0 0)⟩]
  methods := [(0, [0])]
  impls := [⟨0, 0, .base 2, .emit 5⟩]
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`cfg2b`:

```lean
-- lean/MonoShim/MissingEdges.lean:105
def cfg2b : MonoCfg := ⟨refsNoVtable P2b.sig, synthStd P2b⟩
```

`T2b`:

```lean
-- lean/MonoShim/MissingEdges.lean:106
def T2b : List Key := [.dropGlue (.base 2), .inst 0 []]
```

`P2c`:

```lean
-- lean/MonoShim/MissingEdges.lean:129-135
def P2c : Program where
  fns := [⟨false, .seq (.reify 0 1 []) (.callPtr 0)⟩, ⟨false, .emit 3⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`cfg2c`:

```lean
-- lean/MonoShim/MissingEdges.lean:137
def cfg2c : MonoCfg := ⟨refsNoOperand P2c.sig, synthStd P2c⟩
```

`T2c`:

```lean
-- lean/MonoShim/MissingEdges.lean:138
def T2c : List Key := [.inst 0 []]
```

`P2d`:

```lean
-- lean/MonoShim/MissingEdges.lean:161-167
def P2d : Program where
  fns := [⟨false, .seq (.reify 0 1 []) (.callPtr 0)⟩, ⟨true, .emit 4⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`cfg2d`:

```lean
-- lean/MonoShim/MissingEdges.lean:169
def cfg2d : MonoCfg := ⟨refsNoReifyShim P2d.sig, synthStd P2d⟩
```

`T2d`:

```lean
-- lean/MonoShim/MissingEdges.lean:170
def T2d : List Key := [.inst 1 [], .inst 0 []]
```

`full_edges_close_missing_edge_examples`:

```lean
-- lean/MonoShim/MissingEdges.lean:194-208
theorem full_edges_close_missing_edge_examples :
    collect (edgesM P2a (stdCfg P2a)) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    Closed P2a.sig (tableM P2a (stdCfg P2a) [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []])
      [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    collect (edgesM P2b (stdCfg P2b)) fifo [.inst 0 []] 10 =
      some [.dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []] ∧
    Closed P2b.sig (tableM P2b (stdCfg P2b) [.dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []])
      [.dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []] ∧
    collect (edgesM P2c (stdCfg P2c)) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 1 [], .inst 0 []]) [.inst 1 [], .inst 0 []] ∧
    collect (edgesM P2d (stdCfg P2d)) fifo [.inst 0 []] 10 =
      some [.inst 1 [], .reifyShim 1 [], .inst 0 []] ∧
    Closed P2d.sig (tableM P2d (stdCfg P2d) [.inst 1 [], .reifyShim 1 [], .inst 0 []])
      [.inst 1 [], .reifyShim 1 [], .inst 0 []] := by
```

`Q2c`:

```lean
-- lean/MonoShim/MoreTightness.lean:12
def Q2c : Key → Spec := fun _ => appends [3]
```

`nonclosed_target_breaks_spec_transfer`:

```lean
-- lean/MonoShim/MoreTightness.lean:42-46
theorem nonclosed_target_breaks_spec_transfer :
    ¬ Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) [.inst 0 []] ∧
    GenericVerified P2c Q2c ∧ ImplsConform P2c Q2c [.inst 0 []] ∧
    SynthVerified P2c (stdCfg P2c) Q2c [.inst 0 []] ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P2c.sig (tableM P2c (stdCfg P2c) [.inst 0 []]) (Q2c k) k) := by
```

`unverified_generic_body_breaks_spec_transfer`:

```lean
-- lean/MonoShim/MoreTightness.lean:60-65
theorem unverified_generic_body_breaks_spec_transfer :
    Closed P4bad.sig (tableM P4bad (stdCfg P4bad) [.inst 0 []]) [.inst 0 []] ∧
    ¬ GenericVerified P4bad Q4b ∧ ImplsConform P4bad Q4b [.inst 0 []] ∧
    SynthVerified P4bad (stdCfg P4bad) Q4b [.inst 0 []] ∧
    runM P4bad (stdCfg P4bad) [.inst 0 []] 2 (.inst 0 []) st0 = (.ok, ⟨[2], 0⟩) ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P4bad.sig (tableM P4bad (stdCfg P4bad) [.inst 0 []]) (Q4b k) k) := by
```

`schedDrop`:

```lean
-- lean/MonoShim/MoreTightness.lean:80
def schedDrop (w _ : List Key) : List Key := w
```

`inadmissible_scheduler_misses_keys`:

```lean
-- lean/MonoShim/MoreTightness.lean:84-88
theorem inadmissible_scheduler_misses_keys :
    ¬ SchedOK schedDrop ∧
    collect (edgesM P2c (stdCfg P2c)) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    Reach (edgesM P2c (stdCfg P2c)) [.inst 0 []] (.inst 1 []) ∧ Key.inst 1 [] ∉ [Key.inst 0 []] ∧
    ¬ (∀ k, k ∈ [Key.inst 0 []] ↔ Reach (edgesM P2c (stdCfg P2c)) [.inst 0 []] k) := by
```

`polyrec_inadmissible_scheduler_terminates`:

```lean
-- lean/MonoShim/MoreTightness.lean:98-99
theorem polyrec_inadmissible_scheduler_terminates :
    ¬ SchedOK schedDrop ∧ collect (edgesM P5 (stdCfg P5)) schedDrop [.inst 0 []] 5 = some [.inst 0 []] :=
```

`pre2a`:

```lean
-- lean/MonoShim/MoreTightness.lean:103
def pre2a : List (Key × Stmt) := [(.dropGlue (.base 1), .invoke (.userDrop 1))]
```

`precomputed_example`:

```lean
-- lean/MonoShim/MoreTightness.lean:107-114
theorem precomputed_example :
    SchedOK fifo ∧ SchedOK lifo ∧
    (∀ k, Reach (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) [.inst 0 []] k → k.isShim = true →
      pre2a.lookup k = synthStd P2a k) ∧
    collect (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    collect (edgesM P2a (preCfg (refs P2a.sig) pre2a)) lifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] := by
```

`stale_precomputed_table_changes_target`:

```lean
-- lean/MonoShim/MoreTightness.lean:128-141
theorem stale_precomputed_table_changes_target :
    SchedOK fifo ∧
    ¬ (∀ k, Reach (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) [.inst 0 []] k → k.isShim = true →
        (pre2a.drop 1).lookup k = synthStd P2a k) ∧
    collect (edgesM P2a ⟨refs P2a.sig, synthStd P2a⟩) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    collect (edgesM P2a (preCfg (refs P2a.sig) (pre2a.drop 1))) fifo [.inst 0 []] 10 =
      some [.dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    ¬ ((∀ k, k ∈ ([.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] : List Key) ↔
          k ∈ ([.dropGlue (.base 1), .inst 1 [], .inst 0 []] : List Key)) ∧
       ∀ k, tableM P2a ⟨refs P2a.sig, synthStd P2a⟩
              [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] k =
            tableM P2a (preCfg (refs P2a.sig) (pre2a.drop 1))
              [.dropGlue (.base 1), .inst 1 [], .inst 0 []] k) := by
```

`fifo_lifo_same_set_example`:

```lean
-- lean/MonoShim/MoreTightness.lean:156-162
theorem fifo_lifo_same_set_example :
    SchedOK fifo ∧ SchedOK lifo ∧
    collect (edgesM Pall (stdCfg Pall)) fifo [.inst 0 []] 40 = some Tall ∧
    collect (edgesM Pall (stdCfg Pall)) lifo [.inst 0 []] 40 =
      some [.userDrop 0, .dropGlue (.base 0), .dropGlue (.base 3), .userClone 3, .userClone 0,
        .cloneShim (.pair (.base 0) (.base 3)), .cloneShim .fnPtr, .inst 1 [], .reifyShim 1 [],
        .userDrop 2, .dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []] := by
```

`inadmissible_scheduler_breaks_precomputed_equality`:

```lean
-- lean/MonoShim/MoreTightness.lean:168-176
theorem inadmissible_scheduler_breaks_precomputed_equality :
    SchedOK fifo ∧ ¬ SchedOK schedDrop ∧
    (∀ k, Reach (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) [.inst 0 []] k → k.isShim = true →
      ([] : List (Key × Stmt)).lookup k = synthStd P2c k) ∧
    collect (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    collect (edgesM P2c (preCfg (refs P2c.sig) [])) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    ¬ ((∀ k, k ∈ ([.inst 1 [], .inst 0 []] : List Key) ↔ k ∈ ([.inst 0 []] : List Key)) ∧
       ∀ k, tableM P2c ⟨refs P2c.sig, synthStd P2c⟩ [.inst 1 [], .inst 0 []] k =
            tableM P2c (preCfg (refs P2c.sig) []) [.inst 0 []] k) := by
```

`nondeterministic_units_break_link_equality`:

```lean
-- lean/MonoShim/MoreTightness.lean:193-199
theorem nondeterministic_units_break_link_equality :
    ¬ DeterministicUnits (synthStd P4a) [unitB (synthRev P4a), unitA (synthStd P4a)] ∧
    UnitsCover [unitB (synthRev P4a), unitA (synthStd P4a)] T4a ∧
    linkUnits P4a (refs P4a.sig) [unitB (synthRev P4a), unitA (synthStd P4a)] glueKey4a ≠
      tableM P4a (stdCfg P4a) T4a glueKey4a ∧
    ¬ (∀ k, linkUnits P4a (refs P4a.sig) [unitB (synthRev P4a), unitA (synthStd P4a)] k =
      tableM P4a ⟨refs P4a.sig, synthStd P4a⟩ T4a k) := by
```

`uncovering_units_break_link_equality`:

```lean
-- lean/MonoShim/MoreTightness.lean:221-227
theorem uncovering_units_break_link_equality :
    DeterministicUnits (synthStd P4a) [unitA (synthStd P4a)] ∧
    ¬ UnitsCover [unitA (synthStd P4a)] T4a ∧
    linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a)] (.dropGlue (.base 0)) ≠
      tableM P4a (stdCfg P4a) T4a (.dropGlue (.base 0)) ∧
    ¬ (∀ k, linkUnits P4a (refs P4a.sig) [unitA (synthStd P4a)] k =
      tableM P4a ⟨refs P4a.sig, synthStd P4a⟩ T4a k) := by
```

`inadmissible_first_scheduler_breaks_order_independence`:

```lean
-- lean/MonoShim/MoreTightness.lean:244-248
theorem inadmissible_first_scheduler_breaks_order_independence :
    ¬ SchedOK schedDrop ∧ SchedOK fifo ∧
    collect (edgesM P2c (stdCfg P2c)) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    collect (edgesM P2c (stdCfg P2c)) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    ¬ (∀ k, k ∈ ([.inst 0 []] : List Key) ↔ k ∈ ([.inst 1 [], .inst 0 []] : List Key)) := by
```

`inadmissible_second_scheduler_breaks_order_independence`:

```lean
-- lean/MonoShim/MoreTightness.lean:256-260
theorem inadmissible_second_scheduler_breaks_order_independence :
    SchedOK fifo ∧ ¬ SchedOK schedDrop ∧
    collect (edgesM P2c (stdCfg P2c)) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    collect (edgesM P2c (stdCfg P2c)) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    ¬ (∀ k, k ∈ ([.inst 1 [], .inst 0 []] : List Key) ↔ k ∈ ([.inst 0 []] : List Key)) := by
```

`inadmissible_on_demand_scheduler_breaks_precomputed_equality`:

```lean
-- lean/MonoShim/MoreTightness.lean:270-278
theorem inadmissible_on_demand_scheduler_breaks_precomputed_equality :
    ¬ SchedOK schedDrop ∧ SchedOK fifo ∧
    (∀ k, Reach (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) [.inst 0 []] k → k.isShim = true →
      ([] : List (Key × Stmt)).lookup k = synthStd P2c k) ∧
    collect (edgesM P2c ⟨refs P2c.sig, synthStd P2c⟩) schedDrop [.inst 0 []] 10 = some [.inst 0 []] ∧
    collect (edgesM P2c (preCfg (refs P2c.sig) [])) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    ¬ ((∀ k, k ∈ ([.inst 0 []] : List Key) ↔ k ∈ ([.inst 1 [], .inst 0 []] : List Key)) ∧
       ∀ k, tableM P2c ⟨refs P2c.sig, synthStd P2c⟩ [.inst 0 []] k =
            tableM P2c (preCfg (refs P2c.sig) []) [.inst 1 [], .inst 0 []] k) := by
```

`P7a`:

```lean
-- lean/MonoShim/Relativity.lean:12-18
def P7a : Program where
  fns := [⟨false, .seq .panic (.call 1 [])⟩, ⟨false, .emit 1⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`T7a`:

```lean
-- lean/MonoShim/Relativity.lean:20
def T7a : List Key := [.inst 1 [], .inst 0 []]
```

`reach_subset_of_rootsIn_edgesIn`:

```lean
-- lean/MonoShim/Relativity.lean:24-25
theorem reach_subset_of_rootsIn_edgesIn (edges : Key → List Key) (roots T : List Key)
    (hR : RootsIn roots T) (hE : EdgesIn edges T) : ∀ k, Reach edges roots k → k ∈ T := by
```

`P7b`:

```lean
-- lean/MonoShim/Relativity.lean:50-56
def P7b : Program where
  fns := [⟨false, .call 1 []⟩, ⟨false, .drop (.base 0)⟩]
  methods := []
  impls := []
  dropImpls := [(0, .emit 3)]
  cloneImpls := []
  assoc := []
```

`edgesAvail`:

```lean
-- lean/MonoShim/Relativity.lean:60-61
def edgesAvail (P : Program) (cfg : MonoCfg) (avail : Key → Bool) (k : Key) : List Key :=
  (edgesM P cfg k).filter avail
```

`availLocal`:

```lean
-- lean/MonoShim/Relativity.lean:65-67
def availLocal : Key → Bool
  | .inst 1 _ => false
  | _ => true
```

`T7b`:

```lean
-- lean/MonoShim/Relativity.lean:70
def T7b : List Key := [.userDrop 0, .dropGlue (.base 0), .inst 1 [], .inst 0 []]
```

`meetsAt_tableM_iff_srcDef_of_adequacy`:

```lean
-- lean/MonoShim/SourceOnly.lean:96-99
theorem meetsAt_tableM_iff_srcDef_of_adequacy (P : Program) (cfg : MonoCfg) (T : List Key)
    (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E) (h2 : SynthAgrees P cfg T)
    (h3a : CanonicalKeys P T) (h3b : CanonicalRefs P cfg T) (Q : Spec) :
    ∀ k ∈ T, (MeetsAt P.sig (tableM P cfg T) Q k ↔ MeetsAt P.sig (srcDef P) Q k) := by
```

`canonicalRefs_of_closed_canonicalKeys`:

```lean
-- lean/MonoShim/SourceOnly.lean:110-112
theorem canonicalRefs_of_closed_canonicalKeys (P : Program) (cfg : MonoCfg) (T : List Key)
    (hC : Closed P.sig (tableM P cfg T) T) (h3a : CanonicalKeys P T) :
    CanonicalRefs P cfg T := by
```

`meetsAt_tableM_iff_srcDef_of_closed`:

```lean
-- lean/MonoShim/SourceOnly.lean:121-124
theorem meetsAt_tableM_iff_srcDef_of_closed (P : Program) (cfg : MonoCfg) (T : List Key)
    (hC : Closed P.sig (tableM P cfg T) T) (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T)
    (Q : Spec) :
    ∀ k ∈ T, (MeetsAt P.sig (tableM P cfg T) Q k ↔ MeetsAt P.sig (srcDef P) Q k) := by
```

`appends`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:10
def appends (l : List Nat) : Spec := fun st o => o = (.ok, { st with evs := st.evs ++ l })
```

`P4a`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:16-22
def P4a : Program where
  fns := [⟨false, .drop (.pair (.base 0) (.base 1))⟩]
  methods := []
  impls := []
  dropImpls := [(0, .emit 10), (1, .emit 20)]
  cloneImpls := []
  assoc := []
```

`synthRev`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:26-28
def synthRev (P : Program) : Key → Option Stmt
  | .dropGlue (.pair a b) => some (.seq (.onUnwind (.drop b) (.drop a)) (.drop a))
  | k => synthStd P k
```

`cfgRev`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:30
def cfgRev (P : Program) : MonoCfg := ⟨refs P.sig, synthRev P⟩
```

`Q4a`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:33-40
def Q4a : Key → Spec
  | .inst 0 [] => appends [10, 20]
  | .dropGlue (.pair (.base 0) (.base 1)) => appends [10, 20]
  | .dropGlue (.base 0) => appends [10]
  | .dropGlue (.base 1) => appends [20]
  | .userDrop 0 => appends [10]
  | .userDrop 1 => appends [20]
  | _ => fun _ _ => True
```

`T4a`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:42-44
def T4a : List Key :=
  [.userDrop 1, .userDrop 0, .dropGlue (.base 1), .dropGlue (.base 0),
    .dropGlue (.pair (.base 0) (.base 1)), .inst 0 []]
```

`P4a_std_meets_specs`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:126-129
theorem P4a_std_meets_specs :
    Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a ∧ GenericVerified P4a Q4a ∧
    ImplsConform P4a Q4a T4a ∧ SynthVerified P4a (stdCfg P4a) Q4a T4a ∧
    ∀ k ∈ T4a, MeetsAt P4a.sig (tableM P4a (stdCfg P4a) T4a) (Q4a k) k := by
```

`srcVerdict_correct_of_adequacy`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:192-196
theorem srcVerdict_correct_of_adequacy (P : Program) (cfg : MonoCfg) (T : List Key)
    (Q : Key → Spec) (hR : RootsIn [.inst 0 []] T) (hE : EdgesIn (edgesM P cfg) T)
    (h1 : CoversRefs P.sig cfg.E) (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T)
    (h3b : CanonicalRefs P cfg T) :
    srcVerdict P Q = true ↔ MeetsAt P.sig (tableM P cfg T) (Q (.inst 0 [])) (.inst 0 []) := by
```

`srcVerdict_correct_example`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:202-205
theorem srcVerdict_correct_example :
    RootsIn [.inst 0 []] T4a ∧ EdgesIn (edgesM P4a (stdCfg P4a)) T4a ∧
    CoversRefs P4a.sig (stdCfg P4a).E ∧ SynthAgrees P4a (stdCfg P4a) T4a ∧
    CanonicalKeys P4a T4a ∧ CanonicalRefs P4a (stdCfg P4a) T4a ∧ srcVerdict P4a Q4a = true := by
```

`P4b`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:220-226
def P4b : Program where
  fns := [⟨false, .mcall 0 0 (.param 0)⟩]
  methods := [(0, [0])]
  impls := [⟨0, 0, .base 0, .emit 1⟩, ⟨0, 0, .base 1, .emit 2⟩]
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`Q4b`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:229
def Q4b : Key → Spec := fun _ => appends [1]
```

`T4b`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:231
def T4b : List Key := [.meth 0 0 (.base 1), .inst 0 [.base 1]]
```

`generic_verified_wrong_at_nonconforming_impl`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:247-253
theorem generic_verified_wrong_at_nonconforming_impl :
    collect (edgesM P4b (stdCfg P4b)) fifo [.inst 0 [.base 1]] 10 = some T4b ∧
    Closed P4b.sig (tableM P4b (stdCfg P4b) T4b) T4b ∧ GenericVerified P4b Q4b ∧
    SynthVerified P4b (stdCfg P4b) Q4b T4b ∧ ¬ ImplsConform P4b Q4b T4b ∧
    runM P4b (stdCfg P4b) T4b 2 (.inst 0 [.base 1]) st0 = (.ok, ⟨[2], 0⟩) ∧
    ¬ MeetsAt P4b.sig (tableM P4b (stdCfg P4b) T4b) (Q4b (.inst 0 [.base 1])) (.inst 0 [.base 1]) ∧
    ¬ (∀ k ∈ T4b, MeetsAt P4b.sig (tableM P4b (stdCfg P4b) T4b) (Q4b k) k) := by
```

`generic_verified_right_at_conforming_impl`:

```lean
-- lean/MonoShim/SourceOnlyExamples.lean:274-276
theorem generic_verified_right_at_conforming_impl :
    ∀ k ∈ [.meth 0 0 (.base 0), .inst 0 [.base 0]],
      MeetsAt P4b.sig (tableM P4b (stdCfg P4b) [.meth 0 0 (.base 0), .inst 0 [.base 0]]) (Q4b k) k := by
```

`Q4aRev`:

```lean
-- lean/MonoShim/SourceTransfer.lean:14-21
def Q4aRev : Key → Spec
  | .inst 0 [] => appends [20, 10]
  | .dropGlue (.pair (.base 0) (.base 1)) => appends [20, 10]
  | .dropGlue (.base 0) => appends [10]
  | .dropGlue (.base 1) => appends [20]
  | .userDrop 0 => appends [10]
  | .userDrop 1 => appends [20]
  | _ => fun _ _ => True
```

`P4a_std_meets_specs_in_source_semantics`:

```lean
-- lean/MonoShim/SourceTransfer.lean:73-78
theorem P4a_std_meets_specs_in_source_semantics :
    Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a ∧
    GenericVerified P4a Q4a ∧ ImplsConform P4a Q4a T4a ∧
    SynthVerified P4a (stdCfg P4a) Q4a T4a ∧
    SynthAgrees P4a (stdCfg P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    ∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4a k) k := by
```

`nonclosed_target_breaks_source_transfer`:

```lean
-- lean/MonoShim/SourceTransfer.lean:91-96
theorem nonclosed_target_breaks_source_transfer :
    ¬ Closed P4a.sig (tableM P4a (stdCfg P4a) [.inst 0 []]) [.inst 0 []] ∧
    GenericVerified P4a Q4aRev ∧ ImplsConform P4a Q4aRev [.inst 0 []] ∧
    SynthVerified P4a (stdCfg P4a) Q4aRev [.inst 0 []] ∧
    SynthAgrees P4a (stdCfg P4a) [.inst 0 []] ∧ CanonicalKeys P4a [.inst 0 []] ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
```

`unverified_generic_body_breaks_source_transfer`:

```lean
-- lean/MonoShim/SourceTransfer.lean:108-113
theorem unverified_generic_body_breaks_source_transfer :
    Closed P4bad.sig (tableM P4bad (stdCfg P4bad) [.inst 0 []]) [.inst 0 []] ∧
    ¬ GenericVerified P4bad Q4b ∧ ImplsConform P4bad Q4b [.inst 0 []] ∧
    SynthVerified P4bad (stdCfg P4bad) Q4b [.inst 0 []] ∧
    SynthAgrees P4bad (stdCfg P4bad) [.inst 0 []] ∧ CanonicalKeys P4bad [.inst 0 []] ∧
    ¬ (∀ k ∈ [.inst 0 []], MeetsAt P4bad.sig (srcDef P4bad) (Q4b k) k) := by
```

`nonconforming_impl_breaks_source_transfer`:

```lean
-- lean/MonoShim/SourceTransfer.lean:126-130
theorem nonconforming_impl_breaks_source_transfer :
    Closed P4b.sig (tableM P4b (stdCfg P4b) T4b) T4b ∧ GenericVerified P4b Q4b ∧
    ¬ ImplsConform P4b Q4b T4b ∧ SynthVerified P4b (stdCfg P4b) Q4b T4b ∧
    SynthAgrees P4b (stdCfg P4b) T4b ∧ CanonicalKeys P4b T4b ∧
    ¬ (∀ k ∈ T4b, MeetsAt P4b.sig (srcDef P4b) (Q4b k) k) := by
```

`unverified_synth_breaks_source_transfer`:

```lean
-- lean/MonoShim/SourceTransfer.lean:144-148
theorem unverified_synth_breaks_source_transfer :
    Closed P4a.sig (tableM P4a (stdCfg P4a) T4a) T4a ∧ GenericVerified P4a Q4aRev ∧
    ImplsConform P4a Q4aRev T4a ∧ ¬ SynthVerified P4a (stdCfg P4a) Q4aRev T4a ∧
    SynthAgrees P4a (stdCfg P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
```

`synth_disagreement_breaks_source_transfer`:

```lean
-- lean/MonoShim/SourceTransfer.lean:163-168
theorem synth_disagreement_breaks_source_transfer :
    Closed P4a.sig (tableM P4a (cfgRev P4a) T4a) T4a ∧ GenericVerified P4a Q4aRev ∧
    ImplsConform P4a Q4aRev T4a ∧ SynthVerified P4a (cfgRev P4a) Q4aRev T4a ∧
    ¬ SynthAgrees P4a (cfgRev P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    (∀ k ∈ T4a, MeetsAt P4a.sig (tableM P4a (cfgRev P4a) T4a) (Q4aRev k) k) ∧
    ¬ (∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4aRev k) k) := by
```

`PncMeth`:

```lean
-- lean/MonoShim/SourceTransfer.lean:178-184
def PncMeth : Program where
  fns := []
  methods := [(0, [0])]
  impls := [⟨0, 0, .proj 0 (.base 0), .emit 1⟩, ⟨0, 0, .base 1, .emit 2⟩]
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .base 1)]
```

`TncMeth`:

```lean
-- lean/MonoShim/SourceTransfer.lean:186
def TncMeth : List Key := [.meth 0 0 (.proj 0 (.base 0))]
```

`noncanonical_key_breaks_source_transfer`:

```lean
-- lean/MonoShim/SourceTransfer.lean:192-197
theorem noncanonical_key_breaks_source_transfer :
    Closed PncMeth.sig (tableM PncMeth (stdCfg PncMeth) TncMeth) TncMeth ∧
    GenericVerified PncMeth Q4b ∧ ImplsConform PncMeth Q4b TncMeth ∧
    SynthVerified PncMeth (stdCfg PncMeth) Q4b TncMeth ∧
    SynthAgrees PncMeth (stdCfg PncMeth) TncMeth ∧ ¬ CanonicalKeys PncMeth TncMeth ∧
    ¬ (∀ k ∈ TncMeth, MeetsAt PncMeth.sig (srcDef PncMeth) (Q4b k) k) := by
```

`cfgJunkEdges`:

```lean
-- lean/MonoShim/SourceTransfer.lean:217
def cfgJunkEdges (P : Program) : MonoCfg := ⟨fun _ => [.inst 99 []], synthStd P⟩
```

`source_transfer_without_covering_or_edge_closure`:

```lean
-- lean/MonoShim/SourceTransfer.lean:223-230
theorem source_transfer_without_covering_or_edge_closure :
    ¬ CoversRefs P4a.sig (cfgJunkEdges P4a).E ∧
    ¬ EdgesIn (edgesM P4a (cfgJunkEdges P4a)) T4a ∧
    Closed P4a.sig (tableM P4a (cfgJunkEdges P4a) T4a) T4a ∧
    GenericVerified P4a Q4a ∧ ImplsConform P4a Q4a T4a ∧
    SynthVerified P4a (cfgJunkEdges P4a) Q4a T4a ∧
    SynthAgrees P4a (cfgJunkEdges P4a) T4a ∧ CanonicalKeys P4a T4a ∧
    ∀ k ∈ T4a, MeetsAt P4a.sig (srcDef P4a) (Q4a k) k := by
```

`P5`:

```lean
-- lean/MonoShim/Termination.lean:31-37
def P5 : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .guard (.call 1 [.box (.param 0)])⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`P5ok`:

```lean
-- lean/MonoShim/Termination.lean:159-165
def P5ok : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.box (.param 0)]⟩, ⟨false, .drop (.param 0)⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`rank5ok`:

```lean
-- lean/MonoShim/Termination.lean:167-170
def rank5ok : Nat → Nat
  | 0 => 2
  | 1 => 1
  | _ => 0
```

`P5ok_rankCheck_and_collects`:

```lean
-- lean/MonoShim/Termination.lean:172-176
theorem P5ok_rankCheck_and_collects :
    rankCheck P5ok rank5ok = true ∧ assocNormal P5ok = true ∧ SchedOK fifo ∧
    collect (edgesM P5ok (stdCfg P5ok)) fifo [.inst 0 []] 20 =
      some [.dropGlue (.base 0), .dropGlue (.box (.base 0)), .inst 2 [.box (.base 0)],
        .inst 1 [.base 0], .inst 0 []] := by
```

`P5flat`:

```lean
-- lean/MonoShim/Termination.lean:185-191
def P5flat : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .guard (.call 1 [.param 0])⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`P5flat_collects`:

```lean
-- lean/MonoShim/Termination.lean:193-194
theorem P5flat_collects : collect (edgesM P5flat (stdCfg P5flat)) fifo [.inst 0 []] 10 =
    some [.inst 1 [.base 0], .inst 0 []] := by
```

`P5mut`:

```lean
-- lean/MonoShim/Termination.lean:200-207
def P5mut : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.box (.param 0)]⟩,
    ⟨false, .call 1 [.base 0]⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`rankCheck_not_necessary`:

```lean
-- lean/MonoShim/Termination.lean:209-212
theorem rankCheck_not_necessary :
    (∀ rank, rankCheck P5mut rank = false) ∧
    collect (edgesM P5mut (stdCfg P5mut)) fifo [.inst 0 []] 10 =
      some [.inst 2 [.box (.base 0)], .inst 1 [.base 0], .inst 0 []] := by
```

`polyrec_fails_rankCheck_and_diverges`:

```lean
-- lean/MonoShim/Termination.lean:222-224
theorem polyrec_fails_rankCheck_and_diverges :
    (∀ rank, rankCheck P5 rank = false) ∧ assocNormal P5 = true ∧ SchedOK fifo ∧
    ¬ ∃ fuel T, collect (edgesM P5 (stdCfg P5)) fifo [.inst 0 []] fuel = some T := by
```

`P9assoc`:

```lean
-- lean/MonoShim/Termination.lean:249-255
def P9assoc : Program where
  fns := [⟨false, .call 1 [.proj 0 (.base 0)]⟩, ⟨false, .call 1 [.param 0]⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .box (.proj 0 (.base 0)))]
```

`nonnormal_assoc_breaks_termination`:

```lean
-- lean/MonoShim/Termination.lean:282-285
theorem nonnormal_assoc_breaks_termination :
    rankCheck P9assoc (fun _ => 0) = true ∧ assocNormal P9assoc = false ∧ SchedOK fifo ∧
    CanonicalKeys P9assoc [.inst 0 []] ∧
    ¬ ∃ fuel T, collect (edgesM P9assoc (stdCfg P9assoc)) fifo [.inst 0 []] fuel = some T := by
```

`Pempty`:

```lean
-- lean/MonoShim/Termination.lean:295-301
def Pempty : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []
```

`schedBump`:

```lean
-- lean/MonoShim/Termination.lean:304-306
def schedBump : List Key → List Key → List Key
  | .userDrop n :: _, _ => [.userDrop (n + 1), .userDrop (n + 2)]
  | _, _ => []
```

`inadmissible_scheduler_breaks_termination`:

```lean
-- lean/MonoShim/Termination.lean:337-340
theorem inadmissible_scheduler_breaks_termination :
    rankCheck Pempty (fun _ => 0) = true ∧ assocNormal Pempty = true ∧ ¬ SchedOK schedBump ∧
    ¬ ∃ fuel T, collect (edgesM Pempty (stdCfg Pempty)) schedBump
        [.userDrop 0, .userDrop 1] fuel = some T := by
```

`fifo_ok`:

```lean
-- lean/MonoShim/Worklist.lean:115
theorem fifo_ok : SchedOK fifo := by intro w n x; simp [fifo]
```

`lifo_ok`:

```lean
-- lean/MonoShim/Worklist.lean:116
theorem lifo_ok : SchedOK lifo := by intro w n x; simp [lifo, or_comm]
```

`reach_congr`:

```lean
-- lean/MonoShim/Worklist.lean:128-129
theorem reach_congr (e1 e2 : Key → List Key) (roots : List Key)
    (h : ∀ k, Reach e1 roots k → e1 k = e2 k) : ∀ k, Reach e1 roots k ↔ Reach e2 roots k := by
```

### Primary sources

Source facts below were read at the stated revisions; the synthesis drawn from them is in the cards' prior-art notes and under Modeling bridges.

- **rustc**, `rust-lang/rust` commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (documentation and source; not built):
  - `compiler/rustc_monomorphize/src/collector.rs`: module documentation L1–195, quoted at L23–29 (items instantiated locally on demand: constants, vtables, object shims), L46–47 (graph of mono items and uses), L57–59 (collection from the roots), L109–111 (operand position), L114 (drop glue), L122–124 (vtable methods), L130–139 (external items without MIR), L141–154 (eager and lazy strategies; L145–147 the lazy strategy's goal); source L700–710 (`fn monomorphize`, calling `instantiate_mir_and_normalize_erasing_regions`).
  - `compiler/rustc_mir_transform/src/shim.rs`: `build_clone_shim` L508–531 (uses `tuple_like_shim` for tuples); `clone_fields` L658–705, comments L673–678, cleanup drop with `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)` at L694.
  - `compiler/rustc_middle/src/ty/instance.rs`: documentation of `ShimKind::Reify`, L114–118.
  - `compiler/rustc_mir_transform/src/elaborate_drop.rs`: documentation comment of the full drop ladder, L897–912; cleanup half-ladder `vec![Unwind::InCleanup; fields.len() + 1]`, L952.
  - `library/core/src/ptr/mod.rs`: documentation of `ptr::eq`, L2471–2474; of `ptr::fn_addr_eq`, L2558–2559.
- **The Rust Reference**, `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (normative for the language; read, not executed): `src/destructors.md` L10–14 (`destructors.operation`; quoted sentences at L10, L12, L14), L58–59 (`destructors.scope.intro`), L352–355 (`destructors.scope.operands`); `src/attributes/codegen.md` L1046–1047 (`attributes.codegen.track_caller.decay`; quoted sentence at L1047).
- R. Griesemer, R. Hu, W. Kokke, J. Lange, I. L. Taylor, B. Toninho, P. Wadler, N. Yoshida, "Featherweight Go", Proc. ACM Program. Lang. 4 (OOPSLA), pp. 1–29, 2020, doi:10.1145/3428217 (arXiv:2005.11710v4): §2.4 and Fig. 10 (polymorphic recursion), Theorem 5.1 (Decidability), Theorem 5.2 (Monomorphisable), §5.3 (`nomono` is conservative), Theorem 5.4 (Bisimulation).
- S. Ellis, S. Zhu, N. Yoshida, L. Song, "Generic Go to Go: Dictionary-Passing, Monomorphisation, and Hybrid", Proc. ACM Program. Lang. 6 (OOPSLA2), pp. 1207–1235, 2022, doi:10.1145/3563331.
- A. Mycroft, "Polymorphic type schemes and recursive definitions", International Symposium on Programming, LNCS 167, pp. 217–228, 1984, doi:10.1007/3-540-12925-1_41.
- A. Tolmach, D. P. Oliva, "From ML to Ada: Strongly-typed language interoperability via source translation", Journal of Functional Programming 8(4):367–412, 1998, doi:10.1017/S0956796898003086.
- S. Weeks, "Whole-program compilation in MLton", Proc. 2006 ACM Workshop on ML, p. 1, doi:10.1145/1159876.1159877 (a one-page invited-talk abstract).
- J. Wu, Y. Wang, L. Yu, L. Meng, "RustCompCert: A Verified and Verifying Compiler for a Sequential Subset of Rust", arXiv:2602.07455v1 (submitted 7 February 2026; doi:10.48550/arXiv.2602.07455), 2026; a workshop-presentation proposal (submitted to Rust Verify 2026) describing ongoing work on a sequential subset of Rust without polymorphism or traits.
- A. VanHattum, D. Schwartz-Narbonne, N. Chong, A. Sampson, "Verifying Dynamic Trait Objects in Rust", ICSE-SEIP 2022, pp. 321–330, doi:10.1145/3510457.3513031.
- C. A. R. Hoare, "Procedures and parameters: an axiomatic approach", LNM 188, pp. 102–116, 1971, doi:10.1007/BFb0059696.
- K. R. Apt, "Ten Years of Hoare's Logic: A Survey—Part I", ACM TOPLAS 3(4):431–483, 1981, doi:10.1145/357146.357150.
- T. Nipkow, "Hoare Logics for Recursive Procedures and Unbounded Nondeterminism", CSL 2002, LNCS 2471, pp. 103–119, doi:10.1007/3-540-45793-3_8.
- B. H. Liskov, J. M. Wing, "A Behavioral Notion of Subtyping", ACM TOPLAS 16(6):1811–1841, 1994, doi:10.1145/197320.197383.
- P. Lammich, R. Neumann, "A Framework for Verifying Depth-First Search Algorithms", CPP 2015, pp. 137–146, doi:10.1145/2676724.2693165.
- S. Wimmer, P. Lammich, "Worklist Algorithms", Archive of Formal Proofs, 2024, https://isa-afp.org/entries/Worklist_Algorithms.html (identified by its URL; the entry is versioned by the archive, and no immutable revision was recorded).

Novelty: no T3 claim is made. Tiers are T0 (re-derivation) or T1 (folklore made precise); the search for prior mechanizations was not exhaustive.

Observation date: the toolchain tag and every rustc and Reference line range above were checked against the pinned revisions on 2026-11-21.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` in the sources, computes `collectAxioms` for every package declaration (allowed: `propext`, `Classical.choice`, `Quot.sound`), and recomputes, for every Lean name referenced by `results.json` and every name recorded in `audit/statements.json`, the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the types and values of every package constant reachable from the statement; theorem bodies excluded), comparing them with `audit/statements.json`. Its exit status is 0 if and only if every check passes.

A narrower manual check of the main results:

```sh
cd lean
lake build
cat > /tmp/MonoShimAxioms.lean <<'EOF'
import MonoShim
#print axioms Toy.MonoShim.closed_of_edgesIn_covering_total_canonicalRefs_instDefined
#print axioms Toy.MonoShim.runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical
#print axioms Toy.MonoShim.cleanup_edges_missing_break_closure
#print axioms Toy.MonoShim.vtable_edges_missing_break_closure
#print axioms Toy.MonoShim.operand_edges_missing_break_closure
#print axioms Toy.MonoShim.reify_shim_edges_missing_break_closure
#print axioms Toy.MonoShim.ladder_exec_eq_cloneAgg
#print axioms Toy.MonoShim.no_source_only_verdict_correct_for_every_synthesizer
#print axioms Toy.MonoShim.source_defs_verified_yet_program_violates_spec_under_reverse_glue
#print axioms Toy.MonoShim.closed_target_meets_specs_of_generic_impl_synth_verified
#print axioms Toy.MonoShim.closed_target_meets_specs_in_source_semantics
#print axioms Toy.MonoShim.collect_mem_iff_reach
#print axioms Toy.MonoShim.collect_order_independent
#print axioms Toy.MonoShim.polyrec_runs_finite
#print axioms Toy.MonoShim.polyrec_instances_reachable
#print axioms Toy.MonoShim.polyrec_collector_diverges
#print axioms Toy.MonoShim.collect_terminates_of_rankCheck_of_assocNormal
#print axioms Toy.MonoShim.precomputed_and_on_demand_synthesis_same_target
#print axioms Toy.MonoShim.linkUnits_eq_tableM_of_deterministic
#print axioms Toy.MonoShim.canonicalRefs_stdCfg_of_assocNormal
#print axioms Toy.MonoShim.noncanonical_refs_break_closure
#print axioms Toy.MonoShim.collected_set_includes_dead_code_not_minimal
#print axioms Toy.MonoShim.per_crate_collection_has_holes
EOF
lake env lean /tmp/MonoShimAxioms.lean
```

Each `#print axioms` line must list at most `propext`, `Classical.choice` and `Quot.sound` (a declaration that uses no axiom is reported as depending on none). To check whether the findings still hold after a change to the model, rerun both commands: a change to any definition in a statement's closure changes its closure hash, and `support/revalidate.py` then reports which statements are affected. The modeling bridges are revalidated separately by rereading the cited line ranges of `rust-lang/rust` and `rust-lang/reference` at the pinned commits (or at a newer revision, to see whether the documented behaviour changed); no command in this section checks them.
