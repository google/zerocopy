<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Two-Stage Trust-Boundary Auditing, Single-File .olean Axiom-Stubbing, and Conservative Extension Laws in Lean 4.34.1

## Summary

Anneal's single-stage trust-boundary checker (`TrustedBoundary.lean`) replays
every constant across `Trusted.*`, `Anneal.*`, `Mir`, and `Proof` inside
`Lean.Kernel.Environment.replay` (`~1.88 s`) and scans all 225 imported and
local `ModuleData` entries in `env.header.moduleData` (`~51 ms`) on every per-CR
`cargo anneal` run. Because `Trusted.*` and `Anneal.*` (`11` modules, `4,650`
constants, `17.11 MB` of `.olean` artifacts) are static across target crates,
splitting verification into a one-time **Stage-1 `preaudit`** (`foundation ++
Trusted ++ Anneal` -> `theory-lock.json`) and a per-crate **Stage-2
`runtime-audit`** (`Mir ++ Proof` replayed over the locked Stage-1 kernel
environment) eliminates redundant kernel replay and module-data scanning without
weakening Anneal's soundness guarantee.

Combining a **Single-`importEnv` + `readModuleData`** Stage-2 architecture with
**Single-File `.olean` Axiom-Stubbing** (converting Stage-1 `.thmInfo` entries
to `.axiomInfo` and pruning unreachable `_private.*._proof_*` subterms via
`readModuleData` + `saveModuleData` with `isModule := false`, **Config 3b**)
reduces Stage-1 `.olean` disk size by **54.6%** (`17.11 MB -> 7.77 MB`;
`MirLemmas.olean` shrinks **9.63x** from `1.71 MB` to `178 KB`, and
`FunctionalTranslation.olean` shrinks **2.50x** from `12.55 MB` to `5.02 MB`),
reduces per-crate `Proof.lean` elaboration time from `320.7 ms` to `261.2 ms`
(**-18.6%**), reduces Stage-2 `runtime-audit` wall-clock time from `2,013.5 ms`
to **`75.2 ms`** (**26.8x speedup**), and cuts peak process RSS during
`runtime-audit` by **43.9%** (`616.5 MiB -> 346.1 MiB`, with only `+49.2 MiB` of
marginal RSS growth after `import_base`).

Mechanized proofs in `support/ConservativityModel.lean` (452 lines, zero
`sorry`, verified under Lean 4.34.1) establish that replacing kernel-replayed
Stage-1 theorems with `.axiomInfo` stubs of identical `(name, levelParams,
type)`—paired with a monotonic 6-feature candidate summary (`axioms`,
`directFeats`, `guardedFeats : Feature -> Finset Feature`) in
`theory-lock.json`—is both **sound and complete** with respect to single-stage
full replay, and that vacuous definitions or theorems in `theory/Anneal/`
(`def BrokenSpec : Prop := True`) cannot help derive `Trusted.CrateTheorem
Mir.crate` (`vacuous_helper_immunity`).

---

## Applicability

These findings apply to:

- **Lean 4.34.1 (`leanprover/lean4:v4.34.1`, commit
  `025fb1be5f4f8cef5fb9ba7ff9cb3cd9eb8aa6cf`)**: specifically the staged
  constant map `Lean.SMap` (`src/lean/Lean/Data/SMap.lean`), `.olean` compaction
  and import finalization (`src/lean/Lean/Environment.lean` and
  `src/runtime/compact.cpp`), kernel replay (`src/lean/Lean/Replay.lean`), the
  C++ kernel typechecker (`src/kernel/type_checker.cpp`,
  `src/kernel/declaration.h`, `src/kernel/environment.cpp`), and synchronous vs.
  asynchronous theorem elaboration (`src/lean/Lean/Elab/MutualDef.lean`,
  `src/lean/Lean/Elab/AddDecl.lean`, `src/lean/Lean/Elab/PreDefinition/Basic.lean`).
- **Anneal (`joshlf/anneal`, commit
  `ca5600a7cf83d1431789c61c6d2bf8fd3ab0b383`)**: specifically the kernel
  boundary checker (`trusted/audit/lean/TrustedBoundary.lean`), the Rust audit
  CLI (`trusted/audit/src/lib.rs`), the trusted core (`trusted/lean/Trusted/`),
  and the untrusted theory library (`theory/Anneal/`).

---

## Findings

### Finding 1: Stage-1 (`map₁`) vs. Stage-2 (`map₂`) Kernel Environment Mechanics and `Kernel.Environment.replay` Worklist Invariants

In Lean 4.34.1, both `Lean.Environment` (`src/lean/Lean/Environment.lean:294`)
and `Lean.Kernel.Environment` (`src/lean/Lean/Environment.lean:265-272`) store
their constant tables in a two-stage map:

```lean
abbrev ConstMap := SMap Name ConstantInfo
```

defined in `src/lean/Lean/Data/SMap.lean:25-30`:

```lean
structure SMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  stage₁ : Bool := true
  map₁   : Std.HashMap α β := ∅
  map₂   : PHashMap α β := ∅
```

During `importModulesCore` and `finalizeImport`
(`src/lean/Lean/Environment.lean:2307-2388`), all constants from imported
`.olean` files are inserted into `privateConstantMap : Std.HashMap Name
ConstantInfo` (`map₁`). At line 2354, `finalizeImport` calls `constants.switch`
(`SMap.switch` at `src/lean/Lean/Data/SMap.lean:71-75`), flipping `stage₁ :=
false`.

Once `stage₁ == false`:

- **Lookups (`SMap.find?` at `src/lean/Lean/Data/SMap.lean:78-83` and C++
  `environment::find` in `src/kernel/environment.cpp`)**: check `map₁` (`O(1)`
  flat hash table) first, falling back to `map₂` (`PHashMap` persistent trie)
  only on a miss.
- **Insertions (`SMap.insert` at `src/lean/Lean/Data/SMap.lean:48-52` and
  `Kernel.Environment.add` at `src/lean/Lean/Environment.lean:1058`)**: insert
  exclusively into `map₂`, leaving `map₁` untouched.
- **Stage-2 Isolation (`SMap.foldStage2` at
  `src/lean/Lean/Data/SMap.lean:111-112`)**: iterates exclusively over `map₂`.

#### `Lean.Kernel.Environment.replay` Worklist Invariant

`Lean.Kernel.Environment.replay` (`src/lean/Lean/Replay.lean:176-190`) takes a
 map `newConstants : Std.HashMap Name ConstantInfo` and a `base : Environment`:

```lean
def replay (newConstants : Std.HashMap Name ConstantInfo) (base : Environment) : IO Environment := do
  let mut remaining : NameSet := ∅
  for (n, _) in newConstants do
    remaining := remaining.insert n
  let (_, s) ← (replayConstants remaining).run { newConstants }
    |>.run { env := base.toKernelEnv, remaining }
  return Environment.ofKernelEnv s.env
```

The replay worklist (`src/lean/Lean/Replay.lean:47-53`) is governed by `isTodo`:

```lean
def isTodo (n : Name) : ReplayM Bool := do
  let r := (← get).remaining
  let p := (← get).pending
  return r.contains n || p.contains n
```

When `replayConstant` (`src/lean/Lean/Replay.lean:106-150`) traverses a constant
`n ∈ newConstants`:

1. It computes the surface expression references `ci.getUsedConstantsAsSet`
   (`src/lean/Lean/Declaration.lean:511-513`: `ci.type.getUsedConstantsAsSet ++
   match ci.value? (allowOpaque := true) with | some v =>
   v.getUsedConstantsAsSet | none => ∅`).
2. It calls `replayConstants usedConstants` (`src/lean/Lean/Replay.lean:74-78`),
   which filters dependencies through `if (← isTodo n) then replayConstant n`.
3. Every constant already in `base.toKernelEnv` (`map₁`) satisfies `n ∉
   newConstants`, so `isTodo n == false`. It is **never added to the replay
   worklist and never re-typechecked**.
4. Instead, when `addDecl` (`src/lean/Lean/Replay.lean:31-35`) calls C++
   `lean_add_decl` (`src/kernel/environment.cpp`), the C++ kernel resolves every
   `Const c lvls` inside `n`'s type and value against `s.env` (`map₁ ∪ map₂`) in
   `O(1)` via `environment::find`.

#### Cross-Stage Collision Allowance (`subsumesInfo`)

When `finalizeImport` encounters a constant name `c` in a newly imported module
that already exists in an earlier imported module, it calls `subsumesInfo`
(`src/lean/Lean/Environment.lean:2248-2301, 2338-2343`). `subsumesInfo` permits
two specific cross-module collisions:

1. **`.thmInfo tval₁` vs. `.thmInfo tval₂` (lines 2258-2263)**: allowed when
   `tval₁.levelParams == tval₂.levelParams && tval₁.type == tval₂.type &&
   tval₁.all == tval₂.all` (used when two modules independently realize the
   same equation theorem via `realizeConst`).
2. **`.thmInfo tval₁` vs. `.axiomInfo aval₂` (or vice versa, lines 2289-2300)**:
   allowed when `tval₁.levelParams == aval₂.levelParams && tval₁.type ==
   aval₂.type && tval₁.all == [aval₂.name] && !aval₂.isUnsafe`.

---

### Finding 2: C++ Kernel Reducibility, `@[irreducible]` vs. `opaque` vs. `.thmInfo` vs. `.axiomInfo`, and Why `constant_info::has_value(false)` Returns `true` for `.thmInfo` (`ProbeKernelReducibility.lean`)

A natural question is whether Stage-1 definitions or proof terms can be hidden
from the C++ kernel during Stage-2 typechecking using `@[irreducible]`,
`ReducibilityHints.opaque`, or `.thmInfo`. Direct inspection of the Lean 4.34.1
elaborator and C++ kernel (`src/kernel/type_checker.cpp`,
`src/kernel/declaration.h`), verified empirically by
`support/ProbeKernelReducibility.lean`, demonstrates why **only `.opaqueInfo`
(for `Type`-valued definitions) and `.axiomInfo` (for `Prop` theorems)** prevent
C++ kernel unfolding.

#### 1. `@[irreducible]` Is Purely an Elaborator/Meta Extension

In `Lean.Elab.addNonRecAux`
(`src/lean/Lean/Elab/PreDefinition/Basic.lean:186-216`), every `DefKind.def` is
compiled to `Declaration.defnDecl` with:

```lean
hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
```

and sent to the kernel via `addDecl` at **line 214** *before* attributes are
applied at **line 216** (`applyAttributesOf #[preDef]
AttributeApplicationTime.afterTypeChecking`). When `@[irreducible]` runs
(`src/lean/Lean/ReducibilityAttrs.lean:51-102, 186-211`), `setReducibilityStatus`
inserts `(declName, .irreducible)` into `reducibilityCoreExt :
MapDeclarationExtension ReducibilityStatus`. It **never modifies** the
`ConstantInfo.defnInfo` stored in `env.constants`. Consequently, inside the C++
kernel, an `@[irreducible] def` is an ordinary `.defnInfo` with
`ReducibilityHints.regular h`.

#### 2. `ReducibilityHints.opaque` on `.defnInfo` Still Unfolds in the C++ Kernel

Even if a `.defnInfo` is constructed directly with `hints :=
ReducibilityHints.opaque`, the C++ kernel unfolds it in two places:

- **`type_checker::whnf` (`src/kernel/type_checker.cpp:555-586, 736-776`)**:
  `is_delta(env(), e)` checks `info->has_value()` without inspecting
  `get_hints()`. Calling `whnf` unconditionally unfolds any `.defnInfo` at the
  head of an expression.
- **`type_checker::lazy_delta_reduction_step`
  (`src/kernel/type_checker.cpp:999-1056`)**:
  - If `t` is a delta-reducible constant (`is_delta(env(), t)` is `true`) and `s`
    is *not* (`!d_s`, e.g., `true`, `0`, or a constructor), lines 1004-1009
    unconditionally unfold `t` via `unfold_names_core(t)` without consulting
    `get_hints()`.
  - If both `t` and `s` have `ReducibilityHints.opaque`,
    `reducibility_hints::compare` (`src/kernel/declaration.cpp:24-35`) returns
    `0` (since `h1.m_kind == h2.m_kind == reducibility_hints_kind::Opaque`),
    causing lines 1046-1047 (`else { return unfold_both(t, s); }`) to unfold
    **both** definitions simultaneously.

#### 3. The `hasValue` Discrepancy Between Lean-Level `Declaration.lean` and C++ `declaration.h`

Lean 4.34.1 has three distinct `hasValue` / `has_value` predicates with
different behaviors on `.thmInfo`:

1. **Lean-level `ConstantInfo.hasValue`
   (`src/lean/Lean/Declaration.lean:495-500`)**:
   ```lean
   def hasValue (info : ConstantInfo) (allowOpaque := false) : Bool :=
     match info with
     | .defnInfo _ => true
     | .thmInfo _  => allowOpaque
     | .opaqueInfo _ => allowOpaque
     | _           => false
   ```
   Here, `ConstantInfo.hasValue (allowOpaque := false)` returns **`false`** for
   `.thmInfo`.
2. **C++ `declaration::has_value()` (`src/kernel/declaration.h:227-230`)**:
   returns `is_theorem() || is_definition() || is_opaque()`.
3. **C++ `constant_info::has_value(bool allow_opaque = false)`
   (`src/kernel/declaration.h:466-468`)**:
   ```cpp
   bool has_value(bool allow_opaque = false) const {
       return is_theorem() || is_definition() || (allow_opaque && is_opaque());
   }
   ```
   Here, `constant_info::has_value(false)` returns **`true` for `is_theorem()`
   (`.thmInfo`)** and **`false` for `is_opaque()` (`.opaqueInfo`) and
   `is_axiom()` (`.axiomInfo`)**!

Why does `.thmInfo` usually not unfold during `is_def_eq`? In
`type_checker::is_def_eq_core` (`src/kernel/type_checker.cpp:1166-1231`), step 6
(`is_def_eq_proof_irrel(t, s)` at line 1202, defined at lines 932-939) executes
**before** step 7 (`lazy_delta_reduction(t, s)` at line 1206). When `t` and `s`
are proofs of propositions (`is_prop(t_type)`), `is_def_eq_proof_irrel` reduces
`is_def_eq(t, s)` to `is_def_eq(infer_type(t), infer_type(s))` in `O(1)` without
unfolding `t` or `s`.

However, whenever the C++ kernel enters `whnf_core` (`type_checker.cpp:768`) or
subsingleton recursor reduction `inductive_reduce_rec` (`type_checker.cpp:637`,
such as reducing `Acc.rec` over a well-founded accessibility proof—explicitly
documented in `src/lean/Lean/Environment.lean:2264-2266`), `is_delta` calls
`info->has_value(false)`, which returns `true` for `.thmInfo` and **unfolds the
theorem's proof body**. Converting Stage-1 `.thmInfo` constants to `.axiomInfo`
makes `info->has_value(false)` strictly `false`, guaranteeing that even
`Kernel.whnf` cannot unfold or deserialize a Stage-1 proof body.

*(Note on Lean 4.34.1 equivalence caching: in `src/kernel/type_checker.h:35-39`
and `src/kernel/type_checker.cpp:1182-1228`, the union-find `equiv_manager`
`m_eqv_manager` is commented out with `/* ... */` and replaced by directed
`m_success` and `m_failure` `expr_pair` hash sets).*

#### Declaration-Kind Comparison Table (`support/ProbeKernelReducibility.lean`)

| Declaration Kind | `ConstantInfo` Constructor | Kernel `hints` | Lean `hasValue (allowOpaque := false)` | C++ `constant_info::has_value(false)` | `Kernel.whnf` Unfolds? | `Kernel.isDefEq` vs. Ground Value Unfolds? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `def` (standard) | `.defnInfo` | `.regular h` | `true` | `true` | **Yes** | **Yes** (`O(fuel)`) |
| `@[irreducible] def` | `.defnInfo` | `.regular h` | `true` | `true` | **Yes** | **Yes** (`O(fuel)`) |
| Raw `.defnInfo` with `.opaque` hints | `.defnInfo` | `.opaque` | `true` | `true` | **Yes** | **Yes** (`O(fuel)`) |
| `opaque d : T := v` | `.opaqueInfo` | N/A | `false` | **`false`** | **No** | **No** (`isDefEq d v = false`) |
| `axiom a : T` (in `Type`) | `.axiomInfo` | N/A | `false` | **`false`** | **No** | **No** |
| `theorem t : P := p` (`Prop`) | `.thmInfo` | N/A | `false` | **`true`** | **Yes** (if `Kernel.whnf` called) | **No** (`is_def_eq_proof_irrel` short-circuits in `O(1)`) |
| `axiom t : P` (`Prop` stub) | `.axiomInfo` | N/A | `false` | **`false`** | **No** | **No** (`is_def_eq_proof_irrel` short-circuits in `O(1)`) |

#### Empirical Kernel Benchmark (`support/ProbeKernelReducibility.lean`)

`support/ProbeKernelReducibility.lean` measures C++ kernel `addDecl` time for an
`Eq.refl` proof over `heavyIrred fuel 0` (`@[irreducible] def` performing
`fuel * 20` `UInt64` modular Mix64 rounds) versus `heavyThm fuel 0` (`.thmInfo`
whose proof body forces `heavyIrred fuel 0 = computedVal` via `Eq.refl`):

| `fuel` | `@[irreducible] def` Kernel `Eq.refl` (`us`) | Raw `.defnInfo (.opaque)` Kernel `Eq.refl` (`us`) | `.thmInfo` Application Kernel Check (`us`) | `.thmInfo` vs. `@[irreducible]` Speedup |
| ---: | ---: | ---: | ---: | ---: |
| `200` | `4,659 us` | `4,752 us` | `59 us` | **79.0x** |
| `500` | `12,188 us` | `11,729 us` | `58 us` | **210.1x** |
| `1000` | `23,932 us` | `23,365 us` | `29 us` | **825.2x** |
| `2000` | `46,772 us` | `46,778 us` | `62 us` | **754.4x** |

---

### Finding 3: Formal Conservative Extension, Cut-Elimination (`Deriv.linkAxioms`), Statement-Origin Invariance, and Vacuous-Helper Immunity (`ConservativityModel.lean`)

`support/ConservativityModel.lean` (452 lines, zero `sorry`) mechanizes a formal
meta-theory of Lean 4's type theory and Anneal's 5-origin trust-boundary
partition:

```lean
inductive Origin where
  | foundation -- Init.* / Lean.*
  | trusted    -- Trusted.*
  | theory     -- Anneal.*
  | mir        -- Mir.*
  | proof      -- Proof.*
  deriving DecidableEq, Repr
```

#### 1. Definitional Equality Depends Only on Value-Bearing Constants (`statement_origin_invariance`)

In CIC/Lean 4, the computation rules ($\beta$, $\delta$, $\iota$, $\zeta$) unfold
only value-bearing constants (`.defnInfo`, `.ctorInfo`, `.recInfo`, `.quotInfo`).
Neither `.thmInfo` nor `.axiomInfo` participates in `isDefEq` on proposition
types (`Trusted.CrateTheorem Mir.crate`). Let `SameComputablePrefix E₁ E₂` hold
whenever `E₁` and `E₂` agree on all value-bearing declarations on `{.foundation,
.trusted, .theory, .mir}` and agree on the signatures `(name, levelParams, type)`
of all declarations. Then (`support/ConservativityModel.lean:115-129`,
`#print axioms statement_origin_invariance -> [propext]`):

```lean
theorem statement_origin_invariance
    (E₁ E₂ : Env) (hPref : SameComputablePrefix E₁ E₂) (t u : Expr)
    (ht : ∀ c ∈ Expr.consts t, (E₁.originOf c).isComputablePrefix = true)
    (hu : ∀ c ∈ Expr.consts u, (E₁.originOf c).isComputablePrefix = true) :
    DefEq E₁ t u ↔ DefEq E₂ t u
```

Because `Trusted.CrateTheorem` has origin `.trusted` and `Mir.crate` has origin
`.mir`, the statement `Trusted.CrateTheorem Mir.crate` denotes the **exact same
mathematical proposition** whether `Anneal.*` theorems are stored as `.thmInfo`
or `.axiomInfo`.

#### 2. Cut-Elimination (`Deriv.linkAxioms`) and Axiom-Footprint Preservation (`linked_axioms_subset_allowed`)

Given a Stage-1 derivation tree `hBase : ∀ a ∈ S, ∃ d : Deriv E_base a.type,
d.axiomsUsed ⊆ AllowedAxioms` and a Stage-2 derivation tree `d_staged : Deriv
(E_base.axiomize S) P`, recursive cut-elimination (`Deriv.linkAxioms` at
`support/ConservativityModel.lean:183-199`) substitutes each `.useAxiom a` leaf
(`a ∈ S`) with its Stage-1 derivation `hBase.choose a`, yielding a single-stage
derivation `d_full : Deriv E_base P` whose axiom footprint is bounded by the
union (`support/ConservativityModel.lean:217-253`, `[propext]`):

```lean
theorem linked_axioms_subset_allowed
    (E : Env) (S : Finset DeclName) (AllowedAxioms : Finset DeclName)
    (hS : ∀ a ∈ S, E.kindOf a = some .thm)
    (hBase : ∀ a ∈ S, ∃ d : Deriv E (E.typeOf a), d.axiomsUsed ⊆ AllowedAxioms)
    {P : PropType} (d : Deriv (E.axiomize S) P)
    (hStaged : d.axiomsUsed ⊆ AllowedAxioms ∪ S) :
    (d.linkAxioms E S hS hBase).axiomsUsed ⊆ AllowedAxioms
```

#### 3. Bidirectional Soundness and Completeness (`staged_precompilation_sound_and_complete`)

Combining `Deriv.linkAxioms` (Stage 2 -> Single Stage) with `Deriv.weakenToAxioms`
(Single Stage -> Stage 2) proves (`support/ConservativityModel.lean:269-306`,
**zero axioms** `[]`):

```lean
theorem staged_precompilation_sound_and_complete
    (E : Env) (S : Finset DeclName) (AllowedAxioms : Finset DeclName)
    (hS : ∀ a ∈ S, E.kindOf a = some .thm)
    (hBase : ∀ a ∈ S, ∃ d : Deriv E (E.typeOf a), d.axiomsUsed ⊆ AllowedAxioms)
    (P : PropType) :
    (∃ d_staged : Deriv (E.axiomize S) P, d_staged.axiomsUsed ⊆ AllowedAxioms ∪ S) ↔
    (∃ d_full : Deriv E P, d_full.axiomsUsed ⊆ AllowedAxioms)
```

#### 4. Vacuous-Helper Immunity (`vacuous_helper_immunity`)

Suppose a bug or adversary in `theory/Anneal/` defines a vacuous specification
`def BrokenSpec (c : Trusted.Crate) : Prop := True` and proves `theorem
broken_sound (c : Trusted.Crate) : BrokenSpec c := True.intro`. When Stage 2
imports `broken_sound` as an `.axiomInfo` stub `axiom broken_sound (c :
Trusted.Crate) : BrokenSpec c`, can `Proof.lean` exploit that axiom to prove
`Trusted.CrateTheorem Mir.crate` for a buggy crate?

**No.** Because `broken_sound` has a genuine Stage-1 proof `True.intro` using
$\emptyset \subseteq \text{AllowedAxioms}$, any Stage-2 derivation of
`Trusted.CrateTheorem Mir.crate` using `broken_sound` can be linked via
`Deriv.linkAxioms` to a derivation in the base environment without `broken_sound`
(`support/ConservativityModel.lean:325-336`, **zero axioms** `[]`):

```lean
theorem vacuous_helper_immunity
    (E : Env) (AllowedAxioms : Finset DeclName)
    (broken_thm : DeclName) (hThm : E.kindOf broken_thm = some .thm)
    (d_trivial : Deriv E (E.typeOf broken_thm))
    (hTrivialClean : d_trivial.axiomsUsed ⊆ AllowedAxioms)
    (TargetTheorem : PropType)
    (d_exploit : Deriv (E.axiomize {broken_thm}) TargetTheorem)
    (hExploitClean : d_exploit.axiomsUsed ⊆ AllowedAxioms ∪ {broken_thm}) :
    ∃ d_real : Deriv E TargetTheorem, d_real.axiomsUsed ⊆ AllowedAxioms
```

#### 5. Why a Flat Unconditional Candidate Summary Is Incomplete (`flat_summary_incomplete_counterexample` vs. `conditional_summary_sound_and_complete`)

If Stage 1 recorded only a flat set `candUsed(c) : Finset Feature` per constant,
it would face an impossibility on `@[vetted]` bridge definitions such as:

```lean
@[vetted] def bridge (x : Nat) : Nat := Trusted.candidate "mir_ast" x
```

Inside `bridge`, the reference to `"mir_ast"` sits inside `Trusted.candidate
"mir_ast" ...`. Thus `bridge` itself has `directFeats = ∅`, and a caller that
wraps `bridge` in `Trusted.candidate "mir_ast" (bridge 0)` requires **zero**
enabled candidate features (`flat_summary_incomplete_counterexample`,
`support/ConservativityModel.lean:414-430`, `[]`), whereas an unguarded caller
requires `"mir_ast"`. Recording the pair `(directFeats(c), guardedFeats(c) :
Feature -> Finset Feature)` per constant is both sound and complete for arbitrary
nesting depths (`conditional_summary_sound_and_complete`,
`support/ConservativityModel.lean:437-443`, `[]`).

---

### Finding 4: Two-Stage Trust-Boundary Architecture (`preaudit` + `theory-lock.json` + Single-`importEnv` `runtime-audit`) and the Monotonic 6-Feature Fixed-Point Law (`directCandidateFeatures` + `deferredCandidateEdges`)

#### 1. Exact Partition of the 12 `TrustedBoundary.lean` Invariants Across Stage 1 and Stage 2

All 12 invariants enforced by Anneal's single-stage `TrustedBoundary.lean`
partition cleanly into **Stage-1 `preaudit`** (`foundation ++ Trusted ++ Anneal`
-> `theory-lock.json`) and **Stage-2 `runtime-audit`** (`Mir ++ Proof` over
locked Stage 1):

| # | Invariant (`TrustedBoundary.lean`) | Stage-1 `preaudit` (`foundation ++ Trusted ++ Anneal`) | Stage-2 `runtime-audit` (`Mir ++ Proof` over Locked Stage 1) |
| :-: | :--- | :--- | :--- |
| **1** | **Foundation lock** (`verifyFoundationLock`, lines 881-912) | Verify `foundation-lock.json` against `Init.*`/`Lean.*` modules; bind `foundationLockSha256` into `theory-lock.json`. | Verify `foundation-lock.json` (or `theory-lock.json` digest) against loaded `Init.*`/`Lean.*` `.olean`s. |
| **2** | **Import graph provenance** (`verifyImportGraph`, lines 914-926) | Verify all non-foundation imports of `Trusted.*` and `Anneal.*` stay within `Trusted.* ∪ Anneal.*`. | Verify `Mir` imports only `Foundation ∪ Trusted ∪ Anneal` and `Proof` imports only `Foundation ∪ Trusted ∪ Anneal ∪ {Mir}`. |
| **3** | **Local constant classification & namespace isolation** (`collectLocals`, lines 518-558) | Classify all constants in `Trusted.*` and `Anneal.*`; reject `Mir.*`, `Proof.*`, or unknown roots. | Inspect only `Mir.olean` and `Proof.olean` via `readModuleData`; reject any constant whose root is not `Mir` or `Proof` unless it is a valid `realizeConst` equation/splitter of a Stage-1 constant. |
| **4** | **Declaration-kind policy** (`verifyDeclKinds`, lines 560-599) | Enforce `Trusted.*` kind rules (no `unsafe`/`partial`, axioms only `[vetted]`/`[candidate]`, inductives `[vetted]`/`[candidate]`) and `Anneal.*` kind rules (no axioms, no `unsafe`/`partial`). | Enforce `Mir.*` kind rules (no axioms, no `unsafe`/`partial`) and `Proof.*` kind rules (`verify_crate` is `.thmInfo`, no axioms, no `unsafe`/`partial`). |
| **5** | **`Trusted.candidate` syntax & feature-name registry** (`candidateSyntaxError?`, lines 435-466) | Validate all `Trusted.candidate` applications in `Trusted.*` and `Anneal.*` against the 6-feature registry. | Validate all `Trusted.candidate` applications in `Mir.*` and `Proof.*`. |
| **6** | **Vetted-type ownership & constructor non-contamination** (`buildTrustedOwnerMap`, `checkTrustedNonContamination`, lines 601-745) | Fully check `Trusted.*` and populate `ownerMap : HashMap Name Name` in `theory-lock.json`. | Load `ownerMap` from `theory-lock.json` (no new `Trusted.*` constants can exist in Stage 2). |
| **7** | **Stage-1 kernel replay** (`Kernel.Environment.replay` on `Trusted.* ∪ Anneal.*`) | Replay all `4,650` constants in `Trusted.* ∪ Anneal.*` once during `preaudit`. | **Skipped (`0 ms`)**: Stage-1 `.olean`s are hash-verified against `theory-lock.json` and loaded into `map₁`. |
| **8** | **Stage-2 kernel replay** (`Kernel.Environment.replay` on `Mir.* ∪ Proof.*`) | N/A | Replay only the `~65` constants in `Mir.olean` and `Proof.olean` against `base.toKernelEnv` (`map₁`) in **`~2.2 ms`**. |
| **9** | **Envelope check on `Mir.crate` and `Proof.verify_crate`** (`verifyCrateEnvelope`, lines 928-969) | Confirm `Trusted.Crate` and `Trusted.CrateTheorem` exist in `Trusted.*`, have `levelParams == []`, and depend on zero candidate features. | Confirm `Mir.crate : Trusted.Crate` (`.defnInfo`, `levelParams == []`), `Proof.verify_crate : Trusted.CrateTheorem Mir.crate` (`.thmInfo`, `levelParams == []`), and `Mir.crate` reaches zero candidate features. |
| **10** | **Reachable closure & axiom policy** (`verifyProofClosure`, lines 768-830) | Compute transitive `axioms : Array Name` for every constant `c ∈ Trusted.* ∪ Anneal.*` and store in `theory-lock.json`. | Traverse Stage-2 DAG from `Proof.verify_crate` and `Mir.crate`; on Stage-1 constants, union precomputed `summary.axioms` from `theory-lock.json` in `O(1)`. |
| **11** | **Unconditional & deferred `Trusted.candidate` feature tracking** (lines 774-821) | Compute `(directFeats, guardedFeats)` for every constant `c ∈ Trusted.* ∪ Anneal.*` via the 6-feature fixed point and store in `theory-lock.json`. | Traverse Stage-2 DAG with `activeGuard?`; on Stage-1 constants, union `directFeats` (or route to `deferred[g]`) and union `guardedFeats` into `deferred`, then run the 6-feature fixed point. |
| **12** | **No open expressions (`hasLooseBVars`)** (`exprEdges`, lines 479-481) | Verify `!e.hasLooseBVars` at top level of every `Trusted.*` and `Anneal.*` declaration. | Verify `!e.hasLooseBVars` at top level of every `Mir.*` and `Proof.*` declaration (with `allowLooseBVarsInSubexpr = true` inside binder-under-`candidate` subexpressions). |

#### 2. The Monotonic 6-Feature Fixed-Point Law

Anneal's candidate feature registry
(`trusted/audit/lean/TrustedBoundary.lean:69-77`) is a finite 6-element lattice:

$$\mathcal{F} = \{\texttt{refinement},\; \texttt{step\_result},\; \texttt{memory},\; \texttt{mir\_ast},\; \texttt{mir\_semantics},\; \texttt{rustc\_capture}\}, \quad |\mathcal{F}| = 6.$$

For every Stage-1 constant $c \in \text{Trusted} \cup \text{Anneal}$, Stage 1
computes (`support/SingleImportTwoStageBoundary.lean:458-534`):

- $\text{axioms}(c) \subseteq \text{AxiomNames}$: all foundation and `Trusted.*`
  axioms transitively reachable from $c$ (never treating stubbed Stage-1
  `Anneal.*` theorems as axioms).
- $\text{directFeats}(c) \subseteq \mathcal{F}$: candidate features reachable
  from $c$ along unguarded paths, closed under Stage-1 guarded transitions:
  $$F_{k+1} = F_k \cup \bigcup_{g \in F_k} \text{guardedFeats}(c)(g)$$
  which converges in at most $|\mathcal{F}| = 6$ iterations.
- $\text{guardedFeats}(c) : \mathcal{F} \to \mathcal{P}(\mathcal{F})$: for each
  feature $g \in \mathcal{F}$, the set of candidate features reachable inside a
  `Trusted.candidate g body` guard within $c$ (or transitively within
  declarations called by $c$ under guard $g$).

When Stage 2 encounters a Stage-1 constant $d$ during `verifyProofClosure` under
an optional Stage-2 guard `activeGuard?`
(`support/SingleImportTwoStageBoundary.lean:699-716`):

- **If `activeGuard? == none` (unguarded Stage-2 call)**: Stage 2 unions
  $\text{directFeats}(d)$ into `directCandidateFeatures` and unions
  $\text{guardedFeats}(d)(g)$ into `deferredCandidateEdges[g]` for each $g$.
- **If `activeGuard? == some g₀` (Stage-2 call inside `Trusted.candidate g₀
  ...`)**: Stage 2 routes $\text{directFeats}(d)$ into
  `deferredCandidateEdges[g₀]` and unions $\text{guardedFeats}(d)(g)$ into
  `deferredCandidateEdges[g]` for each $g$.

Stage 2 then runs the same monotonic 6-feature fixed point over
`directCandidateFeatures` and `deferredCandidateEdges`.

#### 3. Single-`importEnv` + `readModuleData` Stage-2 Architecture

A naive Stage-2 implementation calls `importModules` twice in the same process:
once on `allMods := foundation ++ trusted ++ theory ++ #[Mir, Proof]` and a
second time on `baseMods := foundation ++ trusted ++ theory` (`53.8 ms` extra),
and iterates over all 225 modules in `env.header.moduleData` (`50.8 ms`).

Does `importModules #[Mir, Proof]` mutate any Stage-1 constant in `map₁`? In
`src/lean/Lean/Environment.lean:2315-2354`, `finalizeImport` inserts constants
from `Mir` and `Proof` into `privateConstantMap` unless a constant name collides
with an already-imported Stage-1 constant (which happens only when `Proof.lean`
independently realizes an equation/splitter theorem via `realizeConst`, where
`subsumesInfo` keeps the existing Stage-1 `ConstantInfo`).

Therefore, Stage 2 needs only **one `importModules` call** (`import_base` on
`baseMods := foundation ++ trusted ++ theory` with `loadExts := false`,
`support/SingleImportTwoStageBoundary.lean:555-630, 773-932`):

1. **Single `importModules` (`import_base`, `69.9 ms`)**: imports `foundation ++
   trusted ++ theory` once into `baseEnv`.
2. **Direct `readModuleData` (`98 us`)**: reads `Mir.olean` and `Proof.olean`
   directly via `readModuleData`, inspecting only the `~65` declarations in those
   two files rather than scanning `415,436` constants across 225 modules.
3. **Combined `verifyAndCollectDirectCrateData` (`607 us` vs. `50,826 us`, an
   83.7x speedup)**: classifies all constants in `Mir.olean` and `Proof.olean`,
   enforces declaration-kind rules, validates any cross-stage `realizeConst`
   constants against `baseEnv`, and builds `toReplay : Std.HashMap Name
   ConstantInfo`.
4. **Stage-2 Kernel Replay (`2,213 us`)**: runs `baseEnv.replay toReplay`,
   producing `finalEnv : Environment` whose `map₁` holds Stage 1 and whose
   `map₂` holds the kernel-checked `Mir` and `Proof` constants.
5. **Envelope + Closure Audit (`344 us`)**: runs `verifyCrateEnvelope` and
   `verifyProofClosure` on `finalEnv` using `theory-lock.json`.

---

### Finding 5: Six Boundary-Audit Vulnerabilities and Cross-Stage Seams Discovered and Resolved (`foundation-lock.json` / `--prefix-cache-dir` unhashed `.olean`s; `hasLooseBVars` under `Trusted.candidate` binders; pure-source `-DElab.async=false` `verify_crate.{v}` universe-parameter spoofing; cross-stage `realizeConst` in `Proof.olean`; deferred `Trusted.candidate` guard laundering; and `dep == depOwner` false-positive guard-dispatch coupling)

During the design and red-team verification of the two-stage boundary auditor
(`support/ProbePrecompileThreats.lean`, `support/ProbeTwoStagePreAudit.lean`,
and `support/SingleImportTwoStageBoundary.lean`), six boundary vulnerabilities
and cross-stage seams were identified and closed.

#### Vulnerability 1: Unhashed Foundation `.olean`s and Redundant Full Replay Under `--prefix-cache-dir` (`trusted/audit/src/lib.rs:1117-1173, 1676-1803`)

In `trusted/audit/src/lib.rs`:

1. `Checker::tool_admission` (lines 1117-1173) verified `lean --version` and
   checked that `lean --print-libdir` was a non-empty directory (`!s.is_empty()`),
   and `verify_foundation_lock` (`TrustedBoundary.lean:881-912`) checked only the
   module import graph (`m.imports`) against `foundation-lock.json` without
   computing SHA-256 digests over the `Init/*.olean` files on disk.
2. `materialize_shared_prefix_cache` (lines 1711-1803) validated cached
   `Trusted/*.olean` and `Anneal/*.olean` files using only `regular(path,
   "cached module artifact")` (existence + non-directory check), without
   cryptographic digests.
3. Even when `--prefix-cache-dir` was passed to `cargo-anneal`,
   `TrustedBoundary.lean:832-873, 971-972` still executed `emptyEnv.replay
   locals.toReplay` over **every** constant in `Trusted.*`, `Anneal.*`, `Mir.*`,
   and `Proof.*` (`~1.88 s`) on every crate verification.

**Resolution:** `preaudit` hashes every foundation module (`Init.*`/`Lean.*`)
and every Stage-1 module (`Trusted.*`/`Anneal.*`), recording both
`foundationLockSha256` and per-module `.olean` SHA-256 digests (`artifactSha256`)
in `theory-lock.json` (`support/SingleImportTwoStageBoundary.lean:69-88,
536-628`). Stage-2 `runtime-audit` verifies those SHA-256 digests before calling
`importModules`.

#### Vulnerability 2: Latent `hasLooseBVars` Rejection on Extracted `Trusted.candidate` Subexpressions Under Binders (`TrustedBoundary.lean:479-503, 702, 782, 795`)

In `trusted/audit/lean/TrustedBoundary.lean:479-503`:

```lean
partial def exprEdges (e : Expr) : Except String ExprScan := do
  if e.hasLooseBVars then
    throw "open expression in stored declaration"
```

When `exprEdges` encounters `Trusted.candidate "<feat>" body` inside a `lam`,
`forallE`, or `letE` binder—for example:

```lean
@[vetted] def binderGuarded (x : Nat) : Nat :=
  (fun y => Trusted.candidate "mir_ast" (candAstHelper + y)) x
```

`exprEdges` extracts `body = candAstHelper + (.bvar 0)` and stores it in
`DeferredGuard.subexpr`. Subsequently, `checkTrustedNonContamination` (line 702)
and `verifyProofClosure` (lines 782, 795) call `expressionEdges
deferred.subexpr`, which calls `exprEdges (candAstHelper + (.bvar 0))`. Because
`.bvar 0` was bound by the outer `fun y => ...` that was stripped when `body`
was extracted, `deferred.subexpr.hasLooseBVars` is `true`, and `exprEdges`
falsely throws `"open expression in stored declaration"` on completely valid
closed Lean definitions!

**Resolution (`support/SingleImportTwoStageBoundary.lean:160-189`):** Parameterize
`exprEdges (e : Expr) (allowLooseBVarsInSubexpr : Bool := false)`: enforce
`!e.hasLooseBVars` at the top level of every stored declaration's `type` and
`value` (`allowLooseBVarsInSubexpr = false`), and pass
`allowLooseBVarsInSubexpr = true` when scanning extracted `DeferredGuard.subexpr`
fragments.

#### Vulnerability 3: Pure-Source `-DElab.async=false` Universe-Parameter Spoofing on `Proof.verify_crate.{v}` and `Mir.crate.{v}` (`TrustedBoundary.lean:948-958`)

In `trusted/audit/lean/TrustedBoundary.lean:948-958`, `verifyCrateEnvelope`
checked:

```lean
unless mirCrateCi.type == expectedCrateType do ...
unless proofCi.type == expectedTheoremType do ...
```

Crucially, `ConstantInfo.type` does not include `ConstantVal.levelParams`! Can a
pure `.lean` file (without editing `.olean` bytes) produce a `Proof.verify_crate`
theorem with non-empty `levelParams = [v]` while keeping `proofCi.type ==
Trusted.CrateTheorem Mir.crate`?

**Yes, specifically because `trusted/audit/src/lib.rs:1229` invokes `lean
-DElab.async=false`!** Here is the exact compiler chain in Lean 4.34.1:

1. Normally (`Elab.async=true`), `Lean.Elab.Command.elabMutualDef`
   (`src/lean/Lean/Elab/MutualDef.lean:1237-1243`) takes the `elabAsync` path
   (`MutualDef.lean:1114-1140`), which runs `levelMVarToParamHeader` on the
   theorem header *before* elaborating the proof body, so universe variables
   mentioned only in the proof body are rejected with `"unbound level param"`.
2. When `-DElab.async=false` is passed (`trusted/audit/src/lib.rs:1229`),
   `MutualDef.lean:1243` takes `elabSync` (`MutualDef.lean:1100-1112`), which
   elaborates both the type and the proof body before calling
   `addPreDefinitions` (`src/lean/Lean/Elab/PreDefinition/Basic.lean:337`).
3. Inside `addPreDefinitions`, `getLevelParamsPreDecls`
   (`src/lean/Lean/Elab/PreDefinition/Basic.lean:68-70`) collects universe
   parameters from **both** `preDef.type` **and `preDef.value`**:
   ```lean
   for preDef in preDefs do
     s := collectLevelParams s preDef.type
     s := collectLevelParams s preDef.value
   ```
4. It then calls `sortDeclLevelParams scopeParams allUserLevelParams s.params`
   (`src/lean/Lean/Elab/DeclUtil.lean:79-81`). Any universe variable declared via
   `universe v` in `Proof.lean` is in `scopeParams`, so a proof body mentioning
   `let _ : PUnit.{v} := PUnit.unit` produces `Proof.verify_crate.{v} :
   Trusted.CrateTheorem Mir.crate` with `levelParams = [`v]` from pure `.lean`
   source!

**Resolution (`support/SingleImportTwoStageBoundary.lean:659-670`):** Explicitly
require `mirCrateCi.levelParams.isEmpty` and `proofCi.levelParams.isEmpty` in
`verifyCrateEnvelope` (and `crateTypeCi.levelParams.isEmpty` and
`crateThmCi.levelParams.isEmpty` in Stage 1).

#### Vulnerability 4: Cross-Stage `realizeConst` Equation and Splitter Constants Emitted Into `Proof.olean`

When tactics in `Proof.lean` (`simp`, `rw`, `unfold`, `split`) unfold a Stage-1
definition from `Anneal.*` or `Trusted.*` whose equation or match-splitter
theorems were not pre-generated during Stage 1, `Lean.Elab.realizeConst`
generates them on the fly during Stage 2 and writes them into `Proof.olean`'s
`ModuleData.constants` under the **Stage-1 namespace** (for example,
`Anneal.evalHelper.eq_1`, `Trusted.chainedGate.eq_1`, or
`_private.Proof.0.Trusted.chainedGate.match_1.splitter`).

This creates four failure modes in a naive boundary checker:

1. **Namespace rejection**: `collectLocals` sees a constant in `Proof.olean`
   whose root namespace is `Anneal` or `Trusted` (or `_private.Proof.0.Trusted`)
   and rejects it if it assumes Stage-2 modules only define `Mir.*`/`Proof.*`.
2. **Duplicate realization collision**: If both `Anneal` (Stage 1) and `Proof`
   (Stage 2) realize `Anneal.evalHelper.eq_1`, Stage 2 must verify that the
   Stage-2 copy satisfies `sameRealizedThmHeader` (`subsumesInfo`: both are
   `.thmInfo` with identical `levelParams`, `type`, and `all == [name]`) and skip
   re-adding it (`support/SingleImportTwoStageBoundary.lean:288-293, 577-582`).
3. **Spoofed `Trusted.*` / `Anneal.*` declarations in `Proof.olean`**: If Stage 2
   blindly allowed any `Anneal.*` or `Trusted.*` constant in `Proof.olean`, a
   hostile `Proof.lean` could open `namespace Trusted` and inject a new
   definition. Stage 2 prevents this via `realizedRootPrefix?`
   (`support/SingleImportTwoStageBoundary.lean:251-285`), which strips `.eq_N`,
   `.eq_def`, `.eq_unfold`, `.congr_simp`, `.splitter`, and `_private.<mod>.0.`
   suffixes/prefixes and requires the underlying root definition `rootName` to
   **already exist in `baseEnv` (`map₁`)** as a value-bearing constant.
4. **Candidate-guard laundering through `Proof`-realized `@[vetted]` equations**:
   When `Proof.lean` realizes `Trusted.vettedFn.eq_1` for a Stage-1 `@[vetted]`
   definition `Trusted.vettedFn` whose body uses `Trusted.candidate "mir_ast"`,
   the theorem `Trusted.vettedFn.eq_1` has `Trusted.candidate "mir_ast"` in its
   RHS type, **not** wrapped in `Trusted.candidate` at the theorem level.
   Because `Trusted.vettedFn.eq_1` is not itself marked `@[vetted]` in
   `Proof.olean`, `verifyProofClosure` would falsely flag `"mir_ast"` as an
   unguarded candidate feature unless `isVettedRealizedEqInStage2` checks
   `lockSummary.vettedDefs.contains rootName`
   (`support/SingleImportTwoStageBoundary.lean:596-600`).

#### Vulnerability 5: Direct and Deferred `Trusted.candidate` Laundering Across Axiom-Stubbed Stage-1 `.olean`s (Plus `waived` and `Lean.reduceBool` Threats)

`support/ProbePrecompileThreats.lean` tests four cross-stage attack vectors:

- **Threat 1 (Direct Candidate Laundering via Stubbed Stage-1 Theorem)**: An
  `Anneal.*` theorem `laundered_mir_ast_thm : True` references a
  `@[candidate "mir_ast"]` axiom inside its proof term (`let _ := ...; trivial`).
  When `laundered_mir_ast_thm` is stubbed to `.axiomInfo` (`type = True`), its
  `.olean` representation has zero references to `"mir_ast"`. **Defense**: Stage 1
  computes `directFeats = ["mir_ast"]` from the unstubbed `.thmInfo` body before
  stubbing and writes it to `theory-lock.json`; Stage 2 rejects any proof using
  `laundered_mir_ast_thm` unless `"mir_ast"` is enabled.
- **Threat 2 (Vacuous Spec / `waived` Obligation Laundering)**: A Stage-1 helper
  sets `VerificationResult.waived := [fnId]`. **Defense**: `Trusted.CrateTheorem`
  requires `VerificationResult ... []` (`waived = []`) in the **type** of
  `Proof.verify_crate`, so the C++ kernel rejects any mismatch via `is_def_eq`
  regardless of Stage-1 stubbing.
- **Threat 3 (Deferred `Trusted.candidate` Guard Laundering)**: A `@[vetted]`
  Stage-1 definition `vetted_stage1_bridge` guards a use of `cand_step_result`
  behind `Trusted.candidate "mir_ast"`. **Defense**: `theory-lock.json` records
  `guardedFeats = [("mir_ast", ["step_result"])]`, so if Stage 2 enables
  `"mir_ast"`, the 6-feature fixed point automatically activates `"step_result"`
  and rejects the crate unless `"step_result"` is also enabled.
- **Threat 4 (`Lean.reduceBool` / `Lean.reduceNat` Native-Code Bypass)**: In
  `src/kernel/type_checker.cpp:614-635`, `reduce_native` executes compiled native
  code if `Lean.reduceBool` or `Lean.reduceNat` is applied to a closed constant.
  In `Init/Core.lean:2361-2379`, both `Lean.reduceBool` and `Lean.reduceNat` are
  `.opaqueInfo` declarations whose values reference `axiom Lean.trustCompiler :
  True`. **Defense**: Any Stage-1 or Stage-2 declaration mentioning
  `Lean.reduceBool` or `Lean.reduceNat` transitively pulls `Lean.trustCompiler`
  into `axioms` and is rejected by the 3-axiom allowlist (`propext`,
  `Quot.sound`, `Classical.choice`).

#### Vulnerability 6: False-Positive Guard-Dispatch Coupling When `dep == depOwner` (`TrustedBoundary.lean:715-721`)

In `trusted/audit/lean/TrustedBoundary.lean:715-721`,
`checkTrustedNonContamination` checks every constant `c` in `Trusted.*` that has
a value body (`ci.hasValue (allowOpaque := true)`) and is not itself registered
in `ownerMap`:

```lean
for dep in valueScan.consts do
  if let some depOwner := ownerMap.get? dep then
    throw s!"trusted declaration '{name}' matches on or constructs vetted type '{depOwner}' via '{dep}'..."
```

Because `buildTrustedOwnerMap` (line 670) inserts `ownerMap :=
ownerMap.insert name name` for the `@[vetted]` inductive type `I` itself (in
addition to its constructors `I.mk` and recursors `I.rec`, `I.casesOn`), any
`@[vetted]` function whose body mentions the **type name `I`** (for example, as a
type annotation `(x : I)` or inside `@Eq I x x`) has `dep = I` and `depOwner =
I`, falsely throwing `"matches on or constructs vetted type 'I' via 'I'"` even
though it neither constructs nor eliminates `I`!

**Resolution (`support/SingleImportTwoStageBoundary.lean:358-363`):** Guard the
check with `if dep != depOwner then ...` so that referencing the type former `I`
is permitted while referencing any constructor (`I.mk`), recursor (`I.rec`), or
matcher (`match_1`) owned by `I` (`dep != depOwner`) is still rejected.

---

### Finding 6: Single-File `.olean` Axiom-Stubbing (`readModuleData` + `.thmInfo -> .axiomInfo` + `saveModuleData`), Lean 4 `module` System Comparison, Byte-Level `.olean` Breakdown, and End-to-End Runtime Benchmarks (Configs 0 through 3d, Double-Import vs. Single-Import + `readModuleData`)

Even after Stage-2 `runtime-audit` skips replaying Stage-1 constants, both
`lean Proof.lean` (during proof elaboration) and `runtime-audit` (during
`import_base`) must still load and mmap the Stage-1 `.olean` files from disk.
We investigated two families of techniques to strip Stage-1 proof bodies from
disk: Lean 4's experimental `module` system (**Configs 2a/2b**) and single-file
`.olean` post-processing via `readModuleData` + `saveModuleData` (**Configs
3a/3b/3c/3d**).

#### 1. How Lean 4's `module` System Splits `.olean` / `.olean.server` / `.olean.private` and Why It Is Incompatible With Anneal

When a file begins with the `module` header (`env.header.isModule == true`):

1. **`Lean.Kernel.Environment.addDeclAux`
   (`src/lean/Lean/Elab/AddDecl.lean:101-161`)**: when elaborating a theorem, it
   creates a private `_proof_1` constant in the full kernel environment (`env`),
   replaces the public theorem's value in the **exported** environment
   (`exportedEnv`) with `mkAppN (mkConst auxDeclName ...) ...`, and sets
   `checked := asyncEnv.checked` (which still contains the full proof body).
2. **`saveModuleData` (`src/lean/Lean/Environment.lean:1858-1918`)**: when
   `env.header.isModule == true`, Lean writes **three** files instead of one:
   - `<Mod>.olean` (`exported`): contains public constants where every `.thmInfo`
     has its `value` replaced by an application of its private `_proof_1`
     constant (`3.66 MB` across Anneal's 11 Stage-1 modules).
   - `<Mod>.olean.server`: contains server/elaborator extension entries (`2.37
     MB`).
   - `<Mod>.olean.private`: contains all private constants, including the full
     `_proof_1` bodies (`10.65 MB`).

Testing Configs 2a and 2b across Anneal (`support/ProbeAxiomStubRuntime.lean`)
exposed **five structural incompatibilities**:

1. **Viral `module` header requirement (`src/lean/Lean/Environment.lean:2115-2119`)**:
   a non-`module` file cannot import a `module` file without `import all`.
2. **`meta import` drags 33 extra `Init.*` modules into `env.header.modules`
   (`src/lean/Lean/Environment.lean:2125-2146`)**: under `module`, macro/syntax
   definitions require `meta import`, which sets `importAll := !isMeta` (`false`)
   and causes `importModulesCore` to promote private transitive imports of `Init`
   into the module graph, failing `verifyFoundationLock` with `"unexpected
   foundation module 'Init.Data.Array.BasicAux' outside foundation-lock.json"`.
3. **Hidden private transitive `Init.*` imports (`Init.WFTactics`,
   `Init.Data.Nat.Mod`)**: `module` disables transitive re-export of private
   `Init` imports unless explicitly imported in `theory/Anneal/`.
4. **Equation-generation privacy mismatch (`&& !isProp` in
   `src/lean/Lean/Elab/MutualDef.lean:1382-1384`)**: under `module`, a public
   `def` without `@[expose]` has its `match_1` auxiliary declaration marked
   `private`. For `Prop`-valued definitions such as `noAliasBefore`
   (`theory/Anneal/FunctionalTranslation.lean:3247`), `MutualDef.lean:1382-1384`
   skips `mkUnfoldEq` because of `&& !isProp`, and `MatchEqs.lean:458` later
   fails with `"unknown constant 'Anneal.Refinement.noAliasBefore.match_1'"`
   when `rw [noAliasBefore]` runs inside a `theorem` proof block (where
   `isPrivatePrefix` is active).
5. **All 3 `.olean*` files are loaded under standard `LEAN_PATH` (Config 2a),
   while loading only `.olean` via `ImportArtifacts` (Config 2b) drops 90
   reachable `_private` constants (`closure_visited = 292` vs. `382`)**:
   `findOLeanParts` (`src/lean/Lean/Environment.lean:2023-2040`) loads `.olean`,
   `.olean.server`, and `.olean.private` whenever they exist on disk (`16.68 MB`
   total), yielding zero I/O savings in Config 2a; whereas hiding
   `.olean.private` in Config 2b strips `_private` helper functions and
   `_proof_1` targets from the environment, leaving dangling constant references
    inside `.thmInfo.value` and omitting 90 reachable constants from the audit
   closure!

#### 2. Single-File `.olean` Axiom-Stubbing (`readModuleData` + `.thmInfo -> .axiomInfo` + `saveModuleData`)

By contrast, post-processing standard single-file `.olean` artifacts (`isModule
== false`) after Stage-1 `preaudit` via `readModuleData` and `saveModuleData`
(`support/ProbeAxiomStubRuntime.lean` and
`support/SingleImportTwoStageBoundary.lean:1058-1155`) requires **zero source
changes** to `Trusted.*`, `Anneal.*`, `Mir.lean`, or `Proof.lean`, and preserves
`closure_visited = 382` identically to the unstubbed baseline.

We evaluated four single-file compaction levels:

- **Config 3a (`.thmInfo -> .axiomInfo`)**: converts every `.thmInfo tval` in
  `ModuleData.constants` and `ModuleData.constNames` to:
  ```lean
  .axiomInfo { name := tval.name, levelParams := tval.levelParams, type := tval.type, isUnsafe := false }
  ```
- **Config 3b (`.thmInfo -> .axiomInfo` + unreachable `_private.*._proof_*`
  pruning — Recommended)**: in addition to converting `.thmInfo` to `.axiomInfo`,
  computes the transitive constant closure reachable from all surviving types and
  non-`.thmInfo` values in the module, and removes any `_private.*._proof_*` or
  `_private.*._simp_*` auxiliary theorem that was referenced only by the stripped
  `.thmInfo` proof bodies.
- **Config 3c (`elab-minimal`: Config 3b + stripping 5 LCNF/IR codegen
  `envExtensions`)**: strips `Compiler.LCNF.monoExt`,
  `Compiler.LCNF.declMapExt`, `Compiler.LCNF.baseExt`,
  `Compiler.LCNF.impureSigExt`, and `IR.functionSummariesExt` from
  `ModuleData.entries` (saving an additional `1.66 MB` across the 11 modules).
- **Config 3d (`audit-only`: Config 3b + `entries := #[]`)**: strips all
  `ModuleData.entries` (`5.01 MB` total `.olean` size, used only if a separate
  audit-only `.olean` directory is maintained; cannot be used by `lean
  Proof.lean` because `lean Proof.lean` needs `matchPatternAttr` and `simpExtension`
  entries).

#### 3. Per-Module `.olean` Disk Size Across All 11 Stage-1 Modules

| Stage-1 Module | Constants (`.thmInfo`) | Config 0/1 Baseline (B) | Config 2a All 3 `.olean*` (B) | Config 2b `.olean` Only (B) | Config 3a `.thmInfo -> .axiomInfo` (B) | Config 3b + Prune `_proof_*` (B) | Config 3c `elab-minimal` (B) | Config 3d `audit-only` (B) | Config 3b vs. Baseline |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Trusted/Core.olean` | `138` (`0`) | `176,472` | `191,824` | `78,024` | `176,472` | `176,472` | `124,040` | `85,784` | `0.0%` (`1.00x`) |
| `Trusted/Memory.olean` | `190` (`0`) | `174,568` | `191,720` | `80,960` | `174,568` | `174,568` | `120,032` | `94,408` | `0.0%` (`1.00x`) |
| `Trusted/MirAst.olean` | `677` (`0`) | `647,784` | `706,664` | `282,424` | `647,784` | `647,784` | `460,552` | `370,128` | `0.0%` (`1.00x`) |
| `Trusted/MirSemantics.olean` | `223` (`1`) | `664,536` | `732,728` | `495,536` | `664,296` | `664,296` | `539,304` | `484,064` | `-0.04%` (`1.00x`) |
| `Trusted/Refinement.olean` | `31` (`0`) | `28,152` | `30,152` | `11,032` | `28,152` | `28,152` | `18,432` | `11,648` | `0.0%` (`1.00x`) |
| `Trusted/RustcCapture.olean` | `7` (`0`) | `3,536` | `3,760` | `2,920` | `3,536` | `3,536` | `3,536` | `1,632` | `0.0%` (`1.00x`) |
| `Trusted/StepResult.olean` | `37` (`0`) | `27,824` | `29,888` | `13,808` | `27,824` | `27,824` | `18,744` | `14,720` | `0.0%` (`1.00x`) |
| `Trusted.olean` | `0` (`0`) | `1,256` | `1,400` | `1,256` | `1,256` | `1,256` | `1,256` | `1,256` | `0.0%` (`1.00x`) |
| `Anneal/MirLemmas.olean` | `299` (`188`) | `1,709,392` | `1,622,872` | `93,656` | `182,784` | **`177,560`** | `133,312` | `102,424` | **`-89.6%` (`9.63x`)** |
| `Anneal/FunctionalTranslation.olean` | `2,980` (`310`) | `12,545,816` | `12,131,808` | `2,331,136` | `5,041,840` | **`5,015,656`** | `3,974,728` | `3,569,208` | **`-60.0%` (`2.50x`)** |
| `Anneal.olean` | `1,068` (`28`) | `1,133,288` | `1,041,472` | `266,280` | `850,464` | **`850,464`** | `715,928` | `277,736` | **`-25.0%` (`1.33x`)** |
| **Total (11 Stage-1 modules)** | **`4,650` (`527`)** | **`17,112,624`** (`17.11 MB`) | **`16,684,288`** (`16.68 MB`) | **`3,657,032`** *(unsound)* | **`7,798,976`** (`7.80 MB`) | **`7,767,568`** (**`7.77 MB`**) | **`6,109,864`** (`6.11 MB`) | **`5,013,008`** (`5.01 MB`) | **`-54.6%` (`2.20x`)** |

#### 4. Exact Byte-Level Breakdown of `FunctionalTranslation.olean` (`5.02 MB` in Config 3b)

Why does `Anneal/FunctionalTranslation.olean` retain `5,015,656 B` (`5.02 MB`)
after stripping all `310` `.thmInfo` proof bodies (`-7.53 MB`)? Using incremental
`saveModuleData` ablation in `support/ProbeAxiomStubRuntime.lean`, we measured
the exact byte contribution of every component inside Lean's compacted region
(`src/runtime/compact.cpp`):

| Component Inside `FunctionalTranslation.olean` (Config 3b) | Count | Compacted Bytes | Share of `5.02 MB` | Why Present / Whether Needed |
| :--- | ---: | ---: | ---: | :--- |
| **1. `.defnInfo` value bodies** (`274` user `def`s + `172` `match_N` + `9` `_sunfold` + `3` `brecOn`/`below`) | `458` defs | **`2,440,944 B`** | **48.67%** | **Required**: C++ kernel `is_def_eq` (`type_checker.cpp`) and `Proof.lean` `simp`/`rw` unfold these `def` bodies during Stage-2 verification. |
| **2. `ModuleData.entries` (`PersistentEnvExtension`s)** | `40` exts (`5,409` entries) | **`1,405,520 B`** | **28.02%** | `1,040,928 B` (74.1% of `entries`) are 5 LCNF/IR codegen extensions (`monoExt` `430,728 B`, `declMapExt` `312,648 B`, `baseExt` `233,904 B`, `impureSigExt` `45,184 B`, `functionSummariesExt` `10,232 B`). The remaining `364,592 B` are `matchPatternAttr` (`184,384 B`), `simpExtension` (`55,664 B`), `docStringExt` (`25,992 B`), etc. |
| **3. `.defnInfo` types, inductives, `.ctorInfo`, `.recInfo`, and shared `Name`/`Level` DAG** | `2,670` non-thm consts | **`995,728 B`** | **19.85%** | **Required**: kernel type signatures, inductive eliminators, and shared `Expr`/`Name` nodes. |
| **4. `.axiomInfo` type signatures (stubbed theorems)** | `310` stubbed thms | **`151,624 B`** | **3.02%** | **Required**: theorem statement propositions (`tval.type`) checked by `Proof.lean` and Stage-2 `replay`. |
| **5. `extraConstNames` + `imports` header** | `405` names | **`21,840 B`** | **0.44%** | **Required**: module header and realized constant registration. |
| **Total (`FunctionalTranslation.olean` in Config 3b)** | **`2,980` consts** | **`5,015,656 B`** | **100.00%** | — |

#### 5. End-to-End Runtime and Memory Benchmarks (Configs 0 through 3d, Double-Import vs. Single-Import + `readModuleData`)

All benchmarks below were executed on the real Anneal codebase (`Trusted.*` +
`Anneal.*` + `Mir.lean` + `Proof.lean`, 5 iterations after warm-up, median
reported, verified by `support/ProbeAxiomStubRuntime.lean` and
`support/SingleImportTwoStageBoundary.lean`):

| Configuration | Stage-1 `.olean` Disk Size | `lean Proof.lean` Elab Time (`ms`) | Audit `import_base` (`ms`) | Audit `import_2nd_env` (`ms`) | Audit `collect_locals` / `readModuleData` (`ms`) | Audit `kernel_replay` (`ms`) | Audit `envelope + closure` (`ms`) | **Total Stage-2 Audit (`ms`)** | **Speedup vs. Config 0** | Peak RSS (`MiB`) | Audit RSS Delta (`MiB`) | Sound & Complete? |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| **Config 0: Single-Stage Full Replay** (`TrustedBoundary.lean` baseline) | `17.11 MB` | `320.7 ms` | `78.4 ms` | `0.0 ms` | `49.7 ms` | `1,885.1 ms` | `0.30 ms` | **`2,013.5 ms`** | `1.00x` | `616.5 MiB` | `+252.9 MiB` | Yes (`382` consts) |
| **Config 1 (Double-Import): Two-Stage Unmodified `.olean`s** | `17.11 MB` | `320.7 ms` | `83.9 ms` | `53.8 ms` | `50.8 ms` | `3.55 ms` | `0.46 ms` | **`192.9 ms`** | `10.44x` | `412.2 MiB` | `+99.1 MiB` | Yes (`382` consts) |
| **Config 1 (Single-Import + `readModuleData`): Unmodified `.olean`s** | `17.11 MB` | `320.7 ms` | `74.4 ms` | **`0.0 ms`** | **`0.71 ms`** | `2.38 ms` | `0.34 ms` | **`79.3 ms`** | **`25.39x`** | `361.9 MiB` | **`+49.2 MiB`** | Yes (`382` consts) |
| **Config 2a: Lean 4 `module` System (All 3 `.olean*` in `LEAN_PATH`)** | `16.68 MB` | `315.4 ms` | `82.1 ms` | `51.0 ms` | `56.6 ms` | `3.67 ms` | `0.48 ms` | **`194.2 ms`** | `10.37x` | `409.5 MiB` | `+97.8 MiB` | Fragile (requires 33 extra `Init` lock entries) |
| **Config 2b: Lean 4 `module` System (`.exported` `.olean` Only)** | `3.66 MB` | `261.9 ms` | `77.6 ms` | `46.6 ms` | `55.6 ms` | `3.52 ms` | `0.39 ms` | **`184.0 ms`** | `10.94x` | `397.7 MiB` | `+85.4 MiB` | **NO** (drops 90 `_private` consts: `292` vs. `382`) |
| **Config 3a (Double-Import): `.thmInfo -> .axiomInfo`** | `7.80 MB` | `261.9 ms` | `78.9 ms` | `49.2 ms` | `52.5 ms` | `3.58 ms` | `0.46 ms` | **`185.0 ms`** | `10.88x` | `396.3 MiB` | `+83.6 MiB` | Yes (`382` consts) |
| **Config 3b (Double-Import): `.thmInfo -> .axiomInfo` + Prune `_proof_*`** | `7.77 MB` | `261.2 ms` | `78.2 ms` | `48.6 ms` | `51.2 ms` | `3.55 ms` | `0.46 ms` | **`182.3 ms`** | `11.04x` | `396.0 MiB` | `+83.4 MiB` | Yes (`382` consts) |
| **Config 3b (Single-Import + `readModuleData` — RECOMMENDED)** | **`7.77 MB` (`-54.6%`)** | **`261.2 ms` (`-18.6%`)** | **`69.9 ms`** | **`0.0 ms`** | **`0.71 ms`** | **`2.21 ms`** | **`0.34 ms`** | **`75.2 ms`** | **`26.78x`** | **`346.1 MiB` (`-43.9%`)** | **`+49.2 MiB`** | **Yes (`382` consts)** |
| **Config 3c (Single-Import): Config 3b + Strip 5 LCNF/IR Extensions** | `6.11 MB` (`-64.3%`) | `258.4 ms` (`-19.4%`) | `69.1 ms` | `0.0 ms` | `0.70 ms` | `2.20 ms` | `0.34 ms` | **`74.3 ms`** | **`27.10x`** | `344.2 MiB` | `+49.0 MiB` | Yes (breaks `native_decide` on Stage 1) |
| **Config 3d (Single-Import): Config 3b + Strip All `entries`** | `5.01 MB` (`-70.7%`) | *N/A (cannot elab `Proof.lean`)* | `68.0 ms` | `0.0 ms` | `0.69 ms` | `2.19 ms` | `0.34 ms` | **`73.1 ms`** | **`27.54x`** | `341.8 MiB` | `+48.8 MiB` | Audit-only (requires dual `.olean` dirs) |

#### Why Config 3b + Single-Import Is the Optimal Production Architecture

1. **Eliminates both dominant Stage-2 bottlenecks**: `kernel_replay` drops by
   **852x** (`1,885.1 ms -> 2.21 ms`), `collect_locals` drops by **70x–83.7x**
   (`49.7 ms -> 0.71 ms`, including `98 us` for `readModuleData` on `Mir.olean`
   and `Proof.olean`), and `import_2nd_env` (`53.8 ms`) is completely eliminated
   (`0.0 ms`).
2. **Speeds up `lean Proof.lean` elaboration by 18.6% (`320.7 ms -> 261.2 ms`)**
   and cuts Stage-1 `.olean` size by **54.6% (`17.11 MB -> 7.77 MB`)** using a
   single `.olean` directory shared by both `lean Proof.lean` and
   `runtime-audit`.
3. **Avoids internal compiler-extension coupling**: Config 3c saves only an
   extra `0.9 ms` (`75.2 ms -> 74.3 ms`) and `1.66 MB` by hardcoding internal
   Lean compiler extension names (`Compiler.LCNF.monoExt`, etc.). Config 3b uses
   only the public `ModuleData` API (`constants`, `constNames`,
   `extraConstNames`) and preserves full elaborator compatibility.

---

## Boundaries

1. **Stage-1 `.defnInfo` Bodies Cannot Be Stripped if Unfolded by Stage 2**:
   While Stage-1 `.thmInfo` proof bodies can be replaced with `.axiomInfo` stubs
   because of proof irrelevance (`is_def_eq_proof_irrel`, Finding 2) and cut
   elimination (`Deriv.linkAxioms`, Finding 3), Stage-1 `.defnInfo` value bodies
   (`2.44 MB` in `FunctionalTranslation.olean`) are required whenever `Proof.lean`
   or Stage-2 `is_def_eq` unfolds those definitions. Converting a Stage-1
   `.defnInfo` to `.opaqueInfo` or `.axiomInfo` makes it definitionally
   inequivalent to its RHS (`ProbeKernelReducibility.lean`).
2. **`theory-lock.json` Must Be Bound to Both `foundation-lock.json` and Every
   Stage-1 `.olean` SHA-256 Digest**: Axiom-stubbing Stage-1 `.olean` files is
   sound **only** when paired with `theory-lock.json` generated from the
   unstubbed Stage-1 environment *before* `.thmInfo -> .axiomInfo` stubbing, and
   verified via SHA-256 over the stubbed `.olean` files *before* Stage-2
   `importModules`.
3. **Single-`importEnv` Requires Rejecting Non-Realized Cross-Namespace
   Constants in `Mir.olean` and `Proof.olean`**: Because `readModuleData`
   inspects the raw `ModuleData.constants` arrays of `Mir.olean` and
   `Proof.olean`, `verifyAndCollectDirectCrateData` must reject any declaration
   outside the `Mir.*` and `Proof.*` namespaces unless it passes
   `realizedRootPrefix?` against `baseEnv.checked.get` and (when colliding with
   an existing Stage-1 realization) satisfies `sameRealizedThmHeader`.

---

## Evidence

All claims, theorems, vulnerability reproducers, and benchmarks in this report
are backed by self-contained, warning-free Lean 4.34.1 artifacts in `support/`:

- [`support/ConservativityModel.lean`](support/ConservativityModel.lean) (452
  lines, SHA-256
  `9fa5dc4018783b185275c3089870cc0241f3062680464eef782920b51bd5ed86`):
  Mechanized formalization of Anneal's 5-origin partition and all 6
  conservativity meta-theorems (`statement_origin_invariance`,
  `linked_axioms_subset_allowed`, `staged_precompilation_sound_and_complete`,
  `vacuous_helper_immunity`, `flat_summary_incomplete_counterexample`,
  `conditional_summary_sound_and_complete`), with zero `sorry`.
- [`support/ProbeKernelReducibility.lean`](support/ProbeKernelReducibility.lean)
  (230 lines, SHA-256
  `da91db6ea689fa75d6a78246bf59e40f9c1206584d5b595085204a4efe4856ea`):
  Empirical C++ kernel probe testing `@[irreducible] def`, raw `.defnInfo` with
  `ReducibilityHints.opaque`, `.opaqueInfo`, `.thmInfo`, and `.axiomInfo` under
  `Kernel.whnf` and `Kernel.isDefEq` across `fuel = 200, 500, 1000, 2000`.
- [`support/ProbePrecompileThreats.lean`](support/ProbePrecompileThreats.lean)
  (383 lines, SHA-256
  `e7b17d248439e9f621525f950accd83941d593c0d257aadf382c1f3abe41a1e7`):
  End-to-end threat suite reproducing and verifying defenses against direct
  candidate laundering (Threat 1), `waived` obligation tampering (Threat 2),
  deferred `Trusted.candidate` guard laundering (Threat 3), and
  `Lean.reduceBool` native-evaluation bypass (Threat 4).
- [`support/ProbeTwoStagePreAudit.lean`](support/ProbeTwoStagePreAudit.lean)
  (651 lines, SHA-256
  `6710c085670f7ea7d46e9b2527ddc74d766dd88c64e27c048f91c0c6c1800848`):
  Prototype two-stage boundary auditor (`preaudit` + `runtime-audit`) measuring
  double-import Stage-2 latency against single-stage full replay.
- [`support/ProbeAxiomStubRuntime.lean`](support/ProbeAxiomStubRuntime.lean)
  (430 lines, SHA-256
  `21a5196ef1fbfd192a444a6b77e804b2e3a2bb4e81dbe99d77dbec043edda613`):
  Empirical benchmark and byte-level `.olean` analyzer across Configs 0, 1, 2a,
  2b, 3a, 3b, 3c, and 3d on the 11 Stage-1 modules of Anneal.
- [`support/SingleImportTwoStageBoundary.lean`](support/SingleImportTwoStageBoundary.lean)
  (1,405 lines, SHA-256
  `94b02641581a2b470df710a42fcaeae90c143404ae7b42f106280f3172eae422`):
  Production-grade single-`importEnv` + `readModuleData` two-stage boundary
  auditor implementing `preaudit`, `runtime-audit`, `stub-oleans` (Config 3b),
  `benchmark`, and `self-test` (10 automated positive and negative security
  tests covering all 6 vulnerabilities and cross-stage `realizeConst` seams).

---

## Revalidation

To revalidate the mechanized proofs and empirical probes from this report
directory using Lean 4.34.1:

```bash
# 1. Verify the mechanized conservativity meta-theorems (zero sorry)
lean -DwarningAsError=true support/ConservativityModel.lean

# 2. Run the C++ kernel reducibility and ConstantInfo.has_value probe
lean -DwarningAsError=true support/ProbeKernelReducibility.lean

# 3. Run the 4-threat cross-stage security suite
lean -DwarningAsError=true support/ProbePrecompileThreats.lean

# 4. Typecheck the two-stage preaudit/runtime-audit and .olean stubbing suites
lean -DwarningAsError=true support/ProbeTwoStagePreAudit.lean
lean -DwarningAsError=true support/ProbeAxiomStubRuntime.lean
lean -DwarningAsError=true support/SingleImportTwoStageBoundary.lean
```

To run the full 10-case security self-test and the end-to-end Anneal benchmark
with `support/SingleImportTwoStageBoundary.lean` inside an Anneal checkout
containing compiled `.olean` artifacts:

```bash
lean --run support/SingleImportTwoStageBoundary.lean self-test
lean --run support/SingleImportTwoStageBoundary.lean benchmark <path-to-anneal-build-dir>
```
