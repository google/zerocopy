<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Lean 4 Verification Scaling, Negative Test Failure Attribution, and TCB Semantic Mutation Oracles in Anneal

## Summary

- **Warm per-crate verification exhibits a sharp $O(N^2)$ `Proof.lean` kernel
  reduction curve as function count $N$ scales: coalescing $N = 10$ functions
  into one crate reduces per-function verification time by 4.0x (`56.65 ms/fn`
  vs. `227.80 ms/fn` at $N = 1$), whereas $N = 50$ degrades to `5.0401s` and
  `703.1 MB` RSS (`113.28 ms/fn`).** The quadratic growth originates in
  `checkNoDupIds` (`theory/Anneal/MirLemmas.lean:4103-4142`), which constructs a
  right-nested conjunction of $\binom{N}{2}$ pairwise inequality proofs (`x ≠
  y`) over `c.bodies`, `c.functions`, and `c.tcb`, compounded by linear list
  scans (`checkMemTCB` and `findBody`) inside `proveFnsLoop` (`L4424-4453`).
  Basis: Source inspection of `theory/Anneal/MirLemmas.lean:4103-4542` at
  `5d2b5702871baf19c1a42d327ed2e80b231f34d2` and empirical scaling benchmarks in
  `support/attribution_and_mutation_metrics.json`.

- **Standard `Proof.lean` compilation (`Anneal.proveCrate Mir.crate rfl`), `by
  decide`, and `lean --json` all emit the identical unreduced type mismatch
  (`Anneal.checkCrate Mir.crate = []`) on every negative test, but invoking
  `lean --run` on `Anneal.proveCrateOpt Mir.crate` over the already-compiled
  `Mir.olean` extracts the exact `(scope, message)` pair in `0.224s` (`195.1 MB`
  RSS).** Because Lean 4's elaborator does not WHNF-reduce the expected type
  `Anneal.checkCrate Mir.crate = []` when formatting an application type
  mismatch for `rfl`, compiler diagnostics cannot distinguish *which* function
  or obligation failed. Evaluating `IO.println (repr (Anneal.proveCrateOpt
  Mir.crate))` via `lean --run` pinpoints the exact function scope and failure
  reason across all nine negative verification categories without modifying
  `trusted/`.
  Basis: Source inspection of `theory/Anneal/MirLemmas.lean:4232-4542` and
  empirical attribution experiments across 9 negative crates in
  `support/attribution_and_mutation_metrics.json`.

- **Concrete MIR execution cannot use `#eval` pattern-matching on `evalMirStep`
  because `StepResult.silent` wraps a `State → Prop` predicate, but executes
  directly inside the Lean 4 kernel via `ExecNormal` and higher-order
  unification (`.step rfl`).** `StepResult.silent next` is defined as `.choice
  (· = next)` (`trusted/lean/Trusted/StepResult.lean:46-48`), making `next`
  inaccessible to VM pattern matching (`Invalid pattern(s): 's'' is an explicit
  pattern variable, but it only occurs in positions that are inaccessible to
  pattern matching`). Instead, `ExecNormal.step`
  (`theory/Anneal/Lowering.lean:40-43`) states `evalMirStep ... s = .silent s'`
  as an equality, enabling `.step rfl` to unify `?s'` with the concrete
  successor state at each step inside the kernel.
  Basis: Source inspection of `trusted/lean/Trusted/StepResult.lean:34-48` and
  `theory/Anneal/Lowering.lean:35-44`, verified by the kernel-checked probe
  `support/LitmusAndAttributionCanaries.lean`.

- **Live TCB semantic mutation testing of
  `trusted/lean/Trusted/MirSemantics.lean` reveals that 7 of 8 single-line
  semantic mutations (`87.5%`) are killed by recompiling `Anneal.Lowering` and
  `Anneal.MirLemmas`, while mutant `M8` (changing `defaultTrustPolicy.isAllowed
  (.fnVerified _ _)` from `False` to `True` at `MirSemantics.lean:1169`)
  survives all 4,703 lines of `MirLemmas.lean`.** Because
  `crateTheorem_single_fnVerified` and `proveCrateOpt` construct `tcb` lists
  containing only `TCBItem.rustcLowering` entries and discharge `h_no_fn` by
  constructor inequality (`tcbItem_rustcLowering_ne_fnVerified`),
  `MirLemmas.lean` never exercises the fact that `defaultTrustPolicy.isAllowed
  (.fnVerified _ _)` is `False`. Adding the 7-line negative canary
  `canary_defaultTrustPolicy_rejects_fnVerified_waiver`
  (`support/LitmusAndAttributionCanaries.lean:46-50`) kills `M8` immediately.
  Basis: Empirical 8-mutant TCB mutation campaign on
  `trusted/lean/Trusted/MirSemantics.lean` at
  `5d2b5702871baf19c1a42d327ed2e80b231f34d2` recorded in
  `support/attribution_and_mutation_metrics.json` and
  `support/LitmusAndAttributionCanaries.lean`.

## Applicability

| Subject | Kind | Version | Revision |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` | repository | `simplify-trusted` | `5d2b5702871baf19c1a42d327ed2e80b231f34d2` |
| `leanprover/lean4` | repository | `v4.34.1` | `5045d0056413266e57c625dcd7c365b10e377c52` |
| `rust-lang/rust` | repository | `1.98.0-nightly (2026-05-30)` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` |

These findings apply to `joshlf/anneal` at
`5d2b5702871baf19c1a42d327ed2e80b231f34d2` (including the `Trusted.*` semantics
from `main` at `c00e36ade29c57830f07c934774abb347471060c` and `trusted-core` at
`ebac418ccf7c234ae402cf76a491c903bff3be4f`) compiled with Lean `v4.34.1` under
`-DwarningAsError=true -DElab.async=false -Ddebug.skipKernelTC=false -t0`.

## Boundaries

- `anneal-rustc-capture` determinism, dual-profile (`debug` vs. `release`) MIR
  equivalence, `validate_target_crate`, and Rust integration test harness
  selection are covered in the companion report
  [`anneal-integration-test-harness-capture-and-boundary-2026`](../anneal-integration-test-harness-capture-and-boundary-2026/REPORT.md).
- The $O(N^2)$ scaling measurements evaluate `proveCrateOpt` and `checkNoDupIds`
  at `5d2b5702871baf19c1a42d327ed2e80b231f34d2`; replacing `checkNoDupIds` with
  an $O(N \log N)$ sort-and-adjacent-compare check or `RBMap` lookup would shift
  the coalescing sweet spot above $N = 10$.

## Findings

### Cold Prefix Compilation and Warm $O(N^2)$ Per-Crate Scaling

Basis: Empirical compilation benchmarks of all 10 prefix modules (`Trusted.*`
and `Anneal.*`) and synthetic crates of $N \in \{1, 5, 10, 20, 50\}$ functions
in `support/attribution_and_mutation_metrics.json`, paired with source analysis
of `theory/Anneal/MirLemmas.lean:4103-4542`.

#### Cold 10-Module Prefix Compilation Breakdown

`cargo-anneal` compiles ten Lean 4 modules in topological order into
`PREFIX_CACHE` (`trusted/cargo-anneal/src/lib.rs:34-45,1076-1143`) using
`-DwarningAsError=true -DElab.async=false -Ddebug.skipKernelTC=false -t0` with
`cwd="/"` (required because invoking `lean` without `--root` rejects any `.lean`
file whose path does not reside under `cwd` with `input file '...' must be
contained in root directory`). The per-module cold compilation costs are:

| Module | Wall Time (`s`) | Max RSS (`MB`) | `.olean` Size (`KB`) | Share of Cold Build Time |
| :--- | ---: | ---: | ---: | ---: |
| `Trusted.Refinement` | `0.4404` | `182.9` | `325.3` | `2.9%` |
| `Trusted.StepResult` | `0.4436` | `181.2` | `335.7` | `2.9%` |
| `Trusted.MirAst` | `0.8758` | `184.8` | `1,006.8` | `5.8%` |
| `Trusted.MirSemantics` | `1.1583` | `195.3` | `1,411.1` | `7.7%` |
| `Trusted` | `0.2073` | `182.4` | `1,402.1` | `1.4%` |
| `Anneal.Refinement` | `0.2995` | `181.4` | `327.9` | `2.0%` |
| `Anneal.StepResult` | `0.4357` | `181.6` | `350.8` | `2.9%` |
| `Anneal.Lowering` | `2.7076` | `244.2` | `3,123.3` | `17.9%` |
| `Anneal.MirLemmas` | `8.7411` | `437.3` | `8,476.7` | `57.8%` |
| `Anneal` | `0.2628` | `193.9` | `800.8` | `1.7%` |
| **Total (10 modules)** | **`15.1317`** | **`437.3` (peak)** | **`17,540.9`** | **`100.0%`** |

`Anneal.MirLemmas` (`8.7411s`, `57.8%`) and `Anneal.Lowering` (`2.7076s`,
`17.9%`) account for `75.7%` of the cold prefix build. Rebuilding only
`Trusted.MirSemantics`, `Anneal.Lowering`, and `Anneal.MirLemmas` (leaving
`Refinement`, `StepResult`, and `MirAst` cached) takes `11.53–11.94s`.

#### Warm Per-Crate Scaling ($N = 1..50$ Functions) and the Coalescing Sweet Spot

Once `PREFIX_CACHE` is warm, verifying a target crate requires three steps:
running `anneal-rustc-capture` (`~23–30 ms`), compiling `.anneal/Mir.lean`, and
compiling `.anneal/Proof.lean` (`def crate_verified : Trusted.CrateTheorem
Mir.crate := Anneal.proveCrate Mir.crate rfl`). Measuring warm verification as a
single crate scales from $N = 1$ to $N = 50$ public functions (`pub fn f_i(x:
usize) -> usize { x }`):

| Function Count ($N$) | Capture (`s`) | `Mir.lean` (`B`) | `Mir.lean` Compile (`s`) | `Proof.lean` Compile (`s`) | `Proof.lean` Peak RSS (`MB`) | Total Warm Time (`s`) | Per-Function Warm Cost (`ms/fn`) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `1` | `0.0230` | `800` | `0.0972` | `0.1076` | `200.8` | `0.2278` | `227.80` |
| `5` | `0.0284` | `3,104` | `0.1494` | `0.1852` | `210.7` | `0.3630` | `72.60` |
| **`10`** | **`0.0229`** | **`5,984`** | **`0.1678`** | **`0.3758`** | **`221.6`** | **`0.5665`** | **`56.65` (Optimal)** |
| `20` | `0.0240` | `11,814` | `0.2477` | `1.0167` | `285.3` | `1.2884` | `64.42` |
| `50` | `0.0303` | `29,304` | `0.5934` | `5.0401` | `703.1` | `5.6638` | `113.28` |

Two competing effects govern per-function throughput:

1. **Process-Startup Amortization ($N = 1 \to 10$):** Spawning two `lean`
   processes (`Mir.lean` and `Proof.lean`) and mmap-loading `17.5 MB` of prefix
   `.olean`s imposes a fixed `~200 ms` floor per crate. Coalescing 10 positive
   functions into a single litmus crate amortizes this floor and achieves a
   **4.0x speedup** (`56.65 ms/fn` vs. `227.80 ms/fn` at $N = 1$).
2. **Quadratic $O(N^2)$ Kernel Reduction ($N > 15$):** Inside `proveCrateOpt`
   (`theory/Anneal/MirLemmas.lean:4458-4526`), `checkNoDupIds` (`L4103-4142`)
   verifies `List.Nodup` over `c.bodies.map (·.id)`, `c.functions.map (·.name)`,
   and `c.tcb` by recursively calling `checkNotMemId`, constructing a
   right-nested conjunction of $\binom{N}{2}$ decidable inequality proofs that
   the Lean 4 kernel reduces during `rfl` checking. Simultaneously,
   `proveFnsLoop` (`L4424-4453`) performs an $O(N)$ `checkMemTCB` scan and an
   $O(N)$ `findBody` scan for each of the $N$ functions. By $N = 50$,
   `Proof.lean` kernel checking alone takes `5.0401s` and `703.1 MB` RSS.

Consequently, positive integration test suites should **batch independent
functions in groups of $8 \le N \le 15$ per crate**, while keeping negative test
cases at $N = 1$ (or asserting per-function failure scope via `proveCrateOpt`).

### Negative Test Failure Attribution: Solving the Opaque `proveCrate` Error

Basis: Source inspection of `theory/Anneal/MirLemmas.lean:4232-4542` and
empirical comparison of four attribution mechanisms (`M1`–`M4`) across 9
negative crates in `support/attribution_and_mutation_metrics.json`.

#### Why `Anneal.proveCrate Mir.crate rfl` Masks the Failure Reason

In `theory/Anneal/MirLemmas.lean:4232-4542`, the reflective verifier already
computes a structured `ProofError` containing both the failing scope (`"crate"`
or the exact Rust function name `fn.name`) and a human-readable diagnostic
message:

```lean
structure ProofError where
  scope : String
  message : String
  deriving Repr, DecidableEq

def proveCrateOpt (c : Crate) : Except ProofError (PLift (CrateTheorem c)) := ...

def checkCrate (c : Crate) : List String :=
  match proveCrateOpt c with
  | .ok _ => []
  | .error err => [err.message, err.scope]

theorem proveCrate (c : Crate) (h : checkCrate c = []) : CrateTheorem c := ...
```

Despite the comment at `MirLemmas.lean:4528-4531` stating that `checkCrate`
exposes the failure reason in Lean's type mismatch message when `proveCrate
Mir.crate rfl` fails, **Lean 4's elaborator does not WHNF-reduce
`Anneal.checkCrate Mir.crate` before formatting the `Application type mismatch`
diagnostic**. Testing all four candidate attribution mechanisms on negative
crates (`M1`–`M4` in `support/attribution_and_mutation_metrics.json`):

- **`M1` — Standard `Proof.lean` (`Anneal.proveCrate Mir.crate rfl`):** Prints
  `Application type mismatch: The argument rfl has type ?m.2 = ?m.2 but is
  expected to have type Anneal.checkCrate Mir.crate = []`. The error text is
  100% identical across all 9 negative failure modes.
- **`M2` — Tactic `by decide` (`Anneal.proveCrate Mir.crate (by decide)`):**
  Prints `tactic 'decide' proved that the proposition Anneal.checkCrate
  Mir.crate = [] is false`, which also leaves `checkCrate Mir.crate` unreduced.
- **`M3` — `lean --json` on `Proof.lean`:** Wraps the exact unreduced `M1`
  string in JSON (`"data": "Application type mismatch..."`).
- **`M4` — Running `lean --run` on `Anneal.proveCrateOpt Mir.crate` against the
  already-compiled `Mir.olean`:** When `Proof.lean` fails during a negative
  integration test, `.anneal/Mir.olean` has already been compiled (`~0.10s`).
  Invoking `lean --run` on a 3-line runner script:

  ```lean
  prelude
  import Trusted
  import Anneal
  import Mir
  def main : IO Unit :=
    match Anneal.proveCrateOpt Mir.crate with
    | .ok _ => IO.println "OK"
    | .error e => IO.eprintln s!"scope={e.scope} | message={e.message}"
  ```

  completes in **`0.224s`** (`195.1 MB` RSS) and extracts the exact structured
  `(scope, message)` pair across all nine negative categories in
  `MirLemmas.lean`:

| Negative Test Case | `M1` (`proveCrate Mir.crate rfl`) | `M4` (`lean --run` on `proveCrateOpt Mir.crate`) |
| :--- | :--- | :--- |
| 1. `neg_wrong_spec_body` (`pub fn id(x: usize) -> usize { 0 }` with `ensures: result == x`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=id \| message=unproved function body` |
| 2. `neg_nonzero_violates_inv` (`make_nonzero` returning `NonZeroUsize(0)`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=make_nonzero \| message=unproved safe NonZeroUsize function` |
| 3. `neg_nonzero_pub_field` (`pub struct NonZeroUsize(pub usize)` with `invariant: self.0 != 0`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=crate \| message=unsupported ADT inventory` |
| 4. `neg_multi_fn_second_fails` (`good_id` followed by unprovable `bad_id`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=bad_id \| message=unproved function body` |
| 5. `synthetic_empty_crate` (`functions := []`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=crate \| message=crate defines no public functions` |
| 6. `synthetic_dup_body_id` (duplicate `BodyId` in `c.bodies`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=crate \| message=duplicate body IDs` |
| 7. `synthetic_dup_fn_name` (duplicate `fn.name` in `c.functions`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=crate \| message=duplicate function names` |
| 8. `synthetic_fn_verified_waiver` (`TCBItem.fnVerified` in `c.tcb`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=crate \| message=disallowed fnVerified TCB waiver` |
| 9. `synthetic_missing_tcb_waiver` (`c.tcb := []` missing `rustcLowering`) | `expected to have type Anneal.checkCrate Mir.crate = []` | `scope=id \| message=missing TCBItem.rustcLowering waiver` |

This `M4` runner (or a two-line change in `emit_proof_module` replacing
`checkCrate c = []` with `checkCrate c = ["", ""]` on failure, or a diagnostic
helper in `cargo-anneal` tests) ensures negative integration tests never pass
for the wrong reason.

### Concrete Kernel Execution (`ExecNormal`) vs. `#eval` on `StepResult.silent`

Basis: Source inspection of `trusted/lean/Trusted/StepResult.lean:34-48` and
`theory/Anneal/Lowering.lean:35-44`, verified by
`support/LitmusAndAttributionCanaries.lean`.

In `trusted/lean/Trusted/StepResult.lean:34-48`, `StepResult` embeds
deterministic transitions inside demonic nondeterministic choice over a
`Prop`-valued predicate `branches : State → Prop`:

```lean
inductive StepResult (Term : Type u) (State : Type v) : Type (max u v) where
  | choice (Guard : Type v) (branches : State → Prop)
  | terminated (outcome : Term)
  | failed

def StepResult.silent {Term : Type u} {State : Type v}
    (next : State) : StepResult Term State :=
  .choice Empty (· = next)
```

Because `branches : State → Prop` is erased by Lean 4's code generator and lives
in `Prop`, pattern-matching `match evalMirStep ... with | .silent s' => ...` in
a recursive `#eval` fuel loop is rejected by Lean 4 (`Invalid pattern(s): 's''
is an explicit pattern variable, but it only occurs in positions that are
inaccessible to pattern matching: StepResult.choice Empty .(fun x => x = s')`).

Instead, concrete input/output conformance tests execute directly inside the
Lean 4 kernel via `ExecNormal` (`theory/Anneal/Lowering.lean:35-44`):

```lean
inductive ExecNormal (adts : List AdtDecl) (bodies : List BodyDecl)
    (b : MirBody) : MirState → (MirReturn → Prop) → Prop where
  | normal {s : MirState} {ret : MirReturn} {post : MirReturn → Prop} :
      evalMirStep adts bodies b s = .terminated (.normal ret) →
      post ret →
      ExecNormal adts bodies b s post
  | step {s s' : MirState} {post : MirReturn → Prop} :
      evalMirStep adts bodies b s = .silent s' →
      ExecNormal adts bodies b s' post →
      ExecNormal adts bodies b s post
```

When a concrete litmus theorem applies `.step rfl`, Lean 4's higher-order
unifier reduces the left-hand side `evalMirStep adts bodies b s` to
`StepResult.choice Empty (fun x => x = <concrete_next_state>)` and unifies that
term with `.silent ?s'` (`StepResult.choice Empty (fun x => x = ?s')`), binding
`?s'` to `<concrete_next_state>` without requiring fuel or `Decidable`
instances! As verified in `support/LitmusAndAttributionCanaries.lean`:

- `exec_id_42` steps `idCopyBody` on `42 : usize` in 1 `.step rfl` + `.normal
  rfl rfl`.
- `exec_alloc_passthrough_42` steps `allocPassthroughBody` on `42 : usize` in 4
  `.step rfl` transitions + `.normal rfl rfl`.
- `exec_make_nonzero_0` steps `makeNonZeroBody` on `0 : usize` across 9 `.step
  rfl` transitions to `.adt 0 (.usize 1)`.
- `exec_make_nonzero_42` steps `makeNonZeroBody` on `42 : usize` across 12
  `.step rfl` transitions to `.adt 0 (.usize 42)`.

### Live TCB Semantic Mutation Campaign on `Trusted/MirSemantics.lean`

Basis: Empirical 8-mutant campaign injecting single-line semantic faults into
`trusted/lean/Trusted/MirSemantics.lean` at
`5d2b5702871baf19c1a42d327ed2e80b231f34d2` and recompiling `Anneal.Lowering`,
`Anneal.MirLemmas`, and `support/LitmusAndAttributionCanaries.lean`
(`support/attribution_and_mutation_metrics.json`).

Because `Trusted/MirSemantics.lean` is part of the unverified TCB (`trusted/`),
any bug in `MirSemantics.lean` that is not contradicted by `theory/Anneal/` or
an explicit semantic canary could silently weaken `Trusted.CrateTheorem`. We
injected eight single-line semantic mutations (`M1`–`M8`) into
`trusted/lean/Trusted/MirSemantics.lean` while keeping `Refinement`,
`StepResult`, and `MirAst` `.olean`s cached (`~11.5s` per mutant run):

| Mutant ID | Mutated Definition in `Trusted/MirSemantics.lean` | Single-Line Semantic Fault | Outcome vs. Existing `theory/Anneal/` | Wall Time (`s`) | Killing Theorem / Canary |
| :--- | :--- | :--- | :--- | ---: | :--- |
| `M1` | `evalRvalue` (`.binaryOp .eq`) | Invert `.usize a, .usize b` equality (`!decide (a = b)`) | **KILLED** (`Anneal.MirLemmas`) | `11.55` | `makeNonZeroBody_execNormal` (`MirLemmas.lean:1943`) |
| `M2` | `evalOperand` (`.move`) | Skip `deinitPlace` on moved source place (`some (v, s.locals)`) | **KILLED** (`Anneal.MirLemmas`) | `11.74` | Move deinitialization lemma (`MirLemmas.lean:2434`) |
| `M3` | `evalMirStmt` (`.storageLive`) | Omit `bumpGen s.localGens loc.index` on `StorageLive` | **KILLED** (`Anneal.MirLemmas`) | `11.63` | Generation bump proof (`MirLemmas.lean:2195`) |
| `M4` | `evalMirTerminator` (`.return_`) | Drop `retVal.returnRefsOk s activeBody.localCount` check on return | **KILLED** (`Anneal.MirLemmas`) | `11.53` | Return reference validity proof (`MirLemmas.lean:3348`) |
| `M5` | `evalMirTerminator` (`.unreachable`) | Change `.unreachable` from `.failed` (UB) to `.terminated .unwind` | **KILLED** (`Anneal.MirLemmas`) | `11.56` | `MirLemmas.lean:155` (`StepResult.terminated .unwind` vs. `.failed`) |
| `M6` | `evalMirTerminator` (`.assert`) | Change failed `Assert` from `.terminated .unwind` (panic) to `.failed` (UB) | **KILLED** (`Anneal.Lowering`) | `3.42` | `Anneal/Lowering.lean:511` (`StepResult.failed` vs. `.terminated .unwind`) |
| `M7` | `AdmissibleAdtInv` | Flip `decl.allFieldsPubSafe = true` to `false` | **KILLED** (`Anneal.MirLemmas`) | `11.86` | `MirLemmas.lean:949` (`Bool.false = Bool.true`) |
| **`M8`** | **`defaultTrustPolicy.isAllowed` (`L1169`)** | **Change `\| .fnVerified _ _ => False` to `True`** | **SURVIVED** (`rc = 0` across all 4,703 lines of `MirLemmas.lean`!) | `11.94` | **Killed by `canary_defaultTrustPolicy_rejects_fnVerified_waiver`** (`LitmusAndAttributionCanaries.lean:49`) |

#### Why Mutant `M8` Survived `theory/Anneal/` and How the Canary Kills It

In `trusted/lean/Trusted/MirSemantics.lean:1165-1170`, `defaultTrustPolicy`
defines which `TCBItem` waivers a verified crate may assume without proof:

```lean
def defaultTrustPolicy : TrustPolicy where
  isAllowed
    | .rustcLowering _ _ => True
    | .fnVerified _ _ => False
```

If `.fnVerified _ _` is accidentally set to `True` (`M8`), `CrateTheorem` allows
any function to be assumed verified via a `TCBItem.fnVerified` waiver in
`c.tcb`. Yet all 4,703 lines of `theory/Anneal/MirLemmas.lean` compile cleanly
against `M8` (`rc = 0` in `11.94s`) because `crateTheorem_single_fnVerified`
(`MirLemmas.lean:892-910`) and `proveCrateOpt` (`L4409-4418`) only ever prove
*positive* admissibility of `.rustcLowering` waivers and discharge the absence
of `.fnVerified` waivers in `c.tcb` by syntactic constructor inequality
(`tcbItem_rustcLowering_ne_fnVerified`), never referencing the fact that
`defaultTrustPolicy.isAllowed (.fnVerified _ _)` reduces to `False`.

Adding the 7-line negative TCB canary in
`support/LitmusAndAttributionCanaries.lean:46-50`:

```lean
theorem canary_defaultTrustPolicy_rejects_fnVerified_waiver
    (fnName : String) (bodyId : BodyId) :
    ¬ defaultTrustPolicy.isAllowed (.fnVerified fnName bodyId) := by
  intro h
  exact h
```

compiles in `<0.15s` against the unmutated prefix (`rc = 0`) and immediately
rejects `M8` (`rc = 1`, `Type mismatch: h has type defaultTrustPolicy.isAllowed
(TCBItem.fnVerified fnName bodyId) but is expected to have type False`).

## Evidence

- `joshlf/anneal` at `5d2b5702871baf19c1a42d327ed2e80b231f34d2`:
  - `trusted/lean/Trusted/StepResult.lean:34-48` (`StepResult.choice` and
    `StepResult.silent` `Prop`-erased predicate representation).
  - `trusted/lean/Trusted/MirSemantics.lean:1165-1170` (`defaultTrustPolicy`).
  - `theory/Anneal/Lowering.lean:35-44` (`ExecNormal` inductive relation).
  - `theory/Anneal/MirLemmas.lean:892-910` (`crateTheorem_single_fnVerified`),
    `L1890-2120` (`makeNonZeroBody_execNormal`, `newUncheckedBody_execNormal`,
    `getUncheckedNonZeroBody_execNormal`), `L4103-4142` (`checkNoDupIds`
    $O(N^2)$ pairwise conjunction), and `L4232-4542` (`ProofError`,
    `proveCrateOpt`, `checkCrate`, and `proveCrate`).
- Local reproducible probe and data in this package:
  - [`support/LitmusAndAttributionCanaries.lean`](support/LitmusAndAttributionCanaries.lean)
    (kernel-checked `ExecNormal` concrete execution theorems and `M8` negative
    trust-policy canary).
  - [`support/attribution_and_mutation_metrics.json`](support/attribution_and_mutation_metrics.json)
    (cold prefix build table, $N = 1..50$ scaling measurements, 9-case negative
    attribution results, and 8-mutant `MirSemantics.lean` mutation logs).

## Related Reports

- [`anneal-integration-test-harness-capture-and-boundary-2026`](../anneal-integration-test-harness-capture-and-boundary-2026/REPORT.md)
- [`lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`](../lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026/REPORT.md)
- [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md)
- [`anneal-structural-external-calls-and-tcb-mutation-testing-2026`](../anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md)

## Revalidation

Revalidate this report when any of the following change:

1. `theory/Anneal/MirLemmas.lean` replaces `checkNoDupIds` or `proveFnsLoop`
   with sub-quadratic data structures.
2. `theory/Anneal/MirLemmas.lean` or `trusted/cargo-anneal` changes how
   `proveCrate` / `checkCrate` surfaces `ProofError` diagnostics on negative
   crates.
3. `trusted/lean/Trusted/MirSemantics.lean` modifies `defaultTrustPolicy`,
   `evalMirStep`, or `AdmissibleAdtInv`.
