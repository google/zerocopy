# Lean 4 Kernel Memory Ceilings, `maxRecDepth` Cliffs, and Per-Body MIR Proof Sharding

## Summary

Verifying multi-function Rust crates against captured Mid-level Intermediate Representation (MIR) in Lean 4 `v4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`) under Anneal's Pass 1 boundary (`joshlf/anneal` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`) encounters four distinct runtime, kernel, and elaborator bottlenecks rooted in Lean's C++ kernel and elaborator architecture:

1. **Per-Process `-M` Ceiling vs. Per-Declaration `type_checker::state` Retention:** The `-M` (`--memory`) CLI flag installs a global byte cap checked every `LEAN_CHECK_MEM_THRESHOLD = 200` invocations of `check_system` via jemalloc `stats.allocated` (under `HAS_JEMALLOC`) or OS resident memory (`getrusage` `ru_maxrss` and `/proc/self/statm`). Simultaneously, `environment::add_theorem` allocates one stack-scoped `type_checker::state` holding six unbounded hash tables (`m_infer_type[2]`, `m_whnf_core`, `m_whnf`, `m_success`, `m_failure`, and `m_unfold`) per declaration, while `Core.State.env` retains all elaborated declarations until `IO.Process.exit` tears down the process without GC. Discharging all `M` bodies inside one monolithic `CrateTheorem` proof retains every body's WHNF, unfold, and definitional-equality pair inside one `type_checker::state`; sharding proofs into one `.lean` module per function isolates both `type_checker::state` and `Core.State.env` per child process, exporting only a compact `BodyShardVerified` theorem type.
2. **Lazy `.eq_1` Realization Collisions Across Diamond Shards:** Equation theorems (`f.eq_1`, `f.eq_def`) are registered via `enableRealizationsForConst` and synthesized lazily by `realizeConst` when downstream modules invoke `simp [f]` or `unfold f`. Compiling sibling shards in parallel materializes identical `.eq_1` constants into multiple `.olean`s, failing `TrustedBoundary.collectRepoModuleConstants` duplicate and origin checks (`orig == mName`). Same-module explicit `f_def : f x = rhs := rfl` theorems or same-module anchor proofs prevent downstream equation synthesis.
3. **Dual `maxRecDepth` Cliffs (`512` vs. `8,192`) and `%[...|...]` List Desugaring:** `defaultMaxRecDepth := 512` caps `Core.withIncRecDepth`, whereas `scope_rec_depth` in `type_checker.cpp` permits `512 * g_kernel_rec_depth_factor = 8,192` frames. List literals of 33 or more elements (`elemsAndSeps.size >= 64`) desugar to `%[...|...]`, whose macro resides in `Init.NotationExtra` and is absent from `TrustedBoundary.allowedNotationSyntaxKinds`, while flat `List.cons` chains and linear Peano fuel (`symRun`) exhaust `maxRecDepth`. Balanced `++` (`List.append`) chunk trees and binary-doubling `runPow2` (`2^k` steps at depth `k`) keep recursion logarithmic.
4. **Why `decide +kernel` Violates Closed Policies and Corrupts Failure Classification:** Both `+kernel` and `+native` parse as `Lean.Parser.Tactic.configItem`, excluded by `TrustedBoundary.allowedTheoryTacticKinds` to block `decide +native` (`Lean.ofReduceBool`). Further, `decide +kernel` routes through `doKernel` (`mkAuxLemma`), reporting refutations on mutated crates as `(kernel)` or `maxRecDepth` exceptions rather than clean frontend mismatches. Evaluating canonicalized symbolic normalizers (`SymWord` / `SymBool` over masked `Nat` GMP literals returning a ground `CertVerdict`) via `rfl`, coupled with binary-radix `lookupBodyByPath` (`BTree`) and sorted identity-uniqueness witnesses (`O(M log M)`), proves sharded `CrateTheorem` claims with zero TCB expansion.

## Applicability

This report relates two pinned upstream subjects to characterize how Lean `v4.34.1` resource guards and constant realization govern Pass 1 `theory/` verification of multi-body Rust crates:

- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Source for `src/Lean/Shell.lean`, `src/runtime/{memory.cpp,interrupt.h,interrupt.cpp,thread.cpp}`, `src/kernel/{type_checker.h,type_checker.cpp,environment.cpp}`, `src/Init/{Prelude.lean,Notation.lean,NotationExtra.lean,Data/List/Notation.lean,Tactics.lean}`, and `src/Lean/{CoreM.lean,AddDecl.lean,Environment.lean,Elab/PreDefinition/Eqns.lean,Meta/Eqns.lean,Elab/Tactic/Decide.lean}`. Applies to batch CLI verification (`-t0 -DElab.async=false -Ddebug.skipKernelTC=false -M <MiB>`).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Authority for the 51-module `Init.*` prelude lock (`trusted/lean/foundation-lock.json`), Pass 1 parser/replay checks (`trusted/audit/TrustedBoundary.lean`), captured MIR AST and semantics (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`: `BodyVerified`, `ProgramVerified`, `CrateTheorem`, `UnitTheorem`), and MIR WP (`theory/Anneal/MirWp.lean`: `BodiesVerified`).

Cross-corpus scope: GMP limb tuning and external `nanoda` checkers are covered in `lean-kernel-natgmp-limb-tuning-and-nanoda-parallel-audit-throughput` and `lean-kernel-derivation-scale-checking-and-reflection-throughput`; large generated ISA specs in `lean-large-isa-and-compiler-semantics-scaling` and `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`; `.olean` provenance isolation in `anneal-trusted-boundary-audit-olean-stubbing-and-conservativity` and `lean-elaboration-metaprogramming-import-isolation-and-kernel-audit`; content-addressed caching in `anneal-verification-pipeline-profiling-and-content-addressed-caching`. This report isolates how Lean `v4.34.1` memory, recursion, realization, and `decide` semantics drive multi-body MIR sharding and canonical normalization.

## Findings

### 1. Runtime `-M` Heap Accounting, `LEAN_NAT_MAX_SIZE`, and Process Teardown

Basis: source

Lean's `-M` (`--memory=num`) flag (`src/Lean/Shell.lean` L160–161, L356–362, L476–478) configures `max_memory` in MiB and calls `Internal.setMaxMemory (maxMemory.toUSize * 1024 * 1024)`. In `src/runtime/memory.cpp` (L114–158), `set_max_memory` stores `g_max_memory`, and `check_memory(component_name)` is called inside `check_system` (`src/runtime/interrupt.cpp` L108–115) every `LEAN_CHECK_MEM_THRESHOLD = 200` checks (L14–16, L148):

```cpp
// src/runtime/memory.cpp L145-158
void check_memory(char const * component_name) {
    if (g_max_memory == 0) return;
    g_counter++;
    if (g_counter >= LEAN_CHECK_MEM_THRESHOLD) {
        g_counter = 0;
        size_t r = get_peak_rss();
        if (r > 0 && r < g_max_memory) return;
        r = get_current_rss();
        if (r == 0 || r < g_max_memory) return;
        throw_memory_exception(component_name);
    }
}
```

Platform preprocessor branches yield two materially different accounting regimes:

| Build / OS Branch | `get_peak_rss()` / `get_current_rss()` (`memory.cpp`) | Charges `mmap`'d `.olean`? | Operational Behavior Under `-M2048` |
| :--- | :--- | :--- | :--- |
| **`HAS_JEMALLOC`** (`L18–41`) | `mallctl("epoch")` + `mallctl("stats.allocated")` | **No** (live jemalloc heap bytes only) | Tracks elaborated terms, `type_checker::state` caches, and `Environment` maps; read-only `CompactedRegion` `.olean` pages (`src/runtime/compact.cpp`) do not consume `-M` budget. |
| **Linux non-jemalloc** (`L76–106`) | `getrusage(RUSAGE_SELF).ru_maxrss * 1024`, fallback `/proc/self/statm` (`resident * sysconf(_SC_PAGESIZE)`) | **Yes** (if `.olean` pages are faulted in) | Once peak RSS (`ru_maxrss`) reaches `g_max_memory`, every 200 checks reads `/proc/self/statm` and throws `memory_exception` whenever live RSS exceeds `g_max_memory`. |
| **macOS / Windows** (`L42–64, L72–94`) | `mach_task_basic_info.resident_size` / `WorkingSetSize` | **Yes** (working set) | Charges both heap allocations and faulted mapped `.olean` pages. |

Two related runtime details bound large-crate proof checking:

1. **Kernel Numeral Size Guard (`LEAN_NAT_MAX_SIZE`):** Independently of `-M`, `src/kernel/type_checker.cpp` enforces `LEAN_NAT_MAX_SIZE_DEFAULT = 128 * 1024 * 1024` (128 MiB, L31–36) via `check_nat_size` (L294–303) inside `infer_lit` (L318–319), `reduce_bin_nat_op` (L655–656), `reduce_pow` (L670–673), and `reduce_shiftLeft` (L685–688), plus `get_count_arg` (L308–313) enforcing `count <= UINT_MAX`. Any Pass 1 `Nat.shiftLeft`/`Nat.pow` over symbolic inputs must clamp shift widths (e.g., `Nat.ble shift 128`) before evaluation.
2. **Zero-GC Process Exit:** In `src/Lean/Shell.lean` L574–579, non-ASAN builds (`!Internal.hasAddressSanitizer ()`) exit via `IO.Process.exit` without tearing down the `Environment`. Running `M` isolated shard processes pays zero GC/destructor teardown cost.

### 2. Per-Declaration `type_checker::state` Caches, Module Retention, and `.eq_1` Collisions

Basis: source + derived

In `src/kernel/environment.cpp`, `environment::add_definition` (L181) and `environment::add_theorem` (L192–209) construct a stack-scoped `type_checker checker(*this, diag.get())` per declaration (after `sharecommon_persistent_fn` DAG-shares `v.get_value()` and `v.get_type()`, L197–199). In `src/kernel/type_checker.h` L25–49, `type_checker::state` holds six caches: `m_infer_type[2]`, `m_whnf_core`, `m_whnf`, `m_success`, `m_failure`, and `m_unfold`. As L33–42 explain, `m_success` and `m_failure` are deliberately `expr_pair_set` hash sets rather than an equivalence-closure union-find, because kernel `is_def_eq` is a sound, incomplete semi-decision procedure and **not transitive**.

This lifetime creates three distinct memory profiles across crate verification layouts:
- **Monolithic `CrateTheorem` (`M` bodies in 1 theorem):** Every body's unfolded `Program.bodies` tails, `evalStep` reductions, and `is_def_eq` pairs accumulate inside one `type_checker::state` until `add_theorem` finishes (L208), exhausting `-M2048`.
- **`M` separate `theorem`s in one `.lean` file:** Destroys `type_checker::state` between theorems, **but** `Core.State.env` (`src/Lean/CoreM.lean` L187–214) retains all elaborated `ConstantInfo.thmInfo` proof `Expr`s and auxiliary constants in process heap until exit.
- **Per-body `.lean` module shards:** Bounds both `type_checker::state` and `Core.State.env` to one body per `-M2048` child process. Each `Shard_i.olean` exports one `BodyShardVerified` theorem constant, which root `Proof.lean` references solely via `infer_constant` (`type_checker.cpp` L101–123) without ever unfolding the shard proof body.

#### Lazy `.eq_1` Equation Synthesis Collisions Across Sharded Diamonds

When sharded modules share an upstream specification module (`Spec/Logic.lean` $\to$ `{Shard_0.lean, Shard_1.lean}` $\to$ `Proof.lean`), Lean `v4.34.1`'s lazy equation synthesis breaks `.olean` disjointness:
1. Elaborating `def f` in `Spec/Logic.lean` registers `Core.enableRealizationsForConst` (`src/Lean/CoreM.lean` L847–849; `src/Lean/Environment.lean` L862–879) without immediately emitting `f.eq_1`.
2. When `Shard_0` and `Shard_1` both run `simp only [Logic.f]` or `unfold Logic.f`, `Lean.Meta.getEqnsFor?` (`src/Lean/Meta/Eqns.lean` L225–257) sees `alreadyGenerated?` return `none` (`L228`, `L239`) and invokes `Environment.realizeConst` (`src/Lean/Elab/PreDefinition/Eqns.lean` L30–71, L370; `src/Lean/Meta/Eqns.lean` L183–200; `src/Lean/Environment.lean` L2709–2782).
3. `realizeConst` adds `Logic.f.eq_1` (`isRealized := true`) into `asyncConstsMap` and `kenv`, so `mkModuleData` (`L1858–1885`) serializes `Logic.f.eq_1` into **both** `Shard_0.olean` and `Shard_1.olean`.
4. Combining both shards triggers `duplicate declaration` and `inventory origin mismatch` (`orig == mName`) inside `TrustedBoundary.collectRepoModuleConstants` (`trusted/audit/TrustedBoundary.lean` L1246–1255). Meanwhile, `Lean.Parser.Tactic.delta` is excluded from `allowedTheoryTacticKinds` (`L536–557`).

Two zero-TCB conventions eliminate this collision permanently:
1. **Explicit `_def := rfl` / Structure Projections:** Emit `theorem f_def (x : A) : f x = rhs := rfl` in `Spec/Logic.lean` and rewrite downstream via `rw [Logic.f_def]` / `simp only [Logic.f_def]` (never invoking `getEqnsFor?`), or pack non-recursive specs in a `structure` reduced via `.proj` (`reduce_proj`).
2. **Same-Module Anchor Materialization:** For pattern-matching definitions requiring `simp [g]`, add `private theorem g_eqns_anchor : True := by unfold g; exact True.intro` inside `Spec/Logic.lean` so `g.eq_1`..`g.eq_k` serialize once into `Spec/Logic.olean` with provenance `Spec.Logic` and `alreadyGenerated?` hits downstream.

### 3. Dual `maxRecDepth` Cliffs (`512` vs. `8,192`), `%[...|...]` List Desugaring, and Binary-Doubling Execution

Basis: source + derived

Lean `v4.34.1` enforces three nested recursion bounds:

| Layer | Bound (`5045d005`) | Source Anchors | Failure Mode |
| :--- | :--- | :--- | :--- |
| **Elaborator / `MetaM`** | `defaultMaxRecDepth := 512` | `Init/Prelude.lean` L4911, L5898; `Lean/Util/RecDepth.lean` L15–18; `CoreM.lean` L224, L471 | `runtime.maxRecDepth` in `TermElabM`/`MetaM`/`PrettyPrinter` |
| **C++ Kernel** | `512 * g_kernel_rec_depth_factor = 8,192` | `AddDecl.lean` L28, L32; `interrupt.h` L45–82; `interrupt.cpp` L57–82; `type_checker.cpp` L329, L469, L1172 | `stack_space_exception("type checker")` via `scope_rec_depth` |
| **OS Thread Stack** | `1 GiB` (64-bit) / `-s` | `thread.cpp` L28, L75–78; `Shell.lean` L329–340 | `check_stack` OS stack overflow guard |

Because elaborator `MetaM` hits `512` at `1/16`th the kernel's `8,192` ceiling (`interrupt.cpp` L60–66), two common MIR constructs trigger `runtime.maxRecDepth`:

1. **Flat List Literals (`«term[_]»` vs. `%[...|...]`):** In `src/Init/Data/List/Notation.lean` L50–63, `expandListLit` counts `size := elems.elemsAndSeps.size` (elements plus commas, so 32 items give `size = 63`, 33 items give `size = 65`):
   - `size < 64` expands to right-nested `List.cons`; `size >= 64` expands to `%[ $elems,* | List.nil ]`.
   - The `%[...|...]` macro rule lives in `src/Init/NotationExtra.lean` L286–297, and `«term%[_|_]»` is **absent** from `TrustedBoundary.allowedNotationSyntaxKinds` (`L521–527`, which admits `«term[_]»` and `«term_++_»`). Moreover, `%[...|...]` emits binary `let` chains that `whnf_core` (`type_checker.cpp` L543–544) eagerly zeta-substitutes into depth-`N` `List.cons` spines, and `unexpandListCons` (`Init/NotationExtra.lean` L155–162) recurses `O(N)` frames when printing errors.
   - **Cure:** Render captured `Body.locals`, `Body.basicBlocks`, `BasicBlock.statements`, and `String.ofList` character lists as **balanced binary `++` (`List.append`) trees over leaf `[...]` chunks of `<= 16` items**, bounding elaboration and zeta depth to `O(log N) <= 10`.
2. **Linear Peano Fuel vs. `runPow2`:** Stepping an interpreter via `Nat.rec ... K st` nests `K` frames in `Meta.whnf`, tripping `512` at `K ~ 350–450`. Binary-doubling `runPow2` (`2^k` steps at depth `k`) executes `512` steps at depth `9` and `4,096` steps at depth `12`.

### 4. Why `decide +kernel` Violates Closed Policies and Corrupts Failure Attribution

Basis: normative + source

`src/Init/Tactics.lean` (`L1382–1494`) defines `DecideConfig` (`native : Bool`, `kernel : Bool`, `revert : Bool`) and `syntax (name := decide) "decide" optConfig : tactic` (`L1472`), with `native_decide` defined as `decide +native` (`L1393`). Combined with `TrustedBoundary.lean` (`L529–557`) and `src/Lean/Elab/Tactic/Decide.lean` (`L70–193`), `+kernel` fails on two independent grounds:

1. **Syntactic Audit Rejection:** `TrustedBoundary.allowedTheoryTacticKinds` (`L536–557`) includes `Lean.Parser.Tactic.decide` and `Lean.Parser.Tactic.optConfig` while excluding `Lean.Parser.Tactic.configItem`. Because `+kernel`, `+native`, and `+revert` parse as `configItem`, admitting `configItem` without per-option inspection would expose `decide +native` (`Lean.ofReduceBool`), so Pass 1 rejects `decide +kernel` upfront.
2. **Diagnostic Misclassification on Mutant Failures:** Default `decide` (`doElab`, `Decide.lean` L88–103) reduces the `Decidable` instance via `Meta.whnf` first; on `isFalse` or stuck reduction, `diagnose` (`L134–182`) produces a structured frontend tactic error. By contrast, `decide +kernel` (`doKernel`, `L104–133`) bypasses `Meta.whnf` and calls `mkAuxLemma` directly in the kernel (`Elab.async := false`, `L116–117`). When a mutated Rust program makes the proposition false—or when `catch ex` tries fallback `Meta.whnf s` (`L125`) and hits `maxRecDepth`—`doKernel` emits raw `"(kernel) ..."` or `"runtime.maxRecDepth"` errors, which automated verification drivers cannot distinguish from internal tool crashes.

**`rfl` + `CertVerdict` Pattern:** Returning a tiny ground `CertVerdict` (`ok | fuelExhausted bb stmt | faultReached bb stmt | mismatch bb stmt gotTag expTag`) from a Pass-1 sound checker `checkCert_sound : checkCert ... = .ok -> Oblig` lets proof sites write `exact checkCert_sound ... rfl`. Valid crates reduce on C++ GMP `reduce_nat` (`type_checker.cpp` L702–733, L1181–1185); mutated crates fail in frontend `Meta.isDefEq` comparing two small ground constructors without AST dumping, `(kernel)` exceptions, or `maxRecDepth`.

### 5. Canonical Symbolic Expression Normalizers (`SymWord` / `SymBool`) Eliminating MIR-to-Spec Brittleness

Basis: source + derived

Direct inspection of `Trusted/MirAst.lean` (`L153–174`, `L400–447`, `L678–681`) and `Trusted/MirSemantics.lean` (`L1111–1159`, `L1490–1567`) shows four systematic representation gaps between captured `PostCleanup` MIR and human specifications:
- **Comparison orientation:** MIR preserves `BinOp.{gt, ge, ne}` alongside `{lt, le, eq}` (`MirAst.lean` L407);
- **Boolean XOR / negation:** `BinOp.bitXor` on booleans evaluates as `bne l r` (`MirSemantics.lean` L1157), so `b ^ true` encodes `!b`;
- **Switch polarity:** `rustc` commonly emits `SwitchTargets` matching `0` first (`evalBoolSwitchBranches` at `MirSemantics.lean` L1494–1500 tests `if !discr`), while `TrustedBoundary.lean` (`L521–527`) excludes `boolIfThenElse` (`bif`) and permits only `termIfThenElse` (`if ... then ... else ...`);
- **Bitwise masking & slicing:** Shift RHS values mask modulo `w.bitWidth`, chained shifts merge when `k0 + km < w.bitWidth`, and `(x >>> lo) &&& lowMask rem` vs `(x &&& (lowMask rem <<< lo)) >>> lo` canonicalize to `bitSlice`.

The self-contained Pass-1-admissible (`prelude`, locked `Init.*` only, `@Nat.rec` fuel with zero `._unsafe_rec` helpers, zero axioms) module below illustrates canonical normalization, GMP-aligned masked `Nat` arithmetic (`Nat.ble shift 128` DoS guard), `CertVerdict`, and binary-doubling `runPow2`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace AnnealSymNormDesign

inductive Width where | i8 | i16 | i32 | i64 | isize | i128

def Width.bits : Width → Nat
  | .i8 => 8 | .i16 => 16 | .i32 => 32
  | .i64 => 64 | .isize => 64 | .i128 => 128

/-- Shift guard preventing `check_nat_size` (`LEAN_NAT_MAX_SIZE`) blowup. -/
def lowMask (len : Nat) : Nat :=
  if Nat.ble len 128 then Nat.sub (Nat.shiftLeft 1 len) 1 else 0

def maskW (w : Width) (n : Nat) : Nat :=
  Nat.land n (lowMask w.bits)

mutual
  inductive SymWord where
    | arg      (idx : Nat) (w : Width)
    | lit      (w : Width) (bits : Nat)
    | bitSlice (x : SymWord) (lo len : Nat)
    | add      (w : Width) (a b : SymWord)
    | band     (w : Width) (a b : SymWord)
    | bor      (w : Width) (a b : SymWord)
    | bxor     (w : Width) (a b : SymWord)
    | shl      (w : Width) (a : SymWord) (k : Nat)
    | lshr     (w : Width) (a : SymWord) (k : Nat)
    | ite      (c : SymBool) (t e : SymWord)

  inductive SymBool where
    | arg    (idx : Nat)
    | lit    (b : Bool)
    | bnot   (a : SymBool)
    | band   (a b : SymBool)
    | bxor   (a b : SymBool)
    | eqW    (w : Width) (a b : SymWord)
    | ltW    (w : Width) (a b : SymWord)
    | leW    (w : Width) (a b : SymWord)
end

def normNot : SymBool → SymBool
  | .lit b     => .lit (!b)
  | .bnot a    => a
  | .ltW w a b => .leW w b a
  | .leW w a b => .ltW w b a
  | c          => .bnot c

def normBoolXor : SymBool → SymBool → SymBool
  | a, .lit true  => normNot a
  | .lit true, a  => normNot a
  | a, .lit false => a
  | .lit false, a => a
  | a, b          => .bxor a b

inductive CmpKind where | eq | ne | lt | le | gt | ge

def normCmp (op : CmpKind) (w : Width) (a b : SymWord) : SymBool :=
  match op with
  | .eq => .eqW w a b
  | .ne => .bnot (.eqW w a b)
  | .lt => .ltW w a b
  | .le => .leW w a b
  | .gt => .ltW w b a
  | .ge => .leW w b a

def normLshr (w : Width) (a : SymWord) (k : Nat) : SymWord :=
  let km := Nat.mod k w.bits
  if Nat.beq km 0 then a
  else match a with
    | .lshr _ inner k0 =>
      if Nat.blt (Nat.add k0 km) w.bits then .lshr w inner (Nat.add k0 km)
      else .lshr w a km
    | _ => .lshr w a km

def normBand (w : Width) (a b : SymWord) : SymWord :=
  match a, b with
  | .lshr _ x lo, .lit _ m =>
    let rem := Nat.sub w.bits lo
    if Nat.beq m (lowMask rem) then .bitSlice x lo rem else .band w a b
  | .lit _ m, .lshr _ x lo =>
    let rem := Nat.sub w.bits lo
    if Nat.beq m (lowMask rem) then .bitSlice x lo rem else .band w a b
  | _, _ => .band w a b

def normSwitchBool (discr : SymBool) (onZero onNonZero : SymWord) : SymWord :=
  match discr with
  | .lit true  => onNonZero
  | .lit false => onZero
  | .bnot c    => .ite c onZero onNonZero
  | _          => .ite discr onNonZero onZero

def evalSymPair (wEnv : Nat → Nat) (bEnv : Nat → Bool) (depth : Nat) :
    (SymWord → Nat) × (SymBool → Bool) :=
  @Nat.rec (fun _ => (SymWord → Nat) × (SymBool → Bool))
    (fun _ => 0, fun _ => false)
    (fun _ rec =>
      let recW := rec.1
      let recB := rec.2
      ( fun sw =>
          match sw with
          | .arg idx w       => maskW w (wEnv idx)
          | .lit w b         => maskW w b
          | .bitSlice x lo n => Nat.land (Nat.shiftRight (recW x) lo) (lowMask n)
          | .add w a b       => maskW w (Nat.add (recW a) (recW b))
          | .band w a b      => maskW w (Nat.land (recW a) (recW b))
          | .bor w a b       => maskW w (Nat.lor (recW a) (recW b))
          | .bxor w a b      => maskW w (Nat.xor (recW a) (recW b))
          | .shl w a k       => maskW w (Nat.shiftLeft (recW a) (Nat.mod k w.bits))
          | .lshr w a k      => Nat.shiftRight (recW a) (Nat.mod k w.bits)
          | .ite c t e       => if recB c then recW t else recW e
      , fun sb =>
          match sb with
          | .arg idx   => bEnv idx
          | .lit b     => b
          | .bnot a    => !(recB a)
          | .band a b  => recB a && recB b
          | .bxor a b  => if recB a then !(recB b) else recB b
          | .eqW _ a b => Nat.beq (recW a) (recW b)
          | .ltW _ a b => Nat.blt (recW a) (recW b)
          | .leW _ a b => Nat.ble (recW a) (recW b) ))
    depth

def evalSymWord (wEnv : Nat → Nat) (bEnv : Nat → Bool) (depth : Nat) (sw : SymWord) : Nat :=
  (evalSymPair wEnv bEnv depth).1 sw

inductive CertVerdict where
  | ok
  | fuelExhausted (bb stmt : Nat)
  | faultReached  (bb stmt : Nat)
  | mismatch      (bb stmt gotTag expTag : Nat)

def runPow2 {St Out : Type} (step : St → Option (Option Out × St))
    (pow2 : Nat) (st : St) : Option (Option Out × St) :=
  @Nat.rec (fun _ => St → Option (Option Out × St))
    step
    (fun _ half s =>
      match half s with
      | some (none, s') => half s'
      | other           => other)
    pow2 st

end AnnealSymNormDesign
```

Keeping intermediate word values as masked `Nat`s (`< 2^w`) routes closed evaluation directly onto C++ GMP `reduce_nat` (`type_checker.cpp` L702–733), avoiding `BitVec w` `Fin` proof overhead.

### 6. Binary-Radix `lookupBodyByPath` and Per-Body Sharded `CrateTheorem` Combinators

Basis: source + derived

In `Trusted/MirSemantics.lean` (`L1708–1809`), `CrateTheorem c` checks `c.program.scope = .crate`, `pointerWidthBits = 64`, `mirProfileVersion = 1`, `bodiesHaveUniqueIdentities` (`stringListPairwiseNe`, `L1720–1722`), `∀ defId body, getElem? c.program.bodies defId = some body → BodyVerified ...`, and `c.specs.property c.program`. `theory/Anneal/MirWp.lean` (`L1933–1940`) notes that `BodiesVerified` uses `List.foldr` rather than equation-compiler recursion because pattern-matching recursion even on a `Prop` generates an `unsafe` `._unsafe_rec` helper rejected by `TrustedBoundary`.

To shard `CrateTheorem` across `M` independent `.lean` files without unfolding `p.bodies` (`O(M^2)` list suffixes), `stringListPairwiseNe` (`O(M^2)`), or `String.append` spec-key reductions:
1. Index `p.bodies` and an aligned literal `SpecEntry` table via a balanced binary radix tree `BTree` keyed by `List Bool` paths (`lookupBodyByPath`), validated once per crate via `checkTreeMatches ... = true` (`by rfl`), reducing shard lookups to `⌈log₂ M⌉` projections.
2. Verify `bodiesHaveUniqueIdentities` from an `O(M log M)` sorted permutation witness (`sortedStrictlyLt sortedIds && checkPermMatches ... = true`).
3. Assemble per-body `ShardOk idx b` theorems via `AllShardsOk` (`List.foldr`, zero `._unsafe_rec`) into `CrateTheorem` under strict Statement-Origin Separation (zero `Anneal.*` constants in `CrateTheorem c`):

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic

namespace AnnealCrateShardDesign

inductive BTree (α : Type) where
  | leaf
  | node (l : BTree α) (v : Option α) (r : BTree α)

def BTree.getPath {α : Type} (path : List Bool) (t : BTree α) : Option α :=
  List.foldr
    (fun bit k cur =>
      match cur with
      | .leaf => none
      | .node l _ r => k (if bit then r else l))
    (fun cur =>
      match cur with
      | .leaf => none
      | .node _ v _ => v)
    path
    t

def natToPathAux : Nat → Nat → List Bool :=
  @Nat.rec (fun _ => Nat → List Bool)
    (fun _ => [])
    (fun _ rec n =>
      if Nat.ble n 1 then []
      else (Nat.beq (Nat.mod n 2) 1) :: rec (Nat.div n 2))

def idxToPath (idx : Nat) : List Bool :=
  natToPathAux 32 (Nat.add idx 1)

def lookupBodyByPath {α : Type} (t : BTree α) (defId : Nat) : Option α :=
  BTree.getPath (idxToPath defId) t

def checkTreeMatches {α : Type} (eqFn : α → α → Bool)
    (t : BTree α) (base : Nat) (xs : List α) : Bool :=
  List.foldr
    (fun x k idx =>
      match lookupBodyByPath t idx with
      | some y => eqFn x y && k (idx + 1)
      | none   => false)
    (fun _ => true)
    xs
    base

def AllShardsOk {Body : Type} (ShardOk : Nat → Body → Prop)
    (t : BTree Body) (base : Nat) (bs : List Body) : Prop :=
  List.foldr
    (fun b k idx =>
      (lookupBodyByPath t idx = some b → ShardOk idx b) ∧ k (idx + 1))
    (fun _ => True)
    bs
    base

def getAt {α : Type} (k : Nat) (xs : List α) : Option α :=
  @Nat.rec (fun _ => List α → Option α)
    (fun ys => match ys with | [] => none | y :: _ => some y)
    (fun _ rec ys => match ys with | [] => none | _ :: tl => rec tl)
    k
    xs

theorem allShardsOk_lookup {Body : Type} {ShardOk : Nat → Body → Prop}
    {t : BTree Body} {eqFn : Body → Body → Bool}
    (eqSound : ∀ a b, eqFn a b = true → a = b) :
    ∀ (base : Nat) (bs : List Body),
      checkTreeMatches eqFn t base bs = true →
      AllShardsOk ShardOk t base bs →
      ∀ (k : Nat) (b : Body),
        getAt k bs = some b →
        ShardOk (base + k) b
  | _, [], _, _, _, _, hGet => by unfold getAt at hGet; cases hGet
  | base, hd :: tl, hChk, hShards, 0, b, hGet => by
    unfold getAt at hGet
    dsimp only at hGet
    injection hGet with hEq
    subst hd
    unfold checkTreeMatches at hChk
    unfold AllShardsOk at hShards
    dsimp only at hChk hShards
    cases hLut : lookupBodyByPath t base with
    | none => rw [hLut] at hChk; cases hChk
    | some y =>
      rw [hLut] at hChk
      cases hCmp : eqFn b y with
      | false => rw [hCmp] at hChk; cases hChk
      | true =>
        rw [eqSound b y hCmp] at hLut
        rw [Nat.add_zero]
        exact hShards.1 hLut
  | base, hd :: tl, hChk, hShards, k + 1, b, hGet => by
    change getAt k tl = some b at hGet
    unfold checkTreeMatches at hChk
    unfold AllShardsOk at hShards
    dsimp only at hChk hShards
    cases hLut : lookupBodyByPath t base with
    | none => rw [hLut] at hChk; cases hChk
    | some y =>
      rw [hLut] at hChk
      cases hCmp : eqFn hd y with
      | false => rw [hCmp] at hChk; cases hChk
      | true =>
        rw [hCmp] at hChk
        have hSub := allShardsOk_lookup eqSound (base + 1) tl hChk hShards.2 k b hGet
        rw [Nat.add_assoc, Nat.add_comm 1 k] at hSub
        exact hSub

end AnnealCrateShardDesign
```

## Boundaries

- **Direct `decide +kernel`, `decide +native`, `%[...|...]`, and equation-compiled `Type`-valued recursion (`unsupported`):** `TrustedBoundary.lean` (`L521–557`, `L1117–1153`) rejects `Parser.Tactic.configItem` (`+kernel`, `+native`, `+revert`), omits `«term%[_|_]»` and `boolIfThenElse` (`bif`), and rejects any recursive `def` whose equation compiler synthesizes a `partial`/`unsafe` `._unsafe_rec` helper.
- **Single-file multi-theorem splitting (`known not to apply`):** Separating `BodyVerified` proofs into `M` distinct `theorem` declarations in one `.lean` file resets `type_checker::state` (`environment.cpp` L196–208) between theorems, **but** does not bound process memory because `Core.State.env` (`CoreM.lean` L187–214) retains all elaborated declarations until process exit; likewise, `HAS_JEMALLOC` `-M` checks (`memory.cpp` L18–41) exclude mapped `.olean` pages whereas non-jemalloc Linux `/proc/self/statm` (`L95–105`) counts resident mapped pages.
- **macOS/Windows RSS paths and live host execution of the distilled Lean snippets (`not examined`):** macOS `mach_task_basic_info` (`memory.cpp` L88–94) and Windows `GetProcessMemoryInfo` (`L42–64`) were inspected by source only; live Lean `v4.34.1` compilation of `AnnealSymNormDesign` and `AnnealCrateShardDesign` was not executed dynamically in this turn, so their kernel admissibility is `derived` from `TrustedBoundary.lean` and `MirWp.lean`.
- **Post-`v4.34.1` evolution of `List/Notation.lean` and `g_kernel_rec_depth_factor` (`unknown`):** Whether Lean releases after `5045d0056413266e57c625dcd7c365b10e377c52` alter the 33-element `%[...|...]` threshold (`L59`) or the `16×` kernel recursion multiplier (`interrupt.cpp` L66) is unknown without re-inspecting newer tags.

## Evidence

| Subject / Pin | Inspected Files & Exact Line Ranges | Verified Anchors & Observations |
| :--- | :--- | :--- |
| `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) | `src/Lean/Shell.lean` L160–161, L193–194, L329–369, L476–481, L574–579 | `-M` sets `Internal.setMaxMemory (maxMemory * 1024 * 1024)`; non-ASAN builds exit via `IO.Process.exit` skipping GC |
| `leanprover/lean4` (`5045d005`, `v4.34.1`) | `src/runtime/memory.cpp` L14–162; `src/runtime/interrupt.h` L45–82; `src/runtime/interrupt.cpp` L57–115; `src/runtime/thread.cpp` L24–85 | `LEAN_CHECK_MEM_THRESHOLD = 200`; jemalloc `stats.allocated` vs `/proc/self/statm`; `g_kernel_rec_depth_factor = 16`; `1 GiB` stack |
| `leanprover/lean4` (`5045d005`, `v4.34.1`) | `src/kernel/type_checker.h` L25–49; `src/kernel/type_checker.cpp` L31–36, L294–320, L329, L469, L543, L660–733, L1172–1185; `src/kernel/environment.cpp` L180–209 | Per-declaration `type_checker::state` (6 caches); `LEAN_NAT_MAX_SIZE_DEFAULT = 128 MiB`; GMP `reduce_nat`; `decide` fast path |
| `leanprover/lean4` (`5045d005`, `v4.34.1`) | `src/Init/Prelude.lean` L4911, L5898; `src/Lean/Util/RecDepth.lean` L15–18; `src/Lean/CoreM.lean` L187–224, L471, L847–849; `src/Lean/AddDecl.lean` L23–33 | `defaultMaxRecDepth := 512`; `Core.State.env` retention; `maxRecDepth` passed to `addDeclCore` |
| `leanprover/lean4` (`5045d005`, `v4.34.1`) | `src/Init/Data/List/Notation.lean` L35–63; `src/Init/NotationExtra.lean` L152–162, L286–297 | `< 64` tokens (`≤ 32` items) $\to$ `List.cons`; `≥ 64` $\to$ `%[...|...]` defined in `Init.NotationExtra` |
| `leanprover/lean4` (`5045d005`, `v4.34.1`) | `src/Lean/Environment.lean` L851–880, L1858–1885, L2648–2782; `src/Lean/Meta/Eqns.lean` L180–257; `src/Lean/Elab/PreDefinition/Eqns.lean` L30–103, L370 | `enableRealizationsForConst` + `realizeConst` persists lazy `.eq_1` into the caller's `.olean` (`mkModuleData`) |
| `leanprover/lean4` (`5045d005`, `v4.34.1`) | `src/Init/Tactics.lean` L1382–1494; `src/Lean/Elab/Tactic/Decide.lean` L70–193 | `DecideConfig` (`+kernel`, `+native`, `+revert`); `doElab` vs `doKernel` (`mkAuxLemma`) diagnostics |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/lean/foundation-lock.json`; `trusted/audit/TrustedBoundary.lean` L521–557, L1117–1153, L1240–1265; `trusted/lean/Trusted/MirAst.lean` L153–174, L400–447, L678–681; `trusted/lean/Trusted/MirSemantics.lean` L1111–1159, L1490–1569, L1708–1809; `theory/Anneal/MirWp.lean` L1925–1963 | Closed allowlists excluding `configItem` and `%[...|...]`; `.olean` duplicate/origin checks; `MirSemantics` `BinOp`/`SwitchTargets`/`CrateTheorem`; `List.foldr` in `BodiesVerified` |

## Revalidation

1. **Check Lean Runtime & Kernel Constants Across Toolchain Upgrades:** Inspect `src/runtime/memory.cpp` (`LEAN_CHECK_MEM_THRESHOLD`), `src/runtime/interrupt.cpp` (`g_kernel_rec_depth_factor`), `src/Init/Prelude.lean` (`defaultMaxRecDepth`), `src/Init/Data/List/Notation.lean` (`size < 64`), and `src/kernel/type_checker.h` (`type_checker::state`) in `leanprover/lean4` against the values recorded under **Evidence**.
2. **Verify Anneal Pass 1 Allowlists & Foundation Ceiling:**
   ```bash
   python3 -c 'import json; g=set(json.load(open("trusted/lean/foundation-lock.json"))["graph"]); print(len(g), "Init.NotationExtra" in g, "Init.Data.List.Notation" in g)'
   ```
   Confirm `51 True True` and check `TrustedBoundary.lean` (`allowedNotationSyntaxKinds`, `allowedTheoryTacticKinds`, `collectRepoModuleConstants`).
3. **Typecheck the Distilled Lean Snippets:** Save `AnnealSymNormDesign` and `AnnealCrateShardDesign` to `/tmp/symnorm_test.lean` and `/tmp/crateshard_test.lean`, append `#print axioms`, and run:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/symnorm_test.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/crateshard_test.lean
   ```
   Verify exit `0`, axiom closure $\subseteq \{\text{propext}\}$, and zero `._unsafe_rec` helpers.
